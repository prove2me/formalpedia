-- Prove2me | solution 1 for syracuse_descends_range_1686043_1688043
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:23:15.1423+00:00
-- url     : https://prove2.me/submissions/89cfea58-a5e8-487b-a55e-8e87c67b6b5e

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


theorem B2531333 : Blo 1686043 2531333 := bbase (se 4 (by rfl) ⟨237312, by rfl⟩ : syracuseStep 2531333 = 474625) (by norm_num)
theorem B19226645 : Blo 1686043 19226645 := bbase (se 6 (by rfl) ⟨450624, by rfl⟩ : syracuseStep 19226645 = 901249) (by norm_num)
theorem B2531357 : Blo 1686043 2531357 := bbase (se 3 (by rfl) ⟨474629, by rfl⟩ : syracuseStep 2531357 = 949259) (by norm_num)
theorem B2531381 : Blo 1686043 2531381 := bbase (se 5 (by rfl) ⟨118658, by rfl⟩ : syracuseStep 2531381 = 237317) (by norm_num)
theorem B1802293 : Blo 1686043 1802293 := bbase (se 5 (by rfl) ⟨84482, by rfl⟩ : syracuseStep 1802293 = 168965) (by norm_num)
theorem B2531405 : Blo 1686043 2531405 := bbase (se 3 (by rfl) ⟨474638, by rfl⟩ : syracuseStep 2531405 = 949277) (by norm_num)
theorem B3203165 : Blo 1686043 3203165 := bbase (se 3 (by rfl) ⟨600593, by rfl⟩ : syracuseStep 3203165 = 1201187) (by norm_num)
theorem B2531429 : Blo 1686043 2531429 := bbase (se 4 (by rfl) ⟨237321, by rfl⟩ : syracuseStep 2531429 = 474643) (by norm_num)
theorem B2531453 : Blo 1686043 2531453 := bbase (se 3 (by rfl) ⟨474647, by rfl⟩ : syracuseStep 2531453 = 949295) (by norm_num)
theorem B4268173 : Blo 1686043 4268173 := bbase (se 3 (by rfl) ⟨800282, by rfl⟩ : syracuseStep 4268173 = 1600565) (by norm_num)
theorem B3604621 : Blo 1686043 3604621 := bbase (se 3 (by rfl) ⟨675866, by rfl⟩ : syracuseStep 3604621 = 1351733) (by norm_num)
theorem B2531477 : Blo 1686043 2531477 := bbase (se 6 (by rfl) ⟨59331, by rfl⟩ : syracuseStep 2531477 = 118663) (by norm_num)
theorem B2531501 : Blo 1686043 2531501 := bbase (se 3 (by rfl) ⟨474656, by rfl⟩ : syracuseStep 2531501 = 949313) (by norm_num)
theorem B1802413 : Blo 1686043 1802413 := bbase (se 3 (by rfl) ⟨337952, by rfl⟩ : syracuseStep 1802413 = 675905) (by norm_num)
theorem B2531525 : Blo 1686043 2531525 := bbase (se 4 (by rfl) ⟨237330, by rfl⟩ : syracuseStep 2531525 = 474661) (by norm_num)
theorem B3653837 : Blo 1686043 3653837 := bbase (se 3 (by rfl) ⟨685094, by rfl⟩ : syracuseStep 3653837 = 1370189) (by norm_num)
theorem B7798997 : Blo 1686043 7798997 := bbase (se 7 (by rfl) ⟨91394, by rfl⟩ : syracuseStep 7798997 = 182789) (by norm_num)
theorem B2531549 : Blo 1686043 2531549 := bbase (se 3 (by rfl) ⟨474665, by rfl⟩ : syracuseStep 2531549 = 949331) (by norm_num)
theorem B3039461 : Blo 1686043 3039461 := bbase (se 4 (by rfl) ⟨284949, by rfl⟩ : syracuseStep 3039461 = 569899) (by norm_num)
theorem B3203317 : Blo 1686043 3203317 := bbase (se 5 (by rfl) ⟨150155, by rfl⟩ : syracuseStep 3203317 = 300311) (by norm_num)
theorem B2531573 : Blo 1686043 2531573 := bbase (se 5 (by rfl) ⟨118667, by rfl⟩ : syracuseStep 2531573 = 237335) (by norm_num)
theorem B4268285 : Blo 1686043 4268285 := bbase (se 3 (by rfl) ⟨800303, by rfl⟩ : syracuseStep 4268285 = 1600607) (by norm_num)
theorem B2531597 : Blo 1686043 2531597 := bbase (se 3 (by rfl) ⟨474674, by rfl⟩ : syracuseStep 2531597 = 949349) (by norm_num)
theorem B2531621 : Blo 1686043 2531621 := bbase (se 4 (by rfl) ⟨237339, by rfl⟩ : syracuseStep 2531621 = 474679) (by norm_num)
theorem B10805557 : Blo 1686043 10805557 := bbase (se 5 (by rfl) ⟨506510, by rfl⟩ : syracuseStep 10805557 = 1013021) (by norm_num)
theorem B2531645 : Blo 1686043 2531645 := bbase (se 3 (by rfl) ⟨474683, by rfl⟩ : syracuseStep 2531645 = 949367) (by norm_num)
theorem B32440661 : Blo 1686043 32440661 := bbase (se 10 (by rfl) ⟨47520, by rfl⟩ : syracuseStep 32440661 = 95041) (by norm_num)
theorem B2531669 : Blo 1686043 2531669 := bbase (se 10 (by rfl) ⟨3708, by rfl⟩ : syracuseStep 2531669 = 7417) (by norm_num)
theorem B2703709 : Blo 1686043 2703709 := bbase (se 3 (by rfl) ⟨506945, by rfl⟩ : syracuseStep 2703709 = 1013891) (by norm_num)
theorem B2531693 : Blo 1686043 2531693 := bbase (se 3 (by rfl) ⟨474692, by rfl⟩ : syracuseStep 2531693 = 949385) (by norm_num)
theorem B5693813 : Blo 1686043 5693813 := bbase (se 5 (by rfl) ⟨266897, by rfl⟩ : syracuseStep 5693813 = 533795) (by norm_num)
theorem B2531717 : Blo 1686043 2531717 := bbase (se 4 (by rfl) ⟨237348, by rfl⟩ : syracuseStep 2531717 = 474697) (by norm_num)
theorem B2531741 : Blo 1686043 2531741 := bbase (se 3 (by rfl) ⟨474701, by rfl⟩ : syracuseStep 2531741 = 949403) (by norm_num)
theorem B2531765 : Blo 1686043 2531765 := bbase (se 5 (by rfl) ⟨118676, by rfl⟩ : syracuseStep 2531765 = 237353) (by norm_num)
theorem B4268477 : Blo 1686043 4268477 := bbase (se 3 (by rfl) ⟨800339, by rfl⟩ : syracuseStep 4268477 = 1600679) (by norm_num)
theorem B2531789 : Blo 1686043 2531789 := bbase (se 3 (by rfl) ⟨474710, by rfl⟩ : syracuseStep 2531789 = 949421) (by norm_num)
theorem B2531813 : Blo 1686043 2531813 := bbase (se 4 (by rfl) ⟨237357, by rfl⟩ : syracuseStep 2531813 = 474715) (by norm_num)
theorem B2310637 : Blo 1686043 2310637 := bbase (se 3 (by rfl) ⟨433244, by rfl⟩ : syracuseStep 2310637 = 866489) (by norm_num)
theorem B2531837 : Blo 1686043 2531837 := bbase (se 3 (by rfl) ⟨474719, by rfl⟩ : syracuseStep 2531837 = 949439) (by norm_num)
theorem B2531861 : Blo 1686043 2531861 := bbase (se 6 (by rfl) ⟨59340, by rfl⟩ : syracuseStep 2531861 = 118681) (by norm_num)
theorem B3203621 : Blo 1686043 3203621 := bbase (se 4 (by rfl) ⟨300339, by rfl⟩ : syracuseStep 3203621 = 600679) (by norm_num)
theorem B2163245 : Blo 1686043 2163245 := bbase (se 3 (by rfl) ⟨405608, by rfl⟩ : syracuseStep 2163245 = 811217) (by norm_num)
theorem B2531885 : Blo 1686043 2531885 := bbase (se 3 (by rfl) ⟨474728, by rfl⟩ : syracuseStep 2531885 = 949457) (by norm_num)
theorem B2531909 : Blo 1686043 2531909 := bbase (se 4 (by rfl) ⟨237366, by rfl⟩ : syracuseStep 2531909 = 474733) (by norm_num)
theorem B2531933 : Blo 1686043 2531933 := bbase (se 3 (by rfl) ⟨474737, by rfl⟩ : syracuseStep 2531933 = 949475) (by norm_num)
theorem B2531957 : Blo 1686043 2531957 := bbase (se 5 (by rfl) ⟨118685, by rfl⟩ : syracuseStep 2531957 = 237371) (by norm_num)
theorem B2531981 : Blo 1686043 2531981 := bbase (se 3 (by rfl) ⟨474746, by rfl⟩ : syracuseStep 2531981 = 949493) (by norm_num)
theorem B2532005 : Blo 1686043 2532005 := bbase (se 4 (by rfl) ⟨237375, by rfl⟩ : syracuseStep 2532005 = 474751) (by norm_num)
theorem B2532029 : Blo 1686043 2532029 := bbase (se 3 (by rfl) ⟨474755, by rfl⟩ : syracuseStep 2532029 = 949511) (by norm_num)
theorem B2532053 : Blo 1686043 2532053 := bbase (se 7 (by rfl) ⟨29672, by rfl⟩ : syracuseStep 2532053 = 59345) (by norm_num)
theorem B8545013 : Blo 1686043 8545013 := bbase (se 5 (by rfl) ⟨400547, by rfl⟩ : syracuseStep 8545013 = 801095) (by norm_num)
theorem B3793661 : Blo 1686043 3793661 := bbase (se 3 (by rfl) ⟨711311, by rfl⟩ : syracuseStep 3793661 = 1422623) (by norm_num)
theorem B4801285 : Blo 1686043 4801285 := bbase (se 4 (by rfl) ⟨450120, by rfl⟩ : syracuseStep 4801285 = 900241) (by norm_num)
theorem B4268821 : Blo 1686043 4268821 := bbase (se 6 (by rfl) ⟨100050, by rfl⟩ : syracuseStep 4268821 = 200101) (by norm_num)
theorem B5694245 : Blo 1686043 5694245 := bbase (se 4 (by rfl) ⟨533835, by rfl⟩ : syracuseStep 5694245 = 1067671) (by norm_num)
theorem B3793733 : Blo 1686043 3793733 := bbase (se 4 (by rfl) ⟨355662, by rfl⟩ : syracuseStep 3793733 = 711325) (by norm_num)
theorem B2401093 : Blo 1686043 2401093 := bbase (se 4 (by rfl) ⟨225102, by rfl⟩ : syracuseStep 2401093 = 450205) (by norm_num)
theorem B4268933 : Blo 1686043 4268933 := bbase (se 4 (by rfl) ⟨400212, by rfl⟩ : syracuseStep 4268933 = 800425) (by norm_num)
theorem B6407045 : Blo 1686043 6407045 := bbase (se 4 (by rfl) ⟨600660, by rfl⟩ : syracuseStep 6407045 = 1201321) (by norm_num)
theorem B3793805 : Blo 1686043 3793805 := bbase (se 3 (by rfl) ⟨711338, by rfl⟩ : syracuseStep 3793805 = 1422677) (by norm_num)
theorem B3793877 : Blo 1686043 3793877 := bbase (se 7 (by rfl) ⟨44459, by rfl⟩ : syracuseStep 3793877 = 88919) (by norm_num)
theorem B3793949 : Blo 1686043 3793949 := bbase (se 3 (by rfl) ⟨711365, by rfl⟩ : syracuseStep 3793949 = 1422731) (by norm_num)
theorem B4269125 : Blo 1686043 4269125 := bbase (se 4 (by rfl) ⟨400230, by rfl⟩ : syracuseStep 4269125 = 800461) (by norm_num)
theorem B7693397 : Blo 1686043 7693397 := bbase (se 8 (by rfl) ⟨45078, by rfl⟩ : syracuseStep 7693397 = 90157) (by norm_num)
theorem B5407829 : Blo 1686043 5407829 := bbase (se 8 (by rfl) ⟨31686, by rfl⟩ : syracuseStep 5407829 = 63373) (by norm_num)
theorem B3794021 : Blo 1686043 3794021 := bbase (se 4 (by rfl) ⟨355689, by rfl⟩ : syracuseStep 3794021 = 711379) (by norm_num)
theorem B2565245 : Blo 1686043 2565245 := bbase (se 3 (by rfl) ⟨480983, by rfl⟩ : syracuseStep 2565245 = 961967) (by norm_num)
theorem B8537237 : Blo 1686043 8537237 := bbase (se 6 (by rfl) ⟨200091, by rfl⟩ : syracuseStep 8537237 = 400183) (by norm_num)
theorem B2401429 : Blo 1686043 2401429 := bbase (se 6 (by rfl) ⟨56283, by rfl⟩ : syracuseStep 2401429 = 112567) (by norm_num)
theorem B6407333 : Blo 1686043 6407333 := bbase (se 4 (by rfl) ⟨600687, by rfl⟩ : syracuseStep 6407333 = 1201375) (by norm_num)
theorem B2163881 : Blo 1686043 2163881 := bbase (se 2 (by rfl) ⟨811455, by rfl⟩ : syracuseStep 2163881 = 1622911) (by norm_num)
theorem B3794093 : Blo 1686043 3794093 := bbase (se 3 (by rfl) ⟨711392, by rfl⟩ : syracuseStep 3794093 = 1422785) (by norm_num)
theorem B5694677 : Blo 1686043 5694677 := bbase (se 7 (by rfl) ⟨66734, by rfl⟩ : syracuseStep 5694677 = 133469) (by norm_num)
theorem B3794165 : Blo 1686043 3794165 := bbase (se 5 (by rfl) ⟨177851, by rfl⟩ : syracuseStep 3794165 = 355703) (by norm_num)
theorem B3204373 : Blo 1686043 3204373 := bbase (se 6 (by rfl) ⟨75102, by rfl⟩ : syracuseStep 3204373 = 150205) (by norm_num)
theorem B2884901 : Blo 1686043 2884901 := bbase (se 4 (by rfl) ⟨270459, by rfl⟩ : syracuseStep 2884901 = 540919) (by norm_num)
theorem B1951025 : Blo 1686043 1951025 := bbase (se 2 (by rfl) ⟨731634, by rfl⟩ : syracuseStep 1951025 = 1463269) (by norm_num)
theorem B3794237 : Blo 1686043 3794237 := bbase (se 3 (by rfl) ⟨711419, by rfl⟩ : syracuseStep 3794237 = 1422839) (by norm_num)
theorem B2401645 : Blo 1686043 2401645 := bbase (se 3 (by rfl) ⟨450308, by rfl⟩ : syracuseStep 2401645 = 900617) (by norm_num)
theorem B3794309 : Blo 1686043 3794309 := bbase (se 4 (by rfl) ⟨355716, by rfl⟩ : syracuseStep 3794309 = 711433) (by norm_num)
theorem B4269469 : Blo 1686043 4269469 := bbase (se 3 (by rfl) ⟨800525, by rfl⟩ : syracuseStep 4269469 = 1601051) (by norm_num)
theorem B3204517 : Blo 1686043 3204517 := bbase (se 4 (by rfl) ⟨300423, by rfl⟩ : syracuseStep 3204517 = 600847) (by norm_num)
theorem B3900869 : Blo 1686043 3900869 := bbase (se 4 (by rfl) ⟨365706, by rfl⟩ : syracuseStep 3900869 = 731413) (by norm_num)
theorem B3794381 : Blo 1686043 3794381 := bbase (se 3 (by rfl) ⟨711446, by rfl⟩ : syracuseStep 3794381 = 1422893) (by norm_num)
theorem B9602549 : Blo 1686043 9602549 := bbase (se 5 (by rfl) ⟨450119, by rfl⟩ : syracuseStep 9602549 = 900239) (by norm_num)
theorem B4269581 : Blo 1686043 4269581 := bbase (se 3 (by rfl) ⟨800546, by rfl⟩ : syracuseStep 4269581 = 1601093) (by norm_num)
theorem B3794453 : Blo 1686043 3794453 := bbase (se 6 (by rfl) ⟨88932, by rfl⟩ : syracuseStep 3794453 = 177865) (by norm_num)
theorem B3794525 : Blo 1686043 3794525 := bbase (se 3 (by rfl) ⟨711473, by rfl⟩ : syracuseStep 3794525 = 1422947) (by norm_num)
theorem B5695109 : Blo 1686043 5695109 := bbase (se 4 (by rfl) ⟨533916, by rfl⟩ : syracuseStep 5695109 = 1067833) (by norm_num)
theorem B3794597 : Blo 1686043 3794597 := bbase (se 4 (by rfl) ⟨355743, by rfl⟩ : syracuseStep 3794597 = 711487) (by norm_num)
theorem B4269773 : Blo 1686043 4269773 := bbase (se 3 (by rfl) ⟨800582, by rfl⟩ : syracuseStep 4269773 = 1601165) (by norm_num)
theorem B2311885 : Blo 1686043 2311885 := bbase (se 3 (by rfl) ⟨433478, by rfl⟩ : syracuseStep 2311885 = 866957) (by norm_num)
theorem B2279125 : Blo 1686043 2279125 := bbase (se 7 (by rfl) ⟨26708, by rfl⟩ : syracuseStep 2279125 = 53417) (by norm_num)
theorem B2402021 : Blo 1686043 2402021 := bbase (se 4 (by rfl) ⟨225189, by rfl⟩ : syracuseStep 2402021 = 450379) (by norm_num)
theorem B3794669 : Blo 1686043 3794669 := bbase (se 3 (by rfl) ⟨711500, by rfl⟩ : syracuseStep 3794669 = 1423001) (by norm_num)
theorem B3794741 : Blo 1686043 3794741 := bbase (se 5 (by rfl) ⟨177878, by rfl⟩ : syracuseStep 3794741 = 355757) (by norm_num)
theorem B3794813 : Blo 1686043 3794813 := bbase (se 3 (by rfl) ⟨711527, by rfl⟩ : syracuseStep 3794813 = 1423055) (by norm_num)
theorem B28837781 : Blo 1686043 28837781 := bbase (se 6 (by rfl) ⟨675885, by rfl⟩ : syracuseStep 28837781 = 1351771) (by norm_num)
theorem B3794885 : Blo 1686043 3794885 := bbase (se 4 (by rfl) ⟨355770, by rfl⟩ : syracuseStep 3794885 = 711541) (by norm_num)
theorem B3794957 : Blo 1686043 3794957 := bbase (se 3 (by rfl) ⟨711554, by rfl⟩ : syracuseStep 3794957 = 1423109) (by norm_num)
theorem B5769253 : Blo 1686043 5769253 := bbase (se 4 (by rfl) ⟨540867, by rfl⟩ : syracuseStep 5769253 = 1081735) (by norm_num)
theorem B4270117 : Blo 1686043 4270117 := bbase (se 4 (by rfl) ⟨400323, by rfl⟩ : syracuseStep 4270117 = 800647) (by norm_num)
theorem B5695541 : Blo 1686043 5695541 := bbase (se 5 (by rfl) ⟨266978, by rfl⟩ : syracuseStep 5695541 = 533957) (by norm_num)
theorem B3795029 : Blo 1686043 3795029 := bbase (se 8 (by rfl) ⟨22236, by rfl⟩ : syracuseStep 3795029 = 44473) (by norm_num)
theorem B10815605 : Blo 1686043 10815605 := bbase (se 5 (by rfl) ⟨506981, by rfl⟩ : syracuseStep 10815605 = 1013963) (by norm_num)
theorem B2279557 : Blo 1686043 2279557 := bbase (se 4 (by rfl) ⟨213708, by rfl⟩ : syracuseStep 2279557 = 427417) (by norm_num)
theorem B6842501 : Blo 1686043 6842501 := bbase (se 4 (by rfl) ⟨641484, by rfl⟩ : syracuseStep 6842501 = 1282969) (by norm_num)
theorem B4270229 : Blo 1686043 4270229 := bbase (se 6 (by rfl) ⟨100083, by rfl⟩ : syracuseStep 4270229 = 200167) (by norm_num)
theorem B3795101 : Blo 1686043 3795101 := bbase (se 3 (by rfl) ⟨711581, by rfl⟩ : syracuseStep 3795101 = 1423163) (by norm_num)
theorem B9119957 : Blo 1686043 9119957 := bbase (se 7 (by rfl) ⟨106874, by rfl⟩ : syracuseStep 9119957 = 213749) (by norm_num)
theorem B4802789 : Blo 1686043 4802789 := bbase (se 4 (by rfl) ⟨450261, by rfl⟩ : syracuseStep 4802789 = 900523) (by norm_num)
theorem B3795173 : Blo 1686043 3795173 := bbase (se 4 (by rfl) ⟨355797, by rfl⟩ : syracuseStep 3795173 = 711595) (by norm_num)
theorem B3795245 : Blo 1686043 3795245 := bbase (se 3 (by rfl) ⟨711608, by rfl⟩ : syracuseStep 3795245 = 1423217) (by norm_num)
theorem B6408517 : Blo 1686043 6408517 := bbase (se 4 (by rfl) ⟨600798, by rfl⟩ : syracuseStep 6408517 = 1201597) (by norm_num)
theorem B3082573 : Blo 1686043 3082573 := bbase (se 3 (by rfl) ⟨577982, by rfl⟩ : syracuseStep 3082573 = 1155965) (by norm_num)
theorem B4270421 : Blo 1686043 4270421 := bbase (se 10 (by rfl) ⟨6255, by rfl⟩ : syracuseStep 4270421 = 12511) (by norm_num)
theorem B3795317 : Blo 1686043 3795317 := bbase (se 5 (by rfl) ⟨177905, by rfl⟩ : syracuseStep 3795317 = 355811) (by norm_num)
theorem B2165113 : Blo 1686043 2165113 := bbase (se 2 (by rfl) ⟨811917, by rfl⟩ : syracuseStep 2165113 = 1623835) (by norm_num)
theorem B3418525 : Blo 1686043 3418525 := bbase (se 3 (by rfl) ⟨640973, by rfl⟩ : syracuseStep 3418525 = 1281947) (by norm_num)
theorem B8538533 : Blo 1686043 8538533 := bbase (se 4 (by rfl) ⟨800487, by rfl⟩ : syracuseStep 8538533 = 1600975) (by norm_num)
theorem B3795389 : Blo 1686043 3795389 := bbase (se 3 (by rfl) ⟨711635, by rfl⟩ : syracuseStep 3795389 = 1423271) (by norm_num)
theorem B5695973 : Blo 1686043 5695973 := bbase (se 4 (by rfl) ⟨533997, by rfl⟩ : syracuseStep 5695973 = 1067995) (by norm_num)
theorem B4385269 : Blo 1686043 4385269 := bbase (se 5 (by rfl) ⟨205559, by rfl⟩ : syracuseStep 4385269 = 411119) (by norm_num)
theorem B4327925 : Blo 1686043 4327925 := bbase (se 5 (by rfl) ⟨202871, by rfl⟩ : syracuseStep 4327925 = 405743) (by norm_num)
theorem B3795461 : Blo 1686043 3795461 := bbase (se 4 (by rfl) ⟨355824, by rfl⟩ : syracuseStep 3795461 = 711649) (by norm_num)
theorem B11536949 : Blo 1686043 11536949 := bbase (se 5 (by rfl) ⟨540794, by rfl⟩ : syracuseStep 11536949 = 1081589) (by norm_num)
theorem B5130805 : Blo 1686043 5130805 := bbase (se 5 (by rfl) ⟨240506, by rfl⟩ : syracuseStep 5130805 = 481013) (by norm_num)
theorem B2845253 : Blo 1686043 2845253 := bbase (se 4 (by rfl) ⟨266742, by rfl⟩ : syracuseStep 2845253 = 533485) (by norm_num)
theorem B3795533 : Blo 1686043 3795533 := bbase (se 3 (by rfl) ⟨711662, by rfl⟩ : syracuseStep 3795533 = 1423325) (by norm_num)
theorem B9734741 : Blo 1686043 9734741 := bbase (se 8 (by rfl) ⟨57039, by rfl⟩ : syracuseStep 9734741 = 114079) (by norm_num)
theorem B2026081 : Blo 1686043 2026081 := bbase (se 2 (by rfl) ⟨759780, by rfl⟩ : syracuseStep 2026081 = 1519561) (by norm_num)
theorem B6408821 : Blo 1686043 6408821 := bbase (se 5 (by rfl) ⟨300413, by rfl⟩ : syracuseStep 6408821 = 600827) (by norm_num)
theorem B3795605 : Blo 1686043 3795605 := bbase (se 6 (by rfl) ⟨88959, by rfl⟩ : syracuseStep 3795605 = 177919) (by norm_num)
theorem B2026153 : Blo 1686043 2026153 := bbase (se 2 (by rfl) ⟨759807, by rfl⟩ : syracuseStep 2026153 = 1519615) (by norm_num)
theorem B4270765 : Blo 1686043 4270765 := bbase (se 3 (by rfl) ⟨800768, by rfl⟩ : syracuseStep 4270765 = 1601537) (by norm_num)
theorem B2845381 : Blo 1686043 2845381 := bbase (se 4 (by rfl) ⟨266754, by rfl⟩ : syracuseStep 2845381 = 533509) (by norm_num)
theorem B5130949 : Blo 1686043 5130949 := bbase (se 4 (by rfl) ⟨481026, by rfl⟩ : syracuseStep 5130949 = 962053) (by norm_num)
theorem B6163157 : Blo 1686043 6163157 := bbase (se 7 (by rfl) ⟨72224, by rfl⟩ : syracuseStep 6163157 = 144449) (by norm_num)
theorem B3795677 : Blo 1686043 3795677 := bbase (se 3 (by rfl) ⟨711689, by rfl⟩ : syracuseStep 3795677 = 1423379) (by norm_num)
theorem B2845469 : Blo 1686043 2845469 := bbase (se 3 (by rfl) ⟨533525, by rfl⟩ : syracuseStep 2845469 = 1067051) (by norm_num)
theorem B4270877 : Blo 1686043 4270877 := bbase (se 3 (by rfl) ⟨800789, by rfl⟩ : syracuseStep 4270877 = 1601579) (by norm_num)
theorem B3795749 : Blo 1686043 3795749 := bbase (se 4 (by rfl) ⟨355851, by rfl⟩ : syracuseStep 3795749 = 711703) (by norm_num)
theorem B3795821 : Blo 1686043 3795821 := bbase (se 3 (by rfl) ⟨711716, by rfl⟩ : syracuseStep 3795821 = 1423433) (by norm_num)
theorem B5696405 : Blo 1686043 5696405 := bbase (se 6 (by rfl) ⟨133509, by rfl⟩ : syracuseStep 5696405 = 267019) (by norm_num)
theorem B2845597 : Blo 1686043 2845597 := bbase (se 3 (by rfl) ⟨533549, by rfl⟩ : syracuseStep 2845597 = 1067099) (by norm_num)
theorem B3795893 : Blo 1686043 3795893 := bbase (se 5 (by rfl) ⟨177932, by rfl⟩ : syracuseStep 3795893 = 355865) (by norm_num)
theorem B4271069 : Blo 1686043 4271069 := bbase (se 3 (by rfl) ⟨800825, by rfl⟩ : syracuseStep 4271069 = 1601651) (by norm_num)
theorem B2845685 : Blo 1686043 2845685 := bbase (se 5 (by rfl) ⟨133391, by rfl⟩ : syracuseStep 2845685 = 266783) (by norm_num)
theorem B3951613 : Blo 1686043 3951613 := bbase (se 3 (by rfl) ⟨740927, by rfl⟩ : syracuseStep 3951613 = 1481855) (by norm_num)
theorem B3795965 : Blo 1686043 3795965 := bbase (se 3 (by rfl) ⟨711743, by rfl⟩ : syracuseStep 3795965 = 1423487) (by norm_num)
theorem B8776757 : Blo 1686043 8776757 := bbase (se 5 (by rfl) ⟨411410, by rfl⟩ : syracuseStep 8776757 = 822821) (by norm_num)
theorem B3796037 : Blo 1686043 3796037 := bbase (se 4 (by rfl) ⟨355878, by rfl⟩ : syracuseStep 3796037 = 711757) (by norm_num)
theorem B2845813 : Blo 1686043 2845813 := bbase (se 5 (by rfl) ⟨133397, by rfl⟩ : syracuseStep 2845813 = 266795) (by norm_num)
theorem B2403445 : Blo 1686043 2403445 := bbase (se 5 (by rfl) ⟨112661, by rfl⟩ : syracuseStep 2403445 = 225323) (by norm_num)
theorem B3796109 : Blo 1686043 3796109 := bbase (se 3 (by rfl) ⟨711770, by rfl⟩ : syracuseStep 3796109 = 1423541) (by norm_num)
theorem B2845901 : Blo 1686043 2845901 := bbase (se 3 (by rfl) ⟨533606, by rfl⟩ : syracuseStep 2845901 = 1067213) (by norm_num)
theorem B3796181 : Blo 1686043 3796181 := bbase (se 7 (by rfl) ⟨44486, by rfl⟩ : syracuseStep 3796181 = 88973) (by norm_num)
theorem B13864213 : Blo 1686043 13864213 := bbase (se 6 (by rfl) ⟨324942, by rfl⟩ : syracuseStep 13864213 = 649885) (by norm_num)
theorem B3796253 : Blo 1686043 3796253 := bbase (se 3 (by rfl) ⟨711797, by rfl⟩ : syracuseStep 3796253 = 1423595) (by norm_num)
theorem B4271413 : Blo 1686043 4271413 := bbase (se 5 (by rfl) ⟨200222, by rfl⟩ : syracuseStep 4271413 = 400445) (by norm_num)
theorem B8105285 : Blo 1686043 8105285 := bbase (se 4 (by rfl) ⟨759870, by rfl⟩ : syracuseStep 8105285 = 1519741) (by norm_num)
theorem B5696837 : Blo 1686043 5696837 := bbase (se 4 (by rfl) ⟨534078, by rfl⟩ : syracuseStep 5696837 = 1068157) (by norm_num)
theorem B2846029 : Blo 1686043 2846029 := bbase (se 3 (by rfl) ⟨533630, by rfl⟩ : syracuseStep 2846029 = 1067261) (by norm_num)
theorem B14404949 : Blo 1686043 14404949 := bbase (se 11 (by rfl) ⟨10550, by rfl⟩ : syracuseStep 14404949 = 21101) (by norm_num)
theorem B14601557 : Blo 1686043 14601557 := bbase (se 11 (by rfl) ⟨10694, by rfl⟩ : syracuseStep 14601557 = 21389) (by norm_num)
theorem B3796325 : Blo 1686043 3796325 := bbase (se 4 (by rfl) ⟨355905, by rfl⟩ : syracuseStep 3796325 = 711811) (by norm_num)
theorem B9498005 : Blo 1686043 9498005 := bbase (se 6 (by rfl) ⟨222609, by rfl⟩ : syracuseStep 9498005 = 445219) (by norm_num)
theorem B2846117 : Blo 1686043 2846117 := bbase (se 4 (by rfl) ⟨266823, by rfl⟩ : syracuseStep 2846117 = 533647) (by norm_num)
theorem B4271525 : Blo 1686043 4271525 := bbase (se 4 (by rfl) ⟨400455, by rfl⟩ : syracuseStep 4271525 = 800911) (by norm_num)
theorem B3796397 : Blo 1686043 3796397 := bbase (se 3 (by rfl) ⟨711824, by rfl⟩ : syracuseStep 3796397 = 1423649) (by norm_num)
theorem B2280893 : Blo 1686043 2280893 := bbase (se 3 (by rfl) ⟨427667, by rfl⟩ : syracuseStep 2280893 = 855335) (by norm_num)
theorem B3796469 : Blo 1686043 3796469 := bbase (se 5 (by rfl) ⟨177959, by rfl⟩ : syracuseStep 3796469 = 355919) (by norm_num)
theorem B6082037 : Blo 1686043 6082037 := bbase (se 5 (by rfl) ⟨285095, by rfl⟩ : syracuseStep 6082037 = 570191) (by norm_num)
theorem B3419653 : Blo 1686043 3419653 := bbase (se 4 (by rfl) ⟨320592, by rfl⟩ : syracuseStep 3419653 = 641185) (by norm_num)
theorem B7204373 : Blo 1686043 7204373 := bbase (se 6 (by rfl) ⟨168852, by rfl⟩ : syracuseStep 7204373 = 337705) (by norm_num)
theorem B2846245 : Blo 1686043 2846245 := bbase (se 4 (by rfl) ⟨266835, by rfl⟩ : syracuseStep 2846245 = 533671) (by norm_num)
theorem B3796541 : Blo 1686043 3796541 := bbase (se 3 (by rfl) ⟨711851, by rfl⟩ : syracuseStep 3796541 = 1423703) (by norm_num)
theorem B4271717 : Blo 1686043 4271717 := bbase (se 4 (by rfl) ⟨400473, by rfl⟩ : syracuseStep 4271717 = 800947) (by norm_num)
theorem B1691249 : Blo 1686043 1691249 := bbase (se 2 (by rfl) ⟨634218, by rfl⟩ : syracuseStep 1691249 = 1268437) (by norm_num)
theorem B4869749 : Blo 1686043 4869749 := bbase (se 5 (by rfl) ⟨228269, by rfl⟩ : syracuseStep 4869749 = 456539) (by norm_num)
theorem B2846333 : Blo 1686043 2846333 := bbase (se 3 (by rfl) ⟨533687, by rfl⟩ : syracuseStep 2846333 = 1067375) (by norm_num)
theorem B3796613 : Blo 1686043 3796613 := bbase (se 4 (by rfl) ⟨355932, by rfl⟩ : syracuseStep 3796613 = 711865) (by norm_num)
theorem B2027153 : Blo 1686043 2027153 := bbase (se 2 (by rfl) ⟨760182, by rfl⟩ : syracuseStep 2027153 = 1520365) (by norm_num)
theorem B9604757 : Blo 1686043 9604757 := bbase (se 6 (by rfl) ⟨225111, by rfl⟩ : syracuseStep 9604757 = 450223) (by norm_num)
theorem B8539829 : Blo 1686043 8539829 := bbase (se 5 (by rfl) ⟨400304, by rfl⟩ : syracuseStep 8539829 = 800609) (by norm_num)
theorem B3796685 : Blo 1686043 3796685 := bbase (se 3 (by rfl) ⟨711878, by rfl⟩ : syracuseStep 3796685 = 1423757) (by norm_num)
theorem B2846461 : Blo 1686043 2846461 := bbase (se 3 (by rfl) ⟨533711, by rfl⟩ : syracuseStep 2846461 = 1067423) (by norm_num)
theorem B3247885 : Blo 1686043 3247885 := bbase (se 3 (by rfl) ⟨608978, by rfl⟩ : syracuseStep 3247885 = 1217957) (by norm_num)
theorem B4804373 : Blo 1686043 4804373 := bbase (se 6 (by rfl) ⟨112602, by rfl⟩ : syracuseStep 4804373 = 225205) (by norm_num)
theorem B3796757 : Blo 1686043 3796757 := bbase (se 6 (by rfl) ⟨88986, by rfl⟩ : syracuseStep 3796757 = 177973) (by norm_num)
theorem B2846549 : Blo 1686043 2846549 := bbase (se 9 (by rfl) ⟨8339, by rfl⟩ : syracuseStep 2846549 = 16679) (by norm_num)
theorem B3796829 : Blo 1686043 3796829 := bbase (se 3 (by rfl) ⟨711905, by rfl⟩ : syracuseStep 3796829 = 1423811) (by norm_num)
theorem B3796901 : Blo 1686043 3796901 := bbase (se 4 (by rfl) ⟨355959, by rfl⟩ : syracuseStep 3796901 = 711919) (by norm_num)
theorem B4272061 : Blo 1686043 4272061 := bbase (se 3 (by rfl) ⟨801011, by rfl⟩ : syracuseStep 4272061 = 1602023) (by norm_num)
theorem B2133965 : Blo 1686043 2133965 := bbase (se 3 (by rfl) ⟨400118, by rfl⟩ : syracuseStep 2133965 = 800237) (by norm_num)
theorem B2846677 : Blo 1686043 2846677 := bbase (se 7 (by rfl) ⟨33359, by rfl⟩ : syracuseStep 2846677 = 66719) (by norm_num)
theorem B3796973 : Blo 1686043 3796973 := bbase (se 3 (by rfl) ⟨711932, by rfl⟩ : syracuseStep 3796973 = 1423865) (by norm_num)
theorem B2134021 : Blo 1686043 2134021 := bbase (se 4 (by rfl) ⟨200064, by rfl⟩ : syracuseStep 2134021 = 400129) (by norm_num)
theorem B2846765 : Blo 1686043 2846765 := bbase (se 3 (by rfl) ⟨533768, by rfl⟩ : syracuseStep 2846765 = 1067537) (by norm_num)
theorem B4272173 : Blo 1686043 4272173 := bbase (se 3 (by rfl) ⟨801032, by rfl⟩ : syracuseStep 4272173 = 1602065) (by norm_num)
theorem B3797045 : Blo 1686043 3797045 := bbase (se 5 (by rfl) ⟨177986, by rfl⟩ : syracuseStep 3797045 = 355973) (by norm_num)
theorem B6082613 : Blo 1686043 6082613 := bbase (se 5 (by rfl) ⟨285122, by rfl⟩ : syracuseStep 6082613 = 570245) (by norm_num)
theorem B2134117 : Blo 1686043 2134117 := bbase (se 4 (by rfl) ⟨200073, by rfl⟩ : syracuseStep 2134117 = 400147) (by norm_num)
theorem B3797117 : Blo 1686043 3797117 := bbase (se 3 (by rfl) ⟨711959, by rfl⟩ : syracuseStep 3797117 = 1423919) (by norm_num)
theorem B2846893 : Blo 1686043 2846893 := bbase (se 3 (by rfl) ⟨533792, by rfl⟩ : syracuseStep 2846893 = 1067585) (by norm_num)
theorem B3797189 : Blo 1686043 3797189 := bbase (se 4 (by rfl) ⟨355986, by rfl⟩ : syracuseStep 3797189 = 711973) (by norm_num)
theorem B10809557 : Blo 1686043 10809557 := bbase (se 7 (by rfl) ⟨126674, by rfl⟩ : syracuseStep 10809557 = 253349) (by norm_num)
theorem B4272365 : Blo 1686043 4272365 := bbase (se 3 (by rfl) ⟨801068, by rfl⟩ : syracuseStep 4272365 = 1602137) (by norm_num)
theorem B2846981 : Blo 1686043 2846981 := bbase (se 4 (by rfl) ⟨266904, by rfl⟩ : syracuseStep 2846981 = 533809) (by norm_num)
theorem B4329733 : Blo 1686043 4329733 := bbase (se 4 (by rfl) ⟨405912, by rfl⟩ : syracuseStep 4329733 = 811825) (by norm_num)
theorem B3797261 : Blo 1686043 3797261 := bbase (se 3 (by rfl) ⟨711986, by rfl⟩ : syracuseStep 3797261 = 1423973) (by norm_num)
theorem B2134289 : Blo 1686043 2134289 := bbase (se 2 (by rfl) ⟨800358, by rfl⟩ : syracuseStep 2134289 = 1600717) (by norm_num)
theorem B6836501 : Blo 1686043 6836501 := bbase (se 6 (by rfl) ⟨160230, by rfl⟩ : syracuseStep 6836501 = 320461) (by norm_num)
theorem B5402933 : Blo 1686043 5402933 := bbase (se 5 (by rfl) ⟨253262, by rfl⟩ : syracuseStep 5402933 = 506525) (by norm_num)
theorem B2027845 : Blo 1686043 2027845 := bbase (se 4 (by rfl) ⟨190110, by rfl⟩ : syracuseStep 2027845 = 380221) (by norm_num)
theorem B2134345 : Blo 1686043 2134345 := bbase (se 2 (by rfl) ⟨800379, by rfl⟩ : syracuseStep 2134345 = 1600759) (by norm_num)
theorem B2027849 : Blo 1686043 2027849 := bbase (se 2 (by rfl) ⟨760443, by rfl⟩ : syracuseStep 2027849 = 1520887) (by norm_num)
theorem B5476693 : Blo 1686043 5476693 := bbase (se 10 (by rfl) ⟨8022, by rfl⟩ : syracuseStep 5476693 = 16045) (by norm_num)
theorem B3797333 : Blo 1686043 3797333 := bbase (se 10 (by rfl) ⟨5562, by rfl⟩ : syracuseStep 3797333 = 11125) (by norm_num)
theorem B1896817 : Blo 1686043 1896817 := bbase (se 2 (by rfl) ⟨711306, by rfl⟩ : syracuseStep 1896817 = 1422613) (by norm_num)
theorem B2847109 : Blo 1686043 2847109 := bbase (se 4 (by rfl) ⟨266916, by rfl⟩ : syracuseStep 2847109 = 533833) (by norm_num)
theorem B1896853 : Blo 1686043 1896853 := bbase (se 6 (by rfl) ⟨44457, by rfl⟩ : syracuseStep 1896853 = 88915) (by norm_num)
theorem B3797405 : Blo 1686043 3797405 := bbase (se 3 (by rfl) ⟨712013, by rfl⟩ : syracuseStep 3797405 = 1424027) (by norm_num)
theorem B2134441 : Blo 1686043 2134441 := bbase (se 2 (by rfl) ⟨800415, by rfl⟩ : syracuseStep 2134441 = 1600831) (by norm_num)
theorem B4805045 : Blo 1686043 4805045 := bbase (se 5 (by rfl) ⟨225236, by rfl⟩ : syracuseStep 4805045 = 450473) (by norm_num)
theorem B1896889 : Blo 1686043 1896889 := bbase (se 2 (by rfl) ⟨711333, by rfl⟩ : syracuseStep 1896889 = 1422667) (by norm_num)
theorem B1896925 : Blo 1686043 1896925 := bbase (se 3 (by rfl) ⟨355673, by rfl⟩ : syracuseStep 1896925 = 711347) (by norm_num)
theorem B2847197 : Blo 1686043 2847197 := bbase (se 3 (by rfl) ⟨533849, by rfl⟩ : syracuseStep 2847197 = 1067699) (by norm_num)
theorem B3797477 : Blo 1686043 3797477 := bbase (se 4 (by rfl) ⟨356013, by rfl⟩ : syracuseStep 3797477 = 712027) (by norm_num)
theorem B1896961 : Blo 1686043 1896961 := bbase (se 2 (by rfl) ⟨711360, by rfl⟩ : syracuseStep 1896961 = 1422721) (by norm_num)
theorem B7205381 : Blo 1686043 7205381 := bbase (se 4 (by rfl) ⟨675504, by rfl⟩ : syracuseStep 7205381 = 1351009) (by norm_num)
theorem B4051469 : Blo 1686043 4051469 := bbase (se 3 (by rfl) ⟨759650, by rfl⟩ : syracuseStep 4051469 = 1519301) (by norm_num)
theorem B1896997 : Blo 1686043 1896997 := bbase (se 4 (by rfl) ⟨177843, by rfl⟩ : syracuseStep 1896997 = 355687) (by norm_num)
theorem B3797549 : Blo 1686043 3797549 := bbase (se 3 (by rfl) ⟨712040, by rfl⟩ : syracuseStep 3797549 = 1424081) (by norm_num)
theorem B4272709 : Blo 1686043 4272709 := bbase (se 4 (by rfl) ⟨400566, by rfl⟩ : syracuseStep 4272709 = 801133) (by norm_num)
theorem B1897033 : Blo 1686043 1897033 := bbase (se 2 (by rfl) ⟨711387, by rfl⟩ : syracuseStep 1897033 = 1422775) (by norm_num)
theorem B2134613 : Blo 1686043 2134613 := bbase (se 8 (by rfl) ⟨12507, by rfl⟩ : syracuseStep 2134613 = 25015) (by norm_num)
theorem B2847325 : Blo 1686043 2847325 := bbase (se 3 (by rfl) ⟨533873, by rfl⟩ : syracuseStep 2847325 = 1067747) (by norm_num)
theorem B1897069 : Blo 1686043 1897069 := bbase (se 3 (by rfl) ⟨355700, by rfl⟩ : syracuseStep 1897069 = 711401) (by norm_num)
theorem B1733233 : Blo 1686043 1733233 := bbase (se 2 (by rfl) ⟨649962, by rfl⟩ : syracuseStep 1733233 = 1299925) (by norm_num)
theorem B3797621 : Blo 1686043 3797621 := bbase (se 5 (by rfl) ⟨178013, by rfl⟩ : syracuseStep 3797621 = 356027) (by norm_num)
theorem B2134669 : Blo 1686043 2134669 := bbase (se 3 (by rfl) ⟨400250, by rfl⟩ : syracuseStep 2134669 = 800501) (by norm_num)
theorem B1897105 : Blo 1686043 1897105 := bbase (se 2 (by rfl) ⟨711414, by rfl⟩ : syracuseStep 1897105 = 1422829) (by norm_num)
theorem B1897141 : Blo 1686043 1897141 := bbase (se 5 (by rfl) ⟨88928, by rfl⟩ : syracuseStep 1897141 = 177857) (by norm_num)
theorem B2847413 : Blo 1686043 2847413 := bbase (se 5 (by rfl) ⟨133472, by rfl⟩ : syracuseStep 2847413 = 266945) (by norm_num)
theorem B4272821 : Blo 1686043 4272821 := bbase (se 5 (by rfl) ⟨200288, by rfl⟩ : syracuseStep 4272821 = 400577) (by norm_num)
theorem B3797693 : Blo 1686043 3797693 := bbase (se 3 (by rfl) ⟨712067, by rfl⟩ : syracuseStep 3797693 = 1424135) (by norm_num)
theorem B3601093 : Blo 1686043 3601093 := bbase (se 4 (by rfl) ⟨337602, by rfl⟩ : syracuseStep 3601093 = 675205) (by norm_num)
theorem B1897177 : Blo 1686043 1897177 := bbase (se 2 (by rfl) ⟨711441, by rfl⟩ : syracuseStep 1897177 = 1422883) (by norm_num)
theorem B3420893 : Blo 1686043 3420893 := bbase (se 3 (by rfl) ⟨641417, by rfl⟩ : syracuseStep 3420893 = 1282835) (by norm_num)
theorem B2134765 : Blo 1686043 2134765 := bbase (se 3 (by rfl) ⟨400268, by rfl⟩ : syracuseStep 2134765 = 800537) (by norm_num)
theorem B1897213 : Blo 1686043 1897213 := bbase (se 3 (by rfl) ⟨355727, by rfl⟩ : syracuseStep 1897213 = 711455) (by norm_num)
theorem B3797765 : Blo 1686043 3797765 := bbase (se 4 (by rfl) ⟨356040, by rfl⟩ : syracuseStep 3797765 = 712081) (by norm_num)
theorem B1897249 : Blo 1686043 1897249 := bbase (se 2 (by rfl) ⟨711468, by rfl⟩ : syracuseStep 1897249 = 1422937) (by norm_num)
theorem B2847541 : Blo 1686043 2847541 := bbase (se 5 (by rfl) ⟨133478, by rfl⟩ : syracuseStep 2847541 = 266957) (by norm_num)
theorem B1897285 : Blo 1686043 1897285 := bbase (se 4 (by rfl) ⟨177870, by rfl⟩ : syracuseStep 1897285 = 355741) (by norm_num)
theorem B3797837 : Blo 1686043 3797837 := bbase (se 3 (by rfl) ⟨712094, by rfl⟩ : syracuseStep 3797837 = 1424189) (by norm_num)
theorem B20288341 : Blo 1686043 20288341 := bbase (se 9 (by rfl) ⟨59438, by rfl⟩ : syracuseStep 20288341 = 118877) (by norm_num)
theorem B4805477 : Blo 1686043 4805477 := bbase (se 4 (by rfl) ⟨450513, by rfl⟩ : syracuseStep 4805477 = 901027) (by norm_num)
theorem B1897321 : Blo 1686043 1897321 := bbase (se 2 (by rfl) ⟨711495, by rfl⟩ : syracuseStep 1897321 = 1422991) (by norm_num)
theorem B1897357 : Blo 1686043 1897357 := bbase (se 3 (by rfl) ⟨355754, by rfl⟩ : syracuseStep 1897357 = 711509) (by norm_num)
theorem B2847629 : Blo 1686043 2847629 := bbase (se 3 (by rfl) ⟨533930, by rfl⟩ : syracuseStep 2847629 = 1067861) (by norm_num)
theorem B3797909 : Blo 1686043 3797909 := bbase (se 6 (by rfl) ⟨89013, by rfl⟩ : syracuseStep 3797909 = 178027) (by norm_num)
theorem B2134937 : Blo 1686043 2134937 := bbase (se 2 (by rfl) ⟨800601, by rfl⟩ : syracuseStep 2134937 = 1601203) (by norm_num)
theorem B1897393 : Blo 1686043 1897393 := bbase (se 2 (by rfl) ⟨711522, by rfl⟩ : syracuseStep 1897393 = 1423045) (by norm_num)
theorem B11539381 : Blo 1686043 11539381 := bbase (se 5 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 11539381 = 1081817) (by norm_num)
theorem B8541125 : Blo 1686043 8541125 := bbase (se 4 (by rfl) ⟨800730, by rfl⟩ : syracuseStep 8541125 = 1601461) (by norm_num)
theorem B8221637 : Blo 1686043 8221637 := bbase (se 4 (by rfl) ⟨770778, by rfl⟩ : syracuseStep 8221637 = 1541557) (by norm_num)
theorem B2134993 : Blo 1686043 2134993 := bbase (se 2 (by rfl) ⟨800622, by rfl⟩ : syracuseStep 2134993 = 1601245) (by norm_num)
theorem B1897429 : Blo 1686043 1897429 := bbase (se 7 (by rfl) ⟨22235, by rfl⟩ : syracuseStep 1897429 = 44471) (by norm_num)
theorem B3797981 : Blo 1686043 3797981 := bbase (se 3 (by rfl) ⟨712121, by rfl⟩ : syracuseStep 3797981 = 1424243) (by norm_num)
theorem B1897465 : Blo 1686043 1897465 := bbase (se 2 (by rfl) ⟨711549, by rfl⟩ : syracuseStep 1897465 = 1423099) (by norm_num)
theorem B2847757 : Blo 1686043 2847757 := bbase (se 3 (by rfl) ⟨533954, by rfl⟩ : syracuseStep 2847757 = 1067909) (by norm_num)
theorem B1897501 : Blo 1686043 1897501 := bbase (se 3 (by rfl) ⟨355781, by rfl⟩ : syracuseStep 1897501 = 711563) (by norm_num)
theorem B3798053 : Blo 1686043 3798053 := bbase (se 4 (by rfl) ⟨356067, by rfl⟩ : syracuseStep 3798053 = 712135) (by norm_num)
theorem B2135089 : Blo 1686043 2135089 := bbase (se 2 (by rfl) ⟨800658, by rfl⟩ : syracuseStep 2135089 = 1601317) (by norm_num)
theorem B1897537 : Blo 1686043 1897537 := bbase (se 2 (by rfl) ⟨711576, by rfl⟩ : syracuseStep 1897537 = 1423153) (by norm_num)
theorem B6403157 : Blo 1686043 6403157 := bbase (se 8 (by rfl) ⟨37518, by rfl⟩ : syracuseStep 6403157 = 75037) (by norm_num)
theorem B1709149 : Blo 1686043 1709149 := bbase (se 3 (by rfl) ⟨320465, by rfl⟩ : syracuseStep 1709149 = 640931) (by norm_num)
theorem B1897573 : Blo 1686043 1897573 := bbase (se 4 (by rfl) ⟨177897, by rfl⟩ : syracuseStep 1897573 = 355795) (by norm_num)
theorem B2847845 : Blo 1686043 2847845 := bbase (se 4 (by rfl) ⟨266985, by rfl⟩ : syracuseStep 2847845 = 533971) (by norm_num)
theorem B1897609 : Blo 1686043 1897609 := bbase (se 2 (by rfl) ⟨711603, by rfl⟩ : syracuseStep 1897609 = 1423207) (by norm_num)
theorem B1897645 : Blo 1686043 1897645 := bbase (se 3 (by rfl) ⟨355808, by rfl⟩ : syracuseStep 1897645 = 711617) (by norm_num)
theorem B3601597 : Blo 1686043 3601597 := bbase (se 3 (by rfl) ⟨675299, by rfl⟩ : syracuseStep 3601597 = 1350599) (by norm_num)
theorem B1897681 : Blo 1686043 1897681 := bbase (se 2 (by rfl) ⟨711630, by rfl⟩ : syracuseStep 1897681 = 1423261) (by norm_num)
theorem B2135261 : Blo 1686043 2135261 := bbase (se 3 (by rfl) ⟨400361, by rfl⟩ : syracuseStep 2135261 = 800723) (by norm_num)
theorem B2847973 : Blo 1686043 2847973 := bbase (se 4 (by rfl) ⟨266997, by rfl⟩ : syracuseStep 2847973 = 533995) (by norm_num)
theorem B1897717 : Blo 1686043 1897717 := bbase (se 5 (by rfl) ⟨88955, by rfl⟩ : syracuseStep 1897717 = 177911) (by norm_num)
theorem B2135317 : Blo 1686043 2135317 := bbase (se 6 (by rfl) ⟨50046, by rfl⟩ : syracuseStep 2135317 = 100093) (by norm_num)
theorem B1897753 : Blo 1686043 1897753 := bbase (se 2 (by rfl) ⟨711657, by rfl⟩ : syracuseStep 1897753 = 1423315) (by norm_num)
theorem B1897789 : Blo 1686043 1897789 := bbase (se 3 (by rfl) ⟨355835, by rfl⟩ : syracuseStep 1897789 = 711671) (by norm_num)
theorem B2848061 : Blo 1686043 2848061 := bbase (se 3 (by rfl) ⟨534011, by rfl⟩ : syracuseStep 2848061 = 1068023) (by norm_num)
theorem B1897825 : Blo 1686043 1897825 := bbase (se 2 (by rfl) ⟨711684, by rfl⟩ : syracuseStep 1897825 = 1423369) (by norm_num)
theorem B4560229 : Blo 1686043 4560229 := bbase (se 4 (by rfl) ⟨427521, by rfl⟩ : syracuseStep 4560229 = 855043) (by norm_num)
theorem B6403445 : Blo 1686043 6403445 := bbase (se 5 (by rfl) ⟨300161, by rfl⟩ : syracuseStep 6403445 = 600323) (by norm_num)
theorem B2135413 : Blo 1686043 2135413 := bbase (se 5 (by rfl) ⟨100097, by rfl⟩ : syracuseStep 2135413 = 200195) (by norm_num)
theorem B1897861 : Blo 1686043 1897861 := bbase (se 4 (by rfl) ⟨177924, by rfl⟩ : syracuseStep 1897861 = 355849) (by norm_num)
theorem B19469717 : Blo 1686043 19469717 := bbase (se 6 (by rfl) ⟨456321, by rfl⟩ : syracuseStep 19469717 = 912643) (by norm_num)
theorem B5690789 : Blo 1686043 5690789 := bbase (se 4 (by rfl) ⟨533511, by rfl⟩ : syracuseStep 5690789 = 1067023) (by norm_num)
theorem B1897897 : Blo 1686043 1897897 := bbase (se 2 (by rfl) ⟨711711, by rfl⟩ : syracuseStep 1897897 = 1423423) (by norm_num)
theorem B2848189 : Blo 1686043 2848189 := bbase (se 3 (by rfl) ⟨534035, by rfl⟩ : syracuseStep 2848189 = 1068071) (by norm_num)
theorem B2700749 : Blo 1686043 2700749 := bbase (se 3 (by rfl) ⟨506390, by rfl⟩ : syracuseStep 2700749 = 1012781) (by norm_num)
theorem B1897933 : Blo 1686043 1897933 := bbase (se 3 (by rfl) ⟨355862, by rfl⟩ : syracuseStep 1897933 = 711725) (by norm_num)
theorem B1897969 : Blo 1686043 1897969 := bbase (se 2 (by rfl) ⟨711738, by rfl⟩ : syracuseStep 1897969 = 1423477) (by norm_num)
theorem B1898005 : Blo 1686043 1898005 := bbase (se 6 (by rfl) ⟨44484, by rfl⟩ : syracuseStep 1898005 = 88969) (by norm_num)
theorem B2848277 : Blo 1686043 2848277 := bbase (se 6 (by rfl) ⟨66756, by rfl⟩ : syracuseStep 2848277 = 133513) (by norm_num)
theorem B2135585 : Blo 1686043 2135585 := bbase (se 2 (by rfl) ⟨800844, by rfl⟩ : syracuseStep 2135585 = 1601689) (by norm_num)
theorem B1898041 : Blo 1686043 1898041 := bbase (se 2 (by rfl) ⟨711765, by rfl⟩ : syracuseStep 1898041 = 1423531) (by norm_num)
theorem B4806229 : Blo 1686043 4806229 := bbase (se 8 (by rfl) ⟨28161, by rfl⟩ : syracuseStep 4806229 = 56323) (by norm_num)
theorem B2135641 : Blo 1686043 2135641 := bbase (se 2 (by rfl) ⟨800865, by rfl⟩ : syracuseStep 2135641 = 1601731) (by norm_num)
theorem B1898077 : Blo 1686043 1898077 := bbase (se 3 (by rfl) ⟨355889, by rfl⟩ : syracuseStep 1898077 = 711779) (by norm_num)
theorem B1898113 : Blo 1686043 1898113 := bbase (se 2 (by rfl) ⟨711792, by rfl⟩ : syracuseStep 1898113 = 1423585) (by norm_num)
theorem B2848405 : Blo 1686043 2848405 := bbase (se 6 (by rfl) ⟨66759, by rfl⟩ : syracuseStep 2848405 = 133519) (by norm_num)
theorem B1898149 : Blo 1686043 1898149 := bbase (se 4 (by rfl) ⟨177951, by rfl⟩ : syracuseStep 1898149 = 355903) (by norm_num)
theorem B2135737 : Blo 1686043 2135737 := bbase (se 2 (by rfl) ⟨800901, by rfl⟩ : syracuseStep 2135737 = 1601803) (by norm_num)
theorem B1898185 : Blo 1686043 1898185 := bbase (se 2 (by rfl) ⟨711819, by rfl⟩ : syracuseStep 1898185 = 1423639) (by norm_num)
theorem B1898221 : Blo 1686043 1898221 := bbase (se 3 (by rfl) ⟨355916, by rfl⟩ : syracuseStep 1898221 = 711833) (by norm_num)
theorem B2848493 : Blo 1686043 2848493 := bbase (se 3 (by rfl) ⟨534092, by rfl⟩ : syracuseStep 2848493 = 1068185) (by norm_num)
theorem B1898257 : Blo 1686043 1898257 := bbase (se 2 (by rfl) ⟨711846, by rfl⟩ : syracuseStep 1898257 = 1423693) (by norm_num)
theorem B2529077 : Blo 1686043 2529077 := bbase (se 5 (by rfl) ⟨118550, by rfl⟩ : syracuseStep 2529077 = 237101) (by norm_num)
theorem B1898293 : Blo 1686043 1898293 := bbase (se 5 (by rfl) ⟨88982, by rfl⟩ : syracuseStep 1898293 = 177965) (by norm_num)
theorem B2529101 : Blo 1686043 2529101 := bbase (se 3 (by rfl) ⟨474206, by rfl⟩ : syracuseStep 2529101 = 948413) (by norm_num)
theorem B5691221 : Blo 1686043 5691221 := bbase (se 9 (by rfl) ⟨16673, by rfl⟩ : syracuseStep 5691221 = 33347) (by norm_num)
theorem B1898329 : Blo 1686043 1898329 := bbase (se 2 (by rfl) ⟨711873, by rfl⟩ : syracuseStep 1898329 = 1423747) (by norm_num)
theorem B2529125 : Blo 1686043 2529125 := bbase (se 4 (by rfl) ⟨237105, by rfl⟩ : syracuseStep 2529125 = 474211) (by norm_num)
theorem B2135909 : Blo 1686043 2135909 := bbase (se 4 (by rfl) ⟨200241, by rfl⟩ : syracuseStep 2135909 = 400483) (by norm_num)
theorem B4052845 : Blo 1686043 4052845 := bbase (se 3 (by rfl) ⟨759908, by rfl⟩ : syracuseStep 4052845 = 1519817) (by norm_num)
theorem B2529149 : Blo 1686043 2529149 := bbase (se 3 (by rfl) ⟨474215, by rfl⟩ : syracuseStep 2529149 = 948431) (by norm_num)
theorem B1898365 : Blo 1686043 1898365 := bbase (se 3 (by rfl) ⟨355943, by rfl⟩ : syracuseStep 1898365 = 711887) (by norm_num)
theorem B1709957 : Blo 1686043 1709957 := bbase (se 4 (by rfl) ⟨160308, by rfl⟩ : syracuseStep 1709957 = 320617) (by norm_num)
theorem B2529173 : Blo 1686043 2529173 := bbase (se 6 (by rfl) ⟨59277, by rfl⟩ : syracuseStep 2529173 = 118555) (by norm_num)
theorem B2135965 : Blo 1686043 2135965 := bbase (se 3 (by rfl) ⟨400493, by rfl⟩ : syracuseStep 2135965 = 800987) (by norm_num)
theorem B1898401 : Blo 1686043 1898401 := bbase (se 2 (by rfl) ⟨711900, by rfl⟩ : syracuseStep 1898401 = 1423801) (by norm_num)
theorem B3200933 : Blo 1686043 3200933 := bbase (se 4 (by rfl) ⟨300087, by rfl⟩ : syracuseStep 3200933 = 600175) (by norm_num)
theorem B2529197 : Blo 1686043 2529197 := bbase (se 3 (by rfl) ⟨474224, by rfl⟩ : syracuseStep 2529197 = 948449) (by norm_num)
theorem B2529221 : Blo 1686043 2529221 := bbase (se 4 (by rfl) ⟨237114, by rfl⟩ : syracuseStep 2529221 = 474229) (by norm_num)
theorem B1898437 : Blo 1686043 1898437 := bbase (se 4 (by rfl) ⟨177978, by rfl⟩ : syracuseStep 1898437 = 355957) (by norm_num)
theorem B2529245 : Blo 1686043 2529245 := bbase (se 3 (by rfl) ⟨474233, by rfl⟩ : syracuseStep 2529245 = 948467) (by norm_num)
theorem B1898473 : Blo 1686043 1898473 := bbase (se 2 (by rfl) ⟨711927, by rfl⟩ : syracuseStep 1898473 = 1423855) (by norm_num)
theorem B2529269 : Blo 1686043 2529269 := bbase (se 5 (by rfl) ⟨118559, by rfl⟩ : syracuseStep 2529269 = 237119) (by norm_num)
theorem B2136061 : Blo 1686043 2136061 := bbase (se 3 (by rfl) ⟨400511, by rfl⟩ : syracuseStep 2136061 = 801023) (by norm_num)
theorem B2529293 : Blo 1686043 2529293 := bbase (se 3 (by rfl) ⟨474242, by rfl⟩ : syracuseStep 2529293 = 948485) (by norm_num)
theorem B1898509 : Blo 1686043 1898509 := bbase (se 3 (by rfl) ⟨355970, by rfl⟩ : syracuseStep 1898509 = 711941) (by norm_num)
theorem B2529317 : Blo 1686043 2529317 := bbase (se 4 (by rfl) ⟨237123, by rfl⟩ : syracuseStep 2529317 = 474247) (by norm_num)
theorem B1898545 : Blo 1686043 1898545 := bbase (se 2 (by rfl) ⟨711954, by rfl⟩ : syracuseStep 1898545 = 1423909) (by norm_num)
theorem B3602485 : Blo 1686043 3602485 := bbase (se 5 (by rfl) ⟨168866, by rfl⟩ : syracuseStep 3602485 = 337733) (by norm_num)
theorem B2529341 : Blo 1686043 2529341 := bbase (se 3 (by rfl) ⟨474251, by rfl⟩ : syracuseStep 2529341 = 948503) (by norm_num)
theorem B2529365 : Blo 1686043 2529365 := bbase (se 8 (by rfl) ⟨14820, by rfl⟩ : syracuseStep 2529365 = 29641) (by norm_num)
theorem B1898581 : Blo 1686043 1898581 := bbase (se 8 (by rfl) ⟨11124, by rfl⟩ : syracuseStep 1898581 = 22249) (by norm_num)
theorem B2529389 : Blo 1686043 2529389 := bbase (se 3 (by rfl) ⟨474260, by rfl⟩ : syracuseStep 2529389 = 948521) (by norm_num)
theorem B1898617 : Blo 1686043 1898617 := bbase (se 2 (by rfl) ⟨711981, by rfl⟩ : syracuseStep 1898617 = 1423963) (by norm_num)
theorem B2529413 : Blo 1686043 2529413 := bbase (se 4 (by rfl) ⟨237132, by rfl⟩ : syracuseStep 2529413 = 474265) (by norm_num)
theorem B2529437 : Blo 1686043 2529437 := bbase (se 3 (by rfl) ⟨474269, by rfl⟩ : syracuseStep 2529437 = 948539) (by norm_num)
theorem B1898653 : Blo 1686043 1898653 := bbase (se 3 (by rfl) ⟨355997, by rfl⟩ : syracuseStep 1898653 = 711995) (by norm_num)
theorem B2136233 : Blo 1686043 2136233 := bbase (se 2 (by rfl) ⟨801087, by rfl⟩ : syracuseStep 2136233 = 1602175) (by norm_num)
theorem B2529461 : Blo 1686043 2529461 := bbase (se 5 (by rfl) ⟨118568, by rfl⟩ : syracuseStep 2529461 = 237137) (by norm_num)
theorem B1898689 : Blo 1686043 1898689 := bbase (se 2 (by rfl) ⟨712008, by rfl⟩ : syracuseStep 1898689 = 1424017) (by norm_num)
theorem B3201221 : Blo 1686043 3201221 := bbase (se 4 (by rfl) ⟨300114, by rfl⟩ : syracuseStep 3201221 = 600229) (by norm_num)
theorem B2529485 : Blo 1686043 2529485 := bbase (se 3 (by rfl) ⟨474278, by rfl⟩ : syracuseStep 2529485 = 948557) (by norm_num)
theorem B8542421 : Blo 1686043 8542421 := bbase (se 7 (by rfl) ⟨100106, by rfl⟩ : syracuseStep 8542421 = 200213) (by norm_num)
theorem B2136289 : Blo 1686043 2136289 := bbase (se 2 (by rfl) ⟨801108, by rfl⟩ : syracuseStep 2136289 = 1602217) (by norm_num)
theorem B2529509 : Blo 1686043 2529509 := bbase (se 4 (by rfl) ⟨237141, by rfl⟩ : syracuseStep 2529509 = 474283) (by norm_num)
theorem B1898725 : Blo 1686043 1898725 := bbase (se 4 (by rfl) ⟨178005, by rfl⟩ : syracuseStep 1898725 = 356011) (by norm_num)
theorem B7207157 : Blo 1686043 7207157 := bbase (se 5 (by rfl) ⟨337835, by rfl⟩ : syracuseStep 7207157 = 675671) (by norm_num)
theorem B2529533 : Blo 1686043 2529533 := bbase (se 3 (by rfl) ⟨474287, by rfl⟩ : syracuseStep 2529533 = 948575) (by norm_num)
theorem B5691653 : Blo 1686043 5691653 := bbase (se 4 (by rfl) ⟨533592, by rfl⟩ : syracuseStep 5691653 = 1067185) (by norm_num)
theorem B1898761 : Blo 1686043 1898761 := bbase (se 2 (by rfl) ⟨712035, by rfl⟩ : syracuseStep 1898761 = 1424071) (by norm_num)
theorem B2529557 : Blo 1686043 2529557 := bbase (se 6 (by rfl) ⟨59286, by rfl⟩ : syracuseStep 2529557 = 118573) (by norm_num)
theorem B2529581 : Blo 1686043 2529581 := bbase (se 3 (by rfl) ⟨474296, by rfl⟩ : syracuseStep 2529581 = 948593) (by norm_num)
theorem B1898797 : Blo 1686043 1898797 := bbase (se 3 (by rfl) ⟨356024, by rfl⟩ : syracuseStep 1898797 = 712049) (by norm_num)
theorem B13678901 : Blo 1686043 13678901 := bbase (se 5 (by rfl) ⟨641198, by rfl⟩ : syracuseStep 13678901 = 1282397) (by norm_num)
theorem B2136385 : Blo 1686043 2136385 := bbase (se 2 (by rfl) ⟨801144, by rfl⟩ : syracuseStep 2136385 = 1602289) (by norm_num)
theorem B2529605 : Blo 1686043 2529605 := bbase (se 4 (by rfl) ⟨237150, by rfl⟩ : syracuseStep 2529605 = 474301) (by norm_num)
theorem B1898833 : Blo 1686043 1898833 := bbase (se 2 (by rfl) ⟨712062, by rfl⟩ : syracuseStep 1898833 = 1424125) (by norm_num)
theorem B3201373 : Blo 1686043 3201373 := bbase (se 3 (by rfl) ⟨600257, by rfl⟩ : syracuseStep 3201373 = 1200515) (by norm_num)
theorem B2529629 : Blo 1686043 2529629 := bbase (se 3 (by rfl) ⟨474305, by rfl⟩ : syracuseStep 2529629 = 948611) (by norm_num)
theorem B2529653 : Blo 1686043 2529653 := bbase (se 5 (by rfl) ⟨118577, by rfl⟩ : syracuseStep 2529653 = 237155) (by norm_num)
theorem B1898869 : Blo 1686043 1898869 := bbase (se 5 (by rfl) ⟨89009, by rfl⟩ : syracuseStep 1898869 = 178019) (by norm_num)
theorem B2529677 : Blo 1686043 2529677 := bbase (se 3 (by rfl) ⟨474314, by rfl⟩ : syracuseStep 2529677 = 948629) (by norm_num)
theorem B1898905 : Blo 1686043 1898905 := bbase (se 2 (by rfl) ⟨712089, by rfl⟩ : syracuseStep 1898905 = 1424179) (by norm_num)
theorem B2529701 : Blo 1686043 2529701 := bbase (se 4 (by rfl) ⟨237159, by rfl⟩ : syracuseStep 2529701 = 474319) (by norm_num)
theorem B2529725 : Blo 1686043 2529725 := bbase (se 3 (by rfl) ⟨474323, by rfl⟩ : syracuseStep 2529725 = 948647) (by norm_num)
theorem B1898941 : Blo 1686043 1898941 := bbase (se 3 (by rfl) ⟨356051, by rfl⟩ : syracuseStep 1898941 = 712103) (by norm_num)
theorem B5405125 : Blo 1686043 5405125 := bbase (se 4 (by rfl) ⟨506730, by rfl⟩ : syracuseStep 5405125 = 1013461) (by norm_num)
theorem B2529749 : Blo 1686043 2529749 := bbase (se 7 (by rfl) ⟨29645, by rfl⟩ : syracuseStep 2529749 = 59291) (by norm_num)
theorem B1898977 : Blo 1686043 1898977 := bbase (se 2 (by rfl) ⟨712116, by rfl⟩ : syracuseStep 1898977 = 1424233) (by norm_num)
theorem B2529773 : Blo 1686043 2529773 := bbase (se 3 (by rfl) ⟨474332, by rfl⟩ : syracuseStep 2529773 = 948665) (by norm_num)
theorem B2529797 : Blo 1686043 2529797 := bbase (se 4 (by rfl) ⟨237168, by rfl⟩ : syracuseStep 2529797 = 474337) (by norm_num)
theorem B1899013 : Blo 1686043 1899013 := bbase (se 4 (by rfl) ⟨178032, by rfl⟩ : syracuseStep 1899013 = 356065) (by norm_num)
theorem B1710605 : Blo 1686043 1710605 := bbase (se 3 (by rfl) ⟨320738, by rfl⟩ : syracuseStep 1710605 = 641477) (by norm_num)
theorem B6404629 : Blo 1686043 6404629 := bbase (se 6 (by rfl) ⟨150108, by rfl⟩ : syracuseStep 6404629 = 300217) (by norm_num)
theorem B2529821 : Blo 1686043 2529821 := bbase (se 3 (by rfl) ⟨474341, by rfl⟩ : syracuseStep 2529821 = 948683) (by norm_num)
theorem B3602981 : Blo 1686043 3602981 := bbase (se 4 (by rfl) ⟨337779, by rfl⟩ : syracuseStep 3602981 = 675559) (by norm_num)
theorem B1899049 : Blo 1686043 1899049 := bbase (se 2 (by rfl) ⟨712143, by rfl⟩ : syracuseStep 1899049 = 1424287) (by norm_num)
theorem B2529845 : Blo 1686043 2529845 := bbase (se 5 (by rfl) ⟨118586, by rfl⟩ : syracuseStep 2529845 = 237173) (by norm_num)
theorem B2529869 : Blo 1686043 2529869 := bbase (se 3 (by rfl) ⟨474350, by rfl⟩ : syracuseStep 2529869 = 948701) (by norm_num)
theorem B2529893 : Blo 1686043 2529893 := bbase (se 4 (by rfl) ⟨237177, by rfl⟩ : syracuseStep 2529893 = 474355) (by norm_num)
theorem B2529917 : Blo 1686043 2529917 := bbase (se 3 (by rfl) ⟨474359, by rfl⟩ : syracuseStep 2529917 = 948719) (by norm_num)
theorem B1800841 : Blo 1686043 1800841 := bbase (se 2 (by rfl) ⟨675315, by rfl⟩ : syracuseStep 1800841 = 1350631) (by norm_num)
theorem B3201677 : Blo 1686043 3201677 := bbase (se 3 (by rfl) ⟨600314, by rfl⟩ : syracuseStep 3201677 = 1200629) (by norm_num)
theorem B2529941 : Blo 1686043 2529941 := bbase (se 6 (by rfl) ⟨59295, by rfl⟩ : syracuseStep 2529941 = 118591) (by norm_num)
theorem B2529965 : Blo 1686043 2529965 := bbase (se 3 (by rfl) ⟨474368, by rfl⟩ : syracuseStep 2529965 = 948737) (by norm_num)
theorem B5692085 : Blo 1686043 5692085 := bbase (se 5 (by rfl) ⟨266816, by rfl⟩ : syracuseStep 5692085 = 533633) (by norm_num)
theorem B1800901 : Blo 1686043 1800901 := bbase (se 4 (by rfl) ⟨168834, by rfl⟩ : syracuseStep 1800901 = 337669) (by norm_num)
theorem B2529989 : Blo 1686043 2529989 := bbase (se 4 (by rfl) ⟨237186, by rfl⟩ : syracuseStep 2529989 = 474373) (by norm_num)
theorem B1923797 : Blo 1686043 1923797 := bbase (se 7 (by rfl) ⟨22544, by rfl⟩ : syracuseStep 1923797 = 45089) (by norm_num)
theorem B2530013 : Blo 1686043 2530013 := bbase (se 3 (by rfl) ⟨474377, by rfl⟩ : syracuseStep 2530013 = 948755) (by norm_num)
theorem B2530037 : Blo 1686043 2530037 := bbase (se 5 (by rfl) ⟨118595, by rfl⟩ : syracuseStep 2530037 = 237191) (by norm_num)
theorem B2530061 : Blo 1686043 2530061 := bbase (se 3 (by rfl) ⟨474386, by rfl⟩ : syracuseStep 2530061 = 948773) (by norm_num)
theorem B2530085 : Blo 1686043 2530085 := bbase (se 4 (by rfl) ⟨237195, by rfl⟩ : syracuseStep 2530085 = 474391) (by norm_num)
theorem B2530109 : Blo 1686043 2530109 := bbase (se 3 (by rfl) ⟨474395, by rfl⟩ : syracuseStep 2530109 = 948791) (by norm_num)
theorem B6404933 : Blo 1686043 6404933 := bbase (se 4 (by rfl) ⟨600462, by rfl⟩ : syracuseStep 6404933 = 1200925) (by norm_num)
theorem B4561733 : Blo 1686043 4561733 := bbase (se 4 (by rfl) ⟨427662, by rfl⟩ : syracuseStep 4561733 = 855325) (by norm_num)
theorem B2530133 : Blo 1686043 2530133 := bbase (se 9 (by rfl) ⟨7412, by rfl⟩ : syracuseStep 2530133 = 14825) (by norm_num)
theorem B1825637 : Blo 1686043 1825637 := bbase (se 4 (by rfl) ⟨171153, by rfl⟩ : syracuseStep 1825637 = 342307) (by norm_num)
theorem B2530157 : Blo 1686043 2530157 := bbase (se 3 (by rfl) ⟨474404, by rfl⟩ : syracuseStep 2530157 = 948809) (by norm_num)
theorem B2530181 : Blo 1686043 2530181 := bbase (se 4 (by rfl) ⟨237204, by rfl⟩ : syracuseStep 2530181 = 474409) (by norm_num)
theorem B2530205 : Blo 1686043 2530205 := bbase (se 3 (by rfl) ⟨474413, by rfl⟩ : syracuseStep 2530205 = 948827) (by norm_num)
theorem B1923997 : Blo 1686043 1923997 := bbase (se 3 (by rfl) ⟨360749, by rfl⟩ : syracuseStep 1923997 = 721499) (by norm_num)
theorem B2530229 : Blo 1686043 2530229 := bbase (se 5 (by rfl) ⟨118604, by rfl⟩ : syracuseStep 2530229 = 237209) (by norm_num)
theorem B2702261 : Blo 1686043 2702261 := bbase (se 5 (by rfl) ⟨126668, by rfl⟩ : syracuseStep 2702261 = 253337) (by norm_num)
theorem B2530253 : Blo 1686043 2530253 := bbase (se 3 (by rfl) ⟨474422, by rfl⟩ : syracuseStep 2530253 = 948845) (by norm_num)
theorem B2530277 : Blo 1686043 2530277 := bbase (se 4 (by rfl) ⟨237213, by rfl⟩ : syracuseStep 2530277 = 474427) (by norm_num)
theorem B2530301 : Blo 1686043 2530301 := bbase (se 3 (by rfl) ⟨474431, by rfl⟩ : syracuseStep 2530301 = 948863) (by norm_num)
theorem B1801217 : Blo 1686043 1801217 := bbase (se 2 (by rfl) ⟨675456, by rfl⟩ : syracuseStep 1801217 = 1350913) (by norm_num)
theorem B2530325 : Blo 1686043 2530325 := bbase (se 6 (by rfl) ⟨59304, by rfl⟩ : syracuseStep 2530325 = 118609) (by norm_num)
theorem B4054045 : Blo 1686043 4054045 := bbase (se 3 (by rfl) ⟨760133, by rfl⟩ : syracuseStep 4054045 = 1520267) (by norm_num)
theorem B2530349 : Blo 1686043 2530349 := bbase (se 3 (by rfl) ⟨474440, by rfl⟩ : syracuseStep 2530349 = 948881) (by norm_num)
theorem B2530373 : Blo 1686043 2530373 := bbase (se 4 (by rfl) ⟨237222, by rfl⟩ : syracuseStep 2530373 = 474445) (by norm_num)
theorem B2530397 : Blo 1686043 2530397 := bbase (se 3 (by rfl) ⟨474449, by rfl⟩ : syracuseStep 2530397 = 948899) (by norm_num)
theorem B5692517 : Blo 1686043 5692517 := bbase (se 4 (by rfl) ⟨533673, by rfl⟩ : syracuseStep 5692517 = 1067347) (by norm_num)
theorem B2530421 : Blo 1686043 2530421 := bbase (se 5 (by rfl) ⟨118613, by rfl⟩ : syracuseStep 2530421 = 237227) (by norm_num)
theorem B2530445 : Blo 1686043 2530445 := bbase (se 3 (by rfl) ⟨474458, by rfl⟩ : syracuseStep 2530445 = 948917) (by norm_num)
theorem B2776213 : Blo 1686043 2776213 := bbase (se 6 (by rfl) ⟨65067, by rfl⟩ : syracuseStep 2776213 = 130135) (by norm_num)
theorem B3849373 : Blo 1686043 3849373 := bbase (se 3 (by rfl) ⟨721757, by rfl⟩ : syracuseStep 3849373 = 1443515) (by norm_num)
theorem B2530469 : Blo 1686043 2530469 := bbase (se 4 (by rfl) ⟨237231, by rfl⟩ : syracuseStep 2530469 = 474463) (by norm_num)
theorem B12811445 : Blo 1686043 12811445 := bbase (se 5 (by rfl) ⟨600536, by rfl⟩ : syracuseStep 12811445 = 1201073) (by norm_num)
theorem B7699637 : Blo 1686043 7699637 := bbase (se 5 (by rfl) ⟨360920, by rfl⟩ : syracuseStep 7699637 = 721841) (by norm_num)
theorem B2530493 : Blo 1686043 2530493 := bbase (se 3 (by rfl) ⟨474467, by rfl⟩ : syracuseStep 2530493 = 948935) (by norm_num)
theorem B15383765 : Blo 1686043 15383765 := bbase (se 7 (by rfl) ⟨180278, by rfl⟩ : syracuseStep 15383765 = 360557) (by norm_num)
theorem B2530517 : Blo 1686043 2530517 := bbase (se 7 (by rfl) ⟨29654, by rfl⟩ : syracuseStep 2530517 = 59309) (by norm_num)
theorem B3849445 : Blo 1686043 3849445 := bbase (se 4 (by rfl) ⟨360885, by rfl⟩ : syracuseStep 3849445 = 721771) (by norm_num)
theorem B2530541 : Blo 1686043 2530541 := bbase (se 3 (by rfl) ⟨474476, by rfl⟩ : syracuseStep 2530541 = 948953) (by norm_num)
theorem B2530565 : Blo 1686043 2530565 := bbase (se 4 (by rfl) ⟨237240, by rfl⟩ : syracuseStep 2530565 = 474481) (by norm_num)
theorem B5405957 : Blo 1686043 5405957 := bbase (se 4 (by rfl) ⟨506808, by rfl⟩ : syracuseStep 5405957 = 1013617) (by norm_num)
theorem B2530589 : Blo 1686043 2530589 := bbase (se 3 (by rfl) ⟨474485, by rfl⟩ : syracuseStep 2530589 = 948971) (by norm_num)
theorem B2530613 : Blo 1686043 2530613 := bbase (se 5 (by rfl) ⟨118622, by rfl⟩ : syracuseStep 2530613 = 237245) (by norm_num)
theorem B2530637 : Blo 1686043 2530637 := bbase (se 3 (by rfl) ⟨474494, by rfl⟩ : syracuseStep 2530637 = 948989) (by norm_num)
theorem B2530661 : Blo 1686043 2530661 := bbase (se 4 (by rfl) ⟨237249, by rfl⟩ : syracuseStep 2530661 = 474499) (by norm_num)
theorem B3202429 : Blo 1686043 3202429 := bbase (se 3 (by rfl) ⟨600455, by rfl⟩ : syracuseStep 3202429 = 1200911) (by norm_num)
theorem B2530685 : Blo 1686043 2530685 := bbase (se 3 (by rfl) ⟨474503, by rfl⟩ : syracuseStep 2530685 = 949007) (by norm_num)
theorem B2702717 : Blo 1686043 2702717 := bbase (se 3 (by rfl) ⟨506759, by rfl⟩ : syracuseStep 2702717 = 1013519) (by norm_num)
theorem B2530709 : Blo 1686043 2530709 := bbase (se 6 (by rfl) ⟨59313, by rfl⟩ : syracuseStep 2530709 = 118627) (by norm_num)
theorem B3653021 : Blo 1686043 3653021 := bbase (se 3 (by rfl) ⟨684941, by rfl⟩ : syracuseStep 3653021 = 1369883) (by norm_num)
theorem B3603869 : Blo 1686043 3603869 := bbase (se 3 (by rfl) ⟨675725, by rfl⟩ : syracuseStep 3603869 = 1351451) (by norm_num)
theorem B2530733 : Blo 1686043 2530733 := bbase (se 3 (by rfl) ⟨474512, by rfl⟩ : syracuseStep 2530733 = 949025) (by norm_num)
theorem B1801661 : Blo 1686043 1801661 := bbase (se 3 (by rfl) ⟨337811, by rfl⟩ : syracuseStep 1801661 = 675623) (by norm_num)
theorem B2530757 : Blo 1686043 2530757 := bbase (se 4 (by rfl) ⟨237258, by rfl⟩ : syracuseStep 2530757 = 474517) (by norm_num)
theorem B2530781 : Blo 1686043 2530781 := bbase (se 3 (by rfl) ⟨474521, by rfl⟩ : syracuseStep 2530781 = 949043) (by norm_num)
theorem B8543717 : Blo 1686043 8543717 := bbase (se 4 (by rfl) ⟨800973, by rfl⟩ : syracuseStep 8543717 = 1601947) (by norm_num)
theorem B2530805 : Blo 1686043 2530805 := bbase (se 5 (by rfl) ⟨118631, by rfl⟩ : syracuseStep 2530805 = 237263) (by norm_num)
theorem B1801721 : Blo 1686043 1801721 := bbase (se 2 (by rfl) ⟨675645, by rfl⟩ : syracuseStep 1801721 = 1351291) (by norm_num)
theorem B3038717 : Blo 1686043 3038717 := bbase (se 3 (by rfl) ⟨569759, by rfl⟩ : syracuseStep 3038717 = 1139519) (by norm_num)
theorem B3202573 : Blo 1686043 3202573 := bbase (se 3 (by rfl) ⟨600482, by rfl⟩ : syracuseStep 3202573 = 1200965) (by norm_num)
theorem B2530829 : Blo 1686043 2530829 := bbase (se 3 (by rfl) ⟨474530, by rfl⟩ : syracuseStep 2530829 = 949061) (by norm_num)
theorem B5692949 : Blo 1686043 5692949 := bbase (se 6 (by rfl) ⟨133428, by rfl⟩ : syracuseStep 5692949 = 266857) (by norm_num)
theorem B3603989 : Blo 1686043 3603989 := bbase (se 6 (by rfl) ⟨84468, by rfl⟩ : syracuseStep 3603989 = 168937) (by norm_num)
theorem B1826329 : Blo 1686043 1826329 := bbase (se 2 (by rfl) ⟨684873, by rfl⟩ : syracuseStep 1826329 = 1369747) (by norm_num)
theorem B2530853 : Blo 1686043 2530853 := bbase (se 4 (by rfl) ⟨237267, by rfl⟩ : syracuseStep 2530853 = 474535) (by norm_num)
theorem B2530877 : Blo 1686043 2530877 := bbase (se 3 (by rfl) ⟨474539, by rfl⟩ : syracuseStep 2530877 = 949079) (by norm_num)
theorem B12803669 : Blo 1686043 12803669 := bbase (se 8 (by rfl) ⟨75021, by rfl⟩ : syracuseStep 12803669 = 150043) (by norm_num)
theorem B2530901 : Blo 1686043 2530901 := bbase (se 8 (by rfl) ⟨14829, by rfl⟩ : syracuseStep 2530901 = 29659) (by norm_num)
theorem B2530925 : Blo 1686043 2530925 := bbase (se 3 (by rfl) ⟨474548, by rfl⟩ : syracuseStep 2530925 = 949097) (by norm_num)
theorem B1801849 : Blo 1686043 1801849 := bbase (se 2 (by rfl) ⟨675693, by rfl⟩ : syracuseStep 1801849 = 1351387) (by norm_num)
theorem B2530949 : Blo 1686043 2530949 := bbase (se 4 (by rfl) ⟨237276, by rfl⟩ : syracuseStep 2530949 = 474553) (by norm_num)
theorem B4054661 : Blo 1686043 4054661 := bbase (se 4 (by rfl) ⟨380124, by rfl⟩ : syracuseStep 4054661 = 760249) (by norm_num)
theorem B2530973 : Blo 1686043 2530973 := bbase (se 3 (by rfl) ⟨474557, by rfl⟩ : syracuseStep 2530973 = 949115) (by norm_num)
theorem B3202733 : Blo 1686043 3202733 := bbase (se 3 (by rfl) ⟨600512, by rfl⟩ : syracuseStep 3202733 = 1201025) (by norm_num)
theorem B2530997 : Blo 1686043 2530997 := bbase (se 5 (by rfl) ⟨118640, by rfl⟩ : syracuseStep 2530997 = 237281) (by norm_num)
theorem B2531021 : Blo 1686043 2531021 := bbase (se 3 (by rfl) ⟨474566, by rfl⟩ : syracuseStep 2531021 = 949133) (by norm_num)
theorem B2531045 : Blo 1686043 2531045 := bbase (se 4 (by rfl) ⟨237285, by rfl⟩ : syracuseStep 2531045 = 474571) (by norm_num)
theorem B2531069 : Blo 1686043 2531069 := bbase (se 3 (by rfl) ⟨474575, by rfl⟩ : syracuseStep 2531069 = 949151) (by norm_num)
theorem B2531093 : Blo 1686043 2531093 := bbase (se 6 (by rfl) ⟨59322, by rfl⟩ : syracuseStep 2531093 = 118645) (by norm_num)
theorem B2531117 : Blo 1686043 2531117 := bbase (se 3 (by rfl) ⟨474584, by rfl⟩ : syracuseStep 2531117 = 949169) (by norm_num)
theorem B4267829 : Blo 1686043 4267829 := bbase (se 5 (by rfl) ⟨200054, by rfl⟩ : syracuseStep 4267829 = 400109) (by norm_num)
theorem B3202877 : Blo 1686043 3202877 := bbase (se 3 (by rfl) ⟨600539, by rfl⟩ : syracuseStep 3202877 = 1201079) (by norm_num)
theorem B2531141 : Blo 1686043 2531141 := bbase (se 4 (by rfl) ⟨237294, by rfl⟩ : syracuseStep 2531141 = 474589) (by norm_num)
theorem B4054853 : Blo 1686043 4054853 := bbase (se 4 (by rfl) ⟨380142, by rfl⟩ : syracuseStep 4054853 = 760285) (by norm_num)
theorem B2531165 : Blo 1686043 2531165 := bbase (se 3 (by rfl) ⟨474593, by rfl⟩ : syracuseStep 2531165 = 949187) (by norm_num)
theorem B2531189 : Blo 1686043 2531189 := bbase (se 5 (by rfl) ⟨118649, by rfl⟩ : syracuseStep 2531189 = 237299) (by norm_num)
theorem B8535941 : Blo 1686043 8535941 := bbase (se 4 (by rfl) ⟨800244, by rfl⟩ : syracuseStep 8535941 = 1600489) (by norm_num)
theorem B2531213 : Blo 1686043 2531213 := bbase (se 3 (by rfl) ⟨474602, by rfl⟩ : syracuseStep 2531213 = 949205) (by norm_num)
theorem B33316757 : Blo 1686043 33316757 := bbase (se 6 (by rfl) ⟨780861, by rfl⟩ : syracuseStep 33316757 = 1561723) (by norm_num)
theorem B2531237 : Blo 1686043 2531237 := bbase (se 4 (by rfl) ⟨237303, by rfl⟩ : syracuseStep 2531237 = 474607) (by norm_num)
theorem B4054949 : Blo 1686043 4054949 := bbase (se 4 (by rfl) ⟨380151, by rfl⟩ : syracuseStep 4054949 = 760303) (by norm_num)
theorem B2531261 : Blo 1686043 2531261 := bbase (se 3 (by rfl) ⟨474611, by rfl⟩ : syracuseStep 2531261 = 949223) (by norm_num)
theorem B5693381 : Blo 1686043 5693381 := bbase (se 4 (by rfl) ⟨533754, by rfl⟩ : syracuseStep 5693381 = 1067509) (by norm_num)
theorem B5480389 : Blo 1686043 5480389 := bbase (se 4 (by rfl) ⟨513786, by rfl⟩ : syracuseStep 5480389 = 1027573) (by norm_num)
theorem B2531285 : Blo 1686043 2531285 := bbase (se 7 (by rfl) ⟨29663, by rfl⟩ : syracuseStep 2531285 = 59327) (by norm_num)
theorem B2564077 : Blo 1686043 2564077 := bbase (se 3 (by rfl) ⟨480764, by rfl⟩ : syracuseStep 2564077 = 961529) (by norm_num)
theorem B2531309 : Blo 1686043 2531309 := bbase (se 3 (by rfl) ⟨474620, by rfl⟩ : syracuseStep 2531309 = 949241) (by norm_num)
theorem B1687555 : Blo 1686043 1687555 := bstep (se 1 (by rfl) ⟨1265666, by rfl⟩ : syracuseStep 1687555 = 2531333) B2531333
theorem B2531345 : Blo 1686043 2531345 := bstep (se 2 (by rfl) ⟨949254, by rfl⟩ : syracuseStep 2531345 = 1898509) B1898509
theorem B1687571 : Blo 1686043 1687571 := bstep (se 1 (by rfl) ⟨1265678, by rfl⟩ : syracuseStep 1687571 = 2531357) B2531357
theorem B2531363 : Blo 1686043 2531363 := bstep (se 1 (by rfl) ⟨1898522, by rfl⟩ : syracuseStep 2531363 = 3797045) B3797045
theorem B1687587 : Blo 1686043 1687587 := bstep (se 1 (by rfl) ⟨1265690, by rfl⟩ : syracuseStep 1687587 = 2531381) B2531381
theorem B4055075 : Blo 1686043 4055075 := bstep (se 1 (by rfl) ⟨3041306, by rfl⟩ : syracuseStep 4055075 = 6082613) B6082613
theorem B7692337 : Blo 1686043 7692337 := bstep (se 2 (by rfl) ⟨2884626, by rfl⟩ : syracuseStep 7692337 = 5769253) B5769253
theorem B5693489 : Blo 1686043 5693489 := bstep (se 2 (by rfl) ⟨2135058, by rfl⟩ : syracuseStep 5693489 = 4270117) B4270117
theorem B1687603 : Blo 1686043 1687603 := bstep (se 1 (by rfl) ⟨1265702, by rfl⟩ : syracuseStep 1687603 = 2531405) B2531405
theorem B2531393 : Blo 1686043 2531393 := bstep (se 2 (by rfl) ⟨949272, by rfl⟩ : syracuseStep 2531393 = 1898545) B1898545
theorem B1687619 : Blo 1686043 1687619 := bstep (se 1 (by rfl) ⟨1265714, by rfl⟩ : syracuseStep 1687619 = 2531429) B2531429
theorem B2531411 : Blo 1686043 2531411 := bstep (se 1 (by rfl) ⟨1898558, by rfl⟩ : syracuseStep 2531411 = 3797117) B3797117
theorem B1687635 : Blo 1686043 1687635 := bstep (se 1 (by rfl) ⟨1265726, by rfl⟩ : syracuseStep 1687635 = 2531453) B2531453
theorem B1687651 : Blo 1686043 1687651 := bstep (se 1 (by rfl) ⟨1265738, by rfl⟩ : syracuseStep 1687651 = 2531477) B2531477
theorem B2531441 : Blo 1686043 2531441 := bstep (se 2 (by rfl) ⟨949290, by rfl⟩ : syracuseStep 2531441 = 1898581) B1898581
theorem B1687667 : Blo 1686043 1687667 := bstep (se 1 (by rfl) ⟨1265750, by rfl⟩ : syracuseStep 1687667 = 2531501) B2531501
theorem B2531459 : Blo 1686043 2531459 := bstep (se 1 (by rfl) ⟨1898594, by rfl⟩ : syracuseStep 2531459 = 3797189) B3797189
theorem B1687683 : Blo 1686043 1687683 := bstep (se 1 (by rfl) ⟨1265762, by rfl⟩ : syracuseStep 1687683 = 2531525) B2531525
theorem B1687699 : Blo 1686043 1687699 := bstep (se 1 (by rfl) ⟨1265774, by rfl⟩ : syracuseStep 1687699 = 2531549) B2531549
theorem B2531489 : Blo 1686043 2531489 := bstep (se 2 (by rfl) ⟨949308, by rfl⟩ : syracuseStep 2531489 = 1898617) B1898617
theorem B1687715 : Blo 1686043 1687715 := bstep (se 1 (by rfl) ⟨1265786, by rfl⟩ : syracuseStep 1687715 = 2531573) B2531573
theorem B3039409 : Blo 1686043 3039409 := bstep (se 2 (by rfl) ⟨1139778, by rfl⟩ : syracuseStep 3039409 = 2279557) B2279557
theorem B2531507 : Blo 1686043 2531507 := bstep (se 1 (by rfl) ⟨1898630, by rfl⟩ : syracuseStep 2531507 = 3797261) B3797261
theorem B1687731 : Blo 1686043 1687731 := bstep (se 1 (by rfl) ⟨1265798, by rfl⟩ : syracuseStep 1687731 = 2531597) B2531597
theorem B1687747 : Blo 1686043 1687747 := bstep (se 1 (by rfl) ⟨1265810, by rfl⟩ : syracuseStep 1687747 = 2531621) B2531621
theorem B2531537 : Blo 1686043 2531537 := bstep (se 2 (by rfl) ⟨949326, by rfl⟩ : syracuseStep 2531537 = 1898653) B1898653
theorem B1687763 : Blo 1686043 1687763 := bstep (se 1 (by rfl) ⟨1265822, by rfl⟩ : syracuseStep 1687763 = 2531645) B2531645
theorem B2531555 : Blo 1686043 2531555 := bstep (se 1 (by rfl) ⟨1898666, by rfl⟩ : syracuseStep 2531555 = 3797333) B3797333
theorem B21627107 : Blo 1686043 21627107 := bstep (se 1 (by rfl) ⟨16220330, by rfl⟩ : syracuseStep 21627107 = 32440661) B32440661
theorem B1687779 : Blo 1686043 1687779 := bstep (se 1 (by rfl) ⟨1265834, by rfl⟩ : syracuseStep 1687779 = 2531669) B2531669
theorem B1687795 : Blo 1686043 1687795 := bstep (se 1 (by rfl) ⟨1265846, by rfl⟩ : syracuseStep 1687795 = 2531693) B2531693
theorem B2531585 : Blo 1686043 2531585 := bstep (se 2 (by rfl) ⟨949344, by rfl⟩ : syracuseStep 2531585 = 1898689) B1898689
theorem B1687811 : Blo 1686043 1687811 := bstep (se 1 (by rfl) ⟨1265858, by rfl⟩ : syracuseStep 1687811 = 2531717) B2531717
theorem B2531603 : Blo 1686043 2531603 := bstep (se 1 (by rfl) ⟨1898702, by rfl⟩ : syracuseStep 2531603 = 3797405) B3797405
theorem B1687827 : Blo 1686043 1687827 := bstep (se 1 (by rfl) ⟨1265870, by rfl⟩ : syracuseStep 1687827 = 2531741) B2531741
theorem B3203363 : Blo 1686043 3203363 := bstep (se 1 (by rfl) ⟨2402522, by rfl⟩ : syracuseStep 3203363 = 4805045) B4805045
theorem B1687843 : Blo 1686043 1687843 := bstep (se 1 (by rfl) ⟨1265882, by rfl⟩ : syracuseStep 1687843 = 2531765) B2531765
theorem B2531633 : Blo 1686043 2531633 := bstep (se 2 (by rfl) ⟨949362, by rfl⟩ : syracuseStep 2531633 = 1898725) B1898725
theorem B1687859 : Blo 1686043 1687859 := bstep (se 1 (by rfl) ⟨1265894, by rfl⟩ : syracuseStep 1687859 = 2531789) B2531789
theorem B2531651 : Blo 1686043 2531651 := bstep (se 1 (by rfl) ⟨1898738, by rfl⟩ : syracuseStep 2531651 = 3797477) B3797477
theorem B1687875 : Blo 1686043 1687875 := bstep (se 1 (by rfl) ⟨1265906, by rfl⟩ : syracuseStep 1687875 = 2531813) B2531813
theorem B1687891 : Blo 1686043 1687891 := bstep (se 1 (by rfl) ⟨1265918, by rfl⟩ : syracuseStep 1687891 = 2531837) B2531837
theorem B2531681 : Blo 1686043 2531681 := bstep (se 2 (by rfl) ⟨949380, by rfl⟩ : syracuseStep 2531681 = 1898761) B1898761
theorem B1687907 : Blo 1686043 1687907 := bstep (se 1 (by rfl) ⟨1265930, by rfl⟩ : syracuseStep 1687907 = 2531861) B2531861
theorem B2531699 : Blo 1686043 2531699 := bstep (se 1 (by rfl) ⟨1898774, by rfl⟩ : syracuseStep 2531699 = 3797549) B3797549
theorem B1687923 : Blo 1686043 1687923 := bstep (se 1 (by rfl) ⟨1265942, by rfl⟩ : syracuseStep 1687923 = 2531885) B2531885
theorem B1687939 : Blo 1686043 1687939 := bstep (se 1 (by rfl) ⟨1265954, by rfl⟩ : syracuseStep 1687939 = 2531909) B2531909
theorem B2531729 : Blo 1686043 2531729 := bstep (se 2 (by rfl) ⟨949398, by rfl⟩ : syracuseStep 2531729 = 1898797) B1898797
theorem B1687955 : Blo 1686043 1687955 := bstep (se 1 (by rfl) ⟨1265966, by rfl⟩ : syracuseStep 1687955 = 2531933) B2531933
theorem B2531747 : Blo 1686043 2531747 := bstep (se 1 (by rfl) ⟨1898810, by rfl⟩ : syracuseStep 2531747 = 3797621) B3797621
theorem B1687971 : Blo 1686043 1687971 := bstep (se 1 (by rfl) ⟨1265978, by rfl⟩ : syracuseStep 1687971 = 2531957) B2531957
theorem B8544689 : Blo 1686043 8544689 := bstep (se 2 (by rfl) ⟨3204258, by rfl⟩ : syracuseStep 8544689 = 6408517) B6408517
theorem B2703793 : Blo 1686043 2703793 := bstep (se 2 (by rfl) ⟨1013922, by rfl⟩ : syracuseStep 2703793 = 2027845) B2027845
theorem B1687987 : Blo 1686043 1687987 := bstep (se 1 (by rfl) ⟨1265990, by rfl⟩ : syracuseStep 1687987 = 2531981) B2531981
theorem B2531777 : Blo 1686043 2531777 := bstep (se 2 (by rfl) ⟨949416, by rfl⟩ : syracuseStep 2531777 = 1898833) B1898833
theorem B1688003 : Blo 1686043 1688003 := bstep (se 1 (by rfl) ⟨1266002, by rfl⟩ : syracuseStep 1688003 = 2532005) B2532005
theorem B4268497 : Blo 1686043 4268497 := bstep (se 2 (by rfl) ⟨1600686, by rfl⟩ : syracuseStep 4268497 = 3201373) B3201373
theorem B2531795 : Blo 1686043 2531795 := bstep (se 1 (by rfl) ⟨1898846, by rfl⟩ : syracuseStep 2531795 = 3797693) B3797693
theorem B1688019 : Blo 1686043 1688019 := bstep (se 1 (by rfl) ⟨1266014, by rfl⟩ : syracuseStep 1688019 = 2532029) B2532029
theorem B1688035 : Blo 1686043 1688035 := bstep (se 1 (by rfl) ⟨1266026, by rfl⟩ : syracuseStep 1688035 = 2532053) B2532053
theorem B2531825 : Blo 1686043 2531825 := bstep (se 2 (by rfl) ⟨949434, by rfl⟩ : syracuseStep 2531825 = 1898869) B1898869
theorem B2531843 : Blo 1686043 2531843 := bstep (se 1 (by rfl) ⟨1898882, by rfl⟩ : syracuseStep 2531843 = 3797765) B3797765
theorem B8536589 : Blo 1686043 8536589 := bstep (se 3 (by rfl) ⟨1600610, by rfl⟩ : syracuseStep 8536589 = 3201221) B3201221
theorem B2531873 : Blo 1686043 2531873 := bstep (se 2 (by rfl) ⟨949452, by rfl⟩ : syracuseStep 2531873 = 1898905) B1898905
theorem B2531891 : Blo 1686043 2531891 := bstep (se 1 (by rfl) ⟨1898918, by rfl⟩ : syracuseStep 2531891 = 3797837) B3797837
theorem B3203651 : Blo 1686043 3203651 := bstep (se 1 (by rfl) ⟨2402738, by rfl⟩ : syracuseStep 3203651 = 4805477) B4805477
theorem B5694029 : Blo 1686043 5694029 := bstep (se 3 (by rfl) ⟨1067630, by rfl⟩ : syracuseStep 5694029 = 2135261) B2135261
theorem B2531921 : Blo 1686043 2531921 := bstep (se 2 (by rfl) ⟨949470, by rfl⟩ : syracuseStep 2531921 = 1898941) B1898941
theorem B2531939 : Blo 1686043 2531939 := bstep (se 1 (by rfl) ⟨1898954, by rfl⟩ : syracuseStep 2531939 = 3797909) B3797909
theorem B2531969 : Blo 1686043 2531969 := bstep (se 2 (by rfl) ⟨949488, by rfl⟩ : syracuseStep 2531969 = 1898977) B1898977
theorem B5694083 : Blo 1686043 5694083 := bstep (se 1 (by rfl) ⟨4270562, by rfl⟩ : syracuseStep 5694083 = 8541125) B8541125
theorem B5481091 : Blo 1686043 5481091 := bstep (se 1 (by rfl) ⟨4110818, by rfl⟩ : syracuseStep 5481091 = 8221637) B8221637
theorem B3080849 : Blo 1686043 3080849 := bstep (se 2 (by rfl) ⟨1155318, by rfl⟩ : syracuseStep 3080849 = 2310637) B2310637
theorem B2531987 : Blo 1686043 2531987 := bstep (se 1 (by rfl) ⟨1898990, by rfl⟩ : syracuseStep 2531987 = 3797981) B3797981
theorem B2532017 : Blo 1686043 2532017 := bstep (se 2 (by rfl) ⟨949506, by rfl⟩ : syracuseStep 2532017 = 1899013) B1899013
theorem B2532035 : Blo 1686043 2532035 := bstep (se 1 (by rfl) ⟨1899026, by rfl⟩ : syracuseStep 2532035 = 3798053) B3798053
theorem B2532065 : Blo 1686043 2532065 := bstep (se 2 (by rfl) ⟨949524, by rfl⟩ : syracuseStep 2532065 = 1899049) B1899049
theorem B4268771 : Blo 1686043 4268771 := bstep (se 1 (by rfl) ⟨3201578, by rfl⟩ : syracuseStep 4268771 = 6403157) B6403157
theorem B5128931 : Blo 1686043 5128931 := bstep (se 1 (by rfl) ⟨3846698, by rfl⟩ : syracuseStep 5128931 = 7693397) B7693397
theorem B3605219 : Blo 1686043 3605219 := bstep (se 1 (by rfl) ⟨2703914, by rfl⟩ : syracuseStep 3605219 = 5407829) B5407829
theorem B6841073 : Blo 1686043 6841073 := bstep (se 2 (by rfl) ⟨2565402, by rfl⟩ : syracuseStep 6841073 = 5130805) B5130805
theorem B7693069 : Blo 1686043 7693069 := bstep (se 3 (by rfl) ⟨1442450, by rfl⟩ : syracuseStep 7693069 = 2884901) B2884901
theorem B5202733 : Blo 1686043 5202733 := bstep (se 3 (by rfl) ⟨975512, by rfl⟩ : syracuseStep 5202733 = 1951025) B1951025
theorem B2310977 : Blo 1686043 2310977 := bstep (se 2 (by rfl) ⟨866616, by rfl⟩ : syracuseStep 2310977 = 1733233) B1733233
theorem B2401121 : Blo 1686043 2401121 := bstep (se 2 (by rfl) ⟨900420, by rfl⟩ : syracuseStep 2401121 = 1800841) B1800841
theorem B5407597 : Blo 1686043 5407597 := bstep (se 3 (by rfl) ⟨1013924, by rfl⟩ : syracuseStep 5407597 = 2027849) B2027849
theorem B10806149 : Blo 1686043 10806149 := bstep (se 4 (by rfl) ⟨1013076, by rfl⟩ : syracuseStep 10806149 = 2026153) B2026153
theorem B38937485 : Blo 1686043 38937485 := bstep (se 3 (by rfl) ⟨7300778, by rfl⟩ : syracuseStep 38937485 = 14601557) B14601557
theorem B5694353 : Blo 1686043 5694353 := bstep (se 2 (by rfl) ⟨2135382, by rfl⟩ : syracuseStep 5694353 = 4270765) B4270765
theorem B4268963 : Blo 1686043 4268963 := bstep (se 1 (by rfl) ⟨3201722, by rfl⟩ : syracuseStep 4268963 = 6403445) B6403445
theorem B4801457 : Blo 1686043 4801457 := bstep (se 2 (by rfl) ⟨1800546, by rfl⟩ : syracuseStep 4801457 = 3601093) B3601093
theorem B3793841 : Blo 1686043 3793841 := bstep (se 2 (by rfl) ⟨1422690, by rfl⟩ : syracuseStep 3793841 = 2845381) B2845381
theorem B2401201 : Blo 1686043 2401201 := bstep (se 2 (by rfl) ⟨900450, by rfl⟩ : syracuseStep 2401201 = 1800901) B1800901
theorem B6841265 : Blo 1686043 6841265 := bstep (se 2 (by rfl) ⟨2565474, by rfl⟩ : syracuseStep 6841265 = 5130949) B5130949
theorem B3793859 : Blo 1686043 3793859 := bstep (se 1 (by rfl) ⟨2845394, by rfl⟩ : syracuseStep 3793859 = 5690789) B5690789
theorem B12330053 : Blo 1686043 12330053 := bstep (se 4 (by rfl) ⟨1155942, by rfl⟩ : syracuseStep 12330053 = 2311885) B2311885
theorem B27051121 : Blo 1686043 27051121 := bstep (se 2 (by rfl) ⟨10144170, by rfl⟩ : syracuseStep 27051121 = 20288341) B20288341
theorem B7201997 : Blo 1686043 7201997 := bstep (se 3 (by rfl) ⟨1350374, by rfl⟩ : syracuseStep 7201997 = 2700749) B2700749
theorem B3794129 : Blo 1686043 3794129 := bstep (se 2 (by rfl) ⟨1422798, by rfl⟩ : syracuseStep 3794129 = 2845597) B2845597
theorem B2565329 : Blo 1686043 2565329 := bstep (se 2 (by rfl) ⟨961998, by rfl⟩ : syracuseStep 2565329 = 1923997) B1923997
theorem B3794147 : Blo 1686043 3794147 := bstep (se 1 (by rfl) ⟨2845610, by rfl⟩ : syracuseStep 3794147 = 5691221) B5691221
theorem B15385841 : Blo 1686043 15385841 := bstep (se 2 (by rfl) ⟨5769690, by rfl⟩ : syracuseStep 15385841 = 11539381) B11539381
theorem B8103245 : Blo 1686043 8103245 := bstep (se 3 (by rfl) ⟨1519358, by rfl⟩ : syracuseStep 8103245 = 3038717) B3038717
theorem B5268817 : Blo 1686043 5268817 := bstep (se 2 (by rfl) ⟨1975806, by rfl⟩ : syracuseStep 5268817 = 3951613) B3951613
theorem B7210403 : Blo 1686043 7210403 := bstep (se 1 (by rfl) ⟨5407802, by rfl⟩ : syracuseStep 7210403 = 10815605) B10815605
theorem B5694893 : Blo 1686043 5694893 := bstep (se 3 (by rfl) ⟨1067792, by rfl⟩ : syracuseStep 5694893 = 2135585) B2135585
theorem B73942469 : Blo 1686043 73942469 := bstep (se 4 (by rfl) ⟨6932106, by rfl⟩ : syracuseStep 73942469 = 13864213) B13864213
theorem B5768653 : Blo 1686043 5768653 := bstep (se 3 (by rfl) ⟨1081622, by rfl⟩ : syracuseStep 5768653 = 2163245) B2163245
theorem B2278865 : Blo 1686043 2278865 := bstep (se 2 (by rfl) ⟨854574, by rfl⟩ : syracuseStep 2278865 = 1709149) B1709149
theorem B5694947 : Blo 1686043 5694947 := bstep (se 1 (by rfl) ⟨4271210, by rfl⟩ : syracuseStep 5694947 = 8542421) B8542421
theorem B3794417 : Blo 1686043 3794417 := bstep (se 2 (by rfl) ⟨1422906, by rfl⟩ : syracuseStep 3794417 = 2845813) B2845813
theorem B3204593 : Blo 1686043 3204593 := bstep (se 2 (by rfl) ⟨1201722, by rfl⟩ : syracuseStep 3204593 = 2403445) B2403445
theorem B3794435 : Blo 1686043 3794435 := bstep (se 1 (by rfl) ⟨2845826, by rfl⟩ : syracuseStep 3794435 = 5691653) B5691653
theorem B9119267 : Blo 1686043 9119267 := bstep (se 1 (by rfl) ⟨6839450, by rfl⟩ : syracuseStep 9119267 = 13678901) B13678901
theorem B4802129 : Blo 1686043 4802129 := bstep (se 2 (by rfl) ⟨1800798, by rfl⟩ : syracuseStep 4802129 = 3601597) B3601597
theorem B2401987 : Blo 1686043 2401987 := bstep (se 1 (by rfl) ⟨1801490, by rfl⟩ : syracuseStep 2401987 = 3602981) B3602981
theorem B6489827 : Blo 1686043 6489827 := bstep (se 1 (by rfl) ⟨4867370, by rfl⟩ : syracuseStep 6489827 = 9734741) B9734741
theorem B5695217 : Blo 1686043 5695217 := bstep (se 2 (by rfl) ⟨2135706, by rfl⟩ : syracuseStep 5695217 = 4271413) B4271413
theorem B3794705 : Blo 1686043 3794705 := bstep (se 2 (by rfl) ⟨1423014, by rfl⟩ : syracuseStep 3794705 = 2846029) B2846029
theorem B3794723 : Blo 1686043 3794723 := bstep (se 1 (by rfl) ⟨2846042, by rfl⟩ : syracuseStep 3794723 = 5692085) B5692085
theorem B6080305 : Blo 1686043 6080305 := bstep (se 2 (by rfl) ⟨2280114, by rfl⟩ : syracuseStep 6080305 = 4560229) B4560229
theorem B14419781 : Blo 1686043 14419781 := bstep (se 4 (by rfl) ⟨1351854, by rfl⟩ : syracuseStep 14419781 = 2703709) B2703709
theorem B4269905 : Blo 1686043 4269905 := bstep (se 2 (by rfl) ⟨1601214, by rfl⟩ : syracuseStep 4269905 = 3202429) B3202429
theorem B4269955 : Blo 1686043 4269955 := bstep (se 1 (by rfl) ⟨3202466, by rfl⟩ : syracuseStep 4269955 = 6404933) B6404933
theorem B3041155 : Blo 1686043 3041155 := bstep (se 1 (by rfl) ⟨2280866, by rfl⟩ : syracuseStep 3041155 = 4561733) B4561733
theorem B5130125 : Blo 1686043 5130125 := bstep (se 3 (by rfl) ⟨961898, by rfl⟩ : syracuseStep 5130125 = 1923797) B1923797
theorem B4270097 : Blo 1686043 4270097 := bstep (se 2 (by rfl) ⟨1601286, by rfl⟩ : syracuseStep 4270097 = 3202573) B3202573
theorem B2435105 : Blo 1686043 2435105 := bstep (se 2 (by rfl) ⟨913164, by rfl⟩ : syracuseStep 2435105 = 1826329) B1826329
theorem B5851171 : Blo 1686043 5851171 := bstep (se 1 (by rfl) ⟨4388378, by rfl⟩ : syracuseStep 5851171 = 8776757) B8776757
theorem B3794993 : Blo 1686043 3794993 := bstep (se 2 (by rfl) ⟨1423122, by rfl⟩ : syracuseStep 3794993 = 2846245) B2846245
theorem B3795011 : Blo 1686043 3795011 := bstep (se 1 (by rfl) ⟨2846258, by rfl⟩ : syracuseStep 3795011 = 5692517) B5692517
theorem B6408305 : Blo 1686043 6408305 := bstep (se 2 (by rfl) ⟨2403114, by rfl⟩ : syracuseStep 6408305 = 4806229) B4806229
theorem B2402465 : Blo 1686043 2402465 := bstep (se 2 (by rfl) ⟨900924, by rfl⟩ : syracuseStep 2402465 = 1801849) B1801849
theorem B9603299 : Blo 1686043 9603299 := bstep (se 1 (by rfl) ⟨7202474, by rfl⟩ : syracuseStep 9603299 = 14404949) B14404949
theorem B4868365 : Blo 1686043 4868365 := bstep (se 3 (by rfl) ⟨912818, by rfl⟩ : syracuseStep 4868365 = 1825637) B1825637
theorem B5695757 : Blo 1686043 5695757 := bstep (se 3 (by rfl) ⟨1067954, by rfl⟩ : syracuseStep 5695757 = 2135909) B2135909
theorem B2435347 : Blo 1686043 2435347 := bstep (se 1 (by rfl) ⟨1826510, by rfl⟩ : syracuseStep 2435347 = 3653021) B3653021
theorem B2402579 : Blo 1686043 2402579 := bstep (se 1 (by rfl) ⟨1801934, by rfl⟩ : syracuseStep 2402579 = 3603869) B3603869
theorem B5695811 : Blo 1686043 5695811 := bstep (se 1 (by rfl) ⟨4271858, by rfl⟩ : syracuseStep 5695811 = 8543717) B8543717
theorem B3795281 : Blo 1686043 3795281 := bstep (se 2 (by rfl) ⟨1423230, by rfl⟩ : syracuseStep 3795281 = 2846461) B2846461
theorem B4802915 : Blo 1686043 4802915 := bstep (se 1 (by rfl) ⟨3602186, by rfl⟩ : syracuseStep 4802915 = 7204373) B7204373
theorem B3795299 : Blo 1686043 3795299 := bstep (se 1 (by rfl) ⟨2846474, by rfl⟩ : syracuseStep 3795299 = 5692949) B5692949
theorem B2402659 : Blo 1686043 2402659 := bstep (se 1 (by rfl) ⟨1801994, by rfl⟩ : syracuseStep 2402659 = 3603989) B3603989
theorem B3246499 : Blo 1686043 3246499 := bstep (se 1 (by rfl) ⟨2434874, by rfl⟩ : syracuseStep 3246499 = 4869749) B4869749
theorem B2845219 : Blo 1686043 2845219 := bstep (se 1 (by rfl) ⟨2133914, by rfl⟩ : syracuseStep 2845219 = 4267829) B4267829
theorem B5696081 : Blo 1686043 5696081 := bstep (se 2 (by rfl) ⟨2136030, by rfl⟩ : syracuseStep 5696081 = 4272061) B4272061
theorem B22211171 : Blo 1686043 22211171 := bstep (se 1 (by rfl) ⟨16658378, by rfl⟩ : syracuseStep 22211171 = 33316757) B33316757
theorem B3795569 : Blo 1686043 3795569 := bstep (se 2 (by rfl) ⟨1423338, by rfl⟩ : syracuseStep 3795569 = 2846677) B2846677
theorem B3795587 : Blo 1686043 3795587 := bstep (se 1 (by rfl) ⟨2846690, by rfl⟩ : syracuseStep 3795587 = 5693381) B5693381
theorem B3418769 : Blo 1686043 3418769 := bstep (se 2 (by rfl) ⟨1282038, by rfl⟩ : syracuseStep 3418769 = 2564077) B2564077
theorem B4803245 : Blo 1686043 4803245 := bstep (se 3 (by rfl) ⟨900608, by rfl⟩ : syracuseStep 4803245 = 1801217) B1801217
theorem B2845361 : Blo 1686043 2845361 := bstep (se 2 (by rfl) ⟨1067010, by rfl⟩ : syracuseStep 2845361 = 2134021) B2134021
theorem B4803313 : Blo 1686043 4803313 := bstep (se 2 (by rfl) ⟨1801242, by rfl⟩ : syracuseStep 4803313 = 3602485) B3602485
theorem B2845489 : Blo 1686043 2845489 := bstep (se 2 (by rfl) ⟨1067058, by rfl⟩ : syracuseStep 2845489 = 2134117) B2134117
theorem B2435891 : Blo 1686043 2435891 := bstep (se 1 (by rfl) ⟨1826918, by rfl⟩ : syracuseStep 2435891 = 3653837) B3653837
theorem B2026307 : Blo 1686043 2026307 := bstep (se 1 (by rfl) ⟨1519730, by rfl⟩ : syracuseStep 2026307 = 3039461) B3039461
theorem B2845523 : Blo 1686043 2845523 := bstep (se 1 (by rfl) ⟨2134142, by rfl⟩ : syracuseStep 2845523 = 4268285) B4268285
theorem B4557667 : Blo 1686043 4557667 := bstep (se 1 (by rfl) ⟨3418250, by rfl⟩ : syracuseStep 4557667 = 6836501) B6836501
theorem B3795857 : Blo 1686043 3795857 := bstep (se 2 (by rfl) ⟨1423446, by rfl⟩ : syracuseStep 3795857 = 2846893) B2846893
theorem B2403217 : Blo 1686043 2403217 := bstep (se 2 (by rfl) ⟨901206, by rfl⟩ : syracuseStep 2403217 = 1802413) B1802413
theorem B3795875 : Blo 1686043 3795875 := bstep (se 1 (by rfl) ⟨2846906, by rfl⟩ : syracuseStep 3795875 = 5693813) B5693813
theorem B9612229 : Blo 1686043 9612229 := bstep (se 4 (by rfl) ⟨901146, by rfl⟩ : syracuseStep 9612229 = 1802293) B1802293
theorem B2845651 : Blo 1686043 2845651 := bstep (se 1 (by rfl) ⟨2134238, by rfl⟩ : syracuseStep 2845651 = 4268477) B4268477
theorem B4271089 : Blo 1686043 4271089 := bstep (se 2 (by rfl) ⟨1601658, by rfl⟩ : syracuseStep 4271089 = 3203317) B3203317
theorem B4803587 : Blo 1686043 4803587 := bstep (se 1 (by rfl) ⟨3602690, by rfl⟩ : syracuseStep 4803587 = 7205381) B7205381
theorem B2845793 : Blo 1686043 2845793 := bstep (se 2 (by rfl) ⟨1067172, by rfl⟩ : syracuseStep 2845793 = 2134345) B2134345
theorem B5770349 : Blo 1686043 5770349 := bstep (se 3 (by rfl) ⟨1081940, by rfl⟩ : syracuseStep 5770349 = 2163881) B2163881
theorem B5696621 : Blo 1686043 5696621 := bstep (se 3 (by rfl) ⟨1068116, by rfl⟩ : syracuseStep 5696621 = 2136233) B2136233
theorem B7302257 : Blo 1686043 7302257 := bstep (se 2 (by rfl) ⟨2738346, by rfl⟩ : syracuseStep 7302257 = 5476693) B5476693
theorem B5696675 : Blo 1686043 5696675 := bstep (se 1 (by rfl) ⟨4272506, by rfl⟩ : syracuseStep 5696675 = 8545013) B8545013
theorem B3796145 : Blo 1686043 3796145 := bstep (se 2 (by rfl) ⟨1423554, by rfl⟩ : syracuseStep 3796145 = 2847109) B2847109
theorem B3796163 : Blo 1686043 3796163 := bstep (se 1 (by rfl) ⟨2847122, by rfl⟩ : syracuseStep 3796163 = 5694245) B5694245
theorem B4558033 : Blo 1686043 4558033 := bstep (se 2 (by rfl) ⟨1709262, by rfl⟩ : syracuseStep 4558033 = 3418525) B3418525
theorem B2845921 : Blo 1686043 2845921 := bstep (se 2 (by rfl) ⟨1067220, by rfl⟩ : syracuseStep 2845921 = 2134441) B2134441
theorem B2845955 : Blo 1686043 2845955 := bstep (se 1 (by rfl) ⟨2134466, by rfl⟩ : syracuseStep 2845955 = 4268933) B4268933
theorem B4271363 : Blo 1686043 4271363 := bstep (se 1 (by rfl) ⟨3203522, by rfl⟩ : syracuseStep 4271363 = 6407045) B6407045
theorem B8539505 : Blo 1686043 8539505 := bstep (se 2 (by rfl) ⟨3202314, by rfl⟩ : syracuseStep 8539505 = 6404629) B6404629
theorem B2846083 : Blo 1686043 2846083 := bstep (se 1 (by rfl) ⟨2134562, by rfl⟩ : syracuseStep 2846083 = 4269125) B4269125
theorem B5696945 : Blo 1686043 5696945 := bstep (se 2 (by rfl) ⟨2136354, by rfl⟩ : syracuseStep 5696945 = 4272709) B4272709
theorem B4271555 : Blo 1686043 4271555 := bstep (se 1 (by rfl) ⟨3203666, by rfl⟩ : syracuseStep 4271555 = 6407333) B6407333
theorem B14806469 : Blo 1686043 14806469 := bstep (se 4 (by rfl) ⟨1388106, by rfl⟩ : syracuseStep 14806469 = 2776213) B2776213
theorem B3796433 : Blo 1686043 3796433 := bstep (se 2 (by rfl) ⟨1423662, by rfl⟩ : syracuseStep 3796433 = 2847325) B2847325
theorem B3796451 : Blo 1686043 3796451 := bstep (se 1 (by rfl) ⟨2847338, by rfl⟩ : syracuseStep 3796451 = 5694677) B5694677
theorem B2846225 : Blo 1686043 2846225 := bstep (se 2 (by rfl) ⟨1067334, by rfl⟩ : syracuseStep 2846225 = 2134669) B2134669
theorem B12979811 : Blo 1686043 12979811 := bstep (se 1 (by rfl) ⟨9734858, by rfl⟩ : syracuseStep 12979811 = 19469717) B19469717
theorem B2600579 : Blo 1686043 2600579 := bstep (se 1 (by rfl) ⟨1950434, by rfl⟩ : syracuseStep 2600579 = 3900869) B3900869
theorem B2846353 : Blo 1686043 2846353 := bstep (se 2 (by rfl) ⟨1067382, by rfl⟩ : syracuseStep 2846353 = 2134765) B2134765
theorem B6401699 : Blo 1686043 6401699 := bstep (se 1 (by rfl) ⟨4801274, by rfl⟩ : syracuseStep 6401699 = 9602549) B9602549
theorem B6401713 : Blo 1686043 6401713 := bstep (se 2 (by rfl) ⟨2400642, by rfl⟩ : syracuseStep 6401713 = 4801285) B4801285
theorem B2846387 : Blo 1686043 2846387 := bstep (se 1 (by rfl) ⟨2134790, by rfl⟩ : syracuseStep 2846387 = 4269581) B4269581
theorem B3796721 : Blo 1686043 3796721 := bstep (se 2 (by rfl) ⟨1423770, by rfl⟩ : syracuseStep 3796721 = 2847541) B2847541
theorem B3796739 : Blo 1686043 3796739 := bstep (se 1 (by rfl) ⟨2847554, by rfl⟩ : syracuseStep 3796739 = 5695109) B5695109
theorem B2846515 : Blo 1686043 2846515 := bstep (se 1 (by rfl) ⟨2134886, by rfl⟩ : syracuseStep 2846515 = 4269773) B4269773
theorem B4804429 : Blo 1686043 4804429 := bstep (se 3 (by rfl) ⟨900830, by rfl⟩ : syracuseStep 4804429 = 1801661) B1801661
theorem B6082381 : Blo 1686043 6082381 := bstep (se 3 (by rfl) ⟨1140446, by rfl⟩ : syracuseStep 6082381 = 2280893) B2280893
theorem B2846657 : Blo 1686043 2846657 := bstep (se 2 (by rfl) ⟨1067496, by rfl⟩ : syracuseStep 2846657 = 2134993) B2134993
theorem B2133955 : Blo 1686043 2133955 := bstep (se 1 (by rfl) ⟨1600466, by rfl⟩ : syracuseStep 2133955 = 3200933) B3200933
theorem B4804589 : Blo 1686043 4804589 := bstep (se 3 (by rfl) ⟨900860, by rfl⟩ : syracuseStep 4804589 = 1801721) B1801721
theorem B3797009 : Blo 1686043 3797009 := bstep (se 2 (by rfl) ⟨1423878, by rfl⟩ : syracuseStep 3797009 = 2847757) B2847757
theorem B3797027 : Blo 1686043 3797027 := bstep (se 1 (by rfl) ⟨2847770, by rfl⟩ : syracuseStep 3797027 = 5695541) B5695541
theorem B2846785 : Blo 1686043 2846785 := bstep (se 2 (by rfl) ⟨1067544, by rfl⟩ : syracuseStep 2846785 = 2135089) B2135089
theorem B2846819 : Blo 1686043 2846819 := bstep (se 1 (by rfl) ⟨2135114, by rfl⟩ : syracuseStep 2846819 = 4270229) B4270229
theorem B30765197 : Blo 1686043 30765197 := bstep (se 3 (by rfl) ⟨5768474, by rfl⟩ : syracuseStep 30765197 = 11536949) B11536949
theorem B4804771 : Blo 1686043 4804771 := bstep (se 1 (by rfl) ⟨3603578, by rfl⟩ : syracuseStep 4804771 = 7207157) B7207157
theorem B5132497 : Blo 1686043 5132497 := bstep (se 2 (by rfl) ⟨1924686, by rfl⟩ : syracuseStep 5132497 = 3849373) B3849373
theorem B2846947 : Blo 1686043 2846947 := bstep (se 1 (by rfl) ⟨2135210, by rfl⟩ : syracuseStep 2846947 = 4270421) B4270421
theorem B4509997 : Blo 1686043 4509997 := bstep (se 3 (by rfl) ⟨845624, by rfl⟩ : syracuseStep 4509997 = 1691249) B1691249
theorem B3797297 : Blo 1686043 3797297 := bstep (se 2 (by rfl) ⟨1423986, by rfl⟩ : syracuseStep 3797297 = 2847973) B2847973
theorem B5132593 : Blo 1686043 5132593 := bstep (se 2 (by rfl) ⟨1924722, by rfl⟩ : syracuseStep 5132593 = 3849445) B3849445
theorem B3797315 : Blo 1686043 3797315 := bstep (se 1 (by rfl) ⟨2847986, by rfl⟩ : syracuseStep 3797315 = 5695973) B5695973
theorem B2847089 : Blo 1686043 2847089 := bstep (se 2 (by rfl) ⟨1067658, by rfl⟩ : syracuseStep 2847089 = 2135317) B2135317
theorem B4272497 : Blo 1686043 4272497 := bstep (se 2 (by rfl) ⟨1602186, by rfl⟩ : syracuseStep 4272497 = 3204373) B3204373
theorem B1896835 : Blo 1686043 1896835 := bstep (se 1 (by rfl) ⟨1422626, by rfl⟩ : syracuseStep 1896835 = 2845253) B2845253
theorem B4272547 : Blo 1686043 4272547 := bstep (se 1 (by rfl) ⟨3204410, by rfl⟩ : syracuseStep 4272547 = 6408821) B6408821
theorem B2134451 : Blo 1686043 2134451 := bstep (se 1 (by rfl) ⟨1600838, by rfl⟩ : syracuseStep 2134451 = 3201677) B3201677
theorem B4108771 : Blo 1686043 4108771 := bstep (se 1 (by rfl) ⟨3081578, by rfl⟩ : syracuseStep 4108771 = 6163157) B6163157
theorem B2847217 : Blo 1686043 2847217 := bstep (se 2 (by rfl) ⟨1067706, by rfl⟩ : syracuseStep 2847217 = 2135413) B2135413
theorem B1896979 : Blo 1686043 1896979 := bstep (se 1 (by rfl) ⟨1422734, by rfl⟩ : syracuseStep 1896979 = 2845469) B2845469
theorem B2847251 : Blo 1686043 2847251 := bstep (se 1 (by rfl) ⟨2135438, by rfl⟩ : syracuseStep 2847251 = 4270877) B4270877
theorem B4272689 : Blo 1686043 4272689 := bstep (se 2 (by rfl) ⟨1602258, by rfl⟩ : syracuseStep 4272689 = 3204517) B3204517
theorem B9122381 : Blo 1686043 9122381 := bstep (se 3 (by rfl) ⟨1710446, by rfl⟩ : syracuseStep 9122381 = 3420893) B3420893
theorem B3797585 : Blo 1686043 3797585 := bstep (se 2 (by rfl) ⟨1424094, by rfl⟩ : syracuseStep 3797585 = 2848189) B2848189
theorem B3797603 : Blo 1686043 3797603 := bstep (se 1 (by rfl) ⟨2848202, by rfl⟩ : syracuseStep 3797603 = 5696405) B5696405
theorem B11547269 : Blo 1686043 11547269 := bstep (se 4 (by rfl) ⟨1082556, by rfl⟩ : syracuseStep 11547269 = 2165113) B2165113
theorem B2847379 : Blo 1686043 2847379 := bstep (se 1 (by rfl) ⟨2135534, by rfl⟩ : syracuseStep 2847379 = 4271069) B4271069
theorem B1897123 : Blo 1686043 1897123 := bstep (se 1 (by rfl) ⟨1422842, by rfl⟩ : syracuseStep 1897123 = 2845685) B2845685
theorem B4559537 : Blo 1686043 4559537 := bstep (se 2 (by rfl) ⟨1709826, by rfl⟩ : syracuseStep 4559537 = 3419653) B3419653
theorem B2847521 : Blo 1686043 2847521 := bstep (se 2 (by rfl) ⟨1067820, by rfl⟩ : syracuseStep 2847521 = 2135641) B2135641
theorem B8540963 : Blo 1686043 8540963 := bstep (se 1 (by rfl) ⟨6405722, by rfl⟩ : syracuseStep 8540963 = 12811445) B12811445
theorem B5133091 : Blo 1686043 5133091 := bstep (se 1 (by rfl) ⟨3849818, by rfl⟩ : syracuseStep 5133091 = 7699637) B7699637
theorem B1897267 : Blo 1686043 1897267 := bstep (se 1 (by rfl) ⟨1422950, by rfl⟩ : syracuseStep 1897267 = 2845901) B2845901
theorem B3797873 : Blo 1686043 3797873 := bstep (se 2 (by rfl) ⟨1424202, by rfl⟩ : syracuseStep 3797873 = 2848405) B2848405
theorem B5403523 : Blo 1686043 5403523 := bstep (se 1 (by rfl) ⟨4052642, by rfl⟩ : syracuseStep 5403523 = 8105285) B8105285
theorem B3797891 : Blo 1686043 3797891 := bstep (se 1 (by rfl) ⟨2848418, by rfl⟩ : syracuseStep 3797891 = 5696837) B5696837
theorem B2847649 : Blo 1686043 2847649 := bstep (se 2 (by rfl) ⟨1067868, by rfl⟩ : syracuseStep 2847649 = 2135737) B2135737
theorem B1897411 : Blo 1686043 1897411 := bstep (se 1 (by rfl) ⟨1423058, by rfl⟩ : syracuseStep 1897411 = 2846117) B2846117
theorem B2847683 : Blo 1686043 2847683 := bstep (se 1 (by rfl) ⟨2135762, by rfl⟩ : syracuseStep 2847683 = 4271525) B4271525
theorem B4559885 : Blo 1686043 4559885 := bstep (se 3 (by rfl) ⟨854978, by rfl⟩ : syracuseStep 4559885 = 1709957) B1709957
theorem B4330513 : Blo 1686043 4330513 := bstep (se 2 (by rfl) ⟨1623942, by rfl⟩ : syracuseStep 4330513 = 3247885) B3247885
theorem B2847811 : Blo 1686043 2847811 := bstep (se 1 (by rfl) ⟨2135858, by rfl⟩ : syracuseStep 2847811 = 4271717) B4271717
theorem B1897555 : Blo 1686043 1897555 := bstep (se 1 (by rfl) ⟨1423166, by rfl⟩ : syracuseStep 1897555 = 2846333) B2846333
theorem B6403171 : Blo 1686043 6403171 := bstep (se 1 (by rfl) ⟨4802378, by rfl⟩ : syracuseStep 6403171 = 9604757) B9604757
theorem B2135155 : Blo 1686043 2135155 := bstep (se 1 (by rfl) ⟨1601366, by rfl⟩ : syracuseStep 2135155 = 3202733) B3202733
theorem B7206029 : Blo 1686043 7206029 := bstep (se 3 (by rfl) ⟨1351130, by rfl⟩ : syracuseStep 7206029 = 2702261) B2702261
theorem B5403793 : Blo 1686043 5403793 := bstep (se 2 (by rfl) ⟨2026422, by rfl⟩ : syracuseStep 5403793 = 4052845) B4052845
theorem B5690573 : Blo 1686043 5690573 := bstep (se 3 (by rfl) ⟨1066982, by rfl⟩ : syracuseStep 5690573 = 2133965) B2133965
theorem B2135251 : Blo 1686043 2135251 := bstep (se 1 (by rfl) ⟨1601438, by rfl⟩ : syracuseStep 2135251 = 3202877) B3202877
theorem B2847953 : Blo 1686043 2847953 := bstep (se 2 (by rfl) ⟨1067982, by rfl⟩ : syracuseStep 2847953 = 2135965) B2135965
theorem B1897699 : Blo 1686043 1897699 := bstep (se 1 (by rfl) ⟨1423274, by rfl⟩ : syracuseStep 1897699 = 2846549) B2846549
theorem B5690627 : Blo 1686043 5690627 := bstep (se 1 (by rfl) ⟨4267970, by rfl⟩ : syracuseStep 5690627 = 8535941) B8535941
theorem B2848081 : Blo 1686043 2848081 := bstep (se 2 (by rfl) ⟨1068030, by rfl⟩ : syracuseStep 2848081 = 2136061) B2136061
theorem B12817763 : Blo 1686043 12817763 := bstep (se 1 (by rfl) ⟨9613322, by rfl⟩ : syracuseStep 12817763 = 19226645) B19226645
theorem B1897843 : Blo 1686043 1897843 := bstep (se 1 (by rfl) ⟨1423382, by rfl⟩ : syracuseStep 1897843 = 2846765) B2846765
theorem B2848115 : Blo 1686043 2848115 := bstep (se 1 (by rfl) ⟨2136086, by rfl⟩ : syracuseStep 2848115 = 4272173) B4272173
theorem B5199331 : Blo 1686043 5199331 := bstep (se 1 (by rfl) ⟨3899498, by rfl⟩ : syracuseStep 5199331 = 7798997) B7798997
theorem B7206371 : Blo 1686043 7206371 := bstep (se 1 (by rfl) ⟨5404778, by rfl⟩ : syracuseStep 7206371 = 10809557) B10809557
theorem B2848243 : Blo 1686043 2848243 := bstep (se 1 (by rfl) ⟨2136182, by rfl⟩ : syracuseStep 2848243 = 4272365) B4272365
theorem B1897987 : Blo 1686043 1897987 := bstep (se 1 (by rfl) ⟨1423490, by rfl⟩ : syracuseStep 1897987 = 2846981) B2846981
theorem B5690897 : Blo 1686043 5690897 := bstep (se 2 (by rfl) ⟨2134086, by rfl⟩ : syracuseStep 5690897 = 4268173) B4268173
theorem B4806161 : Blo 1686043 4806161 := bstep (se 2 (by rfl) ⟨1802310, by rfl⟩ : syracuseStep 4806161 = 3604621) B3604621
theorem B3601955 : Blo 1686043 3601955 := bstep (se 1 (by rfl) ⟨2701466, by rfl⟩ : syracuseStep 3601955 = 5402933) B5402933
theorem B8541773 : Blo 1686043 8541773 := bstep (se 3 (by rfl) ⟨1601582, by rfl⟩ : syracuseStep 8541773 = 3203165) B3203165
theorem B2848385 : Blo 1686043 2848385 := bstep (se 2 (by rfl) ⟨1068144, by rfl⟩ : syracuseStep 2848385 = 2136289) B2136289
theorem B1898131 : Blo 1686043 1898131 := bstep (se 1 (by rfl) ⟨1423598, by rfl⟩ : syracuseStep 1898131 = 2847197) B2847197
theorem B5772977 : Blo 1686043 5772977 := bstep (se 2 (by rfl) ⟨2164866, by rfl⟩ : syracuseStep 5772977 = 4329733) B4329733
theorem B2135747 : Blo 1686043 2135747 := bstep (se 1 (by rfl) ⟨1601810, by rfl⟩ : syracuseStep 2135747 = 3203621) B3203621
theorem B14407409 : Blo 1686043 14407409 := bstep (se 2 (by rfl) ⟨5402778, by rfl⟩ : syracuseStep 14407409 = 10805557) B10805557
theorem B2848513 : Blo 1686043 2848513 := bstep (se 2 (by rfl) ⟨1068192, by rfl⟩ : syracuseStep 2848513 = 2136385) B2136385
theorem B4110097 : Blo 1686043 4110097 := bstep (se 2 (by rfl) ⟨1541286, by rfl⟩ : syracuseStep 4110097 = 3082573) B3082573
theorem B1898275 : Blo 1686043 1898275 := bstep (se 1 (by rfl) ⟨1423706, by rfl⟩ : syracuseStep 1898275 = 2847413) B2847413
theorem B2848547 : Blo 1686043 2848547 := bstep (se 1 (by rfl) ⟨2136410, by rfl⟩ : syracuseStep 2848547 = 4272821) B4272821
theorem B2529089 : Blo 1686043 2529089 := bstep (se 2 (by rfl) ⟨948408, by rfl⟩ : syracuseStep 2529089 = 1896817) B1896817
theorem B2529107 : Blo 1686043 2529107 := bstep (se 1 (by rfl) ⟨1896830, by rfl⟩ : syracuseStep 2529107 = 3793661) B3793661
theorem B2529137 : Blo 1686043 2529137 := bstep (se 2 (by rfl) ⟨948426, by rfl⟩ : syracuseStep 2529137 = 1896853) B1896853
theorem B2529155 : Blo 1686043 2529155 := bstep (se 1 (by rfl) ⟨1896866, by rfl⟩ : syracuseStep 2529155 = 3793733) B3793733
theorem B24319885 : Blo 1686043 24319885 := bstep (se 3 (by rfl) ⟨4559978, by rfl⟩ : syracuseStep 24319885 = 9119957) B9119957
theorem B2529185 : Blo 1686043 2529185 := bstep (se 2 (by rfl) ⟨948444, by rfl⟩ : syracuseStep 2529185 = 1896889) B1896889
theorem B7206833 : Blo 1686043 7206833 := bstep (se 2 (by rfl) ⟨2702562, by rfl⟩ : syracuseStep 7206833 = 5405125) B5405125
theorem B2529203 : Blo 1686043 2529203 := bstep (se 1 (by rfl) ⟨1896902, by rfl⟩ : syracuseStep 2529203 = 3793805) B3793805
theorem B1898419 : Blo 1686043 1898419 := bstep (se 1 (by rfl) ⟨1423814, by rfl⟩ : syracuseStep 1898419 = 2847629) B2847629
theorem B2529233 : Blo 1686043 2529233 := bstep (se 2 (by rfl) ⟨948462, by rfl⟩ : syracuseStep 2529233 = 1896925) B1896925
theorem B2529251 : Blo 1686043 2529251 := bstep (se 1 (by rfl) ⟨1896938, by rfl⟩ : syracuseStep 2529251 = 3793877) B3793877
theorem B5847025 : Blo 1686043 5847025 := bstep (se 2 (by rfl) ⟨2192634, by rfl⟩ : syracuseStep 5847025 = 4385269) B4385269
theorem B2529281 : Blo 1686043 2529281 := bstep (se 2 (by rfl) ⟨948480, by rfl⟩ : syracuseStep 2529281 = 1896961) B1896961
theorem B2529299 : Blo 1686043 2529299 := bstep (se 1 (by rfl) ⟨1896974, by rfl⟩ : syracuseStep 2529299 = 3793949) B3793949
theorem B5691437 : Blo 1686043 5691437 := bstep (se 3 (by rfl) ⟨1067144, by rfl⟩ : syracuseStep 5691437 = 2134289) B2134289
theorem B2529329 : Blo 1686043 2529329 := bstep (se 2 (by rfl) ⟨948498, by rfl⟩ : syracuseStep 2529329 = 1896997) B1896997
theorem B2529347 : Blo 1686043 2529347 := bstep (se 1 (by rfl) ⟨1897010, by rfl⟩ : syracuseStep 2529347 = 3794021) B3794021
theorem B1898563 : Blo 1686043 1898563 := bstep (se 1 (by rfl) ⟨1423922, by rfl⟩ : syracuseStep 1898563 = 2847845) B2847845
theorem B1710163 : Blo 1686043 1710163 := bstep (se 1 (by rfl) ⟨1282622, by rfl⟩ : syracuseStep 1710163 = 2565245) B2565245
theorem B2529377 : Blo 1686043 2529377 := bstep (se 2 (by rfl) ⟨948516, by rfl⟩ : syracuseStep 2529377 = 1897033) B1897033
theorem B5691491 : Blo 1686043 5691491 := bstep (se 1 (by rfl) ⟨4268618, by rfl⟩ : syracuseStep 5691491 = 8537237) B8537237
theorem B2529395 : Blo 1686043 2529395 := bstep (se 1 (by rfl) ⟨1897046, by rfl⟩ : syracuseStep 2529395 = 3794093) B3794093
theorem B2701441 : Blo 1686043 2701441 := bstep (se 2 (by rfl) ⟨1013040, by rfl⟩ : syracuseStep 2701441 = 2026081) B2026081
theorem B2529425 : Blo 1686043 2529425 := bstep (se 2 (by rfl) ⟨948534, by rfl⟩ : syracuseStep 2529425 = 1897069) B1897069
theorem B2529443 : Blo 1686043 2529443 := bstep (se 1 (by rfl) ⟨1897082, by rfl⟩ : syracuseStep 2529443 = 3794165) B3794165
theorem B2529473 : Blo 1686043 2529473 := bstep (se 2 (by rfl) ⟨948552, by rfl⟩ : syracuseStep 2529473 = 1897105) B1897105
theorem B2529491 : Blo 1686043 2529491 := bstep (se 1 (by rfl) ⟨1897118, by rfl⟩ : syracuseStep 2529491 = 3794237) B3794237
theorem B1898707 : Blo 1686043 1898707 := bstep (se 1 (by rfl) ⟨1424030, by rfl⟩ : syracuseStep 1898707 = 2848061) B2848061
theorem B2529521 : Blo 1686043 2529521 := bstep (se 2 (by rfl) ⟨948570, by rfl⟩ : syracuseStep 2529521 = 1897141) B1897141
theorem B2529539 : Blo 1686043 2529539 := bstep (se 1 (by rfl) ⟨1897154, by rfl⟩ : syracuseStep 2529539 = 3794309) B3794309
theorem B2529569 : Blo 1686043 2529569 := bstep (se 2 (by rfl) ⟨948588, by rfl⟩ : syracuseStep 2529569 = 1897177) B1897177
theorem B2529587 : Blo 1686043 2529587 := bstep (se 1 (by rfl) ⟨1897190, by rfl⟩ : syracuseStep 2529587 = 3794381) B3794381
theorem B2529617 : Blo 1686043 2529617 := bstep (se 2 (by rfl) ⟨948606, by rfl⟩ : syracuseStep 2529617 = 1897213) B1897213
theorem B2529635 : Blo 1686043 2529635 := bstep (se 1 (by rfl) ⟨1897226, by rfl⟩ : syracuseStep 2529635 = 3794453) B3794453
theorem B1898851 : Blo 1686043 1898851 := bstep (se 1 (by rfl) ⟨1424138, by rfl⟩ : syracuseStep 1898851 = 2848277) B2848277
theorem B5691761 : Blo 1686043 5691761 := bstep (se 2 (by rfl) ⟨2134410, by rfl⟩ : syracuseStep 5691761 = 4268821) B4268821
theorem B2529665 : Blo 1686043 2529665 := bstep (se 2 (by rfl) ⟨948624, by rfl⟩ : syracuseStep 2529665 = 1897249) B1897249
theorem B2529683 : Blo 1686043 2529683 := bstep (se 1 (by rfl) ⟨1897262, by rfl⟩ : syracuseStep 2529683 = 3794525) B3794525
theorem B3201457 : Blo 1686043 3201457 := bstep (se 2 (by rfl) ⟨1200546, by rfl⟩ : syracuseStep 3201457 = 2401093) B2401093
theorem B2529713 : Blo 1686043 2529713 := bstep (se 2 (by rfl) ⟨948642, by rfl⟩ : syracuseStep 2529713 = 1897285) B1897285
theorem B2529731 : Blo 1686043 2529731 := bstep (se 1 (by rfl) ⟨1897298, by rfl⟩ : syracuseStep 2529731 = 3794597) B3794597
theorem B2529761 : Blo 1686043 2529761 := bstep (se 2 (by rfl) ⟨948660, by rfl⟩ : syracuseStep 2529761 = 1897321) B1897321
theorem B2529779 : Blo 1686043 2529779 := bstep (se 1 (by rfl) ⟨1897334, by rfl⟩ : syracuseStep 2529779 = 3794669) B3794669
theorem B1898995 : Blo 1686043 1898995 := bstep (se 1 (by rfl) ⟨1424246, by rfl⟩ : syracuseStep 1898995 = 2848493) B2848493
theorem B2529809 : Blo 1686043 2529809 := bstep (se 2 (by rfl) ⟨948678, by rfl⟩ : syracuseStep 2529809 = 1897357) B1897357
theorem B1686051 : Blo 1686043 1686051 := bstep (se 1 (by rfl) ⟨1264538, by rfl⟩ : syracuseStep 1686051 = 2529077) B2529077
theorem B2529827 : Blo 1686043 2529827 := bstep (se 1 (by rfl) ⟨1897370, by rfl⟩ : syracuseStep 2529827 = 3794741) B3794741
theorem B1686067 : Blo 1686043 1686067 := bstep (se 1 (by rfl) ⟨1264550, by rfl⟩ : syracuseStep 1686067 = 2529101) B2529101
theorem B2529857 : Blo 1686043 2529857 := bstep (se 2 (by rfl) ⟨948696, by rfl⟩ : syracuseStep 2529857 = 1897393) B1897393
theorem B1686083 : Blo 1686043 1686083 := bstep (se 1 (by rfl) ⟨1264562, by rfl⟩ : syracuseStep 1686083 = 2529125) B2529125
theorem B1686099 : Blo 1686043 1686099 := bstep (se 1 (by rfl) ⟨1264574, by rfl⟩ : syracuseStep 1686099 = 2529149) B2529149
theorem B2529875 : Blo 1686043 2529875 := bstep (se 1 (by rfl) ⟨1897406, by rfl⟩ : syracuseStep 2529875 = 3794813) B3794813
theorem B1686115 : Blo 1686043 1686115 := bstep (se 1 (by rfl) ⟨1264586, by rfl⟩ : syracuseStep 1686115 = 2529173) B2529173
theorem B19225187 : Blo 1686043 19225187 := bstep (se 1 (by rfl) ⟨14418890, by rfl⟩ : syracuseStep 19225187 = 28837781) B28837781
theorem B2529905 : Blo 1686043 2529905 := bstep (se 2 (by rfl) ⟨948714, by rfl⟩ : syracuseStep 2529905 = 1897429) B1897429
theorem B1686131 : Blo 1686043 1686131 := bstep (se 1 (by rfl) ⟨1264598, by rfl⟩ : syracuseStep 1686131 = 2529197) B2529197
theorem B1686147 : Blo 1686043 1686147 := bstep (se 1 (by rfl) ⟨1264610, by rfl⟩ : syracuseStep 1686147 = 2529221) B2529221
theorem B2529923 : Blo 1686043 2529923 := bstep (se 1 (by rfl) ⟨1897442, by rfl⟩ : syracuseStep 2529923 = 3794885) B3794885
theorem B11541133 : Blo 1686043 11541133 := bstep (se 3 (by rfl) ⟨2163962, by rfl⟩ : syracuseStep 11541133 = 4327925) B4327925
theorem B1686163 : Blo 1686043 1686163 := bstep (se 1 (by rfl) ⟨1264622, by rfl⟩ : syracuseStep 1686163 = 2529245) B2529245
theorem B2529953 : Blo 1686043 2529953 := bstep (se 2 (by rfl) ⟨948732, by rfl⟩ : syracuseStep 2529953 = 1897465) B1897465
theorem B1686179 : Blo 1686043 1686179 := bstep (se 1 (by rfl) ⟨1264634, by rfl⟩ : syracuseStep 1686179 = 2529269) B2529269
theorem B1686195 : Blo 1686043 1686195 := bstep (se 1 (by rfl) ⟨1264646, by rfl⟩ : syracuseStep 1686195 = 2529293) B2529293
theorem B2529971 : Blo 1686043 2529971 := bstep (se 1 (by rfl) ⟨1897478, by rfl⟩ : syracuseStep 2529971 = 3794957) B3794957
theorem B1686211 : Blo 1686043 1686211 := bstep (se 1 (by rfl) ⟨1264658, by rfl⟩ : syracuseStep 1686211 = 2529317) B2529317
theorem B10803917 : Blo 1686043 10803917 := bstep (se 3 (by rfl) ⟨2025734, by rfl⟩ : syracuseStep 10803917 = 4051469) B4051469
theorem B4561613 : Blo 1686043 4561613 := bstep (se 3 (by rfl) ⟨855302, by rfl⟩ : syracuseStep 4561613 = 1710605) B1710605
theorem B2530001 : Blo 1686043 2530001 := bstep (se 2 (by rfl) ⟨948750, by rfl⟩ : syracuseStep 2530001 = 1897501) B1897501
theorem B1686227 : Blo 1686043 1686227 := bstep (se 1 (by rfl) ⟨1264670, by rfl⟩ : syracuseStep 1686227 = 2529341) B2529341
theorem B5405393 : Blo 1686043 5405393 := bstep (se 2 (by rfl) ⟨2027022, by rfl⟩ : syracuseStep 5405393 = 4054045) B4054045
theorem B1686243 : Blo 1686043 1686243 := bstep (se 1 (by rfl) ⟨1264682, by rfl⟩ : syracuseStep 1686243 = 2529365) B2529365
theorem B2530019 : Blo 1686043 2530019 := bstep (se 1 (by rfl) ⟨1897514, by rfl⟩ : syracuseStep 2530019 = 3795029) B3795029
theorem B1686259 : Blo 1686043 1686259 := bstep (se 1 (by rfl) ⟨1264694, by rfl⟩ : syracuseStep 1686259 = 2529389) B2529389
theorem B2530049 : Blo 1686043 2530049 := bstep (se 2 (by rfl) ⟨948768, by rfl⟩ : syracuseStep 2530049 = 1897537) B1897537
theorem B1686275 : Blo 1686043 1686275 := bstep (se 1 (by rfl) ⟨1264706, by rfl⟩ : syracuseStep 1686275 = 2529413) B2529413
theorem B4561667 : Blo 1686043 4561667 := bstep (se 1 (by rfl) ⟨3421250, by rfl⟩ : syracuseStep 4561667 = 6842501) B6842501
theorem B1686291 : Blo 1686043 1686291 := bstep (se 1 (by rfl) ⟨1264718, by rfl⟩ : syracuseStep 1686291 = 2529437) B2529437
theorem B2530067 : Blo 1686043 2530067 := bstep (se 1 (by rfl) ⟨1897550, by rfl⟩ : syracuseStep 2530067 = 3795101) B3795101
theorem B1686307 : Blo 1686043 1686307 := bstep (se 1 (by rfl) ⟨1264730, by rfl⟩ : syracuseStep 1686307 = 2529461) B2529461
theorem B2530097 : Blo 1686043 2530097 := bstep (se 2 (by rfl) ⟨948786, by rfl⟩ : syracuseStep 2530097 = 1897573) B1897573
theorem B1686323 : Blo 1686043 1686323 := bstep (se 1 (by rfl) ⟨1264742, by rfl⟩ : syracuseStep 1686323 = 2529485) B2529485
theorem B1686339 : Blo 1686043 1686339 := bstep (se 1 (by rfl) ⟨1264754, by rfl⟩ : syracuseStep 1686339 = 2529509) B2529509
theorem B3201859 : Blo 1686043 3201859 := bstep (se 1 (by rfl) ⟨2401394, by rfl⟩ : syracuseStep 3201859 = 4802789) B4802789
theorem B2530115 : Blo 1686043 2530115 := bstep (se 1 (by rfl) ⟨1897586, by rfl⟩ : syracuseStep 2530115 = 3795173) B3795173
theorem B1686355 : Blo 1686043 1686355 := bstep (se 1 (by rfl) ⟨1264766, by rfl⟩ : syracuseStep 1686355 = 2529533) B2529533
theorem B2530145 : Blo 1686043 2530145 := bstep (se 2 (by rfl) ⟨948804, by rfl⟩ : syracuseStep 2530145 = 1897609) B1897609
theorem B1686371 : Blo 1686043 1686371 := bstep (se 1 (by rfl) ⟨1264778, by rfl⟩ : syracuseStep 1686371 = 2529557) B2529557
theorem B3201905 : Blo 1686043 3201905 := bstep (se 2 (by rfl) ⟨1200714, by rfl⟩ : syracuseStep 3201905 = 2401429) B2401429
theorem B1686387 : Blo 1686043 1686387 := bstep (se 1 (by rfl) ⟨1264790, by rfl⟩ : syracuseStep 1686387 = 2529581) B2529581
theorem B2530163 : Blo 1686043 2530163 := bstep (se 1 (by rfl) ⟨1897622, by rfl⟩ : syracuseStep 2530163 = 3795245) B3795245
theorem B1686403 : Blo 1686043 1686403 := bstep (se 1 (by rfl) ⟨1264802, by rfl⟩ : syracuseStep 1686403 = 2529605) B2529605
theorem B5692301 : Blo 1686043 5692301 := bstep (se 3 (by rfl) ⟨1067306, by rfl⟩ : syracuseStep 5692301 = 2134613) B2134613
theorem B2530193 : Blo 1686043 2530193 := bstep (se 2 (by rfl) ⟨948822, by rfl⟩ : syracuseStep 2530193 = 1897645) B1897645
theorem B1686419 : Blo 1686043 1686419 := bstep (se 1 (by rfl) ⟨1264814, by rfl⟩ : syracuseStep 1686419 = 2529629) B2529629
theorem B1686435 : Blo 1686043 1686435 := bstep (se 1 (by rfl) ⟨1264826, by rfl⟩ : syracuseStep 1686435 = 2529653) B2529653
theorem B2530211 : Blo 1686043 2530211 := bstep (se 1 (by rfl) ⟨1897658, by rfl⟩ : syracuseStep 2530211 = 3795317) B3795317
theorem B1686451 : Blo 1686043 1686451 := bstep (se 1 (by rfl) ⟨1264838, by rfl⟩ : syracuseStep 1686451 = 2529677) B2529677
theorem B2530241 : Blo 1686043 2530241 := bstep (se 2 (by rfl) ⟨948840, by rfl⟩ : syracuseStep 2530241 = 1897681) B1897681
theorem B1686467 : Blo 1686043 1686467 := bstep (se 1 (by rfl) ⟨1264850, by rfl⟩ : syracuseStep 1686467 = 2529701) B2529701
theorem B5692355 : Blo 1686043 5692355 := bstep (se 1 (by rfl) ⟨4269266, by rfl⟩ : syracuseStep 5692355 = 8538533) B8538533
theorem B1686483 : Blo 1686043 1686483 := bstep (se 1 (by rfl) ⟨1264862, by rfl⟩ : syracuseStep 1686483 = 2529725) B2529725
theorem B2530259 : Blo 1686043 2530259 := bstep (se 1 (by rfl) ⟨1897694, by rfl⟩ : syracuseStep 2530259 = 3795389) B3795389
theorem B1686499 : Blo 1686043 1686499 := bstep (se 1 (by rfl) ⟨1264874, by rfl⟩ : syracuseStep 1686499 = 2529749) B2529749
theorem B2530289 : Blo 1686043 2530289 := bstep (se 2 (by rfl) ⟨948858, by rfl⟩ : syracuseStep 2530289 = 1897717) B1897717
theorem B1686515 : Blo 1686043 1686515 := bstep (se 1 (by rfl) ⟨1264886, by rfl⟩ : syracuseStep 1686515 = 2529773) B2529773
theorem B1686531 : Blo 1686043 1686531 := bstep (se 1 (by rfl) ⟨1264898, by rfl⟩ : syracuseStep 1686531 = 2529797) B2529797
theorem B2530307 : Blo 1686043 2530307 := bstep (se 1 (by rfl) ⟨1897730, by rfl⟩ : syracuseStep 2530307 = 3795461) B3795461
theorem B1686547 : Blo 1686043 1686547 := bstep (se 1 (by rfl) ⟨1264910, by rfl⟩ : syracuseStep 1686547 = 2529821) B2529821
theorem B2530337 : Blo 1686043 2530337 := bstep (se 2 (by rfl) ⟨948876, by rfl⟩ : syracuseStep 2530337 = 1897753) B1897753
theorem B1686563 : Blo 1686043 1686563 := bstep (se 1 (by rfl) ⟨1264922, by rfl⟩ : syracuseStep 1686563 = 2529845) B2529845
theorem B5405741 : Blo 1686043 5405741 := bstep (se 3 (by rfl) ⟨1013576, by rfl⟩ : syracuseStep 5405741 = 2027153) B2027153
theorem B1686579 : Blo 1686043 1686579 := bstep (se 1 (by rfl) ⟨1264934, by rfl⟩ : syracuseStep 1686579 = 2529869) B2529869
theorem B2530355 : Blo 1686043 2530355 := bstep (se 1 (by rfl) ⟨1897766, by rfl⟩ : syracuseStep 2530355 = 3795533) B3795533
theorem B1686595 : Blo 1686043 1686595 := bstep (se 1 (by rfl) ⟨1264946, by rfl⟩ : syracuseStep 1686595 = 2529893) B2529893
theorem B2530385 : Blo 1686043 2530385 := bstep (se 2 (by rfl) ⟨948894, by rfl⟩ : syracuseStep 2530385 = 1897789) B1897789
theorem B1686611 : Blo 1686043 1686611 := bstep (se 1 (by rfl) ⟨1264958, by rfl⟩ : syracuseStep 1686611 = 2529917) B2529917
theorem B1686627 : Blo 1686043 1686627 := bstep (se 1 (by rfl) ⟨1264970, by rfl⟩ : syracuseStep 1686627 = 2529941) B2529941
theorem B2530403 : Blo 1686043 2530403 := bstep (se 1 (by rfl) ⟨1897802, by rfl⟩ : syracuseStep 2530403 = 3795605) B3795605
theorem B1686643 : Blo 1686043 1686643 := bstep (se 1 (by rfl) ⟨1264982, by rfl⟩ : syracuseStep 1686643 = 2529965) B2529965
theorem B2530433 : Blo 1686043 2530433 := bstep (se 2 (by rfl) ⟨948912, by rfl⟩ : syracuseStep 2530433 = 1897825) B1897825
theorem B1686659 : Blo 1686043 1686659 := bstep (se 1 (by rfl) ⟨1264994, by rfl⟩ : syracuseStep 1686659 = 2529989) B2529989
theorem B3202193 : Blo 1686043 3202193 := bstep (se 2 (by rfl) ⟨1200822, by rfl⟩ : syracuseStep 3202193 = 2401645) B2401645
theorem B1686675 : Blo 1686043 1686675 := bstep (se 1 (by rfl) ⟨1265006, by rfl⟩ : syracuseStep 1686675 = 2530013) B2530013
theorem B2530451 : Blo 1686043 2530451 := bstep (se 1 (by rfl) ⟨1897838, by rfl⟩ : syracuseStep 2530451 = 3795677) B3795677
theorem B1686691 : Blo 1686043 1686691 := bstep (se 1 (by rfl) ⟨1265018, by rfl⟩ : syracuseStep 1686691 = 2530037) B2530037
theorem B2530481 : Blo 1686043 2530481 := bstep (se 2 (by rfl) ⟨948930, by rfl⟩ : syracuseStep 2530481 = 1897861) B1897861
theorem B1686707 : Blo 1686043 1686707 := bstep (se 1 (by rfl) ⟨1265030, by rfl⟩ : syracuseStep 1686707 = 2530061) B2530061
theorem B1686723 : Blo 1686043 1686723 := bstep (se 1 (by rfl) ⟨1265042, by rfl⟩ : syracuseStep 1686723 = 2530085) B2530085
theorem B2530499 : Blo 1686043 2530499 := bstep (se 1 (by rfl) ⟨1897874, by rfl⟩ : syracuseStep 2530499 = 3795749) B3795749
theorem B5692625 : Blo 1686043 5692625 := bstep (se 2 (by rfl) ⟨2134734, by rfl⟩ : syracuseStep 5692625 = 4269469) B4269469
theorem B1686739 : Blo 1686043 1686739 := bstep (se 1 (by rfl) ⟨1265054, by rfl⟩ : syracuseStep 1686739 = 2530109) B2530109
theorem B2530529 : Blo 1686043 2530529 := bstep (se 2 (by rfl) ⟨948948, by rfl⟩ : syracuseStep 2530529 = 1897897) B1897897
theorem B1686755 : Blo 1686043 1686755 := bstep (se 1 (by rfl) ⟨1265066, by rfl⟩ : syracuseStep 1686755 = 2530133) B2530133
theorem B1686771 : Blo 1686043 1686771 := bstep (se 1 (by rfl) ⟨1265078, by rfl⟩ : syracuseStep 1686771 = 2530157) B2530157
theorem B2530547 : Blo 1686043 2530547 := bstep (se 1 (by rfl) ⟨1897910, by rfl⟩ : syracuseStep 2530547 = 3795821) B3795821
theorem B1686787 : Blo 1686043 1686787 := bstep (se 1 (by rfl) ⟨1265090, by rfl⟩ : syracuseStep 1686787 = 2530181) B2530181
theorem B6405389 : Blo 1686043 6405389 := bstep (se 3 (by rfl) ⟨1201010, by rfl⟩ : syracuseStep 6405389 = 2402021) B2402021
theorem B2530577 : Blo 1686043 2530577 := bstep (se 2 (by rfl) ⟨948966, by rfl⟩ : syracuseStep 2530577 = 1897933) B1897933
theorem B1686803 : Blo 1686043 1686803 := bstep (se 1 (by rfl) ⟨1265102, by rfl⟩ : syracuseStep 1686803 = 2530205) B2530205
theorem B1686819 : Blo 1686043 1686819 := bstep (se 1 (by rfl) ⟨1265114, by rfl⟩ : syracuseStep 1686819 = 2530229) B2530229
theorem B2530595 : Blo 1686043 2530595 := bstep (se 1 (by rfl) ⟨1897946, by rfl⟩ : syracuseStep 2530595 = 3795893) B3795893
theorem B1686835 : Blo 1686043 1686835 := bstep (se 1 (by rfl) ⟨1265126, by rfl⟩ : syracuseStep 1686835 = 2530253) B2530253
theorem B2530625 : Blo 1686043 2530625 := bstep (se 2 (by rfl) ⟨948984, by rfl⟩ : syracuseStep 2530625 = 1897969) B1897969
theorem B1686851 : Blo 1686043 1686851 := bstep (se 1 (by rfl) ⟨1265138, by rfl⟩ : syracuseStep 1686851 = 2530277) B2530277
theorem B1686867 : Blo 1686043 1686867 := bstep (se 1 (by rfl) ⟨1265150, by rfl⟩ : syracuseStep 1686867 = 2530301) B2530301
theorem B2530643 : Blo 1686043 2530643 := bstep (se 1 (by rfl) ⟨1897982, by rfl⟩ : syracuseStep 2530643 = 3795965) B3795965
theorem B1686883 : Blo 1686043 1686883 := bstep (se 1 (by rfl) ⟨1265162, by rfl⟩ : syracuseStep 1686883 = 2530325) B2530325
theorem B2530673 : Blo 1686043 2530673 := bstep (se 2 (by rfl) ⟨949002, by rfl⟩ : syracuseStep 2530673 = 1898005) B1898005
theorem B1686899 : Blo 1686043 1686899 := bstep (se 1 (by rfl) ⟨1265174, by rfl⟩ : syracuseStep 1686899 = 2530349) B2530349
theorem B1686915 : Blo 1686043 1686915 := bstep (se 1 (by rfl) ⟨1265186, by rfl⟩ : syracuseStep 1686915 = 2530373) B2530373
theorem B2530691 : Blo 1686043 2530691 := bstep (se 1 (by rfl) ⟨1898018, by rfl⟩ : syracuseStep 2530691 = 3796037) B3796037
theorem B1686931 : Blo 1686043 1686931 := bstep (se 1 (by rfl) ⟨1265198, by rfl⟩ : syracuseStep 1686931 = 2530397) B2530397
theorem B2530721 : Blo 1686043 2530721 := bstep (se 2 (by rfl) ⟨949020, by rfl⟩ : syracuseStep 2530721 = 1898041) B1898041
theorem B1686947 : Blo 1686043 1686947 := bstep (se 1 (by rfl) ⟨1265210, by rfl⟩ : syracuseStep 1686947 = 2530421) B2530421
theorem B1686963 : Blo 1686043 1686963 := bstep (se 1 (by rfl) ⟨1265222, by rfl⟩ : syracuseStep 1686963 = 2530445) B2530445
theorem B2530739 : Blo 1686043 2530739 := bstep (se 1 (by rfl) ⟨1898054, by rfl⟩ : syracuseStep 2530739 = 3796109) B3796109
theorem B1686979 : Blo 1686043 1686979 := bstep (se 1 (by rfl) ⟨1265234, by rfl⟩ : syracuseStep 1686979 = 2530469) B2530469
theorem B2530769 : Blo 1686043 2530769 := bstep (se 2 (by rfl) ⟨949038, by rfl⟩ : syracuseStep 2530769 = 1898077) B1898077
theorem B1686995 : Blo 1686043 1686995 := bstep (se 1 (by rfl) ⟨1265246, by rfl⟩ : syracuseStep 1686995 = 2530493) B2530493
theorem B10255843 : Blo 1686043 10255843 := bstep (se 1 (by rfl) ⟨7691882, by rfl⟩ : syracuseStep 10255843 = 15383765) B15383765
theorem B1687011 : Blo 1686043 1687011 := bstep (se 1 (by rfl) ⟨1265258, by rfl⟩ : syracuseStep 1687011 = 2530517) B2530517
theorem B2530787 : Blo 1686043 2530787 := bstep (se 1 (by rfl) ⟨1898090, by rfl⟩ : syracuseStep 2530787 = 3796181) B3796181
theorem B1687027 : Blo 1686043 1687027 := bstep (se 1 (by rfl) ⟨1265270, by rfl⟩ : syracuseStep 1687027 = 2530541) B2530541
theorem B2530817 : Blo 1686043 2530817 := bstep (se 2 (by rfl) ⟨949056, by rfl⟩ : syracuseStep 2530817 = 1898113) B1898113
theorem B1687043 : Blo 1686043 1687043 := bstep (se 1 (by rfl) ⟨1265282, by rfl⟩ : syracuseStep 1687043 = 2530565) B2530565
theorem B3603971 : Blo 1686043 3603971 := bstep (se 1 (by rfl) ⟨2702978, by rfl⟩ : syracuseStep 3603971 = 5405957) B5405957
theorem B1687059 : Blo 1686043 1687059 := bstep (se 1 (by rfl) ⟨1265294, by rfl⟩ : syracuseStep 1687059 = 2530589) B2530589
theorem B2530835 : Blo 1686043 2530835 := bstep (se 1 (by rfl) ⟨1898126, by rfl⟩ : syracuseStep 2530835 = 3796253) B3796253
theorem B1687075 : Blo 1686043 1687075 := bstep (se 1 (by rfl) ⟨1265306, by rfl⟩ : syracuseStep 1687075 = 2530613) B2530613
theorem B2530865 : Blo 1686043 2530865 := bstep (se 2 (by rfl) ⟨949074, by rfl⟩ : syracuseStep 2530865 = 1898149) B1898149
theorem B1687091 : Blo 1686043 1687091 := bstep (se 1 (by rfl) ⟨1265318, by rfl⟩ : syracuseStep 1687091 = 2530637) B2530637
theorem B1687107 : Blo 1686043 1687107 := bstep (se 1 (by rfl) ⟨1265330, by rfl⟩ : syracuseStep 1687107 = 2530661) B2530661
theorem B2530883 : Blo 1686043 2530883 := bstep (se 1 (by rfl) ⟨1898162, by rfl⟩ : syracuseStep 2530883 = 3796325) B3796325
theorem B1687123 : Blo 1686043 1687123 := bstep (se 1 (by rfl) ⟨1265342, by rfl⟩ : syracuseStep 1687123 = 2530685) B2530685
theorem B1801811 : Blo 1686043 1801811 := bstep (se 1 (by rfl) ⟨1351358, by rfl⟩ : syracuseStep 1801811 = 2702717) B2702717
theorem B2530913 : Blo 1686043 2530913 := bstep (se 2 (by rfl) ⟨949092, by rfl⟩ : syracuseStep 2530913 = 1898185) B1898185
theorem B6332003 : Blo 1686043 6332003 := bstep (se 1 (by rfl) ⟨4749002, by rfl⟩ : syracuseStep 6332003 = 9498005) B9498005
theorem B1687139 : Blo 1686043 1687139 := bstep (se 1 (by rfl) ⟨1265354, by rfl⟩ : syracuseStep 1687139 = 2530709) B2530709
theorem B3038833 : Blo 1686043 3038833 := bstep (se 2 (by rfl) ⟨1139562, by rfl⟩ : syracuseStep 3038833 = 2279125) B2279125
theorem B1687155 : Blo 1686043 1687155 := bstep (se 1 (by rfl) ⟨1265366, by rfl⟩ : syracuseStep 1687155 = 2530733) B2530733
theorem B2530931 : Blo 1686043 2530931 := bstep (se 1 (by rfl) ⟨1898198, by rfl⟩ : syracuseStep 2530931 = 3796397) B3796397
theorem B1687171 : Blo 1686043 1687171 := bstep (se 1 (by rfl) ⟨1265378, by rfl⟩ : syracuseStep 1687171 = 2530757) B2530757
theorem B2530961 : Blo 1686043 2530961 := bstep (se 2 (by rfl) ⟨949110, by rfl⟩ : syracuseStep 2530961 = 1898221) B1898221
theorem B1687187 : Blo 1686043 1687187 := bstep (se 1 (by rfl) ⟨1265390, by rfl⟩ : syracuseStep 1687187 = 2530781) B2530781
theorem B1687203 : Blo 1686043 1687203 := bstep (se 1 (by rfl) ⟨1265402, by rfl⟩ : syracuseStep 1687203 = 2530805) B2530805
theorem B2530979 : Blo 1686043 2530979 := bstep (se 1 (by rfl) ⟨1898234, by rfl⟩ : syracuseStep 2530979 = 3796469) B3796469
theorem B4054691 : Blo 1686043 4054691 := bstep (se 1 (by rfl) ⟨3041018, by rfl⟩ : syracuseStep 4054691 = 6082037) B6082037
theorem B1687219 : Blo 1686043 1687219 := bstep (se 1 (by rfl) ⟨1265414, by rfl⟩ : syracuseStep 1687219 = 2530829) B2530829
theorem B2531009 : Blo 1686043 2531009 := bstep (se 2 (by rfl) ⟨949128, by rfl⟩ : syracuseStep 2531009 = 1898257) B1898257
theorem B1687235 : Blo 1686043 1687235 := bstep (se 1 (by rfl) ⟨1265426, by rfl⟩ : syracuseStep 1687235 = 2530853) B2530853
theorem B1687251 : Blo 1686043 1687251 := bstep (se 1 (by rfl) ⟨1265438, by rfl⟩ : syracuseStep 1687251 = 2530877) B2530877
theorem B2531027 : Blo 1686043 2531027 := bstep (se 1 (by rfl) ⟨1898270, by rfl⟩ : syracuseStep 2531027 = 3796541) B3796541
theorem B8535779 : Blo 1686043 8535779 := bstep (se 1 (by rfl) ⟨6401834, by rfl⟩ : syracuseStep 8535779 = 12803669) B12803669
theorem B1687267 : Blo 1686043 1687267 := bstep (se 1 (by rfl) ⟨1265450, by rfl⟩ : syracuseStep 1687267 = 2530901) B2530901
theorem B5693165 : Blo 1686043 5693165 := bstep (se 3 (by rfl) ⟨1067468, by rfl⟩ : syracuseStep 5693165 = 2134937) B2134937
theorem B2531057 : Blo 1686043 2531057 := bstep (se 2 (by rfl) ⟨949146, by rfl⟩ : syracuseStep 2531057 = 1898293) B1898293
theorem B1687283 : Blo 1686043 1687283 := bstep (se 1 (by rfl) ⟨1265462, by rfl⟩ : syracuseStep 1687283 = 2530925) B2530925
theorem B1687299 : Blo 1686043 1687299 := bstep (se 1 (by rfl) ⟨1265474, by rfl⟩ : syracuseStep 1687299 = 2530949) B2530949
theorem B2531075 : Blo 1686043 2531075 := bstep (se 1 (by rfl) ⟨1898306, by rfl⟩ : syracuseStep 2531075 = 3796613) B3796613
theorem B2703107 : Blo 1686043 2703107 := bstep (se 1 (by rfl) ⟨2027330, by rfl⟩ : syracuseStep 2703107 = 4054661) B4054661
theorem B1687315 : Blo 1686043 1687315 := bstep (se 1 (by rfl) ⟨1265486, by rfl⟩ : syracuseStep 1687315 = 2530973) B2530973
theorem B2531105 : Blo 1686043 2531105 := bstep (se 2 (by rfl) ⟨949164, by rfl⟩ : syracuseStep 2531105 = 1898329) B1898329
theorem B5693219 : Blo 1686043 5693219 := bstep (se 1 (by rfl) ⟨4269914, by rfl⟩ : syracuseStep 5693219 = 8539829) B8539829
theorem B1687331 : Blo 1686043 1687331 := bstep (se 1 (by rfl) ⟨1265498, by rfl⟩ : syracuseStep 1687331 = 2530997) B2530997
theorem B1687347 : Blo 1686043 1687347 := bstep (se 1 (by rfl) ⟨1265510, by rfl⟩ : syracuseStep 1687347 = 2531021) B2531021
theorem B2531123 : Blo 1686043 2531123 := bstep (se 1 (by rfl) ⟨1898342, by rfl⟩ : syracuseStep 2531123 = 3796685) B3796685
theorem B1687363 : Blo 1686043 1687363 := bstep (se 1 (by rfl) ⟨1265522, by rfl⟩ : syracuseStep 1687363 = 2531045) B2531045
theorem B2531153 : Blo 1686043 2531153 := bstep (se 2 (by rfl) ⟨949182, by rfl⟩ : syracuseStep 2531153 = 1898365) B1898365
theorem B1687379 : Blo 1686043 1687379 := bstep (se 1 (by rfl) ⟨1265534, by rfl⟩ : syracuseStep 1687379 = 2531069) B2531069
theorem B3202915 : Blo 1686043 3202915 := bstep (se 1 (by rfl) ⟨2402186, by rfl⟩ : syracuseStep 3202915 = 4804373) B4804373
theorem B1687395 : Blo 1686043 1687395 := bstep (se 1 (by rfl) ⟨1265546, by rfl⟩ : syracuseStep 1687395 = 2531093) B2531093
theorem B2531171 : Blo 1686043 2531171 := bstep (se 1 (by rfl) ⟨1898378, by rfl⟩ : syracuseStep 2531171 = 3796757) B3796757
theorem B1687411 : Blo 1686043 1687411 := bstep (se 1 (by rfl) ⟨1265558, by rfl⟩ : syracuseStep 1687411 = 2531117) B2531117
theorem B2531201 : Blo 1686043 2531201 := bstep (se 2 (by rfl) ⟨949200, by rfl⟩ : syracuseStep 2531201 = 1898401) B1898401
theorem B1687427 : Blo 1686043 1687427 := bstep (se 1 (by rfl) ⟨1265570, by rfl⟩ : syracuseStep 1687427 = 2531141) B2531141
theorem B2703235 : Blo 1686043 2703235 := bstep (se 1 (by rfl) ⟨2027426, by rfl⟩ : syracuseStep 2703235 = 4054853) B4054853
theorem B1687443 : Blo 1686043 1687443 := bstep (se 1 (by rfl) ⟨1265582, by rfl⟩ : syracuseStep 1687443 = 2531165) B2531165
theorem B2531219 : Blo 1686043 2531219 := bstep (se 1 (by rfl) ⟨1898414, by rfl⟩ : syracuseStep 2531219 = 3796829) B3796829
theorem B1687459 : Blo 1686043 1687459 := bstep (se 1 (by rfl) ⟨1265594, by rfl⟩ : syracuseStep 1687459 = 2531189) B2531189
theorem B2531249 : Blo 1686043 2531249 := bstep (se 2 (by rfl) ⟨949218, by rfl⟩ : syracuseStep 2531249 = 1898437) B1898437
theorem B7307185 : Blo 1686043 7307185 := bstep (se 2 (by rfl) ⟨2740194, by rfl⟩ : syracuseStep 7307185 = 5480389) B5480389
theorem B1687475 : Blo 1686043 1687475 := bstep (se 1 (by rfl) ⟨1265606, by rfl⟩ : syracuseStep 1687475 = 2531213) B2531213
theorem B1687491 : Blo 1686043 1687491 := bstep (se 1 (by rfl) ⟨1265618, by rfl⟩ : syracuseStep 1687491 = 2531237) B2531237
theorem B2531267 : Blo 1686043 2531267 := bstep (se 1 (by rfl) ⟨1898450, by rfl⟩ : syracuseStep 2531267 = 3796901) B3796901
theorem B2703299 : Blo 1686043 2703299 := bstep (se 1 (by rfl) ⟨2027474, by rfl⟩ : syracuseStep 2703299 = 4054949) B4054949
theorem B1687507 : Blo 1686043 1687507 := bstep (se 1 (by rfl) ⟨1265630, by rfl⟩ : syracuseStep 1687507 = 2531261) B2531261
theorem B2531297 : Blo 1686043 2531297 := bstep (se 2 (by rfl) ⟨949236, by rfl⟩ : syracuseStep 2531297 = 1898473) B1898473
theorem B1687523 : Blo 1686043 1687523 := bstep (se 1 (by rfl) ⟨1265642, by rfl⟩ : syracuseStep 1687523 = 2531285) B2531285
theorem B1687539 : Blo 1686043 1687539 := bstep (se 1 (by rfl) ⟨1265654, by rfl⟩ : syracuseStep 1687539 = 2531309) B2531309
theorem B2531315 : Blo 1686043 2531315 := bstep (se 1 (by rfl) ⟨1898486, by rfl⟩ : syracuseStep 2531315 = 3796973) B3796973
theorem B2531339 : Blo 1686043 2531339 := bstep (se 1 (by rfl) ⟨1898504, by rfl⟩ : syracuseStep 2531339 = 3797009) B3797009
theorem B1687563 : Blo 1686043 1687563 := bstep (se 1 (by rfl) ⟨1265672, by rfl⟩ : syracuseStep 1687563 = 2531345) B2531345
theorem B2531351 : Blo 1686043 2531351 := bstep (se 1 (by rfl) ⟨1898513, by rfl⟩ : syracuseStep 2531351 = 3797027) B3797027
theorem B1687575 : Blo 1686043 1687575 := bstep (se 1 (by rfl) ⟨1265681, by rfl⟩ : syracuseStep 1687575 = 2531363) B2531363
theorem B2703383 : Blo 1686043 2703383 := bstep (se 1 (by rfl) ⟨2027537, by rfl⟩ : syracuseStep 2703383 = 4055075) B4055075
theorem B1687595 : Blo 1686043 1687595 := bstep (se 1 (by rfl) ⟨1265696, by rfl⟩ : syracuseStep 1687595 = 2531393) B2531393
theorem B1687607 : Blo 1686043 1687607 := bstep (se 1 (by rfl) ⟨1265705, by rfl⟩ : syracuseStep 1687607 = 2531411) B2531411
theorem B1687627 : Blo 1686043 1687627 := bstep (se 1 (by rfl) ⟨1265720, by rfl⟩ : syracuseStep 1687627 = 2531441) B2531441
theorem B1687639 : Blo 1686043 1687639 := bstep (se 1 (by rfl) ⟨1265729, by rfl⟩ : syracuseStep 1687639 = 2531459) B2531459
theorem B2531417 : Blo 1686043 2531417 := bstep (se 2 (by rfl) ⟨949281, by rfl⟩ : syracuseStep 2531417 = 1898563) B1898563
theorem B1687659 : Blo 1686043 1687659 := bstep (se 1 (by rfl) ⟨1265744, by rfl⟩ : syracuseStep 1687659 = 2531489) B2531489
theorem B1687671 : Blo 1686043 1687671 := bstep (se 1 (by rfl) ⟨1265753, by rfl⟩ : syracuseStep 1687671 = 2531507) B2531507
theorem B1687691 : Blo 1686043 1687691 := bstep (se 1 (by rfl) ⟨1265768, by rfl⟩ : syracuseStep 1687691 = 2531537) B2531537
theorem B1687703 : Blo 1686043 1687703 := bstep (se 1 (by rfl) ⟨1265777, by rfl⟩ : syracuseStep 1687703 = 2531555) B2531555
theorem B14418071 : Blo 1686043 14418071 := bstep (se 1 (by rfl) ⟨10813553, by rfl⟩ : syracuseStep 14418071 = 21627107) B21627107
theorem B1687723 : Blo 1686043 1687723 := bstep (se 1 (by rfl) ⟨1265792, by rfl⟩ : syracuseStep 1687723 = 2531585) B2531585
theorem B1687735 : Blo 1686043 1687735 := bstep (se 1 (by rfl) ⟨1265801, by rfl⟩ : syracuseStep 1687735 = 2531603) B2531603
theorem B2531531 : Blo 1686043 2531531 := bstep (se 1 (by rfl) ⟨1898648, by rfl⟩ : syracuseStep 2531531 = 3797297) B3797297
theorem B1687755 : Blo 1686043 1687755 := bstep (se 1 (by rfl) ⟨1265816, by rfl⟩ : syracuseStep 1687755 = 2531633) B2531633
theorem B2531543 : Blo 1686043 2531543 := bstep (se 1 (by rfl) ⟨1898657, by rfl⟩ : syracuseStep 2531543 = 3797315) B3797315
theorem B1687767 : Blo 1686043 1687767 := bstep (se 1 (by rfl) ⟨1265825, by rfl⟩ : syracuseStep 1687767 = 2531651) B2531651
theorem B6406361 : Blo 1686043 6406361 := bstep (se 2 (by rfl) ⟨2402385, by rfl⟩ : syracuseStep 6406361 = 4804771) B4804771
theorem B1687787 : Blo 1686043 1687787 := bstep (se 1 (by rfl) ⟨1265840, by rfl⟩ : syracuseStep 1687787 = 2531681) B2531681
theorem B1687799 : Blo 1686043 1687799 := bstep (se 1 (by rfl) ⟨1265849, by rfl⟩ : syracuseStep 1687799 = 2531699) B2531699
theorem B41025797 : Blo 1686043 41025797 := bstep (se 4 (by rfl) ⟨3846168, by rfl⟩ : syracuseStep 41025797 = 7692337) B7692337
theorem B1687819 : Blo 1686043 1687819 := bstep (se 1 (by rfl) ⟨1265864, by rfl⟩ : syracuseStep 1687819 = 2531729) B2531729
theorem B1687831 : Blo 1686043 1687831 := bstep (se 1 (by rfl) ⟨1265873, by rfl⟩ : syracuseStep 1687831 = 2531747) B2531747
theorem B2531609 : Blo 1686043 2531609 := bstep (se 2 (by rfl) ⟨949353, by rfl⟩ : syracuseStep 2531609 = 1898707) B1898707
theorem B1687851 : Blo 1686043 1687851 := bstep (se 1 (by rfl) ⟨1265888, by rfl⟩ : syracuseStep 1687851 = 2531777) B2531777
theorem B1687863 : Blo 1686043 1687863 := bstep (se 1 (by rfl) ⟨1265897, by rfl⟩ : syracuseStep 1687863 = 2531795) B2531795
theorem B1687883 : Blo 1686043 1687883 := bstep (se 1 (by rfl) ⟨1265912, by rfl⟩ : syracuseStep 1687883 = 2531825) B2531825
theorem B1687895 : Blo 1686043 1687895 := bstep (se 1 (by rfl) ⟨1265921, by rfl⟩ : syracuseStep 1687895 = 2531843) B2531843
theorem B1687915 : Blo 1686043 1687915 := bstep (se 1 (by rfl) ⟨1265936, by rfl⟩ : syracuseStep 1687915 = 2531873) B2531873
theorem B1687927 : Blo 1686043 1687927 := bstep (se 1 (by rfl) ⟨1265945, by rfl⟩ : syracuseStep 1687927 = 2531891) B2531891
theorem B2531723 : Blo 1686043 2531723 := bstep (se 1 (by rfl) ⟨1898792, by rfl⟩ : syracuseStep 2531723 = 3797585) B3797585
theorem B1687947 : Blo 1686043 1687947 := bstep (se 1 (by rfl) ⟨1265960, by rfl⟩ : syracuseStep 1687947 = 2531921) B2531921
theorem B2531735 : Blo 1686043 2531735 := bstep (se 1 (by rfl) ⟨1898801, by rfl⟩ : syracuseStep 2531735 = 3797603) B3797603
theorem B1687959 : Blo 1686043 1687959 := bstep (se 1 (by rfl) ⟨1265969, by rfl⟩ : syracuseStep 1687959 = 2531939) B2531939
theorem B1687979 : Blo 1686043 1687979 := bstep (se 1 (by rfl) ⟨1265984, by rfl⟩ : syracuseStep 1687979 = 2531969) B2531969
theorem B6406573 : Blo 1686043 6406573 := bstep (se 3 (by rfl) ⟨1201232, by rfl⟩ : syracuseStep 6406573 = 2402465) B2402465
theorem B1687991 : Blo 1686043 1687991 := bstep (se 1 (by rfl) ⟨1265993, by rfl⟩ : syracuseStep 1687991 = 2531987) B2531987
theorem B3039691 : Blo 1686043 3039691 := bstep (se 1 (by rfl) ⟨2279768, by rfl⟩ : syracuseStep 3039691 = 4559537) B4559537
theorem B1688011 : Blo 1686043 1688011 := bstep (se 1 (by rfl) ⟨1266008, by rfl⟩ : syracuseStep 1688011 = 2532017) B2532017
theorem B1688023 : Blo 1686043 1688023 := bstep (se 1 (by rfl) ⟨1266017, by rfl⟩ : syracuseStep 1688023 = 2532035) B2532035
theorem B3203545 : Blo 1686043 3203545 := bstep (se 2 (by rfl) ⟨1201329, by rfl⟩ : syracuseStep 3203545 = 2402659) B2402659
theorem B2531801 : Blo 1686043 2531801 := bstep (se 2 (by rfl) ⟨949425, by rfl⟩ : syracuseStep 2531801 = 1898851) B1898851
theorem B1688043 : Blo 1686043 1688043 := bstep (se 1 (by rfl) ⟨1266032, by rfl⟩ : syracuseStep 1688043 = 2532065) B2532065
theorem B5693975 : Blo 1686043 5693975 := bstep (se 1 (by rfl) ⟨4270481, by rfl⟩ : syracuseStep 5693975 = 8540963) B8540963
theorem B6840877 : Blo 1686043 6840877 := bstep (se 3 (by rfl) ⟨1282664, by rfl⟩ : syracuseStep 6840877 = 2565329) B2565329
theorem B4268609 : Blo 1686043 4268609 := bstep (se 2 (by rfl) ⟨1600728, by rfl⟩ : syracuseStep 4268609 = 3201457) B3201457
theorem B3605057 : Blo 1686043 3605057 := bstep (se 2 (by rfl) ⟨1351896, by rfl⟩ : syracuseStep 3605057 = 2703793) B2703793
theorem B2531915 : Blo 1686043 2531915 := bstep (se 1 (by rfl) ⟨1898936, by rfl⟩ : syracuseStep 2531915 = 3797873) B3797873
theorem B2531927 : Blo 1686043 2531927 := bstep (se 1 (by rfl) ⟨1898945, by rfl⟩ : syracuseStep 2531927 = 3797891) B3797891
theorem B2531993 : Blo 1686043 2531993 := bstep (se 2 (by rfl) ⟨949497, by rfl⟩ : syracuseStep 2531993 = 1898995) B1898995
theorem B3039923 : Blo 1686043 3039923 := bstep (se 1 (by rfl) ⟨2279942, by rfl⟩ : syracuseStep 3039923 = 4559885) B4559885
theorem B3793625 : Blo 1686043 3793625 := bstep (se 2 (by rfl) ⟨1422609, by rfl⟩ : syracuseStep 3793625 = 2845219) B2845219
theorem B6406877 : Blo 1686043 6406877 := bstep (se 3 (by rfl) ⟨1201289, by rfl⟩ : syracuseStep 6406877 = 2402579) B2402579
theorem B4801331 : Blo 1686043 4801331 := bstep (se 1 (by rfl) ⟨3600998, by rfl⟩ : syracuseStep 4801331 = 7201997) B7201997
theorem B3793715 : Blo 1686043 3793715 := bstep (se 1 (by rfl) ⟨2845286, by rfl⟩ : syracuseStep 3793715 = 5690573) B5690573
theorem B10257227 : Blo 1686043 10257227 := bstep (se 1 (by rfl) ⟨7692920, by rfl⟩ : syracuseStep 10257227 = 15385841) B15385841
theorem B3793751 : Blo 1686043 3793751 := bstep (se 1 (by rfl) ⟨2845313, by rfl⟩ : syracuseStep 3793751 = 5690627) B5690627
theorem B8545175 : Blo 1686043 8545175 := bstep (se 1 (by rfl) ⟨6408881, by rfl⟩ : syracuseStep 8545175 = 12817763) B12817763
theorem B3793931 : Blo 1686043 3793931 := bstep (se 1 (by rfl) ⟨2845448, by rfl⟩ : syracuseStep 3793931 = 5690897) B5690897
theorem B3204107 : Blo 1686043 3204107 := bstep (se 1 (by rfl) ⟨2403080, by rfl⟩ : syracuseStep 3204107 = 4806161) B4806161
theorem B10257425 : Blo 1686043 10257425 := bstep (se 2 (by rfl) ⟨3846534, by rfl⟩ : syracuseStep 10257425 = 7693069) B7693069
theorem B6079511 : Blo 1686043 6079511 := bstep (se 1 (by rfl) ⟨4559633, by rfl⟩ : syracuseStep 6079511 = 9119267) B9119267
theorem B5694515 : Blo 1686043 5694515 := bstep (se 1 (by rfl) ⟨4270886, by rfl⟩ : syracuseStep 5694515 = 8541773) B8541773
theorem B3793985 : Blo 1686043 3793985 := bstep (se 2 (by rfl) ⟨1422744, by rfl⟩ : syracuseStep 3793985 = 2845489) B2845489
theorem B4269145 : Blo 1686043 4269145 := bstep (se 2 (by rfl) ⟨1600929, by rfl⟩ : syracuseStep 4269145 = 3201859) B3201859
theorem B7210129 : Blo 1686043 7210129 := bstep (se 2 (by rfl) ⟨2703798, by rfl⟩ : syracuseStep 7210129 = 5407597) B5407597
theorem B4326551 : Blo 1686043 4326551 := bstep (se 1 (by rfl) ⟨3244913, by rfl⟩ : syracuseStep 4326551 = 6489827) B6489827
theorem B3204289 : Blo 1686043 3204289 := bstep (se 2 (by rfl) ⟨1201608, by rfl⟩ : syracuseStep 3204289 = 2403217) B2403217
theorem B3794201 : Blo 1686043 3794201 := bstep (se 2 (by rfl) ⟨1422825, by rfl⟩ : syracuseStep 3794201 = 2845651) B2845651
theorem B5694785 : Blo 1686043 5694785 := bstep (se 2 (by rfl) ⟨2135544, by rfl⟩ : syracuseStep 5694785 = 4271089) B4271089
theorem B9610589 : Blo 1686043 9610589 := bstep (se 3 (by rfl) ⟨1801985, by rfl⟩ : syracuseStep 9610589 = 3603971) B3603971
theorem B3794291 : Blo 1686043 3794291 := bstep (se 1 (by rfl) ⟨2845718, by rfl⟩ : syracuseStep 3794291 = 5691437) B5691437
theorem B3794327 : Blo 1686043 3794327 := bstep (se 1 (by rfl) ⟨2845745, by rfl⟩ : syracuseStep 3794327 = 5691491) B5691491
theorem B8537561 : Blo 1686043 8537561 := bstep (se 2 (by rfl) ⟨3201585, by rfl⟩ : syracuseStep 8537561 = 6403171) B6403171
theorem B24053317 : Blo 1686043 24053317 := bstep (se 4 (by rfl) ⟨2254998, by rfl⟩ : syracuseStep 24053317 = 4509997) B4509997
theorem B3794507 : Blo 1686043 3794507 := bstep (se 1 (by rfl) ⟨2845880, by rfl⟩ : syracuseStep 3794507 = 5691761) B5691761
theorem B34612829 : Blo 1686043 34612829 := bstep (se 3 (by rfl) ⟨6489905, by rfl⟩ : syracuseStep 34612829 = 12979811) B12979811
theorem B3794561 : Blo 1686043 3794561 := bstep (se 2 (by rfl) ⟨1422960, by rfl⟩ : syracuseStep 3794561 = 2845921) B2845921
theorem B2279179 : Blo 1686043 2279179 := bstep (se 1 (by rfl) ⟨1709384, by rfl⟩ : syracuseStep 2279179 = 3418769) B3418769
theorem B7202611 : Blo 1686043 7202611 := bstep (se 1 (by rfl) ⟨5401958, by rfl⟩ : syracuseStep 7202611 = 10803917) B10803917
theorem B3041075 : Blo 1686043 3041075 := bstep (se 1 (by rfl) ⟨2280806, by rfl⟩ : syracuseStep 3041075 = 4561613) B4561613
theorem B3041111 : Blo 1686043 3041111 := bstep (se 1 (by rfl) ⟨2280833, by rfl⟩ : syracuseStep 3041111 = 4561667) B4561667
theorem B3794777 : Blo 1686043 3794777 := bstep (se 2 (by rfl) ⟨1423041, by rfl⟩ : syracuseStep 3794777 = 2846083) B2846083
theorem B5695325 : Blo 1686043 5695325 := bstep (se 3 (by rfl) ⟨1067873, by rfl⟩ : syracuseStep 5695325 = 2135747) B2135747
theorem B3794867 : Blo 1686043 3794867 := bstep (se 1 (by rfl) ⟨2846150, by rfl⟩ : syracuseStep 3794867 = 5692301) B5692301
theorem B3794903 : Blo 1686043 3794903 := bstep (se 1 (by rfl) ⟨2846177, by rfl⟩ : syracuseStep 3794903 = 5692355) B5692355
theorem B13674457 : Blo 1686043 13674457 := bstep (se 2 (by rfl) ⟨5127921, by rfl⟩ : syracuseStep 13674457 = 10255843) B10255843
theorem B6932441 : Blo 1686043 6932441 := bstep (se 2 (by rfl) ⟨2599665, by rfl⟩ : syracuseStep 6932441 = 5199331) B5199331
theorem B4868171 : Blo 1686043 4868171 := bstep (se 1 (by rfl) ⟨3651128, by rfl⟩ : syracuseStep 4868171 = 7302257) B7302257
theorem B3795083 : Blo 1686043 3795083 := bstep (se 1 (by rfl) ⟨2846312, by rfl⟩ : syracuseStep 3795083 = 5692625) B5692625
theorem B6162605 : Blo 1686043 6162605 := bstep (se 3 (by rfl) ⟨1155488, by rfl⟩ : syracuseStep 6162605 = 2310977) B2310977
theorem B4270259 : Blo 1686043 4270259 := bstep (se 1 (by rfl) ⟨3202694, by rfl⟩ : syracuseStep 4270259 = 6405389) B6405389
theorem B3795137 : Blo 1686043 3795137 := bstep (se 2 (by rfl) ⟨1423176, by rfl⟩ : syracuseStep 3795137 = 2846353) B2846353
theorem B4221335 : Blo 1686043 4221335 := bstep (se 1 (by rfl) ⟨3166001, by rfl⟩ : syracuseStep 4221335 = 6332003) B6332003
theorem B3795353 : Blo 1686043 3795353 := bstep (se 2 (by rfl) ⟨1423257, by rfl⟩ : syracuseStep 3795353 = 2846515) B2846515
theorem B4270553 : Blo 1686043 4270553 := bstep (se 2 (by rfl) ⟨1601457, by rfl⟩ : syracuseStep 4270553 = 3202915) B3202915
theorem B3795443 : Blo 1686043 3795443 := bstep (se 1 (by rfl) ⟨2846582, by rfl⟩ : syracuseStep 3795443 = 5693165) B5693165
theorem B32426513 : Blo 1686043 32426513 := bstep (se 2 (by rfl) ⟨12159942, by rfl⟩ : syracuseStep 32426513 = 24319885) B24319885
theorem B3795479 : Blo 1686043 3795479 := bstep (se 1 (by rfl) ⟨2846609, by rfl⟩ : syracuseStep 3795479 = 5693219) B5693219
theorem B9742913 : Blo 1686043 9742913 := bstep (se 2 (by rfl) ⟨3653592, by rfl⟩ : syracuseStep 9742913 = 7307185) B7307185
theorem B2845273 : Blo 1686043 2845273 := bstep (se 2 (by rfl) ⟨1066977, by rfl⟩ : syracuseStep 2845273 = 2133955) B2133955
theorem B3795659 : Blo 1686043 3795659 := bstep (se 1 (by rfl) ⟨2846744, by rfl⟩ : syracuseStep 3795659 = 5693489) B5693489
theorem B7801561 : Blo 1686043 7801561 := bstep (se 2 (by rfl) ⟨2925585, by rfl⟩ : syracuseStep 7801561 = 5851171) B5851171
theorem B3795713 : Blo 1686043 3795713 := bstep (se 2 (by rfl) ⟨1423392, by rfl⟩ : syracuseStep 3795713 = 2846785) B2846785
theorem B6843329 : Blo 1686043 6843329 := bstep (se 2 (by rfl) ⟨2566248, by rfl⟩ : syracuseStep 6843329 = 5132497) B5132497
theorem B5696459 : Blo 1686043 5696459 := bstep (se 1 (by rfl) ⟨4272344, by rfl⟩ : syracuseStep 5696459 = 8544689) B8544689
theorem B3795929 : Blo 1686043 3795929 := bstep (se 2 (by rfl) ⟨1423473, by rfl⟩ : syracuseStep 3795929 = 2846947) B2846947
theorem B6491153 : Blo 1686043 6491153 := bstep (se 2 (by rfl) ⟨2434182, by rfl⟩ : syracuseStep 6491153 = 4868365) B4868365
theorem B8539181 : Blo 1686043 8539181 := bstep (se 3 (by rfl) ⟨1601096, by rfl⟩ : syracuseStep 8539181 = 3202193) B3202193
theorem B3796019 : Blo 1686043 3796019 := bstep (se 1 (by rfl) ⟨2847014, by rfl⟩ : syracuseStep 3796019 = 5694029) B5694029
theorem B6081587 : Blo 1686043 6081587 := bstep (se 1 (by rfl) ⟨4561190, by rfl⟩ : syracuseStep 6081587 = 9122381) B9122381
theorem B6843457 : Blo 1686043 6843457 := bstep (se 2 (by rfl) ⟨2566296, by rfl⟩ : syracuseStep 6843457 = 5132593) B5132593
theorem B3796055 : Blo 1686043 3796055 := bstep (se 1 (by rfl) ⟨2847041, by rfl⟩ : syracuseStep 3796055 = 5694083) B5694083
theorem B9120869 : Blo 1686043 9120869 := bstep (se 4 (by rfl) ⟨855081, by rfl⟩ : syracuseStep 9120869 = 1710163) B1710163
theorem B2845847 : Blo 1686043 2845847 := bstep (se 1 (by rfl) ⟨2134385, by rfl⟩ : syracuseStep 2845847 = 4268771) B4268771
theorem B2403479 : Blo 1686043 2403479 := bstep (se 1 (by rfl) ⟨1802609, by rfl⟩ : syracuseStep 2403479 = 3605219) B3605219
theorem B5696729 : Blo 1686043 5696729 := bstep (se 2 (by rfl) ⟨2136273, by rfl⟩ : syracuseStep 5696729 = 4272547) B4272547
theorem B7204099 : Blo 1686043 7204099 := bstep (se 1 (by rfl) ⟨5403074, by rfl⟩ : syracuseStep 7204099 = 10806149) B10806149
theorem B3796235 : Blo 1686043 3796235 := bstep (se 1 (by rfl) ⟨2847176, by rfl⟩ : syracuseStep 3796235 = 5694353) B5694353
theorem B2845975 : Blo 1686043 2845975 := bstep (se 1 (by rfl) ⟨2134481, by rfl⟩ : syracuseStep 2845975 = 4268963) B4268963
theorem B3796289 : Blo 1686043 3796289 := bstep (se 2 (by rfl) ⟨1423608, by rfl⟩ : syracuseStep 3796289 = 2847217) B2847217
theorem B29232485 : Blo 1686043 29232485 := bstep (se 4 (by rfl) ⟨2740545, by rfl⟩ : syracuseStep 29232485 = 5481091) B5481091
theorem B8220035 : Blo 1686043 8220035 := bstep (se 1 (by rfl) ⟨6165026, by rfl⟩ : syracuseStep 8220035 = 12330053) B12330053
theorem B4804019 : Blo 1686043 4804019 := bstep (se 1 (by rfl) ⟨3603014, by rfl⟩ : syracuseStep 4804019 = 7206029) B7206029
theorem B15388177 : Blo 1686043 15388177 := bstep (se 2 (by rfl) ⟨5770566, by rfl⟩ : syracuseStep 15388177 = 11541133) B11541133
theorem B3796505 : Blo 1686043 3796505 := bstep (se 2 (by rfl) ⟨1423689, by rfl⟩ : syracuseStep 3796505 = 2847379) B2847379
theorem B3796595 : Blo 1686043 3796595 := bstep (se 1 (by rfl) ⟨2847446, by rfl⟩ : syracuseStep 3796595 = 5694893) B5694893
theorem B49294979 : Blo 1686043 49294979 := bstep (se 1 (by rfl) ⟨36971234, by rfl⟩ : syracuseStep 49294979 = 73942469) B73942469
theorem B4804247 : Blo 1686043 4804247 := bstep (se 1 (by rfl) ⟨3603185, by rfl⟩ : syracuseStep 4804247 = 7206371) B7206371
theorem B3796631 : Blo 1686043 3796631 := bstep (se 1 (by rfl) ⟨2847473, by rfl⟩ : syracuseStep 3796631 = 5694947) B5694947
theorem B6844121 : Blo 1686043 6844121 := bstep (se 2 (by rfl) ⟨2566545, by rfl⟩ : syracuseStep 6844121 = 5133091) B5133091
theorem B9604939 : Blo 1686043 9604939 := bstep (se 1 (by rfl) ⟨7203704, by rfl⟩ : syracuseStep 9604939 = 14407409) B14407409
theorem B3796811 : Blo 1686043 3796811 := bstep (se 1 (by rfl) ⟨2847608, by rfl⟩ : syracuseStep 3796811 = 5695217) B5695217
theorem B7204697 : Blo 1686043 7204697 := bstep (se 2 (by rfl) ⟨2701761, by rfl⟩ : syracuseStep 7204697 = 5403523) B5403523
theorem B3796865 : Blo 1686043 3796865 := bstep (se 2 (by rfl) ⟨1423824, by rfl⟩ : syracuseStep 3796865 = 2847649) B2847649
theorem B9613187 : Blo 1686043 9613187 := bstep (se 1 (by rfl) ⟨7209890, by rfl⟩ : syracuseStep 9613187 = 14419781) B14419781
theorem B2846603 : Blo 1686043 2846603 := bstep (se 1 (by rfl) ⟨2134952, by rfl⟩ : syracuseStep 2846603 = 4269905) B4269905
theorem B12816305 : Blo 1686043 12816305 := bstep (se 2 (by rfl) ⟨4806114, by rfl⟩ : syracuseStep 12816305 = 9612229) B9612229
theorem B3420083 : Blo 1686043 3420083 := bstep (se 1 (by rfl) ⟨2565062, by rfl⟩ : syracuseStep 3420083 = 5130125) B5130125
theorem B4804555 : Blo 1686043 4804555 := bstep (se 1 (by rfl) ⟨3603416, by rfl⟩ : syracuseStep 4804555 = 7206833) B7206833
theorem B2846731 : Blo 1686043 2846731 := bstep (se 1 (by rfl) ⟨2135048, by rfl⟩ : syracuseStep 2846731 = 4270097) B4270097
theorem B4272203 : Blo 1686043 4272203 := bstep (se 1 (by rfl) ⟨3204152, by rfl⟩ : syracuseStep 4272203 = 6408305) B6408305
theorem B3797081 : Blo 1686043 3797081 := bstep (se 2 (by rfl) ⟨1423905, by rfl⟩ : syracuseStep 3797081 = 2847811) B2847811
theorem B9605213 : Blo 1686043 9605213 := bstep (se 3 (by rfl) ⟨1800977, by rfl⟩ : syracuseStep 9605213 = 3601955) B3601955
theorem B12988517 : Blo 1686043 12988517 := bstep (se 4 (by rfl) ⟨1217673, by rfl⟩ : syracuseStep 12988517 = 2435347) B2435347
theorem B6402199 : Blo 1686043 6402199 := bstep (se 1 (by rfl) ⟨4801649, by rfl⟩ : syracuseStep 6402199 = 9603299) B9603299
theorem B2846873 : Blo 1686043 2846873 := bstep (se 2 (by rfl) ⟨1067577, by rfl⟩ : syracuseStep 2846873 = 2135155) B2135155
theorem B3797171 : Blo 1686043 3797171 := bstep (se 1 (by rfl) ⟨2847878, by rfl⟩ : syracuseStep 3797171 = 5695757) B5695757
theorem B7205057 : Blo 1686043 7205057 := bstep (se 2 (by rfl) ⟨2701896, by rfl⟩ : syracuseStep 7205057 = 5403793) B5403793
theorem B3797207 : Blo 1686043 3797207 := bstep (se 1 (by rfl) ⟨2847905, by rfl⟩ : syracuseStep 3797207 = 5695811) B5695811
theorem B4804829 : Blo 1686043 4804829 := bstep (se 3 (by rfl) ⟨900905, by rfl⟩ : syracuseStep 4804829 = 1801811) B1801811
theorem B2847001 : Blo 1686043 2847001 := bstep (se 2 (by rfl) ⟨1067625, by rfl⟩ : syracuseStep 2847001 = 2135251) B2135251
theorem B3797387 : Blo 1686043 3797387 := bstep (se 1 (by rfl) ⟨2848040, by rfl⟩ : syracuseStep 3797387 = 5696081) B5696081
theorem B14807447 : Blo 1686043 14807447 := bstep (se 1 (by rfl) ⟨11105585, by rfl⟩ : syracuseStep 14807447 = 22211171) B22211171
theorem B12816791 : Blo 1686043 12816791 := bstep (se 1 (by rfl) ⟨9612593, by rfl⟩ : syracuseStep 12816791 = 19225187) B19225187
theorem B7025089 : Blo 1686043 7025089 := bstep (se 2 (by rfl) ⟨2634408, by rfl⟩ : syracuseStep 7025089 = 5268817) B5268817
theorem B3797441 : Blo 1686043 3797441 := bstep (se 2 (by rfl) ⟨1424040, by rfl⟩ : syracuseStep 3797441 = 2848081) B2848081
theorem B1896907 : Blo 1686043 1896907 := bstep (se 1 (by rfl) ⟨1422680, by rfl⟩ : syracuseStep 1896907 = 2845361) B2845361
theorem B14414381 : Blo 1686043 14414381 := bstep (se 3 (by rfl) ⟨2702696, by rfl⟩ : syracuseStep 14414381 = 5405393) B5405393
theorem B1897015 : Blo 1686043 1897015 := bstep (se 1 (by rfl) ⟨1422761, by rfl⟩ : syracuseStep 1897015 = 2845523) B2845523
theorem B2134603 : Blo 1686043 2134603 := bstep (se 1 (by rfl) ⟨1600952, by rfl⟩ : syracuseStep 2134603 = 3201905) B3201905
theorem B13677149 : Blo 1686043 13677149 := bstep (se 3 (by rfl) ⟨2564465, by rfl⟩ : syracuseStep 13677149 = 5128931) B5128931
theorem B3797657 : Blo 1686043 3797657 := bstep (se 2 (by rfl) ⟨1424121, by rfl⟩ : syracuseStep 3797657 = 2848243) B2848243
theorem B1897195 : Blo 1686043 1897195 := bstep (se 1 (by rfl) ⟨1422896, by rfl⟩ : syracuseStep 1897195 = 2845793) B2845793
theorem B3846899 : Blo 1686043 3846899 := bstep (se 1 (by rfl) ⟨2885174, by rfl⟩ : syracuseStep 3846899 = 5770349) B5770349
theorem B3797747 : Blo 1686043 3797747 := bstep (se 1 (by rfl) ⟨2848310, by rfl⟩ : syracuseStep 3797747 = 5696621) B5696621
theorem B3797783 : Blo 1686043 3797783 := bstep (se 1 (by rfl) ⟨2848337, by rfl⟩ : syracuseStep 3797783 = 5696675) B5696675
theorem B4051777 : Blo 1686043 4051777 := bstep (se 2 (by rfl) ⟨1519416, by rfl⟩ : syracuseStep 4051777 = 3038833) B3038833
theorem B1897303 : Blo 1686043 1897303 := bstep (se 1 (by rfl) ⟨1422977, by rfl⟩ : syracuseStep 1897303 = 2845955) B2845955
theorem B2847575 : Blo 1686043 2847575 := bstep (se 1 (by rfl) ⟨2135681, by rfl⟩ : syracuseStep 2847575 = 4271363) B4271363
theorem B5403485 : Blo 1686043 5403485 := bstep (se 3 (by rfl) ⟨1013153, by rfl⟩ : syracuseStep 5403485 = 2026307) B2026307
theorem B17314661 : Blo 1686043 17314661 := bstep (se 4 (by rfl) ⟨1623249, by rfl⟩ : syracuseStep 17314661 = 3246499) B3246499
theorem B6402989 : Blo 1686043 6402989 := bstep (se 3 (by rfl) ⟨1200560, by rfl⟩ : syracuseStep 6402989 = 2401121) B2401121
theorem B3797963 : Blo 1686043 3797963 := bstep (se 1 (by rfl) ⟨2848472, by rfl⟩ : syracuseStep 3797963 = 5696945) B5696945
theorem B2847703 : Blo 1686043 2847703 := bstep (se 1 (by rfl) ⟨2135777, by rfl⟩ : syracuseStep 2847703 = 4271555) B4271555
theorem B3798017 : Blo 1686043 3798017 := bstep (se 2 (by rfl) ⟨1424256, by rfl⟩ : syracuseStep 3798017 = 2848513) B2848513
theorem B1897483 : Blo 1686043 1897483 := bstep (se 1 (by rfl) ⟨1423112, by rfl⟩ : syracuseStep 1897483 = 2846225) B2846225
theorem B8107073 : Blo 1686043 8107073 := bstep (se 2 (by rfl) ⟨3040152, by rfl⟩ : syracuseStep 8107073 = 6080305) B6080305
theorem B1733719 : Blo 1686043 1733719 := bstep (se 1 (by rfl) ⟨1300289, by rfl⟩ : syracuseStep 1733719 = 2600579) B2600579
theorem B1897591 : Blo 1686043 1897591 := bstep (se 1 (by rfl) ⟨1423193, by rfl⟩ : syracuseStep 1897591 = 2846387) B2846387
theorem B5690519 : Blo 1686043 5690519 := bstep (se 1 (by rfl) ⟨4267889, by rfl⟩ : syracuseStep 5690519 = 8535779) B8535779
theorem B1897771 : Blo 1686043 1897771 := bstep (se 1 (by rfl) ⟨1423328, by rfl⟩ : syracuseStep 1897771 = 2846657) B2846657
theorem B7796033 : Blo 1686043 7796033 := bstep (se 2 (by rfl) ⟨2923512, by rfl⟩ : syracuseStep 7796033 = 5847025) B5847025
theorem B1897879 : Blo 1686043 1897879 := bstep (se 1 (by rfl) ⟨1423409, by rfl⟩ : syracuseStep 1897879 = 2846819) B2846819
theorem B6493613 : Blo 1686043 6493613 := bstep (se 3 (by rfl) ⟨1217552, by rfl⟩ : syracuseStep 6493613 = 2435105) B2435105
theorem B20510131 : Blo 1686043 20510131 := bstep (se 1 (by rfl) ⟨15382598, by rfl⟩ : syracuseStep 20510131 = 30765197) B30765197
theorem B3601921 : Blo 1686043 3601921 := bstep (se 2 (by rfl) ⟨1350720, by rfl⟩ : syracuseStep 3601921 = 2701441) B2701441
theorem B2135575 : Blo 1686043 2135575 := bstep (se 1 (by rfl) ⟨1601681, by rfl⟩ : syracuseStep 2135575 = 3203363) B3203363
theorem B1898059 : Blo 1686043 1898059 := bstep (se 1 (by rfl) ⟨1423544, by rfl⟩ : syracuseStep 1898059 = 2847089) B2847089
theorem B2848331 : Blo 1686043 2848331 := bstep (se 1 (by rfl) ⟨2136248, by rfl⟩ : syracuseStep 2848331 = 4272497) B4272497
theorem B5691059 : Blo 1686043 5691059 := bstep (se 1 (by rfl) ⟨4268294, by rfl⟩ : syracuseStep 5691059 = 8536589) B8536589
theorem B1898167 : Blo 1686043 1898167 := bstep (se 1 (by rfl) ⟨1423625, by rfl⟩ : syracuseStep 1898167 = 2847251) B2847251
theorem B2848459 : Blo 1686043 2848459 := bstep (se 1 (by rfl) ⟨2136344, by rfl⟩ : syracuseStep 2848459 = 4272689) B4272689
theorem B7698179 : Blo 1686043 7698179 := bstep (se 1 (by rfl) ⟨5773634, by rfl⟩ : syracuseStep 7698179 = 11547269) B11547269
theorem B4560715 : Blo 1686043 4560715 := bstep (se 1 (by rfl) ⟨3420536, by rfl⟩ : syracuseStep 4560715 = 6841073) B6841073
theorem B2529113 : Blo 1686043 2529113 := bstep (se 2 (by rfl) ⟨948417, by rfl⟩ : syracuseStep 2529113 = 1896835) B1896835
theorem B1898347 : Blo 1686043 1898347 := bstep (se 1 (by rfl) ⟨1423760, by rfl⟩ : syracuseStep 1898347 = 2847521) B2847521
theorem B25958323 : Blo 1686043 25958323 := bstep (se 1 (by rfl) ⟨19468742, by rfl⟩ : syracuseStep 25958323 = 38937485) B38937485
theorem B5691329 : Blo 1686043 5691329 := bstep (se 2 (by rfl) ⟨2134248, by rfl⟩ : syracuseStep 5691329 = 4268497) B4268497
theorem B3200971 : Blo 1686043 3200971 := bstep (se 1 (by rfl) ⟨2400728, by rfl⟩ : syracuseStep 3200971 = 4801457) B4801457
theorem B2529227 : Blo 1686043 2529227 := bstep (se 1 (by rfl) ⟨1896920, by rfl⟩ : syracuseStep 2529227 = 3793841) B3793841
theorem B2529239 : Blo 1686043 2529239 := bstep (se 1 (by rfl) ⟨1896929, by rfl⟩ : syracuseStep 2529239 = 3793859) B3793859
theorem B1898455 : Blo 1686043 1898455 := bstep (se 1 (by rfl) ⟨1423841, by rfl⟩ : syracuseStep 1898455 = 2847683) B2847683
theorem B5478361 : Blo 1686043 5478361 := bstep (se 2 (by rfl) ⟨2054385, by rfl⟩ : syracuseStep 5478361 = 4108771) B4108771
theorem B2529305 : Blo 1686043 2529305 := bstep (se 2 (by rfl) ⟨948489, by rfl⟩ : syracuseStep 2529305 = 1896979) B1896979
theorem B2529419 : Blo 1686043 2529419 := bstep (se 1 (by rfl) ⟨1897064, by rfl⟩ : syracuseStep 2529419 = 3794129) B3794129
theorem B1898635 : Blo 1686043 1898635 := bstep (se 1 (by rfl) ⟨1423976, by rfl⟩ : syracuseStep 1898635 = 2847953) B2847953
theorem B2529431 : Blo 1686043 2529431 := bstep (se 1 (by rfl) ⟨1897073, by rfl⟩ : syracuseStep 2529431 = 3794147) B3794147
theorem B21608653 : Blo 1686043 21608653 := bstep (se 3 (by rfl) ⟨4051622, by rfl⟩ : syracuseStep 21608653 = 8103245) B8103245
theorem B2529497 : Blo 1686043 2529497 := bstep (se 2 (by rfl) ⟨948561, by rfl⟩ : syracuseStep 2529497 = 1897123) B1897123
theorem B1898743 : Blo 1686043 1898743 := bstep (se 1 (by rfl) ⟨1424057, by rfl⟩ : syracuseStep 1898743 = 2848115) B2848115
theorem B16210181 : Blo 1686043 16210181 := bstep (se 4 (by rfl) ⟨1519704, by rfl⟩ : syracuseStep 16210181 = 3039409) B3039409
theorem B4806935 : Blo 1686043 4806935 := bstep (se 1 (by rfl) ⟨3605201, by rfl⟩ : syracuseStep 4806935 = 7210403) B7210403
theorem B6404417 : Blo 1686043 6404417 := bstep (se 2 (by rfl) ⟨2401656, by rfl⟩ : syracuseStep 6404417 = 4803313) B4803313
theorem B2529611 : Blo 1686043 2529611 := bstep (se 1 (by rfl) ⟨1897208, by rfl⟩ : syracuseStep 2529611 = 3794417) B3794417
theorem B2136395 : Blo 1686043 2136395 := bstep (se 1 (by rfl) ⟨1602296, by rfl⟩ : syracuseStep 2136395 = 3204593) B3204593
theorem B2529623 : Blo 1686043 2529623 := bstep (se 1 (by rfl) ⟨1897217, by rfl⟩ : syracuseStep 2529623 = 3794435) B3794435
theorem B3201419 : Blo 1686043 3201419 := bstep (se 1 (by rfl) ⟨2401064, by rfl⟩ : syracuseStep 3201419 = 4802129) B4802129
theorem B6936977 : Blo 1686043 6936977 := bstep (se 2 (by rfl) ⟨2601366, by rfl⟩ : syracuseStep 6936977 = 5202733) B5202733
theorem B2529689 : Blo 1686043 2529689 := bstep (se 2 (by rfl) ⟨948633, by rfl⟩ : syracuseStep 2529689 = 1897267) B1897267
theorem B1898923 : Blo 1686043 1898923 := bstep (se 1 (by rfl) ⟨1424192, by rfl⟩ : syracuseStep 1898923 = 2848385) B2848385
theorem B3848651 : Blo 1686043 3848651 := bstep (se 1 (by rfl) ⟨2886488, by rfl⟩ : syracuseStep 3848651 = 5772977) B5772977
theorem B6076889 : Blo 1686043 6076889 := bstep (se 2 (by rfl) ⟨2278833, by rfl⟩ : syracuseStep 6076889 = 4557667) B4557667
theorem B5691869 : Blo 1686043 5691869 := bstep (se 3 (by rfl) ⟨1067225, by rfl⟩ : syracuseStep 5691869 = 2134451) B2134451
theorem B2529803 : Blo 1686043 2529803 := bstep (se 1 (by rfl) ⟨1897352, by rfl⟩ : syracuseStep 2529803 = 3794705) B3794705
theorem B2529815 : Blo 1686043 2529815 := bstep (se 1 (by rfl) ⟨1897361, by rfl⟩ : syracuseStep 2529815 = 3794723) B3794723
theorem B1899031 : Blo 1686043 1899031 := bstep (se 1 (by rfl) ⟨1424273, by rfl⟩ : syracuseStep 1899031 = 2848547) B2848547
theorem B1686059 : Blo 1686043 1686059 := bstep (se 1 (by rfl) ⟨1264544, by rfl⟩ : syracuseStep 1686059 = 2529089) B2529089
theorem B6076973 : Blo 1686043 6076973 := bstep (se 3 (by rfl) ⟨1139432, by rfl⟩ : syracuseStep 6076973 = 2278865) B2278865
theorem B1686071 : Blo 1686043 1686071 := bstep (se 1 (by rfl) ⟨1264553, by rfl⟩ : syracuseStep 1686071 = 2529107) B2529107
theorem B3201601 : Blo 1686043 3201601 := bstep (se 2 (by rfl) ⟨1200600, by rfl⟩ : syracuseStep 3201601 = 2401201) B2401201
theorem B1686091 : Blo 1686043 1686091 := bstep (se 1 (by rfl) ⟨1264568, by rfl⟩ : syracuseStep 1686091 = 2529137) B2529137
theorem B1686103 : Blo 1686043 1686103 := bstep (se 1 (by rfl) ⟨1264577, by rfl⟩ : syracuseStep 1686103 = 2529155) B2529155
theorem B2529881 : Blo 1686043 2529881 := bstep (se 2 (by rfl) ⟨948705, by rfl⟩ : syracuseStep 2529881 = 1897411) B1897411
theorem B1686123 : Blo 1686043 1686123 := bstep (se 1 (by rfl) ⟨1264592, by rfl⟩ : syracuseStep 1686123 = 2529185) B2529185
theorem B1686135 : Blo 1686043 1686135 := bstep (se 1 (by rfl) ⟨1264601, by rfl⟩ : syracuseStep 1686135 = 2529203) B2529203
theorem B1686155 : Blo 1686043 1686155 := bstep (se 1 (by rfl) ⟨1264616, by rfl⟩ : syracuseStep 1686155 = 2529233) B2529233
theorem B1686167 : Blo 1686043 1686167 := bstep (se 1 (by rfl) ⟨1264625, by rfl⟩ : syracuseStep 1686167 = 2529251) B2529251
theorem B1686187 : Blo 1686043 1686187 := bstep (se 1 (by rfl) ⟨1264640, by rfl⟩ : syracuseStep 1686187 = 2529281) B2529281
theorem B1686199 : Blo 1686043 1686199 := bstep (se 1 (by rfl) ⟨1264649, by rfl⟩ : syracuseStep 1686199 = 2529299) B2529299
theorem B5774017 : Blo 1686043 5774017 := bstep (se 2 (by rfl) ⟨2165256, by rfl⟩ : syracuseStep 5774017 = 4330513) B4330513
theorem B1686219 : Blo 1686043 1686219 := bstep (se 1 (by rfl) ⟨1264664, by rfl⟩ : syracuseStep 1686219 = 2529329) B2529329
theorem B2529995 : Blo 1686043 2529995 := bstep (se 1 (by rfl) ⟨1897496, by rfl⟩ : syracuseStep 2529995 = 3794993) B3794993
theorem B1686231 : Blo 1686043 1686231 := bstep (se 1 (by rfl) ⟨1264673, by rfl⟩ : syracuseStep 1686231 = 2529347) B2529347
theorem B2530007 : Blo 1686043 2530007 := bstep (se 1 (by rfl) ⟨1897505, by rfl⟩ : syracuseStep 2530007 = 3795011) B3795011
theorem B1686251 : Blo 1686043 1686251 := bstep (se 1 (by rfl) ⟨1264688, by rfl⟩ : syracuseStep 1686251 = 2529377) B2529377
theorem B1686263 : Blo 1686043 1686263 := bstep (se 1 (by rfl) ⟨1264697, by rfl⟩ : syracuseStep 1686263 = 2529395) B2529395
theorem B1686283 : Blo 1686043 1686283 := bstep (se 1 (by rfl) ⟨1264712, by rfl⟩ : syracuseStep 1686283 = 2529425) B2529425
theorem B1686295 : Blo 1686043 1686295 := bstep (se 1 (by rfl) ⟨1264721, by rfl⟩ : syracuseStep 1686295 = 2529443) B2529443
theorem B2530073 : Blo 1686043 2530073 := bstep (se 2 (by rfl) ⟨948777, by rfl⟩ : syracuseStep 2530073 = 1897555) B1897555
theorem B1686315 : Blo 1686043 1686315 := bstep (se 1 (by rfl) ⟨1264736, by rfl⟩ : syracuseStep 1686315 = 2529473) B2529473
theorem B1686327 : Blo 1686043 1686327 := bstep (se 1 (by rfl) ⟨1264745, by rfl⟩ : syracuseStep 1686327 = 2529491) B2529491
theorem B36068161 : Blo 1686043 36068161 := bstep (se 2 (by rfl) ⟨13525560, by rfl⟩ : syracuseStep 36068161 = 27051121) B27051121
theorem B1686347 : Blo 1686043 1686347 := bstep (se 1 (by rfl) ⟨1264760, by rfl⟩ : syracuseStep 1686347 = 2529521) B2529521
theorem B1686359 : Blo 1686043 1686359 := bstep (se 1 (by rfl) ⟨1264769, by rfl⟩ : syracuseStep 1686359 = 2529539) B2529539
theorem B8543069 : Blo 1686043 8543069 := bstep (se 3 (by rfl) ⟨1601825, by rfl⟩ : syracuseStep 8543069 = 3203651) B3203651
theorem B1686379 : Blo 1686043 1686379 := bstep (se 1 (by rfl) ⟨1264784, by rfl⟩ : syracuseStep 1686379 = 2529569) B2529569
theorem B1686391 : Blo 1686043 1686391 := bstep (se 1 (by rfl) ⟨1264793, by rfl⟩ : syracuseStep 1686391 = 2529587) B2529587
theorem B1686411 : Blo 1686043 1686411 := bstep (se 1 (by rfl) ⟨1264808, by rfl⟩ : syracuseStep 1686411 = 2529617) B2529617
theorem B2530187 : Blo 1686043 2530187 := bstep (se 1 (by rfl) ⟨1897640, by rfl⟩ : syracuseStep 2530187 = 3795281) B3795281
theorem B1686423 : Blo 1686043 1686423 := bstep (se 1 (by rfl) ⟨1264817, by rfl⟩ : syracuseStep 1686423 = 2529635) B2529635
theorem B3201943 : Blo 1686043 3201943 := bstep (se 1 (by rfl) ⟨2401457, by rfl⟩ : syracuseStep 3201943 = 4802915) B4802915
theorem B2530199 : Blo 1686043 2530199 := bstep (se 1 (by rfl) ⟨1897649, by rfl⟩ : syracuseStep 2530199 = 3795299) B3795299
theorem B1686443 : Blo 1686043 1686443 := bstep (se 1 (by rfl) ⟨1264832, by rfl⟩ : syracuseStep 1686443 = 2529665) B2529665
theorem B1686455 : Blo 1686043 1686455 := bstep (se 1 (by rfl) ⟨1264841, by rfl⟩ : syracuseStep 1686455 = 2529683) B2529683
theorem B6077377 : Blo 1686043 6077377 := bstep (se 2 (by rfl) ⟨2279016, by rfl⟩ : syracuseStep 6077377 = 4558033) B4558033
theorem B1686475 : Blo 1686043 1686475 := bstep (se 1 (by rfl) ⟨1264856, by rfl⟩ : syracuseStep 1686475 = 2529713) B2529713
theorem B1686487 : Blo 1686043 1686487 := bstep (se 1 (by rfl) ⟨1264865, by rfl⟩ : syracuseStep 1686487 = 2529731) B2529731
theorem B2530265 : Blo 1686043 2530265 := bstep (se 2 (by rfl) ⟨948849, by rfl⟩ : syracuseStep 2530265 = 1897699) B1897699
theorem B1686507 : Blo 1686043 1686507 := bstep (se 1 (by rfl) ⟨1264880, by rfl⟩ : syracuseStep 1686507 = 2529761) B2529761
theorem B1686519 : Blo 1686043 1686519 := bstep (se 1 (by rfl) ⟨1264889, by rfl⟩ : syracuseStep 1686519 = 2529779) B2529779
theorem B1686539 : Blo 1686043 1686539 := bstep (se 1 (by rfl) ⟨1264904, by rfl⟩ : syracuseStep 1686539 = 2529809) B2529809
theorem B1686551 : Blo 1686043 1686551 := bstep (se 1 (by rfl) ⟨1264913, by rfl⟩ : syracuseStep 1686551 = 2529827) B2529827
theorem B1686571 : Blo 1686043 1686571 := bstep (se 1 (by rfl) ⟨1264928, by rfl⟩ : syracuseStep 1686571 = 2529857) B2529857
theorem B8215597 : Blo 1686043 8215597 := bstep (se 3 (by rfl) ⟨1540424, by rfl⟩ : syracuseStep 8215597 = 3080849) B3080849
theorem B1686583 : Blo 1686043 1686583 := bstep (se 1 (by rfl) ⟨1264937, by rfl⟩ : syracuseStep 1686583 = 2529875) B2529875
theorem B1686603 : Blo 1686043 1686603 := bstep (se 1 (by rfl) ⟨1264952, by rfl⟩ : syracuseStep 1686603 = 2529905) B2529905
theorem B2530379 : Blo 1686043 2530379 := bstep (se 1 (by rfl) ⟨1897784, by rfl⟩ : syracuseStep 2530379 = 3795569) B3795569
theorem B1686615 : Blo 1686043 1686615 := bstep (se 1 (by rfl) ⟨1264961, by rfl⟩ : syracuseStep 1686615 = 2529923) B2529923
theorem B2530391 : Blo 1686043 2530391 := bstep (se 1 (by rfl) ⟨1897793, by rfl⟩ : syracuseStep 2530391 = 3795587) B3795587
theorem B1686635 : Blo 1686043 1686635 := bstep (se 1 (by rfl) ⟨1264976, by rfl⟩ : syracuseStep 1686635 = 2529953) B2529953
theorem B3202163 : Blo 1686043 3202163 := bstep (se 1 (by rfl) ⟨2401622, by rfl⟩ : syracuseStep 3202163 = 4803245) B4803245
theorem B1686647 : Blo 1686043 1686647 := bstep (se 1 (by rfl) ⟨1264985, by rfl⟩ : syracuseStep 1686647 = 2529971) B2529971
theorem B1686667 : Blo 1686043 1686667 := bstep (se 1 (by rfl) ⟨1265000, by rfl⟩ : syracuseStep 1686667 = 2530001) B2530001
theorem B1686679 : Blo 1686043 1686679 := bstep (se 1 (by rfl) ⟨1265009, by rfl⟩ : syracuseStep 1686679 = 2530019) B2530019
theorem B2530457 : Blo 1686043 2530457 := bstep (se 2 (by rfl) ⟨948921, by rfl⟩ : syracuseStep 2530457 = 1897843) B1897843
theorem B1686699 : Blo 1686043 1686699 := bstep (se 1 (by rfl) ⟨1265024, by rfl⟩ : syracuseStep 1686699 = 2530049) B2530049
theorem B72973493 : Blo 1686043 72973493 := bstep (se 5 (by rfl) ⟨3420632, by rfl⟩ : syracuseStep 72973493 = 6841265) B6841265
theorem B1686711 : Blo 1686043 1686711 := bstep (se 1 (by rfl) ⟨1265033, by rfl⟩ : syracuseStep 1686711 = 2530067) B2530067
theorem B1686731 : Blo 1686043 1686731 := bstep (se 1 (by rfl) ⟨1265048, by rfl⟩ : syracuseStep 1686731 = 2530097) B2530097
theorem B1686743 : Blo 1686043 1686743 := bstep (se 1 (by rfl) ⟨1265057, by rfl⟩ : syracuseStep 1686743 = 2530115) B2530115
theorem B1686763 : Blo 1686043 1686763 := bstep (se 1 (by rfl) ⟨1265072, by rfl⟩ : syracuseStep 1686763 = 2530145) B2530145
theorem B1686775 : Blo 1686043 1686775 := bstep (se 1 (by rfl) ⟨1265081, by rfl⟩ : syracuseStep 1686775 = 2530163) B2530163
theorem B1686795 : Blo 1686043 1686795 := bstep (se 1 (by rfl) ⟨1265096, by rfl⟩ : syracuseStep 1686795 = 2530193) B2530193
theorem B2530571 : Blo 1686043 2530571 := bstep (se 1 (by rfl) ⟨1897928, by rfl⟩ : syracuseStep 2530571 = 3795857) B3795857
theorem B7691537 : Blo 1686043 7691537 := bstep (se 2 (by rfl) ⟨2884326, by rfl⟩ : syracuseStep 7691537 = 5768653) B5768653
theorem B1686807 : Blo 1686043 1686807 := bstep (se 1 (by rfl) ⟨1265105, by rfl⟩ : syracuseStep 1686807 = 2530211) B2530211
theorem B2530583 : Blo 1686043 2530583 := bstep (se 1 (by rfl) ⟨1897937, by rfl⟩ : syracuseStep 2530583 = 3795875) B3795875
theorem B1686827 : Blo 1686043 1686827 := bstep (se 1 (by rfl) ⟨1265120, by rfl⟩ : syracuseStep 1686827 = 2530241) B2530241
theorem B1686839 : Blo 1686043 1686839 := bstep (se 1 (by rfl) ⟨1265129, by rfl⟩ : syracuseStep 1686839 = 2530259) B2530259
theorem B1686859 : Blo 1686043 1686859 := bstep (se 1 (by rfl) ⟨1265144, by rfl⟩ : syracuseStep 1686859 = 2530289) B2530289
theorem B3202391 : Blo 1686043 3202391 := bstep (se 1 (by rfl) ⟨2401793, by rfl⟩ : syracuseStep 3202391 = 4803587) B4803587
theorem B1686871 : Blo 1686043 1686871 := bstep (se 1 (by rfl) ⟨1265153, by rfl⟩ : syracuseStep 1686871 = 2530307) B2530307
theorem B2530649 : Blo 1686043 2530649 := bstep (se 2 (by rfl) ⟨948993, by rfl⟩ : syracuseStep 2530649 = 1897987) B1897987
theorem B1686891 : Blo 1686043 1686891 := bstep (se 1 (by rfl) ⟨1265168, by rfl⟩ : syracuseStep 1686891 = 2530337) B2530337
theorem B3603827 : Blo 1686043 3603827 := bstep (se 1 (by rfl) ⟨2702870, by rfl⟩ : syracuseStep 3603827 = 5405741) B5405741
theorem B1686903 : Blo 1686043 1686903 := bstep (se 1 (by rfl) ⟨1265177, by rfl⟩ : syracuseStep 1686903 = 2530355) B2530355
theorem B1686923 : Blo 1686043 1686923 := bstep (se 1 (by rfl) ⟨1265192, by rfl⟩ : syracuseStep 1686923 = 2530385) B2530385
theorem B1686935 : Blo 1686043 1686935 := bstep (se 1 (by rfl) ⟨1265201, by rfl⟩ : syracuseStep 1686935 = 2530403) B2530403
theorem B1686955 : Blo 1686043 1686955 := bstep (se 1 (by rfl) ⟨1265216, by rfl⟩ : syracuseStep 1686955 = 2530433) B2530433
theorem B1686967 : Blo 1686043 1686967 := bstep (se 1 (by rfl) ⟨1265225, by rfl⟩ : syracuseStep 1686967 = 2530451) B2530451
theorem B1686987 : Blo 1686043 1686987 := bstep (se 1 (by rfl) ⟨1265240, by rfl⟩ : syracuseStep 1686987 = 2530481) B2530481
theorem B2530763 : Blo 1686043 2530763 := bstep (se 1 (by rfl) ⟨1898072, by rfl⟩ : syracuseStep 2530763 = 3796145) B3796145
theorem B1686999 : Blo 1686043 1686999 := bstep (se 1 (by rfl) ⟨1265249, by rfl⟩ : syracuseStep 1686999 = 2530499) B2530499
theorem B2530775 : Blo 1686043 2530775 := bstep (se 1 (by rfl) ⟨1898081, by rfl⟩ : syracuseStep 2530775 = 3796163) B3796163
theorem B6495709 : Blo 1686043 6495709 := bstep (se 3 (by rfl) ⟨1217945, by rfl⟩ : syracuseStep 6495709 = 2435891) B2435891
theorem B1687019 : Blo 1686043 1687019 := bstep (se 1 (by rfl) ⟨1265264, by rfl⟩ : syracuseStep 1687019 = 2530529) B2530529
theorem B1687031 : Blo 1686043 1687031 := bstep (se 1 (by rfl) ⟨1265273, by rfl⟩ : syracuseStep 1687031 = 2530547) B2530547
theorem B1687051 : Blo 1686043 1687051 := bstep (se 1 (by rfl) ⟨1265288, by rfl⟩ : syracuseStep 1687051 = 2530577) B2530577
theorem B1687063 : Blo 1686043 1687063 := bstep (se 1 (by rfl) ⟨1265297, by rfl⟩ : syracuseStep 1687063 = 2530595) B2530595
theorem B2530841 : Blo 1686043 2530841 := bstep (se 2 (by rfl) ⟨949065, by rfl⟩ : syracuseStep 2530841 = 1898131) B1898131
theorem B1687083 : Blo 1686043 1687083 := bstep (se 1 (by rfl) ⟨1265312, by rfl⟩ : syracuseStep 1687083 = 2530625) B2530625
theorem B1687095 : Blo 1686043 1687095 := bstep (se 1 (by rfl) ⟨1265321, by rfl⟩ : syracuseStep 1687095 = 2530643) B2530643
theorem B8535617 : Blo 1686043 8535617 := bstep (se 2 (by rfl) ⟨3200856, by rfl⟩ : syracuseStep 8535617 = 6401713) B6401713
theorem B5693003 : Blo 1686043 5693003 := bstep (se 1 (by rfl) ⟨4269752, by rfl⟩ : syracuseStep 5693003 = 8539505) B8539505
theorem B1687115 : Blo 1686043 1687115 := bstep (se 1 (by rfl) ⟨1265336, by rfl⟩ : syracuseStep 1687115 = 2530673) B2530673
theorem B1687127 : Blo 1686043 1687127 := bstep (se 1 (by rfl) ⟨1265345, by rfl⟩ : syracuseStep 1687127 = 2530691) B2530691
theorem B3202649 : Blo 1686043 3202649 := bstep (se 2 (by rfl) ⟨1200993, by rfl⟩ : syracuseStep 3202649 = 2401987) B2401987
theorem B1687147 : Blo 1686043 1687147 := bstep (se 1 (by rfl) ⟨1265360, by rfl⟩ : syracuseStep 1687147 = 2530721) B2530721
theorem B1687159 : Blo 1686043 1687159 := bstep (se 1 (by rfl) ⟨1265369, by rfl⟩ : syracuseStep 1687159 = 2530739) B2530739
theorem B9870979 : Blo 1686043 9870979 := bstep (se 1 (by rfl) ⟨7403234, by rfl⟩ : syracuseStep 9870979 = 14806469) B14806469
theorem B1687179 : Blo 1686043 1687179 := bstep (se 1 (by rfl) ⟨1265384, by rfl⟩ : syracuseStep 1687179 = 2530769) B2530769
theorem B2530955 : Blo 1686043 2530955 := bstep (se 1 (by rfl) ⟨1898216, by rfl⟩ : syracuseStep 2530955 = 3796433) B3796433
theorem B1687191 : Blo 1686043 1687191 := bstep (se 1 (by rfl) ⟨1265393, by rfl⟩ : syracuseStep 1687191 = 2530787) B2530787
theorem B2530967 : Blo 1686043 2530967 := bstep (se 1 (by rfl) ⟨1898225, by rfl⟩ : syracuseStep 2530967 = 3796451) B3796451
theorem B1687211 : Blo 1686043 1687211 := bstep (se 1 (by rfl) ⟨1265408, by rfl⟩ : syracuseStep 1687211 = 2530817) B2530817
theorem B1687223 : Blo 1686043 1687223 := bstep (se 1 (by rfl) ⟨1265417, by rfl⟩ : syracuseStep 1687223 = 2530835) B2530835
theorem B5480129 : Blo 1686043 5480129 := bstep (se 2 (by rfl) ⟨2055048, by rfl⟩ : syracuseStep 5480129 = 4110097) B4110097
theorem B1687243 : Blo 1686043 1687243 := bstep (se 1 (by rfl) ⟨1265432, by rfl⟩ : syracuseStep 1687243 = 2530865) B2530865
theorem B1687255 : Blo 1686043 1687255 := bstep (se 1 (by rfl) ⟨1265441, by rfl⟩ : syracuseStep 1687255 = 2530883) B2530883
theorem B2531033 : Blo 1686043 2531033 := bstep (se 2 (by rfl) ⟨949137, by rfl⟩ : syracuseStep 2531033 = 1898275) B1898275
theorem B1687275 : Blo 1686043 1687275 := bstep (se 1 (by rfl) ⟨1265456, by rfl⟩ : syracuseStep 1687275 = 2530913) B2530913
theorem B1687287 : Blo 1686043 1687287 := bstep (se 1 (by rfl) ⟨1265465, by rfl⟩ : syracuseStep 1687287 = 2530931) B2530931
theorem B1687307 : Blo 1686043 1687307 := bstep (se 1 (by rfl) ⟨1265480, by rfl⟩ : syracuseStep 1687307 = 2530961) B2530961
theorem B6405905 : Blo 1686043 6405905 := bstep (se 2 (by rfl) ⟨2402214, by rfl⟩ : syracuseStep 6405905 = 4804429) B4804429
theorem B8109841 : Blo 1686043 8109841 := bstep (se 2 (by rfl) ⟨3041190, by rfl⟩ : syracuseStep 8109841 = 6082381) B6082381
theorem B4267799 : Blo 1686043 4267799 := bstep (se 1 (by rfl) ⟨3200849, by rfl⟩ : syracuseStep 4267799 = 6401699) B6401699
theorem B1687319 : Blo 1686043 1687319 := bstep (se 1 (by rfl) ⟨1265489, by rfl⟩ : syracuseStep 1687319 = 2530979) B2530979
theorem B2703127 : Blo 1686043 2703127 := bstep (se 1 (by rfl) ⟨2027345, by rfl⟩ : syracuseStep 2703127 = 4054691) B4054691
theorem B1687339 : Blo 1686043 1687339 := bstep (se 1 (by rfl) ⟨1265504, by rfl⟩ : syracuseStep 1687339 = 2531009) B2531009
theorem B1687351 : Blo 1686043 1687351 := bstep (se 1 (by rfl) ⟨1265513, by rfl⟩ : syracuseStep 1687351 = 2531027) B2531027
theorem B1687371 : Blo 1686043 1687371 := bstep (se 1 (by rfl) ⟨1265528, by rfl⟩ : syracuseStep 1687371 = 2531057) B2531057
theorem B2531147 : Blo 1686043 2531147 := bstep (se 1 (by rfl) ⟨1898360, by rfl⟩ : syracuseStep 2531147 = 3796721) B3796721
theorem B1687383 : Blo 1686043 1687383 := bstep (se 1 (by rfl) ⟨1265537, by rfl⟩ : syracuseStep 1687383 = 2531075) B2531075
theorem B5693273 : Blo 1686043 5693273 := bstep (se 2 (by rfl) ⟨2134977, by rfl⟩ : syracuseStep 5693273 = 4269955) B4269955
theorem B2531159 : Blo 1686043 2531159 := bstep (se 1 (by rfl) ⟨1898369, by rfl⟩ : syracuseStep 2531159 = 3796739) B3796739
theorem B1802071 : Blo 1686043 1802071 := bstep (se 1 (by rfl) ⟨1351553, by rfl⟩ : syracuseStep 1802071 = 2703107) B2703107
theorem B3604313 : Blo 1686043 3604313 := bstep (se 2 (by rfl) ⟨1351617, by rfl⟩ : syracuseStep 3604313 = 2703235) B2703235
theorem B4054873 : Blo 1686043 4054873 := bstep (se 2 (by rfl) ⟨1520577, by rfl⟩ : syracuseStep 4054873 = 3041155) B3041155
theorem B7208797 : Blo 1686043 7208797 := bstep (se 3 (by rfl) ⟨1351649, by rfl⟩ : syracuseStep 7208797 = 2703299) B2703299
theorem B1687403 : Blo 1686043 1687403 := bstep (se 1 (by rfl) ⟨1265552, by rfl⟩ : syracuseStep 1687403 = 2531105) B2531105
theorem B1687415 : Blo 1686043 1687415 := bstep (se 1 (by rfl) ⟨1265561, by rfl⟩ : syracuseStep 1687415 = 2531123) B2531123
theorem B1687435 : Blo 1686043 1687435 := bstep (se 1 (by rfl) ⟨1265576, by rfl⟩ : syracuseStep 1687435 = 2531153) B2531153
theorem B1687447 : Blo 1686043 1687447 := bstep (se 1 (by rfl) ⟨1265585, by rfl⟩ : syracuseStep 1687447 = 2531171) B2531171
theorem B2531225 : Blo 1686043 2531225 := bstep (se 2 (by rfl) ⟨949209, by rfl⟩ : syracuseStep 2531225 = 1898419) B1898419
theorem B1687467 : Blo 1686043 1687467 := bstep (se 1 (by rfl) ⟨1265600, by rfl⟩ : syracuseStep 1687467 = 2531201) B2531201
theorem B1687479 : Blo 1686043 1687479 := bstep (se 1 (by rfl) ⟨1265609, by rfl⟩ : syracuseStep 1687479 = 2531219) B2531219
theorem B1687499 : Blo 1686043 1687499 := bstep (se 1 (by rfl) ⟨1265624, by rfl⟩ : syracuseStep 1687499 = 2531249) B2531249
theorem B1687511 : Blo 1686043 1687511 := bstep (se 1 (by rfl) ⟨1265633, by rfl⟩ : syracuseStep 1687511 = 2531267) B2531267
theorem B1687531 : Blo 1686043 1687531 := bstep (se 1 (by rfl) ⟨1265648, by rfl⟩ : syracuseStep 1687531 = 2531297) B2531297
theorem B3203059 : Blo 1686043 3203059 := bstep (se 1 (by rfl) ⟨2402294, by rfl⟩ : syracuseStep 3203059 = 4804589) B4804589
theorem B1687543 : Blo 1686043 1687543 := bstep (se 1 (by rfl) ⟨1265657, by rfl⟩ : syracuseStep 1687543 = 2531315) B2531315
theorem B1687559 : Blo 1686043 1687559 := bstep (se 1 (by rfl) ⟨1265669, by rfl⟩ : syracuseStep 1687559 = 2531339) B2531339
theorem B1687567 : Blo 1686043 1687567 := bstep (se 1 (by rfl) ⟨1265675, by rfl⟩ : syracuseStep 1687567 = 2531351) B2531351
theorem B1802255 : Blo 1686043 1802255 := bstep (se 1 (by rfl) ⟨1351691, by rfl⟩ : syracuseStep 1802255 = 2703383) B2703383
theorem B2531387 : Blo 1686043 2531387 := bstep (se 1 (by rfl) ⟨1898540, by rfl⟩ : syracuseStep 2531387 = 3797081) B3797081
theorem B1687611 : Blo 1686043 1687611 := bstep (se 1 (by rfl) ⟨1265708, by rfl⟩ : syracuseStep 1687611 = 2531417) B2531417
theorem B2531447 : Blo 1686043 2531447 := bstep (se 1 (by rfl) ⟨1898585, by rfl⟩ : syracuseStep 2531447 = 3797171) B3797171
theorem B1687687 : Blo 1686043 1687687 := bstep (se 1 (by rfl) ⟨1265765, by rfl⟩ : syracuseStep 1687687 = 2531531) B2531531
theorem B2531471 : Blo 1686043 2531471 := bstep (se 1 (by rfl) ⟨1898603, by rfl⟩ : syracuseStep 2531471 = 3797207) B3797207
theorem B1687695 : Blo 1686043 1687695 := bstep (se 1 (by rfl) ⟨1265771, by rfl⟩ : syracuseStep 1687695 = 2531543) B2531543
theorem B3203219 : Blo 1686043 3203219 := bstep (se 1 (by rfl) ⟨2402414, by rfl⟩ : syracuseStep 3203219 = 4804829) B4804829
theorem B2531513 : Blo 1686043 2531513 := bstep (se 2 (by rfl) ⟨949317, by rfl⟩ : syracuseStep 2531513 = 1898635) B1898635
theorem B1687739 : Blo 1686043 1687739 := bstep (se 1 (by rfl) ⟨1265804, by rfl⟩ : syracuseStep 1687739 = 2531609) B2531609
theorem B8536265 : Blo 1686043 8536265 := bstep (se 2 (by rfl) ⟨3201099, by rfl⟩ : syracuseStep 8536265 = 6402199) B6402199
theorem B2531591 : Blo 1686043 2531591 := bstep (se 1 (by rfl) ⟨1898693, by rfl⟩ : syracuseStep 2531591 = 3797387) B3797387
theorem B1687815 : Blo 1686043 1687815 := bstep (se 1 (by rfl) ⟨1265861, by rfl⟩ : syracuseStep 1687815 = 2531723) B2531723
theorem B9871631 : Blo 1686043 9871631 := bstep (se 1 (by rfl) ⟨7403723, by rfl⟩ : syracuseStep 9871631 = 14807447) B14807447
theorem B8544527 : Blo 1686043 8544527 := bstep (se 1 (by rfl) ⟨6408395, by rfl⟩ : syracuseStep 8544527 = 12816791) B12816791
theorem B28811537 : Blo 1686043 28811537 := bstep (se 2 (by rfl) ⟨10804326, by rfl⟩ : syracuseStep 28811537 = 21608653) B21608653
theorem B1687823 : Blo 1686043 1687823 := bstep (se 1 (by rfl) ⟨1265867, by rfl⟩ : syracuseStep 1687823 = 2531735) B2531735
theorem B2531627 : Blo 1686043 2531627 := bstep (se 1 (by rfl) ⟨1898720, by rfl⟩ : syracuseStep 2531627 = 3797441) B3797441
theorem B1687867 : Blo 1686043 1687867 := bstep (se 1 (by rfl) ⟨1265900, by rfl⟩ : syracuseStep 1687867 = 2531801) B2531801
theorem B2531657 : Blo 1686043 2531657 := bstep (se 2 (by rfl) ⟨949371, by rfl⟩ : syracuseStep 2531657 = 1898743) B1898743
theorem B9609587 : Blo 1686043 9609587 := bstep (se 1 (by rfl) ⟨7207190, by rfl⟩ : syracuseStep 9609587 = 14414381) B14414381
theorem B1687943 : Blo 1686043 1687943 := bstep (se 1 (by rfl) ⟨1265957, by rfl⟩ : syracuseStep 1687943 = 2531915) B2531915
theorem B1687951 : Blo 1686043 1687951 := bstep (se 1 (by rfl) ⟨1265963, by rfl⟩ : syracuseStep 1687951 = 2531927) B2531927
theorem B9118099 : Blo 1686043 9118099 := bstep (se 1 (by rfl) ⟨6838574, by rfl⟩ : syracuseStep 9118099 = 13677149) B13677149
theorem B2531771 : Blo 1686043 2531771 := bstep (se 1 (by rfl) ⟨1898828, by rfl⟩ : syracuseStep 2531771 = 3797657) B3797657
theorem B1687995 : Blo 1686043 1687995 := bstep (se 1 (by rfl) ⟨1265996, by rfl⟩ : syracuseStep 1687995 = 2531993) B2531993
theorem B2531831 : Blo 1686043 2531831 := bstep (se 1 (by rfl) ⟨1898873, by rfl⟩ : syracuseStep 2531831 = 3797747) B3797747
theorem B2531855 : Blo 1686043 2531855 := bstep (se 1 (by rfl) ⟨1898891, by rfl⟩ : syracuseStep 2531855 = 3797783) B3797783
theorem B2531897 : Blo 1686043 2531897 := bstep (se 2 (by rfl) ⟨949461, by rfl⟩ : syracuseStep 2531897 = 1898923) B1898923
theorem B11543107 : Blo 1686043 11543107 := bstep (se 1 (by rfl) ⟨8657330, by rfl⟩ : syracuseStep 11543107 = 17314661) B17314661
theorem B4268659 : Blo 1686043 4268659 := bstep (se 1 (by rfl) ⟨3201494, by rfl⟩ : syracuseStep 4268659 = 6402989) B6402989
theorem B2531975 : Blo 1686043 2531975 := bstep (se 1 (by rfl) ⟨1898981, by rfl⟩ : syracuseStep 2531975 = 3797963) B3797963
theorem B2532011 : Blo 1686043 2532011 := bstep (se 1 (by rfl) ⟨1899008, by rfl⟩ : syracuseStep 2532011 = 3798017) B3798017
theorem B2532041 : Blo 1686043 2532041 := bstep (se 2 (by rfl) ⟨949515, by rfl⟩ : syracuseStep 2532041 = 1899031) B1899031
theorem B4268801 : Blo 1686043 4268801 := bstep (se 2 (by rfl) ⟨1600800, by rfl⟩ : syracuseStep 4268801 = 3201601) B3201601
theorem B3793679 : Blo 1686043 3793679 := bstep (se 1 (by rfl) ⟨2845259, by rfl⟩ : syracuseStep 3793679 = 5690519) B5690519
theorem B2884367 : Blo 1686043 2884367 := bstep (se 1 (by rfl) ⟨2163275, by rfl⟩ : syracuseStep 2884367 = 4326551) B4326551
theorem B3793697 : Blo 1686043 3793697 := bstep (se 2 (by rfl) ⟨1422636, by rfl⟩ : syracuseStep 3793697 = 2845273) B2845273
theorem B6407059 : Blo 1686043 6407059 := bstep (se 1 (by rfl) ⟨4805294, by rfl⟩ : syracuseStep 6407059 = 9610589) B9610589
theorem B138544181 : Blo 1686043 138544181 := bstep (se 5 (by rfl) ⟨6494258, by rfl⟩ : syracuseStep 138544181 = 12988517) B12988517
theorem B11256893 : Blo 1686043 11256893 := bstep (se 3 (by rfl) ⟨2110667, by rfl⟩ : syracuseStep 11256893 = 4221335) B4221335
theorem B3794039 : Blo 1686043 3794039 := bstep (se 1 (by rfl) ⟨2845529, by rfl⟩ : syracuseStep 3794039 = 5691059) B5691059
theorem B41608325 : Blo 1686043 41608325 := bstep (se 4 (by rfl) ⟨3900780, by rfl⟩ : syracuseStep 41608325 = 7801561) B7801561
theorem B4269257 : Blo 1686043 4269257 := bstep (se 2 (by rfl) ⟨1600971, by rfl⟩ : syracuseStep 4269257 = 3201943) B3201943
theorem B8103169 : Blo 1686043 8103169 := bstep (se 2 (by rfl) ⟨3038688, by rfl⟩ : syracuseStep 8103169 = 6077377) B6077377
theorem B3794219 : Blo 1686043 3794219 := bstep (se 1 (by rfl) ⟨2845664, by rfl⟩ : syracuseStep 3794219 = 5691329) B5691329
theorem B4621627 : Blo 1686043 4621627 := bstep (se 1 (by rfl) ⟨3466220, by rfl⟩ : syracuseStep 4621627 = 6932441) B6932441
theorem B3245447 : Blo 1686043 3245447 := bstep (se 1 (by rfl) ⟨2434085, by rfl⟩ : syracuseStep 3245447 = 4868171) B4868171
theorem B10954129 : Blo 1686043 10954129 := bstep (se 2 (by rfl) ⟨4107798, by rfl⟩ : syracuseStep 10954129 = 8215597) B8215597
theorem B2311625 : Blo 1686043 2311625 := bstep (se 2 (by rfl) ⟨866859, by rfl⟩ : syracuseStep 2311625 = 1733719) B1733719
theorem B10806787 : Blo 1686043 10806787 := bstep (se 1 (by rfl) ⟨8105090, by rfl⟩ : syracuseStep 10806787 = 16210181) B16210181
theorem B3204623 : Blo 1686043 3204623 := bstep (se 1 (by rfl) ⟨2403467, by rfl⟩ : syracuseStep 3204623 = 4806935) B4806935
theorem B4269611 : Blo 1686043 4269611 := bstep (se 1 (by rfl) ⟨3202208, by rfl⟩ : syracuseStep 4269611 = 6404417) B6404417
theorem B2565767 : Blo 1686043 2565767 := bstep (se 1 (by rfl) ⟨1924325, by rfl⟩ : syracuseStep 2565767 = 3848651) B3848651
theorem B3794579 : Blo 1686043 3794579 := bstep (se 1 (by rfl) ⟨2845934, by rfl⟩ : syracuseStep 3794579 = 5691869) B5691869
theorem B3794633 : Blo 1686043 3794633 := bstep (se 2 (by rfl) ⟨1422987, by rfl⟩ : syracuseStep 3794633 = 2845975) B2845975
theorem B24323813 : Blo 1686043 24323813 := bstep (se 4 (by rfl) ⟨2280357, by rfl⟩ : syracuseStep 24323813 = 4560715) B4560715
theorem B9611045 : Blo 1686043 9611045 := bstep (se 4 (by rfl) ⟨901035, by rfl⟩ : syracuseStep 9611045 = 1802071) B1802071
theorem B5695379 : Blo 1686043 5695379 := bstep (se 1 (by rfl) ⟨4271534, by rfl⟩ : syracuseStep 5695379 = 8543069) B8543069
theorem B27346841 : Blo 1686043 27346841 := bstep (se 2 (by rfl) ⟨10255065, by rfl⟩ : syracuseStep 27346841 = 20510131) B20510131
theorem B8660945 : Blo 1686043 8660945 := bstep (se 2 (by rfl) ⟨3247854, by rfl⟩ : syracuseStep 8660945 = 6495709) B6495709
theorem B10258397 : Blo 1686043 10258397 := bstep (se 3 (by rfl) ⟨1923449, by rfl⟩ : syracuseStep 10258397 = 3846899) B3846899
theorem B4802561 : Blo 1686043 4802561 := bstep (se 2 (by rfl) ⟨1800960, by rfl⟩ : syracuseStep 4802561 = 3601921) B3601921
theorem B4327435 : Blo 1686043 4327435 := bstep (se 1 (by rfl) ⟨3245576, by rfl⟩ : syracuseStep 4327435 = 6491153) B6491153
theorem B6080579 : Blo 1686043 6080579 := bstep (se 1 (by rfl) ⟨4560434, by rfl⟩ : syracuseStep 6080579 = 9120869) B9120869
theorem B2402551 : Blo 1686043 2402551 := bstep (se 1 (by rfl) ⟨1801913, by rfl⟩ : syracuseStep 2402551 = 3603827) B3603827
theorem B3795335 : Blo 1686043 3795335 := bstep (se 1 (by rfl) ⟨2846501, by rfl⟩ : syracuseStep 3795335 = 5693003) B5693003
theorem B9603481 : Blo 1686043 9603481 := bstep (se 2 (by rfl) ⟨3601305, by rfl⟩ : syracuseStep 9603481 = 7202611) B7202611
theorem B12806585 : Blo 1686043 12806585 := bstep (se 2 (by rfl) ⟨4802469, by rfl⟩ : syracuseStep 12806585 = 9604939) B9604939
theorem B9611729 : Blo 1686043 9611729 := bstep (se 2 (by rfl) ⟨3604398, by rfl⟩ : syracuseStep 9611729 = 7208797) B7208797
theorem B4270603 : Blo 1686043 4270603 := bstep (se 1 (by rfl) ⟨3202952, by rfl⟩ : syracuseStep 4270603 = 6405905) B6405905
theorem B2845199 : Blo 1686043 2845199 := bstep (se 1 (by rfl) ⟨2133899, by rfl⟩ : syracuseStep 2845199 = 4267799) B4267799
theorem B4803131 : Blo 1686043 4803131 := bstep (se 1 (by rfl) ⟨3602348, by rfl⟩ : syracuseStep 4803131 = 7204697) B7204697
theorem B3795515 : Blo 1686043 3795515 := bstep (se 1 (by rfl) ⟨2846636, by rfl⟩ : syracuseStep 3795515 = 5693273) B5693273
theorem B2402875 : Blo 1686043 2402875 := bstep (se 1 (by rfl) ⟨1802156, by rfl⟩ : syracuseStep 2402875 = 3604313) B3604313
theorem B6408791 : Blo 1686043 6408791 := bstep (se 1 (by rfl) ⟨4806593, by rfl⟩ : syracuseStep 6408791 = 9613187) B9613187
theorem B2280055 : Blo 1686043 2280055 := bstep (se 1 (by rfl) ⟨1710041, by rfl⟩ : syracuseStep 2280055 = 3420083) B3420083
theorem B4270745 : Blo 1686043 4270745 := bstep (se 2 (by rfl) ⟨1601529, by rfl⟩ : syracuseStep 4270745 = 3203059) B3203059
theorem B3795641 : Blo 1686043 3795641 := bstep (se 2 (by rfl) ⟨1423365, by rfl⟩ : syracuseStep 3795641 = 2846731) B2846731
theorem B9612047 : Blo 1686043 9612047 := bstep (se 1 (by rfl) ⟨7209035, by rfl⟩ : syracuseStep 9612047 = 14418071) B14418071
theorem B4803371 : Blo 1686043 4803371 := bstep (se 1 (by rfl) ⟨3602528, by rfl⟩ : syracuseStep 4803371 = 7205057) B7205057
theorem B4270907 : Blo 1686043 4270907 := bstep (se 1 (by rfl) ⟨3203180, by rfl⟩ : syracuseStep 4270907 = 6406361) B6406361
theorem B3795983 : Blo 1686043 3795983 := bstep (se 1 (by rfl) ⟨2846987, by rfl⟩ : syracuseStep 3795983 = 5693975) B5693975
theorem B3796001 : Blo 1686043 3796001 := bstep (se 2 (by rfl) ⟨1423500, by rfl⟩ : syracuseStep 3796001 = 2847001) B2847001
theorem B2845739 : Blo 1686043 2845739 := bstep (se 1 (by rfl) ⟨2134304, by rfl⟩ : syracuseStep 2845739 = 4268609) B4268609
theorem B2403371 : Blo 1686043 2403371 := bstep (se 1 (by rfl) ⟨1802528, by rfl⟩ : syracuseStep 2403371 = 3605057) B3605057
theorem B6409277 : Blo 1686043 6409277 := bstep (se 3 (by rfl) ⟨1201739, by rfl⟩ : syracuseStep 6409277 = 2403479) B2403479
theorem B2026615 : Blo 1686043 2026615 := bstep (se 1 (by rfl) ⟨1519961, by rfl⟩ : syracuseStep 2026615 = 3039923) B3039923
theorem B4271251 : Blo 1686043 4271251 := bstep (se 1 (by rfl) ⟨3203438, by rfl⟩ : syracuseStep 4271251 = 6406877) B6406877
theorem B9366785 : Blo 1686043 9366785 := bstep (se 2 (by rfl) ⟨3512544, by rfl⟩ : syracuseStep 9366785 = 7025089) B7025089
theorem B5696783 : Blo 1686043 5696783 := bstep (se 1 (by rfl) ⟨4272587, by rfl⟩ : syracuseStep 5696783 = 8545175) B8545175
theorem B4271393 : Blo 1686043 4271393 := bstep (se 2 (by rfl) ⟨1601772, by rfl⟩ : syracuseStep 4271393 = 3203545) B3203545
theorem B3796343 : Blo 1686043 3796343 := bstep (se 1 (by rfl) ⟨2847257, by rfl⟩ : syracuseStep 3796343 = 5694515) B5694515
theorem B9121169 : Blo 1686043 9121169 := bstep (se 2 (by rfl) ⟨3420438, by rfl⟩ : syracuseStep 9121169 = 6840877) B6840877
theorem B2846137 : Blo 1686043 2846137 := bstep (se 2 (by rfl) ⟨1067301, by rfl⟩ : syracuseStep 2846137 = 2134603) B2134603
theorem B5697053 : Blo 1686043 5697053 := bstep (se 3 (by rfl) ⟨1068197, by rfl⟩ : syracuseStep 5697053 = 2136395) B2136395
theorem B5197355 : Blo 1686043 5197355 := bstep (se 1 (by rfl) ⟨3898016, by rfl⟩ : syracuseStep 5197355 = 7796033) B7796033
theorem B3796523 : Blo 1686043 3796523 := bstep (se 1 (by rfl) ⟨2847392, by rfl⟩ : syracuseStep 3796523 = 5694785) B5694785
theorem B5402369 : Blo 1686043 5402369 := bstep (se 2 (by rfl) ⟨2025888, by rfl⟩ : syracuseStep 5402369 = 4051777) B4051777
theorem B48090881 : Blo 1686043 48090881 := bstep (se 2 (by rfl) ⟨18034080, by rfl⟩ : syracuseStep 48090881 = 36068161) B36068161
theorem B5132119 : Blo 1686043 5132119 := bstep (se 1 (by rfl) ⟨3849089, by rfl⟩ : syracuseStep 5132119 = 7698179) B7698179
theorem B3796883 : Blo 1686043 3796883 := bstep (se 1 (by rfl) ⟨2847662, by rfl⟩ : syracuseStep 3796883 = 5695325) B5695325
theorem B3796937 : Blo 1686043 3796937 := bstep (se 2 (by rfl) ⟨1423851, by rfl⟩ : syracuseStep 3796937 = 2847703) B2847703
theorem B4108403 : Blo 1686043 4108403 := bstep (se 1 (by rfl) ⟨3081302, by rfl⟩ : syracuseStep 4108403 = 6162605) B6162605
theorem B2846839 : Blo 1686043 2846839 := bstep (se 1 (by rfl) ⟨2135129, by rfl⟩ : syracuseStep 2846839 = 4270259) B4270259
theorem B9613505 : Blo 1686043 9613505 := bstep (se 2 (by rfl) ⟨3605064, by rfl⟩ : syracuseStep 9613505 = 7210129) B7210129
theorem B4272385 : Blo 1686043 4272385 := bstep (se 2 (by rfl) ⟨1602144, by rfl⟩ : syracuseStep 4272385 = 3204289) B3204289
theorem B2134279 : Blo 1686043 2134279 := bstep (se 1 (by rfl) ⟨1600709, by rfl⟩ : syracuseStep 2134279 = 3201419) B3201419
theorem B4624651 : Blo 1686043 4624651 := bstep (se 1 (by rfl) ⟨3468488, by rfl⟩ : syracuseStep 4624651 = 6936977) B6936977
theorem B4051259 : Blo 1686043 4051259 := bstep (se 1 (by rfl) ⟨3038444, by rfl⟩ : syracuseStep 4051259 = 6076889) B6076889
theorem B2847035 : Blo 1686043 2847035 := bstep (se 1 (by rfl) ⟨2135276, by rfl⟩ : syracuseStep 2847035 = 4270553) B4270553
theorem B9605465 : Blo 1686043 9605465 := bstep (se 2 (by rfl) ⟨3602049, by rfl⟩ : syracuseStep 9605465 = 7204099) B7204099
theorem B4051315 : Blo 1686043 4051315 := bstep (se 1 (by rfl) ⟨3038486, by rfl⟩ : syracuseStep 4051315 = 6076973) B6076973
theorem B3797639 : Blo 1686043 3797639 := bstep (se 1 (by rfl) ⟨2848229, by rfl⟩ : syracuseStep 3797639 = 5696459) B5696459
theorem B20517569 : Blo 1686043 20517569 := bstep (se 2 (by rfl) ⟨7694088, by rfl⟩ : syracuseStep 20517569 = 15388177) B15388177
theorem B2847433 : Blo 1686043 2847433 := bstep (se 2 (by rfl) ⟨1067787, by rfl⟩ : syracuseStep 2847433 = 2135575) B2135575
theorem B2134775 : Blo 1686043 2134775 := bstep (se 1 (by rfl) ⟨1601081, by rfl⟩ : syracuseStep 2134775 = 3202163) B3202163
theorem B1897231 : Blo 1686043 1897231 := bstep (se 1 (by rfl) ⟨1422923, by rfl⟩ : syracuseStep 1897231 = 2845847) B2845847
theorem B48648995 : Blo 1686043 48648995 := bstep (se 1 (by rfl) ⟨36486746, by rfl⟩ : syracuseStep 48648995 = 72973493) B72973493
theorem B3797819 : Blo 1686043 3797819 := bstep (se 1 (by rfl) ⟨2848364, by rfl⟩ : syracuseStep 3797819 = 5696729) B5696729
theorem B13161305 : Blo 1686043 13161305 := bstep (se 2 (by rfl) ⟨4935489, by rfl⟩ : syracuseStep 13161305 = 9870979) B9870979
theorem B2134927 : Blo 1686043 2134927 := bstep (se 1 (by rfl) ⟨1601195, by rfl⟩ : syracuseStep 2134927 = 3202391) B3202391
theorem B3797945 : Blo 1686043 3797945 := bstep (se 2 (by rfl) ⟨1424229, by rfl⟩ : syracuseStep 3797945 = 2848459) B2848459
theorem B5690411 : Blo 1686043 5690411 := bstep (se 1 (by rfl) ⟨4267808, by rfl⟩ : syracuseStep 5690411 = 8535617) B8535617
theorem B2135099 : Blo 1686043 2135099 := bstep (se 1 (by rfl) ⟨1601324, by rfl⟩ : syracuseStep 2135099 = 3202649) B3202649
theorem B32863319 : Blo 1686043 32863319 := bstep (se 1 (by rfl) ⟨24647489, by rfl⟩ : syracuseStep 32863319 = 49294979) B49294979
theorem B29217925 : Blo 1686043 29217925 := bstep (se 4 (by rfl) ⟨2739180, by rfl⟩ : syracuseStep 29217925 = 5478361) B5478361
theorem B1897735 : Blo 1686043 1897735 := bstep (se 1 (by rfl) ⟨1423301, by rfl⟩ : syracuseStep 1897735 = 2846603) B2846603
theorem B18232609 : Blo 1686043 18232609 := bstep (se 2 (by rfl) ⟨6837228, by rfl⟩ : syracuseStep 18232609 = 13674457) B13674457
theorem B2848135 : Blo 1686043 2848135 := bstep (se 1 (by rfl) ⟨2136101, by rfl⟩ : syracuseStep 2848135 = 4272203) B4272203
theorem B6403475 : Blo 1686043 6403475 := bstep (se 1 (by rfl) ⟨4802606, by rfl⟩ : syracuseStep 6403475 = 9605213) B9605213
theorem B1897915 : Blo 1686043 1897915 := bstep (se 1 (by rfl) ⟨1423436, by rfl⟩ : syracuseStep 1897915 = 2846873) B2846873
theorem B27350531 : Blo 1686043 27350531 := bstep (se 1 (by rfl) ⟨20512898, by rfl⟩ : syracuseStep 27350531 = 41025797) B41025797
theorem B2529083 : Blo 1686043 2529083 := bstep (se 1 (by rfl) ⟨1896812, by rfl⟩ : syracuseStep 2529083 = 3793625) B3793625
theorem B2529143 : Blo 1686043 2529143 := bstep (se 1 (by rfl) ⟨1896857, by rfl⟩ : syracuseStep 2529143 = 3793715) B3793715
theorem B3200887 : Blo 1686043 3200887 := bstep (se 1 (by rfl) ⟨2400665, by rfl⟩ : syracuseStep 3200887 = 4801331) B4801331
theorem B6838151 : Blo 1686043 6838151 := bstep (se 1 (by rfl) ⟨5128613, by rfl⟩ : syracuseStep 6838151 = 10257227) B10257227
theorem B2529167 : Blo 1686043 2529167 := bstep (se 1 (by rfl) ⟨1896875, by rfl⟩ : syracuseStep 2529167 = 3793751) B3793751
theorem B1898383 : Blo 1686043 1898383 := bstep (se 1 (by rfl) ⟨1423787, by rfl⟩ : syracuseStep 1898383 = 2847575) B2847575
theorem B8542097 : Blo 1686043 8542097 := bstep (se 2 (by rfl) ⟨3203286, by rfl⟩ : syracuseStep 8542097 = 6406573) B6406573
theorem B3602323 : Blo 1686043 3602323 := bstep (se 1 (by rfl) ⟨2701742, by rfl⟩ : syracuseStep 3602323 = 5403485) B5403485
theorem B2529209 : Blo 1686043 2529209 := bstep (se 2 (by rfl) ⟨948453, by rfl⟩ : syracuseStep 2529209 = 1896907) B1896907
theorem B4052921 : Blo 1686043 4052921 := bstep (se 2 (by rfl) ⟨1519845, by rfl⟩ : syracuseStep 4052921 = 3039691) B3039691
theorem B2529287 : Blo 1686043 2529287 := bstep (se 1 (by rfl) ⟨1896965, by rfl⟩ : syracuseStep 2529287 = 3793931) B3793931
theorem B2136071 : Blo 1686043 2136071 := bstep (se 1 (by rfl) ⟨1602053, by rfl⟩ : syracuseStep 2136071 = 3204107) B3204107
theorem B6838283 : Blo 1686043 6838283 := bstep (se 1 (by rfl) ⟨5128712, by rfl⟩ : syracuseStep 6838283 = 10257425) B10257425
theorem B4053007 : Blo 1686043 4053007 := bstep (se 1 (by rfl) ⟨3039755, by rfl⟩ : syracuseStep 4053007 = 6079511) B6079511
theorem B2529323 : Blo 1686043 2529323 := bstep (se 1 (by rfl) ⟨1896992, by rfl⟩ : syracuseStep 2529323 = 3793985) B3793985
theorem B5404715 : Blo 1686043 5404715 := bstep (se 1 (by rfl) ⟨4053536, by rfl⟩ : syracuseStep 5404715 = 8107073) B8107073
theorem B20510765 : Blo 1686043 20510765 := bstep (se 3 (by rfl) ⟨3845768, by rfl⟩ : syracuseStep 20510765 = 7691537) B7691537
theorem B2529353 : Blo 1686043 2529353 := bstep (se 2 (by rfl) ⟨948507, by rfl⟩ : syracuseStep 2529353 = 1897015) B1897015
theorem B2529467 : Blo 1686043 2529467 := bstep (se 1 (by rfl) ⟨1897100, by rfl⟩ : syracuseStep 2529467 = 3794201) B3794201
theorem B2529527 : Blo 1686043 2529527 := bstep (se 1 (by rfl) ⟨1897145, by rfl⟩ : syracuseStep 2529527 = 3794291) B3794291
theorem B7698689 : Blo 1686043 7698689 := bstep (se 2 (by rfl) ⟨2887008, by rfl⟩ : syracuseStep 7698689 = 5774017) B5774017
theorem B2529551 : Blo 1686043 2529551 := bstep (se 1 (by rfl) ⟨1897163, by rfl⟩ : syracuseStep 2529551 = 3794327) B3794327
theorem B2529593 : Blo 1686043 2529593 := bstep (se 2 (by rfl) ⟨948597, by rfl⟩ : syracuseStep 2529593 = 1897195) B1897195
theorem B5691707 : Blo 1686043 5691707 := bstep (se 1 (by rfl) ⟨4268780, by rfl⟩ : syracuseStep 5691707 = 8537561) B8537561
theorem B21920093 : Blo 1686043 21920093 := bstep (se 3 (by rfl) ⟨4110017, by rfl⟩ : syracuseStep 21920093 = 8220035) B8220035
theorem B2529671 : Blo 1686043 2529671 := bstep (se 1 (by rfl) ⟨1897253, by rfl⟩ : syracuseStep 2529671 = 3794507) B3794507
theorem B1898887 : Blo 1686043 1898887 := bstep (se 1 (by rfl) ⟨1424165, by rfl⟩ : syracuseStep 1898887 = 2848331) B2848331
theorem B23075219 : Blo 1686043 23075219 := bstep (se 1 (by rfl) ⟨17306414, by rfl⟩ : syracuseStep 23075219 = 34612829) B34612829
theorem B2529707 : Blo 1686043 2529707 := bstep (se 1 (by rfl) ⟨1897280, by rfl⟩ : syracuseStep 2529707 = 3794561) B3794561
theorem B2529737 : Blo 1686043 2529737 := bstep (se 2 (by rfl) ⟨948651, by rfl⟩ : syracuseStep 2529737 = 1897303) B1897303
theorem B17316301 : Blo 1686043 17316301 := bstep (se 3 (by rfl) ⟨3246806, by rfl⟩ : syracuseStep 17316301 = 6493613) B6493613
theorem B1686075 : Blo 1686043 1686075 := bstep (se 1 (by rfl) ⟨1264556, by rfl⟩ : syracuseStep 1686075 = 2529113) B2529113
theorem B2529851 : Blo 1686043 2529851 := bstep (se 1 (by rfl) ⟨1897388, by rfl⟩ : syracuseStep 2529851 = 3794777) B3794777
theorem B2529911 : Blo 1686043 2529911 := bstep (se 1 (by rfl) ⟨1897433, by rfl⟩ : syracuseStep 2529911 = 3794867) B3794867
theorem B1686151 : Blo 1686043 1686151 := bstep (se 1 (by rfl) ⟨1264613, by rfl⟩ : syracuseStep 1686151 = 2529227) B2529227
theorem B1686159 : Blo 1686043 1686159 := bstep (se 1 (by rfl) ⟨1264619, by rfl⟩ : syracuseStep 1686159 = 2529239) B2529239
theorem B2529935 : Blo 1686043 2529935 := bstep (se 1 (by rfl) ⟨1897451, by rfl⟩ : syracuseStep 2529935 = 3794903) B3794903
theorem B2529977 : Blo 1686043 2529977 := bstep (se 2 (by rfl) ⟨948741, by rfl⟩ : syracuseStep 2529977 = 1897483) B1897483
theorem B1686203 : Blo 1686043 1686203 := bstep (se 1 (by rfl) ⟨1264652, by rfl⟩ : syracuseStep 1686203 = 2529305) B2529305
theorem B9124609 : Blo 1686043 9124609 := bstep (se 2 (by rfl) ⟨3421728, by rfl⟩ : syracuseStep 9124609 = 6843457) B6843457
theorem B1686279 : Blo 1686043 1686279 := bstep (se 1 (by rfl) ⟨1264709, by rfl⟩ : syracuseStep 1686279 = 2529419) B2529419
theorem B2530055 : Blo 1686043 2530055 := bstep (se 1 (by rfl) ⟨1897541, by rfl⟩ : syracuseStep 2530055 = 3795083) B3795083
theorem B1686287 : Blo 1686043 1686287 := bstep (se 1 (by rfl) ⟨1264715, by rfl⟩ : syracuseStep 1686287 = 2529431) B2529431
theorem B513137429 : Blo 1686043 513137429 := bstep (se 6 (by rfl) ⟨12026658, by rfl⟩ : syracuseStep 513137429 = 24053317) B24053317
theorem B5692193 : Blo 1686043 5692193 := bstep (se 2 (by rfl) ⟨2134572, by rfl⟩ : syracuseStep 5692193 = 4269145) B4269145
theorem B2530091 : Blo 1686043 2530091 := bstep (se 1 (by rfl) ⟨1897568, by rfl⟩ : syracuseStep 2530091 = 3795137) B3795137
theorem B1686331 : Blo 1686043 1686331 := bstep (se 1 (by rfl) ⟨1264748, by rfl⟩ : syracuseStep 1686331 = 2529497) B2529497
theorem B2530121 : Blo 1686043 2530121 := bstep (se 2 (by rfl) ⟨948795, by rfl⟩ : syracuseStep 2530121 = 1897591) B1897591
theorem B1686407 : Blo 1686043 1686407 := bstep (se 1 (by rfl) ⟨1264805, by rfl⟩ : syracuseStep 1686407 = 2529611) B2529611
theorem B1686415 : Blo 1686043 1686415 := bstep (se 1 (by rfl) ⟨1264811, by rfl⟩ : syracuseStep 1686415 = 2529623) B2529623
theorem B1686459 : Blo 1686043 1686459 := bstep (se 1 (by rfl) ⟨1264844, by rfl⟩ : syracuseStep 1686459 = 2529689) B2529689
theorem B2530235 : Blo 1686043 2530235 := bstep (se 1 (by rfl) ⟨1897676, by rfl⟩ : syracuseStep 2530235 = 3795353) B3795353
theorem B2530295 : Blo 1686043 2530295 := bstep (se 1 (by rfl) ⟨1897721, by rfl⟩ : syracuseStep 2530295 = 3795443) B3795443
theorem B1686535 : Blo 1686043 1686535 := bstep (se 1 (by rfl) ⟨1264901, by rfl⟩ : syracuseStep 1686535 = 2529803) B2529803
theorem B21617675 : Blo 1686043 21617675 := bstep (se 1 (by rfl) ⟨16213256, by rfl⟩ : syracuseStep 21617675 = 32426513) B32426513
theorem B1686543 : Blo 1686043 1686543 := bstep (se 1 (by rfl) ⟨1264907, by rfl⟩ : syracuseStep 1686543 = 2529815) B2529815
theorem B2530319 : Blo 1686043 2530319 := bstep (se 1 (by rfl) ⟨1897739, by rfl⟩ : syracuseStep 2530319 = 3795479) B3795479
theorem B6495275 : Blo 1686043 6495275 := bstep (se 1 (by rfl) ⟨4871456, by rfl⟩ : syracuseStep 6495275 = 9742913) B9742913
theorem B2530361 : Blo 1686043 2530361 := bstep (se 2 (by rfl) ⟨948885, by rfl⟩ : syracuseStep 2530361 = 1897771) B1897771
theorem B1686587 : Blo 1686043 1686587 := bstep (se 1 (by rfl) ⟨1264940, by rfl⟩ : syracuseStep 1686587 = 2529881) B2529881
theorem B1686663 : Blo 1686043 1686663 := bstep (se 1 (by rfl) ⟨1264997, by rfl⟩ : syracuseStep 1686663 = 2529995) B2529995
theorem B2530439 : Blo 1686043 2530439 := bstep (se 1 (by rfl) ⟨1897829, by rfl⟩ : syracuseStep 2530439 = 3795659) B3795659
theorem B1686671 : Blo 1686043 1686671 := bstep (se 1 (by rfl) ⟨1265003, by rfl⟩ : syracuseStep 1686671 = 2530007) B2530007
theorem B2530475 : Blo 1686043 2530475 := bstep (se 1 (by rfl) ⟨1897856, by rfl⟩ : syracuseStep 2530475 = 3795713) B3795713
theorem B14613677 : Blo 1686043 14613677 := bstep (se 3 (by rfl) ⟨2740064, by rfl⟩ : syracuseStep 14613677 = 5480129) B5480129
theorem B1686715 : Blo 1686043 1686715 := bstep (se 1 (by rfl) ⟨1265036, by rfl⟩ : syracuseStep 1686715 = 2530073) B2530073
theorem B2530505 : Blo 1686043 2530505 := bstep (se 2 (by rfl) ⟨948939, by rfl⟩ : syracuseStep 2530505 = 1897879) B1897879
theorem B1686791 : Blo 1686043 1686791 := bstep (se 1 (by rfl) ⟨1265093, by rfl⟩ : syracuseStep 1686791 = 2530187) B2530187
theorem B1686799 : Blo 1686043 1686799 := bstep (se 1 (by rfl) ⟨1265099, by rfl⟩ : syracuseStep 1686799 = 2530199) B2530199
theorem B4562219 : Blo 1686043 4562219 := bstep (se 1 (by rfl) ⟨3421664, by rfl⟩ : syracuseStep 4562219 = 6843329) B6843329
theorem B1686843 : Blo 1686043 1686843 := bstep (se 1 (by rfl) ⟨1265132, by rfl⟩ : syracuseStep 1686843 = 2530265) B2530265
theorem B2530619 : Blo 1686043 2530619 := bstep (se 1 (by rfl) ⟨1897964, by rfl⟩ : syracuseStep 2530619 = 3795929) B3795929
theorem B5692787 : Blo 1686043 5692787 := bstep (se 1 (by rfl) ⟨4269590, by rfl⟩ : syracuseStep 5692787 = 8539181) B8539181
theorem B2530679 : Blo 1686043 2530679 := bstep (se 1 (by rfl) ⟨1898009, by rfl⟩ : syracuseStep 2530679 = 3796019) B3796019
theorem B4054391 : Blo 1686043 4054391 := bstep (se 1 (by rfl) ⟨3040793, by rfl⟩ : syracuseStep 4054391 = 6081587) B6081587
theorem B1686919 : Blo 1686043 1686919 := bstep (se 1 (by rfl) ⟨1265189, by rfl⟩ : syracuseStep 1686919 = 2530379) B2530379
theorem B1686927 : Blo 1686043 1686927 := bstep (se 1 (by rfl) ⟨1265195, by rfl⟩ : syracuseStep 1686927 = 2530391) B2530391
theorem B2530703 : Blo 1686043 2530703 := bstep (se 1 (by rfl) ⟨1898027, by rfl⟩ : syracuseStep 2530703 = 3796055) B3796055
theorem B2530745 : Blo 1686043 2530745 := bstep (se 2 (by rfl) ⟨949029, by rfl⟩ : syracuseStep 2530745 = 1898059) B1898059
theorem B1686971 : Blo 1686043 1686971 := bstep (se 1 (by rfl) ⟨1265228, by rfl⟩ : syracuseStep 1686971 = 2530457) B2530457
theorem B8109533 : Blo 1686043 8109533 := bstep (se 3 (by rfl) ⟨1520537, by rfl⟩ : syracuseStep 8109533 = 3041075) B3041075
theorem B1687047 : Blo 1686043 1687047 := bstep (se 1 (by rfl) ⟨1265285, by rfl⟩ : syracuseStep 1687047 = 2530571) B2530571
theorem B2530823 : Blo 1686043 2530823 := bstep (se 1 (by rfl) ⟨1898117, by rfl⟩ : syracuseStep 2530823 = 3796235) B3796235
theorem B1687055 : Blo 1686043 1687055 := bstep (se 1 (by rfl) ⟨1265291, by rfl⟩ : syracuseStep 1687055 = 2530583) B2530583
theorem B2530859 : Blo 1686043 2530859 := bstep (se 1 (by rfl) ⟨1898144, by rfl⟩ : syracuseStep 2530859 = 3796289) B3796289
theorem B1687099 : Blo 1686043 1687099 := bstep (se 1 (by rfl) ⟨1265324, by rfl⟩ : syracuseStep 1687099 = 2530649) B2530649
theorem B8109629 : Blo 1686043 8109629 := bstep (se 3 (by rfl) ⟨1520555, by rfl⟩ : syracuseStep 8109629 = 3041111) B3041111
theorem B19488323 : Blo 1686043 19488323 := bstep (se 1 (by rfl) ⟨14616242, by rfl⟩ : syracuseStep 19488323 = 29232485) B29232485
theorem B2530889 : Blo 1686043 2530889 := bstep (se 2 (by rfl) ⟨949083, by rfl⟩ : syracuseStep 2530889 = 1898167) B1898167
theorem B3202679 : Blo 1686043 3202679 := bstep (se 1 (by rfl) ⟨2402009, by rfl⟩ : syracuseStep 3202679 = 4804019) B4804019
theorem B1687175 : Blo 1686043 1687175 := bstep (se 1 (by rfl) ⟨1265381, by rfl⟩ : syracuseStep 1687175 = 2530763) B2530763
theorem B1687183 : Blo 1686043 1687183 := bstep (se 1 (by rfl) ⟨1265387, by rfl⟩ : syracuseStep 1687183 = 2530775) B2530775
theorem B3038905 : Blo 1686043 3038905 := bstep (se 2 (by rfl) ⟨1139589, by rfl⟩ : syracuseStep 3038905 = 2279179) B2279179
theorem B1687227 : Blo 1686043 1687227 := bstep (se 1 (by rfl) ⟨1265420, by rfl⟩ : syracuseStep 1687227 = 2530841) B2530841
theorem B2531003 : Blo 1686043 2531003 := bstep (se 1 (by rfl) ⟨1898252, by rfl⟩ : syracuseStep 2531003 = 3796505) B3796505
theorem B10813121 : Blo 1686043 10813121 := bstep (se 2 (by rfl) ⟨4054920, by rfl⟩ : syracuseStep 10813121 = 8109841) B8109841
theorem B3604169 : Blo 1686043 3604169 := bstep (se 2 (by rfl) ⟨1351563, by rfl⟩ : syracuseStep 3604169 = 2703127) B2703127
theorem B2531063 : Blo 1686043 2531063 := bstep (se 1 (by rfl) ⟨1898297, by rfl⟩ : syracuseStep 2531063 = 3796595) B3796595
theorem B1687303 : Blo 1686043 1687303 := bstep (se 1 (by rfl) ⟨1265477, by rfl⟩ : syracuseStep 1687303 = 2530955) B2530955
theorem B3202831 : Blo 1686043 3202831 := bstep (se 1 (by rfl) ⟨2402123, by rfl⟩ : syracuseStep 3202831 = 4804247) B4804247
theorem B1687311 : Blo 1686043 1687311 := bstep (se 1 (by rfl) ⟨1265483, by rfl⟩ : syracuseStep 1687311 = 2530967) B2530967
theorem B2531087 : Blo 1686043 2531087 := bstep (se 1 (by rfl) ⟨1898315, by rfl⟩ : syracuseStep 2531087 = 3796631) B3796631
theorem B5406497 : Blo 1686043 5406497 := bstep (se 2 (by rfl) ⟨2027436, by rfl⟩ : syracuseStep 5406497 = 4054873) B4054873
theorem B2531129 : Blo 1686043 2531129 := bstep (se 2 (by rfl) ⟨949173, by rfl⟩ : syracuseStep 2531129 = 1898347) B1898347
theorem B1687355 : Blo 1686043 1687355 := bstep (se 1 (by rfl) ⟨1265516, by rfl⟩ : syracuseStep 1687355 = 2531033) B2531033
theorem B4562747 : Blo 1686043 4562747 := bstep (se 1 (by rfl) ⟨3422060, by rfl⟩ : syracuseStep 4562747 = 6844121) B6844121
theorem B1687431 : Blo 1686043 1687431 := bstep (se 1 (by rfl) ⟨1265573, by rfl⟩ : syracuseStep 1687431 = 2531147) B2531147
theorem B2531207 : Blo 1686043 2531207 := bstep (se 1 (by rfl) ⟨1898405, by rfl⟩ : syracuseStep 2531207 = 3796811) B3796811
theorem B1687439 : Blo 1686043 1687439 := bstep (se 1 (by rfl) ⟨1265579, by rfl⟩ : syracuseStep 1687439 = 2531159) B2531159
theorem B34611097 : Blo 1686043 34611097 := bstep (se 2 (by rfl) ⟨12979161, by rfl⟩ : syracuseStep 34611097 = 25958323) B25958323
theorem B2531243 : Blo 1686043 2531243 := bstep (se 1 (by rfl) ⟨1898432, by rfl⟩ : syracuseStep 2531243 = 3796865) B3796865
theorem B4267961 : Blo 1686043 4267961 := bstep (se 2 (by rfl) ⟨1600485, by rfl⟩ : syracuseStep 4267961 = 3200971) B3200971
theorem B6406073 : Blo 1686043 6406073 := bstep (se 2 (by rfl) ⟨2402277, by rfl⟩ : syracuseStep 6406073 = 4804555) B4804555
theorem B1687483 : Blo 1686043 1687483 := bstep (se 1 (by rfl) ⟨1265612, by rfl⟩ : syracuseStep 1687483 = 2531225) B2531225
theorem B2531273 : Blo 1686043 2531273 := bstep (se 2 (by rfl) ⟨949227, by rfl⟩ : syracuseStep 2531273 = 1898455) B1898455
theorem B8544203 : Blo 1686043 8544203 := bstep (se 1 (by rfl) ⟨6408152, by rfl⟩ : syracuseStep 8544203 = 12816305) B12816305
theorem B1687591 : Blo 1686043 1687591 := bstep (se 1 (by rfl) ⟨1265693, by rfl⟩ : syracuseStep 1687591 = 2531387) B2531387
theorem B1687631 : Blo 1686043 1687631 := bstep (se 1 (by rfl) ⟨1265723, by rfl⟩ : syracuseStep 1687631 = 2531447) B2531447
theorem B1687647 : Blo 1686043 1687647 := bstep (se 1 (by rfl) ⟨1265735, by rfl⟩ : syracuseStep 1687647 = 2531471) B2531471
theorem B1687675 : Blo 1686043 1687675 := bstep (se 1 (by rfl) ⟨1265756, by rfl⟩ : syracuseStep 1687675 = 2531513) B2531513
theorem B5693597 : Blo 1686043 5693597 := bstep (se 3 (by rfl) ⟨1067549, by rfl⟩ : syracuseStep 5693597 = 2135099) B2135099
theorem B1687727 : Blo 1686043 1687727 := bstep (se 1 (by rfl) ⟨1265795, by rfl⟩ : syracuseStep 1687727 = 2531591) B2531591
theorem B1687751 : Blo 1686043 1687751 := bstep (se 1 (by rfl) ⟨1265813, by rfl⟩ : syracuseStep 1687751 = 2531627) B2531627
theorem B1687771 : Blo 1686043 1687771 := bstep (se 1 (by rfl) ⟨1265828, by rfl⟩ : syracuseStep 1687771 = 2531657) B2531657
theorem B6406391 : Blo 1686043 6406391 := bstep (se 1 (by rfl) ⟨4804793, by rfl⟩ : syracuseStep 6406391 = 9609587) B9609587
theorem B1687847 : Blo 1686043 1687847 := bstep (se 1 (by rfl) ⟨1265885, by rfl⟩ : syracuseStep 1687847 = 2531771) B2531771
theorem B3203401 : Blo 1686043 3203401 := bstep (se 2 (by rfl) ⟨1201275, by rfl⟩ : syracuseStep 3203401 = 2402551) B2402551
theorem B1687887 : Blo 1686043 1687887 := bstep (se 1 (by rfl) ⟨1265915, by rfl⟩ : syracuseStep 1687887 = 2531831) B2531831
theorem B1687903 : Blo 1686043 1687903 := bstep (se 1 (by rfl) ⟨1265927, by rfl⟩ : syracuseStep 1687903 = 2531855) B2531855
theorem B1687931 : Blo 1686043 1687931 := bstep (se 1 (by rfl) ⟨1265948, by rfl⟩ : syracuseStep 1687931 = 2531897) B2531897
theorem B2531759 : Blo 1686043 2531759 := bstep (se 1 (by rfl) ⟨1898819, by rfl⟩ : syracuseStep 2531759 = 3797639) B3797639
theorem B1687983 : Blo 1686043 1687983 := bstep (se 1 (by rfl) ⟨1265987, by rfl⟩ : syracuseStep 1687983 = 2531975) B2531975
theorem B1688007 : Blo 1686043 1688007 := bstep (se 1 (by rfl) ⟨1266005, by rfl⟩ : syracuseStep 1688007 = 2532011) B2532011
theorem B1688027 : Blo 1686043 1688027 := bstep (se 1 (by rfl) ⟨1266020, by rfl⟩ : syracuseStep 1688027 = 2532041) B2532041
theorem B2531849 : Blo 1686043 2531849 := bstep (se 2 (by rfl) ⟨949443, by rfl⟩ : syracuseStep 2531849 = 1898887) B1898887
theorem B32432663 : Blo 1686043 32432663 := bstep (se 1 (by rfl) ⟨24324497, by rfl⟩ : syracuseStep 32432663 = 48648995) B48648995
theorem B12157465 : Blo 1686043 12157465 := bstep (se 2 (by rfl) ⟨4559049, by rfl⟩ : syracuseStep 12157465 = 9118099) B9118099
theorem B12804641 : Blo 1686043 12804641 := bstep (se 2 (by rfl) ⟨4801740, by rfl⟩ : syracuseStep 12804641 = 9603481) B9603481
theorem B2531879 : Blo 1686043 2531879 := bstep (se 1 (by rfl) ⟨1898909, by rfl⟩ : syracuseStep 2531879 = 3797819) B3797819
theorem B8774203 : Blo 1686043 8774203 := bstep (se 1 (by rfl) ⟨6580652, by rfl⟩ : syracuseStep 8774203 = 13161305) B13161305
theorem B2531963 : Blo 1686043 2531963 := bstep (se 1 (by rfl) ⟨1898972, by rfl⟩ : syracuseStep 2531963 = 3797945) B3797945
theorem B5694137 : Blo 1686043 5694137 := bstep (se 2 (by rfl) ⟨2135301, by rfl⟩ : syracuseStep 5694137 = 4270603) B4270603
theorem B3793607 : Blo 1686043 3793607 := bstep (se 1 (by rfl) ⟨2845205, by rfl⟩ : syracuseStep 3793607 = 5690411) B5690411
theorem B7504595 : Blo 1686043 7504595 := bstep (se 1 (by rfl) ⟨5628446, by rfl⟩ : syracuseStep 7504595 = 11256893) B11256893
theorem B27738883 : Blo 1686043 27738883 := bstep (se 1 (by rfl) ⟨20804162, by rfl⟩ : syracuseStep 27738883 = 41608325) B41608325
theorem B3040073 : Blo 1686043 3040073 := bstep (se 2 (by rfl) ⟨1140027, by rfl⟩ : syracuseStep 3040073 = 2280055) B2280055
theorem B4268983 : Blo 1686043 4268983 := bstep (se 1 (by rfl) ⟨3201737, by rfl⟩ : syracuseStep 4268983 = 6403475) B6403475
theorem B12166145 : Blo 1686043 12166145 := bstep (se 2 (by rfl) ⟨4562304, by rfl⟩ : syracuseStep 12166145 = 9124609) B9124609
theorem B6407363 : Blo 1686043 6407363 := bstep (se 1 (by rfl) ⟨4805522, by rfl⟩ : syracuseStep 6407363 = 9611045) B9611045
theorem B5694731 : Blo 1686043 5694731 := bstep (se 1 (by rfl) ⟨4271048, by rfl⟩ : syracuseStep 5694731 = 8542097) B8542097
theorem B13673843 : Blo 1686043 13673843 := bstep (se 1 (by rfl) ⟨10255382, by rfl⟩ : syracuseStep 13673843 = 20510765) B20510765
theorem B8545661 : Blo 1686043 8545661 := bstep (se 3 (by rfl) ⟨1602311, by rfl⟩ : syracuseStep 8545661 = 3204623) B3204623
theorem B5695001 : Blo 1686043 5695001 := bstep (se 2 (by rfl) ⟨2135625, by rfl⟩ : syracuseStep 5695001 = 4271251) B4271251
theorem B3794471 : Blo 1686043 3794471 := bstep (se 1 (by rfl) ⟨2845853, by rfl⟩ : syracuseStep 3794471 = 5691707) B5691707
theorem B8537723 : Blo 1686043 8537723 := bstep (se 1 (by rfl) ⟨6403292, by rfl⟩ : syracuseStep 8537723 = 12806585) B12806585
theorem B6407819 : Blo 1686043 6407819 := bstep (se 1 (by rfl) ⟨4805864, by rfl⟩ : syracuseStep 6407819 = 9611729) B9611729
theorem B6842045 : Blo 1686043 6842045 := bstep (se 3 (by rfl) ⟨1282883, by rfl⟩ : syracuseStep 6842045 = 2565767) B2565767
theorem B6162169 : Blo 1686043 6162169 := bstep (se 2 (by rfl) ⟨2310813, by rfl⟩ : syracuseStep 6162169 = 4621627) B4621627
theorem B6408031 : Blo 1686043 6408031 := bstep (se 1 (by rfl) ⟨4806023, by rfl⟩ : syracuseStep 6408031 = 9612047) B9612047
theorem B342091619 : Blo 1686043 342091619 := bstep (se 1 (by rfl) ⟨256568714, by rfl⟩ : syracuseStep 342091619 = 513137429) B513137429
theorem B3794795 : Blo 1686043 3794795 := bstep (se 1 (by rfl) ⟨2846096, by rfl⟩ : syracuseStep 3794795 = 5692193) B5692193
theorem B3794849 : Blo 1686043 3794849 := bstep (se 2 (by rfl) ⟨1423068, by rfl⟩ : syracuseStep 3794849 = 2846137) B2846137
theorem B14411783 : Blo 1686043 14411783 := bstep (se 1 (by rfl) ⟨10808837, by rfl⟩ : syracuseStep 14411783 = 21617675) B21617675
theorem B9742451 : Blo 1686043 9742451 := bstep (se 1 (by rfl) ⟨7306838, by rfl⟩ : syracuseStep 9742451 = 14613677) B14613677
theorem B6244523 : Blo 1686043 6244523 := bstep (se 1 (by rfl) ⟨4683392, by rfl⟩ : syracuseStep 6244523 = 9366785) B9366785
theorem B3041479 : Blo 1686043 3041479 := bstep (se 1 (by rfl) ⟨2281109, by rfl⟩ : syracuseStep 3041479 = 4562219) B4562219
theorem B3795191 : Blo 1686043 3795191 := bstep (se 1 (by rfl) ⟨2846393, by rfl⟩ : syracuseStep 3795191 = 5692787) B5692787
theorem B6080779 : Blo 1686043 6080779 := bstep (se 1 (by rfl) ⟨4560584, by rfl⟩ : syracuseStep 6080779 = 9121169) B9121169
theorem B4270441 : Blo 1686043 4270441 := bstep (se 2 (by rfl) ⟨1601415, by rfl⟩ : syracuseStep 4270441 = 3202831) B3202831
theorem B6842825 : Blo 1686043 6842825 := bstep (se 2 (by rfl) ⟨2566059, by rfl⟩ : syracuseStep 6842825 = 5132119) B5132119
theorem B2402779 : Blo 1686043 2402779 := bstep (se 1 (by rfl) ⟨1802084, by rfl⟩ : syracuseStep 2402779 = 3604169) B3604169
theorem B10807789 : Blo 1686043 10807789 := bstep (se 3 (by rfl) ⟨2026460, by rfl⟩ : syracuseStep 10807789 = 4052921) B4052921
theorem B4803097 : Blo 1686043 4803097 := bstep (se 2 (by rfl) ⟨1801161, by rfl⟩ : syracuseStep 4803097 = 3602323) B3602323
theorem B46148129 : Blo 1686043 46148129 := bstep (se 2 (by rfl) ⟨17305548, by rfl⟩ : syracuseStep 46148129 = 34611097) B34611097
theorem B3041831 : Blo 1686043 3041831 := bstep (se 1 (by rfl) ⟨2281373, by rfl⟩ : syracuseStep 3041831 = 4562747) B4562747
theorem B2845307 : Blo 1686043 2845307 := bstep (se 1 (by rfl) ⟨2133980, by rfl⟩ : syracuseStep 2845307 = 4267961) B4267961
theorem B4270715 : Blo 1686043 4270715 := bstep (se 1 (by rfl) ⟨3203036, by rfl⟩ : syracuseStep 4270715 = 6406073) B6406073
theorem B5696135 : Blo 1686043 5696135 := bstep (se 1 (by rfl) ⟨4272101, by rfl⟩ : syracuseStep 5696135 = 8544203) B8544203
theorem B5696189 : Blo 1686043 5696189 := bstep (se 3 (by rfl) ⟨1068035, by rfl⟩ : syracuseStep 5696189 = 2136071) B2136071
theorem B23079653 : Blo 1686043 23079653 := bstep (se 4 (by rfl) ⟨2163717, by rfl⟩ : syracuseStep 23079653 = 4327435) B4327435
theorem B2738935 : Blo 1686043 2738935 := bstep (se 1 (by rfl) ⟨2054201, by rfl⟩ : syracuseStep 2738935 = 4108403) B4108403
theorem B17320733 : Blo 1686043 17320733 := bstep (se 3 (by rfl) ⟨3247637, by rfl⟩ : syracuseStep 17320733 = 6495275) B6495275
theorem B6408989 : Blo 1686043 6408989 := bstep (se 3 (by rfl) ⟨1201685, by rfl⟩ : syracuseStep 6408989 = 2403371) B2403371
theorem B6409003 : Blo 1686043 6409003 := bstep (se 1 (by rfl) ⟨4806752, by rfl⟩ : syracuseStep 6409003 = 9613505) B9613505
theorem B3795785 : Blo 1686043 3795785 := bstep (se 2 (by rfl) ⟨1423419, by rfl⟩ : syracuseStep 3795785 = 2846839) B2846839
theorem B6581087 : Blo 1686043 6581087 := bstep (se 1 (by rfl) ⟨4935815, by rfl⟩ : syracuseStep 6581087 = 9871631) B9871631
theorem B5696351 : Blo 1686043 5696351 := bstep (se 1 (by rfl) ⟨4272263, by rfl⟩ : syracuseStep 5696351 = 8544527) B8544527
theorem B12815333 : Blo 1686043 12815333 := bstep (se 4 (by rfl) ⟨1201437, by rfl⟩ : syracuseStep 12815333 = 2402875) B2402875
theorem B5696513 : Blo 1686043 5696513 := bstep (se 2 (by rfl) ⟨2136192, by rfl⟩ : syracuseStep 5696513 = 4272385) B4272385
theorem B2845705 : Blo 1686043 2845705 := bstep (se 2 (by rfl) ⟨1067139, by rfl⟩ : syracuseStep 2845705 = 2134279) B2134279
theorem B2845867 : Blo 1686043 2845867 := bstep (se 1 (by rfl) ⟨2134400, by rfl⟩ : syracuseStep 2845867 = 4268801) B4268801
theorem B23088401 : Blo 1686043 23088401 := bstep (se 2 (by rfl) ⟨8658150, by rfl⟩ : syracuseStep 23088401 = 17316301) B17316301
theorem B21908879 : Blo 1686043 21908879 := bstep (se 1 (by rfl) ⟨16431659, by rfl⟩ : syracuseStep 21908879 = 32863319) B32863319
theorem B2846171 : Blo 1686043 2846171 := bstep (se 1 (by rfl) ⟨2134628, by rfl⟩ : syracuseStep 2846171 = 4269257) B4269257
theorem B3796577 : Blo 1686043 3796577 := bstep (se 2 (by rfl) ⟨1423716, by rfl⟩ : syracuseStep 3796577 = 2847433) B2847433
theorem B8654525 : Blo 1686043 8654525 := bstep (se 3 (by rfl) ⟨1622723, by rfl⟩ : syracuseStep 8654525 = 3245447) B3245447
theorem B2846407 : Blo 1686043 2846407 := bstep (se 1 (by rfl) ⟨2134805, by rfl⟩ : syracuseStep 2846407 = 4269611) B4269611
theorem B16215875 : Blo 1686043 16215875 := bstep (se 1 (by rfl) ⟨12161906, by rfl⟩ : syracuseStep 16215875 = 24323813) B24323813
theorem B2846569 : Blo 1686043 2846569 := bstep (se 2 (by rfl) ⟨1067463, by rfl⟩ : syracuseStep 2846569 = 2134927) B2134927
theorem B6164333 : Blo 1686043 6164333 := bstep (se 3 (by rfl) ⟨1155812, by rfl⟩ : syracuseStep 6164333 = 2311625) B2311625
theorem B3796919 : Blo 1686043 3796919 := bstep (se 1 (by rfl) ⟨2847689, by rfl⟩ : syracuseStep 3796919 = 5695379) B5695379
theorem B18231227 : Blo 1686043 18231227 := bstep (se 1 (by rfl) ⟨13673420, by rfl⟩ : syracuseStep 18231227 = 27346841) B27346841
theorem B4558855 : Blo 1686043 4558855 := bstep (se 1 (by rfl) ⟨3419141, by rfl⟩ : syracuseStep 4558855 = 6838283) B6838283
theorem B5132459 : Blo 1686043 5132459 := bstep (se 1 (by rfl) ⟨3849344, by rfl⟩ : syracuseStep 5132459 = 7698689) B7698689
theorem B38957233 : Blo 1686043 38957233 := bstep (se 2 (by rfl) ⟨14608962, by rfl⟩ : syracuseStep 38957233 = 29217925) B29217925
theorem B8540477 : Blo 1686043 8540477 := bstep (se 3 (by rfl) ⟨1601339, by rfl⟩ : syracuseStep 8540477 = 3202679) B3202679
theorem B1896799 : Blo 1686043 1896799 := bstep (se 1 (by rfl) ⟨1422599, by rfl⟩ : syracuseStep 1896799 = 2845199) B2845199
theorem B24310145 : Blo 1686043 24310145 := bstep (se 2 (by rfl) ⟨9116304, by rfl⟩ : syracuseStep 24310145 = 18232609) B18232609
theorem B4272527 : Blo 1686043 4272527 := bstep (se 1 (by rfl) ⟨3204395, by rfl⟩ : syracuseStep 4272527 = 6408791) B6408791
theorem B2847163 : Blo 1686043 2847163 := bstep (se 1 (by rfl) ⟨2135372, by rfl⟩ : syracuseStep 2847163 = 4270745) B4270745
theorem B3797513 : Blo 1686043 3797513 := bstep (se 2 (by rfl) ⟨1424067, by rfl⟩ : syracuseStep 3797513 = 2848135) B2848135
theorem B2847271 : Blo 1686043 2847271 := bstep (se 1 (by rfl) ⟨2135453, by rfl⟩ : syracuseStep 2847271 = 4270907) B4270907
theorem B21607013 : Blo 1686043 21607013 := bstep (se 4 (by rfl) ⟨2025657, by rfl⟩ : syracuseStep 21607013 = 4051315) B4051315
theorem B128242349 : Blo 1686043 128242349 := bstep (se 3 (by rfl) ⟨24045440, by rfl⟩ : syracuseStep 128242349 = 48090881) B48090881
theorem B1897159 : Blo 1686043 1897159 := bstep (se 1 (by rfl) ⟨1422869, by rfl⟩ : syracuseStep 1897159 = 2845739) B2845739
theorem B4272851 : Blo 1686043 4272851 := bstep (se 1 (by rfl) ⟨3204638, by rfl⟩ : syracuseStep 4272851 = 6409277) B6409277
theorem B3797855 : Blo 1686043 3797855 := bstep (se 1 (by rfl) ⟨2848391, by rfl⟩ : syracuseStep 3797855 = 5696783) B5696783
theorem B2847595 : Blo 1686043 2847595 := bstep (se 1 (by rfl) ⟨2135696, by rfl⟩ : syracuseStep 2847595 = 4271393) B4271393
theorem B4051873 : Blo 1686043 4051873 := bstep (se 2 (by rfl) ⟨1519452, by rfl⟩ : syracuseStep 4051873 = 3038905) B3038905
theorem B3798035 : Blo 1686043 3798035 := bstep (se 1 (by rfl) ⟨2848526, by rfl⟩ : syracuseStep 3798035 = 5697053) B5697053
theorem B3601579 : Blo 1686043 3601579 := bstep (se 1 (by rfl) ⟨2701184, by rfl⟩ : syracuseStep 3601579 = 5402369) B5402369
theorem B5404009 : Blo 1686043 5404009 := bstep (se 2 (by rfl) ⟨2026503, by rfl⟩ : syracuseStep 5404009 = 4053007) B4053007
theorem B4806013 : Blo 1686043 4806013 := bstep (se 3 (by rfl) ⟨901127, by rfl⟩ : syracuseStep 4806013 = 1802255) B1802255
theorem B2135479 : Blo 1686043 2135479 := bstep (se 1 (by rfl) ⟨1601609, by rfl⟩ : syracuseStep 2135479 = 3203219) B3203219
theorem B5690843 : Blo 1686043 5690843 := bstep (se 1 (by rfl) ⟨4268132, by rfl⟩ : syracuseStep 5690843 = 8536265) B8536265
theorem B19207691 : Blo 1686043 19207691 := bstep (se 1 (by rfl) ⟨14405768, by rfl⟩ : syracuseStep 19207691 = 28811537) B28811537
theorem B2700839 : Blo 1686043 2700839 := bstep (se 1 (by rfl) ⟨2025629, by rfl⟩ : syracuseStep 2700839 = 4051259) B4051259
theorem B1898023 : Blo 1686043 1898023 := bstep (se 1 (by rfl) ⟨1423517, by rfl⟩ : syracuseStep 1898023 = 2847035) B2847035
theorem B6403643 : Blo 1686043 6403643 := bstep (se 1 (by rfl) ⟨4802732, by rfl⟩ : syracuseStep 6403643 = 9605465) B9605465
theorem B6166201 : Blo 1686043 6166201 := bstep (se 2 (by rfl) ⟨2312325, by rfl⟩ : syracuseStep 6166201 = 4624651) B4624651
theorem B13678379 : Blo 1686043 13678379 := bstep (se 1 (by rfl) ⟨10258784, by rfl⟩ : syracuseStep 13678379 = 20517569) B20517569
theorem B2529119 : Blo 1686043 2529119 := bstep (se 1 (by rfl) ⟨1896839, by rfl⟩ : syracuseStep 2529119 = 3793679) B3793679
theorem B2529131 : Blo 1686043 2529131 := bstep (se 1 (by rfl) ⟨1896848, by rfl⟩ : syracuseStep 2529131 = 3793697) B3793697
theorem B92362787 : Blo 1686043 92362787 := bstep (se 1 (by rfl) ⟨69272090, by rfl⟩ : syracuseStep 92362787 = 138544181) B138544181
theorem B2529359 : Blo 1686043 2529359 := bstep (se 1 (by rfl) ⟨1897019, by rfl⟩ : syracuseStep 2529359 = 3794039) B3794039
theorem B15390809 : Blo 1686043 15390809 := bstep (se 2 (by rfl) ⟨5771553, by rfl⟩ : syracuseStep 15390809 = 11543107) B11543107
theorem B5691545 : Blo 1686043 5691545 := bstep (se 2 (by rfl) ⟨2134329, by rfl⟩ : syracuseStep 5691545 = 4268659) B4268659
theorem B2529479 : Blo 1686043 2529479 := bstep (se 1 (by rfl) ⟨1897109, by rfl⟩ : syracuseStep 2529479 = 3794219) B3794219
theorem B18233687 : Blo 1686043 18233687 := bstep (se 1 (by rfl) ⟨13675265, by rfl⟩ : syracuseStep 18233687 = 27350531) B27350531
theorem B2529641 : Blo 1686043 2529641 := bstep (se 2 (by rfl) ⟨948615, by rfl⟩ : syracuseStep 2529641 = 1897231) B1897231
theorem B2529719 : Blo 1686043 2529719 := bstep (se 1 (by rfl) ⟨1897289, by rfl⟩ : syracuseStep 2529719 = 3794579) B3794579
theorem B2529755 : Blo 1686043 2529755 := bstep (se 1 (by rfl) ⟨1897316, by rfl⟩ : syracuseStep 2529755 = 3794633) B3794633
theorem B8542745 : Blo 1686043 8542745 := bstep (se 2 (by rfl) ⟨3203529, by rfl⟩ : syracuseStep 8542745 = 6407059) B6407059
theorem B1686055 : Blo 1686043 1686055 := bstep (se 1 (by rfl) ⟨1264541, by rfl⟩ : syracuseStep 1686055 = 2529083) B2529083
theorem B1686095 : Blo 1686043 1686095 := bstep (se 1 (by rfl) ⟨1264571, by rfl⟩ : syracuseStep 1686095 = 2529143) B2529143
theorem B1686111 : Blo 1686043 1686111 := bstep (se 1 (by rfl) ⟨1264583, by rfl⟩ : syracuseStep 1686111 = 2529167) B2529167
theorem B1686139 : Blo 1686043 1686139 := bstep (se 1 (by rfl) ⟨1264604, by rfl⟩ : syracuseStep 1686139 = 2529209) B2529209
theorem B5773963 : Blo 1686043 5773963 := bstep (se 1 (by rfl) ⟨4330472, by rfl⟩ : syracuseStep 5773963 = 8660945) B8660945
theorem B6838931 : Blo 1686043 6838931 := bstep (se 1 (by rfl) ⟨5129198, by rfl⟩ : syracuseStep 6838931 = 10258397) B10258397
theorem B3201707 : Blo 1686043 3201707 := bstep (se 1 (by rfl) ⟨2401280, by rfl⟩ : syracuseStep 3201707 = 4802561) B4802561
theorem B1686191 : Blo 1686043 1686191 := bstep (se 1 (by rfl) ⟨1264643, by rfl⟩ : syracuseStep 1686191 = 2529287) B2529287
theorem B1686215 : Blo 1686043 1686215 := bstep (se 1 (by rfl) ⟨1264661, by rfl⟩ : syracuseStep 1686215 = 2529323) B2529323
theorem B3603143 : Blo 1686043 3603143 := bstep (se 1 (by rfl) ⟨2702357, by rfl⟩ : syracuseStep 3603143 = 5404715) B5404715
theorem B4053719 : Blo 1686043 4053719 := bstep (se 1 (by rfl) ⟨3040289, by rfl⟩ : syracuseStep 4053719 = 6080579) B6080579
theorem B1686235 : Blo 1686043 1686235 := bstep (se 1 (by rfl) ⟨1264676, by rfl⟩ : syracuseStep 1686235 = 2529353) B2529353
theorem B72940277 : Blo 1686043 72940277 := bstep (se 5 (by rfl) ⟨3419075, by rfl⟩ : syracuseStep 72940277 = 6838151) B6838151
theorem B1686311 : Blo 1686043 1686311 := bstep (se 1 (by rfl) ⟨1264733, by rfl⟩ : syracuseStep 1686311 = 2529467) B2529467
theorem B2702153 : Blo 1686043 2702153 := bstep (se 2 (by rfl) ⟨1013307, by rfl⟩ : syracuseStep 2702153 = 2026615) B2026615
theorem B1686351 : Blo 1686043 1686351 := bstep (se 1 (by rfl) ⟨1264763, by rfl⟩ : syracuseStep 1686351 = 2529527) B2529527
theorem B51968861 : Blo 1686043 51968861 := bstep (se 3 (by rfl) ⟨9744161, by rfl⟩ : syracuseStep 51968861 = 19488323) B19488323
theorem B1686367 : Blo 1686043 1686367 := bstep (se 1 (by rfl) ⟨1264775, by rfl⟩ : syracuseStep 1686367 = 2529551) B2529551
theorem B1686395 : Blo 1686043 1686395 := bstep (se 1 (by rfl) ⟨1264796, by rfl⟩ : syracuseStep 1686395 = 2529593) B2529593
theorem B14613395 : Blo 1686043 14613395 := bstep (se 1 (by rfl) ⟨10960046, by rfl⟩ : syracuseStep 14613395 = 21920093) B21920093
theorem B1686447 : Blo 1686043 1686447 := bstep (se 1 (by rfl) ⟨1264835, by rfl⟩ : syracuseStep 1686447 = 2529671) B2529671
theorem B2530223 : Blo 1686043 2530223 := bstep (se 1 (by rfl) ⟨1897667, by rfl⟩ : syracuseStep 2530223 = 3795335) B3795335
theorem B15383479 : Blo 1686043 15383479 := bstep (se 1 (by rfl) ⟨11537609, by rfl⟩ : syracuseStep 15383479 = 23075219) B23075219
theorem B1686471 : Blo 1686043 1686471 := bstep (se 1 (by rfl) ⟨1264853, by rfl⟩ : syracuseStep 1686471 = 2529707) B2529707
theorem B1686491 : Blo 1686043 1686491 := bstep (se 1 (by rfl) ⟨1264868, by rfl⟩ : syracuseStep 1686491 = 2529737) B2529737
theorem B10804225 : Blo 1686043 10804225 := bstep (se 2 (by rfl) ⟨4051584, by rfl⟩ : syracuseStep 10804225 = 8103169) B8103169
theorem B2530313 : Blo 1686043 2530313 := bstep (se 2 (by rfl) ⟨948867, by rfl⟩ : syracuseStep 2530313 = 1897735) B1897735
theorem B1686567 : Blo 1686043 1686567 := bstep (se 1 (by rfl) ⟨1264925, by rfl⟩ : syracuseStep 1686567 = 2529851) B2529851
theorem B3202087 : Blo 1686043 3202087 := bstep (se 1 (by rfl) ⟨2401565, by rfl⟩ : syracuseStep 3202087 = 4803131) B4803131
theorem B2530343 : Blo 1686043 2530343 := bstep (se 1 (by rfl) ⟨1897757, by rfl⟩ : syracuseStep 2530343 = 3795515) B3795515
theorem B1686607 : Blo 1686043 1686607 := bstep (se 1 (by rfl) ⟨1264955, by rfl⟩ : syracuseStep 1686607 = 2529911) B2529911
theorem B1686623 : Blo 1686043 1686623 := bstep (se 1 (by rfl) ⟨1264967, by rfl⟩ : syracuseStep 1686623 = 2529935) B2529935
theorem B1686651 : Blo 1686043 1686651 := bstep (se 1 (by rfl) ⟨1264988, by rfl⟩ : syracuseStep 1686651 = 2529977) B2529977
theorem B2530427 : Blo 1686043 2530427 := bstep (se 1 (by rfl) ⟨1897820, by rfl⟩ : syracuseStep 2530427 = 3795641) B3795641
theorem B1686703 : Blo 1686043 1686703 := bstep (se 1 (by rfl) ⟨1265027, by rfl⟩ : syracuseStep 1686703 = 2530055) B2530055
theorem B14605505 : Blo 1686043 14605505 := bstep (se 2 (by rfl) ⟨5477064, by rfl⟩ : syracuseStep 14605505 = 10954129) B10954129
theorem B1686727 : Blo 1686043 1686727 := bstep (se 1 (by rfl) ⟨1265045, by rfl⟩ : syracuseStep 1686727 = 2530091) B2530091
theorem B3202247 : Blo 1686043 3202247 := bstep (se 1 (by rfl) ⟨2401685, by rfl⟩ : syracuseStep 3202247 = 4803371) B4803371
theorem B1686747 : Blo 1686043 1686747 := bstep (se 1 (by rfl) ⟨1265060, by rfl⟩ : syracuseStep 1686747 = 2530121) B2530121
theorem B2530553 : Blo 1686043 2530553 := bstep (se 2 (by rfl) ⟨948957, by rfl⟩ : syracuseStep 2530553 = 1897915) B1897915
theorem B1686823 : Blo 1686043 1686823 := bstep (se 1 (by rfl) ⟨1265117, by rfl⟩ : syracuseStep 1686823 = 2530235) B2530235
theorem B5692733 : Blo 1686043 5692733 := bstep (se 3 (by rfl) ⟨1067387, by rfl⟩ : syracuseStep 5692733 = 2134775) B2134775
theorem B1686863 : Blo 1686043 1686863 := bstep (se 1 (by rfl) ⟨1265147, by rfl⟩ : syracuseStep 1686863 = 2530295) B2530295
theorem B14409049 : Blo 1686043 14409049 := bstep (se 2 (by rfl) ⟨5403393, by rfl⟩ : syracuseStep 14409049 = 10806787) B10806787
theorem B1686879 : Blo 1686043 1686879 := bstep (se 1 (by rfl) ⟨1265159, by rfl⟩ : syracuseStep 1686879 = 2530319) B2530319
theorem B2530655 : Blo 1686043 2530655 := bstep (se 1 (by rfl) ⟨1897991, by rfl⟩ : syracuseStep 2530655 = 3795983) B3795983
theorem B2530667 : Blo 1686043 2530667 := bstep (se 1 (by rfl) ⟨1898000, by rfl⟩ : syracuseStep 2530667 = 3796001) B3796001
theorem B1686907 : Blo 1686043 1686907 := bstep (se 1 (by rfl) ⟨1265180, by rfl⟩ : syracuseStep 1686907 = 2530361) B2530361
theorem B7691645 : Blo 1686043 7691645 := bstep (se 3 (by rfl) ⟨1442183, by rfl⟩ : syracuseStep 7691645 = 2884367) B2884367
theorem B1686959 : Blo 1686043 1686959 := bstep (se 1 (by rfl) ⟨1265219, by rfl⟩ : syracuseStep 1686959 = 2530439) B2530439
theorem B1686983 : Blo 1686043 1686983 := bstep (se 1 (by rfl) ⟨1265237, by rfl⟩ : syracuseStep 1686983 = 2530475) B2530475
theorem B1687003 : Blo 1686043 1687003 := bstep (se 1 (by rfl) ⟨1265252, by rfl⟩ : syracuseStep 1687003 = 2530505) B2530505
theorem B1687079 : Blo 1686043 1687079 := bstep (se 1 (by rfl) ⟨1265309, by rfl⟩ : syracuseStep 1687079 = 2530619) B2530619
theorem B1687119 : Blo 1686043 1687119 := bstep (se 1 (by rfl) ⟨1265339, by rfl⟩ : syracuseStep 1687119 = 2530679) B2530679
theorem B2530895 : Blo 1686043 2530895 := bstep (se 1 (by rfl) ⟨1898171, by rfl⟩ : syracuseStep 2530895 = 3796343) B3796343
theorem B2702927 : Blo 1686043 2702927 := bstep (se 1 (by rfl) ⟨2027195, by rfl⟩ : syracuseStep 2702927 = 4054391) B4054391
theorem B1687135 : Blo 1686043 1687135 := bstep (se 1 (by rfl) ⟨1265351, by rfl⟩ : syracuseStep 1687135 = 2530703) B2530703
theorem B1687163 : Blo 1686043 1687163 := bstep (se 1 (by rfl) ⟨1265372, by rfl⟩ : syracuseStep 1687163 = 2530745) B2530745
theorem B5406355 : Blo 1686043 5406355 := bstep (se 1 (by rfl) ⟨4054766, by rfl⟩ : syracuseStep 5406355 = 8109533) B8109533
theorem B1687215 : Blo 1686043 1687215 := bstep (se 1 (by rfl) ⟨1265411, by rfl⟩ : syracuseStep 1687215 = 2530823) B2530823
theorem B3464903 : Blo 1686043 3464903 := bstep (se 1 (by rfl) ⟨2598677, by rfl⟩ : syracuseStep 3464903 = 5197355) B5197355
theorem B1687239 : Blo 1686043 1687239 := bstep (se 1 (by rfl) ⟨1265429, by rfl⟩ : syracuseStep 1687239 = 2530859) B2530859
theorem B2531015 : Blo 1686043 2531015 := bstep (se 1 (by rfl) ⟨1898261, by rfl⟩ : syracuseStep 2531015 = 3796523) B3796523
theorem B5406419 : Blo 1686043 5406419 := bstep (se 1 (by rfl) ⟨4054814, by rfl⟩ : syracuseStep 5406419 = 8109629) B8109629
theorem B1687259 : Blo 1686043 1687259 := bstep (se 1 (by rfl) ⟨1265444, by rfl⟩ : syracuseStep 1687259 = 2530889) B2530889
theorem B1687335 : Blo 1686043 1687335 := bstep (se 1 (by rfl) ⟨1265501, by rfl⟩ : syracuseStep 1687335 = 2531003) B2531003
theorem B7208747 : Blo 1686043 7208747 := bstep (se 1 (by rfl) ⟨5406560, by rfl⟩ : syracuseStep 7208747 = 10813121) B10813121
theorem B4267849 : Blo 1686043 4267849 := bstep (se 2 (by rfl) ⟨1600443, by rfl⟩ : syracuseStep 4267849 = 3200887) B3200887
theorem B1687375 : Blo 1686043 1687375 := bstep (se 1 (by rfl) ⟨1265531, by rfl⟩ : syracuseStep 1687375 = 2531063) B2531063
theorem B1687391 : Blo 1686043 1687391 := bstep (se 1 (by rfl) ⟨1265543, by rfl⟩ : syracuseStep 1687391 = 2531087) B2531087
theorem B2531177 : Blo 1686043 2531177 := bstep (se 2 (by rfl) ⟨949191, by rfl⟩ : syracuseStep 2531177 = 1898383) B1898383
theorem B3604331 : Blo 1686043 3604331 := bstep (se 1 (by rfl) ⟨2703248, by rfl⟩ : syracuseStep 3604331 = 5406497) B5406497
theorem B1687419 : Blo 1686043 1687419 := bstep (se 1 (by rfl) ⟨1265564, by rfl⟩ : syracuseStep 1687419 = 2531129) B2531129
theorem B1687471 : Blo 1686043 1687471 := bstep (se 1 (by rfl) ⟨1265603, by rfl⟩ : syracuseStep 1687471 = 2531207) B2531207
theorem B2531255 : Blo 1686043 2531255 := bstep (se 1 (by rfl) ⟨1898441, by rfl⟩ : syracuseStep 2531255 = 3796883) B3796883
theorem B1687495 : Blo 1686043 1687495 := bstep (se 1 (by rfl) ⟨1265621, by rfl⟩ : syracuseStep 1687495 = 2531243) B2531243
theorem B1687515 : Blo 1686043 1687515 := bstep (se 1 (by rfl) ⟨1265636, by rfl⟩ : syracuseStep 1687515 = 2531273) B2531273
theorem B2531291 : Blo 1686043 2531291 := bstep (se 1 (by rfl) ⟨1898468, by rfl⟩ : syracuseStep 2531291 = 3796937) B3796937
theorem B6078473 : Blo 1686043 6078473 := bstep (se 2 (by rfl) ⟨2279427, by rfl⟩ : syracuseStep 6078473 = 4558855) B4558855
theorem B5693651 : Blo 1686043 5693651 := bstep (se 1 (by rfl) ⟨4270238, by rfl⟩ : syracuseStep 5693651 = 8540477) B8540477
theorem B1687839 : Blo 1686043 1687839 := bstep (se 1 (by rfl) ⟨1265879, by rfl⟩ : syracuseStep 1687839 = 2531759) B2531759
theorem B2531675 : Blo 1686043 2531675 := bstep (se 1 (by rfl) ⟨1898756, by rfl⟩ : syracuseStep 2531675 = 3797513) B3797513
theorem B1687899 : Blo 1686043 1687899 := bstep (se 1 (by rfl) ⟨1265924, by rfl⟩ : syracuseStep 1687899 = 2531849) B2531849
theorem B8536427 : Blo 1686043 8536427 := bstep (se 1 (by rfl) ⟨6402320, by rfl⟩ : syracuseStep 8536427 = 12804641) B12804641
theorem B1687919 : Blo 1686043 1687919 := bstep (se 1 (by rfl) ⟨1265939, by rfl⟩ : syracuseStep 1687919 = 2531879) B2531879
theorem B1687975 : Blo 1686043 1687975 := bstep (se 1 (by rfl) ⟨1265981, by rfl⟩ : syracuseStep 1687975 = 2531963) B2531963
theorem B5693921 : Blo 1686043 5693921 := bstep (se 2 (by rfl) ⟨2135220, by rfl⟩ : syracuseStep 5693921 = 4270441) B4270441
theorem B2531903 : Blo 1686043 2531903 := bstep (se 1 (by rfl) ⟨1898927, by rfl⟩ : syracuseStep 2531903 = 3797855) B3797855
theorem B3203705 : Blo 1686043 3203705 := bstep (se 2 (by rfl) ⟨1201389, by rfl⟩ : syracuseStep 3203705 = 2402779) B2402779
theorem B14410385 : Blo 1686043 14410385 := bstep (se 2 (by rfl) ⟨5403894, by rfl⟩ : syracuseStep 14410385 = 10807789) B10807789
theorem B8110763 : Blo 1686043 8110763 := bstep (se 1 (by rfl) ⟨6083072, by rfl⟩ : syracuseStep 8110763 = 12166145) B12166145
theorem B2532023 : Blo 1686043 2532023 := bstep (se 1 (by rfl) ⟨1899017, by rfl⟩ : syracuseStep 2532023 = 3798035) B3798035
theorem B11698937 : Blo 1686043 11698937 := bstep (se 2 (by rfl) ⟨4387101, by rfl⟩ : syracuseStep 11698937 = 8774203) B8774203
theorem B3793895 : Blo 1686043 3793895 := bstep (se 1 (by rfl) ⟨2845421, by rfl⟩ : syracuseStep 3793895 = 5690843) B5690843
theorem B12805127 : Blo 1686043 12805127 := bstep (se 1 (by rfl) ⟨9603845, by rfl⟩ : syracuseStep 12805127 = 19207691) B19207691
theorem B16221221 : Blo 1686043 16221221 := bstep (se 4 (by rfl) ⟨1520739, by rfl⟩ : syracuseStep 16221221 = 3041479) B3041479
theorem B4269095 : Blo 1686043 4269095 := bstep (se 1 (by rfl) ⟨3201821, by rfl⟩ : syracuseStep 4269095 = 6403643) B6403643
theorem B8545337 : Blo 1686043 8545337 := bstep (se 2 (by rfl) ⟨3204501, by rfl⟩ : syracuseStep 8545337 = 6409003) B6409003
theorem B9118919 : Blo 1686043 9118919 := bstep (se 1 (by rfl) ⟨6839189, by rfl⟩ : syracuseStep 9118919 = 13678379) B13678379
theorem B3794273 : Blo 1686043 3794273 := bstep (se 2 (by rfl) ⟨1422852, by rfl⟩ : syracuseStep 3794273 = 2845705) B2845705
theorem B4269449 : Blo 1686043 4269449 := bstep (se 2 (by rfl) ⟨1601043, by rfl⟩ : syracuseStep 4269449 = 3202087) B3202087
theorem B3794363 : Blo 1686043 3794363 := bstep (se 1 (by rfl) ⟨2845772, by rfl⟩ : syracuseStep 3794363 = 5691545) B5691545
theorem B8111549 : Blo 1686043 8111549 := bstep (se 3 (by rfl) ⟨1520915, by rfl⟩ : syracuseStep 8111549 = 3041831) B3041831
theorem B4163015 : Blo 1686043 4163015 := bstep (se 1 (by rfl) ⟨3122261, by rfl⟩ : syracuseStep 4163015 = 6244523) B6244523
theorem B4802105 : Blo 1686043 4802105 := bstep (se 2 (by rfl) ⟨1800789, by rfl⟩ : syracuseStep 4802105 = 3601579) B3601579
theorem B3794489 : Blo 1686043 3794489 := bstep (se 2 (by rfl) ⟨1422933, by rfl⟩ : syracuseStep 3794489 = 2845867) B2845867
theorem B5695163 : Blo 1686043 5695163 := bstep (se 1 (by rfl) ⟨4271372, by rfl⟩ : syracuseStep 5695163 = 8542745) B8542745
theorem B18237149 : Blo 1686043 18237149 := bstep (se 3 (by rfl) ⟨3419465, by rfl⟩ : syracuseStep 18237149 = 6838931) B6838931
theorem B8537885 : Blo 1686043 8537885 := bstep (se 3 (by rfl) ⟨1600853, by rfl⟩ : syracuseStep 8537885 = 3201707) B3201707
theorem B19212065 : Blo 1686043 19212065 := bstep (se 2 (by rfl) ⟨7204524, by rfl⟩ : syracuseStep 19212065 = 14409049) B14409049
theorem B15386435 : Blo 1686043 15386435 := bstep (se 1 (by rfl) ⟨11539826, by rfl⟩ : syracuseStep 15386435 = 23079653) B23079653
theorem B6408017 : Blo 1686043 6408017 := bstep (se 2 (by rfl) ⟨2403006, by rfl⟩ : syracuseStep 6408017 = 4806013) B4806013
theorem B34645907 : Blo 1686043 34645907 := bstep (se 1 (by rfl) ⟨25984430, by rfl⟩ : syracuseStep 34645907 = 51968861) B51968861
theorem B3795155 : Blo 1686043 3795155 := bstep (se 1 (by rfl) ⟨2846366, by rfl⟩ : syracuseStep 3795155 = 5692733) B5692733
theorem B3795209 : Blo 1686043 3795209 := bstep (se 2 (by rfl) ⟨1423203, by rfl⟩ : syracuseStep 3795209 = 2846407) B2846407
theorem B5769683 : Blo 1686043 5769683 := bstep (se 1 (by rfl) ⟨4327262, by rfl⟩ : syracuseStep 5769683 = 8654525) B8654525
theorem B3795425 : Blo 1686043 3795425 := bstep (se 2 (by rfl) ⟨1423284, by rfl⟩ : syracuseStep 3795425 = 2846569) B2846569
theorem B2402887 : Blo 1686043 2402887 := bstep (se 1 (by rfl) ⟨1802165, by rfl⟩ : syracuseStep 2402887 = 3604331) B3604331
theorem B3795731 : Blo 1686043 3795731 := bstep (se 1 (by rfl) ⟨2846798, by rfl⟩ : syracuseStep 3795731 = 5693597) B5693597
theorem B4270927 : Blo 1686043 4270927 := bstep (se 1 (by rfl) ⟨3203195, by rfl⟩ : syracuseStep 4270927 = 6406391) B6406391
theorem B16206763 : Blo 1686043 16206763 := bstep (se 1 (by rfl) ⟨12155072, by rfl⟩ : syracuseStep 16206763 = 24310145) B24310145
theorem B25979869 : Blo 1686043 25979869 := bstep (se 3 (by rfl) ⟨4871225, by rfl⟩ : syracuseStep 25979869 = 9742451) B9742451
theorem B21621775 : Blo 1686043 21621775 := bstep (se 1 (by rfl) ⟨16216331, by rfl⟩ : syracuseStep 21621775 = 32432663) B32432663
theorem B14404675 : Blo 1686043 14404675 := bstep (se 1 (by rfl) ⟨10803506, by rfl⟩ : syracuseStep 14404675 = 21607013) B21607013
theorem B4271201 : Blo 1686043 4271201 := bstep (se 2 (by rfl) ⟨1601700, by rfl⟩ : syracuseStep 4271201 = 3203401) B3203401
theorem B85494899 : Blo 1686043 85494899 := bstep (se 1 (by rfl) ⟨64121174, by rfl⟩ : syracuseStep 85494899 = 128242349) B128242349
theorem B3796091 : Blo 1686043 3796091 := bstep (se 1 (by rfl) ⟨2847068, by rfl⟩ : syracuseStep 3796091 = 5694137) B5694137
theorem B2026715 : Blo 1686043 2026715 := bstep (se 1 (by rfl) ⟨1520036, by rfl⟩ : syracuseStep 2026715 = 3040073) B3040073
theorem B3796217 : Blo 1686043 3796217 := bstep (se 2 (by rfl) ⟨1423581, by rfl⟩ : syracuseStep 3796217 = 2847163) B2847163
theorem B3796361 : Blo 1686043 3796361 := bstep (se 2 (by rfl) ⟨1423635, by rfl⟩ : syracuseStep 3796361 = 2847271) B2847271
theorem B4271575 : Blo 1686043 4271575 := bstep (se 1 (by rfl) ⟨3203681, by rfl⟩ : syracuseStep 4271575 = 6407363) B6407363
theorem B3796487 : Blo 1686043 3796487 := bstep (se 1 (by rfl) ⟨2847365, by rfl⟩ : syracuseStep 3796487 = 5694731) B5694731
theorem B5697107 : Blo 1686043 5697107 := bstep (se 1 (by rfl) ⟨4272830, by rfl⟩ : syracuseStep 5697107 = 8545661) B8545661
theorem B3796667 : Blo 1686043 3796667 := bstep (se 1 (by rfl) ⟨2847500, by rfl⟩ : syracuseStep 3796667 = 5695001) B5695001
theorem B4271879 : Blo 1686043 4271879 := bstep (se 1 (by rfl) ⟨3203909, by rfl⟩ : syracuseStep 4271879 = 6407819) B6407819
theorem B3796793 : Blo 1686043 3796793 := bstep (se 2 (by rfl) ⟨1423797, by rfl⟩ : syracuseStep 3796793 = 2847595) B2847595
theorem B228061079 : Blo 1686043 228061079 := bstep (se 1 (by rfl) ⟨171045809, by rfl⟩ : syracuseStep 228061079 = 342091619) B342091619
theorem B14405633 : Blo 1686043 14405633 := bstep (se 2 (by rfl) ⟨5402112, by rfl⟩ : syracuseStep 14405633 = 10804225) B10804225
theorem B61575191 : Blo 1686043 61575191 := bstep (se 1 (by rfl) ⟨46181393, by rfl⟩ : syracuseStep 61575191 = 92362787) B92362787
theorem B10260539 : Blo 1686043 10260539 := bstep (se 1 (by rfl) ⟨7695404, by rfl⟩ : syracuseStep 10260539 = 15390809) B15390809
theorem B30765419 : Blo 1686043 30765419 := bstep (se 1 (by rfl) ⟨23074064, by rfl⟩ : syracuseStep 30765419 = 46148129) B46148129
theorem B1896871 : Blo 1686043 1896871 := bstep (se 1 (by rfl) ⟨1422653, by rfl⟩ : syracuseStep 1896871 = 2845307) B2845307
theorem B2847143 : Blo 1686043 2847143 := bstep (se 1 (by rfl) ⟨2135357, by rfl⟩ : syracuseStep 2847143 = 4270715) B4270715
theorem B3797423 : Blo 1686043 3797423 := bstep (se 1 (by rfl) ⟨2848067, by rfl⟩ : syracuseStep 3797423 = 5696135) B5696135
theorem B3797459 : Blo 1686043 3797459 := bstep (se 1 (by rfl) ⟨2848094, by rfl⟩ : syracuseStep 3797459 = 5696189) B5696189
theorem B7205345 : Blo 1686043 7205345 := bstep (se 2 (by rfl) ⟨2702004, by rfl⟩ : syracuseStep 7205345 = 5404009) B5404009
theorem B11547155 : Blo 1686043 11547155 := bstep (se 1 (by rfl) ⟨8660366, by rfl⟩ : syracuseStep 11547155 = 17320733) B17320733
theorem B4272659 : Blo 1686043 4272659 := bstep (se 1 (by rfl) ⟨3204494, by rfl⟩ : syracuseStep 4272659 = 6408989) B6408989
theorem B4387391 : Blo 1686043 4387391 := bstep (se 1 (by rfl) ⟨3290543, by rfl⟩ : syracuseStep 4387391 = 6581087) B6581087
theorem B3797567 : Blo 1686043 3797567 := bstep (se 1 (by rfl) ⟨2848175, by rfl⟩ : syracuseStep 3797567 = 5696351) B5696351
theorem B2847305 : Blo 1686043 2847305 := bstep (se 2 (by rfl) ⟨1067739, by rfl⟩ : syracuseStep 2847305 = 2135479) B2135479
theorem B3797675 : Blo 1686043 3797675 := bstep (se 1 (by rfl) ⟨2848256, by rfl⟩ : syracuseStep 3797675 = 5696513) B5696513
theorem B9737003 : Blo 1686043 9737003 := bstep (se 1 (by rfl) ⟨7302752, by rfl⟩ : syracuseStep 9737003 = 14605505) B14605505
theorem B2134831 : Blo 1686043 2134831 := bstep (se 1 (by rfl) ⟨1601123, by rfl⟩ : syracuseStep 2134831 = 3202247) B3202247
theorem B8221601 : Blo 1686043 8221601 := bstep (se 2 (by rfl) ⟨3083100, by rfl⟩ : syracuseStep 8221601 = 6166201) B6166201
theorem B1897447 : Blo 1686043 1897447 := bstep (se 1 (by rfl) ⟨1423085, by rfl⟩ : syracuseStep 1897447 = 2846171) B2846171
theorem B5690465 : Blo 1686043 5690465 := bstep (se 2 (by rfl) ⟨2133924, by rfl⟩ : syracuseStep 5690465 = 4267849) B4267849
theorem B4805831 : Blo 1686043 4805831 := bstep (se 1 (by rfl) ⟨3604373, by rfl⟩ : syracuseStep 4805831 = 7208747) B7208747
theorem B10810583 : Blo 1686043 10810583 := bstep (se 1 (by rfl) ⟨8107937, by rfl⟩ : syracuseStep 10810583 = 16215875) B16215875
theorem B4109555 : Blo 1686043 4109555 := bstep (se 1 (by rfl) ⟨3082166, by rfl⟩ : syracuseStep 4109555 = 6164333) B6164333
theorem B12154151 : Blo 1686043 12154151 := bstep (se 1 (by rfl) ⟨9115613, by rfl⟩ : syracuseStep 12154151 = 18231227) B18231227
theorem B3421639 : Blo 1686043 3421639 := bstep (se 1 (by rfl) ⟨2566229, by rfl⟩ : syracuseStep 3421639 = 5132459) B5132459
theorem B51942977 : Blo 1686043 51942977 := bstep (se 2 (by rfl) ⟨19478616, by rfl⟩ : syracuseStep 51942977 = 38957233) B38957233
theorem B2848351 : Blo 1686043 2848351 := bstep (se 1 (by rfl) ⟨2136263, by rfl⟩ : syracuseStep 2848351 = 4272527) B4272527
theorem B8107705 : Blo 1686043 8107705 := bstep (se 2 (by rfl) ⟨3040389, by rfl⟩ : syracuseStep 8107705 = 6080779) B6080779
theorem B2529065 : Blo 1686043 2529065 := bstep (se 2 (by rfl) ⟨948399, by rfl⟩ : syracuseStep 2529065 = 1896799) B1896799
theorem B2529071 : Blo 1686043 2529071 := bstep (se 1 (by rfl) ⟨1896803, by rfl⟩ : syracuseStep 2529071 = 3793607) B3793607
theorem B5003063 : Blo 1686043 5003063 := bstep (se 1 (by rfl) ⟨3752297, by rfl⟩ : syracuseStep 5003063 = 7504595) B7504595
theorem B2848567 : Blo 1686043 2848567 := bstep (se 1 (by rfl) ⟨2136425, by rfl⟩ : syracuseStep 2848567 = 4272851) B4272851
theorem B16209953 : Blo 1686043 16209953 := bstep (se 2 (by rfl) ⟨6078732, by rfl⟩ : syracuseStep 16209953 = 12157465) B12157465
theorem B6404129 : Blo 1686043 6404129 := bstep (se 2 (by rfl) ⟨2401548, by rfl⟩ : syracuseStep 6404129 = 4803097) B4803097
theorem B7698617 : Blo 1686043 7698617 := bstep (se 2 (by rfl) ⟨2886981, by rfl⟩ : syracuseStep 7698617 = 5773963) B5773963
theorem B9115895 : Blo 1686043 9115895 := bstep (se 1 (by rfl) ⟨6836921, by rfl⟩ : syracuseStep 9115895 = 13673843) B13673843
theorem B2529545 : Blo 1686043 2529545 := bstep (se 2 (by rfl) ⟨948579, by rfl⟩ : syracuseStep 2529545 = 1897159) B1897159
theorem B3651913 : Blo 1686043 3651913 := bstep (se 2 (by rfl) ⟨1369467, by rfl⟩ : syracuseStep 3651913 = 2738935) B2738935
theorem B20511053 : Blo 1686043 20511053 := bstep (se 3 (by rfl) ⟨3845822, by rfl⟩ : syracuseStep 20511053 = 7691645) B7691645
theorem B36985177 : Blo 1686043 36985177 := bstep (se 2 (by rfl) ⟨13869441, by rfl⟩ : syracuseStep 36985177 = 27738883) B27738883
theorem B1800559 : Blo 1686043 1800559 := bstep (se 1 (by rfl) ⟨1350419, by rfl⟩ : syracuseStep 1800559 = 2700839) B2700839
theorem B2529647 : Blo 1686043 2529647 := bstep (se 1 (by rfl) ⟨1897235, by rfl⟩ : syracuseStep 2529647 = 3794471) B3794471
theorem B5691815 : Blo 1686043 5691815 := bstep (se 1 (by rfl) ⟨4268861, by rfl⟩ : syracuseStep 5691815 = 8537723) B8537723
theorem B4561363 : Blo 1686043 4561363 := bstep (se 1 (by rfl) ⟨3421022, by rfl⟩ : syracuseStep 4561363 = 6842045) B6842045
theorem B1686079 : Blo 1686043 1686079 := bstep (se 1 (by rfl) ⟨1264559, by rfl⟩ : syracuseStep 1686079 = 2529119) B2529119
theorem B1686087 : Blo 1686043 1686087 := bstep (se 1 (by rfl) ⟨1264565, by rfl⟩ : syracuseStep 1686087 = 2529131) B2529131
theorem B2529863 : Blo 1686043 2529863 := bstep (se 1 (by rfl) ⟨1897397, by rfl⟩ : syracuseStep 2529863 = 3794795) B3794795
theorem B20511305 : Blo 1686043 20511305 := bstep (se 2 (by rfl) ⟨7691739, by rfl⟩ : syracuseStep 20511305 = 15383479) B15383479
theorem B5691977 : Blo 1686043 5691977 := bstep (se 2 (by rfl) ⟨2134491, by rfl⟩ : syracuseStep 5691977 = 4268983) B4268983
theorem B2529899 : Blo 1686043 2529899 := bstep (se 1 (by rfl) ⟨1897424, by rfl⟩ : syracuseStep 2529899 = 3794849) B3794849
theorem B9607855 : Blo 1686043 9607855 := bstep (se 1 (by rfl) ⟨7205891, by rfl⟩ : syracuseStep 9607855 = 14411783) B14411783
theorem B1686239 : Blo 1686043 1686239 := bstep (se 1 (by rfl) ⟨1264679, by rfl⟩ : syracuseStep 1686239 = 2529359) B2529359
theorem B1686319 : Blo 1686043 1686319 := bstep (se 1 (by rfl) ⟨1264739, by rfl⟩ : syracuseStep 1686319 = 2529479) B2529479
theorem B2530127 : Blo 1686043 2530127 := bstep (se 1 (by rfl) ⟨1897595, by rfl⟩ : syracuseStep 2530127 = 3795191) B3795191
theorem B155876213 : Blo 1686043 155876213 := bstep (se 5 (by rfl) ⟨7306697, by rfl⟩ : syracuseStep 155876213 = 14613395) B14613395
theorem B7207805 : Blo 1686043 7207805 := bstep (se 3 (by rfl) ⟨1351463, by rfl⟩ : syracuseStep 7207805 = 2702927) B2702927
theorem B12155791 : Blo 1686043 12155791 := bstep (se 1 (by rfl) ⟨9116843, by rfl⟩ : syracuseStep 12155791 = 18233687) B18233687
theorem B1686427 : Blo 1686043 1686427 := bstep (se 1 (by rfl) ⟨1264820, by rfl⟩ : syracuseStep 1686427 = 2529641) B2529641
theorem B1686479 : Blo 1686043 1686479 := bstep (se 1 (by rfl) ⟨1264859, by rfl⟩ : syracuseStep 1686479 = 2529719) B2529719
theorem B4561883 : Blo 1686043 4561883 := bstep (se 1 (by rfl) ⟨3421412, by rfl⟩ : syracuseStep 4561883 = 6842825) B6842825
theorem B1686503 : Blo 1686043 1686503 := bstep (se 1 (by rfl) ⟨1264877, by rfl⟩ : syracuseStep 1686503 = 2529755) B2529755
theorem B2702479 : Blo 1686043 2702479 := bstep (se 1 (by rfl) ⟨2026859, by rfl⟩ : syracuseStep 2702479 = 4053719) B4053719
theorem B48626851 : Blo 1686043 48626851 := bstep (se 1 (by rfl) ⟨36470138, by rfl⟩ : syracuseStep 48626851 = 72940277) B72940277
theorem B9239741 : Blo 1686043 9239741 := bstep (se 3 (by rfl) ⟨1732451, by rfl⟩ : syracuseStep 9239741 = 3464903) B3464903
theorem B9608381 : Blo 1686043 9608381 := bstep (se 3 (by rfl) ⟨1801571, by rfl⟩ : syracuseStep 9608381 = 3603143) B3603143
theorem B1801435 : Blo 1686043 1801435 := bstep (se 1 (by rfl) ⟨1351076, by rfl⟩ : syracuseStep 1801435 = 2702153) B2702153
theorem B2530523 : Blo 1686043 2530523 := bstep (se 1 (by rfl) ⟨1897892, by rfl⟩ : syracuseStep 2530523 = 3795785) B3795785
theorem B1686815 : Blo 1686043 1686815 := bstep (se 1 (by rfl) ⟨1265111, by rfl⟩ : syracuseStep 1686815 = 2530223) B2530223
theorem B8543555 : Blo 1686043 8543555 := bstep (se 1 (by rfl) ⟨6407666, by rfl⟩ : syracuseStep 8543555 = 12815333) B12815333
theorem B1686875 : Blo 1686043 1686875 := bstep (se 1 (by rfl) ⟨1265156, by rfl⟩ : syracuseStep 1686875 = 2530313) B2530313
theorem B1686895 : Blo 1686043 1686895 := bstep (se 1 (by rfl) ⟨1265171, by rfl⟩ : syracuseStep 1686895 = 2530343) B2530343
theorem B2530697 : Blo 1686043 2530697 := bstep (se 2 (by rfl) ⟨949011, by rfl⟩ : syracuseStep 2530697 = 1898023) B1898023
theorem B1686951 : Blo 1686043 1686951 := bstep (se 1 (by rfl) ⟨1265213, by rfl⟩ : syracuseStep 1686951 = 2530427) B2530427
theorem B1687035 : Blo 1686043 1687035 := bstep (se 1 (by rfl) ⟨1265276, by rfl⟩ : syracuseStep 1687035 = 2530553) B2530553
theorem B21609989 : Blo 1686043 21609989 := bstep (se 4 (by rfl) ⟨2025936, by rfl⟩ : syracuseStep 21609989 = 4051873) B4051873
theorem B15392267 : Blo 1686043 15392267 := bstep (se 1 (by rfl) ⟨11544200, by rfl⟩ : syracuseStep 15392267 = 23088401) B23088401
theorem B7208473 : Blo 1686043 7208473 := bstep (se 2 (by rfl) ⟨2703177, by rfl⟩ : syracuseStep 7208473 = 5406355) B5406355
theorem B1687103 : Blo 1686043 1687103 := bstep (se 1 (by rfl) ⟨1265327, by rfl⟩ : syracuseStep 1687103 = 2530655) B2530655
theorem B1687111 : Blo 1686043 1687111 := bstep (se 1 (by rfl) ⟨1265333, by rfl⟩ : syracuseStep 1687111 = 2530667) B2530667
theorem B14605919 : Blo 1686043 14605919 := bstep (se 1 (by rfl) ⟨10954439, by rfl⟩ : syracuseStep 14605919 = 21908879) B21908879
theorem B8216225 : Blo 1686043 8216225 := bstep (se 2 (by rfl) ⟨3081084, by rfl⟩ : syracuseStep 8216225 = 6162169) B6162169
theorem B1687263 : Blo 1686043 1687263 := bstep (se 1 (by rfl) ⟨1265447, by rfl⟩ : syracuseStep 1687263 = 2530895) B2530895
theorem B2531051 : Blo 1686043 2531051 := bstep (se 1 (by rfl) ⟨1898288, by rfl⟩ : syracuseStep 2531051 = 3796577) B3796577
theorem B8544041 : Blo 1686043 8544041 := bstep (se 2 (by rfl) ⟨3204015, by rfl⟩ : syracuseStep 8544041 = 6408031) B6408031
theorem B1687343 : Blo 1686043 1687343 := bstep (se 1 (by rfl) ⟨1265507, by rfl⟩ : syracuseStep 1687343 = 2531015) B2531015
theorem B3604279 : Blo 1686043 3604279 := bstep (se 1 (by rfl) ⟨2703209, by rfl⟩ : syracuseStep 3604279 = 5406419) B5406419
theorem B1687451 : Blo 1686043 1687451 := bstep (se 1 (by rfl) ⟨1265588, by rfl⟩ : syracuseStep 1687451 = 2531177) B2531177
theorem B1687503 : Blo 1686043 1687503 := bstep (se 1 (by rfl) ⟨1265627, by rfl⟩ : syracuseStep 1687503 = 2531255) B2531255
theorem B2531279 : Blo 1686043 2531279 := bstep (se 1 (by rfl) ⟨1898459, by rfl⟩ : syracuseStep 2531279 = 3796919) B3796919
theorem B1687527 : Blo 1686043 1687527 := bstep (se 1 (by rfl) ⟨1265645, by rfl⟩ : syracuseStep 1687527 = 2531291) B2531291
theorem B41050127 : Blo 1686043 41050127 := bstep (se 1 (by rfl) ⟨30787595, by rfl⟩ : syracuseStep 41050127 = 61575191) B61575191
theorem B6840359 : Blo 1686043 6840359 := bstep (se 1 (by rfl) ⟨5130269, by rfl⟩ : syracuseStep 6840359 = 10260539) B10260539
theorem B1687783 : Blo 1686043 1687783 := bstep (se 1 (by rfl) ⟨1265837, by rfl⟩ : syracuseStep 1687783 = 2531675) B2531675
theorem B2531615 : Blo 1686043 2531615 := bstep (se 1 (by rfl) ⟨1898711, by rfl⟩ : syracuseStep 2531615 = 3797423) B3797423
theorem B2531639 : Blo 1686043 2531639 := bstep (se 1 (by rfl) ⟨1898729, by rfl⟩ : syracuseStep 2531639 = 3797459) B3797459
theorem B2924927 : Blo 1686043 2924927 := bstep (se 1 (by rfl) ⟨2193695, by rfl⟩ : syracuseStep 2924927 = 4387391) B4387391
theorem B2531711 : Blo 1686043 2531711 := bstep (se 1 (by rfl) ⟨1898783, by rfl⟩ : syracuseStep 2531711 = 3797567) B3797567
theorem B1687935 : Blo 1686043 1687935 := bstep (se 1 (by rfl) ⟨1265951, by rfl⟩ : syracuseStep 1687935 = 2531903) B2531903
theorem B5407175 : Blo 1686043 5407175 := bstep (se 1 (by rfl) ⟨4055381, by rfl⟩ : syracuseStep 5407175 = 8110763) B8110763
theorem B2531783 : Blo 1686043 2531783 := bstep (se 1 (by rfl) ⟨1898837, by rfl⟩ : syracuseStep 2531783 = 3797675) B3797675
theorem B1688015 : Blo 1686043 1688015 := bstep (se 1 (by rfl) ⟨1266011, by rfl⟩ : syracuseStep 1688015 = 2532023) B2532023
theorem B7799291 : Blo 1686043 7799291 := bstep (se 1 (by rfl) ⟨5849468, by rfl⟩ : syracuseStep 7799291 = 11698937) B11698937
theorem B5481067 : Blo 1686043 5481067 := bstep (se 1 (by rfl) ⟨4110800, by rfl⟩ : syracuseStep 5481067 = 8221601) B8221601
theorem B8536751 : Blo 1686043 8536751 := bstep (se 1 (by rfl) ⟨6402563, by rfl⟩ : syracuseStep 8536751 = 12805127) B12805127
theorem B10814147 : Blo 1686043 10814147 := bstep (se 1 (by rfl) ⟨8110610, by rfl⟩ : syracuseStep 10814147 = 16221221) B16221221
theorem B3793643 : Blo 1686043 3793643 := bstep (se 1 (by rfl) ⟨2845232, by rfl⟩ : syracuseStep 3793643 = 5690465) B5690465
theorem B3203849 : Blo 1686043 3203849 := bstep (se 2 (by rfl) ⟨1201443, by rfl⟩ : syracuseStep 3203849 = 2402887) B2402887
theorem B3203887 : Blo 1686043 3203887 := bstep (se 1 (by rfl) ⟨2402915, by rfl⟩ : syracuseStep 3203887 = 4805831) B4805831
theorem B8102767 : Blo 1686043 8102767 := bstep (se 1 (by rfl) ⟨6077075, by rfl⟩ : syracuseStep 8102767 = 12154151) B12154151
theorem B34628651 : Blo 1686043 34628651 := bstep (se 1 (by rfl) ⟨25971488, by rfl⟩ : syracuseStep 34628651 = 51942977) B51942977
theorem B5694569 : Blo 1686043 5694569 := bstep (se 2 (by rfl) ⟨2135463, by rfl⟩ : syracuseStep 5694569 = 4270927) B4270927
theorem B12158099 : Blo 1686043 12158099 := bstep (se 1 (by rfl) ⟨9118574, by rfl⟩ : syracuseStep 12158099 = 18237149) B18237149
theorem B11101373 : Blo 1686043 11101373 := bstep (se 3 (by rfl) ⟨2081507, by rfl⟩ : syracuseStep 11101373 = 4163015) B4163015
theorem B3335375 : Blo 1686043 3335375 := bstep (se 1 (by rfl) ⟨2501531, by rfl⟩ : syracuseStep 3335375 = 5003063) B5003063
theorem B10257623 : Blo 1686043 10257623 := bstep (se 1 (by rfl) ⟨7693217, by rfl⟩ : syracuseStep 10257623 = 15386435) B15386435
theorem B28829033 : Blo 1686043 28829033 := bstep (se 2 (by rfl) ⟨10810887, by rfl⟩ : syracuseStep 28829033 = 21621775) B21621775
theorem B10806635 : Blo 1686043 10806635 := bstep (se 1 (by rfl) ⟨8104976, by rfl⟩ : syracuseStep 10806635 = 16209953) B16209953
theorem B4269419 : Blo 1686043 4269419 := bstep (se 1 (by rfl) ⟨3202064, by rfl⟩ : syracuseStep 4269419 = 6404129) B6404129
theorem B12805613 : Blo 1686043 12805613 := bstep (se 3 (by rfl) ⟨2401052, by rfl⟩ : syracuseStep 12805613 = 4802105) B4802105
theorem B13674035 : Blo 1686043 13674035 := bstep (se 1 (by rfl) ⟨10255526, by rfl⟩ : syracuseStep 13674035 = 20511053) B20511053
theorem B3794543 : Blo 1686043 3794543 := bstep (se 1 (by rfl) ⟨2845907, by rfl⟩ : syracuseStep 3794543 = 5691815) B5691815
theorem B2401913 : Blo 1686043 2401913 := bstep (se 2 (by rfl) ⟨900717, by rfl⟩ : syracuseStep 2401913 = 1801435) B1801435
theorem B13674203 : Blo 1686043 13674203 := bstep (se 1 (by rfl) ⟨10255652, by rfl⟩ : syracuseStep 13674203 = 20511305) B20511305
theorem B3794651 : Blo 1686043 3794651 := bstep (se 1 (by rfl) ⟨2845988, by rfl⟩ : syracuseStep 3794651 = 5691977) B5691977
theorem B103917475 : Blo 1686043 103917475 := bstep (se 1 (by rfl) ⟨77938106, by rfl⟩ : syracuseStep 103917475 = 155876213) B155876213
theorem B9602981 : Blo 1686043 9602981 := bstep (se 4 (by rfl) ⟨900279, by rfl⟩ : syracuseStep 9602981 = 1800559) B1800559
theorem B5695433 : Blo 1686043 5695433 := bstep (se 2 (by rfl) ⟨2135787, by rfl⟩ : syracuseStep 5695433 = 4271575) B4271575
theorem B3041255 : Blo 1686043 3041255 := bstep (se 1 (by rfl) ⟨2280941, by rfl⟩ : syracuseStep 3041255 = 4561883) B4561883
theorem B9611297 : Blo 1686043 9611297 := bstep (se 2 (by rfl) ⟨3604236, by rfl⟩ : syracuseStep 9611297 = 7208473) B7208473
theorem B5695703 : Blo 1686043 5695703 := bstep (se 1 (by rfl) ⟨4271777, by rfl⟩ : syracuseStep 5695703 = 8543555) B8543555
theorem B19220813 : Blo 1686043 19220813 := bstep (se 3 (by rfl) ⟨3603902, by rfl⟩ : syracuseStep 19220813 = 7207805) B7207805
theorem B5696027 : Blo 1686043 5696027 := bstep (se 1 (by rfl) ⟨4272020, by rfl⟩ : syracuseStep 5696027 = 8544041) B8544041
theorem B9603755 : Blo 1686043 9603755 := bstep (se 1 (by rfl) ⟨7202816, by rfl⟩ : syracuseStep 9603755 = 14405633) B14405633
theorem B3795767 : Blo 1686043 3795767 := bstep (se 1 (by rfl) ⟨2846825, by rfl⟩ : syracuseStep 3795767 = 5693651) B5693651
theorem B4803563 : Blo 1686043 4803563 := bstep (se 1 (by rfl) ⟨3602672, by rfl⟩ : syracuseStep 4803563 = 7205345) B7205345
theorem B3795947 : Blo 1686043 3795947 := bstep (se 1 (by rfl) ⟨2846960, by rfl⟩ : syracuseStep 3795947 = 5693921) B5693921
theorem B4869217 : Blo 1686043 4869217 := bstep (se 2 (by rfl) ⟨1825956, by rfl⟩ : syracuseStep 4869217 = 3651913) B3651913
theorem B24317117 : Blo 1686043 24317117 := bstep (se 3 (by rfl) ⟨4559459, by rfl⟩ : syracuseStep 24317117 = 9118919) B9118919
theorem B6491335 : Blo 1686043 6491335 := bstep (se 1 (by rfl) ⟨4868501, by rfl⟩ : syracuseStep 6491335 = 9737003) B9737003
theorem B6081817 : Blo 1686043 6081817 := bstep (se 2 (by rfl) ⟨2280681, by rfl⟩ : syracuseStep 6081817 = 4561363) B4561363
theorem B2846063 : Blo 1686043 2846063 := bstep (se 1 (by rfl) ⟨2134547, by rfl⟩ : syracuseStep 2846063 = 4269095) B4269095
theorem B5696891 : Blo 1686043 5696891 := bstep (se 1 (by rfl) ⟨4272668, by rfl⟩ : syracuseStep 5696891 = 8545337) B8545337
theorem B2846299 : Blo 1686043 2846299 := bstep (se 1 (by rfl) ⟨2134724, by rfl⟩ : syracuseStep 2846299 = 4269449) B4269449
theorem B2846441 : Blo 1686043 2846441 := bstep (se 2 (by rfl) ⟨1067415, by rfl⟩ : syracuseStep 2846441 = 2134831) B2134831
theorem B3796775 : Blo 1686043 3796775 := bstep (se 1 (by rfl) ⟨2847581, by rfl⟩ : syracuseStep 3796775 = 5695163) B5695163
theorem B21630797 : Blo 1686043 21630797 := bstep (se 3 (by rfl) ⟨4055774, by rfl⟩ : syracuseStep 21630797 = 8111549) B8111549
theorem B16207721 : Blo 1686043 16207721 := bstep (se 2 (by rfl) ⟨6077895, by rfl⟩ : syracuseStep 16207721 = 12155791) B12155791
theorem B12808043 : Blo 1686043 12808043 := bstep (se 1 (by rfl) ⟨9606032, by rfl⟩ : syracuseStep 12808043 = 19212065) B19212065
theorem B4272011 : Blo 1686043 4272011 := bstep (se 1 (by rfl) ⟨3204008, by rfl⟩ : syracuseStep 4272011 = 6408017) B6408017
theorem B34639825 : Blo 1686043 34639825 := bstep (se 2 (by rfl) ⟨12989934, by rfl⟩ : syracuseStep 34639825 = 25979869) B25979869
theorem B19206233 : Blo 1686043 19206233 := bstep (se 2 (by rfl) ⟨7202337, by rfl⟩ : syracuseStep 19206233 = 14404675) B14404675
theorem B5132411 : Blo 1686043 5132411 := bstep (se 1 (by rfl) ⟨3849308, by rfl⟩ : syracuseStep 5132411 = 7698617) B7698617
theorem B64835801 : Blo 1686043 64835801 := bstep (se 2 (by rfl) ⟨24313425, by rfl⟩ : syracuseStep 64835801 = 48626851) B48626851
theorem B3846455 : Blo 1686043 3846455 := bstep (se 1 (by rfl) ⟨2884841, by rfl⟩ : syracuseStep 3846455 = 5769683) B5769683
theorem B2847467 : Blo 1686043 2847467 := bstep (se 1 (by rfl) ⟨2135600, by rfl⟩ : syracuseStep 2847467 = 4271201) B4271201
theorem B56996599 : Blo 1686043 56996599 := bstep (se 1 (by rfl) ⟨42747449, by rfl⟩ : syracuseStep 56996599 = 85494899) B85494899
theorem B3797801 : Blo 1686043 3797801 := bstep (se 2 (by rfl) ⟨1424175, by rfl⟩ : syracuseStep 3797801 = 2848351) B2848351
theorem B10810273 : Blo 1686043 10810273 := bstep (se 2 (by rfl) ⟨4053852, by rfl⟩ : syracuseStep 10810273 = 8107705) B8107705
theorem B14406659 : Blo 1686043 14406659 := bstep (se 1 (by rfl) ⟨10804994, by rfl⟩ : syracuseStep 14406659 = 21609989) B21609989
theorem B10261511 : Blo 1686043 10261511 := bstep (se 1 (by rfl) ⟨7696133, by rfl⟩ : syracuseStep 10261511 = 15392267) B15392267
theorem B3798071 : Blo 1686043 3798071 := bstep (se 1 (by rfl) ⟨2848553, by rfl⟩ : syracuseStep 3798071 = 5697107) B5697107
theorem B9737279 : Blo 1686043 9737279 := bstep (se 1 (by rfl) ⟨7302959, by rfl⟩ : syracuseStep 9737279 = 14605919) B14605919
theorem B4805705 : Blo 1686043 4805705 := bstep (se 2 (by rfl) ⟨1802139, by rfl⟩ : syracuseStep 4805705 = 3604279) B3604279
theorem B3798089 : Blo 1686043 3798089 := bstep (se 2 (by rfl) ⟨1424283, by rfl⟩ : syracuseStep 3798089 = 2848567) B2848567
theorem B5477483 : Blo 1686043 5477483 := bstep (se 1 (by rfl) ⟨4108112, by rfl⟩ : syracuseStep 5477483 = 8216225) B8216225
theorem B2847919 : Blo 1686043 2847919 := bstep (se 1 (by rfl) ⟨2135939, by rfl⟩ : syracuseStep 2847919 = 4271879) B4271879
theorem B152040719 : Blo 1686043 152040719 := bstep (se 1 (by rfl) ⟨114030539, by rfl⟩ : syracuseStep 152040719 = 228061079) B228061079
theorem B4052315 : Blo 1686043 4052315 := bstep (se 1 (by rfl) ⟨3039236, by rfl⟩ : syracuseStep 4052315 = 6078473) B6078473
theorem B20510279 : Blo 1686043 20510279 := bstep (se 1 (by rfl) ⟨15382709, by rfl⟩ : syracuseStep 20510279 = 30765419) B30765419
theorem B5690951 : Blo 1686043 5690951 := bstep (se 1 (by rfl) ⟨4268213, by rfl⟩ : syracuseStep 5690951 = 8536427) B8536427
theorem B1898095 : Blo 1686043 1898095 := bstep (se 1 (by rfl) ⟨1423571, by rfl⟩ : syracuseStep 1898095 = 2847143) B2847143
theorem B2848439 : Blo 1686043 2848439 := bstep (se 1 (by rfl) ⟨2136329, by rfl⟩ : syracuseStep 2848439 = 4272659) B4272659
theorem B1898203 : Blo 1686043 1898203 := bstep (se 1 (by rfl) ⟨1423652, by rfl⟩ : syracuseStep 1898203 = 2847305) B2847305
theorem B2135803 : Blo 1686043 2135803 := bstep (se 1 (by rfl) ⟨1601852, by rfl⟩ : syracuseStep 2135803 = 3203705) B3203705
theorem B9606923 : Blo 1686043 9606923 := bstep (se 1 (by rfl) ⟨7205192, by rfl⟩ : syracuseStep 9606923 = 14410385) B14410385
theorem B49313569 : Blo 1686043 49313569 := bstep (se 2 (by rfl) ⟨18492588, by rfl⟩ : syracuseStep 49313569 = 36985177) B36985177
theorem B2529161 : Blo 1686043 2529161 := bstep (se 2 (by rfl) ⟨948435, by rfl⟩ : syracuseStep 2529161 = 1896871) B1896871
theorem B5404573 : Blo 1686043 5404573 := bstep (se 3 (by rfl) ⟨1013357, by rfl⟩ : syracuseStep 5404573 = 2026715) B2026715
theorem B10958813 : Blo 1686043 10958813 := bstep (se 3 (by rfl) ⟨2054777, by rfl⟩ : syracuseStep 10958813 = 4109555) B4109555
theorem B2529263 : Blo 1686043 2529263 := bstep (se 1 (by rfl) ⟨1896947, by rfl⟩ : syracuseStep 2529263 = 3793895) B3793895
theorem B7207055 : Blo 1686043 7207055 := bstep (se 1 (by rfl) ⟨5405291, by rfl⟩ : syracuseStep 7207055 = 10810583) B10810583
theorem B12810473 : Blo 1686043 12810473 := bstep (se 2 (by rfl) ⟨4803927, by rfl⟩ : syracuseStep 12810473 = 9607855) B9607855
theorem B2529515 : Blo 1686043 2529515 := bstep (se 1 (by rfl) ⟨1897136, by rfl⟩ : syracuseStep 2529515 = 3794273) B3794273
theorem B2529575 : Blo 1686043 2529575 := bstep (se 1 (by rfl) ⟨1897181, by rfl⟩ : syracuseStep 2529575 = 3794363) B3794363
theorem B2529659 : Blo 1686043 2529659 := bstep (se 1 (by rfl) ⟨1897244, by rfl⟩ : syracuseStep 2529659 = 3794489) B3794489
theorem B5691923 : Blo 1686043 5691923 := bstep (se 1 (by rfl) ⟨4268942, by rfl⟩ : syracuseStep 5691923 = 8537885) B8537885
theorem B1686043 : Blo 1686043 1686043 := bstep (se 1 (by rfl) ⟨1264532, by rfl⟩ : syracuseStep 1686043 = 2529065) B2529065
theorem B1686047 : Blo 1686043 1686047 := bstep (se 1 (by rfl) ⟨1264535, by rfl⟩ : syracuseStep 1686047 = 2529071) B2529071
theorem B21609017 : Blo 1686043 21609017 := bstep (se 2 (by rfl) ⟨8103381, by rfl⟩ : syracuseStep 21609017 = 16206763) B16206763
theorem B2529929 : Blo 1686043 2529929 := bstep (se 2 (by rfl) ⟨948723, by rfl⟩ : syracuseStep 2529929 = 1897447) B1897447
theorem B30792413 : Blo 1686043 30792413 := bstep (se 3 (by rfl) ⟨5773577, by rfl⟩ : syracuseStep 30792413 = 11547155) B11547155
theorem B2530103 : Blo 1686043 2530103 := bstep (se 1 (by rfl) ⟨1897577, by rfl⟩ : syracuseStep 2530103 = 3795155) B3795155
theorem B6077263 : Blo 1686043 6077263 := bstep (se 1 (by rfl) ⟨4557947, by rfl⟩ : syracuseStep 6077263 = 9115895) B9115895
theorem B1686363 : Blo 1686043 1686363 := bstep (se 1 (by rfl) ⟨1264772, by rfl⟩ : syracuseStep 1686363 = 2529545) B2529545
theorem B2530139 : Blo 1686043 2530139 := bstep (se 1 (by rfl) ⟨1897604, by rfl⟩ : syracuseStep 2530139 = 3795209) B3795209
theorem B3603305 : Blo 1686043 3603305 := bstep (se 2 (by rfl) ⟨1351239, by rfl⟩ : syracuseStep 3603305 = 2702479) B2702479
theorem B1686431 : Blo 1686043 1686431 := bstep (se 1 (by rfl) ⟨1264823, by rfl⟩ : syracuseStep 1686431 = 2529647) B2529647
theorem B2530283 : Blo 1686043 2530283 := bstep (se 1 (by rfl) ⟨1897712, by rfl⟩ : syracuseStep 2530283 = 3795425) B3795425
theorem B1686575 : Blo 1686043 1686575 := bstep (se 1 (by rfl) ⟨1264931, by rfl⟩ : syracuseStep 1686575 = 2529863) B2529863
theorem B1686599 : Blo 1686043 1686599 := bstep (se 1 (by rfl) ⟨1264949, by rfl⟩ : syracuseStep 1686599 = 2529899) B2529899
theorem B2530487 : Blo 1686043 2530487 := bstep (se 1 (by rfl) ⟨1897865, by rfl⟩ : syracuseStep 2530487 = 3795731) B3795731
theorem B1686751 : Blo 1686043 1686751 := bstep (se 1 (by rfl) ⟨1265063, by rfl⟩ : syracuseStep 1686751 = 2530127) B2530127
theorem B4562185 : Blo 1686043 4562185 := bstep (se 2 (by rfl) ⟨1710819, by rfl⟩ : syracuseStep 4562185 = 3421639) B3421639
theorem B2530727 : Blo 1686043 2530727 := bstep (se 1 (by rfl) ⟨1898045, by rfl⟩ : syracuseStep 2530727 = 3796091) B3796091
theorem B6159827 : Blo 1686043 6159827 := bstep (se 1 (by rfl) ⟨4619870, by rfl⟩ : syracuseStep 6159827 = 9239741) B9239741
theorem B6405587 : Blo 1686043 6405587 := bstep (se 1 (by rfl) ⟨4804190, by rfl⟩ : syracuseStep 6405587 = 9608381) B9608381
theorem B1687015 : Blo 1686043 1687015 := bstep (se 1 (by rfl) ⟨1265261, by rfl⟩ : syracuseStep 1687015 = 2530523) B2530523
theorem B2530811 : Blo 1686043 2530811 := bstep (se 1 (by rfl) ⟨1898108, by rfl⟩ : syracuseStep 2530811 = 3796217) B3796217
theorem B1687131 : Blo 1686043 1687131 := bstep (se 1 (by rfl) ⟨1265348, by rfl⟩ : syracuseStep 1687131 = 2530697) B2530697
theorem B2530907 : Blo 1686043 2530907 := bstep (se 1 (by rfl) ⟨1898180, by rfl⟩ : syracuseStep 2530907 = 3796361) B3796361
theorem B2530991 : Blo 1686043 2530991 := bstep (se 1 (by rfl) ⟨1898243, by rfl⟩ : syracuseStep 2530991 = 3796487) B3796487
theorem B92389085 : Blo 1686043 92389085 := bstep (se 3 (by rfl) ⟨17322953, by rfl⟩ : syracuseStep 92389085 = 34645907) B34645907
theorem B2531111 : Blo 1686043 2531111 := bstep (se 1 (by rfl) ⟨1898333, by rfl⟩ : syracuseStep 2531111 = 3796667) B3796667
theorem B1687367 : Blo 1686043 1687367 := bstep (se 1 (by rfl) ⟨1265525, by rfl⟩ : syracuseStep 1687367 = 2531051) B2531051
theorem B2531195 : Blo 1686043 2531195 := bstep (se 1 (by rfl) ⟨1898396, by rfl⟩ : syracuseStep 2531195 = 3796793) B3796793
theorem B1687519 : Blo 1686043 1687519 := bstep (se 1 (by rfl) ⟨1265639, by rfl⟩ : syracuseStep 1687519 = 2531279) B2531279
theorem B12804155 : Blo 1686043 12804155 := bstep (se 1 (by rfl) ⟨9603116, by rfl⟩ : syracuseStep 12804155 = 19206233) B19206233
theorem B1687743 : Blo 1686043 1687743 := bstep (se 1 (by rfl) ⟨1265807, by rfl⟩ : syracuseStep 1687743 = 2531615) B2531615
theorem B2564303 : Blo 1686043 2564303 := bstep (se 1 (by rfl) ⟨1923227, by rfl⟩ : syracuseStep 2564303 = 3846455) B3846455
theorem B1687759 : Blo 1686043 1687759 := bstep (se 1 (by rfl) ⟨1265819, by rfl⟩ : syracuseStep 1687759 = 2531639) B2531639
theorem B1949951 : Blo 1686043 1949951 := bstep (se 1 (by rfl) ⟨1462463, by rfl⟩ : syracuseStep 1949951 = 2924927) B2924927
theorem B1687807 : Blo 1686043 1687807 := bstep (se 1 (by rfl) ⟨1265855, by rfl⟩ : syracuseStep 1687807 = 2531711) B2531711
theorem B1687855 : Blo 1686043 1687855 := bstep (se 1 (by rfl) ⟨1265891, by rfl⟩ : syracuseStep 1687855 = 2531783) B2531783
theorem B7209431 : Blo 1686043 7209431 := bstep (se 1 (by rfl) ⟨5407073, by rfl⟩ : syracuseStep 7209431 = 10814147) B10814147
theorem B25969157 : Blo 1686043 25969157 := bstep (se 4 (by rfl) ⟨2434608, by rfl⟩ : syracuseStep 25969157 = 4869217) B4869217
theorem B2531867 : Blo 1686043 2531867 := bstep (se 1 (by rfl) ⟨1898900, by rfl⟩ : syracuseStep 2531867 = 3797801) B3797801
theorem B6841007 : Blo 1686043 6841007 := bstep (se 1 (by rfl) ⟨5130755, by rfl⟩ : syracuseStep 6841007 = 10261511) B10261511
theorem B23085767 : Blo 1686043 23085767 := bstep (se 1 (by rfl) ⟨17314325, by rfl⟩ : syracuseStep 23085767 = 34628651) B34628651
theorem B2532047 : Blo 1686043 2532047 := bstep (se 1 (by rfl) ⟨1899035, by rfl⟩ : syracuseStep 2532047 = 3798071) B3798071
theorem B3203803 : Blo 1686043 3203803 := bstep (se 1 (by rfl) ⟨2402852, by rfl⟩ : syracuseStep 3203803 = 4805705) B4805705
theorem B2532059 : Blo 1686043 2532059 := bstep (se 1 (by rfl) ⟨1899044, by rfl⟩ : syracuseStep 2532059 = 3798089) B3798089
theorem B7308089 : Blo 1686043 7308089 := bstep (se 2 (by rfl) ⟨2740533, by rfl⟩ : syracuseStep 7308089 = 5481067) B5481067
theorem B101360479 : Blo 1686043 101360479 := bstep (se 1 (by rfl) ⟨76020359, by rfl⟩ : syracuseStep 101360479 = 152040719) B152040719
theorem B19219355 : Blo 1686043 19219355 := bstep (se 1 (by rfl) ⟨14414516, by rfl⟩ : syracuseStep 19219355 = 28829033) B28829033
theorem B10806173 : Blo 1686043 10806173 := bstep (se 3 (by rfl) ⟨2026157, by rfl⟩ : syracuseStep 10806173 = 4052315) B4052315
theorem B8537075 : Blo 1686043 8537075 := bstep (se 1 (by rfl) ⟨6402806, by rfl⟩ : syracuseStep 8537075 = 12805613) B12805613
theorem B13673519 : Blo 1686043 13673519 := bstep (se 1 (by rfl) ⟨10255139, by rfl⟩ : syracuseStep 13673519 = 20510279) B20510279
theorem B3793967 : Blo 1686043 3793967 := bstep (se 1 (by rfl) ⟨2845475, by rfl⟩ : syracuseStep 3793967 = 5690951) B5690951
theorem B8103017 : Blo 1686043 8103017 := bstep (se 2 (by rfl) ⟨3038631, by rfl⟩ : syracuseStep 8103017 = 6077263) B6077263
theorem B14419133 : Blo 1686043 14419133 := bstep (se 3 (by rfl) ⟨2703587, by rfl⟩ : syracuseStep 14419133 = 5407175) B5407175
theorem B16426205 : Blo 1686043 16426205 := bstep (se 3 (by rfl) ⟨3079913, by rfl⟩ : syracuseStep 16426205 = 6159827) B6159827
theorem B6407531 : Blo 1686043 6407531 := bstep (se 1 (by rfl) ⟨4805648, by rfl⟩ : syracuseStep 6407531 = 9611297) B9611297
theorem B36464093 : Blo 1686043 36464093 := bstep (se 3 (by rfl) ⟨6837017, by rfl⟩ : syracuseStep 36464093 = 13674035) B13674035
theorem B12813875 : Blo 1686043 12813875 := bstep (se 1 (by rfl) ⟨9610406, by rfl⟩ : syracuseStep 12813875 = 19220813) B19220813
theorem B3794615 : Blo 1686043 3794615 := bstep (se 1 (by rfl) ⟨2845961, by rfl⟩ : syracuseStep 3794615 = 5691923) B5691923
theorem B3795065 : Blo 1686043 3795065 := bstep (se 2 (by rfl) ⟨1423149, by rfl⟩ : syracuseStep 3795065 = 2846299) B2846299
theorem B4270391 : Blo 1686043 4270391 := bstep (se 1 (by rfl) ⟨3202793, by rfl⟩ : syracuseStep 4270391 = 6405587) B6405587
theorem B65751425 : Blo 1686043 65751425 := bstep (se 2 (by rfl) ⟨24656784, by rfl⟩ : syracuseStep 65751425 = 49313569) B49313569
theorem B14420531 : Blo 1686043 14420531 := bstep (se 1 (by rfl) ⟨10815398, by rfl⟩ : syracuseStep 14420531 = 21630797) B21630797
theorem B8538695 : Blo 1686043 8538695 := bstep (se 1 (by rfl) ⟨6404021, by rfl⟩ : syracuseStep 8538695 = 12808043) B12808043
theorem B43223867 : Blo 1686043 43223867 := bstep (se 1 (by rfl) ⟨32417900, by rfl⟩ : syracuseStep 43223867 = 64835801) B64835801
theorem B9604439 : Blo 1686043 9604439 := bstep (se 1 (by rfl) ⟨7203329, by rfl⟩ : syracuseStep 9604439 = 14406659) B14406659
theorem B6491519 : Blo 1686043 6491519 := bstep (se 1 (by rfl) ⟨4868639, by rfl⟩ : syracuseStep 6491519 = 9737279) B9737279
theorem B3796379 : Blo 1686043 3796379 := bstep (se 1 (by rfl) ⟨2847284, by rfl⟩ : syracuseStep 3796379 = 5694569) B5694569
theorem B8105399 : Blo 1686043 8105399 := bstep (se 1 (by rfl) ⟨6079049, by rfl⟩ : syracuseStep 8105399 = 12158099) B12158099
theorem B7400915 : Blo 1686043 7400915 := bstep (se 1 (by rfl) ⟨5550686, by rfl⟩ : syracuseStep 7400915 = 11101373) B11101373
theorem B7204423 : Blo 1686043 7204423 := bstep (se 1 (by rfl) ⟨5403317, by rfl⟩ : syracuseStep 7204423 = 10806635) B10806635
theorem B2846279 : Blo 1686043 2846279 := bstep (se 1 (by rfl) ⟨2134709, by rfl⟩ : syracuseStep 2846279 = 4269419) B4269419
theorem B4271849 : Blo 1686043 4271849 := bstep (se 2 (by rfl) ⟨1601943, by rfl⟩ : syracuseStep 4271849 = 3203887) B3203887
theorem B14413697 : Blo 1686043 14413697 := bstep (se 2 (by rfl) ⟨5405136, by rfl⟩ : syracuseStep 14413697 = 10810273) B10810273
theorem B6401987 : Blo 1686043 6401987 := bstep (se 1 (by rfl) ⟨4801490, by rfl⟩ : syracuseStep 6401987 = 9602981) B9602981
theorem B3796955 : Blo 1686043 3796955 := bstep (se 1 (by rfl) ⟨2847716, by rfl⟩ : syracuseStep 3796955 = 5695433) B5695433
theorem B2027503 : Blo 1686043 2027503 := bstep (se 1 (by rfl) ⟨1520627, by rfl⟩ : syracuseStep 2027503 = 3041255) B3041255
theorem B4804703 : Blo 1686043 4804703 := bstep (se 1 (by rfl) ⟨3603527, by rfl⟩ : syracuseStep 4804703 = 7207055) B7207055
theorem B3797135 : Blo 1686043 3797135 := bstep (se 1 (by rfl) ⟨2847851, by rfl⟩ : syracuseStep 3797135 = 5695703) B5695703
theorem B8540315 : Blo 1686043 8540315 := bstep (se 1 (by rfl) ⟨6405236, by rfl⟩ : syracuseStep 8540315 = 12810473) B12810473
theorem B3797225 : Blo 1686043 3797225 := bstep (se 2 (by rfl) ⟨1423959, by rfl⟩ : syracuseStep 3797225 = 2847919) B2847919
theorem B8655113 : Blo 1686043 8655113 := bstep (se 2 (by rfl) ⟨3245667, by rfl⟩ : syracuseStep 8655113 = 6491335) B6491335
theorem B6082913 : Blo 1686043 6082913 := bstep (se 2 (by rfl) ⟨2281092, by rfl⟩ : syracuseStep 6082913 = 4562185) B4562185
theorem B3797351 : Blo 1686043 3797351 := bstep (se 1 (by rfl) ⟨2848013, by rfl⟩ : syracuseStep 3797351 = 5696027) B5696027
theorem B14406011 : Blo 1686043 14406011 := bstep (se 1 (by rfl) ⟨10804508, by rfl⟩ : syracuseStep 14406011 = 21609017) B21609017
theorem B6402503 : Blo 1686043 6402503 := bstep (se 1 (by rfl) ⟨4801877, by rfl⟩ : syracuseStep 6402503 = 9603755) B9603755
theorem B82113101 : Blo 1686043 82113101 := bstep (se 3 (by rfl) ⟨15396206, by rfl⟩ : syracuseStep 82113101 = 30792413) B30792413
theorem B554226533 : Blo 1686043 554226533 := bstep (se 4 (by rfl) ⟨51958737, by rfl⟩ : syracuseStep 554226533 = 103917475) B103917475
theorem B1897375 : Blo 1686043 1897375 := bstep (se 1 (by rfl) ⟨1423031, by rfl⟩ : syracuseStep 1897375 = 2846063) B2846063
theorem B3797927 : Blo 1686043 3797927 := bstep (se 1 (by rfl) ⟨2848445, by rfl⟩ : syracuseStep 3797927 = 5696891) B5696891
theorem B2847737 : Blo 1686043 2847737 := bstep (se 2 (by rfl) ⟨1067901, by rfl⟩ : syracuseStep 2847737 = 2135803) B2135803
theorem B61592723 : Blo 1686043 61592723 := bstep (se 1 (by rfl) ⟨46194542, by rfl⟩ : syracuseStep 61592723 = 92389085) B92389085
theorem B1897627 : Blo 1686043 1897627 := bstep (se 1 (by rfl) ⟨1423220, by rfl⟩ : syracuseStep 1897627 = 2846441) B2846441
theorem B7206097 : Blo 1686043 7206097 := bstep (se 2 (by rfl) ⟨2702286, by rfl⟩ : syracuseStep 7206097 = 5404573) B5404573
theorem B2848007 : Blo 1686043 2848007 := bstep (se 1 (by rfl) ⟨2136005, by rfl⟩ : syracuseStep 2848007 = 4272011) B4272011
theorem B12809501 : Blo 1686043 12809501 := bstep (se 3 (by rfl) ⟨2401781, by rfl⟩ : syracuseStep 12809501 = 4803563) B4803563
theorem B27366751 : Blo 1686043 27366751 := bstep (se 1 (by rfl) ⟨20525063, by rfl⟩ : syracuseStep 27366751 = 41050127) B41050127
theorem B4560239 : Blo 1686043 4560239 := bstep (se 1 (by rfl) ⟨3420179, by rfl⟩ : syracuseStep 4560239 = 6840359) B6840359
theorem B3421607 : Blo 1686043 3421607 := bstep (se 1 (by rfl) ⟨2566205, by rfl⟩ : syracuseStep 3421607 = 5132411) B5132411
theorem B5199527 : Blo 1686043 5199527 := bstep (se 1 (by rfl) ⟨3899645, by rfl⟩ : syracuseStep 5199527 = 7799291) B7799291
theorem B5691167 : Blo 1686043 5691167 := bstep (se 1 (by rfl) ⟨4268375, by rfl⟩ : syracuseStep 5691167 = 8536751) B8536751
theorem B2529095 : Blo 1686043 2529095 := bstep (se 1 (by rfl) ⟨1896821, by rfl⟩ : syracuseStep 2529095 = 3793643) B3793643
theorem B1898311 : Blo 1686043 1898311 := bstep (se 1 (by rfl) ⟨1423733, by rfl⟩ : syracuseStep 1898311 = 2847467) B2847467
theorem B2135899 : Blo 1686043 2135899 := bstep (se 1 (by rfl) ⟨1601924, by rfl⟩ : syracuseStep 2135899 = 3203849) B3203849
theorem B8894333 : Blo 1686043 8894333 := bstep (se 3 (by rfl) ⟨1667687, by rfl⟩ : syracuseStep 8894333 = 3335375) B3335375
theorem B3651655 : Blo 1686043 3651655 := bstep (se 1 (by rfl) ⟨2738741, by rfl⟩ : syracuseStep 3651655 = 5477483) B5477483
theorem B6838415 : Blo 1686043 6838415 := bstep (se 1 (by rfl) ⟨5128811, by rfl⟩ : syracuseStep 6838415 = 10257623) B10257623
theorem B75995465 : Blo 1686043 75995465 := bstep (se 2 (by rfl) ⟨28498299, by rfl⟩ : syracuseStep 75995465 = 56996599) B56996599
theorem B2529695 : Blo 1686043 2529695 := bstep (se 1 (by rfl) ⟨1897271, by rfl⟩ : syracuseStep 2529695 = 3794543) B3794543
theorem B1898959 : Blo 1686043 1898959 := bstep (se 1 (by rfl) ⟨1424219, by rfl⟩ : syracuseStep 1898959 = 2848439) B2848439
theorem B9116135 : Blo 1686043 9116135 := bstep (se 1 (by rfl) ⟨6837101, by rfl⟩ : syracuseStep 9116135 = 13674203) B13674203
theorem B2529767 : Blo 1686043 2529767 := bstep (se 1 (by rfl) ⟨1897325, by rfl⟩ : syracuseStep 2529767 = 3794651) B3794651
theorem B10803689 : Blo 1686043 10803689 := bstep (se 2 (by rfl) ⟨4051383, by rfl⟩ : syracuseStep 10803689 = 8102767) B8102767
theorem B6404615 : Blo 1686043 6404615 := bstep (se 1 (by rfl) ⟨4803461, by rfl⟩ : syracuseStep 6404615 = 9606923) B9606923
theorem B1686107 : Blo 1686043 1686107 := bstep (se 1 (by rfl) ⟨1264580, by rfl⟩ : syracuseStep 1686107 = 2529161) B2529161
theorem B7305875 : Blo 1686043 7305875 := bstep (se 1 (by rfl) ⟨5479406, by rfl⟩ : syracuseStep 7305875 = 10958813) B10958813
theorem B1686175 : Blo 1686043 1686175 := bstep (se 1 (by rfl) ⟨1264631, by rfl⟩ : syracuseStep 1686175 = 2529263) B2529263
theorem B1686343 : Blo 1686043 1686343 := bstep (se 1 (by rfl) ⟨1264757, by rfl⟩ : syracuseStep 1686343 = 2529515) B2529515
theorem B1686383 : Blo 1686043 1686383 := bstep (se 1 (by rfl) ⟨1264787, by rfl⟩ : syracuseStep 1686383 = 2529575) B2529575
theorem B1686439 : Blo 1686043 1686439 := bstep (se 1 (by rfl) ⟨1264829, by rfl⟩ : syracuseStep 1686439 = 2529659) B2529659
theorem B6405101 : Blo 1686043 6405101 := bstep (se 3 (by rfl) ⟨1200956, by rfl⟩ : syracuseStep 6405101 = 2401913) B2401913
theorem B8109089 : Blo 1686043 8109089 := bstep (se 2 (by rfl) ⟨3040908, by rfl⟩ : syracuseStep 8109089 = 6081817) B6081817
theorem B1686619 : Blo 1686043 1686619 := bstep (se 1 (by rfl) ⟨1264964, by rfl⟩ : syracuseStep 1686619 = 2529929) B2529929
theorem B1686735 : Blo 1686043 1686735 := bstep (se 1 (by rfl) ⟨1265051, by rfl⟩ : syracuseStep 1686735 = 2530103) B2530103
theorem B2530511 : Blo 1686043 2530511 := bstep (se 1 (by rfl) ⟨1897883, by rfl⟩ : syracuseStep 2530511 = 3795767) B3795767
theorem B1686759 : Blo 1686043 1686759 := bstep (se 1 (by rfl) ⟨1265069, by rfl⟩ : syracuseStep 1686759 = 2530139) B2530139
theorem B1686855 : Blo 1686043 1686855 := bstep (se 1 (by rfl) ⟨1265141, by rfl⟩ : syracuseStep 1686855 = 2530283) B2530283
theorem B2530631 : Blo 1686043 2530631 := bstep (se 1 (by rfl) ⟨1897973, by rfl⟩ : syracuseStep 2530631 = 3795947) B3795947
theorem B1686991 : Blo 1686043 1686991 := bstep (se 1 (by rfl) ⟨1265243, by rfl⟩ : syracuseStep 1686991 = 2530487) B2530487
theorem B16211411 : Blo 1686043 16211411 := bstep (se 1 (by rfl) ⟨12158558, by rfl⟩ : syracuseStep 16211411 = 24317117) B24317117
theorem B2530793 : Blo 1686043 2530793 := bstep (se 2 (by rfl) ⟨949047, by rfl⟩ : syracuseStep 2530793 = 1898095) B1898095
theorem B9608813 : Blo 1686043 9608813 := bstep (se 3 (by rfl) ⟨1801652, by rfl⟩ : syracuseStep 9608813 = 3603305) B3603305
theorem B1687151 : Blo 1686043 1687151 := bstep (se 1 (by rfl) ⟨1265363, by rfl⟩ : syracuseStep 1687151 = 2530727) B2530727
theorem B2530937 : Blo 1686043 2530937 := bstep (se 2 (by rfl) ⟨949101, by rfl⟩ : syracuseStep 2530937 = 1898203) B1898203
theorem B1687207 : Blo 1686043 1687207 := bstep (se 1 (by rfl) ⟨1265405, by rfl⟩ : syracuseStep 1687207 = 2530811) B2530811
theorem B1687271 : Blo 1686043 1687271 := bstep (se 1 (by rfl) ⟨1265453, by rfl⟩ : syracuseStep 1687271 = 2530907) B2530907
theorem B1687327 : Blo 1686043 1687327 := bstep (se 1 (by rfl) ⟨1265495, by rfl⟩ : syracuseStep 1687327 = 2530991) B2530991
theorem B1687407 : Blo 1686043 1687407 := bstep (se 1 (by rfl) ⟨1265555, by rfl⟩ : syracuseStep 1687407 = 2531111) B2531111
theorem B2531183 : Blo 1686043 2531183 := bstep (se 1 (by rfl) ⟨1898387, by rfl⟩ : syracuseStep 2531183 = 3796775) B3796775
theorem B10805147 : Blo 1686043 10805147 := bstep (se 1 (by rfl) ⟨8103860, by rfl⟩ : syracuseStep 10805147 = 16207721) B16207721
theorem B1687463 : Blo 1686043 1687463 := bstep (se 1 (by rfl) ⟨1265597, by rfl⟩ : syracuseStep 1687463 = 2531195) B2531195
theorem B46186433 : Blo 1686043 46186433 := bstep (se 2 (by rfl) ⟨17319912, by rfl⟩ : syracuseStep 46186433 = 34639825) B34639825
theorem B8536103 : Blo 1686043 8536103 := bstep (se 1 (by rfl) ⟨6402077, by rfl⟩ : syracuseStep 8536103 = 12804155) B12804155
theorem B3203135 : Blo 1686043 3203135 := bstep (se 1 (by rfl) ⟨2402351, by rfl⟩ : syracuseStep 3203135 = 4804703) B4804703
theorem B2531423 : Blo 1686043 2531423 := bstep (se 1 (by rfl) ⟨1898567, by rfl⟩ : syracuseStep 2531423 = 3797135) B3797135
theorem B5693543 : Blo 1686043 5693543 := bstep (se 1 (by rfl) ⟨4270157, by rfl⟩ : syracuseStep 5693543 = 8540315) B8540315
theorem B2531483 : Blo 1686043 2531483 := bstep (se 1 (by rfl) ⟨1898612, by rfl⟩ : syracuseStep 2531483 = 3797225) B3797225
theorem B4055275 : Blo 1686043 4055275 := bstep (se 1 (by rfl) ⟨3041456, by rfl⟩ : syracuseStep 4055275 = 6082913) B6082913
theorem B2531567 : Blo 1686043 2531567 := bstep (se 1 (by rfl) ⟨1898675, by rfl⟩ : syracuseStep 2531567 = 3797351) B3797351
theorem B4268335 : Blo 1686043 4268335 := bstep (se 1 (by rfl) ⟨3201251, by rfl⟩ : syracuseStep 4268335 = 6402503) B6402503
theorem B1687911 : Blo 1686043 1687911 := bstep (se 1 (by rfl) ⟨1265933, by rfl⟩ : syracuseStep 1687911 = 2531867) B2531867
theorem B1688031 : Blo 1686043 1688031 := bstep (se 1 (by rfl) ⟨1266023, by rfl⟩ : syracuseStep 1688031 = 2532047) B2532047
theorem B1688039 : Blo 1686043 1688039 := bstep (se 1 (by rfl) ⟨1266029, by rfl⟩ : syracuseStep 1688039 = 2532059) B2532059
theorem B369484355 : Blo 1686043 369484355 := bstep (se 1 (by rfl) ⟨277113266, by rfl⟩ : syracuseStep 369484355 = 554226533) B554226533
theorem B12812903 : Blo 1686043 12812903 := bstep (se 1 (by rfl) ⟨9609677, by rfl⟩ : syracuseStep 12812903 = 19219355) B19219355
theorem B2531945 : Blo 1686043 2531945 := bstep (se 2 (by rfl) ⟨949479, by rfl⟩ : syracuseStep 2531945 = 1898959) B1898959
theorem B2531951 : Blo 1686043 2531951 := bstep (se 1 (by rfl) ⟨1898963, by rfl⟩ : syracuseStep 2531951 = 3797927) B3797927
theorem B3466351 : Blo 1686043 3466351 := bstep (se 1 (by rfl) ⟨2599763, by rfl⟩ : syracuseStep 3466351 = 5199527) B5199527
theorem B3794111 : Blo 1686043 3794111 := bstep (se 1 (by rfl) ⟨2845583, by rfl⟩ : syracuseStep 3794111 = 5691167) B5691167
theorem B7202459 : Blo 1686043 7202459 := bstep (se 1 (by rfl) ⟨5401844, by rfl⟩ : syracuseStep 7202459 = 10803689) B10803689
theorem B4269743 : Blo 1686043 4269743 := bstep (se 1 (by rfl) ⟨3202307, by rfl⟩ : syracuseStep 4269743 = 6404615) B6404615
theorem B36489001 : Blo 1686043 36489001 := bstep (se 2 (by rfl) ⟨13683375, by rfl⟩ : syracuseStep 36489001 = 27366751) B27366751
theorem B4270067 : Blo 1686043 4270067 := bstep (se 1 (by rfl) ⟨3202550, by rfl⟩ : syracuseStep 4270067 = 6405101) B6405101
theorem B4327679 : Blo 1686043 4327679 := bstep (se 1 (by rfl) ⟨3245759, by rfl⟩ : syracuseStep 4327679 = 6491519) B6491519
theorem B4933943 : Blo 1686043 4933943 := bstep (se 1 (by rfl) ⟨3700457, by rfl⟩ : syracuseStep 4933943 = 7400915) B7400915
theorem B10807607 : Blo 1686043 10807607 := bstep (se 1 (by rfl) ⟨8105705, by rfl⟩ : syracuseStep 10807607 = 16211411) B16211411
theorem B23718221 : Blo 1686043 23718221 := bstep (se 3 (by rfl) ⟨4447166, by rfl⟩ : syracuseStep 23718221 = 8894333) B8894333
theorem B7203431 : Blo 1686043 7203431 := bstep (se 1 (by rfl) ⟨5402573, by rfl⟩ : syracuseStep 7203431 = 10805147) B10805147
theorem B4868873 : Blo 1686043 4868873 := bstep (se 2 (by rfl) ⟨1825827, by rfl⟩ : syracuseStep 4868873 = 3651655) B3651655
theorem B9604007 : Blo 1686043 9604007 := bstep (se 1 (by rfl) ⟨7203005, by rfl⟩ : syracuseStep 9604007 = 14406011) B14406011
theorem B17312771 : Blo 1686043 17312771 := bstep (se 1 (by rfl) ⟨12984578, by rfl⟩ : syracuseStep 17312771 = 25969157) B25969157
theorem B54742067 : Blo 1686043 54742067 := bstep (se 1 (by rfl) ⟨41056550, by rfl⟩ : syracuseStep 54742067 = 82113101) B82113101
theorem B7204115 : Blo 1686043 7204115 := bstep (se 1 (by rfl) ⟨5403086, by rfl⟩ : syracuseStep 7204115 = 10806173) B10806173
theorem B23080301 : Blo 1686043 23080301 := bstep (se 3 (by rfl) ⟨4327556, by rfl⟩ : syracuseStep 23080301 = 8655113) B8655113
theorem B5402011 : Blo 1686043 5402011 := bstep (se 1 (by rfl) ⟨4051508, by rfl⟩ : syracuseStep 5402011 = 8103017) B8103017
theorem B810618293 : Blo 1686043 810618293 := bstep (se 5 (by rfl) ⟨37997732, by rfl⟩ : syracuseStep 810618293 = 75995465) B75995465
theorem B41061815 : Blo 1686043 41061815 := bstep (se 1 (by rfl) ⟨30796361, by rfl⟩ : syracuseStep 41061815 = 61592723) B61592723
theorem B9612755 : Blo 1686043 9612755 := bstep (se 1 (by rfl) ⟨7209566, by rfl⟩ : syracuseStep 9612755 = 14419133) B14419133
theorem B8539667 : Blo 1686043 8539667 := bstep (se 1 (by rfl) ⟨6404750, by rfl⟩ : syracuseStep 8539667 = 12809501) B12809501
theorem B4271687 : Blo 1686043 4271687 := bstep (se 1 (by rfl) ⟨3203765, by rfl⟩ : syracuseStep 4271687 = 6407531) B6407531
theorem B4271737 : Blo 1686043 4271737 := bstep (se 2 (by rfl) ⟨1601901, by rfl⟩ : syracuseStep 4271737 = 3203803) B3203803
theorem B12160637 : Blo 1686043 12160637 := bstep (se 3 (by rfl) ⟨2280119, by rfl⟩ : syracuseStep 12160637 = 4560239) B4560239
theorem B24309395 : Blo 1686043 24309395 := bstep (se 1 (by rfl) ⟨18232046, by rfl⟩ : syracuseStep 24309395 = 36464093) B36464093
theorem B135147305 : Blo 1686043 135147305 := bstep (se 2 (by rfl) ⟨50680239, by rfl⟩ : syracuseStep 135147305 = 101360479) B101360479
theorem B4558943 : Blo 1686043 4558943 := bstep (se 1 (by rfl) ⟨3419207, by rfl⟩ : syracuseStep 4558943 = 6838415) B6838415
theorem B2846927 : Blo 1686043 2846927 := bstep (se 1 (by rfl) ⟨2135195, by rfl⟩ : syracuseStep 2846927 = 4270391) B4270391
theorem B9613687 : Blo 1686043 9613687 := bstep (se 1 (by rfl) ⟨7210265, by rfl⟩ : syracuseStep 9613687 = 14420531) B14420531
theorem B4870583 : Blo 1686043 4870583 := bstep (se 1 (by rfl) ⟨3652937, by rfl⟩ : syracuseStep 4870583 = 7305875) B7305875
theorem B28815911 : Blo 1686043 28815911 := bstep (se 1 (by rfl) ⟨21611933, by rfl⟩ : syracuseStep 28815911 = 43223867) B43223867
theorem B9605897 : Blo 1686043 9605897 := bstep (se 2 (by rfl) ⟨3602211, by rfl⟩ : syracuseStep 9605897 = 7204423) B7204423
theorem B6402959 : Blo 1686043 6402959 := bstep (se 1 (by rfl) ⟨4802219, by rfl⟩ : syracuseStep 6402959 = 9604439) B9604439
theorem B5403599 : Blo 1686043 5403599 := bstep (se 1 (by rfl) ⟨4052699, by rfl⟩ : syracuseStep 5403599 = 8105399) B8105399
theorem B1897519 : Blo 1686043 1897519 := bstep (se 1 (by rfl) ⟨1423139, by rfl⟩ : syracuseStep 1897519 = 2846279) B2846279
theorem B2847865 : Blo 1686043 2847865 := bstep (se 2 (by rfl) ⟨1067949, by rfl⟩ : syracuseStep 2847865 = 2135899) B2135899
theorem B2847899 : Blo 1686043 2847899 := bstep (se 1 (by rfl) ⟨2135924, by rfl⟩ : syracuseStep 2847899 = 4271849) B4271849
theorem B30790955 : Blo 1686043 30790955 := bstep (se 1 (by rfl) ⟨23093216, by rfl⟩ : syracuseStep 30790955 = 46186433) B46186433
theorem B4806287 : Blo 1686043 4806287 := bstep (se 1 (by rfl) ⟨3604715, by rfl⟩ : syracuseStep 4806287 = 7209431) B7209431
theorem B4560671 : Blo 1686043 4560671 := bstep (se 1 (by rfl) ⟨3420503, by rfl⟩ : syracuseStep 4560671 = 6841007) B6841007
theorem B4872059 : Blo 1686043 4872059 := bstep (se 1 (by rfl) ⟨3654044, by rfl⟩ : syracuseStep 4872059 = 7308089) B7308089
theorem B6838141 : Blo 1686043 6838141 := bstep (se 3 (by rfl) ⟨1282151, by rfl⟩ : syracuseStep 6838141 = 2564303) B2564303
theorem B5691383 : Blo 1686043 5691383 := bstep (se 1 (by rfl) ⟨4268537, by rfl⟩ : syracuseStep 5691383 = 8537075) B8537075
theorem B1898491 : Blo 1686043 1898491 := bstep (se 1 (by rfl) ⟨1423868, by rfl⟩ : syracuseStep 1898491 = 2847737) B2847737
theorem B5199869 : Blo 1686043 5199869 := bstep (se 3 (by rfl) ⟨974975, by rfl⟩ : syracuseStep 5199869 = 1949951) B1949951
theorem B9115679 : Blo 1686043 9115679 := bstep (se 1 (by rfl) ⟨6836759, by rfl⟩ : syracuseStep 9115679 = 13673519) B13673519
theorem B2529311 : Blo 1686043 2529311 := bstep (se 1 (by rfl) ⟨1896983, by rfl⟩ : syracuseStep 2529311 = 3793967) B3793967
theorem B10950803 : Blo 1686043 10950803 := bstep (se 1 (by rfl) ⟨8213102, by rfl⟩ : syracuseStep 10950803 = 16426205) B16426205
theorem B1898671 : Blo 1686043 1898671 := bstep (se 1 (by rfl) ⟨1424003, by rfl⟩ : syracuseStep 1898671 = 2848007) B2848007
theorem B8542583 : Blo 1686043 8542583 := bstep (se 1 (by rfl) ⟨6406937, by rfl⟩ : syracuseStep 8542583 = 12813875) B12813875
theorem B9124285 : Blo 1686043 9124285 := bstep (se 3 (by rfl) ⟨1710803, by rfl⟩ : syracuseStep 9124285 = 3421607) B3421607
theorem B2529743 : Blo 1686043 2529743 := bstep (se 1 (by rfl) ⟨1897307, by rfl⟩ : syracuseStep 2529743 = 3794615) B3794615
theorem B2529833 : Blo 1686043 2529833 := bstep (se 2 (by rfl) ⟨948687, by rfl⟩ : syracuseStep 2529833 = 1897375) B1897375
theorem B1686063 : Blo 1686043 1686063 := bstep (se 1 (by rfl) ⟨1264547, by rfl⟩ : syracuseStep 1686063 = 2529095) B2529095
theorem B2530043 : Blo 1686043 2530043 := bstep (se 1 (by rfl) ⟨1897532, by rfl⟩ : syracuseStep 2530043 = 3795065) B3795065
theorem B2530169 : Blo 1686043 2530169 := bstep (se 2 (by rfl) ⟨948813, by rfl⟩ : syracuseStep 2530169 = 1897627) B1897627
theorem B43834283 : Blo 1686043 43834283 := bstep (se 1 (by rfl) ⟨32875712, by rfl⟩ : syracuseStep 43834283 = 65751425) B65751425
theorem B1686463 : Blo 1686043 1686463 := bstep (se 1 (by rfl) ⟨1264847, by rfl⟩ : syracuseStep 1686463 = 2529695) B2529695
theorem B9608129 : Blo 1686043 9608129 := bstep (se 2 (by rfl) ⟨3603048, by rfl⟩ : syracuseStep 9608129 = 7206097) B7206097
theorem B6077423 : Blo 1686043 6077423 := bstep (se 1 (by rfl) ⟨4558067, by rfl⟩ : syracuseStep 6077423 = 9116135) B9116135
theorem B1686511 : Blo 1686043 1686511 := bstep (se 1 (by rfl) ⟨1264883, by rfl⟩ : syracuseStep 1686511 = 2529767) B2529767
theorem B5692463 : Blo 1686043 5692463 := bstep (se 1 (by rfl) ⟨4269347, by rfl⟩ : syracuseStep 5692463 = 8538695) B8538695
theorem B61562045 : Blo 1686043 61562045 := bstep (se 3 (by rfl) ⟨11542883, by rfl⟩ : syracuseStep 61562045 = 23085767) B23085767
theorem B5406059 : Blo 1686043 5406059 := bstep (se 1 (by rfl) ⟨4054544, by rfl⟩ : syracuseStep 5406059 = 8109089) B8109089
theorem B1687007 : Blo 1686043 1687007 := bstep (se 1 (by rfl) ⟨1265255, by rfl⟩ : syracuseStep 1687007 = 2530511) B2530511
theorem B1687087 : Blo 1686043 1687087 := bstep (se 1 (by rfl) ⟨1265315, by rfl⟩ : syracuseStep 1687087 = 2530631) B2530631
theorem B2530919 : Blo 1686043 2530919 := bstep (se 1 (by rfl) ⟨1898189, by rfl⟩ : syracuseStep 2530919 = 3796379) B3796379
theorem B1687195 : Blo 1686043 1687195 := bstep (se 1 (by rfl) ⟨1265396, by rfl⟩ : syracuseStep 1687195 = 2530793) B2530793
theorem B6405875 : Blo 1686043 6405875 := bstep (se 1 (by rfl) ⟨4804406, by rfl⟩ : syracuseStep 6405875 = 9608813) B9608813
theorem B1687291 : Blo 1686043 1687291 := bstep (se 1 (by rfl) ⟨1265468, by rfl⟩ : syracuseStep 1687291 = 2530937) B2530937
theorem B2531081 : Blo 1686043 2531081 := bstep (se 2 (by rfl) ⟨949155, by rfl⟩ : syracuseStep 2531081 = 1898311) B1898311
theorem B1687455 : Blo 1686043 1687455 := bstep (se 1 (by rfl) ⟨1265591, by rfl⟩ : syracuseStep 1687455 = 2531183) B2531183
theorem B9609131 : Blo 1686043 9609131 := bstep (se 1 (by rfl) ⟨7206848, by rfl⟩ : syracuseStep 9609131 = 14413697) B14413697
theorem B4267991 : Blo 1686043 4267991 := bstep (se 1 (by rfl) ⟨3200993, by rfl⟩ : syracuseStep 4267991 = 6401987) B6401987
theorem B2531303 : Blo 1686043 2531303 := bstep (se 1 (by rfl) ⟨1898477, by rfl⟩ : syracuseStep 2531303 = 3796955) B3796955
theorem B2703337 : Blo 1686043 2703337 := bstep (se 2 (by rfl) ⟨1013751, by rfl⟩ : syracuseStep 2703337 = 2027503) B2027503
theorem B3039295 : Blo 1686043 3039295 := bstep (se 1 (by rfl) ⟨2279471, by rfl⟩ : syracuseStep 3039295 = 4558943) B4558943
theorem B1687615 : Blo 1686043 1687615 := bstep (se 1 (by rfl) ⟨1265711, by rfl⟩ : syracuseStep 1687615 = 2531423) B2531423
theorem B1687655 : Blo 1686043 1687655 := bstep (se 1 (by rfl) ⟨1265741, by rfl⟩ : syracuseStep 1687655 = 2531483) B2531483
theorem B1687711 : Blo 1686043 1687711 := bstep (se 1 (by rfl) ⟨1265783, by rfl⟩ : syracuseStep 1687711 = 2531567) B2531567
theorem B2531561 : Blo 1686043 2531561 := bstep (se 2 (by rfl) ⟨949335, by rfl⟩ : syracuseStep 2531561 = 1898671) B1898671
theorem B19210607 : Blo 1686043 19210607 := bstep (se 1 (by rfl) ⟨14407955, by rfl⟩ : syracuseStep 19210607 = 28815911) B28815911
theorem B1687963 : Blo 1686043 1687963 := bstep (se 1 (by rfl) ⟨1265972, by rfl⟩ : syracuseStep 1687963 = 2531945) B2531945
theorem B1687967 : Blo 1686043 1687967 := bstep (se 1 (by rfl) ⟨1265975, by rfl⟩ : syracuseStep 1687967 = 2531951) B2531951
theorem B12165713 : Blo 1686043 12165713 := bstep (se 2 (by rfl) ⟨4562142, by rfl⟩ : syracuseStep 12165713 = 9124285) B9124285
theorem B4268639 : Blo 1686043 4268639 := bstep (se 1 (by rfl) ⟨3201479, by rfl⟩ : syracuseStep 4268639 = 6402959) B6402959
theorem B28820285 : Blo 1686043 28820285 := bstep (se 3 (by rfl) ⟨5403803, by rfl⟩ : syracuseStep 28820285 = 10807607) B10807607
theorem B3204191 : Blo 1686043 3204191 := bstep (se 1 (by rfl) ⟨2403143, by rfl⟩ : syracuseStep 3204191 = 4806287) B4806287
theorem B4801639 : Blo 1686043 4801639 := bstep (se 1 (by rfl) ⟨3601229, by rfl⟩ : syracuseStep 4801639 = 7202459) B7202459
theorem B21628133 : Blo 1686043 21628133 := bstep (se 4 (by rfl) ⟨2027637, by rfl⟩ : syracuseStep 21628133 = 4055275) B4055275
theorem B3794255 : Blo 1686043 3794255 := bstep (se 1 (by rfl) ⟨2845691, by rfl⟩ : syracuseStep 3794255 = 5691383) B5691383
theorem B7300535 : Blo 1686043 7300535 := bstep (se 1 (by rfl) ⟨5475401, by rfl⟩ : syracuseStep 7300535 = 10950803) B10950803
theorem B4621801 : Blo 1686043 4621801 := bstep (se 2 (by rfl) ⟨1733175, by rfl⟩ : syracuseStep 4621801 = 3466351) B3466351
theorem B15812147 : Blo 1686043 15812147 := bstep (se 1 (by rfl) ⟨11859110, by rfl⟩ : syracuseStep 15812147 = 23718221) B23718221
theorem B5695055 : Blo 1686043 5695055 := bstep (se 1 (by rfl) ⟨4271291, by rfl⟩ : syracuseStep 5695055 = 8542583) B8542583
theorem B3245915 : Blo 1686043 3245915 := bstep (se 1 (by rfl) ⟨2434436, by rfl⟩ : syracuseStep 3245915 = 4868873) B4868873
theorem B7202681 : Blo 1686043 7202681 := bstep (se 2 (by rfl) ⟨2701005, by rfl⟩ : syracuseStep 7202681 = 5402011) B5402011
theorem B29222855 : Blo 1686043 29222855 := bstep (se 1 (by rfl) ⟨21917141, by rfl⟩ : syracuseStep 29222855 = 43834283) B43834283
theorem B3794975 : Blo 1686043 3794975 := bstep (se 1 (by rfl) ⟨2846231, by rfl⟩ : syracuseStep 3794975 = 5692463) B5692463
theorem B360392813 : Blo 1686043 360392813 := bstep (se 3 (by rfl) ⟨67573652, by rfl⟩ : syracuseStep 360392813 = 135147305) B135147305
theorem B5695649 : Blo 1686043 5695649 := bstep (se 2 (by rfl) ⟨2135868, by rfl⟩ : syracuseStep 5695649 = 4271737) B4271737
theorem B4802743 : Blo 1686043 4802743 := bstep (se 1 (by rfl) ⟨3602057, by rfl⟩ : syracuseStep 4802743 = 7204115) B7204115
theorem B15386867 : Blo 1686043 15386867 := bstep (se 1 (by rfl) ⟨11540150, by rfl⟩ : syracuseStep 15386867 = 23080301) B23080301
theorem B540412195 : Blo 1686043 540412195 := bstep (se 1 (by rfl) ⟨405309146, by rfl⟩ : syracuseStep 540412195 = 810618293) B810618293
theorem B6408503 : Blo 1686043 6408503 := bstep (se 1 (by rfl) ⟨4806377, by rfl⟩ : syracuseStep 6408503 = 9612755) B9612755
theorem B16206263 : Blo 1686043 16206263 := bstep (se 1 (by rfl) ⟨12154697, by rfl⟩ : syracuseStep 16206263 = 24309395) B24309395
theorem B4270583 : Blo 1686043 4270583 := bstep (se 1 (by rfl) ⟨3202937, by rfl⟩ : syracuseStep 4270583 = 6405875) B6405875
theorem B2845327 : Blo 1686043 2845327 := bstep (se 1 (by rfl) ⟨2133995, by rfl⟩ : syracuseStep 2845327 = 4267991) B4267991
theorem B3795695 : Blo 1686043 3795695 := bstep (se 1 (by rfl) ⟨2846771, by rfl⟩ : syracuseStep 3795695 = 5693543) B5693543
theorem B3247055 : Blo 1686043 3247055 := bstep (se 1 (by rfl) ⟨2435291, by rfl⟩ : syracuseStep 3247055 = 4870583) B4870583
theorem B2846495 : Blo 1686043 2846495 := bstep (se 1 (by rfl) ⟨2134871, by rfl⟩ : syracuseStep 2846495 = 4269743) B4269743
theorem B3248039 : Blo 1686043 3248039 := bstep (se 1 (by rfl) ⟨2436029, by rfl⟩ : syracuseStep 3248039 = 4872059) B4872059
theorem B2846711 : Blo 1686043 2846711 := bstep (se 1 (by rfl) ⟨2135033, by rfl⟩ : syracuseStep 2846711 = 4270067) B4270067
theorem B3797153 : Blo 1686043 3797153 := bstep (se 2 (by rfl) ⟨1423932, by rfl⟩ : syracuseStep 3797153 = 2847865) B2847865
theorem B3289295 : Blo 1686043 3289295 := bstep (se 1 (by rfl) ⟨2466971, by rfl⟩ : syracuseStep 3289295 = 4933943) B4933943
theorem B6402671 : Blo 1686043 6402671 := bstep (se 1 (by rfl) ⟨4802003, by rfl⟩ : syracuseStep 6402671 = 9604007) B9604007
theorem B4051615 : Blo 1686043 4051615 := bstep (se 1 (by rfl) ⟨3038711, by rfl⟩ : syracuseStep 4051615 = 6077423) B6077423
theorem B12161789 : Blo 1686043 12161789 := bstep (se 3 (by rfl) ⟨2280335, by rfl⟩ : syracuseStep 12161789 = 4560671) B4560671
theorem B27374543 : Blo 1686043 27374543 := bstep (se 1 (by rfl) ⟨20530907, by rfl⟩ : syracuseStep 27374543 = 41061815) B41061815
theorem B2847791 : Blo 1686043 2847791 := bstep (se 1 (by rfl) ⟨2135843, by rfl⟩ : syracuseStep 2847791 = 4271687) B4271687
theorem B8107091 : Blo 1686043 8107091 := bstep (se 1 (by rfl) ⟨6080318, by rfl⟩ : syracuseStep 8107091 = 12160637) B12160637
theorem B13866317 : Blo 1686043 13866317 := bstep (se 3 (by rfl) ⟨2599934, by rfl⟩ : syracuseStep 13866317 = 5199869) B5199869
theorem B5690735 : Blo 1686043 5690735 := bstep (se 1 (by rfl) ⟨4268051, by rfl⟩ : syracuseStep 5690735 = 8536103) B8536103
theorem B2135423 : Blo 1686043 2135423 := bstep (se 1 (by rfl) ⟨1601567, by rfl⟩ : syracuseStep 2135423 = 3203135) B3203135
theorem B1897951 : Blo 1686043 1897951 := bstep (se 1 (by rfl) ⟨1423463, by rfl⟩ : syracuseStep 1897951 = 2846927) B2846927
theorem B246322903 : Blo 1686043 246322903 := bstep (se 1 (by rfl) ⟨184742177, by rfl⟩ : syracuseStep 246322903 = 369484355) B369484355
theorem B5691113 : Blo 1686043 5691113 := bstep (se 2 (by rfl) ⟨2134167, by rfl⟩ : syracuseStep 5691113 = 4268335) B4268335
theorem B8541935 : Blo 1686043 8541935 := bstep (se 1 (by rfl) ⟨6406451, by rfl⟩ : syracuseStep 8541935 = 12812903) B12812903
theorem B12818249 : Blo 1686043 12818249 := bstep (se 2 (by rfl) ⟨4806843, by rfl⟩ : syracuseStep 12818249 = 9613687) B9613687
theorem B6403931 : Blo 1686043 6403931 := bstep (se 1 (by rfl) ⟨4802948, by rfl⟩ : syracuseStep 6403931 = 9605897) B9605897
theorem B3602399 : Blo 1686043 3602399 := bstep (se 1 (by rfl) ⟨2701799, by rfl⟩ : syracuseStep 3602399 = 5403599) B5403599
theorem B11540477 : Blo 1686043 11540477 := bstep (se 3 (by rfl) ⟨2163839, by rfl⟩ : syracuseStep 11540477 = 4327679) B4327679
theorem B1898599 : Blo 1686043 1898599 := bstep (se 1 (by rfl) ⟨1423949, by rfl⟩ : syracuseStep 1898599 = 2847899) B2847899
theorem B2529407 : Blo 1686043 2529407 := bstep (se 1 (by rfl) ⟨1897055, by rfl⟩ : syracuseStep 2529407 = 3794111) B3794111
theorem B20527303 : Blo 1686043 20527303 := bstep (se 1 (by rfl) ⟨15395477, by rfl⟩ : syracuseStep 20527303 = 30790955) B30790955
theorem B14416157 : Blo 1686043 14416157 := bstep (se 3 (by rfl) ⟨2703029, by rfl⟩ : syracuseStep 14416157 = 5406059) B5406059
theorem B6077119 : Blo 1686043 6077119 := bstep (se 1 (by rfl) ⟨4557839, by rfl⟩ : syracuseStep 6077119 = 9115679) B9115679
theorem B1686207 : Blo 1686043 1686207 := bstep (se 1 (by rfl) ⟨1264655, by rfl⟩ : syracuseStep 1686207 = 2529311) B2529311
theorem B2530025 : Blo 1686043 2530025 := bstep (se 2 (by rfl) ⟨948759, by rfl⟩ : syracuseStep 2530025 = 1897519) B1897519
theorem B19209149 : Blo 1686043 19209149 := bstep (se 3 (by rfl) ⟨3601715, by rfl⟩ : syracuseStep 19209149 = 7203431) B7203431
theorem B1686495 : Blo 1686043 1686495 := bstep (se 1 (by rfl) ⟨1264871, by rfl⟩ : syracuseStep 1686495 = 2529743) B2529743
theorem B1686555 : Blo 1686043 1686555 := bstep (se 1 (by rfl) ⟨1264916, by rfl⟩ : syracuseStep 1686555 = 2529833) B2529833
theorem B1686695 : Blo 1686043 1686695 := bstep (se 1 (by rfl) ⟨1265021, by rfl⟩ : syracuseStep 1686695 = 2530043) B2530043
theorem B1686779 : Blo 1686043 1686779 := bstep (se 1 (by rfl) ⟨1265084, by rfl⟩ : syracuseStep 1686779 = 2530169) B2530169
theorem B6405419 : Blo 1686043 6405419 := bstep (se 1 (by rfl) ⟨4804064, by rfl⟩ : syracuseStep 6405419 = 9608129) B9608129
theorem B11541847 : Blo 1686043 11541847 := bstep (se 1 (by rfl) ⟨8656385, by rfl⟩ : syracuseStep 11541847 = 17312771) B17312771
theorem B36494711 : Blo 1686043 36494711 := bstep (se 1 (by rfl) ⟨27371033, by rfl⟩ : syracuseStep 36494711 = 54742067) B54742067
theorem B41041363 : Blo 1686043 41041363 := bstep (se 1 (by rfl) ⟨30781022, by rfl⟩ : syracuseStep 41041363 = 61562045) B61562045
theorem B5693111 : Blo 1686043 5693111 := bstep (se 1 (by rfl) ⟨4269833, by rfl⟩ : syracuseStep 5693111 = 8539667) B8539667
theorem B48652001 : Blo 1686043 48652001 := bstep (se 2 (by rfl) ⟨18244500, by rfl⟩ : syracuseStep 48652001 = 36489001) B36489001
theorem B1687279 : Blo 1686043 1687279 := bstep (se 1 (by rfl) ⟨1265459, by rfl⟩ : syracuseStep 1687279 = 2530919) B2530919
theorem B9117521 : Blo 1686043 9117521 := bstep (se 2 (by rfl) ⟨3419070, by rfl⟩ : syracuseStep 9117521 = 6838141) B6838141
theorem B1687387 : Blo 1686043 1687387 := bstep (se 1 (by rfl) ⟨1265540, by rfl⟩ : syracuseStep 1687387 = 2531081) B2531081
theorem B14417797 : Blo 1686043 14417797 := bstep (se 4 (by rfl) ⟨1351668, by rfl⟩ : syracuseStep 14417797 = 2703337) B2703337
theorem B6406087 : Blo 1686043 6406087 := bstep (se 1 (by rfl) ⟨4804565, by rfl⟩ : syracuseStep 6406087 = 9609131) B9609131
theorem B1687535 : Blo 1686043 1687535 := bstep (se 1 (by rfl) ⟨1265651, by rfl⟩ : syracuseStep 1687535 = 2531303) B2531303
theorem B2531321 : Blo 1686043 2531321 := bstep (se 2 (by rfl) ⟨949245, by rfl⟩ : syracuseStep 2531321 = 1898491) B1898491
theorem B2531435 : Blo 1686043 2531435 := bstep (se 1 (by rfl) ⟨1898576, by rfl⟩ : syracuseStep 2531435 = 3797153) B3797153
theorem B2531465 : Blo 1686043 2531465 := bstep (se 2 (by rfl) ⟨949299, by rfl⟩ : syracuseStep 2531465 = 1898599) B1898599
theorem B1687707 : Blo 1686043 1687707 := bstep (se 1 (by rfl) ⟨1265780, by rfl⟩ : syracuseStep 1687707 = 2531561) B2531561
theorem B27369737 : Blo 1686043 27369737 := bstep (se 2 (by rfl) ⟨10263651, by rfl⟩ : syracuseStep 27369737 = 20527303) B20527303
theorem B8110475 : Blo 1686043 8110475 := bstep (se 1 (by rfl) ⟨6082856, by rfl⟩ : syracuseStep 8110475 = 12165713) B12165713
theorem B4268447 : Blo 1686043 4268447 := bstep (se 1 (by rfl) ⟨3201335, by rfl⟩ : syracuseStep 4268447 = 6402671) B6402671
theorem B14418755 : Blo 1686043 14418755 := bstep (se 1 (by rfl) ⟨10814066, by rfl⟩ : syracuseStep 14418755 = 21628133) B21628133
theorem B3793769 : Blo 1686043 3793769 := bstep (se 2 (by rfl) ⟨1422663, by rfl⟩ : syracuseStep 3793769 = 2845327) B2845327
theorem B3793823 : Blo 1686043 3793823 := bstep (se 1 (by rfl) ⟨2845367, by rfl⟩ : syracuseStep 3793823 = 5690735) B5690735
theorem B8102825 : Blo 1686043 8102825 := bstep (se 2 (by rfl) ⟨3038559, by rfl⟩ : syracuseStep 8102825 = 6077119) B6077119
theorem B5694461 : Blo 1686043 5694461 := bstep (se 3 (by rfl) ⟨1067711, by rfl⟩ : syracuseStep 5694461 = 2135423) B2135423
theorem B3794075 : Blo 1686043 3794075 := bstep (se 1 (by rfl) ⟨2845556, by rfl⟩ : syracuseStep 3794075 = 5691113) B5691113
theorem B5694623 : Blo 1686043 5694623 := bstep (se 1 (by rfl) ⟨4270967, by rfl⟩ : syracuseStep 5694623 = 8541935) B8541935
theorem B8545499 : Blo 1686043 8545499 := bstep (se 1 (by rfl) ⟨6409124, by rfl⟩ : syracuseStep 8545499 = 12818249) B12818249
theorem B4269287 : Blo 1686043 4269287 := bstep (se 1 (by rfl) ⟨3201965, by rfl⟩ : syracuseStep 4269287 = 6403931) B6403931
theorem B2163943 : Blo 1686043 2163943 := bstep (se 1 (by rfl) ⟨1622957, by rfl⟩ : syracuseStep 2163943 = 3245915) B3245915
theorem B4801787 : Blo 1686043 4801787 := bstep (se 1 (by rfl) ⟨3601340, by rfl⟩ : syracuseStep 4801787 = 7202681) B7202681
theorem B19481903 : Blo 1686043 19481903 := bstep (se 1 (by rfl) ⟨14611427, by rfl⟩ : syracuseStep 19481903 = 29222855) B29222855
theorem B7693651 : Blo 1686043 7693651 := bstep (se 1 (by rfl) ⟨5770238, by rfl⟩ : syracuseStep 7693651 = 11540477) B11540477
theorem B10257911 : Blo 1686043 10257911 := bstep (se 1 (by rfl) ⟨7693433, by rfl⟩ : syracuseStep 10257911 = 15386867) B15386867
theorem B9610771 : Blo 1686043 9610771 := bstep (se 1 (by rfl) ⟨7208078, by rfl⟩ : syracuseStep 9610771 = 14416157) B14416157
theorem B12806099 : Blo 1686043 12806099 := bstep (se 1 (by rfl) ⟨9604574, by rfl⟩ : syracuseStep 12806099 = 19209149) B19209149
theorem B2164703 : Blo 1686043 2164703 := bstep (se 1 (by rfl) ⟨1623527, by rfl⟩ : syracuseStep 2164703 = 3247055) B3247055
theorem B6162401 : Blo 1686043 6162401 := bstep (se 2 (by rfl) ⟨2310900, by rfl⟩ : syracuseStep 6162401 = 4621801) B4621801
theorem B4270279 : Blo 1686043 4270279 := bstep (se 1 (by rfl) ⟨3202709, by rfl⟩ : syracuseStep 4270279 = 6405419) B6405419
theorem B8661437 : Blo 1686043 8661437 := bstep (se 3 (by rfl) ⟨1624019, by rfl⟩ : syracuseStep 8661437 = 3248039) B3248039
theorem B3795407 : Blo 1686043 3795407 := bstep (se 1 (by rfl) ⟨2846555, by rfl⟩ : syracuseStep 3795407 = 5693111) B5693111
theorem B32434667 : Blo 1686043 32434667 := bstep (se 1 (by rfl) ⟨24326000, by rfl⟩ : syracuseStep 32434667 = 48652001) B48652001
theorem B12807071 : Blo 1686043 12807071 := bstep (se 1 (by rfl) ⟨9605303, by rfl⟩ : syracuseStep 12807071 = 19210607) B19210607
theorem B2845759 : Blo 1686043 2845759 := bstep (se 1 (by rfl) ⟨2134319, by rfl⟩ : syracuseStep 2845759 = 4268639) B4268639
theorem B19213523 : Blo 1686043 19213523 := bstep (se 1 (by rfl) ⟨14410142, by rfl⟩ : syracuseStep 19213523 = 28820285) B28820285
theorem B1687547 : Blo 1686043 1687547 := bstep (se 1 (by rfl) ⟨1265660, by rfl⟩ : syracuseStep 1687547 = 2531321) B2531321
theorem B5402153 : Blo 1686043 5402153 := bstep (se 2 (by rfl) ⟨2025807, by rfl⟩ : syracuseStep 5402153 = 4051615) B4051615
theorem B9244211 : Blo 1686043 9244211 := bstep (se 1 (by rfl) ⟨6933158, by rfl⟩ : syracuseStep 9244211 = 13866317) B13866317
theorem B3796703 : Blo 1686043 3796703 := bstep (se 1 (by rfl) ⟨2847527, by rfl⟩ : syracuseStep 3796703 = 5695055) B5695055
theorem B3797099 : Blo 1686043 3797099 := bstep (se 1 (by rfl) ⟨2847824, by rfl⟩ : syracuseStep 3797099 = 5695649) B5695649
theorem B6402185 : Blo 1686043 6402185 := bstep (se 2 (by rfl) ⟨2400819, by rfl⟩ : syracuseStep 6402185 = 4801639) B4801639
theorem B4272335 : Blo 1686043 4272335 := bstep (se 1 (by rfl) ⟨3204251, by rfl⟩ : syracuseStep 4272335 = 6408503) B6408503
theorem B2847055 : Blo 1686043 2847055 := bstep (se 1 (by rfl) ⟨2135291, by rfl⟩ : syracuseStep 2847055 = 4270583) B4270583
theorem B15389129 : Blo 1686043 15389129 := bstep (se 2 (by rfl) ⟨5770923, by rfl⟩ : syracuseStep 15389129 = 11541847) B11541847
theorem B328430537 : Blo 1686043 328430537 := bstep (se 2 (by rfl) ⟨123161451, by rfl⟩ : syracuseStep 328430537 = 246322903) B246322903
theorem B19223729 : Blo 1686043 19223729 := bstep (se 2 (by rfl) ⟨7208898, by rfl⟩ : syracuseStep 19223729 = 14417797) B14417797
theorem B1897663 : Blo 1686043 1897663 := bstep (se 1 (by rfl) ⟨1423247, by rfl⟩ : syracuseStep 1897663 = 2846495) B2846495
theorem B9606397 : Blo 1686043 9606397 := bstep (se 3 (by rfl) ⟨1801199, by rfl⟩ : syracuseStep 9606397 = 3602399) B3602399
theorem B8541449 : Blo 1686043 8541449 := bstep (se 2 (by rfl) ⟨3203043, by rfl⟩ : syracuseStep 8541449 = 6406087) B6406087
theorem B1897807 : Blo 1686043 1897807 := bstep (se 1 (by rfl) ⟨1423355, by rfl⟩ : syracuseStep 1897807 = 2846711) B2846711
theorem B4052393 : Blo 1686043 4052393 := bstep (se 2 (by rfl) ⟨1519647, by rfl⟩ : syracuseStep 4052393 = 3039295) B3039295
theorem B6403657 : Blo 1686043 6403657 := bstep (se 2 (by rfl) ⟨2401371, by rfl⟩ : syracuseStep 6403657 = 4802743) B4802743
theorem B720549593 : Blo 1686043 720549593 := bstep (se 2 (by rfl) ⟨270206097, by rfl⟩ : syracuseStep 720549593 = 540412195) B540412195
theorem B8107859 : Blo 1686043 8107859 := bstep (se 1 (by rfl) ⟨6080894, by rfl⟩ : syracuseStep 8107859 = 12161789) B12161789
theorem B8771453 : Blo 1686043 8771453 := bstep (se 3 (by rfl) ⟨1644647, by rfl⟩ : syracuseStep 8771453 = 3289295) B3289295
theorem B18249695 : Blo 1686043 18249695 := bstep (se 1 (by rfl) ⟨13687271, by rfl⟩ : syracuseStep 18249695 = 27374543) B27374543
theorem B1898527 : Blo 1686043 1898527 := bstep (se 1 (by rfl) ⟨1423895, by rfl⟩ : syracuseStep 1898527 = 2847791) B2847791
theorem B5404727 : Blo 1686043 5404727 := bstep (se 1 (by rfl) ⟨4053545, by rfl⟩ : syracuseStep 5404727 = 8107091) B8107091
theorem B2136127 : Blo 1686043 2136127 := bstep (se 1 (by rfl) ⟨1602095, by rfl⟩ : syracuseStep 2136127 = 3204191) B3204191
theorem B2529503 : Blo 1686043 2529503 := bstep (se 1 (by rfl) ⟨1897127, by rfl⟩ : syracuseStep 2529503 = 3794255) B3794255
theorem B10541431 : Blo 1686043 10541431 := bstep (se 1 (by rfl) ⟨7906073, by rfl⟩ : syracuseStep 10541431 = 15812147) B15812147
theorem B2529983 : Blo 1686043 2529983 := bstep (se 1 (by rfl) ⟨1897487, by rfl⟩ : syracuseStep 2529983 = 3794975) B3794975
theorem B240261875 : Blo 1686043 240261875 := bstep (se 1 (by rfl) ⟨180196406, by rfl⟩ : syracuseStep 240261875 = 360392813) B360392813
theorem B1686271 : Blo 1686043 1686271 := bstep (se 1 (by rfl) ⟨1264703, by rfl⟩ : syracuseStep 1686271 = 2529407) B2529407
theorem B10804175 : Blo 1686043 10804175 := bstep (se 1 (by rfl) ⟨8103131, by rfl⟩ : syracuseStep 10804175 = 16206263) B16206263
theorem B1686683 : Blo 1686043 1686683 := bstep (se 1 (by rfl) ⟨1265012, by rfl⟩ : syracuseStep 1686683 = 2530025) B2530025
theorem B2530463 : Blo 1686043 2530463 := bstep (se 1 (by rfl) ⟨1897847, by rfl⟩ : syracuseStep 2530463 = 3795695) B3795695
theorem B77872373 : Blo 1686043 77872373 := bstep (se 5 (by rfl) ⟨3650267, by rfl⟩ : syracuseStep 77872373 = 7300535) B7300535
theorem B54721817 : Blo 1686043 54721817 := bstep (se 2 (by rfl) ⟨20520681, by rfl⟩ : syracuseStep 54721817 = 41041363) B41041363
theorem B2530601 : Blo 1686043 2530601 := bstep (se 2 (by rfl) ⟨948975, by rfl⟩ : syracuseStep 2530601 = 1897951) B1897951
theorem B24329807 : Blo 1686043 24329807 := bstep (se 1 (by rfl) ⟨18247355, by rfl⟩ : syracuseStep 24329807 = 36494711) B36494711
theorem B6078347 : Blo 1686043 6078347 := bstep (se 1 (by rfl) ⟨4558760, by rfl⟩ : syracuseStep 6078347 = 9117521) B9117521
theorem B2531369 : Blo 1686043 2531369 := bstep (se 2 (by rfl) ⟨949263, by rfl⟩ : syracuseStep 2531369 = 1898527) B1898527
theorem B2531399 : Blo 1686043 2531399 := bstep (se 1 (by rfl) ⟨1898549, by rfl⟩ : syracuseStep 2531399 = 3797099) B3797099
theorem B1687623 : Blo 1686043 1687623 := bstep (se 1 (by rfl) ⟨1265717, by rfl⟩ : syracuseStep 1687623 = 2531435) B2531435
theorem B4268123 : Blo 1686043 4268123 := bstep (se 1 (by rfl) ⟨3201092, by rfl⟩ : syracuseStep 4268123 = 6402185) B6402185
theorem B1687643 : Blo 1686043 1687643 := bstep (se 1 (by rfl) ⟨1265732, by rfl⟩ : syracuseStep 1687643 = 2531465) B2531465
theorem B5406983 : Blo 1686043 5406983 := bstep (se 1 (by rfl) ⟨4055237, by rfl⟩ : syracuseStep 5406983 = 8110475) B8110475
theorem B5693705 : Blo 1686043 5693705 := bstep (se 2 (by rfl) ⟨2135139, by rfl⟩ : syracuseStep 5693705 = 4270279) B4270279
theorem B5694299 : Blo 1686043 5694299 := bstep (se 1 (by rfl) ⟨4270724, by rfl⟩ : syracuseStep 5694299 = 8541449) B8541449
theorem B8537399 : Blo 1686043 8537399 := bstep (se 1 (by rfl) ⟨6403049, by rfl⟩ : syracuseStep 8537399 = 12806099) B12806099
theorem B12166463 : Blo 1686043 12166463 := bstep (se 1 (by rfl) ⟨9124847, by rfl⟩ : syracuseStep 12166463 = 18249695) B18249695
theorem B3794345 : Blo 1686043 3794345 := bstep (se 2 (by rfl) ⟨1422879, by rfl⟩ : syracuseStep 3794345 = 2845759) B2845759
theorem B24651229 : Blo 1686043 24651229 := bstep (se 3 (by rfl) ⟨4622105, by rfl⟩ : syracuseStep 24651229 = 9244211) B9244211
theorem B2885257 : Blo 1686043 2885257 := bstep (se 2 (by rfl) ⟨1081971, by rfl⟩ : syracuseStep 2885257 = 2163943) B2163943
theorem B10258201 : Blo 1686043 10258201 := bstep (se 2 (by rfl) ⟨3846825, by rfl⟩ : syracuseStep 10258201 = 7693651) B7693651
theorem B8538047 : Blo 1686043 8538047 := bstep (se 1 (by rfl) ⟨6403535, by rfl⟩ : syracuseStep 8538047 = 12807071) B12807071
theorem B7202783 : Blo 1686043 7202783 := bstep (se 1 (by rfl) ⟨5402087, by rfl⟩ : syracuseStep 7202783 = 10804175) B10804175
theorem B12814361 : Blo 1686043 12814361 := bstep (se 2 (by rfl) ⟨4805385, by rfl⟩ : syracuseStep 12814361 = 9610771) B9610771
theorem B8538209 : Blo 1686043 8538209 := bstep (se 2 (by rfl) ⟨3201828, by rfl⟩ : syracuseStep 8538209 = 6403657) B6403657
theorem B51914915 : Blo 1686043 51914915 := bstep (se 1 (by rfl) ⟨38936186, by rfl⟩ : syracuseStep 51914915 = 77872373) B77872373
theorem B36481211 : Blo 1686043 36481211 := bstep (se 1 (by rfl) ⟨27360908, by rfl⟩ : syracuseStep 36481211 = 54721817) B54721817
theorem B18246491 : Blo 1686043 18246491 := bstep (se 1 (by rfl) ⟨13684868, by rfl⟩ : syracuseStep 18246491 = 27369737) B27369737
theorem B2845631 : Blo 1686043 2845631 := bstep (se 1 (by rfl) ⟨2134223, by rfl⟩ : syracuseStep 2845631 = 4268447) B4268447
theorem B10259419 : Blo 1686043 10259419 := bstep (se 1 (by rfl) ⟨7694564, by rfl⟩ : syracuseStep 10259419 = 15389129) B15389129
theorem B3796073 : Blo 1686043 3796073 := bstep (se 2 (by rfl) ⟨1423527, by rfl⟩ : syracuseStep 3796073 = 2847055) B2847055
theorem B9612503 : Blo 1686043 9612503 := bstep (se 1 (by rfl) ⟨7209377, by rfl⟩ : syracuseStep 9612503 = 14418755) B14418755
theorem B5401883 : Blo 1686043 5401883 := bstep (se 1 (by rfl) ⟨4051412, by rfl⟩ : syracuseStep 5401883 = 8102825) B8102825
theorem B3796307 : Blo 1686043 3796307 := bstep (se 1 (by rfl) ⟨2847230, by rfl⟩ : syracuseStep 3796307 = 5694461) B5694461
theorem B3796415 : Blo 1686043 3796415 := bstep (se 1 (by rfl) ⟨2847311, by rfl⟩ : syracuseStep 3796415 = 5694623) B5694623
theorem B12815819 : Blo 1686043 12815819 := bstep (se 1 (by rfl) ⟨9611864, by rfl⟩ : syracuseStep 12815819 = 19223729) B19223729
theorem B5696999 : Blo 1686043 5696999 := bstep (se 1 (by rfl) ⟨4272749, by rfl⟩ : syracuseStep 5696999 = 8545499) B8545499
theorem B2846191 : Blo 1686043 2846191 := bstep (se 1 (by rfl) ⟨2134643, by rfl⟩ : syracuseStep 2846191 = 4269287) B4269287
theorem B12987935 : Blo 1686043 12987935 := bstep (se 1 (by rfl) ⟨9740951, by rfl⟩ : syracuseStep 12987935 = 19481903) B19481903
theorem B480366395 : Blo 1686043 480366395 := bstep (se 1 (by rfl) ⟨360274796, by rfl⟩ : syracuseStep 480366395 = 720549593) B720549593
theorem B4108267 : Blo 1686043 4108267 := bstep (se 1 (by rfl) ⟨3081200, by rfl⟩ : syracuseStep 4108267 = 6162401) B6162401
theorem B21623111 : Blo 1686043 21623111 := bstep (se 1 (by rfl) ⟨16217333, by rfl⟩ : syracuseStep 21623111 = 32434667) B32434667
theorem B12808529 : Blo 1686043 12808529 := bstep (se 2 (by rfl) ⟨4803198, by rfl⟩ : syracuseStep 12808529 = 9606397) B9606397
theorem B160174583 : Blo 1686043 160174583 := bstep (se 1 (by rfl) ⟨120130937, by rfl⟩ : syracuseStep 160174583 = 240261875) B240261875
theorem B12809015 : Blo 1686043 12809015 := bstep (se 1 (by rfl) ⟨9606761, by rfl⟩ : syracuseStep 12809015 = 19213523) B19213523
theorem B3601435 : Blo 1686043 3601435 := bstep (se 1 (by rfl) ⟨2701076, by rfl⟩ : syracuseStep 3601435 = 5402153) B5402153
theorem B5772541 : Blo 1686043 5772541 := bstep (se 3 (by rfl) ⟨1082351, by rfl⟩ : syracuseStep 5772541 = 2164703) B2164703
theorem B4052231 : Blo 1686043 4052231 := bstep (se 1 (by rfl) ⟨3039173, by rfl⟩ : syracuseStep 4052231 = 6078347) B6078347
theorem B2848169 : Blo 1686043 2848169 := bstep (se 2 (by rfl) ⟨1068063, by rfl⟩ : syracuseStep 2848169 = 2136127) B2136127
theorem B2848223 : Blo 1686043 2848223 := bstep (se 1 (by rfl) ⟨2136167, by rfl⟩ : syracuseStep 2848223 = 4272335) B4272335
theorem B14055241 : Blo 1686043 14055241 := bstep (se 2 (by rfl) ⟨5270715, by rfl⟩ : syracuseStep 14055241 = 10541431) B10541431
theorem B2529179 : Blo 1686043 2529179 := bstep (se 1 (by rfl) ⟨1896884, by rfl⟩ : syracuseStep 2529179 = 3793769) B3793769
theorem B2529215 : Blo 1686043 2529215 := bstep (se 1 (by rfl) ⟨1896911, by rfl⟩ : syracuseStep 2529215 = 3793823) B3793823
theorem B218953691 : Blo 1686043 218953691 := bstep (se 1 (by rfl) ⟨164215268, by rfl⟩ : syracuseStep 218953691 = 328430537) B328430537
theorem B2529383 : Blo 1686043 2529383 := bstep (se 1 (by rfl) ⟨1897037, by rfl⟩ : syracuseStep 2529383 = 3794075) B3794075
theorem B3201191 : Blo 1686043 3201191 := bstep (se 1 (by rfl) ⟨2400893, by rfl⟩ : syracuseStep 3201191 = 4801787) B4801787
theorem B2701595 : Blo 1686043 2701595 := bstep (se 1 (by rfl) ⟨2026196, by rfl⟩ : syracuseStep 2701595 = 4052393) B4052393
theorem B6838607 : Blo 1686043 6838607 := bstep (se 1 (by rfl) ⟨5128955, by rfl⟩ : syracuseStep 6838607 = 10257911) B10257911
theorem B5405239 : Blo 1686043 5405239 := bstep (se 1 (by rfl) ⟨4053929, by rfl⟩ : syracuseStep 5405239 = 8107859) B8107859
theorem B5847635 : Blo 1686043 5847635 := bstep (se 1 (by rfl) ⟨4385726, by rfl⟩ : syracuseStep 5847635 = 8771453) B8771453
theorem B3603151 : Blo 1686043 3603151 := bstep (se 1 (by rfl) ⟨2702363, by rfl⟩ : syracuseStep 3603151 = 5404727) B5404727
theorem B1686335 : Blo 1686043 1686335 := bstep (se 1 (by rfl) ⟨1264751, by rfl⟩ : syracuseStep 1686335 = 2529503) B2529503
theorem B2530217 : Blo 1686043 2530217 := bstep (se 2 (by rfl) ⟨948831, by rfl⟩ : syracuseStep 2530217 = 1897663) B1897663
theorem B5774291 : Blo 1686043 5774291 := bstep (se 1 (by rfl) ⟨4330718, by rfl⟩ : syracuseStep 5774291 = 8661437) B8661437
theorem B2530271 : Blo 1686043 2530271 := bstep (se 1 (by rfl) ⟨1897703, by rfl⟩ : syracuseStep 2530271 = 3795407) B3795407
theorem B2530409 : Blo 1686043 2530409 := bstep (se 2 (by rfl) ⟨948903, by rfl⟩ : syracuseStep 2530409 = 1897807) B1897807
theorem B1686655 : Blo 1686043 1686655 := bstep (se 1 (by rfl) ⟨1264991, by rfl⟩ : syracuseStep 1686655 = 2529983) B2529983
theorem B1686975 : Blo 1686043 1686975 := bstep (se 1 (by rfl) ⟨1265231, by rfl⟩ : syracuseStep 1686975 = 2530463) B2530463
theorem B1687067 : Blo 1686043 1687067 := bstep (se 1 (by rfl) ⟨1265300, by rfl⟩ : syracuseStep 1687067 = 2530601) B2530601
theorem B16219871 : Blo 1686043 16219871 := bstep (se 1 (by rfl) ⟨12164903, by rfl⟩ : syracuseStep 16219871 = 24329807) B24329807
theorem B2531135 : Blo 1686043 2531135 := bstep (se 1 (by rfl) ⟨1898351, by rfl⟩ : syracuseStep 2531135 = 3796703) B3796703
theorem B1687579 : Blo 1686043 1687579 := bstep (se 1 (by rfl) ⟨1265684, by rfl⟩ : syracuseStep 1687579 = 2531369) B2531369
theorem B1687599 : Blo 1686043 1687599 := bstep (se 1 (by rfl) ⟨1265699, by rfl⟩ : syracuseStep 1687599 = 2531399) B2531399
theorem B3604655 : Blo 1686043 3604655 := bstep (se 1 (by rfl) ⟨2703491, by rfl⟩ : syracuseStep 3604655 = 5406983) B5406983
theorem B106783055 : Blo 1686043 106783055 := bstep (se 1 (by rfl) ⟨80087291, by rfl⟩ : syracuseStep 106783055 = 160174583) B160174583
theorem B18236285 : Blo 1686043 18236285 := bstep (se 3 (by rfl) ⟨3419303, by rfl⟩ : syracuseStep 18236285 = 6838607) B6838607
theorem B8110975 : Blo 1686043 8110975 := bstep (se 1 (by rfl) ⟨6083231, by rfl⟩ : syracuseStep 8110975 = 12166463) B12166463
theorem B4801855 : Blo 1686043 4801855 := bstep (se 1 (by rfl) ⟨3601391, by rfl⟩ : syracuseStep 4801855 = 7202783) B7202783
theorem B4801913 : Blo 1686043 4801913 := bstep (se 2 (by rfl) ⟨1800717, by rfl⟩ : syracuseStep 4801913 = 3601435) B3601435
theorem B32868305 : Blo 1686043 32868305 := bstep (se 2 (by rfl) ⟨12325614, by rfl⟩ : syracuseStep 32868305 = 24651229) B24651229
theorem B3794921 : Blo 1686043 3794921 := bstep (se 2 (by rfl) ⟨1423095, by rfl⟩ : syracuseStep 3794921 = 2846191) B2846191
theorem B6408335 : Blo 1686043 6408335 := bstep (se 1 (by rfl) ⟨4806251, by rfl⟩ : syracuseStep 6408335 = 9612503) B9612503
theorem B320244263 : Blo 1686043 320244263 := bstep (se 1 (by rfl) ⟨240183197, by rfl⟩ : syracuseStep 320244263 = 480366395) B480366395
theorem B2845415 : Blo 1686043 2845415 := bstep (se 1 (by rfl) ⟨2134061, by rfl⟩ : syracuseStep 2845415 = 4268123) B4268123
theorem B3795803 : Blo 1686043 3795803 := bstep (se 1 (by rfl) ⟨2846852, by rfl⟩ : syracuseStep 3795803 = 5693705) B5693705
theorem B8539019 : Blo 1686043 8539019 := bstep (se 1 (by rfl) ⟨6404264, by rfl⟩ : syracuseStep 8539019 = 12808529) B12808529
theorem B8539343 : Blo 1686043 8539343 := bstep (se 1 (by rfl) ⟨6404507, by rfl⟩ : syracuseStep 8539343 = 12809015) B12809015
theorem B3796199 : Blo 1686043 3796199 := bstep (se 1 (by rfl) ⟨2847149, by rfl⟩ : syracuseStep 3796199 = 5694299) B5694299
theorem B4804201 : Blo 1686043 4804201 := bstep (se 2 (by rfl) ⟨1801575, by rfl⟩ : syracuseStep 4804201 = 3603151) B3603151
theorem B145969127 : Blo 1686043 145969127 := bstep (se 1 (by rfl) ⟨109476845, by rfl⟩ : syracuseStep 145969127 = 218953691) B218953691
theorem B2134127 : Blo 1686043 2134127 := bstep (se 1 (by rfl) ⟨1600595, by rfl⟩ : syracuseStep 2134127 = 3201191) B3201191
theorem B7696721 : Blo 1686043 7696721 := bstep (se 2 (by rfl) ⟨2886270, by rfl⟩ : syracuseStep 7696721 = 5772541) B5772541
theorem B1897087 : Blo 1686043 1897087 := bstep (se 1 (by rfl) ⟨1422815, by rfl⟩ : syracuseStep 1897087 = 2845631) B2845631
theorem B3847009 : Blo 1686043 3847009 := bstep (se 2 (by rfl) ⟨1442628, by rfl⟩ : syracuseStep 3847009 = 2885257) B2885257
theorem B3601255 : Blo 1686043 3601255 := bstep (se 1 (by rfl) ⟨2700941, by rfl⟩ : syracuseStep 3601255 = 5401883) B5401883
theorem B3797999 : Blo 1686043 3797999 := bstep (se 1 (by rfl) ⟨2848499, by rfl⟩ : syracuseStep 3797999 = 5696999) B5696999
theorem B13677601 : Blo 1686043 13677601 := bstep (se 2 (by rfl) ⟨5129100, by rfl⟩ : syracuseStep 13677601 = 10258201) B10258201
theorem B18740321 : Blo 1686043 18740321 := bstep (se 2 (by rfl) ⟨7027620, by rfl⟩ : syracuseStep 18740321 = 14055241) B14055241
theorem B5477689 : Blo 1686043 5477689 := bstep (se 2 (by rfl) ⟨2054133, by rfl⟩ : syracuseStep 5477689 = 4108267) B4108267
theorem B14415407 : Blo 1686043 14415407 := bstep (se 1 (by rfl) ⟨10811555, by rfl⟩ : syracuseStep 14415407 = 21623111) B21623111
theorem B7206985 : Blo 1686043 7206985 := bstep (se 2 (by rfl) ⟨2702619, by rfl⟩ : syracuseStep 7206985 = 5405239) B5405239
theorem B2701487 : Blo 1686043 2701487 := bstep (se 1 (by rfl) ⟨2026115, by rfl⟩ : syracuseStep 2701487 = 4052231) B4052231
theorem B5691599 : Blo 1686043 5691599 := bstep (se 1 (by rfl) ⟨4268699, by rfl⟩ : syracuseStep 5691599 = 8537399) B8537399
theorem B2529563 : Blo 1686043 2529563 := bstep (se 1 (by rfl) ⟨1897172, by rfl⟩ : syracuseStep 2529563 = 3794345) B3794345
theorem B1898779 : Blo 1686043 1898779 := bstep (se 1 (by rfl) ⟨1424084, by rfl⟩ : syracuseStep 1898779 = 2848169) B2848169
theorem B1898815 : Blo 1686043 1898815 := bstep (se 1 (by rfl) ⟨1424111, by rfl⟩ : syracuseStep 1898815 = 2848223) B2848223
theorem B1686119 : Blo 1686043 1686119 := bstep (se 1 (by rfl) ⟨1264589, by rfl⟩ : syracuseStep 1686119 = 2529179) B2529179
theorem B13679225 : Blo 1686043 13679225 := bstep (se 2 (by rfl) ⟨5129709, by rfl⟩ : syracuseStep 13679225 = 10259419) B10259419
theorem B1686143 : Blo 1686043 1686143 := bstep (se 1 (by rfl) ⟨1264607, by rfl⟩ : syracuseStep 1686143 = 2529215) B2529215
theorem B5692031 : Blo 1686043 5692031 := bstep (se 1 (by rfl) ⟨4269023, by rfl⟩ : syracuseStep 5692031 = 8538047) B8538047
theorem B8542907 : Blo 1686043 8542907 := bstep (se 1 (by rfl) ⟨6407180, by rfl⟩ : syracuseStep 8542907 = 12814361) B12814361
theorem B5692139 : Blo 1686043 5692139 := bstep (se 1 (by rfl) ⟨4269104, by rfl⟩ : syracuseStep 5692139 = 8538209) B8538209
theorem B1686255 : Blo 1686043 1686255 := bstep (se 1 (by rfl) ⟨1264691, by rfl⟩ : syracuseStep 1686255 = 2529383) B2529383
theorem B34609943 : Blo 1686043 34609943 := bstep (se 1 (by rfl) ⟨25957457, by rfl⟩ : syracuseStep 34609943 = 51914915) B51914915
theorem B24320807 : Blo 1686043 24320807 := bstep (se 1 (by rfl) ⟨18240605, by rfl⟩ : syracuseStep 24320807 = 36481211) B36481211
theorem B1801063 : Blo 1686043 1801063 := bstep (se 1 (by rfl) ⟨1350797, by rfl⟩ : syracuseStep 1801063 = 2701595) B2701595
theorem B3898423 : Blo 1686043 3898423 := bstep (se 1 (by rfl) ⟨2923817, by rfl⟩ : syracuseStep 3898423 = 5847635) B5847635
theorem B12164327 : Blo 1686043 12164327 := bstep (se 1 (by rfl) ⟨9123245, by rfl⟩ : syracuseStep 12164327 = 18246491) B18246491
theorem B1686811 : Blo 1686043 1686811 := bstep (se 1 (by rfl) ⟨1265108, by rfl⟩ : syracuseStep 1686811 = 2530217) B2530217
theorem B3849527 : Blo 1686043 3849527 := bstep (se 1 (by rfl) ⟨2887145, by rfl⟩ : syracuseStep 3849527 = 5774291) B5774291
theorem B1686847 : Blo 1686043 1686847 := bstep (se 1 (by rfl) ⟨1265135, by rfl⟩ : syracuseStep 1686847 = 2530271) B2530271
theorem B1686939 : Blo 1686043 1686939 := bstep (se 1 (by rfl) ⟨1265204, by rfl⟩ : syracuseStep 1686939 = 2530409) B2530409
theorem B2530715 : Blo 1686043 2530715 := bstep (se 1 (by rfl) ⟨1898036, by rfl⟩ : syracuseStep 2530715 = 3796073) B3796073
theorem B2530871 : Blo 1686043 2530871 := bstep (se 1 (by rfl) ⟨1898153, by rfl⟩ : syracuseStep 2530871 = 3796307) B3796307
theorem B2530943 : Blo 1686043 2530943 := bstep (se 1 (by rfl) ⟨1898207, by rfl⟩ : syracuseStep 2530943 = 3796415) B3796415
theorem B8543879 : Blo 1686043 8543879 := bstep (se 1 (by rfl) ⟨6407909, by rfl⟩ : syracuseStep 8543879 = 12815819) B12815819
theorem B8658623 : Blo 1686043 8658623 := bstep (se 1 (by rfl) ⟨6493967, by rfl⟩ : syracuseStep 8658623 = 12987935) B12987935
theorem B10813247 : Blo 1686043 10813247 := bstep (se 1 (by rfl) ⟨8109935, by rfl⟩ : syracuseStep 10813247 = 16219871) B16219871
theorem B1687423 : Blo 1686043 1687423 := bstep (se 1 (by rfl) ⟨1265567, by rfl⟩ : syracuseStep 1687423 = 2531135) B2531135
theorem B9609313 : Blo 1686043 9609313 := bstep (se 2 (by rfl) ⟨3603492, by rfl⟩ : syracuseStep 9609313 = 7206985) B7206985
theorem B71188703 : Blo 1686043 71188703 := bstep (se 1 (by rfl) ⟨53391527, by rfl⟩ : syracuseStep 71188703 = 106783055) B106783055
theorem B2531705 : Blo 1686043 2531705 := bstep (se 2 (by rfl) ⟨949389, by rfl⟩ : syracuseStep 2531705 = 1898779) B1898779
theorem B2531753 : Blo 1686043 2531753 := bstep (se 2 (by rfl) ⟨949407, by rfl⟩ : syracuseStep 2531753 = 1898815) B1898815
theorem B12157523 : Blo 1686043 12157523 := bstep (se 1 (by rfl) ⟨9118142, by rfl⟩ : syracuseStep 12157523 = 18236285) B18236285
theorem B2531999 : Blo 1686043 2531999 := bstep (se 1 (by rfl) ⟨1898999, by rfl⟩ : syracuseStep 2531999 = 3797999) B3797999
theorem B12493547 : Blo 1686043 12493547 := bstep (se 1 (by rfl) ⟨9370160, by rfl⟩ : syracuseStep 12493547 = 18740321) B18740321
theorem B9610271 : Blo 1686043 9610271 := bstep (se 1 (by rfl) ⟨7207703, by rfl⟩ : syracuseStep 9610271 = 14415407) B14415407
theorem B5129345 : Blo 1686043 5129345 := bstep (se 2 (by rfl) ⟨1923504, by rfl⟩ : syracuseStep 5129345 = 3847009) B3847009
theorem B4801673 : Blo 1686043 4801673 := bstep (se 2 (by rfl) ⟨1800627, by rfl⟩ : syracuseStep 4801673 = 3601255) B3601255
theorem B2401417 : Blo 1686043 2401417 := bstep (se 2 (by rfl) ⟨900531, by rfl⟩ : syracuseStep 2401417 = 1801063) B1801063
theorem B10814633 : Blo 1686043 10814633 := bstep (se 2 (by rfl) ⟨4055487, by rfl⟩ : syracuseStep 10814633 = 8110975) B8110975
theorem B18236801 : Blo 1686043 18236801 := bstep (se 2 (by rfl) ⟨6838800, by rfl⟩ : syracuseStep 18236801 = 13677601) B13677601
theorem B3794399 : Blo 1686043 3794399 := bstep (se 1 (by rfl) ⟨2845799, by rfl⟩ : syracuseStep 3794399 = 5691599) B5691599
theorem B29214341 : Blo 1686043 29214341 := bstep (se 4 (by rfl) ⟨2738844, by rfl⟩ : syracuseStep 29214341 = 5477689) B5477689
theorem B9119483 : Blo 1686043 9119483 := bstep (se 1 (by rfl) ⟨6839612, by rfl⟩ : syracuseStep 9119483 = 13679225) B13679225
theorem B3794687 : Blo 1686043 3794687 := bstep (se 1 (by rfl) ⟨2846015, by rfl⟩ : syracuseStep 3794687 = 5692031) B5692031
theorem B5695271 : Blo 1686043 5695271 := bstep (se 1 (by rfl) ⟨4271453, by rfl⟩ : syracuseStep 5695271 = 8542907) B8542907
theorem B3794759 : Blo 1686043 3794759 := bstep (se 1 (by rfl) ⟨2846069, by rfl⟩ : syracuseStep 3794759 = 5692139) B5692139
theorem B16213871 : Blo 1686043 16213871 := bstep (se 1 (by rfl) ⟨12160403, by rfl⟩ : syracuseStep 16213871 = 24320807) B24320807
theorem B2566351 : Blo 1686043 2566351 := bstep (se 1 (by rfl) ⟨1924763, by rfl⟩ : syracuseStep 2566351 = 3849527) B3849527
theorem B5695919 : Blo 1686043 5695919 := bstep (se 1 (by rfl) ⟨4271939, by rfl⟩ : syracuseStep 5695919 = 8543879) B8543879
theorem B2403103 : Blo 1686043 2403103 := bstep (se 1 (by rfl) ⟨1802327, by rfl⟩ : syracuseStep 2403103 = 3604655) B3604655
theorem B5131147 : Blo 1686043 5131147 := bstep (se 1 (by rfl) ⟨3848360, by rfl⟩ : syracuseStep 5131147 = 7696721) B7696721
theorem B5197897 : Blo 1686043 5197897 := bstep (se 2 (by rfl) ⟨1949211, by rfl⟩ : syracuseStep 5197897 = 3898423) B3898423
theorem B4272223 : Blo 1686043 4272223 := bstep (se 1 (by rfl) ⟨3204167, by rfl⟩ : syracuseStep 4272223 = 6408335) B6408335
theorem B213496175 : Blo 1686043 213496175 := bstep (se 1 (by rfl) ⟨160122131, by rfl⟩ : syracuseStep 213496175 = 320244263) B320244263
theorem B6402473 : Blo 1686043 6402473 := bstep (se 2 (by rfl) ⟨2400927, by rfl⟩ : syracuseStep 6402473 = 4801855) B4801855
theorem B1896943 : Blo 1686043 1896943 := bstep (se 1 (by rfl) ⟨1422707, by rfl⟩ : syracuseStep 1896943 = 2845415) B2845415
theorem B23073295 : Blo 1686043 23073295 := bstep (se 1 (by rfl) ⟨17304971, by rfl⟩ : syracuseStep 23073295 = 34609943) B34609943
theorem B5772415 : Blo 1686043 5772415 := bstep (se 1 (by rfl) ⟨4329311, by rfl⟩ : syracuseStep 5772415 = 8658623) B8658623
theorem B5691005 : Blo 1686043 5691005 := bstep (se 3 (by rfl) ⟨1067063, by rfl⟩ : syracuseStep 5691005 = 2134127) B2134127
theorem B2529449 : Blo 1686043 2529449 := bstep (se 2 (by rfl) ⟨948543, by rfl⟩ : syracuseStep 2529449 = 1897087) B1897087
theorem B3201275 : Blo 1686043 3201275 := bstep (se 1 (by rfl) ⟨2400956, by rfl⟩ : syracuseStep 3201275 = 4801913) B4801913
theorem B21912203 : Blo 1686043 21912203 := bstep (se 1 (by rfl) ⟨16434152, by rfl⟩ : syracuseStep 21912203 = 32868305) B32868305
theorem B2529947 : Blo 1686043 2529947 := bstep (se 1 (by rfl) ⟨1897460, by rfl⟩ : syracuseStep 2529947 = 3794921) B3794921
theorem B1800991 : Blo 1686043 1800991 := bstep (se 1 (by rfl) ⟨1350743, by rfl⟩ : syracuseStep 1800991 = 2701487) B2701487
theorem B1686375 : Blo 1686043 1686375 := bstep (se 1 (by rfl) ⟨1264781, by rfl⟩ : syracuseStep 1686375 = 2529563) B2529563
theorem B2530535 : Blo 1686043 2530535 := bstep (se 1 (by rfl) ⟨1897901, by rfl⟩ : syracuseStep 2530535 = 3795803) B3795803
theorem B5692679 : Blo 1686043 5692679 := bstep (se 1 (by rfl) ⟨4269509, by rfl⟩ : syracuseStep 5692679 = 8539019) B8539019
theorem B5692895 : Blo 1686043 5692895 := bstep (se 1 (by rfl) ⟨4269671, by rfl⟩ : syracuseStep 5692895 = 8539343) B8539343
theorem B6405601 : Blo 1686043 6405601 := bstep (se 2 (by rfl) ⟨2402100, by rfl⟩ : syracuseStep 6405601 = 4804201) B4804201
theorem B2530799 : Blo 1686043 2530799 := bstep (se 1 (by rfl) ⟨1898099, by rfl⟩ : syracuseStep 2530799 = 3796199) B3796199
theorem B8109551 : Blo 1686043 8109551 := bstep (se 1 (by rfl) ⟨6082163, by rfl⟩ : syracuseStep 8109551 = 12164327) B12164327
theorem B1687143 : Blo 1686043 1687143 := bstep (se 1 (by rfl) ⟨1265357, by rfl⟩ : syracuseStep 1687143 = 2530715) B2530715
theorem B1687247 : Blo 1686043 1687247 := bstep (se 1 (by rfl) ⟨1265435, by rfl⟩ : syracuseStep 1687247 = 2530871) B2530871
theorem B1687295 : Blo 1686043 1687295 := bstep (se 1 (by rfl) ⟨1265471, by rfl⟩ : syracuseStep 1687295 = 2530943) B2530943
theorem B7208831 : Blo 1686043 7208831 := bstep (se 1 (by rfl) ⟨5406623, by rfl⟩ : syracuseStep 7208831 = 10813247) B10813247
theorem B97312751 : Blo 1686043 97312751 := bstep (se 1 (by rfl) ⟨72984563, by rfl⟩ : syracuseStep 97312751 = 145969127) B145969127
theorem B6930529 : Blo 1686043 6930529 := bstep (se 2 (by rfl) ⟨2598948, by rfl⟩ : syracuseStep 6930529 = 5197897) B5197897
theorem B12812417 : Blo 1686043 12812417 := bstep (se 2 (by rfl) ⟨4804656, by rfl⟩ : syracuseStep 12812417 = 9609313) B9609313
theorem B1687803 : Blo 1686043 1687803 := bstep (se 1 (by rfl) ⟨1265852, by rfl⟩ : syracuseStep 1687803 = 2531705) B2531705
theorem B4268315 : Blo 1686043 4268315 := bstep (se 1 (by rfl) ⟨3201236, by rfl⟩ : syracuseStep 4268315 = 6402473) B6402473
theorem B1687835 : Blo 1686043 1687835 := bstep (se 1 (by rfl) ⟨1265876, by rfl⟩ : syracuseStep 1687835 = 2531753) B2531753
theorem B1687999 : Blo 1686043 1687999 := bstep (se 1 (by rfl) ⟨1265999, by rfl⟩ : syracuseStep 1687999 = 2531999) B2531999
theorem B6406847 : Blo 1686043 6406847 := bstep (se 1 (by rfl) ⟨4805135, by rfl⟩ : syracuseStep 6406847 = 9610271) B9610271
theorem B7209755 : Blo 1686043 7209755 := bstep (se 1 (by rfl) ⟨5407316, by rfl⟩ : syracuseStep 7209755 = 10814633) B10814633
theorem B12157867 : Blo 1686043 12157867 := bstep (se 1 (by rfl) ⟨9118400, by rfl⟩ : syracuseStep 12157867 = 18236801) B18236801
theorem B2401321 : Blo 1686043 2401321 := bstep (se 2 (by rfl) ⟨900495, by rfl⟩ : syracuseStep 2401321 = 1800991) B1800991
theorem B3204137 : Blo 1686043 3204137 := bstep (se 2 (by rfl) ⟨1201551, by rfl⟩ : syracuseStep 3204137 = 2403103) B2403103
theorem B3794003 : Blo 1686043 3794003 := bstep (se 1 (by rfl) ⟨2845502, by rfl⟩ : syracuseStep 3794003 = 5691005) B5691005
theorem B6079655 : Blo 1686043 6079655 := bstep (se 1 (by rfl) ⟨4559741, by rfl⟩ : syracuseStep 6079655 = 9119483) B9119483
theorem B6841529 : Blo 1686043 6841529 := bstep (se 2 (by rfl) ⟨2565573, by rfl⟩ : syracuseStep 6841529 = 5131147) B5131147
theorem B14608135 : Blo 1686043 14608135 := bstep (se 1 (by rfl) ⟨10956101, by rfl⟩ : syracuseStep 14608135 = 21912203) B21912203
theorem B3795119 : Blo 1686043 3795119 := bstep (se 1 (by rfl) ⟨2846339, by rfl⟩ : syracuseStep 3795119 = 5692679) B5692679
theorem B3795263 : Blo 1686043 3795263 := bstep (se 1 (by rfl) ⟨2846447, by rfl⟩ : syracuseStep 3795263 = 5692895) B5692895
theorem B64875167 : Blo 1686043 64875167 := bstep (se 1 (by rfl) ⟨48656375, by rfl⟩ : syracuseStep 64875167 = 97312751) B97312751
theorem B5696297 : Blo 1686043 5696297 := bstep (se 2 (by rfl) ⟨2136111, by rfl⟩ : syracuseStep 5696297 = 4272223) B4272223
theorem B47459135 : Blo 1686043 47459135 := bstep (se 1 (by rfl) ⟨35594351, by rfl⟩ : syracuseStep 47459135 = 71188703) B71188703
theorem B142330783 : Blo 1686043 142330783 := bstep (se 1 (by rfl) ⟨106748087, by rfl⟩ : syracuseStep 142330783 = 213496175) B213496175
theorem B8105015 : Blo 1686043 8105015 := bstep (se 1 (by rfl) ⟨6078761, by rfl⟩ : syracuseStep 8105015 = 12157523) B12157523
theorem B30764393 : Blo 1686043 30764393 := bstep (se 2 (by rfl) ⟨11536647, by rfl⟩ : syracuseStep 30764393 = 23073295) B23073295
theorem B12807557 : Blo 1686043 12807557 := bstep (se 4 (by rfl) ⟨1200708, by rfl⟩ : syracuseStep 12807557 = 2401417) B2401417
theorem B3419563 : Blo 1686043 3419563 := bstep (se 1 (by rfl) ⟨2564672, by rfl⟩ : syracuseStep 3419563 = 5129345) B5129345
theorem B19476227 : Blo 1686043 19476227 := bstep (se 1 (by rfl) ⟨14607170, by rfl⟩ : syracuseStep 19476227 = 29214341) B29214341
theorem B3796847 : Blo 1686043 3796847 := bstep (se 1 (by rfl) ⟨2847635, by rfl⟩ : syracuseStep 3796847 = 5695271) B5695271
theorem B2134183 : Blo 1686043 2134183 := bstep (se 1 (by rfl) ⟨1600637, by rfl⟩ : syracuseStep 2134183 = 3201275) B3201275
theorem B7696553 : Blo 1686043 7696553 := bstep (se 2 (by rfl) ⟨2886207, by rfl⟩ : syracuseStep 7696553 = 5772415) B5772415
theorem B3797279 : Blo 1686043 3797279 := bstep (se 1 (by rfl) ⟨2847959, by rfl⟩ : syracuseStep 3797279 = 5695919) B5695919
theorem B8540801 : Blo 1686043 8540801 := bstep (se 2 (by rfl) ⟨3202800, by rfl⟩ : syracuseStep 8540801 = 6405601) B6405601
theorem B4805887 : Blo 1686043 4805887 := bstep (se 1 (by rfl) ⟨3604415, by rfl⟩ : syracuseStep 4805887 = 7208831) B7208831
theorem B3421801 : Blo 1686043 3421801 := bstep (se 2 (by rfl) ⟨1283175, by rfl⟩ : syracuseStep 3421801 = 2566351) B2566351
theorem B8329031 : Blo 1686043 8329031 := bstep (se 1 (by rfl) ⟨6246773, by rfl⟩ : syracuseStep 8329031 = 12493547) B12493547
theorem B2529257 : Blo 1686043 2529257 := bstep (se 2 (by rfl) ⟨948471, by rfl⟩ : syracuseStep 2529257 = 1896943) B1896943
theorem B3201115 : Blo 1686043 3201115 := bstep (se 1 (by rfl) ⟨2400836, by rfl⟩ : syracuseStep 3201115 = 4801673) B4801673
theorem B2529599 : Blo 1686043 2529599 := bstep (se 1 (by rfl) ⟨1897199, by rfl⟩ : syracuseStep 2529599 = 3794399) B3794399
theorem B2529791 : Blo 1686043 2529791 := bstep (se 1 (by rfl) ⟨1897343, by rfl⟩ : syracuseStep 2529791 = 3794687) B3794687
theorem B2529839 : Blo 1686043 2529839 := bstep (se 1 (by rfl) ⟨1897379, by rfl⟩ : syracuseStep 2529839 = 3794759) B3794759
theorem B1686299 : Blo 1686043 1686299 := bstep (se 1 (by rfl) ⟨1264724, by rfl⟩ : syracuseStep 1686299 = 2529449) B2529449
theorem B1686631 : Blo 1686043 1686631 := bstep (se 1 (by rfl) ⟨1264973, by rfl⟩ : syracuseStep 1686631 = 2529947) B2529947
theorem B1687023 : Blo 1686043 1687023 := bstep (se 1 (by rfl) ⟨1265267, by rfl⟩ : syracuseStep 1687023 = 2530535) B2530535
theorem B43236989 : Blo 1686043 43236989 := bstep (se 3 (by rfl) ⟨8106935, by rfl⟩ : syracuseStep 43236989 = 16213871) B16213871
theorem B1687199 : Blo 1686043 1687199 := bstep (se 1 (by rfl) ⟨1265399, by rfl⟩ : syracuseStep 1687199 = 2530799) B2530799
theorem B5406367 : Blo 1686043 5406367 := bstep (se 1 (by rfl) ⟨4054775, by rfl⟩ : syracuseStep 5406367 = 8109551) B8109551
theorem B8544365 : Blo 1686043 8544365 := bstep (se 3 (by rfl) ⟨1602068, by rfl⟩ : syracuseStep 8544365 = 3204137) B3204137
theorem B4268153 : Blo 1686043 4268153 := bstep (se 2 (by rfl) ⟨1600557, by rfl⟩ : syracuseStep 4268153 = 3201115) B3201115
theorem B2531519 : Blo 1686043 2531519 := bstep (se 1 (by rfl) ⟨1898639, by rfl⟩ : syracuseStep 2531519 = 3797279) B3797279
theorem B5693867 : Blo 1686043 5693867 := bstep (se 1 (by rfl) ⟨4270400, by rfl⟩ : syracuseStep 5693867 = 8540801) B8540801
theorem B16212413 : Blo 1686043 16212413 := bstep (se 3 (by rfl) ⟨3039827, by rfl⟩ : syracuseStep 16212413 = 6079655) B6079655
theorem B36962821 : Blo 1686043 36962821 := bstep (se 4 (by rfl) ⟨3465264, by rfl⟩ : syracuseStep 36962821 = 6930529) B6930529
theorem B6407849 : Blo 1686043 6407849 := bstep (se 2 (by rfl) ⟨2402943, by rfl⟩ : syracuseStep 6407849 = 4805887) B4805887
theorem B31639423 : Blo 1686043 31639423 := bstep (se 1 (by rfl) ⟨23729567, by rfl⟩ : syracuseStep 31639423 = 47459135) B47459135
theorem B8538371 : Blo 1686043 8538371 := bstep (se 1 (by rfl) ⟨6403778, by rfl⟩ : syracuseStep 8538371 = 12807557) B12807557
theorem B2845543 : Blo 1686043 2845543 := bstep (se 1 (by rfl) ⟨2134157, by rfl⟩ : syracuseStep 2845543 = 4268315) B4268315
theorem B2845577 : Blo 1686043 2845577 := bstep (se 2 (by rfl) ⟨1067091, by rfl⟩ : syracuseStep 2845577 = 2134183) B2134183
theorem B20524141 : Blo 1686043 20524141 := bstep (se 3 (by rfl) ⟨3848276, by rfl⟩ : syracuseStep 20524141 = 7696553) B7696553
theorem B4271231 : Blo 1686043 4271231 := bstep (se 1 (by rfl) ⟨3203423, by rfl⟩ : syracuseStep 4271231 = 6406847) B6406847
theorem B43250111 : Blo 1686043 43250111 := bstep (se 1 (by rfl) ⟨32437583, by rfl⟩ : syracuseStep 43250111 = 64875167) B64875167
theorem B3797531 : Blo 1686043 3797531 := bstep (se 1 (by rfl) ⟨2848148, by rfl⟩ : syracuseStep 3797531 = 5696297) B5696297
theorem B4559417 : Blo 1686043 4559417 := bstep (se 2 (by rfl) ⟨1709781, by rfl⟩ : syracuseStep 4559417 = 3419563) B3419563
theorem B5403343 : Blo 1686043 5403343 := bstep (se 1 (by rfl) ⟨4052507, by rfl⟩ : syracuseStep 5403343 = 8105015) B8105015
theorem B20509595 : Blo 1686043 20509595 := bstep (se 1 (by rfl) ⟨15382196, by rfl⟩ : syracuseStep 20509595 = 30764393) B30764393
theorem B19477513 : Blo 1686043 19477513 := bstep (se 2 (by rfl) ⟨7304067, by rfl⟩ : syracuseStep 19477513 = 14608135) B14608135
theorem B28824659 : Blo 1686043 28824659 := bstep (se 1 (by rfl) ⟨21618494, by rfl⟩ : syracuseStep 28824659 = 43236989) B43236989
theorem B8541611 : Blo 1686043 8541611 := bstep (se 1 (by rfl) ⟨6406208, by rfl⟩ : syracuseStep 8541611 = 12812417) B12812417
theorem B4806503 : Blo 1686043 4806503 := bstep (se 1 (by rfl) ⟨3604877, by rfl⟩ : syracuseStep 4806503 = 7209755) B7209755
theorem B2529335 : Blo 1686043 2529335 := bstep (se 1 (by rfl) ⟨1897001, by rfl⟩ : syracuseStep 2529335 = 3794003) B3794003
theorem B4561019 : Blo 1686043 4561019 := bstep (se 1 (by rfl) ⟨3420764, by rfl⟩ : syracuseStep 4561019 = 6841529) B6841529
theorem B189774377 : Blo 1686043 189774377 := bstep (se 2 (by rfl) ⟨71165391, by rfl⟩ : syracuseStep 189774377 = 142330783) B142330783
theorem B5552687 : Blo 1686043 5552687 := bstep (se 1 (by rfl) ⟨4164515, by rfl⟩ : syracuseStep 5552687 = 8329031) B8329031
theorem B16210489 : Blo 1686043 16210489 := bstep (se 2 (by rfl) ⟨6078933, by rfl⟩ : syracuseStep 16210489 = 12157867) B12157867
theorem B1686171 : Blo 1686043 1686171 := bstep (se 1 (by rfl) ⟨1264628, by rfl⟩ : syracuseStep 1686171 = 2529257) B2529257
theorem B3201761 : Blo 1686043 3201761 := bstep (se 2 (by rfl) ⟨1200660, by rfl⟩ : syracuseStep 3201761 = 2401321) B2401321
theorem B2530079 : Blo 1686043 2530079 := bstep (se 1 (by rfl) ⟨1897559, by rfl⟩ : syracuseStep 2530079 = 3795119) B3795119
theorem B1686399 : Blo 1686043 1686399 := bstep (se 1 (by rfl) ⟨1264799, by rfl⟩ : syracuseStep 1686399 = 2529599) B2529599
theorem B2530175 : Blo 1686043 2530175 := bstep (se 1 (by rfl) ⟨1897631, by rfl⟩ : syracuseStep 2530175 = 3795263) B3795263
theorem B1686527 : Blo 1686043 1686527 := bstep (se 1 (by rfl) ⟨1264895, by rfl⟩ : syracuseStep 1686527 = 2529791) B2529791
theorem B1686559 : Blo 1686043 1686559 := bstep (se 1 (by rfl) ⟨1264919, by rfl⟩ : syracuseStep 1686559 = 2529839) B2529839
theorem B4562401 : Blo 1686043 4562401 := bstep (se 2 (by rfl) ⟨1710900, by rfl⟩ : syracuseStep 4562401 = 3421801) B3421801
theorem B7208489 : Blo 1686043 7208489 := bstep (se 2 (by rfl) ⟨2703183, by rfl⟩ : syracuseStep 7208489 = 5406367) B5406367
theorem B12984151 : Blo 1686043 12984151 := bstep (se 1 (by rfl) ⟨9738113, by rfl⟩ : syracuseStep 12984151 = 19476227) B19476227
theorem B2531231 : Blo 1686043 2531231 := bstep (se 1 (by rfl) ⟨1898423, by rfl⟩ : syracuseStep 2531231 = 3796847) B3796847
theorem B1687679 : Blo 1686043 1687679 := bstep (se 1 (by rfl) ⟨1265759, by rfl⟩ : syracuseStep 1687679 = 2531519) B2531519
theorem B2531687 : Blo 1686043 2531687 := bstep (se 1 (by rfl) ⟨1898765, by rfl⟩ : syracuseStep 2531687 = 3797531) B3797531
theorem B3039611 : Blo 1686043 3039611 := bstep (se 1 (by rfl) ⟨2279708, by rfl⟩ : syracuseStep 3039611 = 4559417) B4559417
theorem B13673063 : Blo 1686043 13673063 := bstep (se 1 (by rfl) ⟨10254797, by rfl⟩ : syracuseStep 13673063 = 20509595) B20509595
theorem B49283761 : Blo 1686043 49283761 := bstep (se 2 (by rfl) ⟨18481410, by rfl⟩ : syracuseStep 49283761 = 36962821) B36962821
theorem B5694407 : Blo 1686043 5694407 := bstep (se 1 (by rfl) ⟨4270805, by rfl⟩ : syracuseStep 5694407 = 8541611) B8541611
theorem B3794057 : Blo 1686043 3794057 := bstep (se 2 (by rfl) ⟨1422771, by rfl⟩ : syracuseStep 3794057 = 2845543) B2845543
theorem B3204335 : Blo 1686043 3204335 := bstep (se 1 (by rfl) ⟨2403251, by rfl⟩ : syracuseStep 3204335 = 4806503) B4806503
theorem B25970017 : Blo 1686043 25970017 := bstep (se 2 (by rfl) ⟨9738756, by rfl⟩ : syracuseStep 25970017 = 19477513) B19477513
theorem B3040679 : Blo 1686043 3040679 := bstep (se 1 (by rfl) ⟨2280509, by rfl⟩ : syracuseStep 3040679 = 4561019) B4561019
theorem B17312201 : Blo 1686043 17312201 := bstep (se 2 (by rfl) ⟨6492075, by rfl⟩ : syracuseStep 17312201 = 12984151) B12984151
theorem B5696243 : Blo 1686043 5696243 := bstep (se 1 (by rfl) ⟨4272182, by rfl⟩ : syracuseStep 5696243 = 8544365) B8544365
theorem B2845435 : Blo 1686043 2845435 := bstep (se 1 (by rfl) ⟨2134076, by rfl⟩ : syracuseStep 2845435 = 4268153) B4268153
theorem B3795911 : Blo 1686043 3795911 := bstep (se 1 (by rfl) ⟨2846933, by rfl⟩ : syracuseStep 3795911 = 5693867) B5693867
theorem B10808275 : Blo 1686043 10808275 := bstep (se 1 (by rfl) ⟨8106206, by rfl⟩ : syracuseStep 10808275 = 16212413) B16212413
theorem B21613985 : Blo 1686043 21613985 := bstep (se 2 (by rfl) ⟨8105244, by rfl⟩ : syracuseStep 21613985 = 16210489) B16210489
theorem B7204457 : Blo 1686043 7204457 := bstep (se 2 (by rfl) ⟨2701671, by rfl⟩ : syracuseStep 7204457 = 5403343) B5403343
theorem B4271899 : Blo 1686043 4271899 := bstep (se 1 (by rfl) ⟨3203924, by rfl⟩ : syracuseStep 4271899 = 6407849) B6407849
theorem B27365521 : Blo 1686043 27365521 := bstep (se 2 (by rfl) ⟨10262070, by rfl⟩ : syracuseStep 27365521 = 20524141) B20524141
theorem B2134507 : Blo 1686043 2134507 := bstep (se 1 (by rfl) ⟨1600880, by rfl⟩ : syracuseStep 2134507 = 3201761) B3201761
theorem B1897051 : Blo 1686043 1897051 := bstep (se 1 (by rfl) ⟨1422788, by rfl⟩ : syracuseStep 1897051 = 2845577) B2845577
theorem B6083201 : Blo 1686043 6083201 := bstep (se 2 (by rfl) ⟨2281200, by rfl⟩ : syracuseStep 6083201 = 4562401) B4562401
theorem B2847487 : Blo 1686043 2847487 := bstep (se 1 (by rfl) ⟨2135615, by rfl⟩ : syracuseStep 2847487 = 4271231) B4271231
theorem B4805659 : Blo 1686043 4805659 := bstep (se 1 (by rfl) ⟨3604244, by rfl⟩ : syracuseStep 4805659 = 7208489) B7208489
theorem B42185897 : Blo 1686043 42185897 := bstep (se 2 (by rfl) ⟨15819711, by rfl⟩ : syracuseStep 42185897 = 31639423) B31639423
theorem B28833407 : Blo 1686043 28833407 := bstep (se 1 (by rfl) ⟨21625055, by rfl⟩ : syracuseStep 28833407 = 43250111) B43250111
theorem B19216439 : Blo 1686043 19216439 := bstep (se 1 (by rfl) ⟨14412329, by rfl⟩ : syracuseStep 19216439 = 28824659) B28824659
theorem B1686223 : Blo 1686043 1686223 := bstep (se 1 (by rfl) ⟨1264667, by rfl⟩ : syracuseStep 1686223 = 2529335) B2529335
theorem B5692247 : Blo 1686043 5692247 := bstep (se 1 (by rfl) ⟨4269185, by rfl⟩ : syracuseStep 5692247 = 8538371) B8538371
theorem B126516251 : Blo 1686043 126516251 := bstep (se 1 (by rfl) ⟨94887188, by rfl⟩ : syracuseStep 126516251 = 189774377) B189774377
theorem B3701791 : Blo 1686043 3701791 := bstep (se 1 (by rfl) ⟨2776343, by rfl⟩ : syracuseStep 3701791 = 5552687) B5552687
theorem B1686719 : Blo 1686043 1686719 := bstep (se 1 (by rfl) ⟨1265039, by rfl⟩ : syracuseStep 1686719 = 2530079) B2530079
theorem B1686783 : Blo 1686043 1686783 := bstep (se 1 (by rfl) ⟨1265087, by rfl⟩ : syracuseStep 1686783 = 2530175) B2530175
theorem B1687487 : Blo 1686043 1687487 := bstep (se 1 (by rfl) ⟨1265615, by rfl⟩ : syracuseStep 1687487 = 2531231) B2531231
theorem B19742885 : Blo 1686043 19742885 := bstep (se 4 (by rfl) ⟨1850895, by rfl⟩ : syracuseStep 19742885 = 3701791) B3701791
theorem B36487361 : Blo 1686043 36487361 := bstep (se 2 (by rfl) ⟨13682760, by rfl⟩ : syracuseStep 36487361 = 27365521) B27365521
theorem B1687791 : Blo 1686043 1687791 := bstep (se 1 (by rfl) ⟨1265843, by rfl⟩ : syracuseStep 1687791 = 2531687) B2531687
theorem B28123931 : Blo 1686043 28123931 := bstep (se 1 (by rfl) ⟨21092948, by rfl⟩ : syracuseStep 28123931 = 42185897) B42185897
theorem B3793913 : Blo 1686043 3793913 := bstep (se 2 (by rfl) ⟨1422717, by rfl⟩ : syracuseStep 3793913 = 2845435) B2845435
theorem B14411033 : Blo 1686043 14411033 := bstep (se 2 (by rfl) ⟨5404137, by rfl⟩ : syracuseStep 14411033 = 10808275) B10808275
theorem B6407545 : Blo 1686043 6407545 := bstep (se 2 (by rfl) ⟨2402829, by rfl⟩ : syracuseStep 6407545 = 4805659) B4805659
theorem B16221869 : Blo 1686043 16221869 := bstep (se 3 (by rfl) ⟨3041600, by rfl⟩ : syracuseStep 16221869 = 6083201) B6083201
theorem B3794831 : Blo 1686043 3794831 := bstep (se 1 (by rfl) ⟨2846123, by rfl⟩ : syracuseStep 3794831 = 5692247) B5692247
theorem B5695865 : Blo 1686043 5695865 := bstep (se 2 (by rfl) ⟨2135949, by rfl⟩ : syracuseStep 5695865 = 4271899) B4271899
theorem B4802971 : Blo 1686043 4802971 := bstep (se 1 (by rfl) ⟨3602228, by rfl⟩ : syracuseStep 4802971 = 7204457) B7204457
theorem B3796271 : Blo 1686043 3796271 := bstep (se 1 (by rfl) ⟨2847203, by rfl⟩ : syracuseStep 3796271 = 5694407) B5694407
theorem B2846009 : Blo 1686043 2846009 := bstep (se 2 (by rfl) ⟨1067253, by rfl⟩ : syracuseStep 2846009 = 2134507) B2134507
theorem B65711681 : Blo 1686043 65711681 := bstep (se 2 (by rfl) ⟨24641880, by rfl⟩ : syracuseStep 65711681 = 49283761) B49283761
theorem B2027119 : Blo 1686043 2027119 := bstep (se 1 (by rfl) ⟨1520339, by rfl⟩ : syracuseStep 2027119 = 3040679) B3040679
theorem B3796649 : Blo 1686043 3796649 := bstep (se 2 (by rfl) ⟨1423743, by rfl⟩ : syracuseStep 3796649 = 2847487) B2847487
theorem B19222271 : Blo 1686043 19222271 := bstep (se 1 (by rfl) ⟨14416703, by rfl⟩ : syracuseStep 19222271 = 28833407) B28833407
theorem B3797495 : Blo 1686043 3797495 := bstep (se 1 (by rfl) ⟨2848121, by rfl⟩ : syracuseStep 3797495 = 5696243) B5696243
theorem B9115375 : Blo 1686043 9115375 := bstep (se 1 (by rfl) ⟨6836531, by rfl⟩ : syracuseStep 9115375 = 13673063) B13673063
theorem B2529371 : Blo 1686043 2529371 := bstep (se 1 (by rfl) ⟨1897028, by rfl⟩ : syracuseStep 2529371 = 3794057) B3794057
theorem B2529401 : Blo 1686043 2529401 := bstep (se 2 (by rfl) ⟨948525, by rfl⟩ : syracuseStep 2529401 = 1897051) B1897051
theorem B2136223 : Blo 1686043 2136223 := bstep (se 1 (by rfl) ⟨1602167, by rfl⟩ : syracuseStep 2136223 = 3204335) B3204335
theorem B32422517 : Blo 1686043 32422517 := bstep (se 5 (by rfl) ⟨1519805, by rfl⟩ : syracuseStep 32422517 = 3039611) B3039611
theorem B12810959 : Blo 1686043 12810959 := bstep (se 1 (by rfl) ⟨9608219, by rfl⟩ : syracuseStep 12810959 = 19216439) B19216439
theorem B11541467 : Blo 1686043 11541467 := bstep (se 1 (by rfl) ⟨8656100, by rfl⟩ : syracuseStep 11541467 = 17312201) B17312201
theorem B34626689 : Blo 1686043 34626689 := bstep (se 2 (by rfl) ⟨12985008, by rfl⟩ : syracuseStep 34626689 = 25970017) B25970017
theorem B2530607 : Blo 1686043 2530607 := bstep (se 1 (by rfl) ⟨1897955, by rfl⟩ : syracuseStep 2530607 = 3795911) B3795911
theorem B84344167 : Blo 1686043 84344167 := bstep (se 1 (by rfl) ⟨63258125, by rfl⟩ : syracuseStep 84344167 = 126516251) B126516251
theorem B14409323 : Blo 1686043 14409323 := bstep (se 1 (by rfl) ⟨10806992, by rfl⟩ : syracuseStep 14409323 = 21613985) B21613985
theorem B2531663 : Blo 1686043 2531663 := bstep (se 1 (by rfl) ⟨1898747, by rfl⟩ : syracuseStep 2531663 = 3797495) B3797495
theorem B10814579 : Blo 1686043 10814579 := bstep (se 1 (by rfl) ⟨8110934, by rfl⟩ : syracuseStep 10814579 = 16221869) B16221869
theorem B7694311 : Blo 1686043 7694311 := bstep (se 1 (by rfl) ⟨5770733, by rfl⟩ : syracuseStep 7694311 = 11541467) B11541467
theorem B12814847 : Blo 1686043 12814847 := bstep (se 1 (by rfl) ⟨9611135, by rfl⟩ : syracuseStep 12814847 = 19222271) B19222271
theorem B24324907 : Blo 1686043 24324907 := bstep (se 1 (by rfl) ⟨18243680, by rfl⟩ : syracuseStep 24324907 = 36487361) B36487361
theorem B3797243 : Blo 1686043 3797243 := bstep (se 1 (by rfl) ⟨2847932, by rfl⟩ : syracuseStep 3797243 = 5695865) B5695865
theorem B21615011 : Blo 1686043 21615011 := bstep (se 1 (by rfl) ⟨16211258, by rfl⟩ : syracuseStep 21615011 = 32422517) B32422517
theorem B8540639 : Blo 1686043 8540639 := bstep (se 1 (by rfl) ⟨6405479, by rfl⟩ : syracuseStep 8540639 = 12810959) B12810959
theorem B1897339 : Blo 1686043 1897339 := bstep (se 1 (by rfl) ⟨1423004, by rfl⟩ : syracuseStep 1897339 = 2846009) B2846009
theorem B12153833 : Blo 1686043 12153833 := bstep (se 2 (by rfl) ⟨4557687, by rfl⟩ : syracuseStep 12153833 = 9115375) B9115375
theorem B43807787 : Blo 1686043 43807787 := bstep (se 1 (by rfl) ⟨32855840, by rfl⟩ : syracuseStep 43807787 = 65711681) B65711681
theorem B9606215 : Blo 1686043 9606215 := bstep (se 1 (by rfl) ⟨7204661, by rfl⟩ : syracuseStep 9606215 = 14409323) B14409323
theorem B13161923 : Blo 1686043 13161923 := bstep (se 1 (by rfl) ⟨9871442, by rfl⟩ : syracuseStep 13161923 = 19742885) B19742885
theorem B2848297 : Blo 1686043 2848297 := bstep (se 2 (by rfl) ⟨1068111, by rfl⟩ : syracuseStep 2848297 = 2136223) B2136223
theorem B18749287 : Blo 1686043 18749287 := bstep (se 1 (by rfl) ⟨14061965, by rfl⟩ : syracuseStep 18749287 = 28123931) B28123931
theorem B6403961 : Blo 1686043 6403961 := bstep (se 2 (by rfl) ⟨2401485, by rfl⟩ : syracuseStep 6403961 = 4802971) B4802971
theorem B2529275 : Blo 1686043 2529275 := bstep (se 1 (by rfl) ⟨1896956, by rfl⟩ : syracuseStep 2529275 = 3793913) B3793913
theorem B9607355 : Blo 1686043 9607355 := bstep (se 1 (by rfl) ⟨7205516, by rfl⟩ : syracuseStep 9607355 = 14411033) B14411033
theorem B2529887 : Blo 1686043 2529887 := bstep (se 1 (by rfl) ⟨1897415, by rfl⟩ : syracuseStep 2529887 = 3794831) B3794831
theorem B1686247 : Blo 1686043 1686247 := bstep (se 1 (by rfl) ⟨1264685, by rfl⟩ : syracuseStep 1686247 = 2529371) B2529371
theorem B1686267 : Blo 1686043 1686267 := bstep (se 1 (by rfl) ⟨1264700, by rfl⟩ : syracuseStep 1686267 = 2529401) B2529401
theorem B112458889 : Blo 1686043 112458889 := bstep (se 2 (by rfl) ⟨42172083, by rfl⟩ : syracuseStep 112458889 = 84344167) B84344167
theorem B8543393 : Blo 1686043 8543393 := bstep (se 2 (by rfl) ⟨3203772, by rfl⟩ : syracuseStep 8543393 = 6407545) B6407545
theorem B23084459 : Blo 1686043 23084459 := bstep (se 1 (by rfl) ⟨17313344, by rfl⟩ : syracuseStep 23084459 = 34626689) B34626689
theorem B2702825 : Blo 1686043 2702825 := bstep (se 2 (by rfl) ⟨1013559, by rfl⟩ : syracuseStep 2702825 = 2027119) B2027119
theorem B1687071 : Blo 1686043 1687071 := bstep (se 1 (by rfl) ⟨1265303, by rfl⟩ : syracuseStep 1687071 = 2530607) B2530607
theorem B2530847 : Blo 1686043 2530847 := bstep (se 1 (by rfl) ⟨1898135, by rfl⟩ : syracuseStep 2530847 = 3796271) B3796271
theorem B2531099 : Blo 1686043 2531099 := bstep (se 1 (by rfl) ⟨1898324, by rfl⟩ : syracuseStep 2531099 = 3796649) B3796649
theorem B2531495 : Blo 1686043 2531495 := bstep (se 1 (by rfl) ⟨1898621, by rfl⟩ : syracuseStep 2531495 = 3797243) B3797243
theorem B1687775 : Blo 1686043 1687775 := bstep (se 1 (by rfl) ⟨1265831, by rfl⟩ : syracuseStep 1687775 = 2531663) B2531663
theorem B14410007 : Blo 1686043 14410007 := bstep (se 1 (by rfl) ⟨10807505, by rfl⟩ : syracuseStep 14410007 = 21615011) B21615011
theorem B5693759 : Blo 1686043 5693759 := bstep (se 1 (by rfl) ⟨4270319, by rfl⟩ : syracuseStep 5693759 = 8540639) B8540639
theorem B8102555 : Blo 1686043 8102555 := bstep (se 1 (by rfl) ⟨6076916, by rfl⟩ : syracuseStep 8102555 = 12153833) B12153833
theorem B29205191 : Blo 1686043 29205191 := bstep (se 1 (by rfl) ⟨21903893, by rfl⟩ : syracuseStep 29205191 = 43807787) B43807787
theorem B7209719 : Blo 1686043 7209719 := bstep (se 1 (by rfl) ⟨5407289, by rfl⟩ : syracuseStep 7209719 = 10814579) B10814579
theorem B8774615 : Blo 1686043 8774615 := bstep (se 1 (by rfl) ⟨6580961, by rfl⟩ : syracuseStep 8774615 = 13161923) B13161923
theorem B32433209 : Blo 1686043 32433209 := bstep (se 2 (by rfl) ⟨12162453, by rfl⟩ : syracuseStep 32433209 = 24324907) B24324907
theorem B4269307 : Blo 1686043 4269307 := bstep (se 1 (by rfl) ⟨3201980, by rfl⟩ : syracuseStep 4269307 = 6403961) B6403961
theorem B5695595 : Blo 1686043 5695595 := bstep (se 1 (by rfl) ⟨4271696, by rfl⟩ : syracuseStep 5695595 = 8543393) B8543393
theorem B10259081 : Blo 1686043 10259081 := bstep (se 2 (by rfl) ⟨3847155, by rfl⟩ : syracuseStep 10259081 = 7694311) B7694311
theorem B3797729 : Blo 1686043 3797729 := bstep (se 2 (by rfl) ⟨1424148, by rfl⟩ : syracuseStep 3797729 = 2848297) B2848297
theorem B15389639 : Blo 1686043 15389639 := bstep (se 1 (by rfl) ⟨11542229, by rfl⟩ : syracuseStep 15389639 = 23084459) B23084459
theorem B24999049 : Blo 1686043 24999049 := bstep (se 2 (by rfl) ⟨9374643, by rfl⟩ : syracuseStep 24999049 = 18749287) B18749287
theorem B6404143 : Blo 1686043 6404143 := bstep (se 1 (by rfl) ⟨4803107, by rfl⟩ : syracuseStep 6404143 = 9606215) B9606215
theorem B2529785 : Blo 1686043 2529785 := bstep (se 2 (by rfl) ⟨948669, by rfl⟩ : syracuseStep 2529785 = 1897339) B1897339
theorem B1686183 : Blo 1686043 1686183 := bstep (se 1 (by rfl) ⟨1264637, by rfl⟩ : syracuseStep 1686183 = 2529275) B2529275
theorem B6404903 : Blo 1686043 6404903 := bstep (se 1 (by rfl) ⟨4803677, by rfl⟩ : syracuseStep 6404903 = 9607355) B9607355
theorem B149945185 : Blo 1686043 149945185 := bstep (se 2 (by rfl) ⟨56229444, by rfl⟩ : syracuseStep 149945185 = 112458889) B112458889
theorem B8543231 : Blo 1686043 8543231 := bstep (se 1 (by rfl) ⟨6407423, by rfl⟩ : syracuseStep 8543231 = 12814847) B12814847
theorem B1686591 : Blo 1686043 1686591 := bstep (se 1 (by rfl) ⟨1264943, by rfl⟩ : syracuseStep 1686591 = 2529887) B2529887
theorem B1801883 : Blo 1686043 1801883 := bstep (se 1 (by rfl) ⟨1351412, by rfl⟩ : syracuseStep 1801883 = 2702825) B2702825
theorem B1687231 : Blo 1686043 1687231 := bstep (se 1 (by rfl) ⟨1265423, by rfl⟩ : syracuseStep 1687231 = 2530847) B2530847
theorem B1687399 : Blo 1686043 1687399 := bstep (se 1 (by rfl) ⟨1265549, by rfl⟩ : syracuseStep 1687399 = 2531099) B2531099
theorem B1687663 : Blo 1686043 1687663 := bstep (se 1 (by rfl) ⟨1265747, by rfl⟩ : syracuseStep 1687663 = 2531495) B2531495
theorem B2531819 : Blo 1686043 2531819 := bstep (se 1 (by rfl) ⟨1898864, by rfl⟩ : syracuseStep 2531819 = 3797729) B3797729
theorem B5849743 : Blo 1686043 5849743 := bstep (se 1 (by rfl) ⟨4387307, by rfl⟩ : syracuseStep 5849743 = 8774615) B8774615
theorem B199926913 : Blo 1686043 199926913 := bstep (se 2 (by rfl) ⟨74972592, by rfl⟩ : syracuseStep 199926913 = 149945185) B149945185
theorem B4269935 : Blo 1686043 4269935 := bstep (se 1 (by rfl) ⟨3202451, by rfl⟩ : syracuseStep 4269935 = 6404903) B6404903
theorem B5695487 : Blo 1686043 5695487 := bstep (se 1 (by rfl) ⟨4271615, by rfl⟩ : syracuseStep 5695487 = 8543231) B8543231
theorem B8538857 : Blo 1686043 8538857 := bstep (se 2 (by rfl) ⟨3202071, by rfl⟩ : syracuseStep 8538857 = 6404143) B6404143
theorem B3795839 : Blo 1686043 3795839 := bstep (se 1 (by rfl) ⟨2846879, by rfl⟩ : syracuseStep 3795839 = 5693759) B5693759
theorem B5401703 : Blo 1686043 5401703 := bstep (se 1 (by rfl) ⟨4051277, by rfl⟩ : syracuseStep 5401703 = 8102555) B8102555
theorem B10259759 : Blo 1686043 10259759 := bstep (se 1 (by rfl) ⟨7694819, by rfl⟩ : syracuseStep 10259759 = 15389639) B15389639
theorem B21622139 : Blo 1686043 21622139 := bstep (se 1 (by rfl) ⟨16216604, by rfl⟩ : syracuseStep 21622139 = 32433209) B32433209
theorem B133328261 : Blo 1686043 133328261 := bstep (se 4 (by rfl) ⟨12499524, by rfl⟩ : syracuseStep 133328261 = 24999049) B24999049
theorem B3797063 : Blo 1686043 3797063 := bstep (se 1 (by rfl) ⟨2847797, by rfl⟩ : syracuseStep 3797063 = 5695595) B5695595
theorem B4805021 : Blo 1686043 4805021 := bstep (se 3 (by rfl) ⟨900941, by rfl⟩ : syracuseStep 4805021 = 1801883) B1801883
theorem B9606671 : Blo 1686043 9606671 := bstep (se 1 (by rfl) ⟨7205003, by rfl⟩ : syracuseStep 9606671 = 14410007) B14410007
theorem B19470127 : Blo 1686043 19470127 := bstep (se 1 (by rfl) ⟨14602595, by rfl⟩ : syracuseStep 19470127 = 29205191) B29205191
theorem B4806479 : Blo 1686043 4806479 := bstep (se 1 (by rfl) ⟨3604859, by rfl⟩ : syracuseStep 4806479 = 7209719) B7209719
theorem B5692409 : Blo 1686043 5692409 := bstep (se 2 (by rfl) ⟨2134653, by rfl⟩ : syracuseStep 5692409 = 4269307) B4269307
theorem B1686523 : Blo 1686043 1686523 := bstep (se 1 (by rfl) ⟨1264892, by rfl⟩ : syracuseStep 1686523 = 2529785) B2529785
theorem B6839387 : Blo 1686043 6839387 := bstep (se 1 (by rfl) ⟨5129540, by rfl⟩ : syracuseStep 6839387 = 10259081) B10259081
theorem B2531375 : Blo 1686043 2531375 := bstep (se 1 (by rfl) ⟨1898531, by rfl⟩ : syracuseStep 2531375 = 3797063) B3797063
theorem B1687879 : Blo 1686043 1687879 := bstep (se 1 (by rfl) ⟨1265909, by rfl⟩ : syracuseStep 1687879 = 2531819) B2531819
theorem B7799657 : Blo 1686043 7799657 := bstep (se 2 (by rfl) ⟨2924871, by rfl⟩ : syracuseStep 7799657 = 5849743) B5849743
theorem B12813389 : Blo 1686043 12813389 := bstep (se 3 (by rfl) ⟨2402510, by rfl⟩ : syracuseStep 12813389 = 4805021) B4805021
theorem B266569217 : Blo 1686043 266569217 := bstep (se 2 (by rfl) ⟨99963456, by rfl⟩ : syracuseStep 266569217 = 199926913) B199926913
theorem B3794939 : Blo 1686043 3794939 := bstep (se 1 (by rfl) ⟨2846204, by rfl⟩ : syracuseStep 3794939 = 5692409) B5692409
theorem B88885507 : Blo 1686043 88885507 := bstep (se 1 (by rfl) ⟨66664130, by rfl⟩ : syracuseStep 88885507 = 133328261) B133328261
theorem B2846623 : Blo 1686043 2846623 := bstep (se 1 (by rfl) ⟨2134967, by rfl⟩ : syracuseStep 2846623 = 4269935) B4269935
theorem B3796991 : Blo 1686043 3796991 := bstep (se 1 (by rfl) ⟨2847743, by rfl⟩ : syracuseStep 3796991 = 5695487) B5695487
theorem B4559591 : Blo 1686043 4559591 := bstep (se 1 (by rfl) ⟨3419693, by rfl⟩ : syracuseStep 4559591 = 6839387) B6839387
theorem B3601135 : Blo 1686043 3601135 := bstep (se 1 (by rfl) ⟨2700851, by rfl⟩ : syracuseStep 3601135 = 5401703) B5401703
theorem B12817277 : Blo 1686043 12817277 := bstep (se 3 (by rfl) ⟨2403239, by rfl⟩ : syracuseStep 12817277 = 4806479) B4806479
theorem B14414759 : Blo 1686043 14414759 := bstep (se 1 (by rfl) ⟨10811069, by rfl⟩ : syracuseStep 14414759 = 21622139) B21622139
theorem B6404447 : Blo 1686043 6404447 := bstep (se 1 (by rfl) ⟨4803335, by rfl⟩ : syracuseStep 6404447 = 9606671) B9606671
theorem B5692571 : Blo 1686043 5692571 := bstep (se 1 (by rfl) ⟨4269428, by rfl⟩ : syracuseStep 5692571 = 8538857) B8538857
theorem B2530559 : Blo 1686043 2530559 := bstep (se 1 (by rfl) ⟨1897919, by rfl⟩ : syracuseStep 2530559 = 3795839) B3795839
theorem B6839839 : Blo 1686043 6839839 := bstep (se 1 (by rfl) ⟨5129879, by rfl⟩ : syracuseStep 6839839 = 10259759) B10259759
theorem B25960169 : Blo 1686043 25960169 := bstep (se 2 (by rfl) ⟨9735063, by rfl⟩ : syracuseStep 25960169 = 19470127) B19470127
theorem B1687583 : Blo 1686043 1687583 := bstep (se 1 (by rfl) ⟨1265687, by rfl⟩ : syracuseStep 1687583 = 2531375) B2531375
theorem B118514009 : Blo 1686043 118514009 := bstep (se 2 (by rfl) ⟨44442753, by rfl⟩ : syracuseStep 118514009 = 88885507) B88885507
theorem B8544851 : Blo 1686043 8544851 := bstep (se 1 (by rfl) ⟨6408638, by rfl⟩ : syracuseStep 8544851 = 12817277) B12817277
theorem B9609839 : Blo 1686043 9609839 := bstep (se 1 (by rfl) ⟨7207379, by rfl⟩ : syracuseStep 9609839 = 14414759) B14414759
theorem B4801513 : Blo 1686043 4801513 := bstep (se 2 (by rfl) ⟨1800567, by rfl⟩ : syracuseStep 4801513 = 3601135) B3601135
theorem B4269631 : Blo 1686043 4269631 := bstep (se 1 (by rfl) ⟨3202223, by rfl⟩ : syracuseStep 4269631 = 6404447) B6404447
theorem B12158909 : Blo 1686043 12158909 := bstep (se 3 (by rfl) ⟨2279795, by rfl⟩ : syracuseStep 12158909 = 4559591) B4559591
theorem B9119785 : Blo 1686043 9119785 := bstep (se 2 (by rfl) ⟨3419919, by rfl⟩ : syracuseStep 9119785 = 6839839) B6839839
theorem B3795047 : Blo 1686043 3795047 := bstep (se 1 (by rfl) ⟨2846285, by rfl⟩ : syracuseStep 3795047 = 5692571) B5692571
theorem B3795497 : Blo 1686043 3795497 := bstep (se 2 (by rfl) ⟨1423311, by rfl⟩ : syracuseStep 3795497 = 2846623) B2846623
theorem B177712811 : Blo 1686043 177712811 := bstep (se 1 (by rfl) ⟨133284608, by rfl⟩ : syracuseStep 177712811 = 266569217) B266569217
theorem B17306779 : Blo 1686043 17306779 := bstep (se 1 (by rfl) ⟨12980084, by rfl⟩ : syracuseStep 17306779 = 25960169) B25960169
theorem B2531327 : Blo 1686043 2531327 := bstep (se 1 (by rfl) ⟨1898495, by rfl⟩ : syracuseStep 2531327 = 3796991) B3796991
theorem B8542259 : Blo 1686043 8542259 := bstep (se 1 (by rfl) ⟨6406694, by rfl⟩ : syracuseStep 8542259 = 12813389) B12813389
theorem B83196341 : Blo 1686043 83196341 := bstep (se 5 (by rfl) ⟨3899828, by rfl⟩ : syracuseStep 83196341 = 7799657) B7799657
theorem B2529959 : Blo 1686043 2529959 := bstep (se 1 (by rfl) ⟨1897469, by rfl⟩ : syracuseStep 2529959 = 3794939) B3794939
theorem B1687039 : Blo 1686043 1687039 := bstep (se 1 (by rfl) ⟨1265279, by rfl⟩ : syracuseStep 1687039 = 2530559) B2530559
theorem B6406559 : Blo 1686043 6406559 := bstep (se 1 (by rfl) ⟨4804919, by rfl⟩ : syracuseStep 6406559 = 9609839) B9609839
theorem B5694839 : Blo 1686043 5694839 := bstep (se 1 (by rfl) ⟨4271129, by rfl⟩ : syracuseStep 5694839 = 8542259) B8542259
theorem B118475207 : Blo 1686043 118475207 := bstep (se 1 (by rfl) ⟨88856405, by rfl⟩ : syracuseStep 118475207 = 177712811) B177712811
theorem B12159713 : Blo 1686043 12159713 := bstep (se 2 (by rfl) ⟨4559892, by rfl⟩ : syracuseStep 12159713 = 9119785) B9119785
theorem B5696567 : Blo 1686043 5696567 := bstep (se 1 (by rfl) ⟨4272425, by rfl⟩ : syracuseStep 5696567 = 8544851) B8544851
theorem B8105939 : Blo 1686043 8105939 := bstep (se 1 (by rfl) ⟨6079454, by rfl⟩ : syracuseStep 8105939 = 12158909) B12158909
theorem B6402017 : Blo 1686043 6402017 := bstep (se 2 (by rfl) ⟨2400756, by rfl⟩ : syracuseStep 6402017 = 4801513) B4801513
theorem B55464227 : Blo 1686043 55464227 := bstep (se 1 (by rfl) ⟨41598170, by rfl⟩ : syracuseStep 55464227 = 83196341) B83196341
theorem B79009339 : Blo 1686043 79009339 := bstep (se 1 (by rfl) ⟨59257004, by rfl⟩ : syracuseStep 79009339 = 118514009) B118514009
theorem B2530031 : Blo 1686043 2530031 := bstep (se 1 (by rfl) ⟨1897523, by rfl⟩ : syracuseStep 2530031 = 3795047) B3795047
theorem B23075705 : Blo 1686043 23075705 := bstep (se 2 (by rfl) ⟨8653389, by rfl⟩ : syracuseStep 23075705 = 17306779) B17306779
theorem B2530331 : Blo 1686043 2530331 := bstep (se 1 (by rfl) ⟨1897748, by rfl⟩ : syracuseStep 2530331 = 3795497) B3795497
theorem B1686639 : Blo 1686043 1686639 := bstep (se 1 (by rfl) ⟨1264979, by rfl⟩ : syracuseStep 1686639 = 2529959) B2529959
theorem B5692841 : Blo 1686043 5692841 := bstep (se 2 (by rfl) ⟨2134815, by rfl⟩ : syracuseStep 5692841 = 4269631) B4269631
theorem B1687551 : Blo 1686043 1687551 := bstep (se 1 (by rfl) ⟨1265663, by rfl⟩ : syracuseStep 1687551 = 2531327) B2531327
theorem B3795227 : Blo 1686043 3795227 := bstep (se 1 (by rfl) ⟨2846420, by rfl⟩ : syracuseStep 3795227 = 5692841) B5692841
theorem B4271039 : Blo 1686043 4271039 := bstep (se 1 (by rfl) ⟨3203279, by rfl⟩ : syracuseStep 4271039 = 6406559) B6406559
theorem B3796559 : Blo 1686043 3796559 := bstep (se 1 (by rfl) ⟨2847419, by rfl⟩ : syracuseStep 3796559 = 5694839) B5694839
theorem B78983471 : Blo 1686043 78983471 := bstep (se 1 (by rfl) ⟨59237603, by rfl⟩ : syracuseStep 78983471 = 118475207) B118475207
theorem B8106475 : Blo 1686043 8106475 := bstep (se 1 (by rfl) ⟨6079856, by rfl⟩ : syracuseStep 8106475 = 12159713) B12159713
theorem B3797711 : Blo 1686043 3797711 := bstep (se 1 (by rfl) ⟨2848283, by rfl⟩ : syracuseStep 3797711 = 5696567) B5696567
theorem B105345785 : Blo 1686043 105345785 := bstep (se 2 (by rfl) ⟨39504669, by rfl⟩ : syracuseStep 105345785 = 79009339) B79009339
theorem B5403959 : Blo 1686043 5403959 := bstep (se 1 (by rfl) ⟨4052969, by rfl⟩ : syracuseStep 5403959 = 8105939) B8105939
theorem B36976151 : Blo 1686043 36976151 := bstep (se 1 (by rfl) ⟨27732113, by rfl⟩ : syracuseStep 36976151 = 55464227) B55464227
theorem B1686687 : Blo 1686043 1686687 := bstep (se 1 (by rfl) ⟨1265015, by rfl⟩ : syracuseStep 1686687 = 2530031) B2530031
theorem B15383803 : Blo 1686043 15383803 := bstep (se 1 (by rfl) ⟨11537852, by rfl⟩ : syracuseStep 15383803 = 23075705) B23075705
theorem B1686887 : Blo 1686043 1686887 := bstep (se 1 (by rfl) ⟨1265165, by rfl⟩ : syracuseStep 1686887 = 2530331) B2530331
theorem B4268011 : Blo 1686043 4268011 := bstep (se 1 (by rfl) ⟨3201008, by rfl⟩ : syracuseStep 4268011 = 6402017) B6402017
theorem B2531807 : Blo 1686043 2531807 := bstep (se 1 (by rfl) ⟨1898855, by rfl⟩ : syracuseStep 2531807 = 3797711) B3797711
theorem B70230523 : Blo 1686043 70230523 := bstep (se 1 (by rfl) ⟨52672892, by rfl⟩ : syracuseStep 70230523 = 105345785) B105345785
theorem B24650767 : Blo 1686043 24650767 := bstep (se 1 (by rfl) ⟨18488075, by rfl⟩ : syracuseStep 24650767 = 36976151) B36976151
theorem B10808633 : Blo 1686043 10808633 := bstep (se 2 (by rfl) ⟨4053237, by rfl⟩ : syracuseStep 10808633 = 8106475) B8106475
theorem B2847359 : Blo 1686043 2847359 := bstep (se 1 (by rfl) ⟨2135519, by rfl⟩ : syracuseStep 2847359 = 4271039) B4271039
theorem B5690681 : Blo 1686043 5690681 := bstep (se 2 (by rfl) ⟨2134005, by rfl⟩ : syracuseStep 5690681 = 4268011) B4268011
theorem B210622589 : Blo 1686043 210622589 := bstep (se 3 (by rfl) ⟨39491735, by rfl⟩ : syracuseStep 210622589 = 78983471) B78983471
theorem B3602639 : Blo 1686043 3602639 := bstep (se 1 (by rfl) ⟨2701979, by rfl⟩ : syracuseStep 3602639 = 5403959) B5403959
theorem B2530151 : Blo 1686043 2530151 := bstep (se 1 (by rfl) ⟨1897613, by rfl⟩ : syracuseStep 2530151 = 3795227) B3795227
theorem B20511737 : Blo 1686043 20511737 := bstep (se 2 (by rfl) ⟨7691901, by rfl⟩ : syracuseStep 20511737 = 15383803) B15383803
theorem B2531039 : Blo 1686043 2531039 := bstep (se 1 (by rfl) ⟨1898279, by rfl⟩ : syracuseStep 2531039 = 3796559) B3796559
theorem B1687871 : Blo 1686043 1687871 := bstep (se 1 (by rfl) ⟨1265903, by rfl⟩ : syracuseStep 1687871 = 2531807) B2531807
theorem B3793787 : Blo 1686043 3793787 := bstep (se 1 (by rfl) ⟨2845340, by rfl⟩ : syracuseStep 3793787 = 5690681) B5690681
theorem B32867689 : Blo 1686043 32867689 := bstep (se 2 (by rfl) ⟨12325383, by rfl⟩ : syracuseStep 32867689 = 24650767) B24650767
theorem B2401759 : Blo 1686043 2401759 := bstep (se 1 (by rfl) ⟨1801319, by rfl⟩ : syracuseStep 2401759 = 3602639) B3602639
theorem B13674491 : Blo 1686043 13674491 := bstep (se 1 (by rfl) ⟨10255868, by rfl⟩ : syracuseStep 13674491 = 20511737) B20511737
theorem B140415059 : Blo 1686043 140415059 := bstep (se 1 (by rfl) ⟨105311294, by rfl⟩ : syracuseStep 140415059 = 210622589) B210622589
theorem B7205755 : Blo 1686043 7205755 := bstep (se 1 (by rfl) ⟨5404316, by rfl⟩ : syracuseStep 7205755 = 10808633) B10808633
theorem B1898239 : Blo 1686043 1898239 := bstep (se 1 (by rfl) ⟨1423679, by rfl⟩ : syracuseStep 1898239 = 2847359) B2847359
theorem B93640697 : Blo 1686043 93640697 := bstep (se 2 (by rfl) ⟨35115261, by rfl⟩ : syracuseStep 93640697 = 70230523) B70230523
theorem B1686767 : Blo 1686043 1686767 := bstep (se 1 (by rfl) ⟨1265075, by rfl⟩ : syracuseStep 1686767 = 2530151) B2530151
theorem B1687359 : Blo 1686043 1687359 := bstep (se 1 (by rfl) ⟨1265519, by rfl⟩ : syracuseStep 1687359 = 2531039) B2531039
theorem B93610039 : Blo 1686043 93610039 := bstep (se 1 (by rfl) ⟨70207529, by rfl⟩ : syracuseStep 93610039 = 140415059) B140415059
theorem B62427131 : Blo 1686043 62427131 := bstep (se 1 (by rfl) ⟨46820348, by rfl⟩ : syracuseStep 62427131 = 93640697) B93640697
theorem B43823585 : Blo 1686043 43823585 := bstep (se 2 (by rfl) ⟨16433844, by rfl⟩ : syracuseStep 43823585 = 32867689) B32867689
theorem B2529191 : Blo 1686043 2529191 := bstep (se 1 (by rfl) ⟨1896893, by rfl⟩ : syracuseStep 2529191 = 3793787) B3793787
theorem B9607673 : Blo 1686043 9607673 := bstep (se 2 (by rfl) ⟨3602877, by rfl⟩ : syracuseStep 9607673 = 7205755) B7205755
theorem B9116327 : Blo 1686043 9116327 := bstep (se 1 (by rfl) ⟨6837245, by rfl⟩ : syracuseStep 9116327 = 13674491) B13674491
theorem B3202345 : Blo 1686043 3202345 := bstep (se 2 (by rfl) ⟨1200879, by rfl⟩ : syracuseStep 3202345 = 2401759) B2401759
theorem B2530985 : Blo 1686043 2530985 := bstep (se 2 (by rfl) ⟨949119, by rfl⟩ : syracuseStep 2530985 = 1898239) B1898239
theorem B124813385 : Blo 1686043 124813385 := bstep (se 2 (by rfl) ⟨46805019, by rfl⟩ : syracuseStep 124813385 = 93610039) B93610039
theorem B4269793 : Blo 1686043 4269793 := bstep (se 2 (by rfl) ⟨1601172, by rfl⟩ : syracuseStep 4269793 = 3202345) B3202345
theorem B41618087 : Blo 1686043 41618087 := bstep (se 1 (by rfl) ⟨31213565, by rfl⟩ : syracuseStep 41618087 = 62427131) B62427131
theorem B29215723 : Blo 1686043 29215723 := bstep (se 1 (by rfl) ⟨21911792, by rfl⟩ : syracuseStep 29215723 = 43823585) B43823585
theorem B1686127 : Blo 1686043 1686127 := bstep (se 1 (by rfl) ⟨1264595, by rfl⟩ : syracuseStep 1686127 = 2529191) B2529191
theorem B6405115 : Blo 1686043 6405115 := bstep (se 1 (by rfl) ⟨4803836, by rfl⟩ : syracuseStep 6405115 = 9607673) B9607673
theorem B6077551 : Blo 1686043 6077551 := bstep (se 1 (by rfl) ⟨4558163, by rfl⟩ : syracuseStep 6077551 = 9116327) B9116327
theorem B1687323 : Blo 1686043 1687323 := bstep (se 1 (by rfl) ⟨1265492, by rfl⟩ : syracuseStep 1687323 = 2530985) B2530985
theorem B38954297 : Blo 1686043 38954297 := bstep (se 2 (by rfl) ⟨14607861, by rfl⟩ : syracuseStep 38954297 = 29215723) B29215723
theorem B8103401 : Blo 1686043 8103401 := bstep (se 2 (by rfl) ⟨3038775, by rfl⟩ : syracuseStep 8103401 = 6077551) B6077551
theorem B83208923 : Blo 1686043 83208923 := bstep (se 1 (by rfl) ⟨62406692, by rfl⟩ : syracuseStep 83208923 = 124813385) B124813385
theorem B8540153 : Blo 1686043 8540153 := bstep (se 2 (by rfl) ⟨3202557, by rfl⟩ : syracuseStep 8540153 = 6405115) B6405115
theorem B27745391 : Blo 1686043 27745391 := bstep (se 1 (by rfl) ⟨20809043, by rfl⟩ : syracuseStep 27745391 = 41618087) B41618087
theorem B5693057 : Blo 1686043 5693057 := bstep (se 2 (by rfl) ⟨2134896, by rfl⟩ : syracuseStep 5693057 = 4269793) B4269793
theorem B25969531 : Blo 1686043 25969531 := bstep (se 1 (by rfl) ⟨19477148, by rfl⟩ : syracuseStep 25969531 = 38954297) B38954297
theorem B3795371 : Blo 1686043 3795371 := bstep (se 1 (by rfl) ⟨2846528, by rfl⟩ : syracuseStep 3795371 = 5693057) B5693057
theorem B5402267 : Blo 1686043 5402267 := bstep (se 1 (by rfl) ⟨4051700, by rfl⟩ : syracuseStep 5402267 = 8103401) B8103401
theorem B55472615 : Blo 1686043 55472615 := bstep (se 1 (by rfl) ⟨41604461, by rfl⟩ : syracuseStep 55472615 = 83208923) B83208923
theorem B18496927 : Blo 1686043 18496927 := bstep (se 1 (by rfl) ⟨13872695, by rfl⟩ : syracuseStep 18496927 = 27745391) B27745391
theorem B5693435 : Blo 1686043 5693435 := bstep (se 1 (by rfl) ⟨4270076, by rfl⟩ : syracuseStep 5693435 = 8540153) B8540153
theorem B3795623 : Blo 1686043 3795623 := bstep (se 1 (by rfl) ⟨2846717, by rfl⟩ : syracuseStep 3795623 = 5693435) B5693435
theorem B36981743 : Blo 1686043 36981743 := bstep (se 1 (by rfl) ⟨27736307, by rfl⟩ : syracuseStep 36981743 = 55472615) B55472615
theorem B24662569 : Blo 1686043 24662569 := bstep (se 2 (by rfl) ⟨9248463, by rfl⟩ : syracuseStep 24662569 = 18496927) B18496927
theorem B3601511 : Blo 1686043 3601511 := bstep (se 1 (by rfl) ⟨2701133, by rfl⟩ : syracuseStep 3601511 = 5402267) B5402267
theorem B34626041 : Blo 1686043 34626041 := bstep (se 2 (by rfl) ⟨12984765, by rfl⟩ : syracuseStep 34626041 = 25969531) B25969531
theorem B2530247 : Blo 1686043 2530247 := bstep (se 1 (by rfl) ⟨1897685, by rfl⟩ : syracuseStep 2530247 = 3795371) B3795371
theorem B32883425 : Blo 1686043 32883425 := bstep (se 2 (by rfl) ⟨12331284, by rfl⟩ : syracuseStep 32883425 = 24662569) B24662569
theorem B2401007 : Blo 1686043 2401007 := bstep (se 1 (by rfl) ⟨1800755, by rfl⟩ : syracuseStep 2401007 = 3601511) B3601511
theorem B98617981 : Blo 1686043 98617981 := bstep (se 3 (by rfl) ⟨18490871, by rfl⟩ : syracuseStep 98617981 = 36981743) B36981743
theorem B23084027 : Blo 1686043 23084027 := bstep (se 1 (by rfl) ⟨17313020, by rfl⟩ : syracuseStep 23084027 = 34626041) B34626041
theorem B2530415 : Blo 1686043 2530415 := bstep (se 1 (by rfl) ⟨1897811, by rfl⟩ : syracuseStep 2530415 = 3795623) B3795623
theorem B1686831 : Blo 1686043 1686831 := bstep (se 1 (by rfl) ⟨1265123, by rfl⟩ : syracuseStep 1686831 = 2530247) B2530247
theorem B21922283 : Blo 1686043 21922283 := bstep (se 1 (by rfl) ⟨16441712, by rfl⟩ : syracuseStep 21922283 = 32883425) B32883425
theorem B131490641 : Blo 1686043 131490641 := bstep (se 2 (by rfl) ⟨49308990, by rfl⟩ : syracuseStep 131490641 = 98617981) B98617981
theorem B6402685 : Blo 1686043 6402685 := bstep (se 3 (by rfl) ⟨1200503, by rfl⟩ : syracuseStep 6402685 = 2401007) B2401007
theorem B15389351 : Blo 1686043 15389351 := bstep (se 1 (by rfl) ⟨11542013, by rfl⟩ : syracuseStep 15389351 = 23084027) B23084027
theorem B1686943 : Blo 1686043 1686943 := bstep (se 1 (by rfl) ⟨1265207, by rfl⟩ : syracuseStep 1686943 = 2530415) B2530415
theorem B8536913 : Blo 1686043 8536913 := bstep (se 2 (by rfl) ⟨3201342, by rfl⟩ : syracuseStep 8536913 = 6402685) B6402685
theorem B58459421 : Blo 1686043 58459421 := bstep (se 3 (by rfl) ⟨10961141, by rfl⟩ : syracuseStep 58459421 = 21922283) B21922283
theorem B10259567 : Blo 1686043 10259567 := bstep (se 1 (by rfl) ⟨7694675, by rfl⟩ : syracuseStep 10259567 = 15389351) B15389351
theorem B87660427 : Blo 1686043 87660427 := bstep (se 1 (by rfl) ⟨65745320, by rfl⟩ : syracuseStep 87660427 = 131490641) B131490641
theorem B116880569 : Blo 1686043 116880569 := bstep (se 2 (by rfl) ⟨43830213, by rfl⟩ : syracuseStep 116880569 = 87660427) B87660427
theorem B5691275 : Blo 1686043 5691275 := bstep (se 1 (by rfl) ⟨4268456, by rfl⟩ : syracuseStep 5691275 = 8536913) B8536913
theorem B155891789 : Blo 1686043 155891789 := bstep (se 3 (by rfl) ⟨29229710, by rfl⟩ : syracuseStep 155891789 = 58459421) B58459421
theorem B6839711 : Blo 1686043 6839711 := bstep (se 1 (by rfl) ⟨5129783, by rfl⟩ : syracuseStep 6839711 = 10259567) B10259567
theorem B3794183 : Blo 1686043 3794183 := bstep (se 1 (by rfl) ⟨2845637, by rfl⟩ : syracuseStep 3794183 = 5691275) B5691275
theorem B103927859 : Blo 1686043 103927859 := bstep (se 1 (by rfl) ⟨77945894, by rfl⟩ : syracuseStep 103927859 = 155891789) B155891789
theorem B4559807 : Blo 1686043 4559807 := bstep (se 1 (by rfl) ⟨3419855, by rfl⟩ : syracuseStep 4559807 = 6839711) B6839711
theorem B77920379 : Blo 1686043 77920379 := bstep (se 1 (by rfl) ⟨58440284, by rfl⟩ : syracuseStep 77920379 = 116880569) B116880569
theorem B3039871 : Blo 1686043 3039871 := bstep (se 1 (by rfl) ⟨2279903, by rfl⟩ : syracuseStep 3039871 = 4559807) B4559807
theorem B51946919 : Blo 1686043 51946919 := bstep (se 1 (by rfl) ⟨38960189, by rfl⟩ : syracuseStep 51946919 = 77920379) B77920379
theorem B69285239 : Blo 1686043 69285239 := bstep (se 1 (by rfl) ⟨51963929, by rfl⟩ : syracuseStep 69285239 = 103927859) B103927859
theorem B2529455 : Blo 1686043 2529455 := bstep (se 1 (by rfl) ⟨1897091, by rfl⟩ : syracuseStep 2529455 = 3794183) B3794183
theorem B46190159 : Blo 1686043 46190159 := bstep (se 1 (by rfl) ⟨34642619, by rfl⟩ : syracuseStep 46190159 = 69285239) B69285239
theorem B34631279 : Blo 1686043 34631279 := bstep (se 1 (by rfl) ⟨25973459, by rfl⟩ : syracuseStep 34631279 = 51946919) B51946919
theorem B4053161 : Blo 1686043 4053161 := bstep (se 2 (by rfl) ⟨1519935, by rfl⟩ : syracuseStep 4053161 = 3039871) B3039871
theorem B1686303 : Blo 1686043 1686303 := bstep (se 1 (by rfl) ⟨1264727, by rfl⟩ : syracuseStep 1686303 = 2529455) B2529455
theorem B23087519 : Blo 1686043 23087519 := bstep (se 1 (by rfl) ⟨17315639, by rfl⟩ : syracuseStep 23087519 = 34631279) B34631279
theorem B2702107 : Blo 1686043 2702107 := bstep (se 1 (by rfl) ⟨2026580, by rfl⟩ : syracuseStep 2702107 = 4053161) B4053161
theorem B30793439 : Blo 1686043 30793439 := bstep (se 1 (by rfl) ⟨23095079, by rfl⟩ : syracuseStep 30793439 = 46190159) B46190159
theorem B3602809 : Blo 1686043 3602809 := bstep (se 2 (by rfl) ⟨1351053, by rfl⟩ : syracuseStep 3602809 = 2702107) B2702107
theorem B15391679 : Blo 1686043 15391679 := bstep (se 1 (by rfl) ⟨11543759, by rfl⟩ : syracuseStep 15391679 = 23087519) B23087519
theorem B20528959 : Blo 1686043 20528959 := bstep (se 1 (by rfl) ⟨15396719, by rfl⟩ : syracuseStep 20528959 = 30793439) B30793439
theorem B27371945 : Blo 1686043 27371945 := bstep (se 2 (by rfl) ⟨10264479, by rfl⟩ : syracuseStep 27371945 = 20528959) B20528959
theorem B41044477 : Blo 1686043 41044477 := bstep (se 3 (by rfl) ⟨7695839, by rfl⟩ : syracuseStep 41044477 = 15391679) B15391679
theorem B19214981 : Blo 1686043 19214981 := bstep (se 4 (by rfl) ⟨1801404, by rfl⟩ : syracuseStep 19214981 = 3602809) B3602809
theorem B54725969 : Blo 1686043 54725969 := bstep (se 2 (by rfl) ⟨20522238, by rfl⟩ : syracuseStep 54725969 = 41044477) B41044477
theorem B18247963 : Blo 1686043 18247963 := bstep (se 1 (by rfl) ⟨13685972, by rfl⟩ : syracuseStep 18247963 = 27371945) B27371945
theorem B12809987 : Blo 1686043 12809987 := bstep (se 1 (by rfl) ⟨9607490, by rfl⟩ : syracuseStep 12809987 = 19214981) B19214981
theorem B24330617 : Blo 1686043 24330617 := bstep (se 2 (by rfl) ⟨9123981, by rfl⟩ : syracuseStep 24330617 = 18247963) B18247963
theorem B8539991 : Blo 1686043 8539991 := bstep (se 1 (by rfl) ⟨6404993, by rfl⟩ : syracuseStep 8539991 = 12809987) B12809987
theorem B36483979 : Blo 1686043 36483979 := bstep (se 1 (by rfl) ⟨27362984, by rfl⟩ : syracuseStep 36483979 = 54725969) B54725969
theorem B16220411 : Blo 1686043 16220411 := bstep (se 1 (by rfl) ⟨12165308, by rfl⟩ : syracuseStep 16220411 = 24330617) B24330617
theorem B48645305 : Blo 1686043 48645305 := bstep (se 2 (by rfl) ⟨18241989, by rfl⟩ : syracuseStep 48645305 = 36483979) B36483979
theorem B5693327 : Blo 1686043 5693327 := bstep (se 1 (by rfl) ⟨4269995, by rfl⟩ : syracuseStep 5693327 = 8539991) B8539991
theorem B10813607 : Blo 1686043 10813607 := bstep (se 1 (by rfl) ⟨8110205, by rfl⟩ : syracuseStep 10813607 = 16220411) B16220411
theorem B3795551 : Blo 1686043 3795551 := bstep (se 1 (by rfl) ⟨2846663, by rfl⟩ : syracuseStep 3795551 = 5693327) B5693327
theorem B32430203 : Blo 1686043 32430203 := bstep (se 1 (by rfl) ⟨24322652, by rfl⟩ : syracuseStep 32430203 = 48645305) B48645305
theorem B7209071 : Blo 1686043 7209071 := bstep (se 1 (by rfl) ⟨5406803, by rfl⟩ : syracuseStep 7209071 = 10813607) B10813607
theorem B21620135 : Blo 1686043 21620135 := bstep (se 1 (by rfl) ⟨16215101, by rfl⟩ : syracuseStep 21620135 = 32430203) B32430203
theorem B2530367 : Blo 1686043 2530367 := bstep (se 1 (by rfl) ⟨1897775, by rfl⟩ : syracuseStep 2530367 = 3795551) B3795551
theorem B14413423 : Blo 1686043 14413423 := bstep (se 1 (by rfl) ⟨10810067, by rfl⟩ : syracuseStep 14413423 = 21620135) B21620135
theorem B4806047 : Blo 1686043 4806047 := bstep (se 1 (by rfl) ⟨3604535, by rfl⟩ : syracuseStep 4806047 = 7209071) B7209071
theorem B1686911 : Blo 1686043 1686911 := bstep (se 1 (by rfl) ⟨1265183, by rfl⟩ : syracuseStep 1686911 = 2530367) B2530367
theorem B3204031 : Blo 1686043 3204031 := bstep (se 1 (by rfl) ⟨2403023, by rfl⟩ : syracuseStep 3204031 = 4806047) B4806047
theorem B19217897 : Blo 1686043 19217897 := bstep (se 2 (by rfl) ⟨7206711, by rfl⟩ : syracuseStep 19217897 = 14413423) B14413423
theorem B4272041 : Blo 1686043 4272041 := bstep (se 2 (by rfl) ⟨1602015, by rfl⟩ : syracuseStep 4272041 = 3204031) B3204031
theorem B12811931 : Blo 1686043 12811931 := bstep (se 1 (by rfl) ⟨9608948, by rfl⟩ : syracuseStep 12811931 = 19217897) B19217897
theorem B8541287 : Blo 1686043 8541287 := bstep (se 1 (by rfl) ⟨6405965, by rfl⟩ : syracuseStep 8541287 = 12811931) B12811931
theorem B2848027 : Blo 1686043 2848027 := bstep (se 1 (by rfl) ⟨2136020, by rfl⟩ : syracuseStep 2848027 = 4272041) B4272041
theorem B5694191 : Blo 1686043 5694191 := bstep (se 1 (by rfl) ⟨4270643, by rfl⟩ : syracuseStep 5694191 = 8541287) B8541287
theorem B3797369 : Blo 1686043 3797369 := bstep (se 2 (by rfl) ⟨1424013, by rfl⟩ : syracuseStep 3797369 = 2848027) B2848027
theorem B2531579 : Blo 1686043 2531579 := bstep (se 1 (by rfl) ⟨1898684, by rfl⟩ : syracuseStep 2531579 = 3797369) B3797369
theorem B3796127 : Blo 1686043 3796127 := bstep (se 1 (by rfl) ⟨2847095, by rfl⟩ : syracuseStep 3796127 = 5694191) B5694191
theorem B1687719 : Blo 1686043 1687719 := bstep (se 1 (by rfl) ⟨1265789, by rfl⟩ : syracuseStep 1687719 = 2531579) B2531579
theorem B2530751 : Blo 1686043 2530751 := bstep (se 1 (by rfl) ⟨1898063, by rfl⟩ : syracuseStep 2530751 = 3796127) B3796127
theorem B1687167 : Blo 1686043 1687167 := bstep (se 1 (by rfl) ⟨1265375, by rfl⟩ : syracuseStep 1687167 = 2530751) B2530751

theorem C0 (j : ℕ) (h1 : 421510 ≤ j) (h2 : j ≤ 422010) : Blo 1686043 (4 * j + 3) := by
  interval_cases j
  · exact B1686043
  · exact B1686047
  · exact B1686051
  · exact B1686055
  · exact B1686059
  · exact B1686063
  · exact B1686067
  · exact B1686071
  · exact B1686075
  · exact B1686079
  · exact B1686083
  · exact B1686087
  · exact B1686091
  · exact B1686095
  · exact B1686099
  · exact B1686103
  · exact B1686107
  · exact B1686111
  · exact B1686115
  · exact B1686119
  · exact B1686123
  · exact B1686127
  · exact B1686131
  · exact B1686135
  · exact B1686139
  · exact B1686143
  · exact B1686147
  · exact B1686151
  · exact B1686155
  · exact B1686159
  · exact B1686163
  · exact B1686167
  · exact B1686171
  · exact B1686175
  · exact B1686179
  · exact B1686183
  · exact B1686187
  · exact B1686191
  · exact B1686195
  · exact B1686199
  · exact B1686203
  · exact B1686207
  · exact B1686211
  · exact B1686215
  · exact B1686219
  · exact B1686223
  · exact B1686227
  · exact B1686231
  · exact B1686235
  · exact B1686239
  · exact B1686243
  · exact B1686247
  · exact B1686251
  · exact B1686255
  · exact B1686259
  · exact B1686263
  · exact B1686267
  · exact B1686271
  · exact B1686275
  · exact B1686279
  · exact B1686283
  · exact B1686287
  · exact B1686291
  · exact B1686295
  · exact B1686299
  · exact B1686303
  · exact B1686307
  · exact B1686311
  · exact B1686315
  · exact B1686319
  · exact B1686323
  · exact B1686327
  · exact B1686331
  · exact B1686335
  · exact B1686339
  · exact B1686343
  · exact B1686347
  · exact B1686351
  · exact B1686355
  · exact B1686359
  · exact B1686363
  · exact B1686367
  · exact B1686371
  · exact B1686375
  · exact B1686379
  · exact B1686383
  · exact B1686387
  · exact B1686391
  · exact B1686395
  · exact B1686399
  · exact B1686403
  · exact B1686407
  · exact B1686411
  · exact B1686415
  · exact B1686419
  · exact B1686423
  · exact B1686427
  · exact B1686431
  · exact B1686435
  · exact B1686439
  · exact B1686443
  · exact B1686447
  · exact B1686451
  · exact B1686455
  · exact B1686459
  · exact B1686463
  · exact B1686467
  · exact B1686471
  · exact B1686475
  · exact B1686479
  · exact B1686483
  · exact B1686487
  · exact B1686491
  · exact B1686495
  · exact B1686499
  · exact B1686503
  · exact B1686507
  · exact B1686511
  · exact B1686515
  · exact B1686519
  · exact B1686523
  · exact B1686527
  · exact B1686531
  · exact B1686535
  · exact B1686539
  · exact B1686543
  · exact B1686547
  · exact B1686551
  · exact B1686555
  · exact B1686559
  · exact B1686563
  · exact B1686567
  · exact B1686571
  · exact B1686575
  · exact B1686579
  · exact B1686583
  · exact B1686587
  · exact B1686591
  · exact B1686595
  · exact B1686599
  · exact B1686603
  · exact B1686607
  · exact B1686611
  · exact B1686615
  · exact B1686619
  · exact B1686623
  · exact B1686627
  · exact B1686631
  · exact B1686635
  · exact B1686639
  · exact B1686643
  · exact B1686647
  · exact B1686651
  · exact B1686655
  · exact B1686659
  · exact B1686663
  · exact B1686667
  · exact B1686671
  · exact B1686675
  · exact B1686679
  · exact B1686683
  · exact B1686687
  · exact B1686691
  · exact B1686695
  · exact B1686699
  · exact B1686703
  · exact B1686707
  · exact B1686711
  · exact B1686715
  · exact B1686719
  · exact B1686723
  · exact B1686727
  · exact B1686731
  · exact B1686735
  · exact B1686739
  · exact B1686743
  · exact B1686747
  · exact B1686751
  · exact B1686755
  · exact B1686759
  · exact B1686763
  · exact B1686767
  · exact B1686771
  · exact B1686775
  · exact B1686779
  · exact B1686783
  · exact B1686787
  · exact B1686791
  · exact B1686795
  · exact B1686799
  · exact B1686803
  · exact B1686807
  · exact B1686811
  · exact B1686815
  · exact B1686819
  · exact B1686823
  · exact B1686827
  · exact B1686831
  · exact B1686835
  · exact B1686839
  · exact B1686843
  · exact B1686847
  · exact B1686851
  · exact B1686855
  · exact B1686859
  · exact B1686863
  · exact B1686867
  · exact B1686871
  · exact B1686875
  · exact B1686879
  · exact B1686883
  · exact B1686887
  · exact B1686891
  · exact B1686895
  · exact B1686899
  · exact B1686903
  · exact B1686907
  · exact B1686911
  · exact B1686915
  · exact B1686919
  · exact B1686923
  · exact B1686927
  · exact B1686931
  · exact B1686935
  · exact B1686939
  · exact B1686943
  · exact B1686947
  · exact B1686951
  · exact B1686955
  · exact B1686959
  · exact B1686963
  · exact B1686967
  · exact B1686971
  · exact B1686975
  · exact B1686979
  · exact B1686983
  · exact B1686987
  · exact B1686991
  · exact B1686995
  · exact B1686999
  · exact B1687003
  · exact B1687007
  · exact B1687011
  · exact B1687015
  · exact B1687019
  · exact B1687023
  · exact B1687027
  · exact B1687031
  · exact B1687035
  · exact B1687039
  · exact B1687043
  · exact B1687047
  · exact B1687051
  · exact B1687055
  · exact B1687059
  · exact B1687063
  · exact B1687067
  · exact B1687071
  · exact B1687075
  · exact B1687079
  · exact B1687083
  · exact B1687087
  · exact B1687091
  · exact B1687095
  · exact B1687099
  · exact B1687103
  · exact B1687107
  · exact B1687111
  · exact B1687115
  · exact B1687119
  · exact B1687123
  · exact B1687127
  · exact B1687131
  · exact B1687135
  · exact B1687139
  · exact B1687143
  · exact B1687147
  · exact B1687151
  · exact B1687155
  · exact B1687159
  · exact B1687163
  · exact B1687167
  · exact B1687171
  · exact B1687175
  · exact B1687179
  · exact B1687183
  · exact B1687187
  · exact B1687191
  · exact B1687195
  · exact B1687199
  · exact B1687203
  · exact B1687207
  · exact B1687211
  · exact B1687215
  · exact B1687219
  · exact B1687223
  · exact B1687227
  · exact B1687231
  · exact B1687235
  · exact B1687239
  · exact B1687243
  · exact B1687247
  · exact B1687251
  · exact B1687255
  · exact B1687259
  · exact B1687263
  · exact B1687267
  · exact B1687271
  · exact B1687275
  · exact B1687279
  · exact B1687283
  · exact B1687287
  · exact B1687291
  · exact B1687295
  · exact B1687299
  · exact B1687303
  · exact B1687307
  · exact B1687311
  · exact B1687315
  · exact B1687319
  · exact B1687323
  · exact B1687327
  · exact B1687331
  · exact B1687335
  · exact B1687339
  · exact B1687343
  · exact B1687347
  · exact B1687351
  · exact B1687355
  · exact B1687359
  · exact B1687363
  · exact B1687367
  · exact B1687371
  · exact B1687375
  · exact B1687379
  · exact B1687383
  · exact B1687387
  · exact B1687391
  · exact B1687395
  · exact B1687399
  · exact B1687403
  · exact B1687407
  · exact B1687411
  · exact B1687415
  · exact B1687419
  · exact B1687423
  · exact B1687427
  · exact B1687431
  · exact B1687435
  · exact B1687439
  · exact B1687443
  · exact B1687447
  · exact B1687451
  · exact B1687455
  · exact B1687459
  · exact B1687463
  · exact B1687467
  · exact B1687471
  · exact B1687475
  · exact B1687479
  · exact B1687483
  · exact B1687487
  · exact B1687491
  · exact B1687495
  · exact B1687499
  · exact B1687503
  · exact B1687507
  · exact B1687511
  · exact B1687515
  · exact B1687519
  · exact B1687523
  · exact B1687527
  · exact B1687531
  · exact B1687535
  · exact B1687539
  · exact B1687543
  · exact B1687547
  · exact B1687551
  · exact B1687555
  · exact B1687559
  · exact B1687563
  · exact B1687567
  · exact B1687571
  · exact B1687575
  · exact B1687579
  · exact B1687583
  · exact B1687587
  · exact B1687591
  · exact B1687595
  · exact B1687599
  · exact B1687603
  · exact B1687607
  · exact B1687611
  · exact B1687615
  · exact B1687619
  · exact B1687623
  · exact B1687627
  · exact B1687631
  · exact B1687635
  · exact B1687639
  · exact B1687643
  · exact B1687647
  · exact B1687651
  · exact B1687655
  · exact B1687659
  · exact B1687663
  · exact B1687667
  · exact B1687671
  · exact B1687675
  · exact B1687679
  · exact B1687683
  · exact B1687687
  · exact B1687691
  · exact B1687695
  · exact B1687699
  · exact B1687703
  · exact B1687707
  · exact B1687711
  · exact B1687715
  · exact B1687719
  · exact B1687723
  · exact B1687727
  · exact B1687731
  · exact B1687735
  · exact B1687739
  · exact B1687743
  · exact B1687747
  · exact B1687751
  · exact B1687755
  · exact B1687759
  · exact B1687763
  · exact B1687767
  · exact B1687771
  · exact B1687775
  · exact B1687779
  · exact B1687783
  · exact B1687787
  · exact B1687791
  · exact B1687795
  · exact B1687799
  · exact B1687803
  · exact B1687807
  · exact B1687811
  · exact B1687815
  · exact B1687819
  · exact B1687823
  · exact B1687827
  · exact B1687831
  · exact B1687835
  · exact B1687839
  · exact B1687843
  · exact B1687847
  · exact B1687851
  · exact B1687855
  · exact B1687859
  · exact B1687863
  · exact B1687867
  · exact B1687871
  · exact B1687875
  · exact B1687879
  · exact B1687883
  · exact B1687887
  · exact B1687891
  · exact B1687895
  · exact B1687899
  · exact B1687903
  · exact B1687907
  · exact B1687911
  · exact B1687915
  · exact B1687919
  · exact B1687923
  · exact B1687927
  · exact B1687931
  · exact B1687935
  · exact B1687939
  · exact B1687943
  · exact B1687947
  · exact B1687951
  · exact B1687955
  · exact B1687959
  · exact B1687963
  · exact B1687967
  · exact B1687971
  · exact B1687975
  · exact B1687979
  · exact B1687983
  · exact B1687987
  · exact B1687991
  · exact B1687995
  · exact B1687999
  · exact B1688003
  · exact B1688007
  · exact B1688011
  · exact B1688015
  · exact B1688019
  · exact B1688023
  · exact B1688027
  · exact B1688031
  · exact B1688035
  · exact B1688039
  · exact B1688043

theorem solution (m : ℕ) (hlo : 1686043 ≤ m) (hhi : m ≤ 1688043) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 421510 ≤ j := by omega
    have hj2 : j ≤ 422010 := by omega
    have hb : Blo 1686043 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
