-- Prove2me | solution 1 for syracuse_descends_range_1190412_1192412
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:38.682574+00:00
-- url     : https://prove2.me/submissions/c44e10d1-9034-44ad-8e01-cbf985ba9942

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


theorem B3817477 : Blo 1190412 3817477 := bbase (se 4 (by rfl) ⟨357888, by rfl⟩ : syracuseStep 3817477 = 715777) (by norm_num)
theorem B1785869 : Blo 1190412 1785869 := bbase (se 3 (by rfl) ⟨334850, by rfl⟩ : syracuseStep 1785869 = 669701) (by norm_num)
theorem B1695757 : Blo 1190412 1695757 := bbase (se 3 (by rfl) ⟨317954, by rfl⟩ : syracuseStep 1695757 = 635909) (by norm_num)
theorem B1507349 : Blo 1190412 1507349 := bbase (se 6 (by rfl) ⟨35328, by rfl⟩ : syracuseStep 1507349 = 70657) (by norm_num)
theorem B2678813 : Blo 1190412 2678813 := bbase (se 3 (by rfl) ⟨502277, by rfl⟩ : syracuseStep 2678813 = 1004555) (by norm_num)
theorem B1785893 : Blo 1190412 1785893 := bbase (se 4 (by rfl) ⟨167427, by rfl⟩ : syracuseStep 1785893 = 334855) (by norm_num)
theorem B5161013 : Blo 1190412 5161013 := bbase (se 5 (by rfl) ⟨241922, by rfl⟩ : syracuseStep 5161013 = 483845) (by norm_num)
theorem B1785917 : Blo 1190412 1785917 := bbase (se 3 (by rfl) ⟨334859, by rfl⟩ : syracuseStep 1785917 = 669719) (by norm_num)
theorem B1507405 : Blo 1190412 1507405 := bbase (se 3 (by rfl) ⟨282638, by rfl⟩ : syracuseStep 1507405 = 565277) (by norm_num)
theorem B1785941 : Blo 1190412 1785941 := bbase (se 8 (by rfl) ⟨10464, by rfl⟩ : syracuseStep 1785941 = 20929) (by norm_num)
theorem B2678885 : Blo 1190412 2678885 := bbase (se 4 (by rfl) ⟨251145, by rfl⟩ : syracuseStep 2678885 = 502291) (by norm_num)
theorem B1785965 : Blo 1190412 1785965 := bbase (se 3 (by rfl) ⟨334868, by rfl⟩ : syracuseStep 1785965 = 669737) (by norm_num)
theorem B1785989 : Blo 1190412 1785989 := bbase (se 4 (by rfl) ⟨167436, by rfl⟩ : syracuseStep 1785989 = 334873) (by norm_num)
theorem B4022405 : Blo 1190412 4022405 := bbase (se 4 (by rfl) ⟨377100, by rfl⟩ : syracuseStep 4022405 = 754201) (by norm_num)
theorem B1786013 : Blo 1190412 1786013 := bbase (se 3 (by rfl) ⟨334877, by rfl⟩ : syracuseStep 1786013 = 669755) (by norm_num)
theorem B1908893 : Blo 1190412 1908893 := bbase (se 3 (by rfl) ⟨357917, by rfl⟩ : syracuseStep 1908893 = 715835) (by norm_num)
theorem B6029477 : Blo 1190412 6029477 := bbase (se 4 (by rfl) ⟨565263, by rfl⟩ : syracuseStep 6029477 = 1130527) (by norm_num)
theorem B2678957 : Blo 1190412 2678957 := bbase (se 3 (by rfl) ⟨502304, by rfl⟩ : syracuseStep 2678957 = 1004609) (by norm_num)
theorem B1507501 : Blo 1190412 1507501 := bbase (se 3 (by rfl) ⟨282656, by rfl⟩ : syracuseStep 1507501 = 565313) (by norm_num)
theorem B1786037 : Blo 1190412 1786037 := bbase (se 5 (by rfl) ⟨83720, by rfl⟩ : syracuseStep 1786037 = 167441) (by norm_num)
theorem B1786061 : Blo 1190412 1786061 := bbase (se 3 (by rfl) ⟨334886, by rfl⟩ : syracuseStep 1786061 = 669773) (by norm_num)
theorem B1786085 : Blo 1190412 1786085 := bbase (se 4 (by rfl) ⟨167445, by rfl⟩ : syracuseStep 1786085 = 334891) (by norm_num)
theorem B1695973 : Blo 1190412 1695973 := bbase (se 4 (by rfl) ⟨158997, by rfl⟩ : syracuseStep 1695973 = 317995) (by norm_num)
theorem B2679029 : Blo 1190412 2679029 := bbase (se 5 (by rfl) ⟨125579, by rfl⟩ : syracuseStep 2679029 = 251159) (by norm_num)
theorem B1786109 : Blo 1190412 1786109 := bbase (se 3 (by rfl) ⟨334895, by rfl⟩ : syracuseStep 1786109 = 669791) (by norm_num)
theorem B1786133 : Blo 1190412 1786133 := bbase (se 6 (by rfl) ⟨41862, by rfl⟩ : syracuseStep 1786133 = 83725) (by norm_num)
theorem B3014941 : Blo 1190412 3014941 := bbase (se 3 (by rfl) ⟨565301, by rfl⟩ : syracuseStep 3014941 = 1130603) (by norm_num)
theorem B1909021 : Blo 1190412 1909021 := bbase (se 3 (by rfl) ⟨357941, by rfl⟩ : syracuseStep 1909021 = 715883) (by norm_num)
theorem B2449693 : Blo 1190412 2449693 := bbase (se 3 (by rfl) ⟨459317, by rfl⟩ : syracuseStep 2449693 = 918635) (by norm_num)
theorem B1786157 : Blo 1190412 1786157 := bbase (se 3 (by rfl) ⟨334904, by rfl⟩ : syracuseStep 1786157 = 669809) (by norm_num)
theorem B2679101 : Blo 1190412 2679101 := bbase (se 3 (by rfl) ⟨502331, by rfl⟩ : syracuseStep 2679101 = 1004663) (by norm_num)
theorem B1786181 : Blo 1190412 1786181 := bbase (se 4 (by rfl) ⟨167454, by rfl⟩ : syracuseStep 1786181 = 334909) (by norm_num)
theorem B5431637 : Blo 1190412 5431637 := bbase (se 10 (by rfl) ⟨7956, by rfl⟩ : syracuseStep 5431637 = 15913) (by norm_num)
theorem B1507673 : Blo 1190412 1507673 := bbase (se 2 (by rfl) ⟨565377, by rfl⟩ : syracuseStep 1507673 = 1130755) (by norm_num)
theorem B1786205 : Blo 1190412 1786205 := bbase (se 3 (by rfl) ⟨334913, by rfl⟩ : syracuseStep 1786205 = 669827) (by norm_num)
theorem B1786229 : Blo 1190412 1786229 := bbase (se 5 (by rfl) ⟨83729, by rfl⟩ : syracuseStep 1786229 = 167459) (by norm_num)
theorem B2679173 : Blo 1190412 2679173 := bbase (se 4 (by rfl) ⟨251172, by rfl⟩ : syracuseStep 2679173 = 502345) (by norm_num)
theorem B1786253 : Blo 1190412 1786253 := bbase (se 3 (by rfl) ⟨334922, by rfl⟩ : syracuseStep 1786253 = 669845) (by norm_num)
theorem B3015053 : Blo 1190412 3015053 := bbase (se 3 (by rfl) ⟨565322, by rfl⟩ : syracuseStep 3015053 = 1130645) (by norm_num)
theorem B1507729 : Blo 1190412 1507729 := bbase (se 2 (by rfl) ⟨565398, by rfl⟩ : syracuseStep 1507729 = 1130797) (by norm_num)
theorem B2417045 : Blo 1190412 2417045 := bbase (se 6 (by rfl) ⟨56649, by rfl⟩ : syracuseStep 2417045 = 113299) (by norm_num)
theorem B1786277 : Blo 1190412 1786277 := bbase (se 4 (by rfl) ⟨167463, by rfl⟩ : syracuseStep 1786277 = 334927) (by norm_num)
theorem B1786301 : Blo 1190412 1786301 := bbase (se 3 (by rfl) ⟨334931, by rfl⟩ : syracuseStep 1786301 = 669863) (by norm_num)
theorem B2679245 : Blo 1190412 2679245 := bbase (se 3 (by rfl) ⟨502358, by rfl⟩ : syracuseStep 2679245 = 1004717) (by norm_num)
theorem B1786325 : Blo 1190412 1786325 := bbase (se 7 (by rfl) ⟨20933, by rfl⟩ : syracuseStep 1786325 = 41867) (by norm_num)
theorem B1786349 : Blo 1190412 1786349 := bbase (se 3 (by rfl) ⟨334940, by rfl⟩ : syracuseStep 1786349 = 669881) (by norm_num)
theorem B1507825 : Blo 1190412 1507825 := bbase (se 2 (by rfl) ⟨565434, by rfl⟩ : syracuseStep 1507825 = 1130869) (by norm_num)
theorem B1786373 : Blo 1190412 1786373 := bbase (se 4 (by rfl) ⟨167472, by rfl⟩ : syracuseStep 1786373 = 334945) (by norm_num)
theorem B2679317 : Blo 1190412 2679317 := bbase (se 6 (by rfl) ⟨62796, by rfl⟩ : syracuseStep 2679317 = 125593) (by norm_num)
theorem B6439445 : Blo 1190412 6439445 := bbase (se 6 (by rfl) ⟨150924, by rfl⟩ : syracuseStep 6439445 = 301849) (by norm_num)
theorem B1786397 : Blo 1190412 1786397 := bbase (se 3 (by rfl) ⟨334949, by rfl⟩ : syracuseStep 1786397 = 669899) (by norm_num)
theorem B2261533 : Blo 1190412 2261533 := bbase (se 3 (by rfl) ⟨424037, by rfl⟩ : syracuseStep 2261533 = 848075) (by norm_num)
theorem B1786421 : Blo 1190412 1786421 := bbase (se 5 (by rfl) ⟨83738, by rfl⟩ : syracuseStep 1786421 = 167477) (by norm_num)
theorem B4022837 : Blo 1190412 4022837 := bbase (se 5 (by rfl) ⟨188570, by rfl⟩ : syracuseStep 4022837 = 377141) (by norm_num)
theorem B1786445 : Blo 1190412 1786445 := bbase (se 3 (by rfl) ⟨334958, by rfl⟩ : syracuseStep 1786445 = 669917) (by norm_num)
theorem B3015245 : Blo 1190412 3015245 := bbase (se 3 (by rfl) ⟨565358, by rfl⟩ : syracuseStep 3015245 = 1130717) (by norm_num)
theorem B2679389 : Blo 1190412 2679389 := bbase (se 3 (by rfl) ⟨502385, by rfl⟩ : syracuseStep 2679389 = 1004771) (by norm_num)
theorem B1696349 : Blo 1190412 1696349 := bbase (se 3 (by rfl) ⟨318065, by rfl⟩ : syracuseStep 1696349 = 636131) (by norm_num)
theorem B2482781 : Blo 1190412 2482781 := bbase (se 3 (by rfl) ⟨465521, by rfl⟩ : syracuseStep 2482781 = 931043) (by norm_num)
theorem B1786469 : Blo 1190412 1786469 := bbase (se 4 (by rfl) ⟨167481, by rfl⟩ : syracuseStep 1786469 = 334963) (by norm_num)
theorem B1786493 : Blo 1190412 1786493 := bbase (se 3 (by rfl) ⟨334967, by rfl⟩ : syracuseStep 1786493 = 669935) (by norm_num)
theorem B1786517 : Blo 1190412 1786517 := bbase (se 6 (by rfl) ⟨41871, by rfl⟩ : syracuseStep 1786517 = 83743) (by norm_num)
theorem B1507997 : Blo 1190412 1507997 := bbase (se 3 (by rfl) ⟨282749, by rfl⟩ : syracuseStep 1507997 = 565499) (by norm_num)
theorem B2679461 : Blo 1190412 2679461 := bbase (se 4 (by rfl) ⟨251199, by rfl⟩ : syracuseStep 2679461 = 502399) (by norm_num)
theorem B1786541 : Blo 1190412 1786541 := bbase (se 3 (by rfl) ⟨334976, by rfl⟩ : syracuseStep 1786541 = 669953) (by norm_num)
theorem B2261677 : Blo 1190412 2261677 := bbase (se 3 (by rfl) ⟨424064, by rfl⟩ : syracuseStep 2261677 = 848129) (by norm_num)
theorem B1786565 : Blo 1190412 1786565 := bbase (se 4 (by rfl) ⟨167490, by rfl⟩ : syracuseStep 1786565 = 334981) (by norm_num)
theorem B1508053 : Blo 1190412 1508053 := bbase (se 7 (by rfl) ⟨17672, by rfl⟩ : syracuseStep 1508053 = 35345) (by norm_num)
theorem B1786589 : Blo 1190412 1786589 := bbase (se 3 (by rfl) ⟨334985, by rfl⟩ : syracuseStep 1786589 = 669971) (by norm_num)
theorem B2679533 : Blo 1190412 2679533 := bbase (se 3 (by rfl) ⟨502412, by rfl⟩ : syracuseStep 2679533 = 1004825) (by norm_num)
theorem B1786613 : Blo 1190412 1786613 := bbase (se 5 (by rfl) ⟨83747, by rfl⟩ : syracuseStep 1786613 = 167495) (by norm_num)
theorem B1786637 : Blo 1190412 1786637 := bbase (se 3 (by rfl) ⟨334994, by rfl⟩ : syracuseStep 1786637 = 669989) (by norm_num)
theorem B1786661 : Blo 1190412 1786661 := bbase (se 4 (by rfl) ⟨167499, by rfl⟩ : syracuseStep 1786661 = 334999) (by norm_num)
theorem B2679605 : Blo 1190412 2679605 := bbase (se 5 (by rfl) ⟨125606, by rfl⟩ : syracuseStep 2679605 = 251213) (by norm_num)
theorem B1508149 : Blo 1190412 1508149 := bbase (se 5 (by rfl) ⟨70694, by rfl⟩ : syracuseStep 1508149 = 141389) (by norm_num)
theorem B1786685 : Blo 1190412 1786685 := bbase (se 3 (by rfl) ⟨335003, by rfl⟩ : syracuseStep 1786685 = 670007) (by norm_num)
theorem B2261837 : Blo 1190412 2261837 := bbase (se 3 (by rfl) ⟨424094, by rfl⟩ : syracuseStep 2261837 = 848189) (by norm_num)
theorem B1786709 : Blo 1190412 1786709 := bbase (se 9 (by rfl) ⟨5234, by rfl⟩ : syracuseStep 1786709 = 10469) (by norm_num)
theorem B4522837 : Blo 1190412 4522837 := bbase (se 9 (by rfl) ⟨13250, by rfl⟩ : syracuseStep 4522837 = 26501) (by norm_num)
theorem B1786733 : Blo 1190412 1786733 := bbase (se 3 (by rfl) ⟨335012, by rfl⟩ : syracuseStep 1786733 = 670025) (by norm_num)
theorem B2679677 : Blo 1190412 2679677 := bbase (se 3 (by rfl) ⟨502439, by rfl⟩ : syracuseStep 2679677 = 1004879) (by norm_num)
theorem B1786757 : Blo 1190412 1786757 := bbase (se 4 (by rfl) ⟨167508, by rfl⟩ : syracuseStep 1786757 = 335017) (by norm_num)
theorem B1786781 : Blo 1190412 1786781 := bbase (se 3 (by rfl) ⟨335021, by rfl⟩ : syracuseStep 1786781 = 670043) (by norm_num)
theorem B1909661 : Blo 1190412 1909661 := bbase (se 3 (by rfl) ⟨358061, by rfl⟩ : syracuseStep 1909661 = 716123) (by norm_num)
theorem B3015589 : Blo 1190412 3015589 := bbase (se 4 (by rfl) ⟨282711, by rfl⟩ : syracuseStep 3015589 = 565423) (by norm_num)
theorem B1786805 : Blo 1190412 1786805 := bbase (se 5 (by rfl) ⟨83756, by rfl⟩ : syracuseStep 1786805 = 167513) (by norm_num)
theorem B2679749 : Blo 1190412 2679749 := bbase (se 4 (by rfl) ⟨251226, by rfl⟩ : syracuseStep 2679749 = 502453) (by norm_num)
theorem B1786829 : Blo 1190412 1786829 := bbase (se 3 (by rfl) ⟨335030, by rfl⟩ : syracuseStep 1786829 = 670061) (by norm_num)
theorem B2261981 : Blo 1190412 2261981 := bbase (se 3 (by rfl) ⟨424121, by rfl⟩ : syracuseStep 2261981 = 848243) (by norm_num)
theorem B1508321 : Blo 1190412 1508321 := bbase (se 2 (by rfl) ⟨565620, by rfl⟩ : syracuseStep 1508321 = 1131241) (by norm_num)
theorem B1786853 : Blo 1190412 1786853 := bbase (se 4 (by rfl) ⟨167517, by rfl⟩ : syracuseStep 1786853 = 335035) (by norm_num)
theorem B4023269 : Blo 1190412 4023269 := bbase (se 4 (by rfl) ⟨377181, by rfl⟩ : syracuseStep 4023269 = 754363) (by norm_num)
theorem B1786877 : Blo 1190412 1786877 := bbase (se 3 (by rfl) ⟨335039, by rfl⟩ : syracuseStep 1786877 = 670079) (by norm_num)
theorem B2679821 : Blo 1190412 2679821 := bbase (se 3 (by rfl) ⟨502466, by rfl⟩ : syracuseStep 2679821 = 1004933) (by norm_num)
theorem B1786901 : Blo 1190412 1786901 := bbase (se 6 (by rfl) ⟨41880, by rfl⟩ : syracuseStep 1786901 = 83761) (by norm_num)
theorem B3015701 : Blo 1190412 3015701 := bbase (se 6 (by rfl) ⟨70680, by rfl⟩ : syracuseStep 3015701 = 141361) (by norm_num)
theorem B1508377 : Blo 1190412 1508377 := bbase (se 2 (by rfl) ⟨565641, by rfl⟩ : syracuseStep 1508377 = 1131283) (by norm_num)
theorem B1786925 : Blo 1190412 1786925 := bbase (se 3 (by rfl) ⟨335048, by rfl⟩ : syracuseStep 1786925 = 670097) (by norm_num)
theorem B1786949 : Blo 1190412 1786949 := bbase (se 4 (by rfl) ⟨167526, by rfl⟩ : syracuseStep 1786949 = 335053) (by norm_num)
theorem B2679893 : Blo 1190412 2679893 := bbase (se 8 (by rfl) ⟨15702, by rfl⟩ : syracuseStep 2679893 = 31405) (by norm_num)
theorem B10183765 : Blo 1190412 10183765 := bbase (se 8 (by rfl) ⟨59670, by rfl⟩ : syracuseStep 10183765 = 119341) (by norm_num)
theorem B1786973 : Blo 1190412 1786973 := bbase (se 3 (by rfl) ⟨335057, by rfl⟩ : syracuseStep 1786973 = 670115) (by norm_num)
theorem B1786997 : Blo 1190412 1786997 := bbase (se 5 (by rfl) ⟨83765, by rfl⟩ : syracuseStep 1786997 = 167531) (by norm_num)
theorem B1508473 : Blo 1190412 1508473 := bbase (se 2 (by rfl) ⟨565677, by rfl⟩ : syracuseStep 1508473 = 1131355) (by norm_num)
theorem B4523141 : Blo 1190412 4523141 := bbase (se 4 (by rfl) ⟨424044, by rfl⟩ : syracuseStep 4523141 = 848089) (by norm_num)
theorem B1787021 : Blo 1190412 1787021 := bbase (se 3 (by rfl) ⟨335066, by rfl⟩ : syracuseStep 1787021 = 670133) (by norm_num)
theorem B2679965 : Blo 1190412 2679965 := bbase (se 3 (by rfl) ⟨502493, by rfl⟩ : syracuseStep 2679965 = 1004987) (by norm_num)
theorem B1787045 : Blo 1190412 1787045 := bbase (se 4 (by rfl) ⟨167535, by rfl⟩ : syracuseStep 1787045 = 335071) (by norm_num)
theorem B1787069 : Blo 1190412 1787069 := bbase (se 3 (by rfl) ⟨335075, by rfl⟩ : syracuseStep 1787069 = 670151) (by norm_num)
theorem B1787093 : Blo 1190412 1787093 := bbase (se 7 (by rfl) ⟨20942, by rfl⟩ : syracuseStep 1787093 = 41885) (by norm_num)
theorem B3015893 : Blo 1190412 3015893 := bbase (se 7 (by rfl) ⟨35342, by rfl⟩ : syracuseStep 3015893 = 70685) (by norm_num)
theorem B3622117 : Blo 1190412 3622117 := bbase (se 4 (by rfl) ⟨339573, by rfl⟩ : syracuseStep 3622117 = 679147) (by norm_num)
theorem B2680037 : Blo 1190412 2680037 := bbase (se 4 (by rfl) ⟨251253, by rfl⟩ : syracuseStep 2680037 = 502507) (by norm_num)
theorem B1787117 : Blo 1190412 1787117 := bbase (se 3 (by rfl) ⟨335084, by rfl⟩ : syracuseStep 1787117 = 670169) (by norm_num)
theorem B2262269 : Blo 1190412 2262269 := bbase (se 3 (by rfl) ⟨424175, by rfl⟩ : syracuseStep 2262269 = 848351) (by norm_num)
theorem B1787141 : Blo 1190412 1787141 := bbase (se 4 (by rfl) ⟨167544, by rfl⟩ : syracuseStep 1787141 = 335089) (by norm_num)
theorem B1787165 : Blo 1190412 1787165 := bbase (se 3 (by rfl) ⟨335093, by rfl⟩ : syracuseStep 1787165 = 670187) (by norm_num)
theorem B1508645 : Blo 1190412 1508645 := bbase (se 4 (by rfl) ⟨141435, by rfl⟩ : syracuseStep 1508645 = 282871) (by norm_num)
theorem B2680109 : Blo 1190412 2680109 := bbase (se 3 (by rfl) ⟨502520, by rfl⟩ : syracuseStep 2680109 = 1005041) (by norm_num)
theorem B1787189 : Blo 1190412 1787189 := bbase (se 5 (by rfl) ⟨83774, by rfl⟩ : syracuseStep 1787189 = 167549) (by norm_num)
theorem B5432645 : Blo 1190412 5432645 := bbase (se 4 (by rfl) ⟨509310, by rfl⟩ : syracuseStep 5432645 = 1018621) (by norm_num)
theorem B1787213 : Blo 1190412 1787213 := bbase (se 3 (by rfl) ⟨335102, by rfl⟩ : syracuseStep 1787213 = 670205) (by norm_num)
theorem B1508701 : Blo 1190412 1508701 := bbase (se 3 (by rfl) ⟨282881, by rfl⟩ : syracuseStep 1508701 = 565763) (by norm_num)
theorem B1787237 : Blo 1190412 1787237 := bbase (se 4 (by rfl) ⟨167553, by rfl⟩ : syracuseStep 1787237 = 335107) (by norm_num)
theorem B2680181 : Blo 1190412 2680181 := bbase (se 5 (by rfl) ⟨125633, by rfl⟩ : syracuseStep 2680181 = 251267) (by norm_num)
theorem B1860989 : Blo 1190412 1860989 := bbase (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) (by norm_num)
theorem B1787261 : Blo 1190412 1787261 := bbase (se 3 (by rfl) ⟨335111, by rfl⟩ : syracuseStep 1787261 = 670223) (by norm_num)
theorem B7243157 : Blo 1190412 7243157 := bbase (se 6 (by rfl) ⟨169761, by rfl⟩ : syracuseStep 7243157 = 339523) (by norm_num)
theorem B1787285 : Blo 1190412 1787285 := bbase (se 6 (by rfl) ⟨41889, by rfl⟩ : syracuseStep 1787285 = 83779) (by norm_num)
theorem B2262421 : Blo 1190412 2262421 := bbase (se 6 (by rfl) ⟨53025, by rfl⟩ : syracuseStep 2262421 = 106051) (by norm_num)
theorem B4023701 : Blo 1190412 4023701 := bbase (se 6 (by rfl) ⟨94305, by rfl⟩ : syracuseStep 4023701 = 188611) (by norm_num)
theorem B3220901 : Blo 1190412 3220901 := bbase (se 4 (by rfl) ⟨301959, by rfl⟩ : syracuseStep 3220901 = 603919) (by norm_num)
theorem B1787309 : Blo 1190412 1787309 := bbase (se 3 (by rfl) ⟨335120, by rfl⟩ : syracuseStep 1787309 = 670241) (by norm_num)
theorem B6030773 : Blo 1190412 6030773 := bbase (se 5 (by rfl) ⟨282692, by rfl⟩ : syracuseStep 6030773 = 565385) (by norm_num)
theorem B2680253 : Blo 1190412 2680253 := bbase (se 3 (by rfl) ⟨502547, by rfl⟩ : syracuseStep 2680253 = 1005095) (by norm_num)
theorem B1508797 : Blo 1190412 1508797 := bbase (se 3 (by rfl) ⟨282899, by rfl⟩ : syracuseStep 1508797 = 565799) (by norm_num)
theorem B6112709 : Blo 1190412 6112709 := bbase (se 4 (by rfl) ⟨573066, by rfl⟩ : syracuseStep 6112709 = 1146133) (by norm_num)
theorem B1787333 : Blo 1190412 1787333 := bbase (se 4 (by rfl) ⟨167562, by rfl⟩ : syracuseStep 1787333 = 335125) (by norm_num)
theorem B1787357 : Blo 1190412 1787357 := bbase (se 3 (by rfl) ⟨335129, by rfl⟩ : syracuseStep 1787357 = 670259) (by norm_num)
theorem B1787381 : Blo 1190412 1787381 := bbase (se 5 (by rfl) ⟨83783, by rfl⟩ : syracuseStep 1787381 = 167567) (by norm_num)
theorem B2680325 : Blo 1190412 2680325 := bbase (se 4 (by rfl) ⟨251280, by rfl⟩ : syracuseStep 2680325 = 502561) (by norm_num)
theorem B3393029 : Blo 1190412 3393029 := bbase (se 4 (by rfl) ⟨318096, by rfl⟩ : syracuseStep 3393029 = 636193) (by norm_num)
theorem B1271305 : Blo 1190412 1271305 := bbase (se 2 (by rfl) ⟨476739, by rfl⟩ : syracuseStep 1271305 = 953479) (by norm_num)
theorem B1787405 : Blo 1190412 1787405 := bbase (se 3 (by rfl) ⟨335138, by rfl⟩ : syracuseStep 1787405 = 670277) (by norm_num)
theorem B1787429 : Blo 1190412 1787429 := bbase (se 4 (by rfl) ⟨167571, by rfl⟩ : syracuseStep 1787429 = 335143) (by norm_num)
theorem B3016237 : Blo 1190412 3016237 := bbase (se 3 (by rfl) ⟨565544, by rfl⟩ : syracuseStep 3016237 = 1131089) (by norm_num)
theorem B1787453 : Blo 1190412 1787453 := bbase (se 3 (by rfl) ⟨335147, by rfl⟩ : syracuseStep 1787453 = 670295) (by norm_num)
theorem B1836605 : Blo 1190412 1836605 := bbase (se 3 (by rfl) ⟨344363, by rfl⟩ : syracuseStep 1836605 = 688727) (by norm_num)
theorem B2680397 : Blo 1190412 2680397 := bbase (se 3 (by rfl) ⟨502574, by rfl⟩ : syracuseStep 2680397 = 1005149) (by norm_num)
theorem B1787477 : Blo 1190412 1787477 := bbase (se 8 (by rfl) ⟨10473, by rfl⟩ : syracuseStep 1787477 = 20947) (by norm_num)
theorem B1836629 : Blo 1190412 1836629 := bbase (se 8 (by rfl) ⟨10761, by rfl⟩ : syracuseStep 1836629 = 21523) (by norm_num)
theorem B1508969 : Blo 1190412 1508969 := bbase (se 2 (by rfl) ⟨565863, by rfl⟩ : syracuseStep 1508969 = 1131727) (by norm_num)
theorem B1787501 : Blo 1190412 1787501 := bbase (se 3 (by rfl) ⟨335156, by rfl⟩ : syracuseStep 1787501 = 670313) (by norm_num)
theorem B1787525 : Blo 1190412 1787525 := bbase (se 4 (by rfl) ⟨167580, by rfl⟩ : syracuseStep 1787525 = 335161) (by norm_num)
theorem B2680469 : Blo 1190412 2680469 := bbase (se 6 (by rfl) ⟨62823, by rfl⟩ : syracuseStep 2680469 = 125647) (by norm_num)
theorem B3016349 : Blo 1190412 3016349 := bbase (se 3 (by rfl) ⟨565565, by rfl⟩ : syracuseStep 3016349 = 1131131) (by norm_num)
theorem B1787549 : Blo 1190412 1787549 := bbase (se 3 (by rfl) ⟨335165, by rfl⟩ : syracuseStep 1787549 = 670331) (by norm_num)
theorem B1509025 : Blo 1190412 1509025 := bbase (se 2 (by rfl) ⟨565884, by rfl⟩ : syracuseStep 1509025 = 1131769) (by norm_num)
theorem B1787573 : Blo 1190412 1787573 := bbase (se 5 (by rfl) ⟨83792, by rfl⟩ : syracuseStep 1787573 = 167585) (by norm_num)
theorem B2262725 : Blo 1190412 2262725 := bbase (se 4 (by rfl) ⟨212130, by rfl⟩ : syracuseStep 2262725 = 424261) (by norm_num)
theorem B1787597 : Blo 1190412 1787597 := bbase (se 3 (by rfl) ⟨335174, by rfl⟩ : syracuseStep 1787597 = 670349) (by norm_num)
theorem B3819221 : Blo 1190412 3819221 := bbase (se 7 (by rfl) ⟨44756, by rfl⟩ : syracuseStep 3819221 = 89513) (by norm_num)
theorem B2680541 : Blo 1190412 2680541 := bbase (se 3 (by rfl) ⟨502601, by rfl⟩ : syracuseStep 2680541 = 1005203) (by norm_num)
theorem B1787621 : Blo 1190412 1787621 := bbase (se 4 (by rfl) ⟨167589, by rfl⟩ : syracuseStep 1787621 = 335179) (by norm_num)
theorem B5089013 : Blo 1190412 5089013 := bbase (se 5 (by rfl) ⟨238547, by rfl⟩ : syracuseStep 5089013 = 477095) (by norm_num)
theorem B1787645 : Blo 1190412 1787645 := bbase (se 3 (by rfl) ⟨335183, by rfl⟩ : syracuseStep 1787645 = 670367) (by norm_num)
theorem B1509121 : Blo 1190412 1509121 := bbase (se 2 (by rfl) ⟨565920, by rfl⟩ : syracuseStep 1509121 = 1131841) (by norm_num)
theorem B4073237 : Blo 1190412 4073237 := bbase (se 6 (by rfl) ⟨95466, by rfl⟩ : syracuseStep 4073237 = 190933) (by norm_num)
theorem B1787669 : Blo 1190412 1787669 := bbase (se 6 (by rfl) ⟨41898, by rfl⟩ : syracuseStep 1787669 = 83797) (by norm_num)
theorem B2680613 : Blo 1190412 2680613 := bbase (se 4 (by rfl) ⟨251307, by rfl⟩ : syracuseStep 2680613 = 502615) (by norm_num)
theorem B1787693 : Blo 1190412 1787693 := bbase (se 3 (by rfl) ⟨335192, by rfl⟩ : syracuseStep 1787693 = 670385) (by norm_num)
theorem B2008901 : Blo 1190412 2008901 := bbase (se 4 (by rfl) ⟨188334, by rfl⟩ : syracuseStep 2008901 = 376669) (by norm_num)
theorem B1787717 : Blo 1190412 1787717 := bbase (se 4 (by rfl) ⟨167598, by rfl⟩ : syracuseStep 1787717 = 335197) (by norm_num)
theorem B4024133 : Blo 1190412 4024133 := bbase (se 4 (by rfl) ⟨377262, by rfl⟩ : syracuseStep 4024133 = 754525) (by norm_num)
theorem B3016541 : Blo 1190412 3016541 := bbase (se 3 (by rfl) ⟨565601, by rfl⟩ : syracuseStep 3016541 = 1131203) (by norm_num)
theorem B1787741 : Blo 1190412 1787741 := bbase (se 3 (by rfl) ⟨335201, by rfl⟩ : syracuseStep 1787741 = 670403) (by norm_num)
theorem B2680685 : Blo 1190412 2680685 := bbase (se 3 (by rfl) ⟨502628, by rfl⟩ : syracuseStep 2680685 = 1005257) (by norm_num)
theorem B1787765 : Blo 1190412 1787765 := bbase (se 5 (by rfl) ⟨83801, by rfl⟩ : syracuseStep 1787765 = 167603) (by norm_num)
theorem B1812341 : Blo 1190412 1812341 := bbase (se 5 (by rfl) ⟨84953, by rfl⟩ : syracuseStep 1812341 = 169907) (by norm_num)
theorem B1787789 : Blo 1190412 1787789 := bbase (se 3 (by rfl) ⟨335210, by rfl⟩ : syracuseStep 1787789 = 670421) (by norm_num)
theorem B4532117 : Blo 1190412 4532117 := bbase (se 6 (by rfl) ⟨106221, by rfl⟩ : syracuseStep 4532117 = 212443) (by norm_num)
theorem B3819413 : Blo 1190412 3819413 := bbase (se 6 (by rfl) ⟨89517, by rfl⟩ : syracuseStep 3819413 = 179035) (by norm_num)
theorem B1787813 : Blo 1190412 1787813 := bbase (se 4 (by rfl) ⟨167607, by rfl⟩ : syracuseStep 1787813 = 335215) (by norm_num)
theorem B9168821 : Blo 1190412 9168821 := bbase (se 5 (by rfl) ⟨429788, by rfl⟩ : syracuseStep 9168821 = 859577) (by norm_num)
theorem B2680757 : Blo 1190412 2680757 := bbase (se 5 (by rfl) ⟨125660, by rfl⟩ : syracuseStep 2680757 = 251321) (by norm_num)
theorem B1271737 : Blo 1190412 1271737 := bbase (se 2 (by rfl) ⟨476901, by rfl⟩ : syracuseStep 1271737 = 953803) (by norm_num)
theorem B1787837 : Blo 1190412 1787837 := bbase (se 3 (by rfl) ⟨335219, by rfl⟩ : syracuseStep 1787837 = 670439) (by norm_num)
theorem B2009029 : Blo 1190412 2009029 := bbase (se 4 (by rfl) ⟨188346, by rfl⟩ : syracuseStep 2009029 = 376693) (by norm_num)
theorem B1787861 : Blo 1190412 1787861 := bbase (se 7 (by rfl) ⟨20951, by rfl⟩ : syracuseStep 1787861 = 41903) (by norm_num)
theorem B1787885 : Blo 1190412 1787885 := bbase (se 3 (by rfl) ⟨335228, by rfl⟩ : syracuseStep 1787885 = 670457) (by norm_num)
theorem B1697773 : Blo 1190412 1697773 := bbase (se 3 (by rfl) ⟨318332, by rfl⟩ : syracuseStep 1697773 = 636665) (by norm_num)
theorem B2680829 : Blo 1190412 2680829 := bbase (se 3 (by rfl) ⟨502655, by rfl⟩ : syracuseStep 2680829 = 1005311) (by norm_num)
theorem B1271809 : Blo 1190412 1271809 := bbase (se 2 (by rfl) ⟨476928, by rfl⟩ : syracuseStep 1271809 = 953857) (by norm_num)
theorem B1787909 : Blo 1190412 1787909 := bbase (se 4 (by rfl) ⟨167616, by rfl⟩ : syracuseStep 1787909 = 335233) (by norm_num)
theorem B2009117 : Blo 1190412 2009117 := bbase (se 3 (by rfl) ⟨376709, by rfl⟩ : syracuseStep 2009117 = 753419) (by norm_num)
theorem B1787933 : Blo 1190412 1787933 := bbase (se 3 (by rfl) ⟨335237, by rfl⟩ : syracuseStep 1787933 = 670475) (by norm_num)
theorem B1787957 : Blo 1190412 1787957 := bbase (se 5 (by rfl) ⟨83810, by rfl⟩ : syracuseStep 1787957 = 167621) (by norm_num)
theorem B2680901 : Blo 1190412 2680901 := bbase (se 4 (by rfl) ⟨251334, by rfl⟩ : syracuseStep 2680901 = 502669) (by norm_num)
theorem B1787981 : Blo 1190412 1787981 := bbase (se 3 (by rfl) ⟨335246, by rfl⟩ : syracuseStep 1787981 = 670493) (by norm_num)
theorem B1788005 : Blo 1190412 1788005 := bbase (se 4 (by rfl) ⟨167625, by rfl⟩ : syracuseStep 1788005 = 335251) (by norm_num)
theorem B1788029 : Blo 1190412 1788029 := bbase (se 3 (by rfl) ⟨335255, by rfl⟩ : syracuseStep 1788029 = 670511) (by norm_num)
theorem B2680973 : Blo 1190412 2680973 := bbase (se 3 (by rfl) ⟨502682, by rfl⟩ : syracuseStep 2680973 = 1005365) (by norm_num)
theorem B1788053 : Blo 1190412 1788053 := bbase (se 6 (by rfl) ⟨41907, by rfl⟩ : syracuseStep 1788053 = 83815) (by norm_num)
theorem B2009245 : Blo 1190412 2009245 := bbase (se 3 (by rfl) ⟨376733, by rfl⟩ : syracuseStep 2009245 = 753467) (by norm_num)
theorem B3393701 : Blo 1190412 3393701 := bbase (se 4 (by rfl) ⟨318159, by rfl⟩ : syracuseStep 3393701 = 636319) (by norm_num)
theorem B1788077 : Blo 1190412 1788077 := bbase (se 3 (by rfl) ⟨335264, by rfl⟩ : syracuseStep 1788077 = 670529) (by norm_num)
theorem B3016885 : Blo 1190412 3016885 := bbase (se 5 (by rfl) ⟨141416, by rfl⟩ : syracuseStep 3016885 = 282833) (by norm_num)
theorem B1788101 : Blo 1190412 1788101 := bbase (se 4 (by rfl) ⟨167634, by rfl⟩ : syracuseStep 1788101 = 335269) (by norm_num)
theorem B3623125 : Blo 1190412 3623125 := bbase (se 7 (by rfl) ⟨42458, by rfl⟩ : syracuseStep 3623125 = 84917) (by norm_num)
theorem B2681045 : Blo 1190412 2681045 := bbase (se 7 (by rfl) ⟨31418, by rfl⟩ : syracuseStep 2681045 = 62837) (by norm_num)
theorem B1788125 : Blo 1190412 1788125 := bbase (se 3 (by rfl) ⟨335273, by rfl⟩ : syracuseStep 1788125 = 670547) (by norm_num)
theorem B2009333 : Blo 1190412 2009333 := bbase (se 5 (by rfl) ⟨94187, by rfl⟩ : syracuseStep 2009333 = 188375) (by norm_num)
theorem B1788149 : Blo 1190412 1788149 := bbase (se 5 (by rfl) ⟨83819, by rfl⟩ : syracuseStep 1788149 = 167639) (by norm_num)
theorem B1788173 : Blo 1190412 1788173 := bbase (se 3 (by rfl) ⟨335282, by rfl⟩ : syracuseStep 1788173 = 670565) (by norm_num)
theorem B2681117 : Blo 1190412 2681117 := bbase (se 3 (by rfl) ⟨502709, by rfl⟩ : syracuseStep 2681117 = 1005419) (by norm_num)
theorem B3016997 : Blo 1190412 3016997 := bbase (se 4 (by rfl) ⟨282843, by rfl⟩ : syracuseStep 3016997 = 565687) (by norm_num)
theorem B1788197 : Blo 1190412 1788197 := bbase (se 4 (by rfl) ⟨167643, by rfl⟩ : syracuseStep 1788197 = 335287) (by norm_num)
theorem B1788221 : Blo 1190412 1788221 := bbase (se 3 (by rfl) ⟨335291, by rfl⟩ : syracuseStep 1788221 = 670583) (by norm_num)
theorem B1788245 : Blo 1190412 1788245 := bbase (se 10 (by rfl) ⟨2619, by rfl⟩ : syracuseStep 1788245 = 5239) (by norm_num)
theorem B2681189 : Blo 1190412 2681189 := bbase (se 4 (by rfl) ⟨251361, by rfl⟩ : syracuseStep 2681189 = 502723) (by norm_num)
theorem B1788269 : Blo 1190412 1788269 := bbase (se 3 (by rfl) ⟨335300, by rfl⟩ : syracuseStep 1788269 = 670601) (by norm_num)
theorem B2009461 : Blo 1190412 2009461 := bbase (se 5 (by rfl) ⟨94193, by rfl⟩ : syracuseStep 2009461 = 188387) (by norm_num)
theorem B1272181 : Blo 1190412 1272181 := bbase (se 5 (by rfl) ⟨59633, by rfl⟩ : syracuseStep 1272181 = 119267) (by norm_num)
theorem B2902397 : Blo 1190412 2902397 := bbase (se 3 (by rfl) ⟨544199, by rfl⟩ : syracuseStep 2902397 = 1088399) (by norm_num)
theorem B1788293 : Blo 1190412 1788293 := bbase (se 4 (by rfl) ⟨167652, by rfl⟩ : syracuseStep 1788293 = 335305) (by norm_num)
theorem B1788317 : Blo 1190412 1788317 := bbase (se 3 (by rfl) ⟨335309, by rfl⟩ : syracuseStep 1788317 = 670619) (by norm_num)
theorem B2681261 : Blo 1190412 2681261 := bbase (se 3 (by rfl) ⟨502736, by rfl⟩ : syracuseStep 2681261 = 1005473) (by norm_num)
theorem B1788341 : Blo 1190412 1788341 := bbase (se 5 (by rfl) ⟨83828, by rfl⟩ : syracuseStep 1788341 = 167657) (by norm_num)
theorem B2263477 : Blo 1190412 2263477 := bbase (se 5 (by rfl) ⟨106100, by rfl⟩ : syracuseStep 2263477 = 212201) (by norm_num)
theorem B2009549 : Blo 1190412 2009549 := bbase (se 3 (by rfl) ⟨376790, by rfl⟩ : syracuseStep 2009549 = 753581) (by norm_num)
theorem B1788365 : Blo 1190412 1788365 := bbase (se 3 (by rfl) ⟨335318, by rfl⟩ : syracuseStep 1788365 = 670637) (by norm_num)
theorem B2615765 : Blo 1190412 2615765 := bbase (se 7 (by rfl) ⟨30653, by rfl⟩ : syracuseStep 2615765 = 61307) (by norm_num)
theorem B3017189 : Blo 1190412 3017189 := bbase (se 4 (by rfl) ⟨282861, by rfl⟩ : syracuseStep 3017189 = 565723) (by norm_num)
theorem B1788389 : Blo 1190412 1788389 := bbase (se 4 (by rfl) ⟨167661, by rfl⟩ : syracuseStep 1788389 = 335323) (by norm_num)
theorem B2681333 : Blo 1190412 2681333 := bbase (se 5 (by rfl) ⟨125687, by rfl⟩ : syracuseStep 2681333 = 251375) (by norm_num)
theorem B1788413 : Blo 1190412 1788413 := bbase (se 3 (by rfl) ⟨335327, by rfl⟩ : syracuseStep 1788413 = 670655) (by norm_num)
theorem B1788437 : Blo 1190412 1788437 := bbase (se 6 (by rfl) ⟨41916, by rfl⟩ : syracuseStep 1788437 = 83833) (by norm_num)
theorem B1788461 : Blo 1190412 1788461 := bbase (se 3 (by rfl) ⟨335336, by rfl⟩ : syracuseStep 1788461 = 670673) (by norm_num)
theorem B2681405 : Blo 1190412 2681405 := bbase (se 3 (by rfl) ⟨502763, by rfl⟩ : syracuseStep 2681405 = 1005527) (by norm_num)
theorem B1788485 : Blo 1190412 1788485 := bbase (se 4 (by rfl) ⟨167670, by rfl⟩ : syracuseStep 1788485 = 335341) (by norm_num)
theorem B2263621 : Blo 1190412 2263621 := bbase (se 4 (by rfl) ⟨212214, by rfl⟩ : syracuseStep 2263621 = 424429) (by norm_num)
theorem B2009677 : Blo 1190412 2009677 := bbase (se 3 (by rfl) ⟨376814, by rfl⟩ : syracuseStep 2009677 = 753629) (by norm_num)
theorem B3394133 : Blo 1190412 3394133 := bbase (se 8 (by rfl) ⟨19887, by rfl⟩ : syracuseStep 3394133 = 39775) (by norm_num)
theorem B1788509 : Blo 1190412 1788509 := bbase (se 3 (by rfl) ⟨335345, by rfl⟩ : syracuseStep 1788509 = 670691) (by norm_num)
theorem B3623525 : Blo 1190412 3623525 := bbase (se 4 (by rfl) ⟨339705, by rfl⟩ : syracuseStep 3623525 = 679411) (by norm_num)
theorem B1206901 : Blo 1190412 1206901 := bbase (se 5 (by rfl) ⟨56573, by rfl⟩ : syracuseStep 1206901 = 113147) (by norm_num)
theorem B1788533 : Blo 1190412 1788533 := bbase (se 5 (by rfl) ⟨83837, by rfl⟩ : syracuseStep 1788533 = 167675) (by norm_num)
theorem B2681477 : Blo 1190412 2681477 := bbase (se 4 (by rfl) ⟨251388, by rfl⟩ : syracuseStep 2681477 = 502777) (by norm_num)
theorem B1788557 : Blo 1190412 1788557 := bbase (se 3 (by rfl) ⟨335354, by rfl⟩ : syracuseStep 1788557 = 670709) (by norm_num)
theorem B2009765 : Blo 1190412 2009765 := bbase (se 4 (by rfl) ⟨188415, by rfl⟩ : syracuseStep 2009765 = 376831) (by norm_num)
theorem B1788581 : Blo 1190412 1788581 := bbase (se 4 (by rfl) ⟨167679, by rfl⟩ : syracuseStep 1788581 = 335359) (by norm_num)
theorem B1788605 : Blo 1190412 1788605 := bbase (se 3 (by rfl) ⟨335363, by rfl⟩ : syracuseStep 1788605 = 670727) (by norm_num)
theorem B6032069 : Blo 1190412 6032069 := bbase (se 4 (by rfl) ⟨565506, by rfl⟩ : syracuseStep 6032069 = 1131013) (by norm_num)
theorem B2681549 : Blo 1190412 2681549 := bbase (se 3 (by rfl) ⟨502790, by rfl⟩ : syracuseStep 2681549 = 1005581) (by norm_num)
theorem B1272557 : Blo 1190412 1272557 := bbase (se 3 (by rfl) ⟨238604, by rfl⟩ : syracuseStep 1272557 = 477209) (by norm_num)
theorem B6875893 : Blo 1190412 6875893 := bbase (se 5 (by rfl) ⟨322307, by rfl⟩ : syracuseStep 6875893 = 644615) (by norm_num)
theorem B2861821 : Blo 1190412 2861821 := bbase (se 3 (by rfl) ⟨536591, by rfl⟩ : syracuseStep 2861821 = 1073183) (by norm_num)
theorem B2681621 : Blo 1190412 2681621 := bbase (se 6 (by rfl) ⟨62850, by rfl⟩ : syracuseStep 2681621 = 125701) (by norm_num)
theorem B2009893 : Blo 1190412 2009893 := bbase (se 4 (by rfl) ⟨188427, by rfl⟩ : syracuseStep 2009893 = 376855) (by norm_num)
theorem B1272629 : Blo 1190412 1272629 := bbase (se 5 (by rfl) ⟨59654, by rfl⟩ : syracuseStep 1272629 = 119309) (by norm_num)
theorem B3017533 : Blo 1190412 3017533 := bbase (se 3 (by rfl) ⟨565787, by rfl⟩ : syracuseStep 3017533 = 1131575) (by norm_num)
theorem B2681693 : Blo 1190412 2681693 := bbase (se 3 (by rfl) ⟨502817, by rfl⟩ : syracuseStep 2681693 = 1005635) (by norm_num)
theorem B2009981 : Blo 1190412 2009981 := bbase (se 3 (by rfl) ⟨376871, by rfl⟩ : syracuseStep 2009981 = 753743) (by norm_num)
theorem B1207189 : Blo 1190412 1207189 := bbase (se 6 (by rfl) ⟨28293, by rfl⟩ : syracuseStep 1207189 = 56587) (by norm_num)
theorem B2681765 : Blo 1190412 2681765 := bbase (se 4 (by rfl) ⟨251415, by rfl⟩ : syracuseStep 2681765 = 502831) (by norm_num)
theorem B3017645 : Blo 1190412 3017645 := bbase (se 3 (by rfl) ⟨565808, by rfl⟩ : syracuseStep 3017645 = 1131617) (by norm_num)
theorem B2681837 : Blo 1190412 2681837 := bbase (se 3 (by rfl) ⟨502844, by rfl⟩ : syracuseStep 2681837 = 1005689) (by norm_num)
theorem B1272817 : Blo 1190412 1272817 := bbase (se 2 (by rfl) ⟨477306, by rfl⟩ : syracuseStep 1272817 = 954613) (by norm_num)
theorem B2010109 : Blo 1190412 2010109 := bbase (se 3 (by rfl) ⟨376895, by rfl⟩ : syracuseStep 2010109 = 753791) (by norm_num)
theorem B10185749 : Blo 1190412 10185749 := bbase (se 6 (by rfl) ⟨238728, by rfl⟩ : syracuseStep 10185749 = 477457) (by norm_num)
theorem B2681909 : Blo 1190412 2681909 := bbase (se 5 (by rfl) ⟨125714, by rfl⟩ : syracuseStep 2681909 = 251429) (by norm_num)
theorem B2010197 : Blo 1190412 2010197 := bbase (se 8 (by rfl) ⟨11778, by rfl⟩ : syracuseStep 2010197 = 23557) (by norm_num)
theorem B3017837 : Blo 1190412 3017837 := bbase (se 3 (by rfl) ⟨565844, by rfl⟩ : syracuseStep 3017837 = 1131689) (by norm_num)
theorem B2681981 : Blo 1190412 2681981 := bbase (se 3 (by rfl) ⟨502871, by rfl⟩ : syracuseStep 2681981 = 1005743) (by norm_num)
theorem B1273001 : Blo 1190412 1273001 := bbase (se 2 (by rfl) ⟨477375, by rfl⟩ : syracuseStep 1273001 = 954751) (by norm_num)
theorem B4525253 : Blo 1190412 4525253 := bbase (se 4 (by rfl) ⟨424242, by rfl⟩ : syracuseStep 4525253 = 848485) (by norm_num)
theorem B2682053 : Blo 1190412 2682053 := bbase (se 4 (by rfl) ⟨251442, by rfl⟩ : syracuseStep 2682053 = 502885) (by norm_num)
theorem B2010325 : Blo 1190412 2010325 := bbase (se 7 (by rfl) ⟨23558, by rfl⟩ : syracuseStep 2010325 = 47117) (by norm_num)
theorem B3058901 : Blo 1190412 3058901 := bbase (se 7 (by rfl) ⟨35846, by rfl⟩ : syracuseStep 3058901 = 71693) (by norm_num)
theorem B2682125 : Blo 1190412 2682125 := bbase (se 3 (by rfl) ⟨502898, by rfl⟩ : syracuseStep 2682125 = 1005797) (by norm_num)
theorem B2010413 : Blo 1190412 2010413 := bbase (se 3 (by rfl) ⟨376952, by rfl⟩ : syracuseStep 2010413 = 753905) (by norm_num)
theorem B1224001 : Blo 1190412 1224001 := bbase (se 2 (by rfl) ⟨459000, by rfl⟩ : syracuseStep 1224001 = 918001) (by norm_num)
theorem B3394885 : Blo 1190412 3394885 := bbase (se 4 (by rfl) ⟨318270, by rfl⟩ : syracuseStep 3394885 = 636541) (by norm_num)
theorem B2682197 : Blo 1190412 2682197 := bbase (se 11 (by rfl) ⟨1964, by rfl⟩ : syracuseStep 2682197 = 3929) (by norm_num)
theorem B2682269 : Blo 1190412 2682269 := bbase (se 3 (by rfl) ⟨502925, by rfl⟩ : syracuseStep 2682269 = 1005851) (by norm_num)
theorem B2010541 : Blo 1190412 2010541 := bbase (se 3 (by rfl) ⟨376976, by rfl⟩ : syracuseStep 2010541 = 753953) (by norm_num)
theorem B2862533 : Blo 1190412 2862533 := bbase (se 4 (by rfl) ⟨268362, by rfl⟩ : syracuseStep 2862533 = 536725) (by norm_num)
theorem B3018181 : Blo 1190412 3018181 := bbase (se 4 (by rfl) ⟨282954, by rfl⟩ : syracuseStep 3018181 = 565909) (by norm_num)
theorem B4296149 : Blo 1190412 4296149 := bbase (se 7 (by rfl) ⟨50345, by rfl⟩ : syracuseStep 4296149 = 100691) (by norm_num)
theorem B5090789 : Blo 1190412 5090789 := bbase (se 4 (by rfl) ⟨477261, by rfl⟩ : syracuseStep 5090789 = 954523) (by norm_num)
theorem B4525541 : Blo 1190412 4525541 := bbase (se 4 (by rfl) ⟨424269, by rfl⟩ : syracuseStep 4525541 = 848539) (by norm_num)
theorem B2682341 : Blo 1190412 2682341 := bbase (se 4 (by rfl) ⟨251469, by rfl⟩ : syracuseStep 2682341 = 502939) (by norm_num)
theorem B4017653 : Blo 1190412 4017653 := bbase (se 5 (by rfl) ⟨188327, by rfl⟩ : syracuseStep 4017653 = 376655) (by norm_num)
theorem B2010629 : Blo 1190412 2010629 := bbase (se 4 (by rfl) ⟨188496, by rfl⟩ : syracuseStep 2010629 = 376993) (by norm_num)
theorem B2682413 : Blo 1190412 2682413 := bbase (se 3 (by rfl) ⟨502952, by rfl⟩ : syracuseStep 2682413 = 1005905) (by norm_num)
theorem B3018293 : Blo 1190412 3018293 := bbase (se 5 (by rfl) ⟨141482, by rfl⟩ : syracuseStep 3018293 = 282965) (by norm_num)
theorem B2682485 : Blo 1190412 2682485 := bbase (se 5 (by rfl) ⟨125741, by rfl⟩ : syracuseStep 2682485 = 251483) (by norm_num)
theorem B2010757 : Blo 1190412 2010757 := bbase (se 4 (by rfl) ⟨188508, by rfl⟩ : syracuseStep 2010757 = 377017) (by norm_num)
theorem B2682557 : Blo 1190412 2682557 := bbase (se 3 (by rfl) ⟨502979, by rfl⟩ : syracuseStep 2682557 = 1005959) (by norm_num)
theorem B2010845 : Blo 1190412 2010845 := bbase (se 3 (by rfl) ⟨377033, by rfl⟩ : syracuseStep 2010845 = 754067) (by norm_num)
theorem B2682629 : Blo 1190412 2682629 := bbase (se 4 (by rfl) ⟨251496, by rfl⟩ : syracuseStep 2682629 = 502993) (by norm_num)
theorem B2543413 : Blo 1190412 2543413 := bbase (se 5 (by rfl) ⟨119222, by rfl⟩ : syracuseStep 2543413 = 238445) (by norm_num)
theorem B9047861 : Blo 1190412 9047861 := bbase (se 5 (by rfl) ⟨424118, by rfl⟩ : syracuseStep 9047861 = 848237) (by norm_num)
theorem B2862917 : Blo 1190412 2862917 := bbase (se 4 (by rfl) ⟨268398, by rfl⟩ : syracuseStep 2862917 = 536797) (by norm_num)
theorem B2682701 : Blo 1190412 2682701 := bbase (se 3 (by rfl) ⟨503006, by rfl⟩ : syracuseStep 2682701 = 1006013) (by norm_num)
theorem B2010973 : Blo 1190412 2010973 := bbase (se 3 (by rfl) ⟨377057, by rfl⟩ : syracuseStep 2010973 = 754115) (by norm_num)
theorem B1339249 : Blo 1190412 1339249 := bbase (se 2 (by rfl) ⟨502218, by rfl⟩ : syracuseStep 1339249 = 1004437) (by norm_num)
theorem B2322317 : Blo 1190412 2322317 := bbase (se 3 (by rfl) ⟨435434, by rfl⟩ : syracuseStep 2322317 = 870869) (by norm_num)
theorem B1339285 : Blo 1190412 1339285 := bbase (se 6 (by rfl) ⟨31389, by rfl⟩ : syracuseStep 1339285 = 62779) (by norm_num)
theorem B2682773 : Blo 1190412 2682773 := bbase (se 6 (by rfl) ⟨62877, by rfl⟩ : syracuseStep 2682773 = 125755) (by norm_num)
theorem B4018085 : Blo 1190412 4018085 := bbase (se 4 (by rfl) ⟨376695, by rfl⟩ : syracuseStep 4018085 = 753391) (by norm_num)
theorem B2011061 : Blo 1190412 2011061 := bbase (se 5 (by rfl) ⟨94268, by rfl⟩ : syracuseStep 2011061 = 188537) (by norm_num)
theorem B1339321 : Blo 1190412 1339321 := bbase (se 2 (by rfl) ⟨502245, by rfl⟩ : syracuseStep 1339321 = 1004491) (by norm_num)
theorem B6033365 : Blo 1190412 6033365 := bbase (se 7 (by rfl) ⟨70703, by rfl⟩ : syracuseStep 6033365 = 141407) (by norm_num)
theorem B1339357 : Blo 1190412 1339357 := bbase (se 3 (by rfl) ⟨251129, by rfl⟩ : syracuseStep 1339357 = 502259) (by norm_num)
theorem B2682845 : Blo 1190412 2682845 := bbase (se 3 (by rfl) ⟨503033, by rfl⟩ : syracuseStep 2682845 = 1006067) (by norm_num)
theorem B1339393 : Blo 1190412 1339393 := bbase (se 2 (by rfl) ⟨502272, by rfl⟩ : syracuseStep 1339393 = 1004545) (by norm_num)
theorem B1339429 : Blo 1190412 1339429 := bbase (se 4 (by rfl) ⟨125571, by rfl⟩ : syracuseStep 1339429 = 251143) (by norm_num)
theorem B2682917 : Blo 1190412 2682917 := bbase (se 4 (by rfl) ⟨251523, by rfl⟩ : syracuseStep 2682917 = 503047) (by norm_num)
theorem B1208369 : Blo 1190412 1208369 := bbase (se 2 (by rfl) ⟨453138, by rfl⟩ : syracuseStep 1208369 = 906277) (by norm_num)
theorem B2011189 : Blo 1190412 2011189 := bbase (se 5 (by rfl) ⟨94274, by rfl⟩ : syracuseStep 2011189 = 188549) (by norm_num)
theorem B1339465 : Blo 1190412 1339465 := bbase (se 2 (by rfl) ⟨502299, by rfl⟩ : syracuseStep 1339465 = 1004599) (by norm_num)
theorem B2863205 : Blo 1190412 2863205 := bbase (se 4 (by rfl) ⟨268425, by rfl⟩ : syracuseStep 2863205 = 536851) (by norm_num)
theorem B1339501 : Blo 1190412 1339501 := bbase (se 3 (by rfl) ⟨251156, by rfl⟩ : syracuseStep 1339501 = 502313) (by norm_num)
theorem B2011277 : Blo 1190412 2011277 := bbase (se 3 (by rfl) ⟨377114, by rfl⟩ : syracuseStep 2011277 = 754229) (by norm_num)
theorem B1339537 : Blo 1190412 1339537 := bbase (se 2 (by rfl) ⟨502326, by rfl⟩ : syracuseStep 1339537 = 1004653) (by norm_num)
theorem B1241233 : Blo 1190412 1241233 := bbase (se 2 (by rfl) ⟨465462, by rfl⟩ : syracuseStep 1241233 = 930925) (by norm_num)
theorem B1339573 : Blo 1190412 1339573 := bbase (se 5 (by rfl) ⟨62792, by rfl⟩ : syracuseStep 1339573 = 125585) (by norm_num)
theorem B9040085 : Blo 1190412 9040085 := bbase (se 7 (by rfl) ⟨105938, by rfl⟩ : syracuseStep 9040085 = 211877) (by norm_num)
theorem B1339609 : Blo 1190412 1339609 := bbase (se 2 (by rfl) ⟨502353, by rfl⟩ : syracuseStep 1339609 = 1004707) (by norm_num)
theorem B3870965 : Blo 1190412 3870965 := bbase (se 5 (by rfl) ⟨181451, by rfl⟩ : syracuseStep 3870965 = 362903) (by norm_num)
theorem B1339645 : Blo 1190412 1339645 := bbase (se 3 (by rfl) ⟨251183, by rfl⟩ : syracuseStep 1339645 = 502367) (by norm_num)
theorem B2011405 : Blo 1190412 2011405 := bbase (se 3 (by rfl) ⟨377138, by rfl⟩ : syracuseStep 2011405 = 754277) (by norm_num)
theorem B1339681 : Blo 1190412 1339681 := bbase (se 2 (by rfl) ⟨502380, by rfl⟩ : syracuseStep 1339681 = 1004761) (by norm_num)
theorem B1339717 : Blo 1190412 1339717 := bbase (se 4 (by rfl) ⟨125598, by rfl⟩ : syracuseStep 1339717 = 251197) (by norm_num)
theorem B1528141 : Blo 1190412 1528141 := bbase (se 3 (by rfl) ⟨286526, by rfl⟩ : syracuseStep 1528141 = 573053) (by norm_num)
theorem B4018517 : Blo 1190412 4018517 := bbase (se 10 (by rfl) ⟨5886, by rfl⟩ : syracuseStep 4018517 = 11773) (by norm_num)
theorem B2011493 : Blo 1190412 2011493 := bbase (se 4 (by rfl) ⟨188577, by rfl⟩ : syracuseStep 2011493 = 377155) (by norm_num)
theorem B1339753 : Blo 1190412 1339753 := bbase (se 2 (by rfl) ⟨502407, by rfl⟩ : syracuseStep 1339753 = 1004815) (by norm_num)
theorem B1339789 : Blo 1190412 1339789 := bbase (se 3 (by rfl) ⟨251210, by rfl⟩ : syracuseStep 1339789 = 502421) (by norm_num)
theorem B1339825 : Blo 1190412 1339825 := bbase (se 2 (by rfl) ⟨502434, by rfl⟩ : syracuseStep 1339825 = 1004869) (by norm_num)
theorem B5091781 : Blo 1190412 5091781 := bbase (se 4 (by rfl) ⟨477354, by rfl⟩ : syracuseStep 5091781 = 954709) (by norm_num)
theorem B1339861 : Blo 1190412 1339861 := bbase (se 7 (by rfl) ⟨15701, by rfl⟩ : syracuseStep 1339861 = 31403) (by norm_num)
theorem B2011621 : Blo 1190412 2011621 := bbase (se 4 (by rfl) ⟨188589, by rfl⟩ : syracuseStep 2011621 = 377179) (by norm_num)
theorem B1339897 : Blo 1190412 1339897 := bbase (se 2 (by rfl) ⟨502461, by rfl⟩ : syracuseStep 1339897 = 1004923) (by norm_num)
theorem B1339933 : Blo 1190412 1339933 := bbase (se 3 (by rfl) ⟨251237, by rfl⟩ : syracuseStep 1339933 = 502475) (by norm_num)
theorem B3813941 : Blo 1190412 3813941 := bbase (se 5 (by rfl) ⟨178778, by rfl⟩ : syracuseStep 3813941 = 357557) (by norm_num)
theorem B2011709 : Blo 1190412 2011709 := bbase (se 3 (by rfl) ⟨377195, by rfl⟩ : syracuseStep 2011709 = 754391) (by norm_num)
theorem B1339969 : Blo 1190412 1339969 := bbase (se 2 (by rfl) ⟨502488, by rfl⟩ : syracuseStep 1339969 = 1004977) (by norm_num)
theorem B1340005 : Blo 1190412 1340005 := bbase (se 4 (by rfl) ⟨125625, by rfl⟩ : syracuseStep 1340005 = 251251) (by norm_num)
theorem B5722757 : Blo 1190412 5722757 := bbase (se 4 (by rfl) ⟨536508, by rfl⟩ : syracuseStep 5722757 = 1073017) (by norm_num)
theorem B4526725 : Blo 1190412 4526725 := bbase (se 4 (by rfl) ⟨424380, by rfl⟩ : syracuseStep 4526725 = 848761) (by norm_num)
theorem B1340041 : Blo 1190412 1340041 := bbase (se 2 (by rfl) ⟨502515, by rfl⟩ : syracuseStep 1340041 = 1005031) (by norm_num)
theorem B1340077 : Blo 1190412 1340077 := bbase (se 3 (by rfl) ⟨251264, by rfl⟩ : syracuseStep 1340077 = 502529) (by norm_num)
theorem B2544301 : Blo 1190412 2544301 := bbase (se 3 (by rfl) ⟨477056, by rfl⟩ : syracuseStep 2544301 = 954113) (by norm_num)
theorem B2011837 : Blo 1190412 2011837 := bbase (se 3 (by rfl) ⟨377219, by rfl⟩ : syracuseStep 2011837 = 754439) (by norm_num)
theorem B1340113 : Blo 1190412 1340113 := bbase (se 2 (by rfl) ⟨502542, by rfl⟩ : syracuseStep 1340113 = 1005085) (by norm_num)
theorem B10867445 : Blo 1190412 10867445 := bbase (se 5 (by rfl) ⟨509411, by rfl⟩ : syracuseStep 10867445 = 1018823) (by norm_num)
theorem B1340149 : Blo 1190412 1340149 := bbase (se 5 (by rfl) ⟨62819, by rfl⟩ : syracuseStep 1340149 = 125639) (by norm_num)
theorem B4018949 : Blo 1190412 4018949 := bbase (se 4 (by rfl) ⟨376776, by rfl⟩ : syracuseStep 4018949 = 753553) (by norm_num)
theorem B1430281 : Blo 1190412 1430281 := bbase (se 2 (by rfl) ⟨536355, by rfl⟩ : syracuseStep 1430281 = 1072711) (by norm_num)
theorem B21721877 : Blo 1190412 21721877 := bbase (se 6 (by rfl) ⟨509106, by rfl⟩ : syracuseStep 21721877 = 1018213) (by norm_num)
theorem B2011925 : Blo 1190412 2011925 := bbase (se 6 (by rfl) ⟨47154, by rfl⟩ : syracuseStep 2011925 = 94309) (by norm_num)
theorem B1340185 : Blo 1190412 1340185 := bbase (se 2 (by rfl) ⟨502569, by rfl⟩ : syracuseStep 1340185 = 1005139) (by norm_num)
theorem B2716469 : Blo 1190412 2716469 := bbase (se 5 (by rfl) ⟨127334, by rfl⟩ : syracuseStep 2716469 = 254669) (by norm_num)
theorem B1528633 : Blo 1190412 1528633 := bbase (se 2 (by rfl) ⟨573237, by rfl⟩ : syracuseStep 1528633 = 1146475) (by norm_num)
theorem B1340221 : Blo 1190412 1340221 := bbase (se 3 (by rfl) ⟨251291, by rfl⟩ : syracuseStep 1340221 = 502583) (by norm_num)
theorem B1340257 : Blo 1190412 1340257 := bbase (se 2 (by rfl) ⟨502596, by rfl⟩ : syracuseStep 1340257 = 1005193) (by norm_num)
theorem B2577277 : Blo 1190412 2577277 := bbase (se 3 (by rfl) ⟨483239, by rfl⟩ : syracuseStep 2577277 = 966479) (by norm_num)
theorem B2036605 : Blo 1190412 2036605 := bbase (se 3 (by rfl) ⟨381863, by rfl⟩ : syracuseStep 2036605 = 763727) (by norm_num)
theorem B1340293 : Blo 1190412 1340293 := bbase (se 4 (by rfl) ⟨125652, by rfl⟩ : syracuseStep 1340293 = 251305) (by norm_num)
theorem B2012053 : Blo 1190412 2012053 := bbase (se 6 (by rfl) ⟨47157, by rfl⟩ : syracuseStep 2012053 = 94315) (by norm_num)
theorem B1340329 : Blo 1190412 1340329 := bbase (se 2 (by rfl) ⟨502623, by rfl⟩ : syracuseStep 1340329 = 1005247) (by norm_num)
theorem B4527029 : Blo 1190412 4527029 := bbase (se 5 (by rfl) ⟨212204, by rfl⟩ : syracuseStep 4527029 = 424409) (by norm_num)
theorem B1340365 : Blo 1190412 1340365 := bbase (se 3 (by rfl) ⟨251318, by rfl⟩ : syracuseStep 1340365 = 502637) (by norm_num)
theorem B6779861 : Blo 1190412 6779861 := bbase (se 7 (by rfl) ⟨79451, by rfl⟩ : syracuseStep 6779861 = 158903) (by norm_num)
theorem B2036701 : Blo 1190412 2036701 := bbase (se 3 (by rfl) ⟨381881, by rfl⟩ : syracuseStep 2036701 = 763763) (by norm_num)
theorem B2012141 : Blo 1190412 2012141 := bbase (se 3 (by rfl) ⟨377276, by rfl⟩ : syracuseStep 2012141 = 754553) (by norm_num)
theorem B1340401 : Blo 1190412 1340401 := bbase (se 2 (by rfl) ⟨502650, by rfl⟩ : syracuseStep 1340401 = 1005301) (by norm_num)
theorem B1340437 : Blo 1190412 1340437 := bbase (se 6 (by rfl) ⟨31416, by rfl⟩ : syracuseStep 1340437 = 62833) (by norm_num)
theorem B1340473 : Blo 1190412 1340473 := bbase (se 2 (by rfl) ⟨502677, by rfl⟩ : syracuseStep 1340473 = 1005355) (by norm_num)
theorem B1610813 : Blo 1190412 1610813 := bbase (se 3 (by rfl) ⟨302027, by rfl⟩ : syracuseStep 1610813 = 604055) (by norm_num)
theorem B1340509 : Blo 1190412 1340509 := bbase (se 3 (by rfl) ⟨251345, by rfl⟩ : syracuseStep 1340509 = 502691) (by norm_num)
theorem B1340545 : Blo 1190412 1340545 := bbase (se 2 (by rfl) ⟨502704, by rfl⟩ : syracuseStep 1340545 = 1005409) (by norm_num)
theorem B2544797 : Blo 1190412 2544797 := bbase (se 3 (by rfl) ⟨477149, by rfl⟩ : syracuseStep 2544797 = 954299) (by norm_num)
theorem B1340581 : Blo 1190412 1340581 := bbase (se 4 (by rfl) ⟨125679, by rfl⟩ : syracuseStep 1340581 = 251359) (by norm_num)
theorem B4019381 : Blo 1190412 4019381 := bbase (se 5 (by rfl) ⟨188408, by rfl⟩ : syracuseStep 4019381 = 376817) (by norm_num)
theorem B1340617 : Blo 1190412 1340617 := bbase (se 2 (by rfl) ⟨502731, by rfl⟩ : syracuseStep 1340617 = 1005463) (by norm_num)
theorem B6034661 : Blo 1190412 6034661 := bbase (se 4 (by rfl) ⟨565749, by rfl⟩ : syracuseStep 6034661 = 1131499) (by norm_num)
theorem B1340653 : Blo 1190412 1340653 := bbase (se 3 (by rfl) ⟨251372, by rfl⟩ : syracuseStep 1340653 = 502745) (by norm_num)
theorem B1340689 : Blo 1190412 1340689 := bbase (se 2 (by rfl) ⟨502758, by rfl⟩ : syracuseStep 1340689 = 1005517) (by norm_num)
theorem B1340725 : Blo 1190412 1340725 := bbase (se 5 (by rfl) ⟨62846, by rfl⟩ : syracuseStep 1340725 = 125693) (by norm_num)
theorem B1340761 : Blo 1190412 1340761 := bbase (se 2 (by rfl) ⟨502785, by rfl⟩ : syracuseStep 1340761 = 1005571) (by norm_num)
theorem B1340797 : Blo 1190412 1340797 := bbase (se 3 (by rfl) ⟨251399, by rfl⟩ : syracuseStep 1340797 = 502799) (by norm_num)
theorem B1340833 : Blo 1190412 1340833 := bbase (se 2 (by rfl) ⟨502812, by rfl⟩ : syracuseStep 1340833 = 1005625) (by norm_num)
theorem B1340869 : Blo 1190412 1340869 := bbase (se 4 (by rfl) ⟨125706, by rfl⟩ : syracuseStep 1340869 = 251413) (by norm_num)
theorem B1340905 : Blo 1190412 1340905 := bbase (se 2 (by rfl) ⟨502839, by rfl⟩ : syracuseStep 1340905 = 1005679) (by norm_num)
theorem B1340941 : Blo 1190412 1340941 := bbase (se 3 (by rfl) ⟨251426, by rfl⟩ : syracuseStep 1340941 = 502853) (by norm_num)
theorem B1340977 : Blo 1190412 1340977 := bbase (se 2 (by rfl) ⟨502866, by rfl⟩ : syracuseStep 1340977 = 1005733) (by norm_num)
theorem B1341013 : Blo 1190412 1341013 := bbase (se 8 (by rfl) ⟨7857, by rfl⟩ : syracuseStep 1341013 = 15715) (by norm_num)
theorem B4019813 : Blo 1190412 4019813 := bbase (se 4 (by rfl) ⟨376857, by rfl⟩ : syracuseStep 4019813 = 753715) (by norm_num)
theorem B1341049 : Blo 1190412 1341049 := bbase (se 2 (by rfl) ⟨502893, by rfl⟩ : syracuseStep 1341049 = 1005787) (by norm_num)
theorem B6026885 : Blo 1190412 6026885 := bbase (se 4 (by rfl) ⟨565020, by rfl⟩ : syracuseStep 6026885 = 1130041) (by norm_num)
theorem B1341085 : Blo 1190412 1341085 := bbase (se 3 (by rfl) ⟨251453, by rfl⟩ : syracuseStep 1341085 = 502907) (by norm_num)
theorem B2037413 : Blo 1190412 2037413 := bbase (se 4 (by rfl) ⟨191007, by rfl⟩ : syracuseStep 2037413 = 382015) (by norm_num)
theorem B1341121 : Blo 1190412 1341121 := bbase (se 2 (by rfl) ⟨502920, by rfl⟩ : syracuseStep 1341121 = 1005841) (by norm_num)
theorem B1341157 : Blo 1190412 1341157 := bbase (se 4 (by rfl) ⟨125733, by rfl⟩ : syracuseStep 1341157 = 251467) (by norm_num)
theorem B1341193 : Blo 1190412 1341193 := bbase (se 2 (by rfl) ⟨502947, by rfl⟩ : syracuseStep 1341193 = 1005895) (by norm_num)
theorem B17880853 : Blo 1190412 17880853 := bbase (se 6 (by rfl) ⟨419082, by rfl⟩ : syracuseStep 17880853 = 838165) (by norm_num)
theorem B1341229 : Blo 1190412 1341229 := bbase (se 3 (by rfl) ⟨251480, by rfl⟩ : syracuseStep 1341229 = 502961) (by norm_num)
theorem B5084981 : Blo 1190412 5084981 := bbase (se 5 (by rfl) ⟨238358, by rfl⟩ : syracuseStep 5084981 = 476717) (by norm_num)
theorem B1341265 : Blo 1190412 1341265 := bbase (se 2 (by rfl) ⟨502974, by rfl⟩ : syracuseStep 1341265 = 1005949) (by norm_num)
theorem B1341301 : Blo 1190412 1341301 := bbase (se 5 (by rfl) ⟨62873, by rfl⟩ : syracuseStep 1341301 = 125747) (by norm_num)
theorem B4585349 : Blo 1190412 4585349 := bbase (se 4 (by rfl) ⟨429876, by rfl⟩ : syracuseStep 4585349 = 859753) (by norm_num)
theorem B1341337 : Blo 1190412 1341337 := bbase (se 2 (by rfl) ⟨503001, by rfl⟩ : syracuseStep 1341337 = 1006003) (by norm_num)
theorem B1341373 : Blo 1190412 1341373 := bbase (se 3 (by rfl) ⟨251507, by rfl⟩ : syracuseStep 1341373 = 503015) (by norm_num)
theorem B2414549 : Blo 1190412 2414549 := bbase (se 7 (by rfl) ⟨28295, by rfl⟩ : syracuseStep 2414549 = 56591) (by norm_num)
theorem B1341409 : Blo 1190412 1341409 := bbase (se 2 (by rfl) ⟨503028, by rfl⟩ : syracuseStep 1341409 = 1006057) (by norm_num)
theorem B2545661 : Blo 1190412 2545661 := bbase (se 3 (by rfl) ⟨477311, by rfl⟩ : syracuseStep 2545661 = 954623) (by norm_num)
theorem B1341445 : Blo 1190412 1341445 := bbase (se 4 (by rfl) ⟨125760, by rfl⟩ : syracuseStep 1341445 = 251521) (by norm_num)
theorem B4020245 : Blo 1190412 4020245 := bbase (se 6 (by rfl) ⟨94224, by rfl⟩ : syracuseStep 4020245 = 188449) (by norm_num)
theorem B8149045 : Blo 1190412 8149045 := bbase (se 5 (by rfl) ⟨381986, by rfl⟩ : syracuseStep 8149045 = 763973) (by norm_num)
theorem B2414645 : Blo 1190412 2414645 := bbase (se 5 (by rfl) ⟨113186, by rfl⟩ : syracuseStep 2414645 = 226373) (by norm_num)
theorem B2545805 : Blo 1190412 2545805 := bbase (se 3 (by rfl) ⟨477338, by rfl⟩ : syracuseStep 2545805 = 954677) (by norm_num)
theorem B7633109 : Blo 1190412 7633109 := bbase (se 7 (by rfl) ⟨89450, by rfl⟩ : syracuseStep 7633109 = 178901) (by norm_num)
theorem B6109445 : Blo 1190412 6109445 := bbase (se 4 (by rfl) ⟨572760, by rfl⟩ : syracuseStep 6109445 = 1145521) (by norm_num)
theorem B1431977 : Blo 1190412 1431977 := bbase (se 2 (by rfl) ⟨536991, by rfl⟩ : syracuseStep 1431977 = 1073983) (by norm_num)
theorem B4020677 : Blo 1190412 4020677 := bbase (se 4 (by rfl) ⟨376938, by rfl⟩ : syracuseStep 4020677 = 753877) (by norm_num)
theorem B3389941 : Blo 1190412 3389941 := bbase (se 5 (by rfl) ⟨158903, by rfl⟩ : syracuseStep 3389941 = 317807) (by norm_num)
theorem B6035957 : Blo 1190412 6035957 := bbase (se 5 (by rfl) ⟨282935, by rfl⟩ : syracuseStep 6035957 = 565871) (by norm_num)
theorem B2718301 : Blo 1190412 2718301 := bbase (se 3 (by rfl) ⟨509681, by rfl⟩ : syracuseStep 2718301 = 1019363) (by norm_num)
theorem B1907317 : Blo 1190412 1907317 := bbase (se 5 (by rfl) ⟨89405, by rfl⟩ : syracuseStep 1907317 = 178811) (by norm_num)
theorem B1432189 : Blo 1190412 1432189 := bbase (se 3 (by rfl) ⟨268535, by rfl⟩ : syracuseStep 1432189 = 537071) (by norm_num)
theorem B3013301 : Blo 1190412 3013301 := bbase (se 5 (by rfl) ⟨141248, by rfl⟩ : syracuseStep 3013301 = 282497) (by norm_num)
theorem B1907381 : Blo 1190412 1907381 := bbase (se 5 (by rfl) ⟨89408, by rfl⟩ : syracuseStep 1907381 = 178817) (by norm_num)
theorem B3816197 : Blo 1190412 3816197 := bbase (se 4 (by rfl) ⟨357768, by rfl⟩ : syracuseStep 3816197 = 715537) (by norm_num)
theorem B1432333 : Blo 1190412 1432333 := bbase (se 3 (by rfl) ⟨268562, by rfl⟩ : syracuseStep 1432333 = 537125) (by norm_num)
theorem B74316629 : Blo 1190412 74316629 := bbase (se 9 (by rfl) ⟨217724, by rfl⟩ : syracuseStep 74316629 = 435449) (by norm_num)
theorem B6437717 : Blo 1190412 6437717 := bbase (se 9 (by rfl) ⟨18860, by rfl⟩ : syracuseStep 6437717 = 37721) (by norm_num)
theorem B2579293 : Blo 1190412 2579293 := bbase (se 3 (by rfl) ⟨483617, by rfl⟩ : syracuseStep 2579293 = 967235) (by norm_num)
theorem B2292581 : Blo 1190412 2292581 := bbase (se 4 (by rfl) ⟨214929, by rfl⟩ : syracuseStep 2292581 = 429859) (by norm_num)
theorem B11598709 : Blo 1190412 11598709 := bbase (se 5 (by rfl) ⟨543689, by rfl⟩ : syracuseStep 11598709 = 1087379) (by norm_num)
theorem B4021109 : Blo 1190412 4021109 := bbase (se 5 (by rfl) ⟨188489, by rfl⟩ : syracuseStep 4021109 = 376979) (by norm_num)
theorem B2546549 : Blo 1190412 2546549 := bbase (se 5 (by rfl) ⟨119369, by rfl⟩ : syracuseStep 2546549 = 238739) (by norm_num)
theorem B6028181 : Blo 1190412 6028181 := bbase (se 6 (by rfl) ⟨141285, by rfl⟩ : syracuseStep 6028181 = 282571) (by norm_num)
theorem B6445973 : Blo 1190412 6445973 := bbase (se 6 (by rfl) ⟨151077, by rfl⟩ : syracuseStep 6445973 = 302155) (by norm_num)
theorem B13581269 : Blo 1190412 13581269 := bbase (se 7 (by rfl) ⟨159155, by rfl⟩ : syracuseStep 13581269 = 318311) (by norm_num)
theorem B3013645 : Blo 1190412 3013645 := bbase (se 3 (by rfl) ⟨565058, by rfl⟩ : syracuseStep 3013645 = 1130117) (by norm_num)
theorem B2260037 : Blo 1190412 2260037 := bbase (se 4 (by rfl) ⟨211878, by rfl⟩ : syracuseStep 2260037 = 423757) (by norm_num)
theorem B6782069 : Blo 1190412 6782069 := bbase (se 5 (by rfl) ⟨317909, by rfl⟩ : syracuseStep 6782069 = 635819) (by norm_num)
theorem B3013757 : Blo 1190412 3013757 := bbase (se 3 (by rfl) ⟨565079, by rfl⟩ : syracuseStep 3013757 = 1130159) (by norm_num)
theorem B4832405 : Blo 1190412 4832405 := bbase (se 6 (by rfl) ⟨113259, by rfl⟩ : syracuseStep 4832405 = 226519) (by norm_num)
theorem B2415781 : Blo 1190412 2415781 := bbase (se 4 (by rfl) ⟨226479, by rfl⟩ : syracuseStep 2415781 = 452959) (by norm_num)
theorem B1359037 : Blo 1190412 1359037 := bbase (se 3 (by rfl) ⟨254819, by rfl⟩ : syracuseStep 1359037 = 509639) (by norm_num)
theorem B11443477 : Blo 1190412 11443477 := bbase (se 6 (by rfl) ⟨268206, by rfl⟩ : syracuseStep 11443477 = 536413) (by norm_num)
theorem B4021541 : Blo 1190412 4021541 := bbase (se 4 (by rfl) ⟨377019, by rfl⟩ : syracuseStep 4021541 = 754039) (by norm_num)
theorem B3013949 : Blo 1190412 3013949 := bbase (se 3 (by rfl) ⟨565115, by rfl⟩ : syracuseStep 3013949 = 1130231) (by norm_num)
theorem B5725525 : Blo 1190412 5725525 := bbase (se 11 (by rfl) ⟨4193, by rfl⟩ : syracuseStep 5725525 = 8387) (by norm_num)
theorem B2260325 : Blo 1190412 2260325 := bbase (se 4 (by rfl) ⟨211905, by rfl⟩ : syracuseStep 2260325 = 423811) (by norm_num)
theorem B2039165 : Blo 1190412 2039165 := bbase (se 3 (by rfl) ⟨382343, by rfl⟩ : syracuseStep 2039165 = 764687) (by norm_num)
theorem B1506701 : Blo 1190412 1506701 := bbase (se 3 (by rfl) ⟨282506, by rfl⟩ : syracuseStep 1506701 = 565013) (by norm_num)
theorem B4521365 : Blo 1190412 4521365 := bbase (se 6 (by rfl) ⟨105969, by rfl⟩ : syracuseStep 4521365 = 211939) (by norm_num)
theorem B1506757 : Blo 1190412 1506757 := bbase (se 4 (by rfl) ⟨141258, by rfl⟩ : syracuseStep 1506757 = 282517) (by norm_num)
theorem B2260477 : Blo 1190412 2260477 := bbase (se 3 (by rfl) ⟨423839, by rfl⟩ : syracuseStep 2260477 = 847679) (by norm_num)
theorem B3816965 : Blo 1190412 3816965 := bbase (se 4 (by rfl) ⟨357840, by rfl⟩ : syracuseStep 3816965 = 715681) (by norm_num)
theorem B3055133 : Blo 1190412 3055133 := bbase (se 3 (by rfl) ⟨572837, by rfl⟩ : syracuseStep 3055133 = 1145675) (by norm_num)
theorem B1506853 : Blo 1190412 1506853 := bbase (se 4 (by rfl) ⟨141267, by rfl⟩ : syracuseStep 1506853 = 282535) (by norm_num)
theorem B2039357 : Blo 1190412 2039357 := bbase (se 3 (by rfl) ⟨382379, by rfl⟩ : syracuseStep 2039357 = 764759) (by norm_num)
theorem B5226053 : Blo 1190412 5226053 := bbase (se 4 (by rfl) ⟨489942, by rfl⟩ : syracuseStep 5226053 = 979885) (by norm_num)
theorem B1359497 : Blo 1190412 1359497 := bbase (se 2 (by rfl) ⟨509811, by rfl⟩ : syracuseStep 1359497 = 1019623) (by norm_num)
theorem B3014293 : Blo 1190412 3014293 := bbase (se 6 (by rfl) ⟨70647, by rfl⟩ : syracuseStep 3014293 = 141295) (by norm_num)
theorem B2678453 : Blo 1190412 2678453 := bbase (se 5 (by rfl) ⟨125552, by rfl⟩ : syracuseStep 2678453 = 251105) (by norm_num)
theorem B4521653 : Blo 1190412 4521653 := bbase (se 5 (by rfl) ⟨211952, by rfl⟩ : syracuseStep 4521653 = 423905) (by norm_num)
theorem B1695421 : Blo 1190412 1695421 := bbase (se 3 (by rfl) ⟨317891, by rfl⟩ : syracuseStep 1695421 = 635783) (by norm_num)
theorem B1507025 : Blo 1190412 1507025 := bbase (se 2 (by rfl) ⟨565134, by rfl⟩ : syracuseStep 1507025 = 1130269) (by norm_num)
theorem B4021973 : Blo 1190412 4021973 := bbase (se 7 (by rfl) ⟨47132, by rfl⟩ : syracuseStep 4021973 = 94265) (by norm_num)
theorem B2719469 : Blo 1190412 2719469 := bbase (se 3 (by rfl) ⟨509900, by rfl⟩ : syracuseStep 2719469 = 1019801) (by norm_num)
theorem B2678525 : Blo 1190412 2678525 := bbase (se 3 (by rfl) ⟨502223, by rfl⟩ : syracuseStep 2678525 = 1004447) (by norm_num)
theorem B3014405 : Blo 1190412 3014405 := bbase (se 4 (by rfl) ⟨282600, by rfl⟩ : syracuseStep 3014405 = 565201) (by norm_num)
theorem B1507081 : Blo 1190412 1507081 := bbase (se 2 (by rfl) ⟨565155, by rfl⟩ : syracuseStep 1507081 = 1130311) (by norm_num)
theorem B4185877 : Blo 1190412 4185877 := bbase (se 6 (by rfl) ⟨98106, by rfl⟩ : syracuseStep 4185877 = 196213) (by norm_num)
theorem B1785629 : Blo 1190412 1785629 := bbase (se 3 (by rfl) ⟨334805, by rfl⟩ : syracuseStep 1785629 = 669611) (by norm_num)
theorem B2260781 : Blo 1190412 2260781 := bbase (se 3 (by rfl) ⟨423896, by rfl⟩ : syracuseStep 2260781 = 847793) (by norm_num)
theorem B1785653 : Blo 1190412 1785653 := bbase (se 5 (by rfl) ⟨83702, by rfl⟩ : syracuseStep 1785653 = 167405) (by norm_num)
theorem B2678597 : Blo 1190412 2678597 := bbase (se 4 (by rfl) ⟨251118, by rfl⟩ : syracuseStep 2678597 = 502237) (by norm_num)
theorem B1785677 : Blo 1190412 1785677 := bbase (se 3 (by rfl) ⟨334814, by rfl⟩ : syracuseStep 1785677 = 669629) (by norm_num)
theorem B3620693 : Blo 1190412 3620693 := bbase (se 9 (by rfl) ⟨10607, by rfl⟩ : syracuseStep 3620693 = 21215) (by norm_num)
theorem B1785701 : Blo 1190412 1785701 := bbase (se 4 (by rfl) ⟨167409, by rfl⟩ : syracuseStep 1785701 = 334819) (by norm_num)
theorem B1507177 : Blo 1190412 1507177 := bbase (se 2 (by rfl) ⟨565191, by rfl⟩ : syracuseStep 1507177 = 1130383) (by norm_num)
theorem B1785725 : Blo 1190412 1785725 := bbase (se 3 (by rfl) ⟨334823, by rfl⟩ : syracuseStep 1785725 = 669647) (by norm_num)
theorem B2678669 : Blo 1190412 2678669 := bbase (se 3 (by rfl) ⟨502250, by rfl⟩ : syracuseStep 2678669 = 1004501) (by norm_num)
theorem B1785749 : Blo 1190412 1785749 := bbase (se 6 (by rfl) ⟨41853, by rfl⟩ : syracuseStep 1785749 = 83707) (by norm_num)
theorem B1785773 : Blo 1190412 1785773 := bbase (se 3 (by rfl) ⟨334832, by rfl⟩ : syracuseStep 1785773 = 669665) (by norm_num)
theorem B1785797 : Blo 1190412 1785797 := bbase (se 4 (by rfl) ⟨167418, by rfl⟩ : syracuseStep 1785797 = 334837) (by norm_num)
theorem B3014597 : Blo 1190412 3014597 := bbase (se 4 (by rfl) ⟨282618, by rfl⟩ : syracuseStep 3014597 = 565237) (by norm_num)
theorem B2678741 : Blo 1190412 2678741 := bbase (se 7 (by rfl) ⟨31391, by rfl⟩ : syracuseStep 2678741 = 62783) (by norm_num)
theorem B3391445 : Blo 1190412 3391445 := bbase (se 7 (by rfl) ⟨39743, by rfl⟩ : syracuseStep 3391445 = 79487) (by norm_num)
theorem B1785821 : Blo 1190412 1785821 := bbase (se 3 (by rfl) ⟨334841, by rfl⟩ : syracuseStep 1785821 = 669683) (by norm_num)
theorem B1908701 : Blo 1190412 1908701 := bbase (se 3 (by rfl) ⟨357881, by rfl⟩ : syracuseStep 1908701 = 715763) (by norm_num)
theorem B1785845 : Blo 1190412 1785845 := bbase (se 5 (by rfl) ⟨83711, by rfl⟩ : syracuseStep 1785845 = 167423) (by norm_num)
theorem B1785857 : Blo 1190412 1785857 := bstep (se 2 (by rfl) ⟨669696, by rfl⟩ : syracuseStep 1785857 = 1339393) B1339393
theorem B1695745 : Blo 1190412 1695745 := bstep (se 2 (by rfl) ⟨635904, by rfl⟩ : syracuseStep 1695745 = 1271809) B1271809
theorem B2261009 : Blo 1190412 2261009 := bstep (se 2 (by rfl) ⟨847878, by rfl⟩ : syracuseStep 2261009 = 1695757) B1695757
theorem B1785875 : Blo 1190412 1785875 := bstep (se 1 (by rfl) ⟨1339406, by rfl⟩ : syracuseStep 1785875 = 2678813) B2678813
theorem B3440675 : Blo 1190412 3440675 := bstep (se 1 (by rfl) ⟨2580506, by rfl⟩ : syracuseStep 3440675 = 5161013) B5161013
theorem B1785905 : Blo 1190412 1785905 := bstep (se 2 (by rfl) ⟨669714, by rfl⟩ : syracuseStep 1785905 = 1339429) B1339429
theorem B1785923 : Blo 1190412 1785923 := bstep (se 1 (by rfl) ⟨1339442, by rfl⟩ : syracuseStep 1785923 = 2678885) B2678885
theorem B1908803 : Blo 1190412 1908803 := bstep (se 1 (by rfl) ⟨1431602, by rfl⟩ : syracuseStep 1908803 = 2863205) B2863205
theorem B1785953 : Blo 1190412 1785953 := bstep (se 2 (by rfl) ⟨669732, by rfl⟩ : syracuseStep 1785953 = 1339465) B1339465
theorem B1785971 : Blo 1190412 1785971 := bstep (se 1 (by rfl) ⟨1339478, by rfl⟩ : syracuseStep 1785971 = 2678957) B2678957
theorem B1786001 : Blo 1190412 1786001 := bstep (se 2 (by rfl) ⟨669750, by rfl⟩ : syracuseStep 1786001 = 1339501) B1339501
theorem B1786019 : Blo 1190412 1786019 := bstep (se 1 (by rfl) ⟨1339514, by rfl⟩ : syracuseStep 1786019 = 2679029) B2679029
theorem B2580643 : Blo 1190412 2580643 := bstep (se 1 (by rfl) ⟨1935482, by rfl⟩ : syracuseStep 2580643 = 3870965) B3870965
theorem B1786049 : Blo 1190412 1786049 := bstep (se 2 (by rfl) ⟨669768, by rfl⟩ : syracuseStep 1786049 = 1339537) B1339537
theorem B2678993 : Blo 1190412 2678993 := bstep (se 2 (by rfl) ⟨1004622, by rfl⟩ : syracuseStep 2678993 = 2009245) B2009245
theorem B1786067 : Blo 1190412 1786067 := bstep (se 1 (by rfl) ⟨1339550, by rfl⟩ : syracuseStep 1786067 = 2679101) B2679101
theorem B2679011 : Blo 1190412 2679011 := bstep (se 1 (by rfl) ⟨2009258, by rfl⟩ : syracuseStep 2679011 = 4018517) B4018517
theorem B1786097 : Blo 1190412 1786097 := bstep (se 2 (by rfl) ⟨669786, by rfl⟩ : syracuseStep 1786097 = 1339573) B1339573
theorem B4022513 : Blo 1190412 4022513 := bstep (se 2 (by rfl) ⟨1508442, by rfl⟩ : syracuseStep 4022513 = 3016885) B3016885
theorem B1786115 : Blo 1190412 1786115 := bstep (se 1 (by rfl) ⟨1339586, by rfl⟩ : syracuseStep 1786115 = 2679173) B2679173
theorem B1786145 : Blo 1190412 1786145 := bstep (se 2 (by rfl) ⟨669804, by rfl⟩ : syracuseStep 1786145 = 1339609) B1339609
theorem B2261297 : Blo 1190412 2261297 := bstep (se 2 (by rfl) ⟨847986, by rfl⟩ : syracuseStep 2261297 = 1695973) B1695973
theorem B1786163 : Blo 1190412 1786163 := bstep (se 1 (by rfl) ⟨1339622, by rfl⟩ : syracuseStep 1786163 = 2679245) B2679245
theorem B1786193 : Blo 1190412 1786193 := bstep (se 2 (by rfl) ⟨669822, by rfl⟩ : syracuseStep 1786193 = 1339645) B1339645
theorem B1786211 : Blo 1190412 1786211 := bstep (se 1 (by rfl) ⟨1339658, by rfl⟩ : syracuseStep 1786211 = 2679317) B2679317
theorem B4292963 : Blo 1190412 4292963 := bstep (se 1 (by rfl) ⟨3219722, by rfl⟩ : syracuseStep 4292963 = 6439445) B6439445
theorem B1786241 : Blo 1190412 1786241 := bstep (se 2 (by rfl) ⟨669840, by rfl⟩ : syracuseStep 1786241 = 1339681) B1339681
theorem B1786259 : Blo 1190412 1786259 := bstep (se 1 (by rfl) ⟨1339694, by rfl⟩ : syracuseStep 1786259 = 2679389) B2679389
theorem B1786289 : Blo 1190412 1786289 := bstep (se 2 (by rfl) ⟨669858, by rfl⟩ : syracuseStep 1786289 = 1339717) B1339717
theorem B1786307 : Blo 1190412 1786307 := bstep (se 1 (by rfl) ⟨1339730, by rfl⟩ : syracuseStep 1786307 = 2679461) B2679461
theorem B1786337 : Blo 1190412 1786337 := bstep (se 2 (by rfl) ⟨669876, by rfl⟩ : syracuseStep 1786337 = 1339753) B1339753
theorem B2679281 : Blo 1190412 2679281 := bstep (se 2 (by rfl) ⟨1004730, by rfl⟩ : syracuseStep 2679281 = 2009461) B2009461
theorem B1696241 : Blo 1190412 1696241 := bstep (se 2 (by rfl) ⟨636090, by rfl⟩ : syracuseStep 1696241 = 1272181) B1272181
theorem B1786355 : Blo 1190412 1786355 := bstep (se 1 (by rfl) ⟨1339766, by rfl⟩ : syracuseStep 1786355 = 2679533) B2679533
theorem B2679299 : Blo 1190412 2679299 := bstep (se 1 (by rfl) ⟨2009474, by rfl⟩ : syracuseStep 2679299 = 4018949) B4018949
theorem B1786385 : Blo 1190412 1786385 := bstep (se 2 (by rfl) ⟨669894, by rfl⟩ : syracuseStep 1786385 = 1339789) B1339789
theorem B1786403 : Blo 1190412 1786403 := bstep (se 1 (by rfl) ⟨1339802, by rfl⟩ : syracuseStep 1786403 = 2679605) B2679605
theorem B1810979 : Blo 1190412 1810979 := bstep (se 1 (by rfl) ⟨1358234, by rfl⟩ : syracuseStep 1810979 = 2716469) B2716469
theorem B1507891 : Blo 1190412 1507891 := bstep (se 1 (by rfl) ⟨1130918, by rfl⟩ : syracuseStep 1507891 = 2261837) B2261837
theorem B1786433 : Blo 1190412 1786433 := bstep (se 2 (by rfl) ⟨669912, by rfl⟩ : syracuseStep 1786433 = 1339825) B1339825
theorem B1786451 : Blo 1190412 1786451 := bstep (se 1 (by rfl) ⟨1339838, by rfl⟩ : syracuseStep 1786451 = 2679677) B2679677
theorem B1786481 : Blo 1190412 1786481 := bstep (se 2 (by rfl) ⟨669930, by rfl⟩ : syracuseStep 1786481 = 1339861) B1339861
theorem B1786499 : Blo 1190412 1786499 := bstep (se 1 (by rfl) ⟨1339874, by rfl⟩ : syracuseStep 1786499 = 2679749) B2679749
theorem B1507987 : Blo 1190412 1507987 := bstep (se 1 (by rfl) ⟨1130990, by rfl⟩ : syracuseStep 1507987 = 2261981) B2261981
theorem B1786529 : Blo 1190412 1786529 := bstep (se 2 (by rfl) ⟨669948, by rfl⟩ : syracuseStep 1786529 = 1339897) B1339897
theorem B1786547 : Blo 1190412 1786547 := bstep (se 1 (by rfl) ⟨1339910, by rfl⟩ : syracuseStep 1786547 = 2679821) B2679821
theorem B1786577 : Blo 1190412 1786577 := bstep (se 2 (by rfl) ⟨669966, by rfl⟩ : syracuseStep 1786577 = 1339933) B1339933
theorem B3015377 : Blo 1190412 3015377 := bstep (se 2 (by rfl) ⟨1130766, by rfl⟩ : syracuseStep 3015377 = 2261533) B2261533
theorem B1786595 : Blo 1190412 1786595 := bstep (se 1 (by rfl) ⟨1339946, by rfl⟩ : syracuseStep 1786595 = 2679893) B2679893
theorem B1786625 : Blo 1190412 1786625 := bstep (se 2 (by rfl) ⟨669984, by rfl⟩ : syracuseStep 1786625 = 1339969) B1339969
theorem B3015427 : Blo 1190412 3015427 := bstep (se 1 (by rfl) ⟨2261570, by rfl⟩ : syracuseStep 3015427 = 4523141) B4523141
theorem B6619909 : Blo 1190412 6619909 := bstep (se 4 (by rfl) ⟨620616, by rfl⟩ : syracuseStep 6619909 = 1241233) B1241233
theorem B4023053 : Blo 1190412 4023053 := bstep (se 3 (by rfl) ⟨754322, by rfl⟩ : syracuseStep 4023053 = 1508645) B1508645
theorem B2679569 : Blo 1190412 2679569 := bstep (se 2 (by rfl) ⟨1004838, by rfl⟩ : syracuseStep 2679569 = 2009677) B2009677
theorem B1786643 : Blo 1190412 1786643 := bstep (se 1 (by rfl) ⟨1339982, by rfl⟩ : syracuseStep 1786643 = 2679965) B2679965
theorem B2679587 : Blo 1190412 2679587 := bstep (se 1 (by rfl) ⟨2009690, by rfl⟩ : syracuseStep 2679587 = 4019381) B4019381
theorem B1786673 : Blo 1190412 1786673 := bstep (se 2 (by rfl) ⟨670002, by rfl⟩ : syracuseStep 1786673 = 1340005) B1340005
theorem B1786691 : Blo 1190412 1786691 := bstep (se 1 (by rfl) ⟨1340018, by rfl⟩ : syracuseStep 1786691 = 2680037) B2680037
theorem B4023107 : Blo 1190412 4023107 := bstep (se 1 (by rfl) ⟨3017330, by rfl⟩ : syracuseStep 4023107 = 6034661) B6034661
theorem B1909585 : Blo 1190412 1909585 := bstep (se 2 (by rfl) ⟨716094, by rfl⟩ : syracuseStep 1909585 = 1432189) B1432189
theorem B1786721 : Blo 1190412 1786721 := bstep (se 2 (by rfl) ⟨670020, by rfl⟩ : syracuseStep 1786721 = 1340041) B1340041
theorem B1786739 : Blo 1190412 1786739 := bstep (se 1 (by rfl) ⟨1340054, by rfl⟩ : syracuseStep 1786739 = 2680109) B2680109
theorem B3621763 : Blo 1190412 3621763 := bstep (se 1 (by rfl) ⟨2716322, by rfl⟩ : syracuseStep 3621763 = 5432645) B5432645
theorem B14484365 : Blo 1190412 14484365 := bstep (se 3 (by rfl) ⟨2715818, by rfl⟩ : syracuseStep 14484365 = 5431637) B5431637
theorem B1786769 : Blo 1190412 1786769 := bstep (se 2 (by rfl) ⟨670038, by rfl⟩ : syracuseStep 1786769 = 1340077) B1340077
theorem B3015569 : Blo 1190412 3015569 := bstep (se 2 (by rfl) ⟨1130838, by rfl⟩ : syracuseStep 3015569 = 2261677) B2261677
theorem B1786787 : Blo 1190412 1786787 := bstep (se 1 (by rfl) ⟨1340090, by rfl⟩ : syracuseStep 1786787 = 2680181) B2680181
theorem B1786817 : Blo 1190412 1786817 := bstep (se 2 (by rfl) ⟨670056, by rfl⟩ : syracuseStep 1786817 = 1340113) B1340113
theorem B2147267 : Blo 1190412 2147267 := bstep (se 1 (by rfl) ⟨1610450, by rfl⟩ : syracuseStep 2147267 = 3220901) B3220901
theorem B1786835 : Blo 1190412 1786835 := bstep (se 1 (by rfl) ⟨1340126, by rfl⟩ : syracuseStep 1786835 = 2680253) B2680253
theorem B1786865 : Blo 1190412 1786865 := bstep (se 2 (by rfl) ⟨670074, by rfl⟩ : syracuseStep 1786865 = 1340149) B1340149
theorem B1786883 : Blo 1190412 1786883 := bstep (se 1 (by rfl) ⟨1340162, by rfl⟩ : syracuseStep 1786883 = 2680325) B2680325
theorem B2262019 : Blo 1190412 2262019 := bstep (se 1 (by rfl) ⟨1696514, by rfl⟩ : syracuseStep 2262019 = 3393029) B3393029
theorem B1786913 : Blo 1190412 1786913 := bstep (se 2 (by rfl) ⟨670092, by rfl⟩ : syracuseStep 1786913 = 1340185) B1340185
theorem B2679857 : Blo 1190412 2679857 := bstep (se 2 (by rfl) ⟨1004946, by rfl⟩ : syracuseStep 2679857 = 2009893) B2009893
theorem B1786931 : Blo 1190412 1786931 := bstep (se 1 (by rfl) ⟨1340198, by rfl⟩ : syracuseStep 1786931 = 2680397) B2680397
theorem B2679875 : Blo 1190412 2679875 := bstep (se 1 (by rfl) ⟨2009906, by rfl⟩ : syracuseStep 2679875 = 4019813) B4019813
theorem B1786961 : Blo 1190412 1786961 := bstep (se 2 (by rfl) ⟨670110, by rfl⟩ : syracuseStep 1786961 = 1340221) B1340221
theorem B4023377 : Blo 1190412 4023377 := bstep (se 2 (by rfl) ⟨1508766, by rfl⟩ : syracuseStep 4023377 = 3017533) B3017533
theorem B1786979 : Blo 1190412 1786979 := bstep (se 1 (by rfl) ⟨1340234, by rfl⟩ : syracuseStep 1786979 = 2680469) B2680469
theorem B3818605 : Blo 1190412 3818605 := bstep (se 3 (by rfl) ⟨715988, by rfl⟩ : syracuseStep 3818605 = 1431977) B1431977
theorem B6030449 : Blo 1190412 6030449 := bstep (se 2 (by rfl) ⟨2261418, by rfl⟩ : syracuseStep 6030449 = 4522837) B4522837
theorem B1787009 : Blo 1190412 1787009 := bstep (se 2 (by rfl) ⟨670128, by rfl⟩ : syracuseStep 1787009 = 1340257) B1340257
theorem B1508483 : Blo 1190412 1508483 := bstep (se 1 (by rfl) ⟨1131362, by rfl⟩ : syracuseStep 1508483 = 2262725) B2262725
theorem B1787027 : Blo 1190412 1787027 := bstep (se 1 (by rfl) ⟨1340270, by rfl⟩ : syracuseStep 1787027 = 2680541) B2680541
theorem B3392675 : Blo 1190412 3392675 := bstep (se 1 (by rfl) ⟨2544506, by rfl⟩ : syracuseStep 3392675 = 5089013) B5089013
theorem B1787057 : Blo 1190412 1787057 := bstep (se 2 (by rfl) ⟨670146, by rfl⟩ : syracuseStep 1787057 = 1340293) B1340293
theorem B1787075 : Blo 1190412 1787075 := bstep (se 1 (by rfl) ⟨1340306, by rfl⟩ : syracuseStep 1787075 = 2680613) B2680613
theorem B1787105 : Blo 1190412 1787105 := bstep (se 2 (by rfl) ⟨670164, by rfl⟩ : syracuseStep 1787105 = 1340329) B1340329
theorem B1787123 : Blo 1190412 1787123 := bstep (se 1 (by rfl) ⟨1340342, by rfl⟩ : syracuseStep 1787123 = 2680685) B2680685
theorem B3056899 : Blo 1190412 3056899 := bstep (se 1 (by rfl) ⟨2292674, by rfl⟩ : syracuseStep 3056899 = 4585349) B4585349
theorem B13575437 : Blo 1190412 13575437 := bstep (se 3 (by rfl) ⟨2545394, by rfl⟩ : syracuseStep 13575437 = 5090789) B5090789
theorem B1787153 : Blo 1190412 1787153 := bstep (se 2 (by rfl) ⟨670182, by rfl⟩ : syracuseStep 1787153 = 1340365) B1340365
theorem B6112547 : Blo 1190412 6112547 := bstep (se 1 (by rfl) ⟨4584410, by rfl⟩ : syracuseStep 6112547 = 9168821) B9168821
theorem B1787171 : Blo 1190412 1787171 := bstep (se 1 (by rfl) ⟨1340378, by rfl⟩ : syracuseStep 1787171 = 2680757) B2680757
theorem B1787201 : Blo 1190412 1787201 := bstep (se 2 (by rfl) ⟨670200, by rfl⟩ : syracuseStep 1787201 = 1340401) B1340401
theorem B2680145 : Blo 1190412 2680145 := bstep (se 2 (by rfl) ⟨1005054, by rfl⟩ : syracuseStep 2680145 = 2010109) B2010109
theorem B1787219 : Blo 1190412 1787219 := bstep (se 1 (by rfl) ⟨1340414, by rfl⟩ : syracuseStep 1787219 = 2680829) B2680829
theorem B1697107 : Blo 1190412 1697107 := bstep (se 1 (by rfl) ⟨1272830, by rfl⟩ : syracuseStep 1697107 = 2545661) B2545661
theorem B2680163 : Blo 1190412 2680163 := bstep (se 1 (by rfl) ⟨2010122, by rfl⟩ : syracuseStep 2680163 = 4020245) B4020245
theorem B1787249 : Blo 1190412 1787249 := bstep (se 2 (by rfl) ⟨670218, by rfl⟩ : syracuseStep 1787249 = 1340437) B1340437
theorem B1787267 : Blo 1190412 1787267 := bstep (se 1 (by rfl) ⟨1340450, by rfl⟩ : syracuseStep 1787267 = 2680901) B2680901
theorem B7628165 : Blo 1190412 7628165 := bstep (se 4 (by rfl) ⟨715140, by rfl⟩ : syracuseStep 7628165 = 1430281) B1430281
theorem B1787297 : Blo 1190412 1787297 := bstep (se 2 (by rfl) ⟨670236, by rfl⟩ : syracuseStep 1787297 = 1340473) B1340473
theorem B1787315 : Blo 1190412 1787315 := bstep (se 1 (by rfl) ⟨1340486, by rfl⟩ : syracuseStep 1787315 = 2680973) B2680973
theorem B1697203 : Blo 1190412 1697203 := bstep (se 1 (by rfl) ⟨1272902, by rfl⟩ : syracuseStep 1697203 = 2545805) B2545805
theorem B2262467 : Blo 1190412 2262467 := bstep (se 1 (by rfl) ⟨1696850, by rfl⟩ : syracuseStep 2262467 = 3393701) B3393701
theorem B1787345 : Blo 1190412 1787345 := bstep (se 2 (by rfl) ⟨670254, by rfl⟩ : syracuseStep 1787345 = 1340509) B1340509
theorem B5088739 : Blo 1190412 5088739 := bstep (se 1 (by rfl) ⟨3816554, by rfl⟩ : syracuseStep 5088739 = 7633109) B7633109
theorem B1787363 : Blo 1190412 1787363 := bstep (se 1 (by rfl) ⟨1340522, by rfl⟩ : syracuseStep 1787363 = 2681045) B2681045
theorem B1787393 : Blo 1190412 1787393 := bstep (se 2 (by rfl) ⟨670272, by rfl⟩ : syracuseStep 1787393 = 1340545) B1340545
theorem B13936141 : Blo 1190412 13936141 := bstep (se 3 (by rfl) ⟨2613026, by rfl⟩ : syracuseStep 13936141 = 5226053) B5226053
theorem B1787411 : Blo 1190412 1787411 := bstep (se 1 (by rfl) ⟨1340558, by rfl⟩ : syracuseStep 1787411 = 2681117) B2681117
theorem B1787441 : Blo 1190412 1787441 := bstep (se 2 (by rfl) ⟨670290, by rfl⟩ : syracuseStep 1787441 = 1340581) B1340581
theorem B3221041 : Blo 1190412 3221041 := bstep (se 2 (by rfl) ⟨1207890, by rfl⟩ : syracuseStep 3221041 = 2415781) B2415781
theorem B48342581 : Blo 1190412 48342581 := bstep (se 5 (by rfl) ⟨2266058, by rfl⟩ : syracuseStep 48342581 = 4532117) B4532117
theorem B25781813 : Blo 1190412 25781813 := bstep (se 5 (by rfl) ⟨1208522, by rfl⟩ : syracuseStep 25781813 = 2417045) B2417045
theorem B1787459 : Blo 1190412 1787459 := bstep (se 1 (by rfl) ⟨1340594, by rfl⟩ : syracuseStep 1787459 = 2681189) B2681189
theorem B4523597 : Blo 1190412 4523597 := bstep (se 3 (by rfl) ⟨848174, by rfl⟩ : syracuseStep 4523597 = 1696349) B1696349
theorem B1787489 : Blo 1190412 1787489 := bstep (se 2 (by rfl) ⟨670308, by rfl⟩ : syracuseStep 1787489 = 1340617) B1340617
theorem B4023917 : Blo 1190412 4023917 := bstep (se 3 (by rfl) ⟨754484, by rfl⟩ : syracuseStep 4023917 = 1508969) B1508969
theorem B2680433 : Blo 1190412 2680433 := bstep (se 2 (by rfl) ⟨1005162, by rfl⟩ : syracuseStep 2680433 = 2010325) B2010325
theorem B1787507 : Blo 1190412 1787507 := bstep (se 1 (by rfl) ⟨1340630, by rfl⟩ : syracuseStep 1787507 = 2681261) B2681261
theorem B2680451 : Blo 1190412 2680451 := bstep (se 1 (by rfl) ⟨2010338, by rfl⟩ : syracuseStep 2680451 = 4020677) B4020677
theorem B8152709 : Blo 1190412 8152709 := bstep (se 4 (by rfl) ⟨764316, by rfl⟩ : syracuseStep 8152709 = 1528633) B1528633
theorem B1787537 : Blo 1190412 1787537 := bstep (se 2 (by rfl) ⟨670326, by rfl⟩ : syracuseStep 1787537 = 1340653) B1340653
theorem B1787555 : Blo 1190412 1787555 := bstep (se 1 (by rfl) ⟨1340666, by rfl⟩ : syracuseStep 1787555 = 2681333) B2681333
theorem B4023971 : Blo 1190412 4023971 := bstep (se 1 (by rfl) ⟨3017978, by rfl⟩ : syracuseStep 4023971 = 6035957) B6035957
theorem B1787585 : Blo 1190412 1787585 := bstep (se 2 (by rfl) ⟨670344, by rfl⟩ : syracuseStep 1787585 = 1340689) B1340689
theorem B1787603 : Blo 1190412 1787603 := bstep (se 1 (by rfl) ⟨1340702, by rfl⟩ : syracuseStep 1787603 = 2681405) B2681405
theorem B2262755 : Blo 1190412 2262755 := bstep (se 1 (by rfl) ⟨1697066, by rfl⟩ : syracuseStep 2262755 = 3394133) B3394133
theorem B1787633 : Blo 1190412 1787633 := bstep (se 2 (by rfl) ⟨670362, by rfl⟩ : syracuseStep 1787633 = 1340725) B1340725
theorem B1632001 : Blo 1190412 1632001 := bstep (se 2 (by rfl) ⟨612000, by rfl⟩ : syracuseStep 1632001 = 1224001) B1224001
theorem B1787651 : Blo 1190412 1787651 := bstep (se 1 (by rfl) ⟨1340738, by rfl⟩ : syracuseStep 1787651 = 2681477) B2681477
theorem B5433101 : Blo 1190412 5433101 := bstep (se 3 (by rfl) ⟨1018706, by rfl⟩ : syracuseStep 5433101 = 2037413) B2037413
theorem B1787681 : Blo 1190412 1787681 := bstep (se 2 (by rfl) ⟨670380, by rfl⟩ : syracuseStep 1787681 = 1340761) B1340761
theorem B2008867 : Blo 1190412 2008867 := bstep (se 1 (by rfl) ⟨1506650, by rfl⟩ : syracuseStep 2008867 = 3013301) B3013301
theorem B1271587 : Blo 1190412 1271587 := bstep (se 1 (by rfl) ⟨953690, by rfl⟩ : syracuseStep 1271587 = 1907381) B1907381
theorem B1787699 : Blo 1190412 1787699 := bstep (se 1 (by rfl) ⟨1340774, by rfl⟩ : syracuseStep 1787699 = 2681549) B2681549
theorem B13756229 : Blo 1190412 13756229 := bstep (se 4 (by rfl) ⟨1289646, by rfl⟩ : syracuseStep 13756229 = 2579293) B2579293
theorem B1787729 : Blo 1190412 1787729 := bstep (se 2 (by rfl) ⟨670398, by rfl⟩ : syracuseStep 1787729 = 1340797) B1340797
theorem B1787747 : Blo 1190412 1787747 := bstep (se 1 (by rfl) ⟨1340810, by rfl⟩ : syracuseStep 1787747 = 2681621) B2681621
theorem B3016561 : Blo 1190412 3016561 := bstep (se 2 (by rfl) ⟨1131210, by rfl⟩ : syracuseStep 3016561 = 2262421) B2262421
theorem B1787777 : Blo 1190412 1787777 := bstep (se 2 (by rfl) ⟨670416, by rfl⟩ : syracuseStep 1787777 = 1340833) B1340833
theorem B2680721 : Blo 1190412 2680721 := bstep (se 2 (by rfl) ⟨1005270, by rfl⟩ : syracuseStep 2680721 = 2010541) B2010541
theorem B1787795 : Blo 1190412 1787795 := bstep (se 1 (by rfl) ⟨1340846, by rfl⟩ : syracuseStep 1787795 = 2681693) B2681693
theorem B2680739 : Blo 1190412 2680739 := bstep (se 1 (by rfl) ⟨2010554, by rfl⟩ : syracuseStep 2680739 = 4021109) B4021109
theorem B1697699 : Blo 1190412 1697699 := bstep (se 1 (by rfl) ⟨1273274, by rfl⟩ : syracuseStep 1697699 = 2546549) B2546549
theorem B2009009 : Blo 1190412 2009009 := bstep (se 2 (by rfl) ⟨753378, by rfl⟩ : syracuseStep 2009009 = 1506757) B1506757
theorem B1787825 : Blo 1190412 1787825 := bstep (se 2 (by rfl) ⟨670434, by rfl⟩ : syracuseStep 1787825 = 1340869) B1340869
theorem B4024241 : Blo 1190412 4024241 := bstep (se 2 (by rfl) ⟨1509090, by rfl⟩ : syracuseStep 4024241 = 3018181) B3018181
theorem B1787843 : Blo 1190412 1787843 := bstep (se 1 (by rfl) ⟨1340882, by rfl⟩ : syracuseStep 1787843 = 2681765) B2681765
theorem B3393485 : Blo 1190412 3393485 := bstep (se 3 (by rfl) ⟨636278, by rfl⟩ : syracuseStep 3393485 = 1272557) B1272557
theorem B1787873 : Blo 1190412 1787873 := bstep (se 2 (by rfl) ⟨670452, by rfl⟩ : syracuseStep 1787873 = 1340905) B1340905
theorem B9054179 : Blo 1190412 9054179 := bstep (se 1 (by rfl) ⟨6790634, by rfl⟩ : syracuseStep 9054179 = 13581269) B13581269
theorem B1787891 : Blo 1190412 1787891 := bstep (se 1 (by rfl) ⟨1340918, by rfl⟩ : syracuseStep 1787891 = 2681837) B2681837
theorem B1787921 : Blo 1190412 1787921 := bstep (se 2 (by rfl) ⟨670470, by rfl⟩ : syracuseStep 1787921 = 1340941) B1340941
theorem B1787939 : Blo 1190412 1787939 := bstep (se 1 (by rfl) ⟨1340954, by rfl⟩ : syracuseStep 1787939 = 2681909) B2681909
theorem B2009137 : Blo 1190412 2009137 := bstep (se 2 (by rfl) ⟨753426, by rfl⟩ : syracuseStep 2009137 = 1506853) B1506853
theorem B1787969 : Blo 1190412 1787969 := bstep (se 2 (by rfl) ⟨670488, by rfl⟩ : syracuseStep 1787969 = 1340977) B1340977
theorem B2009171 : Blo 1190412 2009171 := bstep (se 1 (by rfl) ⟨1506878, by rfl⟩ : syracuseStep 2009171 = 3013757) B3013757
theorem B1787987 : Blo 1190412 1787987 := bstep (se 1 (by rfl) ⟨1340990, by rfl⟩ : syracuseStep 1787987 = 2681981) B2681981
theorem B3221603 : Blo 1190412 3221603 := bstep (se 1 (by rfl) ⟨2416202, by rfl⟩ : syracuseStep 3221603 = 4832405) B4832405
theorem B1788017 : Blo 1190412 1788017 := bstep (se 2 (by rfl) ⟨670506, by rfl⟩ : syracuseStep 1788017 = 1341013) B1341013
theorem B3016835 : Blo 1190412 3016835 := bstep (se 1 (by rfl) ⟨2262626, by rfl⟩ : syracuseStep 3016835 = 4525253) B4525253
theorem B1788035 : Blo 1190412 1788035 := bstep (se 1 (by rfl) ⟨1341026, by rfl⟩ : syracuseStep 1788035 = 2682053) B2682053
theorem B3393677 : Blo 1190412 3393677 := bstep (se 3 (by rfl) ⟨636314, by rfl⟩ : syracuseStep 3393677 = 1272629) B1272629
theorem B1788065 : Blo 1190412 1788065 := bstep (se 2 (by rfl) ⟨670524, by rfl⟩ : syracuseStep 1788065 = 1341049) B1341049
theorem B2681009 : Blo 1190412 2681009 := bstep (se 2 (by rfl) ⟨1005378, by rfl⟩ : syracuseStep 2681009 = 2010757) B2010757
theorem B1788083 : Blo 1190412 1788083 := bstep (se 1 (by rfl) ⟨1341062, by rfl⟩ : syracuseStep 1788083 = 2682125) B2682125
theorem B2681027 : Blo 1190412 2681027 := bstep (se 1 (by rfl) ⟨2010770, by rfl⟩ : syracuseStep 2681027 = 4021541) B4021541
theorem B1788113 : Blo 1190412 1788113 := bstep (se 2 (by rfl) ⟨670542, by rfl⟩ : syracuseStep 1788113 = 1341085) B1341085
theorem B2009299 : Blo 1190412 2009299 := bstep (se 1 (by rfl) ⟨1506974, by rfl⟩ : syracuseStep 2009299 = 3013949) B3013949
theorem B1788131 : Blo 1190412 1788131 := bstep (se 1 (by rfl) ⟨1341098, by rfl⟩ : syracuseStep 1788131 = 2682197) B2682197
theorem B1788161 : Blo 1190412 1788161 := bstep (se 2 (by rfl) ⟨670560, by rfl⟩ : syracuseStep 1788161 = 1341121) B1341121
theorem B6113549 : Blo 1190412 6113549 := bstep (se 3 (by rfl) ⟨1146290, by rfl⟩ : syracuseStep 6113549 = 2292581) B2292581
theorem B1788179 : Blo 1190412 1788179 := bstep (se 1 (by rfl) ⟨1341134, by rfl⟩ : syracuseStep 1788179 = 2682269) B2682269
theorem B1788209 : Blo 1190412 1788209 := bstep (se 2 (by rfl) ⟨670578, by rfl⟩ : syracuseStep 1788209 = 1341157) B1341157
theorem B3017027 : Blo 1190412 3017027 := bstep (se 1 (by rfl) ⟨2262770, by rfl⟩ : syracuseStep 3017027 = 4525541) B4525541
theorem B1788227 : Blo 1190412 1788227 := bstep (se 1 (by rfl) ⟨1341170, by rfl⟩ : syracuseStep 1788227 = 2682341) B2682341
theorem B2009441 : Blo 1190412 2009441 := bstep (se 2 (by rfl) ⟨753540, by rfl⟩ : syracuseStep 2009441 = 1507081) B1507081
theorem B1788257 : Blo 1190412 1788257 := bstep (se 2 (by rfl) ⟨670596, by rfl⟩ : syracuseStep 1788257 = 1341193) B1341193
theorem B5581169 : Blo 1190412 5581169 := bstep (se 2 (by rfl) ⟨2092938, by rfl⟩ : syracuseStep 5581169 = 4185877) B4185877
theorem B23841137 : Blo 1190412 23841137 := bstep (se 2 (by rfl) ⟨8940426, by rfl⟩ : syracuseStep 23841137 = 17880853) B17880853
theorem B1788275 : Blo 1190412 1788275 := bstep (se 1 (by rfl) ⟨1341206, by rfl⟩ : syracuseStep 1788275 = 2682413) B2682413
theorem B10185101 : Blo 1190412 10185101 := bstep (se 3 (by rfl) ⟨1909706, by rfl⟩ : syracuseStep 10185101 = 3819413) B3819413
theorem B1788305 : Blo 1190412 1788305 := bstep (se 2 (by rfl) ⟨670614, by rfl⟩ : syracuseStep 1788305 = 1341229) B1341229
theorem B1788323 : Blo 1190412 1788323 := bstep (se 1 (by rfl) ⟨1341242, by rfl⟩ : syracuseStep 1788323 = 2682485) B2682485
theorem B1788353 : Blo 1190412 1788353 := bstep (se 2 (by rfl) ⟨670632, by rfl⟩ : syracuseStep 1788353 = 1341265) B1341265
theorem B2681297 : Blo 1190412 2681297 := bstep (se 2 (by rfl) ⟨1005486, by rfl⟩ : syracuseStep 2681297 = 2010973) B2010973
theorem B1788371 : Blo 1190412 1788371 := bstep (se 1 (by rfl) ⟨1341278, by rfl⟩ : syracuseStep 1788371 = 2682557) B2682557
theorem B2009569 : Blo 1190412 2009569 := bstep (se 2 (by rfl) ⟨753588, by rfl⟩ : syracuseStep 2009569 = 1507177) B1507177
theorem B2681315 : Blo 1190412 2681315 := bstep (se 1 (by rfl) ⟨2010986, by rfl⟩ : syracuseStep 2681315 = 4021973) B4021973
theorem B1788401 : Blo 1190412 1788401 := bstep (se 2 (by rfl) ⟨670650, by rfl⟩ : syracuseStep 1788401 = 1341301) B1341301
theorem B1812979 : Blo 1190412 1812979 := bstep (se 1 (by rfl) ⟨1359734, by rfl⟩ : syracuseStep 1812979 = 2719469) B2719469
theorem B2009603 : Blo 1190412 2009603 := bstep (se 1 (by rfl) ⟨1507202, by rfl⟩ : syracuseStep 2009603 = 3014405) B3014405
theorem B1788419 : Blo 1190412 1788419 := bstep (se 1 (by rfl) ⟨1341314, by rfl⟩ : syracuseStep 1788419 = 2682629) B2682629
theorem B1190419 : Blo 1190412 1190419 := bstep (se 1 (by rfl) ⟨892814, by rfl⟩ : syracuseStep 1190419 = 1785629) B1785629
theorem B1788449 : Blo 1190412 1788449 := bstep (se 2 (by rfl) ⟨670668, by rfl⟩ : syracuseStep 1788449 = 1341337) B1341337
theorem B1190435 : Blo 1190412 1190435 := bstep (se 1 (by rfl) ⟨892826, by rfl⟩ : syracuseStep 1190435 = 1785653) B1785653
theorem B6031907 : Blo 1190412 6031907 := bstep (se 1 (by rfl) ⟨4523930, by rfl⟩ : syracuseStep 6031907 = 9047861) B9047861
theorem B1190451 : Blo 1190412 1190451 := bstep (se 1 (by rfl) ⟨892838, by rfl⟩ : syracuseStep 1190451 = 1785677) B1785677
theorem B1788467 : Blo 1190412 1788467 := bstep (se 1 (by rfl) ⟨1341350, by rfl⟩ : syracuseStep 1788467 = 2682701) B2682701
theorem B1190467 : Blo 1190412 1190467 := bstep (se 1 (by rfl) ⟨892850, by rfl⟩ : syracuseStep 1190467 = 1785701) B1785701
theorem B1788497 : Blo 1190412 1788497 := bstep (se 2 (by rfl) ⟨670686, by rfl⟩ : syracuseStep 1788497 = 1341373) B1341373
theorem B1190483 : Blo 1190412 1190483 := bstep (se 1 (by rfl) ⟨892862, by rfl⟩ : syracuseStep 1190483 = 1785725) B1785725
theorem B1190499 : Blo 1190412 1190499 := bstep (se 1 (by rfl) ⟨892874, by rfl⟩ : syracuseStep 1190499 = 1785749) B1785749
theorem B1788515 : Blo 1190412 1788515 := bstep (se 1 (by rfl) ⟨1341386, by rfl⟩ : syracuseStep 1788515 = 2682773) B2682773
theorem B1190515 : Blo 1190412 1190515 := bstep (se 1 (by rfl) ⟨892886, by rfl⟩ : syracuseStep 1190515 = 1785773) B1785773
theorem B1788545 : Blo 1190412 1788545 := bstep (se 2 (by rfl) ⟨670704, by rfl⟩ : syracuseStep 1788545 = 1341409) B1341409
theorem B1190531 : Blo 1190412 1190531 := bstep (se 1 (by rfl) ⟨892898, by rfl⟩ : syracuseStep 1190531 = 1785797) B1785797
theorem B2009731 : Blo 1190412 2009731 := bstep (se 1 (by rfl) ⟨1507298, by rfl⟩ : syracuseStep 2009731 = 3014597) B3014597
theorem B2263697 : Blo 1190412 2263697 := bstep (se 2 (by rfl) ⟨848886, by rfl⟩ : syracuseStep 2263697 = 1697773) B1697773
theorem B1190547 : Blo 1190412 1190547 := bstep (se 1 (by rfl) ⟨892910, by rfl⟩ : syracuseStep 1190547 = 1785821) B1785821
theorem B1272467 : Blo 1190412 1272467 := bstep (se 1 (by rfl) ⟨954350, by rfl⟩ : syracuseStep 1272467 = 1908701) B1908701
theorem B1788563 : Blo 1190412 1788563 := bstep (se 1 (by rfl) ⟨1341422, by rfl⟩ : syracuseStep 1788563 = 2682845) B2682845
theorem B1190563 : Blo 1190412 1190563 := bstep (se 1 (by rfl) ⟨892922, by rfl⟩ : syracuseStep 1190563 = 1785845) B1785845
theorem B5089969 : Blo 1190412 5089969 := bstep (se 2 (by rfl) ⟨1908738, by rfl⟩ : syracuseStep 5089969 = 3817477) B3817477
theorem B1190579 : Blo 1190412 1190579 := bstep (se 1 (by rfl) ⟨892934, by rfl⟩ : syracuseStep 1190579 = 1785869) B1785869
theorem B1788593 : Blo 1190412 1788593 := bstep (se 2 (by rfl) ⟨670722, by rfl⟩ : syracuseStep 1788593 = 1341445) B1341445
theorem B1190595 : Blo 1190412 1190595 := bstep (se 1 (by rfl) ⟨892946, by rfl⟩ : syracuseStep 1190595 = 1785893) B1785893
theorem B1788611 : Blo 1190412 1788611 := bstep (se 1 (by rfl) ⟨1341458, by rfl⟩ : syracuseStep 1788611 = 2682917) B2682917
theorem B1190611 : Blo 1190412 1190611 := bstep (se 1 (by rfl) ⟨892958, by rfl⟩ : syracuseStep 1190611 = 1785917) B1785917
theorem B1190627 : Blo 1190412 1190627 := bstep (se 1 (by rfl) ⟨892970, by rfl⟩ : syracuseStep 1190627 = 1785941) B1785941
theorem B10865393 : Blo 1190412 10865393 := bstep (se 2 (by rfl) ⟨4074522, by rfl⟩ : syracuseStep 10865393 = 8149045) B8149045
theorem B2681585 : Blo 1190412 2681585 := bstep (se 2 (by rfl) ⟨1005594, by rfl⟩ : syracuseStep 2681585 = 2011189) B2011189
theorem B1190643 : Blo 1190412 1190643 := bstep (se 1 (by rfl) ⟨892982, by rfl⟩ : syracuseStep 1190643 = 1785965) B1785965
theorem B1190659 : Blo 1190412 1190659 := bstep (se 1 (by rfl) ⟨892994, by rfl⟩ : syracuseStep 1190659 = 1785989) B1785989
theorem B2681603 : Blo 1190412 2681603 := bstep (se 1 (by rfl) ⟨2011202, by rfl⟩ : syracuseStep 2681603 = 4022405) B4022405
theorem B2009873 : Blo 1190412 2009873 := bstep (se 2 (by rfl) ⟨753702, by rfl⟩ : syracuseStep 2009873 = 1507405) B1507405
theorem B1190675 : Blo 1190412 1190675 := bstep (se 1 (by rfl) ⟨893006, by rfl⟩ : syracuseStep 1190675 = 1786013) B1786013
theorem B1272595 : Blo 1190412 1272595 := bstep (se 1 (by rfl) ⟨954446, by rfl⟩ : syracuseStep 1272595 = 1908893) B1908893
theorem B1190691 : Blo 1190412 1190691 := bstep (se 1 (by rfl) ⟨893018, by rfl⟩ : syracuseStep 1190691 = 1786037) B1786037
theorem B3222317 : Blo 1190412 3222317 := bstep (se 3 (by rfl) ⟨604184, by rfl⟩ : syracuseStep 3222317 = 1208369) B1208369
theorem B1190707 : Blo 1190412 1190707 := bstep (se 1 (by rfl) ⟨893030, by rfl⟩ : syracuseStep 1190707 = 1786061) B1786061
theorem B1190723 : Blo 1190412 1190723 := bstep (se 1 (by rfl) ⟨893042, by rfl⟩ : syracuseStep 1190723 = 1786085) B1786085
theorem B4295501 : Blo 1190412 4295501 := bstep (se 3 (by rfl) ⟨805406, by rfl⟩ : syracuseStep 4295501 = 1610813) B1610813
theorem B1190739 : Blo 1190412 1190739 := bstep (se 1 (by rfl) ⟨893054, by rfl⟩ : syracuseStep 1190739 = 1786109) B1786109
theorem B1190755 : Blo 1190412 1190755 := bstep (se 1 (by rfl) ⟨893066, by rfl⟩ : syracuseStep 1190755 = 1786133) B1786133
theorem B1190771 : Blo 1190412 1190771 := bstep (se 1 (by rfl) ⟨893078, by rfl⟩ : syracuseStep 1190771 = 1786157) B1786157
theorem B1190787 : Blo 1190412 1190787 := bstep (se 1 (by rfl) ⟨893090, by rfl⟩ : syracuseStep 1190787 = 1786181) B1786181
theorem B2010001 : Blo 1190412 2010001 := bstep (se 2 (by rfl) ⟨753750, by rfl⟩ : syracuseStep 2010001 = 1507501) B1507501
theorem B1190803 : Blo 1190412 1190803 := bstep (se 1 (by rfl) ⟨893102, by rfl⟩ : syracuseStep 1190803 = 1786205) B1786205
theorem B1190819 : Blo 1190412 1190819 := bstep (se 1 (by rfl) ⟨893114, by rfl⟩ : syracuseStep 1190819 = 1786229) B1786229
theorem B1190835 : Blo 1190412 1190835 := bstep (se 1 (by rfl) ⟨893126, by rfl⟩ : syracuseStep 1190835 = 1786253) B1786253
theorem B2010035 : Blo 1190412 2010035 := bstep (se 1 (by rfl) ⟨1507526, by rfl⟩ : syracuseStep 2010035 = 3015053) B3015053
theorem B1190851 : Blo 1190412 1190851 := bstep (se 1 (by rfl) ⟨893138, by rfl⟩ : syracuseStep 1190851 = 1786277) B1786277
theorem B1190867 : Blo 1190412 1190867 := bstep (se 1 (by rfl) ⟨893150, by rfl⟩ : syracuseStep 1190867 = 1786301) B1786301
theorem B1190883 : Blo 1190412 1190883 := bstep (se 1 (by rfl) ⟨893162, by rfl⟩ : syracuseStep 1190883 = 1786325) B1786325
theorem B1190899 : Blo 1190412 1190899 := bstep (se 1 (by rfl) ⟨893174, by rfl⟩ : syracuseStep 1190899 = 1786349) B1786349
theorem B1190915 : Blo 1190412 1190915 := bstep (se 1 (by rfl) ⟨893186, by rfl⟩ : syracuseStep 1190915 = 1786373) B1786373
theorem B2681873 : Blo 1190412 2681873 := bstep (se 2 (by rfl) ⟨1005702, by rfl⟩ : syracuseStep 2681873 = 2011405) B2011405
theorem B1190931 : Blo 1190412 1190931 := bstep (se 1 (by rfl) ⟨893198, by rfl⟩ : syracuseStep 1190931 = 1786397) B1786397
theorem B2542627 : Blo 1190412 2542627 := bstep (se 1 (by rfl) ⟨1906970, by rfl⟩ : syracuseStep 2542627 = 3813941) B3813941
theorem B1190947 : Blo 1190412 1190947 := bstep (se 1 (by rfl) ⟨893210, by rfl⟩ : syracuseStep 1190947 = 1786421) B1786421
theorem B2681891 : Blo 1190412 2681891 := bstep (se 1 (by rfl) ⟨2011418, by rfl⟩ : syracuseStep 2681891 = 4022837) B4022837
theorem B1190963 : Blo 1190412 1190963 := bstep (se 1 (by rfl) ⟨893222, by rfl⟩ : syracuseStep 1190963 = 1786445) B1786445
theorem B2010163 : Blo 1190412 2010163 := bstep (se 1 (by rfl) ⟨1507622, by rfl⟩ : syracuseStep 2010163 = 3015245) B3015245
theorem B1190979 : Blo 1190412 1190979 := bstep (se 1 (by rfl) ⟨893234, by rfl⟩ : syracuseStep 1190979 = 1786469) B1786469
theorem B6786125 : Blo 1190412 6786125 := bstep (se 3 (by rfl) ⟨1272398, by rfl⟩ : syracuseStep 6786125 = 2544797) B2544797
theorem B1190995 : Blo 1190412 1190995 := bstep (se 1 (by rfl) ⟨893246, by rfl⟩ : syracuseStep 1190995 = 1786493) B1786493
theorem B1191011 : Blo 1190412 1191011 := bstep (se 1 (by rfl) ⟨893258, by rfl⟩ : syracuseStep 1191011 = 1786517) B1786517
theorem B3394669 : Blo 1190412 3394669 := bstep (se 3 (by rfl) ⟨636500, by rfl⟩ : syracuseStep 3394669 = 1273001) B1273001
theorem B1191027 : Blo 1190412 1191027 := bstep (se 1 (by rfl) ⟨893270, by rfl⟩ : syracuseStep 1191027 = 1786541) B1786541
theorem B1191043 : Blo 1190412 1191043 := bstep (se 1 (by rfl) ⟨893282, by rfl⟩ : syracuseStep 1191043 = 1786565) B1786565
theorem B1191059 : Blo 1190412 1191059 := bstep (se 1 (by rfl) ⟨893294, by rfl⟩ : syracuseStep 1191059 = 1786589) B1786589
theorem B1191075 : Blo 1190412 1191075 := bstep (se 1 (by rfl) ⟨893306, by rfl⟩ : syracuseStep 1191075 = 1786613) B1786613
theorem B7244963 : Blo 1190412 7244963 := bstep (se 1 (by rfl) ⟨5433722, by rfl⟩ : syracuseStep 7244963 = 10867445) B10867445
theorem B1191091 : Blo 1190412 1191091 := bstep (se 1 (by rfl) ⟨893318, by rfl⟩ : syracuseStep 1191091 = 1786637) B1786637
theorem B2010305 : Blo 1190412 2010305 := bstep (se 2 (by rfl) ⟨753864, by rfl⟩ : syracuseStep 2010305 = 1507729) B1507729
theorem B1191107 : Blo 1190412 1191107 := bstep (se 1 (by rfl) ⟨893330, by rfl⟩ : syracuseStep 1191107 = 1786661) B1786661
theorem B1191123 : Blo 1190412 1191123 := bstep (se 1 (by rfl) ⟨893342, by rfl⟩ : syracuseStep 1191123 = 1786685) B1786685
theorem B1191139 : Blo 1190412 1191139 := bstep (se 1 (by rfl) ⟨893354, by rfl⟩ : syracuseStep 1191139 = 1786709) B1786709
theorem B3017969 : Blo 1190412 3017969 := bstep (se 2 (by rfl) ⟨1131738, by rfl⟩ : syracuseStep 3017969 = 2263477) B2263477
theorem B1191155 : Blo 1190412 1191155 := bstep (se 1 (by rfl) ⟨893366, by rfl⟩ : syracuseStep 1191155 = 1786733) B1786733
theorem B1191171 : Blo 1190412 1191171 := bstep (se 1 (by rfl) ⟨893378, by rfl⟩ : syracuseStep 1191171 = 1786757) B1786757
theorem B1191187 : Blo 1190412 1191187 := bstep (se 1 (by rfl) ⟨893390, by rfl⟩ : syracuseStep 1191187 = 1786781) B1786781
theorem B1191203 : Blo 1190412 1191203 := bstep (se 1 (by rfl) ⟨893402, by rfl⟩ : syracuseStep 1191203 = 1786805) B1786805
theorem B3018019 : Blo 1190412 3018019 := bstep (se 1 (by rfl) ⟨2263514, by rfl⟩ : syracuseStep 3018019 = 4527029) B4527029
theorem B2682161 : Blo 1190412 2682161 := bstep (se 2 (by rfl) ⟨1005810, by rfl⟩ : syracuseStep 2682161 = 2011621) B2011621
theorem B1191219 : Blo 1190412 1191219 := bstep (se 1 (by rfl) ⟨893414, by rfl⟩ : syracuseStep 1191219 = 1786829) B1786829
theorem B2010433 : Blo 1190412 2010433 := bstep (se 2 (by rfl) ⟨753912, by rfl⟩ : syracuseStep 2010433 = 1507825) B1507825
theorem B1191235 : Blo 1190412 1191235 := bstep (se 1 (by rfl) ⟨893426, by rfl⟩ : syracuseStep 1191235 = 1786853) B1786853
theorem B2682179 : Blo 1190412 2682179 := bstep (se 1 (by rfl) ⟨2011634, by rfl⟩ : syracuseStep 2682179 = 4023269) B4023269
theorem B6032717 : Blo 1190412 6032717 := bstep (se 3 (by rfl) ⟨1131134, by rfl⟩ : syracuseStep 6032717 = 2262269) B2262269
theorem B1191251 : Blo 1190412 1191251 := bstep (se 1 (by rfl) ⟨893438, by rfl⟩ : syracuseStep 1191251 = 1786877) B1786877
theorem B1191267 : Blo 1190412 1191267 := bstep (se 1 (by rfl) ⟨893450, by rfl⟩ : syracuseStep 1191267 = 1786901) B1786901
theorem B2010467 : Blo 1190412 2010467 := bstep (se 1 (by rfl) ⟨1507850, by rfl⟩ : syracuseStep 2010467 = 3015701) B3015701
theorem B1191283 : Blo 1190412 1191283 := bstep (se 1 (by rfl) ⟨893462, by rfl⟩ : syracuseStep 1191283 = 1786925) B1786925
theorem B1191299 : Blo 1190412 1191299 := bstep (se 1 (by rfl) ⟨893474, by rfl⟩ : syracuseStep 1191299 = 1786949) B1786949
theorem B1191315 : Blo 1190412 1191315 := bstep (se 1 (by rfl) ⟨893486, by rfl⟩ : syracuseStep 1191315 = 1786973) B1786973
theorem B1191331 : Blo 1190412 1191331 := bstep (se 1 (by rfl) ⟨893498, by rfl⟩ : syracuseStep 1191331 = 1786997) B1786997
theorem B3018161 : Blo 1190412 3018161 := bstep (se 2 (by rfl) ⟨1131810, by rfl⟩ : syracuseStep 3018161 = 2263621) B2263621
theorem B1191347 : Blo 1190412 1191347 := bstep (se 1 (by rfl) ⟨893510, by rfl⟩ : syracuseStep 1191347 = 1787021) B1787021
theorem B1191363 : Blo 1190412 1191363 := bstep (se 1 (by rfl) ⟨893522, by rfl⟩ : syracuseStep 1191363 = 1787045) B1787045
theorem B3624401 : Blo 1190412 3624401 := bstep (se 2 (by rfl) ⟨1359150, by rfl⟩ : syracuseStep 3624401 = 2718301) B2718301
theorem B1191379 : Blo 1190412 1191379 := bstep (se 1 (by rfl) ⟨893534, by rfl⟩ : syracuseStep 1191379 = 1787069) B1787069
theorem B1191395 : Blo 1190412 1191395 := bstep (se 1 (by rfl) ⟨893546, by rfl⟩ : syracuseStep 1191395 = 1787093) B1787093
theorem B2010595 : Blo 1190412 2010595 := bstep (se 1 (by rfl) ⟨1507946, by rfl⟩ : syracuseStep 2010595 = 3015893) B3015893
theorem B1609201 : Blo 1190412 1609201 := bstep (se 2 (by rfl) ⟨603450, by rfl⟩ : syracuseStep 1609201 = 1206901) B1206901
theorem B2543089 : Blo 1190412 2543089 := bstep (se 2 (by rfl) ⟨953658, by rfl⟩ : syracuseStep 2543089 = 1907317) B1907317
theorem B1191411 : Blo 1190412 1191411 := bstep (se 1 (by rfl) ⟨893558, by rfl⟩ : syracuseStep 1191411 = 1787117) B1787117
theorem B1191427 : Blo 1190412 1191427 := bstep (se 1 (by rfl) ⟨893570, by rfl⟩ : syracuseStep 1191427 = 1787141) B1787141
theorem B1191443 : Blo 1190412 1191443 := bstep (se 1 (by rfl) ⟨893582, by rfl⟩ : syracuseStep 1191443 = 1787165) B1787165
theorem B1191459 : Blo 1190412 1191459 := bstep (se 1 (by rfl) ⟨893594, by rfl⟩ : syracuseStep 1191459 = 1787189) B1787189
theorem B1191475 : Blo 1190412 1191475 := bstep (se 1 (by rfl) ⟨893606, by rfl⟩ : syracuseStep 1191475 = 1787213) B1787213
theorem B1191491 : Blo 1190412 1191491 := bstep (se 1 (by rfl) ⟨893618, by rfl⟩ : syracuseStep 1191491 = 1787237) B1787237
theorem B13569605 : Blo 1190412 13569605 := bstep (se 4 (by rfl) ⟨1272150, by rfl⟩ : syracuseStep 13569605 = 2544301) B2544301
theorem B2682449 : Blo 1190412 2682449 := bstep (se 2 (by rfl) ⟨1005918, by rfl⟩ : syracuseStep 2682449 = 2011837) B2011837
theorem B1191507 : Blo 1190412 1191507 := bstep (se 1 (by rfl) ⟨893630, by rfl⟩ : syracuseStep 1191507 = 1787261) B1787261
theorem B4828771 : Blo 1190412 4828771 := bstep (se 1 (by rfl) ⟨3621578, by rfl⟩ : syracuseStep 4828771 = 7243157) B7243157
theorem B1191523 : Blo 1190412 1191523 := bstep (se 1 (by rfl) ⟨893642, by rfl⟩ : syracuseStep 1191523 = 1787285) B1787285
theorem B2682467 : Blo 1190412 2682467 := bstep (se 1 (by rfl) ⟨2011850, by rfl⟩ : syracuseStep 2682467 = 4023701) B4023701
theorem B2010737 : Blo 1190412 2010737 := bstep (se 2 (by rfl) ⟨754026, by rfl⟩ : syracuseStep 2010737 = 1508053) B1508053
theorem B1191539 : Blo 1190412 1191539 := bstep (se 1 (by rfl) ⟨893654, by rfl⟩ : syracuseStep 1191539 = 1787309) B1787309
theorem B4075139 : Blo 1190412 4075139 := bstep (se 1 (by rfl) ⟨3056354, by rfl⟩ : syracuseStep 4075139 = 6112709) B6112709
theorem B1191555 : Blo 1190412 1191555 := bstep (se 1 (by rfl) ⟨893666, by rfl⟩ : syracuseStep 1191555 = 1787333) B1787333
theorem B1191571 : Blo 1190412 1191571 := bstep (se 1 (by rfl) ⟨893678, by rfl⟩ : syracuseStep 1191571 = 1787357) B1787357
theorem B1191587 : Blo 1190412 1191587 := bstep (se 1 (by rfl) ⟨893690, by rfl⟩ : syracuseStep 1191587 = 1787381) B1787381
theorem B1191603 : Blo 1190412 1191603 := bstep (se 1 (by rfl) ⟨893702, by rfl⟩ : syracuseStep 1191603 = 1787405) B1787405
theorem B1191619 : Blo 1190412 1191619 := bstep (se 1 (by rfl) ⟨893714, by rfl⟩ : syracuseStep 1191619 = 1787429) B1787429
theorem B4017869 : Blo 1190412 4017869 := bstep (se 3 (by rfl) ⟨753350, by rfl⟩ : syracuseStep 4017869 = 1506701) B1506701
theorem B1191635 : Blo 1190412 1191635 := bstep (se 1 (by rfl) ⟨893726, by rfl⟩ : syracuseStep 1191635 = 1787453) B1787453
theorem B1224403 : Blo 1190412 1224403 := bstep (se 1 (by rfl) ⟨918302, by rfl⟩ : syracuseStep 1224403 = 1836605) B1836605
theorem B1191651 : Blo 1190412 1191651 := bstep (se 1 (by rfl) ⟨893738, by rfl⟩ : syracuseStep 1191651 = 1787477) B1787477
theorem B1224419 : Blo 1190412 1224419 := bstep (se 1 (by rfl) ⟨918314, by rfl⟩ : syracuseStep 1224419 = 1836629) B1836629
theorem B2010865 : Blo 1190412 2010865 := bstep (se 2 (by rfl) ⟨754074, by rfl⟩ : syracuseStep 2010865 = 1508149) B1508149
theorem B1191667 : Blo 1190412 1191667 := bstep (se 1 (by rfl) ⟨893750, by rfl⟩ : syracuseStep 1191667 = 1787501) B1787501
theorem B4017923 : Blo 1190412 4017923 := bstep (se 1 (by rfl) ⟨3013442, by rfl⟩ : syracuseStep 4017923 = 6026885) B6026885
theorem B1191683 : Blo 1190412 1191683 := bstep (se 1 (by rfl) ⟨893762, by rfl⟩ : syracuseStep 1191683 = 1787525) B1787525
theorem B2010899 : Blo 1190412 2010899 := bstep (se 1 (by rfl) ⟨1508174, by rfl⟩ : syracuseStep 2010899 = 3016349) B3016349
theorem B1191699 : Blo 1190412 1191699 := bstep (se 1 (by rfl) ⟨893774, by rfl⟩ : syracuseStep 1191699 = 1787549) B1787549
theorem B1191715 : Blo 1190412 1191715 := bstep (se 1 (by rfl) ⟨893786, by rfl⟩ : syracuseStep 1191715 = 1787573) B1787573
theorem B1191731 : Blo 1190412 1191731 := bstep (se 1 (by rfl) ⟨893798, by rfl⟩ : syracuseStep 1191731 = 1787597) B1787597
theorem B1191747 : Blo 1190412 1191747 := bstep (se 1 (by rfl) ⟨893810, by rfl⟩ : syracuseStep 1191747 = 1787621) B1787621
theorem B2715473 : Blo 1190412 2715473 := bstep (se 2 (by rfl) ⟨1018302, by rfl⟩ : syracuseStep 2715473 = 2036605) B2036605
theorem B1191763 : Blo 1190412 1191763 := bstep (se 1 (by rfl) ⟨893822, by rfl⟩ : syracuseStep 1191763 = 1787645) B1787645
theorem B2715491 : Blo 1190412 2715491 := bstep (se 1 (by rfl) ⟨2036618, by rfl⟩ : syracuseStep 2715491 = 4073237) B4073237
theorem B1191779 : Blo 1190412 1191779 := bstep (se 1 (by rfl) ⟨893834, by rfl⟩ : syracuseStep 1191779 = 1787669) B1787669
theorem B2682737 : Blo 1190412 2682737 := bstep (se 2 (by rfl) ⟨1006026, by rfl⟩ : syracuseStep 2682737 = 2012053) B2012053
theorem B1191795 : Blo 1190412 1191795 := bstep (se 1 (by rfl) ⟨893846, by rfl⟩ : syracuseStep 1191795 = 1787693) B1787693
theorem B1339267 : Blo 1190412 1339267 := bstep (se 1 (by rfl) ⟨1004450, by rfl⟩ : syracuseStep 1339267 = 2008901) B2008901
theorem B1191811 : Blo 1190412 1191811 := bstep (se 1 (by rfl) ⟨893858, by rfl⟩ : syracuseStep 1191811 = 1787717) B1787717
theorem B2682755 : Blo 1190412 2682755 := bstep (se 1 (by rfl) ⟨2012066, by rfl⟩ : syracuseStep 2682755 = 4024133) B4024133
theorem B2011027 : Blo 1190412 2011027 := bstep (se 1 (by rfl) ⟨1508270, by rfl⟩ : syracuseStep 2011027 = 3016541) B3016541
theorem B1191827 : Blo 1190412 1191827 := bstep (se 1 (by rfl) ⟨893870, by rfl⟩ : syracuseStep 1191827 = 1787741) B1787741
theorem B1191843 : Blo 1190412 1191843 := bstep (se 1 (by rfl) ⟨893882, by rfl⟩ : syracuseStep 1191843 = 1787765) B1787765
theorem B1191859 : Blo 1190412 1191859 := bstep (se 1 (by rfl) ⟨893894, by rfl⟩ : syracuseStep 1191859 = 1787789) B1787789
theorem B1191875 : Blo 1190412 1191875 := bstep (se 1 (by rfl) ⟨893906, by rfl⟩ : syracuseStep 1191875 = 1787813) B1787813
theorem B36671429 : Blo 1190412 36671429 := bstep (se 4 (by rfl) ⟨3437946, by rfl⟩ : syracuseStep 36671429 = 6875893) B6875893
theorem B2715601 : Blo 1190412 2715601 := bstep (se 2 (by rfl) ⟨1018350, by rfl⟩ : syracuseStep 2715601 = 2036701) B2036701
theorem B1191891 : Blo 1190412 1191891 := bstep (se 1 (by rfl) ⟨893918, by rfl⟩ : syracuseStep 1191891 = 1787837) B1787837
theorem B1609699 : Blo 1190412 1609699 := bstep (se 1 (by rfl) ⟨1207274, by rfl⟩ : syracuseStep 1609699 = 2414549) B2414549
theorem B1191907 : Blo 1190412 1191907 := bstep (se 1 (by rfl) ⟨893930, by rfl⟩ : syracuseStep 1191907 = 1787861) B1787861
theorem B1191923 : Blo 1190412 1191923 := bstep (se 1 (by rfl) ⟨893942, by rfl⟩ : syracuseStep 1191923 = 1787885) B1787885
theorem B1191939 : Blo 1190412 1191939 := bstep (se 1 (by rfl) ⟨893954, by rfl⟩ : syracuseStep 1191939 = 1787909) B1787909
theorem B4018193 : Blo 1190412 4018193 := bstep (se 2 (by rfl) ⟨1506822, by rfl⟩ : syracuseStep 4018193 = 3013645) B3013645
theorem B1339411 : Blo 1190412 1339411 := bstep (se 1 (by rfl) ⟨1004558, by rfl⟩ : syracuseStep 1339411 = 2009117) B2009117
theorem B1191955 : Blo 1190412 1191955 := bstep (se 1 (by rfl) ⟨893966, by rfl⟩ : syracuseStep 1191955 = 1787933) B1787933
theorem B2011169 : Blo 1190412 2011169 := bstep (se 2 (by rfl) ⟨754188, by rfl⟩ : syracuseStep 2011169 = 1508377) B1508377
theorem B1609763 : Blo 1190412 1609763 := bstep (se 1 (by rfl) ⟨1207322, by rfl⟩ : syracuseStep 1609763 = 2414645) B2414645
theorem B1191971 : Blo 1190412 1191971 := bstep (se 1 (by rfl) ⟨893978, by rfl⟩ : syracuseStep 1191971 = 1787957) B1787957
theorem B1191987 : Blo 1190412 1191987 := bstep (se 1 (by rfl) ⟨893990, by rfl⟩ : syracuseStep 1191987 = 1787981) B1787981
theorem B1192003 : Blo 1190412 1192003 := bstep (se 1 (by rfl) ⟨894002, by rfl⟩ : syracuseStep 1192003 = 1788005) B1788005
theorem B7639109 : Blo 1190412 7639109 := bstep (se 4 (by rfl) ⟨716166, by rfl⟩ : syracuseStep 7639109 = 1432333) B1432333
theorem B1192019 : Blo 1190412 1192019 := bstep (se 1 (by rfl) ⟨894014, by rfl⟩ : syracuseStep 1192019 = 1788029) B1788029
theorem B1192035 : Blo 1190412 1192035 := bstep (se 1 (by rfl) ⟨894026, by rfl⟩ : syracuseStep 1192035 = 1788053) B1788053
theorem B13578353 : Blo 1190412 13578353 := bstep (se 2 (by rfl) ⟨5091882, by rfl⟩ : syracuseStep 13578353 = 10183765) B10183765
theorem B1192051 : Blo 1190412 1192051 := bstep (se 1 (by rfl) ⟨894038, by rfl⟩ : syracuseStep 1192051 = 1788077) B1788077
theorem B1192067 : Blo 1190412 1192067 := bstep (se 1 (by rfl) ⟨894050, by rfl⟩ : syracuseStep 1192067 = 1788101) B1788101
theorem B1192083 : Blo 1190412 1192083 := bstep (se 1 (by rfl) ⟨894062, by rfl⟩ : syracuseStep 1192083 = 1788125) B1788125
theorem B2011297 : Blo 1190412 2011297 := bstep (se 2 (by rfl) ⟨754236, by rfl⟩ : syracuseStep 2011297 = 1508473) B1508473
theorem B1339555 : Blo 1190412 1339555 := bstep (se 1 (by rfl) ⟨1004666, by rfl⟩ : syracuseStep 1339555 = 2009333) B2009333
theorem B1192099 : Blo 1190412 1192099 := bstep (se 1 (by rfl) ⟨894074, by rfl⟩ : syracuseStep 1192099 = 1788149) B1788149
theorem B1192115 : Blo 1190412 1192115 := bstep (se 1 (by rfl) ⟨894086, by rfl⟩ : syracuseStep 1192115 = 1788173) B1788173
theorem B2011331 : Blo 1190412 2011331 := bstep (se 1 (by rfl) ⟨1508498, by rfl⟩ : syracuseStep 2011331 = 3016997) B3016997
theorem B1192131 : Blo 1190412 1192131 := bstep (se 1 (by rfl) ⟨894098, by rfl⟩ : syracuseStep 1192131 = 1788197) B1788197
theorem B1192147 : Blo 1190412 1192147 := bstep (se 1 (by rfl) ⟨894110, by rfl⟩ : syracuseStep 1192147 = 1788221) B1788221
theorem B1192163 : Blo 1190412 1192163 := bstep (se 1 (by rfl) ⟨894122, by rfl⟩ : syracuseStep 1192163 = 1788245) B1788245
theorem B1192179 : Blo 1190412 1192179 := bstep (se 1 (by rfl) ⟨894134, by rfl⟩ : syracuseStep 1192179 = 1788269) B1788269
theorem B1192195 : Blo 1190412 1192195 := bstep (se 1 (by rfl) ⟨894146, by rfl⟩ : syracuseStep 1192195 = 1788293) B1788293
theorem B1192211 : Blo 1190412 1192211 := bstep (se 1 (by rfl) ⟨894158, by rfl⟩ : syracuseStep 1192211 = 1788317) B1788317
theorem B1192227 : Blo 1190412 1192227 := bstep (se 1 (by rfl) ⟨894170, by rfl⟩ : syracuseStep 1192227 = 1788341) B1788341
theorem B4829489 : Blo 1190412 4829489 := bstep (se 2 (by rfl) ⟨1811058, by rfl⟩ : syracuseStep 4829489 = 3622117) B3622117
theorem B1339699 : Blo 1190412 1339699 := bstep (se 1 (by rfl) ⟨1004774, by rfl⟩ : syracuseStep 1339699 = 2009549) B2009549
theorem B1192243 : Blo 1190412 1192243 := bstep (se 1 (by rfl) ⟨894182, by rfl⟩ : syracuseStep 1192243 = 1788365) B1788365
theorem B20369717 : Blo 1190412 20369717 := bstep (se 5 (by rfl) ⟨954830, by rfl⟩ : syracuseStep 20369717 = 1909661) B1909661
theorem B2011459 : Blo 1190412 2011459 := bstep (se 1 (by rfl) ⟨1508594, by rfl⟩ : syracuseStep 2011459 = 3017189) B3017189
theorem B1192259 : Blo 1190412 1192259 := bstep (se 1 (by rfl) ⟨894194, by rfl⟩ : syracuseStep 1192259 = 1788389) B1788389
theorem B1192275 : Blo 1190412 1192275 := bstep (se 1 (by rfl) ⟨894206, by rfl⟩ : syracuseStep 1192275 = 1788413) B1788413
theorem B1192291 : Blo 1190412 1192291 := bstep (se 1 (by rfl) ⟨894218, by rfl⟩ : syracuseStep 1192291 = 1788437) B1788437
theorem B3625325 : Blo 1190412 3625325 := bstep (se 3 (by rfl) ⟨679748, by rfl⟩ : syracuseStep 3625325 = 1359497) B1359497
theorem B15257969 : Blo 1190412 15257969 := bstep (se 2 (by rfl) ⟨5721738, by rfl⟩ : syracuseStep 15257969 = 11443477) B11443477
theorem B1192307 : Blo 1190412 1192307 := bstep (se 1 (by rfl) ⟨894230, by rfl⟩ : syracuseStep 1192307 = 1788461) B1788461
theorem B1192323 : Blo 1190412 1192323 := bstep (se 1 (by rfl) ⟨894242, by rfl⟩ : syracuseStep 1192323 = 1788485) B1788485
theorem B1192339 : Blo 1190412 1192339 := bstep (se 1 (by rfl) ⟨894254, by rfl⟩ : syracuseStep 1192339 = 1788509) B1788509
theorem B1192355 : Blo 1190412 1192355 := bstep (se 1 (by rfl) ⟨894266, by rfl⟩ : syracuseStep 1192355 = 1788533) B1788533
theorem B4526513 : Blo 1190412 4526513 := bstep (se 2 (by rfl) ⟨1697442, by rfl⟩ : syracuseStep 4526513 = 3394885) B3394885
theorem B1192371 : Blo 1190412 1192371 := bstep (se 1 (by rfl) ⟨894278, by rfl⟩ : syracuseStep 1192371 = 1788557) B1788557
theorem B1339843 : Blo 1190412 1339843 := bstep (se 1 (by rfl) ⟨1004882, by rfl⟩ : syracuseStep 1339843 = 2009765) B2009765
theorem B1192387 : Blo 1190412 1192387 := bstep (se 1 (by rfl) ⟨894290, by rfl⟩ : syracuseStep 1192387 = 1788581) B1788581
theorem B2011601 : Blo 1190412 2011601 := bstep (se 2 (by rfl) ⟨754350, by rfl⟩ : syracuseStep 2011601 = 1508701) B1508701
theorem B1192403 : Blo 1190412 1192403 := bstep (se 1 (by rfl) ⟨894302, by rfl⟩ : syracuseStep 1192403 = 1788605) B1788605
theorem B2544131 : Blo 1190412 2544131 := bstep (se 1 (by rfl) ⟨1908098, by rfl⟩ : syracuseStep 2544131 = 3816197) B3816197
theorem B4018733 : Blo 1190412 4018733 := bstep (se 3 (by rfl) ⟨753512, by rfl⟩ : syracuseStep 4018733 = 1507025) B1507025
theorem B2011729 : Blo 1190412 2011729 := bstep (se 2 (by rfl) ⟨754398, by rfl⟩ : syracuseStep 2011729 = 1508797) B1508797
theorem B1339987 : Blo 1190412 1339987 := bstep (se 1 (by rfl) ⟨1004990, by rfl⟩ : syracuseStep 1339987 = 2009981) B2009981
theorem B4018787 : Blo 1190412 4018787 := bstep (se 1 (by rfl) ⟨3014090, by rfl⟩ : syracuseStep 4018787 = 6028181) B6028181
theorem B4297315 : Blo 1190412 4297315 := bstep (se 1 (by rfl) ⟨3222986, by rfl⟩ : syracuseStep 4297315 = 6445973) B6445973
theorem B2011763 : Blo 1190412 2011763 := bstep (se 1 (by rfl) ⟨1508822, by rfl⟩ : syracuseStep 2011763 = 3017645) B3017645
theorem B1340131 : Blo 1190412 1340131 := bstep (se 1 (by rfl) ⟨1005098, by rfl⟩ : syracuseStep 1340131 = 2010197) B2010197
theorem B2011891 : Blo 1190412 2011891 := bstep (se 1 (by rfl) ⟨1508918, by rfl⟩ : syracuseStep 2011891 = 3017837) B3017837
theorem B4019057 : Blo 1190412 4019057 := bstep (se 2 (by rfl) ⟨1507146, by rfl⟩ : syracuseStep 4019057 = 3014293) B3014293
theorem B1340275 : Blo 1190412 1340275 := bstep (se 1 (by rfl) ⟨1005206, by rfl⟩ : syracuseStep 1340275 = 2010413) B2010413
theorem B2012033 : Blo 1190412 2012033 := bstep (se 2 (by rfl) ⟨754512, by rfl⟩ : syracuseStep 2012033 = 1509025) B1509025
theorem B2864099 : Blo 1190412 2864099 := bstep (se 1 (by rfl) ⟨2148074, by rfl⟩ : syracuseStep 2864099 = 4296149) B4296149
theorem B2012161 : Blo 1190412 2012161 := bstep (se 2 (by rfl) ⟨754560, by rfl⟩ : syracuseStep 2012161 = 1509121) B1509121
theorem B2544643 : Blo 1190412 2544643 := bstep (se 1 (by rfl) ⟨1908482, by rfl⟩ : syracuseStep 2544643 = 3816965) B3816965
theorem B1340419 : Blo 1190412 1340419 := bstep (se 1 (by rfl) ⟨1005314, by rfl⟩ : syracuseStep 1340419 = 2010629) B2010629
theorem B2036755 : Blo 1190412 2036755 := bstep (se 1 (by rfl) ⟨1527566, by rfl⟩ : syracuseStep 2036755 = 3055133) B3055133
theorem B2012195 : Blo 1190412 2012195 := bstep (se 1 (by rfl) ⟨1509146, by rfl⟩ : syracuseStep 2012195 = 3018293) B3018293
theorem B1340563 : Blo 1190412 1340563 := bstep (se 1 (by rfl) ⟨1005422, by rfl⟩ : syracuseStep 1340563 = 2010845) B2010845
theorem B2413795 : Blo 1190412 2413795 := bstep (se 1 (by rfl) ⟨1810346, by rfl⟩ : syracuseStep 2413795 = 3620693) B3620693
theorem B6788357 : Blo 1190412 6788357 := bstep (se 4 (by rfl) ⟨636408, by rfl⟩ : syracuseStep 6788357 = 1272817) B1272817
theorem B1340707 : Blo 1190412 1340707 := bstep (se 1 (by rfl) ⟨1005530, by rfl⟩ : syracuseStep 1340707 = 2011061) B2011061
theorem B6780293 : Blo 1190412 6780293 := bstep (se 4 (by rfl) ⟨635652, by rfl⟩ : syracuseStep 6780293 = 1271305) B1271305
theorem B4019597 : Blo 1190412 4019597 := bstep (se 3 (by rfl) ⟨753674, by rfl⟩ : syracuseStep 4019597 = 1507349) B1507349
theorem B1340851 : Blo 1190412 1340851 := bstep (se 1 (by rfl) ⟨1005638, by rfl⟩ : syracuseStep 1340851 = 2011277) B2011277
theorem B4019651 : Blo 1190412 4019651 := bstep (se 1 (by rfl) ⟨3014738, by rfl⟩ : syracuseStep 4019651 = 6029477) B6029477
theorem B6026723 : Blo 1190412 6026723 := bstep (se 1 (by rfl) ⟨4520042, by rfl⟩ : syracuseStep 6026723 = 9040085) B9040085
theorem B1340995 : Blo 1190412 1340995 := bstep (se 1 (by rfl) ⟨1005746, by rfl⟩ : syracuseStep 1340995 = 2011493) B2011493
theorem B4830833 : Blo 1190412 4830833 := bstep (se 2 (by rfl) ⟨1811562, by rfl⟩ : syracuseStep 4830833 = 3623125) B3623125
theorem B4019921 : Blo 1190412 4019921 := bstep (se 2 (by rfl) ⟨1507470, by rfl⟩ : syracuseStep 4019921 = 3014941) B3014941
theorem B2545361 : Blo 1190412 2545361 := bstep (se 2 (by rfl) ⟨954510, by rfl⟩ : syracuseStep 2545361 = 1909021) B1909021
theorem B3266257 : Blo 1190412 3266257 := bstep (se 2 (by rfl) ⟨1224846, by rfl⟩ : syracuseStep 3266257 = 2449693) B2449693
theorem B1341139 : Blo 1190412 1341139 := bstep (se 1 (by rfl) ⟨1005854, by rfl⟩ : syracuseStep 1341139 = 2011709) B2011709
theorem B3815171 : Blo 1190412 3815171 := bstep (se 1 (by rfl) ⟨2861378, by rfl⟩ : syracuseStep 3815171 = 5722757) B5722757
theorem B2037521 : Blo 1190412 2037521 := bstep (se 2 (by rfl) ⟨764070, by rfl⟩ : syracuseStep 2037521 = 1528141) B1528141
theorem B14481251 : Blo 1190412 14481251 := bstep (se 1 (by rfl) ⟨10860938, by rfl⟩ : syracuseStep 14481251 = 21721877) B21721877
theorem B1341283 : Blo 1190412 1341283 := bstep (se 1 (by rfl) ⟨1005962, by rfl⟩ : syracuseStep 1341283 = 2011925) B2011925
theorem B6789041 : Blo 1190412 6789041 := bstep (se 2 (by rfl) ⟨2545890, by rfl⟩ : syracuseStep 6789041 = 5091781) B5091781
theorem B4519907 : Blo 1190412 4519907 := bstep (se 1 (by rfl) ⟨3389930, by rfl⟩ : syracuseStep 4519907 = 6779861) B6779861
theorem B4519921 : Blo 1190412 4519921 := bstep (se 2 (by rfl) ⟨1694970, by rfl⟩ : syracuseStep 4519921 = 3389941) B3389941
theorem B1341427 : Blo 1190412 1341427 := bstep (se 1 (by rfl) ⟨1006070, by rfl⟩ : syracuseStep 1341427 = 2012141) B2012141
theorem B16291853 : Blo 1190412 16291853 := bstep (se 3 (by rfl) ⟨3054722, by rfl⟩ : syracuseStep 16291853 = 6109445) B6109445
theorem B6035633 : Blo 1190412 6035633 := bstep (se 2 (by rfl) ⟨2263362, by rfl⟩ : syracuseStep 6035633 = 4526725) B4526725
theorem B4020461 : Blo 1190412 4020461 := bstep (se 3 (by rfl) ⟨753836, by rfl⟩ : syracuseStep 4020461 = 1507673) B1507673
theorem B6027533 : Blo 1190412 6027533 := bstep (se 3 (by rfl) ⟨1130162, by rfl⟩ : syracuseStep 6027533 = 2260325) B2260325
theorem B4020515 : Blo 1190412 4020515 := bstep (se 1 (by rfl) ⟨3015386, by rfl⟩ : syracuseStep 4020515 = 6030773) B6030773
theorem B26482997 : Blo 1190412 26482997 := bstep (se 5 (by rfl) ⟨1241390, by rfl⟩ : syracuseStep 26482997 = 2482781) B2482781
theorem B7248197 : Blo 1190412 7248197 := bstep (se 4 (by rfl) ⟨679518, by rfl⟩ : syracuseStep 7248197 = 1359037) B1359037
theorem B4962637 : Blo 1190412 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B7739725 : Blo 1190412 7739725 := bstep (se 3 (by rfl) ⟨1451198, by rfl⟩ : syracuseStep 7739725 = 2902397) B2902397
theorem B3815761 : Blo 1190412 3815761 := bstep (se 2 (by rfl) ⟨1430910, by rfl⟩ : syracuseStep 3815761 = 2861821) B2861821
theorem B2546147 : Blo 1190412 2546147 := bstep (se 1 (by rfl) ⟨1909610, by rfl⟩ : syracuseStep 2546147 = 3819221) B3819221
theorem B15464945 : Blo 1190412 15464945 := bstep (se 2 (by rfl) ⟨5799354, by rfl⟩ : syracuseStep 15464945 = 11598709) B11598709
theorem B3389987 : Blo 1190412 3389987 := bstep (se 1 (by rfl) ⟨2542490, by rfl⟩ : syracuseStep 3389987 = 5084981) B5084981
theorem B4020785 : Blo 1190412 4020785 := bstep (se 2 (by rfl) ⟨1507794, by rfl⟩ : syracuseStep 4020785 = 3015589) B3015589
theorem B5438285 : Blo 1190412 5438285 := bstep (se 3 (by rfl) ⟨1019678, by rfl⟩ : syracuseStep 5438285 = 2039357) B2039357
theorem B2415683 : Blo 1190412 2415683 := bstep (se 1 (by rfl) ⟨1811762, by rfl⟩ : syracuseStep 2415683 = 3623525) B3623525
theorem B4021325 : Blo 1190412 4021325 := bstep (se 3 (by rfl) ⟨753998, by rfl⟩ : syracuseStep 4021325 = 1507997) B1507997
theorem B7634033 : Blo 1190412 7634033 := bstep (se 2 (by rfl) ⟨2862762, by rfl⟩ : syracuseStep 7634033 = 5725525) B5725525
theorem B4021379 : Blo 1190412 4021379 := bstep (se 1 (by rfl) ⟨3016034, by rfl⟩ : syracuseStep 4021379 = 6032069) B6032069
theorem B49544419 : Blo 1190412 49544419 := bstep (se 1 (by rfl) ⟨37158314, by rfl⟩ : syracuseStep 49544419 = 74316629) B74316629
theorem B4291811 : Blo 1190412 4291811 := bstep (se 1 (by rfl) ⟨3218858, by rfl⟩ : syracuseStep 4291811 = 6437717) B6437717
theorem B13745477 : Blo 1190412 13745477 := bstep (se 4 (by rfl) ⟨1288638, by rfl⟩ : syracuseStep 13745477 = 2577277) B2577277
theorem B3013969 : Blo 1190412 3013969 := bstep (se 2 (by rfl) ⟨1130238, by rfl⟩ : syracuseStep 3013969 = 2260477) B2260477
theorem B6790499 : Blo 1190412 6790499 := bstep (se 1 (by rfl) ⟨5092874, by rfl⟩ : syracuseStep 6790499 = 10185749) B10185749
theorem B1506691 : Blo 1190412 1506691 := bstep (se 1 (by rfl) ⟨1130018, by rfl⟩ : syracuseStep 1506691 = 2260037) B2260037
theorem B4021649 : Blo 1190412 4021649 := bstep (se 2 (by rfl) ⟨1508118, by rfl⟩ : syracuseStep 4021649 = 3016237) B3016237
theorem B4521379 : Blo 1190412 4521379 := bstep (se 1 (by rfl) ⟨3391034, by rfl⟩ : syracuseStep 4521379 = 6782069) B6782069
theorem B6438341 : Blo 1190412 6438341 := bstep (se 4 (by rfl) ⟨603594, by rfl⟩ : syracuseStep 6438341 = 1207189) B1207189
theorem B2039267 : Blo 1190412 2039267 := bstep (se 1 (by rfl) ⟨1529450, by rfl⟩ : syracuseStep 2039267 = 3058901) B3058901
theorem B27901493 : Blo 1190412 27901493 := bstep (se 5 (by rfl) ⟨1307882, by rfl⟩ : syracuseStep 27901493 = 2615765) B2615765
theorem B2260561 : Blo 1190412 2260561 := bstep (se 2 (by rfl) ⟨847710, by rfl⟩ : syracuseStep 2260561 = 1695421) B1695421
theorem B1359443 : Blo 1190412 1359443 := bstep (se 1 (by rfl) ⟨1019582, by rfl⟩ : syracuseStep 1359443 = 2039165) B2039165
theorem B3014243 : Blo 1190412 3014243 := bstep (se 1 (by rfl) ⟨2260682, by rfl⟩ : syracuseStep 3014243 = 4521365) B4521365
theorem B1908355 : Blo 1190412 1908355 := bstep (se 1 (by rfl) ⟨1431266, by rfl⟩ : syracuseStep 1908355 = 2862533) B2862533
theorem B4832909 : Blo 1190412 4832909 := bstep (se 3 (by rfl) ⟨906170, by rfl⟩ : syracuseStep 4832909 = 1812341) B1812341
theorem B2678435 : Blo 1190412 2678435 := bstep (se 1 (by rfl) ⟨2008826, by rfl⟩ : syracuseStep 2678435 = 4017653) B4017653
theorem B6192845 : Blo 1190412 6192845 := bstep (se 3 (by rfl) ⟨1161158, by rfl⟩ : syracuseStep 6192845 = 2322317) B2322317
theorem B3391217 : Blo 1190412 3391217 := bstep (se 2 (by rfl) ⟨1271706, by rfl⟩ : syracuseStep 3391217 = 2543413) B2543413
theorem B1785635 : Blo 1190412 1785635 := bstep (se 1 (by rfl) ⟨1339226, by rfl⟩ : syracuseStep 1785635 = 2678453) B2678453
theorem B3014435 : Blo 1190412 3014435 := bstep (se 1 (by rfl) ⟨2260826, by rfl⟩ : syracuseStep 3014435 = 4521653) B4521653
theorem B1785665 : Blo 1190412 1785665 := bstep (se 2 (by rfl) ⟨669624, by rfl⟩ : syracuseStep 1785665 = 1339249) B1339249
theorem B1785683 : Blo 1190412 1785683 := bstep (se 1 (by rfl) ⟨1339262, by rfl⟩ : syracuseStep 1785683 = 2678525) B2678525
theorem B1785713 : Blo 1190412 1785713 := bstep (se 2 (by rfl) ⟨669642, by rfl⟩ : syracuseStep 1785713 = 1339285) B1339285
theorem B1507187 : Blo 1190412 1507187 := bstep (se 1 (by rfl) ⟨1130390, by rfl⟩ : syracuseStep 1507187 = 2260781) B2260781
theorem B1785731 : Blo 1190412 1785731 := bstep (se 1 (by rfl) ⟨1339298, by rfl⟩ : syracuseStep 1785731 = 2678597) B2678597
theorem B1908611 : Blo 1190412 1908611 := bstep (se 1 (by rfl) ⟨1431458, by rfl⟩ : syracuseStep 1908611 = 2862917) B2862917
theorem B1785761 : Blo 1190412 1785761 := bstep (se 2 (by rfl) ⟨669660, by rfl⟩ : syracuseStep 1785761 = 1339321) B1339321
theorem B1695649 : Blo 1190412 1695649 := bstep (se 2 (by rfl) ⟨635868, by rfl⟩ : syracuseStep 1695649 = 1271737) B1271737
theorem B4022189 : Blo 1190412 4022189 := bstep (se 3 (by rfl) ⟨754160, by rfl⟩ : syracuseStep 4022189 = 1508321) B1508321
theorem B2678705 : Blo 1190412 2678705 := bstep (se 2 (by rfl) ⟨1004514, by rfl⟩ : syracuseStep 2678705 = 2009029) B2009029
theorem B1785779 : Blo 1190412 1785779 := bstep (se 1 (by rfl) ⟨1339334, by rfl⟩ : syracuseStep 1785779 = 2678669) B2678669
theorem B2678723 : Blo 1190412 2678723 := bstep (se 1 (by rfl) ⟨2009042, by rfl⟩ : syracuseStep 2678723 = 4018085) B4018085
theorem B1785809 : Blo 1190412 1785809 := bstep (se 2 (by rfl) ⟨669678, by rfl⟩ : syracuseStep 1785809 = 1339357) B1339357
theorem B1785827 : Blo 1190412 1785827 := bstep (se 1 (by rfl) ⟨1339370, by rfl⟩ : syracuseStep 1785827 = 2678741) B2678741
theorem B2260963 : Blo 1190412 2260963 := bstep (se 1 (by rfl) ⟨1695722, by rfl⟩ : syracuseStep 2260963 = 3391445) B3391445
theorem B4022243 : Blo 1190412 4022243 := bstep (se 1 (by rfl) ⟨3016682, by rfl⟩ : syracuseStep 4022243 = 6033365) B6033365
theorem B9043973 : Blo 1190412 9043973 := bstep (se 4 (by rfl) ⟨847872, by rfl⟩ : syracuseStep 9043973 = 1695745) B1695745
theorem B2678795 : Blo 1190412 2678795 := bstep (se 1 (by rfl) ⟨2009096, by rfl⟩ : syracuseStep 2678795 = 4018193) B4018193
theorem B1507339 : Blo 1190412 1507339 := bstep (se 1 (by rfl) ⟨1130504, by rfl⟩ : syracuseStep 1507339 = 2261009) B2261009
theorem B1785881 : Blo 1190412 1785881 := bstep (se 2 (by rfl) ⟨669705, by rfl⟩ : syracuseStep 1785881 = 1339411) B1339411
theorem B2678849 : Blo 1190412 2678849 := bstep (se 2 (by rfl) ⟨1004568, by rfl⟩ : syracuseStep 2678849 = 2009137) B2009137
theorem B74326085 : Blo 1190412 74326085 := bstep (se 4 (by rfl) ⟨6968070, by rfl⟩ : syracuseStep 74326085 = 13936141) B13936141
theorem B9052235 : Blo 1190412 9052235 := bstep (se 1 (by rfl) ⟨6789176, by rfl⟩ : syracuseStep 9052235 = 13578353) B13578353
theorem B9175133 : Blo 1190412 9175133 := bstep (se 3 (by rfl) ⟨1720337, by rfl⟩ : syracuseStep 9175133 = 3440675) B3440675
theorem B10862693 : Blo 1190412 10862693 := bstep (se 4 (by rfl) ⟨1018377, by rfl⟩ : syracuseStep 10862693 = 2036755) B2036755
theorem B1785995 : Blo 1190412 1785995 := bstep (se 1 (by rfl) ⟨1339496, by rfl⟩ : syracuseStep 1785995 = 2678993) B2678993
theorem B1786007 : Blo 1190412 1786007 := bstep (se 1 (by rfl) ⟨1339505, by rfl⟩ : syracuseStep 1786007 = 2679011) B2679011
theorem B3219659 : Blo 1190412 3219659 := bstep (se 1 (by rfl) ⟨2414744, by rfl⟩ : syracuseStep 3219659 = 4829489) B4829489
theorem B1786073 : Blo 1190412 1786073 := bstep (se 2 (by rfl) ⟨669777, by rfl⟩ : syracuseStep 1786073 = 1339555) B1339555
theorem B2416883 : Blo 1190412 2416883 := bstep (se 1 (by rfl) ⟨1812662, by rfl⟩ : syracuseStep 2416883 = 3625325) B3625325
theorem B2679065 : Blo 1190412 2679065 := bstep (se 2 (by rfl) ⟨1004649, by rfl⟩ : syracuseStep 2679065 = 2009299) B2009299
theorem B1786187 : Blo 1190412 1786187 := bstep (se 1 (by rfl) ⟨1339640, by rfl⟩ : syracuseStep 1786187 = 2679281) B2679281
theorem B1786199 : Blo 1190412 1786199 := bstep (se 1 (by rfl) ⟨1339649, by rfl⟩ : syracuseStep 1786199 = 2679299) B2679299
theorem B1696087 : Blo 1190412 1696087 := bstep (se 1 (by rfl) ⟨1272065, by rfl⟩ : syracuseStep 1696087 = 2544131) B2544131
theorem B4022621 : Blo 1190412 4022621 := bstep (se 3 (by rfl) ⟨754241, by rfl⟩ : syracuseStep 4022621 = 1508483) B1508483
theorem B2679155 : Blo 1190412 2679155 := bstep (se 1 (by rfl) ⟨2009366, by rfl⟩ : syracuseStep 2679155 = 4018733) B4018733
theorem B17170805 : Blo 1190412 17170805 := bstep (se 5 (by rfl) ⟨804881, by rfl⟩ : syracuseStep 17170805 = 1609763) B1609763
theorem B2679191 : Blo 1190412 2679191 := bstep (se 1 (by rfl) ⟨2009393, by rfl⟩ : syracuseStep 2679191 = 4018787) B4018787
theorem B1786265 : Blo 1190412 1786265 := bstep (se 2 (by rfl) ⟨669849, by rfl⟩ : syracuseStep 1786265 = 1339699) B1339699
theorem B5087681 : Blo 1190412 5087681 := bstep (se 2 (by rfl) ⟨1907880, by rfl⟩ : syracuseStep 5087681 = 3815761) B3815761
theorem B1786379 : Blo 1190412 1786379 := bstep (se 1 (by rfl) ⟨1339784, by rfl⟩ : syracuseStep 1786379 = 2679569) B2679569
theorem B1786391 : Blo 1190412 1786391 := bstep (se 1 (by rfl) ⟨1339793, by rfl⟩ : syracuseStep 1786391 = 2679587) B2679587
theorem B2679371 : Blo 1190412 2679371 := bstep (se 1 (by rfl) ⟨2009528, by rfl⟩ : syracuseStep 2679371 = 4019057) B4019057
theorem B1786457 : Blo 1190412 1786457 := bstep (se 2 (by rfl) ⟨669921, by rfl⟩ : syracuseStep 1786457 = 1339843) B1339843
theorem B2679425 : Blo 1190412 2679425 := bstep (se 2 (by rfl) ⟨1004784, by rfl⟩ : syracuseStep 2679425 = 2009569) B2009569
theorem B2417305 : Blo 1190412 2417305 := bstep (se 2 (by rfl) ⟨906489, by rfl⟩ : syracuseStep 2417305 = 1812979) B1812979
theorem B1786571 : Blo 1190412 1786571 := bstep (se 1 (by rfl) ⟨1339928, by rfl⟩ : syracuseStep 1786571 = 2679857) B2679857
theorem B1786583 : Blo 1190412 1786583 := bstep (se 1 (by rfl) ⟨1339937, by rfl⟩ : syracuseStep 1786583 = 2679875) B2679875
theorem B2261783 : Blo 1190412 2261783 := bstep (se 1 (by rfl) ⟨1696337, by rfl⟩ : syracuseStep 2261783 = 3392675) B3392675
theorem B1786649 : Blo 1190412 1786649 := bstep (se 2 (by rfl) ⟨669993, by rfl⟩ : syracuseStep 1786649 = 1339987) B1339987
theorem B6030125 : Blo 1190412 6030125 := bstep (se 3 (by rfl) ⟨1130648, by rfl⟩ : syracuseStep 6030125 = 2261297) B2261297
theorem B2679641 : Blo 1190412 2679641 := bstep (se 2 (by rfl) ⟨1004865, by rfl⟩ : syracuseStep 2679641 = 2009731) B2009731
theorem B13763429 : Blo 1190412 13763429 := bstep (se 4 (by rfl) ⟨1290321, by rfl⟩ : syracuseStep 13763429 = 2580643) B2580643
theorem B1786763 : Blo 1190412 1786763 := bstep (se 1 (by rfl) ⟨1340072, by rfl⟩ : syracuseStep 1786763 = 2680145) B2680145
theorem B1786775 : Blo 1190412 1786775 := bstep (se 1 (by rfl) ⟨1340081, by rfl⟩ : syracuseStep 1786775 = 2680163) B2680163
theorem B2679731 : Blo 1190412 2679731 := bstep (se 1 (by rfl) ⟨2009798, by rfl⟩ : syracuseStep 2679731 = 4019597) B4019597
theorem B2679767 : Blo 1190412 2679767 := bstep (se 1 (by rfl) ⟨2009825, by rfl⟩ : syracuseStep 2679767 = 4019651) B4019651
theorem B1786841 : Blo 1190412 1786841 := bstep (se 2 (by rfl) ⟨670065, by rfl⟩ : syracuseStep 1786841 = 1340131) B1340131
theorem B1508311 : Blo 1190412 1508311 := bstep (se 1 (by rfl) ⟨1131233, by rfl⟩ : syracuseStep 1508311 = 2262467) B2262467
theorem B1696793 : Blo 1190412 1696793 := bstep (se 2 (by rfl) ⟨636297, by rfl⟩ : syracuseStep 1696793 = 1272595) B1272595
theorem B32228387 : Blo 1190412 32228387 := bstep (se 1 (by rfl) ⟨24171290, by rfl⟩ : syracuseStep 32228387 = 48342581) B48342581
theorem B17187875 : Blo 1190412 17187875 := bstep (se 1 (by rfl) ⟨12890906, by rfl⟩ : syracuseStep 17187875 = 25781813) B25781813
theorem B3015731 : Blo 1190412 3015731 := bstep (se 1 (by rfl) ⟨2261798, by rfl⟩ : syracuseStep 3015731 = 4523597) B4523597
theorem B1786955 : Blo 1190412 1786955 := bstep (se 1 (by rfl) ⟨1340216, by rfl⟩ : syracuseStep 1786955 = 2680433) B2680433
theorem B3220555 : Blo 1190412 3220555 := bstep (se 1 (by rfl) ⟨2415416, by rfl⟩ : syracuseStep 3220555 = 4830833) B4830833
theorem B1786967 : Blo 1190412 1786967 := bstep (se 1 (by rfl) ⟨1340225, by rfl⟩ : syracuseStep 1786967 = 2680451) B2680451
theorem B6530149 : Blo 1190412 6530149 := bstep (se 4 (by rfl) ⟨612201, by rfl⟩ : syracuseStep 6530149 = 1224403) B1224403
theorem B2679947 : Blo 1190412 2679947 := bstep (se 1 (by rfl) ⟨2009960, by rfl⟩ : syracuseStep 2679947 = 4019921) B4019921
theorem B1696907 : Blo 1190412 1696907 := bstep (se 1 (by rfl) ⟨1272680, by rfl⟩ : syracuseStep 1696907 = 2545361) B2545361
theorem B1787033 : Blo 1190412 1787033 := bstep (se 2 (by rfl) ⟨670137, by rfl⟩ : syracuseStep 1787033 = 1340275) B1340275
theorem B3622067 : Blo 1190412 3622067 := bstep (se 1 (by rfl) ⟨2716550, by rfl⟩ : syracuseStep 3622067 = 5433101) B5433101
theorem B2680001 : Blo 1190412 2680001 := bstep (se 2 (by rfl) ⟨1005000, by rfl⟩ : syracuseStep 2680001 = 2010001) B2010001
theorem B1787147 : Blo 1190412 1787147 := bstep (se 1 (by rfl) ⟨1340360, by rfl⟩ : syracuseStep 1787147 = 2680721) B2680721
theorem B1787159 : Blo 1190412 1787159 := bstep (se 1 (by rfl) ⟨1340369, by rfl⟩ : syracuseStep 1787159 = 2680739) B2680739
theorem B4523309 : Blo 1190412 4523309 := bstep (se 3 (by rfl) ⟨848120, by rfl⟩ : syracuseStep 4523309 = 1696241) B1696241
theorem B2262323 : Blo 1190412 2262323 := bstep (se 1 (by rfl) ⟨1696742, by rfl⟩ : syracuseStep 2262323 = 3393485) B3393485
theorem B3392857 : Blo 1190412 3392857 := bstep (se 2 (by rfl) ⟨1272321, by rfl⟩ : syracuseStep 3392857 = 2544643) B2544643
theorem B1787225 : Blo 1190412 1787225 := bstep (se 2 (by rfl) ⟨670209, by rfl⟩ : syracuseStep 1787225 = 1340419) B1340419
theorem B3016025 : Blo 1190412 3016025 := bstep (se 2 (by rfl) ⟨1131009, by rfl⟩ : syracuseStep 3016025 = 2262019) B2262019
theorem B2147735 : Blo 1190412 2147735 := bstep (se 1 (by rfl) ⟨1610801, by rfl⟩ : syracuseStep 2147735 = 3221603) B3221603
theorem B2680217 : Blo 1190412 2680217 := bstep (se 2 (by rfl) ⟨1005081, by rfl⟩ : syracuseStep 2680217 = 2010163) B2010163
theorem B1787339 : Blo 1190412 1787339 := bstep (se 1 (by rfl) ⟨1340504, by rfl⟩ : syracuseStep 1787339 = 2681009) B2681009
theorem B4023755 : Blo 1190412 4023755 := bstep (se 1 (by rfl) ⟨3017816, by rfl⟩ : syracuseStep 4023755 = 6035633) B6035633
theorem B1787351 : Blo 1190412 1787351 := bstep (se 1 (by rfl) ⟨1340513, by rfl⟩ : syracuseStep 1787351 = 2681027) B2681027
theorem B2680307 : Blo 1190412 2680307 := bstep (se 1 (by rfl) ⟨2010230, by rfl⟩ : syracuseStep 2680307 = 4020461) B4020461
theorem B2680343 : Blo 1190412 2680343 := bstep (se 1 (by rfl) ⟨2010257, by rfl⟩ : syracuseStep 2680343 = 4020515) B4020515
theorem B1787417 : Blo 1190412 1787417 := bstep (se 2 (by rfl) ⟨670281, by rfl⟩ : syracuseStep 1787417 = 1340563) B1340563
theorem B17655331 : Blo 1190412 17655331 := bstep (se 1 (by rfl) ⟨13241498, by rfl⟩ : syracuseStep 17655331 = 26482997) B26482997
theorem B3720779 : Blo 1190412 3720779 := bstep (se 1 (by rfl) ⟨2790584, by rfl⟩ : syracuseStep 3720779 = 5581169) B5581169
theorem B15894091 : Blo 1190412 15894091 := bstep (se 1 (by rfl) ⟨11920568, by rfl⟩ : syracuseStep 15894091 = 23841137) B23841137
theorem B1787531 : Blo 1190412 1787531 := bstep (se 1 (by rfl) ⟨1340648, by rfl⟩ : syracuseStep 1787531 = 2681297) B2681297
theorem B1787543 : Blo 1190412 1787543 := bstep (se 1 (by rfl) ⟨1340657, by rfl⟩ : syracuseStep 1787543 = 2681315) B2681315
theorem B1697431 : Blo 1190412 1697431 := bstep (se 1 (by rfl) ⟨1273073, by rfl⟩ : syracuseStep 1697431 = 2546147) B2546147
theorem B2680523 : Blo 1190412 2680523 := bstep (se 1 (by rfl) ⟨2010392, by rfl⟩ : syracuseStep 2680523 = 4020785) B4020785
theorem B1787609 : Blo 1190412 1787609 := bstep (se 2 (by rfl) ⟨670353, by rfl⟩ : syracuseStep 1787609 = 1340707) B1340707
theorem B4024025 : Blo 1190412 4024025 := bstep (se 2 (by rfl) ⟨1509009, by rfl⟩ : syracuseStep 4024025 = 3018019) B3018019
theorem B3393245 : Blo 1190412 3393245 := bstep (se 3 (by rfl) ⟨636233, by rfl⟩ : syracuseStep 3393245 = 1272467) B1272467
theorem B2680577 : Blo 1190412 2680577 := bstep (se 2 (by rfl) ⟨1005216, by rfl⟩ : syracuseStep 2680577 = 2010433) B2010433
theorem B1509131 : Blo 1190412 1509131 := bstep (se 1 (by rfl) ⟨1131848, by rfl⟩ : syracuseStep 1509131 = 2263697) B2263697
theorem B2262809 : Blo 1190412 2262809 := bstep (se 2 (by rfl) ⟨848553, by rfl⟩ : syracuseStep 2262809 = 1697107) B1697107
theorem B7243595 : Blo 1190412 7243595 := bstep (se 1 (by rfl) ⟨5432696, by rfl⟩ : syracuseStep 7243595 = 10865393) B10865393
theorem B1787723 : Blo 1190412 1787723 := bstep (se 1 (by rfl) ⟨1340792, by rfl⟩ : syracuseStep 1787723 = 2681585) B2681585
theorem B1787735 : Blo 1190412 1787735 := bstep (se 1 (by rfl) ⟨1340801, by rfl⟩ : syracuseStep 1787735 = 2681603) B2681603
theorem B2008921 : Blo 1190412 2008921 := bstep (se 2 (by rfl) ⟨753345, by rfl⟩ : syracuseStep 2008921 = 1506691) B1506691
theorem B2148211 : Blo 1190412 2148211 := bstep (se 1 (by rfl) ⟨1611158, by rfl⟩ : syracuseStep 2148211 = 3222317) B3222317
theorem B1787801 : Blo 1190412 1787801 := bstep (se 2 (by rfl) ⟨670425, by rfl⟩ : syracuseStep 1787801 = 1340851) B1340851
theorem B6784985 : Blo 1190412 6784985 := bstep (se 2 (by rfl) ⟨2544369, by rfl⟩ : syracuseStep 6784985 = 5088739) B5088739
theorem B2680793 : Blo 1190412 2680793 := bstep (se 2 (by rfl) ⟨1005297, by rfl⟩ : syracuseStep 2680793 = 2010595) B2010595
theorem B1787915 : Blo 1190412 1787915 := bstep (se 1 (by rfl) ⟨1340936, by rfl⟩ : syracuseStep 1787915 = 2681873) B2681873
theorem B1787927 : Blo 1190412 1787927 := bstep (se 1 (by rfl) ⟨1340945, by rfl⟩ : syracuseStep 1787927 = 2681891) B2681891
theorem B5433389 : Blo 1190412 5433389 := bstep (se 3 (by rfl) ⟨1018760, by rfl⟩ : syracuseStep 5433389 = 2037521) B2037521
theorem B2680883 : Blo 1190412 2680883 := bstep (se 1 (by rfl) ⟨2010662, by rfl⟩ : syracuseStep 2680883 = 4021325) B4021325
theorem B4524083 : Blo 1190412 4524083 := bstep (se 1 (by rfl) ⟨3393062, by rfl⟩ : syracuseStep 4524083 = 6786125) B6786125
theorem B4294721 : Blo 1190412 4294721 := bstep (se 2 (by rfl) ⟨1610520, by rfl⟩ : syracuseStep 4294721 = 3221041) B3221041
theorem B5089355 : Blo 1190412 5089355 := bstep (se 1 (by rfl) ⟨3817016, by rfl⟩ : syracuseStep 5089355 = 7634033) B7634033
theorem B2680919 : Blo 1190412 2680919 := bstep (se 1 (by rfl) ⟨2010689, by rfl⟩ : syracuseStep 2680919 = 4021379) B4021379
theorem B1787993 : Blo 1190412 1787993 := bstep (se 2 (by rfl) ⟨670497, by rfl⟩ : syracuseStep 1787993 = 1340995) B1340995
theorem B2861207 : Blo 1190412 2861207 := bstep (se 1 (by rfl) ⟨2145905, by rfl⟩ : syracuseStep 2861207 = 4291811) B4291811
theorem B1788107 : Blo 1190412 1788107 := bstep (se 1 (by rfl) ⟨1341080, by rfl⟩ : syracuseStep 1788107 = 2682161) B2682161
theorem B1788119 : Blo 1190412 1788119 := bstep (se 1 (by rfl) ⟨1341089, by rfl⟩ : syracuseStep 1788119 = 2682179) B2682179
theorem B2681099 : Blo 1190412 2681099 := bstep (se 1 (by rfl) ⟨2010824, by rfl⟩ : syracuseStep 2681099 = 4021649) B4021649
theorem B1788185 : Blo 1190412 1788185 := bstep (se 2 (by rfl) ⟨670569, by rfl⟩ : syracuseStep 1788185 = 1341139) B1341139
theorem B2681153 : Blo 1190412 2681153 := bstep (se 2 (by rfl) ⟨1005432, by rfl⟩ : syracuseStep 2681153 = 2010865) B2010865
theorem B9046403 : Blo 1190412 9046403 := bstep (se 1 (by rfl) ⟨6784802, by rfl⟩ : syracuseStep 9046403 = 13569605) B13569605
theorem B1788299 : Blo 1190412 1788299 := bstep (se 1 (by rfl) ⟨1341224, by rfl⟩ : syracuseStep 1788299 = 2682449) B2682449
theorem B2009495 : Blo 1190412 2009495 := bstep (se 1 (by rfl) ⟨1507121, by rfl⟩ : syracuseStep 2009495 = 3014243) B3014243
theorem B1788311 : Blo 1190412 1788311 := bstep (se 1 (by rfl) ⟨1341233, by rfl⟩ : syracuseStep 1788311 = 2682467) B2682467
theorem B3221939 : Blo 1190412 3221939 := bstep (se 1 (by rfl) ⟨2416454, by rfl⟩ : syracuseStep 3221939 = 4832909) B4832909
theorem B1788377 : Blo 1190412 1788377 := bstep (se 2 (by rfl) ⟨670641, by rfl⟩ : syracuseStep 1788377 = 1341283) B1341283
theorem B1190423 : Blo 1190412 1190423 := bstep (se 1 (by rfl) ⟨892817, by rfl⟩ : syracuseStep 1190423 = 1785635) B1785635
theorem B2009623 : Blo 1190412 2009623 := bstep (se 1 (by rfl) ⟨1507217, by rfl⟩ : syracuseStep 2009623 = 3014435) B3014435
theorem B2681369 : Blo 1190412 2681369 := bstep (se 2 (by rfl) ⟨1005513, by rfl⟩ : syracuseStep 2681369 = 2011027) B2011027
theorem B1190443 : Blo 1190412 1190443 := bstep (se 1 (by rfl) ⟨892832, by rfl⟩ : syracuseStep 1190443 = 1785665) B1785665
theorem B1190455 : Blo 1190412 1190455 := bstep (se 1 (by rfl) ⟨892841, by rfl⟩ : syracuseStep 1190455 = 1785683) B1785683
theorem B1190475 : Blo 1190412 1190475 := bstep (se 1 (by rfl) ⟨892856, by rfl⟩ : syracuseStep 1190475 = 1785713) B1785713
theorem B1788491 : Blo 1190412 1788491 := bstep (se 1 (by rfl) ⟨1341368, by rfl⟩ : syracuseStep 1788491 = 2682737) B2682737
theorem B1190487 : Blo 1190412 1190487 := bstep (se 1 (by rfl) ⟨892865, by rfl⟩ : syracuseStep 1190487 = 1785731) B1785731
theorem B1272407 : Blo 1190412 1272407 := bstep (se 1 (by rfl) ⟨954305, by rfl⟩ : syracuseStep 1272407 = 1908611) B1908611
theorem B1788503 : Blo 1190412 1788503 := bstep (se 1 (by rfl) ⟨1341377, by rfl⟩ : syracuseStep 1788503 = 2682755) B2682755
theorem B7637597 : Blo 1190412 7637597 := bstep (se 3 (by rfl) ⟨1432049, by rfl⟩ : syracuseStep 7637597 = 2864099) B2864099
theorem B1190507 : Blo 1190412 1190507 := bstep (se 1 (by rfl) ⟨892880, by rfl⟩ : syracuseStep 1190507 = 1785761) B1785761
theorem B2681459 : Blo 1190412 2681459 := bstep (se 1 (by rfl) ⟨2011094, by rfl⟩ : syracuseStep 2681459 = 4022189) B4022189
theorem B1190519 : Blo 1190412 1190519 := bstep (se 1 (by rfl) ⟨892889, by rfl⟩ : syracuseStep 1190519 = 1785779) B1785779
theorem B24447619 : Blo 1190412 24447619 := bstep (se 1 (by rfl) ⟨18335714, by rfl⟩ : syracuseStep 24447619 = 36671429) B36671429
theorem B1190539 : Blo 1190412 1190539 := bstep (se 1 (by rfl) ⟨892904, by rfl⟩ : syracuseStep 1190539 = 1785809) B1785809
theorem B1190551 : Blo 1190412 1190551 := bstep (se 1 (by rfl) ⟨892913, by rfl⟩ : syracuseStep 1190551 = 1785827) B1785827
theorem B2681495 : Blo 1190412 2681495 := bstep (se 1 (by rfl) ⟨2011121, by rfl⟩ : syracuseStep 2681495 = 4022243) B4022243
theorem B1788569 : Blo 1190412 1788569 := bstep (se 2 (by rfl) ⟨670713, by rfl⟩ : syracuseStep 1788569 = 1341427) B1341427
theorem B1190571 : Blo 1190412 1190571 := bstep (se 1 (by rfl) ⟨892928, by rfl⟩ : syracuseStep 1190571 = 1785857) B1785857
theorem B1190583 : Blo 1190412 1190583 := bstep (se 1 (by rfl) ⟨892937, by rfl⟩ : syracuseStep 1190583 = 1785875) B1785875
theorem B1190603 : Blo 1190412 1190603 := bstep (se 1 (by rfl) ⟨892952, by rfl⟩ : syracuseStep 1190603 = 1785905) B1785905
theorem B1190615 : Blo 1190412 1190615 := bstep (se 1 (by rfl) ⟨892961, by rfl⟩ : syracuseStep 1190615 = 1785923) B1785923
theorem B1190635 : Blo 1190412 1190635 := bstep (se 1 (by rfl) ⟨892976, by rfl⟩ : syracuseStep 1190635 = 1785953) B1785953
theorem B1190647 : Blo 1190412 1190647 := bstep (se 1 (by rfl) ⟨892985, by rfl⟩ : syracuseStep 1190647 = 1785971) B1785971
theorem B1190667 : Blo 1190412 1190667 := bstep (se 1 (by rfl) ⟨893000, by rfl⟩ : syracuseStep 1190667 = 1786001) B1786001
theorem B1190679 : Blo 1190412 1190679 := bstep (se 1 (by rfl) ⟨893009, by rfl⟩ : syracuseStep 1190679 = 1786019) B1786019
theorem B1190699 : Blo 1190412 1190699 := bstep (se 1 (by rfl) ⟨893024, by rfl⟩ : syracuseStep 1190699 = 1786049) B1786049
theorem B1190711 : Blo 1190412 1190711 := bstep (se 1 (by rfl) ⟨893033, by rfl⟩ : syracuseStep 1190711 = 1786067) B1786067
theorem B1190731 : Blo 1190412 1190731 := bstep (se 1 (by rfl) ⟨893048, by rfl⟩ : syracuseStep 1190731 = 1786097) B1786097
theorem B2681675 : Blo 1190412 2681675 := bstep (se 1 (by rfl) ⟨2011256, by rfl⟩ : syracuseStep 2681675 = 4022513) B4022513
theorem B1190743 : Blo 1190412 1190743 := bstep (se 1 (by rfl) ⟨893057, by rfl⟩ : syracuseStep 1190743 = 1786115) B1786115
theorem B6441821 : Blo 1190412 6441821 := bstep (se 3 (by rfl) ⟨1207841, by rfl⟩ : syracuseStep 6441821 = 2415683) B2415683
theorem B5090141 : Blo 1190412 5090141 := bstep (se 3 (by rfl) ⟨954401, by rfl⟩ : syracuseStep 5090141 = 1908803) B1908803
theorem B1190763 : Blo 1190412 1190763 := bstep (se 1 (by rfl) ⟨893072, by rfl⟩ : syracuseStep 1190763 = 1786145) B1786145
theorem B1190775 : Blo 1190412 1190775 := bstep (se 1 (by rfl) ⟨893081, by rfl⟩ : syracuseStep 1190775 = 1786163) B1786163
theorem B2681729 : Blo 1190412 2681729 := bstep (se 2 (by rfl) ⟨1005648, by rfl⟩ : syracuseStep 2681729 = 2011297) B2011297
theorem B1190795 : Blo 1190412 1190795 := bstep (se 1 (by rfl) ⟨893096, by rfl⟩ : syracuseStep 1190795 = 1786193) B1786193
theorem B1190807 : Blo 1190412 1190807 := bstep (se 1 (by rfl) ⟨893105, by rfl⟩ : syracuseStep 1190807 = 1786211) B1786211
theorem B2861975 : Blo 1190412 2861975 := bstep (se 1 (by rfl) ⟨2146481, by rfl⟩ : syracuseStep 2861975 = 4292963) B4292963
theorem B1190827 : Blo 1190412 1190827 := bstep (se 1 (by rfl) ⟨893120, by rfl⟩ : syracuseStep 1190827 = 1786241) B1786241
theorem B1190839 : Blo 1190412 1190839 := bstep (se 1 (by rfl) ⟨893129, by rfl⟩ : syracuseStep 1190839 = 1786259) B1786259
theorem B1190859 : Blo 1190412 1190859 := bstep (se 1 (by rfl) ⟨893144, by rfl⟩ : syracuseStep 1190859 = 1786289) B1786289
theorem B3017675 : Blo 1190412 3017675 := bstep (se 1 (by rfl) ⟨2263256, by rfl⟩ : syracuseStep 3017675 = 4526513) B4526513
theorem B1190871 : Blo 1190412 1190871 := bstep (se 1 (by rfl) ⟨893153, by rfl⟩ : syracuseStep 1190871 = 1786307) B1786307
theorem B1190891 : Blo 1190412 1190891 := bstep (se 1 (by rfl) ⟨893168, by rfl⟩ : syracuseStep 1190891 = 1786337) B1786337
theorem B1190903 : Blo 1190412 1190903 := bstep (se 1 (by rfl) ⟨893177, by rfl⟩ : syracuseStep 1190903 = 1786355) B1786355
theorem B1190923 : Blo 1190412 1190923 := bstep (se 1 (by rfl) ⟨893192, by rfl⟩ : syracuseStep 1190923 = 1786385) B1786385
theorem B1190935 : Blo 1190412 1190935 := bstep (se 1 (by rfl) ⟨893201, by rfl⟩ : syracuseStep 1190935 = 1786403) B1786403
theorem B1207319 : Blo 1190412 1207319 := bstep (se 1 (by rfl) ⟨905489, by rfl⟩ : syracuseStep 1207319 = 1810979) B1810979
theorem B1190955 : Blo 1190412 1190955 := bstep (se 1 (by rfl) ⟨893216, by rfl⟩ : syracuseStep 1190955 = 1786433) B1786433
theorem B1190967 : Blo 1190412 1190967 := bstep (se 1 (by rfl) ⟨893225, by rfl⟩ : syracuseStep 1190967 = 1786451) B1786451
theorem B1190987 : Blo 1190412 1190987 := bstep (se 1 (by rfl) ⟨893240, by rfl⟩ : syracuseStep 1190987 = 1786481) B1786481
theorem B1190999 : Blo 1190412 1190999 := bstep (se 1 (by rfl) ⟨893249, by rfl⟩ : syracuseStep 1190999 = 1786499) B1786499
theorem B2681945 : Blo 1190412 2681945 := bstep (se 2 (by rfl) ⟨1005729, by rfl⟩ : syracuseStep 2681945 = 2011459) B2011459
theorem B1191019 : Blo 1190412 1191019 := bstep (se 1 (by rfl) ⟨893264, by rfl⟩ : syracuseStep 1191019 = 1786529) B1786529
theorem B1191031 : Blo 1190412 1191031 := bstep (se 1 (by rfl) ⟨893273, by rfl⟩ : syracuseStep 1191031 = 1786547) B1786547
theorem B1191051 : Blo 1190412 1191051 := bstep (se 1 (by rfl) ⟨893288, by rfl⟩ : syracuseStep 1191051 = 1786577) B1786577
theorem B2010251 : Blo 1190412 2010251 := bstep (se 1 (by rfl) ⟨1507688, by rfl⟩ : syracuseStep 2010251 = 3015377) B3015377
theorem B1191063 : Blo 1190412 1191063 := bstep (se 1 (by rfl) ⟨893297, by rfl⟩ : syracuseStep 1191063 = 1786595) B1786595
theorem B1191083 : Blo 1190412 1191083 := bstep (se 1 (by rfl) ⟨893312, by rfl⟩ : syracuseStep 1191083 = 1786625) B1786625
theorem B2682035 : Blo 1190412 2682035 := bstep (se 1 (by rfl) ⟨2011526, by rfl⟩ : syracuseStep 2682035 = 4023053) B4023053
theorem B1191095 : Blo 1190412 1191095 := bstep (se 1 (by rfl) ⟨893321, by rfl⟩ : syracuseStep 1191095 = 1786643) B1786643
theorem B1191115 : Blo 1190412 1191115 := bstep (se 1 (by rfl) ⟨893336, by rfl⟩ : syracuseStep 1191115 = 1786673) B1786673
theorem B1191127 : Blo 1190412 1191127 := bstep (se 1 (by rfl) ⟨893345, by rfl⟩ : syracuseStep 1191127 = 1786691) B1786691
theorem B2682071 : Blo 1190412 2682071 := bstep (se 1 (by rfl) ⟨2011553, by rfl⟩ : syracuseStep 2682071 = 4023107) B4023107
theorem B1191147 : Blo 1190412 1191147 := bstep (se 1 (by rfl) ⟨893360, by rfl⟩ : syracuseStep 1191147 = 1786721) B1786721
theorem B1191159 : Blo 1190412 1191159 := bstep (se 1 (by rfl) ⟨893369, by rfl⟩ : syracuseStep 1191159 = 1786739) B1786739
theorem B1191179 : Blo 1190412 1191179 := bstep (se 1 (by rfl) ⟨893384, by rfl⟩ : syracuseStep 1191179 = 1786769) B1786769
theorem B2010379 : Blo 1190412 2010379 := bstep (se 1 (by rfl) ⟨1507784, by rfl⟩ : syracuseStep 2010379 = 3015569) B3015569
theorem B1191191 : Blo 1190412 1191191 := bstep (se 1 (by rfl) ⟨893393, by rfl⟩ : syracuseStep 1191191 = 1786787) B1786787
theorem B1191211 : Blo 1190412 1191211 := bstep (se 1 (by rfl) ⟨893408, by rfl⟩ : syracuseStep 1191211 = 1786817) B1786817
theorem B1191223 : Blo 1190412 1191223 := bstep (se 1 (by rfl) ⟨893417, by rfl⟩ : syracuseStep 1191223 = 1786835) B1786835
theorem B1191243 : Blo 1190412 1191243 := bstep (se 1 (by rfl) ⟨893432, by rfl⟩ : syracuseStep 1191243 = 1786865) B1786865
theorem B1191255 : Blo 1190412 1191255 := bstep (se 1 (by rfl) ⟨893441, by rfl⟩ : syracuseStep 1191255 = 1786883) B1786883
theorem B1191275 : Blo 1190412 1191275 := bstep (se 1 (by rfl) ⟨893456, by rfl⟩ : syracuseStep 1191275 = 1786913) B1786913
theorem B1191287 : Blo 1190412 1191287 := bstep (se 1 (by rfl) ⟨893465, by rfl⟩ : syracuseStep 1191287 = 1786931) B1786931
theorem B1191307 : Blo 1190412 1191307 := bstep (se 1 (by rfl) ⟨893480, by rfl⟩ : syracuseStep 1191307 = 1786961) B1786961
theorem B2682251 : Blo 1190412 2682251 := bstep (se 1 (by rfl) ⟨2011688, by rfl⟩ : syracuseStep 2682251 = 4023377) B4023377
theorem B1191319 : Blo 1190412 1191319 := bstep (se 1 (by rfl) ⟨893489, by rfl⟩ : syracuseStep 1191319 = 1786979) B1786979
theorem B2010521 : Blo 1190412 2010521 := bstep (se 2 (by rfl) ⟨753945, by rfl⟩ : syracuseStep 2010521 = 1507891) B1507891
theorem B1191339 : Blo 1190412 1191339 := bstep (se 1 (by rfl) ⟨893504, by rfl⟩ : syracuseStep 1191339 = 1787009) B1787009
theorem B1191351 : Blo 1190412 1191351 := bstep (se 1 (by rfl) ⟨893513, by rfl⟩ : syracuseStep 1191351 = 1787027) B1787027
theorem B2682305 : Blo 1190412 2682305 := bstep (se 2 (by rfl) ⟨1005864, by rfl⟩ : syracuseStep 2682305 = 2011729) B2011729
theorem B1191371 : Blo 1190412 1191371 := bstep (se 1 (by rfl) ⟨893528, by rfl⟩ : syracuseStep 1191371 = 1787057) B1787057
theorem B1191383 : Blo 1190412 1191383 := bstep (se 1 (by rfl) ⟨893537, by rfl⟩ : syracuseStep 1191383 = 1787075) B1787075
theorem B5729753 : Blo 1190412 5729753 := bstep (se 2 (by rfl) ⟨2148657, by rfl⟩ : syracuseStep 5729753 = 4297315) B4297315
theorem B1191403 : Blo 1190412 1191403 := bstep (se 1 (by rfl) ⟨893552, by rfl⟩ : syracuseStep 1191403 = 1787105) B1787105
theorem B1191415 : Blo 1190412 1191415 := bstep (se 1 (by rfl) ⟨893561, by rfl⟩ : syracuseStep 1191415 = 1787123) B1787123
theorem B4525571 : Blo 1190412 4525571 := bstep (se 1 (by rfl) ⟨3394178, by rfl⟩ : syracuseStep 4525571 = 6788357) B6788357
theorem B1191435 : Blo 1190412 1191435 := bstep (se 1 (by rfl) ⟨893576, by rfl⟩ : syracuseStep 1191435 = 1787153) B1787153
theorem B4075031 : Blo 1190412 4075031 := bstep (se 1 (by rfl) ⟨3056273, by rfl⟩ : syracuseStep 4075031 = 6112547) B6112547
theorem B1191447 : Blo 1190412 1191447 := bstep (se 1 (by rfl) ⟨893585, by rfl⟩ : syracuseStep 1191447 = 1787171) B1787171
theorem B2010649 : Blo 1190412 2010649 := bstep (se 2 (by rfl) ⟨753993, by rfl⟩ : syracuseStep 2010649 = 1507987) B1507987
theorem B1191467 : Blo 1190412 1191467 := bstep (se 1 (by rfl) ⟨893600, by rfl⟩ : syracuseStep 1191467 = 1787201) B1787201
theorem B1191479 : Blo 1190412 1191479 := bstep (se 1 (by rfl) ⟨893609, by rfl⟩ : syracuseStep 1191479 = 1787219) B1787219
theorem B6786625 : Blo 1190412 6786625 := bstep (se 2 (by rfl) ⟨2544984, by rfl⟩ : syracuseStep 6786625 = 5089969) B5089969
theorem B1191499 : Blo 1190412 1191499 := bstep (se 1 (by rfl) ⟨893624, by rfl⟩ : syracuseStep 1191499 = 1787249) B1787249
theorem B1191511 : Blo 1190412 1191511 := bstep (se 1 (by rfl) ⟨893633, by rfl⟩ : syracuseStep 1191511 = 1787267) B1787267
theorem B1191531 : Blo 1190412 1191531 := bstep (se 1 (by rfl) ⟨893648, by rfl⟩ : syracuseStep 1191531 = 1787297) B1787297
theorem B1191543 : Blo 1190412 1191543 := bstep (se 1 (by rfl) ⟨893657, by rfl⟩ : syracuseStep 1191543 = 1787315) B1787315
theorem B1191563 : Blo 1190412 1191563 := bstep (se 1 (by rfl) ⟨893672, by rfl⟩ : syracuseStep 1191563 = 1787345) B1787345
theorem B4017815 : Blo 1190412 4017815 := bstep (se 1 (by rfl) ⟨3013361, by rfl⟩ : syracuseStep 4017815 = 6026723) B6026723
theorem B1191575 : Blo 1190412 1191575 := bstep (se 1 (by rfl) ⟨893681, by rfl⟩ : syracuseStep 1191575 = 1787363) B1787363
theorem B2682521 : Blo 1190412 2682521 := bstep (se 2 (by rfl) ⟨1005945, by rfl⟩ : syracuseStep 2682521 = 2011891) B2011891
theorem B1191595 : Blo 1190412 1191595 := bstep (se 1 (by rfl) ⟨893696, by rfl⟩ : syracuseStep 1191595 = 1787393) B1787393
theorem B8826545 : Blo 1190412 8826545 := bstep (se 2 (by rfl) ⟨3309954, by rfl⟩ : syracuseStep 8826545 = 6619909) B6619909
theorem B1191607 : Blo 1190412 1191607 := bstep (se 1 (by rfl) ⟨893705, by rfl⟩ : syracuseStep 1191607 = 1787411) B1787411
theorem B1191627 : Blo 1190412 1191627 := bstep (se 1 (by rfl) ⟨893720, by rfl⟩ : syracuseStep 1191627 = 1787441) B1787441
theorem B1191639 : Blo 1190412 1191639 := bstep (se 1 (by rfl) ⟨893729, by rfl⟩ : syracuseStep 1191639 = 1787459) B1787459
theorem B1191659 : Blo 1190412 1191659 := bstep (se 1 (by rfl) ⟨893744, by rfl⟩ : syracuseStep 1191659 = 1787489) B1787489
theorem B2682611 : Blo 1190412 2682611 := bstep (se 1 (by rfl) ⟨2011958, by rfl⟩ : syracuseStep 2682611 = 4023917) B4023917
theorem B1191671 : Blo 1190412 1191671 := bstep (se 1 (by rfl) ⟨893753, by rfl⟩ : syracuseStep 1191671 = 1787507) B1787507
theorem B1191691 : Blo 1190412 1191691 := bstep (se 1 (by rfl) ⟨893768, by rfl⟩ : syracuseStep 1191691 = 1787537) B1787537
theorem B1191703 : Blo 1190412 1191703 := bstep (se 1 (by rfl) ⟨893777, by rfl⟩ : syracuseStep 1191703 = 1787555) B1787555
theorem B2682647 : Blo 1190412 2682647 := bstep (se 1 (by rfl) ⟨2011985, by rfl⟩ : syracuseStep 2682647 = 4023971) B4023971
theorem B1191723 : Blo 1190412 1191723 := bstep (se 1 (by rfl) ⟨893792, by rfl⟩ : syracuseStep 1191723 = 1787585) B1787585
theorem B1191735 : Blo 1190412 1191735 := bstep (se 1 (by rfl) ⟨893801, by rfl⟩ : syracuseStep 1191735 = 1787603) B1787603
theorem B1191755 : Blo 1190412 1191755 := bstep (se 1 (by rfl) ⟨893816, by rfl⟩ : syracuseStep 1191755 = 1787633) B1787633
theorem B2543447 : Blo 1190412 2543447 := bstep (se 1 (by rfl) ⟨1907585, by rfl⟩ : syracuseStep 2543447 = 3815171) B3815171
theorem B1191767 : Blo 1190412 1191767 := bstep (se 1 (by rfl) ⟨893825, by rfl⟩ : syracuseStep 1191767 = 1787651) B1787651
theorem B4829017 : Blo 1190412 4829017 := bstep (se 2 (by rfl) ⟨1810881, by rfl⟩ : syracuseStep 4829017 = 3621763) B3621763
theorem B1191787 : Blo 1190412 1191787 := bstep (se 1 (by rfl) ⟨893840, by rfl⟩ : syracuseStep 1191787 = 1787681) B1787681
theorem B1191799 : Blo 1190412 1191799 := bstep (se 1 (by rfl) ⟨893849, by rfl⟩ : syracuseStep 1191799 = 1787699) B1787699
theorem B9170819 : Blo 1190412 9170819 := bstep (se 1 (by rfl) ⟨6878114, by rfl⟩ : syracuseStep 9170819 = 13756229) B13756229
theorem B1191819 : Blo 1190412 1191819 := bstep (se 1 (by rfl) ⟨893864, by rfl⟩ : syracuseStep 1191819 = 1787729) B1787729
theorem B9654167 : Blo 1190412 9654167 := bstep (se 1 (by rfl) ⟨7240625, by rfl⟩ : syracuseStep 9654167 = 14481251) B14481251
theorem B1191831 : Blo 1190412 1191831 := bstep (se 1 (by rfl) ⟨893873, by rfl⟩ : syracuseStep 1191831 = 1787747) B1787747
theorem B1191851 : Blo 1190412 1191851 := bstep (se 1 (by rfl) ⟨893888, by rfl⟩ : syracuseStep 1191851 = 1787777) B1787777
theorem B1191863 : Blo 1190412 1191863 := bstep (se 1 (by rfl) ⟨893897, by rfl⟩ : syracuseStep 1191863 = 1787795) B1787795
theorem B1339339 : Blo 1190412 1339339 := bstep (se 1 (by rfl) ⟨1004504, by rfl⟩ : syracuseStep 1339339 = 2009009) B2009009
theorem B1191883 : Blo 1190412 1191883 := bstep (se 1 (by rfl) ⟨893912, by rfl⟩ : syracuseStep 1191883 = 1787825) B1787825
theorem B4526027 : Blo 1190412 4526027 := bstep (se 1 (by rfl) ⟨3394520, by rfl⟩ : syracuseStep 4526027 = 6789041) B6789041
theorem B2682827 : Blo 1190412 2682827 := bstep (se 1 (by rfl) ⟨2012120, by rfl⟩ : syracuseStep 2682827 = 4024241) B4024241
theorem B1191895 : Blo 1190412 1191895 := bstep (se 1 (by rfl) ⟨893921, by rfl⟩ : syracuseStep 1191895 = 1787843) B1787843
theorem B1191915 : Blo 1190412 1191915 := bstep (se 1 (by rfl) ⟨893936, by rfl⟩ : syracuseStep 1191915 = 1787873) B1787873
theorem B1191927 : Blo 1190412 1191927 := bstep (se 1 (by rfl) ⟨893945, by rfl⟩ : syracuseStep 1191927 = 1787891) B1787891
theorem B2682881 : Blo 1190412 2682881 := bstep (se 2 (by rfl) ⟨1006080, by rfl⟩ : syracuseStep 2682881 = 2012161) B2012161
theorem B1191947 : Blo 1190412 1191947 := bstep (se 1 (by rfl) ⟨893960, by rfl⟩ : syracuseStep 1191947 = 1787921) B1787921
theorem B1191959 : Blo 1190412 1191959 := bstep (se 1 (by rfl) ⟨893969, by rfl⟩ : syracuseStep 1191959 = 1787939) B1787939
theorem B1191979 : Blo 1190412 1191979 := bstep (se 1 (by rfl) ⟨893984, by rfl⟩ : syracuseStep 1191979 = 1787969) B1787969
theorem B1339447 : Blo 1190412 1339447 := bstep (se 1 (by rfl) ⟨1004585, by rfl⟩ : syracuseStep 1339447 = 2009171) B2009171
theorem B1191991 : Blo 1190412 1191991 := bstep (se 1 (by rfl) ⟨893993, by rfl⟩ : syracuseStep 1191991 = 1787987) B1787987
theorem B1192011 : Blo 1190412 1192011 := bstep (se 1 (by rfl) ⟨894008, by rfl⟩ : syracuseStep 1192011 = 1788017) B1788017
theorem B2011223 : Blo 1190412 2011223 := bstep (se 1 (by rfl) ⟨1508417, by rfl⟩ : syracuseStep 2011223 = 3016835) B3016835
theorem B1192023 : Blo 1190412 1192023 := bstep (se 1 (by rfl) ⟨894017, by rfl⟩ : syracuseStep 1192023 = 1788035) B1788035
theorem B1192043 : Blo 1190412 1192043 := bstep (se 1 (by rfl) ⟨894032, by rfl⟩ : syracuseStep 1192043 = 1788065) B1788065
theorem B1192055 : Blo 1190412 1192055 := bstep (se 1 (by rfl) ⟨894041, by rfl⟩ : syracuseStep 1192055 = 1788083) B1788083
theorem B1192075 : Blo 1190412 1192075 := bstep (se 1 (by rfl) ⟨894056, by rfl⟩ : syracuseStep 1192075 = 1788113) B1788113
theorem B5091473 : Blo 1190412 5091473 := bstep (se 2 (by rfl) ⟨1909302, by rfl⟩ : syracuseStep 5091473 = 3818605) B3818605
theorem B4526225 : Blo 1190412 4526225 := bstep (se 2 (by rfl) ⟨1697334, by rfl⟩ : syracuseStep 4526225 = 3394669) B3394669
theorem B1192087 : Blo 1190412 1192087 := bstep (se 1 (by rfl) ⟨894065, by rfl⟩ : syracuseStep 1192087 = 1788131) B1788131
theorem B1192107 : Blo 1190412 1192107 := bstep (se 1 (by rfl) ⟨894080, by rfl⟩ : syracuseStep 1192107 = 1788161) B1788161
theorem B4018355 : Blo 1190412 4018355 := bstep (se 1 (by rfl) ⟨3013766, by rfl⟩ : syracuseStep 4018355 = 6027533) B6027533
theorem B4075699 : Blo 1190412 4075699 := bstep (se 1 (by rfl) ⟨3056774, by rfl⟩ : syracuseStep 4075699 = 6113549) B6113549
theorem B1192119 : Blo 1190412 1192119 := bstep (se 1 (by rfl) ⟨894089, by rfl⟩ : syracuseStep 1192119 = 1788179) B1788179
theorem B1192139 : Blo 1190412 1192139 := bstep (se 1 (by rfl) ⟨894104, by rfl⟩ : syracuseStep 1192139 = 1788209) B1788209
theorem B2011351 : Blo 1190412 2011351 := bstep (se 1 (by rfl) ⟨1508513, by rfl⟩ : syracuseStep 2011351 = 3017027) B3017027
theorem B1192151 : Blo 1190412 1192151 := bstep (se 1 (by rfl) ⟨894113, by rfl⟩ : syracuseStep 1192151 = 1788227) B1788227
theorem B3625181 : Blo 1190412 3625181 := bstep (se 3 (by rfl) ⟨679721, by rfl⟩ : syracuseStep 3625181 = 1359443) B1359443
theorem B1339627 : Blo 1190412 1339627 := bstep (se 1 (by rfl) ⟨1004720, by rfl⟩ : syracuseStep 1339627 = 2009441) B2009441
theorem B1192171 : Blo 1190412 1192171 := bstep (se 1 (by rfl) ⟨894128, by rfl⟩ : syracuseStep 1192171 = 1788257) B1788257
theorem B1192183 : Blo 1190412 1192183 := bstep (se 1 (by rfl) ⟨894137, by rfl⟩ : syracuseStep 1192183 = 1788275) B1788275
theorem B1192203 : Blo 1190412 1192203 := bstep (se 1 (by rfl) ⟨894152, by rfl⟩ : syracuseStep 1192203 = 1788305) B1788305
theorem B1192215 : Blo 1190412 1192215 := bstep (se 1 (by rfl) ⟨894161, by rfl⟩ : syracuseStep 1192215 = 1788323) B1788323
theorem B1192235 : Blo 1190412 1192235 := bstep (se 1 (by rfl) ⟨894176, by rfl⟩ : syracuseStep 1192235 = 1788353) B1788353
theorem B1192247 : Blo 1190412 1192247 := bstep (se 1 (by rfl) ⟨894185, by rfl⟩ : syracuseStep 1192247 = 1788371) B1788371
theorem B10309963 : Blo 1190412 10309963 := bstep (se 1 (by rfl) ⟨7732472, by rfl⟩ : syracuseStep 10309963 = 15464945) B15464945
theorem B1192267 : Blo 1190412 1192267 := bstep (se 1 (by rfl) ⟨894200, by rfl⟩ : syracuseStep 1192267 = 1788401) B1788401
theorem B1339735 : Blo 1190412 1339735 := bstep (se 1 (by rfl) ⟨1004801, by rfl⟩ : syracuseStep 1339735 = 2009603) B2009603
theorem B1192279 : Blo 1190412 1192279 := bstep (se 1 (by rfl) ⟨894209, by rfl⟩ : syracuseStep 1192279 = 1788419) B1788419
theorem B4075865 : Blo 1190412 4075865 := bstep (se 2 (by rfl) ⟨1528449, by rfl⟩ : syracuseStep 4075865 = 3056899) B3056899
theorem B1192299 : Blo 1190412 1192299 := bstep (se 1 (by rfl) ⟨894224, by rfl⟩ : syracuseStep 1192299 = 1788449) B1788449
theorem B1192311 : Blo 1190412 1192311 := bstep (se 1 (by rfl) ⟨894233, by rfl⟩ : syracuseStep 1192311 = 1788467) B1788467
theorem B1192331 : Blo 1190412 1192331 := bstep (se 1 (by rfl) ⟨894248, by rfl⟩ : syracuseStep 1192331 = 1788497) B1788497
theorem B1192343 : Blo 1190412 1192343 := bstep (se 1 (by rfl) ⟨894257, by rfl⟩ : syracuseStep 1192343 = 1788515) B1788515
theorem B1192363 : Blo 1190412 1192363 := bstep (se 1 (by rfl) ⟨894272, by rfl⟩ : syracuseStep 1192363 = 1788545) B1788545
theorem B1192375 : Blo 1190412 1192375 := bstep (se 1 (by rfl) ⟨894281, by rfl⟩ : syracuseStep 1192375 = 1788563) B1788563
theorem B4018625 : Blo 1190412 4018625 := bstep (se 2 (by rfl) ⟨1506984, by rfl⟩ : syracuseStep 4018625 = 3013969) B3013969
theorem B1192395 : Blo 1190412 1192395 := bstep (se 1 (by rfl) ⟨894296, by rfl⟩ : syracuseStep 1192395 = 1788593) B1788593
theorem B1192407 : Blo 1190412 1192407 := bstep (se 1 (by rfl) ⟨894305, by rfl⟩ : syracuseStep 1192407 = 1788611) B1788611
theorem B1339915 : Blo 1190412 1339915 := bstep (se 1 (by rfl) ⟨1004936, by rfl⟩ : syracuseStep 1339915 = 2009873) B2009873
theorem B2863667 : Blo 1190412 2863667 := bstep (se 1 (by rfl) ⟨2147750, by rfl⟩ : syracuseStep 2863667 = 4295501) B4295501
theorem B3625523 : Blo 1190412 3625523 := bstep (se 1 (by rfl) ⟨2719142, by rfl⟩ : syracuseStep 3625523 = 5438285) B5438285
theorem B3265117 : Blo 1190412 3265117 := bstep (se 3 (by rfl) ⟨612209, by rfl⟩ : syracuseStep 3265117 = 1224419) B1224419
theorem B6034013 : Blo 1190412 6034013 := bstep (se 3 (by rfl) ⟨1131377, by rfl⟩ : syracuseStep 6034013 = 2262755) B2262755
theorem B1340023 : Blo 1190412 1340023 := bstep (se 1 (by rfl) ⟨1005017, by rfl⟩ : syracuseStep 1340023 = 2010035) B2010035
theorem B4829975 : Blo 1190412 4829975 := bstep (se 1 (by rfl) ⟨3622481, by rfl⟩ : syracuseStep 4829975 = 7244963) B7244963
theorem B1340203 : Blo 1190412 1340203 := bstep (se 1 (by rfl) ⟨1005152, by rfl⟩ : syracuseStep 1340203 = 2010305) B2010305
theorem B2011979 : Blo 1190412 2011979 := bstep (se 1 (by rfl) ⟨1508984, by rfl⟩ : syracuseStep 2011979 = 3017969) B3017969
theorem B2544473 : Blo 1190412 2544473 := bstep (se 2 (by rfl) ⟨954177, by rfl⟩ : syracuseStep 2544473 = 1908355) B1908355
theorem B9163651 : Blo 1190412 9163651 := bstep (se 1 (by rfl) ⟨6872738, by rfl⟩ : syracuseStep 9163651 = 13745477) B13745477
theorem B1340311 : Blo 1190412 1340311 := bstep (se 1 (by rfl) ⟨1005233, by rfl⟩ : syracuseStep 1340311 = 2010467) B2010467
theorem B4526999 : Blo 1190412 4526999 := bstep (se 1 (by rfl) ⟨3395249, by rfl⟩ : syracuseStep 4526999 = 6790499) B6790499
theorem B4355009 : Blo 1190412 4355009 := bstep (se 2 (by rfl) ⟨1633128, by rfl⟩ : syracuseStep 4355009 = 3266257) B3266257
theorem B2012107 : Blo 1190412 2012107 := bstep (se 1 (by rfl) ⟨1509080, by rfl⟩ : syracuseStep 2012107 = 3018161) B3018161
theorem B4019165 : Blo 1190412 4019165 := bstep (se 3 (by rfl) ⟨753593, by rfl⟩ : syracuseStep 4019165 = 1507187) B1507187
theorem B2176001 : Blo 1190412 2176001 := bstep (se 2 (by rfl) ⟨816000, by rfl⟩ : syracuseStep 2176001 = 1632001) B1632001
theorem B18600995 : Blo 1190412 18600995 := bstep (se 1 (by rfl) ⟨13950746, by rfl⟩ : syracuseStep 18600995 = 27901493) B27901493
theorem B1340491 : Blo 1190412 1340491 := bstep (se 1 (by rfl) ⟨1005368, by rfl⟩ : syracuseStep 1340491 = 2010737) B2010737
theorem B2716759 : Blo 1190412 2716759 := bstep (se 1 (by rfl) ⟨2037569, by rfl⟩ : syracuseStep 2716759 = 4075139) B4075139
theorem B4527197 : Blo 1190412 4527197 := bstep (se 3 (by rfl) ⟨848849, by rfl⟩ : syracuseStep 4527197 = 1697699) B1697699
theorem B1340599 : Blo 1190412 1340599 := bstep (se 1 (by rfl) ⟨1005449, by rfl⟩ : syracuseStep 1340599 = 2010899) B2010899
theorem B6026561 : Blo 1190412 6026561 := bstep (se 2 (by rfl) ⟨2259960, by rfl⟩ : syracuseStep 6026561 = 4519921) B4519921
theorem B1340779 : Blo 1190412 1340779 := bstep (se 1 (by rfl) ⟨1005584, by rfl⟩ : syracuseStep 1340779 = 2011169) B2011169
theorem B5092739 : Blo 1190412 5092739 := bstep (se 1 (by rfl) ⟨3819554, by rfl⟩ : syracuseStep 5092739 = 7639109) B7639109
theorem B1340887 : Blo 1190412 1340887 := bstep (se 1 (by rfl) ⟨1005665, by rfl⟩ : syracuseStep 1340887 = 2011331) B2011331
theorem B13579811 : Blo 1190412 13579811 := bstep (se 1 (by rfl) ⟨10184858, by rfl⟩ : syracuseStep 13579811 = 20369717) B20369717
theorem B10171979 : Blo 1190412 10171979 := bstep (se 1 (by rfl) ⟨7628984, by rfl⟩ : syracuseStep 10171979 = 15257969) B15257969
theorem B1341067 : Blo 1190412 1341067 := bstep (se 1 (by rfl) ⟨1005800, by rfl⟩ : syracuseStep 1341067 = 2011601) B2011601
theorem B9049805 : Blo 1190412 9049805 := bstep (se 3 (by rfl) ⟨1696838, by rfl⟩ : syracuseStep 9049805 = 3393677) B3393677
theorem B1341175 : Blo 1190412 1341175 := bstep (se 1 (by rfl) ⟨1005881, by rfl⟩ : syracuseStep 1341175 = 2011763) B2011763
theorem B6616849 : Blo 1190412 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B10319633 : Blo 1190412 10319633 := bstep (se 2 (by rfl) ⟨3869862, by rfl⟩ : syracuseStep 10319633 = 7739725) B7739725
theorem B1341355 : Blo 1190412 1341355 := bstep (se 1 (by rfl) ⟨1006016, by rfl⟩ : syracuseStep 1341355 = 2012033) B2012033
theorem B9656243 : Blo 1190412 9656243 := bstep (se 1 (by rfl) ⟨7242182, by rfl⟩ : syracuseStep 9656243 = 14484365) B14484365
theorem B1341463 : Blo 1190412 1341463 := bstep (se 1 (by rfl) ⟨1006097, by rfl⟩ : syracuseStep 1341463 = 2012195) B2012195
theorem B4020299 : Blo 1190412 4020299 := bstep (se 1 (by rfl) ⟨3015224, by rfl⟩ : syracuseStep 4020299 = 6030449) B6030449
theorem B9050291 : Blo 1190412 9050291 := bstep (se 1 (by rfl) ⟨6787718, by rfl⟩ : syracuseStep 9050291 = 13575437) B13575437
theorem B4520195 : Blo 1190412 4520195 := bstep (se 1 (by rfl) ⟨3390146, by rfl⟩ : syracuseStep 4520195 = 6780293) B6780293
theorem B5085443 : Blo 1190412 5085443 := bstep (se 1 (by rfl) ⟨3814082, by rfl⟩ : syracuseStep 5085443 = 7628165) B7628165
theorem B4020569 : Blo 1190412 4020569 := bstep (se 2 (by rfl) ⟨1507713, by rfl⟩ : syracuseStep 4020569 = 3015427) B3015427
theorem B2546113 : Blo 1190412 2546113 := bstep (se 2 (by rfl) ⟨954792, by rfl⟩ : syracuseStep 2546113 = 1909585) B1909585
theorem B3013271 : Blo 1190412 3013271 := bstep (se 1 (by rfl) ⟨2259953, by rfl⟩ : syracuseStep 3013271 = 4519907) B4519907
theorem B6036119 : Blo 1190412 6036119 := bstep (se 1 (by rfl) ⟨4527089, by rfl⟩ : syracuseStep 6036119 = 9054179) B9054179
theorem B10861235 : Blo 1190412 10861235 := bstep (se 1 (by rfl) ⟨8145926, by rfl⟩ : syracuseStep 10861235 = 16291853) B16291853
theorem B3390169 : Blo 1190412 3390169 := bstep (se 2 (by rfl) ⟨1271313, by rfl⟩ : syracuseStep 3390169 = 2542627) B2542627
theorem B4832131 : Blo 1190412 4832131 := bstep (se 1 (by rfl) ⟨3624098, by rfl⟩ : syracuseStep 4832131 = 7248197) B7248197
theorem B6790067 : Blo 1190412 6790067 := bstep (se 1 (by rfl) ⟨5092550, by rfl⟩ : syracuseStep 6790067 = 10185101) B10185101
theorem B66059225 : Blo 1190412 66059225 := bstep (se 2 (by rfl) ⟨24772209, by rfl⟩ : syracuseStep 66059225 = 49544419) B49544419
theorem B3218393 : Blo 1190412 3218393 := bstep (se 2 (by rfl) ⟨1206897, by rfl⟩ : syracuseStep 3218393 = 2413795) B2413795
theorem B21740557 : Blo 1190412 21740557 := bstep (se 3 (by rfl) ⟨4076354, by rfl⟩ : syracuseStep 21740557 = 8152709) B8152709
theorem B2259991 : Blo 1190412 2259991 := bstep (se 1 (by rfl) ⟨1694993, by rfl⟩ : syracuseStep 2259991 = 3389987) B3389987
theorem B4021271 : Blo 1190412 4021271 := bstep (se 1 (by rfl) ⟨3015953, by rfl⟩ : syracuseStep 4021271 = 6031907) B6031907
theorem B6028505 : Blo 1190412 6028505 := bstep (se 2 (by rfl) ⟨2260689, by rfl⟩ : syracuseStep 6028505 = 4521379) B4521379
theorem B2145601 : Blo 1190412 2145601 := bstep (se 2 (by rfl) ⟨804600, by rfl⟩ : syracuseStep 2145601 = 1609201) B1609201
theorem B3390785 : Blo 1190412 3390785 := bstep (se 2 (by rfl) ⟨1271544, by rfl⟩ : syracuseStep 3390785 = 2543089) B2543089
theorem B3014081 : Blo 1190412 3014081 := bstep (se 2 (by rfl) ⟨1130280, by rfl⟩ : syracuseStep 3014081 = 2260561) B2260561
theorem B6438361 : Blo 1190412 6438361 := bstep (se 2 (by rfl) ⟨2414385, by rfl⟩ : syracuseStep 6438361 = 4828771) B4828771
theorem B4021811 : Blo 1190412 4021811 := bstep (se 1 (by rfl) ⟨3016358, by rfl⟩ : syracuseStep 4021811 = 6032717) B6032717
theorem B7241309 : Blo 1190412 7241309 := bstep (se 3 (by rfl) ⟨1357745, by rfl⟩ : syracuseStep 7241309 = 2715491) B2715491
theorem B9051749 : Blo 1190412 9051749 := bstep (se 4 (by rfl) ⟨848601, by rfl⟩ : syracuseStep 9051749 = 1697203) B1697203
theorem B4292227 : Blo 1190412 4292227 := bstep (se 1 (by rfl) ⟨3219170, by rfl⟩ : syracuseStep 4292227 = 6438341) B6438341
theorem B2416267 : Blo 1190412 2416267 := bstep (se 1 (by rfl) ⟨1812200, by rfl⟩ : syracuseStep 2416267 = 3624401) B3624401
theorem B1359511 : Blo 1190412 1359511 := bstep (se 1 (by rfl) ⟨1019633, by rfl⟩ : syracuseStep 1359511 = 2039267) B2039267
theorem B2678489 : Blo 1190412 2678489 := bstep (se 2 (by rfl) ⟨1004433, by rfl⟩ : syracuseStep 2678489 = 2008867) B2008867
theorem B1695449 : Blo 1190412 1695449 := bstep (se 2 (by rfl) ⟨635793, by rfl⟩ : syracuseStep 1695449 = 1271587) B1271587
theorem B1785623 : Blo 1190412 1785623 := bstep (se 1 (by rfl) ⟨1339217, by rfl⟩ : syracuseStep 1785623 = 2678435) B2678435
theorem B2678579 : Blo 1190412 2678579 := bstep (se 1 (by rfl) ⟨2008934, by rfl⟩ : syracuseStep 2678579 = 4017869) B4017869
theorem B4128563 : Blo 1190412 4128563 := bstep (se 1 (by rfl) ⟨3096422, by rfl⟩ : syracuseStep 4128563 = 6192845) B6192845
theorem B4022081 : Blo 1190412 4022081 := bstep (se 2 (by rfl) ⟨1508280, by rfl⟩ : syracuseStep 4022081 = 3016561) B3016561
theorem B2260811 : Blo 1190412 2260811 := bstep (se 1 (by rfl) ⟨1695608, by rfl⟩ : syracuseStep 2260811 = 3391217) B3391217
theorem B2678615 : Blo 1190412 2678615 := bstep (se 1 (by rfl) ⟨2008961, by rfl⟩ : syracuseStep 2678615 = 4017923) B4017923
theorem B1785689 : Blo 1190412 1785689 := bstep (se 2 (by rfl) ⟨669633, by rfl⟩ : syracuseStep 1785689 = 1339267) B1339267
theorem B5726045 : Blo 1190412 5726045 := bstep (se 3 (by rfl) ⟨1073633, by rfl⟩ : syracuseStep 5726045 = 2147267) B2147267
theorem B2260865 : Blo 1190412 2260865 := bstep (se 2 (by rfl) ⟨847824, by rfl⟩ : syracuseStep 2260865 = 1695649) B1695649
theorem B1810315 : Blo 1190412 1810315 := bstep (se 1 (by rfl) ⟨1357736, by rfl⟩ : syracuseStep 1810315 = 2715473) B2715473
theorem B3620801 : Blo 1190412 3620801 := bstep (se 2 (by rfl) ⟨1357800, by rfl⟩ : syracuseStep 3620801 = 2715601) B2715601
theorem B1785803 : Blo 1190412 1785803 := bstep (se 1 (by rfl) ⟨1339352, by rfl⟩ : syracuseStep 1785803 = 2678705) B2678705
theorem B1785815 : Blo 1190412 1785815 := bstep (se 1 (by rfl) ⟨1339361, by rfl⟩ : syracuseStep 1785815 = 2678723) B2678723
theorem B3014617 : Blo 1190412 3014617 := bstep (se 2 (by rfl) ⟨1130481, by rfl⟩ : syracuseStep 3014617 = 2260963) B2260963
theorem B2146265 : Blo 1190412 2146265 := bstep (se 2 (by rfl) ⟨804849, by rfl⟩ : syracuseStep 2146265 = 1609699) B1609699
theorem B6029315 : Blo 1190412 6029315 := bstep (se 1 (by rfl) ⟨4521986, by rfl⟩ : syracuseStep 6029315 = 9043973) B9043973
theorem B1785863 : Blo 1190412 1785863 := bstep (se 1 (by rfl) ⟨1339397, by rfl⟩ : syracuseStep 1785863 = 2678795) B2678795
theorem B1785899 : Blo 1190412 1785899 := bstep (se 1 (by rfl) ⟨1339424, by rfl⟩ : syracuseStep 1785899 = 2678849) B2678849
theorem B3219517 : Blo 1190412 3219517 := bstep (se 3 (by rfl) ⟨603659, by rfl⟩ : syracuseStep 3219517 = 1207319) B1207319
theorem B7241795 : Blo 1190412 7241795 := bstep (se 1 (by rfl) ⟨5431346, by rfl⟩ : syracuseStep 7241795 = 10862693) B10862693
theorem B1785929 : Blo 1190412 1785929 := bstep (se 2 (by rfl) ⟨669723, by rfl⟩ : syracuseStep 1785929 = 1339447) B1339447
theorem B2678903 : Blo 1190412 2678903 := bstep (se 1 (by rfl) ⟨2009177, by rfl⟩ : syracuseStep 2678903 = 4018355) B4018355
theorem B2146439 : Blo 1190412 2146439 := bstep (se 1 (by rfl) ⟨1609829, by rfl⟩ : syracuseStep 2146439 = 3219659) B3219659
theorem B2416787 : Blo 1190412 2416787 := bstep (se 1 (by rfl) ⟨1812590, by rfl⟩ : syracuseStep 2416787 = 3625181) B3625181
theorem B11452589 : Blo 1190412 11452589 := bstep (se 3 (by rfl) ⟨2147360, by rfl⟩ : syracuseStep 11452589 = 4294721) B4294721
theorem B1786043 : Blo 1190412 1786043 := bstep (se 1 (by rfl) ⟨1339532, by rfl⟩ : syracuseStep 1786043 = 2679065) B2679065
theorem B1786103 : Blo 1190412 1786103 := bstep (se 1 (by rfl) ⟨1339577, by rfl⟩ : syracuseStep 1786103 = 2679155) B2679155
theorem B1786127 : Blo 1190412 1786127 := bstep (se 1 (by rfl) ⟨1339595, by rfl⟩ : syracuseStep 1786127 = 2679191) B2679191
theorem B2679083 : Blo 1190412 2679083 := bstep (se 1 (by rfl) ⟨2009312, by rfl⟩ : syracuseStep 2679083 = 4018625) B4018625
theorem B3391787 : Blo 1190412 3391787 := bstep (se 1 (by rfl) ⟨2543840, by rfl⟩ : syracuseStep 3391787 = 5087681) B5087681
theorem B1786169 : Blo 1190412 1786169 := bstep (se 2 (by rfl) ⟨669813, by rfl⟩ : syracuseStep 1786169 = 1339627) B1339627
theorem B1909111 : Blo 1190412 1909111 := bstep (se 1 (by rfl) ⟨1431833, by rfl⟩ : syracuseStep 1909111 = 2863667) B2863667
theorem B2417015 : Blo 1190412 2417015 := bstep (se 1 (by rfl) ⟨1812761, by rfl⟩ : syracuseStep 2417015 = 3625523) B3625523
theorem B1786247 : Blo 1190412 1786247 := bstep (se 1 (by rfl) ⟨1339685, by rfl⟩ : syracuseStep 1786247 = 2679371) B2679371
theorem B4022675 : Blo 1190412 4022675 := bstep (se 1 (by rfl) ⟨3017006, by rfl⟩ : syracuseStep 4022675 = 6034013) B6034013
theorem B1786283 : Blo 1190412 1786283 := bstep (se 1 (by rfl) ⟨1339712, by rfl⟩ : syracuseStep 1786283 = 2679425) B2679425
theorem B13746617 : Blo 1190412 13746617 := bstep (se 2 (by rfl) ⟨5154981, by rfl⟩ : syracuseStep 13746617 = 10309963) B10309963
theorem B1786313 : Blo 1190412 1786313 := bstep (se 2 (by rfl) ⟨669867, by rfl⟩ : syracuseStep 1786313 = 1339735) B1339735
theorem B2261449 : Blo 1190412 2261449 := bstep (se 2 (by rfl) ⟨848043, by rfl⟩ : syracuseStep 2261449 = 1696087) B1696087
theorem B3219983 : Blo 1190412 3219983 := bstep (se 1 (by rfl) ⟨2414987, by rfl⟩ : syracuseStep 3219983 = 4829975) B4829975
theorem B1786427 : Blo 1190412 1786427 := bstep (se 1 (by rfl) ⟨1339820, by rfl⟩ : syracuseStep 1786427 = 2679641) B2679641
theorem B1696315 : Blo 1190412 1696315 := bstep (se 1 (by rfl) ⟨1272236, by rfl⟩ : syracuseStep 1696315 = 2544473) B2544473
theorem B9175619 : Blo 1190412 9175619 := bstep (se 1 (by rfl) ⟨6881714, by rfl⟩ : syracuseStep 9175619 = 13763429) B13763429
theorem B1786487 : Blo 1190412 1786487 := bstep (se 1 (by rfl) ⟨1339865, by rfl⟩ : syracuseStep 1786487 = 2679731) B2679731
theorem B1786511 : Blo 1190412 1786511 := bstep (se 1 (by rfl) ⟨1339883, by rfl⟩ : syracuseStep 1786511 = 2679767) B2679767
theorem B2679443 : Blo 1190412 2679443 := bstep (se 1 (by rfl) ⟨2009582, by rfl⟩ : syracuseStep 2679443 = 4019165) B4019165
theorem B1450667 : Blo 1190412 1450667 := bstep (se 1 (by rfl) ⟨1088000, by rfl⟩ : syracuseStep 1450667 = 2176001) B2176001
theorem B1786553 : Blo 1190412 1786553 := bstep (se 2 (by rfl) ⟨669957, by rfl⟩ : syracuseStep 1786553 = 1339915) B1339915
theorem B2679497 : Blo 1190412 2679497 := bstep (se 2 (by rfl) ⟨1004811, by rfl⟩ : syracuseStep 2679497 = 2009623) B2009623
theorem B1786631 : Blo 1190412 1786631 := bstep (se 1 (by rfl) ⟨1339973, by rfl⟩ : syracuseStep 1786631 = 2679947) B2679947
theorem B7250725 : Blo 1190412 7250725 := bstep (se 4 (by rfl) ⟨679755, by rfl⟩ : syracuseStep 7250725 = 1359511) B1359511
theorem B1786667 : Blo 1190412 1786667 := bstep (se 1 (by rfl) ⟨1340000, by rfl⟩ : syracuseStep 1786667 = 2680001) B2680001
theorem B1786697 : Blo 1190412 1786697 := bstep (se 2 (by rfl) ⟨670011, by rfl⟩ : syracuseStep 1786697 = 1340023) B1340023
theorem B32596825 : Blo 1190412 32596825 := bstep (se 2 (by rfl) ⟨12223809, by rfl⟩ : syracuseStep 32596825 = 24447619) B24447619
theorem B3015539 : Blo 1190412 3015539 := bstep (se 1 (by rfl) ⟨2261654, by rfl⟩ : syracuseStep 3015539 = 4523309) B4523309
theorem B1508215 : Blo 1190412 1508215 := bstep (se 1 (by rfl) ⟨1131161, by rfl⟩ : syracuseStep 1508215 = 2262323) B2262323
theorem B1786811 : Blo 1190412 1786811 := bstep (se 1 (by rfl) ⟨1340108, by rfl⟩ : syracuseStep 1786811 = 2680217) B2680217
theorem B1786871 : Blo 1190412 1786871 := bstep (se 1 (by rfl) ⟨1340153, by rfl⟩ : syracuseStep 1786871 = 2680307) B2680307
theorem B1786895 : Blo 1190412 1786895 := bstep (se 1 (by rfl) ⟨1340171, by rfl⟩ : syracuseStep 1786895 = 2680343) B2680343
theorem B9053207 : Blo 1190412 9053207 := bstep (se 1 (by rfl) ⟨6789905, by rfl⟩ : syracuseStep 9053207 = 13579811) B13579811
theorem B1786937 : Blo 1190412 1786937 := bstep (se 2 (by rfl) ⟨670101, by rfl⟩ : syracuseStep 1786937 = 1340203) B1340203
theorem B5727293 : Blo 1190412 5727293 := bstep (se 3 (by rfl) ⟨1073867, by rfl⟩ : syracuseStep 5727293 = 2147735) B2147735
theorem B1787015 : Blo 1190412 1787015 := bstep (se 1 (by rfl) ⟨1340261, by rfl⟩ : syracuseStep 1787015 = 2680523) B2680523
theorem B2262163 : Blo 1190412 2262163 := bstep (se 1 (by rfl) ⟨1696622, by rfl⟩ : syracuseStep 2262163 = 3393245) B3393245
theorem B1787051 : Blo 1190412 1787051 := bstep (se 1 (by rfl) ⟨1340288, by rfl⟩ : syracuseStep 1787051 = 2680577) B2680577
theorem B1508539 : Blo 1190412 1508539 := bstep (se 1 (by rfl) ⟨1131404, by rfl⟩ : syracuseStep 1508539 = 2262809) B2262809
theorem B1787081 : Blo 1190412 1787081 := bstep (se 2 (by rfl) ⟨670155, by rfl⟩ : syracuseStep 1787081 = 1340311) B1340311
theorem B4523323 : Blo 1190412 4523323 := bstep (se 1 (by rfl) ⟨3392492, by rfl⟩ : syracuseStep 4523323 = 6784985) B6784985
theorem B1787195 : Blo 1190412 1787195 := bstep (se 1 (by rfl) ⟨1340396, by rfl⟩ : syracuseStep 1787195 = 2680793) B2680793
theorem B3622259 : Blo 1190412 3622259 := bstep (se 1 (by rfl) ⟨2716694, by rfl⟩ : syracuseStep 3622259 = 5433389) B5433389
theorem B1787255 : Blo 1190412 1787255 := bstep (se 1 (by rfl) ⟨1340441, by rfl⟩ : syracuseStep 1787255 = 2680883) B2680883
theorem B3016055 : Blo 1190412 3016055 := bstep (se 1 (by rfl) ⟨2262041, by rfl⟩ : syracuseStep 3016055 = 4524083) B4524083
theorem B2680199 : Blo 1190412 2680199 := bstep (se 1 (by rfl) ⟨2010149, by rfl⟩ : syracuseStep 2680199 = 4020299) B4020299
theorem B3392903 : Blo 1190412 3392903 := bstep (se 1 (by rfl) ⟨2544677, by rfl⟩ : syracuseStep 3392903 = 5089355) B5089355
theorem B1787279 : Blo 1190412 1787279 := bstep (se 1 (by rfl) ⟨1340459, by rfl⟩ : syracuseStep 1787279 = 2680919) B2680919
theorem B4294073 : Blo 1190412 4294073 := bstep (se 2 (by rfl) ⟨1610277, by rfl⟩ : syracuseStep 4294073 = 3220555) B3220555
theorem B1787321 : Blo 1190412 1787321 := bstep (se 2 (by rfl) ⟨670245, by rfl⟩ : syracuseStep 1787321 = 1340491) B1340491
theorem B1787399 : Blo 1190412 1787399 := bstep (se 1 (by rfl) ⟨1340549, by rfl⟩ : syracuseStep 1787399 = 2681099) B2681099
theorem B1787435 : Blo 1190412 1787435 := bstep (se 1 (by rfl) ⟨1340576, by rfl⟩ : syracuseStep 1787435 = 2681153) B2681153
theorem B2680379 : Blo 1190412 2680379 := bstep (se 1 (by rfl) ⟨2010284, by rfl⟩ : syracuseStep 2680379 = 4020569) B4020569
theorem B3393085 : Blo 1190412 3393085 := bstep (se 3 (by rfl) ⟨636203, by rfl⟩ : syracuseStep 3393085 = 1272407) B1272407
theorem B1787465 : Blo 1190412 1787465 := bstep (se 2 (by rfl) ⟨670299, by rfl⟩ : syracuseStep 1787465 = 1340599) B1340599
theorem B6030935 : Blo 1190412 6030935 := bstep (se 1 (by rfl) ⟨4523201, by rfl⟩ : syracuseStep 6030935 = 9046403) B9046403
theorem B2147959 : Blo 1190412 2147959 := bstep (se 1 (by rfl) ⟨1610969, by rfl⟩ : syracuseStep 2147959 = 3221939) B3221939
theorem B2680505 : Blo 1190412 2680505 := bstep (se 2 (by rfl) ⟨1005189, by rfl⟩ : syracuseStep 2680505 = 2010379) B2010379
theorem B1787579 : Blo 1190412 1787579 := bstep (se 1 (by rfl) ⟨1340684, by rfl⟩ : syracuseStep 1787579 = 2681369) B2681369
theorem B1787639 : Blo 1190412 1787639 := bstep (se 1 (by rfl) ⟨1340729, by rfl⟩ : syracuseStep 1787639 = 2681459) B2681459
theorem B2860801 : Blo 1190412 2860801 := bstep (se 2 (by rfl) ⟨1072800, by rfl⟩ : syracuseStep 2860801 = 2145601) B2145601
theorem B2008847 : Blo 1190412 2008847 := bstep (se 1 (by rfl) ⟨1506635, by rfl⟩ : syracuseStep 2008847 = 3013271) B3013271
theorem B1787663 : Blo 1190412 1787663 := bstep (se 1 (by rfl) ⟨1340747, by rfl⟩ : syracuseStep 1787663 = 2681495) B2681495
theorem B4024079 : Blo 1190412 4024079 := bstep (se 1 (by rfl) ⟨3018059, by rfl⟩ : syracuseStep 4024079 = 6036119) B6036119
theorem B4523809 : Blo 1190412 4523809 := bstep (se 2 (by rfl) ⟨1696428, by rfl⟩ : syracuseStep 4523809 = 3392857) B3392857
theorem B1787705 : Blo 1190412 1787705 := bstep (se 2 (by rfl) ⟨670389, by rfl⟩ : syracuseStep 1787705 = 1340779) B1340779
theorem B1787783 : Blo 1190412 1787783 := bstep (se 1 (by rfl) ⟨1340837, by rfl⟩ : syracuseStep 1787783 = 2681675) B2681675
theorem B4294547 : Blo 1190412 4294547 := bstep (se 1 (by rfl) ⟨3220910, by rfl⟩ : syracuseStep 4294547 = 6441821) B6441821
theorem B3393427 : Blo 1190412 3393427 := bstep (se 1 (by rfl) ⟨2545070, by rfl⟩ : syracuseStep 3393427 = 5090141) B5090141
theorem B1787819 : Blo 1190412 1787819 := bstep (se 1 (by rfl) ⟨1340864, by rfl⟩ : syracuseStep 1787819 = 2681729) B2681729
theorem B1787849 : Blo 1190412 1787849 := bstep (se 2 (by rfl) ⟨670443, by rfl⟩ : syracuseStep 1787849 = 1340887) B1340887
theorem B2680847 : Blo 1190412 2680847 := bstep (se 1 (by rfl) ⟨2010635, by rfl⟩ : syracuseStep 2680847 = 4021271) B4021271
theorem B4024349 : Blo 1190412 4024349 := bstep (se 3 (by rfl) ⟨754565, by rfl⟩ : syracuseStep 4024349 = 1509131) B1509131
theorem B2680865 : Blo 1190412 2680865 := bstep (se 2 (by rfl) ⟨1005324, by rfl⟩ : syracuseStep 2680865 = 2010649) B2010649
theorem B1787963 : Blo 1190412 1787963 := bstep (se 1 (by rfl) ⟨1340972, by rfl⟩ : syracuseStep 1787963 = 2681945) B2681945
theorem B6031421 : Blo 1190412 6031421 := bstep (se 3 (by rfl) ⟨1130891, by rfl⟩ : syracuseStep 6031421 = 2261783) B2261783
theorem B1788023 : Blo 1190412 1788023 := bstep (se 1 (by rfl) ⟨1341017, by rfl⟩ : syracuseStep 1788023 = 2682035) B2682035
theorem B1788047 : Blo 1190412 1788047 := bstep (se 1 (by rfl) ⟨1341035, by rfl⟩ : syracuseStep 1788047 = 2682071) B2682071
theorem B3221689 : Blo 1190412 3221689 := bstep (se 2 (by rfl) ⟨1208133, by rfl⟩ : syracuseStep 3221689 = 2416267) B2416267
theorem B1788089 : Blo 1190412 1788089 := bstep (se 2 (by rfl) ⟨670533, by rfl⟩ : syracuseStep 1788089 = 1341067) B1341067
theorem B2263241 : Blo 1190412 2263241 := bstep (se 2 (by rfl) ⟨848715, by rfl⟩ : syracuseStep 2263241 = 1697431) B1697431
theorem B1788167 : Blo 1190412 1788167 := bstep (se 1 (by rfl) ⟨1341125, by rfl⟩ : syracuseStep 1788167 = 2682251) B2682251
theorem B2009387 : Blo 1190412 2009387 := bstep (se 1 (by rfl) ⟨1507040, by rfl⟩ : syracuseStep 2009387 = 3014081) B3014081
theorem B1788203 : Blo 1190412 1788203 := bstep (se 1 (by rfl) ⟨1341152, by rfl⟩ : syracuseStep 1788203 = 2682305) B2682305
theorem B3819835 : Blo 1190412 3819835 := bstep (se 1 (by rfl) ⟨2864876, by rfl⟩ : syracuseStep 3819835 = 5729753) B5729753
theorem B1788233 : Blo 1190412 1788233 := bstep (se 2 (by rfl) ⟨670587, by rfl⟩ : syracuseStep 1788233 = 1341175) B1341175
theorem B3017047 : Blo 1190412 3017047 := bstep (se 1 (by rfl) ⟨2262785, by rfl⟩ : syracuseStep 3017047 = 4525571) B4525571
theorem B2681207 : Blo 1190412 2681207 := bstep (se 1 (by rfl) ⟨2010905, by rfl⟩ : syracuseStep 2681207 = 4021811) B4021811
theorem B4827539 : Blo 1190412 4827539 := bstep (se 1 (by rfl) ⟨3620654, by rfl⟩ : syracuseStep 4827539 = 7241309) B7241309
theorem B1788347 : Blo 1190412 1788347 := bstep (se 1 (by rfl) ⟨1341260, by rfl⟩ : syracuseStep 1788347 = 2682521) B2682521
theorem B5884363 : Blo 1190412 5884363 := bstep (se 1 (by rfl) ⟨4413272, by rfl⟩ : syracuseStep 5884363 = 8826545) B8826545
theorem B1788407 : Blo 1190412 1788407 := bstep (se 1 (by rfl) ⟨1341305, by rfl⟩ : syracuseStep 1788407 = 2682611) B2682611
theorem B1190415 : Blo 1190412 1190415 := bstep (se 1 (by rfl) ⟨892811, by rfl⟩ : syracuseStep 1190415 = 1785623) B1785623
theorem B1788431 : Blo 1190412 1788431 := bstep (se 1 (by rfl) ⟨1341323, by rfl⟩ : syracuseStep 1788431 = 2682647) B2682647
theorem B2681387 : Blo 1190412 2681387 := bstep (se 1 (by rfl) ⟨2011040, by rfl⟩ : syracuseStep 2681387 = 4022081) B4022081
theorem B1788473 : Blo 1190412 1788473 := bstep (se 2 (by rfl) ⟨670677, by rfl⟩ : syracuseStep 1788473 = 1341355) B1341355
theorem B1190459 : Blo 1190412 1190459 := bstep (se 1 (by rfl) ⟨892844, by rfl⟩ : syracuseStep 1190459 = 1785689) B1785689
theorem B6113879 : Blo 1190412 6113879 := bstep (se 1 (by rfl) ⟨4585409, by rfl⟩ : syracuseStep 6113879 = 9170819) B9170819
theorem B1190535 : Blo 1190412 1190535 := bstep (se 1 (by rfl) ⟨892901, by rfl⟩ : syracuseStep 1190535 = 1785803) B1785803
theorem B3017351 : Blo 1190412 3017351 := bstep (se 1 (by rfl) ⟨2263013, by rfl⟩ : syracuseStep 3017351 = 4526027) B4526027
theorem B1788551 : Blo 1190412 1788551 := bstep (se 1 (by rfl) ⟨1341413, by rfl⟩ : syracuseStep 1788551 = 2682827) B2682827
theorem B1190543 : Blo 1190412 1190543 := bstep (se 1 (by rfl) ⟨892907, by rfl⟩ : syracuseStep 1190543 = 1785815) B1785815
theorem B1788587 : Blo 1190412 1788587 := bstep (se 1 (by rfl) ⟨1341440, by rfl⟩ : syracuseStep 1788587 = 2682881) B2682881
theorem B2009785 : Blo 1190412 2009785 := bstep (se 2 (by rfl) ⟨753669, by rfl⟩ : syracuseStep 2009785 = 1507339) B1507339
theorem B1190587 : Blo 1190412 1190587 := bstep (se 1 (by rfl) ⟨892940, by rfl⟩ : syracuseStep 1190587 = 1785881) B1785881
theorem B1788617 : Blo 1190412 1788617 := bstep (se 2 (by rfl) ⟨670731, by rfl⟩ : syracuseStep 1788617 = 1341463) B1341463
theorem B4524781 : Blo 1190412 4524781 := bstep (se 3 (by rfl) ⟨848396, by rfl⟩ : syracuseStep 4524781 = 1696793) B1696793
theorem B1190663 : Blo 1190412 1190663 := bstep (se 1 (by rfl) ⟨892997, by rfl⟩ : syracuseStep 1190663 = 1785995) B1785995
theorem B3394315 : Blo 1190412 3394315 := bstep (se 1 (by rfl) ⟨2545736, by rfl⟩ : syracuseStep 3394315 = 5091473) B5091473
theorem B3017483 : Blo 1190412 3017483 := bstep (se 1 (by rfl) ⟨2263112, by rfl⟩ : syracuseStep 3017483 = 4526225) B4526225
theorem B1190671 : Blo 1190412 1190671 := bstep (se 1 (by rfl) ⟨893003, by rfl⟩ : syracuseStep 1190671 = 1786007) B1786007
theorem B1190715 : Blo 1190412 1190715 := bstep (se 1 (by rfl) ⟨893036, by rfl⟩ : syracuseStep 1190715 = 1786073) B1786073
theorem B1190791 : Blo 1190412 1190791 := bstep (se 1 (by rfl) ⟨893093, by rfl⟩ : syracuseStep 1190791 = 1786187) B1786187
theorem B1190799 : Blo 1190412 1190799 := bstep (se 1 (by rfl) ⟨893099, by rfl⟩ : syracuseStep 1190799 = 1786199) B1786199
theorem B2681747 : Blo 1190412 2681747 := bstep (se 1 (by rfl) ⟨2011310, by rfl⟩ : syracuseStep 2681747 = 4022621) B4022621
theorem B5434265 : Blo 1190412 5434265 := bstep (se 2 (by rfl) ⟨2037849, by rfl⟩ : syracuseStep 5434265 = 4075699) B4075699
theorem B11447203 : Blo 1190412 11447203 := bstep (se 1 (by rfl) ⟨8585402, by rfl⟩ : syracuseStep 11447203 = 17170805) B17170805
theorem B1190843 : Blo 1190412 1190843 := bstep (se 1 (by rfl) ⟨893132, by rfl⟩ : syracuseStep 1190843 = 1786265) B1786265
theorem B2681801 : Blo 1190412 2681801 := bstep (se 2 (by rfl) ⟨1005675, by rfl⟩ : syracuseStep 2681801 = 2011351) B2011351
theorem B1190919 : Blo 1190412 1190919 := bstep (se 1 (by rfl) ⟨893189, by rfl⟩ : syracuseStep 1190919 = 1786379) B1786379
theorem B1190927 : Blo 1190412 1190927 := bstep (se 1 (by rfl) ⟨893195, by rfl⟩ : syracuseStep 1190927 = 1786391) B1786391
theorem B4525085 : Blo 1190412 4525085 := bstep (se 3 (by rfl) ⟨848453, by rfl⟩ : syracuseStep 4525085 = 1696907) B1696907
theorem B1190971 : Blo 1190412 1190971 := bstep (se 1 (by rfl) ⟨893228, by rfl⟩ : syracuseStep 1190971 = 1786457) B1786457
theorem B1191047 : Blo 1190412 1191047 := bstep (se 1 (by rfl) ⟨893285, by rfl⟩ : syracuseStep 1191047 = 1786571) B1786571
theorem B1191055 : Blo 1190412 1191055 := bstep (se 1 (by rfl) ⟨893291, by rfl⟩ : syracuseStep 1191055 = 1786583) B1786583
theorem B1191099 : Blo 1190412 1191099 := bstep (se 1 (by rfl) ⟨893324, by rfl⟩ : syracuseStep 1191099 = 1786649) B1786649
theorem B3394817 : Blo 1190412 3394817 := bstep (se 2 (by rfl) ⟨1273056, by rfl⟩ : syracuseStep 3394817 = 2546113) B2546113
theorem B1191175 : Blo 1190412 1191175 := bstep (se 1 (by rfl) ⟨893381, by rfl⟩ : syracuseStep 1191175 = 1786763) B1786763
theorem B1191183 : Blo 1190412 1191183 := bstep (se 1 (by rfl) ⟨893387, by rfl⟩ : syracuseStep 1191183 = 1786775) B1786775
theorem B3017999 : Blo 1190412 3017999 := bstep (se 1 (by rfl) ⟨2263499, by rfl⟩ : syracuseStep 3017999 = 4526999) B4526999
theorem B1191227 : Blo 1190412 1191227 := bstep (se 1 (by rfl) ⟨893420, by rfl⟩ : syracuseStep 1191227 = 1786841) B1786841
theorem B2010487 : Blo 1190412 2010487 := bstep (se 1 (by rfl) ⟨1507865, by rfl⟩ : syracuseStep 2010487 = 3015731) B3015731
theorem B1191303 : Blo 1190412 1191303 := bstep (se 1 (by rfl) ⟨893477, by rfl⟩ : syracuseStep 1191303 = 1786955) B1786955
theorem B1191311 : Blo 1190412 1191311 := bstep (se 1 (by rfl) ⟨893483, by rfl⟩ : syracuseStep 1191311 = 1786967) B1786967
theorem B3018131 : Blo 1190412 3018131 := bstep (se 1 (by rfl) ⟨2263598, by rfl⟩ : syracuseStep 3018131 = 4527197) B4527197
theorem B1191355 : Blo 1190412 1191355 := bstep (se 1 (by rfl) ⟨893516, by rfl⟩ : syracuseStep 1191355 = 1787033) B1787033
theorem B1191431 : Blo 1190412 1191431 := bstep (se 1 (by rfl) ⟨893573, by rfl⟩ : syracuseStep 1191431 = 1787147) B1787147
theorem B1191439 : Blo 1190412 1191439 := bstep (se 1 (by rfl) ⟨893579, by rfl⟩ : syracuseStep 1191439 = 1787159) B1787159
theorem B3223073 : Blo 1190412 3223073 := bstep (se 2 (by rfl) ⟨1208652, by rfl⟩ : syracuseStep 3223073 = 2417305) B2417305
theorem B4017707 : Blo 1190412 4017707 := bstep (se 1 (by rfl) ⟨3013280, by rfl⟩ : syracuseStep 4017707 = 6026561) B6026561
theorem B1191483 : Blo 1190412 1191483 := bstep (se 1 (by rfl) ⟨893612, by rfl⟩ : syracuseStep 1191483 = 1787225) B1787225
theorem B2010683 : Blo 1190412 2010683 := bstep (se 1 (by rfl) ⟨1508012, by rfl⟩ : syracuseStep 2010683 = 3016025) B3016025
theorem B3395159 : Blo 1190412 3395159 := bstep (se 1 (by rfl) ⟨2546369, by rfl⟩ : syracuseStep 3395159 = 5092739) B5092739
theorem B1191559 : Blo 1190412 1191559 := bstep (se 1 (by rfl) ⟨893669, by rfl⟩ : syracuseStep 1191559 = 1787339) B1787339
theorem B2682503 : Blo 1190412 2682503 := bstep (se 1 (by rfl) ⟨2011877, by rfl⟩ : syracuseStep 2682503 = 4023755) B4023755
theorem B1191567 : Blo 1190412 1191567 := bstep (se 1 (by rfl) ⟨893675, by rfl⟩ : syracuseStep 1191567 = 1787351) B1787351
theorem B1191611 : Blo 1190412 1191611 := bstep (se 1 (by rfl) ⟨893708, by rfl⟩ : syracuseStep 1191611 = 1787417) B1787417
theorem B1191687 : Blo 1190412 1191687 := bstep (se 1 (by rfl) ⟨893765, by rfl⟩ : syracuseStep 1191687 = 1787531) B1787531
theorem B1191695 : Blo 1190412 1191695 := bstep (se 1 (by rfl) ⟨893771, by rfl⟩ : syracuseStep 1191695 = 1787543) B1787543
theorem B6033203 : Blo 1190412 6033203 := bstep (se 1 (by rfl) ⟨4524902, by rfl⟩ : syracuseStep 6033203 = 9049805) B9049805
theorem B1191739 : Blo 1190412 1191739 := bstep (se 1 (by rfl) ⟨893804, by rfl⟩ : syracuseStep 1191739 = 1787609) B1787609
theorem B2682683 : Blo 1190412 2682683 := bstep (se 1 (by rfl) ⟨2012012, by rfl⟩ : syracuseStep 2682683 = 4024025) B4024025
theorem B12218201 : Blo 1190412 12218201 := bstep (se 2 (by rfl) ⟨4581825, by rfl⟩ : syracuseStep 12218201 = 9163651) B9163651
theorem B6442841 : Blo 1190412 6442841 := bstep (se 2 (by rfl) ⟨2416065, by rfl⟩ : syracuseStep 6442841 = 4832131) B4832131
theorem B4829063 : Blo 1190412 4829063 := bstep (se 1 (by rfl) ⟨3621797, by rfl⟩ : syracuseStep 4829063 = 7243595) B7243595
theorem B1191815 : Blo 1190412 1191815 := bstep (se 1 (by rfl) ⟨893861, by rfl⟩ : syracuseStep 1191815 = 1787723) B1787723
theorem B1191823 : Blo 1190412 1191823 := bstep (se 1 (by rfl) ⟨893867, by rfl⟩ : syracuseStep 1191823 = 1787735) B1787735
theorem B1191867 : Blo 1190412 1191867 := bstep (se 1 (by rfl) ⟨893900, by rfl⟩ : syracuseStep 1191867 = 1787801) B1787801
theorem B2682809 : Blo 1190412 2682809 := bstep (se 2 (by rfl) ⟨1006053, by rfl⟩ : syracuseStep 2682809 = 2012107) B2012107
theorem B2011081 : Blo 1190412 2011081 := bstep (se 2 (by rfl) ⟨754155, by rfl⟩ : syracuseStep 2011081 = 1508311) B1508311
theorem B1191943 : Blo 1190412 1191943 := bstep (se 1 (by rfl) ⟨893957, by rfl⟩ : syracuseStep 1191943 = 1787915) B1787915
theorem B1191951 : Blo 1190412 1191951 := bstep (se 1 (by rfl) ⟨893963, by rfl⟩ : syracuseStep 1191951 = 1787927) B1787927
theorem B28987409 : Blo 1190412 28987409 := bstep (se 2 (by rfl) ⟨10870278, by rfl⟩ : syracuseStep 28987409 = 21740557) B21740557
theorem B1191995 : Blo 1190412 1191995 := bstep (se 1 (by rfl) ⟨893996, by rfl⟩ : syracuseStep 1191995 = 1787993) B1787993
theorem B6033527 : Blo 1190412 6033527 := bstep (se 1 (by rfl) ⟨4525145, by rfl⟩ : syracuseStep 6033527 = 9050291) B9050291
theorem B1192071 : Blo 1190412 1192071 := bstep (se 1 (by rfl) ⟨894053, by rfl⟩ : syracuseStep 1192071 = 1788107) B1788107
theorem B1192079 : Blo 1190412 1192079 := bstep (se 1 (by rfl) ⟨894059, by rfl⟩ : syracuseStep 1192079 = 1788119) B1788119
theorem B1192123 : Blo 1190412 1192123 := bstep (se 1 (by rfl) ⟨894092, by rfl⟩ : syracuseStep 1192123 = 1788185) B1788185
theorem B1192199 : Blo 1190412 1192199 := bstep (se 1 (by rfl) ⟨894149, by rfl⟩ : syracuseStep 1192199 = 1788299) B1788299
theorem B1339663 : Blo 1190412 1339663 := bstep (se 1 (by rfl) ⟨1004747, by rfl⟩ : syracuseStep 1339663 = 2009495) B2009495
theorem B1192207 : Blo 1190412 1192207 := bstep (se 1 (by rfl) ⟨894155, by rfl⟩ : syracuseStep 1192207 = 1788311) B1788311
theorem B1192251 : Blo 1190412 1192251 := bstep (se 1 (by rfl) ⟨894188, by rfl⟩ : syracuseStep 1192251 = 1788377) B1788377
theorem B1192327 : Blo 1190412 1192327 := bstep (se 1 (by rfl) ⟨894245, by rfl⟩ : syracuseStep 1192327 = 1788491) B1788491
theorem B1192335 : Blo 1190412 1192335 := bstep (se 1 (by rfl) ⟨894251, by rfl⟩ : syracuseStep 1192335 = 1788503) B1788503
theorem B5091731 : Blo 1190412 5091731 := bstep (se 1 (by rfl) ⟨3818798, by rfl⟩ : syracuseStep 5091731 = 7637597) B7637597
theorem B1192379 : Blo 1190412 1192379 := bstep (se 1 (by rfl) ⟨894284, by rfl⟩ : syracuseStep 1192379 = 1788569) B1788569
theorem B11457125 : Blo 1190412 11457125 := bstep (se 4 (by rfl) ⟨1074105, by rfl⟩ : syracuseStep 11457125 = 2148211) B2148211
theorem B4526711 : Blo 1190412 4526711 := bstep (se 1 (by rfl) ⟨3395033, by rfl⟩ : syracuseStep 4526711 = 6790067) B6790067
theorem B2011783 : Blo 1190412 2011783 := bstep (se 1 (by rfl) ⟨1508837, by rfl⟩ : syracuseStep 2011783 = 3017675) B3017675
theorem B46453429 : Blo 1190412 46453429 := bstep (se 5 (by rfl) ⟨2177504, by rfl⟩ : syracuseStep 46453429 = 4355009) B4355009
theorem B23540441 : Blo 1190412 23540441 := bstep (se 2 (by rfl) ⟨8827665, by rfl⟩ : syracuseStep 23540441 = 17655331) B17655331
theorem B9655013 : Blo 1190412 9655013 := bstep (se 4 (by rfl) ⟨905157, by rfl⟩ : syracuseStep 9655013 = 1810315) B1810315
theorem B9048833 : Blo 1190412 9048833 := bstep (se 2 (by rfl) ⟨3393312, by rfl⟩ : syracuseStep 9048833 = 6786625) B6786625
theorem B1340167 : Blo 1190412 1340167 := bstep (se 1 (by rfl) ⟨1005125, by rfl⟩ : syracuseStep 1340167 = 2010251) B2010251
theorem B4019003 : Blo 1190412 4019003 := bstep (se 1 (by rfl) ⟨3014252, by rfl⟩ : syracuseStep 4019003 = 6028505) B6028505
theorem B5722969 : Blo 1190412 5722969 := bstep (se 2 (by rfl) ⟨2146113, by rfl⟩ : syracuseStep 5722969 = 4292227) B4292227
theorem B1340347 : Blo 1190412 1340347 := bstep (se 1 (by rfl) ⟨1005260, by rfl⟩ : syracuseStep 1340347 = 2010521) B2010521
theorem B2716687 : Blo 1190412 2716687 := bstep (se 1 (by rfl) ⟨2037515, by rfl⟩ : syracuseStep 2716687 = 4075031) B4075031
theorem B6034499 : Blo 1190412 6034499 := bstep (se 1 (by rfl) ⟨4525874, by rfl⟩ : syracuseStep 6034499 = 9051749) B9051749
theorem B9655469 : Blo 1190412 9655469 := bstep (se 3 (by rfl) ⟨1810400, by rfl⟩ : syracuseStep 9655469 = 3620801) B3620801
theorem B8582381 : Blo 1190412 8582381 := bstep (se 3 (by rfl) ⟨1609196, by rfl⟩ : syracuseStep 8582381 = 3218393) B3218393
theorem B6436111 : Blo 1190412 6436111 := bstep (se 1 (by rfl) ⟨4827083, by rfl⟩ : syracuseStep 6436111 = 9654167) B9654167
theorem B4019489 : Blo 1190412 4019489 := bstep (se 2 (by rfl) ⟨1507308, by rfl⟩ : syracuseStep 4019489 = 3014617) B3014617
theorem B1430843 : Blo 1190412 1430843 := bstep (se 1 (by rfl) ⟨1073132, by rfl⟩ : syracuseStep 1430843 = 2146265) B2146265
theorem B49550723 : Blo 1190412 49550723 := bstep (se 1 (by rfl) ⟨37163042, by rfl⟩ : syracuseStep 49550723 = 74326085) B74326085
theorem B6034823 : Blo 1190412 6034823 := bstep (se 1 (by rfl) ⟨4526117, by rfl⟩ : syracuseStep 6034823 = 9052235) B9052235
theorem B1340815 : Blo 1190412 1340815 := bstep (se 1 (by rfl) ⟨1005611, by rfl⟩ : syracuseStep 1340815 = 2011223) B2011223
theorem B6116755 : Blo 1190412 6116755 := bstep (se 1 (by rfl) ⟨4587566, by rfl⟩ : syracuseStep 6116755 = 9175133) B9175133
theorem B2717243 : Blo 1190412 2717243 := bstep (se 1 (by rfl) ⟨2037932, by rfl⟩ : syracuseStep 2717243 = 4075865) B4075865
theorem B14489381 : Blo 1190412 14489381 := bstep (se 4 (by rfl) ⟨1358379, by rfl⟩ : syracuseStep 14489381 = 2716759) B2716759
theorem B17413957 : Blo 1190412 17413957 := bstep (se 4 (by rfl) ⟨1632558, by rfl⟩ : syracuseStep 17413957 = 3265117) B3265117
theorem B4020083 : Blo 1190412 4020083 := bstep (se 1 (by rfl) ⟨3015062, by rfl⟩ : syracuseStep 4020083 = 6030125) B6030125
theorem B1341319 : Blo 1190412 1341319 := bstep (se 1 (by rfl) ⟨1005989, by rfl⟩ : syracuseStep 1341319 = 2011979) B2011979
theorem B6445021 : Blo 1190412 6445021 := bstep (se 3 (by rfl) ⟨1208441, by rfl⟩ : syracuseStep 6445021 = 2416883) B2416883
theorem B21485591 : Blo 1190412 21485591 := bstep (se 1 (by rfl) ⟨16114193, by rfl⟩ : syracuseStep 21485591 = 32228387) B32228387
theorem B12400663 : Blo 1190412 12400663 := bstep (se 1 (by rfl) ⟨9300497, by rfl⟩ : syracuseStep 12400663 = 18600995) B18600995
theorem B11458583 : Blo 1190412 11458583 := bstep (se 1 (by rfl) ⟨8593937, by rfl⟩ : syracuseStep 11458583 = 17187875) B17187875
theorem B39688309 : Blo 1190412 39688309 := bstep (se 5 (by rfl) ⟨1860389, by rfl⟩ : syracuseStep 39688309 = 3720779) B3720779
theorem B2414711 : Blo 1190412 2414711 := bstep (se 1 (by rfl) ⟨1811033, by rfl⟩ : syracuseStep 2414711 = 3622067) B3622067
theorem B4520225 : Blo 1190412 4520225 := bstep (se 2 (by rfl) ⟨1695084, by rfl⟩ : syracuseStep 4520225 = 3390169) B3390169
theorem B6781319 : Blo 1190412 6781319 := bstep (se 1 (by rfl) ⟨5085989, by rfl⟩ : syracuseStep 6781319 = 10171979) B10171979
theorem B6879755 : Blo 1190412 6879755 := bstep (se 1 (by rfl) ⟨5159816, by rfl⟩ : syracuseStep 6879755 = 10319633) B10319633
theorem B6437495 : Blo 1190412 6437495 := bstep (se 1 (by rfl) ⟨4828121, by rfl⟩ : syracuseStep 6437495 = 9656243) B9656243
theorem B3013321 : Blo 1190412 3013321 := bstep (se 2 (by rfl) ⟨1129995, by rfl⟩ : syracuseStep 3013321 = 2259991) B2259991
theorem B1907471 : Blo 1190412 1907471 := bstep (se 1 (by rfl) ⟨1430603, by rfl⟩ : syracuseStep 1907471 = 2861207) B2861207
theorem B8706865 : Blo 1190412 8706865 := bstep (se 2 (by rfl) ⟨3265074, by rfl⟩ : syracuseStep 8706865 = 6530149) B6530149
theorem B3013463 : Blo 1190412 3013463 := bstep (se 1 (by rfl) ⟨2260097, by rfl⟩ : syracuseStep 3013463 = 4520195) B4520195
theorem B3390295 : Blo 1190412 3390295 := bstep (se 1 (by rfl) ⟨2542721, by rfl⟩ : syracuseStep 3390295 = 5085443) B5085443
theorem B7240823 : Blo 1190412 7240823 := bstep (se 1 (by rfl) ⟨5430617, by rfl⟩ : syracuseStep 7240823 = 10861235) B10861235
theorem B4521197 : Blo 1190412 4521197 := bstep (se 3 (by rfl) ⟨847724, by rfl⟩ : syracuseStep 4521197 = 1695449) B1695449
theorem B1907983 : Blo 1190412 1907983 := bstep (se 1 (by rfl) ⟨1430987, by rfl⟩ : syracuseStep 1907983 = 2861975) B2861975
theorem B8584481 : Blo 1190412 8584481 := bstep (se 2 (by rfl) ⟨3219180, by rfl⟩ : syracuseStep 8584481 = 6438361) B6438361
theorem B44039483 : Blo 1190412 44039483 := bstep (se 1 (by rfl) ⟨33029612, by rfl⟩ : syracuseStep 44039483 = 66059225) B66059225
theorem B21192121 : Blo 1190412 21192121 := bstep (se 2 (by rfl) ⟨7947045, by rfl⟩ : syracuseStep 21192121 = 15894091) B15894091
theorem B6028829 : Blo 1190412 6028829 := bstep (se 3 (by rfl) ⟨1130405, by rfl⟩ : syracuseStep 6028829 = 2260811) B2260811
theorem B2260523 : Blo 1190412 2260523 := bstep (se 1 (by rfl) ⟨1695392, by rfl⟩ : syracuseStep 2260523 = 3390785) B3390785
theorem B6782525 : Blo 1190412 6782525 := bstep (se 3 (by rfl) ⟨1271723, by rfl⟩ : syracuseStep 6782525 = 2543447) B2543447
theorem B8822465 : Blo 1190412 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B2678543 : Blo 1190412 2678543 := bstep (se 1 (by rfl) ⟨2008907, by rfl⟩ : syracuseStep 2678543 = 4017815) B4017815
theorem B2678561 : Blo 1190412 2678561 := bstep (se 2 (by rfl) ⟨1004460, by rfl⟩ : syracuseStep 2678561 = 2008921) B2008921
theorem B6438689 : Blo 1190412 6438689 := bstep (se 2 (by rfl) ⟨2414508, by rfl⟩ : syracuseStep 6438689 = 4829017) B4829017
theorem B1785659 : Blo 1190412 1785659 := bstep (se 1 (by rfl) ⟨1339244, by rfl⟩ : syracuseStep 1785659 = 2678489) B2678489
theorem B1785719 : Blo 1190412 1785719 := bstep (se 1 (by rfl) ⟨1339289, by rfl⟩ : syracuseStep 1785719 = 2678579) B2678579
theorem B2752375 : Blo 1190412 2752375 := bstep (se 1 (by rfl) ⟨2064281, by rfl⟩ : syracuseStep 2752375 = 4128563) B4128563
theorem B1785743 : Blo 1190412 1785743 := bstep (se 1 (by rfl) ⟨1339307, by rfl⟩ : syracuseStep 1785743 = 2678615) B2678615
theorem B3817363 : Blo 1190412 3817363 := bstep (se 1 (by rfl) ⟨2863022, by rfl⟩ : syracuseStep 3817363 = 5726045) B5726045
theorem B1507243 : Blo 1190412 1507243 := bstep (se 1 (by rfl) ⟨1130432, by rfl⟩ : syracuseStep 1507243 = 2260865) B2260865
theorem B1785785 : Blo 1190412 1785785 := bstep (se 2 (by rfl) ⟨669669, by rfl⟩ : syracuseStep 1785785 = 1339339) B1339339
theorem B77299757 : Blo 1190412 77299757 := bstep (se 3 (by rfl) ⟨14493704, by rfl⟩ : syracuseStep 77299757 = 28987409) B28987409
theorem B1785935 : Blo 1190412 1785935 := bstep (se 1 (by rfl) ⟨1339451, by rfl⟩ : syracuseStep 1785935 = 2678903) B2678903
theorem B4022351 : Blo 1190412 4022351 := bstep (se 1 (by rfl) ⟨3016763, by rfl⟩ : syracuseStep 4022351 = 6033527) B6033527
theorem B4292689 : Blo 1190412 4292689 := bstep (se 2 (by rfl) ⟨1609758, by rfl⟩ : syracuseStep 4292689 = 3219517) B3219517
theorem B7635059 : Blo 1190412 7635059 := bstep (se 1 (by rfl) ⟨5726294, by rfl⟩ : syracuseStep 7635059 = 11452589) B11452589
theorem B1786055 : Blo 1190412 1786055 := bstep (se 1 (by rfl) ⟨1339541, by rfl⟩ : syracuseStep 1786055 = 2679083) B2679083
theorem B2261191 : Blo 1190412 2261191 := bstep (se 1 (by rfl) ⟨1695893, by rfl⟩ : syracuseStep 2261191 = 3391787) B3391787
theorem B2146655 : Blo 1190412 2146655 := bstep (se 1 (by rfl) ⟨1609991, by rfl⟩ : syracuseStep 2146655 = 3219983) B3219983
theorem B1786217 : Blo 1190412 1786217 := bstep (se 2 (by rfl) ⟨669831, by rfl⟩ : syracuseStep 1786217 = 1339663) B1339663
theorem B1786295 : Blo 1190412 1786295 := bstep (se 1 (by rfl) ⟨1339721, by rfl⟩ : syracuseStep 1786295 = 2679443) B2679443
theorem B4022729 : Blo 1190412 4022729 := bstep (se 2 (by rfl) ⟨1508523, by rfl⟩ : syracuseStep 4022729 = 3017047) B3017047
theorem B1786331 : Blo 1190412 1786331 := bstep (se 1 (by rfl) ⟨1339748, by rfl⟩ : syracuseStep 1786331 = 2679497) B2679497
theorem B2679335 : Blo 1190412 2679335 := bstep (se 1 (by rfl) ⟨2009501, by rfl⟩ : syracuseStep 2679335 = 4019003) B4019003
theorem B3015265 : Blo 1190412 3015265 := bstep (se 2 (by rfl) ⟨1130724, by rfl⟩ : syracuseStep 3015265 = 2261449) B2261449
theorem B3818195 : Blo 1190412 3818195 := bstep (se 1 (by rfl) ⟨2863646, by rfl⟩ : syracuseStep 3818195 = 5727293) B5727293
theorem B4022999 : Blo 1190412 4022999 := bstep (se 1 (by rfl) ⟨3017249, by rfl⟩ : syracuseStep 4022999 = 6034499) B6034499
theorem B2261753 : Blo 1190412 2261753 := bstep (se 2 (by rfl) ⟨848157, by rfl⟩ : syracuseStep 2261753 = 1696315) B1696315
theorem B2679659 : Blo 1190412 2679659 := bstep (se 1 (by rfl) ⟨2009744, by rfl⟩ : syracuseStep 2679659 = 4019489) B4019489
theorem B2679713 : Blo 1190412 2679713 := bstep (se 2 (by rfl) ⟨1004892, by rfl⟩ : syracuseStep 2679713 = 2009785) B2009785
theorem B1786799 : Blo 1190412 1786799 := bstep (se 1 (by rfl) ⟨1340099, by rfl⟩ : syracuseStep 1786799 = 2680199) B2680199
theorem B2261935 : Blo 1190412 2261935 := bstep (se 1 (by rfl) ⟨1696451, by rfl⟩ : syracuseStep 2261935 = 3392903) B3392903
theorem B4023215 : Blo 1190412 4023215 := bstep (se 1 (by rfl) ⟨3017411, by rfl⟩ : syracuseStep 4023215 = 6034823) B6034823
theorem B9659357 : Blo 1190412 9659357 := bstep (se 3 (by rfl) ⟨1811129, by rfl⟩ : syracuseStep 9659357 = 3622259) B3622259
theorem B1786889 : Blo 1190412 1786889 := bstep (se 2 (by rfl) ⟨670083, by rfl⟩ : syracuseStep 1786889 = 1340167) B1340167
theorem B1786919 : Blo 1190412 1786919 := bstep (se 1 (by rfl) ⟨1340189, by rfl⟩ : syracuseStep 1786919 = 2680379) B2680379
theorem B1811495 : Blo 1190412 1811495 := bstep (se 1 (by rfl) ⟨1358621, by rfl⟩ : syracuseStep 1811495 = 2717243) B2717243
theorem B11609153 : Blo 1190412 11609153 := bstep (se 2 (by rfl) ⟨4353432, by rfl⟩ : syracuseStep 11609153 = 8706865) B8706865
theorem B1787003 : Blo 1190412 1787003 := bstep (se 1 (by rfl) ⟨1340252, by rfl⟩ : syracuseStep 1787003 = 2680505) B2680505
theorem B9659587 : Blo 1190412 9659587 := bstep (se 1 (by rfl) ⟨7244690, by rfl⟩ : syracuseStep 9659587 = 14489381) B14489381
theorem B15262937 : Blo 1190412 15262937 := bstep (se 2 (by rfl) ⟨5723601, by rfl⟩ : syracuseStep 15262937 = 11447203) B11447203
theorem B2680055 : Blo 1190412 2680055 := bstep (se 1 (by rfl) ⟨2010041, by rfl⟩ : syracuseStep 2680055 = 4020083) B4020083
theorem B1787129 : Blo 1190412 1787129 := bstep (se 2 (by rfl) ⟨670173, by rfl⟩ : syracuseStep 1787129 = 1340347) B1340347
theorem B1787231 : Blo 1190412 1787231 := bstep (se 1 (by rfl) ⟨1340423, by rfl⟩ : syracuseStep 1787231 = 2680847) B2680847
theorem B3622249 : Blo 1190412 3622249 := bstep (se 2 (by rfl) ⟨1358343, by rfl⟩ : syracuseStep 3622249 = 2716687) B2716687
theorem B1787243 : Blo 1190412 1787243 := bstep (se 1 (by rfl) ⟨1340432, by rfl⟩ : syracuseStep 1787243 = 2680865) B2680865
theorem B3016217 : Blo 1190412 3016217 := bstep (se 2 (by rfl) ⟨1131081, by rfl⟩ : syracuseStep 3016217 = 2262163) B2262163
theorem B1787471 : Blo 1190412 1787471 := bstep (se 1 (by rfl) ⟨1340603, by rfl⟩ : syracuseStep 1787471 = 2681207) B2681207
theorem B1787591 : Blo 1190412 1787591 := bstep (se 1 (by rfl) ⟨1340693, by rfl⟩ : syracuseStep 1787591 = 2681387) B2681387
theorem B6031097 : Blo 1190412 6031097 := bstep (se 2 (by rfl) ⟨2261661, by rfl⟩ : syracuseStep 6031097 = 4523323) B4523323
theorem B3868445 : Blo 1190412 3868445 := bstep (se 3 (by rfl) ⟨725333, by rfl⟩ : syracuseStep 3868445 = 1450667) B1450667
theorem B2680649 : Blo 1190412 2680649 := bstep (se 2 (by rfl) ⟨1005243, by rfl⟩ : syracuseStep 2680649 = 2010487) B2010487
theorem B1271647 : Blo 1190412 1271647 := bstep (se 1 (by rfl) ⟨953735, by rfl⟩ : syracuseStep 1271647 = 1907471) B1907471
theorem B1787753 : Blo 1190412 1787753 := bstep (se 2 (by rfl) ⟨670407, by rfl⟩ : syracuseStep 1787753 = 1340815) B1340815
theorem B2008975 : Blo 1190412 2008975 := bstep (se 1 (by rfl) ⟨1506731, by rfl⟩ : syracuseStep 2008975 = 3013463) B3013463
theorem B28256161 : Blo 1190412 28256161 := bstep (se 2 (by rfl) ⟨10596060, by rfl⟩ : syracuseStep 28256161 = 21192121) B21192121
theorem B1787831 : Blo 1190412 1787831 := bstep (se 1 (by rfl) ⟨1340873, by rfl⟩ : syracuseStep 1787831 = 2681747) B2681747
theorem B3622843 : Blo 1190412 3622843 := bstep (se 1 (by rfl) ⟨2717132, by rfl⟩ : syracuseStep 3622843 = 5434265) B5434265
theorem B1787867 : Blo 1190412 1787867 := bstep (se 1 (by rfl) ⟨1340900, by rfl⟩ : syracuseStep 1787867 = 2681801) B2681801
theorem B3016723 : Blo 1190412 3016723 := bstep (se 1 (by rfl) ⟨2262542, by rfl⟩ : syracuseStep 3016723 = 4525085) B4525085
theorem B4827215 : Blo 1190412 4827215 := bstep (se 1 (by rfl) ⟨3620411, by rfl⟩ : syracuseStep 4827215 = 7240823) B7240823
theorem B4524113 : Blo 1190412 4524113 := bstep (se 2 (by rfl) ⟨1696542, by rfl⟩ : syracuseStep 4524113 = 3393085) B3393085
theorem B2263211 : Blo 1190412 2263211 := bstep (se 1 (by rfl) ⟨1697408, by rfl⟩ : syracuseStep 2263211 = 3394817) B3394817
theorem B2148715 : Blo 1190412 2148715 := bstep (se 1 (by rfl) ⟨1611536, by rfl⟩ : syracuseStep 2148715 = 3223073) B3223073
theorem B6031745 : Blo 1190412 6031745 := bstep (se 2 (by rfl) ⟨2261904, by rfl⟩ : syracuseStep 6031745 = 4523809) B4523809
theorem B2263439 : Blo 1190412 2263439 := bstep (se 1 (by rfl) ⟨1697579, by rfl⟩ : syracuseStep 2263439 = 3395159) B3395159
theorem B1788335 : Blo 1190412 1788335 := bstep (se 1 (by rfl) ⟨1341251, by rfl⟩ : syracuseStep 1788335 = 2682503) B2682503
theorem B23218609 : Blo 1190412 23218609 := bstep (se 2 (by rfl) ⟨8706978, by rfl⟩ : syracuseStep 23218609 = 17413957) B17413957
theorem B1788425 : Blo 1190412 1788425 := bstep (se 2 (by rfl) ⟨670659, by rfl⟩ : syracuseStep 1788425 = 1341319) B1341319
theorem B5089817 : Blo 1190412 5089817 := bstep (se 2 (by rfl) ⟨1908681, by rfl⟩ : syracuseStep 5089817 = 3817363) B3817363
theorem B4524569 : Blo 1190412 4524569 := bstep (se 2 (by rfl) ⟨1696713, by rfl⟩ : syracuseStep 4524569 = 3393427) B3393427
theorem B1190439 : Blo 1190412 1190439 := bstep (se 1 (by rfl) ⟨892829, by rfl⟩ : syracuseStep 1190439 = 1785659) B1785659
theorem B1788455 : Blo 1190412 1788455 := bstep (se 1 (by rfl) ⟨1341341, by rfl⟩ : syracuseStep 1788455 = 2682683) B2682683
theorem B2009657 : Blo 1190412 2009657 := bstep (se 2 (by rfl) ⟨753621, by rfl⟩ : syracuseStep 2009657 = 1507243) B1507243
theorem B8145467 : Blo 1190412 8145467 := bstep (se 1 (by rfl) ⟨6109100, by rfl⟩ : syracuseStep 8145467 = 12218201) B12218201
theorem B4295227 : Blo 1190412 4295227 := bstep (se 1 (by rfl) ⟨3221420, by rfl⟩ : syracuseStep 4295227 = 6442841) B6442841
theorem B1190479 : Blo 1190412 1190479 := bstep (se 1 (by rfl) ⟨892859, by rfl⟩ : syracuseStep 1190479 = 1785719) B1785719
theorem B1190495 : Blo 1190412 1190495 := bstep (se 1 (by rfl) ⟨892871, by rfl⟩ : syracuseStep 1190495 = 1785743) B1785743
theorem B2681441 : Blo 1190412 2681441 := bstep (se 2 (by rfl) ⟨1005540, by rfl⟩ : syracuseStep 2681441 = 2011081) B2011081
theorem B1190523 : Blo 1190412 1190523 := bstep (se 1 (by rfl) ⟨892892, by rfl⟩ : syracuseStep 1190523 = 1785785) B1785785
theorem B1788539 : Blo 1190412 1788539 := bstep (se 1 (by rfl) ⟨1341404, by rfl⟩ : syracuseStep 1788539 = 2682809) B2682809
theorem B1190575 : Blo 1190412 1190575 := bstep (se 1 (by rfl) ⟨892931, by rfl⟩ : syracuseStep 1190575 = 1785863) B1785863
theorem B1190599 : Blo 1190412 1190599 := bstep (se 1 (by rfl) ⟨892949, by rfl⟩ : syracuseStep 1190599 = 1785899) B1785899
theorem B16534217 : Blo 1190412 16534217 := bstep (se 2 (by rfl) ⟨6200331, by rfl⟩ : syracuseStep 16534217 = 12400663) B12400663
theorem B4827863 : Blo 1190412 4827863 := bstep (se 1 (by rfl) ⟨3620897, by rfl⟩ : syracuseStep 4827863 = 7241795) B7241795
theorem B1190619 : Blo 1190412 1190619 := bstep (se 1 (by rfl) ⟨892964, by rfl⟩ : syracuseStep 1190619 = 1785929) B1785929
theorem B1190695 : Blo 1190412 1190695 := bstep (se 1 (by rfl) ⟨893021, by rfl⟩ : syracuseStep 1190695 = 1786043) B1786043
theorem B1190735 : Blo 1190412 1190735 := bstep (se 1 (by rfl) ⟨893051, by rfl⟩ : syracuseStep 1190735 = 1786103) B1786103
theorem B1190751 : Blo 1190412 1190751 := bstep (se 1 (by rfl) ⟨893063, by rfl⟩ : syracuseStep 1190751 = 1786127) B1786127
theorem B1190779 : Blo 1190412 1190779 := bstep (se 1 (by rfl) ⟨893084, by rfl⟩ : syracuseStep 1190779 = 1786169) B1786169
theorem B4295585 : Blo 1190412 4295585 := bstep (se 2 (by rfl) ⟨1610844, by rfl⟩ : syracuseStep 4295585 = 3221689) B3221689
theorem B1190831 : Blo 1190412 1190831 := bstep (se 1 (by rfl) ⟨893123, by rfl⟩ : syracuseStep 1190831 = 1786247) B1786247
theorem B2681783 : Blo 1190412 2681783 := bstep (se 1 (by rfl) ⟨2011337, by rfl⟩ : syracuseStep 2681783 = 4022675) B4022675
theorem B3394487 : Blo 1190412 3394487 := bstep (se 1 (by rfl) ⟨2545865, by rfl⟩ : syracuseStep 3394487 = 5091731) B5091731
theorem B1190855 : Blo 1190412 1190855 := bstep (se 1 (by rfl) ⟨893141, by rfl⟩ : syracuseStep 1190855 = 1786283) B1786283
theorem B1190875 : Blo 1190412 1190875 := bstep (se 1 (by rfl) ⟨893156, by rfl⟩ : syracuseStep 1190875 = 1786313) B1786313
theorem B1190951 : Blo 1190412 1190951 := bstep (se 1 (by rfl) ⟨893213, by rfl⟩ : syracuseStep 1190951 = 1786427) B1786427
theorem B7638083 : Blo 1190412 7638083 := bstep (se 1 (by rfl) ⟨5728562, by rfl⟩ : syracuseStep 7638083 = 11457125) B11457125
theorem B1190991 : Blo 1190412 1190991 := bstep (se 1 (by rfl) ⟨893243, by rfl⟩ : syracuseStep 1190991 = 1786487) B1786487
theorem B3017807 : Blo 1190412 3017807 := bstep (se 1 (by rfl) ⟨2263355, by rfl⟩ : syracuseStep 3017807 = 4526711) B4526711
theorem B1191007 : Blo 1190412 1191007 := bstep (se 1 (by rfl) ⟨893255, by rfl⟩ : syracuseStep 1191007 = 1786511) B1786511
theorem B1191035 : Blo 1190412 1191035 := bstep (se 1 (by rfl) ⟨893276, by rfl⟩ : syracuseStep 1191035 = 1786553) B1786553
theorem B6032555 : Blo 1190412 6032555 := bstep (se 1 (by rfl) ⟨4524416, by rfl⟩ : syracuseStep 6032555 = 9048833) B9048833
theorem B1191087 : Blo 1190412 1191087 := bstep (se 1 (by rfl) ⟨893315, by rfl⟩ : syracuseStep 1191087 = 1786631) B1786631
theorem B1191111 : Blo 1190412 1191111 := bstep (se 1 (by rfl) ⟨893333, by rfl⟩ : syracuseStep 1191111 = 1786667) B1786667
theorem B1191131 : Blo 1190412 1191131 := bstep (se 1 (by rfl) ⟨893348, by rfl⟩ : syracuseStep 1191131 = 1786697) B1786697
theorem B2010359 : Blo 1190412 2010359 := bstep (se 1 (by rfl) ⟨1507769, by rfl⟩ : syracuseStep 2010359 = 3015539) B3015539
theorem B1191207 : Blo 1190412 1191207 := bstep (se 1 (by rfl) ⟨893405, by rfl⟩ : syracuseStep 1191207 = 1786811) B1786811
theorem B1191247 : Blo 1190412 1191247 := bstep (se 1 (by rfl) ⟨893435, by rfl⟩ : syracuseStep 1191247 = 1786871) B1786871
theorem B1191263 : Blo 1190412 1191263 := bstep (se 1 (by rfl) ⟨893447, by rfl⟩ : syracuseStep 1191263 = 1786895) B1786895
theorem B1191291 : Blo 1190412 1191291 := bstep (se 1 (by rfl) ⟨893468, by rfl⟩ : syracuseStep 1191291 = 1786937) B1786937
theorem B1191343 : Blo 1190412 1191343 := bstep (se 1 (by rfl) ⟨893507, by rfl⟩ : syracuseStep 1191343 = 1787015) B1787015
theorem B1191367 : Blo 1190412 1191367 := bstep (se 1 (by rfl) ⟨893525, by rfl⟩ : syracuseStep 1191367 = 1787051) B1787051
theorem B1191387 : Blo 1190412 1191387 := bstep (se 1 (by rfl) ⟨893540, by rfl⟩ : syracuseStep 1191387 = 1787081) B1787081
theorem B5721587 : Blo 1190412 5721587 := bstep (se 1 (by rfl) ⟨4291190, by rfl⟩ : syracuseStep 5721587 = 8582381) B8582381
theorem B2682377 : Blo 1190412 2682377 := bstep (se 2 (by rfl) ⟨1005891, by rfl⟩ : syracuseStep 2682377 = 2011783) B2011783
theorem B1191463 : Blo 1190412 1191463 := bstep (se 1 (by rfl) ⟨893597, by rfl⟩ : syracuseStep 1191463 = 1787195) B1787195
theorem B1191503 : Blo 1190412 1191503 := bstep (se 1 (by rfl) ⟨893627, by rfl⟩ : syracuseStep 1191503 = 1787255) B1787255
theorem B2010703 : Blo 1190412 2010703 := bstep (se 1 (by rfl) ⟨1508027, by rfl⟩ : syracuseStep 2010703 = 3016055) B3016055
theorem B33033815 : Blo 1190412 33033815 := bstep (se 1 (by rfl) ⟨24775361, by rfl⟩ : syracuseStep 33033815 = 49550723) B49550723
theorem B1191519 : Blo 1190412 1191519 := bstep (se 1 (by rfl) ⟨893639, by rfl⟩ : syracuseStep 1191519 = 1787279) B1787279
theorem B4017761 : Blo 1190412 4017761 := bstep (se 2 (by rfl) ⟨1506660, by rfl⟩ : syracuseStep 4017761 = 3013321) B3013321
theorem B2862715 : Blo 1190412 2862715 := bstep (se 1 (by rfl) ⟨2147036, by rfl⟩ : syracuseStep 2862715 = 4294073) B4294073
theorem B1191547 : Blo 1190412 1191547 := bstep (se 1 (by rfl) ⟨893660, by rfl⟩ : syracuseStep 1191547 = 1787321) B1787321
theorem B6033041 : Blo 1190412 6033041 := bstep (se 2 (by rfl) ⟨2262390, by rfl⟩ : syracuseStep 6033041 = 4524781) B4524781
theorem B1191599 : Blo 1190412 1191599 := bstep (se 1 (by rfl) ⟨893699, by rfl⟩ : syracuseStep 1191599 = 1787399) B1787399
theorem B4525753 : Blo 1190412 4525753 := bstep (se 2 (by rfl) ⟨1697157, by rfl⟩ : syracuseStep 4525753 = 3394315) B3394315
theorem B1191623 : Blo 1190412 1191623 := bstep (se 1 (by rfl) ⟨893717, by rfl⟩ : syracuseStep 1191623 = 1787435) B1787435
theorem B1191643 : Blo 1190412 1191643 := bstep (se 1 (by rfl) ⟨893732, by rfl⟩ : syracuseStep 1191643 = 1787465) B1787465
theorem B43462433 : Blo 1190412 43462433 := bstep (se 2 (by rfl) ⟨16298412, by rfl⟩ : syracuseStep 43462433 = 32596825) B32596825
theorem B7630625 : Blo 1190412 7630625 := bstep (se 2 (by rfl) ⟨2861484, by rfl⟩ : syracuseStep 7630625 = 5722969) B5722969
theorem B1191719 : Blo 1190412 1191719 := bstep (se 1 (by rfl) ⟨893789, by rfl⟩ : syracuseStep 1191719 = 1787579) B1787579
theorem B2010953 : Blo 1190412 2010953 := bstep (se 2 (by rfl) ⟨754107, by rfl⟩ : syracuseStep 2010953 = 1508215) B1508215
theorem B1191759 : Blo 1190412 1191759 := bstep (se 1 (by rfl) ⟨893819, by rfl⟩ : syracuseStep 1191759 = 1787639) B1787639
theorem B1339231 : Blo 1190412 1339231 := bstep (se 1 (by rfl) ⟨1004423, by rfl⟩ : syracuseStep 1339231 = 2008847) B2008847
theorem B1191775 : Blo 1190412 1191775 := bstep (se 1 (by rfl) ⟨893831, by rfl⟩ : syracuseStep 1191775 = 1787663) B1787663
theorem B2682719 : Blo 1190412 2682719 := bstep (se 1 (by rfl) ⟨2012039, by rfl⟩ : syracuseStep 2682719 = 4024079) B4024079
theorem B1191803 : Blo 1190412 1191803 := bstep (se 1 (by rfl) ⟨893852, by rfl⟩ : syracuseStep 1191803 = 1787705) B1787705
theorem B1191855 : Blo 1190412 1191855 := bstep (se 1 (by rfl) ⟨893891, by rfl⟩ : syracuseStep 1191855 = 1787783) B1787783
theorem B2863031 : Blo 1190412 2863031 := bstep (se 1 (by rfl) ⟨2147273, by rfl⟩ : syracuseStep 2863031 = 4294547) B4294547
theorem B1191879 : Blo 1190412 1191879 := bstep (se 1 (by rfl) ⟨893909, by rfl⟩ : syracuseStep 1191879 = 1787819) B1787819
theorem B1191899 : Blo 1190412 1191899 := bstep (se 1 (by rfl) ⟨893924, by rfl⟩ : syracuseStep 1191899 = 1787849) B1787849
theorem B15257605 : Blo 1190412 15257605 := bstep (se 4 (by rfl) ⟨1430400, by rfl⟩ : syracuseStep 15257605 = 2860801) B2860801
theorem B14323727 : Blo 1190412 14323727 := bstep (se 1 (by rfl) ⟨10742795, by rfl⟩ : syracuseStep 14323727 = 21485591) B21485591
theorem B7639055 : Blo 1190412 7639055 := bstep (se 1 (by rfl) ⟨5729291, by rfl⟩ : syracuseStep 7639055 = 11458583) B11458583
theorem B2682899 : Blo 1190412 2682899 := bstep (se 1 (by rfl) ⟨2012174, by rfl⟩ : syracuseStep 2682899 = 4024349) B4024349
theorem B18346013 : Blo 1190412 18346013 := bstep (se 3 (by rfl) ⟨3439877, by rfl⟩ : syracuseStep 18346013 = 6879755) B6879755
theorem B1191975 : Blo 1190412 1191975 := bstep (se 1 (by rfl) ⟨893981, by rfl⟩ : syracuseStep 1191975 = 1787963) B1787963
theorem B1609807 : Blo 1190412 1609807 := bstep (se 1 (by rfl) ⟨1207355, by rfl⟩ : syracuseStep 1609807 = 2414711) B2414711
theorem B1192015 : Blo 1190412 1192015 := bstep (se 1 (by rfl) ⟨894011, by rfl⟩ : syracuseStep 1192015 = 1788023) B1788023
theorem B1192031 : Blo 1190412 1192031 := bstep (se 1 (by rfl) ⟨894023, by rfl⟩ : syracuseStep 1192031 = 1788047) B1788047
theorem B1192059 : Blo 1190412 1192059 := bstep (se 1 (by rfl) ⟨894044, by rfl⟩ : syracuseStep 1192059 = 1788089) B1788089
theorem B1192111 : Blo 1190412 1192111 := bstep (se 1 (by rfl) ⟨894083, by rfl⟩ : syracuseStep 1192111 = 1788167) B1788167
theorem B38670533 : Blo 1190412 38670533 := bstep (se 4 (by rfl) ⟨3625362, by rfl⟩ : syracuseStep 38670533 = 7250725) B7250725
theorem B1339591 : Blo 1190412 1339591 := bstep (se 1 (by rfl) ⟨1004693, by rfl⟩ : syracuseStep 1339591 = 2009387) B2009387
theorem B1192135 : Blo 1190412 1192135 := bstep (se 1 (by rfl) ⟨894101, by rfl⟩ : syracuseStep 1192135 = 1788203) B1788203
theorem B1192155 : Blo 1190412 1192155 := bstep (se 1 (by rfl) ⟨894116, by rfl⟩ : syracuseStep 1192155 = 1788233) B1788233
theorem B2011385 : Blo 1190412 2011385 := bstep (se 2 (by rfl) ⟨754269, by rfl⟩ : syracuseStep 2011385 = 1508539) B1508539
theorem B1192231 : Blo 1190412 1192231 := bstep (se 1 (by rfl) ⟨894173, by rfl⟩ : syracuseStep 1192231 = 1788347) B1788347
theorem B17166653 : Blo 1190412 17166653 := bstep (se 3 (by rfl) ⟨3218747, by rfl⟩ : syracuseStep 17166653 = 6437495) B6437495
theorem B1192271 : Blo 1190412 1192271 := bstep (se 1 (by rfl) ⟨894203, by rfl⟩ : syracuseStep 1192271 = 1788407) B1788407
theorem B1192287 : Blo 1190412 1192287 := bstep (se 1 (by rfl) ⟨894215, by rfl⟩ : syracuseStep 1192287 = 1788431) B1788431
theorem B8581481 : Blo 1190412 8581481 := bstep (se 2 (by rfl) ⟨3218055, by rfl⟩ : syracuseStep 8581481 = 6436111) B6436111
theorem B2543977 : Blo 1190412 2543977 := bstep (se 2 (by rfl) ⟨953991, by rfl⟩ : syracuseStep 2543977 = 1907983) B1907983
theorem B1192315 : Blo 1190412 1192315 := bstep (se 1 (by rfl) ⟨894236, by rfl⟩ : syracuseStep 1192315 = 1788473) B1788473
theorem B4075919 : Blo 1190412 4075919 := bstep (se 1 (by rfl) ⟨3056939, by rfl⟩ : syracuseStep 4075919 = 6113879) B6113879
theorem B2011567 : Blo 1190412 2011567 := bstep (se 1 (by rfl) ⟨1508675, by rfl⟩ : syracuseStep 2011567 = 3017351) B3017351
theorem B1192367 : Blo 1190412 1192367 := bstep (se 1 (by rfl) ⟨894275, by rfl⟩ : syracuseStep 1192367 = 1788551) B1788551
theorem B1192391 : Blo 1190412 1192391 := bstep (se 1 (by rfl) ⟨894293, by rfl⟩ : syracuseStep 1192391 = 1788587) B1788587
theorem B1192411 : Blo 1190412 1192411 := bstep (se 1 (by rfl) ⟨894308, by rfl⟩ : syracuseStep 1192411 = 1788617) B1788617
theorem B2011655 : Blo 1190412 2011655 := bstep (se 1 (by rfl) ⟨1508741, by rfl⟩ : syracuseStep 2011655 = 3017483) B3017483
theorem B8155673 : Blo 1190412 8155673 := bstep (se 2 (by rfl) ⟨3058377, by rfl⟩ : syracuseStep 8155673 = 6116755) B6116755
theorem B2863945 : Blo 1190412 2863945 := bstep (se 2 (by rfl) ⟨1073979, by rfl⟩ : syracuseStep 2863945 = 2147959) B2147959
theorem B2011999 : Blo 1190412 2011999 := bstep (se 1 (by rfl) ⟨1508999, by rfl⟩ : syracuseStep 2011999 = 3017999) B3017999
theorem B5722987 : Blo 1190412 5722987 := bstep (se 1 (by rfl) ⟨4292240, by rfl⟩ : syracuseStep 5722987 = 8584481) B8584481
theorem B2012087 : Blo 1190412 2012087 := bstep (se 1 (by rfl) ⟨1509065, by rfl⟩ : syracuseStep 2012087 = 3018131) B3018131
theorem B4019219 : Blo 1190412 4019219 := bstep (se 1 (by rfl) ⟨3014414, by rfl⟩ : syracuseStep 4019219 = 6028829) B6028829
theorem B1340455 : Blo 1190412 1340455 := bstep (se 1 (by rfl) ⟨1005341, by rfl⟩ : syracuseStep 1340455 = 2010683) B2010683
theorem B4019543 : Blo 1190412 4019543 := bstep (se 1 (by rfl) ⟨3014657, by rfl⟩ : syracuseStep 4019543 = 6029315) B6029315
theorem B1430959 : Blo 1190412 1430959 := bstep (se 1 (by rfl) ⟨1073219, by rfl⟩ : syracuseStep 1430959 = 2146439) B2146439
theorem B1611191 : Blo 1190412 1611191 := bstep (se 1 (by rfl) ⟨1208393, by rfl⟩ : syracuseStep 1611191 = 2416787) B2416787
theorem B52917745 : Blo 1190412 52917745 := bstep (se 2 (by rfl) ⟨19844154, by rfl⟩ : syracuseStep 52917745 = 39688309) B39688309
theorem B1611343 : Blo 1190412 1611343 := bstep (se 1 (by rfl) ⟨1208507, by rfl⟩ : syracuseStep 1611343 = 2417015) B2417015
theorem B9164411 : Blo 1190412 9164411 := bstep (se 1 (by rfl) ⟨6873308, by rfl⟩ : syracuseStep 9164411 = 13746617) B13746617
theorem B5093113 : Blo 1190412 5093113 := bstep (se 2 (by rfl) ⟨1909917, by rfl⟩ : syracuseStep 5093113 = 3819835) B3819835
theorem B6436675 : Blo 1190412 6436675 := bstep (se 1 (by rfl) ⟨4827506, by rfl⟩ : syracuseStep 6436675 = 9655013) B9655013
theorem B2545481 : Blo 1190412 2545481 := bstep (se 2 (by rfl) ⟨954555, by rfl⟩ : syracuseStep 2545481 = 1909111) B1909111
theorem B6035309 : Blo 1190412 6035309 := bstep (se 3 (by rfl) ⟨1131620, by rfl⟩ : syracuseStep 6035309 = 2263241) B2263241
theorem B7845817 : Blo 1190412 7845817 := bstep (se 2 (by rfl) ⟨2942181, by rfl⟩ : syracuseStep 7845817 = 5884363) B5884363
theorem B6035471 : Blo 1190412 6035471 := bstep (se 1 (by rfl) ⟨4526603, by rfl⟩ : syracuseStep 6035471 = 9053207) B9053207
theorem B6436979 : Blo 1190412 6436979 := bstep (se 1 (by rfl) ⟨4827734, by rfl⟩ : syracuseStep 6436979 = 9655469) B9655469
theorem B3815581 : Blo 1190412 3815581 := bstep (se 3 (by rfl) ⟨715421, by rfl⟩ : syracuseStep 3815581 = 1430843) B1430843
theorem B61937905 : Blo 1190412 61937905 := bstep (se 2 (by rfl) ⟨23226714, by rfl⟩ : syracuseStep 61937905 = 46453429) B46453429
theorem B4020623 : Blo 1190412 4020623 := bstep (se 1 (by rfl) ⟨3015467, by rfl⟩ : syracuseStep 4020623 = 6030935) B6030935
theorem B4520393 : Blo 1190412 4520393 := bstep (se 2 (by rfl) ⟨1695147, by rfl⟩ : syracuseStep 4520393 = 3390295) B3390295
theorem B4020947 : Blo 1190412 4020947 := bstep (se 1 (by rfl) ⟨3015710, by rfl⟩ : syracuseStep 4020947 = 6031421) B6031421
theorem B24468317 : Blo 1190412 24468317 := bstep (se 3 (by rfl) ⟨4587809, by rfl⟩ : syracuseStep 24468317 = 9175619) B9175619
theorem B3013483 : Blo 1190412 3013483 := bstep (se 1 (by rfl) ⟨2260112, by rfl⟩ : syracuseStep 3013483 = 4520225) B4520225
theorem B4520879 : Blo 1190412 4520879 := bstep (se 1 (by rfl) ⟨3390659, by rfl⟩ : syracuseStep 4520879 = 6781319) B6781319
theorem B3218359 : Blo 1190412 3218359 := bstep (se 1 (by rfl) ⟨2413769, by rfl⟩ : syracuseStep 3218359 = 4827539) B4827539
theorem B62774509 : Blo 1190412 62774509 := bstep (se 3 (by rfl) ⟨11770220, by rfl⟩ : syracuseStep 62774509 = 23540441) B23540441
theorem B3014131 : Blo 1190412 3014131 := bstep (se 1 (by rfl) ⟨2260598, by rfl⟩ : syracuseStep 3014131 = 4521197) B4521197
theorem B29359655 : Blo 1190412 29359655 := bstep (se 1 (by rfl) ⟨22019741, by rfl⟩ : syracuseStep 29359655 = 44039483) B44039483
theorem B12877501 : Blo 1190412 12877501 := bstep (se 3 (by rfl) ⟨2414531, by rfl⟩ : syracuseStep 12877501 = 4829063) B4829063
theorem B2678471 : Blo 1190412 2678471 := bstep (se 1 (by rfl) ⟨2008853, by rfl⟩ : syracuseStep 2678471 = 4017707) B4017707
theorem B1507015 : Blo 1190412 1507015 := bstep (se 1 (by rfl) ⟨1130261, by rfl⟩ : syracuseStep 1507015 = 2260523) B2260523
theorem B4521683 : Blo 1190412 4521683 := bstep (se 1 (by rfl) ⟨3391262, by rfl⟩ : syracuseStep 4521683 = 6782525) B6782525
theorem B5881643 : Blo 1190412 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B3669833 : Blo 1190412 3669833 := bstep (se 2 (by rfl) ⟨1376187, by rfl⟩ : syracuseStep 3669833 = 2752375) B2752375
theorem B1785695 : Blo 1190412 1785695 := bstep (se 1 (by rfl) ⟨1339271, by rfl⟩ : syracuseStep 1785695 = 2678543) B2678543
theorem B1785707 : Blo 1190412 1785707 := bstep (se 1 (by rfl) ⟨1339280, by rfl⟩ : syracuseStep 1785707 = 2678561) B2678561
theorem B4292459 : Blo 1190412 4292459 := bstep (se 1 (by rfl) ⟨3219344, by rfl⟩ : syracuseStep 4292459 = 6438689) B6438689
theorem B4022135 : Blo 1190412 4022135 := bstep (se 1 (by rfl) ⟨3016601, by rfl⟩ : syracuseStep 4022135 = 6033203) B6033203
theorem B8593361 : Blo 1190412 8593361 := bstep (se 2 (by rfl) ⟨3222510, by rfl⟩ : syracuseStep 8593361 = 6445021) B6445021
theorem B12230675 : Blo 1190412 12230675 := bstep (se 1 (by rfl) ⟨9173006, by rfl⟩ : syracuseStep 12230675 = 18346013) B18346013
theorem B4022297 : Blo 1190412 4022297 := bstep (se 2 (by rfl) ⟨1508361, by rfl⟩ : syracuseStep 4022297 = 3016723) B3016723
theorem B2146409 : Blo 1190412 2146409 := bstep (se 2 (by rfl) ⟨804903, by rfl⟩ : syracuseStep 2146409 = 1609807) B1609807
theorem B25780355 : Blo 1190412 25780355 := bstep (se 1 (by rfl) ⟨19335266, by rfl⟩ : syracuseStep 25780355 = 38670533) B38670533
theorem B11444435 : Blo 1190412 11444435 := bstep (se 1 (by rfl) ⟨8583326, by rfl⟩ : syracuseStep 11444435 = 17166653) B17166653
theorem B5087441 : Blo 1190412 5087441 := bstep (se 2 (by rfl) ⟨1907790, by rfl⟩ : syracuseStep 5087441 = 3815581) B3815581
theorem B1786121 : Blo 1190412 1786121 := bstep (se 2 (by rfl) ⟨669795, by rfl⟩ : syracuseStep 1786121 = 1339591) B1339591
theorem B3014921 : Blo 1190412 3014921 := bstep (se 2 (by rfl) ⟨1130595, by rfl⟩ : syracuseStep 3014921 = 2261191) B2261191
theorem B82583873 : Blo 1190412 82583873 := bstep (se 2 (by rfl) ⟨30968952, by rfl⟩ : syracuseStep 82583873 = 61937905) B61937905
theorem B1786223 : Blo 1190412 1786223 := bstep (se 1 (by rfl) ⟨1339667, by rfl⟩ : syracuseStep 1786223 = 2679335) B2679335
theorem B3391969 : Blo 1190412 3391969 := bstep (se 2 (by rfl) ⟨1271988, by rfl⟩ : syracuseStep 3391969 = 2543977) B2543977
theorem B1507835 : Blo 1190412 1507835 := bstep (se 1 (by rfl) ⟨1130876, by rfl⟩ : syracuseStep 1507835 = 2261753) B2261753
theorem B30958145 : Blo 1190412 30958145 := bstep (se 2 (by rfl) ⟨11609304, by rfl⟩ : syracuseStep 30958145 = 23218609) B23218609
theorem B1786439 : Blo 1190412 1786439 := bstep (se 1 (by rfl) ⟨1339829, by rfl⟩ : syracuseStep 1786439 = 2679659) B2679659
theorem B1786475 : Blo 1190412 1786475 := bstep (se 1 (by rfl) ⟨1339856, by rfl⟩ : syracuseStep 1786475 = 2679713) B2679713
theorem B6439571 : Blo 1190412 6439571 := bstep (se 1 (by rfl) ⟨4829678, by rfl⟩ : syracuseStep 6439571 = 9659357) B9659357
theorem B2679479 : Blo 1190412 2679479 := bstep (se 1 (by rfl) ⟨2009609, by rfl⟩ : syracuseStep 2679479 = 4019219) B4019219
theorem B5726969 : Blo 1190412 5726969 := bstep (se 2 (by rfl) ⟨2147613, by rfl⟩ : syracuseStep 5726969 = 4295227) B4295227
theorem B10175291 : Blo 1190412 10175291 := bstep (se 1 (by rfl) ⟨7631468, by rfl⟩ : syracuseStep 10175291 = 15262937) B15262937
theorem B1786703 : Blo 1190412 1786703 := bstep (se 1 (by rfl) ⟨1340027, by rfl⟩ : syracuseStep 1786703 = 2680055) B2680055
theorem B2679695 : Blo 1190412 2679695 := bstep (se 1 (by rfl) ⟨2009771, by rfl⟩ : syracuseStep 2679695 = 4019543) B4019543
theorem B3818593 : Blo 1190412 3818593 := bstep (se 2 (by rfl) ⟨1431972, by rfl⟩ : syracuseStep 3818593 = 2863945) B2863945
theorem B1787099 : Blo 1190412 1787099 := bstep (se 1 (by rfl) ⟨1340324, by rfl⟩ : syracuseStep 1787099 = 2680649) B2680649
theorem B1696987 : Blo 1190412 1696987 := bstep (se 1 (by rfl) ⟨1272740, by rfl⟩ : syracuseStep 1696987 = 2545481) B2545481
theorem B3015913 : Blo 1190412 3015913 := bstep (se 2 (by rfl) ⟨1130967, by rfl⟩ : syracuseStep 3015913 = 2261935) B2261935
theorem B4023539 : Blo 1190412 4023539 := bstep (se 1 (by rfl) ⟨3017654, by rfl⟩ : syracuseStep 4023539 = 6035309) B6035309
theorem B4023647 : Blo 1190412 4023647 := bstep (se 1 (by rfl) ⟨3017735, by rfl⟩ : syracuseStep 4023647 = 6035471) B6035471
theorem B1787273 : Blo 1190412 1787273 := bstep (se 2 (by rfl) ⟨670227, by rfl⟩ : syracuseStep 1787273 = 1340455) B1340455
theorem B3016075 : Blo 1190412 3016075 := bstep (se 1 (by rfl) ⟨2262056, by rfl⟩ : syracuseStep 3016075 = 4524113) B4524113
theorem B1508807 : Blo 1190412 1508807 := bstep (se 1 (by rfl) ⟨1131605, by rfl⟩ : syracuseStep 1508807 = 2263211) B2263211
theorem B12879449 : Blo 1190412 12879449 := bstep (se 2 (by rfl) ⟨4829793, by rfl⟩ : syracuseStep 12879449 = 9659587) B9659587
theorem B2680415 : Blo 1190412 2680415 := bstep (se 1 (by rfl) ⟨2010311, by rfl⟩ : syracuseStep 2680415 = 4020623) B4020623
theorem B1508959 : Blo 1190412 1508959 := bstep (se 1 (by rfl) ⟨1131719, by rfl⟩ : syracuseStep 1508959 = 2263439) B2263439
theorem B83699345 : Blo 1190412 83699345 := bstep (se 2 (by rfl) ⟨31387254, by rfl⟩ : syracuseStep 83699345 = 62774509) B62774509
theorem B3393211 : Blo 1190412 3393211 := bstep (se 1 (by rfl) ⟨2544908, by rfl⟩ : syracuseStep 3393211 = 5089817) B5089817
theorem B3016379 : Blo 1190412 3016379 := bstep (se 1 (by rfl) ⟨2262284, by rfl⟩ : syracuseStep 3016379 = 4524569) B4524569
theorem B1787627 : Blo 1190412 1787627 := bstep (se 1 (by rfl) ⟨1340720, by rfl⟩ : syracuseStep 1787627 = 2681441) B2681441
theorem B2680631 : Blo 1190412 2680631 := bstep (se 1 (by rfl) ⟨2010473, by rfl⟩ : syracuseStep 2680631 = 4020947) B4020947
theorem B44091245 : Blo 1190412 44091245 := bstep (se 3 (by rfl) ⟨8267108, by rfl⟩ : syracuseStep 44091245 = 16534217) B16534217
theorem B19318661 : Blo 1190412 19318661 := bstep (se 4 (by rfl) ⟨1811124, by rfl⟩ : syracuseStep 19318661 = 3622249) B3622249
theorem B16312211 : Blo 1190412 16312211 := bstep (se 1 (by rfl) ⟨12234158, by rfl⟩ : syracuseStep 16312211 = 24468317) B24468317
theorem B1787855 : Blo 1190412 1787855 := bstep (se 1 (by rfl) ⟨1340891, by rfl⟩ : syracuseStep 1787855 = 2681783) B2681783
theorem B2262991 : Blo 1190412 2262991 := bstep (se 1 (by rfl) ⟨1697243, by rfl⟩ : syracuseStep 2262991 = 3394487) B3394487
theorem B2680937 : Blo 1190412 2680937 := bstep (se 2 (by rfl) ⟨1005351, by rfl⟩ : syracuseStep 2680937 = 2010703) B2010703
theorem B2148457 : Blo 1190412 2148457 := bstep (se 2 (by rfl) ⟨805671, by rfl⟩ : syracuseStep 2148457 = 1611343) B1611343
theorem B2009353 : Blo 1190412 2009353 := bstep (se 2 (by rfl) ⟨753507, by rfl⟩ : syracuseStep 2009353 = 1507015) B1507015
theorem B1788251 : Blo 1190412 1788251 := bstep (se 1 (by rfl) ⟨1341188, by rfl⟩ : syracuseStep 1788251 = 2682377) B2682377
theorem B19573103 : Blo 1190412 19573103 := bstep (se 1 (by rfl) ⟨14679827, by rfl⟩ : syracuseStep 19573103 = 29359655) B29359655
theorem B22022543 : Blo 1190412 22022543 := bstep (se 1 (by rfl) ⟨16516907, by rfl⟩ : syracuseStep 22022543 = 33033815) B33033815
theorem B1190463 : Blo 1190412 1190463 := bstep (se 1 (by rfl) ⟨892847, by rfl⟩ : syracuseStep 1190463 = 1785695) B1785695
theorem B1788479 : Blo 1190412 1788479 := bstep (se 1 (by rfl) ⟨1341359, by rfl⟩ : syracuseStep 1788479 = 2682719) B2682719
theorem B1190471 : Blo 1190412 1190471 := bstep (se 1 (by rfl) ⟨892853, by rfl⟩ : syracuseStep 1190471 = 1785707) B1785707
theorem B2861639 : Blo 1190412 2861639 := bstep (se 1 (by rfl) ⟨2146229, by rfl⟩ : syracuseStep 2861639 = 4292459) B4292459
theorem B2681423 : Blo 1190412 2681423 := bstep (se 1 (by rfl) ⟨2011067, by rfl⟩ : syracuseStep 2681423 = 4022135) B4022135
theorem B5728907 : Blo 1190412 5728907 := bstep (se 1 (by rfl) ⟨4296680, by rfl⟩ : syracuseStep 5728907 = 8593361) B8593361
theorem B20343473 : Blo 1190412 20343473 := bstep (se 2 (by rfl) ⟨7628802, by rfl⟩ : syracuseStep 20343473 = 15257605) B15257605
theorem B1788599 : Blo 1190412 1788599 := bstep (se 1 (by rfl) ⟨1341449, by rfl⟩ : syracuseStep 1788599 = 2682899) B2682899
theorem B1190623 : Blo 1190412 1190623 := bstep (se 1 (by rfl) ⟨892967, by rfl⟩ : syracuseStep 1190623 = 1785935) B1785935
theorem B2681567 : Blo 1190412 2681567 := bstep (se 1 (by rfl) ⟨2011175, by rfl⟩ : syracuseStep 2681567 = 4022351) B4022351
theorem B5090039 : Blo 1190412 5090039 := bstep (se 1 (by rfl) ⟨3817529, by rfl⟩ : syracuseStep 5090039 = 7635059) B7635059
theorem B1190703 : Blo 1190412 1190703 := bstep (se 1 (by rfl) ⟨893027, by rfl⟩ : syracuseStep 1190703 = 1786055) B1786055
theorem B5720987 : Blo 1190412 5720987 := bstep (se 1 (by rfl) ⟨4290740, by rfl⟩ : syracuseStep 5720987 = 8581481) B8581481
theorem B1190811 : Blo 1190412 1190811 := bstep (se 1 (by rfl) ⟨893108, by rfl⟩ : syracuseStep 1190811 = 1786217) B1786217
theorem B1190863 : Blo 1190412 1190863 := bstep (se 1 (by rfl) ⟨893147, by rfl⟩ : syracuseStep 1190863 = 1786295) B1786295
theorem B2681819 : Blo 1190412 2681819 := bstep (se 1 (by rfl) ⟨2011364, by rfl⟩ : syracuseStep 2681819 = 4022729) B4022729
theorem B1190887 : Blo 1190412 1190887 := bstep (se 1 (by rfl) ⟨893165, by rfl⟩ : syracuseStep 1190887 = 1786331) B1786331
theorem B2681999 : Blo 1190412 2681999 := bstep (se 1 (by rfl) ⟨2011499, by rfl⟩ : syracuseStep 2681999 = 4022999) B4022999
theorem B2682089 : Blo 1190412 2682089 := bstep (se 2 (by rfl) ⟨1005783, by rfl⟩ : syracuseStep 2682089 = 2011567) B2011567
theorem B1191199 : Blo 1190412 1191199 := bstep (se 1 (by rfl) ⟨893399, by rfl⟩ : syracuseStep 1191199 = 1786799) B1786799
theorem B2682143 : Blo 1190412 2682143 := bstep (se 1 (by rfl) ⟨2011607, by rfl⟩ : syracuseStep 2682143 = 4023215) B4023215
theorem B1191259 : Blo 1190412 1191259 := bstep (se 1 (by rfl) ⟨893444, by rfl⟩ : syracuseStep 1191259 = 1786889) B1786889
theorem B1191279 : Blo 1190412 1191279 := bstep (se 1 (by rfl) ⟨893459, by rfl⟩ : syracuseStep 1191279 = 1786919) B1786919
theorem B1191335 : Blo 1190412 1191335 := bstep (se 1 (by rfl) ⟨893501, by rfl⟩ : syracuseStep 1191335 = 1787003) B1787003
theorem B1191419 : Blo 1190412 1191419 := bstep (se 1 (by rfl) ⟨893564, by rfl⟩ : syracuseStep 1191419 = 1787129) B1787129
theorem B1191487 : Blo 1190412 1191487 := bstep (se 1 (by rfl) ⟨893615, by rfl⟩ : syracuseStep 1191487 = 1787231) B1787231
theorem B1191495 : Blo 1190412 1191495 := bstep (se 1 (by rfl) ⟨893621, by rfl⟩ : syracuseStep 1191495 = 1787243) B1787243
theorem B2010811 : Blo 1190412 2010811 := bstep (se 1 (by rfl) ⟨1508108, by rfl⟩ : syracuseStep 2010811 = 3016217) B3016217
theorem B1191647 : Blo 1190412 1191647 := bstep (se 1 (by rfl) ⟨893735, by rfl⟩ : syracuseStep 1191647 = 1787471) B1787471
theorem B2682665 : Blo 1190412 2682665 := bstep (se 2 (by rfl) ⟨1005999, by rfl⟩ : syracuseStep 2682665 = 2011999) B2011999
theorem B1191727 : Blo 1190412 1191727 := bstep (se 1 (by rfl) ⟨893795, by rfl⟩ : syracuseStep 1191727 = 1787591) B1787591
theorem B4017977 : Blo 1190412 4017977 := bstep (se 2 (by rfl) ⟨1506741, by rfl⟩ : syracuseStep 4017977 = 3013483) B3013483
theorem B7630649 : Blo 1190412 7630649 := bstep (se 2 (by rfl) ⟨2861493, by rfl⟩ : syracuseStep 7630649 = 5722987) B5722987
theorem B4296509 : Blo 1190412 4296509 := bstep (se 3 (by rfl) ⟨805595, by rfl⟩ : syracuseStep 4296509 = 1611191) B1611191
theorem B1191835 : Blo 1190412 1191835 := bstep (se 1 (by rfl) ⟨893876, by rfl⟩ : syracuseStep 1191835 = 1787753) B1787753
theorem B1191887 : Blo 1190412 1191887 := bstep (se 1 (by rfl) ⟨893915, by rfl⟩ : syracuseStep 1191887 = 1787831) B1787831
theorem B1191911 : Blo 1190412 1191911 := bstep (se 1 (by rfl) ⟨893933, by rfl⟩ : syracuseStep 1191911 = 1787867) B1787867
theorem B1192223 : Blo 1190412 1192223 := bstep (se 1 (by rfl) ⟨894167, by rfl⟩ : syracuseStep 1192223 = 1788335) B1788335
theorem B1192283 : Blo 1190412 1192283 := bstep (se 1 (by rfl) ⟨894212, by rfl⟩ : syracuseStep 1192283 = 1788425) B1788425
theorem B1192303 : Blo 1190412 1192303 := bstep (se 1 (by rfl) ⟨894227, by rfl⟩ : syracuseStep 1192303 = 1788455) B1788455
theorem B1339771 : Blo 1190412 1339771 := bstep (se 1 (by rfl) ⟨1004828, by rfl⟩ : syracuseStep 1339771 = 2009657) B2009657
theorem B1192359 : Blo 1190412 1192359 := bstep (se 1 (by rfl) ⟨894269, by rfl⟩ : syracuseStep 1192359 = 1788539) B1788539
theorem B12874301 : Blo 1190412 12874301 := bstep (se 3 (by rfl) ⟨2413931, by rfl⟩ : syracuseStep 12874301 = 4827863) B4827863
theorem B2863723 : Blo 1190412 2863723 := bstep (se 1 (by rfl) ⟨2147792, by rfl⟩ : syracuseStep 2863723 = 4295585) B4295585
theorem B4018841 : Blo 1190412 4018841 := bstep (se 2 (by rfl) ⟨1507065, by rfl⟩ : syracuseStep 4018841 = 3014131) B3014131
theorem B5092055 : Blo 1190412 5092055 := bstep (se 1 (by rfl) ⟨3819041, by rfl⟩ : syracuseStep 5092055 = 7638083) B7638083
theorem B2011871 : Blo 1190412 2011871 := bstep (se 1 (by rfl) ⟨1508903, by rfl⟩ : syracuseStep 2011871 = 3017807) B3017807
theorem B1340239 : Blo 1190412 1340239 := bstep (se 1 (by rfl) ⟨1005179, by rfl⟩ : syracuseStep 1340239 = 2010359) B2010359
theorem B6034337 : Blo 1190412 6034337 := bstep (se 2 (by rfl) ⟨2262876, by rfl⟩ : syracuseStep 6034337 = 4525753) B4525753
theorem B3814391 : Blo 1190412 3814391 := bstep (se 1 (by rfl) ⟨2860793, by rfl⟩ : syracuseStep 3814391 = 5721587) B5721587
theorem B8582233 : Blo 1190412 8582233 := bstep (se 2 (by rfl) ⟨3218337, by rfl⟩ : syracuseStep 8582233 = 6436675) B6436675
theorem B3921095 : Blo 1190412 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B2446555 : Blo 1190412 2446555 := bstep (se 1 (by rfl) ⟨1834916, by rfl⟩ : syracuseStep 2446555 = 3669833) B3669833
theorem B1340635 : Blo 1190412 1340635 := bstep (se 1 (by rfl) ⟨1005476, by rfl⟩ : syracuseStep 1340635 = 2010953) B2010953
theorem B4830457 : Blo 1190412 4830457 := bstep (se 2 (by rfl) ⟨1811421, by rfl⟩ : syracuseStep 4830457 = 3622843) B3622843
theorem B5092703 : Blo 1190412 5092703 := bstep (se 1 (by rfl) ⟨3819527, by rfl⟩ : syracuseStep 5092703 = 7639055) B7639055
theorem B51533171 : Blo 1190412 51533171 := bstep (se 1 (by rfl) ⟨38649878, by rfl⟩ : syracuseStep 51533171 = 77299757) B77299757
theorem B38196605 : Blo 1190412 38196605 := bstep (se 3 (by rfl) ⟨7161863, by rfl⟩ : syracuseStep 38196605 = 14323727) B14323727
theorem B4830653 : Blo 1190412 4830653 := bstep (se 3 (by rfl) ⟨905747, by rfl⟩ : syracuseStep 4830653 = 1811495) B1811495
theorem B5723585 : Blo 1190412 5723585 := bstep (se 2 (by rfl) ⟨2146344, by rfl⟩ : syracuseStep 5723585 = 4292689) B4292689
theorem B1340923 : Blo 1190412 1340923 := bstep (se 1 (by rfl) ⟨1005692, by rfl⟩ : syracuseStep 1340923 = 2011385) B2011385
theorem B1431103 : Blo 1190412 1431103 := bstep (se 1 (by rfl) ⟨1073327, by rfl⟩ : syracuseStep 1431103 = 2146655) B2146655
theorem B2717279 : Blo 1190412 2717279 := bstep (se 1 (by rfl) ⟨2037959, by rfl⟩ : syracuseStep 2717279 = 4075919) B4075919
theorem B1341103 : Blo 1190412 1341103 := bstep (se 1 (by rfl) ⟨1005827, by rfl⟩ : syracuseStep 1341103 = 2011655) B2011655
theorem B5437115 : Blo 1190412 5437115 := bstep (se 1 (by rfl) ⟨4077836, by rfl⟩ : syracuseStep 5437115 = 8155673) B8155673
theorem B2545463 : Blo 1190412 2545463 := bstep (se 1 (by rfl) ⟨1909097, by rfl⟩ : syracuseStep 2545463 = 3818195) B3818195
theorem B2864953 : Blo 1190412 2864953 := bstep (se 2 (by rfl) ⟨1074357, by rfl⟩ : syracuseStep 2864953 = 2148715) B2148715
theorem B1341391 : Blo 1190412 1341391 := bstep (se 1 (by rfl) ⟨1006043, by rfl⟩ : syracuseStep 1341391 = 2012087) B2012087
theorem B7739435 : Blo 1190412 7739435 := bstep (se 1 (by rfl) ⟨5804576, by rfl⟩ : syracuseStep 7739435 = 11609153) B11609153
theorem B4020353 : Blo 1190412 4020353 := bstep (se 2 (by rfl) ⟨1507632, by rfl⟩ : syracuseStep 4020353 = 3015265) B3015265
theorem B6109607 : Blo 1190412 6109607 := bstep (se 1 (by rfl) ⟨4582205, by rfl⟩ : syracuseStep 6109607 = 9164411) B9164411
theorem B4020731 : Blo 1190412 4020731 := bstep (se 1 (by rfl) ⟨3015548, by rfl⟩ : syracuseStep 4020731 = 6031097) B6031097
theorem B2578963 : Blo 1190412 2578963 := bstep (se 1 (by rfl) ⟨1934222, by rfl⟩ : syracuseStep 2578963 = 3868445) B3868445
theorem B4291145 : Blo 1190412 4291145 := bstep (se 2 (by rfl) ⟨1609179, by rfl⟩ : syracuseStep 4291145 = 3218359) B3218359
theorem B3218143 : Blo 1190412 3218143 := bstep (se 1 (by rfl) ⟨2413607, by rfl⟩ : syracuseStep 3218143 = 4827215) B4827215
theorem B4291319 : Blo 1190412 4291319 := bstep (se 1 (by rfl) ⟨3218489, by rfl⟩ : syracuseStep 4291319 = 6436979) B6436979
theorem B4021163 : Blo 1190412 4021163 := bstep (se 1 (by rfl) ⟨3015872, by rfl⟩ : syracuseStep 4021163 = 6031745) B6031745
theorem B3013595 : Blo 1190412 3013595 := bstep (se 1 (by rfl) ⟨2260196, by rfl⟩ : syracuseStep 3013595 = 4520393) B4520393
theorem B5430311 : Blo 1190412 5430311 := bstep (se 1 (by rfl) ⟨4072733, by rfl⟩ : syracuseStep 5430311 = 8145467) B8145467
theorem B1907945 : Blo 1190412 1907945 := bstep (se 2 (by rfl) ⟨715479, by rfl⟩ : syracuseStep 1907945 = 1430959) B1430959
theorem B3013919 : Blo 1190412 3013919 := bstep (se 1 (by rfl) ⟨2260439, by rfl⟩ : syracuseStep 3013919 = 4520879) B4520879
theorem B70556993 : Blo 1190412 70556993 := bstep (se 2 (by rfl) ⟨26458872, by rfl⟩ : syracuseStep 70556993 = 52917745) B52917745
theorem B4021703 : Blo 1190412 4021703 := bstep (se 1 (by rfl) ⟨3016277, by rfl⟩ : syracuseStep 4021703 = 6032555) B6032555
theorem B3816953 : Blo 1190412 3816953 := bstep (se 2 (by rfl) ⟨1431357, by rfl⟩ : syracuseStep 3816953 = 2862715) B2862715
theorem B17170001 : Blo 1190412 17170001 := bstep (se 2 (by rfl) ⟨6438750, by rfl⟩ : syracuseStep 17170001 = 12877501) B12877501
theorem B6790817 : Blo 1190412 6790817 := bstep (se 2 (by rfl) ⟨2546556, by rfl⟩ : syracuseStep 6790817 = 5093113) B5093113
theorem B2678507 : Blo 1190412 2678507 := bstep (se 1 (by rfl) ⟨2008880, by rfl⟩ : syracuseStep 2678507 = 4017761) B4017761
theorem B4022027 : Blo 1190412 4022027 := bstep (se 1 (by rfl) ⟨3016520, by rfl⟩ : syracuseStep 4022027 = 6033041) B6033041
theorem B1785641 : Blo 1190412 1785641 := bstep (se 2 (by rfl) ⟨669615, by rfl⟩ : syracuseStep 1785641 = 1339231) B1339231
theorem B1695529 : Blo 1190412 1695529 := bstep (se 2 (by rfl) ⟨635823, by rfl⟩ : syracuseStep 1695529 = 1271647) B1271647
theorem B1785647 : Blo 1190412 1785647 := bstep (se 1 (by rfl) ⟨1339235, by rfl⟩ : syracuseStep 1785647 = 2678471) B2678471
theorem B3014455 : Blo 1190412 3014455 := bstep (se 1 (by rfl) ⟨2260841, by rfl⟩ : syracuseStep 3014455 = 4521683) B4521683
theorem B7634749 : Blo 1190412 7634749 := bstep (se 3 (by rfl) ⟨1431515, by rfl⟩ : syracuseStep 7634749 = 2863031) B2863031
theorem B2678633 : Blo 1190412 2678633 := bstep (se 2 (by rfl) ⟨1004487, by rfl⟩ : syracuseStep 2678633 = 2008975) B2008975
theorem B5087083 : Blo 1190412 5087083 := bstep (se 1 (by rfl) ⟨3815312, by rfl⟩ : syracuseStep 5087083 = 7630625) B7630625
theorem B28974955 : Blo 1190412 28974955 := bstep (se 1 (by rfl) ⟨21731216, by rfl⟩ : syracuseStep 28974955 = 43462433) B43462433
theorem B37674881 : Blo 1190412 37674881 := bstep (se 2 (by rfl) ⟨14128080, by rfl⟩ : syracuseStep 37674881 = 28256161) B28256161
theorem B10461089 : Blo 1190412 10461089 := bstep (se 2 (by rfl) ⟨3922908, by rfl⟩ : syracuseStep 10461089 = 7845817) B7845817
theorem B17186903 : Blo 1190412 17186903 := bstep (se 1 (by rfl) ⟨12890177, by rfl⟩ : syracuseStep 17186903 = 25780355) B25780355
theorem B3391627 : Blo 1190412 3391627 := bstep (se 1 (by rfl) ⟨2543720, by rfl⟩ : syracuseStep 3391627 = 5087441) B5087441
theorem B2679137 : Blo 1190412 2679137 := bstep (se 2 (by rfl) ⟨1004676, by rfl⟩ : syracuseStep 2679137 = 2009353) B2009353
theorem B4293047 : Blo 1190412 4293047 := bstep (se 1 (by rfl) ⟨3219785, by rfl⟩ : syracuseStep 4293047 = 6439571) B6439571
theorem B2679227 : Blo 1190412 2679227 := bstep (se 1 (by rfl) ⟨2009420, by rfl⟩ : syracuseStep 2679227 = 4018841) B4018841
theorem B1786319 : Blo 1190412 1786319 := bstep (se 1 (by rfl) ⟨1339739, by rfl⟩ : syracuseStep 1786319 = 2679479) B2679479
theorem B1786361 : Blo 1190412 1786361 := bstep (se 2 (by rfl) ⟨669885, by rfl⟩ : syracuseStep 1786361 = 1339771) B1339771
theorem B3817979 : Blo 1190412 3817979 := bstep (se 1 (by rfl) ⟨2863484, by rfl⟩ : syracuseStep 3817979 = 5726969) B5726969
theorem B6783527 : Blo 1190412 6783527 := bstep (se 1 (by rfl) ⟨5087645, by rfl⟩ : syracuseStep 6783527 = 10175291) B10175291
theorem B1786463 : Blo 1190412 1786463 := bstep (se 1 (by rfl) ⟨1339847, by rfl⟩ : syracuseStep 1786463 = 2679695) B2679695
theorem B4022891 : Blo 1190412 4022891 := bstep (se 1 (by rfl) ⟨3017168, by rfl⟩ : syracuseStep 4022891 = 6034337) B6034337
theorem B4522625 : Blo 1190412 4522625 := bstep (se 2 (by rfl) ⟨1695984, by rfl⟩ : syracuseStep 4522625 = 3391969) B3391969
theorem B3818297 : Blo 1190412 3818297 := bstep (se 2 (by rfl) ⟨1431861, by rfl⟩ : syracuseStep 3818297 = 2863723) B2863723
theorem B3220435 : Blo 1190412 3220435 := bstep (se 1 (by rfl) ⟨2415326, by rfl⟩ : syracuseStep 3220435 = 4830653) B4830653
theorem B8586299 : Blo 1190412 8586299 := bstep (se 1 (by rfl) ⟨6439724, by rfl⟩ : syracuseStep 8586299 = 12879449) B12879449
theorem B1786943 : Blo 1190412 1786943 := bstep (se 1 (by rfl) ⟨1340207, by rfl⟩ : syracuseStep 1786943 = 2680415) B2680415
theorem B1811519 : Blo 1190412 1811519 := bstep (se 1 (by rfl) ⟨1358639, by rfl⟩ : syracuseStep 1811519 = 2717279) B2717279
theorem B1786985 : Blo 1190412 1786985 := bstep (se 2 (by rfl) ⟨670119, by rfl⟩ : syracuseStep 1786985 = 1340239) B1340239
theorem B4023485 : Blo 1190412 4023485 := bstep (se 3 (by rfl) ⟨754403, by rfl⟩ : syracuseStep 4023485 = 1508807) B1508807
theorem B1787087 : Blo 1190412 1787087 := bstep (se 1 (by rfl) ⟨1340315, by rfl⟩ : syracuseStep 1787087 = 2680631) B2680631
theorem B29394163 : Blo 1190412 29394163 := bstep (se 1 (by rfl) ⟨22045622, by rfl⟩ : syracuseStep 29394163 = 44091245) B44091245
theorem B12879107 : Blo 1190412 12879107 := bstep (se 1 (by rfl) ⟨9659330, by rfl⟩ : syracuseStep 12879107 = 19318661) B19318661
theorem B1787291 : Blo 1190412 1787291 := bstep (se 1 (by rfl) ⟨1340468, by rfl⟩ : syracuseStep 1787291 = 2680937) B2680937
theorem B2680235 : Blo 1190412 2680235 := bstep (se 1 (by rfl) ⟨2010176, by rfl⟩ : syracuseStep 2680235 = 4020353) B4020353
theorem B14681695 : Blo 1190412 14681695 := bstep (se 1 (by rfl) ⟨11011271, by rfl⟩ : syracuseStep 14681695 = 22022543) B22022543
theorem B3262073 : Blo 1190412 3262073 := bstep (se 2 (by rfl) ⟨1223277, by rfl⟩ : syracuseStep 3262073 = 2446555) B2446555
theorem B1787513 : Blo 1190412 1787513 := bstep (se 2 (by rfl) ⟨670317, by rfl⟩ : syracuseStep 1787513 = 1340635) B1340635
theorem B2262649 : Blo 1190412 2262649 := bstep (se 2 (by rfl) ⟨848493, by rfl⟩ : syracuseStep 2262649 = 1696987) B1696987
theorem B15279749 : Blo 1190412 15279749 := bstep (se 4 (by rfl) ⟨1432476, by rfl⟩ : syracuseStep 15279749 = 2864953) B2864953
theorem B6440609 : Blo 1190412 6440609 := bstep (se 2 (by rfl) ⟨2415228, by rfl⟩ : syracuseStep 6440609 = 4830457) B4830457
theorem B2680487 : Blo 1190412 2680487 := bstep (se 1 (by rfl) ⟨2010365, by rfl⟩ : syracuseStep 2680487 = 4020731) B4020731
theorem B2860763 : Blo 1190412 2860763 := bstep (se 1 (by rfl) ⟨2145572, by rfl⟩ : syracuseStep 2860763 = 4291145) B4291145
theorem B1787615 : Blo 1190412 1787615 := bstep (se 1 (by rfl) ⟨1340711, by rfl⟩ : syracuseStep 1787615 = 2681423) B2681423
theorem B1787711 : Blo 1190412 1787711 := bstep (se 1 (by rfl) ⟨1340783, by rfl⟩ : syracuseStep 1787711 = 2681567) B2681567
theorem B2860879 : Blo 1190412 2860879 := bstep (se 1 (by rfl) ⟨2145659, by rfl⟩ : syracuseStep 2860879 = 4291319) B4291319
theorem B3393359 : Blo 1190412 3393359 := bstep (se 1 (by rfl) ⟨2545019, by rfl⟩ : syracuseStep 3393359 = 5090039) B5090039
theorem B2680775 : Blo 1190412 2680775 := bstep (se 1 (by rfl) ⟨2010581, by rfl⟩ : syracuseStep 2680775 = 4021163) B4021163
theorem B2009063 : Blo 1190412 2009063 := bstep (se 1 (by rfl) ⟨1506797, by rfl⟩ : syracuseStep 2009063 = 3013595) B3013595
theorem B1787879 : Blo 1190412 1787879 := bstep (se 1 (by rfl) ⟨1340909, by rfl⟩ : syracuseStep 1787879 = 2681819) B2681819
theorem B1787897 : Blo 1190412 1787897 := bstep (se 2 (by rfl) ⟨670461, by rfl⟩ : syracuseStep 1787897 = 1340923) B1340923
theorem B1787999 : Blo 1190412 1787999 := bstep (se 1 (by rfl) ⟨1340999, by rfl⟩ : syracuseStep 1787999 = 2681999) B2681999
theorem B1271963 : Blo 1190412 1271963 := bstep (se 1 (by rfl) ⟨953972, by rfl⟩ : syracuseStep 1271963 = 1907945) B1907945
theorem B1788059 : Blo 1190412 1788059 := bstep (se 1 (by rfl) ⟨1341044, by rfl⟩ : syracuseStep 1788059 = 2682089) B2682089
theorem B2009279 : Blo 1190412 2009279 := bstep (se 1 (by rfl) ⟨1506959, by rfl⟩ : syracuseStep 2009279 = 3013919) B3013919
theorem B1788095 : Blo 1190412 1788095 := bstep (se 1 (by rfl) ⟨1341071, by rfl⟩ : syracuseStep 1788095 = 2682143) B2682143
theorem B1788137 : Blo 1190412 1788137 := bstep (se 2 (by rfl) ⟨670551, by rfl⟩ : syracuseStep 1788137 = 1341103) B1341103
theorem B4524281 : Blo 1190412 4524281 := bstep (se 2 (by rfl) ⟨1696605, by rfl⟩ : syracuseStep 4524281 = 3393211) B3393211
theorem B2681081 : Blo 1190412 2681081 := bstep (se 2 (by rfl) ⟨1005405, by rfl⟩ : syracuseStep 2681081 = 2010811) B2010811
theorem B2681135 : Blo 1190412 2681135 := bstep (se 1 (by rfl) ⟨2010851, by rfl⟩ : syracuseStep 2681135 = 4021703) B4021703
theorem B11446667 : Blo 1190412 11446667 := bstep (se 1 (by rfl) ⟨8585000, by rfl⟩ : syracuseStep 11446667 = 17170001) B17170001
theorem B15255965 : Blo 1190412 15255965 := bstep (se 3 (by rfl) ⟨2860493, by rfl⟩ : syracuseStep 15255965 = 5720987) B5720987
theorem B2681351 : Blo 1190412 2681351 := bstep (se 1 (by rfl) ⟨2011013, by rfl⟩ : syracuseStep 2681351 = 4022027) B4022027
theorem B1190427 : Blo 1190412 1190427 := bstep (se 1 (by rfl) ⟨892820, by rfl⟩ : syracuseStep 1190427 = 1785641) B1785641
theorem B1788443 : Blo 1190412 1788443 := bstep (se 1 (by rfl) ⟨1341332, by rfl⟩ : syracuseStep 1788443 = 2682665) B2682665
theorem B1190431 : Blo 1190412 1190431 := bstep (se 1 (by rfl) ⟨892823, by rfl⟩ : syracuseStep 1190431 = 1785647) B1785647
theorem B3017321 : Blo 1190412 3017321 := bstep (se 2 (by rfl) ⟨1131495, by rfl⟩ : syracuseStep 3017321 = 2262991) B2262991
theorem B1788521 : Blo 1190412 1788521 := bstep (se 2 (by rfl) ⟨670695, by rfl⟩ : syracuseStep 1788521 = 1341391) B1341391
theorem B6974059 : Blo 1190412 6974059 := bstep (se 1 (by rfl) ⟨5230544, by rfl⟩ : syracuseStep 6974059 = 10461089) B10461089
theorem B8153783 : Blo 1190412 8153783 := bstep (se 1 (by rfl) ⟨6115337, by rfl⟩ : syracuseStep 8153783 = 12230675) B12230675
theorem B2681531 : Blo 1190412 2681531 := bstep (se 1 (by rfl) ⟨2011148, by rfl⟩ : syracuseStep 2681531 = 4022297) B4022297
theorem B7629623 : Blo 1190412 7629623 := bstep (se 1 (by rfl) ⟨5722217, by rfl⟩ : syracuseStep 7629623 = 11444435) B11444435
theorem B1190747 : Blo 1190412 1190747 := bstep (se 1 (by rfl) ⟨893060, by rfl⟩ : syracuseStep 1190747 = 1786121) B1786121
theorem B2009947 : Blo 1190412 2009947 := bstep (se 1 (by rfl) ⟨1507460, by rfl⟩ : syracuseStep 2009947 = 3014921) B3014921
theorem B1190815 : Blo 1190412 1190815 := bstep (se 1 (by rfl) ⟨893111, by rfl⟩ : syracuseStep 1190815 = 1786223) B1786223
theorem B20638763 : Blo 1190412 20638763 := bstep (se 1 (by rfl) ⟨15479072, by rfl⟩ : syracuseStep 20638763 = 30958145) B30958145
theorem B1190959 : Blo 1190412 1190959 := bstep (se 1 (by rfl) ⟨893219, by rfl⟩ : syracuseStep 1190959 = 1786439) B1786439
theorem B1190983 : Blo 1190412 1190983 := bstep (se 1 (by rfl) ⟨893237, by rfl⟩ : syracuseStep 1190983 = 1786475) B1786475
theorem B3394703 : Blo 1190412 3394703 := bstep (se 1 (by rfl) ⟨2546027, by rfl⟩ : syracuseStep 3394703 = 5092055) B5092055
theorem B10456253 : Blo 1190412 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B1191135 : Blo 1190412 1191135 := bstep (se 1 (by rfl) ⟨893351, by rfl⟩ : syracuseStep 1191135 = 1786703) B1786703
theorem B2542927 : Blo 1190412 2542927 := bstep (se 1 (by rfl) ⟨1907195, by rfl⟩ : syracuseStep 2542927 = 3814391) B3814391
theorem B1191399 : Blo 1190412 1191399 := bstep (se 1 (by rfl) ⟨893549, by rfl⟩ : syracuseStep 1191399 = 1787099) B1787099
theorem B2682359 : Blo 1190412 2682359 := bstep (se 1 (by rfl) ⟨2011769, by rfl⟩ : syracuseStep 2682359 = 4023539) B4023539
theorem B2682431 : Blo 1190412 2682431 := bstep (se 1 (by rfl) ⟨2011823, by rfl⟩ : syracuseStep 2682431 = 4023647) B4023647
theorem B3395135 : Blo 1190412 3395135 := bstep (se 1 (by rfl) ⟨2546351, by rfl⟩ : syracuseStep 3395135 = 5092703) B5092703
theorem B25464403 : Blo 1190412 25464403 := bstep (se 1 (by rfl) ⟨19098302, by rfl⟩ : syracuseStep 25464403 = 38196605) B38196605
theorem B1191515 : Blo 1190412 1191515 := bstep (se 1 (by rfl) ⟨893636, by rfl⟩ : syracuseStep 1191515 = 1787273) B1787273
theorem B52194941 : Blo 1190412 52194941 := bstep (se 3 (by rfl) ⟨9786551, by rfl⟩ : syracuseStep 52194941 = 19573103) B19573103
theorem B55799563 : Blo 1190412 55799563 := bstep (se 1 (by rfl) ⟨41849672, by rfl⟩ : syracuseStep 55799563 = 83699345) B83699345
theorem B2010919 : Blo 1190412 2010919 := bstep (se 1 (by rfl) ⟨1508189, by rfl⟩ : syracuseStep 2010919 = 3016379) B3016379
theorem B3624743 : Blo 1190412 3624743 := bstep (se 1 (by rfl) ⟨2718557, by rfl⟩ : syracuseStep 3624743 = 5437115) B5437115
theorem B1191751 : Blo 1190412 1191751 := bstep (se 1 (by rfl) ⟨893813, by rfl⟩ : syracuseStep 1191751 = 1787627) B1787627
theorem B10874807 : Blo 1190412 10874807 := bstep (se 1 (by rfl) ⟨8156105, by rfl⟩ : syracuseStep 10874807 = 16312211) B16312211
theorem B1191903 : Blo 1190412 1191903 := bstep (se 1 (by rfl) ⟨893927, by rfl⟩ : syracuseStep 1191903 = 1787855) B1787855
theorem B5091457 : Blo 1190412 5091457 := bstep (se 2 (by rfl) ⟨1909296, by rfl⟩ : syracuseStep 5091457 = 3818593) B3818593
theorem B1192167 : Blo 1190412 1192167 := bstep (se 1 (by rfl) ⟨894125, by rfl⟩ : syracuseStep 1192167 = 1788251) B1788251
theorem B1192319 : Blo 1190412 1192319 := bstep (se 1 (by rfl) ⟨894239, by rfl⟩ : syracuseStep 1192319 = 1788479) B1788479
theorem B13562315 : Blo 1190412 13562315 := bstep (se 1 (by rfl) ⟨10171736, by rfl⟩ : syracuseStep 13562315 = 20343473) B20343473
theorem B1192399 : Blo 1190412 1192399 := bstep (se 1 (by rfl) ⟨894299, by rfl⟩ : syracuseStep 1192399 = 1788599) B1788599
theorem B2011945 : Blo 1190412 2011945 := bstep (se 2 (by rfl) ⟨754479, by rfl⟩ : syracuseStep 2011945 = 1508959) B1508959
theorem B6787901 : Blo 1190412 6787901 := bstep (se 3 (by rfl) ⟨1272731, by rfl⟩ : syracuseStep 6787901 = 2545463) B2545463
theorem B2544635 : Blo 1190412 2544635 := bstep (se 1 (by rfl) ⟨1908476, by rfl⟩ : syracuseStep 2544635 = 3816953) B3816953
theorem B4019273 : Blo 1190412 4019273 := bstep (se 2 (by rfl) ⟨1507227, by rfl⟩ : syracuseStep 4019273 = 3014455) B3014455
theorem B10179665 : Blo 1190412 10179665 := bstep (se 2 (by rfl) ⟨3817374, by rfl⟩ : syracuseStep 10179665 = 7634749) B7634749
theorem B4527211 : Blo 1190412 4527211 := bstep (se 1 (by rfl) ⟨3395408, by rfl⟩ : syracuseStep 4527211 = 6790817) B6790817
theorem B2864339 : Blo 1190412 2864339 := bstep (se 1 (by rfl) ⟨2148254, by rfl⟩ : syracuseStep 2864339 = 4296509) B4296509
theorem B1430939 : Blo 1190412 1430939 := bstep (se 1 (by rfl) ⟨1073204, by rfl⟩ : syracuseStep 1430939 = 2146409) B2146409
theorem B2864609 : Blo 1190412 2864609 := bstep (se 2 (by rfl) ⟨1074228, by rfl⟩ : syracuseStep 2864609 = 2148457) B2148457
theorem B55055915 : Blo 1190412 55055915 := bstep (se 1 (by rfl) ⟨41291936, by rfl⟩ : syracuseStep 55055915 = 82583873) B82583873
theorem B8582867 : Blo 1190412 8582867 := bstep (se 1 (by rfl) ⟨6437150, by rfl⟩ : syracuseStep 8582867 = 12874301) B12874301
theorem B1341247 : Blo 1190412 1341247 := bstep (se 1 (by rfl) ⟨1005935, by rfl⟩ : syracuseStep 1341247 = 2011871) B2011871
theorem B3438617 : Blo 1190412 3438617 := bstep (se 2 (by rfl) ⟨1289481, by rfl⟩ : syracuseStep 3438617 = 2578963) B2578963
theorem B34355447 : Blo 1190412 34355447 := bstep (se 1 (by rfl) ⟨25766585, by rfl⟩ : syracuseStep 34355447 = 51533171) B51533171
theorem B4290857 : Blo 1190412 4290857 := bstep (se 2 (by rfl) ⟨1609071, by rfl⟩ : syracuseStep 4290857 = 3218143) B3218143
theorem B3815723 : Blo 1190412 3815723 := bstep (se 1 (by rfl) ⟨2861792, by rfl⟩ : syracuseStep 3815723 = 5723585) B5723585
theorem B16292285 : Blo 1190412 16292285 := bstep (se 3 (by rfl) ⟨3054803, by rfl⟩ : syracuseStep 16292285 = 6109607) B6109607
theorem B4020893 : Blo 1190412 4020893 := bstep (se 3 (by rfl) ⟨753917, by rfl⟩ : syracuseStep 4020893 = 1507835) B1507835
theorem B5159623 : Blo 1190412 5159623 := bstep (se 1 (by rfl) ⟨3869717, by rfl⟩ : syracuseStep 5159623 = 7739435) B7739435
theorem B11442977 : Blo 1190412 11442977 := bstep (se 2 (by rfl) ⟨4291116, by rfl⟩ : syracuseStep 11442977 = 8582233) B8582233
theorem B4021217 : Blo 1190412 4021217 := bstep (se 2 (by rfl) ⟨1507956, by rfl⟩ : syracuseStep 4021217 = 3015913) B3015913
theorem B15277085 : Blo 1190412 15277085 := bstep (se 3 (by rfl) ⟨2864453, by rfl⟩ : syracuseStep 15277085 = 5728907) B5728907
theorem B1907759 : Blo 1190412 1907759 := bstep (se 1 (by rfl) ⟨1430819, by rfl⟩ : syracuseStep 1907759 = 2861639) B2861639
theorem B4021433 : Blo 1190412 4021433 := bstep (se 2 (by rfl) ⟨1508037, by rfl⟩ : syracuseStep 4021433 = 3016075) B3016075
theorem B3620207 : Blo 1190412 3620207 := bstep (se 1 (by rfl) ⟨2715155, by rfl⟩ : syracuseStep 3620207 = 5430311) B5430311
theorem B1908137 : Blo 1190412 1908137 := bstep (se 2 (by rfl) ⟨715551, by rfl⟩ : syracuseStep 1908137 = 1431103) B1431103
theorem B47037995 : Blo 1190412 47037995 := bstep (se 1 (by rfl) ⟨35278496, by rfl⟩ : syracuseStep 47037995 = 70556993) B70556993
theorem B2260705 : Blo 1190412 2260705 := bstep (se 2 (by rfl) ⟨847764, by rfl⟩ : syracuseStep 2260705 = 1695529) B1695529
theorem B6782777 : Blo 1190412 6782777 := bstep (se 2 (by rfl) ⟨2543541, by rfl⟩ : syracuseStep 6782777 = 5087083) B5087083
theorem B38633273 : Blo 1190412 38633273 := bstep (se 2 (by rfl) ⟨14487477, by rfl⟩ : syracuseStep 38633273 = 28974955) B28974955
theorem B1785671 : Blo 1190412 1785671 := bstep (se 1 (by rfl) ⟨1339253, by rfl⟩ : syracuseStep 1785671 = 2678507) B2678507
theorem B5087099 : Blo 1190412 5087099 := bstep (se 1 (by rfl) ⟨3815324, by rfl⟩ : syracuseStep 5087099 = 7630649) B7630649
theorem B2678651 : Blo 1190412 2678651 := bstep (se 1 (by rfl) ⟨2008988, by rfl⟩ : syracuseStep 2678651 = 4017977) B4017977
theorem B1785755 : Blo 1190412 1785755 := bstep (se 1 (by rfl) ⟨1339316, by rfl⟩ : syracuseStep 1785755 = 2678633) B2678633
theorem B25116587 : Blo 1190412 25116587 := bstep (se 1 (by rfl) ⟨18837440, by rfl⟩ : syracuseStep 25116587 = 37674881) B37674881
theorem B5087357 : Blo 1190412 5087357 := bstep (se 3 (by rfl) ⟨953879, by rfl⟩ : syracuseStep 5087357 = 1907759) B1907759
theorem B4522169 : Blo 1190412 4522169 := bstep (se 2 (by rfl) ⟨1695813, by rfl⟩ : syracuseStep 4522169 = 3391627) B3391627
theorem B1786091 : Blo 1190412 1786091 := bstep (se 1 (by rfl) ⟨1339568, by rfl⟩ : syracuseStep 1786091 = 2679137) B2679137
theorem B1786151 : Blo 1190412 1786151 := bstep (se 1 (by rfl) ⟨1339613, by rfl⟩ : syracuseStep 1786151 = 2679227) B2679227
theorem B4522351 : Blo 1190412 4522351 := bstep (se 1 (by rfl) ⟨3391763, by rfl⟩ : syracuseStep 4522351 = 6783527) B6783527
theorem B3391901 : Blo 1190412 3391901 := bstep (se 3 (by rfl) ⟨635981, by rfl⟩ : syracuseStep 3391901 = 1271963) B1271963
theorem B3015083 : Blo 1190412 3015083 := bstep (se 1 (by rfl) ⟨2261312, by rfl⟩ : syracuseStep 3015083 = 4522625) B4522625
theorem B2679515 : Blo 1190412 2679515 := bstep (se 1 (by rfl) ⟨2009636, by rfl⟩ : syracuseStep 2679515 = 4019273) B4019273
theorem B1909559 : Blo 1190412 1909559 := bstep (se 1 (by rfl) ⟨1432169, by rfl⟩ : syracuseStep 1909559 = 2864339) B2864339
theorem B9298745 : Blo 1190412 9298745 := bstep (se 2 (by rfl) ⟨3487029, by rfl⟩ : syracuseStep 9298745 = 6974059) B6974059
theorem B8586071 : Blo 1190412 8586071 := bstep (se 1 (by rfl) ⟨6439553, by rfl⟩ : syracuseStep 8586071 = 12879107) B12879107
theorem B1786823 : Blo 1190412 1786823 := bstep (se 1 (by rfl) ⟨1340117, by rfl⟩ : syracuseStep 1786823 = 2680235) B2680235
theorem B1909739 : Blo 1190412 1909739 := bstep (se 1 (by rfl) ⟨1432304, by rfl⟩ : syracuseStep 1909739 = 2864609) B2864609
theorem B4293739 : Blo 1190412 4293739 := bstep (se 1 (by rfl) ⟨3220304, by rfl⟩ : syracuseStep 4293739 = 6440609) B6440609
theorem B5088365 : Blo 1190412 5088365 := bstep (se 3 (by rfl) ⟨954068, by rfl⟩ : syracuseStep 5088365 = 1908137) B1908137
theorem B1786991 : Blo 1190412 1786991 := bstep (se 1 (by rfl) ⟨1340243, by rfl⟩ : syracuseStep 1786991 = 2680487) B2680487
theorem B2679929 : Blo 1190412 2679929 := bstep (se 2 (by rfl) ⟨1004973, by rfl⟩ : syracuseStep 2679929 = 2009947) B2009947
theorem B2262239 : Blo 1190412 2262239 := bstep (se 1 (by rfl) ⟨1696679, by rfl⟩ : syracuseStep 2262239 = 3393359) B3393359
theorem B4293913 : Blo 1190412 4293913 := bstep (se 2 (by rfl) ⟨1610217, by rfl⟩ : syracuseStep 4293913 = 3220435) B3220435
theorem B1787183 : Blo 1190412 1787183 := bstep (se 1 (by rfl) ⟨1340387, by rfl⟩ : syracuseStep 1787183 = 2680775) B2680775
theorem B3016187 : Blo 1190412 3016187 := bstep (se 1 (by rfl) ⟨2262140, by rfl⟩ : syracuseStep 3016187 = 4524281) B4524281
theorem B1787387 : Blo 1190412 1787387 := bstep (se 1 (by rfl) ⟨1340540, by rfl⟩ : syracuseStep 1787387 = 2681081) B2681081
theorem B9053693 : Blo 1190412 9053693 := bstep (se 3 (by rfl) ⟨1697567, by rfl⟩ : syracuseStep 9053693 = 3395135) B3395135
theorem B2860571 : Blo 1190412 2860571 := bstep (se 1 (by rfl) ⟨2145428, by rfl⟩ : syracuseStep 2860571 = 4290857) B4290857
theorem B1787423 : Blo 1190412 1787423 := bstep (se 1 (by rfl) ⟨1340567, by rfl⟩ : syracuseStep 1787423 = 2681135) B2681135
theorem B39192217 : Blo 1190412 39192217 := bstep (se 2 (by rfl) ⟨14697081, by rfl⟩ : syracuseStep 39192217 = 29394163) B29394163
theorem B1787567 : Blo 1190412 1787567 := bstep (se 1 (by rfl) ⟨1340675, by rfl⟩ : syracuseStep 1787567 = 2681351) B2681351
theorem B2680595 : Blo 1190412 2680595 := bstep (se 1 (by rfl) ⟨2010446, by rfl⟩ : syracuseStep 2680595 = 4020893) B4020893
theorem B1787687 : Blo 1190412 1787687 := bstep (se 1 (by rfl) ⟨1340765, by rfl⟩ : syracuseStep 1787687 = 2681531) B2681531
theorem B7628651 : Blo 1190412 7628651 := bstep (se 1 (by rfl) ⟨5721488, by rfl⟩ : syracuseStep 7628651 = 11442977) B11442977
theorem B7628701 : Blo 1190412 7628701 := bstep (se 3 (by rfl) ⟨1430381, by rfl⟩ : syracuseStep 7628701 = 2860763) B2860763
theorem B2680811 : Blo 1190412 2680811 := bstep (se 1 (by rfl) ⟨2010608, by rfl⟩ : syracuseStep 2680811 = 4021217) B4021217
theorem B10184723 : Blo 1190412 10184723 := bstep (se 1 (by rfl) ⟨7638542, by rfl⟩ : syracuseStep 10184723 = 15277085) B15277085
theorem B2263135 : Blo 1190412 2263135 := bstep (se 1 (by rfl) ⟨1697351, by rfl⟩ : syracuseStep 2263135 = 3394703) B3394703
theorem B2680955 : Blo 1190412 2680955 := bstep (se 1 (by rfl) ⟨2010716, by rfl⟩ : syracuseStep 2680955 = 4021433) B4021433
theorem B3016865 : Blo 1190412 3016865 := bstep (se 2 (by rfl) ⟨1131324, by rfl⟩ : syracuseStep 3016865 = 2262649) B2262649
theorem B1788239 : Blo 1190412 1788239 := bstep (se 1 (by rfl) ⟨1341179, by rfl⟩ : syracuseStep 1788239 = 2682359) B2682359
theorem B1788287 : Blo 1190412 1788287 := bstep (se 1 (by rfl) ⟨1341215, by rfl⟩ : syracuseStep 1788287 = 2682431) B2682431
theorem B2681225 : Blo 1190412 2681225 := bstep (se 2 (by rfl) ⟨1005459, by rfl⟩ : syracuseStep 2681225 = 2010919) B2010919
theorem B1788329 : Blo 1190412 1788329 := bstep (se 2 (by rfl) ⟨670623, by rfl⟩ : syracuseStep 1788329 = 1341247) B1341247
theorem B1190447 : Blo 1190412 1190447 := bstep (se 1 (by rfl) ⟨892835, by rfl⟩ : syracuseStep 1190447 = 1785671) B1785671
theorem B1190503 : Blo 1190412 1190503 := bstep (se 1 (by rfl) ⟨892877, by rfl⟩ : syracuseStep 1190503 = 1785755) B1785755
theorem B6785693 : Blo 1190412 6785693 := bstep (se 3 (by rfl) ⟨1272317, by rfl⟩ : syracuseStep 6785693 = 2544635) B2544635
theorem B36678581 : Blo 1190412 36678581 := bstep (se 5 (by rfl) ⟨1719308, by rfl⟩ : syracuseStep 36678581 = 3438617) B3438617
theorem B1190879 : Blo 1190412 1190879 := bstep (se 1 (by rfl) ⟨893159, by rfl⟩ : syracuseStep 1190879 = 1786319) B1786319
theorem B1190907 : Blo 1190412 1190907 := bstep (se 1 (by rfl) ⟨893180, by rfl⟩ : syracuseStep 1190907 = 1786361) B1786361
theorem B1190975 : Blo 1190412 1190975 := bstep (se 1 (by rfl) ⟨893231, by rfl⟩ : syracuseStep 1190975 = 1786463) B1786463
theorem B2681927 : Blo 1190412 2681927 := bstep (se 1 (by rfl) ⟨2011445, by rfl⟩ : syracuseStep 2681927 = 4022891) B4022891
theorem B4525267 : Blo 1190412 4525267 := bstep (se 1 (by rfl) ⟨3393950, by rfl⟩ : syracuseStep 4525267 = 6787901) B6787901
theorem B1191295 : Blo 1190412 1191295 := bstep (se 1 (by rfl) ⟨893471, by rfl⟩ : syracuseStep 1191295 = 1786943) B1786943
theorem B1207679 : Blo 1190412 1207679 := bstep (se 1 (by rfl) ⟨905759, by rfl⟩ : syracuseStep 1207679 = 1811519) B1811519
theorem B6786443 : Blo 1190412 6786443 := bstep (se 1 (by rfl) ⟨5089832, by rfl⟩ : syracuseStep 6786443 = 10179665) B10179665
theorem B1191323 : Blo 1190412 1191323 := bstep (se 1 (by rfl) ⟨893492, by rfl⟩ : syracuseStep 1191323 = 1786985) B1786985
theorem B2682323 : Blo 1190412 2682323 := bstep (se 1 (by rfl) ⟨2011742, by rfl⟩ : syracuseStep 2682323 = 4023485) B4023485
theorem B1191391 : Blo 1190412 1191391 := bstep (se 1 (by rfl) ⟨893543, by rfl⟩ : syracuseStep 1191391 = 1787087) B1787087
theorem B1191527 : Blo 1190412 1191527 := bstep (se 1 (by rfl) ⟨893645, by rfl⟩ : syracuseStep 1191527 = 1787291) B1787291
theorem B36703943 : Blo 1190412 36703943 := bstep (se 1 (by rfl) ⟨27527957, by rfl⟩ : syracuseStep 36703943 = 55055915) B55055915
theorem B2682593 : Blo 1190412 2682593 := bstep (se 2 (by rfl) ⟨1005972, by rfl⟩ : syracuseStep 2682593 = 2011945) B2011945
theorem B1191675 : Blo 1190412 1191675 := bstep (se 1 (by rfl) ⟨893756, by rfl⟩ : syracuseStep 1191675 = 1787513) B1787513
theorem B10186499 : Blo 1190412 10186499 := bstep (se 1 (by rfl) ⟨7639874, by rfl⟩ : syracuseStep 10186499 = 15279749) B15279749
theorem B5721911 : Blo 1190412 5721911 := bstep (se 1 (by rfl) ⟨4291433, by rfl⟩ : syracuseStep 5721911 = 8582867) B8582867
theorem B11448125 : Blo 1190412 11448125 := bstep (se 3 (by rfl) ⟨2146523, by rfl⟩ : syracuseStep 11448125 = 4293047) B4293047
theorem B1191743 : Blo 1190412 1191743 := bstep (se 1 (by rfl) ⟨893807, by rfl⟩ : syracuseStep 1191743 = 1787615) B1787615
theorem B1191807 : Blo 1190412 1191807 := bstep (se 1 (by rfl) ⟨893855, by rfl⟩ : syracuseStep 1191807 = 1787711) B1787711
theorem B1339375 : Blo 1190412 1339375 := bstep (se 1 (by rfl) ⟨1004531, by rfl⟩ : syracuseStep 1339375 = 2009063) B2009063
theorem B1191919 : Blo 1190412 1191919 := bstep (se 1 (by rfl) ⟨893939, by rfl⟩ : syracuseStep 1191919 = 1787879) B1787879
theorem B1191931 : Blo 1190412 1191931 := bstep (se 1 (by rfl) ⟨893948, by rfl⟩ : syracuseStep 1191931 = 1787897) B1787897
theorem B1191999 : Blo 1190412 1191999 := bstep (se 1 (by rfl) ⟨893999, by rfl⟩ : syracuseStep 1191999 = 1787999) B1787999
theorem B1192039 : Blo 1190412 1192039 := bstep (se 1 (by rfl) ⟨894029, by rfl⟩ : syracuseStep 1192039 = 1788059) B1788059
theorem B1339519 : Blo 1190412 1339519 := bstep (se 1 (by rfl) ⟨1004639, by rfl⟩ : syracuseStep 1339519 = 2009279) B2009279
theorem B1192063 : Blo 1190412 1192063 := bstep (se 1 (by rfl) ⟨894047, by rfl⟩ : syracuseStep 1192063 = 1788095) B1788095
theorem B1192091 : Blo 1190412 1192091 := bstep (se 1 (by rfl) ⟨894068, by rfl⟩ : syracuseStep 1192091 = 1788137) B1788137
theorem B2543815 : Blo 1190412 2543815 := bstep (se 1 (by rfl) ⟨1907861, by rfl⟩ : syracuseStep 2543815 = 3815723) B3815723
theorem B7631111 : Blo 1190412 7631111 := bstep (se 1 (by rfl) ⟨5723333, by rfl⟩ : syracuseStep 7631111 = 11446667) B11446667
theorem B10170643 : Blo 1190412 10170643 := bstep (se 1 (by rfl) ⟨7627982, by rfl⟩ : syracuseStep 10170643 = 15255965) B15255965
theorem B1192295 : Blo 1190412 1192295 := bstep (se 1 (by rfl) ⟨894221, by rfl⟩ : syracuseStep 1192295 = 1788443) B1788443
theorem B2011547 : Blo 1190412 2011547 := bstep (se 1 (by rfl) ⟨1508660, by rfl⟩ : syracuseStep 2011547 = 3017321) B3017321
theorem B1192347 : Blo 1190412 1192347 := bstep (se 1 (by rfl) ⟨894260, by rfl⟩ : syracuseStep 1192347 = 1788521) B1788521
theorem B5435855 : Blo 1190412 5435855 := bstep (se 1 (by rfl) ⟨4076891, by rfl⟩ : syracuseStep 5435855 = 8153783) B8153783
theorem B13759175 : Blo 1190412 13759175 := bstep (se 1 (by rfl) ⟨10319381, by rfl⟩ : syracuseStep 13759175 = 20638763) B20638763
theorem B33952537 : Blo 1190412 33952537 := bstep (se 2 (by rfl) ⟨12732201, by rfl⟩ : syracuseStep 33952537 = 25464403) B25464403
theorem B19575593 : Blo 1190412 19575593 := bstep (se 2 (by rfl) ⟨7340847, by rfl⟩ : syracuseStep 19575593 = 14681695) B14681695
theorem B2413471 : Blo 1190412 2413471 := bstep (se 1 (by rfl) ⟨1810103, by rfl⟩ : syracuseStep 2413471 = 3620207) B3620207
theorem B34796627 : Blo 1190412 34796627 := bstep (se 1 (by rfl) ⟨26097470, by rfl⟩ : syracuseStep 34796627 = 52194941) B52194941
theorem B3814505 : Blo 1190412 3814505 := bstep (se 2 (by rfl) ⟨1430439, by rfl⟩ : syracuseStep 3814505 = 2860879) B2860879
theorem B11457935 : Blo 1190412 11457935 := bstep (se 1 (by rfl) ⟨8593451, by rfl⟩ : syracuseStep 11457935 = 17186903) B17186903
theorem B6788609 : Blo 1190412 6788609 := bstep (se 2 (by rfl) ⟨2545728, by rfl⟩ : syracuseStep 6788609 = 5091457) B5091457
theorem B9041543 : Blo 1190412 9041543 := bstep (se 1 (by rfl) ⟨6781157, by rfl⟩ : syracuseStep 9041543 = 13562315) B13562315
theorem B2545319 : Blo 1190412 2545319 := bstep (se 1 (by rfl) ⟨1908989, by rfl⟩ : syracuseStep 2545319 = 3817979) B3817979
theorem B5724199 : Blo 1190412 5724199 := bstep (se 1 (by rfl) ⟨4293149, by rfl⟩ : syracuseStep 5724199 = 8586299) B8586299
theorem B6879497 : Blo 1190412 6879497 := bstep (se 2 (by rfl) ⟨2579811, by rfl⟩ : syracuseStep 6879497 = 5159623) B5159623
theorem B3815837 : Blo 1190412 3815837 := bstep (se 3 (by rfl) ⟨715469, by rfl⟩ : syracuseStep 3815837 = 1430939) B1430939
theorem B6036281 : Blo 1190412 6036281 := bstep (se 2 (by rfl) ⟨2263605, by rfl⟩ : syracuseStep 6036281 = 4527211) B4527211
theorem B22903631 : Blo 1190412 22903631 := bstep (se 1 (by rfl) ⟨17177723, by rfl⟩ : syracuseStep 22903631 = 34355447) B34355447
theorem B10861523 : Blo 1190412 10861523 := bstep (se 1 (by rfl) ⟨8146142, by rfl⟩ : syracuseStep 10861523 = 16292285) B16292285
theorem B8698861 : Blo 1190412 8698861 := bstep (se 3 (by rfl) ⟨1631036, by rfl⟩ : syracuseStep 8698861 = 3262073) B3262073
theorem B3390569 : Blo 1190412 3390569 := bstep (se 2 (by rfl) ⟨1271463, by rfl⟩ : syracuseStep 3390569 = 2542927) B2542927
theorem B5086415 : Blo 1190412 5086415 := bstep (se 1 (by rfl) ⟨3814811, by rfl⟩ : syracuseStep 5086415 = 7629623) B7629623
theorem B6970835 : Blo 1190412 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B10182125 : Blo 1190412 10182125 := bstep (se 3 (by rfl) ⟨1909148, by rfl⟩ : syracuseStep 10182125 = 3818297) B3818297
theorem B3014273 : Blo 1190412 3014273 := bstep (se 2 (by rfl) ⟨1130352, by rfl⟩ : syracuseStep 3014273 = 2260705) B2260705
theorem B74399417 : Blo 1190412 74399417 := bstep (se 2 (by rfl) ⟨27899781, by rfl⟩ : syracuseStep 74399417 = 55799563) B55799563
theorem B31358663 : Blo 1190412 31358663 := bstep (se 1 (by rfl) ⟨23518997, by rfl⟩ : syracuseStep 31358663 = 47037995) B47037995
theorem B2416495 : Blo 1190412 2416495 := bstep (se 1 (by rfl) ⟨1812371, by rfl⟩ : syracuseStep 2416495 = 3624743) B3624743
theorem B25755515 : Blo 1190412 25755515 := bstep (se 1 (by rfl) ⟨19316636, by rfl⟩ : syracuseStep 25755515 = 38633273) B38633273
theorem B4521851 : Blo 1190412 4521851 := bstep (se 1 (by rfl) ⟨3391388, by rfl⟩ : syracuseStep 4521851 = 6782777) B6782777
theorem B1785767 : Blo 1190412 1785767 := bstep (se 1 (by rfl) ⟨1339325, by rfl⟩ : syracuseStep 1785767 = 2678651) B2678651
theorem B3391399 : Blo 1190412 3391399 := bstep (se 1 (by rfl) ⟨2543549, by rfl⟩ : syracuseStep 3391399 = 5087099) B5087099
theorem B16744391 : Blo 1190412 16744391 := bstep (se 1 (by rfl) ⟨12558293, by rfl⟩ : syracuseStep 16744391 = 25116587) B25116587
theorem B7249871 : Blo 1190412 7249871 := bstep (se 1 (by rfl) ⟨5437403, by rfl⟩ : syracuseStep 7249871 = 10874807) B10874807
theorem B3391571 : Blo 1190412 3391571 := bstep (se 1 (by rfl) ⟨2543678, by rfl⟩ : syracuseStep 3391571 = 5087357) B5087357
theorem B3014779 : Blo 1190412 3014779 := bstep (se 1 (by rfl) ⟨2261084, by rfl⟩ : syracuseStep 3014779 = 4522169) B4522169
theorem B1786025 : Blo 1190412 1786025 := bstep (se 2 (by rfl) ⟨669759, by rfl⟩ : syracuseStep 1786025 = 1339519) B1339519
theorem B5087407 : Blo 1190412 5087407 := bstep (se 1 (by rfl) ⟨3815555, by rfl⟩ : syracuseStep 5087407 = 7631111) B7631111
theorem B3391753 : Blo 1190412 3391753 := bstep (se 2 (by rfl) ⟨1271907, by rfl⟩ : syracuseStep 3391753 = 2543815) B2543815
theorem B2261267 : Blo 1190412 2261267 := bstep (se 1 (by rfl) ⟨1695950, by rfl⟩ : syracuseStep 2261267 = 3391901) B3391901
theorem B1786343 : Blo 1190412 1786343 := bstep (se 1 (by rfl) ⟨1339757, by rfl⟩ : syracuseStep 1786343 = 2679515) B2679515
theorem B6029801 : Blo 1190412 6029801 := bstep (se 2 (by rfl) ⟨2261175, by rfl⟩ : syracuseStep 6029801 = 4522351) B4522351
theorem B13050395 : Blo 1190412 13050395 := bstep (se 1 (by rfl) ⟨9787796, by rfl⟩ : syracuseStep 13050395 = 19575593) B19575593
theorem B3392243 : Blo 1190412 3392243 := bstep (se 1 (by rfl) ⟨2544182, by rfl⟩ : syracuseStep 3392243 = 5088365) B5088365
theorem B1786619 : Blo 1190412 1786619 := bstep (se 1 (by rfl) ⟨1339964, by rfl⟩ : syracuseStep 1786619 = 2679929) B2679929
theorem B1508159 : Blo 1190412 1508159 := bstep (se 1 (by rfl) ⟨1131119, by rfl⟩ : syracuseStep 1508159 = 2262239) B2262239
theorem B1696879 : Blo 1190412 1696879 := bstep (se 1 (by rfl) ⟨1272659, by rfl⟩ : syracuseStep 1696879 = 2545319) B2545319
theorem B1787063 : Blo 1190412 1787063 := bstep (se 1 (by rfl) ⟨1340297, by rfl⟩ : syracuseStep 1787063 = 2680595) B2680595
theorem B1787207 : Blo 1190412 1787207 := bstep (se 1 (by rfl) ⟨1340405, by rfl⟩ : syracuseStep 1787207 = 2680811) B2680811
theorem B1787303 : Blo 1190412 1787303 := bstep (se 1 (by rfl) ⟨1340477, by rfl⟩ : syracuseStep 1787303 = 2680955) B2680955
theorem B1787483 : Blo 1190412 1787483 := bstep (se 1 (by rfl) ⟨1340612, by rfl⟩ : syracuseStep 1787483 = 2681225) B2681225
theorem B4523795 : Blo 1190412 4523795 := bstep (se 1 (by rfl) ⟨3392846, by rfl⟩ : syracuseStep 4523795 = 6785693) B6785693
theorem B4024187 : Blo 1190412 4024187 := bstep (se 1 (by rfl) ⟨3018140, by rfl⟩ : syracuseStep 4024187 = 6036281) B6036281
theorem B1787951 : Blo 1190412 1787951 := bstep (se 1 (by rfl) ⟨1340963, by rfl⟩ : syracuseStep 1787951 = 2681927) B2681927
theorem B4524295 : Blo 1190412 4524295 := bstep (se 1 (by rfl) ⟨3393221, by rfl⟩ : syracuseStep 4524295 = 6786443) B6786443
theorem B4647223 : Blo 1190412 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B1788215 : Blo 1190412 1788215 := bstep (se 1 (by rfl) ⟨1341161, by rfl⟩ : syracuseStep 1788215 = 2682323) B2682323
theorem B2009515 : Blo 1190412 2009515 := bstep (se 1 (by rfl) ⟨1507136, by rfl⟩ : syracuseStep 2009515 = 3014273) B3014273
theorem B3221993 : Blo 1190412 3221993 := bstep (se 2 (by rfl) ⟨1208247, by rfl⟩ : syracuseStep 3221993 = 2416495) B2416495
theorem B1788395 : Blo 1190412 1788395 := bstep (se 1 (by rfl) ⟨1341296, by rfl⟩ : syracuseStep 1788395 = 2682593) B2682593
theorem B1190511 : Blo 1190412 1190511 := bstep (se 1 (by rfl) ⟨892883, by rfl⟩ : syracuseStep 1190511 = 1785767) B1785767
theorem B3017513 : Blo 1190412 3017513 := bstep (se 2 (by rfl) ⟨1131567, by rfl⟩ : syracuseStep 3017513 = 2263135) B2263135
theorem B1190727 : Blo 1190412 1190727 := bstep (se 1 (by rfl) ⟨893045, by rfl⟩ : syracuseStep 1190727 = 1786091) B1786091
theorem B1190767 : Blo 1190412 1190767 := bstep (se 1 (by rfl) ⟨893075, by rfl⟩ : syracuseStep 1190767 = 1786151) B1786151
theorem B2010055 : Blo 1190412 2010055 := bstep (se 1 (by rfl) ⟨1507541, by rfl⟩ : syracuseStep 2010055 = 3015083) B3015083
theorem B3623903 : Blo 1190412 3623903 := bstep (se 1 (by rfl) ⟨2717927, by rfl⟩ : syracuseStep 3623903 = 5435855) B5435855
theorem B13560857 : Blo 1190412 13560857 := bstep (se 2 (by rfl) ⟨5085321, by rfl⟩ : syracuseStep 13560857 = 10170643) B10170643
theorem B1273039 : Blo 1190412 1273039 := bstep (se 1 (by rfl) ⟨954779, by rfl⟩ : syracuseStep 1273039 = 1909559) B1909559
theorem B22899941 : Blo 1190412 22899941 := bstep (se 4 (by rfl) ⟨2146869, by rfl⟩ : syracuseStep 22899941 = 4293739) B4293739
theorem B1191215 : Blo 1190412 1191215 := bstep (se 1 (by rfl) ⟨893411, by rfl⟩ : syracuseStep 1191215 = 1786823) B1786823
theorem B1273159 : Blo 1190412 1273159 := bstep (se 1 (by rfl) ⟨954869, by rfl⟩ : syracuseStep 1273159 = 1909739) B1909739
theorem B2543003 : Blo 1190412 2543003 := bstep (se 1 (by rfl) ⟨1907252, by rfl⟩ : syracuseStep 2543003 = 3814505) B3814505
theorem B1191327 : Blo 1190412 1191327 := bstep (se 1 (by rfl) ⟨893495, by rfl⟩ : syracuseStep 1191327 = 1786991) B1786991
theorem B1191455 : Blo 1190412 1191455 := bstep (se 1 (by rfl) ⟨893591, by rfl⟩ : syracuseStep 1191455 = 1787183) B1787183
theorem B7638623 : Blo 1190412 7638623 := bstep (se 1 (by rfl) ⟨5728967, by rfl⟩ : syracuseStep 7638623 = 11457935) B11457935
theorem B2010791 : Blo 1190412 2010791 := bstep (se 1 (by rfl) ⟨1508093, by rfl⟩ : syracuseStep 2010791 = 3016187) B3016187
theorem B1191591 : Blo 1190412 1191591 := bstep (se 1 (by rfl) ⟨893693, by rfl⟩ : syracuseStep 1191591 = 1787387) B1787387
theorem B4525739 : Blo 1190412 4525739 := bstep (se 1 (by rfl) ⟨3394304, by rfl⟩ : syracuseStep 4525739 = 6788609) B6788609
theorem B1191615 : Blo 1190412 1191615 := bstep (se 1 (by rfl) ⟨893711, by rfl⟩ : syracuseStep 1191615 = 1787423) B1787423
theorem B1191711 : Blo 1190412 1191711 := bstep (se 1 (by rfl) ⟨893783, by rfl⟩ : syracuseStep 1191711 = 1787567) B1787567
theorem B1191791 : Blo 1190412 1191791 := bstep (se 1 (by rfl) ⟨893843, by rfl⟩ : syracuseStep 1191791 = 1787687) B1787687
theorem B12881909 : Blo 1190412 12881909 := bstep (se 5 (by rfl) ⟨603839, by rfl⟩ : syracuseStep 12881909 = 1207679) B1207679
theorem B2011243 : Blo 1190412 2011243 := bstep (se 1 (by rfl) ⟨1508432, by rfl⟩ : syracuseStep 2011243 = 3016865) B3016865
theorem B181080197 : Blo 1190412 181080197 := bstep (se 4 (by rfl) ⟨16976268, by rfl⟩ : syracuseStep 181080197 = 33952537) B33952537
theorem B1192159 : Blo 1190412 1192159 := bstep (se 1 (by rfl) ⟨894119, by rfl⟩ : syracuseStep 1192159 = 1788239) B1788239
theorem B1192191 : Blo 1190412 1192191 := bstep (se 1 (by rfl) ⟨894143, by rfl⟩ : syracuseStep 1192191 = 1788287) B1788287
theorem B2543891 : Blo 1190412 2543891 := bstep (se 1 (by rfl) ⟨1907918, by rfl⟩ : syracuseStep 2543891 = 3815837) B3815837
theorem B6033689 : Blo 1190412 6033689 := bstep (se 2 (by rfl) ⟨2262633, by rfl⟩ : syracuseStep 6033689 = 4525267) B4525267
theorem B1192219 : Blo 1190412 1192219 := bstep (se 1 (by rfl) ⟨894164, by rfl⟩ : syracuseStep 1192219 = 1788329) B1788329
theorem B6788083 : Blo 1190412 6788083 := bstep (se 1 (by rfl) ⟨5091062, by rfl⟩ : syracuseStep 6788083 = 10182125) B10182125
theorem B49599611 : Blo 1190412 49599611 := bstep (se 1 (by rfl) ⟨37199708, by rfl⟩ : syracuseStep 49599611 = 74399417) B74399417
theorem B3814607 : Blo 1190412 3814607 := bstep (se 1 (by rfl) ⟨2860955, by rfl⟩ : syracuseStep 3814607 = 5721911) B5721911
theorem B10171601 : Blo 1190412 10171601 := bstep (se 2 (by rfl) ⟨3814350, by rfl⟩ : syracuseStep 10171601 = 7628701) B7628701
theorem B7632083 : Blo 1190412 7632083 := bstep (se 1 (by rfl) ⟨5724062, by rfl⟩ : syracuseStep 7632083 = 11448125) B11448125
theorem B11162927 : Blo 1190412 11162927 := bstep (se 1 (by rfl) ⟨8372195, by rfl⟩ : syracuseStep 11162927 = 16744391) B16744391
theorem B7632265 : Blo 1190412 7632265 := bstep (se 2 (by rfl) ⟨2862099, by rfl⟩ : syracuseStep 7632265 = 5724199) B5724199
theorem B73381301 : Blo 1190412 73381301 := bstep (se 5 (by rfl) ⟨3439748, by rfl⟩ : syracuseStep 73381301 = 6879497) B6879497
theorem B1341031 : Blo 1190412 1341031 := bstep (se 1 (by rfl) ⟨1005773, by rfl⟩ : syracuseStep 1341031 = 2011547) B2011547
theorem B9172783 : Blo 1190412 9172783 := bstep (se 1 (by rfl) ⟨6879587, by rfl⟩ : syracuseStep 9172783 = 13759175) B13759175
theorem B6199163 : Blo 1190412 6199163 := bstep (se 1 (by rfl) ⟨4649372, by rfl⟩ : syracuseStep 6199163 = 9298745) B9298745
theorem B13563773 : Blo 1190412 13563773 := bstep (se 3 (by rfl) ⟨2543207, by rfl⟩ : syracuseStep 13563773 = 5086415) B5086415
theorem B5724047 : Blo 1190412 5724047 := bstep (se 1 (by rfl) ⟨4293035, by rfl⟩ : syracuseStep 5724047 = 8586071) B8586071
theorem B23197751 : Blo 1190412 23197751 := bstep (se 1 (by rfl) ⟨17398313, by rfl⟩ : syracuseStep 23197751 = 34796627) B34796627
theorem B209025157 : Blo 1190412 209025157 := bstep (se 4 (by rfl) ⟨19596108, by rfl⟩ : syracuseStep 209025157 = 39192217) B39192217
theorem B6035795 : Blo 1190412 6035795 := bstep (se 1 (by rfl) ⟨4526846, by rfl⟩ : syracuseStep 6035795 = 9053693) B9053693
theorem B1907047 : Blo 1190412 1907047 := bstep (se 1 (by rfl) ⟨1430285, by rfl⟩ : syracuseStep 1907047 = 2860571) B2860571
theorem B6027695 : Blo 1190412 6027695 := bstep (se 1 (by rfl) ⟨4520771, by rfl⟩ : syracuseStep 6027695 = 9041543) B9041543
theorem B3217961 : Blo 1190412 3217961 := bstep (se 2 (by rfl) ⟨1206735, by rfl⟩ : syracuseStep 3217961 = 2413471) B2413471
theorem B5085767 : Blo 1190412 5085767 := bstep (se 1 (by rfl) ⟨3814325, by rfl⟩ : syracuseStep 5085767 = 7628651) B7628651
theorem B11598481 : Blo 1190412 11598481 := bstep (se 2 (by rfl) ⟨4349430, by rfl⟩ : syracuseStep 11598481 = 8698861) B8698861
theorem B6789815 : Blo 1190412 6789815 := bstep (se 1 (by rfl) ⟨5092361, by rfl⟩ : syracuseStep 6789815 = 10184723) B10184723
theorem B5725217 : Blo 1190412 5725217 := bstep (se 2 (by rfl) ⟨2146956, by rfl⟩ : syracuseStep 5725217 = 4293913) B4293913
theorem B15269087 : Blo 1190412 15269087 := bstep (se 1 (by rfl) ⟨11451815, by rfl⟩ : syracuseStep 15269087 = 22903631) B22903631
theorem B24452387 : Blo 1190412 24452387 := bstep (se 1 (by rfl) ⟨18339290, by rfl⟩ : syracuseStep 24452387 = 36678581) B36678581
theorem B7241015 : Blo 1190412 7241015 := bstep (se 1 (by rfl) ⟨5430761, by rfl⟩ : syracuseStep 7241015 = 10861523) B10861523
theorem B2260379 : Blo 1190412 2260379 := bstep (se 1 (by rfl) ⟨1695284, by rfl⟩ : syracuseStep 2260379 = 3390569) B3390569
theorem B20905775 : Blo 1190412 20905775 := bstep (se 1 (by rfl) ⟨15679331, by rfl⟩ : syracuseStep 20905775 = 31358663) B31358663
theorem B24469295 : Blo 1190412 24469295 := bstep (se 1 (by rfl) ⟨18351971, by rfl⟩ : syracuseStep 24469295 = 36703943) B36703943
theorem B6790999 : Blo 1190412 6790999 := bstep (se 1 (by rfl) ⟨5093249, by rfl⟩ : syracuseStep 6790999 = 10186499) B10186499
theorem B19332989 : Blo 1190412 19332989 := bstep (se 3 (by rfl) ⟨3624935, by rfl⟩ : syracuseStep 19332989 = 7249871) B7249871
theorem B4521865 : Blo 1190412 4521865 := bstep (se 2 (by rfl) ⟨1695699, by rfl⟩ : syracuseStep 4521865 = 3391399) B3391399
theorem B3014567 : Blo 1190412 3014567 := bstep (se 1 (by rfl) ⟨2260925, by rfl⟩ : syracuseStep 3014567 = 4521851) B4521851
theorem B17170343 : Blo 1190412 17170343 := bstep (se 1 (by rfl) ⟨12877757, by rfl⟩ : syracuseStep 17170343 = 25755515) B25755515
theorem B1785833 : Blo 1190412 1785833 := bstep (se 2 (by rfl) ⟨669687, by rfl⟩ : syracuseStep 1785833 = 1339375) B1339375
theorem B2261047 : Blo 1190412 2261047 := bstep (se 1 (by rfl) ⟨1695785, by rfl⟩ : syracuseStep 2261047 = 3391571) B3391571
theorem B278700209 : Blo 1190412 278700209 := bstep (se 2 (by rfl) ⟨104512578, by rfl⟩ : syracuseStep 278700209 = 209025157) B209025157
theorem B1507511 : Blo 1190412 1507511 := bstep (se 1 (by rfl) ⟨1130633, by rfl⟩ : syracuseStep 1507511 = 2261267) B2261267
theorem B4022459 : Blo 1190412 4022459 := bstep (se 1 (by rfl) ⟨3016844, by rfl⟩ : syracuseStep 4022459 = 6033689) B6033689
theorem B6783209 : Blo 1190412 6783209 := bstep (se 2 (by rfl) ⟨2543703, by rfl⟩ : syracuseStep 6783209 = 5087407) B5087407
theorem B4522337 : Blo 1190412 4522337 := bstep (se 2 (by rfl) ⟨1695876, by rfl⟩ : syracuseStep 4522337 = 3391753) B3391753
theorem B8700263 : Blo 1190412 8700263 := bstep (se 1 (by rfl) ⟨6525197, by rfl⟩ : syracuseStep 8700263 = 13050395) B13050395
theorem B2261495 : Blo 1190412 2261495 := bstep (se 1 (by rfl) ⟨1696121, by rfl⟩ : syracuseStep 2261495 = 3392243) B3392243
theorem B2679353 : Blo 1190412 2679353 := bstep (se 2 (by rfl) ⟨1004757, by rfl⟩ : syracuseStep 2679353 = 2009515) B2009515
theorem B6783709 : Blo 1190412 6783709 := bstep (se 3 (by rfl) ⟨1271945, by rfl⟩ : syracuseStep 6783709 = 2543891) B2543891
theorem B61858565 : Blo 1190412 61858565 := bstep (se 4 (by rfl) ⟨5799240, by rfl⟩ : syracuseStep 61858565 = 11598481) B11598481
theorem B19309373 : Blo 1190412 19309373 := bstep (se 3 (by rfl) ⟨3620507, by rfl⟩ : syracuseStep 19309373 = 7241015) B7241015
theorem B3015863 : Blo 1190412 3015863 := bstep (se 1 (by rfl) ⟨2261897, by rfl⟩ : syracuseStep 3015863 = 4523795) B4523795
theorem B2680073 : Blo 1190412 2680073 := bstep (se 2 (by rfl) ⟨1005027, by rfl⟩ : syracuseStep 2680073 = 2010055) B2010055
theorem B2262505 : Blo 1190412 2262505 := bstep (se 2 (by rfl) ⟨848439, by rfl⟩ : syracuseStep 2262505 = 1696879) B1696879
theorem B4023863 : Blo 1190412 4023863 := bstep (se 1 (by rfl) ⟨3017897, by rfl⟩ : syracuseStep 4023863 = 6035795) B6035795
theorem B2147995 : Blo 1190412 2147995 := bstep (se 1 (by rfl) ⟨1610996, by rfl⟩ : syracuseStep 2147995 = 3221993) B3221993
theorem B1697545 : Blo 1190412 1697545 := bstep (se 2 (by rfl) ⟨636579, by rfl⟩ : syracuseStep 1697545 = 1273159) B1273159
theorem B10176353 : Blo 1190412 10176353 := bstep (se 2 (by rfl) ⟨3816132, by rfl⟩ : syracuseStep 10176353 = 7632265) B7632265
theorem B65251453 : Blo 1190412 65251453 := bstep (se 3 (by rfl) ⟨12234647, by rfl⟩ : syracuseStep 65251453 = 24469295) B24469295
theorem B1788041 : Blo 1190412 1788041 := bstep (se 2 (by rfl) ⟨670515, by rfl⟩ : syracuseStep 1788041 = 1341031) B1341031
theorem B3017159 : Blo 1190412 3017159 := bstep (se 1 (by rfl) ⟨2262869, by rfl⟩ : syracuseStep 3017159 = 4525739) B4525739
theorem B9054665 : Blo 1190412 9054665 := bstep (se 2 (by rfl) ⟨3395499, by rfl⟩ : syracuseStep 9054665 = 6790999) B6790999
theorem B13937183 : Blo 1190412 13937183 := bstep (se 1 (by rfl) ⟨10452887, by rfl⟩ : syracuseStep 13937183 = 20905775) B20905775
theorem B12888659 : Blo 1190412 12888659 := bstep (se 1 (by rfl) ⟨9666494, by rfl⟩ : syracuseStep 12888659 = 19332989) B19332989
theorem B2009711 : Blo 1190412 2009711 := bstep (se 1 (by rfl) ⟨1507283, by rfl⟩ : syracuseStep 2009711 = 3014567) B3014567
theorem B11446895 : Blo 1190412 11446895 := bstep (se 1 (by rfl) ⟨8585171, by rfl⟩ : syracuseStep 11446895 = 17170343) B17170343
theorem B1190555 : Blo 1190412 1190555 := bstep (se 1 (by rfl) ⟨892916, by rfl⟩ : syracuseStep 1190555 = 1785833) B1785833
theorem B8587939 : Blo 1190412 8587939 := bstep (se 1 (by rfl) ⟨6440954, by rfl⟩ : syracuseStep 8587939 = 12881909) B12881909
theorem B120720131 : Blo 1190412 120720131 := bstep (se 1 (by rfl) ⟨90540098, by rfl⟩ : syracuseStep 120720131 = 181080197) B181080197
theorem B1190683 : Blo 1190412 1190683 := bstep (se 1 (by rfl) ⟨893012, by rfl⟩ : syracuseStep 1190683 = 1786025) B1786025
theorem B2681657 : Blo 1190412 2681657 := bstep (se 2 (by rfl) ⟨1005621, by rfl⟩ : syracuseStep 2681657 = 2011243) B2011243
theorem B1190895 : Blo 1190412 1190895 := bstep (se 1 (by rfl) ⟨893171, by rfl⟩ : syracuseStep 1190895 = 1786343) B1786343
theorem B6032393 : Blo 1190412 6032393 := bstep (se 2 (by rfl) ⟨2262147, by rfl⟩ : syracuseStep 6032393 = 4524295) B4524295
theorem B1191079 : Blo 1190412 1191079 := bstep (se 1 (by rfl) ⟨893309, by rfl⟩ : syracuseStep 1191079 = 1786619) B1786619
theorem B20352221 : Blo 1190412 20352221 := bstep (se 3 (by rfl) ⟨3816041, by rfl⟩ : syracuseStep 20352221 = 7632083) B7632083
theorem B33066407 : Blo 1190412 33066407 := bstep (se 1 (by rfl) ⟨24799805, by rfl⟩ : syracuseStep 33066407 = 49599611) B49599611
theorem B1191375 : Blo 1190412 1191375 := bstep (se 1 (by rfl) ⟨893531, by rfl⟩ : syracuseStep 1191375 = 1787063) B1787063
theorem B2543071 : Blo 1190412 2543071 := bstep (se 1 (by rfl) ⟨1907303, by rfl⟩ : syracuseStep 2543071 = 3814607) B3814607
theorem B7441951 : Blo 1190412 7441951 := bstep (se 1 (by rfl) ⟨5581463, by rfl⟩ : syracuseStep 7441951 = 11162927) B11162927
theorem B1191471 : Blo 1190412 1191471 := bstep (se 1 (by rfl) ⟨893603, by rfl⟩ : syracuseStep 1191471 = 1787207) B1787207
theorem B1191535 : Blo 1190412 1191535 := bstep (se 1 (by rfl) ⟨893651, by rfl⟩ : syracuseStep 1191535 = 1787303) B1787303
theorem B1191655 : Blo 1190412 1191655 := bstep (se 1 (by rfl) ⟨893741, by rfl⟩ : syracuseStep 1191655 = 1787483) B1787483
theorem B4132775 : Blo 1190412 4132775 := bstep (se 1 (by rfl) ⟨3099581, by rfl⟩ : syracuseStep 4132775 = 6199163) B6199163
theorem B2682791 : Blo 1190412 2682791 := bstep (se 1 (by rfl) ⟨2012093, by rfl⟩ : syracuseStep 2682791 = 4024187) B4024187
theorem B1191967 : Blo 1190412 1191967 := bstep (se 1 (by rfl) ⟨893975, by rfl⟩ : syracuseStep 1191967 = 1787951) B1787951
theorem B1192143 : Blo 1190412 1192143 := bstep (se 1 (by rfl) ⟨894107, by rfl⟩ : syracuseStep 1192143 = 1788215) B1788215
theorem B4018463 : Blo 1190412 4018463 := bstep (se 1 (by rfl) ⟨3013847, by rfl⟩ : syracuseStep 4018463 = 6027695) B6027695
theorem B24785189 : Blo 1190412 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B1192263 : Blo 1190412 1192263 := bstep (se 1 (by rfl) ⟨894197, by rfl⟩ : syracuseStep 1192263 = 1788395) B1788395
theorem B4526543 : Blo 1190412 4526543 := bstep (se 1 (by rfl) ⟨3394907, by rfl⟩ : syracuseStep 4526543 = 6789815) B6789815
theorem B2011675 : Blo 1190412 2011675 := bstep (se 1 (by rfl) ⟨1508756, by rfl⟩ : syracuseStep 2011675 = 3017513) B3017513
theorem B10170917 : Blo 1190412 10170917 := bstep (se 4 (by rfl) ⟨953523, by rfl⟩ : syracuseStep 10170917 = 1907047) B1907047
theorem B9040571 : Blo 1190412 9040571 := bstep (se 1 (by rfl) ⟨6780428, by rfl⟩ : syracuseStep 9040571 = 13560857) B13560857
theorem B10179391 : Blo 1190412 10179391 := bstep (se 1 (by rfl) ⟨7634543, by rfl⟩ : syracuseStep 10179391 = 15269087) B15269087
theorem B15266627 : Blo 1190412 15266627 := bstep (se 1 (by rfl) ⟨11449970, by rfl⟩ : syracuseStep 15266627 = 22899941) B22899941
theorem B5092415 : Blo 1190412 5092415 := bstep (se 1 (by rfl) ⟨3819311, by rfl⟩ : syracuseStep 5092415 = 7638623) B7638623
theorem B1340527 : Blo 1190412 1340527 := bstep (se 1 (by rfl) ⟨1005395, by rfl⟩ : syracuseStep 1340527 = 2010791) B2010791
theorem B4019705 : Blo 1190412 4019705 := bstep (se 2 (by rfl) ⟨1507389, by rfl⟩ : syracuseStep 4019705 = 3014779) B3014779
theorem B4019867 : Blo 1190412 4019867 := bstep (se 1 (by rfl) ⟨3014900, by rfl⟩ : syracuseStep 4019867 = 6029801) B6029801
theorem B6781067 : Blo 1190412 6781067 := bstep (se 1 (by rfl) ⟨5085800, by rfl⟩ : syracuseStep 6781067 = 10171601) B10171601
theorem B48920867 : Blo 1190412 48920867 := bstep (se 1 (by rfl) ⟨36690650, by rfl⟩ : syracuseStep 48920867 = 73381301) B73381301
theorem B6789541 : Blo 1190412 6789541 := bstep (se 4 (by rfl) ⟨636519, by rfl⟩ : syracuseStep 6789541 = 1273039) B1273039
theorem B9042515 : Blo 1190412 9042515 := bstep (se 1 (by rfl) ⟨6781886, by rfl⟩ : syracuseStep 9042515 = 13563773) B13563773
theorem B3816031 : Blo 1190412 3816031 := bstep (se 1 (by rfl) ⟨2862023, by rfl⟩ : syracuseStep 3816031 = 5724047) B5724047
theorem B9050777 : Blo 1190412 9050777 := bstep (se 2 (by rfl) ⟨3394041, by rfl⟩ : syracuseStep 9050777 = 6788083) B6788083
theorem B15465167 : Blo 1190412 15465167 := bstep (se 1 (by rfl) ⟨11598875, by rfl⟩ : syracuseStep 15465167 = 23197751) B23197751
theorem B48921509 : Blo 1190412 48921509 := bstep (se 4 (by rfl) ⟨4586391, by rfl⟩ : syracuseStep 48921509 = 9172783) B9172783
theorem B2145307 : Blo 1190412 2145307 := bstep (se 1 (by rfl) ⟨1608980, by rfl⟩ : syracuseStep 2145307 = 3217961) B3217961
theorem B3390511 : Blo 1190412 3390511 := bstep (se 1 (by rfl) ⟨2542883, by rfl⟩ : syracuseStep 3390511 = 5085767) B5085767
theorem B2415935 : Blo 1190412 2415935 := bstep (se 1 (by rfl) ⟨1811951, by rfl⟩ : syracuseStep 2415935 = 3623903) B3623903
theorem B3816811 : Blo 1190412 3816811 := bstep (se 1 (by rfl) ⟨2862608, by rfl⟩ : syracuseStep 3816811 = 5725217) B5725217
theorem B4021757 : Blo 1190412 4021757 := bstep (se 3 (by rfl) ⟨754079, by rfl⟩ : syracuseStep 4021757 = 1508159) B1508159
theorem B16301591 : Blo 1190412 16301591 := bstep (se 1 (by rfl) ⟨12226193, by rfl⟩ : syracuseStep 16301591 = 24452387) B24452387
theorem B1506919 : Blo 1190412 1506919 := bstep (se 1 (by rfl) ⟨1130189, by rfl⟩ : syracuseStep 1506919 = 2260379) B2260379
theorem B1695335 : Blo 1190412 1695335 := bstep (se 1 (by rfl) ⟨1271501, by rfl⟩ : syracuseStep 1695335 = 2543003) B2543003
theorem B6029153 : Blo 1190412 6029153 := bstep (se 2 (by rfl) ⟨2260932, by rfl⟩ : syracuseStep 6029153 = 4521865) B4521865
theorem B3014729 : Blo 1190412 3014729 := bstep (se 2 (by rfl) ⟨1130523, by rfl⟩ : syracuseStep 3014729 = 2261047) B2261047
theorem B4522139 : Blo 1190412 4522139 := bstep (se 1 (by rfl) ⟨3391604, by rfl⟩ : syracuseStep 4522139 = 6783209) B6783209
theorem B2678975 : Blo 1190412 2678975 := bstep (se 1 (by rfl) ⟨2009231, by rfl⟩ : syracuseStep 2678975 = 4018463) B4018463
theorem B16523459 : Blo 1190412 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B3014891 : Blo 1190412 3014891 := bstep (se 1 (by rfl) ⟨2261168, by rfl⟩ : syracuseStep 3014891 = 4522337) B4522337
theorem B5800175 : Blo 1190412 5800175 := bstep (se 1 (by rfl) ⟨4350131, by rfl⟩ : syracuseStep 5800175 = 8700263) B8700263
theorem B1507663 : Blo 1190412 1507663 := bstep (se 1 (by rfl) ⟨1130747, by rfl⟩ : syracuseStep 1507663 = 2261495) B2261495
theorem B1786235 : Blo 1190412 1786235 := bstep (se 1 (by rfl) ⟨1339676, by rfl⟩ : syracuseStep 1786235 = 2679353) B2679353
theorem B41239043 : Blo 1190412 41239043 := bstep (se 1 (by rfl) ⟨30929282, by rfl⟩ : syracuseStep 41239043 = 61858565) B61858565
theorem B9052721 : Blo 1190412 9052721 := bstep (se 2 (by rfl) ⟨3394770, by rfl⟩ : syracuseStep 9052721 = 6789541) B6789541
theorem B5088041 : Blo 1190412 5088041 := bstep (se 2 (by rfl) ⟨1908015, by rfl⟩ : syracuseStep 5088041 = 3816031) B3816031
theorem B1786715 : Blo 1190412 1786715 := bstep (se 1 (by rfl) ⟨1340036, by rfl⟩ : syracuseStep 1786715 = 2680073) B2680073
theorem B9044945 : Blo 1190412 9044945 := bstep (se 2 (by rfl) ⟨3391854, by rfl⟩ : syracuseStep 9044945 = 6783709) B6783709
theorem B2679803 : Blo 1190412 2679803 := bstep (se 1 (by rfl) ⟨2009852, by rfl⟩ : syracuseStep 2679803 = 4019705) B4019705
theorem B2679911 : Blo 1190412 2679911 := bstep (se 1 (by rfl) ⟨2009933, by rfl⟩ : syracuseStep 2679911 = 4019867) B4019867
theorem B6784235 : Blo 1190412 6784235 := bstep (se 1 (by rfl) ⟨5088176, by rfl⟩ : syracuseStep 6784235 = 10176353) B10176353
theorem B2860409 : Blo 1190412 2860409 := bstep (se 2 (by rfl) ⟨1072653, by rfl⟩ : syracuseStep 2860409 = 2145307) B2145307
theorem B1787369 : Blo 1190412 1787369 := bstep (se 2 (by rfl) ⟨670263, by rfl⟩ : syracuseStep 1787369 = 1340527) B1340527
theorem B32613911 : Blo 1190412 32613911 := bstep (se 1 (by rfl) ⟨24460433, by rfl⟩ : syracuseStep 32613911 = 48920867) B48920867
theorem B9291455 : Blo 1190412 9291455 := bstep (se 1 (by rfl) ⟨6968591, by rfl⟩ : syracuseStep 9291455 = 13937183) B13937183
theorem B5089081 : Blo 1190412 5089081 := bstep (se 2 (by rfl) ⟨1908405, by rfl⟩ : syracuseStep 5089081 = 3816811) B3816811
theorem B80480087 : Blo 1190412 80480087 := bstep (se 1 (by rfl) ⟨60360065, by rfl⟩ : syracuseStep 80480087 = 120720131) B120720131
theorem B1787771 : Blo 1190412 1787771 := bstep (se 1 (by rfl) ⟨1340828, by rfl⟩ : syracuseStep 1787771 = 2681657) B2681657
theorem B32614339 : Blo 1190412 32614339 := bstep (se 1 (by rfl) ⟨24460754, by rfl⟩ : syracuseStep 32614339 = 48921509) B48921509
theorem B3016673 : Blo 1190412 3016673 := bstep (se 2 (by rfl) ⟨1131252, by rfl⟩ : syracuseStep 3016673 = 2262505) B2262505
theorem B9922601 : Blo 1190412 9922601 := bstep (se 2 (by rfl) ⟨3720975, by rfl⟩ : syracuseStep 9922601 = 7441951) B7441951
theorem B2009225 : Blo 1190412 2009225 := bstep (se 2 (by rfl) ⟨753459, by rfl⟩ : syracuseStep 2009225 = 1506919) B1506919
theorem B13568147 : Blo 1190412 13568147 := bstep (se 1 (by rfl) ⟨10176110, by rfl⟩ : syracuseStep 13568147 = 20352221) B20352221
theorem B2681171 : Blo 1190412 2681171 := bstep (se 1 (by rfl) ⟨2010878, by rfl⟩ : syracuseStep 2681171 = 4021757) B4021757
theorem B2263393 : Blo 1190412 2263393 := bstep (se 2 (by rfl) ⟨848772, by rfl⟩ : syracuseStep 2263393 = 1697545) B1697545
theorem B11020733 : Blo 1190412 11020733 := bstep (se 3 (by rfl) ⟨2066387, by rfl⟩ : syracuseStep 11020733 = 4132775) B4132775
theorem B1788527 : Blo 1190412 1788527 := bstep (se 1 (by rfl) ⟨1341395, by rfl⟩ : syracuseStep 1788527 = 2682791) B2682791
theorem B2681639 : Blo 1190412 2681639 := bstep (se 1 (by rfl) ⟨2011229, by rfl⟩ : syracuseStep 2681639 = 4022459) B4022459
theorem B87001937 : Blo 1190412 87001937 := bstep (se 2 (by rfl) ⟨32625726, by rfl⟩ : syracuseStep 87001937 = 65251453) B65251453
theorem B3017695 : Blo 1190412 3017695 := bstep (se 1 (by rfl) ⟨2263271, by rfl⟩ : syracuseStep 3017695 = 4526543) B4526543
theorem B12872915 : Blo 1190412 12872915 := bstep (se 1 (by rfl) ⟨9654686, by rfl⟩ : syracuseStep 12872915 = 19309373) B19309373
theorem B10177751 : Blo 1190412 10177751 := bstep (se 1 (by rfl) ⟨7633313, by rfl⟩ : syracuseStep 10177751 = 15266627) B15266627
theorem B2682233 : Blo 1190412 2682233 := bstep (se 2 (by rfl) ⟨1005837, by rfl⟩ : syracuseStep 2682233 = 2011675) B2011675
theorem B3394943 : Blo 1190412 3394943 := bstep (se 1 (by rfl) ⟨2546207, by rfl⟩ : syracuseStep 3394943 = 5092415) B5092415
theorem B2010575 : Blo 1190412 2010575 := bstep (se 1 (by rfl) ⟨1507931, by rfl⟩ : syracuseStep 2010575 = 3015863) B3015863
theorem B2682575 : Blo 1190412 2682575 := bstep (se 1 (by rfl) ⟨2011931, by rfl⟩ : syracuseStep 2682575 = 4023863) B4023863
theorem B1192027 : Blo 1190412 1192027 := bstep (se 1 (by rfl) ⟨894020, by rfl⟩ : syracuseStep 1192027 = 1788041) B1788041
theorem B2011439 : Blo 1190412 2011439 := bstep (se 1 (by rfl) ⟨1508579, by rfl⟩ : syracuseStep 2011439 = 3017159) B3017159
theorem B1339807 : Blo 1190412 1339807 := bstep (se 1 (by rfl) ⟨1004855, by rfl⟩ : syracuseStep 1339807 = 2009711) B2009711
theorem B7631263 : Blo 1190412 7631263 := bstep (se 1 (by rfl) ⟨5723447, by rfl⟩ : syracuseStep 7631263 = 11446895) B11446895
theorem B6033851 : Blo 1190412 6033851 := bstep (se 1 (by rfl) ⟨4525388, by rfl⟩ : syracuseStep 6033851 = 9050777) B9050777
theorem B10310111 : Blo 1190412 10310111 := bstep (se 1 (by rfl) ⟨7732583, by rfl⟩ : syracuseStep 10310111 = 15465167) B15465167
theorem B2863993 : Blo 1190412 2863993 := bstep (se 2 (by rfl) ⟨1073997, by rfl⟩ : syracuseStep 2863993 = 2147995) B2147995
theorem B1610623 : Blo 1190412 1610623 := bstep (se 1 (by rfl) ⟨1207967, by rfl⟩ : syracuseStep 1610623 = 2415935) B2415935
theorem B10867727 : Blo 1190412 10867727 := bstep (se 1 (by rfl) ⟨8150795, by rfl⟩ : syracuseStep 10867727 = 16301591) B16301591
theorem B4019435 : Blo 1190412 4019435 := bstep (se 1 (by rfl) ⟨3014576, by rfl⟩ : syracuseStep 4019435 = 6029153) B6029153
theorem B185800139 : Blo 1190412 185800139 := bstep (se 1 (by rfl) ⟨139350104, by rfl⟩ : syracuseStep 185800139 = 278700209) B278700209
theorem B6780611 : Blo 1190412 6780611 := bstep (se 1 (by rfl) ⟨5085458, by rfl⟩ : syracuseStep 6780611 = 10170917) B10170917
theorem B6027047 : Blo 1190412 6027047 := bstep (se 1 (by rfl) ⟨4520285, by rfl⟩ : syracuseStep 6027047 = 9040571) B9040571
theorem B4020029 : Blo 1190412 4020029 := bstep (se 3 (by rfl) ⟨753755, by rfl⟩ : syracuseStep 4020029 = 1507511) B1507511
theorem B11450585 : Blo 1190412 11450585 := bstep (se 2 (by rfl) ⟨4293969, by rfl⟩ : syracuseStep 11450585 = 8587939) B8587939
theorem B13572521 : Blo 1190412 13572521 := bstep (se 2 (by rfl) ⟨5089695, by rfl⟩ : syracuseStep 13572521 = 10179391) B10179391
theorem B88177085 : Blo 1190412 88177085 := bstep (se 3 (by rfl) ⟨16533203, by rfl⟩ : syracuseStep 88177085 = 33066407) B33066407
theorem B4520681 : Blo 1190412 4520681 := bstep (se 2 (by rfl) ⟨1695255, by rfl⟩ : syracuseStep 4520681 = 3390511) B3390511
theorem B4520711 : Blo 1190412 4520711 := bstep (se 1 (by rfl) ⟨3390533, by rfl⟩ : syracuseStep 4520711 = 6781067) B6781067
theorem B4520893 : Blo 1190412 4520893 := bstep (se 3 (by rfl) ⟨847667, by rfl⟩ : syracuseStep 4520893 = 1695335) B1695335
theorem B6036443 : Blo 1190412 6036443 := bstep (se 1 (by rfl) ⟨4527332, by rfl⟩ : syracuseStep 6036443 = 9054665) B9054665
theorem B6028343 : Blo 1190412 6028343 := bstep (se 1 (by rfl) ⟨4521257, by rfl⟩ : syracuseStep 6028343 = 9042515) B9042515
theorem B8592439 : Blo 1190412 8592439 := bstep (se 1 (by rfl) ⟨6444329, by rfl⟩ : syracuseStep 8592439 = 12888659) B12888659
theorem B3390761 : Blo 1190412 3390761 := bstep (se 2 (by rfl) ⟨1271535, by rfl⟩ : syracuseStep 3390761 = 2543071) B2543071
theorem B4021595 : Blo 1190412 4021595 := bstep (se 1 (by rfl) ⟨3016196, by rfl⟩ : syracuseStep 4021595 = 6032393) B6032393
theorem B3014759 : Blo 1190412 3014759 := bstep (se 1 (by rfl) ⟨2261069, by rfl⟩ : syracuseStep 3014759 = 4522139) B4522139
theorem B1785983 : Blo 1190412 1785983 := bstep (se 1 (by rfl) ⟨1339487, by rfl⟩ : syracuseStep 1785983 = 2678975) B2678975
theorem B3866783 : Blo 1190412 3866783 := bstep (se 1 (by rfl) ⟨2900087, by rfl⟩ : syracuseStep 3866783 = 5800175) B5800175
theorem B4022567 : Blo 1190412 4022567 := bstep (se 1 (by rfl) ⟨3016925, by rfl⟩ : syracuseStep 4022567 = 6033851) B6033851
theorem B6873407 : Blo 1190412 6873407 := bstep (se 1 (by rfl) ⟨5155055, by rfl⟩ : syracuseStep 6873407 = 10310111) B10310111
theorem B27492695 : Blo 1190412 27492695 := bstep (se 1 (by rfl) ⟨20619521, by rfl⟩ : syracuseStep 27492695 = 41239043) B41239043
theorem B3392027 : Blo 1190412 3392027 := bstep (se 1 (by rfl) ⟨2544020, by rfl⟩ : syracuseStep 3392027 = 5088041) B5088041
theorem B1786409 : Blo 1190412 1786409 := bstep (se 2 (by rfl) ⟨669903, by rfl⟩ : syracuseStep 1786409 = 1339807) B1339807
theorem B10175017 : Blo 1190412 10175017 := bstep (se 2 (by rfl) ⟨3815631, by rfl⟩ : syracuseStep 10175017 = 7631263) B7631263
theorem B6029963 : Blo 1190412 6029963 := bstep (se 1 (by rfl) ⟨4522472, by rfl⟩ : syracuseStep 6029963 = 9044945) B9044945
theorem B1786535 : Blo 1190412 1786535 := bstep (se 1 (by rfl) ⟨1339901, by rfl⟩ : syracuseStep 1786535 = 2679803) B2679803
theorem B1786607 : Blo 1190412 1786607 := bstep (se 1 (by rfl) ⟨1339955, by rfl⟩ : syracuseStep 1786607 = 2679911) B2679911
theorem B2679623 : Blo 1190412 2679623 := bstep (se 1 (by rfl) ⟨2009717, by rfl⟩ : syracuseStep 2679623 = 4019435) B4019435
theorem B4522823 : Blo 1190412 4522823 := bstep (se 1 (by rfl) ⟨3392117, by rfl⟩ : syracuseStep 4522823 = 6784235) B6784235
theorem B21742607 : Blo 1190412 21742607 := bstep (se 1 (by rfl) ⟨16306955, by rfl⟩ : syracuseStep 21742607 = 32613911) B32613911
theorem B6194303 : Blo 1190412 6194303 := bstep (se 1 (by rfl) ⟨4645727, by rfl⟩ : syracuseStep 6194303 = 9291455) B9291455
theorem B3818657 : Blo 1190412 3818657 := bstep (se 2 (by rfl) ⟨1431996, by rfl⟩ : syracuseStep 3818657 = 2863993) B2863993
theorem B2680019 : Blo 1190412 2680019 := bstep (se 1 (by rfl) ⟨2010014, by rfl⟩ : syracuseStep 2680019 = 4020029) B4020029
theorem B4023593 : Blo 1190412 4023593 := bstep (se 2 (by rfl) ⟨1508847, by rfl⟩ : syracuseStep 4023593 = 3017695) B3017695
theorem B9045431 : Blo 1190412 9045431 := bstep (se 1 (by rfl) ⟨6784073, by rfl⟩ : syracuseStep 9045431 = 13568147) B13568147
theorem B1787447 : Blo 1190412 1787447 := bstep (se 1 (by rfl) ⟨1340585, by rfl⟩ : syracuseStep 1787447 = 2681171) B2681171
theorem B1787759 : Blo 1190412 1787759 := bstep (se 1 (by rfl) ⟨1340819, by rfl⟩ : syracuseStep 1787759 = 2681639) B2681639
theorem B58001291 : Blo 1190412 58001291 := bstep (se 1 (by rfl) ⟨43500968, by rfl⟩ : syracuseStep 58001291 = 87001937) B87001937
theorem B4024295 : Blo 1190412 4024295 := bstep (se 1 (by rfl) ⟨3018221, by rfl⟩ : syracuseStep 4024295 = 6036443) B6036443
theorem B6785167 : Blo 1190412 6785167 := bstep (se 1 (by rfl) ⟨5088875, by rfl⟩ : syracuseStep 6785167 = 10177751) B10177751
theorem B2681063 : Blo 1190412 2681063 := bstep (se 1 (by rfl) ⟨2010797, by rfl⟩ : syracuseStep 2681063 = 4021595) B4021595
theorem B1788155 : Blo 1190412 1788155 := bstep (se 1 (by rfl) ⟨1341116, by rfl⟩ : syracuseStep 1788155 = 2682233) B2682233
theorem B2263295 : Blo 1190412 2263295 := bstep (se 1 (by rfl) ⟨1697471, by rfl⟩ : syracuseStep 2263295 = 3394943) B3394943
theorem B6785441 : Blo 1190412 6785441 := bstep (se 2 (by rfl) ⟨2544540, by rfl⟩ : syracuseStep 6785441 = 5089081) B5089081
theorem B1788383 : Blo 1190412 1788383 := bstep (se 1 (by rfl) ⟨1341287, by rfl⟩ : syracuseStep 1788383 = 2682575) B2682575
theorem B43485785 : Blo 1190412 43485785 := bstep (se 2 (by rfl) ⟨16307169, by rfl⟩ : syracuseStep 43485785 = 32614339) B32614339
theorem B2009819 : Blo 1190412 2009819 := bstep (se 1 (by rfl) ⟨1507364, by rfl⟩ : syracuseStep 2009819 = 3014729) B3014729
theorem B2009927 : Blo 1190412 2009927 := bstep (se 1 (by rfl) ⟨1507445, by rfl⟩ : syracuseStep 2009927 = 3014891) B3014891
theorem B1190823 : Blo 1190412 1190823 := bstep (se 1 (by rfl) ⟨893117, by rfl⟩ : syracuseStep 1190823 = 1786235) B1786235
theorem B2010217 : Blo 1190412 2010217 := bstep (se 2 (by rfl) ⟨753831, by rfl⟩ : syracuseStep 2010217 = 1507663) B1507663
theorem B3017857 : Blo 1190412 3017857 := bstep (se 2 (by rfl) ⟨1131696, by rfl⟩ : syracuseStep 3017857 = 2263393) B2263393
theorem B1191143 : Blo 1190412 1191143 := bstep (se 1 (by rfl) ⟨893357, by rfl⟩ : syracuseStep 1191143 = 1786715) B1786715
theorem B30534893 : Blo 1190412 30534893 := bstep (se 3 (by rfl) ⟨5725292, by rfl⟩ : syracuseStep 30534893 = 11450585) B11450585
theorem B123866759 : Blo 1190412 123866759 := bstep (se 1 (by rfl) ⟨92900069, by rfl⟩ : syracuseStep 123866759 = 185800139) B185800139
theorem B1191579 : Blo 1190412 1191579 := bstep (se 1 (by rfl) ⟨893684, by rfl⟩ : syracuseStep 1191579 = 1787369) B1787369
theorem B4018031 : Blo 1190412 4018031 := bstep (se 1 (by rfl) ⟨3013523, by rfl⟩ : syracuseStep 4018031 = 6027047) B6027047
theorem B53653391 : Blo 1190412 53653391 := bstep (se 1 (by rfl) ⟨40240043, by rfl⟩ : syracuseStep 53653391 = 80480087) B80480087
theorem B1191847 : Blo 1190412 1191847 := bstep (se 1 (by rfl) ⟨893885, by rfl⟩ : syracuseStep 1191847 = 1787771) B1787771
theorem B2011115 : Blo 1190412 2011115 := bstep (se 1 (by rfl) ⟨1508336, by rfl⟩ : syracuseStep 2011115 = 3016673) B3016673
theorem B6615067 : Blo 1190412 6615067 := bstep (se 1 (by rfl) ⟨4961300, by rfl⟩ : syracuseStep 6615067 = 9922601) B9922601
theorem B11456585 : Blo 1190412 11456585 := bstep (se 2 (by rfl) ⟨4296219, by rfl⟩ : syracuseStep 11456585 = 8592439) B8592439
theorem B1339483 : Blo 1190412 1339483 := bstep (se 1 (by rfl) ⟨1004612, by rfl⟩ : syracuseStep 1339483 = 2009225) B2009225
theorem B9048347 : Blo 1190412 9048347 := bstep (se 1 (by rfl) ⟨6786260, by rfl⟩ : syracuseStep 9048347 = 13572521) B13572521
theorem B1192351 : Blo 1190412 1192351 := bstep (se 1 (by rfl) ⟨894263, by rfl⟩ : syracuseStep 1192351 = 1788527) B1788527
theorem B8589989 : Blo 1190412 8589989 := bstep (se 4 (by rfl) ⟨805311, by rfl⟩ : syracuseStep 8589989 = 1610623) B1610623
theorem B4018895 : Blo 1190412 4018895 := bstep (se 1 (by rfl) ⟨3014171, by rfl⟩ : syracuseStep 4018895 = 6028343) B6028343
theorem B8581943 : Blo 1190412 8581943 := bstep (se 1 (by rfl) ⟨6436457, by rfl⟩ : syracuseStep 8581943 = 12872915) B12872915
theorem B1340383 : Blo 1190412 1340383 := bstep (se 1 (by rfl) ⟨1005287, by rfl⟩ : syracuseStep 1340383 = 2010575) B2010575
theorem B28980605 : Blo 1190412 28980605 := bstep (se 3 (by rfl) ⟨5433863, by rfl⟩ : syracuseStep 28980605 = 10867727) B10867727
theorem B11015639 : Blo 1190412 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B1340959 : Blo 1190412 1340959 := bstep (se 1 (by rfl) ⟨1005719, by rfl⟩ : syracuseStep 1340959 = 2011439) B2011439
theorem B6035147 : Blo 1190412 6035147 := bstep (se 1 (by rfl) ⟨4526360, by rfl⟩ : syracuseStep 6035147 = 9052721) B9052721
theorem B9042029 : Blo 1190412 9042029 := bstep (se 3 (by rfl) ⟨1695380, by rfl⟩ : syracuseStep 9042029 = 3390761) B3390761
theorem B1906939 : Blo 1190412 1906939 := bstep (se 1 (by rfl) ⟨1430204, by rfl⟩ : syracuseStep 1906939 = 2860409) B2860409
theorem B4520407 : Blo 1190412 4520407 := bstep (se 1 (by rfl) ⟨3390305, by rfl⟩ : syracuseStep 4520407 = 6780611) B6780611
theorem B6027857 : Blo 1190412 6027857 := bstep (se 2 (by rfl) ⟨2260446, by rfl⟩ : syracuseStep 6027857 = 4520893) B4520893
theorem B7347155 : Blo 1190412 7347155 := bstep (se 1 (by rfl) ⟨5510366, by rfl⟩ : syracuseStep 7347155 = 11020733) B11020733
theorem B58784723 : Blo 1190412 58784723 := bstep (se 1 (by rfl) ⟨44088542, by rfl⟩ : syracuseStep 58784723 = 88177085) B88177085
theorem B3013787 : Blo 1190412 3013787 := bstep (se 1 (by rfl) ⟨2260340, by rfl⟩ : syracuseStep 3013787 = 4520681) B4520681
theorem B3013807 : Blo 1190412 3013807 := bstep (se 1 (by rfl) ⟨2260355, by rfl⟩ : syracuseStep 3013807 = 4520711) B4520711
theorem B1785977 : Blo 1190412 1785977 := bstep (se 2 (by rfl) ⟨669741, by rfl⟩ : syracuseStep 1785977 = 1339483) B1339483
theorem B2261351 : Blo 1190412 2261351 := bstep (se 1 (by rfl) ⟨1696013, by rfl⟩ : syracuseStep 2261351 = 3392027) B3392027
theorem B2679263 : Blo 1190412 2679263 := bstep (se 1 (by rfl) ⟨2009447, by rfl⟩ : syracuseStep 2679263 = 4018895) B4018895
theorem B1786415 : Blo 1190412 1786415 := bstep (se 1 (by rfl) ⟨1339811, by rfl⟩ : syracuseStep 1786415 = 2679623) B2679623
theorem B3015215 : Blo 1190412 3015215 := bstep (se 1 (by rfl) ⟨2261411, by rfl⟩ : syracuseStep 3015215 = 4522823) B4522823
theorem B13566689 : Blo 1190412 13566689 := bstep (se 2 (by rfl) ⟨5087508, by rfl⟩ : syracuseStep 13566689 = 10175017) B10175017
theorem B4129535 : Blo 1190412 4129535 := bstep (se 1 (by rfl) ⟨3097151, by rfl⟩ : syracuseStep 4129535 = 6194303) B6194303
theorem B1786679 : Blo 1190412 1786679 := bstep (se 1 (by rfl) ⟨1340009, by rfl⟩ : syracuseStep 1786679 = 2680019) B2680019
theorem B6030287 : Blo 1190412 6030287 := bstep (se 1 (by rfl) ⟨4522715, by rfl⟩ : syracuseStep 6030287 = 9045431) B9045431
theorem B4023431 : Blo 1190412 4023431 := bstep (se 1 (by rfl) ⟨3017573, by rfl⟩ : syracuseStep 4023431 = 6035147) B6035147
theorem B38667527 : Blo 1190412 38667527 := bstep (se 1 (by rfl) ⟨29000645, by rfl⟩ : syracuseStep 38667527 = 58001291) B58001291
theorem B1787177 : Blo 1190412 1787177 := bstep (se 2 (by rfl) ⟨670191, by rfl⟩ : syracuseStep 1787177 = 1340383) B1340383
theorem B2680289 : Blo 1190412 2680289 := bstep (se 2 (by rfl) ⟨1005108, by rfl⟩ : syracuseStep 2680289 = 2010217) B2010217
theorem B1787375 : Blo 1190412 1787375 := bstep (se 1 (by rfl) ⟨1340531, by rfl⟩ : syracuseStep 1787375 = 2681063) B2681063
theorem B1508863 : Blo 1190412 1508863 := bstep (se 1 (by rfl) ⟨1131647, by rfl⟩ : syracuseStep 1508863 = 2263295) B2263295
theorem B4023809 : Blo 1190412 4023809 := bstep (se 2 (by rfl) ⟨1508928, by rfl⟩ : syracuseStep 4023809 = 3017857) B3017857
theorem B4523627 : Blo 1190412 4523627 := bstep (se 1 (by rfl) ⟨3392720, by rfl⟩ : syracuseStep 4523627 = 6785441) B6785441
theorem B22906637 : Blo 1190412 22906637 := bstep (se 3 (by rfl) ⟨4294994, by rfl⟩ : syracuseStep 22906637 = 8589989) B8589989
theorem B1787945 : Blo 1190412 1787945 := bstep (se 2 (by rfl) ⟨670479, by rfl⟩ : syracuseStep 1787945 = 1340959) B1340959
theorem B2009191 : Blo 1190412 2009191 := bstep (se 1 (by rfl) ⟨1506893, by rfl⟩ : syracuseStep 2009191 = 3013787) B3013787
theorem B82577839 : Blo 1190412 82577839 := bstep (se 1 (by rfl) ⟨61933379, by rfl⟩ : syracuseStep 82577839 = 123866759) B123866759
theorem B35768927 : Blo 1190412 35768927 := bstep (se 1 (by rfl) ⟨26826695, by rfl⟩ : syracuseStep 35768927 = 53653391) B53653391
theorem B7637723 : Blo 1190412 7637723 := bstep (se 1 (by rfl) ⟨5728292, by rfl⟩ : syracuseStep 7637723 = 11456585) B11456585
theorem B2009839 : Blo 1190412 2009839 := bstep (se 1 (by rfl) ⟨1507379, by rfl⟩ : syracuseStep 2009839 = 3014759) B3014759
theorem B1190655 : Blo 1190412 1190655 := bstep (se 1 (by rfl) ⟨892991, by rfl⟩ : syracuseStep 1190655 = 1785983) B1785983
theorem B6032231 : Blo 1190412 6032231 := bstep (se 1 (by rfl) ⟨4524173, by rfl⟩ : syracuseStep 6032231 = 9048347) B9048347
theorem B9046889 : Blo 1190412 9046889 := bstep (se 2 (by rfl) ⟨3392583, by rfl⟩ : syracuseStep 9046889 = 6785167) B6785167
theorem B2681711 : Blo 1190412 2681711 := bstep (se 1 (by rfl) ⟨2011283, by rfl⟩ : syracuseStep 2681711 = 4022567) B4022567
theorem B4582271 : Blo 1190412 4582271 := bstep (se 1 (by rfl) ⟨3436703, by rfl⟩ : syracuseStep 4582271 = 6873407) B6873407
theorem B18328463 : Blo 1190412 18328463 := bstep (se 1 (by rfl) ⟨13746347, by rfl⟩ : syracuseStep 18328463 = 27492695) B27492695
theorem B2542585 : Blo 1190412 2542585 := bstep (se 2 (by rfl) ⟨953469, by rfl⟩ : syracuseStep 2542585 = 1906939) B1906939
theorem B1190939 : Blo 1190412 1190939 := bstep (se 1 (by rfl) ⟨893204, by rfl⟩ : syracuseStep 1190939 = 1786409) B1786409
theorem B1191023 : Blo 1190412 1191023 := bstep (se 1 (by rfl) ⟨893267, by rfl⟩ : syracuseStep 1191023 = 1786535) B1786535
theorem B1191071 : Blo 1190412 1191071 := bstep (se 1 (by rfl) ⟨893303, by rfl⟩ : syracuseStep 1191071 = 1786607) B1786607
theorem B5721295 : Blo 1190412 5721295 := bstep (se 1 (by rfl) ⟨4290971, by rfl⟩ : syracuseStep 5721295 = 8581943) B8581943
theorem B14495071 : Blo 1190412 14495071 := bstep (se 1 (by rfl) ⟨10871303, by rfl⟩ : syracuseStep 14495071 = 21742607) B21742607
theorem B2682395 : Blo 1190412 2682395 := bstep (se 1 (by rfl) ⟨2011796, by rfl⟩ : syracuseStep 2682395 = 4023593) B4023593
theorem B19320403 : Blo 1190412 19320403 := bstep (se 1 (by rfl) ⟨14490302, by rfl⟩ : syracuseStep 19320403 = 28980605) B28980605
theorem B7343759 : Blo 1190412 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B1191631 : Blo 1190412 1191631 := bstep (se 1 (by rfl) ⟨893723, by rfl⟩ : syracuseStep 1191631 = 1787447) B1787447
theorem B1191839 : Blo 1190412 1191839 := bstep (se 1 (by rfl) ⟨893879, by rfl⟩ : syracuseStep 1191839 = 1787759) B1787759
theorem B2682863 : Blo 1190412 2682863 := bstep (se 1 (by rfl) ⟨2012147, by rfl⟩ : syracuseStep 2682863 = 4024295) B4024295
theorem B1192103 : Blo 1190412 1192103 := bstep (se 1 (by rfl) ⟨894077, by rfl⟩ : syracuseStep 1192103 = 1788155) B1788155
theorem B4018409 : Blo 1190412 4018409 := bstep (se 2 (by rfl) ⟨1506903, by rfl⟩ : syracuseStep 4018409 = 3013807) B3013807
theorem B1192255 : Blo 1190412 1192255 := bstep (se 1 (by rfl) ⟨894191, by rfl⟩ : syracuseStep 1192255 = 1788383) B1788383
theorem B4018571 : Blo 1190412 4018571 := bstep (se 1 (by rfl) ⟨3013928, by rfl⟩ : syracuseStep 4018571 = 6027857) B6027857
theorem B1339879 : Blo 1190412 1339879 := bstep (se 1 (by rfl) ⟨1004909, by rfl⟩ : syracuseStep 1339879 = 2009819) B2009819
theorem B1339951 : Blo 1190412 1339951 := bstep (se 1 (by rfl) ⟨1004963, by rfl⟩ : syracuseStep 1339951 = 2009927) B2009927
theorem B78369653 : Blo 1190412 78369653 := bstep (se 5 (by rfl) ⟨3673577, by rfl⟩ : syracuseStep 78369653 = 7347155) B7347155
theorem B1340743 : Blo 1190412 1340743 := bstep (se 1 (by rfl) ⟨1005557, by rfl⟩ : syracuseStep 1340743 = 2011115) B2011115
theorem B8820089 : Blo 1190412 8820089 := bstep (se 2 (by rfl) ⟨3307533, by rfl⟩ : syracuseStep 8820089 = 6615067) B6615067
theorem B10311421 : Blo 1190412 10311421 := bstep (se 3 (by rfl) ⟨1933391, by rfl⟩ : syracuseStep 10311421 = 3866783) B3866783
theorem B4019975 : Blo 1190412 4019975 := bstep (se 1 (by rfl) ⟨3014981, by rfl⟩ : syracuseStep 4019975 = 6029963) B6029963
theorem B6027209 : Blo 1190412 6027209 := bstep (se 2 (by rfl) ⟨2260203, by rfl⟩ : syracuseStep 6027209 = 4520407) B4520407
theorem B2545771 : Blo 1190412 2545771 := bstep (se 1 (by rfl) ⟨1909328, by rfl⟩ : syracuseStep 2545771 = 3818657) B3818657
theorem B6028019 : Blo 1190412 6028019 := bstep (se 1 (by rfl) ⟨4521014, by rfl⟩ : syracuseStep 6028019 = 9042029) B9042029
theorem B28990523 : Blo 1190412 28990523 := bstep (se 1 (by rfl) ⟨21742892, by rfl⟩ : syracuseStep 28990523 = 43485785) B43485785
theorem B39189815 : Blo 1190412 39189815 := bstep (se 1 (by rfl) ⟨29392361, by rfl⟩ : syracuseStep 39189815 = 58784723) B58784723
theorem B20356595 : Blo 1190412 20356595 := bstep (se 1 (by rfl) ⟨15267446, by rfl⟩ : syracuseStep 20356595 = 30534893) B30534893
theorem B2678687 : Blo 1190412 2678687 := bstep (se 1 (by rfl) ⟨2009015, by rfl⟩ : syracuseStep 2678687 = 4018031) B4018031
theorem B2678921 : Blo 1190412 2678921 := bstep (se 2 (by rfl) ⟨1004595, by rfl⟩ : syracuseStep 2678921 = 2009191) B2009191
theorem B2678939 : Blo 1190412 2678939 := bstep (se 1 (by rfl) ⟨2009204, by rfl⟩ : syracuseStep 2678939 = 4018409) B4018409
theorem B1507567 : Blo 1190412 1507567 := bstep (se 1 (by rfl) ⟨1130675, by rfl⟩ : syracuseStep 1507567 = 2261351) B2261351
theorem B2679047 : Blo 1190412 2679047 := bstep (se 1 (by rfl) ⟨2009285, by rfl⟩ : syracuseStep 2679047 = 4018571) B4018571
theorem B1786175 : Blo 1190412 1786175 := bstep (se 1 (by rfl) ⟨1339631, by rfl⟩ : syracuseStep 1786175 = 2679263) B2679263
theorem B9044459 : Blo 1190412 9044459 := bstep (se 1 (by rfl) ⟨6783344, by rfl⟩ : syracuseStep 9044459 = 13566689) B13566689
theorem B2753023 : Blo 1190412 2753023 := bstep (se 1 (by rfl) ⟨2064767, by rfl⟩ : syracuseStep 2753023 = 4129535) B4129535
theorem B1786505 : Blo 1190412 1786505 := bstep (se 2 (by rfl) ⟨669939, by rfl⟩ : syracuseStep 1786505 = 1339879) B1339879
theorem B1786601 : Blo 1190412 1786601 := bstep (se 2 (by rfl) ⟨669975, by rfl⟩ : syracuseStep 1786601 = 1339951) B1339951
theorem B2679785 : Blo 1190412 2679785 := bstep (se 2 (by rfl) ⟨1004919, by rfl⟩ : syracuseStep 2679785 = 2009839) B2009839
theorem B1786859 : Blo 1190412 1786859 := bstep (se 1 (by rfl) ⟨1340144, by rfl⟩ : syracuseStep 1786859 = 2680289) B2680289
theorem B3015751 : Blo 1190412 3015751 := bstep (se 1 (by rfl) ⟨2261813, by rfl⟩ : syracuseStep 3015751 = 4523627) B4523627
theorem B2679983 : Blo 1190412 2679983 := bstep (se 1 (by rfl) ⟨2009987, by rfl⟩ : syracuseStep 2679983 = 4019975) B4019975
theorem B15271091 : Blo 1190412 15271091 := bstep (se 1 (by rfl) ⟨11453318, by rfl⟩ : syracuseStep 15271091 = 22906637) B22906637
theorem B7628393 : Blo 1190412 7628393 := bstep (se 2 (by rfl) ⟨2860647, by rfl⟩ : syracuseStep 7628393 = 5721295) B5721295
theorem B1787657 : Blo 1190412 1787657 := bstep (se 2 (by rfl) ⟨670371, by rfl⟩ : syracuseStep 1787657 = 1340743) B1340743
theorem B19326761 : Blo 1190412 19326761 := bstep (se 2 (by rfl) ⟨7247535, by rfl⟩ : syracuseStep 19326761 = 14495071) B14495071
theorem B6031259 : Blo 1190412 6031259 := bstep (se 1 (by rfl) ⟨4523444, by rfl⟩ : syracuseStep 6031259 = 9046889) B9046889
theorem B1787807 : Blo 1190412 1787807 := bstep (se 1 (by rfl) ⟨1340855, by rfl⟩ : syracuseStep 1787807 = 2681711) B2681711
theorem B19327015 : Blo 1190412 19327015 := bstep (se 1 (by rfl) ⟨14495261, by rfl⟩ : syracuseStep 19327015 = 28990523) B28990523
theorem B26126543 : Blo 1190412 26126543 := bstep (se 1 (by rfl) ⟨19594907, by rfl⟩ : syracuseStep 26126543 = 39189815) B39189815
theorem B13748561 : Blo 1190412 13748561 := bstep (se 2 (by rfl) ⟨5155710, by rfl⟩ : syracuseStep 13748561 = 10311421) B10311421
theorem B1788263 : Blo 1190412 1788263 := bstep (se 1 (by rfl) ⟨1341197, by rfl⟩ : syracuseStep 1788263 = 2682395) B2682395
theorem B1788575 : Blo 1190412 1788575 := bstep (se 1 (by rfl) ⟨1341431, by rfl⟩ : syracuseStep 1788575 = 2682863) B2682863
theorem B1190651 : Blo 1190412 1190651 := bstep (se 1 (by rfl) ⟨892988, by rfl⟩ : syracuseStep 1190651 = 1785977) B1785977
theorem B3394361 : Blo 1190412 3394361 := bstep (se 2 (by rfl) ⟨1272885, by rfl⟩ : syracuseStep 3394361 = 2545771) B2545771
theorem B1190943 : Blo 1190412 1190943 := bstep (se 1 (by rfl) ⟨893207, by rfl⟩ : syracuseStep 1190943 = 1786415) B1786415
theorem B2010143 : Blo 1190412 2010143 := bstep (se 1 (by rfl) ⟨1507607, by rfl⟩ : syracuseStep 2010143 = 3015215) B3015215
theorem B1191119 : Blo 1190412 1191119 := bstep (se 1 (by rfl) ⟨893339, by rfl⟩ : syracuseStep 1191119 = 1786679) B1786679
theorem B110103785 : Blo 1190412 110103785 := bstep (se 2 (by rfl) ⟨41288919, by rfl⟩ : syracuseStep 110103785 = 82577839) B82577839
theorem B2682287 : Blo 1190412 2682287 := bstep (se 1 (by rfl) ⟨2011715, by rfl⟩ : syracuseStep 2682287 = 4023431) B4023431
theorem B1191451 : Blo 1190412 1191451 := bstep (se 1 (by rfl) ⟨893588, by rfl⟩ : syracuseStep 1191451 = 1787177) B1787177
theorem B1191583 : Blo 1190412 1191583 := bstep (se 1 (by rfl) ⟨893687, by rfl⟩ : syracuseStep 1191583 = 1787375) B1787375
theorem B2682539 : Blo 1190412 2682539 := bstep (se 1 (by rfl) ⟨2011904, by rfl⟩ : syracuseStep 2682539 = 4023809) B4023809
theorem B4018139 : Blo 1190412 4018139 := bstep (se 1 (by rfl) ⟨3013604, by rfl⟩ : syracuseStep 4018139 = 6027209) B6027209
theorem B1191963 : Blo 1190412 1191963 := bstep (se 1 (by rfl) ⟨893972, by rfl⟩ : syracuseStep 1191963 = 1787945) B1787945
theorem B5091815 : Blo 1190412 5091815 := bstep (se 1 (by rfl) ⟨3818861, by rfl⟩ : syracuseStep 5091815 = 7637723) B7637723
theorem B4018679 : Blo 1190412 4018679 := bstep (se 1 (by rfl) ⟨3014009, by rfl⟩ : syracuseStep 4018679 = 6028019) B6028019
theorem B12218975 : Blo 1190412 12218975 := bstep (se 1 (by rfl) ⟨9164231, by rfl⟩ : syracuseStep 12218975 = 18328463) B18328463
theorem B2011817 : Blo 1190412 2011817 := bstep (se 2 (by rfl) ⟨754431, by rfl⟩ : syracuseStep 2011817 = 1508863) B1508863
theorem B25760537 : Blo 1190412 25760537 := bstep (se 2 (by rfl) ⟨9660201, by rfl⟩ : syracuseStep 25760537 = 19320403) B19320403
theorem B13571063 : Blo 1190412 13571063 := bstep (se 1 (by rfl) ⟨10178297, by rfl⟩ : syracuseStep 13571063 = 20356595) B20356595
theorem B4895839 : Blo 1190412 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B4020191 : Blo 1190412 4020191 := bstep (se 1 (by rfl) ⟨3015143, by rfl⟩ : syracuseStep 4020191 = 6030287) B6030287
theorem B25778351 : Blo 1190412 25778351 := bstep (se 1 (by rfl) ⟨19333763, by rfl⟩ : syracuseStep 25778351 = 38667527) B38667527
theorem B5880059 : Blo 1190412 5880059 := bstep (se 1 (by rfl) ⟨4410044, by rfl⟩ : syracuseStep 5880059 = 8820089) B8820089
theorem B3390113 : Blo 1190412 3390113 := bstep (se 2 (by rfl) ⟨1271292, by rfl⟩ : syracuseStep 3390113 = 2542585) B2542585
theorem B23845951 : Blo 1190412 23845951 := bstep (se 1 (by rfl) ⟨17884463, by rfl⟩ : syracuseStep 23845951 = 35768927) B35768927
theorem B4021487 : Blo 1190412 4021487 := bstep (se 1 (by rfl) ⟨3016115, by rfl⟩ : syracuseStep 4021487 = 6032231) B6032231
theorem B3054847 : Blo 1190412 3054847 := bstep (se 1 (by rfl) ⟨2291135, by rfl⟩ : syracuseStep 3054847 = 4582271) B4582271
theorem B208985741 : Blo 1190412 208985741 := bstep (se 3 (by rfl) ⟨39184826, by rfl⟩ : syracuseStep 208985741 = 78369653) B78369653
theorem B1785791 : Blo 1190412 1785791 := bstep (se 1 (by rfl) ⟨1339343, by rfl⟩ : syracuseStep 1785791 = 2678687) B2678687
theorem B1785947 : Blo 1190412 1785947 := bstep (se 1 (by rfl) ⟨1339460, by rfl⟩ : syracuseStep 1785947 = 2678921) B2678921
theorem B1785959 : Blo 1190412 1785959 := bstep (se 1 (by rfl) ⟨1339469, by rfl⟩ : syracuseStep 1785959 = 2678939) B2678939
theorem B1786031 : Blo 1190412 1786031 := bstep (se 1 (by rfl) ⟨1339523, by rfl⟩ : syracuseStep 1786031 = 2679047) B2679047
theorem B6029639 : Blo 1190412 6029639 := bstep (se 1 (by rfl) ⟨4522229, by rfl⟩ : syracuseStep 6029639 = 9044459) B9044459
theorem B2679119 : Blo 1190412 2679119 := bstep (se 1 (by rfl) ⟨2009339, by rfl⟩ : syracuseStep 2679119 = 4018679) B4018679
theorem B1786523 : Blo 1190412 1786523 := bstep (se 1 (by rfl) ⟨1339892, by rfl⟩ : syracuseStep 1786523 = 2679785) B2679785
theorem B3670697 : Blo 1190412 3670697 := bstep (se 2 (by rfl) ⟨1376511, by rfl⟩ : syracuseStep 3670697 = 2753023) B2753023
theorem B1786655 : Blo 1190412 1786655 := bstep (se 1 (by rfl) ⟨1339991, by rfl⟩ : syracuseStep 1786655 = 2679983) B2679983
theorem B2680127 : Blo 1190412 2680127 := bstep (se 1 (by rfl) ⟨2010095, by rfl⟩ : syracuseStep 2680127 = 4020191) B4020191
theorem B31794601 : Blo 1190412 31794601 := bstep (se 2 (by rfl) ⟨11922975, by rfl⟩ : syracuseStep 31794601 = 23845951) B23845951
theorem B4073129 : Blo 1190412 4073129 := bstep (se 2 (by rfl) ⟨1527423, by rfl⟩ : syracuseStep 4073129 = 3054847) B3054847
theorem B2262907 : Blo 1190412 2262907 := bstep (se 1 (by rfl) ⟨1697180, by rfl⟩ : syracuseStep 2262907 = 3394361) B3394361
theorem B73402523 : Blo 1190412 73402523 := bstep (se 1 (by rfl) ⟨55051892, by rfl⟩ : syracuseStep 73402523 = 110103785) B110103785
theorem B2680991 : Blo 1190412 2680991 := bstep (se 1 (by rfl) ⟨2010743, by rfl⟩ : syracuseStep 2680991 = 4021487) B4021487
theorem B1788191 : Blo 1190412 1788191 := bstep (se 1 (by rfl) ⟨1341143, by rfl⟩ : syracuseStep 1788191 = 2682287) B2682287
theorem B139323827 : Blo 1190412 139323827 := bstep (se 1 (by rfl) ⟨104492870, by rfl⟩ : syracuseStep 139323827 = 208985741) B208985741
theorem B1788359 : Blo 1190412 1788359 := bstep (se 1 (by rfl) ⟨1341269, by rfl⟩ : syracuseStep 1788359 = 2682539) B2682539
theorem B1190527 : Blo 1190412 1190527 := bstep (se 1 (by rfl) ⟨892895, by rfl⟩ : syracuseStep 1190527 = 1785791) B1785791
theorem B1190783 : Blo 1190412 1190783 := bstep (se 1 (by rfl) ⟨893087, by rfl⟩ : syracuseStep 1190783 = 1786175) B1786175
theorem B2010089 : Blo 1190412 2010089 := bstep (se 2 (by rfl) ⟨753783, by rfl⟩ : syracuseStep 2010089 = 1507567) B1507567
theorem B3394543 : Blo 1190412 3394543 := bstep (se 1 (by rfl) ⟨2545907, by rfl⟩ : syracuseStep 3394543 = 5091815) B5091815
theorem B8145983 : Blo 1190412 8145983 := bstep (se 1 (by rfl) ⟨6109487, by rfl⟩ : syracuseStep 8145983 = 12218975) B12218975
theorem B1191003 : Blo 1190412 1191003 := bstep (se 1 (by rfl) ⟨893252, by rfl⟩ : syracuseStep 1191003 = 1786505) B1786505
theorem B1191067 : Blo 1190412 1191067 := bstep (se 1 (by rfl) ⟨893300, by rfl⟩ : syracuseStep 1191067 = 1786601) B1786601
theorem B17173691 : Blo 1190412 17173691 := bstep (se 1 (by rfl) ⟨12880268, by rfl⟩ : syracuseStep 17173691 = 25760537) B25760537
theorem B1191239 : Blo 1190412 1191239 := bstep (se 1 (by rfl) ⟨893429, by rfl⟩ : syracuseStep 1191239 = 1786859) B1786859
theorem B9047375 : Blo 1190412 9047375 := bstep (se 1 (by rfl) ⟨6785531, by rfl⟩ : syracuseStep 9047375 = 13571063) B13571063
theorem B1191771 : Blo 1190412 1191771 := bstep (se 1 (by rfl) ⟨893828, by rfl⟩ : syracuseStep 1191771 = 1787657) B1787657
theorem B1191871 : Blo 1190412 1191871 := bstep (se 1 (by rfl) ⟨893903, by rfl⟩ : syracuseStep 1191871 = 1787807) B1787807
theorem B3920039 : Blo 1190412 3920039 := bstep (se 1 (by rfl) ⟨2940029, by rfl⟩ : syracuseStep 3920039 = 5880059) B5880059
theorem B1192175 : Blo 1190412 1192175 := bstep (se 1 (by rfl) ⟨894131, by rfl⟩ : syracuseStep 1192175 = 1788263) B1788263
theorem B1192383 : Blo 1190412 1192383 := bstep (se 1 (by rfl) ⟨894287, by rfl⟩ : syracuseStep 1192383 = 1788575) B1788575
theorem B1340095 : Blo 1190412 1340095 := bstep (se 1 (by rfl) ⟨1005071, by rfl⟩ : syracuseStep 1340095 = 2010143) B2010143
theorem B25769353 : Blo 1190412 25769353 := bstep (se 2 (by rfl) ⟨9663507, by rfl⟩ : syracuseStep 25769353 = 19327015) B19327015
theorem B1341211 : Blo 1190412 1341211 := bstep (se 1 (by rfl) ⟨1005908, by rfl⟩ : syracuseStep 1341211 = 2011817) B2011817
theorem B69670781 : Blo 1190412 69670781 := bstep (se 3 (by rfl) ⟨13063271, by rfl⟩ : syracuseStep 69670781 = 26126543) B26126543
theorem B10180727 : Blo 1190412 10180727 := bstep (se 1 (by rfl) ⟨7635545, by rfl⟩ : syracuseStep 10180727 = 15271091) B15271091
theorem B5085595 : Blo 1190412 5085595 := bstep (se 1 (by rfl) ⟨3814196, by rfl⟩ : syracuseStep 5085595 = 7628393) B7628393
theorem B12884507 : Blo 1190412 12884507 := bstep (se 1 (by rfl) ⟨9663380, by rfl⟩ : syracuseStep 12884507 = 19326761) B19326761
theorem B4020839 : Blo 1190412 4020839 := bstep (se 1 (by rfl) ⟨3015629, by rfl⟩ : syracuseStep 4020839 = 6031259) B6031259
theorem B4021001 : Blo 1190412 4021001 := bstep (se 2 (by rfl) ⟨1507875, by rfl⟩ : syracuseStep 4021001 = 3015751) B3015751
theorem B17185567 : Blo 1190412 17185567 := bstep (se 1 (by rfl) ⟨12889175, by rfl⟩ : syracuseStep 17185567 = 25778351) B25778351
theorem B6527785 : Blo 1190412 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B9165707 : Blo 1190412 9165707 := bstep (se 1 (by rfl) ⟨6874280, by rfl⟩ : syracuseStep 9165707 = 13748561) B13748561
theorem B2260075 : Blo 1190412 2260075 := bstep (se 1 (by rfl) ⟨1695056, by rfl⟩ : syracuseStep 2260075 = 3390113) B3390113
theorem B2678759 : Blo 1190412 2678759 := bstep (se 1 (by rfl) ⟨2009069, by rfl⟩ : syracuseStep 2678759 = 4018139) B4018139
theorem B2613359 : Blo 1190412 2613359 := bstep (se 1 (by rfl) ⟨1960019, by rfl⟩ : syracuseStep 2613359 = 3920039) B3920039
theorem B1786079 : Blo 1190412 1786079 := bstep (se 1 (by rfl) ⟨1339559, by rfl⟩ : syracuseStep 1786079 = 2679119) B2679119
theorem B1786751 : Blo 1190412 1786751 := bstep (se 1 (by rfl) ⟨1340063, by rfl⟩ : syracuseStep 1786751 = 2680127) B2680127
theorem B1786793 : Blo 1190412 1786793 := bstep (se 2 (by rfl) ⟨670047, by rfl⟩ : syracuseStep 1786793 = 1340095) B1340095
theorem B22914089 : Blo 1190412 22914089 := bstep (se 2 (by rfl) ⟨8592783, by rfl⟩ : syracuseStep 22914089 = 17185567) B17185567
theorem B1787327 : Blo 1190412 1787327 := bstep (se 1 (by rfl) ⟨1340495, by rfl⟩ : syracuseStep 1787327 = 2680991) B2680991
theorem B92882551 : Blo 1190412 92882551 := bstep (se 1 (by rfl) ⟨69661913, by rfl⟩ : syracuseStep 92882551 = 139323827) B139323827
theorem B2680559 : Blo 1190412 2680559 := bstep (se 1 (by rfl) ⟨2010419, by rfl⟩ : syracuseStep 2680559 = 4020839) B4020839
theorem B2680667 : Blo 1190412 2680667 := bstep (se 1 (by rfl) ⟨2010500, by rfl⟩ : syracuseStep 2680667 = 4021001) B4021001
theorem B34359137 : Blo 1190412 34359137 := bstep (se 2 (by rfl) ⟨12884676, by rfl⟩ : syracuseStep 34359137 = 25769353) B25769353
theorem B6031583 : Blo 1190412 6031583 := bstep (se 1 (by rfl) ⟨4523687, by rfl⟩ : syracuseStep 6031583 = 9047375) B9047375
theorem B1788281 : Blo 1190412 1788281 := bstep (se 2 (by rfl) ⟨670605, by rfl⟩ : syracuseStep 1788281 = 1341211) B1341211
theorem B3017209 : Blo 1190412 3017209 := bstep (se 2 (by rfl) ⟨1131453, by rfl⟩ : syracuseStep 3017209 = 2262907) B2262907
theorem B1190631 : Blo 1190412 1190631 := bstep (se 1 (by rfl) ⟨892973, by rfl⟩ : syracuseStep 1190631 = 1785947) B1785947
theorem B1190639 : Blo 1190412 1190639 := bstep (se 1 (by rfl) ⟨892979, by rfl⟩ : syracuseStep 1190639 = 1785959) B1785959
theorem B1190687 : Blo 1190412 1190687 := bstep (se 1 (by rfl) ⟨893015, by rfl⟩ : syracuseStep 1190687 = 1786031) B1786031
theorem B1191015 : Blo 1190412 1191015 := bstep (se 1 (by rfl) ⟨893261, by rfl⟩ : syracuseStep 1191015 = 1786523) B1786523
theorem B1191103 : Blo 1190412 1191103 := bstep (se 1 (by rfl) ⟨893327, by rfl⟩ : syracuseStep 1191103 = 1786655) B1786655
theorem B8703713 : Blo 1190412 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B2715419 : Blo 1190412 2715419 := bstep (se 1 (by rfl) ⟨2036564, by rfl⟩ : syracuseStep 2715419 = 4073129) B4073129
theorem B4526057 : Blo 1190412 4526057 := bstep (se 2 (by rfl) ⟨1697271, by rfl⟩ : syracuseStep 4526057 = 3394543) B3394543
theorem B6787151 : Blo 1190412 6787151 := bstep (se 1 (by rfl) ⟨5090363, by rfl⟩ : syracuseStep 6787151 = 10180727) B10180727
theorem B48935015 : Blo 1190412 48935015 := bstep (se 1 (by rfl) ⟨36701261, by rfl⟩ : syracuseStep 48935015 = 73402523) B73402523
theorem B1192127 : Blo 1190412 1192127 := bstep (se 1 (by rfl) ⟨894095, by rfl⟩ : syracuseStep 1192127 = 1788191) B1788191
theorem B1192239 : Blo 1190412 1192239 := bstep (se 1 (by rfl) ⟨894179, by rfl⟩ : syracuseStep 1192239 = 1788359) B1788359
theorem B8589671 : Blo 1190412 8589671 := bstep (se 1 (by rfl) ⟨6442253, by rfl⟩ : syracuseStep 8589671 = 12884507) B12884507
theorem B1340059 : Blo 1190412 1340059 := bstep (se 1 (by rfl) ⟨1005044, by rfl⟩ : syracuseStep 1340059 = 2010089) B2010089
theorem B11449127 : Blo 1190412 11449127 := bstep (se 1 (by rfl) ⟨8586845, by rfl⟩ : syracuseStep 11449127 = 17173691) B17173691
theorem B4019759 : Blo 1190412 4019759 := bstep (se 1 (by rfl) ⟨3014819, by rfl⟩ : syracuseStep 4019759 = 6029639) B6029639
theorem B6780793 : Blo 1190412 6780793 := bstep (se 2 (by rfl) ⟨2542797, by rfl⟩ : syracuseStep 6780793 = 5085595) B5085595
theorem B46447187 : Blo 1190412 46447187 := bstep (se 1 (by rfl) ⟨34835390, by rfl⟩ : syracuseStep 46447187 = 69670781) B69670781
theorem B3013433 : Blo 1190412 3013433 := bstep (se 2 (by rfl) ⟨1130037, by rfl⟩ : syracuseStep 3013433 = 2260075) B2260075
theorem B9788525 : Blo 1190412 9788525 := bstep (se 3 (by rfl) ⟨1835348, by rfl⟩ : syracuseStep 9788525 = 3670697) B3670697
theorem B42392801 : Blo 1190412 42392801 := bstep (se 2 (by rfl) ⟨15897300, by rfl⟩ : syracuseStep 42392801 = 31794601) B31794601
theorem B6110471 : Blo 1190412 6110471 := bstep (se 1 (by rfl) ⟨4582853, by rfl⟩ : syracuseStep 6110471 = 9165707) B9165707
theorem B5430655 : Blo 1190412 5430655 := bstep (se 1 (by rfl) ⟨4072991, by rfl⟩ : syracuseStep 5430655 = 8145983) B8145983
theorem B1785839 : Blo 1190412 1785839 := bstep (se 1 (by rfl) ⟨1339379, by rfl⟩ : syracuseStep 1785839 = 2678759) B2678759
theorem B5726447 : Blo 1190412 5726447 := bstep (se 1 (by rfl) ⟨4294835, by rfl⟩ : syracuseStep 5726447 = 8589671) B8589671
theorem B4022945 : Blo 1190412 4022945 := bstep (se 2 (by rfl) ⟨1508604, by rfl⟩ : syracuseStep 4022945 = 3017209) B3017209
theorem B495436661 : Blo 1190412 495436661 := bstep (se 5 (by rfl) ⟨23223593, by rfl⟩ : syracuseStep 495436661 = 46447187) B46447187
theorem B1786745 : Blo 1190412 1786745 := bstep (se 2 (by rfl) ⟨670029, by rfl⟩ : syracuseStep 1786745 = 1340059) B1340059
theorem B2679839 : Blo 1190412 2679839 := bstep (se 1 (by rfl) ⟨2009879, by rfl⟩ : syracuseStep 2679839 = 4019759) B4019759
theorem B1787039 : Blo 1190412 1787039 := bstep (se 1 (by rfl) ⟨1340279, by rfl⟩ : syracuseStep 1787039 = 2680559) B2680559
theorem B1787111 : Blo 1190412 1787111 := bstep (se 1 (by rfl) ⟨1340333, by rfl⟩ : syracuseStep 1787111 = 2680667) B2680667
theorem B22906091 : Blo 1190412 22906091 := bstep (se 1 (by rfl) ⟨17179568, by rfl⟩ : syracuseStep 22906091 = 34359137) B34359137
theorem B2008955 : Blo 1190412 2008955 := bstep (se 1 (by rfl) ⟨1506716, by rfl⟩ : syracuseStep 2008955 = 3013433) B3013433
theorem B23209901 : Blo 1190412 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B4073647 : Blo 1190412 4073647 := bstep (se 1 (by rfl) ⟨3055235, by rfl⟩ : syracuseStep 4073647 = 6110471) B6110471
theorem B3017371 : Blo 1190412 3017371 := bstep (se 1 (by rfl) ⟨2263028, by rfl⟩ : syracuseStep 3017371 = 4526057) B4526057
theorem B1190559 : Blo 1190412 1190559 := bstep (se 1 (by rfl) ⟨892919, by rfl⟩ : syracuseStep 1190559 = 1785839) B1785839
theorem B4524767 : Blo 1190412 4524767 := bstep (se 1 (by rfl) ⟨3393575, by rfl⟩ : syracuseStep 4524767 = 6787151) B6787151
theorem B32623343 : Blo 1190412 32623343 := bstep (se 1 (by rfl) ⟨24467507, by rfl⟩ : syracuseStep 32623343 = 48935015) B48935015
theorem B1190719 : Blo 1190412 1190719 := bstep (se 1 (by rfl) ⟨893039, by rfl⟩ : syracuseStep 1190719 = 1786079) B1786079
theorem B1191167 : Blo 1190412 1191167 := bstep (se 1 (by rfl) ⟨893375, by rfl⟩ : syracuseStep 1191167 = 1786751) B1786751
theorem B1191195 : Blo 1190412 1191195 := bstep (se 1 (by rfl) ⟨893396, by rfl⟩ : syracuseStep 1191195 = 1786793) B1786793
theorem B1191551 : Blo 1190412 1191551 := bstep (se 1 (by rfl) ⟨893663, by rfl⟩ : syracuseStep 1191551 = 1787327) B1787327
theorem B1192187 : Blo 1190412 1192187 := bstep (se 1 (by rfl) ⟨894140, by rfl⟩ : syracuseStep 1192187 = 1788281) B1788281
theorem B6525683 : Blo 1190412 6525683 := bstep (se 1 (by rfl) ⟨4894262, by rfl⟩ : syracuseStep 6525683 = 9788525) B9788525
theorem B123843401 : Blo 1190412 123843401 := bstep (se 2 (by rfl) ⟨46441275, by rfl⟩ : syracuseStep 123843401 = 92882551) B92882551
theorem B9041057 : Blo 1190412 9041057 := bstep (se 2 (by rfl) ⟨3390396, by rfl⟩ : syracuseStep 9041057 = 6780793) B6780793
theorem B1742239 : Blo 1190412 1742239 := bstep (se 1 (by rfl) ⟨1306679, by rfl⟩ : syracuseStep 1742239 = 2613359) B2613359
theorem B7632751 : Blo 1190412 7632751 := bstep (se 1 (by rfl) ⟨5724563, by rfl⟩ : syracuseStep 7632751 = 11449127) B11449127
theorem B15276059 : Blo 1190412 15276059 := bstep (se 1 (by rfl) ⟨11457044, by rfl⟩ : syracuseStep 15276059 = 22914089) B22914089
theorem B4021055 : Blo 1190412 4021055 := bstep (se 1 (by rfl) ⟨3015791, by rfl⟩ : syracuseStep 4021055 = 6031583) B6031583
theorem B7240873 : Blo 1190412 7240873 := bstep (se 2 (by rfl) ⟨2715327, by rfl⟩ : syracuseStep 7240873 = 5430655) B5430655
theorem B28261867 : Blo 1190412 28261867 := bstep (se 1 (by rfl) ⟨21196400, by rfl⟩ : syracuseStep 28261867 = 42392801) B42392801
theorem B1810279 : Blo 1190412 1810279 := bstep (se 1 (by rfl) ⟨1357709, by rfl⟩ : syracuseStep 1810279 = 2715419) B2715419
theorem B3817631 : Blo 1190412 3817631 := bstep (se 1 (by rfl) ⟨2863223, by rfl⟩ : syracuseStep 3817631 = 5726447) B5726447
theorem B5431529 : Blo 1190412 5431529 := bstep (se 2 (by rfl) ⟨2036823, by rfl⟩ : syracuseStep 5431529 = 4073647) B4073647
theorem B4350455 : Blo 1190412 4350455 := bstep (se 1 (by rfl) ⟨3262841, by rfl⟩ : syracuseStep 4350455 = 6525683) B6525683
theorem B1786559 : Blo 1190412 1786559 := bstep (se 1 (by rfl) ⟨1339919, by rfl⟩ : syracuseStep 1786559 = 2679839) B2679839
theorem B15270727 : Blo 1190412 15270727 := bstep (se 1 (by rfl) ⟨11453045, by rfl⟩ : syracuseStep 15270727 = 22906091) B22906091
theorem B4023161 : Blo 1190412 4023161 := bstep (se 2 (by rfl) ⟨1508685, by rfl⟩ : syracuseStep 4023161 = 3017371) B3017371
theorem B10184039 : Blo 1190412 10184039 := bstep (se 1 (by rfl) ⟨7638029, by rfl⟩ : syracuseStep 10184039 = 15276059) B15276059
theorem B3016511 : Blo 1190412 3016511 := bstep (se 1 (by rfl) ⟨2262383, by rfl⟩ : syracuseStep 3016511 = 4524767) B4524767
theorem B2680703 : Blo 1190412 2680703 := bstep (se 1 (by rfl) ⟨2010527, by rfl⟩ : syracuseStep 2680703 = 4021055) B4021055
theorem B9291941 : Blo 1190412 9291941 := bstep (se 4 (by rfl) ⟨871119, by rfl⟩ : syracuseStep 9291941 = 1742239) B1742239
theorem B10177001 : Blo 1190412 10177001 := bstep (se 2 (by rfl) ⟨3816375, by rfl⟩ : syracuseStep 10177001 = 7632751) B7632751
theorem B2681963 : Blo 1190412 2681963 := bstep (se 1 (by rfl) ⟨2011472, by rfl⟩ : syracuseStep 2681963 = 4022945) B4022945
theorem B82562267 : Blo 1190412 82562267 := bstep (se 1 (by rfl) ⟨61921700, by rfl⟩ : syracuseStep 82562267 = 123843401) B123843401
theorem B1191163 : Blo 1190412 1191163 := bstep (se 1 (by rfl) ⟨893372, by rfl⟩ : syracuseStep 1191163 = 1786745) B1786745
theorem B1191359 : Blo 1190412 1191359 := bstep (se 1 (by rfl) ⟨893519, by rfl⟩ : syracuseStep 1191359 = 1787039) B1787039
theorem B1191407 : Blo 1190412 1191407 := bstep (se 1 (by rfl) ⟨893555, by rfl⟩ : syracuseStep 1191407 = 1787111) B1787111
theorem B1339303 : Blo 1190412 1339303 := bstep (se 1 (by rfl) ⟨1004477, by rfl⟩ : syracuseStep 1339303 = 2008955) B2008955
theorem B9654497 : Blo 1190412 9654497 := bstep (se 2 (by rfl) ⟨3620436, by rfl⟩ : syracuseStep 9654497 = 7240873) B7240873
theorem B9654821 : Blo 1190412 9654821 := bstep (se 4 (by rfl) ⟨905139, by rfl⟩ : syracuseStep 9654821 = 1810279) B1810279
theorem B330291107 : Blo 1190412 330291107 := bstep (se 1 (by rfl) ⟨247718330, by rfl⟩ : syracuseStep 330291107 = 495436661) B495436661
theorem B6027371 : Blo 1190412 6027371 := bstep (se 1 (by rfl) ⟨4520528, by rfl⟩ : syracuseStep 6027371 = 9041057) B9041057
theorem B15473267 : Blo 1190412 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B21748895 : Blo 1190412 21748895 := bstep (se 1 (by rfl) ⟨16311671, by rfl⟩ : syracuseStep 21748895 = 32623343) B32623343
theorem B37682489 : Blo 1190412 37682489 := bstep (se 2 (by rfl) ⟨14130933, by rfl⟩ : syracuseStep 37682489 = 28261867) B28261867
theorem B3621019 : Blo 1190412 3621019 := bstep (se 1 (by rfl) ⟨2715764, by rfl⟩ : syracuseStep 3621019 = 5431529) B5431529
theorem B2900303 : Blo 1190412 2900303 := bstep (se 1 (by rfl) ⟨2175227, by rfl⟩ : syracuseStep 2900303 = 4350455) B4350455
theorem B1787135 : Blo 1190412 1787135 := bstep (se 1 (by rfl) ⟨1340351, by rfl⟩ : syracuseStep 1787135 = 2680703) B2680703
theorem B220194071 : Blo 1190412 220194071 := bstep (se 1 (by rfl) ⟨165145553, by rfl⟩ : syracuseStep 220194071 = 330291107) B330291107
theorem B6194627 : Blo 1190412 6194627 := bstep (se 1 (by rfl) ⟨4645970, by rfl⟩ : syracuseStep 6194627 = 9291941) B9291941
theorem B6784667 : Blo 1190412 6784667 := bstep (se 1 (by rfl) ⟨5088500, by rfl⟩ : syracuseStep 6784667 = 10177001) B10177001
theorem B10315511 : Blo 1190412 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B1787975 : Blo 1190412 1787975 := bstep (se 1 (by rfl) ⟨1340981, by rfl⟩ : syracuseStep 1787975 = 2681963) B2681963
theorem B1191039 : Blo 1190412 1191039 := bstep (se 1 (by rfl) ⟨893279, by rfl⟩ : syracuseStep 1191039 = 1786559) B1786559
theorem B2682107 : Blo 1190412 2682107 := bstep (se 1 (by rfl) ⟨2011580, by rfl⟩ : syracuseStep 2682107 = 4023161) B4023161
theorem B20360969 : Blo 1190412 20360969 := bstep (se 2 (by rfl) ⟨7635363, by rfl⟩ : syracuseStep 20360969 = 15270727) B15270727
theorem B2011007 : Blo 1190412 2011007 := bstep (se 1 (by rfl) ⟨1508255, by rfl⟩ : syracuseStep 2011007 = 3016511) B3016511
theorem B4018247 : Blo 1190412 4018247 := bstep (se 1 (by rfl) ⟨3013685, by rfl⟩ : syracuseStep 4018247 = 6027371) B6027371
theorem B25121659 : Blo 1190412 25121659 := bstep (se 1 (by rfl) ⟨18841244, by rfl⟩ : syracuseStep 25121659 = 37682489) B37682489
theorem B6436331 : Blo 1190412 6436331 := bstep (se 1 (by rfl) ⟨4827248, by rfl⟩ : syracuseStep 6436331 = 9654497) B9654497
theorem B6436547 : Blo 1190412 6436547 := bstep (se 1 (by rfl) ⟨4827410, by rfl⟩ : syracuseStep 6436547 = 9654821) B9654821
theorem B10180349 : Blo 1190412 10180349 := bstep (se 3 (by rfl) ⟨1908815, by rfl⟩ : syracuseStep 10180349 = 3817631) B3817631
theorem B6789359 : Blo 1190412 6789359 := bstep (se 1 (by rfl) ⟨5092019, by rfl⟩ : syracuseStep 6789359 = 10184039) B10184039
theorem B14499263 : Blo 1190412 14499263 := bstep (se 1 (by rfl) ⟨10874447, by rfl⟩ : syracuseStep 14499263 = 21748895) B21748895
theorem B55041511 : Blo 1190412 55041511 := bstep (se 1 (by rfl) ⟨41281133, by rfl⟩ : syracuseStep 55041511 = 82562267) B82562267
theorem B1785737 : Blo 1190412 1785737 := bstep (se 2 (by rfl) ⟨669651, by rfl⟩ : syracuseStep 1785737 = 1339303) B1339303
theorem B2678831 : Blo 1190412 2678831 := bstep (se 1 (by rfl) ⟨2009123, by rfl⟩ : syracuseStep 2678831 = 4018247) B4018247
theorem B1933535 : Blo 1190412 1933535 := bstep (se 1 (by rfl) ⟨1450151, by rfl⟩ : syracuseStep 1933535 = 2900303) B2900303
theorem B4129751 : Blo 1190412 4129751 := bstep (se 1 (by rfl) ⟨3097313, by rfl⟩ : syracuseStep 4129751 = 6194627) B6194627
theorem B4523111 : Blo 1190412 4523111 := bstep (se 1 (by rfl) ⟨3392333, by rfl⟩ : syracuseStep 4523111 = 6784667) B6784667
theorem B1788071 : Blo 1190412 1788071 := bstep (se 1 (by rfl) ⟨1341053, by rfl⟩ : syracuseStep 1788071 = 2682107) B2682107
theorem B1190491 : Blo 1190412 1190491 := bstep (se 1 (by rfl) ⟨892868, by rfl⟩ : syracuseStep 1190491 = 1785737) B1785737
theorem B4828025 : Blo 1190412 4828025 := bstep (se 2 (by rfl) ⟨1810509, by rfl⟩ : syracuseStep 4828025 = 3621019) B3621019
theorem B1191423 : Blo 1190412 1191423 := bstep (se 1 (by rfl) ⟨893567, by rfl⟩ : syracuseStep 1191423 = 1787135) B1787135
theorem B146796047 : Blo 1190412 146796047 := bstep (se 1 (by rfl) ⟨110097035, by rfl⟩ : syracuseStep 146796047 = 220194071) B220194071
theorem B6877007 : Blo 1190412 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B6786899 : Blo 1190412 6786899 := bstep (se 1 (by rfl) ⟨5090174, by rfl⟩ : syracuseStep 6786899 = 10180349) B10180349
theorem B1191983 : Blo 1190412 1191983 := bstep (se 1 (by rfl) ⟨893987, by rfl⟩ : syracuseStep 1191983 = 1787975) B1787975
theorem B4526239 : Blo 1190412 4526239 := bstep (se 1 (by rfl) ⟨3394679, by rfl⟩ : syracuseStep 4526239 = 6789359) B6789359
theorem B73388681 : Blo 1190412 73388681 := bstep (se 2 (by rfl) ⟨27520755, by rfl⟩ : syracuseStep 73388681 = 55041511) B55041511
theorem B1340671 : Blo 1190412 1340671 := bstep (se 1 (by rfl) ⟨1005503, by rfl⟩ : syracuseStep 1340671 = 2011007) B2011007
theorem B4290887 : Blo 1190412 4290887 := bstep (se 1 (by rfl) ⟨3218165, by rfl⟩ : syracuseStep 4290887 = 6436331) B6436331
theorem B4291031 : Blo 1190412 4291031 := bstep (se 1 (by rfl) ⟨3218273, by rfl⟩ : syracuseStep 4291031 = 6436547) B6436547
theorem B33495545 : Blo 1190412 33495545 := bstep (se 2 (by rfl) ⟨12560829, by rfl⟩ : syracuseStep 33495545 = 25121659) B25121659
theorem B9666175 : Blo 1190412 9666175 := bstep (se 1 (by rfl) ⟨7249631, by rfl⟩ : syracuseStep 9666175 = 14499263) B14499263
theorem B13573979 : Blo 1190412 13573979 := bstep (se 1 (by rfl) ⟨10180484, by rfl⟩ : syracuseStep 13573979 = 20360969) B20360969
theorem B1785887 : Blo 1190412 1785887 := bstep (se 1 (by rfl) ⟨1339415, by rfl⟩ : syracuseStep 1785887 = 2678831) B2678831
theorem B2753167 : Blo 1190412 2753167 := bstep (se 1 (by rfl) ⟨2064875, by rfl⟩ : syracuseStep 2753167 = 4129751) B4129751
theorem B3015407 : Blo 1190412 3015407 := bstep (se 1 (by rfl) ⟨2261555, by rfl⟩ : syracuseStep 3015407 = 4523111) B4523111
theorem B2860591 : Blo 1190412 2860591 := bstep (se 1 (by rfl) ⟨2145443, by rfl⟩ : syracuseStep 2860591 = 4290887) B4290887
theorem B2860687 : Blo 1190412 2860687 := bstep (se 1 (by rfl) ⟨2145515, by rfl⟩ : syracuseStep 2860687 = 4291031) B4291031
theorem B1787561 : Blo 1190412 1787561 := bstep (se 2 (by rfl) ⟨670335, by rfl⟩ : syracuseStep 1787561 = 1340671) B1340671
theorem B12888233 : Blo 1190412 12888233 := bstep (se 2 (by rfl) ⟨4833087, by rfl⟩ : syracuseStep 12888233 = 9666175) B9666175
theorem B97864031 : Blo 1190412 97864031 := bstep (se 1 (by rfl) ⟨73398023, by rfl⟩ : syracuseStep 97864031 = 146796047) B146796047
theorem B4524599 : Blo 1190412 4524599 := bstep (se 1 (by rfl) ⟨3393449, by rfl⟩ : syracuseStep 4524599 = 6786899) B6786899
theorem B1289023 : Blo 1190412 1289023 := bstep (se 1 (by rfl) ⟨966767, by rfl⟩ : syracuseStep 1289023 = 1933535) B1933535
theorem B48925787 : Blo 1190412 48925787 := bstep (se 1 (by rfl) ⟨36694340, by rfl⟩ : syracuseStep 48925787 = 73388681) B73388681
theorem B1192047 : Blo 1190412 1192047 := bstep (se 1 (by rfl) ⟨894035, by rfl⟩ : syracuseStep 1192047 = 1788071) B1788071
theorem B12874733 : Blo 1190412 12874733 := bstep (se 3 (by rfl) ⟨2414012, by rfl⟩ : syracuseStep 12874733 = 4828025) B4828025
theorem B4584671 : Blo 1190412 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B9049319 : Blo 1190412 9049319 := bstep (se 1 (by rfl) ⟨6786989, by rfl⟩ : syracuseStep 9049319 = 13573979) B13573979
theorem B6034985 : Blo 1190412 6034985 := bstep (se 2 (by rfl) ⟨2263119, by rfl⟩ : syracuseStep 6034985 = 4526239) B4526239
theorem B22330363 : Blo 1190412 22330363 := bstep (se 1 (by rfl) ⟨16747772, by rfl⟩ : syracuseStep 22330363 = 33495545) B33495545
theorem B3056447 : Blo 1190412 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B3670889 : Blo 1190412 3670889 := bstep (se 2 (by rfl) ⟨1376583, by rfl⟩ : syracuseStep 3670889 = 2753167) B2753167
theorem B4023323 : Blo 1190412 4023323 := bstep (se 1 (by rfl) ⟨3017492, by rfl⟩ : syracuseStep 4023323 = 6034985) B6034985
theorem B65242687 : Blo 1190412 65242687 := bstep (se 1 (by rfl) ⟨48932015, by rfl⟩ : syracuseStep 65242687 = 97864031) B97864031
theorem B6874789 : Blo 1190412 6874789 := bstep (se 4 (by rfl) ⟨644511, by rfl⟩ : syracuseStep 6874789 = 1289023) B1289023
theorem B3016399 : Blo 1190412 3016399 := bstep (se 1 (by rfl) ⟨2262299, by rfl⟩ : syracuseStep 3016399 = 4524599) B4524599
theorem B1190591 : Blo 1190412 1190591 := bstep (se 1 (by rfl) ⟨892943, by rfl⟩ : syracuseStep 1190591 = 1785887) B1785887
theorem B130468765 : Blo 1190412 130468765 := bstep (se 3 (by rfl) ⟨24462893, by rfl⟩ : syracuseStep 130468765 = 48925787) B48925787
theorem B2010271 : Blo 1190412 2010271 := bstep (se 1 (by rfl) ⟨1507703, by rfl⟩ : syracuseStep 2010271 = 3015407) B3015407
theorem B6032879 : Blo 1190412 6032879 := bstep (se 1 (by rfl) ⟨4524659, by rfl⟩ : syracuseStep 6032879 = 9049319) B9049319
theorem B1191707 : Blo 1190412 1191707 := bstep (se 1 (by rfl) ⟨893780, by rfl⟩ : syracuseStep 1191707 = 1787561) B1787561
theorem B29773817 : Blo 1190412 29773817 := bstep (se 2 (by rfl) ⟨11165181, by rfl⟩ : syracuseStep 29773817 = 22330363) B22330363
theorem B3814121 : Blo 1190412 3814121 := bstep (se 2 (by rfl) ⟨1430295, by rfl⟩ : syracuseStep 3814121 = 2860591) B2860591
theorem B3814249 : Blo 1190412 3814249 := bstep (se 2 (by rfl) ⟨1430343, by rfl⟩ : syracuseStep 3814249 = 2860687) B2860687
theorem B8583155 : Blo 1190412 8583155 := bstep (se 1 (by rfl) ⟨6437366, by rfl⟩ : syracuseStep 8583155 = 12874733) B12874733
theorem B8592155 : Blo 1190412 8592155 := bstep (se 1 (by rfl) ⟨6444116, by rfl⟩ : syracuseStep 8592155 = 12888233) B12888233
theorem B173958353 : Blo 1190412 173958353 := bstep (se 2 (by rfl) ⟨65234382, by rfl⟩ : syracuseStep 173958353 = 130468765) B130468765
theorem B2680361 : Blo 1190412 2680361 := bstep (se 2 (by rfl) ⟨1005135, by rfl⟩ : syracuseStep 2680361 = 2010271) B2010271
theorem B5728103 : Blo 1190412 5728103 := bstep (se 1 (by rfl) ⟨4296077, by rfl⟩ : syracuseStep 5728103 = 8592155) B8592155
theorem B2542747 : Blo 1190412 2542747 := bstep (se 1 (by rfl) ⟨1907060, by rfl⟩ : syracuseStep 2542747 = 3814121) B3814121
theorem B2682215 : Blo 1190412 2682215 := bstep (se 1 (by rfl) ⟨2011661, by rfl⟩ : syracuseStep 2682215 = 4023323) B4023323
theorem B5722103 : Blo 1190412 5722103 := bstep (se 1 (by rfl) ⟨4291577, by rfl⟩ : syracuseStep 5722103 = 8583155) B8583155
theorem B19849211 : Blo 1190412 19849211 := bstep (se 1 (by rfl) ⟨14886908, by rfl⟩ : syracuseStep 19849211 = 29773817) B29773817
theorem B2037631 : Blo 1190412 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B39156149 : Blo 1190412 39156149 := bstep (se 5 (by rfl) ⟨1835444, by rfl⟩ : syracuseStep 39156149 = 3670889) B3670889
theorem B5085665 : Blo 1190412 5085665 := bstep (se 2 (by rfl) ⟨1907124, by rfl⟩ : syracuseStep 5085665 = 3814249) B3814249
theorem B86990249 : Blo 1190412 86990249 := bstep (se 2 (by rfl) ⟨32621343, by rfl⟩ : syracuseStep 86990249 = 65242687) B65242687
theorem B9166385 : Blo 1190412 9166385 := bstep (se 2 (by rfl) ⟨3437394, by rfl⟩ : syracuseStep 9166385 = 6874789) B6874789
theorem B4021865 : Blo 1190412 4021865 := bstep (se 2 (by rfl) ⟨1508199, by rfl⟩ : syracuseStep 4021865 = 3016399) B3016399
theorem B4021919 : Blo 1190412 4021919 := bstep (se 1 (by rfl) ⟨3016439, by rfl⟩ : syracuseStep 4021919 = 6032879) B6032879
theorem B1786907 : Blo 1190412 1786907 := bstep (se 1 (by rfl) ⟨1340180, by rfl⟩ : syracuseStep 1786907 = 2680361) B2680361
theorem B3818735 : Blo 1190412 3818735 := bstep (se 1 (by rfl) ⟨2864051, by rfl⟩ : syracuseStep 3818735 = 5728103) B5728103
theorem B1788143 : Blo 1190412 1788143 := bstep (se 1 (by rfl) ⟨1341107, by rfl⟩ : syracuseStep 1788143 = 2682215) B2682215
theorem B57993499 : Blo 1190412 57993499 := bstep (se 1 (by rfl) ⟨43495124, by rfl⟩ : syracuseStep 57993499 = 86990249) B86990249
theorem B2681243 : Blo 1190412 2681243 := bstep (se 1 (by rfl) ⟨2010932, by rfl⟩ : syracuseStep 2681243 = 4021865) B4021865
theorem B2681279 : Blo 1190412 2681279 := bstep (se 1 (by rfl) ⟨2010959, by rfl⟩ : syracuseStep 2681279 = 4021919) B4021919
theorem B13232807 : Blo 1190412 13232807 := bstep (se 1 (by rfl) ⟨9924605, by rfl⟩ : syracuseStep 13232807 = 19849211) B19849211
theorem B26104099 : Blo 1190412 26104099 := bstep (se 1 (by rfl) ⟨19578074, by rfl⟩ : syracuseStep 26104099 = 39156149) B39156149
theorem B2716841 : Blo 1190412 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B15258941 : Blo 1190412 15258941 := bstep (se 3 (by rfl) ⟨2861051, by rfl⟩ : syracuseStep 15258941 = 5722103) B5722103
theorem B115972235 : Blo 1190412 115972235 := bstep (se 1 (by rfl) ⟨86979176, by rfl⟩ : syracuseStep 115972235 = 173958353) B173958353
theorem B3390329 : Blo 1190412 3390329 := bstep (se 2 (by rfl) ⟨1271373, by rfl⟩ : syracuseStep 3390329 = 2542747) B2542747
theorem B3390443 : Blo 1190412 3390443 := bstep (se 1 (by rfl) ⟨2542832, by rfl⟩ : syracuseStep 3390443 = 5085665) B5085665
theorem B6110923 : Blo 1190412 6110923 := bstep (se 1 (by rfl) ⟨4583192, by rfl⟩ : syracuseStep 6110923 = 9166385) B9166385
theorem B77324665 : Blo 1190412 77324665 := bstep (se 2 (by rfl) ⟨28996749, by rfl⟩ : syracuseStep 77324665 = 57993499) B57993499
theorem B1787495 : Blo 1190412 1787495 := bstep (se 1 (by rfl) ⟨1340621, by rfl⟩ : syracuseStep 1787495 = 2681243) B2681243
theorem B1787519 : Blo 1190412 1787519 := bstep (se 1 (by rfl) ⟨1340639, by rfl⟩ : syracuseStep 1787519 = 2681279) B2681279
theorem B7244909 : Blo 1190412 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B1191271 : Blo 1190412 1191271 := bstep (se 1 (by rfl) ⟨893453, by rfl⟩ : syracuseStep 1191271 = 1786907) B1786907
theorem B1192095 : Blo 1190412 1192095 := bstep (se 1 (by rfl) ⟨894071, by rfl⟩ : syracuseStep 1192095 = 1788143) B1788143
theorem B8147897 : Blo 1190412 8147897 := bstep (se 2 (by rfl) ⟨3055461, by rfl⟩ : syracuseStep 8147897 = 6110923) B6110923
theorem B34805465 : Blo 1190412 34805465 := bstep (se 2 (by rfl) ⟨13052049, by rfl⟩ : syracuseStep 34805465 = 26104099) B26104099
theorem B2545823 : Blo 1190412 2545823 := bstep (se 1 (by rfl) ⟨1909367, by rfl⟩ : syracuseStep 2545823 = 3818735) B3818735
theorem B10172627 : Blo 1190412 10172627 := bstep (se 1 (by rfl) ⟨7629470, by rfl⟩ : syracuseStep 10172627 = 15258941) B15258941
theorem B77314823 : Blo 1190412 77314823 := bstep (se 1 (by rfl) ⟨57986117, by rfl⟩ : syracuseStep 77314823 = 115972235) B115972235
theorem B8821871 : Blo 1190412 8821871 := bstep (se 1 (by rfl) ⟨6616403, by rfl⟩ : syracuseStep 8821871 = 13232807) B13232807
theorem B2260219 : Blo 1190412 2260219 := bstep (se 1 (by rfl) ⟨1695164, by rfl⟩ : syracuseStep 2260219 = 3390329) B3390329
theorem B2260295 : Blo 1190412 2260295 := bstep (se 1 (by rfl) ⟨1695221, by rfl⟩ : syracuseStep 2260295 = 3390443) B3390443
theorem B5431931 : Blo 1190412 5431931 := bstep (se 1 (by rfl) ⟨4073948, by rfl⟩ : syracuseStep 5431931 = 8147897) B8147897
theorem B1697215 : Blo 1190412 1697215 := bstep (se 1 (by rfl) ⟨1272911, by rfl⟩ : syracuseStep 1697215 = 2545823) B2545823
theorem B103099553 : Blo 1190412 103099553 := bstep (se 2 (by rfl) ⟨38662332, by rfl⟩ : syracuseStep 103099553 = 77324665) B77324665
theorem B1191663 : Blo 1190412 1191663 := bstep (se 1 (by rfl) ⟨893747, by rfl⟩ : syracuseStep 1191663 = 1787495) B1787495
theorem B1191679 : Blo 1190412 1191679 := bstep (se 1 (by rfl) ⟨893759, by rfl⟩ : syracuseStep 1191679 = 1787519) B1787519
theorem B23203643 : Blo 1190412 23203643 := bstep (se 1 (by rfl) ⟨17402732, by rfl⟩ : syracuseStep 23203643 = 34805465) B34805465
theorem B4829939 : Blo 1190412 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B6781751 : Blo 1190412 6781751 := bstep (se 1 (by rfl) ⟨5086313, by rfl⟩ : syracuseStep 6781751 = 10172627) B10172627
theorem B3013625 : Blo 1190412 3013625 := bstep (se 2 (by rfl) ⟨1130109, by rfl⟩ : syracuseStep 3013625 = 2260219) B2260219
theorem B51543215 : Blo 1190412 51543215 := bstep (se 1 (by rfl) ⟨38657411, by rfl⟩ : syracuseStep 51543215 = 77314823) B77314823
theorem B5881247 : Blo 1190412 5881247 := bstep (se 1 (by rfl) ⟨4410935, by rfl⟩ : syracuseStep 5881247 = 8821871) B8821871
theorem B1506863 : Blo 1190412 1506863 := bstep (se 1 (by rfl) ⟨1130147, by rfl⟩ : syracuseStep 1506863 = 2260295) B2260295
theorem B3621287 : Blo 1190412 3621287 := bstep (se 1 (by rfl) ⟨2715965, by rfl⟩ : syracuseStep 3621287 = 5431931) B5431931
theorem B3219959 : Blo 1190412 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B2262953 : Blo 1190412 2262953 := bstep (se 2 (by rfl) ⟨848607, by rfl⟩ : syracuseStep 2262953 = 1697215) B1697215
theorem B2009083 : Blo 1190412 2009083 := bstep (se 1 (by rfl) ⟨1506812, by rfl⟩ : syracuseStep 2009083 = 3013625) B3013625
theorem B68733035 : Blo 1190412 68733035 := bstep (se 1 (by rfl) ⟨51549776, by rfl⟩ : syracuseStep 68733035 = 103099553) B103099553
theorem B61876381 : Blo 1190412 61876381 := bstep (se 3 (by rfl) ⟨11601821, by rfl⟩ : syracuseStep 61876381 = 23203643) B23203643
theorem B4018301 : Blo 1190412 4018301 := bstep (se 3 (by rfl) ⟨753431, by rfl⟩ : syracuseStep 4018301 = 1506863) B1506863
theorem B34362143 : Blo 1190412 34362143 := bstep (se 1 (by rfl) ⟨25771607, by rfl⟩ : syracuseStep 34362143 = 51543215) B51543215
theorem B3920831 : Blo 1190412 3920831 := bstep (se 1 (by rfl) ⟨2940623, by rfl⟩ : syracuseStep 3920831 = 5881247) B5881247
theorem B4521167 : Blo 1190412 4521167 := bstep (se 1 (by rfl) ⟨3390875, by rfl⟩ : syracuseStep 4521167 = 6781751) B6781751
theorem B2678867 : Blo 1190412 2678867 := bstep (se 1 (by rfl) ⟨2009150, by rfl⟩ : syracuseStep 2678867 = 4018301) B4018301
theorem B82501841 : Blo 1190412 82501841 := bstep (se 2 (by rfl) ⟨30938190, by rfl⟩ : syracuseStep 82501841 = 61876381) B61876381
theorem B2613887 : Blo 1190412 2613887 := bstep (se 1 (by rfl) ⟨1960415, by rfl⟩ : syracuseStep 2613887 = 3920831) B3920831
theorem B1508635 : Blo 1190412 1508635 := bstep (se 1 (by rfl) ⟨1131476, by rfl⟩ : syracuseStep 1508635 = 2262953) B2262953
theorem B8586557 : Blo 1190412 8586557 := bstep (se 3 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 8586557 = 3219959) B3219959
theorem B22908095 : Blo 1190412 22908095 := bstep (se 1 (by rfl) ⟨17181071, by rfl⟩ : syracuseStep 22908095 = 34362143) B34362143
theorem B45822023 : Blo 1190412 45822023 := bstep (se 1 (by rfl) ⟨34366517, by rfl⟩ : syracuseStep 45822023 = 68733035) B68733035
theorem B2414191 : Blo 1190412 2414191 := bstep (se 1 (by rfl) ⟨1810643, by rfl⟩ : syracuseStep 2414191 = 3621287) B3621287
theorem B3014111 : Blo 1190412 3014111 := bstep (se 1 (by rfl) ⟨2260583, by rfl⟩ : syracuseStep 3014111 = 4521167) B4521167
theorem B2678777 : Blo 1190412 2678777 := bstep (se 2 (by rfl) ⟨1004541, by rfl⟩ : syracuseStep 2678777 = 2009083) B2009083
theorem B30548015 : Blo 1190412 30548015 := bstep (se 1 (by rfl) ⟨22911011, by rfl⟩ : syracuseStep 30548015 = 45822023) B45822023
theorem B1785911 : Blo 1190412 1785911 := bstep (se 1 (by rfl) ⟨1339433, by rfl⟩ : syracuseStep 1785911 = 2678867) B2678867
theorem B220004909 : Blo 1190412 220004909 := bstep (se 3 (by rfl) ⟨41250920, by rfl⟩ : syracuseStep 220004909 = 82501841) B82501841
theorem B15272063 : Blo 1190412 15272063 := bstep (se 1 (by rfl) ⟨11454047, by rfl⟩ : syracuseStep 15272063 = 22908095) B22908095
theorem B2009407 : Blo 1190412 2009407 := bstep (se 1 (by rfl) ⟨1507055, by rfl⟩ : syracuseStep 2009407 = 3014111) B3014111
theorem B2011513 : Blo 1190412 2011513 := bstep (se 2 (by rfl) ⟨754317, by rfl⟩ : syracuseStep 2011513 = 1508635) B1508635
theorem B1742591 : Blo 1190412 1742591 := bstep (se 1 (by rfl) ⟨1306943, by rfl⟩ : syracuseStep 1742591 = 2613887) B2613887
theorem B5724371 : Blo 1190412 5724371 := bstep (se 1 (by rfl) ⟨4293278, by rfl⟩ : syracuseStep 5724371 = 8586557) B8586557
theorem B3218921 : Blo 1190412 3218921 := bstep (se 2 (by rfl) ⟨1207095, by rfl⟩ : syracuseStep 3218921 = 2414191) B2414191
theorem B1785851 : Blo 1190412 1785851 := bstep (se 1 (by rfl) ⟨1339388, by rfl⟩ : syracuseStep 1785851 = 2678777) B2678777
theorem B20365343 : Blo 1190412 20365343 := bstep (se 1 (by rfl) ⟨15274007, by rfl⟩ : syracuseStep 20365343 = 30548015) B30548015
theorem B146669939 : Blo 1190412 146669939 := bstep (se 1 (by rfl) ⟨110002454, by rfl⟩ : syracuseStep 146669939 = 220004909) B220004909
theorem B2679209 : Blo 1190412 2679209 := bstep (se 2 (by rfl) ⟨1004703, by rfl⟩ : syracuseStep 2679209 = 2009407) B2009407
theorem B4646909 : Blo 1190412 4646909 := bstep (se 3 (by rfl) ⟨871295, by rfl⟩ : syracuseStep 4646909 = 1742591) B1742591
theorem B1190567 : Blo 1190412 1190567 := bstep (se 1 (by rfl) ⟨892925, by rfl⟩ : syracuseStep 1190567 = 1785851) B1785851
theorem B1190607 : Blo 1190412 1190607 := bstep (se 1 (by rfl) ⟨892955, by rfl⟩ : syracuseStep 1190607 = 1785911) B1785911
theorem B2682017 : Blo 1190412 2682017 := bstep (se 2 (by rfl) ⟨1005756, by rfl⟩ : syracuseStep 2682017 = 2011513) B2011513
theorem B10181375 : Blo 1190412 10181375 := bstep (se 1 (by rfl) ⟨7636031, by rfl⟩ : syracuseStep 10181375 = 15272063) B15272063
theorem B3816247 : Blo 1190412 3816247 := bstep (se 1 (by rfl) ⟨2862185, by rfl⟩ : syracuseStep 3816247 = 5724371) B5724371
theorem B2145947 : Blo 1190412 2145947 := bstep (se 1 (by rfl) ⟨1609460, by rfl⟩ : syracuseStep 2145947 = 3218921) B3218921
theorem B97779959 : Blo 1190412 97779959 := bstep (se 1 (by rfl) ⟨73334969, by rfl⟩ : syracuseStep 97779959 = 146669939) B146669939
theorem B1786139 : Blo 1190412 1786139 := bstep (se 1 (by rfl) ⟨1339604, by rfl⟩ : syracuseStep 1786139 = 2679209) B2679209
theorem B5088329 : Blo 1190412 5088329 := bstep (se 2 (by rfl) ⟨1908123, by rfl⟩ : syracuseStep 5088329 = 3816247) B3816247
theorem B3097939 : Blo 1190412 3097939 := bstep (se 1 (by rfl) ⟨2323454, by rfl⟩ : syracuseStep 3097939 = 4646909) B4646909
theorem B1788011 : Blo 1190412 1788011 := bstep (se 1 (by rfl) ⟨1341008, by rfl⟩ : syracuseStep 1788011 = 2682017) B2682017
theorem B13576895 : Blo 1190412 13576895 := bstep (se 1 (by rfl) ⟨10182671, by rfl⟩ : syracuseStep 13576895 = 20365343) B20365343
theorem B5722525 : Blo 1190412 5722525 := bstep (se 3 (by rfl) ⟨1072973, by rfl⟩ : syracuseStep 5722525 = 2145947) B2145947
theorem B6787583 : Blo 1190412 6787583 := bstep (se 1 (by rfl) ⟨5090687, by rfl⟩ : syracuseStep 6787583 = 10181375) B10181375
theorem B3392219 : Blo 1190412 3392219 := bstep (se 1 (by rfl) ⟨2544164, by rfl⟩ : syracuseStep 3392219 = 5088329) B5088329
theorem B4130585 : Blo 1190412 4130585 := bstep (se 2 (by rfl) ⟨1548969, by rfl⟩ : syracuseStep 4130585 = 3097939) B3097939
theorem B65186639 : Blo 1190412 65186639 := bstep (se 1 (by rfl) ⟨48889979, by rfl⟩ : syracuseStep 65186639 = 97779959) B97779959
theorem B1190759 : Blo 1190412 1190759 := bstep (se 1 (by rfl) ⟨893069, by rfl⟩ : syracuseStep 1190759 = 1786139) B1786139
theorem B4525055 : Blo 1190412 4525055 := bstep (se 1 (by rfl) ⟨3393791, by rfl⟩ : syracuseStep 4525055 = 6787583) B6787583
theorem B7630033 : Blo 1190412 7630033 := bstep (se 2 (by rfl) ⟨2861262, by rfl⟩ : syracuseStep 7630033 = 5722525) B5722525
theorem B1192007 : Blo 1190412 1192007 := bstep (se 1 (by rfl) ⟨894005, by rfl⟩ : syracuseStep 1192007 = 1788011) B1788011
theorem B9051263 : Blo 1190412 9051263 := bstep (se 1 (by rfl) ⟨6788447, by rfl⟩ : syracuseStep 9051263 = 13576895) B13576895
theorem B2753723 : Blo 1190412 2753723 := bstep (se 1 (by rfl) ⟨2065292, by rfl⟩ : syracuseStep 2753723 = 4130585) B4130585
theorem B9045917 : Blo 1190412 9045917 := bstep (se 3 (by rfl) ⟨1696109, by rfl⟩ : syracuseStep 9045917 = 3392219) B3392219
theorem B3016703 : Blo 1190412 3016703 := bstep (se 1 (by rfl) ⟨2262527, by rfl⟩ : syracuseStep 3016703 = 4525055) B4525055
theorem B6034175 : Blo 1190412 6034175 := bstep (se 1 (by rfl) ⟨4525631, by rfl⟩ : syracuseStep 6034175 = 9051263) B9051263
theorem B10173377 : Blo 1190412 10173377 := bstep (se 2 (by rfl) ⟨3815016, by rfl⟩ : syracuseStep 10173377 = 7630033) B7630033
theorem B43457759 : Blo 1190412 43457759 := bstep (se 1 (by rfl) ⟨32593319, by rfl⟩ : syracuseStep 43457759 = 65186639) B65186639
theorem B4022783 : Blo 1190412 4022783 := bstep (se 1 (by rfl) ⟨3017087, by rfl⟩ : syracuseStep 4022783 = 6034175) B6034175
theorem B6030611 : Blo 1190412 6030611 := bstep (se 1 (by rfl) ⟨4522958, by rfl⟩ : syracuseStep 6030611 = 9045917) B9045917
theorem B7343261 : Blo 1190412 7343261 := bstep (se 3 (by rfl) ⟨1376861, by rfl⟩ : syracuseStep 7343261 = 2753723) B2753723
theorem B2011135 : Blo 1190412 2011135 := bstep (se 1 (by rfl) ⟨1508351, by rfl⟩ : syracuseStep 2011135 = 3016703) B3016703
theorem B28971839 : Blo 1190412 28971839 := bstep (se 1 (by rfl) ⟨21728879, by rfl⟩ : syracuseStep 28971839 = 43457759) B43457759
theorem B6782251 : Blo 1190412 6782251 := bstep (se 1 (by rfl) ⟨5086688, by rfl⟩ : syracuseStep 6782251 = 10173377) B10173377
theorem B2681513 : Blo 1190412 2681513 := bstep (se 2 (by rfl) ⟨1005567, by rfl⟩ : syracuseStep 2681513 = 2011135) B2011135
theorem B2681855 : Blo 1190412 2681855 := bstep (se 1 (by rfl) ⟨2011391, by rfl⟩ : syracuseStep 2681855 = 4022783) B4022783
theorem B4895507 : Blo 1190412 4895507 := bstep (se 1 (by rfl) ⟨3671630, by rfl⟩ : syracuseStep 4895507 = 7343261) B7343261
theorem B19314559 : Blo 1190412 19314559 := bstep (se 1 (by rfl) ⟨14485919, by rfl⟩ : syracuseStep 19314559 = 28971839) B28971839
theorem B4020407 : Blo 1190412 4020407 := bstep (se 1 (by rfl) ⟨3015305, by rfl⟩ : syracuseStep 4020407 = 6030611) B6030611
theorem B9043001 : Blo 1190412 9043001 := bstep (se 2 (by rfl) ⟨3391125, by rfl⟩ : syracuseStep 9043001 = 6782251) B6782251
theorem B2680271 : Blo 1190412 2680271 := bstep (se 1 (by rfl) ⟨2010203, by rfl⟩ : syracuseStep 2680271 = 4020407) B4020407
theorem B1787675 : Blo 1190412 1787675 := bstep (se 1 (by rfl) ⟨1340756, by rfl⟩ : syracuseStep 1787675 = 2681513) B2681513
theorem B1787903 : Blo 1190412 1787903 := bstep (se 1 (by rfl) ⟨1340927, by rfl⟩ : syracuseStep 1787903 = 2681855) B2681855
theorem B3263671 : Blo 1190412 3263671 := bstep (se 1 (by rfl) ⟨2447753, by rfl⟩ : syracuseStep 3263671 = 4895507) B4895507
theorem B25752745 : Blo 1190412 25752745 := bstep (se 2 (by rfl) ⟨9657279, by rfl⟩ : syracuseStep 25752745 = 19314559) B19314559
theorem B6028667 : Blo 1190412 6028667 := bstep (se 1 (by rfl) ⟨4521500, by rfl⟩ : syracuseStep 6028667 = 9043001) B9043001
theorem B1786847 : Blo 1190412 1786847 := bstep (se 1 (by rfl) ⟨1340135, by rfl⟩ : syracuseStep 1786847 = 2680271) B2680271
theorem B1191783 : Blo 1190412 1191783 := bstep (se 1 (by rfl) ⟨893837, by rfl⟩ : syracuseStep 1191783 = 1787675) B1787675
theorem B1191935 : Blo 1190412 1191935 := bstep (se 1 (by rfl) ⟨893951, by rfl⟩ : syracuseStep 1191935 = 1787903) B1787903
theorem B34336993 : Blo 1190412 34336993 := bstep (se 2 (by rfl) ⟨12876372, by rfl⟩ : syracuseStep 34336993 = 25752745) B25752745
theorem B4019111 : Blo 1190412 4019111 := bstep (se 1 (by rfl) ⟨3014333, by rfl⟩ : syracuseStep 4019111 = 6028667) B6028667
theorem B17406245 : Blo 1190412 17406245 := bstep (se 4 (by rfl) ⟨1631835, by rfl⟩ : syracuseStep 17406245 = 3263671) B3263671
theorem B2679407 : Blo 1190412 2679407 := bstep (se 1 (by rfl) ⟨2009555, by rfl⟩ : syracuseStep 2679407 = 4019111) B4019111
theorem B1191231 : Blo 1190412 1191231 := bstep (se 1 (by rfl) ⟨893423, by rfl⟩ : syracuseStep 1191231 = 1786847) B1786847
theorem B11604163 : Blo 1190412 11604163 := bstep (se 1 (by rfl) ⟨8703122, by rfl⟩ : syracuseStep 11604163 = 17406245) B17406245
theorem B45782657 : Blo 1190412 45782657 := bstep (se 2 (by rfl) ⟨17168496, by rfl⟩ : syracuseStep 45782657 = 34336993) B34336993
theorem B1786271 : Blo 1190412 1786271 := bstep (se 1 (by rfl) ⟨1339703, by rfl⟩ : syracuseStep 1786271 = 2679407) B2679407
theorem B15472217 : Blo 1190412 15472217 := bstep (se 2 (by rfl) ⟨5802081, by rfl⟩ : syracuseStep 15472217 = 11604163) B11604163
theorem B30521771 : Blo 1190412 30521771 := bstep (se 1 (by rfl) ⟨22891328, by rfl⟩ : syracuseStep 30521771 = 45782657) B45782657
theorem B10314811 : Blo 1190412 10314811 := bstep (se 1 (by rfl) ⟨7736108, by rfl⟩ : syracuseStep 10314811 = 15472217) B15472217
theorem B1190847 : Blo 1190412 1190847 := bstep (se 1 (by rfl) ⟨893135, by rfl⟩ : syracuseStep 1190847 = 1786271) B1786271
theorem B20347847 : Blo 1190412 20347847 := bstep (se 1 (by rfl) ⟨15260885, by rfl⟩ : syracuseStep 20347847 = 30521771) B30521771
theorem B13753081 : Blo 1190412 13753081 := bstep (se 2 (by rfl) ⟨5157405, by rfl⟩ : syracuseStep 13753081 = 10314811) B10314811
theorem B13565231 : Blo 1190412 13565231 := bstep (se 1 (by rfl) ⟨10173923, by rfl⟩ : syracuseStep 13565231 = 20347847) B20347847
theorem B18337441 : Blo 1190412 18337441 := bstep (se 2 (by rfl) ⟨6876540, by rfl⟩ : syracuseStep 18337441 = 13753081) B13753081
theorem B9043487 : Blo 1190412 9043487 := bstep (se 1 (by rfl) ⟨6782615, by rfl⟩ : syracuseStep 9043487 = 13565231) B13565231
theorem B24449921 : Blo 1190412 24449921 := bstep (se 2 (by rfl) ⟨9168720, by rfl⟩ : syracuseStep 24449921 = 18337441) B18337441
theorem B6028991 : Blo 1190412 6028991 := bstep (se 1 (by rfl) ⟨4521743, by rfl⟩ : syracuseStep 6028991 = 9043487) B9043487
theorem B4019327 : Blo 1190412 4019327 := bstep (se 1 (by rfl) ⟨3014495, by rfl⟩ : syracuseStep 4019327 = 6028991) B6028991
theorem B16299947 : Blo 1190412 16299947 := bstep (se 1 (by rfl) ⟨12224960, by rfl⟩ : syracuseStep 16299947 = 24449921) B24449921
theorem B2679551 : Blo 1190412 2679551 := bstep (se 1 (by rfl) ⟨2009663, by rfl⟩ : syracuseStep 2679551 = 4019327) B4019327
theorem B10866631 : Blo 1190412 10866631 := bstep (se 1 (by rfl) ⟨8149973, by rfl⟩ : syracuseStep 10866631 = 16299947) B16299947
theorem B1786367 : Blo 1190412 1786367 := bstep (se 1 (by rfl) ⟨1339775, by rfl⟩ : syracuseStep 1786367 = 2679551) B2679551
theorem B14488841 : Blo 1190412 14488841 := bstep (se 2 (by rfl) ⟨5433315, by rfl⟩ : syracuseStep 14488841 = 10866631) B10866631
theorem B1190911 : Blo 1190412 1190911 := bstep (se 1 (by rfl) ⟨893183, by rfl⟩ : syracuseStep 1190911 = 1786367) B1786367
theorem B38636909 : Blo 1190412 38636909 := bstep (se 3 (by rfl) ⟨7244420, by rfl⟩ : syracuseStep 38636909 = 14488841) B14488841
theorem B25757939 : Blo 1190412 25757939 := bstep (se 1 (by rfl) ⟨19318454, by rfl⟩ : syracuseStep 25757939 = 38636909) B38636909
theorem B17171959 : Blo 1190412 17171959 := bstep (se 1 (by rfl) ⟨12878969, by rfl⟩ : syracuseStep 17171959 = 25757939) B25757939
theorem B22895945 : Blo 1190412 22895945 := bstep (se 2 (by rfl) ⟨8585979, by rfl⟩ : syracuseStep 22895945 = 17171959) B17171959
theorem B15263963 : Blo 1190412 15263963 := bstep (se 1 (by rfl) ⟨11447972, by rfl⟩ : syracuseStep 15263963 = 22895945) B22895945
theorem B10175975 : Blo 1190412 10175975 := bstep (se 1 (by rfl) ⟨7631981, by rfl⟩ : syracuseStep 10175975 = 15263963) B15263963
theorem B6783983 : Blo 1190412 6783983 := bstep (se 1 (by rfl) ⟨5087987, by rfl⟩ : syracuseStep 6783983 = 10175975) B10175975
theorem B4522655 : Blo 1190412 4522655 := bstep (se 1 (by rfl) ⟨3391991, by rfl⟩ : syracuseStep 4522655 = 6783983) B6783983
theorem B3015103 : Blo 1190412 3015103 := bstep (se 1 (by rfl) ⟨2261327, by rfl⟩ : syracuseStep 3015103 = 4522655) B4522655
theorem B4020137 : Blo 1190412 4020137 := bstep (se 2 (by rfl) ⟨1507551, by rfl⟩ : syracuseStep 4020137 = 3015103) B3015103
theorem B2680091 : Blo 1190412 2680091 := bstep (se 1 (by rfl) ⟨2010068, by rfl⟩ : syracuseStep 2680091 = 4020137) B4020137
theorem B1786727 : Blo 1190412 1786727 := bstep (se 1 (by rfl) ⟨1340045, by rfl⟩ : syracuseStep 1786727 = 2680091) B2680091
theorem B1191151 : Blo 1190412 1191151 := bstep (se 1 (by rfl) ⟨893363, by rfl⟩ : syracuseStep 1191151 = 1786727) B1786727

theorem C0 (j : ℕ) (h1 : 297603 ≤ j) (h2 : j ≤ 298102) : Blo 1190412 (4 * j + 3) := by
  interval_cases j
  · exact B1190415
  · exact B1190419
  · exact B1190423
  · exact B1190427
  · exact B1190431
  · exact B1190435
  · exact B1190439
  · exact B1190443
  · exact B1190447
  · exact B1190451
  · exact B1190455
  · exact B1190459
  · exact B1190463
  · exact B1190467
  · exact B1190471
  · exact B1190475
  · exact B1190479
  · exact B1190483
  · exact B1190487
  · exact B1190491
  · exact B1190495
  · exact B1190499
  · exact B1190503
  · exact B1190507
  · exact B1190511
  · exact B1190515
  · exact B1190519
  · exact B1190523
  · exact B1190527
  · exact B1190531
  · exact B1190535
  · exact B1190539
  · exact B1190543
  · exact B1190547
  · exact B1190551
  · exact B1190555
  · exact B1190559
  · exact B1190563
  · exact B1190567
  · exact B1190571
  · exact B1190575
  · exact B1190579
  · exact B1190583
  · exact B1190587
  · exact B1190591
  · exact B1190595
  · exact B1190599
  · exact B1190603
  · exact B1190607
  · exact B1190611
  · exact B1190615
  · exact B1190619
  · exact B1190623
  · exact B1190627
  · exact B1190631
  · exact B1190635
  · exact B1190639
  · exact B1190643
  · exact B1190647
  · exact B1190651
  · exact B1190655
  · exact B1190659
  · exact B1190663
  · exact B1190667
  · exact B1190671
  · exact B1190675
  · exact B1190679
  · exact B1190683
  · exact B1190687
  · exact B1190691
  · exact B1190695
  · exact B1190699
  · exact B1190703
  · exact B1190707
  · exact B1190711
  · exact B1190715
  · exact B1190719
  · exact B1190723
  · exact B1190727
  · exact B1190731
  · exact B1190735
  · exact B1190739
  · exact B1190743
  · exact B1190747
  · exact B1190751
  · exact B1190755
  · exact B1190759
  · exact B1190763
  · exact B1190767
  · exact B1190771
  · exact B1190775
  · exact B1190779
  · exact B1190783
  · exact B1190787
  · exact B1190791
  · exact B1190795
  · exact B1190799
  · exact B1190803
  · exact B1190807
  · exact B1190811
  · exact B1190815
  · exact B1190819
  · exact B1190823
  · exact B1190827
  · exact B1190831
  · exact B1190835
  · exact B1190839
  · exact B1190843
  · exact B1190847
  · exact B1190851
  · exact B1190855
  · exact B1190859
  · exact B1190863
  · exact B1190867
  · exact B1190871
  · exact B1190875
  · exact B1190879
  · exact B1190883
  · exact B1190887
  · exact B1190891
  · exact B1190895
  · exact B1190899
  · exact B1190903
  · exact B1190907
  · exact B1190911
  · exact B1190915
  · exact B1190919
  · exact B1190923
  · exact B1190927
  · exact B1190931
  · exact B1190935
  · exact B1190939
  · exact B1190943
  · exact B1190947
  · exact B1190951
  · exact B1190955
  · exact B1190959
  · exact B1190963
  · exact B1190967
  · exact B1190971
  · exact B1190975
  · exact B1190979
  · exact B1190983
  · exact B1190987
  · exact B1190991
  · exact B1190995
  · exact B1190999
  · exact B1191003
  · exact B1191007
  · exact B1191011
  · exact B1191015
  · exact B1191019
  · exact B1191023
  · exact B1191027
  · exact B1191031
  · exact B1191035
  · exact B1191039
  · exact B1191043
  · exact B1191047
  · exact B1191051
  · exact B1191055
  · exact B1191059
  · exact B1191063
  · exact B1191067
  · exact B1191071
  · exact B1191075
  · exact B1191079
  · exact B1191083
  · exact B1191087
  · exact B1191091
  · exact B1191095
  · exact B1191099
  · exact B1191103
  · exact B1191107
  · exact B1191111
  · exact B1191115
  · exact B1191119
  · exact B1191123
  · exact B1191127
  · exact B1191131
  · exact B1191135
  · exact B1191139
  · exact B1191143
  · exact B1191147
  · exact B1191151
  · exact B1191155
  · exact B1191159
  · exact B1191163
  · exact B1191167
  · exact B1191171
  · exact B1191175
  · exact B1191179
  · exact B1191183
  · exact B1191187
  · exact B1191191
  · exact B1191195
  · exact B1191199
  · exact B1191203
  · exact B1191207
  · exact B1191211
  · exact B1191215
  · exact B1191219
  · exact B1191223
  · exact B1191227
  · exact B1191231
  · exact B1191235
  · exact B1191239
  · exact B1191243
  · exact B1191247
  · exact B1191251
  · exact B1191255
  · exact B1191259
  · exact B1191263
  · exact B1191267
  · exact B1191271
  · exact B1191275
  · exact B1191279
  · exact B1191283
  · exact B1191287
  · exact B1191291
  · exact B1191295
  · exact B1191299
  · exact B1191303
  · exact B1191307
  · exact B1191311
  · exact B1191315
  · exact B1191319
  · exact B1191323
  · exact B1191327
  · exact B1191331
  · exact B1191335
  · exact B1191339
  · exact B1191343
  · exact B1191347
  · exact B1191351
  · exact B1191355
  · exact B1191359
  · exact B1191363
  · exact B1191367
  · exact B1191371
  · exact B1191375
  · exact B1191379
  · exact B1191383
  · exact B1191387
  · exact B1191391
  · exact B1191395
  · exact B1191399
  · exact B1191403
  · exact B1191407
  · exact B1191411
  · exact B1191415
  · exact B1191419
  · exact B1191423
  · exact B1191427
  · exact B1191431
  · exact B1191435
  · exact B1191439
  · exact B1191443
  · exact B1191447
  · exact B1191451
  · exact B1191455
  · exact B1191459
  · exact B1191463
  · exact B1191467
  · exact B1191471
  · exact B1191475
  · exact B1191479
  · exact B1191483
  · exact B1191487
  · exact B1191491
  · exact B1191495
  · exact B1191499
  · exact B1191503
  · exact B1191507
  · exact B1191511
  · exact B1191515
  · exact B1191519
  · exact B1191523
  · exact B1191527
  · exact B1191531
  · exact B1191535
  · exact B1191539
  · exact B1191543
  · exact B1191547
  · exact B1191551
  · exact B1191555
  · exact B1191559
  · exact B1191563
  · exact B1191567
  · exact B1191571
  · exact B1191575
  · exact B1191579
  · exact B1191583
  · exact B1191587
  · exact B1191591
  · exact B1191595
  · exact B1191599
  · exact B1191603
  · exact B1191607
  · exact B1191611
  · exact B1191615
  · exact B1191619
  · exact B1191623
  · exact B1191627
  · exact B1191631
  · exact B1191635
  · exact B1191639
  · exact B1191643
  · exact B1191647
  · exact B1191651
  · exact B1191655
  · exact B1191659
  · exact B1191663
  · exact B1191667
  · exact B1191671
  · exact B1191675
  · exact B1191679
  · exact B1191683
  · exact B1191687
  · exact B1191691
  · exact B1191695
  · exact B1191699
  · exact B1191703
  · exact B1191707
  · exact B1191711
  · exact B1191715
  · exact B1191719
  · exact B1191723
  · exact B1191727
  · exact B1191731
  · exact B1191735
  · exact B1191739
  · exact B1191743
  · exact B1191747
  · exact B1191751
  · exact B1191755
  · exact B1191759
  · exact B1191763
  · exact B1191767
  · exact B1191771
  · exact B1191775
  · exact B1191779
  · exact B1191783
  · exact B1191787
  · exact B1191791
  · exact B1191795
  · exact B1191799
  · exact B1191803
  · exact B1191807
  · exact B1191811
  · exact B1191815
  · exact B1191819
  · exact B1191823
  · exact B1191827
  · exact B1191831
  · exact B1191835
  · exact B1191839
  · exact B1191843
  · exact B1191847
  · exact B1191851
  · exact B1191855
  · exact B1191859
  · exact B1191863
  · exact B1191867
  · exact B1191871
  · exact B1191875
  · exact B1191879
  · exact B1191883
  · exact B1191887
  · exact B1191891
  · exact B1191895
  · exact B1191899
  · exact B1191903
  · exact B1191907
  · exact B1191911
  · exact B1191915
  · exact B1191919
  · exact B1191923
  · exact B1191927
  · exact B1191931
  · exact B1191935
  · exact B1191939
  · exact B1191943
  · exact B1191947
  · exact B1191951
  · exact B1191955
  · exact B1191959
  · exact B1191963
  · exact B1191967
  · exact B1191971
  · exact B1191975
  · exact B1191979
  · exact B1191983
  · exact B1191987
  · exact B1191991
  · exact B1191995
  · exact B1191999
  · exact B1192003
  · exact B1192007
  · exact B1192011
  · exact B1192015
  · exact B1192019
  · exact B1192023
  · exact B1192027
  · exact B1192031
  · exact B1192035
  · exact B1192039
  · exact B1192043
  · exact B1192047
  · exact B1192051
  · exact B1192055
  · exact B1192059
  · exact B1192063
  · exact B1192067
  · exact B1192071
  · exact B1192075
  · exact B1192079
  · exact B1192083
  · exact B1192087
  · exact B1192091
  · exact B1192095
  · exact B1192099
  · exact B1192103
  · exact B1192107
  · exact B1192111
  · exact B1192115
  · exact B1192119
  · exact B1192123
  · exact B1192127
  · exact B1192131
  · exact B1192135
  · exact B1192139
  · exact B1192143
  · exact B1192147
  · exact B1192151
  · exact B1192155
  · exact B1192159
  · exact B1192163
  · exact B1192167
  · exact B1192171
  · exact B1192175
  · exact B1192179
  · exact B1192183
  · exact B1192187
  · exact B1192191
  · exact B1192195
  · exact B1192199
  · exact B1192203
  · exact B1192207
  · exact B1192211
  · exact B1192215
  · exact B1192219
  · exact B1192223
  · exact B1192227
  · exact B1192231
  · exact B1192235
  · exact B1192239
  · exact B1192243
  · exact B1192247
  · exact B1192251
  · exact B1192255
  · exact B1192259
  · exact B1192263
  · exact B1192267
  · exact B1192271
  · exact B1192275
  · exact B1192279
  · exact B1192283
  · exact B1192287
  · exact B1192291
  · exact B1192295
  · exact B1192299
  · exact B1192303
  · exact B1192307
  · exact B1192311
  · exact B1192315
  · exact B1192319
  · exact B1192323
  · exact B1192327
  · exact B1192331
  · exact B1192335
  · exact B1192339
  · exact B1192343
  · exact B1192347
  · exact B1192351
  · exact B1192355
  · exact B1192359
  · exact B1192363
  · exact B1192367
  · exact B1192371
  · exact B1192375
  · exact B1192379
  · exact B1192383
  · exact B1192387
  · exact B1192391
  · exact B1192395
  · exact B1192399
  · exact B1192403
  · exact B1192407
  · exact B1192411

theorem solution (m : ℕ) (hlo : 1190412 ≤ m) (hhi : m ≤ 1192412) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 297603 ≤ j := by omega
    have hj2 : j ≤ 298102 := by omega
    have hb : Blo 1190412 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
