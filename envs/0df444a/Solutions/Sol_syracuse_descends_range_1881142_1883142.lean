-- Prove2me | solution 1 for syracuse_descends_range_1881142_1883142
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:17:58.137677+00:00
-- url     : https://prove2.me/submissions/b9eae911-ba24-45cf-84ab-f9a35e5b3ae5

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


theorem B3014677 : Blo 1881142 3014677 := bbase (se 6 (by rfl) ⟨70656, by rfl⟩ : syracuseStep 3014677 = 141313) (by norm_num)
theorem B4235309 : Blo 1881142 4235309 := bbase (se 3 (by rfl) ⟨794120, by rfl⟩ : syracuseStep 4235309 = 1588241) (by norm_num)
theorem B8036405 : Blo 1881142 8036405 := bbase (se 5 (by rfl) ⟨376706, by rfl⟩ : syracuseStep 8036405 = 753413) (by norm_num)
theorem B3571789 : Blo 1881142 3571789 := bbase (se 3 (by rfl) ⟨669710, by rfl⟩ : syracuseStep 3571789 = 1339421) (by norm_num)
theorem B9527381 : Blo 1881142 9527381 := bbase (se 8 (by rfl) ⟨55824, by rfl⟩ : syracuseStep 9527381 = 111649) (by norm_num)
theorem B2261081 : Blo 1881142 2261081 := bbase (se 2 (by rfl) ⟨847905, by rfl⟩ : syracuseStep 2261081 = 1695811) (by norm_num)
theorem B4235381 : Blo 1881142 4235381 := bbase (se 5 (by rfl) ⟨198533, by rfl⟩ : syracuseStep 4235381 = 397067) (by norm_num)
theorem B3219589 : Blo 1881142 3219589 := bbase (se 4 (by rfl) ⟨301836, by rfl⟩ : syracuseStep 3219589 = 603673) (by norm_num)
theorem B2678933 : Blo 1881142 2678933 := bbase (se 6 (by rfl) ⟨62787, by rfl⟩ : syracuseStep 2678933 = 125575) (by norm_num)
theorem B2146457 : Blo 1881142 2146457 := bbase (se 2 (by rfl) ⟨804921, by rfl⟩ : syracuseStep 2146457 = 1609843) (by norm_num)
theorem B4235453 : Blo 1881142 4235453 := bbase (se 3 (by rfl) ⟨794147, by rfl⟩ : syracuseStep 4235453 = 1588295) (by norm_num)
theorem B5505221 : Blo 1881142 5505221 := bbase (se 4 (by rfl) ⟨516114, by rfl⟩ : syracuseStep 5505221 = 1032229) (by norm_num)
theorem B6439109 : Blo 1881142 6439109 := bbase (se 4 (by rfl) ⟨603666, by rfl⟩ : syracuseStep 6439109 = 1207333) (by norm_num)
theorem B3571933 : Blo 1881142 3571933 := bbase (se 3 (by rfl) ⟨669737, by rfl⟩ : syracuseStep 3571933 = 1339475) (by norm_num)
theorem B7143653 : Blo 1881142 7143653 := bbase (se 4 (by rfl) ⟨669717, by rfl⟩ : syracuseStep 7143653 = 1339435) (by norm_num)
theorem B4235525 : Blo 1881142 4235525 := bbase (se 4 (by rfl) ⟨397080, by rfl⟩ : syracuseStep 4235525 = 794161) (by norm_num)
theorem B25747733 : Blo 1881142 25747733 := bbase (se 6 (by rfl) ⟨603462, by rfl⟩ : syracuseStep 25747733 = 1206925) (by norm_num)
theorem B6111541 : Blo 1881142 6111541 := bbase (se 5 (by rfl) ⟨286478, by rfl⟩ : syracuseStep 6111541 = 572957) (by norm_num)
theorem B4235597 : Blo 1881142 4235597 := bbase (se 3 (by rfl) ⟨794174, by rfl⟩ : syracuseStep 4235597 = 1588349) (by norm_num)
theorem B5087573 : Blo 1881142 5087573 := bbase (se 10 (by rfl) ⟨7452, by rfl⟩ : syracuseStep 5087573 = 14905) (by norm_num)
theorem B20914517 : Blo 1881142 20914517 := bbase (se 10 (by rfl) ⟨30636, by rfl⟩ : syracuseStep 20914517 = 61273) (by norm_num)
theorem B6349157 : Blo 1881142 6349157 := bbase (se 4 (by rfl) ⟨595233, by rfl⟩ : syracuseStep 6349157 = 1190467) (by norm_num)
theorem B3572093 : Blo 1881142 3572093 := bbase (se 3 (by rfl) ⟨669767, by rfl⟩ : syracuseStep 3572093 = 1339535) (by norm_num)
theorem B4235669 : Blo 1881142 4235669 := bbase (se 6 (by rfl) ⟨99273, by rfl⟩ : syracuseStep 4235669 = 198547) (by norm_num)
theorem B6029765 : Blo 1881142 6029765 := bbase (se 4 (by rfl) ⟨565290, by rfl⟩ : syracuseStep 6029765 = 1130581) (by norm_num)
theorem B20341205 : Blo 1881142 20341205 := bbase (se 7 (by rfl) ⟨238373, by rfl⟩ : syracuseStep 20341205 = 476747) (by norm_num)
theorem B4235741 : Blo 1881142 4235741 := bbase (se 3 (by rfl) ⟨794201, by rfl⟩ : syracuseStep 4235741 = 1588403) (by norm_num)
theorem B4522477 : Blo 1881142 4522477 := bbase (se 3 (by rfl) ⟨847964, by rfl⟩ : syracuseStep 4522477 = 1695929) (by norm_num)
theorem B3572237 : Blo 1881142 3572237 := bbase (se 3 (by rfl) ⟨669794, by rfl⟩ : syracuseStep 3572237 = 1339589) (by norm_num)
theorem B4235813 : Blo 1881142 4235813 := bbase (se 4 (by rfl) ⟨397107, by rfl⟩ : syracuseStep 4235813 = 794215) (by norm_num)
theorem B6029893 : Blo 1881142 6029893 := bbase (se 4 (by rfl) ⟨565302, by rfl⟩ : syracuseStep 6029893 = 1130605) (by norm_num)
theorem B4235885 : Blo 1881142 4235885 := bbase (se 3 (by rfl) ⟨794228, by rfl⟩ : syracuseStep 4235885 = 1588457) (by norm_num)
theorem B4235957 : Blo 1881142 4235957 := bbase (se 5 (by rfl) ⟨198560, by rfl⟩ : syracuseStep 4235957 = 397121) (by norm_num)
theorem B2679485 : Blo 1881142 2679485 := bbase (se 3 (by rfl) ⟨502403, by rfl⟩ : syracuseStep 2679485 = 1004807) (by norm_num)
theorem B4522709 : Blo 1881142 4522709 := bbase (se 7 (by rfl) ⟨53000, by rfl⟩ : syracuseStep 4522709 = 106001) (by norm_num)
theorem B4236029 : Blo 1881142 4236029 := bbase (se 3 (by rfl) ⟨794255, by rfl⟩ : syracuseStep 4236029 = 1588511) (by norm_num)
theorem B5088005 : Blo 1881142 5088005 := bbase (se 4 (by rfl) ⟨477000, by rfl⟩ : syracuseStep 5088005 = 954001) (by norm_num)
theorem B6349589 : Blo 1881142 6349589 := bbase (se 6 (by rfl) ⟨148818, by rfl⟩ : syracuseStep 6349589 = 297637) (by norm_num)
theorem B8037157 : Blo 1881142 8037157 := bbase (se 4 (by rfl) ⟨753483, by rfl⟩ : syracuseStep 8037157 = 1506967) (by norm_num)
theorem B2147113 : Blo 1881142 2147113 := bbase (se 2 (by rfl) ⟨805167, by rfl⟩ : syracuseStep 2147113 = 1610335) (by norm_num)
theorem B3572525 : Blo 1881142 3572525 := bbase (se 3 (by rfl) ⟨669848, by rfl⟩ : syracuseStep 3572525 = 1339697) (by norm_num)
theorem B4236101 : Blo 1881142 4236101 := bbase (se 4 (by rfl) ⟨397134, by rfl⟩ : syracuseStep 4236101 = 794269) (by norm_num)
theorem B4522853 : Blo 1881142 4522853 := bbase (se 4 (by rfl) ⟨424017, by rfl⟩ : syracuseStep 4522853 = 848035) (by norm_num)
theorem B5358469 : Blo 1881142 5358469 := bbase (se 4 (by rfl) ⟨502356, by rfl⟩ : syracuseStep 5358469 = 1004713) (by norm_num)
theorem B5088133 : Blo 1881142 5088133 := bbase (se 4 (by rfl) ⟨477012, by rfl⟩ : syracuseStep 5088133 = 954025) (by norm_num)
theorem B4236173 : Blo 1881142 4236173 := bbase (se 3 (by rfl) ⟨794282, by rfl⟩ : syracuseStep 4236173 = 1588565) (by norm_num)
theorem B3572677 : Blo 1881142 3572677 := bbase (se 4 (by rfl) ⟨334938, by rfl⟩ : syracuseStep 3572677 = 669877) (by norm_num)
theorem B4236245 : Blo 1881142 4236245 := bbase (se 7 (by rfl) ⟨49643, by rfl⟩ : syracuseStep 4236245 = 99287) (by norm_num)
theorem B3621877 : Blo 1881142 3621877 := bbase (se 5 (by rfl) ⟨169775, by rfl⟩ : syracuseStep 3621877 = 339551) (by norm_num)
theorem B3015677 : Blo 1881142 3015677 := bbase (se 3 (by rfl) ⟨565439, by rfl⟩ : syracuseStep 3015677 = 1130879) (by norm_num)
theorem B4293661 : Blo 1881142 4293661 := bbase (se 3 (by rfl) ⟨805061, by rfl⟩ : syracuseStep 4293661 = 1610123) (by norm_num)
theorem B4236317 : Blo 1881142 4236317 := bbase (se 3 (by rfl) ⟨794309, by rfl⟩ : syracuseStep 4236317 = 1588619) (by norm_num)
theorem B5358629 : Blo 1881142 5358629 := bbase (se 4 (by rfl) ⟨502371, by rfl⟩ : syracuseStep 5358629 = 1004743) (by norm_num)
theorem B4523093 : Blo 1881142 4523093 := bbase (se 8 (by rfl) ⟨26502, by rfl⟩ : syracuseStep 4523093 = 53005) (by norm_num)
theorem B4236389 : Blo 1881142 4236389 := bbase (se 4 (by rfl) ⟨397161, by rfl⟩ : syracuseStep 4236389 = 794323) (by norm_num)
theorem B2147429 : Blo 1881142 2147429 := bbase (se 4 (by rfl) ⟨201321, by rfl⟩ : syracuseStep 2147429 = 402643) (by norm_num)
theorem B10724501 : Blo 1881142 10724501 := bbase (se 6 (by rfl) ⟨251355, by rfl⟩ : syracuseStep 10724501 = 502711) (by norm_num)
theorem B6784165 : Blo 1881142 6784165 := bbase (se 4 (by rfl) ⟨636015, by rfl⟩ : syracuseStep 6784165 = 1272031) (by norm_num)
theorem B4236461 : Blo 1881142 4236461 := bbase (se 3 (by rfl) ⟨794336, by rfl⟩ : syracuseStep 4236461 = 1588673) (by norm_num)
theorem B6350021 : Blo 1881142 6350021 := bbase (se 4 (by rfl) ⟨595314, by rfl⟩ : syracuseStep 6350021 = 1190629) (by norm_num)
theorem B3572981 : Blo 1881142 3572981 := bbase (se 5 (by rfl) ⟨167483, by rfl⟩ : syracuseStep 3572981 = 334967) (by norm_num)
theorem B4236533 : Blo 1881142 4236533 := bbase (se 5 (by rfl) ⟨198587, by rfl⟩ : syracuseStep 4236533 = 397175) (by norm_num)
theorem B2262277 : Blo 1881142 2262277 := bbase (se 4 (by rfl) ⟨212088, by rfl⟩ : syracuseStep 2262277 = 424177) (by norm_num)
theorem B5358869 : Blo 1881142 5358869 := bbase (se 6 (by rfl) ⟨125598, by rfl⟩ : syracuseStep 5358869 = 251197) (by norm_num)
theorem B4236605 : Blo 1881142 4236605 := bbase (se 3 (by rfl) ⟨794363, by rfl⟩ : syracuseStep 4236605 = 1588727) (by norm_num)
theorem B5432645 : Blo 1881142 5432645 := bbase (se 4 (by rfl) ⟨509310, by rfl⟩ : syracuseStep 5432645 = 1018621) (by norm_num)
theorem B9528677 : Blo 1881142 9528677 := bbase (se 4 (by rfl) ⟨893313, by rfl⟩ : syracuseStep 9528677 = 1786627) (by norm_num)
theorem B4293989 : Blo 1881142 4293989 := bbase (se 4 (by rfl) ⟨402561, by rfl⟩ : syracuseStep 4293989 = 805123) (by norm_num)
theorem B4236677 : Blo 1881142 4236677 := bbase (se 4 (by rfl) ⟨397188, by rfl⟩ : syracuseStep 4236677 = 794377) (by norm_num)
theorem B2680237 : Blo 1881142 2680237 := bbase (se 3 (by rfl) ⟨502544, by rfl⟩ : syracuseStep 2680237 = 1005089) (by norm_num)
theorem B3720629 : Blo 1881142 3720629 := bbase (se 5 (by rfl) ⟨174404, by rfl⟩ : syracuseStep 3720629 = 348809) (by norm_num)
theorem B4236749 : Blo 1881142 4236749 := bbase (se 3 (by rfl) ⟨794390, by rfl⟩ : syracuseStep 4236749 = 1588781) (by norm_num)
theorem B5359061 : Blo 1881142 5359061 := bbase (se 7 (by rfl) ⟨62801, by rfl⟩ : syracuseStep 5359061 = 125603) (by norm_num)
theorem B8037893 : Blo 1881142 8037893 := bbase (se 4 (by rfl) ⟨753552, by rfl⟩ : syracuseStep 8037893 = 1507105) (by norm_num)
theorem B4236821 : Blo 1881142 4236821 := bbase (se 6 (by rfl) ⟨99300, by rfl⟩ : syracuseStep 4236821 = 198601) (by norm_num)
theorem B14296661 : Blo 1881142 14296661 := bbase (se 8 (by rfl) ⟨83769, by rfl⟩ : syracuseStep 14296661 = 167539) (by norm_num)
theorem B4236893 : Blo 1881142 4236893 := bbase (se 3 (by rfl) ⟨794417, by rfl⟩ : syracuseStep 4236893 = 1588835) (by norm_num)
theorem B6350453 : Blo 1881142 6350453 := bbase (se 5 (by rfl) ⟨297677, by rfl⟩ : syracuseStep 6350453 = 595355) (by norm_num)
theorem B4236965 : Blo 1881142 4236965 := bbase (se 4 (by rfl) ⟨397215, by rfl⟩ : syracuseStep 4236965 = 794431) (by norm_num)
theorem B4237037 : Blo 1881142 4237037 := bbase (se 3 (by rfl) ⟨794444, by rfl⟩ : syracuseStep 4237037 = 1588889) (by norm_num)
theorem B2008837 : Blo 1881142 2008837 := bbase (se 4 (by rfl) ⟨188328, by rfl⟩ : syracuseStep 2008837 = 376657) (by norm_num)
theorem B15255317 : Blo 1881142 15255317 := bbase (se 6 (by rfl) ⟨357546, by rfl⟩ : syracuseStep 15255317 = 715093) (by norm_num)
theorem B4523861 : Blo 1881142 4523861 := bbase (se 9 (by rfl) ⟨13253, by rfl⟩ : syracuseStep 4523861 = 26507) (by norm_num)
theorem B9045877 : Blo 1881142 9045877 := bbase (se 5 (by rfl) ⟨424025, by rfl⟩ : syracuseStep 9045877 = 848051) (by norm_num)
theorem B2860957 : Blo 1881142 2860957 := bbase (se 3 (by rfl) ⟨536429, by rfl⟩ : syracuseStep 2860957 = 1072859) (by norm_num)
theorem B3573733 : Blo 1881142 3573733 := bbase (se 4 (by rfl) ⟨335037, by rfl⟩ : syracuseStep 3573733 = 670075) (by norm_num)
theorem B14288885 : Blo 1881142 14288885 := bbase (se 5 (by rfl) ⟨669791, by rfl⟩ : syracuseStep 14288885 = 1339583) (by norm_num)
theorem B6350885 : Blo 1881142 6350885 := bbase (se 4 (by rfl) ⟨595395, by rfl⟩ : syracuseStep 6350885 = 1190791) (by norm_num)
theorem B3573877 : Blo 1881142 3573877 := bbase (se 5 (by rfl) ⟨167525, by rfl⟩ : syracuseStep 3573877 = 335051) (by norm_num)
theorem B2009281 : Blo 1881142 2009281 := bbase (se 2 (by rfl) ⟨753480, by rfl⟩ : syracuseStep 2009281 = 1506961) (by norm_num)
theorem B2681029 : Blo 1881142 2681029 := bbase (se 4 (by rfl) ⟨251346, by rfl⟩ : syracuseStep 2681029 = 502693) (by norm_num)
theorem B2861261 : Blo 1881142 2861261 := bbase (se 3 (by rfl) ⟨536486, by rfl⟩ : syracuseStep 2861261 = 1072973) (by norm_num)
theorem B5802197 : Blo 1881142 5802197 := bbase (se 7 (by rfl) ⟨67994, by rfl⟩ : syracuseStep 5802197 = 135989) (by norm_num)
theorem B3574037 : Blo 1881142 3574037 := bbase (se 6 (by rfl) ⟨83766, by rfl⟩ : syracuseStep 3574037 = 167533) (by norm_num)
theorem B7145765 : Blo 1881142 7145765 := bbase (se 4 (by rfl) ⟨669915, by rfl⟩ : syracuseStep 7145765 = 1339831) (by norm_num)
theorem B2009405 : Blo 1881142 2009405 := bbase (se 3 (by rfl) ⟨376763, by rfl⟩ : syracuseStep 2009405 = 753527) (by norm_num)
theorem B4761949 : Blo 1881142 4761949 := bbase (se 3 (by rfl) ⟨892865, by rfl⟩ : syracuseStep 4761949 = 1785731) (by norm_num)
theorem B3574181 : Blo 1881142 3574181 := bbase (se 4 (by rfl) ⟨335079, by rfl⟩ : syracuseStep 3574181 = 670159) (by norm_num)
theorem B5360053 : Blo 1881142 5360053 := bbase (se 5 (by rfl) ⟨251252, by rfl⟩ : syracuseStep 5360053 = 502505) (by norm_num)
theorem B6785477 : Blo 1881142 6785477 := bbase (se 4 (by rfl) ⟨636138, by rfl⟩ : syracuseStep 6785477 = 1272277) (by norm_num)
theorem B4762061 : Blo 1881142 4762061 := bbase (se 3 (by rfl) ⟨892886, by rfl⟩ : syracuseStep 4762061 = 1785773) (by norm_num)
theorem B6351317 : Blo 1881142 6351317 := bbase (se 7 (by rfl) ⟨74429, by rfl⟩ : syracuseStep 6351317 = 148859) (by norm_num)
theorem B11446741 : Blo 1881142 11446741 := bbase (se 7 (by rfl) ⟨134141, by rfl⟩ : syracuseStep 11446741 = 268283) (by norm_num)
theorem B2009657 : Blo 1881142 2009657 := bbase (se 2 (by rfl) ⟨753621, by rfl⟩ : syracuseStep 2009657 = 1507243) (by norm_num)
theorem B7146053 : Blo 1881142 7146053 := bbase (se 4 (by rfl) ⟨669942, by rfl⟩ : syracuseStep 7146053 = 1339885) (by norm_num)
theorem B3623501 : Blo 1881142 3623501 := bbase (se 3 (by rfl) ⟨679406, by rfl⟩ : syracuseStep 3623501 = 1358813) (by norm_num)
theorem B9529973 : Blo 1881142 9529973 := bbase (se 5 (by rfl) ⟨446717, by rfl⟩ : syracuseStep 9529973 = 893435) (by norm_num)
theorem B4762253 : Blo 1881142 4762253 := bbase (se 3 (by rfl) ⟨892922, by rfl⟩ : syracuseStep 4762253 = 1785845) (by norm_num)
theorem B3574469 : Blo 1881142 3574469 := bbase (se 4 (by rfl) ⟨335106, by rfl⟩ : syracuseStep 3574469 = 670213) (by norm_num)
theorem B2116309 : Blo 1881142 2116309 := bbase (se 7 (by rfl) ⟨24800, by rfl⟩ : syracuseStep 2116309 = 49601) (by norm_num)
theorem B2116345 : Blo 1881142 2116345 := bbase (se 2 (by rfl) ⟨793629, by rfl⟩ : syracuseStep 2116345 = 1587259) (by norm_num)
theorem B2116381 : Blo 1881142 2116381 := bbase (se 3 (by rfl) ⟨396821, by rfl⟩ : syracuseStep 2116381 = 793643) (by norm_num)
theorem B7629605 : Blo 1881142 7629605 := bbase (se 4 (by rfl) ⟨715275, by rfl⟩ : syracuseStep 7629605 = 1430551) (by norm_num)
theorem B2116417 : Blo 1881142 2116417 := bbase (se 2 (by rfl) ⟨793656, by rfl⟩ : syracuseStep 2116417 = 1587313) (by norm_num)
theorem B3574621 : Blo 1881142 3574621 := bbase (se 3 (by rfl) ⟨670241, by rfl⟩ : syracuseStep 3574621 = 1340483) (by norm_num)
theorem B2116453 : Blo 1881142 2116453 := bbase (se 4 (by rfl) ⟨198417, by rfl⟩ : syracuseStep 2116453 = 396835) (by norm_num)
theorem B4582253 : Blo 1881142 4582253 := bbase (se 3 (by rfl) ⟨859172, by rfl⟩ : syracuseStep 4582253 = 1718345) (by norm_num)
theorem B6351749 : Blo 1881142 6351749 := bbase (se 4 (by rfl) ⟨595476, by rfl⟩ : syracuseStep 6351749 = 1190953) (by norm_num)
theorem B2116489 : Blo 1881142 2116489 := bbase (se 2 (by rfl) ⟨793683, by rfl⟩ : syracuseStep 2116489 = 1587367) (by norm_num)
theorem B2116525 : Blo 1881142 2116525 := bbase (se 3 (by rfl) ⟨396848, by rfl⟩ : syracuseStep 2116525 = 793697) (by norm_num)
theorem B2116561 : Blo 1881142 2116561 := bbase (se 2 (by rfl) ⟨793710, by rfl⟩ : syracuseStep 2116561 = 1587421) (by norm_num)
theorem B4762597 : Blo 1881142 4762597 := bbase (se 4 (by rfl) ⟨446493, by rfl⟩ : syracuseStep 4762597 = 892987) (by norm_num)
theorem B2116597 : Blo 1881142 2116597 := bbase (se 5 (by rfl) ⟨99215, by rfl⟩ : syracuseStep 2116597 = 198431) (by norm_num)
theorem B2010101 : Blo 1881142 2010101 := bbase (se 5 (by rfl) ⟨94223, by rfl⟩ : syracuseStep 2010101 = 188447) (by norm_num)
theorem B2116633 : Blo 1881142 2116633 := bbase (se 2 (by rfl) ⟨793737, by rfl⟩ : syracuseStep 2116633 = 1587475) (by norm_num)
theorem B2116669 : Blo 1881142 2116669 := bbase (se 3 (by rfl) ⟨396875, by rfl⟩ : syracuseStep 2116669 = 793751) (by norm_num)
theorem B4762709 : Blo 1881142 4762709 := bbase (se 8 (by rfl) ⟨27906, by rfl⟩ : syracuseStep 4762709 = 55813) (by norm_num)
theorem B2116705 : Blo 1881142 2116705 := bbase (se 2 (by rfl) ⟨793764, by rfl⟩ : syracuseStep 2116705 = 1587529) (by norm_num)
theorem B2116741 : Blo 1881142 2116741 := bbase (se 4 (by rfl) ⟨198444, by rfl⟩ : syracuseStep 2116741 = 396889) (by norm_num)
theorem B3574925 : Blo 1881142 3574925 := bbase (se 3 (by rfl) ⟨670298, by rfl⟩ : syracuseStep 3574925 = 1340597) (by norm_num)
theorem B2116777 : Blo 1881142 2116777 := bbase (se 2 (by rfl) ⟨793791, by rfl⟩ : syracuseStep 2116777 = 1587583) (by norm_num)
theorem B2116813 : Blo 1881142 2116813 := bbase (se 3 (by rfl) ⟨396902, by rfl⟩ : syracuseStep 2116813 = 793805) (by norm_num)
theorem B2010349 : Blo 1881142 2010349 := bbase (se 3 (by rfl) ⟨376940, by rfl⟩ : syracuseStep 2010349 = 753881) (by norm_num)
theorem B2116849 : Blo 1881142 2116849 := bbase (se 2 (by rfl) ⟨793818, by rfl⟩ : syracuseStep 2116849 = 1587637) (by norm_num)
theorem B4762901 : Blo 1881142 4762901 := bbase (se 6 (by rfl) ⟨111630, by rfl⟩ : syracuseStep 4762901 = 223261) (by norm_num)
theorem B2116885 : Blo 1881142 2116885 := bbase (se 6 (by rfl) ⟨49614, by rfl⟩ : syracuseStep 2116885 = 99229) (by norm_num)
theorem B6352181 : Blo 1881142 6352181 := bbase (se 5 (by rfl) ⟨297758, by rfl⟩ : syracuseStep 6352181 = 595517) (by norm_num)
theorem B2116921 : Blo 1881142 2116921 := bbase (se 2 (by rfl) ⟨793845, by rfl⟩ : syracuseStep 2116921 = 1587691) (by norm_num)
theorem B2116957 : Blo 1881142 2116957 := bbase (se 3 (by rfl) ⟨396929, by rfl⟩ : syracuseStep 2116957 = 793859) (by norm_num)
theorem B2116993 : Blo 1881142 2116993 := bbase (se 2 (by rfl) ⟨793872, by rfl⟩ : syracuseStep 2116993 = 1587745) (by norm_num)
theorem B6032789 : Blo 1881142 6032789 := bbase (se 6 (by rfl) ⟨141393, by rfl⟩ : syracuseStep 6032789 = 282787) (by norm_num)
theorem B2117029 : Blo 1881142 2117029 := bbase (se 4 (by rfl) ⟨198471, by rfl⟩ : syracuseStep 2117029 = 396943) (by norm_num)
theorem B2117065 : Blo 1881142 2117065 := bbase (se 2 (by rfl) ⟨793899, by rfl⟩ : syracuseStep 2117065 = 1587799) (by norm_num)
theorem B2117101 : Blo 1881142 2117101 := bbase (se 3 (by rfl) ⟨396956, by rfl⟩ : syracuseStep 2117101 = 793913) (by norm_num)
theorem B5361157 : Blo 1881142 5361157 := bbase (se 4 (by rfl) ⟨502608, by rfl⟩ : syracuseStep 5361157 = 1005217) (by norm_num)
theorem B2117137 : Blo 1881142 2117137 := bbase (se 2 (by rfl) ⟨793926, by rfl⟩ : syracuseStep 2117137 = 1587853) (by norm_num)
theorem B2117173 : Blo 1881142 2117173 := bbase (se 5 (by rfl) ⟨99242, by rfl⟩ : syracuseStep 2117173 = 198485) (by norm_num)
theorem B10317365 : Blo 1881142 10317365 := bbase (se 5 (by rfl) ⟨483626, by rfl⟩ : syracuseStep 10317365 = 967253) (by norm_num)
theorem B16084565 : Blo 1881142 16084565 := bbase (se 8 (by rfl) ⟨94245, by rfl⟩ : syracuseStep 16084565 = 188491) (by norm_num)
theorem B2117209 : Blo 1881142 2117209 := bbase (se 2 (by rfl) ⟨793953, by rfl⟩ : syracuseStep 2117209 = 1587907) (by norm_num)
theorem B2821733 : Blo 1881142 2821733 := bbase (se 4 (by rfl) ⟨264537, by rfl⟩ : syracuseStep 2821733 = 529075) (by norm_num)
theorem B4763245 : Blo 1881142 4763245 := bbase (se 3 (by rfl) ⟨893108, by rfl⟩ : syracuseStep 4763245 = 1786217) (by norm_num)
theorem B2821757 : Blo 1881142 2821757 := bbase (se 3 (by rfl) ⟨529079, by rfl⟩ : syracuseStep 2821757 = 1058159) (by norm_num)
theorem B2117245 : Blo 1881142 2117245 := bbase (se 3 (by rfl) ⟨396983, by rfl⟩ : syracuseStep 2117245 = 793967) (by norm_num)
theorem B2821781 : Blo 1881142 2821781 := bbase (se 6 (by rfl) ⟨66135, by rfl⟩ : syracuseStep 2821781 = 132271) (by norm_num)
theorem B2117281 : Blo 1881142 2117281 := bbase (se 2 (by rfl) ⟨793980, by rfl⟩ : syracuseStep 2117281 = 1587961) (by norm_num)
theorem B2010793 : Blo 1881142 2010793 := bbase (se 2 (by rfl) ⟨754047, by rfl⟩ : syracuseStep 2010793 = 1508095) (by norm_num)
theorem B2821805 : Blo 1881142 2821805 := bbase (se 3 (by rfl) ⟨529088, by rfl⟩ : syracuseStep 2821805 = 1058177) (by norm_num)
theorem B12054197 : Blo 1881142 12054197 := bbase (se 5 (by rfl) ⟨565040, by rfl⟩ : syracuseStep 12054197 = 1130081) (by norm_num)
theorem B4017853 : Blo 1881142 4017853 := bbase (se 3 (by rfl) ⟨753347, by rfl⟩ : syracuseStep 4017853 = 1506695) (by norm_num)
theorem B2821829 : Blo 1881142 2821829 := bbase (se 4 (by rfl) ⟨264546, by rfl⟩ : syracuseStep 2821829 = 529093) (by norm_num)
theorem B2117317 : Blo 1881142 2117317 := bbase (se 4 (by rfl) ⟨198498, by rfl⟩ : syracuseStep 2117317 = 396997) (by norm_num)
theorem B16076501 : Blo 1881142 16076501 := bbase (se 7 (by rfl) ⟨188396, by rfl⟩ : syracuseStep 16076501 = 376793) (by norm_num)
theorem B2821853 : Blo 1881142 2821853 := bbase (se 3 (by rfl) ⟨529097, by rfl⟩ : syracuseStep 2821853 = 1058195) (by norm_num)
theorem B4763357 : Blo 1881142 4763357 := bbase (se 3 (by rfl) ⟨893129, by rfl⟩ : syracuseStep 4763357 = 1786259) (by norm_num)
theorem B6352613 : Blo 1881142 6352613 := bbase (se 4 (by rfl) ⟨595557, by rfl⟩ : syracuseStep 6352613 = 1191115) (by norm_num)
theorem B7147237 : Blo 1881142 7147237 := bbase (se 4 (by rfl) ⟨670053, by rfl⟩ : syracuseStep 7147237 = 1340107) (by norm_num)
theorem B2010853 : Blo 1881142 2010853 := bbase (se 4 (by rfl) ⟨188517, by rfl⟩ : syracuseStep 2010853 = 377035) (by norm_num)
theorem B2117353 : Blo 1881142 2117353 := bbase (se 2 (by rfl) ⟨794007, by rfl⟩ : syracuseStep 2117353 = 1588015) (by norm_num)
theorem B2821877 : Blo 1881142 2821877 := bbase (se 5 (by rfl) ⟨132275, by rfl⟩ : syracuseStep 2821877 = 264551) (by norm_num)
theorem B2821901 : Blo 1881142 2821901 := bbase (se 3 (by rfl) ⟨529106, by rfl⟩ : syracuseStep 2821901 = 1058213) (by norm_num)
theorem B2117389 : Blo 1881142 2117389 := bbase (se 3 (by rfl) ⟨397010, by rfl⟩ : syracuseStep 2117389 = 794021) (by norm_num)
theorem B2821925 : Blo 1881142 2821925 := bbase (se 4 (by rfl) ⟨264555, by rfl⟩ : syracuseStep 2821925 = 529111) (by norm_num)
theorem B2117425 : Blo 1881142 2117425 := bbase (se 2 (by rfl) ⟨794034, by rfl⟩ : syracuseStep 2117425 = 1588069) (by norm_num)
theorem B2821949 : Blo 1881142 2821949 := bbase (se 3 (by rfl) ⟨529115, by rfl⟩ : syracuseStep 2821949 = 1058231) (by norm_num)
theorem B2821973 : Blo 1881142 2821973 := bbase (se 9 (by rfl) ⟨8267, by rfl⟩ : syracuseStep 2821973 = 16535) (by norm_num)
theorem B2117461 : Blo 1881142 2117461 := bbase (se 9 (by rfl) ⟨6203, by rfl⟩ : syracuseStep 2117461 = 12407) (by norm_num)
theorem B2821997 : Blo 1881142 2821997 := bbase (se 3 (by rfl) ⟨529124, by rfl⟩ : syracuseStep 2821997 = 1058249) (by norm_num)
theorem B2117497 : Blo 1881142 2117497 := bbase (se 2 (by rfl) ⟨794061, by rfl⟩ : syracuseStep 2117497 = 1588123) (by norm_num)
theorem B2822021 : Blo 1881142 2822021 := bbase (se 4 (by rfl) ⟨264564, by rfl⟩ : syracuseStep 2822021 = 529129) (by norm_num)
theorem B9531269 : Blo 1881142 9531269 := bbase (se 4 (by rfl) ⟨893556, by rfl⟩ : syracuseStep 9531269 = 1787113) (by norm_num)
theorem B10719125 : Blo 1881142 10719125 := bbase (se 6 (by rfl) ⟨251229, by rfl⟩ : syracuseStep 10719125 = 502459) (by norm_num)
theorem B2822045 : Blo 1881142 2822045 := bbase (se 3 (by rfl) ⟨529133, by rfl⟩ : syracuseStep 2822045 = 1058267) (by norm_num)
theorem B4763549 : Blo 1881142 4763549 := bbase (se 3 (by rfl) ⟨893165, by rfl⟩ : syracuseStep 4763549 = 1786331) (by norm_num)
theorem B2117533 : Blo 1881142 2117533 := bbase (se 3 (by rfl) ⟨397037, by rfl⟩ : syracuseStep 2117533 = 794075) (by norm_num)
theorem B2822069 : Blo 1881142 2822069 := bbase (se 5 (by rfl) ⟨132284, by rfl⟩ : syracuseStep 2822069 = 264569) (by norm_num)
theorem B2117569 : Blo 1881142 2117569 := bbase (se 2 (by rfl) ⟨794088, by rfl⟩ : syracuseStep 2117569 = 1588177) (by norm_num)
theorem B2822093 : Blo 1881142 2822093 := bbase (se 3 (by rfl) ⟨529142, by rfl⟩ : syracuseStep 2822093 = 1058285) (by norm_num)
theorem B2822117 : Blo 1881142 2822117 := bbase (se 4 (by rfl) ⟨264573, by rfl⟩ : syracuseStep 2822117 = 529147) (by norm_num)
theorem B2117605 : Blo 1881142 2117605 := bbase (se 4 (by rfl) ⟨198525, by rfl⟩ : syracuseStep 2117605 = 397051) (by norm_num)
theorem B2822141 : Blo 1881142 2822141 := bbase (se 3 (by rfl) ⟨529151, by rfl⟩ : syracuseStep 2822141 = 1058303) (by norm_num)
theorem B2117641 : Blo 1881142 2117641 := bbase (se 2 (by rfl) ⟨794115, by rfl⟩ : syracuseStep 2117641 = 1588231) (by norm_num)
theorem B2822165 : Blo 1881142 2822165 := bbase (se 6 (by rfl) ⟨66144, by rfl⟩ : syracuseStep 2822165 = 132289) (by norm_num)
theorem B7147541 : Blo 1881142 7147541 := bbase (se 6 (by rfl) ⟨167520, by rfl⟩ : syracuseStep 7147541 = 335041) (by norm_num)
theorem B3174437 : Blo 1881142 3174437 := bbase (se 4 (by rfl) ⟨297603, by rfl⟩ : syracuseStep 3174437 = 595207) (by norm_num)
theorem B2822189 : Blo 1881142 2822189 := bbase (se 3 (by rfl) ⟨529160, by rfl⟩ : syracuseStep 2822189 = 1058321) (by norm_num)
theorem B2117677 : Blo 1881142 2117677 := bbase (se 3 (by rfl) ⟨397064, by rfl⟩ : syracuseStep 2117677 = 794129) (by norm_num)
theorem B2822213 : Blo 1881142 2822213 := bbase (se 4 (by rfl) ⟨264582, by rfl⟩ : syracuseStep 2822213 = 529165) (by norm_num)
theorem B2117713 : Blo 1881142 2117713 := bbase (se 2 (by rfl) ⟨794142, by rfl⟩ : syracuseStep 2117713 = 1588285) (by norm_num)
theorem B2822237 : Blo 1881142 2822237 := bbase (se 3 (by rfl) ⟨529169, by rfl⟩ : syracuseStep 2822237 = 1058339) (by norm_num)
theorem B2822261 : Blo 1881142 2822261 := bbase (se 5 (by rfl) ⟨132293, by rfl⟩ : syracuseStep 2822261 = 264587) (by norm_num)
theorem B2117749 : Blo 1881142 2117749 := bbase (se 5 (by rfl) ⟨99269, by rfl⟩ : syracuseStep 2117749 = 198539) (by norm_num)
theorem B2822285 : Blo 1881142 2822285 := bbase (se 3 (by rfl) ⟨529178, by rfl⟩ : syracuseStep 2822285 = 1058357) (by norm_num)
theorem B6353045 : Blo 1881142 6353045 := bbase (se 6 (by rfl) ⟨148899, by rfl⟩ : syracuseStep 6353045 = 297799) (by norm_num)
theorem B2117785 : Blo 1881142 2117785 := bbase (se 2 (by rfl) ⟨794169, by rfl⟩ : syracuseStep 2117785 = 1588339) (by norm_num)
theorem B3174565 : Blo 1881142 3174565 := bbase (se 4 (by rfl) ⟨297615, by rfl⟩ : syracuseStep 3174565 = 595231) (by norm_num)
theorem B2822309 : Blo 1881142 2822309 := bbase (se 4 (by rfl) ⟨264591, by rfl⟩ : syracuseStep 2822309 = 529183) (by norm_num)
theorem B2822333 : Blo 1881142 2822333 := bbase (se 3 (by rfl) ⟨529187, by rfl⟩ : syracuseStep 2822333 = 1058375) (by norm_num)
theorem B2117821 : Blo 1881142 2117821 := bbase (se 3 (by rfl) ⟨397091, by rfl⟩ : syracuseStep 2117821 = 794183) (by norm_num)
theorem B2822357 : Blo 1881142 2822357 := bbase (se 7 (by rfl) ⟨33074, by rfl⟩ : syracuseStep 2822357 = 66149) (by norm_num)
theorem B2117857 : Blo 1881142 2117857 := bbase (se 2 (by rfl) ⟨794196, by rfl⟩ : syracuseStep 2117857 = 1588393) (by norm_num)
theorem B2822381 : Blo 1881142 2822381 := bbase (se 3 (by rfl) ⟨529196, by rfl⟩ : syracuseStep 2822381 = 1058393) (by norm_num)
theorem B4763893 : Blo 1881142 4763893 := bbase (se 5 (by rfl) ⟨223307, by rfl⟩ : syracuseStep 4763893 = 446615) (by norm_num)
theorem B3174653 : Blo 1881142 3174653 := bbase (se 3 (by rfl) ⟨595247, by rfl⟩ : syracuseStep 3174653 = 1190495) (by norm_num)
theorem B2822405 : Blo 1881142 2822405 := bbase (se 4 (by rfl) ⟨264600, by rfl⟩ : syracuseStep 2822405 = 529201) (by norm_num)
theorem B2117893 : Blo 1881142 2117893 := bbase (se 4 (by rfl) ⟨198552, by rfl⟩ : syracuseStep 2117893 = 397105) (by norm_num)
theorem B2822429 : Blo 1881142 2822429 := bbase (se 3 (by rfl) ⟨529205, by rfl⟩ : syracuseStep 2822429 = 1058411) (by norm_num)
theorem B9523493 : Blo 1881142 9523493 := bbase (se 4 (by rfl) ⟨892827, by rfl⟩ : syracuseStep 9523493 = 1785655) (by norm_num)
theorem B2117929 : Blo 1881142 2117929 := bbase (se 2 (by rfl) ⟨794223, by rfl⟩ : syracuseStep 2117929 = 1588447) (by norm_num)
theorem B2822453 : Blo 1881142 2822453 := bbase (se 5 (by rfl) ⟨132302, by rfl⟩ : syracuseStep 2822453 = 264605) (by norm_num)
theorem B2822477 : Blo 1881142 2822477 := bbase (se 3 (by rfl) ⟨529214, by rfl⟩ : syracuseStep 2822477 = 1058429) (by norm_num)
theorem B2117965 : Blo 1881142 2117965 := bbase (se 3 (by rfl) ⟨397118, by rfl⟩ : syracuseStep 2117965 = 794237) (by norm_num)
theorem B2715997 : Blo 1881142 2715997 := bbase (se 3 (by rfl) ⟨509249, by rfl⟩ : syracuseStep 2715997 = 1018499) (by norm_num)
theorem B3813733 : Blo 1881142 3813733 := bbase (se 4 (by rfl) ⟨357537, by rfl⟩ : syracuseStep 3813733 = 715075) (by norm_num)
theorem B2822501 : Blo 1881142 2822501 := bbase (se 4 (by rfl) ⟨264609, by rfl⟩ : syracuseStep 2822501 = 529219) (by norm_num)
theorem B4764005 : Blo 1881142 4764005 := bbase (se 4 (by rfl) ⟨446625, by rfl⟩ : syracuseStep 4764005 = 893251) (by norm_num)
theorem B2118001 : Blo 1881142 2118001 := bbase (se 2 (by rfl) ⟨794250, by rfl⟩ : syracuseStep 2118001 = 1588501) (by norm_num)
theorem B3174781 : Blo 1881142 3174781 := bbase (se 3 (by rfl) ⟨595271, by rfl⟩ : syracuseStep 3174781 = 1190543) (by norm_num)
theorem B2822525 : Blo 1881142 2822525 := bbase (se 3 (by rfl) ⟨529223, by rfl⟩ : syracuseStep 2822525 = 1058447) (by norm_num)
theorem B2822549 : Blo 1881142 2822549 := bbase (se 6 (by rfl) ⟨66153, by rfl⟩ : syracuseStep 2822549 = 132307) (by norm_num)
theorem B2118037 : Blo 1881142 2118037 := bbase (se 6 (by rfl) ⟨49641, by rfl⟩ : syracuseStep 2118037 = 99283) (by norm_num)
theorem B2822573 : Blo 1881142 2822573 := bbase (se 3 (by rfl) ⟨529232, by rfl⟩ : syracuseStep 2822573 = 1058465) (by norm_num)
theorem B2118073 : Blo 1881142 2118073 := bbase (se 2 (by rfl) ⟨794277, by rfl⟩ : syracuseStep 2118073 = 1588555) (by norm_num)
theorem B2822597 : Blo 1881142 2822597 := bbase (se 4 (by rfl) ⟨264618, by rfl⟩ : syracuseStep 2822597 = 529237) (by norm_num)
theorem B3174869 : Blo 1881142 3174869 := bbase (se 7 (by rfl) ⟨37205, by rfl⟩ : syracuseStep 3174869 = 74411) (by norm_num)
theorem B2822621 : Blo 1881142 2822621 := bbase (se 3 (by rfl) ⟨529241, by rfl⟩ : syracuseStep 2822621 = 1058483) (by norm_num)
theorem B2118109 : Blo 1881142 2118109 := bbase (se 3 (by rfl) ⟨397145, by rfl⟩ : syracuseStep 2118109 = 794291) (by norm_num)
theorem B2822645 : Blo 1881142 2822645 := bbase (se 5 (by rfl) ⟨132311, by rfl⟩ : syracuseStep 2822645 = 264623) (by norm_num)
theorem B2118145 : Blo 1881142 2118145 := bbase (se 2 (by rfl) ⟨794304, by rfl⟩ : syracuseStep 2118145 = 1588609) (by norm_num)
theorem B2822669 : Blo 1881142 2822669 := bbase (se 3 (by rfl) ⟨529250, by rfl⟩ : syracuseStep 2822669 = 1058501) (by norm_num)
theorem B2822693 : Blo 1881142 2822693 := bbase (se 4 (by rfl) ⟨264627, by rfl⟩ : syracuseStep 2822693 = 529255) (by norm_num)
theorem B4764197 : Blo 1881142 4764197 := bbase (se 4 (by rfl) ⟨446643, by rfl⟩ : syracuseStep 4764197 = 893287) (by norm_num)
theorem B2118181 : Blo 1881142 2118181 := bbase (se 4 (by rfl) ⟨198579, by rfl⟩ : syracuseStep 2118181 = 397159) (by norm_num)
theorem B2822717 : Blo 1881142 2822717 := bbase (se 3 (by rfl) ⟨529259, by rfl⟩ : syracuseStep 2822717 = 1058519) (by norm_num)
theorem B6353477 : Blo 1881142 6353477 := bbase (se 4 (by rfl) ⟨595638, by rfl⟩ : syracuseStep 6353477 = 1191277) (by norm_num)
theorem B2118217 : Blo 1881142 2118217 := bbase (se 2 (by rfl) ⟨794331, by rfl⟩ : syracuseStep 2118217 = 1588663) (by norm_num)
theorem B2036305 : Blo 1881142 2036305 := bbase (se 2 (by rfl) ⟨763614, by rfl⟩ : syracuseStep 2036305 = 1527229) (by norm_num)
theorem B3174997 : Blo 1881142 3174997 := bbase (se 8 (by rfl) ⟨18603, by rfl⟩ : syracuseStep 3174997 = 37207) (by norm_num)
theorem B2822741 : Blo 1881142 2822741 := bbase (se 8 (by rfl) ⟨16539, by rfl⟩ : syracuseStep 2822741 = 33079) (by norm_num)
theorem B2822765 : Blo 1881142 2822765 := bbase (se 3 (by rfl) ⟨529268, by rfl⟩ : syracuseStep 2822765 = 1058537) (by norm_num)
theorem B2118253 : Blo 1881142 2118253 := bbase (se 3 (by rfl) ⟨397172, by rfl⟩ : syracuseStep 2118253 = 794345) (by norm_num)
theorem B2822789 : Blo 1881142 2822789 := bbase (se 4 (by rfl) ⟨264636, by rfl⟩ : syracuseStep 2822789 = 529273) (by norm_num)
theorem B2118289 : Blo 1881142 2118289 := bbase (se 2 (by rfl) ⟨794358, by rfl⟩ : syracuseStep 2118289 = 1588717) (by norm_num)
theorem B2822813 : Blo 1881142 2822813 := bbase (se 3 (by rfl) ⟨529277, by rfl⟩ : syracuseStep 2822813 = 1058555) (by norm_num)
theorem B3175085 : Blo 1881142 3175085 := bbase (se 3 (by rfl) ⟨595328, by rfl⟩ : syracuseStep 3175085 = 1190657) (by norm_num)
theorem B2822837 : Blo 1881142 2822837 := bbase (se 5 (by rfl) ⟨132320, by rfl⟩ : syracuseStep 2822837 = 264641) (by norm_num)
theorem B2118325 : Blo 1881142 2118325 := bbase (se 5 (by rfl) ⟨99296, by rfl⟩ : syracuseStep 2118325 = 198593) (by norm_num)
theorem B2822861 : Blo 1881142 2822861 := bbase (se 3 (by rfl) ⟨529286, by rfl⟩ : syracuseStep 2822861 = 1058573) (by norm_num)
theorem B2118361 : Blo 1881142 2118361 := bbase (se 2 (by rfl) ⟨794385, by rfl⟩ : syracuseStep 2118361 = 1588771) (by norm_num)
theorem B2822885 : Blo 1881142 2822885 := bbase (se 4 (by rfl) ⟨264645, by rfl⟩ : syracuseStep 2822885 = 529291) (by norm_num)
theorem B8041189 : Blo 1881142 8041189 := bbase (se 4 (by rfl) ⟨753861, by rfl⟩ : syracuseStep 8041189 = 1507723) (by norm_num)
theorem B14480117 : Blo 1881142 14480117 := bbase (se 5 (by rfl) ⟨678755, by rfl⟩ : syracuseStep 14480117 = 1357511) (by norm_num)
theorem B2822909 : Blo 1881142 2822909 := bbase (se 3 (by rfl) ⟨529295, by rfl⟩ : syracuseStep 2822909 = 1058591) (by norm_num)
theorem B2118397 : Blo 1881142 2118397 := bbase (se 3 (by rfl) ⟨397199, by rfl⟩ : syracuseStep 2118397 = 794399) (by norm_num)
theorem B2036497 : Blo 1881142 2036497 := bbase (se 2 (by rfl) ⟨763686, by rfl⟩ : syracuseStep 2036497 = 1527373) (by norm_num)
theorem B2822933 : Blo 1881142 2822933 := bbase (se 6 (by rfl) ⟨66162, by rfl⟩ : syracuseStep 2822933 = 132325) (by norm_num)
theorem B2118433 : Blo 1881142 2118433 := bbase (se 2 (by rfl) ⟨794412, by rfl⟩ : syracuseStep 2118433 = 1588825) (by norm_num)
theorem B3175213 : Blo 1881142 3175213 := bbase (se 3 (by rfl) ⟨595352, by rfl⟩ : syracuseStep 3175213 = 1190705) (by norm_num)
theorem B2822957 : Blo 1881142 2822957 := bbase (se 3 (by rfl) ⟨529304, by rfl⟩ : syracuseStep 2822957 = 1058609) (by norm_num)
theorem B2822981 : Blo 1881142 2822981 := bbase (se 4 (by rfl) ⟨264654, by rfl⟩ : syracuseStep 2822981 = 529309) (by norm_num)
theorem B2118469 : Blo 1881142 2118469 := bbase (se 4 (by rfl) ⟨198606, by rfl⟩ : syracuseStep 2118469 = 397213) (by norm_num)
theorem B2823005 : Blo 1881142 2823005 := bbase (se 3 (by rfl) ⟨529313, by rfl⟩ : syracuseStep 2823005 = 1058627) (by norm_num)
theorem B2118505 : Blo 1881142 2118505 := bbase (se 2 (by rfl) ⟨794439, by rfl⟩ : syracuseStep 2118505 = 1588879) (by norm_num)
theorem B2823029 : Blo 1881142 2823029 := bbase (se 5 (by rfl) ⟨132329, by rfl⟩ : syracuseStep 2823029 = 264659) (by norm_num)
theorem B7246709 : Blo 1881142 7246709 := bbase (se 5 (by rfl) ⟨339689, by rfl⟩ : syracuseStep 7246709 = 679379) (by norm_num)
theorem B4764541 : Blo 1881142 4764541 := bbase (se 3 (by rfl) ⟨893351, by rfl⟩ : syracuseStep 4764541 = 1786703) (by norm_num)
theorem B3175301 : Blo 1881142 3175301 := bbase (se 4 (by rfl) ⟨297684, by rfl⟩ : syracuseStep 3175301 = 595369) (by norm_num)
theorem B2823053 : Blo 1881142 2823053 := bbase (se 3 (by rfl) ⟨529322, by rfl⟩ : syracuseStep 2823053 = 1058645) (by norm_num)
theorem B2823077 : Blo 1881142 2823077 := bbase (se 4 (by rfl) ⟨264663, by rfl⟩ : syracuseStep 2823077 = 529327) (by norm_num)
theorem B2413481 : Blo 1881142 2413481 := bbase (se 2 (by rfl) ⟨905055, by rfl⟩ : syracuseStep 2413481 = 1810111) (by norm_num)
theorem B2823101 : Blo 1881142 2823101 := bbase (se 3 (by rfl) ⟨529331, by rfl⟩ : syracuseStep 2823101 = 1058663) (by norm_num)
theorem B2823125 : Blo 1881142 2823125 := bbase (se 7 (by rfl) ⟨33083, by rfl⟩ : syracuseStep 2823125 = 66167) (by norm_num)
theorem B2823149 : Blo 1881142 2823149 := bbase (se 3 (by rfl) ⟨529340, by rfl⟩ : syracuseStep 2823149 = 1058681) (by norm_num)
theorem B4764653 : Blo 1881142 4764653 := bbase (se 3 (by rfl) ⟨893372, by rfl⟩ : syracuseStep 4764653 = 1786745) (by norm_num)
theorem B6353909 : Blo 1881142 6353909 := bbase (se 5 (by rfl) ⟨297839, by rfl⟩ : syracuseStep 6353909 = 595679) (by norm_num)
theorem B3175429 : Blo 1881142 3175429 := bbase (se 4 (by rfl) ⟨297696, by rfl⟩ : syracuseStep 3175429 = 595393) (by norm_num)
theorem B2823173 : Blo 1881142 2823173 := bbase (se 4 (by rfl) ⟨264672, by rfl⟩ : syracuseStep 2823173 = 529345) (by norm_num)
theorem B2823197 : Blo 1881142 2823197 := bbase (se 3 (by rfl) ⟨529349, by rfl⟩ : syracuseStep 2823197 = 1058699) (by norm_num)
theorem B2036773 : Blo 1881142 2036773 := bbase (se 4 (by rfl) ⟨190947, by rfl⟩ : syracuseStep 2036773 = 381895) (by norm_num)
theorem B4830245 : Blo 1881142 4830245 := bbase (se 4 (by rfl) ⟨452835, by rfl⟩ : syracuseStep 4830245 = 905671) (by norm_num)
theorem B2380853 : Blo 1881142 2380853 := bbase (se 5 (by rfl) ⟨111602, by rfl⟩ : syracuseStep 2380853 = 223205) (by norm_num)
theorem B2823221 : Blo 1881142 2823221 := bbase (se 5 (by rfl) ⟨132338, by rfl⟩ : syracuseStep 2823221 = 264677) (by norm_num)
theorem B10720309 : Blo 1881142 10720309 := bbase (se 5 (by rfl) ⟨502514, by rfl⟩ : syracuseStep 10720309 = 1005029) (by norm_num)
theorem B2823245 : Blo 1881142 2823245 := bbase (se 3 (by rfl) ⟨529358, by rfl⟩ : syracuseStep 2823245 = 1058717) (by norm_num)
theorem B3175517 : Blo 1881142 3175517 := bbase (se 3 (by rfl) ⟨595409, by rfl⟩ : syracuseStep 3175517 = 1190819) (by norm_num)
theorem B9040997 : Blo 1881142 9040997 := bbase (se 4 (by rfl) ⟨847593, by rfl⟩ : syracuseStep 9040997 = 1695187) (by norm_num)
theorem B2823269 : Blo 1881142 2823269 := bbase (se 4 (by rfl) ⟨264681, by rfl⟩ : syracuseStep 2823269 = 529363) (by norm_num)
theorem B2380909 : Blo 1881142 2380909 := bbase (se 3 (by rfl) ⟨446420, by rfl⟩ : syracuseStep 2380909 = 892841) (by norm_num)
theorem B2823293 : Blo 1881142 2823293 := bbase (se 3 (by rfl) ⟨529367, by rfl⟩ : syracuseStep 2823293 = 1058735) (by norm_num)
theorem B2823317 : Blo 1881142 2823317 := bbase (se 6 (by rfl) ⟨66171, by rfl⟩ : syracuseStep 2823317 = 132343) (by norm_num)
theorem B9532565 : Blo 1881142 9532565 := bbase (se 6 (by rfl) ⟨223419, by rfl⟩ : syracuseStep 9532565 = 446839) (by norm_num)
theorem B4019357 : Blo 1881142 4019357 := bbase (se 3 (by rfl) ⟨753629, by rfl⟩ : syracuseStep 4019357 = 1507259) (by norm_num)
theorem B2823341 : Blo 1881142 2823341 := bbase (se 3 (by rfl) ⟨529376, by rfl⟩ : syracuseStep 2823341 = 1058753) (by norm_num)
theorem B4764845 : Blo 1881142 4764845 := bbase (se 3 (by rfl) ⟨893408, by rfl⟩ : syracuseStep 4764845 = 1786817) (by norm_num)
theorem B2823365 : Blo 1881142 2823365 := bbase (se 4 (by rfl) ⟨264690, by rfl⟩ : syracuseStep 2823365 = 529381) (by norm_num)
theorem B2381005 : Blo 1881142 2381005 := bbase (se 3 (by rfl) ⟨446438, by rfl⟩ : syracuseStep 2381005 = 892877) (by norm_num)
theorem B3175645 : Blo 1881142 3175645 := bbase (se 3 (by rfl) ⟨595433, by rfl⟩ : syracuseStep 3175645 = 1190867) (by norm_num)
theorem B2823389 : Blo 1881142 2823389 := bbase (se 3 (by rfl) ⟨529385, by rfl⟩ : syracuseStep 2823389 = 1058771) (by norm_num)
theorem B2823413 : Blo 1881142 2823413 := bbase (se 5 (by rfl) ⟨132347, by rfl⟩ : syracuseStep 2823413 = 264695) (by norm_num)
theorem B2823437 : Blo 1881142 2823437 := bbase (se 3 (by rfl) ⟨529394, by rfl⟩ : syracuseStep 2823437 = 1058789) (by norm_num)
theorem B2823461 : Blo 1881142 2823461 := bbase (se 4 (by rfl) ⟨264699, by rfl⟩ : syracuseStep 2823461 = 529399) (by norm_num)
theorem B4019501 : Blo 1881142 4019501 := bbase (se 3 (by rfl) ⟨753656, by rfl⟩ : syracuseStep 4019501 = 1507313) (by norm_num)
theorem B3175733 : Blo 1881142 3175733 := bbase (se 5 (by rfl) ⟨148862, by rfl⟩ : syracuseStep 3175733 = 297725) (by norm_num)
theorem B6198581 : Blo 1881142 6198581 := bbase (se 5 (by rfl) ⟨290558, by rfl⟩ : syracuseStep 6198581 = 581117) (by norm_num)
theorem B2823485 : Blo 1881142 2823485 := bbase (se 3 (by rfl) ⟨529403, by rfl⟩ : syracuseStep 2823485 = 1058807) (by norm_num)
theorem B2823509 : Blo 1881142 2823509 := bbase (se 14 (by rfl) ⟨258, by rfl⟩ : syracuseStep 2823509 = 517) (by norm_num)
theorem B2823533 : Blo 1881142 2823533 := bbase (se 3 (by rfl) ⟨529412, by rfl⟩ : syracuseStep 2823533 = 1058825) (by norm_num)
theorem B2381177 : Blo 1881142 2381177 := bbase (se 2 (by rfl) ⟨892941, by rfl⟩ : syracuseStep 2381177 = 1785883) (by norm_num)
theorem B4232573 : Blo 1881142 4232573 := bbase (se 3 (by rfl) ⟨793607, by rfl⟩ : syracuseStep 4232573 = 1587215) (by norm_num)
theorem B2823557 : Blo 1881142 2823557 := bbase (se 4 (by rfl) ⟨264708, by rfl⟩ : syracuseStep 2823557 = 529417) (by norm_num)
theorem B2823581 : Blo 1881142 2823581 := bbase (se 3 (by rfl) ⟨529421, by rfl⟩ : syracuseStep 2823581 = 1058843) (by norm_num)
theorem B6354341 : Blo 1881142 6354341 := bbase (se 4 (by rfl) ⟨595719, by rfl⟩ : syracuseStep 6354341 = 1191439) (by norm_num)
theorem B2381233 : Blo 1881142 2381233 := bbase (se 2 (by rfl) ⟨892962, by rfl⟩ : syracuseStep 2381233 = 1785925) (by norm_num)
theorem B3175861 : Blo 1881142 3175861 := bbase (se 5 (by rfl) ⟨148868, by rfl⟩ : syracuseStep 3175861 = 297737) (by norm_num)
theorem B2823605 : Blo 1881142 2823605 := bbase (se 5 (by rfl) ⟨132356, by rfl⟩ : syracuseStep 2823605 = 264713) (by norm_num)
theorem B4232645 : Blo 1881142 4232645 := bbase (se 4 (by rfl) ⟨396810, by rfl⟩ : syracuseStep 4232645 = 793621) (by norm_num)
theorem B2823629 : Blo 1881142 2823629 := bbase (se 3 (by rfl) ⟨529430, by rfl⟩ : syracuseStep 2823629 = 1058861) (by norm_num)
theorem B2823653 : Blo 1881142 2823653 := bbase (se 4 (by rfl) ⟨264717, by rfl⟩ : syracuseStep 2823653 = 529435) (by norm_num)
theorem B2823677 : Blo 1881142 2823677 := bbase (se 3 (by rfl) ⟨529439, by rfl⟩ : syracuseStep 2823677 = 1058879) (by norm_num)
theorem B4765189 : Blo 1881142 4765189 := bbase (se 4 (by rfl) ⟨446736, by rfl⟩ : syracuseStep 4765189 = 893473) (by norm_num)
theorem B4232717 : Blo 1881142 4232717 := bbase (se 3 (by rfl) ⟨793634, by rfl⟩ : syracuseStep 4232717 = 1587269) (by norm_num)
theorem B3175949 : Blo 1881142 3175949 := bbase (se 3 (by rfl) ⟨595490, by rfl⟩ : syracuseStep 3175949 = 1190981) (by norm_num)
theorem B2381329 : Blo 1881142 2381329 := bbase (se 2 (by rfl) ⟨892998, by rfl⟩ : syracuseStep 2381329 = 1785997) (by norm_num)
theorem B3814933 : Blo 1881142 3814933 := bbase (se 6 (by rfl) ⟨89412, by rfl⟩ : syracuseStep 3814933 = 178825) (by norm_num)
theorem B2823701 : Blo 1881142 2823701 := bbase (se 6 (by rfl) ⟨66180, by rfl⟩ : syracuseStep 2823701 = 132361) (by norm_num)
theorem B2823725 : Blo 1881142 2823725 := bbase (se 3 (by rfl) ⟨529448, by rfl⟩ : syracuseStep 2823725 = 1058897) (by norm_num)
theorem B9524789 : Blo 1881142 9524789 := bbase (se 5 (by rfl) ⟨446474, by rfl⟩ : syracuseStep 9524789 = 892949) (by norm_num)
theorem B2823749 : Blo 1881142 2823749 := bbase (se 4 (by rfl) ⟨264726, by rfl⟩ : syracuseStep 2823749 = 529453) (by norm_num)
theorem B4232789 : Blo 1881142 4232789 := bbase (se 8 (by rfl) ⟨24801, by rfl⟩ : syracuseStep 4232789 = 49603) (by norm_num)
theorem B2823773 : Blo 1881142 2823773 := bbase (se 3 (by rfl) ⟨529457, by rfl⟩ : syracuseStep 2823773 = 1058915) (by norm_num)
theorem B2823797 : Blo 1881142 2823797 := bbase (se 5 (by rfl) ⟨132365, by rfl⟩ : syracuseStep 2823797 = 264731) (by norm_num)
theorem B4765301 : Blo 1881142 4765301 := bbase (se 5 (by rfl) ⟨223373, by rfl⟩ : syracuseStep 4765301 = 446747) (by norm_num)
theorem B3176077 : Blo 1881142 3176077 := bbase (se 3 (by rfl) ⟨595514, by rfl⟩ : syracuseStep 3176077 = 1191029) (by norm_num)
theorem B2823821 : Blo 1881142 2823821 := bbase (se 3 (by rfl) ⟨529466, by rfl⟩ : syracuseStep 2823821 = 1058933) (by norm_num)
theorem B4019861 : Blo 1881142 4019861 := bbase (se 6 (by rfl) ⟨94215, by rfl⟩ : syracuseStep 4019861 = 188431) (by norm_num)
theorem B4232861 : Blo 1881142 4232861 := bbase (se 3 (by rfl) ⟨793661, by rfl⟩ : syracuseStep 4232861 = 1587323) (by norm_num)
theorem B2823845 : Blo 1881142 2823845 := bbase (se 4 (by rfl) ⟨264735, by rfl⟩ : syracuseStep 2823845 = 529471) (by norm_num)
theorem B2381501 : Blo 1881142 2381501 := bbase (se 3 (by rfl) ⟨446531, by rfl⟩ : syracuseStep 2381501 = 893063) (by norm_num)
theorem B2823869 : Blo 1881142 2823869 := bbase (se 3 (by rfl) ⟨529475, by rfl⟩ : syracuseStep 2823869 = 1058951) (by norm_num)
theorem B2823893 : Blo 1881142 2823893 := bbase (se 7 (by rfl) ⟨33092, by rfl⟩ : syracuseStep 2823893 = 66185) (by norm_num)
theorem B4232933 : Blo 1881142 4232933 := bbase (se 4 (by rfl) ⟨396837, by rfl⟩ : syracuseStep 4232933 = 793675) (by norm_num)
theorem B3176165 : Blo 1881142 3176165 := bbase (se 4 (by rfl) ⟨297765, by rfl⟩ : syracuseStep 3176165 = 595531) (by norm_num)
theorem B2823917 : Blo 1881142 2823917 := bbase (se 3 (by rfl) ⟨529484, by rfl⟩ : syracuseStep 2823917 = 1058969) (by norm_num)
theorem B2381557 : Blo 1881142 2381557 := bbase (se 5 (by rfl) ⟨111635, by rfl⟩ : syracuseStep 2381557 = 223271) (by norm_num)
theorem B2823941 : Blo 1881142 2823941 := bbase (se 4 (by rfl) ⟨264744, by rfl⟩ : syracuseStep 2823941 = 529489) (by norm_num)
theorem B2823965 : Blo 1881142 2823965 := bbase (se 3 (by rfl) ⟨529493, by rfl⟩ : syracuseStep 2823965 = 1058987) (by norm_num)
theorem B6526757 : Blo 1881142 6526757 := bbase (se 4 (by rfl) ⟨611883, by rfl⟩ : syracuseStep 6526757 = 1223767) (by norm_num)
theorem B4233005 : Blo 1881142 4233005 := bbase (se 3 (by rfl) ⟨793688, by rfl⟩ : syracuseStep 4233005 = 1587377) (by norm_num)
theorem B2823989 : Blo 1881142 2823989 := bbase (se 5 (by rfl) ⟨132374, by rfl⟩ : syracuseStep 2823989 = 264749) (by norm_num)
theorem B4765493 : Blo 1881142 4765493 := bbase (se 5 (by rfl) ⟨223382, by rfl⟩ : syracuseStep 4765493 = 446765) (by norm_num)
theorem B2824013 : Blo 1881142 2824013 := bbase (se 3 (by rfl) ⟨529502, by rfl⟩ : syracuseStep 2824013 = 1059005) (by norm_num)
theorem B2381653 : Blo 1881142 2381653 := bbase (se 9 (by rfl) ⟨6977, by rfl⟩ : syracuseStep 2381653 = 13955) (by norm_num)
theorem B6354773 : Blo 1881142 6354773 := bbase (se 9 (by rfl) ⟨18617, by rfl⟩ : syracuseStep 6354773 = 37235) (by norm_num)
theorem B3176293 : Blo 1881142 3176293 := bbase (se 4 (by rfl) ⟨297777, by rfl⟩ : syracuseStep 3176293 = 595555) (by norm_num)
theorem B2824037 : Blo 1881142 2824037 := bbase (se 4 (by rfl) ⟨264753, by rfl⟩ : syracuseStep 2824037 = 529507) (by norm_num)
theorem B4233077 : Blo 1881142 4233077 := bbase (se 5 (by rfl) ⟨198425, by rfl⟩ : syracuseStep 4233077 = 396851) (by norm_num)
theorem B2824061 : Blo 1881142 2824061 := bbase (se 3 (by rfl) ⟨529511, by rfl⟩ : syracuseStep 2824061 = 1059023) (by norm_num)
theorem B2824085 : Blo 1881142 2824085 := bbase (se 6 (by rfl) ⟨66189, by rfl⟩ : syracuseStep 2824085 = 132379) (by norm_num)
theorem B2824109 : Blo 1881142 2824109 := bbase (se 3 (by rfl) ⟨529520, by rfl⟩ : syracuseStep 2824109 = 1059041) (by norm_num)
theorem B4233149 : Blo 1881142 4233149 := bbase (se 3 (by rfl) ⟨793715, by rfl⟩ : syracuseStep 4233149 = 1587431) (by norm_num)
theorem B3176381 : Blo 1881142 3176381 := bbase (se 3 (by rfl) ⟨595571, by rfl⟩ : syracuseStep 3176381 = 1191143) (by norm_num)
theorem B2824133 : Blo 1881142 2824133 := bbase (se 4 (by rfl) ⟨264762, by rfl⟩ : syracuseStep 2824133 = 529525) (by norm_num)
theorem B2291657 : Blo 1881142 2291657 := bbase (se 2 (by rfl) ⟨859371, by rfl⟩ : syracuseStep 2291657 = 1718743) (by norm_num)
theorem B2824157 : Blo 1881142 2824157 := bbase (se 3 (by rfl) ⟨529529, by rfl⟩ : syracuseStep 2824157 = 1059059) (by norm_num)
theorem B2824181 : Blo 1881142 2824181 := bbase (se 5 (by rfl) ⟨132383, by rfl⟩ : syracuseStep 2824181 = 264767) (by norm_num)
theorem B2381825 : Blo 1881142 2381825 := bbase (se 2 (by rfl) ⟨893184, by rfl⟩ : syracuseStep 2381825 = 1786369) (by norm_num)
theorem B4233221 : Blo 1881142 4233221 := bbase (se 4 (by rfl) ⟨396864, by rfl⟩ : syracuseStep 4233221 = 793729) (by norm_num)
theorem B2824205 : Blo 1881142 2824205 := bbase (se 3 (by rfl) ⟨529538, by rfl⟩ : syracuseStep 2824205 = 1059077) (by norm_num)
theorem B2824229 : Blo 1881142 2824229 := bbase (se 4 (by rfl) ⟨264771, by rfl⟩ : syracuseStep 2824229 = 529543) (by norm_num)
theorem B2381881 : Blo 1881142 2381881 := bbase (se 2 (by rfl) ⟨893205, by rfl⟩ : syracuseStep 2381881 = 1786411) (by norm_num)
theorem B3176509 : Blo 1881142 3176509 := bbase (se 3 (by rfl) ⟨595595, by rfl⟩ : syracuseStep 3176509 = 1191191) (by norm_num)
theorem B2824253 : Blo 1881142 2824253 := bbase (se 3 (by rfl) ⟨529547, by rfl⟩ : syracuseStep 2824253 = 1059095) (by norm_num)
theorem B4233293 : Blo 1881142 4233293 := bbase (se 3 (by rfl) ⟨793742, by rfl⟩ : syracuseStep 4233293 = 1587485) (by norm_num)
theorem B2824277 : Blo 1881142 2824277 := bbase (se 8 (by rfl) ⟨16548, by rfl⟩ : syracuseStep 2824277 = 33097) (by norm_num)
theorem B7149653 : Blo 1881142 7149653 := bbase (se 8 (by rfl) ⟨41892, by rfl⟩ : syracuseStep 7149653 = 83785) (by norm_num)
theorem B2824301 : Blo 1881142 2824301 := bbase (se 3 (by rfl) ⟨529556, by rfl⟩ : syracuseStep 2824301 = 1059113) (by norm_num)
theorem B9164933 : Blo 1881142 9164933 := bbase (se 4 (by rfl) ⟨859212, by rfl⟩ : syracuseStep 9164933 = 1718425) (by norm_num)
theorem B2824325 : Blo 1881142 2824325 := bbase (se 4 (by rfl) ⟨264780, by rfl⟩ : syracuseStep 2824325 = 529561) (by norm_num)
theorem B4765837 : Blo 1881142 4765837 := bbase (se 3 (by rfl) ⟨893594, by rfl⟩ : syracuseStep 4765837 = 1787189) (by norm_num)
theorem B4233365 : Blo 1881142 4233365 := bbase (se 6 (by rfl) ⟨99219, by rfl⟩ : syracuseStep 4233365 = 198439) (by norm_num)
theorem B3176597 : Blo 1881142 3176597 := bbase (se 6 (by rfl) ⟨74451, by rfl⟩ : syracuseStep 3176597 = 148903) (by norm_num)
theorem B2381977 : Blo 1881142 2381977 := bbase (se 2 (by rfl) ⟨893241, by rfl⟩ : syracuseStep 2381977 = 1786483) (by norm_num)
theorem B2824349 : Blo 1881142 2824349 := bbase (se 3 (by rfl) ⟨529565, by rfl⟩ : syracuseStep 2824349 = 1059131) (by norm_num)
theorem B2824373 : Blo 1881142 2824373 := bbase (se 5 (by rfl) ⟨132392, by rfl⟩ : syracuseStep 2824373 = 264785) (by norm_num)
theorem B2824397 : Blo 1881142 2824397 := bbase (se 3 (by rfl) ⟨529574, by rfl⟩ : syracuseStep 2824397 = 1059149) (by norm_num)
theorem B2578645 : Blo 1881142 2578645 := bbase (se 7 (by rfl) ⟨30218, by rfl⟩ : syracuseStep 2578645 = 60437) (by norm_num)
theorem B7633109 : Blo 1881142 7633109 := bbase (se 7 (by rfl) ⟨89450, by rfl⟩ : syracuseStep 7633109 = 178901) (by norm_num)
theorem B4233437 : Blo 1881142 4233437 := bbase (se 3 (by rfl) ⟨793769, by rfl⟩ : syracuseStep 4233437 = 1587539) (by norm_num)
theorem B3922141 : Blo 1881142 3922141 := bbase (se 3 (by rfl) ⟨735401, by rfl⟩ : syracuseStep 3922141 = 1470803) (by norm_num)
theorem B2824421 : Blo 1881142 2824421 := bbase (se 4 (by rfl) ⟨264789, by rfl⟩ : syracuseStep 2824421 = 529579) (by norm_num)
theorem B6027509 : Blo 1881142 6027509 := bbase (se 5 (by rfl) ⟨282539, by rfl⟩ : syracuseStep 6027509 = 565079) (by norm_num)
theorem B4765949 : Blo 1881142 4765949 := bbase (se 3 (by rfl) ⟨893615, by rfl⟩ : syracuseStep 4765949 = 1787231) (by norm_num)
theorem B2824445 : Blo 1881142 2824445 := bbase (se 3 (by rfl) ⟨529583, by rfl⟩ : syracuseStep 2824445 = 1059167) (by norm_num)
theorem B6355205 : Blo 1881142 6355205 := bbase (se 4 (by rfl) ⟨595800, by rfl⟩ : syracuseStep 6355205 = 1191601) (by norm_num)
theorem B3176725 : Blo 1881142 3176725 := bbase (se 6 (by rfl) ⟨74454, by rfl⟩ : syracuseStep 3176725 = 148909) (by norm_num)
theorem B2824469 : Blo 1881142 2824469 := bbase (se 6 (by rfl) ⟨66198, by rfl⟩ : syracuseStep 2824469 = 132397) (by norm_num)
theorem B4233509 : Blo 1881142 4233509 := bbase (se 4 (by rfl) ⟨396891, by rfl⟩ : syracuseStep 4233509 = 793783) (by norm_num)
theorem B2824493 : Blo 1881142 2824493 := bbase (se 3 (by rfl) ⟨529592, by rfl⟩ : syracuseStep 2824493 = 1059185) (by norm_num)
theorem B2382149 : Blo 1881142 2382149 := bbase (se 4 (by rfl) ⟨223326, by rfl⟩ : syracuseStep 2382149 = 446653) (by norm_num)
theorem B2824517 : Blo 1881142 2824517 := bbase (se 4 (by rfl) ⟨264798, by rfl⟩ : syracuseStep 2824517 = 529597) (by norm_num)
theorem B4962637 : Blo 1881142 4962637 := bbase (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) (by norm_num)
theorem B2824541 : Blo 1881142 2824541 := bbase (se 3 (by rfl) ⟨529601, by rfl⟩ : syracuseStep 2824541 = 1059203) (by norm_num)
theorem B4233581 : Blo 1881142 4233581 := bbase (se 3 (by rfl) ⟨793796, by rfl⟩ : syracuseStep 4233581 = 1587593) (by norm_num)
theorem B3176813 : Blo 1881142 3176813 := bbase (se 3 (by rfl) ⟨595652, by rfl⟩ : syracuseStep 3176813 = 1191305) (by norm_num)
theorem B2824565 : Blo 1881142 2824565 := bbase (se 5 (by rfl) ⟨132401, by rfl⟩ : syracuseStep 2824565 = 264803) (by norm_num)
theorem B7149941 : Blo 1881142 7149941 := bbase (se 5 (by rfl) ⟨335153, by rfl⟩ : syracuseStep 7149941 = 670307) (by norm_num)
theorem B2382205 : Blo 1881142 2382205 := bbase (se 3 (by rfl) ⟨446663, by rfl⟩ : syracuseStep 2382205 = 893327) (by norm_num)
theorem B2038141 : Blo 1881142 2038141 := bbase (se 3 (by rfl) ⟨382151, by rfl⟩ : syracuseStep 2038141 = 764303) (by norm_num)
theorem B2824589 : Blo 1881142 2824589 := bbase (se 3 (by rfl) ⟨529610, by rfl⟩ : syracuseStep 2824589 = 1059221) (by norm_num)
theorem B2824613 : Blo 1881142 2824613 := bbase (se 4 (by rfl) ⟨264807, by rfl⟩ : syracuseStep 2824613 = 529615) (by norm_num)
theorem B4233653 : Blo 1881142 4233653 := bbase (se 5 (by rfl) ⟨198452, by rfl⟩ : syracuseStep 4233653 = 396905) (by norm_num)
theorem B4766141 : Blo 1881142 4766141 := bbase (se 3 (by rfl) ⟨893651, by rfl⟩ : syracuseStep 4766141 = 1787303) (by norm_num)
theorem B2824637 : Blo 1881142 2824637 := bbase (se 3 (by rfl) ⟨529619, by rfl⟩ : syracuseStep 2824637 = 1059239) (by norm_num)
theorem B2824661 : Blo 1881142 2824661 := bbase (se 7 (by rfl) ⟨33101, by rfl⟩ : syracuseStep 2824661 = 66203) (by norm_num)
theorem B2382301 : Blo 1881142 2382301 := bbase (se 3 (by rfl) ⟨446681, by rfl⟩ : syracuseStep 2382301 = 893363) (by norm_num)
theorem B3176941 : Blo 1881142 3176941 := bbase (se 3 (by rfl) ⟨595676, by rfl⟩ : syracuseStep 3176941 = 1191353) (by norm_num)
theorem B2824685 : Blo 1881142 2824685 := bbase (se 3 (by rfl) ⟨529628, by rfl⟩ : syracuseStep 2824685 = 1059257) (by norm_num)
theorem B12065269 : Blo 1881142 12065269 := bbase (se 5 (by rfl) ⟨565559, by rfl⟩ : syracuseStep 12065269 = 1131119) (by norm_num)
theorem B4233725 : Blo 1881142 4233725 := bbase (se 3 (by rfl) ⟨793823, by rfl⟩ : syracuseStep 4233725 = 1587647) (by norm_num)
theorem B2824709 : Blo 1881142 2824709 := bbase (se 4 (by rfl) ⟨264816, by rfl⟩ : syracuseStep 2824709 = 529633) (by norm_num)
theorem B4020749 : Blo 1881142 4020749 := bbase (se 3 (by rfl) ⟨753890, by rfl⟩ : syracuseStep 4020749 = 1507781) (by norm_num)
theorem B4233797 : Blo 1881142 4233797 := bbase (se 4 (by rfl) ⟨396918, by rfl⟩ : syracuseStep 4233797 = 793837) (by norm_num)
theorem B3177029 : Blo 1881142 3177029 := bbase (se 4 (by rfl) ⟨297846, by rfl⟩ : syracuseStep 3177029 = 595693) (by norm_num)
theorem B12057173 : Blo 1881142 12057173 := bbase (se 8 (by rfl) ⟨70647, by rfl⟩ : syracuseStep 12057173 = 141295) (by norm_num)
theorem B2382473 : Blo 1881142 2382473 := bbase (se 2 (by rfl) ⟨893427, by rfl⟩ : syracuseStep 2382473 = 1786855) (by norm_num)
theorem B4233869 : Blo 1881142 4233869 := bbase (se 3 (by rfl) ⟨793850, by rfl⟩ : syracuseStep 4233869 = 1587701) (by norm_num)
theorem B2292373 : Blo 1881142 2292373 := bbase (se 6 (by rfl) ⟨53727, by rfl⟩ : syracuseStep 2292373 = 107455) (by norm_num)
theorem B2382529 : Blo 1881142 2382529 := bbase (se 2 (by rfl) ⟨893448, by rfl⟩ : syracuseStep 2382529 = 1786897) (by norm_num)
theorem B3177157 : Blo 1881142 3177157 := bbase (se 4 (by rfl) ⟨297858, by rfl⟩ : syracuseStep 3177157 = 595717) (by norm_num)
theorem B4233941 : Blo 1881142 4233941 := bbase (se 7 (by rfl) ⟨49616, by rfl⟩ : syracuseStep 4233941 = 99233) (by norm_num)
theorem B2415349 : Blo 1881142 2415349 := bbase (se 5 (by rfl) ⟨113219, by rfl⟩ : syracuseStep 2415349 = 226439) (by norm_num)
theorem B11451125 : Blo 1881142 11451125 := bbase (se 5 (by rfl) ⟨536771, by rfl⟩ : syracuseStep 11451125 = 1073543) (by norm_num)
theorem B4020997 : Blo 1881142 4020997 := bbase (se 4 (by rfl) ⟨376968, by rfl⟩ : syracuseStep 4020997 = 753937) (by norm_num)
theorem B4766485 : Blo 1881142 4766485 := bbase (se 6 (by rfl) ⟨111714, by rfl⟩ : syracuseStep 4766485 = 223429) (by norm_num)
theorem B4234013 : Blo 1881142 4234013 := bbase (se 3 (by rfl) ⟨793877, by rfl⟩ : syracuseStep 4234013 = 1587755) (by norm_num)
theorem B3177245 : Blo 1881142 3177245 := bbase (se 3 (by rfl) ⟨595733, by rfl⟩ : syracuseStep 3177245 = 1191467) (by norm_num)
theorem B2382625 : Blo 1881142 2382625 := bbase (se 2 (by rfl) ⟨893484, by rfl⟩ : syracuseStep 2382625 = 1786969) (by norm_num)
theorem B2415421 : Blo 1881142 2415421 := bbase (se 3 (by rfl) ⟨452891, by rfl⟩ : syracuseStep 2415421 = 905783) (by norm_num)
theorem B9526085 : Blo 1881142 9526085 := bbase (se 4 (by rfl) ⟨893070, by rfl⟩ : syracuseStep 9526085 = 1786141) (by norm_num)
theorem B4234085 : Blo 1881142 4234085 := bbase (se 4 (by rfl) ⟨396945, by rfl⟩ : syracuseStep 4234085 = 793891) (by norm_num)
theorem B4766597 : Blo 1881142 4766597 := bbase (se 4 (by rfl) ⟨446868, by rfl⟩ : syracuseStep 4766597 = 893737) (by norm_num)
theorem B3177373 : Blo 1881142 3177373 := bbase (se 3 (by rfl) ⟨595757, by rfl⟩ : syracuseStep 3177373 = 1191515) (by norm_num)
theorem B2415529 : Blo 1881142 2415529 := bbase (se 2 (by rfl) ⟨905823, by rfl⟩ : syracuseStep 2415529 = 1811647) (by norm_num)
theorem B4234157 : Blo 1881142 4234157 := bbase (se 3 (by rfl) ⟨793904, by rfl⟩ : syracuseStep 4234157 = 1587809) (by norm_num)
theorem B3218357 : Blo 1881142 3218357 := bbase (se 5 (by rfl) ⟨150860, by rfl⟩ : syracuseStep 3218357 = 301721) (by norm_num)
theorem B1907645 : Blo 1881142 1907645 := bbase (se 3 (by rfl) ⟨357683, by rfl⟩ : syracuseStep 1907645 = 715367) (by norm_num)
theorem B2382797 : Blo 1881142 2382797 := bbase (se 3 (by rfl) ⟨446774, by rfl⟩ : syracuseStep 2382797 = 893549) (by norm_num)
theorem B4234229 : Blo 1881142 4234229 := bbase (se 5 (by rfl) ⟨198479, by rfl⟩ : syracuseStep 4234229 = 396959) (by norm_num)
theorem B10722293 : Blo 1881142 10722293 := bbase (se 5 (by rfl) ⟨502607, by rfl⟩ : syracuseStep 10722293 = 1005215) (by norm_num)
theorem B3177461 : Blo 1881142 3177461 := bbase (se 5 (by rfl) ⟨148943, by rfl⟩ : syracuseStep 3177461 = 297887) (by norm_num)
theorem B2382853 : Blo 1881142 2382853 := bbase (se 4 (by rfl) ⟨223392, by rfl⟩ : syracuseStep 2382853 = 446785) (by norm_num)
theorem B4234301 : Blo 1881142 4234301 := bbase (se 3 (by rfl) ⟨793931, by rfl⟩ : syracuseStep 4234301 = 1587863) (by norm_num)
theorem B9657413 : Blo 1881142 9657413 := bbase (se 4 (by rfl) ⟨905382, by rfl⟩ : syracuseStep 9657413 = 1810765) (by norm_num)
theorem B2260057 : Blo 1881142 2260057 := bbase (se 2 (by rfl) ⟨847521, by rfl⟩ : syracuseStep 2260057 = 1695043) (by norm_num)
theorem B2382949 : Blo 1881142 2382949 := bbase (se 4 (by rfl) ⟨223401, by rfl⟩ : syracuseStep 2382949 = 446803) (by norm_num)
theorem B3177589 : Blo 1881142 3177589 := bbase (se 5 (by rfl) ⟨148949, by rfl⟩ : syracuseStep 3177589 = 297899) (by norm_num)
theorem B4234373 : Blo 1881142 4234373 := bbase (se 4 (by rfl) ⟨396972, by rfl⟩ : syracuseStep 4234373 = 793945) (by norm_num)
theorem B2145421 : Blo 1881142 2145421 := bbase (se 3 (by rfl) ⟨402266, by rfl⟩ : syracuseStep 2145421 = 804533) (by norm_num)
theorem B2579653 : Blo 1881142 2579653 := bbase (se 4 (by rfl) ⟨241842, by rfl⟩ : syracuseStep 2579653 = 483685) (by norm_num)
theorem B4234445 : Blo 1881142 4234445 := bbase (se 3 (by rfl) ⟨793958, by rfl⟩ : syracuseStep 4234445 = 1587917) (by norm_num)
theorem B3177677 : Blo 1881142 3177677 := bbase (se 3 (by rfl) ⟨595814, by rfl⟩ : syracuseStep 3177677 = 1191629) (by norm_num)
theorem B4021501 : Blo 1881142 4021501 := bbase (se 3 (by rfl) ⟨754031, by rfl⟩ : syracuseStep 4021501 = 1508063) (by norm_num)
theorem B2383121 : Blo 1881142 2383121 := bbase (se 2 (by rfl) ⟨893670, by rfl⟩ : syracuseStep 2383121 = 1787341) (by norm_num)
theorem B4234517 : Blo 1881142 4234517 := bbase (se 6 (by rfl) ⟨99246, by rfl⟩ : syracuseStep 4234517 = 198493) (by norm_num)
theorem B2383177 : Blo 1881142 2383177 := bbase (se 2 (by rfl) ⟨893691, by rfl⟩ : syracuseStep 2383177 = 1787383) (by norm_num)
theorem B4234589 : Blo 1881142 4234589 := bbase (se 3 (by rfl) ⟨793985, by rfl⟩ : syracuseStep 4234589 = 1587971) (by norm_num)
theorem B3014005 : Blo 1881142 3014005 := bbase (se 5 (by rfl) ⟨141281, by rfl⟩ : syracuseStep 3014005 = 282563) (by norm_num)
theorem B4234661 : Blo 1881142 4234661 := bbase (se 4 (by rfl) ⟨396999, by rfl⟩ : syracuseStep 4234661 = 793999) (by norm_num)
theorem B2383273 : Blo 1881142 2383273 := bbase (se 2 (by rfl) ⟨893727, by rfl⟩ : syracuseStep 2383273 = 1787455) (by norm_num)
theorem B3390893 : Blo 1881142 3390893 := bbase (se 3 (by rfl) ⟨635792, by rfl⟩ : syracuseStep 3390893 = 1271585) (by norm_num)
theorem B3620285 : Blo 1881142 3620285 := bbase (se 3 (by rfl) ⟨678803, by rfl⟩ : syracuseStep 3620285 = 1357607) (by norm_num)
theorem B4234733 : Blo 1881142 4234733 := bbase (se 3 (by rfl) ⟨794012, by rfl⟩ : syracuseStep 4234733 = 1588025) (by norm_num)
theorem B1908209 : Blo 1881142 1908209 := bbase (se 2 (by rfl) ⟨715578, by rfl⟩ : syracuseStep 1908209 = 1431157) (by norm_num)
theorem B4234805 : Blo 1881142 4234805 := bbase (se 5 (by rfl) ⟨198506, by rfl⟩ : syracuseStep 4234805 = 397013) (by norm_num)
theorem B4234877 : Blo 1881142 4234877 := bbase (se 3 (by rfl) ⟨794039, by rfl⟩ : syracuseStep 4234877 = 1588079) (by norm_num)
theorem B2678437 : Blo 1881142 2678437 := bbase (se 4 (by rfl) ⟨251103, by rfl⟩ : syracuseStep 2678437 = 502207) (by norm_num)
theorem B4128421 : Blo 1881142 4128421 := bbase (se 4 (by rfl) ⟨387039, by rfl⟩ : syracuseStep 4128421 = 774079) (by norm_num)
theorem B2064061 : Blo 1881142 2064061 := bbase (se 3 (by rfl) ⟨387011, by rfl⟩ : syracuseStep 2064061 = 774023) (by norm_num)
theorem B4234949 : Blo 1881142 4234949 := bbase (se 4 (by rfl) ⟨397026, by rfl⟩ : syracuseStep 4234949 = 794053) (by norm_num)
theorem B5357285 : Blo 1881142 5357285 := bbase (se 4 (by rfl) ⟨502245, by rfl⟩ : syracuseStep 5357285 = 1004491) (by norm_num)
theorem B4235021 : Blo 1881142 4235021 := bbase (se 3 (by rfl) ⟨794066, by rfl⟩ : syracuseStep 4235021 = 1588133) (by norm_num)
theorem B8036117 : Blo 1881142 8036117 := bbase (se 6 (by rfl) ⟨188346, by rfl⟩ : syracuseStep 8036117 = 376693) (by norm_num)
theorem B1908553 : Blo 1881142 1908553 := bbase (se 2 (by rfl) ⟨715707, by rfl⟩ : syracuseStep 1908553 = 1431415) (by norm_num)
theorem B4235093 : Blo 1881142 4235093 := bbase (se 9 (by rfl) ⟨12407, by rfl⟩ : syracuseStep 4235093 = 24815) (by norm_num)
theorem B1908569 : Blo 1881142 1908569 := bbase (se 2 (by rfl) ⟨715713, by rfl⟩ : syracuseStep 1908569 = 1431427) (by norm_num)
theorem B4235165 : Blo 1881142 4235165 := bbase (se 3 (by rfl) ⟨794093, by rfl⟩ : syracuseStep 4235165 = 1588187) (by norm_num)
theorem B3391397 : Blo 1881142 3391397 := bbase (se 4 (by rfl) ⟨317943, by rfl⟩ : syracuseStep 3391397 = 635887) (by norm_num)
theorem B7143349 : Blo 1881142 7143349 := bbase (se 5 (by rfl) ⟨334844, by rfl⟩ : syracuseStep 7143349 = 669689) (by norm_num)
theorem B3620837 : Blo 1881142 3620837 := bbase (se 4 (by rfl) ⟨339453, by rfl⟩ : syracuseStep 3620837 = 678907) (by norm_num)
theorem B4235237 : Blo 1881142 4235237 := bbase (se 4 (by rfl) ⟨397053, by rfl⟩ : syracuseStep 4235237 = 794107) (by norm_num)
theorem B5357603 : Blo 1881142 5357603 := bstep (se 1 (by rfl) ⟨4018202, by rfl⟩ : syracuseStep 5357603 = 8036405) B8036405
theorem B4235345 : Blo 1881142 4235345 := bstep (se 2 (by rfl) ⟨1588254, by rfl⟩ : syracuseStep 4235345 = 3176509) B3176509
theorem B4235363 : Blo 1881142 4235363 := bstep (se 1 (by rfl) ⟨3176522, by rfl⟩ : syracuseStep 4235363 = 6353045) B6353045
theorem B3670147 : Blo 1881142 3670147 := bstep (se 1 (by rfl) ⟨2752610, by rfl⟩ : syracuseStep 3670147 = 5505221) B5505221
theorem B6348941 : Blo 1881142 6348941 := bstep (se 3 (by rfl) ⟨1190426, by rfl⟩ : syracuseStep 6348941 = 2380853) B2380853
theorem B4292785 : Blo 1881142 4292785 := bstep (se 2 (by rfl) ⟨1609794, by rfl⟩ : syracuseStep 4292785 = 3219589) B3219589
theorem B6348995 : Blo 1881142 6348995 := bstep (se 1 (by rfl) ⟨4761746, by rfl⟩ : syracuseStep 6348995 = 9523493) B9523493
theorem B3391715 : Blo 1881142 3391715 := bstep (se 1 (by rfl) ⟨2543786, by rfl⟩ : syracuseStep 3391715 = 5087573) B5087573
theorem B13943011 : Blo 1881142 13943011 := bstep (se 1 (by rfl) ⟨10457258, by rfl⟩ : syracuseStep 13943011 = 20914517) B20914517
theorem B6029549 : Blo 1881142 6029549 := bstep (se 3 (by rfl) ⟨1130540, by rfl⟩ : syracuseStep 6029549 = 2261081) B2261081
theorem B2679041 : Blo 1881142 2679041 := bstep (se 2 (by rfl) ⟨1004640, by rfl⟩ : syracuseStep 2679041 = 2009281) B2009281
theorem B5726477 : Blo 1881142 5726477 := bstep (se 3 (by rfl) ⟨1073714, by rfl⟩ : syracuseStep 5726477 = 2147429) B2147429
theorem B4235633 : Blo 1881142 4235633 := bstep (se 2 (by rfl) ⟨1588362, by rfl⟩ : syracuseStep 4235633 = 3176725) B3176725
theorem B4235651 : Blo 1881142 4235651 := bstep (se 1 (by rfl) ⟨3176738, by rfl⟩ : syracuseStep 4235651 = 6353477) B6353477
theorem B7143821 : Blo 1881142 7143821 := bstep (se 3 (by rfl) ⟨1339466, by rfl⟩ : syracuseStep 7143821 = 2678933) B2678933
theorem B6349265 : Blo 1881142 6349265 := bstep (se 2 (by rfl) ⟨2380974, by rfl⟩ : syracuseStep 6349265 = 4761949) B4761949
theorem B3621329 : Blo 1881142 3621329 := bstep (se 2 (by rfl) ⟨1357998, by rfl⟩ : syracuseStep 3621329 = 2715997) B2715997
theorem B3015139 : Blo 1881142 3015139 := bstep (se 1 (by rfl) ⟨2261354, by rfl⟩ : syracuseStep 3015139 = 4522709) B4522709
theorem B3392003 : Blo 1881142 3392003 := bstep (se 1 (by rfl) ⟨2544002, by rfl⟩ : syracuseStep 3392003 = 5088005) B5088005
theorem B17170957 : Blo 1881142 17170957 := bstep (se 3 (by rfl) ⟨3219554, by rfl⟩ : syracuseStep 17170957 = 6439109) B6439109
theorem B3015235 : Blo 1881142 3015235 := bstep (se 1 (by rfl) ⟨2261426, by rfl⟩ : syracuseStep 3015235 = 4522853) B4522853
theorem B6029969 : Blo 1881142 6029969 := bstep (se 2 (by rfl) ⟨2261238, by rfl⟩ : syracuseStep 6029969 = 4522477) B4522477
theorem B4235921 : Blo 1881142 4235921 := bstep (se 2 (by rfl) ⟨1588470, by rfl⟩ : syracuseStep 4235921 = 3176941) B3176941
theorem B4235939 : Blo 1881142 4235939 := bstep (se 1 (by rfl) ⟨3176954, by rfl⟩ : syracuseStep 4235939 = 6353909) B6353909
theorem B3572419 : Blo 1881142 3572419 := bstep (se 1 (by rfl) ⟨2679314, by rfl⟩ : syracuseStep 3572419 = 5358629) B5358629
theorem B3220163 : Blo 1881142 3220163 := bstep (se 1 (by rfl) ⟨2415122, by rfl⟩ : syracuseStep 3220163 = 4830245) B4830245
theorem B3015395 : Blo 1881142 3015395 := bstep (se 1 (by rfl) ⟨2261546, by rfl⟩ : syracuseStep 3015395 = 4523093) B4523093
theorem B2679571 : Blo 1881142 2679571 := bstep (se 1 (by rfl) ⟨2009678, by rfl⟩ : syracuseStep 2679571 = 4019357) B4019357
theorem B5358413 : Blo 1881142 5358413 := bstep (se 3 (by rfl) ⟨1004702, by rfl⟩ : syracuseStep 5358413 = 2009405) B2009405
theorem B3572579 : Blo 1881142 3572579 := bstep (se 1 (by rfl) ⟨2679434, by rfl⟩ : syracuseStep 3572579 = 5358869) B5358869
theorem B3056497 : Blo 1881142 3056497 := bstep (se 2 (by rfl) ⟨1146186, by rfl⟩ : syracuseStep 3056497 = 2292373) B2292373
theorem B3621763 : Blo 1881142 3621763 := bstep (se 1 (by rfl) ⟨2716322, by rfl⟩ : syracuseStep 3621763 = 5432645) B5432645
theorem B4236209 : Blo 1881142 4236209 := bstep (se 2 (by rfl) ⟨1588578, by rfl⟩ : syracuseStep 4236209 = 3177157) B3177157
theorem B4236227 : Blo 1881142 4236227 := bstep (se 1 (by rfl) ⟨3177170, by rfl⟩ : syracuseStep 4236227 = 6354341) B6354341
theorem B6349805 : Blo 1881142 6349805 := bstep (se 3 (by rfl) ⟨1190588, by rfl⟩ : syracuseStep 6349805 = 2381177) B2381177
theorem B3220465 : Blo 1881142 3220465 := bstep (se 2 (by rfl) ⟨1207674, by rfl⟩ : syracuseStep 3220465 = 2415349) B2415349
theorem B5358595 : Blo 1881142 5358595 := bstep (se 1 (by rfl) ⟨4018946, by rfl⟩ : syracuseStep 5358595 = 8037893) B8037893
theorem B6349859 : Blo 1881142 6349859 := bstep (se 1 (by rfl) ⟨4762394, by rfl⟩ : syracuseStep 6349859 = 9524789) B9524789
theorem B10716209 : Blo 1881142 10716209 := bstep (se 2 (by rfl) ⟨4018578, by rfl⟩ : syracuseStep 10716209 = 8037157) B8037157
theorem B3220561 : Blo 1881142 3220561 := bstep (se 2 (by rfl) ⟨1207710, by rfl⟩ : syracuseStep 3220561 = 2415421) B2415421
theorem B2679907 : Blo 1881142 2679907 := bstep (se 1 (by rfl) ⟨2009930, by rfl⟩ : syracuseStep 2679907 = 4019861) B4019861
theorem B7144625 : Blo 1881142 7144625 := bstep (se 2 (by rfl) ⟨2679234, by rfl⟩ : syracuseStep 7144625 = 5358469) B5358469
theorem B6784177 : Blo 1881142 6784177 := bstep (se 2 (by rfl) ⟨2544066, by rfl⟩ : syracuseStep 6784177 = 5088133) B5088133
theorem B4351171 : Blo 1881142 4351171 := bstep (se 1 (by rfl) ⟨3263378, by rfl⟩ : syracuseStep 4351171 = 6526757) B6526757
theorem B4236497 : Blo 1881142 4236497 := bstep (se 2 (by rfl) ⟨1588686, by rfl⟩ : syracuseStep 4236497 = 3177373) B3177373
theorem B3220705 : Blo 1881142 3220705 := bstep (se 2 (by rfl) ⟨1207764, by rfl⟩ : syracuseStep 3220705 = 2415529) B2415529
theorem B4236515 : Blo 1881142 4236515 := bstep (se 1 (by rfl) ⟨3177386, by rfl⟩ : syracuseStep 4236515 = 6354773) B6354773
theorem B5088557 : Blo 1881142 5088557 := bstep (se 3 (by rfl) ⟨954104, by rfl⟩ : syracuseStep 5088557 = 1908209) B1908209
theorem B6350129 : Blo 1881142 6350129 := bstep (se 2 (by rfl) ⟨2381298, by rfl⟩ : syracuseStep 6350129 = 4762597) B4762597
theorem B5088739 : Blo 1881142 5088739 := bstep (se 1 (by rfl) ⟨3816554, by rfl⟩ : syracuseStep 5088739 = 7633109) B7633109
theorem B5359085 : Blo 1881142 5359085 := bstep (se 3 (by rfl) ⟨1004828, by rfl⟩ : syracuseStep 5359085 = 2009657) B2009657
theorem B4236785 : Blo 1881142 4236785 := bstep (se 2 (by rfl) ⟨1588794, by rfl⟩ : syracuseStep 4236785 = 3177589) B3177589
theorem B4236803 : Blo 1881142 4236803 := bstep (se 1 (by rfl) ⟨3177602, by rfl⟩ : syracuseStep 4236803 = 6355205) B6355205
theorem B2860561 : Blo 1881142 2860561 := bstep (se 2 (by rfl) ⟨1072710, by rfl⟩ : syracuseStep 2860561 = 2145421) B2145421
theorem B9045553 : Blo 1881142 9045553 := bstep (se 2 (by rfl) ⟨3392082, by rfl⟩ : syracuseStep 9045553 = 6784165) B6784165
theorem B4523651 : Blo 1881142 4523651 := bstep (se 1 (by rfl) ⟨3392738, by rfl⟩ : syracuseStep 4523651 = 6785477) B6785477
theorem B2680465 : Blo 1881142 2680465 := bstep (se 2 (by rfl) ⟨1005174, by rfl⟩ : syracuseStep 2680465 = 2010349) B2010349
theorem B3016369 : Blo 1881142 3016369 := bstep (se 2 (by rfl) ⟨1131138, by rfl⟩ : syracuseStep 3016369 = 2262277) B2262277
theorem B2680499 : Blo 1881142 2680499 := bstep (se 1 (by rfl) ⟨2010374, by rfl⟩ : syracuseStep 2680499 = 4020749) B4020749
theorem B8038115 : Blo 1881142 8038115 := bstep (se 1 (by rfl) ⟨6028586, by rfl⟩ : syracuseStep 8038115 = 12057173) B12057173
theorem B6350669 : Blo 1881142 6350669 := bstep (se 3 (by rfl) ⟨1190750, by rfl⟩ : syracuseStep 6350669 = 2381501) B2381501
theorem B7145293 : Blo 1881142 7145293 := bstep (se 3 (by rfl) ⟨1339742, by rfl⟩ : syracuseStep 7145293 = 2679485) B2679485
theorem B6350723 : Blo 1881142 6350723 := bstep (se 1 (by rfl) ⟨4763042, by rfl⟩ : syracuseStep 6350723 = 9526085) B9526085
theorem B3573649 : Blo 1881142 3573649 := bstep (se 2 (by rfl) ⟨1340118, by rfl⟩ : syracuseStep 3573649 = 2680237) B2680237
theorem B6350993 : Blo 1881142 6350993 := bstep (se 2 (by rfl) ⟨2381622, by rfl⟩ : syracuseStep 6350993 = 4763245) B4763245
theorem B2681057 : Blo 1881142 2681057 := bstep (se 2 (by rfl) ⟨1005396, by rfl⟩ : syracuseStep 2681057 = 2010793) B2010793
theorem B5089517 : Blo 1881142 5089517 := bstep (se 3 (by rfl) ⟨954284, by rfl⟩ : syracuseStep 5089517 = 1908569) B1908569
theorem B9529649 : Blo 1881142 9529649 := bstep (se 2 (by rfl) ⟨3573618, by rfl⟩ : syracuseStep 9529649 = 7147237) B7147237
theorem B2681137 : Blo 1881142 2681137 := bstep (se 2 (by rfl) ⟨1005426, by rfl⟩ : syracuseStep 2681137 = 2010853) B2010853
theorem B61049285 : Blo 1881142 61049285 := bstep (se 4 (by rfl) ⟨5723370, by rfl⟩ : syracuseStep 61049285 = 11446741) B11446741
theorem B10717667 : Blo 1881142 10717667 := bstep (se 1 (by rfl) ⟨8038250, by rfl⟩ : syracuseStep 10717667 = 16076501) B16076501
theorem B12061169 : Blo 1881142 12061169 := bstep (se 2 (by rfl) ⟨4522938, by rfl⟩ : syracuseStep 12061169 = 9045877) B9045877
theorem B7146083 : Blo 1881142 7146083 := bstep (se 1 (by rfl) ⟨5359562, by rfl⟩ : syracuseStep 7146083 = 10719125) B10719125
theorem B5360269 : Blo 1881142 5360269 := bstep (se 3 (by rfl) ⟨1005050, by rfl⟩ : syracuseStep 5360269 = 2010101) B2010101
theorem B6351533 : Blo 1881142 6351533 := bstep (se 3 (by rfl) ⟨1190912, by rfl⟩ : syracuseStep 6351533 = 2381825) B2381825
theorem B2116291 : Blo 1881142 2116291 := bstep (se 1 (by rfl) ⟨1587218, by rfl⟩ : syracuseStep 2116291 = 3174437) B3174437
theorem B6351587 : Blo 1881142 6351587 := bstep (se 1 (by rfl) ⟨4763690, by rfl⟩ : syracuseStep 6351587 = 9527381) B9527381
theorem B4762385 : Blo 1881142 4762385 := bstep (se 2 (by rfl) ⟨1785894, by rfl⟩ : syracuseStep 4762385 = 3571789) B3571789
theorem B4762435 : Blo 1881142 4762435 := bstep (se 1 (by rfl) ⟨3571826, by rfl⟩ : syracuseStep 4762435 = 7143653) B7143653
theorem B2116435 : Blo 1881142 2116435 := bstep (se 1 (by rfl) ⟨1587326, by rfl⟩ : syracuseStep 2116435 = 3174653) B3174653
theorem B17165155 : Blo 1881142 17165155 := bstep (se 1 (by rfl) ⟨12873866, by rfl⟩ : syracuseStep 17165155 = 25747733) B25747733
theorem B3574705 : Blo 1881142 3574705 := bstep (se 2 (by rfl) ⟨1340514, by rfl⟩ : syracuseStep 3574705 = 2681029) B2681029
theorem B4762577 : Blo 1881142 4762577 := bstep (se 2 (by rfl) ⟨1785966, by rfl⟩ : syracuseStep 4762577 = 3571933) B3571933
theorem B5229521 : Blo 1881142 5229521 := bstep (se 2 (by rfl) ⟨1961070, by rfl⟩ : syracuseStep 5229521 = 3922141) B3922141
theorem B13560803 : Blo 1881142 13560803 := bstep (se 1 (by rfl) ⟨10170602, by rfl⟩ : syracuseStep 13560803 = 20341205) B20341205
theorem B2116579 : Blo 1881142 2116579 := bstep (se 1 (by rfl) ⟨1587434, by rfl⟩ : syracuseStep 2116579 = 3174869) B3174869
theorem B6351857 : Blo 1881142 6351857 := bstep (se 2 (by rfl) ⟨2381946, by rfl⟩ : syracuseStep 6351857 = 4763893) B4763893
theorem B2116723 : Blo 1881142 2116723 := bstep (se 1 (by rfl) ⟨1587542, by rfl⟩ : syracuseStep 2116723 = 3175085) B3175085
theorem B9653411 : Blo 1881142 9653411 := bstep (se 1 (by rfl) ⟨7240058, by rfl⟩ : syracuseStep 9653411 = 14480117) B14480117
theorem B7146737 : Blo 1881142 7146737 := bstep (se 2 (by rfl) ⟨2680026, by rfl⟩ : syracuseStep 7146737 = 5360053) B5360053
theorem B2116867 : Blo 1881142 2116867 := bstep (se 1 (by rfl) ⟨1587650, by rfl⟩ : syracuseStep 2116867 = 3175301) B3175301
theorem B2117011 : Blo 1881142 2117011 := bstep (se 1 (by rfl) ⟨1587758, by rfl⟩ : syracuseStep 2117011 = 3175517) B3175517
theorem B8039857 : Blo 1881142 8039857 := bstep (se 2 (by rfl) ⟨3014946, by rfl⟩ : syracuseStep 8039857 = 6029893) B6029893
theorem B10718669 : Blo 1881142 10718669 := bstep (se 3 (by rfl) ⟨2009750, by rfl⟩ : syracuseStep 10718669 = 4019501) B4019501
theorem B6352397 : Blo 1881142 6352397 := bstep (se 3 (by rfl) ⟨1191074, by rfl⟩ : syracuseStep 6352397 = 2382149) B2382149
theorem B2117155 : Blo 1881142 2117155 := bstep (se 1 (by rfl) ⟨1587866, by rfl⟩ : syracuseStep 2117155 = 3175733) B3175733
theorem B4132387 : Blo 1881142 4132387 := bstep (se 1 (by rfl) ⟨3099290, by rfl⟩ : syracuseStep 4132387 = 6198581) B6198581
theorem B6352451 : Blo 1881142 6352451 := bstep (se 1 (by rfl) ⟨4764338, by rfl⟩ : syracuseStep 6352451 = 9528677) B9528677
theorem B2862659 : Blo 1881142 2862659 := bstep (se 1 (by rfl) ⟨2146994, by rfl⟩ : syracuseStep 2862659 = 4293989) B4293989
theorem B2821715 : Blo 1881142 2821715 := bstep (se 1 (by rfl) ⟨2116286, by rfl⟩ : syracuseStep 2821715 = 4232573) B4232573
theorem B2821745 : Blo 1881142 2821745 := bstep (se 2 (by rfl) ⟨1058154, by rfl⟩ : syracuseStep 2821745 = 2116309) B2116309
theorem B2821763 : Blo 1881142 2821763 := bstep (se 1 (by rfl) ⟨2116322, by rfl⟩ : syracuseStep 2821763 = 4232645) B4232645
theorem B2821793 : Blo 1881142 2821793 := bstep (se 2 (by rfl) ⟨1058172, by rfl⟩ : syracuseStep 2821793 = 2116345) B2116345
theorem B5361329 : Blo 1881142 5361329 := bstep (se 2 (by rfl) ⟨2010498, by rfl⟩ : syracuseStep 5361329 = 4020997) B4020997
theorem B2821811 : Blo 1881142 2821811 := bstep (se 1 (by rfl) ⟨2116358, by rfl⟩ : syracuseStep 2821811 = 4232717) B4232717
theorem B2117299 : Blo 1881142 2117299 := bstep (se 1 (by rfl) ⟨1587974, by rfl⟩ : syracuseStep 2117299 = 3175949) B3175949
theorem B2715329 : Blo 1881142 2715329 := bstep (se 2 (by rfl) ⟨1018248, by rfl⟩ : syracuseStep 2715329 = 2036497) B2036497
theorem B13758149 : Blo 1881142 13758149 := bstep (se 4 (by rfl) ⟨1289826, by rfl⟩ : syracuseStep 13758149 = 2579653) B2579653
theorem B2821841 : Blo 1881142 2821841 := bstep (se 2 (by rfl) ⟨1058190, by rfl⟩ : syracuseStep 2821841 = 2116381) B2116381
theorem B2821859 : Blo 1881142 2821859 := bstep (se 1 (by rfl) ⟨2116394, by rfl⟩ : syracuseStep 2821859 = 4232789) B4232789
theorem B9531107 : Blo 1881142 9531107 := bstep (se 1 (by rfl) ⟨7148330, by rfl⟩ : syracuseStep 9531107 = 14296661) B14296661
theorem B2821889 : Blo 1881142 2821889 := bstep (se 2 (by rfl) ⟨1058208, by rfl⟩ : syracuseStep 2821889 = 2116417) B2116417
theorem B2821907 : Blo 1881142 2821907 := bstep (se 1 (by rfl) ⟨2116430, by rfl⟩ : syracuseStep 2821907 = 4232861) B4232861
theorem B2821937 : Blo 1881142 2821937 := bstep (se 2 (by rfl) ⟨1058226, by rfl⟩ : syracuseStep 2821937 = 2116453) B2116453
theorem B2821955 : Blo 1881142 2821955 := bstep (se 1 (by rfl) ⟨2116466, by rfl⟩ : syracuseStep 2821955 = 4232933) B4232933
theorem B2117443 : Blo 1881142 2117443 := bstep (se 1 (by rfl) ⟨1588082, by rfl⟩ : syracuseStep 2117443 = 3176165) B3176165
theorem B6352721 : Blo 1881142 6352721 := bstep (se 2 (by rfl) ⟨2382270, by rfl⟩ : syracuseStep 6352721 = 4764541) B4764541
theorem B2821985 : Blo 1881142 2821985 := bstep (se 2 (by rfl) ⟨1058244, by rfl⟩ : syracuseStep 2821985 = 2116489) B2116489
theorem B10170211 : Blo 1881142 10170211 := bstep (se 1 (by rfl) ⟨7627658, by rfl⟩ : syracuseStep 10170211 = 15255317) B15255317
theorem B2822003 : Blo 1881142 2822003 := bstep (se 1 (by rfl) ⟨2116502, by rfl⟩ : syracuseStep 2822003 = 4233005) B4233005
theorem B14290829 : Blo 1881142 14290829 := bstep (se 3 (by rfl) ⟨2679530, by rfl⟩ : syracuseStep 14290829 = 5359061) B5359061
theorem B2822033 : Blo 1881142 2822033 := bstep (se 2 (by rfl) ⟨1058262, by rfl⟩ : syracuseStep 2822033 = 2116525) B2116525
theorem B2822051 : Blo 1881142 2822051 := bstep (se 1 (by rfl) ⟨2116538, by rfl⟩ : syracuseStep 2822051 = 4233077) B4233077
theorem B4763569 : Blo 1881142 4763569 := bstep (se 2 (by rfl) ⟨1786338, by rfl⟩ : syracuseStep 4763569 = 3572677) B3572677
theorem B2822081 : Blo 1881142 2822081 := bstep (se 2 (by rfl) ⟨1058280, by rfl⟩ : syracuseStep 2822081 = 2116561) B2116561
theorem B2822099 : Blo 1881142 2822099 := bstep (se 1 (by rfl) ⟨2116574, by rfl⟩ : syracuseStep 2822099 = 4233149) B4233149
theorem B2117587 : Blo 1881142 2117587 := bstep (se 1 (by rfl) ⟨1588190, by rfl⟩ : syracuseStep 2117587 = 3176381) B3176381
theorem B2822129 : Blo 1881142 2822129 := bstep (se 2 (by rfl) ⟨1058298, by rfl⟩ : syracuseStep 2822129 = 2116597) B2116597
theorem B2822147 : Blo 1881142 2822147 := bstep (se 1 (by rfl) ⟨2116610, by rfl⟩ : syracuseStep 2822147 = 4233221) B4233221
theorem B2822177 : Blo 1881142 2822177 := bstep (se 2 (by rfl) ⟨1058316, by rfl⟩ : syracuseStep 2822177 = 2116633) B2116633
theorem B2715697 : Blo 1881142 2715697 := bstep (se 2 (by rfl) ⟨1018386, by rfl⟩ : syracuseStep 2715697 = 2036773) B2036773
theorem B2822195 : Blo 1881142 2822195 := bstep (se 1 (by rfl) ⟨2116646, by rfl⟩ : syracuseStep 2822195 = 4233293) B4233293
theorem B2822225 : Blo 1881142 2822225 := bstep (se 2 (by rfl) ⟨1058334, by rfl⟩ : syracuseStep 2822225 = 2116669) B2116669
theorem B2822243 : Blo 1881142 2822243 := bstep (se 1 (by rfl) ⟨2116682, by rfl⟩ : syracuseStep 2822243 = 4233365) B4233365
theorem B2117731 : Blo 1881142 2117731 := bstep (se 1 (by rfl) ⟨1588298, by rfl⟩ : syracuseStep 2117731 = 3176597) B3176597
theorem B2822273 : Blo 1881142 2822273 := bstep (se 2 (by rfl) ⟨1058352, by rfl⟩ : syracuseStep 2822273 = 2116705) B2116705
theorem B3174545 : Blo 1881142 3174545 := bstep (se 2 (by rfl) ⟨1190454, by rfl⟩ : syracuseStep 3174545 = 2380909) B2380909
theorem B2822291 : Blo 1881142 2822291 := bstep (se 1 (by rfl) ⟨2116718, by rfl⟩ : syracuseStep 2822291 = 4233437) B4233437
theorem B4018339 : Blo 1881142 4018339 := bstep (se 1 (by rfl) ⟨3013754, by rfl⟩ : syracuseStep 4018339 = 6027509) B6027509
theorem B2822321 : Blo 1881142 2822321 := bstep (se 2 (by rfl) ⟨1058370, by rfl⟩ : syracuseStep 2822321 = 2116741) B2116741
theorem B2822339 : Blo 1881142 2822339 := bstep (se 1 (by rfl) ⟨2116754, by rfl⟩ : syracuseStep 2822339 = 4233509) B4233509
theorem B4763843 : Blo 1881142 4763843 := bstep (se 1 (by rfl) ⟨3572882, by rfl⟩ : syracuseStep 4763843 = 7145765) B7145765
theorem B2822369 : Blo 1881142 2822369 := bstep (se 2 (by rfl) ⟨1058388, by rfl⟩ : syracuseStep 2822369 = 2116777) B2116777
theorem B2822387 : Blo 1881142 2822387 := bstep (se 1 (by rfl) ⟨2116790, by rfl⟩ : syracuseStep 2822387 = 4233581) B4233581
theorem B2117875 : Blo 1881142 2117875 := bstep (se 1 (by rfl) ⟨1588406, by rfl⟩ : syracuseStep 2117875 = 3176813) B3176813
theorem B3174673 : Blo 1881142 3174673 := bstep (se 2 (by rfl) ⟨1190502, by rfl⟩ : syracuseStep 3174673 = 2381005) B2381005
theorem B2822417 : Blo 1881142 2822417 := bstep (se 2 (by rfl) ⟨1058406, by rfl⟩ : syracuseStep 2822417 = 2116813) B2116813
theorem B2822435 : Blo 1881142 2822435 := bstep (se 1 (by rfl) ⟨2116826, by rfl⟩ : syracuseStep 2822435 = 4233653) B4233653
theorem B3174707 : Blo 1881142 3174707 := bstep (se 1 (by rfl) ⟨2381030, by rfl⟩ : syracuseStep 3174707 = 4762061) B4762061
theorem B2822465 : Blo 1881142 2822465 := bstep (se 2 (by rfl) ⟨1058424, by rfl⟩ : syracuseStep 2822465 = 2116849) B2116849
theorem B5362001 : Blo 1881142 5362001 := bstep (se 2 (by rfl) ⟨2010750, by rfl⟩ : syracuseStep 5362001 = 4021501) B4021501
theorem B2822483 : Blo 1881142 2822483 := bstep (se 1 (by rfl) ⟨2116862, by rfl⟩ : syracuseStep 2822483 = 4233725) B4233725
theorem B6353261 : Blo 1881142 6353261 := bstep (se 3 (by rfl) ⟨1191236, by rfl⟩ : syracuseStep 6353261 = 2382473) B2382473
theorem B2822513 : Blo 1881142 2822513 := bstep (se 2 (by rfl) ⟨1058442, by rfl⟩ : syracuseStep 2822513 = 2116885) B2116885
theorem B2822531 : Blo 1881142 2822531 := bstep (se 1 (by rfl) ⟨2116898, by rfl⟩ : syracuseStep 2822531 = 4233797) B4233797
theorem B4764035 : Blo 1881142 4764035 := bstep (se 1 (by rfl) ⟨3573026, by rfl⟩ : syracuseStep 4764035 = 7146053) B7146053
theorem B2118019 : Blo 1881142 2118019 := bstep (se 1 (by rfl) ⟨1588514, by rfl⟩ : syracuseStep 2118019 = 3177029) B3177029
theorem B2822561 : Blo 1881142 2822561 := bstep (se 2 (by rfl) ⟨1058460, by rfl⟩ : syracuseStep 2822561 = 2116921) B2116921
theorem B6353315 : Blo 1881142 6353315 := bstep (se 1 (by rfl) ⟨4764986, by rfl⟩ : syracuseStep 6353315 = 9529973) B9529973
theorem B3174835 : Blo 1881142 3174835 := bstep (se 1 (by rfl) ⟨2381126, by rfl⟩ : syracuseStep 3174835 = 4762253) B4762253
theorem B2822579 : Blo 1881142 2822579 := bstep (se 1 (by rfl) ⟨2116934, by rfl⟩ : syracuseStep 2822579 = 4233869) B4233869
theorem B2822609 : Blo 1881142 2822609 := bstep (se 2 (by rfl) ⟨1058478, by rfl⟩ : syracuseStep 2822609 = 2116957) B2116957
theorem B2822627 : Blo 1881142 2822627 := bstep (se 1 (by rfl) ⟨2116970, by rfl⟩ : syracuseStep 2822627 = 4233941) B4233941
theorem B4018673 : Blo 1881142 4018673 := bstep (se 2 (by rfl) ⟨1507002, by rfl⟩ : syracuseStep 4018673 = 3014005) B3014005
theorem B2822657 : Blo 1881142 2822657 := bstep (se 2 (by rfl) ⟨1058496, by rfl⟩ : syracuseStep 2822657 = 2116993) B2116993
theorem B9531917 : Blo 1881142 9531917 := bstep (se 3 (by rfl) ⟨1787234, by rfl⟩ : syracuseStep 9531917 = 3574469) B3574469
theorem B2822675 : Blo 1881142 2822675 := bstep (se 1 (by rfl) ⟨2117006, by rfl⟩ : syracuseStep 2822675 = 4234013) B4234013
theorem B2118163 : Blo 1881142 2118163 := bstep (se 1 (by rfl) ⟨1588622, by rfl⟩ : syracuseStep 2118163 = 3177245) B3177245
theorem B2822705 : Blo 1881142 2822705 := bstep (se 2 (by rfl) ⟨1058514, by rfl⟩ : syracuseStep 2822705 = 2117029) B2117029
theorem B3174977 : Blo 1881142 3174977 := bstep (se 2 (by rfl) ⟨1190616, by rfl⟩ : syracuseStep 3174977 = 2381233) B2381233
theorem B2822723 : Blo 1881142 2822723 := bstep (se 1 (by rfl) ⟨2117042, by rfl⟩ : syracuseStep 2822723 = 4234085) B4234085
theorem B2822753 : Blo 1881142 2822753 := bstep (se 2 (by rfl) ⟨1058532, by rfl⟩ : syracuseStep 2822753 = 2117065) B2117065
theorem B2822771 : Blo 1881142 2822771 := bstep (se 1 (by rfl) ⟨2117078, by rfl⟩ : syracuseStep 2822771 = 4234157) B4234157
theorem B2822801 : Blo 1881142 2822801 := bstep (se 2 (by rfl) ⟨1058550, by rfl⟩ : syracuseStep 2822801 = 2117101) B2117101
theorem B2822819 : Blo 1881142 2822819 := bstep (se 1 (by rfl) ⟨2117114, by rfl⟩ : syracuseStep 2822819 = 4234229) B4234229
theorem B7148195 : Blo 1881142 7148195 := bstep (se 1 (by rfl) ⟨5361146, by rfl⟩ : syracuseStep 7148195 = 10722293) B10722293
theorem B2118307 : Blo 1881142 2118307 := bstep (se 1 (by rfl) ⟨1588730, by rfl⟩ : syracuseStep 2118307 = 3177461) B3177461
theorem B6353585 : Blo 1881142 6353585 := bstep (se 2 (by rfl) ⟨2382594, by rfl⟩ : syracuseStep 6353585 = 4765189) B4765189
theorem B7148209 : Blo 1881142 7148209 := bstep (se 2 (by rfl) ⟨2680578, by rfl⟩ : syracuseStep 7148209 = 5361157) B5361157
theorem B3175105 : Blo 1881142 3175105 := bstep (se 2 (by rfl) ⟨1190664, by rfl⟩ : syracuseStep 3175105 = 2381329) B2381329
theorem B2822849 : Blo 1881142 2822849 := bstep (se 2 (by rfl) ⟨1058568, by rfl⟩ : syracuseStep 2822849 = 2117137) B2117137
theorem B2822867 : Blo 1881142 2822867 := bstep (se 1 (by rfl) ⟨2117150, by rfl⟩ : syracuseStep 2822867 = 4234301) B4234301
theorem B3175139 : Blo 1881142 3175139 := bstep (se 1 (by rfl) ⟨2381354, by rfl⟩ : syracuseStep 3175139 = 4762709) B4762709
theorem B2822897 : Blo 1881142 2822897 := bstep (se 2 (by rfl) ⟨1058586, by rfl⟩ : syracuseStep 2822897 = 2117173) B2117173
theorem B2822915 : Blo 1881142 2822915 := bstep (se 1 (by rfl) ⟨2117186, by rfl⟩ : syracuseStep 2822915 = 4234373) B4234373
theorem B2822945 : Blo 1881142 2822945 := bstep (se 2 (by rfl) ⟨1058604, by rfl⟩ : syracuseStep 2822945 = 2117209) B2117209
theorem B2822963 : Blo 1881142 2822963 := bstep (se 1 (by rfl) ⟨2117222, by rfl⟩ : syracuseStep 2822963 = 4234445) B4234445
theorem B2118451 : Blo 1881142 2118451 := bstep (se 1 (by rfl) ⟨1588838, by rfl⟩ : syracuseStep 2118451 = 3177677) B3177677
theorem B2822993 : Blo 1881142 2822993 := bstep (se 2 (by rfl) ⟨1058622, by rfl⟩ : syracuseStep 2822993 = 2117245) B2117245
theorem B3175267 : Blo 1881142 3175267 := bstep (se 1 (by rfl) ⟨2381450, by rfl⟩ : syracuseStep 3175267 = 4762901) B4762901
theorem B2823011 : Blo 1881142 2823011 := bstep (se 1 (by rfl) ⟨2117258, by rfl⟩ : syracuseStep 2823011 = 4234517) B4234517
theorem B2823041 : Blo 1881142 2823041 := bstep (se 2 (by rfl) ⟨1058640, by rfl⟩ : syracuseStep 2823041 = 2117281) B2117281
theorem B12063629 : Blo 1881142 12063629 := bstep (se 3 (by rfl) ⟨2261930, by rfl⟩ : syracuseStep 12063629 = 4523861) B4523861
theorem B2823059 : Blo 1881142 2823059 := bstep (se 1 (by rfl) ⟨2117294, by rfl⟩ : syracuseStep 2823059 = 4234589) B4234589
theorem B2823089 : Blo 1881142 2823089 := bstep (se 2 (by rfl) ⟨1058658, by rfl⟩ : syracuseStep 2823089 = 2117317) B2117317
theorem B2823107 : Blo 1881142 2823107 := bstep (se 1 (by rfl) ⟨2117330, by rfl⟩ : syracuseStep 2823107 = 4234661) B4234661
theorem B2413523 : Blo 1881142 2413523 := bstep (se 1 (by rfl) ⟨1810142, by rfl⟩ : syracuseStep 2413523 = 3620285) B3620285
theorem B2823137 : Blo 1881142 2823137 := bstep (se 2 (by rfl) ⟨1058676, by rfl⟩ : syracuseStep 2823137 = 2117353) B2117353
theorem B3175409 : Blo 1881142 3175409 := bstep (se 2 (by rfl) ⟨1190778, by rfl⟩ : syracuseStep 3175409 = 2381557) B2381557
theorem B2823155 : Blo 1881142 2823155 := bstep (se 1 (by rfl) ⟨2117366, by rfl⟩ : syracuseStep 2823155 = 4234733) B4234733
theorem B2823185 : Blo 1881142 2823185 := bstep (se 2 (by rfl) ⟨1058694, by rfl⟩ : syracuseStep 2823185 = 2117389) B2117389
theorem B2823203 : Blo 1881142 2823203 := bstep (se 1 (by rfl) ⟨2117402, by rfl⟩ : syracuseStep 2823203 = 4234805) B4234805
theorem B6878243 : Blo 1881142 6878243 := bstep (se 1 (by rfl) ⟨5158682, by rfl⟩ : syracuseStep 6878243 = 10317365) B10317365
theorem B2823233 : Blo 1881142 2823233 := bstep (se 2 (by rfl) ⟨1058712, by rfl⟩ : syracuseStep 2823233 = 2117425) B2117425
theorem B1881155 : Blo 1881142 1881155 := bstep (se 1 (by rfl) ⟨1410866, by rfl⟩ : syracuseStep 1881155 = 2821733) B2821733
theorem B1881171 : Blo 1881142 1881171 := bstep (se 1 (by rfl) ⟨1410878, by rfl⟩ : syracuseStep 1881171 = 2821757) B2821757
theorem B2823251 : Blo 1881142 2823251 := bstep (se 1 (by rfl) ⟨2117438, by rfl⟩ : syracuseStep 2823251 = 4234877) B4234877
theorem B1881187 : Blo 1881142 1881187 := bstep (se 1 (by rfl) ⟨1410890, by rfl⟩ : syracuseStep 1881187 = 2821781) B2821781
theorem B2544737 : Blo 1881142 2544737 := bstep (se 2 (by rfl) ⟨954276, by rfl⟩ : syracuseStep 2544737 = 1908553) B1908553
theorem B6435949 : Blo 1881142 6435949 := bstep (se 3 (by rfl) ⟨1206740, by rfl⟩ : syracuseStep 6435949 = 2413481) B2413481
theorem B3175537 : Blo 1881142 3175537 := bstep (se 2 (by rfl) ⟨1190826, by rfl⟩ : syracuseStep 3175537 = 2381653) B2381653
theorem B2823281 : Blo 1881142 2823281 := bstep (se 2 (by rfl) ⟨1058730, by rfl⟩ : syracuseStep 2823281 = 2117461) B2117461
theorem B1881203 : Blo 1881142 1881203 := bstep (se 1 (by rfl) ⟨1410902, by rfl⟩ : syracuseStep 1881203 = 2821805) B2821805
theorem B1881219 : Blo 1881142 1881219 := bstep (se 1 (by rfl) ⟨1410914, by rfl⟩ : syracuseStep 1881219 = 2821829) B2821829
theorem B2823299 : Blo 1881142 2823299 := bstep (se 1 (by rfl) ⟨2117474, by rfl⟩ : syracuseStep 2823299 = 4234949) B4234949
theorem B1881235 : Blo 1881142 1881235 := bstep (se 1 (by rfl) ⟨1410926, by rfl⟩ : syracuseStep 1881235 = 2821853) B2821853
theorem B3175571 : Blo 1881142 3175571 := bstep (se 1 (by rfl) ⟨2381678, by rfl⟩ : syracuseStep 3175571 = 4763357) B4763357
theorem B2823329 : Blo 1881142 2823329 := bstep (se 2 (by rfl) ⟨1058748, by rfl⟩ : syracuseStep 2823329 = 2117497) B2117497
theorem B1881251 : Blo 1881142 1881251 := bstep (se 1 (by rfl) ⟨1410938, by rfl⟩ : syracuseStep 1881251 = 2821877) B2821877
theorem B1881267 : Blo 1881142 1881267 := bstep (se 1 (by rfl) ⟨1410950, by rfl⟩ : syracuseStep 1881267 = 2821901) B2821901
theorem B2823347 : Blo 1881142 2823347 := bstep (se 1 (by rfl) ⟨2117510, by rfl⟩ : syracuseStep 2823347 = 4235021) B4235021
theorem B1881283 : Blo 1881142 1881283 := bstep (se 1 (by rfl) ⟨1410962, by rfl⟩ : syracuseStep 1881283 = 2821925) B2821925
theorem B6354125 : Blo 1881142 6354125 := bstep (se 3 (by rfl) ⟨1191398, by rfl⟩ : syracuseStep 6354125 = 2382797) B2382797
theorem B3814609 : Blo 1881142 3814609 := bstep (se 2 (by rfl) ⟨1430478, by rfl⟩ : syracuseStep 3814609 = 2860957) B2860957
theorem B2823377 : Blo 1881142 2823377 := bstep (se 2 (by rfl) ⟨1058766, by rfl⟩ : syracuseStep 2823377 = 2117533) B2117533
theorem B1881299 : Blo 1881142 1881299 := bstep (se 1 (by rfl) ⟨1410974, by rfl⟩ : syracuseStep 1881299 = 2821949) B2821949
theorem B1881315 : Blo 1881142 1881315 := bstep (se 1 (by rfl) ⟨1410986, by rfl⟩ : syracuseStep 1881315 = 2821973) B2821973
theorem B2823395 : Blo 1881142 2823395 := bstep (se 1 (by rfl) ⟨2117546, by rfl⟩ : syracuseStep 2823395 = 4235093) B4235093
theorem B9524465 : Blo 1881142 9524465 := bstep (se 2 (by rfl) ⟨3571674, by rfl⟩ : syracuseStep 9524465 = 7143349) B7143349
theorem B1881331 : Blo 1881142 1881331 := bstep (se 1 (by rfl) ⟨1410998, by rfl⟩ : syracuseStep 1881331 = 2821997) B2821997
theorem B2823425 : Blo 1881142 2823425 := bstep (se 2 (by rfl) ⟨1058784, by rfl⟩ : syracuseStep 2823425 = 2117569) B2117569
theorem B1881347 : Blo 1881142 1881347 := bstep (se 1 (by rfl) ⟨1411010, by rfl⟩ : syracuseStep 1881347 = 2822021) B2822021
theorem B6354179 : Blo 1881142 6354179 := bstep (se 1 (by rfl) ⟨4765634, by rfl⟩ : syracuseStep 6354179 = 9531269) B9531269
theorem B1881363 : Blo 1881142 1881363 := bstep (se 1 (by rfl) ⟨1411022, by rfl⟩ : syracuseStep 1881363 = 2822045) B2822045
theorem B3175699 : Blo 1881142 3175699 := bstep (se 1 (by rfl) ⟨2381774, by rfl⟩ : syracuseStep 3175699 = 4763549) B4763549
theorem B2823443 : Blo 1881142 2823443 := bstep (se 1 (by rfl) ⟨2117582, by rfl⟩ : syracuseStep 2823443 = 4235165) B4235165
theorem B1881379 : Blo 1881142 1881379 := bstep (se 1 (by rfl) ⟨1411034, by rfl⟩ : syracuseStep 1881379 = 2822069) B2822069
theorem B2823473 : Blo 1881142 2823473 := bstep (se 2 (by rfl) ⟨1058802, by rfl⟩ : syracuseStep 2823473 = 2117605) B2117605
theorem B4764977 : Blo 1881142 4764977 := bstep (se 2 (by rfl) ⟨1786866, by rfl⟩ : syracuseStep 4764977 = 3573733) B3573733
theorem B1881395 : Blo 1881142 1881395 := bstep (se 1 (by rfl) ⟨1411046, by rfl⟩ : syracuseStep 1881395 = 2822093) B2822093
theorem B1881411 : Blo 1881142 1881411 := bstep (se 1 (by rfl) ⟨1411058, by rfl⟩ : syracuseStep 1881411 = 2822117) B2822117
theorem B2413891 : Blo 1881142 2413891 := bstep (se 1 (by rfl) ⟨1810418, by rfl⟩ : syracuseStep 2413891 = 3620837) B3620837
theorem B2823491 : Blo 1881142 2823491 := bstep (se 1 (by rfl) ⟨2117618, by rfl⟩ : syracuseStep 2823491 = 4235237) B4235237
theorem B8041805 : Blo 1881142 8041805 := bstep (se 3 (by rfl) ⟨1507838, by rfl⟩ : syracuseStep 8041805 = 3015677) B3015677
theorem B1881427 : Blo 1881142 1881427 := bstep (se 1 (by rfl) ⟨1411070, by rfl⟩ : syracuseStep 1881427 = 2822141) B2822141
theorem B2823521 : Blo 1881142 2823521 := bstep (se 2 (by rfl) ⟨1058820, by rfl⟩ : syracuseStep 2823521 = 2117641) B2117641
theorem B1881443 : Blo 1881142 1881443 := bstep (se 1 (by rfl) ⟨1411082, by rfl⟩ : syracuseStep 1881443 = 2822165) B2822165
theorem B4765027 : Blo 1881142 4765027 := bstep (se 1 (by rfl) ⟨3573770, by rfl⟩ : syracuseStep 4765027 = 7147541) B7147541
theorem B1881459 : Blo 1881142 1881459 := bstep (se 1 (by rfl) ⟨1411094, by rfl⟩ : syracuseStep 1881459 = 2822189) B2822189
theorem B2823539 : Blo 1881142 2823539 := bstep (se 1 (by rfl) ⟨2117654, by rfl⟩ : syracuseStep 2823539 = 4235309) B4235309
theorem B1881475 : Blo 1881142 1881475 := bstep (se 1 (by rfl) ⟨1411106, by rfl⟩ : syracuseStep 1881475 = 2822213) B2822213
theorem B2823569 : Blo 1881142 2823569 := bstep (se 2 (by rfl) ⟨1058838, by rfl⟩ : syracuseStep 2823569 = 2117677) B2117677
theorem B1881491 : Blo 1881142 1881491 := bstep (se 1 (by rfl) ⟨1411118, by rfl⟩ : syracuseStep 1881491 = 2822237) B2822237
theorem B3175841 : Blo 1881142 3175841 := bstep (se 2 (by rfl) ⟨1190940, by rfl⟩ : syracuseStep 3175841 = 2381881) B2381881
theorem B1881507 : Blo 1881142 1881507 := bstep (se 1 (by rfl) ⟨1411130, by rfl⟩ : syracuseStep 1881507 = 2822261) B2822261
theorem B2823587 : Blo 1881142 2823587 := bstep (se 1 (by rfl) ⟨2117690, by rfl⟩ : syracuseStep 2823587 = 4235381) B4235381
theorem B1881523 : Blo 1881142 1881523 := bstep (se 1 (by rfl) ⟨1411142, by rfl⟩ : syracuseStep 1881523 = 2822285) B2822285
theorem B2823617 : Blo 1881142 2823617 := bstep (se 2 (by rfl) ⟨1058856, by rfl⟩ : syracuseStep 2823617 = 2117713) B2117713
theorem B1881539 : Blo 1881142 1881539 := bstep (se 1 (by rfl) ⟨1411154, by rfl⟩ : syracuseStep 1881539 = 2822309) B2822309
theorem B16078277 : Blo 1881142 16078277 := bstep (se 4 (by rfl) ⟨1507338, by rfl⟩ : syracuseStep 16078277 = 3014677) B3014677
theorem B1881555 : Blo 1881142 1881555 := bstep (se 1 (by rfl) ⟨1411166, by rfl⟩ : syracuseStep 1881555 = 2822333) B2822333
theorem B2823635 : Blo 1881142 2823635 := bstep (se 1 (by rfl) ⟨2117726, by rfl⟩ : syracuseStep 2823635 = 4235453) B4235453
theorem B1881571 : Blo 1881142 1881571 := bstep (se 1 (by rfl) ⟨1411178, by rfl⟩ : syracuseStep 1881571 = 2822357) B2822357
theorem B2823665 : Blo 1881142 2823665 := bstep (se 2 (by rfl) ⟨1058874, by rfl⟩ : syracuseStep 2823665 = 2117749) B2117749
theorem B4765169 : Blo 1881142 4765169 := bstep (se 2 (by rfl) ⟨1786938, by rfl⟩ : syracuseStep 4765169 = 3573877) B3573877
theorem B1881587 : Blo 1881142 1881587 := bstep (se 1 (by rfl) ⟨1411190, by rfl⟩ : syracuseStep 1881587 = 2822381) B2822381
theorem B1881603 : Blo 1881142 1881603 := bstep (se 1 (by rfl) ⟨1411202, by rfl⟩ : syracuseStep 1881603 = 2822405) B2822405
theorem B2823683 : Blo 1881142 2823683 := bstep (se 1 (by rfl) ⟨2117762, by rfl⟩ : syracuseStep 2823683 = 4235525) B4235525
theorem B1881619 : Blo 1881142 1881619 := bstep (se 1 (by rfl) ⟨1411214, by rfl⟩ : syracuseStep 1881619 = 2822429) B2822429
theorem B6354449 : Blo 1881142 6354449 := bstep (se 2 (by rfl) ⟨2382918, by rfl⟩ : syracuseStep 6354449 = 4765837) B4765837
theorem B3175969 : Blo 1881142 3175969 := bstep (se 2 (by rfl) ⟨1190988, by rfl⟩ : syracuseStep 3175969 = 2381977) B2381977
theorem B2823713 : Blo 1881142 2823713 := bstep (se 2 (by rfl) ⟨1058892, by rfl⟩ : syracuseStep 2823713 = 2117785) B2117785
theorem B1881635 : Blo 1881142 1881635 := bstep (se 1 (by rfl) ⟨1411226, by rfl⟩ : syracuseStep 1881635 = 2822453) B2822453
theorem B4232753 : Blo 1881142 4232753 := bstep (se 2 (by rfl) ⟨1587282, by rfl⟩ : syracuseStep 4232753 = 3174565) B3174565
theorem B1881651 : Blo 1881142 1881651 := bstep (se 1 (by rfl) ⟨1411238, by rfl⟩ : syracuseStep 1881651 = 2822477) B2822477
theorem B2823731 : Blo 1881142 2823731 := bstep (se 1 (by rfl) ⟨2117798, by rfl⟩ : syracuseStep 2823731 = 4235597) B4235597
theorem B4232771 : Blo 1881142 4232771 := bstep (se 1 (by rfl) ⟨3174578, by rfl⟩ : syracuseStep 4232771 = 6349157) B6349157
theorem B1881667 : Blo 1881142 1881667 := bstep (se 1 (by rfl) ⟨1411250, by rfl⟩ : syracuseStep 1881667 = 2822501) B2822501
theorem B3176003 : Blo 1881142 3176003 := bstep (se 1 (by rfl) ⟨2382002, by rfl⟩ : syracuseStep 3176003 = 4764005) B4764005
theorem B2823761 : Blo 1881142 2823761 := bstep (se 2 (by rfl) ⟨1058910, by rfl⟩ : syracuseStep 2823761 = 2117821) B2117821
theorem B2381395 : Blo 1881142 2381395 := bstep (se 1 (by rfl) ⟨1786046, by rfl⟩ : syracuseStep 2381395 = 3572093) B3572093
theorem B1881683 : Blo 1881142 1881683 := bstep (se 1 (by rfl) ⟨1411262, by rfl⟩ : syracuseStep 1881683 = 2822525) B2822525
theorem B1881699 : Blo 1881142 1881699 := bstep (se 1 (by rfl) ⟨1411274, by rfl⟩ : syracuseStep 1881699 = 2822549) B2822549
theorem B2823779 : Blo 1881142 2823779 := bstep (se 1 (by rfl) ⟨2117834, by rfl⟩ : syracuseStep 2823779 = 4235669) B4235669
theorem B1881715 : Blo 1881142 1881715 := bstep (se 1 (by rfl) ⟨1411286, by rfl⟩ : syracuseStep 1881715 = 2822573) B2822573
theorem B2823809 : Blo 1881142 2823809 := bstep (se 2 (by rfl) ⟨1058928, by rfl⟩ : syracuseStep 2823809 = 2117857) B2117857
theorem B1881731 : Blo 1881142 1881731 := bstep (se 1 (by rfl) ⟨1411298, by rfl⟩ : syracuseStep 1881731 = 2822597) B2822597
theorem B4019843 : Blo 1881142 4019843 := bstep (se 1 (by rfl) ⟨3014882, by rfl⟩ : syracuseStep 4019843 = 6029765) B6029765
theorem B1881747 : Blo 1881142 1881747 := bstep (se 1 (by rfl) ⟨1411310, by rfl⟩ : syracuseStep 1881747 = 2822621) B2822621
theorem B2823827 : Blo 1881142 2823827 := bstep (se 1 (by rfl) ⟨2117870, by rfl⟩ : syracuseStep 2823827 = 4235741) B4235741
theorem B1881763 : Blo 1881142 1881763 := bstep (se 1 (by rfl) ⟨1411322, by rfl⟩ : syracuseStep 1881763 = 2822645) B2822645
theorem B2823857 : Blo 1881142 2823857 := bstep (se 2 (by rfl) ⟨1058946, by rfl⟩ : syracuseStep 2823857 = 2117893) B2117893
theorem B2381491 : Blo 1881142 2381491 := bstep (se 1 (by rfl) ⟨1786118, by rfl⟩ : syracuseStep 2381491 = 3572237) B3572237
theorem B1881779 : Blo 1881142 1881779 := bstep (se 1 (by rfl) ⟨1411334, by rfl⟩ : syracuseStep 1881779 = 2822669) B2822669
theorem B1881795 : Blo 1881142 1881795 := bstep (se 1 (by rfl) ⟨1411346, by rfl⟩ : syracuseStep 1881795 = 2822693) B2822693
theorem B3176131 : Blo 1881142 3176131 := bstep (se 1 (by rfl) ⟨2382098, by rfl⟩ : syracuseStep 3176131 = 4764197) B4764197
theorem B2823875 : Blo 1881142 2823875 := bstep (se 1 (by rfl) ⟨2117906, by rfl⟩ : syracuseStep 2823875 = 4235813) B4235813
theorem B1881811 : Blo 1881142 1881811 := bstep (se 1 (by rfl) ⟨1411358, by rfl⟩ : syracuseStep 1881811 = 2822717) B2822717
theorem B2823905 : Blo 1881142 2823905 := bstep (se 2 (by rfl) ⟨1058964, by rfl⟩ : syracuseStep 2823905 = 2117929) B2117929
theorem B1881827 : Blo 1881142 1881827 := bstep (se 1 (by rfl) ⟨1411370, by rfl⟩ : syracuseStep 1881827 = 2822741) B2822741
theorem B5723885 : Blo 1881142 5723885 := bstep (se 3 (by rfl) ⟨1073228, by rfl⟩ : syracuseStep 5723885 = 2146457) B2146457
theorem B8148721 : Blo 1881142 8148721 := bstep (se 2 (by rfl) ⟨3055770, by rfl⟩ : syracuseStep 8148721 = 6111541) B6111541
theorem B1881843 : Blo 1881142 1881843 := bstep (se 1 (by rfl) ⟨1411382, by rfl⟩ : syracuseStep 1881843 = 2822765) B2822765
theorem B2823923 : Blo 1881142 2823923 := bstep (se 1 (by rfl) ⟨2117942, by rfl⟩ : syracuseStep 2823923 = 4235885) B4235885
theorem B1881859 : Blo 1881142 1881859 := bstep (se 1 (by rfl) ⟨1411394, by rfl⟩ : syracuseStep 1881859 = 2822789) B2822789
theorem B10860293 : Blo 1881142 10860293 := bstep (se 4 (by rfl) ⟨1018152, by rfl⟩ : syracuseStep 10860293 = 2036305) B2036305
theorem B6616849 : Blo 1881142 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B2823953 : Blo 1881142 2823953 := bstep (se 2 (by rfl) ⟨1058982, by rfl⟩ : syracuseStep 2823953 = 2117965) B2117965
theorem B1881875 : Blo 1881142 1881875 := bstep (se 1 (by rfl) ⟨1411406, by rfl⟩ : syracuseStep 1881875 = 2822813) B2822813
theorem B1881891 : Blo 1881142 1881891 := bstep (se 1 (by rfl) ⟨1411418, by rfl⟩ : syracuseStep 1881891 = 2822837) B2822837
theorem B2823971 : Blo 1881142 2823971 := bstep (se 1 (by rfl) ⟨2117978, by rfl⟩ : syracuseStep 2823971 = 4235957) B4235957
theorem B5084977 : Blo 1881142 5084977 := bstep (se 2 (by rfl) ⟨1906866, by rfl⟩ : syracuseStep 5084977 = 3813733) B3813733
theorem B1881907 : Blo 1881142 1881907 := bstep (se 1 (by rfl) ⟨1411430, by rfl⟩ : syracuseStep 1881907 = 2822861) B2822861
theorem B2824001 : Blo 1881142 2824001 := bstep (se 2 (by rfl) ⟨1059000, by rfl⟩ : syracuseStep 2824001 = 2118001) B2118001
theorem B1881923 : Blo 1881142 1881923 := bstep (se 1 (by rfl) ⟨1411442, by rfl⟩ : syracuseStep 1881923 = 2822885) B2822885
theorem B4233041 : Blo 1881142 4233041 := bstep (se 2 (by rfl) ⟨1587390, by rfl⟩ : syracuseStep 4233041 = 3174781) B3174781
theorem B3176273 : Blo 1881142 3176273 := bstep (se 2 (by rfl) ⟨1191102, by rfl⟩ : syracuseStep 3176273 = 2382205) B2382205
theorem B1881939 : Blo 1881142 1881939 := bstep (se 1 (by rfl) ⟨1411454, by rfl⟩ : syracuseStep 1881939 = 2822909) B2822909
theorem B2824019 : Blo 1881142 2824019 := bstep (se 1 (by rfl) ⟨2118014, by rfl⟩ : syracuseStep 2824019 = 4236029) B4236029
theorem B4233059 : Blo 1881142 4233059 := bstep (se 1 (by rfl) ⟨3174794, by rfl⟩ : syracuseStep 4233059 = 6349589) B6349589
theorem B1881955 : Blo 1881142 1881955 := bstep (se 1 (by rfl) ⟨1411466, by rfl⟩ : syracuseStep 1881955 = 2822933) B2822933
theorem B2824049 : Blo 1881142 2824049 := bstep (se 2 (by rfl) ⟨1059018, by rfl⟩ : syracuseStep 2824049 = 2118037) B2118037
theorem B1881971 : Blo 1881142 1881971 := bstep (se 1 (by rfl) ⟨1411478, by rfl⟩ : syracuseStep 1881971 = 2822957) B2822957
theorem B1881987 : Blo 1881142 1881987 := bstep (se 1 (by rfl) ⟨1411490, by rfl⟩ : syracuseStep 1881987 = 2822981) B2822981
theorem B2824067 : Blo 1881142 2824067 := bstep (se 1 (by rfl) ⟨2118050, by rfl⟩ : syracuseStep 2824067 = 4236101) B4236101
theorem B15472525 : Blo 1881142 15472525 := bstep (se 3 (by rfl) ⟨2901098, by rfl⟩ : syracuseStep 15472525 = 5802197) B5802197
theorem B1882003 : Blo 1881142 1882003 := bstep (se 1 (by rfl) ⟨1411502, by rfl⟩ : syracuseStep 1882003 = 2823005) B2823005
theorem B2824097 : Blo 1881142 2824097 := bstep (se 2 (by rfl) ⟨1059036, by rfl⟩ : syracuseStep 2824097 = 2118073) B2118073
theorem B1882019 : Blo 1881142 1882019 := bstep (se 1 (by rfl) ⟨1411514, by rfl⟩ : syracuseStep 1882019 = 2823029) B2823029
theorem B4831139 : Blo 1881142 4831139 := bstep (se 1 (by rfl) ⟨3623354, by rfl⟩ : syracuseStep 4831139 = 7246709) B7246709
theorem B1882035 : Blo 1881142 1882035 := bstep (se 1 (by rfl) ⟨1411526, by rfl⟩ : syracuseStep 1882035 = 2823053) B2823053
theorem B2824115 : Blo 1881142 2824115 := bstep (se 1 (by rfl) ⟨2118086, by rfl⟩ : syracuseStep 2824115 = 4236173) B4236173
theorem B1882051 : Blo 1881142 1882051 := bstep (se 1 (by rfl) ⟨1411538, by rfl⟩ : syracuseStep 1882051 = 2823077) B2823077
theorem B3176401 : Blo 1881142 3176401 := bstep (se 2 (by rfl) ⟨1191150, by rfl⟩ : syracuseStep 3176401 = 2382301) B2382301
theorem B2824145 : Blo 1881142 2824145 := bstep (se 2 (by rfl) ⟨1059054, by rfl⟩ : syracuseStep 2824145 = 2118109) B2118109
theorem B1882067 : Blo 1881142 1882067 := bstep (se 1 (by rfl) ⟨1411550, by rfl⟩ : syracuseStep 1882067 = 2823101) B2823101
theorem B1882083 : Blo 1881142 1882083 := bstep (se 1 (by rfl) ⟨1411562, by rfl⟩ : syracuseStep 1882083 = 2823125) B2823125
theorem B2824163 : Blo 1881142 2824163 := bstep (se 1 (by rfl) ⟨2118122, by rfl⟩ : syracuseStep 2824163 = 4236245) B4236245
theorem B16087025 : Blo 1881142 16087025 := bstep (se 2 (by rfl) ⟨6032634, by rfl⟩ : syracuseStep 16087025 = 12065269) B12065269
theorem B1882099 : Blo 1881142 1882099 := bstep (se 1 (by rfl) ⟨1411574, by rfl⟩ : syracuseStep 1882099 = 2823149) B2823149
theorem B3176435 : Blo 1881142 3176435 := bstep (se 1 (by rfl) ⟨2382326, by rfl⟩ : syracuseStep 3176435 = 4764653) B4764653
theorem B1882115 : Blo 1881142 1882115 := bstep (se 1 (by rfl) ⟨1411586, by rfl⟩ : syracuseStep 1882115 = 2823173) B2823173
theorem B2824193 : Blo 1881142 2824193 := bstep (se 2 (by rfl) ⟨1059072, by rfl⟩ : syracuseStep 2824193 = 2118145) B2118145
theorem B1882131 : Blo 1881142 1882131 := bstep (se 1 (by rfl) ⟨1411598, by rfl⟩ : syracuseStep 1882131 = 2823197) B2823197
theorem B2824211 : Blo 1881142 2824211 := bstep (se 1 (by rfl) ⟨2118158, by rfl⟩ : syracuseStep 2824211 = 4236317) B4236317
theorem B1882147 : Blo 1881142 1882147 := bstep (se 1 (by rfl) ⟨1411610, by rfl⟩ : syracuseStep 1882147 = 2823221) B2823221
theorem B6354989 : Blo 1881142 6354989 := bstep (se 3 (by rfl) ⟨1191560, by rfl⟩ : syracuseStep 6354989 = 2383121) B2383121
theorem B2824241 : Blo 1881142 2824241 := bstep (se 2 (by rfl) ⟨1059090, by rfl⟩ : syracuseStep 2824241 = 2118181) B2118181
theorem B1882163 : Blo 1881142 1882163 := bstep (se 1 (by rfl) ⟨1411622, by rfl⟩ : syracuseStep 1882163 = 2823245) B2823245
theorem B6027331 : Blo 1881142 6027331 := bstep (se 1 (by rfl) ⟨4520498, by rfl⟩ : syracuseStep 6027331 = 9040997) B9040997
theorem B1882179 : Blo 1881142 1882179 := bstep (se 1 (by rfl) ⟨1411634, by rfl⟩ : syracuseStep 1882179 = 2823269) B2823269
theorem B2824259 : Blo 1881142 2824259 := bstep (se 1 (by rfl) ⟨2118194, by rfl⟩ : syracuseStep 2824259 = 4236389) B4236389
theorem B1882195 : Blo 1881142 1882195 := bstep (se 1 (by rfl) ⟨1411646, by rfl⟩ : syracuseStep 1882195 = 2823293) B2823293
theorem B1882211 : Blo 1881142 1882211 := bstep (se 1 (by rfl) ⟨1411658, by rfl⟩ : syracuseStep 1882211 = 2823317) B2823317
theorem B2824289 : Blo 1881142 2824289 := bstep (se 2 (by rfl) ⟨1059108, by rfl⟩ : syracuseStep 2824289 = 2118217) B2118217
theorem B6355043 : Blo 1881142 6355043 := bstep (se 1 (by rfl) ⟨4766282, by rfl⟩ : syracuseStep 6355043 = 9532565) B9532565
theorem B7149667 : Blo 1881142 7149667 := bstep (se 1 (by rfl) ⟨5362250, by rfl⟩ : syracuseStep 7149667 = 10724501) B10724501
theorem B4233329 : Blo 1881142 4233329 := bstep (se 2 (by rfl) ⟨1587498, by rfl⟩ : syracuseStep 4233329 = 3174997) B3174997
theorem B1882227 : Blo 1881142 1882227 := bstep (se 1 (by rfl) ⟨1411670, by rfl⟩ : syracuseStep 1882227 = 2823341) B2823341
theorem B3176563 : Blo 1881142 3176563 := bstep (se 1 (by rfl) ⟨2382422, by rfl⟩ : syracuseStep 3176563 = 4764845) B4764845
theorem B2824307 : Blo 1881142 2824307 := bstep (se 1 (by rfl) ⟨2118230, by rfl⟩ : syracuseStep 2824307 = 4236461) B4236461
theorem B4233347 : Blo 1881142 4233347 := bstep (se 1 (by rfl) ⟨3175010, by rfl⟩ : syracuseStep 4233347 = 6350021) B6350021
theorem B1882243 : Blo 1881142 1882243 := bstep (se 1 (by rfl) ⟨1411682, by rfl⟩ : syracuseStep 1882243 = 2823365) B2823365
theorem B2824337 : Blo 1881142 2824337 := bstep (se 2 (by rfl) ⟨1059126, by rfl⟩ : syracuseStep 2824337 = 2118253) B2118253
theorem B1882259 : Blo 1881142 1882259 := bstep (se 1 (by rfl) ⟨1411694, by rfl⟩ : syracuseStep 1882259 = 2823389) B2823389
theorem B2381987 : Blo 1881142 2381987 := bstep (se 1 (by rfl) ⟨1786490, by rfl⟩ : syracuseStep 2381987 = 3572981) B3572981
theorem B1882275 : Blo 1881142 1882275 := bstep (se 1 (by rfl) ⟨1411706, by rfl⟩ : syracuseStep 1882275 = 2823413) B2823413
theorem B2824355 : Blo 1881142 2824355 := bstep (se 1 (by rfl) ⟨2118266, by rfl⟩ : syracuseStep 2824355 = 4236533) B4236533
theorem B1882291 : Blo 1881142 1882291 := bstep (se 1 (by rfl) ⟨1411718, by rfl⟩ : syracuseStep 1882291 = 2823437) B2823437
theorem B2824385 : Blo 1881142 2824385 := bstep (se 2 (by rfl) ⟨1059144, by rfl⟩ : syracuseStep 2824385 = 2118289) B2118289
theorem B1882307 : Blo 1881142 1882307 := bstep (se 1 (by rfl) ⟨1411730, by rfl⟩ : syracuseStep 1882307 = 2823461) B2823461
theorem B14284997 : Blo 1881142 14284997 := bstep (se 4 (by rfl) ⟨1339218, by rfl⟩ : syracuseStep 14284997 = 2678437) B2678437
theorem B1882323 : Blo 1881142 1882323 := bstep (se 1 (by rfl) ⟨1411742, by rfl⟩ : syracuseStep 1882323 = 2823485) B2823485
theorem B2824403 : Blo 1881142 2824403 := bstep (se 1 (by rfl) ⟨2118302, by rfl⟩ : syracuseStep 2824403 = 4236605) B4236605
theorem B1882339 : Blo 1881142 1882339 := bstep (se 1 (by rfl) ⟨1411754, by rfl⟩ : syracuseStep 1882339 = 2823509) B2823509
theorem B2824433 : Blo 1881142 2824433 := bstep (se 2 (by rfl) ⟨1059162, by rfl⟩ : syracuseStep 2824433 = 2118325) B2118325
theorem B1882355 : Blo 1881142 1882355 := bstep (se 1 (by rfl) ⟨1411766, by rfl⟩ : syracuseStep 1882355 = 2823533) B2823533
theorem B3176705 : Blo 1881142 3176705 := bstep (se 2 (by rfl) ⟨1191264, by rfl⟩ : syracuseStep 3176705 = 2382529) B2382529
theorem B1882371 : Blo 1881142 1882371 := bstep (se 1 (by rfl) ⟨1411778, by rfl⟩ : syracuseStep 1882371 = 2823557) B2823557
theorem B2824451 : Blo 1881142 2824451 := bstep (se 1 (by rfl) ⟨2118338, by rfl⟩ : syracuseStep 2824451 = 4236677) B4236677
theorem B1882387 : Blo 1881142 1882387 := bstep (se 1 (by rfl) ⟨1411790, by rfl⟩ : syracuseStep 1882387 = 2823581) B2823581
theorem B2824481 : Blo 1881142 2824481 := bstep (se 2 (by rfl) ⟨1059180, by rfl⟩ : syracuseStep 2824481 = 2118361) B2118361
theorem B2480419 : Blo 1881142 2480419 := bstep (se 1 (by rfl) ⟨1860314, by rfl⟩ : syracuseStep 2480419 = 3720629) B3720629
theorem B1882403 : Blo 1881142 1882403 := bstep (se 1 (by rfl) ⟨1411802, by rfl⟩ : syracuseStep 1882403 = 2823605) B2823605
theorem B10721585 : Blo 1881142 10721585 := bstep (se 2 (by rfl) ⟨4020594, by rfl⟩ : syracuseStep 10721585 = 8041189) B8041189
theorem B1882419 : Blo 1881142 1882419 := bstep (se 1 (by rfl) ⟨1411814, by rfl⟩ : syracuseStep 1882419 = 2823629) B2823629
theorem B2824499 : Blo 1881142 2824499 := bstep (se 1 (by rfl) ⟨2118374, by rfl⟩ : syracuseStep 2824499 = 4236749) B4236749
theorem B1882435 : Blo 1881142 1882435 := bstep (se 1 (by rfl) ⟨1411826, by rfl⟩ : syracuseStep 1882435 = 2823653) B2823653
theorem B11008325 : Blo 1881142 11008325 := bstep (se 4 (by rfl) ⟨1032030, by rfl⟩ : syracuseStep 11008325 = 2064061) B2064061
theorem B2824529 : Blo 1881142 2824529 := bstep (se 2 (by rfl) ⟨1059198, by rfl⟩ : syracuseStep 2824529 = 2118397) B2118397
theorem B1882451 : Blo 1881142 1882451 := bstep (se 1 (by rfl) ⟨1411838, by rfl⟩ : syracuseStep 1882451 = 2823677) B2823677
theorem B1882467 : Blo 1881142 1882467 := bstep (se 1 (by rfl) ⟨1411850, by rfl⟩ : syracuseStep 1882467 = 2823701) B2823701
theorem B2824547 : Blo 1881142 2824547 := bstep (se 1 (by rfl) ⟨2118410, by rfl⟩ : syracuseStep 2824547 = 4236821) B4236821
theorem B6355313 : Blo 1881142 6355313 := bstep (se 2 (by rfl) ⟨2383242, by rfl⟩ : syracuseStep 6355313 = 4766485) B4766485
theorem B1882483 : Blo 1881142 1882483 := bstep (se 1 (by rfl) ⟨1411862, by rfl⟩ : syracuseStep 1882483 = 2823725) B2823725
theorem B3176833 : Blo 1881142 3176833 := bstep (se 2 (by rfl) ⟨1191312, by rfl⟩ : syracuseStep 3176833 = 2382625) B2382625
theorem B1882499 : Blo 1881142 1882499 := bstep (se 1 (by rfl) ⟨1411874, by rfl⟩ : syracuseStep 1882499 = 2823749) B2823749
theorem B2824577 : Blo 1881142 2824577 := bstep (se 2 (by rfl) ⟨1059216, by rfl⟩ : syracuseStep 2824577 = 2118433) B2118433
theorem B4233617 : Blo 1881142 4233617 := bstep (se 2 (by rfl) ⟨1587606, by rfl⟩ : syracuseStep 4233617 = 3175213) B3175213
theorem B1882515 : Blo 1881142 1882515 := bstep (se 1 (by rfl) ⟨1411886, by rfl⟩ : syracuseStep 1882515 = 2823773) B2823773
theorem B2824595 : Blo 1881142 2824595 := bstep (se 1 (by rfl) ⟨2118446, by rfl⟩ : syracuseStep 2824595 = 4236893) B4236893
theorem B4233635 : Blo 1881142 4233635 := bstep (se 1 (by rfl) ⟨3175226, by rfl⟩ : syracuseStep 4233635 = 6350453) B6350453
theorem B1882531 : Blo 1881142 1882531 := bstep (se 1 (by rfl) ⟨1411898, by rfl⟩ : syracuseStep 1882531 = 2823797) B2823797
theorem B3176867 : Blo 1881142 3176867 := bstep (se 1 (by rfl) ⟨2382650, by rfl⟩ : syracuseStep 3176867 = 4765301) B4765301
theorem B2824625 : Blo 1881142 2824625 := bstep (se 2 (by rfl) ⟨1059234, by rfl⟩ : syracuseStep 2824625 = 2118469) B2118469
theorem B1882547 : Blo 1881142 1882547 := bstep (se 1 (by rfl) ⟨1411910, by rfl⟩ : syracuseStep 1882547 = 2823821) B2823821
theorem B1882563 : Blo 1881142 1882563 := bstep (se 1 (by rfl) ⟨1411922, by rfl⟩ : syracuseStep 1882563 = 2823845) B2823845
theorem B2824643 : Blo 1881142 2824643 := bstep (se 1 (by rfl) ⟨2118482, by rfl⟩ : syracuseStep 2824643 = 4236965) B4236965
theorem B13752773 : Blo 1881142 13752773 := bstep (se 4 (by rfl) ⟨1289322, by rfl⟩ : syracuseStep 13752773 = 2578645) B2578645
theorem B4766161 : Blo 1881142 4766161 := bstep (se 2 (by rfl) ⟨1787310, by rfl⟩ : syracuseStep 4766161 = 3574621) B3574621
theorem B1882579 : Blo 1881142 1882579 := bstep (se 1 (by rfl) ⟨1411934, by rfl⟩ : syracuseStep 1882579 = 2823869) B2823869
theorem B2824673 : Blo 1881142 2824673 := bstep (se 2 (by rfl) ⟨1059252, by rfl⟩ : syracuseStep 2824673 = 2118505) B2118505
theorem B1882595 : Blo 1881142 1882595 := bstep (se 1 (by rfl) ⟨1411946, by rfl⟩ : syracuseStep 1882595 = 2823893) B2823893
theorem B1882611 : Blo 1881142 1882611 := bstep (se 1 (by rfl) ⟨1411958, by rfl⟩ : syracuseStep 1882611 = 2823917) B2823917
theorem B2824691 : Blo 1881142 2824691 := bstep (se 1 (by rfl) ⟨2118518, by rfl⟩ : syracuseStep 2824691 = 4237037) B4237037
theorem B1882627 : Blo 1881142 1882627 := bstep (se 1 (by rfl) ⟨1411970, by rfl⟩ : syracuseStep 1882627 = 2823941) B2823941
theorem B1882643 : Blo 1881142 1882643 := bstep (se 1 (by rfl) ⟨1411982, by rfl⟩ : syracuseStep 1882643 = 2823965) B2823965
theorem B1882659 : Blo 1881142 1882659 := bstep (se 1 (by rfl) ⟨1411994, by rfl⟩ : syracuseStep 1882659 = 2823989) B2823989
theorem B3176995 : Blo 1881142 3176995 := bstep (se 1 (by rfl) ⟨2382746, by rfl⟩ : syracuseStep 3176995 = 4765493) B4765493
theorem B1882675 : Blo 1881142 1882675 := bstep (se 1 (by rfl) ⟨1412006, by rfl⟩ : syracuseStep 1882675 = 2824013) B2824013
theorem B1882691 : Blo 1881142 1882691 := bstep (se 1 (by rfl) ⟨1412018, by rfl⟩ : syracuseStep 1882691 = 2824037) B2824037
theorem B1882707 : Blo 1881142 1882707 := bstep (se 1 (by rfl) ⟨1412030, by rfl⟩ : syracuseStep 1882707 = 2824061) B2824061
theorem B1882723 : Blo 1881142 1882723 := bstep (se 1 (by rfl) ⟨1412042, by rfl⟩ : syracuseStep 1882723 = 2824085) B2824085
theorem B1882739 : Blo 1881142 1882739 := bstep (se 1 (by rfl) ⟨1412054, by rfl⟩ : syracuseStep 1882739 = 2824109) B2824109
theorem B1882755 : Blo 1881142 1882755 := bstep (se 1 (by rfl) ⟨1412066, by rfl⟩ : syracuseStep 1882755 = 2824133) B2824133
theorem B1882771 : Blo 1881142 1882771 := bstep (se 1 (by rfl) ⟨1412078, by rfl⟩ : syracuseStep 1882771 = 2824157) B2824157
theorem B9525923 : Blo 1881142 9525923 := bstep (se 1 (by rfl) ⟨7144442, by rfl⟩ : syracuseStep 9525923 = 14288885) B14288885
theorem B1882787 : Blo 1881142 1882787 := bstep (se 1 (by rfl) ⟨1412090, by rfl⟩ : syracuseStep 1882787 = 2824181) B2824181
theorem B4233905 : Blo 1881142 4233905 := bstep (se 2 (by rfl) ⟨1587714, by rfl⟩ : syracuseStep 4233905 = 3175429) B3175429
theorem B3177137 : Blo 1881142 3177137 := bstep (se 2 (by rfl) ⟨1191426, by rfl⟩ : syracuseStep 3177137 = 2382853) B2382853
theorem B1882803 : Blo 1881142 1882803 := bstep (se 1 (by rfl) ⟨1412102, by rfl⟩ : syracuseStep 1882803 = 2824205) B2824205
theorem B4233923 : Blo 1881142 4233923 := bstep (se 1 (by rfl) ⟨3175442, by rfl⟩ : syracuseStep 4233923 = 6350885) B6350885
theorem B1882819 : Blo 1881142 1882819 := bstep (se 1 (by rfl) ⟨1412114, by rfl⟩ : syracuseStep 1882819 = 2824229) B2824229
theorem B5724881 : Blo 1881142 5724881 := bstep (se 2 (by rfl) ⟨2146830, by rfl⟩ : syracuseStep 5724881 = 4293661) B4293661
theorem B1882835 : Blo 1881142 1882835 := bstep (se 1 (by rfl) ⟨1412126, by rfl⟩ : syracuseStep 1882835 = 2824253) B2824253
theorem B1882851 : Blo 1881142 1882851 := bstep (se 1 (by rfl) ⟨1412138, by rfl⟩ : syracuseStep 1882851 = 2824277) B2824277
theorem B4766435 : Blo 1881142 4766435 := bstep (se 1 (by rfl) ⟨3574826, by rfl⟩ : syracuseStep 4766435 = 7149653) B7149653
theorem B14293745 : Blo 1881142 14293745 := bstep (se 2 (by rfl) ⟨5360154, by rfl⟩ : syracuseStep 14293745 = 10720309) B10720309
theorem B1882867 : Blo 1881142 1882867 := bstep (se 1 (by rfl) ⟨1412150, by rfl⟩ : syracuseStep 1882867 = 2824301) B2824301
theorem B6109955 : Blo 1881142 6109955 := bstep (se 1 (by rfl) ⟨4582466, by rfl⟩ : syracuseStep 6109955 = 9164933) B9164933
theorem B1882883 : Blo 1881142 1882883 := bstep (se 1 (by rfl) ⟨1412162, by rfl⟩ : syracuseStep 1882883 = 2824325) B2824325
theorem B1882899 : Blo 1881142 1882899 := bstep (se 1 (by rfl) ⟨1412174, by rfl⟩ : syracuseStep 1882899 = 2824349) B2824349
theorem B3013409 : Blo 1881142 3013409 := bstep (se 2 (by rfl) ⟨1130028, by rfl⟩ : syracuseStep 3013409 = 2260057) B2260057
theorem B1882915 : Blo 1881142 1882915 := bstep (se 1 (by rfl) ⟨1412186, by rfl⟩ : syracuseStep 1882915 = 2824373) B2824373
theorem B3177265 : Blo 1881142 3177265 := bstep (se 2 (by rfl) ⟨1191474, by rfl⟩ : syracuseStep 3177265 = 2382949) B2382949
theorem B1907507 : Blo 1881142 1907507 := bstep (se 1 (by rfl) ⟨1430630, by rfl⟩ : syracuseStep 1907507 = 2861261) B2861261
theorem B1882931 : Blo 1881142 1882931 := bstep (se 1 (by rfl) ⟨1412198, by rfl⟩ : syracuseStep 1882931 = 2824397) B2824397
theorem B1882947 : Blo 1881142 1882947 := bstep (se 1 (by rfl) ⟨1412210, by rfl⟩ : syracuseStep 1882947 = 2824421) B2824421
theorem B3177299 : Blo 1881142 3177299 := bstep (se 1 (by rfl) ⟨2382974, by rfl⟩ : syracuseStep 3177299 = 4765949) B4765949
theorem B1882963 : Blo 1881142 1882963 := bstep (se 1 (by rfl) ⟨1412222, by rfl⟩ : syracuseStep 1882963 = 2824445) B2824445
theorem B2382691 : Blo 1881142 2382691 := bstep (se 1 (by rfl) ⟨1787018, by rfl⟩ : syracuseStep 2382691 = 3574037) B3574037
theorem B1882979 : Blo 1881142 1882979 := bstep (se 1 (by rfl) ⟨1412234, by rfl⟩ : syracuseStep 1882979 = 2824469) B2824469
theorem B1882995 : Blo 1881142 1882995 := bstep (se 1 (by rfl) ⟨1412246, by rfl⟩ : syracuseStep 1882995 = 2824493) B2824493
theorem B1883011 : Blo 1881142 1883011 := bstep (se 1 (by rfl) ⟨1412258, by rfl⟩ : syracuseStep 1883011 = 2824517) B2824517
theorem B11451269 : Blo 1881142 11451269 := bstep (se 4 (by rfl) ⟨1073556, by rfl⟩ : syracuseStep 11451269 = 2147113) B2147113
theorem B1883027 : Blo 1881142 1883027 := bstep (se 1 (by rfl) ⟨1412270, by rfl⟩ : syracuseStep 1883027 = 2824541) B2824541
theorem B1883043 : Blo 1881142 1883043 := bstep (se 1 (by rfl) ⟨1412282, by rfl⟩ : syracuseStep 1883043 = 2824565) B2824565
theorem B4766627 : Blo 1881142 4766627 := bstep (se 1 (by rfl) ⟨3574970, by rfl⟩ : syracuseStep 4766627 = 7149941) B7149941
theorem B1883059 : Blo 1881142 1883059 := bstep (se 1 (by rfl) ⟨1412294, by rfl⟩ : syracuseStep 1883059 = 2824589) B2824589
theorem B2382787 : Blo 1881142 2382787 := bstep (se 1 (by rfl) ⟨1787090, by rfl⟩ : syracuseStep 2382787 = 3574181) B3574181
theorem B1883075 : Blo 1881142 1883075 := bstep (se 1 (by rfl) ⟨1412306, by rfl⟩ : syracuseStep 1883075 = 2824613) B2824613
theorem B4234193 : Blo 1881142 4234193 := bstep (se 2 (by rfl) ⟨1587822, by rfl⟩ : syracuseStep 4234193 = 3175645) B3175645
theorem B3177427 : Blo 1881142 3177427 := bstep (se 1 (by rfl) ⟨2383070, by rfl⟩ : syracuseStep 3177427 = 4766141) B4766141
theorem B1883091 : Blo 1881142 1883091 := bstep (se 1 (by rfl) ⟨1412318, by rfl⟩ : syracuseStep 1883091 = 2824637) B2824637
theorem B4234211 : Blo 1881142 4234211 := bstep (se 1 (by rfl) ⟨3175658, by rfl⟩ : syracuseStep 4234211 = 6351317) B6351317
theorem B1883107 : Blo 1881142 1883107 := bstep (se 1 (by rfl) ⟨1412330, by rfl⟩ : syracuseStep 1883107 = 2824661) B2824661
theorem B1883123 : Blo 1881142 1883123 := bstep (se 1 (by rfl) ⟨1412342, by rfl⟩ : syracuseStep 1883123 = 2824685) B2824685
theorem B1883139 : Blo 1881142 1883139 := bstep (se 1 (by rfl) ⟨1412354, by rfl⟩ : syracuseStep 1883139 = 2824709) B2824709
theorem B2415667 : Blo 1881142 2415667 := bstep (se 1 (by rfl) ⟨1811750, by rfl⟩ : syracuseStep 2415667 = 3623501) B3623501
theorem B3177569 : Blo 1881142 3177569 := bstep (se 2 (by rfl) ⟨1191588, by rfl⟩ : syracuseStep 3177569 = 2383177) B2383177
theorem B32144525 : Blo 1881142 32144525 := bstep (se 3 (by rfl) ⟨6027098, by rfl⟩ : syracuseStep 32144525 = 12054197) B12054197
theorem B7634083 : Blo 1881142 7634083 := bstep (se 1 (by rfl) ⟨5725562, by rfl⟩ : syracuseStep 7634083 = 11451125) B11451125
theorem B5086403 : Blo 1881142 5086403 := bstep (se 1 (by rfl) ⟨3814802, by rfl⟩ : syracuseStep 5086403 = 7629605) B7629605
theorem B3177697 : Blo 1881142 3177697 := bstep (se 2 (by rfl) ⟨1191636, by rfl⟩ : syracuseStep 3177697 = 2383273) B2383273
theorem B4234481 : Blo 1881142 4234481 := bstep (se 2 (by rfl) ⟨1587930, by rfl⟩ : syracuseStep 4234481 = 3175861) B3175861
theorem B3054835 : Blo 1881142 3054835 := bstep (se 1 (by rfl) ⟨2291126, by rfl⟩ : syracuseStep 3054835 = 4582253) B4582253
theorem B4234499 : Blo 1881142 4234499 := bstep (se 1 (by rfl) ⟨3175874, by rfl⟩ : syracuseStep 4234499 = 6351749) B6351749
theorem B3177731 : Blo 1881142 3177731 := bstep (se 1 (by rfl) ⟨2383298, by rfl⟩ : syracuseStep 3177731 = 4766597) B4766597
theorem B2145571 : Blo 1881142 2145571 := bstep (se 1 (by rfl) ⟨1609178, by rfl⟩ : syracuseStep 2145571 = 3218357) B3218357
theorem B10870085 : Blo 1881142 10870085 := bstep (se 4 (by rfl) ⟨1019070, by rfl⟩ : syracuseStep 10870085 = 2038141) B2038141
theorem B5086577 : Blo 1881142 5086577 := bstep (se 2 (by rfl) ⟨1907466, by rfl⟩ : syracuseStep 5086577 = 3814933) B3814933
theorem B6438275 : Blo 1881142 6438275 := bstep (se 1 (by rfl) ⟨4828706, by rfl⟩ : syracuseStep 6438275 = 9657413) B9657413
theorem B2383283 : Blo 1881142 2383283 := bstep (se 1 (by rfl) ⟨1787462, by rfl⟩ : syracuseStep 2383283 = 3574925) B3574925
theorem B24444341 : Blo 1881142 24444341 := bstep (se 5 (by rfl) ⟨1145828, by rfl⟩ : syracuseStep 24444341 = 2291657) B2291657
theorem B9526733 : Blo 1881142 9526733 := bstep (se 3 (by rfl) ⟨1786262, by rfl⟩ : syracuseStep 9526733 = 3572525) B3572525
theorem B4234769 : Blo 1881142 4234769 := bstep (se 2 (by rfl) ⟨1588038, by rfl⟩ : syracuseStep 4234769 = 3176077) B3176077
theorem B4234787 : Blo 1881142 4234787 := bstep (se 1 (by rfl) ⟨3176090, by rfl⟩ : syracuseStep 4234787 = 6352181) B6352181
theorem B5504561 : Blo 1881142 5504561 := bstep (se 2 (by rfl) ⟨2064210, by rfl⟩ : syracuseStep 5504561 = 4128421) B4128421
theorem B5357137 : Blo 1881142 5357137 := bstep (se 2 (by rfl) ⟨2008926, by rfl⟩ : syracuseStep 5357137 = 4017853) B4017853
theorem B4021859 : Blo 1881142 4021859 := bstep (se 1 (by rfl) ⟨3016394, by rfl⟩ : syracuseStep 4021859 = 6032789) B6032789
theorem B2260595 : Blo 1881142 2260595 := bstep (se 1 (by rfl) ⟨1695446, by rfl⟩ : syracuseStep 2260595 = 3390893) B3390893
theorem B2678449 : Blo 1881142 2678449 := bstep (se 2 (by rfl) ⟨1004418, by rfl⟩ : syracuseStep 2678449 = 2008837) B2008837
theorem B10723043 : Blo 1881142 10723043 := bstep (se 1 (by rfl) ⟨8042282, by rfl⟩ : syracuseStep 10723043 = 16084565) B16084565
theorem B4235057 : Blo 1881142 4235057 := bstep (se 2 (by rfl) ⟨1588146, by rfl⟩ : syracuseStep 4235057 = 3176293) B3176293
theorem B3571523 : Blo 1881142 3571523 := bstep (se 1 (by rfl) ⟨2678642, by rfl⟩ : syracuseStep 3571523 = 5357285) B5357285
theorem B4235075 : Blo 1881142 4235075 := bstep (se 1 (by rfl) ⟨3176306, by rfl⟩ : syracuseStep 4235075 = 6352613) B6352613
theorem B5087053 : Blo 1881142 5087053 := bstep (se 3 (by rfl) ⟨953822, by rfl⟩ : syracuseStep 5087053 = 1907645) B1907645
theorem B5357411 : Blo 1881142 5357411 := bstep (se 1 (by rfl) ⟨4018058, by rfl⟩ : syracuseStep 5357411 = 8036117) B8036117
theorem B2260931 : Blo 1881142 2260931 := bstep (se 1 (by rfl) ⟨1695698, by rfl⟩ : syracuseStep 2260931 = 3391397) B3391397
theorem B19316677 : Blo 1881142 19316677 := bstep (se 4 (by rfl) ⟨1810938, by rfl⟩ : syracuseStep 19316677 = 3621877) B3621877
theorem B91578437 : Blo 1881142 91578437 := bstep (se 4 (by rfl) ⟨8585478, by rfl⟩ : syracuseStep 91578437 = 17170957) B17170957
theorem B8036441 : Blo 1881142 8036441 := bstep (se 2 (by rfl) ⟨3013665, by rfl⟩ : syracuseStep 8036441 = 6027331) B6027331
theorem B14286941 : Blo 1881142 14286941 := bstep (se 3 (by rfl) ⟨2678801, by rfl⟩ : syracuseStep 14286941 = 5357603) B5357603
theorem B18341981 : Blo 1881142 18341981 := bstep (se 3 (by rfl) ⟨3439121, by rfl⟩ : syracuseStep 18341981 = 6878243) B6878243
theorem B2261143 : Blo 1881142 2261143 := bstep (se 1 (by rfl) ⟨1695857, by rfl⟩ : syracuseStep 2261143 = 3391715) B3391715
theorem B4235417 : Blo 1881142 4235417 := bstep (se 2 (by rfl) ⟨1588281, by rfl⟩ : syracuseStep 4235417 = 3176563) B3176563
theorem B4235507 : Blo 1881142 4235507 := bstep (se 1 (by rfl) ⟨3176630, by rfl⟩ : syracuseStep 4235507 = 6353261) B6353261
theorem B14483717 : Blo 1881142 14483717 := bstep (se 4 (by rfl) ⟨1357848, by rfl⟩ : syracuseStep 14483717 = 2715697) B2715697
theorem B4235543 : Blo 1881142 4235543 := bstep (se 1 (by rfl) ⟨3176657, by rfl⟩ : syracuseStep 4235543 = 6353315) B6353315
theorem B16081253 : Blo 1881142 16081253 := bstep (se 4 (by rfl) ⟨1507617, by rfl⟩ : syracuseStep 16081253 = 3015235) B3015235
theorem B4235723 : Blo 1881142 4235723 := bstep (se 1 (by rfl) ⟨3176792, by rfl⟩ : syracuseStep 4235723 = 6353585) B6353585
theorem B2146775 : Blo 1881142 2146775 := bstep (se 1 (by rfl) ⟨1610081, by rfl⟩ : syracuseStep 2146775 = 3220163) B3220163
theorem B4235777 : Blo 1881142 4235777 := bstep (se 2 (by rfl) ⟨1588416, by rfl⟩ : syracuseStep 4235777 = 3176833) B3176833
theorem B3572275 : Blo 1881142 3572275 := bstep (se 1 (by rfl) ⟨2679206, by rfl⟩ : syracuseStep 3572275 = 5358413) B5358413
theorem B7144109 : Blo 1881142 7144109 := bstep (se 3 (by rfl) ⟨1339520, by rfl⟩ : syracuseStep 7144109 = 2679041) B2679041
theorem B7144139 : Blo 1881142 7144139 := bstep (se 1 (by rfl) ⟨5358104, by rfl⟩ : syracuseStep 7144139 = 10716209) B10716209
theorem B15270605 : Blo 1881142 15270605 := bstep (se 3 (by rfl) ⟨2863238, by rfl⟩ : syracuseStep 15270605 = 5726477) B5726477
theorem B4235993 : Blo 1881142 4235993 := bstep (se 2 (by rfl) ⟨1588497, by rfl⟩ : syracuseStep 4235993 = 3176995) B3176995
theorem B4236083 : Blo 1881142 4236083 := bstep (se 1 (by rfl) ⟨3177062, by rfl⟩ : syracuseStep 4236083 = 6354125) B6354125
theorem B6349643 : Blo 1881142 6349643 := bstep (se 1 (by rfl) ⟨4762232, by rfl⟩ : syracuseStep 6349643 = 9524465) B9524465
theorem B4236119 : Blo 1881142 4236119 := bstep (se 1 (by rfl) ⟨3177089, by rfl⟩ : syracuseStep 4236119 = 6354179) B6354179
theorem B21431141 : Blo 1881142 21431141 := bstep (se 4 (by rfl) ⟨2009169, by rfl⟩ : syracuseStep 21431141 = 4018339) B4018339
theorem B3392371 : Blo 1881142 3392371 := bstep (se 1 (by rfl) ⟨2544278, by rfl⟩ : syracuseStep 3392371 = 5088557) B5088557
theorem B3572723 : Blo 1881142 3572723 := bstep (se 1 (by rfl) ⟨2679542, by rfl⟩ : syracuseStep 3572723 = 5359085) B5359085
theorem B4236299 : Blo 1881142 4236299 := bstep (se 1 (by rfl) ⟨3177224, by rfl⟩ : syracuseStep 4236299 = 6354449) B6354449
theorem B3572761 : Blo 1881142 3572761 := bstep (se 2 (by rfl) ⟨1339785, by rfl⟩ : syracuseStep 3572761 = 2679571) B2679571
theorem B4236353 : Blo 1881142 4236353 := bstep (se 2 (by rfl) ⟨1588632, by rfl⟩ : syracuseStep 4236353 = 3177265) B3177265
theorem B2679895 : Blo 1881142 2679895 := bstep (se 1 (by rfl) ⟨2009921, by rfl⟩ : syracuseStep 2679895 = 4019843) B4019843
theorem B6349913 : Blo 1881142 6349913 := bstep (se 2 (by rfl) ⟨2381217, by rfl⟩ : syracuseStep 6349913 = 4762435) B4762435
theorem B3015767 : Blo 1881142 3015767 := bstep (se 1 (by rfl) ⟨2261825, by rfl⟩ : syracuseStep 3015767 = 4523651) B4523651
theorem B5358743 : Blo 1881142 5358743 := bstep (se 1 (by rfl) ⟨4019057, by rfl⟩ : syracuseStep 5358743 = 8038115) B8038115
theorem B3220759 : Blo 1881142 3220759 := bstep (se 1 (by rfl) ⟨2415569, by rfl⟩ : syracuseStep 3220759 = 4831139) B4831139
theorem B4236569 : Blo 1881142 4236569 := bstep (se 2 (by rfl) ⟨1588713, by rfl⟩ : syracuseStep 4236569 = 3177427) B3177427
theorem B10716461 : Blo 1881142 10716461 := bstep (se 3 (by rfl) ⟨2009336, by rfl⟩ : syracuseStep 10716461 = 4018673) B4018673
theorem B4293953 : Blo 1881142 4293953 := bstep (se 2 (by rfl) ⟨1610232, by rfl⟩ : syracuseStep 4293953 = 3220465) B3220465
theorem B10724683 : Blo 1881142 10724683 := bstep (se 1 (by rfl) ⟨8043512, by rfl⟩ : syracuseStep 10724683 = 16087025) B16087025
theorem B7144793 : Blo 1881142 7144793 := bstep (se 2 (by rfl) ⟨2679297, by rfl⟩ : syracuseStep 7144793 = 5358595) B5358595
theorem B9045341 : Blo 1881142 9045341 := bstep (se 3 (by rfl) ⟨1696001, by rfl⟩ : syracuseStep 9045341 = 3392003) B3392003
theorem B4236659 : Blo 1881142 4236659 := bstep (se 1 (by rfl) ⟨3177494, by rfl⟩ : syracuseStep 4236659 = 6354989) B6354989
theorem B4236695 : Blo 1881142 4236695 := bstep (se 1 (by rfl) ⟨3177521, by rfl⟩ : syracuseStep 4236695 = 6355043) B6355043
theorem B3220889 : Blo 1881142 3220889 := bstep (se 2 (by rfl) ⟨1207833, by rfl⟩ : syracuseStep 3220889 = 2415667) B2415667
theorem B4294081 : Blo 1881142 4294081 := bstep (se 2 (by rfl) ⟨1610280, by rfl⟩ : syracuseStep 4294081 = 3220561) B3220561
theorem B3573209 : Blo 1881142 3573209 := bstep (se 2 (by rfl) ⟨1339953, by rfl⟩ : syracuseStep 3573209 = 2679907) B2679907
theorem B3393011 : Blo 1881142 3393011 := bstep (se 1 (by rfl) ⟨2544758, by rfl⟩ : syracuseStep 3393011 = 5089517) B5089517
theorem B9045569 : Blo 1881142 9045569 := bstep (se 2 (by rfl) ⟨3392088, by rfl⟩ : syracuseStep 9045569 = 6784177) B6784177
theorem B4236875 : Blo 1881142 4236875 := bstep (se 1 (by rfl) ⟨3177656, by rfl⟩ : syracuseStep 4236875 = 6355313) B6355313
theorem B5801561 : Blo 1881142 5801561 := bstep (se 2 (by rfl) ⟨2175585, by rfl⟩ : syracuseStep 5801561 = 4351171) B4351171
theorem B10724957 : Blo 1881142 10724957 := bstep (se 3 (by rfl) ⟨2010929, by rfl⟩ : syracuseStep 10724957 = 4021859) B4021859
theorem B4236929 : Blo 1881142 4236929 := bstep (se 2 (by rfl) ⟨1588848, by rfl⟩ : syracuseStep 4236929 = 3177697) B3177697
theorem B40699523 : Blo 1881142 40699523 := bstep (se 1 (by rfl) ⟨30524642, by rfl⟩ : syracuseStep 40699523 = 61049285) B61049285
theorem B9168515 : Blo 1881142 9168515 := bstep (se 1 (by rfl) ⟨6876386, by rfl⟩ : syracuseStep 9168515 = 13752773) B13752773
theorem B7145111 : Blo 1881142 7145111 := bstep (se 1 (by rfl) ⟨5358833, by rfl⟩ : syracuseStep 7145111 = 10717667) B10717667
theorem B4073113 : Blo 1881142 4073113 := bstep (se 2 (by rfl) ⟨1527417, by rfl⟩ : syracuseStep 4073113 = 3054835) B3054835
theorem B6350615 : Blo 1881142 6350615 := bstep (se 1 (by rfl) ⟨4762961, by rfl⟩ : syracuseStep 6350615 = 9525923) B9525923
theorem B9529163 : Blo 1881142 9529163 := bstep (se 1 (by rfl) ⟨7146872, by rfl⟩ : syracuseStep 9529163 = 14293745) B14293745
theorem B4073303 : Blo 1881142 4073303 := bstep (se 1 (by rfl) ⟨3054977, by rfl⟩ : syracuseStep 4073303 = 6109955) B6109955
theorem B6784985 : Blo 1881142 6784985 := bstep (se 2 (by rfl) ⟨2544369, by rfl⟩ : syracuseStep 6784985 = 5088739) B5088739
theorem B12060737 : Blo 1881142 12060737 := bstep (se 2 (by rfl) ⟨4522776, by rfl⟩ : syracuseStep 12060737 = 9045553) B9045553
theorem B3573953 : Blo 1881142 3573953 := bstep (se 2 (by rfl) ⟨1340232, by rfl⟩ : syracuseStep 3573953 = 2680465) B2680465
theorem B16296227 : Blo 1881142 16296227 := bstep (se 1 (by rfl) ⟨12222170, by rfl⟩ : syracuseStep 16296227 = 24444341) B24444341
theorem B6351155 : Blo 1881142 6351155 := bstep (se 1 (by rfl) ⟨4763366, by rfl⟩ : syracuseStep 6351155 = 9526733) B9526733
theorem B7145779 : Blo 1881142 7145779 := bstep (se 1 (by rfl) ⟨5359334, by rfl⟩ : syracuseStep 7145779 = 10718669) B10718669
theorem B10864961 : Blo 1881142 10864961 := bstep (se 2 (by rfl) ⟨4074360, by rfl⟩ : syracuseStep 10864961 = 8148721) B8148721
theorem B3574219 : Blo 1881142 3574219 := bstep (se 1 (by rfl) ⟨2680664, by rfl⟩ : syracuseStep 3574219 = 5361329) B5361329
theorem B13560281 : Blo 1881142 13560281 := bstep (se 2 (by rfl) ⟨5085105, by rfl⟩ : syracuseStep 13560281 = 10170211) B10170211
theorem B20630033 : Blo 1881142 20630033 := bstep (se 2 (by rfl) ⟨7736262, by rfl⟩ : syracuseStep 20630033 = 15472525) B15472525
theorem B6351425 : Blo 1881142 6351425 := bstep (se 2 (by rfl) ⟨2381784, by rfl⟩ : syracuseStep 6351425 = 4763569) B4763569
theorem B15256325 : Blo 1881142 15256325 := bstep (se 4 (by rfl) ⟨1430280, by rfl⟩ : syracuseStep 15256325 = 2860561) B2860561
theorem B2116363 : Blo 1881142 2116363 := bstep (se 1 (by rfl) ⟨1587272, by rfl⟩ : syracuseStep 2116363 = 3174545) B3174545
theorem B4893529 : Blo 1881142 4893529 := bstep (se 2 (by rfl) ⟨1835073, by rfl⟩ : syracuseStep 4893529 = 3670147) B3670147
theorem B2116471 : Blo 1881142 2116471 := bstep (se 1 (by rfl) ⟨1587353, by rfl⟩ : syracuseStep 2116471 = 3174707) B3174707
theorem B3574667 : Blo 1881142 3574667 := bstep (se 1 (by rfl) ⟨2681000, by rfl⟩ : syracuseStep 3574667 = 5362001) B5362001
theorem B6785965 : Blo 1881142 6785965 := bstep (se 3 (by rfl) ⟨1272368, by rfl⟩ : syracuseStep 6785965 = 2544737) B2544737
theorem B4762547 : Blo 1881142 4762547 := bstep (se 1 (by rfl) ⟨3571910, by rfl⟩ : syracuseStep 4762547 = 7143821) B7143821
theorem B18590681 : Blo 1881142 18590681 := bstep (se 2 (by rfl) ⟨6971505, by rfl⟩ : syracuseStep 18590681 = 13943011) B13943011
theorem B2116651 : Blo 1881142 2116651 := bstep (se 1 (by rfl) ⟨1587488, by rfl⟩ : syracuseStep 2116651 = 3174977) B3174977
theorem B3574849 : Blo 1881142 3574849 := bstep (se 2 (by rfl) ⟨1340568, by rfl⟩ : syracuseStep 3574849 = 2681137) B2681137
theorem B6351965 : Blo 1881142 6351965 := bstep (se 3 (by rfl) ⟨1190993, by rfl⟩ : syracuseStep 6351965 = 2381987) B2381987
theorem B2116759 : Blo 1881142 2116759 := bstep (se 1 (by rfl) ⟨1587569, by rfl⟩ : syracuseStep 2116759 = 3175139) B3175139
theorem B2010263 : Blo 1881142 2010263 := bstep (se 1 (by rfl) ⟨1507697, by rfl⟩ : syracuseStep 2010263 = 3015395) B3015395
theorem B2116939 : Blo 1881142 2116939 := bstep (se 1 (by rfl) ⟨1587704, by rfl⟩ : syracuseStep 2116939 = 3175409) B3175409
theorem B2117047 : Blo 1881142 2117047 := bstep (se 1 (by rfl) ⟨1587785, by rfl⟩ : syracuseStep 2117047 = 3175571) B3175571
theorem B4763083 : Blo 1881142 4763083 := bstep (se 1 (by rfl) ⟨3572312, by rfl⟩ : syracuseStep 4763083 = 7144625) B7144625
theorem B29355533 : Blo 1881142 29355533 := bstep (se 3 (by rfl) ⟨5504162, by rfl⟩ : syracuseStep 29355533 = 11008325) B11008325
theorem B28986893 : Blo 1881142 28986893 := bstep (se 3 (by rfl) ⟨5435042, by rfl⟩ : syracuseStep 28986893 = 10870085) B10870085
theorem B7147025 : Blo 1881142 7147025 := bstep (se 2 (by rfl) ⟨2680134, by rfl⟩ : syracuseStep 7147025 = 5360269) B5360269
theorem B5361203 : Blo 1881142 5361203 := bstep (se 1 (by rfl) ⟨4020902, by rfl⟩ : syracuseStep 5361203 = 8041805) B8041805
theorem B9530945 : Blo 1881142 9530945 := bstep (se 2 (by rfl) ⟨3574104, by rfl⟩ : syracuseStep 9530945 = 7148209) B7148209
theorem B2821721 : Blo 1881142 2821721 := bstep (se 2 (by rfl) ⟨1058145, by rfl⟩ : syracuseStep 2821721 = 2116291) B2116291
theorem B4763225 : Blo 1881142 4763225 := bstep (se 2 (by rfl) ⟨1786209, by rfl⟩ : syracuseStep 4763225 = 3572419) B3572419
theorem B2117227 : Blo 1881142 2117227 := bstep (se 1 (by rfl) ⟨1587920, by rfl⟩ : syracuseStep 2117227 = 3175841) B3175841
theorem B10718851 : Blo 1881142 10718851 := bstep (se 1 (by rfl) ⟨8039138, by rfl⟩ : syracuseStep 10718851 = 16078277) B16078277
theorem B2821835 : Blo 1881142 2821835 := bstep (se 1 (by rfl) ⟨2116376, by rfl⟩ : syracuseStep 2821835 = 4232753) B4232753
theorem B2821847 : Blo 1881142 2821847 := bstep (se 1 (by rfl) ⟨2116385, by rfl⟩ : syracuseStep 2821847 = 4232771) B4232771
theorem B2117335 : Blo 1881142 2117335 := bstep (se 1 (by rfl) ⟨1588001, by rfl⟩ : syracuseStep 2117335 = 3176003) B3176003
theorem B2821913 : Blo 1881142 2821913 := bstep (se 2 (by rfl) ⟨1058217, by rfl⟩ : syracuseStep 2821913 = 2116435) B2116435
theorem B4829017 : Blo 1881142 4829017 := bstep (se 2 (by rfl) ⟨1810881, by rfl⟩ : syracuseStep 4829017 = 3621763) B3621763
theorem B2822027 : Blo 1881142 2822027 := bstep (se 1 (by rfl) ⟨2116520, by rfl⟩ : syracuseStep 2822027 = 4233041) B4233041
theorem B2117515 : Blo 1881142 2117515 := bstep (se 1 (by rfl) ⟨1588136, by rfl⟩ : syracuseStep 2117515 = 3176273) B3176273
theorem B2822039 : Blo 1881142 2822039 := bstep (se 1 (by rfl) ⟨2116529, by rfl⟩ : syracuseStep 2822039 = 4233059) B4233059
theorem B2822105 : Blo 1881142 2822105 := bstep (se 2 (by rfl) ⟨1058289, by rfl⟩ : syracuseStep 2822105 = 2116579) B2116579
theorem B2117623 : Blo 1881142 2117623 := bstep (se 1 (by rfl) ⟨1588217, by rfl⟩ : syracuseStep 2117623 = 3176435) B3176435
theorem B2822219 : Blo 1881142 2822219 := bstep (se 1 (by rfl) ⟨2116664, by rfl⟩ : syracuseStep 2822219 = 4233329) B4233329
theorem B2822231 : Blo 1881142 2822231 := bstep (se 1 (by rfl) ⟨2116673, by rfl⟩ : syracuseStep 2822231 = 4233347) B4233347
theorem B9523331 : Blo 1881142 9523331 := bstep (se 1 (by rfl) ⟨7142498, by rfl⟩ : syracuseStep 9523331 = 14284997) B14284997
theorem B8581265 : Blo 1881142 8581265 := bstep (se 2 (by rfl) ⟨3217974, by rfl⟩ : syracuseStep 8581265 = 6435949) B6435949
theorem B2822297 : Blo 1881142 2822297 := bstep (se 2 (by rfl) ⟨1058361, by rfl⟩ : syracuseStep 2822297 = 2116723) B2116723
theorem B2117803 : Blo 1881142 2117803 := bstep (se 1 (by rfl) ⟨1588352, by rfl⟩ : syracuseStep 2117803 = 3176705) B3176705
theorem B6353099 : Blo 1881142 6353099 := bstep (se 1 (by rfl) ⟨4764824, by rfl⟩ : syracuseStep 6353099 = 9529649) B9529649
theorem B7147723 : Blo 1881142 7147723 := bstep (se 1 (by rfl) ⟨5360792, by rfl⟩ : syracuseStep 7147723 = 10721585) B10721585
theorem B10178777 : Blo 1881142 10178777 := bstep (se 2 (by rfl) ⟨3817041, by rfl⟩ : syracuseStep 10178777 = 7634083) B7634083
theorem B2822411 : Blo 1881142 2822411 := bstep (se 1 (by rfl) ⟨2116808, by rfl⟩ : syracuseStep 2822411 = 4233617) B4233617
theorem B2822423 : Blo 1881142 2822423 := bstep (se 1 (by rfl) ⟨2116817, by rfl⟩ : syracuseStep 2822423 = 4233635) B4233635
theorem B2117911 : Blo 1881142 2117911 := bstep (se 1 (by rfl) ⟨1588433, by rfl⟩ : syracuseStep 2117911 = 3176867) B3176867
theorem B8040779 : Blo 1881142 8040779 := bstep (se 1 (by rfl) ⟨6030584, by rfl⟩ : syracuseStep 8040779 = 12061169) B12061169
theorem B2822489 : Blo 1881142 2822489 := bstep (se 2 (by rfl) ⟨1058433, by rfl⟩ : syracuseStep 2822489 = 2116867) B2116867
theorem B12874085 : Blo 1881142 12874085 := bstep (se 4 (by rfl) ⟨1206945, by rfl⟩ : syracuseStep 12874085 = 2413891) B2413891
theorem B4764055 : Blo 1881142 4764055 := bstep (se 1 (by rfl) ⟨3573041, by rfl⟩ : syracuseStep 4764055 = 7146083) B7146083
theorem B2822603 : Blo 1881142 2822603 := bstep (se 1 (by rfl) ⟨2116952, by rfl⟩ : syracuseStep 2822603 = 4233905) B4233905
theorem B2118091 : Blo 1881142 2118091 := bstep (se 1 (by rfl) ⟨1588568, by rfl⟩ : syracuseStep 2118091 = 3177137) B3177137
theorem B2822615 : Blo 1881142 2822615 := bstep (se 1 (by rfl) ⟨2116961, by rfl⟩ : syracuseStep 2822615 = 4233923) B4233923
theorem B6353369 : Blo 1881142 6353369 := bstep (se 2 (by rfl) ⟨2382513, by rfl⟩ : syracuseStep 6353369 = 4765027) B4765027
theorem B7147997 : Blo 1881142 7147997 := bstep (se 3 (by rfl) ⟨1340249, by rfl⟩ : syracuseStep 7147997 = 2680499) B2680499
theorem B3174923 : Blo 1881142 3174923 := bstep (se 1 (by rfl) ⟨2381192, by rfl⟩ : syracuseStep 3174923 = 4762385) B4762385
theorem B2822681 : Blo 1881142 2822681 := bstep (se 2 (by rfl) ⟨1058505, by rfl⟩ : syracuseStep 2822681 = 2117011) B2117011
theorem B2118199 : Blo 1881142 2118199 := bstep (se 1 (by rfl) ⟨1588649, by rfl⟩ : syracuseStep 2118199 = 3177299) B3177299
theorem B10719809 : Blo 1881142 10719809 := bstep (se 2 (by rfl) ⟨4019928, by rfl⟩ : syracuseStep 10719809 = 8039857) B8039857
theorem B3175051 : Blo 1881142 3175051 := bstep (se 1 (by rfl) ⟨2381288, by rfl⟩ : syracuseStep 3175051 = 4762577) B4762577
theorem B2822795 : Blo 1881142 2822795 := bstep (se 1 (by rfl) ⟨2117096, by rfl⟩ : syracuseStep 2822795 = 4234193) B4234193
theorem B3486347 : Blo 1881142 3486347 := bstep (se 1 (by rfl) ⟨2614760, by rfl⟩ : syracuseStep 3486347 = 5229521) B5229521
theorem B9040535 : Blo 1881142 9040535 := bstep (se 1 (by rfl) ⟨6780401, by rfl⟩ : syracuseStep 9040535 = 13560803) B13560803
theorem B2822807 : Blo 1881142 2822807 := bstep (se 1 (by rfl) ⟨2117105, by rfl⟩ : syracuseStep 2822807 = 4234211) B4234211
theorem B2822873 : Blo 1881142 2822873 := bstep (se 2 (by rfl) ⟨1058577, by rfl⟩ : syracuseStep 2822873 = 2117155) B2117155
theorem B5509849 : Blo 1881142 5509849 := bstep (se 2 (by rfl) ⟨2066193, by rfl⟩ : syracuseStep 5509849 = 4132387) B4132387
theorem B2118379 : Blo 1881142 2118379 := bstep (se 1 (by rfl) ⟨1588784, by rfl⟩ : syracuseStep 2118379 = 3177569) B3177569
theorem B6435607 : Blo 1881142 6435607 := bstep (se 1 (by rfl) ⟨4826705, by rfl⟩ : syracuseStep 6435607 = 9653411) B9653411
theorem B3175193 : Blo 1881142 3175193 := bstep (se 2 (by rfl) ⟨1190697, by rfl⟩ : syracuseStep 3175193 = 2381395) B2381395
theorem B2822987 : Blo 1881142 2822987 := bstep (se 1 (by rfl) ⟨2117240, by rfl⟩ : syracuseStep 2822987 = 4234481) B4234481
theorem B4764491 : Blo 1881142 4764491 := bstep (se 1 (by rfl) ⟨3573368, by rfl⟩ : syracuseStep 4764491 = 7146737) B7146737
theorem B2822999 : Blo 1881142 2822999 := bstep (se 1 (by rfl) ⟨2117249, by rfl⟩ : syracuseStep 2822999 = 4234499) B4234499
theorem B2118487 : Blo 1881142 2118487 := bstep (se 1 (by rfl) ⟨1588865, by rfl⟩ : syracuseStep 2118487 = 3177731) B3177731
theorem B3175321 : Blo 1881142 3175321 := bstep (se 2 (by rfl) ⟨1190745, by rfl⟩ : syracuseStep 3175321 = 2381491) B2381491
theorem B2823065 : Blo 1881142 2823065 := bstep (se 2 (by rfl) ⟨1058649, by rfl⟩ : syracuseStep 2823065 = 2117299) B2117299
theorem B2823179 : Blo 1881142 2823179 := bstep (se 1 (by rfl) ⟨2117384, by rfl⟩ : syracuseStep 2823179 = 4234769) B4234769
theorem B65205269 : Blo 1881142 65205269 := bstep (se 6 (by rfl) ⟨1528248, by rfl⟩ : syracuseStep 65205269 = 3056497) B3056497
theorem B2823191 : Blo 1881142 2823191 := bstep (se 1 (by rfl) ⟨2117393, by rfl⟩ : syracuseStep 2823191 = 4234787) B4234787
theorem B1881143 : Blo 1881142 1881143 := bstep (se 1 (by rfl) ⟨1410857, by rfl⟩ : syracuseStep 1881143 = 2821715) B2821715
theorem B6779969 : Blo 1881142 6779969 := bstep (se 2 (by rfl) ⟨2542488, by rfl⟩ : syracuseStep 6779969 = 5084977) B5084977
theorem B1881163 : Blo 1881142 1881163 := bstep (se 1 (by rfl) ⟨1410872, by rfl⟩ : syracuseStep 1881163 = 2821745) B2821745
theorem B1881175 : Blo 1881142 1881175 := bstep (se 1 (by rfl) ⟨1410881, by rfl⟩ : syracuseStep 1881175 = 2821763) B2821763
theorem B2823257 : Blo 1881142 2823257 := bstep (se 2 (by rfl) ⟨1058721, by rfl⟩ : syracuseStep 2823257 = 2117443) B2117443
theorem B1881195 : Blo 1881142 1881195 := bstep (se 1 (by rfl) ⟨1410896, by rfl⟩ : syracuseStep 1881195 = 2821793) B2821793
theorem B1881207 : Blo 1881142 1881207 := bstep (se 1 (by rfl) ⟨1410905, by rfl⟩ : syracuseStep 1881207 = 2821811) B2821811
theorem B9172099 : Blo 1881142 9172099 := bstep (se 1 (by rfl) ⟨6879074, by rfl⟩ : syracuseStep 9172099 = 13758149) B13758149
theorem B1881227 : Blo 1881142 1881227 := bstep (se 1 (by rfl) ⟨1410920, by rfl⟩ : syracuseStep 1881227 = 2821841) B2821841
theorem B1881239 : Blo 1881142 1881239 := bstep (se 1 (by rfl) ⟨1410929, by rfl⟩ : syracuseStep 1881239 = 2821859) B2821859
theorem B6354071 : Blo 1881142 6354071 := bstep (se 1 (by rfl) ⟨4765553, by rfl⟩ : syracuseStep 6354071 = 9531107) B9531107
theorem B7148695 : Blo 1881142 7148695 := bstep (se 1 (by rfl) ⟨5361521, by rfl⟩ : syracuseStep 7148695 = 10723043) B10723043
theorem B1881259 : Blo 1881142 1881259 := bstep (se 1 (by rfl) ⟨1410944, by rfl⟩ : syracuseStep 1881259 = 2821889) B2821889
theorem B1881271 : Blo 1881142 1881271 := bstep (se 1 (by rfl) ⟨1410953, by rfl⟩ : syracuseStep 1881271 = 2821907) B2821907
theorem B4764865 : Blo 1881142 4764865 := bstep (se 2 (by rfl) ⟨1786824, by rfl⟩ : syracuseStep 4764865 = 3573649) B3573649
theorem B1881291 : Blo 1881142 1881291 := bstep (se 1 (by rfl) ⟨1410968, by rfl⟩ : syracuseStep 1881291 = 2821937) B2821937
theorem B2823371 : Blo 1881142 2823371 := bstep (se 1 (by rfl) ⟨2117528, by rfl⟩ : syracuseStep 2823371 = 4235057) B4235057
theorem B2381015 : Blo 1881142 2381015 := bstep (se 1 (by rfl) ⟨1785761, by rfl⟩ : syracuseStep 2381015 = 3571523) B3571523
theorem B1881303 : Blo 1881142 1881303 := bstep (se 1 (by rfl) ⟨1410977, by rfl⟩ : syracuseStep 1881303 = 2821955) B2821955
theorem B2823383 : Blo 1881142 2823383 := bstep (se 1 (by rfl) ⟨2117537, by rfl⟩ : syracuseStep 2823383 = 4235075) B4235075
theorem B6436061 : Blo 1881142 6436061 := bstep (se 3 (by rfl) ⟨1206761, by rfl⟩ : syracuseStep 6436061 = 2413523) B2413523
theorem B1881323 : Blo 1881142 1881323 := bstep (se 1 (by rfl) ⟨1410992, by rfl⟩ : syracuseStep 1881323 = 2821985) B2821985
theorem B1881335 : Blo 1881142 1881335 := bstep (se 1 (by rfl) ⟨1411001, by rfl⟩ : syracuseStep 1881335 = 2822003) B2822003
theorem B1881355 : Blo 1881142 1881355 := bstep (se 1 (by rfl) ⟨1411016, by rfl⟩ : syracuseStep 1881355 = 2822033) B2822033
theorem B1881367 : Blo 1881142 1881367 := bstep (se 1 (by rfl) ⟨1411025, by rfl⟩ : syracuseStep 1881367 = 2822051) B2822051
theorem B2823449 : Blo 1881142 2823449 := bstep (se 2 (by rfl) ⟨1058793, by rfl⟩ : syracuseStep 2823449 = 2117587) B2117587
theorem B1881387 : Blo 1881142 1881387 := bstep (se 1 (by rfl) ⟨1411040, by rfl⟩ : syracuseStep 1881387 = 2822081) B2822081
theorem B1881399 : Blo 1881142 1881399 := bstep (se 1 (by rfl) ⟨1411049, by rfl⟩ : syracuseStep 1881399 = 2822099) B2822099
theorem B1881419 : Blo 1881142 1881419 := bstep (se 1 (by rfl) ⟨1411064, by rfl⟩ : syracuseStep 1881419 = 2822129) B2822129
theorem B1881431 : Blo 1881142 1881431 := bstep (se 1 (by rfl) ⟨1411073, by rfl⟩ : syracuseStep 1881431 = 2822147) B2822147
theorem B1881451 : Blo 1881142 1881451 := bstep (se 1 (by rfl) ⟨1411088, by rfl⟩ : syracuseStep 1881451 = 2822177) B2822177
theorem B1881463 : Blo 1881142 1881463 := bstep (se 1 (by rfl) ⟨1411097, by rfl⟩ : syracuseStep 1881463 = 2822195) B2822195
theorem B1881483 : Blo 1881142 1881483 := bstep (se 1 (by rfl) ⟨1411112, by rfl⟩ : syracuseStep 1881483 = 2822225) B2822225
theorem B2823563 : Blo 1881142 2823563 := bstep (se 1 (by rfl) ⟨2117672, by rfl⟩ : syracuseStep 2823563 = 4235345) B4235345
theorem B1881495 : Blo 1881142 1881495 := bstep (se 1 (by rfl) ⟨1411121, by rfl⟩ : syracuseStep 1881495 = 2822243) B2822243
theorem B2823575 : Blo 1881142 2823575 := bstep (se 1 (by rfl) ⟨2117681, by rfl⟩ : syracuseStep 2823575 = 4235363) B4235363
theorem B1881515 : Blo 1881142 1881515 := bstep (se 1 (by rfl) ⟨1411136, by rfl⟩ : syracuseStep 1881515 = 2822273) B2822273
theorem B4232627 : Blo 1881142 4232627 := bstep (se 1 (by rfl) ⟨3174470, by rfl⟩ : syracuseStep 4232627 = 6348941) B6348941
theorem B1881527 : Blo 1881142 1881527 := bstep (se 1 (by rfl) ⟨1411145, by rfl⟩ : syracuseStep 1881527 = 2822291) B2822291
theorem B1881547 : Blo 1881142 1881547 := bstep (se 1 (by rfl) ⟨1411160, by rfl⟩ : syracuseStep 1881547 = 2822321) B2822321
theorem B4232663 : Blo 1881142 4232663 := bstep (se 1 (by rfl) ⟨3174497, by rfl⟩ : syracuseStep 4232663 = 6348995) B6348995
theorem B1881559 : Blo 1881142 1881559 := bstep (se 1 (by rfl) ⟨1411169, by rfl⟩ : syracuseStep 1881559 = 2822339) B2822339
theorem B3175895 : Blo 1881142 3175895 := bstep (se 1 (by rfl) ⟨2381921, by rfl⟩ : syracuseStep 3175895 = 4763843) B4763843
theorem B2823641 : Blo 1881142 2823641 := bstep (se 2 (by rfl) ⟨1058865, by rfl⟩ : syracuseStep 2823641 = 2117731) B2117731
theorem B9532889 : Blo 1881142 9532889 := bstep (se 2 (by rfl) ⟨3574833, by rfl⟩ : syracuseStep 9532889 = 7149667) B7149667
theorem B1881579 : Blo 1881142 1881579 := bstep (se 1 (by rfl) ⟨1411184, by rfl⟩ : syracuseStep 1881579 = 2822369) B2822369
theorem B4019699 : Blo 1881142 4019699 := bstep (se 1 (by rfl) ⟨3014774, by rfl⟩ : syracuseStep 4019699 = 6029549) B6029549
theorem B1881591 : Blo 1881142 1881591 := bstep (se 1 (by rfl) ⟨1411193, by rfl⟩ : syracuseStep 1881591 = 2822387) B2822387
theorem B1881611 : Blo 1881142 1881611 := bstep (se 1 (by rfl) ⟨1411208, by rfl⟩ : syracuseStep 1881611 = 2822417) B2822417
theorem B1881623 : Blo 1881142 1881623 := bstep (se 1 (by rfl) ⟨1411217, by rfl⟩ : syracuseStep 1881623 = 2822435) B2822435
theorem B1881643 : Blo 1881142 1881643 := bstep (se 1 (by rfl) ⟨1411232, by rfl⟩ : syracuseStep 1881643 = 2822465) B2822465
theorem B1881655 : Blo 1881142 1881655 := bstep (se 1 (by rfl) ⟨1411241, by rfl⟩ : syracuseStep 1881655 = 2822483) B2822483
theorem B5723713 : Blo 1881142 5723713 := bstep (se 2 (by rfl) ⟨2146392, by rfl⟩ : syracuseStep 5723713 = 4292785) B4292785
theorem B1881675 : Blo 1881142 1881675 := bstep (se 1 (by rfl) ⟨1411256, by rfl⟩ : syracuseStep 1881675 = 2822513) B2822513
theorem B2823755 : Blo 1881142 2823755 := bstep (se 1 (by rfl) ⟨2117816, by rfl⟩ : syracuseStep 2823755 = 4235633) B4235633
theorem B1881687 : Blo 1881142 1881687 := bstep (se 1 (by rfl) ⟨1411265, by rfl⟩ : syracuseStep 1881687 = 2822531) B2822531
theorem B3176023 : Blo 1881142 3176023 := bstep (se 1 (by rfl) ⟨2382017, by rfl⟩ : syracuseStep 3176023 = 4764035) B4764035
theorem B2823767 : Blo 1881142 2823767 := bstep (se 1 (by rfl) ⟨2117825, by rfl⟩ : syracuseStep 2823767 = 4235651) B4235651
theorem B1881707 : Blo 1881142 1881707 := bstep (se 1 (by rfl) ⟨1411280, by rfl⟩ : syracuseStep 1881707 = 2822561) B2822561
theorem B1881719 : Blo 1881142 1881719 := bstep (se 1 (by rfl) ⟨1411289, by rfl⟩ : syracuseStep 1881719 = 2822579) B2822579
theorem B4232843 : Blo 1881142 4232843 := bstep (se 1 (by rfl) ⟨3174632, by rfl⟩ : syracuseStep 4232843 = 6349265) B6349265
theorem B1881739 : Blo 1881142 1881739 := bstep (se 1 (by rfl) ⟨1411304, by rfl⟩ : syracuseStep 1881739 = 2822609) B2822609
theorem B2414219 : Blo 1881142 2414219 := bstep (se 1 (by rfl) ⟨1810664, by rfl⟩ : syracuseStep 2414219 = 3621329) B3621329
theorem B1881751 : Blo 1881142 1881751 := bstep (se 1 (by rfl) ⟨1411313, by rfl⟩ : syracuseStep 1881751 = 2822627) B2822627
theorem B2823833 : Blo 1881142 2823833 := bstep (se 2 (by rfl) ⟨1058937, by rfl⟩ : syracuseStep 2823833 = 2117875) B2117875
theorem B1881771 : Blo 1881142 1881771 := bstep (se 1 (by rfl) ⟨1411328, by rfl⟩ : syracuseStep 1881771 = 2822657) B2822657
theorem B6354611 : Blo 1881142 6354611 := bstep (se 1 (by rfl) ⟨4765958, by rfl⟩ : syracuseStep 6354611 = 9531917) B9531917
theorem B1881783 : Blo 1881142 1881783 := bstep (se 1 (by rfl) ⟨1411337, by rfl⟩ : syracuseStep 1881783 = 2822675) B2822675
theorem B4232897 : Blo 1881142 4232897 := bstep (se 2 (by rfl) ⟨1587336, by rfl⟩ : syracuseStep 4232897 = 3174673) B3174673
theorem B1881803 : Blo 1881142 1881803 := bstep (se 1 (by rfl) ⟨1411352, by rfl⟩ : syracuseStep 1881803 = 2822705) B2822705
theorem B1881815 : Blo 1881142 1881815 := bstep (se 1 (by rfl) ⟨1411361, by rfl⟩ : syracuseStep 1881815 = 2822723) B2822723
theorem B3307225 : Blo 1881142 3307225 := bstep (se 2 (by rfl) ⟨1240209, by rfl⟩ : syracuseStep 3307225 = 2480419) B2480419
theorem B1881835 : Blo 1881142 1881835 := bstep (se 1 (by rfl) ⟨1411376, by rfl⟩ : syracuseStep 1881835 = 2822753) B2822753
theorem B1881847 : Blo 1881142 1881847 := bstep (se 1 (by rfl) ⟨1411385, by rfl⟩ : syracuseStep 1881847 = 2822771) B2822771
theorem B1881867 : Blo 1881142 1881867 := bstep (se 1 (by rfl) ⟨1411400, by rfl⟩ : syracuseStep 1881867 = 2822801) B2822801
theorem B2823947 : Blo 1881142 2823947 := bstep (se 1 (by rfl) ⟨2117960, by rfl⟩ : syracuseStep 2823947 = 4235921) B4235921
theorem B1881879 : Blo 1881142 1881879 := bstep (se 1 (by rfl) ⟨1411409, by rfl⟩ : syracuseStep 1881879 = 2822819) B2822819
theorem B2823959 : Blo 1881142 2823959 := bstep (se 1 (by rfl) ⟨2117969, by rfl⟩ : syracuseStep 2823959 = 4235939) B4235939
theorem B4765463 : Blo 1881142 4765463 := bstep (se 1 (by rfl) ⟨3574097, by rfl⟩ : syracuseStep 4765463 = 7148195) B7148195
theorem B1881899 : Blo 1881142 1881899 := bstep (se 1 (by rfl) ⟨1411424, by rfl⟩ : syracuseStep 1881899 = 2822849) B2822849
theorem B1881911 : Blo 1881142 1881911 := bstep (se 1 (by rfl) ⟨1411433, by rfl⟩ : syracuseStep 1881911 = 2822867) B2822867
theorem B1881931 : Blo 1881142 1881931 := bstep (se 1 (by rfl) ⟨1411448, by rfl⟩ : syracuseStep 1881931 = 2822897) B2822897
theorem B1881943 : Blo 1881142 1881943 := bstep (se 1 (by rfl) ⟨1411457, by rfl⟩ : syracuseStep 1881943 = 2822915) B2822915
theorem B2824025 : Blo 1881142 2824025 := bstep (se 2 (by rfl) ⟨1059009, by rfl⟩ : syracuseStep 2824025 = 2118019) B2118019
theorem B1881963 : Blo 1881142 1881963 := bstep (se 1 (by rfl) ⟨1411472, by rfl⟩ : syracuseStep 1881963 = 2822945) B2822945
theorem B1881975 : Blo 1881142 1881975 := bstep (se 1 (by rfl) ⟨1411481, by rfl⟩ : syracuseStep 1881975 = 2822963) B2822963
theorem B1881995 : Blo 1881142 1881995 := bstep (se 1 (by rfl) ⟨1411496, by rfl⟩ : syracuseStep 1881995 = 2822993) B2822993
theorem B2381719 : Blo 1881142 2381719 := bstep (se 1 (by rfl) ⟨1786289, by rfl⟩ : syracuseStep 2381719 = 3572579) B3572579
theorem B1882007 : Blo 1881142 1882007 := bstep (se 1 (by rfl) ⟨1411505, by rfl⟩ : syracuseStep 1882007 = 2823011) B2823011
theorem B4233113 : Blo 1881142 4233113 := bstep (se 2 (by rfl) ⟨1587417, by rfl⟩ : syracuseStep 4233113 = 3174835) B3174835
theorem B1882027 : Blo 1881142 1882027 := bstep (se 1 (by rfl) ⟨1411520, by rfl⟩ : syracuseStep 1882027 = 2823041) B2823041
theorem B7149485 : Blo 1881142 7149485 := bstep (se 3 (by rfl) ⟨1340528, by rfl⟩ : syracuseStep 7149485 = 2681057) B2681057
theorem B8042419 : Blo 1881142 8042419 := bstep (se 1 (by rfl) ⟨6031814, by rfl⟩ : syracuseStep 8042419 = 12063629) B12063629
theorem B1882039 : Blo 1881142 1882039 := bstep (se 1 (by rfl) ⟨1411529, by rfl⟩ : syracuseStep 1882039 = 2823059) B2823059
theorem B6354881 : Blo 1881142 6354881 := bstep (se 2 (by rfl) ⟨2383080, by rfl⟩ : syracuseStep 6354881 = 4766161) B4766161
theorem B1882059 : Blo 1881142 1882059 := bstep (se 1 (by rfl) ⟨1411544, by rfl⟩ : syracuseStep 1882059 = 2823089) B2823089
theorem B2824139 : Blo 1881142 2824139 := bstep (se 1 (by rfl) ⟨2118104, by rfl⟩ : syracuseStep 2824139 = 4236209) B4236209
theorem B1882071 : Blo 1881142 1882071 := bstep (se 1 (by rfl) ⟨1411553, by rfl⟩ : syracuseStep 1882071 = 2823107) B2823107
theorem B4020185 : Blo 1881142 4020185 := bstep (se 2 (by rfl) ⟨1507569, by rfl⟩ : syracuseStep 4020185 = 3015139) B3015139
theorem B2824151 : Blo 1881142 2824151 := bstep (se 1 (by rfl) ⟨2118113, by rfl⟩ : syracuseStep 2824151 = 4236227) B4236227
theorem B1882091 : Blo 1881142 1882091 := bstep (se 1 (by rfl) ⟨1411568, by rfl⟩ : syracuseStep 1882091 = 2823137) B2823137
theorem B4233203 : Blo 1881142 4233203 := bstep (se 1 (by rfl) ⟨3174902, by rfl⟩ : syracuseStep 4233203 = 6349805) B6349805
theorem B1882103 : Blo 1881142 1882103 := bstep (se 1 (by rfl) ⟨1411577, by rfl⟩ : syracuseStep 1882103 = 2823155) B2823155
theorem B1882123 : Blo 1881142 1882123 := bstep (se 1 (by rfl) ⟨1411592, by rfl⟩ : syracuseStep 1882123 = 2823185) B2823185
theorem B4233239 : Blo 1881142 4233239 := bstep (se 1 (by rfl) ⟨3174929, by rfl⟩ : syracuseStep 4233239 = 6349859) B6349859
theorem B1882135 : Blo 1881142 1882135 := bstep (se 1 (by rfl) ⟨1411601, by rfl⟩ : syracuseStep 1882135 = 2823203) B2823203
theorem B2824217 : Blo 1881142 2824217 := bstep (se 2 (by rfl) ⟨1059081, by rfl⟩ : syracuseStep 2824217 = 2118163) B2118163
theorem B1882155 : Blo 1881142 1882155 := bstep (se 1 (by rfl) ⟨1411616, by rfl⟩ : syracuseStep 1882155 = 2823233) B2823233
theorem B1882167 : Blo 1881142 1882167 := bstep (se 1 (by rfl) ⟨1411625, by rfl⟩ : syracuseStep 1882167 = 2823251) B2823251
theorem B1882187 : Blo 1881142 1882187 := bstep (se 1 (by rfl) ⟨1411640, by rfl⟩ : syracuseStep 1882187 = 2823281) B2823281
theorem B1882199 : Blo 1881142 1882199 := bstep (se 1 (by rfl) ⟨1411649, by rfl⟩ : syracuseStep 1882199 = 2823299) B2823299
theorem B1882219 : Blo 1881142 1882219 := bstep (se 1 (by rfl) ⟨1411664, by rfl⟩ : syracuseStep 1882219 = 2823329) B2823329
theorem B1882231 : Blo 1881142 1882231 := bstep (se 1 (by rfl) ⟨1411673, by rfl⟩ : syracuseStep 1882231 = 2823347) B2823347
theorem B1882251 : Blo 1881142 1882251 := bstep (se 1 (by rfl) ⟨1411688, by rfl⟩ : syracuseStep 1882251 = 2823377) B2823377
theorem B2824331 : Blo 1881142 2824331 := bstep (se 1 (by rfl) ⟨2118248, by rfl⟩ : syracuseStep 2824331 = 4236497) B4236497
theorem B1882263 : Blo 1881142 1882263 := bstep (se 1 (by rfl) ⟨1411697, by rfl⟩ : syracuseStep 1882263 = 2823395) B2823395
theorem B2824343 : Blo 1881142 2824343 := bstep (se 1 (by rfl) ⟨2118257, by rfl⟩ : syracuseStep 2824343 = 4236515) B4236515
theorem B1882283 : Blo 1881142 1882283 := bstep (se 1 (by rfl) ⟨1411712, by rfl⟩ : syracuseStep 1882283 = 2823425) B2823425
theorem B1882295 : Blo 1881142 1882295 := bstep (se 1 (by rfl) ⟨1411721, by rfl⟩ : syracuseStep 1882295 = 2823443) B2823443
theorem B4233419 : Blo 1881142 4233419 := bstep (se 1 (by rfl) ⟨3175064, by rfl⟩ : syracuseStep 4233419 = 6350129) B6350129
theorem B1882315 : Blo 1881142 1882315 := bstep (se 1 (by rfl) ⟨1411736, by rfl⟩ : syracuseStep 1882315 = 2823473) B2823473
theorem B3176651 : Blo 1881142 3176651 := bstep (se 1 (by rfl) ⟨2382488, by rfl⟩ : syracuseStep 3176651 = 4764977) B4764977
theorem B1882327 : Blo 1881142 1882327 := bstep (se 1 (by rfl) ⟨1411745, by rfl⟩ : syracuseStep 1882327 = 2823491) B2823491
theorem B2824409 : Blo 1881142 2824409 := bstep (se 2 (by rfl) ⟨1059153, by rfl⟩ : syracuseStep 2824409 = 2118307) B2118307
theorem B1882347 : Blo 1881142 1882347 := bstep (se 1 (by rfl) ⟨1411760, by rfl⟩ : syracuseStep 1882347 = 2823521) B2823521
theorem B1882359 : Blo 1881142 1882359 := bstep (se 1 (by rfl) ⟨1411769, by rfl⟩ : syracuseStep 1882359 = 2823539) B2823539
theorem B4233473 : Blo 1881142 4233473 := bstep (se 2 (by rfl) ⟨1587552, by rfl⟩ : syracuseStep 4233473 = 3175105) B3175105
theorem B1882379 : Blo 1881142 1882379 := bstep (se 1 (by rfl) ⟨1411784, by rfl⟩ : syracuseStep 1882379 = 2823569) B2823569
theorem B1882391 : Blo 1881142 1882391 := bstep (se 1 (by rfl) ⟨1411793, by rfl⟩ : syracuseStep 1882391 = 2823587) B2823587
theorem B1882411 : Blo 1881142 1882411 := bstep (se 1 (by rfl) ⟨1411808, by rfl⟩ : syracuseStep 1882411 = 2823617) B2823617
theorem B1882423 : Blo 1881142 1882423 := bstep (se 1 (by rfl) ⟨1411817, by rfl⟩ : syracuseStep 1882423 = 2823635) B2823635
theorem B1882443 : Blo 1881142 1882443 := bstep (se 1 (by rfl) ⟨1411832, by rfl⟩ : syracuseStep 1882443 = 2823665) B2823665
theorem B3176779 : Blo 1881142 3176779 := bstep (se 1 (by rfl) ⟨2382584, by rfl⟩ : syracuseStep 3176779 = 4765169) B4765169
theorem B2824523 : Blo 1881142 2824523 := bstep (se 1 (by rfl) ⟨2118392, by rfl⟩ : syracuseStep 2824523 = 4236785) B4236785
theorem B1882455 : Blo 1881142 1882455 := bstep (se 1 (by rfl) ⟨1411841, by rfl⟩ : syracuseStep 1882455 = 2823683) B2823683
theorem B2824535 : Blo 1881142 2824535 := bstep (se 1 (by rfl) ⟨2118401, by rfl⟩ : syracuseStep 2824535 = 4236803) B4236803
theorem B1882475 : Blo 1881142 1882475 := bstep (se 1 (by rfl) ⟨1411856, by rfl⟩ : syracuseStep 1882475 = 2823713) B2823713
theorem B1882487 : Blo 1881142 1882487 := bstep (se 1 (by rfl) ⟨1411865, by rfl⟩ : syracuseStep 1882487 = 2823731) B2823731
theorem B1882507 : Blo 1881142 1882507 := bstep (se 1 (by rfl) ⟨1411880, by rfl⟩ : syracuseStep 1882507 = 2823761) B2823761
theorem B1882519 : Blo 1881142 1882519 := bstep (se 1 (by rfl) ⟨1411889, by rfl⟩ : syracuseStep 1882519 = 2823779) B2823779
theorem B2824601 : Blo 1881142 2824601 := bstep (se 2 (by rfl) ⟨1059225, by rfl⟩ : syracuseStep 2824601 = 2118451) B2118451
theorem B1882539 : Blo 1881142 1882539 := bstep (se 1 (by rfl) ⟨1411904, by rfl⟩ : syracuseStep 1882539 = 2823809) B2823809
theorem B1882551 : Blo 1881142 1882551 := bstep (se 1 (by rfl) ⟨1411913, by rfl⟩ : syracuseStep 1882551 = 2823827) B2823827
theorem B1882571 : Blo 1881142 1882571 := bstep (se 1 (by rfl) ⟨1411928, by rfl⟩ : syracuseStep 1882571 = 2823857) B2823857
theorem B1882583 : Blo 1881142 1882583 := bstep (se 1 (by rfl) ⟨1411937, by rfl⟩ : syracuseStep 1882583 = 2823875) B2823875
theorem B22886873 : Blo 1881142 22886873 := bstep (se 2 (by rfl) ⟨8582577, by rfl⟩ : syracuseStep 22886873 = 17165155) B17165155
theorem B4233689 : Blo 1881142 4233689 := bstep (se 2 (by rfl) ⟨1587633, by rfl⟩ : syracuseStep 4233689 = 3175267) B3175267
theorem B3176921 : Blo 1881142 3176921 := bstep (se 2 (by rfl) ⟨1191345, by rfl⟩ : syracuseStep 3176921 = 2382691) B2382691
theorem B6355421 : Blo 1881142 6355421 := bstep (se 3 (by rfl) ⟨1191641, by rfl⟩ : syracuseStep 6355421 = 2383283) B2383283
theorem B1882603 : Blo 1881142 1882603 := bstep (se 1 (by rfl) ⟨1411952, by rfl⟩ : syracuseStep 1882603 = 2823905) B2823905
theorem B3815923 : Blo 1881142 3815923 := bstep (se 1 (by rfl) ⟨2861942, by rfl⟩ : syracuseStep 3815923 = 5723885) B5723885
theorem B1882615 : Blo 1881142 1882615 := bstep (se 1 (by rfl) ⟨1411961, by rfl⟩ : syracuseStep 1882615 = 2823923) B2823923
theorem B7240195 : Blo 1881142 7240195 := bstep (se 1 (by rfl) ⟨5430146, by rfl⟩ : syracuseStep 7240195 = 10860293) B10860293
theorem B17177093 : Blo 1881142 17177093 := bstep (se 4 (by rfl) ⟨1610352, by rfl⟩ : syracuseStep 17177093 = 3220705) B3220705
theorem B1882635 : Blo 1881142 1882635 := bstep (se 1 (by rfl) ⟨1411976, by rfl⟩ : syracuseStep 1882635 = 2823953) B2823953
theorem B1882647 : Blo 1881142 1882647 := bstep (se 1 (by rfl) ⟨1411985, by rfl⟩ : syracuseStep 1882647 = 2823971) B2823971
theorem B1882667 : Blo 1881142 1882667 := bstep (se 1 (by rfl) ⟨1412000, by rfl⟩ : syracuseStep 1882667 = 2824001) B2824001
theorem B4233779 : Blo 1881142 4233779 := bstep (se 1 (by rfl) ⟨3175334, by rfl⟩ : syracuseStep 4233779 = 6350669) B6350669
theorem B1882679 : Blo 1881142 1882679 := bstep (se 1 (by rfl) ⟨1412009, by rfl⟩ : syracuseStep 1882679 = 2824019) B2824019
theorem B4766273 : Blo 1881142 4766273 := bstep (se 2 (by rfl) ⟨1787352, by rfl⟩ : syracuseStep 4766273 = 3574705) B3574705
theorem B1882699 : Blo 1881142 1882699 := bstep (se 1 (by rfl) ⟨1412024, by rfl⟩ : syracuseStep 1882699 = 2824049) B2824049
theorem B4233815 : Blo 1881142 4233815 := bstep (se 1 (by rfl) ⟨3175361, by rfl⟩ : syracuseStep 4233815 = 6350723) B6350723
theorem B1882711 : Blo 1881142 1882711 := bstep (se 1 (by rfl) ⟨1412033, by rfl⟩ : syracuseStep 1882711 = 2824067) B2824067
theorem B3177049 : Blo 1881142 3177049 := bstep (se 2 (by rfl) ⟨1191393, by rfl⟩ : syracuseStep 3177049 = 2382787) B2382787
theorem B1882731 : Blo 1881142 1882731 := bstep (se 1 (by rfl) ⟨1412048, by rfl⟩ : syracuseStep 1882731 = 2824097) B2824097
theorem B1882743 : Blo 1881142 1882743 := bstep (se 1 (by rfl) ⟨1412057, by rfl⟩ : syracuseStep 1882743 = 2824115) B2824115
theorem B1882763 : Blo 1881142 1882763 := bstep (se 1 (by rfl) ⟨1412072, by rfl⟩ : syracuseStep 1882763 = 2824145) B2824145
theorem B1882775 : Blo 1881142 1882775 := bstep (se 1 (by rfl) ⟨1412081, by rfl⟩ : syracuseStep 1882775 = 2824163) B2824163
theorem B1882795 : Blo 1881142 1882795 := bstep (se 1 (by rfl) ⟨1412096, by rfl⟩ : syracuseStep 1882795 = 2824193) B2824193
theorem B1882807 : Blo 1881142 1882807 := bstep (se 1 (by rfl) ⟨1412105, by rfl⟩ : syracuseStep 1882807 = 2824211) B2824211
theorem B1882827 : Blo 1881142 1882827 := bstep (se 1 (by rfl) ⟨1412120, by rfl⟩ : syracuseStep 1882827 = 2824241) B2824241
theorem B1882839 : Blo 1881142 1882839 := bstep (se 1 (by rfl) ⟨1412129, by rfl⟩ : syracuseStep 1882839 = 2824259) B2824259
theorem B1882859 : Blo 1881142 1882859 := bstep (se 1 (by rfl) ⟨1412144, by rfl⟩ : syracuseStep 1882859 = 2824289) B2824289
theorem B1882871 : Blo 1881142 1882871 := bstep (se 1 (by rfl) ⟨1412153, by rfl⟩ : syracuseStep 1882871 = 2824307) B2824307
theorem B4233995 : Blo 1881142 4233995 := bstep (se 1 (by rfl) ⟨3175496, by rfl⟩ : syracuseStep 4233995 = 6350993) B6350993
theorem B1882891 : Blo 1881142 1882891 := bstep (se 1 (by rfl) ⟨1412168, by rfl⟩ : syracuseStep 1882891 = 2824337) B2824337
theorem B1882903 : Blo 1881142 1882903 := bstep (se 1 (by rfl) ⟨1412177, by rfl⟩ : syracuseStep 1882903 = 2824355) B2824355
theorem B1882923 : Blo 1881142 1882923 := bstep (se 1 (by rfl) ⟨1412192, by rfl⟩ : syracuseStep 1882923 = 2824385) B2824385
theorem B1882935 : Blo 1881142 1882935 := bstep (se 1 (by rfl) ⟨1412201, by rfl⟩ : syracuseStep 1882935 = 2824403) B2824403
theorem B4234049 : Blo 1881142 4234049 := bstep (se 2 (by rfl) ⟨1587768, by rfl⟩ : syracuseStep 4234049 = 3175537) B3175537
theorem B1882955 : Blo 1881142 1882955 := bstep (se 1 (by rfl) ⟨1412216, by rfl⟩ : syracuseStep 1882955 = 2824433) B2824433
theorem B1882967 : Blo 1881142 1882967 := bstep (se 1 (by rfl) ⟨1412225, by rfl⟩ : syracuseStep 1882967 = 2824451) B2824451
theorem B7633757 : Blo 1881142 7633757 := bstep (se 3 (by rfl) ⟨1431329, by rfl⟩ : syracuseStep 7633757 = 2862659) B2862659
theorem B11443045 : Blo 1881142 11443045 := bstep (se 4 (by rfl) ⟨1072785, by rfl⟩ : syracuseStep 11443045 = 2145571) B2145571
theorem B1882987 : Blo 1881142 1882987 := bstep (se 1 (by rfl) ⟨1412240, by rfl⟩ : syracuseStep 1882987 = 2824481) B2824481
theorem B1882999 : Blo 1881142 1882999 := bstep (se 1 (by rfl) ⟨1412249, by rfl⟩ : syracuseStep 1882999 = 2824499) B2824499
theorem B1883019 : Blo 1881142 1883019 := bstep (se 1 (by rfl) ⟨1412264, by rfl⟩ : syracuseStep 1883019 = 2824529) B2824529
theorem B1883031 : Blo 1881142 1883031 := bstep (se 1 (by rfl) ⟨1412273, by rfl⟩ : syracuseStep 1883031 = 2824547) B2824547
theorem B1883051 : Blo 1881142 1883051 := bstep (se 1 (by rfl) ⟨1412288, by rfl⟩ : syracuseStep 1883051 = 2824577) B2824577
theorem B1883063 : Blo 1881142 1883063 := bstep (se 1 (by rfl) ⟨1412297, by rfl⟩ : syracuseStep 1883063 = 2824595) B2824595
theorem B5086145 : Blo 1881142 5086145 := bstep (se 2 (by rfl) ⟨1907304, by rfl⟩ : syracuseStep 5086145 = 3814609) B3814609
theorem B1883083 : Blo 1881142 1883083 := bstep (se 1 (by rfl) ⟨1412312, by rfl⟩ : syracuseStep 1883083 = 2824625) B2824625
theorem B1883095 : Blo 1881142 1883095 := bstep (se 1 (by rfl) ⟨1412321, by rfl⟩ : syracuseStep 1883095 = 2824643) B2824643
theorem B6028253 : Blo 1881142 6028253 := bstep (se 3 (by rfl) ⟨1130297, by rfl⟩ : syracuseStep 6028253 = 2260595) B2260595
theorem B1883115 : Blo 1881142 1883115 := bstep (se 1 (by rfl) ⟨1412336, by rfl⟩ : syracuseStep 1883115 = 2824673) B2824673
theorem B1883127 : Blo 1881142 1883127 := bstep (se 1 (by rfl) ⟨1412345, by rfl⟩ : syracuseStep 1883127 = 2824691) B2824691
theorem B4234265 : Blo 1881142 4234265 := bstep (se 2 (by rfl) ⟨1587849, by rfl⟩ : syracuseStep 4234265 = 3175699) B3175699
theorem B16079917 : Blo 1881142 16079917 := bstep (se 3 (by rfl) ⟨3014984, by rfl⟩ : syracuseStep 16079917 = 6029969) B6029969
theorem B4234355 : Blo 1881142 4234355 := bstep (se 1 (by rfl) ⟨3175766, by rfl⟩ : syracuseStep 4234355 = 6351533) B6351533
theorem B3816587 : Blo 1881142 3816587 := bstep (se 1 (by rfl) ⟨2862440, by rfl⟩ : syracuseStep 3816587 = 5724881) B5724881
theorem B4234391 : Blo 1881142 4234391 := bstep (se 1 (by rfl) ⟨3175793, by rfl⟩ : syracuseStep 4234391 = 6351587) B6351587
theorem B3177623 : Blo 1881142 3177623 := bstep (se 1 (by rfl) ⟨2383217, by rfl⟩ : syracuseStep 3177623 = 4766435) B4766435
theorem B7240877 : Blo 1881142 7240877 := bstep (se 3 (by rfl) ⟨1357664, by rfl⟩ : syracuseStep 7240877 = 2715329) B2715329
theorem B7634179 : Blo 1881142 7634179 := bstep (se 1 (by rfl) ⟨5725634, by rfl⟩ : syracuseStep 7634179 = 11451269) B11451269
theorem B3177751 : Blo 1881142 3177751 := bstep (se 1 (by rfl) ⟨2383313, by rfl⟩ : syracuseStep 3177751 = 4766627) B4766627
theorem B4234571 : Blo 1881142 4234571 := bstep (se 1 (by rfl) ⟨3175928, by rfl⟩ : syracuseStep 4234571 = 6351857) B6351857
theorem B4234625 : Blo 1881142 4234625 := bstep (se 2 (by rfl) ⟨1587984, by rfl⟩ : syracuseStep 4234625 = 3175969) B3175969
theorem B8035757 : Blo 1881142 8035757 := bstep (se 3 (by rfl) ⟨1506704, by rfl⟩ : syracuseStep 8035757 = 3013409) B3013409
theorem B21429683 : Blo 1881142 21429683 := bstep (se 1 (by rfl) ⟨16072262, by rfl⟩ : syracuseStep 21429683 = 32144525) B32144525
theorem B7142849 : Blo 1881142 7142849 := bstep (se 2 (by rfl) ⟨2678568, by rfl⟩ : syracuseStep 7142849 = 5357137) B5357137
theorem B3390935 : Blo 1881142 3390935 := bstep (se 1 (by rfl) ⟨2543201, by rfl⟩ : syracuseStep 3390935 = 5086403) B5086403
theorem B5086685 : Blo 1881142 5086685 := bstep (se 3 (by rfl) ⟨953753, by rfl⟩ : syracuseStep 5086685 = 1907507) B1907507
theorem B3571265 : Blo 1881142 3571265 := bstep (se 2 (by rfl) ⟨1339224, by rfl⟩ : syracuseStep 3571265 = 2678449) B2678449
theorem B4021825 : Blo 1881142 4021825 := bstep (se 2 (by rfl) ⟨1508184, by rfl⟩ : syracuseStep 4021825 = 3016369) B3016369
theorem B3391051 : Blo 1881142 3391051 := bstep (se 1 (by rfl) ⟨2543288, by rfl⟩ : syracuseStep 3391051 = 5086577) B5086577
theorem B4292183 : Blo 1881142 4292183 := bstep (se 1 (by rfl) ⟨3219137, by rfl⟩ : syracuseStep 4292183 = 6438275) B6438275
theorem B4234841 : Blo 1881142 4234841 := bstep (se 2 (by rfl) ⟨1588065, by rfl⟩ : syracuseStep 4234841 = 3176131) B3176131
theorem B4234931 : Blo 1881142 4234931 := bstep (se 1 (by rfl) ⟨3176198, by rfl⟩ : syracuseStep 4234931 = 6352397) B6352397
theorem B8822465 : Blo 1881142 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B3669707 : Blo 1881142 3669707 := bstep (se 1 (by rfl) ⟨2752280, by rfl⟩ : syracuseStep 3669707 = 5504561) B5504561
theorem B4234967 : Blo 1881142 4234967 := bstep (se 1 (by rfl) ⟨3176225, by rfl⟩ : syracuseStep 4234967 = 6352451) B6352451
theorem B9527057 : Blo 1881142 9527057 := bstep (se 2 (by rfl) ⟨3572646, by rfl⟩ : syracuseStep 9527057 = 7145293) B7145293
theorem B6782737 : Blo 1881142 6782737 := bstep (se 2 (by rfl) ⟨2543526, by rfl⟩ : syracuseStep 6782737 = 5087053) B5087053
theorem B6029149 : Blo 1881142 6029149 := bstep (se 3 (by rfl) ⟨1130465, by rfl⟩ : syracuseStep 6029149 = 2260931) B2260931
theorem B4235147 : Blo 1881142 4235147 := bstep (se 1 (by rfl) ⟨3176360, by rfl⟩ : syracuseStep 4235147 = 6352721) B6352721
theorem B3571607 : Blo 1881142 3571607 := bstep (se 1 (by rfl) ⟨2678705, by rfl⟩ : syracuseStep 3571607 = 5357411) B5357411
theorem B25755569 : Blo 1881142 25755569 := bstep (se 2 (by rfl) ⟨9658338, by rfl⟩ : syracuseStep 25755569 = 19316677) B19316677
theorem B9527219 : Blo 1881142 9527219 := bstep (se 1 (by rfl) ⟨7145414, by rfl⟩ : syracuseStep 9527219 = 14290829) B14290829
theorem B4235201 : Blo 1881142 4235201 := bstep (se 2 (by rfl) ⟨1588200, by rfl⟩ : syracuseStep 4235201 = 3176401) B3176401
theorem B5357627 : Blo 1881142 5357627 := bstep (se 1 (by rfl) ⟨4018220, by rfl⟩ : syracuseStep 5357627 = 8036441) B8036441
theorem B6348887 : Blo 1881142 6348887 := bstep (se 1 (by rfl) ⟨4761665, by rfl⟩ : syracuseStep 6348887 = 9523331) B9523331
theorem B4235399 : Blo 1881142 4235399 := bstep (se 1 (by rfl) ⟨3176549, by rfl⟩ : syracuseStep 4235399 = 6353099) B6353099
theorem B220053685 : Blo 1881142 220053685 := bstep (se 5 (by rfl) ⟨10315016, by rfl⟩ : syracuseStep 220053685 = 20630033) B20630033
theorem B3014857 : Blo 1881142 3014857 := bstep (se 2 (by rfl) ⟨1130571, by rfl⟩ : syracuseStep 3014857 = 2261143) B2261143
theorem B4235579 : Blo 1881142 4235579 := bstep (se 1 (by rfl) ⟨3176684, by rfl⟩ : syracuseStep 4235579 = 6353369) B6353369
theorem B9527705 : Blo 1881142 9527705 := bstep (se 2 (by rfl) ⟨3572889, by rfl⟩ : syracuseStep 9527705 = 7145779) B7145779
theorem B4235705 : Blo 1881142 4235705 := bstep (se 2 (by rfl) ⟨1588389, by rfl⟩ : syracuseStep 4235705 = 3176779) B3176779
theorem B148750805 : Blo 1881142 148750805 := bstep (se 7 (by rfl) ⟨1743173, by rfl⟩ : syracuseStep 148750805 = 3486347) B3486347
theorem B6349373 : Blo 1881142 6349373 := bstep (se 3 (by rfl) ⟨1190507, by rfl⟩ : syracuseStep 6349373 = 2381015) B2381015
theorem B14287427 : Blo 1881142 14287427 := bstep (se 1 (by rfl) ⟨10715570, by rfl⟩ : syracuseStep 14287427 = 21431141) B21431141
theorem B5087897 : Blo 1881142 5087897 := bstep (se 2 (by rfl) ⟨1907961, by rfl⟩ : syracuseStep 5087897 = 3815923) B3815923
theorem B3572495 : Blo 1881142 3572495 := bstep (se 1 (by rfl) ⟨2679371, by rfl⟩ : syracuseStep 3572495 = 5358743) B5358743
theorem B4236047 : Blo 1881142 4236047 := bstep (se 1 (by rfl) ⟨3177035, by rfl⟩ : syracuseStep 4236047 = 6354071) B6354071
theorem B4236065 : Blo 1881142 4236065 := bstep (se 2 (by rfl) ⟨1588524, by rfl⟩ : syracuseStep 4236065 = 3177049) B3177049
theorem B7144307 : Blo 1881142 7144307 := bstep (se 1 (by rfl) ⟨5358230, by rfl⟩ : syracuseStep 7144307 = 10716461) B10716461
theorem B6030227 : Blo 1881142 6030227 := bstep (se 1 (by rfl) ⟨4522670, by rfl⟩ : syracuseStep 6030227 = 9045341) B9045341
theorem B2679799 : Blo 1881142 2679799 := bstep (se 1 (by rfl) ⟨2009849, by rfl⟩ : syracuseStep 2679799 = 4019699) B4019699
theorem B6030379 : Blo 1881142 6030379 := bstep (se 1 (by rfl) ⟨4522784, by rfl⟩ : syracuseStep 6030379 = 9045569) B9045569
theorem B3867707 : Blo 1881142 3867707 := bstep (se 1 (by rfl) ⟨2900780, by rfl⟩ : syracuseStep 3867707 = 5801561) B5801561
theorem B6112343 : Blo 1881142 6112343 := bstep (se 1 (by rfl) ⟨4584257, by rfl⟩ : syracuseStep 6112343 = 9168515) B9168515
theorem B4236407 : Blo 1881142 4236407 := bstep (se 1 (by rfl) ⟨3177305, by rfl⟩ : syracuseStep 4236407 = 6354611) B6354611
theorem B4523161 : Blo 1881142 4523161 := bstep (se 2 (by rfl) ⟨1696185, by rfl⟩ : syracuseStep 4523161 = 3392371) B3392371
theorem B4236587 : Blo 1881142 4236587 := bstep (se 1 (by rfl) ⟨3177440, by rfl⟩ : syracuseStep 4236587 = 6354881) B6354881
theorem B2680123 : Blo 1881142 2680123 := bstep (se 1 (by rfl) ⟨2010092, by rfl⟩ : syracuseStep 2680123 = 4020185) B4020185
theorem B40715621 : Blo 1881142 40715621 := bstep (se 4 (by rfl) ⟨3817089, by rfl⟩ : syracuseStep 40715621 = 7634179) B7634179
theorem B21439889 : Blo 1881142 21439889 := bstep (se 2 (by rfl) ⟨8039958, by rfl⟩ : syracuseStep 21439889 = 16079917) B16079917
theorem B10864151 : Blo 1881142 10864151 := bstep (se 1 (by rfl) ⟨8148113, by rfl⟩ : syracuseStep 10864151 = 16296227) B16296227
theorem B7243307 : Blo 1881142 7243307 := bstep (se 1 (by rfl) ⟨5432480, by rfl⟩ : syracuseStep 7243307 = 10864961) B10864961
theorem B4236947 : Blo 1881142 4236947 := bstep (se 1 (by rfl) ⟨3177710, by rfl⟩ : syracuseStep 4236947 = 6355421) B6355421
theorem B4294345 : Blo 1881142 4294345 := bstep (se 2 (by rfl) ⟨1610379, by rfl⟩ : syracuseStep 4294345 = 3220759) B3220759
theorem B4237001 : Blo 1881142 4237001 := bstep (se 2 (by rfl) ⟨1588875, by rfl⟩ : syracuseStep 4237001 = 3177751) B3177751
theorem B5089171 : Blo 1881142 5089171 := bstep (se 1 (by rfl) ⟨3816878, by rfl⟩ : syracuseStep 5089171 = 7633757) B7633757
theorem B6350777 : Blo 1881142 6350777 := bstep (se 2 (by rfl) ⟨2381541, by rfl⟩ : syracuseStep 6350777 = 4763083) B4763083
theorem B4827251 : Blo 1881142 4827251 := bstep (se 1 (by rfl) ⟨3620438, by rfl⟩ : syracuseStep 4827251 = 7240877) B7240877
theorem B36169973 : Blo 1881142 36169973 := bstep (se 5 (by rfl) ⟨1695467, by rfl⟩ : syracuseStep 36169973 = 3390935) B3390935
theorem B22898933 : Blo 1881142 22898933 := bstep (se 5 (by rfl) ⟨1073387, by rfl⟩ : syracuseStep 22898933 = 2146775) B2146775
theorem B4409633 : Blo 1881142 4409633 := bstep (se 2 (by rfl) ⟨1653612, by rfl⟩ : syracuseStep 4409633 = 3307225) B3307225
theorem B4761899 : Blo 1881142 4761899 := bstep (se 1 (by rfl) ⟨3571424, by rfl⟩ : syracuseStep 4761899 = 7142849) B7142849
theorem B3574135 : Blo 1881142 3574135 := bstep (se 1 (by rfl) ⟨2680601, by rfl⟩ : syracuseStep 3574135 = 5361203) B5361203
theorem B2861455 : Blo 1881142 2861455 := bstep (se 1 (by rfl) ⟨2146091, by rfl⟩ : syracuseStep 2861455 = 4292183) B4292183
theorem B8038865 : Blo 1881142 8038865 := bstep (se 2 (by rfl) ⟨3014574, by rfl⟩ : syracuseStep 8038865 = 6029149) B6029149
theorem B6351371 : Blo 1881142 6351371 := bstep (se 1 (by rfl) ⟨4763528, by rfl⟩ : syracuseStep 6351371 = 9527057) B9527057
theorem B6351479 : Blo 1881142 6351479 := bstep (se 1 (by rfl) ⟨4763609, by rfl⟩ : syracuseStep 6351479 = 9527219) B9527219
theorem B5720843 : Blo 1881142 5720843 := bstep (se 1 (by rfl) ⟨4290632, by rfl⟩ : syracuseStep 5720843 = 8581265) B8581265
theorem B6785851 : Blo 1881142 6785851 := bstep (se 1 (by rfl) ⟨5089388, by rfl⟩ : syracuseStep 6785851 = 10178777) B10178777
theorem B5360519 : Blo 1881142 5360519 := bstep (se 1 (by rfl) ⟨4020389, by rfl⟩ : syracuseStep 5360519 = 8040779) B8040779
theorem B9530297 : Blo 1881142 9530297 := bstep (se 2 (by rfl) ⟨3573861, by rfl⟩ : syracuseStep 9530297 = 7147723) B7147723
theorem B2116615 : Blo 1881142 2116615 := bstep (se 1 (by rfl) ⟨1587461, by rfl⟩ : syracuseStep 2116615 = 3174923) B3174923
theorem B7146539 : Blo 1881142 7146539 := bstep (se 1 (by rfl) ⟨5359904, by rfl⟩ : syracuseStep 7146539 = 10719809) B10719809
theorem B4762739 : Blo 1881142 4762739 := bstep (se 1 (by rfl) ⟨3572054, by rfl⟩ : syracuseStep 4762739 = 7144109) B7144109
theorem B4762759 : Blo 1881142 4762759 := bstep (se 1 (by rfl) ⟨3572069, by rfl⟩ : syracuseStep 4762759 = 7144139) B7144139
theorem B2116795 : Blo 1881142 2116795 := bstep (se 1 (by rfl) ⟨1587596, by rfl⟩ : syracuseStep 2116795 = 3175193) B3175193
theorem B6352073 : Blo 1881142 6352073 := bstep (se 2 (by rfl) ⟨2382027, by rfl⟩ : syracuseStep 6352073 = 4764055) B4764055
theorem B9653593 : Blo 1881142 9653593 := bstep (se 2 (by rfl) ⟨3620097, by rfl⟩ : syracuseStep 9653593 = 7240195) B7240195
theorem B43470179 : Blo 1881142 43470179 := bstep (se 1 (by rfl) ⟨32602634, by rfl⟩ : syracuseStep 43470179 = 65205269) B65205269
theorem B2010511 : Blo 1881142 2010511 := bstep (se 1 (by rfl) ⟨1507883, by rfl⟩ : syracuseStep 2010511 = 3015767) B3015767
theorem B4763033 : Blo 1881142 4763033 := bstep (se 2 (by rfl) ⟨1786137, by rfl⟩ : syracuseStep 4763033 = 3572275) B3572275
theorem B2862635 : Blo 1881142 2862635 := bstep (se 1 (by rfl) ⟨2146976, by rfl⟩ : syracuseStep 2862635 = 4293953) B4293953
theorem B4763195 : Blo 1881142 4763195 := bstep (se 1 (by rfl) ⟨3572396, by rfl⟩ : syracuseStep 4763195 = 7144793) B7144793
theorem B2821751 : Blo 1881142 2821751 := bstep (se 1 (by rfl) ⟨2116313, by rfl⟩ : syracuseStep 2821751 = 4232627) B4232627
theorem B2821775 : Blo 1881142 2821775 := bstep (se 1 (by rfl) ⟨2116331, by rfl⟩ : syracuseStep 2821775 = 4232663) B4232663
theorem B2117263 : Blo 1881142 2117263 := bstep (se 1 (by rfl) ⟨1587947, by rfl⟩ : syracuseStep 2117263 = 3175895) B3175895
theorem B2821817 : Blo 1881142 2821817 := bstep (se 2 (by rfl) ⟨1058181, by rfl⟩ : syracuseStep 2821817 = 2116363) B2116363
theorem B8580809 : Blo 1881142 8580809 := bstep (se 2 (by rfl) ⟨3217803, by rfl⟩ : syracuseStep 8580809 = 6435607) B6435607
theorem B8589037 : Blo 1881142 8589037 := bstep (se 3 (by rfl) ⟨1610444, by rfl⟩ : syracuseStep 8589037 = 3220889) B3220889
theorem B2821895 : Blo 1881142 2821895 := bstep (se 1 (by rfl) ⟨2116421, by rfl⟩ : syracuseStep 2821895 = 4232843) B4232843
theorem B4763407 : Blo 1881142 4763407 := bstep (se 1 (by rfl) ⟨3572555, by rfl⟩ : syracuseStep 4763407 = 7145111) B7145111
theorem B6524705 : Blo 1881142 6524705 := bstep (se 2 (by rfl) ⟨2446764, by rfl⟩ : syracuseStep 6524705 = 4893529) B4893529
theorem B2821931 : Blo 1881142 2821931 := bstep (se 1 (by rfl) ⟨2116448, by rfl⟩ : syracuseStep 2821931 = 4232897) B4232897
theorem B15257393 : Blo 1881142 15257393 := bstep (se 2 (by rfl) ⟨5721522, by rfl⟩ : syracuseStep 15257393 = 11443045) B11443045
theorem B2821961 : Blo 1881142 2821961 := bstep (se 2 (by rfl) ⟨1058235, by rfl⟩ : syracuseStep 2821961 = 2116471) B2116471
theorem B6352775 : Blo 1881142 6352775 := bstep (se 1 (by rfl) ⟨4764581, by rfl⟩ : syracuseStep 6352775 = 9529163) B9529163
theorem B2715535 : Blo 1881142 2715535 := bstep (se 1 (by rfl) ⟨2036651, by rfl⟩ : syracuseStep 2715535 = 4073303) B4073303
theorem B9047953 : Blo 1881142 9047953 := bstep (se 2 (by rfl) ⟨3392982, by rfl⟩ : syracuseStep 9047953 = 6785965) B6785965
theorem B2822075 : Blo 1881142 2822075 := bstep (se 1 (by rfl) ⟨2116556, by rfl⟩ : syracuseStep 2822075 = 4233113) B4233113
theorem B9048029 : Blo 1881142 9048029 := bstep (se 3 (by rfl) ⟨1696505, by rfl⟩ : syracuseStep 9048029 = 3393011) B3393011
theorem B2822135 : Blo 1881142 2822135 := bstep (se 1 (by rfl) ⟨2116601, by rfl⟩ : syracuseStep 2822135 = 4233203) B4233203
theorem B2822159 : Blo 1881142 2822159 := bstep (se 1 (by rfl) ⟨2116619, by rfl⟩ : syracuseStep 2822159 = 4233239) B4233239
theorem B4763681 : Blo 1881142 4763681 := bstep (se 2 (by rfl) ⟨1786380, by rfl⟩ : syracuseStep 4763681 = 3572761) B3572761
theorem B8040491 : Blo 1881142 8040491 := bstep (se 1 (by rfl) ⟨6030368, by rfl⟩ : syracuseStep 8040491 = 12060737) B12060737
theorem B2822201 : Blo 1881142 2822201 := bstep (se 2 (by rfl) ⟨1058325, by rfl⟩ : syracuseStep 2822201 = 2116651) B2116651
theorem B2822279 : Blo 1881142 2822279 := bstep (se 1 (by rfl) ⟨2116709, by rfl⟩ : syracuseStep 2822279 = 4233419) B4233419
theorem B2117767 : Blo 1881142 2117767 := bstep (se 1 (by rfl) ⟨1588325, by rfl⟩ : syracuseStep 2117767 = 3176651) B3176651
theorem B2822315 : Blo 1881142 2822315 := bstep (se 1 (by rfl) ⟨2116736, by rfl⟩ : syracuseStep 2822315 = 4233473) B4233473
theorem B2822345 : Blo 1881142 2822345 := bstep (se 2 (by rfl) ⟨1058379, by rfl⟩ : syracuseStep 2822345 = 2116759) B2116759
theorem B9531593 : Blo 1881142 9531593 := bstep (se 2 (by rfl) ⟨3574347, by rfl⟩ : syracuseStep 9531593 = 7148695) B7148695
theorem B21442805 : Blo 1881142 21442805 := bstep (se 5 (by rfl) ⟨1005131, by rfl⟩ : syracuseStep 21442805 = 2010263) B2010263
theorem B6353153 : Blo 1881142 6353153 := bstep (se 2 (by rfl) ⟨2382432, by rfl⟩ : syracuseStep 6353153 = 4764865) B4764865
theorem B9040187 : Blo 1881142 9040187 := bstep (se 1 (by rfl) ⟨6780140, by rfl⟩ : syracuseStep 9040187 = 13560281) B13560281
theorem B15257915 : Blo 1881142 15257915 := bstep (se 1 (by rfl) ⟨11443436, by rfl⟩ : syracuseStep 15257915 = 22886873) B22886873
theorem B2822459 : Blo 1881142 2822459 := bstep (se 1 (by rfl) ⟨2116844, by rfl⟩ : syracuseStep 2822459 = 4233689) B4233689
theorem B2117947 : Blo 1881142 2117947 := bstep (se 1 (by rfl) ⟨1588460, by rfl⟩ : syracuseStep 2117947 = 3176921) B3176921
theorem B108532061 : Blo 1881142 108532061 := bstep (se 3 (by rfl) ⟨20349761, by rfl⟩ : syracuseStep 108532061 = 40699523) B40699523
theorem B2822519 : Blo 1881142 2822519 := bstep (se 1 (by rfl) ⟨2116889, by rfl⟩ : syracuseStep 2822519 = 4233779) B4233779
theorem B2822543 : Blo 1881142 2822543 := bstep (se 1 (by rfl) ⟨2116907, by rfl⟩ : syracuseStep 2822543 = 4233815) B4233815
theorem B2822585 : Blo 1881142 2822585 := bstep (se 2 (by rfl) ⟨1058469, by rfl⟩ : syracuseStep 2822585 = 2116939) B2116939
theorem B14299577 : Blo 1881142 14299577 := bstep (se 2 (by rfl) ⟨5362341, by rfl⟩ : syracuseStep 14299577 = 10724683) B10724683
theorem B10170883 : Blo 1881142 10170883 := bstep (se 1 (by rfl) ⟨7628162, by rfl⟩ : syracuseStep 10170883 = 15256325) B15256325
theorem B2822663 : Blo 1881142 2822663 := bstep (se 1 (by rfl) ⟨2116997, by rfl⟩ : syracuseStep 2822663 = 4233995) B4233995
theorem B2822699 : Blo 1881142 2822699 := bstep (se 1 (by rfl) ⟨2117024, by rfl⟩ : syracuseStep 2822699 = 4234049) B4234049
theorem B2822729 : Blo 1881142 2822729 := bstep (se 2 (by rfl) ⟨1058523, by rfl⟩ : syracuseStep 2822729 = 2117047) B2117047
theorem B3175031 : Blo 1881142 3175031 := bstep (se 1 (by rfl) ⟨2381273, by rfl⟩ : syracuseStep 3175031 = 4762547) B4762547
theorem B4018835 : Blo 1881142 4018835 := bstep (se 1 (by rfl) ⟨3014126, by rfl⟩ : syracuseStep 4018835 = 6028253) B6028253
theorem B2822843 : Blo 1881142 2822843 := bstep (se 1 (by rfl) ⟨2117132, by rfl⟩ : syracuseStep 2822843 = 4234265) B4234265
theorem B2822903 : Blo 1881142 2822903 := bstep (se 1 (by rfl) ⟨2117177, by rfl⟩ : syracuseStep 2822903 = 4234355) B4234355
theorem B7631617 : Blo 1881142 7631617 := bstep (se 2 (by rfl) ⟨2861856, by rfl⟩ : syracuseStep 7631617 = 5723713) B5723713
theorem B5362433 : Blo 1881142 5362433 := bstep (se 2 (by rfl) ⟨2010912, by rfl⟩ : syracuseStep 5362433 = 4021825) B4021825
theorem B2544391 : Blo 1881142 2544391 := bstep (se 1 (by rfl) ⟨1908293, by rfl⟩ : syracuseStep 2544391 = 3816587) B3816587
theorem B2822927 : Blo 1881142 2822927 := bstep (se 1 (by rfl) ⟨2117195, by rfl⟩ : syracuseStep 2822927 = 4234391) B4234391
theorem B2118415 : Blo 1881142 2118415 := bstep (se 1 (by rfl) ⟨1588811, by rfl⟩ : syracuseStep 2118415 = 3177623) B3177623
theorem B2822969 : Blo 1881142 2822969 := bstep (se 2 (by rfl) ⟨1058613, by rfl⟩ : syracuseStep 2822969 = 2117227) B2117227
theorem B14291801 : Blo 1881142 14291801 := bstep (se 2 (by rfl) ⟨5359425, by rfl⟩ : syracuseStep 14291801 = 10718851) B10718851
theorem B2823047 : Blo 1881142 2823047 := bstep (se 1 (by rfl) ⟨2117285, by rfl⟩ : syracuseStep 2823047 = 4234571) B4234571
theorem B2823083 : Blo 1881142 2823083 := bstep (se 1 (by rfl) ⟨2117312, by rfl⟩ : syracuseStep 2823083 = 4234625) B4234625
theorem B2823113 : Blo 1881142 2823113 := bstep (se 2 (by rfl) ⟨1058667, by rfl⟩ : syracuseStep 2823113 = 2117335) B2117335
theorem B4764683 : Blo 1881142 4764683 := bstep (se 1 (by rfl) ⟨3573512, by rfl⟩ : syracuseStep 4764683 = 7147025) B7147025
theorem B2380843 : Blo 1881142 2380843 := bstep (se 1 (by rfl) ⟨1785632, by rfl⟩ : syracuseStep 2380843 = 3571265) B3571265
theorem B6353963 : Blo 1881142 6353963 := bstep (se 1 (by rfl) ⟨4765472, by rfl⟩ : syracuseStep 6353963 = 9530945) B9530945
theorem B1881147 : Blo 1881142 1881147 := bstep (se 1 (by rfl) ⟨1410860, by rfl⟩ : syracuseStep 1881147 = 2821721) B2821721
theorem B3175483 : Blo 1881142 3175483 := bstep (se 1 (by rfl) ⟨2381612, by rfl⟩ : syracuseStep 3175483 = 4763225) B4763225
theorem B2823227 : Blo 1881142 2823227 := bstep (se 1 (by rfl) ⟨2117420, by rfl⟩ : syracuseStep 2823227 = 4234841) B4234841
theorem B2823287 : Blo 1881142 2823287 := bstep (se 1 (by rfl) ⟨2117465, by rfl⟩ : syracuseStep 2823287 = 4234931) B4234931
theorem B1881223 : Blo 1881142 1881223 := bstep (se 1 (by rfl) ⟨1410917, by rfl⟩ : syracuseStep 1881223 = 2821835) B2821835
theorem B2446471 : Blo 1881142 2446471 := bstep (se 1 (by rfl) ⟨1834853, by rfl⟩ : syracuseStep 2446471 = 3669707) B3669707
theorem B1881231 : Blo 1881142 1881231 := bstep (se 1 (by rfl) ⟨1410923, by rfl⟩ : syracuseStep 1881231 = 2821847) B2821847
theorem B2823311 : Blo 1881142 2823311 := bstep (se 1 (by rfl) ⟨2117483, by rfl⟩ : syracuseStep 2823311 = 4234967) B4234967
theorem B2823353 : Blo 1881142 2823353 := bstep (se 2 (by rfl) ⟨1058757, by rfl⟩ : syracuseStep 2823353 = 2117515) B2117515
theorem B1881275 : Blo 1881142 1881275 := bstep (se 1 (by rfl) ⟨1410956, by rfl⟩ : syracuseStep 1881275 = 2821913) B2821913
theorem B3175625 : Blo 1881142 3175625 := bstep (se 2 (by rfl) ⟨1190859, by rfl⟩ : syracuseStep 3175625 = 2381719) B2381719
theorem B18093293 : Blo 1881142 18093293 := bstep (se 3 (by rfl) ⟨3392492, by rfl⟩ : syracuseStep 18093293 = 6784985) B6784985
theorem B49575149 : Blo 1881142 49575149 := bstep (se 3 (by rfl) ⟨9295340, by rfl⟩ : syracuseStep 49575149 = 18590681) B18590681
theorem B1881351 : Blo 1881142 1881351 := bstep (se 1 (by rfl) ⟨1411013, by rfl⟩ : syracuseStep 1881351 = 2822027) B2822027
theorem B2823431 : Blo 1881142 2823431 := bstep (se 1 (by rfl) ⟨2117573, by rfl⟩ : syracuseStep 2823431 = 4235147) B4235147
theorem B2381071 : Blo 1881142 2381071 := bstep (se 1 (by rfl) ⟨1785803, by rfl⟩ : syracuseStep 2381071 = 3571607) B3571607
theorem B1881359 : Blo 1881142 1881359 := bstep (se 1 (by rfl) ⟨1411019, by rfl⟩ : syracuseStep 1881359 = 2822039) B2822039
theorem B2823467 : Blo 1881142 2823467 := bstep (se 1 (by rfl) ⟨2117600, by rfl⟩ : syracuseStep 2823467 = 4235201) B4235201
theorem B1881403 : Blo 1881142 1881403 := bstep (se 1 (by rfl) ⟨1411052, by rfl⟩ : syracuseStep 1881403 = 2822105) B2822105
theorem B2823497 : Blo 1881142 2823497 := bstep (se 2 (by rfl) ⟨1058811, by rfl⟩ : syracuseStep 2823497 = 2117623) B2117623
theorem B61052291 : Blo 1881142 61052291 := bstep (se 1 (by rfl) ⟨45789218, by rfl⟩ : syracuseStep 61052291 = 91578437) B91578437
theorem B1881479 : Blo 1881142 1881479 := bstep (se 1 (by rfl) ⟨1411109, by rfl⟩ : syracuseStep 1881479 = 2822219) B2822219
theorem B1881487 : Blo 1881142 1881487 := bstep (se 1 (by rfl) ⟨1411115, by rfl⟩ : syracuseStep 1881487 = 2822231) B2822231
theorem B9524627 : Blo 1881142 9524627 := bstep (se 1 (by rfl) ⟨7143470, by rfl⟩ : syracuseStep 9524627 = 14286941) B14286941
theorem B12227987 : Blo 1881142 12227987 := bstep (se 1 (by rfl) ⟨9170990, by rfl⟩ : syracuseStep 12227987 = 18341981) B18341981
theorem B1881531 : Blo 1881142 1881531 := bstep (se 1 (by rfl) ⟨1411148, by rfl⟩ : syracuseStep 1881531 = 2822297) B2822297
theorem B2823611 : Blo 1881142 2823611 := bstep (se 1 (by rfl) ⟨2117708, by rfl⟩ : syracuseStep 2823611 = 4235417) B4235417
theorem B2823671 : Blo 1881142 2823671 := bstep (se 1 (by rfl) ⟨2117753, by rfl⟩ : syracuseStep 2823671 = 4235507) B4235507
theorem B9655811 : Blo 1881142 9655811 := bstep (se 1 (by rfl) ⟨7241858, by rfl⟩ : syracuseStep 9655811 = 14483717) B14483717
theorem B1881607 : Blo 1881142 1881607 := bstep (se 1 (by rfl) ⟨1411205, by rfl⟩ : syracuseStep 1881607 = 2822411) B2822411
theorem B1881615 : Blo 1881142 1881615 := bstep (se 1 (by rfl) ⟨1411211, by rfl⟩ : syracuseStep 1881615 = 2822423) B2822423
theorem B2823695 : Blo 1881142 2823695 := bstep (se 1 (by rfl) ⟨2117771, by rfl⟩ : syracuseStep 2823695 = 4235543) B4235543
theorem B2823737 : Blo 1881142 2823737 := bstep (se 2 (by rfl) ⟨1058901, by rfl⟩ : syracuseStep 2823737 = 2117803) B2117803
theorem B1881659 : Blo 1881142 1881659 := bstep (se 1 (by rfl) ⟨1411244, by rfl⟩ : syracuseStep 1881659 = 2822489) B2822489
theorem B8582723 : Blo 1881142 8582723 := bstep (se 1 (by rfl) ⟨6437042, by rfl⟩ : syracuseStep 8582723 = 12874085) B12874085
theorem B10720835 : Blo 1881142 10720835 := bstep (se 1 (by rfl) ⟨8040626, by rfl⟩ : syracuseStep 10720835 = 16081253) B16081253
theorem B1881735 : Blo 1881142 1881735 := bstep (se 1 (by rfl) ⟨1411301, by rfl⟩ : syracuseStep 1881735 = 2822603) B2822603
theorem B2823815 : Blo 1881142 2823815 := bstep (se 1 (by rfl) ⟨2117861, by rfl⟩ : syracuseStep 2823815 = 4235723) B4235723
theorem B1881743 : Blo 1881142 1881743 := bstep (se 1 (by rfl) ⟨1411307, by rfl⟩ : syracuseStep 1881743 = 2822615) B2822615
theorem B4765331 : Blo 1881142 4765331 := bstep (se 1 (by rfl) ⟨3573998, by rfl⟩ : syracuseStep 4765331 = 7147997) B7147997
theorem B2823851 : Blo 1881142 2823851 := bstep (se 1 (by rfl) ⟨2117888, by rfl⟩ : syracuseStep 2823851 = 4235777) B4235777
theorem B1881787 : Blo 1881142 1881787 := bstep (se 1 (by rfl) ⟨1411340, by rfl⟩ : syracuseStep 1881787 = 2822681) B2822681
theorem B2823881 : Blo 1881142 2823881 := bstep (se 2 (by rfl) ⟨1058955, by rfl⟩ : syracuseStep 2823881 = 2117911) B2117911
theorem B1881863 : Blo 1881142 1881863 := bstep (se 1 (by rfl) ⟨1411397, by rfl⟩ : syracuseStep 1881863 = 2822795) B2822795
theorem B6027023 : Blo 1881142 6027023 := bstep (se 1 (by rfl) ⟨4520267, by rfl⟩ : syracuseStep 6027023 = 9040535) B9040535
theorem B1881871 : Blo 1881142 1881871 := bstep (se 1 (by rfl) ⟨1411403, by rfl⟩ : syracuseStep 1881871 = 2822807) B2822807
theorem B14292773 : Blo 1881142 14292773 := bstep (se 4 (by rfl) ⟨1339947, by rfl⟩ : syracuseStep 14292773 = 2679895) B2679895
theorem B10180403 : Blo 1881142 10180403 := bstep (se 1 (by rfl) ⟨7635302, by rfl⟩ : syracuseStep 10180403 = 15270605) B15270605
theorem B1881915 : Blo 1881142 1881915 := bstep (se 1 (by rfl) ⟨1411436, by rfl⟩ : syracuseStep 1881915 = 2822873) B2822873
theorem B2823995 : Blo 1881142 2823995 := bstep (se 1 (by rfl) ⟨2117996, by rfl⟩ : syracuseStep 2823995 = 4235993) B4235993
theorem B2824055 : Blo 1881142 2824055 := bstep (se 1 (by rfl) ⟨2118041, by rfl⟩ : syracuseStep 2824055 = 4236083) B4236083
theorem B4233095 : Blo 1881142 4233095 := bstep (se 1 (by rfl) ⟨3174821, by rfl⟩ : syracuseStep 4233095 = 6349643) B6349643
theorem B1881991 : Blo 1881142 1881991 := bstep (se 1 (by rfl) ⟨1411493, by rfl⟩ : syracuseStep 1881991 = 2822987) B2822987
theorem B3176327 : Blo 1881142 3176327 := bstep (se 1 (by rfl) ⟨2382245, by rfl⟩ : syracuseStep 3176327 = 4764491) B4764491
theorem B1881999 : Blo 1881142 1881999 := bstep (se 1 (by rfl) ⟨1411499, by rfl⟩ : syracuseStep 1881999 = 2822999) B2822999
theorem B2824079 : Blo 1881142 2824079 := bstep (se 1 (by rfl) ⟨2118059, by rfl⟩ : syracuseStep 2824079 = 4236119) B4236119
theorem B4765625 : Blo 1881142 4765625 := bstep (se 2 (by rfl) ⟨1787109, by rfl⟩ : syracuseStep 4765625 = 3574219) B3574219
theorem B2824121 : Blo 1881142 2824121 := bstep (se 2 (by rfl) ⟨1059045, by rfl⟩ : syracuseStep 2824121 = 2118091) B2118091
theorem B1882043 : Blo 1881142 1882043 := bstep (se 1 (by rfl) ⟨1411532, by rfl⟩ : syracuseStep 1882043 = 2823065) B2823065
theorem B2381815 : Blo 1881142 2381815 := bstep (se 1 (by rfl) ⟨1786361, by rfl⟩ : syracuseStep 2381815 = 3572723) B3572723
theorem B1882119 : Blo 1881142 1882119 := bstep (se 1 (by rfl) ⟨1411589, by rfl⟩ : syracuseStep 1882119 = 2823179) B2823179
theorem B2824199 : Blo 1881142 2824199 := bstep (se 1 (by rfl) ⟨2118149, by rfl⟩ : syracuseStep 2824199 = 4236299) B4236299
theorem B1882127 : Blo 1881142 1882127 := bstep (se 1 (by rfl) ⟨1411595, by rfl⟩ : syracuseStep 1882127 = 2823191) B2823191
theorem B4519979 : Blo 1881142 4519979 := bstep (se 1 (by rfl) ⟨3389984, by rfl⟩ : syracuseStep 4519979 = 6779969) B6779969
theorem B2824235 : Blo 1881142 2824235 := bstep (se 1 (by rfl) ⟨2118176, by rfl⟩ : syracuseStep 2824235 = 4236353) B4236353
theorem B4233275 : Blo 1881142 4233275 := bstep (se 1 (by rfl) ⟨3174956, by rfl⟩ : syracuseStep 4233275 = 6349913) B6349913
theorem B1882171 : Blo 1881142 1882171 := bstep (se 1 (by rfl) ⟨1411628, by rfl⟩ : syracuseStep 1882171 = 2823257) B2823257
theorem B2824265 : Blo 1881142 2824265 := bstep (se 2 (by rfl) ⟨1059099, by rfl⟩ : syracuseStep 2824265 = 2118199) B2118199
theorem B1882247 : Blo 1881142 1882247 := bstep (se 1 (by rfl) ⟨1411685, by rfl⟩ : syracuseStep 1882247 = 2823371) B2823371
theorem B1882255 : Blo 1881142 1882255 := bstep (se 1 (by rfl) ⟨1411691, by rfl⟩ : syracuseStep 1882255 = 2823383) B2823383
theorem B4290707 : Blo 1881142 4290707 := bstep (se 1 (by rfl) ⟨3218030, by rfl⟩ : syracuseStep 4290707 = 6436061) B6436061
theorem B4233401 : Blo 1881142 4233401 := bstep (se 2 (by rfl) ⟨1587525, by rfl⟩ : syracuseStep 4233401 = 3175051) B3175051
theorem B1882299 : Blo 1881142 1882299 := bstep (se 1 (by rfl) ⟨1411724, by rfl⟩ : syracuseStep 1882299 = 2823449) B2823449
theorem B2824379 : Blo 1881142 2824379 := bstep (se 1 (by rfl) ⟨2118284, by rfl⟩ : syracuseStep 2824379 = 4236569) B4236569
theorem B2824439 : Blo 1881142 2824439 := bstep (se 1 (by rfl) ⟨2118329, by rfl⟩ : syracuseStep 2824439 = 4236659) B4236659
theorem B1882375 : Blo 1881142 1882375 := bstep (se 1 (by rfl) ⟨1411781, by rfl⟩ : syracuseStep 1882375 = 2823563) B2823563
theorem B1882383 : Blo 1881142 1882383 := bstep (se 1 (by rfl) ⟨1411787, by rfl⟩ : syracuseStep 1882383 = 2823575) B2823575
theorem B2824463 : Blo 1881142 2824463 := bstep (se 1 (by rfl) ⟨2118347, by rfl⟩ : syracuseStep 2824463 = 4236695) B4236695
theorem B7346465 : Blo 1881142 7346465 := bstep (se 2 (by rfl) ⟨2754924, by rfl⟩ : syracuseStep 7346465 = 5509849) B5509849
theorem B2382139 : Blo 1881142 2382139 := bstep (se 1 (by rfl) ⟨1786604, by rfl⟩ : syracuseStep 2382139 = 3573209) B3573209
theorem B1882427 : Blo 1881142 1882427 := bstep (se 1 (by rfl) ⟨1411820, by rfl⟩ : syracuseStep 1882427 = 2823641) B2823641
theorem B2824505 : Blo 1881142 2824505 := bstep (se 2 (by rfl) ⟨1059189, by rfl⟩ : syracuseStep 2824505 = 2118379) B2118379
theorem B6355259 : Blo 1881142 6355259 := bstep (se 1 (by rfl) ⟨4766444, by rfl⟩ : syracuseStep 6355259 = 9532889) B9532889
theorem B1882503 : Blo 1881142 1882503 := bstep (se 1 (by rfl) ⟨1411877, by rfl⟩ : syracuseStep 1882503 = 2823755) B2823755
theorem B2824583 : Blo 1881142 2824583 := bstep (se 1 (by rfl) ⟨2118437, by rfl⟩ : syracuseStep 2824583 = 4236875) B4236875
theorem B1882511 : Blo 1881142 1882511 := bstep (se 1 (by rfl) ⟨1411883, by rfl⟩ : syracuseStep 1882511 = 2823767) B2823767
theorem B7149971 : Blo 1881142 7149971 := bstep (se 1 (by rfl) ⟨5362478, by rfl⟩ : syracuseStep 7149971 = 10724957) B10724957
theorem B2824619 : Blo 1881142 2824619 := bstep (se 1 (by rfl) ⟨2118464, by rfl⟩ : syracuseStep 2824619 = 4236929) B4236929
theorem B1882555 : Blo 1881142 1882555 := bstep (se 1 (by rfl) ⟨1411916, by rfl⟩ : syracuseStep 1882555 = 2823833) B2823833
theorem B2824649 : Blo 1881142 2824649 := bstep (se 2 (by rfl) ⟨1059243, by rfl⟩ : syracuseStep 2824649 = 2118487) B2118487
theorem B1882631 : Blo 1881142 1882631 := bstep (se 1 (by rfl) ⟨1411973, by rfl⟩ : syracuseStep 1882631 = 2823947) B2823947
theorem B4233743 : Blo 1881142 4233743 := bstep (se 1 (by rfl) ⟨3175307, by rfl⟩ : syracuseStep 4233743 = 6350615) B6350615
theorem B1882639 : Blo 1881142 1882639 := bstep (se 1 (by rfl) ⟨1411979, by rfl⟩ : syracuseStep 1882639 = 2823959) B2823959
theorem B3176975 : Blo 1881142 3176975 := bstep (se 1 (by rfl) ⟨2382731, by rfl⟩ : syracuseStep 3176975 = 4765463) B4765463
theorem B4233761 : Blo 1881142 4233761 := bstep (se 2 (by rfl) ⟨1587660, by rfl⟩ : syracuseStep 4233761 = 3175321) B3175321
theorem B1882683 : Blo 1881142 1882683 := bstep (se 1 (by rfl) ⟨1412012, by rfl⟩ : syracuseStep 1882683 = 2824025) B2824025
theorem B13564493 : Blo 1881142 13564493 := bstep (se 3 (by rfl) ⟨2543342, by rfl⟩ : syracuseStep 13564493 = 5086685) B5086685
theorem B4766323 : Blo 1881142 4766323 := bstep (se 1 (by rfl) ⟨3574742, by rfl⟩ : syracuseStep 4766323 = 7149485) B7149485
theorem B1882759 : Blo 1881142 1882759 := bstep (se 1 (by rfl) ⟨1412069, by rfl⟩ : syracuseStep 1882759 = 2824139) B2824139
theorem B1882767 : Blo 1881142 1882767 := bstep (se 1 (by rfl) ⟨1412075, by rfl⟩ : syracuseStep 1882767 = 2824151) B2824151
theorem B1882811 : Blo 1881142 1882811 := bstep (se 1 (by rfl) ⟨1412108, by rfl⟩ : syracuseStep 1882811 = 2824217) B2824217
theorem B4766465 : Blo 1881142 4766465 := bstep (se 2 (by rfl) ⟨1787424, by rfl⟩ : syracuseStep 4766465 = 3574849) B3574849
theorem B1882887 : Blo 1881142 1882887 := bstep (se 1 (by rfl) ⟨1412165, by rfl⟩ : syracuseStep 1882887 = 2824331) B2824331
theorem B1882895 : Blo 1881142 1882895 := bstep (se 1 (by rfl) ⟨1412171, by rfl⟩ : syracuseStep 1882895 = 2824343) B2824343
theorem B2382635 : Blo 1881142 2382635 := bstep (se 1 (by rfl) ⟨1786976, by rfl⟩ : syracuseStep 2382635 = 3573953) B3573953
theorem B1882939 : Blo 1881142 1882939 := bstep (se 1 (by rfl) ⟨1412204, by rfl⟩ : syracuseStep 1882939 = 2824409) B2824409
theorem B12229465 : Blo 1881142 12229465 := bstep (se 2 (by rfl) ⟨4586049, by rfl⟩ : syracuseStep 12229465 = 9172099) B9172099
theorem B4234103 : Blo 1881142 4234103 := bstep (se 1 (by rfl) ⟨3175577, by rfl⟩ : syracuseStep 4234103 = 6351155) B6351155
theorem B1883015 : Blo 1881142 1883015 := bstep (se 1 (by rfl) ⟨1412261, by rfl⟩ : syracuseStep 1883015 = 2824523) B2824523
theorem B1883023 : Blo 1881142 1883023 := bstep (se 1 (by rfl) ⟨1412267, by rfl⟩ : syracuseStep 1883023 = 2824535) B2824535
theorem B1883067 : Blo 1881142 1883067 := bstep (se 1 (by rfl) ⟨1412300, by rfl⟩ : syracuseStep 1883067 = 2824601) B2824601
theorem B11451395 : Blo 1881142 11451395 := bstep (se 1 (by rfl) ⟨8588546, by rfl⟩ : syracuseStep 11451395 = 17177093) B17177093
theorem B6437917 : Blo 1881142 6437917 := bstep (se 3 (by rfl) ⟨1207109, by rfl⟩ : syracuseStep 6437917 = 2414219) B2414219
theorem B4234283 : Blo 1881142 4234283 := bstep (se 1 (by rfl) ⟨3175712, by rfl⟩ : syracuseStep 4234283 = 6351425) B6351425
theorem B3177515 : Blo 1881142 3177515 := bstep (se 1 (by rfl) ⟨2383136, by rfl⟩ : syracuseStep 3177515 = 4766273) B4766273
theorem B5725441 : Blo 1881142 5725441 := bstep (se 2 (by rfl) ⟨2147040, by rfl⟩ : syracuseStep 5725441 = 4294081) B4294081
theorem B2383111 : Blo 1881142 2383111 := bstep (se 1 (by rfl) ⟨1787333, by rfl⟩ : syracuseStep 2383111 = 3574667) B3574667
theorem B3390763 : Blo 1881142 3390763 := bstep (se 1 (by rfl) ⟨2543072, by rfl⟩ : syracuseStep 3390763 = 5086145) B5086145
theorem B4234643 : Blo 1881142 4234643 := bstep (se 1 (by rfl) ⟨3175982, by rfl⟩ : syracuseStep 4234643 = 6351965) B6351965
theorem B4521401 : Blo 1881142 4521401 := bstep (se 2 (by rfl) ⟨1695525, by rfl⟩ : syracuseStep 4521401 = 3391051) B3391051
theorem B4234697 : Blo 1881142 4234697 := bstep (se 2 (by rfl) ⟨1588011, by rfl⟩ : syracuseStep 4234697 = 3176023) B3176023
theorem B5430817 : Blo 1881142 5430817 := bstep (se 2 (by rfl) ⟨2036556, by rfl⟩ : syracuseStep 5430817 = 4073113) B4073113
theorem B5357171 : Blo 1881142 5357171 := bstep (se 1 (by rfl) ⟨4017878, by rfl⟩ : syracuseStep 5357171 = 8035757) B8035757
theorem B14286455 : Blo 1881142 14286455 := bstep (se 1 (by rfl) ⟨10714841, by rfl⟩ : syracuseStep 14286455 = 21429683) B21429683
theorem B19570355 : Blo 1881142 19570355 := bstep (se 1 (by rfl) ⟨14677766, by rfl⟩ : syracuseStep 19570355 = 29355533) B29355533
theorem B19324595 : Blo 1881142 19324595 := bstep (se 1 (by rfl) ⟨14493446, by rfl⟩ : syracuseStep 19324595 = 28986893) B28986893
theorem B9043649 : Blo 1881142 9043649 := bstep (se 2 (by rfl) ⟨3391368, by rfl⟩ : syracuseStep 9043649 = 6782737) B6782737
theorem B6438689 : Blo 1881142 6438689 := bstep (se 2 (by rfl) ⟨2414508, by rfl⟩ : syracuseStep 6438689 = 4829017) B4829017
theorem B5881643 : Blo 1881142 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B10723225 : Blo 1881142 10723225 := bstep (se 2 (by rfl) ⟨4021209, by rfl⟩ : syracuseStep 10723225 = 8042419) B8042419
theorem B17170379 : Blo 1881142 17170379 := bstep (se 1 (by rfl) ⟨12877784, by rfl⟩ : syracuseStep 17170379 = 25755569) B25755569
theorem B3571751 : Blo 1881142 3571751 := bstep (se 1 (by rfl) ⟨2678813, by rfl⟩ : syracuseStep 3571751 = 5357627) B5357627
theorem B10313885 : Blo 1881142 10313885 := bstep (se 3 (by rfl) ⟨1933853, by rfl⟩ : syracuseStep 10313885 = 3867707) B3867707
theorem B14295203 : Blo 1881142 14295203 := bstep (se 1 (by rfl) ⟨10721402, by rfl⟩ : syracuseStep 14295203 = 21442805) B21442805
theorem B4235435 : Blo 1881142 4235435 := bstep (se 1 (by rfl) ⟨3176576, by rfl⟩ : syracuseStep 4235435 = 6353153) B6353153
theorem B32162021 : Blo 1881142 32162021 := bstep (se 4 (by rfl) ⟨3015189, by rfl⟩ : syracuseStep 32162021 = 6030379) B6030379
theorem B293404913 : Blo 1881142 293404913 := bstep (se 2 (by rfl) ⟨110026842, by rfl⟩ : syracuseStep 293404913 = 220053685) B220053685
theorem B3391931 : Blo 1881142 3391931 := bstep (se 1 (by rfl) ⟨2543948, by rfl⟩ : syracuseStep 3391931 = 5087897) B5087897
theorem B9527867 : Blo 1881142 9527867 := bstep (se 1 (by rfl) ⟨7145900, by rfl⟩ : syracuseStep 9527867 = 14291801) B14291801
theorem B4235975 : Blo 1881142 4235975 := bstep (se 1 (by rfl) ⟨3176981, by rfl⟩ : syracuseStep 4235975 = 6353963) B6353963
theorem B6349751 : Blo 1881142 6349751 := bstep (se 1 (by rfl) ⟨4762313, by rfl⟩ : syracuseStep 6349751 = 9524627) B9524627
theorem B10175489 : Blo 1881142 10175489 := bstep (se 2 (by rfl) ⟨3815808, by rfl⟩ : syracuseStep 10175489 = 7631617) B7631617
theorem B7242767 : Blo 1881142 7242767 := bstep (se 1 (by rfl) ⟨5432075, by rfl⟩ : syracuseStep 7242767 = 10864151) B10864151
theorem B9528515 : Blo 1881142 9528515 := bstep (se 1 (by rfl) ⟨7146386, by rfl⟩ : syracuseStep 9528515 = 14292773) B14292773
theorem B3573065 : Blo 1881142 3573065 := bstep (se 2 (by rfl) ⟨1339899, by rfl⟩ : syracuseStep 3573065 = 2679799) B2679799
theorem B2860471 : Blo 1881142 2860471 := bstep (se 1 (by rfl) ⟨2145353, by rfl⟩ : syracuseStep 2860471 = 4290707) B4290707
theorem B3261961 : Blo 1881142 3261961 := bstep (se 2 (by rfl) ⟨1223235, by rfl⟩ : syracuseStep 3261961 = 2446471) B2446471
theorem B6350345 : Blo 1881142 6350345 := bstep (se 2 (by rfl) ⟨2381379, by rfl⟩ : syracuseStep 6350345 = 4762759) B4762759
theorem B6030881 : Blo 1881142 6030881 := bstep (se 2 (by rfl) ⟨2261580, by rfl⟩ : syracuseStep 6030881 = 4523161) B4523161
theorem B4236839 : Blo 1881142 4236839 := bstep (se 1 (by rfl) ⟨3177629, by rfl⟩ : syracuseStep 4236839 = 6355259) B6355259
theorem B10716893 : Blo 1881142 10716893 := bstep (se 3 (by rfl) ⟨2009417, by rfl⟩ : syracuseStep 10716893 = 4018835) B4018835
theorem B3573497 : Blo 1881142 3573497 := bstep (se 2 (by rfl) ⟨1340061, by rfl⟩ : syracuseStep 3573497 = 2680123) B2680123
theorem B12871457 : Blo 1881142 12871457 := bstep (se 2 (by rfl) ⟨4826796, by rfl⟩ : syracuseStep 12871457 = 9653593) B9653593
theorem B6351209 : Blo 1881142 6351209 := bstep (se 2 (by rfl) ⟨2381703, by rfl⟩ : syracuseStep 6351209 = 4763407) B4763407
theorem B5720539 : Blo 1881142 5720539 := bstep (se 1 (by rfl) ⟨4290404, by rfl⟩ : syracuseStep 5720539 = 8580809) B8580809
theorem B6785561 : Blo 1881142 6785561 := bstep (se 2 (by rfl) ⟨2544585, by rfl⟩ : syracuseStep 6785561 = 5089171) B5089171
theorem B14297633 : Blo 1881142 14297633 := bstep (se 2 (by rfl) ⟨5361612, by rfl⟩ : syracuseStep 14297633 = 10723225) B10723225
theorem B24128077 : Blo 1881142 24128077 := bstep (se 3 (by rfl) ⟨4524014, by rfl⟩ : syracuseStep 24128077 = 9048029) B9048029
theorem B11446919 : Blo 1881142 11446919 := bstep (se 1 (by rfl) ⟨8585189, by rfl⟩ : syracuseStep 11446919 = 17170379) B17170379
theorem B5360327 : Blo 1881142 5360327 := bstep (se 1 (by rfl) ⟨4020245, by rfl⟩ : syracuseStep 5360327 = 8040491) B8040491
theorem B72354707 : Blo 1881142 72354707 := bstep (se 1 (by rfl) ⟨54266030, by rfl⟩ : syracuseStep 72354707 = 108532061) B108532061
theorem B6351803 : Blo 1881142 6351803 := bstep (se 1 (by rfl) ⟨4763852, by rfl⟩ : syracuseStep 6351803 = 9527705) B9527705
theorem B99167203 : Blo 1881142 99167203 := bstep (se 1 (by rfl) ⟨74375402, by rfl⟩ : syracuseStep 99167203 = 148750805) B148750805
theorem B2116687 : Blo 1881142 2116687 := bstep (se 1 (by rfl) ⟨1587515, by rfl⟩ : syracuseStep 2116687 = 3175031) B3175031
theorem B3574955 : Blo 1881142 3574955 := bstep (se 1 (by rfl) ⟨2681216, by rfl⟩ : syracuseStep 3574955 = 5362433) B5362433
theorem B4762871 : Blo 1881142 4762871 := bstep (se 1 (by rfl) ⟨3572153, by rfl⟩ : syracuseStep 4762871 = 7144307) B7144307
theorem B13561177 : Blo 1881142 13561177 := bstep (se 2 (by rfl) ⟨5085441, by rfl⟩ : syracuseStep 13561177 = 10170883) B10170883
theorem B4074895 : Blo 1881142 4074895 := bstep (se 1 (by rfl) ⟨3056171, by rfl⟩ : syracuseStep 4074895 = 6112343) B6112343
theorem B11759021 : Blo 1881142 11759021 := bstep (se 3 (by rfl) ⟨2204816, by rfl⟩ : syracuseStep 11759021 = 4409633) B4409633
theorem B2117083 : Blo 1881142 2117083 := bstep (se 1 (by rfl) ⟨1587812, by rfl⟩ : syracuseStep 2117083 = 3175625) B3175625
theorem B12062195 : Blo 1881142 12062195 := bstep (se 1 (by rfl) ⟨9046646, by rfl⟩ : syracuseStep 12062195 = 18093293) B18093293
theorem B33050099 : Blo 1881142 33050099 := bstep (se 1 (by rfl) ⟨24787574, by rfl⟩ : syracuseStep 33050099 = 49575149) B49575149
theorem B27143747 : Blo 1881142 27143747 := bstep (se 1 (by rfl) ⟨20357810, by rfl⟩ : syracuseStep 27143747 = 40715621) B40715621
theorem B40701527 : Blo 1881142 40701527 := bstep (se 1 (by rfl) ⟨30526145, by rfl⟩ : syracuseStep 40701527 = 61052291) B61052291
theorem B4828871 : Blo 1881142 4828871 := bstep (se 1 (by rfl) ⟨3621653, by rfl⟩ : syracuseStep 4828871 = 7243307) B7243307
theorem B5721815 : Blo 1881142 5721815 := bstep (se 1 (by rfl) ⟨4291361, by rfl⟩ : syracuseStep 5721815 = 8582723) B8582723
theorem B7147223 : Blo 1881142 7147223 := bstep (se 1 (by rfl) ⟨5360417, by rfl⟩ : syracuseStep 7147223 = 10720835) B10720835
theorem B32607965 : Blo 1881142 32607965 := bstep (se 3 (by rfl) ⟨6113993, by rfl⟩ : syracuseStep 32607965 = 12227987) B12227987
theorem B9047801 : Blo 1881142 9047801 := bstep (se 2 (by rfl) ⟨3392925, by rfl⟩ : syracuseStep 9047801 = 6785851) B6785851
theorem B16305953 : Blo 1881142 16305953 := bstep (se 2 (by rfl) ⟨6114732, by rfl⟩ : syracuseStep 16305953 = 12229465) B12229465
theorem B4018015 : Blo 1881142 4018015 := bstep (se 1 (by rfl) ⟨3013511, by rfl⟩ : syracuseStep 4018015 = 6027023) B6027023
theorem B6786935 : Blo 1881142 6786935 := bstep (se 1 (by rfl) ⟨5090201, by rfl⟩ : syracuseStep 6786935 = 10180403) B10180403
theorem B2822063 : Blo 1881142 2822063 := bstep (se 1 (by rfl) ⟨2116547, by rfl⟩ : syracuseStep 2822063 = 4233095) B4233095
theorem B2117551 : Blo 1881142 2117551 := bstep (se 1 (by rfl) ⟨1588163, by rfl⟩ : syracuseStep 2117551 = 3176327) B3176327
theorem B2822153 : Blo 1881142 2822153 := bstep (se 2 (by rfl) ⟨1058307, by rfl⟩ : syracuseStep 2822153 = 2116615) B2116615
theorem B13570085 : Blo 1881142 13570085 := bstep (se 4 (by rfl) ⟨1272195, by rfl⟩ : syracuseStep 13570085 = 2544391) B2544391
theorem B2822183 : Blo 1881142 2822183 := bstep (se 1 (by rfl) ⟨2116637, by rfl⟩ : syracuseStep 2822183 = 4233275) B4233275
theorem B3174457 : Blo 1881142 3174457 := bstep (se 2 (by rfl) ⟨1190421, by rfl⟩ : syracuseStep 3174457 = 2380843) B2380843
theorem B2822267 : Blo 1881142 2822267 := bstep (se 1 (by rfl) ⟨2116700, by rfl⟩ : syracuseStep 2822267 = 4233401) B4233401
theorem B24113315 : Blo 1881142 24113315 := bstep (se 1 (by rfl) ⟨18084986, by rfl⟩ : syracuseStep 24113315 = 36169973) B36169973
theorem B15265955 : Blo 1881142 15265955 := bstep (se 1 (by rfl) ⟨11449466, by rfl⟩ : syracuseStep 15265955 = 22898933) B22898933
theorem B3174599 : Blo 1881142 3174599 := bstep (se 1 (by rfl) ⟨2380949, by rfl⟩ : syracuseStep 3174599 = 4761899) B4761899
theorem B2822393 : Blo 1881142 2822393 := bstep (se 2 (by rfl) ⟨1058397, by rfl⟩ : syracuseStep 2822393 = 2116795) B2116795
theorem B2822495 : Blo 1881142 2822495 := bstep (se 1 (by rfl) ⟨2116871, by rfl⟩ : syracuseStep 2822495 = 4233743) B4233743
theorem B2117983 : Blo 1881142 2117983 := bstep (se 1 (by rfl) ⟨1588487, by rfl⟩ : syracuseStep 2117983 = 3176975) B3176975
theorem B3174761 : Blo 1881142 3174761 := bstep (se 2 (by rfl) ⟨1190535, by rfl⟩ : syracuseStep 3174761 = 2381071) B2381071
theorem B2822507 : Blo 1881142 2822507 := bstep (se 1 (by rfl) ⟨2116880, by rfl⟩ : syracuseStep 2822507 = 4233761) B4233761
theorem B3813895 : Blo 1881142 3813895 := bstep (se 1 (by rfl) ⟨2860421, by rfl⟩ : syracuseStep 3813895 = 5720843) B5720843
theorem B2822735 : Blo 1881142 2822735 := bstep (se 1 (by rfl) ⟨2117051, by rfl⟩ : syracuseStep 2822735 = 4234103) B4234103
theorem B6353531 : Blo 1881142 6353531 := bstep (se 1 (by rfl) ⟨4765148, by rfl⟩ : syracuseStep 6353531 = 9530297) B9530297
theorem B2822855 : Blo 1881142 2822855 := bstep (se 1 (by rfl) ⟨2117141, by rfl⟩ : syracuseStep 2822855 = 4234283) B4234283
theorem B4764359 : Blo 1881142 4764359 := bstep (se 1 (by rfl) ⟨3573269, by rfl⟩ : syracuseStep 4764359 = 7146539) B7146539
theorem B2118343 : Blo 1881142 2118343 := bstep (se 1 (by rfl) ⟨1588757, by rfl⟩ : syracuseStep 2118343 = 3177515) B3177515
theorem B3175159 : Blo 1881142 3175159 := bstep (se 1 (by rfl) ⟨2381369, by rfl⟩ : syracuseStep 3175159 = 4762739) B4762739
theorem B6353693 : Blo 1881142 6353693 := bstep (se 3 (by rfl) ⟨1191317, by rfl⟩ : syracuseStep 6353693 = 2382635) B2382635
theorem B2823017 : Blo 1881142 2823017 := bstep (se 2 (by rfl) ⟨1058631, by rfl⟩ : syracuseStep 2823017 = 2117263) B2117263
theorem B28980119 : Blo 1881142 28980119 := bstep (se 1 (by rfl) ⟨21735089, by rfl⟩ : syracuseStep 28980119 = 43470179) B43470179
theorem B2823095 : Blo 1881142 2823095 := bstep (se 1 (by rfl) ⟨2117321, by rfl⟩ : syracuseStep 2823095 = 4234643) B4234643
theorem B3175355 : Blo 1881142 3175355 := bstep (se 1 (by rfl) ⟨2381516, by rfl⟩ : syracuseStep 3175355 = 4763033) B4763033
theorem B2823131 : Blo 1881142 2823131 := bstep (se 1 (by rfl) ⟨2117348, by rfl⟩ : syracuseStep 2823131 = 4234697) B4234697
theorem B3175463 : Blo 1881142 3175463 := bstep (se 1 (by rfl) ⟨2381597, by rfl⟩ : syracuseStep 3175463 = 4763195) B4763195
theorem B1881167 : Blo 1881142 1881167 := bstep (se 1 (by rfl) ⟨1410875, by rfl⟩ : syracuseStep 1881167 = 2821751) B2821751
theorem B9524303 : Blo 1881142 9524303 := bstep (se 1 (by rfl) ⟨7143227, by rfl⟩ : syracuseStep 9524303 = 14286455) B14286455
theorem B1881183 : Blo 1881142 1881183 := bstep (se 1 (by rfl) ⟨1410887, by rfl⟩ : syracuseStep 1881183 = 2821775) B2821775
theorem B13046903 : Blo 1881142 13046903 := bstep (se 1 (by rfl) ⟨9785177, by rfl⟩ : syracuseStep 13046903 = 19570355) B19570355
theorem B1881211 : Blo 1881142 1881211 := bstep (se 1 (by rfl) ⟨1410908, by rfl⟩ : syracuseStep 1881211 = 2821817) B2821817
theorem B12883063 : Blo 1881142 12883063 := bstep (se 1 (by rfl) ⟨9662297, by rfl⟩ : syracuseStep 12883063 = 19324595) B19324595
theorem B1881263 : Blo 1881142 1881263 := bstep (se 1 (by rfl) ⟨1410947, by rfl⟩ : syracuseStep 1881263 = 2821895) B2821895
theorem B12063937 : Blo 1881142 12063937 := bstep (se 2 (by rfl) ⟨4523976, by rfl⟩ : syracuseStep 12063937 = 9047953) B9047953
theorem B1881287 : Blo 1881142 1881287 := bstep (se 1 (by rfl) ⟨1410965, by rfl⟩ : syracuseStep 1881287 = 2821931) B2821931
theorem B3921095 : Blo 1881142 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B10171595 : Blo 1881142 10171595 := bstep (se 1 (by rfl) ⟨7628696, by rfl⟩ : syracuseStep 10171595 = 15257393) B15257393
theorem B1881307 : Blo 1881142 1881307 := bstep (se 1 (by rfl) ⟨1410980, by rfl⟩ : syracuseStep 1881307 = 2821961) B2821961
theorem B1881383 : Blo 1881142 1881383 := bstep (se 1 (by rfl) ⟨1411037, by rfl⟩ : syracuseStep 1881383 = 2822075) B2822075
theorem B3175753 : Blo 1881142 3175753 := bstep (se 2 (by rfl) ⟨1190907, by rfl⟩ : syracuseStep 3175753 = 2381815) B2381815
theorem B1881423 : Blo 1881142 1881423 := bstep (se 1 (by rfl) ⟨1411067, by rfl⟩ : syracuseStep 1881423 = 2822135) B2822135
theorem B1881439 : Blo 1881142 1881439 := bstep (se 1 (by rfl) ⟨1411079, by rfl⟩ : syracuseStep 1881439 = 2822159) B2822159
theorem B3175787 : Blo 1881142 3175787 := bstep (se 1 (by rfl) ⟨2381840, by rfl⟩ : syracuseStep 3175787 = 4763681) B4763681
theorem B1881467 : Blo 1881142 1881467 := bstep (se 1 (by rfl) ⟨1411100, by rfl⟩ : syracuseStep 1881467 = 2822201) B2822201
theorem B4232591 : Blo 1881142 4232591 := bstep (se 1 (by rfl) ⟨3174443, by rfl⟩ : syracuseStep 4232591 = 6348887) B6348887
theorem B1881519 : Blo 1881142 1881519 := bstep (se 1 (by rfl) ⟨1411139, by rfl⟩ : syracuseStep 1881519 = 2822279) B2822279
theorem B2823599 : Blo 1881142 2823599 := bstep (se 1 (by rfl) ⟨2117699, by rfl⟩ : syracuseStep 2823599 = 4235399) B4235399
theorem B1881543 : Blo 1881142 1881543 := bstep (se 1 (by rfl) ⟨1411157, by rfl⟩ : syracuseStep 1881543 = 2822315) B2822315
theorem B1881563 : Blo 1881142 1881563 := bstep (se 1 (by rfl) ⟨1411172, by rfl⟩ : syracuseStep 1881563 = 2822345) B2822345
theorem B6354395 : Blo 1881142 6354395 := bstep (se 1 (by rfl) ⟨4765796, by rfl⟩ : syracuseStep 6354395 = 9531593) B9531593
theorem B2823689 : Blo 1881142 2823689 := bstep (se 2 (by rfl) ⟨1058883, by rfl⟩ : syracuseStep 2823689 = 2117767) B2117767
theorem B10171943 : Blo 1881142 10171943 := bstep (se 1 (by rfl) ⟨7628957, by rfl⟩ : syracuseStep 10171943 = 15257915) B15257915
theorem B1881639 : Blo 1881142 1881639 := bstep (se 1 (by rfl) ⟨1411229, by rfl⟩ : syracuseStep 1881639 = 2822459) B2822459
theorem B2823719 : Blo 1881142 2823719 := bstep (se 1 (by rfl) ⟨2117789, by rfl⟩ : syracuseStep 2823719 = 4235579) B4235579
theorem B1881679 : Blo 1881142 1881679 := bstep (se 1 (by rfl) ⟨1411259, by rfl⟩ : syracuseStep 1881679 = 2822519) B2822519
theorem B1881695 : Blo 1881142 1881695 := bstep (se 1 (by rfl) ⟨1411271, by rfl⟩ : syracuseStep 1881695 = 2822543) B2822543
theorem B4019809 : Blo 1881142 4019809 := bstep (se 2 (by rfl) ⟨1507428, by rfl⟩ : syracuseStep 4019809 = 3014857) B3014857
theorem B1881723 : Blo 1881142 1881723 := bstep (se 1 (by rfl) ⟨1411292, by rfl⟩ : syracuseStep 1881723 = 2822585) B2822585
theorem B2823803 : Blo 1881142 2823803 := bstep (se 1 (by rfl) ⟨2117852, by rfl⟩ : syracuseStep 2823803 = 4235705) B4235705
theorem B9533051 : Blo 1881142 9533051 := bstep (se 1 (by rfl) ⟨7149788, by rfl⟩ : syracuseStep 9533051 = 14299577) B14299577
theorem B1881775 : Blo 1881142 1881775 := bstep (se 1 (by rfl) ⟨1411331, by rfl⟩ : syracuseStep 1881775 = 2822663) B2822663
theorem B1881799 : Blo 1881142 1881799 := bstep (se 1 (by rfl) ⟨1411349, by rfl⟩ : syracuseStep 1881799 = 2822699) B2822699
theorem B4232915 : Blo 1881142 4232915 := bstep (se 1 (by rfl) ⟨3174686, by rfl⟩ : syracuseStep 4232915 = 6349373) B6349373
theorem B9524951 : Blo 1881142 9524951 := bstep (se 1 (by rfl) ⟨7143713, by rfl⟩ : syracuseStep 9524951 = 14287427) B14287427
theorem B1881819 : Blo 1881142 1881819 := bstep (se 1 (by rfl) ⟨1411364, by rfl⟩ : syracuseStep 1881819 = 2822729) B2822729
theorem B3176185 : Blo 1881142 3176185 := bstep (se 2 (by rfl) ⟨1191069, by rfl⟩ : syracuseStep 3176185 = 2382139) B2382139
theorem B2823929 : Blo 1881142 2823929 := bstep (se 2 (by rfl) ⟨1058973, by rfl⟩ : syracuseStep 2823929 = 2117947) B2117947
theorem B1881895 : Blo 1881142 1881895 := bstep (se 1 (by rfl) ⟨1411421, by rfl⟩ : syracuseStep 1881895 = 2822843) B2822843
theorem B4765513 : Blo 1881142 4765513 := bstep (se 2 (by rfl) ⟨1787067, by rfl⟩ : syracuseStep 4765513 = 3574135) B3574135
theorem B1881935 : Blo 1881142 1881935 := bstep (se 1 (by rfl) ⟨1411451, by rfl⟩ : syracuseStep 1881935 = 2822903) B2822903
theorem B2381663 : Blo 1881142 2381663 := bstep (se 1 (by rfl) ⟨1786247, by rfl⟩ : syracuseStep 2381663 = 3572495) B3572495
theorem B1881951 : Blo 1881142 1881951 := bstep (se 1 (by rfl) ⟨1411463, by rfl⟩ : syracuseStep 1881951 = 2822927) B2822927
theorem B2824031 : Blo 1881142 2824031 := bstep (se 1 (by rfl) ⟨2118023, by rfl⟩ : syracuseStep 2824031 = 4236047) B4236047
theorem B3815273 : Blo 1881142 3815273 := bstep (se 2 (by rfl) ⟨1430727, by rfl⟩ : syracuseStep 3815273 = 2861455) B2861455
theorem B2824043 : Blo 1881142 2824043 := bstep (se 1 (by rfl) ⟨2118032, by rfl⟩ : syracuseStep 2824043 = 4236065) B4236065
theorem B1881979 : Blo 1881142 1881979 := bstep (se 1 (by rfl) ⟨1411484, by rfl⟩ : syracuseStep 1881979 = 2822969) B2822969
theorem B1882031 : Blo 1881142 1882031 := bstep (se 1 (by rfl) ⟨1411523, by rfl⟩ : syracuseStep 1882031 = 2823047) B2823047
theorem B4020151 : Blo 1881142 4020151 := bstep (se 1 (by rfl) ⟨3015113, by rfl⟩ : syracuseStep 4020151 = 6030227) B6030227
theorem B1882055 : Blo 1881142 1882055 := bstep (se 1 (by rfl) ⟨1411541, by rfl⟩ : syracuseStep 1882055 = 2823083) B2823083
theorem B1882075 : Blo 1881142 1882075 := bstep (se 1 (by rfl) ⟨1411556, by rfl⟩ : syracuseStep 1882075 = 2823113) B2823113
theorem B3176455 : Blo 1881142 3176455 := bstep (se 1 (by rfl) ⟨2382341, by rfl⟩ : syracuseStep 3176455 = 4764683) B4764683
theorem B1882151 : Blo 1881142 1882151 := bstep (se 1 (by rfl) ⟨1411613, by rfl⟩ : syracuseStep 1882151 = 2823227) B2823227
theorem B1882191 : Blo 1881142 1882191 := bstep (se 1 (by rfl) ⟨1411643, by rfl⟩ : syracuseStep 1882191 = 2823287) B2823287
theorem B2824271 : Blo 1881142 2824271 := bstep (se 1 (by rfl) ⟨2118203, by rfl⟩ : syracuseStep 2824271 = 4236407) B4236407
theorem B1882207 : Blo 1881142 1882207 := bstep (se 1 (by rfl) ⟨1411655, by rfl⟩ : syracuseStep 1882207 = 2823311) B2823311
theorem B1882235 : Blo 1881142 1882235 := bstep (se 1 (by rfl) ⟨1411676, by rfl⟩ : syracuseStep 1882235 = 2823353) B2823353
theorem B6355097 : Blo 1881142 6355097 := bstep (se 2 (by rfl) ⟨2383161, by rfl⟩ : syracuseStep 6355097 = 4766323) B4766323
theorem B24107165 : Blo 1881142 24107165 := bstep (se 3 (by rfl) ⟨4520093, by rfl⟩ : syracuseStep 24107165 = 9040187) B9040187
theorem B1882287 : Blo 1881142 1882287 := bstep (se 1 (by rfl) ⟨1411715, by rfl⟩ : syracuseStep 1882287 = 2823431) B2823431
theorem B1882311 : Blo 1881142 1882311 := bstep (se 1 (by rfl) ⟨1411733, by rfl⟩ : syracuseStep 1882311 = 2823467) B2823467
theorem B2824391 : Blo 1881142 2824391 := bstep (se 1 (by rfl) ⟨2118293, by rfl⟩ : syracuseStep 2824391 = 4236587) B4236587
theorem B1882331 : Blo 1881142 1882331 := bstep (se 1 (by rfl) ⟨1411748, by rfl⟩ : syracuseStep 1882331 = 2823497) B2823497
theorem B14293259 : Blo 1881142 14293259 := bstep (se 1 (by rfl) ⟨10719944, by rfl⟩ : syracuseStep 14293259 = 21439889) B21439889
theorem B1882407 : Blo 1881142 1882407 := bstep (se 1 (by rfl) ⟨1411805, by rfl⟩ : syracuseStep 1882407 = 2823611) B2823611
theorem B1882447 : Blo 1881142 1882447 := bstep (se 1 (by rfl) ⟨1411835, by rfl⟩ : syracuseStep 1882447 = 2823671) B2823671
theorem B6437207 : Blo 1881142 6437207 := bstep (se 1 (by rfl) ⟨4827905, by rfl⟩ : syracuseStep 6437207 = 9655811) B9655811
theorem B1882463 : Blo 1881142 1882463 := bstep (se 1 (by rfl) ⟨1411847, by rfl⟩ : syracuseStep 1882463 = 2823695) B2823695
theorem B2824553 : Blo 1881142 2824553 := bstep (se 2 (by rfl) ⟨1059207, by rfl⟩ : syracuseStep 2824553 = 2118415) B2118415
theorem B1882491 : Blo 1881142 1882491 := bstep (se 1 (by rfl) ⟨1411868, by rfl⟩ : syracuseStep 1882491 = 2823737) B2823737
theorem B1882543 : Blo 1881142 1882543 := bstep (se 1 (by rfl) ⟨1411907, by rfl⟩ : syracuseStep 1882543 = 2823815) B2823815
theorem B3176887 : Blo 1881142 3176887 := bstep (se 1 (by rfl) ⟨2382665, by rfl⟩ : syracuseStep 3176887 = 4765331) B4765331
theorem B2824631 : Blo 1881142 2824631 := bstep (se 1 (by rfl) ⟨2118473, by rfl⟩ : syracuseStep 2824631 = 4236947) B4236947
theorem B1882567 : Blo 1881142 1882567 := bstep (se 1 (by rfl) ⟨1411925, by rfl⟩ : syracuseStep 1882567 = 2823851) B2823851
theorem B1882587 : Blo 1881142 1882587 := bstep (se 1 (by rfl) ⟨1411940, by rfl⟩ : syracuseStep 1882587 = 2823881) B2823881
theorem B2824667 : Blo 1881142 2824667 := bstep (se 1 (by rfl) ⟨2118500, by rfl⟩ : syracuseStep 2824667 = 4237001) B4237001
theorem B1882663 : Blo 1881142 1882663 := bstep (se 1 (by rfl) ⟨1411997, by rfl⟩ : syracuseStep 1882663 = 2823995) B2823995
theorem B21436973 : Blo 1881142 21436973 := bstep (se 3 (by rfl) ⟨4019432, by rfl⟩ : syracuseStep 21436973 = 8038865) B8038865
theorem B1882703 : Blo 1881142 1882703 := bstep (se 1 (by rfl) ⟨1412027, by rfl⟩ : syracuseStep 1882703 = 2824055) B2824055
theorem B1882719 : Blo 1881142 1882719 := bstep (se 1 (by rfl) ⟨1412039, by rfl⟩ : syracuseStep 1882719 = 2824079) B2824079
theorem B4233851 : Blo 1881142 4233851 := bstep (se 1 (by rfl) ⟨3175388, by rfl⟩ : syracuseStep 4233851 = 6350777) B6350777
theorem B3177083 : Blo 1881142 3177083 := bstep (se 1 (by rfl) ⟨2382812, by rfl⟩ : syracuseStep 3177083 = 4765625) B4765625
theorem B1882747 : Blo 1881142 1882747 := bstep (se 1 (by rfl) ⟨1412060, by rfl⟩ : syracuseStep 1882747 = 2824121) B2824121
theorem B1882799 : Blo 1881142 1882799 := bstep (se 1 (by rfl) ⟨1412099, by rfl⟩ : syracuseStep 1882799 = 2824199) B2824199
theorem B3013319 : Blo 1881142 3013319 := bstep (se 1 (by rfl) ⟨2259989, by rfl⟩ : syracuseStep 3013319 = 4519979) B4519979
theorem B1882823 : Blo 1881142 1882823 := bstep (se 1 (by rfl) ⟨1412117, by rfl⟩ : syracuseStep 1882823 = 2824235) B2824235
theorem B8583889 : Blo 1881142 8583889 := bstep (se 2 (by rfl) ⟨3218958, by rfl⟩ : syracuseStep 8583889 = 6437917) B6437917
theorem B1882843 : Blo 1881142 1882843 := bstep (se 1 (by rfl) ⟨1412132, by rfl⟩ : syracuseStep 1882843 = 2824265) B2824265
theorem B3218167 : Blo 1881142 3218167 := bstep (se 1 (by rfl) ⟨2413625, by rfl⟩ : syracuseStep 3218167 = 4827251) B4827251
theorem B4233977 : Blo 1881142 4233977 := bstep (se 2 (by rfl) ⟨1587741, by rfl⟩ : syracuseStep 4233977 = 3175483) B3175483
theorem B7633693 : Blo 1881142 7633693 := bstep (se 3 (by rfl) ⟨1431317, by rfl⟩ : syracuseStep 7633693 = 2862635) B2862635
theorem B1882919 : Blo 1881142 1882919 := bstep (se 1 (by rfl) ⟨1412189, by rfl⟩ : syracuseStep 1882919 = 2824379) B2824379
theorem B1882959 : Blo 1881142 1882959 := bstep (se 1 (by rfl) ⟨1412219, by rfl⟩ : syracuseStep 1882959 = 2824439) B2824439
theorem B1882975 : Blo 1881142 1882975 := bstep (se 1 (by rfl) ⟨1412231, by rfl⟩ : syracuseStep 1882975 = 2824463) B2824463
theorem B4897643 : Blo 1881142 4897643 := bstep (se 1 (by rfl) ⟨3673232, by rfl⟩ : syracuseStep 4897643 = 7346465) B7346465
theorem B1883003 : Blo 1881142 1883003 := bstep (se 1 (by rfl) ⟨1412252, by rfl⟩ : syracuseStep 1883003 = 2824505) B2824505
theorem B1883055 : Blo 1881142 1883055 := bstep (se 1 (by rfl) ⟨1412291, by rfl⟩ : syracuseStep 1883055 = 2824583) B2824583
theorem B4766647 : Blo 1881142 4766647 := bstep (se 1 (by rfl) ⟨3574985, by rfl⟩ : syracuseStep 4766647 = 7149971) B7149971
theorem B1883079 : Blo 1881142 1883079 := bstep (se 1 (by rfl) ⟨1412309, by rfl⟩ : syracuseStep 1883079 = 2824619) B2824619
theorem B1883099 : Blo 1881142 1883099 := bstep (se 1 (by rfl) ⟨1412324, by rfl⟩ : syracuseStep 1883099 = 2824649) B2824649
theorem B7633921 : Blo 1881142 7633921 := bstep (se 2 (by rfl) ⟨2862720, by rfl⟩ : syracuseStep 7633921 = 5725441) B5725441
theorem B4234247 : Blo 1881142 4234247 := bstep (se 1 (by rfl) ⟨3175685, by rfl⟩ : syracuseStep 4234247 = 6351371) B6351371
theorem B3177481 : Blo 1881142 3177481 := bstep (se 2 (by rfl) ⟨1191555, by rfl⟩ : syracuseStep 3177481 = 2383111) B2383111
theorem B9042995 : Blo 1881142 9042995 := bstep (se 1 (by rfl) ⟨6782246, by rfl⟩ : syracuseStep 9042995 = 13564493) B13564493
theorem B4521017 : Blo 1881142 4521017 := bstep (se 2 (by rfl) ⟨1695381, by rfl⟩ : syracuseStep 4521017 = 3390763) B3390763
theorem B4234319 : Blo 1881142 4234319 := bstep (se 1 (by rfl) ⟨3175739, by rfl⟩ : syracuseStep 4234319 = 6351479) B6351479
theorem B3177643 : Blo 1881142 3177643 := bstep (se 1 (by rfl) ⟨2383232, by rfl⟩ : syracuseStep 3177643 = 4766465) B4766465
theorem B7634263 : Blo 1881142 7634263 := bstep (se 1 (by rfl) ⟨5725697, by rfl⟩ : syracuseStep 7634263 = 11451395) B11451395
theorem B7241089 : Blo 1881142 7241089 := bstep (se 2 (by rfl) ⟨2715408, by rfl⟩ : syracuseStep 7241089 = 5430817) B5430817
theorem B10722725 : Blo 1881142 10722725 := bstep (se 4 (by rfl) ⟨1005255, by rfl⟩ : syracuseStep 10722725 = 2010511) B2010511
theorem B4234715 : Blo 1881142 4234715 := bstep (se 1 (by rfl) ⟨3176036, by rfl⟩ : syracuseStep 4234715 = 6352073) B6352073
theorem B5725793 : Blo 1881142 5725793 := bstep (se 2 (by rfl) ⟨2147172, by rfl⟩ : syracuseStep 5725793 = 4294345) B4294345
theorem B3014267 : Blo 1881142 3014267 := bstep (se 1 (by rfl) ⟨2260700, by rfl⟩ : syracuseStep 3014267 = 4521401) B4521401
theorem B11452049 : Blo 1881142 11452049 := bstep (se 2 (by rfl) ⟨4294518, by rfl⟩ : syracuseStep 11452049 = 8589037) B8589037
theorem B14294717 : Blo 1881142 14294717 := bstep (se 3 (by rfl) ⟨2680259, by rfl⟩ : syracuseStep 14294717 = 5360519) B5360519
theorem B3571447 : Blo 1881142 3571447 := bstep (se 1 (by rfl) ⟨2678585, by rfl⟩ : syracuseStep 3571447 = 5357171) B5357171
theorem B6029099 : Blo 1881142 6029099 := bstep (se 1 (by rfl) ⟨4521824, by rfl⟩ : syracuseStep 6029099 = 9043649) B9043649
theorem B3620713 : Blo 1881142 3620713 := bstep (se 2 (by rfl) ⟨1357767, by rfl⟩ : syracuseStep 3620713 = 2715535) B2715535
theorem B4349803 : Blo 1881142 4349803 := bstep (se 1 (by rfl) ⟨3262352, by rfl⟩ : syracuseStep 4349803 = 6524705) B6524705
theorem B4292459 : Blo 1881142 4292459 := bstep (se 1 (by rfl) ⟨3219344, by rfl⟩ : syracuseStep 4292459 = 6438689) B6438689
theorem B4235183 : Blo 1881142 4235183 := bstep (se 1 (by rfl) ⟨3176387, by rfl⟩ : syracuseStep 4235183 = 6352775) B6352775
theorem B4235273 : Blo 1881142 4235273 := bstep (se 2 (by rfl) ⟨1588227, by rfl⟩ : syracuseStep 4235273 = 3176455) B3176455
theorem B2261287 : Blo 1881142 2261287 := bstep (se 1 (by rfl) ⟨1695965, by rfl⟩ : syracuseStep 2261287 = 3391931) B3391931
theorem B4235687 : Blo 1881142 4235687 := bstep (se 1 (by rfl) ⟨3176765, by rfl⟩ : syracuseStep 4235687 = 6353531) B6353531
theorem B4235795 : Blo 1881142 4235795 := bstep (se 1 (by rfl) ⟨3176846, by rfl⟩ : syracuseStep 4235795 = 6353693) B6353693
theorem B27124253 : Blo 1881142 27124253 := bstep (se 3 (by rfl) ⟨5085797, by rfl⟩ : syracuseStep 27124253 = 10171595) B10171595
theorem B4235849 : Blo 1881142 4235849 := bstep (se 2 (by rfl) ⟨1588443, by rfl⟩ : syracuseStep 4235849 = 3176887) B3176887
theorem B7627385 : Blo 1881142 7627385 := bstep (se 2 (by rfl) ⟨2860269, by rfl⟩ : syracuseStep 7627385 = 5720539) B5720539
theorem B6783659 : Blo 1881142 6783659 := bstep (se 1 (by rfl) ⟨5087744, by rfl⟩ : syracuseStep 6783659 = 10175489) B10175489
theorem B6349535 : Blo 1881142 6349535 := bstep (se 1 (by rfl) ⟨4762151, by rfl⟩ : syracuseStep 6349535 = 9524303) B9524303
theorem B32170769 : Blo 1881142 32170769 := bstep (se 2 (by rfl) ⟨12064038, by rfl⟩ : syracuseStep 32170769 = 24128077) B24128077
theorem B11445185 : Blo 1881142 11445185 := bstep (se 2 (by rfl) ⟨4291944, by rfl⟩ : syracuseStep 11445185 = 8583889) B8583889
theorem B4236263 : Blo 1881142 4236263 := bstep (se 1 (by rfl) ⟨3177197, by rfl⟩ : syracuseStep 4236263 = 6354395) B6354395
theorem B6349967 : Blo 1881142 6349967 := bstep (se 1 (by rfl) ⟨4762475, by rfl⟩ : syracuseStep 6349967 = 9524951) B9524951
theorem B7144595 : Blo 1881142 7144595 := bstep (se 1 (by rfl) ⟨5358446, by rfl⟩ : syracuseStep 7144595 = 10716893) B10716893
theorem B4236641 : Blo 1881142 4236641 := bstep (se 2 (by rfl) ⟨1588740, by rfl⟩ : syracuseStep 4236641 = 3177481) B3177481
theorem B4236731 : Blo 1881142 4236731 := bstep (se 1 (by rfl) ⟨3177548, by rfl⟩ : syracuseStep 4236731 = 6355097) B6355097
theorem B9528839 : Blo 1881142 9528839 := bstep (se 1 (by rfl) ⟨7146629, by rfl⟩ : syracuseStep 9528839 = 14293259) B14293259
theorem B4236857 : Blo 1881142 4236857 := bstep (se 2 (by rfl) ⟨1588821, by rfl⟩ : syracuseStep 4236857 = 3177643) B3177643
theorem B8038045 : Blo 1881142 8038045 := bstep (se 3 (by rfl) ⟨1507133, by rfl⟩ : syracuseStep 8038045 = 3014267) B3014267
theorem B4523707 : Blo 1881142 4523707 := bstep (se 1 (by rfl) ⟨3392780, by rfl⟩ : syracuseStep 4523707 = 6785561) B6785561
theorem B18081569 : Blo 1881142 18081569 := bstep (se 2 (by rfl) ⟨6780588, by rfl⟩ : syracuseStep 18081569 = 13561177) B13561177
theorem B3573551 : Blo 1881142 3573551 := bstep (se 1 (by rfl) ⟨2680163, by rfl⟩ : syracuseStep 3573551 = 5360327) B5360327
theorem B5433193 : Blo 1881142 5433193 := bstep (se 2 (by rfl) ⟨2037447, by rfl⟩ : syracuseStep 5433193 = 4074895) B4074895
theorem B48236471 : Blo 1881142 48236471 := bstep (se 1 (by rfl) ⟨36177353, by rfl⟩ : syracuseStep 48236471 = 72354707) B72354707
theorem B9529325 : Blo 1881142 9529325 := bstep (se 3 (by rfl) ⟨1786748, by rfl⟩ : syracuseStep 9529325 = 3573497) B3573497
theorem B5359745 : Blo 1881142 5359745 := bstep (se 2 (by rfl) ⟨2009904, by rfl⟩ : syracuseStep 5359745 = 4019809) B4019809
theorem B6351101 : Blo 1881142 6351101 := bstep (se 3 (by rfl) ⟨1190831, by rfl⟩ : syracuseStep 6351101 = 2381663) B2381663
theorem B13060381 : Blo 1881142 13060381 := bstep (se 3 (by rfl) ⟨2448821, by rfl⟩ : syracuseStep 13060381 = 4897643) B4897643
theorem B4761929 : Blo 1881142 4761929 := bstep (se 2 (by rfl) ⟨1785723, by rfl⟩ : syracuseStep 4761929 = 3571447) B3571447
theorem B27134351 : Blo 1881142 27134351 := bstep (se 1 (by rfl) ⟨20350763, by rfl⟩ : syracuseStep 27134351 = 40701527) B40701527
theorem B9529811 : Blo 1881142 9529811 := bstep (se 1 (by rfl) ⟨7147358, by rfl⟩ : syracuseStep 9529811 = 14294717) B14294717
theorem B4827617 : Blo 1881142 4827617 := bstep (se 2 (by rfl) ⟨1810356, by rfl⟩ : syracuseStep 4827617 = 3620713) B3620713
theorem B6031867 : Blo 1881142 6031867 := bstep (se 1 (by rfl) ⟨4523900, by rfl⟩ : syracuseStep 6031867 = 9047801) B9047801
theorem B2861639 : Blo 1881142 2861639 := bstep (se 1 (by rfl) ⟨2146229, by rfl⟩ : syracuseStep 2861639 = 4292459) B4292459
theorem B5360201 : Blo 1881142 5360201 := bstep (se 2 (by rfl) ⟨2010075, by rfl⟩ : syracuseStep 5360201 = 4020151) B4020151
theorem B4524623 : Blo 1881142 4524623 := bstep (se 1 (by rfl) ⟨3393467, by rfl⟩ : syracuseStep 4524623 = 6786935) B6786935
theorem B9046723 : Blo 1881142 9046723 := bstep (se 1 (by rfl) ⟨6785042, by rfl⟩ : syracuseStep 9046723 = 13570085) B13570085
theorem B6875923 : Blo 1881142 6875923 := bstep (se 1 (by rfl) ⟨5156942, by rfl⟩ : syracuseStep 6875923 = 10313885) B10313885
theorem B16075543 : Blo 1881142 16075543 := bstep (se 1 (by rfl) ⟨12056657, by rfl⟩ : syracuseStep 16075543 = 24113315) B24113315
theorem B9530135 : Blo 1881142 9530135 := bstep (se 1 (by rfl) ⟨7147601, by rfl⟩ : syracuseStep 9530135 = 14295203) B14295203
theorem B2116399 : Blo 1881142 2116399 := bstep (se 1 (by rfl) ⟨1587299, by rfl⟩ : syracuseStep 2116399 = 3174599) B3174599
theorem B21441347 : Blo 1881142 21441347 := bstep (se 1 (by rfl) ⟨16081010, by rfl⟩ : syracuseStep 21441347 = 32162021) B32162021
theorem B195603275 : Blo 1881142 195603275 := bstep (se 1 (by rfl) ⟨146702456, by rfl⟩ : syracuseStep 195603275 = 293404913) B293404913
theorem B2116507 : Blo 1881142 2116507 := bstep (se 1 (by rfl) ⟨1587380, by rfl⟩ : syracuseStep 2116507 = 3174761) B3174761
theorem B6351911 : Blo 1881142 6351911 := bstep (se 1 (by rfl) ⟨4763933, by rfl⟩ : syracuseStep 6351911 = 9527867) B9527867
theorem B40709213 : Blo 1881142 40709213 := bstep (se 3 (by rfl) ⟨7632977, by rfl⟩ : syracuseStep 40709213 = 15265955) B15265955
theorem B10456253 : Blo 1881142 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B19320079 : Blo 1881142 19320079 := bstep (se 1 (by rfl) ⟨14490059, by rfl⟩ : syracuseStep 19320079 = 28980119) B28980119
theorem B2116903 : Blo 1881142 2116903 := bstep (se 1 (by rfl) ⟨1587677, by rfl⟩ : syracuseStep 2116903 = 3175355) B3175355
theorem B4828511 : Blo 1881142 4828511 := bstep (se 1 (by rfl) ⟨3621383, by rfl⟩ : syracuseStep 4828511 = 7242767) B7242767
theorem B2116975 : Blo 1881142 2116975 := bstep (se 1 (by rfl) ⟨1587731, by rfl⟩ : syracuseStep 2116975 = 3175463) B3175463
theorem B6352343 : Blo 1881142 6352343 := bstep (se 1 (by rfl) ⟨4764257, by rfl⟩ : syracuseStep 6352343 = 9528515) B9528515
theorem B2117191 : Blo 1881142 2117191 := bstep (se 1 (by rfl) ⟨1587893, by rfl⟩ : syracuseStep 2117191 = 3175787) B3175787
theorem B2821727 : Blo 1881142 2821727 := bstep (se 1 (by rfl) ⟨2116295, by rfl⟩ : syracuseStep 2821727 = 4232591) B4232591
theorem B10178257 : Blo 1881142 10178257 := bstep (se 2 (by rfl) ⟨3816846, by rfl⟩ : syracuseStep 10178257 = 7633693) B7633693
theorem B2821943 : Blo 1881142 2821943 := bstep (se 1 (by rfl) ⟨2116457, by rfl⟩ : syracuseStep 2821943 = 4232915) B4232915
theorem B8580971 : Blo 1881142 8580971 := bstep (se 1 (by rfl) ⟨6435728, by rfl⟩ : syracuseStep 8580971 = 12871457) B12871457
theorem B132222937 : Blo 1881142 132222937 := bstep (se 2 (by rfl) ⟨49583601, by rfl⟩ : syracuseStep 132222937 = 99167203) B99167203
theorem B10178561 : Blo 1881142 10178561 := bstep (se 2 (by rfl) ⟨3816960, by rfl⟩ : syracuseStep 10178561 = 7633921) B7633921
theorem B2822249 : Blo 1881142 2822249 := bstep (se 2 (by rfl) ⟨1058343, by rfl⟩ : syracuseStep 2822249 = 2116687) B2116687
theorem B16085249 : Blo 1881142 16085249 := bstep (se 2 (by rfl) ⟨6031968, by rfl⟩ : syracuseStep 16085249 = 12063937) B12063937
theorem B9531755 : Blo 1881142 9531755 := bstep (se 1 (by rfl) ⟨7148816, by rfl⟩ : syracuseStep 9531755 = 14297633) B14297633
theorem B14291315 : Blo 1881142 14291315 := bstep (se 1 (by rfl) ⟨10718486, by rfl⟩ : syracuseStep 14291315 = 21436973) B21436973
theorem B2822567 : Blo 1881142 2822567 := bstep (se 1 (by rfl) ⟨2116925, by rfl⟩ : syracuseStep 2822567 = 4233851) B4233851
theorem B2118055 : Blo 1881142 2118055 := bstep (se 1 (by rfl) ⟨1588541, by rfl⟩ : syracuseStep 2118055 = 3177083) B3177083
theorem B7631279 : Blo 1881142 7631279 := bstep (se 1 (by rfl) ⟨5723459, by rfl⟩ : syracuseStep 7631279 = 11446919) B11446919
theorem B10179017 : Blo 1881142 10179017 := bstep (se 2 (by rfl) ⟨3817131, by rfl⟩ : syracuseStep 10179017 = 7634263) B7634263
theorem B2822651 : Blo 1881142 2822651 := bstep (se 1 (by rfl) ⟨2116988, by rfl⟩ : syracuseStep 2822651 = 4233977) B4233977
theorem B9654785 : Blo 1881142 9654785 := bstep (se 2 (by rfl) ⟨3620544, by rfl⟩ : syracuseStep 9654785 = 7241089) B7241089
theorem B3813961 : Blo 1881142 3813961 := bstep (se 2 (by rfl) ⟨1430235, by rfl⟩ : syracuseStep 3813961 = 2860471) B2860471
theorem B86954573 : Blo 1881142 86954573 := bstep (se 3 (by rfl) ⟨16303982, by rfl⟩ : syracuseStep 86954573 = 32607965) B32607965
theorem B2822777 : Blo 1881142 2822777 := bstep (se 2 (by rfl) ⟨1058541, by rfl⟩ : syracuseStep 2822777 = 2117083) B2117083
theorem B2822831 : Blo 1881142 2822831 := bstep (se 1 (by rfl) ⟨2117123, by rfl⟩ : syracuseStep 2822831 = 4234247) B4234247
theorem B2822879 : Blo 1881142 2822879 := bstep (se 1 (by rfl) ⟨2117159, by rfl⟩ : syracuseStep 2822879 = 4234319) B4234319
theorem B3175247 : Blo 1881142 3175247 := bstep (se 1 (by rfl) ⟨2381435, by rfl⟩ : syracuseStep 3175247 = 4762871) B4762871
theorem B7148483 : Blo 1881142 7148483 := bstep (se 1 (by rfl) ⟨5361362, by rfl⟩ : syracuseStep 7148483 = 10722725) B10722725
theorem B2823143 : Blo 1881142 2823143 := bstep (se 1 (by rfl) ⟨2117357, by rfl⟩ : syracuseStep 2823143 = 4234715) B4234715
theorem B8041463 : Blo 1881142 8041463 := bstep (se 1 (by rfl) ⟨6031097, by rfl⟩ : syracuseStep 8041463 = 12062195) B12062195
theorem B22033399 : Blo 1881142 22033399 := bstep (se 1 (by rfl) ⟨16525049, by rfl⟩ : syracuseStep 22033399 = 33050099) B33050099
theorem B6354017 : Blo 1881142 6354017 := bstep (se 2 (by rfl) ⟨2382756, by rfl⟩ : syracuseStep 6354017 = 4765513) B4765513
theorem B3814543 : Blo 1881142 3814543 := bstep (se 1 (by rfl) ⟨2860907, by rfl⟩ : syracuseStep 3814543 = 5721815) B5721815
theorem B4764815 : Blo 1881142 4764815 := bstep (se 1 (by rfl) ⟨3573611, by rfl⟩ : syracuseStep 4764815 = 7147223) B7147223
theorem B4019399 : Blo 1881142 4019399 := bstep (se 1 (by rfl) ⟨3014549, by rfl⟩ : syracuseStep 4019399 = 6029099) B6029099
theorem B2823401 : Blo 1881142 2823401 := bstep (se 2 (by rfl) ⟨1058775, by rfl⟩ : syracuseStep 2823401 = 2117551) B2117551
theorem B1881375 : Blo 1881142 1881375 := bstep (se 1 (by rfl) ⟨1411031, by rfl⟩ : syracuseStep 1881375 = 2822063) B2822063
theorem B2823455 : Blo 1881142 2823455 := bstep (se 1 (by rfl) ⟨2117591, by rfl⟩ : syracuseStep 2823455 = 4235183) B4235183
theorem B1881435 : Blo 1881142 1881435 := bstep (se 1 (by rfl) ⟨1411076, by rfl⟩ : syracuseStep 1881435 = 2822153) B2822153
theorem B2381167 : Blo 1881142 2381167 := bstep (se 1 (by rfl) ⟨1785875, by rfl⟩ : syracuseStep 2381167 = 3571751) B3571751
theorem B1881455 : Blo 1881142 1881455 := bstep (se 1 (by rfl) ⟨1411091, by rfl⟩ : syracuseStep 1881455 = 2822183) B2822183
theorem B4232609 : Blo 1881142 4232609 := bstep (se 2 (by rfl) ⟨1587228, by rfl⟩ : syracuseStep 4232609 = 3174457) B3174457
theorem B1881511 : Blo 1881142 1881511 := bstep (se 1 (by rfl) ⟨1411133, by rfl⟩ : syracuseStep 1881511 = 2822267) B2822267
theorem B2823623 : Blo 1881142 2823623 := bstep (se 1 (by rfl) ⟨2117717, by rfl⟩ : syracuseStep 2823623 = 4235435) B4235435
theorem B1881595 : Blo 1881142 1881595 := bstep (se 1 (by rfl) ⟨1411196, by rfl⟩ : syracuseStep 1881595 = 2822393) B2822393
theorem B1881663 : Blo 1881142 1881663 := bstep (se 1 (by rfl) ⟨1411247, by rfl⟩ : syracuseStep 1881663 = 2822495) B2822495
theorem B1881671 : Blo 1881142 1881671 := bstep (se 1 (by rfl) ⟨1411253, by rfl⟩ : syracuseStep 1881671 = 2822507) B2822507
theorem B173930165 : Blo 1881142 173930165 := bstep (se 5 (by rfl) ⟨8152976, by rfl⟩ : syracuseStep 173930165 = 16305953) B16305953
theorem B1881823 : Blo 1881142 1881823 := bstep (se 1 (by rfl) ⟨1411367, by rfl⟩ : syracuseStep 1881823 = 2822735) B2822735
theorem B9533213 : Blo 1881142 9533213 := bstep (se 3 (by rfl) ⟨1787477, by rfl⟩ : syracuseStep 9533213 = 3574955) B3574955
theorem B2823977 : Blo 1881142 2823977 := bstep (se 2 (by rfl) ⟨1058991, by rfl⟩ : syracuseStep 2823977 = 2117983) B2117983
theorem B1881903 : Blo 1881142 1881903 := bstep (se 1 (by rfl) ⟨1411427, by rfl⟩ : syracuseStep 1881903 = 2822855) B2822855
theorem B3176239 : Blo 1881142 3176239 := bstep (se 1 (by rfl) ⟨2382179, by rfl⟩ : syracuseStep 3176239 = 4764359) B4764359
theorem B2823983 : Blo 1881142 2823983 := bstep (se 1 (by rfl) ⟨2117987, by rfl⟩ : syracuseStep 2823983 = 4235975) B4235975
theorem B1882011 : Blo 1881142 1882011 := bstep (se 1 (by rfl) ⟨1411508, by rfl⟩ : syracuseStep 1882011 = 2823017) B2823017
theorem B4233167 : Blo 1881142 4233167 := bstep (se 1 (by rfl) ⟨3174875, by rfl⟩ : syracuseStep 4233167 = 6349751) B6349751
theorem B1882063 : Blo 1881142 1882063 := bstep (se 1 (by rfl) ⟨1411547, by rfl⟩ : syracuseStep 1882063 = 2823095) B2823095
theorem B1882087 : Blo 1881142 1882087 := bstep (se 1 (by rfl) ⟨1411565, by rfl⟩ : syracuseStep 1882087 = 2823131) B2823131
theorem B5085193 : Blo 1881142 5085193 := bstep (se 2 (by rfl) ⟨1906947, by rfl⟩ : syracuseStep 5085193 = 3813895) B3813895
theorem B8697935 : Blo 1881142 8697935 := bstep (se 1 (by rfl) ⟨6523451, by rfl⟩ : syracuseStep 8697935 = 13046903) B13046903
theorem B2382043 : Blo 1881142 2382043 := bstep (se 1 (by rfl) ⟨1786532, by rfl⟩ : syracuseStep 2382043 = 3573065) B3573065
theorem B2824457 : Blo 1881142 2824457 := bstep (se 2 (by rfl) ⟨1059171, by rfl⟩ : syracuseStep 2824457 = 2118343) B2118343
theorem B1882399 : Blo 1881142 1882399 := bstep (se 1 (by rfl) ⟨1411799, by rfl⟩ : syracuseStep 1882399 = 2823599) B2823599
theorem B4290889 : Blo 1881142 4290889 := bstep (se 2 (by rfl) ⟨1609083, by rfl⟩ : syracuseStep 4290889 = 3218167) B3218167
theorem B4233545 : Blo 1881142 4233545 := bstep (se 2 (by rfl) ⟨1587579, by rfl⟩ : syracuseStep 4233545 = 3175159) B3175159
theorem B4233563 : Blo 1881142 4233563 := bstep (se 1 (by rfl) ⟨3175172, by rfl⟩ : syracuseStep 4233563 = 6350345) B6350345
theorem B1882459 : Blo 1881142 1882459 := bstep (se 1 (by rfl) ⟨1411844, by rfl⟩ : syracuseStep 1882459 = 2823689) B2823689
theorem B4020587 : Blo 1881142 4020587 := bstep (se 1 (by rfl) ⟨3015440, by rfl⟩ : syracuseStep 4020587 = 6030881) B6030881
theorem B6781295 : Blo 1881142 6781295 := bstep (se 1 (by rfl) ⟨5085971, by rfl⟩ : syracuseStep 6781295 = 10171943) B10171943
theorem B1882479 : Blo 1881142 1882479 := bstep (se 1 (by rfl) ⟨1411859, by rfl⟩ : syracuseStep 1882479 = 2823719) B2823719
theorem B2824559 : Blo 1881142 2824559 := bstep (se 1 (by rfl) ⟨2118419, by rfl⟩ : syracuseStep 2824559 = 4236839) B4236839
theorem B1882535 : Blo 1881142 1882535 := bstep (se 1 (by rfl) ⟨1411901, by rfl⟩ : syracuseStep 1882535 = 2823803) B2823803
theorem B6355367 : Blo 1881142 6355367 := bstep (se 1 (by rfl) ⟨4766525, by rfl⟩ : syracuseStep 6355367 = 9533051) B9533051
theorem B1882619 : Blo 1881142 1882619 := bstep (se 1 (by rfl) ⟨1411964, by rfl⟩ : syracuseStep 1882619 = 2823929) B2823929
theorem B1882687 : Blo 1881142 1882687 := bstep (se 1 (by rfl) ⟨1412015, by rfl⟩ : syracuseStep 1882687 = 2824031) B2824031
theorem B1882695 : Blo 1881142 1882695 := bstep (se 1 (by rfl) ⟨1412021, by rfl⟩ : syracuseStep 1882695 = 2824043) B2824043
theorem B6355529 : Blo 1881142 6355529 := bstep (se 2 (by rfl) ⟨2383323, by rfl⟩ : syracuseStep 6355529 = 4766647) B4766647
theorem B1882847 : Blo 1881142 1882847 := bstep (se 1 (by rfl) ⟨1412135, by rfl⟩ : syracuseStep 1882847 = 2824271) B2824271
theorem B16071443 : Blo 1881142 16071443 := bstep (se 1 (by rfl) ⟨12053582, by rfl⟩ : syracuseStep 16071443 = 24107165) B24107165
theorem B1882927 : Blo 1881142 1882927 := bstep (se 1 (by rfl) ⟨1412195, by rfl⟩ : syracuseStep 1882927 = 2824391) B2824391
theorem B17177417 : Blo 1881142 17177417 := bstep (se 2 (by rfl) ⟨6441531, by rfl⟩ : syracuseStep 17177417 = 12883063) B12883063
theorem B4291471 : Blo 1881142 4291471 := bstep (se 1 (by rfl) ⟨3218603, by rfl⟩ : syracuseStep 4291471 = 6437207) B6437207
theorem B4234139 : Blo 1881142 4234139 := bstep (se 1 (by rfl) ⟨3175604, by rfl⟩ : syracuseStep 4234139 = 6351209) B6351209
theorem B1883035 : Blo 1881142 1883035 := bstep (se 1 (by rfl) ⟨1412276, by rfl⟩ : syracuseStep 1883035 = 2824553) B2824553
theorem B1883087 : Blo 1881142 1883087 := bstep (se 1 (by rfl) ⟨1412315, by rfl⟩ : syracuseStep 1883087 = 2824631) B2824631
theorem B1883111 : Blo 1881142 1883111 := bstep (se 1 (by rfl) ⟨1412333, by rfl⟩ : syracuseStep 1883111 = 2824667) B2824667
theorem B4234337 : Blo 1881142 4234337 := bstep (se 2 (by rfl) ⟨1587876, by rfl⟩ : syracuseStep 4234337 = 3175753) B3175753
theorem B8035517 : Blo 1881142 8035517 := bstep (se 3 (by rfl) ⟨1506659, by rfl⟩ : syracuseStep 8035517 = 3013319) B3013319
theorem B4234535 : Blo 1881142 4234535 := bstep (se 1 (by rfl) ⟨3175901, by rfl⟩ : syracuseStep 4234535 = 6351803) B6351803
theorem B4349281 : Blo 1881142 4349281 := bstep (se 2 (by rfl) ⟨1630980, by rfl⟩ : syracuseStep 4349281 = 3261961) B3261961
theorem B6028663 : Blo 1881142 6028663 := bstep (se 1 (by rfl) ⟨4521497, by rfl⟩ : syracuseStep 6028663 = 9042995) B9042995
theorem B3014011 : Blo 1881142 3014011 := bstep (se 1 (by rfl) ⟨2260508, by rfl⟩ : syracuseStep 3014011 = 4521017) B4521017
theorem B10174061 : Blo 1881142 10174061 := bstep (se 3 (by rfl) ⟨1907636, by rfl⟩ : syracuseStep 10174061 = 3815273) B3815273
theorem B7839347 : Blo 1881142 7839347 := bstep (se 1 (by rfl) ⟨5879510, by rfl⟩ : syracuseStep 7839347 = 11759021) B11759021
theorem B4234913 : Blo 1881142 4234913 := bstep (se 2 (by rfl) ⟨1588092, by rfl⟩ : syracuseStep 4234913 = 3176185) B3176185
theorem B18095831 : Blo 1881142 18095831 := bstep (se 1 (by rfl) ⟨13571873, by rfl⟩ : syracuseStep 18095831 = 27143747) B27143747
theorem B3817195 : Blo 1881142 3817195 := bstep (se 1 (by rfl) ⟨2862896, by rfl⟩ : syracuseStep 3817195 = 5725793) B5725793
theorem B7634699 : Blo 1881142 7634699 := bstep (se 1 (by rfl) ⟨5726024, by rfl⟩ : syracuseStep 7634699 = 11452049) B11452049
theorem B5357353 : Blo 1881142 5357353 := bstep (se 2 (by rfl) ⟨2009007, by rfl⟩ : syracuseStep 5357353 = 4018015) B4018015
theorem B3219247 : Blo 1881142 3219247 := bstep (se 1 (by rfl) ⟨2414435, by rfl⟩ : syracuseStep 3219247 = 4828871) B4828871
theorem B5799737 : Blo 1881142 5799737 := bstep (se 2 (by rfl) ⟨2174901, by rfl⟩ : syracuseStep 5799737 = 4349803) B4349803
theorem B10723499 : Blo 1881142 10723499 := bstep (se 1 (by rfl) ⟨8042624, by rfl⟩ : syracuseStep 10723499 = 16085249) B16085249
theorem B9527543 : Blo 1881142 9527543 := bstep (se 1 (by rfl) ⟨7145657, by rfl⟩ : syracuseStep 9527543 = 14291315) B14291315
theorem B5087519 : Blo 1881142 5087519 := bstep (se 1 (by rfl) ⟨3815639, by rfl⟩ : syracuseStep 5087519 = 7631279) B7631279
theorem B4522439 : Blo 1881142 4522439 := bstep (se 1 (by rfl) ⟨3391829, by rfl⟩ : syracuseStep 4522439 = 6783659) B6783659
theorem B21447179 : Blo 1881142 21447179 := bstep (se 1 (by rfl) ⟨16085384, by rfl⟩ : syracuseStep 21447179 = 32170769) B32170769
theorem B4236011 : Blo 1881142 4236011 := bstep (se 1 (by rfl) ⟨3177008, by rfl⟩ : syracuseStep 4236011 = 6354017) B6354017
theorem B2679599 : Blo 1881142 2679599 := bstep (se 1 (by rfl) ⟨2009699, by rfl⟩ : syracuseStep 2679599 = 4019399) B4019399
theorem B24126437 : Blo 1881142 24126437 := bstep (se 4 (by rfl) ⟨2261853, by rfl⟩ : syracuseStep 24126437 = 4523707) B4523707
theorem B9167897 : Blo 1881142 9167897 := bstep (se 2 (by rfl) ⟨3437961, by rfl⟩ : syracuseStep 9167897 = 6875923) B6875923
theorem B20358373 : Blo 1881142 20358373 := bstep (se 4 (by rfl) ⟨1908597, by rfl⟩ : syracuseStep 20358373 = 3817195) B3817195
theorem B29377865 : Blo 1881142 29377865 := bstep (se 2 (by rfl) ⟨11016699, by rfl⟩ : syracuseStep 29377865 = 22033399) B22033399
theorem B3573163 : Blo 1881142 3573163 := bstep (se 1 (by rfl) ⟨2679872, by rfl⟩ : syracuseStep 3573163 = 5359745) B5359745
theorem B12060197 : Blo 1881142 12060197 := bstep (se 4 (by rfl) ⟨1130643, by rfl⟩ : syracuseStep 12060197 = 2261287) B2261287
theorem B2680391 : Blo 1881142 2680391 := bstep (se 1 (by rfl) ⟨2010293, by rfl⟩ : syracuseStep 2680391 = 4020587) B4020587
theorem B18089567 : Blo 1881142 18089567 := bstep (se 1 (by rfl) ⟨13567175, by rfl⟩ : syracuseStep 18089567 = 27134351) B27134351
theorem B4236911 : Blo 1881142 4236911 := bstep (se 1 (by rfl) ⟨3177683, by rfl⟩ : syracuseStep 4236911 = 6355367) B6355367
theorem B3573467 : Blo 1881142 3573467 := bstep (se 1 (by rfl) ⟨2680100, by rfl⟩ : syracuseStep 3573467 = 5360201) B5360201
theorem B4237019 : Blo 1881142 4237019 := bstep (se 1 (by rfl) ⟨3177764, by rfl⟩ : syracuseStep 4237019 = 6355529) B6355529
theorem B3016415 : Blo 1881142 3016415 := bstep (se 1 (by rfl) ⟨2262311, by rfl⟩ : syracuseStep 3016415 = 4524623) B4524623
theorem B8038217 : Blo 1881142 8038217 := bstep (se 2 (by rfl) ⟨3014331, by rfl⟩ : syracuseStep 8038217 = 6028663) B6028663
theorem B28977029 : Blo 1881142 28977029 := bstep (se 4 (by rfl) ⟨2716596, by rfl⟩ : syracuseStep 28977029 = 5433193) B5433193
theorem B130402183 : Blo 1881142 130402183 := bstep (se 1 (by rfl) ⟨97801637, by rfl⟩ : syracuseStep 130402183 = 195603275) B195603275
theorem B10717393 : Blo 1881142 10717393 := bstep (se 2 (by rfl) ⟨4019022, by rfl⟩ : syracuseStep 10717393 = 8038045) B8038045
theorem B5089799 : Blo 1881142 5089799 := bstep (se 1 (by rfl) ⟨3817349, by rfl⟩ : syracuseStep 5089799 = 7634699) B7634699
theorem B5720647 : Blo 1881142 5720647 := bstep (se 1 (by rfl) ⟨4290485, by rfl⟩ : syracuseStep 5720647 = 8580971) B8580971
theorem B6785707 : Blo 1881142 6785707 := bstep (se 1 (by rfl) ⟨5089280, by rfl⟩ : syracuseStep 6785707 = 10178561) B10178561
theorem B6786011 : Blo 1881142 6786011 := bstep (se 1 (by rfl) ⟨5089508, by rfl⟩ : syracuseStep 6786011 = 10179017) B10179017
theorem B18082835 : Blo 1881142 18082835 := bstep (se 1 (by rfl) ⟨13562126, by rfl⟩ : syracuseStep 18082835 = 27124253) B27124253
theorem B5721185 : Blo 1881142 5721185 := bstep (se 2 (by rfl) ⟨2145444, by rfl⟩ : syracuseStep 5721185 = 4290889) B4290889
theorem B2116831 : Blo 1881142 2116831 := bstep (se 1 (by rfl) ⟨1587623, by rfl⟩ : syracuseStep 2116831 = 3175247) B3175247
theorem B7630123 : Blo 1881142 7630123 := bstep (se 1 (by rfl) ⟨5722592, by rfl⟩ : syracuseStep 7630123 = 11445185) B11445185
theorem B5360975 : Blo 1881142 5360975 := bstep (se 1 (by rfl) ⟨4020731, by rfl⟩ : syracuseStep 5360975 = 8041463) B8041463
theorem B4763063 : Blo 1881142 4763063 := bstep (se 1 (by rfl) ⟨3572297, by rfl⟩ : syracuseStep 4763063 = 7144595) B7144595
theorem B12062297 : Blo 1881142 12062297 := bstep (se 2 (by rfl) ⟨4523361, by rfl⟩ : syracuseStep 12062297 = 9046723) B9046723
theorem B2821739 : Blo 1881142 2821739 := bstep (se 1 (by rfl) ⟨2116304, by rfl⟩ : syracuseStep 2821739 = 4232609) B4232609
theorem B6352559 : Blo 1881142 6352559 := bstep (se 1 (by rfl) ⟨4764419, by rfl⟩ : syracuseStep 6352559 = 9528839) B9528839
theorem B21434057 : Blo 1881142 21434057 := bstep (se 2 (by rfl) ⟨8037771, by rfl⟩ : syracuseStep 21434057 = 16075543) B16075543
theorem B2821865 : Blo 1881142 2821865 := bstep (se 2 (by rfl) ⟨1058199, by rfl⟩ : syracuseStep 2821865 = 2116399) B2116399
theorem B115953443 : Blo 1881142 115953443 := bstep (se 1 (by rfl) ⟨86965082, by rfl⟩ : syracuseStep 115953443 = 173930165) B173930165
theorem B12054379 : Blo 1881142 12054379 := bstep (se 1 (by rfl) ⟨9040784, by rfl⟩ : syracuseStep 12054379 = 18081569) B18081569
theorem B2822009 : Blo 1881142 2822009 := bstep (se 2 (by rfl) ⟨1058253, by rfl⟩ : syracuseStep 2822009 = 2116507) B2116507
theorem B32157647 : Blo 1881142 32157647 := bstep (se 1 (by rfl) ⟨24118235, by rfl⟩ : syracuseStep 32157647 = 48236471) B48236471
theorem B2822111 : Blo 1881142 2822111 := bstep (se 1 (by rfl) ⟨2116583, by rfl⟩ : syracuseStep 2822111 = 4233167) B4233167
theorem B6352883 : Blo 1881142 6352883 := bstep (se 1 (by rfl) ⟨4764662, by rfl⟩ : syracuseStep 6352883 = 9529325) B9529325
theorem B231878861 : Blo 1881142 231878861 := bstep (se 3 (by rfl) ⟨43477286, by rfl⟩ : syracuseStep 231878861 = 86954573) B86954573
theorem B3174619 : Blo 1881142 3174619 := bstep (se 1 (by rfl) ⟨2380964, by rfl⟩ : syracuseStep 3174619 = 4761929) B4761929
theorem B2822363 : Blo 1881142 2822363 := bstep (se 1 (by rfl) ⟨2116772, by rfl⟩ : syracuseStep 2822363 = 4233545) B4233545
theorem B2822375 : Blo 1881142 2822375 := bstep (se 1 (by rfl) ⟨2116781, by rfl⟩ : syracuseStep 2822375 = 4233563) B4233563
theorem B6353207 : Blo 1881142 6353207 := bstep (se 1 (by rfl) ⟨4764905, by rfl⟩ : syracuseStep 6353207 = 9529811) B9529811
theorem B25760105 : Blo 1881142 25760105 := bstep (se 2 (by rfl) ⟨9660039, by rfl⟩ : syracuseStep 25760105 = 19320079) B19320079
theorem B2822537 : Blo 1881142 2822537 := bstep (se 2 (by rfl) ⟨1058451, by rfl⟩ : syracuseStep 2822537 = 2116903) B2116903
theorem B3174889 : Blo 1881142 3174889 := bstep (se 2 (by rfl) ⟨1190583, by rfl⟩ : syracuseStep 3174889 = 2381167) B2381167
theorem B2822633 : Blo 1881142 2822633 := bstep (se 2 (by rfl) ⟨1058487, by rfl⟩ : syracuseStep 2822633 = 2116975) B2116975
theorem B4018681 : Blo 1881142 4018681 := bstep (se 2 (by rfl) ⟨1507005, by rfl⟩ : syracuseStep 4018681 = 3014011) B3014011
theorem B6353423 : Blo 1881142 6353423 := bstep (se 1 (by rfl) ⟨4765067, by rfl⟩ : syracuseStep 6353423 = 9530135) B9530135
theorem B2822759 : Blo 1881142 2822759 := bstep (se 1 (by rfl) ⟨2117069, by rfl⟩ : syracuseStep 2822759 = 4234139) B4234139
theorem B2822891 : Blo 1881142 2822891 := bstep (se 1 (by rfl) ⟨2117168, by rfl⟩ : syracuseStep 2822891 = 4234337) B4234337
theorem B2822921 : Blo 1881142 2822921 := bstep (se 2 (by rfl) ⟨1058595, by rfl⟩ : syracuseStep 2822921 = 2117191) B2117191
theorem B2823023 : Blo 1881142 2823023 := bstep (se 1 (by rfl) ⟨2117267, by rfl⟩ : syracuseStep 2823023 = 4234535) B4234535
theorem B13571009 : Blo 1881142 13571009 := bstep (se 2 (by rfl) ⟨5089128, by rfl⟩ : syracuseStep 13571009 = 10178257) B10178257
theorem B1881151 : Blo 1881142 1881151 := bstep (se 1 (by rfl) ⟨1410863, by rfl⟩ : syracuseStep 1881151 = 2821727) B2821727
theorem B2823275 : Blo 1881142 2823275 := bstep (se 1 (by rfl) ⟨2117456, by rfl⟩ : syracuseStep 2823275 = 4234913) B4234913
theorem B12063887 : Blo 1881142 12063887 := bstep (se 1 (by rfl) ⟨9047915, by rfl⟩ : syracuseStep 12063887 = 18095831) B18095831
theorem B1881295 : Blo 1881142 1881295 := bstep (se 1 (by rfl) ⟨1410971, by rfl⟩ : syracuseStep 1881295 = 2821943) B2821943
theorem B176297249 : Blo 1881142 176297249 := bstep (se 2 (by rfl) ⟨66111468, by rfl⟩ : syracuseStep 176297249 = 132222937) B132222937
theorem B2823515 : Blo 1881142 2823515 := bstep (se 1 (by rfl) ⟨2117636, by rfl⟩ : syracuseStep 2823515 = 4235273) B4235273
theorem B6780257 : Blo 1881142 6780257 := bstep (se 2 (by rfl) ⟨2542596, by rfl⟩ : syracuseStep 6780257 = 5085193) B5085193
theorem B1881499 : Blo 1881142 1881499 := bstep (se 1 (by rfl) ⟨1411124, by rfl⟩ : syracuseStep 1881499 = 2822249) B2822249
theorem B6354503 : Blo 1881142 6354503 := bstep (se 1 (by rfl) ⟨4765877, by rfl⟩ : syracuseStep 6354503 = 9531755) B9531755
theorem B1881711 : Blo 1881142 1881711 := bstep (se 1 (by rfl) ⟨1411283, by rfl⟩ : syracuseStep 1881711 = 2822567) B2822567
theorem B2823791 : Blo 1881142 2823791 := bstep (se 1 (by rfl) ⟨2117843, by rfl⟩ : syracuseStep 2823791 = 4235687) B4235687
theorem B3176057 : Blo 1881142 3176057 := bstep (se 2 (by rfl) ⟨1191021, by rfl⟩ : syracuseStep 3176057 = 2382043) B2382043
theorem B1881767 : Blo 1881142 1881767 := bstep (se 1 (by rfl) ⟨1411325, by rfl⟩ : syracuseStep 1881767 = 2822651) B2822651
theorem B6436523 : Blo 1881142 6436523 := bstep (se 1 (by rfl) ⟨4827392, by rfl⟩ : syracuseStep 6436523 = 9654785) B9654785
theorem B2823863 : Blo 1881142 2823863 := bstep (se 1 (by rfl) ⟨2117897, by rfl⟩ : syracuseStep 2823863 = 4235795) B4235795
theorem B17413841 : Blo 1881142 17413841 := bstep (se 2 (by rfl) ⟨6530190, by rfl⟩ : syracuseStep 17413841 = 13060381) B13060381
theorem B2823899 : Blo 1881142 2823899 := bstep (se 1 (by rfl) ⟨2117924, by rfl⟩ : syracuseStep 2823899 = 4235849) B4235849
theorem B1881851 : Blo 1881142 1881851 := bstep (se 1 (by rfl) ⟨1411388, by rfl⟩ : syracuseStep 1881851 = 2822777) B2822777
theorem B1881887 : Blo 1881142 1881887 := bstep (se 1 (by rfl) ⟨1411415, by rfl⟩ : syracuseStep 1881887 = 2822831) B2822831
theorem B4233023 : Blo 1881142 4233023 := bstep (se 1 (by rfl) ⟨3174767, by rfl⟩ : syracuseStep 4233023 = 6349535) B6349535
theorem B1881919 : Blo 1881142 1881919 := bstep (se 1 (by rfl) ⟨1411439, by rfl⟩ : syracuseStep 1881919 = 2822879) B2822879
theorem B2824073 : Blo 1881142 2824073 := bstep (se 2 (by rfl) ⟨1059027, by rfl⟩ : syracuseStep 2824073 = 2118055) B2118055
theorem B4765655 : Blo 1881142 4765655 := bstep (se 1 (by rfl) ⟨3574241, by rfl⟩ : syracuseStep 4765655 = 7148483) B7148483
theorem B1882095 : Blo 1881142 1882095 := bstep (se 1 (by rfl) ⟨1411571, by rfl⟩ : syracuseStep 1882095 = 2823143) B2823143
theorem B2824175 : Blo 1881142 2824175 := bstep (se 1 (by rfl) ⟨2118131, by rfl⟩ : syracuseStep 2824175 = 4236263) B4236263
theorem B8042489 : Blo 1881142 8042489 := bstep (se 2 (by rfl) ⟨3015933, by rfl⟩ : syracuseStep 8042489 = 6031867) B6031867
theorem B4233311 : Blo 1881142 4233311 := bstep (se 1 (by rfl) ⟨3174983, by rfl⟩ : syracuseStep 4233311 = 6349967) B6349967
theorem B5085281 : Blo 1881142 5085281 := bstep (se 2 (by rfl) ⟨1906980, by rfl⟩ : syracuseStep 5085281 = 3813961) B3813961
theorem B3176543 : Blo 1881142 3176543 := bstep (se 1 (by rfl) ⟨2382407, by rfl⟩ : syracuseStep 3176543 = 4764815) B4764815
theorem B1882267 : Blo 1881142 1882267 := bstep (se 1 (by rfl) ⟨1411700, by rfl⟩ : syracuseStep 1882267 = 2823401) B2823401
theorem B1882303 : Blo 1881142 1882303 := bstep (se 1 (by rfl) ⟨1411727, by rfl⟩ : syracuseStep 1882303 = 2823455) B2823455
theorem B2824427 : Blo 1881142 2824427 := bstep (se 1 (by rfl) ⟨2118320, by rfl⟩ : syracuseStep 2824427 = 4236641) B4236641
theorem B12876029 : Blo 1881142 12876029 := bstep (se 3 (by rfl) ⟨2414255, by rfl⟩ : syracuseStep 12876029 = 4828511) B4828511
theorem B2824487 : Blo 1881142 2824487 := bstep (se 1 (by rfl) ⟨2118365, by rfl⟩ : syracuseStep 2824487 = 4236731) B4236731
theorem B1882415 : Blo 1881142 1882415 := bstep (se 1 (by rfl) ⟨1411811, by rfl⟩ : syracuseStep 1882415 = 2823623) B2823623
theorem B2824571 : Blo 1881142 2824571 := bstep (se 1 (by rfl) ⟨2118428, by rfl⟩ : syracuseStep 2824571 = 4236857) B4236857
theorem B6355475 : Blo 1881142 6355475 := bstep (se 1 (by rfl) ⟨4766606, by rfl⟩ : syracuseStep 6355475 = 9533213) B9533213
theorem B1882651 : Blo 1881142 1882651 := bstep (se 1 (by rfl) ⟨1411988, by rfl⟩ : syracuseStep 1882651 = 2823977) B2823977
theorem B2382367 : Blo 1881142 2382367 := bstep (se 1 (by rfl) ⟨1786775, by rfl⟩ : syracuseStep 2382367 = 3573551) B3573551
theorem B1882655 : Blo 1881142 1882655 := bstep (se 1 (by rfl) ⟨1411991, by rfl⟩ : syracuseStep 1882655 = 2823983) B2823983
theorem B5798623 : Blo 1881142 5798623 := bstep (se 1 (by rfl) ⟨4348967, by rfl⟩ : syracuseStep 5798623 = 8697935) B8697935
theorem B4234067 : Blo 1881142 4234067 := bstep (se 1 (by rfl) ⟨3175550, by rfl⟩ : syracuseStep 4234067 = 6351101) B6351101
theorem B1882971 : Blo 1881142 1882971 := bstep (se 1 (by rfl) ⟨1412228, by rfl⟩ : syracuseStep 1882971 = 2824457) B2824457
theorem B5086057 : Blo 1881142 5086057 := bstep (se 2 (by rfl) ⟨1907271, by rfl⟩ : syracuseStep 5086057 = 3814543) B3814543
theorem B4520863 : Blo 1881142 4520863 := bstep (se 1 (by rfl) ⟨3390647, by rfl⟩ : syracuseStep 4520863 = 6781295) B6781295
theorem B1883039 : Blo 1881142 1883039 := bstep (se 1 (by rfl) ⟨1412279, by rfl⟩ : syracuseStep 1883039 = 2824559) B2824559
theorem B17169317 : Blo 1881142 17169317 := bstep (se 4 (by rfl) ⟨1609623, by rfl⟩ : syracuseStep 17169317 = 3219247) B3219247
theorem B20904925 : Blo 1881142 20904925 := bstep (se 3 (by rfl) ⟨3919673, by rfl⟩ : syracuseStep 20904925 = 7839347) B7839347
theorem B3218411 : Blo 1881142 3218411 := bstep (se 1 (by rfl) ⟨2413808, by rfl⟩ : syracuseStep 3218411 = 4827617) B4827617
theorem B20339693 : Blo 1881142 20339693 := bstep (se 3 (by rfl) ⟨3813692, by rfl⟩ : syracuseStep 20339693 = 7627385) B7627385
theorem B1907759 : Blo 1881142 1907759 := bstep (se 1 (by rfl) ⟨1430819, by rfl⟩ : syracuseStep 1907759 = 2861639) B2861639
theorem B5799041 : Blo 1881142 5799041 := bstep (se 2 (by rfl) ⟨2174640, by rfl⟩ : syracuseStep 5799041 = 4349281) B4349281
theorem B10714295 : Blo 1881142 10714295 := bstep (se 1 (by rfl) ⟨8035721, by rfl⟩ : syracuseStep 10714295 = 16071443) B16071443
theorem B14294231 : Blo 1881142 14294231 := bstep (se 1 (by rfl) ⟨10720673, by rfl⟩ : syracuseStep 14294231 = 21441347) B21441347
theorem B11451611 : Blo 1881142 11451611 := bstep (se 1 (by rfl) ⟨8588708, by rfl⟩ : syracuseStep 11451611 = 17177417) B17177417
theorem B4234607 : Blo 1881142 4234607 := bstep (se 1 (by rfl) ⟨3175955, by rfl⟩ : syracuseStep 4234607 = 6351911) B6351911
theorem B27139475 : Blo 1881142 27139475 := bstep (se 1 (by rfl) ⟨20354606, by rfl⟩ : syracuseStep 27139475 = 40709213) B40709213
theorem B22887845 : Blo 1881142 22887845 := bstep (se 4 (by rfl) ⟨2145735, by rfl⟩ : syracuseStep 22887845 = 4291471) B4291471
theorem B5357011 : Blo 1881142 5357011 := bstep (se 1 (by rfl) ⟨4017758, by rfl⟩ : syracuseStep 5357011 = 8035517) B8035517
theorem B6970835 : Blo 1881142 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B4234895 : Blo 1881142 4234895 := bstep (se 1 (by rfl) ⟨3176171, by rfl⟩ : syracuseStep 4234895 = 6352343) B6352343
theorem B7143137 : Blo 1881142 7143137 := bstep (se 2 (by rfl) ⟨2678676, by rfl⟩ : syracuseStep 7143137 = 5357353) B5357353
theorem B4234985 : Blo 1881142 4234985 := bstep (se 2 (by rfl) ⟨1588119, by rfl⟩ : syracuseStep 4234985 = 3176239) B3176239
theorem B6782707 : Blo 1881142 6782707 := bstep (se 1 (by rfl) ⟨5087030, by rfl⟩ : syracuseStep 6782707 = 10174061) B10174061
theorem B3866491 : Blo 1881142 3866491 := bstep (se 1 (by rfl) ⟨2899868, by rfl⟩ : syracuseStep 3866491 = 5799737) B5799737
theorem B5087357 : Blo 1881142 5087357 := bstep (se 3 (by rfl) ⟨953879, by rfl⟩ : syracuseStep 5087357 = 1907759) B1907759
theorem B3391679 : Blo 1881142 3391679 := bstep (se 1 (by rfl) ⟨2543759, by rfl⟩ : syracuseStep 3391679 = 5087519) B5087519
theorem B4235471 : Blo 1881142 4235471 := bstep (se 1 (by rfl) ⟨3176603, by rfl⟩ : syracuseStep 4235471 = 6353207) B6353207
theorem B4235615 : Blo 1881142 4235615 := bstep (se 1 (by rfl) ⟨3176711, by rfl⟩ : syracuseStep 4235615 = 6353423) B6353423
theorem B5358241 : Blo 1881142 5358241 := bstep (se 2 (by rfl) ⟨2009340, by rfl⟩ : syracuseStep 5358241 = 4018681) B4018681
theorem B6111931 : Blo 1881142 6111931 := bstep (se 1 (by rfl) ⟨4583948, by rfl⟩ : syracuseStep 6111931 = 9167897) B9167897
theorem B7627529 : Blo 1881142 7627529 := bstep (se 2 (by rfl) ⟨2860323, by rfl⟩ : syracuseStep 7627529 = 5720647) B5720647
theorem B117531499 : Blo 1881142 117531499 := bstep (se 1 (by rfl) ⟨88148624, by rfl⟩ : syracuseStep 117531499 = 176297249) B176297249
theorem B4236335 : Blo 1881142 4236335 := bstep (se 1 (by rfl) ⟨3177251, by rfl⟩ : syracuseStep 4236335 = 6354503) B6354503
theorem B12059711 : Blo 1881142 12059711 := bstep (se 1 (by rfl) ⟨9044783, by rfl⟩ : syracuseStep 12059711 = 18089567) B18089567
theorem B11609227 : Blo 1881142 11609227 := bstep (se 1 (by rfl) ⟨8706920, by rfl⟩ : syracuseStep 11609227 = 17413841) B17413841
theorem B12059837 : Blo 1881142 12059837 := bstep (se 3 (by rfl) ⟨2261219, by rfl⟩ : syracuseStep 12059837 = 4522439) B4522439
theorem B5358811 : Blo 1881142 5358811 := bstep (se 1 (by rfl) ⟨4019108, by rfl⟩ : syracuseStep 5358811 = 8038217) B8038217
theorem B19318019 : Blo 1881142 19318019 := bstep (se 1 (by rfl) ⟨14488514, by rfl⟩ : syracuseStep 19318019 = 28977029) B28977029
theorem B3393199 : Blo 1881142 3393199 := bstep (se 1 (by rfl) ⟨2544899, by rfl⟩ : syracuseStep 3393199 = 5089799) B5089799
theorem B4236983 : Blo 1881142 4236983 := bstep (se 1 (by rfl) ⟨3177737, by rfl⟩ : syracuseStep 4236983 = 6355475) B6355475
theorem B17164061 : Blo 1881142 17164061 := bstep (se 3 (by rfl) ⟨3218261, by rfl⟩ : syracuseStep 17164061 = 6436523) B6436523
theorem B11446211 : Blo 1881142 11446211 := bstep (se 1 (by rfl) ⟨8584658, by rfl⟩ : syracuseStep 11446211 = 17169317) B17169317
theorem B4524007 : Blo 1881142 4524007 := bstep (se 1 (by rfl) ⟨3393005, by rfl⟩ : syracuseStep 4524007 = 6786011) B6786011
theorem B13559795 : Blo 1881142 13559795 := bstep (se 1 (by rfl) ⟨10169846, by rfl⟩ : syracuseStep 13559795 = 20339693) B20339693
theorem B7145597 : Blo 1881142 7145597 := bstep (se 3 (by rfl) ⟨1339799, by rfl⟩ : syracuseStep 7145597 = 2679599) B2679599
theorem B9529487 : Blo 1881142 9529487 := bstep (se 1 (by rfl) ⟨7147115, by rfl⟩ : syracuseStep 9529487 = 14294231) B14294231
theorem B3573983 : Blo 1881142 3573983 := bstep (se 1 (by rfl) ⟨2680487, by rfl⟩ : syracuseStep 3573983 = 5360975) B5360975
theorem B4647223 : Blo 1881142 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B14289371 : Blo 1881142 14289371 := bstep (se 1 (by rfl) ⟨10717028, by rfl⟩ : syracuseStep 14289371 = 21434057) B21434057
theorem B4762091 : Blo 1881142 4762091 := bstep (se 1 (by rfl) ⟨3571568, by rfl⟩ : syracuseStep 4762091 = 7143137) B7143137
theorem B5155321 : Blo 1881142 5155321 := bstep (se 2 (by rfl) ⟨1933245, by rfl⟩ : syracuseStep 5155321 = 3866491) B3866491
theorem B173869577 : Blo 1881142 173869577 := bstep (se 2 (by rfl) ⟨65201091, by rfl⟩ : syracuseStep 173869577 = 130402183) B130402183
theorem B77302295 : Blo 1881142 77302295 := bstep (se 1 (by rfl) ⟨57976721, by rfl⟩ : syracuseStep 77302295 = 115953443) B115953443
theorem B154585907 : Blo 1881142 154585907 := bstep (se 1 (by rfl) ⟨115939430, by rfl⟩ : syracuseStep 154585907 = 231878861) B231878861
theorem B6351695 : Blo 1881142 6351695 := bstep (se 1 (by rfl) ⟨4763771, by rfl⟩ : syracuseStep 6351695 = 9527543) B9527543
theorem B17173403 : Blo 1881142 17173403 := bstep (se 1 (by rfl) ⟨12880052, by rfl⟩ : syracuseStep 17173403 = 25760105) B25760105
theorem B14289857 : Blo 1881142 14289857 := bstep (se 2 (by rfl) ⟨5358696, by rfl⟩ : syracuseStep 14289857 = 10717393) B10717393
theorem B14298119 : Blo 1881142 14298119 := bstep (se 1 (by rfl) ⟨10723589, by rfl⟩ : syracuseStep 14298119 = 21447179) B21447179
theorem B9047339 : Blo 1881142 9047339 := bstep (se 1 (by rfl) ⟨6785504, by rfl⟩ : syracuseStep 9047339 = 13571009) B13571009
theorem B16084291 : Blo 1881142 16084291 := bstep (se 1 (by rfl) ⟨12063218, by rfl⟩ : syracuseStep 16084291 = 24126437) B24126437
theorem B9047609 : Blo 1881142 9047609 := bstep (se 2 (by rfl) ⟨3392853, by rfl⟩ : syracuseStep 9047609 = 6785707) B6785707
theorem B8040131 : Blo 1881142 8040131 := bstep (se 1 (by rfl) ⟨6030098, by rfl⟩ : syracuseStep 8040131 = 12060197) B12060197
theorem B2117371 : Blo 1881142 2117371 := bstep (se 1 (by rfl) ⟨1588028, by rfl⟩ : syracuseStep 2117371 = 3176057) B3176057
theorem B2010943 : Blo 1881142 2010943 := bstep (se 1 (by rfl) ⟨1508207, by rfl⟩ : syracuseStep 2010943 = 3016415) B3016415
theorem B2822015 : Blo 1881142 2822015 := bstep (se 1 (by rfl) ⟨2116511, by rfl⟩ : syracuseStep 2822015 = 4233023) B4233023
theorem B27873233 : Blo 1881142 27873233 := bstep (se 2 (by rfl) ⟨10452462, by rfl⟩ : syracuseStep 27873233 = 20904925) B20904925
theorem B5361659 : Blo 1881142 5361659 := bstep (se 1 (by rfl) ⟨4021244, by rfl⟩ : syracuseStep 5361659 = 8042489) B8042489
theorem B2822207 : Blo 1881142 2822207 := bstep (se 1 (by rfl) ⟨2116655, by rfl⟩ : syracuseStep 2822207 = 4233311) B4233311
theorem B2117695 : Blo 1881142 2117695 := bstep (se 1 (by rfl) ⟨1588271, by rfl⟩ : syracuseStep 2117695 = 3176543) B3176543
theorem B7147709 : Blo 1881142 7147709 := bstep (se 3 (by rfl) ⟨1340195, by rfl⟩ : syracuseStep 7147709 = 2680391) B2680391
theorem B2822441 : Blo 1881142 2822441 := bstep (se 2 (by rfl) ⟨1058415, by rfl⟩ : syracuseStep 2822441 = 2116831) B2116831
theorem B27144497 : Blo 1881142 27144497 := bstep (se 2 (by rfl) ⟨10179186, by rfl⟩ : syracuseStep 27144497 = 20358373) B20358373
theorem B2822711 : Blo 1881142 2822711 := bstep (se 1 (by rfl) ⟨2117033, by rfl⟩ : syracuseStep 2822711 = 4234067) B4234067
theorem B4764217 : Blo 1881142 4764217 := bstep (se 2 (by rfl) ⟨1786581, by rfl⟩ : syracuseStep 4764217 = 3573163) B3573163
theorem B12055223 : Blo 1881142 12055223 := bstep (se 1 (by rfl) ⟨9041417, by rfl⟩ : syracuseStep 12055223 = 18082835) B18082835
theorem B3814123 : Blo 1881142 3814123 := bstep (se 1 (by rfl) ⟨2860592, by rfl⟩ : syracuseStep 3814123 = 5721185) B5721185
theorem B2823071 : Blo 1881142 2823071 := bstep (se 1 (by rfl) ⟨2117303, by rfl⟩ : syracuseStep 2823071 = 4234607) B4234607
theorem B18092983 : Blo 1881142 18092983 := bstep (se 1 (by rfl) ⟨13569737, by rfl⟩ : syracuseStep 18092983 = 27139475) B27139475
theorem B15258563 : Blo 1881142 15258563 := bstep (se 1 (by rfl) ⟨11443922, by rfl⟩ : syracuseStep 15258563 = 22887845) B22887845
theorem B3175375 : Blo 1881142 3175375 := bstep (se 1 (by rfl) ⟨2381531, by rfl⟩ : syracuseStep 3175375 = 4763063) B4763063
theorem B8041531 : Blo 1881142 8041531 := bstep (se 1 (by rfl) ⟨6031148, by rfl⟩ : syracuseStep 8041531 = 12062297) B12062297
theorem B1881159 : Blo 1881142 1881159 := bstep (se 1 (by rfl) ⟨1410869, by rfl⟩ : syracuseStep 1881159 = 2821739) B2821739
theorem B2823263 : Blo 1881142 2823263 := bstep (se 1 (by rfl) ⟨2117447, by rfl⟩ : syracuseStep 2823263 = 4234895) B4234895
theorem B1881243 : Blo 1881142 1881243 := bstep (se 1 (by rfl) ⟨1410932, by rfl⟩ : syracuseStep 1881243 = 2821865) B2821865
theorem B2823323 : Blo 1881142 2823323 := bstep (se 1 (by rfl) ⟨2117492, by rfl⟩ : syracuseStep 2823323 = 4234985) B4234985
theorem B1881339 : Blo 1881142 1881339 := bstep (se 1 (by rfl) ⟨1411004, by rfl⟩ : syracuseStep 1881339 = 2822009) B2822009
theorem B8582429 : Blo 1881142 8582429 := bstep (se 3 (by rfl) ⟨1609205, by rfl⟩ : syracuseStep 8582429 = 3218411) B3218411
theorem B1881407 : Blo 1881142 1881407 := bstep (se 1 (by rfl) ⟨1411055, by rfl⟩ : syracuseStep 1881407 = 2822111) B2822111
theorem B7148999 : Blo 1881142 7148999 := bstep (se 1 (by rfl) ⟨5361749, by rfl⟩ : syracuseStep 7148999 = 10723499) B10723499
theorem B1881575 : Blo 1881142 1881575 := bstep (se 1 (by rfl) ⟨1411181, by rfl⟩ : syracuseStep 1881575 = 2822363) B2822363
theorem B1881583 : Blo 1881142 1881583 := bstep (se 1 (by rfl) ⟨1411187, by rfl⟩ : syracuseStep 1881583 = 2822375) B2822375
theorem B1881691 : Blo 1881142 1881691 := bstep (se 1 (by rfl) ⟨1411268, by rfl⟩ : syracuseStep 1881691 = 2822537) B2822537
theorem B4232825 : Blo 1881142 4232825 := bstep (se 2 (by rfl) ⟨1587309, by rfl⟩ : syracuseStep 4232825 = 3174619) B3174619
theorem B1881755 : Blo 1881142 1881755 := bstep (se 1 (by rfl) ⟨1411316, by rfl⟩ : syracuseStep 1881755 = 2822633) B2822633
theorem B1881839 : Blo 1881142 1881839 := bstep (se 1 (by rfl) ⟨1411379, by rfl⟩ : syracuseStep 1881839 = 2822759) B2822759
theorem B1881927 : Blo 1881142 1881927 := bstep (se 1 (by rfl) ⟨1411445, by rfl⟩ : syracuseStep 1881927 = 2822891) B2822891
theorem B2824007 : Blo 1881142 2824007 := bstep (se 1 (by rfl) ⟨2118005, by rfl⟩ : syracuseStep 2824007 = 4236011) B4236011
theorem B1881947 : Blo 1881142 1881947 := bstep (se 1 (by rfl) ⟨1411460, by rfl⟩ : syracuseStep 1881947 = 2822921) B2822921
theorem B1882015 : Blo 1881142 1882015 := bstep (se 1 (by rfl) ⟨1411511, by rfl⟩ : syracuseStep 1882015 = 2823023) B2823023
theorem B4233185 : Blo 1881142 4233185 := bstep (se 2 (by rfl) ⟨1587444, by rfl⟩ : syracuseStep 4233185 = 3174889) B3174889
theorem B3176489 : Blo 1881142 3176489 := bstep (se 2 (by rfl) ⟨1191183, by rfl⟩ : syracuseStep 3176489 = 2382367) B2382367
theorem B1882183 : Blo 1881142 1882183 := bstep (se 1 (by rfl) ⟨1411637, by rfl⟩ : syracuseStep 1882183 = 2823275) B2823275
theorem B8042591 : Blo 1881142 8042591 := bstep (se 1 (by rfl) ⟨6031943, by rfl⟩ : syracuseStep 8042591 = 12063887) B12063887
theorem B19585243 : Blo 1881142 19585243 := bstep (se 1 (by rfl) ⟨14688932, by rfl⟩ : syracuseStep 19585243 = 29377865) B29377865
theorem B1882343 : Blo 1881142 1882343 := bstep (se 1 (by rfl) ⟨1411757, by rfl⟩ : syracuseStep 1882343 = 2823515) B2823515
theorem B4520171 : Blo 1881142 4520171 := bstep (se 1 (by rfl) ⟨3390128, by rfl⟩ : syracuseStep 4520171 = 6780257) B6780257
theorem B7731497 : Blo 1881142 7731497 := bstep (se 2 (by rfl) ⟨2899311, by rfl⟩ : syracuseStep 7731497 = 5798623) B5798623
theorem B1882527 : Blo 1881142 1882527 := bstep (se 1 (by rfl) ⟨1411895, by rfl⟩ : syracuseStep 1882527 = 2823791) B2823791
theorem B2824607 : Blo 1881142 2824607 := bstep (se 1 (by rfl) ⟨2118455, by rfl⟩ : syracuseStep 2824607 = 4236911) B4236911
theorem B1882575 : Blo 1881142 1882575 := bstep (se 1 (by rfl) ⟨1411931, by rfl⟩ : syracuseStep 1882575 = 2823863) B2823863
theorem B6781409 : Blo 1881142 6781409 := bstep (se 2 (by rfl) ⟨2543028, by rfl⟩ : syracuseStep 6781409 = 5086057) B5086057
theorem B2382311 : Blo 1881142 2382311 := bstep (se 1 (by rfl) ⟨1786733, by rfl⟩ : syracuseStep 2382311 = 3573467) B3573467
theorem B1882599 : Blo 1881142 1882599 := bstep (se 1 (by rfl) ⟨1411949, by rfl⟩ : syracuseStep 1882599 = 2823899) B2823899
theorem B2824679 : Blo 1881142 2824679 := bstep (se 1 (by rfl) ⟨2118509, by rfl⟩ : syracuseStep 2824679 = 4237019) B4237019
theorem B6027817 : Blo 1881142 6027817 := bstep (se 2 (by rfl) ⟨2260431, by rfl⟩ : syracuseStep 6027817 = 4520863) B4520863
theorem B1882715 : Blo 1881142 1882715 := bstep (se 1 (by rfl) ⟨1412036, by rfl⟩ : syracuseStep 1882715 = 2824073) B2824073
theorem B36174437 : Blo 1881142 36174437 := bstep (se 4 (by rfl) ⟨3391353, by rfl⟩ : syracuseStep 36174437 = 6782707) B6782707
theorem B3177103 : Blo 1881142 3177103 := bstep (se 1 (by rfl) ⟨2382827, by rfl⟩ : syracuseStep 3177103 = 4765655) B4765655
theorem B1882783 : Blo 1881142 1882783 := bstep (se 1 (by rfl) ⟨1412087, by rfl⟩ : syracuseStep 1882783 = 2824175) B2824175
theorem B3390187 : Blo 1881142 3390187 := bstep (se 1 (by rfl) ⟨2542640, by rfl⟩ : syracuseStep 3390187 = 5085281) B5085281
theorem B1882951 : Blo 1881142 1882951 := bstep (se 1 (by rfl) ⟨1412213, by rfl⟩ : syracuseStep 1882951 = 2824427) B2824427
theorem B8584019 : Blo 1881142 8584019 := bstep (se 1 (by rfl) ⟨6438014, by rfl⟩ : syracuseStep 8584019 = 12876029) B12876029
theorem B1882991 : Blo 1881142 1882991 := bstep (se 1 (by rfl) ⟨1412243, by rfl⟩ : syracuseStep 1882991 = 2824487) B2824487
theorem B1883047 : Blo 1881142 1883047 := bstep (se 1 (by rfl) ⟨1412285, by rfl⟩ : syracuseStep 1883047 = 2824571) B2824571
theorem B10173497 : Blo 1881142 10173497 := bstep (se 2 (by rfl) ⟨3815061, by rfl⟩ : syracuseStep 10173497 = 7630123) B7630123
theorem B7142681 : Blo 1881142 7142681 := bstep (se 2 (by rfl) ⟨2678505, by rfl⟩ : syracuseStep 7142681 = 5357011) B5357011
theorem B3866027 : Blo 1881142 3866027 := bstep (se 1 (by rfl) ⟨2899520, by rfl⟩ : syracuseStep 3866027 = 5799041) B5799041
theorem B7142863 : Blo 1881142 7142863 := bstep (se 1 (by rfl) ⟨5357147, by rfl⟩ : syracuseStep 7142863 = 10714295) B10714295
theorem B7634407 : Blo 1881142 7634407 := bstep (se 1 (by rfl) ⟨5725805, by rfl⟩ : syracuseStep 7634407 = 11451611) B11451611
theorem B4235039 : Blo 1881142 4235039 := bstep (se 1 (by rfl) ⟨3176279, by rfl⟩ : syracuseStep 4235039 = 6352559) B6352559
theorem B16072505 : Blo 1881142 16072505 := bstep (se 2 (by rfl) ⟨6027189, by rfl⟩ : syracuseStep 16072505 = 12054379) B12054379
theorem B21438431 : Blo 1881142 21438431 := bstep (se 1 (by rfl) ⟨16078823, by rfl⟩ : syracuseStep 21438431 = 32157647) B32157647
theorem B4235255 : Blo 1881142 4235255 := bstep (se 1 (by rfl) ⟨3176441, by rfl⟩ : syracuseStep 4235255 = 6352883) B6352883
theorem B3391571 : Blo 1881142 3391571 := bstep (se 1 (by rfl) ⟨2543678, by rfl⟩ : syracuseStep 3391571 = 5087357) B5087357
theorem B2261119 : Blo 1881142 2261119 := bstep (se 1 (by rfl) ⟨1695839, by rfl⟩ : syracuseStep 2261119 = 3391679) B3391679
theorem B18096331 : Blo 1881142 18096331 := bstep (se 1 (by rfl) ⟨13572248, by rfl⟩ : syracuseStep 18096331 = 27144497) B27144497
theorem B8036815 : Blo 1881142 8036815 := bstep (se 1 (by rfl) ⟨6027611, by rfl⟩ : syracuseStep 8036815 = 12055223) B12055223
theorem B6873761 : Blo 1881142 6873761 := bstep (se 2 (by rfl) ⟨2577660, by rfl⟩ : syracuseStep 6873761 = 5155321) B5155321
theorem B8037089 : Blo 1881142 8037089 := bstep (se 2 (by rfl) ⟨3013908, by rfl⟩ : syracuseStep 8037089 = 6027817) B6027817
theorem B61915877 : Blo 1881142 61915877 := bstep (se 4 (by rfl) ⟨5804613, by rfl⟩ : syracuseStep 61915877 = 11609227) B11609227
theorem B4236137 : Blo 1881142 4236137 := bstep (se 2 (by rfl) ⟨1588551, by rfl⟩ : syracuseStep 4236137 = 3177103) B3177103
theorem B7144321 : Blo 1881142 7144321 := bstep (se 2 (by rfl) ⟨2679120, by rfl⟩ : syracuseStep 7144321 = 5358241) B5358241
theorem B7145081 : Blo 1881142 7145081 := bstep (se 2 (by rfl) ⟨2679405, by rfl⟩ : syracuseStep 7145081 = 5358811) B5358811
theorem B103057271 : Blo 1881142 103057271 := bstep (se 1 (by rfl) ⟨77292953, by rfl⟩ : syracuseStep 103057271 = 154585907) B154585907
theorem B4761787 : Blo 1881142 4761787 := bstep (se 1 (by rfl) ⟨3571340, by rfl⟩ : syracuseStep 4761787 = 7142681) B7142681
theorem B6031559 : Blo 1881142 6031559 := bstep (se 1 (by rfl) ⟨4523669, by rfl⟩ : syracuseStep 6031559 = 9047339) B9047339
theorem B4524265 : Blo 1881142 4524265 := bstep (se 2 (by rfl) ⟨1696599, by rfl⟩ : syracuseStep 4524265 = 3393199) B3393199
theorem B6031739 : Blo 1881142 6031739 := bstep (se 1 (by rfl) ⟨4523804, by rfl⟩ : syracuseStep 6031739 = 9047609) B9047609
theorem B2681257 : Blo 1881142 2681257 := bstep (se 2 (by rfl) ⟨1005471, by rfl⟩ : syracuseStep 2681257 = 2010943) B2010943
theorem B5360087 : Blo 1881142 5360087 := bstep (se 1 (by rfl) ⟨4020065, by rfl⟩ : syracuseStep 5360087 = 8040131) B8040131
theorem B6032009 : Blo 1881142 6032009 := bstep (se 2 (by rfl) ⟨2262003, by rfl⟩ : syracuseStep 6032009 = 4524007) B4524007
theorem B18582155 : Blo 1881142 18582155 := bstep (se 1 (by rfl) ⟨13936616, by rfl⟩ : syracuseStep 18582155 = 27873233) B27873233
theorem B3574439 : Blo 1881142 3574439 := bstep (se 1 (by rfl) ⟨2680829, by rfl⟩ : syracuseStep 3574439 = 5361659) B5361659
theorem B9530621 : Blo 1881142 9530621 := bstep (se 3 (by rfl) ⟨1786991, by rfl⟩ : syracuseStep 9530621 = 3573983) B3573983
theorem B51514717 : Blo 1881142 51514717 := bstep (se 3 (by rfl) ⟨9659009, by rfl⟩ : syracuseStep 51514717 = 19318019) B19318019
theorem B8039807 : Blo 1881142 8039807 := bstep (se 1 (by rfl) ⟨6029855, by rfl⟩ : syracuseStep 8039807 = 12059711) B12059711
theorem B6352289 : Blo 1881142 6352289 := bstep (se 2 (by rfl) ⟨2382108, by rfl⟩ : syracuseStep 6352289 = 4764217) B4764217
theorem B8039891 : Blo 1881142 8039891 := bstep (se 1 (by rfl) ⟨6029918, by rfl⟩ : syracuseStep 8039891 = 12059837) B12059837
theorem B2821883 : Blo 1881142 2821883 := bstep (se 1 (by rfl) ⟨2116412, by rfl⟩ : syracuseStep 2821883 = 4232825) B4232825
theorem B10309405 : Blo 1881142 10309405 := bstep (se 3 (by rfl) ⟨1933013, by rfl⟩ : syracuseStep 10309405 = 3866027) B3866027
theorem B156708665 : Blo 1881142 156708665 := bstep (se 2 (by rfl) ⟨58765749, by rfl⟩ : syracuseStep 156708665 = 117531499) B117531499
theorem B6352829 : Blo 1881142 6352829 := bstep (se 3 (by rfl) ⟨1191155, by rfl⟩ : syracuseStep 6352829 = 2382311) B2382311
theorem B2822123 : Blo 1881142 2822123 := bstep (se 1 (by rfl) ⟨2116592, by rfl⟩ : syracuseStep 2822123 = 4233185) B4233185
theorem B9039863 : Blo 1881142 9039863 := bstep (se 1 (by rfl) ⟨6779897, by rfl⟩ : syracuseStep 9039863 = 13559795) B13559795
theorem B2117659 : Blo 1881142 2117659 := bstep (se 1 (by rfl) ⟨1588244, by rfl⟩ : syracuseStep 2117659 = 3176489) B3176489
theorem B5361727 : Blo 1881142 5361727 := bstep (se 1 (by rfl) ⟨4021295, by rfl⟩ : syracuseStep 5361727 = 8042591) B8042591
theorem B4763731 : Blo 1881142 4763731 := bstep (se 1 (by rfl) ⟨3572798, by rfl⟩ : syracuseStep 4763731 = 7145597) B7145597
theorem B6352991 : Blo 1881142 6352991 := bstep (se 1 (by rfl) ⟨4764743, by rfl⟩ : syracuseStep 6352991 = 9529487) B9529487
theorem B24785189 : Blo 1881142 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B3174727 : Blo 1881142 3174727 := bstep (se 1 (by rfl) ⟨2381045, by rfl⟩ : syracuseStep 3174727 = 4762091) B4762091
theorem B115913051 : Blo 1881142 115913051 := bstep (se 1 (by rfl) ⟨86934788, by rfl⟩ : syracuseStep 115913051 = 173869577) B173869577
theorem B5722679 : Blo 1881142 5722679 := bstep (se 1 (by rfl) ⟨4292009, by rfl⟩ : syracuseStep 5722679 = 8584019) B8584019
theorem B11448935 : Blo 1881142 11448935 := bstep (se 1 (by rfl) ⟨8586701, by rfl⟩ : syracuseStep 11448935 = 17173403) B17173403
theorem B9523817 : Blo 1881142 9523817 := bstep (se 2 (by rfl) ⟨3571431, by rfl⟩ : syracuseStep 9523817 = 7142863) B7142863
theorem B10179209 : Blo 1881142 10179209 := bstep (se 2 (by rfl) ⟨3817203, by rfl⟩ : syracuseStep 10179209 = 7634407) B7634407
theorem B9532079 : Blo 1881142 9532079 := bstep (se 1 (by rfl) ⟨7149059, by rfl⟩ : syracuseStep 9532079 = 14298119) B14298119
theorem B2823161 : Blo 1881142 2823161 := bstep (se 2 (by rfl) ⟨1058685, by rfl⟩ : syracuseStep 2823161 = 2117371) B2117371
theorem B2823359 : Blo 1881142 2823359 := bstep (se 1 (by rfl) ⟨2117519, by rfl⟩ : syracuseStep 2823359 = 4235039) B4235039
theorem B1881343 : Blo 1881142 1881343 := bstep (se 1 (by rfl) ⟨1411007, by rfl⟩ : syracuseStep 1881343 = 2822015) B2822015
theorem B14292287 : Blo 1881142 14292287 := bstep (se 1 (by rfl) ⟨10719215, by rfl⟩ : syracuseStep 14292287 = 21438431) B21438431
theorem B2823503 : Blo 1881142 2823503 := bstep (se 1 (by rfl) ⟨2117627, by rfl⟩ : syracuseStep 2823503 = 4235255) B4235255
theorem B1881471 : Blo 1881142 1881471 := bstep (se 1 (by rfl) ⟨1411103, by rfl⟩ : syracuseStep 1881471 = 2822207) B2822207
theorem B2823593 : Blo 1881142 2823593 := bstep (se 2 (by rfl) ⟨1058847, by rfl⟩ : syracuseStep 2823593 = 2117695) B2117695
theorem B4765139 : Blo 1881142 4765139 := bstep (se 1 (by rfl) ⟨3573854, by rfl⟩ : syracuseStep 4765139 = 7147709) B7147709
theorem B2823647 : Blo 1881142 2823647 := bstep (se 1 (by rfl) ⟨2117735, by rfl⟩ : syracuseStep 2823647 = 4235471) B4235471
theorem B27129325 : Blo 1881142 27129325 := bstep (se 3 (by rfl) ⟨5086748, by rfl⟩ : syracuseStep 27129325 = 10173497) B10173497
theorem B1881627 : Blo 1881142 1881627 := bstep (se 1 (by rfl) ⟨1411220, by rfl⟩ : syracuseStep 1881627 = 2822441) B2822441
theorem B2823743 : Blo 1881142 2823743 := bstep (se 1 (by rfl) ⟨2117807, by rfl⟩ : syracuseStep 2823743 = 4235615) B4235615
theorem B1881807 : Blo 1881142 1881807 := bstep (se 1 (by rfl) ⟨1411355, by rfl⟩ : syracuseStep 1881807 = 2822711) B2822711
theorem B5085019 : Blo 1881142 5085019 := bstep (se 1 (by rfl) ⟨3813764, by rfl⟩ : syracuseStep 5085019 = 7627529) B7627529
theorem B1882047 : Blo 1881142 1882047 := bstep (se 1 (by rfl) ⟨1411535, by rfl⟩ : syracuseStep 1882047 = 2823071) B2823071
theorem B10172375 : Blo 1881142 10172375 := bstep (se 1 (by rfl) ⟨7629281, by rfl⟩ : syracuseStep 10172375 = 15258563) B15258563
theorem B2824223 : Blo 1881142 2824223 := bstep (se 1 (by rfl) ⟨2118167, by rfl⟩ : syracuseStep 2824223 = 4236335) B4236335
theorem B1882175 : Blo 1881142 1882175 := bstep (se 1 (by rfl) ⟨1411631, by rfl⟩ : syracuseStep 1882175 = 2823263) B2823263
theorem B22886477 : Blo 1881142 22886477 := bstep (se 3 (by rfl) ⟨4291214, by rfl⟩ : syracuseStep 22886477 = 8582429) B8582429
theorem B1882215 : Blo 1881142 1882215 := bstep (se 1 (by rfl) ⟨1411661, by rfl⟩ : syracuseStep 1882215 = 2823323) B2823323
theorem B20617325 : Blo 1881142 20617325 := bstep (se 3 (by rfl) ⟨3865748, by rfl⟩ : syracuseStep 20617325 = 7731497) B7731497
theorem B8149241 : Blo 1881142 8149241 := bstep (se 2 (by rfl) ⟨3055965, by rfl⟩ : syracuseStep 8149241 = 6111931) B6111931
theorem B4765999 : Blo 1881142 4765999 := bstep (se 1 (by rfl) ⟨3574499, by rfl⟩ : syracuseStep 4765999 = 7148999) B7148999
theorem B4520249 : Blo 1881142 4520249 := bstep (se 2 (by rfl) ⟨1695093, by rfl⟩ : syracuseStep 4520249 = 3390187) B3390187
theorem B5085497 : Blo 1881142 5085497 := bstep (se 2 (by rfl) ⟨1907061, by rfl⟩ : syracuseStep 5085497 = 3814123) B3814123
theorem B2824655 : Blo 1881142 2824655 := bstep (se 1 (by rfl) ⟨2118491, by rfl⟩ : syracuseStep 2824655 = 4236983) B4236983
theorem B104454629 : Blo 1881142 104454629 := bstep (se 4 (by rfl) ⟨9792621, by rfl⟩ : syracuseStep 104454629 = 19585243) B19585243
theorem B11442707 : Blo 1881142 11442707 := bstep (se 1 (by rfl) ⟨8582030, by rfl⟩ : syracuseStep 11442707 = 17164061) B17164061
theorem B1882671 : Blo 1881142 1882671 := bstep (se 1 (by rfl) ⟨1412003, by rfl⟩ : syracuseStep 1882671 = 2824007) B2824007
theorem B24123977 : Blo 1881142 24123977 := bstep (se 2 (by rfl) ⟨9046491, by rfl⟩ : syracuseStep 24123977 = 18092983) B18092983
theorem B4233833 : Blo 1881142 4233833 := bstep (se 2 (by rfl) ⟨1587687, by rfl⟩ : syracuseStep 4233833 = 3175375) B3175375
theorem B10722041 : Blo 1881142 10722041 := bstep (se 2 (by rfl) ⟨4020765, by rfl⟩ : syracuseStep 10722041 = 8041531) B8041531
theorem B3013447 : Blo 1881142 3013447 := bstep (se 1 (by rfl) ⟨2260085, by rfl⟩ : syracuseStep 3013447 = 4520171) B4520171
theorem B1883071 : Blo 1881142 1883071 := bstep (se 1 (by rfl) ⟨1412303, by rfl⟩ : syracuseStep 1883071 = 2824607) B2824607
theorem B9526247 : Blo 1881142 9526247 := bstep (se 1 (by rfl) ⟨7144685, by rfl⟩ : syracuseStep 9526247 = 14289371) B14289371
theorem B4520939 : Blo 1881142 4520939 := bstep (se 1 (by rfl) ⟨3390704, by rfl⟩ : syracuseStep 4520939 = 6781409) B6781409
theorem B1883119 : Blo 1881142 1883119 := bstep (se 1 (by rfl) ⟨1412339, by rfl⟩ : syracuseStep 1883119 = 2824679) B2824679
theorem B51534863 : Blo 1881142 51534863 := bstep (se 1 (by rfl) ⟨38651147, by rfl⟩ : syracuseStep 51534863 = 77302295) B77302295
theorem B24116291 : Blo 1881142 24116291 := bstep (se 1 (by rfl) ⟨18087218, by rfl⟩ : syracuseStep 24116291 = 36174437) B36174437
theorem B21445721 : Blo 1881142 21445721 := bstep (se 2 (by rfl) ⟨8042145, by rfl⟩ : syracuseStep 21445721 = 16084291) B16084291
theorem B4234463 : Blo 1881142 4234463 := bstep (se 1 (by rfl) ⟨3175847, by rfl⟩ : syracuseStep 4234463 = 6351695) B6351695
theorem B9526571 : Blo 1881142 9526571 := bstep (se 1 (by rfl) ⟨7144928, by rfl⟩ : syracuseStep 9526571 = 14289857) B14289857
theorem B30523229 : Blo 1881142 30523229 := bstep (se 3 (by rfl) ⟨5723105, by rfl⟩ : syracuseStep 30523229 = 11446211) B11446211
theorem B10715003 : Blo 1881142 10715003 := bstep (se 1 (by rfl) ⟨8036252, by rfl⟩ : syracuseStep 10715003 = 16072505) B16072505
theorem B2261047 : Blo 1881142 2261047 := bstep (se 1 (by rfl) ⟨1695785, by rfl⟩ : syracuseStep 2261047 = 3391571) B3391571
theorem B4235327 : Blo 1881142 4235327 := bstep (se 1 (by rfl) ⟨3176495, by rfl⟩ : syracuseStep 4235327 = 6352991) B6352991
theorem B3014825 : Blo 1881142 3014825 := bstep (se 2 (by rfl) ⟨1130559, by rfl⟩ : syracuseStep 3014825 = 2261119) B2261119
theorem B16523459 : Blo 1881142 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B77275367 : Blo 1881142 77275367 := bstep (se 1 (by rfl) ⟨57956525, by rfl⟩ : syracuseStep 77275367 = 115913051) B115913051
theorem B6349049 : Blo 1881142 6349049 := bstep (se 2 (by rfl) ⟨2380893, by rfl⟩ : syracuseStep 6349049 = 4761787) B4761787
theorem B6349211 : Blo 1881142 6349211 := bstep (se 1 (by rfl) ⟨4761908, by rfl⟩ : syracuseStep 6349211 = 9523817) B9523817
theorem B5358059 : Blo 1881142 5358059 := bstep (se 1 (by rfl) ⟨4018544, by rfl⟩ : syracuseStep 5358059 = 8037089) B8037089
theorem B10715753 : Blo 1881142 10715753 := bstep (se 2 (by rfl) ⟨4018407, by rfl⟩ : syracuseStep 10715753 = 8036815) B8036815
theorem B9528191 : Blo 1881142 9528191 := bstep (se 1 (by rfl) ⟨7146143, by rfl⟩ : syracuseStep 9528191 = 14292287) B14292287
theorem B5432827 : Blo 1881142 5432827 := bstep (se 1 (by rfl) ⟨4074620, by rfl⟩ : syracuseStep 5432827 = 8149241) B8149241
theorem B3573391 : Blo 1881142 3573391 := bstep (se 1 (by rfl) ⟨2680043, by rfl⟩ : syracuseStep 3573391 = 5360087) B5360087
theorem B7628471 : Blo 1881142 7628471 := bstep (se 1 (by rfl) ⟨5721353, by rfl⟩ : syracuseStep 7628471 = 11442707) B11442707
theorem B16082651 : Blo 1881142 16082651 := bstep (se 1 (by rfl) ⟨12061988, by rfl⟩ : syracuseStep 16082651 = 24123977) B24123977
theorem B12388103 : Blo 1881142 12388103 := bstep (se 1 (by rfl) ⟨9291077, by rfl⟩ : syracuseStep 12388103 = 18582155) B18582155
theorem B6350831 : Blo 1881142 6350831 := bstep (se 1 (by rfl) ⟨4763123, by rfl⟩ : syracuseStep 6350831 = 9526247) B9526247
theorem B14297147 : Blo 1881142 14297147 := bstep (se 1 (by rfl) ⟨10722860, by rfl⟩ : syracuseStep 14297147 = 21445721) B21445721
theorem B6351047 : Blo 1881142 6351047 := bstep (se 1 (by rfl) ⟨4763285, by rfl⟩ : syracuseStep 6351047 = 9526571) B9526571
theorem B5359871 : Blo 1881142 5359871 := bstep (se 1 (by rfl) ⟨4019903, by rfl⟩ : syracuseStep 5359871 = 8039807) B8039807
theorem B5359927 : Blo 1881142 5359927 := bstep (se 1 (by rfl) ⟨4019945, by rfl⟩ : syracuseStep 5359927 = 8039891) B8039891
theorem B6351641 : Blo 1881142 6351641 := bstep (se 2 (by rfl) ⟨2381865, by rfl⟩ : syracuseStep 6351641 = 4763731) B4763731
theorem B24128441 : Blo 1881142 24128441 := bstep (se 2 (by rfl) ⟨9048165, by rfl⟩ : syracuseStep 24128441 = 18096331) B18096331
theorem B6786139 : Blo 1881142 6786139 := bstep (se 1 (by rfl) ⟨5089604, by rfl⟩ : syracuseStep 6786139 = 10179209) B10179209
theorem B4582507 : Blo 1881142 4582507 := bstep (se 1 (by rfl) ⟨3436880, by rfl⟩ : syracuseStep 4582507 = 6873761) B6873761
theorem B3575009 : Blo 1881142 3575009 := bstep (se 2 (by rfl) ⟨1340628, by rfl⟩ : syracuseStep 3575009 = 2681257) B2681257
theorem B4763387 : Blo 1881142 4763387 := bstep (se 1 (by rfl) ⟨3572540, by rfl⟩ : syracuseStep 4763387 = 7145081) B7145081
theorem B4017929 : Blo 1881142 4017929 := bstep (se 2 (by rfl) ⟨1506723, by rfl⟩ : syracuseStep 4017929 = 3013447) B3013447
theorem B24129413 : Blo 1881142 24129413 := bstep (se 4 (by rfl) ⟨2262132, by rfl⟩ : syracuseStep 24129413 = 4524265) B4524265
theorem B15257651 : Blo 1881142 15257651 := bstep (se 1 (by rfl) ⟨11443238, by rfl⟩ : syracuseStep 15257651 = 22886477) B22886477
theorem B69636419 : Blo 1881142 69636419 := bstep (se 1 (by rfl) ⟨52227314, by rfl⟩ : syracuseStep 69636419 = 104454629) B104454629
theorem B2822555 : Blo 1881142 2822555 := bstep (se 1 (by rfl) ⟨2116916, by rfl⟩ : syracuseStep 2822555 = 4233833) B4233833
theorem B68686289 : Blo 1881142 68686289 := bstep (se 2 (by rfl) ⟨25757358, by rfl⟩ : syracuseStep 68686289 = 51514717) B51514717
theorem B7148027 : Blo 1881142 7148027 := bstep (se 1 (by rfl) ⟨5361020, by rfl⟩ : syracuseStep 7148027 = 10722041) B10722041
theorem B36172433 : Blo 1881142 36172433 := bstep (se 2 (by rfl) ⟨13564662, by rfl⟩ : syracuseStep 36172433 = 27129325) B27129325
theorem B16077527 : Blo 1881142 16077527 := bstep (se 1 (by rfl) ⟨12058145, by rfl⟩ : syracuseStep 16077527 = 24116291) B24116291
theorem B2822975 : Blo 1881142 2822975 := bstep (se 1 (by rfl) ⟨2117231, by rfl⟩ : syracuseStep 2822975 = 4234463) B4234463
theorem B6353747 : Blo 1881142 6353747 := bstep (se 1 (by rfl) ⟨4765310, by rfl⟩ : syracuseStep 6353747 = 9530621) B9530621
theorem B48223349 : Blo 1881142 48223349 := bstep (se 5 (by rfl) ⟨2260469, by rfl⟩ : syracuseStep 48223349 = 4520939) B4520939
theorem B6780025 : Blo 1881142 6780025 := bstep (se 2 (by rfl) ⟨2542509, by rfl⟩ : syracuseStep 6780025 = 5085019) B5085019
theorem B1881255 : Blo 1881142 1881255 := bstep (se 1 (by rfl) ⟨1410941, by rfl⟩ : syracuseStep 1881255 = 2821883) B2821883
theorem B1881415 : Blo 1881142 1881415 := bstep (se 1 (by rfl) ⟨1411061, by rfl⟩ : syracuseStep 1881415 = 2822123) B2822123
theorem B6026575 : Blo 1881142 6026575 := bstep (se 1 (by rfl) ⟨4519931, by rfl⟩ : syracuseStep 6026575 = 9039863) B9039863
theorem B2823545 : Blo 1881142 2823545 := bstep (se 2 (by rfl) ⟨1058829, by rfl⟩ : syracuseStep 2823545 = 2117659) B2117659
theorem B7148969 : Blo 1881142 7148969 := bstep (se 2 (by rfl) ⟨2680863, by rfl⟩ : syracuseStep 7148969 = 5361727) B5361727
theorem B3815119 : Blo 1881142 3815119 := bstep (se 1 (by rfl) ⟨2861339, by rfl⟩ : syracuseStep 3815119 = 5722679) B5722679
theorem B6354665 : Blo 1881142 6354665 := bstep (se 2 (by rfl) ⟨2382999, by rfl⟩ : syracuseStep 6354665 = 4765999) B4765999
theorem B7632623 : Blo 1881142 7632623 := bstep (se 1 (by rfl) ⟨5724467, by rfl⟩ : syracuseStep 7632623 = 11448935) B11448935
theorem B4232969 : Blo 1881142 4232969 := bstep (se 2 (by rfl) ⟨1587363, by rfl⟩ : syracuseStep 4232969 = 3174727) B3174727
theorem B6354719 : Blo 1881142 6354719 := bstep (se 1 (by rfl) ⟨4766039, by rfl⟩ : syracuseStep 6354719 = 9532079) B9532079
theorem B41277251 : Blo 1881142 41277251 := bstep (se 1 (by rfl) ⟨30957938, by rfl⟩ : syracuseStep 41277251 = 61915877) B61915877
theorem B2824091 : Blo 1881142 2824091 := bstep (se 1 (by rfl) ⟨2118068, by rfl⟩ : syracuseStep 2824091 = 4236137) B4236137
theorem B1882107 : Blo 1881142 1882107 := bstep (se 1 (by rfl) ⟨1411580, by rfl⟩ : syracuseStep 1882107 = 2823161) B2823161
theorem B1882239 : Blo 1881142 1882239 := bstep (se 1 (by rfl) ⟨1411679, by rfl⟩ : syracuseStep 1882239 = 2823359) B2823359
theorem B1882335 : Blo 1881142 1882335 := bstep (se 1 (by rfl) ⟨1411751, by rfl⟩ : syracuseStep 1882335 = 2823503) B2823503
theorem B1882395 : Blo 1881142 1882395 := bstep (se 1 (by rfl) ⟨1411796, by rfl⟩ : syracuseStep 1882395 = 2823593) B2823593
theorem B3176759 : Blo 1881142 3176759 := bstep (se 1 (by rfl) ⟨2382569, by rfl⟩ : syracuseStep 3176759 = 4765139) B4765139
theorem B1882431 : Blo 1881142 1882431 := bstep (se 1 (by rfl) ⟨1411823, by rfl⟩ : syracuseStep 1882431 = 2823647) B2823647
theorem B1882495 : Blo 1881142 1882495 := bstep (se 1 (by rfl) ⟨1411871, by rfl⟩ : syracuseStep 1882495 = 2823743) B2823743
theorem B9525761 : Blo 1881142 9525761 := bstep (se 2 (by rfl) ⟨3572160, by rfl⟩ : syracuseStep 9525761 = 7144321) B7144321
theorem B68704847 : Blo 1881142 68704847 := bstep (se 1 (by rfl) ⟨51528635, by rfl⟩ : syracuseStep 68704847 = 103057271) B103057271
theorem B6781583 : Blo 1881142 6781583 := bstep (se 1 (by rfl) ⟨5086187, by rfl⟩ : syracuseStep 6781583 = 10172375) B10172375
theorem B1882815 : Blo 1881142 1882815 := bstep (se 1 (by rfl) ⟨1412111, by rfl⟩ : syracuseStep 1882815 = 2824223) B2824223
theorem B13744883 : Blo 1881142 13744883 := bstep (se 1 (by rfl) ⟨10308662, by rfl⟩ : syracuseStep 13744883 = 20617325) B20617325
theorem B4021039 : Blo 1881142 4021039 := bstep (se 1 (by rfl) ⟨3015779, by rfl⟩ : syracuseStep 4021039 = 6031559) B6031559
theorem B3013499 : Blo 1881142 3013499 := bstep (se 1 (by rfl) ⟨2260124, by rfl⟩ : syracuseStep 3013499 = 4520249) B4520249
theorem B3390331 : Blo 1881142 3390331 := bstep (se 1 (by rfl) ⟨2542748, by rfl⟩ : syracuseStep 3390331 = 5085497) B5085497
theorem B4021159 : Blo 1881142 4021159 := bstep (se 1 (by rfl) ⟨3015869, by rfl⟩ : syracuseStep 4021159 = 6031739) B6031739
theorem B1883103 : Blo 1881142 1883103 := bstep (se 1 (by rfl) ⟨1412327, by rfl⟩ : syracuseStep 1883103 = 2824655) B2824655
theorem B4021339 : Blo 1881142 4021339 := bstep (se 1 (by rfl) ⟨3016004, by rfl⟩ : syracuseStep 4021339 = 6032009) B6032009
theorem B2382959 : Blo 1881142 2382959 := bstep (se 1 (by rfl) ⟨1787219, by rfl⟩ : syracuseStep 2382959 = 3574439) B3574439
theorem B34356575 : Blo 1881142 34356575 := bstep (se 1 (by rfl) ⟨25767431, by rfl⟩ : syracuseStep 34356575 = 51534863) B51534863
theorem B4234859 : Blo 1881142 4234859 := bstep (se 1 (by rfl) ⟨3176144, by rfl⟩ : syracuseStep 4234859 = 6352289) B6352289
theorem B13745873 : Blo 1881142 13745873 := bstep (se 2 (by rfl) ⟨5154702, by rfl⟩ : syracuseStep 13745873 = 10309405) B10309405
theorem B104472443 : Blo 1881142 104472443 := bstep (se 1 (by rfl) ⟨78354332, by rfl⟩ : syracuseStep 104472443 = 156708665) B156708665
theorem B20348819 : Blo 1881142 20348819 := bstep (se 1 (by rfl) ⟨15261614, by rfl⟩ : syracuseStep 20348819 = 30523229) B30523229
theorem B7143335 : Blo 1881142 7143335 := bstep (se 1 (by rfl) ⟨5357501, by rfl⟩ : syracuseStep 7143335 = 10715003) B10715003
theorem B4235219 : Blo 1881142 4235219 := bstep (se 1 (by rfl) ⟨3176414, by rfl⟩ : syracuseStep 4235219 = 6352829) B6352829
theorem B3014729 : Blo 1881142 3014729 := bstep (se 2 (by rfl) ⟨1130523, by rfl⟩ : syracuseStep 3014729 = 2261047) B2261047
theorem B46424279 : Blo 1881142 46424279 := bstep (se 1 (by rfl) ⟨34818209, by rfl⟩ : syracuseStep 46424279 = 69636419) B69636419
theorem B3572039 : Blo 1881142 3572039 := bstep (se 1 (by rfl) ⟨2679029, by rfl⟩ : syracuseStep 3572039 = 5358059) B5358059
theorem B7143835 : Blo 1881142 7143835 := bstep (se 1 (by rfl) ⟨5357876, by rfl⟩ : syracuseStep 7143835 = 10715753) B10715753
theorem B4235831 : Blo 1881142 4235831 := bstep (se 1 (by rfl) ⟨3176873, by rfl⟩ : syracuseStep 4235831 = 6353747) B6353747
theorem B4236443 : Blo 1881142 4236443 := bstep (se 1 (by rfl) ⟨3177332, by rfl⟩ : syracuseStep 4236443 = 6354665) B6354665
theorem B5088415 : Blo 1881142 5088415 := bstep (se 1 (by rfl) ⟨3816311, by rfl⟩ : syracuseStep 5088415 = 7632623) B7632623
theorem B8258735 : Blo 1881142 8258735 := bstep (se 1 (by rfl) ⟨6194051, by rfl⟩ : syracuseStep 8258735 = 12388103) B12388103
theorem B4236479 : Blo 1881142 4236479 := bstep (se 1 (by rfl) ⟨3177359, by rfl⟩ : syracuseStep 4236479 = 6354719) B6354719
theorem B27518167 : Blo 1881142 27518167 := bstep (se 1 (by rfl) ⟨20638625, by rfl⟩ : syracuseStep 27518167 = 41277251) B41277251
theorem B3573247 : Blo 1881142 3573247 := bstep (se 1 (by rfl) ⟨2679935, by rfl⟩ : syracuseStep 3573247 = 5359871) B5359871
theorem B6350507 : Blo 1881142 6350507 := bstep (se 1 (by rfl) ⟨4762880, by rfl⟩ : syracuseStep 6350507 = 9525761) B9525761
theorem B45803231 : Blo 1881142 45803231 := bstep (se 1 (by rfl) ⟨34352423, by rfl⟩ : syracuseStep 45803231 = 68704847) B68704847
theorem B2008999 : Blo 1881142 2008999 := bstep (se 1 (by rfl) ⟨1506749, by rfl⟩ : syracuseStep 2008999 = 3013499) B3013499
theorem B7243769 : Blo 1881142 7243769 := bstep (se 2 (by rfl) ⟨2716413, by rfl⟩ : syracuseStep 7243769 = 5432827) B5432827
theorem B4762223 : Blo 1881142 4762223 := bstep (se 1 (by rfl) ⟨3571667, by rfl⟩ : syracuseStep 4762223 = 7143335) B7143335
theorem B7146569 : Blo 1881142 7146569 := bstep (se 2 (by rfl) ⟨2679963, by rfl⟩ : syracuseStep 7146569 = 5359927) B5359927
theorem B8039533 : Blo 1881142 8039533 := bstep (se 3 (by rfl) ⟨1507412, by rfl⟩ : syracuseStep 8039533 = 3014825) B3014825
theorem B10718351 : Blo 1881142 10718351 := bstep (se 1 (by rfl) ⟨8038763, by rfl⟩ : syracuseStep 10718351 = 16077527) B16077527
theorem B6352127 : Blo 1881142 6352127 := bstep (se 1 (by rfl) ⟨4764095, by rfl⟩ : syracuseStep 6352127 = 9528191) B9528191
theorem B32148899 : Blo 1881142 32148899 := bstep (se 1 (by rfl) ⟨24111674, by rfl⟩ : syracuseStep 32148899 = 48223349) B48223349
theorem B5361385 : Blo 1881142 5361385 := bstep (se 2 (by rfl) ⟨2010519, by rfl⟩ : syracuseStep 5361385 = 4021039) B4021039
theorem B2821979 : Blo 1881142 2821979 := bstep (se 1 (by rfl) ⟨2116484, by rfl⟩ : syracuseStep 2821979 = 4232969) B4232969
theorem B5361545 : Blo 1881142 5361545 := bstep (se 2 (by rfl) ⟨2010579, by rfl⟩ : syracuseStep 5361545 = 4021159) B4021159
theorem B9531431 : Blo 1881142 9531431 := bstep (se 1 (by rfl) ⟨7148573, by rfl⟩ : syracuseStep 9531431 = 14297147) B14297147
theorem B5361785 : Blo 1881142 5361785 := bstep (se 2 (by rfl) ⟨2010669, by rfl⟩ : syracuseStep 5361785 = 4021339) B4021339
theorem B9048185 : Blo 1881142 9048185 := bstep (se 2 (by rfl) ⟨3393069, by rfl⟩ : syracuseStep 9048185 = 6786139) B6786139
theorem B9040033 : Blo 1881142 9040033 := bstep (se 2 (by rfl) ⟨3390012, by rfl⟩ : syracuseStep 9040033 = 6780025) B6780025
theorem B2117839 : Blo 1881142 2117839 := bstep (se 1 (by rfl) ⟨1588379, by rfl⟩ : syracuseStep 2117839 = 3176759) B3176759
theorem B18084221 : Blo 1881142 18084221 := bstep (se 3 (by rfl) ⟨3390791, by rfl⟩ : syracuseStep 18084221 = 6781583) B6781583
theorem B9163255 : Blo 1881142 9163255 := bstep (se 1 (by rfl) ⟨6872441, by rfl⟩ : syracuseStep 9163255 = 13744883) B13744883
theorem B36655661 : Blo 1881142 36655661 := bstep (se 3 (by rfl) ⟨6872936, by rfl⟩ : syracuseStep 36655661 = 13745873) B13745873
theorem B16085627 : Blo 1881142 16085627 := bstep (se 1 (by rfl) ⟨12064220, by rfl⟩ : syracuseStep 16085627 = 24128441) B24128441
theorem B4764521 : Blo 1881142 4764521 := bstep (se 2 (by rfl) ⟨1786695, by rfl⟩ : syracuseStep 4764521 = 3573391) B3573391
theorem B2823239 : Blo 1881142 2823239 := bstep (se 1 (by rfl) ⟨2117429, by rfl⟩ : syracuseStep 2823239 = 4234859) B4234859
theorem B3175591 : Blo 1881142 3175591 := bstep (se 1 (by rfl) ⟨2381693, by rfl⟩ : syracuseStep 3175591 = 4763387) B4763387
theorem B16086275 : Blo 1881142 16086275 := bstep (se 1 (by rfl) ⟨12064706, by rfl⟩ : syracuseStep 16086275 = 24129413) B24129413
theorem B2823479 : Blo 1881142 2823479 := bstep (se 1 (by rfl) ⟨2117609, by rfl⟩ : syracuseStep 2823479 = 4235219) B4235219
theorem B2823551 : Blo 1881142 2823551 := bstep (se 1 (by rfl) ⟨2117663, by rfl⟩ : syracuseStep 2823551 = 4235327) B4235327
theorem B11015639 : Blo 1881142 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B40687069 : Blo 1881142 40687069 := bstep (se 3 (by rfl) ⟨7628825, by rfl⟩ : syracuseStep 40687069 = 15257651) B15257651
theorem B51516911 : Blo 1881142 51516911 := bstep (se 1 (by rfl) ⟨38637683, by rfl⟩ : syracuseStep 51516911 = 77275367) B77275367
theorem B4232699 : Blo 1881142 4232699 := bstep (se 1 (by rfl) ⟨3174524, by rfl⟩ : syracuseStep 4232699 = 6349049) B6349049
theorem B4232807 : Blo 1881142 4232807 := bstep (se 1 (by rfl) ⟨3174605, by rfl⟩ : syracuseStep 4232807 = 6349211) B6349211
theorem B1881703 : Blo 1881142 1881703 := bstep (se 1 (by rfl) ⟨1411277, by rfl⟩ : syracuseStep 1881703 = 2822555) B2822555
theorem B6354557 : Blo 1881142 6354557 := bstep (se 3 (by rfl) ⟨1191479, by rfl⟩ : syracuseStep 6354557 = 2382959) B2382959
theorem B45790859 : Blo 1881142 45790859 := bstep (se 1 (by rfl) ⟨34343144, by rfl⟩ : syracuseStep 45790859 = 68686289) B68686289
theorem B4765351 : Blo 1881142 4765351 := bstep (se 1 (by rfl) ⟨3574013, by rfl⟩ : syracuseStep 4765351 = 7148027) B7148027
theorem B24114955 : Blo 1881142 24114955 := bstep (se 1 (by rfl) ⟨18086216, by rfl⟩ : syracuseStep 24114955 = 36172433) B36172433
theorem B1881983 : Blo 1881142 1881983 := bstep (se 1 (by rfl) ⟨1411487, by rfl⟩ : syracuseStep 1881983 = 2822975) B2822975
theorem B1882363 : Blo 1881142 1882363 := bstep (se 1 (by rfl) ⟨1411772, by rfl⟩ : syracuseStep 1882363 = 2823545) B2823545
theorem B4765979 : Blo 1881142 4765979 := bstep (se 1 (by rfl) ⟨3574484, by rfl⟩ : syracuseStep 4765979 = 7148969) B7148969
theorem B20347301 : Blo 1881142 20347301 := bstep (se 4 (by rfl) ⟨1907559, by rfl⟩ : syracuseStep 20347301 = 3815119) B3815119
theorem B5085647 : Blo 1881142 5085647 := bstep (se 1 (by rfl) ⟨3814235, by rfl⟩ : syracuseStep 5085647 = 7628471) B7628471
theorem B10721767 : Blo 1881142 10721767 := bstep (se 1 (by rfl) ⟨8041325, by rfl⟩ : syracuseStep 10721767 = 16082651) B16082651
theorem B4520441 : Blo 1881142 4520441 := bstep (se 2 (by rfl) ⟨1695165, by rfl⟩ : syracuseStep 4520441 = 3390331) B3390331
theorem B1882727 : Blo 1881142 1882727 := bstep (se 1 (by rfl) ⟨1412045, by rfl⟩ : syracuseStep 1882727 = 2824091) B2824091
theorem B4233887 : Blo 1881142 4233887 := bstep (se 1 (by rfl) ⟨3175415, by rfl⟩ : syracuseStep 4233887 = 6350831) B6350831
theorem B4234031 : Blo 1881142 4234031 := bstep (se 1 (by rfl) ⟨3175523, by rfl⟩ : syracuseStep 4234031 = 6351047) B6351047
theorem B6110009 : Blo 1881142 6110009 := bstep (se 2 (by rfl) ⟨2291253, by rfl⟩ : syracuseStep 6110009 = 4582507) B4582507
theorem B8035433 : Blo 1881142 8035433 := bstep (se 2 (by rfl) ⟨3013287, by rfl⟩ : syracuseStep 8035433 = 6026575) B6026575
theorem B4234427 : Blo 1881142 4234427 := bstep (se 1 (by rfl) ⟨3175820, by rfl⟩ : syracuseStep 4234427 = 6351641) B6351641
theorem B10714477 : Blo 1881142 10714477 := bstep (se 3 (by rfl) ⟨2008964, by rfl⟩ : syracuseStep 10714477 = 4017929) B4017929
theorem B2383339 : Blo 1881142 2383339 := bstep (se 1 (by rfl) ⟨1787504, by rfl⟩ : syracuseStep 2383339 = 3575009) B3575009
theorem B22904383 : Blo 1881142 22904383 := bstep (se 1 (by rfl) ⟨17178287, by rfl⟩ : syracuseStep 22904383 = 34356575) B34356575
theorem B278593181 : Blo 1881142 278593181 := bstep (se 3 (by rfl) ⟨52236221, by rfl⟩ : syracuseStep 278593181 = 104472443) B104472443
theorem B13565879 : Blo 1881142 13565879 := bstep (se 1 (by rfl) ⟨10174409, by rfl⟩ : syracuseStep 13565879 = 20348819) B20348819
theorem B30949519 : Blo 1881142 30949519 := bstep (se 1 (by rfl) ⟨23212139, by rfl⟩ : syracuseStep 30949519 = 46424279) B46424279
theorem B24437107 : Blo 1881142 24437107 := bstep (se 1 (by rfl) ⟨18327830, by rfl⟩ : syracuseStep 24437107 = 36655661) B36655661
theorem B10723751 : Blo 1881142 10723751 := bstep (se 1 (by rfl) ⟨8042813, by rfl⟩ : syracuseStep 10723751 = 16085627) B16085627
theorem B14295689 : Blo 1881142 14295689 := bstep (se 2 (by rfl) ⟨5360883, by rfl⟩ : syracuseStep 14295689 = 10721767) B10721767
theorem B5505823 : Blo 1881142 5505823 := bstep (se 1 (by rfl) ⟨4129367, by rfl⟩ : syracuseStep 5505823 = 8258735) B8258735
theorem B10724183 : Blo 1881142 10724183 := bstep (se 1 (by rfl) ⟨8043137, by rfl⟩ : syracuseStep 10724183 = 16086275) B16086275
theorem B4236371 : Blo 1881142 4236371 := bstep (se 1 (by rfl) ⟨3177278, by rfl⟩ : syracuseStep 4236371 = 6354557) B6354557
theorem B6784553 : Blo 1881142 6784553 := bstep (se 2 (by rfl) ⟨2544207, by rfl⟩ : syracuseStep 6784553 = 5088415) B5088415
theorem B4073339 : Blo 1881142 4073339 := bstep (se 1 (by rfl) ⟨3055004, by rfl⟩ : syracuseStep 4073339 = 6110009) B6110009
theorem B54249425 : Blo 1881142 54249425 := bstep (se 2 (by rfl) ⟨20343534, by rfl⟩ : syracuseStep 54249425 = 40687069) B40687069
theorem B7145567 : Blo 1881142 7145567 := bstep (se 1 (by rfl) ⟨5359175, by rfl⟩ : syracuseStep 7145567 = 10718351) B10718351
theorem B21432599 : Blo 1881142 21432599 := bstep (se 1 (by rfl) ⟨16074449, by rfl⟩ : syracuseStep 21432599 = 32148899) B32148899
theorem B3574363 : Blo 1881142 3574363 := bstep (se 1 (by rfl) ⟨2680772, by rfl⟩ : syracuseStep 3574363 = 5361545) B5361545
theorem B2009819 : Blo 1881142 2009819 := bstep (se 1 (by rfl) ⟨1507364, by rfl⟩ : syracuseStep 2009819 = 3014729) B3014729
theorem B3574523 : Blo 1881142 3574523 := bstep (se 1 (by rfl) ⟨2680892, by rfl⟩ : syracuseStep 3574523 = 5361785) B5361785
theorem B6032123 : Blo 1881142 6032123 := bstep (se 1 (by rfl) ⟨4524092, by rfl⟩ : syracuseStep 6032123 = 9048185) B9048185
theorem B12053377 : Blo 1881142 12053377 := bstep (se 2 (by rfl) ⟨4520016, by rfl⟩ : syracuseStep 12053377 = 9040033) B9040033
theorem B12217673 : Blo 1881142 12217673 := bstep (se 2 (by rfl) ⟨4581627, by rfl⟩ : syracuseStep 12217673 = 9163255) B9163255
theorem B7343759 : Blo 1881142 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B34344607 : Blo 1881142 34344607 := bstep (se 1 (by rfl) ⟨25758455, by rfl⟩ : syracuseStep 34344607 = 51516911) B51516911
theorem B2821799 : Blo 1881142 2821799 := bstep (se 1 (by rfl) ⟨2116349, by rfl⟩ : syracuseStep 2821799 = 4232699) B4232699
theorem B2821871 : Blo 1881142 2821871 := bstep (se 1 (by rfl) ⟨2116403, by rfl⟩ : syracuseStep 2821871 = 4232807) B4232807
theorem B54259469 : Blo 1881142 54259469 := bstep (se 3 (by rfl) ⟨10173650, by rfl⟩ : syracuseStep 54259469 = 20347301) B20347301
theorem B30535487 : Blo 1881142 30535487 := bstep (se 1 (by rfl) ⟨22901615, by rfl⟩ : syracuseStep 30535487 = 45803231) B45803231
theorem B4829179 : Blo 1881142 4829179 := bstep (se 1 (by rfl) ⟨3621884, by rfl⟩ : syracuseStep 4829179 = 7243769) B7243769
theorem B10719377 : Blo 1881142 10719377 := bstep (se 2 (by rfl) ⟨4019766, by rfl⟩ : syracuseStep 10719377 = 8039533) B8039533
theorem B3174815 : Blo 1881142 3174815 := bstep (se 1 (by rfl) ⟨2381111, by rfl⟩ : syracuseStep 3174815 = 4762223) B4762223
theorem B2822591 : Blo 1881142 2822591 := bstep (se 1 (by rfl) ⟨2116943, by rfl⟩ : syracuseStep 2822591 = 4233887) B4233887
theorem B2822687 : Blo 1881142 2822687 := bstep (se 1 (by rfl) ⟨2117015, by rfl⟩ : syracuseStep 2822687 = 4234031) B4234031
theorem B4764329 : Blo 1881142 4764329 := bstep (se 2 (by rfl) ⟨1786623, by rfl⟩ : syracuseStep 4764329 = 3573247) B3573247
theorem B4764379 : Blo 1881142 4764379 := bstep (se 1 (by rfl) ⟨3573284, by rfl⟩ : syracuseStep 4764379 = 7146569) B7146569
theorem B2822951 : Blo 1881142 2822951 := bstep (se 1 (by rfl) ⟨2117213, by rfl⟩ : syracuseStep 2822951 = 4234427) B4234427
theorem B6353801 : Blo 1881142 6353801 := bstep (se 2 (by rfl) ⟨2382675, by rfl⟩ : syracuseStep 6353801 = 4765351) B4765351
theorem B7148513 : Blo 1881142 7148513 := bstep (se 2 (by rfl) ⟨2680692, by rfl⟩ : syracuseStep 7148513 = 5361385) B5361385
theorem B1881319 : Blo 1881142 1881319 := bstep (se 1 (by rfl) ⟨1410989, by rfl⟩ : syracuseStep 1881319 = 2821979) B2821979
theorem B6354287 : Blo 1881142 6354287 := bstep (se 1 (by rfl) ⟨4765715, by rfl⟩ : syracuseStep 6354287 = 9531431) B9531431
theorem B12056147 : Blo 1881142 12056147 := bstep (se 1 (by rfl) ⟨9042110, by rfl⟩ : syracuseStep 12056147 = 18084221) B18084221
theorem B2823785 : Blo 1881142 2823785 := bstep (se 2 (by rfl) ⟨1058919, by rfl⟩ : syracuseStep 2823785 = 2117839) B2117839
theorem B2823887 : Blo 1881142 2823887 := bstep (se 1 (by rfl) ⟨2117915, by rfl⟩ : syracuseStep 2823887 = 4235831) B4235831
theorem B9525113 : Blo 1881142 9525113 := bstep (se 2 (by rfl) ⟨3571917, by rfl⟩ : syracuseStep 9525113 = 7143835) B7143835
theorem B3176347 : Blo 1881142 3176347 := bstep (se 1 (by rfl) ⟨2382260, by rfl⟩ : syracuseStep 3176347 = 4764521) B4764521
theorem B1882159 : Blo 1881142 1882159 := bstep (se 1 (by rfl) ⟨1411619, by rfl⟩ : syracuseStep 1882159 = 2823239) B2823239
theorem B2824295 : Blo 1881142 2824295 := bstep (se 1 (by rfl) ⟨2118221, by rfl⟩ : syracuseStep 2824295 = 4236443) B4236443
theorem B2824319 : Blo 1881142 2824319 := bstep (se 1 (by rfl) ⟨2118239, by rfl⟩ : syracuseStep 2824319 = 4236479) B4236479
theorem B9525437 : Blo 1881142 9525437 := bstep (se 3 (by rfl) ⟨1786019, by rfl⟩ : syracuseStep 9525437 = 3572039) B3572039
theorem B1882319 : Blo 1881142 1882319 := bstep (se 1 (by rfl) ⟨1411739, by rfl⟩ : syracuseStep 1882319 = 2823479) B2823479
theorem B1882367 : Blo 1881142 1882367 := bstep (se 1 (by rfl) ⟨1411775, by rfl⟩ : syracuseStep 1882367 = 2823551) B2823551
theorem B4233671 : Blo 1881142 4233671 := bstep (se 1 (by rfl) ⟨3175253, by rfl⟩ : syracuseStep 4233671 = 6350507) B6350507
theorem B3177319 : Blo 1881142 3177319 := bstep (se 1 (by rfl) ⟨2382989, by rfl⟩ : syracuseStep 3177319 = 4765979) B4765979
theorem B4234121 : Blo 1881142 4234121 := bstep (se 2 (by rfl) ⟨1587795, by rfl⟩ : syracuseStep 4234121 = 3175591) B3175591
theorem B36690889 : Blo 1881142 36690889 := bstep (se 2 (by rfl) ⟨13759083, by rfl⟩ : syracuseStep 36690889 = 27518167) B27518167
theorem B3390431 : Blo 1881142 3390431 := bstep (se 1 (by rfl) ⟨2542823, by rfl⟩ : syracuseStep 3390431 = 5085647) B5085647
theorem B3013627 : Blo 1881142 3013627 := bstep (se 1 (by rfl) ⟨2260220, by rfl⟩ : syracuseStep 3013627 = 4520441) B4520441
theorem B122108957 : Blo 1881142 122108957 := bstep (se 3 (by rfl) ⟨22895429, by rfl⟩ : syracuseStep 122108957 = 45790859) B45790859
theorem B14285969 : Blo 1881142 14285969 := bstep (se 2 (by rfl) ⟨5357238, by rfl⟩ : syracuseStep 14285969 = 10714477) B10714477
theorem B3177785 : Blo 1881142 3177785 := bstep (se 2 (by rfl) ⟨1191669, by rfl⟩ : syracuseStep 3177785 = 2383339) B2383339
theorem B5356955 : Blo 1881142 5356955 := bstep (se 1 (by rfl) ⟨4017716, by rfl⟩ : syracuseStep 5356955 = 8035433) B8035433
theorem B30539177 : Blo 1881142 30539177 := bstep (se 2 (by rfl) ⟨11452191, by rfl⟩ : syracuseStep 30539177 = 22904383) B22904383
theorem B4234751 : Blo 1881142 4234751 := bstep (se 1 (by rfl) ⟨3176063, by rfl⟩ : syracuseStep 4234751 = 6352127) B6352127
theorem B32153273 : Blo 1881142 32153273 := bstep (se 2 (by rfl) ⟨12057477, by rfl⟩ : syracuseStep 32153273 = 24114955) B24114955
theorem B185728787 : Blo 1881142 185728787 := bstep (se 1 (by rfl) ⟨139296590, by rfl⟩ : syracuseStep 185728787 = 278593181) B278593181
theorem B2678665 : Blo 1881142 2678665 := bstep (se 2 (by rfl) ⟨1004499, by rfl⟩ : syracuseStep 2678665 = 2008999) B2008999
theorem B9043919 : Blo 1881142 9043919 := bstep (se 1 (by rfl) ⟨6782939, by rfl⟩ : syracuseStep 9043919 = 13565879) B13565879
theorem B4235867 : Blo 1881142 4235867 := bstep (se 1 (by rfl) ⟨3176900, by rfl⟩ : syracuseStep 4235867 = 6353801) B6353801
theorem B32580461 : Blo 1881142 32580461 := bstep (se 3 (by rfl) ⟨6108836, by rfl⟩ : syracuseStep 32580461 = 12217673) B12217673
theorem B4236191 : Blo 1881142 4236191 := bstep (se 1 (by rfl) ⟨3177143, by rfl⟩ : syracuseStep 4236191 = 6354287) B6354287
theorem B4523035 : Blo 1881142 4523035 := bstep (se 1 (by rfl) ⟨3392276, by rfl⟩ : syracuseStep 4523035 = 6784553) B6784553
theorem B8037431 : Blo 1881142 8037431 := bstep (se 1 (by rfl) ⟨6028073, by rfl⟩ : syracuseStep 8037431 = 12056147) B12056147
theorem B4236425 : Blo 1881142 4236425 := bstep (se 2 (by rfl) ⟨1588659, by rfl⟩ : syracuseStep 4236425 = 3177319) B3177319
theorem B6350075 : Blo 1881142 6350075 := bstep (se 1 (by rfl) ⟨4762556, by rfl⟩ : syracuseStep 6350075 = 9525113) B9525113
theorem B6350291 : Blo 1881142 6350291 := bstep (se 1 (by rfl) ⟨4762718, by rfl⟩ : syracuseStep 6350291 = 9525437) B9525437
theorem B14288399 : Blo 1881142 14288399 := bstep (se 1 (by rfl) ⟨10716299, by rfl⟩ : syracuseStep 14288399 = 21432599) B21432599
theorem B5359517 : Blo 1881142 5359517 := bstep (se 3 (by rfl) ⟨1004909, by rfl⟩ : syracuseStep 5359517 = 2009819) B2009819
theorem B81405971 : Blo 1881142 81405971 := bstep (se 1 (by rfl) ⟨61054478, by rfl⟩ : syracuseStep 81405971 = 122108957) B122108957
theorem B20359451 : Blo 1881142 20359451 := bstep (se 1 (by rfl) ⟨15269588, by rfl⟩ : syracuseStep 20359451 = 30539177) B30539177
theorem B7146251 : Blo 1881142 7146251 := bstep (se 1 (by rfl) ⟨5359688, by rfl⟩ : syracuseStep 7146251 = 10719377) B10719377
theorem B41266025 : Blo 1881142 41266025 := bstep (se 2 (by rfl) ⟨15474759, by rfl⟩ : syracuseStep 41266025 = 30949519) B30949519
theorem B2116543 : Blo 1881142 2116543 := bstep (se 1 (by rfl) ⟨1587407, by rfl⟩ : syracuseStep 2116543 = 3174815) B3174815
theorem B9530459 : Blo 1881142 9530459 := bstep (se 1 (by rfl) ⟨7147844, by rfl⟩ : syracuseStep 9530459 = 14295689) B14295689
theorem B32582809 : Blo 1881142 32582809 := bstep (se 2 (by rfl) ⟨12218553, by rfl⟩ : syracuseStep 32582809 = 24437107) B24437107
theorem B6352505 : Blo 1881142 6352505 := bstep (se 2 (by rfl) ⟨2382189, by rfl⟩ : syracuseStep 6352505 = 4764379) B4764379
theorem B4018169 : Blo 1881142 4018169 := bstep (se 2 (by rfl) ⟨1506813, by rfl⟩ : syracuseStep 4018169 = 3013627) B3013627
theorem B4763711 : Blo 1881142 4763711 := bstep (se 1 (by rfl) ⟨3572783, by rfl⟩ : syracuseStep 4763711 = 7145567) B7145567
theorem B29364389 : Blo 1881142 29364389 := bstep (se 4 (by rfl) ⟨2752911, by rfl⟩ : syracuseStep 29364389 = 5505823) B5505823
theorem B2822447 : Blo 1881142 2822447 := bstep (se 1 (by rfl) ⟨2116835, by rfl⟩ : syracuseStep 2822447 = 4233671) B4233671
theorem B6438905 : Blo 1881142 6438905 := bstep (se 2 (by rfl) ⟨2414589, by rfl⟩ : syracuseStep 6438905 = 4829179) B4829179
theorem B2822747 : Blo 1881142 2822747 := bstep (se 1 (by rfl) ⟨2117060, by rfl⟩ : syracuseStep 2822747 = 4234121) B4234121
theorem B9523979 : Blo 1881142 9523979 := bstep (se 1 (by rfl) ⟨7142984, by rfl⟩ : syracuseStep 9523979 = 14285969) B14285969
theorem B2118523 : Blo 1881142 2118523 := bstep (se 1 (by rfl) ⟨1588892, by rfl⟩ : syracuseStep 2118523 = 3177785) B3177785
theorem B2823167 : Blo 1881142 2823167 := bstep (se 1 (by rfl) ⟨2117375, by rfl⟩ : syracuseStep 2823167 = 4234751) B4234751
theorem B4895839 : Blo 1881142 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B1881199 : Blo 1881142 1881199 := bstep (se 1 (by rfl) ⟨1410899, by rfl⟩ : syracuseStep 1881199 = 2821799) B2821799
theorem B21435515 : Blo 1881142 21435515 := bstep (se 1 (by rfl) ⟨16076636, by rfl⟩ : syracuseStep 21435515 = 32153273) B32153273
theorem B1881247 : Blo 1881142 1881247 := bstep (se 1 (by rfl) ⟨1410935, by rfl⟩ : syracuseStep 1881247 = 2821871) B2821871
theorem B36172979 : Blo 1881142 36172979 := bstep (se 1 (by rfl) ⟨27129734, by rfl⟩ : syracuseStep 36172979 = 54259469) B54259469
theorem B123819191 : Blo 1881142 123819191 := bstep (se 1 (by rfl) ⟨92864393, by rfl⟩ : syracuseStep 123819191 = 185728787) B185728787
theorem B9041149 : Blo 1881142 9041149 := bstep (se 3 (by rfl) ⟨1695215, by rfl⟩ : syracuseStep 9041149 = 3390431) B3390431
theorem B7149167 : Blo 1881142 7149167 := bstep (se 1 (by rfl) ⟨5361875, by rfl⟩ : syracuseStep 7149167 = 10723751) B10723751
theorem B1881727 : Blo 1881142 1881727 := bstep (se 1 (by rfl) ⟨1411295, by rfl⟩ : syracuseStep 1881727 = 2822591) B2822591
theorem B1881791 : Blo 1881142 1881791 := bstep (se 1 (by rfl) ⟨1411343, by rfl⟩ : syracuseStep 1881791 = 2822687) B2822687
theorem B3176219 : Blo 1881142 3176219 := bstep (se 1 (by rfl) ⟨2382164, by rfl⟩ : syracuseStep 3176219 = 4764329) B4764329
theorem B1881967 : Blo 1881142 1881967 := bstep (se 1 (by rfl) ⟨1411475, by rfl⟩ : syracuseStep 1881967 = 2822951) B2822951
theorem B7149455 : Blo 1881142 7149455 := bstep (se 1 (by rfl) ⟨5362091, by rfl⟩ : syracuseStep 7149455 = 10724183) B10724183
theorem B4765675 : Blo 1881142 4765675 := bstep (se 1 (by rfl) ⟨3574256, by rfl⟩ : syracuseStep 4765675 = 7148513) B7148513
theorem B2824247 : Blo 1881142 2824247 := bstep (se 1 (by rfl) ⟨2118185, by rfl⟩ : syracuseStep 2824247 = 4236371) B4236371
theorem B4765817 : Blo 1881142 4765817 := bstep (se 2 (by rfl) ⟨1787181, by rfl⟩ : syracuseStep 4765817 = 3574363) B3574363
theorem B1882523 : Blo 1881142 1882523 := bstep (se 1 (by rfl) ⟨1411892, by rfl⟩ : syracuseStep 1882523 = 2823785) B2823785
theorem B1882591 : Blo 1881142 1882591 := bstep (se 1 (by rfl) ⟨1411943, by rfl⟩ : syracuseStep 1882591 = 2823887) B2823887
theorem B16071169 : Blo 1881142 16071169 := bstep (se 2 (by rfl) ⟨6026688, by rfl⟩ : syracuseStep 16071169 = 12053377) B12053377
theorem B48921185 : Blo 1881142 48921185 := bstep (se 2 (by rfl) ⟨18345444, by rfl⟩ : syracuseStep 48921185 = 36690889) B36690889
theorem B36166283 : Blo 1881142 36166283 := bstep (se 1 (by rfl) ⟨27124712, by rfl⟩ : syracuseStep 36166283 = 54249425) B54249425
theorem B1882863 : Blo 1881142 1882863 := bstep (se 1 (by rfl) ⟨1412147, by rfl⟩ : syracuseStep 1882863 = 2824295) B2824295
theorem B1882879 : Blo 1881142 1882879 := bstep (se 1 (by rfl) ⟨1412159, by rfl⟩ : syracuseStep 1882879 = 2824319) B2824319
theorem B2383015 : Blo 1881142 2383015 := bstep (se 1 (by rfl) ⟨1787261, by rfl⟩ : syracuseStep 2383015 = 3574523) B3574523
theorem B4021415 : Blo 1881142 4021415 := bstep (se 1 (by rfl) ⟨3016061, by rfl⟩ : syracuseStep 4021415 = 6032123) B6032123
theorem B45792809 : Blo 1881142 45792809 := bstep (se 2 (by rfl) ⟨17172303, by rfl⟩ : syracuseStep 45792809 = 34344607) B34344607
theorem B3571303 : Blo 1881142 3571303 := bstep (se 1 (by rfl) ⟨2678477, by rfl⟩ : syracuseStep 3571303 = 5356955) B5356955
theorem B10862237 : Blo 1881142 10862237 := bstep (se 3 (by rfl) ⟨2036669, by rfl⟩ : syracuseStep 10862237 = 4073339) B4073339
theorem B3571553 : Blo 1881142 3571553 := bstep (se 2 (by rfl) ⟨1339332, by rfl⟩ : syracuseStep 3571553 = 2678665) B2678665
theorem B4235129 : Blo 1881142 4235129 := bstep (se 2 (by rfl) ⟨1588173, by rfl⟩ : syracuseStep 4235129 = 3176347) B3176347
theorem B20356991 : Blo 1881142 20356991 := bstep (se 1 (by rfl) ⟨15267743, by rfl⟩ : syracuseStep 20356991 = 30535487) B30535487
theorem B6029279 : Blo 1881142 6029279 := bstep (se 1 (by rfl) ⟨4521959, by rfl⟩ : syracuseStep 6029279 = 9043919) B9043919
theorem B6349319 : Blo 1881142 6349319 := bstep (se 1 (by rfl) ⟨4761989, by rfl⟩ : syracuseStep 6349319 = 9523979) B9523979
theorem B5358287 : Blo 1881142 5358287 := bstep (se 1 (by rfl) ⟨4018715, by rfl⟩ : syracuseStep 5358287 = 8037431) B8037431
theorem B3573011 : Blo 1881142 3573011 := bstep (se 1 (by rfl) ⟨2679758, by rfl⟩ : syracuseStep 3573011 = 5359517) B5359517
theorem B6030713 : Blo 1881142 6030713 := bstep (se 2 (by rfl) ⟨2261517, by rfl⟩ : syracuseStep 6030713 = 4523035) B4523035
theorem B43443745 : Blo 1881142 43443745 := bstep (se 2 (by rfl) ⟨16291404, by rfl⟩ : syracuseStep 43443745 = 32582809) B32582809
theorem B32614123 : Blo 1881142 32614123 := bstep (se 1 (by rfl) ⟨24460592, by rfl⟩ : syracuseStep 32614123 = 48921185) B48921185
theorem B24110855 : Blo 1881142 24110855 := bstep (se 1 (by rfl) ⟨18083141, by rfl⟩ : syracuseStep 24110855 = 36166283) B36166283
theorem B27510683 : Blo 1881142 27510683 := bstep (se 1 (by rfl) ⟨20633012, by rfl⟩ : syracuseStep 27510683 = 41266025) B41266025
theorem B2680943 : Blo 1881142 2680943 := bstep (se 1 (by rfl) ⟨2010707, by rfl⟩ : syracuseStep 2680943 = 4021415) B4021415
theorem B4761737 : Blo 1881142 4761737 := bstep (se 2 (by rfl) ⟨1785651, by rfl⟩ : syracuseStep 4761737 = 3571303) B3571303
theorem B4292603 : Blo 1881142 4292603 := bstep (se 1 (by rfl) ⟨3219452, by rfl⟩ : syracuseStep 4292603 = 6438905) B6438905
theorem B21720307 : Blo 1881142 21720307 := bstep (se 1 (by rfl) ⟨16290230, by rfl⟩ : syracuseStep 21720307 = 32580461) B32580461
theorem B14290343 : Blo 1881142 14290343 := bstep (se 1 (by rfl) ⟨10717757, by rfl⟩ : syracuseStep 14290343 = 21435515) B21435515
theorem B82546127 : Blo 1881142 82546127 := bstep (se 1 (by rfl) ⟨61909595, by rfl⟩ : syracuseStep 82546127 = 123819191) B123819191
theorem B2117479 : Blo 1881142 2117479 := bstep (se 1 (by rfl) ⟨1588109, by rfl⟩ : syracuseStep 2117479 = 3176219) B3176219
theorem B2822057 : Blo 1881142 2822057 := bstep (se 2 (by rfl) ⟨1058271, by rfl⟩ : syracuseStep 2822057 = 2116543) B2116543
theorem B12054865 : Blo 1881142 12054865 := bstep (se 2 (by rfl) ⟨4520574, by rfl⟩ : syracuseStep 12054865 = 9041149) B9041149
theorem B4764167 : Blo 1881142 4764167 := bstep (se 1 (by rfl) ⟨3573125, by rfl⟩ : syracuseStep 4764167 = 7146251) B7146251
theorem B6353639 : Blo 1881142 6353639 := bstep (se 1 (by rfl) ⟨4765229, by rfl⟩ : syracuseStep 6353639 = 9530459) B9530459
theorem B9524141 : Blo 1881142 9524141 := bstep (se 3 (by rfl) ⟨1785776, by rfl⟩ : syracuseStep 9524141 = 3571553) B3571553
theorem B30528539 : Blo 1881142 30528539 := bstep (se 1 (by rfl) ⟨22896404, by rfl⟩ : syracuseStep 30528539 = 45792809) B45792809
theorem B2823419 : Blo 1881142 2823419 := bstep (se 1 (by rfl) ⟨2117564, by rfl⟩ : syracuseStep 2823419 = 4235129) B4235129
theorem B13571327 : Blo 1881142 13571327 := bstep (se 1 (by rfl) ⟨10178495, by rfl⟩ : syracuseStep 13571327 = 20356991) B20356991
theorem B6354233 : Blo 1881142 6354233 := bstep (se 2 (by rfl) ⟨2382837, by rfl⟩ : syracuseStep 6354233 = 4765675) B4765675
theorem B4019519 : Blo 1881142 4019519 := bstep (se 1 (by rfl) ⟨3014639, by rfl⟩ : syracuseStep 4019519 = 6029279) B6029279
theorem B3175807 : Blo 1881142 3175807 := bstep (se 1 (by rfl) ⟨2381855, by rfl⟩ : syracuseStep 3175807 = 4763711) B4763711
theorem B19576259 : Blo 1881142 19576259 := bstep (se 1 (by rfl) ⟨14682194, by rfl⟩ : syracuseStep 19576259 = 29364389) B29364389
theorem B1881631 : Blo 1881142 1881631 := bstep (se 1 (by rfl) ⟨1411223, by rfl⟩ : syracuseStep 1881631 = 2822447) B2822447
theorem B1881831 : Blo 1881142 1881831 := bstep (se 1 (by rfl) ⟨1411373, by rfl⟩ : syracuseStep 1881831 = 2822747) B2822747
theorem B2823911 : Blo 1881142 2823911 := bstep (se 1 (by rfl) ⟨2117933, by rfl⟩ : syracuseStep 2823911 = 4235867) B4235867
theorem B2824127 : Blo 1881142 2824127 := bstep (se 1 (by rfl) ⟨2118095, by rfl⟩ : syracuseStep 2824127 = 4236191) B4236191
theorem B1882111 : Blo 1881142 1882111 := bstep (se 1 (by rfl) ⟨1411583, by rfl⟩ : syracuseStep 1882111 = 2823167) B2823167
theorem B21428225 : Blo 1881142 21428225 := bstep (se 2 (by rfl) ⟨8035584, by rfl⟩ : syracuseStep 21428225 = 16071169) B16071169
theorem B2824283 : Blo 1881142 2824283 := bstep (se 1 (by rfl) ⟨2118212, by rfl⟩ : syracuseStep 2824283 = 4236425) B4236425
theorem B24115319 : Blo 1881142 24115319 := bstep (se 1 (by rfl) ⟨18086489, by rfl⟩ : syracuseStep 24115319 = 36172979) B36172979
theorem B4233383 : Blo 1881142 4233383 := bstep (se 1 (by rfl) ⟨3175037, by rfl⟩ : syracuseStep 4233383 = 6350075) B6350075
theorem B4233527 : Blo 1881142 4233527 := bstep (se 1 (by rfl) ⟨3175145, by rfl⟩ : syracuseStep 4233527 = 6350291) B6350291
theorem B9525599 : Blo 1881142 9525599 := bstep (se 1 (by rfl) ⟨7144199, by rfl⟩ : syracuseStep 9525599 = 14288399) B14288399
theorem B4766111 : Blo 1881142 4766111 := bstep (se 1 (by rfl) ⟨3574583, by rfl⟩ : syracuseStep 4766111 = 7149167) B7149167
theorem B2824697 : Blo 1881142 2824697 := bstep (se 2 (by rfl) ⟨1059261, by rfl⟩ : syracuseStep 2824697 = 2118523) B2118523
theorem B4766303 : Blo 1881142 4766303 := bstep (se 1 (by rfl) ⟨3574727, by rfl⟩ : syracuseStep 4766303 = 7149455) B7149455
theorem B54270647 : Blo 1881142 54270647 := bstep (se 1 (by rfl) ⟨40702985, by rfl⟩ : syracuseStep 54270647 = 81405971) B81405971
theorem B1882831 : Blo 1881142 1882831 := bstep (se 1 (by rfl) ⟨1412123, by rfl⟩ : syracuseStep 1882831 = 2824247) B2824247
theorem B3177211 : Blo 1881142 3177211 := bstep (se 1 (by rfl) ⟨2382908, by rfl⟩ : syracuseStep 3177211 = 4765817) B4765817
theorem B6527785 : Blo 1881142 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B13572967 : Blo 1881142 13572967 := bstep (se 1 (by rfl) ⟨10179725, by rfl⟩ : syracuseStep 13572967 = 20359451) B20359451
theorem B3177353 : Blo 1881142 3177353 := bstep (se 2 (by rfl) ⟨1191507, by rfl⟩ : syracuseStep 3177353 = 2383015) B2383015
theorem B4235003 : Blo 1881142 4235003 := bstep (se 1 (by rfl) ⟨3176252, by rfl⟩ : syracuseStep 4235003 = 6352505) B6352505
theorem B7241491 : Blo 1881142 7241491 := bstep (se 1 (by rfl) ⟨5431118, by rfl⟩ : syracuseStep 7241491 = 10862237) B10862237
theorem B2678779 : Blo 1881142 2678779 := bstep (se 1 (by rfl) ⟨2009084, by rfl⟩ : syracuseStep 2678779 = 4018169) B4018169
theorem B16073153 : Blo 1881142 16073153 := bstep (se 2 (by rfl) ⟨6027432, by rfl⟩ : syracuseStep 16073153 = 12054865) B12054865
theorem B3572191 : Blo 1881142 3572191 := bstep (se 1 (by rfl) ⟨2679143, by rfl⟩ : syracuseStep 3572191 = 5358287) B5358287
theorem B4235759 : Blo 1881142 4235759 := bstep (se 1 (by rfl) ⟨3176819, by rfl⟩ : syracuseStep 4235759 = 6353639) B6353639
theorem B6349427 : Blo 1881142 6349427 := bstep (se 1 (by rfl) ⟨4762070, by rfl⟩ : syracuseStep 6349427 = 9524141) B9524141
theorem B9528029 : Blo 1881142 9528029 := bstep (se 3 (by rfl) ⟨1786505, by rfl⟩ : syracuseStep 9528029 = 3573011) B3573011
theorem B4236155 : Blo 1881142 4236155 := bstep (se 1 (by rfl) ⟨3177116, by rfl⟩ : syracuseStep 4236155 = 6354233) B6354233
theorem B2679679 : Blo 1881142 2679679 := bstep (se 1 (by rfl) ⟨2009759, by rfl⟩ : syracuseStep 2679679 = 4019519) B4019519
theorem B13050839 : Blo 1881142 13050839 := bstep (se 1 (by rfl) ⟨9788129, by rfl⟩ : syracuseStep 13050839 = 19576259) B19576259
theorem B16081901 : Blo 1881142 16081901 := bstep (se 3 (by rfl) ⟨3015356, by rfl⟩ : syracuseStep 16081901 = 6030713) B6030713
theorem B4236281 : Blo 1881142 4236281 := bstep (se 2 (by rfl) ⟨1588605, by rfl⟩ : syracuseStep 4236281 = 3177211) B3177211
theorem B18097289 : Blo 1881142 18097289 := bstep (se 2 (by rfl) ⟨6786483, by rfl⟩ : syracuseStep 18097289 = 13572967) B13572967
theorem B16073903 : Blo 1881142 16073903 := bstep (se 1 (by rfl) ⟨12055427, by rfl⟩ : syracuseStep 16073903 = 24110855) B24110855
theorem B6350399 : Blo 1881142 6350399 := bstep (se 1 (by rfl) ⟨4762799, by rfl⟩ : syracuseStep 6350399 = 9525599) B9525599
theorem B293447285 : Blo 1881142 293447285 := bstep (se 5 (by rfl) ⟨13755341, by rfl⟩ : syracuseStep 293447285 = 27510683) B27510683
theorem B28960409 : Blo 1881142 28960409 := bstep (se 2 (by rfl) ⟨10860153, by rfl⟩ : syracuseStep 28960409 = 21720307) B21720307
theorem B43485497 : Blo 1881142 43485497 := bstep (se 2 (by rfl) ⟨16307061, by rfl⟩ : syracuseStep 43485497 = 32614123) B32614123
theorem B2861735 : Blo 1881142 2861735 := bstep (se 1 (by rfl) ⟨2146301, by rfl⟩ : syracuseStep 2861735 = 4292603) B4292603
theorem B20352359 : Blo 1881142 20352359 := bstep (se 1 (by rfl) ⟨15264269, by rfl⟩ : syracuseStep 20352359 = 30528539) B30528539
theorem B9047551 : Blo 1881142 9047551 := bstep (se 1 (by rfl) ⟨6785663, by rfl⟩ : syracuseStep 9047551 = 13571327) B13571327
theorem B8703713 : Blo 1881142 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B16076879 : Blo 1881142 16076879 := bstep (se 1 (by rfl) ⟨12057659, by rfl⟩ : syracuseStep 16076879 = 24115319) B24115319
theorem B3174491 : Blo 1881142 3174491 := bstep (se 1 (by rfl) ⟨2380868, by rfl⟩ : syracuseStep 3174491 = 4761737) B4761737
theorem B2822255 : Blo 1881142 2822255 := bstep (se 1 (by rfl) ⟨2116691, by rfl⟩ : syracuseStep 2822255 = 4233383) B4233383
theorem B2822351 : Blo 1881142 2822351 := bstep (se 1 (by rfl) ⟨2116763, by rfl⟩ : syracuseStep 2822351 = 4233527) B4233527
theorem B36180431 : Blo 1881142 36180431 := bstep (se 1 (by rfl) ⟨27135323, by rfl⟩ : syracuseStep 36180431 = 54270647) B54270647
theorem B2118235 : Blo 1881142 2118235 := bstep (se 1 (by rfl) ⟨1588676, by rfl⟩ : syracuseStep 2118235 = 3177353) B3177353
theorem B55030751 : Blo 1881142 55030751 := bstep (se 1 (by rfl) ⟨41273063, by rfl⟩ : syracuseStep 55030751 = 82546127) B82546127
theorem B9655321 : Blo 1881142 9655321 := bstep (se 2 (by rfl) ⟨3620745, by rfl⟩ : syracuseStep 9655321 = 7241491) B7241491
theorem B2823305 : Blo 1881142 2823305 := bstep (se 2 (by rfl) ⟨1058739, by rfl⟩ : syracuseStep 2823305 = 2117479) B2117479
theorem B2823335 : Blo 1881142 2823335 := bstep (se 1 (by rfl) ⟨2117501, by rfl⟩ : syracuseStep 2823335 = 4235003) B4235003
theorem B1881371 : Blo 1881142 1881371 := bstep (se 1 (by rfl) ⟨1411028, by rfl⟩ : syracuseStep 1881371 = 2822057) B2822057
theorem B231699973 : Blo 1881142 231699973 := bstep (se 4 (by rfl) ⟨21721872, by rfl⟩ : syracuseStep 231699973 = 43443745) B43443745
theorem B7149181 : Blo 1881142 7149181 := bstep (se 3 (by rfl) ⟨1340471, by rfl⟩ : syracuseStep 7149181 = 2680943) B2680943
theorem B4232879 : Blo 1881142 4232879 := bstep (se 1 (by rfl) ⟨3174659, by rfl⟩ : syracuseStep 4232879 = 6349319) B6349319
theorem B3176111 : Blo 1881142 3176111 := bstep (se 1 (by rfl) ⟨2382083, by rfl⟩ : syracuseStep 3176111 = 4764167) B4764167
theorem B1882279 : Blo 1881142 1882279 := bstep (se 1 (by rfl) ⟨1411709, by rfl⟩ : syracuseStep 1882279 = 2823419) B2823419
theorem B1882607 : Blo 1881142 1882607 := bstep (se 1 (by rfl) ⟨1411955, by rfl⟩ : syracuseStep 1882607 = 2823911) B2823911
theorem B1882751 : Blo 1881142 1882751 := bstep (se 1 (by rfl) ⟨1412063, by rfl⟩ : syracuseStep 1882751 = 2824127) B2824127
theorem B14285483 : Blo 1881142 14285483 := bstep (se 1 (by rfl) ⟨10714112, by rfl⟩ : syracuseStep 14285483 = 21428225) B21428225
theorem B1882855 : Blo 1881142 1882855 := bstep (se 1 (by rfl) ⟨1412141, by rfl⟩ : syracuseStep 1882855 = 2824283) B2824283
theorem B3177407 : Blo 1881142 3177407 := bstep (se 1 (by rfl) ⟨2383055, by rfl⟩ : syracuseStep 3177407 = 4766111) B4766111
theorem B1883131 : Blo 1881142 1883131 := bstep (se 1 (by rfl) ⟨1412348, by rfl⟩ : syracuseStep 1883131 = 2824697) B2824697
theorem B3177535 : Blo 1881142 3177535 := bstep (se 1 (by rfl) ⟨2383151, by rfl⟩ : syracuseStep 3177535 = 4766303) B4766303
theorem B4234409 : Blo 1881142 4234409 := bstep (se 2 (by rfl) ⟨1587903, by rfl⟩ : syracuseStep 4234409 = 3175807) B3175807
theorem B9526895 : Blo 1881142 9526895 := bstep (se 1 (by rfl) ⟨7145171, by rfl⟩ : syracuseStep 9526895 = 14290343) B14290343
theorem B3571705 : Blo 1881142 3571705 := bstep (se 2 (by rfl) ⟨1339389, by rfl⟩ : syracuseStep 3571705 = 2678779) B2678779
theorem B10715435 : Blo 1881142 10715435 := bstep (se 1 (by rfl) ⟨8036576, by rfl⟩ : syracuseStep 10715435 = 16073153) B16073153
theorem B10715935 : Blo 1881142 10715935 := bstep (se 1 (by rfl) ⟨8036951, by rfl⟩ : syracuseStep 10715935 = 16073903) B16073903
theorem B3572905 : Blo 1881142 3572905 := bstep (se 2 (by rfl) ⟨1339839, by rfl⟩ : syracuseStep 3572905 = 2679679) B2679679
theorem B4236713 : Blo 1881142 4236713 := bstep (se 2 (by rfl) ⟨1588767, by rfl⟩ : syracuseStep 4236713 = 3177535) B3177535
theorem B23209901 : Blo 1881142 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B13568239 : Blo 1881142 13568239 := bstep (se 1 (by rfl) ⟨10176179, by rfl⟩ : syracuseStep 13568239 = 20352359) B20352359
theorem B6351263 : Blo 1881142 6351263 := bstep (se 1 (by rfl) ⟨4763447, by rfl⟩ : syracuseStep 6351263 = 9526895) B9526895
theorem B34802237 : Blo 1881142 34802237 := bstep (se 3 (by rfl) ⟨6525419, by rfl⟩ : syracuseStep 34802237 = 13050839) B13050839
theorem B4762273 : Blo 1881142 4762273 := bstep (se 2 (by rfl) ⟨1785852, by rfl⟩ : syracuseStep 4762273 = 3571705) B3571705
theorem B10717919 : Blo 1881142 10717919 := bstep (se 1 (by rfl) ⟨8038439, by rfl⟩ : syracuseStep 10717919 = 16076879) B16076879
theorem B2116327 : Blo 1881142 2116327 := bstep (se 1 (by rfl) ⟨1587245, by rfl⟩ : syracuseStep 2116327 = 3174491) B3174491
theorem B24120287 : Blo 1881142 24120287 := bstep (se 1 (by rfl) ⟨18090215, by rfl⟩ : syracuseStep 24120287 = 36180431) B36180431
theorem B6352019 : Blo 1881142 6352019 := bstep (se 1 (by rfl) ⟨4764014, by rfl⟩ : syracuseStep 6352019 = 9528029) B9528029
theorem B4762921 : Blo 1881142 4762921 := bstep (se 2 (by rfl) ⟨1786095, by rfl⟩ : syracuseStep 4762921 = 3572191) B3572191
theorem B36687167 : Blo 1881142 36687167 := bstep (se 1 (by rfl) ⟨27515375, by rfl⟩ : syracuseStep 36687167 = 55030751) B55030751
theorem B2821919 : Blo 1881142 2821919 := bstep (se 1 (by rfl) ⟨2116439, by rfl⟩ : syracuseStep 2821919 = 4232879) B4232879
theorem B2117407 : Blo 1881142 2117407 := bstep (se 1 (by rfl) ⟨1588055, by rfl⟩ : syracuseStep 2117407 = 3176111) B3176111
theorem B12873761 : Blo 1881142 12873761 := bstep (se 2 (by rfl) ⟨4827660, by rfl⟩ : syracuseStep 12873761 = 9655321) B9655321
theorem B7631293 : Blo 1881142 7631293 := bstep (se 3 (by rfl) ⟨1430867, by rfl⟩ : syracuseStep 7631293 = 2861735) B2861735
theorem B9523655 : Blo 1881142 9523655 := bstep (se 1 (by rfl) ⟨7142741, by rfl⟩ : syracuseStep 9523655 = 14285483) B14285483
theorem B2118271 : Blo 1881142 2118271 := bstep (se 1 (by rfl) ⟨1588703, by rfl⟩ : syracuseStep 2118271 = 3177407) B3177407
theorem B12063401 : Blo 1881142 12063401 := bstep (se 2 (by rfl) ⟨4523775, by rfl⟩ : syracuseStep 12063401 = 9047551) B9047551
theorem B308933297 : Blo 1881142 308933297 := bstep (se 2 (by rfl) ⟨115849986, by rfl⟩ : syracuseStep 308933297 = 231699973) B231699973
theorem B2822939 : Blo 1881142 2822939 := bstep (se 1 (by rfl) ⟨2117204, by rfl⟩ : syracuseStep 2822939 = 4234409) B4234409
theorem B9532241 : Blo 1881142 9532241 := bstep (se 2 (by rfl) ⟨3574590, by rfl⟩ : syracuseStep 9532241 = 7149181) B7149181
theorem B1881503 : Blo 1881142 1881503 := bstep (se 1 (by rfl) ⟨1411127, by rfl⟩ : syracuseStep 1881503 = 2822255) B2822255
theorem B1881567 : Blo 1881142 1881567 := bstep (se 1 (by rfl) ⟨1411175, by rfl⟩ : syracuseStep 1881567 = 2822351) B2822351
theorem B2823839 : Blo 1881142 2823839 := bstep (se 1 (by rfl) ⟨2117879, by rfl⟩ : syracuseStep 2823839 = 4235759) B4235759
theorem B4232951 : Blo 1881142 4232951 := bstep (se 1 (by rfl) ⟨3174713, by rfl⟩ : syracuseStep 4232951 = 6349427) B6349427
theorem B2824103 : Blo 1881142 2824103 := bstep (se 1 (by rfl) ⟨2118077, by rfl⟩ : syracuseStep 2824103 = 4236155) B4236155
theorem B10721267 : Blo 1881142 10721267 := bstep (se 1 (by rfl) ⟨8040950, by rfl⟩ : syracuseStep 10721267 = 16081901) B16081901
theorem B2824187 : Blo 1881142 2824187 := bstep (se 1 (by rfl) ⟨2118140, by rfl⟩ : syracuseStep 2824187 = 4236281) B4236281
theorem B1882203 : Blo 1881142 1882203 := bstep (se 1 (by rfl) ⟨1411652, by rfl⟩ : syracuseStep 1882203 = 2823305) B2823305
theorem B12064859 : Blo 1881142 12064859 := bstep (se 1 (by rfl) ⟨9048644, by rfl⟩ : syracuseStep 12064859 = 18097289) B18097289
theorem B1882223 : Blo 1881142 1882223 := bstep (se 1 (by rfl) ⟨1411667, by rfl⟩ : syracuseStep 1882223 = 2823335) B2823335
theorem B2824313 : Blo 1881142 2824313 := bstep (se 2 (by rfl) ⟨1059117, by rfl⟩ : syracuseStep 2824313 = 2118235) B2118235
theorem B4233599 : Blo 1881142 4233599 := bstep (se 1 (by rfl) ⟨3175199, by rfl⟩ : syracuseStep 4233599 = 6350399) B6350399
theorem B195631523 : Blo 1881142 195631523 := bstep (se 1 (by rfl) ⟨146723642, by rfl⟩ : syracuseStep 195631523 = 293447285) B293447285
theorem B19306939 : Blo 1881142 19306939 := bstep (se 1 (by rfl) ⟨14480204, by rfl⟩ : syracuseStep 19306939 = 28960409) B28960409
theorem B28990331 : Blo 1881142 28990331 := bstep (se 1 (by rfl) ⟨21742748, by rfl⟩ : syracuseStep 28990331 = 43485497) B43485497
theorem B7143623 : Blo 1881142 7143623 := bstep (se 1 (by rfl) ⟨5357717, by rfl⟩ : syracuseStep 7143623 = 10715435) B10715435
theorem B6349103 : Blo 1881142 6349103 := bstep (se 1 (by rfl) ⟨4761827, by rfl⟩ : syracuseStep 6349103 = 9523655) B9523655
theorem B205955531 : Blo 1881142 205955531 := bstep (se 1 (by rfl) ⟨154466648, by rfl⟩ : syracuseStep 205955531 = 308933297) B308933297
theorem B10175057 : Blo 1881142 10175057 := bstep (se 2 (by rfl) ⟨3815646, by rfl⟩ : syracuseStep 10175057 = 7631293) B7631293
theorem B6349697 : Blo 1881142 6349697 := bstep (se 2 (by rfl) ⟨2381136, by rfl⟩ : syracuseStep 6349697 = 4762273) B4762273
theorem B14287913 : Blo 1881142 14287913 := bstep (se 2 (by rfl) ⟨5357967, by rfl⟩ : syracuseStep 14287913 = 10715935) B10715935
theorem B23201491 : Blo 1881142 23201491 := bstep (se 1 (by rfl) ⟨17401118, by rfl⟩ : syracuseStep 23201491 = 34802237) B34802237
theorem B6350561 : Blo 1881142 6350561 := bstep (se 2 (by rfl) ⟨2381460, by rfl⟩ : syracuseStep 6350561 = 4762921) B4762921
theorem B7145279 : Blo 1881142 7145279 := bstep (se 1 (by rfl) ⟨5358959, by rfl⟩ : syracuseStep 7145279 = 10717919) B10717919
theorem B19326887 : Blo 1881142 19326887 := bstep (se 1 (by rfl) ⟨14495165, by rfl⟩ : syracuseStep 19326887 = 28990331) B28990331
theorem B18090985 : Blo 1881142 18090985 := bstep (se 2 (by rfl) ⟨6784119, by rfl⟩ : syracuseStep 18090985 = 13568239) B13568239
theorem B25742585 : Blo 1881142 25742585 := bstep (se 2 (by rfl) ⟨9653469, by rfl⟩ : syracuseStep 25742585 = 19306939) B19306939
theorem B2821769 : Blo 1881142 2821769 := bstep (se 2 (by rfl) ⟨1058163, by rfl⟩ : syracuseStep 2821769 = 2116327) B2116327
theorem B2821967 : Blo 1881142 2821967 := bstep (se 1 (by rfl) ⟨2116475, by rfl⟩ : syracuseStep 2821967 = 4232951) B4232951
theorem B7147511 : Blo 1881142 7147511 := bstep (se 1 (by rfl) ⟨5360633, by rfl⟩ : syracuseStep 7147511 = 10721267) B10721267
theorem B4763873 : Blo 1881142 4763873 := bstep (se 2 (by rfl) ⟨1786452, by rfl⟩ : syracuseStep 4763873 = 3572905) B3572905
theorem B2822399 : Blo 1881142 2822399 := bstep (se 1 (by rfl) ⟨2116799, by rfl⟩ : syracuseStep 2822399 = 4233599) B4233599
theorem B130421015 : Blo 1881142 130421015 := bstep (se 1 (by rfl) ⟨97815761, by rfl⟩ : syracuseStep 130421015 = 195631523) B195631523
theorem B24458111 : Blo 1881142 24458111 := bstep (se 1 (by rfl) ⟨18343583, by rfl⟩ : syracuseStep 24458111 = 36687167) B36687167
theorem B2823209 : Blo 1881142 2823209 := bstep (se 2 (by rfl) ⟨1058703, by rfl⟩ : syracuseStep 2823209 = 2117407) B2117407
theorem B1881279 : Blo 1881142 1881279 := bstep (se 1 (by rfl) ⟨1410959, by rfl⟩ : syracuseStep 1881279 = 2821919) B2821919
theorem B8582507 : Blo 1881142 8582507 := bstep (se 1 (by rfl) ⟨6436880, by rfl⟩ : syracuseStep 8582507 = 12873761) B12873761
theorem B8042267 : Blo 1881142 8042267 := bstep (se 1 (by rfl) ⟨6031700, by rfl⟩ : syracuseStep 8042267 = 12063401) B12063401
theorem B1881959 : Blo 1881142 1881959 := bstep (se 1 (by rfl) ⟨1411469, by rfl⟩ : syracuseStep 1881959 = 2822939) B2822939
theorem B6354827 : Blo 1881142 6354827 := bstep (se 1 (by rfl) ⟨4766120, by rfl⟩ : syracuseStep 6354827 = 9532241) B9532241
theorem B2824361 : Blo 1881142 2824361 := bstep (se 2 (by rfl) ⟨1059135, by rfl⟩ : syracuseStep 2824361 = 2118271) B2118271
theorem B2824475 : Blo 1881142 2824475 := bstep (se 1 (by rfl) ⟨2118356, by rfl⟩ : syracuseStep 2824475 = 4236713) B4236713
theorem B1882559 : Blo 1881142 1882559 := bstep (se 1 (by rfl) ⟨1411919, by rfl⟩ : syracuseStep 1882559 = 2823839) B2823839
theorem B1882735 : Blo 1881142 1882735 := bstep (se 1 (by rfl) ⟨1412051, by rfl⟩ : syracuseStep 1882735 = 2824103) B2824103
theorem B15473267 : Blo 1881142 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B1882791 : Blo 1881142 1882791 := bstep (se 1 (by rfl) ⟨1412093, by rfl⟩ : syracuseStep 1882791 = 2824187) B2824187
theorem B8043239 : Blo 1881142 8043239 := bstep (se 1 (by rfl) ⟨6032429, by rfl⟩ : syracuseStep 8043239 = 12064859) B12064859
theorem B1882875 : Blo 1881142 1882875 := bstep (se 1 (by rfl) ⟨1412156, by rfl⟩ : syracuseStep 1882875 = 2824313) B2824313
theorem B4234175 : Blo 1881142 4234175 := bstep (se 1 (by rfl) ⟨3175631, by rfl⟩ : syracuseStep 4234175 = 6351263) B6351263
theorem B16080191 : Blo 1881142 16080191 := bstep (se 1 (by rfl) ⟨12060143, by rfl⟩ : syracuseStep 16080191 = 24120287) B24120287
theorem B4234679 : Blo 1881142 4234679 := bstep (se 1 (by rfl) ⟨3176009, by rfl⟩ : syracuseStep 4234679 = 6352019) B6352019
theorem B6783371 : Blo 1881142 6783371 := bstep (se 1 (by rfl) ⟨5087528, by rfl⟩ : syracuseStep 6783371 = 10175057) B10175057
theorem B4236551 : Blo 1881142 4236551 := bstep (se 1 (by rfl) ⟨3177413, by rfl⟩ : syracuseStep 4236551 = 6354827) B6354827
theorem B10315511 : Blo 1881142 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B21448637 : Blo 1881142 21448637 := bstep (se 3 (by rfl) ⟨4021619, by rfl⟩ : syracuseStep 21448637 = 8043239) B8043239
theorem B30935321 : Blo 1881142 30935321 := bstep (se 2 (by rfl) ⟨11600745, by rfl⟩ : syracuseStep 30935321 = 23201491) B23201491
theorem B4762415 : Blo 1881142 4762415 := bstep (se 1 (by rfl) ⟨3571811, by rfl⟩ : syracuseStep 4762415 = 7143623) B7143623
theorem B16305407 : Blo 1881142 16305407 := bstep (se 1 (by rfl) ⟨12229055, by rfl⟩ : syracuseStep 16305407 = 24458111) B24458111
theorem B5721671 : Blo 1881142 5721671 := bstep (se 1 (by rfl) ⟨4291253, by rfl⟩ : syracuseStep 5721671 = 8582507) B8582507
theorem B5361511 : Blo 1881142 5361511 := bstep (se 1 (by rfl) ⟨4021133, by rfl⟩ : syracuseStep 5361511 = 8042267) B8042267
theorem B4763519 : Blo 1881142 4763519 := bstep (se 1 (by rfl) ⟨3572639, by rfl⟩ : syracuseStep 4763519 = 7145279) B7145279
theorem B24121313 : Blo 1881142 24121313 := bstep (se 2 (by rfl) ⟨9045492, by rfl⟩ : syracuseStep 24121313 = 18090985) B18090985
theorem B2822783 : Blo 1881142 2822783 := bstep (se 1 (by rfl) ⟨2117087, by rfl⟩ : syracuseStep 2822783 = 4234175) B4234175
theorem B10720127 : Blo 1881142 10720127 := bstep (se 1 (by rfl) ⟨8040095, by rfl⟩ : syracuseStep 10720127 = 16080191) B16080191
theorem B2823119 : Blo 1881142 2823119 := bstep (se 1 (by rfl) ⟨2117339, by rfl⟩ : syracuseStep 2823119 = 4234679) B4234679
theorem B1881179 : Blo 1881142 1881179 := bstep (se 1 (by rfl) ⟨1410884, by rfl⟩ : syracuseStep 1881179 = 2821769) B2821769
theorem B1881311 : Blo 1881142 1881311 := bstep (se 1 (by rfl) ⟨1410983, by rfl⟩ : syracuseStep 1881311 = 2821967) B2821967
theorem B4765007 : Blo 1881142 4765007 := bstep (se 1 (by rfl) ⟨3573755, by rfl⟩ : syracuseStep 4765007 = 7147511) B7147511
theorem B3175915 : Blo 1881142 3175915 := bstep (se 1 (by rfl) ⟨2381936, by rfl⟩ : syracuseStep 3175915 = 4763873) B4763873
theorem B1881599 : Blo 1881142 1881599 := bstep (se 1 (by rfl) ⟨1411199, by rfl⟩ : syracuseStep 1881599 = 2822399) B2822399
theorem B86947343 : Blo 1881142 86947343 := bstep (se 1 (by rfl) ⟨65210507, by rfl⟩ : syracuseStep 86947343 = 130421015) B130421015
theorem B4232735 : Blo 1881142 4232735 := bstep (se 1 (by rfl) ⟨3174551, by rfl⟩ : syracuseStep 4232735 = 6349103) B6349103
theorem B137303687 : Blo 1881142 137303687 := bstep (se 1 (by rfl) ⟨102977765, by rfl⟩ : syracuseStep 137303687 = 205955531) B205955531
theorem B4233131 : Blo 1881142 4233131 := bstep (se 1 (by rfl) ⟨3174848, by rfl⟩ : syracuseStep 4233131 = 6349697) B6349697
theorem B9525275 : Blo 1881142 9525275 := bstep (se 1 (by rfl) ⟨7143956, by rfl⟩ : syracuseStep 9525275 = 14287913) B14287913
theorem B1882139 : Blo 1881142 1882139 := bstep (se 1 (by rfl) ⟨1411604, by rfl⟩ : syracuseStep 1882139 = 2823209) B2823209
theorem B4233707 : Blo 1881142 4233707 := bstep (se 1 (by rfl) ⟨3175280, by rfl⟩ : syracuseStep 4233707 = 6350561) B6350561
theorem B12884591 : Blo 1881142 12884591 := bstep (se 1 (by rfl) ⟨9663443, by rfl⟩ : syracuseStep 12884591 = 19326887) B19326887
theorem B1882907 : Blo 1881142 1882907 := bstep (se 1 (by rfl) ⟨1412180, by rfl⟩ : syracuseStep 1882907 = 2824361) B2824361
theorem B1882983 : Blo 1881142 1882983 := bstep (se 1 (by rfl) ⟨1412237, by rfl⟩ : syracuseStep 1882983 = 2824475) B2824475
theorem B17161723 : Blo 1881142 17161723 := bstep (se 1 (by rfl) ⟨12871292, by rfl⟩ : syracuseStep 17161723 = 25742585) B25742585
theorem B4522247 : Blo 1881142 4522247 := bstep (se 1 (by rfl) ⟨3391685, by rfl⟩ : syracuseStep 4522247 = 6783371) B6783371
theorem B6350183 : Blo 1881142 6350183 := bstep (se 1 (by rfl) ⟨4762637, by rfl⟩ : syracuseStep 6350183 = 9525275) B9525275
theorem B22882297 : Blo 1881142 22882297 := bstep (se 2 (by rfl) ⟨8580861, by rfl⟩ : syracuseStep 22882297 = 17161723) B17161723
theorem B7146751 : Blo 1881142 7146751 := bstep (se 1 (by rfl) ⟨5360063, by rfl⟩ : syracuseStep 7146751 = 10720127) B10720127
theorem B2821823 : Blo 1881142 2821823 := bstep (se 1 (by rfl) ⟨2116367, by rfl⟩ : syracuseStep 2821823 = 4232735) B4232735
theorem B6877007 : Blo 1881142 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B2822087 : Blo 1881142 2822087 := bstep (se 1 (by rfl) ⟨2116565, by rfl⟩ : syracuseStep 2822087 = 4233131) B4233131
theorem B14299091 : Blo 1881142 14299091 := bstep (se 1 (by rfl) ⟨10724318, by rfl⟩ : syracuseStep 14299091 = 21448637) B21448637
theorem B20623547 : Blo 1881142 20623547 := bstep (se 1 (by rfl) ⟨15467660, by rfl⟩ : syracuseStep 20623547 = 30935321) B30935321
theorem B2822471 : Blo 1881142 2822471 := bstep (se 1 (by rfl) ⟨2116853, by rfl⟩ : syracuseStep 2822471 = 4233707) B4233707
theorem B8589727 : Blo 1881142 8589727 := bstep (se 1 (by rfl) ⟨6442295, by rfl⟩ : syracuseStep 8589727 = 12884591) B12884591
theorem B3174943 : Blo 1881142 3174943 := bstep (se 1 (by rfl) ⟨2381207, by rfl⟩ : syracuseStep 3174943 = 4762415) B4762415
theorem B3814447 : Blo 1881142 3814447 := bstep (se 1 (by rfl) ⟨2860835, by rfl⟩ : syracuseStep 3814447 = 5721671) B5721671
theorem B7148681 : Blo 1881142 7148681 := bstep (se 2 (by rfl) ⟨2680755, by rfl⟩ : syracuseStep 7148681 = 5361511) B5361511
theorem B3175679 : Blo 1881142 3175679 := bstep (se 1 (by rfl) ⟨2381759, by rfl⟩ : syracuseStep 3175679 = 4763519) B4763519
theorem B1881855 : Blo 1881142 1881855 := bstep (se 1 (by rfl) ⟨1411391, by rfl⟩ : syracuseStep 1881855 = 2822783) B2822783
theorem B1882079 : Blo 1881142 1882079 := bstep (se 1 (by rfl) ⟨1411559, by rfl⟩ : syracuseStep 1882079 = 2823119) B2823119
theorem B2824367 : Blo 1881142 2824367 := bstep (se 1 (by rfl) ⟨2118275, by rfl⟩ : syracuseStep 2824367 = 4236551) B4236551
theorem B3176671 : Blo 1881142 3176671 := bstep (se 1 (by rfl) ⟨2382503, by rfl⟩ : syracuseStep 3176671 = 4765007) B4765007
theorem B57964895 : Blo 1881142 57964895 := bstep (se 1 (by rfl) ⟨43473671, by rfl⟩ : syracuseStep 57964895 = 86947343) B86947343
theorem B91535791 : Blo 1881142 91535791 := bstep (se 1 (by rfl) ⟨68651843, by rfl⟩ : syracuseStep 91535791 = 137303687) B137303687
theorem B4234553 : Blo 1881142 4234553 := bstep (se 2 (by rfl) ⟨1587957, by rfl⟩ : syracuseStep 4234553 = 3175915) B3175915
theorem B10870271 : Blo 1881142 10870271 := bstep (se 1 (by rfl) ⟨8152703, by rfl⟩ : syracuseStep 10870271 = 16305407) B16305407
theorem B16080875 : Blo 1881142 16080875 := bstep (se 1 (by rfl) ⟨12060656, by rfl⟩ : syracuseStep 16080875 = 24121313) B24121313
theorem B3014831 : Blo 1881142 3014831 := bstep (se 1 (by rfl) ⟨2261123, by rfl⟩ : syracuseStep 3014831 = 4522247) B4522247
theorem B4235561 : Blo 1881142 4235561 := bstep (se 2 (by rfl) ⟨1588335, by rfl⟩ : syracuseStep 4235561 = 3176671) B3176671
theorem B11452969 : Blo 1881142 11452969 := bstep (se 2 (by rfl) ⟨4294863, by rfl⟩ : syracuseStep 11452969 = 8589727) B8589727
theorem B38643263 : Blo 1881142 38643263 := bstep (se 1 (by rfl) ⟨28982447, by rfl⟩ : syracuseStep 38643263 = 57964895) B57964895
theorem B9529001 : Blo 1881142 9529001 := bstep (se 2 (by rfl) ⟨3573375, by rfl⟩ : syracuseStep 9529001 = 7146751) B7146751
theorem B30509729 : Blo 1881142 30509729 := bstep (se 2 (by rfl) ⟨11441148, by rfl⟩ : syracuseStep 30509729 = 22882297) B22882297
theorem B13749031 : Blo 1881142 13749031 := bstep (se 1 (by rfl) ⟨10311773, by rfl⟩ : syracuseStep 13749031 = 20623547) B20623547
theorem B122047721 : Blo 1881142 122047721 := bstep (se 2 (by rfl) ⟨45767895, by rfl⟩ : syracuseStep 122047721 = 91535791) B91535791
theorem B2117119 : Blo 1881142 2117119 := bstep (se 1 (by rfl) ⟨1587839, by rfl⟩ : syracuseStep 2117119 = 3175679) B3175679
theorem B2823035 : Blo 1881142 2823035 := bstep (se 1 (by rfl) ⟨2117276, by rfl⟩ : syracuseStep 2823035 = 4234553) B4234553
theorem B7246847 : Blo 1881142 7246847 := bstep (se 1 (by rfl) ⟨5435135, by rfl⟩ : syracuseStep 7246847 = 10870271) B10870271
theorem B1881215 : Blo 1881142 1881215 := bstep (se 1 (by rfl) ⟨1410911, by rfl⟩ : syracuseStep 1881215 = 2821823) B2821823
theorem B4584671 : Blo 1881142 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B1881391 : Blo 1881142 1881391 := bstep (se 1 (by rfl) ⟨1411043, by rfl⟩ : syracuseStep 1881391 = 2822087) B2822087
theorem B9532727 : Blo 1881142 9532727 := bstep (se 1 (by rfl) ⟨7149545, by rfl⟩ : syracuseStep 9532727 = 14299091) B14299091
theorem B10720583 : Blo 1881142 10720583 := bstep (se 1 (by rfl) ⟨8040437, by rfl⟩ : syracuseStep 10720583 = 16080875) B16080875
theorem B1881647 : Blo 1881142 1881647 := bstep (se 1 (by rfl) ⟨1411235, by rfl⟩ : syracuseStep 1881647 = 2822471) B2822471
theorem B4233257 : Blo 1881142 4233257 := bstep (se 2 (by rfl) ⟨1587471, by rfl⟩ : syracuseStep 4233257 = 3174943) B3174943
theorem B4765787 : Blo 1881142 4765787 := bstep (se 1 (by rfl) ⟨3574340, by rfl⟩ : syracuseStep 4765787 = 7148681) B7148681
theorem B4233455 : Blo 1881142 4233455 := bstep (se 1 (by rfl) ⟨3175091, by rfl⟩ : syracuseStep 4233455 = 6350183) B6350183
theorem B5085929 : Blo 1881142 5085929 := bstep (se 2 (by rfl) ⟨1907223, by rfl⟩ : syracuseStep 5085929 = 3814447) B3814447
theorem B1882911 : Blo 1881142 1882911 := bstep (se 1 (by rfl) ⟨1412183, by rfl⟩ : syracuseStep 1882911 = 2824367) B2824367
theorem B15270625 : Blo 1881142 15270625 := bstep (se 2 (by rfl) ⟨5726484, by rfl⟩ : syracuseStep 15270625 = 11452969) B11452969
theorem B3056447 : Blo 1881142 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B73328165 : Blo 1881142 73328165 := bstep (se 4 (by rfl) ⟨6874515, by rfl⟩ : syracuseStep 73328165 = 13749031) B13749031
theorem B81365147 : Blo 1881142 81365147 := bstep (se 1 (by rfl) ⟨61023860, by rfl⟩ : syracuseStep 81365147 = 122047721) B122047721
theorem B8039549 : Blo 1881142 8039549 := bstep (se 3 (by rfl) ⟨1507415, by rfl⟩ : syracuseStep 8039549 = 3014831) B3014831
theorem B7147055 : Blo 1881142 7147055 := bstep (se 1 (by rfl) ⟨5360291, by rfl⟩ : syracuseStep 7147055 = 10720583) B10720583
theorem B6352667 : Blo 1881142 6352667 := bstep (se 1 (by rfl) ⟨4764500, by rfl⟩ : syracuseStep 6352667 = 9529001) B9529001
theorem B2822171 : Blo 1881142 2822171 := bstep (se 1 (by rfl) ⟨2116628, by rfl⟩ : syracuseStep 2822171 = 4233257) B4233257
theorem B2822303 : Blo 1881142 2822303 := bstep (se 1 (by rfl) ⟨2116727, by rfl⟩ : syracuseStep 2822303 = 4233455) B4233455
theorem B13562477 : Blo 1881142 13562477 := bstep (se 3 (by rfl) ⟨2542964, by rfl⟩ : syracuseStep 13562477 = 5085929) B5085929
theorem B2822825 : Blo 1881142 2822825 := bstep (se 2 (by rfl) ⟨1058559, by rfl⟩ : syracuseStep 2822825 = 2117119) B2117119
theorem B2823707 : Blo 1881142 2823707 := bstep (se 1 (by rfl) ⟨2117780, by rfl⟩ : syracuseStep 2823707 = 4235561) B4235561
theorem B1882023 : Blo 1881142 1882023 := bstep (se 1 (by rfl) ⟨1411517, by rfl⟩ : syracuseStep 1882023 = 2823035) B2823035
theorem B6355151 : Blo 1881142 6355151 := bstep (se 1 (by rfl) ⟨4766363, by rfl⟩ : syracuseStep 6355151 = 9532727) B9532727
theorem B25762175 : Blo 1881142 25762175 := bstep (se 1 (by rfl) ⟨19321631, by rfl⟩ : syracuseStep 25762175 = 38643263) B38643263
theorem B3177191 : Blo 1881142 3177191 := bstep (se 1 (by rfl) ⟨2382893, by rfl⟩ : syracuseStep 3177191 = 4765787) B4765787
theorem B20339819 : Blo 1881142 20339819 := bstep (se 1 (by rfl) ⟨15254864, by rfl⟩ : syracuseStep 20339819 = 30509729) B30509729
theorem B19324925 : Blo 1881142 19324925 := bstep (se 3 (by rfl) ⟨3623423, by rfl⟩ : syracuseStep 19324925 = 7246847) B7246847
theorem B4236767 : Blo 1881142 4236767 := bstep (se 1 (by rfl) ⟨3177575, by rfl⟩ : syracuseStep 4236767 = 6355151) B6355151
theorem B13559879 : Blo 1881142 13559879 := bstep (se 1 (by rfl) ⟨10169909, by rfl⟩ : syracuseStep 13559879 = 20339819) B20339819
theorem B5359699 : Blo 1881142 5359699 := bstep (se 1 (by rfl) ⟨4019774, by rfl⟩ : syracuseStep 5359699 = 8039549) B8039549
theorem B48885443 : Blo 1881142 48885443 := bstep (se 1 (by rfl) ⟨36664082, by rfl⟩ : syracuseStep 48885443 = 73328165) B73328165
theorem B54243431 : Blo 1881142 54243431 := bstep (se 1 (by rfl) ⟨40682573, by rfl⟩ : syracuseStep 54243431 = 81365147) B81365147
theorem B17174783 : Blo 1881142 17174783 := bstep (se 1 (by rfl) ⟨12881087, by rfl⟩ : syracuseStep 17174783 = 25762175) B25762175
theorem B2118127 : Blo 1881142 2118127 := bstep (se 1 (by rfl) ⟨1588595, by rfl⟩ : syracuseStep 2118127 = 3177191) B3177191
theorem B4764703 : Blo 1881142 4764703 := bstep (se 1 (by rfl) ⟨3573527, by rfl⟩ : syracuseStep 4764703 = 7147055) B7147055
theorem B12883283 : Blo 1881142 12883283 := bstep (se 1 (by rfl) ⟨9662462, by rfl⟩ : syracuseStep 12883283 = 19324925) B19324925
theorem B1881447 : Blo 1881142 1881447 := bstep (se 1 (by rfl) ⟨1411085, by rfl⟩ : syracuseStep 1881447 = 2822171) B2822171
theorem B1881535 : Blo 1881142 1881535 := bstep (se 1 (by rfl) ⟨1411151, by rfl⟩ : syracuseStep 1881535 = 2822303) B2822303
theorem B9041651 : Blo 1881142 9041651 := bstep (se 1 (by rfl) ⟨6781238, by rfl⟩ : syracuseStep 9041651 = 13562477) B13562477
theorem B1881883 : Blo 1881142 1881883 := bstep (se 1 (by rfl) ⟨1411412, by rfl⟩ : syracuseStep 1881883 = 2822825) B2822825
theorem B2037631 : Blo 1881142 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B1882471 : Blo 1881142 1882471 := bstep (se 1 (by rfl) ⟨1411853, by rfl⟩ : syracuseStep 1882471 = 2823707) B2823707
theorem B81443333 : Blo 1881142 81443333 := bstep (se 4 (by rfl) ⟨7635312, by rfl⟩ : syracuseStep 81443333 = 15270625) B15270625
theorem B4235111 : Blo 1881142 4235111 := bstep (se 1 (by rfl) ⟨3176333, by rfl⟩ : syracuseStep 4235111 = 6352667) B6352667
theorem B32590295 : Blo 1881142 32590295 := bstep (se 1 (by rfl) ⟨24442721, by rfl⟩ : syracuseStep 32590295 = 48885443) B48885443
theorem B36162287 : Blo 1881142 36162287 := bstep (se 1 (by rfl) ⟨27121715, by rfl⟩ : syracuseStep 36162287 = 54243431) B54243431
theorem B7146265 : Blo 1881142 7146265 := bstep (se 2 (by rfl) ⟨2679849, by rfl⟩ : syracuseStep 7146265 = 5359699) B5359699
theorem B8588855 : Blo 1881142 8588855 := bstep (se 1 (by rfl) ⟨6441641, by rfl⟩ : syracuseStep 8588855 = 12883283) B12883283
theorem B6352937 : Blo 1881142 6352937 := bstep (se 2 (by rfl) ⟨2382351, by rfl⟩ : syracuseStep 6352937 = 4764703) B4764703
theorem B9039919 : Blo 1881142 9039919 := bstep (se 1 (by rfl) ⟨6779939, by rfl⟩ : syracuseStep 9039919 = 13559879) B13559879
theorem B2716841 : Blo 1881142 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B2823407 : Blo 1881142 2823407 := bstep (se 1 (by rfl) ⟨2117555, by rfl⟩ : syracuseStep 2823407 = 4235111) B4235111
theorem B11449855 : Blo 1881142 11449855 := bstep (se 1 (by rfl) ⟨8587391, by rfl⟩ : syracuseStep 11449855 = 17174783) B17174783
theorem B2824169 : Blo 1881142 2824169 := bstep (se 2 (by rfl) ⟨1059063, by rfl⟩ : syracuseStep 2824169 = 2118127) B2118127
theorem B2824511 : Blo 1881142 2824511 := bstep (se 1 (by rfl) ⟨2118383, by rfl⟩ : syracuseStep 2824511 = 4236767) B4236767
theorem B6027767 : Blo 1881142 6027767 := bstep (se 1 (by rfl) ⟨4520825, by rfl⟩ : syracuseStep 6027767 = 9041651) B9041651
theorem B54295555 : Blo 1881142 54295555 := bstep (se 1 (by rfl) ⟨40721666, by rfl⟩ : syracuseStep 54295555 = 81443333) B81443333
theorem B4235291 : Blo 1881142 4235291 := bstep (se 1 (by rfl) ⟨3176468, by rfl⟩ : syracuseStep 4235291 = 6352937) B6352937
theorem B9528353 : Blo 1881142 9528353 := bstep (se 2 (by rfl) ⟨3573132, by rfl⟩ : syracuseStep 9528353 = 7146265) B7146265
theorem B72394073 : Blo 1881142 72394073 := bstep (se 2 (by rfl) ⟨27147777, by rfl⟩ : syracuseStep 72394073 = 54295555) B54295555
theorem B21726863 : Blo 1881142 21726863 := bstep (se 1 (by rfl) ⟨16295147, by rfl⟩ : syracuseStep 21726863 = 32590295) B32590295
theorem B61065893 : Blo 1881142 61065893 := bstep (se 4 (by rfl) ⟨5724927, by rfl⟩ : syracuseStep 61065893 = 11449855) B11449855
theorem B12053225 : Blo 1881142 12053225 := bstep (se 2 (by rfl) ⟨4519959, by rfl⟩ : syracuseStep 12053225 = 9039919) B9039919
theorem B7244909 : Blo 1881142 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B4018511 : Blo 1881142 4018511 := bstep (se 1 (by rfl) ⟨3013883, by rfl⟩ : syracuseStep 4018511 = 6027767) B6027767
theorem B1882271 : Blo 1881142 1882271 := bstep (se 1 (by rfl) ⟨1411703, by rfl⟩ : syracuseStep 1882271 = 2823407) B2823407
theorem B1882779 : Blo 1881142 1882779 := bstep (se 1 (by rfl) ⟨1412084, by rfl⟩ : syracuseStep 1882779 = 2824169) B2824169
theorem B1883007 : Blo 1881142 1883007 := bstep (se 1 (by rfl) ⟨1412255, by rfl⟩ : syracuseStep 1883007 = 2824511) B2824511
theorem B24108191 : Blo 1881142 24108191 := bstep (se 1 (by rfl) ⟨18081143, by rfl⟩ : syracuseStep 24108191 = 36162287) B36162287
theorem B5725903 : Blo 1881142 5725903 := bstep (se 1 (by rfl) ⟨4294427, by rfl⟩ : syracuseStep 5725903 = 8588855) B8588855
theorem B2679007 : Blo 1881142 2679007 := bstep (se 1 (by rfl) ⟨2009255, by rfl⟩ : syracuseStep 2679007 = 4018511) B4018511
theorem B14484575 : Blo 1881142 14484575 := bstep (se 1 (by rfl) ⟨10863431, by rfl⟩ : syracuseStep 14484575 = 21726863) B21726863
theorem B6352235 : Blo 1881142 6352235 := bstep (se 1 (by rfl) ⟨4764176, by rfl⟩ : syracuseStep 6352235 = 9528353) B9528353
theorem B48262715 : Blo 1881142 48262715 := bstep (se 1 (by rfl) ⟨36197036, by rfl⟩ : syracuseStep 48262715 = 72394073) B72394073
theorem B40710595 : Blo 1881142 40710595 := bstep (se 1 (by rfl) ⟨30532946, by rfl⟩ : syracuseStep 40710595 = 61065893) B61065893
theorem B4829939 : Blo 1881142 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B2823527 : Blo 1881142 2823527 := bstep (se 1 (by rfl) ⟨2117645, by rfl⟩ : syracuseStep 2823527 = 4235291) B4235291
theorem B8035483 : Blo 1881142 8035483 := bstep (se 1 (by rfl) ⟨6026612, by rfl⟩ : syracuseStep 8035483 = 12053225) B12053225
theorem B16072127 : Blo 1881142 16072127 := bstep (se 1 (by rfl) ⟨12054095, by rfl⟩ : syracuseStep 16072127 = 24108191) B24108191
theorem B7634537 : Blo 1881142 7634537 := bstep (se 2 (by rfl) ⟨2862951, by rfl⟩ : syracuseStep 7634537 = 5725903) B5725903
theorem B3572009 : Blo 1881142 3572009 := bstep (se 2 (by rfl) ⟨1339503, by rfl⟩ : syracuseStep 3572009 = 2679007) B2679007
theorem B3219959 : Blo 1881142 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B54280793 : Blo 1881142 54280793 := bstep (se 2 (by rfl) ⟨20355297, by rfl⟩ : syracuseStep 54280793 = 40710595) B40710595
theorem B5089691 : Blo 1881142 5089691 := bstep (se 1 (by rfl) ⟨3817268, by rfl⟩ : syracuseStep 5089691 = 7634537) B7634537
theorem B32175143 : Blo 1881142 32175143 := bstep (se 1 (by rfl) ⟨24131357, by rfl⟩ : syracuseStep 32175143 = 48262715) B48262715
theorem B9656383 : Blo 1881142 9656383 := bstep (se 1 (by rfl) ⟨7242287, by rfl⟩ : syracuseStep 9656383 = 14484575) B14484575
theorem B1882351 : Blo 1881142 1882351 := bstep (se 1 (by rfl) ⟨1411763, by rfl⟩ : syracuseStep 1882351 = 2823527) B2823527
theorem B10713977 : Blo 1881142 10713977 := bstep (se 2 (by rfl) ⟨4017741, by rfl⟩ : syracuseStep 10713977 = 8035483) B8035483
theorem B4234823 : Blo 1881142 4234823 := bstep (se 1 (by rfl) ⟨3176117, by rfl⟩ : syracuseStep 4234823 = 6352235) B6352235
theorem B10714751 : Blo 1881142 10714751 := bstep (se 1 (by rfl) ⟨8036063, by rfl⟩ : syracuseStep 10714751 = 16072127) B16072127
theorem B2146639 : Blo 1881142 2146639 := bstep (se 1 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 2146639 = 3219959) B3219959
theorem B3393127 : Blo 1881142 3393127 := bstep (se 1 (by rfl) ⟨2544845, by rfl⟩ : syracuseStep 3393127 = 5089691) B5089691
theorem B36187195 : Blo 1881142 36187195 := bstep (se 1 (by rfl) ⟨27140396, by rfl⟩ : syracuseStep 36187195 = 54280793) B54280793
theorem B21450095 : Blo 1881142 21450095 := bstep (se 1 (by rfl) ⟨16087571, by rfl⟩ : syracuseStep 21450095 = 32175143) B32175143
theorem B2823215 : Blo 1881142 2823215 := bstep (se 1 (by rfl) ⟨2117411, by rfl⟩ : syracuseStep 2823215 = 4234823) B4234823
theorem B12875177 : Blo 1881142 12875177 := bstep (se 2 (by rfl) ⟨4828191, by rfl⟩ : syracuseStep 12875177 = 9656383) B9656383
theorem B2381339 : Blo 1881142 2381339 := bstep (se 1 (by rfl) ⟨1786004, by rfl⟩ : syracuseStep 2381339 = 3572009) B3572009
theorem B7142651 : Blo 1881142 7142651 := bstep (se 1 (by rfl) ⟨5356988, by rfl⟩ : syracuseStep 7142651 = 10713977) B10713977
theorem B7143167 : Blo 1881142 7143167 := bstep (se 1 (by rfl) ⟨5357375, by rfl⟩ : syracuseStep 7143167 = 10714751) B10714751
theorem B6350237 : Blo 1881142 6350237 := bstep (se 3 (by rfl) ⟨1190669, by rfl⟩ : syracuseStep 6350237 = 2381339) B2381339
theorem B4524169 : Blo 1881142 4524169 := bstep (se 2 (by rfl) ⟨1696563, by rfl⟩ : syracuseStep 4524169 = 3393127) B3393127
theorem B4761767 : Blo 1881142 4761767 := bstep (se 1 (by rfl) ⟨3571325, by rfl⟩ : syracuseStep 4761767 = 7142651) B7142651
theorem B4762111 : Blo 1881142 4762111 := bstep (se 1 (by rfl) ⟨3571583, by rfl⟩ : syracuseStep 4762111 = 7143167) B7143167
theorem B2862185 : Blo 1881142 2862185 := bstep (se 2 (by rfl) ⟨1073319, by rfl⟩ : syracuseStep 2862185 = 2146639) B2146639
theorem B14300063 : Blo 1881142 14300063 := bstep (se 1 (by rfl) ⟨10725047, by rfl⟩ : syracuseStep 14300063 = 21450095) B21450095
theorem B1882143 : Blo 1881142 1882143 := bstep (se 1 (by rfl) ⟨1411607, by rfl⟩ : syracuseStep 1882143 = 2823215) B2823215
theorem B8583451 : Blo 1881142 8583451 := bstep (se 1 (by rfl) ⟨6437588, by rfl⟩ : syracuseStep 8583451 = 12875177) B12875177
theorem B48249593 : Blo 1881142 48249593 := bstep (se 2 (by rfl) ⟨18093597, by rfl⟩ : syracuseStep 48249593 = 36187195) B36187195
theorem B6349481 : Blo 1881142 6349481 := bstep (se 2 (by rfl) ⟨2381055, by rfl⟩ : syracuseStep 6349481 = 4762111) B4762111
theorem B45778405 : Blo 1881142 45778405 := bstep (se 4 (by rfl) ⟨4291725, by rfl⟩ : syracuseStep 45778405 = 8583451) B8583451
theorem B6032225 : Blo 1881142 6032225 := bstep (se 2 (by rfl) ⟨2262084, by rfl⟩ : syracuseStep 6032225 = 4524169) B4524169
theorem B3174511 : Blo 1881142 3174511 := bstep (se 1 (by rfl) ⟨2380883, by rfl⟩ : syracuseStep 3174511 = 4761767) B4761767
theorem B32166395 : Blo 1881142 32166395 := bstep (se 1 (by rfl) ⟨24124796, by rfl⟩ : syracuseStep 32166395 = 48249593) B48249593
theorem B9533375 : Blo 1881142 9533375 := bstep (se 1 (by rfl) ⟨7150031, by rfl⟩ : syracuseStep 9533375 = 14300063) B14300063
theorem B4233491 : Blo 1881142 4233491 := bstep (se 1 (by rfl) ⟨3175118, by rfl⟩ : syracuseStep 4233491 = 6350237) B6350237
theorem B30529973 : Blo 1881142 30529973 := bstep (se 5 (by rfl) ⟨1431092, by rfl⟩ : syracuseStep 30529973 = 2862185) B2862185
theorem B2822327 : Blo 1881142 2822327 := bstep (se 1 (by rfl) ⟨2116745, by rfl⟩ : syracuseStep 2822327 = 4233491) B4233491
theorem B20353315 : Blo 1881142 20353315 := bstep (se 1 (by rfl) ⟨15264986, by rfl⟩ : syracuseStep 20353315 = 30529973) B30529973
theorem B4232681 : Blo 1881142 4232681 := bstep (se 2 (by rfl) ⟨1587255, by rfl⟩ : syracuseStep 4232681 = 3174511) B3174511
theorem B21444263 : Blo 1881142 21444263 := bstep (se 1 (by rfl) ⟨16083197, by rfl⟩ : syracuseStep 21444263 = 32166395) B32166395
theorem B4232987 : Blo 1881142 4232987 := bstep (se 1 (by rfl) ⟨3174740, by rfl⟩ : syracuseStep 4232987 = 6349481) B6349481
theorem B6355583 : Blo 1881142 6355583 := bstep (se 1 (by rfl) ⟨4766687, by rfl⟩ : syracuseStep 6355583 = 9533375) B9533375
theorem B4021483 : Blo 1881142 4021483 := bstep (se 1 (by rfl) ⟨3016112, by rfl⟩ : syracuseStep 4021483 = 6032225) B6032225
theorem B61037873 : Blo 1881142 61037873 := bstep (se 2 (by rfl) ⟨22889202, by rfl⟩ : syracuseStep 61037873 = 45778405) B45778405
theorem B14296175 : Blo 1881142 14296175 := bstep (se 1 (by rfl) ⟨10722131, by rfl⟩ : syracuseStep 14296175 = 21444263) B21444263
theorem B4237055 : Blo 1881142 4237055 := bstep (se 1 (by rfl) ⟨3177791, by rfl⟩ : syracuseStep 4237055 = 6355583) B6355583
theorem B40691915 : Blo 1881142 40691915 := bstep (se 1 (by rfl) ⟨30518936, by rfl⟩ : syracuseStep 40691915 = 61037873) B61037873
theorem B2821787 : Blo 1881142 2821787 := bstep (se 1 (by rfl) ⟨2116340, by rfl⟩ : syracuseStep 2821787 = 4232681) B4232681
theorem B2821991 : Blo 1881142 2821991 := bstep (se 1 (by rfl) ⟨2116493, by rfl⟩ : syracuseStep 2821991 = 4232987) B4232987
theorem B5361977 : Blo 1881142 5361977 := bstep (se 2 (by rfl) ⟨2010741, by rfl⟩ : syracuseStep 5361977 = 4021483) B4021483
theorem B1881551 : Blo 1881142 1881551 := bstep (se 1 (by rfl) ⟨1411163, by rfl⟩ : syracuseStep 1881551 = 2822327) B2822327
theorem B27137753 : Blo 1881142 27137753 := bstep (se 2 (by rfl) ⟨10176657, by rfl⟩ : syracuseStep 27137753 = 20353315) B20353315
theorem B9530783 : Blo 1881142 9530783 := bstep (se 1 (by rfl) ⟨7148087, by rfl⟩ : syracuseStep 9530783 = 14296175) B14296175
theorem B14298605 : Blo 1881142 14298605 := bstep (se 3 (by rfl) ⟨2680988, by rfl⟩ : syracuseStep 14298605 = 5361977) B5361977
theorem B18091835 : Blo 1881142 18091835 := bstep (se 1 (by rfl) ⟨13568876, by rfl⟩ : syracuseStep 18091835 = 27137753) B27137753
theorem B27127943 : Blo 1881142 27127943 := bstep (se 1 (by rfl) ⟨20345957, by rfl⟩ : syracuseStep 27127943 = 40691915) B40691915
theorem B1881191 : Blo 1881142 1881191 := bstep (se 1 (by rfl) ⟨1410893, by rfl⟩ : syracuseStep 1881191 = 2821787) B2821787
theorem B1881327 : Blo 1881142 1881327 := bstep (se 1 (by rfl) ⟨1410995, by rfl⟩ : syracuseStep 1881327 = 2821991) B2821991
theorem B2824703 : Blo 1881142 2824703 := bstep (se 1 (by rfl) ⟨2118527, by rfl⟩ : syracuseStep 2824703 = 4237055) B4237055
theorem B12061223 : Blo 1881142 12061223 := bstep (se 1 (by rfl) ⟨9045917, by rfl⟩ : syracuseStep 12061223 = 18091835) B18091835
theorem B6353855 : Blo 1881142 6353855 := bstep (se 1 (by rfl) ⟨4765391, by rfl⟩ : syracuseStep 6353855 = 9530783) B9530783
theorem B9532403 : Blo 1881142 9532403 := bstep (se 1 (by rfl) ⟨7149302, by rfl⟩ : syracuseStep 9532403 = 14298605) B14298605
theorem B18085295 : Blo 1881142 18085295 := bstep (se 1 (by rfl) ⟨13563971, by rfl⟩ : syracuseStep 18085295 = 27127943) B27127943
theorem B1883135 : Blo 1881142 1883135 := bstep (se 1 (by rfl) ⟨1412351, by rfl⟩ : syracuseStep 1883135 = 2824703) B2824703
theorem B4235903 : Blo 1881142 4235903 := bstep (se 1 (by rfl) ⟨3176927, by rfl⟩ : syracuseStep 4235903 = 6353855) B6353855
theorem B8040815 : Blo 1881142 8040815 := bstep (se 1 (by rfl) ⟨6030611, by rfl⟩ : syracuseStep 8040815 = 12061223) B12061223
theorem B6354935 : Blo 1881142 6354935 := bstep (se 1 (by rfl) ⟨4766201, by rfl⟩ : syracuseStep 6354935 = 9532403) B9532403
theorem B12056863 : Blo 1881142 12056863 := bstep (se 1 (by rfl) ⟨9042647, by rfl⟩ : syracuseStep 12056863 = 18085295) B18085295
theorem B4236623 : Blo 1881142 4236623 := bstep (se 1 (by rfl) ⟨3177467, by rfl⟩ : syracuseStep 4236623 = 6354935) B6354935
theorem B5360543 : Blo 1881142 5360543 := bstep (se 1 (by rfl) ⟨4020407, by rfl⟩ : syracuseStep 5360543 = 8040815) B8040815
theorem B16075817 : Blo 1881142 16075817 := bstep (se 2 (by rfl) ⟨6028431, by rfl⟩ : syracuseStep 16075817 = 12056863) B12056863
theorem B2823935 : Blo 1881142 2823935 := bstep (se 1 (by rfl) ⟨2117951, by rfl⟩ : syracuseStep 2823935 = 4235903) B4235903
theorem B3573695 : Blo 1881142 3573695 := bstep (se 1 (by rfl) ⟨2680271, by rfl⟩ : syracuseStep 3573695 = 5360543) B5360543
theorem B10717211 : Blo 1881142 10717211 := bstep (se 1 (by rfl) ⟨8037908, by rfl⟩ : syracuseStep 10717211 = 16075817) B16075817
theorem B2824415 : Blo 1881142 2824415 := bstep (se 1 (by rfl) ⟨2118311, by rfl⟩ : syracuseStep 2824415 = 4236623) B4236623
theorem B1882623 : Blo 1881142 1882623 := bstep (se 1 (by rfl) ⟨1411967, by rfl⟩ : syracuseStep 1882623 = 2823935) B2823935
theorem B7144807 : Blo 1881142 7144807 := bstep (se 1 (by rfl) ⟨5358605, by rfl⟩ : syracuseStep 7144807 = 10717211) B10717211
theorem B2382463 : Blo 1881142 2382463 := bstep (se 1 (by rfl) ⟨1786847, by rfl⟩ : syracuseStep 2382463 = 3573695) B3573695
theorem B1882943 : Blo 1881142 1882943 := bstep (se 1 (by rfl) ⟨1412207, by rfl⟩ : syracuseStep 1882943 = 2824415) B2824415
theorem B3176617 : Blo 1881142 3176617 := bstep (se 2 (by rfl) ⟨1191231, by rfl⟩ : syracuseStep 3176617 = 2382463) B2382463
theorem B9526409 : Blo 1881142 9526409 := bstep (se 2 (by rfl) ⟨3572403, by rfl⟩ : syracuseStep 9526409 = 7144807) B7144807
theorem B4235489 : Blo 1881142 4235489 := bstep (se 2 (by rfl) ⟨1588308, by rfl⟩ : syracuseStep 4235489 = 3176617) B3176617
theorem B6350939 : Blo 1881142 6350939 := bstep (se 1 (by rfl) ⟨4763204, by rfl⟩ : syracuseStep 6350939 = 9526409) B9526409
theorem B2823659 : Blo 1881142 2823659 := bstep (se 1 (by rfl) ⟨2117744, by rfl⟩ : syracuseStep 2823659 = 4235489) B4235489
theorem B4233959 : Blo 1881142 4233959 := bstep (se 1 (by rfl) ⟨3175469, by rfl⟩ : syracuseStep 4233959 = 6350939) B6350939
theorem B2822639 : Blo 1881142 2822639 := bstep (se 1 (by rfl) ⟨2116979, by rfl⟩ : syracuseStep 2822639 = 4233959) B4233959
theorem B1882439 : Blo 1881142 1882439 := bstep (se 1 (by rfl) ⟨1411829, by rfl⟩ : syracuseStep 1882439 = 2823659) B2823659
theorem B1881759 : Blo 1881142 1881759 := bstep (se 1 (by rfl) ⟨1411319, by rfl⟩ : syracuseStep 1881759 = 2822639) B2822639

theorem C0 (j : ℕ) (h1 : 470285 ≤ j) (h2 : j ≤ 470784) : Blo 1881142 (4 * j + 3) := by
  interval_cases j
  · exact B1881143
  · exact B1881147
  · exact B1881151
  · exact B1881155
  · exact B1881159
  · exact B1881163
  · exact B1881167
  · exact B1881171
  · exact B1881175
  · exact B1881179
  · exact B1881183
  · exact B1881187
  · exact B1881191
  · exact B1881195
  · exact B1881199
  · exact B1881203
  · exact B1881207
  · exact B1881211
  · exact B1881215
  · exact B1881219
  · exact B1881223
  · exact B1881227
  · exact B1881231
  · exact B1881235
  · exact B1881239
  · exact B1881243
  · exact B1881247
  · exact B1881251
  · exact B1881255
  · exact B1881259
  · exact B1881263
  · exact B1881267
  · exact B1881271
  · exact B1881275
  · exact B1881279
  · exact B1881283
  · exact B1881287
  · exact B1881291
  · exact B1881295
  · exact B1881299
  · exact B1881303
  · exact B1881307
  · exact B1881311
  · exact B1881315
  · exact B1881319
  · exact B1881323
  · exact B1881327
  · exact B1881331
  · exact B1881335
  · exact B1881339
  · exact B1881343
  · exact B1881347
  · exact B1881351
  · exact B1881355
  · exact B1881359
  · exact B1881363
  · exact B1881367
  · exact B1881371
  · exact B1881375
  · exact B1881379
  · exact B1881383
  · exact B1881387
  · exact B1881391
  · exact B1881395
  · exact B1881399
  · exact B1881403
  · exact B1881407
  · exact B1881411
  · exact B1881415
  · exact B1881419
  · exact B1881423
  · exact B1881427
  · exact B1881431
  · exact B1881435
  · exact B1881439
  · exact B1881443
  · exact B1881447
  · exact B1881451
  · exact B1881455
  · exact B1881459
  · exact B1881463
  · exact B1881467
  · exact B1881471
  · exact B1881475
  · exact B1881479
  · exact B1881483
  · exact B1881487
  · exact B1881491
  · exact B1881495
  · exact B1881499
  · exact B1881503
  · exact B1881507
  · exact B1881511
  · exact B1881515
  · exact B1881519
  · exact B1881523
  · exact B1881527
  · exact B1881531
  · exact B1881535
  · exact B1881539
  · exact B1881543
  · exact B1881547
  · exact B1881551
  · exact B1881555
  · exact B1881559
  · exact B1881563
  · exact B1881567
  · exact B1881571
  · exact B1881575
  · exact B1881579
  · exact B1881583
  · exact B1881587
  · exact B1881591
  · exact B1881595
  · exact B1881599
  · exact B1881603
  · exact B1881607
  · exact B1881611
  · exact B1881615
  · exact B1881619
  · exact B1881623
  · exact B1881627
  · exact B1881631
  · exact B1881635
  · exact B1881639
  · exact B1881643
  · exact B1881647
  · exact B1881651
  · exact B1881655
  · exact B1881659
  · exact B1881663
  · exact B1881667
  · exact B1881671
  · exact B1881675
  · exact B1881679
  · exact B1881683
  · exact B1881687
  · exact B1881691
  · exact B1881695
  · exact B1881699
  · exact B1881703
  · exact B1881707
  · exact B1881711
  · exact B1881715
  · exact B1881719
  · exact B1881723
  · exact B1881727
  · exact B1881731
  · exact B1881735
  · exact B1881739
  · exact B1881743
  · exact B1881747
  · exact B1881751
  · exact B1881755
  · exact B1881759
  · exact B1881763
  · exact B1881767
  · exact B1881771
  · exact B1881775
  · exact B1881779
  · exact B1881783
  · exact B1881787
  · exact B1881791
  · exact B1881795
  · exact B1881799
  · exact B1881803
  · exact B1881807
  · exact B1881811
  · exact B1881815
  · exact B1881819
  · exact B1881823
  · exact B1881827
  · exact B1881831
  · exact B1881835
  · exact B1881839
  · exact B1881843
  · exact B1881847
  · exact B1881851
  · exact B1881855
  · exact B1881859
  · exact B1881863
  · exact B1881867
  · exact B1881871
  · exact B1881875
  · exact B1881879
  · exact B1881883
  · exact B1881887
  · exact B1881891
  · exact B1881895
  · exact B1881899
  · exact B1881903
  · exact B1881907
  · exact B1881911
  · exact B1881915
  · exact B1881919
  · exact B1881923
  · exact B1881927
  · exact B1881931
  · exact B1881935
  · exact B1881939
  · exact B1881943
  · exact B1881947
  · exact B1881951
  · exact B1881955
  · exact B1881959
  · exact B1881963
  · exact B1881967
  · exact B1881971
  · exact B1881975
  · exact B1881979
  · exact B1881983
  · exact B1881987
  · exact B1881991
  · exact B1881995
  · exact B1881999
  · exact B1882003
  · exact B1882007
  · exact B1882011
  · exact B1882015
  · exact B1882019
  · exact B1882023
  · exact B1882027
  · exact B1882031
  · exact B1882035
  · exact B1882039
  · exact B1882043
  · exact B1882047
  · exact B1882051
  · exact B1882055
  · exact B1882059
  · exact B1882063
  · exact B1882067
  · exact B1882071
  · exact B1882075
  · exact B1882079
  · exact B1882083
  · exact B1882087
  · exact B1882091
  · exact B1882095
  · exact B1882099
  · exact B1882103
  · exact B1882107
  · exact B1882111
  · exact B1882115
  · exact B1882119
  · exact B1882123
  · exact B1882127
  · exact B1882131
  · exact B1882135
  · exact B1882139
  · exact B1882143
  · exact B1882147
  · exact B1882151
  · exact B1882155
  · exact B1882159
  · exact B1882163
  · exact B1882167
  · exact B1882171
  · exact B1882175
  · exact B1882179
  · exact B1882183
  · exact B1882187
  · exact B1882191
  · exact B1882195
  · exact B1882199
  · exact B1882203
  · exact B1882207
  · exact B1882211
  · exact B1882215
  · exact B1882219
  · exact B1882223
  · exact B1882227
  · exact B1882231
  · exact B1882235
  · exact B1882239
  · exact B1882243
  · exact B1882247
  · exact B1882251
  · exact B1882255
  · exact B1882259
  · exact B1882263
  · exact B1882267
  · exact B1882271
  · exact B1882275
  · exact B1882279
  · exact B1882283
  · exact B1882287
  · exact B1882291
  · exact B1882295
  · exact B1882299
  · exact B1882303
  · exact B1882307
  · exact B1882311
  · exact B1882315
  · exact B1882319
  · exact B1882323
  · exact B1882327
  · exact B1882331
  · exact B1882335
  · exact B1882339
  · exact B1882343
  · exact B1882347
  · exact B1882351
  · exact B1882355
  · exact B1882359
  · exact B1882363
  · exact B1882367
  · exact B1882371
  · exact B1882375
  · exact B1882379
  · exact B1882383
  · exact B1882387
  · exact B1882391
  · exact B1882395
  · exact B1882399
  · exact B1882403
  · exact B1882407
  · exact B1882411
  · exact B1882415
  · exact B1882419
  · exact B1882423
  · exact B1882427
  · exact B1882431
  · exact B1882435
  · exact B1882439
  · exact B1882443
  · exact B1882447
  · exact B1882451
  · exact B1882455
  · exact B1882459
  · exact B1882463
  · exact B1882467
  · exact B1882471
  · exact B1882475
  · exact B1882479
  · exact B1882483
  · exact B1882487
  · exact B1882491
  · exact B1882495
  · exact B1882499
  · exact B1882503
  · exact B1882507
  · exact B1882511
  · exact B1882515
  · exact B1882519
  · exact B1882523
  · exact B1882527
  · exact B1882531
  · exact B1882535
  · exact B1882539
  · exact B1882543
  · exact B1882547
  · exact B1882551
  · exact B1882555
  · exact B1882559
  · exact B1882563
  · exact B1882567
  · exact B1882571
  · exact B1882575
  · exact B1882579
  · exact B1882583
  · exact B1882587
  · exact B1882591
  · exact B1882595
  · exact B1882599
  · exact B1882603
  · exact B1882607
  · exact B1882611
  · exact B1882615
  · exact B1882619
  · exact B1882623
  · exact B1882627
  · exact B1882631
  · exact B1882635
  · exact B1882639
  · exact B1882643
  · exact B1882647
  · exact B1882651
  · exact B1882655
  · exact B1882659
  · exact B1882663
  · exact B1882667
  · exact B1882671
  · exact B1882675
  · exact B1882679
  · exact B1882683
  · exact B1882687
  · exact B1882691
  · exact B1882695
  · exact B1882699
  · exact B1882703
  · exact B1882707
  · exact B1882711
  · exact B1882715
  · exact B1882719
  · exact B1882723
  · exact B1882727
  · exact B1882731
  · exact B1882735
  · exact B1882739
  · exact B1882743
  · exact B1882747
  · exact B1882751
  · exact B1882755
  · exact B1882759
  · exact B1882763
  · exact B1882767
  · exact B1882771
  · exact B1882775
  · exact B1882779
  · exact B1882783
  · exact B1882787
  · exact B1882791
  · exact B1882795
  · exact B1882799
  · exact B1882803
  · exact B1882807
  · exact B1882811
  · exact B1882815
  · exact B1882819
  · exact B1882823
  · exact B1882827
  · exact B1882831
  · exact B1882835
  · exact B1882839
  · exact B1882843
  · exact B1882847
  · exact B1882851
  · exact B1882855
  · exact B1882859
  · exact B1882863
  · exact B1882867
  · exact B1882871
  · exact B1882875
  · exact B1882879
  · exact B1882883
  · exact B1882887
  · exact B1882891
  · exact B1882895
  · exact B1882899
  · exact B1882903
  · exact B1882907
  · exact B1882911
  · exact B1882915
  · exact B1882919
  · exact B1882923
  · exact B1882927
  · exact B1882931
  · exact B1882935
  · exact B1882939
  · exact B1882943
  · exact B1882947
  · exact B1882951
  · exact B1882955
  · exact B1882959
  · exact B1882963
  · exact B1882967
  · exact B1882971
  · exact B1882975
  · exact B1882979
  · exact B1882983
  · exact B1882987
  · exact B1882991
  · exact B1882995
  · exact B1882999
  · exact B1883003
  · exact B1883007
  · exact B1883011
  · exact B1883015
  · exact B1883019
  · exact B1883023
  · exact B1883027
  · exact B1883031
  · exact B1883035
  · exact B1883039
  · exact B1883043
  · exact B1883047
  · exact B1883051
  · exact B1883055
  · exact B1883059
  · exact B1883063
  · exact B1883067
  · exact B1883071
  · exact B1883075
  · exact B1883079
  · exact B1883083
  · exact B1883087
  · exact B1883091
  · exact B1883095
  · exact B1883099
  · exact B1883103
  · exact B1883107
  · exact B1883111
  · exact B1883115
  · exact B1883119
  · exact B1883123
  · exact B1883127
  · exact B1883131
  · exact B1883135
  · exact B1883139

theorem solution (m : ℕ) (hlo : 1881142 ≤ m) (hhi : m ≤ 1883142) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 470285 ≤ j := by omega
    have hj2 : j ≤ 470784 := by omega
    have hb : Blo 1881142 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
