-- Prove2me | solution 1 for syracuse_descends_range_381763_385763
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:43.143945+00:00
-- url     : https://prove2.me/submissions/adf81710-91e2-4167-afc3-ae1d46293a4d

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


theorem B983069 : Blo 381763 983069 := bbase (se 3 (by rfl) ⟨184325, by rfl⟩ : syracuseStep 983069 = 368651) (by norm_num)
theorem B819229 : Blo 381763 819229 := bbase (se 3 (by rfl) ⟨153605, by rfl⟩ : syracuseStep 819229 = 307211) (by norm_num)
theorem B1474757 : Blo 381763 1474757 := bbase (se 4 (by rfl) ⟨138258, by rfl⟩ : syracuseStep 1474757 = 276517) (by norm_num)
theorem B917837 : Blo 381763 917837 := bbase (se 3 (by rfl) ⟨172094, by rfl⟩ : syracuseStep 917837 = 344189) (by norm_num)
theorem B688493 : Blo 381763 688493 := bbase (se 3 (by rfl) ⟨129092, by rfl⟩ : syracuseStep 688493 = 258185) (by norm_num)
theorem B688637 : Blo 381763 688637 := bbase (se 3 (by rfl) ⟨129119, by rfl⟩ : syracuseStep 688637 = 258239) (by norm_num)
theorem B819733 : Blo 381763 819733 := bbase (se 6 (by rfl) ⟨19212, by rfl⟩ : syracuseStep 819733 = 38425) (by norm_num)
theorem B688709 : Blo 381763 688709 := bbase (se 4 (by rfl) ⟨64566, by rfl⟩ : syracuseStep 688709 = 129133) (by norm_num)
theorem B918125 : Blo 381763 918125 := bbase (se 3 (by rfl) ⟨172148, by rfl⟩ : syracuseStep 918125 = 344297) (by norm_num)
theorem B459437 : Blo 381763 459437 := bbase (se 3 (by rfl) ⟨86144, by rfl⟩ : syracuseStep 459437 = 172289) (by norm_num)
theorem B3277493 : Blo 381763 3277493 := bbase (se 5 (by rfl) ⟨153632, by rfl⟩ : syracuseStep 3277493 = 307265) (by norm_num)
theorem B2458325 : Blo 381763 2458325 := bbase (se 7 (by rfl) ⟨28808, by rfl⟩ : syracuseStep 2458325 = 57617) (by norm_num)
theorem B1934117 : Blo 381763 1934117 := bbase (se 4 (by rfl) ⟨181323, by rfl⟩ : syracuseStep 1934117 = 362647) (by norm_num)
theorem B2753365 : Blo 381763 2753365 := bbase (se 9 (by rfl) ⟨8066, by rfl⟩ : syracuseStep 2753365 = 16133) (by norm_num)
theorem B983909 : Blo 381763 983909 := bbase (se 4 (by rfl) ⟨92241, by rfl⟩ : syracuseStep 983909 = 184483) (by norm_num)
theorem B2196341 : Blo 381763 2196341 := bbase (se 5 (by rfl) ⟨102953, by rfl⟩ : syracuseStep 2196341 = 205907) (by norm_num)
theorem B1377157 : Blo 381763 1377157 := bbase (se 4 (by rfl) ⟨129108, by rfl⟩ : syracuseStep 1377157 = 258217) (by norm_num)
theorem B1835941 : Blo 381763 1835941 := bbase (se 4 (by rfl) ⟨172119, by rfl⟩ : syracuseStep 1835941 = 344239) (by norm_num)
theorem B689213 : Blo 381763 689213 := bbase (se 3 (by rfl) ⟨129227, by rfl⟩ : syracuseStep 689213 = 258455) (by norm_num)
theorem B3671189 : Blo 381763 3671189 := bbase (se 6 (by rfl) ⟨86043, by rfl⟩ : syracuseStep 3671189 = 172087) (by norm_num)
theorem B1377605 : Blo 381763 1377605 := bbase (se 4 (by rfl) ⟨129150, by rfl⟩ : syracuseStep 1377605 = 258301) (by norm_num)
theorem B460129 : Blo 381763 460129 := bbase (se 2 (by rfl) ⟨172548, by rfl⟩ : syracuseStep 460129 = 345097) (by norm_num)
theorem B525685 : Blo 381763 525685 := bbase (se 5 (by rfl) ⟨24641, by rfl⟩ : syracuseStep 525685 = 49283) (by norm_num)
theorem B820621 : Blo 381763 820621 := bbase (se 3 (by rfl) ⟨153866, by rfl⟩ : syracuseStep 820621 = 307733) (by norm_num)
theorem B460225 : Blo 381763 460225 := bbase (se 2 (by rfl) ⟨172584, by rfl⟩ : syracuseStep 460225 = 345169) (by norm_num)
theorem B984565 : Blo 381763 984565 := bbase (se 5 (by rfl) ⟨46151, by rfl⟩ : syracuseStep 984565 = 92303) (by norm_num)
theorem B394813 : Blo 381763 394813 := bbase (se 3 (by rfl) ⟨74027, by rfl⟩ : syracuseStep 394813 = 148055) (by norm_num)
theorem B3508085 : Blo 381763 3508085 := bbase (se 5 (by rfl) ⟨164441, by rfl⟩ : syracuseStep 3508085 = 328883) (by norm_num)
theorem B821117 : Blo 381763 821117 := bbase (se 3 (by rfl) ⟨153959, by rfl⟩ : syracuseStep 821117 = 307919) (by norm_num)
theorem B1935413 : Blo 381763 1935413 := bbase (se 5 (by rfl) ⟨90722, by rfl⟩ : syracuseStep 1935413 = 181445) (by norm_num)
theorem B1476725 : Blo 381763 1476725 := bbase (se 5 (by rfl) ⟨69221, by rfl⟩ : syracuseStep 1476725 = 138443) (by norm_num)
theorem B5376149 : Blo 381763 5376149 := bbase (se 6 (by rfl) ⟨126003, by rfl⟩ : syracuseStep 5376149 = 252007) (by norm_num)
theorem B1640645 : Blo 381763 1640645 := bbase (se 4 (by rfl) ⟨153810, by rfl⟩ : syracuseStep 1640645 = 307621) (by norm_num)
theorem B461009 : Blo 381763 461009 := bbase (se 2 (by rfl) ⟨172878, by rfl⟩ : syracuseStep 461009 = 345757) (by norm_num)
theorem B2328821 : Blo 381763 2328821 := bbase (se 5 (by rfl) ⟨109163, by rfl⟩ : syracuseStep 2328821 = 218327) (by norm_num)
theorem B1968437 : Blo 381763 1968437 := bbase (se 5 (by rfl) ⟨92270, by rfl⟩ : syracuseStep 1968437 = 184541) (by norm_num)
theorem B3705173 : Blo 381763 3705173 := bbase (se 10 (by rfl) ⟨5427, by rfl⟩ : syracuseStep 3705173 = 10855) (by norm_num)
theorem B2623861 : Blo 381763 2623861 := bbase (se 5 (by rfl) ⟨122993, by rfl⟩ : syracuseStep 2623861 = 245987) (by norm_num)
theorem B461317 : Blo 381763 461317 := bbase (se 4 (by rfl) ⟨43248, by rfl⟩ : syracuseStep 461317 = 86497) (by norm_num)
theorem B920173 : Blo 381763 920173 := bbase (se 3 (by rfl) ⟨172532, by rfl⟩ : syracuseStep 920173 = 345065) (by norm_num)
theorem B822005 : Blo 381763 822005 := bbase (se 5 (by rfl) ⟨38531, by rfl⟩ : syracuseStep 822005 = 77063) (by norm_num)
theorem B822125 : Blo 381763 822125 := bbase (se 3 (by rfl) ⟨154148, by rfl⟩ : syracuseStep 822125 = 308297) (by norm_num)
theorem B461705 : Blo 381763 461705 := bbase (se 2 (by rfl) ⟨173139, by rfl⟩ : syracuseStep 461705 = 346279) (by norm_num)
theorem B592861 : Blo 381763 592861 := bbase (se 3 (by rfl) ⟨111161, by rfl⟩ : syracuseStep 592861 = 222323) (by norm_num)
theorem B1641653 : Blo 381763 1641653 := bbase (se 5 (by rfl) ⟨76952, by rfl⟩ : syracuseStep 1641653 = 153905) (by norm_num)
theorem B462061 : Blo 381763 462061 := bbase (se 3 (by rfl) ⟨86636, by rfl⟩ : syracuseStep 462061 = 173273) (by norm_num)
theorem B494849 : Blo 381763 494849 := bbase (se 2 (by rfl) ⟨185568, by rfl⟩ : syracuseStep 494849 = 371137) (by norm_num)
theorem B1936709 : Blo 381763 1936709 := bbase (se 4 (by rfl) ⟨181566, by rfl⟩ : syracuseStep 1936709 = 363133) (by norm_num)
theorem B429493 : Blo 381763 429493 := bbase (se 5 (by rfl) ⟨20132, by rfl⟩ : syracuseStep 429493 = 40265) (by norm_num)
theorem B429529 : Blo 381763 429529 := bbase (se 2 (by rfl) ⟨161073, by rfl⟩ : syracuseStep 429529 = 322147) (by norm_num)
theorem B822757 : Blo 381763 822757 := bbase (se 4 (by rfl) ⟨77133, by rfl⟩ : syracuseStep 822757 = 154267) (by norm_num)
theorem B429565 : Blo 381763 429565 := bbase (se 3 (by rfl) ⟨80543, by rfl⟩ : syracuseStep 429565 = 161087) (by norm_num)
theorem B4918805 : Blo 381763 4918805 := bbase (se 6 (by rfl) ⟨115284, by rfl⟩ : syracuseStep 4918805 = 230569) (by norm_num)
theorem B429601 : Blo 381763 429601 := bbase (se 2 (by rfl) ⟨161100, by rfl⟩ : syracuseStep 429601 = 322201) (by norm_num)
theorem B462397 : Blo 381763 462397 := bbase (se 3 (by rfl) ⟨86699, by rfl⟩ : syracuseStep 462397 = 173399) (by norm_num)
theorem B429637 : Blo 381763 429637 := bbase (se 4 (by rfl) ⟨40278, by rfl⟩ : syracuseStep 429637 = 80557) (by norm_num)
theorem B429673 : Blo 381763 429673 := bbase (se 2 (by rfl) ⟨161127, by rfl⟩ : syracuseStep 429673 = 322255) (by norm_num)
theorem B429709 : Blo 381763 429709 := bbase (se 3 (by rfl) ⟨80570, by rfl⟩ : syracuseStep 429709 = 161141) (by norm_num)
theorem B429745 : Blo 381763 429745 := bbase (se 2 (by rfl) ⟨161154, by rfl⟩ : syracuseStep 429745 = 322309) (by norm_num)
theorem B659141 : Blo 381763 659141 := bbase (se 4 (by rfl) ⟨61794, by rfl⟩ : syracuseStep 659141 = 123589) (by norm_num)
theorem B429781 : Blo 381763 429781 := bbase (se 7 (by rfl) ⟨5036, by rfl⟩ : syracuseStep 429781 = 10073) (by norm_num)
theorem B429817 : Blo 381763 429817 := bbase (se 2 (by rfl) ⟨161181, by rfl⟩ : syracuseStep 429817 = 322363) (by norm_num)
theorem B429853 : Blo 381763 429853 := bbase (se 3 (by rfl) ⟨80597, by rfl⟩ : syracuseStep 429853 = 161195) (by norm_num)
theorem B429889 : Blo 381763 429889 := bbase (se 2 (by rfl) ⟨161208, by rfl⟩ : syracuseStep 429889 = 322417) (by norm_num)
theorem B429925 : Blo 381763 429925 := bbase (se 4 (by rfl) ⟨40305, by rfl⟩ : syracuseStep 429925 = 80611) (by norm_num)
theorem B429961 : Blo 381763 429961 := bbase (se 2 (by rfl) ⟨161235, by rfl⟩ : syracuseStep 429961 = 322471) (by norm_num)
theorem B429997 : Blo 381763 429997 := bbase (se 3 (by rfl) ⟨80624, by rfl⟩ : syracuseStep 429997 = 161249) (by norm_num)
theorem B2920373 : Blo 381763 2920373 := bbase (se 5 (by rfl) ⟨136892, by rfl⟩ : syracuseStep 2920373 = 273785) (by norm_num)
theorem B430033 : Blo 381763 430033 := bbase (se 2 (by rfl) ⟨161262, by rfl⟩ : syracuseStep 430033 = 322525) (by norm_num)
theorem B430069 : Blo 381763 430069 := bbase (se 5 (by rfl) ⟨20159, by rfl⟩ : syracuseStep 430069 = 40319) (by norm_num)
theorem B430105 : Blo 381763 430105 := bbase (se 2 (by rfl) ⟨161289, by rfl⟩ : syracuseStep 430105 = 322579) (by norm_num)
theorem B725021 : Blo 381763 725021 := bbase (se 3 (by rfl) ⟨135941, by rfl⟩ : syracuseStep 725021 = 271883) (by norm_num)
theorem B692269 : Blo 381763 692269 := bbase (se 3 (by rfl) ⟨129800, by rfl⟩ : syracuseStep 692269 = 259601) (by norm_num)
theorem B430141 : Blo 381763 430141 := bbase (se 3 (by rfl) ⟨80651, by rfl⟩ : syracuseStep 430141 = 161303) (by norm_num)
theorem B430177 : Blo 381763 430177 := bbase (se 2 (by rfl) ⟨161316, by rfl⟩ : syracuseStep 430177 = 322633) (by norm_num)
theorem B430213 : Blo 381763 430213 := bbase (se 4 (by rfl) ⟨40332, by rfl⟩ : syracuseStep 430213 = 80665) (by norm_num)
theorem B430249 : Blo 381763 430249 := bbase (se 2 (by rfl) ⟨161343, by rfl⟩ : syracuseStep 430249 = 322687) (by norm_num)
theorem B430285 : Blo 381763 430285 := bbase (se 3 (by rfl) ⟨80678, by rfl⟩ : syracuseStep 430285 = 161357) (by norm_num)
theorem B430321 : Blo 381763 430321 := bbase (se 2 (by rfl) ⟨161370, by rfl⟩ : syracuseStep 430321 = 322741) (by norm_num)
theorem B430357 : Blo 381763 430357 := bbase (se 6 (by rfl) ⟨10086, by rfl⟩ : syracuseStep 430357 = 20173) (by norm_num)
theorem B430393 : Blo 381763 430393 := bbase (se 2 (by rfl) ⟨161397, by rfl⟩ : syracuseStep 430393 = 322795) (by norm_num)
theorem B430429 : Blo 381763 430429 := bbase (se 3 (by rfl) ⟨80705, by rfl⟩ : syracuseStep 430429 = 161411) (by norm_num)
theorem B823645 : Blo 381763 823645 := bbase (se 3 (by rfl) ⟨154433, by rfl⟩ : syracuseStep 823645 = 308867) (by norm_num)
theorem B430465 : Blo 381763 430465 := bbase (se 2 (by rfl) ⟨161424, by rfl⟩ : syracuseStep 430465 = 322849) (by norm_num)
theorem B430501 : Blo 381763 430501 := bbase (se 4 (by rfl) ⟨40359, by rfl⟩ : syracuseStep 430501 = 80719) (by norm_num)
theorem B463277 : Blo 381763 463277 := bbase (se 3 (by rfl) ⟨86864, by rfl⟩ : syracuseStep 463277 = 173729) (by norm_num)
theorem B430537 : Blo 381763 430537 := bbase (se 2 (by rfl) ⟨161451, by rfl⟩ : syracuseStep 430537 = 322903) (by norm_num)
theorem B823765 : Blo 381763 823765 := bbase (se 7 (by rfl) ⟨9653, by rfl⟩ : syracuseStep 823765 = 19307) (by norm_num)
theorem B430573 : Blo 381763 430573 := bbase (se 3 (by rfl) ⟨80732, by rfl⟩ : syracuseStep 430573 = 161465) (by norm_num)
theorem B2462197 : Blo 381763 2462197 := bbase (se 5 (by rfl) ⟨115415, by rfl⟩ : syracuseStep 2462197 = 230831) (by norm_num)
theorem B692725 : Blo 381763 692725 := bbase (se 5 (by rfl) ⟨32471, by rfl⟩ : syracuseStep 692725 = 64943) (by norm_num)
theorem B1970693 : Blo 381763 1970693 := bbase (se 4 (by rfl) ⟨184752, by rfl⟩ : syracuseStep 1970693 = 369505) (by norm_num)
theorem B430609 : Blo 381763 430609 := bbase (se 2 (by rfl) ⟨161478, by rfl⟩ : syracuseStep 430609 = 322957) (by norm_num)
theorem B430645 : Blo 381763 430645 := bbase (se 5 (by rfl) ⟨20186, by rfl⟩ : syracuseStep 430645 = 40373) (by norm_num)
theorem B1938005 : Blo 381763 1938005 := bbase (se 8 (by rfl) ⟨11355, by rfl⟩ : syracuseStep 1938005 = 22711) (by norm_num)
theorem B430681 : Blo 381763 430681 := bbase (se 2 (by rfl) ⟨161505, by rfl⟩ : syracuseStep 430681 = 323011) (by norm_num)
theorem B430717 : Blo 381763 430717 := bbase (se 3 (by rfl) ⟨80759, by rfl⟩ : syracuseStep 430717 = 161519) (by norm_num)
theorem B430753 : Blo 381763 430753 := bbase (se 2 (by rfl) ⟨161532, by rfl⟩ : syracuseStep 430753 = 323065) (by norm_num)
theorem B430789 : Blo 381763 430789 := bbase (se 4 (by rfl) ⟨40386, by rfl⟩ : syracuseStep 430789 = 80773) (by norm_num)
theorem B430825 : Blo 381763 430825 := bbase (se 2 (by rfl) ⟨161559, by rfl⟩ : syracuseStep 430825 = 323119) (by norm_num)
theorem B725773 : Blo 381763 725773 := bbase (se 3 (by rfl) ⟨136082, by rfl⟩ : syracuseStep 725773 = 272165) (by norm_num)
theorem B430861 : Blo 381763 430861 := bbase (se 3 (by rfl) ⟨80786, by rfl⟩ : syracuseStep 430861 = 161573) (by norm_num)
theorem B430897 : Blo 381763 430897 := bbase (se 2 (by rfl) ⟨161586, by rfl⟩ : syracuseStep 430897 = 323173) (by norm_num)
theorem B1839941 : Blo 381763 1839941 := bbase (se 4 (by rfl) ⟨172494, by rfl⟩ : syracuseStep 1839941 = 344989) (by norm_num)
theorem B430933 : Blo 381763 430933 := bbase (se 9 (by rfl) ⟨1262, by rfl⟩ : syracuseStep 430933 = 2525) (by norm_num)
theorem B430969 : Blo 381763 430969 := bbase (se 2 (by rfl) ⟨161613, by rfl⟩ : syracuseStep 430969 = 323227) (by norm_num)
theorem B725917 : Blo 381763 725917 := bbase (se 3 (by rfl) ⟨136109, by rfl⟩ : syracuseStep 725917 = 272219) (by norm_num)
theorem B431005 : Blo 381763 431005 := bbase (se 3 (by rfl) ⟨80813, by rfl⟩ : syracuseStep 431005 = 161627) (by norm_num)
theorem B1643429 : Blo 381763 1643429 := bbase (se 4 (by rfl) ⟨154071, by rfl⟩ : syracuseStep 1643429 = 308143) (by norm_num)
theorem B431041 : Blo 381763 431041 := bbase (se 2 (by rfl) ⟨161640, by rfl⟩ : syracuseStep 431041 = 323281) (by norm_num)
theorem B922565 : Blo 381763 922565 := bbase (se 4 (by rfl) ⟨86490, by rfl⟩ : syracuseStep 922565 = 172981) (by norm_num)
theorem B431077 : Blo 381763 431077 := bbase (se 4 (by rfl) ⟨40413, by rfl⟩ : syracuseStep 431077 = 80827) (by norm_num)
theorem B431113 : Blo 381763 431113 := bbase (se 2 (by rfl) ⟨161667, by rfl⟩ : syracuseStep 431113 = 323335) (by norm_num)
theorem B431149 : Blo 381763 431149 := bbase (se 3 (by rfl) ⟨80840, by rfl⟩ : syracuseStep 431149 = 161681) (by norm_num)
theorem B726077 : Blo 381763 726077 := bbase (se 3 (by rfl) ⟨136139, by rfl⟩ : syracuseStep 726077 = 272279) (by norm_num)
theorem B431185 : Blo 381763 431185 := bbase (se 2 (by rfl) ⟨161694, by rfl⟩ : syracuseStep 431185 = 323389) (by norm_num)
theorem B922709 : Blo 381763 922709 := bbase (se 8 (by rfl) ⟨5406, by rfl⟩ : syracuseStep 922709 = 10813) (by norm_num)
theorem B431221 : Blo 381763 431221 := bbase (se 5 (by rfl) ⟨20213, by rfl⟩ : syracuseStep 431221 = 40427) (by norm_num)
theorem B431257 : Blo 381763 431257 := bbase (se 2 (by rfl) ⟨161721, by rfl⟩ : syracuseStep 431257 = 323443) (by norm_num)
theorem B431293 : Blo 381763 431293 := bbase (se 3 (by rfl) ⟨80867, by rfl⟩ : syracuseStep 431293 = 161735) (by norm_num)
theorem B726221 : Blo 381763 726221 := bbase (se 3 (by rfl) ⟨136166, by rfl⟩ : syracuseStep 726221 = 272333) (by norm_num)
theorem B431329 : Blo 381763 431329 := bbase (se 2 (by rfl) ⟨161748, by rfl⟩ : syracuseStep 431329 = 323497) (by norm_num)
theorem B431365 : Blo 381763 431365 := bbase (se 4 (by rfl) ⟨40440, by rfl⟩ : syracuseStep 431365 = 80881) (by norm_num)
theorem B431401 : Blo 381763 431401 := bbase (se 2 (by rfl) ⟨161775, by rfl⟩ : syracuseStep 431401 = 323551) (by norm_num)
theorem B431437 : Blo 381763 431437 := bbase (se 3 (by rfl) ⟨80894, by rfl⟩ : syracuseStep 431437 = 161789) (by norm_num)
theorem B431473 : Blo 381763 431473 := bbase (se 2 (by rfl) ⟨161802, by rfl⟩ : syracuseStep 431473 = 323605) (by norm_num)
theorem B431509 : Blo 381763 431509 := bbase (se 6 (by rfl) ⟨10113, by rfl⟩ : syracuseStep 431509 = 20227) (by norm_num)
theorem B431545 : Blo 381763 431545 := bbase (se 2 (by rfl) ⟨161829, by rfl⟩ : syracuseStep 431545 = 323659) (by norm_num)
theorem B431581 : Blo 381763 431581 := bbase (se 3 (by rfl) ⟨80921, by rfl⟩ : syracuseStep 431581 = 161843) (by norm_num)
theorem B726509 : Blo 381763 726509 := bbase (se 3 (by rfl) ⟨136220, by rfl⟩ : syracuseStep 726509 = 272441) (by norm_num)
theorem B431617 : Blo 381763 431617 := bbase (se 2 (by rfl) ⟨161856, by rfl⟩ : syracuseStep 431617 = 323713) (by norm_num)
theorem B431653 : Blo 381763 431653 := bbase (se 4 (by rfl) ⟨40467, by rfl⟩ : syracuseStep 431653 = 80935) (by norm_num)
theorem B693821 : Blo 381763 693821 := bbase (se 3 (by rfl) ⟨130091, by rfl⟩ : syracuseStep 693821 = 260183) (by norm_num)
theorem B431689 : Blo 381763 431689 := bbase (se 2 (by rfl) ⟨161883, by rfl⟩ : syracuseStep 431689 = 323767) (by norm_num)
theorem B431725 : Blo 381763 431725 := bbase (se 3 (by rfl) ⟨80948, by rfl⟩ : syracuseStep 431725 = 161897) (by norm_num)
theorem B726661 : Blo 381763 726661 := bbase (se 4 (by rfl) ⟨68124, by rfl⟩ : syracuseStep 726661 = 136249) (by norm_num)
theorem B431761 : Blo 381763 431761 := bbase (se 2 (by rfl) ⟨161910, by rfl⟩ : syracuseStep 431761 = 323821) (by norm_num)
theorem B431797 : Blo 381763 431797 := bbase (se 5 (by rfl) ⟨20240, by rfl⟩ : syracuseStep 431797 = 40481) (by norm_num)
theorem B1316533 : Blo 381763 1316533 := bbase (se 5 (by rfl) ⟨61712, by rfl⟩ : syracuseStep 1316533 = 123425) (by norm_num)
theorem B431833 : Blo 381763 431833 := bbase (se 2 (by rfl) ⟨161937, by rfl⟩ : syracuseStep 431833 = 323875) (by norm_num)
theorem B431869 : Blo 381763 431869 := bbase (se 3 (by rfl) ⟨80975, by rfl⟩ : syracuseStep 431869 = 161951) (by norm_num)
theorem B431905 : Blo 381763 431905 := bbase (se 2 (by rfl) ⟨161964, by rfl⟩ : syracuseStep 431905 = 323929) (by norm_num)
theorem B431941 : Blo 381763 431941 := bbase (se 4 (by rfl) ⟨40494, by rfl⟩ : syracuseStep 431941 = 80989) (by norm_num)
theorem B694109 : Blo 381763 694109 := bbase (se 3 (by rfl) ⟨130145, by rfl⟩ : syracuseStep 694109 = 260291) (by norm_num)
theorem B1939301 : Blo 381763 1939301 := bbase (se 4 (by rfl) ⟨181809, by rfl⟩ : syracuseStep 1939301 = 363619) (by norm_num)
theorem B431977 : Blo 381763 431977 := bbase (se 2 (by rfl) ⟨161991, by rfl⟩ : syracuseStep 431977 = 323983) (by norm_num)
theorem B432013 : Blo 381763 432013 := bbase (se 3 (by rfl) ⟨81002, by rfl⟩ : syracuseStep 432013 = 162005) (by norm_num)
theorem B432049 : Blo 381763 432049 := bbase (se 2 (by rfl) ⟨162018, by rfl⟩ : syracuseStep 432049 = 324037) (by norm_num)
theorem B726965 : Blo 381763 726965 := bbase (se 5 (by rfl) ⟨34076, by rfl⟩ : syracuseStep 726965 = 68153) (by norm_num)
theorem B432085 : Blo 381763 432085 := bbase (se 7 (by rfl) ⟨5063, by rfl⟩ : syracuseStep 432085 = 10127) (by norm_num)
theorem B432121 : Blo 381763 432121 := bbase (se 2 (by rfl) ⟨162045, by rfl⟩ : syracuseStep 432121 = 324091) (by norm_num)
theorem B432157 : Blo 381763 432157 := bbase (se 3 (by rfl) ⟨81029, by rfl⟩ : syracuseStep 432157 = 162059) (by norm_num)
theorem B432193 : Blo 381763 432193 := bbase (se 2 (by rfl) ⟨162072, by rfl⟩ : syracuseStep 432193 = 324145) (by norm_num)
theorem B432229 : Blo 381763 432229 := bbase (se 4 (by rfl) ⟨40521, by rfl⟩ : syracuseStep 432229 = 81043) (by norm_num)
theorem B432265 : Blo 381763 432265 := bbase (se 2 (by rfl) ⟨162099, by rfl⟩ : syracuseStep 432265 = 324199) (by norm_num)
theorem B432301 : Blo 381763 432301 := bbase (se 3 (by rfl) ⟨81056, by rfl⟩ : syracuseStep 432301 = 162113) (by norm_num)
theorem B432337 : Blo 381763 432337 := bbase (se 2 (by rfl) ⟨162126, by rfl⟩ : syracuseStep 432337 = 324253) (by norm_num)
theorem B432373 : Blo 381763 432373 := bbase (se 5 (by rfl) ⟨20267, by rfl⟩ : syracuseStep 432373 = 40535) (by norm_num)
theorem B432409 : Blo 381763 432409 := bbase (se 2 (by rfl) ⟨162153, by rfl⟩ : syracuseStep 432409 = 324307) (by norm_num)
theorem B432445 : Blo 381763 432445 := bbase (se 3 (by rfl) ⟨81083, by rfl⟩ : syracuseStep 432445 = 162167) (by norm_num)
theorem B432481 : Blo 381763 432481 := bbase (se 2 (by rfl) ⟨162180, by rfl⟩ : syracuseStep 432481 = 324361) (by norm_num)
theorem B432517 : Blo 381763 432517 := bbase (se 4 (by rfl) ⟨40548, by rfl⟩ : syracuseStep 432517 = 81097) (by norm_num)
theorem B432553 : Blo 381763 432553 := bbase (se 2 (by rfl) ⟨162207, by rfl⟩ : syracuseStep 432553 = 324415) (by norm_num)
theorem B432589 : Blo 381763 432589 := bbase (se 3 (by rfl) ⟨81110, by rfl⟩ : syracuseStep 432589 = 162221) (by norm_num)
theorem B432625 : Blo 381763 432625 := bbase (se 2 (by rfl) ⟨162234, by rfl⟩ : syracuseStep 432625 = 324469) (by norm_num)
theorem B432661 : Blo 381763 432661 := bbase (se 6 (by rfl) ⟨10140, by rfl⟩ : syracuseStep 432661 = 20281) (by norm_num)
theorem B432697 : Blo 381763 432697 := bbase (se 2 (by rfl) ⟨162261, by rfl⟩ : syracuseStep 432697 = 324523) (by norm_num)
theorem B432733 : Blo 381763 432733 := bbase (se 3 (by rfl) ⟨81137, by rfl⟩ : syracuseStep 432733 = 162275) (by norm_num)
theorem B432769 : Blo 381763 432769 := bbase (se 2 (by rfl) ⟨162288, by rfl⟩ : syracuseStep 432769 = 324577) (by norm_num)
theorem B727717 : Blo 381763 727717 := bbase (se 4 (by rfl) ⟨68223, by rfl⟩ : syracuseStep 727717 = 136447) (by norm_num)
theorem B432805 : Blo 381763 432805 := bbase (se 4 (by rfl) ⟨40575, by rfl⟩ : syracuseStep 432805 = 81151) (by norm_num)
theorem B432841 : Blo 381763 432841 := bbase (se 2 (by rfl) ⟨162315, by rfl⟩ : syracuseStep 432841 = 324631) (by norm_num)
theorem B432877 : Blo 381763 432877 := bbase (se 3 (by rfl) ⟨81164, by rfl⟩ : syracuseStep 432877 = 162329) (by norm_num)
theorem B1088261 : Blo 381763 1088261 := bbase (se 4 (by rfl) ⟨102024, by rfl⟩ : syracuseStep 1088261 = 204049) (by norm_num)
theorem B432913 : Blo 381763 432913 := bbase (se 2 (by rfl) ⟨162342, by rfl⟩ : syracuseStep 432913 = 324685) (by norm_num)
theorem B727861 : Blo 381763 727861 := bbase (se 5 (by rfl) ⟨34118, by rfl⟩ : syracuseStep 727861 = 68237) (by norm_num)
theorem B432949 : Blo 381763 432949 := bbase (se 5 (by rfl) ⟨20294, by rfl⟩ : syracuseStep 432949 = 40589) (by norm_num)
theorem B432985 : Blo 381763 432985 := bbase (se 2 (by rfl) ⟨162369, by rfl⟩ : syracuseStep 432985 = 324739) (by norm_num)
theorem B433021 : Blo 381763 433021 := bbase (se 3 (by rfl) ⟨81191, by rfl⟩ : syracuseStep 433021 = 162383) (by norm_num)
theorem B859013 : Blo 381763 859013 := bbase (se 4 (by rfl) ⟨80532, by rfl⟩ : syracuseStep 859013 = 161065) (by norm_num)
theorem B433057 : Blo 381763 433057 := bbase (se 2 (by rfl) ⟨162396, by rfl⟩ : syracuseStep 433057 = 324793) (by norm_num)
theorem B433093 : Blo 381763 433093 := bbase (se 4 (by rfl) ⟨40602, by rfl⟩ : syracuseStep 433093 = 81205) (by norm_num)
theorem B859085 : Blo 381763 859085 := bbase (se 3 (by rfl) ⟨161078, by rfl⟩ : syracuseStep 859085 = 322157) (by norm_num)
theorem B728021 : Blo 381763 728021 := bbase (se 7 (by rfl) ⟨8531, by rfl⟩ : syracuseStep 728021 = 17063) (by norm_num)
theorem B433129 : Blo 381763 433129 := bbase (se 2 (by rfl) ⟨162423, by rfl⟩ : syracuseStep 433129 = 324847) (by norm_num)
theorem B433165 : Blo 381763 433165 := bbase (se 3 (by rfl) ⟨81218, by rfl⟩ : syracuseStep 433165 = 162437) (by norm_num)
theorem B859157 : Blo 381763 859157 := bbase (se 6 (by rfl) ⟨20136, by rfl⟩ : syracuseStep 859157 = 40273) (by norm_num)
theorem B924709 : Blo 381763 924709 := bbase (se 4 (by rfl) ⟨86691, by rfl⟩ : syracuseStep 924709 = 173383) (by norm_num)
theorem B433201 : Blo 381763 433201 := bbase (se 2 (by rfl) ⟨162450, by rfl⟩ : syracuseStep 433201 = 324901) (by norm_num)
theorem B433237 : Blo 381763 433237 := bbase (se 8 (by rfl) ⟨2538, by rfl⟩ : syracuseStep 433237 = 5077) (by norm_num)
theorem B859229 : Blo 381763 859229 := bbase (se 3 (by rfl) ⟨161105, by rfl⟩ : syracuseStep 859229 = 322211) (by norm_num)
theorem B728165 : Blo 381763 728165 := bbase (se 4 (by rfl) ⟨68265, by rfl⟩ : syracuseStep 728165 = 136531) (by norm_num)
theorem B1940597 : Blo 381763 1940597 := bbase (se 5 (by rfl) ⟨90965, by rfl⟩ : syracuseStep 1940597 = 181931) (by norm_num)
theorem B433273 : Blo 381763 433273 := bbase (se 2 (by rfl) ⟨162477, by rfl⟩ : syracuseStep 433273 = 324955) (by norm_num)
theorem B433309 : Blo 381763 433309 := bbase (se 3 (by rfl) ⟨81245, by rfl⟩ : syracuseStep 433309 = 162491) (by norm_num)
theorem B859301 : Blo 381763 859301 := bbase (se 4 (by rfl) ⟨80559, by rfl⟩ : syracuseStep 859301 = 161119) (by norm_num)
theorem B433345 : Blo 381763 433345 := bbase (se 2 (by rfl) ⟨162504, by rfl⟩ : syracuseStep 433345 = 325009) (by norm_num)
theorem B433381 : Blo 381763 433381 := bbase (se 4 (by rfl) ⟨40629, by rfl⟩ : syracuseStep 433381 = 81259) (by norm_num)
theorem B859373 : Blo 381763 859373 := bbase (se 3 (by rfl) ⟨161132, by rfl⟩ : syracuseStep 859373 = 322265) (by norm_num)
theorem B433417 : Blo 381763 433417 := bbase (se 2 (by rfl) ⟨162531, by rfl⟩ : syracuseStep 433417 = 325063) (by norm_num)
theorem B433453 : Blo 381763 433453 := bbase (se 3 (by rfl) ⟨81272, by rfl⟩ : syracuseStep 433453 = 162545) (by norm_num)
theorem B859445 : Blo 381763 859445 := bbase (se 5 (by rfl) ⟨40286, by rfl⟩ : syracuseStep 859445 = 80573) (by norm_num)
theorem B433489 : Blo 381763 433489 := bbase (se 2 (by rfl) ⟨162558, by rfl⟩ : syracuseStep 433489 = 325117) (by norm_num)
theorem B433525 : Blo 381763 433525 := bbase (se 5 (by rfl) ⟨20321, by rfl⟩ : syracuseStep 433525 = 40643) (by norm_num)
theorem B859517 : Blo 381763 859517 := bbase (se 3 (by rfl) ⟨161159, by rfl⟩ : syracuseStep 859517 = 322319) (by norm_num)
theorem B728453 : Blo 381763 728453 := bbase (se 4 (by rfl) ⟨68292, by rfl⟩ : syracuseStep 728453 = 136585) (by norm_num)
theorem B433561 : Blo 381763 433561 := bbase (se 2 (by rfl) ⟨162585, by rfl⟩ : syracuseStep 433561 = 325171) (by norm_num)
theorem B433597 : Blo 381763 433597 := bbase (se 3 (by rfl) ⟨81299, by rfl⟩ : syracuseStep 433597 = 162599) (by norm_num)
theorem B859589 : Blo 381763 859589 := bbase (se 4 (by rfl) ⟨80586, by rfl⟩ : syracuseStep 859589 = 161173) (by norm_num)
theorem B433633 : Blo 381763 433633 := bbase (se 2 (by rfl) ⟨162612, by rfl⟩ : syracuseStep 433633 = 325225) (by norm_num)
theorem B433669 : Blo 381763 433669 := bbase (se 4 (by rfl) ⟨40656, by rfl⟩ : syracuseStep 433669 = 81313) (by norm_num)
theorem B859661 : Blo 381763 859661 := bbase (se 3 (by rfl) ⟨161186, by rfl⟩ : syracuseStep 859661 = 322373) (by norm_num)
theorem B728605 : Blo 381763 728605 := bbase (se 3 (by rfl) ⟨136613, by rfl⟩ : syracuseStep 728605 = 273227) (by norm_num)
theorem B433705 : Blo 381763 433705 := bbase (se 2 (by rfl) ⟨162639, by rfl⟩ : syracuseStep 433705 = 325279) (by norm_num)
theorem B1121861 : Blo 381763 1121861 := bbase (se 4 (by rfl) ⟨105174, by rfl⟩ : syracuseStep 1121861 = 210349) (by norm_num)
theorem B433741 : Blo 381763 433741 := bbase (se 3 (by rfl) ⟨81326, by rfl⟩ : syracuseStep 433741 = 162653) (by norm_num)
theorem B859733 : Blo 381763 859733 := bbase (se 8 (by rfl) ⟨5037, by rfl⟩ : syracuseStep 859733 = 10075) (by norm_num)
theorem B433777 : Blo 381763 433777 := bbase (se 2 (by rfl) ⟨162666, by rfl⟩ : syracuseStep 433777 = 325333) (by norm_num)
theorem B433813 : Blo 381763 433813 := bbase (se 6 (by rfl) ⟨10167, by rfl⟩ : syracuseStep 433813 = 20335) (by norm_num)
theorem B859805 : Blo 381763 859805 := bbase (se 3 (by rfl) ⟨161213, by rfl⟩ : syracuseStep 859805 = 322427) (by norm_num)
theorem B433849 : Blo 381763 433849 := bbase (se 2 (by rfl) ⟨162693, by rfl⟩ : syracuseStep 433849 = 325387) (by norm_num)
theorem B433885 : Blo 381763 433885 := bbase (se 3 (by rfl) ⟨81353, by rfl⟩ : syracuseStep 433885 = 162707) (by norm_num)
theorem B859877 : Blo 381763 859877 := bbase (se 4 (by rfl) ⟨80613, by rfl⟩ : syracuseStep 859877 = 161227) (by norm_num)
theorem B433921 : Blo 381763 433921 := bbase (se 2 (by rfl) ⟨162720, by rfl⟩ : syracuseStep 433921 = 325441) (by norm_num)
theorem B433957 : Blo 381763 433957 := bbase (se 4 (by rfl) ⟨40683, by rfl⟩ : syracuseStep 433957 = 81367) (by norm_num)
theorem B859949 : Blo 381763 859949 := bbase (se 3 (by rfl) ⟨161240, by rfl⟩ : syracuseStep 859949 = 322481) (by norm_num)
theorem B728909 : Blo 381763 728909 := bbase (se 3 (by rfl) ⟨136670, by rfl⟩ : syracuseStep 728909 = 273341) (by norm_num)
theorem B1449845 : Blo 381763 1449845 := bbase (se 5 (by rfl) ⟨67961, by rfl⟩ : syracuseStep 1449845 = 135923) (by norm_num)
theorem B860021 : Blo 381763 860021 := bbase (se 5 (by rfl) ⟨40313, by rfl⟩ : syracuseStep 860021 = 80627) (by norm_num)
theorem B1089445 : Blo 381763 1089445 := bbase (se 4 (by rfl) ⟨102135, by rfl⟩ : syracuseStep 1089445 = 204271) (by norm_num)
theorem B860093 : Blo 381763 860093 := bbase (se 3 (by rfl) ⟨161267, by rfl⟩ : syracuseStep 860093 = 322535) (by norm_num)
theorem B2957269 : Blo 381763 2957269 := bbase (se 7 (by rfl) ⟨34655, by rfl⟩ : syracuseStep 2957269 = 69311) (by norm_num)
theorem B860165 : Blo 381763 860165 := bbase (se 4 (by rfl) ⟨80640, by rfl⟩ : syracuseStep 860165 = 161281) (by norm_num)
theorem B1089605 : Blo 381763 1089605 := bbase (se 4 (by rfl) ⟨102150, by rfl⟩ : syracuseStep 1089605 = 204301) (by norm_num)
theorem B860237 : Blo 381763 860237 := bbase (se 3 (by rfl) ⟨161294, by rfl⟩ : syracuseStep 860237 = 322589) (by norm_num)
theorem B1450133 : Blo 381763 1450133 := bbase (se 6 (by rfl) ⟨33987, by rfl⟩ : syracuseStep 1450133 = 67975) (by norm_num)
theorem B860309 : Blo 381763 860309 := bbase (se 6 (by rfl) ⟨20163, by rfl⟩ : syracuseStep 860309 = 40327) (by norm_num)
theorem B860381 : Blo 381763 860381 := bbase (se 3 (by rfl) ⟨161321, by rfl⟩ : syracuseStep 860381 = 322643) (by norm_num)
theorem B860453 : Blo 381763 860453 := bbase (se 4 (by rfl) ⟨80667, by rfl⟩ : syracuseStep 860453 = 161335) (by norm_num)
theorem B1089845 : Blo 381763 1089845 := bbase (se 5 (by rfl) ⟨51086, by rfl⟩ : syracuseStep 1089845 = 102173) (by norm_num)
theorem B860525 : Blo 381763 860525 := bbase (se 3 (by rfl) ⟨161348, by rfl⟩ : syracuseStep 860525 = 322697) (by norm_num)
theorem B1843573 : Blo 381763 1843573 := bbase (se 5 (by rfl) ⟨86417, by rfl⟩ : syracuseStep 1843573 = 172835) (by norm_num)
theorem B1941893 : Blo 381763 1941893 := bbase (se 4 (by rfl) ⟨182052, by rfl⟩ : syracuseStep 1941893 = 364105) (by norm_num)
theorem B926093 : Blo 381763 926093 := bbase (se 3 (by rfl) ⟨173642, by rfl⟩ : syracuseStep 926093 = 347285) (by norm_num)
theorem B926101 : Blo 381763 926101 := bbase (se 6 (by rfl) ⟨21705, by rfl⟩ : syracuseStep 926101 = 43411) (by norm_num)
theorem B860597 : Blo 381763 860597 := bbase (se 5 (by rfl) ⟨40340, by rfl⟩ : syracuseStep 860597 = 80681) (by norm_num)
theorem B1090037 : Blo 381763 1090037 := bbase (se 5 (by rfl) ⟨51095, by rfl⟩ : syracuseStep 1090037 = 102191) (by norm_num)
theorem B860669 : Blo 381763 860669 := bbase (se 3 (by rfl) ⟨161375, by rfl⟩ : syracuseStep 860669 = 322751) (by norm_num)
theorem B729661 : Blo 381763 729661 := bbase (se 3 (by rfl) ⟨136811, by rfl⟩ : syracuseStep 729661 = 273623) (by norm_num)
theorem B860741 : Blo 381763 860741 := bbase (se 4 (by rfl) ⟨80694, by rfl⟩ : syracuseStep 860741 = 161389) (by norm_num)
theorem B860813 : Blo 381763 860813 := bbase (se 3 (by rfl) ⟨161402, by rfl⟩ : syracuseStep 860813 = 322805) (by norm_num)
theorem B729805 : Blo 381763 729805 := bbase (se 3 (by rfl) ⟨136838, by rfl⟩ : syracuseStep 729805 = 273677) (by norm_num)
theorem B860885 : Blo 381763 860885 := bbase (se 7 (by rfl) ⟨10088, by rfl⟩ : syracuseStep 860885 = 20177) (by norm_num)
theorem B860957 : Blo 381763 860957 := bbase (se 3 (by rfl) ⟨161429, by rfl⟩ : syracuseStep 860957 = 322859) (by norm_num)
theorem B861029 : Blo 381763 861029 := bbase (se 4 (by rfl) ⟨80721, by rfl⟩ : syracuseStep 861029 = 161443) (by norm_num)
theorem B729965 : Blo 381763 729965 := bbase (se 3 (by rfl) ⟨136868, by rfl⟩ : syracuseStep 729965 = 273737) (by norm_num)
theorem B861101 : Blo 381763 861101 := bbase (se 3 (by rfl) ⟨161456, by rfl⟩ : syracuseStep 861101 = 322913) (by norm_num)
theorem B861173 : Blo 381763 861173 := bbase (se 5 (by rfl) ⟨40367, by rfl⟩ : syracuseStep 861173 = 80735) (by norm_num)
theorem B1385461 : Blo 381763 1385461 := bbase (se 5 (by rfl) ⟨64943, by rfl⟩ : syracuseStep 1385461 = 129887) (by norm_num)
theorem B730109 : Blo 381763 730109 := bbase (se 3 (by rfl) ⟨136895, by rfl⟩ : syracuseStep 730109 = 273791) (by norm_num)
theorem B861245 : Blo 381763 861245 := bbase (se 3 (by rfl) ⟨161483, by rfl⟩ : syracuseStep 861245 = 322967) (by norm_num)
theorem B1647701 : Blo 381763 1647701 := bbase (se 8 (by rfl) ⟨9654, by rfl⟩ : syracuseStep 1647701 = 19309) (by norm_num)
theorem B861317 : Blo 381763 861317 := bbase (se 4 (by rfl) ⟨80748, by rfl⟩ : syracuseStep 861317 = 161497) (by norm_num)
theorem B861389 : Blo 381763 861389 := bbase (se 3 (by rfl) ⟨161510, by rfl⟩ : syracuseStep 861389 = 323021) (by norm_num)
theorem B435413 : Blo 381763 435413 := bbase (se 7 (by rfl) ⟨5102, by rfl⟩ : syracuseStep 435413 = 10205) (by norm_num)
theorem B861461 : Blo 381763 861461 := bbase (se 6 (by rfl) ⟨20190, by rfl⟩ : syracuseStep 861461 = 40381) (by norm_num)
theorem B730397 : Blo 381763 730397 := bbase (se 3 (by rfl) ⟨136949, by rfl⟩ : syracuseStep 730397 = 273899) (by norm_num)
theorem B1451317 : Blo 381763 1451317 := bbase (se 5 (by rfl) ⟨68030, by rfl⟩ : syracuseStep 1451317 = 136061) (by norm_num)
theorem B861533 : Blo 381763 861533 := bbase (se 3 (by rfl) ⟨161537, by rfl⟩ : syracuseStep 861533 = 323075) (by norm_num)
theorem B861605 : Blo 381763 861605 := bbase (se 4 (by rfl) ⟨80775, by rfl⟩ : syracuseStep 861605 = 161551) (by norm_num)
theorem B730549 : Blo 381763 730549 := bbase (se 5 (by rfl) ⟨34244, by rfl⟩ : syracuseStep 730549 = 68489) (by norm_num)
theorem B435665 : Blo 381763 435665 := bbase (se 2 (by rfl) ⟨163374, by rfl⟩ : syracuseStep 435665 = 326749) (by norm_num)
theorem B1091029 : Blo 381763 1091029 := bbase (se 7 (by rfl) ⟨12785, by rfl⟩ : syracuseStep 1091029 = 25571) (by norm_num)
theorem B861677 : Blo 381763 861677 := bbase (se 3 (by rfl) ⟨161564, by rfl⟩ : syracuseStep 861677 = 323129) (by norm_num)
theorem B861749 : Blo 381763 861749 := bbase (se 5 (by rfl) ⟨40394, by rfl⟩ : syracuseStep 861749 = 80789) (by norm_num)
theorem B1451621 : Blo 381763 1451621 := bbase (se 4 (by rfl) ⟨136089, by rfl⟩ : syracuseStep 1451621 = 272179) (by norm_num)
theorem B861821 : Blo 381763 861821 := bbase (se 3 (by rfl) ⟨161591, by rfl⟩ : syracuseStep 861821 = 323183) (by norm_num)
theorem B1943189 : Blo 381763 1943189 := bbase (se 6 (by rfl) ⟨45543, by rfl⟩ : syracuseStep 1943189 = 91087) (by norm_num)
theorem B861893 : Blo 381763 861893 := bbase (se 4 (by rfl) ⟨80802, by rfl⟩ : syracuseStep 861893 = 161605) (by norm_num)
theorem B730853 : Blo 381763 730853 := bbase (se 4 (by rfl) ⟨68517, by rfl⟩ : syracuseStep 730853 = 137035) (by norm_num)
theorem B861965 : Blo 381763 861965 := bbase (se 3 (by rfl) ⟨161618, by rfl⟩ : syracuseStep 861965 = 323237) (by norm_num)
theorem B829205 : Blo 381763 829205 := bbase (se 6 (by rfl) ⟨19434, by rfl⟩ : syracuseStep 829205 = 38869) (by norm_num)
theorem B862037 : Blo 381763 862037 := bbase (se 9 (by rfl) ⟨2525, by rfl⟩ : syracuseStep 862037 = 5051) (by norm_num)
theorem B829325 : Blo 381763 829325 := bbase (se 3 (by rfl) ⟨155498, by rfl⟩ : syracuseStep 829325 = 310997) (by norm_num)
theorem B862109 : Blo 381763 862109 := bbase (se 3 (by rfl) ⟨161645, by rfl⟩ : syracuseStep 862109 = 323291) (by norm_num)
theorem B862181 : Blo 381763 862181 := bbase (se 4 (by rfl) ⟨80829, by rfl⟩ : syracuseStep 862181 = 161659) (by norm_num)
theorem B862253 : Blo 381763 862253 := bbase (se 3 (by rfl) ⟨161672, by rfl⟩ : syracuseStep 862253 = 323345) (by norm_num)
theorem B862325 : Blo 381763 862325 := bbase (se 5 (by rfl) ⟨40421, by rfl⟩ : syracuseStep 862325 = 80843) (by norm_num)
theorem B862397 : Blo 381763 862397 := bbase (se 3 (by rfl) ⟨161699, by rfl⟩ : syracuseStep 862397 = 323399) (by norm_num)
theorem B862469 : Blo 381763 862469 := bbase (se 4 (by rfl) ⟨80856, by rfl⟩ : syracuseStep 862469 = 161713) (by norm_num)
theorem B862541 : Blo 381763 862541 := bbase (se 3 (by rfl) ⟨161726, by rfl⟩ : syracuseStep 862541 = 323453) (by norm_num)
theorem B862613 : Blo 381763 862613 := bbase (se 6 (by rfl) ⟨20217, by rfl⟩ : syracuseStep 862613 = 40435) (by norm_num)
theorem B731605 : Blo 381763 731605 := bbase (se 7 (by rfl) ⟨8573, by rfl⟩ : syracuseStep 731605 = 17147) (by norm_num)
theorem B862685 : Blo 381763 862685 := bbase (se 3 (by rfl) ⟨161753, by rfl⟩ : syracuseStep 862685 = 323507) (by norm_num)
theorem B1288709 : Blo 381763 1288709 := bbase (se 4 (by rfl) ⟨120816, by rfl⟩ : syracuseStep 1288709 = 241633) (by norm_num)
theorem B862757 : Blo 381763 862757 := bbase (se 4 (by rfl) ⟨80883, by rfl⟩ : syracuseStep 862757 = 161767) (by norm_num)
theorem B1092133 : Blo 381763 1092133 := bbase (se 4 (by rfl) ⟨102387, by rfl⟩ : syracuseStep 1092133 = 204775) (by norm_num)
theorem B1878565 : Blo 381763 1878565 := bbase (se 4 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 1878565 = 352231) (by norm_num)
theorem B731749 : Blo 381763 731749 := bbase (se 4 (by rfl) ⟨68601, by rfl⟩ : syracuseStep 731749 = 137203) (by norm_num)
theorem B862829 : Blo 381763 862829 := bbase (se 3 (by rfl) ⟨161780, by rfl⟩ : syracuseStep 862829 = 323561) (by norm_num)
theorem B862901 : Blo 381763 862901 := bbase (se 5 (by rfl) ⟨40448, by rfl⟩ : syracuseStep 862901 = 80897) (by norm_num)
theorem B862973 : Blo 381763 862973 := bbase (se 3 (by rfl) ⟨161807, by rfl⟩ : syracuseStep 862973 = 323615) (by norm_num)
theorem B731909 : Blo 381763 731909 := bbase (se 4 (by rfl) ⟨68616, by rfl⟩ : syracuseStep 731909 = 137233) (by norm_num)
theorem B863045 : Blo 381763 863045 := bbase (se 4 (by rfl) ⟨80910, by rfl⟩ : syracuseStep 863045 = 161821) (by norm_num)
theorem B1223525 : Blo 381763 1223525 := bbase (se 4 (by rfl) ⟨114705, by rfl⟩ : syracuseStep 1223525 = 229411) (by norm_num)
theorem B437101 : Blo 381763 437101 := bbase (se 3 (by rfl) ⟨81956, by rfl⟩ : syracuseStep 437101 = 163913) (by norm_num)
theorem B863117 : Blo 381763 863117 := bbase (se 3 (by rfl) ⟨161834, by rfl⟩ : syracuseStep 863117 = 323669) (by norm_num)
theorem B732053 : Blo 381763 732053 := bbase (se 6 (by rfl) ⟨17157, by rfl⟩ : syracuseStep 732053 = 34315) (by norm_num)
theorem B1944485 : Blo 381763 1944485 := bbase (se 4 (by rfl) ⟨182295, by rfl⟩ : syracuseStep 1944485 = 364591) (by norm_num)
theorem B1289141 : Blo 381763 1289141 := bbase (se 5 (by rfl) ⟨60428, by rfl⟩ : syracuseStep 1289141 = 120857) (by norm_num)
theorem B863189 : Blo 381763 863189 := bbase (se 7 (by rfl) ⟨10115, by rfl⟩ : syracuseStep 863189 = 20231) (by norm_num)
theorem B863261 : Blo 381763 863261 := bbase (se 3 (by rfl) ⟨161861, by rfl⟩ : syracuseStep 863261 = 323723) (by norm_num)
theorem B863333 : Blo 381763 863333 := bbase (se 4 (by rfl) ⟨80937, by rfl⟩ : syracuseStep 863333 = 161875) (by norm_num)
theorem B666749 : Blo 381763 666749 := bbase (se 3 (by rfl) ⟨125015, by rfl⟩ : syracuseStep 666749 = 250031) (by norm_num)
theorem B863405 : Blo 381763 863405 := bbase (se 3 (by rfl) ⟨161888, by rfl⟩ : syracuseStep 863405 = 323777) (by norm_num)
theorem B732341 : Blo 381763 732341 := bbase (se 5 (by rfl) ⟨34328, by rfl⟩ : syracuseStep 732341 = 68657) (by norm_num)
theorem B863477 : Blo 381763 863477 := bbase (se 5 (by rfl) ⟨40475, by rfl⟩ : syracuseStep 863477 = 80951) (by norm_num)
theorem B863549 : Blo 381763 863549 := bbase (se 3 (by rfl) ⟨161915, by rfl⟩ : syracuseStep 863549 = 323831) (by norm_num)
theorem B1289573 : Blo 381763 1289573 := bbase (se 4 (by rfl) ⟨120897, by rfl⟩ : syracuseStep 1289573 = 241795) (by norm_num)
theorem B863621 : Blo 381763 863621 := bbase (se 4 (by rfl) ⟨80964, by rfl⟩ : syracuseStep 863621 = 161929) (by norm_num)
theorem B863693 : Blo 381763 863693 := bbase (se 3 (by rfl) ⟨161942, by rfl⟩ : syracuseStep 863693 = 323885) (by norm_num)
theorem B863765 : Blo 381763 863765 := bbase (se 6 (by rfl) ⟨20244, by rfl⟩ : syracuseStep 863765 = 40489) (by norm_num)
theorem B2928149 : Blo 381763 2928149 := bbase (se 6 (by rfl) ⟨68628, by rfl⟩ : syracuseStep 2928149 = 137257) (by norm_num)
theorem B863837 : Blo 381763 863837 := bbase (se 3 (by rfl) ⟨161969, by rfl⟩ : syracuseStep 863837 = 323939) (by norm_num)
theorem B1453733 : Blo 381763 1453733 := bbase (se 4 (by rfl) ⟨136287, by rfl⟩ : syracuseStep 1453733 = 272575) (by norm_num)
theorem B863909 : Blo 381763 863909 := bbase (se 4 (by rfl) ⟨80991, by rfl⟩ : syracuseStep 863909 = 161983) (by norm_num)
theorem B863981 : Blo 381763 863981 := bbase (se 3 (by rfl) ⟨161996, by rfl⟩ : syracuseStep 863981 = 323993) (by norm_num)
theorem B1290005 : Blo 381763 1290005 := bbase (se 6 (by rfl) ⟨30234, by rfl⟩ : syracuseStep 1290005 = 60469) (by norm_num)
theorem B864053 : Blo 381763 864053 := bbase (se 5 (by rfl) ⟨40502, by rfl⟩ : syracuseStep 864053 = 81005) (by norm_num)
theorem B864125 : Blo 381763 864125 := bbase (se 3 (by rfl) ⟨162023, by rfl⟩ : syracuseStep 864125 = 324047) (by norm_num)
theorem B3125141 : Blo 381763 3125141 := bbase (se 6 (by rfl) ⟨73245, by rfl⟩ : syracuseStep 3125141 = 146491) (by norm_num)
theorem B1454021 : Blo 381763 1454021 := bbase (se 4 (by rfl) ⟨136314, by rfl⟩ : syracuseStep 1454021 = 272629) (by norm_num)
theorem B864197 : Blo 381763 864197 := bbase (se 4 (by rfl) ⟨81018, by rfl⟩ : syracuseStep 864197 = 162037) (by norm_num)
theorem B1093637 : Blo 381763 1093637 := bbase (se 4 (by rfl) ⟨102528, by rfl⟩ : syracuseStep 1093637 = 205057) (by norm_num)
theorem B864269 : Blo 381763 864269 := bbase (se 3 (by rfl) ⟨162050, by rfl⟩ : syracuseStep 864269 = 324101) (by norm_num)
theorem B438305 : Blo 381763 438305 := bbase (se 2 (by rfl) ⟨164364, by rfl⟩ : syracuseStep 438305 = 328729) (by norm_num)
theorem B864341 : Blo 381763 864341 := bbase (se 8 (by rfl) ⟨5064, by rfl⟩ : syracuseStep 864341 = 10129) (by norm_num)
theorem B1388677 : Blo 381763 1388677 := bbase (se 4 (by rfl) ⟨130188, by rfl⟩ : syracuseStep 1388677 = 260377) (by norm_num)
theorem B864413 : Blo 381763 864413 := bbase (se 3 (by rfl) ⟨162077, by rfl⟩ : syracuseStep 864413 = 324155) (by norm_num)
theorem B2076853 : Blo 381763 2076853 := bbase (se 5 (by rfl) ⟨97352, by rfl⟩ : syracuseStep 2076853 = 194705) (by norm_num)
theorem B1945781 : Blo 381763 1945781 := bbase (se 5 (by rfl) ⟨91208, by rfl⟩ : syracuseStep 1945781 = 182417) (by norm_num)
theorem B1290437 : Blo 381763 1290437 := bbase (se 4 (by rfl) ⟨120978, by rfl⟩ : syracuseStep 1290437 = 241957) (by norm_num)
theorem B864485 : Blo 381763 864485 := bbase (se 4 (by rfl) ⟨81045, by rfl⟩ : syracuseStep 864485 = 162091) (by norm_num)
theorem B700693 : Blo 381763 700693 := bbase (se 6 (by rfl) ⟨16422, by rfl⟩ : syracuseStep 700693 = 32845) (by norm_num)
theorem B864557 : Blo 381763 864557 := bbase (se 3 (by rfl) ⟨162104, by rfl⟩ : syracuseStep 864557 = 324209) (by norm_num)
theorem B864629 : Blo 381763 864629 := bbase (se 5 (by rfl) ⟨40529, by rfl⟩ : syracuseStep 864629 = 81059) (by norm_num)
theorem B864701 : Blo 381763 864701 := bbase (se 3 (by rfl) ⟨162131, by rfl⟩ : syracuseStep 864701 = 324263) (by norm_num)
theorem B864773 : Blo 381763 864773 := bbase (se 4 (by rfl) ⟨81072, by rfl⟩ : syracuseStep 864773 = 162145) (by norm_num)
theorem B864845 : Blo 381763 864845 := bbase (se 3 (by rfl) ⟨162158, by rfl⟩ : syracuseStep 864845 = 324317) (by norm_num)
theorem B438889 : Blo 381763 438889 := bbase (se 2 (by rfl) ⟨164583, by rfl⟩ : syracuseStep 438889 = 329167) (by norm_num)
theorem B1290869 : Blo 381763 1290869 := bbase (se 5 (by rfl) ⟨60509, by rfl⟩ : syracuseStep 1290869 = 121019) (by norm_num)
theorem B864917 : Blo 381763 864917 := bbase (se 6 (by rfl) ⟨20271, by rfl⟩ : syracuseStep 864917 = 40543) (by norm_num)
theorem B438953 : Blo 381763 438953 := bbase (se 2 (by rfl) ⟨164607, by rfl⟩ : syracuseStep 438953 = 329215) (by norm_num)
theorem B438989 : Blo 381763 438989 := bbase (se 3 (by rfl) ⟨82310, by rfl⟩ : syracuseStep 438989 = 164621) (by norm_num)
theorem B3683029 : Blo 381763 3683029 := bbase (se 7 (by rfl) ⟨43160, by rfl⟩ : syracuseStep 3683029 = 86321) (by norm_num)
theorem B864989 : Blo 381763 864989 := bbase (se 3 (by rfl) ⟨162185, by rfl⟩ : syracuseStep 864989 = 324371) (by norm_num)
theorem B865061 : Blo 381763 865061 := bbase (se 4 (by rfl) ⟨81099, by rfl⟩ : syracuseStep 865061 = 162199) (by norm_num)
theorem B1389413 : Blo 381763 1389413 := bbase (se 4 (by rfl) ⟨130257, by rfl⟩ : syracuseStep 1389413 = 260515) (by norm_num)
theorem B865133 : Blo 381763 865133 := bbase (se 3 (by rfl) ⟨162212, by rfl⟩ : syracuseStep 865133 = 324425) (by norm_num)
theorem B2077589 : Blo 381763 2077589 := bbase (se 6 (by rfl) ⟨48693, by rfl⟩ : syracuseStep 2077589 = 97387) (by norm_num)
theorem B865205 : Blo 381763 865205 := bbase (se 5 (by rfl) ⟨40556, by rfl⟩ : syracuseStep 865205 = 81113) (by norm_num)
theorem B12530645 : Blo 381763 12530645 := bbase (se 7 (by rfl) ⟨146843, by rfl⟩ : syracuseStep 12530645 = 293687) (by norm_num)
theorem B865277 : Blo 381763 865277 := bbase (se 3 (by rfl) ⟨162239, by rfl⟩ : syracuseStep 865277 = 324479) (by norm_num)
theorem B1291301 : Blo 381763 1291301 := bbase (se 4 (by rfl) ⟨121059, by rfl⟩ : syracuseStep 1291301 = 242119) (by norm_num)
theorem B865349 : Blo 381763 865349 := bbase (se 4 (by rfl) ⟨81126, by rfl⟩ : syracuseStep 865349 = 162253) (by norm_num)
theorem B1455205 : Blo 381763 1455205 := bbase (se 4 (by rfl) ⟨136425, by rfl⟩ : syracuseStep 1455205 = 272851) (by norm_num)
theorem B865421 : Blo 381763 865421 := bbase (se 3 (by rfl) ⟨162266, by rfl⟩ : syracuseStep 865421 = 324533) (by norm_num)
theorem B865493 : Blo 381763 865493 := bbase (se 7 (by rfl) ⟨10142, by rfl⟩ : syracuseStep 865493 = 20285) (by norm_num)
theorem B865565 : Blo 381763 865565 := bbase (se 3 (by rfl) ⟨162293, by rfl⟩ : syracuseStep 865565 = 324587) (by norm_num)
theorem B865637 : Blo 381763 865637 := bbase (se 4 (by rfl) ⟨81153, by rfl⟩ : syracuseStep 865637 = 162307) (by norm_num)
theorem B1455509 : Blo 381763 1455509 := bbase (se 6 (by rfl) ⟨34113, by rfl⟩ : syracuseStep 1455509 = 68227) (by norm_num)
theorem B865709 : Blo 381763 865709 := bbase (se 3 (by rfl) ⟨162320, by rfl⟩ : syracuseStep 865709 = 324641) (by norm_num)
theorem B734653 : Blo 381763 734653 := bbase (se 3 (by rfl) ⟨137747, by rfl⟩ : syracuseStep 734653 = 275495) (by norm_num)
theorem B1947077 : Blo 381763 1947077 := bbase (se 4 (by rfl) ⟨182538, by rfl⟩ : syracuseStep 1947077 = 365077) (by norm_num)
theorem B1291733 : Blo 381763 1291733 := bbase (se 7 (by rfl) ⟨15137, by rfl⟩ : syracuseStep 1291733 = 30275) (by norm_num)
theorem B865781 : Blo 381763 865781 := bbase (se 5 (by rfl) ⟨40583, by rfl⟩ : syracuseStep 865781 = 81167) (by norm_num)
theorem B2635253 : Blo 381763 2635253 := bbase (se 5 (by rfl) ⟨123527, by rfl⟩ : syracuseStep 2635253 = 247055) (by norm_num)
theorem B439825 : Blo 381763 439825 := bbase (se 2 (by rfl) ⟨164934, by rfl⟩ : syracuseStep 439825 = 329869) (by norm_num)
theorem B1095221 : Blo 381763 1095221 := bbase (se 5 (by rfl) ⟨51338, by rfl⟩ : syracuseStep 1095221 = 102677) (by norm_num)
theorem B865853 : Blo 381763 865853 := bbase (se 3 (by rfl) ⟨162347, by rfl⟩ : syracuseStep 865853 = 324695) (by norm_num)
theorem B8336981 : Blo 381763 8336981 := bbase (se 8 (by rfl) ⟨48849, by rfl⟩ : syracuseStep 8336981 = 97699) (by norm_num)
theorem B865925 : Blo 381763 865925 := bbase (se 4 (by rfl) ⟨81180, by rfl⟩ : syracuseStep 865925 = 162361) (by norm_num)
theorem B865997 : Blo 381763 865997 := bbase (se 3 (by rfl) ⟨162374, by rfl⟩ : syracuseStep 865997 = 324749) (by norm_num)
theorem B866069 : Blo 381763 866069 := bbase (se 6 (by rfl) ⟨20298, by rfl⟩ : syracuseStep 866069 = 40597) (by norm_num)
theorem B1161029 : Blo 381763 1161029 := bbase (se 4 (by rfl) ⟨108846, by rfl⟩ : syracuseStep 1161029 = 217693) (by norm_num)
theorem B866141 : Blo 381763 866141 := bbase (se 3 (by rfl) ⟨162401, by rfl⟩ : syracuseStep 866141 = 324803) (by norm_num)
theorem B1292165 : Blo 381763 1292165 := bbase (se 4 (by rfl) ⟨121140, by rfl⟩ : syracuseStep 1292165 = 242281) (by norm_num)
theorem B866213 : Blo 381763 866213 := bbase (se 4 (by rfl) ⟨81207, by rfl⟩ : syracuseStep 866213 = 162415) (by norm_num)
theorem B866285 : Blo 381763 866285 := bbase (se 3 (by rfl) ⟨162428, by rfl⟩ : syracuseStep 866285 = 324857) (by norm_num)
theorem B866357 : Blo 381763 866357 := bbase (se 5 (by rfl) ⟨40610, by rfl⟩ : syracuseStep 866357 = 81221) (by norm_num)
theorem B866429 : Blo 381763 866429 := bbase (se 3 (by rfl) ⟨162455, by rfl⟩ : syracuseStep 866429 = 324911) (by norm_num)
theorem B407701 : Blo 381763 407701 := bbase (se 6 (by rfl) ⟨9555, by rfl⟩ : syracuseStep 407701 = 19111) (by norm_num)
theorem B866501 : Blo 381763 866501 := bbase (se 4 (by rfl) ⟨81234, by rfl⟩ : syracuseStep 866501 = 162469) (by norm_num)
theorem B1095893 : Blo 381763 1095893 := bbase (se 7 (by rfl) ⟨12842, by rfl⟩ : syracuseStep 1095893 = 25685) (by norm_num)
theorem B407773 : Blo 381763 407773 := bbase (se 3 (by rfl) ⟨76457, by rfl⟩ : syracuseStep 407773 = 152915) (by norm_num)
theorem B866573 : Blo 381763 866573 := bbase (se 3 (by rfl) ⟨162482, by rfl⟩ : syracuseStep 866573 = 324965) (by norm_num)
theorem B1292597 : Blo 381763 1292597 := bbase (se 5 (by rfl) ⟨60590, by rfl⟩ : syracuseStep 1292597 = 121181) (by norm_num)
theorem B3946805 : Blo 381763 3946805 := bbase (se 5 (by rfl) ⟨185006, by rfl⟩ : syracuseStep 3946805 = 370013) (by norm_num)
theorem B866645 : Blo 381763 866645 := bbase (se 10 (by rfl) ⟨1269, by rfl⟩ : syracuseStep 866645 = 2539) (by norm_num)
theorem B407953 : Blo 381763 407953 := bbase (se 2 (by rfl) ⟨152982, by rfl⟩ : syracuseStep 407953 = 305965) (by norm_num)
theorem B866717 : Blo 381763 866717 := bbase (se 3 (by rfl) ⟨162509, by rfl⟩ : syracuseStep 866717 = 325019) (by norm_num)
theorem B866789 : Blo 381763 866789 := bbase (se 4 (by rfl) ⟨81261, by rfl⟩ : syracuseStep 866789 = 162523) (by norm_num)
theorem B866861 : Blo 381763 866861 := bbase (se 3 (by rfl) ⟨162536, by rfl⟩ : syracuseStep 866861 = 325073) (by norm_num)
theorem B1227317 : Blo 381763 1227317 := bbase (se 5 (by rfl) ⟨57530, by rfl⟩ : syracuseStep 1227317 = 115061) (by norm_num)
theorem B866933 : Blo 381763 866933 := bbase (se 5 (by rfl) ⟨40637, by rfl⟩ : syracuseStep 866933 = 81275) (by norm_num)
theorem B1096325 : Blo 381763 1096325 := bbase (se 4 (by rfl) ⟨102780, by rfl⟩ : syracuseStep 1096325 = 205561) (by norm_num)
theorem B867005 : Blo 381763 867005 := bbase (se 3 (by rfl) ⟨162563, by rfl⟩ : syracuseStep 867005 = 325127) (by norm_num)
theorem B1948373 : Blo 381763 1948373 := bbase (se 7 (by rfl) ⟨22832, by rfl⟩ : syracuseStep 1948373 = 45665) (by norm_num)
theorem B1293029 : Blo 381763 1293029 := bbase (se 4 (by rfl) ⟨121221, by rfl⟩ : syracuseStep 1293029 = 242443) (by norm_num)
theorem B867077 : Blo 381763 867077 := bbase (se 4 (by rfl) ⟨81288, by rfl⟩ : syracuseStep 867077 = 162577) (by norm_num)
theorem B408397 : Blo 381763 408397 := bbase (se 3 (by rfl) ⟨76574, by rfl⟩ : syracuseStep 408397 = 153149) (by norm_num)
theorem B867149 : Blo 381763 867149 := bbase (se 3 (by rfl) ⟨162590, by rfl⟩ : syracuseStep 867149 = 325181) (by norm_num)
theorem B867221 : Blo 381763 867221 := bbase (se 6 (by rfl) ⟨20325, by rfl⟩ : syracuseStep 867221 = 40651) (by norm_num)
theorem B408521 : Blo 381763 408521 := bbase (se 2 (by rfl) ⟨153195, by rfl⟩ : syracuseStep 408521 = 306391) (by norm_num)
theorem B867293 : Blo 381763 867293 := bbase (se 3 (by rfl) ⟨162617, by rfl⟩ : syracuseStep 867293 = 325235) (by norm_num)
theorem B1850357 : Blo 381763 1850357 := bbase (se 5 (by rfl) ⟨86735, by rfl⟩ : syracuseStep 1850357 = 173471) (by norm_num)
theorem B867365 : Blo 381763 867365 := bbase (se 4 (by rfl) ⟨81315, by rfl⟩ : syracuseStep 867365 = 162631) (by norm_num)
theorem B867437 : Blo 381763 867437 := bbase (se 3 (by rfl) ⟨162644, by rfl⟩ : syracuseStep 867437 = 325289) (by norm_num)
theorem B1293461 : Blo 381763 1293461 := bbase (se 6 (by rfl) ⟨30315, by rfl⟩ : syracuseStep 1293461 = 60631) (by norm_num)
theorem B867509 : Blo 381763 867509 := bbase (se 5 (by rfl) ⟨40664, by rfl⟩ : syracuseStep 867509 = 81329) (by norm_num)
theorem B408773 : Blo 381763 408773 := bbase (se 4 (by rfl) ⟨38322, by rfl⟩ : syracuseStep 408773 = 76645) (by norm_num)
theorem B572645 : Blo 381763 572645 := bbase (se 4 (by rfl) ⟨53685, by rfl⟩ : syracuseStep 572645 = 107371) (by norm_num)
theorem B1752293 : Blo 381763 1752293 := bbase (se 4 (by rfl) ⟨164277, by rfl⟩ : syracuseStep 1752293 = 328555) (by norm_num)
theorem B572669 : Blo 381763 572669 := bbase (se 3 (by rfl) ⟨107375, by rfl⟩ : syracuseStep 572669 = 214751) (by norm_num)
theorem B867581 : Blo 381763 867581 := bbase (se 3 (by rfl) ⟨162671, by rfl⟩ : syracuseStep 867581 = 325343) (by norm_num)
theorem B933125 : Blo 381763 933125 := bbase (se 4 (by rfl) ⟨87480, by rfl⟩ : syracuseStep 933125 = 174961) (by norm_num)
theorem B572693 : Blo 381763 572693 := bbase (se 6 (by rfl) ⟨13422, by rfl⟩ : syracuseStep 572693 = 26845) (by norm_num)
theorem B572717 : Blo 381763 572717 := bbase (se 3 (by rfl) ⟨107384, by rfl⟩ : syracuseStep 572717 = 214769) (by norm_num)
theorem B572741 : Blo 381763 572741 := bbase (se 4 (by rfl) ⟨53694, by rfl⟩ : syracuseStep 572741 = 107389) (by norm_num)
theorem B867653 : Blo 381763 867653 := bbase (se 4 (by rfl) ⟨81342, by rfl⟩ : syracuseStep 867653 = 162685) (by norm_num)
theorem B507217 : Blo 381763 507217 := bbase (se 2 (by rfl) ⟨190206, by rfl⟩ : syracuseStep 507217 = 380413) (by norm_num)
theorem B572765 : Blo 381763 572765 := bbase (se 3 (by rfl) ⟨107393, by rfl⟩ : syracuseStep 572765 = 214787) (by norm_num)
theorem B572789 : Blo 381763 572789 := bbase (se 5 (by rfl) ⟨26849, by rfl⟩ : syracuseStep 572789 = 53699) (by norm_num)
theorem B1097077 : Blo 381763 1097077 := bbase (se 5 (by rfl) ⟨51425, by rfl⟩ : syracuseStep 1097077 = 102851) (by norm_num)
theorem B572813 : Blo 381763 572813 := bbase (se 3 (by rfl) ⟨107402, by rfl⟩ : syracuseStep 572813 = 214805) (by norm_num)
theorem B867725 : Blo 381763 867725 := bbase (se 3 (by rfl) ⟨162698, by rfl⟩ : syracuseStep 867725 = 325397) (by norm_num)
theorem B572837 : Blo 381763 572837 := bbase (se 4 (by rfl) ⟨53703, by rfl⟩ : syracuseStep 572837 = 107407) (by norm_num)
theorem B736685 : Blo 381763 736685 := bbase (se 3 (by rfl) ⟨138128, by rfl⟩ : syracuseStep 736685 = 276257) (by norm_num)
theorem B572861 : Blo 381763 572861 := bbase (se 3 (by rfl) ⟨107411, by rfl⟩ : syracuseStep 572861 = 214823) (by norm_num)
theorem B1228229 : Blo 381763 1228229 := bbase (se 4 (by rfl) ⟨115146, by rfl⟩ : syracuseStep 1228229 = 230293) (by norm_num)
theorem B572885 : Blo 381763 572885 := bbase (se 7 (by rfl) ⟨6713, by rfl⟩ : syracuseStep 572885 = 13427) (by norm_num)
theorem B1457621 : Blo 381763 1457621 := bbase (se 7 (by rfl) ⟨17081, by rfl⟩ : syracuseStep 1457621 = 34163) (by norm_num)
theorem B867797 : Blo 381763 867797 := bbase (se 7 (by rfl) ⟨10169, by rfl⟩ : syracuseStep 867797 = 20339) (by norm_num)
theorem B572909 : Blo 381763 572909 := bbase (se 3 (by rfl) ⟨107420, by rfl⟩ : syracuseStep 572909 = 214841) (by norm_num)
theorem B572933 : Blo 381763 572933 := bbase (se 4 (by rfl) ⟨53712, by rfl⟩ : syracuseStep 572933 = 107425) (by norm_num)
theorem B572957 : Blo 381763 572957 := bbase (se 3 (by rfl) ⟨107429, by rfl⟩ : syracuseStep 572957 = 214859) (by norm_num)
theorem B867869 : Blo 381763 867869 := bbase (se 3 (by rfl) ⟨162725, by rfl⟩ : syracuseStep 867869 = 325451) (by norm_num)
theorem B572981 : Blo 381763 572981 := bbase (se 5 (by rfl) ⟨26858, by rfl⟩ : syracuseStep 572981 = 53717) (by norm_num)
theorem B1293893 : Blo 381763 1293893 := bbase (se 4 (by rfl) ⟨121302, by rfl⟩ : syracuseStep 1293893 = 242605) (by norm_num)
theorem B573005 : Blo 381763 573005 := bbase (se 3 (by rfl) ⟨107438, by rfl⟩ : syracuseStep 573005 = 214877) (by norm_num)
theorem B573029 : Blo 381763 573029 := bbase (se 4 (by rfl) ⟨53721, by rfl⟩ : syracuseStep 573029 = 107443) (by norm_num)
theorem B1162853 : Blo 381763 1162853 := bbase (se 4 (by rfl) ⟨109017, by rfl⟩ : syracuseStep 1162853 = 218035) (by norm_num)
theorem B867941 : Blo 381763 867941 := bbase (se 4 (by rfl) ⟨81369, by rfl⟩ : syracuseStep 867941 = 162739) (by norm_num)
theorem B573053 : Blo 381763 573053 := bbase (se 3 (by rfl) ⟨107447, by rfl⟩ : syracuseStep 573053 = 214895) (by norm_num)
theorem B409217 : Blo 381763 409217 := bbase (se 2 (by rfl) ⟨153456, by rfl⟩ : syracuseStep 409217 = 306913) (by norm_num)
theorem B573077 : Blo 381763 573077 := bbase (se 6 (by rfl) ⟨13431, by rfl⟩ : syracuseStep 573077 = 26863) (by norm_num)
theorem B573101 : Blo 381763 573101 := bbase (se 3 (by rfl) ⟨107456, by rfl⟩ : syracuseStep 573101 = 214913) (by norm_num)
theorem B573125 : Blo 381763 573125 := bbase (se 4 (by rfl) ⟨53730, by rfl⟩ : syracuseStep 573125 = 107461) (by norm_num)
theorem B573149 : Blo 381763 573149 := bbase (se 3 (by rfl) ⟨107465, by rfl⟩ : syracuseStep 573149 = 214931) (by norm_num)
theorem B573173 : Blo 381763 573173 := bbase (se 5 (by rfl) ⟨26867, by rfl⟩ : syracuseStep 573173 = 53735) (by norm_num)
theorem B1457909 : Blo 381763 1457909 := bbase (se 5 (by rfl) ⟨68339, by rfl⟩ : syracuseStep 1457909 = 136679) (by norm_num)
theorem B573197 : Blo 381763 573197 := bbase (se 3 (by rfl) ⟨107474, by rfl⟩ : syracuseStep 573197 = 214949) (by norm_num)
theorem B573221 : Blo 381763 573221 := bbase (se 4 (by rfl) ⟨53739, by rfl⟩ : syracuseStep 573221 = 107479) (by norm_num)
theorem B573245 : Blo 381763 573245 := bbase (se 3 (by rfl) ⟨107483, by rfl⟩ : syracuseStep 573245 = 214967) (by norm_num)
theorem B573269 : Blo 381763 573269 := bbase (se 9 (by rfl) ⟨1679, by rfl⟩ : syracuseStep 573269 = 3359) (by norm_num)
theorem B3358549 : Blo 381763 3358549 := bbase (se 9 (by rfl) ⟨9839, by rfl⟩ : syracuseStep 3358549 = 19679) (by norm_num)
theorem B573293 : Blo 381763 573293 := bbase (se 3 (by rfl) ⟨107492, by rfl⟩ : syracuseStep 573293 = 214985) (by norm_num)
theorem B409465 : Blo 381763 409465 := bbase (se 2 (by rfl) ⟨153549, by rfl⟩ : syracuseStep 409465 = 307099) (by norm_num)
theorem B573317 : Blo 381763 573317 := bbase (se 4 (by rfl) ⟨53748, by rfl⟩ : syracuseStep 573317 = 107497) (by norm_num)
theorem B573341 : Blo 381763 573341 := bbase (se 3 (by rfl) ⟨107501, by rfl⟩ : syracuseStep 573341 = 215003) (by norm_num)
theorem B573365 : Blo 381763 573365 := bbase (se 5 (by rfl) ⟨26876, by rfl⟩ : syracuseStep 573365 = 53753) (by norm_num)
theorem B573389 : Blo 381763 573389 := bbase (se 3 (by rfl) ⟨107510, by rfl⟩ : syracuseStep 573389 = 215021) (by norm_num)
theorem B966613 : Blo 381763 966613 := bbase (se 7 (by rfl) ⟨11327, by rfl⟩ : syracuseStep 966613 = 22655) (by norm_num)
theorem B573413 : Blo 381763 573413 := bbase (se 4 (by rfl) ⟨53757, by rfl⟩ : syracuseStep 573413 = 107515) (by norm_num)
theorem B1949669 : Blo 381763 1949669 := bbase (se 4 (by rfl) ⟨182781, by rfl⟩ : syracuseStep 1949669 = 365563) (by norm_num)
theorem B1294325 : Blo 381763 1294325 := bbase (se 5 (by rfl) ⟨60671, by rfl⟩ : syracuseStep 1294325 = 121343) (by norm_num)
theorem B573437 : Blo 381763 573437 := bbase (se 3 (by rfl) ⟨107519, by rfl⟩ : syracuseStep 573437 = 215039) (by norm_num)
theorem B573461 : Blo 381763 573461 := bbase (se 6 (by rfl) ⟨13440, by rfl⟩ : syracuseStep 573461 = 26881) (by norm_num)
theorem B573485 : Blo 381763 573485 := bbase (se 3 (by rfl) ⟨107528, by rfl⟩ : syracuseStep 573485 = 215057) (by norm_num)
theorem B966725 : Blo 381763 966725 := bbase (se 4 (by rfl) ⟨90630, by rfl⟩ : syracuseStep 966725 = 181261) (by norm_num)
theorem B573509 : Blo 381763 573509 := bbase (se 4 (by rfl) ⟨53766, by rfl⟩ : syracuseStep 573509 = 107533) (by norm_num)
theorem B573533 : Blo 381763 573533 := bbase (se 3 (by rfl) ⟨107537, by rfl⟩ : syracuseStep 573533 = 215075) (by norm_num)
theorem B573557 : Blo 381763 573557 := bbase (se 5 (by rfl) ⟨26885, by rfl⟩ : syracuseStep 573557 = 53771) (by norm_num)
theorem B573581 : Blo 381763 573581 := bbase (se 3 (by rfl) ⟨107546, by rfl⟩ : syracuseStep 573581 = 215093) (by norm_num)
theorem B573605 : Blo 381763 573605 := bbase (se 4 (by rfl) ⟨53775, by rfl⟩ : syracuseStep 573605 = 107551) (by norm_num)
theorem B573629 : Blo 381763 573629 := bbase (se 3 (by rfl) ⟨107555, by rfl⟩ : syracuseStep 573629 = 215111) (by norm_num)
theorem B573653 : Blo 381763 573653 := bbase (se 7 (by rfl) ⟨6722, by rfl⟩ : syracuseStep 573653 = 13445) (by norm_num)
theorem B573677 : Blo 381763 573677 := bbase (se 3 (by rfl) ⟨107564, by rfl⟩ : syracuseStep 573677 = 215129) (by norm_num)
theorem B966917 : Blo 381763 966917 := bbase (se 4 (by rfl) ⟨90648, by rfl⟩ : syracuseStep 966917 = 181297) (by norm_num)
theorem B573701 : Blo 381763 573701 := bbase (se 4 (by rfl) ⟨53784, by rfl⟩ : syracuseStep 573701 = 107569) (by norm_num)
theorem B573725 : Blo 381763 573725 := bbase (se 3 (by rfl) ⟨107573, by rfl⟩ : syracuseStep 573725 = 215147) (by norm_num)
theorem B573749 : Blo 381763 573749 := bbase (se 5 (by rfl) ⟨26894, by rfl⟩ : syracuseStep 573749 = 53789) (by norm_num)
theorem B409909 : Blo 381763 409909 := bbase (se 5 (by rfl) ⟨19214, by rfl⟩ : syracuseStep 409909 = 38429) (by norm_num)
theorem B573773 : Blo 381763 573773 := bbase (se 3 (by rfl) ⟨107582, by rfl⟩ : syracuseStep 573773 = 215165) (by norm_num)
theorem B573797 : Blo 381763 573797 := bbase (se 4 (by rfl) ⟨53793, by rfl⟩ : syracuseStep 573797 = 107587) (by norm_num)
theorem B409969 : Blo 381763 409969 := bbase (se 2 (by rfl) ⟨153738, by rfl⟩ : syracuseStep 409969 = 307477) (by norm_num)
theorem B573821 : Blo 381763 573821 := bbase (se 3 (by rfl) ⟨107591, by rfl⟩ : syracuseStep 573821 = 215183) (by norm_num)
theorem B1851781 : Blo 381763 1851781 := bbase (se 4 (by rfl) ⟨173604, by rfl⟩ : syracuseStep 1851781 = 347209) (by norm_num)
theorem B573845 : Blo 381763 573845 := bbase (se 6 (by rfl) ⟨13449, by rfl⟩ : syracuseStep 573845 = 26899) (by norm_num)
theorem B1294757 : Blo 381763 1294757 := bbase (se 4 (by rfl) ⟨121383, by rfl⟩ : syracuseStep 1294757 = 242767) (by norm_num)
theorem B573869 : Blo 381763 573869 := bbase (se 3 (by rfl) ⟨107600, by rfl⟩ : syracuseStep 573869 = 215201) (by norm_num)
theorem B573893 : Blo 381763 573893 := bbase (se 4 (by rfl) ⟨53802, by rfl⟩ : syracuseStep 573893 = 107605) (by norm_num)
theorem B573917 : Blo 381763 573917 := bbase (se 3 (by rfl) ⟨107609, by rfl⟩ : syracuseStep 573917 = 215219) (by norm_num)
theorem B573941 : Blo 381763 573941 := bbase (se 5 (by rfl) ⟨26903, by rfl⟩ : syracuseStep 573941 = 53807) (by norm_num)
theorem B573965 : Blo 381763 573965 := bbase (se 3 (by rfl) ⟨107618, by rfl⟩ : syracuseStep 573965 = 215237) (by norm_num)
theorem B573989 : Blo 381763 573989 := bbase (se 4 (by rfl) ⟨53811, by rfl⟩ : syracuseStep 573989 = 107623) (by norm_num)
theorem B574013 : Blo 381763 574013 := bbase (se 3 (by rfl) ⟨107627, by rfl⟩ : syracuseStep 574013 = 215255) (by norm_num)
theorem B574037 : Blo 381763 574037 := bbase (se 8 (by rfl) ⟨3363, by rfl⟩ : syracuseStep 574037 = 6727) (by norm_num)
theorem B967261 : Blo 381763 967261 := bbase (se 3 (by rfl) ⟨181361, by rfl⟩ : syracuseStep 967261 = 362723) (by norm_num)
theorem B574061 : Blo 381763 574061 := bbase (se 3 (by rfl) ⟨107636, by rfl⟩ : syracuseStep 574061 = 215273) (by norm_num)
theorem B574085 : Blo 381763 574085 := bbase (se 4 (by rfl) ⟨53820, by rfl⟩ : syracuseStep 574085 = 107641) (by norm_num)
theorem B574109 : Blo 381763 574109 := bbase (se 3 (by rfl) ⟨107645, by rfl⟩ : syracuseStep 574109 = 215291) (by norm_num)
theorem B410285 : Blo 381763 410285 := bbase (se 3 (by rfl) ⟨76928, by rfl⟩ : syracuseStep 410285 = 153857) (by norm_num)
theorem B574133 : Blo 381763 574133 := bbase (se 5 (by rfl) ⟨26912, by rfl⟩ : syracuseStep 574133 = 53825) (by norm_num)
theorem B967373 : Blo 381763 967373 := bbase (se 3 (by rfl) ⟨181382, by rfl⟩ : syracuseStep 967373 = 362765) (by norm_num)
theorem B574157 : Blo 381763 574157 := bbase (se 3 (by rfl) ⟨107654, by rfl⟩ : syracuseStep 574157 = 215309) (by norm_num)
theorem B574181 : Blo 381763 574181 := bbase (se 4 (by rfl) ⟨53829, by rfl⟩ : syracuseStep 574181 = 107659) (by norm_num)
theorem B2769653 : Blo 381763 2769653 := bbase (se 5 (by rfl) ⟨129827, by rfl⟩ : syracuseStep 2769653 = 259655) (by norm_num)
theorem B574205 : Blo 381763 574205 := bbase (se 3 (by rfl) ⟨107663, by rfl⟩ : syracuseStep 574205 = 215327) (by norm_num)
theorem B1229573 : Blo 381763 1229573 := bbase (se 4 (by rfl) ⟨115272, by rfl⟩ : syracuseStep 1229573 = 230545) (by norm_num)
theorem B574229 : Blo 381763 574229 := bbase (se 6 (by rfl) ⟨13458, by rfl⟩ : syracuseStep 574229 = 26917) (by norm_num)
theorem B574253 : Blo 381763 574253 := bbase (se 3 (by rfl) ⟨107672, by rfl⟩ : syracuseStep 574253 = 215345) (by norm_num)
theorem B574277 : Blo 381763 574277 := bbase (se 4 (by rfl) ⟨53838, by rfl⟩ : syracuseStep 574277 = 107677) (by norm_num)
theorem B4146005 : Blo 381763 4146005 := bbase (se 9 (by rfl) ⟨12146, by rfl⟩ : syracuseStep 4146005 = 24293) (by norm_num)
theorem B1295189 : Blo 381763 1295189 := bbase (se 9 (by rfl) ⟨3794, by rfl⟩ : syracuseStep 1295189 = 7589) (by norm_num)
theorem B574301 : Blo 381763 574301 := bbase (se 3 (by rfl) ⟨107681, by rfl⟩ : syracuseStep 574301 = 215363) (by norm_num)
theorem B574325 : Blo 381763 574325 := bbase (se 5 (by rfl) ⟨26921, by rfl⟩ : syracuseStep 574325 = 53843) (by norm_num)
theorem B967565 : Blo 381763 967565 := bbase (se 3 (by rfl) ⟨181418, by rfl⟩ : syracuseStep 967565 = 362837) (by norm_num)
theorem B574349 : Blo 381763 574349 := bbase (se 3 (by rfl) ⟨107690, by rfl⟩ : syracuseStep 574349 = 215381) (by norm_num)
theorem B1459093 : Blo 381763 1459093 := bbase (se 6 (by rfl) ⟨34197, by rfl⟩ : syracuseStep 1459093 = 68395) (by norm_num)
theorem B574373 : Blo 381763 574373 := bbase (se 4 (by rfl) ⟨53847, by rfl⟩ : syracuseStep 574373 = 107695) (by norm_num)
theorem B1557413 : Blo 381763 1557413 := bbase (se 4 (by rfl) ⟨146007, by rfl⟩ : syracuseStep 1557413 = 292015) (by norm_num)
theorem B574397 : Blo 381763 574397 := bbase (se 3 (by rfl) ⟨107699, by rfl⟩ : syracuseStep 574397 = 215399) (by norm_num)
theorem B574421 : Blo 381763 574421 := bbase (se 7 (by rfl) ⟨6731, by rfl⟩ : syracuseStep 574421 = 13463) (by norm_num)
theorem B574445 : Blo 381763 574445 := bbase (se 3 (by rfl) ⟨107708, by rfl⟩ : syracuseStep 574445 = 215417) (by norm_num)
theorem B574469 : Blo 381763 574469 := bbase (se 4 (by rfl) ⟨53856, by rfl⟩ : syracuseStep 574469 = 107713) (by norm_num)
theorem B574493 : Blo 381763 574493 := bbase (se 3 (by rfl) ⟨107717, by rfl⟩ : syracuseStep 574493 = 215435) (by norm_num)
theorem B574517 : Blo 381763 574517 := bbase (se 5 (by rfl) ⟨26930, by rfl⟩ : syracuseStep 574517 = 53861) (by norm_num)
theorem B574541 : Blo 381763 574541 := bbase (se 3 (by rfl) ⟨107726, by rfl⟩ : syracuseStep 574541 = 215453) (by norm_num)
theorem B574565 : Blo 381763 574565 := bbase (se 4 (by rfl) ⟨53865, by rfl⟩ : syracuseStep 574565 = 107731) (by norm_num)
theorem B410729 : Blo 381763 410729 := bbase (se 2 (by rfl) ⟨154023, by rfl⟩ : syracuseStep 410729 = 308047) (by norm_num)
theorem B574589 : Blo 381763 574589 := bbase (se 3 (by rfl) ⟨107735, by rfl⟩ : syracuseStep 574589 = 215471) (by norm_num)
theorem B574613 : Blo 381763 574613 := bbase (se 6 (by rfl) ⟨13467, by rfl⟩ : syracuseStep 574613 = 26935) (by norm_num)
theorem B410789 : Blo 381763 410789 := bbase (se 4 (by rfl) ⟨38511, by rfl⟩ : syracuseStep 410789 = 77023) (by norm_num)
theorem B574637 : Blo 381763 574637 := bbase (se 3 (by rfl) ⟨107744, by rfl⟩ : syracuseStep 574637 = 215489) (by norm_num)
theorem B574661 : Blo 381763 574661 := bbase (se 4 (by rfl) ⟨53874, by rfl⟩ : syracuseStep 574661 = 107749) (by norm_num)
theorem B1459397 : Blo 381763 1459397 := bbase (se 4 (by rfl) ⟨136818, by rfl⟩ : syracuseStep 1459397 = 273637) (by norm_num)
theorem B574685 : Blo 381763 574685 := bbase (se 3 (by rfl) ⟨107753, by rfl⟩ : syracuseStep 574685 = 215507) (by norm_num)
theorem B967909 : Blo 381763 967909 := bbase (se 4 (by rfl) ⟨90741, by rfl⟩ : syracuseStep 967909 = 181483) (by norm_num)
theorem B574709 : Blo 381763 574709 := bbase (se 5 (by rfl) ⟨26939, by rfl⟩ : syracuseStep 574709 = 53879) (by norm_num)
theorem B1950965 : Blo 381763 1950965 := bbase (se 5 (by rfl) ⟨91451, by rfl⟩ : syracuseStep 1950965 = 182903) (by norm_num)
theorem B1295621 : Blo 381763 1295621 := bbase (se 4 (by rfl) ⟨121464, by rfl⟩ : syracuseStep 1295621 = 242929) (by norm_num)
theorem B574733 : Blo 381763 574733 := bbase (se 3 (by rfl) ⟨107762, by rfl⟩ : syracuseStep 574733 = 215525) (by norm_num)
theorem B574757 : Blo 381763 574757 := bbase (se 4 (by rfl) ⟨53883, by rfl⟩ : syracuseStep 574757 = 107767) (by norm_num)
theorem B410917 : Blo 381763 410917 := bbase (se 4 (by rfl) ⟨38523, by rfl⟩ : syracuseStep 410917 = 77047) (by norm_num)
theorem B574781 : Blo 381763 574781 := bbase (se 3 (by rfl) ⟨107771, by rfl⟩ : syracuseStep 574781 = 215543) (by norm_num)
theorem B968021 : Blo 381763 968021 := bbase (se 12 (by rfl) ⟨354, by rfl⟩ : syracuseStep 968021 = 709) (by norm_num)
theorem B574805 : Blo 381763 574805 := bbase (se 12 (by rfl) ⟨210, by rfl⟩ : syracuseStep 574805 = 421) (by norm_num)
theorem B574829 : Blo 381763 574829 := bbase (se 3 (by rfl) ⟨107780, by rfl⟩ : syracuseStep 574829 = 215561) (by norm_num)
theorem B574853 : Blo 381763 574853 := bbase (se 4 (by rfl) ⟨53892, by rfl⟩ : syracuseStep 574853 = 107785) (by norm_num)
theorem B574877 : Blo 381763 574877 := bbase (se 3 (by rfl) ⟨107789, by rfl⟩ : syracuseStep 574877 = 215579) (by norm_num)
theorem B574901 : Blo 381763 574901 := bbase (se 5 (by rfl) ⟨26948, by rfl⟩ : syracuseStep 574901 = 53897) (by norm_num)
theorem B574925 : Blo 381763 574925 := bbase (se 3 (by rfl) ⟨107798, by rfl⟩ : syracuseStep 574925 = 215597) (by norm_num)
theorem B574949 : Blo 381763 574949 := bbase (se 4 (by rfl) ⟨53901, by rfl⟩ : syracuseStep 574949 = 107803) (by norm_num)
theorem B574973 : Blo 381763 574973 := bbase (se 3 (by rfl) ⟨107807, by rfl⟩ : syracuseStep 574973 = 215615) (by norm_num)
theorem B968213 : Blo 381763 968213 := bbase (se 6 (by rfl) ⟨22692, by rfl⟩ : syracuseStep 968213 = 45385) (by norm_num)
theorem B574997 : Blo 381763 574997 := bbase (se 6 (by rfl) ⟨13476, by rfl⟩ : syracuseStep 574997 = 26953) (by norm_num)
theorem B575021 : Blo 381763 575021 := bbase (se 3 (by rfl) ⟨107816, by rfl⟩ : syracuseStep 575021 = 215633) (by norm_num)
theorem B575045 : Blo 381763 575045 := bbase (se 4 (by rfl) ⟨53910, by rfl⟩ : syracuseStep 575045 = 107821) (by norm_num)
theorem B575069 : Blo 381763 575069 := bbase (se 3 (by rfl) ⟨107825, by rfl⟩ : syracuseStep 575069 = 215651) (by norm_num)
theorem B575093 : Blo 381763 575093 := bbase (se 5 (by rfl) ⟨26957, by rfl⟩ : syracuseStep 575093 = 53915) (by norm_num)
theorem B575117 : Blo 381763 575117 := bbase (se 3 (by rfl) ⟨107834, by rfl⟩ : syracuseStep 575117 = 215669) (by norm_num)
theorem B575141 : Blo 381763 575141 := bbase (se 4 (by rfl) ⟨53919, by rfl⟩ : syracuseStep 575141 = 107839) (by norm_num)
theorem B1296053 : Blo 381763 1296053 := bbase (se 5 (by rfl) ⟨60752, by rfl⟩ : syracuseStep 1296053 = 121505) (by norm_num)
theorem B575165 : Blo 381763 575165 := bbase (se 3 (by rfl) ⟨107843, by rfl⟩ : syracuseStep 575165 = 215687) (by norm_num)
theorem B575189 : Blo 381763 575189 := bbase (se 7 (by rfl) ⟨6740, by rfl⟩ : syracuseStep 575189 = 13481) (by norm_num)
theorem B411361 : Blo 381763 411361 := bbase (se 2 (by rfl) ⟨154260, by rfl⟩ : syracuseStep 411361 = 308521) (by norm_num)
theorem B575213 : Blo 381763 575213 := bbase (se 3 (by rfl) ⟨107852, by rfl⟩ : syracuseStep 575213 = 215705) (by norm_num)
theorem B575237 : Blo 381763 575237 := bbase (se 4 (by rfl) ⟨53928, by rfl⟩ : syracuseStep 575237 = 107857) (by norm_num)
theorem B575261 : Blo 381763 575261 := bbase (se 3 (by rfl) ⟨107861, by rfl⟩ : syracuseStep 575261 = 215723) (by norm_num)
theorem B575285 : Blo 381763 575285 := bbase (se 5 (by rfl) ⟨26966, by rfl⟩ : syracuseStep 575285 = 53933) (by norm_num)
theorem B575309 : Blo 381763 575309 := bbase (se 3 (by rfl) ⟨107870, by rfl⟩ : syracuseStep 575309 = 215741) (by norm_num)
theorem B411481 : Blo 381763 411481 := bbase (se 2 (by rfl) ⟨154305, by rfl⟩ : syracuseStep 411481 = 308611) (by norm_num)
theorem B575333 : Blo 381763 575333 := bbase (se 4 (by rfl) ⟨53937, by rfl⟩ : syracuseStep 575333 = 107875) (by norm_num)
theorem B968557 : Blo 381763 968557 := bbase (se 3 (by rfl) ⟨181604, by rfl⟩ : syracuseStep 968557 = 363209) (by norm_num)
theorem B575357 : Blo 381763 575357 := bbase (se 3 (by rfl) ⟨107879, by rfl⟩ : syracuseStep 575357 = 215759) (by norm_num)
theorem B575381 : Blo 381763 575381 := bbase (se 6 (by rfl) ⟨13485, by rfl⟩ : syracuseStep 575381 = 26971) (by norm_num)
theorem B575405 : Blo 381763 575405 := bbase (se 3 (by rfl) ⟨107888, by rfl⟩ : syracuseStep 575405 = 215777) (by norm_num)
theorem B1034165 : Blo 381763 1034165 := bbase (se 5 (by rfl) ⟨48476, by rfl⟩ : syracuseStep 1034165 = 96953) (by norm_num)
theorem B575429 : Blo 381763 575429 := bbase (se 4 (by rfl) ⟨53946, by rfl⟩ : syracuseStep 575429 = 107893) (by norm_num)
theorem B2181077 : Blo 381763 2181077 := bbase (se 7 (by rfl) ⟨25559, by rfl⟩ : syracuseStep 2181077 = 51119) (by norm_num)
theorem B968669 : Blo 381763 968669 := bbase (se 3 (by rfl) ⟨181625, by rfl⟩ : syracuseStep 968669 = 363251) (by norm_num)
theorem B575453 : Blo 381763 575453 := bbase (se 3 (by rfl) ⟨107897, by rfl⟩ : syracuseStep 575453 = 215795) (by norm_num)
theorem B575477 : Blo 381763 575477 := bbase (se 5 (by rfl) ⟨26975, by rfl⟩ : syracuseStep 575477 = 53951) (by norm_num)
theorem B575501 : Blo 381763 575501 := bbase (se 3 (by rfl) ⟨107906, by rfl⟩ : syracuseStep 575501 = 215813) (by norm_num)
theorem B575525 : Blo 381763 575525 := bbase (se 4 (by rfl) ⟨53955, by rfl⟩ : syracuseStep 575525 = 107911) (by norm_num)
theorem B575549 : Blo 381763 575549 := bbase (se 3 (by rfl) ⟨107915, by rfl⟩ : syracuseStep 575549 = 215831) (by norm_num)
theorem B575573 : Blo 381763 575573 := bbase (se 8 (by rfl) ⟨3372, by rfl⟩ : syracuseStep 575573 = 6745) (by norm_num)
theorem B411733 : Blo 381763 411733 := bbase (se 8 (by rfl) ⟨2412, by rfl⟩ : syracuseStep 411733 = 4825) (by norm_num)
theorem B411737 : Blo 381763 411737 := bbase (se 2 (by rfl) ⟨154401, by rfl⟩ : syracuseStep 411737 = 308803) (by norm_num)
theorem B1296485 : Blo 381763 1296485 := bbase (se 4 (by rfl) ⟨121545, by rfl⟩ : syracuseStep 1296485 = 243091) (by norm_num)
theorem B575597 : Blo 381763 575597 := bbase (se 3 (by rfl) ⟨107924, by rfl⟩ : syracuseStep 575597 = 215849) (by norm_num)
theorem B575621 : Blo 381763 575621 := bbase (se 4 (by rfl) ⟨53964, by rfl⟩ : syracuseStep 575621 = 107929) (by norm_num)
theorem B1230997 : Blo 381763 1230997 := bbase (se 6 (by rfl) ⟨28851, by rfl⟩ : syracuseStep 1230997 = 57703) (by norm_num)
theorem B968861 : Blo 381763 968861 := bbase (se 3 (by rfl) ⟨181661, by rfl⟩ : syracuseStep 968861 = 363323) (by norm_num)
theorem B575645 : Blo 381763 575645 := bbase (se 3 (by rfl) ⟨107933, by rfl⟩ : syracuseStep 575645 = 215867) (by norm_num)
theorem B575669 : Blo 381763 575669 := bbase (se 5 (by rfl) ⟨26984, by rfl⟩ : syracuseStep 575669 = 53969) (by norm_num)
theorem B575693 : Blo 381763 575693 := bbase (se 3 (by rfl) ⟨107942, by rfl⟩ : syracuseStep 575693 = 215885) (by norm_num)
theorem B575717 : Blo 381763 575717 := bbase (se 4 (by rfl) ⟨53973, by rfl⟩ : syracuseStep 575717 = 107947) (by norm_num)
theorem B575741 : Blo 381763 575741 := bbase (se 3 (by rfl) ⟨107951, by rfl⟩ : syracuseStep 575741 = 215903) (by norm_num)
theorem B575765 : Blo 381763 575765 := bbase (se 6 (by rfl) ⟨13494, by rfl⟩ : syracuseStep 575765 = 26989) (by norm_num)
theorem B575789 : Blo 381763 575789 := bbase (se 3 (by rfl) ⟨107960, by rfl⟩ : syracuseStep 575789 = 215921) (by norm_num)
theorem B575813 : Blo 381763 575813 := bbase (se 4 (by rfl) ⟨53982, by rfl⟩ : syracuseStep 575813 = 107965) (by norm_num)
theorem B575837 : Blo 381763 575837 := bbase (se 3 (by rfl) ⟨107969, by rfl⟩ : syracuseStep 575837 = 215939) (by norm_num)
theorem B575861 : Blo 381763 575861 := bbase (se 5 (by rfl) ⟨26993, by rfl⟩ : syracuseStep 575861 = 53987) (by norm_num)
theorem B575885 : Blo 381763 575885 := bbase (se 3 (by rfl) ⟨107978, by rfl⟩ : syracuseStep 575885 = 215957) (by norm_num)
theorem B903565 : Blo 381763 903565 := bbase (se 3 (by rfl) ⟨169418, by rfl⟩ : syracuseStep 903565 = 338837) (by norm_num)
theorem B575909 : Blo 381763 575909 := bbase (se 4 (by rfl) ⟨53991, by rfl⟩ : syracuseStep 575909 = 107983) (by norm_num)
theorem B575933 : Blo 381763 575933 := bbase (se 3 (by rfl) ⟨107987, by rfl⟩ : syracuseStep 575933 = 215975) (by norm_num)
theorem B575957 : Blo 381763 575957 := bbase (se 7 (by rfl) ⟨6749, by rfl⟩ : syracuseStep 575957 = 13499) (by norm_num)
theorem B575981 : Blo 381763 575981 := bbase (se 3 (by rfl) ⟨107996, by rfl⟩ : syracuseStep 575981 = 215993) (by norm_num)
theorem B969205 : Blo 381763 969205 := bbase (se 5 (by rfl) ⟨45431, by rfl⟩ : syracuseStep 969205 = 90863) (by norm_num)
theorem B576005 : Blo 381763 576005 := bbase (se 4 (by rfl) ⟨54000, by rfl⟩ : syracuseStep 576005 = 108001) (by norm_num)
theorem B1952261 : Blo 381763 1952261 := bbase (se 4 (by rfl) ⟨183024, by rfl⟩ : syracuseStep 1952261 = 366049) (by norm_num)
theorem B1296917 : Blo 381763 1296917 := bbase (se 6 (by rfl) ⟨30396, by rfl⟩ : syracuseStep 1296917 = 60793) (by norm_num)
theorem B576029 : Blo 381763 576029 := bbase (se 3 (by rfl) ⟨108005, by rfl⟩ : syracuseStep 576029 = 216011) (by norm_num)
theorem B576053 : Blo 381763 576053 := bbase (se 5 (by rfl) ⟨27002, by rfl⟩ : syracuseStep 576053 = 54005) (by norm_num)
theorem B576077 : Blo 381763 576077 := bbase (se 3 (by rfl) ⟨108014, by rfl⟩ : syracuseStep 576077 = 216029) (by norm_num)
theorem B969317 : Blo 381763 969317 := bbase (se 4 (by rfl) ⟨90873, by rfl⟩ : syracuseStep 969317 = 181747) (by norm_num)
theorem B576101 : Blo 381763 576101 := bbase (se 4 (by rfl) ⟨54009, by rfl⟩ : syracuseStep 576101 = 108019) (by norm_num)
theorem B576125 : Blo 381763 576125 := bbase (se 3 (by rfl) ⟨108023, by rfl⟩ : syracuseStep 576125 = 216047) (by norm_num)
theorem B576149 : Blo 381763 576149 := bbase (se 6 (by rfl) ⟨13503, by rfl⟩ : syracuseStep 576149 = 27007) (by norm_num)
theorem B576173 : Blo 381763 576173 := bbase (se 3 (by rfl) ⟨108032, by rfl⟩ : syracuseStep 576173 = 216065) (by norm_num)
theorem B576197 : Blo 381763 576197 := bbase (se 4 (by rfl) ⟨54018, by rfl⟩ : syracuseStep 576197 = 108037) (by norm_num)
theorem B871117 : Blo 381763 871117 := bbase (se 3 (by rfl) ⟨163334, by rfl⟩ : syracuseStep 871117 = 326669) (by norm_num)
theorem B576221 : Blo 381763 576221 := bbase (se 3 (by rfl) ⟨108041, by rfl⟩ : syracuseStep 576221 = 216083) (by norm_num)
theorem B576245 : Blo 381763 576245 := bbase (se 5 (by rfl) ⟨27011, by rfl⟩ : syracuseStep 576245 = 54023) (by norm_num)
theorem B576269 : Blo 381763 576269 := bbase (se 3 (by rfl) ⟨108050, by rfl⟩ : syracuseStep 576269 = 216101) (by norm_num)
theorem B969509 : Blo 381763 969509 := bbase (se 4 (by rfl) ⟨90891, by rfl⟩ : syracuseStep 969509 = 181783) (by norm_num)
theorem B576293 : Blo 381763 576293 := bbase (se 4 (by rfl) ⟨54027, by rfl⟩ : syracuseStep 576293 = 108055) (by norm_num)
theorem B576317 : Blo 381763 576317 := bbase (se 3 (by rfl) ⟨108059, by rfl⟩ : syracuseStep 576317 = 216119) (by norm_num)
theorem B576341 : Blo 381763 576341 := bbase (se 9 (by rfl) ⟨1688, by rfl⟩ : syracuseStep 576341 = 3377) (by norm_num)
theorem B576365 : Blo 381763 576365 := bbase (se 3 (by rfl) ⟨108068, by rfl⟩ : syracuseStep 576365 = 216137) (by norm_num)
theorem B3689333 : Blo 381763 3689333 := bbase (se 5 (by rfl) ⟨172937, by rfl⟩ : syracuseStep 3689333 = 345875) (by norm_num)
theorem B576389 : Blo 381763 576389 := bbase (se 4 (by rfl) ⟨54036, by rfl⟩ : syracuseStep 576389 = 108073) (by norm_num)
theorem B543629 : Blo 381763 543629 := bbase (se 3 (by rfl) ⟨101930, by rfl⟩ : syracuseStep 543629 = 203861) (by norm_num)
theorem B576413 : Blo 381763 576413 := bbase (se 3 (by rfl) ⟨108077, by rfl⟩ : syracuseStep 576413 = 216155) (by norm_num)
theorem B576437 : Blo 381763 576437 := bbase (se 5 (by rfl) ⟨27020, by rfl⟩ : syracuseStep 576437 = 54041) (by norm_num)
theorem B1297349 : Blo 381763 1297349 := bbase (se 4 (by rfl) ⟨121626, by rfl⟩ : syracuseStep 1297349 = 243253) (by norm_num)
theorem B576461 : Blo 381763 576461 := bbase (se 3 (by rfl) ⟨108086, by rfl⟩ : syracuseStep 576461 = 216173) (by norm_num)
theorem B543709 : Blo 381763 543709 := bbase (se 3 (by rfl) ⟨101945, by rfl⟩ : syracuseStep 543709 = 203891) (by norm_num)
theorem B1166309 : Blo 381763 1166309 := bbase (se 4 (by rfl) ⟨109341, by rfl⟩ : syracuseStep 1166309 = 218683) (by norm_num)
theorem B576485 : Blo 381763 576485 := bbase (se 4 (by rfl) ⟨54045, by rfl⟩ : syracuseStep 576485 = 108091) (by norm_num)
theorem B740333 : Blo 381763 740333 := bbase (se 3 (by rfl) ⟨138812, by rfl⟩ : syracuseStep 740333 = 277625) (by norm_num)
theorem B576509 : Blo 381763 576509 := bbase (se 3 (by rfl) ⟨108095, by rfl⟩ : syracuseStep 576509 = 216191) (by norm_num)
theorem B576533 : Blo 381763 576533 := bbase (se 6 (by rfl) ⟨13512, by rfl⟩ : syracuseStep 576533 = 27025) (by norm_num)
theorem B576557 : Blo 381763 576557 := bbase (se 3 (by rfl) ⟨108104, by rfl⟩ : syracuseStep 576557 = 216209) (by norm_num)
theorem B576581 : Blo 381763 576581 := bbase (se 4 (by rfl) ⟨54054, by rfl⟩ : syracuseStep 576581 = 108109) (by norm_num)
theorem B543829 : Blo 381763 543829 := bbase (se 8 (by rfl) ⟨3186, by rfl⟩ : syracuseStep 543829 = 6373) (by norm_num)
theorem B576605 : Blo 381763 576605 := bbase (se 3 (by rfl) ⟨108113, by rfl⟩ : syracuseStep 576605 = 216227) (by norm_num)
theorem B2182261 : Blo 381763 2182261 := bbase (se 5 (by rfl) ⟨102293, by rfl⟩ : syracuseStep 2182261 = 204587) (by norm_num)
theorem B576629 : Blo 381763 576629 := bbase (se 5 (by rfl) ⟨27029, by rfl⟩ : syracuseStep 576629 = 54059) (by norm_num)
theorem B969853 : Blo 381763 969853 := bbase (se 3 (by rfl) ⟨181847, by rfl⟩ : syracuseStep 969853 = 363695) (by norm_num)
theorem B576653 : Blo 381763 576653 := bbase (se 3 (by rfl) ⟨108122, by rfl⟩ : syracuseStep 576653 = 216245) (by norm_num)
theorem B576677 : Blo 381763 576677 := bbase (se 4 (by rfl) ⟨54063, by rfl⟩ : syracuseStep 576677 = 108127) (by norm_num)
theorem B543925 : Blo 381763 543925 := bbase (se 5 (by rfl) ⟨25496, by rfl⟩ : syracuseStep 543925 = 50993) (by norm_num)
theorem B576701 : Blo 381763 576701 := bbase (se 3 (by rfl) ⟨108131, by rfl⟩ : syracuseStep 576701 = 216263) (by norm_num)
theorem B576725 : Blo 381763 576725 := bbase (se 7 (by rfl) ⟨6758, by rfl⟩ : syracuseStep 576725 = 13517) (by norm_num)
theorem B969965 : Blo 381763 969965 := bbase (se 3 (by rfl) ⟨181868, by rfl⟩ : syracuseStep 969965 = 363737) (by norm_num)
theorem B576749 : Blo 381763 576749 := bbase (se 3 (by rfl) ⟨108140, by rfl⟩ : syracuseStep 576749 = 216281) (by norm_num)
theorem B576773 : Blo 381763 576773 := bbase (se 4 (by rfl) ⟨54072, by rfl⟩ : syracuseStep 576773 = 108145) (by norm_num)
theorem B1461509 : Blo 381763 1461509 := bbase (se 4 (by rfl) ⟨137016, by rfl⟩ : syracuseStep 1461509 = 274033) (by norm_num)
theorem B642325 : Blo 381763 642325 := bbase (se 6 (by rfl) ⟨15054, by rfl⟩ : syracuseStep 642325 = 30109) (by norm_num)
theorem B576797 : Blo 381763 576797 := bbase (se 3 (by rfl) ⟨108149, by rfl⟩ : syracuseStep 576797 = 216299) (by norm_num)
theorem B576821 : Blo 381763 576821 := bbase (se 5 (by rfl) ⟨27038, by rfl⟩ : syracuseStep 576821 = 54077) (by norm_num)
theorem B576845 : Blo 381763 576845 := bbase (se 3 (by rfl) ⟨108158, by rfl⟩ : syracuseStep 576845 = 216317) (by norm_num)
theorem B576869 : Blo 381763 576869 := bbase (se 4 (by rfl) ⟨54081, by rfl⟩ : syracuseStep 576869 = 108163) (by norm_num)
theorem B1297781 : Blo 381763 1297781 := bbase (se 5 (by rfl) ⟨60833, by rfl⟩ : syracuseStep 1297781 = 121667) (by norm_num)
theorem B576893 : Blo 381763 576893 := bbase (se 3 (by rfl) ⟨108167, by rfl⟩ : syracuseStep 576893 = 216335) (by norm_num)
theorem B576917 : Blo 381763 576917 := bbase (se 6 (by rfl) ⟨13521, by rfl⟩ : syracuseStep 576917 = 27043) (by norm_num)
theorem B970157 : Blo 381763 970157 := bbase (se 3 (by rfl) ⟨181904, by rfl⟩ : syracuseStep 970157 = 363809) (by norm_num)
theorem B576941 : Blo 381763 576941 := bbase (se 3 (by rfl) ⟨108176, by rfl⟩ : syracuseStep 576941 = 216353) (by norm_num)
theorem B576965 : Blo 381763 576965 := bbase (se 4 (by rfl) ⟨54090, by rfl⟩ : syracuseStep 576965 = 108181) (by norm_num)
theorem B576989 : Blo 381763 576989 := bbase (se 3 (by rfl) ⟨108185, by rfl⟩ : syracuseStep 576989 = 216371) (by norm_num)
theorem B577013 : Blo 381763 577013 := bbase (se 5 (by rfl) ⟨27047, by rfl⟩ : syracuseStep 577013 = 54095) (by norm_num)
theorem B577037 : Blo 381763 577037 := bbase (se 3 (by rfl) ⟨108194, by rfl⟩ : syracuseStep 577037 = 216389) (by norm_num)
theorem B577061 : Blo 381763 577061 := bbase (se 4 (by rfl) ⟨54099, by rfl⟩ : syracuseStep 577061 = 108199) (by norm_num)
theorem B1461797 : Blo 381763 1461797 := bbase (se 4 (by rfl) ⟨137043, by rfl⟩ : syracuseStep 1461797 = 274087) (by norm_num)
theorem B577085 : Blo 381763 577085 := bbase (se 3 (by rfl) ⟨108203, by rfl⟩ : syracuseStep 577085 = 216407) (by norm_num)
theorem B577109 : Blo 381763 577109 := bbase (se 8 (by rfl) ⟨3381, by rfl⟩ : syracuseStep 577109 = 6763) (by norm_num)
theorem B577133 : Blo 381763 577133 := bbase (se 3 (by rfl) ⟨108212, by rfl⟩ : syracuseStep 577133 = 216425) (by norm_num)
theorem B577157 : Blo 381763 577157 := bbase (se 4 (by rfl) ⟨54108, by rfl⟩ : syracuseStep 577157 = 108217) (by norm_num)
theorem B577181 : Blo 381763 577181 := bbase (se 3 (by rfl) ⟨108221, by rfl⟩ : syracuseStep 577181 = 216443) (by norm_num)
theorem B544421 : Blo 381763 544421 := bbase (se 4 (by rfl) ⟨51039, by rfl⟩ : syracuseStep 544421 = 102079) (by norm_num)
theorem B577205 : Blo 381763 577205 := bbase (se 5 (by rfl) ⟨27056, by rfl⟩ : syracuseStep 577205 = 54113) (by norm_num)
theorem B577229 : Blo 381763 577229 := bbase (se 3 (by rfl) ⟨108230, by rfl⟩ : syracuseStep 577229 = 216461) (by norm_num)
theorem B1232597 : Blo 381763 1232597 := bbase (se 7 (by rfl) ⟨14444, by rfl⟩ : syracuseStep 1232597 = 28889) (by norm_num)
theorem B577253 : Blo 381763 577253 := bbase (se 4 (by rfl) ⟨54117, by rfl⟩ : syracuseStep 577253 = 108235) (by norm_num)
theorem B577277 : Blo 381763 577277 := bbase (se 3 (by rfl) ⟨108239, by rfl⟩ : syracuseStep 577277 = 216479) (by norm_num)
theorem B970501 : Blo 381763 970501 := bbase (se 4 (by rfl) ⟨90984, by rfl⟩ : syracuseStep 970501 = 181969) (by norm_num)
theorem B741133 : Blo 381763 741133 := bbase (se 3 (by rfl) ⟨138962, by rfl⟩ : syracuseStep 741133 = 277925) (by norm_num)
theorem B577301 : Blo 381763 577301 := bbase (se 6 (by rfl) ⟨13530, by rfl⟩ : syracuseStep 577301 = 27061) (by norm_num)
theorem B1298213 : Blo 381763 1298213 := bbase (se 4 (by rfl) ⟨121707, by rfl⟩ : syracuseStep 1298213 = 243415) (by norm_num)
theorem B577325 : Blo 381763 577325 := bbase (se 3 (by rfl) ⟨108248, by rfl⟩ : syracuseStep 577325 = 216497) (by norm_num)
theorem B577349 : Blo 381763 577349 := bbase (se 4 (by rfl) ⟨54126, by rfl⟩ : syracuseStep 577349 = 108253) (by norm_num)
theorem B577373 : Blo 381763 577373 := bbase (se 3 (by rfl) ⟨108257, by rfl⟩ : syracuseStep 577373 = 216515) (by norm_num)
theorem B970613 : Blo 381763 970613 := bbase (se 5 (by rfl) ⟨45497, by rfl⟩ : syracuseStep 970613 = 90995) (by norm_num)
theorem B577397 : Blo 381763 577397 := bbase (se 5 (by rfl) ⟨27065, by rfl⟩ : syracuseStep 577397 = 54131) (by norm_num)
theorem B577421 : Blo 381763 577421 := bbase (se 3 (by rfl) ⟨108266, by rfl⟩ : syracuseStep 577421 = 216533) (by norm_num)
theorem B577445 : Blo 381763 577445 := bbase (se 4 (by rfl) ⟨54135, by rfl⟩ : syracuseStep 577445 = 108271) (by norm_num)
theorem B577469 : Blo 381763 577469 := bbase (se 3 (by rfl) ⟨108275, by rfl⟩ : syracuseStep 577469 = 216551) (by norm_num)
theorem B577493 : Blo 381763 577493 := bbase (se 7 (by rfl) ⟨6767, by rfl⟩ : syracuseStep 577493 = 13535) (by norm_num)
theorem B577517 : Blo 381763 577517 := bbase (se 3 (by rfl) ⟨108284, by rfl⟩ : syracuseStep 577517 = 216569) (by norm_num)
theorem B577541 : Blo 381763 577541 := bbase (se 4 (by rfl) ⟨54144, by rfl⟩ : syracuseStep 577541 = 108289) (by norm_num)
theorem B577565 : Blo 381763 577565 := bbase (se 3 (by rfl) ⟨108293, by rfl⟩ : syracuseStep 577565 = 216587) (by norm_num)
theorem B970805 : Blo 381763 970805 := bbase (se 5 (by rfl) ⟨45506, by rfl⟩ : syracuseStep 970805 = 91013) (by norm_num)
theorem B577589 : Blo 381763 577589 := bbase (se 5 (by rfl) ⟨27074, by rfl⟩ : syracuseStep 577589 = 54149) (by norm_num)
theorem B872525 : Blo 381763 872525 := bbase (se 3 (by rfl) ⟨163598, by rfl⟩ : syracuseStep 872525 = 327197) (by norm_num)
theorem B577613 : Blo 381763 577613 := bbase (se 3 (by rfl) ⟨108302, by rfl⟩ : syracuseStep 577613 = 216605) (by norm_num)
theorem B413797 : Blo 381763 413797 := bbase (se 4 (by rfl) ⟨38793, by rfl⟩ : syracuseStep 413797 = 77587) (by norm_num)
theorem B577637 : Blo 381763 577637 := bbase (se 4 (by rfl) ⟨54153, by rfl⟩ : syracuseStep 577637 = 108307) (by norm_num)
theorem B577661 : Blo 381763 577661 := bbase (se 3 (by rfl) ⟨108311, by rfl⟩ : syracuseStep 577661 = 216623) (by norm_num)
theorem B577685 : Blo 381763 577685 := bbase (se 6 (by rfl) ⟨13539, by rfl⟩ : syracuseStep 577685 = 27079) (by norm_num)
theorem B577709 : Blo 381763 577709 := bbase (se 3 (by rfl) ⟨108320, by rfl⟩ : syracuseStep 577709 = 216641) (by norm_num)
theorem B577733 : Blo 381763 577733 := bbase (se 4 (by rfl) ⟨54162, by rfl⟩ : syracuseStep 577733 = 108325) (by norm_num)
theorem B544973 : Blo 381763 544973 := bbase (se 3 (by rfl) ⟨102182, by rfl⟩ : syracuseStep 544973 = 204365) (by norm_num)
theorem B1298645 : Blo 381763 1298645 := bbase (se 7 (by rfl) ⟨15218, by rfl⟩ : syracuseStep 1298645 = 30437) (by norm_num)
theorem B577757 : Blo 381763 577757 := bbase (se 3 (by rfl) ⟨108329, by rfl⟩ : syracuseStep 577757 = 216659) (by norm_num)
theorem B577781 : Blo 381763 577781 := bbase (se 5 (by rfl) ⟨27083, by rfl⟩ : syracuseStep 577781 = 54167) (by norm_num)
theorem B577805 : Blo 381763 577805 := bbase (se 3 (by rfl) ⟨108338, by rfl⟩ : syracuseStep 577805 = 216677) (by norm_num)
theorem B577829 : Blo 381763 577829 := bbase (se 4 (by rfl) ⟨54171, by rfl⟩ : syracuseStep 577829 = 108343) (by norm_num)
theorem B577853 : Blo 381763 577853 := bbase (se 3 (by rfl) ⟨108347, by rfl⟩ : syracuseStep 577853 = 216695) (by norm_num)
theorem B577877 : Blo 381763 577877 := bbase (se 10 (by rfl) ⟨846, by rfl⟩ : syracuseStep 577877 = 1693) (by norm_num)
theorem B577901 : Blo 381763 577901 := bbase (se 3 (by rfl) ⟨108356, by rfl⟩ : syracuseStep 577901 = 216713) (by norm_num)
theorem B577925 : Blo 381763 577925 := bbase (se 4 (by rfl) ⟨54180, by rfl⟩ : syracuseStep 577925 = 108361) (by norm_num)
theorem B971149 : Blo 381763 971149 := bbase (se 3 (by rfl) ⟨182090, by rfl⟩ : syracuseStep 971149 = 364181) (by norm_num)
theorem B577949 : Blo 381763 577949 := bbase (se 3 (by rfl) ⟨108365, by rfl⟩ : syracuseStep 577949 = 216731) (by norm_num)
theorem B577973 : Blo 381763 577973 := bbase (se 5 (by rfl) ⟨27092, by rfl⟩ : syracuseStep 577973 = 54185) (by norm_num)
theorem B577997 : Blo 381763 577997 := bbase (se 3 (by rfl) ⟨108374, by rfl⟩ : syracuseStep 577997 = 216749) (by norm_num)
theorem B578021 : Blo 381763 578021 := bbase (se 4 (by rfl) ⟨54189, by rfl⟩ : syracuseStep 578021 = 108379) (by norm_num)
theorem B971261 : Blo 381763 971261 := bbase (se 3 (by rfl) ⟨182111, by rfl⟩ : syracuseStep 971261 = 364223) (by norm_num)
theorem B578045 : Blo 381763 578045 := bbase (se 3 (by rfl) ⟨108383, by rfl⟩ : syracuseStep 578045 = 216767) (by norm_num)
theorem B578069 : Blo 381763 578069 := bbase (se 6 (by rfl) ⟨13548, by rfl⟩ : syracuseStep 578069 = 27097) (by norm_num)
theorem B578093 : Blo 381763 578093 := bbase (se 3 (by rfl) ⟨108392, by rfl⟩ : syracuseStep 578093 = 216785) (by norm_num)
theorem B578117 : Blo 381763 578117 := bbase (se 4 (by rfl) ⟨54198, by rfl⟩ : syracuseStep 578117 = 108397) (by norm_num)
theorem B578141 : Blo 381763 578141 := bbase (se 3 (by rfl) ⟨108401, by rfl⟩ : syracuseStep 578141 = 216803) (by norm_num)
theorem B971365 : Blo 381763 971365 := bbase (se 4 (by rfl) ⟨91065, by rfl⟩ : syracuseStep 971365 = 182131) (by norm_num)
theorem B578165 : Blo 381763 578165 := bbase (se 5 (by rfl) ⟨27101, by rfl⟩ : syracuseStep 578165 = 54203) (by norm_num)
theorem B1299077 : Blo 381763 1299077 := bbase (se 4 (by rfl) ⟨121788, by rfl⟩ : syracuseStep 1299077 = 243577) (by norm_num)
theorem B578189 : Blo 381763 578189 := bbase (se 3 (by rfl) ⟨108410, by rfl⟩ : syracuseStep 578189 = 216821) (by norm_num)
theorem B578213 : Blo 381763 578213 := bbase (se 4 (by rfl) ⟨54207, by rfl⟩ : syracuseStep 578213 = 108415) (by norm_num)
theorem B971453 : Blo 381763 971453 := bbase (se 3 (by rfl) ⟨182147, by rfl⟩ : syracuseStep 971453 = 364295) (by norm_num)
theorem B578237 : Blo 381763 578237 := bbase (se 3 (by rfl) ⟨108419, by rfl⟩ : syracuseStep 578237 = 216839) (by norm_num)
theorem B1462981 : Blo 381763 1462981 := bbase (se 4 (by rfl) ⟨137154, by rfl⟩ : syracuseStep 1462981 = 274309) (by norm_num)
theorem B578261 : Blo 381763 578261 := bbase (se 7 (by rfl) ⟨6776, by rfl⟩ : syracuseStep 578261 = 13553) (by norm_num)
theorem B578285 : Blo 381763 578285 := bbase (se 3 (by rfl) ⟨108428, by rfl⟩ : syracuseStep 578285 = 216857) (by norm_num)
theorem B2904821 : Blo 381763 2904821 := bbase (se 5 (by rfl) ⟨136163, by rfl⟩ : syracuseStep 2904821 = 272327) (by norm_num)
theorem B578309 : Blo 381763 578309 := bbase (se 4 (by rfl) ⟨54216, by rfl⟩ : syracuseStep 578309 = 108433) (by norm_num)
theorem B578333 : Blo 381763 578333 := bbase (se 3 (by rfl) ⟨108437, by rfl⟩ : syracuseStep 578333 = 216875) (by norm_num)
theorem B1233701 : Blo 381763 1233701 := bbase (se 4 (by rfl) ⟨115659, by rfl⟩ : syracuseStep 1233701 = 231319) (by norm_num)
theorem B578357 : Blo 381763 578357 := bbase (se 5 (by rfl) ⟨27110, by rfl⟩ : syracuseStep 578357 = 54221) (by norm_num)
theorem B578381 : Blo 381763 578381 := bbase (se 3 (by rfl) ⟨108446, by rfl⟩ : syracuseStep 578381 = 216893) (by norm_num)
theorem B578405 : Blo 381763 578405 := bbase (se 4 (by rfl) ⟨54225, by rfl⟩ : syracuseStep 578405 = 108451) (by norm_num)
theorem B578429 : Blo 381763 578429 := bbase (se 3 (by rfl) ⟨108455, by rfl⟩ : syracuseStep 578429 = 216911) (by norm_num)
theorem B578453 : Blo 381763 578453 := bbase (se 6 (by rfl) ⟨13557, by rfl⟩ : syracuseStep 578453 = 27115) (by norm_num)
theorem B578477 : Blo 381763 578477 := bbase (se 3 (by rfl) ⟨108464, by rfl⟩ : syracuseStep 578477 = 216929) (by norm_num)
theorem B545725 : Blo 381763 545725 := bbase (se 3 (by rfl) ⟨102323, by rfl⟩ : syracuseStep 545725 = 204647) (by norm_num)
theorem B578501 : Blo 381763 578501 := bbase (se 4 (by rfl) ⟨54234, by rfl⟩ : syracuseStep 578501 = 108469) (by norm_num)
theorem B578525 : Blo 381763 578525 := bbase (se 3 (by rfl) ⟨108473, by rfl⟩ : syracuseStep 578525 = 216947) (by norm_num)
theorem B1463285 : Blo 381763 1463285 := bbase (se 5 (by rfl) ⟨68591, by rfl⟩ : syracuseStep 1463285 = 137183) (by norm_num)
theorem B578549 : Blo 381763 578549 := bbase (se 5 (by rfl) ⟨27119, by rfl⟩ : syracuseStep 578549 = 54239) (by norm_num)
theorem B578573 : Blo 381763 578573 := bbase (se 3 (by rfl) ⟨108482, by rfl⟩ : syracuseStep 578573 = 216965) (by norm_num)
theorem B971797 : Blo 381763 971797 := bbase (se 6 (by rfl) ⟨22776, by rfl⟩ : syracuseStep 971797 = 45553) (by norm_num)
theorem B578597 : Blo 381763 578597 := bbase (se 4 (by rfl) ⟨54243, by rfl⟩ : syracuseStep 578597 = 108487) (by norm_num)
theorem B2184245 : Blo 381763 2184245 := bbase (se 5 (by rfl) ⟨102386, by rfl⟩ : syracuseStep 2184245 = 204773) (by norm_num)
theorem B1299509 : Blo 381763 1299509 := bbase (se 5 (by rfl) ⟨60914, by rfl⟩ : syracuseStep 1299509 = 121829) (by norm_num)
theorem B578621 : Blo 381763 578621 := bbase (se 3 (by rfl) ⟨108491, by rfl⟩ : syracuseStep 578621 = 216983) (by norm_num)
theorem B1758293 : Blo 381763 1758293 := bbase (se 8 (by rfl) ⟨10302, by rfl⟩ : syracuseStep 1758293 = 20605) (by norm_num)
theorem B578645 : Blo 381763 578645 := bbase (se 8 (by rfl) ⟨3390, by rfl⟩ : syracuseStep 578645 = 6781) (by norm_num)
theorem B971909 : Blo 381763 971909 := bbase (se 4 (by rfl) ⟨91116, by rfl⟩ : syracuseStep 971909 = 182233) (by norm_num)
theorem B644341 : Blo 381763 644341 := bbase (se 5 (by rfl) ⟨30203, by rfl⟩ : syracuseStep 644341 = 60407) (by norm_num)
theorem B3855637 : Blo 381763 3855637 := bbase (se 6 (by rfl) ⟨90366, by rfl⟩ : syracuseStep 3855637 = 180733) (by norm_num)
theorem B972101 : Blo 381763 972101 := bbase (se 4 (by rfl) ⟨91134, by rfl⟩ : syracuseStep 972101 = 182269) (by norm_num)
theorem B644429 : Blo 381763 644429 := bbase (se 3 (by rfl) ⟨120830, by rfl⟩ : syracuseStep 644429 = 241661) (by norm_num)
theorem B644557 : Blo 381763 644557 := bbase (se 3 (by rfl) ⟨120854, by rfl⟩ : syracuseStep 644557 = 241709) (by norm_num)
theorem B1299941 : Blo 381763 1299941 := bbase (se 4 (by rfl) ⟨121869, by rfl⟩ : syracuseStep 1299941 = 243739) (by norm_num)
theorem B644645 : Blo 381763 644645 := bbase (se 4 (by rfl) ⟨60435, by rfl⟩ : syracuseStep 644645 = 120871) (by norm_num)
theorem B874037 : Blo 381763 874037 := bbase (se 5 (by rfl) ⟨40970, by rfl⟩ : syracuseStep 874037 = 81941) (by norm_num)
theorem B972445 : Blo 381763 972445 := bbase (se 3 (by rfl) ⟨182333, by rfl⟩ : syracuseStep 972445 = 364667) (by norm_num)
theorem B644773 : Blo 381763 644773 := bbase (se 4 (by rfl) ⟨60447, by rfl⟩ : syracuseStep 644773 = 120895) (by norm_num)
theorem B546517 : Blo 381763 546517 := bbase (se 7 (by rfl) ⟨6404, by rfl⟩ : syracuseStep 546517 = 12809) (by norm_num)
theorem B644861 : Blo 381763 644861 := bbase (se 3 (by rfl) ⟨120911, by rfl⟩ : syracuseStep 644861 = 241823) (by norm_num)
theorem B972557 : Blo 381763 972557 := bbase (se 3 (by rfl) ⟨182354, by rfl⟩ : syracuseStep 972557 = 364709) (by norm_num)
theorem B874277 : Blo 381763 874277 := bbase (se 4 (by rfl) ⟨81963, by rfl⟩ : syracuseStep 874277 = 163927) (by norm_num)
theorem B612173 : Blo 381763 612173 := bbase (se 3 (by rfl) ⟨114782, by rfl⟩ : syracuseStep 612173 = 229565) (by norm_num)
theorem B644989 : Blo 381763 644989 := bbase (se 3 (by rfl) ⟨120935, by rfl⟩ : syracuseStep 644989 = 241871) (by norm_num)
theorem B1300373 : Blo 381763 1300373 := bbase (se 6 (by rfl) ⟨30477, by rfl⟩ : syracuseStep 1300373 = 60955) (by norm_num)
theorem B612301 : Blo 381763 612301 := bbase (se 3 (by rfl) ⟨114806, by rfl⟩ : syracuseStep 612301 = 229613) (by norm_num)
theorem B972749 : Blo 381763 972749 := bbase (se 3 (by rfl) ⟨182390, by rfl⟩ : syracuseStep 972749 = 364781) (by norm_num)
theorem B645077 : Blo 381763 645077 := bbase (se 7 (by rfl) ⟨7559, by rfl⟩ : syracuseStep 645077 = 15119) (by norm_num)
theorem B546853 : Blo 381763 546853 := bbase (se 4 (by rfl) ⟨51267, by rfl⟩ : syracuseStep 546853 = 102535) (by norm_num)
theorem B645205 : Blo 381763 645205 := bbase (se 8 (by rfl) ⟨3780, by rfl⟩ : syracuseStep 645205 = 7561) (by norm_num)
theorem B645293 : Blo 381763 645293 := bbase (se 3 (by rfl) ⟨120992, by rfl⟩ : syracuseStep 645293 = 241985) (by norm_num)
theorem B3496117 : Blo 381763 3496117 := bbase (se 5 (by rfl) ⟨163880, by rfl⟩ : syracuseStep 3496117 = 327761) (by norm_num)
theorem B547069 : Blo 381763 547069 := bbase (se 3 (by rfl) ⟨102575, by rfl⟩ : syracuseStep 547069 = 205151) (by norm_num)
theorem B776461 : Blo 381763 776461 := bbase (se 3 (by rfl) ⟨145586, by rfl⟩ : syracuseStep 776461 = 291173) (by norm_num)
theorem B973093 : Blo 381763 973093 := bbase (se 4 (by rfl) ⟨91227, by rfl⟩ : syracuseStep 973093 = 182455) (by norm_num)
theorem B645421 : Blo 381763 645421 := bbase (se 3 (by rfl) ⟨121016, by rfl⟩ : syracuseStep 645421 = 242033) (by norm_num)
theorem B1300805 : Blo 381763 1300805 := bbase (se 4 (by rfl) ⟨121950, by rfl⟩ : syracuseStep 1300805 = 243901) (by norm_num)
theorem B612685 : Blo 381763 612685 := bbase (se 3 (by rfl) ⟨114878, by rfl⟩ : syracuseStep 612685 = 229757) (by norm_num)
theorem B645509 : Blo 381763 645509 := bbase (se 4 (by rfl) ⟨60516, by rfl⟩ : syracuseStep 645509 = 121033) (by norm_num)
theorem B973205 : Blo 381763 973205 := bbase (se 6 (by rfl) ⟨22809, by rfl⟩ : syracuseStep 973205 = 45619) (by norm_num)
theorem B2775509 : Blo 381763 2775509 := bbase (se 7 (by rfl) ⟨32525, by rfl⟩ : syracuseStep 2775509 = 65051) (by norm_num)
theorem B875005 : Blo 381763 875005 := bbase (se 3 (by rfl) ⟨164063, by rfl⟩ : syracuseStep 875005 = 328127) (by norm_num)
theorem B645637 : Blo 381763 645637 := bbase (se 4 (by rfl) ⟨60528, by rfl⟩ : syracuseStep 645637 = 121057) (by norm_num)
theorem B612941 : Blo 381763 612941 := bbase (se 3 (by rfl) ⟨114926, by rfl⟩ : syracuseStep 612941 = 229853) (by norm_num)
theorem B973397 : Blo 381763 973397 := bbase (se 8 (by rfl) ⟨5703, by rfl⟩ : syracuseStep 973397 = 11407) (by norm_num)
theorem B645725 : Blo 381763 645725 := bbase (se 3 (by rfl) ⟨121073, by rfl⟩ : syracuseStep 645725 = 242147) (by norm_num)
theorem B547445 : Blo 381763 547445 := bbase (se 5 (by rfl) ⟨25661, by rfl⟩ : syracuseStep 547445 = 51323) (by norm_num)
theorem B1235621 : Blo 381763 1235621 := bbase (se 4 (by rfl) ⟨115839, by rfl⟩ : syracuseStep 1235621 = 231679) (by norm_num)
theorem B645853 : Blo 381763 645853 := bbase (se 3 (by rfl) ⟨121097, by rfl⟩ : syracuseStep 645853 = 242195) (by norm_num)
theorem B1301237 : Blo 381763 1301237 := bbase (se 5 (by rfl) ⟨60995, by rfl⟩ : syracuseStep 1301237 = 121991) (by norm_num)
theorem B875269 : Blo 381763 875269 := bbase (se 4 (by rfl) ⟨82056, by rfl⟩ : syracuseStep 875269 = 164113) (by norm_num)
theorem B645941 : Blo 381763 645941 := bbase (se 5 (by rfl) ⟨30278, by rfl⟩ : syracuseStep 645941 = 60557) (by norm_num)
theorem B1104725 : Blo 381763 1104725 := bbase (se 9 (by rfl) ⟨3236, by rfl⟩ : syracuseStep 1104725 = 6473) (by norm_num)
theorem B973741 : Blo 381763 973741 := bbase (se 3 (by rfl) ⟨182576, by rfl⟩ : syracuseStep 973741 = 365153) (by norm_num)
theorem B646069 : Blo 381763 646069 := bbase (se 5 (by rfl) ⟨30284, by rfl⟩ : syracuseStep 646069 = 60569) (by norm_num)
theorem B646157 : Blo 381763 646157 := bbase (se 3 (by rfl) ⟨121154, by rfl⟩ : syracuseStep 646157 = 242309) (by norm_num)
theorem B973853 : Blo 381763 973853 := bbase (se 3 (by rfl) ⟨182597, by rfl⟩ : syracuseStep 973853 = 365195) (by norm_num)
theorem B646285 : Blo 381763 646285 := bbase (se 3 (by rfl) ⟨121178, by rfl⟩ : syracuseStep 646285 = 242357) (by norm_num)
theorem B1301669 : Blo 381763 1301669 := bbase (se 4 (by rfl) ⟨122031, by rfl⟩ : syracuseStep 1301669 = 244063) (by norm_num)
theorem B2186453 : Blo 381763 2186453 := bbase (se 7 (by rfl) ⟨25622, by rfl⟩ : syracuseStep 2186453 = 51245) (by norm_num)
theorem B974045 : Blo 381763 974045 := bbase (se 3 (by rfl) ⟨182633, by rfl⟩ : syracuseStep 974045 = 365267) (by norm_num)
theorem B646373 : Blo 381763 646373 := bbase (se 4 (by rfl) ⟨60597, by rfl⟩ : syracuseStep 646373 = 121195) (by norm_num)
theorem B646501 : Blo 381763 646501 := bbase (se 4 (by rfl) ⟨60609, by rfl⟩ : syracuseStep 646501 = 121219) (by norm_num)
theorem B613813 : Blo 381763 613813 := bbase (se 5 (by rfl) ⟨28772, by rfl⟩ : syracuseStep 613813 = 57545) (by norm_num)
theorem B646589 : Blo 381763 646589 := bbase (se 3 (by rfl) ⟨121235, by rfl⟩ : syracuseStep 646589 = 242471) (by norm_num)
theorem B777701 : Blo 381763 777701 := bbase (se 4 (by rfl) ⟨72909, by rfl⟩ : syracuseStep 777701 = 145819) (by norm_num)
theorem B613909 : Blo 381763 613909 := bbase (se 6 (by rfl) ⟨14388, by rfl⟩ : syracuseStep 613909 = 28777) (by norm_num)
theorem B974389 : Blo 381763 974389 := bbase (se 5 (by rfl) ⟨45674, by rfl⟩ : syracuseStep 974389 = 91349) (by norm_num)
theorem B646717 : Blo 381763 646717 := bbase (se 3 (by rfl) ⟨121259, by rfl⟩ : syracuseStep 646717 = 242519) (by norm_num)
theorem B1662565 : Blo 381763 1662565 := bbase (se 4 (by rfl) ⟨155865, by rfl⟩ : syracuseStep 1662565 = 311731) (by norm_num)
theorem B646805 : Blo 381763 646805 := bbase (se 6 (by rfl) ⟨15159, by rfl⟩ : syracuseStep 646805 = 30319) (by norm_num)
theorem B974501 : Blo 381763 974501 := bbase (se 4 (by rfl) ⟨91359, by rfl⟩ : syracuseStep 974501 = 182719) (by norm_num)
theorem B581293 : Blo 381763 581293 := bbase (se 3 (by rfl) ⟨108992, by rfl⟩ : syracuseStep 581293 = 217985) (by norm_num)
theorem B614069 : Blo 381763 614069 := bbase (se 5 (by rfl) ⟨28784, by rfl⟩ : syracuseStep 614069 = 57569) (by norm_num)
theorem B646933 : Blo 381763 646933 := bbase (se 6 (by rfl) ⟨15162, by rfl⟩ : syracuseStep 646933 = 30325) (by norm_num)
theorem B974693 : Blo 381763 974693 := bbase (se 4 (by rfl) ⟨91377, by rfl⟩ : syracuseStep 974693 = 182755) (by norm_num)
theorem B647021 : Blo 381763 647021 := bbase (se 3 (by rfl) ⟨121316, by rfl⟩ : syracuseStep 647021 = 242633) (by norm_num)
theorem B483185 : Blo 381763 483185 := bbase (se 2 (by rfl) ⟨181194, by rfl⟩ : syracuseStep 483185 = 362389) (by norm_num)
theorem B483241 : Blo 381763 483241 := bbase (se 2 (by rfl) ⟨181215, by rfl⟩ : syracuseStep 483241 = 362431) (by norm_num)
theorem B647149 : Blo 381763 647149 := bbase (se 3 (by rfl) ⟨121340, by rfl⟩ : syracuseStep 647149 = 242681) (by norm_num)
theorem B548869 : Blo 381763 548869 := bbase (se 4 (by rfl) ⟨51456, by rfl⟩ : syracuseStep 548869 = 102913) (by norm_num)
theorem B483337 : Blo 381763 483337 := bbase (se 2 (by rfl) ⟨181251, by rfl⟩ : syracuseStep 483337 = 362503) (by norm_num)
theorem B647237 : Blo 381763 647237 := bbase (se 4 (by rfl) ⟨60678, by rfl⟩ : syracuseStep 647237 = 121357) (by norm_num)
theorem B778349 : Blo 381763 778349 := bbase (se 3 (by rfl) ⟨145940, by rfl⟩ : syracuseStep 778349 = 291881) (by norm_num)
theorem B483509 : Blo 381763 483509 := bbase (se 5 (by rfl) ⟨22664, by rfl⟩ : syracuseStep 483509 = 45329) (by norm_num)
theorem B1401013 : Blo 381763 1401013 := bbase (se 5 (by rfl) ⟨65672, by rfl⟩ : syracuseStep 1401013 = 131345) (by norm_num)
theorem B975037 : Blo 381763 975037 := bbase (se 3 (by rfl) ⟨182819, by rfl⟩ : syracuseStep 975037 = 365639) (by norm_num)
theorem B647365 : Blo 381763 647365 := bbase (se 4 (by rfl) ⟨60690, by rfl⟩ : syracuseStep 647365 = 121381) (by norm_num)
theorem B483565 : Blo 381763 483565 := bbase (se 3 (by rfl) ⟨90668, by rfl⟩ : syracuseStep 483565 = 181337) (by norm_num)
theorem B647453 : Blo 381763 647453 := bbase (se 3 (by rfl) ⟨121397, by rfl⟩ : syracuseStep 647453 = 242795) (by norm_num)
theorem B975149 : Blo 381763 975149 := bbase (se 3 (by rfl) ⟨182840, by rfl⟩ : syracuseStep 975149 = 365681) (by norm_num)
theorem B483661 : Blo 381763 483661 := bbase (se 3 (by rfl) ⟨90686, by rfl⟩ : syracuseStep 483661 = 181373) (by norm_num)
theorem B647581 : Blo 381763 647581 := bbase (se 3 (by rfl) ⟨121421, by rfl⟩ : syracuseStep 647581 = 242843) (by norm_num)
theorem B1106389 : Blo 381763 1106389 := bbase (se 7 (by rfl) ⟨12965, by rfl⟩ : syracuseStep 1106389 = 25931) (by norm_num)
theorem B975341 : Blo 381763 975341 := bbase (se 3 (by rfl) ⟨182876, by rfl⟩ : syracuseStep 975341 = 365753) (by norm_num)
theorem B647669 : Blo 381763 647669 := bbase (se 5 (by rfl) ⟨30359, by rfl⟩ : syracuseStep 647669 = 60719) (by norm_num)
theorem B483833 : Blo 381763 483833 := bbase (se 2 (by rfl) ⟨181437, by rfl⟩ : syracuseStep 483833 = 362875) (by norm_num)
theorem B483889 : Blo 381763 483889 := bbase (se 2 (by rfl) ⟨181458, by rfl⟩ : syracuseStep 483889 = 362917) (by norm_num)
theorem B647797 : Blo 381763 647797 := bbase (se 5 (by rfl) ⟨30365, by rfl⟩ : syracuseStep 647797 = 60731) (by norm_num)
theorem B483985 : Blo 381763 483985 := bbase (se 2 (by rfl) ⟨181494, by rfl⟩ : syracuseStep 483985 = 362989) (by norm_num)
theorem B647885 : Blo 381763 647885 := bbase (se 3 (by rfl) ⟨121478, by rfl⟩ : syracuseStep 647885 = 242957) (by norm_num)
theorem B615197 : Blo 381763 615197 := bbase (se 3 (by rfl) ⟨115349, by rfl⟩ : syracuseStep 615197 = 230699) (by norm_num)
theorem B3269429 : Blo 381763 3269429 := bbase (se 5 (by rfl) ⟨153254, by rfl⟩ : syracuseStep 3269429 = 306509) (by norm_num)
theorem B484157 : Blo 381763 484157 := bbase (se 3 (by rfl) ⟨90779, by rfl⟩ : syracuseStep 484157 = 181559) (by norm_num)
theorem B975685 : Blo 381763 975685 := bbase (se 4 (by rfl) ⟨91470, by rfl⟩ : syracuseStep 975685 = 182941) (by norm_num)
theorem B648013 : Blo 381763 648013 := bbase (se 3 (by rfl) ⟨121502, by rfl⟩ : syracuseStep 648013 = 243005) (by norm_num)
theorem B484213 : Blo 381763 484213 := bbase (se 5 (by rfl) ⟨22697, by rfl⟩ : syracuseStep 484213 = 45395) (by norm_num)
theorem B648101 : Blo 381763 648101 := bbase (se 4 (by rfl) ⟨60759, by rfl⟩ : syracuseStep 648101 = 121519) (by norm_num)
theorem B975797 : Blo 381763 975797 := bbase (se 5 (by rfl) ⟨45740, by rfl⟩ : syracuseStep 975797 = 91481) (by norm_num)
theorem B484309 : Blo 381763 484309 := bbase (se 7 (by rfl) ⟨5675, by rfl⟩ : syracuseStep 484309 = 11351) (by norm_num)
theorem B648229 : Blo 381763 648229 := bbase (se 4 (by rfl) ⟨60771, by rfl⟩ : syracuseStep 648229 = 121543) (by norm_num)
theorem B975989 : Blo 381763 975989 := bbase (se 5 (by rfl) ⟨45749, by rfl⟩ : syracuseStep 975989 = 91499) (by norm_num)
theorem B648317 : Blo 381763 648317 := bbase (se 3 (by rfl) ⟨121559, by rfl⟩ : syracuseStep 648317 = 243119) (by norm_num)
theorem B484481 : Blo 381763 484481 := bbase (se 2 (by rfl) ⟨181680, by rfl⟩ : syracuseStep 484481 = 363361) (by norm_num)
theorem B484537 : Blo 381763 484537 := bbase (se 2 (by rfl) ⟨181701, by rfl⟩ : syracuseStep 484537 = 363403) (by norm_num)
theorem B779453 : Blo 381763 779453 := bbase (se 3 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 779453 = 292295) (by norm_num)
theorem B779485 : Blo 381763 779485 := bbase (se 3 (by rfl) ⟨146153, by rfl⟩ : syracuseStep 779485 = 292307) (by norm_num)
theorem B648445 : Blo 381763 648445 := bbase (se 3 (by rfl) ⟨121583, by rfl⟩ : syracuseStep 648445 = 243167) (by norm_num)
theorem B484633 : Blo 381763 484633 := bbase (se 2 (by rfl) ⟨181737, by rfl⟩ : syracuseStep 484633 = 363475) (by norm_num)
theorem B615709 : Blo 381763 615709 := bbase (se 3 (by rfl) ⟨115445, by rfl⟩ : syracuseStep 615709 = 230891) (by norm_num)
theorem B517429 : Blo 381763 517429 := bbase (se 5 (by rfl) ⟨24254, by rfl⟩ : syracuseStep 517429 = 48509) (by norm_num)
theorem B3106133 : Blo 381763 3106133 := bbase (se 12 (by rfl) ⟨1137, by rfl⟩ : syracuseStep 3106133 = 2275) (by norm_num)
theorem B648533 : Blo 381763 648533 := bbase (se 12 (by rfl) ⟨237, by rfl⟩ : syracuseStep 648533 = 475) (by norm_num)
theorem B484805 : Blo 381763 484805 := bbase (se 4 (by rfl) ⟨45450, by rfl⟩ : syracuseStep 484805 = 90901) (by norm_num)
theorem B976333 : Blo 381763 976333 := bbase (se 3 (by rfl) ⟨183062, by rfl⟩ : syracuseStep 976333 = 366125) (by norm_num)
theorem B648661 : Blo 381763 648661 := bbase (se 7 (by rfl) ⟨7601, by rfl⟩ : syracuseStep 648661 = 15203) (by norm_num)
theorem B484861 : Blo 381763 484861 := bbase (se 3 (by rfl) ⟨90911, by rfl⟩ : syracuseStep 484861 = 181823) (by norm_num)
theorem B648749 : Blo 381763 648749 := bbase (se 3 (by rfl) ⟨121640, by rfl⟩ : syracuseStep 648749 = 243281) (by norm_num)
theorem B976445 : Blo 381763 976445 := bbase (se 3 (by rfl) ⟨183083, by rfl⟩ : syracuseStep 976445 = 366167) (by norm_num)
theorem B484957 : Blo 381763 484957 := bbase (se 3 (by rfl) ⟨90929, by rfl⟩ : syracuseStep 484957 = 181859) (by norm_num)
theorem B648877 : Blo 381763 648877 := bbase (se 3 (by rfl) ⟨121664, by rfl⟩ : syracuseStep 648877 = 243329) (by norm_num)
theorem B648965 : Blo 381763 648965 := bbase (se 4 (by rfl) ⟨60840, by rfl⟩ : syracuseStep 648965 = 121681) (by norm_num)
theorem B485129 : Blo 381763 485129 := bbase (se 2 (by rfl) ⟨181923, by rfl⟩ : syracuseStep 485129 = 363847) (by norm_num)
theorem B485185 : Blo 381763 485185 := bbase (se 2 (by rfl) ⟨181944, by rfl⟩ : syracuseStep 485185 = 363889) (by norm_num)
theorem B649093 : Blo 381763 649093 := bbase (se 4 (by rfl) ⟨60852, by rfl⟩ : syracuseStep 649093 = 121705) (by norm_num)
theorem B485281 : Blo 381763 485281 := bbase (se 2 (by rfl) ⟨181980, by rfl⟩ : syracuseStep 485281 = 363961) (by norm_num)
theorem B7858133 : Blo 381763 7858133 := bbase (se 7 (by rfl) ⟨92087, by rfl⟩ : syracuseStep 7858133 = 184175) (by norm_num)
theorem B649181 : Blo 381763 649181 := bbase (se 3 (by rfl) ⟨121721, by rfl⟩ : syracuseStep 649181 = 243443) (by norm_num)
theorem B485453 : Blo 381763 485453 := bbase (se 3 (by rfl) ⟨91022, by rfl⟩ : syracuseStep 485453 = 182045) (by norm_num)
theorem B649309 : Blo 381763 649309 := bbase (se 3 (by rfl) ⟨121745, by rfl⟩ : syracuseStep 649309 = 243491) (by norm_num)
theorem B878701 : Blo 381763 878701 := bbase (se 3 (by rfl) ⟨164756, by rfl⟩ : syracuseStep 878701 = 329513) (by norm_num)
theorem B485509 : Blo 381763 485509 := bbase (se 4 (by rfl) ⟨45516, by rfl⟩ : syracuseStep 485509 = 91033) (by norm_num)
theorem B649397 : Blo 381763 649397 := bbase (se 5 (by rfl) ⟨30440, by rfl⟩ : syracuseStep 649397 = 60881) (by norm_num)
theorem B387293 : Blo 381763 387293 := bbase (se 3 (by rfl) ⟨72617, by rfl⟩ : syracuseStep 387293 = 145235) (by norm_num)
theorem B485605 : Blo 381763 485605 := bbase (se 4 (by rfl) ⟨45525, by rfl⟩ : syracuseStep 485605 = 91051) (by norm_num)
theorem B616709 : Blo 381763 616709 := bbase (se 4 (by rfl) ⟨57816, by rfl⟩ : syracuseStep 616709 = 115633) (by norm_num)
theorem B649525 : Blo 381763 649525 := bbase (se 5 (by rfl) ⟨30446, by rfl⟩ : syracuseStep 649525 = 60893) (by norm_num)
theorem B1632581 : Blo 381763 1632581 := bbase (se 4 (by rfl) ⟨153054, by rfl⟩ : syracuseStep 1632581 = 306109) (by norm_num)
theorem B780653 : Blo 381763 780653 := bbase (se 3 (by rfl) ⟨146372, by rfl⟩ : syracuseStep 780653 = 292745) (by norm_num)
theorem B616837 : Blo 381763 616837 := bbase (se 4 (by rfl) ⟨57828, by rfl⟩ : syracuseStep 616837 = 115657) (by norm_num)
theorem B649613 : Blo 381763 649613 := bbase (se 3 (by rfl) ⟨121802, by rfl⟩ : syracuseStep 649613 = 243605) (by norm_num)
theorem B485777 : Blo 381763 485777 := bbase (se 2 (by rfl) ⟨182166, by rfl⟩ : syracuseStep 485777 = 364333) (by norm_num)
theorem B616901 : Blo 381763 616901 := bbase (se 4 (by rfl) ⟨57834, by rfl⟩ : syracuseStep 616901 = 115669) (by norm_num)
theorem B485833 : Blo 381763 485833 := bbase (se 2 (by rfl) ⟨182187, by rfl⟩ : syracuseStep 485833 = 364375) (by norm_num)
theorem B387553 : Blo 381763 387553 := bbase (se 2 (by rfl) ⟨145332, by rfl⟩ : syracuseStep 387553 = 290665) (by norm_num)
theorem B649741 : Blo 381763 649741 := bbase (se 3 (by rfl) ⟨121826, by rfl⟩ : syracuseStep 649741 = 243653) (by norm_num)
theorem B485929 : Blo 381763 485929 := bbase (se 2 (by rfl) ⟨182223, by rfl⟩ : syracuseStep 485929 = 364447) (by norm_num)
theorem B1632869 : Blo 381763 1632869 := bbase (se 4 (by rfl) ⟨153081, by rfl⟩ : syracuseStep 1632869 = 306163) (by norm_num)
theorem B649829 : Blo 381763 649829 := bbase (se 4 (by rfl) ⟨60921, by rfl⟩ : syracuseStep 649829 = 121843) (by norm_num)
theorem B486101 : Blo 381763 486101 := bbase (se 7 (by rfl) ⟨5696, by rfl⟩ : syracuseStep 486101 = 11393) (by norm_num)
theorem B649957 : Blo 381763 649957 := bbase (se 4 (by rfl) ⟨60933, by rfl⟩ : syracuseStep 649957 = 121867) (by norm_num)
theorem B486157 : Blo 381763 486157 := bbase (se 3 (by rfl) ⟨91154, by rfl⟩ : syracuseStep 486157 = 182309) (by norm_num)
theorem B650045 : Blo 381763 650045 := bbase (se 3 (by rfl) ⟨121883, by rfl⟩ : syracuseStep 650045 = 243767) (by norm_num)
theorem B486253 : Blo 381763 486253 := bbase (se 3 (by rfl) ⟨91172, by rfl⟩ : syracuseStep 486253 = 182345) (by norm_num)
theorem B650173 : Blo 381763 650173 := bbase (se 3 (by rfl) ⟨121907, by rfl⟩ : syracuseStep 650173 = 243815) (by norm_num)
theorem B9989077 : Blo 381763 9989077 := bbase (se 7 (by rfl) ⟨117059, by rfl⟩ : syracuseStep 9989077 = 234119) (by norm_num)
theorem B650261 : Blo 381763 650261 := bbase (se 6 (by rfl) ⟨15240, by rfl⟩ : syracuseStep 650261 = 30481) (by norm_num)
theorem B486425 : Blo 381763 486425 := bbase (se 2 (by rfl) ⟨182409, by rfl⟩ : syracuseStep 486425 = 364819) (by norm_num)
theorem B486481 : Blo 381763 486481 := bbase (se 2 (by rfl) ⟨182430, by rfl⟩ : syracuseStep 486481 = 364861) (by norm_num)
theorem B650389 : Blo 381763 650389 := bbase (se 6 (by rfl) ⟨15243, by rfl⟩ : syracuseStep 650389 = 30487) (by norm_num)
theorem B486577 : Blo 381763 486577 := bbase (se 2 (by rfl) ⟨182466, by rfl⟩ : syracuseStep 486577 = 364933) (by norm_num)
theorem B421049 : Blo 381763 421049 := bbase (se 2 (by rfl) ⟨157893, by rfl⟩ : syracuseStep 421049 = 315787) (by norm_num)
theorem B2616533 : Blo 381763 2616533 := bbase (se 7 (by rfl) ⟨30662, by rfl⟩ : syracuseStep 2616533 = 61325) (by norm_num)
theorem B421085 : Blo 381763 421085 := bbase (se 3 (by rfl) ⟨78953, by rfl⟩ : syracuseStep 421085 = 157907) (by norm_num)
theorem B650477 : Blo 381763 650477 := bbase (se 3 (by rfl) ⟨121964, by rfl⟩ : syracuseStep 650477 = 243929) (by norm_num)
theorem B1469765 : Blo 381763 1469765 := bbase (se 4 (by rfl) ⟨137790, by rfl⟩ : syracuseStep 1469765 = 275581) (by norm_num)
theorem B1633621 : Blo 381763 1633621 := bbase (se 11 (by rfl) ⟨1196, by rfl⟩ : syracuseStep 1633621 = 2393) (by norm_num)
theorem B486749 : Blo 381763 486749 := bbase (se 3 (by rfl) ⟨91265, by rfl⟩ : syracuseStep 486749 = 182531) (by norm_num)
theorem B781669 : Blo 381763 781669 := bbase (se 4 (by rfl) ⟨73281, by rfl⟩ : syracuseStep 781669 = 146563) (by norm_num)
theorem B650605 : Blo 381763 650605 := bbase (se 3 (by rfl) ⟨121988, by rfl⟩ : syracuseStep 650605 = 243977) (by norm_num)
theorem B486805 : Blo 381763 486805 := bbase (se 6 (by rfl) ⟨11409, by rfl⟩ : syracuseStep 486805 = 22819) (by norm_num)
theorem B5270933 : Blo 381763 5270933 := bbase (se 6 (by rfl) ⟨123537, by rfl⟩ : syracuseStep 5270933 = 247075) (by norm_num)
theorem B650693 : Blo 381763 650693 := bbase (se 4 (by rfl) ⟨61002, by rfl⟩ : syracuseStep 650693 = 122005) (by norm_num)
theorem B749029 : Blo 381763 749029 := bbase (se 4 (by rfl) ⟨70221, by rfl⟩ : syracuseStep 749029 = 140443) (by norm_num)
theorem B486901 : Blo 381763 486901 := bbase (se 5 (by rfl) ⟨22823, by rfl⟩ : syracuseStep 486901 = 45647) (by norm_num)
theorem B650821 : Blo 381763 650821 := bbase (se 4 (by rfl) ⟨61014, by rfl⟩ : syracuseStep 650821 = 122029) (by norm_num)
theorem B650909 : Blo 381763 650909 := bbase (se 3 (by rfl) ⟨122045, by rfl⟩ : syracuseStep 650909 = 244091) (by norm_num)
theorem B487073 : Blo 381763 487073 := bbase (se 2 (by rfl) ⟨182652, by rfl⟩ : syracuseStep 487073 = 365305) (by norm_num)
theorem B487129 : Blo 381763 487129 := bbase (se 2 (by rfl) ⟨182673, by rfl⟩ : syracuseStep 487129 = 365347) (by norm_num)
theorem B487225 : Blo 381763 487225 := bbase (se 2 (by rfl) ⟨182709, by rfl⟩ : syracuseStep 487225 = 365419) (by norm_num)
theorem B585557 : Blo 381763 585557 := bbase (se 9 (by rfl) ⟨1715, by rfl⟩ : syracuseStep 585557 = 3431) (by norm_num)
theorem B487397 : Blo 381763 487397 := bbase (se 4 (by rfl) ⟨45693, by rfl⟩ : syracuseStep 487397 = 91387) (by norm_num)
theorem B487453 : Blo 381763 487453 := bbase (se 3 (by rfl) ⟨91397, by rfl⟩ : syracuseStep 487453 = 182795) (by norm_num)
theorem B1634357 : Blo 381763 1634357 := bbase (se 5 (by rfl) ⟨76610, by rfl⟩ : syracuseStep 1634357 = 153221) (by norm_num)
theorem B487549 : Blo 381763 487549 := bbase (se 3 (by rfl) ⟨91415, by rfl⟩ : syracuseStep 487549 = 182831) (by norm_num)
theorem B389345 : Blo 381763 389345 := bbase (se 2 (by rfl) ⟨146004, by rfl⟩ : syracuseStep 389345 = 292009) (by norm_num)
theorem B389369 : Blo 381763 389369 := bbase (se 2 (by rfl) ⟨146013, by rfl⟩ : syracuseStep 389369 = 292027) (by norm_num)
theorem B487721 : Blo 381763 487721 := bbase (se 2 (by rfl) ⟨182895, by rfl⟩ : syracuseStep 487721 = 365791) (by norm_num)
theorem B2912597 : Blo 381763 2912597 := bbase (se 10 (by rfl) ⟨4266, by rfl⟩ : syracuseStep 2912597 = 8533) (by norm_num)
theorem B487777 : Blo 381763 487777 := bbase (se 2 (by rfl) ⟨182916, by rfl⟩ : syracuseStep 487777 = 365833) (by norm_num)
theorem B487873 : Blo 381763 487873 := bbase (se 2 (by rfl) ⟨182952, by rfl⟩ : syracuseStep 487873 = 365905) (by norm_num)
theorem B1470997 : Blo 381763 1470997 := bbase (se 6 (by rfl) ⟨34476, by rfl⟩ : syracuseStep 1470997 = 68953) (by norm_num)
theorem B6582869 : Blo 381763 6582869 := bbase (se 8 (by rfl) ⟨38571, by rfl⟩ : syracuseStep 6582869 = 77143) (by norm_num)
theorem B815717 : Blo 381763 815717 := bbase (se 4 (by rfl) ⟨76473, by rfl⟩ : syracuseStep 815717 = 152947) (by norm_num)
theorem B1110629 : Blo 381763 1110629 := bbase (se 4 (by rfl) ⟨104121, by rfl⟩ : syracuseStep 1110629 = 208243) (by norm_num)
theorem B488045 : Blo 381763 488045 := bbase (se 3 (by rfl) ⟨91508, by rfl⟩ : syracuseStep 488045 = 183017) (by norm_num)
theorem B488101 : Blo 381763 488101 := bbase (se 4 (by rfl) ⟨45759, by rfl⟩ : syracuseStep 488101 = 91519) (by norm_num)
theorem B750277 : Blo 381763 750277 := bbase (se 4 (by rfl) ⟨70338, by rfl⟩ : syracuseStep 750277 = 140677) (by norm_num)
theorem B488197 : Blo 381763 488197 := bbase (se 4 (by rfl) ⟨45768, by rfl⟩ : syracuseStep 488197 = 91537) (by norm_num)
theorem B389917 : Blo 381763 389917 := bbase (se 3 (by rfl) ⟨73109, by rfl⟩ : syracuseStep 389917 = 146219) (by norm_num)
theorem B389953 : Blo 381763 389953 := bbase (se 2 (by rfl) ⟨146232, by rfl⟩ : syracuseStep 389953 = 292465) (by norm_num)
theorem B5665621 : Blo 381763 5665621 := bbase (se 9 (by rfl) ⟨16598, by rfl⟩ : syracuseStep 5665621 = 33197) (by norm_num)
theorem B684893 : Blo 381763 684893 := bbase (se 3 (by rfl) ⟨128417, by rfl⟩ : syracuseStep 684893 = 256835) (by norm_num)
theorem B816085 : Blo 381763 816085 := bbase (se 7 (by rfl) ⟨9563, by rfl⟩ : syracuseStep 816085 = 19127) (by norm_num)
theorem B390505 : Blo 381763 390505 := bbase (se 2 (by rfl) ⟨146439, by rfl⟩ : syracuseStep 390505 = 292879) (by norm_num)
theorem B390521 : Blo 381763 390521 := bbase (se 2 (by rfl) ⟨146445, by rfl⟩ : syracuseStep 390521 = 292891) (by norm_num)
theorem B1964101 : Blo 381763 1964101 := bbase (se 4 (by rfl) ⟨184134, by rfl⟩ : syracuseStep 1964101 = 368269) (by norm_num)
theorem B817589 : Blo 381763 817589 := bbase (se 5 (by rfl) ⟨38324, by rfl⟩ : syracuseStep 817589 = 76649) (by norm_num)
theorem B981445 : Blo 381763 981445 := bbase (se 4 (by rfl) ⟨92010, by rfl⟩ : syracuseStep 981445 = 184021) (by norm_num)
theorem B817733 : Blo 381763 817733 := bbase (se 4 (by rfl) ⟨76662, by rfl⟩ : syracuseStep 817733 = 153325) (by norm_num)
theorem B818093 : Blo 381763 818093 := bbase (se 3 (by rfl) ⟨153392, by rfl⟩ : syracuseStep 818093 = 306785) (by norm_num)
theorem B4390037 : Blo 381763 4390037 := bbase (se 6 (by rfl) ⟨102891, by rfl⟩ : syracuseStep 4390037 = 205783) (by norm_num)
theorem B1965269 : Blo 381763 1965269 := bbase (se 7 (by rfl) ⟨23030, by rfl⟩ : syracuseStep 1965269 = 46061) (by norm_num)
theorem B1637653 : Blo 381763 1637653 := bbase (se 6 (by rfl) ⟨38382, by rfl⟩ : syracuseStep 1637653 = 76765) (by norm_num)
theorem B392693 : Blo 381763 392693 := bbase (se 5 (by rfl) ⟨18407, by rfl⟩ : syracuseStep 392693 = 36815) (by norm_num)
theorem B1932821 : Blo 381763 1932821 := bbase (se 6 (by rfl) ⟨45300, by rfl⟩ : syracuseStep 1932821 = 90601) (by norm_num)
theorem B1638005 : Blo 381763 1638005 := bbase (se 5 (by rfl) ⟨76781, by rfl⟩ : syracuseStep 1638005 = 153563) (by norm_num)
theorem B818981 : Blo 381763 818981 := bbase (se 4 (by rfl) ⟨76779, by rfl⟩ : syracuseStep 818981 = 153559) (by norm_num)
theorem B491437 : Blo 381763 491437 := bbase (se 3 (by rfl) ⟨92144, by rfl⟩ : syracuseStep 491437 = 184289) (by norm_num)
theorem B655379 : Blo 381763 655379 := bstep (se 1 (by rfl) ⟨491534, by rfl⟩ : syracuseStep 655379 = 983069) B983069
theorem B983171 : Blo 381763 983171 := bstep (se 1 (by rfl) ⟨737378, by rfl⟩ : syracuseStep 983171 = 1474757) B1474757
theorem B1868017 : Blo 381763 1868017 := bstep (se 2 (by rfl) ⟨700506, by rfl⟩ : syracuseStep 1868017 = 1401013) B1401013
theorem B458995 : Blo 381763 458995 := bstep (se 1 (by rfl) ⟨344246, by rfl⟩ : syracuseStep 458995 = 688493) B688493
theorem B459091 : Blo 381763 459091 := bstep (se 1 (by rfl) ⟨344318, by rfl⟩ : syracuseStep 459091 = 688637) B688637
theorem B2195909 : Blo 381763 2195909 := bstep (se 4 (by rfl) ⟨205866, by rfl⟩ : syracuseStep 2195909 = 411733) B411733
theorem B1638883 : Blo 381763 1638883 := bstep (se 1 (by rfl) ⟨1229162, by rfl⟩ : syracuseStep 1638883 = 2458325) B2458325
theorem B2458097 : Blo 381763 2458097 := bstep (se 2 (by rfl) ⟨921786, by rfl⟩ : syracuseStep 2458097 = 1843573) B1843573
theorem B819715 : Blo 381763 819715 := bstep (se 1 (by rfl) ⟨614786, by rfl⟩ : syracuseStep 819715 = 1229573) B1229573
theorem B655939 : Blo 381763 655939 := bstep (se 1 (by rfl) ⟨491954, by rfl⟩ : syracuseStep 655939 = 983909) B983909
theorem B1475185 : Blo 381763 1475185 := bstep (se 2 (by rfl) ⟨553194, by rfl⟩ : syracuseStep 1475185 = 1106389) B1106389
theorem B459475 : Blo 381763 459475 := bstep (se 1 (by rfl) ⟨344606, by rfl⟩ : syracuseStep 459475 = 689213) B689213
theorem B3671153 : Blo 381763 3671153 := bstep (se 2 (by rfl) ⟨1376682, by rfl⟩ : syracuseStep 3671153 = 2753365) B2753365
theorem B1836209 : Blo 381763 1836209 := bstep (se 2 (by rfl) ⟨688578, by rfl⟩ : syracuseStep 1836209 = 1377157) B1377157
theorem B3737029 : Blo 381763 3737029 := bstep (se 4 (by rfl) ⟨350346, by rfl⟩ : syracuseStep 3737029 = 700693) B700693
theorem B1836557 : Blo 381763 1836557 := bstep (se 3 (by rfl) ⟨344354, by rfl⟩ : syracuseStep 1836557 = 688709) B688709
theorem B1312291 : Blo 381763 1312291 := bstep (se 1 (by rfl) ⟨984218, by rfl⟩ : syracuseStep 1312291 = 1968437) B1968437
theorem B820945 : Blo 381763 820945 := bstep (se 2 (by rfl) ⟨307854, by rfl⟩ : syracuseStep 820945 = 615709) B615709
theorem B1935089 : Blo 381763 1935089 := bstep (se 2 (by rfl) ⟨725658, by rfl⟩ : syracuseStep 1935089 = 1451317) B1451317
theorem B689905 : Blo 381763 689905 := bstep (se 2 (by rfl) ⟨258714, by rfl⟩ : syracuseStep 689905 = 517429) B517429
theorem B2459555 : Blo 381763 2459555 := bstep (se 1 (by rfl) ⟨1844666, by rfl⟩ : syracuseStep 2459555 = 3689333) B3689333
theorem B1312753 : Blo 381763 1312753 := bstep (se 2 (by rfl) ⟨492282, by rfl⟩ : syracuseStep 1312753 = 984565) B984565
theorem B526417 : Blo 381763 526417 := bstep (se 2 (by rfl) ⟨197406, by rfl⟩ : syracuseStep 526417 = 394813) B394813
theorem B4131125 : Blo 381763 4131125 := bstep (se 5 (by rfl) ⟨193646, by rfl⟩ : syracuseStep 4131125 = 387293) B387293
theorem B3279203 : Blo 381763 3279203 := bstep (se 1 (by rfl) ⟨2459402, by rfl⟩ : syracuseStep 3279203 = 4918805) B4918805
theorem B1641329 : Blo 381763 1641329 := bstep (se 2 (by rfl) ⟨615498, by rfl⟩ : syracuseStep 1641329 = 1230997) B1230997
theorem B2460557 : Blo 381763 2460557 := bstep (se 3 (by rfl) ⟨461354, by rfl⟩ : syracuseStep 2460557 = 922709) B922709
theorem B1313795 : Blo 381763 1313795 := bstep (se 1 (by rfl) ⟨985346, by rfl⟩ : syracuseStep 1313795 = 1970693) B1970693
theorem B1936547 : Blo 381763 1936547 := bstep (se 1 (by rfl) ⟨1452410, by rfl⟩ : syracuseStep 1936547 = 2904821) B2904821
theorem B822449 : Blo 381763 822449 := bstep (se 2 (by rfl) ⟨308418, by rfl⟩ : syracuseStep 822449 = 616837) B616837
theorem B822467 : Blo 381763 822467 := bstep (se 1 (by rfl) ⟨616850, by rfl⟩ : syracuseStep 822467 = 1233701) B1233701
theorem B3673613 : Blo 381763 3673613 := bstep (se 3 (by rfl) ⟨688802, by rfl⟩ : syracuseStep 3673613 = 1377605) B1377605
theorem B429619 : Blo 381763 429619 := bstep (se 1 (by rfl) ⟨322214, by rfl⟩ : syracuseStep 429619 = 644429) B644429
theorem B429763 : Blo 381763 429763 := bstep (se 1 (by rfl) ⟨322322, by rfl⟩ : syracuseStep 429763 = 644645) B644645
theorem B462547 : Blo 381763 462547 := bstep (se 1 (by rfl) ⟨346910, by rfl⟩ : syracuseStep 462547 = 693821) B693821
theorem B429907 : Blo 381763 429907 := bstep (se 1 (by rfl) ⟨322430, by rfl⟩ : syracuseStep 429907 = 644861) B644861
theorem B462739 : Blo 381763 462739 := bstep (se 1 (by rfl) ⟨347054, by rfl⟩ : syracuseStep 462739 = 694109) B694109
theorem B1937357 : Blo 381763 1937357 := bstep (se 3 (by rfl) ⟨363254, by rfl⟩ : syracuseStep 1937357 = 726509) B726509
theorem B724945 : Blo 381763 724945 := bstep (se 2 (by rfl) ⟨271854, by rfl⟩ : syracuseStep 724945 = 543709) B543709
theorem B790481 : Blo 381763 790481 := bstep (se 2 (by rfl) ⟨296430, by rfl⟩ : syracuseStep 790481 = 592861) B592861
theorem B430051 : Blo 381763 430051 := bstep (se 1 (by rfl) ⟨322538, by rfl⟩ : syracuseStep 430051 = 645077) B645077
theorem B725105 : Blo 381763 725105 := bstep (se 2 (by rfl) ⟨271914, by rfl⟩ : syracuseStep 725105 = 543829) B543829
theorem B430195 : Blo 381763 430195 := bstep (se 1 (by rfl) ⟨322646, by rfl⟩ : syracuseStep 430195 = 645293) B645293
theorem B2330765 : Blo 381763 2330765 := bstep (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) B874037
theorem B430339 : Blo 381763 430339 := bstep (se 1 (by rfl) ⟨322754, by rfl⟩ : syracuseStep 430339 = 645509) B645509
theorem B18583829 : Blo 381763 18583829 := bstep (se 6 (by rfl) ⟨435558, by rfl⟩ : syracuseStep 18583829 = 871117) B871117
theorem B856433 : Blo 381763 856433 := bstep (se 2 (by rfl) ⟨321162, by rfl⟩ : syracuseStep 856433 = 642325) B642325
theorem B430483 : Blo 381763 430483 := bstep (se 1 (by rfl) ⟨322862, by rfl⟩ : syracuseStep 430483 = 645725) B645725
theorem B725507 : Blo 381763 725507 := bstep (se 1 (by rfl) ⟨544130, by rfl⟩ : syracuseStep 725507 = 1088261) B1088261
theorem B430627 : Blo 381763 430627 := bstep (se 1 (by rfl) ⟨322970, by rfl⟩ : syracuseStep 430627 = 645941) B645941
theorem B430771 : Blo 381763 430771 := bstep (se 1 (by rfl) ⟨323078, by rfl⟩ : syracuseStep 430771 = 646157) B646157
theorem B430915 : Blo 381763 430915 := bstep (se 1 (by rfl) ⟨323186, by rfl⟩ : syracuseStep 430915 = 646373) B646373
theorem B431059 : Blo 381763 431059 := bstep (se 1 (by rfl) ⟨323294, by rfl⟩ : syracuseStep 431059 = 646589) B646589
theorem B431203 : Blo 381763 431203 := bstep (se 1 (by rfl) ⟨323402, by rfl⟩ : syracuseStep 431203 = 646805) B646805
theorem B2757773 : Blo 381763 2757773 := bstep (se 3 (by rfl) ⟨517082, by rfl⟩ : syracuseStep 2757773 = 1034165) B1034165
theorem B431347 : Blo 381763 431347 := bstep (se 1 (by rfl) ⟨323510, by rfl⟩ : syracuseStep 431347 = 647021) B647021
theorem B726403 : Blo 381763 726403 := bstep (se 1 (by rfl) ⟨544802, by rfl⟩ : syracuseStep 726403 = 1089605) B1089605
theorem B431491 : Blo 381763 431491 := bstep (se 1 (by rfl) ⟨323618, by rfl⟩ : syracuseStep 431491 = 647237) B647237
theorem B431635 : Blo 381763 431635 := bstep (se 1 (by rfl) ⟨323726, by rfl⟩ : syracuseStep 431635 = 647453) B647453
theorem B726563 : Blo 381763 726563 := bstep (se 1 (by rfl) ⟨544922, by rfl⟩ : syracuseStep 726563 = 1089845) B1089845
theorem B3937933 : Blo 381763 3937933 := bstep (se 3 (by rfl) ⟨738362, by rfl⟩ : syracuseStep 3937933 = 1476725) B1476725
theorem B431779 : Blo 381763 431779 := bstep (se 1 (by rfl) ⟨323834, by rfl⟩ : syracuseStep 431779 = 647669) B647669
theorem B431923 : Blo 381763 431923 := bstep (se 1 (by rfl) ⟨323942, by rfl⟩ : syracuseStep 431923 = 647885) B647885
theorem B432067 : Blo 381763 432067 := bstep (se 1 (by rfl) ⟨324050, by rfl⟩ : syracuseStep 432067 = 648101) B648101
theorem B3282929 : Blo 381763 3282929 := bstep (se 2 (by rfl) ⟨1231098, by rfl⟩ : syracuseStep 3282929 = 2462197) B2462197
theorem B923633 : Blo 381763 923633 := bstep (se 2 (by rfl) ⟨346362, by rfl⟩ : syracuseStep 923633 = 692725) B692725
theorem B432211 : Blo 381763 432211 := bstep (se 1 (by rfl) ⟨324158, by rfl⟩ : syracuseStep 432211 = 648317) B648317
theorem B2070755 : Blo 381763 2070755 := bstep (se 1 (by rfl) ⟨1553066, by rfl⟩ : syracuseStep 2070755 = 3106133) B3106133
theorem B432355 : Blo 381763 432355 := bstep (se 1 (by rfl) ⟨324266, by rfl⟩ : syracuseStep 432355 = 648533) B648533
theorem B432499 : Blo 381763 432499 := bstep (se 1 (by rfl) ⟨324374, by rfl⟩ : syracuseStep 432499 = 648749) B648749
theorem B432643 : Blo 381763 432643 := bstep (se 1 (by rfl) ⟨324482, by rfl⟩ : syracuseStep 432643 = 648965) B648965
theorem B1645069 : Blo 381763 1645069 := bstep (se 3 (by rfl) ⟨308450, by rfl⟩ : syracuseStep 1645069 = 616901) B616901
theorem B727633 : Blo 381763 727633 := bstep (se 2 (by rfl) ⟨272862, by rfl⟩ : syracuseStep 727633 = 545725) B545725
theorem B1088113 : Blo 381763 1088113 := bstep (se 2 (by rfl) ⟨408042, by rfl⟩ : syracuseStep 1088113 = 816085) B816085
theorem B432787 : Blo 381763 432787 := bstep (se 1 (by rfl) ⟨324590, by rfl⟩ : syracuseStep 432787 = 649181) B649181
theorem B432931 : Blo 381763 432931 := bstep (se 1 (by rfl) ⟨324698, by rfl⟩ : syracuseStep 432931 = 649397) B649397
theorem B1940273 : Blo 381763 1940273 := bstep (se 2 (by rfl) ⟨727602, by rfl⟩ : syracuseStep 1940273 = 1455205) B1455205
theorem B1088387 : Blo 381763 1088387 := bstep (se 1 (by rfl) ⟨816290, by rfl⟩ : syracuseStep 1088387 = 1632581) B1632581
theorem B433075 : Blo 381763 433075 := bstep (se 1 (by rfl) ⟨324806, by rfl⟩ : syracuseStep 433075 = 649613) B649613
theorem B859121 : Blo 381763 859121 := bstep (se 2 (by rfl) ⟨322170, by rfl⟩ : syracuseStep 859121 = 644341) B644341
theorem B859139 : Blo 381763 859139 := bstep (se 1 (by rfl) ⟨644354, by rfl⟩ : syracuseStep 859139 = 1288709) B1288709
theorem B1088579 : Blo 381763 1088579 := bstep (se 1 (by rfl) ⟨816434, by rfl⟩ : syracuseStep 1088579 = 1632869) B1632869
theorem B433219 : Blo 381763 433219 := bstep (se 1 (by rfl) ⟨324914, by rfl⟩ : syracuseStep 433219 = 649829) B649829
theorem B4168901 : Blo 381763 4168901 := bstep (se 4 (by rfl) ⟨390834, by rfl⟩ : syracuseStep 4168901 = 781669) B781669
theorem B433363 : Blo 381763 433363 := bstep (se 1 (by rfl) ⟨325022, by rfl⟩ : syracuseStep 433363 = 650045) B650045
theorem B859409 : Blo 381763 859409 := bstep (se 2 (by rfl) ⟨322278, by rfl⟩ : syracuseStep 859409 = 644557) B644557
theorem B859427 : Blo 381763 859427 := bstep (se 1 (by rfl) ⟨644570, by rfl⟩ : syracuseStep 859427 = 1289141) B1289141
theorem B433507 : Blo 381763 433507 := bstep (se 1 (by rfl) ⟨325130, by rfl⟩ : syracuseStep 433507 = 650261) B650261
theorem B1744355 : Blo 381763 1744355 := bstep (se 1 (by rfl) ⟨1308266, by rfl⟩ : syracuseStep 1744355 = 2616533) B2616533
theorem B433651 : Blo 381763 433651 := bstep (se 1 (by rfl) ⟨325238, by rfl⟩ : syracuseStep 433651 = 650477) B650477
theorem B859697 : Blo 381763 859697 := bstep (se 2 (by rfl) ⟨322386, by rfl⟩ : syracuseStep 859697 = 644773) B644773
theorem B859715 : Blo 381763 859715 := bstep (se 1 (by rfl) ⟨644786, by rfl⟩ : syracuseStep 859715 = 1289573) B1289573
theorem B3513955 : Blo 381763 3513955 := bstep (se 1 (by rfl) ⟨2635466, by rfl⟩ : syracuseStep 3513955 = 5270933) B5270933
theorem B728689 : Blo 381763 728689 := bstep (se 2 (by rfl) ⟨273258, by rfl⟩ : syracuseStep 728689 = 546517) B546517
theorem B433795 : Blo 381763 433795 := bstep (se 1 (by rfl) ⟨325346, by rfl⟩ : syracuseStep 433795 = 650693) B650693
theorem B1449677 : Blo 381763 1449677 := bstep (se 3 (by rfl) ⟨271814, by rfl⟩ : syracuseStep 1449677 = 543629) B543629
theorem B433939 : Blo 381763 433939 := bstep (se 1 (by rfl) ⟨325454, by rfl⟩ : syracuseStep 433939 = 650909) B650909
theorem B859985 : Blo 381763 859985 := bstep (se 2 (by rfl) ⟨322494, by rfl⟩ : syracuseStep 859985 = 644989) B644989
theorem B860003 : Blo 381763 860003 := bstep (se 1 (by rfl) ⟨645002, by rfl⟩ : syracuseStep 860003 = 1290005) B1290005
theorem B1089389 : Blo 381763 1089389 := bstep (se 3 (by rfl) ⟨204260, by rfl⟩ : syracuseStep 1089389 = 408521) B408521
theorem B1974221 : Blo 381763 1974221 := bstep (se 3 (by rfl) ⟨370166, by rfl⟩ : syracuseStep 1974221 = 740333) B740333
theorem B729091 : Blo 381763 729091 := bstep (se 1 (by rfl) ⟨546818, by rfl⟩ : syracuseStep 729091 = 1093637) B1093637
theorem B1089571 : Blo 381763 1089571 := bstep (se 1 (by rfl) ⟨817178, by rfl⟩ : syracuseStep 1089571 = 1634357) B1634357
theorem B729137 : Blo 381763 729137 := bstep (se 2 (by rfl) ⟨273426, by rfl⟩ : syracuseStep 729137 = 546853) B546853
theorem B860273 : Blo 381763 860273 := bstep (se 2 (by rfl) ⟨322602, by rfl⟩ : syracuseStep 860273 = 645205) B645205
theorem B860291 : Blo 381763 860291 := bstep (se 1 (by rfl) ⟨645218, by rfl⟩ : syracuseStep 860291 = 1290437) B1290437
theorem B1941731 : Blo 381763 1941731 := bstep (se 1 (by rfl) ⟨1456298, by rfl⟩ : syracuseStep 1941731 = 2912597) B2912597
theorem B4661489 : Blo 381763 4661489 := bstep (se 2 (by rfl) ⟨1748058, by rfl⟩ : syracuseStep 4661489 = 3496117) B3496117
theorem B1777997 : Blo 381763 1777997 := bstep (se 3 (by rfl) ⟨333374, by rfl⟩ : syracuseStep 1777997 = 666749) B666749
theorem B729425 : Blo 381763 729425 := bstep (se 2 (by rfl) ⟨273534, by rfl⟩ : syracuseStep 729425 = 547069) B547069
theorem B860561 : Blo 381763 860561 := bstep (se 2 (by rfl) ⟨322710, by rfl⟩ : syracuseStep 860561 = 645421) B645421
theorem B860579 : Blo 381763 860579 := bstep (se 1 (by rfl) ⟨645434, by rfl⟩ : syracuseStep 860579 = 1290869) B1290869
theorem B1122797 : Blo 381763 1122797 := bstep (se 3 (by rfl) ⟨210524, by rfl⟩ : syracuseStep 1122797 = 421049) B421049
theorem B1090061 : Blo 381763 1090061 := bstep (se 3 (by rfl) ⟨204386, by rfl⟩ : syracuseStep 1090061 = 408773) B408773
theorem B926275 : Blo 381763 926275 := bstep (se 1 (by rfl) ⟨694706, by rfl⟩ : syracuseStep 926275 = 1389413) B1389413
theorem B1122893 : Blo 381763 1122893 := bstep (se 3 (by rfl) ⟨210542, by rfl⟩ : syracuseStep 1122893 = 421085) B421085
theorem B1385059 : Blo 381763 1385059 := bstep (se 1 (by rfl) ⟨1038794, by rfl⟩ : syracuseStep 1385059 = 2077589) B2077589
theorem B1319597 : Blo 381763 1319597 := bstep (se 3 (by rfl) ⟨247424, by rfl⟩ : syracuseStep 1319597 = 494849) B494849
theorem B860849 : Blo 381763 860849 := bstep (se 2 (by rfl) ⟨322818, by rfl⟩ : syracuseStep 860849 = 645637) B645637
theorem B860867 : Blo 381763 860867 := bstep (se 1 (by rfl) ⟨645650, by rfl⟩ : syracuseStep 860867 = 1291301) B1291301
theorem B861137 : Blo 381763 861137 := bstep (se 2 (by rfl) ⟨322926, by rfl⟩ : syracuseStep 861137 = 645853) B645853
theorem B861155 : Blo 381763 861155 := bstep (se 1 (by rfl) ⟨645866, by rfl⟩ : syracuseStep 861155 = 1291733) B1291733
theorem B1942541 : Blo 381763 1942541 := bstep (se 3 (by rfl) ⟨364226, by rfl⟩ : syracuseStep 1942541 = 728453) B728453
theorem B730147 : Blo 381763 730147 := bstep (se 1 (by rfl) ⟨547610, by rfl⟩ : syracuseStep 730147 = 1095221) B1095221
theorem B861425 : Blo 381763 861425 := bstep (se 2 (by rfl) ⟨323034, by rfl⟩ : syracuseStep 861425 = 646069) B646069
theorem B861443 : Blo 381763 861443 := bstep (se 1 (by rfl) ⟨646082, by rfl⟩ : syracuseStep 861443 = 1292165) B1292165
theorem B730595 : Blo 381763 730595 := bstep (se 1 (by rfl) ⟨547946, by rfl⟩ : syracuseStep 730595 = 1095893) B1095893
theorem B2991629 : Blo 381763 2991629 := bstep (se 3 (by rfl) ⟨560930, by rfl⟩ : syracuseStep 2991629 = 1121861) B1121861
theorem B861713 : Blo 381763 861713 := bstep (se 2 (by rfl) ⟨323142, by rfl⟩ : syracuseStep 861713 = 646285) B646285
theorem B861731 : Blo 381763 861731 := bstep (se 1 (by rfl) ⟨646298, by rfl⟩ : syracuseStep 861731 = 1292597) B1292597
theorem B2631203 : Blo 381763 2631203 := bstep (se 1 (by rfl) ⟨1973402, by rfl⟩ : syracuseStep 2631203 = 3946805) B3946805
theorem B4368013 : Blo 381763 4368013 := bstep (se 3 (by rfl) ⟨819002, by rfl⟩ : syracuseStep 4368013 = 1638005) B1638005
theorem B1091245 : Blo 381763 1091245 := bstep (se 3 (by rfl) ⟨204608, by rfl⟩ : syracuseStep 1091245 = 409217) B409217
theorem B730883 : Blo 381763 730883 := bstep (se 1 (by rfl) ⟨548162, by rfl⟩ : syracuseStep 730883 = 1096325) B1096325
theorem B1451789 : Blo 381763 1451789 := bstep (se 3 (by rfl) ⟨272210, by rfl⟩ : syracuseStep 1451789 = 544421) B544421
theorem B862001 : Blo 381763 862001 := bstep (se 2 (by rfl) ⟨323250, by rfl⟩ : syracuseStep 862001 = 646501) B646501
theorem B862019 : Blo 381763 862019 := bstep (se 1 (by rfl) ⟨646514, by rfl⟩ : syracuseStep 862019 = 1293029) B1293029
theorem B3286925 : Blo 381763 3286925 := bstep (se 3 (by rfl) ⟨616298, by rfl⟩ : syracuseStep 3286925 = 1232597) B1232597
theorem B862289 : Blo 381763 862289 := bstep (se 2 (by rfl) ⟨323358, by rfl⟩ : syracuseStep 862289 = 646717) B646717
theorem B862307 : Blo 381763 862307 := bstep (se 1 (by rfl) ⟨646730, by rfl⟩ : syracuseStep 862307 = 1293461) B1293461
theorem B2926691 : Blo 381763 2926691 := bstep (se 1 (by rfl) ⟨2195018, by rfl⟩ : syracuseStep 2926691 = 4390037) B4390037
theorem B1288493 : Blo 381763 1288493 := bstep (se 3 (by rfl) ⟨241592, by rfl⟩ : syracuseStep 1288493 = 483185) B483185
theorem B1288547 : Blo 381763 1288547 := bstep (se 1 (by rfl) ⟨966410, by rfl⟩ : syracuseStep 1288547 = 1932821) B1932821
theorem B862577 : Blo 381763 862577 := bstep (se 2 (by rfl) ⟨323466, by rfl⟩ : syracuseStep 862577 = 646933) B646933
theorem B862595 : Blo 381763 862595 := bstep (se 1 (by rfl) ⟨646946, by rfl⟩ : syracuseStep 862595 = 1293893) B1293893
theorem B1452593 : Blo 381763 1452593 := bstep (se 2 (by rfl) ⟨544722, by rfl⟩ : syracuseStep 1452593 = 1089445) B1089445
theorem B1288817 : Blo 381763 1288817 := bstep (se 2 (by rfl) ⟨483306, by rfl⟩ : syracuseStep 1288817 = 966613) B966613
theorem B3943025 : Blo 381763 3943025 := bstep (se 2 (by rfl) ⟨1478634, by rfl⟩ : syracuseStep 3943025 = 2957269) B2957269
theorem B862865 : Blo 381763 862865 := bstep (se 2 (by rfl) ⟨323574, by rfl⟩ : syracuseStep 862865 = 647149) B647149
theorem B862883 : Blo 381763 862883 := bstep (se 1 (by rfl) ⟨647162, by rfl⟩ : syracuseStep 862883 = 1294325) B1294325
theorem B731825 : Blo 381763 731825 := bstep (se 2 (by rfl) ⟨274434, by rfl⟩ : syracuseStep 731825 = 548869) B548869
theorem B1092305 : Blo 381763 1092305 := bstep (se 2 (by rfl) ⟨409614, by rfl⟩ : syracuseStep 1092305 = 819229) B819229
theorem B863153 : Blo 381763 863153 := bstep (se 2 (by rfl) ⟨323682, by rfl⟩ : syracuseStep 863153 = 647365) B647365
theorem B863171 : Blo 381763 863171 := bstep (se 1 (by rfl) ⟨647378, by rfl⟩ : syracuseStep 863171 = 1294757) B1294757
theorem B2075597 : Blo 381763 2075597 := bstep (se 3 (by rfl) ⟨389174, by rfl⟩ : syracuseStep 2075597 = 778349) B778349
theorem B1289357 : Blo 381763 1289357 := bstep (se 3 (by rfl) ⟨241754, by rfl⟩ : syracuseStep 1289357 = 483509) B483509
theorem B2469041 : Blo 381763 2469041 := bstep (se 2 (by rfl) ⟨925890, by rfl⟩ : syracuseStep 2469041 = 1851781) B1851781
theorem B1289411 : Blo 381763 1289411 := bstep (se 1 (by rfl) ⟨967058, by rfl⟩ : syracuseStep 1289411 = 1934117) B1934117
theorem B1453261 : Blo 381763 1453261 := bstep (se 3 (by rfl) ⟨272486, by rfl⟩ : syracuseStep 1453261 = 544973) B544973
theorem B863441 : Blo 381763 863441 := bstep (se 2 (by rfl) ⟨323790, by rfl⟩ : syracuseStep 863441 = 647581) B647581
theorem B2764003 : Blo 381763 2764003 := bstep (se 1 (by rfl) ⟨2073002, by rfl⟩ : syracuseStep 2764003 = 4146005) B4146005
theorem B863459 : Blo 381763 863459 := bstep (se 1 (by rfl) ⟨647594, by rfl⟩ : syracuseStep 863459 = 1295189) B1295189
theorem B1092977 : Blo 381763 1092977 := bstep (se 2 (by rfl) ⟨409866, by rfl⟩ : syracuseStep 1092977 = 819733) B819733
theorem B1289681 : Blo 381763 1289681 := bstep (se 2 (by rfl) ⟨483630, by rfl⟩ : syracuseStep 1289681 = 967261) B967261
theorem B863729 : Blo 381763 863729 := bstep (se 2 (by rfl) ⟨323898, by rfl⟩ : syracuseStep 863729 = 647797) B647797
theorem B863747 : Blo 381763 863747 := bstep (se 1 (by rfl) ⟨647810, by rfl⟩ : syracuseStep 863747 = 1295621) B1295621
theorem B864017 : Blo 381763 864017 := bstep (se 2 (by rfl) ⟨324006, by rfl⟩ : syracuseStep 864017 = 648013) B648013
theorem B864035 : Blo 381763 864035 := bstep (se 1 (by rfl) ⟨648026, by rfl⟩ : syracuseStep 864035 = 1296053) B1296053
theorem B2174789 : Blo 381763 2174789 := bstep (se 4 (by rfl) ⟨203886, by rfl⟩ : syracuseStep 2174789 = 407773) B407773
theorem B1945457 : Blo 381763 1945457 := bstep (se 2 (by rfl) ⟨729546, by rfl⟩ : syracuseStep 1945457 = 1459093) B1459093
theorem B2338723 : Blo 381763 2338723 := bstep (se 1 (by rfl) ⟨1754042, by rfl⟩ : syracuseStep 2338723 = 3508085) B3508085
theorem B1454051 : Blo 381763 1454051 := bstep (se 1 (by rfl) ⟨1090538, by rfl⟩ : syracuseStep 1454051 = 2181077) B2181077
theorem B1290221 : Blo 381763 1290221 := bstep (se 3 (by rfl) ⟨241916, by rfl⟩ : syracuseStep 1290221 = 483833) B483833
theorem B1847281 : Blo 381763 1847281 := bstep (se 2 (by rfl) ⟨692730, by rfl⟩ : syracuseStep 1847281 = 1385461) B1385461
theorem B1290275 : Blo 381763 1290275 := bstep (se 1 (by rfl) ⟨967706, by rfl⟩ : syracuseStep 1290275 = 1935413) B1935413
theorem B864305 : Blo 381763 864305 := bstep (se 2 (by rfl) ⟨324114, by rfl⟩ : syracuseStep 864305 = 648229) B648229
theorem B864323 : Blo 381763 864323 := bstep (se 1 (by rfl) ⟨648242, by rfl⟩ : syracuseStep 864323 = 1296485) B1296485
theorem B3584099 : Blo 381763 3584099 := bstep (se 1 (by rfl) ⟨2688074, by rfl⟩ : syracuseStep 3584099 = 5376149) B5376149
theorem B1093763 : Blo 381763 1093763 := bstep (se 1 (by rfl) ⟨820322, by rfl⟩ : syracuseStep 1093763 = 1640645) B1640645
theorem B1552547 : Blo 381763 1552547 := bstep (se 1 (by rfl) ⟨1164410, by rfl⟩ : syracuseStep 1552547 = 2328821) B2328821
theorem B2470115 : Blo 381763 2470115 := bstep (se 1 (by rfl) ⟨1852586, by rfl⟩ : syracuseStep 2470115 = 3705173) B3705173
theorem B2175245 : Blo 381763 2175245 := bstep (se 3 (by rfl) ⟨407858, by rfl⟩ : syracuseStep 2175245 = 815717) B815717
theorem B2961677 : Blo 381763 2961677 := bstep (se 3 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 2961677 = 1110629) B1110629
theorem B1290545 : Blo 381763 1290545 := bstep (se 2 (by rfl) ⟨483954, by rfl⟩ : syracuseStep 1290545 = 967909) B967909
theorem B864593 : Blo 381763 864593 := bstep (se 2 (by rfl) ⟨324222, by rfl⟩ : syracuseStep 864593 = 648445) B648445
theorem B864611 : Blo 381763 864611 := bstep (se 1 (by rfl) ⟨648458, by rfl⟩ : syracuseStep 864611 = 1296917) B1296917
theorem B1225165 : Blo 381763 1225165 := bstep (se 3 (by rfl) ⟨229718, by rfl⟩ : syracuseStep 1225165 = 459437) B459437
theorem B1094093 : Blo 381763 1094093 := bstep (se 3 (by rfl) ⟨205142, by rfl⟩ : syracuseStep 1094093 = 410285) B410285
theorem B700913 : Blo 381763 700913 := bstep (se 2 (by rfl) ⟨262842, by rfl⟩ : syracuseStep 700913 = 525685) B525685
theorem B1094161 : Blo 381763 1094161 := bstep (se 2 (by rfl) ⟨410310, by rfl⟩ : syracuseStep 1094161 = 820621) B820621
theorem B1454705 : Blo 381763 1454705 := bstep (se 2 (by rfl) ⟨545514, by rfl⟩ : syracuseStep 1454705 = 1091029) B1091029
theorem B864881 : Blo 381763 864881 := bstep (se 2 (by rfl) ⟨324330, by rfl⟩ : syracuseStep 864881 = 648661) B648661
theorem B864899 : Blo 381763 864899 := bstep (se 1 (by rfl) ⟨648674, by rfl⟩ : syracuseStep 864899 = 1297349) B1297349
theorem B7385741 : Blo 381763 7385741 := bstep (se 3 (by rfl) ⟨1384826, by rfl⟩ : syracuseStep 7385741 = 2769653) B2769653
theorem B1094435 : Blo 381763 1094435 := bstep (se 1 (by rfl) ⟨820826, by rfl⟩ : syracuseStep 1094435 = 1641653) B1641653
theorem B1291085 : Blo 381763 1291085 := bstep (se 3 (by rfl) ⟨242078, by rfl⟩ : syracuseStep 1291085 = 484157) B484157
theorem B1291139 : Blo 381763 1291139 := bstep (se 1 (by rfl) ⟨968354, by rfl⟩ : syracuseStep 1291139 = 1936709) B1936709
theorem B865169 : Blo 381763 865169 := bstep (se 2 (by rfl) ⟨324438, by rfl⟩ : syracuseStep 865169 = 648877) B648877
theorem B865187 : Blo 381763 865187 := bstep (se 1 (by rfl) ⟨648890, by rfl⟩ : syracuseStep 865187 = 1297781) B1297781
theorem B439427 : Blo 381763 439427 := bstep (se 1 (by rfl) ⟨329570, by rfl⟩ : syracuseStep 439427 = 659141) B659141
theorem B1291409 : Blo 381763 1291409 := bstep (se 2 (by rfl) ⟨484278, by rfl⟩ : syracuseStep 1291409 = 968557) B968557
theorem B865457 : Blo 381763 865457 := bstep (se 2 (by rfl) ⟨324546, by rfl⟩ : syracuseStep 865457 = 649093) B649093
theorem B865475 : Blo 381763 865475 := bstep (se 1 (by rfl) ⟨649106, by rfl⟩ : syracuseStep 865475 = 1298213) B1298213
theorem B1946915 : Blo 381763 1946915 := bstep (se 1 (by rfl) ⟨1460186, by rfl⟩ : syracuseStep 1946915 = 2920373) B2920373
theorem B4666693 : Blo 381763 4666693 := bstep (se 4 (by rfl) ⟨437502, by rfl⟩ : syracuseStep 4666693 = 875005) B875005
theorem B865745 : Blo 381763 865745 := bstep (se 2 (by rfl) ⟨324654, by rfl⟩ : syracuseStep 865745 = 649309) B649309
theorem B865763 : Blo 381763 865763 := bstep (se 1 (by rfl) ⟨649322, by rfl⟩ : syracuseStep 865763 = 1298645) B1298645
theorem B1095277 : Blo 381763 1095277 := bstep (se 3 (by rfl) ⟨205364, by rfl⟩ : syracuseStep 1095277 = 410729) B410729
theorem B1291949 : Blo 381763 1291949 := bstep (se 3 (by rfl) ⟨242240, by rfl⟩ : syracuseStep 1291949 = 484481) B484481
theorem B1292003 : Blo 381763 1292003 := bstep (se 1 (by rfl) ⟨969002, by rfl⟩ : syracuseStep 1292003 = 1938005) B1938005
theorem B866033 : Blo 381763 866033 := bstep (se 2 (by rfl) ⟨324762, by rfl⟩ : syracuseStep 866033 = 649525) B649525
theorem B866051 : Blo 381763 866051 := bstep (se 1 (by rfl) ⟨649538, by rfl⟩ : syracuseStep 866051 = 1299077) B1299077
theorem B1095437 : Blo 381763 1095437 := bstep (se 3 (by rfl) ⟨205394, by rfl⟩ : syracuseStep 1095437 = 410789) B410789
theorem B1226627 : Blo 381763 1226627 := bstep (se 1 (by rfl) ⟨919970, by rfl⟩ : syracuseStep 1226627 = 1839941) B1839941
theorem B1161101 : Blo 381763 1161101 := bstep (se 3 (by rfl) ⟨217706, by rfl⟩ : syracuseStep 1161101 = 435413) B435413
theorem B1095619 : Blo 381763 1095619 := bstep (se 1 (by rfl) ⟨821714, by rfl⟩ : syracuseStep 1095619 = 1643429) B1643429
theorem B1292273 : Blo 381763 1292273 := bstep (se 2 (by rfl) ⟨484602, by rfl⟩ : syracuseStep 1292273 = 969205) B969205
theorem B866321 : Blo 381763 866321 := bstep (se 2 (by rfl) ⟨324870, by rfl⟩ : syracuseStep 866321 = 649741) B649741
theorem B1456163 : Blo 381763 1456163 := bstep (se 1 (by rfl) ⟨1092122, by rfl⟩ : syracuseStep 1456163 = 2184245) B2184245
theorem B866339 : Blo 381763 866339 := bstep (se 1 (by rfl) ⟨649754, by rfl⟩ : syracuseStep 866339 = 1299509) B1299509
theorem B1456177 : Blo 381763 1456177 := bstep (se 2 (by rfl) ⟨546066, by rfl⟩ : syracuseStep 1456177 = 1092133) B1092133
theorem B2504753 : Blo 381763 2504753 := bstep (se 2 (by rfl) ⟨939282, by rfl⟩ : syracuseStep 2504753 = 1878565) B1878565
theorem B1947725 : Blo 381763 1947725 := bstep (se 3 (by rfl) ⟨365198, by rfl⟩ : syracuseStep 1947725 = 730397) B730397
theorem B1226897 : Blo 381763 1226897 := bstep (se 2 (by rfl) ⟨460086, by rfl⟩ : syracuseStep 1226897 = 920173) B920173
theorem B866609 : Blo 381763 866609 := bstep (se 2 (by rfl) ⟨324978, by rfl⟩ : syracuseStep 866609 = 649957) B649957
theorem B866627 : Blo 381763 866627 := bstep (se 1 (by rfl) ⟨649970, by rfl⟩ : syracuseStep 866627 = 1299941) B1299941
theorem B1292813 : Blo 381763 1292813 := bstep (se 3 (by rfl) ⟨242402, by rfl⟩ : syracuseStep 1292813 = 484805) B484805
theorem B1161773 : Blo 381763 1161773 := bstep (se 3 (by rfl) ⟨217832, by rfl⟩ : syracuseStep 1161773 = 435665) B435665
theorem B408115 : Blo 381763 408115 := bstep (se 1 (by rfl) ⟨306086, by rfl⟩ : syracuseStep 408115 = 612173) B612173
theorem B1292867 : Blo 381763 1292867 := bstep (se 1 (by rfl) ⟨969650, by rfl⟩ : syracuseStep 1292867 = 1939301) B1939301
theorem B866897 : Blo 381763 866897 := bstep (se 2 (by rfl) ⟨325086, by rfl⟩ : syracuseStep 866897 = 650173) B650173
theorem B866915 : Blo 381763 866915 := bstep (se 1 (by rfl) ⟨650186, by rfl⟩ : syracuseStep 866915 = 1300373) B1300373
theorem B13318769 : Blo 381763 13318769 := bstep (se 2 (by rfl) ⟨4994538, by rfl⟩ : syracuseStep 13318769 = 9989077) B9989077
theorem B4668101 : Blo 381763 4668101 := bstep (se 4 (by rfl) ⟨437634, by rfl⟩ : syracuseStep 4668101 = 875269) B875269
theorem B2079557 : Blo 381763 2079557 := bstep (se 4 (by rfl) ⟨194958, by rfl⟩ : syracuseStep 2079557 = 389917) B389917
theorem B1293137 : Blo 381763 1293137 := bstep (se 2 (by rfl) ⟨484926, by rfl⟩ : syracuseStep 1293137 = 969853) B969853
theorem B867185 : Blo 381763 867185 := bstep (se 2 (by rfl) ⟨325194, by rfl⟩ : syracuseStep 867185 = 650389) B650389
theorem B867203 : Blo 381763 867203 := bstep (se 1 (by rfl) ⟨650402, by rfl⟩ : syracuseStep 867203 = 1300805) B1300805
theorem B1850339 : Blo 381763 1850339 := bstep (se 1 (by rfl) ⟨1387754, by rfl⟩ : syracuseStep 1850339 = 2775509) B2775509
theorem B2079749 : Blo 381763 2079749 := bstep (se 4 (by rfl) ⟨194976, by rfl⟩ : syracuseStep 2079749 = 389953) B389953
theorem B2178161 : Blo 381763 2178161 := bstep (se 2 (by rfl) ⟨816810, by rfl⟩ : syracuseStep 2178161 = 1633621) B1633621
theorem B867473 : Blo 381763 867473 := bstep (se 2 (by rfl) ⟨325302, by rfl⟩ : syracuseStep 867473 = 650605) B650605
theorem B867491 : Blo 381763 867491 := bstep (se 1 (by rfl) ⟨650618, by rfl⟩ : syracuseStep 867491 = 1301237) B1301237
theorem B572657 : Blo 381763 572657 := bstep (se 2 (by rfl) ⟨214746, by rfl⟩ : syracuseStep 572657 = 429493) B429493
theorem B572675 : Blo 381763 572675 := bstep (se 1 (by rfl) ⟨429506, by rfl⟩ : syracuseStep 572675 = 859013) B859013
theorem B572705 : Blo 381763 572705 := bstep (se 2 (by rfl) ⟨214764, by rfl⟩ : syracuseStep 572705 = 429529) B429529
theorem B998705 : Blo 381763 998705 := bstep (se 2 (by rfl) ⟨374514, by rfl⟩ : syracuseStep 998705 = 749029) B749029
theorem B1097009 : Blo 381763 1097009 := bstep (se 2 (by rfl) ⟨411378, by rfl⟩ : syracuseStep 1097009 = 822757) B822757
theorem B572723 : Blo 381763 572723 := bstep (se 1 (by rfl) ⟨429542, by rfl⟩ : syracuseStep 572723 = 859085) B859085
theorem B572753 : Blo 381763 572753 := bstep (se 2 (by rfl) ⟨214782, by rfl⟩ : syracuseStep 572753 = 429565) B429565
theorem B572771 : Blo 381763 572771 := bstep (se 1 (by rfl) ⟨429578, by rfl⟩ : syracuseStep 572771 = 859157) B859157
theorem B1293677 : Blo 381763 1293677 := bstep (se 3 (by rfl) ⟨242564, by rfl⟩ : syracuseStep 1293677 = 485129) B485129
theorem B572801 : Blo 381763 572801 := bstep (se 2 (by rfl) ⟨214800, by rfl⟩ : syracuseStep 572801 = 429601) B429601
theorem B572819 : Blo 381763 572819 := bstep (se 1 (by rfl) ⟨429614, by rfl⟩ : syracuseStep 572819 = 859229) B859229
theorem B1293731 : Blo 381763 1293731 := bstep (se 1 (by rfl) ⟨970298, by rfl⟩ : syracuseStep 1293731 = 1940597) B1940597
theorem B572849 : Blo 381763 572849 := bstep (se 2 (by rfl) ⟨214818, by rfl⟩ : syracuseStep 572849 = 429637) B429637
theorem B867761 : Blo 381763 867761 := bstep (se 2 (by rfl) ⟨325410, by rfl⟩ : syracuseStep 867761 = 650821) B650821
theorem B572867 : Blo 381763 572867 := bstep (se 1 (by rfl) ⟨429650, by rfl⟩ : syracuseStep 572867 = 859301) B859301
theorem B867779 : Blo 381763 867779 := bstep (se 1 (by rfl) ⟨650834, by rfl⟩ : syracuseStep 867779 = 1301669) B1301669
theorem B572897 : Blo 381763 572897 := bstep (se 2 (by rfl) ⟨214836, by rfl⟩ : syracuseStep 572897 = 429673) B429673
theorem B1457635 : Blo 381763 1457635 := bstep (se 1 (by rfl) ⟨1093226, by rfl⟩ : syracuseStep 1457635 = 2186453) B2186453
theorem B572915 : Blo 381763 572915 := bstep (se 1 (by rfl) ⟨429686, by rfl⟩ : syracuseStep 572915 = 859373) B859373
theorem B572945 : Blo 381763 572945 := bstep (se 2 (by rfl) ⟨214854, by rfl⟩ : syracuseStep 572945 = 429709) B429709
theorem B572963 : Blo 381763 572963 := bstep (se 1 (by rfl) ⟨429722, by rfl⟩ : syracuseStep 572963 = 859445) B859445
theorem B572993 : Blo 381763 572993 := bstep (se 2 (by rfl) ⟨214872, by rfl⟩ : syracuseStep 572993 = 429745) B429745
theorem B573011 : Blo 381763 573011 := bstep (se 1 (by rfl) ⟨429758, by rfl⟩ : syracuseStep 573011 = 859517) B859517
theorem B573041 : Blo 381763 573041 := bstep (se 2 (by rfl) ⟨214890, by rfl⟩ : syracuseStep 573041 = 429781) B429781
theorem B573059 : Blo 381763 573059 := bstep (se 1 (by rfl) ⟨429794, by rfl⟩ : syracuseStep 573059 = 859589) B859589
theorem B573089 : Blo 381763 573089 := bstep (se 2 (by rfl) ⟨214908, by rfl⟩ : syracuseStep 573089 = 429817) B429817
theorem B1294001 : Blo 381763 1294001 := bstep (se 2 (by rfl) ⟨485250, by rfl⟩ : syracuseStep 1294001 = 970501) B970501
theorem B573107 : Blo 381763 573107 := bstep (se 1 (by rfl) ⟨429830, by rfl⟩ : syracuseStep 573107 = 859661) B859661
theorem B2211533 : Blo 381763 2211533 := bstep (se 3 (by rfl) ⟨414662, by rfl⟩ : syracuseStep 2211533 = 829325) B829325
theorem B573137 : Blo 381763 573137 := bstep (se 2 (by rfl) ⟨214926, by rfl⟩ : syracuseStep 573137 = 429853) B429853
theorem B573155 : Blo 381763 573155 := bstep (se 1 (by rfl) ⟨429866, by rfl⟩ : syracuseStep 573155 = 859733) B859733
theorem B573185 : Blo 381763 573185 := bstep (se 2 (by rfl) ⟨214944, by rfl⟩ : syracuseStep 573185 = 429889) B429889
theorem B573203 : Blo 381763 573203 := bstep (se 1 (by rfl) ⟨429902, by rfl⟩ : syracuseStep 573203 = 859805) B859805
theorem B409379 : Blo 381763 409379 := bstep (se 1 (by rfl) ⟨307034, by rfl⟩ : syracuseStep 409379 = 614069) B614069
theorem B573233 : Blo 381763 573233 := bstep (se 2 (by rfl) ⟨214962, by rfl⟩ : syracuseStep 573233 = 429925) B429925
theorem B573251 : Blo 381763 573251 := bstep (se 1 (by rfl) ⟨429938, by rfl⟩ : syracuseStep 573251 = 859877) B859877
theorem B573281 : Blo 381763 573281 := bstep (se 2 (by rfl) ⟨214980, by rfl⟩ : syracuseStep 573281 = 429961) B429961
theorem B573299 : Blo 381763 573299 := bstep (se 1 (by rfl) ⟨429974, by rfl⟩ : syracuseStep 573299 = 859949) B859949
theorem B573329 : Blo 381763 573329 := bstep (se 2 (by rfl) ⟨214998, by rfl⟩ : syracuseStep 573329 = 429997) B429997
theorem B966563 : Blo 381763 966563 := bstep (se 1 (by rfl) ⟨724922, by rfl⟩ : syracuseStep 966563 = 1449845) B1449845
theorem B573347 : Blo 381763 573347 := bstep (se 1 (by rfl) ⟨430010, by rfl⟩ : syracuseStep 573347 = 860021) B860021
theorem B573377 : Blo 381763 573377 := bstep (se 2 (by rfl) ⟨215016, by rfl⟩ : syracuseStep 573377 = 430033) B430033
theorem B573395 : Blo 381763 573395 := bstep (se 1 (by rfl) ⟨430046, by rfl⟩ : syracuseStep 573395 = 860093) B860093
theorem B573425 : Blo 381763 573425 := bstep (se 2 (by rfl) ⟨215034, by rfl⟩ : syracuseStep 573425 = 430069) B430069
theorem B573443 : Blo 381763 573443 := bstep (se 1 (by rfl) ⟨430082, by rfl⟩ : syracuseStep 573443 = 860165) B860165
theorem B573473 : Blo 381763 573473 := bstep (se 2 (by rfl) ⟨215052, by rfl⟩ : syracuseStep 573473 = 430105) B430105
theorem B573491 : Blo 381763 573491 := bstep (se 1 (by rfl) ⟨430118, by rfl⟩ : syracuseStep 573491 = 860237) B860237
theorem B573521 : Blo 381763 573521 := bstep (se 2 (by rfl) ⟨215070, by rfl⟩ : syracuseStep 573521 = 430141) B430141
theorem B966755 : Blo 381763 966755 := bstep (se 1 (by rfl) ⟨725066, by rfl⟩ : syracuseStep 966755 = 1450133) B1450133
theorem B573539 : Blo 381763 573539 := bstep (se 1 (by rfl) ⟨430154, by rfl⟩ : syracuseStep 573539 = 860309) B860309
theorem B573569 : Blo 381763 573569 := bstep (se 2 (by rfl) ⟨215088, by rfl⟩ : syracuseStep 573569 = 430177) B430177
theorem B573587 : Blo 381763 573587 := bstep (se 1 (by rfl) ⟨430190, by rfl⟩ : syracuseStep 573587 = 860381) B860381
theorem B573617 : Blo 381763 573617 := bstep (se 2 (by rfl) ⟨215106, by rfl⟩ : syracuseStep 573617 = 430213) B430213
theorem B1851569 : Blo 381763 1851569 := bstep (se 2 (by rfl) ⟨694338, by rfl⟩ : syracuseStep 1851569 = 1388677) B1388677
theorem B573635 : Blo 381763 573635 := bstep (se 1 (by rfl) ⟨430226, by rfl⟩ : syracuseStep 573635 = 860453) B860453
theorem B1294541 : Blo 381763 1294541 := bstep (se 3 (by rfl) ⟨242726, by rfl⟩ : syracuseStep 1294541 = 485453) B485453
theorem B573665 : Blo 381763 573665 := bstep (se 2 (by rfl) ⟨215124, by rfl⟩ : syracuseStep 573665 = 430249) B430249
theorem B1097965 : Blo 381763 1097965 := bstep (se 3 (by rfl) ⟨205868, by rfl⟩ : syracuseStep 1097965 = 411737) B411737
theorem B2769137 : Blo 381763 2769137 := bstep (se 2 (by rfl) ⟨1038426, by rfl⟩ : syracuseStep 2769137 = 2076853) B2076853
theorem B573683 : Blo 381763 573683 := bstep (se 1 (by rfl) ⟨430262, by rfl⟩ : syracuseStep 573683 = 860525) B860525
theorem B1294595 : Blo 381763 1294595 := bstep (se 1 (by rfl) ⟨970946, by rfl⟩ : syracuseStep 1294595 = 1941893) B1941893
theorem B573713 : Blo 381763 573713 := bstep (se 2 (by rfl) ⟨215142, by rfl⟩ : syracuseStep 573713 = 430285) B430285
theorem B573731 : Blo 381763 573731 := bstep (se 1 (by rfl) ⟨430298, by rfl⟩ : syracuseStep 573731 = 860597) B860597
theorem B573761 : Blo 381763 573761 := bstep (se 2 (by rfl) ⟨215160, by rfl⟩ : syracuseStep 573761 = 430321) B430321
theorem B573779 : Blo 381763 573779 := bstep (se 1 (by rfl) ⟨430334, by rfl⟩ : syracuseStep 573779 = 860669) B860669
theorem B573809 : Blo 381763 573809 := bstep (se 2 (by rfl) ⟨215178, by rfl⟩ : syracuseStep 573809 = 430357) B430357
theorem B573827 : Blo 381763 573827 := bstep (se 1 (by rfl) ⟨430370, by rfl⟩ : syracuseStep 573827 = 860741) B860741
theorem B573857 : Blo 381763 573857 := bstep (se 2 (by rfl) ⟨215196, by rfl⟩ : syracuseStep 573857 = 430393) B430393
theorem B573875 : Blo 381763 573875 := bstep (se 1 (by rfl) ⟨430406, by rfl⟩ : syracuseStep 573875 = 860813) B860813
theorem B573905 : Blo 381763 573905 := bstep (se 2 (by rfl) ⟨215214, by rfl⟩ : syracuseStep 573905 = 430429) B430429
theorem B1098193 : Blo 381763 1098193 := bstep (se 2 (by rfl) ⟨411822, by rfl⟩ : syracuseStep 1098193 = 823645) B823645
theorem B573923 : Blo 381763 573923 := bstep (se 1 (by rfl) ⟨430442, by rfl⟩ : syracuseStep 573923 = 860885) B860885
theorem B573953 : Blo 381763 573953 := bstep (se 2 (by rfl) ⟨215232, by rfl⟩ : syracuseStep 573953 = 430465) B430465
theorem B1294865 : Blo 381763 1294865 := bstep (se 2 (by rfl) ⟨485574, by rfl⟩ : syracuseStep 1294865 = 971149) B971149
theorem B573971 : Blo 381763 573971 := bstep (se 1 (by rfl) ⟨430478, by rfl⟩ : syracuseStep 573971 = 860957) B860957
theorem B410131 : Blo 381763 410131 := bstep (se 1 (by rfl) ⟨307598, by rfl⟩ : syracuseStep 410131 = 615197) B615197
theorem B2179619 : Blo 381763 2179619 := bstep (se 1 (by rfl) ⟨1634714, by rfl⟩ : syracuseStep 2179619 = 3269429) B3269429
theorem B1229357 : Blo 381763 1229357 := bstep (se 3 (by rfl) ⟨230504, by rfl⟩ : syracuseStep 1229357 = 461009) B461009
theorem B574001 : Blo 381763 574001 := bstep (se 2 (by rfl) ⟨215250, by rfl⟩ : syracuseStep 574001 = 430501) B430501
theorem B574019 : Blo 381763 574019 := bstep (se 1 (by rfl) ⟨430514, by rfl⟩ : syracuseStep 574019 = 861029) B861029
theorem B574049 : Blo 381763 574049 := bstep (se 2 (by rfl) ⟨215268, by rfl⟩ : syracuseStep 574049 = 430537) B430537
theorem B1098353 : Blo 381763 1098353 := bstep (se 2 (by rfl) ⟨411882, by rfl⟩ : syracuseStep 1098353 = 823765) B823765
theorem B574067 : Blo 381763 574067 := bstep (se 1 (by rfl) ⟨430550, by rfl⟩ : syracuseStep 574067 = 861101) B861101
theorem B574097 : Blo 381763 574097 := bstep (se 2 (by rfl) ⟨215286, by rfl⟩ : syracuseStep 574097 = 430573) B430573
theorem B574115 : Blo 381763 574115 := bstep (se 1 (by rfl) ⟨430586, by rfl⟩ : syracuseStep 574115 = 861173) B861173
theorem B574145 : Blo 381763 574145 := bstep (se 2 (by rfl) ⟨215304, by rfl⟩ : syracuseStep 574145 = 430609) B430609
theorem B574163 : Blo 381763 574163 := bstep (se 1 (by rfl) ⟨430622, by rfl⟩ : syracuseStep 574163 = 861245) B861245
theorem B1098467 : Blo 381763 1098467 := bstep (se 1 (by rfl) ⟨823850, by rfl⟩ : syracuseStep 1098467 = 1647701) B1647701
theorem B574193 : Blo 381763 574193 := bstep (se 2 (by rfl) ⟨215322, by rfl⟩ : syracuseStep 574193 = 430645) B430645
theorem B574211 : Blo 381763 574211 := bstep (se 1 (by rfl) ⟨430658, by rfl⟩ : syracuseStep 574211 = 861317) B861317
theorem B574241 : Blo 381763 574241 := bstep (se 2 (by rfl) ⟨215340, by rfl⟩ : syracuseStep 574241 = 430681) B430681
theorem B1295153 : Blo 381763 1295153 := bstep (se 2 (by rfl) ⟨485682, by rfl⟩ : syracuseStep 1295153 = 971365) B971365
theorem B574259 : Blo 381763 574259 := bstep (se 1 (by rfl) ⟨430694, by rfl⟩ : syracuseStep 574259 = 861389) B861389
theorem B574289 : Blo 381763 574289 := bstep (se 2 (by rfl) ⟨215358, by rfl⟩ : syracuseStep 574289 = 430717) B430717
theorem B574307 : Blo 381763 574307 := bstep (se 1 (by rfl) ⟨430730, by rfl⟩ : syracuseStep 574307 = 861461) B861461
theorem B574337 : Blo 381763 574337 := bstep (se 2 (by rfl) ⟨215376, by rfl⟩ : syracuseStep 574337 = 430753) B430753
theorem B574355 : Blo 381763 574355 := bstep (se 1 (by rfl) ⟨430766, by rfl⟩ : syracuseStep 574355 = 861533) B861533
theorem B574385 : Blo 381763 574385 := bstep (se 2 (by rfl) ⟨215394, by rfl⟩ : syracuseStep 574385 = 430789) B430789
theorem B1000369 : Blo 381763 1000369 := bstep (se 2 (by rfl) ⟨375138, by rfl⟩ : syracuseStep 1000369 = 750277) B750277
theorem B1950641 : Blo 381763 1950641 := bstep (se 2 (by rfl) ⟨731490, by rfl⟩ : syracuseStep 1950641 = 1462981) B1462981
theorem B574403 : Blo 381763 574403 := bstep (se 1 (by rfl) ⟨430802, by rfl⟩ : syracuseStep 574403 = 861605) B861605
theorem B2900933 : Blo 381763 2900933 := bstep (se 4 (by rfl) ⟨271962, by rfl⟩ : syracuseStep 2900933 = 543925) B543925
theorem B574433 : Blo 381763 574433 := bstep (se 2 (by rfl) ⟨215412, by rfl⟩ : syracuseStep 574433 = 430825) B430825
theorem B574451 : Blo 381763 574451 := bstep (se 1 (by rfl) ⟨430838, by rfl⟩ : syracuseStep 574451 = 861677) B861677
theorem B967697 : Blo 381763 967697 := bstep (se 2 (by rfl) ⟨362886, by rfl⟩ : syracuseStep 967697 = 725773) B725773
theorem B574481 : Blo 381763 574481 := bstep (se 2 (by rfl) ⟨215430, by rfl⟩ : syracuseStep 574481 = 430861) B430861
theorem B574499 : Blo 381763 574499 := bstep (se 1 (by rfl) ⟨430874, by rfl⟩ : syracuseStep 574499 = 861749) B861749
theorem B1295405 : Blo 381763 1295405 := bstep (se 3 (by rfl) ⟨242888, by rfl⟩ : syracuseStep 1295405 = 485777) B485777
theorem B574529 : Blo 381763 574529 := bstep (se 2 (by rfl) ⟨215448, by rfl⟩ : syracuseStep 574529 = 430897) B430897
theorem B967747 : Blo 381763 967747 := bstep (se 1 (by rfl) ⟨725810, by rfl⟩ : syracuseStep 967747 = 1451621) B1451621
theorem B574547 : Blo 381763 574547 := bstep (se 1 (by rfl) ⟨430910, by rfl⟩ : syracuseStep 574547 = 861821) B861821
theorem B1295459 : Blo 381763 1295459 := bstep (se 1 (by rfl) ⟨971594, by rfl⟩ : syracuseStep 1295459 = 1943189) B1943189
theorem B7554161 : Blo 381763 7554161 := bstep (se 2 (by rfl) ⟨2832810, by rfl⟩ : syracuseStep 7554161 = 5665621) B5665621
theorem B574577 : Blo 381763 574577 := bstep (se 2 (by rfl) ⟨215466, by rfl⟩ : syracuseStep 574577 = 430933) B430933
theorem B574595 : Blo 381763 574595 := bstep (se 1 (by rfl) ⟨430946, by rfl⟩ : syracuseStep 574595 = 861893) B861893
theorem B574625 : Blo 381763 574625 := bstep (se 2 (by rfl) ⟨215484, by rfl⟩ : syracuseStep 574625 = 430969) B430969
theorem B574643 : Blo 381763 574643 := bstep (se 1 (by rfl) ⟨430982, by rfl⟩ : syracuseStep 574643 = 861965) B861965
theorem B967889 : Blo 381763 967889 := bstep (se 2 (by rfl) ⟨362958, by rfl⟩ : syracuseStep 967889 = 725917) B725917
theorem B574673 : Blo 381763 574673 := bstep (se 2 (by rfl) ⟨215502, by rfl⟩ : syracuseStep 574673 = 431005) B431005
theorem B574691 : Blo 381763 574691 := bstep (se 1 (by rfl) ⟨431018, by rfl⟩ : syracuseStep 574691 = 862037) B862037
theorem B574721 : Blo 381763 574721 := bstep (se 2 (by rfl) ⟨215520, by rfl⟩ : syracuseStep 574721 = 431041) B431041
theorem B574739 : Blo 381763 574739 := bstep (se 1 (by rfl) ⟨431054, by rfl⟩ : syracuseStep 574739 = 862109) B862109
theorem B574769 : Blo 381763 574769 := bstep (se 2 (by rfl) ⟨215538, by rfl⟩ : syracuseStep 574769 = 431077) B431077
theorem B574787 : Blo 381763 574787 := bstep (se 1 (by rfl) ⟨431090, by rfl⟩ : syracuseStep 574787 = 862181) B862181
theorem B574817 : Blo 381763 574817 := bstep (se 2 (by rfl) ⟨215556, by rfl⟩ : syracuseStep 574817 = 431113) B431113
theorem B1295729 : Blo 381763 1295729 := bstep (se 2 (by rfl) ⟨485898, by rfl⟩ : syracuseStep 1295729 = 971797) B971797
theorem B574835 : Blo 381763 574835 := bstep (se 1 (by rfl) ⟨431126, by rfl⟩ : syracuseStep 574835 = 862253) B862253
theorem B574865 : Blo 381763 574865 := bstep (se 2 (by rfl) ⟨215574, by rfl⟩ : syracuseStep 574865 = 431149) B431149
theorem B574883 : Blo 381763 574883 := bstep (se 1 (by rfl) ⟨431162, by rfl⟩ : syracuseStep 574883 = 862325) B862325
theorem B574913 : Blo 381763 574913 := bstep (se 2 (by rfl) ⟨215592, by rfl⟩ : syracuseStep 574913 = 431185) B431185
theorem B574931 : Blo 381763 574931 := bstep (se 1 (by rfl) ⟨431198, by rfl⟩ : syracuseStep 574931 = 862397) B862397
theorem B574961 : Blo 381763 574961 := bstep (se 2 (by rfl) ⟨215610, by rfl⟩ : syracuseStep 574961 = 431221) B431221
theorem B574979 : Blo 381763 574979 := bstep (se 1 (by rfl) ⟨431234, by rfl⟩ : syracuseStep 574979 = 862469) B862469
theorem B411139 : Blo 381763 411139 := bstep (se 1 (by rfl) ⟨308354, by rfl⟩ : syracuseStep 411139 = 616709) B616709
theorem B2180621 : Blo 381763 2180621 := bstep (se 3 (by rfl) ⟨408866, by rfl⟩ : syracuseStep 2180621 = 817733) B817733
theorem B575009 : Blo 381763 575009 := bstep (se 2 (by rfl) ⟨215628, by rfl⟩ : syracuseStep 575009 = 431257) B431257
theorem B575027 : Blo 381763 575027 := bstep (se 1 (by rfl) ⟨431270, by rfl⟩ : syracuseStep 575027 = 862541) B862541
theorem B575057 : Blo 381763 575057 := bstep (se 2 (by rfl) ⟨215646, by rfl⟩ : syracuseStep 575057 = 431293) B431293
theorem B575075 : Blo 381763 575075 := bstep (se 1 (by rfl) ⟨431306, by rfl⟩ : syracuseStep 575075 = 862613) B862613
theorem B575105 : Blo 381763 575105 := bstep (se 2 (by rfl) ⟨215664, by rfl⟩ : syracuseStep 575105 = 431329) B431329
theorem B1459853 : Blo 381763 1459853 := bstep (se 3 (by rfl) ⟨273722, by rfl⟩ : syracuseStep 1459853 = 547445) B547445
theorem B575123 : Blo 381763 575123 := bstep (se 1 (by rfl) ⟨431342, by rfl⟩ : syracuseStep 575123 = 862685) B862685
theorem B575153 : Blo 381763 575153 := bstep (se 2 (by rfl) ⟨215682, by rfl⟩ : syracuseStep 575153 = 431365) B431365
theorem B575171 : Blo 381763 575171 := bstep (se 1 (by rfl) ⟨431378, by rfl⟩ : syracuseStep 575171 = 862757) B862757
theorem B575201 : Blo 381763 575201 := bstep (se 2 (by rfl) ⟨215700, by rfl⟩ : syracuseStep 575201 = 431401) B431401
theorem B575219 : Blo 381763 575219 := bstep (se 1 (by rfl) ⟨431414, by rfl⟩ : syracuseStep 575219 = 862829) B862829
theorem B3294989 : Blo 381763 3294989 := bstep (se 3 (by rfl) ⟨617810, by rfl⟩ : syracuseStep 3294989 = 1235621) B1235621
theorem B575249 : Blo 381763 575249 := bstep (se 2 (by rfl) ⟨215718, by rfl⟩ : syracuseStep 575249 = 431437) B431437
theorem B575267 : Blo 381763 575267 := bstep (se 1 (by rfl) ⟨431450, by rfl⟩ : syracuseStep 575267 = 862901) B862901
theorem B575297 : Blo 381763 575297 := bstep (se 2 (by rfl) ⟨215736, by rfl⟩ : syracuseStep 575297 = 431473) B431473
theorem B575315 : Blo 381763 575315 := bstep (se 1 (by rfl) ⟨431486, by rfl⟩ : syracuseStep 575315 = 862973) B862973
theorem B575345 : Blo 381763 575345 := bstep (se 2 (by rfl) ⟨215754, by rfl⟩ : syracuseStep 575345 = 431509) B431509
theorem B575363 : Blo 381763 575363 := bstep (se 1 (by rfl) ⟨431522, by rfl⟩ : syracuseStep 575363 = 863045) B863045
theorem B1296269 : Blo 381763 1296269 := bstep (se 3 (by rfl) ⟨243050, by rfl⟩ : syracuseStep 1296269 = 486101) B486101
theorem B575393 : Blo 381763 575393 := bstep (se 2 (by rfl) ⟨215772, by rfl⟩ : syracuseStep 575393 = 431545) B431545
theorem B575411 : Blo 381763 575411 := bstep (se 1 (by rfl) ⟨431558, by rfl⟩ : syracuseStep 575411 = 863117) B863117
theorem B1296323 : Blo 381763 1296323 := bstep (se 1 (by rfl) ⟨972242, by rfl⟩ : syracuseStep 1296323 = 1944485) B1944485
theorem B575441 : Blo 381763 575441 := bstep (se 2 (by rfl) ⟨215790, by rfl⟩ : syracuseStep 575441 = 431581) B431581
theorem B575459 : Blo 381763 575459 := bstep (se 1 (by rfl) ⟨431594, by rfl⟩ : syracuseStep 575459 = 863189) B863189
theorem B575489 : Blo 381763 575489 := bstep (se 2 (by rfl) ⟨215808, by rfl⟩ : syracuseStep 575489 = 431617) B431617
theorem B575507 : Blo 381763 575507 := bstep (se 1 (by rfl) ⟨431630, by rfl⟩ : syracuseStep 575507 = 863261) B863261
theorem B575537 : Blo 381763 575537 := bstep (se 2 (by rfl) ⟨215826, by rfl⟩ : syracuseStep 575537 = 431653) B431653
theorem B575555 : Blo 381763 575555 := bstep (se 1 (by rfl) ⟨431666, by rfl⟩ : syracuseStep 575555 = 863333) B863333
theorem B575585 : Blo 381763 575585 := bstep (se 2 (by rfl) ⟨215844, by rfl⟩ : syracuseStep 575585 = 431689) B431689
theorem B575603 : Blo 381763 575603 := bstep (se 1 (by rfl) ⟨431702, by rfl⟩ : syracuseStep 575603 = 863405) B863405
theorem B575633 : Blo 381763 575633 := bstep (se 2 (by rfl) ⟨215862, by rfl⟩ : syracuseStep 575633 = 431725) B431725
theorem B575651 : Blo 381763 575651 := bstep (se 1 (by rfl) ⟨431738, by rfl⟩ : syracuseStep 575651 = 863477) B863477
theorem B968881 : Blo 381763 968881 := bstep (se 2 (by rfl) ⟨363330, by rfl⟩ : syracuseStep 968881 = 726661) B726661
theorem B575681 : Blo 381763 575681 := bstep (se 2 (by rfl) ⟨215880, by rfl⟩ : syracuseStep 575681 = 431761) B431761
theorem B1296593 : Blo 381763 1296593 := bstep (se 2 (by rfl) ⟨486222, by rfl⟩ : syracuseStep 1296593 = 972445) B972445
theorem B575699 : Blo 381763 575699 := bstep (se 1 (by rfl) ⟨431774, by rfl⟩ : syracuseStep 575699 = 863549) B863549
theorem B575729 : Blo 381763 575729 := bstep (se 2 (by rfl) ⟨215898, by rfl⟩ : syracuseStep 575729 = 431797) B431797
theorem B1755377 : Blo 381763 1755377 := bstep (se 2 (by rfl) ⟨658266, by rfl⟩ : syracuseStep 1755377 = 1316533) B1316533
theorem B575747 : Blo 381763 575747 := bstep (se 1 (by rfl) ⟨431810, by rfl⟩ : syracuseStep 575747 = 863621) B863621
theorem B9324821 : Blo 381763 9324821 := bstep (se 6 (by rfl) ⟨218550, by rfl⟩ : syracuseStep 9324821 = 437101) B437101
theorem B575777 : Blo 381763 575777 := bstep (se 2 (by rfl) ⟨215916, by rfl⟩ : syracuseStep 575777 = 431833) B431833
theorem B575795 : Blo 381763 575795 := bstep (se 1 (by rfl) ⟨431846, by rfl⟩ : syracuseStep 575795 = 863693) B863693
theorem B575825 : Blo 381763 575825 := bstep (se 2 (by rfl) ⟨215934, by rfl⟩ : syracuseStep 575825 = 431869) B431869
theorem B575843 : Blo 381763 575843 := bstep (se 1 (by rfl) ⟨431882, by rfl⟩ : syracuseStep 575843 = 863765) B863765
theorem B1952099 : Blo 381763 1952099 := bstep (se 1 (by rfl) ⟨1464074, by rfl⟩ : syracuseStep 1952099 = 2928149) B2928149
theorem B1231213 : Blo 381763 1231213 := bstep (se 3 (by rfl) ⟨230852, by rfl⟩ : syracuseStep 1231213 = 461705) B461705
theorem B575873 : Blo 381763 575873 := bstep (se 2 (by rfl) ⟨215952, by rfl⟩ : syracuseStep 575873 = 431905) B431905
theorem B575891 : Blo 381763 575891 := bstep (se 1 (by rfl) ⟨431918, by rfl⟩ : syracuseStep 575891 = 863837) B863837
theorem B575921 : Blo 381763 575921 := bstep (se 2 (by rfl) ⟨215970, by rfl⟩ : syracuseStep 575921 = 431941) B431941
theorem B969155 : Blo 381763 969155 := bstep (se 1 (by rfl) ⟨726866, by rfl⟩ : syracuseStep 969155 = 1453733) B1453733
theorem B575939 : Blo 381763 575939 := bstep (se 1 (by rfl) ⟨431954, by rfl⟩ : syracuseStep 575939 = 863909) B863909
theorem B575969 : Blo 381763 575969 := bstep (se 2 (by rfl) ⟨215988, by rfl⟩ : syracuseStep 575969 = 431977) B431977
theorem B575987 : Blo 381763 575987 := bstep (se 1 (by rfl) ⟨431990, by rfl⟩ : syracuseStep 575987 = 863981) B863981
theorem B576017 : Blo 381763 576017 := bstep (se 2 (by rfl) ⟨216006, by rfl⟩ : syracuseStep 576017 = 432013) B432013
theorem B576035 : Blo 381763 576035 := bstep (se 1 (by rfl) ⟨432026, by rfl⟩ : syracuseStep 576035 = 864053) B864053
theorem B576065 : Blo 381763 576065 := bstep (se 2 (by rfl) ⟨216024, by rfl⟩ : syracuseStep 576065 = 432049) B432049
theorem B576083 : Blo 381763 576083 := bstep (se 1 (by rfl) ⟨432062, by rfl⟩ : syracuseStep 576083 = 864125) B864125
theorem B2083427 : Blo 381763 2083427 := bstep (se 1 (by rfl) ⟨1562570, by rfl⟩ : syracuseStep 2083427 = 3125141) B3125141
theorem B576113 : Blo 381763 576113 := bstep (se 2 (by rfl) ⟨216042, by rfl⟩ : syracuseStep 576113 = 432085) B432085
theorem B969347 : Blo 381763 969347 := bstep (se 1 (by rfl) ⟨727010, by rfl⟩ : syracuseStep 969347 = 1454021) B1454021
theorem B576131 : Blo 381763 576131 := bstep (se 1 (by rfl) ⟨432098, by rfl⟩ : syracuseStep 576131 = 864197) B864197
theorem B576161 : Blo 381763 576161 := bstep (se 2 (by rfl) ⟨216060, by rfl⟩ : syracuseStep 576161 = 432121) B432121
theorem B576179 : Blo 381763 576179 := bstep (se 1 (by rfl) ⟨432134, by rfl⟩ : syracuseStep 576179 = 864269) B864269
theorem B576209 : Blo 381763 576209 := bstep (se 2 (by rfl) ⟨216078, by rfl⟩ : syracuseStep 576209 = 432157) B432157
theorem B576227 : Blo 381763 576227 := bstep (se 1 (by rfl) ⟨432170, by rfl⟩ : syracuseStep 576227 = 864341) B864341
theorem B1297133 : Blo 381763 1297133 := bstep (se 3 (by rfl) ⟨243212, by rfl⟩ : syracuseStep 1297133 = 486425) B486425
theorem B576257 : Blo 381763 576257 := bstep (se 2 (by rfl) ⟨216096, by rfl⟩ : syracuseStep 576257 = 432193) B432193
theorem B576275 : Blo 381763 576275 := bstep (se 1 (by rfl) ⟨432206, by rfl⟩ : syracuseStep 576275 = 864413) B864413
theorem B1297187 : Blo 381763 1297187 := bstep (se 1 (by rfl) ⟨972890, by rfl⟩ : syracuseStep 1297187 = 1945781) B1945781
theorem B576305 : Blo 381763 576305 := bstep (se 2 (by rfl) ⟨216114, by rfl⟩ : syracuseStep 576305 = 432229) B432229
theorem B576323 : Blo 381763 576323 := bstep (se 1 (by rfl) ⟨432242, by rfl⟩ : syracuseStep 576323 = 864485) B864485
theorem B576353 : Blo 381763 576353 := bstep (se 2 (by rfl) ⟨216132, by rfl⟩ : syracuseStep 576353 = 432265) B432265
theorem B543601 : Blo 381763 543601 := bstep (se 2 (by rfl) ⟨203850, by rfl⟩ : syracuseStep 543601 = 407701) B407701
theorem B576371 : Blo 381763 576371 := bstep (se 1 (by rfl) ⟨432278, by rfl⟩ : syracuseStep 576371 = 864557) B864557
theorem B576401 : Blo 381763 576401 := bstep (se 2 (by rfl) ⟨216150, by rfl⟩ : syracuseStep 576401 = 432301) B432301
theorem B576419 : Blo 381763 576419 := bstep (se 1 (by rfl) ⟨432314, by rfl⟩ : syracuseStep 576419 = 864629) B864629
theorem B576449 : Blo 381763 576449 := bstep (se 2 (by rfl) ⟨216168, by rfl⟩ : syracuseStep 576449 = 432337) B432337
theorem B576467 : Blo 381763 576467 := bstep (se 1 (by rfl) ⟨432350, by rfl⟩ : syracuseStep 576467 = 864701) B864701
theorem B576497 : Blo 381763 576497 := bstep (se 2 (by rfl) ⟨216186, by rfl⟩ : syracuseStep 576497 = 432373) B432373
theorem B576515 : Blo 381763 576515 := bstep (se 1 (by rfl) ⟨432386, by rfl⟩ : syracuseStep 576515 = 864773) B864773
theorem B1035281 : Blo 381763 1035281 := bstep (se 2 (by rfl) ⟨388230, by rfl⟩ : syracuseStep 1035281 = 776461) B776461
theorem B576545 : Blo 381763 576545 := bstep (se 2 (by rfl) ⟨216204, by rfl⟩ : syracuseStep 576545 = 432409) B432409
theorem B1297457 : Blo 381763 1297457 := bstep (se 2 (by rfl) ⟨486546, by rfl⟩ : syracuseStep 1297457 = 973093) B973093
theorem B576563 : Blo 381763 576563 := bstep (se 1 (by rfl) ⟨432422, by rfl⟩ : syracuseStep 576563 = 864845) B864845
theorem B576593 : Blo 381763 576593 := bstep (se 2 (by rfl) ⟨216222, by rfl⟩ : syracuseStep 576593 = 432445) B432445
theorem B576611 : Blo 381763 576611 := bstep (se 1 (by rfl) ⟨432458, by rfl⟩ : syracuseStep 576611 = 864917) B864917
theorem B576641 : Blo 381763 576641 := bstep (se 2 (by rfl) ⟨216240, by rfl⟩ : syracuseStep 576641 = 432481) B432481
theorem B1952909 : Blo 381763 1952909 := bstep (se 3 (by rfl) ⟨366170, by rfl⟩ : syracuseStep 1952909 = 732341) B732341
theorem B576659 : Blo 381763 576659 := bstep (se 1 (by rfl) ⟨432494, by rfl⟩ : syracuseStep 576659 = 864989) B864989
theorem B576689 : Blo 381763 576689 := bstep (se 2 (by rfl) ⟨216258, by rfl⟩ : syracuseStep 576689 = 432517) B432517
theorem B543937 : Blo 381763 543937 := bstep (se 2 (by rfl) ⟨203976, by rfl⟩ : syracuseStep 543937 = 407953) B407953
theorem B576707 : Blo 381763 576707 := bstep (se 1 (by rfl) ⟨432530, by rfl⟩ : syracuseStep 576707 = 865061) B865061
theorem B576737 : Blo 381763 576737 := bstep (se 2 (by rfl) ⟨216276, by rfl⟩ : syracuseStep 576737 = 432553) B432553
theorem B576755 : Blo 381763 576755 := bstep (se 1 (by rfl) ⟨432566, by rfl⟩ : syracuseStep 576755 = 865133) B865133
theorem B576785 : Blo 381763 576785 := bstep (se 2 (by rfl) ⟨216294, by rfl⟩ : syracuseStep 576785 = 432589) B432589
theorem B576803 : Blo 381763 576803 := bstep (se 1 (by rfl) ⟨432602, by rfl⟩ : syracuseStep 576803 = 865205) B865205
theorem B576833 : Blo 381763 576833 := bstep (se 2 (by rfl) ⟨216312, by rfl⟩ : syracuseStep 576833 = 432625) B432625
theorem B576851 : Blo 381763 576851 := bstep (se 1 (by rfl) ⟨432638, by rfl⟩ : syracuseStep 576851 = 865277) B865277
theorem B576881 : Blo 381763 576881 := bstep (se 2 (by rfl) ⟨216330, by rfl⟩ : syracuseStep 576881 = 432661) B432661
theorem B576899 : Blo 381763 576899 := bstep (se 1 (by rfl) ⟨432674, by rfl⟩ : syracuseStep 576899 = 865349) B865349
theorem B576929 : Blo 381763 576929 := bstep (se 2 (by rfl) ⟨216348, by rfl⟩ : syracuseStep 576929 = 432697) B432697
theorem B576947 : Blo 381763 576947 := bstep (se 1 (by rfl) ⟨432710, by rfl⟩ : syracuseStep 576947 = 865421) B865421
theorem B576977 : Blo 381763 576977 := bstep (se 2 (by rfl) ⟨216366, by rfl⟩ : syracuseStep 576977 = 432733) B432733
theorem B576995 : Blo 381763 576995 := bstep (se 1 (by rfl) ⟨432746, by rfl⟩ : syracuseStep 576995 = 865493) B865493
theorem B577025 : Blo 381763 577025 := bstep (se 2 (by rfl) ⟨216384, by rfl⟩ : syracuseStep 577025 = 432769) B432769
theorem B3919373 : Blo 381763 3919373 := bstep (se 3 (by rfl) ⟨734882, by rfl⟩ : syracuseStep 3919373 = 1469765) B1469765
theorem B577043 : Blo 381763 577043 := bstep (se 1 (by rfl) ⟨432782, by rfl⟩ : syracuseStep 577043 = 865565) B865565
theorem B970289 : Blo 381763 970289 := bstep (se 2 (by rfl) ⟨363858, by rfl⟩ : syracuseStep 970289 = 727717) B727717
theorem B577073 : Blo 381763 577073 := bstep (se 2 (by rfl) ⟨216402, by rfl⟩ : syracuseStep 577073 = 432805) B432805
theorem B577091 : Blo 381763 577091 := bstep (se 1 (by rfl) ⟨432818, by rfl⟩ : syracuseStep 577091 = 865637) B865637
theorem B1297997 : Blo 381763 1297997 := bstep (se 3 (by rfl) ⟨243374, by rfl⟩ : syracuseStep 1297997 = 486749) B486749
theorem B577121 : Blo 381763 577121 := bstep (se 2 (by rfl) ⟨216420, by rfl⟩ : syracuseStep 577121 = 432841) B432841
theorem B970339 : Blo 381763 970339 := bstep (se 1 (by rfl) ⟨727754, by rfl⟩ : syracuseStep 970339 = 1455509) B1455509
theorem B577139 : Blo 381763 577139 := bstep (se 1 (by rfl) ⟨432854, by rfl⟩ : syracuseStep 577139 = 865709) B865709
theorem B1298051 : Blo 381763 1298051 := bstep (se 1 (by rfl) ⟨973538, by rfl⟩ : syracuseStep 1298051 = 1947077) B1947077
theorem B577169 : Blo 381763 577169 := bstep (se 2 (by rfl) ⟨216438, by rfl⟩ : syracuseStep 577169 = 432877) B432877
theorem B577187 : Blo 381763 577187 := bstep (se 1 (by rfl) ⟨432890, by rfl⟩ : syracuseStep 577187 = 865781) B865781
theorem B1756835 : Blo 381763 1756835 := bstep (se 1 (by rfl) ⟨1317626, by rfl⟩ : syracuseStep 1756835 = 2635253) B2635253
theorem B577217 : Blo 381763 577217 := bstep (se 2 (by rfl) ⟨216456, by rfl⟩ : syracuseStep 577217 = 432913) B432913
theorem B577235 : Blo 381763 577235 := bstep (se 1 (by rfl) ⟨432926, by rfl⟩ : syracuseStep 577235 = 865853) B865853
theorem B5557987 : Blo 381763 5557987 := bstep (se 1 (by rfl) ⟨4168490, by rfl⟩ : syracuseStep 5557987 = 8336981) B8336981
theorem B970481 : Blo 381763 970481 := bstep (se 2 (by rfl) ⟨363930, by rfl⟩ : syracuseStep 970481 = 727861) B727861
theorem B577265 : Blo 381763 577265 := bstep (se 2 (by rfl) ⟨216474, by rfl⟩ : syracuseStep 577265 = 432949) B432949
theorem B577283 : Blo 381763 577283 := bstep (se 1 (by rfl) ⟨432962, by rfl⟩ : syracuseStep 577283 = 865925) B865925
theorem B544529 : Blo 381763 544529 := bstep (se 2 (by rfl) ⟨204198, by rfl⟩ : syracuseStep 544529 = 408397) B408397
theorem B577313 : Blo 381763 577313 := bstep (se 2 (by rfl) ⟨216492, by rfl⟩ : syracuseStep 577313 = 432985) B432985
theorem B577331 : Blo 381763 577331 := bstep (se 1 (by rfl) ⟨432998, by rfl⟩ : syracuseStep 577331 = 865997) B865997
theorem B577361 : Blo 381763 577361 := bstep (se 2 (by rfl) ⟨216510, by rfl⟩ : syracuseStep 577361 = 433021) B433021
theorem B577379 : Blo 381763 577379 := bstep (se 1 (by rfl) ⟨433034, by rfl⟩ : syracuseStep 577379 = 866069) B866069
theorem B577409 : Blo 381763 577409 := bstep (se 2 (by rfl) ⟨216528, by rfl⟩ : syracuseStep 577409 = 433057) B433057
theorem B774019 : Blo 381763 774019 := bstep (se 1 (by rfl) ⟨580514, by rfl⟩ : syracuseStep 774019 = 1161029) B1161029
theorem B1298321 : Blo 381763 1298321 := bstep (se 2 (by rfl) ⟨486870, by rfl⟩ : syracuseStep 1298321 = 973741) B973741
theorem B577427 : Blo 381763 577427 := bstep (se 1 (by rfl) ⟨433070, by rfl⟩ : syracuseStep 577427 = 866141) B866141
theorem B577457 : Blo 381763 577457 := bstep (se 2 (by rfl) ⟨216546, by rfl⟩ : syracuseStep 577457 = 433093) B433093
theorem B577475 : Blo 381763 577475 := bstep (se 1 (by rfl) ⟨433106, by rfl⟩ : syracuseStep 577475 = 866213) B866213
theorem B577505 : Blo 381763 577505 := bstep (se 2 (by rfl) ⟨216564, by rfl⟩ : syracuseStep 577505 = 433129) B433129
theorem B577523 : Blo 381763 577523 := bstep (se 1 (by rfl) ⟨433142, by rfl⟩ : syracuseStep 577523 = 866285) B866285
theorem B577553 : Blo 381763 577553 := bstep (se 2 (by rfl) ⟨216582, by rfl⟩ : syracuseStep 577553 = 433165) B433165
theorem B577571 : Blo 381763 577571 := bstep (se 1 (by rfl) ⟨433178, by rfl⟩ : syracuseStep 577571 = 866357) B866357
theorem B1232945 : Blo 381763 1232945 := bstep (se 2 (by rfl) ⟨462354, by rfl⟩ : syracuseStep 1232945 = 924709) B924709
theorem B577601 : Blo 381763 577601 := bstep (se 2 (by rfl) ⟨216600, by rfl⟩ : syracuseStep 577601 = 433201) B433201
theorem B3952709 : Blo 381763 3952709 := bstep (se 4 (by rfl) ⟨370566, by rfl⟩ : syracuseStep 3952709 = 741133) B741133
theorem B577619 : Blo 381763 577619 := bstep (se 1 (by rfl) ⟨433214, by rfl⟩ : syracuseStep 577619 = 866429) B866429
theorem B577649 : Blo 381763 577649 := bstep (se 2 (by rfl) ⟨216618, by rfl⟩ : syracuseStep 577649 = 433237) B433237
theorem B577667 : Blo 381763 577667 := bstep (se 1 (by rfl) ⟨433250, by rfl⟩ : syracuseStep 577667 = 866501) B866501
theorem B577697 : Blo 381763 577697 := bstep (se 2 (by rfl) ⟨216636, by rfl⟩ : syracuseStep 577697 = 433273) B433273
theorem B577715 : Blo 381763 577715 := bstep (se 1 (by rfl) ⟨433286, by rfl⟩ : syracuseStep 577715 = 866573) B866573
theorem B577745 : Blo 381763 577745 := bstep (se 2 (by rfl) ⟨216654, by rfl⟩ : syracuseStep 577745 = 433309) B433309
theorem B577763 : Blo 381763 577763 := bstep (se 1 (by rfl) ⟨433322, by rfl⟩ : syracuseStep 577763 = 866645) B866645
theorem B577793 : Blo 381763 577793 := bstep (se 2 (by rfl) ⟨216672, by rfl⟩ : syracuseStep 577793 = 433345) B433345
theorem B577811 : Blo 381763 577811 := bstep (se 1 (by rfl) ⟨433358, by rfl⟩ : syracuseStep 577811 = 866717) B866717
theorem B545059 : Blo 381763 545059 := bstep (se 1 (by rfl) ⟨408794, by rfl⟩ : syracuseStep 545059 = 817589) B817589
theorem B577841 : Blo 381763 577841 := bstep (se 2 (by rfl) ⟨216690, by rfl⟩ : syracuseStep 577841 = 433381) B433381
theorem B577859 : Blo 381763 577859 := bstep (se 1 (by rfl) ⟨433394, by rfl⟩ : syracuseStep 577859 = 866789) B866789
theorem B577889 : Blo 381763 577889 := bstep (se 2 (by rfl) ⟨216708, by rfl⟩ : syracuseStep 577889 = 433417) B433417
theorem B2183537 : Blo 381763 2183537 := bstep (se 2 (by rfl) ⟨818826, by rfl⟩ : syracuseStep 2183537 = 1637653) B1637653
theorem B577907 : Blo 381763 577907 := bstep (se 1 (by rfl) ⟨433430, by rfl⟩ : syracuseStep 577907 = 866861) B866861
theorem B577937 : Blo 381763 577937 := bstep (se 2 (by rfl) ⟨216726, by rfl⟩ : syracuseStep 577937 = 433453) B433453
theorem B577955 : Blo 381763 577955 := bstep (se 1 (by rfl) ⟨433466, by rfl⟩ : syracuseStep 577955 = 866933) B866933
theorem B1298861 : Blo 381763 1298861 := bstep (se 3 (by rfl) ⟨243536, by rfl⟩ : syracuseStep 1298861 = 487073) B487073
theorem B676289 : Blo 381763 676289 := bstep (se 2 (by rfl) ⟨253608, by rfl⟩ : syracuseStep 676289 = 507217) B507217
theorem B577985 : Blo 381763 577985 := bstep (se 2 (by rfl) ⟨216744, by rfl⟩ : syracuseStep 577985 = 433489) B433489
theorem B17912261 : Blo 381763 17912261 := bstep (se 4 (by rfl) ⟨1679274, by rfl⟩ : syracuseStep 17912261 = 3358549) B3358549
theorem B578003 : Blo 381763 578003 := bstep (se 1 (by rfl) ⟨433502, by rfl⟩ : syracuseStep 578003 = 867005) B867005
theorem B1298915 : Blo 381763 1298915 := bstep (se 1 (by rfl) ⟨974186, by rfl⟩ : syracuseStep 1298915 = 1948373) B1948373
theorem B1462769 : Blo 381763 1462769 := bstep (se 2 (by rfl) ⟨548538, by rfl⟩ : syracuseStep 1462769 = 1097077) B1097077
theorem B578033 : Blo 381763 578033 := bstep (se 2 (by rfl) ⟨216762, by rfl⟩ : syracuseStep 578033 = 433525) B433525
theorem B578051 : Blo 381763 578051 := bstep (se 1 (by rfl) ⟨433538, by rfl⟩ : syracuseStep 578051 = 867077) B867077
theorem B578081 : Blo 381763 578081 := bstep (se 2 (by rfl) ⟨216780, by rfl⟩ : syracuseStep 578081 = 433561) B433561
theorem B578099 : Blo 381763 578099 := bstep (se 1 (by rfl) ⟨433574, by rfl⟩ : syracuseStep 578099 = 867149) B867149
theorem B578129 : Blo 381763 578129 := bstep (se 2 (by rfl) ⟨216798, by rfl⟩ : syracuseStep 578129 = 433597) B433597
theorem B578147 : Blo 381763 578147 := bstep (se 1 (by rfl) ⟨433610, by rfl⟩ : syracuseStep 578147 = 867221) B867221
theorem B545395 : Blo 381763 545395 := bstep (se 1 (by rfl) ⟨409046, by rfl⟩ : syracuseStep 545395 = 818093) B818093
theorem B578177 : Blo 381763 578177 := bstep (se 2 (by rfl) ⟨216816, by rfl⟩ : syracuseStep 578177 = 433633) B433633
theorem B578195 : Blo 381763 578195 := bstep (se 1 (by rfl) ⟨433646, by rfl⟩ : syracuseStep 578195 = 867293) B867293
theorem B1233571 : Blo 381763 1233571 := bstep (se 1 (by rfl) ⟨925178, by rfl⟩ : syracuseStep 1233571 = 1850357) B1850357
theorem B578225 : Blo 381763 578225 := bstep (se 2 (by rfl) ⟨216834, by rfl⟩ : syracuseStep 578225 = 433669) B433669
theorem B578243 : Blo 381763 578243 := bstep (se 1 (by rfl) ⟨433682, by rfl⟩ : syracuseStep 578243 = 867365) B867365
theorem B971473 : Blo 381763 971473 := bstep (se 2 (by rfl) ⟨364302, by rfl⟩ : syracuseStep 971473 = 728605) B728605
theorem B578273 : Blo 381763 578273 := bstep (se 2 (by rfl) ⟨216852, by rfl⟩ : syracuseStep 578273 = 433705) B433705
theorem B1299185 : Blo 381763 1299185 := bstep (se 2 (by rfl) ⟨487194, by rfl⟩ : syracuseStep 1299185 = 974389) B974389
theorem B578291 : Blo 381763 578291 := bstep (se 1 (by rfl) ⟨433718, by rfl⟩ : syracuseStep 578291 = 867437) B867437
theorem B578321 : Blo 381763 578321 := bstep (se 2 (by rfl) ⟨216870, by rfl⟩ : syracuseStep 578321 = 433741) B433741
theorem B578339 : Blo 381763 578339 := bstep (se 1 (by rfl) ⟨433754, by rfl⟩ : syracuseStep 578339 = 867509) B867509
theorem B2216753 : Blo 381763 2216753 := bstep (se 2 (by rfl) ⟨831282, by rfl⟩ : syracuseStep 2216753 = 1662565) B1662565
theorem B578369 : Blo 381763 578369 := bstep (se 2 (by rfl) ⟨216888, by rfl⟩ : syracuseStep 578369 = 433777) B433777
theorem B381763 : Blo 381763 381763 := bstep (se 1 (by rfl) ⟨286322, by rfl⟩ : syracuseStep 381763 = 572645) B572645
theorem B1168195 : Blo 381763 1168195 := bstep (se 1 (by rfl) ⟨876146, by rfl⟩ : syracuseStep 1168195 = 1752293) B1752293
theorem B381779 : Blo 381763 381779 := bstep (se 1 (by rfl) ⟨286334, by rfl⟩ : syracuseStep 381779 = 572669) B572669
theorem B578387 : Blo 381763 578387 := bstep (se 1 (by rfl) ⟨433790, by rfl⟩ : syracuseStep 578387 = 867581) B867581
theorem B381795 : Blo 381763 381795 := bstep (se 1 (by rfl) ⟨286346, by rfl⟩ : syracuseStep 381795 = 572693) B572693
theorem B578417 : Blo 381763 578417 := bstep (se 2 (by rfl) ⟨216906, by rfl⟩ : syracuseStep 578417 = 433813) B433813
theorem B381811 : Blo 381763 381811 := bstep (se 1 (by rfl) ⟨286358, by rfl⟩ : syracuseStep 381811 = 572717) B572717
theorem B381827 : Blo 381763 381827 := bstep (se 1 (by rfl) ⟨286370, by rfl⟩ : syracuseStep 381827 = 572741) B572741
theorem B578435 : Blo 381763 578435 := bstep (se 1 (by rfl) ⟨433826, by rfl⟩ : syracuseStep 578435 = 867653) B867653
theorem B775057 : Blo 381763 775057 := bstep (se 2 (by rfl) ⟨290646, by rfl⟩ : syracuseStep 775057 = 581293) B581293
theorem B381843 : Blo 381763 381843 := bstep (se 1 (by rfl) ⟨286382, by rfl⟩ : syracuseStep 381843 = 572765) B572765
theorem B578465 : Blo 381763 578465 := bstep (se 2 (by rfl) ⟨216924, by rfl⟩ : syracuseStep 578465 = 433849) B433849
theorem B381859 : Blo 381763 381859 := bstep (se 1 (by rfl) ⟨286394, by rfl⟩ : syracuseStep 381859 = 572789) B572789
theorem B381875 : Blo 381763 381875 := bstep (se 1 (by rfl) ⟨286406, by rfl⟩ : syracuseStep 381875 = 572813) B572813
theorem B578483 : Blo 381763 578483 := bstep (se 1 (by rfl) ⟨433862, by rfl⟩ : syracuseStep 578483 = 867725) B867725
theorem B381891 : Blo 381763 381891 := bstep (se 1 (by rfl) ⟨286418, by rfl⟩ : syracuseStep 381891 = 572837) B572837
theorem B578513 : Blo 381763 578513 := bstep (se 2 (by rfl) ⟨216942, by rfl⟩ : syracuseStep 578513 = 433885) B433885
theorem B381907 : Blo 381763 381907 := bstep (se 1 (by rfl) ⟨286430, by rfl⟩ : syracuseStep 381907 = 572861) B572861
theorem B381923 : Blo 381763 381923 := bstep (se 1 (by rfl) ⟨286442, by rfl⟩ : syracuseStep 381923 = 572885) B572885
theorem B971747 : Blo 381763 971747 := bstep (se 1 (by rfl) ⟨728810, by rfl⟩ : syracuseStep 971747 = 1457621) B1457621
theorem B578531 : Blo 381763 578531 := bstep (se 1 (by rfl) ⟨433898, by rfl⟩ : syracuseStep 578531 = 867797) B867797
theorem B381939 : Blo 381763 381939 := bstep (se 1 (by rfl) ⟨286454, by rfl⟩ : syracuseStep 381939 = 572909) B572909
theorem B578561 : Blo 381763 578561 := bstep (se 2 (by rfl) ⟨216960, by rfl⟩ : syracuseStep 578561 = 433921) B433921
theorem B381955 : Blo 381763 381955 := bstep (se 1 (by rfl) ⟨286466, by rfl⟩ : syracuseStep 381955 = 572933) B572933
theorem B381971 : Blo 381763 381971 := bstep (se 1 (by rfl) ⟨286478, by rfl⟩ : syracuseStep 381971 = 572957) B572957
theorem B578579 : Blo 381763 578579 := bstep (se 1 (by rfl) ⟨433934, by rfl⟩ : syracuseStep 578579 = 867869) B867869
theorem B381987 : Blo 381763 381987 := bstep (se 1 (by rfl) ⟨286490, by rfl⟩ : syracuseStep 381987 = 572981) B572981
theorem B578609 : Blo 381763 578609 := bstep (se 2 (by rfl) ⟨216978, by rfl⟩ : syracuseStep 578609 = 433957) B433957
theorem B382003 : Blo 381763 382003 := bstep (se 1 (by rfl) ⟨286502, by rfl⟩ : syracuseStep 382003 = 573005) B573005
theorem B382019 : Blo 381763 382019 := bstep (se 1 (by rfl) ⟨286514, by rfl⟩ : syracuseStep 382019 = 573029) B573029
theorem B775235 : Blo 381763 775235 := bstep (se 1 (by rfl) ⟨581426, by rfl⟩ : syracuseStep 775235 = 1162853) B1162853
theorem B578627 : Blo 381763 578627 := bstep (se 1 (by rfl) ⟨433970, by rfl⟩ : syracuseStep 578627 = 867941) B867941
theorem B382035 : Blo 381763 382035 := bstep (se 1 (by rfl) ⟨286526, by rfl⟩ : syracuseStep 382035 = 573053) B573053
theorem B382051 : Blo 381763 382051 := bstep (se 1 (by rfl) ⟨286538, by rfl⟩ : syracuseStep 382051 = 573077) B573077
theorem B382067 : Blo 381763 382067 := bstep (se 1 (by rfl) ⟨286550, by rfl⟩ : syracuseStep 382067 = 573101) B573101
theorem B382083 : Blo 381763 382083 := bstep (se 1 (by rfl) ⟨286562, by rfl⟩ : syracuseStep 382083 = 573125) B573125
theorem B382099 : Blo 381763 382099 := bstep (se 1 (by rfl) ⟨286574, by rfl⟩ : syracuseStep 382099 = 573149) B573149
theorem B545953 : Blo 381763 545953 := bstep (se 2 (by rfl) ⟨204732, by rfl⟩ : syracuseStep 545953 = 409465) B409465
theorem B382115 : Blo 381763 382115 := bstep (se 1 (by rfl) ⟨286586, by rfl⟩ : syracuseStep 382115 = 573173) B573173
theorem B971939 : Blo 381763 971939 := bstep (se 1 (by rfl) ⟨728954, by rfl⟩ : syracuseStep 971939 = 1457909) B1457909
theorem B382131 : Blo 381763 382131 := bstep (se 1 (by rfl) ⟨286598, by rfl⟩ : syracuseStep 382131 = 573197) B573197
theorem B382147 : Blo 381763 382147 := bstep (se 1 (by rfl) ⟨286610, by rfl⟩ : syracuseStep 382147 = 573221) B573221
theorem B545987 : Blo 381763 545987 := bstep (se 1 (by rfl) ⟨409490, by rfl⟩ : syracuseStep 545987 = 818981) B818981
theorem B382163 : Blo 381763 382163 := bstep (se 1 (by rfl) ⟨286622, by rfl⟩ : syracuseStep 382163 = 573245) B573245
theorem B644321 : Blo 381763 644321 := bstep (se 2 (by rfl) ⟨241620, by rfl⟩ : syracuseStep 644321 = 483241) B483241
theorem B382179 : Blo 381763 382179 := bstep (se 1 (by rfl) ⟨286634, by rfl⟩ : syracuseStep 382179 = 573269) B573269
theorem B382195 : Blo 381763 382195 := bstep (se 1 (by rfl) ⟨286646, by rfl⟩ : syracuseStep 382195 = 573293) B573293
theorem B382211 : Blo 381763 382211 := bstep (se 1 (by rfl) ⟨286658, by rfl⟩ : syracuseStep 382211 = 573317) B573317
theorem B1299725 : Blo 381763 1299725 := bstep (se 3 (by rfl) ⟨243698, by rfl⟩ : syracuseStep 1299725 = 487397) B487397
theorem B382227 : Blo 381763 382227 := bstep (se 1 (by rfl) ⟨286670, by rfl⟩ : syracuseStep 382227 = 573341) B573341
theorem B382243 : Blo 381763 382243 := bstep (se 1 (by rfl) ⟨286682, by rfl⟩ : syracuseStep 382243 = 573365) B573365
theorem B382259 : Blo 381763 382259 := bstep (se 1 (by rfl) ⟨286694, by rfl⟩ : syracuseStep 382259 = 573389) B573389
theorem B382275 : Blo 381763 382275 := bstep (se 1 (by rfl) ⟨286706, by rfl⟩ : syracuseStep 382275 = 573413) B573413
theorem B1299779 : Blo 381763 1299779 := bstep (se 1 (by rfl) ⟨974834, by rfl⟩ : syracuseStep 1299779 = 1949669) B1949669
theorem B382291 : Blo 381763 382291 := bstep (se 1 (by rfl) ⟨286718, by rfl⟩ : syracuseStep 382291 = 573437) B573437
theorem B644449 : Blo 381763 644449 := bstep (se 2 (by rfl) ⟨241668, by rfl⟩ : syracuseStep 644449 = 483337) B483337
theorem B382307 : Blo 381763 382307 := bstep (se 1 (by rfl) ⟨286730, by rfl⟩ : syracuseStep 382307 = 573461) B573461
theorem B382323 : Blo 381763 382323 := bstep (se 1 (by rfl) ⟨286742, by rfl⟩ : syracuseStep 382323 = 573485) B573485
theorem B644483 : Blo 381763 644483 := bstep (se 1 (by rfl) ⟨483362, by rfl⟩ : syracuseStep 644483 = 966725) B966725
theorem B382339 : Blo 381763 382339 := bstep (se 1 (by rfl) ⟨286754, by rfl⟩ : syracuseStep 382339 = 573509) B573509
theorem B382355 : Blo 381763 382355 := bstep (se 1 (by rfl) ⟨286766, by rfl⟩ : syracuseStep 382355 = 573533) B573533
theorem B382371 : Blo 381763 382371 := bstep (se 1 (by rfl) ⟨286778, by rfl⟩ : syracuseStep 382371 = 573557) B573557
theorem B1168813 : Blo 381763 1168813 := bstep (se 3 (by rfl) ⟨219152, by rfl⟩ : syracuseStep 1168813 = 438305) B438305
theorem B382387 : Blo 381763 382387 := bstep (se 1 (by rfl) ⟨286790, by rfl⟩ : syracuseStep 382387 = 573581) B573581
theorem B382403 : Blo 381763 382403 := bstep (se 1 (by rfl) ⟨286802, by rfl⟩ : syracuseStep 382403 = 573605) B573605
theorem B382419 : Blo 381763 382419 := bstep (se 1 (by rfl) ⟨286814, by rfl⟩ : syracuseStep 382419 = 573629) B573629
theorem B382435 : Blo 381763 382435 := bstep (se 1 (by rfl) ⟨286826, by rfl⟩ : syracuseStep 382435 = 573653) B573653
theorem B382451 : Blo 381763 382451 := bstep (se 1 (by rfl) ⟨286838, by rfl⟩ : syracuseStep 382451 = 573677) B573677
theorem B644611 : Blo 381763 644611 := bstep (se 1 (by rfl) ⟨483458, by rfl⟩ : syracuseStep 644611 = 966917) B966917
theorem B382467 : Blo 381763 382467 := bstep (se 1 (by rfl) ⟨286850, by rfl⟩ : syracuseStep 382467 = 573701) B573701
theorem B382483 : Blo 381763 382483 := bstep (se 1 (by rfl) ⟨286862, by rfl⟩ : syracuseStep 382483 = 573725) B573725
theorem B382499 : Blo 381763 382499 := bstep (se 1 (by rfl) ⟨286874, by rfl⟩ : syracuseStep 382499 = 573749) B573749
theorem B611891 : Blo 381763 611891 := bstep (se 1 (by rfl) ⟨458918, by rfl⟩ : syracuseStep 611891 = 917837) B917837
theorem B382515 : Blo 381763 382515 := bstep (se 1 (by rfl) ⟨286886, by rfl⟩ : syracuseStep 382515 = 573773) B573773
theorem B382531 : Blo 381763 382531 := bstep (se 1 (by rfl) ⟨286898, by rfl⟩ : syracuseStep 382531 = 573797) B573797
theorem B3692101 : Blo 381763 3692101 := bstep (se 4 (by rfl) ⟨346134, by rfl⟩ : syracuseStep 3692101 = 692269) B692269
theorem B1300049 : Blo 381763 1300049 := bstep (se 2 (by rfl) ⟨487518, by rfl⟩ : syracuseStep 1300049 = 975037) B975037
theorem B382547 : Blo 381763 382547 := bstep (se 1 (by rfl) ⟨286910, by rfl⟩ : syracuseStep 382547 = 573821) B573821
theorem B382563 : Blo 381763 382563 := bstep (se 1 (by rfl) ⟨286922, by rfl⟩ : syracuseStep 382563 = 573845) B573845
theorem B382579 : Blo 381763 382579 := bstep (se 1 (by rfl) ⟨286934, by rfl⟩ : syracuseStep 382579 = 573869) B573869
theorem B382595 : Blo 381763 382595 := bstep (se 1 (by rfl) ⟨286946, by rfl⟩ : syracuseStep 382595 = 573893) B573893
theorem B644753 : Blo 381763 644753 := bstep (se 2 (by rfl) ⟨241782, by rfl⟩ : syracuseStep 644753 = 483565) B483565
theorem B382611 : Blo 381763 382611 := bstep (se 1 (by rfl) ⟨286958, by rfl⟩ : syracuseStep 382611 = 573917) B573917
theorem B382627 : Blo 381763 382627 := bstep (se 1 (by rfl) ⟨286970, by rfl⟩ : syracuseStep 382627 = 573941) B573941
theorem B382643 : Blo 381763 382643 := bstep (se 1 (by rfl) ⟨286982, by rfl⟩ : syracuseStep 382643 = 573965) B573965
theorem B382659 : Blo 381763 382659 := bstep (se 1 (by rfl) ⟨286994, by rfl⟩ : syracuseStep 382659 = 573989) B573989
theorem B382675 : Blo 381763 382675 := bstep (se 1 (by rfl) ⟨287006, by rfl⟩ : syracuseStep 382675 = 574013) B574013
theorem B382691 : Blo 381763 382691 := bstep (se 1 (by rfl) ⟨287018, by rfl⟩ : syracuseStep 382691 = 574037) B574037
theorem B546545 : Blo 381763 546545 := bstep (se 2 (by rfl) ⟨204954, by rfl⟩ : syracuseStep 546545 = 409909) B409909
theorem B612083 : Blo 381763 612083 := bstep (se 1 (by rfl) ⟨459062, by rfl⟩ : syracuseStep 612083 = 918125) B918125
theorem B382707 : Blo 381763 382707 := bstep (se 1 (by rfl) ⟨287030, by rfl⟩ : syracuseStep 382707 = 574061) B574061
theorem B382723 : Blo 381763 382723 := bstep (se 1 (by rfl) ⟨287042, by rfl⟩ : syracuseStep 382723 = 574085) B574085
theorem B644881 : Blo 381763 644881 := bstep (se 2 (by rfl) ⟨241830, by rfl⟩ : syracuseStep 644881 = 483661) B483661
theorem B382739 : Blo 381763 382739 := bstep (se 1 (by rfl) ⟨287054, by rfl⟩ : syracuseStep 382739 = 574109) B574109
theorem B382755 : Blo 381763 382755 := bstep (se 1 (by rfl) ⟨287066, by rfl⟩ : syracuseStep 382755 = 574133) B574133
theorem B2184995 : Blo 381763 2184995 := bstep (se 1 (by rfl) ⟨1638746, by rfl⟩ : syracuseStep 2184995 = 3277493) B3277493
theorem B644915 : Blo 381763 644915 := bstep (se 1 (by rfl) ⟨483686, by rfl⟩ : syracuseStep 644915 = 967373) B967373
theorem B382771 : Blo 381763 382771 := bstep (se 1 (by rfl) ⟨287078, by rfl⟩ : syracuseStep 382771 = 574157) B574157
theorem B546625 : Blo 381763 546625 := bstep (se 2 (by rfl) ⟨204984, by rfl⟩ : syracuseStep 546625 = 409969) B409969
theorem B382787 : Blo 381763 382787 := bstep (se 1 (by rfl) ⟨287090, by rfl⟩ : syracuseStep 382787 = 574181) B574181
theorem B382803 : Blo 381763 382803 := bstep (se 1 (by rfl) ⟨287102, by rfl⟩ : syracuseStep 382803 = 574205) B574205
theorem B382819 : Blo 381763 382819 := bstep (se 1 (by rfl) ⟨287114, by rfl⟩ : syracuseStep 382819 = 574229) B574229
theorem B1234801 : Blo 381763 1234801 := bstep (se 2 (by rfl) ⟨463050, by rfl⟩ : syracuseStep 1234801 = 926101) B926101
theorem B382835 : Blo 381763 382835 := bstep (se 1 (by rfl) ⟨287126, by rfl⟩ : syracuseStep 382835 = 574253) B574253
theorem B382851 : Blo 381763 382851 := bstep (se 1 (by rfl) ⟨287138, by rfl⟩ : syracuseStep 382851 = 574277) B574277
theorem B382867 : Blo 381763 382867 := bstep (se 1 (by rfl) ⟨287150, by rfl⟩ : syracuseStep 382867 = 574301) B574301
theorem B382883 : Blo 381763 382883 := bstep (se 1 (by rfl) ⟨287162, by rfl⟩ : syracuseStep 382883 = 574325) B574325
theorem B1464227 : Blo 381763 1464227 := bstep (se 1 (by rfl) ⟨1098170, by rfl⟩ : syracuseStep 1464227 = 2196341) B2196341
theorem B1038253 : Blo 381763 1038253 := bstep (se 3 (by rfl) ⟨194672, by rfl⟩ : syracuseStep 1038253 = 389345) B389345
theorem B645043 : Blo 381763 645043 := bstep (se 1 (by rfl) ⟨483782, by rfl⟩ : syracuseStep 645043 = 967565) B967565
theorem B382899 : Blo 381763 382899 := bstep (se 1 (by rfl) ⟨287174, by rfl⟩ : syracuseStep 382899 = 574349) B574349
theorem B382915 : Blo 381763 382915 := bstep (se 1 (by rfl) ⟨287186, by rfl⟩ : syracuseStep 382915 = 574373) B574373
theorem B1038275 : Blo 381763 1038275 := bstep (se 1 (by rfl) ⟨778706, by rfl⟩ : syracuseStep 1038275 = 1557413) B1557413
theorem B382931 : Blo 381763 382931 := bstep (se 1 (by rfl) ⟨287198, by rfl⟩ : syracuseStep 382931 = 574397) B574397
theorem B382947 : Blo 381763 382947 := bstep (se 1 (by rfl) ⟨287210, by rfl⟩ : syracuseStep 382947 = 574421) B574421
theorem B1038317 : Blo 381763 1038317 := bstep (se 3 (by rfl) ⟨194684, by rfl⟩ : syracuseStep 1038317 = 389369) B389369
theorem B382963 : Blo 381763 382963 := bstep (se 1 (by rfl) ⟨287222, by rfl⟩ : syracuseStep 382963 = 574445) B574445
theorem B382979 : Blo 381763 382979 := bstep (se 1 (by rfl) ⟨287234, by rfl⟩ : syracuseStep 382979 = 574469) B574469
theorem B382995 : Blo 381763 382995 := bstep (se 1 (by rfl) ⟨287246, by rfl⟩ : syracuseStep 382995 = 574493) B574493
theorem B383011 : Blo 381763 383011 := bstep (se 1 (by rfl) ⟨287258, by rfl⟩ : syracuseStep 383011 = 574517) B574517
theorem B383027 : Blo 381763 383027 := bstep (se 1 (by rfl) ⟨287270, by rfl⟩ : syracuseStep 383027 = 574541) B574541
theorem B645185 : Blo 381763 645185 := bstep (se 2 (by rfl) ⟨241944, by rfl⟩ : syracuseStep 645185 = 483889) B483889
theorem B383043 : Blo 381763 383043 := bstep (se 1 (by rfl) ⟨287282, by rfl⟩ : syracuseStep 383043 = 574565) B574565
theorem B972881 : Blo 381763 972881 := bstep (se 2 (by rfl) ⟨364830, by rfl⟩ : syracuseStep 972881 = 729661) B729661
theorem B383059 : Blo 381763 383059 := bstep (se 1 (by rfl) ⟨287294, by rfl⟩ : syracuseStep 383059 = 574589) B574589
theorem B2447459 : Blo 381763 2447459 := bstep (se 1 (by rfl) ⟨1835594, by rfl⟩ : syracuseStep 2447459 = 3671189) B3671189
theorem B383075 : Blo 381763 383075 := bstep (se 1 (by rfl) ⟨287306, by rfl⟩ : syracuseStep 383075 = 574613) B574613
theorem B1300589 : Blo 381763 1300589 := bstep (se 3 (by rfl) ⟨243860, by rfl⟩ : syracuseStep 1300589 = 487721) B487721
theorem B383091 : Blo 381763 383091 := bstep (se 1 (by rfl) ⟨287318, by rfl⟩ : syracuseStep 383091 = 574637) B574637
theorem B383107 : Blo 381763 383107 := bstep (se 1 (by rfl) ⟨287330, by rfl⟩ : syracuseStep 383107 = 574661) B574661
theorem B972931 : Blo 381763 972931 := bstep (se 1 (by rfl) ⟨729698, by rfl⟩ : syracuseStep 972931 = 1459397) B1459397
theorem B383123 : Blo 381763 383123 := bstep (se 1 (by rfl) ⟨287342, by rfl⟩ : syracuseStep 383123 = 574685) B574685
theorem B383139 : Blo 381763 383139 := bstep (se 1 (by rfl) ⟨287354, by rfl⟩ : syracuseStep 383139 = 574709) B574709
theorem B1300643 : Blo 381763 1300643 := bstep (se 1 (by rfl) ⟨975482, by rfl⟩ : syracuseStep 1300643 = 1950965) B1950965
theorem B383155 : Blo 381763 383155 := bstep (se 1 (by rfl) ⟨287366, by rfl⟩ : syracuseStep 383155 = 574733) B574733
theorem B645313 : Blo 381763 645313 := bstep (se 2 (by rfl) ⟨241992, by rfl⟩ : syracuseStep 645313 = 483985) B483985
theorem B383171 : Blo 381763 383171 := bstep (se 1 (by rfl) ⟨287378, by rfl⟩ : syracuseStep 383171 = 574757) B574757
theorem B383187 : Blo 381763 383187 := bstep (se 1 (by rfl) ⟨287390, by rfl⟩ : syracuseStep 383187 = 574781) B574781
theorem B645347 : Blo 381763 645347 := bstep (se 1 (by rfl) ⟨484010, by rfl⟩ : syracuseStep 645347 = 968021) B968021
theorem B383203 : Blo 381763 383203 := bstep (se 1 (by rfl) ⟨287402, by rfl⟩ : syracuseStep 383203 = 574805) B574805
theorem B383219 : Blo 381763 383219 := bstep (se 1 (by rfl) ⟨287414, by rfl⟩ : syracuseStep 383219 = 574829) B574829
theorem B383235 : Blo 381763 383235 := bstep (se 1 (by rfl) ⟨287426, by rfl⟩ : syracuseStep 383235 = 574853) B574853
theorem B973073 : Blo 381763 973073 := bstep (se 2 (by rfl) ⟨364902, by rfl⟩ : syracuseStep 973073 = 729805) B729805
theorem B383251 : Blo 381763 383251 := bstep (se 1 (by rfl) ⟨287438, by rfl⟩ : syracuseStep 383251 = 574877) B574877
theorem B383267 : Blo 381763 383267 := bstep (se 1 (by rfl) ⟨287450, by rfl⟩ : syracuseStep 383267 = 574901) B574901
theorem B383283 : Blo 381763 383283 := bstep (se 1 (by rfl) ⟨287462, by rfl⟩ : syracuseStep 383283 = 574925) B574925
theorem B383299 : Blo 381763 383299 := bstep (se 1 (by rfl) ⟨287474, by rfl⟩ : syracuseStep 383299 = 574949) B574949
theorem B383315 : Blo 381763 383315 := bstep (se 1 (by rfl) ⟨287486, by rfl⟩ : syracuseStep 383315 = 574973) B574973
theorem B645475 : Blo 381763 645475 := bstep (se 1 (by rfl) ⟨484106, by rfl⟩ : syracuseStep 645475 = 968213) B968213
theorem B383331 : Blo 381763 383331 := bstep (se 1 (by rfl) ⟨287498, by rfl⟩ : syracuseStep 383331 = 574997) B574997
theorem B383347 : Blo 381763 383347 := bstep (se 1 (by rfl) ⟨287510, by rfl⟩ : syracuseStep 383347 = 575021) B575021
theorem B383363 : Blo 381763 383363 := bstep (se 1 (by rfl) ⟨287522, by rfl⟩ : syracuseStep 383363 = 575045) B575045
theorem B383379 : Blo 381763 383379 := bstep (se 1 (by rfl) ⟨287534, by rfl⟩ : syracuseStep 383379 = 575069) B575069
theorem B383395 : Blo 381763 383395 := bstep (se 1 (by rfl) ⟨287546, by rfl⟩ : syracuseStep 383395 = 575093) B575093
theorem B1300913 : Blo 381763 1300913 := bstep (se 2 (by rfl) ⟨487842, by rfl⟩ : syracuseStep 1300913 = 975685) B975685
theorem B383411 : Blo 381763 383411 := bstep (se 1 (by rfl) ⟨287558, by rfl⟩ : syracuseStep 383411 = 575117) B575117
theorem B383427 : Blo 381763 383427 := bstep (se 1 (by rfl) ⟨287570, by rfl⟩ : syracuseStep 383427 = 575141) B575141
theorem B1235405 : Blo 381763 1235405 := bstep (se 3 (by rfl) ⟨231638, by rfl⟩ : syracuseStep 1235405 = 463277) B463277
theorem B383443 : Blo 381763 383443 := bstep (se 1 (by rfl) ⟨287582, by rfl⟩ : syracuseStep 383443 = 575165) B575165
theorem B383459 : Blo 381763 383459 := bstep (se 1 (by rfl) ⟨287594, by rfl⟩ : syracuseStep 383459 = 575189) B575189
theorem B645617 : Blo 381763 645617 := bstep (se 2 (by rfl) ⟨242106, by rfl⟩ : syracuseStep 645617 = 484213) B484213
theorem B383475 : Blo 381763 383475 := bstep (se 1 (by rfl) ⟨287606, by rfl⟩ : syracuseStep 383475 = 575213) B575213
theorem B383491 : Blo 381763 383491 := bstep (se 1 (by rfl) ⟨287618, by rfl⟩ : syracuseStep 383491 = 575237) B575237
theorem B383507 : Blo 381763 383507 := bstep (se 1 (by rfl) ⟨287630, by rfl⟩ : syracuseStep 383507 = 575261) B575261
theorem B383523 : Blo 381763 383523 := bstep (se 1 (by rfl) ⟨287642, by rfl⟩ : syracuseStep 383523 = 575285) B575285
theorem B2447921 : Blo 381763 2447921 := bstep (se 2 (by rfl) ⟨917970, by rfl⟩ : syracuseStep 2447921 = 1835941) B1835941
theorem B383539 : Blo 381763 383539 := bstep (se 1 (by rfl) ⟨287654, by rfl⟩ : syracuseStep 383539 = 575309) B575309
theorem B383555 : Blo 381763 383555 := bstep (se 1 (by rfl) ⟨287666, by rfl⟩ : syracuseStep 383555 = 575333) B575333
theorem B383571 : Blo 381763 383571 := bstep (se 1 (by rfl) ⟨287678, by rfl⟩ : syracuseStep 383571 = 575357) B575357
theorem B547411 : Blo 381763 547411 := bstep (se 1 (by rfl) ⟨410558, by rfl⟩ : syracuseStep 547411 = 821117) B821117
theorem B383587 : Blo 381763 383587 := bstep (se 1 (by rfl) ⟨287690, by rfl⟩ : syracuseStep 383587 = 575381) B575381
theorem B645745 : Blo 381763 645745 := bstep (se 2 (by rfl) ⟨242154, by rfl⟩ : syracuseStep 645745 = 484309) B484309
theorem B383603 : Blo 381763 383603 := bstep (se 1 (by rfl) ⟨287702, by rfl⟩ : syracuseStep 383603 = 575405) B575405
theorem B383619 : Blo 381763 383619 := bstep (se 1 (by rfl) ⟨287714, by rfl⟩ : syracuseStep 383619 = 575429) B575429
theorem B2906765 : Blo 381763 2906765 := bstep (se 3 (by rfl) ⟨545018, by rfl⟩ : syracuseStep 2906765 = 1090037) B1090037
theorem B645779 : Blo 381763 645779 := bstep (se 1 (by rfl) ⟨484334, by rfl⟩ : syracuseStep 645779 = 968669) B968669
theorem B383635 : Blo 381763 383635 := bstep (se 1 (by rfl) ⟨287726, by rfl⟩ : syracuseStep 383635 = 575453) B575453
theorem B383651 : Blo 381763 383651 := bstep (se 1 (by rfl) ⟨287738, by rfl⟩ : syracuseStep 383651 = 575477) B575477
theorem B383667 : Blo 381763 383667 := bstep (se 1 (by rfl) ⟨287750, by rfl⟩ : syracuseStep 383667 = 575501) B575501
theorem B383683 : Blo 381763 383683 := bstep (se 1 (by rfl) ⟨287762, by rfl⟩ : syracuseStep 383683 = 575525) B575525
theorem B383699 : Blo 381763 383699 := bstep (se 1 (by rfl) ⟨287774, by rfl⟩ : syracuseStep 383699 = 575549) B575549
theorem B383715 : Blo 381763 383715 := bstep (se 1 (by rfl) ⟨287786, by rfl⟩ : syracuseStep 383715 = 575573) B575573
theorem B383731 : Blo 381763 383731 := bstep (se 1 (by rfl) ⟨287798, by rfl⟩ : syracuseStep 383731 = 575597) B575597
theorem B383747 : Blo 381763 383747 := bstep (se 1 (by rfl) ⟨287810, by rfl⟩ : syracuseStep 383747 = 575621) B575621
theorem B645907 : Blo 381763 645907 := bstep (se 1 (by rfl) ⟨484430, by rfl⟩ : syracuseStep 645907 = 968861) B968861
theorem B383763 : Blo 381763 383763 := bstep (se 1 (by rfl) ⟨287822, by rfl⟩ : syracuseStep 383763 = 575645) B575645
theorem B383779 : Blo 381763 383779 := bstep (se 1 (by rfl) ⟨287834, by rfl⟩ : syracuseStep 383779 = 575669) B575669
theorem B383795 : Blo 381763 383795 := bstep (se 1 (by rfl) ⟨287846, by rfl⟩ : syracuseStep 383795 = 575693) B575693
theorem B383811 : Blo 381763 383811 := bstep (se 1 (by rfl) ⟨287858, by rfl⟩ : syracuseStep 383811 = 575717) B575717
theorem B383827 : Blo 381763 383827 := bstep (se 1 (by rfl) ⟨287870, by rfl⟩ : syracuseStep 383827 = 575741) B575741
theorem B383843 : Blo 381763 383843 := bstep (se 1 (by rfl) ⟨287882, by rfl⟩ : syracuseStep 383843 = 575765) B575765
theorem B383859 : Blo 381763 383859 := bstep (se 1 (by rfl) ⟨287894, by rfl⟩ : syracuseStep 383859 = 575789) B575789
theorem B383875 : Blo 381763 383875 := bstep (se 1 (by rfl) ⟨287906, by rfl⟩ : syracuseStep 383875 = 575813) B575813
theorem B383891 : Blo 381763 383891 := bstep (se 1 (by rfl) ⟨287918, by rfl⟩ : syracuseStep 383891 = 575837) B575837
theorem B646049 : Blo 381763 646049 := bstep (se 2 (by rfl) ⟨242268, by rfl⟩ : syracuseStep 646049 = 484537) B484537
theorem B383907 : Blo 381763 383907 := bstep (se 1 (by rfl) ⟨287930, by rfl⟩ : syracuseStep 383907 = 575861) B575861
theorem B383923 : Blo 381763 383923 := bstep (se 1 (by rfl) ⟨287942, by rfl⟩ : syracuseStep 383923 = 575885) B575885
theorem B383939 : Blo 381763 383939 := bstep (se 1 (by rfl) ⟨287954, by rfl⟩ : syracuseStep 383939 = 575909) B575909
theorem B1301453 : Blo 381763 1301453 := bstep (se 3 (by rfl) ⟨244022, by rfl⟩ : syracuseStep 1301453 = 488045) B488045
theorem B1039313 : Blo 381763 1039313 := bstep (se 2 (by rfl) ⟨389742, by rfl⟩ : syracuseStep 1039313 = 779485) B779485
theorem B383955 : Blo 381763 383955 := bstep (se 1 (by rfl) ⟨287966, by rfl⟩ : syracuseStep 383955 = 575933) B575933
theorem B383971 : Blo 381763 383971 := bstep (se 1 (by rfl) ⟨287978, by rfl⟩ : syracuseStep 383971 = 575957) B575957
theorem B383987 : Blo 381763 383987 := bstep (se 1 (by rfl) ⟨287990, by rfl⟩ : syracuseStep 383987 = 575981) B575981
theorem B384003 : Blo 381763 384003 := bstep (se 1 (by rfl) ⟨288002, by rfl⟩ : syracuseStep 384003 = 576005) B576005
theorem B1301507 : Blo 381763 1301507 := bstep (se 1 (by rfl) ⟨976130, by rfl⟩ : syracuseStep 1301507 = 1952261) B1952261
theorem B384019 : Blo 381763 384019 := bstep (se 1 (by rfl) ⟨288014, by rfl⟩ : syracuseStep 384019 = 576029) B576029
theorem B646177 : Blo 381763 646177 := bstep (se 2 (by rfl) ⟨242316, by rfl⟩ : syracuseStep 646177 = 484633) B484633
theorem B384035 : Blo 381763 384035 := bstep (se 1 (by rfl) ⟨288026, by rfl⟩ : syracuseStep 384035 = 576053) B576053
theorem B547889 : Blo 381763 547889 := bstep (se 2 (by rfl) ⟨205458, by rfl⟩ : syracuseStep 547889 = 410917) B410917
theorem B384051 : Blo 381763 384051 := bstep (se 1 (by rfl) ⟨288038, by rfl⟩ : syracuseStep 384051 = 576077) B576077
theorem B646211 : Blo 381763 646211 := bstep (se 1 (by rfl) ⟨484658, by rfl⟩ : syracuseStep 646211 = 969317) B969317
theorem B384067 : Blo 381763 384067 := bstep (se 1 (by rfl) ⟨288050, by rfl⟩ : syracuseStep 384067 = 576101) B576101
theorem B384083 : Blo 381763 384083 := bstep (se 1 (by rfl) ⟨288062, by rfl⟩ : syracuseStep 384083 = 576125) B576125
theorem B384099 : Blo 381763 384099 := bstep (se 1 (by rfl) ⟨288074, by rfl⟩ : syracuseStep 384099 = 576149) B576149
theorem B1170541 : Blo 381763 1170541 := bstep (se 3 (by rfl) ⟨219476, by rfl⟩ : syracuseStep 1170541 = 438953) B438953
theorem B384115 : Blo 381763 384115 := bstep (se 1 (by rfl) ⟨288086, by rfl⟩ : syracuseStep 384115 = 576173) B576173
theorem B613505 : Blo 381763 613505 := bstep (se 2 (by rfl) ⟨230064, by rfl⟩ : syracuseStep 613505 = 460129) B460129
theorem B384131 : Blo 381763 384131 := bstep (se 1 (by rfl) ⟨288098, by rfl⟩ : syracuseStep 384131 = 576197) B576197
theorem B384147 : Blo 381763 384147 := bstep (se 1 (by rfl) ⟨288110, by rfl⟩ : syracuseStep 384147 = 576221) B576221
theorem B384163 : Blo 381763 384163 := bstep (se 1 (by rfl) ⟨288122, by rfl⟩ : syracuseStep 384163 = 576245) B576245
theorem B548003 : Blo 381763 548003 := bstep (se 1 (by rfl) ⟨411002, by rfl⟩ : syracuseStep 548003 = 822005) B822005
theorem B384179 : Blo 381763 384179 := bstep (se 1 (by rfl) ⟨288134, by rfl⟩ : syracuseStep 384179 = 576269) B576269
theorem B646339 : Blo 381763 646339 := bstep (se 1 (by rfl) ⟨484754, by rfl⟩ : syracuseStep 646339 = 969509) B969509
theorem B384195 : Blo 381763 384195 := bstep (se 1 (by rfl) ⟨288146, by rfl⟩ : syracuseStep 384195 = 576293) B576293
theorem B384211 : Blo 381763 384211 := bstep (se 1 (by rfl) ⟨288158, by rfl⟩ : syracuseStep 384211 = 576317) B576317
theorem B384227 : Blo 381763 384227 := bstep (se 1 (by rfl) ⟨288170, by rfl⟩ : syracuseStep 384227 = 576341) B576341
theorem B974065 : Blo 381763 974065 := bstep (se 2 (by rfl) ⟨365274, by rfl⟩ : syracuseStep 974065 = 730549) B730549
theorem B384243 : Blo 381763 384243 := bstep (se 1 (by rfl) ⟨288182, by rfl⟩ : syracuseStep 384243 = 576365) B576365
theorem B548083 : Blo 381763 548083 := bstep (se 1 (by rfl) ⟨411062, by rfl⟩ : syracuseStep 548083 = 822125) B822125
theorem B384259 : Blo 381763 384259 := bstep (se 1 (by rfl) ⟨288194, by rfl⟩ : syracuseStep 384259 = 576389) B576389
theorem B1301777 : Blo 381763 1301777 := bstep (se 2 (by rfl) ⟨488166, by rfl⟩ : syracuseStep 1301777 = 976333) B976333
theorem B384275 : Blo 381763 384275 := bstep (se 1 (by rfl) ⟨288206, by rfl⟩ : syracuseStep 384275 = 576413) B576413
theorem B384291 : Blo 381763 384291 := bstep (se 1 (by rfl) ⟨288218, by rfl⟩ : syracuseStep 384291 = 576437) B576437
theorem B384307 : Blo 381763 384307 := bstep (se 1 (by rfl) ⟨288230, by rfl⟩ : syracuseStep 384307 = 576461) B576461
theorem B777539 : Blo 381763 777539 := bstep (se 1 (by rfl) ⟨583154, by rfl⟩ : syracuseStep 777539 = 1166309) B1166309
theorem B384323 : Blo 381763 384323 := bstep (se 1 (by rfl) ⟨288242, by rfl⟩ : syracuseStep 384323 = 576485) B576485
theorem B646481 : Blo 381763 646481 := bstep (se 2 (by rfl) ⟨242430, by rfl⟩ : syracuseStep 646481 = 484861) B484861
theorem B384339 : Blo 381763 384339 := bstep (se 1 (by rfl) ⟨288254, by rfl⟩ : syracuseStep 384339 = 576509) B576509
theorem B384355 : Blo 381763 384355 := bstep (se 1 (by rfl) ⟨288266, by rfl⟩ : syracuseStep 384355 = 576533) B576533
theorem B384371 : Blo 381763 384371 := bstep (se 1 (by rfl) ⟨288278, by rfl⟩ : syracuseStep 384371 = 576557) B576557
theorem B384387 : Blo 381763 384387 := bstep (se 1 (by rfl) ⟨288290, by rfl⟩ : syracuseStep 384387 = 576581) B576581
theorem B384403 : Blo 381763 384403 := bstep (se 1 (by rfl) ⟨288302, by rfl⟩ : syracuseStep 384403 = 576605) B576605
theorem B384419 : Blo 381763 384419 := bstep (se 1 (by rfl) ⟨288314, by rfl⟩ : syracuseStep 384419 = 576629) B576629
theorem B384435 : Blo 381763 384435 := bstep (se 1 (by rfl) ⟨288326, by rfl⟩ : syracuseStep 384435 = 576653) B576653
theorem B384451 : Blo 381763 384451 := bstep (se 1 (by rfl) ⟨288338, by rfl⟩ : syracuseStep 384451 = 576677) B576677
theorem B646609 : Blo 381763 646609 := bstep (se 2 (by rfl) ⟨242478, by rfl⟩ : syracuseStep 646609 = 484957) B484957
theorem B384467 : Blo 381763 384467 := bstep (se 1 (by rfl) ⟨288350, by rfl⟩ : syracuseStep 384467 = 576701) B576701
theorem B384483 : Blo 381763 384483 := bstep (se 1 (by rfl) ⟨288362, by rfl⟩ : syracuseStep 384483 = 576725) B576725
theorem B646643 : Blo 381763 646643 := bstep (se 1 (by rfl) ⟨484982, by rfl⟩ : syracuseStep 646643 = 969965) B969965
theorem B384499 : Blo 381763 384499 := bstep (se 1 (by rfl) ⟨288374, by rfl⟩ : syracuseStep 384499 = 576749) B576749
theorem B384515 : Blo 381763 384515 := bstep (se 1 (by rfl) ⟨288386, by rfl⟩ : syracuseStep 384515 = 576773) B576773
theorem B974339 : Blo 381763 974339 := bstep (se 1 (by rfl) ⟨730754, by rfl⟩ : syracuseStep 974339 = 1461509) B1461509
theorem B384531 : Blo 381763 384531 := bstep (se 1 (by rfl) ⟨288398, by rfl⟩ : syracuseStep 384531 = 576797) B576797
theorem B384547 : Blo 381763 384547 := bstep (se 1 (by rfl) ⟨288410, by rfl⟩ : syracuseStep 384547 = 576821) B576821
theorem B384563 : Blo 381763 384563 := bstep (se 1 (by rfl) ⟨288422, by rfl⟩ : syracuseStep 384563 = 576845) B576845
theorem B384579 : Blo 381763 384579 := bstep (se 1 (by rfl) ⟨288434, by rfl⟩ : syracuseStep 384579 = 576869) B576869
theorem B1826381 : Blo 381763 1826381 := bstep (se 3 (by rfl) ⟨342446, by rfl⟩ : syracuseStep 1826381 = 684893) B684893
theorem B384595 : Blo 381763 384595 := bstep (se 1 (by rfl) ⟨288446, by rfl⟩ : syracuseStep 384595 = 576893) B576893
theorem B384611 : Blo 381763 384611 := bstep (se 1 (by rfl) ⟨288458, by rfl⟩ : syracuseStep 384611 = 576917) B576917
theorem B646771 : Blo 381763 646771 := bstep (se 1 (by rfl) ⟨485078, by rfl⟩ : syracuseStep 646771 = 970157) B970157
theorem B384627 : Blo 381763 384627 := bstep (se 1 (by rfl) ⟨288470, by rfl⟩ : syracuseStep 384627 = 576941) B576941
theorem B384643 : Blo 381763 384643 := bstep (se 1 (by rfl) ⟨288482, by rfl⟩ : syracuseStep 384643 = 576965) B576965
theorem B384659 : Blo 381763 384659 := bstep (se 1 (by rfl) ⟨288494, by rfl⟩ : syracuseStep 384659 = 576989) B576989
theorem B384675 : Blo 381763 384675 := bstep (se 1 (by rfl) ⟨288506, by rfl⟩ : syracuseStep 384675 = 577013) B577013
theorem B384691 : Blo 381763 384691 := bstep (se 1 (by rfl) ⟨288518, by rfl⟩ : syracuseStep 384691 = 577037) B577037
theorem B384707 : Blo 381763 384707 := bstep (se 1 (by rfl) ⟨288530, by rfl⟩ : syracuseStep 384707 = 577061) B577061
theorem B974531 : Blo 381763 974531 := bstep (se 1 (by rfl) ⟨730898, by rfl⟩ : syracuseStep 974531 = 1461797) B1461797
theorem B384723 : Blo 381763 384723 := bstep (se 1 (by rfl) ⟨288542, by rfl⟩ : syracuseStep 384723 = 577085) B577085
theorem B384739 : Blo 381763 384739 := bstep (se 1 (by rfl) ⟨288554, by rfl⟩ : syracuseStep 384739 = 577109) B577109
theorem B384755 : Blo 381763 384755 := bstep (se 1 (by rfl) ⟨288566, by rfl⟩ : syracuseStep 384755 = 577133) B577133
theorem B646913 : Blo 381763 646913 := bstep (se 2 (by rfl) ⟨242592, by rfl⟩ : syracuseStep 646913 = 485185) B485185
theorem B384771 : Blo 381763 384771 := bstep (se 1 (by rfl) ⟨288578, by rfl⟩ : syracuseStep 384771 = 577157) B577157
theorem B384787 : Blo 381763 384787 := bstep (se 1 (by rfl) ⟨288590, by rfl⟩ : syracuseStep 384787 = 577181) B577181
theorem B548641 : Blo 381763 548641 := bstep (se 2 (by rfl) ⟨205740, by rfl⟩ : syracuseStep 548641 = 411481) B411481
theorem B384803 : Blo 381763 384803 := bstep (se 1 (by rfl) ⟨288602, by rfl⟩ : syracuseStep 384803 = 577205) B577205
theorem B384819 : Blo 381763 384819 := bstep (se 1 (by rfl) ⟨288614, by rfl⟩ : syracuseStep 384819 = 577229) B577229
theorem B384835 : Blo 381763 384835 := bstep (se 1 (by rfl) ⟨288626, by rfl⟩ : syracuseStep 384835 = 577253) B577253
theorem B384851 : Blo 381763 384851 := bstep (se 1 (by rfl) ⟨288638, by rfl⟩ : syracuseStep 384851 = 577277) B577277
theorem B384867 : Blo 381763 384867 := bstep (se 1 (by rfl) ⟨288650, by rfl⟩ : syracuseStep 384867 = 577301) B577301
theorem B384883 : Blo 381763 384883 := bstep (se 1 (by rfl) ⟨288662, by rfl⟩ : syracuseStep 384883 = 577325) B577325
theorem B647041 : Blo 381763 647041 := bstep (se 2 (by rfl) ⟨242640, by rfl⟩ : syracuseStep 647041 = 485281) B485281
theorem B384899 : Blo 381763 384899 := bstep (se 1 (by rfl) ⟨288674, by rfl⟩ : syracuseStep 384899 = 577349) B577349
theorem B384915 : Blo 381763 384915 := bstep (se 1 (by rfl) ⟨288686, by rfl⟩ : syracuseStep 384915 = 577373) B577373
theorem B647075 : Blo 381763 647075 := bstep (se 1 (by rfl) ⟨485306, by rfl⟩ : syracuseStep 647075 = 970613) B970613
theorem B384931 : Blo 381763 384931 := bstep (se 1 (by rfl) ⟨288698, by rfl⟩ : syracuseStep 384931 = 577397) B577397
theorem B384947 : Blo 381763 384947 := bstep (se 1 (by rfl) ⟨288710, by rfl⟩ : syracuseStep 384947 = 577421) B577421
theorem B384963 : Blo 381763 384963 := bstep (se 1 (by rfl) ⟨288722, by rfl⟩ : syracuseStep 384963 = 577445) B577445
theorem B384979 : Blo 381763 384979 := bstep (se 1 (by rfl) ⟨288734, by rfl⟩ : syracuseStep 384979 = 577469) B577469
theorem B384995 : Blo 381763 384995 := bstep (se 1 (by rfl) ⟨288746, by rfl⟩ : syracuseStep 384995 = 577493) B577493
theorem B385011 : Blo 381763 385011 := bstep (se 1 (by rfl) ⟨288758, by rfl⟩ : syracuseStep 385011 = 577517) B577517
theorem B385027 : Blo 381763 385027 := bstep (se 1 (by rfl) ⟨288770, by rfl⟩ : syracuseStep 385027 = 577541) B577541
theorem B483347 : Blo 381763 483347 := bstep (se 1 (by rfl) ⟨362510, by rfl⟩ : syracuseStep 483347 = 725021) B725021
theorem B385043 : Blo 381763 385043 := bstep (se 1 (by rfl) ⟨288782, by rfl⟩ : syracuseStep 385043 = 577565) B577565
theorem B647203 : Blo 381763 647203 := bstep (se 1 (by rfl) ⟨485402, by rfl⟩ : syracuseStep 647203 = 970805) B970805
theorem B385059 : Blo 381763 385059 := bstep (se 1 (by rfl) ⟨288794, by rfl⟩ : syracuseStep 385059 = 577589) B577589
theorem B581683 : Blo 381763 581683 := bstep (se 1 (by rfl) ⟨436262, by rfl⟩ : syracuseStep 581683 = 872525) B872525
theorem B385075 : Blo 381763 385075 := bstep (se 1 (by rfl) ⟨288806, by rfl⟩ : syracuseStep 385075 = 577613) B577613
theorem B385091 : Blo 381763 385091 := bstep (se 1 (by rfl) ⟨288818, by rfl⟩ : syracuseStep 385091 = 577637) B577637
theorem B385107 : Blo 381763 385107 := bstep (se 1 (by rfl) ⟨288830, by rfl⟩ : syracuseStep 385107 = 577661) B577661
theorem B385123 : Blo 381763 385123 := bstep (se 1 (by rfl) ⟨288842, by rfl⟩ : syracuseStep 385123 = 577685) B577685
theorem B385139 : Blo 381763 385139 := bstep (se 1 (by rfl) ⟨288854, by rfl⟩ : syracuseStep 385139 = 577709) B577709
theorem B385155 : Blo 381763 385155 := bstep (se 1 (by rfl) ⟨288866, by rfl⟩ : syracuseStep 385155 = 577733) B577733
theorem B1171601 : Blo 381763 1171601 := bstep (se 2 (by rfl) ⟨439350, by rfl⟩ : syracuseStep 1171601 = 878701) B878701
theorem B385171 : Blo 381763 385171 := bstep (se 1 (by rfl) ⟨288878, by rfl⟩ : syracuseStep 385171 = 577757) B577757
theorem B385187 : Blo 381763 385187 := bstep (se 1 (by rfl) ⟨288890, by rfl⟩ : syracuseStep 385187 = 577781) B577781
theorem B647345 : Blo 381763 647345 := bstep (se 2 (by rfl) ⟨242754, by rfl⟩ : syracuseStep 647345 = 485509) B485509
theorem B385203 : Blo 381763 385203 := bstep (se 1 (by rfl) ⟨288902, by rfl⟩ : syracuseStep 385203 = 577805) B577805
theorem B385219 : Blo 381763 385219 := bstep (se 1 (by rfl) ⟨288914, by rfl⟩ : syracuseStep 385219 = 577829) B577829
theorem B385235 : Blo 381763 385235 := bstep (se 1 (by rfl) ⟨288926, by rfl⟩ : syracuseStep 385235 = 577853) B577853
theorem B385251 : Blo 381763 385251 := bstep (se 1 (by rfl) ⟨288938, by rfl⟩ : syracuseStep 385251 = 577877) B577877
theorem B385267 : Blo 381763 385267 := bstep (se 1 (by rfl) ⟨288950, by rfl⟩ : syracuseStep 385267 = 577901) B577901
theorem B385283 : Blo 381763 385283 := bstep (se 1 (by rfl) ⟨288962, by rfl⟩ : syracuseStep 385283 = 577925) B577925
theorem B385299 : Blo 381763 385299 := bstep (se 1 (by rfl) ⟨288974, by rfl⟩ : syracuseStep 385299 = 577949) B577949
theorem B385315 : Blo 381763 385315 := bstep (se 1 (by rfl) ⟨288986, by rfl⟩ : syracuseStep 385315 = 577973) B577973
theorem B647473 : Blo 381763 647473 := bstep (se 2 (by rfl) ⟨242802, by rfl⟩ : syracuseStep 647473 = 485605) B485605
theorem B385331 : Blo 381763 385331 := bstep (se 1 (by rfl) ⟨288998, by rfl⟩ : syracuseStep 385331 = 577997) B577997
theorem B385347 : Blo 381763 385347 := bstep (se 1 (by rfl) ⟨289010, by rfl⟩ : syracuseStep 385347 = 578021) B578021
theorem B647507 : Blo 381763 647507 := bstep (se 1 (by rfl) ⟨485630, by rfl⟩ : syracuseStep 647507 = 971261) B971261
theorem B385363 : Blo 381763 385363 := bstep (se 1 (by rfl) ⟨289022, by rfl⟩ : syracuseStep 385363 = 578045) B578045
theorem B385379 : Blo 381763 385379 := bstep (se 1 (by rfl) ⟨289034, by rfl⟩ : syracuseStep 385379 = 578069) B578069
theorem B385395 : Blo 381763 385395 := bstep (se 1 (by rfl) ⟨289046, by rfl⟩ : syracuseStep 385395 = 578093) B578093
theorem B385411 : Blo 381763 385411 := bstep (se 1 (by rfl) ⟨289058, by rfl⟩ : syracuseStep 385411 = 578117) B578117
theorem B385427 : Blo 381763 385427 := bstep (se 1 (by rfl) ⟨289070, by rfl⟩ : syracuseStep 385427 = 578141) B578141
theorem B385443 : Blo 381763 385443 := bstep (se 1 (by rfl) ⟨289082, by rfl⟩ : syracuseStep 385443 = 578165) B578165
theorem B385459 : Blo 381763 385459 := bstep (se 1 (by rfl) ⟨289094, by rfl⟩ : syracuseStep 385459 = 578189) B578189
theorem B385475 : Blo 381763 385475 := bstep (se 1 (by rfl) ⟨289106, by rfl⟩ : syracuseStep 385475 = 578213) B578213
theorem B647635 : Blo 381763 647635 := bstep (se 1 (by rfl) ⟨485726, by rfl⟩ : syracuseStep 647635 = 971453) B971453
theorem B385491 : Blo 381763 385491 := bstep (se 1 (by rfl) ⟨289118, by rfl⟩ : syracuseStep 385491 = 578237) B578237
theorem B385507 : Blo 381763 385507 := bstep (se 1 (by rfl) ⟨289130, by rfl⟩ : syracuseStep 385507 = 578261) B578261
theorem B3498481 : Blo 381763 3498481 := bstep (se 2 (by rfl) ⟨1311930, by rfl⟩ : syracuseStep 3498481 = 2623861) B2623861
theorem B385523 : Blo 381763 385523 := bstep (se 1 (by rfl) ⟨289142, by rfl⟩ : syracuseStep 385523 = 578285) B578285
theorem B385539 : Blo 381763 385539 := bstep (se 1 (by rfl) ⟨289154, by rfl⟩ : syracuseStep 385539 = 578309) B578309
theorem B1204753 : Blo 381763 1204753 := bstep (se 2 (by rfl) ⟨451782, by rfl⟩ : syracuseStep 1204753 = 903565) B903565
theorem B385555 : Blo 381763 385555 := bstep (se 1 (by rfl) ⟨289166, by rfl⟩ : syracuseStep 385555 = 578333) B578333
theorem B385571 : Blo 381763 385571 := bstep (se 1 (by rfl) ⟨289178, by rfl⟩ : syracuseStep 385571 = 578357) B578357
theorem B385587 : Blo 381763 385587 := bstep (se 1 (by rfl) ⟨289190, by rfl⟩ : syracuseStep 385587 = 578381) B578381
theorem B385603 : Blo 381763 385603 := bstep (se 1 (by rfl) ⟨289202, by rfl⟩ : syracuseStep 385603 = 578405) B578405
theorem B385619 : Blo 381763 385619 := bstep (se 1 (by rfl) ⟨289214, by rfl⟩ : syracuseStep 385619 = 578429) B578429
theorem B647777 : Blo 381763 647777 := bstep (se 2 (by rfl) ⟨242916, by rfl⟩ : syracuseStep 647777 = 485833) B485833
theorem B385635 : Blo 381763 385635 := bstep (se 1 (by rfl) ⟨289226, by rfl⟩ : syracuseStep 385635 = 578453) B578453
theorem B975473 : Blo 381763 975473 := bstep (se 2 (by rfl) ⟨365802, by rfl⟩ : syracuseStep 975473 = 731605) B731605
theorem B385651 : Blo 381763 385651 := bstep (se 1 (by rfl) ⟨289238, by rfl⟩ : syracuseStep 385651 = 578477) B578477
theorem B516737 : Blo 381763 516737 := bstep (se 2 (by rfl) ⟨193776, by rfl⟩ : syracuseStep 516737 = 387553) B387553
theorem B615043 : Blo 381763 615043 := bstep (se 1 (by rfl) ⟨461282, by rfl⟩ : syracuseStep 615043 = 922565) B922565
theorem B385667 : Blo 381763 385667 := bstep (se 1 (by rfl) ⟨289250, by rfl⟩ : syracuseStep 385667 = 578501) B578501
theorem B385683 : Blo 381763 385683 := bstep (se 1 (by rfl) ⟨289262, by rfl⟩ : syracuseStep 385683 = 578525) B578525
theorem B975523 : Blo 381763 975523 := bstep (se 1 (by rfl) ⟨731642, by rfl⟩ : syracuseStep 975523 = 1463285) B1463285
theorem B385699 : Blo 381763 385699 := bstep (se 1 (by rfl) ⟨289274, by rfl⟩ : syracuseStep 385699 = 578549) B578549
theorem B615089 : Blo 381763 615089 := bstep (se 2 (by rfl) ⟨230658, by rfl⟩ : syracuseStep 615089 = 461317) B461317
theorem B385715 : Blo 381763 385715 := bstep (se 1 (by rfl) ⟨289286, by rfl⟩ : syracuseStep 385715 = 578573) B578573
theorem B385731 : Blo 381763 385731 := bstep (se 1 (by rfl) ⟨289298, by rfl⟩ : syracuseStep 385731 = 578597) B578597
theorem B484051 : Blo 381763 484051 := bstep (se 1 (by rfl) ⟨363038, by rfl⟩ : syracuseStep 484051 = 726077) B726077
theorem B385747 : Blo 381763 385747 := bstep (se 1 (by rfl) ⟨289310, by rfl⟩ : syracuseStep 385747 = 578621) B578621
theorem B647905 : Blo 381763 647905 := bstep (se 2 (by rfl) ⟨242964, by rfl⟩ : syracuseStep 647905 = 485929) B485929
theorem B1172195 : Blo 381763 1172195 := bstep (se 1 (by rfl) ⟨879146, by rfl⟩ : syracuseStep 1172195 = 1758293) B1758293
theorem B385763 : Blo 381763 385763 := bstep (se 1 (by rfl) ⟨289322, by rfl⟩ : syracuseStep 385763 = 578645) B578645
theorem B647939 : Blo 381763 647939 := bstep (se 1 (by rfl) ⟨485954, by rfl⟩ : syracuseStep 647939 = 971909) B971909
theorem B975665 : Blo 381763 975665 := bstep (se 2 (by rfl) ⟨365874, by rfl⟩ : syracuseStep 975665 = 731749) B731749
theorem B484147 : Blo 381763 484147 := bstep (se 1 (by rfl) ⟨363110, by rfl⟩ : syracuseStep 484147 = 726221) B726221
theorem B648067 : Blo 381763 648067 := bstep (se 1 (by rfl) ⟨486050, by rfl⟩ : syracuseStep 648067 = 972101) B972101
theorem B1041389 : Blo 381763 1041389 := bstep (se 3 (by rfl) ⟨195260, by rfl⟩ : syracuseStep 1041389 = 390521) B390521
theorem B648209 : Blo 381763 648209 := bstep (se 2 (by rfl) ⟨243078, by rfl⟩ : syracuseStep 648209 = 486157) B486157
theorem B648337 : Blo 381763 648337 := bstep (se 2 (by rfl) ⟨243126, by rfl⟩ : syracuseStep 648337 = 486253) B486253
theorem B648371 : Blo 381763 648371 := bstep (se 1 (by rfl) ⟨486278, by rfl⟩ : syracuseStep 648371 = 972557) B972557
theorem B582851 : Blo 381763 582851 := bstep (se 1 (by rfl) ⟨437138, by rfl⟩ : syracuseStep 582851 = 874277) B874277
theorem B484643 : Blo 381763 484643 := bstep (se 1 (by rfl) ⟨363482, by rfl⟩ : syracuseStep 484643 = 726965) B726965
theorem B648499 : Blo 381763 648499 := bstep (se 1 (by rfl) ⟨486374, by rfl⟩ : syracuseStep 648499 = 972749) B972749
theorem B648641 : Blo 381763 648641 := bstep (se 2 (by rfl) ⟨243240, by rfl⟩ : syracuseStep 648641 = 486481) B486481
theorem B2909681 : Blo 381763 2909681 := bstep (se 2 (by rfl) ⟨1091130, by rfl⟩ : syracuseStep 2909681 = 2182261) B2182261
theorem B648769 : Blo 381763 648769 := bstep (se 2 (by rfl) ⟨243288, by rfl⟩ : syracuseStep 648769 = 486577) B486577
theorem B648803 : Blo 381763 648803 := bstep (se 1 (by rfl) ⟨486602, by rfl⟩ : syracuseStep 648803 = 973205) B973205
theorem B616081 : Blo 381763 616081 := bstep (se 2 (by rfl) ⟨231030, by rfl⟩ : syracuseStep 616081 = 462061) B462061
theorem B648931 : Blo 381763 648931 := bstep (se 1 (by rfl) ⟨486698, by rfl⟩ : syracuseStep 648931 = 973397) B973397
theorem B649073 : Blo 381763 649073 := bstep (se 2 (by rfl) ⟨243402, by rfl⟩ : syracuseStep 649073 = 486805) B486805
theorem B485347 : Blo 381763 485347 := bstep (se 1 (by rfl) ⟨364010, by rfl⟩ : syracuseStep 485347 = 728021) B728021
theorem B649201 : Blo 381763 649201 := bstep (se 2 (by rfl) ⟨243450, by rfl⟩ : syracuseStep 649201 = 486901) B486901
theorem B649235 : Blo 381763 649235 := bstep (se 1 (by rfl) ⟨486926, by rfl⟩ : syracuseStep 649235 = 973853) B973853
theorem B485443 : Blo 381763 485443 := bstep (se 1 (by rfl) ⟨364082, by rfl⟩ : syracuseStep 485443 = 728165) B728165
theorem B616529 : Blo 381763 616529 := bstep (se 2 (by rfl) ⟨231198, by rfl⟩ : syracuseStep 616529 = 462397) B462397
theorem B649363 : Blo 381763 649363 := bstep (se 1 (by rfl) ⟨487022, by rfl⟩ : syracuseStep 649363 = 974045) B974045
theorem B649505 : Blo 381763 649505 := bstep (se 2 (by rfl) ⟨243564, by rfl⟩ : syracuseStep 649505 = 487129) B487129
theorem B518467 : Blo 381763 518467 := bstep (se 1 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 518467 = 777701) B777701
theorem B649633 : Blo 381763 649633 := bstep (se 2 (by rfl) ⟨243612, by rfl⟩ : syracuseStep 649633 = 487225) B487225
theorem B649667 : Blo 381763 649667 := bstep (se 1 (by rfl) ⟨487250, by rfl⟩ : syracuseStep 649667 = 974501) B974501
theorem B485939 : Blo 381763 485939 := bstep (se 1 (by rfl) ⟨364454, by rfl⟩ : syracuseStep 485939 = 728909) B728909
theorem B649795 : Blo 381763 649795 := bstep (se 1 (by rfl) ⟨487346, by rfl⟩ : syracuseStep 649795 = 974693) B974693
theorem B649937 : Blo 381763 649937 := bstep (se 2 (by rfl) ⟨243726, by rfl⟩ : syracuseStep 649937 = 487453) B487453
theorem B551729 : Blo 381763 551729 := bstep (se 2 (by rfl) ⟨206898, by rfl⟩ : syracuseStep 551729 = 413797) B413797
theorem B650065 : Blo 381763 650065 := bstep (se 2 (by rfl) ⟨243774, by rfl⟩ : syracuseStep 650065 = 487549) B487549
theorem B650099 : Blo 381763 650099 := bstep (se 1 (by rfl) ⟨487574, by rfl⟩ : syracuseStep 650099 = 975149) B975149
theorem B617395 : Blo 381763 617395 := bstep (se 1 (by rfl) ⟨463046, by rfl⟩ : syracuseStep 617395 = 926093) B926093
theorem B650227 : Blo 381763 650227 := bstep (se 1 (by rfl) ⟨487670, by rfl⟩ : syracuseStep 650227 = 975341) B975341
theorem B650369 : Blo 381763 650369 := bstep (se 2 (by rfl) ⟨243888, by rfl⟩ : syracuseStep 650369 = 487777) B487777
theorem B486643 : Blo 381763 486643 := bstep (se 1 (by rfl) ⟨364982, by rfl⟩ : syracuseStep 486643 = 729965) B729965
theorem B650497 : Blo 381763 650497 := bstep (se 2 (by rfl) ⟨243936, by rfl⟩ : syracuseStep 650497 = 487873) B487873
theorem B650531 : Blo 381763 650531 := bstep (se 1 (by rfl) ⟨487898, by rfl⟩ : syracuseStep 650531 = 975797) B975797
theorem B486739 : Blo 381763 486739 := bstep (se 1 (by rfl) ⟨365054, by rfl⟩ : syracuseStep 486739 = 730109) B730109
theorem B1961329 : Blo 381763 1961329 := bstep (se 2 (by rfl) ⟨735498, by rfl⟩ : syracuseStep 1961329 = 1470997) B1470997
theorem B650659 : Blo 381763 650659 := bstep (se 1 (by rfl) ⟨487994, by rfl⟩ : syracuseStep 650659 = 975989) B975989
theorem B519635 : Blo 381763 519635 := bstep (se 1 (by rfl) ⟨389726, by rfl⟩ : syracuseStep 519635 = 779453) B779453
theorem B585185 : Blo 381763 585185 := bstep (se 2 (by rfl) ⟨219444, by rfl⟩ : syracuseStep 585185 = 438889) B438889
theorem B650801 : Blo 381763 650801 := bstep (se 2 (by rfl) ⟨244050, by rfl⟩ : syracuseStep 650801 = 488101) B488101
theorem B4910705 : Blo 381763 4910705 := bstep (se 2 (by rfl) ⟨1841514, by rfl⟩ : syracuseStep 4910705 = 3683029) B3683029
theorem B650929 : Blo 381763 650929 := bstep (se 2 (by rfl) ⟨244098, by rfl⟩ : syracuseStep 650929 = 488197) B488197
theorem B650963 : Blo 381763 650963 := bstep (se 1 (by rfl) ⟨488222, by rfl⟩ : syracuseStep 650963 = 976445) B976445
theorem B487235 : Blo 381763 487235 := bstep (se 1 (by rfl) ⟨365426, by rfl⟩ : syracuseStep 487235 = 730853) B730853
theorem B552803 : Blo 381763 552803 := bstep (se 1 (by rfl) ⟨414602, by rfl⟩ : syracuseStep 552803 = 829205) B829205
theorem B5238755 : Blo 381763 5238755 := bstep (se 1 (by rfl) ⟨3929066, by rfl⟩ : syracuseStep 5238755 = 7858133) B7858133
theorem B3272845 : Blo 381763 3272845 := bstep (se 3 (by rfl) ⟨613658, by rfl⟩ : syracuseStep 3272845 = 1227317) B1227317
theorem B1634509 : Blo 381763 1634509 := bstep (se 3 (by rfl) ⟨306470, by rfl⟩ : syracuseStep 1634509 = 612941) B612941
theorem B520435 : Blo 381763 520435 := bstep (se 1 (by rfl) ⟨390326, by rfl⟩ : syracuseStep 520435 = 780653) B780653
theorem B5140849 : Blo 381763 5140849 := bstep (se 2 (by rfl) ⟨1927818, by rfl⟩ : syracuseStep 5140849 = 3855637) B3855637
theorem B520673 : Blo 381763 520673 := bstep (se 2 (by rfl) ⟨195252, by rfl⟩ : syracuseStep 520673 = 390505) B390505
theorem B487939 : Blo 381763 487939 := bstep (se 1 (by rfl) ⟨365954, by rfl⟩ : syracuseStep 487939 = 731909) B731909
theorem B815683 : Blo 381763 815683 := bstep (se 1 (by rfl) ⟨611762, by rfl⟩ : syracuseStep 815683 = 1223525) B1223525
theorem B979537 : Blo 381763 979537 := bstep (se 2 (by rfl) ⟨367326, by rfl⟩ : syracuseStep 979537 = 734653) B734653
theorem B488035 : Blo 381763 488035 := bstep (se 1 (by rfl) ⟨366026, by rfl⟩ : syracuseStep 488035 = 732053) B732053
theorem B586433 : Blo 381763 586433 := bstep (se 2 (by rfl) ⟨219912, by rfl⟩ : syracuseStep 586433 = 439825) B439825
theorem B4682549 : Blo 381763 4682549 := bstep (se 5 (by rfl) ⟨219494, by rfl⟩ : syracuseStep 4682549 = 438989) B438989
theorem B2945933 : Blo 381763 2945933 := bstep (se 3 (by rfl) ⟨552362, by rfl⟩ : syracuseStep 2945933 = 1104725) B1104725
theorem B2454533 : Blo 381763 2454533 := bstep (se 4 (by rfl) ⟨230112, by rfl⟩ : syracuseStep 2454533 = 460225) B460225
theorem B390371 : Blo 381763 390371 := bstep (se 1 (by rfl) ⟨292778, by rfl⟩ : syracuseStep 390371 = 585557) B585557
theorem B816401 : Blo 381763 816401 := bstep (se 2 (by rfl) ⟨306150, by rfl⟩ : syracuseStep 816401 = 612301) B612301
theorem B2618801 : Blo 381763 2618801 := bstep (se 2 (by rfl) ⟨982050, by rfl⟩ : syracuseStep 2618801 = 1964101) B1964101
theorem B3274181 : Blo 381763 3274181 := bstep (se 4 (by rfl) ⟨306954, by rfl⟩ : syracuseStep 3274181 = 613909) B613909
theorem B4388579 : Blo 381763 4388579 := bstep (se 1 (by rfl) ⟨3291434, by rfl⟩ : syracuseStep 4388579 = 6582869) B6582869
theorem B816913 : Blo 381763 816913 := bstep (se 2 (by rfl) ⟨306342, by rfl⟩ : syracuseStep 816913 = 612685) B612685
theorem B1308593 : Blo 381763 1308593 := bstep (se 2 (by rfl) ⟨490722, by rfl⟩ : syracuseStep 1308593 = 981445) B981445
theorem B8353763 : Blo 381763 8353763 := bstep (se 1 (by rfl) ⟨6265322, by rfl⟩ : syracuseStep 8353763 = 12530645) B12530645
theorem B2488333 : Blo 381763 2488333 := bstep (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) B933125
theorem B2193925 : Blo 381763 2193925 := bstep (se 4 (by rfl) ⟨205680, by rfl⟩ : syracuseStep 2193925 = 411361) B411361
theorem B1047181 : Blo 381763 1047181 := bstep (se 3 (by rfl) ⟨196346, by rfl⟩ : syracuseStep 1047181 = 392693) B392693
theorem B818417 : Blo 381763 818417 := bstep (se 2 (by rfl) ⟨306906, by rfl⟩ : syracuseStep 818417 = 613813) B613813
theorem B1310179 : Blo 381763 1310179 := bstep (se 1 (by rfl) ⟨982634, by rfl⟩ : syracuseStep 1310179 = 1965269) B1965269
theorem B491123 : Blo 381763 491123 := bstep (se 1 (by rfl) ⟨368342, by rfl⟩ : syracuseStep 491123 = 736685) B736685
theorem B818819 : Blo 381763 818819 := bstep (se 1 (by rfl) ⟨614114, by rfl⟩ : syracuseStep 818819 = 1228229) B1228229
theorem B655249 : Blo 381763 655249 := bstep (se 2 (by rfl) ⟨245718, by rfl⟩ : syracuseStep 655249 = 491437) B491437
theorem B655447 : Blo 381763 655447 := bstep (se 1 (by rfl) ⟨491585, by rfl⟩ : syracuseStep 655447 = 983171) B983171
theorem B2490689 : Blo 381763 2490689 := bstep (se 2 (by rfl) ⟨934008, by rfl⟩ : syracuseStep 2490689 = 1868017) B1868017
theorem B1638731 : Blo 381763 1638731 := bstep (se 1 (by rfl) ⟨1229048, by rfl⟩ : syracuseStep 1638731 = 2458097) B2458097
theorem B819571 : Blo 381763 819571 := bstep (se 1 (by rfl) ⟨614678, by rfl⟩ : syracuseStep 819571 = 1229357) B1229357
theorem B1933955 : Blo 381763 1933955 := bstep (se 1 (by rfl) ⟨1450466, by rfl⟩ : syracuseStep 1933955 = 2900933) B2900933
theorem B1606337 : Blo 381763 1606337 := bstep (se 2 (by rfl) ⟨602376, by rfl⟩ : syracuseStep 1606337 = 1204753) B1204753
theorem B1966913 : Blo 381763 1966913 := bstep (se 2 (by rfl) ⟨737592, by rfl⟩ : syracuseStep 1966913 = 1475185) B1475185
theorem B820057 : Blo 381763 820057 := bstep (se 2 (by rfl) ⟨307521, by rfl⟩ : syracuseStep 820057 = 615043) B615043
theorem B2196659 : Blo 381763 2196659 := bstep (se 1 (by rfl) ⟨1647494, by rfl⟩ : syracuseStep 2196659 = 3294989) B3294989
theorem B1639703 : Blo 381763 1639703 := bstep (se 1 (by rfl) ⟨1229777, by rfl⟩ : syracuseStep 1639703 = 2459555) B2459555
theorem B2754083 : Blo 381763 2754083 := bstep (se 1 (by rfl) ⟨2065562, by rfl⟩ : syracuseStep 2754083 = 4131125) B4131125
theorem B1377965 : Blo 381763 1377965 := bstep (se 3 (by rfl) ⟨258368, by rfl⟩ : syracuseStep 1377965 = 516737) B516737
theorem B4982705 : Blo 381763 4982705 := bstep (se 2 (by rfl) ⟨1868514, by rfl⟩ : syracuseStep 4982705 = 3737029) B3737029
theorem B1640371 : Blo 381763 1640371 := bstep (se 1 (by rfl) ⟨1230278, by rfl⟩ : syracuseStep 1640371 = 2460557) B2460557
theorem B690187 : Blo 381763 690187 := bstep (se 1 (by rfl) ⟨517640, by rfl⟩ : syracuseStep 690187 = 1035281) B1035281
theorem B821441 : Blo 381763 821441 := bstep (se 2 (by rfl) ⟨308040, by rfl⟩ : syracuseStep 821441 = 616081) B616081
theorem B919873 : Blo 381763 919873 := bstep (se 2 (by rfl) ⟨344952, by rfl⟩ : syracuseStep 919873 = 689905) B689905
theorem B4163957 : Blo 381763 4163957 := bstep (se 5 (by rfl) ⟨195185, by rfl⟩ : syracuseStep 4163957 = 390371) B390371
theorem B821963 : Blo 381763 821963 := bstep (se 1 (by rfl) ⟨616472, by rfl⟩ : syracuseStep 821963 = 1232945) B1232945
theorem B12389219 : Blo 381763 12389219 := bstep (se 1 (by rfl) ⟨9291914, by rfl⟩ : syracuseStep 12389219 = 18583829) B18583829
theorem B691289 : Blo 381763 691289 := bstep (se 2 (by rfl) ⟨259233, by rfl⟩ : syracuseStep 691289 = 518467) B518467
theorem B1641617 : Blo 381763 1641617 := bstep (se 2 (by rfl) ⟨615606, by rfl⟩ : syracuseStep 1641617 = 1231213) B1231213
theorem B1477835 : Blo 381763 1477835 := bstep (se 1 (by rfl) ⟨1108376, by rfl⟩ : syracuseStep 1477835 = 2216753) B2216753
theorem B429547 : Blo 381763 429547 := bstep (se 1 (by rfl) ⟨322160, by rfl⟩ : syracuseStep 429547 = 644321) B644321
theorem B429655 : Blo 381763 429655 := bstep (se 1 (by rfl) ⟨322241, by rfl⟩ : syracuseStep 429655 = 644483) B644483
theorem B429835 : Blo 381763 429835 := bstep (se 1 (by rfl) ⟨322376, by rfl⟩ : syracuseStep 429835 = 644753) B644753
theorem B724801 : Blo 381763 724801 := bstep (se 2 (by rfl) ⟨271800, by rfl⟩ : syracuseStep 724801 = 543601) B543601
theorem B429943 : Blo 381763 429943 := bstep (se 1 (by rfl) ⟨322457, by rfl⟩ : syracuseStep 429943 = 644915) B644915
theorem B823193 : Blo 381763 823193 := bstep (se 2 (by rfl) ⟨308697, by rfl⟩ : syracuseStep 823193 = 617395) B617395
theorem B692183 : Blo 381763 692183 := bstep (se 1 (by rfl) ⟨519137, by rfl⟩ : syracuseStep 692183 = 1038275) B1038275
theorem B430123 : Blo 381763 430123 := bstep (se 1 (by rfl) ⟨322592, by rfl⟩ : syracuseStep 430123 = 645185) B645185
theorem B430231 : Blo 381763 430231 := bstep (se 1 (by rfl) ⟨322673, by rfl⟩ : syracuseStep 430231 = 645347) B645347
theorem B1380503 : Blo 381763 1380503 := bstep (se 1 (by rfl) ⟨1035377, by rfl⟩ : syracuseStep 1380503 = 2070755) B2070755
theorem B725249 : Blo 381763 725249 := bstep (se 2 (by rfl) ⟨271968, by rfl⟩ : syracuseStep 725249 = 543937) B543937
theorem B1937681 : Blo 381763 1937681 := bstep (se 2 (by rfl) ⟨726630, by rfl⟩ : syracuseStep 1937681 = 1453261) B1453261
theorem B823603 : Blo 381763 823603 := bstep (se 1 (by rfl) ⟨617702, by rfl⟩ : syracuseStep 823603 = 1235405) B1235405
theorem B430411 : Blo 381763 430411 := bstep (se 1 (by rfl) ⟨322808, by rfl⟩ : syracuseStep 430411 = 645617) B645617
theorem B9802133 : Blo 381763 9802133 := bstep (se 6 (by rfl) ⟨229737, by rfl⟩ : syracuseStep 9802133 = 459475) B459475
theorem B1937843 : Blo 381763 1937843 := bstep (se 1 (by rfl) ⟨1453382, by rfl⟩ : syracuseStep 1937843 = 2906765) B2906765
theorem B430519 : Blo 381763 430519 := bstep (se 1 (by rfl) ⟨322889, by rfl⟩ : syracuseStep 430519 = 645779) B645779
theorem B725591 : Blo 381763 725591 := bstep (se 1 (by rfl) ⟨544193, by rfl⟩ : syracuseStep 725591 = 1088387) B1088387
theorem B430699 : Blo 381763 430699 := bstep (se 1 (by rfl) ⟨323024, by rfl⟩ : syracuseStep 430699 = 646049) B646049
theorem B692875 : Blo 381763 692875 := bstep (se 1 (by rfl) ⟨519656, by rfl⟩ : syracuseStep 692875 = 1039313) B1039313
theorem B430807 : Blo 381763 430807 := bstep (se 1 (by rfl) ⟨323105, by rfl⟩ : syracuseStep 430807 = 646211) B646211
theorem B430987 : Blo 381763 430987 := bstep (se 1 (by rfl) ⟨323240, by rfl⟩ : syracuseStep 430987 = 646481) B646481
theorem B7410649 : Blo 381763 7410649 := bstep (se 2 (by rfl) ⟨2778993, by rfl⟩ : syracuseStep 7410649 = 5557987) B5557987
theorem B431095 : Blo 381763 431095 := bstep (se 1 (by rfl) ⟨323321, by rfl⟩ : syracuseStep 431095 = 646643) B646643
theorem B1217587 : Blo 381763 1217587 := bstep (se 1 (by rfl) ⟨913190, by rfl⟩ : syracuseStep 1217587 = 1826381) B1826381
theorem B431275 : Blo 381763 431275 := bstep (se 1 (by rfl) ⟨323456, by rfl⟩ : syracuseStep 431275 = 646913) B646913
theorem B3118297 : Blo 381763 3118297 := bstep (se 2 (by rfl) ⟨1169361, by rfl⟩ : syracuseStep 3118297 = 2338723) B2338723
theorem B726259 : Blo 381763 726259 := bstep (se 1 (by rfl) ⟨544694, by rfl⟩ : syracuseStep 726259 = 1089389) B1089389
theorem B431383 : Blo 381763 431383 := bstep (se 1 (by rfl) ⟨323537, by rfl⟩ : syracuseStep 431383 = 647075) B647075
theorem B1316147 : Blo 381763 1316147 := bstep (se 1 (by rfl) ⟨987110, by rfl⟩ : syracuseStep 1316147 = 1974221) B1974221
theorem B2463041 : Blo 381763 2463041 := bstep (se 2 (by rfl) ⟨923640, by rfl⟩ : syracuseStep 2463041 = 1847281) B1847281
theorem B431563 : Blo 381763 431563 := bstep (se 1 (by rfl) ⟨323672, by rfl⟩ : syracuseStep 431563 = 647345) B647345
theorem B4363793 : Blo 381763 4363793 := bstep (se 2 (by rfl) ⟨1636422, by rfl⟩ : syracuseStep 4363793 = 3272845) B3272845
theorem B1644077 : Blo 381763 1644077 := bstep (se 3 (by rfl) ⟨308264, by rfl⟩ : syracuseStep 1644077 = 616529) B616529
theorem B431671 : Blo 381763 431671 := bstep (se 1 (by rfl) ⟨323753, by rfl⟩ : syracuseStep 431671 = 647507) B647507
theorem B726707 : Blo 381763 726707 := bstep (se 1 (by rfl) ⟨545030, by rfl⟩ : syracuseStep 726707 = 1090061) B1090061
theorem B726745 : Blo 381763 726745 := bstep (se 2 (by rfl) ⟨272529, by rfl⟩ : syracuseStep 726745 = 545059) B545059
theorem B431851 : Blo 381763 431851 := bstep (se 1 (by rfl) ⟨323888, by rfl⟩ : syracuseStep 431851 = 647777) B647777
theorem B6854465 : Blo 381763 6854465 := bstep (se 2 (by rfl) ⟨2570424, by rfl⟩ : syracuseStep 6854465 = 5140849) B5140849
theorem B431959 : Blo 381763 431959 := bstep (se 1 (by rfl) ⟨323969, by rfl⟩ : syracuseStep 431959 = 647939) B647939
theorem B694259 : Blo 381763 694259 := bstep (se 1 (by rfl) ⟨520694, by rfl⟩ : syracuseStep 694259 = 1041389) B1041389
theorem B432139 : Blo 381763 432139 := bstep (se 1 (by rfl) ⟨324104, by rfl⟩ : syracuseStep 432139 = 648209) B648209
theorem B1087577 : Blo 381763 1087577 := bstep (se 2 (by rfl) ⟨407841, by rfl⟩ : syracuseStep 1087577 = 815683) B815683
theorem B432247 : Blo 381763 432247 := bstep (se 1 (by rfl) ⟨324185, by rfl⟩ : syracuseStep 432247 = 648371) B648371
theorem B727193 : Blo 381763 727193 := bstep (se 2 (by rfl) ⟨272697, by rfl⟩ : syracuseStep 727193 = 545395) B545395
theorem B1644761 : Blo 381763 1644761 := bstep (se 2 (by rfl) ⟨616785, by rfl⟩ : syracuseStep 1644761 = 1233571) B1233571
theorem B432427 : Blo 381763 432427 := bstep (se 1 (by rfl) ⟨324320, by rfl⟩ : syracuseStep 432427 = 648641) B648641
theorem B1939787 : Blo 381763 1939787 := bstep (se 1 (by rfl) ⟨1454840, by rfl⟩ : syracuseStep 1939787 = 2909681) B2909681
theorem B432535 : Blo 381763 432535 := bstep (se 1 (by rfl) ⟨324401, by rfl⟩ : syracuseStep 432535 = 648803) B648803
theorem B432715 : Blo 381763 432715 := bstep (se 1 (by rfl) ⟨324536, by rfl⟩ : syracuseStep 432715 = 649073) B649073
theorem B432823 : Blo 381763 432823 := bstep (se 1 (by rfl) ⟨324617, by rfl⟩ : syracuseStep 432823 = 649235) B649235
theorem B433003 : Blo 381763 433003 := bstep (se 1 (by rfl) ⟨324752, by rfl⟩ : syracuseStep 433003 = 649505) B649505
theorem B858995 : Blo 381763 858995 := bstep (se 1 (by rfl) ⟨644246, by rfl⟩ : syracuseStep 858995 = 1288493) B1288493
theorem B727937 : Blo 381763 727937 := bstep (se 2 (by rfl) ⟨272976, by rfl⟩ : syracuseStep 727937 = 545953) B545953
theorem B859031 : Blo 381763 859031 := bstep (se 1 (by rfl) ⟨644273, by rfl⟩ : syracuseStep 859031 = 1288547) B1288547
theorem B433111 : Blo 381763 433111 := bstep (se 1 (by rfl) ⟨324833, by rfl⟩ : syracuseStep 433111 = 649667) B649667
theorem B859211 : Blo 381763 859211 := bstep (se 1 (by rfl) ⟨644408, by rfl⟩ : syracuseStep 859211 = 1288817) B1288817
theorem B2628683 : Blo 381763 2628683 := bstep (se 1 (by rfl) ⟨1971512, by rfl⟩ : syracuseStep 2628683 = 3943025) B3943025
theorem B859265 : Blo 381763 859265 := bstep (se 2 (by rfl) ⟨322224, by rfl⟩ : syracuseStep 859265 = 644449) B644449
theorem B728203 : Blo 381763 728203 := bstep (se 1 (by rfl) ⟨546152, by rfl⟩ : syracuseStep 728203 = 1092305) B1092305
theorem B433291 : Blo 381763 433291 := bstep (se 1 (by rfl) ⟨324968, by rfl⟩ : syracuseStep 433291 = 649937) B649937
theorem B433399 : Blo 381763 433399 := bstep (se 1 (by rfl) ⟨325049, by rfl⟩ : syracuseStep 433399 = 650099) B650099
theorem B1383731 : Blo 381763 1383731 := bstep (se 1 (by rfl) ⟨1037798, by rfl⟩ : syracuseStep 1383731 = 2075597) B2075597
theorem B859481 : Blo 381763 859481 := bstep (se 2 (by rfl) ⟨322305, by rfl⟩ : syracuseStep 859481 = 644611) B644611
theorem B433579 : Blo 381763 433579 := bstep (se 1 (by rfl) ⟨325184, by rfl⟩ : syracuseStep 433579 = 650369) B650369
theorem B4922801 : Blo 381763 4922801 := bstep (se 2 (by rfl) ⟨1846050, by rfl⟩ : syracuseStep 4922801 = 3692101) B3692101
theorem B859571 : Blo 381763 859571 := bstep (se 1 (by rfl) ⟨644678, by rfl⟩ : syracuseStep 859571 = 1289357) B1289357
theorem B1646027 : Blo 381763 1646027 := bstep (se 1 (by rfl) ⟨1234520, by rfl⟩ : syracuseStep 1646027 = 2469041) B2469041
theorem B859607 : Blo 381763 859607 := bstep (se 1 (by rfl) ⟨644705, by rfl⟩ : syracuseStep 859607 = 1289411) B1289411
theorem B5250577 : Blo 381763 5250577 := bstep (se 2 (by rfl) ⟨1968966, by rfl⟩ : syracuseStep 5250577 = 3937933) B3937933
theorem B433687 : Blo 381763 433687 := bstep (se 1 (by rfl) ⟨325265, by rfl⟩ : syracuseStep 433687 = 650531) B650531
theorem B6233669 : Blo 381763 6233669 := bstep (se 4 (by rfl) ⟨584406, by rfl⟩ : syracuseStep 6233669 = 1168813) B1168813
theorem B728651 : Blo 381763 728651 := bstep (se 1 (by rfl) ⟨546488, by rfl⟩ : syracuseStep 728651 = 1092977) B1092977
theorem B859787 : Blo 381763 859787 := bstep (se 1 (by rfl) ⟨644840, by rfl⟩ : syracuseStep 859787 = 1289681) B1289681
theorem B859841 : Blo 381763 859841 := bstep (se 2 (by rfl) ⟨322440, by rfl⟩ : syracuseStep 859841 = 644881) B644881
theorem B1089217 : Blo 381763 1089217 := bstep (se 2 (by rfl) ⟨408456, by rfl⟩ : syracuseStep 1089217 = 816913) B816913
theorem B433867 : Blo 381763 433867 := bstep (se 1 (by rfl) ⟨325400, by rfl⟩ : syracuseStep 433867 = 650801) B650801
theorem B728833 : Blo 381763 728833 := bstep (se 2 (by rfl) ⟨273312, by rfl⟩ : syracuseStep 728833 = 546625) B546625
theorem B433975 : Blo 381763 433975 := bstep (se 1 (by rfl) ⟨325481, by rfl⟩ : syracuseStep 433975 = 650963) B650963
theorem B1646401 : Blo 381763 1646401 := bstep (se 2 (by rfl) ⟨617400, by rfl⟩ : syracuseStep 1646401 = 1234801) B1234801
theorem B1449859 : Blo 381763 1449859 := bstep (se 1 (by rfl) ⟨1087394, by rfl⟩ : syracuseStep 1449859 = 2174789) B2174789
theorem B1384337 : Blo 381763 1384337 := bstep (se 2 (by rfl) ⟨519126, by rfl⟩ : syracuseStep 1384337 = 1038253) B1038253
theorem B860057 : Blo 381763 860057 := bstep (se 2 (by rfl) ⟨322521, by rfl⟩ : syracuseStep 860057 = 645043) B645043
theorem B860147 : Blo 381763 860147 := bstep (se 1 (by rfl) ⟨645110, by rfl⟩ : syracuseStep 860147 = 1290221) B1290221
theorem B3317777 : Blo 381763 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B860183 : Blo 381763 860183 := bstep (se 1 (by rfl) ⟨645137, by rfl⟩ : syracuseStep 860183 = 1290275) B1290275
theorem B1941569 : Blo 381763 1941569 := bstep (se 2 (by rfl) ⟨728088, by rfl⟩ : syracuseStep 1941569 = 1456177) B1456177
theorem B729175 : Blo 381763 729175 := bstep (se 1 (by rfl) ⟨546881, by rfl⟩ : syracuseStep 729175 = 1093763) B1093763
theorem B1646743 : Blo 381763 1646743 := bstep (se 1 (by rfl) ⟨1235057, by rfl⟩ : syracuseStep 1646743 = 2470115) B2470115
theorem B1450163 : Blo 381763 1450163 := bstep (se 1 (by rfl) ⟨1087622, by rfl⟩ : syracuseStep 1450163 = 2175245) B2175245
theorem B1974451 : Blo 381763 1974451 := bstep (se 1 (by rfl) ⟨1480838, by rfl⟩ : syracuseStep 1974451 = 2961677) B2961677
theorem B860363 : Blo 381763 860363 := bstep (se 1 (by rfl) ⟨645272, by rfl⟩ : syracuseStep 860363 = 1290545) B1290545
theorem B860417 : Blo 381763 860417 := bstep (se 2 (by rfl) ⟨322656, by rfl⟩ : syracuseStep 860417 = 645313) B645313
theorem B729395 : Blo 381763 729395 := bstep (se 1 (by rfl) ⟨547046, by rfl⟩ : syracuseStep 729395 = 1094093) B1094093
theorem B467275 : Blo 381763 467275 := bstep (se 1 (by rfl) ⟨350456, by rfl⟩ : syracuseStep 467275 = 700913) B700913
theorem B4366709 : Blo 381763 4366709 := bstep (se 5 (by rfl) ⟨204689, by rfl⟩ : syracuseStep 4366709 = 409379) B409379
theorem B4923827 : Blo 381763 4923827 := bstep (se 1 (by rfl) ⟨3692870, by rfl⟩ : syracuseStep 4923827 = 7385741) B7385741
theorem B860633 : Blo 381763 860633 := bstep (se 2 (by rfl) ⟨322737, by rfl⟩ : syracuseStep 860633 = 645475) B645475
theorem B729623 : Blo 381763 729623 := bstep (se 1 (by rfl) ⟨547217, by rfl⟩ : syracuseStep 729623 = 1094435) B1094435
theorem B3121699 : Blo 381763 3121699 := bstep (se 1 (by rfl) ⟨2341274, by rfl⟩ : syracuseStep 3121699 = 4682549) B4682549
theorem B860723 : Blo 381763 860723 := bstep (se 1 (by rfl) ⟨645542, by rfl⟩ : syracuseStep 860723 = 1291085) B1291085
theorem B860759 : Blo 381763 860759 := bstep (se 1 (by rfl) ⟨645569, by rfl⟩ : syracuseStep 860759 = 1291139) B1291139
theorem B2925233 : Blo 381763 2925233 := bstep (se 2 (by rfl) ⟨1096962, by rfl⟩ : syracuseStep 2925233 = 2193925) B2193925
theorem B860939 : Blo 381763 860939 := bstep (se 1 (by rfl) ⟨645704, by rfl⟩ : syracuseStep 860939 = 1291409) B1291409
theorem B729881 : Blo 381763 729881 := bstep (se 2 (by rfl) ⟨273705, by rfl⟩ : syracuseStep 729881 = 547411) B547411
theorem B1450817 : Blo 381763 1450817 := bstep (se 2 (by rfl) ⟨544056, by rfl⟩ : syracuseStep 1450817 = 1088113) B1088113
theorem B860993 : Blo 381763 860993 := bstep (se 2 (by rfl) ⟨322872, by rfl⟩ : syracuseStep 860993 = 645745) B645745
theorem B2073437 : Blo 381763 2073437 := bstep (se 3 (by rfl) ⟨388769, by rfl⟩ : syracuseStep 2073437 = 777539) B777539
theorem B1745867 : Blo 381763 1745867 := bstep (se 1 (by rfl) ⟨1309400, by rfl⟩ : syracuseStep 1745867 = 2618801) B2618801
theorem B861209 : Blo 381763 861209 := bstep (se 2 (by rfl) ⟨322953, by rfl⟩ : syracuseStep 861209 = 645907) B645907
theorem B861299 : Blo 381763 861299 := bstep (se 1 (by rfl) ⟨645974, by rfl⟩ : syracuseStep 861299 = 1291949) B1291949
theorem B861335 : Blo 381763 861335 := bstep (se 1 (by rfl) ⟨646001, by rfl⟩ : syracuseStep 861335 = 1292003) B1292003
theorem B2925719 : Blo 381763 2925719 := bstep (se 1 (by rfl) ⟨2194289, by rfl⟩ : syracuseStep 2925719 = 4388579) B4388579
theorem B730291 : Blo 381763 730291 := bstep (se 1 (by rfl) ⟨547718, by rfl⟩ : syracuseStep 730291 = 1095437) B1095437
theorem B1385693 : Blo 381763 1385693 := bstep (se 3 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 1385693 = 519635) B519635
theorem B861515 : Blo 381763 861515 := bstep (se 1 (by rfl) ⟨646136, by rfl⟩ : syracuseStep 861515 = 1292273) B1292273
theorem B861569 : Blo 381763 861569 := bstep (se 2 (by rfl) ⟨323088, by rfl⟩ : syracuseStep 861569 = 646177) B646177
theorem B861785 : Blo 381763 861785 := bstep (se 2 (by rfl) ⟨323169, by rfl⟩ : syracuseStep 861785 = 646339) B646339
theorem B730777 : Blo 381763 730777 := bstep (se 2 (by rfl) ⟨274041, by rfl⟩ : syracuseStep 730777 = 548083) B548083
theorem B861875 : Blo 381763 861875 := bstep (se 1 (by rfl) ⟨646406, by rfl⟩ : syracuseStep 861875 = 1292813) B1292813
theorem B861911 : Blo 381763 861911 := bstep (se 1 (by rfl) ⟨646433, by rfl⟩ : syracuseStep 861911 = 1292867) B1292867
theorem B1386371 : Blo 381763 1386371 := bstep (se 1 (by rfl) ⟨1039778, by rfl⟩ : syracuseStep 1386371 = 2079557) B2079557
theorem B862091 : Blo 381763 862091 := bstep (se 1 (by rfl) ⟨646568, by rfl⟩ : syracuseStep 862091 = 1293137) B1293137
theorem B862145 : Blo 381763 862145 := bstep (se 2 (by rfl) ⟨323304, by rfl⟩ : syracuseStep 862145 = 646609) B646609
theorem B1746905 : Blo 381763 1746905 := bstep (se 2 (by rfl) ⟨655089, by rfl⟩ : syracuseStep 1746905 = 1310179) B1310179
theorem B1943513 : Blo 381763 1943513 := bstep (se 2 (by rfl) ⟨728817, by rfl⟩ : syracuseStep 1943513 = 1457635) B1457635
theorem B1386499 : Blo 381763 1386499 := bstep (se 1 (by rfl) ⟨1039874, by rfl⟩ : syracuseStep 1386499 = 2079749) B2079749
theorem B1452077 : Blo 381763 1452077 := bstep (se 3 (by rfl) ⟨272264, by rfl⟩ : syracuseStep 1452077 = 544529) B544529
theorem B1452107 : Blo 381763 1452107 := bstep (se 1 (by rfl) ⟨1089080, by rfl⟩ : syracuseStep 1452107 = 2178161) B2178161
theorem B862361 : Blo 381763 862361 := bstep (se 2 (by rfl) ⟨323385, by rfl⟩ : syracuseStep 862361 = 646771) B646771
theorem B665803 : Blo 381763 665803 := bstep (se 1 (by rfl) ⟨499352, by rfl⟩ : syracuseStep 665803 = 998705) B998705
theorem B731339 : Blo 381763 731339 := bstep (se 1 (by rfl) ⟨548504, by rfl⟩ : syracuseStep 731339 = 1097009) B1097009
theorem B862451 : Blo 381763 862451 := bstep (se 1 (by rfl) ⟨646838, by rfl⟩ : syracuseStep 862451 = 1293677) B1293677
theorem B862487 : Blo 381763 862487 := bstep (se 1 (by rfl) ⟨646865, by rfl⟩ : syracuseStep 862487 = 1293731) B1293731
theorem B731521 : Blo 381763 731521 := bstep (se 2 (by rfl) ⟨274320, by rfl⟩ : syracuseStep 731521 = 548641) B548641
theorem B862667 : Blo 381763 862667 := bstep (se 1 (by rfl) ⟨647000, by rfl⟩ : syracuseStep 862667 = 1294001) B1294001
theorem B862721 : Blo 381763 862721 := bstep (se 2 (by rfl) ⟨323520, by rfl⟩ : syracuseStep 862721 = 647041) B647041
theorem B2107949 : Blo 381763 2107949 := bstep (se 3 (by rfl) ⟨395240, by rfl⟩ : syracuseStep 2107949 = 790481) B790481
theorem B436919 : Blo 381763 436919 := bstep (se 1 (by rfl) ⟨327689, by rfl⟩ : syracuseStep 436919 = 655379) B655379
theorem B1452761 : Blo 381763 1452761 := bstep (se 2 (by rfl) ⟨544785, by rfl⟩ : syracuseStep 1452761 = 1089571) B1089571
theorem B862937 : Blo 381763 862937 := bstep (se 2 (by rfl) ⟨323601, by rfl⟩ : syracuseStep 862937 = 647203) B647203
theorem B1288925 : Blo 381763 1288925 := bstep (se 3 (by rfl) ⟨241673, by rfl⟩ : syracuseStep 1288925 = 483347) B483347
theorem B863027 : Blo 381763 863027 := bstep (se 1 (by rfl) ⟨647270, by rfl⟩ : syracuseStep 863027 = 1294541) B1294541
theorem B1846091 : Blo 381763 1846091 := bstep (se 1 (by rfl) ⟨1384568, by rfl⟩ : syracuseStep 1846091 = 2769137) B2769137
theorem B863063 : Blo 381763 863063 := bstep (se 1 (by rfl) ⟨647297, by rfl⟩ : syracuseStep 863063 = 1294595) B1294595
theorem B863243 : Blo 381763 863243 := bstep (se 1 (by rfl) ⟨647432, by rfl⟩ : syracuseStep 863243 = 1294865) B1294865
theorem B1453079 : Blo 381763 1453079 := bstep (se 1 (by rfl) ⟨1089809, by rfl⟩ : syracuseStep 1453079 = 2179619) B2179619
theorem B863297 : Blo 381763 863297 := bstep (se 2 (by rfl) ⟨323736, by rfl⟩ : syracuseStep 863297 = 647473) B647473
theorem B732235 : Blo 381763 732235 := bstep (se 1 (by rfl) ⟨549176, by rfl⟩ : syracuseStep 732235 = 1098353) B1098353
theorem B732311 : Blo 381763 732311 := bstep (se 1 (by rfl) ⟨549233, by rfl⟩ : syracuseStep 732311 = 1098467) B1098467
theorem B863435 : Blo 381763 863435 := bstep (se 1 (by rfl) ⟨647576, by rfl⟩ : syracuseStep 863435 = 1295153) B1295153
theorem B863513 : Blo 381763 863513 := bstep (se 2 (by rfl) ⟨323817, by rfl⟩ : syracuseStep 863513 = 647635) B647635
theorem B4664641 : Blo 381763 4664641 := bstep (se 2 (by rfl) ⟨1749240, by rfl⟩ : syracuseStep 4664641 = 3498481) B3498481
theorem B1092953 : Blo 381763 1092953 := bstep (se 2 (by rfl) ⟨409857, by rfl⟩ : syracuseStep 1092953 = 819715) B819715
theorem B863603 : Blo 381763 863603 := bstep (se 1 (by rfl) ⟨647702, by rfl⟩ : syracuseStep 863603 = 1295405) B1295405
theorem B863639 : Blo 381763 863639 := bstep (se 1 (by rfl) ⟨647729, by rfl⟩ : syracuseStep 863639 = 1295459) B1295459
theorem B1846745 : Blo 381763 1846745 := bstep (se 2 (by rfl) ⟨692529, by rfl⟩ : syracuseStep 1846745 = 1385059) B1385059
theorem B1945133 : Blo 381763 1945133 := bstep (se 3 (by rfl) ⟨364712, by rfl⟩ : syracuseStep 1945133 = 729425) B729425
theorem B863819 : Blo 381763 863819 := bstep (se 1 (by rfl) ⟨647864, by rfl⟩ : syracuseStep 863819 = 1295729) B1295729
theorem B863873 : Blo 381763 863873 := bstep (se 2 (by rfl) ⟨323952, by rfl⟩ : syracuseStep 863873 = 647905) B647905
theorem B1224371 : Blo 381763 1224371 := bstep (se 1 (by rfl) ⟨918278, by rfl⟩ : syracuseStep 1224371 = 1836557) B1836557
theorem B1453747 : Blo 381763 1453747 := bstep (se 1 (by rfl) ⟨1090310, by rfl⟩ : syracuseStep 1453747 = 2180621) B2180621
theorem B1290059 : Blo 381763 1290059 := bstep (se 1 (by rfl) ⟨967544, by rfl⟩ : syracuseStep 1290059 = 1935089) B1935089
theorem B864089 : Blo 381763 864089 := bstep (se 2 (by rfl) ⟨324033, by rfl⟩ : syracuseStep 864089 = 648067) B648067
theorem B1388461 : Blo 381763 1388461 := bstep (se 3 (by rfl) ⟨260336, by rfl⟩ : syracuseStep 1388461 = 520673) B520673
theorem B864179 : Blo 381763 864179 := bstep (se 1 (by rfl) ⟨648134, by rfl⟩ : syracuseStep 864179 = 1296269) B1296269
theorem B864215 : Blo 381763 864215 := bstep (se 1 (by rfl) ⟨648161, by rfl⟩ : syracuseStep 864215 = 1296323) B1296323
theorem B1290329 : Blo 381763 1290329 := bstep (se 2 (by rfl) ⟨483873, by rfl⟩ : syracuseStep 1290329 = 967747) B967747
theorem B864395 : Blo 381763 864395 := bstep (se 1 (by rfl) ⟨648296, by rfl⟩ : syracuseStep 864395 = 1296593) B1296593
theorem B864449 : Blo 381763 864449 := bstep (se 2 (by rfl) ⟨324168, by rfl⟩ : syracuseStep 864449 = 648337) B648337
theorem B1388951 : Blo 381763 1388951 := bstep (se 1 (by rfl) ⟨1041713, by rfl⟩ : syracuseStep 1388951 = 2083427) B2083427
theorem B864665 : Blo 381763 864665 := bstep (se 2 (by rfl) ⟨324249, by rfl⟩ : syracuseStep 864665 = 648499) B648499
theorem B864755 : Blo 381763 864755 := bstep (se 1 (by rfl) ⟨648566, by rfl⟩ : syracuseStep 864755 = 1297133) B1297133
theorem B864791 : Blo 381763 864791 := bstep (se 1 (by rfl) ⟨648593, by rfl⟩ : syracuseStep 864791 = 1297187) B1297187
theorem B1094219 : Blo 381763 1094219 := bstep (se 1 (by rfl) ⟨820664, by rfl⟩ : syracuseStep 1094219 = 1641329) B1641329
theorem B864971 : Blo 381763 864971 := bstep (se 1 (by rfl) ⟨648728, by rfl⟩ : syracuseStep 864971 = 1297457) B1297457
theorem B1749721 : Blo 381763 1749721 := bstep (se 2 (by rfl) ⟨656145, by rfl⟩ : syracuseStep 1749721 = 1312291) B1312291
theorem B865025 : Blo 381763 865025 := bstep (se 2 (by rfl) ⟨324384, by rfl⟩ : syracuseStep 865025 = 648769) B648769
theorem B1291031 : Blo 381763 1291031 := bstep (se 1 (by rfl) ⟨968273, by rfl⟩ : syracuseStep 1291031 = 1936547) B1936547
theorem B1454993 : Blo 381763 1454993 := bstep (se 2 (by rfl) ⟨545622, by rfl⟩ : syracuseStep 1454993 = 1091245) B1091245
theorem B865241 : Blo 381763 865241 := bstep (se 2 (by rfl) ⟨324465, by rfl⟩ : syracuseStep 865241 = 648931) B648931
theorem B865331 : Blo 381763 865331 := bstep (se 1 (by rfl) ⟨648998, by rfl⟩ : syracuseStep 865331 = 1297997) B1297997
theorem B865367 : Blo 381763 865367 := bstep (se 1 (by rfl) ⟨649025, by rfl⟩ : syracuseStep 865367 = 1298051) B1298051
theorem B865547 : Blo 381763 865547 := bstep (se 1 (by rfl) ⟨649160, by rfl⟩ : syracuseStep 865547 = 1298321) B1298321
theorem B1291571 : Blo 381763 1291571 := bstep (se 1 (by rfl) ⟨968678, by rfl⟩ : syracuseStep 1291571 = 1937357) B1937357
theorem B1750337 : Blo 381763 1750337 := bstep (se 2 (by rfl) ⟨656376, by rfl⟩ : syracuseStep 1750337 = 1312753) B1312753
theorem B865601 : Blo 381763 865601 := bstep (se 2 (by rfl) ⟨324600, by rfl⟩ : syracuseStep 865601 = 649201) B649201
theorem B2635139 : Blo 381763 2635139 := bstep (se 1 (by rfl) ⟨1976354, by rfl⟩ : syracuseStep 2635139 = 3952709) B3952709
theorem B1553843 : Blo 381763 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B865817 : Blo 381763 865817 := bstep (se 2 (by rfl) ⟨324681, by rfl⟩ : syracuseStep 865817 = 649363) B649363
theorem B1291841 : Blo 381763 1291841 := bstep (se 2 (by rfl) ⟨484440, by rfl⟩ : syracuseStep 1291841 = 968881) B968881
theorem B1455691 : Blo 381763 1455691 := bstep (se 1 (by rfl) ⟨1091768, by rfl⟩ : syracuseStep 1455691 = 2183537) B2183537
theorem B865907 : Blo 381763 865907 := bstep (se 1 (by rfl) ⟨649430, by rfl⟩ : syracuseStep 865907 = 1298861) B1298861
theorem B11941507 : Blo 381763 11941507 := bstep (se 1 (by rfl) ⟨8956130, by rfl⟩ : syracuseStep 11941507 = 17912261) B17912261
theorem B865943 : Blo 381763 865943 := bstep (se 1 (by rfl) ⟨649457, by rfl⟩ : syracuseStep 865943 = 1298915) B1298915
theorem B7354061 : Blo 381763 7354061 := bstep (se 3 (by rfl) ⟨1378886, by rfl⟩ : syracuseStep 7354061 = 2757773) B2757773
theorem B4896557 : Blo 381763 4896557 := bstep (se 3 (by rfl) ⟨918104, by rfl⟩ : syracuseStep 4896557 = 1836209) B1836209
theorem B866123 : Blo 381763 866123 := bstep (se 1 (by rfl) ⟨649592, by rfl⟩ : syracuseStep 866123 = 1299185) B1299185
theorem B1455965 : Blo 381763 1455965 := bstep (se 3 (by rfl) ⟨272993, by rfl⟩ : syracuseStep 1455965 = 545987) B545987
theorem B866177 : Blo 381763 866177 := bstep (se 2 (by rfl) ⟨324816, by rfl⟩ : syracuseStep 866177 = 649633) B649633
theorem B866393 : Blo 381763 866393 := bstep (se 2 (by rfl) ⟨324897, by rfl⟩ : syracuseStep 866393 = 649795) B649795
theorem B1292381 : Blo 381763 1292381 := bstep (se 3 (by rfl) ⟨242321, by rfl⟩ : syracuseStep 1292381 = 484643) B484643
theorem B866483 : Blo 381763 866483 := bstep (se 1 (by rfl) ⟨649862, by rfl⟩ : syracuseStep 866483 = 1299725) B1299725
theorem B866519 : Blo 381763 866519 := bstep (se 1 (by rfl) ⟨649889, by rfl⟩ : syracuseStep 866519 = 1299779) B1299779
theorem B407927 : Blo 381763 407927 := bstep (se 1 (by rfl) ⟨305945, by rfl⟩ : syracuseStep 407927 = 611891) B611891
theorem B866699 : Blo 381763 866699 := bstep (se 1 (by rfl) ⟨650024, by rfl⟩ : syracuseStep 866699 = 1300049) B1300049
theorem B866753 : Blo 381763 866753 := bstep (se 2 (by rfl) ⟨325032, by rfl⟩ : syracuseStep 866753 = 650065) B650065
theorem B1456663 : Blo 381763 1456663 := bstep (se 1 (by rfl) ⟨1092497, by rfl⟩ : syracuseStep 1456663 = 2184995) B2184995
theorem B866969 : Blo 381763 866969 := bstep (se 2 (by rfl) ⟨325113, by rfl⟩ : syracuseStep 866969 = 650227) B650227
theorem B867059 : Blo 381763 867059 := bstep (se 1 (by rfl) ⟨650294, by rfl⟩ : syracuseStep 867059 = 1300589) B1300589
theorem B867095 : Blo 381763 867095 := bstep (se 1 (by rfl) ⟨650321, by rfl⟩ : syracuseStep 867095 = 1300643) B1300643
theorem B867275 : Blo 381763 867275 := bstep (se 1 (by rfl) ⟨650456, by rfl⟩ : syracuseStep 867275 = 1300913) B1300913
theorem B3685337 : Blo 381763 3685337 := bstep (se 2 (by rfl) ⟨1382001, by rfl⟩ : syracuseStep 3685337 = 2764003) B2764003
theorem B867329 : Blo 381763 867329 := bstep (se 2 (by rfl) ⟨325248, by rfl⟩ : syracuseStep 867329 = 650497) B650497
theorem B1293515 : Blo 381763 1293515 := bstep (se 1 (by rfl) ⟨970136, by rfl⟩ : syracuseStep 1293515 = 1940273) B1940273
theorem B867545 : Blo 381763 867545 := bstep (se 2 (by rfl) ⟨325329, by rfl⟩ : syracuseStep 867545 = 650659) B650659
theorem B1457453 : Blo 381763 1457453 := bstep (se 3 (by rfl) ⟨273272, by rfl⟩ : syracuseStep 1457453 = 546545) B546545
theorem B867635 : Blo 381763 867635 := bstep (se 1 (by rfl) ⟨650726, by rfl⟩ : syracuseStep 867635 = 1301453) B1301453
theorem B572747 : Blo 381763 572747 := bstep (se 1 (by rfl) ⟨429560, by rfl⟩ : syracuseStep 572747 = 859121) B859121
theorem B572759 : Blo 381763 572759 := bstep (se 1 (by rfl) ⟨429569, by rfl⟩ : syracuseStep 572759 = 859139) B859139
theorem B867671 : Blo 381763 867671 := bstep (se 1 (by rfl) ⟨650753, by rfl⟩ : syracuseStep 867671 = 1301507) B1301507
theorem B1949021 : Blo 381763 1949021 := bstep (se 3 (by rfl) ⟨365441, by rfl⟩ : syracuseStep 1949021 = 730883) B730883
theorem B572825 : Blo 381763 572825 := bstep (se 2 (by rfl) ⟨214809, by rfl⟩ : syracuseStep 572825 = 429619) B429619
theorem B1293785 : Blo 381763 1293785 := bstep (se 2 (by rfl) ⟨485169, by rfl⟩ : syracuseStep 1293785 = 970339) B970339
theorem B572939 : Blo 381763 572939 := bstep (se 1 (by rfl) ⟨429704, by rfl⟩ : syracuseStep 572939 = 859409) B859409
theorem B867851 : Blo 381763 867851 := bstep (se 1 (by rfl) ⟨650888, by rfl⟩ : syracuseStep 867851 = 1301777) B1301777
theorem B572951 : Blo 381763 572951 := bstep (se 1 (by rfl) ⟨429713, by rfl⟩ : syracuseStep 572951 = 859427) B859427
theorem B867905 : Blo 381763 867905 := bstep (se 2 (by rfl) ⟨325464, by rfl⟩ : syracuseStep 867905 = 650929) B650929
theorem B573017 : Blo 381763 573017 := bstep (se 2 (by rfl) ⟨214881, by rfl⟩ : syracuseStep 573017 = 429763) B429763
theorem B573131 : Blo 381763 573131 := bstep (se 1 (by rfl) ⟨429848, by rfl⟩ : syracuseStep 573131 = 859697) B859697
theorem B3096269 : Blo 381763 3096269 := bstep (se 3 (by rfl) ⟨580550, by rfl⟩ : syracuseStep 3096269 = 1161101) B1161101
theorem B573143 : Blo 381763 573143 := bstep (se 1 (by rfl) ⟨429857, by rfl⟩ : syracuseStep 573143 = 859715) B859715
theorem B573209 : Blo 381763 573209 := bstep (se 2 (by rfl) ⟨214953, by rfl⟩ : syracuseStep 573209 = 429907) B429907
theorem B3489581 : Blo 381763 3489581 := bstep (se 3 (by rfl) ⟨654296, by rfl⟩ : syracuseStep 3489581 = 1308593) B1308593
theorem B966451 : Blo 381763 966451 := bstep (se 1 (by rfl) ⟨724838, by rfl⟩ : syracuseStep 966451 = 1449677) B1449677
theorem B1032025 : Blo 381763 1032025 := bstep (se 2 (by rfl) ⟨387009, by rfl⟩ : syracuseStep 1032025 = 774019) B774019
theorem B573323 : Blo 381763 573323 := bstep (se 1 (by rfl) ⟨429992, by rfl⟩ : syracuseStep 573323 = 859985) B859985
theorem B573335 : Blo 381763 573335 := bstep (se 1 (by rfl) ⟨430001, by rfl⟩ : syracuseStep 573335 = 860003) B860003
theorem B966593 : Blo 381763 966593 := bstep (se 2 (by rfl) ⟨362472, by rfl⟩ : syracuseStep 966593 = 724945) B724945
theorem B2768845 : Blo 381763 2768845 := bstep (se 3 (by rfl) ⟨519158, by rfl⟩ : syracuseStep 2768845 = 1038317) B1038317
theorem B573401 : Blo 381763 573401 := bstep (se 2 (by rfl) ⟨215025, by rfl⟩ : syracuseStep 573401 = 430051) B430051
theorem B573515 : Blo 381763 573515 := bstep (se 1 (by rfl) ⟨430136, by rfl⟩ : syracuseStep 573515 = 860273) B860273
theorem B573527 : Blo 381763 573527 := bstep (se 1 (by rfl) ⟨430145, by rfl⟩ : syracuseStep 573527 = 860291) B860291
theorem B1294487 : Blo 381763 1294487 := bstep (se 1 (by rfl) ⟨970865, by rfl⟩ : syracuseStep 1294487 = 1941731) B1941731
theorem B573593 : Blo 381763 573593 := bstep (se 2 (by rfl) ⟨215097, by rfl⟩ : syracuseStep 573593 = 430195) B430195
theorem B573707 : Blo 381763 573707 := bstep (se 1 (by rfl) ⟨430280, by rfl⟩ : syracuseStep 573707 = 860561) B860561
theorem B2179345 : Blo 381763 2179345 := bstep (se 2 (by rfl) ⟨817254, by rfl⟩ : syracuseStep 2179345 = 1634509) B1634509
theorem B573719 : Blo 381763 573719 := bstep (se 1 (by rfl) ⟨430289, by rfl⟩ : syracuseStep 573719 = 860579) B860579
theorem B573785 : Blo 381763 573785 := bstep (se 2 (by rfl) ⟨215169, by rfl⟩ : syracuseStep 573785 = 430339) B430339
theorem B573899 : Blo 381763 573899 := bstep (se 1 (by rfl) ⟨430424, by rfl⟩ : syracuseStep 573899 = 860849) B860849
theorem B410059 : Blo 381763 410059 := bstep (se 1 (by rfl) ⟨307544, by rfl⟩ : syracuseStep 410059 = 615089) B615089
theorem B573911 : Blo 381763 573911 := bstep (se 1 (by rfl) ⟨430433, by rfl⟩ : syracuseStep 573911 = 860867) B860867
theorem B573977 : Blo 381763 573977 := bstep (se 2 (by rfl) ⟨215241, by rfl⟩ : syracuseStep 573977 = 430483) B430483
theorem B574091 : Blo 381763 574091 := bstep (se 1 (by rfl) ⟨430568, by rfl⟩ : syracuseStep 574091 = 861137) B861137
theorem B574103 : Blo 381763 574103 := bstep (se 1 (by rfl) ⟨430577, by rfl⟩ : syracuseStep 574103 = 861155) B861155
theorem B1295027 : Blo 381763 1295027 := bstep (se 1 (by rfl) ⟨971270, by rfl⟩ : syracuseStep 1295027 = 1942541) B1942541
theorem B1458881 : Blo 381763 1458881 := bstep (se 2 (by rfl) ⟨547080, by rfl⟩ : syracuseStep 1458881 = 1094161) B1094161
theorem B574169 : Blo 381763 574169 := bstep (se 2 (by rfl) ⟨215313, by rfl⟩ : syracuseStep 574169 = 430627) B430627
theorem B574283 : Blo 381763 574283 := bstep (se 1 (by rfl) ⟨430712, by rfl⟩ : syracuseStep 574283 = 861425) B861425
theorem B574295 : Blo 381763 574295 := bstep (se 1 (by rfl) ⟨430721, by rfl⟩ : syracuseStep 574295 = 861443) B861443
theorem B574361 : Blo 381763 574361 := bstep (se 2 (by rfl) ⟨215385, by rfl⟩ : syracuseStep 574361 = 430771) B430771
theorem B1295297 : Blo 381763 1295297 := bstep (se 2 (by rfl) ⟨485736, by rfl⟩ : syracuseStep 1295297 = 971473) B971473
theorem B574475 : Blo 381763 574475 := bstep (se 1 (by rfl) ⟨430856, by rfl⟩ : syracuseStep 574475 = 861713) B861713
theorem B574487 : Blo 381763 574487 := bstep (se 1 (by rfl) ⟨430865, by rfl⟩ : syracuseStep 574487 = 861731) B861731
theorem B1754135 : Blo 381763 1754135 := bstep (se 1 (by rfl) ⟨1315601, by rfl⟩ : syracuseStep 1754135 = 2631203) B2631203
theorem B574553 : Blo 381763 574553 := bstep (se 2 (by rfl) ⟨215457, by rfl⟩ : syracuseStep 574553 = 430915) B430915
theorem B1557593 : Blo 381763 1557593 := bstep (se 2 (by rfl) ⟨584097, by rfl⟩ : syracuseStep 1557593 = 1168195) B1168195
theorem B967859 : Blo 381763 967859 := bstep (se 1 (by rfl) ⟨725894, by rfl⟩ : syracuseStep 967859 = 1451789) B1451789
theorem B1033409 : Blo 381763 1033409 := bstep (se 2 (by rfl) ⟨387528, by rfl⟩ : syracuseStep 1033409 = 775057) B775057
theorem B574667 : Blo 381763 574667 := bstep (se 1 (by rfl) ⟨431000, by rfl⟩ : syracuseStep 574667 = 862001) B862001
theorem B574679 : Blo 381763 574679 := bstep (se 1 (by rfl) ⟨431009, by rfl⟩ : syracuseStep 574679 = 862019) B862019
theorem B574745 : Blo 381763 574745 := bstep (se 2 (by rfl) ⟨215529, by rfl⟩ : syracuseStep 574745 = 431059) B431059
theorem B574859 : Blo 381763 574859 := bstep (se 1 (by rfl) ⟨431144, by rfl⟩ : syracuseStep 574859 = 862289) B862289
theorem B574871 : Blo 381763 574871 := bstep (se 1 (by rfl) ⟨431153, by rfl⟩ : syracuseStep 574871 = 862307) B862307
theorem B1951127 : Blo 381763 1951127 := bstep (se 1 (by rfl) ⟨1463345, by rfl⟩ : syracuseStep 1951127 = 2926691) B2926691
theorem B574937 : Blo 381763 574937 := bstep (se 2 (by rfl) ⟨215601, by rfl⟩ : syracuseStep 574937 = 431203) B431203
theorem B1295837 : Blo 381763 1295837 := bstep (se 3 (by rfl) ⟨242969, by rfl⟩ : syracuseStep 1295837 = 485939) B485939
theorem B575051 : Blo 381763 575051 := bstep (se 1 (by rfl) ⟨431288, by rfl⟩ : syracuseStep 575051 = 862577) B862577
theorem B575063 : Blo 381763 575063 := bstep (se 1 (by rfl) ⟨431297, by rfl⟩ : syracuseStep 575063 = 862595) B862595
theorem B575129 : Blo 381763 575129 := bstep (se 2 (by rfl) ⟨215673, by rfl⟩ : syracuseStep 575129 = 431347) B431347
theorem B968395 : Blo 381763 968395 := bstep (se 1 (by rfl) ⟨726296, by rfl⟩ : syracuseStep 968395 = 1452593) B1452593
theorem B575243 : Blo 381763 575243 := bstep (se 1 (by rfl) ⟨431432, by rfl⟩ : syracuseStep 575243 = 862865) B862865
theorem B575255 : Blo 381763 575255 := bstep (se 1 (by rfl) ⟨431441, by rfl⟩ : syracuseStep 575255 = 862883) B862883
theorem B968537 : Blo 381763 968537 := bstep (se 2 (by rfl) ⟨363201, by rfl⟩ : syracuseStep 968537 = 726403) B726403
theorem B575321 : Blo 381763 575321 := bstep (se 2 (by rfl) ⟨215745, by rfl⟩ : syracuseStep 575321 = 431491) B431491
theorem B575435 : Blo 381763 575435 := bstep (se 1 (by rfl) ⟨431576, by rfl⟩ : syracuseStep 575435 = 863153) B863153
theorem B575447 : Blo 381763 575447 := bstep (se 1 (by rfl) ⟨431585, by rfl⟩ : syracuseStep 575447 = 863171) B863171
theorem B575513 : Blo 381763 575513 := bstep (se 2 (by rfl) ⟨215817, by rfl⟩ : syracuseStep 575513 = 431635) B431635
theorem B575627 : Blo 381763 575627 := bstep (se 1 (by rfl) ⟨431720, by rfl⟩ : syracuseStep 575627 = 863441) B863441
theorem B1460369 : Blo 381763 1460369 := bstep (se 2 (by rfl) ⟨547638, by rfl⟩ : syracuseStep 1460369 = 1095277) B1095277
theorem B575639 : Blo 381763 575639 := bstep (se 1 (by rfl) ⟨431729, by rfl⟩ : syracuseStep 575639 = 863459) B863459
theorem B575705 : Blo 381763 575705 := bstep (se 2 (by rfl) ⟨215889, by rfl⟩ : syracuseStep 575705 = 431779) B431779
theorem B575819 : Blo 381763 575819 := bstep (se 1 (by rfl) ⟨431864, by rfl⟩ : syracuseStep 575819 = 863729) B863729
theorem B575831 : Blo 381763 575831 := bstep (se 1 (by rfl) ⟨431873, by rfl⟩ : syracuseStep 575831 = 863747) B863747
theorem B575897 : Blo 381763 575897 := bstep (se 2 (by rfl) ⟨215961, by rfl⟩ : syracuseStep 575897 = 431923) B431923
theorem B576011 : Blo 381763 576011 := bstep (se 1 (by rfl) ⟨432008, by rfl⟩ : syracuseStep 576011 = 864017) B864017
theorem B576023 : Blo 381763 576023 := bstep (se 1 (by rfl) ⟨432017, by rfl⟩ : syracuseStep 576023 = 864035) B864035
theorem B1296971 : Blo 381763 1296971 := bstep (se 1 (by rfl) ⟨972728, by rfl⟩ : syracuseStep 1296971 = 1945457) B1945457
theorem B576089 : Blo 381763 576089 := bstep (se 2 (by rfl) ⟨216033, by rfl⟩ : syracuseStep 576089 = 432067) B432067
theorem B1460825 : Blo 381763 1460825 := bstep (se 2 (by rfl) ⟨547809, by rfl⟩ : syracuseStep 1460825 = 1095619) B1095619
theorem B3492503 : Blo 381763 3492503 := bstep (se 1 (by rfl) ⟨2619377, by rfl⟩ : syracuseStep 3492503 = 5238755) B5238755
theorem B969367 : Blo 381763 969367 := bstep (se 1 (by rfl) ⟨727025, by rfl⟩ : syracuseStep 969367 = 1454051) B1454051
theorem B576203 : Blo 381763 576203 := bstep (se 1 (by rfl) ⟨432152, by rfl⟩ : syracuseStep 576203 = 864305) B864305
theorem B576215 : Blo 381763 576215 := bstep (se 1 (by rfl) ⟨432161, by rfl⟩ : syracuseStep 576215 = 864323) B864323
theorem B1035031 : Blo 381763 1035031 := bstep (se 1 (by rfl) ⟨776273, by rfl⟩ : syracuseStep 1035031 = 1552547) B1552547
theorem B576281 : Blo 381763 576281 := bstep (se 2 (by rfl) ⟨216105, by rfl⟩ : syracuseStep 576281 = 432211) B432211
theorem B1461037 : Blo 381763 1461037 := bstep (se 3 (by rfl) ⟨273944, by rfl⟩ : syracuseStep 1461037 = 547889) B547889
theorem B1297241 : Blo 381763 1297241 := bstep (se 2 (by rfl) ⟨486465, by rfl⟩ : syracuseStep 1297241 = 972931) B972931
theorem B2902877 : Blo 381763 2902877 := bstep (se 3 (by rfl) ⟨544289, by rfl⟩ : syracuseStep 2902877 = 1088579) B1088579
theorem B576395 : Blo 381763 576395 := bstep (se 1 (by rfl) ⟨432296, by rfl⟩ : syracuseStep 576395 = 864593) B864593
theorem B576407 : Blo 381763 576407 := bstep (se 1 (by rfl) ⟨432305, by rfl⟩ : syracuseStep 576407 = 864611) B864611
theorem B576473 : Blo 381763 576473 := bstep (se 2 (by rfl) ⟨216177, by rfl⟩ : syracuseStep 576473 = 432355) B432355
theorem B969803 : Blo 381763 969803 := bstep (se 1 (by rfl) ⟨727352, by rfl⟩ : syracuseStep 969803 = 1454705) B1454705
theorem B576587 : Blo 381763 576587 := bstep (se 1 (by rfl) ⟨432440, by rfl⟩ : syracuseStep 576587 = 864881) B864881
theorem B576599 : Blo 381763 576599 := bstep (se 1 (by rfl) ⟨432449, by rfl⟩ : syracuseStep 576599 = 864899) B864899
theorem B1461341 : Blo 381763 1461341 := bstep (se 3 (by rfl) ⟨274001, by rfl⟩ : syracuseStep 1461341 = 548003) B548003
theorem B576665 : Blo 381763 576665 := bstep (se 2 (by rfl) ⟨216249, by rfl⟩ : syracuseStep 576665 = 432499) B432499
theorem B576779 : Blo 381763 576779 := bstep (se 1 (by rfl) ⟨432584, by rfl⟩ : syracuseStep 576779 = 865169) B865169
theorem B576791 : Blo 381763 576791 := bstep (se 1 (by rfl) ⟨432593, by rfl⟩ : syracuseStep 576791 = 865187) B865187
theorem B576857 : Blo 381763 576857 := bstep (se 2 (by rfl) ⟨216321, by rfl⟩ : syracuseStep 576857 = 432643) B432643
theorem B544153 : Blo 381763 544153 := bstep (se 2 (by rfl) ⟨204057, by rfl⟩ : syracuseStep 544153 = 408115) B408115
theorem B970177 : Blo 381763 970177 := bstep (se 2 (by rfl) ⟨363816, by rfl⟩ : syracuseStep 970177 = 727633) B727633
theorem B576971 : Blo 381763 576971 := bstep (se 1 (by rfl) ⟨432728, by rfl⟩ : syracuseStep 576971 = 865457) B865457
theorem B576983 : Blo 381763 576983 := bstep (se 1 (by rfl) ⟨432737, by rfl⟩ : syracuseStep 576983 = 865475) B865475
theorem B544267 : Blo 381763 544267 := bstep (se 1 (by rfl) ⟨408200, by rfl⟩ : syracuseStep 544267 = 816401) B816401
theorem B1396241 : Blo 381763 1396241 := bstep (se 2 (by rfl) ⟨523590, by rfl⟩ : syracuseStep 1396241 = 1047181) B1047181
theorem B1297943 : Blo 381763 1297943 := bstep (se 1 (by rfl) ⟨973457, by rfl⟩ : syracuseStep 1297943 = 1946915) B1946915
theorem B577049 : Blo 381763 577049 := bstep (se 2 (by rfl) ⟨216393, by rfl⟩ : syracuseStep 577049 = 432787) B432787
theorem B2182787 : Blo 381763 2182787 := bstep (se 1 (by rfl) ⟨1637090, by rfl⟩ : syracuseStep 2182787 = 3274181) B3274181
theorem B577163 : Blo 381763 577163 := bstep (se 1 (by rfl) ⟨432872, by rfl⟩ : syracuseStep 577163 = 865745) B865745
theorem B577175 : Blo 381763 577175 := bstep (se 1 (by rfl) ⟨432881, by rfl⟩ : syracuseStep 577175 = 865763) B865763
theorem B577241 : Blo 381763 577241 := bstep (se 2 (by rfl) ⟨216465, by rfl⟩ : syracuseStep 577241 = 432931) B432931
theorem B4378373 : Blo 381763 4378373 := bstep (se 4 (by rfl) ⟨410472, by rfl⟩ : syracuseStep 4378373 = 820945) B820945
theorem B577355 : Blo 381763 577355 := bstep (se 1 (by rfl) ⟨433016, by rfl⟩ : syracuseStep 577355 = 866033) B866033
theorem B577367 : Blo 381763 577367 := bstep (se 1 (by rfl) ⟨433025, by rfl⟩ : syracuseStep 577367 = 866051) B866051
theorem B577433 : Blo 381763 577433 := bstep (se 2 (by rfl) ⟨216537, by rfl⟩ : syracuseStep 577433 = 433075) B433075
theorem B1560493 : Blo 381763 1560493 := bstep (se 3 (by rfl) ⟨292592, by rfl⟩ : syracuseStep 1560493 = 585185) B585185
theorem B577547 : Blo 381763 577547 := bstep (se 1 (by rfl) ⟨433160, by rfl⟩ : syracuseStep 577547 = 866321) B866321
theorem B970775 : Blo 381763 970775 := bstep (se 1 (by rfl) ⟨728081, by rfl⟩ : syracuseStep 970775 = 1456163) B1456163
theorem B577559 : Blo 381763 577559 := bstep (se 1 (by rfl) ⟨433169, by rfl⟩ : syracuseStep 577559 = 866339) B866339
theorem B1298483 : Blo 381763 1298483 := bstep (se 1 (by rfl) ⟨973862, by rfl⟩ : syracuseStep 1298483 = 1947725) B1947725
theorem B577625 : Blo 381763 577625 := bstep (se 2 (by rfl) ⟨216609, by rfl⟩ : syracuseStep 577625 = 433219) B433219
theorem B1560721 : Blo 381763 1560721 := bstep (se 2 (by rfl) ⟨585270, by rfl⟩ : syracuseStep 1560721 = 1170541) B1170541
theorem B577739 : Blo 381763 577739 := bstep (se 1 (by rfl) ⟨433304, by rfl⟩ : syracuseStep 577739 = 866609) B866609
theorem B577751 : Blo 381763 577751 := bstep (se 1 (by rfl) ⟨433313, by rfl⟩ : syracuseStep 577751 = 866627) B866627
theorem B577817 : Blo 381763 577817 := bstep (se 2 (by rfl) ⟨216681, by rfl⟩ : syracuseStep 577817 = 433363) B433363
theorem B1298753 : Blo 381763 1298753 := bstep (se 2 (by rfl) ⟨487032, by rfl⟩ : syracuseStep 1298753 = 974065) B974065
theorem B774515 : Blo 381763 774515 := bstep (se 1 (by rfl) ⟨580886, by rfl⟩ : syracuseStep 774515 = 1161773) B1161773
theorem B577931 : Blo 381763 577931 := bstep (se 1 (by rfl) ⟨433448, by rfl⟩ : syracuseStep 577931 = 866897) B866897
theorem B577943 : Blo 381763 577943 := bstep (se 1 (by rfl) ⟨433457, by rfl⟩ : syracuseStep 577943 = 866915) B866915
theorem B578009 : Blo 381763 578009 := bstep (se 2 (by rfl) ⟨216753, by rfl⟩ : syracuseStep 578009 = 433507) B433507
theorem B578123 : Blo 381763 578123 := bstep (se 1 (by rfl) ⟨433592, by rfl⟩ : syracuseStep 578123 = 867185) B867185
theorem B578135 : Blo 381763 578135 := bstep (se 1 (by rfl) ⟨433601, by rfl⟩ : syracuseStep 578135 = 867203) B867203
theorem B1233559 : Blo 381763 1233559 := bstep (se 1 (by rfl) ⟨925169, by rfl⟩ : syracuseStep 1233559 = 1850339) B1850339
theorem B578201 : Blo 381763 578201 := bstep (se 2 (by rfl) ⟨216825, by rfl⟩ : syracuseStep 578201 = 433651) B433651
theorem B578315 : Blo 381763 578315 := bstep (se 1 (by rfl) ⟨433736, by rfl⟩ : syracuseStep 578315 = 867473) B867473
theorem B578327 : Blo 381763 578327 := bstep (se 1 (by rfl) ⟨433745, by rfl⟩ : syracuseStep 578327 = 867491) B867491
theorem B971585 : Blo 381763 971585 := bstep (se 2 (by rfl) ⟨364344, by rfl⟩ : syracuseStep 971585 = 728689) B728689
theorem B381771 : Blo 381763 381771 := bstep (se 1 (by rfl) ⟨286328, by rfl⟩ : syracuseStep 381771 = 572657) B572657
theorem B545611 : Blo 381763 545611 := bstep (se 1 (by rfl) ⟨409208, by rfl⟩ : syracuseStep 545611 = 818417) B818417
theorem B381783 : Blo 381763 381783 := bstep (se 1 (by rfl) ⟨286337, by rfl⟩ : syracuseStep 381783 = 572675) B572675
theorem B578393 : Blo 381763 578393 := bstep (se 2 (by rfl) ⟨216897, by rfl⟩ : syracuseStep 578393 = 433795) B433795
theorem B1299293 : Blo 381763 1299293 := bstep (se 3 (by rfl) ⟨243617, by rfl⟩ : syracuseStep 1299293 = 487235) B487235
theorem B381803 : Blo 381763 381803 := bstep (se 1 (by rfl) ⟨286352, by rfl⟩ : syracuseStep 381803 = 572705) B572705
theorem B381815 : Blo 381763 381815 := bstep (se 1 (by rfl) ⟨286361, by rfl⟩ : syracuseStep 381815 = 572723) B572723
theorem B381835 : Blo 381763 381835 := bstep (se 1 (by rfl) ⟨286376, by rfl⟩ : syracuseStep 381835 = 572753) B572753
theorem B381847 : Blo 381763 381847 := bstep (se 1 (by rfl) ⟨286385, by rfl⟩ : syracuseStep 381847 = 572771) B572771
theorem B381867 : Blo 381763 381867 := bstep (se 1 (by rfl) ⟨286400, by rfl⟩ : syracuseStep 381867 = 572801) B572801
theorem B381879 : Blo 381763 381879 := bstep (se 1 (by rfl) ⟨286409, by rfl⟩ : syracuseStep 381879 = 572819) B572819
theorem B381899 : Blo 381763 381899 := bstep (se 1 (by rfl) ⟨286424, by rfl⟩ : syracuseStep 381899 = 572849) B572849
theorem B578507 : Blo 381763 578507 := bstep (se 1 (by rfl) ⟨433880, by rfl⟩ : syracuseStep 578507 = 867761) B867761
theorem B381911 : Blo 381763 381911 := bstep (se 1 (by rfl) ⟨286433, by rfl⟩ : syracuseStep 381911 = 572867) B572867
theorem B578519 : Blo 381763 578519 := bstep (se 1 (by rfl) ⟨433889, by rfl⟩ : syracuseStep 578519 = 867779) B867779
theorem B381931 : Blo 381763 381931 := bstep (se 1 (by rfl) ⟨286448, by rfl⟩ : syracuseStep 381931 = 572897) B572897
theorem B381943 : Blo 381763 381943 := bstep (se 1 (by rfl) ⟨286457, by rfl⟩ : syracuseStep 381943 = 572915) B572915
theorem B381963 : Blo 381763 381963 := bstep (se 1 (by rfl) ⟨286472, by rfl⟩ : syracuseStep 381963 = 572945) B572945
theorem B381975 : Blo 381763 381975 := bstep (se 1 (by rfl) ⟨286481, by rfl⟩ : syracuseStep 381975 = 572963) B572963
theorem B578585 : Blo 381763 578585 := bstep (se 2 (by rfl) ⟨216969, by rfl⟩ : syracuseStep 578585 = 433939) B433939
theorem B381995 : Blo 381763 381995 := bstep (se 1 (by rfl) ⟨286496, by rfl⟩ : syracuseStep 381995 = 572993) B572993
theorem B382007 : Blo 381763 382007 := bstep (se 1 (by rfl) ⟨286505, by rfl⟩ : syracuseStep 382007 = 573011) B573011
theorem B382027 : Blo 381763 382027 := bstep (se 1 (by rfl) ⟨286520, by rfl⟩ : syracuseStep 382027 = 573041) B573041
theorem B382039 : Blo 381763 382039 := bstep (se 1 (by rfl) ⟨286529, by rfl⟩ : syracuseStep 382039 = 573059) B573059
theorem B545879 : Blo 381763 545879 := bstep (se 1 (by rfl) ⟨409409, by rfl⟩ : syracuseStep 545879 = 818819) B818819
theorem B382059 : Blo 381763 382059 := bstep (se 1 (by rfl) ⟨286544, by rfl⟩ : syracuseStep 382059 = 573089) B573089
theorem B382071 : Blo 381763 382071 := bstep (se 1 (by rfl) ⟨286553, by rfl⟩ : syracuseStep 382071 = 573107) B573107
theorem B382091 : Blo 381763 382091 := bstep (se 1 (by rfl) ⟨286568, by rfl⟩ : syracuseStep 382091 = 573137) B573137
theorem B382103 : Blo 381763 382103 := bstep (se 1 (by rfl) ⟨286577, by rfl⟩ : syracuseStep 382103 = 573155) B573155
theorem B382123 : Blo 381763 382123 := bstep (se 1 (by rfl) ⟨286592, by rfl⟩ : syracuseStep 382123 = 573185) B573185
theorem B382135 : Blo 381763 382135 := bstep (se 1 (by rfl) ⟨286601, by rfl⟩ : syracuseStep 382135 = 573203) B573203
theorem B873665 : Blo 381763 873665 := bstep (se 2 (by rfl) ⟨327624, by rfl⟩ : syracuseStep 873665 = 655249) B655249
theorem B382155 : Blo 381763 382155 := bstep (se 1 (by rfl) ⟨286616, by rfl⟩ : syracuseStep 382155 = 573233) B573233
theorem B382167 : Blo 381763 382167 := bstep (se 1 (by rfl) ⟨286625, by rfl⟩ : syracuseStep 382167 = 573251) B573251
theorem B382187 : Blo 381763 382187 := bstep (se 1 (by rfl) ⟨286640, by rfl⟩ : syracuseStep 382187 = 573281) B573281
theorem B382199 : Blo 381763 382199 := bstep (se 1 (by rfl) ⟨286649, by rfl⟩ : syracuseStep 382199 = 573299) B573299
theorem B382219 : Blo 381763 382219 := bstep (se 1 (by rfl) ⟨286664, by rfl⟩ : syracuseStep 382219 = 573329) B573329
theorem B644375 : Blo 381763 644375 := bstep (se 1 (by rfl) ⟨483281, by rfl⟩ : syracuseStep 644375 = 966563) B966563
theorem B382231 : Blo 381763 382231 := bstep (se 1 (by rfl) ⟨286673, by rfl⟩ : syracuseStep 382231 = 573347) B573347
theorem B382251 : Blo 381763 382251 := bstep (se 1 (by rfl) ⟨286688, by rfl⟩ : syracuseStep 382251 = 573377) B573377
theorem B382263 : Blo 381763 382263 := bstep (se 1 (by rfl) ⟨286697, by rfl⟩ : syracuseStep 382263 = 573395) B573395
theorem B382283 : Blo 381763 382283 := bstep (se 1 (by rfl) ⟨286712, by rfl⟩ : syracuseStep 382283 = 573425) B573425
theorem B382295 : Blo 381763 382295 := bstep (se 1 (by rfl) ⟨286721, by rfl⟩ : syracuseStep 382295 = 573443) B573443
theorem B972121 : Blo 381763 972121 := bstep (se 2 (by rfl) ⟨364545, by rfl⟩ : syracuseStep 972121 = 729091) B729091
theorem B382315 : Blo 381763 382315 := bstep (se 1 (by rfl) ⟨286736, by rfl⟩ : syracuseStep 382315 = 573473) B573473
theorem B382327 : Blo 381763 382327 := bstep (se 1 (by rfl) ⟨286745, by rfl⟩ : syracuseStep 382327 = 573491) B573491
theorem B382347 : Blo 381763 382347 := bstep (se 1 (by rfl) ⟨286760, by rfl⟩ : syracuseStep 382347 = 573521) B573521
theorem B644503 : Blo 381763 644503 := bstep (se 1 (by rfl) ⟨483377, by rfl⟩ : syracuseStep 644503 = 966755) B966755
theorem B382359 : Blo 381763 382359 := bstep (se 1 (by rfl) ⟨286769, by rfl⟩ : syracuseStep 382359 = 573539) B573539
theorem B775577 : Blo 381763 775577 := bstep (se 2 (by rfl) ⟨290841, by rfl⟩ : syracuseStep 775577 = 581683) B581683
theorem B382379 : Blo 381763 382379 := bstep (se 1 (by rfl) ⟨286784, by rfl⟩ : syracuseStep 382379 = 573569) B573569
theorem B382391 : Blo 381763 382391 := bstep (se 1 (by rfl) ⟨286793, by rfl⟩ : syracuseStep 382391 = 573587) B573587
theorem B382411 : Blo 381763 382411 := bstep (se 1 (by rfl) ⟨286808, by rfl⟩ : syracuseStep 382411 = 573617) B573617
theorem B1234379 : Blo 381763 1234379 := bstep (se 1 (by rfl) ⟨925784, by rfl⟩ : syracuseStep 1234379 = 1851569) B1851569
theorem B382423 : Blo 381763 382423 := bstep (se 1 (by rfl) ⟨286817, by rfl⟩ : syracuseStep 382423 = 573635) B573635
theorem B382443 : Blo 381763 382443 := bstep (se 1 (by rfl) ⟨286832, by rfl⟩ : syracuseStep 382443 = 573665) B573665
theorem B382455 : Blo 381763 382455 := bstep (se 1 (by rfl) ⟨286841, by rfl⟩ : syracuseStep 382455 = 573683) B573683
theorem B382475 : Blo 381763 382475 := bstep (se 1 (by rfl) ⟨286856, by rfl⟩ : syracuseStep 382475 = 573713) B573713
theorem B382487 : Blo 381763 382487 := bstep (se 1 (by rfl) ⟨286865, by rfl⟩ : syracuseStep 382487 = 573731) B573731
theorem B382507 : Blo 381763 382507 := bstep (se 1 (by rfl) ⟨286880, by rfl⟩ : syracuseStep 382507 = 573761) B573761
theorem B382519 : Blo 381763 382519 := bstep (se 1 (by rfl) ⟨286889, by rfl⟩ : syracuseStep 382519 = 573779) B573779
theorem B382539 : Blo 381763 382539 := bstep (se 1 (by rfl) ⟨286904, by rfl⟩ : syracuseStep 382539 = 573809) B573809
theorem B382551 : Blo 381763 382551 := bstep (se 1 (by rfl) ⟨286913, by rfl⟩ : syracuseStep 382551 = 573827) B573827
theorem B9557597 : Blo 381763 9557597 := bstep (se 3 (by rfl) ⟨1792049, by rfl⟩ : syracuseStep 9557597 = 3584099) B3584099
theorem B382571 : Blo 381763 382571 := bstep (se 1 (by rfl) ⟨286928, by rfl⟩ : syracuseStep 382571 = 573857) B573857
theorem B382583 : Blo 381763 382583 := bstep (se 1 (by rfl) ⟨286937, by rfl⟩ : syracuseStep 382583 = 573875) B573875
theorem B1463939 : Blo 381763 1463939 := bstep (se 1 (by rfl) ⟨1097954, by rfl⟩ : syracuseStep 1463939 = 2195909) B2195909
theorem B382603 : Blo 381763 382603 := bstep (se 1 (by rfl) ⟨286952, by rfl⟩ : syracuseStep 382603 = 573905) B573905
theorem B1463953 : Blo 381763 1463953 := bstep (se 2 (by rfl) ⟨548982, by rfl⟩ : syracuseStep 1463953 = 1097965) B1097965
theorem B382615 : Blo 381763 382615 := bstep (se 1 (by rfl) ⟨286961, by rfl⟩ : syracuseStep 382615 = 573923) B573923
theorem B611993 : Blo 381763 611993 := bstep (se 2 (by rfl) ⟨229497, by rfl⟩ : syracuseStep 611993 = 458995) B458995
theorem B382635 : Blo 381763 382635 := bstep (se 1 (by rfl) ⟨286976, by rfl⟩ : syracuseStep 382635 = 573953) B573953
theorem B382647 : Blo 381763 382647 := bstep (se 1 (by rfl) ⟨286985, by rfl⟩ : syracuseStep 382647 = 573971) B573971
theorem B382667 : Blo 381763 382667 := bstep (se 1 (by rfl) ⟨287000, by rfl⟩ : syracuseStep 382667 = 574001) B574001
theorem B382679 : Blo 381763 382679 := bstep (se 1 (by rfl) ⟨287009, by rfl⟩ : syracuseStep 382679 = 574019) B574019
theorem B382699 : Blo 381763 382699 := bstep (se 1 (by rfl) ⟨287024, by rfl⟩ : syracuseStep 382699 = 574049) B574049
theorem B382711 : Blo 381763 382711 := bstep (se 1 (by rfl) ⟨287033, by rfl⟩ : syracuseStep 382711 = 574067) B574067
theorem B2807557 : Blo 381763 2807557 := bstep (se 4 (by rfl) ⟨263208, by rfl⟩ : syracuseStep 2807557 = 526417) B526417
theorem B382731 : Blo 381763 382731 := bstep (se 1 (by rfl) ⟨287048, by rfl⟩ : syracuseStep 382731 = 574097) B574097
theorem B382743 : Blo 381763 382743 := bstep (se 1 (by rfl) ⟨287057, by rfl⟩ : syracuseStep 382743 = 574115) B574115
theorem B612121 : Blo 381763 612121 := bstep (se 2 (by rfl) ⟨229545, by rfl⟩ : syracuseStep 612121 = 459091) B459091
theorem B382763 : Blo 381763 382763 := bstep (se 1 (by rfl) ⟨287072, by rfl⟩ : syracuseStep 382763 = 574145) B574145
theorem B382775 : Blo 381763 382775 := bstep (se 1 (by rfl) ⟨287081, by rfl⟩ : syracuseStep 382775 = 574163) B574163
theorem B382795 : Blo 381763 382795 := bstep (se 1 (by rfl) ⟨287096, by rfl⟩ : syracuseStep 382795 = 574193) B574193
theorem B382807 : Blo 381763 382807 := bstep (se 1 (by rfl) ⟨287105, by rfl⟩ : syracuseStep 382807 = 574211) B574211
theorem B382827 : Blo 381763 382827 := bstep (se 1 (by rfl) ⟨287120, by rfl⟩ : syracuseStep 382827 = 574241) B574241
theorem B382839 : Blo 381763 382839 := bstep (se 1 (by rfl) ⟨287129, by rfl⟩ : syracuseStep 382839 = 574259) B574259
theorem B382859 : Blo 381763 382859 := bstep (se 1 (by rfl) ⟨287144, by rfl⟩ : syracuseStep 382859 = 574289) B574289
theorem B382871 : Blo 381763 382871 := bstep (se 1 (by rfl) ⟨287153, by rfl⟩ : syracuseStep 382871 = 574307) B574307
theorem B382891 : Blo 381763 382891 := bstep (se 1 (by rfl) ⟨287168, by rfl⟩ : syracuseStep 382891 = 574337) B574337
theorem B382903 : Blo 381763 382903 := bstep (se 1 (by rfl) ⟨287177, by rfl⟩ : syracuseStep 382903 = 574355) B574355
theorem B1464257 : Blo 381763 1464257 := bstep (se 2 (by rfl) ⟨549096, by rfl⟩ : syracuseStep 1464257 = 1098193) B1098193
theorem B382923 : Blo 381763 382923 := bstep (se 1 (by rfl) ⟨287192, by rfl⟩ : syracuseStep 382923 = 574385) B574385
theorem B1300427 : Blo 381763 1300427 := bstep (se 1 (by rfl) ⟨975320, by rfl⟩ : syracuseStep 1300427 = 1950641) B1950641
theorem B382935 : Blo 381763 382935 := bstep (se 1 (by rfl) ⟨287201, by rfl⟩ : syracuseStep 382935 = 574403) B574403
theorem B2185177 : Blo 381763 2185177 := bstep (se 2 (by rfl) ⟨819441, by rfl⟩ : syracuseStep 2185177 = 1638883) B1638883
theorem B382955 : Blo 381763 382955 := bstep (se 1 (by rfl) ⟨287216, by rfl⟩ : syracuseStep 382955 = 574433) B574433
theorem B382967 : Blo 381763 382967 := bstep (se 1 (by rfl) ⟨287225, by rfl⟩ : syracuseStep 382967 = 574451) B574451
theorem B645131 : Blo 381763 645131 := bstep (se 1 (by rfl) ⟨483848, by rfl⟩ : syracuseStep 645131 = 967697) B967697
theorem B382987 : Blo 381763 382987 := bstep (se 1 (by rfl) ⟨287240, by rfl⟩ : syracuseStep 382987 = 574481) B574481
theorem B382999 : Blo 381763 382999 := bstep (se 1 (by rfl) ⟨287249, by rfl⟩ : syracuseStep 382999 = 574499) B574499
theorem B546841 : Blo 381763 546841 := bstep (se 2 (by rfl) ⟨205065, by rfl⟩ : syracuseStep 546841 = 410131) B410131
theorem B383019 : Blo 381763 383019 := bstep (se 1 (by rfl) ⟨287264, by rfl⟩ : syracuseStep 383019 = 574529) B574529
theorem B383031 : Blo 381763 383031 := bstep (se 1 (by rfl) ⟨287273, by rfl⟩ : syracuseStep 383031 = 574547) B574547
theorem B2447435 : Blo 381763 2447435 := bstep (se 1 (by rfl) ⟨1835576, by rfl⟩ : syracuseStep 2447435 = 3671153) B3671153
theorem B5036107 : Blo 381763 5036107 := bstep (se 1 (by rfl) ⟨3777080, by rfl⟩ : syracuseStep 5036107 = 7554161) B7554161
theorem B383051 : Blo 381763 383051 := bstep (se 1 (by rfl) ⟨287288, by rfl⟩ : syracuseStep 383051 = 574577) B574577
theorem B383063 : Blo 381763 383063 := bstep (se 1 (by rfl) ⟨287297, by rfl⟩ : syracuseStep 383063 = 574595) B574595
theorem B874585 : Blo 381763 874585 := bstep (se 2 (by rfl) ⟨327969, by rfl⟩ : syracuseStep 874585 = 655939) B655939
theorem B1235033 : Blo 381763 1235033 := bstep (se 2 (by rfl) ⟨463137, by rfl⟩ : syracuseStep 1235033 = 926275) B926275
theorem B383083 : Blo 381763 383083 := bstep (se 1 (by rfl) ⟨287312, by rfl⟩ : syracuseStep 383083 = 574625) B574625
theorem B383095 : Blo 381763 383095 := bstep (se 1 (by rfl) ⟨287321, by rfl⟩ : syracuseStep 383095 = 574643) B574643
theorem B645259 : Blo 381763 645259 := bstep (se 1 (by rfl) ⟨483944, by rfl⟩ : syracuseStep 645259 = 967889) B967889
theorem B383115 : Blo 381763 383115 := bstep (se 1 (by rfl) ⟨287336, by rfl⟩ : syracuseStep 383115 = 574673) B574673
theorem B383127 : Blo 381763 383127 := bstep (se 1 (by rfl) ⟨287345, by rfl⟩ : syracuseStep 383127 = 574691) B574691
theorem B383147 : Blo 381763 383147 := bstep (se 1 (by rfl) ⟨287360, by rfl⟩ : syracuseStep 383147 = 574721) B574721
theorem B383159 : Blo 381763 383159 := bstep (se 1 (by rfl) ⟨287369, by rfl⟩ : syracuseStep 383159 = 574739) B574739
theorem B383179 : Blo 381763 383179 := bstep (se 1 (by rfl) ⟨287384, by rfl⟩ : syracuseStep 383179 = 574769) B574769
theorem B4741325 : Blo 381763 4741325 := bstep (se 3 (by rfl) ⟨888998, by rfl⟩ : syracuseStep 4741325 = 1777997) B1777997
theorem B383191 : Blo 381763 383191 := bstep (se 1 (by rfl) ⟨287393, by rfl⟩ : syracuseStep 383191 = 574787) B574787
theorem B1300697 : Blo 381763 1300697 := bstep (se 2 (by rfl) ⟨487761, by rfl⟩ : syracuseStep 1300697 = 975523) B975523
theorem B383211 : Blo 381763 383211 := bstep (se 1 (by rfl) ⟨287408, by rfl⟩ : syracuseStep 383211 = 574817) B574817
theorem B383223 : Blo 381763 383223 := bstep (se 1 (by rfl) ⟨287417, by rfl⟩ : syracuseStep 383223 = 574835) B574835
theorem B383243 : Blo 381763 383243 := bstep (se 1 (by rfl) ⟨287432, by rfl⟩ : syracuseStep 383243 = 574865) B574865
theorem B383255 : Blo 381763 383255 := bstep (se 1 (by rfl) ⟨287441, by rfl⟩ : syracuseStep 383255 = 574883) B574883
theorem B645401 : Blo 381763 645401 := bstep (se 2 (by rfl) ⟨242025, by rfl⟩ : syracuseStep 645401 = 484051) B484051
theorem B383275 : Blo 381763 383275 := bstep (se 1 (by rfl) ⟨287456, by rfl⟩ : syracuseStep 383275 = 574913) B574913
theorem B2283821 : Blo 381763 2283821 := bstep (se 3 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 2283821 = 856433) B856433
theorem B383287 : Blo 381763 383287 := bstep (se 1 (by rfl) ⟨287465, by rfl⟩ : syracuseStep 383287 = 574931) B574931
theorem B383307 : Blo 381763 383307 := bstep (se 1 (by rfl) ⟨287480, by rfl⟩ : syracuseStep 383307 = 574961) B574961
theorem B383319 : Blo 381763 383319 := bstep (se 1 (by rfl) ⟨287489, by rfl⟩ : syracuseStep 383319 = 574979) B574979
theorem B383339 : Blo 381763 383339 := bstep (se 1 (by rfl) ⟨287504, by rfl⟩ : syracuseStep 383339 = 575009) B575009
theorem B383351 : Blo 381763 383351 := bstep (se 1 (by rfl) ⟨287513, by rfl⟩ : syracuseStep 383351 = 575027) B575027
theorem B383371 : Blo 381763 383371 := bstep (se 1 (by rfl) ⟨287528, by rfl⟩ : syracuseStep 383371 = 575057) B575057
theorem B383383 : Blo 381763 383383 := bstep (se 1 (by rfl) ⟨287537, by rfl⟩ : syracuseStep 383383 = 575075) B575075
theorem B645529 : Blo 381763 645529 := bstep (se 2 (by rfl) ⟨242073, by rfl⟩ : syracuseStep 645529 = 484147) B484147
theorem B383403 : Blo 381763 383403 := bstep (se 1 (by rfl) ⟨287552, by rfl⟩ : syracuseStep 383403 = 575105) B575105
theorem B973235 : Blo 381763 973235 := bstep (se 1 (by rfl) ⟨729926, by rfl⟩ : syracuseStep 973235 = 1459853) B1459853
theorem B383415 : Blo 381763 383415 := bstep (se 1 (by rfl) ⟨287561, by rfl⟩ : syracuseStep 383415 = 575123) B575123
theorem B383435 : Blo 381763 383435 := bstep (se 1 (by rfl) ⟨287576, by rfl⟩ : syracuseStep 383435 = 575153) B575153
theorem B383447 : Blo 381763 383447 := bstep (se 1 (by rfl) ⟨287585, by rfl⟩ : syracuseStep 383447 = 575171) B575171
theorem B383467 : Blo 381763 383467 := bstep (se 1 (by rfl) ⟨287600, by rfl⟩ : syracuseStep 383467 = 575201) B575201
theorem B383479 : Blo 381763 383479 := bstep (se 1 (by rfl) ⟨287609, by rfl⟩ : syracuseStep 383479 = 575219) B575219
theorem B383499 : Blo 381763 383499 := bstep (se 1 (by rfl) ⟨287624, by rfl⟩ : syracuseStep 383499 = 575249) B575249
theorem B383511 : Blo 381763 383511 := bstep (se 1 (by rfl) ⟨287633, by rfl⟩ : syracuseStep 383511 = 575267) B575267
theorem B383531 : Blo 381763 383531 := bstep (se 1 (by rfl) ⟨287648, by rfl⟩ : syracuseStep 383531 = 575297) B575297
theorem B383543 : Blo 381763 383543 := bstep (se 1 (by rfl) ⟨287657, by rfl⟩ : syracuseStep 383543 = 575315) B575315
theorem B383563 : Blo 381763 383563 := bstep (se 1 (by rfl) ⟨287672, by rfl⟩ : syracuseStep 383563 = 575345) B575345
theorem B383575 : Blo 381763 383575 := bstep (se 1 (by rfl) ⟨287681, by rfl⟩ : syracuseStep 383575 = 575363) B575363
theorem B2775653 : Blo 381763 2775653 := bstep (se 4 (by rfl) ⟨260217, by rfl⟩ : syracuseStep 2775653 = 520435) B520435
theorem B383595 : Blo 381763 383595 := bstep (se 1 (by rfl) ⟨287696, by rfl⟩ : syracuseStep 383595 = 575393) B575393
theorem B383607 : Blo 381763 383607 := bstep (se 1 (by rfl) ⟨287705, by rfl⟩ : syracuseStep 383607 = 575411) B575411
theorem B383627 : Blo 381763 383627 := bstep (se 1 (by rfl) ⟨287720, by rfl⟩ : syracuseStep 383627 = 575441) B575441
theorem B383639 : Blo 381763 383639 := bstep (se 1 (by rfl) ⟨287729, by rfl⟩ : syracuseStep 383639 = 575459) B575459
theorem B383659 : Blo 381763 383659 := bstep (se 1 (by rfl) ⟨287744, by rfl⟩ : syracuseStep 383659 = 575489) B575489
theorem B383671 : Blo 381763 383671 := bstep (se 1 (by rfl) ⟨287753, by rfl⟩ : syracuseStep 383671 = 575507) B575507
theorem B383691 : Blo 381763 383691 := bstep (se 1 (by rfl) ⟨287768, by rfl⟩ : syracuseStep 383691 = 575537) B575537
theorem B383703 : Blo 381763 383703 := bstep (se 1 (by rfl) ⟨287777, by rfl⟩ : syracuseStep 383703 = 575555) B575555
theorem B973529 : Blo 381763 973529 := bstep (se 2 (by rfl) ⟨365073, by rfl⟩ : syracuseStep 973529 = 730147) B730147
theorem B383723 : Blo 381763 383723 := bstep (se 1 (by rfl) ⟨287792, by rfl⟩ : syracuseStep 383723 = 575585) B575585
theorem B383735 : Blo 381763 383735 := bstep (se 1 (by rfl) ⟨287801, by rfl⟩ : syracuseStep 383735 = 575603) B575603
theorem B383755 : Blo 381763 383755 := bstep (se 1 (by rfl) ⟨287816, by rfl⟩ : syracuseStep 383755 = 575633) B575633
theorem B383767 : Blo 381763 383767 := bstep (se 1 (by rfl) ⟨287825, by rfl⟩ : syracuseStep 383767 = 575651) B575651
theorem B383787 : Blo 381763 383787 := bstep (se 1 (by rfl) ⟨287840, by rfl⟩ : syracuseStep 383787 = 575681) B575681
theorem B383799 : Blo 381763 383799 := bstep (se 1 (by rfl) ⟨287849, by rfl⟩ : syracuseStep 383799 = 575699) B575699
theorem B383819 : Blo 381763 383819 := bstep (se 1 (by rfl) ⟨287864, by rfl⟩ : syracuseStep 383819 = 575729) B575729
theorem B1170251 : Blo 381763 1170251 := bstep (se 1 (by rfl) ⟨877688, by rfl⟩ : syracuseStep 1170251 = 1755377) B1755377
theorem B383831 : Blo 381763 383831 := bstep (se 1 (by rfl) ⟨287873, by rfl⟩ : syracuseStep 383831 = 575747) B575747
theorem B6216547 : Blo 381763 6216547 := bstep (se 1 (by rfl) ⟨4662410, by rfl⟩ : syracuseStep 6216547 = 9324821) B9324821
theorem B383851 : Blo 381763 383851 := bstep (se 1 (by rfl) ⟨287888, by rfl⟩ : syracuseStep 383851 = 575777) B575777
theorem B383863 : Blo 381763 383863 := bstep (se 1 (by rfl) ⟨287897, by rfl⟩ : syracuseStep 383863 = 575795) B575795
theorem B383883 : Blo 381763 383883 := bstep (se 1 (by rfl) ⟨287912, by rfl⟩ : syracuseStep 383883 = 575825) B575825
theorem B2186135 : Blo 381763 2186135 := bstep (se 1 (by rfl) ⟨1639601, by rfl⟩ : syracuseStep 2186135 = 3279203) B3279203
theorem B383895 : Blo 381763 383895 := bstep (se 1 (by rfl) ⟨287921, by rfl⟩ : syracuseStep 383895 = 575843) B575843
theorem B1301399 : Blo 381763 1301399 := bstep (se 1 (by rfl) ⟨976049, by rfl⟩ : syracuseStep 1301399 = 1952099) B1952099
theorem B383915 : Blo 381763 383915 := bstep (se 1 (by rfl) ⟨287936, by rfl⟩ : syracuseStep 383915 = 575873) B575873
theorem B383927 : Blo 381763 383927 := bstep (se 1 (by rfl) ⟨287945, by rfl⟩ : syracuseStep 383927 = 575891) B575891
theorem B383947 : Blo 381763 383947 := bstep (se 1 (by rfl) ⟨287960, by rfl⟩ : syracuseStep 383947 = 575921) B575921
theorem B646103 : Blo 381763 646103 := bstep (se 1 (by rfl) ⟨484577, by rfl⟩ : syracuseStep 646103 = 969155) B969155
theorem B383959 : Blo 381763 383959 := bstep (se 1 (by rfl) ⟨287969, by rfl⟩ : syracuseStep 383959 = 575939) B575939
theorem B383979 : Blo 381763 383979 := bstep (se 1 (by rfl) ⟨287984, by rfl⟩ : syracuseStep 383979 = 575969) B575969
theorem B383991 : Blo 381763 383991 := bstep (se 1 (by rfl) ⟨287993, by rfl⟩ : syracuseStep 383991 = 575987) B575987
theorem B384011 : Blo 381763 384011 := bstep (se 1 (by rfl) ⟨288008, by rfl⟩ : syracuseStep 384011 = 576017) B576017
theorem B384023 : Blo 381763 384023 := bstep (se 1 (by rfl) ⟨288017, by rfl⟩ : syracuseStep 384023 = 576035) B576035
theorem B384043 : Blo 381763 384043 := bstep (se 1 (by rfl) ⟨288032, by rfl⟩ : syracuseStep 384043 = 576065) B576065
theorem B384055 : Blo 381763 384055 := bstep (se 1 (by rfl) ⟨288041, by rfl⟩ : syracuseStep 384055 = 576083) B576083
theorem B384075 : Blo 381763 384075 := bstep (se 1 (by rfl) ⟨288056, by rfl⟩ : syracuseStep 384075 = 576113) B576113
theorem B646231 : Blo 381763 646231 := bstep (se 1 (by rfl) ⟨484673, by rfl⟩ : syracuseStep 646231 = 969347) B969347
theorem B384087 : Blo 381763 384087 := bstep (se 1 (by rfl) ⟨288065, by rfl⟩ : syracuseStep 384087 = 576131) B576131
theorem B384107 : Blo 381763 384107 := bstep (se 1 (by rfl) ⟨288080, by rfl⟩ : syracuseStep 384107 = 576161) B576161
theorem B384119 : Blo 381763 384119 := bstep (se 1 (by rfl) ⟨288089, by rfl⟩ : syracuseStep 384119 = 576179) B576179
theorem B384139 : Blo 381763 384139 := bstep (se 1 (by rfl) ⟨288104, by rfl⟩ : syracuseStep 384139 = 576209) B576209
theorem B384151 : Blo 381763 384151 := bstep (se 1 (by rfl) ⟨288113, by rfl⟩ : syracuseStep 384151 = 576227) B576227
theorem B384171 : Blo 381763 384171 := bstep (se 1 (by rfl) ⟨288128, by rfl⟩ : syracuseStep 384171 = 576257) B576257
theorem B384183 : Blo 381763 384183 := bstep (se 1 (by rfl) ⟨288137, by rfl⟩ : syracuseStep 384183 = 576275) B576275
theorem B384203 : Blo 381763 384203 := bstep (se 1 (by rfl) ⟨288152, by rfl⟩ : syracuseStep 384203 = 576305) B576305
theorem B384215 : Blo 381763 384215 := bstep (se 1 (by rfl) ⟨288161, by rfl⟩ : syracuseStep 384215 = 576323) B576323
theorem B384235 : Blo 381763 384235 := bstep (se 1 (by rfl) ⟨288176, by rfl⟩ : syracuseStep 384235 = 576353) B576353
theorem B384247 : Blo 381763 384247 := bstep (se 1 (by rfl) ⟨288185, by rfl⟩ : syracuseStep 384247 = 576371) B576371
theorem B384267 : Blo 381763 384267 := bstep (se 1 (by rfl) ⟨288200, by rfl⟩ : syracuseStep 384267 = 576401) B576401
theorem B384279 : Blo 381763 384279 := bstep (se 1 (by rfl) ⟨288209, by rfl⟩ : syracuseStep 384279 = 576419) B576419
theorem B384299 : Blo 381763 384299 := bstep (se 1 (by rfl) ⟨288224, by rfl⟩ : syracuseStep 384299 = 576449) B576449
theorem B384311 : Blo 381763 384311 := bstep (se 1 (by rfl) ⟨288233, by rfl⟩ : syracuseStep 384311 = 576467) B576467
theorem B384331 : Blo 381763 384331 := bstep (se 1 (by rfl) ⟨288248, by rfl⟩ : syracuseStep 384331 = 576497) B576497
theorem B875863 : Blo 381763 875863 := bstep (se 1 (by rfl) ⟨656897, by rfl⟩ : syracuseStep 875863 = 1313795) B1313795
theorem B384343 : Blo 381763 384343 := bstep (se 1 (by rfl) ⟨288257, by rfl⟩ : syracuseStep 384343 = 576515) B576515
theorem B384363 : Blo 381763 384363 := bstep (se 1 (by rfl) ⟨288272, by rfl⟩ : syracuseStep 384363 = 576545) B576545
theorem B384375 : Blo 381763 384375 := bstep (se 1 (by rfl) ⟨288281, by rfl⟩ : syracuseStep 384375 = 576563) B576563
theorem B384395 : Blo 381763 384395 := bstep (se 1 (by rfl) ⟨288296, by rfl⟩ : syracuseStep 384395 = 576593) B576593
theorem B384407 : Blo 381763 384407 := bstep (se 1 (by rfl) ⟨288305, by rfl⟩ : syracuseStep 384407 = 576611) B576611
theorem B384427 : Blo 381763 384427 := bstep (se 1 (by rfl) ⟨288320, by rfl⟩ : syracuseStep 384427 = 576641) B576641
theorem B1301939 : Blo 381763 1301939 := bstep (se 1 (by rfl) ⟨976454, by rfl⟩ : syracuseStep 1301939 = 1952909) B1952909
theorem B384439 : Blo 381763 384439 := bstep (se 1 (by rfl) ⟨288329, by rfl⟩ : syracuseStep 384439 = 576659) B576659
theorem B384459 : Blo 381763 384459 := bstep (se 1 (by rfl) ⟨288344, by rfl⟩ : syracuseStep 384459 = 576689) B576689
theorem B548299 : Blo 381763 548299 := bstep (se 1 (by rfl) ⟨411224, by rfl⟩ : syracuseStep 548299 = 822449) B822449
theorem B384471 : Blo 381763 384471 := bstep (se 1 (by rfl) ⟨288353, by rfl⟩ : syracuseStep 384471 = 576707) B576707
theorem B548311 : Blo 381763 548311 := bstep (se 1 (by rfl) ⟨411233, by rfl⟩ : syracuseStep 548311 = 822467) B822467
theorem B384491 : Blo 381763 384491 := bstep (se 1 (by rfl) ⟨288368, by rfl⟩ : syracuseStep 384491 = 576737) B576737
theorem B384503 : Blo 381763 384503 := bstep (se 1 (by rfl) ⟨288377, by rfl⟩ : syracuseStep 384503 = 576755) B576755
theorem B384523 : Blo 381763 384523 := bstep (se 1 (by rfl) ⟨288392, by rfl⟩ : syracuseStep 384523 = 576785) B576785
theorem B384535 : Blo 381763 384535 := bstep (se 1 (by rfl) ⟨288401, by rfl⟩ : syracuseStep 384535 = 576803) B576803
theorem B384555 : Blo 381763 384555 := bstep (se 1 (by rfl) ⟨288416, by rfl⟩ : syracuseStep 384555 = 576833) B576833
theorem B384567 : Blo 381763 384567 := bstep (se 1 (by rfl) ⟨288425, by rfl⟩ : syracuseStep 384567 = 576851) B576851
theorem B384587 : Blo 381763 384587 := bstep (se 1 (by rfl) ⟨288440, by rfl⟩ : syracuseStep 384587 = 576881) B576881
theorem B384599 : Blo 381763 384599 := bstep (se 1 (by rfl) ⟨288449, by rfl⟩ : syracuseStep 384599 = 576899) B576899
theorem B384619 : Blo 381763 384619 := bstep (se 1 (by rfl) ⟨288464, by rfl⟩ : syracuseStep 384619 = 576929) B576929
theorem B384631 : Blo 381763 384631 := bstep (se 1 (by rfl) ⟨288473, by rfl⟩ : syracuseStep 384631 = 576947) B576947
theorem B384651 : Blo 381763 384651 := bstep (se 1 (by rfl) ⟨288488, by rfl⟩ : syracuseStep 384651 = 576977) B576977
theorem B384663 : Blo 381763 384663 := bstep (se 1 (by rfl) ⟨288497, by rfl⟩ : syracuseStep 384663 = 576995) B576995
theorem B384683 : Blo 381763 384683 := bstep (se 1 (by rfl) ⟨288512, by rfl⟩ : syracuseStep 384683 = 577025) B577025
theorem B2612915 : Blo 381763 2612915 := bstep (se 1 (by rfl) ⟨1959686, by rfl⟩ : syracuseStep 2612915 = 3919373) B3919373
theorem B2449075 : Blo 381763 2449075 := bstep (se 1 (by rfl) ⟨1836806, by rfl⟩ : syracuseStep 2449075 = 3673613) B3673613
theorem B384695 : Blo 381763 384695 := bstep (se 1 (by rfl) ⟨288521, by rfl⟩ : syracuseStep 384695 = 577043) B577043
theorem B646859 : Blo 381763 646859 := bstep (se 1 (by rfl) ⟨485144, by rfl⟩ : syracuseStep 646859 = 970289) B970289
theorem B384715 : Blo 381763 384715 := bstep (se 1 (by rfl) ⟨288536, by rfl⟩ : syracuseStep 384715 = 577073) B577073
theorem B384727 : Blo 381763 384727 := bstep (se 1 (by rfl) ⟨288545, by rfl⟩ : syracuseStep 384727 = 577091) B577091
theorem B384747 : Blo 381763 384747 := bstep (se 1 (by rfl) ⟨288560, by rfl⟩ : syracuseStep 384747 = 577121) B577121
theorem B384759 : Blo 381763 384759 := bstep (se 1 (by rfl) ⟨288569, by rfl⟩ : syracuseStep 384759 = 577139) B577139
theorem B384779 : Blo 381763 384779 := bstep (se 1 (by rfl) ⟨288584, by rfl⟩ : syracuseStep 384779 = 577169) B577169
theorem B384791 : Blo 381763 384791 := bstep (se 1 (by rfl) ⟨288593, by rfl⟩ : syracuseStep 384791 = 577187) B577187
theorem B1171223 : Blo 381763 1171223 := bstep (se 1 (by rfl) ⟨878417, by rfl⟩ : syracuseStep 1171223 = 1756835) B1756835
theorem B384811 : Blo 381763 384811 := bstep (se 1 (by rfl) ⟨288608, by rfl⟩ : syracuseStep 384811 = 577217) B577217
theorem B384823 : Blo 381763 384823 := bstep (se 1 (by rfl) ⟨288617, by rfl⟩ : syracuseStep 384823 = 577235) B577235
theorem B646987 : Blo 381763 646987 := bstep (se 1 (by rfl) ⟨485240, by rfl⟩ : syracuseStep 646987 = 970481) B970481
theorem B384843 : Blo 381763 384843 := bstep (se 1 (by rfl) ⟨288632, by rfl⟩ : syracuseStep 384843 = 577265) B577265
theorem B384855 : Blo 381763 384855 := bstep (se 1 (by rfl) ⟨288641, by rfl⟩ : syracuseStep 384855 = 577283) B577283
theorem B384875 : Blo 381763 384875 := bstep (se 1 (by rfl) ⟨288656, by rfl⟩ : syracuseStep 384875 = 577313) B577313
theorem B384887 : Blo 381763 384887 := bstep (se 1 (by rfl) ⟨288665, by rfl⟩ : syracuseStep 384887 = 577331) B577331
theorem B384907 : Blo 381763 384907 := bstep (se 1 (by rfl) ⟨288680, by rfl⟩ : syracuseStep 384907 = 577361) B577361
theorem B384919 : Blo 381763 384919 := bstep (se 1 (by rfl) ⟨288689, by rfl⟩ : syracuseStep 384919 = 577379) B577379
theorem B384939 : Blo 381763 384939 := bstep (se 1 (by rfl) ⟨288704, by rfl⟩ : syracuseStep 384939 = 577409) B577409
theorem B384951 : Blo 381763 384951 := bstep (se 1 (by rfl) ⟨288713, by rfl⟩ : syracuseStep 384951 = 577427) B577427
theorem B384971 : Blo 381763 384971 := bstep (se 1 (by rfl) ⟨288728, by rfl⟩ : syracuseStep 384971 = 577457) B577457
theorem B384983 : Blo 381763 384983 := bstep (se 1 (by rfl) ⟨288737, by rfl⟩ : syracuseStep 384983 = 577475) B577475
theorem B647129 : Blo 381763 647129 := bstep (se 2 (by rfl) ⟨242673, by rfl⟩ : syracuseStep 647129 = 485347) B485347
theorem B385003 : Blo 381763 385003 := bstep (se 1 (by rfl) ⟨288752, by rfl⟩ : syracuseStep 385003 = 577505) B577505
theorem B385015 : Blo 381763 385015 := bstep (se 1 (by rfl) ⟨288761, by rfl⟩ : syracuseStep 385015 = 577523) B577523
theorem B385035 : Blo 381763 385035 := bstep (se 1 (by rfl) ⟨288776, by rfl⟩ : syracuseStep 385035 = 577553) B577553
theorem B385047 : Blo 381763 385047 := bstep (se 1 (by rfl) ⟨288785, by rfl⟩ : syracuseStep 385047 = 577571) B577571
theorem B385067 : Blo 381763 385067 := bstep (se 1 (by rfl) ⟨288800, by rfl⟩ : syracuseStep 385067 = 577601) B577601
theorem B385079 : Blo 381763 385079 := bstep (se 1 (by rfl) ⟨288809, by rfl⟩ : syracuseStep 385079 = 577619) B577619
theorem B483403 : Blo 381763 483403 := bstep (se 1 (by rfl) ⟨362552, by rfl⟩ : syracuseStep 483403 = 725105) B725105
theorem B385099 : Blo 381763 385099 := bstep (se 1 (by rfl) ⟨288824, by rfl⟩ : syracuseStep 385099 = 577649) B577649
theorem B385111 : Blo 381763 385111 := bstep (se 1 (by rfl) ⟨288833, by rfl⟩ : syracuseStep 385111 = 577667) B577667
theorem B647257 : Blo 381763 647257 := bstep (se 2 (by rfl) ⟨242721, by rfl⟩ : syracuseStep 647257 = 485443) B485443
theorem B385131 : Blo 381763 385131 := bstep (se 1 (by rfl) ⟨288848, by rfl⟩ : syracuseStep 385131 = 577697) B577697
theorem B385143 : Blo 381763 385143 := bstep (se 1 (by rfl) ⟨288857, by rfl⟩ : syracuseStep 385143 = 577715) B577715
theorem B385163 : Blo 381763 385163 := bstep (se 1 (by rfl) ⟨288872, by rfl⟩ : syracuseStep 385163 = 577745) B577745
theorem B385175 : Blo 381763 385175 := bstep (se 1 (by rfl) ⟨288881, by rfl⟩ : syracuseStep 385175 = 577763) B577763
theorem B385195 : Blo 381763 385195 := bstep (se 1 (by rfl) ⟨288896, by rfl⟩ : syracuseStep 385195 = 577793) B577793
theorem B385207 : Blo 381763 385207 := bstep (se 1 (by rfl) ⟨288905, by rfl⟩ : syracuseStep 385207 = 577811) B577811
theorem B385227 : Blo 381763 385227 := bstep (se 1 (by rfl) ⟨288920, by rfl⟩ : syracuseStep 385227 = 577841) B577841
theorem B385239 : Blo 381763 385239 := bstep (se 1 (by rfl) ⟨288929, by rfl⟩ : syracuseStep 385239 = 577859) B577859
theorem B385259 : Blo 381763 385259 := bstep (se 1 (by rfl) ⟨288944, by rfl⟩ : syracuseStep 385259 = 577889) B577889
theorem B385271 : Blo 381763 385271 := bstep (se 1 (by rfl) ⟨288953, by rfl⟩ : syracuseStep 385271 = 577907) B577907
theorem B385291 : Blo 381763 385291 := bstep (se 1 (by rfl) ⟨288968, by rfl⟩ : syracuseStep 385291 = 577937) B577937
theorem B93184277 : Blo 381763 93184277 := bstep (se 6 (by rfl) ⟨2184006, by rfl⟩ : syracuseStep 93184277 = 4368013) B4368013
theorem B385303 : Blo 381763 385303 := bstep (se 1 (by rfl) ⟨288977, by rfl⟩ : syracuseStep 385303 = 577955) B577955
theorem B450859 : Blo 381763 450859 := bstep (se 1 (by rfl) ⟨338144, by rfl⟩ : syracuseStep 450859 = 676289) B676289
theorem B385323 : Blo 381763 385323 := bstep (se 1 (by rfl) ⟨288992, by rfl⟩ : syracuseStep 385323 = 577985) B577985
theorem B385335 : Blo 381763 385335 := bstep (se 1 (by rfl) ⟨289001, by rfl⟩ : syracuseStep 385335 = 578003) B578003
theorem B975179 : Blo 381763 975179 := bstep (se 1 (by rfl) ⟨731384, by rfl⟩ : syracuseStep 975179 = 1462769) B1462769
theorem B385355 : Blo 381763 385355 := bstep (se 1 (by rfl) ⟨289016, by rfl⟩ : syracuseStep 385355 = 578033) B578033
theorem B483671 : Blo 381763 483671 := bstep (se 1 (by rfl) ⟨362753, by rfl⟩ : syracuseStep 483671 = 725507) B725507
theorem B385367 : Blo 381763 385367 := bstep (se 1 (by rfl) ⟨289025, by rfl⟩ : syracuseStep 385367 = 578051) B578051
theorem B1171805 : Blo 381763 1171805 := bstep (se 3 (by rfl) ⟨219713, by rfl⟩ : syracuseStep 1171805 = 439427) B439427
theorem B385387 : Blo 381763 385387 := bstep (se 1 (by rfl) ⟨289040, by rfl⟩ : syracuseStep 385387 = 578081) B578081
theorem B385399 : Blo 381763 385399 := bstep (se 1 (by rfl) ⟨289049, by rfl⟩ : syracuseStep 385399 = 578099) B578099
theorem B385419 : Blo 381763 385419 := bstep (se 1 (by rfl) ⟨289064, by rfl⟩ : syracuseStep 385419 = 578129) B578129
theorem B385431 : Blo 381763 385431 := bstep (se 1 (by rfl) ⟨289073, by rfl⟩ : syracuseStep 385431 = 578147) B578147
theorem B385451 : Blo 381763 385451 := bstep (se 1 (by rfl) ⟨289088, by rfl⟩ : syracuseStep 385451 = 578177) B578177
theorem B385463 : Blo 381763 385463 := bstep (se 1 (by rfl) ⟨289097, by rfl⟩ : syracuseStep 385463 = 578195) B578195
theorem B385483 : Blo 381763 385483 := bstep (se 1 (by rfl) ⟨289112, by rfl⟩ : syracuseStep 385483 = 578225) B578225
theorem B385495 : Blo 381763 385495 := bstep (se 1 (by rfl) ⟨289121, by rfl⟩ : syracuseStep 385495 = 578243) B578243
theorem B385515 : Blo 381763 385515 := bstep (se 1 (by rfl) ⟨289136, by rfl⟩ : syracuseStep 385515 = 578273) B578273
theorem B385527 : Blo 381763 385527 := bstep (se 1 (by rfl) ⟨289145, by rfl⟩ : syracuseStep 385527 = 578291) B578291
theorem B385547 : Blo 381763 385547 := bstep (se 1 (by rfl) ⟨289160, by rfl⟩ : syracuseStep 385547 = 578321) B578321
theorem B385559 : Blo 381763 385559 := bstep (se 1 (by rfl) ⟨289169, by rfl⟩ : syracuseStep 385559 = 578339) B578339
theorem B385579 : Blo 381763 385579 := bstep (se 1 (by rfl) ⟨289184, by rfl⟩ : syracuseStep 385579 = 578369) B578369
theorem B385591 : Blo 381763 385591 := bstep (se 1 (by rfl) ⟨289193, by rfl⟩ : syracuseStep 385591 = 578387) B578387
theorem B385611 : Blo 381763 385611 := bstep (se 1 (by rfl) ⟨289208, by rfl⟩ : syracuseStep 385611 = 578417) B578417
theorem B385623 : Blo 381763 385623 := bstep (se 1 (by rfl) ⟨289217, by rfl⟩ : syracuseStep 385623 = 578435) B578435
theorem B385643 : Blo 381763 385643 := bstep (se 1 (by rfl) ⟨289232, by rfl⟩ : syracuseStep 385643 = 578465) B578465
theorem B385655 : Blo 381763 385655 := bstep (se 1 (by rfl) ⟨289241, by rfl⟩ : syracuseStep 385655 = 578483) B578483
theorem B385675 : Blo 381763 385675 := bstep (se 1 (by rfl) ⟨289256, by rfl⟩ : syracuseStep 385675 = 578513) B578513
theorem B647831 : Blo 381763 647831 := bstep (se 1 (by rfl) ⟨485873, by rfl⟩ : syracuseStep 647831 = 971747) B971747
theorem B385687 : Blo 381763 385687 := bstep (se 1 (by rfl) ⟨289265, by rfl⟩ : syracuseStep 385687 = 578531) B578531
theorem B385707 : Blo 381763 385707 := bstep (se 1 (by rfl) ⟨289280, by rfl⟩ : syracuseStep 385707 = 578561) B578561
theorem B385719 : Blo 381763 385719 := bstep (se 1 (by rfl) ⟨289289, by rfl⟩ : syracuseStep 385719 = 578579) B578579
theorem B385739 : Blo 381763 385739 := bstep (se 1 (by rfl) ⟨289304, by rfl⟩ : syracuseStep 385739 = 578609) B578609
theorem B516823 : Blo 381763 516823 := bstep (se 1 (by rfl) ⟨387617, by rfl⟩ : syracuseStep 516823 = 775235) B775235
theorem B385751 : Blo 381763 385751 := bstep (se 1 (by rfl) ⟨289313, by rfl⟩ : syracuseStep 385751 = 578627) B578627
theorem B647959 : Blo 381763 647959 := bstep (se 1 (by rfl) ⟨485969, by rfl⟩ : syracuseStep 647959 = 971939) B971939
theorem B484375 : Blo 381763 484375 := bstep (se 1 (by rfl) ⟨363281, by rfl⟩ : syracuseStep 484375 = 726563) B726563
theorem B976151 : Blo 381763 976151 := bstep (se 1 (by rfl) ⟨732113, by rfl⟩ : syracuseStep 976151 = 1464227) B1464227
theorem B2188619 : Blo 381763 2188619 := bstep (se 1 (by rfl) ⟨1641464, by rfl⟩ : syracuseStep 2188619 = 3282929) B3282929
theorem B615755 : Blo 381763 615755 := bstep (se 1 (by rfl) ⟨461816, by rfl⟩ : syracuseStep 615755 = 923633) B923633
theorem B648587 : Blo 381763 648587 := bstep (se 1 (by rfl) ⟨486440, by rfl⟩ : syracuseStep 648587 = 972881) B972881
theorem B1631639 : Blo 381763 1631639 := bstep (se 1 (by rfl) ⟨1223729, by rfl⟩ : syracuseStep 1631639 = 2447459) B2447459
theorem B648715 : Blo 381763 648715 := bstep (se 1 (by rfl) ⟨486536, by rfl⟩ : syracuseStep 648715 = 973073) B973073
theorem B648857 : Blo 381763 648857 := bstep (se 2 (by rfl) ⟨243321, by rfl⟩ : syracuseStep 648857 = 486643) B486643
theorem B1631947 : Blo 381763 1631947 := bstep (se 1 (by rfl) ⟨1223960, by rfl⟩ : syracuseStep 1631947 = 2447921) B2447921
theorem B648985 : Blo 381763 648985 := bstep (se 2 (by rfl) ⟨243369, by rfl⟩ : syracuseStep 648985 = 486739) B486739
theorem B2615105 : Blo 381763 2615105 := bstep (se 2 (by rfl) ⟨980664, by rfl⟩ : syracuseStep 2615105 = 1961329) B1961329
theorem B1632221 : Blo 381763 1632221 := bstep (se 3 (by rfl) ⟨306041, by rfl⟩ : syracuseStep 1632221 = 612083) B612083
theorem B2779267 : Blo 381763 2779267 := bstep (se 1 (by rfl) ⟨2084450, by rfl⟩ : syracuseStep 2779267 = 4168901) B4168901
theorem B5335301 : Blo 381763 5335301 := bstep (se 4 (by rfl) ⟨500184, by rfl⟩ : syracuseStep 5335301 = 1000369) B1000369
theorem B616729 : Blo 381763 616729 := bstep (se 2 (by rfl) ⟨231273, by rfl⟩ : syracuseStep 616729 = 462547) B462547
theorem B649559 : Blo 381763 649559 := bstep (se 1 (by rfl) ⟨487169, by rfl⟩ : syracuseStep 649559 = 974339) B974339
theorem B649687 : Blo 381763 649687 := bstep (se 1 (by rfl) ⟨487265, by rfl⟩ : syracuseStep 649687 = 974531) B974531
theorem B616985 : Blo 381763 616985 := bstep (se 2 (by rfl) ⟨231369, by rfl⟩ : syracuseStep 616985 = 462739) B462739
theorem B486091 : Blo 381763 486091 := bstep (se 1 (by rfl) ⟨364568, by rfl⟩ : syracuseStep 486091 = 729137) B729137
theorem B781067 : Blo 381763 781067 := bstep (se 1 (by rfl) ⟨585800, by rfl⟩ : syracuseStep 781067 = 1171601) B1171601
theorem B3107659 : Blo 381763 3107659 := bstep (se 1 (by rfl) ⟨2330744, by rfl⟩ : syracuseStep 3107659 = 4661489) B4661489
theorem B748531 : Blo 381763 748531 := bstep (se 1 (by rfl) ⟨561398, by rfl⟩ : syracuseStep 748531 = 1122797) B1122797
theorem B748595 : Blo 381763 748595 := bstep (se 1 (by rfl) ⟨561446, by rfl⟩ : syracuseStep 748595 = 1122893) B1122893
theorem B650315 : Blo 381763 650315 := bstep (se 1 (by rfl) ⟨487736, by rfl⟩ : syracuseStep 650315 = 975473) B975473
theorem B879731 : Blo 381763 879731 := bstep (se 1 (by rfl) ⟨659798, by rfl⟩ : syracuseStep 879731 = 1319597) B1319597
theorem B781463 : Blo 381763 781463 := bstep (se 1 (by rfl) ⟨586097, by rfl⟩ : syracuseStep 781463 = 1172195) B1172195
theorem B650443 : Blo 381763 650443 := bstep (se 1 (by rfl) ⟨487832, by rfl⟩ : syracuseStep 650443 = 975665) B975665
theorem B1633553 : Blo 381763 1633553 := bstep (se 2 (by rfl) ⟨612582, by rfl⟩ : syracuseStep 1633553 = 1225165) B1225165
theorem B650585 : Blo 381763 650585 := bstep (se 2 (by rfl) ⟨243969, by rfl⟩ : syracuseStep 650585 = 487939) B487939
theorem B1306049 : Blo 381763 1306049 := bstep (se 2 (by rfl) ⟨489768, by rfl⟩ : syracuseStep 1306049 = 979537) B979537
theorem B388567 : Blo 381763 388567 := bstep (se 1 (by rfl) ⟨291425, by rfl⟩ : syracuseStep 388567 = 582851) B582851
theorem B650713 : Blo 381763 650713 := bstep (se 2 (by rfl) ⟨244017, by rfl⟩ : syracuseStep 650713 = 488035) B488035
theorem B487063 : Blo 381763 487063 := bstep (se 1 (by rfl) ⟨365297, by rfl⟩ : syracuseStep 487063 = 730595) B730595
theorem B1994419 : Blo 381763 1994419 := bstep (se 1 (by rfl) ⟨1495814, by rfl⟩ : syracuseStep 1994419 = 2991629) B2991629
theorem B2191283 : Blo 381763 2191283 := bstep (se 1 (by rfl) ⟨1643462, by rfl⟩ : syracuseStep 2191283 = 3286925) B3286925
theorem B6222257 : Blo 381763 6222257 := bstep (se 2 (by rfl) ⟨2333346, by rfl⟩ : syracuseStep 6222257 = 4666693) B4666693
theorem B487883 : Blo 381763 487883 := bstep (se 1 (by rfl) ⟨365912, by rfl⟩ : syracuseStep 487883 = 731825) B731825
theorem B1471277 : Blo 381763 1471277 := bstep (se 3 (by rfl) ⟨275864, by rfl⟩ : syracuseStep 1471277 = 551729) B551729
theorem B3273803 : Blo 381763 3273803 := bstep (se 1 (by rfl) ⟨2455352, by rfl⟩ : syracuseStep 3273803 = 4910705) B4910705
theorem B2192741 : Blo 381763 2192741 := bstep (se 4 (by rfl) ⟨205569, by rfl⟩ : syracuseStep 2192741 = 411139) B411139
theorem B1636013 : Blo 381763 1636013 := bstep (se 3 (by rfl) ⟨306752, by rfl⟩ : syracuseStep 1636013 = 613505) B613505
theorem B390955 : Blo 381763 390955 := bstep (se 1 (by rfl) ⟨293216, by rfl⟩ : syracuseStep 390955 = 586433) B586433
theorem B1963955 : Blo 381763 1963955 := bstep (se 1 (by rfl) ⟨1472966, by rfl⟩ : syracuseStep 1963955 = 2945933) B2945933
theorem B1636355 : Blo 381763 1636355 := bstep (se 1 (by rfl) ⟨1227266, by rfl⟩ : syracuseStep 1636355 = 2454533) B2454533
theorem B2193425 : Blo 381763 2193425 := bstep (se 2 (by rfl) ⟨822534, by rfl⟩ : syracuseStep 2193425 = 1645069) B1645069
theorem B817751 : Blo 381763 817751 := bstep (se 1 (by rfl) ⟨613313, by rfl⟩ : syracuseStep 817751 = 1226627) B1226627
theorem B4651613 : Blo 381763 4651613 := bstep (se 3 (by rfl) ⟨872177, by rfl⟩ : syracuseStep 4651613 = 1744355) B1744355
theorem B5569175 : Blo 381763 5569175 := bstep (se 1 (by rfl) ⟨4176881, by rfl⟩ : syracuseStep 5569175 = 8353763) B8353763
theorem B1669835 : Blo 381763 1669835 := bstep (se 1 (by rfl) ⟨1252376, by rfl⟩ : syracuseStep 1669835 = 2504753) B2504753
theorem B817931 : Blo 381763 817931 := bstep (se 1 (by rfl) ⟨613448, by rfl⟩ : syracuseStep 817931 = 1226897) B1226897
theorem B1309661 : Blo 381763 1309661 := bstep (se 3 (by rfl) ⟨245561, by rfl⟩ : syracuseStep 1309661 = 491123) B491123
theorem B8879179 : Blo 381763 8879179 := bstep (se 1 (by rfl) ⟨6659384, by rfl⟩ : syracuseStep 8879179 = 13318769) B13318769
theorem B3112067 : Blo 381763 3112067 := bstep (se 1 (by rfl) ⟨2334050, by rfl⟩ : syracuseStep 3112067 = 4668101) B4668101
theorem B4685273 : Blo 381763 4685273 := bstep (se 2 (by rfl) ⟨1756977, by rfl⟩ : syracuseStep 4685273 = 3513955) B3513955
theorem B1474141 : Blo 381763 1474141 := bstep (se 3 (by rfl) ⟨276401, by rfl⟩ : syracuseStep 1474141 = 552803) B552803
theorem B1474355 : Blo 381763 1474355 := bstep (se 1 (by rfl) ⟨1105766, by rfl⟩ : syracuseStep 1474355 = 2211533) B2211533
theorem B2916485 : Blo 381763 2916485 := bstep (se 4 (by rfl) ⟨273420, by rfl⟩ : syracuseStep 2916485 = 546841) B546841
theorem B2195657 : Blo 381763 2195657 := bstep (se 2 (by rfl) ⟨823371, by rfl⟩ : syracuseStep 2195657 = 1646743) B1646743
theorem B623033 : Blo 381763 623033 := bstep (se 2 (by rfl) ⟨233637, by rfl⟩ : syracuseStep 623033 = 467275) B467275
theorem B1311275 : Blo 381763 1311275 := bstep (se 1 (by rfl) ⟨983456, by rfl⟩ : syracuseStep 1311275 = 1966913) B1966913
theorem B4162265 : Blo 381763 4162265 := bstep (se 2 (by rfl) ⟨1560849, by rfl⟩ : syracuseStep 4162265 = 3121699) B3121699
theorem B1836055 : Blo 381763 1836055 := bstep (se 1 (by rfl) ⟨1377041, by rfl⟩ : syracuseStep 1836055 = 2754083) B2754083
theorem B918643 : Blo 381763 918643 := bstep (se 1 (by rfl) ⟨688982, by rfl⟩ : syracuseStep 918643 = 1377965) B1377965
theorem B2328335 : Blo 381763 2328335 := bstep (se 1 (by rfl) ⟨1746251, by rfl⟩ : syracuseStep 2328335 = 3492503) B3492503
theorem B1935251 : Blo 381763 1935251 := bstep (se 1 (by rfl) ⟨1451438, by rfl⟩ : syracuseStep 1935251 = 2902877) B2902877
theorem B8259479 : Blo 381763 8259479 := bstep (se 1 (by rfl) ⟨6194609, by rfl⟩ : syracuseStep 8259479 = 12389219) B12389219
theorem B460859 : Blo 381763 460859 := bstep (se 1 (by rfl) ⟨345644, by rfl⟩ : syracuseStep 460859 = 691289) B691289
theorem B985223 : Blo 381763 985223 := bstep (se 1 (by rfl) ⟨738917, by rfl⟩ : syracuseStep 985223 = 1477835) B1477835
theorem B2918915 : Blo 381763 2918915 := bstep (se 1 (by rfl) ⟨2189186, by rfl⟩ : syracuseStep 2918915 = 4378373) B4378373
theorem B4655645 : Blo 381763 4655645 := bstep (se 3 (by rfl) ⟨872933, by rfl⟩ : syracuseStep 4655645 = 1745867) B1745867
theorem B920249 : Blo 381763 920249 := bstep (se 2 (by rfl) ⟨345093, by rfl⟩ : syracuseStep 920249 = 690187) B690187
theorem B920335 : Blo 381763 920335 := bstep (se 1 (by rfl) ⟨690251, by rfl⟩ : syracuseStep 920335 = 1380503) B1380503
theorem B3705689 : Blo 381763 3705689 := bstep (se 2 (by rfl) ⟨1389633, by rfl⟩ : syracuseStep 3705689 = 2779267) B2779267
theorem B822305 : Blo 381763 822305 := bstep (se 2 (by rfl) ⟨308364, by rfl⟩ : syracuseStep 822305 = 616729) B616729
theorem B2755757 : Blo 381763 2755757 := bstep (se 3 (by rfl) ⟨516704, by rfl⟩ : syracuseStep 2755757 = 1033409) B1033409
theorem B3509725 : Blo 381763 3509725 := bstep (se 3 (by rfl) ⟨658073, by rfl⟩ : syracuseStep 3509725 = 1316147) B1316147
theorem B429583 : Blo 381763 429583 := bstep (se 1 (by rfl) ⟨322187, by rfl⟩ : syracuseStep 429583 = 644375) B644375
theorem B1642027 : Blo 381763 1642027 := bstep (se 1 (by rfl) ⟨1231520, by rfl⟩ : syracuseStep 1642027 = 2463041) B2463041
theorem B1380041 : Blo 381763 1380041 := bstep (se 2 (by rfl) ⟨517515, by rfl⟩ : syracuseStep 1380041 = 1035031) B1035031
theorem B462839 : Blo 381763 462839 := bstep (se 1 (by rfl) ⟨347129, by rfl⟩ : syracuseStep 462839 = 694259) B694259
theorem B430087 : Blo 381763 430087 := bstep (se 1 (by rfl) ⟨322565, by rfl⟩ : syracuseStep 430087 = 645131) B645131
theorem B725051 : Blo 381763 725051 := bstep (se 1 (by rfl) ⟨543788, by rfl⟩ : syracuseStep 725051 = 1087577) B1087577
theorem B823355 : Blo 381763 823355 := bstep (se 1 (by rfl) ⟨617516, by rfl⟩ : syracuseStep 823355 = 1235033) B1235033
theorem B430267 : Blo 381763 430267 := bstep (se 1 (by rfl) ⟨322700, by rfl⟩ : syracuseStep 430267 = 645401) B645401
theorem B725537 : Blo 381763 725537 := bstep (se 2 (by rfl) ⟨272076, by rfl⟩ : syracuseStep 725537 = 544153) B544153
theorem B430735 : Blo 381763 430735 := bstep (se 1 (by rfl) ⟨323051, by rfl⟩ : syracuseStep 430735 = 646103) B646103
theorem B13931189 : Blo 381763 13931189 := bstep (se 5 (by rfl) ⟨653024, by rfl⟩ : syracuseStep 13931189 = 1306049) B1306049
theorem B725689 : Blo 381763 725689 := bstep (se 2 (by rfl) ⟨272133, by rfl⟩ : syracuseStep 725689 = 544267) B544267
theorem B922487 : Blo 381763 922487 := bstep (se 1 (by rfl) ⟨691865, by rfl⟩ : syracuseStep 922487 = 1383731) B1383731
theorem B1938329 : Blo 381763 1938329 := bstep (se 2 (by rfl) ⟨726873, by rfl⟩ : syracuseStep 1938329 = 1453747) B1453747
theorem B2659225 : Blo 381763 2659225 := bstep (se 2 (by rfl) ⟨997209, by rfl⟩ : syracuseStep 2659225 = 1994419) B1994419
theorem B3281867 : Blo 381763 3281867 := bstep (se 1 (by rfl) ⟨2461400, by rfl⟩ : syracuseStep 3281867 = 4922801) B4922801
theorem B1741943 : Blo 381763 1741943 := bstep (se 1 (by rfl) ⟨1306457, by rfl⟩ : syracuseStep 1741943 = 2612915) B2612915
theorem B431239 : Blo 381763 431239 := bstep (se 1 (by rfl) ⟨323429, by rfl⟩ : syracuseStep 431239 = 646859) B646859
theorem B4658413 : Blo 381763 4658413 := bstep (se 3 (by rfl) ⟨873452, by rfl⟩ : syracuseStep 4658413 = 1746905) B1746905
theorem B431419 : Blo 381763 431419 := bstep (se 1 (by rfl) ⟨323564, by rfl⟩ : syracuseStep 431419 = 647129) B647129
theorem B3282551 : Blo 381763 3282551 := bstep (se 1 (by rfl) ⟨2461913, by rfl⟩ : syracuseStep 3282551 = 4923827) B4923827
theorem B431887 : Blo 381763 431887 := bstep (se 1 (by rfl) ⟨323915, by rfl⟩ : syracuseStep 431887 = 647831) B647831
theorem B22484789 : Blo 381763 22484789 := bstep (se 5 (by rfl) ⟨1053974, by rfl⟩ : syracuseStep 22484789 = 2107949) B2107949
theorem B1382291 : Blo 381763 1382291 := bstep (se 1 (by rfl) ⟨1036718, by rfl⟩ : syracuseStep 1382291 = 2073437) B2073437
theorem B923795 : Blo 381763 923795 := bstep (se 1 (by rfl) ⟨692846, by rfl⟩ : syracuseStep 923795 = 1385693) B1385693
theorem B923833 : Blo 381763 923833 := bstep (se 2 (by rfl) ⟨346437, by rfl⟩ : syracuseStep 923833 = 692875) B692875
theorem B1644745 : Blo 381763 1644745 := bstep (se 2 (by rfl) ⟨616779, by rfl⟩ : syracuseStep 1644745 = 1233559) B1233559
theorem B432391 : Blo 381763 432391 := bstep (se 1 (by rfl) ⟨324293, by rfl⟩ : syracuseStep 432391 = 648587) B648587
theorem B1087759 : Blo 381763 1087759 := bstep (se 1 (by rfl) ⟨815819, by rfl⟩ : syracuseStep 1087759 = 1631639) B1631639
theorem B2332961 : Blo 381763 2332961 := bstep (se 2 (by rfl) ⟨874860, by rfl⟩ : syracuseStep 2332961 = 1749721) B1749721
theorem B1087805 : Blo 381763 1087805 := bstep (se 3 (by rfl) ⟨203963, by rfl⟩ : syracuseStep 1087805 = 407927) B407927
theorem B727481 : Blo 381763 727481 := bstep (se 2 (by rfl) ⟨272805, by rfl⟩ : syracuseStep 727481 = 545611) B545611
theorem B432571 : Blo 381763 432571 := bstep (se 1 (by rfl) ⟨324428, by rfl⟩ : syracuseStep 432571 = 648857) B648857
theorem B924247 : Blo 381763 924247 := bstep (se 1 (by rfl) ⟨693185, by rfl⟩ : syracuseStep 924247 = 1386371) B1386371
theorem B1088147 : Blo 381763 1088147 := bstep (se 1 (by rfl) ⟨816110, by rfl⟩ : syracuseStep 1088147 = 1632221) B1632221
theorem B433039 : Blo 381763 433039 := bstep (se 1 (by rfl) ⟨324779, by rfl⟩ : syracuseStep 433039 = 649559) B649559
theorem B14851133 : Blo 381763 14851133 := bstep (se 3 (by rfl) ⟨2784587, by rfl⟩ : syracuseStep 14851133 = 5569175) B5569175
theorem B859283 : Blo 381763 859283 := bstep (se 1 (by rfl) ⟨644462, by rfl⟩ : syracuseStep 859283 = 1288925) B1288925
theorem B859337 : Blo 381763 859337 := bstep (se 2 (by rfl) ⟨322251, by rfl⟩ : syracuseStep 859337 = 644503) B644503
theorem B499063 : Blo 381763 499063 := bstep (se 1 (by rfl) ⟨374297, by rfl⟩ : syracuseStep 499063 = 748595) B748595
theorem B433543 : Blo 381763 433543 := bstep (se 1 (by rfl) ⟨325157, by rfl⟩ : syracuseStep 433543 = 650315) B650315
theorem B1940921 : Blo 381763 1940921 := bstep (se 2 (by rfl) ⟨727845, by rfl⟩ : syracuseStep 1940921 = 1455691) B1455691
theorem B1089035 : Blo 381763 1089035 := bstep (se 1 (by rfl) ⟨816776, by rfl⟩ : syracuseStep 1089035 = 1633553) B1633553
theorem B433723 : Blo 381763 433723 := bstep (se 1 (by rfl) ⟨325292, by rfl⟩ : syracuseStep 433723 = 650585) B650585
theorem B2924261 : Blo 381763 2924261 := bstep (se 4 (by rfl) ⟨274149, by rfl⟩ : syracuseStep 2924261 = 548299) B548299
theorem B860039 : Blo 381763 860039 := bstep (se 1 (by rfl) ⟨645029, by rfl⟩ : syracuseStep 860039 = 1290059) B1290059
theorem B860219 : Blo 381763 860219 := bstep (se 1 (by rfl) ⟨645164, by rfl⟩ : syracuseStep 860219 = 1290329) B1290329
theorem B860345 : Blo 381763 860345 := bstep (se 2 (by rfl) ⟨322629, by rfl⟩ : syracuseStep 860345 = 645259) B645259
theorem B925967 : Blo 381763 925967 := bstep (se 1 (by rfl) ⟨694475, by rfl⟩ : syracuseStep 925967 = 1388951) B1388951
theorem B8298845 : Blo 381763 8298845 := bstep (se 3 (by rfl) ⟨1556033, by rfl⟩ : syracuseStep 8298845 = 3112067) B3112067
theorem B729479 : Blo 381763 729479 := bstep (se 1 (by rfl) ⟨547109, by rfl⟩ : syracuseStep 729479 = 1094219) B1094219
theorem B860687 : Blo 381763 860687 := bstep (se 1 (by rfl) ⟨645515, by rfl⟩ : syracuseStep 860687 = 1291031) B1291031
theorem B860705 : Blo 381763 860705 := bstep (se 2 (by rfl) ⟨322764, by rfl⟩ : syracuseStep 860705 = 645529) B645529
theorem B1942217 : Blo 381763 1942217 := bstep (se 2 (by rfl) ⟨728331, by rfl⟩ : syracuseStep 1942217 = 1456663) B1456663
theorem B861047 : Blo 381763 861047 := bstep (se 1 (by rfl) ⟨645785, by rfl⟩ : syracuseStep 861047 = 1291571) B1291571
theorem B861227 : Blo 381763 861227 := bstep (se 1 (by rfl) ⟨645920, by rfl⟩ : syracuseStep 861227 = 1291841) B1291841
theorem B1090675 : Blo 381763 1090675 := bstep (se 1 (by rfl) ⟨818006, by rfl⟩ : syracuseStep 1090675 = 1636013) B1636013
theorem B1090903 : Blo 381763 1090903 := bstep (se 1 (by rfl) ⟨818177, by rfl⟩ : syracuseStep 1090903 = 1636355) B1636355
theorem B861587 : Blo 381763 861587 := bstep (se 1 (by rfl) ⟨646190, by rfl⟩ : syracuseStep 861587 = 1292381) B1292381
theorem B11838905 : Blo 381763 11838905 := bstep (se 2 (by rfl) ⟨4439589, by rfl⟩ : syracuseStep 11838905 = 8879179) B8879179
theorem B861641 : Blo 381763 861641 := bstep (se 2 (by rfl) ⟨323115, by rfl⟩ : syracuseStep 861641 = 646231) B646231
theorem B731081 : Blo 381763 731081 := bstep (se 2 (by rfl) ⟨274155, by rfl⟩ : syracuseStep 731081 = 548311) B548311
theorem B862343 : Blo 381763 862343 := bstep (se 1 (by rfl) ⟨646757, by rfl⟩ : syracuseStep 862343 = 1293515) B1293515
theorem B1452289 : Blo 381763 1452289 := bstep (se 2 (by rfl) ⟨544608, by rfl⟩ : syracuseStep 1452289 = 1089217) B1089217
theorem B862523 : Blo 381763 862523 := bstep (se 1 (by rfl) ⟨646892, by rfl⟩ : syracuseStep 862523 = 1293785) B1293785
theorem B3123515 : Blo 381763 3123515 := bstep (se 1 (by rfl) ⟨2342636, by rfl⟩ : syracuseStep 3123515 = 4685273) B4685273
theorem B1288601 : Blo 381763 1288601 := bstep (se 2 (by rfl) ⟨483225, by rfl⟩ : syracuseStep 1288601 = 966451) B966451
theorem B862649 : Blo 381763 862649 := bstep (se 2 (by rfl) ⟨323493, by rfl⟩ : syracuseStep 862649 = 646987) B646987
theorem B1845821 : Blo 381763 1845821 := bstep (se 3 (by rfl) ⟨346091, by rfl⟩ : syracuseStep 1845821 = 692183) B692183
theorem B862991 : Blo 381763 862991 := bstep (se 1 (by rfl) ⟨647243, by rfl⟩ : syracuseStep 862991 = 1294487) B1294487
theorem B863009 : Blo 381763 863009 := bstep (se 2 (by rfl) ⟨323628, by rfl⟩ : syracuseStep 863009 = 647257) B647257
theorem B1092487 : Blo 381763 1092487 := bstep (se 1 (by rfl) ⟨819365, by rfl⟩ : syracuseStep 1092487 = 1638731) B1638731
theorem B2632601 : Blo 381763 2632601 := bstep (se 2 (by rfl) ⟨987225, by rfl⟩ : syracuseStep 2632601 = 1974451) B1974451
theorem B601145 : Blo 381763 601145 := bstep (se 2 (by rfl) ⟨225429, by rfl⟩ : syracuseStep 601145 = 450859) B450859
theorem B1289303 : Blo 381763 1289303 := bstep (se 1 (by rfl) ⟨966977, by rfl⟩ : syracuseStep 1289303 = 1933955) B1933955
theorem B863351 : Blo 381763 863351 := bstep (se 1 (by rfl) ⟨647513, by rfl⟩ : syracuseStep 863351 = 1295027) B1295027
theorem B1092761 : Blo 381763 1092761 := bstep (se 2 (by rfl) ⟨409785, by rfl⟩ : syracuseStep 1092761 = 819571) B819571
theorem B863531 : Blo 381763 863531 := bstep (se 1 (by rfl) ⟨647648, by rfl⟩ : syracuseStep 863531 = 1295297) B1295297
theorem B248491405 : Blo 381763 248491405 := bstep (se 3 (by rfl) ⟨46592138, by rfl⟩ : syracuseStep 248491405 = 93184277) B93184277
theorem B1289789 : Blo 381763 1289789 := bstep (se 3 (by rfl) ⟨241835, by rfl⟩ : syracuseStep 1289789 = 483671) B483671
theorem B3124813 : Blo 381763 3124813 := bstep (se 3 (by rfl) ⟨585902, by rfl⟩ : syracuseStep 3124813 = 1171805) B1171805
theorem B863891 : Blo 381763 863891 := bstep (se 1 (by rfl) ⟨647918, by rfl⟩ : syracuseStep 863891 = 1295837) B1295837
theorem B863945 : Blo 381763 863945 := bstep (se 2 (by rfl) ⟨323979, by rfl⟩ : syracuseStep 863945 = 647959) B647959
theorem B3550949 : Blo 381763 3550949 := bstep (se 4 (by rfl) ⟨332901, by rfl⟩ : syracuseStep 3550949 = 665803) B665803
theorem B1093409 : Blo 381763 1093409 := bstep (se 2 (by rfl) ⟨410028, by rfl⟩ : syracuseStep 1093409 = 820057) B820057
theorem B3321803 : Blo 381763 3321803 := bstep (se 1 (by rfl) ⟨2491352, by rfl⟩ : syracuseStep 3321803 = 4982705) B4982705
theorem B864647 : Blo 381763 864647 := bstep (se 1 (by rfl) ⟨648485, by rfl⟩ : syracuseStep 864647 = 1296971) B1296971
theorem B864827 : Blo 381763 864827 := bstep (se 1 (by rfl) ⟨648620, by rfl⟩ : syracuseStep 864827 = 1297241) B1297241
theorem B864953 : Blo 381763 864953 := bstep (se 2 (by rfl) ⟨324357, by rfl⟩ : syracuseStep 864953 = 648715) B648715
theorem B1094411 : Blo 381763 1094411 := bstep (se 1 (by rfl) ⟨820808, by rfl⟩ : syracuseStep 1094411 = 1641617) B1641617
theorem B2175929 : Blo 381763 2175929 := bstep (se 2 (by rfl) ⟨815973, by rfl⟩ : syracuseStep 2175929 = 1631947) B1631947
theorem B1291193 : Blo 381763 1291193 := bstep (se 2 (by rfl) ⟨484197, by rfl⟩ : syracuseStep 1291193 = 968395) B968395
theorem B930827 : Blo 381763 930827 := bstep (se 1 (by rfl) ⟨698120, by rfl⟩ : syracuseStep 930827 = 1396241) B1396241
theorem B865295 : Blo 381763 865295 := bstep (se 1 (by rfl) ⟨648971, by rfl⟩ : syracuseStep 865295 = 1297943) B1297943
theorem B865313 : Blo 381763 865313 := bstep (se 2 (by rfl) ⟨324492, by rfl⟩ : syracuseStep 865313 = 648985) B648985
theorem B1455191 : Blo 381763 1455191 := bstep (se 1 (by rfl) ⟨1091393, by rfl⟩ : syracuseStep 1455191 = 2182787) B2182787
theorem B1848665 : Blo 381763 1848665 := bstep (se 2 (by rfl) ⟨693249, by rfl⟩ : syracuseStep 1848665 = 1386499) B1386499
theorem B865655 : Blo 381763 865655 := bstep (se 1 (by rfl) ⟨649241, by rfl⟩ : syracuseStep 865655 = 1298483) B1298483
theorem B1291787 : Blo 381763 1291787 := bstep (se 1 (by rfl) ⟨968840, by rfl⟩ : syracuseStep 1291787 = 1937681) B1937681
theorem B865835 : Blo 381763 865835 := bstep (se 1 (by rfl) ⟨649376, by rfl⟩ : syracuseStep 865835 = 1298753) B1298753
theorem B1455677 : Blo 381763 1455677 := bstep (se 3 (by rfl) ⟨272939, by rfl⟩ : syracuseStep 1455677 = 545879) B545879
theorem B6534755 : Blo 381763 6534755 := bstep (se 1 (by rfl) ⟨4901066, by rfl⟩ : syracuseStep 6534755 = 9802133) B9802133
theorem B1291895 : Blo 381763 1291895 := bstep (se 1 (by rfl) ⟨968921, by rfl⟩ : syracuseStep 1291895 = 1937843) B1937843
theorem B1226497 : Blo 381763 1226497 := bstep (se 2 (by rfl) ⟨459936, by rfl⟩ : syracuseStep 1226497 = 919873) B919873
theorem B866195 : Blo 381763 866195 := bstep (se 1 (by rfl) ⟨649646, by rfl⟩ : syracuseStep 866195 = 1299293) B1299293
theorem B866249 : Blo 381763 866249 := bstep (se 2 (by rfl) ⟨324843, by rfl⟩ : syracuseStep 866249 = 649687) B649687
theorem B4372541 : Blo 381763 4372541 := bstep (se 3 (by rfl) ⟨819851, by rfl⟩ : syracuseStep 4372541 = 1639703) B1639703
theorem B1292489 : Blo 381763 1292489 := bstep (se 2 (by rfl) ⟨484683, by rfl⟩ : syracuseStep 1292489 = 969367) B969367
theorem B7027037 : Blo 381763 7027037 := bstep (se 3 (by rfl) ⟨1317569, by rfl⟩ : syracuseStep 7027037 = 2635139) B2635139
theorem B1948049 : Blo 381763 1948049 := bstep (se 2 (by rfl) ⟨730518, by rfl⟩ : syracuseStep 1948049 = 1461037) B1461037
theorem B6371731 : Blo 381763 6371731 := bstep (se 1 (by rfl) ⟨4778798, by rfl⟩ : syracuseStep 6371731 = 9557597) B9557597
theorem B4143545 : Blo 381763 4143545 := bstep (se 2 (by rfl) ⟨1553829, by rfl⟩ : syracuseStep 4143545 = 3107659) B3107659
theorem B4143581 : Blo 381763 4143581 := bstep (se 3 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 4143581 = 1553843) B1553843
theorem B3291677 : Blo 381763 3291677 := bstep (se 3 (by rfl) ⟨617189, by rfl⟩ : syracuseStep 3291677 = 1234379) B1234379
theorem B4569643 : Blo 381763 4569643 := bstep (se 1 (by rfl) ⟨3427232, by rfl⟩ : syracuseStep 4569643 = 6854465) B6854465
theorem B866951 : Blo 381763 866951 := bstep (se 1 (by rfl) ⟨650213, by rfl⟩ : syracuseStep 866951 = 1300427) B1300427
theorem B3160883 : Blo 381763 3160883 := bstep (se 1 (by rfl) ⟨2370662, by rfl⟩ : syracuseStep 3160883 = 4741325) B4741325
theorem B1096507 : Blo 381763 1096507 := bstep (se 1 (by rfl) ⟨822380, by rfl⟩ : syracuseStep 1096507 = 1644761) B1644761
theorem B867131 : Blo 381763 867131 := bstep (se 1 (by rfl) ⟨650348, by rfl⟩ : syracuseStep 867131 = 1300697) B1300697
theorem B1522547 : Blo 381763 1522547 := bstep (se 1 (by rfl) ⟨1141910, by rfl⟩ : syracuseStep 1522547 = 2283821) B2283821
theorem B1293191 : Blo 381763 1293191 := bstep (se 1 (by rfl) ⟨969893, by rfl⟩ : syracuseStep 1293191 = 1939787) B1939787
theorem B867257 : Blo 381763 867257 := bstep (se 2 (by rfl) ⟨325221, by rfl⟩ : syracuseStep 867257 = 650443) B650443
theorem B1850435 : Blo 381763 1850435 := bstep (se 1 (by rfl) ⟨1387826, by rfl⟩ : syracuseStep 1850435 = 2775653) B2775653
theorem B11025557 : Blo 381763 11025557 := bstep (se 6 (by rfl) ⟨258411, by rfl⟩ : syracuseStep 11025557 = 516823) B516823
theorem B572663 : Blo 381763 572663 := bstep (se 1 (by rfl) ⟨429497, by rfl⟩ : syracuseStep 572663 = 858995) B858995
theorem B1293569 : Blo 381763 1293569 := bstep (se 2 (by rfl) ⟨485088, by rfl⟩ : syracuseStep 1293569 = 970177) B970177
theorem B572687 : Blo 381763 572687 := bstep (se 1 (by rfl) ⟨429515, by rfl⟩ : syracuseStep 572687 = 859031) B859031
theorem B1457423 : Blo 381763 1457423 := bstep (se 1 (by rfl) ⟨1093067, by rfl⟩ : syracuseStep 1457423 = 2186135) B2186135
theorem B867599 : Blo 381763 867599 := bstep (se 1 (by rfl) ⟨650699, by rfl⟩ : syracuseStep 867599 = 1301399) B1301399
theorem B867617 : Blo 381763 867617 := bstep (se 2 (by rfl) ⟨325356, by rfl⟩ : syracuseStep 867617 = 650713) B650713
theorem B572729 : Blo 381763 572729 := bstep (se 2 (by rfl) ⟨214773, by rfl⟩ : syracuseStep 572729 = 429547) B429547
theorem B572807 : Blo 381763 572807 := bstep (se 1 (by rfl) ⟨429605, by rfl⟩ : syracuseStep 572807 = 859211) B859211
theorem B1752455 : Blo 381763 1752455 := bstep (se 1 (by rfl) ⟨1314341, by rfl⟩ : syracuseStep 1752455 = 2628683) B2628683
theorem B572843 : Blo 381763 572843 := bstep (se 1 (by rfl) ⟨429632, by rfl⟩ : syracuseStep 572843 = 859265) B859265
theorem B572873 : Blo 381763 572873 := bstep (se 2 (by rfl) ⟨214827, by rfl⟩ : syracuseStep 572873 = 429655) B429655
theorem B572987 : Blo 381763 572987 := bstep (se 1 (by rfl) ⟨429740, by rfl⟩ : syracuseStep 572987 = 859481) B859481
theorem B573047 : Blo 381763 573047 := bstep (se 1 (by rfl) ⟨429785, by rfl⟩ : syracuseStep 573047 = 859571) B859571
theorem B867959 : Blo 381763 867959 := bstep (se 1 (by rfl) ⟨650969, by rfl⟩ : syracuseStep 867959 = 1301939) B1301939
theorem B1097351 : Blo 381763 1097351 := bstep (se 1 (by rfl) ⟨823013, by rfl⟩ : syracuseStep 1097351 = 1646027) B1646027
theorem B573071 : Blo 381763 573071 := bstep (se 1 (by rfl) ⟨429803, by rfl⟩ : syracuseStep 573071 = 859607) B859607
theorem B573113 : Blo 381763 573113 := bstep (se 2 (by rfl) ⟨214917, by rfl⟩ : syracuseStep 573113 = 429835) B429835
theorem B966401 : Blo 381763 966401 := bstep (se 2 (by rfl) ⟨362400, by rfl⟩ : syracuseStep 966401 = 724801) B724801
theorem B573191 : Blo 381763 573191 := bstep (se 1 (by rfl) ⟨429893, by rfl⟩ : syracuseStep 573191 = 859787) B859787
theorem B573227 : Blo 381763 573227 := bstep (se 1 (by rfl) ⟨429920, by rfl⟩ : syracuseStep 573227 = 859841) B859841
theorem B573257 : Blo 381763 573257 := bstep (se 2 (by rfl) ⟨214971, by rfl⟩ : syracuseStep 573257 = 429943) B429943
theorem B2080657 : Blo 381763 2080657 := bstep (se 2 (by rfl) ⟨780246, by rfl⟩ : syracuseStep 2080657 = 1560493) B1560493
theorem B1851281 : Blo 381763 1851281 := bstep (se 2 (by rfl) ⟨694230, by rfl⟩ : syracuseStep 1851281 = 1388461) B1388461
theorem B573371 : Blo 381763 573371 := bstep (se 1 (by rfl) ⟨430028, by rfl⟩ : syracuseStep 573371 = 860057) B860057
theorem B573431 : Blo 381763 573431 := bstep (se 1 (by rfl) ⟨430073, by rfl⟩ : syracuseStep 573431 = 860147) B860147
theorem B2211851 : Blo 381763 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B573455 : Blo 381763 573455 := bstep (se 1 (by rfl) ⟨430091, by rfl⟩ : syracuseStep 573455 = 860183) B860183
theorem B1294379 : Blo 381763 1294379 := bstep (se 1 (by rfl) ⟨970784, by rfl⟩ : syracuseStep 1294379 = 1941569) B1941569
theorem B573497 : Blo 381763 573497 := bstep (se 2 (by rfl) ⟨215061, by rfl⟩ : syracuseStep 573497 = 430123) B430123
theorem B966775 : Blo 381763 966775 := bstep (se 1 (by rfl) ⟨725081, by rfl⟩ : syracuseStep 966775 = 1450163) B1450163
theorem B573575 : Blo 381763 573575 := bstep (se 1 (by rfl) ⟨430181, by rfl⟩ : syracuseStep 573575 = 860363) B860363
theorem B573611 : Blo 381763 573611 := bstep (se 1 (by rfl) ⟨430208, by rfl⟩ : syracuseStep 573611 = 860417) B860417
theorem B2080961 : Blo 381763 2080961 := bstep (se 2 (by rfl) ⟨780360, by rfl⟩ : syracuseStep 2080961 = 1560721) B1560721
theorem B573641 : Blo 381763 573641 := bstep (se 2 (by rfl) ⟨215115, by rfl⟩ : syracuseStep 573641 = 430231) B430231
theorem B573755 : Blo 381763 573755 := bstep (se 1 (by rfl) ⟨430316, by rfl⟩ : syracuseStep 573755 = 860633) B860633
theorem B573815 : Blo 381763 573815 := bstep (se 1 (by rfl) ⟨430361, by rfl⟩ : syracuseStep 573815 = 860723) B860723
theorem B573839 : Blo 381763 573839 := bstep (se 1 (by rfl) ⟨430379, by rfl⟩ : syracuseStep 573839 = 860759) B860759
theorem B1098137 : Blo 381763 1098137 := bstep (se 2 (by rfl) ⟨411801, by rfl⟩ : syracuseStep 1098137 = 823603) B823603
theorem B573881 : Blo 381763 573881 := bstep (se 2 (by rfl) ⟨215205, by rfl⟩ : syracuseStep 573881 = 430411) B430411
theorem B1950155 : Blo 381763 1950155 := bstep (se 1 (by rfl) ⟨1462616, by rfl⟩ : syracuseStep 1950155 = 2925233) B2925233
theorem B573959 : Blo 381763 573959 := bstep (se 1 (by rfl) ⟨430469, by rfl⟩ : syracuseStep 573959 = 860939) B860939
theorem B967211 : Blo 381763 967211 := bstep (se 1 (by rfl) ⟨725408, by rfl⟩ : syracuseStep 967211 = 1450817) B1450817
theorem B573995 : Blo 381763 573995 := bstep (se 1 (by rfl) ⟨430496, by rfl⟩ : syracuseStep 573995 = 860993) B860993
theorem B574025 : Blo 381763 574025 := bstep (se 2 (by rfl) ⟨215259, by rfl⟩ : syracuseStep 574025 = 430519) B430519
theorem B574139 : Blo 381763 574139 := bstep (se 1 (by rfl) ⟨430604, by rfl⟩ : syracuseStep 574139 = 861209) B861209
theorem B574199 : Blo 381763 574199 := bstep (se 1 (by rfl) ⟨430649, by rfl⟩ : syracuseStep 574199 = 861299) B861299
theorem B574223 : Blo 381763 574223 := bstep (se 1 (by rfl) ⟨430667, by rfl⟩ : syracuseStep 574223 = 861335) B861335
theorem B1950479 : Blo 381763 1950479 := bstep (se 1 (by rfl) ⟨1462859, by rfl⟩ : syracuseStep 1950479 = 2925719) B2925719
theorem B574265 : Blo 381763 574265 := bstep (se 2 (by rfl) ⟨215349, by rfl⟩ : syracuseStep 574265 = 430699) B430699
theorem B574343 : Blo 381763 574343 := bstep (se 1 (by rfl) ⟨430757, by rfl⟩ : syracuseStep 574343 = 861515) B861515
theorem B1459079 : Blo 381763 1459079 := bstep (se 1 (by rfl) ⟨1094309, by rfl⟩ : syracuseStep 1459079 = 2188619) B2188619
theorem B410503 : Blo 381763 410503 := bstep (se 1 (by rfl) ⟨307877, by rfl⟩ : syracuseStep 410503 = 615755) B615755
theorem B574379 : Blo 381763 574379 := bstep (se 1 (by rfl) ⟨430784, by rfl⟩ : syracuseStep 574379 = 861569) B861569
theorem B574409 : Blo 381763 574409 := bstep (se 2 (by rfl) ⟨215403, by rfl⟩ : syracuseStep 574409 = 430807) B430807
theorem B574523 : Blo 381763 574523 := bstep (se 1 (by rfl) ⟨430892, by rfl⟩ : syracuseStep 574523 = 861785) B861785
theorem B574583 : Blo 381763 574583 := bstep (se 1 (by rfl) ⟨430937, by rfl⟩ : syracuseStep 574583 = 861875) B861875
theorem B574607 : Blo 381763 574607 := bstep (se 1 (by rfl) ⟨430955, by rfl⟩ : syracuseStep 574607 = 861911) B861911
theorem B574649 : Blo 381763 574649 := bstep (se 2 (by rfl) ⟨215493, by rfl⟩ : syracuseStep 574649 = 430987) B430987
theorem B574727 : Blo 381763 574727 := bstep (se 1 (by rfl) ⟨431045, by rfl⟩ : syracuseStep 574727 = 862091) B862091
theorem B9880865 : Blo 381763 9880865 := bstep (se 2 (by rfl) ⟨3705324, by rfl⟩ : syracuseStep 9880865 = 7410649) B7410649
theorem B574763 : Blo 381763 574763 := bstep (se 1 (by rfl) ⟨431072, by rfl⟩ : syracuseStep 574763 = 862145) B862145
theorem B1295675 : Blo 381763 1295675 := bstep (se 1 (by rfl) ⟨971756, by rfl⟩ : syracuseStep 1295675 = 1943513) B1943513
theorem B574793 : Blo 381763 574793 := bstep (se 2 (by rfl) ⟨215547, by rfl⟩ : syracuseStep 574793 = 431095) B431095
theorem B968051 : Blo 381763 968051 := bstep (se 1 (by rfl) ⟨726038, by rfl⟩ : syracuseStep 968051 = 1452077) B1452077
theorem B968071 : Blo 381763 968071 := bstep (se 1 (by rfl) ⟨726053, by rfl⟩ : syracuseStep 968071 = 1452107) B1452107
theorem B1623449 : Blo 381763 1623449 := bstep (se 2 (by rfl) ⟨608793, by rfl⟩ : syracuseStep 1623449 = 1217587) B1217587
theorem B574907 : Blo 381763 574907 := bstep (se 1 (by rfl) ⟨431180, by rfl⟩ : syracuseStep 574907 = 862361) B862361
theorem B574967 : Blo 381763 574967 := bstep (se 1 (by rfl) ⟨431225, by rfl⟩ : syracuseStep 574967 = 862451) B862451
theorem B3556867 : Blo 381763 3556867 := bstep (se 1 (by rfl) ⟨2667650, by rfl⟩ : syracuseStep 3556867 = 5335301) B5335301
theorem B574991 : Blo 381763 574991 := bstep (se 1 (by rfl) ⟨431243, by rfl⟩ : syracuseStep 574991 = 862487) B862487
theorem B575033 : Blo 381763 575033 := bstep (se 2 (by rfl) ⟨215637, by rfl⟩ : syracuseStep 575033 = 431275) B431275
theorem B575111 : Blo 381763 575111 := bstep (se 1 (by rfl) ⟨431333, by rfl⟩ : syracuseStep 575111 = 862667) B862667
theorem B968345 : Blo 381763 968345 := bstep (se 2 (by rfl) ⟨363129, by rfl⟩ : syracuseStep 968345 = 726259) B726259
theorem B575147 : Blo 381763 575147 := bstep (se 1 (by rfl) ⟨431360, by rfl⟩ : syracuseStep 575147 = 862721) B862721
theorem B411323 : Blo 381763 411323 := bstep (se 1 (by rfl) ⟨308492, by rfl⟩ : syracuseStep 411323 = 616985) B616985
theorem B575177 : Blo 381763 575177 := bstep (se 2 (by rfl) ⟨215691, by rfl⟩ : syracuseStep 575177 = 431383) B431383
theorem B1296161 : Blo 381763 1296161 := bstep (se 2 (by rfl) ⟨486060, by rfl⟩ : syracuseStep 1296161 = 972121) B972121
theorem B968507 : Blo 381763 968507 := bstep (se 1 (by rfl) ⟨726380, by rfl⟩ : syracuseStep 968507 = 1452761) B1452761
theorem B575291 : Blo 381763 575291 := bstep (se 1 (by rfl) ⟨431468, by rfl⟩ : syracuseStep 575291 = 862937) B862937
theorem B1165117 : Blo 381763 1165117 := bstep (se 3 (by rfl) ⟨218459, by rfl⟩ : syracuseStep 1165117 = 436919) B436919
theorem B575351 : Blo 381763 575351 := bstep (se 1 (by rfl) ⟨431513, by rfl⟩ : syracuseStep 575351 = 863027) B863027
theorem B1230727 : Blo 381763 1230727 := bstep (se 1 (by rfl) ⟨923045, by rfl⟩ : syracuseStep 1230727 = 1846091) B1846091
theorem B575375 : Blo 381763 575375 := bstep (se 1 (by rfl) ⟨431531, by rfl⟩ : syracuseStep 575375 = 863063) B863063
theorem B575417 : Blo 381763 575417 := bstep (se 2 (by rfl) ⟨215781, by rfl⟩ : syracuseStep 575417 = 431563) B431563
theorem B575495 : Blo 381763 575495 := bstep (se 1 (by rfl) ⟨431621, by rfl⟩ : syracuseStep 575495 = 863243) B863243
theorem B968719 : Blo 381763 968719 := bstep (se 1 (by rfl) ⟨726539, by rfl⟩ : syracuseStep 968719 = 1453079) B1453079
theorem B575531 : Blo 381763 575531 := bstep (se 1 (by rfl) ⟨431648, by rfl⟩ : syracuseStep 575531 = 863297) B863297
theorem B575561 : Blo 381763 575561 := bstep (se 2 (by rfl) ⟨215835, by rfl⟩ : syracuseStep 575561 = 431671) B431671
theorem B575623 : Blo 381763 575623 := bstep (se 1 (by rfl) ⟨431717, by rfl⟩ : syracuseStep 575623 = 863435) B863435
theorem B575675 : Blo 381763 575675 := bstep (se 1 (by rfl) ⟨431756, by rfl⟩ : syracuseStep 575675 = 863513) B863513
theorem B1951937 : Blo 381763 1951937 := bstep (se 2 (by rfl) ⟨731976, by rfl⟩ : syracuseStep 1951937 = 1463953) B1463953
theorem B575735 : Blo 381763 575735 := bstep (se 1 (by rfl) ⟨431801, by rfl⟩ : syracuseStep 575735 = 863603) B863603
theorem B575759 : Blo 381763 575759 := bstep (se 1 (by rfl) ⟨431819, by rfl⟩ : syracuseStep 575759 = 863639) B863639
theorem B968993 : Blo 381763 968993 := bstep (se 2 (by rfl) ⟨363372, by rfl⟩ : syracuseStep 968993 = 726745) B726745
theorem B575801 : Blo 381763 575801 := bstep (se 2 (by rfl) ⟨215925, by rfl⟩ : syracuseStep 575801 = 431851) B431851
theorem B1231163 : Blo 381763 1231163 := bstep (se 1 (by rfl) ⟨923372, by rfl⟩ : syracuseStep 1231163 = 1846745) B1846745
theorem B1296755 : Blo 381763 1296755 := bstep (se 1 (by rfl) ⟨972566, by rfl⟩ : syracuseStep 1296755 = 1945133) B1945133
theorem B575879 : Blo 381763 575879 := bstep (se 1 (by rfl) ⟨431909, by rfl⟩ : syracuseStep 575879 = 863819) B863819
theorem B575915 : Blo 381763 575915 := bstep (se 1 (by rfl) ⟨431936, by rfl⟩ : syracuseStep 575915 = 863873) B863873
theorem B575945 : Blo 381763 575945 := bstep (se 2 (by rfl) ⟨215979, by rfl⟩ : syracuseStep 575945 = 431959) B431959
theorem B576059 : Blo 381763 576059 := bstep (se 1 (by rfl) ⟨432044, by rfl⟩ : syracuseStep 576059 = 864089) B864089
theorem B576119 : Blo 381763 576119 := bstep (se 1 (by rfl) ⟨432089, by rfl⟩ : syracuseStep 576119 = 864179) B864179
theorem B1460855 : Blo 381763 1460855 := bstep (se 1 (by rfl) ⟨1095641, by rfl⟩ : syracuseStep 1460855 = 2191283) B2191283
theorem B576143 : Blo 381763 576143 := bstep (se 1 (by rfl) ⟨432107, by rfl⟩ : syracuseStep 576143 = 864215) B864215
theorem B576185 : Blo 381763 576185 := bstep (se 2 (by rfl) ⟨216069, by rfl⟩ : syracuseStep 576185 = 432139) B432139
theorem B576263 : Blo 381763 576263 := bstep (se 1 (by rfl) ⟨432197, by rfl⟩ : syracuseStep 576263 = 864395) B864395
theorem B1166113 : Blo 381763 1166113 := bstep (se 2 (by rfl) ⟨437292, by rfl⟩ : syracuseStep 1166113 = 874585) B874585
theorem B576299 : Blo 381763 576299 := bstep (se 1 (by rfl) ⟨432224, by rfl⟩ : syracuseStep 576299 = 864449) B864449
theorem B576329 : Blo 381763 576329 := bstep (se 2 (by rfl) ⟨216123, by rfl⟩ : syracuseStep 576329 = 432247) B432247
theorem B576443 : Blo 381763 576443 := bstep (se 1 (by rfl) ⟨432332, by rfl⟩ : syracuseStep 576443 = 864665) B864665
theorem B4148171 : Blo 381763 4148171 := bstep (se 1 (by rfl) ⟨3111128, by rfl⟩ : syracuseStep 4148171 = 6222257) B6222257
theorem B576503 : Blo 381763 576503 := bstep (se 1 (by rfl) ⟨432377, by rfl⟩ : syracuseStep 576503 = 864755) B864755
theorem B576527 : Blo 381763 576527 := bstep (se 1 (by rfl) ⟨432395, by rfl⟩ : syracuseStep 576527 = 864791) B864791
theorem B576569 : Blo 381763 576569 := bstep (se 2 (by rfl) ⟨216213, by rfl⟩ : syracuseStep 576569 = 432427) B432427
theorem B576647 : Blo 381763 576647 := bstep (se 1 (by rfl) ⟨432485, by rfl⟩ : syracuseStep 576647 = 864971) B864971
theorem B576683 : Blo 381763 576683 := bstep (se 1 (by rfl) ⟨432512, by rfl⟩ : syracuseStep 576683 = 865025) B865025
theorem B576713 : Blo 381763 576713 := bstep (se 2 (by rfl) ⟨216267, by rfl⟩ : syracuseStep 576713 = 432535) B432535
theorem B969995 : Blo 381763 969995 := bstep (se 1 (by rfl) ⟨727496, by rfl⟩ : syracuseStep 969995 = 1454993) B1454993
theorem B576827 : Blo 381763 576827 := bstep (se 1 (by rfl) ⟨432620, by rfl⟩ : syracuseStep 576827 = 865241) B865241
theorem B63688037 : Blo 381763 63688037 := bstep (se 4 (by rfl) ⟨5970753, by rfl⟩ : syracuseStep 63688037 = 11941507) B11941507
theorem B576887 : Blo 381763 576887 := bstep (se 1 (by rfl) ⟨432665, by rfl⟩ : syracuseStep 576887 = 865331) B865331
theorem B2182535 : Blo 381763 2182535 := bstep (se 1 (by rfl) ⟨1636901, by rfl⟩ : syracuseStep 2182535 = 3273803) B3273803
theorem B576911 : Blo 381763 576911 := bstep (se 1 (by rfl) ⟨432683, by rfl⟩ : syracuseStep 576911 = 865367) B865367
theorem B576953 : Blo 381763 576953 := bstep (se 2 (by rfl) ⟨216357, by rfl⟩ : syracuseStep 576953 = 432715) B432715
theorem B577031 : Blo 381763 577031 := bstep (se 1 (by rfl) ⟨432773, by rfl⟩ : syracuseStep 577031 = 865547) B865547
theorem B1166891 : Blo 381763 1166891 := bstep (se 1 (by rfl) ⟨875168, by rfl⟩ : syracuseStep 1166891 = 1750337) B1750337
theorem B577067 : Blo 381763 577067 := bstep (se 1 (by rfl) ⟨432800, by rfl⟩ : syracuseStep 577067 = 865601) B865601
theorem B1461827 : Blo 381763 1461827 := bstep (se 1 (by rfl) ⟨1096370, by rfl⟩ : syracuseStep 1461827 = 2192741) B2192741
theorem B577097 : Blo 381763 577097 := bstep (se 2 (by rfl) ⟨216411, by rfl⟩ : syracuseStep 577097 = 432823) B432823
theorem B577211 : Blo 381763 577211 := bstep (se 1 (by rfl) ⟨432908, by rfl⟩ : syracuseStep 577211 = 865817) B865817
theorem B577271 : Blo 381763 577271 := bstep (se 1 (by rfl) ⟨432953, by rfl⟩ : syracuseStep 577271 = 865907) B865907
theorem B577295 : Blo 381763 577295 := bstep (se 1 (by rfl) ⟨432971, by rfl⟩ : syracuseStep 577295 = 865943) B865943
theorem B4902707 : Blo 381763 4902707 := bstep (se 1 (by rfl) ⟨3677030, by rfl⟩ : syracuseStep 4902707 = 7354061) B7354061
theorem B577337 : Blo 381763 577337 := bstep (se 2 (by rfl) ⟨216501, by rfl⟩ : syracuseStep 577337 = 433003) B433003
theorem B3264371 : Blo 381763 3264371 := bstep (se 1 (by rfl) ⟨2448278, by rfl⟩ : syracuseStep 3264371 = 4896557) B4896557
theorem B577415 : Blo 381763 577415 := bstep (se 1 (by rfl) ⟨433061, by rfl⟩ : syracuseStep 577415 = 866123) B866123
theorem B970643 : Blo 381763 970643 := bstep (se 1 (by rfl) ⟨727982, by rfl⟩ : syracuseStep 970643 = 1455965) B1455965
theorem B577451 : Blo 381763 577451 := bstep (se 1 (by rfl) ⟨433088, by rfl⟩ : syracuseStep 577451 = 866177) B866177
theorem B577481 : Blo 381763 577481 := bstep (se 2 (by rfl) ⟨216555, by rfl⟩ : syracuseStep 577481 = 433111) B433111
theorem B1462283 : Blo 381763 1462283 := bstep (se 1 (by rfl) ⟨1096712, by rfl⟩ : syracuseStep 1462283 = 2193425) B2193425
theorem B577595 : Blo 381763 577595 := bstep (se 1 (by rfl) ⟨433196, by rfl⟩ : syracuseStep 577595 = 866393) B866393
theorem B577655 : Blo 381763 577655 := bstep (se 1 (by rfl) ⟨433241, by rfl⟩ : syracuseStep 577655 = 866483) B866483
theorem B577679 : Blo 381763 577679 := bstep (se 1 (by rfl) ⟨433259, by rfl⟩ : syracuseStep 577679 = 866519) B866519
theorem B970937 : Blo 381763 970937 := bstep (se 2 (by rfl) ⟨364101, by rfl⟩ : syracuseStep 970937 = 728203) B728203
theorem B577721 : Blo 381763 577721 := bstep (se 2 (by rfl) ⟨216645, by rfl⟩ : syracuseStep 577721 = 433291) B433291
theorem B577799 : Blo 381763 577799 := bstep (se 1 (by rfl) ⟨433349, by rfl⟩ : syracuseStep 577799 = 866699) B866699
theorem B577835 : Blo 381763 577835 := bstep (se 1 (by rfl) ⟨433376, by rfl⟩ : syracuseStep 577835 = 866753) B866753
theorem B577865 : Blo 381763 577865 := bstep (se 2 (by rfl) ⟨216699, by rfl⟩ : syracuseStep 577865 = 433399) B433399
theorem B545167 : Blo 381763 545167 := bstep (se 1 (by rfl) ⟨408875, by rfl⟩ : syracuseStep 545167 = 817751) B817751
theorem B3101075 : Blo 381763 3101075 := bstep (se 1 (by rfl) ⟨2325806, by rfl⟩ : syracuseStep 3101075 = 4651613) B4651613
theorem B577979 : Blo 381763 577979 := bstep (se 1 (by rfl) ⟨433484, by rfl⟩ : syracuseStep 577979 = 866969) B866969
theorem B1167817 : Blo 381763 1167817 := bstep (se 2 (by rfl) ⟨437931, by rfl⟩ : syracuseStep 1167817 = 875863) B875863
theorem B578039 : Blo 381763 578039 := bstep (se 1 (by rfl) ⟨433529, by rfl⟩ : syracuseStep 578039 = 867059) B867059
theorem B545287 : Blo 381763 545287 := bstep (se 1 (by rfl) ⟨408965, by rfl⟩ : syracuseStep 545287 = 817931) B817931
theorem B578063 : Blo 381763 578063 := bstep (se 1 (by rfl) ⟨433547, by rfl⟩ : syracuseStep 578063 = 867095) B867095
theorem B578105 : Blo 381763 578105 := bstep (se 2 (by rfl) ⟨216789, by rfl⟩ : syracuseStep 578105 = 433579) B433579
theorem B578183 : Blo 381763 578183 := bstep (se 1 (by rfl) ⟨433637, by rfl⟩ : syracuseStep 578183 = 867275) B867275
theorem B873107 : Blo 381763 873107 := bstep (se 1 (by rfl) ⟨654830, by rfl⟩ : syracuseStep 873107 = 1309661) B1309661
theorem B578219 : Blo 381763 578219 := bstep (se 1 (by rfl) ⟨433664, by rfl⟩ : syracuseStep 578219 = 867329) B867329
theorem B7000769 : Blo 381763 7000769 := bstep (se 2 (by rfl) ⟨2625288, by rfl⟩ : syracuseStep 7000769 = 5250577) B5250577
theorem B578249 : Blo 381763 578249 := bstep (se 2 (by rfl) ⟨216843, by rfl⟩ : syracuseStep 578249 = 433687) B433687
theorem B578363 : Blo 381763 578363 := bstep (se 1 (by rfl) ⟨433772, by rfl⟩ : syracuseStep 578363 = 867545) B867545
theorem B971635 : Blo 381763 971635 := bstep (se 1 (by rfl) ⟨728726, by rfl⟩ : syracuseStep 971635 = 1457453) B1457453
theorem B578423 : Blo 381763 578423 := bstep (se 1 (by rfl) ⟨433817, by rfl⟩ : syracuseStep 578423 = 867635) B867635
theorem B381831 : Blo 381763 381831 := bstep (se 1 (by rfl) ⟨286373, by rfl⟩ : syracuseStep 381831 = 572747) B572747
theorem B381839 : Blo 381763 381839 := bstep (se 1 (by rfl) ⟨286379, by rfl⟩ : syracuseStep 381839 = 572759) B572759
theorem B578447 : Blo 381763 578447 := bstep (se 1 (by rfl) ⟨433835, by rfl⟩ : syracuseStep 578447 = 867671) B867671
theorem B1299347 : Blo 381763 1299347 := bstep (se 1 (by rfl) ⟨974510, by rfl⟩ : syracuseStep 1299347 = 1949021) B1949021
theorem B3265433 : Blo 381763 3265433 := bstep (se 2 (by rfl) ⟨1224537, by rfl⟩ : syracuseStep 3265433 = 2449075) B2449075
theorem B578489 : Blo 381763 578489 := bstep (se 2 (by rfl) ⟨216933, by rfl⟩ : syracuseStep 578489 = 433867) B433867
theorem B381883 : Blo 381763 381883 := bstep (se 1 (by rfl) ⟨286412, by rfl⟩ : syracuseStep 381883 = 572825) B572825
theorem B971777 : Blo 381763 971777 := bstep (se 2 (by rfl) ⟨364416, by rfl⟩ : syracuseStep 971777 = 728833) B728833
theorem B381959 : Blo 381763 381959 := bstep (se 1 (by rfl) ⟨286469, by rfl⟩ : syracuseStep 381959 = 572939) B572939
theorem B578567 : Blo 381763 578567 := bstep (se 1 (by rfl) ⟨433925, by rfl⟩ : syracuseStep 578567 = 867851) B867851
theorem B381967 : Blo 381763 381967 := bstep (se 1 (by rfl) ⟨286475, by rfl⟩ : syracuseStep 381967 = 572951) B572951
theorem B578603 : Blo 381763 578603 := bstep (se 1 (by rfl) ⟨433952, by rfl⟩ : syracuseStep 578603 = 867905) B867905
theorem B3691565 : Blo 381763 3691565 := bstep (se 3 (by rfl) ⟨692168, by rfl⟩ : syracuseStep 3691565 = 1384337) B1384337
theorem B382011 : Blo 381763 382011 := bstep (se 1 (by rfl) ⟨286508, by rfl⟩ : syracuseStep 382011 = 573017) B573017
theorem B578633 : Blo 381763 578633 := bstep (se 2 (by rfl) ⟨216987, by rfl⟩ : syracuseStep 578633 = 433975) B433975
theorem B382087 : Blo 381763 382087 := bstep (se 1 (by rfl) ⟨286565, by rfl⟩ : syracuseStep 382087 = 573131) B573131
theorem B382095 : Blo 381763 382095 := bstep (se 1 (by rfl) ⟨286571, by rfl⟩ : syracuseStep 382095 = 573143) B573143
theorem B382139 : Blo 381763 382139 := bstep (se 1 (by rfl) ⟨286604, by rfl⟩ : syracuseStep 382139 = 573209) B573209
theorem B382215 : Blo 381763 382215 := bstep (se 1 (by rfl) ⟨286661, by rfl⟩ : syracuseStep 382215 = 573323) B573323
theorem B382223 : Blo 381763 382223 := bstep (se 1 (by rfl) ⟨286667, by rfl⟩ : syracuseStep 382223 = 573335) B573335
theorem B3691793 : Blo 381763 3691793 := bstep (se 2 (by rfl) ⟨1384422, by rfl⟩ : syracuseStep 3691793 = 2768845) B2768845
theorem B644395 : Blo 381763 644395 := bstep (se 1 (by rfl) ⟨483296, by rfl⟩ : syracuseStep 644395 = 966593) B966593
theorem B382267 : Blo 381763 382267 := bstep (se 1 (by rfl) ⟨286700, by rfl⟩ : syracuseStep 382267 = 573401) B573401
theorem B382343 : Blo 381763 382343 := bstep (se 1 (by rfl) ⟨286757, by rfl⟩ : syracuseStep 382343 = 573515) B573515
theorem B382351 : Blo 381763 382351 := bstep (se 1 (by rfl) ⟨286763, by rfl⟩ : syracuseStep 382351 = 573527) B573527
theorem B644537 : Blo 381763 644537 := bstep (se 2 (by rfl) ⟨241701, by rfl⟩ : syracuseStep 644537 = 483403) B483403
theorem B382395 : Blo 381763 382395 := bstep (se 1 (by rfl) ⟨286796, by rfl⟩ : syracuseStep 382395 = 573593) B573593
theorem B873929 : Blo 381763 873929 := bstep (se 2 (by rfl) ⟨327723, by rfl⟩ : syracuseStep 873929 = 655447) B655447
theorem B972233 : Blo 381763 972233 := bstep (se 2 (by rfl) ⟨364587, by rfl⟩ : syracuseStep 972233 = 729175) B729175
theorem B382471 : Blo 381763 382471 := bstep (se 1 (by rfl) ⟨286853, by rfl⟩ : syracuseStep 382471 = 573707) B573707
theorem B382479 : Blo 381763 382479 := bstep (se 1 (by rfl) ⟨286859, by rfl⟩ : syracuseStep 382479 = 573719) B573719
theorem B382523 : Blo 381763 382523 := bstep (se 1 (by rfl) ⟨286892, by rfl⟩ : syracuseStep 382523 = 573785) B573785
theorem B382599 : Blo 381763 382599 := bstep (se 1 (by rfl) ⟨286949, by rfl⟩ : syracuseStep 382599 = 573899) B573899
theorem B382607 : Blo 381763 382607 := bstep (se 1 (by rfl) ⟨286955, by rfl⟩ : syracuseStep 382607 = 573911) B573911
theorem B382651 : Blo 381763 382651 := bstep (se 1 (by rfl) ⟨286988, by rfl⟩ : syracuseStep 382651 = 573977) B573977
theorem B2905793 : Blo 381763 2905793 := bstep (se 2 (by rfl) ⟨1089672, by rfl⟩ : syracuseStep 2905793 = 2179345) B2179345
theorem B382727 : Blo 381763 382727 := bstep (se 1 (by rfl) ⟨287045, by rfl⟩ : syracuseStep 382727 = 574091) B574091
theorem B382735 : Blo 381763 382735 := bstep (se 1 (by rfl) ⟨287051, by rfl⟩ : syracuseStep 382735 = 574103) B574103
theorem B972587 : Blo 381763 972587 := bstep (se 1 (by rfl) ⟨729440, by rfl⟩ : syracuseStep 972587 = 1458881) B1458881
theorem B1070891 : Blo 381763 1070891 := bstep (se 1 (by rfl) ⟨803168, by rfl⟩ : syracuseStep 1070891 = 1606337) B1606337
theorem B382779 : Blo 381763 382779 := bstep (se 1 (by rfl) ⟨287084, by rfl⟩ : syracuseStep 382779 = 574169) B574169
theorem B382855 : Blo 381763 382855 := bstep (se 1 (by rfl) ⟨287141, by rfl⟩ : syracuseStep 382855 = 574283) B574283
theorem B382863 : Blo 381763 382863 := bstep (se 1 (by rfl) ⟨287147, by rfl⟩ : syracuseStep 382863 = 574295) B574295
theorem B546745 : Blo 381763 546745 := bstep (se 2 (by rfl) ⟨205029, by rfl⟩ : syracuseStep 546745 = 410059) B410059
theorem B382907 : Blo 381763 382907 := bstep (se 1 (by rfl) ⟨287180, by rfl⟩ : syracuseStep 382907 = 574361) B574361
theorem B382983 : Blo 381763 382983 := bstep (se 1 (by rfl) ⟨287237, by rfl⟩ : syracuseStep 382983 = 574475) B574475
theorem B382991 : Blo 381763 382991 := bstep (se 1 (by rfl) ⟨287243, by rfl⟩ : syracuseStep 382991 = 574487) B574487
theorem B1169423 : Blo 381763 1169423 := bstep (se 1 (by rfl) ⟨877067, by rfl⟩ : syracuseStep 1169423 = 1754135) B1754135
theorem B383035 : Blo 381763 383035 := bstep (se 1 (by rfl) ⟨287276, by rfl⟩ : syracuseStep 383035 = 574553) B574553
theorem B1038395 : Blo 381763 1038395 := bstep (se 1 (by rfl) ⟨778796, by rfl⟩ : syracuseStep 1038395 = 1557593) B1557593
theorem B645239 : Blo 381763 645239 := bstep (se 1 (by rfl) ⟨483929, by rfl⟩ : syracuseStep 645239 = 967859) B967859
theorem B1464439 : Blo 381763 1464439 := bstep (se 1 (by rfl) ⟨1098329, by rfl⟩ : syracuseStep 1464439 = 2196659) B2196659
theorem B383111 : Blo 381763 383111 := bstep (se 1 (by rfl) ⟨287333, by rfl⟩ : syracuseStep 383111 = 574667) B574667
theorem B383119 : Blo 381763 383119 := bstep (se 1 (by rfl) ⟨287339, by rfl⟩ : syracuseStep 383119 = 574679) B574679
theorem B6641837 : Blo 381763 6641837 := bstep (se 3 (by rfl) ⟨1245344, by rfl⟩ : syracuseStep 6641837 = 2490689) B2490689
theorem B383163 : Blo 381763 383163 := bstep (se 1 (by rfl) ⟨287372, by rfl⟩ : syracuseStep 383163 = 574745) B574745
theorem B383239 : Blo 381763 383239 := bstep (se 1 (by rfl) ⟨287429, by rfl⟩ : syracuseStep 383239 = 574859) B574859
theorem B383247 : Blo 381763 383247 := bstep (se 1 (by rfl) ⟨287435, by rfl⟩ : syracuseStep 383247 = 574871) B574871
theorem B1300751 : Blo 381763 1300751 := bstep (se 1 (by rfl) ⟨975563, by rfl⟩ : syracuseStep 1300751 = 1951127) B1951127
theorem B383291 : Blo 381763 383291 := bstep (se 1 (by rfl) ⟨287468, by rfl⟩ : syracuseStep 383291 = 574937) B574937
theorem B383367 : Blo 381763 383367 := bstep (se 1 (by rfl) ⟨287525, by rfl⟩ : syracuseStep 383367 = 575051) B575051
theorem B383375 : Blo 381763 383375 := bstep (se 1 (by rfl) ⟨287531, by rfl⟩ : syracuseStep 383375 = 575063) B575063
theorem B383419 : Blo 381763 383419 := bstep (se 1 (by rfl) ⟨287564, by rfl⟩ : syracuseStep 383419 = 575129) B575129
theorem B383495 : Blo 381763 383495 := bstep (se 1 (by rfl) ⟨287621, by rfl⟩ : syracuseStep 383495 = 575243) B575243
theorem B383503 : Blo 381763 383503 := bstep (se 1 (by rfl) ⟨287627, by rfl⟩ : syracuseStep 383503 = 575255) B575255
theorem B1301021 : Blo 381763 1301021 := bstep (se 3 (by rfl) ⟨243941, by rfl⟩ : syracuseStep 1301021 = 487883) B487883
theorem B645691 : Blo 381763 645691 := bstep (se 1 (by rfl) ⟨484268, by rfl⟩ : syracuseStep 645691 = 968537) B968537
theorem B383547 : Blo 381763 383547 := bstep (se 1 (by rfl) ⟨287660, by rfl⟩ : syracuseStep 383547 = 575321) B575321
theorem B383623 : Blo 381763 383623 := bstep (se 1 (by rfl) ⟨287717, by rfl⟩ : syracuseStep 383623 = 575435) B575435
theorem B383631 : Blo 381763 383631 := bstep (se 1 (by rfl) ⟨287723, by rfl⟩ : syracuseStep 383631 = 575447) B575447
theorem B383675 : Blo 381763 383675 := bstep (se 1 (by rfl) ⟨287756, by rfl⟩ : syracuseStep 383675 = 575513) B575513
theorem B645833 : Blo 381763 645833 := bstep (se 2 (by rfl) ⟨242187, by rfl⟩ : syracuseStep 645833 = 484375) B484375
theorem B383751 : Blo 381763 383751 := bstep (se 1 (by rfl) ⟨287813, by rfl⟩ : syracuseStep 383751 = 575627) B575627
theorem B973579 : Blo 381763 973579 := bstep (se 1 (by rfl) ⟨730184, by rfl⟩ : syracuseStep 973579 = 1460369) B1460369
theorem B383759 : Blo 381763 383759 := bstep (se 1 (by rfl) ⟨287819, by rfl⟩ : syracuseStep 383759 = 575639) B575639
theorem B383803 : Blo 381763 383803 := bstep (se 1 (by rfl) ⟨287852, by rfl⟩ : syracuseStep 383803 = 575705) B575705
theorem B383879 : Blo 381763 383879 := bstep (se 1 (by rfl) ⟨287909, by rfl⟩ : syracuseStep 383879 = 575819) B575819
theorem B383887 : Blo 381763 383887 := bstep (se 1 (by rfl) ⟨287915, by rfl⟩ : syracuseStep 383887 = 575831) B575831
theorem B973721 : Blo 381763 973721 := bstep (se 2 (by rfl) ⟨365145, by rfl⟩ : syracuseStep 973721 = 730291) B730291
theorem B2775971 : Blo 381763 2775971 := bstep (se 1 (by rfl) ⟨2081978, by rfl⟩ : syracuseStep 2775971 = 4163957) B4163957
theorem B383931 : Blo 381763 383931 := bstep (se 1 (by rfl) ⟨287948, by rfl⟩ : syracuseStep 383931 = 575897) B575897
theorem B384007 : Blo 381763 384007 := bstep (se 1 (by rfl) ⟨288005, by rfl⟩ : syracuseStep 384007 = 576011) B576011
theorem B384015 : Blo 381763 384015 := bstep (se 1 (by rfl) ⟨288011, by rfl⟩ : syracuseStep 384015 = 576023) B576023
theorem B384059 : Blo 381763 384059 := bstep (se 1 (by rfl) ⟨288044, by rfl⟩ : syracuseStep 384059 = 576089) B576089
theorem B973883 : Blo 381763 973883 := bstep (se 1 (by rfl) ⟨730412, by rfl⟩ : syracuseStep 973883 = 1460825) B1460825
theorem B384135 : Blo 381763 384135 := bstep (se 1 (by rfl) ⟨288101, by rfl⟩ : syracuseStep 384135 = 576203) B576203
theorem B547975 : Blo 381763 547975 := bstep (se 1 (by rfl) ⟨410981, by rfl⟩ : syracuseStep 547975 = 821963) B821963
theorem B384143 : Blo 381763 384143 := bstep (se 1 (by rfl) ⟨288107, by rfl⟩ : syracuseStep 384143 = 576215) B576215
theorem B384187 : Blo 381763 384187 := bstep (se 1 (by rfl) ⟨288140, by rfl⟩ : syracuseStep 384187 = 576281) B576281
theorem B384263 : Blo 381763 384263 := bstep (se 1 (by rfl) ⟨288197, by rfl⟩ : syracuseStep 384263 = 576395) B576395
theorem B384271 : Blo 381763 384271 := bstep (se 1 (by rfl) ⟨288203, by rfl⟩ : syracuseStep 384271 = 576407) B576407
theorem B384315 : Blo 381763 384315 := bstep (se 1 (by rfl) ⟨288236, by rfl⟩ : syracuseStep 384315 = 576473) B576473
theorem B646535 : Blo 381763 646535 := bstep (se 1 (by rfl) ⟨484901, by rfl⟩ : syracuseStep 646535 = 969803) B969803
theorem B384391 : Blo 381763 384391 := bstep (se 1 (by rfl) ⟨288293, by rfl⟩ : syracuseStep 384391 = 576587) B576587
theorem B384399 : Blo 381763 384399 := bstep (se 1 (by rfl) ⟨288299, by rfl⟩ : syracuseStep 384399 = 576599) B576599
theorem B974227 : Blo 381763 974227 := bstep (se 1 (by rfl) ⟨730670, by rfl⟩ : syracuseStep 974227 = 1461341) B1461341
theorem B384443 : Blo 381763 384443 := bstep (se 1 (by rfl) ⟨288332, by rfl⟩ : syracuseStep 384443 = 576665) B576665
theorem B384519 : Blo 381763 384519 := bstep (se 1 (by rfl) ⟨288389, by rfl⟩ : syracuseStep 384519 = 576779) B576779
theorem B384527 : Blo 381763 384527 := bstep (se 1 (by rfl) ⟨288395, by rfl⟩ : syracuseStep 384527 = 576791) B576791
theorem B974369 : Blo 381763 974369 := bstep (se 2 (by rfl) ⟨365388, by rfl⟩ : syracuseStep 974369 = 730777) B730777
theorem B384571 : Blo 381763 384571 := bstep (se 1 (by rfl) ⟨288428, by rfl⟩ : syracuseStep 384571 = 576857) B576857
theorem B384647 : Blo 381763 384647 := bstep (se 1 (by rfl) ⟨288485, by rfl⟩ : syracuseStep 384647 = 576971) B576971
theorem B384655 : Blo 381763 384655 := bstep (se 1 (by rfl) ⟨288491, by rfl⟩ : syracuseStep 384655 = 576983) B576983
theorem B384699 : Blo 381763 384699 := bstep (se 1 (by rfl) ⟨288524, by rfl⟩ : syracuseStep 384699 = 577049) B577049
theorem B384775 : Blo 381763 384775 := bstep (se 1 (by rfl) ⟨288581, by rfl⟩ : syracuseStep 384775 = 577163) B577163
theorem B384783 : Blo 381763 384783 := bstep (se 1 (by rfl) ⟨288587, by rfl⟩ : syracuseStep 384783 = 577175) B577175
theorem B384827 : Blo 381763 384827 := bstep (se 1 (by rfl) ⟨288620, by rfl⟩ : syracuseStep 384827 = 577241) B577241
theorem B384903 : Blo 381763 384903 := bstep (se 1 (by rfl) ⟨288677, by rfl⟩ : syracuseStep 384903 = 577355) B577355
theorem B384911 : Blo 381763 384911 := bstep (se 1 (by rfl) ⟨288683, by rfl⟩ : syracuseStep 384911 = 577367) B577367
theorem B2187161 : Blo 381763 2187161 := bstep (se 2 (by rfl) ⟨820185, by rfl⟩ : syracuseStep 2187161 = 1640371) B1640371
theorem B384955 : Blo 381763 384955 := bstep (se 1 (by rfl) ⟨288716, by rfl⟩ : syracuseStep 384955 = 577433) B577433
theorem B548795 : Blo 381763 548795 := bstep (se 1 (by rfl) ⟨411596, by rfl⟩ : syracuseStep 548795 = 823193) B823193
theorem B385031 : Blo 381763 385031 := bstep (se 1 (by rfl) ⟨288773, by rfl⟩ : syracuseStep 385031 = 577547) B577547
theorem B647183 : Blo 381763 647183 := bstep (se 1 (by rfl) ⟨485387, by rfl⟩ : syracuseStep 647183 = 970775) B970775
theorem B385039 : Blo 381763 385039 := bstep (se 1 (by rfl) ⟨288779, by rfl⟩ : syracuseStep 385039 = 577559) B577559
theorem B385083 : Blo 381763 385083 := bstep (se 1 (by rfl) ⟨288812, by rfl⟩ : syracuseStep 385083 = 577625) B577625
theorem B385159 : Blo 381763 385159 := bstep (se 1 (by rfl) ⟨288869, by rfl⟩ : syracuseStep 385159 = 577739) B577739
theorem B385167 : Blo 381763 385167 := bstep (se 1 (by rfl) ⟨288875, by rfl⟩ : syracuseStep 385167 = 577751) B577751
theorem B483499 : Blo 381763 483499 := bstep (se 1 (by rfl) ⟨362624, by rfl⟩ : syracuseStep 483499 = 725249) B725249
theorem B385211 : Blo 381763 385211 := bstep (se 1 (by rfl) ⟨288908, by rfl⟩ : syracuseStep 385211 = 577817) B577817
theorem B516343 : Blo 381763 516343 := bstep (se 1 (by rfl) ⟨387257, by rfl⟩ : syracuseStep 516343 = 774515) B774515
theorem B385287 : Blo 381763 385287 := bstep (se 1 (by rfl) ⟨288965, by rfl⟩ : syracuseStep 385287 = 577931) B577931
theorem B385295 : Blo 381763 385295 := bstep (se 1 (by rfl) ⟨288971, by rfl⟩ : syracuseStep 385295 = 577943) B577943
theorem B385339 : Blo 381763 385339 := bstep (se 1 (by rfl) ⟨289004, by rfl⟩ : syracuseStep 385339 = 578009) B578009
theorem B385415 : Blo 381763 385415 := bstep (se 1 (by rfl) ⟨289061, by rfl⟩ : syracuseStep 385415 = 578123) B578123
theorem B483727 : Blo 381763 483727 := bstep (se 1 (by rfl) ⟨362795, by rfl⟩ : syracuseStep 483727 = 725591) B725591
theorem B385423 : Blo 381763 385423 := bstep (se 1 (by rfl) ⟨289067, by rfl⟩ : syracuseStep 385423 = 578135) B578135
theorem B385467 : Blo 381763 385467 := bstep (se 1 (by rfl) ⟨289100, by rfl⟩ : syracuseStep 385467 = 578201) B578201
theorem B975361 : Blo 381763 975361 := bstep (se 2 (by rfl) ⟨365760, by rfl⟩ : syracuseStep 975361 = 731521) B731521
theorem B385543 : Blo 381763 385543 := bstep (se 1 (by rfl) ⟨289157, by rfl⟩ : syracuseStep 385543 = 578315) B578315
theorem B385551 : Blo 381763 385551 := bstep (se 1 (by rfl) ⟨289163, by rfl⟩ : syracuseStep 385551 = 578327) B578327
theorem B647723 : Blo 381763 647723 := bstep (se 1 (by rfl) ⟨485792, by rfl⟩ : syracuseStep 647723 = 971585) B971585
theorem B385595 : Blo 381763 385595 := bstep (se 1 (by rfl) ⟨289196, by rfl⟩ : syracuseStep 385595 = 578393) B578393
theorem B385671 : Blo 381763 385671 := bstep (se 1 (by rfl) ⟨289253, by rfl⟩ : syracuseStep 385671 = 578507) B578507
theorem B385679 : Blo 381763 385679 := bstep (se 1 (by rfl) ⟨289259, by rfl⟩ : syracuseStep 385679 = 578519) B578519
theorem B385723 : Blo 381763 385723 := bstep (se 1 (by rfl) ⟨289292, by rfl⟩ : syracuseStep 385723 = 578585) B578585
theorem B582443 : Blo 381763 582443 := bstep (se 1 (by rfl) ⟨436832, by rfl⟩ : syracuseStep 582443 = 873665) B873665
theorem B648121 : Blo 381763 648121 := bstep (se 2 (by rfl) ⟨243045, by rfl⟩ : syracuseStep 648121 = 486091) B486091
theorem B517051 : Blo 381763 517051 := bstep (se 1 (by rfl) ⟨387788, by rfl⟩ : syracuseStep 517051 = 775577) B775577
theorem B2909195 : Blo 381763 2909195 := bstep (se 1 (by rfl) ⟨2181896, by rfl⟩ : syracuseStep 2909195 = 4363793) B4363793
theorem B975959 : Blo 381763 975959 := bstep (se 1 (by rfl) ⟨731969, by rfl⟩ : syracuseStep 975959 = 1463939) B1463939
theorem B484471 : Blo 381763 484471 := bstep (se 1 (by rfl) ⟨363353, by rfl⟩ : syracuseStep 484471 = 726707) B726707
theorem B976171 : Blo 381763 976171 := bstep (se 1 (by rfl) ⟨732128, by rfl⟩ : syracuseStep 976171 = 1464257) B1464257
theorem B1631623 : Blo 381763 1631623 := bstep (se 1 (by rfl) ⟨1223717, by rfl⟩ : syracuseStep 1631623 = 2447435) B2447435
theorem B976313 : Blo 381763 976313 := bstep (se 2 (by rfl) ⟨366117, by rfl⟩ : syracuseStep 976313 = 732235) B732235
theorem B484795 : Blo 381763 484795 := bstep (se 1 (by rfl) ⟨363596, by rfl⟩ : syracuseStep 484795 = 727193) B727193
theorem B4384205 : Blo 381763 4384205 := bstep (se 3 (by rfl) ⟨822038, by rfl⟩ : syracuseStep 4384205 = 1644077) B1644077
theorem B648823 : Blo 381763 648823 := bstep (se 1 (by rfl) ⟨486617, by rfl⟩ : syracuseStep 648823 = 973235) B973235
theorem B1631981 : Blo 381763 1631981 := bstep (se 3 (by rfl) ⟨305996, by rfl⟩ : syracuseStep 1631981 = 611993) B611993
theorem B6219521 : Blo 381763 6219521 := bstep (se 2 (by rfl) ⟨2332320, by rfl⟩ : syracuseStep 6219521 = 4664641) B4664641
theorem B649019 : Blo 381763 649019 := bstep (se 1 (by rfl) ⟨486764, by rfl⟩ : syracuseStep 649019 = 973529) B973529
theorem B780167 : Blo 381763 780167 := bstep (se 1 (by rfl) ⟨585125, by rfl⟩ : syracuseStep 780167 = 1170251) B1170251
theorem B485291 : Blo 381763 485291 := bstep (se 1 (by rfl) ⟨363968, by rfl⟩ : syracuseStep 485291 = 727937) B727937
theorem B518089 : Blo 381763 518089 := bstep (se 2 (by rfl) ⟨194283, by rfl⟩ : syracuseStep 518089 = 388567) B388567
theorem B6973613 : Blo 381763 6973613 := bstep (se 3 (by rfl) ⟨1307552, by rfl⟩ : syracuseStep 6973613 = 2615105) B2615105
theorem B649417 : Blo 381763 649417 := bstep (se 2 (by rfl) ⟨243531, by rfl⟩ : syracuseStep 649417 = 487063) B487063
theorem B4155779 : Blo 381763 4155779 := bstep (se 1 (by rfl) ⟨3116834, by rfl⟩ : syracuseStep 4155779 = 6233669) B6233669
theorem B485767 : Blo 381763 485767 := bstep (se 1 (by rfl) ⟨364325, by rfl⟩ : syracuseStep 485767 = 728651) B728651
theorem B780815 : Blo 381763 780815 := bstep (se 1 (by rfl) ⟨585611, by rfl⟩ : syracuseStep 780815 = 1171223) B1171223
theorem B3992165 : Blo 381763 3992165 := bstep (se 4 (by rfl) ⟨374265, by rfl⟩ : syracuseStep 3992165 = 748531) B748531
theorem B59894549 : Blo 381763 59894549 := bstep (se 6 (by rfl) ⟨1403778, by rfl⟩ : syracuseStep 59894549 = 2807557) B2807557
theorem B486263 : Blo 381763 486263 := bstep (se 1 (by rfl) ⟨364697, by rfl⟩ : syracuseStep 486263 = 729395) B729395
theorem B650119 : Blo 381763 650119 := bstep (se 1 (by rfl) ⟨487589, by rfl⟩ : syracuseStep 650119 = 975179) B975179
theorem B2911139 : Blo 381763 2911139 := bstep (se 1 (by rfl) ⟨2183354, by rfl⟩ : syracuseStep 2911139 = 4366709) B4366709
theorem B486415 : Blo 381763 486415 := bstep (se 1 (by rfl) ⟨364811, by rfl⟩ : syracuseStep 486415 = 729623) B729623
theorem B2190509 : Blo 381763 2190509 := bstep (se 3 (by rfl) ⟨410720, by rfl⟩ : syracuseStep 2190509 = 821441) B821441
theorem B486587 : Blo 381763 486587 := bstep (se 1 (by rfl) ⟨364940, by rfl⟩ : syracuseStep 486587 = 729881) B729881
theorem B650767 : Blo 381763 650767 := bstep (se 1 (by rfl) ⟨488075, by rfl⟩ : syracuseStep 650767 = 976151) B976151
theorem B487559 : Blo 381763 487559 := bstep (se 1 (by rfl) ⟨365669, by rfl⟩ : syracuseStep 487559 = 731339) B731339
theorem B4157729 : Blo 381763 4157729 := bstep (se 2 (by rfl) ⟨1559148, by rfl⟩ : syracuseStep 4157729 = 3118297) B3118297
theorem B520711 : Blo 381763 520711 := bstep (se 1 (by rfl) ⟨390533, by rfl⟩ : syracuseStep 520711 = 781067) B781067
theorem B4452893 : Blo 381763 4452893 := bstep (se 3 (by rfl) ⟨834917, by rfl⟩ : syracuseStep 4452893 = 1669835) B1669835
theorem B586487 : Blo 381763 586487 := bstep (se 1 (by rfl) ⟨439865, by rfl⟩ : syracuseStep 586487 = 879731) B879731
theorem B520975 : Blo 381763 520975 := bstep (se 1 (by rfl) ⟨390731, by rfl⟩ : syracuseStep 520975 = 781463) B781463
theorem B488207 : Blo 381763 488207 := bstep (se 1 (by rfl) ⟨366155, by rfl⟩ : syracuseStep 488207 = 732311) B732311
theorem B816161 : Blo 381763 816161 := bstep (se 2 (by rfl) ⟨306060, by rfl⟩ : syracuseStep 816161 = 612121) B612121
theorem B521273 : Blo 381763 521273 := bstep (se 2 (by rfl) ⟨195477, by rfl⟩ : syracuseStep 521273 = 390955) B390955
theorem B816247 : Blo 381763 816247 := bstep (se 1 (by rfl) ⟨612185, by rfl⟩ : syracuseStep 816247 = 1224371) B1224371
theorem B2913569 : Blo 381763 2913569 := bstep (se 2 (by rfl) ⟨1092588, by rfl⟩ : syracuseStep 2913569 = 2185177) B2185177
theorem B6714809 : Blo 381763 6714809 := bstep (se 2 (by rfl) ⟨2518053, by rfl⟩ : syracuseStep 6714809 = 5036107) B5036107
theorem B980851 : Blo 381763 980851 := bstep (se 1 (by rfl) ⟨735638, by rfl⟩ : syracuseStep 980851 = 1471277) B1471277
theorem B2914541 : Blo 381763 2914541 := bstep (se 3 (by rfl) ⟨546476, by rfl⟩ : syracuseStep 2914541 = 1092953) B1092953
theorem B8288729 : Blo 381763 8288729 := bstep (se 2 (by rfl) ⟨3108273, by rfl⟩ : syracuseStep 8288729 = 6216547) B6216547
theorem B1309303 : Blo 381763 1309303 := bstep (se 1 (by rfl) ⟨981977, by rfl⟩ : syracuseStep 1309303 = 1963955) B1963955
theorem B2456891 : Blo 381763 2456891 := bstep (se 1 (by rfl) ⟨1842668, by rfl⟩ : syracuseStep 2456891 = 3685337) B3685337
theorem B9305549 : Blo 381763 9305549 := bstep (se 3 (by rfl) ⟨1744790, by rfl⟩ : syracuseStep 9305549 = 3489581) B3489581
theorem B1965521 : Blo 381763 1965521 := bstep (se 2 (by rfl) ⟨737070, by rfl⟩ : syracuseStep 1965521 = 1474141) B1474141
theorem B2195201 : Blo 381763 2195201 := bstep (se 2 (by rfl) ⟨823200, by rfl⟩ : syracuseStep 2195201 = 1646401) B1646401
theorem B1376033 : Blo 381763 1376033 := bstep (se 2 (by rfl) ⟨516012, by rfl⟩ : syracuseStep 1376033 = 1032025) B1032025
theorem B2064179 : Blo 381763 2064179 := bstep (se 1 (by rfl) ⟨1548134, by rfl⟩ : syracuseStep 2064179 = 3096269) B3096269
theorem B1933145 : Blo 381763 1933145 := bstep (se 2 (by rfl) ⟨724929, by rfl⟩ : syracuseStep 1933145 = 1449859) B1449859
theorem B982903 : Blo 381763 982903 := bstep (se 1 (by rfl) ⟨737177, by rfl⟩ : syracuseStep 982903 = 1474355) B1474355
theorem B5898269 : Blo 381763 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B1933469 : Blo 381763 1933469 := bstep (se 3 (by rfl) ⟨362525, by rfl⟩ : syracuseStep 1933469 = 725051) B725051
theorem B688457 : Blo 381763 688457 := bstep (se 2 (by rfl) ⟨258171, by rfl⟩ : syracuseStep 688457 = 516343) B516343
theorem B4915829 : Blo 381763 4915829 := bstep (se 5 (by rfl) ⟨230429, by rfl⟩ : syracuseStep 4915829 = 460859) B460859
theorem B6587243 : Blo 381763 6587243 := bstep (se 1 (by rfl) ⟨4940432, by rfl⟩ : syracuseStep 6587243 = 9880865) B9880865
theorem B1082299 : Blo 381763 1082299 := bstep (se 1 (by rfl) ⟨811724, by rfl⟩ : syracuseStep 1082299 = 1623449) B1623449
theorem B689401 : Blo 381763 689401 := bstep (se 2 (by rfl) ⟨258525, by rfl⟩ : syracuseStep 689401 = 517051) B517051
theorem B5506319 : Blo 381763 5506319 := bstep (se 1 (by rfl) ⟨4129739, by rfl⟩ : syracuseStep 5506319 = 8259479) B8259479
theorem B1934765 : Blo 381763 1934765 := bstep (se 3 (by rfl) ⟨362768, by rfl⟩ : syracuseStep 1934765 = 725537) B725537
theorem B820775 : Blo 381763 820775 := bstep (se 1 (by rfl) ⟨615581, by rfl⟩ : syracuseStep 820775 = 1231163) B1231163
theorem B2918429 : Blo 381763 2918429 := bstep (se 3 (by rfl) ⟨547205, by rfl⟩ : syracuseStep 2918429 = 1094411) B1094411
theorem B1837171 : Blo 381763 1837171 := bstep (se 1 (by rfl) ⟨1377878, by rfl⟩ : syracuseStep 1837171 = 2755757) B2755757
theorem B2459965 : Blo 381763 2459965 := bstep (se 3 (by rfl) ⟨461243, by rfl⟩ : syracuseStep 2459965 = 922487) B922487
theorem B920027 : Blo 381763 920027 := bstep (se 1 (by rfl) ⟨690020, by rfl⟩ : syracuseStep 920027 = 1380041) B1380041
theorem B1640969 : Blo 381763 1640969 := bstep (se 2 (by rfl) ⟨615363, by rfl⟩ : syracuseStep 1640969 = 1230727) B1230727
theorem B690785 : Blo 381763 690785 := bstep (se 2 (by rfl) ⟨259044, by rfl⟩ : syracuseStep 690785 = 518089) B518089
theorem B2067383 : Blo 381763 2067383 := bstep (se 1 (by rfl) ⟨1550537, by rfl⟩ : syracuseStep 2067383 = 3101075) B3101075
theorem B1936385 : Blo 381763 1936385 := bstep (se 2 (by rfl) ⟨726144, by rfl⟩ : syracuseStep 1936385 = 1452289) B1452289
theorem B6982949 : Blo 381763 6982949 := bstep (se 4 (by rfl) ⟨654651, by rfl⟩ : syracuseStep 6982949 = 1309303) B1309303
theorem B2461043 : Blo 381763 2461043 := bstep (se 1 (by rfl) ⟨1845782, by rfl⟩ : syracuseStep 2461043 = 3691565) B3691565
theorem B2461195 : Blo 381763 2461195 := bstep (se 1 (by rfl) ⟨1845896, by rfl⟩ : syracuseStep 2461195 = 3691793) B3691793
theorem B429691 : Blo 381763 429691 := bstep (se 1 (by rfl) ⟨322268, by rfl⟩ : syracuseStep 429691 = 644537) B644537
theorem B1937195 : Blo 381763 1937195 := bstep (se 1 (by rfl) ⟨1452896, by rfl⟩ : syracuseStep 1937195 = 2905793) B2905793
theorem B2330477 : Blo 381763 2330477 := bstep (se 3 (by rfl) ⟨436964, by rfl⟩ : syracuseStep 2330477 = 873929) B873929
theorem B921527 : Blo 381763 921527 := bstep (se 1 (by rfl) ⟨691145, by rfl⟩ : syracuseStep 921527 = 1382291) B1382291
theorem B692263 : Blo 381763 692263 := bstep (se 1 (by rfl) ⟨519197, by rfl⟩ : syracuseStep 692263 = 1038395) B1038395
theorem B430159 : Blo 381763 430159 := bstep (se 1 (by rfl) ⟨322619, by rfl⟩ : syracuseStep 430159 = 645239) B645239
theorem B4427891 : Blo 381763 4427891 := bstep (se 1 (by rfl) ⟨3320918, by rfl⟩ : syracuseStep 4427891 = 6641837) B6641837
theorem B725203 : Blo 381763 725203 := bstep (se 1 (by rfl) ⟨543902, by rfl⟩ : syracuseStep 725203 = 1087805) B1087805
theorem B725431 : Blo 381763 725431 := bstep (se 1 (by rfl) ⟨544073, by rfl⟩ : syracuseStep 725431 = 1088147) B1088147
theorem B430555 : Blo 381763 430555 := bstep (se 1 (by rfl) ⟨322916, by rfl⟩ : syracuseStep 430555 = 645833) B645833
theorem B331321873 : Blo 381763 331321873 := bstep (se 2 (by rfl) ⟨124245702, by rfl⟩ : syracuseStep 331321873 = 248491405) B248491405
theorem B9900755 : Blo 381763 9900755 := bstep (se 1 (by rfl) ⟨7425566, by rfl⟩ : syracuseStep 9900755 = 14851133) B14851133
theorem B4166417 : Blo 381763 4166417 := bstep (se 2 (by rfl) ⟨1562406, by rfl⟩ : syracuseStep 4166417 = 3124813) B3124813
theorem B431023 : Blo 381763 431023 := bstep (se 1 (by rfl) ⟨323267, by rfl⟩ : syracuseStep 431023 = 646535) B646535
theorem B726023 : Blo 381763 726023 := bstep (se 1 (by rfl) ⟨544517, by rfl⟩ : syracuseStep 726023 = 1089035) B1089035
theorem B431455 : Blo 381763 431455 := bstep (se 1 (by rfl) ⟨323591, by rfl⟩ : syracuseStep 431455 = 647183) B647183
theorem B2627261 : Blo 381763 2627261 := bstep (se 3 (by rfl) ⟨492611, by rfl⟩ : syracuseStep 2627261 = 985223) B985223
theorem B431815 : Blo 381763 431815 := bstep (se 1 (by rfl) ⟨323861, by rfl⟩ : syracuseStep 431815 = 647723) B647723
theorem B726889 : Blo 381763 726889 := bstep (se 2 (by rfl) ⟨272583, by rfl⟩ : syracuseStep 726889 = 545167) B545167
theorem B1939463 : Blo 381763 1939463 := bstep (se 1 (by rfl) ⟨1454597, by rfl⟩ : syracuseStep 1939463 = 2909195) B2909195
theorem B727049 : Blo 381763 727049 := bstep (se 2 (by rfl) ⟨272643, by rfl⟩ : syracuseStep 727049 = 545287) B545287
theorem B2922803 : Blo 381763 2922803 := bstep (se 1 (by rfl) ⟨2192102, by rfl⟩ : syracuseStep 2922803 = 4384205) B4384205
theorem B1939949 : Blo 381763 1939949 := bstep (se 3 (by rfl) ⟨363740, by rfl⟩ : syracuseStep 1939949 = 727481) B727481
theorem B1087987 : Blo 381763 1087987 := bstep (se 1 (by rfl) ⟨815990, by rfl⟩ : syracuseStep 1087987 = 1631981) B1631981
theorem B3545633 : Blo 381763 3545633 := bstep (se 2 (by rfl) ⟨1329612, by rfl⟩ : syracuseStep 3545633 = 2659225) B2659225
theorem B432679 : Blo 381763 432679 := bstep (se 1 (by rfl) ⟨324509, by rfl⟩ : syracuseStep 432679 = 649019) B649019
theorem B1088329 : Blo 381763 1088329 := bstep (se 2 (by rfl) ⟨408123, by rfl⟩ : syracuseStep 1088329 = 816247) B816247
theorem B859067 : Blo 381763 859067 := bstep (se 1 (by rfl) ⟨644300, by rfl⟩ : syracuseStep 859067 = 1288601) B1288601
theorem B859193 : Blo 381763 859193 := bstep (se 2 (by rfl) ⟨322197, by rfl⟩ : syracuseStep 859193 = 644395) B644395
theorem B2661443 : Blo 381763 2661443 := bstep (se 1 (by rfl) ⟨1996082, by rfl⟩ : syracuseStep 2661443 = 3992165) B3992165
theorem B1940759 : Blo 381763 1940759 := bstep (se 1 (by rfl) ⟨1455569, by rfl⟩ : syracuseStep 1940759 = 2911139) B2911139
theorem B400763 : Blo 381763 400763 := bstep (se 1 (by rfl) ⟨300572, by rfl⟩ : syracuseStep 400763 = 601145) B601145
theorem B859535 : Blo 381763 859535 := bstep (se 1 (by rfl) ⟨644651, by rfl⟩ : syracuseStep 859535 = 1289303) B1289303
theorem B728507 : Blo 381763 728507 := bstep (se 1 (by rfl) ⟨546380, by rfl⟩ : syracuseStep 728507 = 1092761) B1092761
theorem B859859 : Blo 381763 859859 := bstep (se 1 (by rfl) ⟨644894, by rfl⟩ : syracuseStep 859859 = 1289789) B1289789
theorem B7020269 : Blo 381763 7020269 := bstep (se 3 (by rfl) ⟨1316300, by rfl⟩ : syracuseStep 7020269 = 2632601) B2632601
theorem B2367299 : Blo 381763 2367299 := bstep (se 1 (by rfl) ⟨1775474, by rfl⟩ : syracuseStep 2367299 = 3550949) B3550949
theorem B728939 : Blo 381763 728939 := bstep (se 1 (by rfl) ⟨546704, by rfl⟩ : syracuseStep 728939 = 1093409) B1093409
theorem B728993 : Blo 381763 728993 := bstep (se 2 (by rfl) ⟨273372, by rfl⟩ : syracuseStep 728993 = 546745) B546745
theorem B1450345 : Blo 381763 1450345 := bstep (se 2 (by rfl) ⟨543879, by rfl⟩ : syracuseStep 1450345 = 1087759) B1087759
theorem B8495641 : Blo 381763 8495641 := bstep (se 2 (by rfl) ⟨3185865, by rfl⟩ : syracuseStep 8495641 = 6371731) B6371731
theorem B1450619 : Blo 381763 1450619 := bstep (se 1 (by rfl) ⟨1087964, by rfl⟩ : syracuseStep 1450619 = 2175929) B2175929
theorem B860795 : Blo 381763 860795 := bstep (se 1 (by rfl) ⟨645596, by rfl⟩ : syracuseStep 860795 = 1291193) B1291193
theorem B860921 : Blo 381763 860921 := bstep (se 2 (by rfl) ⟨322845, by rfl⟩ : syracuseStep 860921 = 645691) B645691
theorem B1942379 : Blo 381763 1942379 := bstep (se 1 (by rfl) ⟨1456784, by rfl⟩ : syracuseStep 1942379 = 2913569) B2913569
theorem B861191 : Blo 381763 861191 := bstep (se 1 (by rfl) ⟨645893, by rfl⟩ : syracuseStep 861191 = 1291787) B1291787
theorem B861263 : Blo 381763 861263 := bstep (se 1 (by rfl) ⟨645947, by rfl⟩ : syracuseStep 861263 = 1291895) B1291895
theorem B861659 : Blo 381763 861659 := bstep (se 1 (by rfl) ⟨646244, by rfl⟩ : syracuseStep 861659 = 1292489) B1292489
theorem B1943027 : Blo 381763 1943027 := bstep (se 1 (by rfl) ⟨1457270, by rfl⟩ : syracuseStep 1943027 = 2914541) B2914541
theorem B730633 : Blo 381763 730633 := bstep (se 2 (by rfl) ⟨273987, by rfl⟩ : syracuseStep 730633 = 547975) B547975
theorem B2762363 : Blo 381763 2762363 := bstep (se 1 (by rfl) ⟨2071772, by rfl⟩ : syracuseStep 2762363 = 4143545) B4143545
theorem B2762387 : Blo 381763 2762387 := bstep (se 1 (by rfl) ⟨2071790, by rfl⟩ : syracuseStep 2762387 = 4143581) B4143581
theorem B665417 : Blo 381763 665417 := bstep (se 2 (by rfl) ⟨249531, by rfl⟩ : syracuseStep 665417 = 499063) B499063
theorem B2107255 : Blo 381763 2107255 := bstep (se 1 (by rfl) ⟨1580441, by rfl⟩ : syracuseStep 2107255 = 3160883) B3160883
theorem B862127 : Blo 381763 862127 := bstep (se 1 (by rfl) ⟨646595, by rfl⟩ : syracuseStep 862127 = 1293191) B1293191
theorem B7350371 : Blo 381763 7350371 := bstep (se 1 (by rfl) ⟨5512778, by rfl⟩ : syracuseStep 7350371 = 11025557) B11025557
theorem B862379 : Blo 381763 862379 := bstep (se 1 (by rfl) ⟨646784, by rfl⟩ : syracuseStep 862379 = 1293569) B1293569
theorem B6203699 : Blo 381763 6203699 := bstep (se 1 (by rfl) ⟨4652774, by rfl⟩ : syracuseStep 6203699 = 9305549) B9305549
theorem B731567 : Blo 381763 731567 := bstep (se 1 (by rfl) ⟨548675, by rfl⟩ : syracuseStep 731567 = 1097351) B1097351
theorem B1288763 : Blo 381763 1288763 := bstep (se 1 (by rfl) ⟨966572, by rfl⟩ : syracuseStep 1288763 = 1933145) B1933145
theorem B862919 : Blo 381763 862919 := bstep (se 1 (by rfl) ⟨647189, by rfl⟩ : syracuseStep 862919 = 1294379) B1294379
theorem B1944323 : Blo 381763 1944323 := bstep (se 1 (by rfl) ⟨1458242, by rfl⟩ : syracuseStep 1944323 = 2916485) B2916485
theorem B1387307 : Blo 381763 1387307 := bstep (se 1 (by rfl) ⟨1040480, by rfl⟩ : syracuseStep 1387307 = 2080961) B2080961
theorem B1289033 : Blo 381763 1289033 := bstep (se 2 (by rfl) ⟨483387, by rfl⟩ : syracuseStep 1289033 = 966775) B966775
theorem B732091 : Blo 381763 732091 := bstep (se 1 (by rfl) ⟨549068, by rfl⟩ : syracuseStep 732091 = 1098137) B1098137
theorem B863783 : Blo 381763 863783 := bstep (se 1 (by rfl) ⟨647837, by rfl⟩ : syracuseStep 863783 = 1295675) B1295675
theorem B1552223 : Blo 381763 1552223 := bstep (se 1 (by rfl) ⟨1164167, by rfl⟩ : syracuseStep 1552223 = 2328335) B2328335
theorem B864107 : Blo 381763 864107 := bstep (se 1 (by rfl) ⟨648080, by rfl⟩ : syracuseStep 864107 = 1296161) B1296161
theorem B864161 : Blo 381763 864161 := bstep (se 2 (by rfl) ⟨324060, by rfl⟩ : syracuseStep 864161 = 648121) B648121
theorem B1290167 : Blo 381763 1290167 := bstep (se 1 (by rfl) ⟨967625, by rfl⟩ : syracuseStep 1290167 = 1935251) B1935251
theorem B1224857 : Blo 381763 1224857 := bstep (se 2 (by rfl) ⟨459321, by rfl⟩ : syracuseStep 1224857 = 918643) B918643
theorem B1454233 : Blo 381763 1454233 := bstep (se 2 (by rfl) ⟨545337, by rfl⟩ : syracuseStep 1454233 = 1090675) B1090675
theorem B864503 : Blo 381763 864503 := bstep (se 1 (by rfl) ⟨648377, by rfl⟩ : syracuseStep 864503 = 1296755) B1296755
theorem B1945943 : Blo 381763 1945943 := bstep (se 1 (by rfl) ⟨1459457, by rfl⟩ : syracuseStep 1945943 = 2918915) B2918915
theorem B1454537 : Blo 381763 1454537 := bstep (se 2 (by rfl) ⟨545451, by rfl⟩ : syracuseStep 1454537 = 1090903) B1090903
theorem B2175497 : Blo 381763 2175497 := bstep (se 2 (by rfl) ⟨815811, by rfl⟩ : syracuseStep 2175497 = 1631623) B1631623
theorem B1290761 : Blo 381763 1290761 := bstep (se 2 (by rfl) ⟨484035, by rfl⟩ : syracuseStep 1290761 = 968071) B968071
theorem B2470459 : Blo 381763 2470459 := bstep (se 1 (by rfl) ⟨1852844, by rfl⟩ : syracuseStep 2470459 = 3705689) B3705689
theorem B2765447 : Blo 381763 2765447 := bstep (se 1 (by rfl) ⟨2074085, by rfl⟩ : syracuseStep 2765447 = 4148171) B4148171
theorem B865097 : Blo 381763 865097 := bstep (se 2 (by rfl) ⟨324411, by rfl⟩ : syracuseStep 865097 = 648823) B648823
theorem B1455023 : Blo 381763 1455023 := bstep (se 1 (by rfl) ⟨1091267, by rfl⟩ : syracuseStep 1455023 = 2182535) B2182535
theorem B1553489 : Blo 381763 1553489 := bstep (se 2 (by rfl) ⟨582558, by rfl⟩ : syracuseStep 1553489 = 1165117) B1165117
theorem B2176247 : Blo 381763 2176247 := bstep (se 1 (by rfl) ⟨1632185, by rfl⟩ : syracuseStep 2176247 = 3264371) B3264371
theorem B1291625 : Blo 381763 1291625 := bstep (se 2 (by rfl) ⟨484359, by rfl⟩ : syracuseStep 1291625 = 968719) B968719
theorem B2176429 : Blo 381763 2176429 := bstep (se 3 (by rfl) ⟨408080, by rfl⟩ : syracuseStep 2176429 = 816161) B816161
theorem B1390061 : Blo 381763 1390061 := bstep (se 3 (by rfl) ⟨260636, by rfl⟩ : syracuseStep 1390061 = 521273) B521273
theorem B767497 : Blo 381763 767497 := bstep (se 2 (by rfl) ⟨287811, by rfl⟩ : syracuseStep 767497 = 575623) B575623
theorem B865889 : Blo 381763 865889 := bstep (se 2 (by rfl) ⟨324708, by rfl⟩ : syracuseStep 865889 = 649417) B649417
theorem B9287459 : Blo 381763 9287459 := bstep (se 1 (by rfl) ⟨6965594, by rfl⟩ : syracuseStep 9287459 = 13931189) B13931189
theorem B4667179 : Blo 381763 4667179 := bstep (se 1 (by rfl) ⟨3500384, by rfl⟩ : syracuseStep 4667179 = 7000769) B7000769
theorem B866231 : Blo 381763 866231 := bstep (se 1 (by rfl) ⟨649673, by rfl⟩ : syracuseStep 866231 = 1299347) B1299347
theorem B2176955 : Blo 381763 2176955 := bstep (se 1 (by rfl) ⟨1632716, by rfl⟩ : syracuseStep 2176955 = 3265433) B3265433
theorem B1292219 : Blo 381763 1292219 := bstep (se 1 (by rfl) ⟨969164, by rfl⟩ : syracuseStep 1292219 = 1938329) B1938329
theorem B1227113 : Blo 381763 1227113 := bstep (se 2 (by rfl) ⟨460167, by rfl⟩ : syracuseStep 1227113 = 920335) B920335
theorem B1554817 : Blo 381763 1554817 := bstep (se 2 (by rfl) ⟨583056, by rfl⟩ : syracuseStep 1554817 = 1166113) B1166113
theorem B1456649 : Blo 381763 1456649 := bstep (se 2 (by rfl) ⟨546243, by rfl⟩ : syracuseStep 1456649 = 1092487) B1092487
theorem B866825 : Blo 381763 866825 := bstep (se 2 (by rfl) ⟨325059, by rfl⟩ : syracuseStep 866825 = 650119) B650119
theorem B14989859 : Blo 381763 14989859 := bstep (se 1 (by rfl) ⟨11242394, by rfl⟩ : syracuseStep 14989859 = 22484789) B22484789
theorem B867167 : Blo 381763 867167 := bstep (se 1 (by rfl) ⟨650375, by rfl⟩ : syracuseStep 867167 = 1300751) B1300751
theorem B1555307 : Blo 381763 1555307 := bstep (se 1 (by rfl) ⟨1166480, by rfl⟩ : syracuseStep 1555307 = 2332961) B2332961
theorem B867347 : Blo 381763 867347 := bstep (se 1 (by rfl) ⟨650510, by rfl⟩ : syracuseStep 867347 = 1301021) B1301021
theorem B1096861 : Blo 381763 1096861 := bstep (se 3 (by rfl) ⟨205661, by rfl⟩ : syracuseStep 1096861 = 411323) B411323
theorem B1850647 : Blo 381763 1850647 := bstep (se 1 (by rfl) ⟨1387985, by rfl⟩ : syracuseStep 1850647 = 2775971) B2775971
theorem B572777 : Blo 381763 572777 := bstep (se 2 (by rfl) ⟨214791, by rfl⟩ : syracuseStep 572777 = 429583) B429583
theorem B867689 : Blo 381763 867689 := bstep (se 2 (by rfl) ⟨325383, by rfl⟩ : syracuseStep 867689 = 650767) B650767
theorem B572855 : Blo 381763 572855 := bstep (se 1 (by rfl) ⟨429641, by rfl⟩ : syracuseStep 572855 = 859283) B859283
theorem B572891 : Blo 381763 572891 := bstep (se 1 (by rfl) ⟨429668, by rfl⟩ : syracuseStep 572891 = 859337) B859337
theorem B1293947 : Blo 381763 1293947 := bstep (se 1 (by rfl) ⟨970460, by rfl⟩ : syracuseStep 1293947 = 1940921) B1940921
theorem B1294109 : Blo 381763 1294109 := bstep (se 3 (by rfl) ⟨242645, by rfl⟩ : syracuseStep 1294109 = 485291) B485291
theorem B1949507 : Blo 381763 1949507 := bstep (se 1 (by rfl) ⟨1462130, by rfl⟩ : syracuseStep 1949507 = 2924261) B2924261
theorem B573359 : Blo 381763 573359 := bstep (se 1 (by rfl) ⟨430019, by rfl⟩ : syracuseStep 573359 = 860039) B860039
theorem B1458107 : Blo 381763 1458107 := bstep (se 1 (by rfl) ⟨1093580, by rfl⟩ : syracuseStep 1458107 = 2187161) B2187161
theorem B573449 : Blo 381763 573449 := bstep (se 2 (by rfl) ⟨215043, by rfl⟩ : syracuseStep 573449 = 430087) B430087
theorem B573479 : Blo 381763 573479 := bstep (se 1 (by rfl) ⟨430109, by rfl⟩ : syracuseStep 573479 = 860219) B860219
theorem B573563 : Blo 381763 573563 := bstep (se 1 (by rfl) ⟨430172, by rfl⟩ : syracuseStep 573563 = 860345) B860345
theorem B573689 : Blo 381763 573689 := bstep (se 2 (by rfl) ⟨215133, by rfl⟩ : syracuseStep 573689 = 430267) B430267
theorem B573791 : Blo 381763 573791 := bstep (se 1 (by rfl) ⟨430343, by rfl⟩ : syracuseStep 573791 = 860687) B860687
theorem B573803 : Blo 381763 573803 := bstep (se 1 (by rfl) ⟨430352, by rfl⟩ : syracuseStep 573803 = 860705) B860705
theorem B1294811 : Blo 381763 1294811 := bstep (se 1 (by rfl) ⟨971108, by rfl⟩ : syracuseStep 1294811 = 1942217) B1942217
theorem B574031 : Blo 381763 574031 := bstep (se 1 (by rfl) ⟨430523, by rfl⟩ : syracuseStep 574031 = 861047) B861047
theorem B1557089 : Blo 381763 1557089 := bstep (se 2 (by rfl) ⟨583908, by rfl⟩ : syracuseStep 1557089 = 1167817) B1167817
theorem B574151 : Blo 381763 574151 := bstep (se 1 (by rfl) ⟨430613, by rfl⟩ : syracuseStep 574151 = 861227) B861227
theorem B574313 : Blo 381763 574313 := bstep (se 2 (by rfl) ⟨215367, by rfl⟩ : syracuseStep 574313 = 430735) B430735
theorem B967585 : Blo 381763 967585 := bstep (se 2 (by rfl) ⟨362844, by rfl⟩ : syracuseStep 967585 = 725689) B725689
theorem B574391 : Blo 381763 574391 := bstep (se 1 (by rfl) ⟨430793, by rfl⟩ : syracuseStep 574391 = 861587) B861587
theorem B574427 : Blo 381763 574427 := bstep (se 1 (by rfl) ⟨430820, by rfl⟩ : syracuseStep 574427 = 861641) B861641
theorem B1295513 : Blo 381763 1295513 := bstep (se 2 (by rfl) ⟨485817, by rfl⟩ : syracuseStep 1295513 = 971635) B971635
theorem B4146347 : Blo 381763 4146347 := bstep (se 1 (by rfl) ⟨3109760, by rfl⟩ : syracuseStep 4146347 = 6219521) B6219521
theorem B574895 : Blo 381763 574895 := bstep (se 1 (by rfl) ⟨431171, by rfl⟩ : syracuseStep 574895 = 862343) B862343
theorem B574985 : Blo 381763 574985 := bstep (se 2 (by rfl) ⟨215619, by rfl⟩ : syracuseStep 574985 = 431239) B431239
theorem B575015 : Blo 381763 575015 := bstep (se 1 (by rfl) ⟨431261, by rfl⟩ : syracuseStep 575015 = 862523) B862523
theorem B2082343 : Blo 381763 2082343 := bstep (se 1 (by rfl) ⟨1561757, by rfl⟩ : syracuseStep 2082343 = 3123515) B3123515
theorem B2770519 : Blo 381763 2770519 := bstep (se 1 (by rfl) ⟨2077889, by rfl⟩ : syracuseStep 2770519 = 4155779) B4155779
theorem B575099 : Blo 381763 575099 := bstep (se 1 (by rfl) ⟨431324, by rfl⟩ : syracuseStep 575099 = 862649) B862649
theorem B6211217 : Blo 381763 6211217 := bstep (se 2 (by rfl) ⟨2329206, by rfl⟩ : syracuseStep 6211217 = 4658413) B4658413
theorem B1230547 : Blo 381763 1230547 := bstep (se 1 (by rfl) ⟨922910, by rfl⟩ : syracuseStep 1230547 = 1845821) B1845821
theorem B575225 : Blo 381763 575225 := bstep (se 2 (by rfl) ⟨215709, by rfl⟩ : syracuseStep 575225 = 431419) B431419
theorem B575327 : Blo 381763 575327 := bstep (se 1 (by rfl) ⟨431495, by rfl⟩ : syracuseStep 575327 = 862991) B862991
theorem B39929699 : Blo 381763 39929699 := bstep (se 1 (by rfl) ⟨29947274, by rfl⟩ : syracuseStep 39929699 = 59894549) B59894549
theorem B575339 : Blo 381763 575339 := bstep (se 1 (by rfl) ⟨431504, by rfl⟩ : syracuseStep 575339 = 863009) B863009
theorem B575567 : Blo 381763 575567 := bstep (se 1 (by rfl) ⟨431675, by rfl⟩ : syracuseStep 575567 = 863351) B863351
theorem B1460339 : Blo 381763 1460339 := bstep (se 1 (by rfl) ⟨1095254, by rfl⟩ : syracuseStep 1460339 = 2190509) B2190509
theorem B575687 : Blo 381763 575687 := bstep (se 1 (by rfl) ⟨431765, by rfl⟩ : syracuseStep 575687 = 863531) B863531
theorem B1296701 : Blo 381763 1296701 := bstep (se 3 (by rfl) ⟨243131, by rfl⟩ : syracuseStep 1296701 = 486263) B486263
theorem B575849 : Blo 381763 575849 := bstep (se 2 (by rfl) ⟨215943, by rfl⟩ : syracuseStep 575849 = 431887) B431887
theorem B575927 : Blo 381763 575927 := bstep (se 1 (by rfl) ⟨431945, by rfl⟩ : syracuseStep 575927 = 863891) B863891
theorem B575963 : Blo 381763 575963 := bstep (se 1 (by rfl) ⟨431972, by rfl⟩ : syracuseStep 575963 = 863945) B863945
theorem B2214535 : Blo 381763 2214535 := bstep (se 1 (by rfl) ⟨1660901, by rfl⟩ : syracuseStep 2214535 = 3321803) B3321803
theorem B1952585 : Blo 381763 1952585 := bstep (se 2 (by rfl) ⟨732219, by rfl⟩ : syracuseStep 1952585 = 1464439) B1464439
theorem B2771819 : Blo 381763 2771819 := bstep (se 1 (by rfl) ⟨2078864, by rfl⟩ : syracuseStep 2771819 = 4157729) B4157729
theorem B1231777 : Blo 381763 1231777 := bstep (se 2 (by rfl) ⟨461916, by rfl⟩ : syracuseStep 1231777 = 923833) B923833
theorem B576431 : Blo 381763 576431 := bstep (se 1 (by rfl) ⟨432323, by rfl⟩ : syracuseStep 576431 = 864647) B864647
theorem B576521 : Blo 381763 576521 := bstep (se 2 (by rfl) ⟨216195, by rfl⟩ : syracuseStep 576521 = 432391) B432391
theorem B2968595 : Blo 381763 2968595 := bstep (se 1 (by rfl) ⟨2226446, by rfl⟩ : syracuseStep 2968595 = 4452893) B4452893
theorem B576551 : Blo 381763 576551 := bstep (se 1 (by rfl) ⟨432413, by rfl⟩ : syracuseStep 576551 = 864827) B864827
theorem B576635 : Blo 381763 576635 := bstep (se 1 (by rfl) ⟨432476, by rfl⟩ : syracuseStep 576635 = 864953) B864953
theorem B1297565 : Blo 381763 1297565 := bstep (se 3 (by rfl) ⟨243293, by rfl⟩ : syracuseStep 1297565 = 486587) B486587
theorem B576761 : Blo 381763 576761 := bstep (se 2 (by rfl) ⟨216285, by rfl⟩ : syracuseStep 576761 = 432571) B432571
theorem B576863 : Blo 381763 576863 := bstep (se 1 (by rfl) ⟨432647, by rfl⟩ : syracuseStep 576863 = 865295) B865295
theorem B576875 : Blo 381763 576875 := bstep (se 1 (by rfl) ⟨432656, by rfl⟩ : syracuseStep 576875 = 865313) B865313
theorem B970127 : Blo 381763 970127 := bstep (se 1 (by rfl) ⟨727595, by rfl⟩ : syracuseStep 970127 = 1455191) B1455191
theorem B1232329 : Blo 381763 1232329 := bstep (se 2 (by rfl) ⟨462123, by rfl⟩ : syracuseStep 1232329 = 924247) B924247
theorem B1232443 : Blo 381763 1232443 := bstep (se 1 (by rfl) ⟨924332, by rfl⟩ : syracuseStep 1232443 = 1848665) B1848665
theorem B577103 : Blo 381763 577103 := bstep (se 1 (by rfl) ⟨432827, by rfl⟩ : syracuseStep 577103 = 865655) B865655
theorem B4476539 : Blo 381763 4476539 := bstep (se 1 (by rfl) ⟨3357404, by rfl⟩ : syracuseStep 4476539 = 6714809) B6714809
theorem B1298105 : Blo 381763 1298105 := bstep (se 2 (by rfl) ⟨486789, by rfl⟩ : syracuseStep 1298105 = 973579) B973579
theorem B577223 : Blo 381763 577223 := bstep (se 1 (by rfl) ⟨432917, by rfl⟩ : syracuseStep 577223 = 865835) B865835
theorem B970451 : Blo 381763 970451 := bstep (se 1 (by rfl) ⟨727838, by rfl⟩ : syracuseStep 970451 = 1455677) B1455677
theorem B1462009 : Blo 381763 1462009 := bstep (se 2 (by rfl) ⟨548253, by rfl⟩ : syracuseStep 1462009 = 1096507) B1096507
theorem B577385 : Blo 381763 577385 := bstep (se 2 (by rfl) ⟨216519, by rfl⟩ : syracuseStep 577385 = 433039) B433039
theorem B577463 : Blo 381763 577463 := bstep (se 1 (by rfl) ⟨433097, by rfl⟩ : syracuseStep 577463 = 866195) B866195
theorem B577499 : Blo 381763 577499 := bstep (se 1 (by rfl) ⟨433124, by rfl⟩ : syracuseStep 577499 = 866249) B866249
theorem B1298699 : Blo 381763 1298699 := bstep (se 1 (by rfl) ⟨974024, by rfl⟩ : syracuseStep 1298699 = 1948049) B1948049
theorem B5525819 : Blo 381763 5525819 := bstep (se 1 (by rfl) ⟨4144364, by rfl⟩ : syracuseStep 5525819 = 8288729) B8288729
theorem B577967 : Blo 381763 577967 := bstep (se 1 (by rfl) ⟨433475, by rfl⟩ : syracuseStep 577967 = 866951) B866951
theorem B578057 : Blo 381763 578057 := bstep (se 2 (by rfl) ⟨216771, by rfl⟩ : syracuseStep 578057 = 433543) B433543
theorem B1298969 : Blo 381763 1298969 := bstep (se 2 (by rfl) ⟨487113, by rfl⟩ : syracuseStep 1298969 = 974227) B974227
theorem B578087 : Blo 381763 578087 := bstep (se 1 (by rfl) ⟨433565, by rfl⟩ : syracuseStep 578087 = 867131) B867131
theorem B578171 : Blo 381763 578171 := bstep (se 1 (by rfl) ⟨433628, by rfl⟩ : syracuseStep 578171 = 867257) B867257
theorem B1233623 : Blo 381763 1233623 := bstep (se 1 (by rfl) ⟨925217, by rfl⟩ : syracuseStep 1233623 = 1850435) B1850435
theorem B578297 : Blo 381763 578297 := bstep (se 2 (by rfl) ⟨216861, by rfl⟩ : syracuseStep 578297 = 433723) B433723
theorem B11096837 : Blo 381763 11096837 := bstep (se 4 (by rfl) ⟨1040328, by rfl⟩ : syracuseStep 11096837 = 2080657) B2080657
theorem B381775 : Blo 381763 381775 := bstep (se 1 (by rfl) ⟨286331, by rfl⟩ : syracuseStep 381775 = 572663) B572663
theorem B381791 : Blo 381763 381791 := bstep (se 1 (by rfl) ⟨286343, by rfl⟩ : syracuseStep 381791 = 572687) B572687
theorem B971615 : Blo 381763 971615 := bstep (se 1 (by rfl) ⟨728711, by rfl⟩ : syracuseStep 971615 = 1457423) B1457423
theorem B578399 : Blo 381763 578399 := bstep (se 1 (by rfl) ⟨433799, by rfl⟩ : syracuseStep 578399 = 867599) B867599
theorem B578411 : Blo 381763 578411 := bstep (se 1 (by rfl) ⟨433808, by rfl⟩ : syracuseStep 578411 = 867617) B867617
theorem B381819 : Blo 381763 381819 := bstep (se 1 (by rfl) ⟨286364, by rfl⟩ : syracuseStep 381819 = 572729) B572729
theorem B381871 : Blo 381763 381871 := bstep (se 1 (by rfl) ⟨286403, by rfl⟩ : syracuseStep 381871 = 572807) B572807
theorem B1168303 : Blo 381763 1168303 := bstep (se 1 (by rfl) ⟨876227, by rfl⟩ : syracuseStep 1168303 = 1752455) B1752455
theorem B381895 : Blo 381763 381895 := bstep (se 1 (by rfl) ⟨286421, by rfl⟩ : syracuseStep 381895 = 572843) B572843
theorem B381915 : Blo 381763 381915 := bstep (se 1 (by rfl) ⟨286436, by rfl⟩ : syracuseStep 381915 = 572873) B572873
theorem B381991 : Blo 381763 381991 := bstep (se 1 (by rfl) ⟨286493, by rfl⟩ : syracuseStep 381991 = 572987) B572987
theorem B382031 : Blo 381763 382031 := bstep (se 1 (by rfl) ⟨286523, by rfl⟩ : syracuseStep 382031 = 573047) B573047
theorem B578639 : Blo 381763 578639 := bstep (se 1 (by rfl) ⟨433979, by rfl⟩ : syracuseStep 578639 = 867959) B867959
theorem B382047 : Blo 381763 382047 := bstep (se 1 (by rfl) ⟨286535, by rfl⟩ : syracuseStep 382047 = 573071) B573071
theorem B382075 : Blo 381763 382075 := bstep (se 1 (by rfl) ⟨286556, by rfl⟩ : syracuseStep 382075 = 573113) B573113
theorem B1463453 : Blo 381763 1463453 := bstep (se 3 (by rfl) ⟨274397, by rfl⟩ : syracuseStep 1463453 = 548795) B548795
theorem B644267 : Blo 381763 644267 := bstep (se 1 (by rfl) ⟨483200, by rfl⟩ : syracuseStep 644267 = 966401) B966401
theorem B1463467 : Blo 381763 1463467 := bstep (se 1 (by rfl) ⟨1097600, by rfl⟩ : syracuseStep 1463467 = 2195201) B2195201
theorem B382127 : Blo 381763 382127 := bstep (se 1 (by rfl) ⟨286595, by rfl⟩ : syracuseStep 382127 = 573191) B573191
theorem B382151 : Blo 381763 382151 := bstep (se 1 (by rfl) ⟨286613, by rfl⟩ : syracuseStep 382151 = 573227) B573227
theorem B382171 : Blo 381763 382171 := bstep (se 1 (by rfl) ⟨286628, by rfl⟩ : syracuseStep 382171 = 573257) B573257
theorem B4936949 : Blo 381763 4936949 := bstep (se 5 (by rfl) ⟨231419, by rfl⟩ : syracuseStep 4936949 = 462839) B462839
theorem B1234187 : Blo 381763 1234187 := bstep (se 1 (by rfl) ⟨925640, by rfl⟩ : syracuseStep 1234187 = 1851281) B1851281
theorem B382247 : Blo 381763 382247 := bstep (se 1 (by rfl) ⟨286685, by rfl⟩ : syracuseStep 382247 = 573371) B573371
theorem B382287 : Blo 381763 382287 := bstep (se 1 (by rfl) ⟨286715, by rfl⟩ : syracuseStep 382287 = 573431) B573431
theorem B382303 : Blo 381763 382303 := bstep (se 1 (by rfl) ⟨286727, by rfl⟩ : syracuseStep 382303 = 573455) B573455
theorem B382331 : Blo 381763 382331 := bstep (se 1 (by rfl) ⟨286748, by rfl⟩ : syracuseStep 382331 = 573497) B573497
theorem B382383 : Blo 381763 382383 := bstep (se 1 (by rfl) ⟨286787, by rfl⟩ : syracuseStep 382383 = 573575) B573575
theorem B382407 : Blo 381763 382407 := bstep (se 1 (by rfl) ⟨286805, by rfl⟩ : syracuseStep 382407 = 573611) B573611
theorem B382427 : Blo 381763 382427 := bstep (se 1 (by rfl) ⟨286820, by rfl⟩ : syracuseStep 382427 = 573641) B573641
theorem B1463771 : Blo 381763 1463771 := bstep (se 1 (by rfl) ⟨1097828, by rfl⟩ : syracuseStep 1463771 = 2195657) B2195657
theorem B382503 : Blo 381763 382503 := bstep (se 1 (by rfl) ⟨286877, by rfl⟩ : syracuseStep 382503 = 573755) B573755
theorem B644665 : Blo 381763 644665 := bstep (se 2 (by rfl) ⟨241749, by rfl⟩ : syracuseStep 644665 = 483499) B483499
theorem B382543 : Blo 381763 382543 := bstep (se 1 (by rfl) ⟨286907, by rfl⟩ : syracuseStep 382543 = 573815) B573815
theorem B382559 : Blo 381763 382559 := bstep (se 1 (by rfl) ⟨286919, by rfl⟩ : syracuseStep 382559 = 573839) B573839
theorem B382587 : Blo 381763 382587 := bstep (se 1 (by rfl) ⟨286940, by rfl⟩ : syracuseStep 382587 = 573881) B573881
theorem B415355 : Blo 381763 415355 := bstep (se 1 (by rfl) ⟨311516, by rfl⟩ : syracuseStep 415355 = 623033) B623033
theorem B1300103 : Blo 381763 1300103 := bstep (se 1 (by rfl) ⟨975077, by rfl⟩ : syracuseStep 1300103 = 1950155) B1950155
theorem B382639 : Blo 381763 382639 := bstep (se 1 (by rfl) ⟨286979, by rfl⟩ : syracuseStep 382639 = 573959) B573959
theorem B1300157 : Blo 381763 1300157 := bstep (se 3 (by rfl) ⟨243779, by rfl⟩ : syracuseStep 1300157 = 487559) B487559
theorem B644807 : Blo 381763 644807 := bstep (se 1 (by rfl) ⟨483605, by rfl⟩ : syracuseStep 644807 = 967211) B967211
theorem B382663 : Blo 381763 382663 := bstep (se 1 (by rfl) ⟨286997, by rfl⟩ : syracuseStep 382663 = 573995) B573995
theorem B382683 : Blo 381763 382683 := bstep (se 1 (by rfl) ⟨287012, by rfl⟩ : syracuseStep 382683 = 574025) B574025
theorem B382759 : Blo 381763 382759 := bstep (se 1 (by rfl) ⟨287069, by rfl⟩ : syracuseStep 382759 = 574139) B574139
theorem B2774843 : Blo 381763 2774843 := bstep (se 1 (by rfl) ⟨2081132, by rfl⟩ : syracuseStep 2774843 = 4162265) B4162265
theorem B382799 : Blo 381763 382799 := bstep (se 1 (by rfl) ⟨287099, by rfl⟩ : syracuseStep 382799 = 574199) B574199
theorem B382815 : Blo 381763 382815 := bstep (se 1 (by rfl) ⟨287111, by rfl⟩ : syracuseStep 382815 = 574223) B574223
theorem B1300319 : Blo 381763 1300319 := bstep (se 1 (by rfl) ⟨975239, by rfl⟩ : syracuseStep 1300319 = 1950479) B1950479
theorem B644969 : Blo 381763 644969 := bstep (se 2 (by rfl) ⟨241863, by rfl⟩ : syracuseStep 644969 = 483727) B483727
theorem B382843 : Blo 381763 382843 := bstep (se 1 (by rfl) ⟨287132, by rfl⟩ : syracuseStep 382843 = 574265) B574265
theorem B382895 : Blo 381763 382895 := bstep (se 1 (by rfl) ⟨287171, by rfl⟩ : syracuseStep 382895 = 574343) B574343
theorem B972719 : Blo 381763 972719 := bstep (se 1 (by rfl) ⟨729539, by rfl⟩ : syracuseStep 972719 = 1459079) B1459079
theorem B382919 : Blo 381763 382919 := bstep (se 1 (by rfl) ⟨287189, by rfl⟩ : syracuseStep 382919 = 574379) B574379
theorem B382939 : Blo 381763 382939 := bstep (se 1 (by rfl) ⟨287204, by rfl⟩ : syracuseStep 382939 = 574409) B574409
theorem B1300481 : Blo 381763 1300481 := bstep (se 2 (by rfl) ⟨487680, by rfl⟩ : syracuseStep 1300481 = 975361) B975361
theorem B383015 : Blo 381763 383015 := bstep (se 1 (by rfl) ⟨287261, by rfl⟩ : syracuseStep 383015 = 574523) B574523
theorem B383055 : Blo 381763 383055 := bstep (se 1 (by rfl) ⟨287291, by rfl⟩ : syracuseStep 383055 = 574583) B574583
theorem B383071 : Blo 381763 383071 := bstep (se 1 (by rfl) ⟨287303, by rfl⟩ : syracuseStep 383071 = 574607) B574607
theorem B383099 : Blo 381763 383099 := bstep (se 1 (by rfl) ⟨287324, by rfl⟩ : syracuseStep 383099 = 574649) B574649
theorem B383151 : Blo 381763 383151 := bstep (se 1 (by rfl) ⟨287363, by rfl⟩ : syracuseStep 383151 = 574727) B574727
theorem B383175 : Blo 381763 383175 := bstep (se 1 (by rfl) ⟨287381, by rfl⟩ : syracuseStep 383175 = 574763) B574763
theorem B383195 : Blo 381763 383195 := bstep (se 1 (by rfl) ⟨287396, by rfl⟩ : syracuseStep 383195 = 574793) B574793
theorem B645367 : Blo 381763 645367 := bstep (se 1 (by rfl) ⟨484025, by rfl⟩ : syracuseStep 645367 = 968051) B968051
theorem B383271 : Blo 381763 383271 := bstep (se 1 (by rfl) ⟨287453, by rfl⟩ : syracuseStep 383271 = 574907) B574907
theorem B383311 : Blo 381763 383311 := bstep (se 1 (by rfl) ⟨287483, by rfl⟩ : syracuseStep 383311 = 574967) B574967
theorem B383327 : Blo 381763 383327 := bstep (se 1 (by rfl) ⟨287495, by rfl⟩ : syracuseStep 383327 = 574991) B574991
theorem B383355 : Blo 381763 383355 := bstep (se 1 (by rfl) ⟨287516, by rfl⟩ : syracuseStep 383355 = 575033) B575033
theorem B383407 : Blo 381763 383407 := bstep (se 1 (by rfl) ⟨287555, by rfl⟩ : syracuseStep 383407 = 575111) B575111
theorem B645563 : Blo 381763 645563 := bstep (se 1 (by rfl) ⟨484172, by rfl⟩ : syracuseStep 645563 = 968345) B968345
theorem B383431 : Blo 381763 383431 := bstep (se 1 (by rfl) ⟨287573, by rfl⟩ : syracuseStep 383431 = 575147) B575147
theorem B383451 : Blo 381763 383451 := bstep (se 1 (by rfl) ⟨287588, by rfl⟩ : syracuseStep 383451 = 575177) B575177
theorem B547337 : Blo 381763 547337 := bstep (se 2 (by rfl) ⟨205251, by rfl⟩ : syracuseStep 547337 = 410503) B410503
theorem B645671 : Blo 381763 645671 := bstep (se 1 (by rfl) ⟨484253, by rfl⟩ : syracuseStep 645671 = 968507) B968507
theorem B383527 : Blo 381763 383527 := bstep (se 1 (by rfl) ⟨287645, by rfl⟩ : syracuseStep 383527 = 575291) B575291
theorem B383567 : Blo 381763 383567 := bstep (se 1 (by rfl) ⟨287675, by rfl⟩ : syracuseStep 383567 = 575351) B575351
theorem B383583 : Blo 381763 383583 := bstep (se 1 (by rfl) ⟨287687, by rfl⟩ : syracuseStep 383583 = 575375) B575375
theorem B383611 : Blo 381763 383611 := bstep (se 1 (by rfl) ⟨287708, by rfl⟩ : syracuseStep 383611 = 575417) B575417
theorem B383663 : Blo 381763 383663 := bstep (se 1 (by rfl) ⟨287747, by rfl⟩ : syracuseStep 383663 = 575495) B575495
theorem B383687 : Blo 381763 383687 := bstep (se 1 (by rfl) ⟨287765, by rfl⟩ : syracuseStep 383687 = 575531) B575531
theorem B2448073 : Blo 381763 2448073 := bstep (se 2 (by rfl) ⟨918027, by rfl⟩ : syracuseStep 2448073 = 1836055) B1836055
theorem B383707 : Blo 381763 383707 := bstep (se 1 (by rfl) ⟨287780, by rfl⟩ : syracuseStep 383707 = 575561) B575561
theorem B3496733 : Blo 381763 3496733 := bstep (se 3 (by rfl) ⟨655637, by rfl⟩ : syracuseStep 3496733 = 1311275) B1311275
theorem B383783 : Blo 381763 383783 := bstep (se 1 (by rfl) ⟨287837, by rfl⟩ : syracuseStep 383783 = 575675) B575675
theorem B1301291 : Blo 381763 1301291 := bstep (se 1 (by rfl) ⟨975968, by rfl⟩ : syracuseStep 1301291 = 1951937) B1951937
theorem B645961 : Blo 381763 645961 := bstep (se 2 (by rfl) ⟨242235, by rfl⟩ : syracuseStep 645961 = 484471) B484471
theorem B383823 : Blo 381763 383823 := bstep (se 1 (by rfl) ⟨287867, by rfl⟩ : syracuseStep 383823 = 575735) B575735
theorem B383839 : Blo 381763 383839 := bstep (se 1 (by rfl) ⟨287879, by rfl⟩ : syracuseStep 383839 = 575759) B575759
theorem B645995 : Blo 381763 645995 := bstep (se 1 (by rfl) ⟨484496, by rfl⟩ : syracuseStep 645995 = 968993) B968993
theorem B383867 : Blo 381763 383867 := bstep (se 1 (by rfl) ⟨287900, by rfl⟩ : syracuseStep 383867 = 575801) B575801
theorem B383919 : Blo 381763 383919 := bstep (se 1 (by rfl) ⟨287939, by rfl⟩ : syracuseStep 383919 = 575879) B575879
theorem B383943 : Blo 381763 383943 := bstep (se 1 (by rfl) ⟨287957, by rfl⟩ : syracuseStep 383943 = 575915) B575915
theorem B383963 : Blo 381763 383963 := bstep (se 1 (by rfl) ⟨287972, by rfl⟩ : syracuseStep 383963 = 575945) B575945
theorem B3103763 : Blo 381763 3103763 := bstep (se 1 (by rfl) ⟨2327822, by rfl⟩ : syracuseStep 3103763 = 4655645) B4655645
theorem B384039 : Blo 381763 384039 := bstep (se 1 (by rfl) ⟨288029, by rfl⟩ : syracuseStep 384039 = 576059) B576059
theorem B1301561 : Blo 381763 1301561 := bstep (se 2 (by rfl) ⟨488085, by rfl⟩ : syracuseStep 1301561 = 976171) B976171
theorem B384079 : Blo 381763 384079 := bstep (se 1 (by rfl) ⟨288059, by rfl⟩ : syracuseStep 384079 = 576119) B576119
theorem B973903 : Blo 381763 973903 := bstep (se 1 (by rfl) ⟨730427, by rfl⟩ : syracuseStep 973903 = 1460855) B1460855
theorem B384095 : Blo 381763 384095 := bstep (se 1 (by rfl) ⟨288071, by rfl⟩ : syracuseStep 384095 = 576143) B576143
theorem B613499 : Blo 381763 613499 := bstep (se 1 (by rfl) ⟨460124, by rfl⟩ : syracuseStep 613499 = 920249) B920249
theorem B384123 : Blo 381763 384123 := bstep (se 1 (by rfl) ⟨288092, by rfl⟩ : syracuseStep 384123 = 576185) B576185
theorem B384175 : Blo 381763 384175 := bstep (se 1 (by rfl) ⟨288131, by rfl⟩ : syracuseStep 384175 = 576263) B576263
theorem B384199 : Blo 381763 384199 := bstep (se 1 (by rfl) ⟨288149, by rfl⟩ : syracuseStep 384199 = 576299) B576299
theorem B384219 : Blo 381763 384219 := bstep (se 1 (by rfl) ⟨288164, by rfl⟩ : syracuseStep 384219 = 576329) B576329
theorem B646393 : Blo 381763 646393 := bstep (se 2 (by rfl) ⟨242397, by rfl⟩ : syracuseStep 646393 = 484795) B484795
theorem B384295 : Blo 381763 384295 := bstep (se 1 (by rfl) ⟨288221, by rfl⟩ : syracuseStep 384295 = 576443) B576443
theorem B384335 : Blo 381763 384335 := bstep (se 1 (by rfl) ⟨288251, by rfl⟩ : syracuseStep 384335 = 576503) B576503
theorem B4742489 : Blo 381763 4742489 := bstep (se 2 (by rfl) ⟨1778433, by rfl⟩ : syracuseStep 4742489 = 3556867) B3556867
theorem B384351 : Blo 381763 384351 := bstep (se 1 (by rfl) ⟨288263, by rfl⟩ : syracuseStep 384351 = 576527) B576527
theorem B548203 : Blo 381763 548203 := bstep (se 1 (by rfl) ⟨411152, by rfl⟩ : syracuseStep 548203 = 822305) B822305
theorem B384379 : Blo 381763 384379 := bstep (se 1 (by rfl) ⟨288284, by rfl⟩ : syracuseStep 384379 = 576569) B576569
theorem B1301885 : Blo 381763 1301885 := bstep (se 3 (by rfl) ⟨244103, by rfl⟩ : syracuseStep 1301885 = 488207) B488207
theorem B384431 : Blo 381763 384431 := bstep (se 1 (by rfl) ⟨288323, by rfl⟩ : syracuseStep 384431 = 576647) B576647
theorem B384455 : Blo 381763 384455 := bstep (se 1 (by rfl) ⟨288341, by rfl⟩ : syracuseStep 384455 = 576683) B576683
theorem B384475 : Blo 381763 384475 := bstep (se 1 (by rfl) ⟨288356, by rfl⟩ : syracuseStep 384475 = 576713) B576713
theorem B646663 : Blo 381763 646663 := bstep (se 1 (by rfl) ⟨484997, by rfl⟩ : syracuseStep 646663 = 969995) B969995
theorem B384551 : Blo 381763 384551 := bstep (se 1 (by rfl) ⟨288413, by rfl⟩ : syracuseStep 384551 = 576827) B576827
theorem B384591 : Blo 381763 384591 := bstep (se 1 (by rfl) ⟨288443, by rfl⟩ : syracuseStep 384591 = 576887) B576887
theorem B384607 : Blo 381763 384607 := bstep (se 1 (by rfl) ⟨288455, by rfl⟩ : syracuseStep 384607 = 576911) B576911
theorem B384635 : Blo 381763 384635 := bstep (se 1 (by rfl) ⟨288476, by rfl⟩ : syracuseStep 384635 = 576953) B576953
theorem B384687 : Blo 381763 384687 := bstep (se 1 (by rfl) ⟨288515, by rfl⟩ : syracuseStep 384687 = 577031) B577031
theorem B384711 : Blo 381763 384711 := bstep (se 1 (by rfl) ⟨288533, by rfl⟩ : syracuseStep 384711 = 577067) B577067
theorem B974551 : Blo 381763 974551 := bstep (se 1 (by rfl) ⟨730913, by rfl⟩ : syracuseStep 974551 = 1461827) B1461827
theorem B384731 : Blo 381763 384731 := bstep (se 1 (by rfl) ⟨288548, by rfl⟩ : syracuseStep 384731 = 577097) B577097
theorem B384807 : Blo 381763 384807 := bstep (se 1 (by rfl) ⟨288605, by rfl⟩ : syracuseStep 384807 = 577211) B577211
theorem B384847 : Blo 381763 384847 := bstep (se 1 (by rfl) ⟨288635, by rfl⟩ : syracuseStep 384847 = 577271) B577271
theorem B384863 : Blo 381763 384863 := bstep (se 1 (by rfl) ⟨288647, by rfl⟩ : syracuseStep 384863 = 577295) B577295
theorem B3268471 : Blo 381763 3268471 := bstep (se 1 (by rfl) ⟨2451353, by rfl⟩ : syracuseStep 3268471 = 4902707) B4902707
theorem B384891 : Blo 381763 384891 := bstep (se 1 (by rfl) ⟨288668, by rfl⟩ : syracuseStep 384891 = 577337) B577337
theorem B384943 : Blo 381763 384943 := bstep (se 1 (by rfl) ⟨288707, by rfl⟩ : syracuseStep 384943 = 577415) B577415
theorem B647095 : Blo 381763 647095 := bstep (se 1 (by rfl) ⟨485321, by rfl⟩ : syracuseStep 647095 = 970643) B970643
theorem B384967 : Blo 381763 384967 := bstep (se 1 (by rfl) ⟨288725, by rfl⟩ : syracuseStep 384967 = 577451) B577451
theorem B384987 : Blo 381763 384987 := bstep (se 1 (by rfl) ⟨288740, by rfl⟩ : syracuseStep 384987 = 577481) B577481
theorem B974855 : Blo 381763 974855 := bstep (se 1 (by rfl) ⟨731141, by rfl⟩ : syracuseStep 974855 = 1462283) B1462283
theorem B2777125 : Blo 381763 2777125 := bstep (se 4 (by rfl) ⟨260355, by rfl⟩ : syracuseStep 2777125 = 520711) B520711
theorem B385063 : Blo 381763 385063 := bstep (se 1 (by rfl) ⟨288797, by rfl⟩ : syracuseStep 385063 = 577595) B577595
theorem B548903 : Blo 381763 548903 := bstep (se 1 (by rfl) ⟨411677, by rfl⟩ : syracuseStep 548903 = 823355) B823355
theorem B385103 : Blo 381763 385103 := bstep (se 1 (by rfl) ⟨288827, by rfl⟩ : syracuseStep 385103 = 577655) B577655
theorem B385119 : Blo 381763 385119 := bstep (se 1 (by rfl) ⟨288839, by rfl⟩ : syracuseStep 385119 = 577679) B577679
theorem B647291 : Blo 381763 647291 := bstep (se 1 (by rfl) ⟨485468, by rfl⟩ : syracuseStep 647291 = 970937) B970937
theorem B385147 : Blo 381763 385147 := bstep (se 1 (by rfl) ⟨288860, by rfl⟩ : syracuseStep 385147 = 577721) B577721
theorem B385199 : Blo 381763 385199 := bstep (se 1 (by rfl) ⟨288899, by rfl⟩ : syracuseStep 385199 = 577799) B577799
theorem B385223 : Blo 381763 385223 := bstep (se 1 (by rfl) ⟨288917, by rfl⟩ : syracuseStep 385223 = 577835) B577835
theorem B385243 : Blo 381763 385243 := bstep (se 1 (by rfl) ⟨288932, by rfl⟩ : syracuseStep 385243 = 577865) B577865
theorem B385319 : Blo 381763 385319 := bstep (se 1 (by rfl) ⟨288989, by rfl⟩ : syracuseStep 385319 = 577979) B577979
theorem B4645181 : Blo 381763 4645181 := bstep (se 3 (by rfl) ⟨870971, by rfl⟩ : syracuseStep 4645181 = 1741943) B1741943
theorem B385359 : Blo 381763 385359 := bstep (se 1 (by rfl) ⟨289019, by rfl⟩ : syracuseStep 385359 = 578039) B578039
theorem B385375 : Blo 381763 385375 := bstep (se 1 (by rfl) ⟨289031, by rfl⟩ : syracuseStep 385375 = 578063) B578063
theorem B385403 : Blo 381763 385403 := bstep (se 1 (by rfl) ⟨289052, by rfl⟩ : syracuseStep 385403 = 578105) B578105
theorem B385455 : Blo 381763 385455 := bstep (se 1 (by rfl) ⟨289091, by rfl⟩ : syracuseStep 385455 = 578183) B578183
theorem B582071 : Blo 381763 582071 := bstep (se 1 (by rfl) ⟨436553, by rfl⟩ : syracuseStep 582071 = 873107) B873107
theorem B385479 : Blo 381763 385479 := bstep (se 1 (by rfl) ⟨289109, by rfl⟩ : syracuseStep 385479 = 578219) B578219
theorem B385499 : Blo 381763 385499 := bstep (se 1 (by rfl) ⟨289124, by rfl⟩ : syracuseStep 385499 = 578249) B578249
theorem B647689 : Blo 381763 647689 := bstep (se 2 (by rfl) ⟨242883, by rfl⟩ : syracuseStep 647689 = 485767) B485767
theorem B385575 : Blo 381763 385575 := bstep (se 1 (by rfl) ⟨289181, by rfl⟩ : syracuseStep 385575 = 578363) B578363
theorem B385615 : Blo 381763 385615 := bstep (se 1 (by rfl) ⟨289211, by rfl⟩ : syracuseStep 385615 = 578423) B578423
theorem B385631 : Blo 381763 385631 := bstep (se 1 (by rfl) ⟨289223, by rfl⟩ : syracuseStep 385631 = 578447) B578447
theorem B385659 : Blo 381763 385659 := bstep (se 1 (by rfl) ⟨289244, by rfl⟩ : syracuseStep 385659 = 578489) B578489
theorem B2187911 : Blo 381763 2187911 := bstep (se 1 (by rfl) ⟨1640933, by rfl⟩ : syracuseStep 2187911 = 3281867) B3281867
theorem B647851 : Blo 381763 647851 := bstep (se 1 (by rfl) ⟨485888, by rfl⟩ : syracuseStep 647851 = 971777) B971777
theorem B385711 : Blo 381763 385711 := bstep (se 1 (by rfl) ⟨289283, by rfl⟩ : syracuseStep 385711 = 578567) B578567
theorem B385735 : Blo 381763 385735 := bstep (se 1 (by rfl) ⟨289301, by rfl⟩ : syracuseStep 385735 = 578603) B578603
theorem B385755 : Blo 381763 385755 := bstep (se 1 (by rfl) ⟨289316, by rfl⟩ : syracuseStep 385755 = 578633) B578633
theorem B648155 : Blo 381763 648155 := bstep (se 1 (by rfl) ⟨486116, by rfl⟩ : syracuseStep 648155 = 972233) B972233
theorem B2188367 : Blo 381763 2188367 := bstep (se 1 (by rfl) ⟨1641275, by rfl⟩ : syracuseStep 2188367 = 3282551) B3282551
theorem B648391 : Blo 381763 648391 := bstep (se 1 (by rfl) ⟨486293, by rfl⟩ : syracuseStep 648391 = 972587) B972587
theorem B713927 : Blo 381763 713927 := bstep (se 1 (by rfl) ⟨535445, by rfl⟩ : syracuseStep 713927 = 1070891) B1070891
theorem B779615 : Blo 381763 779615 := bstep (se 1 (by rfl) ⟨584711, by rfl⟩ : syracuseStep 779615 = 1169423) B1169423
theorem B648553 : Blo 381763 648553 := bstep (se 2 (by rfl) ⟨243207, by rfl⟩ : syracuseStep 648553 = 486415) B486415
theorem B2778533 : Blo 381763 2778533 := bstep (se 4 (by rfl) ⟨260487, by rfl⟩ : syracuseStep 2778533 = 520975) B520975
theorem B615863 : Blo 381763 615863 := bstep (se 1 (by rfl) ⟨461897, by rfl⟩ : syracuseStep 615863 = 923795) B923795
theorem B649147 : Blo 381763 649147 := bstep (se 1 (by rfl) ⟨486860, by rfl⟩ : syracuseStep 649147 = 973721) B973721
theorem B4679633 : Blo 381763 4679633 := bstep (se 2 (by rfl) ⟨1754862, by rfl⟩ : syracuseStep 4679633 = 3509725) B3509725
theorem B649255 : Blo 381763 649255 := bstep (se 1 (by rfl) ⟨486941, by rfl⟩ : syracuseStep 649255 = 973883) B973883
theorem B2189369 : Blo 381763 2189369 := bstep (se 2 (by rfl) ⟨821013, by rfl⟩ : syracuseStep 2189369 = 1642027) B1642027
theorem B649579 : Blo 381763 649579 := bstep (se 1 (by rfl) ⟨487184, by rfl⟩ : syracuseStep 649579 = 974369) B974369
theorem B617311 : Blo 381763 617311 := bstep (se 1 (by rfl) ⟨462983, by rfl⟩ : syracuseStep 617311 = 925967) B925967
theorem B5532563 : Blo 381763 5532563 := bstep (se 1 (by rfl) ⟨4149422, by rfl⟩ : syracuseStep 5532563 = 8298845) B8298845
theorem B486319 : Blo 381763 486319 := bstep (se 1 (by rfl) ⟨364739, by rfl⟩ : syracuseStep 486319 = 729479) B729479
theorem B388295 : Blo 381763 388295 := bstep (se 1 (by rfl) ⟨291221, by rfl⟩ : syracuseStep 388295 = 582443) B582443
theorem B650639 : Blo 381763 650639 := bstep (se 1 (by rfl) ⟨487979, by rfl⟩ : syracuseStep 650639 = 975959) B975959
theorem B7892603 : Blo 381763 7892603 := bstep (se 1 (by rfl) ⟨5919452, by rfl⟩ : syracuseStep 7892603 = 11838905) B11838905
theorem B650875 : Blo 381763 650875 := bstep (se 1 (by rfl) ⟨488156, by rfl⟩ : syracuseStep 650875 = 976313) B976313
theorem B520111 : Blo 381763 520111 := bstep (se 1 (by rfl) ⟨390083, by rfl⟩ : syracuseStep 520111 = 780167) B780167
theorem B487387 : Blo 381763 487387 := bstep (se 1 (by rfl) ⟨365540, by rfl⟩ : syracuseStep 487387 = 731081) B731081
theorem B4649075 : Blo 381763 4649075 := bstep (se 1 (by rfl) ⟨3486806, by rfl⟩ : syracuseStep 4649075 = 6973613) B6973613
theorem B520543 : Blo 381763 520543 := bstep (se 1 (by rfl) ⟨390407, by rfl⟩ : syracuseStep 520543 = 780815) B780815
theorem B1635329 : Blo 381763 1635329 := bstep (se 2 (by rfl) ⟨613248, by rfl⟩ : syracuseStep 1635329 = 1226497) B1226497
theorem B1307801 : Blo 381763 1307801 := bstep (se 2 (by rfl) ⟨490425, by rfl⟩ : syracuseStep 1307801 = 980851) B980851
theorem B2192993 : Blo 381763 2192993 := bstep (se 2 (by rfl) ⟨822372, by rfl⟩ : syracuseStep 2192993 = 1644745) B1644745
theorem B390991 : Blo 381763 390991 := bstep (se 1 (by rfl) ⟨293243, by rfl⟩ : syracuseStep 390991 = 586487) B586487
theorem B620551 : Blo 381763 620551 := bstep (se 1 (by rfl) ⟨465413, by rfl⟩ : syracuseStep 620551 = 930827) B930827
theorem B6092857 : Blo 381763 6092857 := bstep (se 2 (by rfl) ⟨2284821, by rfl⟩ : syracuseStep 6092857 = 4569643) B4569643
theorem B169834765 : Blo 381763 169834765 := bstep (se 3 (by rfl) ⟨31844018, by rfl⟩ : syracuseStep 169834765 = 63688037) B63688037
theorem B4356503 : Blo 381763 4356503 := bstep (se 1 (by rfl) ⟨3267377, by rfl⟩ : syracuseStep 4356503 = 6534755) B6534755
theorem B2915027 : Blo 381763 2915027 := bstep (se 1 (by rfl) ⟨2186270, by rfl⟩ : syracuseStep 2915027 = 4372541) B4372541
theorem B3111709 : Blo 381763 3111709 := bstep (se 3 (by rfl) ⟨583445, by rfl⟩ : syracuseStep 3111709 = 1166891) B1166891
theorem B4684691 : Blo 381763 4684691 := bstep (se 1 (by rfl) ⟨3513518, by rfl⟩ : syracuseStep 4684691 = 7027037) B7027037
theorem B2194451 : Blo 381763 2194451 := bstep (se 1 (by rfl) ⟨1645838, by rfl⟩ : syracuseStep 2194451 = 3291677) B3291677
theorem B1015031 : Blo 381763 1015031 := bstep (se 1 (by rfl) ⟨761273, by rfl⟩ : syracuseStep 1015031 = 1522547) B1522547
theorem B3669421 : Blo 381763 3669421 := bstep (se 3 (by rfl) ⟨688016, by rfl⟩ : syracuseStep 3669421 = 1376033) B1376033
theorem B1637927 : Blo 381763 1637927 := bstep (se 1 (by rfl) ⟨1228445, by rfl⟩ : syracuseStep 1637927 = 2456891) B2456891
theorem B1310347 : Blo 381763 1310347 := bstep (se 1 (by rfl) ⟨982760, by rfl⟩ : syracuseStep 1310347 = 1965521) B1965521
theorem B1310537 : Blo 381763 1310537 := bstep (se 2 (by rfl) ⟨491451, by rfl⟩ : syracuseStep 1310537 = 982903) B982903
theorem B1376119 : Blo 381763 1376119 := bstep (se 1 (by rfl) ⟨1032089, by rfl⟩ : syracuseStep 1376119 = 2064179) B2064179
theorem B3309605 : Blo 381763 3309605 := bstep (se 4 (by rfl) ⟨310275, by rfl⟩ : syracuseStep 3309605 = 620551) B620551
theorem B3702833 : Blo 381763 3702833 := bstep (se 2 (by rfl) ⟨1388562, by rfl⟩ : syracuseStep 3702833 = 2777125) B2777125
theorem B15728717 : Blo 381763 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B3277219 : Blo 381763 3277219 := bstep (se 1 (by rfl) ⟨2457914, by rfl⟩ : syracuseStep 3277219 = 4915829) B4915829
theorem B1933793 : Blo 381763 1933793 := bstep (se 2 (by rfl) ⟨725172, by rfl⟩ : syracuseStep 1933793 = 1450345) B1450345
theorem B4391495 : Blo 381763 4391495 := bstep (se 1 (by rfl) ⟨3293621, by rfl⟩ : syracuseStep 4391495 = 6587243) B6587243
theorem B1835885 : Blo 381763 1835885 := bstep (se 3 (by rfl) ⟨344228, by rfl⟩ : syracuseStep 1835885 = 688457) B688457
theorem B1443065 : Blo 381763 1443065 := bstep (se 2 (by rfl) ⟨541149, by rfl⟩ : syracuseStep 1443065 = 1082299) B1082299
theorem B919201 : Blo 381763 919201 := bstep (se 2 (by rfl) ⟨344700, by rfl⟩ : syracuseStep 919201 = 689401) B689401
theorem B460523 : Blo 381763 460523 := bstep (se 1 (by rfl) ⟨345392, by rfl⟩ : syracuseStep 460523 = 690785) B690785
theorem B1378255 : Blo 381763 1378255 := bstep (se 1 (by rfl) ⟨1033691, by rfl⟩ : syracuseStep 1378255 = 2067383) B2067383
theorem B1640695 : Blo 381763 1640695 := bstep (se 1 (by rfl) ⟨1230521, by rfl⟩ : syracuseStep 1640695 = 2461043) B2461043
theorem B1640729 : Blo 381763 1640729 := bstep (se 2 (by rfl) ⟨615273, by rfl⟩ : syracuseStep 1640729 = 1230547) B1230547
theorem B2984359 : Blo 381763 2984359 := bstep (se 1 (by rfl) ⟨2238269, by rfl⟩ : syracuseStep 2984359 = 4476539) B4476539
theorem B4360877 : Blo 381763 4360877 := bstep (se 3 (by rfl) ⟨817664, by rfl⟩ : syracuseStep 4360877 = 1635329) B1635329
theorem B1936061 : Blo 381763 1936061 := bstep (se 3 (by rfl) ⟨363011, by rfl⟩ : syracuseStep 1936061 = 726023) B726023
theorem B2951927 : Blo 381763 2951927 := bstep (se 1 (by rfl) ⟨2213945, by rfl⟩ : syracuseStep 2951927 = 4427891) B4427891
theorem B3279953 : Blo 381763 3279953 := bstep (se 2 (by rfl) ⟨1229982, by rfl⟩ : syracuseStep 3279953 = 2459965) B2459965
theorem B822415 : Blo 381763 822415 := bstep (se 1 (by rfl) ⟨616811, by rfl⟩ : syracuseStep 822415 = 1233623) B1233623
theorem B14683517 : Blo 381763 14683517 := bstep (se 3 (by rfl) ⟨2753159, by rfl⟩ : syracuseStep 14683517 = 5506319) B5506319
theorem B429511 : Blo 381763 429511 := bstep (se 1 (by rfl) ⟨322133, by rfl⟩ : syracuseStep 429511 = 644267) B644267
theorem B822791 : Blo 381763 822791 := bstep (se 1 (by rfl) ⟨617093, by rfl⟩ : syracuseStep 822791 = 1234187) B1234187
theorem B2952713 : Blo 381763 2952713 := bstep (se 2 (by rfl) ⟨1107267, by rfl⟩ : syracuseStep 2952713 = 2214535) B2214535
theorem B429871 : Blo 381763 429871 := bstep (se 1 (by rfl) ⟨322403, by rfl⟩ : syracuseStep 429871 = 644807) B644807
theorem B1642301 : Blo 381763 1642301 := bstep (se 3 (by rfl) ⟨307931, by rfl⟩ : syracuseStep 1642301 = 615863) B615863
theorem B1642369 : Blo 381763 1642369 := bstep (se 2 (by rfl) ⟨615888, by rfl⟩ : syracuseStep 1642369 = 1231777) B1231777
theorem B429979 : Blo 381763 429979 := bstep (se 1 (by rfl) ⟨322484, by rfl⟩ : syracuseStep 429979 = 644969) B644969
theorem B3706829 : Blo 381763 3706829 := bstep (se 3 (by rfl) ⟨695030, by rfl⟩ : syracuseStep 3706829 = 1390061) B1390061
theorem B430375 : Blo 381763 430375 := bstep (se 1 (by rfl) ⟨322781, by rfl⟩ : syracuseStep 430375 = 645563) B645563
theorem B2363755 : Blo 381763 2363755 := bstep (se 1 (by rfl) ⟨1772816, by rfl⟩ : syracuseStep 2363755 = 3545633) B3545633
theorem B430447 : Blo 381763 430447 := bstep (se 1 (by rfl) ⟨322835, by rfl⟩ : syracuseStep 430447 = 645671) B645671
theorem B2331155 : Blo 381763 2331155 := bstep (se 1 (by rfl) ⟨1748366, by rfl⟩ : syracuseStep 2331155 = 3496733) B3496733
theorem B430663 : Blo 381763 430663 := bstep (se 1 (by rfl) ⟨322997, by rfl⟩ : syracuseStep 430663 = 645995) B645995
theorem B1643105 : Blo 381763 1643105 := bstep (se 2 (by rfl) ⟨616164, by rfl⟩ : syracuseStep 1643105 = 1232329) B1232329
theorem B3281593 : Blo 381763 3281593 := bstep (se 2 (by rfl) ⟨1230597, by rfl⟩ : syracuseStep 3281593 = 2461195) B2461195
theorem B1774295 : Blo 381763 1774295 := bstep (se 1 (by rfl) ⟨1330721, by rfl⟩ : syracuseStep 1774295 = 2661443) B2661443
theorem B1643257 : Blo 381763 1643257 := bstep (se 2 (by rfl) ⟨616221, by rfl⟩ : syracuseStep 1643257 = 1232443) B1232443
theorem B1578199 : Blo 381763 1578199 := bstep (se 1 (by rfl) ⟨1183649, by rfl⟩ : syracuseStep 1578199 = 2367299) B2367299
theorem B693481 : Blo 381763 693481 := bstep (se 2 (by rfl) ⟨260055, by rfl⟩ : syracuseStep 693481 = 520111) B520111
theorem B923017 : Blo 381763 923017 := bstep (se 2 (by rfl) ⟨346131, by rfl⟩ : syracuseStep 923017 = 692263) B692263
theorem B431527 : Blo 381763 431527 := bstep (se 1 (by rfl) ⟨323645, by rfl⟩ : syracuseStep 431527 = 647291) B647291
theorem B1938977 : Blo 381763 1938977 := bstep (se 2 (by rfl) ⟨727116, by rfl⟩ : syracuseStep 1938977 = 1454233) B1454233
theorem B694057 : Blo 381763 694057 := bstep (se 2 (by rfl) ⟨260271, by rfl⟩ : syracuseStep 694057 = 520543) B520543
theorem B432103 : Blo 381763 432103 := bstep (se 1 (by rfl) ⟨324077, by rfl⟩ : syracuseStep 432103 = 648155) B648155
theorem B1841575 : Blo 381763 1841575 := bstep (se 1 (by rfl) ⟨1381181, by rfl⟩ : syracuseStep 1841575 = 2762363) B2762363
theorem B1841591 : Blo 381763 1841591 := bstep (se 1 (by rfl) ⟨1381193, by rfl⟩ : syracuseStep 1841591 = 2762387) B2762387
theorem B4135799 : Blo 381763 4135799 := bstep (se 1 (by rfl) ⟨3101849, by rfl⟩ : syracuseStep 4135799 = 6203699) B6203699
theorem B859175 : Blo 381763 859175 := bstep (se 1 (by rfl) ⟨644381, by rfl⟩ : syracuseStep 859175 = 1288763) B1288763
theorem B924871 : Blo 381763 924871 := bstep (se 1 (by rfl) ⟨693653, by rfl⟩ : syracuseStep 924871 = 1387307) B1387307
theorem B859355 : Blo 381763 859355 := bstep (se 1 (by rfl) ⟨644516, by rfl⟩ : syracuseStep 859355 = 1289033) B1289033
theorem B1023329 : Blo 381763 1023329 := bstep (se 2 (by rfl) ⟨383748, by rfl⟩ : syracuseStep 1023329 = 767497) B767497
theorem B859553 : Blo 381763 859553 := bstep (se 2 (by rfl) ⟨322332, by rfl⟩ : syracuseStep 859553 = 644665) B644665
theorem B433759 : Blo 381763 433759 := bstep (se 1 (by rfl) ⟨325319, by rfl⟩ : syracuseStep 433759 = 650639) B650639
theorem B860111 : Blo 381763 860111 := bstep (se 1 (by rfl) ⟨645083, by rfl⟩ : syracuseStep 860111 = 1290167) B1290167
theorem B860489 : Blo 381763 860489 := bstep (se 2 (by rfl) ⟨322683, by rfl⟩ : syracuseStep 860489 = 645367) B645367
theorem B1450331 : Blo 381763 1450331 := bstep (se 1 (by rfl) ⟨1087748, by rfl⟩ : syracuseStep 1450331 = 2175497) B2175497
theorem B860507 : Blo 381763 860507 := bstep (se 1 (by rfl) ⟨645380, by rfl⟩ : syracuseStep 860507 = 1290761) B1290761
theorem B1843631 : Blo 381763 1843631 := bstep (se 1 (by rfl) ⟨1382723, by rfl⟩ : syracuseStep 1843631 = 2765447) B2765447
theorem B2073089 : Blo 381763 2073089 := bstep (se 2 (by rfl) ⟨777408, by rfl⟩ : syracuseStep 2073089 = 1554817) B1554817
theorem B1450649 : Blo 381763 1450649 := bstep (se 2 (by rfl) ⟨543993, by rfl⟩ : syracuseStep 1450649 = 1087987) B1087987
theorem B18621197 : Blo 381763 18621197 := bstep (se 3 (by rfl) ⟨3491474, by rfl⟩ : syracuseStep 18621197 = 6982949) B6982949
theorem B1450831 : Blo 381763 1450831 := bstep (se 1 (by rfl) ⟨1088123, by rfl⟩ : syracuseStep 1450831 = 2176247) B2176247
theorem B861083 : Blo 381763 861083 := bstep (se 1 (by rfl) ⟨645812, by rfl⟩ : syracuseStep 861083 = 1291625) B1291625
theorem B1451105 : Blo 381763 1451105 := bstep (se 2 (by rfl) ⟨544164, by rfl⟩ : syracuseStep 1451105 = 1088329) B1088329
theorem B861281 : Blo 381763 861281 := bstep (se 2 (by rfl) ⟨322980, by rfl⟩ : syracuseStep 861281 = 645961) B645961
theorem B1451303 : Blo 381763 1451303 := bstep (se 1 (by rfl) ⟨1088477, by rfl⟩ : syracuseStep 1451303 = 2176955) B2176955
theorem B861479 : Blo 381763 861479 := bstep (se 1 (by rfl) ⟨646109, by rfl⟩ : syracuseStep 861479 = 1292219) B1292219
theorem B861857 : Blo 381763 861857 := bstep (se 2 (by rfl) ⟨323196, by rfl⟩ : syracuseStep 861857 = 646393) B646393
theorem B2467529 : Blo 381763 2467529 := bstep (se 2 (by rfl) ⟨925323, by rfl⟩ : syracuseStep 2467529 = 1850647) B1850647
theorem B1943351 : Blo 381763 1943351 := bstep (se 1 (by rfl) ⟨1457513, by rfl⟩ : syracuseStep 1943351 = 2915027) B2915027
theorem B730937 : Blo 381763 730937 := bstep (se 2 (by rfl) ⟨274101, by rfl⟩ : syracuseStep 730937 = 548203) B548203
theorem B4892561 : Blo 381763 4892561 := bstep (se 2 (by rfl) ⟨1834710, by rfl⟩ : syracuseStep 4892561 = 3669421) B3669421
theorem B3123127 : Blo 381763 3123127 := bstep (se 1 (by rfl) ⟨2342345, by rfl⟩ : syracuseStep 3123127 = 4684691) B4684691
theorem B862217 : Blo 381763 862217 := bstep (se 2 (by rfl) ⟨323331, by rfl⟩ : syracuseStep 862217 = 646663) B646663
theorem B1747129 : Blo 381763 1747129 := bstep (se 2 (by rfl) ⟨655173, by rfl⟩ : syracuseStep 1747129 = 1310347) B1310347
theorem B4139261 : Blo 381763 4139261 := bstep (se 3 (by rfl) ⟨776111, by rfl⟩ : syracuseStep 4139261 = 1552223) B1552223
theorem B1943837 : Blo 381763 1943837 := bstep (se 3 (by rfl) ⟨364469, by rfl⟩ : syracuseStep 1943837 = 728939) B728939
theorem B1091951 : Blo 381763 1091951 := bstep (se 1 (by rfl) ⟨818963, by rfl⟩ : syracuseStep 1091951 = 1637927) B1637927
theorem B862631 : Blo 381763 862631 := bstep (se 1 (by rfl) ⟨646973, by rfl⟩ : syracuseStep 862631 = 1293947) B1293947
theorem B862739 : Blo 381763 862739 := bstep (se 1 (by rfl) ⟨647054, by rfl⟩ : syracuseStep 862739 = 1294109) B1294109
theorem B862793 : Blo 381763 862793 := bstep (se 2 (by rfl) ⟨323547, by rfl⟩ : syracuseStep 862793 = 647095) B647095
theorem B1288979 : Blo 381763 1288979 := bstep (se 1 (by rfl) ⟨966734, by rfl⟩ : syracuseStep 1288979 = 1933469) B1933469
theorem B863207 : Blo 381763 863207 := bstep (se 1 (by rfl) ⟨647405, by rfl⟩ : syracuseStep 863207 = 1294811) B1294811
theorem B863585 : Blo 381763 863585 := bstep (se 2 (by rfl) ⟨323844, by rfl⟩ : syracuseStep 863585 = 647689) B647689
theorem B863675 : Blo 381763 863675 := bstep (se 1 (by rfl) ⟨647756, by rfl⟩ : syracuseStep 863675 = 1295513) B1295513
theorem B863801 : Blo 381763 863801 := bstep (se 2 (by rfl) ⟨323925, by rfl⟩ : syracuseStep 863801 = 647851) B647851
theorem B1289843 : Blo 381763 1289843 := bstep (se 1 (by rfl) ⟨967382, by rfl⟩ : syracuseStep 1289843 = 1934765) B1934765
theorem B4140811 : Blo 381763 4140811 := bstep (se 1 (by rfl) ⟨3105608, by rfl⟩ : syracuseStep 4140811 = 6211217) B6211217
theorem B1290113 : Blo 381763 1290113 := bstep (se 2 (by rfl) ⟨483792, by rfl⟩ : syracuseStep 1290113 = 967585) B967585
theorem B26619799 : Blo 381763 26619799 := bstep (se 1 (by rfl) ⟨19964849, by rfl⟩ : syracuseStep 26619799 = 39929699) B39929699
theorem B1945619 : Blo 381763 1945619 := bstep (se 1 (by rfl) ⟨1459214, by rfl⟩ : syracuseStep 1945619 = 2918429) B2918429
theorem B864467 : Blo 381763 864467 := bstep (se 1 (by rfl) ⟨648350, by rfl⟩ : syracuseStep 864467 = 1296701) B1296701
theorem B864521 : Blo 381763 864521 := bstep (se 2 (by rfl) ⟨324195, by rfl⟩ : syracuseStep 864521 = 648391) B648391
theorem B1093979 : Blo 381763 1093979 := bstep (se 1 (by rfl) ⟨820484, by rfl⟩ : syracuseStep 1093979 = 1640969) B1640969
theorem B864737 : Blo 381763 864737 := bstep (se 2 (by rfl) ⟨324276, by rfl⟩ : syracuseStep 864737 = 648553) B648553
theorem B1847879 : Blo 381763 1847879 := bstep (se 1 (by rfl) ⟨1385909, by rfl⟩ : syracuseStep 1847879 = 2771819) B2771819
theorem B1290923 : Blo 381763 1290923 := bstep (se 1 (by rfl) ⟨968192, by rfl⟩ : syracuseStep 1290923 = 1936385) B1936385
theorem B1979063 : Blo 381763 1979063 := bstep (se 1 (by rfl) ⟨1484297, by rfl⟩ : syracuseStep 1979063 = 2968595) B2968595
theorem B4141813 : Blo 381763 4141813 := bstep (se 5 (by rfl) ⟨194147, by rfl⟩ : syracuseStep 4141813 = 388295) B388295
theorem B865043 : Blo 381763 865043 := bstep (se 1 (by rfl) ⟨648782, by rfl⟩ : syracuseStep 865043 = 1297565) B1297565
theorem B865403 : Blo 381763 865403 := bstep (se 1 (by rfl) ⟨649052, by rfl⟩ : syracuseStep 865403 = 1298105) B1298105
theorem B1291463 : Blo 381763 1291463 := bstep (se 1 (by rfl) ⟨968597, by rfl⟩ : syracuseStep 1291463 = 1937195) B1937195
theorem B1553651 : Blo 381763 1553651 := bstep (se 1 (by rfl) ⟨1165238, by rfl⟩ : syracuseStep 1553651 = 2330477) B2330477
theorem B865529 : Blo 381763 865529 := bstep (se 2 (by rfl) ⟨324573, by rfl⟩ : syracuseStep 865529 = 649147) B649147
theorem B865673 : Blo 381763 865673 := bstep (se 2 (by rfl) ⟨324627, by rfl⟩ : syracuseStep 865673 = 649255) B649255
theorem B865799 : Blo 381763 865799 := bstep (se 1 (by rfl) ⟨649349, by rfl⟩ : syracuseStep 865799 = 1298699) B1298699
theorem B3683879 : Blo 381763 3683879 := bstep (se 1 (by rfl) ⟨2762909, by rfl⟩ : syracuseStep 3683879 = 5525819) B5525819
theorem B865979 : Blo 381763 865979 := bstep (se 1 (by rfl) ⟨649484, by rfl⟩ : syracuseStep 865979 = 1298969) B1298969
theorem B11056925 : Blo 381763 11056925 := bstep (se 3 (by rfl) ⟨2073173, by rfl⟩ : syracuseStep 11056925 = 4146347) B4146347
theorem B6600503 : Blo 381763 6600503 := bstep (se 1 (by rfl) ⟨4950377, by rfl⟩ : syracuseStep 6600503 = 9900755) B9900755
theorem B866105 : Blo 381763 866105 := bstep (se 2 (by rfl) ⟨324789, by rfl⟩ : syracuseStep 866105 = 649579) B649579
theorem B3291299 : Blo 381763 3291299 := bstep (se 1 (by rfl) ⟨2468474, by rfl⟩ : syracuseStep 3291299 = 4936949) B4936949
theorem B866735 : Blo 381763 866735 := bstep (se 1 (by rfl) ⟨650051, by rfl⟩ : syracuseStep 866735 = 1300103) B1300103
theorem B1751507 : Blo 381763 1751507 := bstep (se 1 (by rfl) ⟨1313630, by rfl⟩ : syracuseStep 1751507 = 2627261) B2627261
theorem B866771 : Blo 381763 866771 := bstep (se 1 (by rfl) ⟨650078, by rfl⟩ : syracuseStep 866771 = 1300157) B1300157
theorem B1849895 : Blo 381763 1849895 := bstep (se 1 (by rfl) ⟨1387421, by rfl⟩ : syracuseStep 1849895 = 2774843) B2774843
theorem B866879 : Blo 381763 866879 := bstep (se 1 (by rfl) ⟨650159, by rfl⟩ : syracuseStep 866879 = 1300319) B1300319
theorem B866987 : Blo 381763 866987 := bstep (se 1 (by rfl) ⟨650240, by rfl⟩ : syracuseStep 866987 = 1300481) B1300481
theorem B1292975 : Blo 381763 1292975 := bstep (se 1 (by rfl) ⟨969731, by rfl⟩ : syracuseStep 1292975 = 1939463) B1939463
theorem B1948535 : Blo 381763 1948535 := bstep (se 1 (by rfl) ⟨1461401, by rfl⟩ : syracuseStep 1948535 = 2922803) B2922803
theorem B1293299 : Blo 381763 1293299 := bstep (se 1 (by rfl) ⟨969974, by rfl⟩ : syracuseStep 1293299 = 1939949) B1939949
theorem B3292325 : Blo 381763 3292325 := bstep (se 4 (by rfl) ⟨308655, by rfl⟩ : syracuseStep 3292325 = 617311) B617311
theorem B867527 : Blo 381763 867527 := bstep (se 1 (by rfl) ⟨650645, by rfl⟩ : syracuseStep 867527 = 1301291) B1301291
theorem B6208757 : Blo 381763 6208757 := bstep (se 5 (by rfl) ⟨291035, by rfl⟩ : syracuseStep 6208757 = 582071) B582071
theorem B572711 : Blo 381763 572711 := bstep (se 1 (by rfl) ⟨429533, by rfl⟩ : syracuseStep 572711 = 859067) B859067
theorem B572795 : Blo 381763 572795 := bstep (se 1 (by rfl) ⟨429596, by rfl⟩ : syracuseStep 572795 = 859193) B859193
theorem B867707 : Blo 381763 867707 := bstep (se 1 (by rfl) ⟨650780, by rfl⟩ : syracuseStep 867707 = 1301561) B1301561
theorem B572921 : Blo 381763 572921 := bstep (se 2 (by rfl) ⟨214845, by rfl⟩ : syracuseStep 572921 = 429691) B429691
theorem B867833 : Blo 381763 867833 := bstep (se 2 (by rfl) ⟨325437, by rfl⟩ : syracuseStep 867833 = 650875) B650875
theorem B1293839 : Blo 381763 1293839 := bstep (se 1 (by rfl) ⟨970379, by rfl⟩ : syracuseStep 1293839 = 1940759) B1940759
theorem B3161659 : Blo 381763 3161659 := bstep (se 1 (by rfl) ⟨2371244, by rfl⟩ : syracuseStep 3161659 = 4742489) B4742489
theorem B867923 : Blo 381763 867923 := bstep (se 1 (by rfl) ⟨650942, by rfl⟩ : syracuseStep 867923 = 1301885) B1301885
theorem B573023 : Blo 381763 573023 := bstep (se 1 (by rfl) ⟨429767, by rfl⟩ : syracuseStep 573023 = 859535) B859535
theorem B1949345 : Blo 381763 1949345 := bstep (se 2 (by rfl) ⟨731004, by rfl⟩ : syracuseStep 1949345 = 1462009) B1462009
theorem B573239 : Blo 381763 573239 := bstep (se 1 (by rfl) ⟨429929, by rfl⟩ : syracuseStep 573239 = 859859) B859859
theorem B573545 : Blo 381763 573545 := bstep (se 2 (by rfl) ⟨215079, by rfl⟩ : syracuseStep 573545 = 430159) B430159
theorem B3096787 : Blo 381763 3096787 := bstep (se 1 (by rfl) ⟨2322590, by rfl⟩ : syracuseStep 3096787 = 4645181) B4645181
theorem B966937 : Blo 381763 966937 := bstep (se 2 (by rfl) ⟨362601, by rfl⟩ : syracuseStep 966937 = 725203) B725203
theorem B967079 : Blo 381763 967079 := bstep (se 1 (by rfl) ⟨725309, by rfl⟩ : syracuseStep 967079 = 1450619) B1450619
theorem B573863 : Blo 381763 573863 := bstep (se 1 (by rfl) ⟨430397, by rfl⟩ : syracuseStep 573863 = 860795) B860795
theorem B1458607 : Blo 381763 1458607 := bstep (se 1 (by rfl) ⟨1093955, by rfl⟩ : syracuseStep 1458607 = 2187911) B2187911
theorem B573947 : Blo 381763 573947 := bstep (se 1 (by rfl) ⟨430460, by rfl⟩ : syracuseStep 573947 = 860921) B860921
theorem B1294919 : Blo 381763 1294919 := bstep (se 1 (by rfl) ⟨971189, by rfl⟩ : syracuseStep 1294919 = 1942379) B1942379
theorem B967241 : Blo 381763 967241 := bstep (se 2 (by rfl) ⟨362715, by rfl⟩ : syracuseStep 967241 = 725431) B725431
theorem B574073 : Blo 381763 574073 := bstep (se 2 (by rfl) ⟨215277, by rfl⟩ : syracuseStep 574073 = 430555) B430555
theorem B574127 : Blo 381763 574127 := bstep (se 1 (by rfl) ⟨430595, by rfl⟩ : syracuseStep 574127 = 861191) B861191
theorem B441762497 : Blo 381763 441762497 := bstep (se 2 (by rfl) ⟨165660936, by rfl⟩ : syracuseStep 441762497 = 331321873) B331321873
theorem B574175 : Blo 381763 574175 := bstep (se 1 (by rfl) ⟨430631, by rfl⟩ : syracuseStep 574175 = 861263) B861263
theorem B1458911 : Blo 381763 1458911 := bstep (se 1 (by rfl) ⟨1094183, by rfl⟩ : syracuseStep 1458911 = 2188367) B2188367
theorem B3293945 : Blo 381763 3293945 := bstep (se 2 (by rfl) ⟨1235229, by rfl⟩ : syracuseStep 3293945 = 2470459) B2470459
theorem B475951 : Blo 381763 475951 := bstep (se 1 (by rfl) ⟨356963, by rfl⟩ : syracuseStep 475951 = 713927) B713927
theorem B1852355 : Blo 381763 1852355 := bstep (se 1 (by rfl) ⟨1389266, by rfl⟩ : syracuseStep 1852355 = 2778533) B2778533
theorem B574439 : Blo 381763 574439 := bstep (se 1 (by rfl) ⟨430829, by rfl⟩ : syracuseStep 574439 = 861659) B861659
theorem B1295351 : Blo 381763 1295351 := bstep (se 1 (by rfl) ⟨971513, by rfl⟩ : syracuseStep 1295351 = 1943027) B1943027
theorem B443611 : Blo 381763 443611 := bstep (se 1 (by rfl) ⟨332708, by rfl⟩ : syracuseStep 443611 = 665417) B665417
theorem B574697 : Blo 381763 574697 := bstep (se 2 (by rfl) ⟨215511, by rfl⟩ : syracuseStep 574697 = 431023) B431023
theorem B1557737 : Blo 381763 1557737 := bstep (se 2 (by rfl) ⟨584151, by rfl⟩ : syracuseStep 1557737 = 1168303) B1168303
theorem B574751 : Blo 381763 574751 := bstep (se 1 (by rfl) ⟨431063, by rfl⟩ : syracuseStep 574751 = 862127) B862127
theorem B1459565 : Blo 381763 1459565 := bstep (se 3 (by rfl) ⟨273668, by rfl⟩ : syracuseStep 1459565 = 547337) B547337
theorem B1459579 : Blo 381763 1459579 := bstep (se 1 (by rfl) ⟨1094684, by rfl⟩ : syracuseStep 1459579 = 2189369) B2189369
theorem B4900247 : Blo 381763 4900247 := bstep (se 1 (by rfl) ⟨3675185, by rfl⟩ : syracuseStep 4900247 = 7350371) B7350371
theorem B574919 : Blo 381763 574919 := bstep (se 1 (by rfl) ⟨431189, by rfl⟩ : syracuseStep 574919 = 862379) B862379
theorem B1951289 : Blo 381763 1951289 := bstep (se 2 (by rfl) ⟨731733, by rfl⟩ : syracuseStep 1951289 = 1463467) B1463467
theorem B575273 : Blo 381763 575273 := bstep (se 2 (by rfl) ⟨215727, by rfl⟩ : syracuseStep 575273 = 431455) B431455
theorem B575279 : Blo 381763 575279 := bstep (se 1 (by rfl) ⟨431459, by rfl⟩ : syracuseStep 575279 = 862919) B862919
theorem B1296215 : Blo 381763 1296215 := bstep (se 1 (by rfl) ⟨972161, by rfl⟩ : syracuseStep 1296215 = 1944323) B1944323
theorem B2901905 : Blo 381763 2901905 := bstep (se 2 (by rfl) ⟨1088214, by rfl⟩ : syracuseStep 2901905 = 2176429) B2176429
theorem B3688375 : Blo 381763 3688375 := bstep (se 1 (by rfl) ⟨2766281, by rfl⟩ : syracuseStep 3688375 = 5532563) B5532563
theorem B575753 : Blo 381763 575753 := bstep (se 2 (by rfl) ⟨215907, by rfl⟩ : syracuseStep 575753 = 431815) B431815
theorem B575855 : Blo 381763 575855 := bstep (se 1 (by rfl) ⟨431891, by rfl⟩ : syracuseStep 575855 = 863783) B863783
theorem B5261735 : Blo 381763 5261735 := bstep (se 1 (by rfl) ⟨3946301, by rfl⟩ : syracuseStep 5261735 = 7892603) B7892603
theorem B969185 : Blo 381763 969185 := bstep (se 2 (by rfl) ⟨363444, by rfl⟩ : syracuseStep 969185 = 726889) B726889
theorem B576071 : Blo 381763 576071 := bstep (se 1 (by rfl) ⟨432053, by rfl⟩ : syracuseStep 576071 = 864107) B864107
theorem B576107 : Blo 381763 576107 := bstep (se 1 (by rfl) ⟨432080, by rfl⟩ : syracuseStep 576107 = 864161) B864161
theorem B8276701 : Blo 381763 8276701 := bstep (se 3 (by rfl) ⟨1551881, by rfl⟩ : syracuseStep 8276701 = 3103763) B3103763
theorem B3099383 : Blo 381763 3099383 := bstep (se 1 (by rfl) ⟨2324537, by rfl⟩ : syracuseStep 3099383 = 4649075) B4649075
theorem B576335 : Blo 381763 576335 := bstep (se 1 (by rfl) ⟨432251, by rfl⟩ : syracuseStep 576335 = 864503) B864503
theorem B1297295 : Blo 381763 1297295 := bstep (se 1 (by rfl) ⟨972971, by rfl⟩ : syracuseStep 1297295 = 1945943) B1945943
theorem B969691 : Blo 381763 969691 := bstep (se 1 (by rfl) ⟨727268, by rfl⟩ : syracuseStep 969691 = 1454537) B1454537
theorem B226446353 : Blo 381763 226446353 := bstep (se 2 (by rfl) ⟨84917382, by rfl⟩ : syracuseStep 226446353 = 169834765) B169834765
theorem B576731 : Blo 381763 576731 := bstep (se 1 (by rfl) ⟨432548, by rfl⟩ : syracuseStep 576731 = 865097) B865097
theorem B970015 : Blo 381763 970015 := bstep (se 1 (by rfl) ⟨727511, by rfl⟩ : syracuseStep 970015 = 1455023) B1455023
theorem B576905 : Blo 381763 576905 := bstep (se 2 (by rfl) ⟨216339, by rfl⟩ : syracuseStep 576905 = 432679) B432679
theorem B1035659 : Blo 381763 1035659 := bstep (se 1 (by rfl) ⟨776744, by rfl⟩ : syracuseStep 1035659 = 1553489) B1553489
theorem B871867 : Blo 381763 871867 := bstep (se 1 (by rfl) ⟨653900, by rfl⟩ : syracuseStep 871867 = 1307801) B1307801
theorem B3264097 : Blo 381763 3264097 := bstep (se 2 (by rfl) ⟨1224036, by rfl⟩ : syracuseStep 3264097 = 2448073) B2448073
theorem B1068701 : Blo 381763 1068701 := bstep (se 3 (by rfl) ⟨200381, by rfl⟩ : syracuseStep 1068701 = 400763) B400763
theorem B4148945 : Blo 381763 4148945 := bstep (se 2 (by rfl) ⟨1555854, by rfl⟩ : syracuseStep 4148945 = 3111709) B3111709
theorem B577259 : Blo 381763 577259 := bstep (se 1 (by rfl) ⟨432944, by rfl⟩ : syracuseStep 577259 = 865889) B865889
theorem B1461995 : Blo 381763 1461995 := bstep (se 1 (by rfl) ⟨1096496, by rfl⟩ : syracuseStep 1461995 = 2192993) B2192993
theorem B577487 : Blo 381763 577487 := bstep (se 1 (by rfl) ⟨433115, by rfl⟩ : syracuseStep 577487 = 866231) B866231
theorem B1298537 : Blo 381763 1298537 := bstep (se 2 (by rfl) ⟨486951, by rfl⟩ : syracuseStep 1298537 = 973903) B973903
theorem B1462481 : Blo 381763 1462481 := bstep (se 2 (by rfl) ⟨548430, by rfl⟩ : syracuseStep 1462481 = 1096861) B1096861
theorem B2904335 : Blo 381763 2904335 := bstep (se 1 (by rfl) ⟨2178251, by rfl⟩ : syracuseStep 2904335 = 4356503) B4356503
theorem B971099 : Blo 381763 971099 := bstep (se 1 (by rfl) ⟨728324, by rfl⟩ : syracuseStep 971099 = 1456649) B1456649
theorem B577883 : Blo 381763 577883 := bstep (se 1 (by rfl) ⟨433412, by rfl⟩ : syracuseStep 577883 = 866825) B866825
theorem B578111 : Blo 381763 578111 := bstep (se 1 (by rfl) ⟨433583, by rfl⟩ : syracuseStep 578111 = 867167) B867167
theorem B1036871 : Blo 381763 1036871 := bstep (se 1 (by rfl) ⟨777653, by rfl⟩ : syracuseStep 1036871 = 1555307) B1555307
theorem B1462967 : Blo 381763 1462967 := bstep (se 1 (by rfl) ⟨1097225, by rfl⟩ : syracuseStep 1462967 = 2194451) B2194451
theorem B578231 : Blo 381763 578231 := bstep (se 1 (by rfl) ⟨433673, by rfl⟩ : syracuseStep 578231 = 867347) B867347
theorem B676687 : Blo 381763 676687 := bstep (se 1 (by rfl) ⟨507515, by rfl⟩ : syracuseStep 676687 = 1015031) B1015031
theorem B3494765 : Blo 381763 3494765 := bstep (se 3 (by rfl) ⟨655268, by rfl⟩ : syracuseStep 3494765 = 1310537) B1310537
theorem B381851 : Blo 381763 381851 := bstep (se 1 (by rfl) ⟨286388, by rfl⟩ : syracuseStep 381851 = 572777) B572777
theorem B578459 : Blo 381763 578459 := bstep (se 1 (by rfl) ⟨433844, by rfl⟩ : syracuseStep 578459 = 867689) B867689
theorem B1299401 : Blo 381763 1299401 := bstep (se 2 (by rfl) ⟨487275, by rfl⟩ : syracuseStep 1299401 = 974551) B974551
theorem B381903 : Blo 381763 381903 := bstep (se 1 (by rfl) ⟨286427, by rfl⟩ : syracuseStep 381903 = 572855) B572855
theorem B381927 : Blo 381763 381927 := bstep (se 1 (by rfl) ⟨286445, by rfl⟩ : syracuseStep 381927 = 572891) B572891
theorem B1299671 : Blo 381763 1299671 := bstep (se 1 (by rfl) ⟨974753, by rfl⟩ : syracuseStep 1299671 = 1949507) B1949507
theorem B382239 : Blo 381763 382239 := bstep (se 1 (by rfl) ⟨286679, by rfl⟩ : syracuseStep 382239 = 573359) B573359
theorem B972071 : Blo 381763 972071 := bstep (se 1 (by rfl) ⟨729053, by rfl⟩ : syracuseStep 972071 = 1458107) B1458107
theorem B382299 : Blo 381763 382299 := bstep (se 1 (by rfl) ⟨286724, by rfl⟩ : syracuseStep 382299 = 573449) B573449
theorem B382319 : Blo 381763 382319 := bstep (se 1 (by rfl) ⟨286739, by rfl⟩ : syracuseStep 382319 = 573479) B573479
theorem B382375 : Blo 381763 382375 := bstep (se 1 (by rfl) ⟨286781, by rfl⟩ : syracuseStep 382375 = 573563) B573563
theorem B1463741 : Blo 381763 1463741 := bstep (se 3 (by rfl) ⟨274451, by rfl⟩ : syracuseStep 1463741 = 548903) B548903
theorem B382459 : Blo 381763 382459 := bstep (se 1 (by rfl) ⟨286844, by rfl⟩ : syracuseStep 382459 = 573689) B573689
theorem B382527 : Blo 381763 382527 := bstep (se 1 (by rfl) ⟨286895, by rfl⟩ : syracuseStep 382527 = 573791) B573791
theorem B382535 : Blo 381763 382535 := bstep (se 1 (by rfl) ⟨286901, by rfl⟩ : syracuseStep 382535 = 573803) B573803
theorem B382687 : Blo 381763 382687 := bstep (se 1 (by rfl) ⟨287015, by rfl⟩ : syracuseStep 382687 = 574031) B574031
theorem B1038059 : Blo 381763 1038059 := bstep (se 1 (by rfl) ⟨778544, by rfl⟩ : syracuseStep 1038059 = 1557089) B1557089
theorem B382767 : Blo 381763 382767 := bstep (se 1 (by rfl) ⟨287075, by rfl⟩ : syracuseStep 382767 = 574151) B574151
theorem B382875 : Blo 381763 382875 := bstep (se 1 (by rfl) ⟨287156, by rfl⟩ : syracuseStep 382875 = 574313) B574313
theorem B382927 : Blo 381763 382927 := bstep (se 1 (by rfl) ⟨287195, by rfl⟩ : syracuseStep 382927 = 574391) B574391
theorem B382951 : Blo 381763 382951 := bstep (se 1 (by rfl) ⟨287213, by rfl⟩ : syracuseStep 382951 = 574427) B574427
theorem B11327521 : Blo 381763 11327521 := bstep (se 2 (by rfl) ⟨4247820, by rfl⟩ : syracuseStep 11327521 = 8495641) B8495641
theorem B383263 : Blo 381763 383263 := bstep (se 1 (by rfl) ⟨287447, by rfl⟩ : syracuseStep 383263 = 574895) B574895
theorem B383323 : Blo 381763 383323 := bstep (se 1 (by rfl) ⟨287492, by rfl⟩ : syracuseStep 383323 = 574985) B574985
theorem B383343 : Blo 381763 383343 := bstep (se 1 (by rfl) ⟨287507, by rfl⟩ : syracuseStep 383343 = 575015) B575015
theorem B547183 : Blo 381763 547183 := bstep (se 1 (by rfl) ⟨410387, by rfl⟩ : syracuseStep 547183 = 820775) B820775
theorem B383399 : Blo 381763 383399 := bstep (se 1 (by rfl) ⟨287549, by rfl⟩ : syracuseStep 383399 = 575099) B575099
theorem B383483 : Blo 381763 383483 := bstep (se 1 (by rfl) ⟨287612, by rfl⟩ : syracuseStep 383483 = 575225) B575225
theorem B383551 : Blo 381763 383551 := bstep (se 1 (by rfl) ⟨287663, by rfl⟩ : syracuseStep 383551 = 575327) B575327
theorem B383559 : Blo 381763 383559 := bstep (se 1 (by rfl) ⟨287669, by rfl⟩ : syracuseStep 383559 = 575339) B575339
theorem B383711 : Blo 381763 383711 := bstep (se 1 (by rfl) ⟨287783, by rfl⟩ : syracuseStep 383711 = 575567) B575567
theorem B973559 : Blo 381763 973559 := bstep (se 1 (by rfl) ⟨730169, by rfl⟩ : syracuseStep 973559 = 1460339) B1460339
theorem B383791 : Blo 381763 383791 := bstep (se 1 (by rfl) ⟨287843, by rfl⟩ : syracuseStep 383791 = 575687) B575687
theorem B383899 : Blo 381763 383899 := bstep (se 1 (by rfl) ⟨287924, by rfl⟩ : syracuseStep 383899 = 575849) B575849
theorem B383951 : Blo 381763 383951 := bstep (se 1 (by rfl) ⟨287963, by rfl⟩ : syracuseStep 383951 = 575927) B575927
theorem B613351 : Blo 381763 613351 := bstep (se 1 (by rfl) ⟨460013, by rfl⟩ : syracuseStep 613351 = 920027) B920027
theorem B383975 : Blo 381763 383975 := bstep (se 1 (by rfl) ⟨287981, by rfl⟩ : syracuseStep 383975 = 575963) B575963
theorem B1301723 : Blo 381763 1301723 := bstep (se 1 (by rfl) ⟨976292, by rfl⟩ : syracuseStep 1301723 = 1952585) B1952585
theorem B384287 : Blo 381763 384287 := bstep (se 1 (by rfl) ⟨288215, by rfl⟩ : syracuseStep 384287 = 576431) B576431
theorem B384347 : Blo 381763 384347 := bstep (se 1 (by rfl) ⟨288260, by rfl⟩ : syracuseStep 384347 = 576521) B576521
theorem B974177 : Blo 381763 974177 := bstep (se 2 (by rfl) ⟨365316, by rfl⟩ : syracuseStep 974177 = 730633) B730633
theorem B384367 : Blo 381763 384367 := bstep (se 1 (by rfl) ⟨288275, by rfl⟩ : syracuseStep 384367 = 576551) B576551
theorem B2776457 : Blo 381763 2776457 := bstep (se 2 (by rfl) ⟨1041171, by rfl⟩ : syracuseStep 2776457 = 2082343) B2082343
theorem B384423 : Blo 381763 384423 := bstep (se 1 (by rfl) ⟨288317, by rfl⟩ : syracuseStep 384423 = 576635) B576635
theorem B3694025 : Blo 381763 3694025 := bstep (se 2 (by rfl) ⟨1385259, by rfl⟩ : syracuseStep 3694025 = 2770519) B2770519
theorem B384507 : Blo 381763 384507 := bstep (se 1 (by rfl) ⟨288380, by rfl⟩ : syracuseStep 384507 = 576761) B576761
theorem B384575 : Blo 381763 384575 := bstep (se 1 (by rfl) ⟨288431, by rfl⟩ : syracuseStep 384575 = 576863) B576863
theorem B384583 : Blo 381763 384583 := bstep (se 1 (by rfl) ⟨288437, by rfl⟩ : syracuseStep 384583 = 576875) B576875
theorem B646751 : Blo 381763 646751 := bstep (se 1 (by rfl) ⟨485063, by rfl⟩ : syracuseStep 646751 = 970127) B970127
theorem B384735 : Blo 381763 384735 := bstep (se 1 (by rfl) ⟨288551, by rfl⟩ : syracuseStep 384735 = 577103) B577103
theorem B384815 : Blo 381763 384815 := bstep (se 1 (by rfl) ⟨288611, by rfl⟩ : syracuseStep 384815 = 577223) B577223
theorem B646967 : Blo 381763 646967 := bstep (se 1 (by rfl) ⟨485225, by rfl⟩ : syracuseStep 646967 = 970451) B970451
theorem B2809673 : Blo 381763 2809673 := bstep (se 2 (by rfl) ⟨1053627, by rfl⟩ : syracuseStep 2809673 = 2107255) B2107255
theorem B384923 : Blo 381763 384923 := bstep (se 1 (by rfl) ⟨288692, by rfl⟩ : syracuseStep 384923 = 577385) B577385
theorem B614351 : Blo 381763 614351 := bstep (se 1 (by rfl) ⟨460763, by rfl⟩ : syracuseStep 614351 = 921527) B921527
theorem B384975 : Blo 381763 384975 := bstep (se 1 (by rfl) ⟨288731, by rfl⟩ : syracuseStep 384975 = 577463) B577463
theorem B384999 : Blo 381763 384999 := bstep (se 1 (by rfl) ⟨288749, by rfl⟩ : syracuseStep 384999 = 577499) B577499
theorem B2449561 : Blo 381763 2449561 := bstep (se 2 (by rfl) ⟨918585, by rfl⟩ : syracuseStep 2449561 = 1837171) B1837171
theorem B385311 : Blo 381763 385311 := bstep (se 1 (by rfl) ⟨288983, by rfl⟩ : syracuseStep 385311 = 577967) B577967
theorem B385371 : Blo 381763 385371 := bstep (se 1 (by rfl) ⟨289028, by rfl⟩ : syracuseStep 385371 = 578057) B578057
theorem B385391 : Blo 381763 385391 := bstep (se 1 (by rfl) ⟨289043, by rfl⟩ : syracuseStep 385391 = 578087) B578087
theorem B385447 : Blo 381763 385447 := bstep (se 1 (by rfl) ⟨289085, by rfl⟩ : syracuseStep 385447 = 578171) B578171
theorem B385531 : Blo 381763 385531 := bstep (se 1 (by rfl) ⟨289148, by rfl⟩ : syracuseStep 385531 = 578297) B578297
theorem B7397891 : Blo 381763 7397891 := bstep (se 1 (by rfl) ⟨5548418, by rfl⟩ : syracuseStep 7397891 = 11096837) B11096837
theorem B2777611 : Blo 381763 2777611 := bstep (se 1 (by rfl) ⟨2083208, by rfl⟩ : syracuseStep 2777611 = 4166417) B4166417
theorem B647743 : Blo 381763 647743 := bstep (se 1 (by rfl) ⟨485807, by rfl⟩ : syracuseStep 647743 = 971615) B971615
theorem B385599 : Blo 381763 385599 := bstep (se 1 (by rfl) ⟨289199, by rfl⟩ : syracuseStep 385599 = 578399) B578399
theorem B385607 : Blo 381763 385607 := bstep (se 1 (by rfl) ⟨289205, by rfl⟩ : syracuseStep 385607 = 578411) B578411
theorem B385759 : Blo 381763 385759 := bstep (se 1 (by rfl) ⟨289319, by rfl⟩ : syracuseStep 385759 = 578639) B578639
theorem B975635 : Blo 381763 975635 := bstep (se 1 (by rfl) ⟨731726, by rfl⟩ : syracuseStep 975635 = 1463453) B1463453
theorem B975847 : Blo 381763 975847 := bstep (se 1 (by rfl) ⟨731885, by rfl⟩ : syracuseStep 975847 = 1463771) B1463771
theorem B648425 : Blo 381763 648425 := bstep (se 2 (by rfl) ⟨243159, by rfl⟩ : syracuseStep 648425 = 486319) B486319
theorem B976121 : Blo 381763 976121 := bstep (se 2 (by rfl) ⟨366045, by rfl⟩ : syracuseStep 976121 = 732091) B732091
theorem B648479 : Blo 381763 648479 := bstep (se 1 (by rfl) ⟨486359, by rfl⟩ : syracuseStep 648479 = 972719) B972719
theorem B484699 : Blo 381763 484699 := bstep (se 1 (by rfl) ⟨363524, by rfl⟩ : syracuseStep 484699 = 727049) B727049
theorem B1107613 : Blo 381763 1107613 := bstep (se 3 (by rfl) ⟨207677, by rfl⟩ : syracuseStep 1107613 = 415355) B415355
theorem B485671 : Blo 381763 485671 := bstep (se 1 (by rfl) ⟨364253, by rfl⟩ : syracuseStep 485671 = 728507) B728507
theorem B4680179 : Blo 381763 4680179 := bstep (se 1 (by rfl) ⟨3510134, by rfl⟩ : syracuseStep 4680179 = 7020269) B7020269
theorem B12479021 : Blo 381763 12479021 := bstep (se 3 (by rfl) ⟨2339816, by rfl⟩ : syracuseStep 12479021 = 4679633) B4679633
theorem B485995 : Blo 381763 485995 := bstep (se 1 (by rfl) ⟨364496, by rfl⟩ : syracuseStep 485995 = 728993) B728993
theorem B649849 : Blo 381763 649849 := bstep (se 2 (by rfl) ⟨243693, by rfl⟩ : syracuseStep 649849 = 487387) B487387
theorem B649903 : Blo 381763 649903 := bstep (se 1 (by rfl) ⟨487427, by rfl⟩ : syracuseStep 649903 = 974855) B974855
theorem B519743 : Blo 381763 519743 := bstep (se 1 (by rfl) ⟨389807, by rfl⟩ : syracuseStep 519743 = 779615) B779615
theorem B487711 : Blo 381763 487711 := bstep (se 1 (by rfl) ⟨365783, by rfl⟩ : syracuseStep 487711 = 731567) B731567
theorem B6222905 : Blo 381763 6222905 := bstep (se 2 (by rfl) ⟨2333589, by rfl⟩ : syracuseStep 6222905 = 4667179) B4667179
theorem B521321 : Blo 381763 521321 := bstep (se 2 (by rfl) ⟨195495, by rfl⟩ : syracuseStep 521321 = 390991) B390991
theorem B8123809 : Blo 381763 8123809 := bstep (se 2 (by rfl) ⟨3046428, by rfl⟩ : syracuseStep 8123809 = 6092857) B6092857
theorem B816571 : Blo 381763 816571 := bstep (se 1 (by rfl) ⟨612428, by rfl⟩ : syracuseStep 816571 = 1224857) B1224857
theorem B1635997 : Blo 381763 1635997 := bstep (se 3 (by rfl) ⟨306749, by rfl⟩ : syracuseStep 1635997 = 613499) B613499
theorem B6191639 : Blo 381763 6191639 := bstep (se 1 (by rfl) ⟨4643729, by rfl⟩ : syracuseStep 6191639 = 9287459) B9287459
theorem B818075 : Blo 381763 818075 := bstep (se 1 (by rfl) ⟨613556, by rfl⟩ : syracuseStep 818075 = 1227113) B1227113
theorem B9993239 : Blo 381763 9993239 := bstep (se 1 (by rfl) ⟨7494929, by rfl⟩ : syracuseStep 9993239 = 14989859) B14989859
theorem B1834825 : Blo 381763 1834825 := bstep (se 2 (by rfl) ⟨688059, by rfl⟩ : syracuseStep 1834825 = 1376119) B1376119
theorem B4357961 : Blo 381763 4357961 := bstep (se 2 (by rfl) ⟨1634235, by rfl⟩ : syracuseStep 4357961 = 3268471) B3268471
theorem B10485811 : Blo 381763 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B4129049 : Blo 381763 4129049 := bstep (se 2 (by rfl) ⟨1548393, by rfl⟩ : syracuseStep 4129049 = 3096787) B3096787
theorem B2195963 : Blo 381763 2195963 := bstep (se 1 (by rfl) ⟨1646972, by rfl⟩ : syracuseStep 2195963 = 3293945) B3293945
theorem B3703481 : Blo 381763 3703481 := bstep (se 2 (by rfl) ⟨1388805, by rfl⟩ : syracuseStep 3703481 = 2777611) B2777611
theorem B1934441 : Blo 381763 1934441 := bstep (se 2 (by rfl) ⟨725415, by rfl⟩ : syracuseStep 1934441 = 1450831) B1450831
theorem B1934603 : Blo 381763 1934603 := bstep (se 1 (by rfl) ⟨1450952, by rfl⟩ : syracuseStep 1934603 = 2901905) B2901905
theorem B3507823 : Blo 381763 3507823 := bstep (se 1 (by rfl) ⟨2630867, by rfl⟩ : syracuseStep 3507823 = 5261735) B5261735
theorem B591481 : Blo 381763 591481 := bstep (se 2 (by rfl) ⟨221805, by rfl⟩ : syracuseStep 591481 = 443611) B443611
theorem B2066255 : Blo 381763 2066255 := bstep (se 1 (by rfl) ⟨1549691, by rfl⟩ : syracuseStep 2066255 = 3099383) B3099383
theorem B1967951 : Blo 381763 1967951 := bstep (se 1 (by rfl) ⟨1475963, by rfl⟩ : syracuseStep 1967951 = 2951927) B2951927
theorem B150964235 : Blo 381763 150964235 := bstep (se 1 (by rfl) ⟨113223176, by rfl⟩ : syracuseStep 150964235 = 226446353) B226446353
theorem B690439 : Blo 381763 690439 := bstep (se 1 (by rfl) ⟨517829, by rfl⟩ : syracuseStep 690439 = 1035659) B1035659
theorem B1968475 : Blo 381763 1968475 := bstep (se 1 (by rfl) ⟨1476356, by rfl⟩ : syracuseStep 1968475 = 2952713) B2952713
theorem B4917833 : Blo 381763 4917833 := bstep (se 2 (by rfl) ⟨1844187, by rfl⟩ : syracuseStep 4917833 = 3688375) B3688375
theorem B4164169 : Blo 381763 4164169 := bstep (se 2 (by rfl) ⟨1561563, by rfl⟩ : syracuseStep 4164169 = 3123127) B3123127
theorem B1837673 : Blo 381763 1837673 := bstep (se 2 (by rfl) ⟨689127, by rfl⟩ : syracuseStep 1837673 = 1378255) B1378255
theorem B1936223 : Blo 381763 1936223 := bstep (se 1 (by rfl) ⟨1452167, by rfl⟩ : syracuseStep 1936223 = 2904335) B2904335
theorem B2329505 : Blo 381763 2329505 := bstep (se 2 (by rfl) ⟨873564, by rfl⟩ : syracuseStep 2329505 = 1747129) B1747129
theorem B691247 : Blo 381763 691247 := bstep (se 1 (by rfl) ⟨518435, by rfl⟩ : syracuseStep 691247 = 1036871) B1036871
theorem B1182863 : Blo 381763 1182863 := bstep (se 1 (by rfl) ⟨887147, by rfl⟩ : syracuseStep 1182863 = 1774295) B1774295
theorem B2329843 : Blo 381763 2329843 := bstep (se 1 (by rfl) ⟨1747382, by rfl⟩ : syracuseStep 2329843 = 3494765) B3494765
theorem B692039 : Blo 381763 692039 := bstep (se 1 (by rfl) ⟨519029, by rfl⟩ : syracuseStep 692039 = 1038059) B1038059
theorem B2757199 : Blo 381763 2757199 := bstep (se 1 (by rfl) ⟨2067899, by rfl⟩ : syracuseStep 2757199 = 4135799) B4135799
theorem B2462683 : Blo 381763 2462683 := bstep (se 1 (by rfl) ⟨1847012, by rfl⟩ : syracuseStep 2462683 = 3694025) B3694025
theorem B431167 : Blo 381763 431167 := bstep (se 1 (by rfl) ⟨323375, by rfl⟩ : syracuseStep 431167 = 646751) B646751
theorem B35493065 : Blo 381763 35493065 := bstep (se 2 (by rfl) ⟨13309899, by rfl⟩ : syracuseStep 35493065 = 26619799) B26619799
theorem B431311 : Blo 381763 431311 := bstep (se 1 (by rfl) ⟨323483, by rfl⟩ : syracuseStep 431311 = 646967) B646967
theorem B1873115 : Blo 381763 1873115 := bstep (se 1 (by rfl) ⟨1404836, by rfl⟩ : syracuseStep 1873115 = 2809673) B2809673
theorem B1382059 : Blo 381763 1382059 := bstep (se 1 (by rfl) ⟨1036544, by rfl⟩ : syracuseStep 1382059 = 2073089) B2073089
theorem B3151673 : Blo 381763 3151673 := bstep (se 2 (by rfl) ⟨1181877, by rfl⟩ : syracuseStep 3151673 = 2363755) B2363755
theorem B432283 : Blo 381763 432283 := bstep (se 1 (by rfl) ⟨324212, by rfl⟩ : syracuseStep 432283 = 648425) B648425
theorem B432319 : Blo 381763 432319 := bstep (se 1 (by rfl) ⟨324239, by rfl⟩ : syracuseStep 432319 = 648479) B648479
theorem B1645019 : Blo 381763 1645019 := bstep (se 1 (by rfl) ⟨1233764, by rfl⟩ : syracuseStep 1645019 = 2467529) B2467529
theorem B2759507 : Blo 381763 2759507 := bstep (se 1 (by rfl) ⟨2069630, by rfl⟩ : syracuseStep 2759507 = 4139261) B4139261
theorem B727967 : Blo 381763 727967 := bstep (se 1 (by rfl) ⟨545975, by rfl⟩ : syracuseStep 727967 = 1091951) B1091951
theorem B2104265 : Blo 381763 2104265 := bstep (se 2 (by rfl) ⟨789099, by rfl⟩ : syracuseStep 2104265 = 1578199) B1578199
theorem B924641 : Blo 381763 924641 := bstep (se 2 (by rfl) ⟨346740, by rfl⟩ : syracuseStep 924641 = 693481) B693481
theorem B3120119 : Blo 381763 3120119 := bstep (se 1 (by rfl) ⟨2340089, by rfl⟩ : syracuseStep 3120119 = 4680179) B4680179
theorem B859319 : Blo 381763 859319 := bstep (se 1 (by rfl) ⟨644489, by rfl⟩ : syracuseStep 859319 = 1288979) B1288979
theorem B925409 : Blo 381763 925409 := bstep (se 2 (by rfl) ⟨347028, by rfl⟩ : syracuseStep 925409 = 694057) B694057
theorem B859895 : Blo 381763 859895 := bstep (se 1 (by rfl) ⟨644921, by rfl⟩ : syracuseStep 859895 = 1289843) B1289843
theorem B860075 : Blo 381763 860075 := bstep (se 1 (by rfl) ⟨645056, by rfl⟩ : syracuseStep 860075 = 1290113) B1290113
theorem B729319 : Blo 381763 729319 := bstep (se 1 (by rfl) ⟨546989, by rfl⟩ : syracuseStep 729319 = 1093979) B1093979
theorem B860615 : Blo 381763 860615 := bstep (se 1 (by rfl) ⟨645461, by rfl⟩ : syracuseStep 860615 = 1290923) B1290923
theorem B1319375 : Blo 381763 1319375 := bstep (se 1 (by rfl) ⟨989531, by rfl⟩ : syracuseStep 1319375 = 1979063) B1979063
theorem B729577 : Blo 381763 729577 := bstep (se 2 (by rfl) ⟨273591, by rfl⟩ : syracuseStep 729577 = 547183) B547183
theorem B860975 : Blo 381763 860975 := bstep (se 1 (by rfl) ⟨645731, by rfl⟩ : syracuseStep 860975 = 1291463) B1291463
theorem B5907269 : Blo 381763 5907269 := bstep (se 4 (by rfl) ⟨553806, by rfl⟩ : syracuseStep 5907269 = 1107613) B1107613
theorem B4400335 : Blo 381763 4400335 := bstep (se 1 (by rfl) ⟨3300251, by rfl⟩ : syracuseStep 4400335 = 6600503) B6600503
theorem B1385981 : Blo 381763 1385981 := bstep (se 3 (by rfl) ⟨259871, by rfl⟩ : syracuseStep 1385981 = 519743) B519743
theorem B861983 : Blo 381763 861983 := bstep (se 1 (by rfl) ⟨646487, by rfl⟩ : syracuseStep 861983 = 1292975) B1292975
theorem B862199 : Blo 381763 862199 := bstep (se 1 (by rfl) ⟨646649, by rfl⟩ : syracuseStep 862199 = 1293299) B1293299
theorem B6662159 : Blo 381763 6662159 := bstep (se 1 (by rfl) ⟨4996619, by rfl⟩ : syracuseStep 6662159 = 9993239) B9993239
theorem B4139171 : Blo 381763 4139171 := bstep (se 1 (by rfl) ⟨3104378, by rfl⟩ : syracuseStep 4139171 = 6208757) B6208757
theorem B862559 : Blo 381763 862559 := bstep (se 1 (by rfl) ⟨646919, by rfl⟩ : syracuseStep 862559 = 1293839) B1293839
theorem B2206403 : Blo 381763 2206403 := bstep (se 1 (by rfl) ⟨1654802, by rfl⟩ : syracuseStep 2206403 = 3309605) B3309605
theorem B2468555 : Blo 381763 2468555 := bstep (se 1 (by rfl) ⟨1851416, by rfl⟩ : syracuseStep 2468555 = 3702833) B3702833
theorem B1289195 : Blo 381763 1289195 := bstep (se 1 (by rfl) ⟨966896, by rfl⟩ : syracuseStep 1289195 = 1933793) B1933793
theorem B1289249 : Blo 381763 1289249 := bstep (se 2 (by rfl) ⟨483468, by rfl⟩ : syracuseStep 1289249 = 966937) B966937
theorem B863279 : Blo 381763 863279 := bstep (se 1 (by rfl) ⟨647459, by rfl⟩ : syracuseStep 863279 = 1294919) B1294919
theorem B2927663 : Blo 381763 2927663 := bstep (se 1 (by rfl) ⟨2195747, by rfl⟩ : syracuseStep 2927663 = 4391495) B4391495
theorem B4369625 : Blo 381763 4369625 := bstep (se 2 (by rfl) ⟨1638609, by rfl⟩ : syracuseStep 4369625 = 3277219) B3277219
theorem B1944809 : Blo 381763 1944809 := bstep (se 2 (by rfl) ⟨729303, by rfl⟩ : syracuseStep 1944809 = 1458607) B1458607
theorem B1223923 : Blo 381763 1223923 := bstep (se 1 (by rfl) ⟨917942, by rfl⟩ : syracuseStep 1223923 = 1835885) B1835885
theorem B863567 : Blo 381763 863567 := bstep (se 1 (by rfl) ⟨647675, by rfl⟩ : syracuseStep 863567 = 1295351) B1295351
theorem B863657 : Blo 381763 863657 := bstep (se 2 (by rfl) ⟨323871, by rfl⟩ : syracuseStep 863657 = 647743) B647743
theorem B634601 : Blo 381763 634601 := bstep (se 2 (by rfl) ⟨237975, by rfl⟩ : syracuseStep 634601 = 475951) B475951
theorem B864143 : Blo 381763 864143 := bstep (se 1 (by rfl) ⟨648107, by rfl⟩ : syracuseStep 864143 = 1296215) B1296215
theorem B1093819 : Blo 381763 1093819 := bstep (se 1 (by rfl) ⟨820364, by rfl⟩ : syracuseStep 1093819 = 1640729) B1640729
theorem B1290707 : Blo 381763 1290707 := bstep (se 1 (by rfl) ⟨968030, by rfl⟩ : syracuseStep 1290707 = 1936061) B1936061
theorem B1946105 : Blo 381763 1946105 := bstep (se 2 (by rfl) ⟨729789, by rfl⟩ : syracuseStep 1946105 = 1459579) B1459579
theorem B864863 : Blo 381763 864863 := bstep (se 1 (by rfl) ⟨648647, by rfl⟩ : syracuseStep 864863 = 1297295) B1297295
theorem B1225601 : Blo 381763 1225601 := bstep (se 2 (by rfl) ⟨459600, by rfl⟩ : syracuseStep 1225601 = 919201) B919201
theorem B2765963 : Blo 381763 2765963 := bstep (se 1 (by rfl) ⟨2074472, by rfl⟩ : syracuseStep 2765963 = 4148945) B4148945
theorem B1094867 : Blo 381763 1094867 := bstep (se 1 (by rfl) ⟨821150, by rfl⟩ : syracuseStep 1094867 = 1642301) B1642301
theorem B2471219 : Blo 381763 2471219 := bstep (se 1 (by rfl) ⟨1853414, by rfl⟩ : syracuseStep 2471219 = 3706829) B3706829
theorem B865691 : Blo 381763 865691 := bstep (se 1 (by rfl) ⟨649268, by rfl⟩ : syracuseStep 865691 = 1298537) B1298537
theorem B1554103 : Blo 381763 1554103 := bstep (se 1 (by rfl) ⟨1165577, by rfl⟩ : syracuseStep 1554103 = 2331155) B2331155
theorem B1095403 : Blo 381763 1095403 := bstep (se 1 (by rfl) ⟨821552, by rfl⟩ : syracuseStep 1095403 = 1643105) B1643105
theorem B3979145 : Blo 381763 3979145 := bstep (se 2 (by rfl) ⟨1492179, by rfl⟩ : syracuseStep 3979145 = 2984359) B2984359
theorem B866267 : Blo 381763 866267 := bstep (se 1 (by rfl) ⟨649700, by rfl⟩ : syracuseStep 866267 = 1299401) B1299401
theorem B866447 : Blo 381763 866447 := bstep (se 1 (by rfl) ⟨649835, by rfl⟩ : syracuseStep 866447 = 1299671) B1299671
theorem B866465 : Blo 381763 866465 := bstep (se 2 (by rfl) ⟨324924, by rfl⟩ : syracuseStep 866465 = 649849) B649849
theorem B866537 : Blo 381763 866537 := bstep (se 2 (by rfl) ⟨324951, by rfl⟩ : syracuseStep 866537 = 649903) B649903
theorem B1292651 : Blo 381763 1292651 := bstep (se 1 (by rfl) ⟨969488, by rfl⟩ : syracuseStep 1292651 = 1938977) B1938977
theorem B1292921 : Blo 381763 1292921 := bstep (se 2 (by rfl) ⟨484845, by rfl⟩ : syracuseStep 1292921 = 969691) B969691
theorem B1096553 : Blo 381763 1096553 := bstep (se 2 (by rfl) ⟨411207, by rfl⟩ : syracuseStep 1096553 = 822415) B822415
theorem B1227727 : Blo 381763 1227727 := bstep (se 1 (by rfl) ⟨920795, by rfl⟩ : syracuseStep 1227727 = 1841591) B1841591
theorem B1293353 : Blo 381763 1293353 := bstep (se 2 (by rfl) ⟨485007, by rfl⟩ : syracuseStep 1293353 = 970015) B970015
theorem B572681 : Blo 381763 572681 := bstep (se 2 (by rfl) ⟨214755, by rfl⟩ : syracuseStep 572681 = 429511) B429511
theorem B1228061 : Blo 381763 1228061 := bstep (se 3 (by rfl) ⟨230261, by rfl⟩ : syracuseStep 1228061 = 460523) B460523
theorem B572783 : Blo 381763 572783 := bstep (se 1 (by rfl) ⟨429587, by rfl⟩ : syracuseStep 572783 = 859175) B859175
theorem B572903 : Blo 381763 572903 := bstep (se 1 (by rfl) ⟨429677, by rfl⟩ : syracuseStep 572903 = 859355) B859355
theorem B867815 : Blo 381763 867815 := bstep (se 1 (by rfl) ⟨650861, by rfl⟩ : syracuseStep 867815 = 1301723) B1301723
theorem B573035 : Blo 381763 573035 := bstep (se 1 (by rfl) ⟨429776, by rfl⟩ : syracuseStep 573035 = 859553) B859553
theorem B573161 : Blo 381763 573161 := bstep (se 2 (by rfl) ⟨214935, by rfl⟩ : syracuseStep 573161 = 429871) B429871
theorem B573305 : Blo 381763 573305 := bstep (se 2 (by rfl) ⟨214989, by rfl⟩ : syracuseStep 573305 = 429979) B429979
theorem B573407 : Blo 381763 573407 := bstep (se 1 (by rfl) ⟨430055, by rfl⟩ : syracuseStep 573407 = 860111) B860111
theorem B573659 : Blo 381763 573659 := bstep (se 1 (by rfl) ⟨430244, by rfl⟩ : syracuseStep 573659 = 860489) B860489
theorem B966887 : Blo 381763 966887 := bstep (se 1 (by rfl) ⟨725165, by rfl⟩ : syracuseStep 966887 = 1450331) B1450331
theorem B573671 : Blo 381763 573671 := bstep (se 1 (by rfl) ⟨430253, by rfl⟩ : syracuseStep 573671 = 860507) B860507
theorem B1229087 : Blo 381763 1229087 := bstep (se 1 (by rfl) ⟨921815, by rfl⟩ : syracuseStep 1229087 = 1843631) B1843631
theorem B4931927 : Blo 381763 4931927 := bstep (se 1 (by rfl) ⟨3698945, by rfl⟩ : syracuseStep 4931927 = 7397891) B7397891
theorem B573833 : Blo 381763 573833 := bstep (se 2 (by rfl) ⟨215187, by rfl⟩ : syracuseStep 573833 = 430375) B430375
theorem B967099 : Blo 381763 967099 := bstep (se 1 (by rfl) ⟨725324, by rfl⟩ : syracuseStep 967099 = 1450649) B1450649
theorem B573929 : Blo 381763 573929 := bstep (se 2 (by rfl) ⟨215223, by rfl⟩ : syracuseStep 573929 = 430447) B430447
theorem B574055 : Blo 381763 574055 := bstep (se 1 (by rfl) ⟨430541, by rfl⟩ : syracuseStep 574055 = 861083) B861083
theorem B967403 : Blo 381763 967403 := bstep (se 1 (by rfl) ⟨725552, by rfl⟩ : syracuseStep 967403 = 1451105) B1451105
theorem B574187 : Blo 381763 574187 := bstep (se 1 (by rfl) ⟨430640, by rfl⟩ : syracuseStep 574187 = 861281) B861281
theorem B574217 : Blo 381763 574217 := bstep (se 2 (by rfl) ⟨215331, by rfl⟩ : syracuseStep 574217 = 430663) B430663
theorem B967535 : Blo 381763 967535 := bstep (se 1 (by rfl) ⟨725651, by rfl⟩ : syracuseStep 967535 = 1451303) B1451303
theorem B574319 : Blo 381763 574319 := bstep (se 1 (by rfl) ⟨430739, by rfl⟩ : syracuseStep 574319 = 861479) B861479
theorem B4375457 : Blo 381763 4375457 := bstep (se 2 (by rfl) ⟨1640796, by rfl⟩ : syracuseStep 4375457 = 3281593) B3281593
theorem B5522417 : Blo 381763 5522417 := bstep (se 2 (by rfl) ⟨2070906, by rfl⟩ : syracuseStep 5522417 = 4141813) B4141813
theorem B902249 : Blo 381763 902249 := bstep (se 2 (by rfl) ⟨338343, by rfl⟩ : syracuseStep 902249 = 676687) B676687
theorem B574571 : Blo 381763 574571 := bstep (se 1 (by rfl) ⟨430928, by rfl⟩ : syracuseStep 574571 = 861857) B861857
theorem B1295567 : Blo 381763 1295567 := bstep (se 1 (by rfl) ⟨971675, by rfl⟩ : syracuseStep 1295567 = 1943351) B1943351
theorem B3261707 : Blo 381763 3261707 := bstep (se 1 (by rfl) ⟨2446280, by rfl⟩ : syracuseStep 3261707 = 4892561) B4892561
theorem B574811 : Blo 381763 574811 := bstep (se 1 (by rfl) ⟨431108, by rfl⟩ : syracuseStep 574811 = 862217) B862217
theorem B1295891 : Blo 381763 1295891 := bstep (se 1 (by rfl) ⟨971918, by rfl⟩ : syracuseStep 1295891 = 1943837) B1943837
theorem B575087 : Blo 381763 575087 := bstep (se 1 (by rfl) ⟨431315, by rfl⟩ : syracuseStep 575087 = 862631) B862631
theorem B575159 : Blo 381763 575159 := bstep (se 1 (by rfl) ⟨431369, by rfl⟩ : syracuseStep 575159 = 862739) B862739
theorem B575195 : Blo 381763 575195 := bstep (se 1 (by rfl) ⟨431396, by rfl⟩ : syracuseStep 575195 = 862793) B862793
theorem B1230689 : Blo 381763 1230689 := bstep (se 2 (by rfl) ⟨461508, by rfl⟩ : syracuseStep 1230689 = 923017) B923017
theorem B10831745 : Blo 381763 10831745 := bstep (se 2 (by rfl) ⟨4061904, by rfl⟩ : syracuseStep 10831745 = 8123809) B8123809
theorem B575369 : Blo 381763 575369 := bstep (se 2 (by rfl) ⟨215763, by rfl⟩ : syracuseStep 575369 = 431527) B431527
theorem B575471 : Blo 381763 575471 := bstep (se 1 (by rfl) ⟨431603, by rfl⟩ : syracuseStep 575471 = 863207) B863207
theorem B2181329 : Blo 381763 2181329 := bstep (se 2 (by rfl) ⟨817998, by rfl⟩ : syracuseStep 2181329 = 1635997) B1635997
theorem B575723 : Blo 381763 575723 := bstep (se 1 (by rfl) ⟨431792, by rfl⟩ : syracuseStep 575723 = 863585) B863585
theorem B575783 : Blo 381763 575783 := bstep (se 1 (by rfl) ⟨431837, by rfl⟩ : syracuseStep 575783 = 863675) B863675
theorem B575867 : Blo 381763 575867 := bstep (se 1 (by rfl) ⟨431900, by rfl⟩ : syracuseStep 575867 = 863801) B863801
theorem B576137 : Blo 381763 576137 := bstep (se 2 (by rfl) ⟨216051, by rfl⟩ : syracuseStep 576137 = 432103) B432103
theorem B1297079 : Blo 381763 1297079 := bstep (se 1 (by rfl) ⟨972809, by rfl⟩ : syracuseStep 1297079 = 1945619) B1945619
theorem B576311 : Blo 381763 576311 := bstep (se 1 (by rfl) ⟨432233, by rfl⟩ : syracuseStep 576311 = 864467) B864467
theorem B576347 : Blo 381763 576347 := bstep (se 1 (by rfl) ⟨432260, by rfl⟩ : syracuseStep 576347 = 864521) B864521
theorem B576491 : Blo 381763 576491 := bstep (se 1 (by rfl) ⟨432368, by rfl⟩ : syracuseStep 576491 = 864737) B864737
theorem B1231919 : Blo 381763 1231919 := bstep (se 1 (by rfl) ⟨923939, by rfl⟩ : syracuseStep 1231919 = 1847879) B1847879
theorem B576695 : Blo 381763 576695 := bstep (se 1 (by rfl) ⟨432521, by rfl⟩ : syracuseStep 576695 = 865043) B865043
theorem B4148603 : Blo 381763 4148603 := bstep (se 1 (by rfl) ⟨3111452, by rfl⟩ : syracuseStep 4148603 = 6222905) B6222905
theorem B576935 : Blo 381763 576935 := bstep (se 1 (by rfl) ⟨432701, by rfl⟩ : syracuseStep 576935 = 865403) B865403
theorem B1035767 : Blo 381763 1035767 := bstep (se 1 (by rfl) ⟨776825, by rfl⟩ : syracuseStep 1035767 = 1553651) B1553651
theorem B577019 : Blo 381763 577019 := bstep (se 1 (by rfl) ⟨432764, by rfl⟩ : syracuseStep 577019 = 865529) B865529
theorem B577115 : Blo 381763 577115 := bstep (se 1 (by rfl) ⟨432836, by rfl⟩ : syracuseStep 577115 = 865673) B865673
theorem B577199 : Blo 381763 577199 := bstep (se 1 (by rfl) ⟨432899, by rfl⟩ : syracuseStep 577199 = 865799) B865799
theorem B577319 : Blo 381763 577319 := bstep (se 1 (by rfl) ⟨432989, by rfl⟩ : syracuseStep 577319 = 865979) B865979
theorem B577403 : Blo 381763 577403 := bstep (se 1 (by rfl) ⟨433052, by rfl⟩ : syracuseStep 577403 = 866105) B866105
theorem B1233161 : Blo 381763 1233161 := bstep (se 2 (by rfl) ⟨462435, by rfl⟩ : syracuseStep 1233161 = 924871) B924871
theorem B577823 : Blo 381763 577823 := bstep (se 1 (by rfl) ⟨433367, by rfl⟩ : syracuseStep 577823 = 866735) B866735
theorem B1167671 : Blo 381763 1167671 := bstep (se 1 (by rfl) ⟨875753, by rfl⟩ : syracuseStep 1167671 = 1751507) B1751507
theorem B577847 : Blo 381763 577847 := bstep (se 1 (by rfl) ⟨433385, by rfl⟩ : syracuseStep 577847 = 866771) B866771
theorem B1233263 : Blo 381763 1233263 := bstep (se 1 (by rfl) ⟨924947, by rfl⟩ : syracuseStep 1233263 = 1849895) B1849895
theorem B577919 : Blo 381763 577919 := bstep (se 1 (by rfl) ⟨433439, by rfl⟩ : syracuseStep 577919 = 866879) B866879
theorem B577991 : Blo 381763 577991 := bstep (se 1 (by rfl) ⟨433493, by rfl⟩ : syracuseStep 577991 = 866987) B866987
theorem B1299023 : Blo 381763 1299023 := bstep (se 1 (by rfl) ⟨974267, by rfl⟩ : syracuseStep 1299023 = 1948535) B1948535
theorem B545383 : Blo 381763 545383 := bstep (se 1 (by rfl) ⟨409037, by rfl⟩ : syracuseStep 545383 = 818075) B818075
theorem B4215545 : Blo 381763 4215545 := bstep (se 2 (by rfl) ⟨1580829, by rfl⟩ : syracuseStep 4215545 = 3161659) B3161659
theorem B578345 : Blo 381763 578345 := bstep (se 2 (by rfl) ⟨216879, by rfl⟩ : syracuseStep 578345 = 433759) B433759
theorem B578351 : Blo 381763 578351 := bstep (se 1 (by rfl) ⟨433763, by rfl⟩ : syracuseStep 578351 = 867527) B867527
theorem B381807 : Blo 381763 381807 := bstep (se 1 (by rfl) ⟨286355, by rfl⟩ : syracuseStep 381807 = 572711) B572711
theorem B381863 : Blo 381763 381863 := bstep (se 1 (by rfl) ⟨286397, by rfl⟩ : syracuseStep 381863 = 572795) B572795
theorem B578471 : Blo 381763 578471 := bstep (se 1 (by rfl) ⟨433853, by rfl⟩ : syracuseStep 578471 = 867707) B867707
theorem B381947 : Blo 381763 381947 := bstep (se 1 (by rfl) ⟨286460, by rfl⟩ : syracuseStep 381947 = 572921) B572921
theorem B578555 : Blo 381763 578555 := bstep (se 1 (by rfl) ⟨433916, by rfl⟩ : syracuseStep 578555 = 867833) B867833
theorem B578615 : Blo 381763 578615 := bstep (se 1 (by rfl) ⟨433961, by rfl⟩ : syracuseStep 578615 = 867923) B867923
theorem B382015 : Blo 381763 382015 := bstep (se 1 (by rfl) ⟨286511, by rfl⟩ : syracuseStep 382015 = 573023) B573023
theorem B2446433 : Blo 381763 2446433 := bstep (se 2 (by rfl) ⟨917412, by rfl⟩ : syracuseStep 2446433 = 1834825) B1834825
theorem B1299563 : Blo 381763 1299563 := bstep (se 1 (by rfl) ⟨974672, by rfl⟩ : syracuseStep 1299563 = 1949345) B1949345
theorem B382159 : Blo 381763 382159 := bstep (se 1 (by rfl) ⟨286619, by rfl⟩ : syracuseStep 382159 = 573239) B573239
theorem B2905307 : Blo 381763 2905307 := bstep (se 1 (by rfl) ⟨2178980, by rfl⟩ : syracuseStep 2905307 = 4357961) B4357961
theorem B382363 : Blo 381763 382363 := bstep (se 1 (by rfl) ⟨286772, by rfl⟩ : syracuseStep 382363 = 573545) B573545
theorem B3266081 : Blo 381763 3266081 := bstep (se 2 (by rfl) ⟨1224780, by rfl⟩ : syracuseStep 3266081 = 2449561) B2449561
theorem B644719 : Blo 381763 644719 := bstep (se 1 (by rfl) ⟨483539, by rfl⟩ : syracuseStep 644719 = 967079) B967079
theorem B382575 : Blo 381763 382575 := bstep (se 1 (by rfl) ⟨286931, by rfl⟩ : syracuseStep 382575 = 573863) B573863
theorem B382631 : Blo 381763 382631 := bstep (se 1 (by rfl) ⟨286973, by rfl⟩ : syracuseStep 382631 = 573947) B573947
theorem B644827 : Blo 381763 644827 := bstep (se 1 (by rfl) ⟨483620, by rfl⟩ : syracuseStep 644827 = 967241) B967241
theorem B382715 : Blo 381763 382715 := bstep (se 1 (by rfl) ⟨287036, by rfl⟩ : syracuseStep 382715 = 574073) B574073
theorem B382751 : Blo 381763 382751 := bstep (se 1 (by rfl) ⟨287063, by rfl⟩ : syracuseStep 382751 = 574127) B574127
theorem B294508331 : Blo 381763 294508331 := bstep (se 1 (by rfl) ⟨220881248, by rfl⟩ : syracuseStep 294508331 = 441762497) B441762497
theorem B382783 : Blo 381763 382783 := bstep (se 1 (by rfl) ⟨287087, by rfl⟩ : syracuseStep 382783 = 574175) B574175
theorem B972607 : Blo 381763 972607 := bstep (se 1 (by rfl) ⟨729455, by rfl⟩ : syracuseStep 972607 = 1458911) B1458911
theorem B382959 : Blo 381763 382959 := bstep (se 1 (by rfl) ⟨287219, by rfl⟩ : syracuseStep 382959 = 574439) B574439
theorem B383131 : Blo 381763 383131 := bstep (se 1 (by rfl) ⟨287348, by rfl⟩ : syracuseStep 383131 = 574697) B574697
theorem B1038491 : Blo 381763 1038491 := bstep (se 1 (by rfl) ⟨778868, by rfl⟩ : syracuseStep 1038491 = 1557737) B1557737
theorem B383167 : Blo 381763 383167 := bstep (se 1 (by rfl) ⟨287375, by rfl⟩ : syracuseStep 383167 = 574751) B574751
theorem B973043 : Blo 381763 973043 := bstep (se 1 (by rfl) ⟨729782, by rfl⟩ : syracuseStep 973043 = 1459565) B1459565
theorem B3266831 : Blo 381763 3266831 := bstep (se 1 (by rfl) ⟨2450123, by rfl⟩ : syracuseStep 3266831 = 4900247) B4900247
theorem B383279 : Blo 381763 383279 := bstep (se 1 (by rfl) ⟨287459, by rfl⟩ : syracuseStep 383279 = 574919) B574919
theorem B1300859 : Blo 381763 1300859 := bstep (se 1 (by rfl) ⟨975644, by rfl⟩ : syracuseStep 1300859 = 1951289) B1951289
theorem B5560757 : Blo 381763 5560757 := bstep (se 5 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 5560757 = 521321) B521321
theorem B383515 : Blo 381763 383515 := bstep (se 1 (by rfl) ⟨287636, by rfl⟩ : syracuseStep 383515 = 575273) B575273
theorem B383519 : Blo 381763 383519 := bstep (se 1 (by rfl) ⟨287639, by rfl⟩ : syracuseStep 383519 = 575279) B575279
theorem B1301129 : Blo 381763 1301129 := bstep (se 2 (by rfl) ⟨487923, by rfl⟩ : syracuseStep 1301129 = 975847) B975847
theorem B383835 : Blo 381763 383835 := bstep (se 1 (by rfl) ⟨287876, by rfl⟩ : syracuseStep 383835 = 575753) B575753
theorem B383903 : Blo 381763 383903 := bstep (se 1 (by rfl) ⟨287927, by rfl⟩ : syracuseStep 383903 = 575855) B575855
theorem B646123 : Blo 381763 646123 := bstep (se 1 (by rfl) ⟨484592, by rfl⟩ : syracuseStep 646123 = 969185) B969185
theorem B384047 : Blo 381763 384047 := bstep (se 1 (by rfl) ⟨288035, by rfl⟩ : syracuseStep 384047 = 576071) B576071
theorem B384071 : Blo 381763 384071 := bstep (se 1 (by rfl) ⟨288053, by rfl⟩ : syracuseStep 384071 = 576107) B576107
theorem B2907251 : Blo 381763 2907251 := bstep (se 1 (by rfl) ⟨2180438, by rfl⟩ : syracuseStep 2907251 = 4360877) B4360877
theorem B646265 : Blo 381763 646265 := bstep (se 2 (by rfl) ⟨242349, by rfl⟩ : syracuseStep 646265 = 484699) B484699
theorem B384223 : Blo 381763 384223 := bstep (se 1 (by rfl) ⟨288167, by rfl⟩ : syracuseStep 384223 = 576335) B576335
theorem B2186635 : Blo 381763 2186635 := bstep (se 1 (by rfl) ⟨1639976, by rfl⟩ : syracuseStep 2186635 = 3279953) B3279953
theorem B384487 : Blo 381763 384487 := bstep (se 1 (by rfl) ⟨288365, by rfl⟩ : syracuseStep 384487 = 576731) B576731
theorem B9789011 : Blo 381763 9789011 := bstep (se 1 (by rfl) ⟨7341758, by rfl⟩ : syracuseStep 9789011 = 14683517) B14683517
theorem B384603 : Blo 381763 384603 := bstep (se 1 (by rfl) ⟨288452, by rfl⟩ : syracuseStep 384603 = 576905) B576905
theorem B548527 : Blo 381763 548527 := bstep (se 1 (by rfl) ⟨411395, by rfl⟩ : syracuseStep 548527 = 822791) B822791
theorem B384839 : Blo 381763 384839 := bstep (se 1 (by rfl) ⟨288629, by rfl⟩ : syracuseStep 384839 = 577259) B577259
theorem B974663 : Blo 381763 974663 := bstep (se 1 (by rfl) ⟨730997, by rfl⟩ : syracuseStep 974663 = 1461995) B1461995
theorem B4939613 : Blo 381763 4939613 := bstep (se 3 (by rfl) ⟨926177, by rfl⟩ : syracuseStep 4939613 = 1852355) B1852355
theorem B15392693 : Blo 381763 15392693 := bstep (se 5 (by rfl) ⟨721532, by rfl⟩ : syracuseStep 15392693 = 1443065) B1443065
theorem B384991 : Blo 381763 384991 := bstep (se 1 (by rfl) ⟨288743, by rfl⟩ : syracuseStep 384991 = 577487) B577487
theorem B974987 : Blo 381763 974987 := bstep (se 1 (by rfl) ⟨731240, by rfl⟩ : syracuseStep 974987 = 1462481) B1462481
theorem B647399 : Blo 381763 647399 := bstep (se 1 (by rfl) ⟨485549, by rfl⟩ : syracuseStep 647399 = 971099) B971099
theorem B385255 : Blo 381763 385255 := bstep (se 1 (by rfl) ⟨288941, by rfl⟩ : syracuseStep 385255 = 577883) B577883
theorem B2187593 : Blo 381763 2187593 := bstep (se 2 (by rfl) ⟨820347, by rfl⟩ : syracuseStep 2187593 = 1640695) B1640695
theorem B385407 : Blo 381763 385407 := bstep (se 1 (by rfl) ⟨289055, by rfl⟩ : syracuseStep 385407 = 578111) B578111
theorem B647561 : Blo 381763 647561 := bstep (se 2 (by rfl) ⟨242835, by rfl⟩ : syracuseStep 647561 = 485671) B485671
theorem B975311 : Blo 381763 975311 := bstep (se 1 (by rfl) ⟨731483, by rfl⟩ : syracuseStep 975311 = 1462967) B1462967
theorem B385487 : Blo 381763 385487 := bstep (se 1 (by rfl) ⟨289115, by rfl⟩ : syracuseStep 385487 = 578231) B578231
theorem B385639 : Blo 381763 385639 := bstep (se 1 (by rfl) ⟨289229, by rfl⟩ : syracuseStep 385639 = 578459) B578459
theorem B647993 : Blo 381763 647993 := bstep (se 2 (by rfl) ⟨242997, by rfl⟩ : syracuseStep 647993 = 485995) B485995
theorem B648047 : Blo 381763 648047 := bstep (se 1 (by rfl) ⟨486035, by rfl⟩ : syracuseStep 648047 = 972071) B972071
theorem B11035601 : Blo 381763 11035601 := bstep (se 2 (by rfl) ⟨4138350, by rfl⟩ : syracuseStep 11035601 = 8276701) B8276701
theorem B975827 : Blo 381763 975827 := bstep (se 1 (by rfl) ⟨731870, by rfl⟩ : syracuseStep 975827 = 1463741) B1463741
theorem B649039 : Blo 381763 649039 := bstep (se 1 (by rfl) ⟨486779, by rfl⟩ : syracuseStep 649039 = 973559) B973559
theorem B4352129 : Blo 381763 4352129 := bstep (se 2 (by rfl) ⟨1632048, by rfl⟩ : syracuseStep 4352129 = 3264097) B3264097
theorem B682219 : Blo 381763 682219 := bstep (se 1 (by rfl) ⟨511664, by rfl⟩ : syracuseStep 682219 = 1023329) B1023329
theorem B649451 : Blo 381763 649451 := bstep (se 1 (by rfl) ⟨487088, by rfl⟩ : syracuseStep 649451 = 974177) B974177
theorem B2189825 : Blo 381763 2189825 := bstep (se 2 (by rfl) ⟨821184, by rfl⟩ : syracuseStep 2189825 = 1642369) B1642369
theorem B3271205 : Blo 381763 3271205 := bstep (se 4 (by rfl) ⟨306675, by rfl⟩ : syracuseStep 3271205 = 613351) B613351
theorem B650281 : Blo 381763 650281 := bstep (se 2 (by rfl) ⟨243855, by rfl⟩ : syracuseStep 650281 = 487711) B487711
theorem B12414131 : Blo 381763 12414131 := bstep (se 1 (by rfl) ⟨9310598, by rfl⟩ : syracuseStep 12414131 = 18621197) B18621197
theorem B650423 : Blo 381763 650423 := bstep (se 1 (by rfl) ⟨487817, by rfl⟩ : syracuseStep 650423 = 975635) B975635
theorem B650747 : Blo 381763 650747 := bstep (se 1 (by rfl) ⟨488060, by rfl⟩ : syracuseStep 650747 = 976121) B976121
theorem B2191009 : Blo 381763 2191009 := bstep (se 2 (by rfl) ⟨821628, by rfl⟩ : syracuseStep 2191009 = 1643257) B1643257
theorem B487291 : Blo 381763 487291 := bstep (se 1 (by rfl) ⟨365468, by rfl⟩ : syracuseStep 487291 = 730937) B730937
theorem B8319347 : Blo 381763 8319347 := bstep (se 1 (by rfl) ⟨6239510, by rfl⟩ : syracuseStep 8319347 = 12479021) B12479021
theorem B4649957 : Blo 381763 4649957 := bstep (se 4 (by rfl) ⟨435933, by rfl⟩ : syracuseStep 4649957 = 871867) B871867
theorem B4355045 : Blo 381763 4355045 := bstep (se 4 (by rfl) ⟨408285, by rfl⟩ : syracuseStep 4355045 = 816571) B816571
theorem B15103361 : Blo 381763 15103361 := bstep (se 2 (by rfl) ⟨5663760, by rfl⟩ : syracuseStep 15103361 = 11327521) B11327521
theorem B2455433 : Blo 381763 2455433 := bstep (se 2 (by rfl) ⟨920787, by rfl⟩ : syracuseStep 2455433 = 1841575) B1841575
theorem B7403885 : Blo 381763 7403885 := bstep (se 3 (by rfl) ⟨1388228, by rfl⟩ : syracuseStep 7403885 = 2776457) B2776457
theorem B2455919 : Blo 381763 2455919 := bstep (se 1 (by rfl) ⟨1841939, by rfl⟩ : syracuseStep 2455919 = 3683879) B3683879
theorem B7371283 : Blo 381763 7371283 := bstep (se 1 (by rfl) ⟨5528462, by rfl⟩ : syracuseStep 7371283 = 11056925) B11056925
theorem B22084325 : Blo 381763 22084325 := bstep (se 4 (by rfl) ⟨2070405, by rfl⟩ : syracuseStep 22084325 = 4140811) B4140811
theorem B2194199 : Blo 381763 2194199 := bstep (se 1 (by rfl) ⟨1645649, by rfl⟩ : syracuseStep 2194199 = 3291299) B3291299
theorem B4127759 : Blo 381763 4127759 := bstep (se 1 (by rfl) ⟨3095819, by rfl⟩ : syracuseStep 4127759 = 6191639) B6191639
theorem B2849869 : Blo 381763 2849869 := bstep (se 3 (by rfl) ⟨534350, by rfl⟩ : syracuseStep 2849869 = 1068701) B1068701
theorem B2194883 : Blo 381763 2194883 := bstep (se 1 (by rfl) ⟨1646162, by rfl⟩ : syracuseStep 2194883 = 3292325) B3292325
theorem B1638269 : Blo 381763 1638269 := bstep (se 3 (by rfl) ⟨307175, by rfl⟩ : syracuseStep 1638269 = 614351) B614351
theorem B2752699 : Blo 381763 2752699 := bstep (se 1 (by rfl) ⟨2064524, by rfl⟩ : syracuseStep 2752699 = 4129049) B4129049
theorem B819391 : Blo 381763 819391 := bstep (se 1 (by rfl) ⟨614543, by rfl⟩ : syracuseStep 819391 = 1229087) B1229087
theorem B2916971 : Blo 381763 2916971 := bstep (se 1 (by rfl) ⟨2187728, by rfl⟩ : syracuseStep 2916971 = 4375457) B4375457
theorem B1377503 : Blo 381763 1377503 := bstep (se 1 (by rfl) ⟨1033127, by rfl⟩ : syracuseStep 1377503 = 2066255) B2066255
theorem B1311967 : Blo 381763 1311967 := bstep (se 1 (by rfl) ⟨983975, by rfl⟩ : syracuseStep 1311967 = 1967951) B1967951
theorem B820459 : Blo 381763 820459 := bstep (se 1 (by rfl) ⟨615344, by rfl⟩ : syracuseStep 820459 = 1230689) B1230689
theorem B5867113 : Blo 381763 5867113 := bstep (se 2 (by rfl) ⟨2200167, by rfl⟩ : syracuseStep 5867113 = 4400335) B4400335
theorem B3278555 : Blo 381763 3278555 := bstep (se 1 (by rfl) ⟨2458916, by rfl⟩ : syracuseStep 3278555 = 4917833) B4917833
theorem B460831 : Blo 381763 460831 := bstep (se 1 (by rfl) ⟨345623, by rfl⟩ : syracuseStep 460831 = 691247) B691247
theorem B821279 : Blo 381763 821279 := bstep (se 1 (by rfl) ⟨615959, by rfl⟩ : syracuseStep 821279 = 1231919) B1231919
theorem B461359 : Blo 381763 461359 := bstep (se 1 (by rfl) ⟨346019, by rfl⟩ : syracuseStep 461359 = 692039) B692039
theorem B822107 : Blo 381763 822107 := bstep (se 1 (by rfl) ⟨616580, by rfl⟩ : syracuseStep 822107 = 1233161) B1233161
theorem B920585 : Blo 381763 920585 := bstep (se 2 (by rfl) ⟨345219, by rfl⟩ : syracuseStep 920585 = 690439) B690439
theorem B2624633 : Blo 381763 2624633 := bstep (se 2 (by rfl) ⟨984237, by rfl⟩ : syracuseStep 2624633 = 1968475) B1968475
theorem B23662043 : Blo 381763 23662043 := bstep (se 1 (by rfl) ⟨17746532, by rfl⟩ : syracuseStep 23662043 = 35493065) B35493065
theorem B1936871 : Blo 381763 1936871 := bstep (se 1 (by rfl) ⟨1452653, by rfl⟩ : syracuseStep 1936871 = 2905307) B2905307
theorem B1248743 : Blo 381763 1248743 := bstep (se 1 (by rfl) ⟨936557, by rfl⟩ : syracuseStep 1248743 = 1873115) B1873115
theorem B2101115 : Blo 381763 2101115 := bstep (se 1 (by rfl) ⟨1575836, by rfl⟩ : syracuseStep 2101115 = 3151673) B3151673
theorem B692327 : Blo 381763 692327 := bstep (se 1 (by rfl) ⟨519245, by rfl⟩ : syracuseStep 692327 = 1038491) B1038491
theorem B3707171 : Blo 381763 3707171 := bstep (se 1 (by rfl) ⟨2780378, by rfl⟩ : syracuseStep 3707171 = 5560757) B5560757
theorem B1839671 : Blo 381763 1839671 := bstep (se 1 (by rfl) ⟨1379753, by rfl⟩ : syracuseStep 1839671 = 2759507) B2759507
theorem B1938167 : Blo 381763 1938167 := bstep (se 1 (by rfl) ⟨1453625, by rfl⟩ : syracuseStep 1938167 = 2907251) B2907251
theorem B430843 : Blo 381763 430843 := bstep (se 1 (by rfl) ⟨323132, by rfl⟩ : syracuseStep 430843 = 646265) B646265
theorem B2921345 : Blo 381763 2921345 := bstep (se 2 (by rfl) ⟨1095504, by rfl⟩ : syracuseStep 2921345 = 2191009) B2191009
theorem B6526007 : Blo 381763 6526007 := bstep (se 1 (by rfl) ⟨4894505, by rfl⟩ : syracuseStep 6526007 = 9789011) B9789011
theorem B431599 : Blo 381763 431599 := bstep (se 1 (by rfl) ⟨323699, by rfl⟩ : syracuseStep 431599 = 647399) B647399
theorem B431707 : Blo 381763 431707 := bstep (se 1 (by rfl) ⟨323780, by rfl⟩ : syracuseStep 431707 = 647561) B647561
theorem B431995 : Blo 381763 431995 := bstep (se 1 (by rfl) ⟨323996, by rfl⟩ : syracuseStep 431995 = 647993) B647993
theorem B3938179 : Blo 381763 3938179 := bstep (se 1 (by rfl) ⟨2953634, by rfl⟩ : syracuseStep 3938179 = 5907269) B5907269
theorem B432031 : Blo 381763 432031 := bstep (se 1 (by rfl) ⟨324023, by rfl⟩ : syracuseStep 432031 = 648047) B648047
theorem B3676265 : Blo 381763 3676265 := bstep (se 2 (by rfl) ⟨1378599, by rfl⟩ : syracuseStep 3676265 = 2757199) B2757199
theorem B923987 : Blo 381763 923987 := bstep (se 1 (by rfl) ⟨692990, by rfl⟩ : syracuseStep 923987 = 1385981) B1385981
theorem B3283577 : Blo 381763 3283577 := bstep (se 2 (by rfl) ⟨1231341, by rfl⟩ : syracuseStep 3283577 = 2462683) B2462683
theorem B2759447 : Blo 381763 2759447 := bstep (se 1 (by rfl) ⟨2069585, by rfl⟩ : syracuseStep 2759447 = 4139171) B4139171
theorem B432967 : Blo 381763 432967 := bstep (se 1 (by rfl) ⟨324725, by rfl⟩ : syracuseStep 432967 = 649451) B649451
theorem B1645703 : Blo 381763 1645703 := bstep (se 1 (by rfl) ⟨1234277, by rfl⟩ : syracuseStep 1645703 = 2468555) B2468555
theorem B859463 : Blo 381763 859463 := bstep (se 1 (by rfl) ⟨644597, by rfl⟩ : syracuseStep 859463 = 1289195) B1289195
theorem B859499 : Blo 381763 859499 := bstep (se 1 (by rfl) ⟨644624, by rfl⟩ : syracuseStep 859499 = 1289249) B1289249
theorem B433615 : Blo 381763 433615 := bstep (se 1 (by rfl) ⟨325211, by rfl⟩ : syracuseStep 433615 = 650423) B650423
theorem B859625 : Blo 381763 859625 := bstep (se 2 (by rfl) ⟨322359, by rfl⟩ : syracuseStep 859625 = 644719) B644719
theorem B1842745 : Blo 381763 1842745 := bstep (se 2 (by rfl) ⟨691029, by rfl⟩ : syracuseStep 1842745 = 1382059) B1382059
theorem B2072137 : Blo 381763 2072137 := bstep (se 2 (by rfl) ⟨777051, by rfl⟩ : syracuseStep 2072137 = 1554103) B1554103
theorem B859769 : Blo 381763 859769 := bstep (se 2 (by rfl) ⟨322413, by rfl⟩ : syracuseStep 859769 = 644827) B644827
theorem B433831 : Blo 381763 433831 := bstep (se 1 (by rfl) ⟨325373, by rfl⟩ : syracuseStep 433831 = 650747) B650747
theorem B1941245 : Blo 381763 1941245 := bstep (se 3 (by rfl) ⟨363983, by rfl⟩ : syracuseStep 1941245 = 727967) B727967
theorem B5611373 : Blo 381763 5611373 := bstep (se 3 (by rfl) ⟨1052132, by rfl⟩ : syracuseStep 5611373 = 2104265) B2104265
theorem B44965813 : Blo 381763 44965813 := bstep (se 5 (by rfl) ⟨2107772, by rfl⟩ : syracuseStep 44965813 = 4215545) B4215545
theorem B5546231 : Blo 381763 5546231 := bstep (se 1 (by rfl) ⟨4159673, by rfl⟩ : syracuseStep 5546231 = 8319347) B8319347
theorem B860471 : Blo 381763 860471 := bstep (se 1 (by rfl) ⟨645353, by rfl⟩ : syracuseStep 860471 = 1290707) B1290707
theorem B3154301 : Blo 381763 3154301 := bstep (se 3 (by rfl) ⟨591431, by rfl⟩ : syracuseStep 3154301 = 1182863) B1182863
theorem B3154565 : Blo 381763 3154565 := bstep (se 4 (by rfl) ⟨295740, by rfl⟩ : syracuseStep 3154565 = 591481) B591481
theorem B1843975 : Blo 381763 1843975 := bstep (se 1 (by rfl) ⟨1382981, by rfl⟩ : syracuseStep 1843975 = 2765963) B2765963
theorem B729911 : Blo 381763 729911 := bstep (se 1 (by rfl) ⟨547433, by rfl⟩ : syracuseStep 729911 = 1094867) B1094867
theorem B1647479 : Blo 381763 1647479 := bstep (se 1 (by rfl) ⟨1235609, by rfl⟩ : syracuseStep 1647479 = 2471219) B2471219
theorem B10068907 : Blo 381763 10068907 := bstep (se 1 (by rfl) ⟨7551680, by rfl⟩ : syracuseStep 10068907 = 15103361) B15103361
theorem B861497 : Blo 381763 861497 := bstep (se 2 (by rfl) ⟨323061, by rfl⟩ : syracuseStep 861497 = 646123) B646123
theorem B2762045 : Blo 381763 2762045 := bstep (se 3 (by rfl) ⟨517883, by rfl⟩ : syracuseStep 2762045 = 1035767) B1035767
theorem B861767 : Blo 381763 861767 := bstep (se 1 (by rfl) ⟨646325, by rfl⟩ : syracuseStep 861767 = 1292651) B1292651
theorem B861947 : Blo 381763 861947 := bstep (se 1 (by rfl) ⟨646460, by rfl⟩ : syracuseStep 861947 = 1292921) B1292921
theorem B14722883 : Blo 381763 14722883 := bstep (se 1 (by rfl) ⟨11042162, by rfl⟩ : syracuseStep 14722883 = 22084325) B22084325
theorem B731035 : Blo 381763 731035 := bstep (se 1 (by rfl) ⟨548276, by rfl⟩ : syracuseStep 731035 = 1096553) B1096553
theorem B862235 : Blo 381763 862235 := bstep (se 1 (by rfl) ⟨646676, by rfl⟩ : syracuseStep 862235 = 1293353) B1293353
theorem B731369 : Blo 381763 731369 := bstep (se 2 (by rfl) ⟨274263, by rfl⟩ : syracuseStep 731369 = 548527) B548527
theorem B1092179 : Blo 381763 1092179 := bstep (se 1 (by rfl) ⟨819134, by rfl⟩ : syracuseStep 1092179 = 1638269) B1638269
theorem B3287951 : Blo 381763 3287951 := bstep (se 1 (by rfl) ⟨2465963, by rfl⟩ : syracuseStep 3287951 = 4931927) B4931927
theorem B2468987 : Blo 381763 2468987 := bstep (se 1 (by rfl) ⟨1851740, by rfl⟩ : syracuseStep 2468987 = 3703481) B3703481
theorem B1289465 : Blo 381763 1289465 := bstep (se 2 (by rfl) ⟨483549, by rfl⟩ : syracuseStep 1289465 = 967099) B967099
theorem B3681611 : Blo 381763 3681611 := bstep (se 1 (by rfl) ⟨2761208, by rfl⟩ : syracuseStep 3681611 = 5522417) B5522417
theorem B1289627 : Blo 381763 1289627 := bstep (se 1 (by rfl) ⟨967220, by rfl⟩ : syracuseStep 1289627 = 1934441) B1934441
theorem B601499 : Blo 381763 601499 := bstep (se 1 (by rfl) ⟨451124, by rfl⟩ : syracuseStep 601499 = 902249) B902249
theorem B863711 : Blo 381763 863711 := bstep (se 1 (by rfl) ⟨647783, by rfl⟩ : syracuseStep 863711 = 1295567) B1295567
theorem B2174471 : Blo 381763 2174471 := bstep (se 1 (by rfl) ⟨1630853, by rfl⟩ : syracuseStep 2174471 = 3261707) B3261707
theorem B1289735 : Blo 381763 1289735 := bstep (se 1 (by rfl) ⟨967301, by rfl⟩ : syracuseStep 1289735 = 1934603) B1934603
theorem B3288701 : Blo 381763 3288701 := bstep (se 3 (by rfl) ⟨616631, by rfl⟩ : syracuseStep 3288701 = 1233263) B1233263
theorem B863927 : Blo 381763 863927 := bstep (se 1 (by rfl) ⟨647945, by rfl⟩ : syracuseStep 863927 = 1295891) B1295891
theorem B3518333 : Blo 381763 3518333 := bstep (se 3 (by rfl) ⟨659687, by rfl⟩ : syracuseStep 3518333 = 1319375) B1319375
theorem B7221163 : Blo 381763 7221163 := bstep (se 1 (by rfl) ⟨5415872, by rfl⟩ : syracuseStep 7221163 = 10831745) B10831745
theorem B100642823 : Blo 381763 100642823 := bstep (se 1 (by rfl) ⟨75482117, by rfl⟩ : syracuseStep 100642823 = 150964235) B150964235
theorem B1454219 : Blo 381763 1454219 := bstep (se 1 (by rfl) ⟨1090664, by rfl⟩ : syracuseStep 1454219 = 2181329) B2181329
theorem B1225115 : Blo 381763 1225115 := bstep (se 1 (by rfl) ⟨918836, by rfl⟩ : syracuseStep 1225115 = 1837673) B1837673
theorem B864719 : Blo 381763 864719 := bstep (se 1 (by rfl) ⟨648539, by rfl⟩ : syracuseStep 864719 = 1297079) B1297079
theorem B1290815 : Blo 381763 1290815 := bstep (se 1 (by rfl) ⟨968111, by rfl⟩ : syracuseStep 1290815 = 1936223) B1936223
theorem B1553003 : Blo 381763 1553003 := bstep (se 1 (by rfl) ⟨1164752, by rfl⟩ : syracuseStep 1553003 = 2329505) B2329505
theorem B2765735 : Blo 381763 2765735 := bstep (se 1 (by rfl) ⟨2074301, by rfl⟩ : syracuseStep 2765735 = 4148603) B4148603
theorem B865385 : Blo 381763 865385 := bstep (se 2 (by rfl) ⟨324519, by rfl⟩ : syracuseStep 865385 = 649039) B649039
theorem B866015 : Blo 381763 866015 := bstep (se 1 (by rfl) ⟨649511, by rfl⟩ : syracuseStep 866015 = 1299023) B1299023
theorem B866375 : Blo 381763 866375 := bstep (se 1 (by rfl) ⟨649781, by rfl⟩ : syracuseStep 866375 = 1299563) B1299563
theorem B5552225 : Blo 381763 5552225 := bstep (se 2 (by rfl) ⟨2082084, by rfl⟩ : syracuseStep 5552225 = 4164169) B4164169
theorem B2177387 : Blo 381763 2177387 := bstep (se 1 (by rfl) ⟨1633040, by rfl⟩ : syracuseStep 2177387 = 3266081) B3266081
theorem B867041 : Blo 381763 867041 := bstep (se 2 (by rfl) ⟨325140, by rfl⟩ : syracuseStep 867041 = 650281) B650281
theorem B2177887 : Blo 381763 2177887 := bstep (se 1 (by rfl) ⟨1633415, by rfl⟩ : syracuseStep 2177887 = 3266831) B3266831
theorem B867239 : Blo 381763 867239 := bstep (se 1 (by rfl) ⟨650429, by rfl⟩ : syracuseStep 867239 = 1300859) B1300859
theorem B1096679 : Blo 381763 1096679 := bstep (se 1 (by rfl) ⟨822509, by rfl⟩ : syracuseStep 1096679 = 1645019) B1645019
theorem B867419 : Blo 381763 867419 := bstep (se 1 (by rfl) ⟨650564, by rfl⟩ : syracuseStep 867419 = 1301129) B1301129
theorem B2080079 : Blo 381763 2080079 := bstep (se 1 (by rfl) ⟨1560059, by rfl⟩ : syracuseStep 2080079 = 3120119) B3120119
theorem B572879 : Blo 381763 572879 := bstep (se 1 (by rfl) ⟨429659, by rfl⟩ : syracuseStep 572879 = 859319) B859319
theorem B573263 : Blo 381763 573263 := bstep (se 1 (by rfl) ⟨429947, by rfl⟩ : syracuseStep 573263 = 859895) B859895
theorem B3293075 : Blo 381763 3293075 := bstep (se 1 (by rfl) ⟨2469806, by rfl⟩ : syracuseStep 3293075 = 4939613) B4939613
theorem B573383 : Blo 381763 573383 := bstep (se 1 (by rfl) ⟨430037, by rfl⟩ : syracuseStep 573383 = 860075) B860075
theorem B1458395 : Blo 381763 1458395 := bstep (se 1 (by rfl) ⟨1093796, by rfl⟩ : syracuseStep 1458395 = 2187593) B2187593
theorem B1458425 : Blo 381763 1458425 := bstep (se 2 (by rfl) ⟨546909, by rfl⟩ : syracuseStep 1458425 = 1093819) B1093819
theorem B573743 : Blo 381763 573743 := bstep (se 1 (by rfl) ⟨430307, by rfl⟩ : syracuseStep 573743 = 860615) B860615
theorem B573983 : Blo 381763 573983 := bstep (se 1 (by rfl) ⟨430487, by rfl⟩ : syracuseStep 573983 = 860975) B860975
theorem B7357067 : Blo 381763 7357067 := bstep (se 1 (by rfl) ⟨5517800, by rfl⟩ : syracuseStep 7357067 = 11035601) B11035601
theorem B574655 : Blo 381763 574655 := bstep (se 1 (by rfl) ⟨430991, by rfl⟩ : syracuseStep 574655 = 861983) B861983
theorem B574799 : Blo 381763 574799 := bstep (se 1 (by rfl) ⟨431099, by rfl⟩ : syracuseStep 574799 = 862199) B862199
theorem B4441439 : Blo 381763 4441439 := bstep (se 1 (by rfl) ⟨3331079, by rfl⟩ : syracuseStep 4441439 = 6662159) B6662159
theorem B574889 : Blo 381763 574889 := bstep (se 2 (by rfl) ⟨215583, by rfl⟩ : syracuseStep 574889 = 431167) B431167
theorem B2901419 : Blo 381763 2901419 := bstep (se 1 (by rfl) ⟨2176064, by rfl⟩ : syracuseStep 2901419 = 4352129) B4352129
theorem B575039 : Blo 381763 575039 := bstep (se 1 (by rfl) ⟨431279, by rfl⟩ : syracuseStep 575039 = 862559) B862559
theorem B575081 : Blo 381763 575081 := bstep (se 2 (by rfl) ⟨215655, by rfl⟩ : syracuseStep 575081 = 431311) B431311
theorem B1459883 : Blo 381763 1459883 := bstep (se 1 (by rfl) ⟨1094912, by rfl⟩ : syracuseStep 1459883 = 2189825) B2189825
theorem B2180803 : Blo 381763 2180803 := bstep (se 1 (by rfl) ⟨1635602, by rfl⟩ : syracuseStep 2180803 = 3271205) B3271205
theorem B575519 : Blo 381763 575519 := bstep (se 1 (by rfl) ⟨431639, by rfl⟩ : syracuseStep 575519 = 863279) B863279
theorem B1951775 : Blo 381763 1951775 := bstep (se 1 (by rfl) ⟨1463831, by rfl⟩ : syracuseStep 1951775 = 2927663) B2927663
theorem B8276087 : Blo 381763 8276087 := bstep (se 1 (by rfl) ⟨6207065, by rfl⟩ : syracuseStep 8276087 = 12414131) B12414131
theorem B1296539 : Blo 381763 1296539 := bstep (se 1 (by rfl) ⟨972404, by rfl⟩ : syracuseStep 1296539 = 1944809) B1944809
theorem B575711 : Blo 381763 575711 := bstep (se 1 (by rfl) ⟨431783, by rfl⟩ : syracuseStep 575711 = 863567) B863567
theorem B575771 : Blo 381763 575771 := bstep (se 1 (by rfl) ⟨431828, by rfl⟩ : syracuseStep 575771 = 863657) B863657
theorem B1460537 : Blo 381763 1460537 := bstep (se 2 (by rfl) ⟨547701, by rfl⟩ : syracuseStep 1460537 = 1095403) B1095403
theorem B1296809 : Blo 381763 1296809 := bstep (se 2 (by rfl) ⟨486303, by rfl⟩ : syracuseStep 1296809 = 972607) B972607
theorem B576095 : Blo 381763 576095 := bstep (se 1 (by rfl) ⟨432071, by rfl⟩ : syracuseStep 576095 = 864143) B864143
theorem B576377 : Blo 381763 576377 := bstep (se 2 (by rfl) ⟨216141, by rfl⟩ : syracuseStep 576377 = 432283) B432283
theorem B576425 : Blo 381763 576425 := bstep (se 2 (by rfl) ⟨216159, by rfl⟩ : syracuseStep 576425 = 432319) B432319
theorem B1297403 : Blo 381763 1297403 := bstep (se 1 (by rfl) ⟨973052, by rfl⟩ : syracuseStep 1297403 = 1946105) B1946105
theorem B576575 : Blo 381763 576575 := bstep (se 1 (by rfl) ⟨432431, by rfl⟩ : syracuseStep 576575 = 864863) B864863
theorem B3099971 : Blo 381763 3099971 := bstep (se 1 (by rfl) ⟨2324978, by rfl⟩ : syracuseStep 3099971 = 4649957) B4649957
theorem B2903363 : Blo 381763 2903363 := bstep (se 1 (by rfl) ⟨2177522, by rfl⟩ : syracuseStep 2903363 = 4355045) B4355045
theorem B577127 : Blo 381763 577127 := bstep (se 1 (by rfl) ⟨432845, by rfl⟩ : syracuseStep 577127 = 865691) B865691
theorem B577511 : Blo 381763 577511 := bstep (se 1 (by rfl) ⟨433133, by rfl⟩ : syracuseStep 577511 = 866267) B866267
theorem B577631 : Blo 381763 577631 := bstep (se 1 (by rfl) ⟨433223, by rfl⟩ : syracuseStep 577631 = 866447) B866447
theorem B577643 : Blo 381763 577643 := bstep (se 1 (by rfl) ⟨433232, by rfl⟩ : syracuseStep 577643 = 866465) B866465
theorem B577691 : Blo 381763 577691 := bstep (se 1 (by rfl) ⟨433268, by rfl⟩ : syracuseStep 577691 = 866537) B866537
theorem B4935923 : Blo 381763 4935923 := bstep (se 1 (by rfl) ⟨3701942, by rfl⟩ : syracuseStep 4935923 = 7403885) B7403885
theorem B1462799 : Blo 381763 1462799 := bstep (se 1 (by rfl) ⟨1097099, by rfl⟩ : syracuseStep 1462799 = 2194199) B2194199
theorem B1692269 : Blo 381763 1692269 := bstep (se 3 (by rfl) ⟨317300, by rfl⟩ : syracuseStep 1692269 = 634601) B634601
theorem B381787 : Blo 381763 381787 := bstep (se 1 (by rfl) ⟨286340, by rfl⟩ : syracuseStep 381787 = 572681) B572681
theorem B381855 : Blo 381763 381855 := bstep (se 1 (by rfl) ⟨286391, by rfl⟩ : syracuseStep 381855 = 572783) B572783
theorem B1463255 : Blo 381763 1463255 := bstep (se 1 (by rfl) ⟨1097441, by rfl⟩ : syracuseStep 1463255 = 2194883) B2194883
theorem B381935 : Blo 381763 381935 := bstep (se 1 (by rfl) ⟨286451, by rfl⟩ : syracuseStep 381935 = 572903) B572903
theorem B578543 : Blo 381763 578543 := bstep (se 1 (by rfl) ⟨433907, by rfl⟩ : syracuseStep 578543 = 867815) B867815
theorem B382023 : Blo 381763 382023 := bstep (se 1 (by rfl) ⟨286517, by rfl⟩ : syracuseStep 382023 = 573035) B573035
theorem B41047181 : Blo 381763 41047181 := bstep (se 3 (by rfl) ⟨7696346, by rfl⟩ : syracuseStep 41047181 = 15392693) B15392693
theorem B382107 : Blo 381763 382107 := bstep (se 1 (by rfl) ⟨286580, by rfl⟩ : syracuseStep 382107 = 573161) B573161
theorem B382203 : Blo 381763 382203 := bstep (se 1 (by rfl) ⟨286652, by rfl⟩ : syracuseStep 382203 = 573305) B573305
theorem B382271 : Blo 381763 382271 := bstep (se 1 (by rfl) ⟨286703, by rfl⟩ : syracuseStep 382271 = 573407) B573407
theorem B13981081 : Blo 381763 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B382439 : Blo 381763 382439 := bstep (se 1 (by rfl) ⟨286829, by rfl⟩ : syracuseStep 382439 = 573659) B573659
theorem B644591 : Blo 381763 644591 := bstep (se 1 (by rfl) ⟨483443, by rfl⟩ : syracuseStep 644591 = 966887) B966887
theorem B382447 : Blo 381763 382447 := bstep (se 1 (by rfl) ⟨286835, by rfl⟩ : syracuseStep 382447 = 573671) B573671
theorem B382555 : Blo 381763 382555 := bstep (se 1 (by rfl) ⟨286916, by rfl⟩ : syracuseStep 382555 = 573833) B573833
theorem B972425 : Blo 381763 972425 := bstep (se 2 (by rfl) ⟨364659, by rfl⟩ : syracuseStep 972425 = 729319) B729319
theorem B382619 : Blo 381763 382619 := bstep (se 1 (by rfl) ⟨286964, by rfl⟩ : syracuseStep 382619 = 573929) B573929
theorem B1463975 : Blo 381763 1463975 := bstep (se 1 (by rfl) ⟨1097981, by rfl⟩ : syracuseStep 1463975 = 2195963) B2195963
theorem B382703 : Blo 381763 382703 := bstep (se 1 (by rfl) ⟨287027, by rfl⟩ : syracuseStep 382703 = 574055) B574055
theorem B644935 : Blo 381763 644935 := bstep (se 1 (by rfl) ⟨483701, by rfl⟩ : syracuseStep 644935 = 967403) B967403
theorem B382791 : Blo 381763 382791 := bstep (se 1 (by rfl) ⟨287093, by rfl⟩ : syracuseStep 382791 = 574187) B574187
theorem B382811 : Blo 381763 382811 := bstep (se 1 (by rfl) ⟨287108, by rfl⟩ : syracuseStep 382811 = 574217) B574217
theorem B645023 : Blo 381763 645023 := bstep (se 1 (by rfl) ⟨483767, by rfl⟩ : syracuseStep 645023 = 967535) B967535
theorem B382879 : Blo 381763 382879 := bstep (se 1 (by rfl) ⟨287159, by rfl⟩ : syracuseStep 382879 = 574319) B574319
theorem B972769 : Blo 381763 972769 := bstep (se 2 (by rfl) ⟨364788, by rfl⟩ : syracuseStep 972769 = 729577) B729577
theorem B383047 : Blo 381763 383047 := bstep (se 1 (by rfl) ⟨287285, by rfl⟩ : syracuseStep 383047 = 574571) B574571
theorem B383207 : Blo 381763 383207 := bstep (se 1 (by rfl) ⟨287405, by rfl⟩ : syracuseStep 383207 = 574811) B574811
theorem B383391 : Blo 381763 383391 := bstep (se 1 (by rfl) ⟨287543, by rfl⟩ : syracuseStep 383391 = 575087) B575087
theorem B383439 : Blo 381763 383439 := bstep (se 1 (by rfl) ⟨287579, by rfl⟩ : syracuseStep 383439 = 575159) B575159
theorem B383463 : Blo 381763 383463 := bstep (se 1 (by rfl) ⟨287597, by rfl⟩ : syracuseStep 383463 = 575195) B575195
theorem B383579 : Blo 381763 383579 := bstep (se 1 (by rfl) ⟨287684, by rfl⟩ : syracuseStep 383579 = 575369) B575369
theorem B383647 : Blo 381763 383647 := bstep (se 1 (by rfl) ⟨287735, by rfl⟩ : syracuseStep 383647 = 575471) B575471
theorem B383815 : Blo 381763 383815 := bstep (se 1 (by rfl) ⟨287861, by rfl⟩ : syracuseStep 383815 = 575723) B575723
theorem B383855 : Blo 381763 383855 := bstep (se 1 (by rfl) ⟨287891, by rfl⟩ : syracuseStep 383855 = 575783) B575783
theorem B383911 : Blo 381763 383911 := bstep (se 1 (by rfl) ⟨287933, by rfl⟩ : syracuseStep 383911 = 575867) B575867
theorem B384091 : Blo 381763 384091 := bstep (se 1 (by rfl) ⟨288068, by rfl⟩ : syracuseStep 384091 = 576137) B576137
theorem B384207 : Blo 381763 384207 := bstep (se 1 (by rfl) ⟨288155, by rfl⟩ : syracuseStep 384207 = 576311) B576311
theorem B384231 : Blo 381763 384231 := bstep (se 1 (by rfl) ⟨288173, by rfl⟩ : syracuseStep 384231 = 576347) B576347
theorem B384327 : Blo 381763 384327 := bstep (se 1 (by rfl) ⟨288245, by rfl⟩ : syracuseStep 384327 = 576491) B576491
theorem B384463 : Blo 381763 384463 := bstep (se 1 (by rfl) ⟨288347, by rfl⟩ : syracuseStep 384463 = 576695) B576695
theorem B4677097 : Blo 381763 4677097 := bstep (se 2 (by rfl) ⟨1753911, by rfl⟩ : syracuseStep 4677097 = 3507823) B3507823
theorem B384623 : Blo 381763 384623 := bstep (se 1 (by rfl) ⟨288467, by rfl⟩ : syracuseStep 384623 = 576935) B576935
theorem B384679 : Blo 381763 384679 := bstep (se 1 (by rfl) ⟨288509, by rfl⟩ : syracuseStep 384679 = 577019) B577019
theorem B384743 : Blo 381763 384743 := bstep (se 1 (by rfl) ⟨288557, by rfl⟩ : syracuseStep 384743 = 577115) B577115
theorem B384799 : Blo 381763 384799 := bstep (se 1 (by rfl) ⟨288599, by rfl⟩ : syracuseStep 384799 = 577199) B577199
theorem B384879 : Blo 381763 384879 := bstep (se 1 (by rfl) ⟨288659, by rfl⟩ : syracuseStep 384879 = 577319) B577319
theorem B384935 : Blo 381763 384935 := bstep (se 1 (by rfl) ⟨288701, by rfl⟩ : syracuseStep 384935 = 577403) B577403
theorem B385215 : Blo 381763 385215 := bstep (se 1 (by rfl) ⟨288911, by rfl⟩ : syracuseStep 385215 = 577823) B577823
theorem B778447 : Blo 381763 778447 := bstep (se 1 (by rfl) ⟨583835, by rfl⟩ : syracuseStep 778447 = 1167671) B1167671
theorem B385231 : Blo 381763 385231 := bstep (se 1 (by rfl) ⟨288923, by rfl⟩ : syracuseStep 385231 = 577847) B577847
theorem B385279 : Blo 381763 385279 := bstep (se 1 (by rfl) ⟨288959, by rfl⟩ : syracuseStep 385279 = 577919) B577919
theorem B385327 : Blo 381763 385327 := bstep (se 1 (by rfl) ⟨288995, by rfl⟩ : syracuseStep 385327 = 577991) B577991
theorem B909625 : Blo 381763 909625 := bstep (se 2 (by rfl) ⟨341109, by rfl⟩ : syracuseStep 909625 = 682219) B682219
theorem B385563 : Blo 381763 385563 := bstep (se 1 (by rfl) ⟨289172, by rfl⟩ : syracuseStep 385563 = 578345) B578345
theorem B385567 : Blo 381763 385567 := bstep (se 1 (by rfl) ⟨289175, by rfl⟩ : syracuseStep 385567 = 578351) B578351
theorem B2908709 : Blo 381763 2908709 := bstep (se 4 (by rfl) ⟨272691, by rfl⟩ : syracuseStep 2908709 = 545383) B545383
theorem B385647 : Blo 381763 385647 := bstep (se 1 (by rfl) ⟨289235, by rfl⟩ : syracuseStep 385647 = 578471) B578471
theorem B385703 : Blo 381763 385703 := bstep (se 1 (by rfl) ⟨289277, by rfl⟩ : syracuseStep 385703 = 578555) B578555
theorem B385743 : Blo 381763 385743 := bstep (se 1 (by rfl) ⟨289307, by rfl⟩ : syracuseStep 385743 = 578615) B578615
theorem B1630955 : Blo 381763 1630955 := bstep (se 1 (by rfl) ⟨1223216, by rfl⟩ : syracuseStep 1630955 = 2446433) B2446433
theorem B196338887 : Blo 381763 196338887 := bstep (se 1 (by rfl) ⟨147254165, by rfl⟩ : syracuseStep 196338887 = 294508331) B294508331
theorem B648695 : Blo 381763 648695 := bstep (se 1 (by rfl) ⟨486521, by rfl⟩ : syracuseStep 648695 = 973043) B973043
theorem B1631897 : Blo 381763 1631897 := bstep (se 2 (by rfl) ⟨611961, by rfl⟩ : syracuseStep 1631897 = 1223923) B1223923
theorem B3106457 : Blo 381763 3106457 := bstep (se 2 (by rfl) ⟨1164921, by rfl⟩ : syracuseStep 3106457 = 2329843) B2329843
theorem B616427 : Blo 381763 616427 := bstep (se 1 (by rfl) ⟨462320, by rfl⟩ : syracuseStep 616427 = 924641) B924641
theorem B6547877 : Blo 381763 6547877 := bstep (se 4 (by rfl) ⟨613863, by rfl⟩ : syracuseStep 6547877 = 1227727) B1227727
theorem B616939 : Blo 381763 616939 := bstep (se 1 (by rfl) ⟨462704, by rfl⟩ : syracuseStep 616939 = 925409) B925409
theorem B649721 : Blo 381763 649721 := bstep (se 2 (by rfl) ⟨243645, by rfl⟩ : syracuseStep 649721 = 487291) B487291
theorem B649775 : Blo 381763 649775 := bstep (se 1 (by rfl) ⟨487331, by rfl⟩ : syracuseStep 649775 = 974663) B974663
theorem B649991 : Blo 381763 649991 := bstep (se 1 (by rfl) ⟨487493, by rfl⟩ : syracuseStep 649991 = 974987) B974987
theorem B650207 : Blo 381763 650207 := bstep (se 1 (by rfl) ⟨487655, by rfl⟩ : syracuseStep 650207 = 975311) B975311
theorem B15199301 : Blo 381763 15199301 := bstep (se 4 (by rfl) ⟨1424934, by rfl⟩ : syracuseStep 15199301 = 2849869) B2849869
theorem B650551 : Blo 381763 650551 := bstep (se 1 (by rfl) ⟨487913, by rfl⟩ : syracuseStep 650551 = 975827) B975827
theorem B1470935 : Blo 381763 1470935 := bstep (se 1 (by rfl) ⟨1103201, by rfl⟩ : syracuseStep 1470935 = 2206403) B2206403
theorem B2913083 : Blo 381763 2913083 := bstep (se 1 (by rfl) ⟨2184812, by rfl⟩ : syracuseStep 2913083 = 4369625) B4369625
theorem B817067 : Blo 381763 817067 := bstep (se 1 (by rfl) ⟨612800, by rfl⟩ : syracuseStep 817067 = 1225601) B1225601
theorem B9828377 : Blo 381763 9828377 := bstep (se 2 (by rfl) ⟨3685641, by rfl⟩ : syracuseStep 9828377 = 7371283) B7371283
theorem B3274829 : Blo 381763 3274829 := bstep (se 3 (by rfl) ⟨614030, by rfl⟩ : syracuseStep 3274829 = 1228061) B1228061
theorem B2652763 : Blo 381763 2652763 := bstep (se 1 (by rfl) ⟨1989572, by rfl⟩ : syracuseStep 2652763 = 3979145) B3979145
theorem B1636955 : Blo 381763 1636955 := bstep (se 1 (by rfl) ⟨1227716, by rfl⟩ : syracuseStep 1636955 = 2455433) B2455433
theorem B1637279 : Blo 381763 1637279 := bstep (se 1 (by rfl) ⟨1227959, by rfl⟩ : syracuseStep 1637279 = 2455919) B2455919
theorem B2915513 : Blo 381763 2915513 := bstep (se 2 (by rfl) ⟨1093317, by rfl⟩ : syracuseStep 2915513 = 2186635) B2186635
theorem B2751839 : Blo 381763 2751839 := bstep (se 1 (by rfl) ⟨2063879, by rfl⟩ : syracuseStep 2751839 = 4127759) B4127759
theorem B3670265 : Blo 381763 3670265 := bstep (se 2 (by rfl) ⟨1376349, by rfl⟩ : syracuseStep 3670265 = 2752699) B2752699
theorem B1212833 : Blo 381763 1212833 := bstep (se 2 (by rfl) ⟨454812, by rfl⟩ : syracuseStep 1212833 = 909625) B909625
theorem B918335 : Blo 381763 918335 := bstep (se 1 (by rfl) ⟨688751, by rfl⟩ : syracuseStep 918335 = 1377503) B1377503
theorem B1934279 : Blo 381763 1934279 := bstep (se 1 (by rfl) ⟨1450709, by rfl⟩ : syracuseStep 1934279 = 2901419) B2901419
theorem B2458633 : Blo 381763 2458633 := bstep (se 2 (by rfl) ⟨921987, by rfl⟩ : syracuseStep 2458633 = 1843975) B1843975
theorem B2066647 : Blo 381763 2066647 := bstep (se 1 (by rfl) ⟨1549985, by rfl⟩ : syracuseStep 2066647 = 3099971) B3099971
theorem B1935575 : Blo 381763 1935575 := bstep (se 1 (by rfl) ⟨1451681, by rfl⟩ : syracuseStep 1935575 = 2903363) B2903363
theorem B2460581 : Blo 381763 2460581 := bstep (se 4 (by rfl) ⟨230679, by rfl⟩ : syracuseStep 2460581 = 461359) B461359
theorem B27364787 : Blo 381763 27364787 := bstep (se 1 (by rfl) ⟨20523590, by rfl⟩ : syracuseStep 27364787 = 41047181) B41047181
theorem B429727 : Blo 381763 429727 := bstep (se 1 (by rfl) ⟨322295, by rfl⟩ : syracuseStep 429727 = 644591) B644591
theorem B430015 : Blo 381763 430015 := bstep (se 1 (by rfl) ⟨322511, by rfl⟩ : syracuseStep 430015 = 645023) B645023
theorem B3740915 : Blo 381763 3740915 := bstep (se 1 (by rfl) ⟨2805686, by rfl⟩ : syracuseStep 3740915 = 5611373) B5611373
theorem B2102867 : Blo 381763 2102867 := bstep (se 1 (by rfl) ⟨1577150, by rfl⟩ : syracuseStep 2102867 = 3154301) B3154301
theorem B1939139 : Blo 381763 1939139 := bstep (se 1 (by rfl) ⟨1454354, by rfl⟩ : syracuseStep 1939139 = 2908709) B2908709
theorem B2103043 : Blo 381763 2103043 := bstep (se 1 (by rfl) ⟨1577282, by rfl⟩ : syracuseStep 2103043 = 3154565) B3154565
theorem B1841363 : Blo 381763 1841363 := bstep (se 1 (by rfl) ⟨1381022, by rfl⟩ : syracuseStep 1841363 = 2762045) B2762045
theorem B2463965 : Blo 381763 2463965 := bstep (se 3 (by rfl) ⟨461993, by rfl⟩ : syracuseStep 2463965 = 923987) B923987
theorem B432463 : Blo 381763 432463 := bstep (se 1 (by rfl) ⟨324347, by rfl⟩ : syracuseStep 432463 = 648695) B648695
theorem B1087931 : Blo 381763 1087931 := bstep (se 1 (by rfl) ⟨815948, by rfl⟩ : syracuseStep 1087931 = 1631897) B1631897
theorem B2070971 : Blo 381763 2070971 := bstep (se 1 (by rfl) ⟨1553228, by rfl⟩ : syracuseStep 2070971 = 3106457) B3106457
theorem B4365251 : Blo 381763 4365251 := bstep (se 1 (by rfl) ⟨3273938, by rfl⟩ : syracuseStep 4365251 = 6547877) B6547877
theorem B433147 : Blo 381763 433147 := bstep (se 1 (by rfl) ⟨324860, by rfl⟩ : syracuseStep 433147 = 649721) B649721
theorem B433183 : Blo 381763 433183 := bstep (se 1 (by rfl) ⟨324887, by rfl⟩ : syracuseStep 433183 = 649775) B649775
theorem B728119 : Blo 381763 728119 := bstep (se 1 (by rfl) ⟨546089, by rfl⟩ : syracuseStep 728119 = 1092179) B1092179
theorem B433327 : Blo 381763 433327 := bstep (se 1 (by rfl) ⟨324995, by rfl⟩ : syracuseStep 433327 = 649991) B649991
theorem B433471 : Blo 381763 433471 := bstep (se 1 (by rfl) ⟨325103, by rfl⟩ : syracuseStep 433471 = 650207) B650207
theorem B10132867 : Blo 381763 10132867 := bstep (se 1 (by rfl) ⟨7599650, by rfl⟩ : syracuseStep 10132867 = 15199301) B15199301
theorem B1645991 : Blo 381763 1645991 := bstep (se 1 (by rfl) ⟨1234493, by rfl⟩ : syracuseStep 1645991 = 2468987) B2468987
theorem B859643 : Blo 381763 859643 := bstep (se 1 (by rfl) ⟨644732, by rfl⟩ : syracuseStep 859643 = 1289465) B1289465
theorem B859751 : Blo 381763 859751 := bstep (se 1 (by rfl) ⟨644813, by rfl⟩ : syracuseStep 859751 = 1289627) B1289627
theorem B1449647 : Blo 381763 1449647 := bstep (se 1 (by rfl) ⟨1087235, by rfl⟩ : syracuseStep 1449647 = 2174471) B2174471
theorem B859823 : Blo 381763 859823 := bstep (se 1 (by rfl) ⟨644867, by rfl⟩ : syracuseStep 859823 = 1289735) B1289735
theorem B859913 : Blo 381763 859913 := bstep (se 2 (by rfl) ⟨322467, by rfl⟩ : syracuseStep 859913 = 644935) B644935
theorem B5250905 : Blo 381763 5250905 := bstep (se 2 (by rfl) ⟨1969089, by rfl⟩ : syracuseStep 5250905 = 3938179) B3938179
theorem B860543 : Blo 381763 860543 := bstep (se 1 (by rfl) ⟨645407, by rfl⟩ : syracuseStep 860543 = 1290815) B1290815
theorem B1942055 : Blo 381763 1942055 := bstep (se 1 (by rfl) ⟨1456541, by rfl⟩ : syracuseStep 1942055 = 2913083) B2913083
theorem B1843823 : Blo 381763 1843823 := bstep (se 1 (by rfl) ⟨1382867, by rfl⟩ : syracuseStep 1843823 = 2765735) B2765735
theorem B1451591 : Blo 381763 1451591 := bstep (se 1 (by rfl) ⟨1088693, by rfl⟩ : syracuseStep 1451591 = 2177387) B2177387
theorem B1091303 : Blo 381763 1091303 := bstep (se 1 (by rfl) ⟨818477, by rfl⟩ : syracuseStep 1091303 = 1636955) B1636955
theorem B1091519 : Blo 381763 1091519 := bstep (se 1 (by rfl) ⟨818639, by rfl⟩ : syracuseStep 1091519 = 1637279) B1637279
theorem B6236129 : Blo 381763 6236129 := bstep (se 2 (by rfl) ⟨2338548, by rfl⟩ : syracuseStep 6236129 = 4677097) B4677097
theorem B731119 : Blo 381763 731119 := bstep (se 1 (by rfl) ⟨548339, by rfl⟩ : syracuseStep 731119 = 1096679) B1096679
theorem B2762849 : Blo 381763 2762849 := bstep (se 2 (by rfl) ⟨1036068, by rfl⟩ : syracuseStep 2762849 = 2072137) B2072137
theorem B1943675 : Blo 381763 1943675 := bstep (se 1 (by rfl) ⟨1457756, by rfl⟩ : syracuseStep 1943675 = 2915513) B2915513
theorem B1386719 : Blo 381763 1386719 := bstep (se 1 (by rfl) ⟨1040039, by rfl⟩ : syracuseStep 1386719 = 2080079) B2080079
theorem B1092521 : Blo 381763 1092521 := bstep (se 2 (by rfl) ⟨409695, by rfl⟩ : syracuseStep 1092521 = 819391) B819391
theorem B1846205 : Blo 381763 1846205 := bstep (se 3 (by rfl) ⟨346163, by rfl⟩ : syracuseStep 1846205 = 692327) B692327
theorem B1944647 : Blo 381763 1944647 := bstep (se 1 (by rfl) ⟨1458485, by rfl⟩ : syracuseStep 1944647 = 2916971) B2916971
theorem B2960959 : Blo 381763 2960959 := bstep (se 1 (by rfl) ⟨2220719, by rfl⟩ : syracuseStep 2960959 = 4441439) B4441439
theorem B5517391 : Blo 381763 5517391 := bstep (se 1 (by rfl) ⟨4138043, by rfl⟩ : syracuseStep 5517391 = 8276087) B8276087
theorem B864359 : Blo 381763 864359 := bstep (se 1 (by rfl) ⟨648269, by rfl⟩ : syracuseStep 864359 = 1296539) B1296539
theorem B864539 : Blo 381763 864539 := bstep (se 1 (by rfl) ⟨648404, by rfl⟩ : syracuseStep 864539 = 1296809) B1296809
theorem B1749289 : Blo 381763 1749289 := bstep (se 2 (by rfl) ⟨655983, by rfl⟩ : syracuseStep 1749289 = 1311967) B1311967
theorem B1093945 : Blo 381763 1093945 := bstep (se 2 (by rfl) ⟨410229, by rfl⟩ : syracuseStep 1093945 = 820459) B820459
theorem B864935 : Blo 381763 864935 := bstep (se 1 (by rfl) ⟨648701, by rfl⟩ : syracuseStep 864935 = 1297403) B1297403
theorem B1749755 : Blo 381763 1749755 := bstep (se 1 (by rfl) ⟨1312316, by rfl⟩ : syracuseStep 1749755 = 2624633) B2624633
theorem B1946429 : Blo 381763 1946429 := bstep (se 3 (by rfl) ⟨364955, by rfl⟩ : syracuseStep 1946429 = 729911) B729911
theorem B15774695 : Blo 381763 15774695 := bstep (se 1 (by rfl) ⟨11831021, by rfl⟩ : syracuseStep 15774695 = 23662043) B23662043
theorem B1291247 : Blo 381763 1291247 := bstep (se 1 (by rfl) ⟨968435, by rfl⟩ : syracuseStep 1291247 = 1936871) B1936871
theorem B3290341 : Blo 381763 3290341 := bstep (se 4 (by rfl) ⟨308469, by rfl⟩ : syracuseStep 3290341 = 616939) B616939
theorem B3290615 : Blo 381763 3290615 := bstep (se 1 (by rfl) ⟨2467961, by rfl⟩ : syracuseStep 3290615 = 4935923) B4935923
theorem B2471447 : Blo 381763 2471447 := bstep (se 1 (by rfl) ⟨1853585, by rfl⟩ : syracuseStep 2471447 = 3707171) B3707171
theorem B1226447 : Blo 381763 1226447 := bstep (se 1 (by rfl) ⟨919835, by rfl⟩ : syracuseStep 1226447 = 1839671) B1839671
theorem B1128179 : Blo 381763 1128179 := bstep (se 1 (by rfl) ⟨846134, by rfl⟩ : syracuseStep 1128179 = 1692269) B1692269
theorem B1292111 : Blo 381763 1292111 := bstep (se 1 (by rfl) ⟨969083, by rfl⟩ : syracuseStep 1292111 = 1938167) B1938167
theorem B1947563 : Blo 381763 1947563 := bstep (se 1 (by rfl) ⟨1460672, by rfl⟩ : syracuseStep 1947563 = 2921345) B2921345
theorem B867401 : Blo 381763 867401 := bstep (se 2 (by rfl) ⟨325275, by rfl⟩ : syracuseStep 867401 = 650551) B650551
theorem B1097135 : Blo 381763 1097135 := bstep (se 1 (by rfl) ⟨822851, by rfl⟩ : syracuseStep 1097135 = 1645703) B1645703
theorem B572975 : Blo 381763 572975 := bstep (se 1 (by rfl) ⟨429731, by rfl⟩ : syracuseStep 572975 = 859463) B859463
theorem B572999 : Blo 381763 572999 := bstep (se 1 (by rfl) ⟨429749, by rfl⟩ : syracuseStep 572999 = 859499) B859499
theorem B573083 : Blo 381763 573083 := bstep (se 1 (by rfl) ⟨429812, by rfl⟩ : syracuseStep 573083 = 859625) B859625
theorem B573179 : Blo 381763 573179 := bstep (se 1 (by rfl) ⟨429884, by rfl⟩ : syracuseStep 573179 = 859769) B859769
theorem B2178845 : Blo 381763 2178845 := bstep (se 3 (by rfl) ⟨408533, by rfl⟩ : syracuseStep 2178845 = 817067) B817067
theorem B1294163 : Blo 381763 1294163 := bstep (se 1 (by rfl) ⟨970622, by rfl⟩ : syracuseStep 1294163 = 1941245) B1941245
theorem B573647 : Blo 381763 573647 := bstep (se 1 (by rfl) ⟨430235, by rfl⟩ : syracuseStep 573647 = 860471) B860471
theorem B1098319 : Blo 381763 1098319 := bstep (se 1 (by rfl) ⟨823739, by rfl⟩ : syracuseStep 1098319 = 1647479) B1647479
theorem B1950317 : Blo 381763 1950317 := bstep (se 3 (by rfl) ⟨365684, by rfl⟩ : syracuseStep 1950317 = 731369) B731369
theorem B130892591 : Blo 381763 130892591 := bstep (se 1 (by rfl) ⟨98169443, by rfl⟩ : syracuseStep 130892591 = 196338887) B196338887
theorem B574331 : Blo 381763 574331 := bstep (se 1 (by rfl) ⟨430748, by rfl⟩ : syracuseStep 574331 = 861497) B861497
theorem B574457 : Blo 381763 574457 := bstep (se 2 (by rfl) ⟨215421, by rfl⟩ : syracuseStep 574457 = 430843) B430843
theorem B574511 : Blo 381763 574511 := bstep (se 1 (by rfl) ⟨430883, by rfl⟩ : syracuseStep 574511 = 861767) B861767
theorem B574631 : Blo 381763 574631 := bstep (se 1 (by rfl) ⟨430973, by rfl⟩ : syracuseStep 574631 = 861947) B861947
theorem B9815255 : Blo 381763 9815255 := bstep (se 1 (by rfl) ⟨7361441, by rfl⟩ : syracuseStep 9815255 = 14722883) B14722883
theorem B410951 : Blo 381763 410951 := bstep (se 1 (by rfl) ⟨308213, by rfl⟩ : syracuseStep 410951 = 616427) B616427
theorem B574823 : Blo 381763 574823 := bstep (se 1 (by rfl) ⟨431117, by rfl⟩ : syracuseStep 574823 = 862235) B862235
theorem B575465 : Blo 381763 575465 := bstep (se 2 (by rfl) ⟨215799, by rfl⟩ : syracuseStep 575465 = 431599) B431599
theorem B7358525 : Blo 381763 7358525 := bstep (se 3 (by rfl) ⟨1379723, by rfl⟩ : syracuseStep 7358525 = 2759447) B2759447
theorem B575609 : Blo 381763 575609 := bstep (se 2 (by rfl) ⟨215853, by rfl⟩ : syracuseStep 575609 = 431707) B431707
theorem B575807 : Blo 381763 575807 := bstep (se 1 (by rfl) ⟨431855, by rfl⟩ : syracuseStep 575807 = 863711) B863711
theorem B575951 : Blo 381763 575951 := bstep (se 1 (by rfl) ⟨431963, by rfl⟩ : syracuseStep 575951 = 863927) B863927
theorem B575993 : Blo 381763 575993 := bstep (se 2 (by rfl) ⟨215997, by rfl⟩ : syracuseStep 575993 = 431995) B431995
theorem B576041 : Blo 381763 576041 := bstep (se 2 (by rfl) ⟨216015, by rfl⟩ : syracuseStep 576041 = 432031) B432031
theorem B2345555 : Blo 381763 2345555 := bstep (se 1 (by rfl) ⟨1759166, by rfl⟩ : syracuseStep 2345555 = 3518333) B3518333
theorem B1297025 : Blo 381763 1297025 := bstep (se 2 (by rfl) ⟨486384, by rfl⟩ : syracuseStep 1297025 = 972769) B972769
theorem B67095215 : Blo 381763 67095215 := bstep (se 1 (by rfl) ⟨50321411, by rfl⟩ : syracuseStep 67095215 = 100642823) B100642823
theorem B969479 : Blo 381763 969479 := bstep (se 1 (by rfl) ⟨727109, by rfl⟩ : syracuseStep 969479 = 1454219) B1454219
theorem B576479 : Blo 381763 576479 := bstep (se 1 (by rfl) ⟨432359, by rfl⟩ : syracuseStep 576479 = 864719) B864719
theorem B1035335 : Blo 381763 1035335 := bstep (se 1 (by rfl) ⟨776501, by rfl⟩ : syracuseStep 1035335 = 1553003) B1553003
theorem B576923 : Blo 381763 576923 := bstep (se 1 (by rfl) ⟨432692, by rfl⟩ : syracuseStep 576923 = 865385) B865385
theorem B577289 : Blo 381763 577289 := bstep (se 2 (by rfl) ⟨216483, by rfl⟩ : syracuseStep 577289 = 432967) B432967
theorem B2903849 : Blo 381763 2903849 := bstep (se 2 (by rfl) ⟨1088943, by rfl⟩ : syracuseStep 2903849 = 2177887) B2177887
theorem B577343 : Blo 381763 577343 := bstep (se 1 (by rfl) ⟨433007, by rfl⟩ : syracuseStep 577343 = 866015) B866015
theorem B3329981 : Blo 381763 3329981 := bstep (se 3 (by rfl) ⟨624371, by rfl⟩ : syracuseStep 3329981 = 1248743) B1248743
theorem B577583 : Blo 381763 577583 := bstep (se 1 (by rfl) ⟨433187, by rfl⟩ : syracuseStep 577583 = 866375) B866375
theorem B2183219 : Blo 381763 2183219 := bstep (se 1 (by rfl) ⟨1637414, by rfl⟩ : syracuseStep 2183219 = 3274829) B3274829
theorem B578027 : Blo 381763 578027 := bstep (se 1 (by rfl) ⟨433520, by rfl⟩ : syracuseStep 578027 = 867041) B867041
theorem B578153 : Blo 381763 578153 := bstep (se 2 (by rfl) ⟨216807, by rfl⟩ : syracuseStep 578153 = 433615) B433615
theorem B578159 : Blo 381763 578159 := bstep (se 1 (by rfl) ⟨433619, by rfl⟩ : syracuseStep 578159 = 867239) B867239
theorem B578279 : Blo 381763 578279 := bstep (se 1 (by rfl) ⟨433709, by rfl⟩ : syracuseStep 578279 = 867419) B867419
theorem B578441 : Blo 381763 578441 := bstep (se 2 (by rfl) ⟨216915, by rfl⟩ : syracuseStep 578441 = 433831) B433831
theorem B381919 : Blo 381763 381919 := bstep (se 1 (by rfl) ⟨286439, by rfl⟩ : syracuseStep 381919 = 572879) B572879
theorem B382175 : Blo 381763 382175 := bstep (se 1 (by rfl) ⟨286631, by rfl⟩ : syracuseStep 382175 = 573263) B573263
theorem B59954417 : Blo 381763 59954417 := bstep (se 2 (by rfl) ⟨22482906, by rfl⟩ : syracuseStep 59954417 = 44965813) B44965813
theorem B382255 : Blo 381763 382255 := bstep (se 1 (by rfl) ⟨286691, by rfl⟩ : syracuseStep 382255 = 573383) B573383
theorem B972263 : Blo 381763 972263 := bstep (se 1 (by rfl) ⟨729197, by rfl⟩ : syracuseStep 972263 = 1458395) B1458395
theorem B972283 : Blo 381763 972283 := bstep (se 1 (by rfl) ⟨729212, by rfl⟩ : syracuseStep 972283 = 1458425) B1458425
theorem B382495 : Blo 381763 382495 := bstep (se 1 (by rfl) ⟨286871, by rfl⟩ : syracuseStep 382495 = 573743) B573743
theorem B1037929 : Blo 381763 1037929 := bstep (se 2 (by rfl) ⟨389223, by rfl⟩ : syracuseStep 1037929 = 778447) B778447
theorem B382655 : Blo 381763 382655 := bstep (se 1 (by rfl) ⟨286991, by rfl⟩ : syracuseStep 382655 = 573983) B573983
theorem B4904711 : Blo 381763 4904711 := bstep (se 1 (by rfl) ⟨3678533, by rfl⟩ : syracuseStep 4904711 = 7357067) B7357067
theorem B383103 : Blo 381763 383103 := bstep (se 1 (by rfl) ⟨287327, by rfl⟩ : syracuseStep 383103 = 574655) B574655
theorem B383199 : Blo 381763 383199 := bstep (se 1 (by rfl) ⟨287399, by rfl⟩ : syracuseStep 383199 = 574799) B574799
theorem B383259 : Blo 381763 383259 := bstep (se 1 (by rfl) ⟨287444, by rfl⟩ : syracuseStep 383259 = 574889) B574889
theorem B383359 : Blo 381763 383359 := bstep (se 1 (by rfl) ⟨287519, by rfl⟩ : syracuseStep 383359 = 575039) B575039
theorem B383387 : Blo 381763 383387 := bstep (se 1 (by rfl) ⟨287540, by rfl⟩ : syracuseStep 383387 = 575081) B575081
theorem B973255 : Blo 381763 973255 := bstep (se 1 (by rfl) ⟨729941, by rfl⟩ : syracuseStep 973255 = 1459883) B1459883
theorem B2185703 : Blo 381763 2185703 := bstep (se 1 (by rfl) ⟨1639277, by rfl⟩ : syracuseStep 2185703 = 3278555) B3278555
theorem B13425209 : Blo 381763 13425209 := bstep (se 2 (by rfl) ⟨5034453, by rfl⟩ : syracuseStep 13425209 = 10068907) B10068907
theorem B383679 : Blo 381763 383679 := bstep (se 1 (by rfl) ⟨287759, by rfl⟩ : syracuseStep 383679 = 575519) B575519
theorem B1301183 : Blo 381763 1301183 := bstep (se 1 (by rfl) ⟨975887, by rfl⟩ : syracuseStep 1301183 = 1951775) B1951775
theorem B383807 : Blo 381763 383807 := bstep (se 1 (by rfl) ⟨287855, by rfl⟩ : syracuseStep 383807 = 575711) B575711
theorem B383847 : Blo 381763 383847 := bstep (se 1 (by rfl) ⟨287885, by rfl⟩ : syracuseStep 383847 = 575771) B575771
theorem B973691 : Blo 381763 973691 := bstep (se 1 (by rfl) ⟨730268, by rfl⟩ : syracuseStep 973691 = 1460537) B1460537
theorem B384063 : Blo 381763 384063 := bstep (se 1 (by rfl) ⟨288047, by rfl⟩ : syracuseStep 384063 = 576095) B576095
theorem B384251 : Blo 381763 384251 := bstep (se 1 (by rfl) ⟨288188, by rfl⟩ : syracuseStep 384251 = 576377) B576377
theorem B384283 : Blo 381763 384283 := bstep (se 1 (by rfl) ⟨288212, by rfl⟩ : syracuseStep 384283 = 576425) B576425
theorem B4349213 : Blo 381763 4349213 := bstep (se 3 (by rfl) ⟨815477, by rfl⟩ : syracuseStep 4349213 = 1630955) B1630955
theorem B384383 : Blo 381763 384383 := bstep (se 1 (by rfl) ⟨288287, by rfl⟩ : syracuseStep 384383 = 576575) B576575
theorem B7822817 : Blo 381763 7822817 := bstep (se 2 (by rfl) ⟨2933556, by rfl⟩ : syracuseStep 7822817 = 5867113) B5867113
theorem B2907737 : Blo 381763 2907737 := bstep (se 2 (by rfl) ⟨1090401, by rfl⟩ : syracuseStep 2907737 = 2180803) B2180803
theorem B384751 : Blo 381763 384751 := bstep (se 1 (by rfl) ⟨288563, by rfl⟩ : syracuseStep 384751 = 577127) B577127
theorem B974713 : Blo 381763 974713 := bstep (se 2 (by rfl) ⟨365517, by rfl⟩ : syracuseStep 974713 = 731035) B731035
theorem B1400743 : Blo 381763 1400743 := bstep (se 1 (by rfl) ⟨1050557, by rfl⟩ : syracuseStep 1400743 = 2101115) B2101115
theorem B385007 : Blo 381763 385007 := bstep (se 1 (by rfl) ⟨288755, by rfl⟩ : syracuseStep 385007 = 577511) B577511
theorem B614441 : Blo 381763 614441 := bstep (se 2 (by rfl) ⟨230415, by rfl⟩ : syracuseStep 614441 = 460831) B460831
theorem B385087 : Blo 381763 385087 := bstep (se 1 (by rfl) ⟨288815, by rfl⟩ : syracuseStep 385087 = 577631) B577631
theorem B385095 : Blo 381763 385095 := bstep (se 1 (by rfl) ⟨288821, by rfl⟩ : syracuseStep 385095 = 577643) B577643
theorem B385127 : Blo 381763 385127 := bstep (se 1 (by rfl) ⟨288845, by rfl⟩ : syracuseStep 385127 = 577691) B577691
theorem B975199 : Blo 381763 975199 := bstep (se 1 (by rfl) ⟨731399, by rfl⟩ : syracuseStep 975199 = 1462799) B1462799
theorem B975503 : Blo 381763 975503 := bstep (se 1 (by rfl) ⟨731627, by rfl⟩ : syracuseStep 975503 = 1463255) B1463255
theorem B385695 : Blo 381763 385695 := bstep (se 1 (by rfl) ⟨289271, by rfl⟩ : syracuseStep 385695 = 578543) B578543
theorem B4350671 : Blo 381763 4350671 := bstep (se 1 (by rfl) ⟨3263003, by rfl⟩ : syracuseStep 4350671 = 6526007) B6526007
theorem B648283 : Blo 381763 648283 := bstep (se 1 (by rfl) ⟨486212, by rfl⟩ : syracuseStep 648283 = 972425) B972425
theorem B975983 : Blo 381763 975983 := bstep (se 1 (by rfl) ⟨731987, by rfl⟩ : syracuseStep 975983 = 1463975) B1463975
theorem B2450843 : Blo 381763 2450843 := bstep (se 1 (by rfl) ⟨1838132, by rfl⟩ : syracuseStep 2450843 = 3676265) B3676265
theorem B2189051 : Blo 381763 2189051 := bstep (se 1 (by rfl) ⟨1641788, by rfl⟩ : syracuseStep 2189051 = 3283577) B3283577
theorem B9628217 : Blo 381763 9628217 := bstep (se 2 (by rfl) ⟨3610581, by rfl⟩ : syracuseStep 9628217 = 7221163) B7221163
theorem B2190077 : Blo 381763 2190077 := bstep (se 3 (by rfl) ⟨410639, by rfl⟩ : syracuseStep 2190077 = 821279) B821279
theorem B3697487 : Blo 381763 3697487 := bstep (se 1 (by rfl) ⟨2773115, by rfl⟩ : syracuseStep 3697487 = 5546231) B5546231
theorem B18641441 : Blo 381763 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B2191967 : Blo 381763 2191967 := bstep (se 1 (by rfl) ⟨1643975, by rfl⟩ : syracuseStep 2191967 = 3287951) B3287951
theorem B2454407 : Blo 381763 2454407 := bstep (se 1 (by rfl) ⟨1840805, by rfl⟩ : syracuseStep 2454407 = 3681611) B3681611
theorem B2192285 : Blo 381763 2192285 := bstep (se 3 (by rfl) ⟨411053, by rfl⟩ : syracuseStep 2192285 = 822107) B822107
theorem B2192467 : Blo 381763 2192467 := bstep (se 1 (by rfl) ⟨1644350, by rfl⟩ : syracuseStep 2192467 = 3288701) B3288701
theorem B2454893 : Blo 381763 2454893 := bstep (se 3 (by rfl) ⟨460292, by rfl⟩ : syracuseStep 2454893 = 920585) B920585
theorem B816743 : Blo 381763 816743 := bstep (se 1 (by rfl) ⟨612557, by rfl⟩ : syracuseStep 816743 = 1225115) B1225115
theorem B980623 : Blo 381763 980623 := bstep (se 1 (by rfl) ⟨735467, by rfl⟩ : syracuseStep 980623 = 1470935) B1470935
theorem B3537017 : Blo 381763 3537017 := bstep (se 2 (by rfl) ⟨1326381, by rfl⟩ : syracuseStep 3537017 = 2652763) B2652763
theorem B1603997 : Blo 381763 1603997 := bstep (se 3 (by rfl) ⟨300749, by rfl⟩ : syracuseStep 1603997 = 601499) B601499
theorem B6552251 : Blo 381763 6552251 := bstep (se 1 (by rfl) ⟨4914188, by rfl⟩ : syracuseStep 6552251 = 9828377) B9828377
theorem B3701483 : Blo 381763 3701483 := bstep (se 1 (by rfl) ⟨2776112, by rfl⟩ : syracuseStep 3701483 = 5552225) B5552225
theorem B2456993 : Blo 381763 2456993 := bstep (se 2 (by rfl) ⟨921372, by rfl⟩ : syracuseStep 2456993 = 1842745) B1842745
theorem B1834559 : Blo 381763 1834559 := bstep (se 1 (by rfl) ⟨1375919, by rfl⟩ : syracuseStep 1834559 = 2751839) B2751839
theorem B2195383 : Blo 381763 2195383 := bstep (se 1 (by rfl) ⟨1646537, by rfl⟩ : syracuseStep 2195383 = 3293075) B3293075
theorem B3278177 : Blo 381763 3278177 := bstep (se 2 (by rfl) ⟨1229316, by rfl⟩ : syracuseStep 3278177 = 2458633) B2458633
theorem B44730143 : Blo 381763 44730143 := bstep (se 1 (by rfl) ⟨33547607, by rfl⟩ : syracuseStep 44730143 = 67095215) B67095215
theorem B1640387 : Blo 381763 1640387 := bstep (se 1 (by rfl) ⟨1230290, by rfl⟩ : syracuseStep 1640387 = 2460581) B2460581
theorem B690223 : Blo 381763 690223 := bstep (se 1 (by rfl) ⟨517667, by rfl⟩ : syracuseStep 690223 = 1035335) B1035335
theorem B349046909 : Blo 381763 349046909 := bstep (se 3 (by rfl) ⟨65446295, by rfl⟩ : syracuseStep 349046909 = 130892591) B130892591
theorem B1935899 : Blo 381763 1935899 := bstep (se 1 (by rfl) ⟨1451924, by rfl⟩ : syracuseStep 1935899 = 2903849) B2903849
theorem B2755529 : Blo 381763 2755529 := bstep (se 2 (by rfl) ⟨1033323, by rfl⟩ : syracuseStep 2755529 = 2066647) B2066647
theorem B1642643 : Blo 381763 1642643 := bstep (se 1 (by rfl) ⟨1231982, by rfl⟩ : syracuseStep 1642643 = 2463965) B2463965
theorem B725287 : Blo 381763 725287 := bstep (se 1 (by rfl) ⟨543965, by rfl⟩ : syracuseStep 725287 = 1087931) B1087931
theorem B1380647 : Blo 381763 1380647 := bstep (se 1 (by rfl) ⟨1035485, by rfl⟩ : syracuseStep 1380647 = 2070971) B2070971
theorem B8950139 : Blo 381763 8950139 := bstep (se 1 (by rfl) ⟨6712604, by rfl⟩ : syracuseStep 8950139 = 13425209) B13425209
theorem B5215211 : Blo 381763 5215211 := bstep (se 1 (by rfl) ⟨3911408, by rfl⟩ : syracuseStep 5215211 = 7822817) B7822817
theorem B1938491 : Blo 381763 1938491 := bstep (se 1 (by rfl) ⟨1453868, by rfl⟩ : syracuseStep 1938491 = 2907737) B2907737
theorem B2332385 : Blo 381763 2332385 := bstep (se 2 (by rfl) ⟨874644, by rfl⟩ : syracuseStep 2332385 = 1749289) B1749289
theorem B727535 : Blo 381763 727535 := bstep (se 1 (by rfl) ⟨545651, by rfl⟩ : syracuseStep 727535 = 1091303) B1091303
theorem B727679 : Blo 381763 727679 := bstep (se 1 (by rfl) ⟨545759, by rfl⟩ : syracuseStep 727679 = 1091519) B1091519
theorem B1841899 : Blo 381763 1841899 := bstep (se 1 (by rfl) ⟨1381424, by rfl⟩ : syracuseStep 1841899 = 2762849) B2762849
theorem B2923289 : Blo 381763 2923289 := bstep (se 2 (by rfl) ⟨1096233, by rfl⟩ : syracuseStep 2923289 = 2192467) B2192467
theorem B924479 : Blo 381763 924479 := bstep (se 1 (by rfl) ⟨693359, by rfl⟩ : syracuseStep 924479 = 1386719) B1386719
theorem B2464991 : Blo 381763 2464991 := bstep (se 1 (by rfl) ⟨1848743, by rfl⟩ : syracuseStep 2464991 = 3697487) B3697487
theorem B728347 : Blo 381763 728347 := bstep (se 1 (by rfl) ⟨546260, by rfl⟩ : syracuseStep 728347 = 1092521) B1092521
theorem B1383905 : Blo 381763 1383905 := bstep (se 2 (by rfl) ⟨518964, by rfl⟩ : syracuseStep 1383905 = 1037929) B1037929
theorem B12427627 : Blo 381763 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B860831 : Blo 381763 860831 := bstep (se 1 (by rfl) ⟨645623, by rfl⟩ : syracuseStep 860831 = 1291247) B1291247
theorem B1647631 : Blo 381763 1647631 := bstep (se 1 (by rfl) ⟨1235723, by rfl⟩ : syracuseStep 1647631 = 2471447) B2471447
theorem B861407 : Blo 381763 861407 := bstep (se 1 (by rfl) ⟨646055, by rfl⟩ : syracuseStep 861407 = 1292111) B1292111
theorem B4368167 : Blo 381763 4368167 := bstep (se 1 (by rfl) ⟨3276125, by rfl⟩ : syracuseStep 4368167 = 6552251) B6552251
theorem B2467655 : Blo 381763 2467655 := bstep (se 1 (by rfl) ⟨1850741, by rfl⟩ : syracuseStep 2467655 = 3701483) B3701483
theorem B13510489 : Blo 381763 13510489 := bstep (se 2 (by rfl) ⟨5066433, by rfl⟩ : syracuseStep 13510489 = 10132867) B10132867
theorem B731423 : Blo 381763 731423 := bstep (se 1 (by rfl) ⟨548567, by rfl⟩ : syracuseStep 731423 = 1097135) B1097135
theorem B1223039 : Blo 381763 1223039 := bstep (se 1 (by rfl) ⟨917279, by rfl⟩ : syracuseStep 1223039 = 1834559) B1834559
theorem B1452563 : Blo 381763 1452563 := bstep (se 1 (by rfl) ⟨1089422, by rfl⟩ : syracuseStep 1452563 = 2178845) B2178845
theorem B862775 : Blo 381763 862775 := bstep (se 1 (by rfl) ⟨647081, by rfl⟩ : syracuseStep 862775 = 1294163) B1294163
theorem B2927177 : Blo 381763 2927177 := bstep (se 2 (by rfl) ⟨1097691, by rfl⟩ : syracuseStep 2927177 = 2195383) B2195383
theorem B1289519 : Blo 381763 1289519 := bstep (se 1 (by rfl) ⟨967139, by rfl⟩ : syracuseStep 1289519 = 1934279) B1934279
theorem B864377 : Blo 381763 864377 := bstep (se 2 (by rfl) ⟨324141, by rfl⟩ : syracuseStep 864377 = 648283) B648283
theorem B1290383 : Blo 381763 1290383 := bstep (se 1 (by rfl) ⟨967787, by rfl⟩ : syracuseStep 1290383 = 1935575) B1935575
theorem B864683 : Blo 381763 864683 := bstep (se 1 (by rfl) ⟨648512, by rfl⟩ : syracuseStep 864683 = 1297025) B1297025
theorem B1455479 : Blo 381763 1455479 := bstep (se 1 (by rfl) ⟨1091609, by rfl⟩ : syracuseStep 1455479 = 2183219) B2183219
theorem B2602621 : Blo 381763 2602621 := bstep (se 3 (by rfl) ⟨487991, by rfl⟩ : syracuseStep 2602621 = 975983) B975983
theorem B9975773 : Blo 381763 9975773 := bstep (se 3 (by rfl) ⟨1870457, by rfl⟩ : syracuseStep 9975773 = 3740915) B3740915
theorem B1095869 : Blo 381763 1095869 := bstep (se 3 (by rfl) ⟨205475, by rfl⟩ : syracuseStep 1095869 = 410951) B410951
theorem B1292759 : Blo 381763 1292759 := bstep (se 1 (by rfl) ⟨969569, by rfl⟩ : syracuseStep 1292759 = 1939139) B1939139
theorem B1227575 : Blo 381763 1227575 := bstep (se 1 (by rfl) ⟨920681, by rfl⟩ : syracuseStep 1227575 = 1841363) B1841363
theorem B1457135 : Blo 381763 1457135 := bstep (se 1 (by rfl) ⟨1092851, by rfl⟩ : syracuseStep 1457135 = 2185703) B2185703
theorem B867455 : Blo 381763 867455 := bstep (se 1 (by rfl) ⟨650591, by rfl⟩ : syracuseStep 867455 = 1301183) B1301183
theorem B3947945 : Blo 381763 3947945 := bstep (se 2 (by rfl) ⟨1480479, by rfl⟩ : syracuseStep 3947945 = 2960959) B2960959
theorem B2899475 : Blo 381763 2899475 := bstep (se 1 (by rfl) ⟨2174606, by rfl⟩ : syracuseStep 2899475 = 4349213) B4349213
theorem B572969 : Blo 381763 572969 := bstep (se 2 (by rfl) ⟨214863, by rfl⟩ : syracuseStep 572969 = 429727) B429727
theorem B1097327 : Blo 381763 1097327 := bstep (se 1 (by rfl) ⟨822995, by rfl⟩ : syracuseStep 1097327 = 1645991) B1645991
theorem B573095 : Blo 381763 573095 := bstep (se 1 (by rfl) ⟨429821, by rfl⟩ : syracuseStep 573095 = 859643) B859643
theorem B573167 : Blo 381763 573167 := bstep (se 1 (by rfl) ⟨429875, by rfl⟩ : syracuseStep 573167 = 859751) B859751
theorem B966431 : Blo 381763 966431 := bstep (se 1 (by rfl) ⟨724823, by rfl⟩ : syracuseStep 966431 = 1449647) B1449647
theorem B573215 : Blo 381763 573215 := bstep (se 1 (by rfl) ⟨429911, by rfl⟩ : syracuseStep 573215 = 859823) B859823
theorem B573275 : Blo 381763 573275 := bstep (se 1 (by rfl) ⟨429956, by rfl⟩ : syracuseStep 573275 = 859913) B859913
theorem B573353 : Blo 381763 573353 := bstep (se 2 (by rfl) ⟨215007, by rfl⟩ : syracuseStep 573353 = 430015) B430015
theorem B409627 : Blo 381763 409627 := bstep (se 1 (by rfl) ⟨307220, by rfl⟩ : syracuseStep 409627 = 614441) B614441
theorem B7356521 : Blo 381763 7356521 := bstep (se 2 (by rfl) ⟨2758695, by rfl⟩ : syracuseStep 7356521 = 5517391) B5517391
theorem B573695 : Blo 381763 573695 := bstep (se 1 (by rfl) ⟨430271, by rfl⟩ : syracuseStep 573695 = 860543) B860543
theorem B1294703 : Blo 381763 1294703 := bstep (se 1 (by rfl) ⟨971027, by rfl⟩ : syracuseStep 1294703 = 1942055) B1942055
theorem B1229215 : Blo 381763 1229215 := bstep (se 1 (by rfl) ⟨921911, by rfl⟩ : syracuseStep 1229215 = 1843823) B1843823
theorem B1458593 : Blo 381763 1458593 := bstep (se 2 (by rfl) ⟨546972, by rfl⟩ : syracuseStep 1458593 = 1093945) B1093945
theorem B2900447 : Blo 381763 2900447 := bstep (se 1 (by rfl) ⟨2175335, by rfl⟩ : syracuseStep 2900447 = 4350671) B4350671
theorem B967727 : Blo 381763 967727 := bstep (se 1 (by rfl) ⟨725795, by rfl⟩ : syracuseStep 967727 = 1451591) B1451591
theorem B1459367 : Blo 381763 1459367 := bstep (se 1 (by rfl) ⟨1094525, by rfl⟩ : syracuseStep 1459367 = 2189051) B2189051
theorem B1295783 : Blo 381763 1295783 := bstep (se 1 (by rfl) ⟨971837, by rfl⟩ : syracuseStep 1295783 = 1943675) B1943675
theorem B1460051 : Blo 381763 1460051 := bstep (se 1 (by rfl) ⟨1095038, by rfl⟩ : syracuseStep 1460051 = 2190077) B2190077
theorem B1230803 : Blo 381763 1230803 := bstep (se 1 (by rfl) ⟨923102, by rfl⟩ : syracuseStep 1230803 = 1846205) B1846205
theorem B1296377 : Blo 381763 1296377 := bstep (se 2 (by rfl) ⟨486141, by rfl⟩ : syracuseStep 1296377 = 972283) B972283
theorem B1296431 : Blo 381763 1296431 := bstep (se 1 (by rfl) ⟨972323, by rfl⟩ : syracuseStep 1296431 = 1944647) B1944647
theorem B2804057 : Blo 381763 2804057 := bstep (se 2 (by rfl) ⟨1051521, by rfl⟩ : syracuseStep 2804057 = 2103043) B2103043
theorem B576239 : Blo 381763 576239 := bstep (se 1 (by rfl) ⟨432179, by rfl⟩ : syracuseStep 576239 = 864359) B864359
theorem B576359 : Blo 381763 576359 := bstep (se 1 (by rfl) ⟨432269, by rfl⟩ : syracuseStep 576359 = 864539) B864539
theorem B1461311 : Blo 381763 1461311 := bstep (se 1 (by rfl) ⟨1095983, by rfl⟩ : syracuseStep 1461311 = 2191967) B2191967
theorem B576617 : Blo 381763 576617 := bstep (se 2 (by rfl) ⟨216231, by rfl⟩ : syracuseStep 576617 = 432463) B432463
theorem B576623 : Blo 381763 576623 := bstep (se 1 (by rfl) ⟨432467, by rfl⟩ : syracuseStep 576623 = 864935) B864935
theorem B1166503 : Blo 381763 1166503 := bstep (se 1 (by rfl) ⟨874877, by rfl⟩ : syracuseStep 1166503 = 1749755) B1749755
theorem B1297619 : Blo 381763 1297619 := bstep (se 1 (by rfl) ⟨973214, by rfl⟩ : syracuseStep 1297619 = 1946429) B1946429
theorem B1297673 : Blo 381763 1297673 := bstep (se 2 (by rfl) ⟨486627, by rfl⟩ : syracuseStep 1297673 = 973255) B973255
theorem B1461523 : Blo 381763 1461523 := bstep (se 1 (by rfl) ⟨1096142, by rfl⟩ : syracuseStep 1461523 = 2192285) B2192285
theorem B5229989 : Blo 381763 5229989 := bstep (se 4 (by rfl) ⟨490311, by rfl⟩ : syracuseStep 5229989 = 980623) B980623
theorem B544495 : Blo 381763 544495 := bstep (se 1 (by rfl) ⟨408371, by rfl⟩ : syracuseStep 544495 = 816743) B816743
theorem B1298375 : Blo 381763 1298375 := bstep (se 1 (by rfl) ⟨973781, by rfl⟩ : syracuseStep 1298375 = 1947563) B1947563
theorem B577529 : Blo 381763 577529 := bstep (se 2 (by rfl) ⟨216573, by rfl⟩ : syracuseStep 577529 = 433147) B433147
theorem B577577 : Blo 381763 577577 := bstep (se 2 (by rfl) ⟨216591, by rfl⟩ : syracuseStep 577577 = 433183) B433183
theorem B970825 : Blo 381763 970825 := bstep (se 2 (by rfl) ⟨364059, by rfl⟩ : syracuseStep 970825 = 728119) B728119
theorem B577769 : Blo 381763 577769 := bstep (se 2 (by rfl) ⟨216663, by rfl⟩ : syracuseStep 577769 = 433327) B433327
theorem B1069331 : Blo 381763 1069331 := bstep (se 1 (by rfl) ⟨801998, by rfl⟩ : syracuseStep 1069331 = 1603997) B1603997
theorem B577961 : Blo 381763 577961 := bstep (se 2 (by rfl) ⟨216735, by rfl⟩ : syracuseStep 577961 = 433471) B433471
theorem B578267 : Blo 381763 578267 := bstep (se 1 (by rfl) ⟨433700, by rfl⟩ : syracuseStep 578267 = 867401) B867401
theorem B381983 : Blo 381763 381983 := bstep (se 1 (by rfl) ⟨286487, by rfl⟩ : syracuseStep 381983 = 572975) B572975
theorem B381999 : Blo 381763 381999 := bstep (se 1 (by rfl) ⟨286499, by rfl⟩ : syracuseStep 381999 = 572999) B572999
theorem B382055 : Blo 381763 382055 := bstep (se 1 (by rfl) ⟨286541, by rfl⟩ : syracuseStep 382055 = 573083) B573083
theorem B1299617 : Blo 381763 1299617 := bstep (se 2 (by rfl) ⟨487356, by rfl⟩ : syracuseStep 1299617 = 974713) B974713
theorem B382119 : Blo 381763 382119 := bstep (se 1 (by rfl) ⟨286589, by rfl⟩ : syracuseStep 382119 = 573179) B573179
theorem B382431 : Blo 381763 382431 := bstep (se 1 (by rfl) ⟨286823, by rfl⟩ : syracuseStep 382431 = 573647) B573647
theorem B2446843 : Blo 381763 2446843 := bstep (se 1 (by rfl) ⟨1835132, by rfl⟩ : syracuseStep 2446843 = 3670265) B3670265
theorem B808555 : Blo 381763 808555 := bstep (se 1 (by rfl) ⟨606416, by rfl⟩ : syracuseStep 808555 = 1212833) B1212833
theorem B1300211 : Blo 381763 1300211 := bstep (se 1 (by rfl) ⟨975158, by rfl⟩ : syracuseStep 1300211 = 1950317) B1950317
theorem B1300265 : Blo 381763 1300265 := bstep (se 2 (by rfl) ⟨487599, by rfl⟩ : syracuseStep 1300265 = 975199) B975199
theorem B382887 : Blo 381763 382887 := bstep (se 1 (by rfl) ⟨287165, by rfl⟩ : syracuseStep 382887 = 574331) B574331
theorem B382971 : Blo 381763 382971 := bstep (se 1 (by rfl) ⟨287228, by rfl⟩ : syracuseStep 382971 = 574457) B574457
theorem B383007 : Blo 381763 383007 := bstep (se 1 (by rfl) ⟨287255, by rfl⟩ : syracuseStep 383007 = 574511) B574511
theorem B1464425 : Blo 381763 1464425 := bstep (se 2 (by rfl) ⟨549159, by rfl⟩ : syracuseStep 1464425 = 1098319) B1098319
theorem B383087 : Blo 381763 383087 := bstep (se 1 (by rfl) ⟨287315, by rfl⟩ : syracuseStep 383087 = 574631) B574631
theorem B6543503 : Blo 381763 6543503 := bstep (se 1 (by rfl) ⟨4907627, by rfl⟩ : syracuseStep 6543503 = 9815255) B9815255
theorem B383215 : Blo 381763 383215 := bstep (se 1 (by rfl) ⟨287411, by rfl⟩ : syracuseStep 383215 = 574823) B574823
theorem B383643 : Blo 381763 383643 := bstep (se 1 (by rfl) ⟨287732, by rfl⟩ : syracuseStep 383643 = 575465) B575465
theorem B4905683 : Blo 381763 4905683 := bstep (se 1 (by rfl) ⟨3679262, by rfl⟩ : syracuseStep 4905683 = 7358525) B7358525
theorem B383739 : Blo 381763 383739 := bstep (se 1 (by rfl) ⟨287804, by rfl⟩ : syracuseStep 383739 = 575609) B575609
theorem B383871 : Blo 381763 383871 := bstep (se 1 (by rfl) ⟨287903, by rfl⟩ : syracuseStep 383871 = 575807) B575807
theorem B383967 : Blo 381763 383967 := bstep (se 1 (by rfl) ⟨287975, by rfl⟩ : syracuseStep 383967 = 575951) B575951
theorem B383995 : Blo 381763 383995 := bstep (se 1 (by rfl) ⟨287996, by rfl⟩ : syracuseStep 383995 = 575993) B575993
theorem B384027 : Blo 381763 384027 := bstep (se 1 (by rfl) ⟨288020, by rfl⟩ : syracuseStep 384027 = 576041) B576041
theorem B646319 : Blo 381763 646319 := bstep (se 1 (by rfl) ⟨484739, by rfl⟩ : syracuseStep 646319 = 969479) B969479
theorem B384319 : Blo 381763 384319 := bstep (se 1 (by rfl) ⟨288239, by rfl⟩ : syracuseStep 384319 = 576479) B576479
theorem B2448893 : Blo 381763 2448893 := bstep (se 3 (by rfl) ⟨459167, by rfl⟩ : syracuseStep 2448893 = 918335) B918335
theorem B384615 : Blo 381763 384615 := bstep (se 1 (by rfl) ⟨288461, by rfl⟩ : syracuseStep 384615 = 576923) B576923
theorem B18243191 : Blo 381763 18243191 := bstep (se 1 (by rfl) ⟨13682393, by rfl⟩ : syracuseStep 18243191 = 27364787) B27364787
theorem B384859 : Blo 381763 384859 := bstep (se 1 (by rfl) ⟨288644, by rfl⟩ : syracuseStep 384859 = 577289) B577289
theorem B384895 : Blo 381763 384895 := bstep (se 1 (by rfl) ⟨288671, by rfl⟩ : syracuseStep 384895 = 577343) B577343
theorem B2219987 : Blo 381763 2219987 := bstep (se 1 (by rfl) ⟨1664990, by rfl⟩ : syracuseStep 2219987 = 3329981) B3329981
theorem B974825 : Blo 381763 974825 := bstep (se 2 (by rfl) ⟨365559, by rfl⟩ : syracuseStep 974825 = 731119) B731119
theorem B385055 : Blo 381763 385055 := bstep (se 1 (by rfl) ⟨288791, by rfl⟩ : syracuseStep 385055 = 577583) B577583
theorem B385351 : Blo 381763 385351 := bstep (se 1 (by rfl) ⟨289013, by rfl⟩ : syracuseStep 385351 = 578027) B578027
theorem B385435 : Blo 381763 385435 := bstep (se 1 (by rfl) ⟨289076, by rfl⟩ : syracuseStep 385435 = 578153) B578153
theorem B385439 : Blo 381763 385439 := bstep (se 1 (by rfl) ⟨289079, by rfl⟩ : syracuseStep 385439 = 578159) B578159
theorem B385519 : Blo 381763 385519 := bstep (se 1 (by rfl) ⟨289139, by rfl⟩ : syracuseStep 385519 = 578279) B578279
theorem B385627 : Blo 381763 385627 := bstep (se 1 (by rfl) ⟨289220, by rfl⟩ : syracuseStep 385627 = 578441) B578441
theorem B39969611 : Blo 381763 39969611 := bstep (se 1 (by rfl) ⟨29977208, by rfl⟩ : syracuseStep 39969611 = 59954417) B59954417
theorem B648175 : Blo 381763 648175 := bstep (se 1 (by rfl) ⟨486131, by rfl⟩ : syracuseStep 648175 = 972263) B972263
theorem B1401911 : Blo 381763 1401911 := bstep (se 1 (by rfl) ⟨1051433, by rfl⟩ : syracuseStep 1401911 = 2102867) B2102867
theorem B3269807 : Blo 381763 3269807 := bstep (se 1 (by rfl) ⟨2452355, by rfl⟩ : syracuseStep 3269807 = 4904711) B4904711
theorem B649127 : Blo 381763 649127 := bstep (se 1 (by rfl) ⟨486845, by rfl⟩ : syracuseStep 649127 = 973691) B973691
theorem B2910167 : Blo 381763 2910167 := bstep (se 1 (by rfl) ⟨2182625, by rfl⟩ : syracuseStep 2910167 = 4365251) B4365251
theorem B3008477 : Blo 381763 3008477 := bstep (se 3 (by rfl) ⟨564089, by rfl⟩ : syracuseStep 3008477 = 1128179) B1128179
theorem B3500603 : Blo 381763 3500603 := bstep (se 1 (by rfl) ⟨2625452, by rfl⟩ : syracuseStep 3500603 = 5250905) B5250905
theorem B650335 : Blo 381763 650335 := bstep (se 1 (by rfl) ⟨487751, by rfl⟩ : syracuseStep 650335 = 975503) B975503
theorem B1633895 : Blo 381763 1633895 := bstep (se 1 (by rfl) ⟨1225421, by rfl⟩ : syracuseStep 1633895 = 2450843) B2450843
theorem B4157419 : Blo 381763 4157419 := bstep (se 1 (by rfl) ⟨3118064, by rfl⟩ : syracuseStep 4157419 = 6236129) B6236129
theorem B6254813 : Blo 381763 6254813 := bstep (se 3 (by rfl) ⟨1172777, by rfl⟩ : syracuseStep 6254813 = 2345555) B2345555
theorem B4387121 : Blo 381763 4387121 := bstep (se 2 (by rfl) ⟨1645170, by rfl⟩ : syracuseStep 4387121 = 3290341) B3290341
theorem B6418811 : Blo 381763 6418811 := bstep (se 1 (by rfl) ⟨4814108, by rfl⟩ : syracuseStep 6418811 = 9628217) B9628217
theorem B1636271 : Blo 381763 1636271 := bstep (se 1 (by rfl) ⟨1227203, by rfl⟩ : syracuseStep 1636271 = 2454407) B2454407
theorem B10516463 : Blo 381763 10516463 := bstep (se 1 (by rfl) ⟨7887347, by rfl⟩ : syracuseStep 10516463 = 15774695) B15774695
theorem B1636595 : Blo 381763 1636595 := bstep (se 1 (by rfl) ⟨1227446, by rfl⟩ : syracuseStep 1636595 = 2454893) B2454893
theorem B2193743 : Blo 381763 2193743 := bstep (se 1 (by rfl) ⟨1645307, by rfl⟩ : syracuseStep 2193743 = 3290615) B3290615
theorem B817631 : Blo 381763 817631 := bstep (se 1 (by rfl) ⟨613223, by rfl⟩ : syracuseStep 817631 = 1226447) B1226447
theorem B2358011 : Blo 381763 2358011 := bstep (se 1 (by rfl) ⟨1768508, by rfl⟩ : syracuseStep 2358011 = 3537017) B3537017
theorem B1637995 : Blo 381763 1637995 := bstep (se 1 (by rfl) ⟨1228496, by rfl⟩ : syracuseStep 1637995 = 2456993) B2456993
theorem B1867657 : Blo 381763 1867657 := bstep (se 2 (by rfl) ⟨700371, by rfl⟩ : syracuseStep 1867657 = 1400743) B1400743
theorem B1933631 : Blo 381763 1933631 := bstep (se 1 (by rfl) ⟨1450223, by rfl⟩ : syracuseStep 1933631 = 2900447) B2900447
theorem B1638953 : Blo 381763 1638953 := bstep (se 2 (by rfl) ⟨614607, by rfl⟩ : syracuseStep 1638953 = 1229215) B1229215
theorem B2851549 : Blo 381763 2851549 := bstep (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) B1069331
theorem B29820095 : Blo 381763 29820095 := bstep (se 1 (by rfl) ⟨22365071, by rfl⟩ : syracuseStep 29820095 = 44730143) B44730143
theorem B820535 : Blo 381763 820535 := bstep (se 1 (by rfl) ⟨615401, by rfl⟩ : syracuseStep 820535 = 1230803) B1230803
theorem B2196841 : Blo 381763 2196841 := bstep (se 2 (by rfl) ⟨823815, by rfl⟩ : syracuseStep 2196841 = 1647631) B1647631
theorem B1869371 : Blo 381763 1869371 := bstep (se 1 (by rfl) ⟨1402028, by rfl⟩ : syracuseStep 1869371 = 2804057) B2804057
theorem B1837019 : Blo 381763 1837019 := bstep (se 1 (by rfl) ⟨1377764, by rfl⟩ : syracuseStep 1837019 = 2755529) B2755529
theorem B920297 : Blo 381763 920297 := bstep (se 2 (by rfl) ⟨345111, by rfl⟩ : syracuseStep 920297 = 690223) B690223
theorem B920431 : Blo 381763 920431 := bstep (se 1 (by rfl) ⟨690323, by rfl⟩ : syracuseStep 920431 = 1380647) B1380647
theorem B5966759 : Blo 381763 5966759 := bstep (se 1 (by rfl) ⟨4475069, by rfl⟩ : syracuseStep 5966759 = 8950139) B8950139
theorem B3476807 : Blo 381763 3476807 := bstep (se 1 (by rfl) ⟨2607605, by rfl⟩ : syracuseStep 3476807 = 5215211) B5215211
theorem B4362335 : Blo 381763 4362335 := bstep (se 1 (by rfl) ⟨3271751, by rfl⟩ : syracuseStep 4362335 = 6543503) B6543503
theorem B430879 : Blo 381763 430879 := bstep (se 1 (by rfl) ⟨323159, by rfl⟩ : syracuseStep 430879 = 646319) B646319
theorem B1643327 : Blo 381763 1643327 := bstep (se 1 (by rfl) ⟨1232495, by rfl⟩ : syracuseStep 1643327 = 2464991) B2464991
theorem B725993 : Blo 381763 725993 := bstep (se 2 (by rfl) ⟨272247, by rfl⟩ : syracuseStep 725993 = 544495) B544495
theorem B922603 : Blo 381763 922603 := bstep (se 1 (by rfl) ⟨691952, by rfl⟩ : syracuseStep 922603 = 1383905) B1383905
theorem B1479991 : Blo 381763 1479991 := bstep (se 1 (by rfl) ⟨1109993, by rfl⟩ : syracuseStep 1479991 = 2219987) B2219987
theorem B5543225 : Blo 381763 5543225 := bstep (se 2 (by rfl) ⟨2078709, by rfl⟩ : syracuseStep 5543225 = 4157419) B4157419
theorem B2922317 : Blo 381763 2922317 := bstep (se 3 (by rfl) ⟨547934, by rfl⟩ : syracuseStep 2922317 = 1095869) B1095869
theorem B26646407 : Blo 381763 26646407 := bstep (se 1 (by rfl) ⟨19984805, by rfl⟩ : syracuseStep 26646407 = 39969611) B39969611
theorem B1645103 : Blo 381763 1645103 := bstep (se 1 (by rfl) ⟨1233827, by rfl⟩ : syracuseStep 1645103 = 2467655) B2467655
theorem B432751 : Blo 381763 432751 := bstep (se 1 (by rfl) ⟨324563, by rfl⟩ : syracuseStep 432751 = 649127) B649127
theorem B1940111 : Blo 381763 1940111 := bstep (se 1 (by rfl) ⟨1455083, by rfl⟩ : syracuseStep 1940111 = 2910167) B2910167
theorem B2005651 : Blo 381763 2005651 := bstep (se 1 (by rfl) ⟨1504238, by rfl⟩ : syracuseStep 2005651 = 3008477) B3008477
theorem B2333735 : Blo 381763 2333735 := bstep (se 1 (by rfl) ⟨1750301, by rfl⟩ : syracuseStep 2333735 = 3500603) B3500603
theorem B859679 : Blo 381763 859679 := bstep (se 1 (by rfl) ⟨644759, by rfl⟩ : syracuseStep 859679 = 1289519) B1289519
theorem B1089263 : Blo 381763 1089263 := bstep (se 1 (by rfl) ⟨816947, by rfl⟩ : syracuseStep 1089263 = 1633895) B1633895
theorem B860255 : Blo 381763 860255 := bstep (se 1 (by rfl) ⟨645191, by rfl⟩ : syracuseStep 860255 = 1290383) B1290383
theorem B4169875 : Blo 381763 4169875 := bstep (se 1 (by rfl) ⟨3127406, by rfl⟩ : syracuseStep 4169875 = 6254813) B6254813
theorem B2924747 : Blo 381763 2924747 := bstep (se 1 (by rfl) ⟨2193560, by rfl⟩ : syracuseStep 2924747 = 4387121) B4387121
theorem B10527853 : Blo 381763 10527853 := bstep (se 3 (by rfl) ⟨1973972, by rfl⟩ : syracuseStep 10527853 = 3947945) B3947945
theorem B1090847 : Blo 381763 1090847 := bstep (se 1 (by rfl) ⟨818135, by rfl⟩ : syracuseStep 1090847 = 1636271) B1636271
theorem B6530381 : Blo 381763 6530381 := bstep (se 3 (by rfl) ⟨1224446, by rfl⟩ : syracuseStep 6530381 = 2448893) B2448893
theorem B1091063 : Blo 381763 1091063 := bstep (se 1 (by rfl) ⟨818297, by rfl⟩ : syracuseStep 1091063 = 1636595) B1636595
theorem B2926205 : Blo 381763 2926205 := bstep (se 3 (by rfl) ⟨548663, by rfl⟩ : syracuseStep 2926205 = 1097327) B1097327
theorem B861839 : Blo 381763 861839 := bstep (se 1 (by rfl) ⟨646379, by rfl⟩ : syracuseStep 861839 = 1292759) B1292759
theorem B863135 : Blo 381763 863135 := bstep (se 1 (by rfl) ⟨647351, by rfl⟩ : syracuseStep 863135 = 1294703) B1294703
theorem B863855 : Blo 381763 863855 := bstep (se 1 (by rfl) ⟨647891, by rfl⟩ : syracuseStep 863855 = 1295783) B1295783
theorem B17116829 : Blo 381763 17116829 := bstep (se 3 (by rfl) ⟨3209405, by rfl⟩ : syracuseStep 17116829 = 6418811) B6418811
theorem B1093591 : Blo 381763 1093591 := bstep (se 1 (by rfl) ⟨820193, by rfl⟩ : syracuseStep 1093591 = 1640387) B1640387
theorem B864233 : Blo 381763 864233 := bstep (se 2 (by rfl) ⟨324087, by rfl⟩ : syracuseStep 864233 = 648175) B648175
theorem B864251 : Blo 381763 864251 := bstep (se 1 (by rfl) ⟨648188, by rfl⟩ : syracuseStep 864251 = 1296377) B1296377
theorem B864287 : Blo 381763 864287 := bstep (se 1 (by rfl) ⟨648215, by rfl⟩ : syracuseStep 864287 = 1296431) B1296431
theorem B232697939 : Blo 381763 232697939 := bstep (se 1 (by rfl) ⟨174523454, by rfl⟩ : syracuseStep 232697939 = 349046909) B349046909
theorem B1290599 : Blo 381763 1290599 := bstep (se 1 (by rfl) ⟨967949, by rfl⟩ : syracuseStep 1290599 = 1935899) B1935899
theorem B865079 : Blo 381763 865079 := bstep (se 1 (by rfl) ⟨648809, by rfl⟩ : syracuseStep 865079 = 1297619) B1297619
theorem B865115 : Blo 381763 865115 := bstep (se 1 (by rfl) ⟨648836, by rfl⟩ : syracuseStep 865115 = 1297673) B1297673
theorem B3486659 : Blo 381763 3486659 := bstep (se 1 (by rfl) ⟨2614994, by rfl⟩ : syracuseStep 3486659 = 5229989) B5229989
theorem B865583 : Blo 381763 865583 := bstep (se 1 (by rfl) ⟨649187, by rfl⟩ : syracuseStep 865583 = 1298375) B1298375
theorem B1095095 : Blo 381763 1095095 := bstep (se 1 (by rfl) ⟨821321, by rfl⟩ : syracuseStep 1095095 = 1642643) B1642643
theorem B1292327 : Blo 381763 1292327 := bstep (se 1 (by rfl) ⟨969245, by rfl⟩ : syracuseStep 1292327 = 1938491) B1938491
theorem B866411 : Blo 381763 866411 := bstep (se 1 (by rfl) ⟨649808, by rfl⟩ : syracuseStep 866411 = 1299617) B1299617
theorem B1554923 : Blo 381763 1554923 := bstep (se 1 (by rfl) ⟨1166192, by rfl⟩ : syracuseStep 1554923 = 2332385) B2332385
theorem B866807 : Blo 381763 866807 := bstep (se 1 (by rfl) ⟨650105, by rfl⟩ : syracuseStep 866807 = 1300211) B1300211
theorem B866843 : Blo 381763 866843 := bstep (se 1 (by rfl) ⟨650132, by rfl⟩ : syracuseStep 866843 = 1300265) B1300265
theorem B867113 : Blo 381763 867113 := bstep (se 2 (by rfl) ⟨325167, by rfl⟩ : syracuseStep 867113 = 650335) B650335
theorem B1555337 : Blo 381763 1555337 := bstep (se 2 (by rfl) ⟨583251, by rfl⟩ : syracuseStep 1555337 = 1166503) B1166503
theorem B1948697 : Blo 381763 1948697 := bstep (se 2 (by rfl) ⟨730761, by rfl⟩ : syracuseStep 1948697 = 1461523) B1461523
theorem B1948859 : Blo 381763 1948859 := bstep (se 1 (by rfl) ⟨1461644, by rfl⟩ : syracuseStep 1948859 = 2923289) B2923289
theorem B1294433 : Blo 381763 1294433 := bstep (se 2 (by rfl) ⟨485412, by rfl⟩ : syracuseStep 1294433 = 970825) B970825
theorem B967049 : Blo 381763 967049 := bstep (se 2 (by rfl) ⟨362643, by rfl⟩ : syracuseStep 967049 = 725287) B725287
theorem B573887 : Blo 381763 573887 := bstep (se 1 (by rfl) ⟨430415, by rfl⟩ : syracuseStep 573887 = 860831) B860831
theorem B934607 : Blo 381763 934607 := bstep (se 1 (by rfl) ⟨700955, by rfl⟩ : syracuseStep 934607 = 1401911) B1401911
theorem B2179871 : Blo 381763 2179871 := bstep (se 1 (by rfl) ⟨1634903, by rfl⟩ : syracuseStep 2179871 = 3269807) B3269807
theorem B574271 : Blo 381763 574271 := bstep (se 1 (by rfl) ⟨430703, by rfl⟩ : syracuseStep 574271 = 861407) B861407
theorem B968375 : Blo 381763 968375 := bstep (se 1 (by rfl) ⟨726281, by rfl⟩ : syracuseStep 968375 = 1452563) B1452563
theorem B575183 : Blo 381763 575183 := bstep (se 1 (by rfl) ⟨431387, by rfl⟩ : syracuseStep 575183 = 862775) B862775
theorem B1951451 : Blo 381763 1951451 := bstep (se 1 (by rfl) ⟨1463588, by rfl⟩ : syracuseStep 1951451 = 2927177) B2927177
theorem B3262457 : Blo 381763 3262457 := bstep (se 2 (by rfl) ⟨1223421, by rfl⟩ : syracuseStep 3262457 = 2446843) B2446843
theorem B576251 : Blo 381763 576251 := bstep (se 1 (by rfl) ⟨432188, by rfl⟩ : syracuseStep 576251 = 864377) B864377
theorem B576455 : Blo 381763 576455 := bstep (se 1 (by rfl) ⟨432341, by rfl⟩ : syracuseStep 576455 = 864683) B864683
theorem B970319 : Blo 381763 970319 := bstep (se 1 (by rfl) ⟨727739, by rfl⟩ : syracuseStep 970319 = 1455479) B1455479
theorem B1462495 : Blo 381763 1462495 := bstep (se 1 (by rfl) ⟨1096871, by rfl⟩ : syracuseStep 1462495 = 2193743) B2193743
theorem B48648509 : Blo 381763 48648509 := bstep (se 3 (by rfl) ⟨9121595, by rfl⟩ : syracuseStep 48648509 = 18243191) B18243191
theorem B545087 : Blo 381763 545087 := bstep (se 1 (by rfl) ⟨408815, by rfl⟩ : syracuseStep 545087 = 817631) B817631
theorem B971129 : Blo 381763 971129 := bstep (se 2 (by rfl) ⟨364173, by rfl⟩ : syracuseStep 971129 = 728347) B728347
theorem B971423 : Blo 381763 971423 := bstep (se 1 (by rfl) ⟨728567, by rfl⟩ : syracuseStep 971423 = 1457135) B1457135
theorem B578303 : Blo 381763 578303 := bstep (se 1 (by rfl) ⟨433727, by rfl⟩ : syracuseStep 578303 = 867455) B867455
theorem B2183993 : Blo 381763 2183993 := bstep (se 2 (by rfl) ⟨818997, by rfl⟩ : syracuseStep 2183993 = 1637995) B1637995
theorem B381979 : Blo 381763 381979 := bstep (se 1 (by rfl) ⟨286484, by rfl⟩ : syracuseStep 381979 = 572969) B572969
theorem B382063 : Blo 381763 382063 := bstep (se 1 (by rfl) ⟨286547, by rfl⟩ : syracuseStep 382063 = 573095) B573095
theorem B382111 : Blo 381763 382111 := bstep (se 1 (by rfl) ⟨286583, by rfl⟩ : syracuseStep 382111 = 573167) B573167
theorem B644287 : Blo 381763 644287 := bstep (se 1 (by rfl) ⟨483215, by rfl⟩ : syracuseStep 644287 = 966431) B966431
theorem B382143 : Blo 381763 382143 := bstep (se 1 (by rfl) ⟨286607, by rfl⟩ : syracuseStep 382143 = 573215) B573215
theorem B382183 : Blo 381763 382183 := bstep (se 1 (by rfl) ⟨286637, by rfl⟩ : syracuseStep 382183 = 573275) B573275
theorem B382235 : Blo 381763 382235 := bstep (se 1 (by rfl) ⟨286676, by rfl⟩ : syracuseStep 382235 = 573353) B573353
theorem B4904347 : Blo 381763 4904347 := bstep (se 1 (by rfl) ⟨3678260, by rfl⟩ : syracuseStep 4904347 = 7356521) B7356521
theorem B2184677 : Blo 381763 2184677 := bstep (se 4 (by rfl) ⟨204813, by rfl⟩ : syracuseStep 2184677 = 409627) B409627
theorem B382463 : Blo 381763 382463 := bstep (se 1 (by rfl) ⟨286847, by rfl⟩ : syracuseStep 382463 = 573695) B573695
theorem B972395 : Blo 381763 972395 := bstep (se 1 (by rfl) ⟨729296, by rfl⟩ : syracuseStep 972395 = 1458593) B1458593
theorem B16570169 : Blo 381763 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B645151 : Blo 381763 645151 := bstep (se 1 (by rfl) ⟨483863, by rfl⟩ : syracuseStep 645151 = 967727) B967727
theorem B972911 : Blo 381763 972911 := bstep (se 1 (by rfl) ⟨729683, by rfl⟩ : syracuseStep 972911 = 1459367) B1459367
theorem B2185451 : Blo 381763 2185451 := bstep (se 1 (by rfl) ⟨1639088, by rfl⟩ : syracuseStep 2185451 = 3278177) B3278177
theorem B973367 : Blo 381763 973367 := bstep (se 1 (by rfl) ⟨730025, by rfl⟩ : syracuseStep 973367 = 1460051) B1460051
theorem B384159 : Blo 381763 384159 := bstep (se 1 (by rfl) ⟨288119, by rfl⟩ : syracuseStep 384159 = 576239) B576239
theorem B384239 : Blo 381763 384239 := bstep (se 1 (by rfl) ⟨288179, by rfl⟩ : syracuseStep 384239 = 576359) B576359
theorem B974207 : Blo 381763 974207 := bstep (se 1 (by rfl) ⟨730655, by rfl⟩ : syracuseStep 974207 = 1461311) B1461311
theorem B384411 : Blo 381763 384411 := bstep (se 1 (by rfl) ⟨288308, by rfl⟩ : syracuseStep 384411 = 576617) B576617
theorem B384415 : Blo 381763 384415 := bstep (se 1 (by rfl) ⟨288311, by rfl⟩ : syracuseStep 384415 = 576623) B576623
theorem B18013985 : Blo 381763 18013985 := bstep (se 2 (by rfl) ⟨6755244, by rfl⟩ : syracuseStep 18013985 = 13510489) B13510489
theorem B385019 : Blo 381763 385019 := bstep (se 1 (by rfl) ⟨288764, by rfl⟩ : syracuseStep 385019 = 577529) B577529
theorem B385051 : Blo 381763 385051 := bstep (se 1 (by rfl) ⟨288788, by rfl⟩ : syracuseStep 385051 = 577577) B577577
theorem B385179 : Blo 381763 385179 := bstep (se 1 (by rfl) ⟨288884, by rfl⟩ : syracuseStep 385179 = 577769) B577769
theorem B385307 : Blo 381763 385307 := bstep (se 1 (by rfl) ⟨288980, by rfl⟩ : syracuseStep 385307 = 577961) B577961
theorem B385511 : Blo 381763 385511 := bstep (se 1 (by rfl) ⟨289133, by rfl⟩ : syracuseStep 385511 = 578267) B578267
theorem B976283 : Blo 381763 976283 := bstep (se 1 (by rfl) ⟨732212, by rfl⟩ : syracuseStep 976283 = 1464425) B1464425
theorem B485023 : Blo 381763 485023 := bstep (se 1 (by rfl) ⟨363767, by rfl⟩ : syracuseStep 485023 = 727535) B727535
theorem B485119 : Blo 381763 485119 := bstep (se 1 (by rfl) ⟨363839, by rfl⟩ : syracuseStep 485119 = 727679) B727679
theorem B3270455 : Blo 381763 3270455 := bstep (se 1 (by rfl) ⟨2452841, by rfl⟩ : syracuseStep 3270455 = 4905683) B4905683
theorem B616319 : Blo 381763 616319 := bstep (se 1 (by rfl) ⟨462239, by rfl⟩ : syracuseStep 616319 = 924479) B924479
theorem B649883 : Blo 381763 649883 := bstep (se 1 (by rfl) ⟨487412, by rfl⟩ : syracuseStep 649883 = 974825) B974825
theorem B2912111 : Blo 381763 2912111 := bstep (se 1 (by rfl) ⟨2184083, by rfl⟩ : syracuseStep 2912111 = 4368167) B4368167
theorem B487615 : Blo 381763 487615 := bstep (se 1 (by rfl) ⟨365711, by rfl⟩ : syracuseStep 487615 = 731423) B731423
theorem B815359 : Blo 381763 815359 := bstep (se 1 (by rfl) ⟨611519, by rfl⟩ : syracuseStep 815359 = 1223039) B1223039
theorem B6288029 : Blo 381763 6288029 := bstep (se 3 (by rfl) ⟨1179005, by rfl⟩ : syracuseStep 6288029 = 2358011) B2358011
theorem B1078073 : Blo 381763 1078073 := bstep (se 2 (by rfl) ⟨404277, by rfl⟩ : syracuseStep 1078073 = 808555) B808555
theorem B3470161 : Blo 381763 3470161 := bstep (se 2 (by rfl) ⟨1301310, by rfl⟩ : syracuseStep 3470161 = 2602621) B2602621
theorem B2455865 : Blo 381763 2455865 := bstep (se 2 (by rfl) ⟨920949, by rfl⟩ : syracuseStep 2455865 = 1841899) B1841899
theorem B6650515 : Blo 381763 6650515 := bstep (se 1 (by rfl) ⟨4987886, by rfl⟩ : syracuseStep 6650515 = 9975773) B9975773
theorem B7010975 : Blo 381763 7010975 := bstep (se 1 (by rfl) ⟨5258231, by rfl⟩ : syracuseStep 7010975 = 10516463) B10516463
theorem B818383 : Blo 381763 818383 := bstep (se 1 (by rfl) ⟨613787, by rfl⟩ : syracuseStep 818383 = 1227575) B1227575
theorem B1932983 : Blo 381763 1932983 := bstep (se 1 (by rfl) ⟨1449737, by rfl⟩ : syracuseStep 1932983 = 2899475) B2899475
theorem B2490209 : Blo 381763 2490209 := bstep (se 2 (by rfl) ⟨933828, by rfl⟩ : syracuseStep 2490209 = 1867657) B1867657
theorem B620527837 : Blo 381763 620527837 := bstep (se 3 (by rfl) ⟨116348969, by rfl⟩ : syracuseStep 620527837 = 232697939) B232697939
theorem B623071 : Blo 381763 623071 := bstep (se 1 (by rfl) ⟨467303, by rfl⟩ : syracuseStep 623071 = 934607) B934607
theorem B1246247 : Blo 381763 1246247 := bstep (se 1 (by rfl) ⟨934685, by rfl⟩ : syracuseStep 1246247 = 1869371) B1869371
theorem B11046779 : Blo 381763 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B17764271 : Blo 381763 17764271 := bstep (se 1 (by rfl) ⟨13323203, by rfl⟩ : syracuseStep 17764271 = 26646407) B26646407
theorem B726175 : Blo 381763 726175 := bstep (se 1 (by rfl) ⟨544631, by rfl⟩ : syracuseStep 726175 = 1089263) B1089263
theorem B1087145 : Blo 381763 1087145 := bstep (se 2 (by rfl) ⟨407679, by rfl⟩ : syracuseStep 1087145 = 815359) B815359
theorem B727231 : Blo 381763 727231 := bstep (se 1 (by rfl) ⟨545423, by rfl⟩ : syracuseStep 727231 = 1090847) B1090847
theorem B727375 : Blo 381763 727375 := bstep (se 1 (by rfl) ⟨545531, by rfl⟩ : syracuseStep 727375 = 1091063) B1091063
theorem B4626881 : Blo 381763 4626881 := bstep (se 2 (by rfl) ⟨1735080, by rfl⟩ : syracuseStep 4626881 = 3470161) B3470161
theorem B859049 : Blo 381763 859049 := bstep (se 2 (by rfl) ⟨322143, by rfl⟩ : syracuseStep 859049 = 644287) B644287
theorem B1973321 : Blo 381763 1973321 := bstep (se 2 (by rfl) ⟨739995, by rfl⟩ : syracuseStep 1973321 = 1479991) B1479991
theorem B433255 : Blo 381763 433255 := bstep (se 1 (by rfl) ⟨324941, by rfl⟩ : syracuseStep 433255 = 649883) B649883
theorem B11411219 : Blo 381763 11411219 := bstep (se 1 (by rfl) ⟨8558414, by rfl⟩ : syracuseStep 11411219 = 17116829) B17116829
theorem B1941407 : Blo 381763 1941407 := bstep (se 1 (by rfl) ⟨1456055, by rfl⟩ : syracuseStep 1941407 = 2912111) B2912111
theorem B860201 : Blo 381763 860201 := bstep (se 2 (by rfl) ⟨322575, by rfl⟩ : syracuseStep 860201 = 645151) B645151
theorem B860399 : Blo 381763 860399 := bstep (se 1 (by rfl) ⟨645299, by rfl⟩ : syracuseStep 860399 = 1290599) B1290599
theorem B730063 : Blo 381763 730063 := bstep (se 1 (by rfl) ⟨547547, by rfl⟩ : syracuseStep 730063 = 1095095) B1095095
theorem B861551 : Blo 381763 861551 := bstep (se 1 (by rfl) ⟨646163, by rfl⟩ : syracuseStep 861551 = 1292327) B1292327
theorem B1091177 : Blo 381763 1091177 := bstep (se 2 (by rfl) ⟨409191, by rfl⟩ : syracuseStep 1091177 = 818383) B818383
theorem B1288655 : Blo 381763 1288655 := bstep (se 1 (by rfl) ⟨966491, by rfl⟩ : syracuseStep 1288655 = 1932983) B1932983
theorem B862955 : Blo 381763 862955 := bstep (se 1 (by rfl) ⟨647216, by rfl⟩ : syracuseStep 862955 = 1294433) B1294433
theorem B1289087 : Blo 381763 1289087 := bstep (se 1 (by rfl) ⟨966815, by rfl⟩ : syracuseStep 1289087 = 1933631) B1933631
theorem B1092635 : Blo 381763 1092635 := bstep (se 1 (by rfl) ⟨819476, by rfl⟩ : syracuseStep 1092635 = 1638953) B1638953
theorem B1453247 : Blo 381763 1453247 := bstep (se 1 (by rfl) ⟨1089935, by rfl⟩ : syracuseStep 1453247 = 2179871) B2179871
theorem B1453565 : Blo 381763 1453565 := bstep (se 3 (by rfl) ⟨272543, by rfl⟩ : syracuseStep 1453565 = 545087) B545087
theorem B1224679 : Blo 381763 1224679 := bstep (se 1 (by rfl) ⟨918509, by rfl⟩ : syracuseStep 1224679 = 1837019) B1837019
theorem B2174971 : Blo 381763 2174971 := bstep (se 1 (by rfl) ⟨1631228, by rfl⟩ : syracuseStep 2174971 = 3262457) B3262457
theorem B14037137 : Blo 381763 14037137 := bstep (se 2 (by rfl) ⟨5263926, by rfl⟩ : syracuseStep 14037137 = 10527853) B10527853
theorem B2929121 : Blo 381763 2929121 := bstep (se 2 (by rfl) ⟨1098420, by rfl⟩ : syracuseStep 2929121 = 2196841) B2196841
theorem B3977839 : Blo 381763 3977839 := bstep (se 1 (by rfl) ⟨2983379, by rfl⟩ : syracuseStep 3977839 = 5966759) B5966759
theorem B1455995 : Blo 381763 1455995 := bstep (se 1 (by rfl) ⟨1091996, by rfl⟩ : syracuseStep 1455995 = 2183993) B2183993
theorem B1095551 : Blo 381763 1095551 := bstep (se 1 (by rfl) ⟨821663, by rfl⟩ : syracuseStep 1095551 = 1643327) B1643327
theorem B1456451 : Blo 381763 1456451 := bstep (se 1 (by rfl) ⟨1092338, by rfl⟩ : syracuseStep 1456451 = 2184677) B2184677
theorem B1227241 : Blo 381763 1227241 := bstep (se 2 (by rfl) ⟨460215, by rfl⟩ : syracuseStep 1227241 = 920431) B920431
theorem B1948211 : Blo 381763 1948211 := bstep (se 1 (by rfl) ⟨1461158, by rfl⟩ : syracuseStep 1948211 = 2922317) B2922317
theorem B1456967 : Blo 381763 1456967 := bstep (se 1 (by rfl) ⟨1092725, by rfl⟩ : syracuseStep 1456967 = 2185451) B2185451
theorem B1096735 : Blo 381763 1096735 := bstep (se 1 (by rfl) ⟨822551, by rfl⟩ : syracuseStep 1096735 = 1645103) B1645103
theorem B1293407 : Blo 381763 1293407 := bstep (se 1 (by rfl) ⟨970055, by rfl⟩ : syracuseStep 1293407 = 1940111) B1940111
theorem B60833045 : Blo 381763 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B1555823 : Blo 381763 1555823 := bstep (se 1 (by rfl) ⟨1166867, by rfl⟩ : syracuseStep 1555823 = 2333735) B2333735
theorem B573119 : Blo 381763 573119 := bstep (se 1 (by rfl) ⟨429839, by rfl⟩ : syracuseStep 573119 = 859679) B859679
theorem B12009323 : Blo 381763 12009323 := bstep (se 1 (by rfl) ⟨9006992, by rfl⟩ : syracuseStep 12009323 = 18013985) B18013985
theorem B1458121 : Blo 381763 1458121 := bstep (se 2 (by rfl) ⟨546795, by rfl⟩ : syracuseStep 1458121 = 1093591) B1093591
theorem B573503 : Blo 381763 573503 := bstep (se 1 (by rfl) ⟨430127, by rfl⟩ : syracuseStep 573503 = 860255) B860255
theorem B1949831 : Blo 381763 1949831 := bstep (se 1 (by rfl) ⟨1462373, by rfl⟩ : syracuseStep 1949831 = 2924747) B2924747
theorem B1949993 : Blo 381763 1949993 := bstep (se 2 (by rfl) ⟨731247, by rfl⟩ : syracuseStep 1949993 = 1462495) B1462495
theorem B574505 : Blo 381763 574505 := bstep (se 2 (by rfl) ⟨215439, by rfl⟩ : syracuseStep 574505 = 430879) B430879
theorem B1950803 : Blo 381763 1950803 := bstep (se 1 (by rfl) ⟨1463102, by rfl⟩ : syracuseStep 1950803 = 2926205) B2926205
theorem B574559 : Blo 381763 574559 := bstep (se 1 (by rfl) ⟨430919, by rfl⟩ : syracuseStep 574559 = 861839) B861839
theorem B2180303 : Blo 381763 2180303 := bstep (se 1 (by rfl) ⟨1635227, by rfl⟩ : syracuseStep 2180303 = 3270455) B3270455
theorem B410879 : Blo 381763 410879 := bstep (se 1 (by rfl) ⟨308159, by rfl⟩ : syracuseStep 410879 = 616319) B616319
theorem B4146461 : Blo 381763 4146461 := bstep (se 3 (by rfl) ⟨777461, by rfl⟩ : syracuseStep 4146461 = 1554923) B1554923
theorem B1230137 : Blo 381763 1230137 := bstep (se 2 (by rfl) ⟨461301, by rfl⟩ : syracuseStep 1230137 = 922603) B922603
theorem B18695933 : Blo 381763 18695933 := bstep (se 3 (by rfl) ⟨3505487, by rfl⟩ : syracuseStep 18695933 = 7010975) B7010975
theorem B6539129 : Blo 381763 6539129 := bstep (se 2 (by rfl) ⟨2452173, by rfl⟩ : syracuseStep 6539129 = 4904347) B4904347
theorem B575423 : Blo 381763 575423 := bstep (se 1 (by rfl) ⟨431567, by rfl⟩ : syracuseStep 575423 = 863135) B863135
theorem B575903 : Blo 381763 575903 := bstep (se 1 (by rfl) ⟨431927, by rfl⟩ : syracuseStep 575903 = 863855) B863855
theorem B576155 : Blo 381763 576155 := bstep (se 1 (by rfl) ⟨432116, by rfl⟩ : syracuseStep 576155 = 864233) B864233
theorem B576167 : Blo 381763 576167 := bstep (se 1 (by rfl) ⟨432125, by rfl⟩ : syracuseStep 576167 = 864251) B864251
theorem B576191 : Blo 381763 576191 := bstep (se 1 (by rfl) ⟨432143, by rfl⟩ : syracuseStep 576191 = 864287) B864287
theorem B576719 : Blo 381763 576719 := bstep (se 1 (by rfl) ⟨432539, by rfl⟩ : syracuseStep 576719 = 865079) B865079
theorem B576743 : Blo 381763 576743 := bstep (se 1 (by rfl) ⟨432557, by rfl⟩ : syracuseStep 576743 = 865115) B865115
theorem B577001 : Blo 381763 577001 := bstep (se 2 (by rfl) ⟨216375, by rfl⟩ : syracuseStep 577001 = 432751) B432751
theorem B8867353 : Blo 381763 8867353 := bstep (se 2 (by rfl) ⟨3325257, by rfl⟩ : syracuseStep 8867353 = 6650515) B6650515
theorem B2674201 : Blo 381763 2674201 := bstep (se 2 (by rfl) ⟨1002825, by rfl⟩ : syracuseStep 2674201 = 2005651) B2005651
theorem B577055 : Blo 381763 577055 := bstep (se 1 (by rfl) ⟨432791, by rfl⟩ : syracuseStep 577055 = 865583) B865583
theorem B577607 : Blo 381763 577607 := bstep (se 1 (by rfl) ⟨433205, by rfl⟩ : syracuseStep 577607 = 866411) B866411
theorem B577871 : Blo 381763 577871 := bstep (se 1 (by rfl) ⟨433403, by rfl⟩ : syracuseStep 577871 = 866807) B866807
theorem B577895 : Blo 381763 577895 := bstep (se 1 (by rfl) ⟨433421, by rfl⟩ : syracuseStep 577895 = 866843) B866843
theorem B578075 : Blo 381763 578075 := bstep (se 1 (by rfl) ⟨433556, by rfl⟩ : syracuseStep 578075 = 867113) B867113
theorem B1036891 : Blo 381763 1036891 := bstep (se 1 (by rfl) ⟨777668, by rfl⟩ : syracuseStep 1036891 = 1555337) B1555337
theorem B1299131 : Blo 381763 1299131 := bstep (se 1 (by rfl) ⟨974348, by rfl⟩ : syracuseStep 1299131 = 1948697) B1948697
theorem B1299239 : Blo 381763 1299239 := bstep (se 1 (by rfl) ⟨974429, by rfl⟩ : syracuseStep 1299239 = 1948859) B1948859
theorem B1660139 : Blo 381763 1660139 := bstep (se 1 (by rfl) ⟨1245104, by rfl⟩ : syracuseStep 1660139 = 2490209) B2490209
theorem B5559833 : Blo 381763 5559833 := bstep (se 2 (by rfl) ⟨2084937, by rfl⟩ : syracuseStep 5559833 = 4169875) B4169875
theorem B644699 : Blo 381763 644699 := bstep (se 1 (by rfl) ⟨483524, by rfl⟩ : syracuseStep 644699 = 967049) B967049
theorem B382591 : Blo 381763 382591 := bstep (se 1 (by rfl) ⟨286943, by rfl⟩ : syracuseStep 382591 = 573887) B573887
theorem B382847 : Blo 381763 382847 := bstep (se 1 (by rfl) ⟨287135, by rfl⟩ : syracuseStep 382847 = 574271) B574271
theorem B19880063 : Blo 381763 19880063 := bstep (se 1 (by rfl) ⟨14910047, by rfl⟩ : syracuseStep 19880063 = 29820095) B29820095
theorem B645583 : Blo 381763 645583 := bstep (se 1 (by rfl) ⟨484187, by rfl⟩ : syracuseStep 645583 = 968375) B968375
theorem B383455 : Blo 381763 383455 := bstep (se 1 (by rfl) ⟨287591, by rfl⟩ : syracuseStep 383455 = 575183) B575183
theorem B1300967 : Blo 381763 1300967 := bstep (se 1 (by rfl) ⟨975725, by rfl⟩ : syracuseStep 1300967 = 1951451) B1951451
theorem B613531 : Blo 381763 613531 := bstep (se 1 (by rfl) ⟨460148, by rfl⟩ : syracuseStep 613531 = 920297) B920297
theorem B384167 : Blo 381763 384167 := bstep (se 1 (by rfl) ⟨288125, by rfl⟩ : syracuseStep 384167 = 576251) B576251
theorem B384303 : Blo 381763 384303 := bstep (se 1 (by rfl) ⟨288227, by rfl⟩ : syracuseStep 384303 = 576455) B576455
theorem B646697 : Blo 381763 646697 := bstep (se 2 (by rfl) ⟨242511, by rfl⟩ : syracuseStep 646697 = 485023) B485023
theorem B2317871 : Blo 381763 2317871 := bstep (se 1 (by rfl) ⟨1738403, by rfl⟩ : syracuseStep 2317871 = 3476807) B3476807
theorem B646825 : Blo 381763 646825 := bstep (se 2 (by rfl) ⟨242559, by rfl⟩ : syracuseStep 646825 = 485119) B485119
theorem B646879 : Blo 381763 646879 := bstep (se 1 (by rfl) ⟨485159, by rfl⟩ : syracuseStep 646879 = 970319) B970319
theorem B9297757 : Blo 381763 9297757 := bstep (se 3 (by rfl) ⟨1743329, by rfl⟩ : syracuseStep 9297757 = 3486659) B3486659
theorem B2908223 : Blo 381763 2908223 := bstep (se 1 (by rfl) ⟨2181167, by rfl⟩ : syracuseStep 2908223 = 4362335) B4362335
theorem B32432339 : Blo 381763 32432339 := bstep (se 1 (by rfl) ⟨24324254, by rfl⟩ : syracuseStep 32432339 = 48648509) B48648509
theorem B647419 : Blo 381763 647419 := bstep (se 1 (by rfl) ⟨485564, by rfl⟩ : syracuseStep 647419 = 971129) B971129
theorem B647615 : Blo 381763 647615 := bstep (se 1 (by rfl) ⟨485711, by rfl⟩ : syracuseStep 647615 = 971423) B971423
theorem B385535 : Blo 381763 385535 := bstep (se 1 (by rfl) ⟨289151, by rfl⟩ : syracuseStep 385535 = 578303) B578303
theorem B483995 : Blo 381763 483995 := bstep (se 1 (by rfl) ⟨362996, by rfl⟩ : syracuseStep 483995 = 725993) B725993
theorem B2188093 : Blo 381763 2188093 := bstep (se 3 (by rfl) ⟨410267, by rfl⟩ : syracuseStep 2188093 = 820535) B820535
theorem B3695483 : Blo 381763 3695483 := bstep (se 1 (by rfl) ⟨2771612, by rfl⟩ : syracuseStep 3695483 = 5543225) B5543225
theorem B648263 : Blo 381763 648263 := bstep (se 1 (by rfl) ⟨486197, by rfl⟩ : syracuseStep 648263 = 972395) B972395
theorem B648607 : Blo 381763 648607 := bstep (se 1 (by rfl) ⟨486455, by rfl⟩ : syracuseStep 648607 = 972911) B972911
theorem B648911 : Blo 381763 648911 := bstep (se 1 (by rfl) ⟨486683, by rfl⟩ : syracuseStep 648911 = 973367) B973367
theorem B649471 : Blo 381763 649471 := bstep (se 1 (by rfl) ⟨487103, by rfl⟩ : syracuseStep 649471 = 974207) B974207
theorem B650153 : Blo 381763 650153 := bstep (se 2 (by rfl) ⟨243807, by rfl⟩ : syracuseStep 650153 = 487615) B487615
theorem B4353587 : Blo 381763 4353587 := bstep (se 1 (by rfl) ⟨3265190, by rfl⟩ : syracuseStep 4353587 = 6530381) B6530381
theorem B650855 : Blo 381763 650855 := bstep (se 1 (by rfl) ⟨488141, by rfl⟩ : syracuseStep 650855 = 976283) B976283
theorem B4192019 : Blo 381763 4192019 := bstep (se 1 (by rfl) ⟨3144014, by rfl⟩ : syracuseStep 4192019 = 6288029) B6288029
theorem B718715 : Blo 381763 718715 := bstep (se 1 (by rfl) ⟨539036, by rfl⟩ : syracuseStep 718715 = 1078073) B1078073
theorem B1637243 : Blo 381763 1637243 := bstep (se 1 (by rfl) ⟨1227932, by rfl⟩ : syracuseStep 1637243 = 2455865) B2455865
theorem B820091 : Blo 381763 820091 := bstep (se 1 (by rfl) ⟨615068, by rfl⟩ : syracuseStep 820091 = 1230137) B1230137
theorem B2917457 : Blo 381763 2917457 := bstep (se 2 (by rfl) ⟨1094046, by rfl⟩ : syracuseStep 2917457 = 2188093) B2188093
theorem B4359419 : Blo 381763 4359419 := bstep (se 1 (by rfl) ⟨3269564, by rfl⟩ : syracuseStep 4359419 = 6539129) B6539129
theorem B3706555 : Blo 381763 3706555 := bstep (se 1 (by rfl) ⟨2779916, by rfl⟩ : syracuseStep 3706555 = 5559833) B5559833
theorem B429799 : Blo 381763 429799 := bstep (se 1 (by rfl) ⟨322349, by rfl⟩ : syracuseStep 429799 = 644699) B644699
theorem B724763 : Blo 381763 724763 := bstep (se 1 (by rfl) ⟨543572, by rfl⟩ : syracuseStep 724763 = 1087145) B1087145
theorem B3084587 : Blo 381763 3084587 := bstep (se 1 (by rfl) ⟨2313440, by rfl⟩ : syracuseStep 3084587 = 4626881) B4626881
theorem B1315547 : Blo 381763 1315547 := bstep (se 1 (by rfl) ⟨986660, by rfl⟩ : syracuseStep 1315547 = 1973321) B1973321
theorem B431131 : Blo 381763 431131 := bstep (se 1 (by rfl) ⟨323348, by rfl⟩ : syracuseStep 431131 = 646697) B646697
theorem B1545247 : Blo 381763 1545247 := bstep (se 1 (by rfl) ⟨1158935, by rfl⟩ : syracuseStep 1545247 = 2317871) B2317871
theorem B7607479 : Blo 381763 7607479 := bstep (se 1 (by rfl) ⟨5705609, by rfl⟩ : syracuseStep 7607479 = 11411219) B11411219
theorem B1938815 : Blo 381763 1938815 := bstep (se 1 (by rfl) ⟨1454111, by rfl⟩ : syracuseStep 1938815 = 2908223) B2908223
theorem B431743 : Blo 381763 431743 := bstep (se 1 (by rfl) ⟨323807, by rfl⟩ : syracuseStep 431743 = 647615) B647615
theorem B432175 : Blo 381763 432175 := bstep (se 1 (by rfl) ⟨324131, by rfl⟩ : syracuseStep 432175 = 648263) B648263
theorem B1382521 : Blo 381763 1382521 := bstep (se 2 (by rfl) ⟨518445, by rfl⟩ : syracuseStep 1382521 = 1036891) B1036891
theorem B727451 : Blo 381763 727451 := bstep (se 1 (by rfl) ⟨545588, by rfl⟩ : syracuseStep 727451 = 1091177) B1091177
theorem B432607 : Blo 381763 432607 := bstep (se 1 (by rfl) ⟨324455, by rfl⟩ : syracuseStep 432607 = 648911) B648911
theorem B859103 : Blo 381763 859103 := bstep (se 1 (by rfl) ⟨644327, by rfl⟩ : syracuseStep 859103 = 1288655) B1288655
theorem B859391 : Blo 381763 859391 := bstep (se 1 (by rfl) ⟨644543, by rfl⟩ : syracuseStep 859391 = 1289087) B1289087
theorem B433435 : Blo 381763 433435 := bstep (se 1 (by rfl) ⟨325076, by rfl⟩ : syracuseStep 433435 = 650153) B650153
theorem B728423 : Blo 381763 728423 := bstep (se 1 (by rfl) ⟨546317, by rfl⟩ : syracuseStep 728423 = 1092635) B1092635
theorem B433903 : Blo 381763 433903 := bstep (se 1 (by rfl) ⟨325427, by rfl⟩ : syracuseStep 433903 = 650855) B650855
theorem B860777 : Blo 381763 860777 := bstep (se 2 (by rfl) ⟨322791, by rfl⟩ : syracuseStep 860777 = 645583) B645583
theorem B2794679 : Blo 381763 2794679 := bstep (se 1 (by rfl) ⟨2096009, by rfl⟩ : syracuseStep 2794679 = 4192019) B4192019
theorem B730367 : Blo 381763 730367 := bstep (se 1 (by rfl) ⟨547775, by rfl⟩ : syracuseStep 730367 = 1095551) B1095551
theorem B1091495 : Blo 381763 1091495 := bstep (se 1 (by rfl) ⟨818621, by rfl⟩ : syracuseStep 1091495 = 1637243) B1637243
theorem B862271 : Blo 381763 862271 := bstep (se 1 (by rfl) ⟨646703, by rfl⟩ : syracuseStep 862271 = 1293407) B1293407
theorem B862433 : Blo 381763 862433 := bstep (se 2 (by rfl) ⟨323412, by rfl⟩ : syracuseStep 862433 = 646825) B646825
theorem B862505 : Blo 381763 862505 := bstep (se 2 (by rfl) ⟨323439, by rfl⟩ : syracuseStep 862505 = 646879) B646879
theorem B12397009 : Blo 381763 12397009 := bstep (se 2 (by rfl) ⟨4648878, by rfl⟩ : syracuseStep 12397009 = 9297757) B9297757
theorem B8006215 : Blo 381763 8006215 := bstep (se 1 (by rfl) ⟨6004661, by rfl⟩ : syracuseStep 8006215 = 12009323) B12009323
theorem B1944161 : Blo 381763 1944161 := bstep (se 2 (by rfl) ⟨729060, by rfl⟩ : syracuseStep 1944161 = 1458121) B1458121
theorem B827370449 : Blo 381763 827370449 := bstep (se 2 (by rfl) ⟨310263918, by rfl⟩ : syracuseStep 827370449 = 620527837) B620527837
theorem B863225 : Blo 381763 863225 := bstep (se 2 (by rfl) ⟨323709, by rfl⟩ : syracuseStep 863225 = 647419) B647419
theorem B86486237 : Blo 381763 86486237 := bstep (se 3 (by rfl) ⟨16216169, by rfl⟩ : syracuseStep 86486237 = 32432339) B32432339
theorem B830831 : Blo 381763 830831 := bstep (se 1 (by rfl) ⟨623123, by rfl⟩ : syracuseStep 830831 = 1246247) B1246247
theorem B1453535 : Blo 381763 1453535 := bstep (se 1 (by rfl) ⟨1090151, by rfl⟩ : syracuseStep 1453535 = 2180303) B2180303
theorem B2764307 : Blo 381763 2764307 := bstep (se 1 (by rfl) ⟨2073230, by rfl⟩ : syracuseStep 2764307 = 4146461) B4146461
theorem B12463955 : Blo 381763 12463955 := bstep (se 1 (by rfl) ⟨9347966, by rfl⟩ : syracuseStep 12463955 = 18695933) B18695933
theorem B1290653 : Blo 381763 1290653 := bstep (se 3 (by rfl) ⟨241997, by rfl⟩ : syracuseStep 1290653 = 483995) B483995
theorem B864809 : Blo 381763 864809 := bstep (se 2 (by rfl) ⟨324303, by rfl⟩ : syracuseStep 864809 = 648607) B648607
theorem B3323045 : Blo 381763 3323045 := bstep (se 4 (by rfl) ⟨311535, by rfl⟩ : syracuseStep 3323045 = 623071) B623071
theorem B11842847 : Blo 381763 11842847 := bstep (se 1 (by rfl) ⟨8882135, by rfl⟩ : syracuseStep 11842847 = 17764271) B17764271
theorem B865961 : Blo 381763 865961 := bstep (se 2 (by rfl) ⟨324735, by rfl⟩ : syracuseStep 865961 = 649471) B649471
theorem B866087 : Blo 381763 866087 := bstep (se 1 (by rfl) ⟨649565, by rfl⟩ : syracuseStep 866087 = 1299131) B1299131
theorem B866159 : Blo 381763 866159 := bstep (se 1 (by rfl) ⟨649619, by rfl⟩ : syracuseStep 866159 = 1299239) B1299239
theorem B21215141 : Blo 381763 21215141 := bstep (se 4 (by rfl) ⟨1988919, by rfl⟩ : syracuseStep 21215141 = 3977839) B3977839
theorem B1095677 : Blo 381763 1095677 := bstep (se 3 (by rfl) ⟨205439, by rfl⟩ : syracuseStep 1095677 = 410879) B410879
theorem B13253375 : Blo 381763 13253375 := bstep (se 1 (by rfl) ⟨9940031, by rfl⟩ : syracuseStep 13253375 = 19880063) B19880063
theorem B867311 : Blo 381763 867311 := bstep (se 1 (by rfl) ⟨650483, by rfl⟩ : syracuseStep 867311 = 1300967) B1300967
theorem B572699 : Blo 381763 572699 := bstep (se 1 (by rfl) ⟨429524, by rfl⟩ : syracuseStep 572699 = 859049) B859049
theorem B1294271 : Blo 381763 1294271 := bstep (se 1 (by rfl) ⟨970703, by rfl⟩ : syracuseStep 1294271 = 1941407) B1941407
theorem B2899961 : Blo 381763 2899961 := bstep (se 2 (by rfl) ⟨1087485, by rfl⟩ : syracuseStep 2899961 = 2174971) B2174971
theorem B573467 : Blo 381763 573467 := bstep (se 1 (by rfl) ⟨430100, by rfl⟩ : syracuseStep 573467 = 860201) B860201
theorem B573599 : Blo 381763 573599 := bstep (se 1 (by rfl) ⟨430199, by rfl⟩ : syracuseStep 573599 = 860399) B860399
theorem B574367 : Blo 381763 574367 := bstep (se 1 (by rfl) ⟨430775, by rfl⟩ : syracuseStep 574367 = 861551) B861551
theorem B968233 : Blo 381763 968233 := bstep (se 2 (by rfl) ⟨363087, by rfl⟩ : syracuseStep 968233 = 726175) B726175
theorem B575303 : Blo 381763 575303 := bstep (se 1 (by rfl) ⟨431477, by rfl⟩ : syracuseStep 575303 = 862955) B862955
theorem B968831 : Blo 381763 968831 := bstep (se 1 (by rfl) ⟨726623, by rfl⟩ : syracuseStep 968831 = 1453247) B1453247
theorem B969043 : Blo 381763 969043 := bstep (se 1 (by rfl) ⟨726782, by rfl⟩ : syracuseStep 969043 = 1453565) B1453565
theorem B2902391 : Blo 381763 2902391 := bstep (se 1 (by rfl) ⟨2176793, by rfl⟩ : syracuseStep 2902391 = 4353587) B4353587
theorem B9358091 : Blo 381763 9358091 := bstep (se 1 (by rfl) ⟨7018568, by rfl⟩ : syracuseStep 9358091 = 14037137) B14037137
theorem B969641 : Blo 381763 969641 := bstep (se 2 (by rfl) ⟨363615, by rfl⟩ : syracuseStep 969641 = 727231) B727231
theorem B1952747 : Blo 381763 1952747 := bstep (se 1 (by rfl) ⟨1464560, by rfl⟩ : syracuseStep 1952747 = 2929121) B2929121
theorem B969833 : Blo 381763 969833 := bstep (se 2 (by rfl) ⟨363687, by rfl⟩ : syracuseStep 969833 = 727375) B727375
theorem B479143 : Blo 381763 479143 := bstep (se 1 (by rfl) ⟨359357, by rfl⟩ : syracuseStep 479143 = 718715) B718715
theorem B970663 : Blo 381763 970663 := bstep (se 1 (by rfl) ⟨727997, by rfl⟩ : syracuseStep 970663 = 1455995) B1455995
theorem B1462313 : Blo 381763 1462313 := bstep (se 2 (by rfl) ⟨548367, by rfl⟩ : syracuseStep 1462313 = 1096735) B1096735
theorem B577673 : Blo 381763 577673 := bstep (se 2 (by rfl) ⟨216627, by rfl⟩ : syracuseStep 577673 = 433255) B433255
theorem B970967 : Blo 381763 970967 := bstep (se 1 (by rfl) ⟨728225, by rfl⟩ : syracuseStep 970967 = 1456451) B1456451
theorem B1298807 : Blo 381763 1298807 := bstep (se 1 (by rfl) ⟨974105, by rfl⟩ : syracuseStep 1298807 = 1948211) B1948211
theorem B971311 : Blo 381763 971311 := bstep (se 1 (by rfl) ⟨728483, by rfl⟩ : syracuseStep 971311 = 1456967) B1456967
theorem B40555363 : Blo 381763 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B1037215 : Blo 381763 1037215 := bstep (se 1 (by rfl) ⟨777911, by rfl⟩ : syracuseStep 1037215 = 1555823) B1555823
theorem B382079 : Blo 381763 382079 := bstep (se 1 (by rfl) ⟨286559, by rfl⟩ : syracuseStep 382079 = 573119) B573119
theorem B382335 : Blo 381763 382335 := bstep (se 1 (by rfl) ⟨286751, by rfl⟩ : syracuseStep 382335 = 573503) B573503
theorem B1299887 : Blo 381763 1299887 := bstep (se 1 (by rfl) ⟨974915, by rfl⟩ : syracuseStep 1299887 = 1949831) B1949831
theorem B1299995 : Blo 381763 1299995 := bstep (se 1 (by rfl) ⟨974996, by rfl⟩ : syracuseStep 1299995 = 1949993) B1949993
theorem B383003 : Blo 381763 383003 := bstep (se 1 (by rfl) ⟨287252, by rfl⟩ : syracuseStep 383003 = 574505) B574505
theorem B1300535 : Blo 381763 1300535 := bstep (se 1 (by rfl) ⟨975401, by rfl⟩ : syracuseStep 1300535 = 1950803) B1950803
theorem B383039 : Blo 381763 383039 := bstep (se 1 (by rfl) ⟨287279, by rfl⟩ : syracuseStep 383039 = 574559) B574559
theorem B973417 : Blo 381763 973417 := bstep (se 2 (by rfl) ⟨365031, by rfl⟩ : syracuseStep 973417 = 730063) B730063
theorem B383615 : Blo 381763 383615 := bstep (se 1 (by rfl) ⟨287711, by rfl⟩ : syracuseStep 383615 = 575423) B575423
theorem B383935 : Blo 381763 383935 := bstep (se 1 (by rfl) ⟨287951, by rfl⟩ : syracuseStep 383935 = 575903) B575903
theorem B384103 : Blo 381763 384103 := bstep (se 1 (by rfl) ⟨288077, by rfl⟩ : syracuseStep 384103 = 576155) B576155
theorem B384111 : Blo 381763 384111 := bstep (se 1 (by rfl) ⟨288083, by rfl⟩ : syracuseStep 384111 = 576167) B576167
theorem B384127 : Blo 381763 384127 := bstep (se 1 (by rfl) ⟨288095, by rfl⟩ : syracuseStep 384127 = 576191) B576191
theorem B384479 : Blo 381763 384479 := bstep (se 1 (by rfl) ⟨288359, by rfl⟩ : syracuseStep 384479 = 576719) B576719
theorem B384495 : Blo 381763 384495 := bstep (se 1 (by rfl) ⟨288371, by rfl⟩ : syracuseStep 384495 = 576743) B576743
theorem B384667 : Blo 381763 384667 := bstep (se 1 (by rfl) ⟨288500, by rfl⟩ : syracuseStep 384667 = 577001) B577001
theorem B9854621 : Blo 381763 9854621 := bstep (se 3 (by rfl) ⟨1847741, by rfl⟩ : syracuseStep 9854621 = 3695483) B3695483
theorem B384703 : Blo 381763 384703 := bstep (se 1 (by rfl) ⟨288527, by rfl⟩ : syracuseStep 384703 = 577055) B577055
theorem B7364519 : Blo 381763 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B385071 : Blo 381763 385071 := bstep (se 1 (by rfl) ⟨288803, by rfl⟩ : syracuseStep 385071 = 577607) B577607
theorem B385247 : Blo 381763 385247 := bstep (se 1 (by rfl) ⟨288935, by rfl⟩ : syracuseStep 385247 = 577871) B577871
theorem B385263 : Blo 381763 385263 := bstep (se 1 (by rfl) ⟨288947, by rfl⟩ : syracuseStep 385263 = 577895) B577895
theorem B385383 : Blo 381763 385383 := bstep (se 1 (by rfl) ⟨289037, by rfl⟩ : syracuseStep 385383 = 578075) B578075
theorem B1106759 : Blo 381763 1106759 := bstep (se 1 (by rfl) ⟨830069, by rfl⟩ : syracuseStep 1106759 = 1660139) B1660139
theorem B11823137 : Blo 381763 11823137 := bstep (se 2 (by rfl) ⟨4433676, by rfl⟩ : syracuseStep 11823137 = 8867353) B8867353
theorem B3565601 : Blo 381763 3565601 := bstep (se 2 (by rfl) ⟨1337100, by rfl⟩ : syracuseStep 3565601 = 2674201) B2674201
theorem B1632905 : Blo 381763 1632905 := bstep (se 2 (by rfl) ⟨612339, by rfl⟩ : syracuseStep 1632905 = 1224679) B1224679
theorem B1636321 : Blo 381763 1636321 := bstep (se 2 (by rfl) ⟨613620, by rfl⟩ : syracuseStep 1636321 = 1227241) B1227241
theorem B818041 : Blo 381763 818041 := bstep (se 2 (by rfl) ⟨306765, by rfl⟩ : syracuseStep 818041 = 613531) B613531
theorem B1934927 : Blo 381763 1934927 := bstep (se 1 (by rfl) ⟨1451195, by rfl⟩ : syracuseStep 1934927 = 2902391) B2902391
theorem B54073817 : Blo 381763 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B1088603 : Blo 381763 1088603 := bstep (se 1 (by rfl) ⟨816452, by rfl⟩ : syracuseStep 1088603 = 1632905) B1632905
theorem B1842871 : Blo 381763 1842871 := bstep (se 1 (by rfl) ⟨1382153, by rfl⟩ : syracuseStep 1842871 = 2764307) B2764307
theorem B1843361 : Blo 381763 1843361 := bstep (se 2 (by rfl) ⟨691260, by rfl⟩ : syracuseStep 1843361 = 1382521) B1382521
theorem B860435 : Blo 381763 860435 := bstep (se 1 (by rfl) ⟨645326, by rfl⟩ : syracuseStep 860435 = 1290653) B1290653
theorem B1090721 : Blo 381763 1090721 := bstep (se 2 (by rfl) ⟨409020, by rfl⟩ : syracuseStep 1090721 = 818041) B818041
theorem B730451 : Blo 381763 730451 := bstep (se 1 (by rfl) ⟨547838, by rfl⟩ : syracuseStep 730451 = 1095677) B1095677
theorem B862847 : Blo 381763 862847 := bstep (se 1 (by rfl) ⟨647135, by rfl⟩ : syracuseStep 862847 = 1294271) B1294271
theorem B1944971 : Blo 381763 1944971 := bstep (se 1 (by rfl) ⟨1458728, by rfl⟩ : syracuseStep 1944971 = 2917457) B2917457
theorem B6238727 : Blo 381763 6238727 := bstep (se 1 (by rfl) ⟨4679045, by rfl⟩ : syracuseStep 6238727 = 9358091) B9358091
theorem B1290977 : Blo 381763 1290977 := bstep (se 2 (by rfl) ⟨484116, by rfl⟩ : syracuseStep 1290977 = 968233) B968233
theorem B865871 : Blo 381763 865871 := bstep (se 1 (by rfl) ⟨649403, by rfl⟩ : syracuseStep 865871 = 1298807) B1298807
theorem B1292057 : Blo 381763 1292057 := bstep (se 2 (by rfl) ⟨484521, by rfl⟩ : syracuseStep 1292057 = 969043) B969043
theorem B16529345 : Blo 381763 16529345 := bstep (se 2 (by rfl) ⟨6198504, by rfl⟩ : syracuseStep 16529345 = 12397009) B12397009
theorem B1292543 : Blo 381763 1292543 := bstep (se 1 (by rfl) ⟨969407, by rfl⟩ : syracuseStep 1292543 = 1938815) B1938815
theorem B866591 : Blo 381763 866591 := bstep (se 1 (by rfl) ⟨649943, by rfl⟩ : syracuseStep 866591 = 1299887) B1299887
theorem B866663 : Blo 381763 866663 := bstep (se 1 (by rfl) ⟨649997, by rfl⟩ : syracuseStep 866663 = 1299995) B1299995
theorem B867023 : Blo 381763 867023 := bstep (se 1 (by rfl) ⟨650267, by rfl⟩ : syracuseStep 867023 = 1300535) B1300535
theorem B572735 : Blo 381763 572735 := bstep (se 1 (by rfl) ⟨429551, by rfl⟩ : syracuseStep 572735 = 859103) B859103
theorem B572927 : Blo 381763 572927 := bstep (se 1 (by rfl) ⟨429695, by rfl⟩ : syracuseStep 572927 = 859391) B859391
theorem B573065 : Blo 381763 573065 := bstep (se 2 (by rfl) ⟨214899, by rfl⟩ : syracuseStep 573065 = 429799) B429799
theorem B6569747 : Blo 381763 6569747 := bstep (se 1 (by rfl) ⟨4927310, by rfl⟩ : syracuseStep 6569747 = 9854621) B9854621
theorem B638857 : Blo 381763 638857 := bstep (se 2 (by rfl) ⟨239571, by rfl⟩ : syracuseStep 638857 = 479143) B479143
theorem B1294217 : Blo 381763 1294217 := bstep (se 2 (by rfl) ⟨485331, by rfl⟩ : syracuseStep 1294217 = 970663) B970663
theorem B573851 : Blo 381763 573851 := bstep (se 1 (by rfl) ⟨430388, by rfl⟩ : syracuseStep 573851 = 860777) B860777
theorem B737839 : Blo 381763 737839 := bstep (se 1 (by rfl) ⟨553379, by rfl⟩ : syracuseStep 737839 = 1106759) B1106759
theorem B1295081 : Blo 381763 1295081 := bstep (se 2 (by rfl) ⟨485655, by rfl⟩ : syracuseStep 1295081 = 971311) B971311
theorem B7882091 : Blo 381763 7882091 := bstep (se 1 (by rfl) ⟨5911568, by rfl⟩ : syracuseStep 7882091 = 11823137) B11823137
theorem B2377067 : Blo 381763 2377067 := bstep (se 1 (by rfl) ⟨1782800, by rfl⟩ : syracuseStep 2377067 = 3565601) B3565601
theorem B574841 : Blo 381763 574841 := bstep (se 2 (by rfl) ⟨215565, by rfl⟩ : syracuseStep 574841 = 431131) B431131
theorem B574847 : Blo 381763 574847 := bstep (se 1 (by rfl) ⟨431135, by rfl⟩ : syracuseStep 574847 = 862271) B862271
theorem B574955 : Blo 381763 574955 := bstep (se 1 (by rfl) ⟨431216, by rfl⟩ : syracuseStep 574955 = 862433) B862433
theorem B575003 : Blo 381763 575003 := bstep (se 1 (by rfl) ⟨431252, by rfl⟩ : syracuseStep 575003 = 862505) B862505
theorem B10143305 : Blo 381763 10143305 := bstep (se 2 (by rfl) ⟨3803739, by rfl⟩ : syracuseStep 10143305 = 7607479) B7607479
theorem B1296107 : Blo 381763 1296107 := bstep (se 1 (by rfl) ⟨972080, by rfl⟩ : syracuseStep 1296107 = 1944161) B1944161
theorem B575483 : Blo 381763 575483 := bstep (se 1 (by rfl) ⟨431612, by rfl⟩ : syracuseStep 575483 = 863225) B863225
theorem B57657491 : Blo 381763 57657491 := bstep (se 1 (by rfl) ⟨43243118, by rfl⟩ : syracuseStep 57657491 = 86486237) B86486237
theorem B575657 : Blo 381763 575657 := bstep (se 2 (by rfl) ⟨215871, by rfl⟩ : syracuseStep 575657 = 431743) B431743
theorem B969023 : Blo 381763 969023 := bstep (se 1 (by rfl) ⟨726767, by rfl⟩ : syracuseStep 969023 = 1453535) B1453535
theorem B8309303 : Blo 381763 8309303 := bstep (se 1 (by rfl) ⟨6231977, by rfl⟩ : syracuseStep 8309303 = 12463955) B12463955
theorem B2181761 : Blo 381763 2181761 := bstep (se 2 (by rfl) ⟨818160, by rfl⟩ : syracuseStep 2181761 = 1636321) B1636321
theorem B576233 : Blo 381763 576233 := bstep (se 2 (by rfl) ⟨216087, by rfl⟩ : syracuseStep 576233 = 432175) B432175
theorem B576539 : Blo 381763 576539 := bstep (se 1 (by rfl) ⟨432404, by rfl⟩ : syracuseStep 576539 = 864809) B864809
theorem B576809 : Blo 381763 576809 := bstep (se 2 (by rfl) ⟨216303, by rfl⟩ : syracuseStep 576809 = 432607) B432607
theorem B2215363 : Blo 381763 2215363 := bstep (se 1 (by rfl) ⟨1661522, by rfl⟩ : syracuseStep 2215363 = 3323045) B3323045
theorem B1297889 : Blo 381763 1297889 := bstep (se 2 (by rfl) ⟨486708, by rfl⟩ : syracuseStep 1297889 = 973417) B973417
theorem B2215549 : Blo 381763 2215549 := bstep (se 3 (by rfl) ⟨415415, by rfl⟩ : syracuseStep 2215549 = 830831) B830831
theorem B577307 : Blo 381763 577307 := bstep (se 1 (by rfl) ⟨432980, by rfl⟩ : syracuseStep 577307 = 865961) B865961
theorem B577391 : Blo 381763 577391 := bstep (se 1 (by rfl) ⟨433043, by rfl⟩ : syracuseStep 577391 = 866087) B866087
theorem B577439 : Blo 381763 577439 := bstep (se 1 (by rfl) ⟨433079, by rfl⟩ : syracuseStep 577439 = 866159) B866159
theorem B14143427 : Blo 381763 14143427 := bstep (se 1 (by rfl) ⟨10607570, by rfl⟩ : syracuseStep 14143427 = 21215141) B21215141
theorem B577913 : Blo 381763 577913 := bstep (se 2 (by rfl) ⟨216717, by rfl⟩ : syracuseStep 577913 = 433435) B433435
theorem B8835583 : Blo 381763 8835583 := bstep (se 1 (by rfl) ⟨6626687, by rfl⟩ : syracuseStep 8835583 = 13253375) B13253375
theorem B578207 : Blo 381763 578207 := bstep (se 1 (by rfl) ⟨433655, by rfl⟩ : syracuseStep 578207 = 867311) B867311
theorem B381799 : Blo 381763 381799 := bstep (se 1 (by rfl) ⟨286349, by rfl⟩ : syracuseStep 381799 = 572699) B572699
theorem B578537 : Blo 381763 578537 := bstep (se 2 (by rfl) ⟨216951, by rfl⟩ : syracuseStep 578537 = 433903) B433903
theorem B382311 : Blo 381763 382311 := bstep (se 1 (by rfl) ⟨286733, by rfl⟩ : syracuseStep 382311 = 573467) B573467
theorem B382399 : Blo 381763 382399 := bstep (se 1 (by rfl) ⟨286799, by rfl⟩ : syracuseStep 382399 = 573599) B573599
theorem B382911 : Blo 381763 382911 := bstep (se 1 (by rfl) ⟨287183, by rfl⟩ : syracuseStep 382911 = 574367) B574367
theorem B2906279 : Blo 381763 2906279 := bstep (se 1 (by rfl) ⟨2179709, by rfl⟩ : syracuseStep 2906279 = 4359419) B4359419
theorem B383535 : Blo 381763 383535 := bstep (se 1 (by rfl) ⟨287651, by rfl⟩ : syracuseStep 383535 = 575303) B575303
theorem B645887 : Blo 381763 645887 := bstep (se 1 (by rfl) ⟨484415, by rfl⟩ : syracuseStep 645887 = 968831) B968831
theorem B646427 : Blo 381763 646427 := bstep (se 1 (by rfl) ⟨484820, by rfl⟩ : syracuseStep 646427 = 969641) B969641
theorem B1301831 : Blo 381763 1301831 := bstep (se 1 (by rfl) ⟨976373, by rfl⟩ : syracuseStep 1301831 = 1952747) B1952747
theorem B646555 : Blo 381763 646555 := bstep (se 1 (by rfl) ⟨484916, by rfl⟩ : syracuseStep 646555 = 969833) B969833
theorem B2186909 : Blo 381763 2186909 := bstep (se 3 (by rfl) ⟨410045, by rfl⟩ : syracuseStep 2186909 = 820091) B820091
theorem B483175 : Blo 381763 483175 := bstep (se 1 (by rfl) ⟨362381, by rfl⟩ : syracuseStep 483175 = 724763) B724763
theorem B974875 : Blo 381763 974875 := bstep (se 1 (by rfl) ⟨731156, by rfl⟩ : syracuseStep 974875 = 1462313) B1462313
theorem B385115 : Blo 381763 385115 := bstep (se 1 (by rfl) ⟨288836, by rfl⟩ : syracuseStep 385115 = 577673) B577673
theorem B647311 : Blo 381763 647311 := bstep (se 1 (by rfl) ⟨485483, by rfl⟩ : syracuseStep 647311 = 970967) B970967
theorem B2056391 : Blo 381763 2056391 := bstep (se 1 (by rfl) ⟨1542293, by rfl⟩ : syracuseStep 2056391 = 3084587) B3084587
theorem B877031 : Blo 381763 877031 := bstep (se 1 (by rfl) ⟨657773, by rfl⟩ : syracuseStep 877031 = 1315547) B1315547
theorem B10674953 : Blo 381763 10674953 := bstep (se 2 (by rfl) ⟨4003107, by rfl⟩ : syracuseStep 10674953 = 8006215) B8006215
theorem B484967 : Blo 381763 484967 := bstep (se 1 (by rfl) ⟨363725, by rfl⟩ : syracuseStep 484967 = 727451) B727451
theorem B5531813 : Blo 381763 5531813 := bstep (se 4 (by rfl) ⟨518607, by rfl⟩ : syracuseStep 5531813 = 1037215) B1037215
theorem B485615 : Blo 381763 485615 := bstep (se 1 (by rfl) ⟨364211, by rfl⟩ : syracuseStep 485615 = 728423) B728423
theorem B4942073 : Blo 381763 4942073 := bstep (se 2 (by rfl) ⟨1853277, by rfl⟩ : syracuseStep 4942073 = 3706555) B3706555
theorem B2910653 : Blo 381763 2910653 := bstep (se 3 (by rfl) ⟨545747, by rfl⟩ : syracuseStep 2910653 = 1091495) B1091495
theorem B4909679 : Blo 381763 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B1863119 : Blo 381763 1863119 := bstep (se 1 (by rfl) ⟨1397339, by rfl⟩ : syracuseStep 1863119 = 2794679) B2794679
theorem B486911 : Blo 381763 486911 := bstep (se 1 (by rfl) ⟨365183, by rfl⟩ : syracuseStep 486911 = 730367) B730367
theorem B2060329 : Blo 381763 2060329 := bstep (se 2 (by rfl) ⟨772623, by rfl⟩ : syracuseStep 2060329 = 1545247) B1545247
theorem B551580299 : Blo 381763 551580299 := bstep (se 1 (by rfl) ⟨413685224, by rfl⟩ : syracuseStep 551580299 = 827370449) B827370449
theorem B7895231 : Blo 381763 7895231 := bstep (se 1 (by rfl) ⟨5921423, by rfl⟩ : syracuseStep 7895231 = 11842847) B11842847
theorem B1933307 : Blo 381763 1933307 := bstep (se 1 (by rfl) ⟨1449980, by rfl⟩ : syracuseStep 1933307 = 2899961) B2899961
theorem B38438327 : Blo 381763 38438327 := bstep (se 1 (by rfl) ⟨28828745, by rfl⟩ : syracuseStep 38438327 = 57657491) B57657491
theorem B5539535 : Blo 381763 5539535 := bstep (se 1 (by rfl) ⟨4154651, by rfl⟩ : syracuseStep 5539535 = 8309303) B8309303
theorem B3935141 : Blo 381763 3935141 := bstep (se 4 (by rfl) ⟨368919, by rfl⟩ : syracuseStep 3935141 = 737839) B737839
theorem B1937519 : Blo 381763 1937519 := bstep (se 1 (by rfl) ⟨1453139, by rfl⟩ : syracuseStep 1937519 = 2906279) B2906279
theorem B36049211 : Blo 381763 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B430591 : Blo 381763 430591 := bstep (se 1 (by rfl) ⟨322943, by rfl⟩ : syracuseStep 430591 = 645887) B645887
theorem B2953817 : Blo 381763 2953817 := bstep (se 2 (by rfl) ⟨1107681, by rfl⟩ : syracuseStep 2953817 = 2215363) B2215363
theorem B725735 : Blo 381763 725735 := bstep (se 1 (by rfl) ⟨544301, by rfl⟩ : syracuseStep 725735 = 1088603) B1088603
theorem B2954065 : Blo 381763 2954065 := bstep (se 2 (by rfl) ⟨1107774, by rfl⟩ : syracuseStep 2954065 = 2215549) B2215549
theorem B430951 : Blo 381763 430951 := bstep (se 1 (by rfl) ⟨323213, by rfl⟩ : syracuseStep 430951 = 646427) B646427
theorem B7116635 : Blo 381763 7116635 := bstep (se 1 (by rfl) ⟨5337476, by rfl⟩ : syracuseStep 7116635 = 10674953) B10674953
theorem B727147 : Blo 381763 727147 := bstep (se 1 (by rfl) ⟨545360, by rfl⟩ : syracuseStep 727147 = 1090721) B1090721
theorem B1940435 : Blo 381763 1940435 := bstep (se 1 (by rfl) ⟨1455326, by rfl⟩ : syracuseStep 1940435 = 2910653) B2910653
theorem B860651 : Blo 381763 860651 := bstep (se 1 (by rfl) ⟨645488, by rfl⟩ : syracuseStep 860651 = 1290977) B1290977
theorem B861371 : Blo 381763 861371 := bstep (se 1 (by rfl) ⟨646028, by rfl⟩ : syracuseStep 861371 = 1292057) B1292057
theorem B11019563 : Blo 381763 11019563 := bstep (se 1 (by rfl) ⟨8264672, by rfl⟩ : syracuseStep 11019563 = 16529345) B16529345
theorem B861695 : Blo 381763 861695 := bstep (se 1 (by rfl) ⟨646271, by rfl⟩ : syracuseStep 861695 = 1292543) B1292543
theorem B862073 : Blo 381763 862073 := bstep (se 2 (by rfl) ⟨323277, by rfl⟩ : syracuseStep 862073 = 646555) B646555
theorem B862811 : Blo 381763 862811 := bstep (se 1 (by rfl) ⟨647108, by rfl⟩ : syracuseStep 862811 = 1294217) B1294217
theorem B1288871 : Blo 381763 1288871 := bstep (se 1 (by rfl) ⟨966653, by rfl⟩ : syracuseStep 1288871 = 1933307) B1933307
theorem B863081 : Blo 381763 863081 := bstep (se 2 (by rfl) ⟨323655, by rfl⟩ : syracuseStep 863081 = 647311) B647311
theorem B863387 : Blo 381763 863387 := bstep (se 1 (by rfl) ⟨647540, by rfl⟩ : syracuseStep 863387 = 1295081) B1295081
theorem B5254727 : Blo 381763 5254727 := bstep (se 1 (by rfl) ⟨3941045, by rfl⟩ : syracuseStep 5254727 = 7882091) B7882091
theorem B6762203 : Blo 381763 6762203 := bstep (se 1 (by rfl) ⟨5071652, by rfl⟩ : syracuseStep 6762203 = 10143305) B10143305
theorem B1289951 : Blo 381763 1289951 := bstep (se 1 (by rfl) ⟨967463, by rfl⟩ : syracuseStep 1289951 = 1934927) B1934927
theorem B864071 : Blo 381763 864071 := bstep (se 1 (by rfl) ⟨648053, by rfl⟩ : syracuseStep 864071 = 1296107) B1296107
theorem B1454507 : Blo 381763 1454507 := bstep (se 1 (by rfl) ⟨1090880, by rfl⟩ : syracuseStep 1454507 = 2181761) B2181761
theorem B865259 : Blo 381763 865259 := bstep (se 1 (by rfl) ⟨648944, by rfl⟩ : syracuseStep 865259 = 1297889) B1297889
theorem B6338845 : Blo 381763 6338845 := bstep (se 3 (by rfl) ⟨1188533, by rfl⟩ : syracuseStep 6338845 = 2377067) B2377067
theorem B1293245 : Blo 381763 1293245 := bstep (se 3 (by rfl) ⟨242483, by rfl⟩ : syracuseStep 1293245 = 484967) B484967
theorem B867887 : Blo 381763 867887 := bstep (se 1 (by rfl) ⟨650915, by rfl⟩ : syracuseStep 867887 = 1301831) B1301831
theorem B1457939 : Blo 381763 1457939 := bstep (se 1 (by rfl) ⟨1093454, by rfl⟩ : syracuseStep 1457939 = 2186909) B2186909
theorem B1228907 : Blo 381763 1228907 := bstep (se 1 (by rfl) ⟨921680, by rfl⟩ : syracuseStep 1228907 = 1843361) B1843361
theorem B573623 : Blo 381763 573623 := bstep (se 1 (by rfl) ⟨430217, by rfl⟩ : syracuseStep 573623 = 860435) B860435
theorem B1294973 : Blo 381763 1294973 := bstep (se 3 (by rfl) ⟨242807, by rfl⟩ : syracuseStep 1294973 = 485615) B485615
theorem B11780777 : Blo 381763 11780777 := bstep (se 2 (by rfl) ⟨4417791, by rfl⟩ : syracuseStep 11780777 = 8835583) B8835583
theorem B3687875 : Blo 381763 3687875 := bstep (se 1 (by rfl) ⟨2765906, by rfl⟩ : syracuseStep 3687875 = 5531813) B5531813
theorem B3294715 : Blo 381763 3294715 := bstep (se 1 (by rfl) ⟨2471036, by rfl⟩ : syracuseStep 3294715 = 4942073) B4942073
theorem B575231 : Blo 381763 575231 := bstep (se 1 (by rfl) ⟨431423, by rfl⟩ : syracuseStep 575231 = 862847) B862847
theorem B1296647 : Blo 381763 1296647 := bstep (se 1 (by rfl) ⟨972485, by rfl⟩ : syracuseStep 1296647 = 1944971) B1944971
theorem B577247 : Blo 381763 577247 := bstep (se 1 (by rfl) ⟨432935, by rfl⟩ : syracuseStep 577247 = 865871) B865871
theorem B4968317 : Blo 381763 4968317 := bstep (se 3 (by rfl) ⟨931559, by rfl⟩ : syracuseStep 4968317 = 1863119) B1863119
theorem B1298429 : Blo 381763 1298429 := bstep (se 3 (by rfl) ⟨243455, by rfl⟩ : syracuseStep 1298429 = 486911) B486911
theorem B5263487 : Blo 381763 5263487 := bstep (se 1 (by rfl) ⟨3947615, by rfl⟩ : syracuseStep 5263487 = 7895231) B7895231
theorem B577727 : Blo 381763 577727 := bstep (se 1 (by rfl) ⟨433295, by rfl⟩ : syracuseStep 577727 = 866591) B866591
theorem B577775 : Blo 381763 577775 := bstep (se 1 (by rfl) ⟨433331, by rfl⟩ : syracuseStep 577775 = 866663) B866663
theorem B578015 : Blo 381763 578015 := bstep (se 1 (by rfl) ⟨433511, by rfl⟩ : syracuseStep 578015 = 867023) B867023
theorem B381823 : Blo 381763 381823 := bstep (se 1 (by rfl) ⟨286367, by rfl⟩ : syracuseStep 381823 = 572735) B572735
theorem B381951 : Blo 381763 381951 := bstep (se 1 (by rfl) ⟨286463, by rfl⟩ : syracuseStep 381951 = 572927) B572927
theorem B382043 : Blo 381763 382043 := bstep (se 1 (by rfl) ⟨286532, by rfl⟩ : syracuseStep 382043 = 573065) B573065
theorem B644233 : Blo 381763 644233 := bstep (se 2 (by rfl) ⟨241587, by rfl⟩ : syracuseStep 644233 = 483175) B483175
theorem B4379831 : Blo 381763 4379831 := bstep (se 1 (by rfl) ⟨3284873, by rfl⟩ : syracuseStep 4379831 = 6569747) B6569747
theorem B1299833 : Blo 381763 1299833 := bstep (se 2 (by rfl) ⟨487437, by rfl⟩ : syracuseStep 1299833 = 974875) B974875
theorem B382567 : Blo 381763 382567 := bstep (se 1 (by rfl) ⟨286925, by rfl⟩ : syracuseStep 382567 = 573851) B573851
theorem B383227 : Blo 381763 383227 := bstep (se 1 (by rfl) ⟨287420, by rfl⟩ : syracuseStep 383227 = 574841) B574841
theorem B383231 : Blo 381763 383231 := bstep (se 1 (by rfl) ⟨287423, by rfl⟩ : syracuseStep 383231 = 574847) B574847
theorem B383303 : Blo 381763 383303 := bstep (se 1 (by rfl) ⟨287477, by rfl⟩ : syracuseStep 383303 = 574955) B574955
theorem B383335 : Blo 381763 383335 := bstep (se 1 (by rfl) ⟨287501, by rfl⟩ : syracuseStep 383335 = 575003) B575003
theorem B383655 : Blo 381763 383655 := bstep (se 1 (by rfl) ⟨287741, by rfl⟩ : syracuseStep 383655 = 575483) B575483
theorem B383771 : Blo 381763 383771 := bstep (se 1 (by rfl) ⟨287828, by rfl⟩ : syracuseStep 383771 = 575657) B575657
theorem B646015 : Blo 381763 646015 := bstep (se 1 (by rfl) ⟨484511, by rfl⟩ : syracuseStep 646015 = 969023) B969023
theorem B384155 : Blo 381763 384155 := bstep (se 1 (by rfl) ⟨288116, by rfl⟩ : syracuseStep 384155 = 576233) B576233
theorem B384359 : Blo 381763 384359 := bstep (se 1 (by rfl) ⟨288269, by rfl⟩ : syracuseStep 384359 = 576539) B576539
theorem B384539 : Blo 381763 384539 := bstep (se 1 (by rfl) ⟨288404, by rfl⟩ : syracuseStep 384539 = 576809) B576809
theorem B384871 : Blo 381763 384871 := bstep (se 1 (by rfl) ⟨288653, by rfl⟩ : syracuseStep 384871 = 577307) B577307
theorem B384927 : Blo 381763 384927 := bstep (se 1 (by rfl) ⟨288695, by rfl⟩ : syracuseStep 384927 = 577391) B577391
theorem B384959 : Blo 381763 384959 := bstep (se 1 (by rfl) ⟨288719, by rfl⟩ : syracuseStep 384959 = 577439) B577439
theorem B9428951 : Blo 381763 9428951 := bstep (se 1 (by rfl) ⟨7071713, by rfl⟩ : syracuseStep 9428951 = 14143427) B14143427
theorem B385275 : Blo 381763 385275 := bstep (se 1 (by rfl) ⟨288956, by rfl⟩ : syracuseStep 385275 = 577913) B577913
theorem B385471 : Blo 381763 385471 := bstep (se 1 (by rfl) ⟨289103, by rfl⟩ : syracuseStep 385471 = 578207) B578207
theorem B385691 : Blo 381763 385691 := bstep (se 1 (by rfl) ⟨289268, by rfl⟩ : syracuseStep 385691 = 578537) B578537
theorem B2747105 : Blo 381763 2747105 := bstep (se 2 (by rfl) ⟨1030164, by rfl⟩ : syracuseStep 2747105 = 2060329) B2060329
theorem B1370927 : Blo 381763 1370927 := bstep (se 1 (by rfl) ⟨1028195, by rfl⟩ : syracuseStep 1370927 = 2056391) B2056391
theorem B584687 : Blo 381763 584687 := bstep (se 1 (by rfl) ⟨438515, by rfl⟩ : syracuseStep 584687 = 877031) B877031
theorem B486967 : Blo 381763 486967 := bstep (se 1 (by rfl) ⟨365225, by rfl⟩ : syracuseStep 486967 = 730451) B730451
theorem B3273119 : Blo 381763 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B4159151 : Blo 381763 4159151 := bstep (se 1 (by rfl) ⟨3119363, by rfl⟩ : syracuseStep 4159151 = 6238727) B6238727
theorem B367720199 : Blo 381763 367720199 := bstep (se 1 (by rfl) ⟨275790149, by rfl⟩ : syracuseStep 367720199 = 551580299) B551580299
theorem B2457161 : Blo 381763 2457161 := bstep (se 2 (by rfl) ⟨921435, by rfl⟩ : syracuseStep 2457161 = 1842871) B1842871
theorem B851809 : Blo 381763 851809 := bstep (se 2 (by rfl) ⟨319428, by rfl⟩ : syracuseStep 851809 = 638857) B638857
theorem B819271 : Blo 381763 819271 := bstep (se 1 (by rfl) ⟨614453, by rfl⟩ : syracuseStep 819271 = 1228907) B1228907
theorem B2458583 : Blo 381763 2458583 := bstep (se 1 (by rfl) ⟨1843937, by rfl⟩ : syracuseStep 2458583 = 3687875) B3687875
theorem B2623427 : Blo 381763 2623427 := bstep (se 1 (by rfl) ⟨1967570, by rfl⟩ : syracuseStep 2623427 = 3935141) B3935141
theorem B4392953 : Blo 381763 4392953 := bstep (se 2 (by rfl) ⟨1647357, by rfl⟩ : syracuseStep 4392953 = 3294715) B3294715
theorem B3508991 : Blo 381763 3508991 := bstep (se 1 (by rfl) ⟨2631743, by rfl⟩ : syracuseStep 3508991 = 5263487) B5263487
theorem B1969211 : Blo 381763 1969211 := bstep (se 1 (by rfl) ⟨1476908, by rfl⟩ : syracuseStep 1969211 = 2953817) B2953817
theorem B2919887 : Blo 381763 2919887 := bstep (se 1 (by rfl) ⟨2189915, by rfl⟩ : syracuseStep 2919887 = 4379831) B4379831
theorem B102502205 : Blo 381763 102502205 := bstep (se 3 (by rfl) ⟨19219163, by rfl⟩ : syracuseStep 102502205 = 38438327) B38438327
theorem B7346375 : Blo 381763 7346375 := bstep (se 1 (by rfl) ⟨5509781, by rfl⟩ : syracuseStep 7346375 = 11019563) B11019563
theorem B3938753 : Blo 381763 3938753 := bstep (se 2 (by rfl) ⟨1477032, by rfl⟩ : syracuseStep 3938753 = 2954065) B2954065
theorem B858977 : Blo 381763 858977 := bstep (se 2 (by rfl) ⟨322116, by rfl⟩ : syracuseStep 858977 = 644233) B644233
theorem B859247 : Blo 381763 859247 := bstep (se 1 (by rfl) ⟨644435, by rfl⟩ : syracuseStep 859247 = 1288871) B1288871
theorem B859967 : Blo 381763 859967 := bstep (se 1 (by rfl) ⟨644975, by rfl⟩ : syracuseStep 859967 = 1289951) B1289951
theorem B861353 : Blo 381763 861353 := bstep (se 2 (by rfl) ⟨323007, by rfl⟩ : syracuseStep 861353 = 646015) B646015
theorem B245146799 : Blo 381763 245146799 := bstep (se 1 (by rfl) ⟨183860099, by rfl⟩ : syracuseStep 245146799 = 367720199) B367720199
theorem B862163 : Blo 381763 862163 := bstep (se 1 (by rfl) ⟨646622, by rfl⟩ : syracuseStep 862163 = 1293245) B1293245
theorem B13248845 : Blo 381763 13248845 := bstep (se 3 (by rfl) ⟨2484158, by rfl⟩ : syracuseStep 13248845 = 4968317) B4968317
theorem B863315 : Blo 381763 863315 := bstep (se 1 (by rfl) ⟨647486, by rfl⟩ : syracuseStep 863315 = 1294973) B1294973
theorem B864431 : Blo 381763 864431 := bstep (se 1 (by rfl) ⟨648323, by rfl⟩ : syracuseStep 864431 = 1296647) B1296647
theorem B865619 : Blo 381763 865619 := bstep (se 1 (by rfl) ⟨649214, by rfl⟩ : syracuseStep 865619 = 1298429) B1298429
theorem B1291679 : Blo 381763 1291679 := bstep (se 1 (by rfl) ⟨968759, by rfl⟩ : syracuseStep 1291679 = 1937519) B1937519
theorem B24032807 : Blo 381763 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B866555 : Blo 381763 866555 := bstep (se 1 (by rfl) ⟨649916, by rfl⟩ : syracuseStep 866555 = 1299833) B1299833
theorem B1293623 : Blo 381763 1293623 := bstep (se 1 (by rfl) ⟨970217, by rfl⟩ : syracuseStep 1293623 = 1940435) B1940435
theorem B573767 : Blo 381763 573767 := bstep (se 1 (by rfl) ⟨430325, by rfl⟩ : syracuseStep 573767 = 860651) B860651
theorem B574121 : Blo 381763 574121 := bstep (se 2 (by rfl) ⟨215295, by rfl⟩ : syracuseStep 574121 = 430591) B430591
theorem B574247 : Blo 381763 574247 := bstep (se 1 (by rfl) ⟨430685, by rfl⟩ : syracuseStep 574247 = 861371) B861371
theorem B574463 : Blo 381763 574463 := bstep (se 1 (by rfl) ⟨430847, by rfl⟩ : syracuseStep 574463 = 861695) B861695
theorem B574601 : Blo 381763 574601 := bstep (se 2 (by rfl) ⟨215475, by rfl⟩ : syracuseStep 574601 = 430951) B430951
theorem B574715 : Blo 381763 574715 := bstep (se 1 (by rfl) ⟨431036, by rfl⟩ : syracuseStep 574715 = 862073) B862073
theorem B575207 : Blo 381763 575207 := bstep (se 1 (by rfl) ⟨431405, by rfl⟩ : syracuseStep 575207 = 862811) B862811
theorem B575387 : Blo 381763 575387 := bstep (se 1 (by rfl) ⟨431540, by rfl⟩ : syracuseStep 575387 = 863081) B863081
theorem B575591 : Blo 381763 575591 := bstep (se 1 (by rfl) ⟨431693, by rfl⟩ : syracuseStep 575591 = 863387) B863387
theorem B4508135 : Blo 381763 4508135 := bstep (se 1 (by rfl) ⟨3381101, by rfl⟩ : syracuseStep 4508135 = 6762203) B6762203
theorem B576047 : Blo 381763 576047 := bstep (se 1 (by rfl) ⟨432035, by rfl⟩ : syracuseStep 576047 = 864071) B864071
theorem B969529 : Blo 381763 969529 := bstep (se 2 (by rfl) ⟨363573, by rfl⟩ : syracuseStep 969529 = 727147) B727147
theorem B2182079 : Blo 381763 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B969671 : Blo 381763 969671 := bstep (se 1 (by rfl) ⟨727253, by rfl⟩ : syracuseStep 969671 = 1454507) B1454507
theorem B576839 : Blo 381763 576839 := bstep (se 1 (by rfl) ⟨432629, by rfl⟩ : syracuseStep 576839 = 865259) B865259
theorem B2772767 : Blo 381763 2772767 := bstep (se 1 (by rfl) ⟨2079575, by rfl⟩ : syracuseStep 2772767 = 4159151) B4159151
theorem B14012605 : Blo 381763 14012605 := bstep (se 3 (by rfl) ⟨2627363, by rfl⟩ : syracuseStep 14012605 = 5254727) B5254727
theorem B578591 : Blo 381763 578591 := bstep (se 1 (by rfl) ⟨433943, by rfl⟩ : syracuseStep 578591 = 867887) B867887
theorem B1135745 : Blo 381763 1135745 := bstep (se 2 (by rfl) ⟨425904, by rfl⟩ : syracuseStep 1135745 = 851809) B851809
theorem B971959 : Blo 381763 971959 := bstep (se 1 (by rfl) ⟨728969, by rfl⟩ : syracuseStep 971959 = 1457939) B1457939
theorem B382415 : Blo 381763 382415 := bstep (se 1 (by rfl) ⟨286811, by rfl⟩ : syracuseStep 382415 = 573623) B573623
theorem B7853851 : Blo 381763 7853851 := bstep (se 1 (by rfl) ⟨5890388, by rfl⟩ : syracuseStep 7853851 = 11780777) B11780777
theorem B3693023 : Blo 381763 3693023 := bstep (se 1 (by rfl) ⟨2769767, by rfl⟩ : syracuseStep 3693023 = 5539535) B5539535
theorem B383487 : Blo 381763 383487 := bstep (se 1 (by rfl) ⟨287615, by rfl⟩ : syracuseStep 383487 = 575231) B575231
theorem B384831 : Blo 381763 384831 := bstep (se 1 (by rfl) ⟨288623, by rfl⟩ : syracuseStep 384831 = 577247) B577247
theorem B385151 : Blo 381763 385151 := bstep (se 1 (by rfl) ⟨288863, by rfl⟩ : syracuseStep 385151 = 577727) B577727
theorem B385183 : Blo 381763 385183 := bstep (se 1 (by rfl) ⟨288887, by rfl⟩ : syracuseStep 385183 = 577775) B577775
theorem B385343 : Blo 381763 385343 := bstep (se 1 (by rfl) ⟨289007, by rfl⟩ : syracuseStep 385343 = 578015) B578015
theorem B483823 : Blo 381763 483823 := bstep (se 1 (by rfl) ⟨362867, by rfl⟩ : syracuseStep 483823 = 725735) B725735
theorem B4744423 : Blo 381763 4744423 := bstep (se 1 (by rfl) ⟨3558317, by rfl⟩ : syracuseStep 4744423 = 7116635) B7116635
theorem B649289 : Blo 381763 649289 := bstep (se 2 (by rfl) ⟨243483, by rfl⟩ : syracuseStep 649289 = 486967) B486967
theorem B6285967 : Blo 381763 6285967 := bstep (se 1 (by rfl) ⟨4714475, by rfl⟩ : syracuseStep 6285967 = 9428951) B9428951
theorem B1831403 : Blo 381763 1831403 := bstep (se 1 (by rfl) ⟨1373552, by rfl⟩ : syracuseStep 1831403 = 2747105) B2747105
theorem B913951 : Blo 381763 913951 := bstep (se 1 (by rfl) ⟨685463, by rfl⟩ : syracuseStep 913951 = 1370927) B1370927
theorem B389791 : Blo 381763 389791 := bstep (se 1 (by rfl) ⟨292343, by rfl⟩ : syracuseStep 389791 = 584687) B584687
theorem B8451793 : Blo 381763 8451793 := bstep (se 2 (by rfl) ⟨3169422, by rfl⟩ : syracuseStep 8451793 = 6338845) B6338845
theorem B1638107 : Blo 381763 1638107 := bstep (se 1 (by rfl) ⟨1228580, by rfl⟩ : syracuseStep 1638107 = 2457161) B2457161
theorem B1639055 : Blo 381763 1639055 := bstep (se 1 (by rfl) ⟨1229291, by rfl⟩ : syracuseStep 1639055 = 2458583) B2458583
theorem B6325897 : Blo 381763 6325897 := bstep (se 2 (by rfl) ⟨2372211, by rfl⟩ : syracuseStep 6325897 = 4744423) B4744423
theorem B2462015 : Blo 381763 2462015 := bstep (se 1 (by rfl) ⟨1846511, by rfl⟩ : syracuseStep 2462015 = 3693023) B3693023
theorem B18683473 : Blo 381763 18683473 := bstep (se 2 (by rfl) ⟨7006302, by rfl⟩ : syracuseStep 18683473 = 14012605) B14012605
theorem B1218601 : Blo 381763 1218601 := bstep (se 2 (by rfl) ⟨456975, by rfl⟩ : syracuseStep 1218601 = 913951) B913951
theorem B432859 : Blo 381763 432859 := bstep (se 1 (by rfl) ⟨324644, by rfl⟩ : syracuseStep 432859 = 649289) B649289
theorem B5251229 : Blo 381763 5251229 := bstep (se 3 (by rfl) ⟨984605, by rfl⟩ : syracuseStep 5251229 = 1969211) B1969211
theorem B1220935 : Blo 381763 1220935 := bstep (se 1 (by rfl) ⟨915701, by rfl⟩ : syracuseStep 1220935 = 1831403) B1831403
theorem B861119 : Blo 381763 861119 := bstep (se 1 (by rfl) ⟨645839, by rfl⟩ : syracuseStep 861119 = 1291679) B1291679
theorem B862415 : Blo 381763 862415 := bstep (se 1 (by rfl) ⟨646811, by rfl⟩ : syracuseStep 862415 = 1293623) B1293623
theorem B1092071 : Blo 381763 1092071 := bstep (se 1 (by rfl) ⟨819053, by rfl⟩ : syracuseStep 1092071 = 1638107) B1638107
theorem B1092361 : Blo 381763 1092361 := bstep (se 2 (by rfl) ⟨409635, by rfl⟩ : syracuseStep 1092361 = 819271) B819271
theorem B1748951 : Blo 381763 1748951 := bstep (se 1 (by rfl) ⟨1311713, by rfl⟩ : syracuseStep 1748951 = 2623427) B2623427
theorem B2928635 : Blo 381763 2928635 := bstep (se 1 (by rfl) ⟨2196476, by rfl⟩ : syracuseStep 2928635 = 4392953) B4392953
theorem B2339327 : Blo 381763 2339327 := bstep (se 1 (by rfl) ⟨1754495, by rfl⟩ : syracuseStep 2339327 = 3508991) B3508991
theorem B1454719 : Blo 381763 1454719 := bstep (se 1 (by rfl) ⟨1091039, by rfl⟩ : syracuseStep 1454719 = 2182079) B2182079
theorem B1946591 : Blo 381763 1946591 := bstep (se 1 (by rfl) ⟨1459943, by rfl⟩ : syracuseStep 1946591 = 2919887) B2919887
theorem B1848511 : Blo 381763 1848511 := bstep (se 1 (by rfl) ⟨1386383, by rfl⟩ : syracuseStep 1848511 = 2772767) B2772767
theorem B68334803 : Blo 381763 68334803 := bstep (se 1 (by rfl) ⟨51251102, by rfl⟩ : syracuseStep 68334803 = 102502205) B102502205
theorem B134100629 : Blo 381763 134100629 := bstep (se 6 (by rfl) ⟨3142983, by rfl⟩ : syracuseStep 134100629 = 6285967) B6285967
theorem B2078885 : Blo 381763 2078885 := bstep (se 4 (by rfl) ⟨194895, by rfl⟩ : syracuseStep 2078885 = 389791) B389791
theorem B1292705 : Blo 381763 1292705 := bstep (se 2 (by rfl) ⟨484764, by rfl⟩ : syracuseStep 1292705 = 969529) B969529
theorem B4897583 : Blo 381763 4897583 := bstep (se 1 (by rfl) ⟨3673187, by rfl⟩ : syracuseStep 4897583 = 7346375) B7346375
theorem B572651 : Blo 381763 572651 := bstep (se 1 (by rfl) ⟨429488, by rfl⟩ : syracuseStep 572651 = 858977) B858977
theorem B572831 : Blo 381763 572831 := bstep (se 1 (by rfl) ⟨429623, by rfl⟩ : syracuseStep 572831 = 859247) B859247
theorem B573311 : Blo 381763 573311 := bstep (se 1 (by rfl) ⟨429983, by rfl⟩ : syracuseStep 573311 = 859967) B859967
theorem B574235 : Blo 381763 574235 := bstep (se 1 (by rfl) ⟨430676, by rfl⟩ : syracuseStep 574235 = 861353) B861353
theorem B163431199 : Blo 381763 163431199 := bstep (se 1 (by rfl) ⟨122573399, by rfl⟩ : syracuseStep 163431199 = 245146799) B245146799
theorem B10503341 : Blo 381763 10503341 := bstep (se 3 (by rfl) ⟨1969376, by rfl⟩ : syracuseStep 10503341 = 3938753) B3938753
theorem B574775 : Blo 381763 574775 := bstep (se 1 (by rfl) ⟨431081, by rfl⟩ : syracuseStep 574775 = 862163) B862163
theorem B8832563 : Blo 381763 8832563 := bstep (se 1 (by rfl) ⟨6624422, by rfl⟩ : syracuseStep 8832563 = 13248845) B13248845
theorem B1295945 : Blo 381763 1295945 := bstep (se 2 (by rfl) ⟨485979, by rfl⟩ : syracuseStep 1295945 = 971959) B971959
theorem B575543 : Blo 381763 575543 := bstep (se 1 (by rfl) ⟨431657, by rfl⟩ : syracuseStep 575543 = 863315) B863315
theorem B10471801 : Blo 381763 10471801 := bstep (se 2 (by rfl) ⟨3926925, by rfl⟩ : syracuseStep 10471801 = 7853851) B7853851
theorem B576287 : Blo 381763 576287 := bstep (se 1 (by rfl) ⟨432215, by rfl⟩ : syracuseStep 576287 = 864431) B864431
theorem B577079 : Blo 381763 577079 := bstep (se 1 (by rfl) ⟨432809, by rfl⟩ : syracuseStep 577079 = 865619) B865619
theorem B577703 : Blo 381763 577703 := bstep (se 1 (by rfl) ⟨433277, by rfl⟩ : syracuseStep 577703 = 866555) B866555
theorem B382511 : Blo 381763 382511 := bstep (se 1 (by rfl) ⟨286883, by rfl⟩ : syracuseStep 382511 = 573767) B573767
theorem B382747 : Blo 381763 382747 := bstep (se 1 (by rfl) ⟨287060, by rfl⟩ : syracuseStep 382747 = 574121) B574121
theorem B382831 : Blo 381763 382831 := bstep (se 1 (by rfl) ⟨287123, by rfl⟩ : syracuseStep 382831 = 574247) B574247
theorem B645097 : Blo 381763 645097 := bstep (se 2 (by rfl) ⟨241911, by rfl⟩ : syracuseStep 645097 = 483823) B483823
theorem B382975 : Blo 381763 382975 := bstep (se 1 (by rfl) ⟨287231, by rfl⟩ : syracuseStep 382975 = 574463) B574463
theorem B383067 : Blo 381763 383067 := bstep (se 1 (by rfl) ⟨287300, by rfl⟩ : syracuseStep 383067 = 574601) B574601
theorem B383143 : Blo 381763 383143 := bstep (se 1 (by rfl) ⟨287357, by rfl⟩ : syracuseStep 383143 = 574715) B574715
theorem B383471 : Blo 381763 383471 := bstep (se 1 (by rfl) ⟨287603, by rfl⟩ : syracuseStep 383471 = 575207) B575207
theorem B383591 : Blo 381763 383591 := bstep (se 1 (by rfl) ⟨287693, by rfl⟩ : syracuseStep 383591 = 575387) B575387
theorem B12114613 : Blo 381763 12114613 := bstep (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) B1135745
theorem B383727 : Blo 381763 383727 := bstep (se 1 (by rfl) ⟨287795, by rfl⟩ : syracuseStep 383727 = 575591) B575591
theorem B3005423 : Blo 381763 3005423 := bstep (se 1 (by rfl) ⟨2254067, by rfl⟩ : syracuseStep 3005423 = 4508135) B4508135
theorem B384031 : Blo 381763 384031 := bstep (se 1 (by rfl) ⟨288023, by rfl⟩ : syracuseStep 384031 = 576047) B576047
theorem B646447 : Blo 381763 646447 := bstep (se 1 (by rfl) ⟨484835, by rfl⟩ : syracuseStep 646447 = 969671) B969671
theorem B384559 : Blo 381763 384559 := bstep (se 1 (by rfl) ⟨288419, by rfl⟩ : syracuseStep 384559 = 576839) B576839
theorem B385727 : Blo 381763 385727 := bstep (se 1 (by rfl) ⟨289295, by rfl⟩ : syracuseStep 385727 = 578591) B578591
theorem B11269057 : Blo 381763 11269057 := bstep (se 2 (by rfl) ⟨4225896, by rfl⟩ : syracuseStep 11269057 = 8451793) B8451793
theorem B16021871 : Blo 381763 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B217908265 : Blo 381763 217908265 := bstep (se 2 (by rfl) ⟨81715599, by rfl⟩ : syracuseStep 217908265 = 163431199) B163431199
theorem B13962401 : Blo 381763 13962401 := bstep (se 2 (by rfl) ⟨5235900, by rfl⟩ : syracuseStep 13962401 = 10471801) B10471801
theorem B2003615 : Blo 381763 2003615 := bstep (se 1 (by rfl) ⟨1502711, by rfl⟩ : syracuseStep 2003615 = 3005423) B3005423
theorem B1939625 : Blo 381763 1939625 := bstep (se 2 (by rfl) ⟨727359, by rfl⟩ : syracuseStep 1939625 = 1454719) B1454719
theorem B2464681 : Blo 381763 2464681 := bstep (se 2 (by rfl) ⟨924255, by rfl⟩ : syracuseStep 2464681 = 1848511) B1848511
theorem B728047 : Blo 381763 728047 := bstep (se 1 (by rfl) ⟨546035, by rfl⟩ : syracuseStep 728047 = 1092071) B1092071
theorem B24911297 : Blo 381763 24911297 := bstep (se 2 (by rfl) ⟨9341736, by rfl⟩ : syracuseStep 24911297 = 18683473) B18683473
theorem B860129 : Blo 381763 860129 := bstep (se 2 (by rfl) ⟨322548, by rfl⟩ : syracuseStep 860129 = 645097) B645097
theorem B45556535 : Blo 381763 45556535 := bstep (se 1 (by rfl) ⟨34167401, by rfl⟩ : syracuseStep 45556535 = 68334803) B68334803
theorem B89400419 : Blo 381763 89400419 := bstep (se 1 (by rfl) ⟨67050314, by rfl⟩ : syracuseStep 89400419 = 134100629) B134100629
theorem B1385923 : Blo 381763 1385923 := bstep (se 1 (by rfl) ⟨1039442, by rfl⟩ : syracuseStep 1385923 = 2078885) B2078885
theorem B861803 : Blo 381763 861803 := bstep (se 1 (by rfl) ⟨646352, by rfl⟩ : syracuseStep 861803 = 1292705) B1292705
theorem B861929 : Blo 381763 861929 := bstep (se 2 (by rfl) ⟨323223, by rfl⟩ : syracuseStep 861929 = 646447) B646447
theorem B1092703 : Blo 381763 1092703 := bstep (se 1 (by rfl) ⟨819527, by rfl⟩ : syracuseStep 1092703 = 1639055) B1639055
theorem B6565373 : Blo 381763 6565373 := bstep (se 3 (by rfl) ⟨1231007, by rfl⟩ : syracuseStep 6565373 = 2462015) B2462015
theorem B863963 : Blo 381763 863963 := bstep (se 1 (by rfl) ⟨647972, by rfl⟩ : syracuseStep 863963 = 1295945) B1295945
theorem B6238205 : Blo 381763 6238205 := bstep (se 3 (by rfl) ⟨1169663, by rfl⟩ : syracuseStep 6238205 = 2339327) B2339327
theorem B8434529 : Blo 381763 8434529 := bstep (se 2 (by rfl) ⟨3162948, by rfl⟩ : syracuseStep 8434529 = 6325897) B6325897
theorem B1456481 : Blo 381763 1456481 := bstep (se 2 (by rfl) ⟨546180, by rfl⟩ : syracuseStep 1456481 = 1092361) B1092361
theorem B574079 : Blo 381763 574079 := bstep (se 1 (by rfl) ⟨430559, by rfl⟩ : syracuseStep 574079 = 861119) B861119
theorem B15025409 : Blo 381763 15025409 := bstep (se 2 (by rfl) ⟨5634528, by rfl⟩ : syracuseStep 15025409 = 11269057) B11269057
theorem B574943 : Blo 381763 574943 := bstep (se 1 (by rfl) ⟨431207, by rfl⟩ : syracuseStep 574943 = 862415) B862415
theorem B1165967 : Blo 381763 1165967 := bstep (se 1 (by rfl) ⟨874475, by rfl⟩ : syracuseStep 1165967 = 1748951) B1748951
theorem B1952423 : Blo 381763 1952423 := bstep (se 1 (by rfl) ⟨1464317, by rfl⟩ : syracuseStep 1952423 = 2928635) B2928635
theorem B1624801 : Blo 381763 1624801 := bstep (se 2 (by rfl) ⟨609300, by rfl⟩ : syracuseStep 1624801 = 1218601) B1218601
theorem B1297727 : Blo 381763 1297727 := bstep (se 1 (by rfl) ⟨973295, by rfl⟩ : syracuseStep 1297727 = 1946591) B1946591
theorem B577145 : Blo 381763 577145 := bstep (se 2 (by rfl) ⟨216429, by rfl⟩ : syracuseStep 577145 = 432859) B432859
theorem B3265055 : Blo 381763 3265055 := bstep (se 1 (by rfl) ⟨2448791, by rfl⟩ : syracuseStep 3265055 = 4897583) B4897583
theorem B381767 : Blo 381763 381767 := bstep (se 1 (by rfl) ⟨286325, by rfl⟩ : syracuseStep 381767 = 572651) B572651
theorem B381887 : Blo 381763 381887 := bstep (se 1 (by rfl) ⟨286415, by rfl⟩ : syracuseStep 381887 = 572831) B572831
theorem B382207 : Blo 381763 382207 := bstep (se 1 (by rfl) ⟨286655, by rfl⟩ : syracuseStep 382207 = 573311) B573311
theorem B1627913 : Blo 381763 1627913 := bstep (se 2 (by rfl) ⟨610467, by rfl⟩ : syracuseStep 1627913 = 1220935) B1220935
theorem B382823 : Blo 381763 382823 := bstep (se 1 (by rfl) ⟨287117, by rfl⟩ : syracuseStep 382823 = 574235) B574235
theorem B7002227 : Blo 381763 7002227 := bstep (se 1 (by rfl) ⟨5251670, by rfl⟩ : syracuseStep 7002227 = 10503341) B10503341
theorem B383183 : Blo 381763 383183 := bstep (se 1 (by rfl) ⟨287387, by rfl⟩ : syracuseStep 383183 = 574775) B574775
theorem B5888375 : Blo 381763 5888375 := bstep (se 1 (by rfl) ⟨4416281, by rfl⟩ : syracuseStep 5888375 = 8832563) B8832563
theorem B383695 : Blo 381763 383695 := bstep (se 1 (by rfl) ⟨287771, by rfl⟩ : syracuseStep 383695 = 575543) B575543
theorem B384191 : Blo 381763 384191 := bstep (se 1 (by rfl) ⟨288143, by rfl⟩ : syracuseStep 384191 = 576287) B576287
theorem B384719 : Blo 381763 384719 := bstep (se 1 (by rfl) ⟨288539, by rfl⟩ : syracuseStep 384719 = 577079) B577079
theorem B385135 : Blo 381763 385135 := bstep (se 1 (by rfl) ⟨288851, by rfl⟩ : syracuseStep 385135 = 577703) B577703
theorem B3500819 : Blo 381763 3500819 := bstep (se 1 (by rfl) ⟨2625614, by rfl⟩ : syracuseStep 3500819 = 5251229) B5251229
theorem B16152817 : Blo 381763 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B10681247 : Blo 381763 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B9308267 : Blo 381763 9308267 := bstep (se 1 (by rfl) ⟨6981200, by rfl⟩ : syracuseStep 9308267 = 13962401) B13962401
theorem B2166401 : Blo 381763 2166401 := bstep (se 2 (by rfl) ⟨812400, by rfl⟩ : syracuseStep 2166401 = 1624801) B1624801
theorem B1085275 : Blo 381763 1085275 := bstep (se 1 (by rfl) ⟨813956, by rfl⟩ : syracuseStep 1085275 = 1627913) B1627913
theorem B2333879 : Blo 381763 2333879 := bstep (se 1 (by rfl) ⟨1750409, by rfl⟩ : syracuseStep 2333879 = 3500819) B3500819
theorem B21537089 : Blo 381763 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B3286241 : Blo 381763 3286241 := bstep (se 2 (by rfl) ⟨1232340, by rfl⟩ : syracuseStep 3286241 = 2464681) B2464681
theorem B7120831 : Blo 381763 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B1847897 : Blo 381763 1847897 := bstep (se 2 (by rfl) ⟨692961, by rfl⟩ : syracuseStep 1847897 = 1385923) B1385923
theorem B865151 : Blo 381763 865151 := bstep (se 1 (by rfl) ⟨648863, by rfl⟩ : syracuseStep 865151 = 1297727) B1297727
theorem B2176703 : Blo 381763 2176703 := bstep (se 1 (by rfl) ⟨1632527, by rfl⟩ : syracuseStep 2176703 = 3265055) B3265055
theorem B4668151 : Blo 381763 4668151 := bstep (se 1 (by rfl) ⟨3501113, by rfl⟩ : syracuseStep 4668151 = 7002227) B7002227
theorem B1293083 : Blo 381763 1293083 := bstep (se 1 (by rfl) ⟨969812, by rfl⟩ : syracuseStep 1293083 = 1939625) B1939625
theorem B1456937 : Blo 381763 1456937 := bstep (se 2 (by rfl) ⟨546351, by rfl⟩ : syracuseStep 1456937 = 1092703) B1092703
theorem B573419 : Blo 381763 573419 := bstep (se 1 (by rfl) ⟨430064, by rfl⟩ : syracuseStep 573419 = 860129) B860129
theorem B574535 : Blo 381763 574535 := bstep (se 1 (by rfl) ⟨430901, by rfl⟩ : syracuseStep 574535 = 861803) B861803
theorem B574619 : Blo 381763 574619 := bstep (se 1 (by rfl) ⟨430964, by rfl⟩ : syracuseStep 574619 = 861929) B861929
theorem B4376915 : Blo 381763 4376915 := bstep (se 1 (by rfl) ⟨3282686, by rfl⟩ : syracuseStep 4376915 = 6565373) B6565373
theorem B575975 : Blo 381763 575975 := bstep (se 1 (by rfl) ⟨431981, by rfl⟩ : syracuseStep 575975 = 863963) B863963
theorem B5623019 : Blo 381763 5623019 := bstep (se 1 (by rfl) ⟨4217264, by rfl⟩ : syracuseStep 5623019 = 8434529) B8434529
theorem B970729 : Blo 381763 970729 := bstep (se 2 (by rfl) ⟨364023, by rfl⟩ : syracuseStep 970729 = 728047) B728047
theorem B970987 : Blo 381763 970987 := bstep (se 1 (by rfl) ⟨728240, by rfl⟩ : syracuseStep 970987 = 1456481) B1456481
theorem B382719 : Blo 381763 382719 := bstep (se 1 (by rfl) ⟨287039, by rfl⟩ : syracuseStep 382719 = 574079) B574079
theorem B10016939 : Blo 381763 10016939 := bstep (se 1 (by rfl) ⟨7512704, by rfl⟩ : syracuseStep 10016939 = 15025409) B15025409
theorem B383295 : Blo 381763 383295 := bstep (se 1 (by rfl) ⟨287471, by rfl⟩ : syracuseStep 383295 = 574943) B574943
theorem B290544353 : Blo 381763 290544353 := bstep (se 2 (by rfl) ⟨108954132, by rfl⟩ : syracuseStep 290544353 = 217908265) B217908265
theorem B777311 : Blo 381763 777311 := bstep (se 1 (by rfl) ⟨582983, by rfl⟩ : syracuseStep 777311 = 1165967) B1165967
theorem B1301615 : Blo 381763 1301615 := bstep (se 1 (by rfl) ⟨976211, by rfl⟩ : syracuseStep 1301615 = 1952423) B1952423
theorem B384763 : Blo 381763 384763 := bstep (se 1 (by rfl) ⟨288572, by rfl⟩ : syracuseStep 384763 = 577145) B577145
theorem B1335743 : Blo 381763 1335743 := bstep (se 1 (by rfl) ⟨1001807, by rfl⟩ : syracuseStep 1335743 = 2003615) B2003615
theorem B3925583 : Blo 381763 3925583 := bstep (se 1 (by rfl) ⟨2944187, by rfl⟩ : syracuseStep 3925583 = 5888375) B5888375
theorem B16607531 : Blo 381763 16607531 := bstep (se 1 (by rfl) ⟨12455648, by rfl⟩ : syracuseStep 16607531 = 24911297) B24911297
theorem B30371023 : Blo 381763 30371023 := bstep (se 1 (by rfl) ⟨22778267, by rfl⟩ : syracuseStep 30371023 = 45556535) B45556535
theorem B59600279 : Blo 381763 59600279 := bstep (se 1 (by rfl) ⟨44700209, by rfl⟩ : syracuseStep 59600279 = 89400419) B89400419
theorem B4158803 : Blo 381763 4158803 := bstep (se 1 (by rfl) ⟨3119102, by rfl⟩ : syracuseStep 4158803 = 6238205) B6238205
theorem B2917943 : Blo 381763 2917943 := bstep (se 1 (by rfl) ⟨2188457, by rfl⟩ : syracuseStep 2917943 = 4376915) B4376915
theorem B1444267 : Blo 381763 1444267 := bstep (se 1 (by rfl) ⟨1083200, by rfl⟩ : syracuseStep 1444267 = 2166401) B2166401
theorem B193696235 : Blo 381763 193696235 := bstep (se 1 (by rfl) ⟨145272176, by rfl⟩ : syracuseStep 193696235 = 290544353) B290544353
theorem B1447033 : Blo 381763 1447033 := bstep (se 2 (by rfl) ⟨542637, by rfl⟩ : syracuseStep 1447033 = 1085275) B1085275
theorem B14358059 : Blo 381763 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B890495 : Blo 381763 890495 := bstep (se 1 (by rfl) ⟨667871, by rfl⟩ : syracuseStep 890495 = 1335743) B1335743
theorem B1451135 : Blo 381763 1451135 := bstep (se 1 (by rfl) ⟨1088351, by rfl⟩ : syracuseStep 1451135 = 2176703) B2176703
theorem B862055 : Blo 381763 862055 := bstep (se 1 (by rfl) ⟨646541, by rfl⟩ : syracuseStep 862055 = 1293083) B1293083
theorem B6205511 : Blo 381763 6205511 := bstep (se 1 (by rfl) ⟨4654133, by rfl⟩ : syracuseStep 6205511 = 9308267) B9308267
theorem B3748679 : Blo 381763 3748679 := bstep (se 1 (by rfl) ⟨2811509, by rfl⟩ : syracuseStep 3748679 = 5623019) B5623019
theorem B11090141 : Blo 381763 11090141 := bstep (se 3 (by rfl) ⟨2079401, by rfl⟩ : syracuseStep 11090141 = 4158803) B4158803
theorem B867743 : Blo 381763 867743 := bstep (se 1 (by rfl) ⟨650807, by rfl⟩ : syracuseStep 867743 = 1301615) B1301615
theorem B1555919 : Blo 381763 1555919 := bstep (se 1 (by rfl) ⟨1166939, by rfl⟩ : syracuseStep 1555919 = 2333879) B2333879
theorem B1294649 : Blo 381763 1294649 := bstep (se 2 (by rfl) ⟨485493, by rfl⟩ : syracuseStep 1294649 = 970987) B970987
theorem B39733519 : Blo 381763 39733519 := bstep (se 1 (by rfl) ⟨29800139, by rfl⟩ : syracuseStep 39733519 = 59600279) B59600279
theorem B1231931 : Blo 381763 1231931 := bstep (se 1 (by rfl) ⟨923948, by rfl⟩ : syracuseStep 1231931 = 1847897) B1847897
theorem B576767 : Blo 381763 576767 := bstep (se 1 (by rfl) ⟨432575, by rfl⟩ : syracuseStep 576767 = 865151) B865151
theorem B971291 : Blo 381763 971291 := bstep (se 1 (by rfl) ⟨728468, by rfl⟩ : syracuseStep 971291 = 1456937) B1456937
theorem B382279 : Blo 381763 382279 := bstep (se 1 (by rfl) ⟨286709, by rfl⟩ : syracuseStep 382279 = 573419) B573419
theorem B383023 : Blo 381763 383023 := bstep (se 1 (by rfl) ⟨287267, by rfl⟩ : syracuseStep 383023 = 574535) B574535
theorem B383079 : Blo 381763 383079 := bstep (se 1 (by rfl) ⟨287309, by rfl⟩ : syracuseStep 383079 = 574619) B574619
theorem B383983 : Blo 381763 383983 := bstep (se 1 (by rfl) ⟨287987, by rfl⟩ : syracuseStep 383983 = 575975) B575975
theorem B9494441 : Blo 381763 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B6677959 : Blo 381763 6677959 := bstep (se 1 (by rfl) ⟨5008469, by rfl⟩ : syracuseStep 6677959 = 10016939) B10016939
theorem B40494697 : Blo 381763 40494697 := bstep (se 2 (by rfl) ⟨15185511, by rfl⟩ : syracuseStep 40494697 = 30371023) B30371023
theorem B518207 : Blo 381763 518207 := bstep (se 1 (by rfl) ⟨388655, by rfl⟩ : syracuseStep 518207 = 777311) B777311
theorem B2190827 : Blo 381763 2190827 := bstep (se 1 (by rfl) ⟨1643120, by rfl⟩ : syracuseStep 2190827 = 3286241) B3286241
theorem B2617055 : Blo 381763 2617055 := bstep (se 1 (by rfl) ⟨1962791, by rfl⟩ : syracuseStep 2617055 = 3925583) B3925583
theorem B11071687 : Blo 381763 11071687 := bstep (se 1 (by rfl) ⟨8303765, by rfl⟩ : syracuseStep 11071687 = 16607531) B16607531
theorem B6224201 : Blo 381763 6224201 := bstep (se 2 (by rfl) ⟨2334075, by rfl⟩ : syracuseStep 6224201 = 4668151) B4668151
theorem B20708885 : Blo 381763 20708885 := bstep (se 6 (by rfl) ⟨485364, by rfl⟩ : syracuseStep 20708885 = 970729) B970729
theorem B821287 : Blo 381763 821287 := bstep (se 1 (by rfl) ⟨615965, by rfl⟩ : syracuseStep 821287 = 1231931) B1231931
theorem B9572039 : Blo 381763 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B593663 : Blo 381763 593663 := bstep (se 1 (by rfl) ⟨445247, by rfl⟩ : syracuseStep 593663 = 890495) B890495
theorem B6329627 : Blo 381763 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B1744703 : Blo 381763 1744703 := bstep (se 1 (by rfl) ⟨1308527, by rfl⟩ : syracuseStep 1744703 = 2617055) B2617055
theorem B4137007 : Blo 381763 4137007 := bstep (se 1 (by rfl) ⟨3102755, by rfl⟩ : syracuseStep 4137007 = 6205511) B6205511
theorem B2499119 : Blo 381763 2499119 := bstep (se 1 (by rfl) ⟨1874339, by rfl⟩ : syracuseStep 2499119 = 3748679) B3748679
theorem B13805923 : Blo 381763 13805923 := bstep (se 1 (by rfl) ⟨10354442, by rfl⟩ : syracuseStep 13805923 = 20708885) B20708885
theorem B863099 : Blo 381763 863099 := bstep (se 1 (by rfl) ⟨647324, by rfl⟩ : syracuseStep 863099 = 1294649) B1294649
theorem B1945295 : Blo 381763 1945295 := bstep (se 1 (by rfl) ⟨1458971, by rfl⟩ : syracuseStep 1945295 = 2917943) B2917943
theorem B14762249 : Blo 381763 14762249 := bstep (se 2 (by rfl) ⟨5535843, by rfl⟩ : syracuseStep 14762249 = 11071687) B11071687
theorem B967423 : Blo 381763 967423 := bstep (se 1 (by rfl) ⟨725567, by rfl⟩ : syracuseStep 967423 = 1451135) B1451135
theorem B574703 : Blo 381763 574703 := bstep (se 1 (by rfl) ⟨431027, by rfl⟩ : syracuseStep 574703 = 862055) B862055
theorem B1460551 : Blo 381763 1460551 := bstep (se 1 (by rfl) ⟨1095413, by rfl⟩ : syracuseStep 1460551 = 2190827) B2190827
theorem B7393427 : Blo 381763 7393427 := bstep (se 1 (by rfl) ⟨5545070, by rfl⟩ : syracuseStep 7393427 = 11090141) B11090141
theorem B4149467 : Blo 381763 4149467 := bstep (se 1 (by rfl) ⟨3112100, by rfl⟩ : syracuseStep 4149467 = 6224201) B6224201
theorem B578495 : Blo 381763 578495 := bstep (se 1 (by rfl) ⟨433871, by rfl⟩ : syracuseStep 578495 = 867743) B867743
theorem B1037279 : Blo 381763 1037279 := bstep (se 1 (by rfl) ⟨777959, by rfl⟩ : syracuseStep 1037279 = 1555919) B1555919
theorem B5527541 : Blo 381763 5527541 := bstep (se 5 (by rfl) ⟨259103, by rfl⟩ : syracuseStep 5527541 = 518207) B518207
theorem B8903945 : Blo 381763 8903945 := bstep (se 2 (by rfl) ⟨3338979, by rfl⟩ : syracuseStep 8903945 = 6677959) B6677959
theorem B384511 : Blo 381763 384511 := bstep (se 1 (by rfl) ⟨288383, by rfl⟩ : syracuseStep 384511 = 576767) B576767
theorem B129130823 : Blo 381763 129130823 := bstep (se 1 (by rfl) ⟨96848117, by rfl⟩ : syracuseStep 129130823 = 193696235) B193696235
theorem B647527 : Blo 381763 647527 := bstep (se 1 (by rfl) ⟨485645, by rfl⟩ : syracuseStep 647527 = 971291) B971291
theorem B52978025 : Blo 381763 52978025 := bstep (se 2 (by rfl) ⟨19866759, by rfl⟩ : syracuseStep 52978025 = 39733519) B39733519
theorem B1925689 : Blo 381763 1925689 := bstep (se 2 (by rfl) ⟨722133, by rfl⟩ : syracuseStep 1925689 = 1444267) B1444267
theorem B1929377 : Blo 381763 1929377 := bstep (se 2 (by rfl) ⟨723516, by rfl⟩ : syracuseStep 1929377 = 1447033) B1447033
theorem B215971717 : Blo 381763 215971717 := bstep (se 4 (by rfl) ⟨20247348, by rfl⟩ : syracuseStep 215971717 = 40494697) B40494697
theorem B5145005 : Blo 381763 5145005 := bstep (se 3 (by rfl) ⟨964688, by rfl⟩ : syracuseStep 5145005 = 1929377) B1929377
theorem B5935963 : Blo 381763 5935963 := bstep (se 1 (by rfl) ⟨4451972, by rfl⟩ : syracuseStep 5935963 = 8903945) B8903945
theorem B86087215 : Blo 381763 86087215 := bstep (se 1 (by rfl) ⟨64565411, by rfl⟩ : syracuseStep 86087215 = 129130823) B129130823
theorem B1583101 : Blo 381763 1583101 := bstep (se 3 (by rfl) ⟨296831, by rfl⟩ : syracuseStep 1583101 = 593663) B593663
theorem B5516009 : Blo 381763 5516009 := bstep (se 2 (by rfl) ⟨2068503, by rfl⟩ : syracuseStep 5516009 = 4137007) B4137007
theorem B9841499 : Blo 381763 9841499 := bstep (se 1 (by rfl) ⟨7381124, by rfl⟩ : syracuseStep 9841499 = 14762249) B14762249
theorem B863369 : Blo 381763 863369 := bstep (se 2 (by rfl) ⟨323763, by rfl⟩ : syracuseStep 863369 = 647527) B647527
theorem B2567585 : Blo 381763 2567585 := bstep (se 2 (by rfl) ⟨962844, by rfl⟩ : syracuseStep 2567585 = 1925689) B1925689
theorem B1289897 : Blo 381763 1289897 := bstep (se 2 (by rfl) ⟨483711, by rfl⟩ : syracuseStep 1289897 = 967423) B967423
theorem B2766077 : Blo 381763 2766077 := bstep (se 3 (by rfl) ⟨518639, by rfl⟩ : syracuseStep 2766077 = 1037279) B1037279
theorem B1095049 : Blo 381763 1095049 := bstep (se 2 (by rfl) ⟨410643, by rfl⟩ : syracuseStep 1095049 = 821287) B821287
theorem B4928951 : Blo 381763 4928951 := bstep (se 1 (by rfl) ⟨3696713, by rfl⟩ : syracuseStep 4928951 = 7393427) B7393427
theorem B2766311 : Blo 381763 2766311 := bstep (se 1 (by rfl) ⟨2074733, by rfl⟩ : syracuseStep 2766311 = 4149467) B4149467
theorem B1947401 : Blo 381763 1947401 := bstep (se 2 (by rfl) ⟨730275, by rfl⟩ : syracuseStep 1947401 = 1460551) B1460551
theorem B3685027 : Blo 381763 3685027 := bstep (se 1 (by rfl) ⟨2763770, by rfl⟩ : syracuseStep 3685027 = 5527541) B5527541
theorem B1163135 : Blo 381763 1163135 := bstep (se 1 (by rfl) ⟨872351, by rfl⟩ : syracuseStep 1163135 = 1744703) B1744703
theorem B575399 : Blo 381763 575399 := bstep (se 1 (by rfl) ⟨431549, by rfl⟩ : syracuseStep 575399 = 863099) B863099
theorem B1296863 : Blo 381763 1296863 := bstep (se 1 (by rfl) ⟨972647, by rfl⟩ : syracuseStep 1296863 = 1945295) B1945295
theorem B383135 : Blo 381763 383135 := bstep (se 1 (by rfl) ⟨287351, by rfl⟩ : syracuseStep 383135 = 574703) B574703
theorem B6381359 : Blo 381763 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B18407897 : Blo 381763 18407897 := bstep (se 2 (by rfl) ⟨6902961, by rfl⟩ : syracuseStep 18407897 = 13805923) B13805923
theorem B385663 : Blo 381763 385663 := bstep (se 1 (by rfl) ⟨289247, by rfl⟩ : syracuseStep 385663 = 578495) B578495
theorem B4219751 : Blo 381763 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B35318683 : Blo 381763 35318683 := bstep (se 1 (by rfl) ⟨26489012, by rfl⟩ : syracuseStep 35318683 = 52978025) B52978025
theorem B1666079 : Blo 381763 1666079 := bstep (se 1 (by rfl) ⟨1249559, by rfl⟩ : syracuseStep 1666079 = 2499119) B2499119
theorem B287962289 : Blo 381763 287962289 := bstep (se 2 (by rfl) ⟨107985858, by rfl⟩ : syracuseStep 287962289 = 215971717) B215971717
theorem B47091577 : Blo 381763 47091577 := bstep (se 2 (by rfl) ⟨17659341, by rfl⟩ : syracuseStep 47091577 = 35318683) B35318683
theorem B3677339 : Blo 381763 3677339 := bstep (se 1 (by rfl) ⟨2758004, by rfl⟩ : syracuseStep 3677339 = 5516009) B5516009
theorem B6560999 : Blo 381763 6560999 := bstep (se 1 (by rfl) ⟨4920749, by rfl⟩ : syracuseStep 6560999 = 9841499) B9841499
theorem B859931 : Blo 381763 859931 := bstep (se 1 (by rfl) ⟨644948, by rfl⟩ : syracuseStep 859931 = 1289897) B1289897
theorem B1844051 : Blo 381763 1844051 := bstep (se 1 (by rfl) ⟨1383038, by rfl⟩ : syracuseStep 1844051 = 2766077) B2766077
theorem B3285967 : Blo 381763 3285967 := bstep (se 1 (by rfl) ⟨2464475, by rfl⟩ : syracuseStep 3285967 = 4928951) B4928951
theorem B1844207 : Blo 381763 1844207 := bstep (se 1 (by rfl) ⟨1383155, by rfl⟩ : syracuseStep 1844207 = 2766311) B2766311
theorem B864575 : Blo 381763 864575 := bstep (se 1 (by rfl) ⟨648431, by rfl⟩ : syracuseStep 864575 = 1296863) B1296863
theorem B2110801 : Blo 381763 2110801 := bstep (se 2 (by rfl) ⟨791550, by rfl⟩ : syracuseStep 2110801 = 1583101) B1583101
theorem B180042709 : Blo 381763 180042709 := bstep (se 7 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 180042709 = 4219751) B4219751
theorem B12271931 : Blo 381763 12271931 := bstep (se 1 (by rfl) ⟨9203948, by rfl⟩ : syracuseStep 12271931 = 18407897) B18407897
theorem B7914617 : Blo 381763 7914617 := bstep (se 2 (by rfl) ⟨2967981, by rfl⟩ : syracuseStep 7914617 = 5935963) B5935963
theorem B1460065 : Blo 381763 1460065 := bstep (se 2 (by rfl) ⟨547524, by rfl⟩ : syracuseStep 1460065 = 1095049) B1095049
theorem B575579 : Blo 381763 575579 := bstep (se 1 (by rfl) ⟨431684, by rfl⟩ : syracuseStep 575579 = 863369) B863369
theorem B191974859 : Blo 381763 191974859 := bstep (se 1 (by rfl) ⟨143981144, by rfl⟩ : syracuseStep 191974859 = 287962289) B287962289
theorem B1298267 : Blo 381763 1298267 := bstep (se 1 (by rfl) ⟨973700, by rfl⟩ : syracuseStep 1298267 = 1947401) B1947401
theorem B775423 : Blo 381763 775423 := bstep (se 1 (by rfl) ⟨581567, by rfl⟩ : syracuseStep 775423 = 1163135) B1163135
theorem B13720013 : Blo 381763 13720013 := bstep (se 3 (by rfl) ⟨2572502, by rfl⟩ : syracuseStep 13720013 = 5145005) B5145005
theorem B383599 : Blo 381763 383599 := bstep (se 1 (by rfl) ⟨287699, by rfl⟩ : syracuseStep 383599 = 575399) B575399
theorem B4254239 : Blo 381763 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B1110719 : Blo 381763 1110719 := bstep (se 1 (by rfl) ⟨833039, by rfl⟩ : syracuseStep 1110719 = 1666079) B1666079
theorem B114782953 : Blo 381763 114782953 := bstep (se 2 (by rfl) ⟨43043607, by rfl⟩ : syracuseStep 114782953 = 86087215) B86087215
theorem B4913369 : Blo 381763 4913369 := bstep (se 2 (by rfl) ⟨1842513, by rfl⟩ : syracuseStep 4913369 = 3685027) B3685027
theorem B6846893 : Blo 381763 6846893 := bstep (se 3 (by rfl) ⟨1283792, by rfl⟩ : syracuseStep 6846893 = 2567585) B2567585
theorem B5276411 : Blo 381763 5276411 := bstep (se 1 (by rfl) ⟨3957308, by rfl⟩ : syracuseStep 5276411 = 7914617) B7914617
theorem B4917469 : Blo 381763 4917469 := bstep (se 3 (by rfl) ⟨922025, by rfl⟩ : syracuseStep 4917469 = 1844051) B1844051
theorem B9146675 : Blo 381763 9146675 := bstep (se 1 (by rfl) ⟨6860006, by rfl⟩ : syracuseStep 9146675 = 13720013) B13720013
theorem B62788769 : Blo 381763 62788769 := bstep (se 2 (by rfl) ⟨23545788, by rfl⟩ : syracuseStep 62788769 = 47091577) B47091577
theorem B11344637 : Blo 381763 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B4564595 : Blo 381763 4564595 := bstep (se 1 (by rfl) ⟨3423446, by rfl⟩ : syracuseStep 4564595 = 6846893) B6846893
theorem B2961917 : Blo 381763 2961917 := bstep (se 3 (by rfl) ⟨555359, by rfl⟩ : syracuseStep 2961917 = 1110719) B1110719
theorem B1946753 : Blo 381763 1946753 := bstep (se 2 (by rfl) ⟨730032, by rfl⟩ : syracuseStep 1946753 = 1460065) B1460065
theorem B865511 : Blo 381763 865511 := bstep (se 1 (by rfl) ⟨649133, by rfl⟩ : syracuseStep 865511 = 1298267) B1298267
theorem B4373999 : Blo 381763 4373999 := bstep (se 1 (by rfl) ⟨3280499, by rfl⟩ : syracuseStep 4373999 = 6560999) B6560999
theorem B573287 : Blo 381763 573287 := bstep (se 1 (by rfl) ⟨429965, by rfl⟩ : syracuseStep 573287 = 859931) B859931
theorem B1229471 : Blo 381763 1229471 := bstep (se 1 (by rfl) ⟨922103, by rfl⟩ : syracuseStep 1229471 = 1844207) B1844207
theorem B153043937 : Blo 381763 153043937 := bstep (se 2 (by rfl) ⟨57391476, by rfl⟩ : syracuseStep 153043937 = 114782953) B114782953
theorem B1033897 : Blo 381763 1033897 := bstep (se 2 (by rfl) ⟨387711, by rfl⟩ : syracuseStep 1033897 = 775423) B775423
theorem B576383 : Blo 381763 576383 := bstep (se 1 (by rfl) ⟨432287, by rfl⟩ : syracuseStep 576383 = 864575) B864575
theorem B8181287 : Blo 381763 8181287 := bstep (se 1 (by rfl) ⟨6135965, by rfl⟩ : syracuseStep 8181287 = 12271931) B12271931
theorem B4381289 : Blo 381763 4381289 := bstep (se 2 (by rfl) ⟨1642983, by rfl⟩ : syracuseStep 4381289 = 3285967) B3285967
theorem B383719 : Blo 381763 383719 := bstep (se 1 (by rfl) ⟨287789, by rfl⟩ : syracuseStep 383719 = 575579) B575579
theorem B127983239 : Blo 381763 127983239 := bstep (se 1 (by rfl) ⟨95987429, by rfl⟩ : syracuseStep 127983239 = 191974859) B191974859
theorem B2451559 : Blo 381763 2451559 := bstep (se 1 (by rfl) ⟨1838669, by rfl⟩ : syracuseStep 2451559 = 3677339) B3677339
theorem B2814401 : Blo 381763 2814401 := bstep (se 2 (by rfl) ⟨1055400, by rfl⟩ : syracuseStep 2814401 = 2110801) B2110801
theorem B240056945 : Blo 381763 240056945 := bstep (se 2 (by rfl) ⟨90021354, by rfl⟩ : syracuseStep 240056945 = 180042709) B180042709
theorem B3275579 : Blo 381763 3275579 := bstep (se 1 (by rfl) ⟨2456684, by rfl⟩ : syracuseStep 3275579 = 4913369) B4913369
theorem B819647 : Blo 381763 819647 := bstep (se 1 (by rfl) ⟨614735, by rfl⟩ : syracuseStep 819647 = 1229471) B1229471
theorem B1378529 : Blo 381763 1378529 := bstep (se 2 (by rfl) ⟨516948, by rfl⟩ : syracuseStep 1378529 = 1033897) B1033897
theorem B6097783 : Blo 381763 6097783 := bstep (se 1 (by rfl) ⟨4573337, by rfl⟩ : syracuseStep 6097783 = 9146675) B9146675
theorem B6556625 : Blo 381763 6556625 := bstep (se 2 (by rfl) ⟨2458734, by rfl⟩ : syracuseStep 6556625 = 4917469) B4917469
theorem B2920859 : Blo 381763 2920859 := bstep (se 1 (by rfl) ⟨2190644, by rfl⟩ : syracuseStep 2920859 = 4381289) B4381289
theorem B1876267 : Blo 381763 1876267 := bstep (se 1 (by rfl) ⟨1407200, by rfl⟩ : syracuseStep 1876267 = 2814401) B2814401
theorem B1974611 : Blo 381763 1974611 := bstep (se 1 (by rfl) ⟨1480958, by rfl⟩ : syracuseStep 1974611 = 2961917) B2961917
theorem B3517607 : Blo 381763 3517607 := bstep (se 1 (by rfl) ⟨2638205, by rfl⟩ : syracuseStep 3517607 = 5276411) B5276411
theorem B41859179 : Blo 381763 41859179 := bstep (se 1 (by rfl) ⟨31394384, by rfl⟩ : syracuseStep 41859179 = 62788769) B62788769
theorem B5454191 : Blo 381763 5454191 := bstep (se 1 (by rfl) ⟨4090643, by rfl⟩ : syracuseStep 5454191 = 8181287) B8181287
theorem B1297835 : Blo 381763 1297835 := bstep (se 1 (by rfl) ⟨973376, by rfl⟩ : syracuseStep 1297835 = 1946753) B1946753
theorem B577007 : Blo 381763 577007 := bstep (se 1 (by rfl) ⟨432755, by rfl⟩ : syracuseStep 577007 = 865511) B865511
theorem B2183719 : Blo 381763 2183719 := bstep (se 1 (by rfl) ⟨1637789, by rfl⟩ : syracuseStep 2183719 = 3275579) B3275579
theorem B382191 : Blo 381763 382191 := bstep (se 1 (by rfl) ⟨286643, by rfl⟩ : syracuseStep 382191 = 573287) B573287
theorem B102029291 : Blo 381763 102029291 := bstep (se 1 (by rfl) ⟨76521968, by rfl⟩ : syracuseStep 102029291 = 153043937) B153043937
theorem B384255 : Blo 381763 384255 := bstep (se 1 (by rfl) ⟨288191, by rfl⟩ : syracuseStep 384255 = 576383) B576383
theorem B3268745 : Blo 381763 3268745 := bstep (se 2 (by rfl) ⟨1225779, by rfl⟩ : syracuseStep 3268745 = 2451559) B2451559
theorem B7563091 : Blo 381763 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B85322159 : Blo 381763 85322159 := bstep (se 1 (by rfl) ⟨63991619, by rfl⟩ : syracuseStep 85322159 = 127983239) B127983239
theorem B3043063 : Blo 381763 3043063 := bstep (se 1 (by rfl) ⟨2282297, by rfl⟩ : syracuseStep 3043063 = 4564595) B4564595
theorem B160037963 : Blo 381763 160037963 := bstep (se 1 (by rfl) ⟨120028472, by rfl⟩ : syracuseStep 160037963 = 240056945) B240056945
theorem B2915999 : Blo 381763 2915999 := bstep (se 1 (by rfl) ⟨2186999, by rfl⟩ : syracuseStep 2915999 = 4373999) B4373999
theorem B919019 : Blo 381763 919019 := bstep (se 1 (by rfl) ⟨689264, by rfl⟩ : syracuseStep 919019 = 1378529) B1378529
theorem B8130377 : Blo 381763 8130377 := bstep (se 2 (by rfl) ⟨3048891, by rfl⟩ : syracuseStep 8130377 = 6097783) B6097783
theorem B1316407 : Blo 381763 1316407 := bstep (se 1 (by rfl) ⟨987305, by rfl⟩ : syracuseStep 1316407 = 1974611) B1974611
theorem B9380285 : Blo 381763 9380285 := bstep (se 3 (by rfl) ⟨1758803, by rfl⟩ : syracuseStep 9380285 = 3517607) B3517607
theorem B1943999 : Blo 381763 1943999 := bstep (se 1 (by rfl) ⟨1457999, by rfl⟩ : syracuseStep 1943999 = 2915999) B2915999
theorem B2501689 : Blo 381763 2501689 := bstep (se 2 (by rfl) ⟨938133, by rfl⟩ : syracuseStep 2501689 = 1876267) B1876267
theorem B4371083 : Blo 381763 4371083 := bstep (se 1 (by rfl) ⟨3278312, by rfl⟩ : syracuseStep 4371083 = 6556625) B6556625
theorem B865223 : Blo 381763 865223 := bstep (se 1 (by rfl) ⟨648917, by rfl⟩ : syracuseStep 865223 = 1297835) B1297835
theorem B1947239 : Blo 381763 1947239 := bstep (se 1 (by rfl) ⟨1460429, by rfl⟩ : syracuseStep 1947239 = 2920859) B2920859
theorem B2179163 : Blo 381763 2179163 := bstep (se 1 (by rfl) ⟨1634372, by rfl⟩ : syracuseStep 2179163 = 3268745) B3268745
theorem B27906119 : Blo 381763 27906119 := bstep (se 1 (by rfl) ⟨20929589, by rfl⟩ : syracuseStep 27906119 = 41859179) B41859179
theorem B546431 : Blo 381763 546431 := bstep (se 1 (by rfl) ⟨409823, by rfl⟩ : syracuseStep 546431 = 819647) B819647
theorem B384671 : Blo 381763 384671 := bstep (se 1 (by rfl) ⟨288503, by rfl⟩ : syracuseStep 384671 = 577007) B577007
theorem B10084121 : Blo 381763 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B68019527 : Blo 381763 68019527 := bstep (se 1 (by rfl) ⟨51014645, by rfl⟩ : syracuseStep 68019527 = 102029291) B102029291
theorem B4057417 : Blo 381763 4057417 := bstep (se 2 (by rfl) ⟨1521531, by rfl⟩ : syracuseStep 4057417 = 3043063) B3043063
theorem B2911625 : Blo 381763 2911625 := bstep (se 2 (by rfl) ⟨1091859, by rfl⟩ : syracuseStep 2911625 = 2183719) B2183719
theorem B56881439 : Blo 381763 56881439 := bstep (se 1 (by rfl) ⟨42661079, by rfl⟩ : syracuseStep 56881439 = 85322159) B85322159
theorem B3636127 : Blo 381763 3636127 := bstep (se 1 (by rfl) ⟨2727095, by rfl⟩ : syracuseStep 3636127 = 5454191) B5454191
theorem B106691975 : Blo 381763 106691975 := bstep (se 1 (by rfl) ⟨80018981, by rfl⟩ : syracuseStep 106691975 = 160037963) B160037963
theorem B6722747 : Blo 381763 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B1941083 : Blo 381763 1941083 := bstep (se 1 (by rfl) ⟨1455812, by rfl⟩ : syracuseStep 1941083 = 2911625) B2911625
theorem B37920959 : Blo 381763 37920959 := bstep (se 1 (by rfl) ⟨28440719, by rfl⟩ : syracuseStep 37920959 = 56881439) B56881439
theorem B1452775 : Blo 381763 1452775 := bstep (se 1 (by rfl) ⟨1089581, by rfl⟩ : syracuseStep 1452775 = 2179163) B2179163
theorem B21639557 : Blo 381763 21639557 := bstep (se 4 (by rfl) ⟨2028708, by rfl⟩ : syracuseStep 21639557 = 4057417) B4057417
theorem B5420251 : Blo 381763 5420251 := bstep (se 1 (by rfl) ⟨4065188, by rfl⟩ : syracuseStep 5420251 = 8130377) B8130377
theorem B1457149 : Blo 381763 1457149 := bstep (se 3 (by rfl) ⟨273215, by rfl⟩ : syracuseStep 1457149 = 546431) B546431
theorem B1295999 : Blo 381763 1295999 := bstep (se 1 (by rfl) ⟨971999, by rfl⟩ : syracuseStep 1295999 = 1943999) B1943999
theorem B1755209 : Blo 381763 1755209 := bstep (se 2 (by rfl) ⟨658203, by rfl⟩ : syracuseStep 1755209 = 1316407) B1316407
theorem B576815 : Blo 381763 576815 := bstep (se 1 (by rfl) ⟨432611, by rfl⟩ : syracuseStep 576815 = 865223) B865223
theorem B1298159 : Blo 381763 1298159 := bstep (se 1 (by rfl) ⟨973619, by rfl⟩ : syracuseStep 1298159 = 1947239) B1947239
theorem B71127983 : Blo 381763 71127983 := bstep (se 1 (by rfl) ⟨53345987, by rfl⟩ : syracuseStep 71127983 = 106691975) B106691975
theorem B612679 : Blo 381763 612679 := bstep (se 1 (by rfl) ⟨459509, by rfl⟩ : syracuseStep 612679 = 919019) B919019
theorem B18604079 : Blo 381763 18604079 := bstep (se 1 (by rfl) ⟨13953059, by rfl⟩ : syracuseStep 18604079 = 27906119) B27906119
theorem B3335585 : Blo 381763 3335585 := bstep (se 2 (by rfl) ⟨1250844, by rfl⟩ : syracuseStep 3335585 = 2501689) B2501689
theorem B6253523 : Blo 381763 6253523 := bstep (se 1 (by rfl) ⟨4690142, by rfl⟩ : syracuseStep 6253523 = 9380285) B9380285
theorem B45346351 : Blo 381763 45346351 := bstep (se 1 (by rfl) ⟨34009763, by rfl⟩ : syracuseStep 45346351 = 68019527) B68019527
theorem B2914055 : Blo 381763 2914055 := bstep (se 1 (by rfl) ⟨2185541, by rfl⟩ : syracuseStep 2914055 = 4371083) B4371083
theorem B4848169 : Blo 381763 4848169 := bstep (se 2 (by rfl) ⟨1818063, by rfl⟩ : syracuseStep 4848169 = 3636127) B3636127
theorem B47418655 : Blo 381763 47418655 := bstep (se 1 (by rfl) ⟨35563991, by rfl⟩ : syracuseStep 47418655 = 71127983) B71127983
theorem B1937033 : Blo 381763 1937033 := bstep (se 2 (by rfl) ⟨726387, by rfl⟩ : syracuseStep 1937033 = 1452775) B1452775
theorem B60461801 : Blo 381763 60461801 := bstep (se 2 (by rfl) ⟨22673175, by rfl⟩ : syracuseStep 60461801 = 45346351) B45346351
theorem B4169015 : Blo 381763 4169015 := bstep (se 1 (by rfl) ⟨3126761, by rfl⟩ : syracuseStep 4169015 = 6253523) B6253523
theorem B14426371 : Blo 381763 14426371 := bstep (se 1 (by rfl) ⟨10819778, by rfl⟩ : syracuseStep 14426371 = 21639557) B21639557
theorem B6464225 : Blo 381763 6464225 := bstep (se 2 (by rfl) ⟨2424084, by rfl⟩ : syracuseStep 6464225 = 4848169) B4848169
theorem B1942703 : Blo 381763 1942703 := bstep (se 1 (by rfl) ⟨1457027, by rfl⟩ : syracuseStep 1942703 = 2914055) B2914055
theorem B1942865 : Blo 381763 1942865 := bstep (se 2 (by rfl) ⟨728574, by rfl⟩ : syracuseStep 1942865 = 1457149) B1457149
theorem B863999 : Blo 381763 863999 := bstep (se 1 (by rfl) ⟨647999, by rfl⟩ : syracuseStep 863999 = 1295999) B1295999
theorem B865439 : Blo 381763 865439 := bstep (se 1 (by rfl) ⟨649079, by rfl⟩ : syracuseStep 865439 = 1298159) B1298159
theorem B8894893 : Blo 381763 8894893 := bstep (se 3 (by rfl) ⟨1667792, by rfl⟩ : syracuseStep 8894893 = 3335585) B3335585
theorem B1294055 : Blo 381763 1294055 := bstep (se 1 (by rfl) ⟨970541, by rfl⟩ : syracuseStep 1294055 = 1941083) B1941083
theorem B12402719 : Blo 381763 12402719 := bstep (se 1 (by rfl) ⟨9302039, by rfl⟩ : syracuseStep 12402719 = 18604079) B18604079
theorem B25280639 : Blo 381763 25280639 := bstep (se 1 (by rfl) ⟨18960479, by rfl⟩ : syracuseStep 25280639 = 37920959) B37920959
theorem B7227001 : Blo 381763 7227001 := bstep (se 2 (by rfl) ⟨2710125, by rfl⟩ : syracuseStep 7227001 = 5420251) B5420251
theorem B384543 : Blo 381763 384543 := bstep (se 1 (by rfl) ⟨288407, by rfl⟩ : syracuseStep 384543 = 576815) B576815
theorem B4481831 : Blo 381763 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B4680557 : Blo 381763 4680557 := bstep (se 3 (by rfl) ⟨877604, by rfl⟩ : syracuseStep 4680557 = 1755209) B1755209
theorem B816905 : Blo 381763 816905 := bstep (se 2 (by rfl) ⟨306339, by rfl⟩ : syracuseStep 816905 = 612679) B612679
theorem B19235161 : Blo 381763 19235161 := bstep (se 2 (by rfl) ⟨7213185, by rfl⟩ : syracuseStep 19235161 = 14426371) B14426371
theorem B17237933 : Blo 381763 17237933 := bstep (se 3 (by rfl) ⟨3232112, by rfl⟩ : syracuseStep 17237933 = 6464225) B6464225
theorem B40307867 : Blo 381763 40307867 := bstep (se 1 (by rfl) ⟨30230900, by rfl⟩ : syracuseStep 40307867 = 60461801) B60461801
theorem B2987887 : Blo 381763 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B3120371 : Blo 381763 3120371 := bstep (se 1 (by rfl) ⟨2340278, by rfl⟩ : syracuseStep 3120371 = 4680557) B4680557
theorem B38544005 : Blo 381763 38544005 := bstep (se 4 (by rfl) ⟨3613500, by rfl⟩ : syracuseStep 38544005 = 7227001) B7227001
theorem B862703 : Blo 381763 862703 := bstep (se 1 (by rfl) ⟨647027, by rfl⟩ : syracuseStep 862703 = 1294055) B1294055
theorem B8268479 : Blo 381763 8268479 := bstep (se 1 (by rfl) ⟨6201359, by rfl⟩ : syracuseStep 8268479 = 12402719) B12402719
theorem B16853759 : Blo 381763 16853759 := bstep (se 1 (by rfl) ⟨12640319, by rfl⟩ : syracuseStep 16853759 = 25280639) B25280639
theorem B1291355 : Blo 381763 1291355 := bstep (se 1 (by rfl) ⟨968516, by rfl⟩ : syracuseStep 1291355 = 1937033) B1937033
theorem B63224873 : Blo 381763 63224873 := bstep (se 2 (by rfl) ⟨23709327, by rfl⟩ : syracuseStep 63224873 = 47418655) B47418655
theorem B2178413 : Blo 381763 2178413 := bstep (se 3 (by rfl) ⟨408452, by rfl⟩ : syracuseStep 2178413 = 816905) B816905
theorem B1295135 : Blo 381763 1295135 := bstep (se 1 (by rfl) ⟨971351, by rfl⟩ : syracuseStep 1295135 = 1942703) B1942703
theorem B1295243 : Blo 381763 1295243 := bstep (se 1 (by rfl) ⟨971432, by rfl⟩ : syracuseStep 1295243 = 1942865) B1942865
theorem B575999 : Blo 381763 575999 := bstep (se 1 (by rfl) ⟨431999, by rfl⟩ : syracuseStep 575999 = 863999) B863999
theorem B576959 : Blo 381763 576959 := bstep (se 1 (by rfl) ⟨432719, by rfl⟩ : syracuseStep 576959 = 865439) B865439
theorem B2779343 : Blo 381763 2779343 := bstep (se 1 (by rfl) ⟨2084507, by rfl⟩ : syracuseStep 2779343 = 4169015) B4169015
theorem B11859857 : Blo 381763 11859857 := bstep (se 2 (by rfl) ⟨4447446, by rfl⟩ : syracuseStep 11859857 = 8894893) B8894893
theorem B26871911 : Blo 381763 26871911 := bstep (se 1 (by rfl) ⟨20153933, by rfl⟩ : syracuseStep 26871911 = 40307867) B40307867
theorem B25696003 : Blo 381763 25696003 := bstep (se 1 (by rfl) ⟨19272002, by rfl⟩ : syracuseStep 25696003 = 38544005) B38544005
theorem B5512319 : Blo 381763 5512319 := bstep (se 1 (by rfl) ⟨4134239, by rfl⟩ : syracuseStep 5512319 = 8268479) B8268479
theorem B860903 : Blo 381763 860903 := bstep (se 1 (by rfl) ⟨645677, by rfl⟩ : syracuseStep 860903 = 1291355) B1291355
theorem B7906571 : Blo 381763 7906571 := bstep (se 1 (by rfl) ⟨5929928, by rfl⟩ : syracuseStep 7906571 = 11859857) B11859857
theorem B42149915 : Blo 381763 42149915 := bstep (se 1 (by rfl) ⟨31612436, by rfl⟩ : syracuseStep 42149915 = 63224873) B63224873
theorem B1452275 : Blo 381763 1452275 := bstep (se 1 (by rfl) ⟨1089206, by rfl⟩ : syracuseStep 1452275 = 2178413) B2178413
theorem B863423 : Blo 381763 863423 := bstep (se 1 (by rfl) ⟨647567, by rfl⟩ : syracuseStep 863423 = 1295135) B1295135
theorem B863495 : Blo 381763 863495 := bstep (se 1 (by rfl) ⟨647621, by rfl⟩ : syracuseStep 863495 = 1295243) B1295243
theorem B2080247 : Blo 381763 2080247 := bstep (se 1 (by rfl) ⟨1560185, by rfl⟩ : syracuseStep 2080247 = 3120371) B3120371
theorem B1852895 : Blo 381763 1852895 := bstep (se 1 (by rfl) ⟨1389671, by rfl⟩ : syracuseStep 1852895 = 2779343) B2779343
theorem B575135 : Blo 381763 575135 := bstep (se 1 (by rfl) ⟨431351, by rfl⟩ : syracuseStep 575135 = 862703) B862703
theorem B3983849 : Blo 381763 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B25646881 : Blo 381763 25646881 := bstep (se 2 (by rfl) ⟨9617580, by rfl⟩ : syracuseStep 25646881 = 19235161) B19235161
theorem B11491955 : Blo 381763 11491955 := bstep (se 1 (by rfl) ⟨8618966, by rfl⟩ : syracuseStep 11491955 = 17237933) B17237933
theorem B383999 : Blo 381763 383999 := bstep (se 1 (by rfl) ⟨287999, by rfl⟩ : syracuseStep 383999 = 575999) B575999
theorem B384639 : Blo 381763 384639 := bstep (se 1 (by rfl) ⟨288479, by rfl⟩ : syracuseStep 384639 = 576959) B576959
theorem B11235839 : Blo 381763 11235839 := bstep (se 1 (by rfl) ⟨8426879, by rfl⟩ : syracuseStep 11235839 = 16853759) B16853759
theorem B2655899 : Blo 381763 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B3674879 : Blo 381763 3674879 := bstep (se 1 (by rfl) ⟨2756159, by rfl⟩ : syracuseStep 3674879 = 5512319) B5512319
theorem B5547325 : Blo 381763 5547325 := bstep (se 3 (by rfl) ⟨1040123, by rfl⟩ : syracuseStep 5547325 = 2080247) B2080247
theorem B29962237 : Blo 381763 29962237 := bstep (se 3 (by rfl) ⟨5617919, by rfl⟩ : syracuseStep 29962237 = 11235839) B11235839
theorem B573935 : Blo 381763 573935 := bstep (se 1 (by rfl) ⟨430451, by rfl⟩ : syracuseStep 573935 = 860903) B860903
theorem B28099943 : Blo 381763 28099943 := bstep (se 1 (by rfl) ⟨21074957, by rfl⟩ : syracuseStep 28099943 = 42149915) B42149915
theorem B968183 : Blo 381763 968183 := bstep (se 1 (by rfl) ⟨726137, by rfl⟩ : syracuseStep 968183 = 1452275) B1452275
theorem B575615 : Blo 381763 575615 := bstep (se 1 (by rfl) ⟨431711, by rfl⟩ : syracuseStep 575615 = 863423) B863423
theorem B575663 : Blo 381763 575663 := bstep (se 1 (by rfl) ⟨431747, by rfl⟩ : syracuseStep 575663 = 863495) B863495
theorem B34261337 : Blo 381763 34261337 := bstep (se 2 (by rfl) ⟨12848001, by rfl⟩ : syracuseStep 34261337 = 25696003) B25696003
theorem B34195841 : Blo 381763 34195841 := bstep (se 2 (by rfl) ⟨12823440, by rfl⟩ : syracuseStep 34195841 = 25646881) B25646881
theorem B1235263 : Blo 381763 1235263 := bstep (se 1 (by rfl) ⟨926447, by rfl⟩ : syracuseStep 1235263 = 1852895) B1852895
theorem B383423 : Blo 381763 383423 := bstep (se 1 (by rfl) ⟨287567, by rfl⟩ : syracuseStep 383423 = 575135) B575135
theorem B17914607 : Blo 381763 17914607 := bstep (se 1 (by rfl) ⟨13435955, by rfl⟩ : syracuseStep 17914607 = 26871911) B26871911
theorem B7661303 : Blo 381763 7661303 := bstep (se 1 (by rfl) ⟨5745977, by rfl⟩ : syracuseStep 7661303 = 11491955) B11491955
theorem B5271047 : Blo 381763 5271047 := bstep (se 1 (by rfl) ⟨3953285, by rfl⟩ : syracuseStep 5271047 = 7906571) B7906571
theorem B1770599 : Blo 381763 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B39949649 : Blo 381763 39949649 := bstep (se 2 (by rfl) ⟨14981118, by rfl⟩ : syracuseStep 39949649 = 29962237) B29962237
theorem B91363565 : Blo 381763 91363565 := bstep (se 3 (by rfl) ⟨17130668, by rfl⟩ : syracuseStep 91363565 = 34261337) B34261337
theorem B3514031 : Blo 381763 3514031 := bstep (se 1 (by rfl) ⟨2635523, by rfl⟩ : syracuseStep 3514031 = 5271047) B5271047
theorem B1647017 : Blo 381763 1647017 := bstep (se 2 (by rfl) ⟨617631, by rfl⟩ : syracuseStep 1647017 = 1235263) B1235263
theorem B11943071 : Blo 381763 11943071 := bstep (se 1 (by rfl) ⟨8957303, by rfl⟩ : syracuseStep 11943071 = 17914607) B17914607
theorem B382623 : Blo 381763 382623 := bstep (se 1 (by rfl) ⟨286967, by rfl⟩ : syracuseStep 382623 = 573935) B573935
theorem B18733295 : Blo 381763 18733295 := bstep (se 1 (by rfl) ⟨14049971, by rfl⟩ : syracuseStep 18733295 = 28099943) B28099943
theorem B645455 : Blo 381763 645455 := bstep (se 1 (by rfl) ⟨484091, by rfl⟩ : syracuseStep 645455 = 968183) B968183
theorem B383743 : Blo 381763 383743 := bstep (se 1 (by rfl) ⟨287807, by rfl⟩ : syracuseStep 383743 = 575615) B575615
theorem B383775 : Blo 381763 383775 := bstep (se 1 (by rfl) ⟨287831, by rfl⟩ : syracuseStep 383775 = 575663) B575663
theorem B22797227 : Blo 381763 22797227 := bstep (se 1 (by rfl) ⟨17097920, by rfl⟩ : syracuseStep 22797227 = 34195841) B34195841
theorem B7396433 : Blo 381763 7396433 := bstep (se 2 (by rfl) ⟨2773662, by rfl⟩ : syracuseStep 7396433 = 5547325) B5547325
theorem B2449919 : Blo 381763 2449919 := bstep (se 1 (by rfl) ⟨1837439, by rfl⟩ : syracuseStep 2449919 = 3674879) B3674879
theorem B5107535 : Blo 381763 5107535 := bstep (se 1 (by rfl) ⟨3830651, by rfl⟩ : syracuseStep 5107535 = 7661303) B7661303
theorem B4721597 : Blo 381763 4721597 := bstep (se 3 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 4721597 = 1770599) B1770599
theorem B430303 : Blo 381763 430303 := bstep (se 1 (by rfl) ⟨322727, by rfl⟩ : syracuseStep 430303 = 645455) B645455
theorem B4930955 : Blo 381763 4930955 := bstep (se 1 (by rfl) ⟨3698216, by rfl⟩ : syracuseStep 4930955 = 7396433) B7396433
theorem B2342687 : Blo 381763 2342687 := bstep (se 1 (by rfl) ⟨1757015, by rfl⟩ : syracuseStep 2342687 = 3514031) B3514031
theorem B1098011 : Blo 381763 1098011 := bstep (se 1 (by rfl) ⟨823508, by rfl⟩ : syracuseStep 1098011 = 1647017) B1647017
theorem B49955453 : Blo 381763 49955453 := bstep (se 3 (by rfl) ⟨9366647, by rfl⟩ : syracuseStep 49955453 = 18733295) B18733295
theorem B26633099 : Blo 381763 26633099 := bstep (se 1 (by rfl) ⟨19974824, by rfl⟩ : syracuseStep 26633099 = 39949649) B39949649
theorem B60909043 : Blo 381763 60909043 := bstep (se 1 (by rfl) ⟨45681782, by rfl⟩ : syracuseStep 60909043 = 91363565) B91363565
theorem B15198151 : Blo 381763 15198151 := bstep (se 1 (by rfl) ⟨11398613, by rfl⟩ : syracuseStep 15198151 = 22797227) B22797227
theorem B1633279 : Blo 381763 1633279 := bstep (se 1 (by rfl) ⟨1224959, by rfl⟩ : syracuseStep 1633279 = 2449919) B2449919
theorem B3405023 : Blo 381763 3405023 := bstep (se 1 (by rfl) ⟨2553767, by rfl⟩ : syracuseStep 3405023 = 5107535) B5107535
theorem B7962047 : Blo 381763 7962047 := bstep (se 1 (by rfl) ⟨5971535, by rfl⟩ : syracuseStep 7962047 = 11943071) B11943071
theorem B3147731 : Blo 381763 3147731 := bstep (se 1 (by rfl) ⟨2360798, by rfl⟩ : syracuseStep 3147731 = 4721597) B4721597
theorem B2270015 : Blo 381763 2270015 := bstep (se 1 (by rfl) ⟨1702511, by rfl⟩ : syracuseStep 2270015 = 3405023) B3405023
theorem B3287303 : Blo 381763 3287303 := bstep (se 1 (by rfl) ⟨2465477, by rfl⟩ : syracuseStep 3287303 = 4930955) B4930955
theorem B732007 : Blo 381763 732007 := bstep (se 1 (by rfl) ⟨549005, by rfl⟩ : syracuseStep 732007 = 1098011) B1098011
theorem B33303635 : Blo 381763 33303635 := bstep (se 1 (by rfl) ⟨24977726, by rfl⟩ : syracuseStep 33303635 = 49955453) B49955453
theorem B81212057 : Blo 381763 81212057 := bstep (se 2 (by rfl) ⟨30454521, by rfl⟩ : syracuseStep 81212057 = 60909043) B60909043
theorem B20264201 : Blo 381763 20264201 := bstep (se 2 (by rfl) ⟨7599075, by rfl⟩ : syracuseStep 20264201 = 15198151) B15198151
theorem B2177705 : Blo 381763 2177705 := bstep (se 2 (by rfl) ⟨816639, by rfl⟩ : syracuseStep 2177705 = 1633279) B1633279
theorem B573737 : Blo 381763 573737 := bstep (se 2 (by rfl) ⟨215151, by rfl⟩ : syracuseStep 573737 = 430303) B430303
theorem B6247165 : Blo 381763 6247165 := bstep (se 3 (by rfl) ⟨1171343, by rfl⟩ : syracuseStep 6247165 = 2342687) B2342687
theorem B17755399 : Blo 381763 17755399 := bstep (se 1 (by rfl) ⟨13316549, by rfl⟩ : syracuseStep 17755399 = 26633099) B26633099
theorem B5308031 : Blo 381763 5308031 := bstep (se 1 (by rfl) ⟨3981023, by rfl⟩ : syracuseStep 5308031 = 7962047) B7962047
theorem B2098487 : Blo 381763 2098487 := bstep (se 1 (by rfl) ⟨1573865, by rfl⟩ : syracuseStep 2098487 = 3147731) B3147731
theorem B1513343 : Blo 381763 1513343 := bstep (se 1 (by rfl) ⟨1135007, by rfl⟩ : syracuseStep 1513343 = 2270015) B2270015
theorem B8329553 : Blo 381763 8329553 := bstep (se 2 (by rfl) ⟨3123582, by rfl⟩ : syracuseStep 8329553 = 6247165) B6247165
theorem B54141371 : Blo 381763 54141371 := bstep (se 1 (by rfl) ⟨40606028, by rfl⟩ : syracuseStep 54141371 = 81212057) B81212057
theorem B13509467 : Blo 381763 13509467 := bstep (se 1 (by rfl) ⟨10132100, by rfl⟩ : syracuseStep 13509467 = 20264201) B20264201
theorem B1451803 : Blo 381763 1451803 := bstep (se 1 (by rfl) ⟨1088852, by rfl⟩ : syracuseStep 1451803 = 2177705) B2177705
theorem B23673865 : Blo 381763 23673865 := bstep (se 2 (by rfl) ⟨8877699, by rfl⟩ : syracuseStep 23673865 = 17755399) B17755399
theorem B22202423 : Blo 381763 22202423 := bstep (se 1 (by rfl) ⟨16651817, by rfl⟩ : syracuseStep 22202423 = 33303635) B33303635
theorem B382491 : Blo 381763 382491 := bstep (se 1 (by rfl) ⟨286868, by rfl⟩ : syracuseStep 382491 = 573737) B573737
theorem B976009 : Blo 381763 976009 := bstep (se 2 (by rfl) ⟨366003, by rfl⟩ : syracuseStep 976009 = 732007) B732007
theorem B2191535 : Blo 381763 2191535 := bstep (se 1 (by rfl) ⟨1643651, by rfl⟩ : syracuseStep 2191535 = 3287303) B3287303
theorem B3538687 : Blo 381763 3538687 := bstep (se 1 (by rfl) ⟨2654015, by rfl⟩ : syracuseStep 3538687 = 5308031) B5308031
theorem B1935737 : Blo 381763 1935737 := bstep (se 2 (by rfl) ⟨725901, by rfl⟩ : syracuseStep 1935737 = 1451803) B1451803
theorem B4035581 : Blo 381763 4035581 := bstep (se 3 (by rfl) ⟨756671, by rfl⟩ : syracuseStep 4035581 = 1513343) B1513343
theorem B31565153 : Blo 381763 31565153 := bstep (se 2 (by rfl) ⟨11836932, by rfl⟩ : syracuseStep 31565153 = 23673865) B23673865
theorem B5553035 : Blo 381763 5553035 := bstep (se 1 (by rfl) ⟨4164776, by rfl⟩ : syracuseStep 5553035 = 8329553) B8329553
theorem B36094247 : Blo 381763 36094247 := bstep (se 1 (by rfl) ⟨27070685, by rfl⟩ : syracuseStep 36094247 = 54141371) B54141371
theorem B1461023 : Blo 381763 1461023 := bstep (se 1 (by rfl) ⟨1095767, by rfl⟩ : syracuseStep 1461023 = 2191535) B2191535
theorem B14801615 : Blo 381763 14801615 := bstep (se 1 (by rfl) ⟨11101211, by rfl⟩ : syracuseStep 14801615 = 22202423) B22202423
theorem B1301345 : Blo 381763 1301345 := bstep (se 2 (by rfl) ⟨488004, by rfl⟩ : syracuseStep 1301345 = 976009) B976009
theorem B5595965 : Blo 381763 5595965 := bstep (se 3 (by rfl) ⟨1049243, by rfl⟩ : syracuseStep 5595965 = 2098487) B2098487
theorem B9006311 : Blo 381763 9006311 := bstep (se 1 (by rfl) ⟨6754733, by rfl⟩ : syracuseStep 9006311 = 13509467) B13509467
theorem B4718249 : Blo 381763 4718249 := bstep (se 2 (by rfl) ⟨1769343, by rfl⟩ : syracuseStep 4718249 = 3538687) B3538687
theorem B2690387 : Blo 381763 2690387 := bstep (se 1 (by rfl) ⟨2017790, by rfl⟩ : syracuseStep 2690387 = 4035581) B4035581
theorem B9867743 : Blo 381763 9867743 := bstep (se 1 (by rfl) ⟨7400807, by rfl⟩ : syracuseStep 9867743 = 14801615) B14801615
theorem B21043435 : Blo 381763 21043435 := bstep (se 1 (by rfl) ⟨15782576, by rfl⟩ : syracuseStep 21043435 = 31565153) B31565153
theorem B6004207 : Blo 381763 6004207 := bstep (se 1 (by rfl) ⟨4503155, by rfl⟩ : syracuseStep 6004207 = 9006311) B9006311
theorem B24062831 : Blo 381763 24062831 := bstep (se 1 (by rfl) ⟨18047123, by rfl⟩ : syracuseStep 24062831 = 36094247) B36094247
theorem B1290491 : Blo 381763 1290491 := bstep (se 1 (by rfl) ⟨967868, by rfl⟩ : syracuseStep 1290491 = 1935737) B1935737
theorem B867563 : Blo 381763 867563 := bstep (se 1 (by rfl) ⟨650672, by rfl⟩ : syracuseStep 867563 = 1301345) B1301345
theorem B974015 : Blo 381763 974015 := bstep (se 1 (by rfl) ⟨730511, by rfl⟩ : syracuseStep 974015 = 1461023) B1461023
theorem B3730643 : Blo 381763 3730643 := bstep (se 1 (by rfl) ⟨2797982, by rfl⟩ : syracuseStep 3730643 = 5595965) B5595965
theorem B3702023 : Blo 381763 3702023 := bstep (se 1 (by rfl) ⟨2776517, by rfl⟩ : syracuseStep 3702023 = 5553035) B5553035
theorem B3145499 : Blo 381763 3145499 := bstep (se 1 (by rfl) ⟨2359124, by rfl⟩ : syracuseStep 3145499 = 4718249) B4718249
theorem B860327 : Blo 381763 860327 := bstep (se 1 (by rfl) ⟨645245, by rfl⟩ : syracuseStep 860327 = 1290491) B1290491
theorem B28057913 : Blo 381763 28057913 := bstep (se 2 (by rfl) ⟨10521717, by rfl⟩ : syracuseStep 28057913 = 21043435) B21043435
theorem B8005609 : Blo 381763 8005609 := bstep (se 2 (by rfl) ⟨3002103, by rfl⟩ : syracuseStep 8005609 = 6004207) B6004207
theorem B2468015 : Blo 381763 2468015 := bstep (se 1 (by rfl) ⟨1851011, by rfl⟩ : syracuseStep 2468015 = 3702023) B3702023
theorem B16041887 : Blo 381763 16041887 := bstep (se 1 (by rfl) ⟨12031415, by rfl⟩ : syracuseStep 16041887 = 24062831) B24062831
theorem B578375 : Blo 381763 578375 := bstep (se 1 (by rfl) ⟨433781, by rfl⟩ : syracuseStep 578375 = 867563) B867563
theorem B1793591 : Blo 381763 1793591 := bstep (se 1 (by rfl) ⟨1345193, by rfl⟩ : syracuseStep 1793591 = 2690387) B2690387
theorem B6578495 : Blo 381763 6578495 := bstep (se 1 (by rfl) ⟨4933871, by rfl⟩ : syracuseStep 6578495 = 9867743) B9867743
theorem B649343 : Blo 381763 649343 := bstep (se 1 (by rfl) ⟨487007, by rfl⟩ : syracuseStep 649343 = 974015) B974015
theorem B2487095 : Blo 381763 2487095 := bstep (se 1 (by rfl) ⟨1865321, by rfl⟩ : syracuseStep 2487095 = 3730643) B3730643
theorem B2096999 : Blo 381763 2096999 := bstep (se 1 (by rfl) ⟨1572749, by rfl⟩ : syracuseStep 2096999 = 3145499) B3145499
theorem B432895 : Blo 381763 432895 := bstep (se 1 (by rfl) ⟨324671, by rfl⟩ : syracuseStep 432895 = 649343) B649343
theorem B1645343 : Blo 381763 1645343 := bstep (se 1 (by rfl) ⟨1234007, by rfl⟩ : syracuseStep 1645343 = 2468015) B2468015
theorem B10694591 : Blo 381763 10694591 := bstep (se 1 (by rfl) ⟨8020943, by rfl⟩ : syracuseStep 10694591 = 16041887) B16041887
theorem B1195727 : Blo 381763 1195727 := bstep (se 1 (by rfl) ⟨896795, by rfl⟩ : syracuseStep 1195727 = 1793591) B1793591
theorem B573551 : Blo 381763 573551 := bstep (se 1 (by rfl) ⟨430163, by rfl⟩ : syracuseStep 573551 = 860327) B860327
theorem B1658063 : Blo 381763 1658063 := bstep (se 1 (by rfl) ⟨1243547, by rfl⟩ : syracuseStep 1658063 = 2487095) B2487095
theorem B1397999 : Blo 381763 1397999 := bstep (se 1 (by rfl) ⟨1048499, by rfl⟩ : syracuseStep 1397999 = 2096999) B2096999
theorem B10674145 : Blo 381763 10674145 := bstep (se 2 (by rfl) ⟨4002804, by rfl⟩ : syracuseStep 10674145 = 8005609) B8005609
theorem B385583 : Blo 381763 385583 := bstep (se 1 (by rfl) ⟨289187, by rfl⟩ : syracuseStep 385583 = 578375) B578375
theorem B18705275 : Blo 381763 18705275 := bstep (se 1 (by rfl) ⟨14028956, by rfl⟩ : syracuseStep 18705275 = 28057913) B28057913
theorem B4385663 : Blo 381763 4385663 := bstep (se 1 (by rfl) ⟨3289247, by rfl⟩ : syracuseStep 4385663 = 6578495) B6578495
theorem B2923775 : Blo 381763 2923775 := bstep (se 1 (by rfl) ⟨2192831, by rfl⟩ : syracuseStep 2923775 = 4385663) B4385663
theorem B3188605 : Blo 381763 3188605 := bstep (se 3 (by rfl) ⟨597863, by rfl⟩ : syracuseStep 3188605 = 1195727) B1195727
theorem B14232193 : Blo 381763 14232193 := bstep (se 2 (by rfl) ⟨5337072, by rfl⟩ : syracuseStep 14232193 = 10674145) B10674145
theorem B931999 : Blo 381763 931999 := bstep (se 1 (by rfl) ⟨698999, by rfl⟩ : syracuseStep 931999 = 1397999) B1397999
theorem B1096895 : Blo 381763 1096895 := bstep (se 1 (by rfl) ⟨822671, by rfl⟩ : syracuseStep 1096895 = 1645343) B1645343
theorem B12470183 : Blo 381763 12470183 := bstep (se 1 (by rfl) ⟨9352637, by rfl⟩ : syracuseStep 12470183 = 18705275) B18705275
theorem B7129727 : Blo 381763 7129727 := bstep (se 1 (by rfl) ⟨5347295, by rfl⟩ : syracuseStep 7129727 = 10694591) B10694591
theorem B577193 : Blo 381763 577193 := bstep (se 2 (by rfl) ⟨216447, by rfl⟩ : syracuseStep 577193 = 432895) B432895
theorem B382367 : Blo 381763 382367 := bstep (se 1 (by rfl) ⟨286775, by rfl⟩ : syracuseStep 382367 = 573551) B573551
theorem B1105375 : Blo 381763 1105375 := bstep (se 1 (by rfl) ⟨829031, by rfl⟩ : syracuseStep 1105375 = 1658063) B1658063
theorem B4753151 : Blo 381763 4753151 := bstep (se 1 (by rfl) ⟨3564863, by rfl⟩ : syracuseStep 4753151 = 7129727) B7129727
theorem B731263 : Blo 381763 731263 := bstep (se 1 (by rfl) ⟨548447, by rfl⟩ : syracuseStep 731263 = 1096895) B1096895
theorem B75905029 : Blo 381763 75905029 := bstep (se 4 (by rfl) ⟨7116096, by rfl⟩ : syracuseStep 75905029 = 14232193) B14232193
theorem B1949183 : Blo 381763 1949183 := bstep (se 1 (by rfl) ⟨1461887, by rfl⟩ : syracuseStep 1949183 = 2923775) B2923775
theorem B8313455 : Blo 381763 8313455 := bstep (se 1 (by rfl) ⟨6235091, by rfl⟩ : syracuseStep 8313455 = 12470183) B12470183
theorem B384795 : Blo 381763 384795 := bstep (se 1 (by rfl) ⟨288596, by rfl⟩ : syracuseStep 384795 = 577193) B577193
theorem B4251473 : Blo 381763 4251473 := bstep (se 2 (by rfl) ⟨1594302, by rfl⟩ : syracuseStep 4251473 = 3188605) B3188605
theorem B1242665 : Blo 381763 1242665 := bstep (se 2 (by rfl) ⟨465999, by rfl⟩ : syracuseStep 1242665 = 931999) B931999
theorem B1473833 : Blo 381763 1473833 := bstep (se 2 (by rfl) ⟨552687, by rfl⟩ : syracuseStep 1473833 = 1105375) B1105375
theorem B5542303 : Blo 381763 5542303 := bstep (se 1 (by rfl) ⟨4156727, by rfl⟩ : syracuseStep 5542303 = 8313455) B8313455
theorem B828443 : Blo 381763 828443 := bstep (se 1 (by rfl) ⟨621332, by rfl⟩ : syracuseStep 828443 = 1242665) B1242665
theorem B2834315 : Blo 381763 2834315 := bstep (se 1 (by rfl) ⟨2125736, by rfl⟩ : syracuseStep 2834315 = 4251473) B4251473
theorem B101206705 : Blo 381763 101206705 := bstep (se 2 (by rfl) ⟨37952514, by rfl⟩ : syracuseStep 101206705 = 75905029) B75905029
theorem B1299455 : Blo 381763 1299455 := bstep (se 1 (by rfl) ⟨974591, by rfl⟩ : syracuseStep 1299455 = 1949183) B1949183
theorem B3168767 : Blo 381763 3168767 := bstep (se 1 (by rfl) ⟨2376575, by rfl⟩ : syracuseStep 3168767 = 4753151) B4753151
theorem B975017 : Blo 381763 975017 := bstep (se 2 (by rfl) ⟨365631, by rfl⟩ : syracuseStep 975017 = 731263) B731263
theorem B3930221 : Blo 381763 3930221 := bstep (se 3 (by rfl) ⟨736916, by rfl⟩ : syracuseStep 3930221 = 1473833) B1473833
theorem B134942273 : Blo 381763 134942273 := bstep (se 2 (by rfl) ⟨50603352, by rfl⟩ : syracuseStep 134942273 = 101206705) B101206705
theorem B866303 : Blo 381763 866303 := bstep (se 1 (by rfl) ⟨649727, by rfl⟩ : syracuseStep 866303 = 1299455) B1299455
theorem B7389737 : Blo 381763 7389737 := bstep (se 2 (by rfl) ⟨2771151, by rfl⟩ : syracuseStep 7389737 = 5542303) B5542303
theorem B1889543 : Blo 381763 1889543 := bstep (se 1 (by rfl) ⟨1417157, by rfl⟩ : syracuseStep 1889543 = 2834315) B2834315
theorem B650011 : Blo 381763 650011 := bstep (se 1 (by rfl) ⟨487508, by rfl⟩ : syracuseStep 650011 = 975017) B975017
theorem B552295 : Blo 381763 552295 := bstep (se 1 (by rfl) ⟨414221, by rfl⟩ : syracuseStep 552295 = 828443) B828443
theorem B8450045 : Blo 381763 8450045 := bstep (se 3 (by rfl) ⟨1584383, by rfl⟩ : syracuseStep 8450045 = 3168767) B3168767
theorem B2620147 : Blo 381763 2620147 := bstep (se 1 (by rfl) ⟨1965110, by rfl⟩ : syracuseStep 2620147 = 3930221) B3930221
theorem B4926491 : Blo 381763 4926491 := bstep (se 1 (by rfl) ⟨3694868, by rfl⟩ : syracuseStep 4926491 = 7389737) B7389737
theorem B89961515 : Blo 381763 89961515 := bstep (se 1 (by rfl) ⟨67471136, by rfl⟩ : syracuseStep 89961515 = 134942273) B134942273
theorem B1259695 : Blo 381763 1259695 := bstep (se 1 (by rfl) ⟨944771, by rfl⟩ : syracuseStep 1259695 = 1889543) B1889543
theorem B866681 : Blo 381763 866681 := bstep (se 2 (by rfl) ⟨325005, by rfl⟩ : syracuseStep 866681 = 650011) B650011
theorem B736393 : Blo 381763 736393 := bstep (se 2 (by rfl) ⟨276147, by rfl⟩ : syracuseStep 736393 = 552295) B552295
theorem B3493529 : Blo 381763 3493529 := bstep (se 2 (by rfl) ⟨1310073, by rfl⟩ : syracuseStep 3493529 = 2620147) B2620147
theorem B577535 : Blo 381763 577535 := bstep (se 1 (by rfl) ⟨433151, by rfl⟩ : syracuseStep 577535 = 866303) B866303
theorem B5633363 : Blo 381763 5633363 := bstep (se 1 (by rfl) ⟨4225022, by rfl⟩ : syracuseStep 5633363 = 8450045) B8450045
theorem B6718373 : Blo 381763 6718373 := bstep (se 4 (by rfl) ⟨629847, by rfl⟩ : syracuseStep 6718373 = 1259695) B1259695
theorem B2329019 : Blo 381763 2329019 := bstep (se 1 (by rfl) ⟨1746764, by rfl⟩ : syracuseStep 2329019 = 3493529) B3493529
theorem B3284327 : Blo 381763 3284327 := bstep (se 1 (by rfl) ⟨2463245, by rfl⟩ : syracuseStep 3284327 = 4926491) B4926491
theorem B59974343 : Blo 381763 59974343 := bstep (se 1 (by rfl) ⟨44980757, by rfl⟩ : syracuseStep 59974343 = 89961515) B89961515
theorem B3755575 : Blo 381763 3755575 := bstep (se 1 (by rfl) ⟨2816681, by rfl⟩ : syracuseStep 3755575 = 5633363) B5633363
theorem B577787 : Blo 381763 577787 := bstep (se 1 (by rfl) ⟨433340, by rfl⟩ : syracuseStep 577787 = 866681) B866681
theorem B385023 : Blo 381763 385023 := bstep (se 1 (by rfl) ⟨288767, by rfl⟩ : syracuseStep 385023 = 577535) B577535
theorem B981857 : Blo 381763 981857 := bstep (se 2 (by rfl) ⟨368196, by rfl⟩ : syracuseStep 981857 = 736393) B736393
theorem B39982895 : Blo 381763 39982895 := bstep (se 1 (by rfl) ⟨29987171, by rfl⟩ : syracuseStep 39982895 = 59974343) B59974343
theorem B1552679 : Blo 381763 1552679 := bstep (se 1 (by rfl) ⟨1164509, by rfl⟩ : syracuseStep 1552679 = 2329019) B2329019
theorem B4478915 : Blo 381763 4478915 := bstep (se 1 (by rfl) ⟨3359186, by rfl⟩ : syracuseStep 4478915 = 6718373) B6718373
theorem B385191 : Blo 381763 385191 := bstep (se 1 (by rfl) ⟨288893, by rfl⟩ : syracuseStep 385191 = 577787) B577787
theorem B5007433 : Blo 381763 5007433 := bstep (se 2 (by rfl) ⟨1877787, by rfl⟩ : syracuseStep 5007433 = 3755575) B3755575
theorem B2189551 : Blo 381763 2189551 := bstep (se 1 (by rfl) ⟨1642163, by rfl⟩ : syracuseStep 2189551 = 3284327) B3284327
theorem B654571 : Blo 381763 654571 := bstep (se 1 (by rfl) ⟨490928, by rfl⟩ : syracuseStep 654571 = 981857) B981857
theorem B2919401 : Blo 381763 2919401 := bstep (se 2 (by rfl) ⟨1094775, by rfl⟩ : syracuseStep 2919401 = 2189551) B2189551
theorem B26655263 : Blo 381763 26655263 := bstep (se 1 (by rfl) ⟨19991447, by rfl⟩ : syracuseStep 26655263 = 39982895) B39982895
theorem B11943773 : Blo 381763 11943773 := bstep (se 3 (by rfl) ⟨2239457, by rfl⟩ : syracuseStep 11943773 = 4478915) B4478915
theorem B3491045 : Blo 381763 3491045 := bstep (se 4 (by rfl) ⟨327285, by rfl⟩ : syracuseStep 3491045 = 654571) B654571
theorem B1035119 : Blo 381763 1035119 := bstep (se 1 (by rfl) ⟨776339, by rfl⟩ : syracuseStep 1035119 = 1552679) B1552679
theorem B6676577 : Blo 381763 6676577 := bstep (se 2 (by rfl) ⟨2503716, by rfl⟩ : syracuseStep 6676577 = 5007433) B5007433
theorem B2327363 : Blo 381763 2327363 := bstep (se 1 (by rfl) ⟨1745522, by rfl⟩ : syracuseStep 2327363 = 3491045) B3491045
theorem B690079 : Blo 381763 690079 := bstep (se 1 (by rfl) ⟨517559, by rfl⟩ : syracuseStep 690079 = 1035119) B1035119
theorem B17770175 : Blo 381763 17770175 := bstep (se 1 (by rfl) ⟨13327631, by rfl⟩ : syracuseStep 17770175 = 26655263) B26655263
theorem B1946267 : Blo 381763 1946267 := bstep (se 1 (by rfl) ⟨1459700, by rfl⟩ : syracuseStep 1946267 = 2919401) B2919401
theorem B4451051 : Blo 381763 4451051 := bstep (se 1 (by rfl) ⟨3338288, by rfl⟩ : syracuseStep 4451051 = 6676577) B6676577
theorem B7962515 : Blo 381763 7962515 := bstep (se 1 (by rfl) ⟨5971886, by rfl⟩ : syracuseStep 7962515 = 11943773) B11943773
theorem B920105 : Blo 381763 920105 := bstep (se 2 (by rfl) ⟨345039, by rfl⟩ : syracuseStep 920105 = 690079) B690079
theorem B1551575 : Blo 381763 1551575 := bstep (se 1 (by rfl) ⟨1163681, by rfl⟩ : syracuseStep 1551575 = 2327363) B2327363
theorem B11846783 : Blo 381763 11846783 := bstep (se 1 (by rfl) ⟨8885087, by rfl⟩ : syracuseStep 11846783 = 17770175) B17770175
theorem B2967367 : Blo 381763 2967367 := bstep (se 1 (by rfl) ⟨2225525, by rfl⟩ : syracuseStep 2967367 = 4451051) B4451051
theorem B1297511 : Blo 381763 1297511 := bstep (se 1 (by rfl) ⟨973133, by rfl⟩ : syracuseStep 1297511 = 1946267) B1946267
theorem B5308343 : Blo 381763 5308343 := bstep (se 1 (by rfl) ⟨3981257, by rfl⟩ : syracuseStep 5308343 = 7962515) B7962515
theorem B31591421 : Blo 381763 31591421 := bstep (se 3 (by rfl) ⟨5923391, by rfl⟩ : syracuseStep 31591421 = 11846783) B11846783
theorem B865007 : Blo 381763 865007 := bstep (se 1 (by rfl) ⟨648755, by rfl⟩ : syracuseStep 865007 = 1297511) B1297511
theorem B1034383 : Blo 381763 1034383 := bstep (se 1 (by rfl) ⟨775787, by rfl⟩ : syracuseStep 1034383 = 1551575) B1551575
theorem B613403 : Blo 381763 613403 := bstep (se 1 (by rfl) ⟨460052, by rfl⟩ : syracuseStep 613403 = 920105) B920105
theorem B3956489 : Blo 381763 3956489 := bstep (se 2 (by rfl) ⟨1483683, by rfl⟩ : syracuseStep 3956489 = 2967367) B2967367
theorem B3538895 : Blo 381763 3538895 := bstep (se 1 (by rfl) ⟨2654171, by rfl⟩ : syracuseStep 3538895 = 5308343) B5308343
theorem B1379177 : Blo 381763 1379177 := bstep (se 2 (by rfl) ⟨517191, by rfl⟩ : syracuseStep 1379177 = 1034383) B1034383
theorem B408935 : Blo 381763 408935 := bstep (se 1 (by rfl) ⟨306701, by rfl⟩ : syracuseStep 408935 = 613403) B613403
theorem B2637659 : Blo 381763 2637659 := bstep (se 1 (by rfl) ⟨1978244, by rfl⟩ : syracuseStep 2637659 = 3956489) B3956489
theorem B576671 : Blo 381763 576671 := bstep (se 1 (by rfl) ⟨432503, by rfl⟩ : syracuseStep 576671 = 865007) B865007
theorem B21060947 : Blo 381763 21060947 := bstep (se 1 (by rfl) ⟨15795710, by rfl⟩ : syracuseStep 21060947 = 31591421) B31591421
theorem B37748213 : Blo 381763 37748213 := bstep (se 5 (by rfl) ⟨1769447, by rfl⟩ : syracuseStep 37748213 = 3538895) B3538895
theorem B919451 : Blo 381763 919451 := bstep (se 1 (by rfl) ⟨689588, by rfl⟩ : syracuseStep 919451 = 1379177) B1379177
theorem B1090493 : Blo 381763 1090493 := bstep (se 3 (by rfl) ⟨204467, by rfl⟩ : syracuseStep 1090493 = 408935) B408935
theorem B14040631 : Blo 381763 14040631 := bstep (se 1 (by rfl) ⟨10530473, by rfl⟩ : syracuseStep 14040631 = 21060947) B21060947
theorem B1758439 : Blo 381763 1758439 := bstep (se 1 (by rfl) ⟨1318829, by rfl⟩ : syracuseStep 1758439 = 2637659) B2637659
theorem B384447 : Blo 381763 384447 := bstep (se 1 (by rfl) ⟨288335, by rfl⟩ : syracuseStep 384447 = 576671) B576671
theorem B25165475 : Blo 381763 25165475 := bstep (se 1 (by rfl) ⟨18874106, by rfl⟩ : syracuseStep 25165475 = 37748213) B37748213
theorem B726995 : Blo 381763 726995 := bstep (se 1 (by rfl) ⟨545246, by rfl⟩ : syracuseStep 726995 = 1090493) B1090493
theorem B18720841 : Blo 381763 18720841 := bstep (se 2 (by rfl) ⟨7020315, by rfl⟩ : syracuseStep 18720841 = 14040631) B14040631
theorem B2344585 : Blo 381763 2344585 := bstep (se 2 (by rfl) ⟨879219, by rfl⟩ : syracuseStep 2344585 = 1758439) B1758439
theorem B2451869 : Blo 381763 2451869 := bstep (se 3 (by rfl) ⟨459725, by rfl⟩ : syracuseStep 2451869 = 919451) B919451
theorem B16776983 : Blo 381763 16776983 := bstep (se 1 (by rfl) ⟨12582737, by rfl⟩ : syracuseStep 16776983 = 25165475) B25165475
theorem B1938653 : Blo 381763 1938653 := bstep (se 3 (by rfl) ⟨363497, by rfl⟩ : syracuseStep 1938653 = 726995) B726995
theorem B11184655 : Blo 381763 11184655 := bstep (se 1 (by rfl) ⟨8388491, by rfl⟩ : syracuseStep 11184655 = 16776983) B16776983
theorem B3126113 : Blo 381763 3126113 := bstep (se 2 (by rfl) ⟨1172292, by rfl⟩ : syracuseStep 3126113 = 2344585) B2344585
theorem B24961121 : Blo 381763 24961121 := bstep (se 2 (by rfl) ⟨9360420, by rfl⟩ : syracuseStep 24961121 = 18720841) B18720841
theorem B1634579 : Blo 381763 1634579 := bstep (se 1 (by rfl) ⟨1225934, by rfl⟩ : syracuseStep 1634579 = 2451869) B2451869
theorem B14912873 : Blo 381763 14912873 := bstep (se 2 (by rfl) ⟨5592327, by rfl⟩ : syracuseStep 14912873 = 11184655) B11184655
theorem B1089719 : Blo 381763 1089719 := bstep (se 1 (by rfl) ⟨817289, by rfl⟩ : syracuseStep 1089719 = 1634579) B1634579
theorem B1292435 : Blo 381763 1292435 := bstep (se 1 (by rfl) ⟨969326, by rfl⟩ : syracuseStep 1292435 = 1938653) B1938653
theorem B2084075 : Blo 381763 2084075 := bstep (se 1 (by rfl) ⟨1563056, by rfl⟩ : syracuseStep 2084075 = 3126113) B3126113
theorem B16640747 : Blo 381763 16640747 := bstep (se 1 (by rfl) ⟨12480560, by rfl⟩ : syracuseStep 16640747 = 24961121) B24961121
theorem B726479 : Blo 381763 726479 := bstep (se 1 (by rfl) ⟨544859, by rfl⟩ : syracuseStep 726479 = 1089719) B1089719
theorem B861623 : Blo 381763 861623 := bstep (se 1 (by rfl) ⟨646217, by rfl⟩ : syracuseStep 861623 = 1292435) B1292435
theorem B1389383 : Blo 381763 1389383 := bstep (se 1 (by rfl) ⟨1042037, by rfl⟩ : syracuseStep 1389383 = 2084075) B2084075
theorem B9941915 : Blo 381763 9941915 := bstep (se 1 (by rfl) ⟨7456436, by rfl⟩ : syracuseStep 9941915 = 14912873) B14912873
theorem B11093831 : Blo 381763 11093831 := bstep (se 1 (by rfl) ⟨8320373, by rfl⟩ : syracuseStep 11093831 = 16640747) B16640747
theorem B926255 : Blo 381763 926255 := bstep (se 1 (by rfl) ⟨694691, by rfl⟩ : syracuseStep 926255 = 1389383) B1389383
theorem B6627943 : Blo 381763 6627943 := bstep (se 1 (by rfl) ⟨4970957, by rfl⟩ : syracuseStep 6627943 = 9941915) B9941915
theorem B574415 : Blo 381763 574415 := bstep (se 1 (by rfl) ⟨430811, by rfl⟩ : syracuseStep 574415 = 861623) B861623
theorem B7395887 : Blo 381763 7395887 := bstep (se 1 (by rfl) ⟨5546915, by rfl⟩ : syracuseStep 7395887 = 11093831) B11093831
theorem B484319 : Blo 381763 484319 := bstep (se 1 (by rfl) ⟨363239, by rfl⟩ : syracuseStep 484319 = 726479) B726479
theorem B2470013 : Blo 381763 2470013 := bstep (se 3 (by rfl) ⟨463127, by rfl⟩ : syracuseStep 2470013 = 926255) B926255
theorem B1291517 : Blo 381763 1291517 := bstep (se 3 (by rfl) ⟨242159, by rfl⟩ : syracuseStep 1291517 = 484319) B484319
theorem B4930591 : Blo 381763 4930591 := bstep (se 1 (by rfl) ⟨3697943, by rfl⟩ : syracuseStep 4930591 = 7395887) B7395887
theorem B382943 : Blo 381763 382943 := bstep (se 1 (by rfl) ⟨287207, by rfl⟩ : syracuseStep 382943 = 574415) B574415
theorem B8837257 : Blo 381763 8837257 := bstep (se 2 (by rfl) ⟨3313971, by rfl⟩ : syracuseStep 8837257 = 6627943) B6627943
theorem B1646675 : Blo 381763 1646675 := bstep (se 1 (by rfl) ⟨1235006, by rfl⟩ : syracuseStep 1646675 = 2470013) B2470013
theorem B861011 : Blo 381763 861011 := bstep (se 1 (by rfl) ⟨645758, by rfl⟩ : syracuseStep 861011 = 1291517) B1291517
theorem B11783009 : Blo 381763 11783009 := bstep (se 2 (by rfl) ⟨4418628, by rfl⟩ : syracuseStep 11783009 = 8837257) B8837257
theorem B6574121 : Blo 381763 6574121 := bstep (se 2 (by rfl) ⟨2465295, by rfl⟩ : syracuseStep 6574121 = 4930591) B4930591
theorem B1097783 : Blo 381763 1097783 := bstep (se 1 (by rfl) ⟨823337, by rfl⟩ : syracuseStep 1097783 = 1646675) B1646675
theorem B574007 : Blo 381763 574007 := bstep (se 1 (by rfl) ⟨430505, by rfl⟩ : syracuseStep 574007 = 861011) B861011
theorem B7855339 : Blo 381763 7855339 := bstep (se 1 (by rfl) ⟨5891504, by rfl⟩ : syracuseStep 7855339 = 11783009) B11783009
theorem B4382747 : Blo 381763 4382747 := bstep (se 1 (by rfl) ⟨3287060, by rfl⟩ : syracuseStep 4382747 = 6574121) B6574121
theorem B2921831 : Blo 381763 2921831 := bstep (se 1 (by rfl) ⟨2191373, by rfl⟩ : syracuseStep 2921831 = 4382747) B4382747
theorem B731855 : Blo 381763 731855 := bstep (se 1 (by rfl) ⟨548891, by rfl⟩ : syracuseStep 731855 = 1097783) B1097783
theorem B10473785 : Blo 381763 10473785 := bstep (se 2 (by rfl) ⟨3927669, by rfl⟩ : syracuseStep 10473785 = 7855339) B7855339
theorem B382671 : Blo 381763 382671 := bstep (se 1 (by rfl) ⟨287003, by rfl⟩ : syracuseStep 382671 = 574007) B574007
theorem B6982523 : Blo 381763 6982523 := bstep (se 1 (by rfl) ⟨5236892, by rfl⟩ : syracuseStep 6982523 = 10473785) B10473785
theorem B1947887 : Blo 381763 1947887 := bstep (se 1 (by rfl) ⟨1460915, by rfl⟩ : syracuseStep 1947887 = 2921831) B2921831
theorem B1951613 : Blo 381763 1951613 := bstep (se 3 (by rfl) ⟨365927, by rfl⟩ : syracuseStep 1951613 = 731855) B731855
theorem B4655015 : Blo 381763 4655015 := bstep (se 1 (by rfl) ⟨3491261, by rfl⟩ : syracuseStep 4655015 = 6982523) B6982523
theorem B1298591 : Blo 381763 1298591 := bstep (se 1 (by rfl) ⟨973943, by rfl⟩ : syracuseStep 1298591 = 1947887) B1947887
theorem B1301075 : Blo 381763 1301075 := bstep (se 1 (by rfl) ⟨975806, by rfl⟩ : syracuseStep 1301075 = 1951613) B1951613
theorem B865727 : Blo 381763 865727 := bstep (se 1 (by rfl) ⟨649295, by rfl⟩ : syracuseStep 865727 = 1298591) B1298591
theorem B867383 : Blo 381763 867383 := bstep (se 1 (by rfl) ⟨650537, by rfl⟩ : syracuseStep 867383 = 1301075) B1301075
theorem B3103343 : Blo 381763 3103343 := bstep (se 1 (by rfl) ⟨2327507, by rfl⟩ : syracuseStep 3103343 = 4655015) B4655015
theorem B2068895 : Blo 381763 2068895 := bstep (se 1 (by rfl) ⟨1551671, by rfl⟩ : syracuseStep 2068895 = 3103343) B3103343
theorem B577151 : Blo 381763 577151 := bstep (se 1 (by rfl) ⟨432863, by rfl⟩ : syracuseStep 577151 = 865727) B865727
theorem B578255 : Blo 381763 578255 := bstep (se 1 (by rfl) ⟨433691, by rfl⟩ : syracuseStep 578255 = 867383) B867383
theorem B1379263 : Blo 381763 1379263 := bstep (se 1 (by rfl) ⟨1034447, by rfl⟩ : syracuseStep 1379263 = 2068895) B2068895
theorem B384767 : Blo 381763 384767 := bstep (se 1 (by rfl) ⟨288575, by rfl⟩ : syracuseStep 384767 = 577151) B577151
theorem B385503 : Blo 381763 385503 := bstep (se 1 (by rfl) ⟨289127, by rfl⟩ : syracuseStep 385503 = 578255) B578255
theorem B1839017 : Blo 381763 1839017 := bstep (se 2 (by rfl) ⟨689631, by rfl⟩ : syracuseStep 1839017 = 1379263) B1379263
theorem B1226011 : Blo 381763 1226011 := bstep (se 1 (by rfl) ⟨919508, by rfl⟩ : syracuseStep 1226011 = 1839017) B1839017
theorem B1634681 : Blo 381763 1634681 := bstep (se 2 (by rfl) ⟨613005, by rfl⟩ : syracuseStep 1634681 = 1226011) B1226011
theorem B1089787 : Blo 381763 1089787 := bstep (se 1 (by rfl) ⟨817340, by rfl⟩ : syracuseStep 1089787 = 1634681) B1634681
theorem B1453049 : Blo 381763 1453049 := bstep (se 2 (by rfl) ⟨544893, by rfl⟩ : syracuseStep 1453049 = 1089787) B1089787
theorem B968699 : Blo 381763 968699 := bstep (se 1 (by rfl) ⟨726524, by rfl⟩ : syracuseStep 968699 = 1453049) B1453049
theorem B645799 : Blo 381763 645799 := bstep (se 1 (by rfl) ⟨484349, by rfl⟩ : syracuseStep 645799 = 968699) B968699
theorem B861065 : Blo 381763 861065 := bstep (se 2 (by rfl) ⟨322899, by rfl⟩ : syracuseStep 861065 = 645799) B645799
theorem B574043 : Blo 381763 574043 := bstep (se 1 (by rfl) ⟨430532, by rfl⟩ : syracuseStep 574043 = 861065) B861065
theorem B382695 : Blo 381763 382695 := bstep (se 1 (by rfl) ⟨287021, by rfl⟩ : syracuseStep 382695 = 574043) B574043

theorem C0 (j : ℕ) (h1 : 95440 ≤ j) (h2 : j ≤ 96139) : Blo 381763 (4 * j + 3) := by
  interval_cases j
  · exact B381763
  · exact B381767
  · exact B381771
  · exact B381775
  · exact B381779
  · exact B381783
  · exact B381787
  · exact B381791
  · exact B381795
  · exact B381799
  · exact B381803
  · exact B381807
  · exact B381811
  · exact B381815
  · exact B381819
  · exact B381823
  · exact B381827
  · exact B381831
  · exact B381835
  · exact B381839
  · exact B381843
  · exact B381847
  · exact B381851
  · exact B381855
  · exact B381859
  · exact B381863
  · exact B381867
  · exact B381871
  · exact B381875
  · exact B381879
  · exact B381883
  · exact B381887
  · exact B381891
  · exact B381895
  · exact B381899
  · exact B381903
  · exact B381907
  · exact B381911
  · exact B381915
  · exact B381919
  · exact B381923
  · exact B381927
  · exact B381931
  · exact B381935
  · exact B381939
  · exact B381943
  · exact B381947
  · exact B381951
  · exact B381955
  · exact B381959
  · exact B381963
  · exact B381967
  · exact B381971
  · exact B381975
  · exact B381979
  · exact B381983
  · exact B381987
  · exact B381991
  · exact B381995
  · exact B381999
  · exact B382003
  · exact B382007
  · exact B382011
  · exact B382015
  · exact B382019
  · exact B382023
  · exact B382027
  · exact B382031
  · exact B382035
  · exact B382039
  · exact B382043
  · exact B382047
  · exact B382051
  · exact B382055
  · exact B382059
  · exact B382063
  · exact B382067
  · exact B382071
  · exact B382075
  · exact B382079
  · exact B382083
  · exact B382087
  · exact B382091
  · exact B382095
  · exact B382099
  · exact B382103
  · exact B382107
  · exact B382111
  · exact B382115
  · exact B382119
  · exact B382123
  · exact B382127
  · exact B382131
  · exact B382135
  · exact B382139
  · exact B382143
  · exact B382147
  · exact B382151
  · exact B382155
  · exact B382159
  · exact B382163
  · exact B382167
  · exact B382171
  · exact B382175
  · exact B382179
  · exact B382183
  · exact B382187
  · exact B382191
  · exact B382195
  · exact B382199
  · exact B382203
  · exact B382207
  · exact B382211
  · exact B382215
  · exact B382219
  · exact B382223
  · exact B382227
  · exact B382231
  · exact B382235
  · exact B382239
  · exact B382243
  · exact B382247
  · exact B382251
  · exact B382255
  · exact B382259
  · exact B382263
  · exact B382267
  · exact B382271
  · exact B382275
  · exact B382279
  · exact B382283
  · exact B382287
  · exact B382291
  · exact B382295
  · exact B382299
  · exact B382303
  · exact B382307
  · exact B382311
  · exact B382315
  · exact B382319
  · exact B382323
  · exact B382327
  · exact B382331
  · exact B382335
  · exact B382339
  · exact B382343
  · exact B382347
  · exact B382351
  · exact B382355
  · exact B382359
  · exact B382363
  · exact B382367
  · exact B382371
  · exact B382375
  · exact B382379
  · exact B382383
  · exact B382387
  · exact B382391
  · exact B382395
  · exact B382399
  · exact B382403
  · exact B382407
  · exact B382411
  · exact B382415
  · exact B382419
  · exact B382423
  · exact B382427
  · exact B382431
  · exact B382435
  · exact B382439
  · exact B382443
  · exact B382447
  · exact B382451
  · exact B382455
  · exact B382459
  · exact B382463
  · exact B382467
  · exact B382471
  · exact B382475
  · exact B382479
  · exact B382483
  · exact B382487
  · exact B382491
  · exact B382495
  · exact B382499
  · exact B382503
  · exact B382507
  · exact B382511
  · exact B382515
  · exact B382519
  · exact B382523
  · exact B382527
  · exact B382531
  · exact B382535
  · exact B382539
  · exact B382543
  · exact B382547
  · exact B382551
  · exact B382555
  · exact B382559
  · exact B382563
  · exact B382567
  · exact B382571
  · exact B382575
  · exact B382579
  · exact B382583
  · exact B382587
  · exact B382591
  · exact B382595
  · exact B382599
  · exact B382603
  · exact B382607
  · exact B382611
  · exact B382615
  · exact B382619
  · exact B382623
  · exact B382627
  · exact B382631
  · exact B382635
  · exact B382639
  · exact B382643
  · exact B382647
  · exact B382651
  · exact B382655
  · exact B382659
  · exact B382663
  · exact B382667
  · exact B382671
  · exact B382675
  · exact B382679
  · exact B382683
  · exact B382687
  · exact B382691
  · exact B382695
  · exact B382699
  · exact B382703
  · exact B382707
  · exact B382711
  · exact B382715
  · exact B382719
  · exact B382723
  · exact B382727
  · exact B382731
  · exact B382735
  · exact B382739
  · exact B382743
  · exact B382747
  · exact B382751
  · exact B382755
  · exact B382759
  · exact B382763
  · exact B382767
  · exact B382771
  · exact B382775
  · exact B382779
  · exact B382783
  · exact B382787
  · exact B382791
  · exact B382795
  · exact B382799
  · exact B382803
  · exact B382807
  · exact B382811
  · exact B382815
  · exact B382819
  · exact B382823
  · exact B382827
  · exact B382831
  · exact B382835
  · exact B382839
  · exact B382843
  · exact B382847
  · exact B382851
  · exact B382855
  · exact B382859
  · exact B382863
  · exact B382867
  · exact B382871
  · exact B382875
  · exact B382879
  · exact B382883
  · exact B382887
  · exact B382891
  · exact B382895
  · exact B382899
  · exact B382903
  · exact B382907
  · exact B382911
  · exact B382915
  · exact B382919
  · exact B382923
  · exact B382927
  · exact B382931
  · exact B382935
  · exact B382939
  · exact B382943
  · exact B382947
  · exact B382951
  · exact B382955
  · exact B382959
  · exact B382963
  · exact B382967
  · exact B382971
  · exact B382975
  · exact B382979
  · exact B382983
  · exact B382987
  · exact B382991
  · exact B382995
  · exact B382999
  · exact B383003
  · exact B383007
  · exact B383011
  · exact B383015
  · exact B383019
  · exact B383023
  · exact B383027
  · exact B383031
  · exact B383035
  · exact B383039
  · exact B383043
  · exact B383047
  · exact B383051
  · exact B383055
  · exact B383059
  · exact B383063
  · exact B383067
  · exact B383071
  · exact B383075
  · exact B383079
  · exact B383083
  · exact B383087
  · exact B383091
  · exact B383095
  · exact B383099
  · exact B383103
  · exact B383107
  · exact B383111
  · exact B383115
  · exact B383119
  · exact B383123
  · exact B383127
  · exact B383131
  · exact B383135
  · exact B383139
  · exact B383143
  · exact B383147
  · exact B383151
  · exact B383155
  · exact B383159
  · exact B383163
  · exact B383167
  · exact B383171
  · exact B383175
  · exact B383179
  · exact B383183
  · exact B383187
  · exact B383191
  · exact B383195
  · exact B383199
  · exact B383203
  · exact B383207
  · exact B383211
  · exact B383215
  · exact B383219
  · exact B383223
  · exact B383227
  · exact B383231
  · exact B383235
  · exact B383239
  · exact B383243
  · exact B383247
  · exact B383251
  · exact B383255
  · exact B383259
  · exact B383263
  · exact B383267
  · exact B383271
  · exact B383275
  · exact B383279
  · exact B383283
  · exact B383287
  · exact B383291
  · exact B383295
  · exact B383299
  · exact B383303
  · exact B383307
  · exact B383311
  · exact B383315
  · exact B383319
  · exact B383323
  · exact B383327
  · exact B383331
  · exact B383335
  · exact B383339
  · exact B383343
  · exact B383347
  · exact B383351
  · exact B383355
  · exact B383359
  · exact B383363
  · exact B383367
  · exact B383371
  · exact B383375
  · exact B383379
  · exact B383383
  · exact B383387
  · exact B383391
  · exact B383395
  · exact B383399
  · exact B383403
  · exact B383407
  · exact B383411
  · exact B383415
  · exact B383419
  · exact B383423
  · exact B383427
  · exact B383431
  · exact B383435
  · exact B383439
  · exact B383443
  · exact B383447
  · exact B383451
  · exact B383455
  · exact B383459
  · exact B383463
  · exact B383467
  · exact B383471
  · exact B383475
  · exact B383479
  · exact B383483
  · exact B383487
  · exact B383491
  · exact B383495
  · exact B383499
  · exact B383503
  · exact B383507
  · exact B383511
  · exact B383515
  · exact B383519
  · exact B383523
  · exact B383527
  · exact B383531
  · exact B383535
  · exact B383539
  · exact B383543
  · exact B383547
  · exact B383551
  · exact B383555
  · exact B383559
  · exact B383563
  · exact B383567
  · exact B383571
  · exact B383575
  · exact B383579
  · exact B383583
  · exact B383587
  · exact B383591
  · exact B383595
  · exact B383599
  · exact B383603
  · exact B383607
  · exact B383611
  · exact B383615
  · exact B383619
  · exact B383623
  · exact B383627
  · exact B383631
  · exact B383635
  · exact B383639
  · exact B383643
  · exact B383647
  · exact B383651
  · exact B383655
  · exact B383659
  · exact B383663
  · exact B383667
  · exact B383671
  · exact B383675
  · exact B383679
  · exact B383683
  · exact B383687
  · exact B383691
  · exact B383695
  · exact B383699
  · exact B383703
  · exact B383707
  · exact B383711
  · exact B383715
  · exact B383719
  · exact B383723
  · exact B383727
  · exact B383731
  · exact B383735
  · exact B383739
  · exact B383743
  · exact B383747
  · exact B383751
  · exact B383755
  · exact B383759
  · exact B383763
  · exact B383767
  · exact B383771
  · exact B383775
  · exact B383779
  · exact B383783
  · exact B383787
  · exact B383791
  · exact B383795
  · exact B383799
  · exact B383803
  · exact B383807
  · exact B383811
  · exact B383815
  · exact B383819
  · exact B383823
  · exact B383827
  · exact B383831
  · exact B383835
  · exact B383839
  · exact B383843
  · exact B383847
  · exact B383851
  · exact B383855
  · exact B383859
  · exact B383863
  · exact B383867
  · exact B383871
  · exact B383875
  · exact B383879
  · exact B383883
  · exact B383887
  · exact B383891
  · exact B383895
  · exact B383899
  · exact B383903
  · exact B383907
  · exact B383911
  · exact B383915
  · exact B383919
  · exact B383923
  · exact B383927
  · exact B383931
  · exact B383935
  · exact B383939
  · exact B383943
  · exact B383947
  · exact B383951
  · exact B383955
  · exact B383959
  · exact B383963
  · exact B383967
  · exact B383971
  · exact B383975
  · exact B383979
  · exact B383983
  · exact B383987
  · exact B383991
  · exact B383995
  · exact B383999
  · exact B384003
  · exact B384007
  · exact B384011
  · exact B384015
  · exact B384019
  · exact B384023
  · exact B384027
  · exact B384031
  · exact B384035
  · exact B384039
  · exact B384043
  · exact B384047
  · exact B384051
  · exact B384055
  · exact B384059
  · exact B384063
  · exact B384067
  · exact B384071
  · exact B384075
  · exact B384079
  · exact B384083
  · exact B384087
  · exact B384091
  · exact B384095
  · exact B384099
  · exact B384103
  · exact B384107
  · exact B384111
  · exact B384115
  · exact B384119
  · exact B384123
  · exact B384127
  · exact B384131
  · exact B384135
  · exact B384139
  · exact B384143
  · exact B384147
  · exact B384151
  · exact B384155
  · exact B384159
  · exact B384163
  · exact B384167
  · exact B384171
  · exact B384175
  · exact B384179
  · exact B384183
  · exact B384187
  · exact B384191
  · exact B384195
  · exact B384199
  · exact B384203
  · exact B384207
  · exact B384211
  · exact B384215
  · exact B384219
  · exact B384223
  · exact B384227
  · exact B384231
  · exact B384235
  · exact B384239
  · exact B384243
  · exact B384247
  · exact B384251
  · exact B384255
  · exact B384259
  · exact B384263
  · exact B384267
  · exact B384271
  · exact B384275
  · exact B384279
  · exact B384283
  · exact B384287
  · exact B384291
  · exact B384295
  · exact B384299
  · exact B384303
  · exact B384307
  · exact B384311
  · exact B384315
  · exact B384319
  · exact B384323
  · exact B384327
  · exact B384331
  · exact B384335
  · exact B384339
  · exact B384343
  · exact B384347
  · exact B384351
  · exact B384355
  · exact B384359
  · exact B384363
  · exact B384367
  · exact B384371
  · exact B384375
  · exact B384379
  · exact B384383
  · exact B384387
  · exact B384391
  · exact B384395
  · exact B384399
  · exact B384403
  · exact B384407
  · exact B384411
  · exact B384415
  · exact B384419
  · exact B384423
  · exact B384427
  · exact B384431
  · exact B384435
  · exact B384439
  · exact B384443
  · exact B384447
  · exact B384451
  · exact B384455
  · exact B384459
  · exact B384463
  · exact B384467
  · exact B384471
  · exact B384475
  · exact B384479
  · exact B384483
  · exact B384487
  · exact B384491
  · exact B384495
  · exact B384499
  · exact B384503
  · exact B384507
  · exact B384511
  · exact B384515
  · exact B384519
  · exact B384523
  · exact B384527
  · exact B384531
  · exact B384535
  · exact B384539
  · exact B384543
  · exact B384547
  · exact B384551
  · exact B384555
  · exact B384559

theorem C1 (j : ℕ) (h1 : 96140 ≤ j) (h2 : j ≤ 96440) : Blo 381763 (4 * j + 3) := by
  interval_cases j
  · exact B384563
  · exact B384567
  · exact B384571
  · exact B384575
  · exact B384579
  · exact B384583
  · exact B384587
  · exact B384591
  · exact B384595
  · exact B384599
  · exact B384603
  · exact B384607
  · exact B384611
  · exact B384615
  · exact B384619
  · exact B384623
  · exact B384627
  · exact B384631
  · exact B384635
  · exact B384639
  · exact B384643
  · exact B384647
  · exact B384651
  · exact B384655
  · exact B384659
  · exact B384663
  · exact B384667
  · exact B384671
  · exact B384675
  · exact B384679
  · exact B384683
  · exact B384687
  · exact B384691
  · exact B384695
  · exact B384699
  · exact B384703
  · exact B384707
  · exact B384711
  · exact B384715
  · exact B384719
  · exact B384723
  · exact B384727
  · exact B384731
  · exact B384735
  · exact B384739
  · exact B384743
  · exact B384747
  · exact B384751
  · exact B384755
  · exact B384759
  · exact B384763
  · exact B384767
  · exact B384771
  · exact B384775
  · exact B384779
  · exact B384783
  · exact B384787
  · exact B384791
  · exact B384795
  · exact B384799
  · exact B384803
  · exact B384807
  · exact B384811
  · exact B384815
  · exact B384819
  · exact B384823
  · exact B384827
  · exact B384831
  · exact B384835
  · exact B384839
  · exact B384843
  · exact B384847
  · exact B384851
  · exact B384855
  · exact B384859
  · exact B384863
  · exact B384867
  · exact B384871
  · exact B384875
  · exact B384879
  · exact B384883
  · exact B384887
  · exact B384891
  · exact B384895
  · exact B384899
  · exact B384903
  · exact B384907
  · exact B384911
  · exact B384915
  · exact B384919
  · exact B384923
  · exact B384927
  · exact B384931
  · exact B384935
  · exact B384939
  · exact B384943
  · exact B384947
  · exact B384951
  · exact B384955
  · exact B384959
  · exact B384963
  · exact B384967
  · exact B384971
  · exact B384975
  · exact B384979
  · exact B384983
  · exact B384987
  · exact B384991
  · exact B384995
  · exact B384999
  · exact B385003
  · exact B385007
  · exact B385011
  · exact B385015
  · exact B385019
  · exact B385023
  · exact B385027
  · exact B385031
  · exact B385035
  · exact B385039
  · exact B385043
  · exact B385047
  · exact B385051
  · exact B385055
  · exact B385059
  · exact B385063
  · exact B385067
  · exact B385071
  · exact B385075
  · exact B385079
  · exact B385083
  · exact B385087
  · exact B385091
  · exact B385095
  · exact B385099
  · exact B385103
  · exact B385107
  · exact B385111
  · exact B385115
  · exact B385119
  · exact B385123
  · exact B385127
  · exact B385131
  · exact B385135
  · exact B385139
  · exact B385143
  · exact B385147
  · exact B385151
  · exact B385155
  · exact B385159
  · exact B385163
  · exact B385167
  · exact B385171
  · exact B385175
  · exact B385179
  · exact B385183
  · exact B385187
  · exact B385191
  · exact B385195
  · exact B385199
  · exact B385203
  · exact B385207
  · exact B385211
  · exact B385215
  · exact B385219
  · exact B385223
  · exact B385227
  · exact B385231
  · exact B385235
  · exact B385239
  · exact B385243
  · exact B385247
  · exact B385251
  · exact B385255
  · exact B385259
  · exact B385263
  · exact B385267
  · exact B385271
  · exact B385275
  · exact B385279
  · exact B385283
  · exact B385287
  · exact B385291
  · exact B385295
  · exact B385299
  · exact B385303
  · exact B385307
  · exact B385311
  · exact B385315
  · exact B385319
  · exact B385323
  · exact B385327
  · exact B385331
  · exact B385335
  · exact B385339
  · exact B385343
  · exact B385347
  · exact B385351
  · exact B385355
  · exact B385359
  · exact B385363
  · exact B385367
  · exact B385371
  · exact B385375
  · exact B385379
  · exact B385383
  · exact B385387
  · exact B385391
  · exact B385395
  · exact B385399
  · exact B385403
  · exact B385407
  · exact B385411
  · exact B385415
  · exact B385419
  · exact B385423
  · exact B385427
  · exact B385431
  · exact B385435
  · exact B385439
  · exact B385443
  · exact B385447
  · exact B385451
  · exact B385455
  · exact B385459
  · exact B385463
  · exact B385467
  · exact B385471
  · exact B385475
  · exact B385479
  · exact B385483
  · exact B385487
  · exact B385491
  · exact B385495
  · exact B385499
  · exact B385503
  · exact B385507
  · exact B385511
  · exact B385515
  · exact B385519
  · exact B385523
  · exact B385527
  · exact B385531
  · exact B385535
  · exact B385539
  · exact B385543
  · exact B385547
  · exact B385551
  · exact B385555
  · exact B385559
  · exact B385563
  · exact B385567
  · exact B385571
  · exact B385575
  · exact B385579
  · exact B385583
  · exact B385587
  · exact B385591
  · exact B385595
  · exact B385599
  · exact B385603
  · exact B385607
  · exact B385611
  · exact B385615
  · exact B385619
  · exact B385623
  · exact B385627
  · exact B385631
  · exact B385635
  · exact B385639
  · exact B385643
  · exact B385647
  · exact B385651
  · exact B385655
  · exact B385659
  · exact B385663
  · exact B385667
  · exact B385671
  · exact B385675
  · exact B385679
  · exact B385683
  · exact B385687
  · exact B385691
  · exact B385695
  · exact B385699
  · exact B385703
  · exact B385707
  · exact B385711
  · exact B385715
  · exact B385719
  · exact B385723
  · exact B385727
  · exact B385731
  · exact B385735
  · exact B385739
  · exact B385743
  · exact B385747
  · exact B385751
  · exact B385755
  · exact B385759
  · exact B385763

theorem solution (m : ℕ) (hlo : 381763 ≤ m) (hhi : m ≤ 385763) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 95440 ≤ j := by omega
    have hj2 : j ≤ 96440 := by omega
    have hb : Blo 381763 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 96140 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
