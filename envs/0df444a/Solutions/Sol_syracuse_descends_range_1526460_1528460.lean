-- Prove2me | solution 1 for syracuse_descends_range_1526460_1528460
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:04:36.316176+00:00
-- url     : https://prove2.me/submissions/2c4865de-0efa-4631-b1b0-c834db9ce63c

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


theorem B1835017 : Blo 1526460 1835017 := bbase (se 2 (by rfl) ⟨688131, by rfl⟩ : syracuseStep 1835017 = 1376263) (by norm_num)
theorem B8822837 : Blo 1526460 8822837 := bbase (se 5 (by rfl) ⟨413570, by rfl⟩ : syracuseStep 8822837 = 827141) (by norm_num)
theorem B2900053 : Blo 1526460 2900053 := bbase (se 8 (by rfl) ⟨16992, by rfl⟩ : syracuseStep 2900053 = 33985) (by norm_num)
theorem B3866717 : Blo 1526460 3866717 := bbase (se 3 (by rfl) ⟨725009, by rfl⟩ : syracuseStep 3866717 = 1450019) (by norm_num)
theorem B1933409 : Blo 1526460 1933409 := bbase (se 2 (by rfl) ⟨725028, by rfl⟩ : syracuseStep 1933409 = 1450057) (by norm_num)
theorem B1933465 : Blo 1526460 1933465 := bbase (se 2 (by rfl) ⟨725049, by rfl⟩ : syracuseStep 1933465 = 1450099) (by norm_num)
theorem B5152949 : Blo 1526460 5152949 := bbase (se 5 (by rfl) ⟨241544, by rfl⟩ : syracuseStep 5152949 = 483089) (by norm_num)
theorem B1630405 : Blo 1526460 1630405 := bbase (se 4 (by rfl) ⟨152850, by rfl⟩ : syracuseStep 1630405 = 305701) (by norm_num)
theorem B4350149 : Blo 1526460 4350149 := bbase (se 4 (by rfl) ⟨407826, by rfl⟩ : syracuseStep 4350149 = 815653) (by norm_num)
theorem B1933561 : Blo 1526460 1933561 := bbase (se 2 (by rfl) ⟨725085, by rfl⟩ : syracuseStep 1933561 = 1450171) (by norm_num)
theorem B1630477 : Blo 1526460 1630477 := bbase (se 3 (by rfl) ⟨305714, by rfl⟩ : syracuseStep 1630477 = 611429) (by norm_num)
theorem B3260749 : Blo 1526460 3260749 := bbase (se 3 (by rfl) ⟨611390, by rfl⟩ : syracuseStep 3260749 = 1222781) (by norm_num)
theorem B9290069 : Blo 1526460 9290069 := bbase (se 10 (by rfl) ⟨13608, by rfl⟩ : syracuseStep 9290069 = 27217) (by norm_num)
theorem B2900357 : Blo 1526460 2900357 := bbase (se 4 (by rfl) ⟨271908, by rfl⟩ : syracuseStep 2900357 = 543817) (by norm_num)
theorem B7340453 : Blo 1526460 7340453 := bbase (se 4 (by rfl) ⟨688167, by rfl⟩ : syracuseStep 7340453 = 1376335) (by norm_num)
theorem B3096997 : Blo 1526460 3096997 := bbase (se 4 (by rfl) ⟨290343, by rfl⟩ : syracuseStep 3096997 = 580687) (by norm_num)
theorem B1933733 : Blo 1526460 1933733 := bbase (se 4 (by rfl) ⟨181287, by rfl⟩ : syracuseStep 1933733 = 362575) (by norm_num)
theorem B3350965 : Blo 1526460 3350965 := bbase (se 5 (by rfl) ⟨157076, by rfl⟩ : syracuseStep 3350965 = 314153) (by norm_num)
theorem B3867061 : Blo 1526460 3867061 := bbase (se 5 (by rfl) ⟨181268, by rfl⟩ : syracuseStep 3867061 = 362537) (by norm_num)
theorem B7733717 : Blo 1526460 7733717 := bbase (se 7 (by rfl) ⟨90629, by rfl⟩ : syracuseStep 7733717 = 181259) (by norm_num)
theorem B1933789 : Blo 1526460 1933789 := bbase (se 3 (by rfl) ⟨362585, by rfl⟩ : syracuseStep 1933789 = 725171) (by norm_num)
theorem B2753045 : Blo 1526460 2753045 := bbase (se 6 (by rfl) ⟨64524, by rfl⟩ : syracuseStep 2753045 = 129049) (by norm_num)
theorem B3138085 : Blo 1526460 3138085 := bbase (se 4 (by rfl) ⟨294195, by rfl⟩ : syracuseStep 3138085 = 588391) (by norm_num)
theorem B3867173 : Blo 1526460 3867173 := bbase (se 4 (by rfl) ⟨362547, by rfl⟩ : syracuseStep 3867173 = 725095) (by norm_num)
theorem B1933885 : Blo 1526460 1933885 := bbase (se 3 (by rfl) ⟨362603, by rfl⟩ : syracuseStep 1933885 = 725207) (by norm_num)
theorem B5800517 : Blo 1526460 5800517 := bbase (se 4 (by rfl) ⟨543798, by rfl⟩ : syracuseStep 5800517 = 1087597) (by norm_num)
theorem B5153381 : Blo 1526460 5153381 := bbase (se 4 (by rfl) ⟨483129, by rfl⟩ : syracuseStep 5153381 = 966259) (by norm_num)
theorem B4350581 : Blo 1526460 4350581 := bbase (se 5 (by rfl) ⟨203933, by rfl⟩ : syracuseStep 4350581 = 407867) (by norm_num)
theorem B1630849 : Blo 1526460 1630849 := bbase (se 2 (by rfl) ⟨611568, by rfl⟩ : syracuseStep 1630849 = 1223137) (by norm_num)
theorem B1548941 : Blo 1526460 1548941 := bbase (se 3 (by rfl) ⟨290426, by rfl⟩ : syracuseStep 1548941 = 580853) (by norm_num)
theorem B1548977 : Blo 1526460 1548977 := bbase (se 2 (by rfl) ⟨580866, by rfl⟩ : syracuseStep 1548977 = 1161733) (by norm_num)
theorem B3867365 : Blo 1526460 3867365 := bbase (se 4 (by rfl) ⟨362565, by rfl⟩ : syracuseStep 3867365 = 725131) (by norm_num)
theorem B1934057 : Blo 1526460 1934057 := bbase (se 2 (by rfl) ⟨725271, by rfl⟩ : syracuseStep 1934057 = 1450543) (by norm_num)
theorem B1934113 : Blo 1526460 1934113 := bbase (se 2 (by rfl) ⟨725292, by rfl⟩ : syracuseStep 1934113 = 1450585) (by norm_num)
theorem B1958737 : Blo 1526460 1958737 := bbase (se 2 (by rfl) ⟨734526, by rfl⟩ : syracuseStep 1958737 = 1469053) (by norm_num)
theorem B5800805 : Blo 1526460 5800805 := bbase (se 4 (by rfl) ⟨543825, by rfl⟩ : syracuseStep 5800805 = 1087651) (by norm_num)
theorem B3097453 : Blo 1526460 3097453 := bbase (se 3 (by rfl) ⟨580772, by rfl⟩ : syracuseStep 3097453 = 1161545) (by norm_num)
theorem B1934209 : Blo 1526460 1934209 := bbase (se 2 (by rfl) ⟨725328, by rfl⟩ : syracuseStep 1934209 = 1450657) (by norm_num)
theorem B1549201 : Blo 1526460 1549201 := bbase (se 2 (by rfl) ⟨580950, by rfl⟩ : syracuseStep 1549201 = 1161901) (by norm_num)
theorem B3670957 : Blo 1526460 3670957 := bbase (se 3 (by rfl) ⟨688304, by rfl⟩ : syracuseStep 3670957 = 1376609) (by norm_num)
theorem B1631225 : Blo 1526460 1631225 := bbase (se 2 (by rfl) ⟨611709, by rfl⟩ : syracuseStep 1631225 = 1223419) (by norm_num)
theorem B5153813 : Blo 1526460 5153813 := bbase (se 6 (by rfl) ⟨120792, by rfl⟩ : syracuseStep 5153813 = 241585) (by norm_num)
theorem B1934381 : Blo 1526460 1934381 := bbase (se 3 (by rfl) ⟨362696, by rfl⟩ : syracuseStep 1934381 = 725393) (by norm_num)
theorem B3867709 : Blo 1526460 3867709 := bbase (se 3 (by rfl) ⟨725195, by rfl⟩ : syracuseStep 3867709 = 1450391) (by norm_num)
theorem B1631297 : Blo 1526460 1631297 := bbase (se 2 (by rfl) ⟨611736, by rfl⟩ : syracuseStep 1631297 = 1223473) (by norm_num)
theorem B1836113 : Blo 1526460 1836113 := bbase (se 2 (by rfl) ⟨688542, by rfl⟩ : syracuseStep 1836113 = 1377085) (by norm_num)
theorem B1934437 : Blo 1526460 1934437 := bbase (se 4 (by rfl) ⟨181353, by rfl⟩ : syracuseStep 1934437 = 362707) (by norm_num)
theorem B4891765 : Blo 1526460 4891765 := bbase (se 5 (by rfl) ⟨229301, by rfl⟩ : syracuseStep 4891765 = 458603) (by norm_num)
theorem B2901109 : Blo 1526460 2901109 := bbase (se 5 (by rfl) ⟨135989, by rfl⟩ : syracuseStep 2901109 = 271979) (by norm_num)
theorem B3867821 : Blo 1526460 3867821 := bbase (se 3 (by rfl) ⟨725216, by rfl⟩ : syracuseStep 3867821 = 1450433) (by norm_num)
theorem B13935797 : Blo 1526460 13935797 := bbase (se 5 (by rfl) ⟨653240, by rfl⟩ : syracuseStep 13935797 = 1306481) (by norm_num)
theorem B3261637 : Blo 1526460 3261637 := bbase (se 4 (by rfl) ⟨305778, by rfl⟩ : syracuseStep 3261637 = 611557) (by norm_num)
theorem B47056085 : Blo 1526460 47056085 := bbase (se 7 (by rfl) ⟨551438, by rfl⟩ : syracuseStep 47056085 = 1102877) (by norm_num)
theorem B1631485 : Blo 1526460 1631485 := bbase (se 3 (by rfl) ⟨305903, by rfl⟩ : syracuseStep 1631485 = 611807) (by norm_num)
theorem B2901253 : Blo 1526460 2901253 := bbase (se 4 (by rfl) ⟨271992, by rfl⟩ : syracuseStep 2901253 = 543985) (by norm_num)
theorem B3671381 : Blo 1526460 3671381 := bbase (se 12 (by rfl) ⟨1344, by rfl⟩ : syracuseStep 3671381 = 2689) (by norm_num)
theorem B4351333 : Blo 1526460 4351333 := bbase (se 4 (by rfl) ⟨407937, by rfl⟩ : syracuseStep 4351333 = 815875) (by norm_num)
theorem B3868013 : Blo 1526460 3868013 := bbase (se 3 (by rfl) ⟨725252, by rfl⟩ : syracuseStep 3868013 = 1450505) (by norm_num)
theorem B1860989 : Blo 1526460 1860989 := bbase (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) (by norm_num)
theorem B2901413 : Blo 1526460 2901413 := bbase (se 4 (by rfl) ⟨272007, by rfl⟩ : syracuseStep 2901413 = 544015) (by norm_num)
theorem B1959337 : Blo 1526460 1959337 := bbase (se 2 (by rfl) ⟨734751, by rfl⟩ : syracuseStep 1959337 = 1469503) (by norm_num)
theorem B1631669 : Blo 1526460 1631669 := bbase (se 5 (by rfl) ⟨76484, by rfl⟩ : syracuseStep 1631669 = 152969) (by norm_num)
theorem B5154245 : Blo 1526460 5154245 := bbase (se 4 (by rfl) ⟨483210, by rfl⟩ : syracuseStep 5154245 = 966421) (by norm_num)
theorem B4130261 : Blo 1526460 4130261 := bbase (se 7 (by rfl) ⟨48401, by rfl⟩ : syracuseStep 4130261 = 96803) (by norm_num)
theorem B6964741 : Blo 1526460 6964741 := bbase (se 4 (by rfl) ⟨652944, by rfl⟩ : syracuseStep 6964741 = 1305889) (by norm_num)
theorem B2901557 : Blo 1526460 2901557 := bbase (se 5 (by rfl) ⟨136010, by rfl⟩ : syracuseStep 2901557 = 272021) (by norm_num)
theorem B4130389 : Blo 1526460 4130389 := bbase (se 8 (by rfl) ⟨24201, by rfl⟩ : syracuseStep 4130389 = 48403) (by norm_num)
theorem B3671669 : Blo 1526460 3671669 := bbase (se 5 (by rfl) ⟨172109, by rfl⟩ : syracuseStep 3671669 = 344219) (by norm_num)
theorem B3262133 : Blo 1526460 3262133 := bbase (se 5 (by rfl) ⟨152912, by rfl⟩ : syracuseStep 3262133 = 305825) (by norm_num)
theorem B3868357 : Blo 1526460 3868357 := bbase (se 4 (by rfl) ⟨362658, by rfl⟩ : syracuseStep 3868357 = 725317) (by norm_num)
theorem B7735013 : Blo 1526460 7735013 := bbase (se 4 (by rfl) ⟨725157, by rfl⟩ : syracuseStep 7735013 = 1450315) (by norm_num)
theorem B3868469 : Blo 1526460 3868469 := bbase (se 5 (by rfl) ⟨181334, by rfl⟩ : syracuseStep 3868469 = 362669) (by norm_num)
theorem B5154677 : Blo 1526460 5154677 := bbase (se 5 (by rfl) ⟨241625, by rfl⟩ : syracuseStep 5154677 = 483251) (by norm_num)
theorem B3868661 : Blo 1526460 3868661 := bbase (se 5 (by rfl) ⟨181343, by rfl⟩ : syracuseStep 3868661 = 362687) (by norm_num)
theorem B5801989 : Blo 1526460 5801989 := bbase (se 4 (by rfl) ⟨543936, by rfl⟩ : syracuseStep 5801989 = 1087873) (by norm_num)
theorem B3434597 : Blo 1526460 3434597 := bbase (se 4 (by rfl) ⟨321993, by rfl⟩ : syracuseStep 3434597 = 643987) (by norm_num)
theorem B3434669 : Blo 1526460 3434669 := bbase (se 3 (by rfl) ⟨644000, by rfl⟩ : syracuseStep 3434669 = 1288001) (by norm_num)
theorem B1960133 : Blo 1526460 1960133 := bbase (se 4 (by rfl) ⟨183762, by rfl⟩ : syracuseStep 1960133 = 367525) (by norm_num)
theorem B3434741 : Blo 1526460 3434741 := bbase (se 5 (by rfl) ⟨161003, by rfl⟩ : syracuseStep 3434741 = 322007) (by norm_num)
theorem B5155109 : Blo 1526460 5155109 := bbase (se 4 (by rfl) ⟨483291, by rfl⟩ : syracuseStep 5155109 = 966583) (by norm_num)
theorem B5802293 : Blo 1526460 5802293 := bbase (se 5 (by rfl) ⟨271982, by rfl⟩ : syracuseStep 5802293 = 543965) (by norm_num)
theorem B3434813 : Blo 1526460 3434813 := bbase (se 3 (by rfl) ⟨644027, by rfl⟩ : syracuseStep 3434813 = 1288055) (by norm_num)
theorem B29804885 : Blo 1526460 29804885 := bbase (se 10 (by rfl) ⟨43659, by rfl⟩ : syracuseStep 29804885 = 87319) (by norm_num)
theorem B18581845 : Blo 1526460 18581845 := bbase (se 10 (by rfl) ⟨27219, by rfl⟩ : syracuseStep 18581845 = 54439) (by norm_num)
theorem B3434885 : Blo 1526460 3434885 := bbase (se 4 (by rfl) ⟨322020, by rfl⟩ : syracuseStep 3434885 = 644041) (by norm_num)
theorem B3434957 : Blo 1526460 3434957 := bbase (se 3 (by rfl) ⟨644054, by rfl⟩ : syracuseStep 3434957 = 1288109) (by norm_num)
theorem B3435029 : Blo 1526460 3435029 := bbase (se 6 (by rfl) ⟨80508, by rfl⟩ : syracuseStep 3435029 = 161017) (by norm_num)
theorem B3262997 : Blo 1526460 3262997 := bbase (se 6 (by rfl) ⟨76476, by rfl⟩ : syracuseStep 3262997 = 152953) (by norm_num)
theorem B2648621 : Blo 1526460 2648621 := bbase (se 3 (by rfl) ⟨496616, by rfl⟩ : syracuseStep 2648621 = 993233) (by norm_num)
theorem B3435101 : Blo 1526460 3435101 := bbase (se 3 (by rfl) ⟨644081, by rfl⟩ : syracuseStep 3435101 = 1288163) (by norm_num)
theorem B12380789 : Blo 1526460 12380789 := bbase (se 5 (by rfl) ⟨580349, by rfl⟩ : syracuseStep 12380789 = 1160699) (by norm_num)
theorem B3918469 : Blo 1526460 3918469 := bbase (se 4 (by rfl) ⟨367356, by rfl⟩ : syracuseStep 3918469 = 734713) (by norm_num)
theorem B6965909 : Blo 1526460 6965909 := bbase (se 6 (by rfl) ⟨163263, by rfl⟩ : syracuseStep 6965909 = 326527) (by norm_num)
theorem B3435173 : Blo 1526460 3435173 := bbase (se 4 (by rfl) ⟨322047, by rfl⟩ : syracuseStep 3435173 = 644095) (by norm_num)
theorem B2091685 : Blo 1526460 2091685 := bbase (se 4 (by rfl) ⟨196095, by rfl⟩ : syracuseStep 2091685 = 392191) (by norm_num)
theorem B3263141 : Blo 1526460 3263141 := bbase (se 4 (by rfl) ⟨305919, by rfl⟩ : syracuseStep 3263141 = 611839) (by norm_num)
theorem B2173645 : Blo 1526460 2173645 := bbase (se 3 (by rfl) ⟨407558, by rfl⟩ : syracuseStep 2173645 = 815117) (by norm_num)
theorem B5155541 : Blo 1526460 5155541 := bbase (se 7 (by rfl) ⟨60416, by rfl⟩ : syracuseStep 5155541 = 120833) (by norm_num)
theorem B3435245 : Blo 1526460 3435245 := bbase (se 3 (by rfl) ⟨644108, by rfl⟩ : syracuseStep 3435245 = 1288217) (by norm_num)
theorem B6523685 : Blo 1526460 6523685 := bbase (se 4 (by rfl) ⟨611595, by rfl⟩ : syracuseStep 6523685 = 1223191) (by norm_num)
theorem B3435317 : Blo 1526460 3435317 := bbase (se 5 (by rfl) ⟨161030, by rfl⟩ : syracuseStep 3435317 = 322061) (by norm_num)
theorem B4647797 : Blo 1526460 4647797 := bbase (se 5 (by rfl) ⟨217865, by rfl⟩ : syracuseStep 4647797 = 435731) (by norm_num)
theorem B3435389 : Blo 1526460 3435389 := bbase (se 3 (by rfl) ⟨644135, by rfl⟩ : syracuseStep 3435389 = 1288271) (by norm_num)
theorem B3435461 : Blo 1526460 3435461 := bbase (se 4 (by rfl) ⟨322074, by rfl⟩ : syracuseStep 3435461 = 644149) (by norm_num)
theorem B3918797 : Blo 1526460 3918797 := bbase (se 3 (by rfl) ⟨734774, by rfl⟩ : syracuseStep 3918797 = 1469549) (by norm_num)
theorem B7736309 : Blo 1526460 7736309 := bbase (se 5 (by rfl) ⟨362639, by rfl⟩ : syracuseStep 7736309 = 725279) (by norm_num)
theorem B3435533 : Blo 1526460 3435533 := bbase (se 3 (by rfl) ⟨644162, by rfl⟩ : syracuseStep 3435533 = 1288325) (by norm_num)
theorem B2173981 : Blo 1526460 2173981 := bbase (se 3 (by rfl) ⟨407621, by rfl⟩ : syracuseStep 2173981 = 815243) (by norm_num)
theorem B3435605 : Blo 1526460 3435605 := bbase (se 8 (by rfl) ⟨20130, by rfl⟩ : syracuseStep 3435605 = 40261) (by norm_num)
theorem B5155973 : Blo 1526460 5155973 := bbase (se 4 (by rfl) ⟨483372, by rfl⟩ : syracuseStep 5155973 = 966745) (by norm_num)
theorem B3435677 : Blo 1526460 3435677 := bbase (se 3 (by rfl) ⟨644189, by rfl⟩ : syracuseStep 3435677 = 1288379) (by norm_num)
theorem B8694965 : Blo 1526460 8694965 := bbase (se 5 (by rfl) ⟨407576, by rfl⟩ : syracuseStep 8694965 = 815153) (by norm_num)
theorem B13053109 : Blo 1526460 13053109 := bbase (se 5 (by rfl) ⟨611864, by rfl⟩ : syracuseStep 13053109 = 1223729) (by norm_num)
theorem B3484853 : Blo 1526460 3484853 := bbase (se 5 (by rfl) ⟨163352, by rfl⟩ : syracuseStep 3484853 = 326705) (by norm_num)
theorem B3435749 : Blo 1526460 3435749 := bbase (se 4 (by rfl) ⟨322101, by rfl⟩ : syracuseStep 3435749 = 644203) (by norm_num)
theorem B2174197 : Blo 1526460 2174197 := bbase (se 5 (by rfl) ⟨101915, by rfl⟩ : syracuseStep 2174197 = 203831) (by norm_num)
theorem B3722525 : Blo 1526460 3722525 := bbase (se 3 (by rfl) ⟨697973, by rfl⟩ : syracuseStep 3722525 = 1395947) (by norm_num)
theorem B3435821 : Blo 1526460 3435821 := bbase (se 3 (by rfl) ⟨644216, by rfl⟩ : syracuseStep 3435821 = 1288433) (by norm_num)
theorem B3484981 : Blo 1526460 3484981 := bbase (se 5 (by rfl) ⟨163358, by rfl⟩ : syracuseStep 3484981 = 326717) (by norm_num)
theorem B3435893 : Blo 1526460 3435893 := bbase (se 5 (by rfl) ⟨161057, by rfl⟩ : syracuseStep 3435893 = 322115) (by norm_num)
theorem B3485053 : Blo 1526460 3485053 := bbase (se 3 (by rfl) ⟨653447, by rfl⟩ : syracuseStep 3485053 = 1306895) (by norm_num)
theorem B7335301 : Blo 1526460 7335301 := bbase (se 4 (by rfl) ⟨687684, by rfl⟩ : syracuseStep 7335301 = 1375369) (by norm_num)
theorem B3263885 : Blo 1526460 3263885 := bbase (se 3 (by rfl) ⟨611978, by rfl⟩ : syracuseStep 3263885 = 1223957) (by norm_num)
theorem B7728533 : Blo 1526460 7728533 := bbase (se 6 (by rfl) ⟨181137, by rfl⟩ : syracuseStep 7728533 = 362275) (by norm_num)
theorem B3435965 : Blo 1526460 3435965 := bbase (se 3 (by rfl) ⟨644243, by rfl⟩ : syracuseStep 3435965 = 1288487) (by norm_num)
theorem B1764821 : Blo 1526460 1764821 := bbase (se 7 (by rfl) ⟨20681, by rfl⟩ : syracuseStep 1764821 = 41363) (by norm_num)
theorem B3436037 : Blo 1526460 3436037 := bbase (se 4 (by rfl) ⟨322128, by rfl⟩ : syracuseStep 3436037 = 644257) (by norm_num)
theorem B5156405 : Blo 1526460 5156405 := bbase (se 5 (by rfl) ⟨241706, by rfl⟩ : syracuseStep 5156405 = 483413) (by norm_num)
theorem B3436109 : Blo 1526460 3436109 := bbase (se 3 (by rfl) ⟨644270, by rfl⟩ : syracuseStep 3436109 = 1288541) (by norm_num)
theorem B2174573 : Blo 1526460 2174573 := bbase (se 3 (by rfl) ⟨407732, by rfl⟩ : syracuseStep 2174573 = 815465) (by norm_num)
theorem B3436181 : Blo 1526460 3436181 := bbase (se 6 (by rfl) ⟨80535, by rfl⟩ : syracuseStep 3436181 = 161071) (by norm_num)
theorem B2576029 : Blo 1526460 2576029 := bbase (se 3 (by rfl) ⟨483005, by rfl⟩ : syracuseStep 2576029 = 966011) (by norm_num)
theorem B3436253 : Blo 1526460 3436253 := bbase (se 3 (by rfl) ⟨644297, by rfl⟩ : syracuseStep 3436253 = 1288595) (by norm_num)
theorem B2576117 : Blo 1526460 2576117 := bbase (se 5 (by rfl) ⟨120755, by rfl⟩ : syracuseStep 2576117 = 241511) (by norm_num)
theorem B3436325 : Blo 1526460 3436325 := bbase (se 4 (by rfl) ⟨322155, by rfl⟩ : syracuseStep 3436325 = 644311) (by norm_num)
theorem B3919661 : Blo 1526460 3919661 := bbase (se 3 (by rfl) ⟨734936, by rfl⟩ : syracuseStep 3919661 = 1469873) (by norm_num)
theorem B2322245 : Blo 1526460 2322245 := bbase (se 4 (by rfl) ⟨217710, by rfl⟩ : syracuseStep 2322245 = 435421) (by norm_num)
theorem B3436397 : Blo 1526460 3436397 := bbase (se 3 (by rfl) ⟨644324, by rfl⟩ : syracuseStep 3436397 = 1288649) (by norm_num)
theorem B2576245 : Blo 1526460 2576245 := bbase (se 5 (by rfl) ⟨120761, by rfl⟩ : syracuseStep 2576245 = 241523) (by norm_num)
theorem B4894597 : Blo 1526460 4894597 := bbase (se 4 (by rfl) ⟨458868, by rfl⟩ : syracuseStep 4894597 = 917737) (by norm_num)
theorem B3436469 : Blo 1526460 3436469 := bbase (se 5 (by rfl) ⟨161084, by rfl⟩ : syracuseStep 3436469 = 322169) (by norm_num)
theorem B4894661 : Blo 1526460 4894661 := bbase (se 4 (by rfl) ⟨458874, by rfl⟩ : syracuseStep 4894661 = 917749) (by norm_num)
theorem B2576333 : Blo 1526460 2576333 := bbase (se 3 (by rfl) ⟨483062, by rfl⟩ : syracuseStep 2576333 = 966125) (by norm_num)
theorem B6279125 : Blo 1526460 6279125 := bbase (se 7 (by rfl) ⟨73583, by rfl⟩ : syracuseStep 6279125 = 147167) (by norm_num)
theorem B5156837 : Blo 1526460 5156837 := bbase (se 4 (by rfl) ⟨483453, by rfl⟩ : syracuseStep 5156837 = 966907) (by norm_num)
theorem B3436541 : Blo 1526460 3436541 := bbase (se 3 (by rfl) ⟨644351, by rfl⟩ : syracuseStep 3436541 = 1288703) (by norm_num)
theorem B2289701 : Blo 1526460 2289701 := bbase (se 4 (by rfl) ⟨214659, by rfl⟩ : syracuseStep 2289701 = 429319) (by norm_num)
theorem B2289725 : Blo 1526460 2289725 := bbase (se 3 (by rfl) ⟨429323, by rfl⟩ : syracuseStep 2289725 = 858647) (by norm_num)
theorem B3436613 : Blo 1526460 3436613 := bbase (se 4 (by rfl) ⟨322182, by rfl⟩ : syracuseStep 3436613 = 644365) (by norm_num)
theorem B2576461 : Blo 1526460 2576461 := bbase (se 3 (by rfl) ⟨483086, by rfl⟩ : syracuseStep 2576461 = 966173) (by norm_num)
theorem B2289749 : Blo 1526460 2289749 := bbase (se 8 (by rfl) ⟨13416, by rfl⟩ : syracuseStep 2289749 = 26833) (by norm_num)
theorem B32206933 : Blo 1526460 32206933 := bbase (se 8 (by rfl) ⟨188712, by rfl⟩ : syracuseStep 32206933 = 377425) (by norm_num)
theorem B2289773 : Blo 1526460 2289773 := bbase (se 3 (by rfl) ⟨429332, by rfl⟩ : syracuseStep 2289773 = 858665) (by norm_num)
theorem B12390517 : Blo 1526460 12390517 := bbase (se 5 (by rfl) ⟨580805, by rfl⟩ : syracuseStep 12390517 = 1161611) (by norm_num)
theorem B2289797 : Blo 1526460 2289797 := bbase (se 4 (by rfl) ⟨214668, by rfl⟩ : syracuseStep 2289797 = 429337) (by norm_num)
theorem B3436685 : Blo 1526460 3436685 := bbase (se 3 (by rfl) ⟨644378, by rfl⟩ : syracuseStep 3436685 = 1288757) (by norm_num)
theorem B2289821 : Blo 1526460 2289821 := bbase (se 3 (by rfl) ⟨429341, by rfl⟩ : syracuseStep 2289821 = 858683) (by norm_num)
theorem B2576549 : Blo 1526460 2576549 := bbase (se 4 (by rfl) ⟨241551, by rfl⟩ : syracuseStep 2576549 = 483103) (by norm_num)
theorem B2289845 : Blo 1526460 2289845 := bbase (se 5 (by rfl) ⟨107336, by rfl⟩ : syracuseStep 2289845 = 214673) (by norm_num)
theorem B2289869 : Blo 1526460 2289869 := bbase (se 3 (by rfl) ⟨429350, by rfl⟩ : syracuseStep 2289869 = 858701) (by norm_num)
theorem B3436757 : Blo 1526460 3436757 := bbase (se 7 (by rfl) ⟨40274, by rfl⟩ : syracuseStep 3436757 = 80549) (by norm_num)
theorem B2289893 : Blo 1526460 2289893 := bbase (se 4 (by rfl) ⟨214677, by rfl⟩ : syracuseStep 2289893 = 429355) (by norm_num)
theorem B2355437 : Blo 1526460 2355437 := bbase (se 3 (by rfl) ⟨441644, by rfl⟩ : syracuseStep 2355437 = 883289) (by norm_num)
theorem B2289917 : Blo 1526460 2289917 := bbase (se 3 (by rfl) ⟨429359, by rfl⟩ : syracuseStep 2289917 = 858719) (by norm_num)
theorem B7737605 : Blo 1526460 7737605 := bbase (se 4 (by rfl) ⟨725400, by rfl⟩ : syracuseStep 7737605 = 1450801) (by norm_num)
theorem B2289941 : Blo 1526460 2289941 := bbase (se 6 (by rfl) ⟨53670, by rfl⟩ : syracuseStep 2289941 = 107341) (by norm_num)
theorem B3436829 : Blo 1526460 3436829 := bbase (se 3 (by rfl) ⟨644405, by rfl⟩ : syracuseStep 3436829 = 1288811) (by norm_num)
theorem B2576677 : Blo 1526460 2576677 := bbase (se 4 (by rfl) ⟨241563, by rfl⟩ : syracuseStep 2576677 = 483127) (by norm_num)
theorem B2289965 : Blo 1526460 2289965 := bbase (se 3 (by rfl) ⟨429368, by rfl⟩ : syracuseStep 2289965 = 858737) (by norm_num)
theorem B2289989 : Blo 1526460 2289989 := bbase (se 4 (by rfl) ⟨214686, by rfl⟩ : syracuseStep 2289989 = 429373) (by norm_num)
theorem B2290013 : Blo 1526460 2290013 := bbase (se 3 (by rfl) ⟨429377, by rfl⟩ : syracuseStep 2290013 = 858755) (by norm_num)
theorem B3436901 : Blo 1526460 3436901 := bbase (se 4 (by rfl) ⟨322209, by rfl⟩ : syracuseStep 3436901 = 644419) (by norm_num)
theorem B2290037 : Blo 1526460 2290037 := bbase (se 5 (by rfl) ⟨107345, by rfl⟩ : syracuseStep 2290037 = 214691) (by norm_num)
theorem B2576765 : Blo 1526460 2576765 := bbase (se 3 (by rfl) ⟨483143, by rfl⟩ : syracuseStep 2576765 = 966287) (by norm_num)
theorem B2290061 : Blo 1526460 2290061 := bbase (se 3 (by rfl) ⟨429386, by rfl⟩ : syracuseStep 2290061 = 858773) (by norm_num)
theorem B5157269 : Blo 1526460 5157269 := bbase (se 6 (by rfl) ⟨120873, by rfl⟩ : syracuseStep 5157269 = 241747) (by norm_num)
theorem B2290085 : Blo 1526460 2290085 := bbase (se 4 (by rfl) ⟨214695, by rfl⟩ : syracuseStep 2290085 = 429391) (by norm_num)
theorem B3436973 : Blo 1526460 3436973 := bbase (se 3 (by rfl) ⟨644432, by rfl⟩ : syracuseStep 3436973 = 1288865) (by norm_num)
theorem B14684597 : Blo 1526460 14684597 := bbase (se 5 (by rfl) ⟨688340, by rfl⟩ : syracuseStep 14684597 = 1376681) (by norm_num)
theorem B2290109 : Blo 1526460 2290109 := bbase (se 3 (by rfl) ⟨429395, by rfl⟩ : syracuseStep 2290109 = 858791) (by norm_num)
theorem B1741249 : Blo 1526460 1741249 := bbase (se 2 (by rfl) ⟨652968, by rfl⟩ : syracuseStep 1741249 = 1305937) (by norm_num)
theorem B2290133 : Blo 1526460 2290133 := bbase (se 7 (by rfl) ⟨26837, by rfl⟩ : syracuseStep 2290133 = 53675) (by norm_num)
theorem B2290157 : Blo 1526460 2290157 := bbase (se 3 (by rfl) ⟨429404, by rfl⟩ : syracuseStep 2290157 = 858809) (by norm_num)
theorem B3437045 : Blo 1526460 3437045 := bbase (se 5 (by rfl) ⟨161111, by rfl⟩ : syracuseStep 3437045 = 322223) (by norm_num)
theorem B2576893 : Blo 1526460 2576893 := bbase (se 3 (by rfl) ⟨483167, by rfl⟩ : syracuseStep 2576893 = 966335) (by norm_num)
theorem B2290181 : Blo 1526460 2290181 := bbase (se 4 (by rfl) ⟨214704, by rfl⟩ : syracuseStep 2290181 = 429409) (by norm_num)
theorem B6525461 : Blo 1526460 6525461 := bbase (se 6 (by rfl) ⟨152940, by rfl⟩ : syracuseStep 6525461 = 305881) (by norm_num)
theorem B2290205 : Blo 1526460 2290205 := bbase (se 3 (by rfl) ⟨429413, by rfl⟩ : syracuseStep 2290205 = 858827) (by norm_num)
theorem B2290229 : Blo 1526460 2290229 := bbase (se 5 (by rfl) ⟨107354, by rfl⟩ : syracuseStep 2290229 = 214709) (by norm_num)
theorem B3437117 : Blo 1526460 3437117 := bbase (se 3 (by rfl) ⟨644459, by rfl⟩ : syracuseStep 3437117 = 1288919) (by norm_num)
theorem B5222981 : Blo 1526460 5222981 := bbase (se 4 (by rfl) ⟨489654, by rfl⟩ : syracuseStep 5222981 = 979309) (by norm_num)
theorem B2290253 : Blo 1526460 2290253 := bbase (se 3 (by rfl) ⟨429422, by rfl⟩ : syracuseStep 2290253 = 858845) (by norm_num)
theorem B2576981 : Blo 1526460 2576981 := bbase (se 8 (by rfl) ⟨15099, by rfl⟩ : syracuseStep 2576981 = 30199) (by norm_num)
theorem B2290277 : Blo 1526460 2290277 := bbase (se 4 (by rfl) ⟨214713, by rfl⟩ : syracuseStep 2290277 = 429427) (by norm_num)
theorem B2290301 : Blo 1526460 2290301 := bbase (se 3 (by rfl) ⟨429431, by rfl⟩ : syracuseStep 2290301 = 858863) (by norm_num)
theorem B3437189 : Blo 1526460 3437189 := bbase (se 4 (by rfl) ⟨322236, by rfl⟩ : syracuseStep 3437189 = 644473) (by norm_num)
theorem B2290325 : Blo 1526460 2290325 := bbase (se 6 (by rfl) ⟨53679, by rfl⟩ : syracuseStep 2290325 = 107359) (by norm_num)
theorem B11162261 : Blo 1526460 11162261 := bbase (se 6 (by rfl) ⟨261615, by rfl⟩ : syracuseStep 11162261 = 523231) (by norm_num)
theorem B7729829 : Blo 1526460 7729829 := bbase (se 4 (by rfl) ⟨724671, by rfl⟩ : syracuseStep 7729829 = 1449343) (by norm_num)
theorem B2290349 : Blo 1526460 2290349 := bbase (se 3 (by rfl) ⟨429440, by rfl⟩ : syracuseStep 2290349 = 858881) (by norm_num)
theorem B5501621 : Blo 1526460 5501621 := bbase (se 5 (by rfl) ⟨257888, by rfl⟩ : syracuseStep 5501621 = 515777) (by norm_num)
theorem B2290373 : Blo 1526460 2290373 := bbase (se 4 (by rfl) ⟨214722, by rfl⟩ : syracuseStep 2290373 = 429445) (by norm_num)
theorem B3437261 : Blo 1526460 3437261 := bbase (se 3 (by rfl) ⟨644486, by rfl⟩ : syracuseStep 3437261 = 1288973) (by norm_num)
theorem B2577109 : Blo 1526460 2577109 := bbase (se 7 (by rfl) ⟨30200, by rfl⟩ : syracuseStep 2577109 = 60401) (by norm_num)
theorem B2290397 : Blo 1526460 2290397 := bbase (se 3 (by rfl) ⟨429449, by rfl⟩ : syracuseStep 2290397 = 858899) (by norm_num)
theorem B2290421 : Blo 1526460 2290421 := bbase (se 5 (by rfl) ⟨107363, by rfl⟩ : syracuseStep 2290421 = 214727) (by norm_num)
theorem B2290445 : Blo 1526460 2290445 := bbase (se 3 (by rfl) ⟨429458, by rfl⟩ : syracuseStep 2290445 = 858917) (by norm_num)
theorem B5796629 : Blo 1526460 5796629 := bbase (se 6 (by rfl) ⟨135858, by rfl⟩ : syracuseStep 5796629 = 271717) (by norm_num)
theorem B3437333 : Blo 1526460 3437333 := bbase (se 6 (by rfl) ⟨80562, by rfl⟩ : syracuseStep 3437333 = 161125) (by norm_num)
theorem B19583765 : Blo 1526460 19583765 := bbase (se 6 (by rfl) ⟨458994, by rfl⟩ : syracuseStep 19583765 = 917989) (by norm_num)
theorem B2290469 : Blo 1526460 2290469 := bbase (se 4 (by rfl) ⟨214731, by rfl⟩ : syracuseStep 2290469 = 429463) (by norm_num)
theorem B2577197 : Blo 1526460 2577197 := bbase (se 3 (by rfl) ⟨483224, by rfl⟩ : syracuseStep 2577197 = 966449) (by norm_num)
theorem B2290493 : Blo 1526460 2290493 := bbase (se 3 (by rfl) ⟨429467, by rfl⟩ : syracuseStep 2290493 = 858935) (by norm_num)
theorem B5157701 : Blo 1526460 5157701 := bbase (se 4 (by rfl) ⟨483534, by rfl⟩ : syracuseStep 5157701 = 967069) (by norm_num)
theorem B2290517 : Blo 1526460 2290517 := bbase (se 9 (by rfl) ⟨6710, by rfl⟩ : syracuseStep 2290517 = 13421) (by norm_num)
theorem B8704853 : Blo 1526460 8704853 := bbase (se 9 (by rfl) ⟨25502, by rfl⟩ : syracuseStep 8704853 = 51005) (by norm_num)
theorem B3437405 : Blo 1526460 3437405 := bbase (se 3 (by rfl) ⟨644513, by rfl⟩ : syracuseStep 3437405 = 1289027) (by norm_num)
theorem B2290541 : Blo 1526460 2290541 := bbase (se 3 (by rfl) ⟨429476, by rfl⟩ : syracuseStep 2290541 = 858953) (by norm_num)
theorem B2290565 : Blo 1526460 2290565 := bbase (se 4 (by rfl) ⟨214740, by rfl⟩ : syracuseStep 2290565 = 429481) (by norm_num)
theorem B2290589 : Blo 1526460 2290589 := bbase (se 3 (by rfl) ⟨429485, by rfl⟩ : syracuseStep 2290589 = 858971) (by norm_num)
theorem B3437477 : Blo 1526460 3437477 := bbase (se 4 (by rfl) ⟨322263, by rfl⟩ : syracuseStep 3437477 = 644527) (by norm_num)
theorem B2577325 : Blo 1526460 2577325 := bbase (se 3 (by rfl) ⟨483248, by rfl⟩ : syracuseStep 2577325 = 966497) (by norm_num)
theorem B2290613 : Blo 1526460 2290613 := bbase (se 5 (by rfl) ⟨107372, by rfl⟩ : syracuseStep 2290613 = 214745) (by norm_num)
theorem B2290637 : Blo 1526460 2290637 := bbase (se 3 (by rfl) ⟨429494, by rfl⟩ : syracuseStep 2290637 = 858989) (by norm_num)
theorem B2290661 : Blo 1526460 2290661 := bbase (se 4 (by rfl) ⟨214749, by rfl⟩ : syracuseStep 2290661 = 429499) (by norm_num)
theorem B5297125 : Blo 1526460 5297125 := bbase (se 4 (by rfl) ⟨496605, by rfl⟩ : syracuseStep 5297125 = 993211) (by norm_num)
theorem B3437549 : Blo 1526460 3437549 := bbase (se 3 (by rfl) ⟨644540, by rfl⟩ : syracuseStep 3437549 = 1289081) (by norm_num)
theorem B2290685 : Blo 1526460 2290685 := bbase (se 3 (by rfl) ⟨429503, by rfl⟩ : syracuseStep 2290685 = 859007) (by norm_num)
theorem B2175997 : Blo 1526460 2175997 := bbase (se 3 (by rfl) ⟨407999, by rfl⟩ : syracuseStep 2175997 = 815999) (by norm_num)
theorem B2577413 : Blo 1526460 2577413 := bbase (se 4 (by rfl) ⟨241632, by rfl⟩ : syracuseStep 2577413 = 483265) (by norm_num)
theorem B1741829 : Blo 1526460 1741829 := bbase (se 4 (by rfl) ⟨163296, by rfl⟩ : syracuseStep 1741829 = 326593) (by norm_num)
theorem B2290709 : Blo 1526460 2290709 := bbase (se 6 (by rfl) ⟨53688, by rfl⟩ : syracuseStep 2290709 = 107377) (by norm_num)
theorem B2446357 : Blo 1526460 2446357 := bbase (se 6 (by rfl) ⟨57336, by rfl⟩ : syracuseStep 2446357 = 114673) (by norm_num)
theorem B1717285 : Blo 1526460 1717285 := bbase (se 4 (by rfl) ⟨160995, by rfl⟩ : syracuseStep 1717285 = 321991) (by norm_num)
theorem B2290733 : Blo 1526460 2290733 := bbase (se 3 (by rfl) ⟨429512, by rfl⟩ : syracuseStep 2290733 = 859025) (by norm_num)
theorem B5796917 : Blo 1526460 5796917 := bbase (se 5 (by rfl) ⟨271730, by rfl⟩ : syracuseStep 5796917 = 543461) (by norm_num)
theorem B3437621 : Blo 1526460 3437621 := bbase (se 5 (by rfl) ⟨161138, by rfl⟩ : syracuseStep 3437621 = 322277) (by norm_num)
theorem B2290757 : Blo 1526460 2290757 := bbase (se 4 (by rfl) ⟨214758, by rfl⟩ : syracuseStep 2290757 = 429517) (by norm_num)
theorem B1717321 : Blo 1526460 1717321 := bbase (se 2 (by rfl) ⟨643995, by rfl⟩ : syracuseStep 1717321 = 1287991) (by norm_num)
theorem B2290781 : Blo 1526460 2290781 := bbase (se 3 (by rfl) ⟨429521, by rfl⟩ : syracuseStep 2290781 = 859043) (by norm_num)
theorem B1717357 : Blo 1526460 1717357 := bbase (se 3 (by rfl) ⟨322004, by rfl⟩ : syracuseStep 1717357 = 644009) (by norm_num)
theorem B2290805 : Blo 1526460 2290805 := bbase (se 5 (by rfl) ⟨107381, by rfl⟩ : syracuseStep 2290805 = 214763) (by norm_num)
theorem B13055093 : Blo 1526460 13055093 := bbase (se 5 (by rfl) ⟨611957, by rfl⟩ : syracuseStep 13055093 = 1223915) (by norm_num)
theorem B3437693 : Blo 1526460 3437693 := bbase (se 3 (by rfl) ⟨644567, by rfl⟩ : syracuseStep 3437693 = 1289135) (by norm_num)
theorem B2577541 : Blo 1526460 2577541 := bbase (se 4 (by rfl) ⟨241644, by rfl⟩ : syracuseStep 2577541 = 483289) (by norm_num)
theorem B2290829 : Blo 1526460 2290829 := bbase (se 3 (by rfl) ⟨429530, by rfl⟩ : syracuseStep 2290829 = 859061) (by norm_num)
theorem B1717393 : Blo 1526460 1717393 := bbase (se 2 (by rfl) ⟨644022, by rfl⟩ : syracuseStep 1717393 = 1288045) (by norm_num)
theorem B2290853 : Blo 1526460 2290853 := bbase (se 4 (by rfl) ⟨214767, by rfl⟩ : syracuseStep 2290853 = 429535) (by norm_num)
theorem B1717429 : Blo 1526460 1717429 := bbase (se 5 (by rfl) ⟨80504, by rfl⟩ : syracuseStep 1717429 = 161009) (by norm_num)
theorem B6968501 : Blo 1526460 6968501 := bbase (se 5 (by rfl) ⟨326648, by rfl⟩ : syracuseStep 6968501 = 653297) (by norm_num)
theorem B2290877 : Blo 1526460 2290877 := bbase (se 3 (by rfl) ⟨429539, by rfl⟩ : syracuseStep 2290877 = 859079) (by norm_num)
theorem B3437765 : Blo 1526460 3437765 := bbase (se 4 (by rfl) ⟨322290, by rfl⟩ : syracuseStep 3437765 = 644581) (by norm_num)
theorem B5223637 : Blo 1526460 5223637 := bbase (se 7 (by rfl) ⟨61214, by rfl⟩ : syracuseStep 5223637 = 122429) (by norm_num)
theorem B2290901 : Blo 1526460 2290901 := bbase (se 7 (by rfl) ⟨26846, by rfl⟩ : syracuseStep 2290901 = 53693) (by norm_num)
theorem B1717465 : Blo 1526460 1717465 := bbase (se 2 (by rfl) ⟨644049, by rfl⟩ : syracuseStep 1717465 = 1288099) (by norm_num)
theorem B2577629 : Blo 1526460 2577629 := bbase (se 3 (by rfl) ⟨483305, by rfl⟩ : syracuseStep 2577629 = 966611) (by norm_num)
theorem B2290925 : Blo 1526460 2290925 := bbase (se 3 (by rfl) ⟨429548, by rfl⟩ : syracuseStep 2290925 = 859097) (by norm_num)
theorem B5158133 : Blo 1526460 5158133 := bbase (se 5 (by rfl) ⟨241787, by rfl⟩ : syracuseStep 5158133 = 483575) (by norm_num)
theorem B1717501 : Blo 1526460 1717501 := bbase (se 3 (by rfl) ⟨322031, by rfl⟩ : syracuseStep 1717501 = 644063) (by norm_num)
theorem B2290949 : Blo 1526460 2290949 := bbase (se 4 (by rfl) ⟨214776, by rfl⟩ : syracuseStep 2290949 = 429553) (by norm_num)
theorem B3437837 : Blo 1526460 3437837 := bbase (se 3 (by rfl) ⟨644594, by rfl⟩ : syracuseStep 3437837 = 1289189) (by norm_num)
theorem B2446613 : Blo 1526460 2446613 := bbase (se 6 (by rfl) ⟨57342, by rfl⟩ : syracuseStep 2446613 = 114685) (by norm_num)
theorem B2290973 : Blo 1526460 2290973 := bbase (se 3 (by rfl) ⟨429557, by rfl⟩ : syracuseStep 2290973 = 859115) (by norm_num)
theorem B1717537 : Blo 1526460 1717537 := bbase (se 2 (by rfl) ⟨644076, by rfl⟩ : syracuseStep 1717537 = 1288153) (by norm_num)
theorem B2290997 : Blo 1526460 2290997 := bbase (se 5 (by rfl) ⟨107390, by rfl⟩ : syracuseStep 2290997 = 214781) (by norm_num)
theorem B1717573 : Blo 1526460 1717573 := bbase (se 4 (by rfl) ⟨161022, by rfl⟩ : syracuseStep 1717573 = 322045) (by norm_num)
theorem B2291021 : Blo 1526460 2291021 := bbase (se 3 (by rfl) ⟨429566, by rfl⟩ : syracuseStep 2291021 = 859133) (by norm_num)
theorem B89257301 : Blo 1526460 89257301 := bbase (se 13 (by rfl) ⟨16343, by rfl⟩ : syracuseStep 89257301 = 32687) (by norm_num)
theorem B3437909 : Blo 1526460 3437909 := bbase (se 13 (by rfl) ⟨629, by rfl⟩ : syracuseStep 3437909 = 1259) (by norm_num)
theorem B2577757 : Blo 1526460 2577757 := bbase (se 3 (by rfl) ⟨483329, by rfl⟩ : syracuseStep 2577757 = 966659) (by norm_num)
theorem B2291045 : Blo 1526460 2291045 := bbase (se 4 (by rfl) ⟨214785, by rfl⟩ : syracuseStep 2291045 = 429571) (by norm_num)
theorem B1717609 : Blo 1526460 1717609 := bbase (se 2 (by rfl) ⟨644103, by rfl⟩ : syracuseStep 1717609 = 1288207) (by norm_num)
theorem B3863933 : Blo 1526460 3863933 := bbase (se 3 (by rfl) ⟨724487, by rfl⟩ : syracuseStep 3863933 = 1448975) (by norm_num)
theorem B2291069 : Blo 1526460 2291069 := bbase (se 3 (by rfl) ⟨429575, by rfl⟩ : syracuseStep 2291069 = 859151) (by norm_num)
theorem B1717645 : Blo 1526460 1717645 := bbase (se 3 (by rfl) ⟨322058, by rfl⟩ : syracuseStep 1717645 = 644117) (by norm_num)
theorem B2291093 : Blo 1526460 2291093 := bbase (se 6 (by rfl) ⟨53697, by rfl⟩ : syracuseStep 2291093 = 107395) (by norm_num)
theorem B3437981 : Blo 1526460 3437981 := bbase (se 3 (by rfl) ⟨644621, by rfl⟩ : syracuseStep 3437981 = 1289243) (by norm_num)
theorem B2291117 : Blo 1526460 2291117 := bbase (se 3 (by rfl) ⟨429584, by rfl⟩ : syracuseStep 2291117 = 859169) (by norm_num)
theorem B1717681 : Blo 1526460 1717681 := bbase (se 2 (by rfl) ⟨644130, by rfl⟩ : syracuseStep 1717681 = 1288261) (by norm_num)
theorem B2577845 : Blo 1526460 2577845 := bbase (se 5 (by rfl) ⟨120836, by rfl⟩ : syracuseStep 2577845 = 241673) (by norm_num)
theorem B2291141 : Blo 1526460 2291141 := bbase (se 4 (by rfl) ⟨214794, by rfl⟩ : syracuseStep 2291141 = 429589) (by norm_num)
theorem B1717717 : Blo 1526460 1717717 := bbase (se 7 (by rfl) ⟨20129, by rfl⟩ : syracuseStep 1717717 = 40259) (by norm_num)
theorem B2446805 : Blo 1526460 2446805 := bbase (se 7 (by rfl) ⟨28673, by rfl⟩ : syracuseStep 2446805 = 57347) (by norm_num)
theorem B2291165 : Blo 1526460 2291165 := bbase (se 3 (by rfl) ⟨429593, by rfl⟩ : syracuseStep 2291165 = 859187) (by norm_num)
theorem B3438053 : Blo 1526460 3438053 := bbase (se 4 (by rfl) ⟨322317, by rfl⟩ : syracuseStep 3438053 = 644635) (by norm_num)
theorem B2291189 : Blo 1526460 2291189 := bbase (se 5 (by rfl) ⟨107399, by rfl⟩ : syracuseStep 2291189 = 214799) (by norm_num)
theorem B6526453 : Blo 1526460 6526453 := bbase (se 5 (by rfl) ⟨305927, by rfl⟩ : syracuseStep 6526453 = 611855) (by norm_num)
theorem B1717753 : Blo 1526460 1717753 := bbase (se 2 (by rfl) ⟨644157, by rfl⟩ : syracuseStep 1717753 = 1288315) (by norm_num)
theorem B2291213 : Blo 1526460 2291213 := bbase (se 3 (by rfl) ⟨429602, by rfl⟩ : syracuseStep 2291213 = 859205) (by norm_num)
theorem B1717789 : Blo 1526460 1717789 := bbase (se 3 (by rfl) ⟨322085, by rfl⟩ : syracuseStep 1717789 = 644171) (by norm_num)
theorem B2291237 : Blo 1526460 2291237 := bbase (se 4 (by rfl) ⟨214803, by rfl⟩ : syracuseStep 2291237 = 429607) (by norm_num)
theorem B3438125 : Blo 1526460 3438125 := bbase (se 3 (by rfl) ⟨644648, by rfl⟩ : syracuseStep 3438125 = 1289297) (by norm_num)
theorem B2577973 : Blo 1526460 2577973 := bbase (se 5 (by rfl) ⟨120842, by rfl⟩ : syracuseStep 2577973 = 241685) (by norm_num)
theorem B3864125 : Blo 1526460 3864125 := bbase (se 3 (by rfl) ⟨724523, by rfl⟩ : syracuseStep 3864125 = 1449047) (by norm_num)
theorem B2291261 : Blo 1526460 2291261 := bbase (se 3 (by rfl) ⟨429611, by rfl⟩ : syracuseStep 2291261 = 859223) (by norm_num)
theorem B1717825 : Blo 1526460 1717825 := bbase (se 2 (by rfl) ⟨644184, by rfl⟩ : syracuseStep 1717825 = 1288369) (by norm_num)
theorem B2291285 : Blo 1526460 2291285 := bbase (se 8 (by rfl) ⟨13425, by rfl⟩ : syracuseStep 2291285 = 26851) (by norm_num)
theorem B1717861 : Blo 1526460 1717861 := bbase (se 4 (by rfl) ⟨161049, by rfl⟩ : syracuseStep 1717861 = 322099) (by norm_num)
theorem B2291309 : Blo 1526460 2291309 := bbase (se 3 (by rfl) ⟨429620, by rfl⟩ : syracuseStep 2291309 = 859241) (by norm_num)
theorem B3438197 : Blo 1526460 3438197 := bbase (se 5 (by rfl) ⟨161165, by rfl⟩ : syracuseStep 3438197 = 322331) (by norm_num)
theorem B2291333 : Blo 1526460 2291333 := bbase (se 4 (by rfl) ⟨214812, by rfl⟩ : syracuseStep 2291333 = 429625) (by norm_num)
theorem B1717897 : Blo 1526460 1717897 := bbase (se 2 (by rfl) ⟨644211, by rfl⟩ : syracuseStep 1717897 = 1288423) (by norm_num)
theorem B2578061 : Blo 1526460 2578061 := bbase (se 3 (by rfl) ⟨483386, by rfl⟩ : syracuseStep 2578061 = 966773) (by norm_num)
theorem B2291357 : Blo 1526460 2291357 := bbase (se 3 (by rfl) ⟨429629, by rfl⟩ : syracuseStep 2291357 = 859259) (by norm_num)
theorem B1717933 : Blo 1526460 1717933 := bbase (se 3 (by rfl) ⟨322112, by rfl⟩ : syracuseStep 1717933 = 644225) (by norm_num)
theorem B2291381 : Blo 1526460 2291381 := bbase (se 5 (by rfl) ⟨107408, by rfl⟩ : syracuseStep 2291381 = 214817) (by norm_num)
theorem B3438269 : Blo 1526460 3438269 := bbase (se 3 (by rfl) ⟨644675, by rfl⟩ : syracuseStep 3438269 = 1289351) (by norm_num)
theorem B2291405 : Blo 1526460 2291405 := bbase (se 3 (by rfl) ⟨429638, by rfl⟩ : syracuseStep 2291405 = 859277) (by norm_num)
theorem B1717969 : Blo 1526460 1717969 := bbase (se 2 (by rfl) ⟨644238, by rfl⟩ : syracuseStep 1717969 = 1288477) (by norm_num)
theorem B2291429 : Blo 1526460 2291429 := bbase (se 4 (by rfl) ⟨214821, by rfl⟩ : syracuseStep 2291429 = 429643) (by norm_num)
theorem B1718005 : Blo 1526460 1718005 := bbase (se 5 (by rfl) ⟨80531, by rfl⟩ : syracuseStep 1718005 = 161063) (by norm_num)
theorem B2291453 : Blo 1526460 2291453 := bbase (se 3 (by rfl) ⟨429647, by rfl⟩ : syracuseStep 2291453 = 859295) (by norm_num)
theorem B3438341 : Blo 1526460 3438341 := bbase (se 4 (by rfl) ⟨322344, by rfl⟩ : syracuseStep 3438341 = 644689) (by norm_num)
theorem B2578189 : Blo 1526460 2578189 := bbase (se 3 (by rfl) ⟨483410, by rfl⟩ : syracuseStep 2578189 = 966821) (by norm_num)
theorem B2291477 : Blo 1526460 2291477 := bbase (se 6 (by rfl) ⟨53706, by rfl⟩ : syracuseStep 2291477 = 107413) (by norm_num)
theorem B1718041 : Blo 1526460 1718041 := bbase (se 2 (by rfl) ⟨644265, by rfl⟩ : syracuseStep 1718041 = 1288531) (by norm_num)
theorem B2291501 : Blo 1526460 2291501 := bbase (se 3 (by rfl) ⟨429656, by rfl⟩ : syracuseStep 2291501 = 859313) (by norm_num)
theorem B1718077 : Blo 1526460 1718077 := bbase (se 3 (by rfl) ⟨322139, by rfl⟩ : syracuseStep 1718077 = 644279) (by norm_num)
theorem B2291525 : Blo 1526460 2291525 := bbase (se 4 (by rfl) ⟨214830, by rfl⟩ : syracuseStep 2291525 = 429661) (by norm_num)
theorem B3438413 : Blo 1526460 3438413 := bbase (se 3 (by rfl) ⟨644702, by rfl⟩ : syracuseStep 3438413 = 1289405) (by norm_num)
theorem B2291549 : Blo 1526460 2291549 := bbase (se 3 (by rfl) ⟨429665, by rfl⟩ : syracuseStep 2291549 = 859331) (by norm_num)
theorem B1718113 : Blo 1526460 1718113 := bbase (se 2 (by rfl) ⟨644292, by rfl⟩ : syracuseStep 1718113 = 1288585) (by norm_num)
theorem B2578277 : Blo 1526460 2578277 := bbase (se 4 (by rfl) ⟨241713, by rfl⟩ : syracuseStep 2578277 = 483427) (by norm_num)
theorem B2291573 : Blo 1526460 2291573 := bbase (se 5 (by rfl) ⟨107417, by rfl⟩ : syracuseStep 2291573 = 214835) (by norm_num)
theorem B1718149 : Blo 1526460 1718149 := bbase (se 4 (by rfl) ⟨161076, by rfl⟩ : syracuseStep 1718149 = 322153) (by norm_num)
theorem B2291597 : Blo 1526460 2291597 := bbase (se 3 (by rfl) ⟨429674, by rfl⟩ : syracuseStep 2291597 = 859349) (by norm_num)
theorem B3864469 : Blo 1526460 3864469 := bbase (se 6 (by rfl) ⟨90573, by rfl⟩ : syracuseStep 3864469 = 181147) (by norm_num)
theorem B3438485 : Blo 1526460 3438485 := bbase (se 6 (by rfl) ⟨80589, by rfl⟩ : syracuseStep 3438485 = 161179) (by norm_num)
theorem B2291621 : Blo 1526460 2291621 := bbase (se 4 (by rfl) ⟨214839, by rfl⟩ : syracuseStep 2291621 = 429679) (by norm_num)
theorem B1718185 : Blo 1526460 1718185 := bbase (se 2 (by rfl) ⟨644319, by rfl⟩ : syracuseStep 1718185 = 1288639) (by norm_num)
theorem B7731125 : Blo 1526460 7731125 := bbase (se 5 (by rfl) ⟨362396, by rfl⟩ : syracuseStep 7731125 = 724793) (by norm_num)
theorem B2291645 : Blo 1526460 2291645 := bbase (se 3 (by rfl) ⟨429683, by rfl⟩ : syracuseStep 2291645 = 859367) (by norm_num)
theorem B1718221 : Blo 1526460 1718221 := bbase (se 3 (by rfl) ⟨322166, by rfl⟩ : syracuseStep 1718221 = 644333) (by norm_num)
theorem B7436245 : Blo 1526460 7436245 := bbase (se 7 (by rfl) ⟨87143, by rfl⟩ : syracuseStep 7436245 = 174287) (by norm_num)
theorem B2291669 : Blo 1526460 2291669 := bbase (se 7 (by rfl) ⟨26855, by rfl⟩ : syracuseStep 2291669 = 53711) (by norm_num)
theorem B3438557 : Blo 1526460 3438557 := bbase (se 3 (by rfl) ⟨644729, by rfl⟩ : syracuseStep 3438557 = 1289459) (by norm_num)
theorem B2578405 : Blo 1526460 2578405 := bbase (se 4 (by rfl) ⟨241725, by rfl⟩ : syracuseStep 2578405 = 483451) (by norm_num)
theorem B2291693 : Blo 1526460 2291693 := bbase (se 3 (by rfl) ⟨429692, by rfl⟩ : syracuseStep 2291693 = 859385) (by norm_num)
theorem B1718257 : Blo 1526460 1718257 := bbase (se 2 (by rfl) ⟨644346, by rfl⟩ : syracuseStep 1718257 = 1288693) (by norm_num)
theorem B4347893 : Blo 1526460 4347893 := bbase (se 5 (by rfl) ⟨203807, by rfl⟩ : syracuseStep 4347893 = 407615) (by norm_num)
theorem B6191093 : Blo 1526460 6191093 := bbase (se 5 (by rfl) ⟨290207, by rfl⟩ : syracuseStep 6191093 = 580415) (by norm_num)
theorem B3864581 : Blo 1526460 3864581 := bbase (se 4 (by rfl) ⟨362304, by rfl⟩ : syracuseStep 3864581 = 724609) (by norm_num)
theorem B2291717 : Blo 1526460 2291717 := bbase (se 4 (by rfl) ⟨214848, by rfl⟩ : syracuseStep 2291717 = 429697) (by norm_num)
theorem B1718293 : Blo 1526460 1718293 := bbase (se 6 (by rfl) ⟨40272, by rfl⟩ : syracuseStep 1718293 = 80545) (by norm_num)
theorem B2291741 : Blo 1526460 2291741 := bbase (se 3 (by rfl) ⟨429701, by rfl⟩ : syracuseStep 2291741 = 859403) (by norm_num)
theorem B2897957 : Blo 1526460 2897957 := bbase (se 4 (by rfl) ⟨271683, by rfl⟩ : syracuseStep 2897957 = 543367) (by norm_num)
theorem B3438629 : Blo 1526460 3438629 := bbase (se 4 (by rfl) ⟨322371, by rfl⟩ : syracuseStep 3438629 = 644743) (by norm_num)
theorem B2291765 : Blo 1526460 2291765 := bbase (se 5 (by rfl) ⟨107426, by rfl⟩ : syracuseStep 2291765 = 214853) (by norm_num)
theorem B1718329 : Blo 1526460 1718329 := bbase (se 2 (by rfl) ⟨644373, by rfl⟩ : syracuseStep 1718329 = 1288747) (by norm_num)
theorem B2578493 : Blo 1526460 2578493 := bbase (se 3 (by rfl) ⟨483467, by rfl⟩ : syracuseStep 2578493 = 966935) (by norm_num)
theorem B7338053 : Blo 1526460 7338053 := bbase (se 4 (by rfl) ⟨687942, by rfl⟩ : syracuseStep 7338053 = 1375885) (by norm_num)
theorem B2291789 : Blo 1526460 2291789 := bbase (se 3 (by rfl) ⟨429710, by rfl⟩ : syracuseStep 2291789 = 859421) (by norm_num)
theorem B1718365 : Blo 1526460 1718365 := bbase (se 3 (by rfl) ⟨322193, by rfl⟩ : syracuseStep 1718365 = 644387) (by norm_num)
theorem B2291813 : Blo 1526460 2291813 := bbase (se 4 (by rfl) ⟨214857, by rfl⟩ : syracuseStep 2291813 = 429715) (by norm_num)
theorem B3438701 : Blo 1526460 3438701 := bbase (se 3 (by rfl) ⟨644756, by rfl⟩ : syracuseStep 3438701 = 1289513) (by norm_num)
theorem B2291837 : Blo 1526460 2291837 := bbase (se 3 (by rfl) ⟨429719, by rfl⟩ : syracuseStep 2291837 = 859439) (by norm_num)
theorem B1718401 : Blo 1526460 1718401 := bbase (se 2 (by rfl) ⟨644400, by rfl⟩ : syracuseStep 1718401 = 1288801) (by norm_num)
theorem B2291861 : Blo 1526460 2291861 := bbase (se 6 (by rfl) ⟨53715, by rfl⟩ : syracuseStep 2291861 = 107431) (by norm_num)
theorem B11606165 : Blo 1526460 11606165 := bbase (se 6 (by rfl) ⟨272019, by rfl⟩ : syracuseStep 11606165 = 544039) (by norm_num)
theorem B1718437 : Blo 1526460 1718437 := bbase (se 4 (by rfl) ⟨161103, by rfl⟩ : syracuseStep 1718437 = 322207) (by norm_num)
theorem B2291885 : Blo 1526460 2291885 := bbase (se 3 (by rfl) ⟨429728, by rfl⟩ : syracuseStep 2291885 = 859457) (by norm_num)
theorem B2119861 : Blo 1526460 2119861 := bbase (se 5 (by rfl) ⟨99368, by rfl⟩ : syracuseStep 2119861 = 198737) (by norm_num)
theorem B3438773 : Blo 1526460 3438773 := bbase (se 5 (by rfl) ⟨161192, by rfl⟩ : syracuseStep 3438773 = 322385) (by norm_num)
theorem B2898109 : Blo 1526460 2898109 := bbase (se 3 (by rfl) ⟨543395, by rfl⟩ : syracuseStep 2898109 = 1086791) (by norm_num)
theorem B2578621 : Blo 1526460 2578621 := bbase (se 3 (by rfl) ⟨483491, by rfl⟩ : syracuseStep 2578621 = 966983) (by norm_num)
theorem B3864773 : Blo 1526460 3864773 := bbase (se 4 (by rfl) ⟨362322, by rfl⟩ : syracuseStep 3864773 = 724645) (by norm_num)
theorem B2291909 : Blo 1526460 2291909 := bbase (se 4 (by rfl) ⟨214866, by rfl⟩ : syracuseStep 2291909 = 429733) (by norm_num)
theorem B1718473 : Blo 1526460 1718473 := bbase (se 2 (by rfl) ⟨644427, by rfl⟩ : syracuseStep 1718473 = 1288855) (by norm_num)
theorem B5798101 : Blo 1526460 5798101 := bbase (se 7 (by rfl) ⟨67946, by rfl⟩ : syracuseStep 5798101 = 135893) (by norm_num)
theorem B2291933 : Blo 1526460 2291933 := bbase (se 3 (by rfl) ⟨429737, by rfl⟩ : syracuseStep 2291933 = 859475) (by norm_num)
theorem B1718509 : Blo 1526460 1718509 := bbase (se 3 (by rfl) ⟨322220, by rfl⟩ : syracuseStep 1718509 = 644441) (by norm_num)
theorem B2291957 : Blo 1526460 2291957 := bbase (se 5 (by rfl) ⟨107435, by rfl⟩ : syracuseStep 2291957 = 214871) (by norm_num)
theorem B3438845 : Blo 1526460 3438845 := bbase (se 3 (by rfl) ⟨644783, by rfl⟩ : syracuseStep 3438845 = 1289567) (by norm_num)
theorem B2291981 : Blo 1526460 2291981 := bbase (se 3 (by rfl) ⟨429746, by rfl⟩ : syracuseStep 2291981 = 859493) (by norm_num)
theorem B1718545 : Blo 1526460 1718545 := bbase (se 2 (by rfl) ⟨644454, by rfl⟩ : syracuseStep 1718545 = 1288909) (by norm_num)
theorem B13220117 : Blo 1526460 13220117 := bbase (se 6 (by rfl) ⟨309846, by rfl⟩ : syracuseStep 13220117 = 619693) (by norm_num)
theorem B2578709 : Blo 1526460 2578709 := bbase (se 6 (by rfl) ⟨60438, by rfl⟩ : syracuseStep 2578709 = 120877) (by norm_num)
theorem B2292005 : Blo 1526460 2292005 := bbase (se 4 (by rfl) ⟨214875, by rfl⟩ : syracuseStep 2292005 = 429751) (by norm_num)
theorem B1718581 : Blo 1526460 1718581 := bbase (se 5 (by rfl) ⟨80558, by rfl⟩ : syracuseStep 1718581 = 161117) (by norm_num)
theorem B2292029 : Blo 1526460 2292029 := bbase (se 3 (by rfl) ⟨429755, by rfl⟩ : syracuseStep 2292029 = 859511) (by norm_num)
theorem B3438917 : Blo 1526460 3438917 := bbase (se 4 (by rfl) ⟨322398, by rfl⟩ : syracuseStep 3438917 = 644797) (by norm_num)
theorem B2292053 : Blo 1526460 2292053 := bbase (se 10 (by rfl) ⟨3357, by rfl⟩ : syracuseStep 2292053 = 6715) (by norm_num)
theorem B1718617 : Blo 1526460 1718617 := bbase (se 2 (by rfl) ⟨644481, by rfl⟩ : syracuseStep 1718617 = 1288963) (by norm_num)
theorem B2292077 : Blo 1526460 2292077 := bbase (se 3 (by rfl) ⟨429764, by rfl⟩ : syracuseStep 2292077 = 859529) (by norm_num)
theorem B1718653 : Blo 1526460 1718653 := bbase (se 3 (by rfl) ⟨322247, by rfl⟩ : syracuseStep 1718653 = 644495) (by norm_num)
theorem B2447741 : Blo 1526460 2447741 := bbase (se 3 (by rfl) ⟨458951, by rfl⟩ : syracuseStep 2447741 = 917903) (by norm_num)
theorem B2292101 : Blo 1526460 2292101 := bbase (se 4 (by rfl) ⟨214884, by rfl⟩ : syracuseStep 2292101 = 429769) (by norm_num)
theorem B3438989 : Blo 1526460 3438989 := bbase (se 3 (by rfl) ⟨644810, by rfl⟩ : syracuseStep 3438989 = 1289621) (by norm_num)
theorem B2578837 : Blo 1526460 2578837 := bbase (se 6 (by rfl) ⟨60441, by rfl⟩ : syracuseStep 2578837 = 120883) (by norm_num)
theorem B2292125 : Blo 1526460 2292125 := bbase (se 3 (by rfl) ⟨429773, by rfl⟩ : syracuseStep 2292125 = 859547) (by norm_num)
theorem B1718689 : Blo 1526460 1718689 := bbase (se 2 (by rfl) ⟨644508, by rfl⟩ : syracuseStep 1718689 = 1289017) (by norm_num)
theorem B2292149 : Blo 1526460 2292149 := bbase (se 5 (by rfl) ⟨107444, by rfl⟩ : syracuseStep 2292149 = 214889) (by norm_num)
theorem B1718725 : Blo 1526460 1718725 := bbase (se 4 (by rfl) ⟨161130, by rfl⟩ : syracuseStep 1718725 = 322261) (by norm_num)
theorem B2292173 : Blo 1526460 2292173 := bbase (se 3 (by rfl) ⟨429782, by rfl⟩ : syracuseStep 2292173 = 859565) (by norm_num)
theorem B2292197 : Blo 1526460 2292197 := bbase (se 4 (by rfl) ⟨214893, by rfl⟩ : syracuseStep 2292197 = 429787) (by norm_num)
theorem B1718761 : Blo 1526460 1718761 := bbase (se 2 (by rfl) ⟨644535, by rfl⟩ : syracuseStep 1718761 = 1289071) (by norm_num)
theorem B2898413 : Blo 1526460 2898413 := bbase (se 3 (by rfl) ⟨543452, by rfl⟩ : syracuseStep 2898413 = 1086905) (by norm_num)
theorem B2578925 : Blo 1526460 2578925 := bbase (se 3 (by rfl) ⟨483548, by rfl⟩ : syracuseStep 2578925 = 967097) (by norm_num)
theorem B2292221 : Blo 1526460 2292221 := bbase (se 3 (by rfl) ⟨429791, by rfl⟩ : syracuseStep 2292221 = 859583) (by norm_num)
theorem B5798405 : Blo 1526460 5798405 := bbase (se 4 (by rfl) ⟨543600, by rfl⟩ : syracuseStep 5798405 = 1087201) (by norm_num)
theorem B1718797 : Blo 1526460 1718797 := bbase (se 3 (by rfl) ⟨322274, by rfl⟩ : syracuseStep 1718797 = 644549) (by norm_num)
theorem B2292245 : Blo 1526460 2292245 := bbase (se 6 (by rfl) ⟨53724, by rfl⟩ : syracuseStep 2292245 = 107449) (by norm_num)
theorem B3865117 : Blo 1526460 3865117 := bbase (se 3 (by rfl) ⟨724709, by rfl⟩ : syracuseStep 3865117 = 1449419) (by norm_num)
theorem B2292269 : Blo 1526460 2292269 := bbase (se 3 (by rfl) ⟨429800, by rfl⟩ : syracuseStep 2292269 = 859601) (by norm_num)
theorem B1718833 : Blo 1526460 1718833 := bbase (se 2 (by rfl) ⟨644562, by rfl⟩ : syracuseStep 1718833 = 1289125) (by norm_num)
theorem B11598389 : Blo 1526460 11598389 := bbase (se 5 (by rfl) ⟨543674, by rfl⟩ : syracuseStep 11598389 = 1087349) (by norm_num)
theorem B2292293 : Blo 1526460 2292293 := bbase (se 4 (by rfl) ⟨214902, by rfl⟩ : syracuseStep 2292293 = 429805) (by norm_num)
theorem B1718869 : Blo 1526460 1718869 := bbase (se 8 (by rfl) ⟨10071, by rfl⟩ : syracuseStep 1718869 = 20143) (by norm_num)
theorem B2292317 : Blo 1526460 2292317 := bbase (se 3 (by rfl) ⟨429809, by rfl⟩ : syracuseStep 2292317 = 859619) (by norm_num)
theorem B2579053 : Blo 1526460 2579053 := bbase (se 3 (by rfl) ⟨483572, by rfl⟩ : syracuseStep 2579053 = 967145) (by norm_num)
theorem B2292341 : Blo 1526460 2292341 := bbase (se 5 (by rfl) ⟨107453, by rfl⟩ : syracuseStep 2292341 = 214907) (by norm_num)
theorem B1718905 : Blo 1526460 1718905 := bbase (se 2 (by rfl) ⟨644589, by rfl⟩ : syracuseStep 1718905 = 1289179) (by norm_num)
theorem B3865229 : Blo 1526460 3865229 := bbase (se 3 (by rfl) ⟨724730, by rfl⟩ : syracuseStep 3865229 = 1449461) (by norm_num)
theorem B2292365 : Blo 1526460 2292365 := bbase (se 3 (by rfl) ⟨429818, by rfl⟩ : syracuseStep 2292365 = 859637) (by norm_num)
theorem B1718941 : Blo 1526460 1718941 := bbase (se 3 (by rfl) ⟨322301, by rfl⟩ : syracuseStep 1718941 = 644603) (by norm_num)
theorem B1931941 : Blo 1526460 1931941 := bbase (se 4 (by rfl) ⟨181119, by rfl⟩ : syracuseStep 1931941 = 362239) (by norm_num)
theorem B2292389 : Blo 1526460 2292389 := bbase (se 4 (by rfl) ⟨214911, by rfl⟩ : syracuseStep 2292389 = 429823) (by norm_num)
theorem B2292413 : Blo 1526460 2292413 := bbase (se 3 (by rfl) ⟨429827, by rfl⟩ : syracuseStep 2292413 = 859655) (by norm_num)
theorem B1718977 : Blo 1526460 1718977 := bbase (se 2 (by rfl) ⟨644616, by rfl⟩ : syracuseStep 1718977 = 1289233) (by norm_num)
theorem B2579141 : Blo 1526460 2579141 := bbase (se 4 (by rfl) ⟨241794, by rfl⟩ : syracuseStep 2579141 = 483589) (by norm_num)
theorem B2292437 : Blo 1526460 2292437 := bbase (se 7 (by rfl) ⟨26864, by rfl⟩ : syracuseStep 2292437 = 53729) (by norm_num)
theorem B1719013 : Blo 1526460 1719013 := bbase (se 4 (by rfl) ⟨161157, by rfl⟩ : syracuseStep 1719013 = 322315) (by norm_num)
theorem B2292461 : Blo 1526460 2292461 := bbase (se 3 (by rfl) ⟨429836, by rfl⟩ : syracuseStep 2292461 = 859673) (by norm_num)
theorem B2448125 : Blo 1526460 2448125 := bbase (se 3 (by rfl) ⟨459023, by rfl⟩ : syracuseStep 2448125 = 918047) (by norm_num)
theorem B2292485 : Blo 1526460 2292485 := bbase (se 4 (by rfl) ⟨214920, by rfl⟩ : syracuseStep 2292485 = 429841) (by norm_num)
theorem B1719049 : Blo 1526460 1719049 := bbase (se 2 (by rfl) ⟨644643, by rfl⟩ : syracuseStep 1719049 = 1289287) (by norm_num)
theorem B2292509 : Blo 1526460 2292509 := bbase (se 3 (by rfl) ⟨429845, by rfl⟩ : syracuseStep 2292509 = 859691) (by norm_num)
theorem B1719085 : Blo 1526460 1719085 := bbase (se 3 (by rfl) ⟨322328, by rfl⟩ : syracuseStep 1719085 = 644657) (by norm_num)
theorem B2292533 : Blo 1526460 2292533 := bbase (se 5 (by rfl) ⟨107462, by rfl⟩ : syracuseStep 2292533 = 214925) (by norm_num)
theorem B2579269 : Blo 1526460 2579269 := bbase (se 4 (by rfl) ⟨241806, by rfl⟩ : syracuseStep 2579269 = 483613) (by norm_num)
theorem B3865421 : Blo 1526460 3865421 := bbase (se 3 (by rfl) ⟨724766, by rfl⟩ : syracuseStep 3865421 = 1449533) (by norm_num)
theorem B2292557 : Blo 1526460 2292557 := bbase (se 3 (by rfl) ⟨429854, by rfl⟩ : syracuseStep 2292557 = 859709) (by norm_num)
theorem B1932113 : Blo 1526460 1932113 := bbase (se 2 (by rfl) ⟨724542, by rfl⟩ : syracuseStep 1932113 = 1449085) (by norm_num)
theorem B1719121 : Blo 1526460 1719121 := bbase (se 2 (by rfl) ⟨644670, by rfl⟩ : syracuseStep 1719121 = 1289341) (by norm_num)
theorem B74316629 : Blo 1526460 74316629 := bbase (se 9 (by rfl) ⟨217724, by rfl⟩ : syracuseStep 74316629 = 435449) (by norm_num)
theorem B2292581 : Blo 1526460 2292581 := bbase (se 4 (by rfl) ⟨214929, by rfl⟩ : syracuseStep 2292581 = 429859) (by norm_num)
theorem B1833845 : Blo 1526460 1833845 := bbase (se 5 (by rfl) ⟨85961, by rfl⟩ : syracuseStep 1833845 = 171923) (by norm_num)
theorem B1719157 : Blo 1526460 1719157 := bbase (se 5 (by rfl) ⟨80585, by rfl⟩ : syracuseStep 1719157 = 161171) (by norm_num)
theorem B2292605 : Blo 1526460 2292605 := bbase (se 3 (by rfl) ⟨429863, by rfl⟩ : syracuseStep 2292605 = 859727) (by norm_num)
theorem B2448253 : Blo 1526460 2448253 := bbase (se 3 (by rfl) ⟨459047, by rfl⟩ : syracuseStep 2448253 = 918095) (by norm_num)
theorem B1932169 : Blo 1526460 1932169 := bbase (se 2 (by rfl) ⟨724563, by rfl⟩ : syracuseStep 1932169 = 1449127) (by norm_num)
theorem B2292629 : Blo 1526460 2292629 := bbase (se 6 (by rfl) ⟨53733, by rfl⟩ : syracuseStep 2292629 = 107467) (by norm_num)
theorem B1719193 : Blo 1526460 1719193 := bbase (se 2 (by rfl) ⟨644697, by rfl⟩ : syracuseStep 1719193 = 1289395) (by norm_num)
theorem B2292653 : Blo 1526460 2292653 := bbase (se 3 (by rfl) ⟨429872, by rfl⟩ : syracuseStep 2292653 = 859745) (by norm_num)
theorem B1719229 : Blo 1526460 1719229 := bbase (se 3 (by rfl) ⟨322355, by rfl⟩ : syracuseStep 1719229 = 644711) (by norm_num)
theorem B2292677 : Blo 1526460 2292677 := bbase (se 4 (by rfl) ⟨214938, by rfl⟩ : syracuseStep 2292677 = 429877) (by norm_num)
theorem B1833941 : Blo 1526460 1833941 := bbase (se 7 (by rfl) ⟨21491, by rfl⟩ : syracuseStep 1833941 = 42983) (by norm_num)
theorem B1719265 : Blo 1526460 1719265 := bbase (se 2 (by rfl) ⟨644724, by rfl⟩ : syracuseStep 1719265 = 1289449) (by norm_num)
theorem B1932265 : Blo 1526460 1932265 := bbase (se 2 (by rfl) ⟨724599, by rfl⟩ : syracuseStep 1932265 = 1449199) (by norm_num)
theorem B1719301 : Blo 1526460 1719301 := bbase (se 4 (by rfl) ⟨161184, by rfl⟩ : syracuseStep 1719301 = 322369) (by norm_num)
theorem B2751517 : Blo 1526460 2751517 := bbase (se 3 (by rfl) ⟨515909, by rfl⟩ : syracuseStep 2751517 = 1031819) (by norm_num)
theorem B3308581 : Blo 1526460 3308581 := bbase (se 4 (by rfl) ⟨310179, by rfl⟩ : syracuseStep 3308581 = 620359) (by norm_num)
theorem B1719337 : Blo 1526460 1719337 := bbase (se 2 (by rfl) ⟨644751, by rfl⟩ : syracuseStep 1719337 = 1289503) (by norm_num)
theorem B1719373 : Blo 1526460 1719373 := bbase (se 3 (by rfl) ⟨322382, by rfl⟩ : syracuseStep 1719373 = 644765) (by norm_num)
theorem B17407061 : Blo 1526460 17407061 := bbase (se 8 (by rfl) ⟨101994, by rfl⟩ : syracuseStep 17407061 = 203989) (by norm_num)
theorem B3095653 : Blo 1526460 3095653 := bbase (se 4 (by rfl) ⟨290217, by rfl⟩ : syracuseStep 3095653 = 580435) (by norm_num)
theorem B1719409 : Blo 1526460 1719409 := bbase (se 2 (by rfl) ⟨644778, by rfl⟩ : syracuseStep 1719409 = 1289557) (by norm_num)
theorem B4127861 : Blo 1526460 4127861 := bbase (se 5 (by rfl) ⟨193493, by rfl⟩ : syracuseStep 4127861 = 386987) (by norm_num)
theorem B7158901 : Blo 1526460 7158901 := bbase (se 5 (by rfl) ⟨335573, by rfl⟩ : syracuseStep 7158901 = 671147) (by norm_num)
theorem B1834105 : Blo 1526460 1834105 := bbase (se 2 (by rfl) ⟨687789, by rfl⟩ : syracuseStep 1834105 = 1375579) (by norm_num)
theorem B19561621 : Blo 1526460 19561621 := bbase (se 6 (by rfl) ⟨458475, by rfl⟩ : syracuseStep 19561621 = 916951) (by norm_num)
theorem B1932437 : Blo 1526460 1932437 := bbase (se 6 (by rfl) ⟨45291, by rfl⟩ : syracuseStep 1932437 = 90583) (by norm_num)
theorem B1719445 : Blo 1526460 1719445 := bbase (se 6 (by rfl) ⟨40299, by rfl⟩ : syracuseStep 1719445 = 80599) (by norm_num)
theorem B1547429 : Blo 1526460 1547429 := bbase (se 4 (by rfl) ⟨145071, by rfl⟩ : syracuseStep 1547429 = 290143) (by norm_num)
theorem B3865765 : Blo 1526460 3865765 := bbase (se 4 (by rfl) ⟨362415, by rfl⟩ : syracuseStep 3865765 = 724831) (by norm_num)
theorem B2751661 : Blo 1526460 2751661 := bbase (se 3 (by rfl) ⟨515936, by rfl⟩ : syracuseStep 2751661 = 1031873) (by norm_num)
theorem B5881013 : Blo 1526460 5881013 := bbase (se 5 (by rfl) ⟨275672, by rfl⟩ : syracuseStep 5881013 = 551345) (by norm_num)
theorem B1719481 : Blo 1526460 1719481 := bbase (se 2 (by rfl) ⟨644805, by rfl⟩ : syracuseStep 1719481 = 1289611) (by norm_num)
theorem B1547461 : Blo 1526460 1547461 := bbase (se 4 (by rfl) ⟨145074, by rfl⟩ : syracuseStep 1547461 = 290149) (by norm_num)
theorem B7732421 : Blo 1526460 7732421 := bbase (se 4 (by rfl) ⟨724914, by rfl⟩ : syracuseStep 7732421 = 1449829) (by norm_num)
theorem B1932493 : Blo 1526460 1932493 := bbase (se 3 (by rfl) ⟨362342, by rfl⟩ : syracuseStep 1932493 = 724685) (by norm_num)
theorem B2899165 : Blo 1526460 2899165 := bbase (se 3 (by rfl) ⟨543593, by rfl⟩ : syracuseStep 2899165 = 1087187) (by norm_num)
theorem B1719517 : Blo 1526460 1719517 := bbase (se 3 (by rfl) ⟨322409, by rfl⟩ : syracuseStep 1719517 = 644819) (by norm_num)
theorem B3865877 : Blo 1526460 3865877 := bbase (se 6 (by rfl) ⟨90606, by rfl⟩ : syracuseStep 3865877 = 181213) (by norm_num)
theorem B1932589 : Blo 1526460 1932589 := bbase (se 3 (by rfl) ⟨362360, by rfl⟩ : syracuseStep 1932589 = 724721) (by norm_num)
theorem B1834321 : Blo 1526460 1834321 := bbase (se 2 (by rfl) ⟨687870, by rfl⟩ : syracuseStep 1834321 = 1375741) (by norm_num)
theorem B5152085 : Blo 1526460 5152085 := bbase (se 11 (by rfl) ⟨3773, by rfl⟩ : syracuseStep 5152085 = 7547) (by norm_num)
theorem B2899309 : Blo 1526460 2899309 := bbase (se 3 (by rfl) ⟨543620, by rfl⟩ : syracuseStep 2899309 = 1087241) (by norm_num)
theorem B3866069 : Blo 1526460 3866069 := bbase (se 7 (by rfl) ⟨45305, by rfl⟩ : syracuseStep 3866069 = 90611) (by norm_num)
theorem B1932761 : Blo 1526460 1932761 := bbase (se 2 (by rfl) ⟨724785, by rfl⟩ : syracuseStep 1932761 = 1449571) (by norm_num)
theorem B1834489 : Blo 1526460 1834489 := bbase (se 2 (by rfl) ⟨687933, by rfl⟩ : syracuseStep 1834489 = 1375867) (by norm_num)
theorem B2899469 : Blo 1526460 2899469 := bbase (se 3 (by rfl) ⟨543650, by rfl⟩ : syracuseStep 2899469 = 1087301) (by norm_num)
theorem B1932817 : Blo 1526460 1932817 := bbase (se 2 (by rfl) ⟨724806, by rfl⟩ : syracuseStep 1932817 = 1449613) (by norm_num)
theorem B2612765 : Blo 1526460 2612765 := bbase (se 3 (by rfl) ⟨489893, by rfl⟩ : syracuseStep 2612765 = 979787) (by norm_num)
theorem B4349477 : Blo 1526460 4349477 := bbase (se 4 (by rfl) ⟨407763, by rfl⟩ : syracuseStep 4349477 = 815527) (by norm_num)
theorem B3137069 : Blo 1526460 3137069 := bbase (se 3 (by rfl) ⟨588200, by rfl⟩ : syracuseStep 3137069 = 1176401) (by norm_num)
theorem B1932913 : Blo 1526460 1932913 := bbase (se 2 (by rfl) ⟨724842, by rfl⟩ : syracuseStep 1932913 = 1449685) (by norm_num)
theorem B2899613 : Blo 1526460 2899613 := bbase (se 3 (by rfl) ⟨543677, by rfl⟩ : syracuseStep 2899613 = 1087355) (by norm_num)
theorem B2752237 : Blo 1526460 2752237 := bbase (se 3 (by rfl) ⟨516044, by rfl⟩ : syracuseStep 2752237 = 1032089) (by norm_num)
theorem B5152517 : Blo 1526460 5152517 := bbase (se 4 (by rfl) ⟨483048, by rfl⟩ : syracuseStep 5152517 = 966097) (by norm_num)
theorem B1933085 : Blo 1526460 1933085 := bbase (se 3 (by rfl) ⟨362453, by rfl⟩ : syracuseStep 1933085 = 724907) (by norm_num)
theorem B3096365 : Blo 1526460 3096365 := bbase (se 3 (by rfl) ⟨580568, by rfl⟩ : syracuseStep 3096365 = 1161137) (by norm_num)
theorem B3866413 : Blo 1526460 3866413 := bbase (se 3 (by rfl) ⟨724952, by rfl⟩ : syracuseStep 3866413 = 1449905) (by norm_num)
theorem B6963029 : Blo 1526460 6963029 := bbase (se 9 (by rfl) ⟨20399, by rfl⟩ : syracuseStep 6963029 = 40799) (by norm_num)
theorem B1933141 : Blo 1526460 1933141 := bbase (se 9 (by rfl) ⟨5663, by rfl⟩ : syracuseStep 1933141 = 11327) (by norm_num)
theorem B3866525 : Blo 1526460 3866525 := bbase (se 3 (by rfl) ⟨724973, by rfl⟩ : syracuseStep 3866525 = 1449947) (by norm_num)
theorem B3530677 : Blo 1526460 3530677 := bbase (se 5 (by rfl) ⟨165500, by rfl⟩ : syracuseStep 3530677 = 331001) (by norm_num)
theorem B1933237 : Blo 1526460 1933237 := bbase (se 5 (by rfl) ⟨90620, by rfl⟩ : syracuseStep 1933237 = 181241) (by norm_num)
theorem B2899901 : Blo 1526460 2899901 := bbase (se 3 (by rfl) ⟨543731, by rfl⟩ : syracuseStep 2899901 = 1087463) (by norm_num)
theorem B44629973 : Blo 1526460 44629973 := bbase (se 7 (by rfl) ⟨523007, by rfl⟩ : syracuseStep 44629973 = 1046015) (by norm_num)
theorem B4644877 : Blo 1526460 4644877 := bstep (se 3 (by rfl) ⟨870914, by rfl⟩ : syracuseStep 4644877 = 1741829) B1741829
theorem B5881891 : Blo 1526460 5881891 := bstep (se 1 (by rfl) ⟨4411418, by rfl⟩ : syracuseStep 5881891 = 8822837) B8822837
theorem B42942577 : Blo 1526460 42942577 := bstep (se 2 (by rfl) ⟨16103466, by rfl⟩ : syracuseStep 42942577 = 32206933) B32206933
theorem B3866737 : Blo 1526460 3866737 := bstep (se 2 (by rfl) ⟨1450026, by rfl⟩ : syracuseStep 3866737 = 2900053) B2900053
theorem B2900099 : Blo 1526460 2900099 := bstep (se 1 (by rfl) ⟨2175074, by rfl⟩ : syracuseStep 2900099 = 4350149) B4350149
theorem B4350125 : Blo 1526460 4350125 := bstep (se 3 (by rfl) ⟨815648, by rfl⟩ : syracuseStep 4350125 = 1631297) B1631297
theorem B16736453 : Blo 1526460 16736453 := bstep (se 4 (by rfl) ⟨1569042, by rfl⟩ : syracuseStep 16736453 = 3138085) B3138085
theorem B6193379 : Blo 1526460 6193379 := bstep (se 1 (by rfl) ⟨4645034, by rfl⟩ : syracuseStep 6193379 = 9290069) B9290069
theorem B1933571 : Blo 1526460 1933571 := bstep (se 1 (by rfl) ⟨1450178, by rfl⟩ : syracuseStep 1933571 = 2900357) B2900357
theorem B9789731 : Blo 1526460 9789731 := bstep (se 1 (by rfl) ⟨7342298, by rfl⟩ : syracuseStep 9789731 = 14684597) B14684597
theorem B1835363 : Blo 1526460 1835363 := bstep (se 1 (by rfl) ⟨1376522, by rfl⟩ : syracuseStep 1835363 = 2753045) B2753045
theorem B3867011 : Blo 1526460 3867011 := bstep (se 1 (by rfl) ⟨2900258, by rfl⟩ : syracuseStep 3867011 = 5800517) B5800517
theorem B5153165 : Blo 1526460 5153165 := bstep (se 3 (by rfl) ⟨966218, by rfl⟩ : syracuseStep 5153165 = 1932437) B1932437
theorem B2900387 : Blo 1526460 2900387 := bstep (se 1 (by rfl) ⟨2175290, by rfl⟩ : syracuseStep 2900387 = 4350581) B4350581
theorem B5153219 : Blo 1526460 5153219 := bstep (se 1 (by rfl) ⟨3864914, by rfl⟩ : syracuseStep 5153219 = 7729829) B7729829
theorem B5227021 : Blo 1526460 5227021 := bstep (se 3 (by rfl) ⟨980066, by rfl⟩ : syracuseStep 5227021 = 1960133) B1960133
theorem B3867203 : Blo 1526460 3867203 := bstep (se 1 (by rfl) ⟨2900402, by rfl⟩ : syracuseStep 3867203 = 5800805) B5800805
theorem B5153489 : Blo 1526460 5153489 := bstep (se 2 (by rfl) ⟨1932558, by rfl⟩ : syracuseStep 5153489 = 3865117) B3865117
theorem B66069269 : Blo 1526460 66069269 := bstep (se 6 (by rfl) ⟨1548498, by rfl⟩ : syracuseStep 66069269 = 3096997) B3096997
theorem B9290531 : Blo 1526460 9290531 := bstep (se 1 (by rfl) ⟨6967898, by rfl⟩ : syracuseStep 9290531 = 13935797) B13935797
theorem B4645667 : Blo 1526460 4645667 := bstep (se 1 (by rfl) ⟨3484250, by rfl⟩ : syracuseStep 4645667 = 6968501) B6968501
theorem B1631075 : Blo 1526460 1631075 := bstep (se 1 (by rfl) ⟨1223306, by rfl⟩ : syracuseStep 1631075 = 2446613) B2446613
theorem B1934275 : Blo 1526460 1934275 := bstep (se 1 (by rfl) ⟨1450706, by rfl⟩ : syracuseStep 1934275 = 2901413) B2901413
theorem B11305925 : Blo 1526460 11305925 := bstep (se 4 (by rfl) ⟨1059930, by rfl⟩ : syracuseStep 11305925 = 2119861) B2119861
theorem B2753507 : Blo 1526460 2753507 := bstep (se 1 (by rfl) ⟨2065130, by rfl⟩ : syracuseStep 2753507 = 4130261) B4130261
theorem B1934371 : Blo 1526460 1934371 := bstep (se 1 (by rfl) ⟨1450778, by rfl⟩ : syracuseStep 1934371 = 2901557) B2901557
theorem B4351117 : Blo 1526460 4351117 := bstep (se 3 (by rfl) ⟨815834, by rfl⟩ : syracuseStep 4351117 = 1631669) B1631669
theorem B4129937 : Blo 1526460 4129937 := bstep (se 2 (by rfl) ⟨1548726, by rfl⟩ : syracuseStep 4129937 = 3097453) B3097453
theorem B2065601 : Blo 1526460 2065601 := bstep (se 2 (by rfl) ⟨774600, by rfl⟩ : syracuseStep 2065601 = 1549201) B1549201
theorem B5154029 : Blo 1526460 5154029 := bstep (se 3 (by rfl) ⟨966380, by rfl⟩ : syracuseStep 5154029 = 1932761) B1932761
theorem B5154083 : Blo 1526460 5154083 := bstep (se 1 (by rfl) ⟨3865562, by rfl⟩ : syracuseStep 5154083 = 7731125) B7731125
theorem B7062833 : Blo 1526460 7062833 := bstep (se 2 (by rfl) ⟨2648562, by rfl⟩ : syracuseStep 7062833 = 5297125) B5297125
theorem B8701253 : Blo 1526460 8701253 := bstep (se 4 (by rfl) ⟨815742, by rfl⟩ : syracuseStep 8701253 = 1631485) B1631485
theorem B2901329 : Blo 1526460 2901329 := bstep (se 2 (by rfl) ⟨1087998, by rfl⟩ : syracuseStep 2901329 = 2175997) B2175997
theorem B3261809 : Blo 1526460 3261809 := bstep (se 2 (by rfl) ⟨1223178, by rfl⟩ : syracuseStep 3261809 = 2446357) B2446357
theorem B4892035 : Blo 1526460 4892035 := bstep (se 1 (by rfl) ⟨3669026, by rfl⟩ : syracuseStep 4892035 = 7338053) B7338053
theorem B17401229 : Blo 1526460 17401229 := bstep (se 3 (by rfl) ⟨3262730, by rfl⟩ : syracuseStep 17401229 = 6525461) B6525461
theorem B8365517 : Blo 1526460 8365517 := bstep (se 3 (by rfl) ⟨1568534, by rfl⟩ : syracuseStep 8365517 = 3137069) B3137069
theorem B6522353 : Blo 1526460 6522353 := bstep (se 2 (by rfl) ⟨2445882, by rfl⟩ : syracuseStep 6522353 = 4891765) B4891765
theorem B9545201 : Blo 1526460 9545201 := bstep (se 2 (by rfl) ⟨3579450, by rfl⟩ : syracuseStep 9545201 = 7158901) B7158901
theorem B3868145 : Blo 1526460 3868145 := bstep (se 2 (by rfl) ⟨1450554, by rfl⟩ : syracuseStep 3868145 = 2901109) B2901109
theorem B13927949 : Blo 1526460 13927949 := bstep (se 3 (by rfl) ⟨2611490, by rfl⟩ : syracuseStep 13927949 = 5222981) B5222981
theorem B3868195 : Blo 1526460 3868195 := bstep (se 1 (by rfl) ⟨2901146, by rfl⟩ : syracuseStep 3868195 = 5802293) B5802293
theorem B5154353 : Blo 1526460 5154353 := bstep (se 2 (by rfl) ⟨1932882, by rfl⟩ : syracuseStep 5154353 = 3865765) B3865765
theorem B1631827 : Blo 1526460 1631827 := bstep (se 1 (by rfl) ⟨1223870, by rfl⟩ : syracuseStep 1631827 = 2447741) B2447741
theorem B6964849 : Blo 1526460 6964849 := bstep (se 2 (by rfl) ⟨2611818, by rfl⟩ : syracuseStep 6964849 = 5223637) B5223637
theorem B9791117 : Blo 1526460 9791117 := bstep (se 3 (by rfl) ⟨1835834, by rfl⟩ : syracuseStep 9791117 = 3671669) B3671669
theorem B3868337 : Blo 1526460 3868337 := bstep (se 2 (by rfl) ⟨1450626, by rfl⟩ : syracuseStep 3868337 = 2901253) B2901253
theorem B4130509 : Blo 1526460 4130509 := bstep (se 3 (by rfl) ⟨774470, by rfl⟩ : syracuseStep 4130509 = 1548941) B1548941
theorem B4646641 : Blo 1526460 4646641 := bstep (se 2 (by rfl) ⟨1742490, by rfl⟩ : syracuseStep 4646641 = 3484981) B3484981
theorem B4130605 : Blo 1526460 4130605 := bstep (se 3 (by rfl) ⟨774488, by rfl⟩ : syracuseStep 4130605 = 1548977) B1548977
theorem B5801777 : Blo 1526460 5801777 := bstep (se 2 (by rfl) ⟨2175666, by rfl⟩ : syracuseStep 5801777 = 4351333) B4351333
theorem B4646737 : Blo 1526460 4646737 := bstep (se 2 (by rfl) ⟨1742526, by rfl⟩ : syracuseStep 4646737 = 3485053) B3485053
theorem B1632083 : Blo 1526460 1632083 := bstep (se 1 (by rfl) ⟨1224062, by rfl⟩ : syracuseStep 1632083 = 2448125) B2448125
theorem B3098531 : Blo 1526460 3098531 := bstep (se 1 (by rfl) ⟨2323898, by rfl⟩ : syracuseStep 3098531 = 4647797) B4647797
theorem B8701937 : Blo 1526460 8701937 := bstep (se 2 (by rfl) ⟨3263226, by rfl⟩ : syracuseStep 8701937 = 6526453) B6526453
theorem B5154893 : Blo 1526460 5154893 := bstep (se 3 (by rfl) ⟨966542, by rfl⟩ : syracuseStep 5154893 = 1933085) B1933085
theorem B5507185 : Blo 1526460 5507185 := bstep (se 2 (by rfl) ⟨2065194, by rfl⟩ : syracuseStep 5507185 = 4130389) B4130389
theorem B5154947 : Blo 1526460 5154947 := bstep (se 1 (by rfl) ⟨3866210, by rfl⟩ : syracuseStep 5154947 = 7732421) B7732421
theorem B3434705 : Blo 1526460 3434705 := bstep (se 2 (by rfl) ⟨1288014, by rfl⟩ : syracuseStep 3434705 = 2576029) B2576029
theorem B3434723 : Blo 1526460 3434723 := bstep (se 1 (by rfl) ⟨2576042, by rfl⟩ : syracuseStep 3434723 = 5152085) B5152085
theorem B5155217 : Blo 1526460 5155217 := bstep (se 2 (by rfl) ⟨1933206, by rfl⟩ : syracuseStep 5155217 = 3866413) B3866413
theorem B3434993 : Blo 1526460 3434993 := bstep (se 2 (by rfl) ⟨1288122, by rfl⟩ : syracuseStep 3434993 = 2576245) B2576245
theorem B3435011 : Blo 1526460 3435011 := bstep (se 1 (by rfl) ⟨2576258, by rfl⟩ : syracuseStep 3435011 = 5152517) B5152517
theorem B9914993 : Blo 1526460 9914993 := bstep (se 2 (by rfl) ⟨3718122, by rfl⟩ : syracuseStep 9914993 = 7436245) B7436245
theorem B3263107 : Blo 1526460 3263107 := bstep (se 1 (by rfl) ⟨2447330, by rfl⟩ : syracuseStep 3263107 = 4894661) B4894661
theorem B16509581 : Blo 1526460 16509581 := bstep (se 3 (by rfl) ⟨3095546, by rfl⟩ : syracuseStep 16509581 = 6191093) B6191093
theorem B7735985 : Blo 1526460 7735985 := bstep (se 2 (by rfl) ⟨2900994, by rfl⟩ : syracuseStep 7735985 = 5801989) B5801989
theorem B1526467 : Blo 1526460 1526467 := bstep (se 1 (by rfl) ⟨1144850, by rfl⟩ : syracuseStep 1526467 = 2289701) B2289701
theorem B1526483 : Blo 1526460 1526483 := bstep (se 1 (by rfl) ⟨1144862, by rfl⟩ : syracuseStep 1526483 = 2289725) B2289725
theorem B1526499 : Blo 1526460 1526499 := bstep (se 1 (by rfl) ⟨1144874, by rfl⟩ : syracuseStep 1526499 = 2289749) B2289749
theorem B1526515 : Blo 1526460 1526515 := bstep (se 1 (by rfl) ⟨1144886, by rfl⟩ : syracuseStep 1526515 = 2289773) B2289773
theorem B1526531 : Blo 1526460 1526531 := bstep (se 1 (by rfl) ⟨1144898, by rfl⟩ : syracuseStep 1526531 = 2289797) B2289797
theorem B7727885 : Blo 1526460 7727885 := bstep (se 3 (by rfl) ⟨1448978, by rfl⟩ : syracuseStep 7727885 = 2897957) B2897957
theorem B3435281 : Blo 1526460 3435281 := bstep (se 2 (by rfl) ⟨1288230, by rfl⟩ : syracuseStep 3435281 = 2576461) B2576461
theorem B1526547 : Blo 1526460 1526547 := bstep (se 1 (by rfl) ⟨1144910, by rfl⟩ : syracuseStep 1526547 = 2289821) B2289821
theorem B1526563 : Blo 1526460 1526563 := bstep (se 1 (by rfl) ⟨1144922, by rfl⟩ : syracuseStep 1526563 = 2289845) B2289845
theorem B3435299 : Blo 1526460 3435299 := bstep (se 1 (by rfl) ⟨2576474, by rfl⟩ : syracuseStep 3435299 = 5152949) B5152949
theorem B1526579 : Blo 1526460 1526579 := bstep (se 1 (by rfl) ⟨1144934, by rfl⟩ : syracuseStep 1526579 = 2289869) B2289869
theorem B1526595 : Blo 1526460 1526595 := bstep (se 1 (by rfl) ⟨1144946, by rfl⟩ : syracuseStep 1526595 = 2289893) B2289893
theorem B1526611 : Blo 1526460 1526611 := bstep (se 1 (by rfl) ⟨1144958, by rfl⟩ : syracuseStep 1526611 = 2289917) B2289917
theorem B1526627 : Blo 1526460 1526627 := bstep (se 1 (by rfl) ⟨1144970, by rfl⟩ : syracuseStep 1526627 = 2289941) B2289941
theorem B1526643 : Blo 1526460 1526643 := bstep (se 1 (by rfl) ⟨1144982, by rfl⟩ : syracuseStep 1526643 = 2289965) B2289965
theorem B1526659 : Blo 1526460 1526659 := bstep (se 1 (by rfl) ⟨1144994, by rfl⟩ : syracuseStep 1526659 = 2289989) B2289989
theorem B1526675 : Blo 1526460 1526675 := bstep (se 1 (by rfl) ⟨1145006, by rfl⟩ : syracuseStep 1526675 = 2290013) B2290013
theorem B1526691 : Blo 1526460 1526691 := bstep (se 1 (by rfl) ⟨1145018, by rfl⟩ : syracuseStep 1526691 = 2290037) B2290037
theorem B5155757 : Blo 1526460 5155757 := bstep (se 3 (by rfl) ⟨966704, by rfl⟩ : syracuseStep 5155757 = 1933409) B1933409
theorem B2173873 : Blo 1526460 2173873 := bstep (se 2 (by rfl) ⟨815202, by rfl⟩ : syracuseStep 2173873 = 1630405) B1630405
theorem B1526707 : Blo 1526460 1526707 := bstep (se 1 (by rfl) ⟨1145030, by rfl⟩ : syracuseStep 1526707 = 2290061) B2290061
theorem B1526723 : Blo 1526460 1526723 := bstep (se 1 (by rfl) ⟨1145042, by rfl⟩ : syracuseStep 1526723 = 2290085) B2290085
theorem B4893635 : Blo 1526460 4893635 := bstep (se 1 (by rfl) ⟨3670226, by rfl⟩ : syracuseStep 4893635 = 7340453) B7340453
theorem B1526739 : Blo 1526460 1526739 := bstep (se 1 (by rfl) ⟨1145054, by rfl⟩ : syracuseStep 1526739 = 2290109) B2290109
theorem B1526755 : Blo 1526460 1526755 := bstep (se 1 (by rfl) ⟨1145066, by rfl⟩ : syracuseStep 1526755 = 2290133) B2290133
theorem B5155811 : Blo 1526460 5155811 := bstep (se 1 (by rfl) ⟨3866858, by rfl⟩ : syracuseStep 5155811 = 7733717) B7733717
theorem B1526771 : Blo 1526460 1526771 := bstep (se 1 (by rfl) ⟨1145078, by rfl⟩ : syracuseStep 1526771 = 2290157) B2290157
theorem B1526787 : Blo 1526460 1526787 := bstep (se 1 (by rfl) ⟨1145090, by rfl⟩ : syracuseStep 1526787 = 2290181) B2290181
theorem B2173969 : Blo 1526460 2173969 := bstep (se 2 (by rfl) ⟨815238, by rfl⟩ : syracuseStep 2173969 = 1630477) B1630477
theorem B1526803 : Blo 1526460 1526803 := bstep (se 1 (by rfl) ⟨1145102, by rfl⟩ : syracuseStep 1526803 = 2290205) B2290205
theorem B1526819 : Blo 1526460 1526819 := bstep (se 1 (by rfl) ⟨1145114, by rfl⟩ : syracuseStep 1526819 = 2290229) B2290229
theorem B3435569 : Blo 1526460 3435569 := bstep (se 2 (by rfl) ⟨1288338, by rfl⟩ : syracuseStep 3435569 = 2576677) B2576677
theorem B1526835 : Blo 1526460 1526835 := bstep (se 1 (by rfl) ⟨1145126, by rfl⟩ : syracuseStep 1526835 = 2290253) B2290253
theorem B1526851 : Blo 1526460 1526851 := bstep (se 1 (by rfl) ⟨1145138, by rfl⟩ : syracuseStep 1526851 = 2290277) B2290277
theorem B3435587 : Blo 1526460 3435587 := bstep (se 1 (by rfl) ⟨2576690, by rfl⟩ : syracuseStep 3435587 = 5153381) B5153381
theorem B1526867 : Blo 1526460 1526867 := bstep (se 1 (by rfl) ⟨1145150, by rfl⟩ : syracuseStep 1526867 = 2290301) B2290301
theorem B1526883 : Blo 1526460 1526883 := bstep (se 1 (by rfl) ⟨1145162, by rfl⟩ : syracuseStep 1526883 = 2290325) B2290325
theorem B7441507 : Blo 1526460 7441507 := bstep (se 1 (by rfl) ⟨5581130, by rfl⟩ : syracuseStep 7441507 = 11162261) B11162261
theorem B24775793 : Blo 1526460 24775793 := bstep (se 2 (by rfl) ⟨9290922, by rfl⟩ : syracuseStep 24775793 = 18581845) B18581845
theorem B1526899 : Blo 1526460 1526899 := bstep (se 1 (by rfl) ⟨1145174, by rfl⟩ : syracuseStep 1526899 = 2290349) B2290349
theorem B1526915 : Blo 1526460 1526915 := bstep (se 1 (by rfl) ⟨1145186, by rfl⟩ : syracuseStep 1526915 = 2290373) B2290373
theorem B1526931 : Blo 1526460 1526931 := bstep (se 1 (by rfl) ⟨1145198, by rfl⟩ : syracuseStep 1526931 = 2290397) B2290397
theorem B1526947 : Blo 1526460 1526947 := bstep (se 1 (by rfl) ⟨1145210, by rfl⟩ : syracuseStep 1526947 = 2290421) B2290421
theorem B1526963 : Blo 1526460 1526963 := bstep (se 1 (by rfl) ⟨1145222, by rfl⟩ : syracuseStep 1526963 = 2290445) B2290445
theorem B1526979 : Blo 1526460 1526979 := bstep (se 1 (by rfl) ⟨1145234, by rfl⟩ : syracuseStep 1526979 = 2290469) B2290469
theorem B1526995 : Blo 1526460 1526995 := bstep (se 1 (by rfl) ⟨1145246, by rfl⟩ : syracuseStep 1526995 = 2290493) B2290493
theorem B1527011 : Blo 1526460 1527011 := bstep (se 1 (by rfl) ⟨1145258, by rfl⟩ : syracuseStep 1527011 = 2290517) B2290517
theorem B5803235 : Blo 1526460 5803235 := bstep (se 1 (by rfl) ⟨4352426, by rfl⟩ : syracuseStep 5803235 = 8704853) B8704853
theorem B4467953 : Blo 1526460 4467953 := bstep (se 2 (by rfl) ⟨1675482, by rfl⟩ : syracuseStep 4467953 = 3350965) B3350965
theorem B5156081 : Blo 1526460 5156081 := bstep (se 2 (by rfl) ⟨1933530, by rfl⟩ : syracuseStep 5156081 = 3867061) B3867061
theorem B1527027 : Blo 1526460 1527027 := bstep (se 1 (by rfl) ⟨1145270, by rfl⟩ : syracuseStep 1527027 = 2290541) B2290541
theorem B2321665 : Blo 1526460 2321665 := bstep (se 2 (by rfl) ⟨870624, by rfl⟩ : syracuseStep 2321665 = 1741249) B1741249
theorem B1527043 : Blo 1526460 1527043 := bstep (se 1 (by rfl) ⟨1145282, by rfl⟩ : syracuseStep 1527043 = 2290565) B2290565
theorem B1527059 : Blo 1526460 1527059 := bstep (se 1 (by rfl) ⟨1145294, by rfl⟩ : syracuseStep 1527059 = 2290589) B2290589
theorem B1527075 : Blo 1526460 1527075 := bstep (se 1 (by rfl) ⟨1145306, by rfl⟩ : syracuseStep 1527075 = 2290613) B2290613
theorem B1527091 : Blo 1526460 1527091 := bstep (se 1 (by rfl) ⟨1145318, by rfl⟩ : syracuseStep 1527091 = 2290637) B2290637
theorem B1527107 : Blo 1526460 1527107 := bstep (se 1 (by rfl) ⟨1145330, by rfl⟩ : syracuseStep 1527107 = 2290661) B2290661
theorem B3435857 : Blo 1526460 3435857 := bstep (se 2 (by rfl) ⟨1288446, by rfl⟩ : syracuseStep 3435857 = 2576893) B2576893
theorem B1527123 : Blo 1526460 1527123 := bstep (se 1 (by rfl) ⟨1145342, by rfl⟩ : syracuseStep 1527123 = 2290685) B2290685
theorem B3435875 : Blo 1526460 3435875 := bstep (se 1 (by rfl) ⟨2576906, by rfl⟩ : syracuseStep 3435875 = 5153813) B5153813
theorem B1527139 : Blo 1526460 1527139 := bstep (se 1 (by rfl) ⟨1145354, by rfl⟩ : syracuseStep 1527139 = 2290709) B2290709
theorem B1527155 : Blo 1526460 1527155 := bstep (se 1 (by rfl) ⟨1145366, by rfl⟩ : syracuseStep 1527155 = 2290733) B2290733
theorem B1527171 : Blo 1526460 1527171 := bstep (se 1 (by rfl) ⟨1145378, by rfl⟩ : syracuseStep 1527171 = 2290757) B2290757
theorem B1527187 : Blo 1526460 1527187 := bstep (se 1 (by rfl) ⟨1145390, by rfl⟩ : syracuseStep 1527187 = 2290781) B2290781
theorem B1527203 : Blo 1526460 1527203 := bstep (se 1 (by rfl) ⟨1145402, by rfl⟩ : syracuseStep 1527203 = 2290805) B2290805
theorem B8703395 : Blo 1526460 8703395 := bstep (se 1 (by rfl) ⟨6527546, by rfl⟩ : syracuseStep 8703395 = 13055093) B13055093
theorem B1527219 : Blo 1526460 1527219 := bstep (se 1 (by rfl) ⟨1145414, by rfl⟩ : syracuseStep 1527219 = 2290829) B2290829
theorem B1527235 : Blo 1526460 1527235 := bstep (se 1 (by rfl) ⟨1145426, by rfl⟩ : syracuseStep 1527235 = 2290853) B2290853
theorem B1527251 : Blo 1526460 1527251 := bstep (se 1 (by rfl) ⟨1145438, by rfl⟩ : syracuseStep 1527251 = 2290877) B2290877
theorem B1527267 : Blo 1526460 1527267 := bstep (se 1 (by rfl) ⟨1145450, by rfl⟩ : syracuseStep 1527267 = 2290901) B2290901
theorem B31370723 : Blo 1526460 31370723 := bstep (se 1 (by rfl) ⟨23528042, by rfl⟩ : syracuseStep 31370723 = 47056085) B47056085
theorem B1527283 : Blo 1526460 1527283 := bstep (se 1 (by rfl) ⟨1145462, by rfl⟩ : syracuseStep 1527283 = 2290925) B2290925
theorem B2174465 : Blo 1526460 2174465 := bstep (se 2 (by rfl) ⟨815424, by rfl⟩ : syracuseStep 2174465 = 1630849) B1630849
theorem B1527299 : Blo 1526460 1527299 := bstep (se 1 (by rfl) ⟨1145474, by rfl⟩ : syracuseStep 1527299 = 2290949) B2290949
theorem B1527315 : Blo 1526460 1527315 := bstep (se 1 (by rfl) ⟨1145486, by rfl⟩ : syracuseStep 1527315 = 2290973) B2290973
theorem B1527331 : Blo 1526460 1527331 := bstep (se 1 (by rfl) ⟨1145498, by rfl⟩ : syracuseStep 1527331 = 2290997) B2290997
theorem B2575921 : Blo 1526460 2575921 := bstep (se 2 (by rfl) ⟨965970, by rfl⟩ : syracuseStep 2575921 = 1931941) B1931941
theorem B2788913 : Blo 1526460 2788913 := bstep (se 2 (by rfl) ⟨1045842, by rfl⟩ : syracuseStep 2788913 = 2091685) B2091685
theorem B1527347 : Blo 1526460 1527347 := bstep (se 1 (by rfl) ⟨1145510, by rfl⟩ : syracuseStep 1527347 = 2291021) B2291021
theorem B1527363 : Blo 1526460 1527363 := bstep (se 1 (by rfl) ⟨1145522, by rfl⟩ : syracuseStep 1527363 = 2291045) B2291045
theorem B2575955 : Blo 1526460 2575955 := bstep (se 1 (by rfl) ⟨1931966, by rfl⟩ : syracuseStep 2575955 = 3863933) B3863933
theorem B1527379 : Blo 1526460 1527379 := bstep (se 1 (by rfl) ⟨1145534, by rfl⟩ : syracuseStep 1527379 = 2291069) B2291069
theorem B1527395 : Blo 1526460 1527395 := bstep (se 1 (by rfl) ⟨1145546, by rfl⟩ : syracuseStep 1527395 = 2291093) B2291093
theorem B3436145 : Blo 1526460 3436145 := bstep (se 2 (by rfl) ⟨1288554, by rfl⟩ : syracuseStep 3436145 = 2577109) B2577109
theorem B1527411 : Blo 1526460 1527411 := bstep (se 1 (by rfl) ⟨1145558, by rfl⟩ : syracuseStep 1527411 = 2291117) B2291117
theorem B3436163 : Blo 1526460 3436163 := bstep (se 1 (by rfl) ⟨2577122, by rfl⟩ : syracuseStep 3436163 = 5154245) B5154245
theorem B1527427 : Blo 1526460 1527427 := bstep (se 1 (by rfl) ⟨1145570, by rfl⟩ : syracuseStep 1527427 = 2291141) B2291141
theorem B1527443 : Blo 1526460 1527443 := bstep (se 1 (by rfl) ⟨1145582, by rfl⟩ : syracuseStep 1527443 = 2291165) B2291165
theorem B1527459 : Blo 1526460 1527459 := bstep (se 1 (by rfl) ⟨1145594, by rfl⟩ : syracuseStep 1527459 = 2291189) B2291189
theorem B1527475 : Blo 1526460 1527475 := bstep (se 1 (by rfl) ⟨1145606, by rfl⟩ : syracuseStep 1527475 = 2291213) B2291213
theorem B1527491 : Blo 1526460 1527491 := bstep (se 1 (by rfl) ⟨1145618, by rfl⟩ : syracuseStep 1527491 = 2291237) B2291237
theorem B17395397 : Blo 1526460 17395397 := bstep (se 4 (by rfl) ⟨1630818, by rfl⟩ : syracuseStep 17395397 = 3261637) B3261637
theorem B2576083 : Blo 1526460 2576083 := bstep (se 1 (by rfl) ⟨1932062, by rfl⟩ : syracuseStep 2576083 = 3864125) B3864125
theorem B1527507 : Blo 1526460 1527507 := bstep (se 1 (by rfl) ⟨1145630, by rfl⟩ : syracuseStep 1527507 = 2291261) B2291261
theorem B1527523 : Blo 1526460 1527523 := bstep (se 1 (by rfl) ⟨1145642, by rfl⟩ : syracuseStep 1527523 = 2291285) B2291285
theorem B1527539 : Blo 1526460 1527539 := bstep (se 1 (by rfl) ⟨1145654, by rfl⟩ : syracuseStep 1527539 = 2291309) B2291309
theorem B1527555 : Blo 1526460 1527555 := bstep (se 1 (by rfl) ⟨1145666, by rfl⟩ : syracuseStep 1527555 = 2291333) B2291333
theorem B5156621 : Blo 1526460 5156621 := bstep (se 3 (by rfl) ⟨966866, by rfl⟩ : syracuseStep 5156621 = 1933733) B1933733
theorem B1527571 : Blo 1526460 1527571 := bstep (se 1 (by rfl) ⟨1145678, by rfl⟩ : syracuseStep 1527571 = 2291357) B2291357
theorem B1527587 : Blo 1526460 1527587 := bstep (se 1 (by rfl) ⟨1145690, by rfl⟩ : syracuseStep 1527587 = 2291381) B2291381
theorem B1527603 : Blo 1526460 1527603 := bstep (se 1 (by rfl) ⟨1145702, by rfl⟩ : syracuseStep 1527603 = 2291405) B2291405
theorem B1527619 : Blo 1526460 1527619 := bstep (se 1 (by rfl) ⟨1145714, by rfl⟩ : syracuseStep 1527619 = 2291429) B2291429
theorem B5156675 : Blo 1526460 5156675 := bstep (se 1 (by rfl) ⟨3867506, by rfl⟩ : syracuseStep 5156675 = 7735013) B7735013
theorem B3264337 : Blo 1526460 3264337 := bstep (se 2 (by rfl) ⟨1224126, by rfl⟩ : syracuseStep 3264337 = 2448253) B2448253
theorem B1527635 : Blo 1526460 1527635 := bstep (se 1 (by rfl) ⟨1145726, by rfl⟩ : syracuseStep 1527635 = 2291453) B2291453
theorem B2576225 : Blo 1526460 2576225 := bstep (se 2 (by rfl) ⟨966084, by rfl⟩ : syracuseStep 2576225 = 1932169) B1932169
theorem B1527651 : Blo 1526460 1527651 := bstep (se 1 (by rfl) ⟨1145738, by rfl⟩ : syracuseStep 1527651 = 2291477) B2291477
theorem B1527667 : Blo 1526460 1527667 := bstep (se 1 (by rfl) ⟨1145750, by rfl⟩ : syracuseStep 1527667 = 2291501) B2291501
theorem B1527683 : Blo 1526460 1527683 := bstep (se 1 (by rfl) ⟨1145762, by rfl⟩ : syracuseStep 1527683 = 2291525) B2291525
theorem B4706189 : Blo 1526460 4706189 := bstep (se 3 (by rfl) ⟨882410, by rfl⟩ : syracuseStep 4706189 = 1764821) B1764821
theorem B6524813 : Blo 1526460 6524813 := bstep (se 3 (by rfl) ⟨1223402, by rfl⟩ : syracuseStep 6524813 = 2446805) B2446805
theorem B3436433 : Blo 1526460 3436433 := bstep (se 2 (by rfl) ⟨1288662, by rfl⟩ : syracuseStep 3436433 = 2577325) B2577325
theorem B4894609 : Blo 1526460 4894609 := bstep (se 2 (by rfl) ⟨1835478, by rfl⟩ : syracuseStep 4894609 = 3670957) B3670957
theorem B1527699 : Blo 1526460 1527699 := bstep (se 1 (by rfl) ⟨1145774, by rfl⟩ : syracuseStep 1527699 = 2291549) B2291549
theorem B3436451 : Blo 1526460 3436451 := bstep (se 1 (by rfl) ⟨2577338, by rfl⟩ : syracuseStep 3436451 = 5154677) B5154677
theorem B1527715 : Blo 1526460 1527715 := bstep (se 1 (by rfl) ⟨1145786, by rfl⟩ : syracuseStep 1527715 = 2291573) B2291573
theorem B1527731 : Blo 1526460 1527731 := bstep (se 1 (by rfl) ⟨1145798, by rfl⟩ : syracuseStep 1527731 = 2291597) B2291597
theorem B1527747 : Blo 1526460 1527747 := bstep (se 1 (by rfl) ⟨1145810, by rfl⟩ : syracuseStep 1527747 = 2291621) B2291621
theorem B1527763 : Blo 1526460 1527763 := bstep (se 1 (by rfl) ⟨1145822, by rfl⟩ : syracuseStep 1527763 = 2291645) B2291645
theorem B2576353 : Blo 1526460 2576353 := bstep (se 2 (by rfl) ⟨966132, by rfl⟩ : syracuseStep 2576353 = 1932265) B1932265
theorem B1527779 : Blo 1526460 1527779 := bstep (se 1 (by rfl) ⟨1145834, by rfl⟩ : syracuseStep 1527779 = 2291669) B2291669
theorem B1527795 : Blo 1526460 1527795 := bstep (se 1 (by rfl) ⟨1145846, by rfl⟩ : syracuseStep 1527795 = 2291693) B2291693
theorem B2576387 : Blo 1526460 2576387 := bstep (se 1 (by rfl) ⟨1932290, by rfl⟩ : syracuseStep 2576387 = 3864581) B3864581
theorem B1527811 : Blo 1526460 1527811 := bstep (se 1 (by rfl) ⟨1145858, by rfl⟩ : syracuseStep 1527811 = 2291717) B2291717
theorem B1527827 : Blo 1526460 1527827 := bstep (se 1 (by rfl) ⟨1145870, by rfl⟩ : syracuseStep 1527827 = 2291741) B2291741
theorem B1527843 : Blo 1526460 1527843 := bstep (se 1 (by rfl) ⟨1145882, by rfl⟩ : syracuseStep 1527843 = 2291765) B2291765
theorem B2289713 : Blo 1526460 2289713 := bstep (se 2 (by rfl) ⟨858642, by rfl⟩ : syracuseStep 2289713 = 1717285) B1717285
theorem B4411441 : Blo 1526460 4411441 := bstep (se 2 (by rfl) ⟨1654290, by rfl⟩ : syracuseStep 4411441 = 3308581) B3308581
theorem B1527859 : Blo 1526460 1527859 := bstep (se 1 (by rfl) ⟨1145894, by rfl⟩ : syracuseStep 1527859 = 2291789) B2291789
theorem B2289731 : Blo 1526460 2289731 := bstep (se 1 (by rfl) ⟨1717298, by rfl⟩ : syracuseStep 2289731 = 3434597) B3434597
theorem B1527875 : Blo 1526460 1527875 := bstep (se 1 (by rfl) ⟨1145906, by rfl⟩ : syracuseStep 1527875 = 2291813) B2291813
theorem B5156945 : Blo 1526460 5156945 := bstep (se 2 (by rfl) ⟨1933854, by rfl⟩ : syracuseStep 5156945 = 3867709) B3867709
theorem B1527891 : Blo 1526460 1527891 := bstep (se 1 (by rfl) ⟨1145918, by rfl⟩ : syracuseStep 1527891 = 2291837) B2291837
theorem B2289761 : Blo 1526460 2289761 := bstep (se 2 (by rfl) ⟨858660, by rfl⟩ : syracuseStep 2289761 = 1717321) B1717321
theorem B1527907 : Blo 1526460 1527907 := bstep (se 1 (by rfl) ⟨1145930, by rfl⟩ : syracuseStep 1527907 = 2291861) B2291861
theorem B7737443 : Blo 1526460 7737443 := bstep (se 1 (by rfl) ⟨5803082, by rfl⟩ : syracuseStep 7737443 = 11606165) B11606165
theorem B2289779 : Blo 1526460 2289779 := bstep (se 1 (by rfl) ⟨1717334, by rfl⟩ : syracuseStep 2289779 = 3434669) B3434669
theorem B1527923 : Blo 1526460 1527923 := bstep (se 1 (by rfl) ⟨1145942, by rfl⟩ : syracuseStep 1527923 = 2291885) B2291885
theorem B2576515 : Blo 1526460 2576515 := bstep (se 1 (by rfl) ⟨1932386, by rfl⟩ : syracuseStep 2576515 = 3864773) B3864773
theorem B1527939 : Blo 1526460 1527939 := bstep (se 1 (by rfl) ⟨1145954, by rfl⟩ : syracuseStep 1527939 = 2291909) B2291909
theorem B2289809 : Blo 1526460 2289809 := bstep (se 2 (by rfl) ⟨858678, by rfl⟩ : syracuseStep 2289809 = 1717357) B1717357
theorem B1527955 : Blo 1526460 1527955 := bstep (se 1 (by rfl) ⟨1145966, by rfl⟩ : syracuseStep 1527955 = 2291933) B2291933
theorem B2445473 : Blo 1526460 2445473 := bstep (se 2 (by rfl) ⟨917052, by rfl⟩ : syracuseStep 2445473 = 1834105) B1834105
theorem B2289827 : Blo 1526460 2289827 := bstep (se 1 (by rfl) ⟨1717370, by rfl⟩ : syracuseStep 2289827 = 3434741) B3434741
theorem B1527971 : Blo 1526460 1527971 := bstep (se 1 (by rfl) ⟨1145978, by rfl⟩ : syracuseStep 1527971 = 2291957) B2291957
theorem B3436721 : Blo 1526460 3436721 := bstep (se 2 (by rfl) ⟨1288770, by rfl⟩ : syracuseStep 3436721 = 2577541) B2577541
theorem B1527987 : Blo 1526460 1527987 := bstep (se 1 (by rfl) ⟨1145990, by rfl⟩ : syracuseStep 1527987 = 2291981) B2291981
theorem B2289857 : Blo 1526460 2289857 := bstep (se 2 (by rfl) ⟨858696, by rfl⟩ : syracuseStep 2289857 = 1717393) B1717393
theorem B3436739 : Blo 1526460 3436739 := bstep (se 1 (by rfl) ⟨2577554, by rfl⟩ : syracuseStep 3436739 = 5155109) B5155109
theorem B1528003 : Blo 1526460 1528003 := bstep (se 1 (by rfl) ⟨1146002, by rfl⟩ : syracuseStep 1528003 = 2292005) B2292005
theorem B2289875 : Blo 1526460 2289875 := bstep (se 1 (by rfl) ⟨1717406, by rfl⟩ : syracuseStep 2289875 = 3434813) B3434813
theorem B1528019 : Blo 1526460 1528019 := bstep (se 1 (by rfl) ⟨1146014, by rfl⟩ : syracuseStep 1528019 = 2292029) B2292029
theorem B19869923 : Blo 1526460 19869923 := bstep (se 1 (by rfl) ⟨14902442, by rfl⟩ : syracuseStep 19869923 = 29804885) B29804885
theorem B1528035 : Blo 1526460 1528035 := bstep (se 1 (by rfl) ⟨1146026, by rfl⟩ : syracuseStep 1528035 = 2292053) B2292053
theorem B2289905 : Blo 1526460 2289905 := bstep (se 2 (by rfl) ⟨858714, by rfl⟩ : syracuseStep 2289905 = 1717429) B1717429
theorem B17404145 : Blo 1526460 17404145 := bstep (se 2 (by rfl) ⟨6526554, by rfl⟩ : syracuseStep 17404145 = 13053109) B13053109
theorem B1528051 : Blo 1526460 1528051 := bstep (se 1 (by rfl) ⟨1146038, by rfl⟩ : syracuseStep 1528051 = 2292077) B2292077
theorem B2289923 : Blo 1526460 2289923 := bstep (se 1 (by rfl) ⟨1717442, by rfl⟩ : syracuseStep 2289923 = 3434885) B3434885
theorem B1528067 : Blo 1526460 1528067 := bstep (se 1 (by rfl) ⟨1146050, by rfl⟩ : syracuseStep 1528067 = 2292101) B2292101
theorem B2576657 : Blo 1526460 2576657 := bstep (se 2 (by rfl) ⟨966246, by rfl⟩ : syracuseStep 2576657 = 1932493) B1932493
theorem B1528083 : Blo 1526460 1528083 := bstep (se 1 (by rfl) ⟨1146062, by rfl⟩ : syracuseStep 1528083 = 2292125) B2292125
theorem B2289953 : Blo 1526460 2289953 := bstep (se 2 (by rfl) ⟨858732, by rfl⟩ : syracuseStep 2289953 = 1717465) B1717465
theorem B1528099 : Blo 1526460 1528099 := bstep (se 1 (by rfl) ⟨1146074, by rfl⟩ : syracuseStep 1528099 = 2292149) B2292149
theorem B2289971 : Blo 1526460 2289971 := bstep (se 1 (by rfl) ⟨1717478, by rfl⟩ : syracuseStep 2289971 = 3434957) B3434957
theorem B1528115 : Blo 1526460 1528115 := bstep (se 1 (by rfl) ⟨1146086, by rfl⟩ : syracuseStep 1528115 = 2292173) B2292173
theorem B1528131 : Blo 1526460 1528131 := bstep (se 1 (by rfl) ⟨1146098, by rfl⟩ : syracuseStep 1528131 = 2292197) B2292197
theorem B2290001 : Blo 1526460 2290001 := bstep (se 2 (by rfl) ⟨858750, by rfl⟩ : syracuseStep 2290001 = 1717501) B1717501
theorem B1528147 : Blo 1526460 1528147 := bstep (se 1 (by rfl) ⟨1146110, by rfl⟩ : syracuseStep 1528147 = 2292221) B2292221
theorem B2290019 : Blo 1526460 2290019 := bstep (se 1 (by rfl) ⟨1717514, by rfl⟩ : syracuseStep 2290019 = 3435029) B3435029
theorem B2175331 : Blo 1526460 2175331 := bstep (se 1 (by rfl) ⟨1631498, by rfl⟩ : syracuseStep 2175331 = 3262997) B3262997
theorem B1528163 : Blo 1526460 1528163 := bstep (se 1 (by rfl) ⟨1146122, by rfl⟩ : syracuseStep 1528163 = 2292245) B2292245
theorem B1765747 : Blo 1526460 1765747 := bstep (se 1 (by rfl) ⟨1324310, by rfl⟩ : syracuseStep 1765747 = 2648621) B2648621
theorem B1528179 : Blo 1526460 1528179 := bstep (se 1 (by rfl) ⟨1146134, by rfl⟩ : syracuseStep 1528179 = 2292269) B2292269
theorem B2290049 : Blo 1526460 2290049 := bstep (se 2 (by rfl) ⟨858768, by rfl⟩ : syracuseStep 2290049 = 1717537) B1717537
theorem B1528195 : Blo 1526460 1528195 := bstep (se 1 (by rfl) ⟨1146146, by rfl⟩ : syracuseStep 1528195 = 2292293) B2292293
theorem B2576785 : Blo 1526460 2576785 := bstep (se 2 (by rfl) ⟨966294, by rfl⟩ : syracuseStep 2576785 = 1932589) B1932589
theorem B2290067 : Blo 1526460 2290067 := bstep (se 1 (by rfl) ⟨1717550, by rfl⟩ : syracuseStep 2290067 = 3435101) B3435101
theorem B1528211 : Blo 1526460 1528211 := bstep (se 1 (by rfl) ⟨1146158, by rfl⟩ : syracuseStep 1528211 = 2292317) B2292317
theorem B8253859 : Blo 1526460 8253859 := bstep (se 1 (by rfl) ⟨6190394, by rfl⟩ : syracuseStep 8253859 = 12380789) B12380789
theorem B1528227 : Blo 1526460 1528227 := bstep (se 1 (by rfl) ⟨1146170, by rfl⟩ : syracuseStep 1528227 = 2292341) B2292341
theorem B2290097 : Blo 1526460 2290097 := bstep (se 2 (by rfl) ⟨858786, by rfl⟩ : syracuseStep 2290097 = 1717573) B1717573
theorem B2576819 : Blo 1526460 2576819 := bstep (se 1 (by rfl) ⟨1932614, by rfl⟩ : syracuseStep 2576819 = 3865229) B3865229
theorem B1528243 : Blo 1526460 1528243 := bstep (se 1 (by rfl) ⟨1146182, by rfl⟩ : syracuseStep 1528243 = 2292365) B2292365
theorem B2445761 : Blo 1526460 2445761 := bstep (se 2 (by rfl) ⟨917160, by rfl⟩ : syracuseStep 2445761 = 1834321) B1834321
theorem B2290115 : Blo 1526460 2290115 := bstep (se 1 (by rfl) ⟨1717586, by rfl⟩ : syracuseStep 2290115 = 3435173) B3435173
theorem B2175427 : Blo 1526460 2175427 := bstep (se 1 (by rfl) ⟨1631570, by rfl⟩ : syracuseStep 2175427 = 3263141) B3263141
theorem B1528259 : Blo 1526460 1528259 := bstep (se 1 (by rfl) ⟨1146194, by rfl⟩ : syracuseStep 1528259 = 2292389) B2292389
theorem B3437009 : Blo 1526460 3437009 := bstep (se 2 (by rfl) ⟨1288878, by rfl⟩ : syracuseStep 3437009 = 2577757) B2577757
theorem B1528275 : Blo 1526460 1528275 := bstep (se 1 (by rfl) ⟨1146206, by rfl⟩ : syracuseStep 1528275 = 2292413) B2292413
theorem B2290145 : Blo 1526460 2290145 := bstep (se 2 (by rfl) ⟨858804, by rfl⟩ : syracuseStep 2290145 = 1717609) B1717609
theorem B3437027 : Blo 1526460 3437027 := bstep (se 1 (by rfl) ⟨2577770, by rfl⟩ : syracuseStep 3437027 = 5155541) B5155541
theorem B1528291 : Blo 1526460 1528291 := bstep (se 1 (by rfl) ⟨1146218, by rfl⟩ : syracuseStep 1528291 = 2292437) B2292437
theorem B2290163 : Blo 1526460 2290163 := bstep (se 1 (by rfl) ⟨1717622, by rfl⟩ : syracuseStep 2290163 = 3435245) B3435245
theorem B1528307 : Blo 1526460 1528307 := bstep (se 1 (by rfl) ⟨1146230, by rfl⟩ : syracuseStep 1528307 = 2292461) B2292461
theorem B1528323 : Blo 1526460 1528323 := bstep (se 1 (by rfl) ⟨1146242, by rfl⟩ : syracuseStep 1528323 = 2292485) B2292485
theorem B2290193 : Blo 1526460 2290193 := bstep (se 2 (by rfl) ⟨858822, by rfl⟩ : syracuseStep 2290193 = 1717645) B1717645
theorem B1528339 : Blo 1526460 1528339 := bstep (se 1 (by rfl) ⟨1146254, by rfl⟩ : syracuseStep 1528339 = 2292509) B2292509
theorem B2290211 : Blo 1526460 2290211 := bstep (se 1 (by rfl) ⟨1717658, by rfl⟩ : syracuseStep 2290211 = 3435317) B3435317
theorem B1528355 : Blo 1526460 1528355 := bstep (se 1 (by rfl) ⟨1146266, by rfl⟩ : syracuseStep 1528355 = 2292533) B2292533
theorem B2576947 : Blo 1526460 2576947 := bstep (se 1 (by rfl) ⟨1932710, by rfl⟩ : syracuseStep 2576947 = 3865421) B3865421
theorem B1528371 : Blo 1526460 1528371 := bstep (se 1 (by rfl) ⟨1146278, by rfl⟩ : syracuseStep 1528371 = 2292557) B2292557
theorem B2290241 : Blo 1526460 2290241 := bstep (se 2 (by rfl) ⟨858840, by rfl⟩ : syracuseStep 2290241 = 1717681) B1717681
theorem B1528387 : Blo 1526460 1528387 := bstep (se 1 (by rfl) ⟨1146290, by rfl⟩ : syracuseStep 1528387 = 2292581) B2292581
theorem B2290259 : Blo 1526460 2290259 := bstep (se 1 (by rfl) ⟨1717694, by rfl⟩ : syracuseStep 2290259 = 3435389) B3435389
theorem B1528403 : Blo 1526460 1528403 := bstep (se 1 (by rfl) ⟨1146302, by rfl⟩ : syracuseStep 1528403 = 2292605) B2292605
theorem B1528419 : Blo 1526460 1528419 := bstep (se 1 (by rfl) ⟨1146314, by rfl⟩ : syracuseStep 1528419 = 2292629) B2292629
theorem B5157485 : Blo 1526460 5157485 := bstep (se 3 (by rfl) ⟨967028, by rfl⟩ : syracuseStep 5157485 = 1934057) B1934057
theorem B2290289 : Blo 1526460 2290289 := bstep (se 2 (by rfl) ⟨858858, by rfl⟩ : syracuseStep 2290289 = 1717717) B1717717
theorem B1528435 : Blo 1526460 1528435 := bstep (se 1 (by rfl) ⟨1146326, by rfl⟩ : syracuseStep 1528435 = 2292653) B2292653
theorem B2290307 : Blo 1526460 2290307 := bstep (se 1 (by rfl) ⟨1717730, by rfl⟩ : syracuseStep 2290307 = 3435461) B3435461
theorem B1528451 : Blo 1526460 1528451 := bstep (se 1 (by rfl) ⟨1146338, by rfl⟩ : syracuseStep 1528451 = 2292677) B2292677
theorem B2290337 : Blo 1526460 2290337 := bstep (se 2 (by rfl) ⟨858876, by rfl⟩ : syracuseStep 2290337 = 1717753) B1717753
theorem B2445985 : Blo 1526460 2445985 := bstep (se 2 (by rfl) ⟨917244, by rfl⟩ : syracuseStep 2445985 = 1834489) B1834489
theorem B5157539 : Blo 1526460 5157539 := bstep (se 1 (by rfl) ⟨3868154, by rfl⟩ : syracuseStep 5157539 = 7736309) B7736309
theorem B9286321 : Blo 1526460 9286321 := bstep (se 2 (by rfl) ⟨3482370, by rfl⟩ : syracuseStep 9286321 = 6964741) B6964741
theorem B2290355 : Blo 1526460 2290355 := bstep (se 1 (by rfl) ⟨1717766, by rfl⟩ : syracuseStep 2290355 = 3435533) B3435533
theorem B2577089 : Blo 1526460 2577089 := bstep (se 2 (by rfl) ⟨966408, by rfl⟩ : syracuseStep 2577089 = 1932817) B1932817
theorem B2290385 : Blo 1526460 2290385 := bstep (se 2 (by rfl) ⟨858894, by rfl⟩ : syracuseStep 2290385 = 1717789) B1717789
theorem B2290403 : Blo 1526460 2290403 := bstep (se 1 (by rfl) ⟨1717802, by rfl⟩ : syracuseStep 2290403 = 3435605) B3435605
theorem B11604707 : Blo 1526460 11604707 := bstep (se 1 (by rfl) ⟨8703530, by rfl⟩ : syracuseStep 11604707 = 17407061) B17407061
theorem B3437297 : Blo 1526460 3437297 := bstep (se 2 (by rfl) ⟨1288986, by rfl⟩ : syracuseStep 3437297 = 2577973) B2577973
theorem B2290433 : Blo 1526460 2290433 := bstep (se 2 (by rfl) ⟨858912, by rfl⟩ : syracuseStep 2290433 = 1717825) B1717825
theorem B3437315 : Blo 1526460 3437315 := bstep (se 1 (by rfl) ⟨2577986, by rfl⟩ : syracuseStep 3437315 = 5155973) B5155973
theorem B2290451 : Blo 1526460 2290451 := bstep (se 1 (by rfl) ⟨1717838, by rfl⟩ : syracuseStep 2290451 = 3435677) B3435677
theorem B5796643 : Blo 1526460 5796643 := bstep (se 1 (by rfl) ⟨4347482, by rfl⟩ : syracuseStep 5796643 = 8694965) B8694965
theorem B2323235 : Blo 1526460 2323235 := bstep (se 1 (by rfl) ⟨1742426, by rfl⟩ : syracuseStep 2323235 = 3484853) B3484853
theorem B3920675 : Blo 1526460 3920675 := bstep (se 1 (by rfl) ⟨2940506, by rfl⟩ : syracuseStep 3920675 = 5881013) B5881013
theorem B2290481 : Blo 1526460 2290481 := bstep (se 2 (by rfl) ⟨858930, by rfl⟩ : syracuseStep 2290481 = 1717861) B1717861
theorem B2577217 : Blo 1526460 2577217 := bstep (se 2 (by rfl) ⟨966456, by rfl⟩ : syracuseStep 2577217 = 1932913) B1932913
theorem B2290499 : Blo 1526460 2290499 := bstep (se 1 (by rfl) ⟨1717874, by rfl⟩ : syracuseStep 2290499 = 3435749) B3435749
theorem B2290529 : Blo 1526460 2290529 := bstep (se 2 (by rfl) ⟨858948, by rfl⟩ : syracuseStep 2290529 = 1717897) B1717897
theorem B2577251 : Blo 1526460 2577251 := bstep (se 1 (by rfl) ⟨1932938, by rfl⟩ : syracuseStep 2577251 = 3865877) B3865877
theorem B2290547 : Blo 1526460 2290547 := bstep (se 1 (by rfl) ⟨1717910, by rfl⟩ : syracuseStep 2290547 = 3435821) B3435821
theorem B2290577 : Blo 1526460 2290577 := bstep (se 2 (by rfl) ⟨858966, by rfl⟩ : syracuseStep 2290577 = 1717933) B1717933
theorem B2290595 : Blo 1526460 2290595 := bstep (se 1 (by rfl) ⟨1717946, by rfl⟩ : syracuseStep 2290595 = 3435893) B3435893
theorem B5157809 : Blo 1526460 5157809 := bstep (se 2 (by rfl) ⟨1934178, by rfl⟩ : syracuseStep 5157809 = 3868357) B3868357
theorem B2175923 : Blo 1526460 2175923 := bstep (se 1 (by rfl) ⟨1631942, by rfl⟩ : syracuseStep 2175923 = 3263885) B3263885
theorem B2290625 : Blo 1526460 2290625 := bstep (se 2 (by rfl) ⟨858984, by rfl⟩ : syracuseStep 2290625 = 1717969) B1717969
theorem B2290643 : Blo 1526460 2290643 := bstep (se 1 (by rfl) ⟨1717982, by rfl⟩ : syracuseStep 2290643 = 3435965) B3435965
theorem B2577379 : Blo 1526460 2577379 := bstep (se 1 (by rfl) ⟨1933034, by rfl⟩ : syracuseStep 2577379 = 3866069) B3866069
theorem B2290673 : Blo 1526460 2290673 := bstep (se 2 (by rfl) ⟨859002, by rfl⟩ : syracuseStep 2290673 = 1718005) B1718005
theorem B2290691 : Blo 1526460 2290691 := bstep (se 1 (by rfl) ⟨1718018, by rfl⟩ : syracuseStep 2290691 = 3436037) B3436037
theorem B3437585 : Blo 1526460 3437585 := bstep (se 2 (by rfl) ⟨1289094, by rfl⟩ : syracuseStep 3437585 = 2578189) B2578189
theorem B1741843 : Blo 1526460 1741843 := bstep (se 1 (by rfl) ⟨1306382, by rfl⟩ : syracuseStep 1741843 = 2612765) B2612765
theorem B2290721 : Blo 1526460 2290721 := bstep (se 2 (by rfl) ⟨859020, by rfl⟩ : syracuseStep 2290721 = 1718041) B1718041
theorem B3437603 : Blo 1526460 3437603 := bstep (se 1 (by rfl) ⟨2578202, by rfl⟩ : syracuseStep 3437603 = 5156405) B5156405
theorem B2290739 : Blo 1526460 2290739 := bstep (se 1 (by rfl) ⟨1718054, by rfl⟩ : syracuseStep 2290739 = 3436109) B3436109
theorem B2290769 : Blo 1526460 2290769 := bstep (se 2 (by rfl) ⟨859038, by rfl⟩ : syracuseStep 2290769 = 1718077) B1718077
theorem B2290787 : Blo 1526460 2290787 := bstep (se 1 (by rfl) ⟨1718090, by rfl⟩ : syracuseStep 2290787 = 3436181) B3436181
theorem B2577521 : Blo 1526460 2577521 := bstep (se 2 (by rfl) ⟨966570, by rfl⟩ : syracuseStep 2577521 = 1933141) B1933141
theorem B2290817 : Blo 1526460 2290817 := bstep (se 2 (by rfl) ⟨859056, by rfl⟩ : syracuseStep 2290817 = 1718113) B1718113
theorem B2290835 : Blo 1526460 2290835 := bstep (se 1 (by rfl) ⟨1718126, by rfl⟩ : syracuseStep 2290835 = 3436253) B3436253
theorem B1717411 : Blo 1526460 1717411 := bstep (se 1 (by rfl) ⟨1288058, by rfl⟩ : syracuseStep 1717411 = 2576117) B2576117
theorem B2290865 : Blo 1526460 2290865 := bstep (se 2 (by rfl) ⟨859074, by rfl⟩ : syracuseStep 2290865 = 1718149) B1718149
theorem B6526129 : Blo 1526460 6526129 := bstep (se 2 (by rfl) ⟨2447298, by rfl⟩ : syracuseStep 6526129 = 4894597) B4894597
theorem B2290883 : Blo 1526460 2290883 := bstep (se 1 (by rfl) ⟨1718162, by rfl⟩ : syracuseStep 2290883 = 3436325) B3436325
theorem B2290913 : Blo 1526460 2290913 := bstep (se 2 (by rfl) ⟨859092, by rfl⟩ : syracuseStep 2290913 = 1718185) B1718185
theorem B4642019 : Blo 1526460 4642019 := bstep (se 1 (by rfl) ⟨3481514, by rfl⟩ : syracuseStep 4642019 = 6963029) B6963029
theorem B4707569 : Blo 1526460 4707569 := bstep (se 2 (by rfl) ⟨1765338, by rfl⟩ : syracuseStep 4707569 = 3530677) B3530677
theorem B2577649 : Blo 1526460 2577649 := bstep (se 2 (by rfl) ⟨966618, by rfl⟩ : syracuseStep 2577649 = 1933237) B1933237
theorem B2290931 : Blo 1526460 2290931 := bstep (se 1 (by rfl) ⟨1718198, by rfl⟩ : syracuseStep 2290931 = 3436397) B3436397
theorem B2290961 : Blo 1526460 2290961 := bstep (se 2 (by rfl) ⟨859110, by rfl⟩ : syracuseStep 2290961 = 1718221) B1718221
theorem B2577683 : Blo 1526460 2577683 := bstep (se 1 (by rfl) ⟨1933262, by rfl⟩ : syracuseStep 2577683 = 3866525) B3866525
theorem B2290979 : Blo 1526460 2290979 := bstep (se 1 (by rfl) ⟨1718234, by rfl⟩ : syracuseStep 2290979 = 3436469) B3436469
theorem B3437873 : Blo 1526460 3437873 := bstep (se 2 (by rfl) ⟨1289202, by rfl⟩ : syracuseStep 3437873 = 2578405) B2578405
theorem B1717555 : Blo 1526460 1717555 := bstep (se 1 (by rfl) ⟨1288166, by rfl⟩ : syracuseStep 1717555 = 2576333) B2576333
theorem B2291009 : Blo 1526460 2291009 := bstep (se 2 (by rfl) ⟨859128, by rfl⟩ : syracuseStep 2291009 = 1718257) B1718257
theorem B3437891 : Blo 1526460 3437891 := bstep (se 1 (by rfl) ⟨2578418, by rfl⟩ : syracuseStep 3437891 = 5156837) B5156837
theorem B2291027 : Blo 1526460 2291027 := bstep (se 1 (by rfl) ⟨1718270, by rfl⟩ : syracuseStep 2291027 = 3436541) B3436541
theorem B2291057 : Blo 1526460 2291057 := bstep (se 2 (by rfl) ⟨859146, by rfl⟩ : syracuseStep 2291057 = 1718293) B1718293
theorem B2291075 : Blo 1526460 2291075 := bstep (se 1 (by rfl) ⟨1718306, by rfl⟩ : syracuseStep 2291075 = 3436613) B3436613
theorem B9786757 : Blo 1526460 9786757 := bstep (se 4 (by rfl) ⟨917508, by rfl⟩ : syracuseStep 9786757 = 1835017) B1835017
theorem B2577811 : Blo 1526460 2577811 := bstep (se 1 (by rfl) ⟨1933358, by rfl⟩ : syracuseStep 2577811 = 3866717) B3866717
theorem B2291105 : Blo 1526460 2291105 := bstep (se 2 (by rfl) ⟨859164, by rfl⟩ : syracuseStep 2291105 = 1718329) B1718329
theorem B2291123 : Blo 1526460 2291123 := bstep (se 1 (by rfl) ⟨1718342, by rfl⟩ : syracuseStep 2291123 = 3436685) B3436685
theorem B1717699 : Blo 1526460 1717699 := bstep (se 1 (by rfl) ⟨1288274, by rfl⟩ : syracuseStep 1717699 = 2576549) B2576549
theorem B5158349 : Blo 1526460 5158349 := bstep (se 3 (by rfl) ⟨967190, by rfl⟩ : syracuseStep 5158349 = 1934381) B1934381
theorem B2291153 : Blo 1526460 2291153 := bstep (se 2 (by rfl) ⟨859182, by rfl⟩ : syracuseStep 2291153 = 1718365) B1718365
theorem B2291171 : Blo 1526460 2291171 := bstep (se 1 (by rfl) ⟨1718378, by rfl⟩ : syracuseStep 2291171 = 3436757) B3436757
theorem B16520689 : Blo 1526460 16520689 := bstep (se 2 (by rfl) ⟨6195258, by rfl⟩ : syracuseStep 16520689 = 12390517) B12390517
theorem B1570291 : Blo 1526460 1570291 := bstep (se 1 (by rfl) ⟨1177718, by rfl⟩ : syracuseStep 1570291 = 2355437) B2355437
theorem B2291201 : Blo 1526460 2291201 := bstep (se 2 (by rfl) ⟨859200, by rfl⟩ : syracuseStep 2291201 = 1718401) B1718401
theorem B5158403 : Blo 1526460 5158403 := bstep (se 1 (by rfl) ⟨3868802, by rfl⟩ : syracuseStep 5158403 = 7737605) B7737605
theorem B2291219 : Blo 1526460 2291219 := bstep (se 1 (by rfl) ⟨1718414, by rfl⟩ : syracuseStep 2291219 = 3436829) B3436829
theorem B2577953 : Blo 1526460 2577953 := bstep (se 2 (by rfl) ⟨966732, by rfl⟩ : syracuseStep 2577953 = 1933465) B1933465
theorem B4896301 : Blo 1526460 4896301 := bstep (se 3 (by rfl) ⟨918056, by rfl⟩ : syracuseStep 4896301 = 1836113) B1836113
theorem B2291249 : Blo 1526460 2291249 := bstep (se 2 (by rfl) ⟨859218, by rfl⟩ : syracuseStep 2291249 = 1718437) B1718437
theorem B2291267 : Blo 1526460 2291267 := bstep (se 1 (by rfl) ⟨1718450, by rfl⟩ : syracuseStep 2291267 = 3436901) B3436901
theorem B3864145 : Blo 1526460 3864145 := bstep (se 2 (by rfl) ⟨1449054, by rfl⟩ : syracuseStep 3864145 = 2898109) B2898109
theorem B3438161 : Blo 1526460 3438161 := bstep (se 2 (by rfl) ⟨1289310, by rfl⟩ : syracuseStep 3438161 = 2578621) B2578621
theorem B1717843 : Blo 1526460 1717843 := bstep (se 1 (by rfl) ⟨1288382, by rfl⟩ : syracuseStep 1717843 = 2576765) B2576765
theorem B2291297 : Blo 1526460 2291297 := bstep (se 2 (by rfl) ⟨859236, by rfl⟩ : syracuseStep 2291297 = 1718473) B1718473
theorem B3438179 : Blo 1526460 3438179 := bstep (se 1 (by rfl) ⟨2578634, by rfl⟩ : syracuseStep 3438179 = 5157269) B5157269
theorem B7730801 : Blo 1526460 7730801 := bstep (se 2 (by rfl) ⟨2899050, by rfl⟩ : syracuseStep 7730801 = 5798101) B5798101
theorem B2291315 : Blo 1526460 2291315 := bstep (se 1 (by rfl) ⟨1718486, by rfl⟩ : syracuseStep 2291315 = 3436973) B3436973
theorem B2291345 : Blo 1526460 2291345 := bstep (se 2 (by rfl) ⟨859254, by rfl⟩ : syracuseStep 2291345 = 1718509) B1718509
theorem B2578081 : Blo 1526460 2578081 := bstep (se 2 (by rfl) ⟨966780, by rfl⟩ : syracuseStep 2578081 = 1933561) B1933561
theorem B2291363 : Blo 1526460 2291363 := bstep (se 1 (by rfl) ⟨1718522, by rfl⟩ : syracuseStep 2291363 = 3437045) B3437045
theorem B2291393 : Blo 1526460 2291393 := bstep (se 2 (by rfl) ⟨859272, by rfl⟩ : syracuseStep 2291393 = 1718545) B1718545
theorem B2578115 : Blo 1526460 2578115 := bstep (se 1 (by rfl) ⟨1933586, by rfl⟩ : syracuseStep 2578115 = 3867173) B3867173
theorem B2291411 : Blo 1526460 2291411 := bstep (se 1 (by rfl) ⟨1718558, by rfl⟩ : syracuseStep 2291411 = 3437117) B3437117
theorem B1717987 : Blo 1526460 1717987 := bstep (se 1 (by rfl) ⟨1288490, by rfl⟩ : syracuseStep 1717987 = 2576981) B2576981
theorem B2291441 : Blo 1526460 2291441 := bstep (se 2 (by rfl) ⟨859290, by rfl⟩ : syracuseStep 2291441 = 1718581) B1718581
theorem B2291459 : Blo 1526460 2291459 := bstep (se 1 (by rfl) ⟨1718594, by rfl⟩ : syracuseStep 2291459 = 3437189) B3437189
theorem B4126477 : Blo 1526460 4126477 := bstep (se 3 (by rfl) ⟨773714, by rfl⟩ : syracuseStep 4126477 = 1547429) B1547429
theorem B4347665 : Blo 1526460 4347665 := bstep (se 2 (by rfl) ⟨1630374, by rfl⟩ : syracuseStep 4347665 = 3260749) B3260749
theorem B2291489 : Blo 1526460 2291489 := bstep (se 2 (by rfl) ⟨859308, by rfl⟩ : syracuseStep 2291489 = 1718617) B1718617
theorem B2291507 : Blo 1526460 2291507 := bstep (se 1 (by rfl) ⟨1718630, by rfl⟩ : syracuseStep 2291507 = 3437261) B3437261
theorem B2578243 : Blo 1526460 2578243 := bstep (se 1 (by rfl) ⟨1933682, by rfl⟩ : syracuseStep 2578243 = 3867365) B3867365
theorem B2291537 : Blo 1526460 2291537 := bstep (se 2 (by rfl) ⟨859326, by rfl⟩ : syracuseStep 2291537 = 1718653) B1718653
theorem B3864419 : Blo 1526460 3864419 := bstep (se 1 (by rfl) ⟨2898314, by rfl⟩ : syracuseStep 3864419 = 5796629) B5796629
theorem B2291555 : Blo 1526460 2291555 := bstep (se 1 (by rfl) ⟨1718666, by rfl⟩ : syracuseStep 2291555 = 3437333) B3437333
theorem B13055843 : Blo 1526460 13055843 := bstep (se 1 (by rfl) ⟨9791882, by rfl⟩ : syracuseStep 13055843 = 19583765) B19583765
theorem B3438449 : Blo 1526460 3438449 := bstep (se 2 (by rfl) ⟨1289418, by rfl⟩ : syracuseStep 3438449 = 2578837) B2578837
theorem B1718131 : Blo 1526460 1718131 := bstep (se 1 (by rfl) ⟨1288598, by rfl⟩ : syracuseStep 1718131 = 2577197) B2577197
theorem B2291585 : Blo 1526460 2291585 := bstep (se 2 (by rfl) ⟨859344, by rfl⟩ : syracuseStep 2291585 = 1718689) B1718689
theorem B3438467 : Blo 1526460 3438467 := bstep (se 1 (by rfl) ⟨2578850, by rfl⟩ : syracuseStep 3438467 = 5157701) B5157701
theorem B2291603 : Blo 1526460 2291603 := bstep (se 1 (by rfl) ⟨1718702, by rfl⟩ : syracuseStep 2291603 = 3437405) B3437405
theorem B2291633 : Blo 1526460 2291633 := bstep (se 2 (by rfl) ⟨859362, by rfl⟩ : syracuseStep 2291633 = 1718725) B1718725
theorem B2291651 : Blo 1526460 2291651 := bstep (se 1 (by rfl) ⟨1718738, by rfl⟩ : syracuseStep 2291651 = 3437477) B3437477
theorem B2578385 : Blo 1526460 2578385 := bstep (se 2 (by rfl) ⟨966894, by rfl⟩ : syracuseStep 2578385 = 1933789) B1933789
theorem B2291681 : Blo 1526460 2291681 := bstep (se 2 (by rfl) ⟨859380, by rfl⟩ : syracuseStep 2291681 = 1718761) B1718761
theorem B2291699 : Blo 1526460 2291699 := bstep (se 1 (by rfl) ⟨1718774, by rfl⟩ : syracuseStep 2291699 = 3437549) B3437549
theorem B1718275 : Blo 1526460 1718275 := bstep (se 1 (by rfl) ⟨1288706, by rfl⟩ : syracuseStep 1718275 = 2577413) B2577413
theorem B2291729 : Blo 1526460 2291729 := bstep (se 2 (by rfl) ⟨859398, by rfl⟩ : syracuseStep 2291729 = 1718797) B1718797
theorem B3864611 : Blo 1526460 3864611 := bstep (se 1 (by rfl) ⟨2898458, by rfl⟩ : syracuseStep 3864611 = 5796917) B5796917
theorem B2291747 : Blo 1526460 2291747 := bstep (se 1 (by rfl) ⟨1718810, by rfl⟩ : syracuseStep 2291747 = 3437621) B3437621
theorem B2291777 : Blo 1526460 2291777 := bstep (se 2 (by rfl) ⟨859416, by rfl⟩ : syracuseStep 2291777 = 1718833) B1718833
theorem B2578513 : Blo 1526460 2578513 := bstep (se 2 (by rfl) ⟨966942, by rfl⟩ : syracuseStep 2578513 = 1933885) B1933885
theorem B2291795 : Blo 1526460 2291795 := bstep (se 1 (by rfl) ⟨1718846, by rfl⟩ : syracuseStep 2291795 = 3437693) B3437693
theorem B2291825 : Blo 1526460 2291825 := bstep (se 2 (by rfl) ⟨859434, by rfl⟩ : syracuseStep 2291825 = 1718869) B1718869
theorem B2578547 : Blo 1526460 2578547 := bstep (se 1 (by rfl) ⟨1933910, by rfl⟩ : syracuseStep 2578547 = 3867821) B3867821
theorem B2291843 : Blo 1526460 2291843 := bstep (se 1 (by rfl) ⟨1718882, by rfl⟩ : syracuseStep 2291843 = 3437765) B3437765
theorem B3438737 : Blo 1526460 3438737 := bstep (se 2 (by rfl) ⟨1289526, by rfl⟩ : syracuseStep 3438737 = 2579053) B2579053
theorem B1718419 : Blo 1526460 1718419 := bstep (se 1 (by rfl) ⟨1288814, by rfl⟩ : syracuseStep 1718419 = 2577629) B2577629
theorem B2291873 : Blo 1526460 2291873 := bstep (se 2 (by rfl) ⟨859452, by rfl⟩ : syracuseStep 2291873 = 1718905) B1718905
theorem B3438755 : Blo 1526460 3438755 := bstep (se 1 (by rfl) ⟨2579066, by rfl⟩ : syracuseStep 3438755 = 5158133) B5158133
theorem B5224625 : Blo 1526460 5224625 := bstep (se 2 (by rfl) ⟨1959234, by rfl⟩ : syracuseStep 5224625 = 3918469) B3918469
theorem B2291891 : Blo 1526460 2291891 := bstep (se 1 (by rfl) ⟨1718918, by rfl⟩ : syracuseStep 2291891 = 3437837) B3437837
theorem B2291921 : Blo 1526460 2291921 := bstep (se 2 (by rfl) ⟨859470, by rfl⟩ : syracuseStep 2291921 = 1718941) B1718941
theorem B59504867 : Blo 1526460 59504867 := bstep (se 1 (by rfl) ⟨44628650, by rfl⟩ : syracuseStep 59504867 = 89257301) B89257301
theorem B2291939 : Blo 1526460 2291939 := bstep (se 1 (by rfl) ⟨1718954, by rfl⟩ : syracuseStep 2291939 = 3437909) B3437909
theorem B2447587 : Blo 1526460 2447587 := bstep (se 1 (by rfl) ⟨1835690, by rfl⟩ : syracuseStep 2447587 = 3671381) B3671381
theorem B2578675 : Blo 1526460 2578675 := bstep (se 1 (by rfl) ⟨1934006, by rfl⟩ : syracuseStep 2578675 = 3868013) B3868013
theorem B2291969 : Blo 1526460 2291969 := bstep (se 2 (by rfl) ⟨859488, by rfl⟩ : syracuseStep 2291969 = 1718977) B1718977
theorem B2898193 : Blo 1526460 2898193 := bstep (se 2 (by rfl) ⟨1086822, by rfl⟩ : syracuseStep 2898193 = 2173645) B2173645
theorem B2291987 : Blo 1526460 2291987 := bstep (se 1 (by rfl) ⟨1718990, by rfl⟩ : syracuseStep 2291987 = 3437981) B3437981
theorem B1718563 : Blo 1526460 1718563 := bstep (se 1 (by rfl) ⟨1288922, by rfl⟩ : syracuseStep 1718563 = 2577845) B2577845
theorem B2292017 : Blo 1526460 2292017 := bstep (se 2 (by rfl) ⟨859506, by rfl⟩ : syracuseStep 2292017 = 1719013) B1719013
theorem B2292035 : Blo 1526460 2292035 := bstep (se 1 (by rfl) ⟨1719026, by rfl⟩ : syracuseStep 2292035 = 3438053) B3438053
theorem B4962637 : Blo 1526460 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B2292065 : Blo 1526460 2292065 := bstep (se 2 (by rfl) ⟨859524, by rfl⟩ : syracuseStep 2292065 = 1719049) B1719049
theorem B2292083 : Blo 1526460 2292083 := bstep (se 1 (by rfl) ⟨1719062, by rfl⟩ : syracuseStep 2292083 = 3438125) B3438125
theorem B2578817 : Blo 1526460 2578817 := bstep (se 2 (by rfl) ⟨967056, by rfl⟩ : syracuseStep 2578817 = 1934113) B1934113
theorem B2292113 : Blo 1526460 2292113 := bstep (se 2 (by rfl) ⟨859542, by rfl⟩ : syracuseStep 2292113 = 1719085) B1719085
theorem B2292131 : Blo 1526460 2292131 := bstep (se 1 (by rfl) ⟨1719098, by rfl⟩ : syracuseStep 2292131 = 3438197) B3438197
theorem B3439025 : Blo 1526460 3439025 := bstep (se 2 (by rfl) ⟨1289634, by rfl⟩ : syracuseStep 3439025 = 2579269) B2579269
theorem B1718707 : Blo 1526460 1718707 := bstep (se 1 (by rfl) ⟨1289030, by rfl⟩ : syracuseStep 1718707 = 2578061) B2578061
theorem B2611649 : Blo 1526460 2611649 := bstep (se 2 (by rfl) ⟨979368, by rfl⟩ : syracuseStep 2611649 = 1958737) B1958737
theorem B2292161 : Blo 1526460 2292161 := bstep (se 2 (by rfl) ⟨859560, by rfl⟩ : syracuseStep 2292161 = 1719121) B1719121
theorem B2292179 : Blo 1526460 2292179 := bstep (se 1 (by rfl) ⟨1719134, by rfl⟩ : syracuseStep 2292179 = 3438269) B3438269
theorem B2292209 : Blo 1526460 2292209 := bstep (se 2 (by rfl) ⟨859578, by rfl⟩ : syracuseStep 2292209 = 1719157) B1719157
theorem B2578945 : Blo 1526460 2578945 := bstep (se 2 (by rfl) ⟨967104, by rfl⟩ : syracuseStep 2578945 = 1934209) B1934209
theorem B2292227 : Blo 1526460 2292227 := bstep (se 1 (by rfl) ⟨1719170, by rfl⟩ : syracuseStep 2292227 = 3438341) B3438341
theorem B2292257 : Blo 1526460 2292257 := bstep (se 2 (by rfl) ⟨859596, by rfl⟩ : syracuseStep 2292257 = 1719193) B1719193
theorem B2578979 : Blo 1526460 2578979 := bstep (se 1 (by rfl) ⟨1934234, by rfl⟩ : syracuseStep 2578979 = 3868469) B3868469
theorem B2292275 : Blo 1526460 2292275 := bstep (se 1 (by rfl) ⟨1719206, by rfl⟩ : syracuseStep 2292275 = 3438413) B3438413
theorem B1718851 : Blo 1526460 1718851 := bstep (se 1 (by rfl) ⟨1289138, by rfl⟩ : syracuseStep 1718851 = 2578277) B2578277
theorem B14678597 : Blo 1526460 14678597 := bstep (se 4 (by rfl) ⟨1376118, by rfl⟩ : syracuseStep 14678597 = 2752237) B2752237
theorem B2292305 : Blo 1526460 2292305 := bstep (se 2 (by rfl) ⟨859614, by rfl⟩ : syracuseStep 2292305 = 1719229) B1719229
theorem B2292323 : Blo 1526460 2292323 := bstep (se 1 (by rfl) ⟨1719242, by rfl⟩ : syracuseStep 2292323 = 3438485) B3438485
theorem B2292353 : Blo 1526460 2292353 := bstep (se 2 (by rfl) ⟨859632, by rfl⟩ : syracuseStep 2292353 = 1719265) B1719265
theorem B2292371 : Blo 1526460 2292371 := bstep (se 1 (by rfl) ⟨1719278, by rfl⟩ : syracuseStep 2292371 = 3438557) B3438557
theorem B2898595 : Blo 1526460 2898595 := bstep (se 1 (by rfl) ⟨2173946, by rfl⟩ : syracuseStep 2898595 = 4347893) B4347893
theorem B2579107 : Blo 1526460 2579107 := bstep (se 1 (by rfl) ⟨1934330, by rfl⟩ : syracuseStep 2579107 = 3868661) B3868661
theorem B2292401 : Blo 1526460 2292401 := bstep (se 2 (by rfl) ⟨859650, by rfl⟩ : syracuseStep 2292401 = 1719301) B1719301
theorem B2292419 : Blo 1526460 2292419 := bstep (se 1 (by rfl) ⟨1719314, by rfl⟩ : syracuseStep 2292419 = 3438629) B3438629
theorem B2898641 : Blo 1526460 2898641 := bstep (se 2 (by rfl) ⟨1086990, by rfl⟩ : syracuseStep 2898641 = 2173981) B2173981
theorem B3668689 : Blo 1526460 3668689 := bstep (se 2 (by rfl) ⟨1375758, by rfl⟩ : syracuseStep 3668689 = 2751517) B2751517
theorem B1718995 : Blo 1526460 1718995 := bstep (se 1 (by rfl) ⟨1289246, by rfl⟩ : syracuseStep 1718995 = 2578493) B2578493
theorem B2292449 : Blo 1526460 2292449 := bstep (se 2 (by rfl) ⟨859668, by rfl⟩ : syracuseStep 2292449 = 1719337) B1719337
theorem B2292467 : Blo 1526460 2292467 := bstep (se 1 (by rfl) ⟨1719350, by rfl⟩ : syracuseStep 2292467 = 3438701) B3438701
theorem B2292497 : Blo 1526460 2292497 := bstep (se 2 (by rfl) ⟨859686, by rfl⟩ : syracuseStep 2292497 = 1719373) B1719373
theorem B2292515 : Blo 1526460 2292515 := bstep (se 1 (by rfl) ⟨1719386, by rfl⟩ : syracuseStep 2292515 = 3438773) B3438773
theorem B4127537 : Blo 1526460 4127537 := bstep (se 2 (by rfl) ⟨1547826, by rfl⟩ : syracuseStep 4127537 = 3095653) B3095653
theorem B2579249 : Blo 1526460 2579249 := bstep (se 2 (by rfl) ⟨967218, by rfl⟩ : syracuseStep 2579249 = 1934437) B1934437
theorem B2292545 : Blo 1526460 2292545 := bstep (se 2 (by rfl) ⟨859704, by rfl⟩ : syracuseStep 2292545 = 1719409) B1719409
theorem B2292563 : Blo 1526460 2292563 := bstep (se 1 (by rfl) ⟨1719422, by rfl⟩ : syracuseStep 2292563 = 3438845) B3438845
theorem B8813411 : Blo 1526460 8813411 := bstep (se 1 (by rfl) ⟨6610058, by rfl⟩ : syracuseStep 8813411 = 13220117) B13220117
theorem B1719139 : Blo 1526460 1719139 := bstep (se 1 (by rfl) ⟨1289354, by rfl⟩ : syracuseStep 1719139 = 2578709) B2578709
theorem B26082161 : Blo 1526460 26082161 := bstep (se 2 (by rfl) ⟨9780810, by rfl⟩ : syracuseStep 26082161 = 19561621) B19561621
theorem B2292593 : Blo 1526460 2292593 := bstep (se 2 (by rfl) ⟨859722, by rfl⟩ : syracuseStep 2292593 = 1719445) B1719445
theorem B2292611 : Blo 1526460 2292611 := bstep (se 1 (by rfl) ⟨1719458, by rfl⟩ : syracuseStep 2292611 = 3438917) B3438917
theorem B3668881 : Blo 1526460 3668881 := bstep (se 2 (by rfl) ⟨1375830, by rfl⟩ : syracuseStep 3668881 = 2751661) B2751661
theorem B2292641 : Blo 1526460 2292641 := bstep (se 2 (by rfl) ⟨859740, by rfl⟩ : syracuseStep 2292641 = 1719481) B1719481
theorem B2063281 : Blo 1526460 2063281 := bstep (se 2 (by rfl) ⟨773730, by rfl⟩ : syracuseStep 2063281 = 1547461) B1547461
theorem B2292659 : Blo 1526460 2292659 := bstep (se 1 (by rfl) ⟨1719494, by rfl⟩ : syracuseStep 2292659 = 3438989) B3438989
theorem B5798861 : Blo 1526460 5798861 := bstep (se 3 (by rfl) ⟨1087286, by rfl⟩ : syracuseStep 5798861 = 2174573) B2174573
theorem B3865553 : Blo 1526460 3865553 := bstep (se 2 (by rfl) ⟨1449582, by rfl⟩ : syracuseStep 3865553 = 2899165) B2899165
theorem B2292689 : Blo 1526460 2292689 := bstep (se 2 (by rfl) ⟨859758, by rfl⟩ : syracuseStep 2292689 = 1719517) B1719517
theorem B2898929 : Blo 1526460 2898929 := bstep (se 2 (by rfl) ⟨1087098, by rfl⟩ : syracuseStep 2898929 = 2174197) B2174197
theorem B1932275 : Blo 1526460 1932275 := bstep (se 1 (by rfl) ⟨1449206, by rfl⟩ : syracuseStep 1932275 = 2898413) B2898413
theorem B1719283 : Blo 1526460 1719283 := bstep (se 1 (by rfl) ⟨1289462, by rfl⟩ : syracuseStep 1719283 = 2578925) B2578925
theorem B3865603 : Blo 1526460 3865603 := bstep (se 1 (by rfl) ⟨2899202, by rfl⟩ : syracuseStep 3865603 = 5798405) B5798405
theorem B7732259 : Blo 1526460 7732259 := bstep (se 1 (by rfl) ⟨5799194, by rfl⟩ : syracuseStep 7732259 = 11598389) B11598389
theorem B4643939 : Blo 1526460 4643939 := bstep (se 1 (by rfl) ⟨3482954, by rfl⟩ : syracuseStep 4643939 = 6965909) B6965909
theorem B1719427 : Blo 1526460 1719427 := bstep (se 1 (by rfl) ⟨1289570, by rfl⟩ : syracuseStep 1719427 = 2579141) B2579141
theorem B14670989 : Blo 1526460 14670989 := bstep (se 3 (by rfl) ⟨2750810, by rfl⟩ : syracuseStep 14670989 = 5501621) B5501621
theorem B8699021 : Blo 1526460 8699021 := bstep (se 3 (by rfl) ⟨1631066, by rfl⟩ : syracuseStep 8699021 = 3262133) B3262133
theorem B3865745 : Blo 1526460 3865745 := bstep (se 2 (by rfl) ⟨1449654, by rfl⟩ : syracuseStep 3865745 = 2899309) B2899309
theorem B9780401 : Blo 1526460 9780401 := bstep (se 2 (by rfl) ⟨3667650, by rfl⟩ : syracuseStep 9780401 = 7335301) B7335301
theorem B4349123 : Blo 1526460 4349123 := bstep (se 1 (by rfl) ⟨3261842, by rfl⟩ : syracuseStep 4349123 = 6523685) B6523685
theorem B2612449 : Blo 1526460 2612449 := bstep (se 2 (by rfl) ⟨979668, by rfl⟩ : syracuseStep 2612449 = 1959337) B1959337
theorem B49544419 : Blo 1526460 49544419 := bstep (se 1 (by rfl) ⟨37158314, by rfl⟩ : syracuseStep 49544419 = 74316629) B74316629
theorem B2612531 : Blo 1526460 2612531 := bstep (se 1 (by rfl) ⟨1959398, by rfl⟩ : syracuseStep 2612531 = 3918797) B3918797
theorem B2751907 : Blo 1526460 2751907 := bstep (se 1 (by rfl) ⟨2063930, by rfl⟩ : syracuseStep 2751907 = 4127861) B4127861
theorem B8256973 : Blo 1526460 8256973 := bstep (se 3 (by rfl) ⟨1548182, by rfl⟩ : syracuseStep 8256973 = 3096365) B3096365
theorem B2481683 : Blo 1526460 2481683 := bstep (se 1 (by rfl) ⟨1861262, by rfl⟩ : syracuseStep 2481683 = 3722525) B3722525
theorem B5152301 : Blo 1526460 5152301 := bstep (se 3 (by rfl) ⟨966056, by rfl⟩ : syracuseStep 5152301 = 1932113) B1932113
theorem B5152355 : Blo 1526460 5152355 := bstep (se 1 (by rfl) ⟨3864266, by rfl⟩ : syracuseStep 5152355 = 7728533) B7728533
theorem B4890253 : Blo 1526460 4890253 := bstep (se 3 (by rfl) ⟨916922, by rfl⟩ : syracuseStep 4890253 = 1833845) B1833845
theorem B1932979 : Blo 1526460 1932979 := bstep (se 1 (by rfl) ⟨1449734, by rfl⟩ : syracuseStep 1932979 = 2899469) B2899469
theorem B2899651 : Blo 1526460 2899651 := bstep (se 1 (by rfl) ⟨2174738, by rfl⟩ : syracuseStep 2899651 = 4349477) B4349477
theorem B1933075 : Blo 1526460 1933075 := bstep (se 1 (by rfl) ⟨1449806, by rfl⟩ : syracuseStep 1933075 = 2899613) B2899613
theorem B7733069 : Blo 1526460 7733069 := bstep (se 3 (by rfl) ⟨1449950, by rfl⟩ : syracuseStep 7733069 = 2899901) B2899901
theorem B5152625 : Blo 1526460 5152625 := bstep (se 2 (by rfl) ⟨1932234, by rfl⟩ : syracuseStep 5152625 = 3864469) B3864469
theorem B2613107 : Blo 1526460 2613107 := bstep (se 1 (by rfl) ⟨1959830, by rfl⟩ : syracuseStep 2613107 = 3919661) B3919661
theorem B1548163 : Blo 1526460 1548163 := bstep (se 1 (by rfl) ⟨1161122, by rfl⟩ : syracuseStep 1548163 = 2322245) B2322245
theorem B4890509 : Blo 1526460 4890509 := bstep (se 3 (by rfl) ⟨916970, by rfl⟩ : syracuseStep 4890509 = 1833941) B1833941
theorem B16744333 : Blo 1526460 16744333 := bstep (se 3 (by rfl) ⟨3139562, by rfl⟩ : syracuseStep 16744333 = 6279125) B6279125
theorem B29753315 : Blo 1526460 29753315 := bstep (se 1 (by rfl) ⟨22314986, by rfl⟩ : syracuseStep 29753315 = 44629973) B44629973
theorem B4349933 : Blo 1526460 4349933 := bstep (se 3 (by rfl) ⟨815612, by rfl⟩ : syracuseStep 4349933 = 1631225) B1631225
theorem B6193169 : Blo 1526460 6193169 := bstep (se 2 (by rfl) ⟨2322438, by rfl⟩ : syracuseStep 6193169 = 4644877) B4644877
theorem B49528853 : Blo 1526460 49528853 := bstep (se 6 (by rfl) ⟨1160832, by rfl⟩ : syracuseStep 49528853 = 2321665) B2321665
theorem B1933399 : Blo 1526460 1933399 := bstep (se 1 (by rfl) ⟨1450049, by rfl⟩ : syracuseStep 1933399 = 2900099) B2900099
theorem B9289829 : Blo 1526460 9289829 := bstep (se 4 (by rfl) ⟨870921, by rfl⟩ : syracuseStep 9289829 = 1741843) B1741843
theorem B1630315 : Blo 1526460 1630315 := bstep (se 1 (by rfl) ⟨1222736, by rfl⟩ : syracuseStep 1630315 = 2445473) B2445473
theorem B11157635 : Blo 1526460 11157635 := bstep (se 1 (by rfl) ⟨8368226, by rfl⟩ : syracuseStep 11157635 = 16736453) B16736453
theorem B13246615 : Blo 1526460 13246615 := bstep (se 1 (by rfl) ⟨9934961, by rfl⟩ : syracuseStep 13246615 = 19869923) B19869923
theorem B23527685 : Blo 1526460 23527685 := bstep (se 4 (by rfl) ⟨2205720, by rfl⟩ : syracuseStep 23527685 = 4411441) B4411441
theorem B41820533 : Blo 1526460 41820533 := bstep (se 5 (by rfl) ⟨1960337, by rfl⟩ : syracuseStep 41820533 = 3920675) B3920675
theorem B11600333 : Blo 1526460 11600333 := bstep (se 3 (by rfl) ⟨2175062, by rfl⟩ : syracuseStep 11600333 = 4350125) B4350125
theorem B2900441 : Blo 1526460 2900441 := bstep (se 2 (by rfl) ⟨1087665, by rfl⟩ : syracuseStep 2900441 = 2175331) B2175331
theorem B6193687 : Blo 1526460 6193687 := bstep (se 1 (by rfl) ⟨4645265, by rfl⟩ : syracuseStep 6193687 = 9290531) B9290531
theorem B3097111 : Blo 1526460 3097111 := bstep (se 1 (by rfl) ⟨2322833, by rfl⟩ : syracuseStep 3097111 = 4645667) B4645667
theorem B16515677 : Blo 1526460 16515677 := bstep (se 3 (by rfl) ⟨3096689, by rfl⟩ : syracuseStep 16515677 = 6193379) B6193379
theorem B7537283 : Blo 1526460 7537283 := bstep (se 1 (by rfl) ⟨5652962, by rfl⟩ : syracuseStep 7537283 = 11305925) B11305925
theorem B1835671 : Blo 1526460 1835671 := bstep (se 1 (by rfl) ⟨1376753, by rfl⟩ : syracuseStep 1835671 = 2753507) B2753507
theorem B2753291 : Blo 1526460 2753291 := bstep (se 1 (by rfl) ⟨2064968, by rfl⟩ : syracuseStep 2753291 = 4129937) B4129937
theorem B18834221 : Blo 1526460 18834221 := bstep (se 3 (by rfl) ⟨3531416, by rfl⟩ : syracuseStep 18834221 = 7062833) B7062833
theorem B4350809 : Blo 1526460 4350809 := bstep (se 2 (by rfl) ⟨1631553, by rfl⟩ : syracuseStep 4350809 = 3263107) B3263107
theorem B3261313 : Blo 1526460 3261313 := bstep (se 2 (by rfl) ⟨1222992, by rfl⟩ : syracuseStep 3261313 = 2445985) B2445985
theorem B5800835 : Blo 1526460 5800835 := bstep (se 1 (by rfl) ⟨4350626, by rfl⟩ : syracuseStep 5800835 = 8701253) B8701253
theorem B1934219 : Blo 1526460 1934219 := bstep (se 1 (by rfl) ⟨1450664, by rfl⟩ : syracuseStep 1934219 = 2901329) B2901329
theorem B11600819 : Blo 1526460 11600819 := bstep (se 1 (by rfl) ⟨8700614, by rfl⟩ : syracuseStep 11600819 = 17401229) B17401229
theorem B4891585 : Blo 1526460 4891585 := bstep (se 2 (by rfl) ⟨1834344, by rfl⟩ : syracuseStep 4891585 = 3668689) B3668689
theorem B5153867 : Blo 1526460 5153867 := bstep (se 1 (by rfl) ⟨3865400, by rfl⟩ : syracuseStep 5153867 = 7730801) B7730801
theorem B7734365 : Blo 1526460 7734365 := bstep (se 3 (by rfl) ⟨1450193, by rfl⟩ : syracuseStep 7734365 = 2900387) B2900387
theorem B6522029 : Blo 1526460 6522029 := bstep (se 3 (by rfl) ⟨1222880, by rfl⟩ : syracuseStep 6522029 = 2445761) B2445761
theorem B4891841 : Blo 1526460 4891841 := bstep (se 2 (by rfl) ⟨1834440, by rfl⟩ : syracuseStep 4891841 = 3668881) B3668881
theorem B3867851 : Blo 1526460 3867851 := bstep (se 1 (by rfl) ⟨2900888, by rfl⟩ : syracuseStep 3867851 = 5801777) B5801777
theorem B5801291 : Blo 1526460 5801291 := bstep (se 1 (by rfl) ⟨4350968, by rfl⟩ : syracuseStep 5801291 = 8701937) B8701937
theorem B5154137 : Blo 1526460 5154137 := bstep (se 2 (by rfl) ⟨1932801, by rfl⟩ : syracuseStep 5154137 = 3865603) B3865603
theorem B3483083 : Blo 1526460 3483083 := bstep (se 1 (by rfl) ⟨2612312, by rfl⟩ : syracuseStep 3483083 = 5224625) B5224625
theorem B9922009 : Blo 1526460 9922009 := bstep (se 2 (by rfl) ⟨3720753, by rfl⟩ : syracuseStep 9922009 = 7441507) B7441507
theorem B39142925 : Blo 1526460 39142925 := bstep (se 3 (by rfl) ⟨7339298, by rfl⟩ : syracuseStep 39142925 = 14678597) B14678597
theorem B5801489 : Blo 1526460 5801489 := bstep (se 2 (by rfl) ⟨2175558, by rfl⟩ : syracuseStep 5801489 = 4351117) B4351117
theorem B8701505 : Blo 1526460 8701505 := bstep (se 2 (by rfl) ⟨3263064, by rfl⟩ : syracuseStep 8701505 = 6526129) B6526129
theorem B22029893 : Blo 1526460 22029893 := bstep (se 4 (by rfl) ⟨2065302, by rfl⟩ : syracuseStep 22029893 = 4130605) B4130605
theorem B3483265 : Blo 1526460 3483265 := bstep (se 2 (by rfl) ⟨1306224, by rfl⟩ : syracuseStep 3483265 = 2612449) B2612449
theorem B6522713 : Blo 1526460 6522713 := bstep (se 2 (by rfl) ⟨2446017, by rfl⟩ : syracuseStep 6522713 = 4892035) B4892035
theorem B5875607 : Blo 1526460 5875607 := bstep (se 1 (by rfl) ⟨4406705, by rfl⟩ : syracuseStep 5875607 = 8813411) B8813411
theorem B5154839 : Blo 1526460 5154839 := bstep (se 1 (by rfl) ⟨3866129, by rfl⟩ : syracuseStep 5154839 = 7732259) B7732259
theorem B3434561 : Blo 1526460 3434561 := bstep (se 2 (by rfl) ⟨1287960, by rfl⟩ : syracuseStep 3434561 = 2575921) B2575921
theorem B16517195 : Blo 1526460 16517195 := bstep (se 1 (by rfl) ⟨12387896, by rfl⟩ : syracuseStep 16517195 = 24775793) B24775793
theorem B6195293 : Blo 1526460 6195293 := bstep (se 3 (by rfl) ⟨1161617, by rfl⟩ : syracuseStep 6195293 = 2323235) B2323235
theorem B3868823 : Blo 1526460 3868823 := bstep (se 1 (by rfl) ⟨2901617, by rfl⟩ : syracuseStep 3868823 = 5803235) B5803235
theorem B4352221 : Blo 1526460 4352221 := bstep (se 3 (by rfl) ⟨816041, by rfl⟩ : syracuseStep 4352221 = 1632083) B1632083
theorem B5507345 : Blo 1526460 5507345 := bstep (se 2 (by rfl) ⟨2065254, by rfl⟩ : syracuseStep 5507345 = 4130509) B4130509
theorem B5802263 : Blo 1526460 5802263 := bstep (se 1 (by rfl) ⟨4351697, by rfl⟩ : syracuseStep 5802263 = 8703395) B8703395
theorem B3434777 : Blo 1526460 3434777 := bstep (se 2 (by rfl) ⟨1288041, by rfl⟩ : syracuseStep 3434777 = 2576083) B2576083
theorem B6195521 : Blo 1526460 6195521 := bstep (se 2 (by rfl) ⟨2323320, by rfl⟩ : syracuseStep 6195521 = 4646641) B4646641
theorem B11602277 : Blo 1526460 11602277 := bstep (se 4 (by rfl) ⟨1087713, by rfl⟩ : syracuseStep 11602277 = 2175427) B2175427
theorem B3434867 : Blo 1526460 3434867 := bstep (se 1 (by rfl) ⟨2576150, by rfl⟩ : syracuseStep 3434867 = 5152301) B5152301
theorem B33499541 : Blo 1526460 33499541 := bstep (se 6 (by rfl) ⟨785145, by rfl⟩ : syracuseStep 33499541 = 1570291) B1570291
theorem B3434903 : Blo 1526460 3434903 := bstep (se 1 (by rfl) ⟨2576177, by rfl⟩ : syracuseStep 3434903 = 5152355) B5152355
theorem B6195649 : Blo 1526460 6195649 := bstep (se 2 (by rfl) ⟨2323368, by rfl⟩ : syracuseStep 6195649 = 4646737) B4646737
theorem B4352449 : Blo 1526460 4352449 := bstep (se 2 (by rfl) ⟨1632168, by rfl⟩ : syracuseStep 4352449 = 3264337) B3264337
theorem B5802461 : Blo 1526460 5802461 := bstep (se 3 (by rfl) ⟨1087961, by rfl⟩ : syracuseStep 5802461 = 2175923) B2175923
theorem B22325777 : Blo 1526460 22325777 := bstep (se 2 (by rfl) ⟨8372166, by rfl⟩ : syracuseStep 22325777 = 16744333) B16744333
theorem B5155379 : Blo 1526460 5155379 := bstep (se 1 (by rfl) ⟨3866534, by rfl⟩ : syracuseStep 5155379 = 7733069) B7733069
theorem B3435083 : Blo 1526460 3435083 := bstep (se 1 (by rfl) ⟨2576312, by rfl⟩ : syracuseStep 3435083 = 5152625) B5152625
theorem B3435137 : Blo 1526460 3435137 := bstep (se 2 (by rfl) ⟨1288176, by rfl⟩ : syracuseStep 3435137 = 2576353) B2576353
theorem B19835543 : Blo 1526460 19835543 := bstep (se 1 (by rfl) ⟨14876657, by rfl⟩ : syracuseStep 19835543 = 29753315) B29753315
theorem B1526475 : Blo 1526460 1526475 := bstep (se 1 (by rfl) ⟨1144856, by rfl⟩ : syracuseStep 1526475 = 2289713) B2289713
theorem B1526487 : Blo 1526460 1526487 := bstep (se 1 (by rfl) ⟨1144865, by rfl⟩ : syracuseStep 1526487 = 2289731) B2289731
theorem B7842521 : Blo 1526460 7842521 := bstep (se 2 (by rfl) ⟨2940945, by rfl⟩ : syracuseStep 7842521 = 5881891) B5881891
theorem B1526507 : Blo 1526460 1526507 := bstep (se 1 (by rfl) ⟨1144880, by rfl⟩ : syracuseStep 1526507 = 2289761) B2289761
theorem B1526519 : Blo 1526460 1526519 := bstep (se 1 (by rfl) ⟨1144889, by rfl⟩ : syracuseStep 1526519 = 2289779) B2289779
theorem B11594501 : Blo 1526460 11594501 := bstep (se 4 (by rfl) ⟨1086984, by rfl⟩ : syracuseStep 11594501 = 2173969) B2173969
theorem B1526539 : Blo 1526460 1526539 := bstep (se 1 (by rfl) ⟨1144904, by rfl⟩ : syracuseStep 1526539 = 2289809) B2289809
theorem B1526551 : Blo 1526460 1526551 := bstep (se 1 (by rfl) ⟨1144913, by rfl⟩ : syracuseStep 1526551 = 2289827) B2289827
theorem B1526571 : Blo 1526460 1526571 := bstep (se 1 (by rfl) ⟨1144928, by rfl⟩ : syracuseStep 1526571 = 2289857) B2289857
theorem B1526583 : Blo 1526460 1526583 := bstep (se 1 (by rfl) ⟨1144937, by rfl⟩ : syracuseStep 1526583 = 2289875) B2289875
theorem B57256769 : Blo 1526460 57256769 := bstep (se 2 (by rfl) ⟨21471288, by rfl⟩ : syracuseStep 57256769 = 42942577) B42942577
theorem B5155649 : Blo 1526460 5155649 := bstep (se 2 (by rfl) ⟨1933368, by rfl⟩ : syracuseStep 5155649 = 3866737) B3866737
theorem B7342913 : Blo 1526460 7342913 := bstep (se 2 (by rfl) ⟨2753592, by rfl⟩ : syracuseStep 7342913 = 5507185) B5507185
theorem B1526603 : Blo 1526460 1526603 := bstep (se 1 (by rfl) ⟨1144952, by rfl⟩ : syracuseStep 1526603 = 2289905) B2289905
theorem B11602763 : Blo 1526460 11602763 := bstep (se 1 (by rfl) ⟨8702072, by rfl⟩ : syracuseStep 11602763 = 17404145) B17404145
theorem B1526615 : Blo 1526460 1526615 := bstep (se 1 (by rfl) ⟨1144961, by rfl⟩ : syracuseStep 1526615 = 2289923) B2289923
theorem B3435353 : Blo 1526460 3435353 := bstep (se 2 (by rfl) ⟨1288257, by rfl⟩ : syracuseStep 3435353 = 2576515) B2576515
theorem B1526635 : Blo 1526460 1526635 := bstep (se 1 (by rfl) ⟨1144976, by rfl⟩ : syracuseStep 1526635 = 2289953) B2289953
theorem B1526647 : Blo 1526460 1526647 := bstep (se 1 (by rfl) ⟨1144985, by rfl⟩ : syracuseStep 1526647 = 2289971) B2289971
theorem B1526667 : Blo 1526460 1526667 := bstep (se 1 (by rfl) ⟨1145000, by rfl⟩ : syracuseStep 1526667 = 2290001) B2290001
theorem B1526679 : Blo 1526460 1526679 := bstep (se 1 (by rfl) ⟨1145009, by rfl⟩ : syracuseStep 1526679 = 2290019) B2290019
theorem B1526699 : Blo 1526460 1526699 := bstep (se 1 (by rfl) ⟨1145024, by rfl⟩ : syracuseStep 1526699 = 2290049) B2290049
theorem B3435443 : Blo 1526460 3435443 := bstep (se 1 (by rfl) ⟨2576582, by rfl⟩ : syracuseStep 3435443 = 5153165) B5153165
theorem B1526711 : Blo 1526460 1526711 := bstep (se 1 (by rfl) ⟨1145033, by rfl⟩ : syracuseStep 1526711 = 2290067) B2290067
theorem B1526731 : Blo 1526460 1526731 := bstep (se 1 (by rfl) ⟨1145048, by rfl⟩ : syracuseStep 1526731 = 2290097) B2290097
theorem B1526743 : Blo 1526460 1526743 := bstep (se 1 (by rfl) ⟨1145057, by rfl⟩ : syracuseStep 1526743 = 2290115) B2290115
theorem B3435479 : Blo 1526460 3435479 := bstep (se 1 (by rfl) ⟨2576609, by rfl⟩ : syracuseStep 3435479 = 5153219) B5153219
theorem B3263449 : Blo 1526460 3263449 := bstep (se 2 (by rfl) ⟨1223793, by rfl⟩ : syracuseStep 3263449 = 2447587) B2447587
theorem B1526763 : Blo 1526460 1526763 := bstep (se 1 (by rfl) ⟨1145072, by rfl⟩ : syracuseStep 1526763 = 2290145) B2290145
theorem B1526775 : Blo 1526460 1526775 := bstep (se 1 (by rfl) ⟨1145081, by rfl⟩ : syracuseStep 1526775 = 2290163) B2290163
theorem B1526795 : Blo 1526460 1526795 := bstep (se 1 (by rfl) ⟨1145096, by rfl⟩ : syracuseStep 1526795 = 2290193) B2290193
theorem B1526807 : Blo 1526460 1526807 := bstep (se 1 (by rfl) ⟨1145105, by rfl⟩ : syracuseStep 1526807 = 2290211) B2290211
theorem B1526827 : Blo 1526460 1526827 := bstep (se 1 (by rfl) ⟨1145120, by rfl⟩ : syracuseStep 1526827 = 2290241) B2290241
theorem B1526839 : Blo 1526460 1526839 := bstep (se 1 (by rfl) ⟨1145129, by rfl⟩ : syracuseStep 1526839 = 2290259) B2290259
theorem B1526859 : Blo 1526460 1526859 := bstep (se 1 (by rfl) ⟨1145144, by rfl⟩ : syracuseStep 1526859 = 2290289) B2290289
theorem B1526871 : Blo 1526460 1526871 := bstep (se 1 (by rfl) ⟨1145153, by rfl⟩ : syracuseStep 1526871 = 2290307) B2290307
theorem B1526891 : Blo 1526460 1526891 := bstep (se 1 (by rfl) ⟨1145168, by rfl⟩ : syracuseStep 1526891 = 2290337) B2290337
theorem B1526903 : Blo 1526460 1526903 := bstep (se 1 (by rfl) ⟨1145177, by rfl⟩ : syracuseStep 1526903 = 2290355) B2290355
theorem B1526923 : Blo 1526460 1526923 := bstep (se 1 (by rfl) ⟨1145192, by rfl⟩ : syracuseStep 1526923 = 2290385) B2290385
theorem B3435659 : Blo 1526460 3435659 := bstep (se 1 (by rfl) ⟨2576744, by rfl⟩ : syracuseStep 3435659 = 5153489) B5153489
theorem B1526935 : Blo 1526460 1526935 := bstep (se 1 (by rfl) ⟨1145201, by rfl⟩ : syracuseStep 1526935 = 2290403) B2290403
theorem B7736471 : Blo 1526460 7736471 := bstep (se 1 (by rfl) ⟨5802353, by rfl⟩ : syracuseStep 7736471 = 11604707) B11604707
theorem B2354329 : Blo 1526460 2354329 := bstep (se 2 (by rfl) ⟨882873, by rfl⟩ : syracuseStep 2354329 = 1765747) B1765747
theorem B1526955 : Blo 1526460 1526955 := bstep (se 1 (by rfl) ⟨1145216, by rfl⟩ : syracuseStep 1526955 = 2290433) B2290433
theorem B5508269 : Blo 1526460 5508269 := bstep (se 3 (by rfl) ⟨1032800, by rfl⟩ : syracuseStep 5508269 = 2065601) B2065601
theorem B1526967 : Blo 1526460 1526967 := bstep (se 1 (by rfl) ⟨1145225, by rfl⟩ : syracuseStep 1526967 = 2290451) B2290451
theorem B3435713 : Blo 1526460 3435713 := bstep (se 2 (by rfl) ⟨1288392, by rfl⟩ : syracuseStep 3435713 = 2576785) B2576785
theorem B1526987 : Blo 1526460 1526987 := bstep (se 1 (by rfl) ⟨1145240, by rfl⟩ : syracuseStep 1526987 = 2290481) B2290481
theorem B1526999 : Blo 1526460 1526999 := bstep (se 1 (by rfl) ⟨1145249, by rfl⟩ : syracuseStep 1526999 = 2290499) B2290499
theorem B11005145 : Blo 1526460 11005145 := bstep (se 2 (by rfl) ⟨4126929, by rfl⟩ : syracuseStep 11005145 = 8253859) B8253859
theorem B1527019 : Blo 1526460 1527019 := bstep (se 1 (by rfl) ⟨1145264, by rfl⟩ : syracuseStep 1527019 = 2290529) B2290529
theorem B1527031 : Blo 1526460 1527031 := bstep (se 1 (by rfl) ⟨1145273, by rfl⟩ : syracuseStep 1527031 = 2290547) B2290547
theorem B37145861 : Blo 1526460 37145861 := bstep (se 4 (by rfl) ⟨3482424, by rfl⟩ : syracuseStep 37145861 = 6964849) B6964849
theorem B1527051 : Blo 1526460 1527051 := bstep (se 1 (by rfl) ⟨1145288, by rfl⟩ : syracuseStep 1527051 = 2290577) B2290577
theorem B1527063 : Blo 1526460 1527063 := bstep (se 1 (by rfl) ⟨1145297, by rfl⟩ : syracuseStep 1527063 = 2290595) B2290595
theorem B1527083 : Blo 1526460 1527083 := bstep (se 1 (by rfl) ⟨1145312, by rfl⟩ : syracuseStep 1527083 = 2290625) B2290625
theorem B12553517 : Blo 1526460 12553517 := bstep (se 3 (by rfl) ⟨2353784, by rfl⟩ : syracuseStep 12553517 = 4707569) B4707569
theorem B1527095 : Blo 1526460 1527095 := bstep (se 1 (by rfl) ⟨1145321, by rfl⟩ : syracuseStep 1527095 = 2290643) B2290643
theorem B1527115 : Blo 1526460 1527115 := bstep (se 1 (by rfl) ⟨1145336, by rfl⟩ : syracuseStep 1527115 = 2290673) B2290673
theorem B1527127 : Blo 1526460 1527127 := bstep (se 1 (by rfl) ⟨1145345, by rfl⟩ : syracuseStep 1527127 = 2290691) B2290691
theorem B5156189 : Blo 1526460 5156189 := bstep (se 3 (by rfl) ⟨966785, by rfl⟩ : syracuseStep 5156189 = 1933571) B1933571
theorem B1527147 : Blo 1526460 1527147 := bstep (se 1 (by rfl) ⟨1145360, by rfl⟩ : syracuseStep 1527147 = 2290721) B2290721
theorem B1527159 : Blo 1526460 1527159 := bstep (se 1 (by rfl) ⟨1145369, by rfl⟩ : syracuseStep 1527159 = 2290739) B2290739
theorem B1527179 : Blo 1526460 1527179 := bstep (se 1 (by rfl) ⟨1145384, by rfl⟩ : syracuseStep 1527179 = 2290769) B2290769
theorem B1527191 : Blo 1526460 1527191 := bstep (se 1 (by rfl) ⟨1145393, by rfl⟩ : syracuseStep 1527191 = 2290787) B2290787
theorem B3435929 : Blo 1526460 3435929 := bstep (se 2 (by rfl) ⟨1288473, by rfl⟩ : syracuseStep 3435929 = 2576947) B2576947
theorem B1527211 : Blo 1526460 1527211 := bstep (se 1 (by rfl) ⟨1145408, by rfl⟩ : syracuseStep 1527211 = 2290817) B2290817
theorem B1527223 : Blo 1526460 1527223 := bstep (se 1 (by rfl) ⟨1145417, by rfl⟩ : syracuseStep 1527223 = 2290835) B2290835
theorem B1527243 : Blo 1526460 1527243 := bstep (se 1 (by rfl) ⟨1145432, by rfl⟩ : syracuseStep 1527243 = 2290865) B2290865
theorem B1527255 : Blo 1526460 1527255 := bstep (se 1 (by rfl) ⟨1145441, by rfl⟩ : syracuseStep 1527255 = 2290883) B2290883
theorem B6966749 : Blo 1526460 6966749 := bstep (se 3 (by rfl) ⟨1306265, by rfl⟩ : syracuseStep 6966749 = 2612531) B2612531
theorem B1527275 : Blo 1526460 1527275 := bstep (se 1 (by rfl) ⟨1145456, by rfl⟩ : syracuseStep 1527275 = 2290913) B2290913
theorem B3436019 : Blo 1526460 3436019 := bstep (se 1 (by rfl) ⟨2577014, by rfl⟩ : syracuseStep 3436019 = 5154029) B5154029
theorem B1527287 : Blo 1526460 1527287 := bstep (se 1 (by rfl) ⟨1145465, by rfl⟩ : syracuseStep 1527287 = 2290931) B2290931
theorem B1527307 : Blo 1526460 1527307 := bstep (se 1 (by rfl) ⟨1145480, by rfl⟩ : syracuseStep 1527307 = 2290961) B2290961
theorem B3436055 : Blo 1526460 3436055 := bstep (se 1 (by rfl) ⟨2577041, by rfl⟩ : syracuseStep 3436055 = 5154083) B5154083
theorem B1527319 : Blo 1526460 1527319 := bstep (se 1 (by rfl) ⟨1145489, by rfl⟩ : syracuseStep 1527319 = 2290979) B2290979
theorem B1527339 : Blo 1526460 1527339 := bstep (se 1 (by rfl) ⟨1145504, by rfl⟩ : syracuseStep 1527339 = 2291009) B2291009
theorem B1527351 : Blo 1526460 1527351 := bstep (se 1 (by rfl) ⟨1145513, by rfl⟩ : syracuseStep 1527351 = 2291027) B2291027
theorem B12381761 : Blo 1526460 12381761 := bstep (se 2 (by rfl) ⟨4643160, by rfl⟩ : syracuseStep 12381761 = 9286321) B9286321
theorem B2174539 : Blo 1526460 2174539 := bstep (se 1 (by rfl) ⟨1630904, by rfl⟩ : syracuseStep 2174539 = 3261809) B3261809
theorem B1527371 : Blo 1526460 1527371 := bstep (se 1 (by rfl) ⟨1145528, by rfl⟩ : syracuseStep 1527371 = 2291057) B2291057
theorem B1527383 : Blo 1526460 1527383 := bstep (se 1 (by rfl) ⟨1145537, by rfl⟩ : syracuseStep 1527383 = 2291075) B2291075
theorem B4894301 : Blo 1526460 4894301 := bstep (se 3 (by rfl) ⟨917681, by rfl⟩ : syracuseStep 4894301 = 1835363) B1835363
theorem B1527403 : Blo 1526460 1527403 := bstep (se 1 (by rfl) ⟨1145552, by rfl⟩ : syracuseStep 1527403 = 2291105) B2291105
theorem B1527415 : Blo 1526460 1527415 := bstep (se 1 (by rfl) ⟨1145561, by rfl⟩ : syracuseStep 1527415 = 2291123) B2291123
theorem B1527435 : Blo 1526460 1527435 := bstep (se 1 (by rfl) ⟨1145576, by rfl⟩ : syracuseStep 1527435 = 2291153) B2291153
theorem B1527447 : Blo 1526460 1527447 := bstep (se 1 (by rfl) ⟨1145585, by rfl⟩ : syracuseStep 1527447 = 2291171) B2291171
theorem B1527467 : Blo 1526460 1527467 := bstep (se 1 (by rfl) ⟨1145600, by rfl⟩ : syracuseStep 1527467 = 2291201) B2291201
theorem B9285299 : Blo 1526460 9285299 := bstep (se 1 (by rfl) ⟨6963974, by rfl⟩ : syracuseStep 9285299 = 13927949) B13927949
theorem B1527479 : Blo 1526460 1527479 := bstep (se 1 (by rfl) ⟨1145609, by rfl⟩ : syracuseStep 1527479 = 2291219) B2291219
theorem B3436235 : Blo 1526460 3436235 := bstep (se 1 (by rfl) ⟨2577176, by rfl⟩ : syracuseStep 3436235 = 5154353) B5154353
theorem B1527499 : Blo 1526460 1527499 := bstep (se 1 (by rfl) ⟨1145624, by rfl⟩ : syracuseStep 1527499 = 2291249) B2291249
theorem B1527511 : Blo 1526460 1527511 := bstep (se 1 (by rfl) ⟨1145633, by rfl⟩ : syracuseStep 1527511 = 2291267) B2291267
theorem B7728857 : Blo 1526460 7728857 := bstep (se 2 (by rfl) ⟨2898321, by rfl⟩ : syracuseStep 7728857 = 5796643) B5796643
theorem B1527531 : Blo 1526460 1527531 := bstep (se 1 (by rfl) ⟨1145648, by rfl⟩ : syracuseStep 1527531 = 2291297) B2291297
theorem B1527543 : Blo 1526460 1527543 := bstep (se 1 (by rfl) ⟨1145657, by rfl⟩ : syracuseStep 1527543 = 2291315) B2291315
theorem B3436289 : Blo 1526460 3436289 := bstep (se 2 (by rfl) ⟨1288608, by rfl⟩ : syracuseStep 3436289 = 2577217) B2577217
theorem B1527563 : Blo 1526460 1527563 := bstep (se 1 (by rfl) ⟨1145672, by rfl⟩ : syracuseStep 1527563 = 2291345) B2291345
theorem B1527575 : Blo 1526460 1527575 := bstep (se 1 (by rfl) ⟨1145681, by rfl⟩ : syracuseStep 1527575 = 2291363) B2291363
theorem B1527595 : Blo 1526460 1527595 := bstep (se 1 (by rfl) ⟨1145696, by rfl⟩ : syracuseStep 1527595 = 2291393) B2291393
theorem B1527607 : Blo 1526460 1527607 := bstep (se 1 (by rfl) ⟨1145705, by rfl⟩ : syracuseStep 1527607 = 2291411) B2291411
theorem B1527627 : Blo 1526460 1527627 := bstep (se 1 (by rfl) ⟨1145720, by rfl⟩ : syracuseStep 1527627 = 2291441) B2291441
theorem B1527639 : Blo 1526460 1527639 := bstep (se 1 (by rfl) ⟨1145729, by rfl⟩ : syracuseStep 1527639 = 2291459) B2291459
theorem B1527659 : Blo 1526460 1527659 := bstep (se 1 (by rfl) ⟨1145744, by rfl⟩ : syracuseStep 1527659 = 2291489) B2291489
theorem B1527671 : Blo 1526460 1527671 := bstep (se 1 (by rfl) ⟨1145753, by rfl⟩ : syracuseStep 1527671 = 2291507) B2291507
theorem B1527691 : Blo 1526460 1527691 := bstep (se 1 (by rfl) ⟨1145768, by rfl⟩ : syracuseStep 1527691 = 2291537) B2291537
theorem B2576279 : Blo 1526460 2576279 := bstep (se 1 (by rfl) ⟨1932209, by rfl⟩ : syracuseStep 2576279 = 3864419) B3864419
theorem B1527703 : Blo 1526460 1527703 := bstep (se 1 (by rfl) ⟨1145777, by rfl⟩ : syracuseStep 1527703 = 2291555) B2291555
theorem B8703895 : Blo 1526460 8703895 := bstep (se 1 (by rfl) ⟨6527921, by rfl⟩ : syracuseStep 8703895 = 13055843) B13055843
theorem B1527723 : Blo 1526460 1527723 := bstep (se 1 (by rfl) ⟨1145792, by rfl⟩ : syracuseStep 1527723 = 2291585) B2291585
theorem B1527735 : Blo 1526460 1527735 := bstep (se 1 (by rfl) ⟨1145801, by rfl⟩ : syracuseStep 1527735 = 2291603) B2291603
theorem B1527755 : Blo 1526460 1527755 := bstep (se 1 (by rfl) ⟨1145816, by rfl⟩ : syracuseStep 1527755 = 2291633) B2291633
theorem B1527767 : Blo 1526460 1527767 := bstep (se 1 (by rfl) ⟨1145825, by rfl⟩ : syracuseStep 1527767 = 2291651) B2291651
theorem B3436505 : Blo 1526460 3436505 := bstep (se 2 (by rfl) ⟨1288689, by rfl⟩ : syracuseStep 3436505 = 2577379) B2577379
theorem B1527787 : Blo 1526460 1527787 := bstep (se 1 (by rfl) ⟨1145840, by rfl⟩ : syracuseStep 1527787 = 2291681) B2291681
theorem B1527799 : Blo 1526460 1527799 := bstep (se 1 (by rfl) ⟨1145849, by rfl⟩ : syracuseStep 1527799 = 2291699) B2291699
theorem B1527819 : Blo 1526460 1527819 := bstep (se 1 (by rfl) ⟨1145864, by rfl⟩ : syracuseStep 1527819 = 2291729) B2291729
theorem B2576407 : Blo 1526460 2576407 := bstep (se 1 (by rfl) ⟨1932305, by rfl⟩ : syracuseStep 2576407 = 3864611) B3864611
theorem B1527831 : Blo 1526460 1527831 := bstep (se 1 (by rfl) ⟨1145873, by rfl⟩ : syracuseStep 1527831 = 2291747) B2291747
theorem B1527851 : Blo 1526460 1527851 := bstep (se 1 (by rfl) ⟨1145888, by rfl⟩ : syracuseStep 1527851 = 2291777) B2291777
theorem B3436595 : Blo 1526460 3436595 := bstep (se 1 (by rfl) ⟨2577446, by rfl⟩ : syracuseStep 3436595 = 5154893) B5154893
theorem B1527863 : Blo 1526460 1527863 := bstep (se 1 (by rfl) ⟨1145897, by rfl⟩ : syracuseStep 1527863 = 2291795) B2291795
theorem B1527883 : Blo 1526460 1527883 := bstep (se 1 (by rfl) ⟨1145912, by rfl⟩ : syracuseStep 1527883 = 2291825) B2291825
theorem B3436631 : Blo 1526460 3436631 := bstep (se 1 (by rfl) ⟨2577473, by rfl⟩ : syracuseStep 3436631 = 5154947) B5154947
theorem B1527895 : Blo 1526460 1527895 := bstep (se 1 (by rfl) ⟨1145921, by rfl⟩ : syracuseStep 1527895 = 2291843) B2291843
theorem B1527915 : Blo 1526460 1527915 := bstep (se 1 (by rfl) ⟨1145936, by rfl⟩ : syracuseStep 1527915 = 2291873) B2291873
theorem B1527927 : Blo 1526460 1527927 := bstep (se 1 (by rfl) ⟨1145945, by rfl⟩ : syracuseStep 1527927 = 2291891) B2291891
theorem B2289803 : Blo 1526460 2289803 := bstep (se 1 (by rfl) ⟨1717352, by rfl⟩ : syracuseStep 2289803 = 3434705) B3434705
theorem B1527947 : Blo 1526460 1527947 := bstep (se 1 (by rfl) ⟨1145960, by rfl⟩ : syracuseStep 1527947 = 2291921) B2291921
theorem B2289815 : Blo 1526460 2289815 := bstep (se 1 (by rfl) ⟨1717361, by rfl⟩ : syracuseStep 2289815 = 3434723) B3434723
theorem B39669911 : Blo 1526460 39669911 := bstep (se 1 (by rfl) ⟨29752433, by rfl⟩ : syracuseStep 39669911 = 59504867) B59504867
theorem B1527959 : Blo 1526460 1527959 := bstep (se 1 (by rfl) ⟨1145969, by rfl⟩ : syracuseStep 1527959 = 2291939) B2291939
theorem B1527979 : Blo 1526460 1527979 := bstep (se 1 (by rfl) ⟨1145984, by rfl⟩ : syracuseStep 1527979 = 2291969) B2291969
theorem B1527991 : Blo 1526460 1527991 := bstep (se 1 (by rfl) ⟨1145993, by rfl⟩ : syracuseStep 1527991 = 2291987) B2291987
theorem B1528011 : Blo 1526460 1528011 := bstep (se 1 (by rfl) ⟨1146008, by rfl⟩ : syracuseStep 1528011 = 2292017) B2292017
theorem B1528023 : Blo 1526460 1528023 := bstep (se 1 (by rfl) ⟨1146017, by rfl⟩ : syracuseStep 1528023 = 2292035) B2292035
theorem B2289881 : Blo 1526460 2289881 := bstep (se 2 (by rfl) ⟨858705, by rfl⟩ : syracuseStep 2289881 = 1717411) B1717411
theorem B1528043 : Blo 1526460 1528043 := bstep (se 1 (by rfl) ⟨1146032, by rfl⟩ : syracuseStep 1528043 = 2292065) B2292065
theorem B1528055 : Blo 1526460 1528055 := bstep (se 1 (by rfl) ⟨1146041, by rfl⟩ : syracuseStep 1528055 = 2292083) B2292083
theorem B3436811 : Blo 1526460 3436811 := bstep (se 1 (by rfl) ⟨2577608, by rfl⟩ : syracuseStep 3436811 = 5155217) B5155217
theorem B1528075 : Blo 1526460 1528075 := bstep (se 1 (by rfl) ⟨1146056, by rfl⟩ : syracuseStep 1528075 = 2292113) B2292113
theorem B1528087 : Blo 1526460 1528087 := bstep (se 1 (by rfl) ⟨1146065, by rfl⟩ : syracuseStep 1528087 = 2292131) B2292131
theorem B1741099 : Blo 1526460 1741099 := bstep (se 1 (by rfl) ⟨1305824, by rfl⟩ : syracuseStep 1741099 = 2611649) B2611649
theorem B1528107 : Blo 1526460 1528107 := bstep (se 1 (by rfl) ⟨1146080, by rfl⟩ : syracuseStep 1528107 = 2292161) B2292161
theorem B1528119 : Blo 1526460 1528119 := bstep (se 1 (by rfl) ⟨1146089, by rfl⟩ : syracuseStep 1528119 = 2292179) B2292179
theorem B3436865 : Blo 1526460 3436865 := bstep (se 2 (by rfl) ⟨1288824, by rfl⟩ : syracuseStep 3436865 = 2577649) B2577649
theorem B2289995 : Blo 1526460 2289995 := bstep (se 1 (by rfl) ⟨1717496, by rfl⟩ : syracuseStep 2289995 = 3434993) B3434993
theorem B1528139 : Blo 1526460 1528139 := bstep (se 1 (by rfl) ⟨1146104, by rfl⟩ : syracuseStep 1528139 = 2292209) B2292209
theorem B2290007 : Blo 1526460 2290007 := bstep (se 1 (by rfl) ⟨1717505, by rfl⟩ : syracuseStep 2290007 = 3435011) B3435011
theorem B1528151 : Blo 1526460 1528151 := bstep (se 1 (by rfl) ⟨1146113, by rfl⟩ : syracuseStep 1528151 = 2292227) B2292227
theorem B1528171 : Blo 1526460 1528171 := bstep (se 1 (by rfl) ⟨1146128, by rfl⟩ : syracuseStep 1528171 = 2292257) B2292257
theorem B1528183 : Blo 1526460 1528183 := bstep (se 1 (by rfl) ⟨1146137, by rfl⟩ : syracuseStep 1528183 = 2292275) B2292275
theorem B1528203 : Blo 1526460 1528203 := bstep (se 1 (by rfl) ⟨1146152, by rfl⟩ : syracuseStep 1528203 = 2292305) B2292305
theorem B1528215 : Blo 1526460 1528215 := bstep (se 1 (by rfl) ⟨1146161, by rfl⟩ : syracuseStep 1528215 = 2292323) B2292323
theorem B2290073 : Blo 1526460 2290073 := bstep (se 2 (by rfl) ⟨858777, by rfl⟩ : syracuseStep 2290073 = 1717555) B1717555
theorem B1528235 : Blo 1526460 1528235 := bstep (se 1 (by rfl) ⟨1146176, by rfl⟩ : syracuseStep 1528235 = 2292353) B2292353
theorem B11006387 : Blo 1526460 11006387 := bstep (se 1 (by rfl) ⟨8254790, by rfl⟩ : syracuseStep 11006387 = 16509581) B16509581
theorem B1528247 : Blo 1526460 1528247 := bstep (se 1 (by rfl) ⟨1146185, by rfl⟩ : syracuseStep 1528247 = 2292371) B2292371
theorem B5157323 : Blo 1526460 5157323 := bstep (se 1 (by rfl) ⟨3867992, by rfl⟩ : syracuseStep 5157323 = 7735985) B7735985
theorem B1528267 : Blo 1526460 1528267 := bstep (se 1 (by rfl) ⟨1146200, by rfl⟩ : syracuseStep 1528267 = 2292401) B2292401
theorem B1528279 : Blo 1526460 1528279 := bstep (se 1 (by rfl) ⟨1146209, by rfl⟩ : syracuseStep 1528279 = 2292419) B2292419
theorem B1528299 : Blo 1526460 1528299 := bstep (se 1 (by rfl) ⟨1146224, by rfl⟩ : syracuseStep 1528299 = 2292449) B2292449
theorem B1528311 : Blo 1526460 1528311 := bstep (se 1 (by rfl) ⟨1146233, by rfl⟩ : syracuseStep 1528311 = 2292467) B2292467
theorem B2290187 : Blo 1526460 2290187 := bstep (se 1 (by rfl) ⟨1717640, by rfl⟩ : syracuseStep 2290187 = 3435281) B3435281
theorem B1528331 : Blo 1526460 1528331 := bstep (se 1 (by rfl) ⟨1146248, by rfl⟩ : syracuseStep 1528331 = 2292497) B2292497
theorem B2290199 : Blo 1526460 2290199 := bstep (se 1 (by rfl) ⟨1717649, by rfl⟩ : syracuseStep 2290199 = 3435299) B3435299
theorem B1528343 : Blo 1526460 1528343 := bstep (se 1 (by rfl) ⟨1146257, by rfl⟩ : syracuseStep 1528343 = 2292515) B2292515
theorem B3437081 : Blo 1526460 3437081 := bstep (se 2 (by rfl) ⟨1288905, by rfl⟩ : syracuseStep 3437081 = 2577811) B2577811
theorem B1528363 : Blo 1526460 1528363 := bstep (se 1 (by rfl) ⟨1146272, by rfl⟩ : syracuseStep 1528363 = 2292545) B2292545
theorem B1528375 : Blo 1526460 1528375 := bstep (se 1 (by rfl) ⟨1146281, by rfl⟩ : syracuseStep 1528375 = 2292563) B2292563
theorem B17388107 : Blo 1526460 17388107 := bstep (se 1 (by rfl) ⟨13041080, by rfl⟩ : syracuseStep 17388107 = 26082161) B26082161
theorem B1528395 : Blo 1526460 1528395 := bstep (se 1 (by rfl) ⟨1146296, by rfl⟩ : syracuseStep 1528395 = 2292593) B2292593
theorem B1528407 : Blo 1526460 1528407 := bstep (se 1 (by rfl) ⟨1146305, by rfl⟩ : syracuseStep 1528407 = 2292611) B2292611
theorem B2290265 : Blo 1526460 2290265 := bstep (se 2 (by rfl) ⟨858849, by rfl⟩ : syracuseStep 2290265 = 1717699) B1717699
theorem B1528427 : Blo 1526460 1528427 := bstep (se 1 (by rfl) ⟨1146320, by rfl⟩ : syracuseStep 1528427 = 2292641) B2292641
theorem B3437171 : Blo 1526460 3437171 := bstep (se 1 (by rfl) ⟨2577878, by rfl⟩ : syracuseStep 3437171 = 5155757) B5155757
theorem B1528439 : Blo 1526460 1528439 := bstep (se 1 (by rfl) ⟨1146329, by rfl⟩ : syracuseStep 1528439 = 2292659) B2292659
theorem B2577035 : Blo 1526460 2577035 := bstep (se 1 (by rfl) ⟨1932776, by rfl⟩ : syracuseStep 2577035 = 3865553) B3865553
theorem B1528459 : Blo 1526460 1528459 := bstep (se 1 (by rfl) ⟨1146344, by rfl⟩ : syracuseStep 1528459 = 2292689) B2292689
theorem B3437207 : Blo 1526460 3437207 := bstep (se 1 (by rfl) ⟨2577905, by rfl⟩ : syracuseStep 3437207 = 5155811) B5155811
theorem B2290379 : Blo 1526460 2290379 := bstep (se 1 (by rfl) ⟨1717784, by rfl⟩ : syracuseStep 2290379 = 3435569) B3435569
theorem B2290391 : Blo 1526460 2290391 := bstep (se 1 (by rfl) ⟨1717793, by rfl⟩ : syracuseStep 2290391 = 3435587) B3435587
theorem B5157593 : Blo 1526460 5157593 := bstep (se 2 (by rfl) ⟨1934097, by rfl⟩ : syracuseStep 5157593 = 3868195) B3868195
theorem B2577163 : Blo 1526460 2577163 := bstep (se 1 (by rfl) ⟨1932872, by rfl⟩ : syracuseStep 2577163 = 3865745) B3865745
theorem B2290457 : Blo 1526460 2290457 := bstep (se 2 (by rfl) ⟨858921, by rfl⟩ : syracuseStep 2290457 = 1717843) B1717843
theorem B2175769 : Blo 1526460 2175769 := bstep (se 2 (by rfl) ⟨815913, by rfl⟩ : syracuseStep 2175769 = 1631827) B1631827
theorem B2978635 : Blo 1526460 2978635 := bstep (se 1 (by rfl) ⟨2233976, by rfl⟩ : syracuseStep 2978635 = 4467953) B4467953
theorem B3437387 : Blo 1526460 3437387 := bstep (se 1 (by rfl) ⟨2578040, by rfl⟩ : syracuseStep 3437387 = 5156081) B5156081
theorem B3437441 : Blo 1526460 3437441 := bstep (se 2 (by rfl) ⟨1289040, by rfl⟩ : syracuseStep 3437441 = 2578081) B2578081
theorem B2290571 : Blo 1526460 2290571 := bstep (se 1 (by rfl) ⟨1717928, by rfl⟩ : syracuseStep 2290571 = 3435857) B3435857
theorem B2290583 : Blo 1526460 2290583 := bstep (se 1 (by rfl) ⟨1717937, by rfl⟩ : syracuseStep 2290583 = 3435875) B3435875
theorem B2577305 : Blo 1526460 2577305 := bstep (se 2 (by rfl) ⟨966489, by rfl⟩ : syracuseStep 2577305 = 1932979) B1932979
theorem B2290649 : Blo 1526460 2290649 := bstep (se 2 (by rfl) ⟨858993, by rfl⟩ : syracuseStep 2290649 = 1717987) B1717987
theorem B5501969 : Blo 1526460 5501969 := bstep (se 2 (by rfl) ⟨2063238, by rfl⟩ : syracuseStep 5501969 = 4126477) B4126477
theorem B2577433 : Blo 1526460 2577433 := bstep (se 2 (by rfl) ⟨966537, by rfl⟩ : syracuseStep 2577433 = 1933075) B1933075
theorem B1717303 : Blo 1526460 1717303 := bstep (se 1 (by rfl) ⟨1287977, by rfl⟩ : syracuseStep 1717303 = 2575955) B2575955
theorem B2290763 : Blo 1526460 2290763 := bstep (se 1 (by rfl) ⟨1718072, by rfl⟩ : syracuseStep 2290763 = 3436145) B3436145
theorem B2290775 : Blo 1526460 2290775 := bstep (se 1 (by rfl) ⟨1718081, by rfl⟩ : syracuseStep 2290775 = 3436163) B3436163
theorem B3437657 : Blo 1526460 3437657 := bstep (se 2 (by rfl) ⟨1289121, by rfl⟩ : syracuseStep 3437657 = 2578243) B2578243
theorem B8262749 : Blo 1526460 8262749 := bstep (se 3 (by rfl) ⟨1549265, by rfl⟩ : syracuseStep 8262749 = 3098531) B3098531
theorem B11596931 : Blo 1526460 11596931 := bstep (se 1 (by rfl) ⟨8697698, by rfl⟩ : syracuseStep 11596931 = 17395397) B17395397
theorem B2290841 : Blo 1526460 2290841 := bstep (se 2 (by rfl) ⟨859065, by rfl⟩ : syracuseStep 2290841 = 1718131) B1718131
theorem B3437747 : Blo 1526460 3437747 := bstep (se 1 (by rfl) ⟨2578310, by rfl⟩ : syracuseStep 3437747 = 5156621) B5156621
theorem B6526145 : Blo 1526460 6526145 := bstep (se 2 (by rfl) ⟨2447304, by rfl⟩ : syracuseStep 6526145 = 4894609) B4894609
theorem B3437783 : Blo 1526460 3437783 := bstep (se 1 (by rfl) ⟨2578337, by rfl⟩ : syracuseStep 3437783 = 5156675) B5156675
theorem B1717483 : Blo 1526460 1717483 := bstep (se 1 (by rfl) ⟨1288112, by rfl⟩ : syracuseStep 1717483 = 2576225) B2576225
theorem B1742071 : Blo 1526460 1742071 := bstep (se 1 (by rfl) ⟨1306553, by rfl⟩ : syracuseStep 1742071 = 2613107) B2613107
theorem B2290955 : Blo 1526460 2290955 := bstep (se 1 (by rfl) ⟨1718216, by rfl⟩ : syracuseStep 2290955 = 3436433) B3436433
theorem B2290967 : Blo 1526460 2290967 := bstep (se 1 (by rfl) ⟨1718225, by rfl⟩ : syracuseStep 2290967 = 3436451) B3436451
theorem B7730477 : Blo 1526460 7730477 := bstep (se 3 (by rfl) ⟨1449464, by rfl⟩ : syracuseStep 7730477 = 2898929) B2898929
theorem B1717591 : Blo 1526460 1717591 := bstep (se 1 (by rfl) ⟨1288193, by rfl⟩ : syracuseStep 1717591 = 2576387) B2576387
theorem B2291033 : Blo 1526460 2291033 := bstep (se 2 (by rfl) ⟨859137, by rfl⟩ : syracuseStep 2291033 = 1718275) B1718275
theorem B3437963 : Blo 1526460 3437963 := bstep (se 1 (by rfl) ⟨2578472, by rfl⟩ : syracuseStep 3437963 = 5156945) B5156945
theorem B5158295 : Blo 1526460 5158295 := bstep (se 1 (by rfl) ⟨3868721, by rfl⟩ : syracuseStep 5158295 = 7737443) B7737443
theorem B3438017 : Blo 1526460 3438017 := bstep (se 2 (by rfl) ⟨1289256, by rfl⟩ : syracuseStep 3438017 = 2578513) B2578513
theorem B2291147 : Blo 1526460 2291147 := bstep (se 1 (by rfl) ⟨1718360, by rfl⟩ : syracuseStep 2291147 = 3436721) B3436721
theorem B2291159 : Blo 1526460 2291159 := bstep (se 1 (by rfl) ⟨1718369, by rfl⟩ : syracuseStep 2291159 = 3436739) B3436739
theorem B1717771 : Blo 1526460 1717771 := bstep (se 1 (by rfl) ⟨1288328, by rfl⟩ : syracuseStep 1717771 = 2576657) B2576657
theorem B6526487 : Blo 1526460 6526487 := bstep (se 1 (by rfl) ⟨4894865, by rfl⟩ : syracuseStep 6526487 = 9789731) B9789731
theorem B2291225 : Blo 1526460 2291225 := bstep (se 2 (by rfl) ⟨859209, by rfl⟩ : syracuseStep 2291225 = 1718419) B1718419
theorem B2578007 : Blo 1526460 2578007 := bstep (se 1 (by rfl) ⟨1933505, by rfl⟩ : syracuseStep 2578007 = 3867011) B3867011
theorem B12383837 : Blo 1526460 12383837 := bstep (se 3 (by rfl) ⟨2321969, by rfl⟩ : syracuseStep 12383837 = 4643939) B4643939
theorem B1717879 : Blo 1526460 1717879 := bstep (se 1 (by rfl) ⟨1288409, by rfl⟩ : syracuseStep 1717879 = 2576819) B2576819
theorem B2291339 : Blo 1526460 2291339 := bstep (se 1 (by rfl) ⟨1718504, by rfl⟩ : syracuseStep 2291339 = 3437009) B3437009
theorem B2291351 : Blo 1526460 2291351 := bstep (se 1 (by rfl) ⟨1718513, by rfl⟩ : syracuseStep 2291351 = 3437027) B3437027
theorem B3438233 : Blo 1526460 3438233 := bstep (se 2 (by rfl) ⟨1289337, by rfl⟩ : syracuseStep 3438233 = 2578675) B2578675
theorem B3864257 : Blo 1526460 3864257 := bstep (se 2 (by rfl) ⟨1449096, by rfl⟩ : syracuseStep 3864257 = 2898193) B2898193
theorem B2578135 : Blo 1526460 2578135 := bstep (se 1 (by rfl) ⟨1933601, by rfl⟩ : syracuseStep 2578135 = 3867203) B3867203
theorem B2291417 : Blo 1526460 2291417 := bstep (se 2 (by rfl) ⟨859281, by rfl⟩ : syracuseStep 2291417 = 1718563) B1718563
theorem B3438323 : Blo 1526460 3438323 := bstep (se 1 (by rfl) ⟨2578742, by rfl⟩ : syracuseStep 3438323 = 5157485) B5157485
theorem B6616849 : Blo 1526460 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B3438359 : Blo 1526460 3438359 := bstep (se 1 (by rfl) ⟨2578769, by rfl⟩ : syracuseStep 3438359 = 5157539) B5157539
theorem B1718059 : Blo 1526460 1718059 := bstep (se 1 (by rfl) ⟨1288544, by rfl⟩ : syracuseStep 1718059 = 2577089) B2577089
theorem B2291531 : Blo 1526460 2291531 := bstep (se 1 (by rfl) ⟨1718648, by rfl⟩ : syracuseStep 2291531 = 3437297) B3437297
theorem B2291543 : Blo 1526460 2291543 := bstep (se 1 (by rfl) ⟨1718657, by rfl⟩ : syracuseStep 2291543 = 3437315) B3437315
theorem B44046179 : Blo 1526460 44046179 := bstep (se 1 (by rfl) ⟨33034634, by rfl⟩ : syracuseStep 44046179 = 66069269) B66069269
theorem B1718167 : Blo 1526460 1718167 := bstep (se 1 (by rfl) ⟨1288625, by rfl⟩ : syracuseStep 1718167 = 2577251) B2577251
theorem B2291609 : Blo 1526460 2291609 := bstep (se 2 (by rfl) ⟨859353, by rfl⟩ : syracuseStep 2291609 = 1718707) B1718707
theorem B3438539 : Blo 1526460 3438539 := bstep (se 1 (by rfl) ⟨2578904, by rfl⟩ : syracuseStep 3438539 = 5157809) B5157809
theorem B3438593 : Blo 1526460 3438593 := bstep (se 2 (by rfl) ⟨1289472, by rfl⟩ : syracuseStep 3438593 = 2578945) B2578945
theorem B2291723 : Blo 1526460 2291723 := bstep (se 1 (by rfl) ⟨1718792, by rfl⟩ : syracuseStep 2291723 = 3437585) B3437585
theorem B6969361 : Blo 1526460 6969361 := bstep (se 2 (by rfl) ⟨2613510, by rfl⟩ : syracuseStep 6969361 = 5227021) B5227021
theorem B2291735 : Blo 1526460 2291735 := bstep (se 1 (by rfl) ⟨1718801, by rfl⟩ : syracuseStep 2291735 = 3437603) B3437603
theorem B1718347 : Blo 1526460 1718347 := bstep (se 1 (by rfl) ⟨1288760, by rfl⟩ : syracuseStep 1718347 = 2577521) B2577521
theorem B2291801 : Blo 1526460 2291801 := bstep (se 2 (by rfl) ⟨859425, by rfl⟩ : syracuseStep 2291801 = 1718851) B1718851
theorem B3094679 : Blo 1526460 3094679 := bstep (se 1 (by rfl) ⟨2321009, by rfl⟩ : syracuseStep 3094679 = 4642019) B4642019
theorem B1718455 : Blo 1526460 1718455 := bstep (se 1 (by rfl) ⟨1288841, by rfl⟩ : syracuseStep 1718455 = 2577683) B2577683
theorem B2291915 : Blo 1526460 2291915 := bstep (se 1 (by rfl) ⟨1718936, by rfl⟩ : syracuseStep 2291915 = 3437873) B3437873
theorem B2291927 : Blo 1526460 2291927 := bstep (se 1 (by rfl) ⟨1718945, by rfl⟩ : syracuseStep 2291927 = 3437891) B3437891
theorem B3864793 : Blo 1526460 3864793 := bstep (se 2 (by rfl) ⟨1449297, by rfl⟩ : syracuseStep 3864793 = 2898595) B2898595
theorem B3438809 : Blo 1526460 3438809 := bstep (se 2 (by rfl) ⟨1289553, by rfl⟩ : syracuseStep 3438809 = 2579107) B2579107
theorem B2291993 : Blo 1526460 2291993 := bstep (se 2 (by rfl) ⟨859497, by rfl⟩ : syracuseStep 2291993 = 1718995) B1718995
theorem B5577011 : Blo 1526460 5577011 := bstep (se 1 (by rfl) ⟨4182758, by rfl⟩ : syracuseStep 5577011 = 8365517) B8365517
theorem B3438899 : Blo 1526460 3438899 := bstep (se 1 (by rfl) ⟨2579174, by rfl⟩ : syracuseStep 3438899 = 5158349) B5158349
theorem B4348235 : Blo 1526460 4348235 := bstep (se 1 (by rfl) ⟨3261176, by rfl⟩ : syracuseStep 4348235 = 6522353) B6522353
theorem B6363467 : Blo 1526460 6363467 := bstep (se 1 (by rfl) ⟨4772600, by rfl⟩ : syracuseStep 6363467 = 9545201) B9545201
theorem B2578763 : Blo 1526460 2578763 := bstep (se 1 (by rfl) ⟨1934072, by rfl⟩ : syracuseStep 2578763 = 3868145) B3868145
theorem B3438935 : Blo 1526460 3438935 := bstep (se 1 (by rfl) ⟨2579201, by rfl⟩ : syracuseStep 3438935 = 5158403) B5158403
theorem B1718635 : Blo 1526460 1718635 := bstep (se 1 (by rfl) ⟨1288976, by rfl⟩ : syracuseStep 1718635 = 2577953) B2577953
theorem B2292107 : Blo 1526460 2292107 := bstep (se 1 (by rfl) ⟨1719080, by rfl⟩ : syracuseStep 2292107 = 3438161) B3438161
theorem B2292119 : Blo 1526460 2292119 := bstep (se 1 (by rfl) ⟨1719089, by rfl⟩ : syracuseStep 2292119 = 3438179) B3438179
theorem B6527411 : Blo 1526460 6527411 := bstep (se 1 (by rfl) ⟨4895558, by rfl⟩ : syracuseStep 6527411 = 9791117) B9791117
theorem B2578891 : Blo 1526460 2578891 := bstep (se 1 (by rfl) ⟨1934168, by rfl⟩ : syracuseStep 2578891 = 3868337) B3868337
theorem B1718743 : Blo 1526460 1718743 := bstep (se 1 (by rfl) ⟨1289057, by rfl⟩ : syracuseStep 1718743 = 2578115) B2578115
theorem B2292185 : Blo 1526460 2292185 := bstep (se 2 (by rfl) ⟨859569, by rfl⟩ : syracuseStep 2292185 = 1719139) B1719139
theorem B2898443 : Blo 1526460 2898443 := bstep (se 1 (by rfl) ⟨2173832, by rfl⟩ : syracuseStep 2898443 = 4347665) B4347665
theorem B2751041 : Blo 1526460 2751041 := bstep (se 2 (by rfl) ⟨1031640, by rfl⟩ : syracuseStep 2751041 = 2063281) B2063281
theorem B2898497 : Blo 1526460 2898497 := bstep (se 2 (by rfl) ⟨1086936, by rfl⟩ : syracuseStep 2898497 = 2173873) B2173873
theorem B2292299 : Blo 1526460 2292299 := bstep (se 1 (by rfl) ⟨1719224, by rfl⟩ : syracuseStep 2292299 = 3438449) B3438449
theorem B2292311 : Blo 1526460 2292311 := bstep (se 1 (by rfl) ⟨1719233, by rfl⟩ : syracuseStep 2292311 = 3438467) B3438467
theorem B2579033 : Blo 1526460 2579033 := bstep (se 2 (by rfl) ⟨967137, by rfl⟩ : syracuseStep 2579033 = 1934275) B1934275
theorem B1718923 : Blo 1526460 1718923 := bstep (se 1 (by rfl) ⟨1289192, by rfl⟩ : syracuseStep 1718923 = 2578385) B2578385
theorem B2292377 : Blo 1526460 2292377 := bstep (se 2 (by rfl) ⟨859641, by rfl⟩ : syracuseStep 2292377 = 1719283) B1719283
theorem B5798573 : Blo 1526460 5798573 := bstep (se 3 (by rfl) ⟨1087232, by rfl⟩ : syracuseStep 5798573 = 2174465) B2174465
theorem B2579161 : Blo 1526460 2579161 := bstep (se 2 (by rfl) ⟨967185, by rfl⟩ : syracuseStep 2579161 = 1934371) B1934371
theorem B6617821 : Blo 1526460 6617821 := bstep (se 3 (by rfl) ⟨1240841, by rfl⟩ : syracuseStep 6617821 = 2481683) B2481683
theorem B1719031 : Blo 1526460 1719031 := bstep (se 1 (by rfl) ⟨1289273, by rfl⟩ : syracuseStep 1719031 = 2578547) B2578547
theorem B2292491 : Blo 1526460 2292491 := bstep (se 1 (by rfl) ⟨1719368, by rfl⟩ : syracuseStep 2292491 = 3438737) B3438737
theorem B2292503 : Blo 1526460 2292503 := bstep (se 1 (by rfl) ⟨1719377, by rfl⟩ : syracuseStep 2292503 = 3438755) B3438755
theorem B2292569 : Blo 1526460 2292569 := bstep (se 2 (by rfl) ⟨859713, by rfl⟩ : syracuseStep 2292569 = 1719427) B1719427
theorem B1719211 : Blo 1526460 1719211 := bstep (se 1 (by rfl) ⟨1289408, by rfl⟩ : syracuseStep 1719211 = 2578817) B2578817
theorem B2292683 : Blo 1526460 2292683 := bstep (se 1 (by rfl) ⟨1719512, by rfl⟩ : syracuseStep 2292683 = 3439025) B3439025
theorem B66059225 : Blo 1526460 66059225 := bstep (se 2 (by rfl) ⟨24772209, by rfl⟩ : syracuseStep 66059225 = 49544419) B49544419
theorem B1719319 : Blo 1526460 1719319 := bstep (se 1 (by rfl) ⟨1289489, by rfl⟩ : syracuseStep 1719319 = 2578979) B2578979
theorem B6609995 : Blo 1526460 6609995 := bstep (se 1 (by rfl) ⟨4957496, by rfl⟩ : syracuseStep 6609995 = 9914993) B9914993
theorem B1932427 : Blo 1526460 1932427 := bstep (se 1 (by rfl) ⟨1449320, by rfl⟩ : syracuseStep 1932427 = 2898641) B2898641
theorem B13049009 : Blo 1526460 13049009 := bstep (se 2 (by rfl) ⟨4893378, by rfl⟩ : syracuseStep 13049009 = 9786757) B9786757
theorem B5151923 : Blo 1526460 5151923 := bstep (se 1 (by rfl) ⟨3863942, by rfl⟩ : syracuseStep 5151923 = 7727885) B7727885
theorem B2751691 : Blo 1526460 2751691 := bstep (se 1 (by rfl) ⟨2063768, by rfl⟩ : syracuseStep 2751691 = 4127537) B4127537
theorem B1719499 : Blo 1526460 1719499 := bstep (se 1 (by rfl) ⟨1289624, by rfl⟩ : syracuseStep 1719499 = 2579249) B2579249
theorem B3669209 : Blo 1526460 3669209 := bstep (se 2 (by rfl) ⟨1375953, by rfl⟩ : syracuseStep 3669209 = 2751907) B2751907
theorem B11009297 : Blo 1526460 11009297 := bstep (se 2 (by rfl) ⟨4128486, by rfl⟩ : syracuseStep 11009297 = 8256973) B8256973
theorem B3865907 : Blo 1526460 3865907 := bstep (se 1 (by rfl) ⟨2899430, by rfl⟩ : syracuseStep 3865907 = 5798861) B5798861
theorem B22027585 : Blo 1526460 22027585 := bstep (se 2 (by rfl) ⟨8260344, by rfl⟩ : syracuseStep 22027585 = 16520689) B16520689
theorem B6528401 : Blo 1526460 6528401 := bstep (se 2 (by rfl) ⟨2448150, by rfl⟩ : syracuseStep 6528401 = 4896301) B4896301
theorem B9780659 : Blo 1526460 9780659 := bstep (se 1 (by rfl) ⟨7335494, by rfl⟩ : syracuseStep 9780659 = 14670989) B14670989
theorem B5799347 : Blo 1526460 5799347 := bstep (se 1 (by rfl) ⟨4349510, by rfl⟩ : syracuseStep 5799347 = 8699021) B8699021
theorem B5152193 : Blo 1526460 5152193 := bstep (se 2 (by rfl) ⟨1932072, by rfl⟩ : syracuseStep 5152193 = 3864145) B3864145
theorem B6520267 : Blo 1526460 6520267 := bstep (se 1 (by rfl) ⟨4890200, by rfl⟩ : syracuseStep 6520267 = 9780401) B9780401
theorem B2899415 : Blo 1526460 2899415 := bstep (se 1 (by rfl) ⟨2174561, by rfl⟩ : syracuseStep 2899415 = 4349123) B4349123
theorem B6520337 : Blo 1526460 6520337 := bstep (se 2 (by rfl) ⟨2445126, by rfl⟩ : syracuseStep 6520337 = 4890253) B4890253
theorem B3866201 : Blo 1526460 3866201 := bstep (se 2 (by rfl) ⟨1449825, by rfl⟩ : syracuseStep 3866201 = 2899651) B2899651
theorem B4349533 : Blo 1526460 4349533 := bstep (se 3 (by rfl) ⟨815537, by rfl⟩ : syracuseStep 4349533 = 1631075) B1631075
theorem B20913815 : Blo 1526460 20913815 := bstep (se 1 (by rfl) ⟨15685361, by rfl⟩ : syracuseStep 20913815 = 31370723) B31370723
theorem B1859275 : Blo 1526460 1859275 := bstep (se 1 (by rfl) ⟨1394456, by rfl⟩ : syracuseStep 1859275 = 2788913) B2788913
theorem B2064217 : Blo 1526460 2064217 := bstep (se 2 (by rfl) ⟨774081, by rfl⟩ : syracuseStep 2064217 = 1548163) B1548163
theorem B13049693 : Blo 1526460 13049693 := bstep (se 3 (by rfl) ⟨2446817, by rfl⟩ : syracuseStep 13049693 = 4893635) B4893635
theorem B3260339 : Blo 1526460 3260339 := bstep (se 1 (by rfl) ⟨2445254, by rfl⟩ : syracuseStep 3260339 = 4890509) B4890509
theorem B3137459 : Blo 1526460 3137459 := bstep (se 1 (by rfl) ⟨2353094, by rfl⟩ : syracuseStep 3137459 = 4706189) B4706189
theorem B4349875 : Blo 1526460 4349875 := bstep (se 1 (by rfl) ⟨3262406, by rfl⟩ : syracuseStep 4349875 = 6524813) B6524813
theorem B5152733 : Blo 1526460 5152733 := bstep (se 3 (by rfl) ⟨966137, by rfl⟩ : syracuseStep 5152733 = 1932275) B1932275
theorem B2899955 : Blo 1526460 2899955 := bstep (se 1 (by rfl) ⟨2174966, by rfl⟩ : syracuseStep 2899955 = 4349933) B4349933
theorem B4128779 : Blo 1526460 4128779 := bstep (se 1 (by rfl) ⟨3096584, by rfl⟩ : syracuseStep 4128779 = 6193169) B6193169
theorem B6193219 : Blo 1526460 6193219 := bstep (se 1 (by rfl) ⟨4644914, by rfl⟩ : syracuseStep 6193219 = 9289829) B9289829
theorem B7438423 : Blo 1526460 7438423 := bstep (se 1 (by rfl) ⟨5578817, by rfl⟩ : syracuseStep 7438423 = 11157635) B11157635
theorem B17662153 : Blo 1526460 17662153 := bstep (se 2 (by rfl) ⟨6623307, by rfl⟩ : syracuseStep 17662153 = 13246615) B13246615
theorem B5153057 : Blo 1526460 5153057 := bstep (se 2 (by rfl) ⟨1932396, by rfl⟩ : syracuseStep 5153057 = 3864793) B3864793
theorem B7733555 : Blo 1526460 7733555 := bstep (se 1 (by rfl) ⟨5800166, by rfl⟩ : syracuseStep 7733555 = 11600333) B11600333
theorem B1933627 : Blo 1526460 1933627 := bstep (se 1 (by rfl) ⟨1450220, by rfl⟩ : syracuseStep 1933627 = 2900441) B2900441
theorem B11592071 : Blo 1526460 11592071 := bstep (se 1 (by rfl) ⟨8694053, by rfl⟩ : syracuseStep 11592071 = 17388107) B17388107
theorem B11010451 : Blo 1526460 11010451 := bstep (se 1 (by rfl) ⟨8257838, by rfl⟩ : syracuseStep 11010451 = 16515677) B16515677
theorem B2900539 : Blo 1526460 2900539 := bstep (se 1 (by rfl) ⟨2175404, by rfl⟩ : syracuseStep 2900539 = 4350809) B4350809
theorem B3867223 : Blo 1526460 3867223 := bstep (se 1 (by rfl) ⟨2900417, by rfl⟩ : syracuseStep 3867223 = 5800835) B5800835
theorem B7733879 : Blo 1526460 7733879 := bstep (se 1 (by rfl) ⟨5800409, by rfl⟩ : syracuseStep 7733879 = 11600819) B11600819
theorem B8258249 : Blo 1526460 8258249 := bstep (se 2 (by rfl) ⟨3096843, by rfl⟩ : syracuseStep 8258249 = 6193687) B6193687
theorem B4129481 : Blo 1526460 4129481 := bstep (se 2 (by rfl) ⟨1548555, by rfl⟩ : syracuseStep 4129481 = 3097111) B3097111
theorem B3261227 : Blo 1526460 3261227 := bstep (se 1 (by rfl) ⟨2445920, by rfl⟩ : syracuseStep 3261227 = 4891841) B4891841
theorem B4350763 : Blo 1526460 4350763 := bstep (se 1 (by rfl) ⟨3263072, by rfl⟩ : syracuseStep 4350763 = 6526145) B6526145
theorem B5153651 : Blo 1526460 5153651 := bstep (se 1 (by rfl) ⟨3865238, by rfl⟩ : syracuseStep 5153651 = 7730477) B7730477
theorem B3867527 : Blo 1526460 3867527 := bstep (se 1 (by rfl) ⟨2900645, by rfl⟩ : syracuseStep 3867527 = 5801291) B5801291
theorem B8823761 : Blo 1526460 8823761 := bstep (se 2 (by rfl) ⟨3308910, by rfl⟩ : syracuseStep 8823761 = 6617821) B6617821
theorem B3867659 : Blo 1526460 3867659 := bstep (se 1 (by rfl) ⟨2900744, by rfl⟩ : syracuseStep 3867659 = 5801489) B5801489
theorem B4350991 : Blo 1526460 4350991 := bstep (se 1 (by rfl) ⟨3263243, by rfl⟩ : syracuseStep 4350991 = 6526487) B6526487
theorem B2901025 : Blo 1526460 2901025 := bstep (se 2 (by rfl) ⟨1087884, by rfl⟩ : syracuseStep 2901025 = 2175769) B2175769
theorem B5801003 : Blo 1526460 5801003 := bstep (se 1 (by rfl) ⟨4350752, by rfl⟩ : syracuseStep 5801003 = 8701505) B8701505
theorem B6522113 : Blo 1526460 6522113 := bstep (se 2 (by rfl) ⟨2445792, by rfl⟩ : syracuseStep 6522113 = 4891585) B4891585
theorem B3917071 : Blo 1526460 3917071 := bstep (se 1 (by rfl) ⟨2937803, by rfl⟩ : syracuseStep 3917071 = 5875607) B5875607
theorem B4351265 : Blo 1526460 4351265 := bstep (se 2 (by rfl) ⟨1631724, by rfl⟩ : syracuseStep 4351265 = 3263449) B3263449
theorem B11011463 : Blo 1526460 11011463 := bstep (se 1 (by rfl) ⟨8258597, by rfl⟩ : syracuseStep 11011463 = 16517195) B16517195
theorem B4130195 : Blo 1526460 4130195 := bstep (se 1 (by rfl) ⟨3097646, by rfl⟩ : syracuseStep 4130195 = 6195293) B6195293
theorem B3671563 : Blo 1526460 3671563 := bstep (se 1 (by rfl) ⟨2753672, by rfl⟩ : syracuseStep 3671563 = 5507345) B5507345
theorem B3868175 : Blo 1526460 3868175 := bstep (se 1 (by rfl) ⟨2901131, by rfl⟩ : syracuseStep 3868175 = 5802263) B5802263
theorem B3139105 : Blo 1526460 3139105 := bstep (se 2 (by rfl) ⟨1177164, by rfl⟩ : syracuseStep 3139105 = 2354329) B2354329
theorem B4130347 : Blo 1526460 4130347 := bstep (se 1 (by rfl) ⟨3097760, by rfl⟩ : syracuseStep 4130347 = 6195521) B6195521
theorem B7734851 : Blo 1526460 7734851 := bstep (se 1 (by rfl) ⟨5801138, by rfl⟩ : syracuseStep 7734851 = 11602277) B11602277
theorem B13051469 : Blo 1526460 13051469 := bstep (se 3 (by rfl) ⟨2447150, by rfl⟩ : syracuseStep 13051469 = 4894301) B4894301
theorem B4351607 : Blo 1526460 4351607 := bstep (se 1 (by rfl) ⟨3263705, by rfl⟩ : syracuseStep 4351607 = 6527411) B6527411
theorem B3868307 : Blo 1526460 3868307 := bstep (se 1 (by rfl) ⟨2901230, by rfl⟩ : syracuseStep 3868307 = 5802461) B5802461
theorem B29370113 : Blo 1526460 29370113 := bstep (se 2 (by rfl) ⟨11013792, by rfl⟩ : syracuseStep 29370113 = 22027585) B22027585
theorem B13223695 : Blo 1526460 13223695 := bstep (se 1 (by rfl) ⟨9917771, by rfl⟩ : syracuseStep 13223695 = 19835543) B19835543
theorem B5228347 : Blo 1526460 5228347 := bstep (se 1 (by rfl) ⟨3921260, by rfl⟩ : syracuseStep 5228347 = 7842521) B7842521
theorem B7735175 : Blo 1526460 7735175 := bstep (se 1 (by rfl) ⟨5801381, by rfl⟩ : syracuseStep 7735175 = 11602763) B11602763
theorem B8693689 : Blo 1526460 8693689 := bstep (se 2 (by rfl) ⟨3260133, by rfl⟩ : syracuseStep 8693689 = 6520267) B6520267
theorem B7342109 : Blo 1526460 7342109 := bstep (se 3 (by rfl) ⟨1376645, by rfl⟩ : syracuseStep 7342109 = 2753291) B2753291
theorem B3672179 : Blo 1526460 3672179 := bstep (se 1 (by rfl) ⟨2754134, by rfl⟩ : syracuseStep 3672179 = 5508269) B5508269
theorem B3434615 : Blo 1526460 3434615 := bstep (se 1 (by rfl) ⟨2575961, by rfl⟩ : syracuseStep 3434615 = 5151923) B5151923
theorem B19581101 : Blo 1526460 19581101 := bstep (se 3 (by rfl) ⟨3671456, by rfl⟩ : syracuseStep 19581101 = 7342913) B7342913
theorem B4352267 : Blo 1526460 4352267 := bstep (se 1 (by rfl) ⟨3264200, by rfl⟩ : syracuseStep 4352267 = 6528401) B6528401
theorem B3434795 : Blo 1526460 3434795 := bstep (se 1 (by rfl) ⟨2576096, by rfl⟩ : syracuseStep 3434795 = 5152193) B5152193
theorem B8366557 : Blo 1526460 8366557 := bstep (se 3 (by rfl) ⟨1568729, by rfl⟩ : syracuseStep 8366557 = 3137459) B3137459
theorem B2173559 : Blo 1526460 2173559 := bstep (se 1 (by rfl) ⟨1630169, by rfl⟩ : syracuseStep 2173559 = 3260339) B3260339
theorem B3435155 : Blo 1526460 3435155 := bstep (se 1 (by rfl) ⟨2576366, by rfl⟩ : syracuseStep 3435155 = 5152733) B5152733
theorem B9292481 : Blo 1526460 9292481 := bstep (se 2 (by rfl) ⟨3484680, by rfl⟩ : syracuseStep 9292481 = 6969361) B6969361
theorem B3435209 : Blo 1526460 3435209 := bstep (se 2 (by rfl) ⟨1288203, by rfl⟩ : syracuseStep 3435209 = 2576407) B2576407
theorem B1526535 : Blo 1526460 1526535 := bstep (se 1 (by rfl) ⟨1144901, by rfl⟩ : syracuseStep 1526535 = 2289803) B2289803
theorem B1526543 : Blo 1526460 1526543 := bstep (se 1 (by rfl) ⟨1144907, by rfl⟩ : syracuseStep 1526543 = 2289815) B2289815
theorem B26446607 : Blo 1526460 26446607 := bstep (se 1 (by rfl) ⟨19834955, by rfl⟩ : syracuseStep 26446607 = 39669911) B39669911
theorem B2173753 : Blo 1526460 2173753 := bstep (se 2 (by rfl) ⟨815157, by rfl⟩ : syracuseStep 2173753 = 1630315) B1630315
theorem B1526587 : Blo 1526460 1526587 := bstep (se 1 (by rfl) ⟨1144940, by rfl⟩ : syracuseStep 1526587 = 2289881) B2289881
theorem B1526663 : Blo 1526460 1526663 := bstep (se 1 (by rfl) ⟨1144997, by rfl⟩ : syracuseStep 1526663 = 2289995) B2289995
theorem B1526671 : Blo 1526460 1526671 := bstep (se 1 (by rfl) ⟨1145003, by rfl⟩ : syracuseStep 1526671 = 2290007) B2290007
theorem B27880355 : Blo 1526460 27880355 := bstep (se 1 (by rfl) ⟨20910266, by rfl⟩ : syracuseStep 27880355 = 41820533) B41820533
theorem B1526715 : Blo 1526460 1526715 := bstep (se 1 (by rfl) ⟨1145036, by rfl⟩ : syracuseStep 1526715 = 2290073) B2290073
theorem B5802961 : Blo 1526460 5802961 := bstep (se 2 (by rfl) ⟨2176110, by rfl⟩ : syracuseStep 5802961 = 4352221) B4352221
theorem B1933303 : Blo 1526460 1933303 := bstep (se 1 (by rfl) ⟨1449977, by rfl⟩ : syracuseStep 1933303 = 2899955) B2899955
theorem B1526791 : Blo 1526460 1526791 := bstep (se 1 (by rfl) ⟨1145093, by rfl⟩ : syracuseStep 1526791 = 2290187) B2290187
theorem B1526799 : Blo 1526460 1526799 := bstep (se 1 (by rfl) ⟨1145099, by rfl⟩ : syracuseStep 1526799 = 2290199) B2290199
theorem B2321465 : Blo 1526460 2321465 := bstep (se 2 (by rfl) ⟨870549, by rfl⟩ : syracuseStep 2321465 = 1741099) B1741099
theorem B1526843 : Blo 1526460 1526843 := bstep (se 1 (by rfl) ⟨1145132, by rfl⟩ : syracuseStep 1526843 = 2290265) B2290265
theorem B5024855 : Blo 1526460 5024855 := bstep (se 1 (by rfl) ⟨3768641, by rfl⟩ : syracuseStep 5024855 = 7537283) B7537283
theorem B1526919 : Blo 1526460 1526919 := bstep (se 1 (by rfl) ⟨1145189, by rfl⟩ : syracuseStep 1526919 = 2290379) B2290379
theorem B1526927 : Blo 1526460 1526927 := bstep (se 1 (by rfl) ⟨1145195, by rfl⟩ : syracuseStep 1526927 = 2290391) B2290391
theorem B1526971 : Blo 1526460 1526971 := bstep (se 1 (by rfl) ⟨1145228, by rfl⟩ : syracuseStep 1526971 = 2290457) B2290457
theorem B8260865 : Blo 1526460 8260865 := bstep (se 2 (by rfl) ⟨3097824, by rfl⟩ : syracuseStep 8260865 = 6195649) B6195649
theorem B5803265 : Blo 1526460 5803265 := bstep (se 2 (by rfl) ⟨2176224, by rfl⟩ : syracuseStep 5803265 = 4352449) B4352449
theorem B1527047 : Blo 1526460 1527047 := bstep (se 1 (by rfl) ⟨1145285, by rfl⟩ : syracuseStep 1527047 = 2290571) B2290571
theorem B1527055 : Blo 1526460 1527055 := bstep (se 1 (by rfl) ⟨1145291, by rfl⟩ : syracuseStep 1527055 = 2290583) B2290583
theorem B1527099 : Blo 1526460 1527099 := bstep (se 1 (by rfl) ⟨1145324, by rfl⟩ : syracuseStep 1527099 = 2290649) B2290649
theorem B3435911 : Blo 1526460 3435911 := bstep (se 1 (by rfl) ⟨2576933, by rfl⟩ : syracuseStep 3435911 = 5153867) B5153867
theorem B1527175 : Blo 1526460 1527175 := bstep (se 1 (by rfl) ⟨1145381, by rfl⟩ : syracuseStep 1527175 = 2290763) B2290763
theorem B1527183 : Blo 1526460 1527183 := bstep (se 1 (by rfl) ⟨1145387, by rfl⟩ : syracuseStep 1527183 = 2290775) B2290775
theorem B5156243 : Blo 1526460 5156243 := bstep (se 1 (by rfl) ⟨3867182, by rfl⟩ : syracuseStep 5156243 = 7734365) B7734365
theorem B5508499 : Blo 1526460 5508499 := bstep (se 1 (by rfl) ⟨4131374, by rfl⟩ : syracuseStep 5508499 = 8262749) B8262749
theorem B1527227 : Blo 1526460 1527227 := bstep (se 1 (by rfl) ⟨1145420, by rfl⟩ : syracuseStep 1527227 = 2290841) B2290841
theorem B1527303 : Blo 1526460 1527303 := bstep (se 1 (by rfl) ⟨1145477, by rfl⟩ : syracuseStep 1527303 = 2290955) B2290955
theorem B1527311 : Blo 1526460 1527311 := bstep (se 1 (by rfl) ⟨1145483, by rfl⟩ : syracuseStep 1527311 = 2290967) B2290967
theorem B3436091 : Blo 1526460 3436091 := bstep (se 1 (by rfl) ⟨2577068, by rfl⟩ : syracuseStep 3436091 = 5154137) B5154137
theorem B1527355 : Blo 1526460 1527355 := bstep (se 1 (by rfl) ⟨1145516, by rfl⟩ : syracuseStep 1527355 = 2291033) B2291033
theorem B2322055 : Blo 1526460 2322055 := bstep (se 1 (by rfl) ⟨1741541, by rfl⟩ : syracuseStep 2322055 = 3483083) B3483083
theorem B1527431 : Blo 1526460 1527431 := bstep (se 1 (by rfl) ⟨1145573, by rfl⟩ : syracuseStep 1527431 = 2291147) B2291147
theorem B1527439 : Blo 1526460 1527439 := bstep (se 1 (by rfl) ⟨1145579, by rfl⟩ : syracuseStep 1527439 = 2291159) B2291159
theorem B26095283 : Blo 1526460 26095283 := bstep (se 1 (by rfl) ⟨19571462, by rfl⟩ : syracuseStep 26095283 = 39142925) B39142925
theorem B3436217 : Blo 1526460 3436217 := bstep (se 2 (by rfl) ⟨1288581, by rfl⟩ : syracuseStep 3436217 = 2577163) B2577163
theorem B1527483 : Blo 1526460 1527483 := bstep (se 1 (by rfl) ⟨1145612, by rfl⟩ : syracuseStep 1527483 = 2291225) B2291225
theorem B1527559 : Blo 1526460 1527559 := bstep (se 1 (by rfl) ⟨1145669, by rfl⟩ : syracuseStep 1527559 = 2291339) B2291339
theorem B1527567 : Blo 1526460 1527567 := bstep (se 1 (by rfl) ⟨1145675, by rfl⟩ : syracuseStep 1527567 = 2291351) B2291351
theorem B2576171 : Blo 1526460 2576171 := bstep (se 1 (by rfl) ⟨1932128, by rfl⟩ : syracuseStep 2576171 = 3864257) B3864257
theorem B1527611 : Blo 1526460 1527611 := bstep (se 1 (by rfl) ⟨1145708, by rfl⟩ : syracuseStep 1527611 = 2291417) B2291417
theorem B1527687 : Blo 1526460 1527687 := bstep (se 1 (by rfl) ⟨1145765, by rfl⟩ : syracuseStep 1527687 = 2291531) B2291531
theorem B1527695 : Blo 1526460 1527695 := bstep (se 1 (by rfl) ⟨1145771, by rfl⟩ : syracuseStep 1527695 = 2291543) B2291543
theorem B29364119 : Blo 1526460 29364119 := bstep (se 1 (by rfl) ⟨22023089, by rfl⟩ : syracuseStep 29364119 = 44046179) B44046179
theorem B1527739 : Blo 1526460 1527739 := bstep (se 1 (by rfl) ⟨1145804, by rfl⟩ : syracuseStep 1527739 = 2291609) B2291609
theorem B1527815 : Blo 1526460 1527815 := bstep (se 1 (by rfl) ⟨1145861, by rfl⟩ : syracuseStep 1527815 = 2291723) B2291723
theorem B3436559 : Blo 1526460 3436559 := bstep (se 1 (by rfl) ⟨2577419, by rfl⟩ : syracuseStep 3436559 = 5154839) B5154839
theorem B1527823 : Blo 1526460 1527823 := bstep (se 1 (by rfl) ⟨1145867, by rfl⟩ : syracuseStep 1527823 = 2291735) B2291735
theorem B7729181 : Blo 1526460 7729181 := bstep (se 3 (by rfl) ⟨1449221, by rfl⟩ : syracuseStep 7729181 = 2898443) B2898443
theorem B3436577 : Blo 1526460 3436577 := bstep (se 2 (by rfl) ⟨1288716, by rfl⟩ : syracuseStep 3436577 = 2577433) B2577433
theorem B2289707 : Blo 1526460 2289707 := bstep (se 1 (by rfl) ⟨1717280, by rfl⟩ : syracuseStep 2289707 = 3434561) B3434561
theorem B1527867 : Blo 1526460 1527867 := bstep (se 1 (by rfl) ⟨1145900, by rfl⟩ : syracuseStep 1527867 = 2291801) B2291801
theorem B2289737 : Blo 1526460 2289737 := bstep (se 2 (by rfl) ⟨858651, by rfl⟩ : syracuseStep 2289737 = 1717303) B1717303
theorem B1527943 : Blo 1526460 1527943 := bstep (se 1 (by rfl) ⟨1145957, by rfl⟩ : syracuseStep 1527943 = 2291915) B2291915
theorem B1527951 : Blo 1526460 1527951 := bstep (se 1 (by rfl) ⟨1145963, by rfl⟩ : syracuseStep 1527951 = 2291927) B2291927
theorem B7336109 : Blo 1526460 7336109 := bstep (se 3 (by rfl) ⟨1375520, by rfl⟩ : syracuseStep 7336109 = 2751041) B2751041
theorem B33018029 : Blo 1526460 33018029 := bstep (se 3 (by rfl) ⟨6190880, by rfl⟩ : syracuseStep 33018029 = 12381761) B12381761
theorem B2576569 : Blo 1526460 2576569 := bstep (se 2 (by rfl) ⟨966213, by rfl⟩ : syracuseStep 2576569 = 1932427) B1932427
theorem B2289851 : Blo 1526460 2289851 := bstep (se 1 (by rfl) ⟨1717388, by rfl⟩ : syracuseStep 2289851 = 3434777) B3434777
theorem B1527995 : Blo 1526460 1527995 := bstep (se 1 (by rfl) ⟨1145996, by rfl⟩ : syracuseStep 1527995 = 2291993) B2291993
theorem B2289911 : Blo 1526460 2289911 := bstep (se 1 (by rfl) ⟨1717433, by rfl⟩ : syracuseStep 2289911 = 3434867) B3434867
theorem B1528071 : Blo 1526460 1528071 := bstep (se 1 (by rfl) ⟨1146053, by rfl⟩ : syracuseStep 1528071 = 2292107) B2292107
theorem B2289935 : Blo 1526460 2289935 := bstep (se 1 (by rfl) ⟨1717451, by rfl⟩ : syracuseStep 2289935 = 3434903) B3434903
theorem B1528079 : Blo 1526460 1528079 := bstep (se 1 (by rfl) ⟨1146059, by rfl⟩ : syracuseStep 1528079 = 2292119) B2292119
theorem B2289977 : Blo 1526460 2289977 := bstep (se 2 (by rfl) ⟨858741, by rfl⟩ : syracuseStep 2289977 = 1717483) B1717483
theorem B1528123 : Blo 1526460 1528123 := bstep (se 1 (by rfl) ⟨1146092, by rfl⟩ : syracuseStep 1528123 = 2292185) B2292185
theorem B2322761 : Blo 1526460 2322761 := bstep (se 2 (by rfl) ⟨871035, by rfl⟩ : syracuseStep 2322761 = 1742071) B1742071
theorem B3436919 : Blo 1526460 3436919 := bstep (se 1 (by rfl) ⟨2577689, by rfl⟩ : syracuseStep 3436919 = 5155379) B5155379
theorem B2290055 : Blo 1526460 2290055 := bstep (se 1 (by rfl) ⟨1717541, by rfl⟩ : syracuseStep 2290055 = 3435083) B3435083
theorem B1528199 : Blo 1526460 1528199 := bstep (se 1 (by rfl) ⟨1146149, by rfl⟩ : syracuseStep 1528199 = 2292299) B2292299
theorem B1528207 : Blo 1526460 1528207 := bstep (se 1 (by rfl) ⟨1146155, by rfl⟩ : syracuseStep 1528207 = 2292311) B2292311
theorem B2290091 : Blo 1526460 2290091 := bstep (se 1 (by rfl) ⟨1717568, by rfl⟩ : syracuseStep 2290091 = 3435137) B3435137
theorem B1528251 : Blo 1526460 1528251 := bstep (se 1 (by rfl) ⟨1146188, by rfl⟩ : syracuseStep 1528251 = 2292377) B2292377
theorem B2290121 : Blo 1526460 2290121 := bstep (se 2 (by rfl) ⟨858795, by rfl⟩ : syracuseStep 2290121 = 1717591) B1717591
theorem B7729667 : Blo 1526460 7729667 := bstep (se 1 (by rfl) ⟨5797250, by rfl⟩ : syracuseStep 7729667 = 11594501) B11594501
theorem B1528327 : Blo 1526460 1528327 := bstep (se 1 (by rfl) ⟨1146245, by rfl⟩ : syracuseStep 1528327 = 2292491) B2292491
theorem B1528335 : Blo 1526460 1528335 := bstep (se 1 (by rfl) ⟨1146251, by rfl⟩ : syracuseStep 1528335 = 2292503) B2292503
theorem B38171179 : Blo 1526460 38171179 := bstep (se 1 (by rfl) ⟨28628384, by rfl⟩ : syracuseStep 38171179 = 57256769) B57256769
theorem B3437099 : Blo 1526460 3437099 := bstep (se 1 (by rfl) ⟨2577824, by rfl⟩ : syracuseStep 3437099 = 5155649) B5155649
theorem B2290235 : Blo 1526460 2290235 := bstep (se 1 (by rfl) ⟨1717676, by rfl⟩ : syracuseStep 2290235 = 3435353) B3435353
theorem B1528379 : Blo 1526460 1528379 := bstep (se 1 (by rfl) ⟨1146284, by rfl⟩ : syracuseStep 1528379 = 2292569) B2292569
theorem B2290295 : Blo 1526460 2290295 := bstep (se 1 (by rfl) ⟨1717721, by rfl⟩ : syracuseStep 2290295 = 3435443) B3435443
theorem B1528455 : Blo 1526460 1528455 := bstep (se 1 (by rfl) ⟨1146341, by rfl⟩ : syracuseStep 1528455 = 2292683) B2292683
theorem B2290319 : Blo 1526460 2290319 := bstep (se 1 (by rfl) ⟨1717739, by rfl⟩ : syracuseStep 2290319 = 3435479) B3435479
theorem B2290361 : Blo 1526460 2290361 := bstep (se 2 (by rfl) ⟨858885, by rfl⟩ : syracuseStep 2290361 = 1717771) B1717771
theorem B2290439 : Blo 1526460 2290439 := bstep (se 1 (by rfl) ⟨1717829, by rfl⟩ : syracuseStep 2290439 = 3435659) B3435659
theorem B5157647 : Blo 1526460 5157647 := bstep (se 1 (by rfl) ⟨3868235, by rfl⟩ : syracuseStep 5157647 = 7736471) B7736471
theorem B2290475 : Blo 1526460 2290475 := bstep (se 1 (by rfl) ⟨1717856, by rfl⟩ : syracuseStep 2290475 = 3435713) B3435713
theorem B2446139 : Blo 1526460 2446139 := bstep (se 1 (by rfl) ⟨1834604, by rfl⟩ : syracuseStep 2446139 = 3669209) B3669209
theorem B7336763 : Blo 1526460 7336763 := bstep (se 1 (by rfl) ⟨5502572, by rfl⟩ : syracuseStep 7336763 = 11005145) B11005145
theorem B2290505 : Blo 1526460 2290505 := bstep (se 2 (by rfl) ⟨858939, by rfl⟩ : syracuseStep 2290505 = 1717879) B1717879
theorem B8369011 : Blo 1526460 8369011 := bstep (se 1 (by rfl) ⟨6276758, by rfl⟩ : syracuseStep 8369011 = 12553517) B12553517
theorem B2577271 : Blo 1526460 2577271 := bstep (se 1 (by rfl) ⟨1932953, by rfl⟩ : syracuseStep 2577271 = 3865907) B3865907
theorem B3437459 : Blo 1526460 3437459 := bstep (se 1 (by rfl) ⟨2578094, by rfl⟩ : syracuseStep 3437459 = 5156189) B5156189
theorem B2479033 : Blo 1526460 2479033 := bstep (se 2 (by rfl) ⟨929637, by rfl⟩ : syracuseStep 2479033 = 1859275) B1859275
theorem B2290619 : Blo 1526460 2290619 := bstep (se 1 (by rfl) ⟨1717964, by rfl⟩ : syracuseStep 2290619 = 3435929) B3435929
theorem B3437513 : Blo 1526460 3437513 := bstep (se 2 (by rfl) ⟨1289067, by rfl⟩ : syracuseStep 3437513 = 2578135) B2578135
theorem B2290679 : Blo 1526460 2290679 := bstep (se 1 (by rfl) ⟨1718009, by rfl⟩ : syracuseStep 2290679 = 3436019) B3436019
theorem B4346891 : Blo 1526460 4346891 := bstep (se 1 (by rfl) ⟨3260168, by rfl⟩ : syracuseStep 4346891 = 6520337) B6520337
theorem B2290703 : Blo 1526460 2290703 := bstep (se 1 (by rfl) ⟨1718027, by rfl⟩ : syracuseStep 2290703 = 3436055) B3436055
theorem B5157917 : Blo 1526460 5157917 := bstep (se 3 (by rfl) ⟨967109, by rfl⟩ : syracuseStep 5157917 = 1934219) B1934219
theorem B2290745 : Blo 1526460 2290745 := bstep (se 2 (by rfl) ⟨859029, by rfl⟩ : syracuseStep 2290745 = 1718059) B1718059
theorem B2577467 : Blo 1526460 2577467 := bstep (se 1 (by rfl) ⟨1933100, by rfl⟩ : syracuseStep 2577467 = 3866201) B3866201
theorem B6190199 : Blo 1526460 6190199 := bstep (se 1 (by rfl) ⟨4642649, by rfl⟩ : syracuseStep 6190199 = 9285299) B9285299
theorem B2290823 : Blo 1526460 2290823 := bstep (se 1 (by rfl) ⟨1718117, by rfl⟩ : syracuseStep 2290823 = 3436235) B3436235
theorem B2290859 : Blo 1526460 2290859 := bstep (se 1 (by rfl) ⟨1718144, by rfl⟩ : syracuseStep 2290859 = 3436289) B3436289
theorem B2290889 : Blo 1526460 2290889 := bstep (se 2 (by rfl) ⟨859083, by rfl⟩ : syracuseStep 2290889 = 1718167) B1718167
theorem B11605193 : Blo 1526460 11605193 := bstep (se 2 (by rfl) ⟨4351947, by rfl⟩ : syracuseStep 11605193 = 8703895) B8703895
theorem B1717519 : Blo 1526460 1717519 := bstep (se 1 (by rfl) ⟨1288139, by rfl⟩ : syracuseStep 1717519 = 2576279) B2576279
theorem B2291003 : Blo 1526460 2291003 := bstep (se 1 (by rfl) ⟨1718252, by rfl⟩ : syracuseStep 2291003 = 3436505) B3436505
theorem B33019235 : Blo 1526460 33019235 := bstep (se 1 (by rfl) ⟨24764426, by rfl⟩ : syracuseStep 33019235 = 49528853) B49528853
theorem B2291063 : Blo 1526460 2291063 := bstep (se 1 (by rfl) ⟨1718297, by rfl⟩ : syracuseStep 2291063 = 3436595) B3436595
theorem B2291087 : Blo 1526460 2291087 := bstep (se 1 (by rfl) ⟨1718315, by rfl⟩ : syracuseStep 2291087 = 3436631) B3436631
theorem B2291129 : Blo 1526460 2291129 := bstep (se 2 (by rfl) ⟨859173, by rfl⟩ : syracuseStep 2291129 = 1718347) B1718347
theorem B2577865 : Blo 1526460 2577865 := bstep (se 2 (by rfl) ⟨966699, by rfl⟩ : syracuseStep 2577865 = 1933399) B1933399
theorem B15685123 : Blo 1526460 15685123 := bstep (se 1 (by rfl) ⟨11763842, by rfl⟩ : syracuseStep 15685123 = 23527685) B23527685
theorem B2291207 : Blo 1526460 2291207 := bstep (se 1 (by rfl) ⟨1718405, by rfl⟩ : syracuseStep 2291207 = 3436811) B3436811
theorem B2291243 : Blo 1526460 2291243 := bstep (se 1 (by rfl) ⟨1718432, by rfl⟩ : syracuseStep 2291243 = 3436865) B3436865
theorem B2291273 : Blo 1526460 2291273 := bstep (se 2 (by rfl) ⟨859227, by rfl⟩ : syracuseStep 2291273 = 1718455) B1718455
theorem B7337591 : Blo 1526460 7337591 := bstep (se 1 (by rfl) ⟨5503193, by rfl⟩ : syracuseStep 7337591 = 11006387) B11006387
theorem B3438215 : Blo 1526460 3438215 := bstep (se 1 (by rfl) ⟨2578661, by rfl⟩ : syracuseStep 3438215 = 5157323) B5157323
theorem B2291387 : Blo 1526460 2291387 := bstep (se 1 (by rfl) ⟨1718540, by rfl⟩ : syracuseStep 2291387 = 3437081) B3437081
theorem B2291447 : Blo 1526460 2291447 := bstep (se 1 (by rfl) ⟨1718585, by rfl⟩ : syracuseStep 2291447 = 3437171) B3437171
theorem B1718023 : Blo 1526460 1718023 := bstep (se 1 (by rfl) ⟨1288517, by rfl⟩ : syracuseStep 1718023 = 2577035) B2577035
theorem B2291471 : Blo 1526460 2291471 := bstep (se 1 (by rfl) ⟨1718603, by rfl⟩ : syracuseStep 2291471 = 3437207) B3437207
theorem B2291513 : Blo 1526460 2291513 := bstep (se 2 (by rfl) ⟨859317, by rfl⟩ : syracuseStep 2291513 = 1718635) B1718635
theorem B3438395 : Blo 1526460 3438395 := bstep (se 1 (by rfl) ⟨2578796, by rfl⟩ : syracuseStep 3438395 = 5157593) B5157593
theorem B12556147 : Blo 1526460 12556147 := bstep (se 1 (by rfl) ⟨9417110, by rfl⟩ : syracuseStep 12556147 = 18834221) B18834221
theorem B2291591 : Blo 1526460 2291591 := bstep (se 1 (by rfl) ⟨1718693, by rfl⟩ : syracuseStep 2291591 = 3437387) B3437387
theorem B2291627 : Blo 1526460 2291627 := bstep (se 1 (by rfl) ⟨1718720, by rfl⟩ : syracuseStep 2291627 = 3437441) B3437441
theorem B3438521 : Blo 1526460 3438521 := bstep (se 2 (by rfl) ⟨1289445, by rfl⟩ : syracuseStep 3438521 = 2578891) B2578891
theorem B1718203 : Blo 1526460 1718203 := bstep (se 1 (by rfl) ⟨1288652, by rfl⟩ : syracuseStep 1718203 = 2577305) B2577305
theorem B2291657 : Blo 1526460 2291657 := bstep (se 2 (by rfl) ⟨859371, by rfl⟩ : syracuseStep 2291657 = 1718743) B1718743
theorem B3667979 : Blo 1526460 3667979 := bstep (se 1 (by rfl) ⟨2750984, by rfl⟩ : syracuseStep 3667979 = 5501969) B5501969
theorem B2291771 : Blo 1526460 2291771 := bstep (se 1 (by rfl) ⟨1718828, by rfl⟩ : syracuseStep 2291771 = 3437657) B3437657
theorem B7731287 : Blo 1526460 7731287 := bstep (se 1 (by rfl) ⟨5798465, by rfl⟩ : syracuseStep 7731287 = 11596931) B11596931
theorem B4348019 : Blo 1526460 4348019 := bstep (se 1 (by rfl) ⟨3261014, by rfl⟩ : syracuseStep 4348019 = 6522029) B6522029
theorem B2291831 : Blo 1526460 2291831 := bstep (se 1 (by rfl) ⟨1718873, by rfl⟩ : syracuseStep 2291831 = 3437747) B3437747
theorem B2578567 : Blo 1526460 2578567 := bstep (se 1 (by rfl) ⟨1933925, by rfl⟩ : syracuseStep 2578567 = 3867851) B3867851
theorem B2291855 : Blo 1526460 2291855 := bstep (se 1 (by rfl) ⟨1718891, by rfl⟩ : syracuseStep 2291855 = 3437783) B3437783
theorem B2291897 : Blo 1526460 2291897 := bstep (se 2 (by rfl) ⟨859461, by rfl⟩ : syracuseStep 2291897 = 1718923) B1718923
theorem B2447561 : Blo 1526460 2447561 := bstep (se 2 (by rfl) ⟨917835, by rfl⟩ : syracuseStep 2447561 = 1835671) B1835671
theorem B2291975 : Blo 1526460 2291975 := bstep (se 1 (by rfl) ⟨1718981, by rfl⟩ : syracuseStep 2291975 = 3437963) B3437963
theorem B3438863 : Blo 1526460 3438863 := bstep (se 1 (by rfl) ⟨2579147, by rfl⟩ : syracuseStep 3438863 = 5158295) B5158295
theorem B3438881 : Blo 1526460 3438881 := bstep (se 2 (by rfl) ⟨1289580, by rfl⟩ : syracuseStep 3438881 = 2579161) B2579161
theorem B2292011 : Blo 1526460 2292011 := bstep (se 1 (by rfl) ⟨1719008, by rfl⟩ : syracuseStep 2292011 = 3438017) B3438017
theorem B2292041 : Blo 1526460 2292041 := bstep (se 2 (by rfl) ⟨859515, by rfl⟩ : syracuseStep 2292041 = 1719031) B1719031
theorem B14686595 : Blo 1526460 14686595 := bstep (se 1 (by rfl) ⟨11014946, by rfl⟩ : syracuseStep 14686595 = 22029893) B22029893
theorem B89332109 : Blo 1526460 89332109 := bstep (se 3 (by rfl) ⟨16749770, by rfl⟩ : syracuseStep 89332109 = 33499541) B33499541
theorem B1718671 : Blo 1526460 1718671 := bstep (se 1 (by rfl) ⟨1289003, by rfl⟩ : syracuseStep 1718671 = 2578007) B2578007
theorem B8255891 : Blo 1526460 8255891 := bstep (se 1 (by rfl) ⟨6191918, by rfl⟩ : syracuseStep 8255891 = 12383837) B12383837
theorem B3971513 : Blo 1526460 3971513 := bstep (se 2 (by rfl) ⟨1489317, by rfl⟩ : syracuseStep 3971513 = 2978635) B2978635
theorem B2292155 : Blo 1526460 2292155 := bstep (se 1 (by rfl) ⟨1719116, by rfl⟩ : syracuseStep 2292155 = 3438233) B3438233
theorem B2292215 : Blo 1526460 2292215 := bstep (se 1 (by rfl) ⟨1719161, by rfl⟩ : syracuseStep 2292215 = 3438323) B3438323
theorem B4348417 : Blo 1526460 4348417 := bstep (se 2 (by rfl) ⟨1630656, by rfl⟩ : syracuseStep 4348417 = 3261313) B3261313
theorem B2292239 : Blo 1526460 2292239 := bstep (se 1 (by rfl) ⟨1719179, by rfl⟩ : syracuseStep 2292239 = 3438359) B3438359
theorem B2292281 : Blo 1526460 2292281 := bstep (se 2 (by rfl) ⟨859605, by rfl⟩ : syracuseStep 2292281 = 1719211) B1719211
theorem B4348475 : Blo 1526460 4348475 := bstep (se 1 (by rfl) ⟨3261356, by rfl⟩ : syracuseStep 4348475 = 6522713) B6522713
theorem B7731773 : Blo 1526460 7731773 := bstep (se 3 (by rfl) ⟨1449707, by rfl⟩ : syracuseStep 7731773 = 2899415) B2899415
theorem B18577997 : Blo 1526460 18577997 := bstep (se 3 (by rfl) ⟨3483374, by rfl⟩ : syracuseStep 18577997 = 6966749) B6966749
theorem B2292359 : Blo 1526460 2292359 := bstep (se 1 (by rfl) ⟨1719269, by rfl⟩ : syracuseStep 2292359 = 3438539) B3438539
theorem B2292395 : Blo 1526460 2292395 := bstep (se 1 (by rfl) ⟨1719296, by rfl⟩ : syracuseStep 2292395 = 3438593) B3438593
theorem B2292425 : Blo 1526460 2292425 := bstep (se 2 (by rfl) ⟨859659, by rfl⟩ : syracuseStep 2292425 = 1719319) B1719319
theorem B2063119 : Blo 1526460 2063119 := bstep (se 1 (by rfl) ⟨1547339, by rfl⟩ : syracuseStep 2063119 = 3094679) B3094679
theorem B2579215 : Blo 1526460 2579215 := bstep (se 1 (by rfl) ⟨1934411, by rfl⟩ : syracuseStep 2579215 = 3868823) B3868823
theorem B2292539 : Blo 1526460 2292539 := bstep (se 1 (by rfl) ⟨1719404, by rfl⟩ : syracuseStep 2292539 = 3438809) B3438809
theorem B3718007 : Blo 1526460 3718007 := bstep (se 1 (by rfl) ⟨2788505, by rfl⟩ : syracuseStep 3718007 = 5577011) B5577011
theorem B2292599 : Blo 1526460 2292599 := bstep (se 1 (by rfl) ⟨1719449, by rfl⟩ : syracuseStep 2292599 = 3438899) B3438899
theorem B2898823 : Blo 1526460 2898823 := bstep (se 1 (by rfl) ⟨2174117, by rfl⟩ : syracuseStep 2898823 = 4348235) B4348235
theorem B4242311 : Blo 1526460 4242311 := bstep (se 1 (by rfl) ⟨3181733, by rfl⟩ : syracuseStep 4242311 = 6363467) B6363467
theorem B1719175 : Blo 1526460 1719175 := bstep (se 1 (by rfl) ⟨1289381, by rfl⟩ : syracuseStep 1719175 = 2578763) B2578763
theorem B2292623 : Blo 1526460 2292623 := bstep (se 1 (by rfl) ⟨1719467, by rfl⟩ : syracuseStep 2292623 = 3438935) B3438935
theorem B3668921 : Blo 1526460 3668921 := bstep (se 2 (by rfl) ⟨1375845, by rfl⟩ : syracuseStep 3668921 = 2751691) B2751691
theorem B2292665 : Blo 1526460 2292665 := bstep (se 2 (by rfl) ⟨859749, by rfl⟩ : syracuseStep 2292665 = 1719499) B1719499
theorem B14883851 : Blo 1526460 14883851 := bstep (se 1 (by rfl) ⟨11162888, by rfl⟩ : syracuseStep 14883851 = 22325777) B22325777
theorem B1932331 : Blo 1526460 1932331 := bstep (se 1 (by rfl) ⟨1449248, by rfl⟩ : syracuseStep 1932331 = 2898497) B2898497
theorem B1719355 : Blo 1526460 1719355 := bstep (se 1 (by rfl) ⟨1289516, by rfl⟩ : syracuseStep 1719355 = 2579033) B2579033
theorem B3865715 : Blo 1526460 3865715 := bstep (se 1 (by rfl) ⟨2899286, by rfl⟩ : syracuseStep 3865715 = 5798573) B5798573
theorem B13229345 : Blo 1526460 13229345 := bstep (se 2 (by rfl) ⟨4961004, by rfl⟩ : syracuseStep 13229345 = 9922009) B9922009
theorem B44039483 : Blo 1526460 44039483 := bstep (se 1 (by rfl) ⟨33029612, by rfl⟩ : syracuseStep 44039483 = 66059225) B66059225
theorem B4406663 : Blo 1526460 4406663 := bstep (se 1 (by rfl) ⟨3304997, by rfl⟩ : syracuseStep 4406663 = 6609995) B6609995
theorem B2899385 : Blo 1526460 2899385 := bstep (se 2 (by rfl) ⟨1087269, by rfl⟩ : syracuseStep 2899385 = 2174539) B2174539
theorem B8699339 : Blo 1526460 8699339 := bstep (se 1 (by rfl) ⟨6524504, by rfl⟩ : syracuseStep 8699339 = 13049009) B13049009
theorem B5799377 : Blo 1526460 5799377 := bstep (se 2 (by rfl) ⟨2174766, by rfl⟩ : syracuseStep 5799377 = 4349533) B4349533
theorem B4644353 : Blo 1526460 4644353 := bstep (se 2 (by rfl) ⟨1741632, by rfl⟩ : syracuseStep 4644353 = 3483265) B3483265
theorem B24763907 : Blo 1526460 24763907 := bstep (se 1 (by rfl) ⟨18572930, by rfl⟩ : syracuseStep 24763907 = 37145861) B37145861
theorem B7339531 : Blo 1526460 7339531 := bstep (se 1 (by rfl) ⟨5504648, by rfl⟩ : syracuseStep 7339531 = 11009297) B11009297
theorem B6520439 : Blo 1526460 6520439 := bstep (se 1 (by rfl) ⟨4890329, by rfl⟩ : syracuseStep 6520439 = 9780659) B9780659
theorem B3866231 : Blo 1526460 3866231 := bstep (se 1 (by rfl) ⟨2899673, by rfl⟩ : syracuseStep 3866231 = 5799347) B5799347
theorem B8822465 : Blo 1526460 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B13942543 : Blo 1526460 13942543 := bstep (se 1 (by rfl) ⟨10456907, by rfl⟩ : syracuseStep 13942543 = 20913815) B20913815
theorem B2752289 : Blo 1526460 2752289 := bstep (se 2 (by rfl) ⟨1032108, by rfl⟩ : syracuseStep 2752289 = 2064217) B2064217
theorem B5152571 : Blo 1526460 5152571 := bstep (se 1 (by rfl) ⟨3864428, by rfl⟩ : syracuseStep 5152571 = 7728857) B7728857
theorem B8699795 : Blo 1526460 8699795 := bstep (se 1 (by rfl) ⟨6524846, by rfl⟩ : syracuseStep 8699795 = 13049693) B13049693
theorem B5799833 : Blo 1526460 5799833 := bstep (se 2 (by rfl) ⟨2174937, by rfl⟩ : syracuseStep 5799833 = 4349875) B4349875
theorem B5152787 : Blo 1526460 5152787 := bstep (se 1 (by rfl) ⟨3864590, by rfl⟩ : syracuseStep 5152787 = 7729181) B7729181
theorem B11010077 : Blo 1526460 11010077 := bstep (se 3 (by rfl) ⟨2064389, by rfl⟩ : syracuseStep 11010077 = 4128779) B4128779
theorem B8257625 : Blo 1526460 8257625 := bstep (se 2 (by rfl) ⟨3096609, by rfl⟩ : syracuseStep 8257625 = 6193219) B6193219
theorem B22012019 : Blo 1526460 22012019 := bstep (se 1 (by rfl) ⟨16509014, by rfl⟩ : syracuseStep 22012019 = 33018029) B33018029
theorem B5153111 : Blo 1526460 5153111 := bstep (se 1 (by rfl) ⟨3864833, by rfl⟩ : syracuseStep 5153111 = 7729667) B7729667
theorem B19562957 : Blo 1526460 19562957 := bstep (se 3 (by rfl) ⟨3668054, by rfl⟩ : syracuseStep 19562957 = 7336109) B7336109
theorem B5505499 : Blo 1526460 5505499 := bstep (se 1 (by rfl) ⟨4129124, by rfl⟩ : syracuseStep 5505499 = 8258249) B8258249
theorem B14680601 : Blo 1526460 14680601 := bstep (se 2 (by rfl) ⟨5505225, by rfl⟩ : syracuseStep 14680601 = 11010451) B11010451
theorem B4891175 : Blo 1526460 4891175 := bstep (se 1 (by rfl) ⟨3668381, by rfl⟩ : syracuseStep 4891175 = 7336763) B7336763
theorem B5882507 : Blo 1526460 5882507 := bstep (se 1 (by rfl) ⟨4411880, by rfl⟩ : syracuseStep 5882507 = 8823761) B8823761
theorem B3867335 : Blo 1526460 3867335 := bstep (se 1 (by rfl) ⟨2900501, by rfl⟩ : syracuseStep 3867335 = 5801003) B5801003
theorem B3867385 : Blo 1526460 3867385 := bstep (se 2 (by rfl) ⟨1450269, by rfl⟩ : syracuseStep 3867385 = 2900539) B2900539
theorem B2900843 : Blo 1526460 2900843 := bstep (se 1 (by rfl) ⟨2175632, by rfl⟩ : syracuseStep 2900843 = 4351265) B4351265
theorem B6194029 : Blo 1526460 6194029 := bstep (se 3 (by rfl) ⟨1161380, by rfl⟩ : syracuseStep 6194029 = 2322761) B2322761
theorem B22012823 : Blo 1526460 22012823 := bstep (se 1 (by rfl) ⟨16509617, by rfl⟩ : syracuseStep 22012823 = 33019235) B33019235
theorem B7340975 : Blo 1526460 7340975 := bstep (se 1 (by rfl) ⟨5505731, by rfl⟩ : syracuseStep 7340975 = 11011463) B11011463
theorem B8700979 : Blo 1526460 8700979 := bstep (se 1 (by rfl) ⟨6525734, by rfl⟩ : syracuseStep 8700979 = 13051469) B13051469
theorem B5801017 : Blo 1526460 5801017 := bstep (se 2 (by rfl) ⟨2175381, by rfl⟩ : syracuseStep 5801017 = 4350763) B4350763
theorem B4891727 : Blo 1526460 4891727 := bstep (se 1 (by rfl) ⟨3668795, by rfl⟩ : syracuseStep 4891727 = 7337591) B7337591
theorem B2901071 : Blo 1526460 2901071 := bstep (se 1 (by rfl) ⟨2175803, by rfl⟩ : syracuseStep 2901071 = 4351607) B4351607
theorem B19580075 : Blo 1526460 19580075 := bstep (se 1 (by rfl) ⟨14685056, by rfl⟩ : syracuseStep 19580075 = 29370113) B29370113
theorem B5801321 : Blo 1526460 5801321 := bstep (se 2 (by rfl) ⟨2175495, by rfl⟩ : syracuseStep 5801321 = 4350991) B4350991
theorem B3868033 : Blo 1526460 3868033 := bstep (se 2 (by rfl) ⟨1450512, by rfl⟩ : syracuseStep 3868033 = 2901025) B2901025
theorem B5154191 : Blo 1526460 5154191 := bstep (se 1 (by rfl) ⟨3865643, by rfl⟩ : syracuseStep 5154191 = 7731287) B7731287
theorem B1631707 : Blo 1526460 1631707 := bstep (se 1 (by rfl) ⟨1223780, by rfl⟩ : syracuseStep 1631707 = 2447561) B2447561
theorem B2901511 : Blo 1526460 2901511 := bstep (se 1 (by rfl) ⟨2176133, by rfl⟩ : syracuseStep 2901511 = 4352267) B4352267
theorem B9791063 : Blo 1526460 9791063 := bstep (se 1 (by rfl) ⟨7343297, by rfl⟩ : syracuseStep 9791063 = 14686595) B14686595
theorem B2647675 : Blo 1526460 2647675 := bstep (se 1 (by rfl) ⟨1985756, by rfl⟩ : syracuseStep 2647675 = 3971513) B3971513
theorem B5154515 : Blo 1526460 5154515 := bstep (se 1 (by rfl) ⟨3865886, by rfl⟩ : syracuseStep 5154515 = 7731773) B7731773
theorem B6194987 : Blo 1526460 6194987 := bstep (se 1 (by rfl) ⟨4646240, by rfl⟩ : syracuseStep 6194987 = 9292481) B9292481
theorem B17631071 : Blo 1526460 17631071 := bstep (se 1 (by rfl) ⟨13223303, by rfl⟩ : syracuseStep 17631071 = 26446607) B26446607
theorem B11011949 : Blo 1526460 11011949 := bstep (se 3 (by rfl) ⟨2064740, by rfl⟩ : syracuseStep 11011949 = 4129481) B4129481
theorem B2828207 : Blo 1526460 2828207 := bstep (se 1 (by rfl) ⟨2121155, by rfl⟩ : syracuseStep 2828207 = 4242311) B4242311
theorem B9922567 : Blo 1526460 9922567 := bstep (se 1 (by rfl) ⟨7441925, by rfl⟩ : syracuseStep 9922567 = 14883851) B14883851
theorem B5507129 : Blo 1526460 5507129 := bstep (se 2 (by rfl) ⟨2065173, by rfl⟩ : syracuseStep 5507129 = 4130347) B4130347
theorem B6523037 : Blo 1526460 6523037 := bstep (se 3 (by rfl) ⟨1223069, by rfl⟩ : syracuseStep 6523037 = 2446139) B2446139
theorem B5507243 : Blo 1526460 5507243 := bstep (se 1 (by rfl) ⟨4130432, by rfl⟩ : syracuseStep 5507243 = 8260865) B8260865
theorem B3868843 : Blo 1526460 3868843 := bstep (se 1 (by rfl) ⟨2901632, by rfl⟩ : syracuseStep 3868843 = 5803265) B5803265
theorem B16509271 : Blo 1526460 16509271 := bstep (se 1 (by rfl) ⟨12381953, by rfl⟩ : syracuseStep 16509271 = 24763907) B24763907
theorem B17631593 : Blo 1526460 17631593 := bstep (se 2 (by rfl) ⟨6611847, by rfl⟩ : syracuseStep 17631593 = 13223695) B13223695
theorem B18590057 : Blo 1526460 18590057 := bstep (se 2 (by rfl) ⟨6971271, by rfl⟩ : syracuseStep 18590057 = 13942543) B13942543
theorem B3435047 : Blo 1526460 3435047 := bstep (se 1 (by rfl) ⟨2576285, by rfl⟩ : syracuseStep 3435047 = 5152571) B5152571
theorem B1526471 : Blo 1526460 1526471 := bstep (se 1 (by rfl) ⟨1144853, by rfl⟩ : syracuseStep 1526471 = 2289707) B2289707
theorem B1526491 : Blo 1526460 1526491 := bstep (se 1 (by rfl) ⟨1144868, by rfl⟩ : syracuseStep 1526491 = 2289737) B2289737
theorem B1526567 : Blo 1526460 1526567 := bstep (se 1 (by rfl) ⟨1144925, by rfl⟩ : syracuseStep 1526567 = 2289851) B2289851
theorem B1526607 : Blo 1526460 1526607 := bstep (se 1 (by rfl) ⟨1144955, by rfl⟩ : syracuseStep 1526607 = 2289911) B2289911
theorem B1526623 : Blo 1526460 1526623 := bstep (se 1 (by rfl) ⟨1144967, by rfl⟩ : syracuseStep 1526623 = 2289935) B2289935
theorem B3435371 : Blo 1526460 3435371 := bstep (se 1 (by rfl) ⟨2576528, by rfl⟩ : syracuseStep 3435371 = 5153057) B5153057
theorem B5155703 : Blo 1526460 5155703 := bstep (se 1 (by rfl) ⟨3866777, by rfl⟩ : syracuseStep 5155703 = 7733555) B7733555
theorem B1526651 : Blo 1526460 1526651 := bstep (se 1 (by rfl) ⟨1144988, by rfl⟩ : syracuseStep 1526651 = 2289977) B2289977
theorem B3435425 : Blo 1526460 3435425 := bstep (se 2 (by rfl) ⟨1288284, by rfl⟩ : syracuseStep 3435425 = 2576569) B2576569
theorem B7728047 : Blo 1526460 7728047 := bstep (se 1 (by rfl) ⟨5796035, by rfl⟩ : syracuseStep 7728047 = 11592071) B11592071
theorem B1526703 : Blo 1526460 1526703 := bstep (se 1 (by rfl) ⟨1145027, by rfl⟩ : syracuseStep 1526703 = 2290055) B2290055
theorem B1526727 : Blo 1526460 1526727 := bstep (se 1 (by rfl) ⟨1145045, by rfl⟩ : syracuseStep 1526727 = 2290091) B2290091
theorem B1526747 : Blo 1526460 1526747 := bstep (se 1 (by rfl) ⟨1145060, by rfl⟩ : syracuseStep 1526747 = 2290121) B2290121
theorem B1526823 : Blo 1526460 1526823 := bstep (se 1 (by rfl) ⟨1145117, by rfl⟩ : syracuseStep 1526823 = 2290235) B2290235
theorem B1526863 : Blo 1526460 1526863 := bstep (se 1 (by rfl) ⟨1145147, by rfl⟩ : syracuseStep 1526863 = 2290295) B2290295
theorem B5155919 : Blo 1526460 5155919 := bstep (se 1 (by rfl) ⟨3866939, by rfl⟩ : syracuseStep 5155919 = 7733879) B7733879
theorem B1526879 : Blo 1526460 1526879 := bstep (se 1 (by rfl) ⟨1145159, by rfl⟩ : syracuseStep 1526879 = 2290319) B2290319
theorem B1526907 : Blo 1526460 1526907 := bstep (se 1 (by rfl) ⟨1145180, by rfl⟩ : syracuseStep 1526907 = 2290361) B2290361
theorem B1526959 : Blo 1526460 1526959 := bstep (se 1 (by rfl) ⟨1145219, by rfl⟩ : syracuseStep 1526959 = 2290439) B2290439
theorem B1526983 : Blo 1526460 1526983 := bstep (se 1 (by rfl) ⟨1145237, by rfl⟩ : syracuseStep 1526983 = 2290475) B2290475
theorem B1527003 : Blo 1526460 1527003 := bstep (se 1 (by rfl) ⟨1145252, by rfl⟩ : syracuseStep 1527003 = 2290505) B2290505
theorem B3435767 : Blo 1526460 3435767 := bstep (se 1 (by rfl) ⟨2576825, by rfl⟩ : syracuseStep 3435767 = 5153651) B5153651
theorem B1527079 : Blo 1526460 1527079 := bstep (se 1 (by rfl) ⟨1145309, by rfl⟩ : syracuseStep 1527079 = 2290619) B2290619
theorem B1527119 : Blo 1526460 1527119 := bstep (se 1 (by rfl) ⟨1145339, by rfl⟩ : syracuseStep 1527119 = 2290679) B2290679
theorem B1527135 : Blo 1526460 1527135 := bstep (se 1 (by rfl) ⟨1145351, by rfl⟩ : syracuseStep 1527135 = 2290703) B2290703
theorem B1527163 : Blo 1526460 1527163 := bstep (se 1 (by rfl) ⟨1145372, by rfl⟩ : syracuseStep 1527163 = 2290745) B2290745
theorem B1527215 : Blo 1526460 1527215 := bstep (se 1 (by rfl) ⟨1145411, by rfl⟩ : syracuseStep 1527215 = 2290823) B2290823
theorem B1527239 : Blo 1526460 1527239 := bstep (se 1 (by rfl) ⟨1145429, by rfl⟩ : syracuseStep 1527239 = 2290859) B2290859
theorem B5156297 : Blo 1526460 5156297 := bstep (se 2 (by rfl) ⟨1933611, by rfl⟩ : syracuseStep 5156297 = 3867223) B3867223
theorem B1527259 : Blo 1526460 1527259 := bstep (se 1 (by rfl) ⟨1145444, by rfl⟩ : syracuseStep 1527259 = 2290889) B2290889
theorem B7736795 : Blo 1526460 7736795 := bstep (se 1 (by rfl) ⟨5802596, by rfl⟩ : syracuseStep 7736795 = 11605193) B11605193
theorem B1527335 : Blo 1526460 1527335 := bstep (se 1 (by rfl) ⟨1145501, by rfl⟩ : syracuseStep 1527335 = 2291003) B2291003
theorem B1527375 : Blo 1526460 1527375 := bstep (se 1 (by rfl) ⟨1145531, by rfl⟩ : syracuseStep 1527375 = 2291063) B2291063
theorem B1527391 : Blo 1526460 1527391 := bstep (se 1 (by rfl) ⟨1145543, by rfl⟩ : syracuseStep 1527391 = 2291087) B2291087
theorem B1527419 : Blo 1526460 1527419 := bstep (se 1 (by rfl) ⟨1145564, by rfl⟩ : syracuseStep 1527419 = 2291129) B2291129
theorem B1527471 : Blo 1526460 1527471 := bstep (se 1 (by rfl) ⟨1145603, by rfl⟩ : syracuseStep 1527471 = 2291207) B2291207
theorem B11751101 : Blo 1526460 11751101 := bstep (se 3 (by rfl) ⟨2203331, by rfl⟩ : syracuseStep 11751101 = 4406663) B4406663
theorem B1527495 : Blo 1526460 1527495 := bstep (se 1 (by rfl) ⟨1145621, by rfl⟩ : syracuseStep 1527495 = 2291243) B2291243
theorem B5156567 : Blo 1526460 5156567 := bstep (se 1 (by rfl) ⟨3867425, by rfl⟩ : syracuseStep 5156567 = 7734851) B7734851
theorem B1527515 : Blo 1526460 1527515 := bstep (se 1 (by rfl) ⟨1145636, by rfl⟩ : syracuseStep 1527515 = 2291273) B2291273
theorem B22015709 : Blo 1526460 22015709 := bstep (se 3 (by rfl) ⟨4127945, by rfl⟩ : syracuseStep 22015709 = 8255891) B8255891
theorem B11013853 : Blo 1526460 11013853 := bstep (se 3 (by rfl) ⟨2065097, by rfl⟩ : syracuseStep 11013853 = 4130195) B4130195
theorem B1527591 : Blo 1526460 1527591 := bstep (se 1 (by rfl) ⟨1145693, by rfl⟩ : syracuseStep 1527591 = 2291387) B2291387
theorem B3436361 : Blo 1526460 3436361 := bstep (se 2 (by rfl) ⟨1288635, by rfl⟩ : syracuseStep 3436361 = 2577271) B2577271
theorem B1527631 : Blo 1526460 1527631 := bstep (se 1 (by rfl) ⟨1145723, by rfl⟩ : syracuseStep 1527631 = 2291447) B2291447
theorem B1527647 : Blo 1526460 1527647 := bstep (se 1 (by rfl) ⟨1145735, by rfl⟩ : syracuseStep 1527647 = 2291471) B2291471
theorem B1527675 : Blo 1526460 1527675 := bstep (se 1 (by rfl) ⟨1145756, by rfl⟩ : syracuseStep 1527675 = 2291513) B2291513
theorem B3305377 : Blo 1526460 3305377 := bstep (se 2 (by rfl) ⟨1239516, by rfl⟩ : syracuseStep 3305377 = 2479033) B2479033
theorem B1527727 : Blo 1526460 1527727 := bstep (se 1 (by rfl) ⟨1145795, by rfl⟩ : syracuseStep 1527727 = 2291591) B2291591
theorem B5156783 : Blo 1526460 5156783 := bstep (se 1 (by rfl) ⟨3867587, by rfl⟩ : syracuseStep 5156783 = 7735175) B7735175
theorem B7737281 : Blo 1526460 7737281 := bstep (se 2 (by rfl) ⟨2901480, by rfl⟩ : syracuseStep 7737281 = 5802961) B5802961
theorem B1527751 : Blo 1526460 1527751 := bstep (se 1 (by rfl) ⟨1145813, by rfl⟩ : syracuseStep 1527751 = 2291627) B2291627
theorem B1527771 : Blo 1526460 1527771 := bstep (se 1 (by rfl) ⟨1145828, by rfl⟩ : syracuseStep 1527771 = 2291657) B2291657
theorem B2445319 : Blo 1526460 2445319 := bstep (se 1 (by rfl) ⟨1833989, by rfl⟩ : syracuseStep 2445319 = 3667979) B3667979
theorem B4894739 : Blo 1526460 4894739 := bstep (se 1 (by rfl) ⟨3671054, by rfl⟩ : syracuseStep 4894739 = 7342109) B7342109
theorem B1527847 : Blo 1526460 1527847 := bstep (se 1 (by rfl) ⟨1145885, by rfl⟩ : syracuseStep 1527847 = 2291771) B2291771
theorem B2576441 : Blo 1526460 2576441 := bstep (se 2 (by rfl) ⟨966165, by rfl⟩ : syracuseStep 2576441 = 1932331) B1932331
theorem B2289743 : Blo 1526460 2289743 := bstep (se 1 (by rfl) ⟨1717307, by rfl⟩ : syracuseStep 2289743 = 3434615) B3434615
theorem B1527887 : Blo 1526460 1527887 := bstep (se 1 (by rfl) ⟨1145915, by rfl⟩ : syracuseStep 1527887 = 2291831) B2291831
theorem B1527903 : Blo 1526460 1527903 := bstep (se 1 (by rfl) ⟨1145927, by rfl⟩ : syracuseStep 1527903 = 2291855) B2291855
theorem B13054067 : Blo 1526460 13054067 := bstep (se 1 (by rfl) ⟨9790550, by rfl⟩ : syracuseStep 13054067 = 19581101) B19581101
theorem B1527931 : Blo 1526460 1527931 := bstep (se 1 (by rfl) ⟨1145948, by rfl⟩ : syracuseStep 1527931 = 2291897) B2291897
theorem B1527983 : Blo 1526460 1527983 := bstep (se 1 (by rfl) ⟨1145987, by rfl⟩ : syracuseStep 1527983 = 2291975) B2291975
theorem B2289863 : Blo 1526460 2289863 := bstep (se 1 (by rfl) ⟨1717397, by rfl⟩ : syracuseStep 2289863 = 3434795) B3434795
theorem B1528007 : Blo 1526460 1528007 := bstep (se 1 (by rfl) ⟨1146005, by rfl⟩ : syracuseStep 1528007 = 2292011) B2292011
theorem B1528027 : Blo 1526460 1528027 := bstep (se 1 (by rfl) ⟨1146020, by rfl⟩ : syracuseStep 1528027 = 2292041) B2292041
theorem B1528103 : Blo 1526460 1528103 := bstep (se 1 (by rfl) ⟨1146077, by rfl⟩ : syracuseStep 1528103 = 2292155) B2292155
theorem B5796157 : Blo 1526460 5796157 := bstep (se 3 (by rfl) ⟨1086779, by rfl⟩ : syracuseStep 5796157 = 2173559) B2173559
theorem B1528143 : Blo 1526460 1528143 := bstep (se 1 (by rfl) ⟨1146107, by rfl⟩ : syracuseStep 1528143 = 2292215) B2292215
theorem B1528159 : Blo 1526460 1528159 := bstep (se 1 (by rfl) ⟨1146119, by rfl⟩ : syracuseStep 1528159 = 2292239) B2292239
theorem B5222761 : Blo 1526460 5222761 := bstep (se 2 (by rfl) ⟨1958535, by rfl⟩ : syracuseStep 5222761 = 3917071) B3917071
theorem B2290025 : Blo 1526460 2290025 := bstep (se 2 (by rfl) ⟨858759, by rfl⟩ : syracuseStep 2290025 = 1717519) B1717519
theorem B1528187 : Blo 1526460 1528187 := bstep (se 1 (by rfl) ⟨1146140, by rfl⟩ : syracuseStep 1528187 = 2292281) B2292281
theorem B1528239 : Blo 1526460 1528239 := bstep (se 1 (by rfl) ⟨1146179, by rfl⟩ : syracuseStep 1528239 = 2292359) B2292359
theorem B2290103 : Blo 1526460 2290103 := bstep (se 1 (by rfl) ⟨1717577, by rfl⟩ : syracuseStep 2290103 = 3435155) B3435155
theorem B1528263 : Blo 1526460 1528263 := bstep (se 1 (by rfl) ⟨1146197, by rfl⟩ : syracuseStep 1528263 = 2292395) B2292395
theorem B2290139 : Blo 1526460 2290139 := bstep (se 1 (by rfl) ⟨1717604, by rfl⟩ : syracuseStep 2290139 = 3435209) B3435209
theorem B1528283 : Blo 1526460 1528283 := bstep (se 1 (by rfl) ⟨1146212, by rfl⟩ : syracuseStep 1528283 = 2292425) B2292425
theorem B7344665 : Blo 1526460 7344665 := bstep (se 2 (by rfl) ⟨2754249, by rfl⟩ : syracuseStep 7344665 = 5508499) B5508499
theorem B1528359 : Blo 1526460 1528359 := bstep (se 1 (by rfl) ⟨1146269, by rfl⟩ : syracuseStep 1528359 = 2292539) B2292539
theorem B2478671 : Blo 1526460 2478671 := bstep (se 1 (by rfl) ⟨1859003, by rfl⟩ : syracuseStep 2478671 = 3718007) B3718007
theorem B1528399 : Blo 1526460 1528399 := bstep (se 1 (by rfl) ⟨1146299, by rfl⟩ : syracuseStep 1528399 = 2292599) B2292599
theorem B1528415 : Blo 1526460 1528415 := bstep (se 1 (by rfl) ⟨1146311, by rfl⟩ : syracuseStep 1528415 = 2292623) B2292623
theorem B3437153 : Blo 1526460 3437153 := bstep (se 2 (by rfl) ⟨1288932, by rfl⟩ : syracuseStep 3437153 = 2577865) B2577865
theorem B44634725 : Blo 1526460 44634725 := bstep (se 4 (by rfl) ⟨4184505, by rfl⟩ : syracuseStep 44634725 = 8369011) B8369011
theorem B2445947 : Blo 1526460 2445947 := bstep (se 1 (by rfl) ⟨1834460, by rfl⟩ : syracuseStep 2445947 = 3668921) B3668921
theorem B1528443 : Blo 1526460 1528443 := bstep (se 1 (by rfl) ⟨1146332, by rfl⟩ : syracuseStep 1528443 = 2292665) B2292665
theorem B9786041 : Blo 1526460 9786041 := bstep (se 2 (by rfl) ⟨3669765, by rfl⟩ : syracuseStep 9786041 = 7339531) B7339531
theorem B4895417 : Blo 1526460 4895417 := bstep (se 2 (by rfl) ⟨1835781, by rfl⟩ : syracuseStep 4895417 = 3671563) B3671563
theorem B2577143 : Blo 1526460 2577143 := bstep (se 1 (by rfl) ⟨1932857, by rfl⟩ : syracuseStep 2577143 = 3865715) B3865715
theorem B8696605 : Blo 1526460 8696605 := bstep (se 3 (by rfl) ⟨1630613, by rfl⟩ : syracuseStep 8696605 = 3261227) B3261227
theorem B8819563 : Blo 1526460 8819563 := bstep (se 1 (by rfl) ⟨6614672, by rfl⟩ : syracuseStep 8819563 = 13229345) B13229345
theorem B2290607 : Blo 1526460 2290607 := bstep (se 1 (by rfl) ⟨1717955, by rfl⟩ : syracuseStep 2290607 = 3435911) B3435911
theorem B3437495 : Blo 1526460 3437495 := bstep (se 1 (by rfl) ⟨2578121, by rfl⟩ : syracuseStep 3437495 = 5156243) B5156243
theorem B2290697 : Blo 1526460 2290697 := bstep (se 2 (by rfl) ⟨859011, by rfl⟩ : syracuseStep 2290697 = 1718023) B1718023
theorem B2290727 : Blo 1526460 2290727 := bstep (se 1 (by rfl) ⟨1718045, by rfl⟩ : syracuseStep 2290727 = 3436091) B3436091
theorem B4346959 : Blo 1526460 4346959 := bstep (se 1 (by rfl) ⟨3260219, by rfl⟩ : syracuseStep 4346959 = 6520439) B6520439
theorem B2577487 : Blo 1526460 2577487 := bstep (se 1 (by rfl) ⟨1933115, by rfl⟩ : syracuseStep 2577487 = 3866231) B3866231
theorem B17396855 : Blo 1526460 17396855 := bstep (se 1 (by rfl) ⟨13047641, by rfl⟩ : syracuseStep 17396855 = 26095283) B26095283
theorem B2290811 : Blo 1526460 2290811 := bstep (se 1 (by rfl) ⟨1718108, by rfl⟩ : syracuseStep 2290811 = 3436217) B3436217
theorem B16741529 : Blo 1526460 16741529 := bstep (se 2 (by rfl) ⟨6278073, by rfl⟩ : syracuseStep 16741529 = 12556147) B12556147
theorem B1717447 : Blo 1526460 1717447 := bstep (se 1 (by rfl) ⟨1288085, by rfl⟩ : syracuseStep 1717447 = 2576171) B2576171
theorem B2290937 : Blo 1526460 2290937 := bstep (se 2 (by rfl) ⟨859101, by rfl⟩ : syracuseStep 2290937 = 1718203) B1718203
theorem B19576079 : Blo 1526460 19576079 := bstep (se 1 (by rfl) ⟨14682059, by rfl⟩ : syracuseStep 19576079 = 29364119) B29364119
theorem B2577737 : Blo 1526460 2577737 := bstep (se 2 (by rfl) ⟨966651, by rfl⟩ : syracuseStep 2577737 = 1933303) B1933303
theorem B2291039 : Blo 1526460 2291039 := bstep (se 1 (by rfl) ⟨1718279, by rfl⟩ : syracuseStep 2291039 = 3436559) B3436559
theorem B2291051 : Blo 1526460 2291051 := bstep (se 1 (by rfl) ⟨1718288, by rfl⟩ : syracuseStep 2291051 = 3436577) B3436577
theorem B9917897 : Blo 1526460 9917897 := bstep (se 2 (by rfl) ⟨3719211, by rfl⟩ : syracuseStep 9917897 = 7438423) B7438423
theorem B3438089 : Blo 1526460 3438089 := bstep (se 2 (by rfl) ⟨1289283, by rfl⟩ : syracuseStep 3438089 = 2578567) B2578567
theorem B13399613 : Blo 1526460 13399613 := bstep (se 3 (by rfl) ⟨2512427, by rfl⟩ : syracuseStep 13399613 = 5024855) B5024855
theorem B2291279 : Blo 1526460 2291279 := bstep (se 1 (by rfl) ⟨1718459, by rfl⟩ : syracuseStep 2291279 = 3436919) B3436919
theorem B23549537 : Blo 1526460 23549537 := bstep (se 2 (by rfl) ⟨8831076, by rfl⟩ : syracuseStep 23549537 = 17662153) B17662153
theorem B2291399 : Blo 1526460 2291399 := bstep (se 1 (by rfl) ⟨1718549, by rfl⟩ : syracuseStep 2291399 = 3437099) B3437099
theorem B2578169 : Blo 1526460 2578169 := bstep (se 2 (by rfl) ⟨966813, by rfl⟩ : syracuseStep 2578169 = 1933627) B1933627
theorem B3438431 : Blo 1526460 3438431 := bstep (se 1 (by rfl) ⟨2578823, by rfl⟩ : syracuseStep 3438431 = 5157647) B5157647
theorem B2291561 : Blo 1526460 2291561 := bstep (se 2 (by rfl) ⟨859335, by rfl⟩ : syracuseStep 2291561 = 1718671) B1718671
theorem B2578351 : Blo 1526460 2578351 := bstep (se 1 (by rfl) ⟨1933763, by rfl⟩ : syracuseStep 2578351 = 3867527) B3867527
theorem B24762293 : Blo 1526460 24762293 := bstep (se 5 (by rfl) ⟨1160732, by rfl⟩ : syracuseStep 24762293 = 2321465) B2321465
theorem B2291639 : Blo 1526460 2291639 := bstep (se 1 (by rfl) ⟨1718729, by rfl⟩ : syracuseStep 2291639 = 3437459) B3437459
theorem B11155409 : Blo 1526460 11155409 := bstep (se 2 (by rfl) ⟨4183278, by rfl⟩ : syracuseStep 11155409 = 8366557) B8366557
theorem B2291675 : Blo 1526460 2291675 := bstep (se 1 (by rfl) ⟨1718756, by rfl⟩ : syracuseStep 2291675 = 3437513) B3437513
theorem B5797889 : Blo 1526460 5797889 := bstep (se 2 (by rfl) ⟨2174208, by rfl⟩ : syracuseStep 5797889 = 4348417) B4348417
theorem B2897927 : Blo 1526460 2897927 := bstep (se 1 (by rfl) ⟨2173445, by rfl⟩ : syracuseStep 2897927 = 4346891) B4346891
theorem B2578439 : Blo 1526460 2578439 := bstep (se 1 (by rfl) ⟨1933829, by rfl⟩ : syracuseStep 2578439 = 3867659) B3867659
theorem B3438611 : Blo 1526460 3438611 := bstep (se 1 (by rfl) ⟨2578958, by rfl⟩ : syracuseStep 3438611 = 5157917) B5157917
theorem B1718311 : Blo 1526460 1718311 := bstep (se 1 (by rfl) ⟨1288733, by rfl⟩ : syracuseStep 1718311 = 2577467) B2577467
theorem B50894905 : Blo 1526460 50894905 := bstep (se 2 (by rfl) ⟨19085589, by rfl⟩ : syracuseStep 50894905 = 38171179) B38171179
theorem B4126799 : Blo 1526460 4126799 := bstep (se 1 (by rfl) ⟨3095099, by rfl⟩ : syracuseStep 4126799 = 6190199) B6190199
theorem B4348075 : Blo 1526460 4348075 := bstep (se 1 (by rfl) ⟨3261056, by rfl⟩ : syracuseStep 4348075 = 6522113) B6522113
theorem B2578783 : Blo 1526460 2578783 := bstep (se 1 (by rfl) ⟨1934087, by rfl⟩ : syracuseStep 2578783 = 3868175) B3868175
theorem B2750825 : Blo 1526460 2750825 := bstep (se 2 (by rfl) ⟨1031559, by rfl⟩ : syracuseStep 2750825 = 2063119) B2063119
theorem B3438953 : Blo 1526460 3438953 := bstep (se 2 (by rfl) ⟨1289607, by rfl⟩ : syracuseStep 3438953 = 2579215) B2579215
theorem B2898337 : Blo 1526460 2898337 := bstep (se 2 (by rfl) ⟨1086876, by rfl⟩ : syracuseStep 2898337 = 2173753) B2173753
theorem B2292143 : Blo 1526460 2292143 := bstep (se 1 (by rfl) ⟨1719107, by rfl⟩ : syracuseStep 2292143 = 3438215) B3438215
theorem B2578871 : Blo 1526460 2578871 := bstep (se 1 (by rfl) ⟨1934153, by rfl⟩ : syracuseStep 2578871 = 3868307) B3868307
theorem B3865097 : Blo 1526460 3865097 := bstep (se 2 (by rfl) ⟨1449411, by rfl⟩ : syracuseStep 3865097 = 2898823) B2898823
theorem B2292233 : Blo 1526460 2292233 := bstep (se 2 (by rfl) ⟨859587, by rfl⟩ : syracuseStep 2292233 = 1719175) B1719175
theorem B2292263 : Blo 1526460 2292263 := bstep (se 1 (by rfl) ⟨1719197, by rfl⟩ : syracuseStep 2292263 = 3438395) B3438395
theorem B2292347 : Blo 1526460 2292347 := bstep (se 1 (by rfl) ⟨1719260, by rfl⟩ : syracuseStep 2292347 = 3438521) B3438521
theorem B2898679 : Blo 1526460 2898679 := bstep (se 1 (by rfl) ⟨2174009, by rfl⟩ : syracuseStep 2898679 = 4348019) B4348019
theorem B2292473 : Blo 1526460 2292473 := bstep (se 2 (by rfl) ⟨859677, by rfl⟩ : syracuseStep 2292473 = 1719355) B1719355
theorem B2448119 : Blo 1526460 2448119 := bstep (se 1 (by rfl) ⟨1836089, by rfl⟩ : syracuseStep 2448119 = 3672179) B3672179
theorem B2292575 : Blo 1526460 2292575 := bstep (se 1 (by rfl) ⟨1719431, by rfl⟩ : syracuseStep 2292575 = 3438863) B3438863
theorem B2292587 : Blo 1526460 2292587 := bstep (se 1 (by rfl) ⟨1719440, by rfl⟩ : syracuseStep 2292587 = 3438881) B3438881
theorem B59554739 : Blo 1526460 59554739 := bstep (se 1 (by rfl) ⟨44666054, by rfl⟩ : syracuseStep 59554739 = 89332109) B89332109
theorem B2898983 : Blo 1526460 2898983 := bstep (se 1 (by rfl) ⟨2174237, by rfl⟩ : syracuseStep 2898983 = 4348475) B4348475
theorem B12385331 : Blo 1526460 12385331 := bstep (se 1 (by rfl) ⟨9288998, by rfl⟩ : syracuseStep 12385331 = 18577997) B18577997
theorem B18586903 : Blo 1526460 18586903 := bstep (se 1 (by rfl) ⟨13940177, by rfl⟩ : syracuseStep 18586903 = 27880355) B27880355
theorem B20913497 : Blo 1526460 20913497 := bstep (se 2 (by rfl) ⟨7842561, by rfl⟩ : syracuseStep 20913497 = 15685123) B15685123
theorem B4185473 : Blo 1526460 4185473 := bstep (se 2 (by rfl) ⟨1569552, by rfl⟩ : syracuseStep 4185473 = 3139105) B3139105
theorem B3096073 : Blo 1526460 3096073 := bstep (se 2 (by rfl) ⟨1161027, by rfl⟩ : syracuseStep 3096073 = 2322055) B2322055
theorem B29359655 : Blo 1526460 29359655 := bstep (se 1 (by rfl) ⟨22019741, by rfl⟩ : syracuseStep 29359655 = 44039483) B44039483
theorem B1932923 : Blo 1526460 1932923 := bstep (se 1 (by rfl) ⟨1449692, by rfl⟩ : syracuseStep 1932923 = 2899385) B2899385
theorem B5799559 : Blo 1526460 5799559 := bstep (se 1 (by rfl) ⟨4349669, by rfl⟩ : syracuseStep 5799559 = 8699339) B8699339
theorem B3866251 : Blo 1526460 3866251 := bstep (se 1 (by rfl) ⟨2899688, by rfl⟩ : syracuseStep 3866251 = 5799377) B5799377
theorem B3096235 : Blo 1526460 3096235 := bstep (se 1 (by rfl) ⟨2322176, by rfl⟩ : syracuseStep 3096235 = 4644353) B4644353
theorem B6971129 : Blo 1526460 6971129 := bstep (se 2 (by rfl) ⟨2614173, by rfl⟩ : syracuseStep 6971129 = 5228347) B5228347
theorem B5881643 : Blo 1526460 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B1834859 : Blo 1526460 1834859 := bstep (se 1 (by rfl) ⟨1376144, by rfl⟩ : syracuseStep 1834859 = 2752289) B2752289
theorem B11591585 : Blo 1526460 11591585 := bstep (se 2 (by rfl) ⟨4346844, by rfl⟩ : syracuseStep 11591585 = 8693689) B8693689
theorem B5799863 : Blo 1526460 5799863 := bstep (se 1 (by rfl) ⟨4349897, by rfl⟩ : syracuseStep 5799863 = 8699795) B8699795
theorem B3866555 : Blo 1526460 3866555 := bstep (se 1 (by rfl) ⟨2899916, by rfl⟩ : syracuseStep 3866555 = 5799833) B5799833
theorem B3260425 : Blo 1526460 3260425 := bstep (se 2 (by rfl) ⟨1222659, by rfl⟩ : syracuseStep 3260425 = 2445319) B2445319
theorem B13230089 : Blo 1526460 13230089 := bstep (se 2 (by rfl) ⟨4961283, by rfl⟩ : syracuseStep 13230089 = 9922567) B9922567
theorem B7340051 : Blo 1526460 7340051 := bstep (se 1 (by rfl) ⟨5505038, by rfl⟩ : syracuseStep 7340051 = 11010077) B11010077
theorem B5505083 : Blo 1526460 5505083 := bstep (se 1 (by rfl) ⟨4128812, by rfl⟩ : syracuseStep 5505083 = 8257625) B8257625
theorem B13041971 : Blo 1526460 13041971 := bstep (se 1 (by rfl) ⟨9781478, by rfl⟩ : syracuseStep 13041971 = 19562957) B19562957
theorem B3260783 : Blo 1526460 3260783 := bstep (se 1 (by rfl) ⟨2445587, by rfl⟩ : syracuseStep 3260783 = 4891175) B4891175
theorem B1630631 : Blo 1526460 1630631 := bstep (se 1 (by rfl) ⟨1222973, by rfl⟩ : syracuseStep 1630631 = 2445947) B2445947
theorem B22012361 : Blo 1526460 22012361 := bstep (se 2 (by rfl) ⟨8254635, by rfl⟩ : syracuseStep 22012361 = 16509271) B16509271
theorem B1933895 : Blo 1526460 1933895 := bstep (se 1 (by rfl) ⟨1450421, by rfl⟩ : syracuseStep 1933895 = 2900843) B2900843
theorem B3261151 : Blo 1526460 3261151 := bstep (se 1 (by rfl) ⟨2445863, by rfl⟩ : syracuseStep 3261151 = 4891727) B4891727
theorem B1934047 : Blo 1526460 1934047 := bstep (se 1 (by rfl) ⟨1450535, by rfl⟩ : syracuseStep 1934047 = 2901071) B2901071
theorem B13050719 : Blo 1526460 13050719 := bstep (se 1 (by rfl) ⟨9788039, by rfl⟩ : syracuseStep 13050719 = 19576079) B19576079
theorem B3867547 : Blo 1526460 3867547 := bstep (se 1 (by rfl) ⟨2900660, by rfl⟩ : syracuseStep 3867547 = 5801321) B5801321
theorem B8258705 : Blo 1526460 8258705 := bstep (se 2 (by rfl) ⟨3097014, by rfl⟩ : syracuseStep 8258705 = 6194029) B6194029
theorem B4129991 : Blo 1526460 4129991 := bstep (se 1 (by rfl) ⟨3097493, by rfl⟩ : syracuseStep 4129991 = 6194987) B6194987
theorem B7341299 : Blo 1526460 7341299 := bstep (se 1 (by rfl) ⟨5505974, by rfl⟩ : syracuseStep 7341299 = 11011949) B11011949
theorem B16508195 : Blo 1526460 16508195 := bstep (se 1 (by rfl) ⟨12381146, by rfl⟩ : syracuseStep 16508195 = 24762293) B24762293
theorem B3671419 : Blo 1526460 3671419 := bstep (se 1 (by rfl) ⟨2753564, by rfl⟩ : syracuseStep 3671419 = 5507129) B5507129
theorem B11601305 : Blo 1526460 11601305 := bstep (se 2 (by rfl) ⟨4350489, by rfl⟩ : syracuseStep 11601305 = 8700979) B8700979
theorem B7734689 : Blo 1526460 7734689 := bstep (se 2 (by rfl) ⟨2900508, by rfl⟩ : syracuseStep 7734689 = 5801017) B5801017
theorem B3671495 : Blo 1526460 3671495 := bstep (se 1 (by rfl) ⟨2753621, by rfl⟩ : syracuseStep 3671495 = 5507243) B5507243
theorem B5154461 : Blo 1526460 5154461 := bstep (se 3 (by rfl) ⟨966461, by rfl⟩ : syracuseStep 5154461 = 1932923) B1932923
theorem B24782537 : Blo 1526460 24782537 := bstep (se 2 (by rfl) ⟨9293451, by rfl⟩ : syracuseStep 24782537 = 18586903) B18586903
theorem B1632079 : Blo 1526460 1632079 := bstep (se 1 (by rfl) ⟨1224059, by rfl⟩ : syracuseStep 1632079 = 2448119) B2448119
theorem B3868681 : Blo 1526460 3868681 := bstep (se 2 (by rfl) ⟨1450755, by rfl⟩ : syracuseStep 3868681 = 2901511) B2901511
theorem B5155001 : Blo 1526460 5155001 := bstep (se 2 (by rfl) ⟨1933125, by rfl⟩ : syracuseStep 5155001 = 3866251) B3866251
theorem B4892957 : Blo 1526460 4892957 := bstep (se 3 (by rfl) ⟨917429, by rfl⟩ : syracuseStep 4892957 = 1834859) B1834859
theorem B19573103 : Blo 1526460 19573103 := bstep (se 1 (by rfl) ⟨14679827, by rfl⟩ : syracuseStep 19573103 = 29359655) B29359655
theorem B7834067 : Blo 1526460 7834067 := bstep (se 1 (by rfl) ⟨5875550, by rfl⟩ : syracuseStep 7834067 = 11751101) B11751101
theorem B29362661 : Blo 1526460 29362661 := bstep (se 4 (by rfl) ⟨2752749, by rfl⟩ : syracuseStep 29362661 = 5505499) B5505499
theorem B8702437 : Blo 1526460 8702437 := bstep (se 4 (by rfl) ⟨815853, by rfl⟩ : syracuseStep 8702437 = 1631707) B1631707
theorem B4647419 : Blo 1526460 4647419 := bstep (se 1 (by rfl) ⟨3485564, by rfl⟩ : syracuseStep 4647419 = 6971129) B6971129
theorem B7727723 : Blo 1526460 7727723 := bstep (se 1 (by rfl) ⟨5795792, by rfl⟩ : syracuseStep 7727723 = 11591585) B11591585
theorem B3435191 : Blo 1526460 3435191 := bstep (se 1 (by rfl) ⟨2576393, by rfl⟩ : syracuseStep 3435191 = 5152787) B5152787
theorem B3263159 : Blo 1526460 3263159 := bstep (se 1 (by rfl) ⟨2447369, by rfl⟩ : syracuseStep 3263159 = 4894739) B4894739
theorem B1526495 : Blo 1526460 1526495 := bstep (se 1 (by rfl) ⟨1144871, by rfl⟩ : syracuseStep 1526495 = 2289743) B2289743
theorem B14674679 : Blo 1526460 14674679 := bstep (se 1 (by rfl) ⟨11006009, by rfl⟩ : syracuseStep 14674679 = 22012019) B22012019
theorem B8702711 : Blo 1526460 8702711 := bstep (se 1 (by rfl) ⟨6527033, by rfl⟩ : syracuseStep 8702711 = 13054067) B13054067
theorem B1526575 : Blo 1526460 1526575 := bstep (se 1 (by rfl) ⟨1144931, by rfl⟩ : syracuseStep 1526575 = 2289863) B2289863
theorem B11004797 : Blo 1526460 11004797 := bstep (se 3 (by rfl) ⟨2063399, by rfl⟩ : syracuseStep 11004797 = 4126799) B4126799
theorem B3435407 : Blo 1526460 3435407 := bstep (se 1 (by rfl) ⟨2576555, by rfl⟩ : syracuseStep 3435407 = 5153111) B5153111
theorem B1526683 : Blo 1526460 1526683 := bstep (se 1 (by rfl) ⟨1145012, by rfl⟩ : syracuseStep 1526683 = 2290025) B2290025
theorem B1526735 : Blo 1526460 1526735 := bstep (se 1 (by rfl) ⟨1145051, by rfl⟩ : syracuseStep 1526735 = 2290103) B2290103
theorem B1526759 : Blo 1526460 1526759 := bstep (se 1 (by rfl) ⟨1145069, by rfl⟩ : syracuseStep 1526759 = 2290139) B2290139
theorem B29756483 : Blo 1526460 29756483 := bstep (se 1 (by rfl) ⟨22317362, by rfl⟩ : syracuseStep 29756483 = 44634725) B44634725
theorem B7728209 : Blo 1526460 7728209 := bstep (se 2 (by rfl) ⟨2898078, by rfl⟩ : syracuseStep 7728209 = 5796157) B5796157
theorem B6524027 : Blo 1526460 6524027 := bstep (se 1 (by rfl) ⟨4893020, by rfl⟩ : syracuseStep 6524027 = 9786041) B9786041
theorem B14675215 : Blo 1526460 14675215 := bstep (se 1 (by rfl) ⟨11006411, by rfl⟩ : syracuseStep 14675215 = 22012823) B22012823
theorem B1527071 : Blo 1526460 1527071 := bstep (se 1 (by rfl) ⟨1145303, by rfl⟩ : syracuseStep 1527071 = 2290607) B2290607
theorem B4893983 : Blo 1526460 4893983 := bstep (se 1 (by rfl) ⟨3670487, by rfl⟩ : syracuseStep 4893983 = 7340975) B7340975
theorem B1527131 : Blo 1526460 1527131 := bstep (se 1 (by rfl) ⟨1145348, by rfl⟩ : syracuseStep 1527131 = 2290697) B2290697
theorem B1527151 : Blo 1526460 1527151 := bstep (se 1 (by rfl) ⟨1145363, by rfl⟩ : syracuseStep 1527151 = 2290727) B2290727
theorem B1527207 : Blo 1526460 1527207 := bstep (se 1 (by rfl) ⟨1145405, by rfl⟩ : syracuseStep 1527207 = 2290811) B2290811
theorem B11161019 : Blo 1526460 11161019 := bstep (se 1 (by rfl) ⟨8370764, by rfl⟩ : syracuseStep 11161019 = 16741529) B16741529
theorem B13053383 : Blo 1526460 13053383 := bstep (se 1 (by rfl) ⟨9790037, by rfl⟩ : syracuseStep 13053383 = 19580075) B19580075
theorem B1527291 : Blo 1526460 1527291 := bstep (se 1 (by rfl) ⟨1145468, by rfl⟩ : syracuseStep 1527291 = 2290937) B2290937
theorem B1527359 : Blo 1526460 1527359 := bstep (se 1 (by rfl) ⟨1145519, by rfl⟩ : syracuseStep 1527359 = 2291039) B2291039
theorem B1527367 : Blo 1526460 1527367 := bstep (se 1 (by rfl) ⟨1145525, by rfl⟩ : syracuseStep 1527367 = 2291051) B2291051
theorem B3436127 : Blo 1526460 3436127 := bstep (se 1 (by rfl) ⟨2577095, by rfl⟩ : syracuseStep 3436127 = 5154191) B5154191
theorem B5156513 : Blo 1526460 5156513 := bstep (se 2 (by rfl) ⟨1933692, by rfl⟩ : syracuseStep 5156513 = 3867385) B3867385
theorem B11161261 : Blo 1526460 11161261 := bstep (se 3 (by rfl) ⟨2092736, by rfl⟩ : syracuseStep 11161261 = 4185473) B4185473
theorem B11595473 : Blo 1526460 11595473 := bstep (se 2 (by rfl) ⟨4348302, by rfl⟩ : syracuseStep 11595473 = 8696605) B8696605
theorem B8933075 : Blo 1526460 8933075 := bstep (se 1 (by rfl) ⟨6699806, by rfl⟩ : syracuseStep 8933075 = 13399613) B13399613
theorem B1527519 : Blo 1526460 1527519 := bstep (se 1 (by rfl) ⟨1145639, by rfl⟩ : syracuseStep 1527519 = 2291279) B2291279
theorem B15699691 : Blo 1526460 15699691 := bstep (se 1 (by rfl) ⟨11774768, by rfl⟩ : syracuseStep 15699691 = 23549537) B23549537
theorem B1527599 : Blo 1526460 1527599 := bstep (se 1 (by rfl) ⟨1145699, by rfl⟩ : syracuseStep 1527599 = 2291399) B2291399
theorem B3436343 : Blo 1526460 3436343 := bstep (se 1 (by rfl) ⟨2577257, by rfl⟩ : syracuseStep 3436343 = 5154515) B5154515
theorem B11759417 : Blo 1526460 11759417 := bstep (se 2 (by rfl) ⟨4409781, by rfl⟩ : syracuseStep 11759417 = 8819563) B8819563
theorem B26447725 : Blo 1526460 26447725 := bstep (se 3 (by rfl) ⟨4958948, by rfl⟩ : syracuseStep 26447725 = 9917897) B9917897
theorem B1527707 : Blo 1526460 1527707 := bstep (se 1 (by rfl) ⟨1145780, by rfl⟩ : syracuseStep 1527707 = 2291561) B2291561
theorem B1527759 : Blo 1526460 1527759 := bstep (se 1 (by rfl) ⟨1145819, by rfl⟩ : syracuseStep 1527759 = 2291639) B2291639
theorem B1527783 : Blo 1526460 1527783 := bstep (se 1 (by rfl) ⟨1145837, by rfl⟩ : syracuseStep 1527783 = 2291675) B2291675
theorem B5795945 : Blo 1526460 5795945 := bstep (se 2 (by rfl) ⟨2173479, by rfl⟩ : syracuseStep 5795945 = 4346959) B4346959
theorem B3436649 : Blo 1526460 3436649 := bstep (se 2 (by rfl) ⟨1288743, by rfl⟩ : syracuseStep 3436649 = 2577487) B2577487
theorem B2289929 : Blo 1526460 2289929 := bstep (se 2 (by rfl) ⟨858723, by rfl⟩ : syracuseStep 2289929 = 1717447) B1717447
theorem B1528095 : Blo 1526460 1528095 := bstep (se 1 (by rfl) ⟨1146071, by rfl⟩ : syracuseStep 1528095 = 2292143) B2292143
theorem B2576731 : Blo 1526460 2576731 := bstep (se 1 (by rfl) ⟨1932548, by rfl⟩ : syracuseStep 2576731 = 3865097) B3865097
theorem B1528155 : Blo 1526460 1528155 := bstep (se 1 (by rfl) ⟨1146116, by rfl⟩ : syracuseStep 1528155 = 2292233) B2292233
theorem B2290031 : Blo 1526460 2290031 := bstep (se 1 (by rfl) ⟨1717523, by rfl⟩ : syracuseStep 2290031 = 3435047) B3435047
theorem B1528175 : Blo 1526460 1528175 := bstep (se 1 (by rfl) ⟨1146131, by rfl⟩ : syracuseStep 1528175 = 2292263) B2292263
theorem B1528231 : Blo 1526460 1528231 := bstep (se 1 (by rfl) ⟨1146173, by rfl⟩ : syracuseStep 1528231 = 2292347) B2292347
theorem B13054445 : Blo 1526460 13054445 := bstep (se 3 (by rfl) ⟨2447708, by rfl⟩ : syracuseStep 13054445 = 4895417) B4895417
theorem B1528315 : Blo 1526460 1528315 := bstep (se 1 (by rfl) ⟨1146236, by rfl⟩ : syracuseStep 1528315 = 2292473) B2292473
theorem B5157377 : Blo 1526460 5157377 := bstep (se 2 (by rfl) ⟨1934016, by rfl⟩ : syracuseStep 5157377 = 3868033) B3868033
theorem B1528383 : Blo 1526460 1528383 := bstep (se 1 (by rfl) ⟨1146287, by rfl⟩ : syracuseStep 1528383 = 2292575) B2292575
theorem B2290247 : Blo 1526460 2290247 := bstep (se 1 (by rfl) ⟨1717685, by rfl⟩ : syracuseStep 2290247 = 3435371) B3435371
theorem B1528391 : Blo 1526460 1528391 := bstep (se 1 (by rfl) ⟨1146293, by rfl⟩ : syracuseStep 1528391 = 2292587) B2292587
theorem B3437135 : Blo 1526460 3437135 := bstep (se 1 (by rfl) ⟨2577851, by rfl⟩ : syracuseStep 3437135 = 5155703) B5155703
theorem B2290283 : Blo 1526460 2290283 := bstep (se 1 (by rfl) ⟨1717712, by rfl⟩ : syracuseStep 2290283 = 3435425) B3435425
theorem B39703159 : Blo 1526460 39703159 := bstep (se 1 (by rfl) ⟨29777369, by rfl⟩ : syracuseStep 39703159 = 59554739) B59554739
theorem B3437279 : Blo 1526460 3437279 := bstep (se 1 (by rfl) ⟨2577959, by rfl⟩ : syracuseStep 3437279 = 5155919) B5155919
theorem B2290511 : Blo 1526460 2290511 := bstep (se 1 (by rfl) ⟨1717883, by rfl⟩ : syracuseStep 2290511 = 3435767) B3435767
theorem B14685137 : Blo 1526460 14685137 := bstep (se 2 (by rfl) ⟨5506926, by rfl⟩ : syracuseStep 14685137 = 11013853) B11013853
theorem B3437531 : Blo 1526460 3437531 := bstep (se 1 (by rfl) ⟨2578148, by rfl⟩ : syracuseStep 3437531 = 5156297) B5156297
theorem B5157863 : Blo 1526460 5157863 := bstep (se 1 (by rfl) ⟨3868397, by rfl⟩ : syracuseStep 5157863 = 7736795) B7736795
theorem B7541885 : Blo 1526460 7541885 := bstep (se 3 (by rfl) ⟨1414103, by rfl⟩ : syracuseStep 7541885 = 2828207) B2828207
theorem B3437711 : Blo 1526460 3437711 := bstep (se 1 (by rfl) ⟨2578283, by rfl⟩ : syracuseStep 3437711 = 5156567) B5156567
theorem B14677139 : Blo 1526460 14677139 := bstep (se 1 (by rfl) ⟨11007854, by rfl⟩ : syracuseStep 14677139 = 22015709) B22015709
theorem B3921095 : Blo 1526460 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B2290907 : Blo 1526460 2290907 := bstep (se 1 (by rfl) ⟨1718180, by rfl⟩ : syracuseStep 2290907 = 3436361) B3436361
theorem B3437801 : Blo 1526460 3437801 := bstep (se 2 (by rfl) ⟨1289175, by rfl⟩ : syracuseStep 3437801 = 2578351) B2578351
theorem B3437855 : Blo 1526460 3437855 := bstep (se 1 (by rfl) ⟨2578391, by rfl⟩ : syracuseStep 3437855 = 5156783) B5156783
theorem B2577703 : Blo 1526460 2577703 := bstep (se 1 (by rfl) ⟨1933277, by rfl⟩ : syracuseStep 2577703 = 3866555) B3866555
theorem B5158187 : Blo 1526460 5158187 := bstep (se 1 (by rfl) ⟨3868640, by rfl⟩ : syracuseStep 5158187 = 7737281) B7737281
theorem B1717627 : Blo 1526460 1717627 := bstep (se 1 (by rfl) ⟨1288220, by rfl⟩ : syracuseStep 1717627 = 2576441) B2576441
theorem B2291081 : Blo 1526460 2291081 := bstep (se 2 (by rfl) ⟨859155, by rfl⟩ : syracuseStep 2291081 = 1718311) B1718311
theorem B67859873 : Blo 1526460 67859873 := bstep (se 2 (by rfl) ⟨25447452, by rfl⟩ : syracuseStep 67859873 = 50894905) B50894905
theorem B5797433 : Blo 1526460 5797433 := bstep (se 2 (by rfl) ⟨2174037, by rfl⟩ : syracuseStep 5797433 = 4348075) B4348075
theorem B5158457 : Blo 1526460 5158457 := bstep (se 2 (by rfl) ⟨1934421, by rfl⟩ : syracuseStep 5158457 = 3868843) B3868843
theorem B9787067 : Blo 1526460 9787067 := bstep (se 1 (by rfl) ⟨7340300, by rfl⟩ : syracuseStep 9787067 = 14680601) B14680601
theorem B4896443 : Blo 1526460 4896443 := bstep (se 1 (by rfl) ⟨3672332, by rfl⟩ : syracuseStep 4896443 = 7344665) B7344665
theorem B1652447 : Blo 1526460 1652447 := bstep (se 1 (by rfl) ⟨1239335, by rfl⟩ : syracuseStep 1652447 = 2478671) B2478671
theorem B2291435 : Blo 1526460 2291435 := bstep (se 1 (by rfl) ⟨1718576, by rfl⟩ : syracuseStep 2291435 = 3437153) B3437153
theorem B3921671 : Blo 1526460 3921671 := bstep (se 1 (by rfl) ⟨2941253, by rfl⟩ : syracuseStep 3921671 = 5882507) B5882507
theorem B3438377 : Blo 1526460 3438377 := bstep (se 2 (by rfl) ⟨1289391, by rfl⟩ : syracuseStep 3438377 = 2578783) B2578783
theorem B2578223 : Blo 1526460 2578223 := bstep (se 1 (by rfl) ⟨1933667, by rfl⟩ : syracuseStep 2578223 = 3867335) B3867335
theorem B1718095 : Blo 1526460 1718095 := bstep (se 1 (by rfl) ⟨1288571, by rfl⟩ : syracuseStep 1718095 = 2577143) B2577143
theorem B3864449 : Blo 1526460 3864449 := bstep (se 2 (by rfl) ⟨1449168, by rfl⟩ : syracuseStep 3864449 = 2898337) B2898337
theorem B2291663 : Blo 1526460 2291663 := bstep (se 1 (by rfl) ⟨1718747, by rfl⟩ : syracuseStep 2291663 = 3437495) B3437495
theorem B11597903 : Blo 1526460 11597903 := bstep (se 1 (by rfl) ⟨8698427, by rfl⟩ : syracuseStep 11597903 = 17396855) B17396855
theorem B1718491 : Blo 1526460 1718491 := bstep (se 1 (by rfl) ⟨1288868, by rfl⟩ : syracuseStep 1718491 = 2577737) B2577737
theorem B16513253 : Blo 1526460 16513253 := bstep (se 4 (by rfl) ⟨1548117, by rfl⟩ : syracuseStep 16513253 = 3096235) B3096235
theorem B3864905 : Blo 1526460 3864905 := bstep (se 2 (by rfl) ⟨1449339, by rfl⟩ : syracuseStep 3864905 = 2898679) B2898679
theorem B2292059 : Blo 1526460 2292059 := bstep (se 1 (by rfl) ⟨1719044, by rfl⟩ : syracuseStep 2292059 = 3438089) B3438089
theorem B6527375 : Blo 1526460 6527375 := bstep (se 1 (by rfl) ⟨4895531, by rfl⟩ : syracuseStep 6527375 = 9791063) B9791063
theorem B1718779 : Blo 1526460 1718779 := bstep (se 1 (by rfl) ⟨1289084, by rfl⟩ : syracuseStep 1718779 = 2578169) B2578169
theorem B11754047 : Blo 1526460 11754047 := bstep (se 1 (by rfl) ⟨8815535, by rfl⟩ : syracuseStep 11754047 = 17631071) B17631071
theorem B2292287 : Blo 1526460 2292287 := bstep (se 1 (by rfl) ⟨1719215, by rfl⟩ : syracuseStep 2292287 = 3438431) B3438431
theorem B7436939 : Blo 1526460 7436939 := bstep (se 1 (by rfl) ⟨5577704, by rfl⟩ : syracuseStep 7436939 = 11155409) B11155409
theorem B3865259 : Blo 1526460 3865259 := bstep (se 1 (by rfl) ⟨2898944, by rfl⟩ : syracuseStep 3865259 = 5797889) B5797889
theorem B1931951 : Blo 1526460 1931951 := bstep (se 1 (by rfl) ⟨1448963, by rfl⟩ : syracuseStep 1931951 = 2897927) B2897927
theorem B1718959 : Blo 1526460 1718959 := bstep (se 1 (by rfl) ⟨1289219, by rfl⟩ : syracuseStep 1718959 = 2578439) B2578439
theorem B2292407 : Blo 1526460 2292407 := bstep (se 1 (by rfl) ⟨1719305, by rfl⟩ : syracuseStep 2292407 = 3438611) B3438611
theorem B4348691 : Blo 1526460 4348691 := bstep (se 1 (by rfl) ⟨3261518, by rfl⟩ : syracuseStep 4348691 = 6523037) B6523037
theorem B1833883 : Blo 1526460 1833883 := bstep (se 1 (by rfl) ⟨1375412, by rfl⟩ : syracuseStep 1833883 = 2750825) B2750825
theorem B11754395 : Blo 1526460 11754395 := bstep (se 1 (by rfl) ⟨8815796, by rfl⟩ : syracuseStep 11754395 = 17631593) B17631593
theorem B12393371 : Blo 1526460 12393371 := bstep (se 1 (by rfl) ⟨9295028, by rfl⟩ : syracuseStep 12393371 = 18590057) B18590057
theorem B2292635 : Blo 1526460 2292635 := bstep (se 1 (by rfl) ⟨1719476, by rfl⟩ : syracuseStep 2292635 = 3438953) B3438953
theorem B1719247 : Blo 1526460 1719247 := bstep (se 1 (by rfl) ⟨1289435, by rfl⟩ : syracuseStep 1719247 = 2578871) B2578871
theorem B5152031 : Blo 1526460 5152031 := bstep (se 1 (by rfl) ⟨3864023, by rfl⟩ : syracuseStep 5152031 = 7728047) B7728047
theorem B4128097 : Blo 1526460 4128097 := bstep (se 2 (by rfl) ⟨1548036, by rfl⟩ : syracuseStep 4128097 = 3096073) B3096073
theorem B1932655 : Blo 1526460 1932655 := bstep (se 1 (by rfl) ⟨1449491, by rfl⟩ : syracuseStep 1932655 = 2898983) B2898983
theorem B8256887 : Blo 1526460 8256887 := bstep (se 1 (by rfl) ⟨6192665, by rfl⟩ : syracuseStep 8256887 = 12385331) B12385331
theorem B3530233 : Blo 1526460 3530233 := bstep (se 2 (by rfl) ⟨1323837, by rfl⟩ : syracuseStep 3530233 = 2647675) B2647675
theorem B17628677 : Blo 1526460 17628677 := bstep (se 4 (by rfl) ⟨1652688, by rfl⟩ : syracuseStep 17628677 = 3305377) B3305377
theorem B7732745 : Blo 1526460 7732745 := bstep (se 2 (by rfl) ⟨2899779, by rfl⟩ : syracuseStep 7732745 = 5799559) B5799559
theorem B111418901 : Blo 1526460 111418901 := bstep (se 6 (by rfl) ⟨2611380, by rfl⟩ : syracuseStep 111418901 = 5222761) B5222761
theorem B13942331 : Blo 1526460 13942331 := bstep (se 1 (by rfl) ⟨10456748, by rfl⟩ : syracuseStep 13942331 = 20913497) B20913497
theorem B3866575 : Blo 1526460 3866575 := bstep (se 1 (by rfl) ⟨2899931, by rfl⟩ : syracuseStep 3866575 = 5799863) B5799863
theorem B3670055 : Blo 1526460 3670055 := bstep (se 1 (by rfl) ⟨2752541, by rfl⟩ : syracuseStep 3670055 = 5505083) B5505083
theorem B8700479 : Blo 1526460 8700479 := bstep (se 1 (by rfl) ⟨6525359, by rfl⟩ : syracuseStep 8700479 = 13050719) B13050719
theorem B9790091 : Blo 1526460 9790091 := bstep (se 1 (by rfl) ⟨7342568, by rfl⟩ : syracuseStep 9790091 = 14685137) B14685137
theorem B5505803 : Blo 1526460 5505803 := bstep (se 1 (by rfl) ⟨4129352, by rfl⟩ : syracuseStep 5505803 = 8258705) B8258705
theorem B2753327 : Blo 1526460 2753327 := bstep (se 1 (by rfl) ⟨2064995, by rfl⟩ : syracuseStep 2753327 = 4129991) B4129991
theorem B52937545 : Blo 1526460 52937545 := bstep (se 2 (by rfl) ⟨19851579, by rfl⟩ : syracuseStep 52937545 = 39703159) B39703159
theorem B7734203 : Blo 1526460 7734203 := bstep (se 1 (by rfl) ⟨5800652, by rfl⟩ : syracuseStep 7734203 = 11601305) B11601305
theorem B2614447 : Blo 1526460 2614447 := bstep (se 1 (by rfl) ⟨1960835, by rfl⟩ : syracuseStep 2614447 = 3921671) B3921671
theorem B3261971 : Blo 1526460 3261971 := bstep (se 1 (by rfl) ⟨2446478, by rfl⟩ : syracuseStep 3261971 = 4892957) B4892957
theorem B4351583 : Blo 1526460 4351583 := bstep (se 1 (by rfl) ⟨3263687, by rfl⟩ : syracuseStep 4351583 = 6527375) B6527375
theorem B3098279 : Blo 1526460 3098279 := bstep (se 1 (by rfl) ⟨2323709, by rfl⟩ : syracuseStep 3098279 = 4647419) B4647419
theorem B9783119 : Blo 1526460 9783119 := bstep (se 1 (by rfl) ⟨7337339, by rfl⟩ : syracuseStep 9783119 = 14674679) B14674679
theorem B5801807 : Blo 1526460 5801807 := bstep (se 1 (by rfl) ⟨4351355, by rfl⟩ : syracuseStep 5801807 = 8702711) B8702711
theorem B3434687 : Blo 1526460 3434687 := bstep (se 1 (by rfl) ⟨2576015, by rfl⟩ : syracuseStep 3434687 = 5152031) B5152031
theorem B3262655 : Blo 1526460 3262655 := bstep (se 1 (by rfl) ⟨2446991, by rfl⟩ : syracuseStep 3262655 = 4893983) B4893983
theorem B7440679 : Blo 1526460 7440679 := bstep (se 1 (by rfl) ⟨5580509, by rfl⟩ : syracuseStep 7440679 = 11161019) B11161019
theorem B8702255 : Blo 1526460 8702255 := bstep (se 1 (by rfl) ⟨6526691, by rfl⟩ : syracuseStep 8702255 = 13053383) B13053383
theorem B20932921 : Blo 1526460 20932921 := bstep (se 2 (by rfl) ⟨7849845, by rfl⟩ : syracuseStep 20932921 = 15699691) B15699691
theorem B5155163 : Blo 1526460 5155163 := bstep (se 1 (by rfl) ⟨3866372, by rfl⟩ : syracuseStep 5155163 = 7732745) B7732745
theorem B74279267 : Blo 1526460 74279267 := bstep (se 1 (by rfl) ⟨55709450, by rfl⟩ : syracuseStep 74279267 = 111418901) B111418901
theorem B5155433 : Blo 1526460 5155433 := bstep (se 2 (by rfl) ⟨1933287, by rfl⟩ : syracuseStep 5155433 = 3866575) B3866575
theorem B4893367 : Blo 1526460 4893367 := bstep (se 1 (by rfl) ⟨3670025, by rfl⟩ : syracuseStep 4893367 = 7340051) B7340051
theorem B1526619 : Blo 1526460 1526619 := bstep (se 1 (by rfl) ⟨1144964, by rfl⟩ : syracuseStep 1526619 = 2289929) B2289929
theorem B8694647 : Blo 1526460 8694647 := bstep (se 1 (by rfl) ⟨6520985, by rfl⟩ : syracuseStep 8694647 = 13041971) B13041971
theorem B1526687 : Blo 1526460 1526687 := bstep (se 1 (by rfl) ⟨1145015, by rfl⟩ : syracuseStep 1526687 = 2290031) B2290031
theorem B14674907 : Blo 1526460 14674907 := bstep (se 1 (by rfl) ⟨11006180, by rfl⟩ : syracuseStep 14674907 = 22012361) B22012361
theorem B8702963 : Blo 1526460 8702963 := bstep (se 1 (by rfl) ⟨6527222, by rfl⟩ : syracuseStep 8702963 = 13054445) B13054445
theorem B1526831 : Blo 1526460 1526831 := bstep (se 1 (by rfl) ⟨1145123, by rfl⟩ : syracuseStep 1526831 = 2290247) B2290247
theorem B1526855 : Blo 1526460 1526855 := bstep (se 1 (by rfl) ⟨1145141, by rfl⟩ : syracuseStep 1526855 = 2290283) B2290283
theorem B3435641 : Blo 1526460 3435641 := bstep (se 2 (by rfl) ⟨1288365, by rfl⟩ : syracuseStep 3435641 = 2576731) B2576731
theorem B10456253 : Blo 1526460 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B1527007 : Blo 1526460 1527007 := bstep (se 1 (by rfl) ⟨1145255, by rfl⟩ : syracuseStep 1527007 = 2290511) B2290511
theorem B11603249 : Blo 1526460 11603249 := bstep (se 2 (by rfl) ⟨4351218, by rfl⟩ : syracuseStep 11603249 = 8702437) B8702437
theorem B9784759 : Blo 1526460 9784759 := bstep (se 1 (by rfl) ⟨7338569, by rfl⟩ : syracuseStep 9784759 = 14677139) B14677139
theorem B1527271 : Blo 1526460 1527271 := bstep (se 1 (by rfl) ⟨1145453, by rfl⟩ : syracuseStep 1527271 = 2290907) B2290907
theorem B4894199 : Blo 1526460 4894199 := bstep (se 1 (by rfl) ⟨3670649, by rfl⟩ : syracuseStep 4894199 = 7341299) B7341299
theorem B11005463 : Blo 1526460 11005463 := bstep (se 1 (by rfl) ⟨8254097, by rfl⟩ : syracuseStep 11005463 = 16508195) B16508195
theorem B1527387 : Blo 1526460 1527387 := bstep (se 1 (by rfl) ⟨1145540, by rfl⟩ : syracuseStep 1527387 = 2291081) B2291081
theorem B45239915 : Blo 1526460 45239915 := bstep (se 1 (by rfl) ⟨33929936, by rfl⟩ : syracuseStep 45239915 = 67859873) B67859873
theorem B5156459 : Blo 1526460 5156459 := bstep (se 1 (by rfl) ⟨3867344, by rfl⟩ : syracuseStep 5156459 = 7734689) B7734689
theorem B8695421 : Blo 1526460 8695421 := bstep (se 3 (by rfl) ⟨1630391, by rfl⟩ : syracuseStep 8695421 = 3260783) B3260783
theorem B3436307 : Blo 1526460 3436307 := bstep (se 1 (by rfl) ⟨2577230, by rfl⟩ : syracuseStep 3436307 = 5154461) B5154461
theorem B6524711 : Blo 1526460 6524711 := bstep (se 1 (by rfl) ⟨4893533, by rfl⟩ : syracuseStep 6524711 = 9787067) B9787067
theorem B3264295 : Blo 1526460 3264295 := bstep (se 1 (by rfl) ⟨2448221, by rfl⟩ : syracuseStep 3264295 = 4896443) B4896443
theorem B1527623 : Blo 1526460 1527623 := bstep (se 1 (by rfl) ⟨1145717, by rfl⟩ : syracuseStep 1527623 = 2291435) B2291435
theorem B5156729 : Blo 1526460 5156729 := bstep (se 2 (by rfl) ⟨1933773, by rfl⟩ : syracuseStep 5156729 = 3867547) B3867547
theorem B2576299 : Blo 1526460 2576299 := bstep (se 1 (by rfl) ⟨1932224, by rfl⟩ : syracuseStep 2576299 = 3864449) B3864449
theorem B1527775 : Blo 1526460 1527775 := bstep (se 1 (by rfl) ⟨1145831, by rfl⟩ : syracuseStep 1527775 = 2291663) B2291663
theorem B3436667 : Blo 1526460 3436667 := bstep (se 1 (by rfl) ⟨2577500, by rfl⟩ : syracuseStep 3436667 = 5155001) B5155001
theorem B5157053 : Blo 1526460 5157053 := bstep (se 3 (by rfl) ⟨966947, by rfl⟩ : syracuseStep 5157053 = 1933895) B1933895
theorem B2576603 : Blo 1526460 2576603 := bstep (se 1 (by rfl) ⟨1932452, by rfl⟩ : syracuseStep 2576603 = 3864905) B3864905
theorem B1528039 : Blo 1526460 1528039 := bstep (se 1 (by rfl) ⟨1146029, by rfl⟩ : syracuseStep 1528039 = 2292059) B2292059
theorem B5222711 : Blo 1526460 5222711 := bstep (se 1 (by rfl) ⟨3917033, by rfl⟩ : syracuseStep 5222711 = 7834067) B7834067
theorem B19575107 : Blo 1526460 19575107 := bstep (se 1 (by rfl) ⟨14681330, by rfl⟩ : syracuseStep 19575107 = 29362661) B29362661
theorem B19566953 : Blo 1526460 19566953 := bstep (se 2 (by rfl) ⟨7337607, by rfl⟩ : syracuseStep 19566953 = 14675215) B14675215
theorem B7836031 : Blo 1526460 7836031 := bstep (se 1 (by rfl) ⟨5877023, by rfl⟩ : syracuseStep 7836031 = 11754047) B11754047
theorem B1528191 : Blo 1526460 1528191 := bstep (se 1 (by rfl) ⟨1146143, by rfl⟩ : syracuseStep 1528191 = 2292287) B2292287
theorem B3436937 : Blo 1526460 3436937 := bstep (se 2 (by rfl) ⟨1288851, by rfl⟩ : syracuseStep 3436937 = 2577703) B2577703
theorem B8704421 : Blo 1526460 8704421 := bstep (se 4 (by rfl) ⟨816039, by rfl⟩ : syracuseStep 8704421 = 1632079) B1632079
theorem B2576839 : Blo 1526460 2576839 := bstep (se 1 (by rfl) ⟨1932629, by rfl⟩ : syracuseStep 2576839 = 3865259) B3865259
theorem B2290127 : Blo 1526460 2290127 := bstep (se 1 (by rfl) ⟨1717595, by rfl⟩ : syracuseStep 2290127 = 3435191) B3435191
theorem B2175439 : Blo 1526460 2175439 := bstep (se 1 (by rfl) ⟨1631579, by rfl⟩ : syracuseStep 2175439 = 3263159) B3263159
theorem B1528271 : Blo 1526460 1528271 := bstep (se 1 (by rfl) ⟨1146203, by rfl⟩ : syracuseStep 1528271 = 2292407) B2292407
theorem B2576873 : Blo 1526460 2576873 := bstep (se 2 (by rfl) ⟨966327, by rfl⟩ : syracuseStep 2576873 = 1932655) B1932655
theorem B2290169 : Blo 1526460 2290169 := bstep (se 2 (by rfl) ⟨858813, by rfl⟩ : syracuseStep 2290169 = 1717627) B1717627
theorem B4895225 : Blo 1526460 4895225 := bstep (se 2 (by rfl) ⟨1835709, by rfl⟩ : syracuseStep 4895225 = 3671419) B3671419
theorem B7336531 : Blo 1526460 7336531 := bstep (se 1 (by rfl) ⟨5502398, by rfl⟩ : syracuseStep 7336531 = 11004797) B11004797
theorem B2290271 : Blo 1526460 2290271 := bstep (se 1 (by rfl) ⟨1717703, by rfl⟩ : syracuseStep 2290271 = 3435407) B3435407
theorem B7836263 : Blo 1526460 7836263 := bstep (se 1 (by rfl) ⟨5877197, by rfl⟩ : syracuseStep 7836263 = 11754395) B11754395
theorem B8262247 : Blo 1526460 8262247 := bstep (se 1 (by rfl) ⟨6196685, by rfl⟩ : syracuseStep 8262247 = 12393371) B12393371
theorem B1528423 : Blo 1526460 1528423 := bstep (se 1 (by rfl) ⟨1146317, by rfl⟩ : syracuseStep 1528423 = 2292635) B2292635
theorem B4706977 : Blo 1526460 4706977 := bstep (se 2 (by rfl) ⟨1765116, by rfl⟩ : syracuseStep 4706977 = 3530233) B3530233
theorem B19837655 : Blo 1526460 19837655 := bstep (se 1 (by rfl) ⟨14878241, by rfl⟩ : syracuseStep 19837655 = 29756483) B29756483
theorem B14881681 : Blo 1526460 14881681 := bstep (se 2 (by rfl) ⟨5580630, by rfl⟩ : syracuseStep 14881681 = 11161261) B11161261
theorem B11752451 : Blo 1526460 11752451 := bstep (se 1 (by rfl) ⟨8814338, by rfl⟩ : syracuseStep 11752451 = 17628677) B17628677
theorem B9294887 : Blo 1526460 9294887 := bstep (se 1 (by rfl) ⟨6971165, by rfl⟩ : syracuseStep 9294887 = 13942331) B13942331
theorem B2290751 : Blo 1526460 2290751 := bstep (se 1 (by rfl) ⟨1718063, by rfl⟩ : syracuseStep 2290751 = 3436127) B3436127
theorem B2290793 : Blo 1526460 2290793 := bstep (se 2 (by rfl) ⟨859047, by rfl⟩ : syracuseStep 2290793 = 1718095) B1718095
theorem B3437675 : Blo 1526460 3437675 := bstep (se 1 (by rfl) ⟨2578256, by rfl⟩ : syracuseStep 3437675 = 5156513) B5156513
theorem B7730315 : Blo 1526460 7730315 := bstep (se 1 (by rfl) ⟨5797736, by rfl⟩ : syracuseStep 7730315 = 11595473) B11595473
theorem B35263633 : Blo 1526460 35263633 := bstep (se 2 (by rfl) ⟨13223862, by rfl⟩ : syracuseStep 35263633 = 26447725) B26447725
theorem B2290895 : Blo 1526460 2290895 := bstep (se 1 (by rfl) ⟨1718171, by rfl⟩ : syracuseStep 2290895 = 3436343) B3436343
theorem B8820059 : Blo 1526460 8820059 := bstep (se 1 (by rfl) ⟨6615044, by rfl⟩ : syracuseStep 8820059 = 13230089) B13230089
theorem B4347233 : Blo 1526460 4347233 := bstep (se 2 (by rfl) ⟨1630212, by rfl⟩ : syracuseStep 4347233 = 3260425) B3260425
theorem B5158241 : Blo 1526460 5158241 := bstep (se 2 (by rfl) ⟨1934340, by rfl⟩ : syracuseStep 5158241 = 3868681) B3868681
theorem B3863963 : Blo 1526460 3863963 := bstep (se 1 (by rfl) ⟨2897972, by rfl⟩ : syracuseStep 3863963 = 5795945) B5795945
theorem B2291099 : Blo 1526460 2291099 := bstep (se 1 (by rfl) ⟨1718324, by rfl⟩ : syracuseStep 2291099 = 3436649) B3436649
theorem B2291321 : Blo 1526460 2291321 := bstep (se 2 (by rfl) ⟨859245, by rfl⟩ : syracuseStep 2291321 = 1718491) B1718491
theorem B3438251 : Blo 1526460 3438251 := bstep (se 1 (by rfl) ⟨2578688, by rfl⟩ : syracuseStep 3438251 = 5157377) B5157377
theorem B2291423 : Blo 1526460 2291423 := bstep (se 1 (by rfl) ⟨1718567, by rfl⟩ : syracuseStep 2291423 = 3437135) B3437135
theorem B2291519 : Blo 1526460 2291519 := bstep (se 1 (by rfl) ⟨1718639, by rfl⟩ : syracuseStep 2291519 = 3437279) B3437279
theorem B2291687 : Blo 1526460 2291687 := bstep (se 1 (by rfl) ⟨1718765, by rfl⟩ : syracuseStep 2291687 = 3437531) B3437531
theorem B3438575 : Blo 1526460 3438575 := bstep (se 1 (by rfl) ⟨2578931, by rfl⟩ : syracuseStep 3438575 = 5157863) B5157863
theorem B2291705 : Blo 1526460 2291705 := bstep (se 2 (by rfl) ⟨859389, by rfl⟩ : syracuseStep 2291705 = 1718779) B1718779
theorem B5027923 : Blo 1526460 5027923 := bstep (se 1 (by rfl) ⟨3770942, by rfl⟩ : syracuseStep 5027923 = 7541885) B7541885
theorem B2291807 : Blo 1526460 2291807 := bstep (se 1 (by rfl) ⟨1718855, by rfl⟩ : syracuseStep 2291807 = 3437711) B3437711
theorem B2291867 : Blo 1526460 2291867 := bstep (se 1 (by rfl) ⟨1718900, by rfl⟩ : syracuseStep 2291867 = 3437801) B3437801
theorem B2291903 : Blo 1526460 2291903 := bstep (se 1 (by rfl) ⟨1718927, by rfl⟩ : syracuseStep 2291903 = 3437855) B3437855
theorem B3438791 : Blo 1526460 3438791 := bstep (se 1 (by rfl) ⟨2579093, by rfl⟩ : syracuseStep 3438791 = 5158187) B5158187
theorem B2291945 : Blo 1526460 2291945 := bstep (se 2 (by rfl) ⟨859479, by rfl⟩ : syracuseStep 2291945 = 1718959) B1718959
theorem B4348201 : Blo 1526460 4348201 := bstep (se 2 (by rfl) ⟨1630575, by rfl⟩ : syracuseStep 4348201 = 3261151) B3261151
theorem B2578729 : Blo 1526460 2578729 := bstep (se 2 (by rfl) ⟨967023, by rfl⟩ : syracuseStep 2578729 = 1934047) B1934047
theorem B2447663 : Blo 1526460 2447663 := bstep (se 1 (by rfl) ⟨1835747, by rfl⟩ : syracuseStep 2447663 = 3671495) B3671495
theorem B3864955 : Blo 1526460 3864955 := bstep (se 1 (by rfl) ⟨2898716, by rfl⟩ : syracuseStep 3864955 = 5797433) B5797433
theorem B3438971 : Blo 1526460 3438971 := bstep (se 1 (by rfl) ⟨2579228, by rfl⟩ : syracuseStep 3438971 = 5158457) B5158457
theorem B4348349 : Blo 1526460 4348349 := bstep (se 3 (by rfl) ⟨815315, by rfl⟩ : syracuseStep 4348349 = 1630631) B1630631
theorem B16521691 : Blo 1526460 16521691 := bstep (se 1 (by rfl) ⟨12391268, by rfl⟩ : syracuseStep 16521691 = 24782537) B24782537
theorem B2292251 : Blo 1526460 2292251 := bstep (se 1 (by rfl) ⟨1719188, by rfl⟩ : syracuseStep 2292251 = 3438377) B3438377
theorem B1718815 : Blo 1526460 1718815 := bstep (se 1 (by rfl) ⟨1289111, by rfl⟩ : syracuseStep 1718815 = 2578223) B2578223
theorem B2292329 : Blo 1526460 2292329 := bstep (se 2 (by rfl) ⟨859623, by rfl⟩ : syracuseStep 2292329 = 1719247) B1719247
theorem B7731935 : Blo 1526460 7731935 := bstep (se 1 (by rfl) ⟨5798951, by rfl⟩ : syracuseStep 7731935 = 11597903) B11597903
theorem B11008835 : Blo 1526460 11008835 := bstep (se 1 (by rfl) ⟨8256626, by rfl⟩ : syracuseStep 11008835 = 16513253) B16513253
theorem B13048735 : Blo 1526460 13048735 := bstep (se 1 (by rfl) ⟨9786551, by rfl⟩ : syracuseStep 13048735 = 19573103) B19573103
theorem B19831837 : Blo 1526460 19831837 := bstep (se 3 (by rfl) ⟨3718469, by rfl⟩ : syracuseStep 19831837 = 7436939) B7436939
theorem B5151815 : Blo 1526460 5151815 := bstep (se 1 (by rfl) ⟨3863861, by rfl⟩ : syracuseStep 5151815 = 7727723) B7727723
theorem B5151869 : Blo 1526460 5151869 := bstep (se 3 (by rfl) ⟨965975, by rfl⟩ : syracuseStep 5151869 = 1931951) B1931951
theorem B5504129 : Blo 1526460 5504129 := bstep (se 2 (by rfl) ⟨2064048, by rfl⟩ : syracuseStep 5504129 = 4128097) B4128097
theorem B2899127 : Blo 1526460 2899127 := bstep (se 1 (by rfl) ⟨2174345, by rfl⟩ : syracuseStep 2899127 = 4348691) B4348691
theorem B4406525 : Blo 1526460 4406525 := bstep (se 3 (by rfl) ⟨826223, by rfl⟩ : syracuseStep 4406525 = 1652447) B1652447
theorem B5152139 : Blo 1526460 5152139 := bstep (se 1 (by rfl) ⟨3864104, by rfl⟩ : syracuseStep 5152139 = 7728209) B7728209
theorem B4349351 : Blo 1526460 4349351 := bstep (se 1 (by rfl) ⟨3262013, by rfl⟩ : syracuseStep 4349351 = 6524027) B6524027
theorem B9780709 : Blo 1526460 9780709 := bstep (se 4 (by rfl) ⟨916941, by rfl⟩ : syracuseStep 9780709 = 1833883) B1833883
theorem B5504591 : Blo 1526460 5504591 := bstep (se 1 (by rfl) ⟨4128443, by rfl⟩ : syracuseStep 5504591 = 8256887) B8256887
theorem B5955383 : Blo 1526460 5955383 := bstep (se 1 (by rfl) ⟨4466537, by rfl⟩ : syracuseStep 5955383 = 8933075) B8933075
theorem B7839611 : Blo 1526460 7839611 := bstep (se 1 (by rfl) ⟨5879708, by rfl⟩ : syracuseStep 7839611 = 11759417) B11759417
theorem B3481807 : Blo 1526460 3481807 := bstep (se 1 (by rfl) ⟨2611355, by rfl⟩ : syracuseStep 3481807 = 5222711) B5222711
theorem B13050071 : Blo 1526460 13050071 := bstep (se 1 (by rfl) ⟨9787553, by rfl⟩ : syracuseStep 13050071 = 19575107) B19575107
theorem B5800319 : Blo 1526460 5800319 := bstep (se 1 (by rfl) ⟨4350239, by rfl⟩ : syracuseStep 5800319 = 8700479) B8700479
theorem B27910561 : Blo 1526460 27910561 := bstep (se 2 (by rfl) ⟨10466460, by rfl⟩ : syracuseStep 27910561 = 20932921) B20932921
theorem B26108405 : Blo 1526460 26108405 := bstep (se 5 (by rfl) ⟨1223831, by rfl⟩ : syracuseStep 26108405 = 2447663) B2447663
theorem B5153273 : Blo 1526460 5153273 := bstep (se 2 (by rfl) ⟨1932477, by rfl⟩ : syracuseStep 5153273 = 3864955) B3864955
theorem B3670535 : Blo 1526460 3670535 := bstep (se 1 (by rfl) ⟨2752901, by rfl⟩ : syracuseStep 3670535 = 5505803) B5505803
theorem B1835551 : Blo 1526460 1835551 := bstep (se 1 (by rfl) ⟨1376663, by rfl⟩ : syracuseStep 1835551 = 2753327) B2753327
theorem B2900585 : Blo 1526460 2900585 := bstep (se 2 (by rfl) ⟨1087719, by rfl⟩ : syracuseStep 2900585 = 2175439) B2175439
theorem B22028921 : Blo 1526460 22028921 := bstep (se 2 (by rfl) ⟨8260845, by rfl⟩ : syracuseStep 22028921 = 16521691) B16521691
theorem B5153543 : Blo 1526460 5153543 := bstep (se 1 (by rfl) ⟨3865157, by rfl⟩ : syracuseStep 5153543 = 7730315) B7730315
theorem B9782041 : Blo 1526460 9782041 := bstep (se 2 (by rfl) ⟨3668265, by rfl⟩ : syracuseStep 9782041 = 7336531) B7336531
theorem B6275969 : Blo 1526460 6275969 := bstep (se 2 (by rfl) ⟨2353488, by rfl⟩ : syracuseStep 6275969 = 4706977) B4706977
theorem B70583393 : Blo 1526460 70583393 := bstep (se 2 (by rfl) ⟨26468772, by rfl⟩ : syracuseStep 70583393 = 52937545) B52937545
theorem B2065519 : Blo 1526460 2065519 := bstep (se 1 (by rfl) ⟨1549139, by rfl⟩ : syracuseStep 2065519 = 3098279) B3098279
theorem B19842241 : Blo 1526460 19842241 := bstep (se 2 (by rfl) ⟨7440840, by rfl⟩ : syracuseStep 19842241 = 14881681) B14881681
theorem B6522079 : Blo 1526460 6522079 := bstep (se 1 (by rfl) ⟨4891559, by rfl⟩ : syracuseStep 6522079 = 9783119) B9783119
theorem B3867871 : Blo 1526460 3867871 := bstep (se 1 (by rfl) ⟨2900903, by rfl⟩ : syracuseStep 3867871 = 5801807) B5801807
theorem B5801503 : Blo 1526460 5801503 := bstep (se 1 (by rfl) ⟨4351127, by rfl⟩ : syracuseStep 5801503 = 8702255) B8702255
theorem B39683621 : Blo 1526460 39683621 := bstep (se 4 (by rfl) ⟨3720339, by rfl⟩ : syracuseStep 39683621 = 7440679) B7440679
theorem B5154623 : Blo 1526460 5154623 := bstep (se 1 (by rfl) ⟨3865967, by rfl⟩ : syracuseStep 5154623 = 7731935) B7731935
theorem B9783271 : Blo 1526460 9783271 := bstep (se 1 (by rfl) ⟨7337453, by rfl⟩ : syracuseStep 9783271 = 14674907) B14674907
theorem B5801975 : Blo 1526460 5801975 := bstep (se 1 (by rfl) ⟨4351481, by rfl⟩ : syracuseStep 5801975 = 8702963) B8702963
theorem B3434543 : Blo 1526460 3434543 := bstep (se 1 (by rfl) ⟨2575907, by rfl⟩ : syracuseStep 3434543 = 5151815) B5151815
theorem B3434579 : Blo 1526460 3434579 := bstep (se 1 (by rfl) ⟨2575934, by rfl⟩ : syracuseStep 3434579 = 5151869) B5151869
theorem B7735499 : Blo 1526460 7735499 := bstep (se 1 (by rfl) ⟨5801624, by rfl⟩ : syracuseStep 7735499 = 11603249) B11603249
theorem B3434759 : Blo 1526460 3434759 := bstep (se 1 (by rfl) ⟨2576069, by rfl⟩ : syracuseStep 3434759 = 5152139) B5152139
theorem B3262799 : Blo 1526460 3262799 := bstep (se 1 (by rfl) ⟨2447099, by rfl⟩ : syracuseStep 3262799 = 4894199) B4894199
theorem B4352393 : Blo 1526460 4352393 := bstep (se 2 (by rfl) ⟨1632147, by rfl⟩ : syracuseStep 4352393 = 3264295) B3264295
theorem B3435065 : Blo 1526460 3435065 := bstep (se 2 (by rfl) ⟨1288149, by rfl⟩ : syracuseStep 3435065 = 2576299) B2576299
theorem B6703897 : Blo 1526460 6703897 := bstep (se 2 (by rfl) ⟨2513961, by rfl⟩ : syracuseStep 6703897 = 5027923) B5027923
theorem B13044635 : Blo 1526460 13044635 := bstep (se 1 (by rfl) ⟨9783476, by rfl⟩ : syracuseStep 13044635 = 19566953) B19566953
theorem B5802947 : Blo 1526460 5802947 := bstep (se 1 (by rfl) ⟨4352210, by rfl⟩ : syracuseStep 5802947 = 8704421) B8704421
theorem B1526751 : Blo 1526460 1526751 := bstep (se 1 (by rfl) ⟨1145063, by rfl⟩ : syracuseStep 1526751 = 2290127) B2290127
theorem B1526779 : Blo 1526460 1526779 := bstep (se 1 (by rfl) ⟨1145084, by rfl⟩ : syracuseStep 1526779 = 2290169) B2290169
theorem B3263483 : Blo 1526460 3263483 := bstep (se 1 (by rfl) ⟨2447612, by rfl⟩ : syracuseStep 3263483 = 4895225) B4895225
theorem B1526847 : Blo 1526460 1526847 := bstep (se 1 (by rfl) ⟨1145135, by rfl⟩ : syracuseStep 1526847 = 2290271) B2290271
theorem B13225103 : Blo 1526460 13225103 := bstep (se 1 (by rfl) ⟨9918827, by rfl⟩ : syracuseStep 13225103 = 19837655) B19837655
theorem B10448041 : Blo 1526460 10448041 := bstep (se 2 (by rfl) ⟨3918015, by rfl⟩ : syracuseStep 10448041 = 7836031) B7836031
theorem B3435785 : Blo 1526460 3435785 := bstep (se 2 (by rfl) ⟨1288419, by rfl⟩ : syracuseStep 3435785 = 2576839) B2576839
theorem B5156135 : Blo 1526460 5156135 := bstep (se 1 (by rfl) ⟨3867101, by rfl⟩ : syracuseStep 5156135 = 7734203) B7734203
theorem B7834967 : Blo 1526460 7834967 := bstep (se 1 (by rfl) ⟨5876225, by rfl⟩ : syracuseStep 7834967 = 11752451) B11752451
theorem B6196591 : Blo 1526460 6196591 := bstep (se 1 (by rfl) ⟨4647443, by rfl⟩ : syracuseStep 6196591 = 9294887) B9294887
theorem B1527167 : Blo 1526460 1527167 := bstep (se 1 (by rfl) ⟨1145375, by rfl⟩ : syracuseStep 1527167 = 2290751) B2290751
theorem B1527195 : Blo 1526460 1527195 := bstep (se 1 (by rfl) ⟨1145396, by rfl⟩ : syracuseStep 1527195 = 2290793) B2290793
theorem B1527263 : Blo 1526460 1527263 := bstep (se 1 (by rfl) ⟨1145447, by rfl⟩ : syracuseStep 1527263 = 2290895) B2290895
theorem B6524489 : Blo 1526460 6524489 := bstep (se 2 (by rfl) ⟨2446683, by rfl⟩ : syracuseStep 6524489 = 4893367) B4893367
theorem B2575975 : Blo 1526460 2575975 := bstep (se 1 (by rfl) ⟨1931981, by rfl⟩ : syracuseStep 2575975 = 3863963) B3863963
theorem B1527399 : Blo 1526460 1527399 := bstep (se 1 (by rfl) ⟨1145549, by rfl⟩ : syracuseStep 1527399 = 2291099) B2291099
theorem B94080629 : Blo 1526460 94080629 := bstep (se 5 (by rfl) ⟨4410029, by rfl⟩ : syracuseStep 94080629 = 8820059) B8820059
theorem B1527547 : Blo 1526460 1527547 := bstep (se 1 (by rfl) ⟨1145660, by rfl⟩ : syracuseStep 1527547 = 2291321) B2291321
theorem B1527615 : Blo 1526460 1527615 := bstep (se 1 (by rfl) ⟨1145711, by rfl⟩ : syracuseStep 1527615 = 2291423) B2291423
theorem B1527679 : Blo 1526460 1527679 := bstep (se 1 (by rfl) ⟨1145759, by rfl⟩ : syracuseStep 1527679 = 2291519) B2291519
theorem B1527791 : Blo 1526460 1527791 := bstep (se 1 (by rfl) ⟨1145843, by rfl⟩ : syracuseStep 1527791 = 2291687) B2291687
theorem B1527803 : Blo 1526460 1527803 := bstep (se 1 (by rfl) ⟨1145852, by rfl⟩ : syracuseStep 1527803 = 2291705) B2291705
theorem B1527871 : Blo 1526460 1527871 := bstep (se 1 (by rfl) ⟨1145903, by rfl⟩ : syracuseStep 1527871 = 2291807) B2291807
theorem B1527911 : Blo 1526460 1527911 := bstep (se 1 (by rfl) ⟨1145933, by rfl⟩ : syracuseStep 1527911 = 2291867) B2291867
theorem B2289791 : Blo 1526460 2289791 := bstep (se 1 (by rfl) ⟨1717343, by rfl⟩ : syracuseStep 2289791 = 3434687) B3434687
theorem B2175103 : Blo 1526460 2175103 := bstep (se 1 (by rfl) ⟨1631327, by rfl⟩ : syracuseStep 2175103 = 3262655) B3262655
theorem B1527935 : Blo 1526460 1527935 := bstep (se 1 (by rfl) ⟨1145951, by rfl⟩ : syracuseStep 1527935 = 2291903) B2291903
theorem B1527963 : Blo 1526460 1527963 := bstep (se 1 (by rfl) ⟨1145972, by rfl⟩ : syracuseStep 1527963 = 2291945) B2291945
theorem B47018177 : Blo 1526460 47018177 := bstep (se 2 (by rfl) ⟨17631816, by rfl⟩ : syracuseStep 47018177 = 35263633) B35263633
theorem B3436775 : Blo 1526460 3436775 := bstep (se 1 (by rfl) ⟨2577581, by rfl⟩ : syracuseStep 3436775 = 5155163) B5155163
theorem B3485929 : Blo 1526460 3485929 := bstep (se 2 (by rfl) ⟨1307223, by rfl⟩ : syracuseStep 3485929 = 2614447) B2614447
theorem B11604221 : Blo 1526460 11604221 := bstep (se 3 (by rfl) ⟨2175791, by rfl⟩ : syracuseStep 11604221 = 4351583) B4351583
theorem B120639773 : Blo 1526460 120639773 := bstep (se 3 (by rfl) ⟨22619957, by rfl⟩ : syracuseStep 120639773 = 45239915) B45239915
theorem B1528167 : Blo 1526460 1528167 := bstep (se 1 (by rfl) ⟨1146125, by rfl⟩ : syracuseStep 1528167 = 2292251) B2292251
theorem B3436955 : Blo 1526460 3436955 := bstep (se 1 (by rfl) ⟨2577716, by rfl⟩ : syracuseStep 3436955 = 5155433) B5155433
theorem B1528219 : Blo 1526460 1528219 := bstep (se 1 (by rfl) ⟨1146164, by rfl⟩ : syracuseStep 1528219 = 2292329) B2292329
theorem B13046345 : Blo 1526460 13046345 := bstep (se 2 (by rfl) ⟨4892379, by rfl⟩ : syracuseStep 13046345 = 9784759) B9784759
theorem B5796431 : Blo 1526460 5796431 := bstep (se 1 (by rfl) ⟨4347323, by rfl⟩ : syracuseStep 5796431 = 8694647) B8694647
theorem B2290427 : Blo 1526460 2290427 := bstep (se 1 (by rfl) ⟨1717820, by rfl⟩ : syracuseStep 2290427 = 3435641) B3435641
theorem B15881021 : Blo 1526460 15881021 := bstep (se 3 (by rfl) ⟨2977691, by rfl⟩ : syracuseStep 15881021 = 5955383) B5955383
theorem B2937683 : Blo 1526460 2937683 := bstep (se 1 (by rfl) ⟨2203262, by rfl⟩ : syracuseStep 2937683 = 4406525) B4406525
theorem B7336975 : Blo 1526460 7336975 := bstep (se 1 (by rfl) ⟨5502731, by rfl⟩ : syracuseStep 7336975 = 11005463) B11005463
theorem B3437639 : Blo 1526460 3437639 := bstep (se 1 (by rfl) ⟨2578229, by rfl⟩ : syracuseStep 3437639 = 5156459) B5156459
theorem B5796947 : Blo 1526460 5796947 := bstep (se 1 (by rfl) ⟨4347710, by rfl⟩ : syracuseStep 5796947 = 8695421) B8695421
theorem B2290871 : Blo 1526460 2290871 := bstep (se 1 (by rfl) ⟨1718153, by rfl⟩ : syracuseStep 2290871 = 3436307) B3436307
theorem B3437819 : Blo 1526460 3437819 := bstep (se 1 (by rfl) ⟨2578364, by rfl⟩ : syracuseStep 3437819 = 5156729) B5156729
theorem B2446703 : Blo 1526460 2446703 := bstep (se 1 (by rfl) ⟨1835027, by rfl⟩ : syracuseStep 2446703 = 3670055) B3670055
theorem B2291111 : Blo 1526460 2291111 := bstep (se 1 (by rfl) ⟨1718333, by rfl⟩ : syracuseStep 2291111 = 3436667) B3436667
theorem B3438035 : Blo 1526460 3438035 := bstep (se 1 (by rfl) ⟨2578526, by rfl⟩ : syracuseStep 3438035 = 5157053) B5157053
theorem B1717735 : Blo 1526460 1717735 := bstep (se 1 (by rfl) ⟨1288301, by rfl⟩ : syracuseStep 1717735 = 2576603) B2576603
theorem B2291291 : Blo 1526460 2291291 := bstep (se 1 (by rfl) ⟨1718468, by rfl⟩ : syracuseStep 2291291 = 3436937) B3436937
theorem B1717915 : Blo 1526460 1717915 := bstep (se 1 (by rfl) ⟨1288436, by rfl⟩ : syracuseStep 1717915 = 2576873) B2576873
theorem B5797601 : Blo 1526460 5797601 := bstep (se 2 (by rfl) ⟨2174100, by rfl⟩ : syracuseStep 5797601 = 4348201) B4348201
theorem B3438305 : Blo 1526460 3438305 := bstep (se 2 (by rfl) ⟨1289364, by rfl⟩ : syracuseStep 3438305 = 2578729) B2578729
theorem B5224175 : Blo 1526460 5224175 := bstep (se 1 (by rfl) ⟨3918131, by rfl⟩ : syracuseStep 5224175 = 7836263) B7836263
theorem B6526727 : Blo 1526460 6526727 := bstep (se 1 (by rfl) ⟨4895045, by rfl⟩ : syracuseStep 6526727 = 9790091) B9790091
theorem B2291753 : Blo 1526460 2291753 := bstep (se 2 (by rfl) ⟨859407, by rfl⟩ : syracuseStep 2291753 = 1718815) B1718815
theorem B2291783 : Blo 1526460 2291783 := bstep (se 1 (by rfl) ⟨1718837, by rfl⟩ : syracuseStep 2291783 = 3437675) B3437675
theorem B11016329 : Blo 1526460 11016329 := bstep (se 2 (by rfl) ⟨4131123, by rfl⟩ : syracuseStep 11016329 = 8262247) B8262247
theorem B2898155 : Blo 1526460 2898155 := bstep (se 1 (by rfl) ⟨2173616, by rfl⟩ : syracuseStep 2898155 = 4347233) B4347233
theorem B3438827 : Blo 1526460 3438827 := bstep (se 1 (by rfl) ⟨2579120, by rfl⟩ : syracuseStep 3438827 = 5158241) B5158241
theorem B2292167 : Blo 1526460 2292167 := bstep (se 1 (by rfl) ⟨1719125, by rfl⟩ : syracuseStep 2292167 = 3438251) B3438251
theorem B17398313 : Blo 1526460 17398313 := bstep (se 2 (by rfl) ⟨6524367, by rfl⟩ : syracuseStep 17398313 = 13048735) B13048735
theorem B2292383 : Blo 1526460 2292383 := bstep (se 1 (by rfl) ⟨1719287, by rfl⟩ : syracuseStep 2292383 = 3438575) B3438575
theorem B26442449 : Blo 1526460 26442449 := bstep (se 2 (by rfl) ⟨9915918, by rfl⟩ : syracuseStep 26442449 = 19831837) B19831837
theorem B8698589 : Blo 1526460 8698589 := bstep (se 3 (by rfl) ⟨1630985, by rfl⟩ : syracuseStep 8698589 = 3261971) B3261971
theorem B2292527 : Blo 1526460 2292527 := bstep (se 1 (by rfl) ⟨1719395, by rfl⟩ : syracuseStep 2292527 = 3438791) B3438791
theorem B49519511 : Blo 1526460 49519511 := bstep (se 1 (by rfl) ⟨37139633, by rfl⟩ : syracuseStep 49519511 = 74279267) B74279267
theorem B2292647 : Blo 1526460 2292647 := bstep (se 1 (by rfl) ⟨1719485, by rfl⟩ : syracuseStep 2292647 = 3438971) B3438971
theorem B2898899 : Blo 1526460 2898899 := bstep (se 1 (by rfl) ⟨2174174, by rfl⟩ : syracuseStep 2898899 = 4348349) B4348349
theorem B7339223 : Blo 1526460 7339223 := bstep (se 1 (by rfl) ⟨5504417, by rfl⟩ : syracuseStep 7339223 = 11008835) B11008835
theorem B13040945 : Blo 1526460 13040945 := bstep (se 2 (by rfl) ⟨4890354, by rfl⟩ : syracuseStep 13040945 = 9780709) B9780709
theorem B3669419 : Blo 1526460 3669419 := bstep (se 1 (by rfl) ⟨2752064, by rfl⟩ : syracuseStep 3669419 = 5504129) B5504129
theorem B1932751 : Blo 1526460 1932751 := bstep (se 1 (by rfl) ⟨1449563, by rfl⟩ : syracuseStep 1932751 = 2899127) B2899127
theorem B6970835 : Blo 1526460 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B2899567 : Blo 1526460 2899567 := bstep (se 1 (by rfl) ⟨2174675, by rfl⟩ : syracuseStep 2899567 = 4349351) B4349351
theorem B3669727 : Blo 1526460 3669727 := bstep (se 1 (by rfl) ⟨2752295, by rfl⟩ : syracuseStep 3669727 = 5504591) B5504591
theorem B4349807 : Blo 1526460 4349807 := bstep (se 1 (by rfl) ⟨3262355, by rfl⟩ : syracuseStep 4349807 = 6524711) B6524711
theorem B5226407 : Blo 1526460 5226407 := bstep (se 1 (by rfl) ⟨3919805, by rfl⟩ : syracuseStep 5226407 = 7839611) B7839611
theorem B8700047 : Blo 1526460 8700047 := bstep (se 1 (by rfl) ⟨6525035, by rfl⟩ : syracuseStep 8700047 = 13050071) B13050071
theorem B9789605 : Blo 1526460 9789605 := bstep (se 4 (by rfl) ⟨917775, by rfl⟩ : syracuseStep 9789605 = 1835551) B1835551
theorem B2900137 : Blo 1526460 2900137 := bstep (se 2 (by rfl) ⟨1087551, by rfl⟩ : syracuseStep 2900137 = 2175103) B2175103
theorem B3866879 : Blo 1526460 3866879 := bstep (se 1 (by rfl) ⟨2900159, by rfl⟩ : syracuseStep 3866879 = 5800319) B5800319
theorem B29376877 : Blo 1526460 29376877 := bstep (se 3 (by rfl) ⟨5508164, by rfl⟩ : syracuseStep 29376877 = 11016329) B11016329
theorem B1933723 : Blo 1526460 1933723 := bstep (se 1 (by rfl) ⟨1450292, by rfl⟩ : syracuseStep 1933723 = 2900585) B2900585
theorem B1958455 : Blo 1526460 1958455 := bstep (se 1 (by rfl) ⟨1468841, by rfl⟩ : syracuseStep 1958455 = 2937683) B2937683
theorem B47055595 : Blo 1526460 47055595 := bstep (se 1 (by rfl) ⟨35291696, by rfl⟩ : syracuseStep 47055595 = 70583393) B70583393
theorem B8700797 : Blo 1526460 8700797 := bstep (se 3 (by rfl) ⟨1631399, by rfl⟩ : syracuseStep 8700797 = 3262799) B3262799
theorem B1631135 : Blo 1526460 1631135 := bstep (se 1 (by rfl) ⟨1223351, by rfl⟩ : syracuseStep 1631135 = 2446703) B2446703
theorem B13042721 : Blo 1526460 13042721 := bstep (se 2 (by rfl) ⟨4891020, by rfl⟩ : syracuseStep 13042721 = 9782041) B9782041
theorem B8938529 : Blo 1526460 8938529 := bstep (se 2 (by rfl) ⟨3351948, by rfl⟩ : syracuseStep 8938529 = 6703897) B6703897
theorem B3482783 : Blo 1526460 3482783 := bstep (se 1 (by rfl) ⟨2612087, by rfl⟩ : syracuseStep 3482783 = 5224175) B5224175
theorem B4351151 : Blo 1526460 4351151 := bstep (se 1 (by rfl) ⟨3263363, by rfl⟩ : syracuseStep 4351151 = 6526727) B6526727
theorem B3867983 : Blo 1526460 3867983 := bstep (se 1 (by rfl) ⟨2900987, by rfl⟩ : syracuseStep 3867983 = 5801975) B5801975
theorem B9782633 : Blo 1526460 9782633 := bstep (se 2 (by rfl) ⟨3668487, by rfl⟩ : syracuseStep 9782633 = 7336975) B7336975
theorem B2901595 : Blo 1526460 2901595 := bstep (se 1 (by rfl) ⟨2176196, by rfl⟩ : syracuseStep 2901595 = 4352393) B4352393
theorem B3868631 : Blo 1526460 3868631 := bstep (se 1 (by rfl) ⟨2901473, by rfl⟩ : syracuseStep 3868631 = 5802947) B5802947
theorem B7735337 : Blo 1526460 7735337 := bstep (se 2 (by rfl) ⟨2900751, by rfl⟩ : syracuseStep 7735337 = 5801503) B5801503
theorem B8816735 : Blo 1526460 8816735 := bstep (se 1 (by rfl) ⟨6612551, by rfl⟩ : syracuseStep 8816735 = 13225103) B13225103
theorem B3434633 : Blo 1526460 3434633 := bstep (se 2 (by rfl) ⟨1287987, by rfl⟩ : syracuseStep 3434633 = 2575975) B2575975
theorem B4892815 : Blo 1526460 4892815 := bstep (se 1 (by rfl) ⟨3669611, by rfl⟩ : syracuseStep 4892815 = 7339223) B7339223
theorem B8693963 : Blo 1526460 8693963 := bstep (se 1 (by rfl) ⟨6520472, by rfl⟩ : syracuseStep 8693963 = 13040945) B13040945
theorem B4892969 : Blo 1526460 4892969 := bstep (se 2 (by rfl) ⟨1834863, by rfl⟩ : syracuseStep 4892969 = 3669727) B3669727
theorem B4647223 : Blo 1526460 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B62720419 : Blo 1526460 62720419 := bstep (se 1 (by rfl) ⟨47040314, by rfl⟩ : syracuseStep 62720419 = 94080629) B94080629
theorem B3484271 : Blo 1526460 3484271 := bstep (se 1 (by rfl) ⟨2613203, by rfl⟩ : syracuseStep 3484271 = 5226407) B5226407
theorem B13044361 : Blo 1526460 13044361 := bstep (se 2 (by rfl) ⟨4891635, by rfl⟩ : syracuseStep 13044361 = 9783271) B9783271
theorem B1526527 : Blo 1526460 1526527 := bstep (se 1 (by rfl) ⟨1144895, by rfl⟩ : syracuseStep 1526527 = 2289791) B2289791
theorem B31345451 : Blo 1526460 31345451 := bstep (se 1 (by rfl) ⟨23509088, by rfl⟩ : syracuseStep 31345451 = 47018177) B47018177
theorem B7736147 : Blo 1526460 7736147 := bstep (se 1 (by rfl) ⟨5802110, by rfl⟩ : syracuseStep 7736147 = 11604221) B11604221
theorem B4647905 : Blo 1526460 4647905 := bstep (se 2 (by rfl) ⟨1742964, by rfl⟩ : syracuseStep 4647905 = 3485929) B3485929
theorem B3435515 : Blo 1526460 3435515 := bstep (se 1 (by rfl) ⟨2576636, by rfl⟩ : syracuseStep 3435515 = 5153273) B5153273
theorem B1526951 : Blo 1526460 1526951 := bstep (se 1 (by rfl) ⟨1145213, by rfl⟩ : syracuseStep 1526951 = 2290427) B2290427
theorem B3435695 : Blo 1526460 3435695 := bstep (se 1 (by rfl) ⟨2576771, by rfl⟩ : syracuseStep 3435695 = 5153543) B5153543
theorem B10587347 : Blo 1526460 10587347 := bstep (se 1 (by rfl) ⟨7940510, by rfl⟩ : syracuseStep 10587347 = 15881021) B15881021
theorem B1527247 : Blo 1526460 1527247 := bstep (se 1 (by rfl) ⟨1145435, by rfl⟩ : syracuseStep 1527247 = 2290871) B2290871
theorem B1527407 : Blo 1526460 1527407 := bstep (se 1 (by rfl) ⟨1145555, by rfl⟩ : syracuseStep 1527407 = 2291111) B2291111
theorem B26455747 : Blo 1526460 26455747 := bstep (se 1 (by rfl) ⟨19841810, by rfl⟩ : syracuseStep 26455747 = 39683621) B39683621
theorem B1527527 : Blo 1526460 1527527 := bstep (se 1 (by rfl) ⟨1145645, by rfl⟩ : syracuseStep 1527527 = 2291291) B2291291
theorem B9785117 : Blo 1526460 9785117 := bstep (se 3 (by rfl) ⟨1834709, by rfl⟩ : syracuseStep 9785117 = 3669419) B3669419
theorem B3436415 : Blo 1526460 3436415 := bstep (se 1 (by rfl) ⟨2577311, by rfl⟩ : syracuseStep 3436415 = 5154623) B5154623
theorem B1527835 : Blo 1526460 1527835 := bstep (se 1 (by rfl) ⟨1145876, by rfl⟩ : syracuseStep 1527835 = 2291753) B2291753
theorem B2289695 : Blo 1526460 2289695 := bstep (se 1 (by rfl) ⟨1717271, by rfl⟩ : syracuseStep 2289695 = 3434543) B3434543
theorem B1527855 : Blo 1526460 1527855 := bstep (se 1 (by rfl) ⟨1145891, by rfl⟩ : syracuseStep 1527855 = 2291783) B2291783
theorem B2289719 : Blo 1526460 2289719 := bstep (se 1 (by rfl) ⟨1717289, by rfl⟩ : syracuseStep 2289719 = 3434579) B3434579
theorem B5156999 : Blo 1526460 5156999 := bstep (se 1 (by rfl) ⟨3867749, by rfl⟩ : syracuseStep 5156999 = 7735499) B7735499
theorem B2289839 : Blo 1526460 2289839 := bstep (se 1 (by rfl) ⟨1717379, by rfl⟩ : syracuseStep 2289839 = 3434759) B3434759
theorem B13930721 : Blo 1526460 13930721 := bstep (se 2 (by rfl) ⟨5224020, by rfl⟩ : syracuseStep 13930721 = 10448041) B10448041
theorem B26456321 : Blo 1526460 26456321 := bstep (se 2 (by rfl) ⟨9921120, by rfl⟩ : syracuseStep 26456321 = 19842241) B19842241
theorem B8696105 : Blo 1526460 8696105 := bstep (se 2 (by rfl) ⟨3261039, by rfl⟩ : syracuseStep 8696105 = 6522079) B6522079
theorem B5157161 : Blo 1526460 5157161 := bstep (se 2 (by rfl) ⟨1933935, by rfl⟩ : syracuseStep 5157161 = 3867871) B3867871
theorem B1528111 : Blo 1526460 1528111 := bstep (se 1 (by rfl) ⟨1146083, by rfl⟩ : syracuseStep 1528111 = 2292167) B2292167
theorem B2290043 : Blo 1526460 2290043 := bstep (se 1 (by rfl) ⟨1717532, by rfl⟩ : syracuseStep 2290043 = 3435065) B3435065
theorem B1528255 : Blo 1526460 1528255 := bstep (se 1 (by rfl) ⟨1146191, by rfl⟩ : syracuseStep 1528255 = 2292383) B2292383
theorem B8262121 : Blo 1526460 8262121 := bstep (se 2 (by rfl) ⟨3098295, by rfl⟩ : syracuseStep 8262121 = 6196591) B6196591
theorem B1528351 : Blo 1526460 1528351 := bstep (se 1 (by rfl) ⟨1146263, by rfl⟩ : syracuseStep 1528351 = 2292527) B2292527
theorem B8696423 : Blo 1526460 8696423 := bstep (se 1 (by rfl) ⟨6522317, by rfl⟩ : syracuseStep 8696423 = 13044635) B13044635
theorem B2577001 : Blo 1526460 2577001 := bstep (se 2 (by rfl) ⟨966375, by rfl⟩ : syracuseStep 2577001 = 1932751) B1932751
theorem B1528431 : Blo 1526460 1528431 := bstep (se 1 (by rfl) ⟨1146323, by rfl⟩ : syracuseStep 1528431 = 2292647) B2292647
theorem B2290313 : Blo 1526460 2290313 := bstep (se 2 (by rfl) ⟨858867, by rfl⟩ : syracuseStep 2290313 = 1717735) B1717735
theorem B2175655 : Blo 1526460 2175655 := bstep (se 1 (by rfl) ⟨1631741, by rfl⟩ : syracuseStep 2175655 = 3263483) B3263483
theorem B2290523 : Blo 1526460 2290523 := bstep (se 1 (by rfl) ⟨1717892, by rfl⟩ : syracuseStep 2290523 = 3435785) B3435785
theorem B3437423 : Blo 1526460 3437423 := bstep (se 1 (by rfl) ⟨2578067, by rfl⟩ : syracuseStep 3437423 = 5156135) B5156135
theorem B2290553 : Blo 1526460 2290553 := bstep (se 2 (by rfl) ⟨858957, by rfl⟩ : syracuseStep 2290553 = 1717915) B1717915
theorem B5223311 : Blo 1526460 5223311 := bstep (se 1 (by rfl) ⟨3917483, by rfl⟩ : syracuseStep 5223311 = 7834967) B7834967
theorem B2291183 : Blo 1526460 2291183 := bstep (se 1 (by rfl) ⟨1718387, by rfl⟩ : syracuseStep 2291183 = 3436775) B3436775
theorem B80426515 : Blo 1526460 80426515 := bstep (se 1 (by rfl) ⟨60319886, by rfl⟩ : syracuseStep 80426515 = 120639773) B120639773
theorem B2291303 : Blo 1526460 2291303 := bstep (se 1 (by rfl) ⟨1718477, by rfl⟩ : syracuseStep 2291303 = 3436955) B3436955
theorem B4642409 : Blo 1526460 4642409 := bstep (se 2 (by rfl) ⟨1740903, by rfl⟩ : syracuseStep 4642409 = 3481807) B3481807
theorem B17405603 : Blo 1526460 17405603 := bstep (se 1 (by rfl) ⟨13054202, by rfl⟩ : syracuseStep 17405603 = 26108405) B26108405
theorem B2447023 : Blo 1526460 2447023 := bstep (se 1 (by rfl) ⟨1835267, by rfl⟩ : syracuseStep 2447023 = 3670535) B3670535
theorem B8697563 : Blo 1526460 8697563 := bstep (se 1 (by rfl) ⟨6523172, by rfl⟩ : syracuseStep 8697563 = 13046345) B13046345
theorem B3864287 : Blo 1526460 3864287 := bstep (se 1 (by rfl) ⟨2898215, by rfl⟩ : syracuseStep 3864287 = 5796431) B5796431
theorem B14685947 : Blo 1526460 14685947 := bstep (se 1 (by rfl) ⟨11014460, by rfl⟩ : syracuseStep 14685947 = 22028921) B22028921
theorem B37214081 : Blo 1526460 37214081 := bstep (se 2 (by rfl) ⟨13955280, by rfl⟩ : syracuseStep 37214081 = 27910561) B27910561
theorem B11016101 : Blo 1526460 11016101 := bstep (se 4 (by rfl) ⟨1032759, by rfl⟩ : syracuseStep 11016101 = 2065519) B2065519
theorem B4183979 : Blo 1526460 4183979 := bstep (se 1 (by rfl) ⟨3137984, by rfl⟩ : syracuseStep 4183979 = 6275969) B6275969
theorem B2291759 : Blo 1526460 2291759 := bstep (se 1 (by rfl) ⟨1718819, by rfl⟩ : syracuseStep 2291759 = 3437639) B3437639
theorem B3864631 : Blo 1526460 3864631 := bstep (se 1 (by rfl) ⟨2898473, by rfl⟩ : syracuseStep 3864631 = 5796947) B5796947
theorem B2291879 : Blo 1526460 2291879 := bstep (se 1 (by rfl) ⟨1718909, by rfl⟩ : syracuseStep 2291879 = 3437819) B3437819
theorem B2292023 : Blo 1526460 2292023 := bstep (se 1 (by rfl) ⟨1719017, by rfl⟩ : syracuseStep 2292023 = 3438035) B3438035
theorem B3865067 : Blo 1526460 3865067 := bstep (se 1 (by rfl) ⟨2898800, by rfl⟩ : syracuseStep 3865067 = 5797601) B5797601
theorem B2292203 : Blo 1526460 2292203 := bstep (se 1 (by rfl) ⟨1719152, by rfl⟩ : syracuseStep 2292203 = 3438305) B3438305
theorem B1932103 : Blo 1526460 1932103 := bstep (se 1 (by rfl) ⟨1449077, by rfl⟩ : syracuseStep 1932103 = 2898155) B2898155
theorem B2292551 : Blo 1526460 2292551 := bstep (se 1 (by rfl) ⟨1719413, by rfl⟩ : syracuseStep 2292551 = 3438827) B3438827
theorem B11598875 : Blo 1526460 11598875 := bstep (se 1 (by rfl) ⟨8699156, by rfl⟩ : syracuseStep 11598875 = 17398313) B17398313
theorem B17628299 : Blo 1526460 17628299 := bstep (se 1 (by rfl) ⟨13221224, by rfl⟩ : syracuseStep 17628299 = 26442449) B26442449
theorem B5799059 : Blo 1526460 5799059 := bstep (se 1 (by rfl) ⟨4349294, by rfl⟩ : syracuseStep 5799059 = 8698589) B8698589
theorem B33013007 : Blo 1526460 33013007 := bstep (se 1 (by rfl) ⟨24759755, by rfl⟩ : syracuseStep 33013007 = 49519511) B49519511
theorem B1932599 : Blo 1526460 1932599 := bstep (se 1 (by rfl) ⟨1449449, by rfl⟩ : syracuseStep 1932599 = 2898899) B2898899
theorem B3866089 : Blo 1526460 3866089 := bstep (se 2 (by rfl) ⟨1449783, by rfl⟩ : syracuseStep 3866089 = 2899567) B2899567
theorem B4349659 : Blo 1526460 4349659 := bstep (se 1 (by rfl) ⟨3262244, by rfl⟩ : syracuseStep 4349659 = 6524489) B6524489
theorem B2899871 : Blo 1526460 2899871 := bstep (se 1 (by rfl) ⟨2174903, by rfl⟩ : syracuseStep 2899871 = 4349807) B4349807
theorem B5152841 : Blo 1526460 5152841 := bstep (se 2 (by rfl) ⟨1932315, by rfl⟩ : syracuseStep 5152841 = 3864631) B3864631
theorem B5800031 : Blo 1526460 5800031 := bstep (se 1 (by rfl) ⟨4350023, by rfl⟩ : syracuseStep 5800031 = 8700047) B8700047
theorem B17637547 : Blo 1526460 17637547 := bstep (se 1 (by rfl) ⟨13228160, by rfl⟩ : syracuseStep 17637547 = 26456321) B26456321
theorem B3866849 : Blo 1526460 3866849 := bstep (se 2 (by rfl) ⟨1450068, by rfl⟩ : syracuseStep 3866849 = 2900137) B2900137
theorem B23511293 : Blo 1526460 23511293 := bstep (se 3 (by rfl) ⟨4408367, by rfl⟩ : syracuseStep 23511293 = 8816735) B8816735
theorem B5800531 : Blo 1526460 5800531 := bstep (se 1 (by rfl) ⟨4350398, by rfl⟩ : syracuseStep 5800531 = 8700797) B8700797
theorem B3482207 : Blo 1526460 3482207 := bstep (se 1 (by rfl) ⟨2611655, by rfl⟩ : syracuseStep 3482207 = 5223311) B5223311
theorem B2900767 : Blo 1526460 2900767 := bstep (se 1 (by rfl) ⟨2175575, by rfl⟩ : syracuseStep 2900767 = 4351151) B4351151
theorem B5153597 : Blo 1526460 5153597 := bstep (se 3 (by rfl) ⟨966299, by rfl⟩ : syracuseStep 5153597 = 1932599) B1932599
theorem B17392481 : Blo 1526460 17392481 := bstep (se 2 (by rfl) ⟨6522180, by rfl⟩ : syracuseStep 17392481 = 13044361) B13044361
theorem B2900873 : Blo 1526460 2900873 := bstep (se 2 (by rfl) ⟨1087827, by rfl⟩ : syracuseStep 2900873 = 2175655) B2175655
theorem B6521755 : Blo 1526460 6521755 := bstep (se 1 (by rfl) ⟨4891316, by rfl⟩ : syracuseStep 6521755 = 9782633) B9782633
theorem B9790631 : Blo 1526460 9790631 := bstep (se 1 (by rfl) ⟨7342973, by rfl⟩ : syracuseStep 9790631 = 14685947) B14685947
theorem B3261979 : Blo 1526460 3261979 := bstep (se 1 (by rfl) ⟨2446484, by rfl⟩ : syracuseStep 3261979 = 4892969) B4892969
theorem B5154785 : Blo 1526460 5154785 := bstep (se 2 (by rfl) ⟨1933044, by rfl⟩ : syracuseStep 5154785 = 3866089) B3866089
theorem B3098603 : Blo 1526460 3098603 := bstep (se 1 (by rfl) ⟨2323952, by rfl⟩ : syracuseStep 3098603 = 4647905) B4647905
theorem B107235353 : Blo 1526460 107235353 := bstep (se 2 (by rfl) ⟨40213257, by rfl⟩ : syracuseStep 107235353 = 80426515) B80426515
theorem B3868793 : Blo 1526460 3868793 := bstep (se 2 (by rfl) ⟨1450797, by rfl⟩ : syracuseStep 3868793 = 2901595) B2901595
theorem B3262697 : Blo 1526460 3262697 := bstep (se 2 (by rfl) ⟨1223511, by rfl⟩ : syracuseStep 3262697 = 2447023) B2447023
theorem B6523411 : Blo 1526460 6523411 := bstep (se 1 (by rfl) ⟨4892558, by rfl⟩ : syracuseStep 6523411 = 9785117) B9785117
theorem B1526463 : Blo 1526460 1526463 := bstep (se 1 (by rfl) ⟨1144847, by rfl⟩ : syracuseStep 1526463 = 2289695) B2289695
theorem B1526479 : Blo 1526460 1526479 := bstep (se 1 (by rfl) ⟨1144859, by rfl⟩ : syracuseStep 1526479 = 2289719) B2289719
theorem B1526559 : Blo 1526460 1526559 := bstep (se 1 (by rfl) ⟨1144919, by rfl⟩ : syracuseStep 1526559 = 2289839) B2289839
theorem B6523753 : Blo 1526460 6523753 := bstep (se 2 (by rfl) ⟨2446407, by rfl⟩ : syracuseStep 6523753 = 4892815) B4892815
theorem B1526695 : Blo 1526460 1526695 := bstep (se 1 (by rfl) ⟨1145021, by rfl⟩ : syracuseStep 1526695 = 2290043) B2290043
theorem B1526875 : Blo 1526460 1526875 := bstep (se 1 (by rfl) ⟨1145156, by rfl⟩ : syracuseStep 1526875 = 2290313) B2290313
theorem B39169169 : Blo 1526460 39169169 := bstep (se 2 (by rfl) ⟨14688438, by rfl⟩ : syracuseStep 39169169 = 29376877) B29376877
theorem B83627225 : Blo 1526460 83627225 := bstep (se 2 (by rfl) ⟨31360209, by rfl⟩ : syracuseStep 83627225 = 62720419) B62720419
theorem B1527015 : Blo 1526460 1527015 := bstep (se 1 (by rfl) ⟨1145261, by rfl⟩ : syracuseStep 1527015 = 2290523) B2290523
theorem B1527035 : Blo 1526460 1527035 := bstep (se 1 (by rfl) ⟨1145276, by rfl⟩ : syracuseStep 1527035 = 2290553) B2290553
theorem B8695147 : Blo 1526460 8695147 := bstep (se 1 (by rfl) ⟨6521360, by rfl⟩ : syracuseStep 8695147 = 13042721) B13042721
theorem B5959019 : Blo 1526460 5959019 := bstep (se 1 (by rfl) ⟨4469264, by rfl⟩ : syracuseStep 5959019 = 8938529) B8938529
theorem B2321855 : Blo 1526460 2321855 := bstep (se 1 (by rfl) ⟨1741391, by rfl⟩ : syracuseStep 2321855 = 3482783) B3482783
theorem B3436001 : Blo 1526460 3436001 := bstep (se 2 (by rfl) ⟨1288500, by rfl⟩ : syracuseStep 3436001 = 2577001) B2577001
theorem B1527455 : Blo 1526460 1527455 := bstep (se 1 (by rfl) ⟨1145591, by rfl⟩ : syracuseStep 1527455 = 2291183) B2291183
theorem B1527535 : Blo 1526460 1527535 := bstep (se 1 (by rfl) ⟨1145651, by rfl⟩ : syracuseStep 1527535 = 2291303) B2291303
theorem B2576137 : Blo 1526460 2576137 := bstep (se 2 (by rfl) ⟨966051, by rfl⟩ : syracuseStep 2576137 = 1932103) B1932103
theorem B11603735 : Blo 1526460 11603735 := bstep (se 1 (by rfl) ⟨8702801, by rfl⟩ : syracuseStep 11603735 = 17405603) B17405603
theorem B2576191 : Blo 1526460 2576191 := bstep (se 1 (by rfl) ⟨1932143, by rfl⟩ : syracuseStep 2576191 = 3864287) B3864287
theorem B24809387 : Blo 1526460 24809387 := bstep (se 1 (by rfl) ⟨18607040, by rfl⟩ : syracuseStep 24809387 = 37214081) B37214081
theorem B7344067 : Blo 1526460 7344067 := bstep (se 1 (by rfl) ⟨5508050, by rfl⟩ : syracuseStep 7344067 = 11016101) B11016101
theorem B5156891 : Blo 1526460 5156891 := bstep (se 1 (by rfl) ⟨3867668, by rfl⟩ : syracuseStep 5156891 = 7735337) B7735337
theorem B1527839 : Blo 1526460 1527839 := bstep (se 1 (by rfl) ⟨1145879, by rfl⟩ : syracuseStep 1527839 = 2291759) B2291759
theorem B2289755 : Blo 1526460 2289755 := bstep (se 1 (by rfl) ⟨1717316, by rfl⟩ : syracuseStep 2289755 = 3434633) B3434633
theorem B1527919 : Blo 1526460 1527919 := bstep (se 1 (by rfl) ⟨1145939, by rfl⟩ : syracuseStep 1527919 = 2291879) B2291879
theorem B5795975 : Blo 1526460 5795975 := bstep (se 1 (by rfl) ⟨4346981, by rfl⟩ : syracuseStep 5795975 = 8693963) B8693963
theorem B1528015 : Blo 1526460 1528015 := bstep (se 1 (by rfl) ⟨1146011, by rfl⟩ : syracuseStep 1528015 = 2292023) B2292023
theorem B24785189 : Blo 1526460 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B2576711 : Blo 1526460 2576711 := bstep (se 1 (by rfl) ⟨1932533, by rfl⟩ : syracuseStep 2576711 = 3865067) B3865067
theorem B1528135 : Blo 1526460 1528135 := bstep (se 1 (by rfl) ⟨1146101, by rfl⟩ : syracuseStep 1528135 = 2292203) B2292203
theorem B2322847 : Blo 1526460 2322847 := bstep (se 1 (by rfl) ⟨1742135, by rfl⟩ : syracuseStep 2322847 = 3484271) B3484271
theorem B1528367 : Blo 1526460 1528367 := bstep (se 1 (by rfl) ⟨1146275, by rfl⟩ : syracuseStep 1528367 = 2292551) B2292551
theorem B5157431 : Blo 1526460 5157431 := bstep (se 1 (by rfl) ⟨3868073, by rfl⟩ : syracuseStep 5157431 = 7736147) B7736147
theorem B2290343 : Blo 1526460 2290343 := bstep (se 1 (by rfl) ⟨1717757, by rfl⟩ : syracuseStep 2290343 = 3435515) B3435515
theorem B11752199 : Blo 1526460 11752199 := bstep (se 1 (by rfl) ⟨8814149, by rfl⟩ : syracuseStep 11752199 = 17628299) B17628299
theorem B2290463 : Blo 1526460 2290463 := bstep (se 1 (by rfl) ⟨1717847, by rfl⟩ : syracuseStep 2290463 = 3435695) B3435695
theorem B7058231 : Blo 1526460 7058231 := bstep (se 1 (by rfl) ⟨5293673, by rfl⟩ : syracuseStep 7058231 = 10587347) B10587347
theorem B22008671 : Blo 1526460 22008671 := bstep (se 1 (by rfl) ⟨16506503, by rfl⟩ : syracuseStep 22008671 = 33013007) B33013007
theorem B2290943 : Blo 1526460 2290943 := bstep (se 1 (by rfl) ⟨1718207, by rfl⟩ : syracuseStep 2290943 = 3436415) B3436415
theorem B3437999 : Blo 1526460 3437999 := bstep (se 1 (by rfl) ⟨2578499, by rfl⟩ : syracuseStep 3437999 = 5156999) B5156999
theorem B6526403 : Blo 1526460 6526403 := bstep (se 1 (by rfl) ⟨4894802, by rfl⟩ : syracuseStep 6526403 = 9789605) B9789605
theorem B9287147 : Blo 1526460 9287147 := bstep (se 1 (by rfl) ⟨6965360, by rfl⟩ : syracuseStep 9287147 = 13930721) B13930721
theorem B2577919 : Blo 1526460 2577919 := bstep (se 1 (by rfl) ⟨1933439, by rfl⟩ : syracuseStep 2577919 = 3866879) B3866879
theorem B5797403 : Blo 1526460 5797403 := bstep (se 1 (by rfl) ⟨4348052, by rfl⟩ : syracuseStep 5797403 = 8696105) B8696105
theorem B3438107 : Blo 1526460 3438107 := bstep (se 1 (by rfl) ⟨2578580, by rfl⟩ : syracuseStep 3438107 = 5157161) B5157161
theorem B5797615 : Blo 1526460 5797615 := bstep (se 1 (by rfl) ⟨4348211, by rfl⟩ : syracuseStep 5797615 = 8696423) B8696423
theorem B2578297 : Blo 1526460 2578297 := bstep (se 2 (by rfl) ⟨966861, by rfl⟩ : syracuseStep 2578297 = 1933723) B1933723
theorem B2291615 : Blo 1526460 2291615 := bstep (se 1 (by rfl) ⟨1718711, by rfl⟩ : syracuseStep 2291615 = 3437423) B3437423
theorem B11016161 : Blo 1526460 11016161 := bstep (se 2 (by rfl) ⟨4131060, by rfl⟩ : syracuseStep 11016161 = 8262121) B8262121
theorem B2611273 : Blo 1526460 2611273 := bstep (se 2 (by rfl) ⟨979227, by rfl⟩ : syracuseStep 2611273 = 1958455) B1958455
theorem B2578655 : Blo 1526460 2578655 := bstep (se 1 (by rfl) ⟨1933991, by rfl⟩ : syracuseStep 2578655 = 3867983) B3867983
theorem B62740793 : Blo 1526460 62740793 := bstep (se 2 (by rfl) ⟨23527797, by rfl⟩ : syracuseStep 62740793 = 47055595) B47055595
theorem B3094939 : Blo 1526460 3094939 := bstep (se 1 (by rfl) ⟨2321204, by rfl⟩ : syracuseStep 3094939 = 4642409) B4642409
theorem B5798375 : Blo 1526460 5798375 := bstep (se 1 (by rfl) ⟨4348781, by rfl⟩ : syracuseStep 5798375 = 8697563) B8697563
theorem B2579087 : Blo 1526460 2579087 := bstep (se 1 (by rfl) ⟨1934315, by rfl⟩ : syracuseStep 2579087 = 3868631) B3868631
theorem B44629109 : Blo 1526460 44629109 := bstep (se 5 (by rfl) ⟨2091989, by rfl⟩ : syracuseStep 44629109 = 4183979) B4183979
theorem B20896967 : Blo 1526460 20896967 := bstep (se 1 (by rfl) ⟨15672725, by rfl⟩ : syracuseStep 20896967 = 31345451) B31345451
theorem B7732583 : Blo 1526460 7732583 := bstep (se 1 (by rfl) ⟨5799437, by rfl⟩ : syracuseStep 7732583 = 11598875) B11598875
theorem B3866039 : Blo 1526460 3866039 := bstep (se 1 (by rfl) ⟨2899529, by rfl⟩ : syracuseStep 3866039 = 5799059) B5799059
theorem B35274329 : Blo 1526460 35274329 := bstep (se 2 (by rfl) ⟨13227873, by rfl⟩ : syracuseStep 35274329 = 26455747) B26455747
theorem B5799545 : Blo 1526460 5799545 := bstep (se 2 (by rfl) ⟨2174829, by rfl⟩ : syracuseStep 5799545 = 4349659) B4349659
theorem B4349693 : Blo 1526460 4349693 := bstep (se 3 (by rfl) ⟨815567, by rfl⟩ : syracuseStep 4349693 = 1631135) B1631135
theorem B1933247 : Blo 1526460 1933247 := bstep (se 1 (by rfl) ⟨1449935, by rfl⟩ : syracuseStep 1933247 = 2899871) B2899871
theorem B3866687 : Blo 1526460 3866687 := bstep (se 1 (by rfl) ⟨2900015, by rfl⟩ : syracuseStep 3866687 = 5800031) B5800031
theorem B3481697 : Blo 1526460 3481697 := bstep (se 2 (by rfl) ⟨1305636, by rfl⟩ : syracuseStep 3481697 = 2611273) B2611273
theorem B16523459 : Blo 1526460 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B3097129 : Blo 1526460 3097129 := bstep (se 2 (by rfl) ⟨1161423, by rfl⟩ : syracuseStep 3097129 = 2322847) B2322847
theorem B14672447 : Blo 1526460 14672447 := bstep (se 1 (by rfl) ⟨11004335, by rfl⟩ : syracuseStep 14672447 = 22008671) B22008671
theorem B7734041 : Blo 1526460 7734041 := bstep (se 2 (by rfl) ⟨2900265, by rfl⟩ : syracuseStep 7734041 = 5800531) B5800531
theorem B4350935 : Blo 1526460 4350935 := bstep (se 1 (by rfl) ⟨3263201, by rfl⟩ : syracuseStep 4350935 = 6526403) B6526403
theorem B3867689 : Blo 1526460 3867689 := bstep (se 2 (by rfl) ⟨1450383, by rfl⟩ : syracuseStep 3867689 = 2900767) B2900767
theorem B24765725 : Blo 1526460 24765725 := bstep (se 3 (by rfl) ⟨4643573, by rfl⟩ : syracuseStep 24765725 = 9287147) B9287147
theorem B2065735 : Blo 1526460 2065735 := bstep (se 1 (by rfl) ⟨1549301, by rfl⟩ : syracuseStep 2065735 = 3098603) B3098603
theorem B11593529 : Blo 1526460 11593529 := bstep (se 2 (by rfl) ⟨4347573, by rfl⟩ : syracuseStep 11593529 = 8695147) B8695147
theorem B5155055 : Blo 1526460 5155055 := bstep (se 1 (by rfl) ⟨3866291, by rfl⟩ : syracuseStep 5155055 = 7732583) B7732583
theorem B3434849 : Blo 1526460 3434849 := bstep (se 2 (by rfl) ⟨1288068, by rfl⟩ : syracuseStep 3434849 = 2576137) B2576137
theorem B7735661 : Blo 1526460 7735661 := bstep (se 3 (by rfl) ⟨1450436, by rfl⟩ : syracuseStep 7735661 = 2900873) B2900873
theorem B3434921 : Blo 1526460 3434921 := bstep (se 2 (by rfl) ⟨1288095, by rfl⟩ : syracuseStep 3434921 = 2576191) B2576191
theorem B5155325 : Blo 1526460 5155325 := bstep (se 3 (by rfl) ⟨966623, by rfl⟩ : syracuseStep 5155325 = 1933247) B1933247
theorem B7735823 : Blo 1526460 7735823 := bstep (se 1 (by rfl) ⟨5801867, by rfl⟩ : syracuseStep 7735823 = 11603735) B11603735
theorem B9792089 : Blo 1526460 9792089 := bstep (se 2 (by rfl) ⟨3672033, by rfl⟩ : syracuseStep 9792089 = 7344067) B7344067
theorem B3435227 : Blo 1526460 3435227 := bstep (se 1 (by rfl) ⟨2576420, by rfl⟩ : syracuseStep 3435227 = 5152841) B5152841
theorem B1526503 : Blo 1526460 1526503 := bstep (se 1 (by rfl) ⟨1144877, by rfl⟩ : syracuseStep 1526503 = 2289755) B2289755
theorem B15674195 : Blo 1526460 15674195 := bstep (se 1 (by rfl) ⟨11755646, by rfl⟩ : syracuseStep 15674195 = 23511293) B23511293
theorem B2321471 : Blo 1526460 2321471 := bstep (se 1 (by rfl) ⟨1741103, by rfl⟩ : syracuseStep 2321471 = 3482207) B3482207
theorem B1526895 : Blo 1526460 1526895 := bstep (se 1 (by rfl) ⟨1145171, by rfl⟩ : syracuseStep 1526895 = 2290343) B2290343
theorem B7834799 : Blo 1526460 7834799 := bstep (se 1 (by rfl) ⟨5876099, by rfl⟩ : syracuseStep 7834799 = 11752199) B11752199
theorem B1526975 : Blo 1526460 1526975 := bstep (se 1 (by rfl) ⟨1145231, by rfl⟩ : syracuseStep 1526975 = 2290463) B2290463
theorem B4705487 : Blo 1526460 4705487 := bstep (se 1 (by rfl) ⟨3529115, by rfl⟩ : syracuseStep 4705487 = 7058231) B7058231
theorem B3435731 : Blo 1526460 3435731 := bstep (se 1 (by rfl) ⟨2576798, by rfl⟩ : syracuseStep 3435731 = 5153597) B5153597
theorem B11594987 : Blo 1526460 11594987 := bstep (se 1 (by rfl) ⟨8696240, by rfl⟩ : syracuseStep 11594987 = 17392481) B17392481
theorem B1527295 : Blo 1526460 1527295 := bstep (se 1 (by rfl) ⟨1145471, by rfl⟩ : syracuseStep 1527295 = 2290943) B2290943
theorem B8695673 : Blo 1526460 8695673 := bstep (se 2 (by rfl) ⟨3260877, by rfl⟩ : syracuseStep 8695673 = 6521755) B6521755
theorem B1527743 : Blo 1526460 1527743 := bstep (se 1 (by rfl) ⟨1145807, by rfl⟩ : syracuseStep 1527743 = 2291615) B2291615
theorem B3436523 : Blo 1526460 3436523 := bstep (se 1 (by rfl) ⟨2577392, by rfl⟩ : syracuseStep 3436523 = 5154785) B5154785
theorem B7344107 : Blo 1526460 7344107 := bstep (se 1 (by rfl) ⟨5508080, by rfl⟩ : syracuseStep 7344107 = 11016161) B11016161
theorem B2175131 : Blo 1526460 2175131 := bstep (se 1 (by rfl) ⟨1631348, by rfl⟩ : syracuseStep 2175131 = 3262697) B3262697
theorem B3437225 : Blo 1526460 3437225 := bstep (se 2 (by rfl) ⟨1288959, by rfl⟩ : syracuseStep 3437225 = 2577919) B2577919
theorem B26112779 : Blo 1526460 26112779 := bstep (se 1 (by rfl) ⟨19584584, by rfl⟩ : syracuseStep 26112779 = 39169169) B39169169
theorem B13931311 : Blo 1526460 13931311 := bstep (se 1 (by rfl) ⟨10448483, by rfl⟩ : syracuseStep 13931311 = 20896967) B20896967
theorem B55751483 : Blo 1526460 55751483 := bstep (se 1 (by rfl) ⟨41813612, by rfl⟩ : syracuseStep 55751483 = 83627225) B83627225
theorem B2577359 : Blo 1526460 2577359 := bstep (se 1 (by rfl) ⟨1933019, by rfl⟩ : syracuseStep 2577359 = 3866039) B3866039
theorem B7730153 : Blo 1526460 7730153 := bstep (se 2 (by rfl) ⟨2898807, by rfl⟩ : syracuseStep 7730153 = 5797615) B5797615
theorem B2290667 : Blo 1526460 2290667 := bstep (se 1 (by rfl) ⟨1718000, by rfl⟩ : syracuseStep 2290667 = 3436001) B3436001
theorem B23516219 : Blo 1526460 23516219 := bstep (se 1 (by rfl) ⟨17637164, by rfl⟩ : syracuseStep 23516219 = 35274329) B35274329
theorem B3437729 : Blo 1526460 3437729 := bstep (se 2 (by rfl) ⟨1289148, by rfl⟩ : syracuseStep 3437729 = 2578297) B2578297
theorem B3437927 : Blo 1526460 3437927 := bstep (se 1 (by rfl) ⟨2578445, by rfl⟩ : syracuseStep 3437927 = 5156891) B5156891
theorem B3863983 : Blo 1526460 3863983 := bstep (se 1 (by rfl) ⟨2897987, by rfl⟩ : syracuseStep 3863983 = 5795975) B5795975
theorem B2577899 : Blo 1526460 2577899 := bstep (se 1 (by rfl) ⟨1933424, by rfl⟩ : syracuseStep 2577899 = 3866849) B3866849
theorem B1717807 : Blo 1526460 1717807 := bstep (se 1 (by rfl) ⟨1288355, by rfl⟩ : syracuseStep 1717807 = 2576711) B2576711
theorem B23516729 : Blo 1526460 23516729 := bstep (se 2 (by rfl) ⟨8818773, by rfl⟩ : syracuseStep 23516729 = 17637547) B17637547
theorem B3438287 : Blo 1526460 3438287 := bstep (se 1 (by rfl) ⟨2578715, by rfl⟩ : syracuseStep 3438287 = 5157431) B5157431
theorem B4126585 : Blo 1526460 4126585 := bstep (se 2 (by rfl) ⟨1547469, by rfl⟩ : syracuseStep 4126585 = 3094939) B3094939
theorem B8697881 : Blo 1526460 8697881 := bstep (se 2 (by rfl) ⟨3261705, by rfl⟩ : syracuseStep 8697881 = 6523411) B6523411
theorem B6527087 : Blo 1526460 6527087 := bstep (se 1 (by rfl) ⟨4895315, by rfl⟩ : syracuseStep 6527087 = 9790631) B9790631
theorem B15890717 : Blo 1526460 15890717 := bstep (se 3 (by rfl) ⟨2979509, by rfl⟩ : syracuseStep 15890717 = 5959019) B5959019
theorem B2291999 : Blo 1526460 2291999 := bstep (se 1 (by rfl) ⟨1718999, by rfl⟩ : syracuseStep 2291999 = 3437999) B3437999
theorem B3864935 : Blo 1526460 3864935 := bstep (se 1 (by rfl) ⟨2898701, by rfl⟩ : syracuseStep 3864935 = 5797403) B5797403
theorem B2292071 : Blo 1526460 2292071 := bstep (se 1 (by rfl) ⟨1719053, by rfl⟩ : syracuseStep 2292071 = 3438107) B3438107
theorem B8698337 : Blo 1526460 8698337 := bstep (se 2 (by rfl) ⟨3261876, by rfl⟩ : syracuseStep 8698337 = 6523753) B6523753
theorem B71490235 : Blo 1526460 71490235 := bstep (se 1 (by rfl) ⟨53617676, by rfl⟩ : syracuseStep 71490235 = 107235353) B107235353
theorem B2579195 : Blo 1526460 2579195 := bstep (se 1 (by rfl) ⟨1934396, by rfl⟩ : syracuseStep 2579195 = 3868793) B3868793
theorem B1719103 : Blo 1526460 1719103 := bstep (se 1 (by rfl) ⟨1289327, by rfl⟩ : syracuseStep 1719103 = 2578655) B2578655
theorem B41827195 : Blo 1526460 41827195 := bstep (se 1 (by rfl) ⟨31370396, by rfl⟩ : syracuseStep 41827195 = 62740793) B62740793
theorem B3865583 : Blo 1526460 3865583 := bstep (se 1 (by rfl) ⟨2899187, by rfl⟩ : syracuseStep 3865583 = 5798375) B5798375
theorem B1719391 : Blo 1526460 1719391 := bstep (se 1 (by rfl) ⟨1289543, by rfl⟩ : syracuseStep 1719391 = 2579087) B2579087
theorem B4349305 : Blo 1526460 4349305 := bstep (se 2 (by rfl) ⟨1630989, by rfl⟩ : syracuseStep 4349305 = 3261979) B3261979
theorem B29752739 : Blo 1526460 29752739 := bstep (se 1 (by rfl) ⟨22314554, by rfl⟩ : syracuseStep 29752739 = 44629109) B44629109
theorem B1547903 : Blo 1526460 1547903 := bstep (se 1 (by rfl) ⟨1160927, by rfl⟩ : syracuseStep 1547903 = 2321855) B2321855
theorem B3866363 : Blo 1526460 3866363 := bstep (se 1 (by rfl) ⟨2899772, by rfl⟩ : syracuseStep 3866363 = 5799545) B5799545
theorem B66158365 : Blo 1526460 66158365 := bstep (se 3 (by rfl) ⟨12404693, by rfl⟩ : syracuseStep 66158365 = 24809387) B24809387
theorem B2899795 : Blo 1526460 2899795 := bstep (se 1 (by rfl) ⟨2174846, by rfl⟩ : syracuseStep 2899795 = 4349693) B4349693
theorem B9781631 : Blo 1526460 9781631 := bstep (se 1 (by rfl) ⟨7336223, by rfl⟩ : syracuseStep 9781631 = 14672447) B14672447
theorem B5800349 : Blo 1526460 5800349 := bstep (se 3 (by rfl) ⟨1087565, by rfl⟩ : syracuseStep 5800349 = 2175131) B2175131
theorem B17408519 : Blo 1526460 17408519 := bstep (se 1 (by rfl) ⟨13056389, by rfl⟩ : syracuseStep 17408519 = 26112779) B26112779
theorem B37167655 : Blo 1526460 37167655 := bstep (se 1 (by rfl) ⟨27875741, by rfl⟩ : syracuseStep 37167655 = 55751483) B55751483
theorem B2900623 : Blo 1526460 2900623 := bstep (se 1 (by rfl) ⟨2175467, by rfl⟩ : syracuseStep 2900623 = 4350935) B4350935
theorem B5153435 : Blo 1526460 5153435 := bstep (se 1 (by rfl) ⟨3865076, by rfl⟩ : syracuseStep 5153435 = 7730153) B7730153
theorem B4129505 : Blo 1526460 4129505 := bstep (se 2 (by rfl) ⟨1548564, by rfl⟩ : syracuseStep 4129505 = 3097129) B3097129
theorem B4351391 : Blo 1526460 4351391 := bstep (se 1 (by rfl) ⟨3263543, by rfl⟩ : syracuseStep 4351391 = 6527087) B6527087
theorem B10593811 : Blo 1526460 10593811 := bstep (se 1 (by rfl) ⟨7945358, by rfl⟩ : syracuseStep 10593811 = 15890717) B15890717
theorem B2754313 : Blo 1526460 2754313 := bstep (se 2 (by rfl) ⟨1032867, by rfl⟩ : syracuseStep 2754313 = 2065735) B2065735
theorem B41797853 : Blo 1526460 41797853 := bstep (se 3 (by rfl) ⟨7837097, by rfl⟩ : syracuseStep 41797853 = 15674195) B15674195
theorem B19835159 : Blo 1526460 19835159 := bstep (se 1 (by rfl) ⟨14876369, by rfl⟩ : syracuseStep 19835159 = 29752739) B29752739
theorem B2321131 : Blo 1526460 2321131 := bstep (se 1 (by rfl) ⟨1740848, by rfl⟩ : syracuseStep 2321131 = 3481697) B3481697
theorem B5156027 : Blo 1526460 5156027 := bstep (se 1 (by rfl) ⟨3867020, by rfl⟩ : syracuseStep 5156027 = 7734041) B7734041
theorem B1527111 : Blo 1526460 1527111 := bstep (se 1 (by rfl) ⟨1145333, by rfl⟩ : syracuseStep 1527111 = 2290667) B2290667
theorem B16510483 : Blo 1526460 16510483 := bstep (se 1 (by rfl) ⟨12382862, by rfl⟩ : syracuseStep 16510483 = 24765725) B24765725
theorem B18575081 : Blo 1526460 18575081 := bstep (se 2 (by rfl) ⟨6965655, by rfl⟩ : syracuseStep 18575081 = 13931311) B13931311
theorem B7729019 : Blo 1526460 7729019 := bstep (se 1 (by rfl) ⟨5796764, by rfl⟩ : syracuseStep 7729019 = 11593529) B11593529
theorem B3436703 : Blo 1526460 3436703 := bstep (se 1 (by rfl) ⟨2577527, by rfl⟩ : syracuseStep 3436703 = 5155055) B5155055
theorem B1527999 : Blo 1526460 1527999 := bstep (se 1 (by rfl) ⟨1145999, by rfl⟩ : syracuseStep 1527999 = 2291999) B2291999
theorem B2289899 : Blo 1526460 2289899 := bstep (se 1 (by rfl) ⟨1717424, by rfl⟩ : syracuseStep 2289899 = 3434849) B3434849
theorem B2576623 : Blo 1526460 2576623 := bstep (se 1 (by rfl) ⟨1932467, by rfl⟩ : syracuseStep 2576623 = 3864935) B3864935
theorem B1528047 : Blo 1526460 1528047 := bstep (se 1 (by rfl) ⟨1146035, by rfl⟩ : syracuseStep 1528047 = 2292071) B2292071
theorem B5157107 : Blo 1526460 5157107 := bstep (se 1 (by rfl) ⟨3867830, by rfl⟩ : syracuseStep 5157107 = 7735661) B7735661
theorem B2289947 : Blo 1526460 2289947 := bstep (se 1 (by rfl) ⟨1717460, by rfl⟩ : syracuseStep 2289947 = 3434921) B3434921
theorem B3436883 : Blo 1526460 3436883 := bstep (se 1 (by rfl) ⟨2577662, by rfl⟩ : syracuseStep 3436883 = 5155325) B5155325
theorem B5157215 : Blo 1526460 5157215 := bstep (se 1 (by rfl) ⟨3867911, by rfl⟩ : syracuseStep 5157215 = 7735823) B7735823
theorem B2290151 : Blo 1526460 2290151 := bstep (se 1 (by rfl) ⟨1717613, by rfl⟩ : syracuseStep 2290151 = 3435227) B3435227
theorem B2577055 : Blo 1526460 2577055 := bstep (se 1 (by rfl) ⟨1932791, by rfl⟩ : syracuseStep 2577055 = 3865583) B3865583
theorem B2290409 : Blo 1526460 2290409 := bstep (se 2 (by rfl) ⟨858903, by rfl⟩ : syracuseStep 2290409 = 1717807) B1717807
theorem B5223199 : Blo 1526460 5223199 := bstep (se 1 (by rfl) ⟨3917399, by rfl⟩ : syracuseStep 5223199 = 7834799) B7834799
theorem B2290487 : Blo 1526460 2290487 := bstep (se 1 (by rfl) ⟨1717865, by rfl⟩ : syracuseStep 2290487 = 3435731) B3435731
theorem B7729991 : Blo 1526460 7729991 := bstep (se 1 (by rfl) ⟨5797493, by rfl⟩ : syracuseStep 7729991 = 11594987) B11594987
theorem B5502113 : Blo 1526460 5502113 := bstep (se 2 (by rfl) ⟨2063292, by rfl⟩ : syracuseStep 5502113 = 4126585) B4126585
theorem B2577575 : Blo 1526460 2577575 := bstep (se 1 (by rfl) ⟨1933181, by rfl⟩ : syracuseStep 2577575 = 3866363) B3866363
theorem B5797115 : Blo 1526460 5797115 := bstep (se 1 (by rfl) ⟨4347836, by rfl⟩ : syracuseStep 5797115 = 8695673) B8695673
theorem B2291015 : Blo 1526460 2291015 := bstep (se 1 (by rfl) ⟨1718261, by rfl⟩ : syracuseStep 2291015 = 3436523) B3436523
theorem B4896071 : Blo 1526460 4896071 := bstep (se 1 (by rfl) ⟨3672053, by rfl⟩ : syracuseStep 4896071 = 7344107) B7344107
theorem B2577791 : Blo 1526460 2577791 := bstep (se 1 (by rfl) ⟨1933343, by rfl⟩ : syracuseStep 2577791 = 3866687) B3866687
theorem B11015639 : Blo 1526460 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B6190589 : Blo 1526460 6190589 := bstep (se 3 (by rfl) ⟨1160735, by rfl⟩ : syracuseStep 6190589 = 2321471) B2321471
theorem B2291483 : Blo 1526460 2291483 := bstep (se 1 (by rfl) ⟨1718612, by rfl⟩ : syracuseStep 2291483 = 3437225) B3437225
theorem B1718239 : Blo 1526460 1718239 := bstep (se 1 (by rfl) ⟨1288679, by rfl⟩ : syracuseStep 1718239 = 2577359) B2577359
theorem B2578459 : Blo 1526460 2578459 := bstep (se 1 (by rfl) ⟨1933844, by rfl⟩ : syracuseStep 2578459 = 3867689) B3867689
theorem B15677479 : Blo 1526460 15677479 := bstep (se 1 (by rfl) ⟨11758109, by rfl⟩ : syracuseStep 15677479 = 23516219) B23516219
theorem B2291819 : Blo 1526460 2291819 := bstep (se 1 (by rfl) ⟨1718864, by rfl⟩ : syracuseStep 2291819 = 3437729) B3437729
theorem B2291951 : Blo 1526460 2291951 := bstep (se 1 (by rfl) ⟨1718963, by rfl⟩ : syracuseStep 2291951 = 3437927) B3437927
theorem B95320313 : Blo 1526460 95320313 := bstep (se 2 (by rfl) ⟨35745117, by rfl⟩ : syracuseStep 95320313 = 71490235) B71490235
theorem B1718599 : Blo 1526460 1718599 := bstep (se 1 (by rfl) ⟨1288949, by rfl⟩ : syracuseStep 1718599 = 2577899) B2577899
theorem B15677819 : Blo 1526460 15677819 := bstep (se 1 (by rfl) ⟨11758364, by rfl⟩ : syracuseStep 15677819 = 23516729) B23516729
theorem B2292137 : Blo 1526460 2292137 := bstep (se 2 (by rfl) ⟨859551, by rfl⟩ : syracuseStep 2292137 = 1719103) B1719103
theorem B2292191 : Blo 1526460 2292191 := bstep (se 1 (by rfl) ⟨1719143, by rfl⟩ : syracuseStep 2292191 = 3438287) B3438287
theorem B55769593 : Blo 1526460 55769593 := bstep (se 2 (by rfl) ⟨20913597, by rfl⟩ : syracuseStep 55769593 = 41827195) B41827195
theorem B5798587 : Blo 1526460 5798587 := bstep (se 1 (by rfl) ⟨4348940, by rfl⟩ : syracuseStep 5798587 = 8697881) B8697881
theorem B2292521 : Blo 1526460 2292521 := bstep (se 2 (by rfl) ⟨859695, by rfl⟩ : syracuseStep 2292521 = 1719391) B1719391
theorem B5798891 : Blo 1526460 5798891 := bstep (se 1 (by rfl) ⟨4349168, by rfl⟩ : syracuseStep 5798891 = 8698337) B8698337
theorem B4127741 : Blo 1526460 4127741 := bstep (se 3 (by rfl) ⟨773951, by rfl⟩ : syracuseStep 4127741 = 1547903) B1547903
theorem B6528059 : Blo 1526460 6528059 := bstep (se 1 (by rfl) ⟨4896044, by rfl⟩ : syracuseStep 6528059 = 9792089) B9792089
theorem B5799073 : Blo 1526460 5799073 := bstep (se 2 (by rfl) ⟨2174652, by rfl⟩ : syracuseStep 5799073 = 4349305) B4349305
theorem B1719463 : Blo 1526460 1719463 := bstep (se 1 (by rfl) ⟨1289597, by rfl⟩ : syracuseStep 1719463 = 2579195) B2579195
theorem B5151977 : Blo 1526460 5151977 := bstep (se 2 (by rfl) ⟨1931991, by rfl⟩ : syracuseStep 5151977 = 3863983) B3863983
theorem B3136991 : Blo 1526460 3136991 := bstep (se 1 (by rfl) ⟨2352743, by rfl⟩ : syracuseStep 3136991 = 4705487) B4705487
theorem B88211153 : Blo 1526460 88211153 := bstep (se 2 (by rfl) ⟨33079182, by rfl⟩ : syracuseStep 88211153 = 66158365) B66158365
theorem B3866393 : Blo 1526460 3866393 := bstep (se 2 (by rfl) ⟨1449897, by rfl⟩ : syracuseStep 3866393 = 2899795) B2899795
theorem B56500325 : Blo 1526460 56500325 := bstep (se 4 (by rfl) ⟨5296905, by rfl⟩ : syracuseStep 56500325 = 10593811) B10593811
theorem B6521087 : Blo 1526460 6521087 := bstep (se 1 (by rfl) ⟨4890815, by rfl⟩ : syracuseStep 6521087 = 9781631) B9781631
theorem B3866899 : Blo 1526460 3866899 := bstep (se 1 (by rfl) ⟨2900174, by rfl⟩ : syracuseStep 3866899 = 5800349) B5800349
theorem B2753003 : Blo 1526460 2753003 := bstep (se 1 (by rfl) ⟨2064752, by rfl⟩ : syracuseStep 2753003 = 4129505) B4129505
theorem B5153327 : Blo 1526460 5153327 := bstep (se 1 (by rfl) ⟨3864995, by rfl⟩ : syracuseStep 5153327 = 7729991) B7729991
theorem B74359457 : Blo 1526460 74359457 := bstep (se 2 (by rfl) ⟨27884796, by rfl⟩ : syracuseStep 74359457 = 55769593) B55769593
theorem B3867497 : Blo 1526460 3867497 := bstep (se 2 (by rfl) ⟨1450311, by rfl⟩ : syracuseStep 3867497 = 2900623) B2900623
theorem B2900927 : Blo 1526460 2900927 := bstep (se 1 (by rfl) ⟨2175695, by rfl⟩ : syracuseStep 2900927 = 4351391) B4351391
theorem B6964265 : Blo 1526460 6964265 := bstep (se 2 (by rfl) ⟨2611599, by rfl⟩ : syracuseStep 6964265 = 5223199) B5223199
theorem B14689669 : Blo 1526460 14689669 := bstep (se 4 (by rfl) ⟨1377156, by rfl⟩ : syracuseStep 14689669 = 2754313) B2754313
theorem B63546875 : Blo 1526460 63546875 := bstep (se 1 (by rfl) ⟨47660156, by rfl⟩ : syracuseStep 63546875 = 95320313) B95320313
theorem B22013977 : Blo 1526460 22013977 := bstep (se 2 (by rfl) ⟨8255241, by rfl⟩ : syracuseStep 22013977 = 16510483) B16510483
theorem B4352039 : Blo 1526460 4352039 := bstep (se 1 (by rfl) ⟨3264029, by rfl⟩ : syracuseStep 4352039 = 6528059) B6528059
theorem B3434651 : Blo 1526460 3434651 := bstep (se 1 (by rfl) ⟨2575988, by rfl⟩ : syracuseStep 3434651 = 5151977) B5151977
theorem B1526599 : Blo 1526460 1526599 := bstep (se 1 (by rfl) ⟨1144949, by rfl⟩ : syracuseStep 1526599 = 2289899) B2289899
theorem B1526631 : Blo 1526460 1526631 := bstep (se 1 (by rfl) ⟨1144973, by rfl⟩ : syracuseStep 1526631 = 2289947) B2289947
theorem B3435497 : Blo 1526460 3435497 := bstep (se 2 (by rfl) ⟨1288311, by rfl⟩ : syracuseStep 3435497 = 2576623) B2576623
theorem B1526767 : Blo 1526460 1526767 := bstep (se 1 (by rfl) ⟨1145075, by rfl⟩ : syracuseStep 1526767 = 2290151) B2290151
theorem B3435623 : Blo 1526460 3435623 := bstep (se 1 (by rfl) ⟨2576717, by rfl⟩ : syracuseStep 3435623 = 5153435) B5153435
theorem B1526939 : Blo 1526460 1526939 := bstep (se 1 (by rfl) ⟨1145204, by rfl⟩ : syracuseStep 1526939 = 2290409) B2290409
theorem B1526991 : Blo 1526460 1526991 := bstep (se 1 (by rfl) ⟨1145243, by rfl⟩ : syracuseStep 1526991 = 2290487) B2290487
theorem B49556873 : Blo 1526460 49556873 := bstep (se 2 (by rfl) ⟨18583827, by rfl⟩ : syracuseStep 49556873 = 37167655) B37167655
theorem B3436073 : Blo 1526460 3436073 := bstep (se 2 (by rfl) ⟨1288527, by rfl⟩ : syracuseStep 3436073 = 2577055) B2577055
theorem B1527343 : Blo 1526460 1527343 := bstep (se 1 (by rfl) ⟨1145507, by rfl⟩ : syracuseStep 1527343 = 2291015) B2291015
theorem B3264047 : Blo 1526460 3264047 := bstep (se 1 (by rfl) ⟨2448035, by rfl⟩ : syracuseStep 3264047 = 4896071) B4896071
theorem B7343759 : Blo 1526460 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B1527655 : Blo 1526460 1527655 := bstep (se 1 (by rfl) ⟨1145741, by rfl⟩ : syracuseStep 1527655 = 2291483) B2291483
theorem B1527879 : Blo 1526460 1527879 := bstep (se 1 (by rfl) ⟨1145909, by rfl⟩ : syracuseStep 1527879 = 2291819) B2291819
theorem B27865235 : Blo 1526460 27865235 := bstep (se 1 (by rfl) ⟨20898926, by rfl⟩ : syracuseStep 27865235 = 41797853) B41797853
theorem B1527967 : Blo 1526460 1527967 := bstep (se 1 (by rfl) ⟨1145975, by rfl⟩ : syracuseStep 1527967 = 2291951) B2291951
theorem B1528091 : Blo 1526460 1528091 := bstep (se 1 (by rfl) ⟨1146068, by rfl⟩ : syracuseStep 1528091 = 2292137) B2292137
theorem B1528127 : Blo 1526460 1528127 := bstep (se 1 (by rfl) ⟨1146095, by rfl⟩ : syracuseStep 1528127 = 2292191) B2292191
theorem B1528347 : Blo 1526460 1528347 := bstep (se 1 (by rfl) ⟨1146260, by rfl⟩ : syracuseStep 1528347 = 2292521) B2292521
theorem B235229741 : Blo 1526460 235229741 := bstep (se 3 (by rfl) ⟨44105576, by rfl⟩ : syracuseStep 235229741 = 88211153) B88211153
theorem B3437351 : Blo 1526460 3437351 := bstep (se 1 (by rfl) ⟨2578013, by rfl⟩ : syracuseStep 3437351 = 5156027) B5156027
theorem B33461237 : Blo 1526460 33461237 := bstep (se 5 (by rfl) ⟨1568495, by rfl⟩ : syracuseStep 33461237 = 3136991) B3136991
theorem B12383387 : Blo 1526460 12383387 := bstep (se 1 (by rfl) ⟨9287540, by rfl⟩ : syracuseStep 12383387 = 18575081) B18575081
theorem B2577595 : Blo 1526460 2577595 := bstep (se 1 (by rfl) ⟨1933196, by rfl⟩ : syracuseStep 2577595 = 3866393) B3866393
theorem B2290985 : Blo 1526460 2290985 := bstep (se 2 (by rfl) ⟨859119, by rfl⟩ : syracuseStep 2290985 = 1718239) B1718239
theorem B3437945 : Blo 1526460 3437945 := bstep (se 2 (by rfl) ⟨1289229, by rfl⟩ : syracuseStep 3437945 = 2578459) B2578459
theorem B20903305 : Blo 1526460 20903305 := bstep (se 2 (by rfl) ⟨7838739, by rfl⟩ : syracuseStep 20903305 = 15677479) B15677479
theorem B2291135 : Blo 1526460 2291135 := bstep (se 1 (by rfl) ⟨1718351, by rfl⟩ : syracuseStep 2291135 = 3436703) B3436703
theorem B3438071 : Blo 1526460 3438071 := bstep (se 1 (by rfl) ⟨2578553, by rfl⟩ : syracuseStep 3438071 = 5157107) B5157107
theorem B2291255 : Blo 1526460 2291255 := bstep (se 1 (by rfl) ⟨1718441, by rfl⟩ : syracuseStep 2291255 = 3436883) B3436883
theorem B3438143 : Blo 1526460 3438143 := bstep (se 1 (by rfl) ⟨2578607, by rfl⟩ : syracuseStep 3438143 = 5157215) B5157215
theorem B11605679 : Blo 1526460 11605679 := bstep (se 1 (by rfl) ⟨8704259, by rfl⟩ : syracuseStep 11605679 = 17408519) B17408519
theorem B2291465 : Blo 1526460 2291465 := bstep (se 2 (by rfl) ⟨859299, by rfl⟩ : syracuseStep 2291465 = 1718599) B1718599
theorem B52893757 : Blo 1526460 52893757 := bstep (se 3 (by rfl) ⟨9917579, by rfl⟩ : syracuseStep 52893757 = 19835159) B19835159
theorem B3668075 : Blo 1526460 3668075 := bstep (se 1 (by rfl) ⟨2751056, by rfl⟩ : syracuseStep 3668075 = 5502113) B5502113
theorem B1718383 : Blo 1526460 1718383 := bstep (se 1 (by rfl) ⟨1288787, by rfl⟩ : syracuseStep 1718383 = 2577575) B2577575
theorem B3864743 : Blo 1526460 3864743 := bstep (se 1 (by rfl) ⟨2898557, by rfl⟩ : syracuseStep 3864743 = 5797115) B5797115
theorem B7731449 : Blo 1526460 7731449 := bstep (se 2 (by rfl) ⟨2899293, by rfl⟩ : syracuseStep 7731449 = 5798587) B5798587
theorem B1718527 : Blo 1526460 1718527 := bstep (se 1 (by rfl) ⟨1288895, by rfl⟩ : syracuseStep 1718527 = 2577791) B2577791
theorem B3094841 : Blo 1526460 3094841 := bstep (se 2 (by rfl) ⟨1160565, by rfl⟩ : syracuseStep 3094841 = 2321131) B2321131
theorem B4127059 : Blo 1526460 4127059 := bstep (se 1 (by rfl) ⟨3095294, by rfl⟩ : syracuseStep 4127059 = 6190589) B6190589
theorem B7732097 : Blo 1526460 7732097 := bstep (se 2 (by rfl) ⟨2899536, by rfl⟩ : syracuseStep 7732097 = 5799073) B5799073
theorem B2292617 : Blo 1526460 2292617 := bstep (se 2 (by rfl) ⟨859731, by rfl⟩ : syracuseStep 2292617 = 1719463) B1719463
theorem B10451879 : Blo 1526460 10451879 := bstep (se 1 (by rfl) ⟨7838909, by rfl⟩ : syracuseStep 10451879 = 15677819) B15677819
theorem B3865927 : Blo 1526460 3865927 := bstep (se 1 (by rfl) ⟨2899445, by rfl⟩ : syracuseStep 3865927 = 5798891) B5798891
theorem B2751827 : Blo 1526460 2751827 := bstep (se 1 (by rfl) ⟨2063870, by rfl⟩ : syracuseStep 2751827 = 4127741) B4127741
theorem B5152679 : Blo 1526460 5152679 := bstep (se 1 (by rfl) ⟨3864509, by rfl⟩ : syracuseStep 5152679 = 7729019) B7729019
theorem B29351969 : Blo 1526460 29351969 := bstep (se 2 (by rfl) ⟨11006988, by rfl⟩ : syracuseStep 29351969 = 22013977) B22013977
theorem B37666883 : Blo 1526460 37666883 := bstep (se 1 (by rfl) ⟨28250162, by rfl⟩ : syracuseStep 37666883 = 56500325) B56500325
theorem B70525009 : Blo 1526460 70525009 := bstep (se 2 (by rfl) ⟨26446878, by rfl⟩ : syracuseStep 70525009 = 52893757) B52893757
theorem B18571373 : Blo 1526460 18571373 := bstep (se 3 (by rfl) ⟨3482132, by rfl⟩ : syracuseStep 18571373 = 6964265) B6964265
theorem B1835335 : Blo 1526460 1835335 := bstep (se 1 (by rfl) ⟨1376501, by rfl⟩ : syracuseStep 1835335 = 2753003) B2753003
theorem B156819827 : Blo 1526460 156819827 := bstep (se 1 (by rfl) ⟨117614870, by rfl⟩ : syracuseStep 156819827 = 235229741) B235229741
theorem B1933951 : Blo 1526460 1933951 := bstep (se 1 (by rfl) ⟨1450463, by rfl⟩ : syracuseStep 1933951 = 2900927) B2900927
theorem B22307491 : Blo 1526460 22307491 := bstep (se 1 (by rfl) ⟨16730618, by rfl⟩ : syracuseStep 22307491 = 33461237) B33461237
theorem B2901359 : Blo 1526460 2901359 := bstep (se 1 (by rfl) ⟨2176019, by rfl⟩ : syracuseStep 2901359 = 4352039) B4352039
theorem B5154299 : Blo 1526460 5154299 := bstep (se 1 (by rfl) ⟨3865724, by rfl⟩ : syracuseStep 5154299 = 7731449) B7731449
theorem B5154569 : Blo 1526460 5154569 := bstep (se 2 (by rfl) ⟨1932963, by rfl⟩ : syracuseStep 5154569 = 3865927) B3865927
theorem B27871073 : Blo 1526460 27871073 := bstep (se 2 (by rfl) ⟨10451652, by rfl⟩ : syracuseStep 27871073 = 20903305) B20903305
theorem B5154731 : Blo 1526460 5154731 := bstep (se 1 (by rfl) ⟨3866048, by rfl⟩ : syracuseStep 5154731 = 7732097) B7732097
theorem B3435119 : Blo 1526460 3435119 := bstep (se 1 (by rfl) ⟨2576339, by rfl⟩ : syracuseStep 3435119 = 5152679) B5152679
theorem B5155865 : Blo 1526460 5155865 := bstep (se 2 (by rfl) ⟨1933449, by rfl⟩ : syracuseStep 5155865 = 3866899) B3866899
theorem B3435551 : Blo 1526460 3435551 := bstep (se 1 (by rfl) ⟨2576663, by rfl⟩ : syracuseStep 3435551 = 5153327) B5153327
theorem B49572971 : Blo 1526460 49572971 := bstep (se 1 (by rfl) ⟨37179728, by rfl⟩ : syracuseStep 49572971 = 74359457) B74359457
theorem B1527323 : Blo 1526460 1527323 := bstep (se 1 (by rfl) ⟨1145492, by rfl⟩ : syracuseStep 1527323 = 2290985) B2290985
theorem B1527423 : Blo 1526460 1527423 := bstep (se 1 (by rfl) ⟨1145567, by rfl⟩ : syracuseStep 1527423 = 2291135) B2291135
theorem B42364583 : Blo 1526460 42364583 := bstep (se 1 (by rfl) ⟨31773437, by rfl⟩ : syracuseStep 42364583 = 63546875) B63546875
theorem B1527503 : Blo 1526460 1527503 := bstep (se 1 (by rfl) ⟨1145627, by rfl⟩ : syracuseStep 1527503 = 2291255) B2291255
theorem B7737119 : Blo 1526460 7737119 := bstep (se 1 (by rfl) ⟨5802839, by rfl⟩ : syracuseStep 7737119 = 11605679) B11605679
theorem B1527643 : Blo 1526460 1527643 := bstep (se 1 (by rfl) ⟨1145732, by rfl⟩ : syracuseStep 1527643 = 2291465) B2291465
theorem B2445383 : Blo 1526460 2445383 := bstep (se 1 (by rfl) ⟨1834037, by rfl⟩ : syracuseStep 2445383 = 3668075) B3668075
theorem B2289767 : Blo 1526460 2289767 := bstep (se 1 (by rfl) ⟨1717325, by rfl⟩ : syracuseStep 2289767 = 3434651) B3434651
theorem B2576495 : Blo 1526460 2576495 := bstep (se 1 (by rfl) ⟨1932371, by rfl⟩ : syracuseStep 2576495 = 3864743) B3864743
theorem B3436793 : Blo 1526460 3436793 := bstep (se 2 (by rfl) ⟨1288797, by rfl⟩ : syracuseStep 3436793 = 2577595) B2577595
theorem B1528411 : Blo 1526460 1528411 := bstep (se 1 (by rfl) ⟨1146308, by rfl⟩ : syracuseStep 1528411 = 2292617) B2292617
theorem B6967919 : Blo 1526460 6967919 := bstep (se 1 (by rfl) ⟨5225939, by rfl⟩ : syracuseStep 6967919 = 10451879) B10451879
theorem B2290331 : Blo 1526460 2290331 := bstep (se 1 (by rfl) ⟨1717748, by rfl⟩ : syracuseStep 2290331 = 3435497) B3435497
theorem B2290415 : Blo 1526460 2290415 := bstep (se 1 (by rfl) ⟨1717811, by rfl⟩ : syracuseStep 2290415 = 3435623) B3435623
theorem B2290715 : Blo 1526460 2290715 := bstep (se 1 (by rfl) ⟨1718036, by rfl⟩ : syracuseStep 2290715 = 3436073) B3436073
theorem B2176031 : Blo 1526460 2176031 := bstep (se 1 (by rfl) ⟨1632023, by rfl⟩ : syracuseStep 2176031 = 3264047) B3264047
theorem B4895839 : Blo 1526460 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B18576823 : Blo 1526460 18576823 := bstep (se 1 (by rfl) ⟨13932617, by rfl⟩ : syracuseStep 18576823 = 27865235) B27865235
theorem B2291177 : Blo 1526460 2291177 := bstep (se 2 (by rfl) ⟨859191, by rfl⟩ : syracuseStep 2291177 = 1718383) B1718383
theorem B2291369 : Blo 1526460 2291369 := bstep (se 2 (by rfl) ⟨859263, by rfl⟩ : syracuseStep 2291369 = 1718527) B1718527
theorem B5502745 : Blo 1526460 5502745 := bstep (se 2 (by rfl) ⟨2063529, by rfl⟩ : syracuseStep 5502745 = 4127059) B4127059
theorem B2291567 : Blo 1526460 2291567 := bstep (se 1 (by rfl) ⟨1718675, by rfl⟩ : syracuseStep 2291567 = 3437351) B3437351
theorem B2578331 : Blo 1526460 2578331 := bstep (se 1 (by rfl) ⟨1933748, by rfl⟩ : syracuseStep 2578331 = 3867497) B3867497
theorem B17389565 : Blo 1526460 17389565 := bstep (se 3 (by rfl) ⟨3260543, by rfl⟩ : syracuseStep 17389565 = 6521087) B6521087
theorem B8255591 : Blo 1526460 8255591 := bstep (se 1 (by rfl) ⟨6191693, by rfl⟩ : syracuseStep 8255591 = 12383387) B12383387
theorem B7338205 : Blo 1526460 7338205 := bstep (se 3 (by rfl) ⟨1375913, by rfl⟩ : syracuseStep 7338205 = 2751827) B2751827
theorem B2291963 : Blo 1526460 2291963 := bstep (se 1 (by rfl) ⟨1718972, by rfl⟩ : syracuseStep 2291963 = 3437945) B3437945
theorem B2292047 : Blo 1526460 2292047 := bstep (se 1 (by rfl) ⟨1719035, by rfl⟩ : syracuseStep 2292047 = 3438071) B3438071
theorem B132151661 : Blo 1526460 132151661 := bstep (se 3 (by rfl) ⟨24778436, by rfl⟩ : syracuseStep 132151661 = 49556873) B49556873
theorem B2292095 : Blo 1526460 2292095 := bstep (se 1 (by rfl) ⟨1719071, by rfl⟩ : syracuseStep 2292095 = 3438143) B3438143
theorem B2063227 : Blo 1526460 2063227 := bstep (se 1 (by rfl) ⟨1547420, by rfl⟩ : syracuseStep 2063227 = 3094841) B3094841
theorem B19586225 : Blo 1526460 19586225 := bstep (se 2 (by rfl) ⟨7344834, by rfl⟩ : syracuseStep 19586225 = 14689669) B14689669
theorem B1630255 : Blo 1526460 1630255 := bstep (se 1 (by rfl) ⟨1222691, by rfl⟩ : syracuseStep 1630255 = 2445383) B2445383
theorem B104546551 : Blo 1526460 104546551 := bstep (se 1 (by rfl) ⟨78409913, by rfl⟩ : syracuseStep 104546551 = 156819827) B156819827
theorem B4645279 : Blo 1526460 4645279 := bstep (se 1 (by rfl) ⟨3483959, by rfl⟩ : syracuseStep 4645279 = 6967919) B6967919
theorem B18580715 : Blo 1526460 18580715 := bstep (se 1 (by rfl) ⟨13935536, by rfl⟩ : syracuseStep 18580715 = 27871073) B27871073
theorem B11593043 : Blo 1526460 11593043 := bstep (se 1 (by rfl) ⟨8694782, by rfl⟩ : syracuseStep 11593043 = 17389565) B17389565
theorem B33048647 : Blo 1526460 33048647 := bstep (se 1 (by rfl) ⟨24786485, by rfl⟩ : syracuseStep 33048647 = 49572971) B49572971
theorem B25111255 : Blo 1526460 25111255 := bstep (se 1 (by rfl) ⟨18833441, by rfl⟩ : syracuseStep 25111255 = 37666883) B37666883
theorem B1526511 : Blo 1526460 1526511 := bstep (se 1 (by rfl) ⟨1144883, by rfl⟩ : syracuseStep 1526511 = 2289767) B2289767
theorem B12380915 : Blo 1526460 12380915 := bstep (se 1 (by rfl) ⟨9285686, by rfl⟩ : syracuseStep 12380915 = 18571373) B18571373
theorem B5802749 : Blo 1526460 5802749 := bstep (se 3 (by rfl) ⟨1088015, by rfl⟩ : syracuseStep 5802749 = 2176031) B2176031
theorem B9784273 : Blo 1526460 9784273 := bstep (se 2 (by rfl) ⟨3669102, by rfl⟩ : syracuseStep 9784273 = 7338205) B7338205
theorem B1526887 : Blo 1526460 1526887 := bstep (se 1 (by rfl) ⟨1145165, by rfl⟩ : syracuseStep 1526887 = 2290331) B2290331
theorem B1526943 : Blo 1526460 1526943 := bstep (se 1 (by rfl) ⟨1145207, by rfl⟩ : syracuseStep 1526943 = 2290415) B2290415
theorem B1527143 : Blo 1526460 1527143 := bstep (se 1 (by rfl) ⟨1145357, by rfl⟩ : syracuseStep 1527143 = 2290715) B2290715
theorem B7736957 : Blo 1526460 7736957 := bstep (se 3 (by rfl) ⟨1450679, by rfl⟩ : syracuseStep 7736957 = 2901359) B2901359
theorem B1527451 : Blo 1526460 1527451 := bstep (se 1 (by rfl) ⟨1145588, by rfl⟩ : syracuseStep 1527451 = 2291177) B2291177
theorem B3436199 : Blo 1526460 3436199 := bstep (se 1 (by rfl) ⟨2577149, by rfl⟩ : syracuseStep 3436199 = 5154299) B5154299
theorem B1527579 : Blo 1526460 1527579 := bstep (se 1 (by rfl) ⟨1145684, by rfl⟩ : syracuseStep 1527579 = 2291369) B2291369
theorem B3436379 : Blo 1526460 3436379 := bstep (se 1 (by rfl) ⟨2577284, by rfl⟩ : syracuseStep 3436379 = 5154569) B5154569
theorem B1527711 : Blo 1526460 1527711 := bstep (se 1 (by rfl) ⟨1145783, by rfl⟩ : syracuseStep 1527711 = 2291567) B2291567
theorem B3436487 : Blo 1526460 3436487 := bstep (se 1 (by rfl) ⟨2577365, by rfl⟩ : syracuseStep 3436487 = 5154731) B5154731
theorem B1527975 : Blo 1526460 1527975 := bstep (se 1 (by rfl) ⟨1145981, by rfl⟩ : syracuseStep 1527975 = 2291963) B2291963
theorem B1528031 : Blo 1526460 1528031 := bstep (se 1 (by rfl) ⟨1146023, by rfl⟩ : syracuseStep 1528031 = 2292047) B2292047
theorem B88101107 : Blo 1526460 88101107 := bstep (se 1 (by rfl) ⟨66075830, by rfl⟩ : syracuseStep 88101107 = 132151661) B132151661
theorem B1528063 : Blo 1526460 1528063 := bstep (se 1 (by rfl) ⟨1146047, by rfl⟩ : syracuseStep 1528063 = 2292095) B2292095
theorem B2290079 : Blo 1526460 2290079 := bstep (se 1 (by rfl) ⟨1717559, by rfl⟩ : syracuseStep 2290079 = 3435119) B3435119
theorem B24769097 : Blo 1526460 24769097 := bstep (se 2 (by rfl) ⟨9288411, by rfl⟩ : syracuseStep 24769097 = 18576823) B18576823
theorem B3437243 : Blo 1526460 3437243 := bstep (se 1 (by rfl) ⟨2577932, by rfl⟩ : syracuseStep 3437243 = 5155865) B5155865
theorem B2290367 : Blo 1526460 2290367 := bstep (se 1 (by rfl) ⟨1717775, by rfl⟩ : syracuseStep 2290367 = 3435551) B3435551
theorem B7336993 : Blo 1526460 7336993 := bstep (se 2 (by rfl) ⟨2751372, by rfl⟩ : syracuseStep 7336993 = 5502745) B5502745
theorem B28243055 : Blo 1526460 28243055 := bstep (se 1 (by rfl) ⟨21182291, by rfl⟩ : syracuseStep 28243055 = 42364583) B42364583
theorem B5158079 : Blo 1526460 5158079 := bstep (se 1 (by rfl) ⟨3868559, by rfl⟩ : syracuseStep 5158079 = 7737119) B7737119
theorem B19567979 : Blo 1526460 19567979 := bstep (se 1 (by rfl) ⟨14675984, by rfl⟩ : syracuseStep 19567979 = 29351969) B29351969
theorem B1717663 : Blo 1526460 1717663 := bstep (se 1 (by rfl) ⟨1288247, by rfl⟩ : syracuseStep 1717663 = 2576495) B2576495
theorem B94033345 : Blo 1526460 94033345 := bstep (se 2 (by rfl) ⟨35262504, by rfl⟩ : syracuseStep 94033345 = 70525009) B70525009
theorem B2291195 : Blo 1526460 2291195 := bstep (se 1 (by rfl) ⟨1718396, by rfl⟩ : syracuseStep 2291195 = 3436793) B3436793
theorem B2447113 : Blo 1526460 2447113 := bstep (se 2 (by rfl) ⟨917667, by rfl⟩ : syracuseStep 2447113 = 1835335) B1835335
theorem B2578601 : Blo 1526460 2578601 := bstep (se 2 (by rfl) ⟨966975, by rfl⟩ : syracuseStep 2578601 = 1933951) B1933951
theorem B29743321 : Blo 1526460 29743321 := bstep (se 2 (by rfl) ⟨11153745, by rfl⟩ : syracuseStep 29743321 = 22307491) B22307491
theorem B2750969 : Blo 1526460 2750969 := bstep (se 2 (by rfl) ⟨1031613, by rfl⟩ : syracuseStep 2750969 = 2063227) B2063227
theorem B1718887 : Blo 1526460 1718887 := bstep (se 1 (by rfl) ⟨1289165, by rfl⟩ : syracuseStep 1718887 = 2578331) B2578331
theorem B5503727 : Blo 1526460 5503727 := bstep (se 1 (by rfl) ⟨4127795, by rfl⟩ : syracuseStep 5503727 = 8255591) B8255591
theorem B6527785 : Blo 1526460 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B13057483 : Blo 1526460 13057483 := bstep (se 1 (by rfl) ⟨9793112, by rfl⟩ : syracuseStep 13057483 = 19586225) B19586225
theorem B39657761 : Blo 1526460 39657761 := bstep (se 2 (by rfl) ⟨14871660, by rfl⟩ : syracuseStep 39657761 = 29743321) B29743321
theorem B139395401 : Blo 1526460 139395401 := bstep (se 2 (by rfl) ⟨52273275, by rfl⟩ : syracuseStep 139395401 = 104546551) B104546551
theorem B6193705 : Blo 1526460 6193705 := bstep (se 2 (by rfl) ⟨2322639, by rfl⟩ : syracuseStep 6193705 = 4645279) B4645279
theorem B12387143 : Blo 1526460 12387143 := bstep (se 1 (by rfl) ⟨9290357, by rfl⟩ : syracuseStep 12387143 = 18580715) B18580715
theorem B33481673 : Blo 1526460 33481673 := bstep (se 2 (by rfl) ⟨12555627, by rfl⟩ : syracuseStep 33481673 = 25111255) B25111255
theorem B9782657 : Blo 1526460 9782657 := bstep (se 2 (by rfl) ⟨3668496, by rfl⟩ : syracuseStep 9782657 = 7336993) B7336993
theorem B3868499 : Blo 1526460 3868499 := bstep (se 1 (by rfl) ⟨2901374, by rfl⟩ : syracuseStep 3868499 = 5802749) B5802749
theorem B17409977 : Blo 1526460 17409977 := bstep (se 2 (by rfl) ⟨6528741, by rfl⟩ : syracuseStep 17409977 = 13057483) B13057483
theorem B3262817 : Blo 1526460 3262817 := bstep (se 2 (by rfl) ⟨1223556, by rfl⟩ : syracuseStep 3262817 = 2447113) B2447113
theorem B2173673 : Blo 1526460 2173673 := bstep (se 2 (by rfl) ⟨815127, by rfl⟩ : syracuseStep 2173673 = 1630255) B1630255
theorem B1526719 : Blo 1526460 1526719 := bstep (se 1 (by rfl) ⟨1145039, by rfl⟩ : syracuseStep 1526719 = 2290079) B2290079
theorem B1526911 : Blo 1526460 1526911 := bstep (se 1 (by rfl) ⟨1145183, by rfl⟩ : syracuseStep 1526911 = 2290367) B2290367
theorem B18828703 : Blo 1526460 18828703 := bstep (se 1 (by rfl) ⟨14121527, by rfl⟩ : syracuseStep 18828703 = 28243055) B28243055
theorem B7728695 : Blo 1526460 7728695 := bstep (se 1 (by rfl) ⟨5796521, by rfl⟩ : syracuseStep 7728695 = 11593043) B11593043
theorem B13045319 : Blo 1526460 13045319 := bstep (se 1 (by rfl) ⟨9783989, by rfl⟩ : syracuseStep 13045319 = 19567979) B19567979
theorem B1527463 : Blo 1526460 1527463 := bstep (se 1 (by rfl) ⟨1145597, by rfl⟩ : syracuseStep 1527463 = 2291195) B2291195
theorem B8703713 : Blo 1526460 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B13045697 : Blo 1526460 13045697 := bstep (se 2 (by rfl) ⟨4892136, by rfl⟩ : syracuseStep 13045697 = 9784273) B9784273
theorem B7335917 : Blo 1526460 7335917 := bstep (se 3 (by rfl) ⟨1375484, by rfl⟩ : syracuseStep 7335917 = 2750969) B2750969
theorem B22032431 : Blo 1526460 22032431 := bstep (se 1 (by rfl) ⟨16524323, by rfl⟩ : syracuseStep 22032431 = 33048647) B33048647
theorem B8253943 : Blo 1526460 8253943 := bstep (se 1 (by rfl) ⟨6190457, by rfl⟩ : syracuseStep 8253943 = 12380915) B12380915
theorem B2290217 : Blo 1526460 2290217 := bstep (se 2 (by rfl) ⟨858831, by rfl⟩ : syracuseStep 2290217 = 1717663) B1717663
theorem B5157971 : Blo 1526460 5157971 := bstep (se 1 (by rfl) ⟨3868478, by rfl⟩ : syracuseStep 5157971 = 7736957) B7736957
theorem B2290799 : Blo 1526460 2290799 := bstep (se 1 (by rfl) ⟨1718099, by rfl⟩ : syracuseStep 2290799 = 3436199) B3436199
theorem B2290919 : Blo 1526460 2290919 := bstep (se 1 (by rfl) ⟨1718189, by rfl⟩ : syracuseStep 2290919 = 3436379) B3436379
theorem B2290991 : Blo 1526460 2290991 := bstep (se 1 (by rfl) ⟨1718243, by rfl⟩ : syracuseStep 2290991 = 3436487) B3436487
theorem B58734071 : Blo 1526460 58734071 := bstep (se 1 (by rfl) ⟨44050553, by rfl⟩ : syracuseStep 58734071 = 88101107) B88101107
theorem B16512731 : Blo 1526460 16512731 := bstep (se 1 (by rfl) ⟨12384548, by rfl⟩ : syracuseStep 16512731 = 24769097) B24769097
theorem B2291495 : Blo 1526460 2291495 := bstep (se 1 (by rfl) ⟨1718621, by rfl⟩ : syracuseStep 2291495 = 3437243) B3437243
theorem B3438719 : Blo 1526460 3438719 := bstep (se 1 (by rfl) ⟨2579039, by rfl⟩ : syracuseStep 3438719 = 5158079) B5158079
theorem B2291849 : Blo 1526460 2291849 := bstep (se 2 (by rfl) ⟨859443, by rfl⟩ : syracuseStep 2291849 = 1718887) B1718887
theorem B1719067 : Blo 1526460 1719067 := bstep (se 1 (by rfl) ⟨1289300, by rfl⟩ : syracuseStep 1719067 = 2578601) B2578601
theorem B3669151 : Blo 1526460 3669151 := bstep (se 1 (by rfl) ⟨2751863, by rfl⟩ : syracuseStep 3669151 = 5503727) B5503727
theorem B125377793 : Blo 1526460 125377793 := bstep (se 2 (by rfl) ⟨47016672, by rfl⟩ : syracuseStep 125377793 = 94033345) B94033345
theorem B14688287 : Blo 1526460 14688287 := bstep (se 1 (by rfl) ⟨11016215, by rfl⟩ : syracuseStep 14688287 = 22032431) B22032431
theorem B92930267 : Blo 1526460 92930267 := bstep (se 1 (by rfl) ⟨69697700, by rfl⟩ : syracuseStep 92930267 = 139395401) B139395401
theorem B8258095 : Blo 1526460 8258095 := bstep (se 1 (by rfl) ⟨6193571, by rfl⟩ : syracuseStep 8258095 = 12387143) B12387143
theorem B8258273 : Blo 1526460 8258273 := bstep (se 2 (by rfl) ⟨3096852, by rfl⟩ : syracuseStep 8258273 = 6193705) B6193705
theorem B6521771 : Blo 1526460 6521771 := bstep (se 1 (by rfl) ⟨4891328, by rfl⟩ : syracuseStep 6521771 = 9782657) B9782657
theorem B4892201 : Blo 1526460 4892201 := bstep (se 2 (by rfl) ⟨1834575, by rfl⟩ : syracuseStep 4892201 = 3669151) B3669151
theorem B100419749 : Blo 1526460 100419749 := bstep (se 4 (by rfl) ⟨9414351, by rfl⟩ : syracuseStep 100419749 = 18828703) B18828703
theorem B83585195 : Blo 1526460 83585195 := bstep (se 1 (by rfl) ⟨62688896, by rfl⟩ : syracuseStep 83585195 = 125377793) B125377793
theorem B5802475 : Blo 1526460 5802475 := bstep (se 1 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 5802475 = 8703713) B8703713
theorem B26438507 : Blo 1526460 26438507 := bstep (se 1 (by rfl) ⟨19828880, by rfl⟩ : syracuseStep 26438507 = 39657761) B39657761
theorem B1526811 : Blo 1526460 1526811 := bstep (se 1 (by rfl) ⟨1145108, by rfl⟩ : syracuseStep 1526811 = 2290217) B2290217
theorem B1527199 : Blo 1526460 1527199 := bstep (se 1 (by rfl) ⟨1145399, by rfl⟩ : syracuseStep 1527199 = 2290799) B2290799
theorem B1527279 : Blo 1526460 1527279 := bstep (se 1 (by rfl) ⟨1145459, by rfl⟩ : syracuseStep 1527279 = 2290919) B2290919
theorem B1527327 : Blo 1526460 1527327 := bstep (se 1 (by rfl) ⟨1145495, by rfl⟩ : syracuseStep 1527327 = 2290991) B2290991
theorem B1527663 : Blo 1526460 1527663 := bstep (se 1 (by rfl) ⟨1145747, by rfl⟩ : syracuseStep 1527663 = 2291495) B2291495
theorem B1527899 : Blo 1526460 1527899 := bstep (se 1 (by rfl) ⟨1145924, by rfl⟩ : syracuseStep 1527899 = 2291849) B2291849
theorem B2175211 : Blo 1526460 2175211 := bstep (se 1 (by rfl) ⟨1631408, by rfl⟩ : syracuseStep 2175211 = 3262817) B3262817
theorem B5796461 : Blo 1526460 5796461 := bstep (se 3 (by rfl) ⟨1086836, by rfl⟩ : syracuseStep 5796461 = 2173673) B2173673
theorem B8696879 : Blo 1526460 8696879 := bstep (se 1 (by rfl) ⟨6522659, by rfl⟩ : syracuseStep 8696879 = 13045319) B13045319
theorem B44021029 : Blo 1526460 44021029 := bstep (se 4 (by rfl) ⟨4126971, by rfl⟩ : syracuseStep 44021029 = 8253943) B8253943
theorem B8697131 : Blo 1526460 8697131 := bstep (se 1 (by rfl) ⟨6522848, by rfl⟩ : syracuseStep 8697131 = 13045697) B13045697
theorem B22321115 : Blo 1526460 22321115 := bstep (se 1 (by rfl) ⟨16740836, by rfl⟩ : syracuseStep 22321115 = 33481673) B33481673
theorem B3438647 : Blo 1526460 3438647 := bstep (se 1 (by rfl) ⟨2578985, by rfl⟩ : syracuseStep 3438647 = 5157971) B5157971
theorem B39156047 : Blo 1526460 39156047 := bstep (se 1 (by rfl) ⟨29367035, by rfl⟩ : syracuseStep 39156047 = 58734071) B58734071
theorem B2292089 : Blo 1526460 2292089 := bstep (se 2 (by rfl) ⟨859533, by rfl⟩ : syracuseStep 2292089 = 1719067) B1719067
theorem B11008487 : Blo 1526460 11008487 := bstep (se 1 (by rfl) ⟨8256365, by rfl⟩ : syracuseStep 11008487 = 16512731) B16512731
theorem B2578999 : Blo 1526460 2578999 := bstep (se 1 (by rfl) ⟨1934249, by rfl⟩ : syracuseStep 2578999 = 3868499) B3868499
theorem B11606651 : Blo 1526460 11606651 := bstep (se 1 (by rfl) ⟨8704988, by rfl⟩ : syracuseStep 11606651 = 17409977) B17409977
theorem B2292479 : Blo 1526460 2292479 := bstep (se 1 (by rfl) ⟨1719359, by rfl⟩ : syracuseStep 2292479 = 3438719) B3438719
theorem B5152463 : Blo 1526460 5152463 := bstep (se 1 (by rfl) ⟨3864347, by rfl⟩ : syracuseStep 5152463 = 7728695) B7728695
theorem B4890611 : Blo 1526460 4890611 := bstep (se 1 (by rfl) ⟨3667958, by rfl⟩ : syracuseStep 4890611 = 7335917) B7335917
theorem B2900281 : Blo 1526460 2900281 := bstep (se 2 (by rfl) ⟨1087605, by rfl⟩ : syracuseStep 2900281 = 2175211) B2175211
theorem B5505515 : Blo 1526460 5505515 := bstep (se 1 (by rfl) ⟨4129136, by rfl⟩ : syracuseStep 5505515 = 8258273) B8258273
theorem B3261467 : Blo 1526460 3261467 := bstep (se 1 (by rfl) ⟨2446100, by rfl⟩ : syracuseStep 3261467 = 4892201) B4892201
theorem B66946499 : Blo 1526460 66946499 := bstep (se 1 (by rfl) ⟨50209874, by rfl⟩ : syracuseStep 66946499 = 100419749) B100419749
theorem B55723463 : Blo 1526460 55723463 := bstep (se 1 (by rfl) ⟨41792597, by rfl⟩ : syracuseStep 55723463 = 83585195) B83585195
theorem B3434975 : Blo 1526460 3434975 := bstep (se 1 (by rfl) ⟨2576231, by rfl⟩ : syracuseStep 3434975 = 5152463) B5152463
theorem B9792191 : Blo 1526460 9792191 := bstep (se 1 (by rfl) ⟨7344143, by rfl⟩ : syracuseStep 9792191 = 14688287) B14688287
theorem B44043173 : Blo 1526460 44043173 := bstep (se 4 (by rfl) ⟨4129047, by rfl⟩ : syracuseStep 44043173 = 8258095) B8258095
theorem B7736633 : Blo 1526460 7736633 := bstep (se 2 (by rfl) ⟨2901237, by rfl⟩ : syracuseStep 7736633 = 5802475) B5802475
theorem B29355965 : Blo 1526460 29355965 := bstep (se 3 (by rfl) ⟨5504243, by rfl⟩ : syracuseStep 29355965 = 11008487) B11008487
theorem B14880743 : Blo 1526460 14880743 := bstep (se 1 (by rfl) ⟨11160557, by rfl⟩ : syracuseStep 14880743 = 22321115) B22321115
theorem B26104031 : Blo 1526460 26104031 := bstep (se 1 (by rfl) ⟨19578023, by rfl⟩ : syracuseStep 26104031 = 39156047) B39156047
theorem B1528059 : Blo 1526460 1528059 := bstep (se 1 (by rfl) ⟨1146044, by rfl⟩ : syracuseStep 1528059 = 2292089) B2292089
theorem B7737767 : Blo 1526460 7737767 := bstep (se 1 (by rfl) ⟨5803325, by rfl⟩ : syracuseStep 7737767 = 11606651) B11606651
theorem B1528319 : Blo 1526460 1528319 := bstep (se 1 (by rfl) ⟨1146239, by rfl⟩ : syracuseStep 1528319 = 2292479) B2292479
theorem B17625671 : Blo 1526460 17625671 := bstep (se 1 (by rfl) ⟨13219253, by rfl⟩ : syracuseStep 17625671 = 26438507) B26438507
theorem B61953511 : Blo 1526460 61953511 := bstep (se 1 (by rfl) ⟨46465133, by rfl⟩ : syracuseStep 61953511 = 92930267) B92930267
theorem B3864307 : Blo 1526460 3864307 := bstep (se 1 (by rfl) ⟨2898230, by rfl⟩ : syracuseStep 3864307 = 5796461) B5796461
theorem B4347847 : Blo 1526460 4347847 := bstep (se 1 (by rfl) ⟨3260885, by rfl⟩ : syracuseStep 4347847 = 6521771) B6521771
theorem B5797919 : Blo 1526460 5797919 := bstep (se 1 (by rfl) ⟨4348439, by rfl⟩ : syracuseStep 5797919 = 8696879) B8696879
theorem B3438665 : Blo 1526460 3438665 := bstep (se 2 (by rfl) ⟨1289499, by rfl⟩ : syracuseStep 3438665 = 2578999) B2578999
theorem B5798087 : Blo 1526460 5798087 := bstep (se 1 (by rfl) ⟨4348565, by rfl⟩ : syracuseStep 5798087 = 8697131) B8697131
theorem B2292431 : Blo 1526460 2292431 := bstep (se 1 (by rfl) ⟨1719323, by rfl⟩ : syracuseStep 2292431 = 3438647) B3438647
theorem B58694705 : Blo 1526460 58694705 := bstep (se 2 (by rfl) ⟨22010514, by rfl⟩ : syracuseStep 58694705 = 44021029) B44021029
theorem B3260407 : Blo 1526460 3260407 := bstep (se 1 (by rfl) ⟨2445305, by rfl⟩ : syracuseStep 3260407 = 4890611) B4890611
theorem B3670343 : Blo 1526460 3670343 := bstep (se 1 (by rfl) ⟨2752757, by rfl⟩ : syracuseStep 3670343 = 5505515) B5505515
theorem B3867041 : Blo 1526460 3867041 := bstep (se 2 (by rfl) ⟨1450140, by rfl⟩ : syracuseStep 3867041 = 2900281) B2900281
theorem B44630999 : Blo 1526460 44630999 := bstep (se 1 (by rfl) ⟨33473249, by rfl⟩ : syracuseStep 44630999 = 66946499) B66946499
theorem B29362115 : Blo 1526460 29362115 := bstep (se 1 (by rfl) ⟨22021586, by rfl⟩ : syracuseStep 29362115 = 44043173) B44043173
theorem B17402687 : Blo 1526460 17402687 := bstep (se 1 (by rfl) ⟨13052015, by rfl⟩ : syracuseStep 17402687 = 26104031) B26104031
theorem B11750447 : Blo 1526460 11750447 := bstep (se 1 (by rfl) ⟨8812835, by rfl⟩ : syracuseStep 11750447 = 17625671) B17625671
theorem B2174311 : Blo 1526460 2174311 := bstep (se 1 (by rfl) ⟨1630733, by rfl⟩ : syracuseStep 2174311 = 3261467) B3261467
theorem B2289983 : Blo 1526460 2289983 := bstep (se 1 (by rfl) ⟨1717487, by rfl⟩ : syracuseStep 2289983 = 3434975) B3434975
theorem B1528287 : Blo 1526460 1528287 := bstep (se 1 (by rfl) ⟨1146215, by rfl⟩ : syracuseStep 1528287 = 2292431) B2292431
theorem B82604681 : Blo 1526460 82604681 := bstep (se 2 (by rfl) ⟨30976755, by rfl⟩ : syracuseStep 82604681 = 61953511) B61953511
theorem B39129803 : Blo 1526460 39129803 := bstep (se 1 (by rfl) ⟨29347352, by rfl⟩ : syracuseStep 39129803 = 58694705) B58694705
theorem B5157755 : Blo 1526460 5157755 := bstep (se 1 (by rfl) ⟨3868316, by rfl⟩ : syracuseStep 5157755 = 7736633) B7736633
theorem B5797129 : Blo 1526460 5797129 := bstep (se 2 (by rfl) ⟨2173923, by rfl⟩ : syracuseStep 5797129 = 4347847) B4347847
theorem B4347209 : Blo 1526460 4347209 := bstep (se 2 (by rfl) ⟨1630203, by rfl⟩ : syracuseStep 4347209 = 3260407) B3260407
theorem B5158511 : Blo 1526460 5158511 := bstep (se 1 (by rfl) ⟨3868883, by rfl⟩ : syracuseStep 5158511 = 7737767) B7737767
theorem B37148975 : Blo 1526460 37148975 := bstep (se 1 (by rfl) ⟨27861731, by rfl⟩ : syracuseStep 37148975 = 55723463) B55723463
theorem B3865279 : Blo 1526460 3865279 := bstep (se 1 (by rfl) ⟨2898959, by rfl⟩ : syracuseStep 3865279 = 5797919) B5797919
theorem B2292443 : Blo 1526460 2292443 := bstep (se 1 (by rfl) ⟨1719332, by rfl⟩ : syracuseStep 2292443 = 3438665) B3438665
theorem B3865391 : Blo 1526460 3865391 := bstep (se 1 (by rfl) ⟨2899043, by rfl⟩ : syracuseStep 3865391 = 5798087) B5798087
theorem B6528127 : Blo 1526460 6528127 := bstep (se 1 (by rfl) ⟨4896095, by rfl⟩ : syracuseStep 6528127 = 9792191) B9792191
theorem B5152409 : Blo 1526460 5152409 := bstep (se 2 (by rfl) ⟨1932153, by rfl⟩ : syracuseStep 5152409 = 3864307) B3864307
theorem B19570643 : Blo 1526460 19570643 := bstep (se 1 (by rfl) ⟨14677982, by rfl⟩ : syracuseStep 19570643 = 29355965) B29355965
theorem B9920495 : Blo 1526460 9920495 := bstep (se 1 (by rfl) ⟨7440371, by rfl⟩ : syracuseStep 9920495 = 14880743) B14880743
theorem B31334525 : Blo 1526460 31334525 := bstep (se 3 (by rfl) ⟨5875223, by rfl⟩ : syracuseStep 31334525 = 11750447) B11750447
theorem B29753999 : Blo 1526460 29753999 := bstep (se 1 (by rfl) ⟨22315499, by rfl⟩ : syracuseStep 29753999 = 44630999) B44630999
theorem B11592557 : Blo 1526460 11592557 := bstep (se 3 (by rfl) ⟨2173604, by rfl⟩ : syracuseStep 11592557 = 4347209) B4347209
theorem B5153705 : Blo 1526460 5153705 := bstep (se 2 (by rfl) ⟨1932639, by rfl⟩ : syracuseStep 5153705 = 3865279) B3865279
theorem B24765983 : Blo 1526460 24765983 := bstep (se 1 (by rfl) ⟨18574487, by rfl⟩ : syracuseStep 24765983 = 37148975) B37148975
theorem B11601791 : Blo 1526460 11601791 := bstep (se 1 (by rfl) ⟨8701343, by rfl⟩ : syracuseStep 11601791 = 17402687) B17402687
theorem B3434939 : Blo 1526460 3434939 := bstep (se 1 (by rfl) ⟨2576204, by rfl⟩ : syracuseStep 3434939 = 5152409) B5152409
theorem B6613663 : Blo 1526460 6613663 := bstep (se 1 (by rfl) ⟨4960247, by rfl⟩ : syracuseStep 6613663 = 9920495) B9920495
theorem B1526655 : Blo 1526460 1526655 := bstep (se 1 (by rfl) ⟨1144991, by rfl⟩ : syracuseStep 1526655 = 2289983) B2289983
theorem B55069787 : Blo 1526460 55069787 := bstep (se 1 (by rfl) ⟨41302340, by rfl⟩ : syracuseStep 55069787 = 82604681) B82604681
theorem B26086535 : Blo 1526460 26086535 := bstep (se 1 (by rfl) ⟨19564901, by rfl⟩ : syracuseStep 26086535 = 39129803) B39129803
theorem B19574743 : Blo 1526460 19574743 := bstep (se 1 (by rfl) ⟨14681057, by rfl⟩ : syracuseStep 19574743 = 29362115) B29362115
theorem B8704169 : Blo 1526460 8704169 := bstep (se 2 (by rfl) ⟨3264063, by rfl⟩ : syracuseStep 8704169 = 6528127) B6528127
theorem B7729505 : Blo 1526460 7729505 := bstep (se 2 (by rfl) ⟨2898564, by rfl⟩ : syracuseStep 7729505 = 5797129) B5797129
theorem B1528295 : Blo 1526460 1528295 := bstep (se 1 (by rfl) ⟨1146221, by rfl⟩ : syracuseStep 1528295 = 2292443) B2292443
theorem B2576927 : Blo 1526460 2576927 := bstep (se 1 (by rfl) ⟨1932695, by rfl⟩ : syracuseStep 2576927 = 3865391) B3865391
theorem B13047095 : Blo 1526460 13047095 := bstep (se 1 (by rfl) ⟨9785321, by rfl⟩ : syracuseStep 13047095 = 19570643) B19570643
theorem B2446895 : Blo 1526460 2446895 := bstep (se 1 (by rfl) ⟨1835171, by rfl⟩ : syracuseStep 2446895 = 3670343) B3670343
theorem B2578027 : Blo 1526460 2578027 := bstep (se 1 (by rfl) ⟨1933520, by rfl⟩ : syracuseStep 2578027 = 3867041) B3867041
theorem B3438503 : Blo 1526460 3438503 := bstep (se 1 (by rfl) ⟨2578877, by rfl⟩ : syracuseStep 3438503 = 5157755) B5157755
theorem B3439007 : Blo 1526460 3439007 := bstep (se 1 (by rfl) ⟨2579255, by rfl⟩ : syracuseStep 3439007 = 5158511) B5158511
theorem B2899081 : Blo 1526460 2899081 := bstep (se 2 (by rfl) ⟨1087155, by rfl⟩ : syracuseStep 2899081 = 2174311) B2174311
theorem B20889683 : Blo 1526460 20889683 := bstep (se 1 (by rfl) ⟨15667262, by rfl⟩ : syracuseStep 20889683 = 31334525) B31334525
theorem B5153003 : Blo 1526460 5153003 := bstep (se 1 (by rfl) ⟨3864752, by rfl⟩ : syracuseStep 5153003 = 7729505) B7729505
theorem B1631263 : Blo 1526460 1631263 := bstep (se 1 (by rfl) ⟨1223447, by rfl⟩ : syracuseStep 1631263 = 2446895) B2446895
theorem B7734527 : Blo 1526460 7734527 := bstep (se 1 (by rfl) ⟨5800895, by rfl⟩ : syracuseStep 7734527 = 11601791) B11601791
theorem B5802779 : Blo 1526460 5802779 := bstep (se 1 (by rfl) ⟨4352084, by rfl⟩ : syracuseStep 5802779 = 8704169) B8704169
theorem B19835999 : Blo 1526460 19835999 := bstep (se 1 (by rfl) ⟨14876999, by rfl⟩ : syracuseStep 19835999 = 29753999) B29753999
theorem B7728371 : Blo 1526460 7728371 := bstep (se 1 (by rfl) ⟨5796278, by rfl⟩ : syracuseStep 7728371 = 11592557) B11592557
theorem B3435803 : Blo 1526460 3435803 := bstep (se 1 (by rfl) ⟨2576852, by rfl⟩ : syracuseStep 3435803 = 5153705) B5153705
theorem B8818217 : Blo 1526460 8818217 := bstep (se 2 (by rfl) ⟨3306831, by rfl⟩ : syracuseStep 8818217 = 6613663) B6613663
theorem B16510655 : Blo 1526460 16510655 := bstep (se 1 (by rfl) ⟨12382991, by rfl⟩ : syracuseStep 16510655 = 24765983) B24765983
theorem B2289959 : Blo 1526460 2289959 := bstep (se 1 (by rfl) ⟨1717469, by rfl⟩ : syracuseStep 2289959 = 3434939) B3434939
theorem B36713191 : Blo 1526460 36713191 := bstep (se 1 (by rfl) ⟨27534893, by rfl⟩ : syracuseStep 36713191 = 55069787) B55069787
theorem B3437369 : Blo 1526460 3437369 := bstep (se 2 (by rfl) ⟨1289013, by rfl⟩ : syracuseStep 3437369 = 2578027) B2578027
theorem B1717951 : Blo 1526460 1717951 := bstep (se 1 (by rfl) ⟨1288463, by rfl⟩ : syracuseStep 1717951 = 2576927) B2576927
theorem B8698063 : Blo 1526460 8698063 := bstep (se 1 (by rfl) ⟨6523547, by rfl⟩ : syracuseStep 8698063 = 13047095) B13047095
theorem B2292335 : Blo 1526460 2292335 := bstep (se 1 (by rfl) ⟨1719251, by rfl⟩ : syracuseStep 2292335 = 3438503) B3438503
theorem B3865441 : Blo 1526460 3865441 := bstep (se 2 (by rfl) ⟨1449540, by rfl⟩ : syracuseStep 3865441 = 2899081) B2899081
theorem B2292671 : Blo 1526460 2292671 := bstep (se 1 (by rfl) ⟨1719503, by rfl⟩ : syracuseStep 2292671 = 3439007) B3439007
theorem B17391023 : Blo 1526460 17391023 := bstep (se 1 (by rfl) ⟨13043267, by rfl⟩ : syracuseStep 17391023 = 26086535) B26086535
theorem B26099657 : Blo 1526460 26099657 := bstep (se 2 (by rfl) ⟨9787371, by rfl⟩ : syracuseStep 26099657 = 19574743) B19574743
theorem B13926455 : Blo 1526460 13926455 := bstep (se 1 (by rfl) ⟨10444841, by rfl⟩ : syracuseStep 13926455 = 20889683) B20889683
theorem B5153921 : Blo 1526460 5153921 := bstep (se 2 (by rfl) ⟨1932720, by rfl⟩ : syracuseStep 5153921 = 3865441) B3865441
theorem B3868519 : Blo 1526460 3868519 := bstep (se 1 (by rfl) ⟨2901389, by rfl⟩ : syracuseStep 3868519 = 5802779) B5802779
theorem B13223999 : Blo 1526460 13223999 := bstep (se 1 (by rfl) ⟨9917999, by rfl⟩ : syracuseStep 13223999 = 19835999) B19835999
theorem B11594015 : Blo 1526460 11594015 := bstep (se 1 (by rfl) ⟨8695511, by rfl⟩ : syracuseStep 11594015 = 17391023) B17391023
theorem B3435335 : Blo 1526460 3435335 := bstep (se 1 (by rfl) ⟨2576501, by rfl⟩ : syracuseStep 3435335 = 5153003) B5153003
theorem B1526639 : Blo 1526460 1526639 := bstep (se 1 (by rfl) ⟨1144979, by rfl⟩ : syracuseStep 1526639 = 2289959) B2289959
theorem B5156351 : Blo 1526460 5156351 := bstep (se 1 (by rfl) ⟨3867263, by rfl⟩ : syracuseStep 5156351 = 7734527) B7734527
theorem B48950921 : Blo 1526460 48950921 := bstep (se 2 (by rfl) ⟨18356595, by rfl⟩ : syracuseStep 48950921 = 36713191) B36713191
theorem B2175017 : Blo 1526460 2175017 := bstep (se 2 (by rfl) ⟨815631, by rfl⟩ : syracuseStep 2175017 = 1631263) B1631263
theorem B1528223 : Blo 1526460 1528223 := bstep (se 1 (by rfl) ⟨1146167, by rfl⟩ : syracuseStep 1528223 = 2292335) B2292335
theorem B1528447 : Blo 1526460 1528447 := bstep (se 1 (by rfl) ⟨1146335, by rfl⟩ : syracuseStep 1528447 = 2292671) B2292671
theorem B2290535 : Blo 1526460 2290535 := bstep (se 1 (by rfl) ⟨1717901, by rfl⟩ : syracuseStep 2290535 = 3435803) B3435803
theorem B2290601 : Blo 1526460 2290601 := bstep (se 2 (by rfl) ⟨858975, by rfl⟩ : syracuseStep 2290601 = 1717951) B1717951
theorem B5878811 : Blo 1526460 5878811 := bstep (se 1 (by rfl) ⟨4409108, by rfl⟩ : syracuseStep 5878811 = 8818217) B8818217
theorem B11007103 : Blo 1526460 11007103 := bstep (se 1 (by rfl) ⟨8255327, by rfl⟩ : syracuseStep 11007103 = 16510655) B16510655
theorem B11597417 : Blo 1526460 11597417 := bstep (se 2 (by rfl) ⟨4349031, by rfl⟩ : syracuseStep 11597417 = 8698063) B8698063
theorem B2291579 : Blo 1526460 2291579 := bstep (se 1 (by rfl) ⟨1718684, by rfl⟩ : syracuseStep 2291579 = 3437369) B3437369
theorem B5152247 : Blo 1526460 5152247 := bstep (se 1 (by rfl) ⟨3864185, by rfl⟩ : syracuseStep 5152247 = 7728371) B7728371
theorem B17399771 : Blo 1526460 17399771 := bstep (se 1 (by rfl) ⟨13049828, by rfl⟩ : syracuseStep 17399771 = 26099657) B26099657
theorem B5800045 : Blo 1526460 5800045 := bstep (se 3 (by rfl) ⟨1087508, by rfl⟩ : syracuseStep 5800045 = 2175017) B2175017
theorem B8815999 : Blo 1526460 8815999 := bstep (se 1 (by rfl) ⟨6611999, by rfl⟩ : syracuseStep 8815999 = 13223999) B13223999
theorem B3434831 : Blo 1526460 3434831 := bstep (se 1 (by rfl) ⟨2576123, by rfl⟩ : syracuseStep 3434831 = 5152247) B5152247
theorem B9284303 : Blo 1526460 9284303 := bstep (se 1 (by rfl) ⟨6963227, by rfl⟩ : syracuseStep 9284303 = 13926455) B13926455
theorem B1527023 : Blo 1526460 1527023 := bstep (se 1 (by rfl) ⟨1145267, by rfl⟩ : syracuseStep 1527023 = 2290535) B2290535
theorem B1527067 : Blo 1526460 1527067 := bstep (se 1 (by rfl) ⟨1145300, by rfl⟩ : syracuseStep 1527067 = 2290601) B2290601
theorem B3919207 : Blo 1526460 3919207 := bstep (se 1 (by rfl) ⟨2939405, by rfl⟩ : syracuseStep 3919207 = 5878811) B5878811
theorem B3435947 : Blo 1526460 3435947 := bstep (se 1 (by rfl) ⟨2576960, by rfl⟩ : syracuseStep 3435947 = 5153921) B5153921
theorem B1527719 : Blo 1526460 1527719 := bstep (se 1 (by rfl) ⟨1145789, by rfl⟩ : syracuseStep 1527719 = 2291579) B2291579
theorem B14676137 : Blo 1526460 14676137 := bstep (se 2 (by rfl) ⟨5503551, by rfl⟩ : syracuseStep 14676137 = 11007103) B11007103
theorem B7729343 : Blo 1526460 7729343 := bstep (se 1 (by rfl) ⟨5797007, by rfl⟩ : syracuseStep 7729343 = 11594015) B11594015
theorem B2290223 : Blo 1526460 2290223 := bstep (se 1 (by rfl) ⟨1717667, by rfl⟩ : syracuseStep 2290223 = 3435335) B3435335
theorem B3437567 : Blo 1526460 3437567 := bstep (se 1 (by rfl) ⟨2578175, by rfl⟩ : syracuseStep 3437567 = 5156351) B5156351
theorem B32633947 : Blo 1526460 32633947 := bstep (se 1 (by rfl) ⟨24475460, by rfl⟩ : syracuseStep 32633947 = 48950921) B48950921
theorem B5158025 : Blo 1526460 5158025 := bstep (se 2 (by rfl) ⟨1934259, by rfl⟩ : syracuseStep 5158025 = 3868519) B3868519
theorem B7731611 : Blo 1526460 7731611 := bstep (se 1 (by rfl) ⟨5798708, by rfl⟩ : syracuseStep 7731611 = 11597417) B11597417
theorem B11599847 : Blo 1526460 11599847 := bstep (se 1 (by rfl) ⟨8699885, by rfl⟩ : syracuseStep 11599847 = 17399771) B17399771
theorem B5152895 : Blo 1526460 5152895 := bstep (se 1 (by rfl) ⟨3864671, by rfl⟩ : syracuseStep 5152895 = 7729343) B7729343
theorem B7733393 : Blo 1526460 7733393 := bstep (se 2 (by rfl) ⟨2900022, by rfl⟩ : syracuseStep 7733393 = 5800045) B5800045
theorem B174047717 : Blo 1526460 174047717 := bstep (se 4 (by rfl) ⟨16316973, by rfl⟩ : syracuseStep 174047717 = 32633947) B32633947
theorem B5154407 : Blo 1526460 5154407 := bstep (se 1 (by rfl) ⟨3865805, by rfl⟩ : syracuseStep 5154407 = 7731611) B7731611
theorem B9784091 : Blo 1526460 9784091 := bstep (se 1 (by rfl) ⟨7338068, by rfl⟩ : syracuseStep 9784091 = 14676137) B14676137
theorem B1526815 : Blo 1526460 1526815 := bstep (se 1 (by rfl) ⟨1145111, by rfl⟩ : syracuseStep 1526815 = 2290223) B2290223
theorem B2289887 : Blo 1526460 2289887 := bstep (se 1 (by rfl) ⟨1717415, by rfl⟩ : syracuseStep 2289887 = 3434831) B3434831
theorem B6189535 : Blo 1526460 6189535 := bstep (se 1 (by rfl) ⟨4642151, by rfl⟩ : syracuseStep 6189535 = 9284303) B9284303
theorem B2290631 : Blo 1526460 2290631 := bstep (se 1 (by rfl) ⟨1717973, by rfl⟩ : syracuseStep 2290631 = 3435947) B3435947
theorem B2291711 : Blo 1526460 2291711 := bstep (se 1 (by rfl) ⟨1718783, by rfl⟩ : syracuseStep 2291711 = 3437567) B3437567
theorem B3438683 : Blo 1526460 3438683 := bstep (se 1 (by rfl) ⟨2579012, by rfl⟩ : syracuseStep 3438683 = 5158025) B5158025
theorem B5225609 : Blo 1526460 5225609 := bstep (se 2 (by rfl) ⟨1959603, by rfl⟩ : syracuseStep 5225609 = 3919207) B3919207
theorem B11754665 : Blo 1526460 11754665 := bstep (se 2 (by rfl) ⟨4407999, by rfl⟩ : syracuseStep 11754665 = 8815999) B8815999
theorem B7733231 : Blo 1526460 7733231 := bstep (se 1 (by rfl) ⟨5799923, by rfl⟩ : syracuseStep 7733231 = 11599847) B11599847
theorem B464127245 : Blo 1526460 464127245 := bstep (se 3 (by rfl) ⟨87023858, by rfl⟩ : syracuseStep 464127245 = 174047717) B174047717
theorem B3483739 : Blo 1526460 3483739 := bstep (se 1 (by rfl) ⟨2612804, by rfl⟩ : syracuseStep 3483739 = 5225609) B5225609
theorem B5155487 : Blo 1526460 5155487 := bstep (se 1 (by rfl) ⟨3866615, by rfl⟩ : syracuseStep 5155487 = 7733231) B7733231
theorem B3435263 : Blo 1526460 3435263 := bstep (se 1 (by rfl) ⟨2576447, by rfl⟩ : syracuseStep 3435263 = 5152895) B5152895
theorem B5155595 : Blo 1526460 5155595 := bstep (se 1 (by rfl) ⟨3866696, by rfl⟩ : syracuseStep 5155595 = 7733393) B7733393
theorem B1526591 : Blo 1526460 1526591 := bstep (se 1 (by rfl) ⟨1144943, by rfl⟩ : syracuseStep 1526591 = 2289887) B2289887
theorem B8252713 : Blo 1526460 8252713 := bstep (se 2 (by rfl) ⟨3094767, by rfl⟩ : syracuseStep 8252713 = 6189535) B6189535
theorem B1527087 : Blo 1526460 1527087 := bstep (se 1 (by rfl) ⟨1145315, by rfl⟩ : syracuseStep 1527087 = 2290631) B2290631
theorem B3436271 : Blo 1526460 3436271 := bstep (se 1 (by rfl) ⟨2577203, by rfl⟩ : syracuseStep 3436271 = 5154407) B5154407
theorem B1527807 : Blo 1526460 1527807 := bstep (se 1 (by rfl) ⟨1145855, by rfl⟩ : syracuseStep 1527807 = 2291711) B2291711
theorem B7836443 : Blo 1526460 7836443 := bstep (se 1 (by rfl) ⟨5877332, by rfl⟩ : syracuseStep 7836443 = 11754665) B11754665
theorem B2292455 : Blo 1526460 2292455 := bstep (se 1 (by rfl) ⟨1719341, by rfl⟩ : syracuseStep 2292455 = 3438683) B3438683
theorem B26090909 : Blo 1526460 26090909 := bstep (se 3 (by rfl) ⟨4892045, by rfl⟩ : syracuseStep 26090909 = 9784091) B9784091
theorem B18579941 : Blo 1526460 18579941 := bstep (se 4 (by rfl) ⟨1741869, by rfl⟩ : syracuseStep 18579941 = 3483739) B3483739
theorem B11003617 : Blo 1526460 11003617 := bstep (se 2 (by rfl) ⟨4126356, by rfl⟩ : syracuseStep 11003617 = 8252713) B8252713
theorem B17393939 : Blo 1526460 17393939 := bstep (se 1 (by rfl) ⟨13045454, by rfl⟩ : syracuseStep 17393939 = 26090909) B26090909
theorem B3436991 : Blo 1526460 3436991 := bstep (se 1 (by rfl) ⟨2577743, by rfl⟩ : syracuseStep 3436991 = 5155487) B5155487
theorem B1528303 : Blo 1526460 1528303 := bstep (se 1 (by rfl) ⟨1146227, by rfl⟩ : syracuseStep 1528303 = 2292455) B2292455
theorem B2290175 : Blo 1526460 2290175 := bstep (se 1 (by rfl) ⟨1717631, by rfl⟩ : syracuseStep 2290175 = 3435263) B3435263
theorem B3437063 : Blo 1526460 3437063 := bstep (se 1 (by rfl) ⟨2577797, by rfl⟩ : syracuseStep 3437063 = 5155595) B5155595
theorem B2290847 : Blo 1526460 2290847 := bstep (se 1 (by rfl) ⟨1718135, by rfl⟩ : syracuseStep 2290847 = 3436271) B3436271
theorem B5224295 : Blo 1526460 5224295 := bstep (se 1 (by rfl) ⟨3918221, by rfl⟩ : syracuseStep 5224295 = 7836443) B7836443
theorem B309418163 : Blo 1526460 309418163 := bstep (se 1 (by rfl) ⟨232063622, by rfl⟩ : syracuseStep 309418163 = 464127245) B464127245
theorem B12386627 : Blo 1526460 12386627 := bstep (se 1 (by rfl) ⟨9289970, by rfl⟩ : syracuseStep 12386627 = 18579941) B18579941
theorem B1526783 : Blo 1526460 1526783 := bstep (se 1 (by rfl) ⟨1145087, by rfl⟩ : syracuseStep 1526783 = 2290175) B2290175
theorem B1527231 : Blo 1526460 1527231 := bstep (se 1 (by rfl) ⟨1145423, by rfl⟩ : syracuseStep 1527231 = 2290847) B2290847
theorem B206278775 : Blo 1526460 206278775 := bstep (se 1 (by rfl) ⟨154709081, by rfl⟩ : syracuseStep 206278775 = 309418163) B309418163
theorem B11595959 : Blo 1526460 11595959 := bstep (se 1 (by rfl) ⟨8696969, by rfl⟩ : syracuseStep 11595959 = 17393939) B17393939
theorem B13931453 : Blo 1526460 13931453 := bstep (se 3 (by rfl) ⟨2612147, by rfl⟩ : syracuseStep 13931453 = 5224295) B5224295
theorem B2291327 : Blo 1526460 2291327 := bstep (se 1 (by rfl) ⟨1718495, by rfl⟩ : syracuseStep 2291327 = 3436991) B3436991
theorem B2291375 : Blo 1526460 2291375 := bstep (se 1 (by rfl) ⟨1718531, by rfl⟩ : syracuseStep 2291375 = 3437063) B3437063
theorem B14671489 : Blo 1526460 14671489 := bstep (se 2 (by rfl) ⟨5501808, by rfl⟩ : syracuseStep 14671489 = 11003617) B11003617
theorem B137519183 : Blo 1526460 137519183 := bstep (se 1 (by rfl) ⟨103139387, by rfl⟩ : syracuseStep 137519183 = 206278775) B206278775
theorem B8257751 : Blo 1526460 8257751 := bstep (se 1 (by rfl) ⟨6193313, by rfl⟩ : syracuseStep 8257751 = 12386627) B12386627
theorem B1527551 : Blo 1526460 1527551 := bstep (se 1 (by rfl) ⟨1145663, by rfl⟩ : syracuseStep 1527551 = 2291327) B2291327
theorem B1527583 : Blo 1526460 1527583 := bstep (se 1 (by rfl) ⟨1145687, by rfl⟩ : syracuseStep 1527583 = 2291375) B2291375
theorem B7730639 : Blo 1526460 7730639 := bstep (se 1 (by rfl) ⟨5797979, by rfl⟩ : syracuseStep 7730639 = 11595959) B11595959
theorem B9287635 : Blo 1526460 9287635 := bstep (se 1 (by rfl) ⟨6965726, by rfl⟩ : syracuseStep 9287635 = 13931453) B13931453
theorem B19561985 : Blo 1526460 19561985 := bstep (se 2 (by rfl) ⟨7335744, by rfl⟩ : syracuseStep 19561985 = 14671489) B14671489
theorem B5505167 : Blo 1526460 5505167 := bstep (se 1 (by rfl) ⟨4128875, by rfl⟩ : syracuseStep 5505167 = 8257751) B8257751
theorem B5153759 : Blo 1526460 5153759 := bstep (se 1 (by rfl) ⟨3865319, by rfl⟩ : syracuseStep 5153759 = 7730639) B7730639
theorem B91679455 : Blo 1526460 91679455 := bstep (se 1 (by rfl) ⟨68759591, by rfl⟩ : syracuseStep 91679455 = 137519183) B137519183
theorem B12383513 : Blo 1526460 12383513 := bstep (se 2 (by rfl) ⟨4643817, by rfl⟩ : syracuseStep 12383513 = 9287635) B9287635
theorem B13041323 : Blo 1526460 13041323 := bstep (se 1 (by rfl) ⟨9780992, by rfl⟩ : syracuseStep 13041323 = 19561985) B19561985
theorem B3670111 : Blo 1526460 3670111 := bstep (se 1 (by rfl) ⟨2752583, by rfl⟩ : syracuseStep 3670111 = 5505167) B5505167
theorem B8694215 : Blo 1526460 8694215 := bstep (se 1 (by rfl) ⟨6520661, by rfl⟩ : syracuseStep 8694215 = 13041323) B13041323
theorem B3435839 : Blo 1526460 3435839 := bstep (se 1 (by rfl) ⟨2576879, by rfl⟩ : syracuseStep 3435839 = 5153759) B5153759
theorem B8255675 : Blo 1526460 8255675 := bstep (se 1 (by rfl) ⟨6191756, by rfl⟩ : syracuseStep 8255675 = 12383513) B12383513
theorem B122239273 : Blo 1526460 122239273 := bstep (se 2 (by rfl) ⟨45839727, by rfl⟩ : syracuseStep 122239273 = 91679455) B91679455
theorem B4893481 : Blo 1526460 4893481 := bstep (se 2 (by rfl) ⟨1835055, by rfl⟩ : syracuseStep 4893481 = 3670111) B3670111
theorem B5796143 : Blo 1526460 5796143 := bstep (se 1 (by rfl) ⟨4347107, by rfl⟩ : syracuseStep 5796143 = 8694215) B8694215
theorem B2290559 : Blo 1526460 2290559 := bstep (se 1 (by rfl) ⟨1717919, by rfl⟩ : syracuseStep 2290559 = 3435839) B3435839
theorem B162985697 : Blo 1526460 162985697 := bstep (se 2 (by rfl) ⟨61119636, by rfl⟩ : syracuseStep 162985697 = 122239273) B122239273
theorem B5503783 : Blo 1526460 5503783 := bstep (se 1 (by rfl) ⟨4127837, by rfl⟩ : syracuseStep 5503783 = 8255675) B8255675
theorem B1527039 : Blo 1526460 1527039 := bstep (se 1 (by rfl) ⟨1145279, by rfl⟩ : syracuseStep 1527039 = 2290559) B2290559
theorem B6524641 : Blo 1526460 6524641 := bstep (se 2 (by rfl) ⟨2446740, by rfl⟩ : syracuseStep 6524641 = 4893481) B4893481
theorem B3864095 : Blo 1526460 3864095 := bstep (se 1 (by rfl) ⟨2898071, by rfl⟩ : syracuseStep 3864095 = 5796143) B5796143
theorem B7338377 : Blo 1526460 7338377 := bstep (se 2 (by rfl) ⟨2751891, by rfl⟩ : syracuseStep 7338377 = 5503783) B5503783
theorem B108657131 : Blo 1526460 108657131 := bstep (se 1 (by rfl) ⟨81492848, by rfl⟩ : syracuseStep 108657131 = 162985697) B162985697
theorem B289752349 : Blo 1526460 289752349 := bstep (se 3 (by rfl) ⟨54328565, by rfl⟩ : syracuseStep 289752349 = 108657131) B108657131
theorem B4892251 : Blo 1526460 4892251 := bstep (se 1 (by rfl) ⟨3669188, by rfl⟩ : syracuseStep 4892251 = 7338377) B7338377
theorem B2576063 : Blo 1526460 2576063 := bstep (se 1 (by rfl) ⟨1932047, by rfl⟩ : syracuseStep 2576063 = 3864095) B3864095
theorem B8699521 : Blo 1526460 8699521 := bstep (se 2 (by rfl) ⟨3262320, by rfl⟩ : syracuseStep 8699521 = 6524641) B6524641
theorem B386336465 : Blo 1526460 386336465 := bstep (se 2 (by rfl) ⟨144876174, by rfl⟩ : syracuseStep 386336465 = 289752349) B289752349
theorem B6523001 : Blo 1526460 6523001 := bstep (se 2 (by rfl) ⟨2446125, by rfl⟩ : syracuseStep 6523001 = 4892251) B4892251
theorem B1717375 : Blo 1526460 1717375 := bstep (se 1 (by rfl) ⟨1288031, by rfl⟩ : syracuseStep 1717375 = 2576063) B2576063
theorem B11599361 : Blo 1526460 11599361 := bstep (se 2 (by rfl) ⟨4349760, by rfl⟩ : syracuseStep 11599361 = 8699521) B8699521
theorem B257557643 : Blo 1526460 257557643 := bstep (se 1 (by rfl) ⟨193168232, by rfl⟩ : syracuseStep 257557643 = 386336465) B386336465
theorem B2289833 : Blo 1526460 2289833 := bstep (se 2 (by rfl) ⟨858687, by rfl⟩ : syracuseStep 2289833 = 1717375) B1717375
theorem B4348667 : Blo 1526460 4348667 := bstep (se 1 (by rfl) ⟨3261500, by rfl⟩ : syracuseStep 4348667 = 6523001) B6523001
theorem B7732907 : Blo 1526460 7732907 := bstep (se 1 (by rfl) ⟨5799680, by rfl⟩ : syracuseStep 7732907 = 11599361) B11599361
theorem B171705095 : Blo 1526460 171705095 := bstep (se 1 (by rfl) ⟨128778821, by rfl⟩ : syracuseStep 171705095 = 257557643) B257557643
theorem B5155271 : Blo 1526460 5155271 := bstep (se 1 (by rfl) ⟨3866453, by rfl⟩ : syracuseStep 5155271 = 7732907) B7732907
theorem B1526555 : Blo 1526460 1526555 := bstep (se 1 (by rfl) ⟨1144916, by rfl⟩ : syracuseStep 1526555 = 2289833) B2289833
theorem B11596445 : Blo 1526460 11596445 := bstep (se 3 (by rfl) ⟨2174333, by rfl⟩ : syracuseStep 11596445 = 4348667) B4348667
theorem B114470063 : Blo 1526460 114470063 := bstep (se 1 (by rfl) ⟨85852547, by rfl⟩ : syracuseStep 114470063 = 171705095) B171705095
theorem B3436847 : Blo 1526460 3436847 := bstep (se 1 (by rfl) ⟨2577635, by rfl⟩ : syracuseStep 3436847 = 5155271) B5155271
theorem B7730963 : Blo 1526460 7730963 := bstep (se 1 (by rfl) ⟨5798222, by rfl⟩ : syracuseStep 7730963 = 11596445) B11596445
theorem B5153975 : Blo 1526460 5153975 := bstep (se 1 (by rfl) ⟨3865481, by rfl⟩ : syracuseStep 5153975 = 7730963) B7730963
theorem B76313375 : Blo 1526460 76313375 := bstep (se 1 (by rfl) ⟨57235031, by rfl⟩ : syracuseStep 76313375 = 114470063) B114470063
theorem B2291231 : Blo 1526460 2291231 := bstep (se 1 (by rfl) ⟨1718423, by rfl⟩ : syracuseStep 2291231 = 3436847) B3436847
theorem B50875583 : Blo 1526460 50875583 := bstep (se 1 (by rfl) ⟨38156687, by rfl⟩ : syracuseStep 50875583 = 76313375) B76313375
theorem B3435983 : Blo 1526460 3435983 := bstep (se 1 (by rfl) ⟨2576987, by rfl⟩ : syracuseStep 3435983 = 5153975) B5153975
theorem B1527487 : Blo 1526460 1527487 := bstep (se 1 (by rfl) ⟨1145615, by rfl⟩ : syracuseStep 1527487 = 2291231) B2291231
theorem B542672885 : Blo 1526460 542672885 := bstep (se 5 (by rfl) ⟨25437791, by rfl⟩ : syracuseStep 542672885 = 50875583) B50875583
theorem B2290655 : Blo 1526460 2290655 := bstep (se 1 (by rfl) ⟨1717991, by rfl⟩ : syracuseStep 2290655 = 3435983) B3435983
theorem B1527103 : Blo 1526460 1527103 := bstep (se 1 (by rfl) ⟨1145327, by rfl⟩ : syracuseStep 1527103 = 2290655) B2290655
theorem B361781923 : Blo 1526460 361781923 := bstep (se 1 (by rfl) ⟨271336442, by rfl⟩ : syracuseStep 361781923 = 542672885) B542672885
theorem B482375897 : Blo 1526460 482375897 := bstep (se 2 (by rfl) ⟨180890961, by rfl⟩ : syracuseStep 482375897 = 361781923) B361781923
theorem B321583931 : Blo 1526460 321583931 := bstep (se 1 (by rfl) ⟨241187948, by rfl⟩ : syracuseStep 321583931 = 482375897) B482375897
theorem B214389287 : Blo 1526460 214389287 := bstep (se 1 (by rfl) ⟨160791965, by rfl⟩ : syracuseStep 214389287 = 321583931) B321583931
theorem B142926191 : Blo 1526460 142926191 := bstep (se 1 (by rfl) ⟨107194643, by rfl⟩ : syracuseStep 142926191 = 214389287) B214389287
theorem B95284127 : Blo 1526460 95284127 := bstep (se 1 (by rfl) ⟨71463095, by rfl⟩ : syracuseStep 95284127 = 142926191) B142926191
theorem B254091005 : Blo 1526460 254091005 := bstep (se 3 (by rfl) ⟨47642063, by rfl⟩ : syracuseStep 254091005 = 95284127) B95284127
theorem B169394003 : Blo 1526460 169394003 := bstep (se 1 (by rfl) ⟨127045502, by rfl⟩ : syracuseStep 169394003 = 254091005) B254091005
theorem B112929335 : Blo 1526460 112929335 := bstep (se 1 (by rfl) ⟨84697001, by rfl⟩ : syracuseStep 112929335 = 169394003) B169394003
theorem B75286223 : Blo 1526460 75286223 := bstep (se 1 (by rfl) ⟨56464667, by rfl⟩ : syracuseStep 75286223 = 112929335) B112929335
theorem B50190815 : Blo 1526460 50190815 := bstep (se 1 (by rfl) ⟨37643111, by rfl⟩ : syracuseStep 50190815 = 75286223) B75286223
theorem B33460543 : Blo 1526460 33460543 := bstep (se 1 (by rfl) ⟨25095407, by rfl⟩ : syracuseStep 33460543 = 50190815) B50190815
theorem B178456229 : Blo 1526460 178456229 := bstep (se 4 (by rfl) ⟨16730271, by rfl⟩ : syracuseStep 178456229 = 33460543) B33460543
theorem B118970819 : Blo 1526460 118970819 := bstep (se 1 (by rfl) ⟨89228114, by rfl⟩ : syracuseStep 118970819 = 178456229) B178456229
theorem B79313879 : Blo 1526460 79313879 := bstep (se 1 (by rfl) ⟨59485409, by rfl⟩ : syracuseStep 79313879 = 118970819) B118970819
theorem B52875919 : Blo 1526460 52875919 := bstep (se 1 (by rfl) ⟨39656939, by rfl⟩ : syracuseStep 52875919 = 79313879) B79313879
theorem B70501225 : Blo 1526460 70501225 := bstep (se 2 (by rfl) ⟨26437959, by rfl⟩ : syracuseStep 70501225 = 52875919) B52875919
theorem B94001633 : Blo 1526460 94001633 := bstep (se 2 (by rfl) ⟨35250612, by rfl⟩ : syracuseStep 94001633 = 70501225) B70501225
theorem B62667755 : Blo 1526460 62667755 := bstep (se 1 (by rfl) ⟨47000816, by rfl⟩ : syracuseStep 62667755 = 94001633) B94001633
theorem B41778503 : Blo 1526460 41778503 := bstep (se 1 (by rfl) ⟨31333877, by rfl⟩ : syracuseStep 41778503 = 62667755) B62667755
theorem B27852335 : Blo 1526460 27852335 := bstep (se 1 (by rfl) ⟨20889251, by rfl⟩ : syracuseStep 27852335 = 41778503) B41778503
theorem B18568223 : Blo 1526460 18568223 := bstep (se 1 (by rfl) ⟨13926167, by rfl⟩ : syracuseStep 18568223 = 27852335) B27852335
theorem B12378815 : Blo 1526460 12378815 := bstep (se 1 (by rfl) ⟨9284111, by rfl⟩ : syracuseStep 12378815 = 18568223) B18568223
theorem B8252543 : Blo 1526460 8252543 := bstep (se 1 (by rfl) ⟨6189407, by rfl⟩ : syracuseStep 8252543 = 12378815) B12378815
theorem B5501695 : Blo 1526460 5501695 := bstep (se 1 (by rfl) ⟨4126271, by rfl⟩ : syracuseStep 5501695 = 8252543) B8252543
theorem B7335593 : Blo 1526460 7335593 := bstep (se 2 (by rfl) ⟨2750847, by rfl⟩ : syracuseStep 7335593 = 5501695) B5501695
theorem B4890395 : Blo 1526460 4890395 := bstep (se 1 (by rfl) ⟨3667796, by rfl⟩ : syracuseStep 4890395 = 7335593) B7335593
theorem B3260263 : Blo 1526460 3260263 := bstep (se 1 (by rfl) ⟨2445197, by rfl⟩ : syracuseStep 3260263 = 4890395) B4890395
theorem B4347017 : Blo 1526460 4347017 := bstep (se 2 (by rfl) ⟨1630131, by rfl⟩ : syracuseStep 4347017 = 3260263) B3260263
theorem B2898011 : Blo 1526460 2898011 := bstep (se 1 (by rfl) ⟨2173508, by rfl⟩ : syracuseStep 2898011 = 4347017) B4347017
theorem B1932007 : Blo 1526460 1932007 := bstep (se 1 (by rfl) ⟨1449005, by rfl⟩ : syracuseStep 1932007 = 2898011) B2898011
theorem B2576009 : Blo 1526460 2576009 := bstep (se 2 (by rfl) ⟨966003, by rfl⟩ : syracuseStep 2576009 = 1932007) B1932007
theorem B1717339 : Blo 1526460 1717339 := bstep (se 1 (by rfl) ⟨1288004, by rfl⟩ : syracuseStep 1717339 = 2576009) B2576009
theorem B2289785 : Blo 1526460 2289785 := bstep (se 2 (by rfl) ⟨858669, by rfl⟩ : syracuseStep 2289785 = 1717339) B1717339
theorem B1526523 : Blo 1526460 1526523 := bstep (se 1 (by rfl) ⟨1144892, by rfl⟩ : syracuseStep 1526523 = 2289785) B2289785

theorem C0 (j : ℕ) (h1 : 381615 ≤ j) (h2 : j ≤ 382114) : Blo 1526460 (4 * j + 3) := by
  interval_cases j
  · exact B1526463
  · exact B1526467
  · exact B1526471
  · exact B1526475
  · exact B1526479
  · exact B1526483
  · exact B1526487
  · exact B1526491
  · exact B1526495
  · exact B1526499
  · exact B1526503
  · exact B1526507
  · exact B1526511
  · exact B1526515
  · exact B1526519
  · exact B1526523
  · exact B1526527
  · exact B1526531
  · exact B1526535
  · exact B1526539
  · exact B1526543
  · exact B1526547
  · exact B1526551
  · exact B1526555
  · exact B1526559
  · exact B1526563
  · exact B1526567
  · exact B1526571
  · exact B1526575
  · exact B1526579
  · exact B1526583
  · exact B1526587
  · exact B1526591
  · exact B1526595
  · exact B1526599
  · exact B1526603
  · exact B1526607
  · exact B1526611
  · exact B1526615
  · exact B1526619
  · exact B1526623
  · exact B1526627
  · exact B1526631
  · exact B1526635
  · exact B1526639
  · exact B1526643
  · exact B1526647
  · exact B1526651
  · exact B1526655
  · exact B1526659
  · exact B1526663
  · exact B1526667
  · exact B1526671
  · exact B1526675
  · exact B1526679
  · exact B1526683
  · exact B1526687
  · exact B1526691
  · exact B1526695
  · exact B1526699
  · exact B1526703
  · exact B1526707
  · exact B1526711
  · exact B1526715
  · exact B1526719
  · exact B1526723
  · exact B1526727
  · exact B1526731
  · exact B1526735
  · exact B1526739
  · exact B1526743
  · exact B1526747
  · exact B1526751
  · exact B1526755
  · exact B1526759
  · exact B1526763
  · exact B1526767
  · exact B1526771
  · exact B1526775
  · exact B1526779
  · exact B1526783
  · exact B1526787
  · exact B1526791
  · exact B1526795
  · exact B1526799
  · exact B1526803
  · exact B1526807
  · exact B1526811
  · exact B1526815
  · exact B1526819
  · exact B1526823
  · exact B1526827
  · exact B1526831
  · exact B1526835
  · exact B1526839
  · exact B1526843
  · exact B1526847
  · exact B1526851
  · exact B1526855
  · exact B1526859
  · exact B1526863
  · exact B1526867
  · exact B1526871
  · exact B1526875
  · exact B1526879
  · exact B1526883
  · exact B1526887
  · exact B1526891
  · exact B1526895
  · exact B1526899
  · exact B1526903
  · exact B1526907
  · exact B1526911
  · exact B1526915
  · exact B1526919
  · exact B1526923
  · exact B1526927
  · exact B1526931
  · exact B1526935
  · exact B1526939
  · exact B1526943
  · exact B1526947
  · exact B1526951
  · exact B1526955
  · exact B1526959
  · exact B1526963
  · exact B1526967
  · exact B1526971
  · exact B1526975
  · exact B1526979
  · exact B1526983
  · exact B1526987
  · exact B1526991
  · exact B1526995
  · exact B1526999
  · exact B1527003
  · exact B1527007
  · exact B1527011
  · exact B1527015
  · exact B1527019
  · exact B1527023
  · exact B1527027
  · exact B1527031
  · exact B1527035
  · exact B1527039
  · exact B1527043
  · exact B1527047
  · exact B1527051
  · exact B1527055
  · exact B1527059
  · exact B1527063
  · exact B1527067
  · exact B1527071
  · exact B1527075
  · exact B1527079
  · exact B1527083
  · exact B1527087
  · exact B1527091
  · exact B1527095
  · exact B1527099
  · exact B1527103
  · exact B1527107
  · exact B1527111
  · exact B1527115
  · exact B1527119
  · exact B1527123
  · exact B1527127
  · exact B1527131
  · exact B1527135
  · exact B1527139
  · exact B1527143
  · exact B1527147
  · exact B1527151
  · exact B1527155
  · exact B1527159
  · exact B1527163
  · exact B1527167
  · exact B1527171
  · exact B1527175
  · exact B1527179
  · exact B1527183
  · exact B1527187
  · exact B1527191
  · exact B1527195
  · exact B1527199
  · exact B1527203
  · exact B1527207
  · exact B1527211
  · exact B1527215
  · exact B1527219
  · exact B1527223
  · exact B1527227
  · exact B1527231
  · exact B1527235
  · exact B1527239
  · exact B1527243
  · exact B1527247
  · exact B1527251
  · exact B1527255
  · exact B1527259
  · exact B1527263
  · exact B1527267
  · exact B1527271
  · exact B1527275
  · exact B1527279
  · exact B1527283
  · exact B1527287
  · exact B1527291
  · exact B1527295
  · exact B1527299
  · exact B1527303
  · exact B1527307
  · exact B1527311
  · exact B1527315
  · exact B1527319
  · exact B1527323
  · exact B1527327
  · exact B1527331
  · exact B1527335
  · exact B1527339
  · exact B1527343
  · exact B1527347
  · exact B1527351
  · exact B1527355
  · exact B1527359
  · exact B1527363
  · exact B1527367
  · exact B1527371
  · exact B1527375
  · exact B1527379
  · exact B1527383
  · exact B1527387
  · exact B1527391
  · exact B1527395
  · exact B1527399
  · exact B1527403
  · exact B1527407
  · exact B1527411
  · exact B1527415
  · exact B1527419
  · exact B1527423
  · exact B1527427
  · exact B1527431
  · exact B1527435
  · exact B1527439
  · exact B1527443
  · exact B1527447
  · exact B1527451
  · exact B1527455
  · exact B1527459
  · exact B1527463
  · exact B1527467
  · exact B1527471
  · exact B1527475
  · exact B1527479
  · exact B1527483
  · exact B1527487
  · exact B1527491
  · exact B1527495
  · exact B1527499
  · exact B1527503
  · exact B1527507
  · exact B1527511
  · exact B1527515
  · exact B1527519
  · exact B1527523
  · exact B1527527
  · exact B1527531
  · exact B1527535
  · exact B1527539
  · exact B1527543
  · exact B1527547
  · exact B1527551
  · exact B1527555
  · exact B1527559
  · exact B1527563
  · exact B1527567
  · exact B1527571
  · exact B1527575
  · exact B1527579
  · exact B1527583
  · exact B1527587
  · exact B1527591
  · exact B1527595
  · exact B1527599
  · exact B1527603
  · exact B1527607
  · exact B1527611
  · exact B1527615
  · exact B1527619
  · exact B1527623
  · exact B1527627
  · exact B1527631
  · exact B1527635
  · exact B1527639
  · exact B1527643
  · exact B1527647
  · exact B1527651
  · exact B1527655
  · exact B1527659
  · exact B1527663
  · exact B1527667
  · exact B1527671
  · exact B1527675
  · exact B1527679
  · exact B1527683
  · exact B1527687
  · exact B1527691
  · exact B1527695
  · exact B1527699
  · exact B1527703
  · exact B1527707
  · exact B1527711
  · exact B1527715
  · exact B1527719
  · exact B1527723
  · exact B1527727
  · exact B1527731
  · exact B1527735
  · exact B1527739
  · exact B1527743
  · exact B1527747
  · exact B1527751
  · exact B1527755
  · exact B1527759
  · exact B1527763
  · exact B1527767
  · exact B1527771
  · exact B1527775
  · exact B1527779
  · exact B1527783
  · exact B1527787
  · exact B1527791
  · exact B1527795
  · exact B1527799
  · exact B1527803
  · exact B1527807
  · exact B1527811
  · exact B1527815
  · exact B1527819
  · exact B1527823
  · exact B1527827
  · exact B1527831
  · exact B1527835
  · exact B1527839
  · exact B1527843
  · exact B1527847
  · exact B1527851
  · exact B1527855
  · exact B1527859
  · exact B1527863
  · exact B1527867
  · exact B1527871
  · exact B1527875
  · exact B1527879
  · exact B1527883
  · exact B1527887
  · exact B1527891
  · exact B1527895
  · exact B1527899
  · exact B1527903
  · exact B1527907
  · exact B1527911
  · exact B1527915
  · exact B1527919
  · exact B1527923
  · exact B1527927
  · exact B1527931
  · exact B1527935
  · exact B1527939
  · exact B1527943
  · exact B1527947
  · exact B1527951
  · exact B1527955
  · exact B1527959
  · exact B1527963
  · exact B1527967
  · exact B1527971
  · exact B1527975
  · exact B1527979
  · exact B1527983
  · exact B1527987
  · exact B1527991
  · exact B1527995
  · exact B1527999
  · exact B1528003
  · exact B1528007
  · exact B1528011
  · exact B1528015
  · exact B1528019
  · exact B1528023
  · exact B1528027
  · exact B1528031
  · exact B1528035
  · exact B1528039
  · exact B1528043
  · exact B1528047
  · exact B1528051
  · exact B1528055
  · exact B1528059
  · exact B1528063
  · exact B1528067
  · exact B1528071
  · exact B1528075
  · exact B1528079
  · exact B1528083
  · exact B1528087
  · exact B1528091
  · exact B1528095
  · exact B1528099
  · exact B1528103
  · exact B1528107
  · exact B1528111
  · exact B1528115
  · exact B1528119
  · exact B1528123
  · exact B1528127
  · exact B1528131
  · exact B1528135
  · exact B1528139
  · exact B1528143
  · exact B1528147
  · exact B1528151
  · exact B1528155
  · exact B1528159
  · exact B1528163
  · exact B1528167
  · exact B1528171
  · exact B1528175
  · exact B1528179
  · exact B1528183
  · exact B1528187
  · exact B1528191
  · exact B1528195
  · exact B1528199
  · exact B1528203
  · exact B1528207
  · exact B1528211
  · exact B1528215
  · exact B1528219
  · exact B1528223
  · exact B1528227
  · exact B1528231
  · exact B1528235
  · exact B1528239
  · exact B1528243
  · exact B1528247
  · exact B1528251
  · exact B1528255
  · exact B1528259
  · exact B1528263
  · exact B1528267
  · exact B1528271
  · exact B1528275
  · exact B1528279
  · exact B1528283
  · exact B1528287
  · exact B1528291
  · exact B1528295
  · exact B1528299
  · exact B1528303
  · exact B1528307
  · exact B1528311
  · exact B1528315
  · exact B1528319
  · exact B1528323
  · exact B1528327
  · exact B1528331
  · exact B1528335
  · exact B1528339
  · exact B1528343
  · exact B1528347
  · exact B1528351
  · exact B1528355
  · exact B1528359
  · exact B1528363
  · exact B1528367
  · exact B1528371
  · exact B1528375
  · exact B1528379
  · exact B1528383
  · exact B1528387
  · exact B1528391
  · exact B1528395
  · exact B1528399
  · exact B1528403
  · exact B1528407
  · exact B1528411
  · exact B1528415
  · exact B1528419
  · exact B1528423
  · exact B1528427
  · exact B1528431
  · exact B1528435
  · exact B1528439
  · exact B1528443
  · exact B1528447
  · exact B1528451
  · exact B1528455
  · exact B1528459

theorem solution (m : ℕ) (hlo : 1526460 ≤ m) (hhi : m ≤ 1528460) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 381615 ≤ j := by omega
    have hj2 : j ≤ 382114 := by omega
    have hb : Blo 1526460 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
