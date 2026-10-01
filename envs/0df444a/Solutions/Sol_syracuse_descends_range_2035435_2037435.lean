-- Prove2me | solution 1 for syracuse_descends_range_2035435_2037435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:49:10.349677+00:00
-- url     : https://prove2.me/submissions/f6815ed5-56bb-4007-aa04-b0e1a1b4aa5f

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

theorem B2289865 : Blo 2035435 2289865 := bbase (se 2 (by rfl) ⟨858699, by rfl⟩ : syracuseStep 2289865 = 1717399) (by norm_num)
theorem B3053153 : Blo 2035435 3053153 := bstep (se 2 (by rfl) ⟨1144932, by rfl⟩ : syracuseStep 3053153 = 2289865) B2289865
theorem B2035435 : Blo 2035435 2035435 := bstep (se 1 (by rfl) ⟨1526576, by rfl⟩ : syracuseStep 2035435 = 3053153) B3053153
theorem B4126421 : Blo 2035435 4126421 := bbase (se 7 (by rfl) ⟨48356, by rfl⟩ : syracuseStep 4126421 = 96713) (by norm_num)
theorem B11003789 : Blo 2035435 11003789 := bstep (se 3 (by rfl) ⟨2063210, by rfl⟩ : syracuseStep 11003789 = 4126421) B4126421
theorem B7335859 : Blo 2035435 7335859 := bstep (se 1 (by rfl) ⟨5501894, by rfl⟩ : syracuseStep 7335859 = 11003789) B11003789
theorem B9781145 : Blo 2035435 9781145 := bstep (se 2 (by rfl) ⟨3667929, by rfl⟩ : syracuseStep 9781145 = 7335859) B7335859
theorem B6520763 : Blo 2035435 6520763 := bstep (se 1 (by rfl) ⟨4890572, by rfl⟩ : syracuseStep 6520763 = 9781145) B9781145
theorem B17388701 : Blo 2035435 17388701 := bstep (se 3 (by rfl) ⟨3260381, by rfl⟩ : syracuseStep 17388701 = 6520763) B6520763
theorem B11592467 : Blo 2035435 11592467 := bstep (se 1 (by rfl) ⟨8694350, by rfl⟩ : syracuseStep 11592467 = 17388701) B17388701
theorem B7728311 : Blo 2035435 7728311 := bstep (se 1 (by rfl) ⟨5796233, by rfl⟩ : syracuseStep 7728311 = 11592467) B11592467
theorem B5152207 : Blo 2035435 5152207 := bstep (se 1 (by rfl) ⟨3864155, by rfl⟩ : syracuseStep 5152207 = 7728311) B7728311
theorem B6869609 : Blo 2035435 6869609 := bstep (se 2 (by rfl) ⟨2576103, by rfl⟩ : syracuseStep 6869609 = 5152207) B5152207
theorem B4579739 : Blo 2035435 4579739 := bstep (se 1 (by rfl) ⟨3434804, by rfl⟩ : syracuseStep 4579739 = 6869609) B6869609
theorem B3053159 : Blo 2035435 3053159 := bstep (se 1 (by rfl) ⟨2289869, by rfl⟩ : syracuseStep 3053159 = 4579739) B4579739
theorem B2035439 : Blo 2035435 2035439 := bstep (se 1 (by rfl) ⟨1526579, by rfl⟩ : syracuseStep 2035439 = 3053159) B3053159
theorem B3053165 : Blo 2035435 3053165 := bbase (se 3 (by rfl) ⟨572468, by rfl⟩ : syracuseStep 3053165 = 1144937) (by norm_num)
theorem B2035443 : Blo 2035435 2035443 := bstep (se 1 (by rfl) ⟨1526582, by rfl⟩ : syracuseStep 2035443 = 3053165) B3053165
theorem B4579757 : Blo 2035435 4579757 := bbase (se 3 (by rfl) ⟨858704, by rfl⟩ : syracuseStep 4579757 = 1717409) (by norm_num)
theorem B3053171 : Blo 2035435 3053171 := bstep (se 1 (by rfl) ⟨2289878, by rfl⟩ : syracuseStep 3053171 = 4579757) B4579757
theorem B2035447 : Blo 2035435 2035447 := bstep (se 1 (by rfl) ⟨1526585, by rfl⟩ : syracuseStep 2035447 = 3053171) B3053171
theorem B2173601 : Blo 2035435 2173601 := bbase (se 2 (by rfl) ⟨815100, by rfl⟩ : syracuseStep 2173601 = 1630201) (by norm_num)
theorem B5796269 : Blo 2035435 5796269 := bstep (se 3 (by rfl) ⟨1086800, by rfl⟩ : syracuseStep 5796269 = 2173601) B2173601
theorem B3864179 : Blo 2035435 3864179 := bstep (se 1 (by rfl) ⟨2898134, by rfl⟩ : syracuseStep 3864179 = 5796269) B5796269
theorem B2576119 : Blo 2035435 2576119 := bstep (se 1 (by rfl) ⟨1932089, by rfl⟩ : syracuseStep 2576119 = 3864179) B3864179
theorem B3434825 : Blo 2035435 3434825 := bstep (se 2 (by rfl) ⟨1288059, by rfl⟩ : syracuseStep 3434825 = 2576119) B2576119
theorem B2289883 : Blo 2035435 2289883 := bstep (se 1 (by rfl) ⟨1717412, by rfl⟩ : syracuseStep 2289883 = 3434825) B3434825
theorem B3053177 : Blo 2035435 3053177 := bstep (se 2 (by rfl) ⟨1144941, by rfl⟩ : syracuseStep 3053177 = 2289883) B2289883
theorem B2035451 : Blo 2035435 2035451 := bstep (se 1 (by rfl) ⟨1526588, by rfl⟩ : syracuseStep 2035451 = 3053177) B3053177
theorem B14116789 : Blo 2035435 14116789 := bbase (se 5 (by rfl) ⟨661724, by rfl⟩ : syracuseStep 14116789 = 1323449) (by norm_num)
theorem B18822385 : Blo 2035435 18822385 := bstep (se 2 (by rfl) ⟨7058394, by rfl⟩ : syracuseStep 18822385 = 14116789) B14116789
theorem B25096513 : Blo 2035435 25096513 := bstep (se 2 (by rfl) ⟨9411192, by rfl⟩ : syracuseStep 25096513 = 18822385) B18822385
theorem B33462017 : Blo 2035435 33462017 := bstep (se 2 (by rfl) ⟨12548256, by rfl⟩ : syracuseStep 33462017 = 25096513) B25096513
theorem B22308011 : Blo 2035435 22308011 := bstep (se 1 (by rfl) ⟨16731008, by rfl⟩ : syracuseStep 22308011 = 33462017) B33462017
theorem B14872007 : Blo 2035435 14872007 := bstep (se 1 (by rfl) ⟨11154005, by rfl⟩ : syracuseStep 14872007 = 22308011) B22308011
theorem B9914671 : Blo 2035435 9914671 := bstep (se 1 (by rfl) ⟨7436003, by rfl⟩ : syracuseStep 9914671 = 14872007) B14872007
theorem B13219561 : Blo 2035435 13219561 := bstep (se 2 (by rfl) ⟨4957335, by rfl⟩ : syracuseStep 13219561 = 9914671) B9914671
theorem B17626081 : Blo 2035435 17626081 := bstep (se 2 (by rfl) ⟨6609780, by rfl⟩ : syracuseStep 17626081 = 13219561) B13219561
theorem B23501441 : Blo 2035435 23501441 := bstep (se 2 (by rfl) ⟨8813040, by rfl⟩ : syracuseStep 23501441 = 17626081) B17626081
theorem B15667627 : Blo 2035435 15667627 := bstep (se 1 (by rfl) ⟨11750720, by rfl⟩ : syracuseStep 15667627 = 23501441) B23501441
theorem B20890169 : Blo 2035435 20890169 := bstep (se 2 (by rfl) ⟨7833813, by rfl⟩ : syracuseStep 20890169 = 15667627) B15667627
theorem B13926779 : Blo 2035435 13926779 := bstep (se 1 (by rfl) ⟨10445084, by rfl⟩ : syracuseStep 13926779 = 20890169) B20890169
theorem B9284519 : Blo 2035435 9284519 := bstep (se 1 (by rfl) ⟨6963389, by rfl⟩ : syracuseStep 9284519 = 13926779) B13926779
theorem B6189679 : Blo 2035435 6189679 := bstep (se 1 (by rfl) ⟨4642259, by rfl⟩ : syracuseStep 6189679 = 9284519) B9284519
theorem B33011621 : Blo 2035435 33011621 := bstep (se 4 (by rfl) ⟨3094839, by rfl⟩ : syracuseStep 33011621 = 6189679) B6189679
theorem B22007747 : Blo 2035435 22007747 := bstep (se 1 (by rfl) ⟨16505810, by rfl⟩ : syracuseStep 22007747 = 33011621) B33011621
theorem B58687325 : Blo 2035435 58687325 := bstep (se 3 (by rfl) ⟨11003873, by rfl⟩ : syracuseStep 58687325 = 22007747) B22007747
theorem B39124883 : Blo 2035435 39124883 := bstep (se 1 (by rfl) ⟨29343662, by rfl⟩ : syracuseStep 39124883 = 58687325) B58687325
theorem B26083255 : Blo 2035435 26083255 := bstep (se 1 (by rfl) ⟨19562441, by rfl⟩ : syracuseStep 26083255 = 39124883) B39124883
theorem B34777673 : Blo 2035435 34777673 := bstep (se 2 (by rfl) ⟨13041627, by rfl⟩ : syracuseStep 34777673 = 26083255) B26083255
theorem B23185115 : Blo 2035435 23185115 := bstep (se 1 (by rfl) ⟨17388836, by rfl⟩ : syracuseStep 23185115 = 34777673) B34777673
theorem B15456743 : Blo 2035435 15456743 := bstep (se 1 (by rfl) ⟨11592557, by rfl⟩ : syracuseStep 15456743 = 23185115) B23185115
theorem B10304495 : Blo 2035435 10304495 := bstep (se 1 (by rfl) ⟨7728371, by rfl⟩ : syracuseStep 10304495 = 15456743) B15456743
theorem B6869663 : Blo 2035435 6869663 := bstep (se 1 (by rfl) ⟨5152247, by rfl⟩ : syracuseStep 6869663 = 10304495) B10304495
theorem B4579775 : Blo 2035435 4579775 := bstep (se 1 (by rfl) ⟨3434831, by rfl⟩ : syracuseStep 4579775 = 6869663) B6869663
theorem B3053183 : Blo 2035435 3053183 := bstep (se 1 (by rfl) ⟨2289887, by rfl⟩ : syracuseStep 3053183 = 4579775) B4579775
theorem B2035455 : Blo 2035435 2035455 := bstep (se 1 (by rfl) ⟨1526591, by rfl⟩ : syracuseStep 2035455 = 3053183) B3053183
theorem B3053189 : Blo 2035435 3053189 := bbase (se 4 (by rfl) ⟨286236, by rfl⟩ : syracuseStep 3053189 = 572473) (by norm_num)
theorem B2035459 : Blo 2035435 2035459 := bstep (se 1 (by rfl) ⟨1526594, by rfl⟩ : syracuseStep 2035459 = 3053189) B3053189
theorem B3434845 : Blo 2035435 3434845 := bbase (se 3 (by rfl) ⟨644033, by rfl⟩ : syracuseStep 3434845 = 1288067) (by norm_num)
theorem B4579793 : Blo 2035435 4579793 := bstep (se 2 (by rfl) ⟨1717422, by rfl⟩ : syracuseStep 4579793 = 3434845) B3434845
theorem B3053195 : Blo 2035435 3053195 := bstep (se 1 (by rfl) ⟨2289896, by rfl⟩ : syracuseStep 3053195 = 4579793) B4579793
theorem B2035463 : Blo 2035435 2035463 := bstep (se 1 (by rfl) ⟨1526597, by rfl⟩ : syracuseStep 2035463 = 3053195) B3053195
theorem B2289901 : Blo 2035435 2289901 := bbase (se 3 (by rfl) ⟨429356, by rfl⟩ : syracuseStep 2289901 = 858713) (by norm_num)
theorem B3053201 : Blo 2035435 3053201 := bstep (se 2 (by rfl) ⟨1144950, by rfl⟩ : syracuseStep 3053201 = 2289901) B2289901
theorem B2035467 : Blo 2035435 2035467 := bstep (se 1 (by rfl) ⟨1526600, by rfl⟩ : syracuseStep 2035467 = 3053201) B3053201
theorem B6869717 : Blo 2035435 6869717 := bbase (se 7 (by rfl) ⟨80504, by rfl⟩ : syracuseStep 6869717 = 161009) (by norm_num)
theorem B4579811 : Blo 2035435 4579811 := bstep (se 1 (by rfl) ⟨3434858, by rfl⟩ : syracuseStep 4579811 = 6869717) B6869717
theorem B3053207 : Blo 2035435 3053207 := bstep (se 1 (by rfl) ⟨2289905, by rfl⟩ : syracuseStep 3053207 = 4579811) B4579811
theorem B2035471 : Blo 2035435 2035471 := bstep (se 1 (by rfl) ⟨1526603, by rfl⟩ : syracuseStep 2035471 = 3053207) B3053207
theorem B3053213 : Blo 2035435 3053213 := bbase (se 3 (by rfl) ⟨572477, by rfl⟩ : syracuseStep 3053213 = 1144955) (by norm_num)
theorem B2035475 : Blo 2035435 2035475 := bstep (se 1 (by rfl) ⟨1526606, by rfl⟩ : syracuseStep 2035475 = 3053213) B3053213
theorem B4579829 : Blo 2035435 4579829 := bbase (se 5 (by rfl) ⟨214679, by rfl⟩ : syracuseStep 4579829 = 429359) (by norm_num)
theorem B3053219 : Blo 2035435 3053219 := bstep (se 1 (by rfl) ⟨2289914, by rfl⟩ : syracuseStep 3053219 = 4579829) B4579829
theorem B2035479 : Blo 2035435 2035479 := bstep (se 1 (by rfl) ⟨1526609, by rfl⟩ : syracuseStep 2035479 = 3053219) B3053219
theorem B7833925 : Blo 2035435 7833925 := bbase (se 4 (by rfl) ⟨734430, by rfl⟩ : syracuseStep 7833925 = 1468861) (by norm_num)
theorem B10445233 : Blo 2035435 10445233 := bstep (se 2 (by rfl) ⟨3916962, by rfl⟩ : syracuseStep 10445233 = 7833925) B7833925
theorem B13926977 : Blo 2035435 13926977 := bstep (se 2 (by rfl) ⟨5222616, by rfl⟩ : syracuseStep 13926977 = 10445233) B10445233
theorem B9284651 : Blo 2035435 9284651 := bstep (se 1 (by rfl) ⟨6963488, by rfl⟩ : syracuseStep 9284651 = 13926977) B13926977
theorem B6189767 : Blo 2035435 6189767 := bstep (se 1 (by rfl) ⟨4642325, by rfl⟩ : syracuseStep 6189767 = 9284651) B9284651
theorem B4126511 : Blo 2035435 4126511 := bstep (se 1 (by rfl) ⟨3094883, by rfl⟩ : syracuseStep 4126511 = 6189767) B6189767
theorem B2751007 : Blo 2035435 2751007 := bstep (se 1 (by rfl) ⟨2063255, by rfl⟩ : syracuseStep 2751007 = 4126511) B4126511
theorem B3668009 : Blo 2035435 3668009 := bstep (se 2 (by rfl) ⟨1375503, by rfl⟩ : syracuseStep 3668009 = 2751007) B2751007
theorem B39125429 : Blo 2035435 39125429 := bstep (se 5 (by rfl) ⟨1834004, by rfl⟩ : syracuseStep 39125429 = 3668009) B3668009
theorem B26083619 : Blo 2035435 26083619 := bstep (se 1 (by rfl) ⟨19562714, by rfl⟩ : syracuseStep 26083619 = 39125429) B39125429
theorem B17389079 : Blo 2035435 17389079 := bstep (se 1 (by rfl) ⟨13041809, by rfl⟩ : syracuseStep 17389079 = 26083619) B26083619
theorem B11592719 : Blo 2035435 11592719 := bstep (se 1 (by rfl) ⟨8694539, by rfl⟩ : syracuseStep 11592719 = 17389079) B17389079
theorem B7728479 : Blo 2035435 7728479 := bstep (se 1 (by rfl) ⟨5796359, by rfl⟩ : syracuseStep 7728479 = 11592719) B11592719
theorem B5152319 : Blo 2035435 5152319 := bstep (se 1 (by rfl) ⟨3864239, by rfl⟩ : syracuseStep 5152319 = 7728479) B7728479
theorem B3434879 : Blo 2035435 3434879 := bstep (se 1 (by rfl) ⟨2576159, by rfl⟩ : syracuseStep 3434879 = 5152319) B5152319
theorem B2289919 : Blo 2035435 2289919 := bstep (se 1 (by rfl) ⟨1717439, by rfl⟩ : syracuseStep 2289919 = 3434879) B3434879
theorem B3053225 : Blo 2035435 3053225 := bstep (se 2 (by rfl) ⟨1144959, by rfl⟩ : syracuseStep 3053225 = 2289919) B2289919
theorem B2035483 : Blo 2035435 2035483 := bstep (se 1 (by rfl) ⟨1526612, by rfl⟩ : syracuseStep 2035483 = 3053225) B3053225
theorem B2751013 : Blo 2035435 2751013 := bbase (se 4 (by rfl) ⟨257907, by rfl⟩ : syracuseStep 2751013 = 515815) (by norm_num)
theorem B3668017 : Blo 2035435 3668017 := bstep (se 2 (by rfl) ⟨1375506, by rfl⟩ : syracuseStep 3668017 = 2751013) B2751013
theorem B4890689 : Blo 2035435 4890689 := bstep (se 2 (by rfl) ⟨1834008, by rfl⟩ : syracuseStep 4890689 = 3668017) B3668017
theorem B3260459 : Blo 2035435 3260459 := bstep (se 1 (by rfl) ⟨2445344, by rfl⟩ : syracuseStep 3260459 = 4890689) B4890689
theorem B2173639 : Blo 2035435 2173639 := bstep (se 1 (by rfl) ⟨1630229, by rfl⟩ : syracuseStep 2173639 = 3260459) B3260459
theorem B2898185 : Blo 2035435 2898185 := bstep (se 2 (by rfl) ⟨1086819, by rfl⟩ : syracuseStep 2898185 = 2173639) B2173639
theorem B7728493 : Blo 2035435 7728493 := bstep (se 3 (by rfl) ⟨1449092, by rfl⟩ : syracuseStep 7728493 = 2898185) B2898185
theorem B10304657 : Blo 2035435 10304657 := bstep (se 2 (by rfl) ⟨3864246, by rfl⟩ : syracuseStep 10304657 = 7728493) B7728493
theorem B6869771 : Blo 2035435 6869771 := bstep (se 1 (by rfl) ⟨5152328, by rfl⟩ : syracuseStep 6869771 = 10304657) B10304657
theorem B4579847 : Blo 2035435 4579847 := bstep (se 1 (by rfl) ⟨3434885, by rfl⟩ : syracuseStep 4579847 = 6869771) B6869771
theorem B3053231 : Blo 2035435 3053231 := bstep (se 1 (by rfl) ⟨2289923, by rfl⟩ : syracuseStep 3053231 = 4579847) B4579847
theorem B2035487 : Blo 2035435 2035487 := bstep (se 1 (by rfl) ⟨1526615, by rfl⟩ : syracuseStep 2035487 = 3053231) B3053231
theorem B3053237 : Blo 2035435 3053237 := bbase (se 5 (by rfl) ⟨143120, by rfl⟩ : syracuseStep 3053237 = 286241) (by norm_num)
theorem B2035491 : Blo 2035435 2035491 := bstep (se 1 (by rfl) ⟨1526618, by rfl⟩ : syracuseStep 2035491 = 3053237) B3053237
theorem B5152349 : Blo 2035435 5152349 := bbase (se 3 (by rfl) ⟨966065, by rfl⟩ : syracuseStep 5152349 = 1932131) (by norm_num)
theorem B3434899 : Blo 2035435 3434899 := bstep (se 1 (by rfl) ⟨2576174, by rfl⟩ : syracuseStep 3434899 = 5152349) B5152349
theorem B4579865 : Blo 2035435 4579865 := bstep (se 2 (by rfl) ⟨1717449, by rfl⟩ : syracuseStep 4579865 = 3434899) B3434899
theorem B3053243 : Blo 2035435 3053243 := bstep (se 1 (by rfl) ⟨2289932, by rfl⟩ : syracuseStep 3053243 = 4579865) B4579865
theorem B2035495 : Blo 2035435 2035495 := bstep (se 1 (by rfl) ⟨1526621, by rfl⟩ : syracuseStep 2035495 = 3053243) B3053243
theorem B2289937 : Blo 2035435 2289937 := bbase (se 2 (by rfl) ⟨858726, by rfl⟩ : syracuseStep 2289937 = 1717453) (by norm_num)
theorem B3053249 : Blo 2035435 3053249 := bstep (se 2 (by rfl) ⟨1144968, by rfl⟩ : syracuseStep 3053249 = 2289937) B2289937
theorem B2035499 : Blo 2035435 2035499 := bstep (se 1 (by rfl) ⟨1526624, by rfl⟩ : syracuseStep 2035499 = 3053249) B3053249
theorem B3864277 : Blo 2035435 3864277 := bbase (se 7 (by rfl) ⟨45284, by rfl⟩ : syracuseStep 3864277 = 90569) (by norm_num)
theorem B5152369 : Blo 2035435 5152369 := bstep (se 2 (by rfl) ⟨1932138, by rfl⟩ : syracuseStep 5152369 = 3864277) B3864277
theorem B6869825 : Blo 2035435 6869825 := bstep (se 2 (by rfl) ⟨2576184, by rfl⟩ : syracuseStep 6869825 = 5152369) B5152369
theorem B4579883 : Blo 2035435 4579883 := bstep (se 1 (by rfl) ⟨3434912, by rfl⟩ : syracuseStep 4579883 = 6869825) B6869825
theorem B3053255 : Blo 2035435 3053255 := bstep (se 1 (by rfl) ⟨2289941, by rfl⟩ : syracuseStep 3053255 = 4579883) B4579883
theorem B2035503 : Blo 2035435 2035503 := bstep (se 1 (by rfl) ⟨1526627, by rfl⟩ : syracuseStep 2035503 = 3053255) B3053255
theorem B3053261 : Blo 2035435 3053261 := bbase (se 3 (by rfl) ⟨572486, by rfl⟩ : syracuseStep 3053261 = 1144973) (by norm_num)
theorem B2035507 : Blo 2035435 2035507 := bstep (se 1 (by rfl) ⟨1526630, by rfl⟩ : syracuseStep 2035507 = 3053261) B3053261
theorem B4579901 : Blo 2035435 4579901 := bbase (se 3 (by rfl) ⟨858731, by rfl⟩ : syracuseStep 4579901 = 1717463) (by norm_num)
theorem B3053267 : Blo 2035435 3053267 := bstep (se 1 (by rfl) ⟨2289950, by rfl⟩ : syracuseStep 3053267 = 4579901) B4579901
theorem B2035511 : Blo 2035435 2035511 := bstep (se 1 (by rfl) ⟨1526633, by rfl⟩ : syracuseStep 2035511 = 3053267) B3053267
theorem B3434933 : Blo 2035435 3434933 := bbase (se 5 (by rfl) ⟨161012, by rfl⟩ : syracuseStep 3434933 = 322025) (by norm_num)
theorem B2289955 : Blo 2035435 2289955 := bstep (se 1 (by rfl) ⟨1717466, by rfl⟩ : syracuseStep 2289955 = 3434933) B3434933
theorem B3053273 : Blo 2035435 3053273 := bstep (se 2 (by rfl) ⟨1144977, by rfl⟩ : syracuseStep 3053273 = 2289955) B2289955
theorem B2035515 : Blo 2035435 2035515 := bstep (se 1 (by rfl) ⟨1526636, by rfl⟩ : syracuseStep 2035515 = 3053273) B3053273
theorem B2173673 : Blo 2035435 2173673 := bbase (se 2 (by rfl) ⟨815127, by rfl⟩ : syracuseStep 2173673 = 1630255) (by norm_num)
theorem B5796461 : Blo 2035435 5796461 := bstep (se 3 (by rfl) ⟨1086836, by rfl⟩ : syracuseStep 5796461 = 2173673) B2173673
theorem B15457229 : Blo 2035435 15457229 := bstep (se 3 (by rfl) ⟨2898230, by rfl⟩ : syracuseStep 15457229 = 5796461) B5796461
theorem B10304819 : Blo 2035435 10304819 := bstep (se 1 (by rfl) ⟨7728614, by rfl⟩ : syracuseStep 10304819 = 15457229) B15457229
theorem B6869879 : Blo 2035435 6869879 := bstep (se 1 (by rfl) ⟨5152409, by rfl⟩ : syracuseStep 6869879 = 10304819) B10304819
theorem B4579919 : Blo 2035435 4579919 := bstep (se 1 (by rfl) ⟨3434939, by rfl⟩ : syracuseStep 4579919 = 6869879) B6869879
theorem B3053279 : Blo 2035435 3053279 := bstep (se 1 (by rfl) ⟨2289959, by rfl⟩ : syracuseStep 3053279 = 4579919) B4579919
theorem B2035519 : Blo 2035435 2035519 := bstep (se 1 (by rfl) ⟨1526639, by rfl⟩ : syracuseStep 2035519 = 3053279) B3053279
theorem B3053285 : Blo 2035435 3053285 := bbase (se 4 (by rfl) ⟨286245, by rfl⟩ : syracuseStep 3053285 = 572491) (by norm_num)
theorem B2035523 : Blo 2035435 2035523 := bstep (se 1 (by rfl) ⟨1526642, by rfl⟩ : syracuseStep 2035523 = 3053285) B3053285
theorem B5796485 : Blo 2035435 5796485 := bbase (se 4 (by rfl) ⟨543420, by rfl⟩ : syracuseStep 5796485 = 1086841) (by norm_num)
theorem B3864323 : Blo 2035435 3864323 := bstep (se 1 (by rfl) ⟨2898242, by rfl⟩ : syracuseStep 3864323 = 5796485) B5796485
theorem B2576215 : Blo 2035435 2576215 := bstep (se 1 (by rfl) ⟨1932161, by rfl⟩ : syracuseStep 2576215 = 3864323) B3864323
theorem B3434953 : Blo 2035435 3434953 := bstep (se 2 (by rfl) ⟨1288107, by rfl⟩ : syracuseStep 3434953 = 2576215) B2576215
theorem B4579937 : Blo 2035435 4579937 := bstep (se 2 (by rfl) ⟨1717476, by rfl⟩ : syracuseStep 4579937 = 3434953) B3434953
theorem B3053291 : Blo 2035435 3053291 := bstep (se 1 (by rfl) ⟨2289968, by rfl⟩ : syracuseStep 3053291 = 4579937) B4579937
theorem B2035527 : Blo 2035435 2035527 := bstep (se 1 (by rfl) ⟨1526645, by rfl⟩ : syracuseStep 2035527 = 3053291) B3053291
theorem B2289973 : Blo 2035435 2289973 := bbase (se 5 (by rfl) ⟨107342, by rfl⟩ : syracuseStep 2289973 = 214685) (by norm_num)
theorem B3053297 : Blo 2035435 3053297 := bstep (se 2 (by rfl) ⟨1144986, by rfl⟩ : syracuseStep 3053297 = 2289973) B2289973
theorem B2035531 : Blo 2035435 2035531 := bstep (se 1 (by rfl) ⟨1526648, by rfl⟩ : syracuseStep 2035531 = 3053297) B3053297
theorem B2576225 : Blo 2035435 2576225 := bbase (se 2 (by rfl) ⟨966084, by rfl⟩ : syracuseStep 2576225 = 1932169) (by norm_num)
theorem B6869933 : Blo 2035435 6869933 := bstep (se 3 (by rfl) ⟨1288112, by rfl⟩ : syracuseStep 6869933 = 2576225) B2576225
theorem B4579955 : Blo 2035435 4579955 := bstep (se 1 (by rfl) ⟨3434966, by rfl⟩ : syracuseStep 4579955 = 6869933) B6869933
theorem B3053303 : Blo 2035435 3053303 := bstep (se 1 (by rfl) ⟨2289977, by rfl⟩ : syracuseStep 3053303 = 4579955) B4579955
theorem B2035535 : Blo 2035435 2035535 := bstep (se 1 (by rfl) ⟨1526651, by rfl⟩ : syracuseStep 2035535 = 3053303) B3053303
theorem B3053309 : Blo 2035435 3053309 := bbase (se 3 (by rfl) ⟨572495, by rfl⟩ : syracuseStep 3053309 = 1144991) (by norm_num)
theorem B2035539 : Blo 2035435 2035539 := bstep (se 1 (by rfl) ⟨1526654, by rfl⟩ : syracuseStep 2035539 = 3053309) B3053309
theorem B4579973 : Blo 2035435 4579973 := bbase (se 4 (by rfl) ⟨429372, by rfl⟩ : syracuseStep 4579973 = 858745) (by norm_num)
theorem B3053315 : Blo 2035435 3053315 := bstep (se 1 (by rfl) ⟨2289986, by rfl⟩ : syracuseStep 3053315 = 4579973) B4579973
theorem B2035543 : Blo 2035435 2035543 := bstep (se 1 (by rfl) ⟨1526657, by rfl⟩ : syracuseStep 2035543 = 3053315) B3053315
theorem B14672501 : Blo 2035435 14672501 := bbase (se 5 (by rfl) ⟨687773, by rfl⟩ : syracuseStep 14672501 = 1375547) (by norm_num)
theorem B9781667 : Blo 2035435 9781667 := bstep (se 1 (by rfl) ⟨7336250, by rfl⟩ : syracuseStep 9781667 = 14672501) B14672501
theorem B6521111 : Blo 2035435 6521111 := bstep (se 1 (by rfl) ⟨4890833, by rfl⟩ : syracuseStep 6521111 = 9781667) B9781667
theorem B4347407 : Blo 2035435 4347407 := bstep (se 1 (by rfl) ⟨3260555, by rfl⟩ : syracuseStep 4347407 = 6521111) B6521111
theorem B2898271 : Blo 2035435 2898271 := bstep (se 1 (by rfl) ⟨2173703, by rfl⟩ : syracuseStep 2898271 = 4347407) B4347407
theorem B3864361 : Blo 2035435 3864361 := bstep (se 2 (by rfl) ⟨1449135, by rfl⟩ : syracuseStep 3864361 = 2898271) B2898271
theorem B5152481 : Blo 2035435 5152481 := bstep (se 2 (by rfl) ⟨1932180, by rfl⟩ : syracuseStep 5152481 = 3864361) B3864361
theorem B3434987 : Blo 2035435 3434987 := bstep (se 1 (by rfl) ⟨2576240, by rfl⟩ : syracuseStep 3434987 = 5152481) B5152481
theorem B2289991 : Blo 2035435 2289991 := bstep (se 1 (by rfl) ⟨1717493, by rfl⟩ : syracuseStep 2289991 = 3434987) B3434987
theorem B3053321 : Blo 2035435 3053321 := bstep (se 2 (by rfl) ⟨1144995, by rfl⟩ : syracuseStep 3053321 = 2289991) B2289991
theorem B2035547 : Blo 2035435 2035547 := bstep (se 1 (by rfl) ⟨1526660, by rfl⟩ : syracuseStep 2035547 = 3053321) B3053321
theorem B10304981 : Blo 2035435 10304981 := bbase (se 7 (by rfl) ⟨120761, by rfl⟩ : syracuseStep 10304981 = 241523) (by norm_num)
theorem B6869987 : Blo 2035435 6869987 := bstep (se 1 (by rfl) ⟨5152490, by rfl⟩ : syracuseStep 6869987 = 10304981) B10304981
theorem B4579991 : Blo 2035435 4579991 := bstep (se 1 (by rfl) ⟨3434993, by rfl⟩ : syracuseStep 4579991 = 6869987) B6869987
theorem B3053327 : Blo 2035435 3053327 := bstep (se 1 (by rfl) ⟨2289995, by rfl⟩ : syracuseStep 3053327 = 4579991) B4579991
theorem B2035551 : Blo 2035435 2035551 := bstep (se 1 (by rfl) ⟨1526663, by rfl⟩ : syracuseStep 2035551 = 3053327) B3053327
theorem B3053333 : Blo 2035435 3053333 := bbase (se 6 (by rfl) ⟨71562, by rfl⟩ : syracuseStep 3053333 = 143125) (by norm_num)
theorem B2035555 : Blo 2035435 2035555 := bstep (se 1 (by rfl) ⟨1526666, by rfl⟩ : syracuseStep 2035555 = 3053333) B3053333
theorem B3018541 : Blo 2035435 3018541 := bbase (se 3 (by rfl) ⟨565976, by rfl⟩ : syracuseStep 3018541 = 1131953) (by norm_num)
theorem B4024721 : Blo 2035435 4024721 := bstep (se 2 (by rfl) ⟨1509270, by rfl⟩ : syracuseStep 4024721 = 3018541) B3018541
theorem B10732589 : Blo 2035435 10732589 := bstep (se 3 (by rfl) ⟨2012360, by rfl⟩ : syracuseStep 10732589 = 4024721) B4024721
theorem B7155059 : Blo 2035435 7155059 := bstep (se 1 (by rfl) ⟨5366294, by rfl⟩ : syracuseStep 7155059 = 10732589) B10732589
theorem B76320629 : Blo 2035435 76320629 := bstep (se 5 (by rfl) ⟨3577529, by rfl⟩ : syracuseStep 76320629 = 7155059) B7155059
theorem B50880419 : Blo 2035435 50880419 := bstep (se 1 (by rfl) ⟨38160314, by rfl⟩ : syracuseStep 50880419 = 76320629) B76320629
theorem B33920279 : Blo 2035435 33920279 := bstep (se 1 (by rfl) ⟨25440209, by rfl⟩ : syracuseStep 33920279 = 50880419) B50880419
theorem B22613519 : Blo 2035435 22613519 := bstep (se 1 (by rfl) ⟨16960139, by rfl⟩ : syracuseStep 22613519 = 33920279) B33920279
theorem B60302717 : Blo 2035435 60302717 := bstep (se 3 (by rfl) ⟨11306759, by rfl⟩ : syracuseStep 60302717 = 22613519) B22613519
theorem B40201811 : Blo 2035435 40201811 := bstep (se 1 (by rfl) ⟨30151358, by rfl⟩ : syracuseStep 40201811 = 60302717) B60302717
theorem B26801207 : Blo 2035435 26801207 := bstep (se 1 (by rfl) ⟨20100905, by rfl⟩ : syracuseStep 26801207 = 40201811) B40201811
theorem B17867471 : Blo 2035435 17867471 := bstep (se 1 (by rfl) ⟨13400603, by rfl⟩ : syracuseStep 17867471 = 26801207) B26801207
theorem B190586357 : Blo 2035435 190586357 := bstep (se 5 (by rfl) ⟨8933735, by rfl⟩ : syracuseStep 190586357 = 17867471) B17867471
theorem B127057571 : Blo 2035435 127057571 := bstep (se 1 (by rfl) ⟨95293178, by rfl⟩ : syracuseStep 127057571 = 190586357) B190586357
theorem B84705047 : Blo 2035435 84705047 := bstep (se 1 (by rfl) ⟨63528785, by rfl⟩ : syracuseStep 84705047 = 127057571) B127057571
theorem B56470031 : Blo 2035435 56470031 := bstep (se 1 (by rfl) ⟨42352523, by rfl⟩ : syracuseStep 56470031 = 84705047) B84705047
theorem B37646687 : Blo 2035435 37646687 := bstep (se 1 (by rfl) ⟨28235015, by rfl⟩ : syracuseStep 37646687 = 56470031) B56470031
theorem B100391165 : Blo 2035435 100391165 := bstep (se 3 (by rfl) ⟨18823343, by rfl⟩ : syracuseStep 100391165 = 37646687) B37646687
theorem B66927443 : Blo 2035435 66927443 := bstep (se 1 (by rfl) ⟨50195582, by rfl⟩ : syracuseStep 66927443 = 100391165) B100391165
theorem B178473181 : Blo 2035435 178473181 := bstep (se 3 (by rfl) ⟨33463721, by rfl⟩ : syracuseStep 178473181 = 66927443) B66927443
theorem B237964241 : Blo 2035435 237964241 := bstep (se 2 (by rfl) ⟨89236590, by rfl⟩ : syracuseStep 237964241 = 178473181) B178473181
theorem B634571309 : Blo 2035435 634571309 := bstep (se 3 (by rfl) ⟨118982120, by rfl⟩ : syracuseStep 634571309 = 237964241) B237964241
theorem B423047539 : Blo 2035435 423047539 := bstep (se 1 (by rfl) ⟨317285654, by rfl⟩ : syracuseStep 423047539 = 634571309) B634571309
theorem B564063385 : Blo 2035435 564063385 := bstep (se 2 (by rfl) ⟨211523769, by rfl⟩ : syracuseStep 564063385 = 423047539) B423047539
theorem B752084513 : Blo 2035435 752084513 := bstep (se 2 (by rfl) ⟨282031692, by rfl⟩ : syracuseStep 752084513 = 564063385) B564063385
theorem B501389675 : Blo 2035435 501389675 := bstep (se 1 (by rfl) ⟨376042256, by rfl⟩ : syracuseStep 501389675 = 752084513) B752084513
theorem B334259783 : Blo 2035435 334259783 := bstep (se 1 (by rfl) ⟨250694837, by rfl⟩ : syracuseStep 334259783 = 501389675) B501389675
theorem B222839855 : Blo 2035435 222839855 := bstep (se 1 (by rfl) ⟨167129891, by rfl⟩ : syracuseStep 222839855 = 334259783) B334259783
theorem B148559903 : Blo 2035435 148559903 := bstep (se 1 (by rfl) ⟨111419927, by rfl⟩ : syracuseStep 148559903 = 222839855) B222839855
theorem B99039935 : Blo 2035435 99039935 := bstep (se 1 (by rfl) ⟨74279951, by rfl⟩ : syracuseStep 99039935 = 148559903) B148559903
theorem B66026623 : Blo 2035435 66026623 := bstep (se 1 (by rfl) ⟨49519967, by rfl⟩ : syracuseStep 66026623 = 99039935) B99039935
theorem B88035497 : Blo 2035435 88035497 := bstep (se 2 (by rfl) ⟨33013311, by rfl⟩ : syracuseStep 88035497 = 66026623) B66026623
theorem B58690331 : Blo 2035435 58690331 := bstep (se 1 (by rfl) ⟨44017748, by rfl⟩ : syracuseStep 58690331 = 88035497) B88035497
theorem B39126887 : Blo 2035435 39126887 := bstep (se 1 (by rfl) ⟨29345165, by rfl⟩ : syracuseStep 39126887 = 58690331) B58690331
theorem B26084591 : Blo 2035435 26084591 := bstep (se 1 (by rfl) ⟨19563443, by rfl⟩ : syracuseStep 26084591 = 39126887) B39126887
theorem B17389727 : Blo 2035435 17389727 := bstep (se 1 (by rfl) ⟨13042295, by rfl⟩ : syracuseStep 17389727 = 26084591) B26084591
theorem B11593151 : Blo 2035435 11593151 := bstep (se 1 (by rfl) ⟨8694863, by rfl⟩ : syracuseStep 11593151 = 17389727) B17389727
theorem B7728767 : Blo 2035435 7728767 := bstep (se 1 (by rfl) ⟨5796575, by rfl⟩ : syracuseStep 7728767 = 11593151) B11593151
theorem B5152511 : Blo 2035435 5152511 := bstep (se 1 (by rfl) ⟨3864383, by rfl⟩ : syracuseStep 5152511 = 7728767) B7728767
theorem B3435007 : Blo 2035435 3435007 := bstep (se 1 (by rfl) ⟨2576255, by rfl⟩ : syracuseStep 3435007 = 5152511) B5152511
theorem B4580009 : Blo 2035435 4580009 := bstep (se 2 (by rfl) ⟨1717503, by rfl⟩ : syracuseStep 4580009 = 3435007) B3435007
theorem B3053339 : Blo 2035435 3053339 := bstep (se 1 (by rfl) ⟨2290004, by rfl⟩ : syracuseStep 3053339 = 4580009) B4580009
theorem B2035559 : Blo 2035435 2035559 := bstep (se 1 (by rfl) ⟨1526669, by rfl⟩ : syracuseStep 2035559 = 3053339) B3053339
theorem B2290009 : Blo 2035435 2290009 := bbase (se 2 (by rfl) ⟨858753, by rfl⟩ : syracuseStep 2290009 = 1717507) (by norm_num)
theorem B3053345 : Blo 2035435 3053345 := bstep (se 2 (by rfl) ⟨1145004, by rfl⟩ : syracuseStep 3053345 = 2290009) B2290009
theorem B2035563 : Blo 2035435 2035563 := bstep (se 1 (by rfl) ⟨1526672, by rfl⟩ : syracuseStep 2035563 = 3053345) B3053345
theorem B2063341 : Blo 2035435 2063341 := bbase (se 3 (by rfl) ⟨386876, by rfl⟩ : syracuseStep 2063341 = 773753) (by norm_num)
theorem B2751121 : Blo 2035435 2751121 := bstep (se 2 (by rfl) ⟨1031670, by rfl⟩ : syracuseStep 2751121 = 2063341) B2063341
theorem B3668161 : Blo 2035435 3668161 := bstep (se 2 (by rfl) ⟨1375560, by rfl⟩ : syracuseStep 3668161 = 2751121) B2751121
theorem B4890881 : Blo 2035435 4890881 := bstep (se 2 (by rfl) ⟨1834080, by rfl⟩ : syracuseStep 4890881 = 3668161) B3668161
theorem B3260587 : Blo 2035435 3260587 := bstep (se 1 (by rfl) ⟨2445440, by rfl⟩ : syracuseStep 3260587 = 4890881) B4890881
theorem B4347449 : Blo 2035435 4347449 := bstep (se 2 (by rfl) ⟨1630293, by rfl⟩ : syracuseStep 4347449 = 3260587) B3260587
theorem B2898299 : Blo 2035435 2898299 := bstep (se 1 (by rfl) ⟨2173724, by rfl⟩ : syracuseStep 2898299 = 4347449) B4347449
theorem B7728797 : Blo 2035435 7728797 := bstep (se 3 (by rfl) ⟨1449149, by rfl⟩ : syracuseStep 7728797 = 2898299) B2898299
theorem B5152531 : Blo 2035435 5152531 := bstep (se 1 (by rfl) ⟨3864398, by rfl⟩ : syracuseStep 5152531 = 7728797) B7728797
theorem B6870041 : Blo 2035435 6870041 := bstep (se 2 (by rfl) ⟨2576265, by rfl⟩ : syracuseStep 6870041 = 5152531) B5152531
theorem B4580027 : Blo 2035435 4580027 := bstep (se 1 (by rfl) ⟨3435020, by rfl⟩ : syracuseStep 4580027 = 6870041) B6870041
theorem B3053351 : Blo 2035435 3053351 := bstep (se 1 (by rfl) ⟨2290013, by rfl⟩ : syracuseStep 3053351 = 4580027) B4580027
theorem B2035567 : Blo 2035435 2035567 := bstep (se 1 (by rfl) ⟨1526675, by rfl⟩ : syracuseStep 2035567 = 3053351) B3053351
theorem B3053357 : Blo 2035435 3053357 := bbase (se 3 (by rfl) ⟨572504, by rfl⟩ : syracuseStep 3053357 = 1145009) (by norm_num)
theorem B2035571 : Blo 2035435 2035571 := bstep (se 1 (by rfl) ⟨1526678, by rfl⟩ : syracuseStep 2035571 = 3053357) B3053357
theorem B4580045 : Blo 2035435 4580045 := bbase (se 3 (by rfl) ⟨858758, by rfl⟩ : syracuseStep 4580045 = 1717517) (by norm_num)
theorem B3053363 : Blo 2035435 3053363 := bstep (se 1 (by rfl) ⟨2290022, by rfl⟩ : syracuseStep 3053363 = 4580045) B4580045
theorem B2035575 : Blo 2035435 2035575 := bstep (se 1 (by rfl) ⟨1526681, by rfl⟩ : syracuseStep 2035575 = 3053363) B3053363
theorem B2576281 : Blo 2035435 2576281 := bbase (se 2 (by rfl) ⟨966105, by rfl⟩ : syracuseStep 2576281 = 1932211) (by norm_num)
theorem B3435041 : Blo 2035435 3435041 := bstep (se 2 (by rfl) ⟨1288140, by rfl⟩ : syracuseStep 3435041 = 2576281) B2576281
theorem B2290027 : Blo 2035435 2290027 := bstep (se 1 (by rfl) ⟨1717520, by rfl⟩ : syracuseStep 2290027 = 3435041) B3435041
theorem B3053369 : Blo 2035435 3053369 := bstep (se 2 (by rfl) ⟨1145013, by rfl⟩ : syracuseStep 3053369 = 2290027) B2290027
theorem B2035579 : Blo 2035435 2035579 := bstep (se 1 (by rfl) ⟨1526684, by rfl⟩ : syracuseStep 2035579 = 3053369) B3053369
theorem B8694965 : Blo 2035435 8694965 := bbase (se 5 (by rfl) ⟨407576, by rfl⟩ : syracuseStep 8694965 = 815153) (by norm_num)
theorem B23186573 : Blo 2035435 23186573 := bstep (se 3 (by rfl) ⟨4347482, by rfl⟩ : syracuseStep 23186573 = 8694965) B8694965
theorem B15457715 : Blo 2035435 15457715 := bstep (se 1 (by rfl) ⟨11593286, by rfl⟩ : syracuseStep 15457715 = 23186573) B23186573
theorem B10305143 : Blo 2035435 10305143 := bstep (se 1 (by rfl) ⟨7728857, by rfl⟩ : syracuseStep 10305143 = 15457715) B15457715
theorem B6870095 : Blo 2035435 6870095 := bstep (se 1 (by rfl) ⟨5152571, by rfl⟩ : syracuseStep 6870095 = 10305143) B10305143
theorem B4580063 : Blo 2035435 4580063 := bstep (se 1 (by rfl) ⟨3435047, by rfl⟩ : syracuseStep 4580063 = 6870095) B6870095
theorem B3053375 : Blo 2035435 3053375 := bstep (se 1 (by rfl) ⟨2290031, by rfl⟩ : syracuseStep 3053375 = 4580063) B4580063
theorem B2035583 : Blo 2035435 2035583 := bstep (se 1 (by rfl) ⟨1526687, by rfl⟩ : syracuseStep 2035583 = 3053375) B3053375
theorem B3053381 : Blo 2035435 3053381 := bbase (se 4 (by rfl) ⟨286254, by rfl⟩ : syracuseStep 3053381 = 572509) (by norm_num)
theorem B2035587 : Blo 2035435 2035587 := bstep (se 1 (by rfl) ⟨1526690, by rfl⟩ : syracuseStep 2035587 = 3053381) B3053381
theorem B3435061 : Blo 2035435 3435061 := bbase (se 5 (by rfl) ⟨161018, by rfl⟩ : syracuseStep 3435061 = 322037) (by norm_num)
theorem B4580081 : Blo 2035435 4580081 := bstep (se 2 (by rfl) ⟨1717530, by rfl⟩ : syracuseStep 4580081 = 3435061) B3435061
theorem B3053387 : Blo 2035435 3053387 := bstep (se 1 (by rfl) ⟨2290040, by rfl⟩ : syracuseStep 3053387 = 4580081) B4580081
theorem B2035591 : Blo 2035435 2035591 := bstep (se 1 (by rfl) ⟨1526693, by rfl⟩ : syracuseStep 2035591 = 3053387) B3053387
theorem B2290045 : Blo 2035435 2290045 := bbase (se 3 (by rfl) ⟨429383, by rfl⟩ : syracuseStep 2290045 = 858767) (by norm_num)
theorem B3053393 : Blo 2035435 3053393 := bstep (se 2 (by rfl) ⟨1145022, by rfl⟩ : syracuseStep 3053393 = 2290045) B2290045
theorem B2035595 : Blo 2035435 2035595 := bstep (se 1 (by rfl) ⟨1526696, by rfl⟩ : syracuseStep 2035595 = 3053393) B3053393
theorem B6870149 : Blo 2035435 6870149 := bbase (se 4 (by rfl) ⟨644076, by rfl⟩ : syracuseStep 6870149 = 1288153) (by norm_num)
theorem B4580099 : Blo 2035435 4580099 := bstep (se 1 (by rfl) ⟨3435074, by rfl⟩ : syracuseStep 4580099 = 6870149) B6870149
theorem B3053399 : Blo 2035435 3053399 := bstep (se 1 (by rfl) ⟨2290049, by rfl⟩ : syracuseStep 3053399 = 4580099) B4580099
theorem B2035599 : Blo 2035435 2035599 := bstep (se 1 (by rfl) ⟨1526699, by rfl⟩ : syracuseStep 2035599 = 3053399) B3053399
theorem B3053405 : Blo 2035435 3053405 := bbase (se 3 (by rfl) ⟨572513, by rfl⟩ : syracuseStep 3053405 = 1145027) (by norm_num)
theorem B2035603 : Blo 2035435 2035603 := bstep (se 1 (by rfl) ⟨1526702, by rfl⟩ : syracuseStep 2035603 = 3053405) B3053405
theorem B4580117 : Blo 2035435 4580117 := bbase (se 6 (by rfl) ⟨107346, by rfl⟩ : syracuseStep 4580117 = 214693) (by norm_num)
theorem B3053411 : Blo 2035435 3053411 := bstep (se 1 (by rfl) ⟨2290058, by rfl⟩ : syracuseStep 3053411 = 4580117) B4580117
theorem B2035607 : Blo 2035435 2035607 := bstep (se 1 (by rfl) ⟨1526705, by rfl⟩ : syracuseStep 2035607 = 3053411) B3053411
theorem B7728965 : Blo 2035435 7728965 := bbase (se 4 (by rfl) ⟨724590, by rfl⟩ : syracuseStep 7728965 = 1449181) (by norm_num)
theorem B5152643 : Blo 2035435 5152643 := bstep (se 1 (by rfl) ⟨3864482, by rfl⟩ : syracuseStep 5152643 = 7728965) B7728965
theorem B3435095 : Blo 2035435 3435095 := bstep (se 1 (by rfl) ⟨2576321, by rfl⟩ : syracuseStep 3435095 = 5152643) B5152643
theorem B2290063 : Blo 2035435 2290063 := bstep (se 1 (by rfl) ⟨1717547, by rfl⟩ : syracuseStep 2290063 = 3435095) B3435095
theorem B3053417 : Blo 2035435 3053417 := bstep (se 2 (by rfl) ⟨1145031, by rfl⟩ : syracuseStep 3053417 = 2290063) B2290063
theorem B2035611 : Blo 2035435 2035611 := bstep (se 1 (by rfl) ⟨1526708, by rfl⟩ : syracuseStep 2035611 = 3053417) B3053417
theorem B8366165 : Blo 2035435 8366165 := bbase (se 8 (by rfl) ⟨49020, by rfl⟩ : syracuseStep 8366165 = 98041) (by norm_num)
theorem B5577443 : Blo 2035435 5577443 := bstep (se 1 (by rfl) ⟨4183082, by rfl⟩ : syracuseStep 5577443 = 8366165) B8366165
theorem B3718295 : Blo 2035435 3718295 := bstep (se 1 (by rfl) ⟨2788721, by rfl⟩ : syracuseStep 3718295 = 5577443) B5577443
theorem B2478863 : Blo 2035435 2478863 := bstep (se 1 (by rfl) ⟨1859147, by rfl⟩ : syracuseStep 2478863 = 3718295) B3718295
theorem B6610301 : Blo 2035435 6610301 := bstep (se 3 (by rfl) ⟨1239431, by rfl⟩ : syracuseStep 6610301 = 2478863) B2478863
theorem B4406867 : Blo 2035435 4406867 := bstep (se 1 (by rfl) ⟨3305150, by rfl⟩ : syracuseStep 4406867 = 6610301) B6610301
theorem B47006581 : Blo 2035435 47006581 := bstep (se 5 (by rfl) ⟨2203433, by rfl⟩ : syracuseStep 47006581 = 4406867) B4406867
theorem B62675441 : Blo 2035435 62675441 := bstep (se 2 (by rfl) ⟨23503290, by rfl⟩ : syracuseStep 62675441 = 47006581) B47006581
theorem B41783627 : Blo 2035435 41783627 := bstep (se 1 (by rfl) ⟨31337720, by rfl⟩ : syracuseStep 41783627 = 62675441) B62675441
theorem B27855751 : Blo 2035435 27855751 := bstep (se 1 (by rfl) ⟨20891813, by rfl⟩ : syracuseStep 27855751 = 41783627) B41783627
theorem B37141001 : Blo 2035435 37141001 := bstep (se 2 (by rfl) ⟨13927875, by rfl⟩ : syracuseStep 37141001 = 27855751) B27855751
theorem B24760667 : Blo 2035435 24760667 := bstep (se 1 (by rfl) ⟨18570500, by rfl⟩ : syracuseStep 24760667 = 37141001) B37141001
theorem B16507111 : Blo 2035435 16507111 := bstep (se 1 (by rfl) ⟨12380333, by rfl⟩ : syracuseStep 16507111 = 24760667) B24760667
theorem B22009481 : Blo 2035435 22009481 := bstep (se 2 (by rfl) ⟨8253555, by rfl⟩ : syracuseStep 22009481 = 16507111) B16507111
theorem B14672987 : Blo 2035435 14672987 := bstep (se 1 (by rfl) ⟨11004740, by rfl⟩ : syracuseStep 14672987 = 22009481) B22009481
theorem B9781991 : Blo 2035435 9781991 := bstep (se 1 (by rfl) ⟨7336493, by rfl⟩ : syracuseStep 9781991 = 14672987) B14672987
theorem B6521327 : Blo 2035435 6521327 := bstep (se 1 (by rfl) ⟨4890995, by rfl⟩ : syracuseStep 6521327 = 9781991) B9781991
theorem B4347551 : Blo 2035435 4347551 := bstep (se 1 (by rfl) ⟨3260663, by rfl⟩ : syracuseStep 4347551 = 6521327) B6521327
theorem B11593469 : Blo 2035435 11593469 := bstep (se 3 (by rfl) ⟨2173775, by rfl⟩ : syracuseStep 11593469 = 4347551) B4347551
theorem B7728979 : Blo 2035435 7728979 := bstep (se 1 (by rfl) ⟨5796734, by rfl⟩ : syracuseStep 7728979 = 11593469) B11593469
theorem B10305305 : Blo 2035435 10305305 := bstep (se 2 (by rfl) ⟨3864489, by rfl⟩ : syracuseStep 10305305 = 7728979) B7728979
theorem B6870203 : Blo 2035435 6870203 := bstep (se 1 (by rfl) ⟨5152652, by rfl⟩ : syracuseStep 6870203 = 10305305) B10305305
theorem B4580135 : Blo 2035435 4580135 := bstep (se 1 (by rfl) ⟨3435101, by rfl⟩ : syracuseStep 4580135 = 6870203) B6870203
theorem B3053423 : Blo 2035435 3053423 := bstep (se 1 (by rfl) ⟨2290067, by rfl⟩ : syracuseStep 3053423 = 4580135) B4580135
theorem B2035615 : Blo 2035435 2035615 := bstep (se 1 (by rfl) ⟨1526711, by rfl⟩ : syracuseStep 2035615 = 3053423) B3053423
theorem B3053429 : Blo 2035435 3053429 := bbase (se 5 (by rfl) ⟨143129, by rfl⟩ : syracuseStep 3053429 = 286259) (by norm_num)
theorem B2035619 : Blo 2035435 2035619 := bstep (se 1 (by rfl) ⟨1526714, by rfl⟩ : syracuseStep 2035619 = 3053429) B3053429
theorem B3260677 : Blo 2035435 3260677 := bbase (se 4 (by rfl) ⟨305688, by rfl⟩ : syracuseStep 3260677 = 611377) (by norm_num)
theorem B4347569 : Blo 2035435 4347569 := bstep (se 2 (by rfl) ⟨1630338, by rfl⟩ : syracuseStep 4347569 = 3260677) B3260677
theorem B2898379 : Blo 2035435 2898379 := bstep (se 1 (by rfl) ⟨2173784, by rfl⟩ : syracuseStep 2898379 = 4347569) B4347569
theorem B3864505 : Blo 2035435 3864505 := bstep (se 2 (by rfl) ⟨1449189, by rfl⟩ : syracuseStep 3864505 = 2898379) B2898379
theorem B5152673 : Blo 2035435 5152673 := bstep (se 2 (by rfl) ⟨1932252, by rfl⟩ : syracuseStep 5152673 = 3864505) B3864505
theorem B3435115 : Blo 2035435 3435115 := bstep (se 1 (by rfl) ⟨2576336, by rfl⟩ : syracuseStep 3435115 = 5152673) B5152673
theorem B4580153 : Blo 2035435 4580153 := bstep (se 2 (by rfl) ⟨1717557, by rfl⟩ : syracuseStep 4580153 = 3435115) B3435115
theorem B3053435 : Blo 2035435 3053435 := bstep (se 1 (by rfl) ⟨2290076, by rfl⟩ : syracuseStep 3053435 = 4580153) B4580153
theorem B2035623 : Blo 2035435 2035623 := bstep (se 1 (by rfl) ⟨1526717, by rfl⟩ : syracuseStep 2035623 = 3053435) B3053435
theorem B2290081 : Blo 2035435 2290081 := bbase (se 2 (by rfl) ⟨858780, by rfl⟩ : syracuseStep 2290081 = 1717561) (by norm_num)
theorem B3053441 : Blo 2035435 3053441 := bstep (se 2 (by rfl) ⟨1145040, by rfl⟩ : syracuseStep 3053441 = 2290081) B2290081
theorem B2035627 : Blo 2035435 2035627 := bstep (se 1 (by rfl) ⟨1526720, by rfl⟩ : syracuseStep 2035627 = 3053441) B3053441
theorem B5152693 : Blo 2035435 5152693 := bbase (se 5 (by rfl) ⟨241532, by rfl⟩ : syracuseStep 5152693 = 483065) (by norm_num)
theorem B6870257 : Blo 2035435 6870257 := bstep (se 2 (by rfl) ⟨2576346, by rfl⟩ : syracuseStep 6870257 = 5152693) B5152693
theorem B4580171 : Blo 2035435 4580171 := bstep (se 1 (by rfl) ⟨3435128, by rfl⟩ : syracuseStep 4580171 = 6870257) B6870257
theorem B3053447 : Blo 2035435 3053447 := bstep (se 1 (by rfl) ⟨2290085, by rfl⟩ : syracuseStep 3053447 = 4580171) B4580171
theorem B2035631 : Blo 2035435 2035631 := bstep (se 1 (by rfl) ⟨1526723, by rfl⟩ : syracuseStep 2035631 = 3053447) B3053447
theorem B3053453 : Blo 2035435 3053453 := bbase (se 3 (by rfl) ⟨572522, by rfl⟩ : syracuseStep 3053453 = 1145045) (by norm_num)
theorem B2035635 : Blo 2035435 2035635 := bstep (se 1 (by rfl) ⟨1526726, by rfl⟩ : syracuseStep 2035635 = 3053453) B3053453
theorem B4580189 : Blo 2035435 4580189 := bbase (se 3 (by rfl) ⟨858785, by rfl⟩ : syracuseStep 4580189 = 1717571) (by norm_num)
theorem B3053459 : Blo 2035435 3053459 := bstep (se 1 (by rfl) ⟨2290094, by rfl⟩ : syracuseStep 3053459 = 4580189) B4580189
theorem B2035639 : Blo 2035435 2035639 := bstep (se 1 (by rfl) ⟨1526729, by rfl⟩ : syracuseStep 2035639 = 3053459) B3053459
theorem B3435149 : Blo 2035435 3435149 := bbase (se 3 (by rfl) ⟨644090, by rfl⟩ : syracuseStep 3435149 = 1288181) (by norm_num)
theorem B2290099 : Blo 2035435 2290099 := bstep (se 1 (by rfl) ⟨1717574, by rfl⟩ : syracuseStep 2290099 = 3435149) B3435149
theorem B3053465 : Blo 2035435 3053465 := bstep (se 2 (by rfl) ⟨1145049, by rfl⟩ : syracuseStep 3053465 = 2290099) B2290099
theorem B2035643 : Blo 2035435 2035643 := bstep (se 1 (by rfl) ⟨1526732, by rfl⟩ : syracuseStep 2035643 = 3053465) B3053465
theorem B6521429 : Blo 2035435 6521429 := bbase (se 8 (by rfl) ⟨38211, by rfl⟩ : syracuseStep 6521429 = 76423) (by norm_num)
theorem B17390477 : Blo 2035435 17390477 := bstep (se 3 (by rfl) ⟨3260714, by rfl⟩ : syracuseStep 17390477 = 6521429) B6521429
theorem B11593651 : Blo 2035435 11593651 := bstep (se 1 (by rfl) ⟨8695238, by rfl⟩ : syracuseStep 11593651 = 17390477) B17390477
theorem B15458201 : Blo 2035435 15458201 := bstep (se 2 (by rfl) ⟨5796825, by rfl⟩ : syracuseStep 15458201 = 11593651) B11593651
theorem B10305467 : Blo 2035435 10305467 := bstep (se 1 (by rfl) ⟨7729100, by rfl⟩ : syracuseStep 10305467 = 15458201) B15458201
theorem B6870311 : Blo 2035435 6870311 := bstep (se 1 (by rfl) ⟨5152733, by rfl⟩ : syracuseStep 6870311 = 10305467) B10305467
theorem B4580207 : Blo 2035435 4580207 := bstep (se 1 (by rfl) ⟨3435155, by rfl⟩ : syracuseStep 4580207 = 6870311) B6870311
theorem B3053471 : Blo 2035435 3053471 := bstep (se 1 (by rfl) ⟨2290103, by rfl⟩ : syracuseStep 3053471 = 4580207) B4580207
theorem B2035647 : Blo 2035435 2035647 := bstep (se 1 (by rfl) ⟨1526735, by rfl⟩ : syracuseStep 2035647 = 3053471) B3053471
theorem B3053477 : Blo 2035435 3053477 := bbase (se 4 (by rfl) ⟨286263, by rfl⟩ : syracuseStep 3053477 = 572527) (by norm_num)
theorem B2035651 : Blo 2035435 2035651 := bstep (se 1 (by rfl) ⟨1526738, by rfl⟩ : syracuseStep 2035651 = 3053477) B3053477
theorem B2576377 : Blo 2035435 2576377 := bbase (se 2 (by rfl) ⟨966141, by rfl⟩ : syracuseStep 2576377 = 1932283) (by norm_num)
theorem B3435169 : Blo 2035435 3435169 := bstep (se 2 (by rfl) ⟨1288188, by rfl⟩ : syracuseStep 3435169 = 2576377) B2576377
theorem B4580225 : Blo 2035435 4580225 := bstep (se 2 (by rfl) ⟨1717584, by rfl⟩ : syracuseStep 4580225 = 3435169) B3435169
theorem B3053483 : Blo 2035435 3053483 := bstep (se 1 (by rfl) ⟨2290112, by rfl⟩ : syracuseStep 3053483 = 4580225) B4580225
theorem B2035655 : Blo 2035435 2035655 := bstep (se 1 (by rfl) ⟨1526741, by rfl⟩ : syracuseStep 2035655 = 3053483) B3053483
theorem B2290117 : Blo 2035435 2290117 := bbase (se 4 (by rfl) ⟨214698, by rfl⟩ : syracuseStep 2290117 = 429397) (by norm_num)
theorem B3053489 : Blo 2035435 3053489 := bstep (se 2 (by rfl) ⟨1145058, by rfl⟩ : syracuseStep 3053489 = 2290117) B2290117
theorem B2035659 : Blo 2035435 2035659 := bstep (se 1 (by rfl) ⟨1526744, by rfl⟩ : syracuseStep 2035659 = 3053489) B3053489
theorem B3864581 : Blo 2035435 3864581 := bbase (se 4 (by rfl) ⟨362304, by rfl⟩ : syracuseStep 3864581 = 724609) (by norm_num)
theorem B2576387 : Blo 2035435 2576387 := bstep (se 1 (by rfl) ⟨1932290, by rfl⟩ : syracuseStep 2576387 = 3864581) B3864581
theorem B6870365 : Blo 2035435 6870365 := bstep (se 3 (by rfl) ⟨1288193, by rfl⟩ : syracuseStep 6870365 = 2576387) B2576387
theorem B4580243 : Blo 2035435 4580243 := bstep (se 1 (by rfl) ⟨3435182, by rfl⟩ : syracuseStep 4580243 = 6870365) B6870365
theorem B3053495 : Blo 2035435 3053495 := bstep (se 1 (by rfl) ⟨2290121, by rfl⟩ : syracuseStep 3053495 = 4580243) B4580243
theorem B2035663 : Blo 2035435 2035663 := bstep (se 1 (by rfl) ⟨1526747, by rfl⟩ : syracuseStep 2035663 = 3053495) B3053495
theorem B3053501 : Blo 2035435 3053501 := bbase (se 3 (by rfl) ⟨572531, by rfl⟩ : syracuseStep 3053501 = 1145063) (by norm_num)
theorem B2035667 : Blo 2035435 2035667 := bstep (se 1 (by rfl) ⟨1526750, by rfl⟩ : syracuseStep 2035667 = 3053501) B3053501
theorem B4580261 : Blo 2035435 4580261 := bbase (se 4 (by rfl) ⟨429399, by rfl⟩ : syracuseStep 4580261 = 858799) (by norm_num)
theorem B3053507 : Blo 2035435 3053507 := bstep (se 1 (by rfl) ⟨2290130, by rfl⟩ : syracuseStep 3053507 = 4580261) B4580261
theorem B2035671 : Blo 2035435 2035671 := bstep (se 1 (by rfl) ⟨1526753, by rfl⟩ : syracuseStep 2035671 = 3053507) B3053507
theorem B5152805 : Blo 2035435 5152805 := bbase (se 4 (by rfl) ⟨483075, by rfl⟩ : syracuseStep 5152805 = 966151) (by norm_num)
theorem B3435203 : Blo 2035435 3435203 := bstep (se 1 (by rfl) ⟨2576402, by rfl⟩ : syracuseStep 3435203 = 5152805) B5152805
theorem B2290135 : Blo 2035435 2290135 := bstep (se 1 (by rfl) ⟨1717601, by rfl⟩ : syracuseStep 2290135 = 3435203) B3435203
theorem B3053513 : Blo 2035435 3053513 := bstep (se 2 (by rfl) ⟨1145067, by rfl⟩ : syracuseStep 3053513 = 2290135) B2290135
theorem B2035675 : Blo 2035435 2035675 := bstep (se 1 (by rfl) ⟨1526756, by rfl⟩ : syracuseStep 2035675 = 3053513) B3053513
theorem B5796917 : Blo 2035435 5796917 := bbase (se 5 (by rfl) ⟨271730, by rfl⟩ : syracuseStep 5796917 = 543461) (by norm_num)
theorem B3864611 : Blo 2035435 3864611 := bstep (se 1 (by rfl) ⟨2898458, by rfl⟩ : syracuseStep 3864611 = 5796917) B5796917
theorem B10305629 : Blo 2035435 10305629 := bstep (se 3 (by rfl) ⟨1932305, by rfl⟩ : syracuseStep 10305629 = 3864611) B3864611
theorem B6870419 : Blo 2035435 6870419 := bstep (se 1 (by rfl) ⟨5152814, by rfl⟩ : syracuseStep 6870419 = 10305629) B10305629
theorem B4580279 : Blo 2035435 4580279 := bstep (se 1 (by rfl) ⟨3435209, by rfl⟩ : syracuseStep 4580279 = 6870419) B6870419
theorem B3053519 : Blo 2035435 3053519 := bstep (se 1 (by rfl) ⟨2290139, by rfl⟩ : syracuseStep 3053519 = 4580279) B4580279
theorem B2035679 : Blo 2035435 2035679 := bstep (se 1 (by rfl) ⟨1526759, by rfl⟩ : syracuseStep 2035679 = 3053519) B3053519
theorem B3053525 : Blo 2035435 3053525 := bbase (se 7 (by rfl) ⟨35783, by rfl⟩ : syracuseStep 3053525 = 71567) (by norm_num)
theorem B2035683 : Blo 2035435 2035683 := bstep (se 1 (by rfl) ⟨1526762, by rfl⟩ : syracuseStep 2035683 = 3053525) B3053525
theorem B7729253 : Blo 2035435 7729253 := bbase (se 4 (by rfl) ⟨724617, by rfl⟩ : syracuseStep 7729253 = 1449235) (by norm_num)
theorem B5152835 : Blo 2035435 5152835 := bstep (se 1 (by rfl) ⟨3864626, by rfl⟩ : syracuseStep 5152835 = 7729253) B7729253
theorem B3435223 : Blo 2035435 3435223 := bstep (se 1 (by rfl) ⟨2576417, by rfl⟩ : syracuseStep 3435223 = 5152835) B5152835
theorem B4580297 : Blo 2035435 4580297 := bstep (se 2 (by rfl) ⟨1717611, by rfl⟩ : syracuseStep 4580297 = 3435223) B3435223
theorem B3053531 : Blo 2035435 3053531 := bstep (se 1 (by rfl) ⟨2290148, by rfl⟩ : syracuseStep 3053531 = 4580297) B4580297
theorem B2035687 : Blo 2035435 2035687 := bstep (se 1 (by rfl) ⟨1526765, by rfl⟩ : syracuseStep 2035687 = 3053531) B3053531
theorem B2290153 : Blo 2035435 2290153 := bbase (se 2 (by rfl) ⟨858807, by rfl⟩ : syracuseStep 2290153 = 1717615) (by norm_num)
theorem B3053537 : Blo 2035435 3053537 := bstep (se 2 (by rfl) ⟨1145076, by rfl⟩ : syracuseStep 3053537 = 2290153) B2290153
theorem B2035691 : Blo 2035435 2035691 := bstep (se 1 (by rfl) ⟨1526768, by rfl⟩ : syracuseStep 2035691 = 3053537) B3053537
theorem B2173861 : Blo 2035435 2173861 := bbase (se 4 (by rfl) ⟨203799, by rfl⟩ : syracuseStep 2173861 = 407599) (by norm_num)
theorem B11593925 : Blo 2035435 11593925 := bstep (se 4 (by rfl) ⟨1086930, by rfl⟩ : syracuseStep 11593925 = 2173861) B2173861
theorem B7729283 : Blo 2035435 7729283 := bstep (se 1 (by rfl) ⟨5796962, by rfl⟩ : syracuseStep 7729283 = 11593925) B11593925
theorem B5152855 : Blo 2035435 5152855 := bstep (se 1 (by rfl) ⟨3864641, by rfl⟩ : syracuseStep 5152855 = 7729283) B7729283
theorem B6870473 : Blo 2035435 6870473 := bstep (se 2 (by rfl) ⟨2576427, by rfl⟩ : syracuseStep 6870473 = 5152855) B5152855
theorem B4580315 : Blo 2035435 4580315 := bstep (se 1 (by rfl) ⟨3435236, by rfl⟩ : syracuseStep 4580315 = 6870473) B6870473
theorem B3053543 : Blo 2035435 3053543 := bstep (se 1 (by rfl) ⟨2290157, by rfl⟩ : syracuseStep 3053543 = 4580315) B4580315
theorem B2035695 : Blo 2035435 2035695 := bstep (se 1 (by rfl) ⟨1526771, by rfl⟩ : syracuseStep 2035695 = 3053543) B3053543
theorem B3053549 : Blo 2035435 3053549 := bbase (se 3 (by rfl) ⟨572540, by rfl⟩ : syracuseStep 3053549 = 1145081) (by norm_num)
theorem B2035699 : Blo 2035435 2035699 := bstep (se 1 (by rfl) ⟨1526774, by rfl⟩ : syracuseStep 2035699 = 3053549) B3053549
theorem B4580333 : Blo 2035435 4580333 := bbase (se 3 (by rfl) ⟨858812, by rfl⟩ : syracuseStep 4580333 = 1717625) (by norm_num)
theorem B3053555 : Blo 2035435 3053555 := bstep (se 1 (by rfl) ⟨2290166, by rfl⟩ : syracuseStep 3053555 = 4580333) B4580333
theorem B2035703 : Blo 2035435 2035703 := bstep (se 1 (by rfl) ⟨1526777, by rfl⟩ : syracuseStep 2035703 = 3053555) B3053555
theorem B4347749 : Blo 2035435 4347749 := bbase (se 4 (by rfl) ⟨407601, by rfl⟩ : syracuseStep 4347749 = 815203) (by norm_num)
theorem B2898499 : Blo 2035435 2898499 := bstep (se 1 (by rfl) ⟨2173874, by rfl⟩ : syracuseStep 2898499 = 4347749) B4347749
theorem B3864665 : Blo 2035435 3864665 := bstep (se 2 (by rfl) ⟨1449249, by rfl⟩ : syracuseStep 3864665 = 2898499) B2898499
theorem B2576443 : Blo 2035435 2576443 := bstep (se 1 (by rfl) ⟨1932332, by rfl⟩ : syracuseStep 2576443 = 3864665) B3864665
theorem B3435257 : Blo 2035435 3435257 := bstep (se 2 (by rfl) ⟨1288221, by rfl⟩ : syracuseStep 3435257 = 2576443) B2576443
theorem B2290171 : Blo 2035435 2290171 := bstep (se 1 (by rfl) ⟨1717628, by rfl⟩ : syracuseStep 2290171 = 3435257) B3435257
theorem B3053561 : Blo 2035435 3053561 := bstep (se 2 (by rfl) ⟨1145085, by rfl⟩ : syracuseStep 3053561 = 2290171) B2290171
theorem B2035707 : Blo 2035435 2035707 := bstep (se 1 (by rfl) ⟨1526780, by rfl⟩ : syracuseStep 2035707 = 3053561) B3053561
theorem B4706189 : Blo 2035435 4706189 := bbase (se 3 (by rfl) ⟨882410, by rfl⟩ : syracuseStep 4706189 = 1764821) (by norm_num)
theorem B3137459 : Blo 2035435 3137459 := bstep (se 1 (by rfl) ⟨2353094, by rfl⟩ : syracuseStep 3137459 = 4706189) B4706189
theorem B8366557 : Blo 2035435 8366557 := bstep (se 3 (by rfl) ⟨1568729, by rfl⟩ : syracuseStep 8366557 = 3137459) B3137459
theorem B11155409 : Blo 2035435 11155409 := bstep (se 2 (by rfl) ⟨4183278, by rfl⟩ : syracuseStep 11155409 = 8366557) B8366557
theorem B7436939 : Blo 2035435 7436939 := bstep (se 1 (by rfl) ⟨5577704, by rfl⟩ : syracuseStep 7436939 = 11155409) B11155409
theorem B19831837 : Blo 2035435 19831837 := bstep (se 3 (by rfl) ⟨3718469, by rfl⟩ : syracuseStep 19831837 = 7436939) B7436939
theorem B26442449 : Blo 2035435 26442449 := bstep (se 2 (by rfl) ⟨9915918, by rfl⟩ : syracuseStep 26442449 = 19831837) B19831837
theorem B17628299 : Blo 2035435 17628299 := bstep (se 1 (by rfl) ⟨13221224, by rfl⟩ : syracuseStep 17628299 = 26442449) B26442449
theorem B11752199 : Blo 2035435 11752199 := bstep (se 1 (by rfl) ⟨8814149, by rfl⟩ : syracuseStep 11752199 = 17628299) B17628299
theorem B7834799 : Blo 2035435 7834799 := bstep (se 1 (by rfl) ⟨5876099, by rfl⟩ : syracuseStep 7834799 = 11752199) B11752199
theorem B5223199 : Blo 2035435 5223199 := bstep (se 1 (by rfl) ⟨3917399, by rfl⟩ : syracuseStep 5223199 = 7834799) B7834799
theorem B6964265 : Blo 2035435 6964265 := bstep (se 2 (by rfl) ⟨2611599, by rfl⟩ : syracuseStep 6964265 = 5223199) B5223199
theorem B18571373 : Blo 2035435 18571373 := bstep (se 3 (by rfl) ⟨3482132, by rfl⟩ : syracuseStep 18571373 = 6964265) B6964265
theorem B12380915 : Blo 2035435 12380915 := bstep (se 1 (by rfl) ⟨9285686, by rfl⟩ : syracuseStep 12380915 = 18571373) B18571373
theorem B8253943 : Blo 2035435 8253943 := bstep (se 1 (by rfl) ⟨6190457, by rfl⟩ : syracuseStep 8253943 = 12380915) B12380915
theorem B176084117 : Blo 2035435 176084117 := bstep (se 6 (by rfl) ⟨4126971, by rfl⟩ : syracuseStep 176084117 = 8253943) B8253943
theorem B117389411 : Blo 2035435 117389411 := bstep (se 1 (by rfl) ⟨88042058, by rfl⟩ : syracuseStep 117389411 = 176084117) B176084117
theorem B78259607 : Blo 2035435 78259607 := bstep (se 1 (by rfl) ⟨58694705, by rfl⟩ : syracuseStep 78259607 = 117389411) B117389411
theorem B52173071 : Blo 2035435 52173071 := bstep (se 1 (by rfl) ⟨39129803, by rfl⟩ : syracuseStep 52173071 = 78259607) B78259607
theorem B34782047 : Blo 2035435 34782047 := bstep (se 1 (by rfl) ⟨26086535, by rfl⟩ : syracuseStep 34782047 = 52173071) B52173071
theorem B23188031 : Blo 2035435 23188031 := bstep (se 1 (by rfl) ⟨17391023, by rfl⟩ : syracuseStep 23188031 = 34782047) B34782047
theorem B15458687 : Blo 2035435 15458687 := bstep (se 1 (by rfl) ⟨11594015, by rfl⟩ : syracuseStep 15458687 = 23188031) B23188031
theorem B10305791 : Blo 2035435 10305791 := bstep (se 1 (by rfl) ⟨7729343, by rfl⟩ : syracuseStep 10305791 = 15458687) B15458687
theorem B6870527 : Blo 2035435 6870527 := bstep (se 1 (by rfl) ⟨5152895, by rfl⟩ : syracuseStep 6870527 = 10305791) B10305791
theorem B4580351 : Blo 2035435 4580351 := bstep (se 1 (by rfl) ⟨3435263, by rfl⟩ : syracuseStep 4580351 = 6870527) B6870527
theorem B3053567 : Blo 2035435 3053567 := bstep (se 1 (by rfl) ⟨2290175, by rfl⟩ : syracuseStep 3053567 = 4580351) B4580351
theorem B2035711 : Blo 2035435 2035711 := bstep (se 1 (by rfl) ⟨1526783, by rfl⟩ : syracuseStep 2035711 = 3053567) B3053567
theorem B3053573 : Blo 2035435 3053573 := bbase (se 4 (by rfl) ⟨286272, by rfl⟩ : syracuseStep 3053573 = 572545) (by norm_num)
theorem B2035715 : Blo 2035435 2035715 := bstep (se 1 (by rfl) ⟨1526786, by rfl⟩ : syracuseStep 2035715 = 3053573) B3053573
theorem B3435277 : Blo 2035435 3435277 := bbase (se 3 (by rfl) ⟨644114, by rfl⟩ : syracuseStep 3435277 = 1288229) (by norm_num)
theorem B4580369 : Blo 2035435 4580369 := bstep (se 2 (by rfl) ⟨1717638, by rfl⟩ : syracuseStep 4580369 = 3435277) B3435277
theorem B3053579 : Blo 2035435 3053579 := bstep (se 1 (by rfl) ⟨2290184, by rfl⟩ : syracuseStep 3053579 = 4580369) B4580369
theorem B2035719 : Blo 2035435 2035719 := bstep (se 1 (by rfl) ⟨1526789, by rfl⟩ : syracuseStep 2035719 = 3053579) B3053579
theorem B2290189 : Blo 2035435 2290189 := bbase (se 3 (by rfl) ⟨429410, by rfl⟩ : syracuseStep 2290189 = 858821) (by norm_num)
theorem B3053585 : Blo 2035435 3053585 := bstep (se 2 (by rfl) ⟨1145094, by rfl⟩ : syracuseStep 3053585 = 2290189) B2290189
theorem B2035723 : Blo 2035435 2035723 := bstep (se 1 (by rfl) ⟨1526792, by rfl⟩ : syracuseStep 2035723 = 3053585) B3053585
theorem B6870581 : Blo 2035435 6870581 := bbase (se 5 (by rfl) ⟨322058, by rfl⟩ : syracuseStep 6870581 = 644117) (by norm_num)
theorem B4580387 : Blo 2035435 4580387 := bstep (se 1 (by rfl) ⟨3435290, by rfl⟩ : syracuseStep 4580387 = 6870581) B6870581
theorem B3053591 : Blo 2035435 3053591 := bstep (se 1 (by rfl) ⟨2290193, by rfl⟩ : syracuseStep 3053591 = 4580387) B4580387
theorem B2035727 : Blo 2035435 2035727 := bstep (se 1 (by rfl) ⟨1526795, by rfl⟩ : syracuseStep 2035727 = 3053591) B3053591
theorem B3053597 : Blo 2035435 3053597 := bbase (se 3 (by rfl) ⟨572549, by rfl⟩ : syracuseStep 3053597 = 1145099) (by norm_num)
theorem B2035731 : Blo 2035435 2035731 := bstep (se 1 (by rfl) ⟨1526798, by rfl⟩ : syracuseStep 2035731 = 3053597) B3053597
theorem B4580405 : Blo 2035435 4580405 := bbase (se 5 (by rfl) ⟨214706, by rfl⟩ : syracuseStep 4580405 = 429413) (by norm_num)
theorem B3053603 : Blo 2035435 3053603 := bstep (se 1 (by rfl) ⟨2290202, by rfl⟩ : syracuseStep 3053603 = 4580405) B4580405
theorem B2035735 : Blo 2035435 2035735 := bstep (se 1 (by rfl) ⟨1526801, by rfl⟩ : syracuseStep 2035735 = 3053603) B3053603
theorem B6610709 : Blo 2035435 6610709 := bbase (se 6 (by rfl) ⟨154938, by rfl⟩ : syracuseStep 6610709 = 309877) (by norm_num)
theorem B4407139 : Blo 2035435 4407139 := bstep (se 1 (by rfl) ⟨3305354, by rfl⟩ : syracuseStep 4407139 = 6610709) B6610709
theorem B5876185 : Blo 2035435 5876185 := bstep (se 2 (by rfl) ⟨2203569, by rfl⟩ : syracuseStep 5876185 = 4407139) B4407139
theorem B7834913 : Blo 2035435 7834913 := bstep (se 2 (by rfl) ⟨2938092, by rfl⟩ : syracuseStep 7834913 = 5876185) B5876185
theorem B5223275 : Blo 2035435 5223275 := bstep (se 1 (by rfl) ⟨3917456, by rfl⟩ : syracuseStep 5223275 = 7834913) B7834913
theorem B3482183 : Blo 2035435 3482183 := bstep (se 1 (by rfl) ⟨2611637, by rfl⟩ : syracuseStep 3482183 = 5223275) B5223275
theorem B2321455 : Blo 2035435 2321455 := bstep (se 1 (by rfl) ⟨1741091, by rfl⟩ : syracuseStep 2321455 = 3482183) B3482183
theorem B3095273 : Blo 2035435 3095273 := bstep (se 2 (by rfl) ⟨1160727, by rfl⟩ : syracuseStep 3095273 = 2321455) B2321455
theorem B8254061 : Blo 2035435 8254061 := bstep (se 3 (by rfl) ⟨1547636, by rfl⟩ : syracuseStep 8254061 = 3095273) B3095273
theorem B5502707 : Blo 2035435 5502707 := bstep (se 1 (by rfl) ⟨4127030, by rfl⟩ : syracuseStep 5502707 = 8254061) B8254061
theorem B3668471 : Blo 2035435 3668471 := bstep (se 1 (by rfl) ⟨2751353, by rfl⟩ : syracuseStep 3668471 = 5502707) B5502707
theorem B2445647 : Blo 2035435 2445647 := bstep (se 1 (by rfl) ⟨1834235, by rfl⟩ : syracuseStep 2445647 = 3668471) B3668471
theorem B6521725 : Blo 2035435 6521725 := bstep (se 3 (by rfl) ⟨1222823, by rfl⟩ : syracuseStep 6521725 = 2445647) B2445647
theorem B8695633 : Blo 2035435 8695633 := bstep (se 2 (by rfl) ⟨3260862, by rfl⟩ : syracuseStep 8695633 = 6521725) B6521725
theorem B11594177 : Blo 2035435 11594177 := bstep (se 2 (by rfl) ⟨4347816, by rfl⟩ : syracuseStep 11594177 = 8695633) B8695633
theorem B7729451 : Blo 2035435 7729451 := bstep (se 1 (by rfl) ⟨5797088, by rfl⟩ : syracuseStep 7729451 = 11594177) B11594177
theorem B5152967 : Blo 2035435 5152967 := bstep (se 1 (by rfl) ⟨3864725, by rfl⟩ : syracuseStep 5152967 = 7729451) B7729451
theorem B3435311 : Blo 2035435 3435311 := bstep (se 1 (by rfl) ⟨2576483, by rfl⟩ : syracuseStep 3435311 = 5152967) B5152967
theorem B2290207 : Blo 2035435 2290207 := bstep (se 1 (by rfl) ⟨1717655, by rfl⟩ : syracuseStep 2290207 = 3435311) B3435311
theorem B3053609 : Blo 2035435 3053609 := bstep (se 2 (by rfl) ⟨1145103, by rfl⟩ : syracuseStep 3053609 = 2290207) B2290207
theorem B2035739 : Blo 2035435 2035739 := bstep (se 1 (by rfl) ⟨1526804, by rfl⟩ : syracuseStep 2035739 = 3053609) B3053609
theorem B10446565 : Blo 2035435 10446565 := bbase (se 4 (by rfl) ⟨979365, by rfl⟩ : syracuseStep 10446565 = 1958731) (by norm_num)
theorem B13928753 : Blo 2035435 13928753 := bstep (se 2 (by rfl) ⟨5223282, by rfl⟩ : syracuseStep 13928753 = 10446565) B10446565
theorem B9285835 : Blo 2035435 9285835 := bstep (se 1 (by rfl) ⟨6964376, by rfl⟩ : syracuseStep 9285835 = 13928753) B13928753
theorem B12381113 : Blo 2035435 12381113 := bstep (se 2 (by rfl) ⟨4642917, by rfl⟩ : syracuseStep 12381113 = 9285835) B9285835
theorem B8254075 : Blo 2035435 8254075 := bstep (se 1 (by rfl) ⟨6190556, by rfl⟩ : syracuseStep 8254075 = 12381113) B12381113
theorem B11005433 : Blo 2035435 11005433 := bstep (se 2 (by rfl) ⟨4127037, by rfl⟩ : syracuseStep 11005433 = 8254075) B8254075
theorem B7336955 : Blo 2035435 7336955 := bstep (se 1 (by rfl) ⟨5502716, by rfl⟩ : syracuseStep 7336955 = 11005433) B11005433
theorem B4891303 : Blo 2035435 4891303 := bstep (se 1 (by rfl) ⟨3668477, by rfl⟩ : syracuseStep 4891303 = 7336955) B7336955
theorem B6521737 : Blo 2035435 6521737 := bstep (se 2 (by rfl) ⟨2445651, by rfl⟩ : syracuseStep 6521737 = 4891303) B4891303
theorem B8695649 : Blo 2035435 8695649 := bstep (se 2 (by rfl) ⟨3260868, by rfl⟩ : syracuseStep 8695649 = 6521737) B6521737
theorem B5797099 : Blo 2035435 5797099 := bstep (se 1 (by rfl) ⟨4347824, by rfl⟩ : syracuseStep 5797099 = 8695649) B8695649
theorem B7729465 : Blo 2035435 7729465 := bstep (se 2 (by rfl) ⟨2898549, by rfl⟩ : syracuseStep 7729465 = 5797099) B5797099
theorem B10305953 : Blo 2035435 10305953 := bstep (se 2 (by rfl) ⟨3864732, by rfl⟩ : syracuseStep 10305953 = 7729465) B7729465
theorem B6870635 : Blo 2035435 6870635 := bstep (se 1 (by rfl) ⟨5152976, by rfl⟩ : syracuseStep 6870635 = 10305953) B10305953
theorem B4580423 : Blo 2035435 4580423 := bstep (se 1 (by rfl) ⟨3435317, by rfl⟩ : syracuseStep 4580423 = 6870635) B6870635
theorem B3053615 : Blo 2035435 3053615 := bstep (se 1 (by rfl) ⟨2290211, by rfl⟩ : syracuseStep 3053615 = 4580423) B4580423
theorem B2035743 : Blo 2035435 2035743 := bstep (se 1 (by rfl) ⟨1526807, by rfl⟩ : syracuseStep 2035743 = 3053615) B3053615
theorem B3053621 : Blo 2035435 3053621 := bbase (se 5 (by rfl) ⟨143138, by rfl⟩ : syracuseStep 3053621 = 286277) (by norm_num)
theorem B2035747 : Blo 2035435 2035747 := bstep (se 1 (by rfl) ⟨1526810, by rfl⟩ : syracuseStep 2035747 = 3053621) B3053621
theorem B5152997 : Blo 2035435 5152997 := bbase (se 4 (by rfl) ⟨483093, by rfl⟩ : syracuseStep 5152997 = 966187) (by norm_num)
theorem B3435331 : Blo 2035435 3435331 := bstep (se 1 (by rfl) ⟨2576498, by rfl⟩ : syracuseStep 3435331 = 5152997) B5152997
theorem B4580441 : Blo 2035435 4580441 := bstep (se 2 (by rfl) ⟨1717665, by rfl⟩ : syracuseStep 4580441 = 3435331) B3435331
theorem B3053627 : Blo 2035435 3053627 := bstep (se 1 (by rfl) ⟨2290220, by rfl⟩ : syracuseStep 3053627 = 4580441) B4580441
theorem B2035751 : Blo 2035435 2035751 := bstep (se 1 (by rfl) ⟨1526813, by rfl⟩ : syracuseStep 2035751 = 3053627) B3053627
theorem B2290225 : Blo 2035435 2290225 := bbase (se 2 (by rfl) ⟨858834, by rfl⟩ : syracuseStep 2290225 = 1717669) (by norm_num)
theorem B3053633 : Blo 2035435 3053633 := bstep (se 2 (by rfl) ⟨1145112, by rfl⟩ : syracuseStep 3053633 = 2290225) B2290225
theorem B2035755 : Blo 2035435 2035755 := bstep (se 1 (by rfl) ⟨1526816, by rfl⟩ : syracuseStep 2035755 = 3053633) B3053633
theorem B20893301 : Blo 2035435 20893301 := bbase (se 5 (by rfl) ⟨979373, by rfl⟩ : syracuseStep 20893301 = 1958747) (by norm_num)
theorem B13928867 : Blo 2035435 13928867 := bstep (se 1 (by rfl) ⟨10446650, by rfl⟩ : syracuseStep 13928867 = 20893301) B20893301
theorem B9285911 : Blo 2035435 9285911 := bstep (se 1 (by rfl) ⟨6964433, by rfl⟩ : syracuseStep 9285911 = 13928867) B13928867
theorem B6190607 : Blo 2035435 6190607 := bstep (se 1 (by rfl) ⟨4642955, by rfl⟩ : syracuseStep 6190607 = 9285911) B9285911
theorem B4127071 : Blo 2035435 4127071 := bstep (se 1 (by rfl) ⟨3095303, by rfl⟩ : syracuseStep 4127071 = 6190607) B6190607
theorem B5502761 : Blo 2035435 5502761 := bstep (se 2 (by rfl) ⟨2063535, by rfl⟩ : syracuseStep 5502761 = 4127071) B4127071
theorem B3668507 : Blo 2035435 3668507 := bstep (se 1 (by rfl) ⟨2751380, by rfl⟩ : syracuseStep 3668507 = 5502761) B5502761
theorem B2445671 : Blo 2035435 2445671 := bstep (se 1 (by rfl) ⟨1834253, by rfl⟩ : syracuseStep 2445671 = 3668507) B3668507
theorem B6521789 : Blo 2035435 6521789 := bstep (se 3 (by rfl) ⟨1222835, by rfl⟩ : syracuseStep 6521789 = 2445671) B2445671
theorem B4347859 : Blo 2035435 4347859 := bstep (se 1 (by rfl) ⟨3260894, by rfl⟩ : syracuseStep 4347859 = 6521789) B6521789
theorem B5797145 : Blo 2035435 5797145 := bstep (se 2 (by rfl) ⟨2173929, by rfl⟩ : syracuseStep 5797145 = 4347859) B4347859
theorem B3864763 : Blo 2035435 3864763 := bstep (se 1 (by rfl) ⟨2898572, by rfl⟩ : syracuseStep 3864763 = 5797145) B5797145
theorem B5153017 : Blo 2035435 5153017 := bstep (se 2 (by rfl) ⟨1932381, by rfl⟩ : syracuseStep 5153017 = 3864763) B3864763
theorem B6870689 : Blo 2035435 6870689 := bstep (se 2 (by rfl) ⟨2576508, by rfl⟩ : syracuseStep 6870689 = 5153017) B5153017
theorem B4580459 : Blo 2035435 4580459 := bstep (se 1 (by rfl) ⟨3435344, by rfl⟩ : syracuseStep 4580459 = 6870689) B6870689
theorem B3053639 : Blo 2035435 3053639 := bstep (se 1 (by rfl) ⟨2290229, by rfl⟩ : syracuseStep 3053639 = 4580459) B4580459
theorem B2035759 : Blo 2035435 2035759 := bstep (se 1 (by rfl) ⟨1526819, by rfl⟩ : syracuseStep 2035759 = 3053639) B3053639
theorem B3053645 : Blo 2035435 3053645 := bbase (se 3 (by rfl) ⟨572558, by rfl⟩ : syracuseStep 3053645 = 1145117) (by norm_num)
theorem B2035763 : Blo 2035435 2035763 := bstep (se 1 (by rfl) ⟨1526822, by rfl⟩ : syracuseStep 2035763 = 3053645) B3053645
theorem B4580477 : Blo 2035435 4580477 := bbase (se 3 (by rfl) ⟨858839, by rfl⟩ : syracuseStep 4580477 = 1717679) (by norm_num)
theorem B3053651 : Blo 2035435 3053651 := bstep (se 1 (by rfl) ⟨2290238, by rfl⟩ : syracuseStep 3053651 = 4580477) B4580477
theorem B2035767 : Blo 2035435 2035767 := bstep (se 1 (by rfl) ⟨1526825, by rfl⟩ : syracuseStep 2035767 = 3053651) B3053651
theorem B3435365 : Blo 2035435 3435365 := bbase (se 4 (by rfl) ⟨322065, by rfl⟩ : syracuseStep 3435365 = 644131) (by norm_num)
theorem B2290243 : Blo 2035435 2290243 := bstep (se 1 (by rfl) ⟨1717682, by rfl⟩ : syracuseStep 2290243 = 3435365) B3435365
theorem B3053657 : Blo 2035435 3053657 := bstep (se 2 (by rfl) ⟨1145121, by rfl⟩ : syracuseStep 3053657 = 2290243) B2290243
theorem B2035771 : Blo 2035435 2035771 := bstep (se 1 (by rfl) ⟨1526828, by rfl⟩ : syracuseStep 2035771 = 3053657) B3053657
theorem B4347893 : Blo 2035435 4347893 := bbase (se 5 (by rfl) ⟨203807, by rfl⟩ : syracuseStep 4347893 = 407615) (by norm_num)
theorem B2898595 : Blo 2035435 2898595 := bstep (se 1 (by rfl) ⟨2173946, by rfl⟩ : syracuseStep 2898595 = 4347893) B4347893
theorem B15459173 : Blo 2035435 15459173 := bstep (se 4 (by rfl) ⟨1449297, by rfl⟩ : syracuseStep 15459173 = 2898595) B2898595
theorem B10306115 : Blo 2035435 10306115 := bstep (se 1 (by rfl) ⟨7729586, by rfl⟩ : syracuseStep 10306115 = 15459173) B15459173
theorem B6870743 : Blo 2035435 6870743 := bstep (se 1 (by rfl) ⟨5153057, by rfl⟩ : syracuseStep 6870743 = 10306115) B10306115
theorem B4580495 : Blo 2035435 4580495 := bstep (se 1 (by rfl) ⟨3435371, by rfl⟩ : syracuseStep 4580495 = 6870743) B6870743
theorem B3053663 : Blo 2035435 3053663 := bstep (se 1 (by rfl) ⟨2290247, by rfl⟩ : syracuseStep 3053663 = 4580495) B4580495
theorem B2035775 : Blo 2035435 2035775 := bstep (se 1 (by rfl) ⟨1526831, by rfl⟩ : syracuseStep 2035775 = 3053663) B3053663
theorem B3053669 : Blo 2035435 3053669 := bbase (se 4 (by rfl) ⟨286281, by rfl⟩ : syracuseStep 3053669 = 572563) (by norm_num)
theorem B2035779 : Blo 2035435 2035779 := bstep (se 1 (by rfl) ⟨1526834, by rfl⟩ : syracuseStep 2035779 = 3053669) B3053669
theorem B2751413 : Blo 2035435 2751413 := bbase (se 5 (by rfl) ⟨128972, by rfl⟩ : syracuseStep 2751413 = 257945) (by norm_num)
theorem B7337101 : Blo 2035435 7337101 := bstep (se 3 (by rfl) ⟨1375706, by rfl⟩ : syracuseStep 7337101 = 2751413) B2751413
theorem B9782801 : Blo 2035435 9782801 := bstep (se 2 (by rfl) ⟨3668550, by rfl⟩ : syracuseStep 9782801 = 7337101) B7337101
theorem B6521867 : Blo 2035435 6521867 := bstep (se 1 (by rfl) ⟨4891400, by rfl⟩ : syracuseStep 6521867 = 9782801) B9782801
theorem B4347911 : Blo 2035435 4347911 := bstep (se 1 (by rfl) ⟨3260933, by rfl⟩ : syracuseStep 4347911 = 6521867) B6521867
theorem B2898607 : Blo 2035435 2898607 := bstep (se 1 (by rfl) ⟨2173955, by rfl⟩ : syracuseStep 2898607 = 4347911) B4347911
theorem B3864809 : Blo 2035435 3864809 := bstep (se 2 (by rfl) ⟨1449303, by rfl⟩ : syracuseStep 3864809 = 2898607) B2898607
theorem B2576539 : Blo 2035435 2576539 := bstep (se 1 (by rfl) ⟨1932404, by rfl⟩ : syracuseStep 2576539 = 3864809) B3864809
theorem B3435385 : Blo 2035435 3435385 := bstep (se 2 (by rfl) ⟨1288269, by rfl⟩ : syracuseStep 3435385 = 2576539) B2576539
theorem B4580513 : Blo 2035435 4580513 := bstep (se 2 (by rfl) ⟨1717692, by rfl⟩ : syracuseStep 4580513 = 3435385) B3435385
theorem B3053675 : Blo 2035435 3053675 := bstep (se 1 (by rfl) ⟨2290256, by rfl⟩ : syracuseStep 3053675 = 4580513) B4580513
theorem B2035783 : Blo 2035435 2035783 := bstep (se 1 (by rfl) ⟨1526837, by rfl⟩ : syracuseStep 2035783 = 3053675) B3053675
theorem B2290261 : Blo 2035435 2290261 := bbase (se 8 (by rfl) ⟨13419, by rfl⟩ : syracuseStep 2290261 = 26839) (by norm_num)
theorem B3053681 : Blo 2035435 3053681 := bstep (se 2 (by rfl) ⟨1145130, by rfl⟩ : syracuseStep 3053681 = 2290261) B2290261
theorem B2035787 : Blo 2035435 2035787 := bstep (se 1 (by rfl) ⟨1526840, by rfl⟩ : syracuseStep 2035787 = 3053681) B3053681
theorem B2576549 : Blo 2035435 2576549 := bbase (se 4 (by rfl) ⟨241551, by rfl⟩ : syracuseStep 2576549 = 483103) (by norm_num)
theorem B6870797 : Blo 2035435 6870797 := bstep (se 3 (by rfl) ⟨1288274, by rfl⟩ : syracuseStep 6870797 = 2576549) B2576549
theorem B4580531 : Blo 2035435 4580531 := bstep (se 1 (by rfl) ⟨3435398, by rfl⟩ : syracuseStep 4580531 = 6870797) B6870797
theorem B3053687 : Blo 2035435 3053687 := bstep (se 1 (by rfl) ⟨2290265, by rfl⟩ : syracuseStep 3053687 = 4580531) B4580531
theorem B2035791 : Blo 2035435 2035791 := bstep (se 1 (by rfl) ⟨1526843, by rfl⟩ : syracuseStep 2035791 = 3053687) B3053687
theorem B3053693 : Blo 2035435 3053693 := bbase (se 3 (by rfl) ⟨572567, by rfl⟩ : syracuseStep 3053693 = 1145135) (by norm_num)
theorem B2035795 : Blo 2035435 2035795 := bstep (se 1 (by rfl) ⟨1526846, by rfl⟩ : syracuseStep 2035795 = 3053693) B3053693
theorem B4580549 : Blo 2035435 4580549 := bbase (se 4 (by rfl) ⟨429426, by rfl⟩ : syracuseStep 4580549 = 858853) (by norm_num)
theorem B3053699 : Blo 2035435 3053699 := bstep (se 1 (by rfl) ⟨2290274, by rfl⟩ : syracuseStep 3053699 = 4580549) B4580549
theorem B2035799 : Blo 2035435 2035799 := bstep (se 1 (by rfl) ⟨1526849, by rfl⟩ : syracuseStep 2035799 = 3053699) B3053699
theorem B13043861 : Blo 2035435 13043861 := bbase (se 6 (by rfl) ⟨305715, by rfl⟩ : syracuseStep 13043861 = 611431) (by norm_num)
theorem B8695907 : Blo 2035435 8695907 := bstep (se 1 (by rfl) ⟨6521930, by rfl⟩ : syracuseStep 8695907 = 13043861) B13043861
theorem B5797271 : Blo 2035435 5797271 := bstep (se 1 (by rfl) ⟨4347953, by rfl⟩ : syracuseStep 5797271 = 8695907) B8695907
theorem B3864847 : Blo 2035435 3864847 := bstep (se 1 (by rfl) ⟨2898635, by rfl⟩ : syracuseStep 3864847 = 5797271) B5797271
theorem B5153129 : Blo 2035435 5153129 := bstep (se 2 (by rfl) ⟨1932423, by rfl⟩ : syracuseStep 5153129 = 3864847) B3864847
theorem B3435419 : Blo 2035435 3435419 := bstep (se 1 (by rfl) ⟨2576564, by rfl⟩ : syracuseStep 3435419 = 5153129) B5153129
theorem B2290279 : Blo 2035435 2290279 := bstep (se 1 (by rfl) ⟨1717709, by rfl⟩ : syracuseStep 2290279 = 3435419) B3435419
theorem B3053705 : Blo 2035435 3053705 := bstep (se 2 (by rfl) ⟨1145139, by rfl⟩ : syracuseStep 3053705 = 2290279) B2290279
theorem B2035803 : Blo 2035435 2035803 := bstep (se 1 (by rfl) ⟨1526852, by rfl⟩ : syracuseStep 2035803 = 3053705) B3053705
theorem B10306277 : Blo 2035435 10306277 := bbase (se 4 (by rfl) ⟨966213, by rfl⟩ : syracuseStep 10306277 = 1932427) (by norm_num)
theorem B6870851 : Blo 2035435 6870851 := bstep (se 1 (by rfl) ⟨5153138, by rfl⟩ : syracuseStep 6870851 = 10306277) B10306277
theorem B4580567 : Blo 2035435 4580567 := bstep (se 1 (by rfl) ⟨3435425, by rfl⟩ : syracuseStep 4580567 = 6870851) B6870851
theorem B3053711 : Blo 2035435 3053711 := bstep (se 1 (by rfl) ⟨2290283, by rfl⟩ : syracuseStep 3053711 = 4580567) B4580567
theorem B2035807 : Blo 2035435 2035807 := bstep (se 1 (by rfl) ⟨1526855, by rfl⟩ : syracuseStep 2035807 = 3053711) B3053711
theorem B3053717 : Blo 2035435 3053717 := bbase (se 6 (by rfl) ⟨71571, by rfl⟩ : syracuseStep 3053717 = 143143) (by norm_num)
theorem B2035811 : Blo 2035435 2035811 := bstep (se 1 (by rfl) ⟨1526858, by rfl⟩ : syracuseStep 2035811 = 3053717) B3053717
theorem B8695957 : Blo 2035435 8695957 := bbase (se 6 (by rfl) ⟨203811, by rfl⟩ : syracuseStep 8695957 = 407623) (by norm_num)
theorem B11594609 : Blo 2035435 11594609 := bstep (se 2 (by rfl) ⟨4347978, by rfl⟩ : syracuseStep 11594609 = 8695957) B8695957
theorem B7729739 : Blo 2035435 7729739 := bstep (se 1 (by rfl) ⟨5797304, by rfl⟩ : syracuseStep 7729739 = 11594609) B11594609
theorem B5153159 : Blo 2035435 5153159 := bstep (se 1 (by rfl) ⟨3864869, by rfl⟩ : syracuseStep 5153159 = 7729739) B7729739
theorem B3435439 : Blo 2035435 3435439 := bstep (se 1 (by rfl) ⟨2576579, by rfl⟩ : syracuseStep 3435439 = 5153159) B5153159
theorem B4580585 : Blo 2035435 4580585 := bstep (se 2 (by rfl) ⟨1717719, by rfl⟩ : syracuseStep 4580585 = 3435439) B3435439
theorem B3053723 : Blo 2035435 3053723 := bstep (se 1 (by rfl) ⟨2290292, by rfl⟩ : syracuseStep 3053723 = 4580585) B4580585
theorem B2035815 : Blo 2035435 2035815 := bstep (se 1 (by rfl) ⟨1526861, by rfl⟩ : syracuseStep 2035815 = 3053723) B3053723
theorem B2290297 : Blo 2035435 2290297 := bbase (se 2 (by rfl) ⟨858861, by rfl⟩ : syracuseStep 2290297 = 1717723) (by norm_num)
theorem B3053729 : Blo 2035435 3053729 := bstep (se 2 (by rfl) ⟨1145148, by rfl⟩ : syracuseStep 3053729 = 2290297) B2290297
theorem B2035819 : Blo 2035435 2035819 := bstep (se 1 (by rfl) ⟨1526864, by rfl⟩ : syracuseStep 2035819 = 3053729) B3053729
theorem B6701173 : Blo 2035435 6701173 := bbase (se 5 (by rfl) ⟨314117, by rfl⟩ : syracuseStep 6701173 = 628235) (by norm_num)
theorem B35739589 : Blo 2035435 35739589 := bstep (se 4 (by rfl) ⟨3350586, by rfl⟩ : syracuseStep 35739589 = 6701173) B6701173
theorem B47652785 : Blo 2035435 47652785 := bstep (se 2 (by rfl) ⟨17869794, by rfl⟩ : syracuseStep 47652785 = 35739589) B35739589
theorem B31768523 : Blo 2035435 31768523 := bstep (se 1 (by rfl) ⟨23826392, by rfl⟩ : syracuseStep 31768523 = 47652785) B47652785
theorem B21179015 : Blo 2035435 21179015 := bstep (se 1 (by rfl) ⟨15884261, by rfl⟩ : syracuseStep 21179015 = 31768523) B31768523
theorem B14119343 : Blo 2035435 14119343 := bstep (se 1 (by rfl) ⟨10589507, by rfl⟩ : syracuseStep 14119343 = 21179015) B21179015
theorem B9412895 : Blo 2035435 9412895 := bstep (se 1 (by rfl) ⟨7059671, by rfl⟩ : syracuseStep 9412895 = 14119343) B14119343
theorem B25101053 : Blo 2035435 25101053 := bstep (se 3 (by rfl) ⟨4706447, by rfl⟩ : syracuseStep 25101053 = 9412895) B9412895
theorem B16734035 : Blo 2035435 16734035 := bstep (se 1 (by rfl) ⟨12550526, by rfl⟩ : syracuseStep 16734035 = 25101053) B25101053
theorem B11156023 : Blo 2035435 11156023 := bstep (se 1 (by rfl) ⟨8367017, by rfl⟩ : syracuseStep 11156023 = 16734035) B16734035
theorem B14874697 : Blo 2035435 14874697 := bstep (se 2 (by rfl) ⟨5578011, by rfl⟩ : syracuseStep 14874697 = 11156023) B11156023
theorem B79331717 : Blo 2035435 79331717 := bstep (se 4 (by rfl) ⟨7437348, by rfl⟩ : syracuseStep 79331717 = 14874697) B14874697
theorem B52887811 : Blo 2035435 52887811 := bstep (se 1 (by rfl) ⟨39665858, by rfl⟩ : syracuseStep 52887811 = 79331717) B79331717
theorem B70517081 : Blo 2035435 70517081 := bstep (se 2 (by rfl) ⟨26443905, by rfl⟩ : syracuseStep 70517081 = 52887811) B52887811
theorem B47011387 : Blo 2035435 47011387 := bstep (se 1 (by rfl) ⟨35258540, by rfl⟩ : syracuseStep 47011387 = 70517081) B70517081
theorem B62681849 : Blo 2035435 62681849 := bstep (se 2 (by rfl) ⟨23505693, by rfl⟩ : syracuseStep 62681849 = 47011387) B47011387
theorem B41787899 : Blo 2035435 41787899 := bstep (se 1 (by rfl) ⟨31340924, by rfl⟩ : syracuseStep 41787899 = 62681849) B62681849
theorem B27858599 : Blo 2035435 27858599 := bstep (se 1 (by rfl) ⟨20893949, by rfl⟩ : syracuseStep 27858599 = 41787899) B41787899
theorem B18572399 : Blo 2035435 18572399 := bstep (se 1 (by rfl) ⟨13929299, by rfl⟩ : syracuseStep 18572399 = 27858599) B27858599
theorem B12381599 : Blo 2035435 12381599 := bstep (se 1 (by rfl) ⟨9286199, by rfl⟩ : syracuseStep 12381599 = 18572399) B18572399
theorem B8254399 : Blo 2035435 8254399 := bstep (se 1 (by rfl) ⟨6190799, by rfl⟩ : syracuseStep 8254399 = 12381599) B12381599
theorem B11005865 : Blo 2035435 11005865 := bstep (se 2 (by rfl) ⟨4127199, by rfl⟩ : syracuseStep 11005865 = 8254399) B8254399
theorem B7337243 : Blo 2035435 7337243 := bstep (se 1 (by rfl) ⟨5502932, by rfl⟩ : syracuseStep 7337243 = 11005865) B11005865
theorem B19565981 : Blo 2035435 19565981 := bstep (se 3 (by rfl) ⟨3668621, by rfl⟩ : syracuseStep 19565981 = 7337243) B7337243
theorem B13043987 : Blo 2035435 13043987 := bstep (se 1 (by rfl) ⟨9782990, by rfl⟩ : syracuseStep 13043987 = 19565981) B19565981
theorem B8695991 : Blo 2035435 8695991 := bstep (se 1 (by rfl) ⟨6521993, by rfl⟩ : syracuseStep 8695991 = 13043987) B13043987
theorem B5797327 : Blo 2035435 5797327 := bstep (se 1 (by rfl) ⟨4347995, by rfl⟩ : syracuseStep 5797327 = 8695991) B8695991
theorem B7729769 : Blo 2035435 7729769 := bstep (se 2 (by rfl) ⟨2898663, by rfl⟩ : syracuseStep 7729769 = 5797327) B5797327
theorem B5153179 : Blo 2035435 5153179 := bstep (se 1 (by rfl) ⟨3864884, by rfl⟩ : syracuseStep 5153179 = 7729769) B7729769
theorem B6870905 : Blo 2035435 6870905 := bstep (se 2 (by rfl) ⟨2576589, by rfl⟩ : syracuseStep 6870905 = 5153179) B5153179
theorem B4580603 : Blo 2035435 4580603 := bstep (se 1 (by rfl) ⟨3435452, by rfl⟩ : syracuseStep 4580603 = 6870905) B6870905
theorem B3053735 : Blo 2035435 3053735 := bstep (se 1 (by rfl) ⟨2290301, by rfl⟩ : syracuseStep 3053735 = 4580603) B4580603
theorem B2035823 : Blo 2035435 2035823 := bstep (se 1 (by rfl) ⟨1526867, by rfl⟩ : syracuseStep 2035823 = 3053735) B3053735
theorem B3053741 : Blo 2035435 3053741 := bbase (se 3 (by rfl) ⟨572576, by rfl⟩ : syracuseStep 3053741 = 1145153) (by norm_num)
theorem B2035827 : Blo 2035435 2035827 := bstep (se 1 (by rfl) ⟨1526870, by rfl⟩ : syracuseStep 2035827 = 3053741) B3053741
theorem B4580621 : Blo 2035435 4580621 := bbase (se 3 (by rfl) ⟨858866, by rfl⟩ : syracuseStep 4580621 = 1717733) (by norm_num)
theorem B3053747 : Blo 2035435 3053747 := bstep (se 1 (by rfl) ⟨2290310, by rfl⟩ : syracuseStep 3053747 = 4580621) B4580621
theorem B2035831 : Blo 2035435 2035831 := bstep (se 1 (by rfl) ⟨1526873, by rfl⟩ : syracuseStep 2035831 = 3053747) B3053747
theorem B2576605 : Blo 2035435 2576605 := bbase (se 3 (by rfl) ⟨483113, by rfl⟩ : syracuseStep 2576605 = 966227) (by norm_num)
theorem B3435473 : Blo 2035435 3435473 := bstep (se 2 (by rfl) ⟨1288302, by rfl⟩ : syracuseStep 3435473 = 2576605) B2576605
theorem B2290315 : Blo 2035435 2290315 := bstep (se 1 (by rfl) ⟨1717736, by rfl⟩ : syracuseStep 2290315 = 3435473) B3435473
theorem B3053753 : Blo 2035435 3053753 := bstep (se 2 (by rfl) ⟨1145157, by rfl⟩ : syracuseStep 3053753 = 2290315) B2290315
theorem B2035835 : Blo 2035435 2035835 := bstep (se 1 (by rfl) ⟨1526876, by rfl⟩ : syracuseStep 2035835 = 3053753) B3053753
theorem B17392117 : Blo 2035435 17392117 := bbase (se 5 (by rfl) ⟨815255, by rfl⟩ : syracuseStep 17392117 = 1630511) (by norm_num)
theorem B23189489 : Blo 2035435 23189489 := bstep (se 2 (by rfl) ⟨8696058, by rfl⟩ : syracuseStep 23189489 = 17392117) B17392117
theorem B15459659 : Blo 2035435 15459659 := bstep (se 1 (by rfl) ⟨11594744, by rfl⟩ : syracuseStep 15459659 = 23189489) B23189489
theorem B10306439 : Blo 2035435 10306439 := bstep (se 1 (by rfl) ⟨7729829, by rfl⟩ : syracuseStep 10306439 = 15459659) B15459659
theorem B6870959 : Blo 2035435 6870959 := bstep (se 1 (by rfl) ⟨5153219, by rfl⟩ : syracuseStep 6870959 = 10306439) B10306439
theorem B4580639 : Blo 2035435 4580639 := bstep (se 1 (by rfl) ⟨3435479, by rfl⟩ : syracuseStep 4580639 = 6870959) B6870959
theorem B3053759 : Blo 2035435 3053759 := bstep (se 1 (by rfl) ⟨2290319, by rfl⟩ : syracuseStep 3053759 = 4580639) B4580639
theorem B2035839 : Blo 2035435 2035839 := bstep (se 1 (by rfl) ⟨1526879, by rfl⟩ : syracuseStep 2035839 = 3053759) B3053759
theorem B3053765 : Blo 2035435 3053765 := bbase (se 4 (by rfl) ⟨286290, by rfl⟩ : syracuseStep 3053765 = 572581) (by norm_num)
theorem B2035843 : Blo 2035435 2035843 := bstep (se 1 (by rfl) ⟨1526882, by rfl⟩ : syracuseStep 2035843 = 3053765) B3053765
theorem B3435493 : Blo 2035435 3435493 := bbase (se 4 (by rfl) ⟨322077, by rfl⟩ : syracuseStep 3435493 = 644155) (by norm_num)
theorem B4580657 : Blo 2035435 4580657 := bstep (se 2 (by rfl) ⟨1717746, by rfl⟩ : syracuseStep 4580657 = 3435493) B3435493
theorem B3053771 : Blo 2035435 3053771 := bstep (se 1 (by rfl) ⟨2290328, by rfl⟩ : syracuseStep 3053771 = 4580657) B4580657
theorem B2035847 : Blo 2035435 2035847 := bstep (se 1 (by rfl) ⟨1526885, by rfl⟩ : syracuseStep 2035847 = 3053771) B3053771
theorem B2290333 : Blo 2035435 2290333 := bbase (se 3 (by rfl) ⟨429437, by rfl⟩ : syracuseStep 2290333 = 858875) (by norm_num)
theorem B3053777 : Blo 2035435 3053777 := bstep (se 2 (by rfl) ⟨1145166, by rfl⟩ : syracuseStep 3053777 = 2290333) B2290333
theorem B2035851 : Blo 2035435 2035851 := bstep (se 1 (by rfl) ⟨1526888, by rfl⟩ : syracuseStep 2035851 = 3053777) B3053777
theorem B6871013 : Blo 2035435 6871013 := bbase (se 4 (by rfl) ⟨644157, by rfl⟩ : syracuseStep 6871013 = 1288315) (by norm_num)
theorem B4580675 : Blo 2035435 4580675 := bstep (se 1 (by rfl) ⟨3435506, by rfl⟩ : syracuseStep 4580675 = 6871013) B6871013
theorem B3053783 : Blo 2035435 3053783 := bstep (se 1 (by rfl) ⟨2290337, by rfl⟩ : syracuseStep 3053783 = 4580675) B4580675
theorem B2035855 : Blo 2035435 2035855 := bstep (se 1 (by rfl) ⟨1526891, by rfl⟩ : syracuseStep 2035855 = 3053783) B3053783
theorem B3053789 : Blo 2035435 3053789 := bbase (se 3 (by rfl) ⟨572585, by rfl⟩ : syracuseStep 3053789 = 1145171) (by norm_num)
theorem B2035859 : Blo 2035435 2035859 := bstep (se 1 (by rfl) ⟨1526894, by rfl⟩ : syracuseStep 2035859 = 3053789) B3053789
theorem B4580693 : Blo 2035435 4580693 := bbase (se 12 (by rfl) ⟨1677, by rfl⟩ : syracuseStep 4580693 = 3355) (by norm_num)
theorem B3053795 : Blo 2035435 3053795 := bstep (se 1 (by rfl) ⟨2290346, by rfl⟩ : syracuseStep 3053795 = 4580693) B4580693
theorem B2035863 : Blo 2035435 2035863 := bstep (se 1 (by rfl) ⟨1526897, by rfl⟩ : syracuseStep 2035863 = 3053795) B3053795
theorem B2174045 : Blo 2035435 2174045 := bbase (se 3 (by rfl) ⟨407633, by rfl⟩ : syracuseStep 2174045 = 815267) (by norm_num)
theorem B5797453 : Blo 2035435 5797453 := bstep (se 3 (by rfl) ⟨1087022, by rfl⟩ : syracuseStep 5797453 = 2174045) B2174045
theorem B7729937 : Blo 2035435 7729937 := bstep (se 2 (by rfl) ⟨2898726, by rfl⟩ : syracuseStep 7729937 = 5797453) B5797453
theorem B5153291 : Blo 2035435 5153291 := bstep (se 1 (by rfl) ⟨3864968, by rfl⟩ : syracuseStep 5153291 = 7729937) B7729937
theorem B3435527 : Blo 2035435 3435527 := bstep (se 1 (by rfl) ⟨2576645, by rfl⟩ : syracuseStep 3435527 = 5153291) B5153291
theorem B2290351 : Blo 2035435 2290351 := bstep (se 1 (by rfl) ⟨1717763, by rfl⟩ : syracuseStep 2290351 = 3435527) B3435527
theorem B3053801 : Blo 2035435 3053801 := bstep (se 2 (by rfl) ⟨1145175, by rfl⟩ : syracuseStep 3053801 = 2290351) B2290351
theorem B2035867 : Blo 2035435 2035867 := bstep (se 1 (by rfl) ⟨1526900, by rfl⟩ : syracuseStep 2035867 = 3053801) B3053801
theorem B2611805 : Blo 2035435 2611805 := bbase (se 3 (by rfl) ⟨489713, by rfl⟩ : syracuseStep 2611805 = 979427) (by norm_num)
theorem B6964813 : Blo 2035435 6964813 := bstep (se 3 (by rfl) ⟨1305902, by rfl⟩ : syracuseStep 6964813 = 2611805) B2611805
theorem B9286417 : Blo 2035435 9286417 := bstep (se 2 (by rfl) ⟨3482406, by rfl⟩ : syracuseStep 9286417 = 6964813) B6964813
theorem B12381889 : Blo 2035435 12381889 := bstep (se 2 (by rfl) ⟨4643208, by rfl⟩ : syracuseStep 12381889 = 9286417) B9286417
theorem B16509185 : Blo 2035435 16509185 := bstep (se 2 (by rfl) ⟨6190944, by rfl⟩ : syracuseStep 16509185 = 12381889) B12381889
theorem B11006123 : Blo 2035435 11006123 := bstep (se 1 (by rfl) ⟨8254592, by rfl⟩ : syracuseStep 11006123 = 16509185) B16509185
theorem B29349661 : Blo 2035435 29349661 := bstep (se 3 (by rfl) ⟨5503061, by rfl⟩ : syracuseStep 29349661 = 11006123) B11006123
theorem B39132881 : Blo 2035435 39132881 := bstep (se 2 (by rfl) ⟨14674830, by rfl⟩ : syracuseStep 39132881 = 29349661) B29349661
theorem B26088587 : Blo 2035435 26088587 := bstep (se 1 (by rfl) ⟨19566440, by rfl⟩ : syracuseStep 26088587 = 39132881) B39132881
theorem B17392391 : Blo 2035435 17392391 := bstep (se 1 (by rfl) ⟨13044293, by rfl⟩ : syracuseStep 17392391 = 26088587) B26088587
theorem B11594927 : Blo 2035435 11594927 := bstep (se 1 (by rfl) ⟨8696195, by rfl⟩ : syracuseStep 11594927 = 17392391) B17392391
theorem B7729951 : Blo 2035435 7729951 := bstep (se 1 (by rfl) ⟨5797463, by rfl⟩ : syracuseStep 7729951 = 11594927) B11594927
theorem B10306601 : Blo 2035435 10306601 := bstep (se 2 (by rfl) ⟨3864975, by rfl⟩ : syracuseStep 10306601 = 7729951) B7729951
theorem B6871067 : Blo 2035435 6871067 := bstep (se 1 (by rfl) ⟨5153300, by rfl⟩ : syracuseStep 6871067 = 10306601) B10306601
theorem B4580711 : Blo 2035435 4580711 := bstep (se 1 (by rfl) ⟨3435533, by rfl⟩ : syracuseStep 4580711 = 6871067) B6871067
theorem B3053807 : Blo 2035435 3053807 := bstep (se 1 (by rfl) ⟨2290355, by rfl⟩ : syracuseStep 3053807 = 4580711) B4580711
theorem B2035871 : Blo 2035435 2035871 := bstep (se 1 (by rfl) ⟨1526903, by rfl⟩ : syracuseStep 2035871 = 3053807) B3053807
theorem B3053813 : Blo 2035435 3053813 := bbase (se 5 (by rfl) ⟨143147, by rfl⟩ : syracuseStep 3053813 = 286295) (by norm_num)
theorem B2035875 : Blo 2035435 2035875 := bstep (se 1 (by rfl) ⟨1526906, by rfl⟩ : syracuseStep 2035875 = 3053813) B3053813
theorem B3095485 : Blo 2035435 3095485 := bbase (se 3 (by rfl) ⟨580403, by rfl⟩ : syracuseStep 3095485 = 1160807) (by norm_num)
theorem B16509253 : Blo 2035435 16509253 := bstep (se 4 (by rfl) ⟨1547742, by rfl⟩ : syracuseStep 16509253 = 3095485) B3095485
theorem B22012337 : Blo 2035435 22012337 := bstep (se 2 (by rfl) ⟨8254626, by rfl⟩ : syracuseStep 22012337 = 16509253) B16509253
theorem B14674891 : Blo 2035435 14674891 := bstep (se 1 (by rfl) ⟨11006168, by rfl⟩ : syracuseStep 14674891 = 22012337) B22012337
theorem B19566521 : Blo 2035435 19566521 := bstep (se 2 (by rfl) ⟨7337445, by rfl⟩ : syracuseStep 19566521 = 14674891) B14674891
theorem B13044347 : Blo 2035435 13044347 := bstep (se 1 (by rfl) ⟨9783260, by rfl⟩ : syracuseStep 13044347 = 19566521) B19566521
theorem B8696231 : Blo 2035435 8696231 := bstep (se 1 (by rfl) ⟨6522173, by rfl⟩ : syracuseStep 8696231 = 13044347) B13044347
theorem B5797487 : Blo 2035435 5797487 := bstep (se 1 (by rfl) ⟨4348115, by rfl⟩ : syracuseStep 5797487 = 8696231) B8696231
theorem B3864991 : Blo 2035435 3864991 := bstep (se 1 (by rfl) ⟨2898743, by rfl⟩ : syracuseStep 3864991 = 5797487) B5797487
theorem B5153321 : Blo 2035435 5153321 := bstep (se 2 (by rfl) ⟨1932495, by rfl⟩ : syracuseStep 5153321 = 3864991) B3864991
theorem B3435547 : Blo 2035435 3435547 := bstep (se 1 (by rfl) ⟨2576660, by rfl⟩ : syracuseStep 3435547 = 5153321) B5153321
theorem B4580729 : Blo 2035435 4580729 := bstep (se 2 (by rfl) ⟨1717773, by rfl⟩ : syracuseStep 4580729 = 3435547) B3435547
theorem B3053819 : Blo 2035435 3053819 := bstep (se 1 (by rfl) ⟨2290364, by rfl⟩ : syracuseStep 3053819 = 4580729) B4580729
theorem B2035879 : Blo 2035435 2035879 := bstep (se 1 (by rfl) ⟨1526909, by rfl⟩ : syracuseStep 2035879 = 3053819) B3053819
theorem B2290369 : Blo 2035435 2290369 := bbase (se 2 (by rfl) ⟨858888, by rfl⟩ : syracuseStep 2290369 = 1717777) (by norm_num)
theorem B3053825 : Blo 2035435 3053825 := bstep (se 2 (by rfl) ⟨1145184, by rfl⟩ : syracuseStep 3053825 = 2290369) B2290369
theorem B2035883 : Blo 2035435 2035883 := bstep (se 1 (by rfl) ⟨1526912, by rfl⟩ : syracuseStep 2035883 = 3053825) B3053825
theorem B5153341 : Blo 2035435 5153341 := bbase (se 3 (by rfl) ⟨966251, by rfl⟩ : syracuseStep 5153341 = 1932503) (by norm_num)
theorem B6871121 : Blo 2035435 6871121 := bstep (se 2 (by rfl) ⟨2576670, by rfl⟩ : syracuseStep 6871121 = 5153341) B5153341
theorem B4580747 : Blo 2035435 4580747 := bstep (se 1 (by rfl) ⟨3435560, by rfl⟩ : syracuseStep 4580747 = 6871121) B6871121
theorem B3053831 : Blo 2035435 3053831 := bstep (se 1 (by rfl) ⟨2290373, by rfl⟩ : syracuseStep 3053831 = 4580747) B4580747
theorem B2035887 : Blo 2035435 2035887 := bstep (se 1 (by rfl) ⟨1526915, by rfl⟩ : syracuseStep 2035887 = 3053831) B3053831
theorem B3053837 : Blo 2035435 3053837 := bbase (se 3 (by rfl) ⟨572594, by rfl⟩ : syracuseStep 3053837 = 1145189) (by norm_num)
theorem B2035891 : Blo 2035435 2035891 := bstep (se 1 (by rfl) ⟨1526918, by rfl⟩ : syracuseStep 2035891 = 3053837) B3053837
theorem B4580765 : Blo 2035435 4580765 := bbase (se 3 (by rfl) ⟨858893, by rfl⟩ : syracuseStep 4580765 = 1717787) (by norm_num)
theorem B3053843 : Blo 2035435 3053843 := bstep (se 1 (by rfl) ⟨2290382, by rfl⟩ : syracuseStep 3053843 = 4580765) B4580765
theorem B2035895 : Blo 2035435 2035895 := bstep (se 1 (by rfl) ⟨1526921, by rfl⟩ : syracuseStep 2035895 = 3053843) B3053843
theorem B3435581 : Blo 2035435 3435581 := bbase (se 3 (by rfl) ⟨644171, by rfl⟩ : syracuseStep 3435581 = 1288343) (by norm_num)
theorem B2290387 : Blo 2035435 2290387 := bstep (se 1 (by rfl) ⟨1717790, by rfl⟩ : syracuseStep 2290387 = 3435581) B3435581
theorem B3053849 : Blo 2035435 3053849 := bstep (se 2 (by rfl) ⟨1145193, by rfl⟩ : syracuseStep 3053849 = 2290387) B2290387
theorem B2035899 : Blo 2035435 2035899 := bstep (se 1 (by rfl) ⟨1526924, by rfl⟩ : syracuseStep 2035899 = 3053849) B3053849
theorem B3261125 : Blo 2035435 3261125 := bbase (se 4 (by rfl) ⟨305730, by rfl⟩ : syracuseStep 3261125 = 611461) (by norm_num)
theorem B2174083 : Blo 2035435 2174083 := bstep (se 1 (by rfl) ⟨1630562, by rfl⟩ : syracuseStep 2174083 = 3261125) B3261125
theorem B11595109 : Blo 2035435 11595109 := bstep (se 4 (by rfl) ⟨1087041, by rfl⟩ : syracuseStep 11595109 = 2174083) B2174083
theorem B15460145 : Blo 2035435 15460145 := bstep (se 2 (by rfl) ⟨5797554, by rfl⟩ : syracuseStep 15460145 = 11595109) B11595109
theorem B10306763 : Blo 2035435 10306763 := bstep (se 1 (by rfl) ⟨7730072, by rfl⟩ : syracuseStep 10306763 = 15460145) B15460145
theorem B6871175 : Blo 2035435 6871175 := bstep (se 1 (by rfl) ⟨5153381, by rfl⟩ : syracuseStep 6871175 = 10306763) B10306763
theorem B4580783 : Blo 2035435 4580783 := bstep (se 1 (by rfl) ⟨3435587, by rfl⟩ : syracuseStep 4580783 = 6871175) B6871175
theorem B3053855 : Blo 2035435 3053855 := bstep (se 1 (by rfl) ⟨2290391, by rfl⟩ : syracuseStep 3053855 = 4580783) B4580783
theorem B2035903 : Blo 2035435 2035903 := bstep (se 1 (by rfl) ⟨1526927, by rfl⟩ : syracuseStep 2035903 = 3053855) B3053855
theorem B3053861 : Blo 2035435 3053861 := bbase (se 4 (by rfl) ⟨286299, by rfl⟩ : syracuseStep 3053861 = 572599) (by norm_num)
theorem B2035907 : Blo 2035435 2035907 := bstep (se 1 (by rfl) ⟨1526930, by rfl⟩ : syracuseStep 2035907 = 3053861) B3053861
theorem B2576701 : Blo 2035435 2576701 := bbase (se 3 (by rfl) ⟨483131, by rfl⟩ : syracuseStep 2576701 = 966263) (by norm_num)
theorem B3435601 : Blo 2035435 3435601 := bstep (se 2 (by rfl) ⟨1288350, by rfl⟩ : syracuseStep 3435601 = 2576701) B2576701
theorem B4580801 : Blo 2035435 4580801 := bstep (se 2 (by rfl) ⟨1717800, by rfl⟩ : syracuseStep 4580801 = 3435601) B3435601
theorem B3053867 : Blo 2035435 3053867 := bstep (se 1 (by rfl) ⟨2290400, by rfl⟩ : syracuseStep 3053867 = 4580801) B4580801
theorem B2035911 : Blo 2035435 2035911 := bstep (se 1 (by rfl) ⟨1526933, by rfl⟩ : syracuseStep 2035911 = 3053867) B3053867
theorem B2290405 : Blo 2035435 2290405 := bbase (se 4 (by rfl) ⟨214725, by rfl⟩ : syracuseStep 2290405 = 429451) (by norm_num)
theorem B3053873 : Blo 2035435 3053873 := bstep (se 2 (by rfl) ⟨1145202, by rfl⟩ : syracuseStep 3053873 = 2290405) B2290405
theorem B2035915 : Blo 2035435 2035915 := bstep (se 1 (by rfl) ⟨1526936, by rfl⟩ : syracuseStep 2035915 = 3053873) B3053873
theorem B6191093 : Blo 2035435 6191093 := bbase (se 5 (by rfl) ⟨290207, by rfl⟩ : syracuseStep 6191093 = 580415) (by norm_num)
theorem B16509581 : Blo 2035435 16509581 := bstep (se 3 (by rfl) ⟨3095546, by rfl⟩ : syracuseStep 16509581 = 6191093) B6191093
theorem B11006387 : Blo 2035435 11006387 := bstep (se 1 (by rfl) ⟨8254790, by rfl⟩ : syracuseStep 11006387 = 16509581) B16509581
theorem B7337591 : Blo 2035435 7337591 := bstep (se 1 (by rfl) ⟨5503193, by rfl⟩ : syracuseStep 7337591 = 11006387) B11006387
theorem B4891727 : Blo 2035435 4891727 := bstep (se 1 (by rfl) ⟨3668795, by rfl⟩ : syracuseStep 4891727 = 7337591) B7337591
theorem B3261151 : Blo 2035435 3261151 := bstep (se 1 (by rfl) ⟨2445863, by rfl⟩ : syracuseStep 3261151 = 4891727) B4891727
theorem B4348201 : Blo 2035435 4348201 := bstep (se 2 (by rfl) ⟨1630575, by rfl⟩ : syracuseStep 4348201 = 3261151) B3261151
theorem B5797601 : Blo 2035435 5797601 := bstep (se 2 (by rfl) ⟨2174100, by rfl⟩ : syracuseStep 5797601 = 4348201) B4348201
theorem B3865067 : Blo 2035435 3865067 := bstep (se 1 (by rfl) ⟨2898800, by rfl⟩ : syracuseStep 3865067 = 5797601) B5797601
theorem B2576711 : Blo 2035435 2576711 := bstep (se 1 (by rfl) ⟨1932533, by rfl⟩ : syracuseStep 2576711 = 3865067) B3865067
theorem B6871229 : Blo 2035435 6871229 := bstep (se 3 (by rfl) ⟨1288355, by rfl⟩ : syracuseStep 6871229 = 2576711) B2576711
theorem B4580819 : Blo 2035435 4580819 := bstep (se 1 (by rfl) ⟨3435614, by rfl⟩ : syracuseStep 4580819 = 6871229) B6871229
theorem B3053879 : Blo 2035435 3053879 := bstep (se 1 (by rfl) ⟨2290409, by rfl⟩ : syracuseStep 3053879 = 4580819) B4580819
theorem B2035919 : Blo 2035435 2035919 := bstep (se 1 (by rfl) ⟨1526939, by rfl⟩ : syracuseStep 2035919 = 3053879) B3053879
theorem B3053885 : Blo 2035435 3053885 := bbase (se 3 (by rfl) ⟨572603, by rfl⟩ : syracuseStep 3053885 = 1145207) (by norm_num)
theorem B2035923 : Blo 2035435 2035923 := bstep (se 1 (by rfl) ⟨1526942, by rfl⟩ : syracuseStep 2035923 = 3053885) B3053885
theorem B4580837 : Blo 2035435 4580837 := bbase (se 4 (by rfl) ⟨429453, by rfl⟩ : syracuseStep 4580837 = 858907) (by norm_num)
theorem B3053891 : Blo 2035435 3053891 := bstep (se 1 (by rfl) ⟨2290418, by rfl⟩ : syracuseStep 3053891 = 4580837) B4580837
theorem B2035927 : Blo 2035435 2035927 := bstep (se 1 (by rfl) ⟨1526945, by rfl⟩ : syracuseStep 2035927 = 3053891) B3053891
theorem B5153453 : Blo 2035435 5153453 := bbase (se 3 (by rfl) ⟨966272, by rfl⟩ : syracuseStep 5153453 = 1932545) (by norm_num)
theorem B3435635 : Blo 2035435 3435635 := bstep (se 1 (by rfl) ⟨2576726, by rfl⟩ : syracuseStep 3435635 = 5153453) B5153453
theorem B2290423 : Blo 2035435 2290423 := bstep (se 1 (by rfl) ⟨1717817, by rfl⟩ : syracuseStep 2290423 = 3435635) B3435635
theorem B3053897 : Blo 2035435 3053897 := bstep (se 2 (by rfl) ⟨1145211, by rfl⟩ : syracuseStep 3053897 = 2290423) B2290423
theorem B2035931 : Blo 2035435 2035931 := bstep (se 1 (by rfl) ⟨1526948, by rfl⟩ : syracuseStep 2035931 = 3053897) B3053897
theorem B4891765 : Blo 2035435 4891765 := bbase (se 5 (by rfl) ⟨229301, by rfl⟩ : syracuseStep 4891765 = 458603) (by norm_num)
theorem B6522353 : Blo 2035435 6522353 := bstep (se 2 (by rfl) ⟨2445882, by rfl⟩ : syracuseStep 6522353 = 4891765) B4891765
theorem B4348235 : Blo 2035435 4348235 := bstep (se 1 (by rfl) ⟨3261176, by rfl⟩ : syracuseStep 4348235 = 6522353) B6522353
theorem B2898823 : Blo 2035435 2898823 := bstep (se 1 (by rfl) ⟨2174117, by rfl⟩ : syracuseStep 2898823 = 4348235) B4348235
theorem B3865097 : Blo 2035435 3865097 := bstep (se 2 (by rfl) ⟨1449411, by rfl⟩ : syracuseStep 3865097 = 2898823) B2898823
theorem B10306925 : Blo 2035435 10306925 := bstep (se 3 (by rfl) ⟨1932548, by rfl⟩ : syracuseStep 10306925 = 3865097) B3865097
theorem B6871283 : Blo 2035435 6871283 := bstep (se 1 (by rfl) ⟨5153462, by rfl⟩ : syracuseStep 6871283 = 10306925) B10306925
theorem B4580855 : Blo 2035435 4580855 := bstep (se 1 (by rfl) ⟨3435641, by rfl⟩ : syracuseStep 4580855 = 6871283) B6871283
theorem B3053903 : Blo 2035435 3053903 := bstep (se 1 (by rfl) ⟨2290427, by rfl⟩ : syracuseStep 3053903 = 4580855) B4580855
theorem B2035935 : Blo 2035435 2035935 := bstep (se 1 (by rfl) ⟨1526951, by rfl⟩ : syracuseStep 2035935 = 3053903) B3053903
theorem B3053909 : Blo 2035435 3053909 := bbase (se 10 (by rfl) ⟨4473, by rfl⟩ : syracuseStep 3053909 = 8947) (by norm_num)
theorem B2035939 : Blo 2035435 2035939 := bstep (se 1 (by rfl) ⟨1526954, by rfl⟩ : syracuseStep 2035939 = 3053909) B3053909
theorem B5797669 : Blo 2035435 5797669 := bbase (se 4 (by rfl) ⟨543531, by rfl⟩ : syracuseStep 5797669 = 1087063) (by norm_num)
theorem B7730225 : Blo 2035435 7730225 := bstep (se 2 (by rfl) ⟨2898834, by rfl⟩ : syracuseStep 7730225 = 5797669) B5797669
theorem B5153483 : Blo 2035435 5153483 := bstep (se 1 (by rfl) ⟨3865112, by rfl⟩ : syracuseStep 5153483 = 7730225) B7730225
theorem B3435655 : Blo 2035435 3435655 := bstep (se 1 (by rfl) ⟨2576741, by rfl⟩ : syracuseStep 3435655 = 5153483) B5153483
theorem B4580873 : Blo 2035435 4580873 := bstep (se 2 (by rfl) ⟨1717827, by rfl⟩ : syracuseStep 4580873 = 3435655) B3435655
theorem B3053915 : Blo 2035435 3053915 := bstep (se 1 (by rfl) ⟨2290436, by rfl⟩ : syracuseStep 3053915 = 4580873) B4580873
theorem B2035943 : Blo 2035435 2035943 := bstep (se 1 (by rfl) ⟨1526957, by rfl⟩ : syracuseStep 2035943 = 3053915) B3053915
theorem B2290441 : Blo 2035435 2290441 := bbase (se 2 (by rfl) ⟨858915, by rfl⟩ : syracuseStep 2290441 = 1717831) (by norm_num)
theorem B3053921 : Blo 2035435 3053921 := bstep (se 2 (by rfl) ⟨1145220, by rfl⟩ : syracuseStep 3053921 = 2290441) B2290441
theorem B2035947 : Blo 2035435 2035947 := bstep (se 1 (by rfl) ⟨1526960, by rfl⟩ : syracuseStep 2035947 = 3053921) B3053921
theorem B9783605 : Blo 2035435 9783605 := bbase (se 5 (by rfl) ⟨458606, by rfl⟩ : syracuseStep 9783605 = 917213) (by norm_num)
theorem B26089613 : Blo 2035435 26089613 := bstep (se 3 (by rfl) ⟨4891802, by rfl⟩ : syracuseStep 26089613 = 9783605) B9783605
theorem B17393075 : Blo 2035435 17393075 := bstep (se 1 (by rfl) ⟨13044806, by rfl⟩ : syracuseStep 17393075 = 26089613) B26089613
theorem B11595383 : Blo 2035435 11595383 := bstep (se 1 (by rfl) ⟨8696537, by rfl⟩ : syracuseStep 11595383 = 17393075) B17393075
theorem B7730255 : Blo 2035435 7730255 := bstep (se 1 (by rfl) ⟨5797691, by rfl⟩ : syracuseStep 7730255 = 11595383) B11595383
theorem B5153503 : Blo 2035435 5153503 := bstep (se 1 (by rfl) ⟨3865127, by rfl⟩ : syracuseStep 5153503 = 7730255) B7730255
theorem B6871337 : Blo 2035435 6871337 := bstep (se 2 (by rfl) ⟨2576751, by rfl⟩ : syracuseStep 6871337 = 5153503) B5153503
theorem B4580891 : Blo 2035435 4580891 := bstep (se 1 (by rfl) ⟨3435668, by rfl⟩ : syracuseStep 4580891 = 6871337) B6871337
theorem B3053927 : Blo 2035435 3053927 := bstep (se 1 (by rfl) ⟨2290445, by rfl⟩ : syracuseStep 3053927 = 4580891) B4580891
theorem B2035951 : Blo 2035435 2035951 := bstep (se 1 (by rfl) ⟨1526963, by rfl⟩ : syracuseStep 2035951 = 3053927) B3053927
theorem B3053933 : Blo 2035435 3053933 := bbase (se 3 (by rfl) ⟨572612, by rfl⟩ : syracuseStep 3053933 = 1145225) (by norm_num)
theorem B2035955 : Blo 2035435 2035955 := bstep (se 1 (by rfl) ⟨1526966, by rfl⟩ : syracuseStep 2035955 = 3053933) B3053933
theorem B4580909 : Blo 2035435 4580909 := bbase (se 3 (by rfl) ⟨858920, by rfl⟩ : syracuseStep 4580909 = 1717841) (by norm_num)
theorem B3053939 : Blo 2035435 3053939 := bstep (se 1 (by rfl) ⟨2290454, by rfl⟩ : syracuseStep 3053939 = 4580909) B4580909
theorem B2035959 : Blo 2035435 2035959 := bstep (se 1 (by rfl) ⟨1526969, by rfl⟩ : syracuseStep 2035959 = 3053939) B3053939
theorem B29350997 : Blo 2035435 29350997 := bbase (se 8 (by rfl) ⟨171978, by rfl⟩ : syracuseStep 29350997 = 343957) (by norm_num)
theorem B19567331 : Blo 2035435 19567331 := bstep (se 1 (by rfl) ⟨14675498, by rfl⟩ : syracuseStep 19567331 = 29350997) B29350997
theorem B13044887 : Blo 2035435 13044887 := bstep (se 1 (by rfl) ⟨9783665, by rfl⟩ : syracuseStep 13044887 = 19567331) B19567331
theorem B8696591 : Blo 2035435 8696591 := bstep (se 1 (by rfl) ⟨6522443, by rfl⟩ : syracuseStep 8696591 = 13044887) B13044887
theorem B5797727 : Blo 2035435 5797727 := bstep (se 1 (by rfl) ⟨4348295, by rfl⟩ : syracuseStep 5797727 = 8696591) B8696591
theorem B3865151 : Blo 2035435 3865151 := bstep (se 1 (by rfl) ⟨2898863, by rfl⟩ : syracuseStep 3865151 = 5797727) B5797727
theorem B2576767 : Blo 2035435 2576767 := bstep (se 1 (by rfl) ⟨1932575, by rfl⟩ : syracuseStep 2576767 = 3865151) B3865151
theorem B3435689 : Blo 2035435 3435689 := bstep (se 2 (by rfl) ⟨1288383, by rfl⟩ : syracuseStep 3435689 = 2576767) B2576767
theorem B2290459 : Blo 2035435 2290459 := bstep (se 1 (by rfl) ⟨1717844, by rfl⟩ : syracuseStep 2290459 = 3435689) B3435689
theorem B3053945 : Blo 2035435 3053945 := bstep (se 2 (by rfl) ⟨1145229, by rfl⟩ : syracuseStep 3053945 = 2290459) B2290459
theorem B2035963 : Blo 2035435 2035963 := bstep (se 1 (by rfl) ⟨1526972, by rfl⟩ : syracuseStep 2035963 = 3053945) B3053945
theorem B2751661 : Blo 2035435 2751661 := bbase (se 3 (by rfl) ⟨515936, by rfl⟩ : syracuseStep 2751661 = 1031873) (by norm_num)
theorem B3668881 : Blo 2035435 3668881 := bstep (se 2 (by rfl) ⟨1375830, by rfl⟩ : syracuseStep 3668881 = 2751661) B2751661
theorem B4891841 : Blo 2035435 4891841 := bstep (se 2 (by rfl) ⟨1834440, by rfl⟩ : syracuseStep 4891841 = 3668881) B3668881
theorem B3261227 : Blo 2035435 3261227 := bstep (se 1 (by rfl) ⟨2445920, by rfl⟩ : syracuseStep 3261227 = 4891841) B4891841
theorem B34786421 : Blo 2035435 34786421 := bstep (se 5 (by rfl) ⟨1630613, by rfl⟩ : syracuseStep 34786421 = 3261227) B3261227
theorem B23190947 : Blo 2035435 23190947 := bstep (se 1 (by rfl) ⟨17393210, by rfl⟩ : syracuseStep 23190947 = 34786421) B34786421
theorem B15460631 : Blo 2035435 15460631 := bstep (se 1 (by rfl) ⟨11595473, by rfl⟩ : syracuseStep 15460631 = 23190947) B23190947
theorem B10307087 : Blo 2035435 10307087 := bstep (se 1 (by rfl) ⟨7730315, by rfl⟩ : syracuseStep 10307087 = 15460631) B15460631
theorem B6871391 : Blo 2035435 6871391 := bstep (se 1 (by rfl) ⟨5153543, by rfl⟩ : syracuseStep 6871391 = 10307087) B10307087
theorem B4580927 : Blo 2035435 4580927 := bstep (se 1 (by rfl) ⟨3435695, by rfl⟩ : syracuseStep 4580927 = 6871391) B6871391
theorem B3053951 : Blo 2035435 3053951 := bstep (se 1 (by rfl) ⟨2290463, by rfl⟩ : syracuseStep 3053951 = 4580927) B4580927
theorem B2035967 : Blo 2035435 2035967 := bstep (se 1 (by rfl) ⟨1526975, by rfl⟩ : syracuseStep 2035967 = 3053951) B3053951
theorem B3053957 : Blo 2035435 3053957 := bbase (se 4 (by rfl) ⟨286308, by rfl⟩ : syracuseStep 3053957 = 572617) (by norm_num)
theorem B2035971 : Blo 2035435 2035971 := bstep (se 1 (by rfl) ⟨1526978, by rfl⟩ : syracuseStep 2035971 = 3053957) B3053957
theorem B3435709 : Blo 2035435 3435709 := bbase (se 3 (by rfl) ⟨644195, by rfl⟩ : syracuseStep 3435709 = 1288391) (by norm_num)
theorem B4580945 : Blo 2035435 4580945 := bstep (se 2 (by rfl) ⟨1717854, by rfl⟩ : syracuseStep 4580945 = 3435709) B3435709
theorem B3053963 : Blo 2035435 3053963 := bstep (se 1 (by rfl) ⟨2290472, by rfl⟩ : syracuseStep 3053963 = 4580945) B4580945
theorem B2035975 : Blo 2035435 2035975 := bstep (se 1 (by rfl) ⟨1526981, by rfl⟩ : syracuseStep 2035975 = 3053963) B3053963
theorem B2290477 : Blo 2035435 2290477 := bbase (se 3 (by rfl) ⟨429464, by rfl⟩ : syracuseStep 2290477 = 858929) (by norm_num)
theorem B3053969 : Blo 2035435 3053969 := bstep (se 2 (by rfl) ⟨1145238, by rfl⟩ : syracuseStep 3053969 = 2290477) B2290477
theorem B2035979 : Blo 2035435 2035979 := bstep (se 1 (by rfl) ⟨1526984, by rfl⟩ : syracuseStep 2035979 = 3053969) B3053969
theorem B6871445 : Blo 2035435 6871445 := bbase (se 6 (by rfl) ⟨161049, by rfl⟩ : syracuseStep 6871445 = 322099) (by norm_num)
theorem B4580963 : Blo 2035435 4580963 := bstep (se 1 (by rfl) ⟨3435722, by rfl⟩ : syracuseStep 4580963 = 6871445) B6871445
theorem B3053975 : Blo 2035435 3053975 := bstep (se 1 (by rfl) ⟨2290481, by rfl⟩ : syracuseStep 3053975 = 4580963) B4580963
theorem B2035983 : Blo 2035435 2035983 := bstep (se 1 (by rfl) ⟨1526987, by rfl⟩ : syracuseStep 2035983 = 3053975) B3053975
theorem B3053981 : Blo 2035435 3053981 := bbase (se 3 (by rfl) ⟨572621, by rfl⟩ : syracuseStep 3053981 = 1145243) (by norm_num)
theorem B2035987 : Blo 2035435 2035987 := bstep (se 1 (by rfl) ⟨1526990, by rfl⟩ : syracuseStep 2035987 = 3053981) B3053981
theorem B4580981 : Blo 2035435 4580981 := bbase (se 5 (by rfl) ⟨214733, by rfl⟩ : syracuseStep 4580981 = 429467) (by norm_num)
theorem B3053987 : Blo 2035435 3053987 := bstep (se 1 (by rfl) ⟨2290490, by rfl⟩ : syracuseStep 3053987 = 4580981) B4580981
theorem B2035991 : Blo 2035435 2035991 := bstep (se 1 (by rfl) ⟨1526993, by rfl⟩ : syracuseStep 2035991 = 3053987) B3053987
theorem B4891909 : Blo 2035435 4891909 := bbase (se 4 (by rfl) ⟨458616, by rfl⟩ : syracuseStep 4891909 = 917233) (by norm_num)
theorem B6522545 : Blo 2035435 6522545 := bstep (se 2 (by rfl) ⟨2445954, by rfl⟩ : syracuseStep 6522545 = 4891909) B4891909
theorem B17393453 : Blo 2035435 17393453 := bstep (se 3 (by rfl) ⟨3261272, by rfl⟩ : syracuseStep 17393453 = 6522545) B6522545
theorem B11595635 : Blo 2035435 11595635 := bstep (se 1 (by rfl) ⟨8696726, by rfl⟩ : syracuseStep 11595635 = 17393453) B17393453
theorem B7730423 : Blo 2035435 7730423 := bstep (se 1 (by rfl) ⟨5797817, by rfl⟩ : syracuseStep 7730423 = 11595635) B11595635
theorem B5153615 : Blo 2035435 5153615 := bstep (se 1 (by rfl) ⟨3865211, by rfl⟩ : syracuseStep 5153615 = 7730423) B7730423
theorem B3435743 : Blo 2035435 3435743 := bstep (se 1 (by rfl) ⟨2576807, by rfl⟩ : syracuseStep 3435743 = 5153615) B5153615
theorem B2290495 : Blo 2035435 2290495 := bstep (se 1 (by rfl) ⟨1717871, by rfl⟩ : syracuseStep 2290495 = 3435743) B3435743
theorem B3053993 : Blo 2035435 3053993 := bstep (se 2 (by rfl) ⟨1145247, by rfl⟩ : syracuseStep 3053993 = 2290495) B2290495
theorem B2035995 : Blo 2035435 2035995 := bstep (se 1 (by rfl) ⟨1526996, by rfl⟩ : syracuseStep 2035995 = 3053993) B3053993
theorem B7730437 : Blo 2035435 7730437 := bbase (se 4 (by rfl) ⟨724728, by rfl⟩ : syracuseStep 7730437 = 1449457) (by norm_num)
theorem B10307249 : Blo 2035435 10307249 := bstep (se 2 (by rfl) ⟨3865218, by rfl⟩ : syracuseStep 10307249 = 7730437) B7730437
theorem B6871499 : Blo 2035435 6871499 := bstep (se 1 (by rfl) ⟨5153624, by rfl⟩ : syracuseStep 6871499 = 10307249) B10307249
theorem B4580999 : Blo 2035435 4580999 := bstep (se 1 (by rfl) ⟨3435749, by rfl⟩ : syracuseStep 4580999 = 6871499) B6871499
theorem B3053999 : Blo 2035435 3053999 := bstep (se 1 (by rfl) ⟨2290499, by rfl⟩ : syracuseStep 3053999 = 4580999) B4580999
theorem B2035999 : Blo 2035435 2035999 := bstep (se 1 (by rfl) ⟨1526999, by rfl⟩ : syracuseStep 2035999 = 3053999) B3053999
theorem B3054005 : Blo 2035435 3054005 := bbase (se 5 (by rfl) ⟨143156, by rfl⟩ : syracuseStep 3054005 = 286313) (by norm_num)
theorem B2036003 : Blo 2035435 2036003 := bstep (se 1 (by rfl) ⟨1527002, by rfl⟩ : syracuseStep 2036003 = 3054005) B3054005
theorem B5153645 : Blo 2035435 5153645 := bbase (se 3 (by rfl) ⟨966308, by rfl⟩ : syracuseStep 5153645 = 1932617) (by norm_num)
theorem B3435763 : Blo 2035435 3435763 := bstep (se 1 (by rfl) ⟨2576822, by rfl⟩ : syracuseStep 3435763 = 5153645) B5153645
theorem B4581017 : Blo 2035435 4581017 := bstep (se 2 (by rfl) ⟨1717881, by rfl⟩ : syracuseStep 4581017 = 3435763) B3435763
theorem B3054011 : Blo 2035435 3054011 := bstep (se 1 (by rfl) ⟨2290508, by rfl⟩ : syracuseStep 3054011 = 4581017) B4581017
theorem B2036007 : Blo 2035435 2036007 := bstep (se 1 (by rfl) ⟨1527005, by rfl⟩ : syracuseStep 2036007 = 3054011) B3054011
theorem B2290513 : Blo 2035435 2290513 := bbase (se 2 (by rfl) ⟨858942, by rfl⟩ : syracuseStep 2290513 = 1717885) (by norm_num)
theorem B3054017 : Blo 2035435 3054017 := bstep (se 2 (by rfl) ⟨1145256, by rfl⟩ : syracuseStep 3054017 = 2290513) B2290513
theorem B2036011 : Blo 2035435 2036011 := bstep (se 1 (by rfl) ⟨1527008, by rfl⟩ : syracuseStep 2036011 = 3054017) B3054017
theorem B31771541 : Blo 2035435 31771541 := bbase (se 6 (by rfl) ⟨744645, by rfl⟩ : syracuseStep 31771541 = 1489291) (by norm_num)
theorem B21181027 : Blo 2035435 21181027 := bstep (se 1 (by rfl) ⟨15885770, by rfl⟩ : syracuseStep 21181027 = 31771541) B31771541
theorem B28241369 : Blo 2035435 28241369 := bstep (se 2 (by rfl) ⟨10590513, by rfl⟩ : syracuseStep 28241369 = 21181027) B21181027
theorem B18827579 : Blo 2035435 18827579 := bstep (se 1 (by rfl) ⟨14120684, by rfl⟩ : syracuseStep 18827579 = 28241369) B28241369
theorem B50206877 : Blo 2035435 50206877 := bstep (se 3 (by rfl) ⟨9413789, by rfl⟩ : syracuseStep 50206877 = 18827579) B18827579
theorem B33471251 : Blo 2035435 33471251 := bstep (se 1 (by rfl) ⟨25103438, by rfl⟩ : syracuseStep 33471251 = 50206877) B50206877
theorem B22314167 : Blo 2035435 22314167 := bstep (se 1 (by rfl) ⟨16735625, by rfl⟩ : syracuseStep 22314167 = 33471251) B33471251
theorem B14876111 : Blo 2035435 14876111 := bstep (se 1 (by rfl) ⟨11157083, by rfl⟩ : syracuseStep 14876111 = 22314167) B22314167
theorem B9917407 : Blo 2035435 9917407 := bstep (se 1 (by rfl) ⟨7438055, by rfl⟩ : syracuseStep 9917407 = 14876111) B14876111
theorem B52892837 : Blo 2035435 52892837 := bstep (se 4 (by rfl) ⟨4958703, by rfl⟩ : syracuseStep 52892837 = 9917407) B9917407
theorem B35261891 : Blo 2035435 35261891 := bstep (se 1 (by rfl) ⟨26446418, by rfl⟩ : syracuseStep 35261891 = 52892837) B52892837
theorem B23507927 : Blo 2035435 23507927 := bstep (se 1 (by rfl) ⟨17630945, by rfl⟩ : syracuseStep 23507927 = 35261891) B35261891
theorem B15671951 : Blo 2035435 15671951 := bstep (se 1 (by rfl) ⟨11753963, by rfl⟩ : syracuseStep 15671951 = 23507927) B23507927
theorem B10447967 : Blo 2035435 10447967 := bstep (se 1 (by rfl) ⟨7835975, by rfl⟩ : syracuseStep 10447967 = 15671951) B15671951
theorem B6965311 : Blo 2035435 6965311 := bstep (se 1 (by rfl) ⟨5223983, by rfl⟩ : syracuseStep 6965311 = 10447967) B10447967
theorem B9287081 : Blo 2035435 9287081 := bstep (se 2 (by rfl) ⟨3482655, by rfl⟩ : syracuseStep 9287081 = 6965311) B6965311
theorem B6191387 : Blo 2035435 6191387 := bstep (se 1 (by rfl) ⟨4643540, by rfl⟩ : syracuseStep 6191387 = 9287081) B9287081
theorem B4127591 : Blo 2035435 4127591 := bstep (se 1 (by rfl) ⟨3095693, by rfl⟩ : syracuseStep 4127591 = 6191387) B6191387
theorem B2751727 : Blo 2035435 2751727 := bstep (se 1 (by rfl) ⟨2063795, by rfl⟩ : syracuseStep 2751727 = 4127591) B4127591
theorem B3668969 : Blo 2035435 3668969 := bstep (se 2 (by rfl) ⟨1375863, by rfl⟩ : syracuseStep 3668969 = 2751727) B2751727
theorem B2445979 : Blo 2035435 2445979 := bstep (se 1 (by rfl) ⟨1834484, by rfl⟩ : syracuseStep 2445979 = 3668969) B3668969
theorem B3261305 : Blo 2035435 3261305 := bstep (se 2 (by rfl) ⟨1222989, by rfl⟩ : syracuseStep 3261305 = 2445979) B2445979
theorem B2174203 : Blo 2035435 2174203 := bstep (se 1 (by rfl) ⟨1630652, by rfl⟩ : syracuseStep 2174203 = 3261305) B3261305
theorem B2898937 : Blo 2035435 2898937 := bstep (se 2 (by rfl) ⟨1087101, by rfl⟩ : syracuseStep 2898937 = 2174203) B2174203
theorem B3865249 : Blo 2035435 3865249 := bstep (se 2 (by rfl) ⟨1449468, by rfl⟩ : syracuseStep 3865249 = 2898937) B2898937
theorem B5153665 : Blo 2035435 5153665 := bstep (se 2 (by rfl) ⟨1932624, by rfl⟩ : syracuseStep 5153665 = 3865249) B3865249
theorem B6871553 : Blo 2035435 6871553 := bstep (se 2 (by rfl) ⟨2576832, by rfl⟩ : syracuseStep 6871553 = 5153665) B5153665
theorem B4581035 : Blo 2035435 4581035 := bstep (se 1 (by rfl) ⟨3435776, by rfl⟩ : syracuseStep 4581035 = 6871553) B6871553
theorem B3054023 : Blo 2035435 3054023 := bstep (se 1 (by rfl) ⟨2290517, by rfl⟩ : syracuseStep 3054023 = 4581035) B4581035
theorem B2036015 : Blo 2035435 2036015 := bstep (se 1 (by rfl) ⟨1527011, by rfl⟩ : syracuseStep 2036015 = 3054023) B3054023
theorem B3054029 : Blo 2035435 3054029 := bbase (se 3 (by rfl) ⟨572630, by rfl⟩ : syracuseStep 3054029 = 1145261) (by norm_num)
theorem B2036019 : Blo 2035435 2036019 := bstep (se 1 (by rfl) ⟨1527014, by rfl⟩ : syracuseStep 2036019 = 3054029) B3054029
theorem B4581053 : Blo 2035435 4581053 := bbase (se 3 (by rfl) ⟨858947, by rfl⟩ : syracuseStep 4581053 = 1717895) (by norm_num)
theorem B3054035 : Blo 2035435 3054035 := bstep (se 1 (by rfl) ⟨2290526, by rfl⟩ : syracuseStep 3054035 = 4581053) B4581053
theorem B2036023 : Blo 2035435 2036023 := bstep (se 1 (by rfl) ⟨1527017, by rfl⟩ : syracuseStep 2036023 = 3054035) B3054035
theorem B3435797 : Blo 2035435 3435797 := bbase (se 6 (by rfl) ⟨80526, by rfl⟩ : syracuseStep 3435797 = 161053) (by norm_num)
theorem B2290531 : Blo 2035435 2290531 := bstep (se 1 (by rfl) ⟨1717898, by rfl⟩ : syracuseStep 2290531 = 3435797) B3435797
theorem B3054041 : Blo 2035435 3054041 := bstep (se 2 (by rfl) ⟨1145265, by rfl⟩ : syracuseStep 3054041 = 2290531) B2290531
theorem B2036027 : Blo 2035435 2036027 := bstep (se 1 (by rfl) ⟨1527020, by rfl⟩ : syracuseStep 2036027 = 3054041) B3054041
theorem B89257301 : Blo 2035435 89257301 := bbase (se 13 (by rfl) ⟨16343, by rfl⟩ : syracuseStep 89257301 = 32687) (by norm_num)
theorem B59504867 : Blo 2035435 59504867 := bstep (se 1 (by rfl) ⟨44628650, by rfl⟩ : syracuseStep 59504867 = 89257301) B89257301
theorem B39669911 : Blo 2035435 39669911 := bstep (se 1 (by rfl) ⟨29752433, by rfl⟩ : syracuseStep 39669911 = 59504867) B59504867
theorem B26446607 : Blo 2035435 26446607 := bstep (se 1 (by rfl) ⟨19834955, by rfl⟩ : syracuseStep 26446607 = 39669911) B39669911
theorem B17631071 : Blo 2035435 17631071 := bstep (se 1 (by rfl) ⟨13223303, by rfl⟩ : syracuseStep 17631071 = 26446607) B26446607
theorem B11754047 : Blo 2035435 11754047 := bstep (se 1 (by rfl) ⟨8815535, by rfl⟩ : syracuseStep 11754047 = 17631071) B17631071
theorem B7836031 : Blo 2035435 7836031 := bstep (se 1 (by rfl) ⟨5877023, by rfl⟩ : syracuseStep 7836031 = 11754047) B11754047
theorem B10448041 : Blo 2035435 10448041 := bstep (se 2 (by rfl) ⟨3918015, by rfl⟩ : syracuseStep 10448041 = 7836031) B7836031
theorem B13930721 : Blo 2035435 13930721 := bstep (se 2 (by rfl) ⟨5224020, by rfl⟩ : syracuseStep 13930721 = 10448041) B10448041
theorem B9287147 : Blo 2035435 9287147 := bstep (se 1 (by rfl) ⟨6965360, by rfl⟩ : syracuseStep 9287147 = 13930721) B13930721
theorem B24765725 : Blo 2035435 24765725 := bstep (se 3 (by rfl) ⟨4643573, by rfl⟩ : syracuseStep 24765725 = 9287147) B9287147
theorem B16510483 : Blo 2035435 16510483 := bstep (se 1 (by rfl) ⟨12382862, by rfl⟩ : syracuseStep 16510483 = 24765725) B24765725
theorem B22013977 : Blo 2035435 22013977 := bstep (se 2 (by rfl) ⟨8255241, by rfl⟩ : syracuseStep 22013977 = 16510483) B16510483
theorem B29351969 : Blo 2035435 29351969 := bstep (se 2 (by rfl) ⟨11006988, by rfl⟩ : syracuseStep 29351969 = 22013977) B22013977
theorem B19567979 : Blo 2035435 19567979 := bstep (se 1 (by rfl) ⟨14675984, by rfl⟩ : syracuseStep 19567979 = 29351969) B29351969
theorem B13045319 : Blo 2035435 13045319 := bstep (se 1 (by rfl) ⟨9783989, by rfl⟩ : syracuseStep 13045319 = 19567979) B19567979
theorem B8696879 : Blo 2035435 8696879 := bstep (se 1 (by rfl) ⟨6522659, by rfl⟩ : syracuseStep 8696879 = 13045319) B13045319
theorem B5797919 : Blo 2035435 5797919 := bstep (se 1 (by rfl) ⟨4348439, by rfl⟩ : syracuseStep 5797919 = 8696879) B8696879
theorem B15461117 : Blo 2035435 15461117 := bstep (se 3 (by rfl) ⟨2898959, by rfl⟩ : syracuseStep 15461117 = 5797919) B5797919
theorem B10307411 : Blo 2035435 10307411 := bstep (se 1 (by rfl) ⟨7730558, by rfl⟩ : syracuseStep 10307411 = 15461117) B15461117
theorem B6871607 : Blo 2035435 6871607 := bstep (se 1 (by rfl) ⟨5153705, by rfl⟩ : syracuseStep 6871607 = 10307411) B10307411
theorem B4581071 : Blo 2035435 4581071 := bstep (se 1 (by rfl) ⟨3435803, by rfl⟩ : syracuseStep 4581071 = 6871607) B6871607
theorem B3054047 : Blo 2035435 3054047 := bstep (se 1 (by rfl) ⟨2290535, by rfl⟩ : syracuseStep 3054047 = 4581071) B4581071
theorem B2036031 : Blo 2035435 2036031 := bstep (se 1 (by rfl) ⟨1527023, by rfl⟩ : syracuseStep 2036031 = 3054047) B3054047
theorem B3054053 : Blo 2035435 3054053 := bbase (se 4 (by rfl) ⟨286317, by rfl⟩ : syracuseStep 3054053 = 572635) (by norm_num)
theorem B2036035 : Blo 2035435 2036035 := bstep (se 1 (by rfl) ⟨1527026, by rfl⟩ : syracuseStep 2036035 = 3054053) B3054053
theorem B2513209 : Blo 2035435 2513209 := bbase (se 2 (by rfl) ⟨942453, by rfl⟩ : syracuseStep 2513209 = 1884907) (by norm_num)
theorem B3350945 : Blo 2035435 3350945 := bstep (se 2 (by rfl) ⟨1256604, by rfl⟩ : syracuseStep 3350945 = 2513209) B2513209
theorem B2233963 : Blo 2035435 2233963 := bstep (se 1 (by rfl) ⟨1675472, by rfl⟩ : syracuseStep 2233963 = 3350945) B3350945
theorem B11914469 : Blo 2035435 11914469 := bstep (se 4 (by rfl) ⟨1116981, by rfl⟩ : syracuseStep 11914469 = 2233963) B2233963
theorem B7942979 : Blo 2035435 7942979 := bstep (se 1 (by rfl) ⟨5957234, by rfl⟩ : syracuseStep 7942979 = 11914469) B11914469
theorem B21181277 : Blo 2035435 21181277 := bstep (se 3 (by rfl) ⟨3971489, by rfl⟩ : syracuseStep 21181277 = 7942979) B7942979
theorem B14120851 : Blo 2035435 14120851 := bstep (se 1 (by rfl) ⟨10590638, by rfl⟩ : syracuseStep 14120851 = 21181277) B21181277
theorem B18827801 : Blo 2035435 18827801 := bstep (se 2 (by rfl) ⟨7060425, by rfl⟩ : syracuseStep 18827801 = 14120851) B14120851
theorem B12551867 : Blo 2035435 12551867 := bstep (se 1 (by rfl) ⟨9413900, by rfl⟩ : syracuseStep 12551867 = 18827801) B18827801
theorem B8367911 : Blo 2035435 8367911 := bstep (se 1 (by rfl) ⟨6275933, by rfl⟩ : syracuseStep 8367911 = 12551867) B12551867
theorem B5578607 : Blo 2035435 5578607 := bstep (se 1 (by rfl) ⟨4183955, by rfl⟩ : syracuseStep 5578607 = 8367911) B8367911
theorem B3719071 : Blo 2035435 3719071 := bstep (se 1 (by rfl) ⟨2789303, by rfl⟩ : syracuseStep 3719071 = 5578607) B5578607
theorem B4958761 : Blo 2035435 4958761 := bstep (se 2 (by rfl) ⟨1859535, by rfl⟩ : syracuseStep 4958761 = 3719071) B3719071
theorem B6611681 : Blo 2035435 6611681 := bstep (se 2 (by rfl) ⟨2479380, by rfl⟩ : syracuseStep 6611681 = 4958761) B4958761
theorem B4407787 : Blo 2035435 4407787 := bstep (se 1 (by rfl) ⟨3305840, by rfl⟩ : syracuseStep 4407787 = 6611681) B6611681
theorem B5877049 : Blo 2035435 5877049 := bstep (se 2 (by rfl) ⟨2203893, by rfl⟩ : syracuseStep 5877049 = 4407787) B4407787
theorem B7836065 : Blo 2035435 7836065 := bstep (se 2 (by rfl) ⟨2938524, by rfl⟩ : syracuseStep 7836065 = 5877049) B5877049
theorem B5224043 : Blo 2035435 5224043 := bstep (se 1 (by rfl) ⟨3918032, by rfl⟩ : syracuseStep 5224043 = 7836065) B7836065
theorem B3482695 : Blo 2035435 3482695 := bstep (se 1 (by rfl) ⟨2612021, by rfl⟩ : syracuseStep 3482695 = 5224043) B5224043
theorem B18574373 : Blo 2035435 18574373 := bstep (se 4 (by rfl) ⟨1741347, by rfl⟩ : syracuseStep 18574373 = 3482695) B3482695
theorem B12382915 : Blo 2035435 12382915 := bstep (se 1 (by rfl) ⟨9287186, by rfl⟩ : syracuseStep 12382915 = 18574373) B18574373
theorem B16510553 : Blo 2035435 16510553 := bstep (se 2 (by rfl) ⟨6191457, by rfl⟩ : syracuseStep 16510553 = 12382915) B12382915
theorem B11007035 : Blo 2035435 11007035 := bstep (se 1 (by rfl) ⟨8255276, by rfl⟩ : syracuseStep 11007035 = 16510553) B16510553
theorem B7338023 : Blo 2035435 7338023 := bstep (se 1 (by rfl) ⟨5503517, by rfl⟩ : syracuseStep 7338023 = 11007035) B11007035
theorem B4892015 : Blo 2035435 4892015 := bstep (se 1 (by rfl) ⟨3669011, by rfl⟩ : syracuseStep 4892015 = 7338023) B7338023
theorem B13045373 : Blo 2035435 13045373 := bstep (se 3 (by rfl) ⟨2446007, by rfl⟩ : syracuseStep 13045373 = 4892015) B4892015
theorem B8696915 : Blo 2035435 8696915 := bstep (se 1 (by rfl) ⟨6522686, by rfl⟩ : syracuseStep 8696915 = 13045373) B13045373
theorem B5797943 : Blo 2035435 5797943 := bstep (se 1 (by rfl) ⟨4348457, by rfl⟩ : syracuseStep 5797943 = 8696915) B8696915
theorem B3865295 : Blo 2035435 3865295 := bstep (se 1 (by rfl) ⟨2898971, by rfl⟩ : syracuseStep 3865295 = 5797943) B5797943
theorem B2576863 : Blo 2035435 2576863 := bstep (se 1 (by rfl) ⟨1932647, by rfl⟩ : syracuseStep 2576863 = 3865295) B3865295
theorem B3435817 : Blo 2035435 3435817 := bstep (se 2 (by rfl) ⟨1288431, by rfl⟩ : syracuseStep 3435817 = 2576863) B2576863
theorem B4581089 : Blo 2035435 4581089 := bstep (se 2 (by rfl) ⟨1717908, by rfl⟩ : syracuseStep 4581089 = 3435817) B3435817
theorem B3054059 : Blo 2035435 3054059 := bstep (se 1 (by rfl) ⟨2290544, by rfl⟩ : syracuseStep 3054059 = 4581089) B4581089
theorem B2036039 : Blo 2035435 2036039 := bstep (se 1 (by rfl) ⟨1527029, by rfl⟩ : syracuseStep 2036039 = 3054059) B3054059
theorem B2290549 : Blo 2035435 2290549 := bbase (se 5 (by rfl) ⟨107369, by rfl⟩ : syracuseStep 2290549 = 214739) (by norm_num)
theorem B3054065 : Blo 2035435 3054065 := bstep (se 2 (by rfl) ⟨1145274, by rfl⟩ : syracuseStep 3054065 = 2290549) B2290549
theorem B2036043 : Blo 2035435 2036043 := bstep (se 1 (by rfl) ⟨1527032, by rfl⟩ : syracuseStep 2036043 = 3054065) B3054065
theorem B2576873 : Blo 2035435 2576873 := bbase (se 2 (by rfl) ⟨966327, by rfl⟩ : syracuseStep 2576873 = 1932655) (by norm_num)
theorem B6871661 : Blo 2035435 6871661 := bstep (se 3 (by rfl) ⟨1288436, by rfl⟩ : syracuseStep 6871661 = 2576873) B2576873
theorem B4581107 : Blo 2035435 4581107 := bstep (se 1 (by rfl) ⟨3435830, by rfl⟩ : syracuseStep 4581107 = 6871661) B6871661
theorem B3054071 : Blo 2035435 3054071 := bstep (se 1 (by rfl) ⟨2290553, by rfl⟩ : syracuseStep 3054071 = 4581107) B4581107
theorem B2036047 : Blo 2035435 2036047 := bstep (se 1 (by rfl) ⟨1527035, by rfl⟩ : syracuseStep 2036047 = 3054071) B3054071
theorem B3054077 : Blo 2035435 3054077 := bbase (se 3 (by rfl) ⟨572639, by rfl⟩ : syracuseStep 3054077 = 1145279) (by norm_num)
theorem B2036051 : Blo 2035435 2036051 := bstep (se 1 (by rfl) ⟨1527038, by rfl⟩ : syracuseStep 2036051 = 3054077) B3054077
theorem B4581125 : Blo 2035435 4581125 := bbase (se 4 (by rfl) ⟨429480, by rfl⟩ : syracuseStep 4581125 = 858961) (by norm_num)
theorem B3054083 : Blo 2035435 3054083 := bstep (se 1 (by rfl) ⟨2290562, by rfl⟩ : syracuseStep 3054083 = 4581125) B4581125
theorem B2036055 : Blo 2035435 2036055 := bstep (se 1 (by rfl) ⟨1527041, by rfl⟩ : syracuseStep 2036055 = 3054083) B3054083
theorem B3865333 : Blo 2035435 3865333 := bbase (se 5 (by rfl) ⟨181187, by rfl⟩ : syracuseStep 3865333 = 362375) (by norm_num)
theorem B5153777 : Blo 2035435 5153777 := bstep (se 2 (by rfl) ⟨1932666, by rfl⟩ : syracuseStep 5153777 = 3865333) B3865333
theorem B3435851 : Blo 2035435 3435851 := bstep (se 1 (by rfl) ⟨2576888, by rfl⟩ : syracuseStep 3435851 = 5153777) B5153777
theorem B2290567 : Blo 2035435 2290567 := bstep (se 1 (by rfl) ⟨1717925, by rfl⟩ : syracuseStep 2290567 = 3435851) B3435851
theorem B3054089 : Blo 2035435 3054089 := bstep (se 2 (by rfl) ⟨1145283, by rfl⟩ : syracuseStep 3054089 = 2290567) B2290567
theorem B2036059 : Blo 2035435 2036059 := bstep (se 1 (by rfl) ⟨1527044, by rfl⟩ : syracuseStep 2036059 = 3054089) B3054089
theorem B10307573 : Blo 2035435 10307573 := bbase (se 5 (by rfl) ⟨483167, by rfl⟩ : syracuseStep 10307573 = 966335) (by norm_num)
theorem B6871715 : Blo 2035435 6871715 := bstep (se 1 (by rfl) ⟨5153786, by rfl⟩ : syracuseStep 6871715 = 10307573) B10307573
theorem B4581143 : Blo 2035435 4581143 := bstep (se 1 (by rfl) ⟨3435857, by rfl⟩ : syracuseStep 4581143 = 6871715) B6871715
theorem B3054095 : Blo 2035435 3054095 := bstep (se 1 (by rfl) ⟨2290571, by rfl⟩ : syracuseStep 3054095 = 4581143) B4581143
theorem B2036063 : Blo 2035435 2036063 := bstep (se 1 (by rfl) ⟨1527047, by rfl⟩ : syracuseStep 2036063 = 3054095) B3054095
theorem B3054101 : Blo 2035435 3054101 := bbase (se 6 (by rfl) ⟨71580, by rfl⟩ : syracuseStep 3054101 = 143161) (by norm_num)
theorem B2036067 : Blo 2035435 2036067 := bstep (se 1 (by rfl) ⟨1527050, by rfl⟩ : syracuseStep 2036067 = 3054101) B3054101
theorem B17394101 : Blo 2035435 17394101 := bbase (se 5 (by rfl) ⟨815348, by rfl⟩ : syracuseStep 17394101 = 1630697) (by norm_num)
theorem B11596067 : Blo 2035435 11596067 := bstep (se 1 (by rfl) ⟨8697050, by rfl⟩ : syracuseStep 11596067 = 17394101) B17394101
theorem B7730711 : Blo 2035435 7730711 := bstep (se 1 (by rfl) ⟨5798033, by rfl⟩ : syracuseStep 7730711 = 11596067) B11596067
theorem B5153807 : Blo 2035435 5153807 := bstep (se 1 (by rfl) ⟨3865355, by rfl⟩ : syracuseStep 5153807 = 7730711) B7730711
theorem B3435871 : Blo 2035435 3435871 := bstep (se 1 (by rfl) ⟨2576903, by rfl⟩ : syracuseStep 3435871 = 5153807) B5153807
theorem B4581161 : Blo 2035435 4581161 := bstep (se 2 (by rfl) ⟨1717935, by rfl⟩ : syracuseStep 4581161 = 3435871) B3435871
theorem B3054107 : Blo 2035435 3054107 := bstep (se 1 (by rfl) ⟨2290580, by rfl⟩ : syracuseStep 3054107 = 4581161) B4581161
theorem B2036071 : Blo 2035435 2036071 := bstep (se 1 (by rfl) ⟨1527053, by rfl⟩ : syracuseStep 2036071 = 3054107) B3054107
theorem B2290585 : Blo 2035435 2290585 := bbase (se 2 (by rfl) ⟨858969, by rfl⟩ : syracuseStep 2290585 = 1717939) (by norm_num)
theorem B3054113 : Blo 2035435 3054113 := bstep (se 2 (by rfl) ⟨1145292, by rfl⟩ : syracuseStep 3054113 = 2290585) B2290585
theorem B2036075 : Blo 2035435 2036075 := bstep (se 1 (by rfl) ⟨1527056, by rfl⟩ : syracuseStep 2036075 = 3054113) B3054113
theorem B7730741 : Blo 2035435 7730741 := bbase (se 5 (by rfl) ⟨362378, by rfl⟩ : syracuseStep 7730741 = 724757) (by norm_num)
theorem B5153827 : Blo 2035435 5153827 := bstep (se 1 (by rfl) ⟨3865370, by rfl⟩ : syracuseStep 5153827 = 7730741) B7730741
theorem B6871769 : Blo 2035435 6871769 := bstep (se 2 (by rfl) ⟨2576913, by rfl⟩ : syracuseStep 6871769 = 5153827) B5153827
theorem B4581179 : Blo 2035435 4581179 := bstep (se 1 (by rfl) ⟨3435884, by rfl⟩ : syracuseStep 4581179 = 6871769) B6871769
theorem B3054119 : Blo 2035435 3054119 := bstep (se 1 (by rfl) ⟨2290589, by rfl⟩ : syracuseStep 3054119 = 4581179) B4581179
theorem B2036079 : Blo 2035435 2036079 := bstep (se 1 (by rfl) ⟨1527059, by rfl⟩ : syracuseStep 2036079 = 3054119) B3054119
theorem B3054125 : Blo 2035435 3054125 := bbase (se 3 (by rfl) ⟨572648, by rfl⟩ : syracuseStep 3054125 = 1145297) (by norm_num)
theorem B2036083 : Blo 2035435 2036083 := bstep (se 1 (by rfl) ⟨1527062, by rfl⟩ : syracuseStep 2036083 = 3054125) B3054125
theorem B4581197 : Blo 2035435 4581197 := bbase (se 3 (by rfl) ⟨858974, by rfl⟩ : syracuseStep 4581197 = 1717949) (by norm_num)
theorem B3054131 : Blo 2035435 3054131 := bstep (se 1 (by rfl) ⟨2290598, by rfl⟩ : syracuseStep 3054131 = 4581197) B4581197
theorem B2036087 : Blo 2035435 2036087 := bstep (se 1 (by rfl) ⟨1527065, by rfl⟩ : syracuseStep 2036087 = 3054131) B3054131
theorem B2576929 : Blo 2035435 2576929 := bbase (se 2 (by rfl) ⟨966348, by rfl⟩ : syracuseStep 2576929 = 1932697) (by norm_num)
theorem B3435905 : Blo 2035435 3435905 := bstep (se 2 (by rfl) ⟨1288464, by rfl⟩ : syracuseStep 3435905 = 2576929) B2576929
theorem B2290603 : Blo 2035435 2290603 := bstep (se 1 (by rfl) ⟨1717952, by rfl⟩ : syracuseStep 2290603 = 3435905) B3435905
theorem B3054137 : Blo 2035435 3054137 := bstep (se 2 (by rfl) ⟨1145301, by rfl⟩ : syracuseStep 3054137 = 2290603) B2290603
theorem B2036091 : Blo 2035435 2036091 := bstep (se 1 (by rfl) ⟨1527068, by rfl⟩ : syracuseStep 2036091 = 3054137) B3054137
theorem B23192405 : Blo 2035435 23192405 := bbase (se 9 (by rfl) ⟨67946, by rfl⟩ : syracuseStep 23192405 = 135893) (by norm_num)
theorem B15461603 : Blo 2035435 15461603 := bstep (se 1 (by rfl) ⟨11596202, by rfl⟩ : syracuseStep 15461603 = 23192405) B23192405
theorem B10307735 : Blo 2035435 10307735 := bstep (se 1 (by rfl) ⟨7730801, by rfl⟩ : syracuseStep 10307735 = 15461603) B15461603
theorem B6871823 : Blo 2035435 6871823 := bstep (se 1 (by rfl) ⟨5153867, by rfl⟩ : syracuseStep 6871823 = 10307735) B10307735
theorem B4581215 : Blo 2035435 4581215 := bstep (se 1 (by rfl) ⟨3435911, by rfl⟩ : syracuseStep 4581215 = 6871823) B6871823
theorem B3054143 : Blo 2035435 3054143 := bstep (se 1 (by rfl) ⟨2290607, by rfl⟩ : syracuseStep 3054143 = 4581215) B4581215
theorem B2036095 : Blo 2035435 2036095 := bstep (se 1 (by rfl) ⟨1527071, by rfl⟩ : syracuseStep 2036095 = 3054143) B3054143
theorem B3054149 : Blo 2035435 3054149 := bbase (se 4 (by rfl) ⟨286326, by rfl⟩ : syracuseStep 3054149 = 572653) (by norm_num)
theorem B2036099 : Blo 2035435 2036099 := bstep (se 1 (by rfl) ⟨1527074, by rfl⟩ : syracuseStep 2036099 = 3054149) B3054149
theorem B3435925 : Blo 2035435 3435925 := bbase (se 6 (by rfl) ⟨80529, by rfl⟩ : syracuseStep 3435925 = 161059) (by norm_num)
theorem B4581233 : Blo 2035435 4581233 := bstep (se 2 (by rfl) ⟨1717962, by rfl⟩ : syracuseStep 4581233 = 3435925) B3435925
theorem B3054155 : Blo 2035435 3054155 := bstep (se 1 (by rfl) ⟨2290616, by rfl⟩ : syracuseStep 3054155 = 4581233) B4581233
theorem B2036103 : Blo 2035435 2036103 := bstep (se 1 (by rfl) ⟨1527077, by rfl⟩ : syracuseStep 2036103 = 3054155) B3054155
theorem B2290621 : Blo 2035435 2290621 := bbase (se 3 (by rfl) ⟨429491, by rfl⟩ : syracuseStep 2290621 = 858983) (by norm_num)
theorem B3054161 : Blo 2035435 3054161 := bstep (se 2 (by rfl) ⟨1145310, by rfl⟩ : syracuseStep 3054161 = 2290621) B2290621
theorem B2036107 : Blo 2035435 2036107 := bstep (se 1 (by rfl) ⟨1527080, by rfl⟩ : syracuseStep 2036107 = 3054161) B3054161
theorem B6871877 : Blo 2035435 6871877 := bbase (se 4 (by rfl) ⟨644238, by rfl⟩ : syracuseStep 6871877 = 1288477) (by norm_num)
theorem B4581251 : Blo 2035435 4581251 := bstep (se 1 (by rfl) ⟨3435938, by rfl⟩ : syracuseStep 4581251 = 6871877) B6871877
theorem B3054167 : Blo 2035435 3054167 := bstep (se 1 (by rfl) ⟨2290625, by rfl⟩ : syracuseStep 3054167 = 4581251) B4581251
theorem B2036111 : Blo 2035435 2036111 := bstep (se 1 (by rfl) ⟨1527083, by rfl⟩ : syracuseStep 2036111 = 3054167) B3054167
theorem B3054173 : Blo 2035435 3054173 := bbase (se 3 (by rfl) ⟨572657, by rfl⟩ : syracuseStep 3054173 = 1145315) (by norm_num)
theorem B2036115 : Blo 2035435 2036115 := bstep (se 1 (by rfl) ⟨1527086, by rfl⟩ : syracuseStep 2036115 = 3054173) B3054173
theorem B4581269 : Blo 2035435 4581269 := bbase (se 6 (by rfl) ⟨107373, by rfl⟩ : syracuseStep 4581269 = 214747) (by norm_num)
theorem B3054179 : Blo 2035435 3054179 := bstep (se 1 (by rfl) ⟨2290634, by rfl⟩ : syracuseStep 3054179 = 4581269) B4581269
theorem B2036119 : Blo 2035435 2036119 := bstep (se 1 (by rfl) ⟨1527089, by rfl⟩ : syracuseStep 2036119 = 3054179) B3054179
theorem B4348637 : Blo 2035435 4348637 := bbase (se 3 (by rfl) ⟨815369, by rfl⟩ : syracuseStep 4348637 = 1630739) (by norm_num)
theorem B2899091 : Blo 2035435 2899091 := bstep (se 1 (by rfl) ⟨2174318, by rfl⟩ : syracuseStep 2899091 = 4348637) B4348637
theorem B7730909 : Blo 2035435 7730909 := bstep (se 3 (by rfl) ⟨1449545, by rfl⟩ : syracuseStep 7730909 = 2899091) B2899091
theorem B5153939 : Blo 2035435 5153939 := bstep (se 1 (by rfl) ⟨3865454, by rfl⟩ : syracuseStep 5153939 = 7730909) B7730909
theorem B3435959 : Blo 2035435 3435959 := bstep (se 1 (by rfl) ⟨2576969, by rfl⟩ : syracuseStep 3435959 = 5153939) B5153939
theorem B2290639 : Blo 2035435 2290639 := bstep (se 1 (by rfl) ⟨1717979, by rfl⟩ : syracuseStep 2290639 = 3435959) B3435959
theorem B3054185 : Blo 2035435 3054185 := bstep (se 2 (by rfl) ⟨1145319, by rfl⟩ : syracuseStep 3054185 = 2290639) B2290639
theorem B2036123 : Blo 2035435 2036123 := bstep (se 1 (by rfl) ⟨1527092, by rfl⟩ : syracuseStep 2036123 = 3054185) B3054185
theorem B2751877 : Blo 2035435 2751877 := bbase (se 4 (by rfl) ⟨257988, by rfl⟩ : syracuseStep 2751877 = 515977) (by norm_num)
theorem B14676677 : Blo 2035435 14676677 := bstep (se 4 (by rfl) ⟨1375938, by rfl⟩ : syracuseStep 14676677 = 2751877) B2751877
theorem B9784451 : Blo 2035435 9784451 := bstep (se 1 (by rfl) ⟨7338338, by rfl⟩ : syracuseStep 9784451 = 14676677) B14676677
theorem B6522967 : Blo 2035435 6522967 := bstep (se 1 (by rfl) ⟨4892225, by rfl⟩ : syracuseStep 6522967 = 9784451) B9784451
theorem B8697289 : Blo 2035435 8697289 := bstep (se 2 (by rfl) ⟨3261483, by rfl⟩ : syracuseStep 8697289 = 6522967) B6522967
theorem B11596385 : Blo 2035435 11596385 := bstep (se 2 (by rfl) ⟨4348644, by rfl⟩ : syracuseStep 11596385 = 8697289) B8697289
theorem B7730923 : Blo 2035435 7730923 := bstep (se 1 (by rfl) ⟨5798192, by rfl⟩ : syracuseStep 7730923 = 11596385) B11596385
theorem B10307897 : Blo 2035435 10307897 := bstep (se 2 (by rfl) ⟨3865461, by rfl⟩ : syracuseStep 10307897 = 7730923) B7730923
theorem B6871931 : Blo 2035435 6871931 := bstep (se 1 (by rfl) ⟨5153948, by rfl⟩ : syracuseStep 6871931 = 10307897) B10307897
theorem B4581287 : Blo 2035435 4581287 := bstep (se 1 (by rfl) ⟨3435965, by rfl⟩ : syracuseStep 4581287 = 6871931) B6871931
theorem B3054191 : Blo 2035435 3054191 := bstep (se 1 (by rfl) ⟨2290643, by rfl⟩ : syracuseStep 3054191 = 4581287) B4581287
theorem B2036127 : Blo 2035435 2036127 := bstep (se 1 (by rfl) ⟨1527095, by rfl⟩ : syracuseStep 2036127 = 3054191) B3054191
theorem B3054197 : Blo 2035435 3054197 := bbase (se 5 (by rfl) ⟨143165, by rfl⟩ : syracuseStep 3054197 = 286331) (by norm_num)
theorem B2036131 : Blo 2035435 2036131 := bstep (se 1 (by rfl) ⟨1527098, by rfl⟩ : syracuseStep 2036131 = 3054197) B3054197
theorem B3865477 : Blo 2035435 3865477 := bbase (se 4 (by rfl) ⟨362388, by rfl⟩ : syracuseStep 3865477 = 724777) (by norm_num)
theorem B5153969 : Blo 2035435 5153969 := bstep (se 2 (by rfl) ⟨1932738, by rfl⟩ : syracuseStep 5153969 = 3865477) B3865477
theorem B3435979 : Blo 2035435 3435979 := bstep (se 1 (by rfl) ⟨2576984, by rfl⟩ : syracuseStep 3435979 = 5153969) B5153969
theorem B4581305 : Blo 2035435 4581305 := bstep (se 2 (by rfl) ⟨1717989, by rfl⟩ : syracuseStep 4581305 = 3435979) B3435979
theorem B3054203 : Blo 2035435 3054203 := bstep (se 1 (by rfl) ⟨2290652, by rfl⟩ : syracuseStep 3054203 = 4581305) B4581305
theorem B2036135 : Blo 2035435 2036135 := bstep (se 1 (by rfl) ⟨1527101, by rfl⟩ : syracuseStep 2036135 = 3054203) B3054203
theorem B2290657 : Blo 2035435 2290657 := bbase (se 2 (by rfl) ⟨858996, by rfl⟩ : syracuseStep 2290657 = 1717993) (by norm_num)
theorem B3054209 : Blo 2035435 3054209 := bstep (se 2 (by rfl) ⟨1145328, by rfl⟩ : syracuseStep 3054209 = 2290657) B2290657
theorem B2036139 : Blo 2035435 2036139 := bstep (se 1 (by rfl) ⟨1527104, by rfl⟩ : syracuseStep 2036139 = 3054209) B3054209
theorem B5153989 : Blo 2035435 5153989 := bbase (se 4 (by rfl) ⟨483186, by rfl⟩ : syracuseStep 5153989 = 966373) (by norm_num)
theorem B6871985 : Blo 2035435 6871985 := bstep (se 2 (by rfl) ⟨2576994, by rfl⟩ : syracuseStep 6871985 = 5153989) B5153989
theorem B4581323 : Blo 2035435 4581323 := bstep (se 1 (by rfl) ⟨3435992, by rfl⟩ : syracuseStep 4581323 = 6871985) B6871985
theorem B3054215 : Blo 2035435 3054215 := bstep (se 1 (by rfl) ⟨2290661, by rfl⟩ : syracuseStep 3054215 = 4581323) B4581323
theorem B2036143 : Blo 2035435 2036143 := bstep (se 1 (by rfl) ⟨1527107, by rfl⟩ : syracuseStep 2036143 = 3054215) B3054215
theorem B3054221 : Blo 2035435 3054221 := bbase (se 3 (by rfl) ⟨572666, by rfl⟩ : syracuseStep 3054221 = 1145333) (by norm_num)
theorem B2036147 : Blo 2035435 2036147 := bstep (se 1 (by rfl) ⟨1527110, by rfl⟩ : syracuseStep 2036147 = 3054221) B3054221
theorem B4581341 : Blo 2035435 4581341 := bbase (se 3 (by rfl) ⟨859001, by rfl⟩ : syracuseStep 4581341 = 1718003) (by norm_num)
theorem B3054227 : Blo 2035435 3054227 := bstep (se 1 (by rfl) ⟨2290670, by rfl⟩ : syracuseStep 3054227 = 4581341) B4581341
theorem B2036151 : Blo 2035435 2036151 := bstep (se 1 (by rfl) ⟨1527113, by rfl⟩ : syracuseStep 2036151 = 3054227) B3054227
theorem B3436013 : Blo 2035435 3436013 := bbase (se 3 (by rfl) ⟨644252, by rfl⟩ : syracuseStep 3436013 = 1288505) (by norm_num)
theorem B2290675 : Blo 2035435 2290675 := bstep (se 1 (by rfl) ⟨1718006, by rfl⟩ : syracuseStep 2290675 = 3436013) B3436013
theorem B3054233 : Blo 2035435 3054233 := bstep (se 2 (by rfl) ⟨1145337, by rfl⟩ : syracuseStep 3054233 = 2290675) B2290675
theorem B2036155 : Blo 2035435 2036155 := bstep (se 1 (by rfl) ⟨1527116, by rfl⟩ : syracuseStep 2036155 = 3054233) B3054233
theorem B17872757 : Blo 2035435 17872757 := bbase (se 5 (by rfl) ⟨837785, by rfl⟩ : syracuseStep 17872757 = 1675571) (by norm_num)
theorem B11915171 : Blo 2035435 11915171 := bstep (se 1 (by rfl) ⟨8936378, by rfl⟩ : syracuseStep 11915171 = 17872757) B17872757
theorem B7943447 : Blo 2035435 7943447 := bstep (se 1 (by rfl) ⟨5957585, by rfl⟩ : syracuseStep 7943447 = 11915171) B11915171
theorem B5295631 : Blo 2035435 5295631 := bstep (se 1 (by rfl) ⟨3971723, by rfl⟩ : syracuseStep 5295631 = 7943447) B7943447
theorem B7060841 : Blo 2035435 7060841 := bstep (se 2 (by rfl) ⟨2647815, by rfl⟩ : syracuseStep 7060841 = 5295631) B5295631
theorem B4707227 : Blo 2035435 4707227 := bstep (se 1 (by rfl) ⟨3530420, by rfl⟩ : syracuseStep 4707227 = 7060841) B7060841
theorem B3138151 : Blo 2035435 3138151 := bstep (se 1 (by rfl) ⟨2353613, by rfl⟩ : syracuseStep 3138151 = 4707227) B4707227
theorem B4184201 : Blo 2035435 4184201 := bstep (se 2 (by rfl) ⟨1569075, by rfl⟩ : syracuseStep 4184201 = 3138151) B3138151
theorem B11157869 : Blo 2035435 11157869 := bstep (se 3 (by rfl) ⟨2092100, by rfl⟩ : syracuseStep 11157869 = 4184201) B4184201
theorem B29754317 : Blo 2035435 29754317 := bstep (se 3 (by rfl) ⟨5578934, by rfl⟩ : syracuseStep 29754317 = 11157869) B11157869
theorem B19836211 : Blo 2035435 19836211 := bstep (se 1 (by rfl) ⟨14877158, by rfl⟩ : syracuseStep 19836211 = 29754317) B29754317
theorem B26448281 : Blo 2035435 26448281 := bstep (se 2 (by rfl) ⟨9918105, by rfl⟩ : syracuseStep 26448281 = 19836211) B19836211
theorem B17632187 : Blo 2035435 17632187 := bstep (se 1 (by rfl) ⟨13224140, by rfl⟩ : syracuseStep 17632187 = 26448281) B26448281
theorem B11754791 : Blo 2035435 11754791 := bstep (se 1 (by rfl) ⟨8816093, by rfl⟩ : syracuseStep 11754791 = 17632187) B17632187
theorem B7836527 : Blo 2035435 7836527 := bstep (se 1 (by rfl) ⟨5877395, by rfl⟩ : syracuseStep 7836527 = 11754791) B11754791
theorem B5224351 : Blo 2035435 5224351 := bstep (se 1 (by rfl) ⟨3918263, by rfl⟩ : syracuseStep 5224351 = 7836527) B7836527
theorem B6965801 : Blo 2035435 6965801 := bstep (se 2 (by rfl) ⟨2612175, by rfl⟩ : syracuseStep 6965801 = 5224351) B5224351
theorem B4643867 : Blo 2035435 4643867 := bstep (se 1 (by rfl) ⟨3482900, by rfl⟩ : syracuseStep 4643867 = 6965801) B6965801
theorem B3095911 : Blo 2035435 3095911 := bstep (se 1 (by rfl) ⟨2321933, by rfl⟩ : syracuseStep 3095911 = 4643867) B4643867
theorem B4127881 : Blo 2035435 4127881 := bstep (se 2 (by rfl) ⟨1547955, by rfl⟩ : syracuseStep 4127881 = 3095911) B3095911
theorem B5503841 : Blo 2035435 5503841 := bstep (se 2 (by rfl) ⟨2063940, by rfl⟩ : syracuseStep 5503841 = 4127881) B4127881
theorem B3669227 : Blo 2035435 3669227 := bstep (se 1 (by rfl) ⟨2751920, by rfl⟩ : syracuseStep 3669227 = 5503841) B5503841
theorem B2446151 : Blo 2035435 2446151 := bstep (se 1 (by rfl) ⟨1834613, by rfl⟩ : syracuseStep 2446151 = 3669227) B3669227
theorem B26092277 : Blo 2035435 26092277 := bstep (se 5 (by rfl) ⟨1223075, by rfl⟩ : syracuseStep 26092277 = 2446151) B2446151
theorem B17394851 : Blo 2035435 17394851 := bstep (se 1 (by rfl) ⟨13046138, by rfl⟩ : syracuseStep 17394851 = 26092277) B26092277
theorem B11596567 : Blo 2035435 11596567 := bstep (se 1 (by rfl) ⟨8697425, by rfl⟩ : syracuseStep 11596567 = 17394851) B17394851
theorem B15462089 : Blo 2035435 15462089 := bstep (se 2 (by rfl) ⟨5798283, by rfl⟩ : syracuseStep 15462089 = 11596567) B11596567
theorem B10308059 : Blo 2035435 10308059 := bstep (se 1 (by rfl) ⟨7731044, by rfl⟩ : syracuseStep 10308059 = 15462089) B15462089
theorem B6872039 : Blo 2035435 6872039 := bstep (se 1 (by rfl) ⟨5154029, by rfl⟩ : syracuseStep 6872039 = 10308059) B10308059
theorem B4581359 : Blo 2035435 4581359 := bstep (se 1 (by rfl) ⟨3436019, by rfl⟩ : syracuseStep 4581359 = 6872039) B6872039
theorem B3054239 : Blo 2035435 3054239 := bstep (se 1 (by rfl) ⟨2290679, by rfl⟩ : syracuseStep 3054239 = 4581359) B4581359
theorem B2036159 : Blo 2035435 2036159 := bstep (se 1 (by rfl) ⟨1527119, by rfl⟩ : syracuseStep 2036159 = 3054239) B3054239
theorem B3054245 : Blo 2035435 3054245 := bbase (se 4 (by rfl) ⟨286335, by rfl⟩ : syracuseStep 3054245 = 572671) (by norm_num)
theorem B2036163 : Blo 2035435 2036163 := bstep (se 1 (by rfl) ⟨1527122, by rfl⟩ : syracuseStep 2036163 = 3054245) B3054245
theorem B2577025 : Blo 2035435 2577025 := bbase (se 2 (by rfl) ⟨966384, by rfl⟩ : syracuseStep 2577025 = 1932769) (by norm_num)
theorem B3436033 : Blo 2035435 3436033 := bstep (se 2 (by rfl) ⟨1288512, by rfl⟩ : syracuseStep 3436033 = 2577025) B2577025
theorem B4581377 : Blo 2035435 4581377 := bstep (se 2 (by rfl) ⟨1718016, by rfl⟩ : syracuseStep 4581377 = 3436033) B3436033
theorem B3054251 : Blo 2035435 3054251 := bstep (se 1 (by rfl) ⟨2290688, by rfl⟩ : syracuseStep 3054251 = 4581377) B4581377
theorem B2036167 : Blo 2035435 2036167 := bstep (se 1 (by rfl) ⟨1527125, by rfl⟩ : syracuseStep 2036167 = 3054251) B3054251
theorem B2290693 : Blo 2035435 2290693 := bbase (se 4 (by rfl) ⟨214752, by rfl⟩ : syracuseStep 2290693 = 429505) (by norm_num)
theorem B3054257 : Blo 2035435 3054257 := bstep (se 2 (by rfl) ⟨1145346, by rfl⟩ : syracuseStep 3054257 = 2290693) B2290693
theorem B2036171 : Blo 2035435 2036171 := bstep (se 1 (by rfl) ⟨1527128, by rfl⟩ : syracuseStep 2036171 = 3054257) B3054257
theorem B2899165 : Blo 2035435 2899165 := bbase (se 3 (by rfl) ⟨543593, by rfl⟩ : syracuseStep 2899165 = 1087187) (by norm_num)
theorem B3865553 : Blo 2035435 3865553 := bstep (se 2 (by rfl) ⟨1449582, by rfl⟩ : syracuseStep 3865553 = 2899165) B2899165
theorem B2577035 : Blo 2035435 2577035 := bstep (se 1 (by rfl) ⟨1932776, by rfl⟩ : syracuseStep 2577035 = 3865553) B3865553
theorem B6872093 : Blo 2035435 6872093 := bstep (se 3 (by rfl) ⟨1288517, by rfl⟩ : syracuseStep 6872093 = 2577035) B2577035
theorem B4581395 : Blo 2035435 4581395 := bstep (se 1 (by rfl) ⟨3436046, by rfl⟩ : syracuseStep 4581395 = 6872093) B6872093
theorem B3054263 : Blo 2035435 3054263 := bstep (se 1 (by rfl) ⟨2290697, by rfl⟩ : syracuseStep 3054263 = 4581395) B4581395
theorem B2036175 : Blo 2035435 2036175 := bstep (se 1 (by rfl) ⟨1527131, by rfl⟩ : syracuseStep 2036175 = 3054263) B3054263
theorem B3054269 : Blo 2035435 3054269 := bbase (se 3 (by rfl) ⟨572675, by rfl⟩ : syracuseStep 3054269 = 1145351) (by norm_num)
theorem B2036179 : Blo 2035435 2036179 := bstep (se 1 (by rfl) ⟨1527134, by rfl⟩ : syracuseStep 2036179 = 3054269) B3054269
theorem B4581413 : Blo 2035435 4581413 := bbase (se 4 (by rfl) ⟨429507, by rfl⟩ : syracuseStep 4581413 = 859015) (by norm_num)
theorem B3054275 : Blo 2035435 3054275 := bstep (se 1 (by rfl) ⟨2290706, by rfl⟩ : syracuseStep 3054275 = 4581413) B4581413
theorem B2036183 : Blo 2035435 2036183 := bstep (se 1 (by rfl) ⟨1527137, by rfl⟩ : syracuseStep 2036183 = 3054275) B3054275
theorem B5154101 : Blo 2035435 5154101 := bbase (se 5 (by rfl) ⟨241598, by rfl⟩ : syracuseStep 5154101 = 483197) (by norm_num)
theorem B3436067 : Blo 2035435 3436067 := bstep (se 1 (by rfl) ⟨2577050, by rfl⟩ : syracuseStep 3436067 = 5154101) B5154101
theorem B2290711 : Blo 2035435 2290711 := bstep (se 1 (by rfl) ⟨1718033, by rfl⟩ : syracuseStep 2290711 = 3436067) B3436067
theorem B3054281 : Blo 2035435 3054281 := bstep (se 2 (by rfl) ⟨1145355, by rfl⟩ : syracuseStep 3054281 = 2290711) B2290711
theorem B2036187 : Blo 2035435 2036187 := bstep (se 1 (by rfl) ⟨1527140, by rfl⟩ : syracuseStep 2036187 = 3054281) B3054281
theorem B6965909 : Blo 2035435 6965909 := bbase (se 6 (by rfl) ⟨163263, by rfl⟩ : syracuseStep 6965909 = 326527) (by norm_num)
theorem B4643939 : Blo 2035435 4643939 := bstep (se 1 (by rfl) ⟨3482954, by rfl⟩ : syracuseStep 4643939 = 6965909) B6965909
theorem B12383837 : Blo 2035435 12383837 := bstep (se 3 (by rfl) ⟨2321969, by rfl⟩ : syracuseStep 12383837 = 4643939) B4643939
theorem B8255891 : Blo 2035435 8255891 := bstep (se 1 (by rfl) ⟨6191918, by rfl⟩ : syracuseStep 8255891 = 12383837) B12383837
theorem B22015709 : Blo 2035435 22015709 := bstep (se 3 (by rfl) ⟨4127945, by rfl⟩ : syracuseStep 22015709 = 8255891) B8255891
theorem B14677139 : Blo 2035435 14677139 := bstep (se 1 (by rfl) ⟨11007854, by rfl⟩ : syracuseStep 14677139 = 22015709) B22015709
theorem B9784759 : Blo 2035435 9784759 := bstep (se 1 (by rfl) ⟨7338569, by rfl⟩ : syracuseStep 9784759 = 14677139) B14677139
theorem B13046345 : Blo 2035435 13046345 := bstep (se 2 (by rfl) ⟨4892379, by rfl⟩ : syracuseStep 13046345 = 9784759) B9784759
theorem B8697563 : Blo 2035435 8697563 := bstep (se 1 (by rfl) ⟨6523172, by rfl⟩ : syracuseStep 8697563 = 13046345) B13046345
theorem B5798375 : Blo 2035435 5798375 := bstep (se 1 (by rfl) ⟨4348781, by rfl⟩ : syracuseStep 5798375 = 8697563) B8697563
theorem B3865583 : Blo 2035435 3865583 := bstep (se 1 (by rfl) ⟨2899187, by rfl⟩ : syracuseStep 3865583 = 5798375) B5798375
theorem B10308221 : Blo 2035435 10308221 := bstep (se 3 (by rfl) ⟨1932791, by rfl⟩ : syracuseStep 10308221 = 3865583) B3865583
theorem B6872147 : Blo 2035435 6872147 := bstep (se 1 (by rfl) ⟨5154110, by rfl⟩ : syracuseStep 6872147 = 10308221) B10308221
theorem B4581431 : Blo 2035435 4581431 := bstep (se 1 (by rfl) ⟨3436073, by rfl⟩ : syracuseStep 4581431 = 6872147) B6872147
theorem B3054287 : Blo 2035435 3054287 := bstep (se 1 (by rfl) ⟨2290715, by rfl⟩ : syracuseStep 3054287 = 4581431) B4581431
theorem B2036191 : Blo 2035435 2036191 := bstep (se 1 (by rfl) ⟨1527143, by rfl⟩ : syracuseStep 2036191 = 3054287) B3054287
theorem B3054293 : Blo 2035435 3054293 := bbase (se 7 (by rfl) ⟨35792, by rfl⟩ : syracuseStep 3054293 = 71585) (by norm_num)
theorem B2036195 : Blo 2035435 2036195 := bstep (se 1 (by rfl) ⟨1527146, by rfl⟩ : syracuseStep 2036195 = 3054293) B3054293
theorem B4959149 : Blo 2035435 4959149 := bbase (se 3 (by rfl) ⟨929840, by rfl⟩ : syracuseStep 4959149 = 1859681) (by norm_num)
theorem B13224397 : Blo 2035435 13224397 := bstep (se 3 (by rfl) ⟨2479574, by rfl⟩ : syracuseStep 13224397 = 4959149) B4959149
theorem B17632529 : Blo 2035435 17632529 := bstep (se 2 (by rfl) ⟨6612198, by rfl⟩ : syracuseStep 17632529 = 13224397) B13224397
theorem B11755019 : Blo 2035435 11755019 := bstep (se 1 (by rfl) ⟨8816264, by rfl⟩ : syracuseStep 11755019 = 17632529) B17632529
theorem B7836679 : Blo 2035435 7836679 := bstep (se 1 (by rfl) ⟨5877509, by rfl⟩ : syracuseStep 7836679 = 11755019) B11755019
theorem B41795621 : Blo 2035435 41795621 := bstep (se 4 (by rfl) ⟨3918339, by rfl⟩ : syracuseStep 41795621 = 7836679) B7836679
theorem B27863747 : Blo 2035435 27863747 := bstep (se 1 (by rfl) ⟨20897810, by rfl⟩ : syracuseStep 27863747 = 41795621) B41795621
theorem B18575831 : Blo 2035435 18575831 := bstep (se 1 (by rfl) ⟨13931873, by rfl⟩ : syracuseStep 18575831 = 27863747) B27863747
theorem B49535549 : Blo 2035435 49535549 := bstep (se 3 (by rfl) ⟨9287915, by rfl⟩ : syracuseStep 49535549 = 18575831) B18575831
theorem B33023699 : Blo 2035435 33023699 := bstep (se 1 (by rfl) ⟨24767774, by rfl⟩ : syracuseStep 33023699 = 49535549) B49535549
theorem B22015799 : Blo 2035435 22015799 := bstep (se 1 (by rfl) ⟨16511849, by rfl⟩ : syracuseStep 22015799 = 33023699) B33023699
theorem B14677199 : Blo 2035435 14677199 := bstep (se 1 (by rfl) ⟨11007899, by rfl⟩ : syracuseStep 14677199 = 22015799) B22015799
theorem B9784799 : Blo 2035435 9784799 := bstep (se 1 (by rfl) ⟨7338599, by rfl⟩ : syracuseStep 9784799 = 14677199) B14677199
theorem B6523199 : Blo 2035435 6523199 := bstep (se 1 (by rfl) ⟨4892399, by rfl⟩ : syracuseStep 6523199 = 9784799) B9784799
theorem B4348799 : Blo 2035435 4348799 := bstep (se 1 (by rfl) ⟨3261599, by rfl⟩ : syracuseStep 4348799 = 6523199) B6523199
theorem B2899199 : Blo 2035435 2899199 := bstep (se 1 (by rfl) ⟨2174399, by rfl⟩ : syracuseStep 2899199 = 4348799) B4348799
theorem B7731197 : Blo 2035435 7731197 := bstep (se 3 (by rfl) ⟨1449599, by rfl⟩ : syracuseStep 7731197 = 2899199) B2899199
theorem B5154131 : Blo 2035435 5154131 := bstep (se 1 (by rfl) ⟨3865598, by rfl⟩ : syracuseStep 5154131 = 7731197) B7731197
theorem B3436087 : Blo 2035435 3436087 := bstep (se 1 (by rfl) ⟨2577065, by rfl⟩ : syracuseStep 3436087 = 5154131) B5154131
theorem B4581449 : Blo 2035435 4581449 := bstep (se 2 (by rfl) ⟨1718043, by rfl⟩ : syracuseStep 4581449 = 3436087) B3436087
theorem B3054299 : Blo 2035435 3054299 := bstep (se 1 (by rfl) ⟨2290724, by rfl⟩ : syracuseStep 3054299 = 4581449) B4581449
theorem B2036199 : Blo 2035435 2036199 := bstep (se 1 (by rfl) ⟨1527149, by rfl⟩ : syracuseStep 2036199 = 3054299) B3054299
theorem B2290729 : Blo 2035435 2290729 := bbase (se 2 (by rfl) ⟨859023, by rfl⟩ : syracuseStep 2290729 = 1718047) (by norm_num)
theorem B3054305 : Blo 2035435 3054305 := bstep (se 2 (by rfl) ⟨1145364, by rfl⟩ : syracuseStep 3054305 = 2290729) B2290729
theorem B2036203 : Blo 2035435 2036203 := bstep (se 1 (by rfl) ⟨1527152, by rfl⟩ : syracuseStep 2036203 = 3054305) B3054305
theorem B7836709 : Blo 2035435 7836709 := bbase (se 4 (by rfl) ⟨734691, by rfl⟩ : syracuseStep 7836709 = 1469383) (by norm_num)
theorem B10448945 : Blo 2035435 10448945 := bstep (se 2 (by rfl) ⟨3918354, by rfl⟩ : syracuseStep 10448945 = 7836709) B7836709
theorem B6965963 : Blo 2035435 6965963 := bstep (se 1 (by rfl) ⟨5224472, by rfl⟩ : syracuseStep 6965963 = 10448945) B10448945
theorem B4643975 : Blo 2035435 4643975 := bstep (se 1 (by rfl) ⟨3482981, by rfl⟩ : syracuseStep 4643975 = 6965963) B6965963
theorem B12383933 : Blo 2035435 12383933 := bstep (se 3 (by rfl) ⟨2321987, by rfl⟩ : syracuseStep 12383933 = 4643975) B4643975
theorem B33023821 : Blo 2035435 33023821 := bstep (se 3 (by rfl) ⟨6191966, by rfl⟩ : syracuseStep 33023821 = 12383933) B12383933
theorem B44031761 : Blo 2035435 44031761 := bstep (se 2 (by rfl) ⟨16511910, by rfl⟩ : syracuseStep 44031761 = 33023821) B33023821
theorem B29354507 : Blo 2035435 29354507 := bstep (se 1 (by rfl) ⟨22015880, by rfl⟩ : syracuseStep 29354507 = 44031761) B44031761
theorem B19569671 : Blo 2035435 19569671 := bstep (se 1 (by rfl) ⟨14677253, by rfl⟩ : syracuseStep 19569671 = 29354507) B29354507
theorem B13046447 : Blo 2035435 13046447 := bstep (se 1 (by rfl) ⟨9784835, by rfl⟩ : syracuseStep 13046447 = 19569671) B19569671
theorem B8697631 : Blo 2035435 8697631 := bstep (se 1 (by rfl) ⟨6523223, by rfl⟩ : syracuseStep 8697631 = 13046447) B13046447
theorem B11596841 : Blo 2035435 11596841 := bstep (se 2 (by rfl) ⟨4348815, by rfl⟩ : syracuseStep 11596841 = 8697631) B8697631
theorem B7731227 : Blo 2035435 7731227 := bstep (se 1 (by rfl) ⟨5798420, by rfl⟩ : syracuseStep 7731227 = 11596841) B11596841
theorem B5154151 : Blo 2035435 5154151 := bstep (se 1 (by rfl) ⟨3865613, by rfl⟩ : syracuseStep 5154151 = 7731227) B7731227
theorem B6872201 : Blo 2035435 6872201 := bstep (se 2 (by rfl) ⟨2577075, by rfl⟩ : syracuseStep 6872201 = 5154151) B5154151
theorem B4581467 : Blo 2035435 4581467 := bstep (se 1 (by rfl) ⟨3436100, by rfl⟩ : syracuseStep 4581467 = 6872201) B6872201
theorem B3054311 : Blo 2035435 3054311 := bstep (se 1 (by rfl) ⟨2290733, by rfl⟩ : syracuseStep 3054311 = 4581467) B4581467
theorem B2036207 : Blo 2035435 2036207 := bstep (se 1 (by rfl) ⟨1527155, by rfl⟩ : syracuseStep 2036207 = 3054311) B3054311
theorem B3054317 : Blo 2035435 3054317 := bbase (se 3 (by rfl) ⟨572684, by rfl⟩ : syracuseStep 3054317 = 1145369) (by norm_num)
theorem B2036211 : Blo 2035435 2036211 := bstep (se 1 (by rfl) ⟨1527158, by rfl⟩ : syracuseStep 2036211 = 3054317) B3054317
theorem B4581485 : Blo 2035435 4581485 := bbase (se 3 (by rfl) ⟨859028, by rfl⟩ : syracuseStep 4581485 = 1718057) (by norm_num)
theorem B3054323 : Blo 2035435 3054323 := bstep (se 1 (by rfl) ⟨2290742, by rfl⟩ : syracuseStep 3054323 = 4581485) B4581485
theorem B2036215 : Blo 2035435 2036215 := bstep (se 1 (by rfl) ⟨1527161, by rfl⟩ : syracuseStep 2036215 = 3054323) B3054323
theorem B3865637 : Blo 2035435 3865637 := bbase (se 4 (by rfl) ⟨362403, by rfl⟩ : syracuseStep 3865637 = 724807) (by norm_num)
theorem B2577091 : Blo 2035435 2577091 := bstep (se 1 (by rfl) ⟨1932818, by rfl⟩ : syracuseStep 2577091 = 3865637) B3865637
theorem B3436121 : Blo 2035435 3436121 := bstep (se 2 (by rfl) ⟨1288545, by rfl⟩ : syracuseStep 3436121 = 2577091) B2577091
theorem B2290747 : Blo 2035435 2290747 := bstep (se 1 (by rfl) ⟨1718060, by rfl⟩ : syracuseStep 2290747 = 3436121) B3436121
theorem B3054329 : Blo 2035435 3054329 := bstep (se 2 (by rfl) ⟨1145373, by rfl⟩ : syracuseStep 3054329 = 2290747) B2290747
theorem B2036219 : Blo 2035435 2036219 := bstep (se 1 (by rfl) ⟨1527164, by rfl⟩ : syracuseStep 2036219 = 3054329) B3054329
theorem B2938789 : Blo 2035435 2938789 := bbase (se 4 (by rfl) ⟨275511, by rfl⟩ : syracuseStep 2938789 = 551023) (by norm_num)
theorem B3918385 : Blo 2035435 3918385 := bstep (se 2 (by rfl) ⟨1469394, by rfl⟩ : syracuseStep 3918385 = 2938789) B2938789
theorem B5224513 : Blo 2035435 5224513 := bstep (se 2 (by rfl) ⟨1959192, by rfl⟩ : syracuseStep 5224513 = 3918385) B3918385
theorem B6966017 : Blo 2035435 6966017 := bstep (se 2 (by rfl) ⟨2612256, by rfl⟩ : syracuseStep 6966017 = 5224513) B5224513
theorem B4644011 : Blo 2035435 4644011 := bstep (se 1 (by rfl) ⟨3483008, by rfl⟩ : syracuseStep 4644011 = 6966017) B6966017
theorem B12384029 : Blo 2035435 12384029 := bstep (se 3 (by rfl) ⟨2322005, by rfl⟩ : syracuseStep 12384029 = 4644011) B4644011
theorem B33024077 : Blo 2035435 33024077 := bstep (se 3 (by rfl) ⟨6192014, by rfl⟩ : syracuseStep 33024077 = 12384029) B12384029
theorem B22016051 : Blo 2035435 22016051 := bstep (se 1 (by rfl) ⟨16512038, by rfl⟩ : syracuseStep 22016051 = 33024077) B33024077
theorem B14677367 : Blo 2035435 14677367 := bstep (se 1 (by rfl) ⟨11008025, by rfl⟩ : syracuseStep 14677367 = 22016051) B22016051
theorem B39139645 : Blo 2035435 39139645 := bstep (se 3 (by rfl) ⟨7338683, by rfl⟩ : syracuseStep 39139645 = 14677367) B14677367
theorem B52186193 : Blo 2035435 52186193 := bstep (se 2 (by rfl) ⟨19569822, by rfl⟩ : syracuseStep 52186193 = 39139645) B39139645
theorem B34790795 : Blo 2035435 34790795 := bstep (se 1 (by rfl) ⟨26093096, by rfl⟩ : syracuseStep 34790795 = 52186193) B52186193
theorem B23193863 : Blo 2035435 23193863 := bstep (se 1 (by rfl) ⟨17395397, by rfl⟩ : syracuseStep 23193863 = 34790795) B34790795
theorem B15462575 : Blo 2035435 15462575 := bstep (se 1 (by rfl) ⟨11596931, by rfl⟩ : syracuseStep 15462575 = 23193863) B23193863
theorem B10308383 : Blo 2035435 10308383 := bstep (se 1 (by rfl) ⟨7731287, by rfl⟩ : syracuseStep 10308383 = 15462575) B15462575
theorem B6872255 : Blo 2035435 6872255 := bstep (se 1 (by rfl) ⟨5154191, by rfl⟩ : syracuseStep 6872255 = 10308383) B10308383
theorem B4581503 : Blo 2035435 4581503 := bstep (se 1 (by rfl) ⟨3436127, by rfl⟩ : syracuseStep 4581503 = 6872255) B6872255
theorem B3054335 : Blo 2035435 3054335 := bstep (se 1 (by rfl) ⟨2290751, by rfl⟩ : syracuseStep 3054335 = 4581503) B4581503
theorem B2036223 : Blo 2035435 2036223 := bstep (se 1 (by rfl) ⟨1527167, by rfl⟩ : syracuseStep 2036223 = 3054335) B3054335
theorem B3054341 : Blo 2035435 3054341 := bbase (se 4 (by rfl) ⟨286344, by rfl⟩ : syracuseStep 3054341 = 572689) (by norm_num)
theorem B2036227 : Blo 2035435 2036227 := bstep (se 1 (by rfl) ⟨1527170, by rfl⟩ : syracuseStep 2036227 = 3054341) B3054341
theorem B3436141 : Blo 2035435 3436141 := bbase (se 3 (by rfl) ⟨644276, by rfl⟩ : syracuseStep 3436141 = 1288553) (by norm_num)
theorem B4581521 : Blo 2035435 4581521 := bstep (se 2 (by rfl) ⟨1718070, by rfl⟩ : syracuseStep 4581521 = 3436141) B3436141
theorem B3054347 : Blo 2035435 3054347 := bstep (se 1 (by rfl) ⟨2290760, by rfl⟩ : syracuseStep 3054347 = 4581521) B4581521
theorem B2036231 : Blo 2035435 2036231 := bstep (se 1 (by rfl) ⟨1527173, by rfl⟩ : syracuseStep 2036231 = 3054347) B3054347
theorem B2290765 : Blo 2035435 2290765 := bbase (se 3 (by rfl) ⟨429518, by rfl⟩ : syracuseStep 2290765 = 859037) (by norm_num)
theorem B3054353 : Blo 2035435 3054353 := bstep (se 2 (by rfl) ⟨1145382, by rfl⟩ : syracuseStep 3054353 = 2290765) B2290765
theorem B2036235 : Blo 2035435 2036235 := bstep (se 1 (by rfl) ⟨1527176, by rfl⟩ : syracuseStep 2036235 = 3054353) B3054353
theorem B6872309 : Blo 2035435 6872309 := bbase (se 5 (by rfl) ⟨322139, by rfl⟩ : syracuseStep 6872309 = 644279) (by norm_num)
theorem B4581539 : Blo 2035435 4581539 := bstep (se 1 (by rfl) ⟨3436154, by rfl⟩ : syracuseStep 4581539 = 6872309) B6872309
theorem B3054359 : Blo 2035435 3054359 := bstep (se 1 (by rfl) ⟨2290769, by rfl⟩ : syracuseStep 3054359 = 4581539) B4581539
theorem B2036239 : Blo 2035435 2036239 := bstep (se 1 (by rfl) ⟨1527179, by rfl⟩ : syracuseStep 2036239 = 3054359) B3054359
theorem B3054365 : Blo 2035435 3054365 := bbase (se 3 (by rfl) ⟨572693, by rfl⟩ : syracuseStep 3054365 = 1145387) (by norm_num)
theorem B2036243 : Blo 2035435 2036243 := bstep (se 1 (by rfl) ⟨1527182, by rfl⟩ : syracuseStep 2036243 = 3054365) B3054365
theorem B4581557 : Blo 2035435 4581557 := bbase (se 5 (by rfl) ⟨214760, by rfl⟩ : syracuseStep 4581557 = 429521) (by norm_num)
theorem B3054371 : Blo 2035435 3054371 := bstep (se 1 (by rfl) ⟨2290778, by rfl⟩ : syracuseStep 3054371 = 4581557) B4581557
theorem B2036247 : Blo 2035435 2036247 := bstep (se 1 (by rfl) ⟨1527185, by rfl⟩ : syracuseStep 2036247 = 3054371) B3054371
theorem B4892525 : Blo 2035435 4892525 := bbase (se 3 (by rfl) ⟨917348, by rfl⟩ : syracuseStep 4892525 = 1834697) (by norm_num)
theorem B3261683 : Blo 2035435 3261683 := bstep (se 1 (by rfl) ⟨2446262, by rfl⟩ : syracuseStep 3261683 = 4892525) B4892525
theorem B2174455 : Blo 2035435 2174455 := bstep (se 1 (by rfl) ⟨1630841, by rfl⟩ : syracuseStep 2174455 = 3261683) B3261683
theorem B11597093 : Blo 2035435 11597093 := bstep (se 4 (by rfl) ⟨1087227, by rfl⟩ : syracuseStep 11597093 = 2174455) B2174455
theorem B7731395 : Blo 2035435 7731395 := bstep (se 1 (by rfl) ⟨5798546, by rfl⟩ : syracuseStep 7731395 = 11597093) B11597093
theorem B5154263 : Blo 2035435 5154263 := bstep (se 1 (by rfl) ⟨3865697, by rfl⟩ : syracuseStep 5154263 = 7731395) B7731395
theorem B3436175 : Blo 2035435 3436175 := bstep (se 1 (by rfl) ⟨2577131, by rfl⟩ : syracuseStep 3436175 = 5154263) B5154263
theorem B2290783 : Blo 2035435 2290783 := bstep (se 1 (by rfl) ⟨1718087, by rfl⟩ : syracuseStep 2290783 = 3436175) B3436175
theorem B3054377 : Blo 2035435 3054377 := bstep (se 2 (by rfl) ⟨1145391, by rfl⟩ : syracuseStep 3054377 = 2290783) B2290783
theorem B2036251 : Blo 2035435 2036251 := bstep (se 1 (by rfl) ⟨1527188, by rfl⟩ : syracuseStep 2036251 = 3054377) B3054377
theorem B4128077 : Blo 2035435 4128077 := bbase (se 3 (by rfl) ⟨774014, by rfl⟩ : syracuseStep 4128077 = 1548029) (by norm_num)
theorem B2752051 : Blo 2035435 2752051 := bstep (se 1 (by rfl) ⟨2064038, by rfl⟩ : syracuseStep 2752051 = 4128077) B4128077
theorem B3669401 : Blo 2035435 3669401 := bstep (se 2 (by rfl) ⟨1376025, by rfl⟩ : syracuseStep 3669401 = 2752051) B2752051
theorem B2446267 : Blo 2035435 2446267 := bstep (se 1 (by rfl) ⟨1834700, by rfl⟩ : syracuseStep 2446267 = 3669401) B3669401
theorem B3261689 : Blo 2035435 3261689 := bstep (se 2 (by rfl) ⟨1223133, by rfl⟩ : syracuseStep 3261689 = 2446267) B2446267
theorem B2174459 : Blo 2035435 2174459 := bstep (se 1 (by rfl) ⟨1630844, by rfl⟩ : syracuseStep 2174459 = 3261689) B3261689
theorem B5798557 : Blo 2035435 5798557 := bstep (se 3 (by rfl) ⟨1087229, by rfl⟩ : syracuseStep 5798557 = 2174459) B2174459
theorem B7731409 : Blo 2035435 7731409 := bstep (se 2 (by rfl) ⟨2899278, by rfl⟩ : syracuseStep 7731409 = 5798557) B5798557
theorem B10308545 : Blo 2035435 10308545 := bstep (se 2 (by rfl) ⟨3865704, by rfl⟩ : syracuseStep 10308545 = 7731409) B7731409
theorem B6872363 : Blo 2035435 6872363 := bstep (se 1 (by rfl) ⟨5154272, by rfl⟩ : syracuseStep 6872363 = 10308545) B10308545
theorem B4581575 : Blo 2035435 4581575 := bstep (se 1 (by rfl) ⟨3436181, by rfl⟩ : syracuseStep 4581575 = 6872363) B6872363
theorem B3054383 : Blo 2035435 3054383 := bstep (se 1 (by rfl) ⟨2290787, by rfl⟩ : syracuseStep 3054383 = 4581575) B4581575
theorem B2036255 : Blo 2035435 2036255 := bstep (se 1 (by rfl) ⟨1527191, by rfl⟩ : syracuseStep 2036255 = 3054383) B3054383
theorem B3054389 : Blo 2035435 3054389 := bbase (se 5 (by rfl) ⟨143174, by rfl⟩ : syracuseStep 3054389 = 286349) (by norm_num)
theorem B2036259 : Blo 2035435 2036259 := bstep (se 1 (by rfl) ⟨1527194, by rfl⟩ : syracuseStep 2036259 = 3054389) B3054389
theorem B5154293 : Blo 2035435 5154293 := bbase (se 5 (by rfl) ⟨241607, by rfl⟩ : syracuseStep 5154293 = 483215) (by norm_num)
theorem B3436195 : Blo 2035435 3436195 := bstep (se 1 (by rfl) ⟨2577146, by rfl⟩ : syracuseStep 3436195 = 5154293) B5154293
theorem B4581593 : Blo 2035435 4581593 := bstep (se 2 (by rfl) ⟨1718097, by rfl⟩ : syracuseStep 4581593 = 3436195) B3436195
theorem B3054395 : Blo 2035435 3054395 := bstep (se 1 (by rfl) ⟨2290796, by rfl⟩ : syracuseStep 3054395 = 4581593) B4581593
theorem B2036263 : Blo 2035435 2036263 := bstep (se 1 (by rfl) ⟨1527197, by rfl⟩ : syracuseStep 2036263 = 3054395) B3054395
theorem B2290801 : Blo 2035435 2290801 := bbase (se 2 (by rfl) ⟨859050, by rfl⟩ : syracuseStep 2290801 = 1718101) (by norm_num)
theorem B3054401 : Blo 2035435 3054401 := bstep (se 2 (by rfl) ⟨1145400, by rfl⟩ : syracuseStep 3054401 = 2290801) B2290801
theorem B2036267 : Blo 2035435 2036267 := bstep (se 1 (by rfl) ⟨1527200, by rfl⟩ : syracuseStep 2036267 = 3054401) B3054401
theorem B6523429 : Blo 2035435 6523429 := bbase (se 4 (by rfl) ⟨611571, by rfl⟩ : syracuseStep 6523429 = 1223143) (by norm_num)
theorem B8697905 : Blo 2035435 8697905 := bstep (se 2 (by rfl) ⟨3261714, by rfl⟩ : syracuseStep 8697905 = 6523429) B6523429
theorem B5798603 : Blo 2035435 5798603 := bstep (se 1 (by rfl) ⟨4348952, by rfl⟩ : syracuseStep 5798603 = 8697905) B8697905
theorem B3865735 : Blo 2035435 3865735 := bstep (se 1 (by rfl) ⟨2899301, by rfl⟩ : syracuseStep 3865735 = 5798603) B5798603
theorem B5154313 : Blo 2035435 5154313 := bstep (se 2 (by rfl) ⟨1932867, by rfl⟩ : syracuseStep 5154313 = 3865735) B3865735
theorem B6872417 : Blo 2035435 6872417 := bstep (se 2 (by rfl) ⟨2577156, by rfl⟩ : syracuseStep 6872417 = 5154313) B5154313
theorem B4581611 : Blo 2035435 4581611 := bstep (se 1 (by rfl) ⟨3436208, by rfl⟩ : syracuseStep 4581611 = 6872417) B6872417
theorem B3054407 : Blo 2035435 3054407 := bstep (se 1 (by rfl) ⟨2290805, by rfl⟩ : syracuseStep 3054407 = 4581611) B4581611
theorem B2036271 : Blo 2035435 2036271 := bstep (se 1 (by rfl) ⟨1527203, by rfl⟩ : syracuseStep 2036271 = 3054407) B3054407
theorem B3054413 : Blo 2035435 3054413 := bbase (se 3 (by rfl) ⟨572702, by rfl⟩ : syracuseStep 3054413 = 1145405) (by norm_num)
theorem B2036275 : Blo 2035435 2036275 := bstep (se 1 (by rfl) ⟨1527206, by rfl⟩ : syracuseStep 2036275 = 3054413) B3054413
theorem B4581629 : Blo 2035435 4581629 := bbase (se 3 (by rfl) ⟨859055, by rfl⟩ : syracuseStep 4581629 = 1718111) (by norm_num)
theorem B3054419 : Blo 2035435 3054419 := bstep (se 1 (by rfl) ⟨2290814, by rfl⟩ : syracuseStep 3054419 = 4581629) B4581629
theorem B2036279 : Blo 2035435 2036279 := bstep (se 1 (by rfl) ⟨1527209, by rfl⟩ : syracuseStep 2036279 = 3054419) B3054419
theorem B3436229 : Blo 2035435 3436229 := bbase (se 4 (by rfl) ⟨322146, by rfl⟩ : syracuseStep 3436229 = 644293) (by norm_num)
theorem B2290819 : Blo 2035435 2290819 := bstep (se 1 (by rfl) ⟨1718114, by rfl⟩ : syracuseStep 2290819 = 3436229) B3436229
theorem B3054425 : Blo 2035435 3054425 := bstep (se 2 (by rfl) ⟨1145409, by rfl⟩ : syracuseStep 3054425 = 2290819) B2290819
theorem B2036283 : Blo 2035435 2036283 := bstep (se 1 (by rfl) ⟨1527212, by rfl⟩ : syracuseStep 2036283 = 3054425) B3054425
theorem B15463061 : Blo 2035435 15463061 := bbase (se 6 (by rfl) ⟨362415, by rfl⟩ : syracuseStep 15463061 = 724831) (by norm_num)
theorem B10308707 : Blo 2035435 10308707 := bstep (se 1 (by rfl) ⟨7731530, by rfl⟩ : syracuseStep 10308707 = 15463061) B15463061
theorem B6872471 : Blo 2035435 6872471 := bstep (se 1 (by rfl) ⟨5154353, by rfl⟩ : syracuseStep 6872471 = 10308707) B10308707
theorem B4581647 : Blo 2035435 4581647 := bstep (se 1 (by rfl) ⟨3436235, by rfl⟩ : syracuseStep 4581647 = 6872471) B6872471
theorem B3054431 : Blo 2035435 3054431 := bstep (se 1 (by rfl) ⟨2290823, by rfl⟩ : syracuseStep 3054431 = 4581647) B4581647
theorem B2036287 : Blo 2035435 2036287 := bstep (se 1 (by rfl) ⟨1527215, by rfl⟩ : syracuseStep 2036287 = 3054431) B3054431
theorem B3054437 : Blo 2035435 3054437 := bbase (se 4 (by rfl) ⟨286353, by rfl⟩ : syracuseStep 3054437 = 572707) (by norm_num)
theorem B2036291 : Blo 2035435 2036291 := bstep (se 1 (by rfl) ⟨1527218, by rfl⟩ : syracuseStep 2036291 = 3054437) B3054437
theorem B3865781 : Blo 2035435 3865781 := bbase (se 5 (by rfl) ⟨181208, by rfl⟩ : syracuseStep 3865781 = 362417) (by norm_num)
theorem B2577187 : Blo 2035435 2577187 := bstep (se 1 (by rfl) ⟨1932890, by rfl⟩ : syracuseStep 2577187 = 3865781) B3865781
theorem B3436249 : Blo 2035435 3436249 := bstep (se 2 (by rfl) ⟨1288593, by rfl⟩ : syracuseStep 3436249 = 2577187) B2577187
theorem B4581665 : Blo 2035435 4581665 := bstep (se 2 (by rfl) ⟨1718124, by rfl⟩ : syracuseStep 4581665 = 3436249) B3436249
theorem B3054443 : Blo 2035435 3054443 := bstep (se 1 (by rfl) ⟨2290832, by rfl⟩ : syracuseStep 3054443 = 4581665) B4581665
theorem B2036295 : Blo 2035435 2036295 := bstep (se 1 (by rfl) ⟨1527221, by rfl⟩ : syracuseStep 2036295 = 3054443) B3054443
theorem B2290837 : Blo 2035435 2290837 := bbase (se 6 (by rfl) ⟨53691, by rfl⟩ : syracuseStep 2290837 = 107383) (by norm_num)
theorem B3054449 : Blo 2035435 3054449 := bstep (se 2 (by rfl) ⟨1145418, by rfl⟩ : syracuseStep 3054449 = 2290837) B2290837
theorem B2036299 : Blo 2035435 2036299 := bstep (se 1 (by rfl) ⟨1527224, by rfl⟩ : syracuseStep 2036299 = 3054449) B3054449
theorem B2577197 : Blo 2035435 2577197 := bbase (se 3 (by rfl) ⟨483224, by rfl⟩ : syracuseStep 2577197 = 966449) (by norm_num)
theorem B6872525 : Blo 2035435 6872525 := bstep (se 3 (by rfl) ⟨1288598, by rfl⟩ : syracuseStep 6872525 = 2577197) B2577197
theorem B4581683 : Blo 2035435 4581683 := bstep (se 1 (by rfl) ⟨3436262, by rfl⟩ : syracuseStep 4581683 = 6872525) B6872525
theorem B3054455 : Blo 2035435 3054455 := bstep (se 1 (by rfl) ⟨2290841, by rfl⟩ : syracuseStep 3054455 = 4581683) B4581683
theorem B2036303 : Blo 2035435 2036303 := bstep (se 1 (by rfl) ⟨1527227, by rfl⟩ : syracuseStep 2036303 = 3054455) B3054455
theorem B3054461 : Blo 2035435 3054461 := bbase (se 3 (by rfl) ⟨572711, by rfl⟩ : syracuseStep 3054461 = 1145423) (by norm_num)
theorem B2036307 : Blo 2035435 2036307 := bstep (se 1 (by rfl) ⟨1527230, by rfl⟩ : syracuseStep 2036307 = 3054461) B3054461
theorem B4581701 : Blo 2035435 4581701 := bbase (se 4 (by rfl) ⟨429534, by rfl⟩ : syracuseStep 4581701 = 859069) (by norm_num)
theorem B3054467 : Blo 2035435 3054467 := bstep (se 1 (by rfl) ⟨2290850, by rfl⟩ : syracuseStep 3054467 = 4581701) B4581701
theorem B2036311 : Blo 2035435 2036311 := bstep (se 1 (by rfl) ⟨1527233, by rfl⟩ : syracuseStep 2036311 = 3054467) B3054467
theorem B3669509 : Blo 2035435 3669509 := bbase (se 4 (by rfl) ⟨344016, by rfl⟩ : syracuseStep 3669509 = 688033) (by norm_num)
theorem B9785357 : Blo 2035435 9785357 := bstep (se 3 (by rfl) ⟨1834754, by rfl⟩ : syracuseStep 9785357 = 3669509) B3669509
theorem B6523571 : Blo 2035435 6523571 := bstep (se 1 (by rfl) ⟨4892678, by rfl⟩ : syracuseStep 6523571 = 9785357) B9785357
theorem B4349047 : Blo 2035435 4349047 := bstep (se 1 (by rfl) ⟨3261785, by rfl⟩ : syracuseStep 4349047 = 6523571) B6523571
theorem B5798729 : Blo 2035435 5798729 := bstep (se 2 (by rfl) ⟨2174523, by rfl⟩ : syracuseStep 5798729 = 4349047) B4349047
theorem B3865819 : Blo 2035435 3865819 := bstep (se 1 (by rfl) ⟨2899364, by rfl⟩ : syracuseStep 3865819 = 5798729) B5798729
theorem B5154425 : Blo 2035435 5154425 := bstep (se 2 (by rfl) ⟨1932909, by rfl⟩ : syracuseStep 5154425 = 3865819) B3865819
theorem B3436283 : Blo 2035435 3436283 := bstep (se 1 (by rfl) ⟨2577212, by rfl⟩ : syracuseStep 3436283 = 5154425) B5154425
theorem B2290855 : Blo 2035435 2290855 := bstep (se 1 (by rfl) ⟨1718141, by rfl⟩ : syracuseStep 2290855 = 3436283) B3436283
theorem B3054473 : Blo 2035435 3054473 := bstep (se 2 (by rfl) ⟨1145427, by rfl⟩ : syracuseStep 3054473 = 2290855) B2290855
theorem B2036315 : Blo 2035435 2036315 := bstep (se 1 (by rfl) ⟨1527236, by rfl⟩ : syracuseStep 2036315 = 3054473) B3054473
theorem B10308869 : Blo 2035435 10308869 := bbase (se 4 (by rfl) ⟨966456, by rfl⟩ : syracuseStep 10308869 = 1932913) (by norm_num)
theorem B6872579 : Blo 2035435 6872579 := bstep (se 1 (by rfl) ⟨5154434, by rfl⟩ : syracuseStep 6872579 = 10308869) B10308869
theorem B4581719 : Blo 2035435 4581719 := bstep (se 1 (by rfl) ⟨3436289, by rfl⟩ : syracuseStep 4581719 = 6872579) B6872579
theorem B3054479 : Blo 2035435 3054479 := bstep (se 1 (by rfl) ⟨2290859, by rfl⟩ : syracuseStep 3054479 = 4581719) B4581719
theorem B2036319 : Blo 2035435 2036319 := bstep (se 1 (by rfl) ⟨1527239, by rfl⟩ : syracuseStep 2036319 = 3054479) B3054479
theorem B3054485 : Blo 2035435 3054485 := bbase (se 6 (by rfl) ⟨71589, by rfl⟩ : syracuseStep 3054485 = 143179) (by norm_num)
theorem B2036323 : Blo 2035435 2036323 := bstep (se 1 (by rfl) ⟨1527242, by rfl⟩ : syracuseStep 2036323 = 3054485) B3054485
theorem B11597525 : Blo 2035435 11597525 := bbase (se 7 (by rfl) ⟨135908, by rfl⟩ : syracuseStep 11597525 = 271817) (by norm_num)
theorem B7731683 : Blo 2035435 7731683 := bstep (se 1 (by rfl) ⟨5798762, by rfl⟩ : syracuseStep 7731683 = 11597525) B11597525
theorem B5154455 : Blo 2035435 5154455 := bstep (se 1 (by rfl) ⟨3865841, by rfl⟩ : syracuseStep 5154455 = 7731683) B7731683
theorem B3436303 : Blo 2035435 3436303 := bstep (se 1 (by rfl) ⟨2577227, by rfl⟩ : syracuseStep 3436303 = 5154455) B5154455
theorem B4581737 : Blo 2035435 4581737 := bstep (se 2 (by rfl) ⟨1718151, by rfl⟩ : syracuseStep 4581737 = 3436303) B3436303
theorem B3054491 : Blo 2035435 3054491 := bstep (se 1 (by rfl) ⟨2290868, by rfl⟩ : syracuseStep 3054491 = 4581737) B4581737
theorem B2036327 : Blo 2035435 2036327 := bstep (se 1 (by rfl) ⟨1527245, by rfl⟩ : syracuseStep 2036327 = 3054491) B3054491
theorem B2290873 : Blo 2035435 2290873 := bbase (se 2 (by rfl) ⟨859077, by rfl⟩ : syracuseStep 2290873 = 1718155) (by norm_num)
theorem B3054497 : Blo 2035435 3054497 := bstep (se 2 (by rfl) ⟨1145436, by rfl⟩ : syracuseStep 3054497 = 2290873) B2290873
theorem B2036331 : Blo 2035435 2036331 := bstep (se 1 (by rfl) ⟨1527248, by rfl⟩ : syracuseStep 2036331 = 3054497) B3054497
theorem B2479741 : Blo 2035435 2479741 := bbase (se 3 (by rfl) ⟨464951, by rfl⟩ : syracuseStep 2479741 = 929903) (by norm_num)
theorem B13225285 : Blo 2035435 13225285 := bstep (se 4 (by rfl) ⟨1239870, by rfl⟩ : syracuseStep 13225285 = 2479741) B2479741
theorem B17633713 : Blo 2035435 17633713 := bstep (se 2 (by rfl) ⟨6612642, by rfl⟩ : syracuseStep 17633713 = 13225285) B13225285
theorem B23511617 : Blo 2035435 23511617 := bstep (se 2 (by rfl) ⟨8816856, by rfl⟩ : syracuseStep 23511617 = 17633713) B17633713
theorem B15674411 : Blo 2035435 15674411 := bstep (se 1 (by rfl) ⟨11755808, by rfl⟩ : syracuseStep 15674411 = 23511617) B23511617
theorem B10449607 : Blo 2035435 10449607 := bstep (se 1 (by rfl) ⟨7837205, by rfl⟩ : syracuseStep 10449607 = 15674411) B15674411
theorem B13932809 : Blo 2035435 13932809 := bstep (se 2 (by rfl) ⟨5224803, by rfl⟩ : syracuseStep 13932809 = 10449607) B10449607
theorem B9288539 : Blo 2035435 9288539 := bstep (se 1 (by rfl) ⟨6966404, by rfl⟩ : syracuseStep 9288539 = 13932809) B13932809
theorem B6192359 : Blo 2035435 6192359 := bstep (se 1 (by rfl) ⟨4644269, by rfl⟩ : syracuseStep 6192359 = 9288539) B9288539
theorem B4128239 : Blo 2035435 4128239 := bstep (se 1 (by rfl) ⟨3096179, by rfl⟩ : syracuseStep 4128239 = 6192359) B6192359
theorem B2752159 : Blo 2035435 2752159 := bstep (se 1 (by rfl) ⟨2064119, by rfl⟩ : syracuseStep 2752159 = 4128239) B4128239
theorem B3669545 : Blo 2035435 3669545 := bstep (se 2 (by rfl) ⟨1376079, by rfl⟩ : syracuseStep 3669545 = 2752159) B2752159
theorem B2446363 : Blo 2035435 2446363 := bstep (se 1 (by rfl) ⟨1834772, by rfl⟩ : syracuseStep 2446363 = 3669545) B3669545
theorem B3261817 : Blo 2035435 3261817 := bstep (se 2 (by rfl) ⟨1223181, by rfl⟩ : syracuseStep 3261817 = 2446363) B2446363
theorem B4349089 : Blo 2035435 4349089 := bstep (se 2 (by rfl) ⟨1630908, by rfl⟩ : syracuseStep 4349089 = 3261817) B3261817
theorem B5798785 : Blo 2035435 5798785 := bstep (se 2 (by rfl) ⟨2174544, by rfl⟩ : syracuseStep 5798785 = 4349089) B4349089
theorem B7731713 : Blo 2035435 7731713 := bstep (se 2 (by rfl) ⟨2899392, by rfl⟩ : syracuseStep 7731713 = 5798785) B5798785
theorem B5154475 : Blo 2035435 5154475 := bstep (se 1 (by rfl) ⟨3865856, by rfl⟩ : syracuseStep 5154475 = 7731713) B7731713
theorem B6872633 : Blo 2035435 6872633 := bstep (se 2 (by rfl) ⟨2577237, by rfl⟩ : syracuseStep 6872633 = 5154475) B5154475
theorem B4581755 : Blo 2035435 4581755 := bstep (se 1 (by rfl) ⟨3436316, by rfl⟩ : syracuseStep 4581755 = 6872633) B6872633
theorem B3054503 : Blo 2035435 3054503 := bstep (se 1 (by rfl) ⟨2290877, by rfl⟩ : syracuseStep 3054503 = 4581755) B4581755
theorem B2036335 : Blo 2035435 2036335 := bstep (se 1 (by rfl) ⟨1527251, by rfl⟩ : syracuseStep 2036335 = 3054503) B3054503
theorem B3054509 : Blo 2035435 3054509 := bbase (se 3 (by rfl) ⟨572720, by rfl⟩ : syracuseStep 3054509 = 1145441) (by norm_num)
theorem B2036339 : Blo 2035435 2036339 := bstep (se 1 (by rfl) ⟨1527254, by rfl⟩ : syracuseStep 2036339 = 3054509) B3054509
theorem B4581773 : Blo 2035435 4581773 := bbase (se 3 (by rfl) ⟨859082, by rfl⟩ : syracuseStep 4581773 = 1718165) (by norm_num)
theorem B3054515 : Blo 2035435 3054515 := bstep (se 1 (by rfl) ⟨2290886, by rfl⟩ : syracuseStep 3054515 = 4581773) B4581773
theorem B2036343 : Blo 2035435 2036343 := bstep (se 1 (by rfl) ⟨1527257, by rfl⟩ : syracuseStep 2036343 = 3054515) B3054515
theorem B2577253 : Blo 2035435 2577253 := bbase (se 4 (by rfl) ⟨241617, by rfl⟩ : syracuseStep 2577253 = 483235) (by norm_num)
theorem B3436337 : Blo 2035435 3436337 := bstep (se 2 (by rfl) ⟨1288626, by rfl⟩ : syracuseStep 3436337 = 2577253) B2577253
theorem B2290891 : Blo 2035435 2290891 := bstep (se 1 (by rfl) ⟨1718168, by rfl⟩ : syracuseStep 2290891 = 3436337) B3436337
theorem B3054521 : Blo 2035435 3054521 := bstep (se 2 (by rfl) ⟨1145445, by rfl⟩ : syracuseStep 3054521 = 2290891) B2290891
theorem B2036347 : Blo 2035435 2036347 := bstep (se 1 (by rfl) ⟨1527260, by rfl⟩ : syracuseStep 2036347 = 3054521) B3054521
theorem B8369189 : Blo 2035435 8369189 := bbase (se 4 (by rfl) ⟨784611, by rfl⟩ : syracuseStep 8369189 = 1569223) (by norm_num)
theorem B5579459 : Blo 2035435 5579459 := bstep (se 1 (by rfl) ⟨4184594, by rfl⟩ : syracuseStep 5579459 = 8369189) B8369189
theorem B3719639 : Blo 2035435 3719639 := bstep (se 1 (by rfl) ⟨2789729, by rfl⟩ : syracuseStep 3719639 = 5579459) B5579459
theorem B2479759 : Blo 2035435 2479759 := bstep (se 1 (by rfl) ⟨1859819, by rfl⟩ : syracuseStep 2479759 = 3719639) B3719639
theorem B52901525 : Blo 2035435 52901525 := bstep (se 6 (by rfl) ⟨1239879, by rfl⟩ : syracuseStep 52901525 = 2479759) B2479759
theorem B35267683 : Blo 2035435 35267683 := bstep (se 1 (by rfl) ⟨26450762, by rfl⟩ : syracuseStep 35267683 = 52901525) B52901525
theorem B47023577 : Blo 2035435 47023577 := bstep (se 2 (by rfl) ⟨17633841, by rfl⟩ : syracuseStep 47023577 = 35267683) B35267683
theorem B31349051 : Blo 2035435 31349051 := bstep (se 1 (by rfl) ⟨23511788, by rfl⟩ : syracuseStep 31349051 = 47023577) B47023577
theorem B20899367 : Blo 2035435 20899367 := bstep (se 1 (by rfl) ⟨15674525, by rfl⟩ : syracuseStep 20899367 = 31349051) B31349051
theorem B13932911 : Blo 2035435 13932911 := bstep (se 1 (by rfl) ⟨10449683, by rfl⟩ : syracuseStep 13932911 = 20899367) B20899367
theorem B9288607 : Blo 2035435 9288607 := bstep (se 1 (by rfl) ⟨6966455, by rfl⟩ : syracuseStep 9288607 = 13932911) B13932911
theorem B12384809 : Blo 2035435 12384809 := bstep (se 2 (by rfl) ⟨4644303, by rfl⟩ : syracuseStep 12384809 = 9288607) B9288607
theorem B8256539 : Blo 2035435 8256539 := bstep (se 1 (by rfl) ⟨6192404, by rfl⟩ : syracuseStep 8256539 = 12384809) B12384809
theorem B5504359 : Blo 2035435 5504359 := bstep (se 1 (by rfl) ⟨4128269, by rfl⟩ : syracuseStep 5504359 = 8256539) B8256539
theorem B7339145 : Blo 2035435 7339145 := bstep (se 2 (by rfl) ⟨2752179, by rfl⟩ : syracuseStep 7339145 = 5504359) B5504359
theorem B19571053 : Blo 2035435 19571053 := bstep (se 3 (by rfl) ⟨3669572, by rfl⟩ : syracuseStep 19571053 = 7339145) B7339145
theorem B26094737 : Blo 2035435 26094737 := bstep (se 2 (by rfl) ⟨9785526, by rfl⟩ : syracuseStep 26094737 = 19571053) B19571053
theorem B17396491 : Blo 2035435 17396491 := bstep (se 1 (by rfl) ⟨13047368, by rfl⟩ : syracuseStep 17396491 = 26094737) B26094737
theorem B23195321 : Blo 2035435 23195321 := bstep (se 2 (by rfl) ⟨8698245, by rfl⟩ : syracuseStep 23195321 = 17396491) B17396491
theorem B15463547 : Blo 2035435 15463547 := bstep (se 1 (by rfl) ⟨11597660, by rfl⟩ : syracuseStep 15463547 = 23195321) B23195321
theorem B10309031 : Blo 2035435 10309031 := bstep (se 1 (by rfl) ⟨7731773, by rfl⟩ : syracuseStep 10309031 = 15463547) B15463547
theorem B6872687 : Blo 2035435 6872687 := bstep (se 1 (by rfl) ⟨5154515, by rfl⟩ : syracuseStep 6872687 = 10309031) B10309031
theorem B4581791 : Blo 2035435 4581791 := bstep (se 1 (by rfl) ⟨3436343, by rfl⟩ : syracuseStep 4581791 = 6872687) B6872687
theorem B3054527 : Blo 2035435 3054527 := bstep (se 1 (by rfl) ⟨2290895, by rfl⟩ : syracuseStep 3054527 = 4581791) B4581791
theorem B2036351 : Blo 2035435 2036351 := bstep (se 1 (by rfl) ⟨1527263, by rfl⟩ : syracuseStep 2036351 = 3054527) B3054527
theorem B3054533 : Blo 2035435 3054533 := bbase (se 4 (by rfl) ⟨286362, by rfl⟩ : syracuseStep 3054533 = 572725) (by norm_num)
theorem B2036355 : Blo 2035435 2036355 := bstep (se 1 (by rfl) ⟨1527266, by rfl⟩ : syracuseStep 2036355 = 3054533) B3054533
theorem B3436357 : Blo 2035435 3436357 := bbase (se 4 (by rfl) ⟨322158, by rfl⟩ : syracuseStep 3436357 = 644317) (by norm_num)
theorem B4581809 : Blo 2035435 4581809 := bstep (se 2 (by rfl) ⟨1718178, by rfl⟩ : syracuseStep 4581809 = 3436357) B3436357
theorem B3054539 : Blo 2035435 3054539 := bstep (se 1 (by rfl) ⟨2290904, by rfl⟩ : syracuseStep 3054539 = 4581809) B4581809
theorem B2036359 : Blo 2035435 2036359 := bstep (se 1 (by rfl) ⟨1527269, by rfl⟩ : syracuseStep 2036359 = 3054539) B3054539
theorem B2290909 : Blo 2035435 2290909 := bbase (se 3 (by rfl) ⟨429545, by rfl⟩ : syracuseStep 2290909 = 859091) (by norm_num)
theorem B3054545 : Blo 2035435 3054545 := bstep (se 2 (by rfl) ⟨1145454, by rfl⟩ : syracuseStep 3054545 = 2290909) B2290909
theorem B2036363 : Blo 2035435 2036363 := bstep (se 1 (by rfl) ⟨1527272, by rfl⟩ : syracuseStep 2036363 = 3054545) B3054545
theorem B6872741 : Blo 2035435 6872741 := bbase (se 4 (by rfl) ⟨644319, by rfl⟩ : syracuseStep 6872741 = 1288639) (by norm_num)
theorem B4581827 : Blo 2035435 4581827 := bstep (se 1 (by rfl) ⟨3436370, by rfl⟩ : syracuseStep 4581827 = 6872741) B6872741
theorem B3054551 : Blo 2035435 3054551 := bstep (se 1 (by rfl) ⟨2290913, by rfl⟩ : syracuseStep 3054551 = 4581827) B4581827
theorem B2036367 : Blo 2035435 2036367 := bstep (se 1 (by rfl) ⟨1527275, by rfl⟩ : syracuseStep 2036367 = 3054551) B3054551
theorem B3054557 : Blo 2035435 3054557 := bbase (se 3 (by rfl) ⟨572729, by rfl⟩ : syracuseStep 3054557 = 1145459) (by norm_num)
theorem B2036371 : Blo 2035435 2036371 := bstep (se 1 (by rfl) ⟨1527278, by rfl⟩ : syracuseStep 2036371 = 3054557) B3054557
theorem B4581845 : Blo 2035435 4581845 := bbase (se 7 (by rfl) ⟨53693, by rfl⟩ : syracuseStep 4581845 = 107387) (by norm_num)
theorem B3054563 : Blo 2035435 3054563 := bstep (se 1 (by rfl) ⟨2290922, by rfl⟩ : syracuseStep 3054563 = 4581845) B4581845
theorem B2036375 : Blo 2035435 2036375 := bstep (se 1 (by rfl) ⟨1527281, by rfl⟩ : syracuseStep 2036375 = 3054563) B3054563
theorem B3397229 : Blo 2035435 3397229 := bbase (se 3 (by rfl) ⟨636980, by rfl⟩ : syracuseStep 3397229 = 1273961) (by norm_num)
theorem B2264819 : Blo 2035435 2264819 := bstep (se 1 (by rfl) ⟨1698614, by rfl⟩ : syracuseStep 2264819 = 3397229) B3397229
theorem B6039517 : Blo 2035435 6039517 := bstep (se 3 (by rfl) ⟨1132409, by rfl⟩ : syracuseStep 6039517 = 2264819) B2264819
theorem B8052689 : Blo 2035435 8052689 := bstep (se 2 (by rfl) ⟨3019758, by rfl⟩ : syracuseStep 8052689 = 6039517) B6039517
theorem B5368459 : Blo 2035435 5368459 := bstep (se 1 (by rfl) ⟨4026344, by rfl⟩ : syracuseStep 5368459 = 8052689) B8052689
theorem B7157945 : Blo 2035435 7157945 := bstep (se 2 (by rfl) ⟨2684229, by rfl⟩ : syracuseStep 7157945 = 5368459) B5368459
theorem B4771963 : Blo 2035435 4771963 := bstep (se 1 (by rfl) ⟨3578972, by rfl⟩ : syracuseStep 4771963 = 7157945) B7157945
theorem B25450469 : Blo 2035435 25450469 := bstep (se 4 (by rfl) ⟨2385981, by rfl⟩ : syracuseStep 25450469 = 4771963) B4771963
theorem B16966979 : Blo 2035435 16966979 := bstep (se 1 (by rfl) ⟨12725234, by rfl⟩ : syracuseStep 16966979 = 25450469) B25450469
theorem B11311319 : Blo 2035435 11311319 := bstep (se 1 (by rfl) ⟨8483489, by rfl⟩ : syracuseStep 11311319 = 16966979) B16966979
theorem B7540879 : Blo 2035435 7540879 := bstep (se 1 (by rfl) ⟨5655659, by rfl⟩ : syracuseStep 7540879 = 11311319) B11311319
theorem B10054505 : Blo 2035435 10054505 := bstep (se 2 (by rfl) ⟨3770439, by rfl⟩ : syracuseStep 10054505 = 7540879) B7540879
theorem B6703003 : Blo 2035435 6703003 := bstep (se 1 (by rfl) ⟨5027252, by rfl⟩ : syracuseStep 6703003 = 10054505) B10054505
theorem B35749349 : Blo 2035435 35749349 := bstep (se 4 (by rfl) ⟨3351501, by rfl⟩ : syracuseStep 35749349 = 6703003) B6703003
theorem B23832899 : Blo 2035435 23832899 := bstep (se 1 (by rfl) ⟨17874674, by rfl⟩ : syracuseStep 23832899 = 35749349) B35749349
theorem B15888599 : Blo 2035435 15888599 := bstep (se 1 (by rfl) ⟨11916449, by rfl⟩ : syracuseStep 15888599 = 23832899) B23832899
theorem B10592399 : Blo 2035435 10592399 := bstep (se 1 (by rfl) ⟨7944299, by rfl⟩ : syracuseStep 10592399 = 15888599) B15888599
theorem B7061599 : Blo 2035435 7061599 := bstep (se 1 (by rfl) ⟨5296199, by rfl⟩ : syracuseStep 7061599 = 10592399) B10592399
theorem B37661861 : Blo 2035435 37661861 := bstep (se 4 (by rfl) ⟨3530799, by rfl⟩ : syracuseStep 37661861 = 7061599) B7061599
theorem B25107907 : Blo 2035435 25107907 := bstep (se 1 (by rfl) ⟨18830930, by rfl⟩ : syracuseStep 25107907 = 37661861) B37661861
theorem B33477209 : Blo 2035435 33477209 := bstep (se 2 (by rfl) ⟨12553953, by rfl⟩ : syracuseStep 33477209 = 25107907) B25107907
theorem B22318139 : Blo 2035435 22318139 := bstep (se 1 (by rfl) ⟨16738604, by rfl⟩ : syracuseStep 22318139 = 33477209) B33477209
theorem B14878759 : Blo 2035435 14878759 := bstep (se 1 (by rfl) ⟨11159069, by rfl⟩ : syracuseStep 14878759 = 22318139) B22318139
theorem B19838345 : Blo 2035435 19838345 := bstep (se 2 (by rfl) ⟨7439379, by rfl⟩ : syracuseStep 19838345 = 14878759) B14878759
theorem B52902253 : Blo 2035435 52902253 := bstep (se 3 (by rfl) ⟨9919172, by rfl⟩ : syracuseStep 52902253 = 19838345) B19838345
theorem B282145349 : Blo 2035435 282145349 := bstep (se 4 (by rfl) ⟨26451126, by rfl⟩ : syracuseStep 282145349 = 52902253) B52902253
theorem B188096899 : Blo 2035435 188096899 := bstep (se 1 (by rfl) ⟨141072674, by rfl⟩ : syracuseStep 188096899 = 282145349) B282145349
theorem B250795865 : Blo 2035435 250795865 := bstep (se 2 (by rfl) ⟨94048449, by rfl⟩ : syracuseStep 250795865 = 188096899) B188096899
theorem B167197243 : Blo 2035435 167197243 := bstep (se 1 (by rfl) ⟨125397932, by rfl⟩ : syracuseStep 167197243 = 250795865) B250795865
theorem B222929657 : Blo 2035435 222929657 := bstep (se 2 (by rfl) ⟨83598621, by rfl⟩ : syracuseStep 222929657 = 167197243) B167197243
theorem B148619771 : Blo 2035435 148619771 := bstep (se 1 (by rfl) ⟨111464828, by rfl⟩ : syracuseStep 148619771 = 222929657) B222929657
theorem B99079847 : Blo 2035435 99079847 := bstep (se 1 (by rfl) ⟨74309885, by rfl⟩ : syracuseStep 99079847 = 148619771) B148619771
theorem B66053231 : Blo 2035435 66053231 := bstep (se 1 (by rfl) ⟨49539923, by rfl⟩ : syracuseStep 66053231 = 99079847) B99079847
theorem B44035487 : Blo 2035435 44035487 := bstep (se 1 (by rfl) ⟨33026615, by rfl⟩ : syracuseStep 44035487 = 66053231) B66053231
theorem B29356991 : Blo 2035435 29356991 := bstep (se 1 (by rfl) ⟨22017743, by rfl⟩ : syracuseStep 29356991 = 44035487) B44035487
theorem B19571327 : Blo 2035435 19571327 := bstep (se 1 (by rfl) ⟨14678495, by rfl⟩ : syracuseStep 19571327 = 29356991) B29356991
theorem B13047551 : Blo 2035435 13047551 := bstep (se 1 (by rfl) ⟨9785663, by rfl⟩ : syracuseStep 13047551 = 19571327) B19571327
theorem B8698367 : Blo 2035435 8698367 := bstep (se 1 (by rfl) ⟨6523775, by rfl⟩ : syracuseStep 8698367 = 13047551) B13047551
theorem B5798911 : Blo 2035435 5798911 := bstep (se 1 (by rfl) ⟨4349183, by rfl⟩ : syracuseStep 5798911 = 8698367) B8698367
theorem B7731881 : Blo 2035435 7731881 := bstep (se 2 (by rfl) ⟨2899455, by rfl⟩ : syracuseStep 7731881 = 5798911) B5798911
theorem B5154587 : Blo 2035435 5154587 := bstep (se 1 (by rfl) ⟨3865940, by rfl⟩ : syracuseStep 5154587 = 7731881) B7731881
theorem B3436391 : Blo 2035435 3436391 := bstep (se 1 (by rfl) ⟨2577293, by rfl⟩ : syracuseStep 3436391 = 5154587) B5154587
theorem B2290927 : Blo 2035435 2290927 := bstep (se 1 (by rfl) ⟨1718195, by rfl⟩ : syracuseStep 2290927 = 3436391) B3436391
theorem B3054569 : Blo 2035435 3054569 := bstep (se 2 (by rfl) ⟨1145463, by rfl⟩ : syracuseStep 3054569 = 2290927) B2290927
theorem B2036379 : Blo 2035435 2036379 := bstep (se 1 (by rfl) ⟨1527284, by rfl⟩ : syracuseStep 2036379 = 3054569) B3054569
theorem B5224925 : Blo 2035435 5224925 := bbase (se 3 (by rfl) ⟨979673, by rfl⟩ : syracuseStep 5224925 = 1959347) (by norm_num)
theorem B13933133 : Blo 2035435 13933133 := bstep (se 3 (by rfl) ⟨2612462, by rfl⟩ : syracuseStep 13933133 = 5224925) B5224925
theorem B9288755 : Blo 2035435 9288755 := bstep (se 1 (by rfl) ⟨6966566, by rfl⟩ : syracuseStep 9288755 = 13933133) B13933133
theorem B6192503 : Blo 2035435 6192503 := bstep (se 1 (by rfl) ⟨4644377, by rfl⟩ : syracuseStep 6192503 = 9288755) B9288755
theorem B4128335 : Blo 2035435 4128335 := bstep (se 1 (by rfl) ⟨3096251, by rfl⟩ : syracuseStep 4128335 = 6192503) B6192503
theorem B2752223 : Blo 2035435 2752223 := bstep (se 1 (by rfl) ⟨2064167, by rfl⟩ : syracuseStep 2752223 = 4128335) B4128335
theorem B7339261 : Blo 2035435 7339261 := bstep (se 3 (by rfl) ⟨1376111, by rfl⟩ : syracuseStep 7339261 = 2752223) B2752223
theorem B9785681 : Blo 2035435 9785681 := bstep (se 2 (by rfl) ⟨3669630, by rfl⟩ : syracuseStep 9785681 = 7339261) B7339261
theorem B6523787 : Blo 2035435 6523787 := bstep (se 1 (by rfl) ⟨4892840, by rfl⟩ : syracuseStep 6523787 = 9785681) B9785681
theorem B17396765 : Blo 2035435 17396765 := bstep (se 3 (by rfl) ⟨3261893, by rfl⟩ : syracuseStep 17396765 = 6523787) B6523787
theorem B11597843 : Blo 2035435 11597843 := bstep (se 1 (by rfl) ⟨8698382, by rfl⟩ : syracuseStep 11597843 = 17396765) B17396765
theorem B7731895 : Blo 2035435 7731895 := bstep (se 1 (by rfl) ⟨5798921, by rfl⟩ : syracuseStep 7731895 = 11597843) B11597843
theorem B10309193 : Blo 2035435 10309193 := bstep (se 2 (by rfl) ⟨3865947, by rfl⟩ : syracuseStep 10309193 = 7731895) B7731895
theorem B6872795 : Blo 2035435 6872795 := bstep (se 1 (by rfl) ⟨5154596, by rfl⟩ : syracuseStep 6872795 = 10309193) B10309193
theorem B4581863 : Blo 2035435 4581863 := bstep (se 1 (by rfl) ⟨3436397, by rfl⟩ : syracuseStep 4581863 = 6872795) B6872795
theorem B3054575 : Blo 2035435 3054575 := bstep (se 1 (by rfl) ⟨2290931, by rfl⟩ : syracuseStep 3054575 = 4581863) B4581863
theorem B2036383 : Blo 2035435 2036383 := bstep (se 1 (by rfl) ⟨1527287, by rfl⟩ : syracuseStep 2036383 = 3054575) B3054575
theorem B3054581 : Blo 2035435 3054581 := bbase (se 5 (by rfl) ⟨143183, by rfl⟩ : syracuseStep 3054581 = 286367) (by norm_num)
theorem B2036387 : Blo 2035435 2036387 := bstep (se 1 (by rfl) ⟨1527290, by rfl⟩ : syracuseStep 2036387 = 3054581) B3054581
theorem B4892861 : Blo 2035435 4892861 := bbase (se 3 (by rfl) ⟨917411, by rfl⟩ : syracuseStep 4892861 = 1834823) (by norm_num)
theorem B3261907 : Blo 2035435 3261907 := bstep (se 1 (by rfl) ⟨2446430, by rfl⟩ : syracuseStep 3261907 = 4892861) B4892861
theorem B4349209 : Blo 2035435 4349209 := bstep (se 2 (by rfl) ⟨1630953, by rfl⟩ : syracuseStep 4349209 = 3261907) B3261907
theorem B5798945 : Blo 2035435 5798945 := bstep (se 2 (by rfl) ⟨2174604, by rfl⟩ : syracuseStep 5798945 = 4349209) B4349209
theorem B3865963 : Blo 2035435 3865963 := bstep (se 1 (by rfl) ⟨2899472, by rfl⟩ : syracuseStep 3865963 = 5798945) B5798945
theorem B5154617 : Blo 2035435 5154617 := bstep (se 2 (by rfl) ⟨1932981, by rfl⟩ : syracuseStep 5154617 = 3865963) B3865963
theorem B3436411 : Blo 2035435 3436411 := bstep (se 1 (by rfl) ⟨2577308, by rfl⟩ : syracuseStep 3436411 = 5154617) B5154617
theorem B4581881 : Blo 2035435 4581881 := bstep (se 2 (by rfl) ⟨1718205, by rfl⟩ : syracuseStep 4581881 = 3436411) B3436411
theorem B3054587 : Blo 2035435 3054587 := bstep (se 1 (by rfl) ⟨2290940, by rfl⟩ : syracuseStep 3054587 = 4581881) B4581881
theorem B2036391 : Blo 2035435 2036391 := bstep (se 1 (by rfl) ⟨1527293, by rfl⟩ : syracuseStep 2036391 = 3054587) B3054587
theorem B2290945 : Blo 2035435 2290945 := bbase (se 2 (by rfl) ⟨859104, by rfl⟩ : syracuseStep 2290945 = 1718209) (by norm_num)
theorem B3054593 : Blo 2035435 3054593 := bstep (se 2 (by rfl) ⟨1145472, by rfl⟩ : syracuseStep 3054593 = 2290945) B2290945
theorem B2036395 : Blo 2035435 2036395 := bstep (se 1 (by rfl) ⟨1527296, by rfl⟩ : syracuseStep 2036395 = 3054593) B3054593
theorem B5154637 : Blo 2035435 5154637 := bbase (se 3 (by rfl) ⟨966494, by rfl⟩ : syracuseStep 5154637 = 1932989) (by norm_num)
theorem B6872849 : Blo 2035435 6872849 := bstep (se 2 (by rfl) ⟨2577318, by rfl⟩ : syracuseStep 6872849 = 5154637) B5154637
theorem B4581899 : Blo 2035435 4581899 := bstep (se 1 (by rfl) ⟨3436424, by rfl⟩ : syracuseStep 4581899 = 6872849) B6872849
theorem B3054599 : Blo 2035435 3054599 := bstep (se 1 (by rfl) ⟨2290949, by rfl⟩ : syracuseStep 3054599 = 4581899) B4581899
theorem B2036399 : Blo 2035435 2036399 := bstep (se 1 (by rfl) ⟨1527299, by rfl⟩ : syracuseStep 2036399 = 3054599) B3054599
theorem B3054605 : Blo 2035435 3054605 := bbase (se 3 (by rfl) ⟨572738, by rfl⟩ : syracuseStep 3054605 = 1145477) (by norm_num)
theorem B2036403 : Blo 2035435 2036403 := bstep (se 1 (by rfl) ⟨1527302, by rfl⟩ : syracuseStep 2036403 = 3054605) B3054605
theorem B4581917 : Blo 2035435 4581917 := bbase (se 3 (by rfl) ⟨859109, by rfl⟩ : syracuseStep 4581917 = 1718219) (by norm_num)
theorem B3054611 : Blo 2035435 3054611 := bstep (se 1 (by rfl) ⟨2290958, by rfl⟩ : syracuseStep 3054611 = 4581917) B4581917
theorem B2036407 : Blo 2035435 2036407 := bstep (se 1 (by rfl) ⟨1527305, by rfl⟩ : syracuseStep 2036407 = 3054611) B3054611
theorem B3436445 : Blo 2035435 3436445 := bbase (se 3 (by rfl) ⟨644333, by rfl⟩ : syracuseStep 3436445 = 1288667) (by norm_num)
theorem B2290963 : Blo 2035435 2290963 := bstep (se 1 (by rfl) ⟨1718222, by rfl⟩ : syracuseStep 2290963 = 3436445) B3436445
theorem B3054617 : Blo 2035435 3054617 := bstep (se 2 (by rfl) ⟨1145481, by rfl⟩ : syracuseStep 3054617 = 2290963) B2290963
theorem B2036411 : Blo 2035435 2036411 := bstep (se 1 (by rfl) ⟨1527308, by rfl⟩ : syracuseStep 2036411 = 3054617) B3054617
theorem B19571669 : Blo 2035435 19571669 := bbase (se 7 (by rfl) ⟨229355, by rfl⟩ : syracuseStep 19571669 = 458711) (by norm_num)
theorem B13047779 : Blo 2035435 13047779 := bstep (se 1 (by rfl) ⟨9785834, by rfl⟩ : syracuseStep 13047779 = 19571669) B19571669
theorem B8698519 : Blo 2035435 8698519 := bstep (se 1 (by rfl) ⟨6523889, by rfl⟩ : syracuseStep 8698519 = 13047779) B13047779
theorem B11598025 : Blo 2035435 11598025 := bstep (se 2 (by rfl) ⟨4349259, by rfl⟩ : syracuseStep 11598025 = 8698519) B8698519
theorem B15464033 : Blo 2035435 15464033 := bstep (se 2 (by rfl) ⟨5799012, by rfl⟩ : syracuseStep 15464033 = 11598025) B11598025
theorem B10309355 : Blo 2035435 10309355 := bstep (se 1 (by rfl) ⟨7732016, by rfl⟩ : syracuseStep 10309355 = 15464033) B15464033
theorem B6872903 : Blo 2035435 6872903 := bstep (se 1 (by rfl) ⟨5154677, by rfl⟩ : syracuseStep 6872903 = 10309355) B10309355
theorem B4581935 : Blo 2035435 4581935 := bstep (se 1 (by rfl) ⟨3436451, by rfl⟩ : syracuseStep 4581935 = 6872903) B6872903
theorem B3054623 : Blo 2035435 3054623 := bstep (se 1 (by rfl) ⟨2290967, by rfl⟩ : syracuseStep 3054623 = 4581935) B4581935
theorem B2036415 : Blo 2035435 2036415 := bstep (se 1 (by rfl) ⟨1527311, by rfl⟩ : syracuseStep 2036415 = 3054623) B3054623
theorem B3054629 : Blo 2035435 3054629 := bbase (se 4 (by rfl) ⟨286371, by rfl⟩ : syracuseStep 3054629 = 572743) (by norm_num)
theorem B2036419 : Blo 2035435 2036419 := bstep (se 1 (by rfl) ⟨1527314, by rfl⟩ : syracuseStep 2036419 = 3054629) B3054629
theorem B2577349 : Blo 2035435 2577349 := bbase (se 4 (by rfl) ⟨241626, by rfl⟩ : syracuseStep 2577349 = 483253) (by norm_num)
theorem B3436465 : Blo 2035435 3436465 := bstep (se 2 (by rfl) ⟨1288674, by rfl⟩ : syracuseStep 3436465 = 2577349) B2577349
theorem B4581953 : Blo 2035435 4581953 := bstep (se 2 (by rfl) ⟨1718232, by rfl⟩ : syracuseStep 4581953 = 3436465) B3436465
theorem B3054635 : Blo 2035435 3054635 := bstep (se 1 (by rfl) ⟨2290976, by rfl⟩ : syracuseStep 3054635 = 4581953) B4581953
theorem B2036423 : Blo 2035435 2036423 := bstep (se 1 (by rfl) ⟨1527317, by rfl⟩ : syracuseStep 2036423 = 3054635) B3054635
theorem B2290981 : Blo 2035435 2290981 := bbase (se 4 (by rfl) ⟨214779, by rfl⟩ : syracuseStep 2290981 = 429559) (by norm_num)
theorem B3054641 : Blo 2035435 3054641 := bstep (se 2 (by rfl) ⟨1145490, by rfl⟩ : syracuseStep 3054641 = 2290981) B2290981
theorem B2036427 : Blo 2035435 2036427 := bstep (se 1 (by rfl) ⟨1527320, by rfl⟩ : syracuseStep 2036427 = 3054641) B3054641
theorem B4892957 : Blo 2035435 4892957 := bbase (se 3 (by rfl) ⟨917429, by rfl⟩ : syracuseStep 4892957 = 1834859) (by norm_num)
theorem B3261971 : Blo 2035435 3261971 := bstep (se 1 (by rfl) ⟨2446478, by rfl⟩ : syracuseStep 3261971 = 4892957) B4892957
theorem B8698589 : Blo 2035435 8698589 := bstep (se 3 (by rfl) ⟨1630985, by rfl⟩ : syracuseStep 8698589 = 3261971) B3261971
theorem B5799059 : Blo 2035435 5799059 := bstep (se 1 (by rfl) ⟨4349294, by rfl⟩ : syracuseStep 5799059 = 8698589) B8698589
theorem B3866039 : Blo 2035435 3866039 := bstep (se 1 (by rfl) ⟨2899529, by rfl⟩ : syracuseStep 3866039 = 5799059) B5799059
theorem B2577359 : Blo 2035435 2577359 := bstep (se 1 (by rfl) ⟨1933019, by rfl⟩ : syracuseStep 2577359 = 3866039) B3866039
theorem B6872957 : Blo 2035435 6872957 := bstep (se 3 (by rfl) ⟨1288679, by rfl⟩ : syracuseStep 6872957 = 2577359) B2577359
theorem B4581971 : Blo 2035435 4581971 := bstep (se 1 (by rfl) ⟨3436478, by rfl⟩ : syracuseStep 4581971 = 6872957) B6872957
theorem B3054647 : Blo 2035435 3054647 := bstep (se 1 (by rfl) ⟨2290985, by rfl⟩ : syracuseStep 3054647 = 4581971) B4581971
theorem B2036431 : Blo 2035435 2036431 := bstep (se 1 (by rfl) ⟨1527323, by rfl⟩ : syracuseStep 2036431 = 3054647) B3054647
theorem B3054653 : Blo 2035435 3054653 := bbase (se 3 (by rfl) ⟨572747, by rfl⟩ : syracuseStep 3054653 = 1145495) (by norm_num)
theorem B2036435 : Blo 2035435 2036435 := bstep (se 1 (by rfl) ⟨1527326, by rfl⟩ : syracuseStep 2036435 = 3054653) B3054653
theorem B4581989 : Blo 2035435 4581989 := bbase (se 4 (by rfl) ⟨429561, by rfl⟩ : syracuseStep 4581989 = 859123) (by norm_num)
theorem B3054659 : Blo 2035435 3054659 := bstep (se 1 (by rfl) ⟨2290994, by rfl⟩ : syracuseStep 3054659 = 4581989) B4581989
theorem B2036439 : Blo 2035435 2036439 := bstep (se 1 (by rfl) ⟨1527329, by rfl⟩ : syracuseStep 2036439 = 3054659) B3054659
theorem B5154749 : Blo 2035435 5154749 := bbase (se 3 (by rfl) ⟨966515, by rfl⟩ : syracuseStep 5154749 = 1933031) (by norm_num)
theorem B3436499 : Blo 2035435 3436499 := bstep (se 1 (by rfl) ⟨2577374, by rfl⟩ : syracuseStep 3436499 = 5154749) B5154749
theorem B2290999 : Blo 2035435 2290999 := bstep (se 1 (by rfl) ⟨1718249, by rfl⟩ : syracuseStep 2290999 = 3436499) B3436499
theorem B3054665 : Blo 2035435 3054665 := bstep (se 2 (by rfl) ⟨1145499, by rfl⟩ : syracuseStep 3054665 = 2290999) B2290999
theorem B2036443 : Blo 2035435 2036443 := bstep (se 1 (by rfl) ⟨1527332, by rfl⟩ : syracuseStep 2036443 = 3054665) B3054665
theorem B3866069 : Blo 2035435 3866069 := bbase (se 7 (by rfl) ⟨45305, by rfl⟩ : syracuseStep 3866069 = 90611) (by norm_num)
theorem B10309517 : Blo 2035435 10309517 := bstep (se 3 (by rfl) ⟨1933034, by rfl⟩ : syracuseStep 10309517 = 3866069) B3866069
theorem B6873011 : Blo 2035435 6873011 := bstep (se 1 (by rfl) ⟨5154758, by rfl⟩ : syracuseStep 6873011 = 10309517) B10309517
theorem B4582007 : Blo 2035435 4582007 := bstep (se 1 (by rfl) ⟨3436505, by rfl⟩ : syracuseStep 4582007 = 6873011) B6873011
theorem B3054671 : Blo 2035435 3054671 := bstep (se 1 (by rfl) ⟨2291003, by rfl⟩ : syracuseStep 3054671 = 4582007) B4582007
theorem B2036447 : Blo 2035435 2036447 := bstep (se 1 (by rfl) ⟨1527335, by rfl⟩ : syracuseStep 2036447 = 3054671) B3054671
theorem B3054677 : Blo 2035435 3054677 := bbase (se 8 (by rfl) ⟨17898, by rfl⟩ : syracuseStep 3054677 = 35797) (by norm_num)
theorem B2036451 : Blo 2035435 2036451 := bstep (se 1 (by rfl) ⟨1527338, by rfl⟩ : syracuseStep 2036451 = 3054677) B3054677
theorem B2064241 : Blo 2035435 2064241 := bbase (se 2 (by rfl) ⟨774090, by rfl⟩ : syracuseStep 2064241 = 1548181) (by norm_num)
theorem B2752321 : Blo 2035435 2752321 := bstep (se 2 (by rfl) ⟨1032120, by rfl⟩ : syracuseStep 2752321 = 2064241) B2064241
theorem B3669761 : Blo 2035435 3669761 := bstep (se 2 (by rfl) ⟨1376160, by rfl⟩ : syracuseStep 3669761 = 2752321) B2752321
theorem B2446507 : Blo 2035435 2446507 := bstep (se 1 (by rfl) ⟨1834880, by rfl⟩ : syracuseStep 2446507 = 3669761) B3669761
theorem B13048037 : Blo 2035435 13048037 := bstep (se 4 (by rfl) ⟨1223253, by rfl⟩ : syracuseStep 13048037 = 2446507) B2446507
theorem B8698691 : Blo 2035435 8698691 := bstep (se 1 (by rfl) ⟨6524018, by rfl⟩ : syracuseStep 8698691 = 13048037) B13048037
theorem B5799127 : Blo 2035435 5799127 := bstep (se 1 (by rfl) ⟨4349345, by rfl⟩ : syracuseStep 5799127 = 8698691) B8698691
theorem B7732169 : Blo 2035435 7732169 := bstep (se 2 (by rfl) ⟨2899563, by rfl⟩ : syracuseStep 7732169 = 5799127) B5799127
theorem B5154779 : Blo 2035435 5154779 := bstep (se 1 (by rfl) ⟨3866084, by rfl⟩ : syracuseStep 5154779 = 7732169) B7732169
theorem B3436519 : Blo 2035435 3436519 := bstep (se 1 (by rfl) ⟨2577389, by rfl⟩ : syracuseStep 3436519 = 5154779) B5154779
theorem B4582025 : Blo 2035435 4582025 := bstep (se 2 (by rfl) ⟨1718259, by rfl⟩ : syracuseStep 4582025 = 3436519) B3436519
theorem B3054683 : Blo 2035435 3054683 := bstep (se 1 (by rfl) ⟨2291012, by rfl⟩ : syracuseStep 3054683 = 4582025) B4582025
theorem B2036455 : Blo 2035435 2036455 := bstep (se 1 (by rfl) ⟨1527341, by rfl⟩ : syracuseStep 2036455 = 3054683) B3054683
theorem B2291017 : Blo 2035435 2291017 := bbase (se 2 (by rfl) ⟨859131, by rfl⟩ : syracuseStep 2291017 = 1718263) (by norm_num)
theorem B3054689 : Blo 2035435 3054689 := bstep (se 2 (by rfl) ⟨1145508, by rfl⟩ : syracuseStep 3054689 = 2291017) B2291017
theorem B2036459 : Blo 2035435 2036459 := bstep (se 1 (by rfl) ⟨1527344, by rfl⟩ : syracuseStep 2036459 = 3054689) B3054689
theorem B3096373 : Blo 2035435 3096373 := bbase (se 5 (by rfl) ⟨145142, by rfl⟩ : syracuseStep 3096373 = 290285) (by norm_num)
theorem B4128497 : Blo 2035435 4128497 := bstep (se 2 (by rfl) ⟨1548186, by rfl⟩ : syracuseStep 4128497 = 3096373) B3096373
theorem B2752331 : Blo 2035435 2752331 := bstep (se 1 (by rfl) ⟨2064248, by rfl⟩ : syracuseStep 2752331 = 4128497) B4128497
theorem B29358197 : Blo 2035435 29358197 := bstep (se 5 (by rfl) ⟨1376165, by rfl⟩ : syracuseStep 29358197 = 2752331) B2752331
theorem B19572131 : Blo 2035435 19572131 := bstep (se 1 (by rfl) ⟨14679098, by rfl⟩ : syracuseStep 19572131 = 29358197) B29358197
theorem B13048087 : Blo 2035435 13048087 := bstep (se 1 (by rfl) ⟨9786065, by rfl⟩ : syracuseStep 13048087 = 19572131) B19572131
theorem B17397449 : Blo 2035435 17397449 := bstep (se 2 (by rfl) ⟨6524043, by rfl⟩ : syracuseStep 17397449 = 13048087) B13048087
theorem B11598299 : Blo 2035435 11598299 := bstep (se 1 (by rfl) ⟨8698724, by rfl⟩ : syracuseStep 11598299 = 17397449) B17397449
theorem B7732199 : Blo 2035435 7732199 := bstep (se 1 (by rfl) ⟨5799149, by rfl⟩ : syracuseStep 7732199 = 11598299) B11598299
theorem B5154799 : Blo 2035435 5154799 := bstep (se 1 (by rfl) ⟨3866099, by rfl⟩ : syracuseStep 5154799 = 7732199) B7732199
theorem B6873065 : Blo 2035435 6873065 := bstep (se 2 (by rfl) ⟨2577399, by rfl⟩ : syracuseStep 6873065 = 5154799) B5154799
theorem B4582043 : Blo 2035435 4582043 := bstep (se 1 (by rfl) ⟨3436532, by rfl⟩ : syracuseStep 4582043 = 6873065) B6873065
theorem B3054695 : Blo 2035435 3054695 := bstep (se 1 (by rfl) ⟨2291021, by rfl⟩ : syracuseStep 3054695 = 4582043) B4582043
theorem B2036463 : Blo 2035435 2036463 := bstep (se 1 (by rfl) ⟨1527347, by rfl⟩ : syracuseStep 2036463 = 3054695) B3054695
theorem B3054701 : Blo 2035435 3054701 := bbase (se 3 (by rfl) ⟨572756, by rfl⟩ : syracuseStep 3054701 = 1145513) (by norm_num)
theorem B2036467 : Blo 2035435 2036467 := bstep (se 1 (by rfl) ⟨1527350, by rfl⟩ : syracuseStep 2036467 = 3054701) B3054701
theorem B4582061 : Blo 2035435 4582061 := bbase (se 3 (by rfl) ⟨859136, by rfl⟩ : syracuseStep 4582061 = 1718273) (by norm_num)
theorem B3054707 : Blo 2035435 3054707 := bstep (se 1 (by rfl) ⟨2291030, by rfl⟩ : syracuseStep 3054707 = 4582061) B4582061
theorem B2036471 : Blo 2035435 2036471 := bstep (se 1 (by rfl) ⟨1527353, by rfl⟩ : syracuseStep 2036471 = 3054707) B3054707
theorem B4349389 : Blo 2035435 4349389 := bbase (se 3 (by rfl) ⟨815510, by rfl⟩ : syracuseStep 4349389 = 1631021) (by norm_num)
theorem B5799185 : Blo 2035435 5799185 := bstep (se 2 (by rfl) ⟨2174694, by rfl⟩ : syracuseStep 5799185 = 4349389) B4349389
theorem B3866123 : Blo 2035435 3866123 := bstep (se 1 (by rfl) ⟨2899592, by rfl⟩ : syracuseStep 3866123 = 5799185) B5799185
theorem B2577415 : Blo 2035435 2577415 := bstep (se 1 (by rfl) ⟨1933061, by rfl⟩ : syracuseStep 2577415 = 3866123) B3866123
theorem B3436553 : Blo 2035435 3436553 := bstep (se 2 (by rfl) ⟨1288707, by rfl⟩ : syracuseStep 3436553 = 2577415) B2577415
theorem B2291035 : Blo 2035435 2291035 := bstep (se 1 (by rfl) ⟨1718276, by rfl⟩ : syracuseStep 2291035 = 3436553) B3436553
theorem B3054713 : Blo 2035435 3054713 := bstep (se 2 (by rfl) ⟨1145517, by rfl⟩ : syracuseStep 3054713 = 2291035) B2291035
theorem B2036475 : Blo 2035435 2036475 := bstep (se 1 (by rfl) ⟨1527356, by rfl⟩ : syracuseStep 2036475 = 3054713) B3054713
theorem B2612585 : Blo 2035435 2612585 := bbase (se 2 (by rfl) ⟨979719, by rfl⟩ : syracuseStep 2612585 = 1959439) (by norm_num)
theorem B6966893 : Blo 2035435 6966893 := bstep (se 3 (by rfl) ⟨1306292, by rfl⟩ : syracuseStep 6966893 = 2612585) B2612585
theorem B4644595 : Blo 2035435 4644595 := bstep (se 1 (by rfl) ⟨3483446, by rfl⟩ : syracuseStep 4644595 = 6966893) B6966893
theorem B6192793 : Blo 2035435 6192793 := bstep (se 2 (by rfl) ⟨2322297, by rfl⟩ : syracuseStep 6192793 = 4644595) B4644595
theorem B33028229 : Blo 2035435 33028229 := bstep (se 4 (by rfl) ⟨3096396, by rfl⟩ : syracuseStep 33028229 = 6192793) B6192793
theorem B22018819 : Blo 2035435 22018819 := bstep (se 1 (by rfl) ⟨16514114, by rfl⟩ : syracuseStep 22018819 = 33028229) B33028229
theorem B29358425 : Blo 2035435 29358425 := bstep (se 2 (by rfl) ⟨11009409, by rfl⟩ : syracuseStep 29358425 = 22018819) B22018819
theorem B19572283 : Blo 2035435 19572283 := bstep (se 1 (by rfl) ⟨14679212, by rfl⟩ : syracuseStep 19572283 = 29358425) B29358425
theorem B26096377 : Blo 2035435 26096377 := bstep (se 2 (by rfl) ⟨9786141, by rfl⟩ : syracuseStep 26096377 = 19572283) B19572283
theorem B34795169 : Blo 2035435 34795169 := bstep (se 2 (by rfl) ⟨13048188, by rfl⟩ : syracuseStep 34795169 = 26096377) B26096377
theorem B23196779 : Blo 2035435 23196779 := bstep (se 1 (by rfl) ⟨17397584, by rfl⟩ : syracuseStep 23196779 = 34795169) B34795169
theorem B15464519 : Blo 2035435 15464519 := bstep (se 1 (by rfl) ⟨11598389, by rfl⟩ : syracuseStep 15464519 = 23196779) B23196779
theorem B10309679 : Blo 2035435 10309679 := bstep (se 1 (by rfl) ⟨7732259, by rfl⟩ : syracuseStep 10309679 = 15464519) B15464519
theorem B6873119 : Blo 2035435 6873119 := bstep (se 1 (by rfl) ⟨5154839, by rfl⟩ : syracuseStep 6873119 = 10309679) B10309679
theorem B4582079 : Blo 2035435 4582079 := bstep (se 1 (by rfl) ⟨3436559, by rfl⟩ : syracuseStep 4582079 = 6873119) B6873119
theorem B3054719 : Blo 2035435 3054719 := bstep (se 1 (by rfl) ⟨2291039, by rfl⟩ : syracuseStep 3054719 = 4582079) B4582079
theorem B2036479 : Blo 2035435 2036479 := bstep (se 1 (by rfl) ⟨1527359, by rfl⟩ : syracuseStep 2036479 = 3054719) B3054719
theorem B3054725 : Blo 2035435 3054725 := bbase (se 4 (by rfl) ⟨286380, by rfl⟩ : syracuseStep 3054725 = 572761) (by norm_num)
theorem B2036483 : Blo 2035435 2036483 := bstep (se 1 (by rfl) ⟨1527362, by rfl⟩ : syracuseStep 2036483 = 3054725) B3054725
theorem B3436573 : Blo 2035435 3436573 := bbase (se 3 (by rfl) ⟨644357, by rfl⟩ : syracuseStep 3436573 = 1288715) (by norm_num)
theorem B4582097 : Blo 2035435 4582097 := bstep (se 2 (by rfl) ⟨1718286, by rfl⟩ : syracuseStep 4582097 = 3436573) B3436573
theorem B3054731 : Blo 2035435 3054731 := bstep (se 1 (by rfl) ⟨2291048, by rfl⟩ : syracuseStep 3054731 = 4582097) B4582097
theorem B2036487 : Blo 2035435 2036487 := bstep (se 1 (by rfl) ⟨1527365, by rfl⟩ : syracuseStep 2036487 = 3054731) B3054731
theorem B2291053 : Blo 2035435 2291053 := bbase (se 3 (by rfl) ⟨429572, by rfl⟩ : syracuseStep 2291053 = 859145) (by norm_num)
theorem B3054737 : Blo 2035435 3054737 := bstep (se 2 (by rfl) ⟨1145526, by rfl⟩ : syracuseStep 3054737 = 2291053) B2291053
theorem B2036491 : Blo 2035435 2036491 := bstep (se 1 (by rfl) ⟨1527368, by rfl⟩ : syracuseStep 2036491 = 3054737) B3054737
theorem B6873173 : Blo 2035435 6873173 := bbase (se 8 (by rfl) ⟨40272, by rfl⟩ : syracuseStep 6873173 = 80545) (by norm_num)
theorem B4582115 : Blo 2035435 4582115 := bstep (se 1 (by rfl) ⟨3436586, by rfl⟩ : syracuseStep 4582115 = 6873173) B6873173
theorem B3054743 : Blo 2035435 3054743 := bstep (se 1 (by rfl) ⟨2291057, by rfl⟩ : syracuseStep 3054743 = 4582115) B4582115
theorem B2036495 : Blo 2035435 2036495 := bstep (se 1 (by rfl) ⟨1527371, by rfl⟩ : syracuseStep 2036495 = 3054743) B3054743
theorem B3054749 : Blo 2035435 3054749 := bbase (se 3 (by rfl) ⟨572765, by rfl⟩ : syracuseStep 3054749 = 1145531) (by norm_num)
theorem B2036499 : Blo 2035435 2036499 := bstep (se 1 (by rfl) ⟨1527374, by rfl⟩ : syracuseStep 2036499 = 3054749) B3054749
theorem B4582133 : Blo 2035435 4582133 := bbase (se 5 (by rfl) ⟨214787, by rfl⟩ : syracuseStep 4582133 = 429575) (by norm_num)
theorem B3054755 : Blo 2035435 3054755 := bstep (se 1 (by rfl) ⟨2291066, by rfl⟩ : syracuseStep 3054755 = 4582133) B4582133
theorem B2036503 : Blo 2035435 2036503 := bstep (se 1 (by rfl) ⟨1527377, by rfl⟩ : syracuseStep 2036503 = 3054755) B3054755
theorem B4644661 : Blo 2035435 4644661 := bbase (se 5 (by rfl) ⟨217718, by rfl⟩ : syracuseStep 4644661 = 435437) (by norm_num)
theorem B6192881 : Blo 2035435 6192881 := bstep (se 2 (by rfl) ⟨2322330, by rfl⟩ : syracuseStep 6192881 = 4644661) B4644661
theorem B4128587 : Blo 2035435 4128587 := bstep (se 1 (by rfl) ⟨3096440, by rfl⟩ : syracuseStep 4128587 = 6192881) B6192881
theorem B2752391 : Blo 2035435 2752391 := bstep (se 1 (by rfl) ⟨2064293, by rfl⟩ : syracuseStep 2752391 = 4128587) B4128587
theorem B7339709 : Blo 2035435 7339709 := bstep (se 3 (by rfl) ⟨1376195, by rfl⟩ : syracuseStep 7339709 = 2752391) B2752391
theorem B4893139 : Blo 2035435 4893139 := bstep (se 1 (by rfl) ⟨3669854, by rfl⟩ : syracuseStep 4893139 = 7339709) B7339709
theorem B26096741 : Blo 2035435 26096741 := bstep (se 4 (by rfl) ⟨2446569, by rfl⟩ : syracuseStep 26096741 = 4893139) B4893139
theorem B17397827 : Blo 2035435 17397827 := bstep (se 1 (by rfl) ⟨13048370, by rfl⟩ : syracuseStep 17397827 = 26096741) B26096741
theorem B11598551 : Blo 2035435 11598551 := bstep (se 1 (by rfl) ⟨8698913, by rfl⟩ : syracuseStep 11598551 = 17397827) B17397827
theorem B7732367 : Blo 2035435 7732367 := bstep (se 1 (by rfl) ⟨5799275, by rfl⟩ : syracuseStep 7732367 = 11598551) B11598551
theorem B5154911 : Blo 2035435 5154911 := bstep (se 1 (by rfl) ⟨3866183, by rfl⟩ : syracuseStep 5154911 = 7732367) B7732367
theorem B3436607 : Blo 2035435 3436607 := bstep (se 1 (by rfl) ⟨2577455, by rfl⟩ : syracuseStep 3436607 = 5154911) B5154911
theorem B2291071 : Blo 2035435 2291071 := bstep (se 1 (by rfl) ⟨1718303, by rfl⟩ : syracuseStep 2291071 = 3436607) B3436607
theorem B3054761 : Blo 2035435 3054761 := bstep (se 2 (by rfl) ⟨1145535, by rfl⟩ : syracuseStep 3054761 = 2291071) B2291071
theorem B2036507 : Blo 2035435 2036507 := bstep (se 1 (by rfl) ⟨1527380, by rfl⟩ : syracuseStep 2036507 = 3054761) B3054761
theorem B4893149 : Blo 2035435 4893149 := bbase (se 3 (by rfl) ⟨917465, by rfl⟩ : syracuseStep 4893149 = 1834931) (by norm_num)
theorem B3262099 : Blo 2035435 3262099 := bstep (se 1 (by rfl) ⟨2446574, by rfl⟩ : syracuseStep 3262099 = 4893149) B4893149
theorem B4349465 : Blo 2035435 4349465 := bstep (se 2 (by rfl) ⟨1631049, by rfl⟩ : syracuseStep 4349465 = 3262099) B3262099
theorem B2899643 : Blo 2035435 2899643 := bstep (se 1 (by rfl) ⟨2174732, by rfl⟩ : syracuseStep 2899643 = 4349465) B4349465
theorem B7732381 : Blo 2035435 7732381 := bstep (se 3 (by rfl) ⟨1449821, by rfl⟩ : syracuseStep 7732381 = 2899643) B2899643
theorem B10309841 : Blo 2035435 10309841 := bstep (se 2 (by rfl) ⟨3866190, by rfl⟩ : syracuseStep 10309841 = 7732381) B7732381
theorem B6873227 : Blo 2035435 6873227 := bstep (se 1 (by rfl) ⟨5154920, by rfl⟩ : syracuseStep 6873227 = 10309841) B10309841
theorem B4582151 : Blo 2035435 4582151 := bstep (se 1 (by rfl) ⟨3436613, by rfl⟩ : syracuseStep 4582151 = 6873227) B6873227
theorem B3054767 : Blo 2035435 3054767 := bstep (se 1 (by rfl) ⟨2291075, by rfl⟩ : syracuseStep 3054767 = 4582151) B4582151
theorem B2036511 : Blo 2035435 2036511 := bstep (se 1 (by rfl) ⟨1527383, by rfl⟩ : syracuseStep 2036511 = 3054767) B3054767
theorem B3054773 : Blo 2035435 3054773 := bbase (se 5 (by rfl) ⟨143192, by rfl⟩ : syracuseStep 3054773 = 286385) (by norm_num)
theorem B2036515 : Blo 2035435 2036515 := bstep (se 1 (by rfl) ⟨1527386, by rfl⟩ : syracuseStep 2036515 = 3054773) B3054773
theorem B5154941 : Blo 2035435 5154941 := bbase (se 3 (by rfl) ⟨966551, by rfl⟩ : syracuseStep 5154941 = 1933103) (by norm_num)
theorem B3436627 : Blo 2035435 3436627 := bstep (se 1 (by rfl) ⟨2577470, by rfl⟩ : syracuseStep 3436627 = 5154941) B5154941
theorem B4582169 : Blo 2035435 4582169 := bstep (se 2 (by rfl) ⟨1718313, by rfl⟩ : syracuseStep 4582169 = 3436627) B3436627
theorem B3054779 : Blo 2035435 3054779 := bstep (se 1 (by rfl) ⟨2291084, by rfl⟩ : syracuseStep 3054779 = 4582169) B4582169
theorem B2036519 : Blo 2035435 2036519 := bstep (se 1 (by rfl) ⟨1527389, by rfl⟩ : syracuseStep 2036519 = 3054779) B3054779
theorem B2291089 : Blo 2035435 2291089 := bbase (se 2 (by rfl) ⟨859158, by rfl⟩ : syracuseStep 2291089 = 1718317) (by norm_num)
theorem B3054785 : Blo 2035435 3054785 := bstep (se 2 (by rfl) ⟨1145544, by rfl⟩ : syracuseStep 3054785 = 2291089) B2291089
theorem B2036523 : Blo 2035435 2036523 := bstep (se 1 (by rfl) ⟨1527392, by rfl⟩ : syracuseStep 2036523 = 3054785) B3054785
theorem B3866221 : Blo 2035435 3866221 := bbase (se 3 (by rfl) ⟨724916, by rfl⟩ : syracuseStep 3866221 = 1449833) (by norm_num)
theorem B5154961 : Blo 2035435 5154961 := bstep (se 2 (by rfl) ⟨1933110, by rfl⟩ : syracuseStep 5154961 = 3866221) B3866221
theorem B6873281 : Blo 2035435 6873281 := bstep (se 2 (by rfl) ⟨2577480, by rfl⟩ : syracuseStep 6873281 = 5154961) B5154961
theorem B4582187 : Blo 2035435 4582187 := bstep (se 1 (by rfl) ⟨3436640, by rfl⟩ : syracuseStep 4582187 = 6873281) B6873281
theorem B3054791 : Blo 2035435 3054791 := bstep (se 1 (by rfl) ⟨2291093, by rfl⟩ : syracuseStep 3054791 = 4582187) B4582187
theorem B2036527 : Blo 2035435 2036527 := bstep (se 1 (by rfl) ⟨1527395, by rfl⟩ : syracuseStep 2036527 = 3054791) B3054791
theorem B3054797 : Blo 2035435 3054797 := bbase (se 3 (by rfl) ⟨572774, by rfl⟩ : syracuseStep 3054797 = 1145549) (by norm_num)
theorem B2036531 : Blo 2035435 2036531 := bstep (se 1 (by rfl) ⟨1527398, by rfl⟩ : syracuseStep 2036531 = 3054797) B3054797
theorem B4582205 : Blo 2035435 4582205 := bbase (se 3 (by rfl) ⟨859163, by rfl⟩ : syracuseStep 4582205 = 1718327) (by norm_num)
theorem B3054803 : Blo 2035435 3054803 := bstep (se 1 (by rfl) ⟨2291102, by rfl⟩ : syracuseStep 3054803 = 4582205) B4582205
theorem B2036535 : Blo 2035435 2036535 := bstep (se 1 (by rfl) ⟨1527401, by rfl⟩ : syracuseStep 2036535 = 3054803) B3054803
theorem B3436661 : Blo 2035435 3436661 := bbase (se 5 (by rfl) ⟨161093, by rfl⟩ : syracuseStep 3436661 = 322187) (by norm_num)
theorem B2291107 : Blo 2035435 2291107 := bstep (se 1 (by rfl) ⟨1718330, by rfl⟩ : syracuseStep 2291107 = 3436661) B3436661
theorem B3054809 : Blo 2035435 3054809 := bstep (se 2 (by rfl) ⟨1145553, by rfl⟩ : syracuseStep 3054809 = 2291107) B2291107
theorem B2036539 : Blo 2035435 2036539 := bstep (se 1 (by rfl) ⟨1527404, by rfl⟩ : syracuseStep 2036539 = 3054809) B3054809
theorem B4349533 : Blo 2035435 4349533 := bbase (se 3 (by rfl) ⟨815537, by rfl⟩ : syracuseStep 4349533 = 1631075) (by norm_num)
theorem B5799377 : Blo 2035435 5799377 := bstep (se 2 (by rfl) ⟨2174766, by rfl⟩ : syracuseStep 5799377 = 4349533) B4349533
theorem B15465005 : Blo 2035435 15465005 := bstep (se 3 (by rfl) ⟨2899688, by rfl⟩ : syracuseStep 15465005 = 5799377) B5799377
theorem B10310003 : Blo 2035435 10310003 := bstep (se 1 (by rfl) ⟨7732502, by rfl⟩ : syracuseStep 10310003 = 15465005) B15465005
theorem B6873335 : Blo 2035435 6873335 := bstep (se 1 (by rfl) ⟨5155001, by rfl⟩ : syracuseStep 6873335 = 10310003) B10310003
theorem B4582223 : Blo 2035435 4582223 := bstep (se 1 (by rfl) ⟨3436667, by rfl⟩ : syracuseStep 4582223 = 6873335) B6873335
theorem B3054815 : Blo 2035435 3054815 := bstep (se 1 (by rfl) ⟨2291111, by rfl⟩ : syracuseStep 3054815 = 4582223) B4582223
theorem B2036543 : Blo 2035435 2036543 := bstep (se 1 (by rfl) ⟨1527407, by rfl⟩ : syracuseStep 2036543 = 3054815) B3054815
theorem B3054821 : Blo 2035435 3054821 := bbase (se 4 (by rfl) ⟨286389, by rfl⟩ : syracuseStep 3054821 = 572779) (by norm_num)
theorem B2036547 : Blo 2035435 2036547 := bstep (se 1 (by rfl) ⟨1527410, by rfl⟩ : syracuseStep 2036547 = 3054821) B3054821
theorem B5225357 : Blo 2035435 5225357 := bbase (se 3 (by rfl) ⟨979754, by rfl⟩ : syracuseStep 5225357 = 1959509) (by norm_num)
theorem B3483571 : Blo 2035435 3483571 := bstep (se 1 (by rfl) ⟨2612678, by rfl⟩ : syracuseStep 3483571 = 5225357) B5225357
theorem B4644761 : Blo 2035435 4644761 := bstep (se 2 (by rfl) ⟨1741785, by rfl⟩ : syracuseStep 4644761 = 3483571) B3483571
theorem B12386029 : Blo 2035435 12386029 := bstep (se 3 (by rfl) ⟨2322380, by rfl⟩ : syracuseStep 12386029 = 4644761) B4644761
theorem B16514705 : Blo 2035435 16514705 := bstep (se 2 (by rfl) ⟨6193014, by rfl⟩ : syracuseStep 16514705 = 12386029) B12386029
theorem B11009803 : Blo 2035435 11009803 := bstep (se 1 (by rfl) ⟨8257352, by rfl⟩ : syracuseStep 11009803 = 16514705) B16514705
theorem B14679737 : Blo 2035435 14679737 := bstep (se 2 (by rfl) ⟨5504901, by rfl⟩ : syracuseStep 14679737 = 11009803) B11009803
theorem B9786491 : Blo 2035435 9786491 := bstep (se 1 (by rfl) ⟨7339868, by rfl⟩ : syracuseStep 9786491 = 14679737) B14679737
theorem B6524327 : Blo 2035435 6524327 := bstep (se 1 (by rfl) ⟨4893245, by rfl⟩ : syracuseStep 6524327 = 9786491) B9786491
theorem B4349551 : Blo 2035435 4349551 := bstep (se 1 (by rfl) ⟨3262163, by rfl⟩ : syracuseStep 4349551 = 6524327) B6524327
theorem B5799401 : Blo 2035435 5799401 := bstep (se 2 (by rfl) ⟨2174775, by rfl⟩ : syracuseStep 5799401 = 4349551) B4349551
theorem B3866267 : Blo 2035435 3866267 := bstep (se 1 (by rfl) ⟨2899700, by rfl⟩ : syracuseStep 3866267 = 5799401) B5799401
theorem B2577511 : Blo 2035435 2577511 := bstep (se 1 (by rfl) ⟨1933133, by rfl⟩ : syracuseStep 2577511 = 3866267) B3866267
theorem B3436681 : Blo 2035435 3436681 := bstep (se 2 (by rfl) ⟨1288755, by rfl⟩ : syracuseStep 3436681 = 2577511) B2577511
theorem B4582241 : Blo 2035435 4582241 := bstep (se 2 (by rfl) ⟨1718340, by rfl⟩ : syracuseStep 4582241 = 3436681) B3436681
theorem B3054827 : Blo 2035435 3054827 := bstep (se 1 (by rfl) ⟨2291120, by rfl⟩ : syracuseStep 3054827 = 4582241) B4582241
theorem B2036551 : Blo 2035435 2036551 := bstep (se 1 (by rfl) ⟨1527413, by rfl⟩ : syracuseStep 2036551 = 3054827) B3054827
theorem B2291125 : Blo 2035435 2291125 := bbase (se 5 (by rfl) ⟨107396, by rfl⟩ : syracuseStep 2291125 = 214793) (by norm_num)
theorem B3054833 : Blo 2035435 3054833 := bstep (se 2 (by rfl) ⟨1145562, by rfl⟩ : syracuseStep 3054833 = 2291125) B2291125
theorem B2036555 : Blo 2035435 2036555 := bstep (se 1 (by rfl) ⟨1527416, by rfl⟩ : syracuseStep 2036555 = 3054833) B3054833
theorem B2577521 : Blo 2035435 2577521 := bbase (se 2 (by rfl) ⟨966570, by rfl⟩ : syracuseStep 2577521 = 1933141) (by norm_num)
theorem B6873389 : Blo 2035435 6873389 := bstep (se 3 (by rfl) ⟨1288760, by rfl⟩ : syracuseStep 6873389 = 2577521) B2577521
theorem B4582259 : Blo 2035435 4582259 := bstep (se 1 (by rfl) ⟨3436694, by rfl⟩ : syracuseStep 4582259 = 6873389) B6873389
theorem B3054839 : Blo 2035435 3054839 := bstep (se 1 (by rfl) ⟨2291129, by rfl⟩ : syracuseStep 3054839 = 4582259) B4582259
theorem B2036559 : Blo 2035435 2036559 := bstep (se 1 (by rfl) ⟨1527419, by rfl⟩ : syracuseStep 2036559 = 3054839) B3054839
theorem B3054845 : Blo 2035435 3054845 := bbase (se 3 (by rfl) ⟨572783, by rfl⟩ : syracuseStep 3054845 = 1145567) (by norm_num)
theorem B2036563 : Blo 2035435 2036563 := bstep (se 1 (by rfl) ⟨1527422, by rfl⟩ : syracuseStep 2036563 = 3054845) B3054845
theorem B4582277 : Blo 2035435 4582277 := bbase (se 4 (by rfl) ⟨429588, by rfl⟩ : syracuseStep 4582277 = 859177) (by norm_num)
theorem B3054851 : Blo 2035435 3054851 := bstep (se 1 (by rfl) ⟨2291138, by rfl⟩ : syracuseStep 3054851 = 4582277) B4582277
theorem B2036567 : Blo 2035435 2036567 := bstep (se 1 (by rfl) ⟨1527425, by rfl⟩ : syracuseStep 2036567 = 3054851) B3054851
theorem B2174797 : Blo 2035435 2174797 := bbase (se 3 (by rfl) ⟨407774, by rfl⟩ : syracuseStep 2174797 = 815549) (by norm_num)
theorem B2899729 : Blo 2035435 2899729 := bstep (se 2 (by rfl) ⟨1087398, by rfl⟩ : syracuseStep 2899729 = 2174797) B2174797
theorem B3866305 : Blo 2035435 3866305 := bstep (se 2 (by rfl) ⟨1449864, by rfl⟩ : syracuseStep 3866305 = 2899729) B2899729
theorem B5155073 : Blo 2035435 5155073 := bstep (se 2 (by rfl) ⟨1933152, by rfl⟩ : syracuseStep 5155073 = 3866305) B3866305
theorem B3436715 : Blo 2035435 3436715 := bstep (se 1 (by rfl) ⟨2577536, by rfl⟩ : syracuseStep 3436715 = 5155073) B5155073
theorem B2291143 : Blo 2035435 2291143 := bstep (se 1 (by rfl) ⟨1718357, by rfl⟩ : syracuseStep 2291143 = 3436715) B3436715
theorem B3054857 : Blo 2035435 3054857 := bstep (se 2 (by rfl) ⟨1145571, by rfl⟩ : syracuseStep 3054857 = 2291143) B2291143
theorem B2036571 : Blo 2035435 2036571 := bstep (se 1 (by rfl) ⟨1527428, by rfl⟩ : syracuseStep 2036571 = 3054857) B3054857
theorem B10310165 : Blo 2035435 10310165 := bbase (se 6 (by rfl) ⟨241644, by rfl⟩ : syracuseStep 10310165 = 483289) (by norm_num)
theorem B6873443 : Blo 2035435 6873443 := bstep (se 1 (by rfl) ⟨5155082, by rfl⟩ : syracuseStep 6873443 = 10310165) B10310165
theorem B4582295 : Blo 2035435 4582295 := bstep (se 1 (by rfl) ⟨3436721, by rfl⟩ : syracuseStep 4582295 = 6873443) B6873443
theorem B3054863 : Blo 2035435 3054863 := bstep (se 1 (by rfl) ⟨2291147, by rfl⟩ : syracuseStep 3054863 = 4582295) B4582295
theorem B2036575 : Blo 2035435 2036575 := bstep (se 1 (by rfl) ⟨1527431, by rfl⟩ : syracuseStep 2036575 = 3054863) B3054863
theorem B3054869 : Blo 2035435 3054869 := bbase (se 6 (by rfl) ⟨71598, by rfl⟩ : syracuseStep 3054869 = 143197) (by norm_num)
theorem B2036579 : Blo 2035435 2036579 := bstep (se 1 (by rfl) ⟨1527434, by rfl⟩ : syracuseStep 2036579 = 3054869) B3054869
theorem B50906069 : Blo 2035435 50906069 := bbase (se 7 (by rfl) ⟨596555, by rfl⟩ : syracuseStep 50906069 = 1193111) (by norm_num)
theorem B33937379 : Blo 2035435 33937379 := bstep (se 1 (by rfl) ⟨25453034, by rfl⟩ : syracuseStep 33937379 = 50906069) B50906069
theorem B22624919 : Blo 2035435 22624919 := bstep (se 1 (by rfl) ⟨16968689, by rfl⟩ : syracuseStep 22624919 = 33937379) B33937379
theorem B15083279 : Blo 2035435 15083279 := bstep (se 1 (by rfl) ⟨11312459, by rfl⟩ : syracuseStep 15083279 = 22624919) B22624919
theorem B10055519 : Blo 2035435 10055519 := bstep (se 1 (by rfl) ⟨7541639, by rfl⟩ : syracuseStep 10055519 = 15083279) B15083279
theorem B6703679 : Blo 2035435 6703679 := bstep (se 1 (by rfl) ⟨5027759, by rfl⟩ : syracuseStep 6703679 = 10055519) B10055519
theorem B17876477 : Blo 2035435 17876477 := bstep (se 3 (by rfl) ⟨3351839, by rfl⟩ : syracuseStep 17876477 = 6703679) B6703679
theorem B11917651 : Blo 2035435 11917651 := bstep (se 1 (by rfl) ⟨8938238, by rfl⟩ : syracuseStep 11917651 = 17876477) B17876477
theorem B15890201 : Blo 2035435 15890201 := bstep (se 2 (by rfl) ⟨5958825, by rfl⟩ : syracuseStep 15890201 = 11917651) B11917651
theorem B10593467 : Blo 2035435 10593467 := bstep (se 1 (by rfl) ⟨7945100, by rfl⟩ : syracuseStep 10593467 = 15890201) B15890201
theorem B7062311 : Blo 2035435 7062311 := bstep (se 1 (by rfl) ⟨5296733, by rfl⟩ : syracuseStep 7062311 = 10593467) B10593467
theorem B4708207 : Blo 2035435 4708207 := bstep (se 1 (by rfl) ⟨3531155, by rfl⟩ : syracuseStep 4708207 = 7062311) B7062311
theorem B6277609 : Blo 2035435 6277609 := bstep (se 2 (by rfl) ⟨2354103, by rfl⟩ : syracuseStep 6277609 = 4708207) B4708207
theorem B8370145 : Blo 2035435 8370145 := bstep (se 2 (by rfl) ⟨3138804, by rfl⟩ : syracuseStep 8370145 = 6277609) B6277609
theorem B11160193 : Blo 2035435 11160193 := bstep (se 2 (by rfl) ⟨4185072, by rfl⟩ : syracuseStep 11160193 = 8370145) B8370145
theorem B14880257 : Blo 2035435 14880257 := bstep (se 2 (by rfl) ⟨5580096, by rfl⟩ : syracuseStep 14880257 = 11160193) B11160193
theorem B9920171 : Blo 2035435 9920171 := bstep (se 1 (by rfl) ⟨7440128, by rfl⟩ : syracuseStep 9920171 = 14880257) B14880257
theorem B6613447 : Blo 2035435 6613447 := bstep (se 1 (by rfl) ⟨4960085, by rfl⟩ : syracuseStep 6613447 = 9920171) B9920171
theorem B8817929 : Blo 2035435 8817929 := bstep (se 2 (by rfl) ⟨3306723, by rfl⟩ : syracuseStep 8817929 = 6613447) B6613447
theorem B5878619 : Blo 2035435 5878619 := bstep (se 1 (by rfl) ⟨4408964, by rfl⟩ : syracuseStep 5878619 = 8817929) B8817929
theorem B3919079 : Blo 2035435 3919079 := bstep (se 1 (by rfl) ⟨2939309, by rfl⟩ : syracuseStep 3919079 = 5878619) B5878619
theorem B2612719 : Blo 2035435 2612719 := bstep (se 1 (by rfl) ⟨1959539, by rfl⟩ : syracuseStep 2612719 = 3919079) B3919079
theorem B13934501 : Blo 2035435 13934501 := bstep (se 4 (by rfl) ⟨1306359, by rfl⟩ : syracuseStep 13934501 = 2612719) B2612719
theorem B9289667 : Blo 2035435 9289667 := bstep (se 1 (by rfl) ⟨6967250, by rfl⟩ : syracuseStep 9289667 = 13934501) B13934501
theorem B6193111 : Blo 2035435 6193111 := bstep (se 1 (by rfl) ⟨4644833, by rfl⟩ : syracuseStep 6193111 = 9289667) B9289667
theorem B8257481 : Blo 2035435 8257481 := bstep (se 2 (by rfl) ⟨3096555, by rfl⟩ : syracuseStep 8257481 = 6193111) B6193111
theorem B5504987 : Blo 2035435 5504987 := bstep (se 1 (by rfl) ⟨4128740, by rfl⟩ : syracuseStep 5504987 = 8257481) B8257481
theorem B3669991 : Blo 2035435 3669991 := bstep (se 1 (by rfl) ⟨2752493, by rfl⟩ : syracuseStep 3669991 = 5504987) B5504987
theorem B19573285 : Blo 2035435 19573285 := bstep (se 4 (by rfl) ⟨1834995, by rfl⟩ : syracuseStep 19573285 = 3669991) B3669991
theorem B26097713 : Blo 2035435 26097713 := bstep (se 2 (by rfl) ⟨9786642, by rfl⟩ : syracuseStep 26097713 = 19573285) B19573285
theorem B17398475 : Blo 2035435 17398475 := bstep (se 1 (by rfl) ⟨13048856, by rfl⟩ : syracuseStep 17398475 = 26097713) B26097713
theorem B11598983 : Blo 2035435 11598983 := bstep (se 1 (by rfl) ⟨8699237, by rfl⟩ : syracuseStep 11598983 = 17398475) B17398475
theorem B7732655 : Blo 2035435 7732655 := bstep (se 1 (by rfl) ⟨5799491, by rfl⟩ : syracuseStep 7732655 = 11598983) B11598983
theorem B5155103 : Blo 2035435 5155103 := bstep (se 1 (by rfl) ⟨3866327, by rfl⟩ : syracuseStep 5155103 = 7732655) B7732655
theorem B3436735 : Blo 2035435 3436735 := bstep (se 1 (by rfl) ⟨2577551, by rfl⟩ : syracuseStep 3436735 = 5155103) B5155103
theorem B4582313 : Blo 2035435 4582313 := bstep (se 2 (by rfl) ⟨1718367, by rfl⟩ : syracuseStep 4582313 = 3436735) B3436735
theorem B3054875 : Blo 2035435 3054875 := bstep (se 1 (by rfl) ⟨2291156, by rfl⟩ : syracuseStep 3054875 = 4582313) B4582313
theorem B2036583 : Blo 2035435 2036583 := bstep (se 1 (by rfl) ⟨1527437, by rfl⟩ : syracuseStep 2036583 = 3054875) B3054875
theorem B2291161 : Blo 2035435 2291161 := bbase (se 2 (by rfl) ⟨859185, by rfl⟩ : syracuseStep 2291161 = 1718371) (by norm_num)
theorem B3054881 : Blo 2035435 3054881 := bstep (se 2 (by rfl) ⟨1145580, by rfl⟩ : syracuseStep 3054881 = 2291161) B2291161
theorem B2036587 : Blo 2035435 2036587 := bstep (se 1 (by rfl) ⟨1527440, by rfl⟩ : syracuseStep 2036587 = 3054881) B3054881
theorem B2899757 : Blo 2035435 2899757 := bbase (se 3 (by rfl) ⟨543704, by rfl⟩ : syracuseStep 2899757 = 1087409) (by norm_num)
theorem B7732685 : Blo 2035435 7732685 := bstep (se 3 (by rfl) ⟨1449878, by rfl⟩ : syracuseStep 7732685 = 2899757) B2899757
theorem B5155123 : Blo 2035435 5155123 := bstep (se 1 (by rfl) ⟨3866342, by rfl⟩ : syracuseStep 5155123 = 7732685) B7732685
theorem B6873497 : Blo 2035435 6873497 := bstep (se 2 (by rfl) ⟨2577561, by rfl⟩ : syracuseStep 6873497 = 5155123) B5155123
theorem B4582331 : Blo 2035435 4582331 := bstep (se 1 (by rfl) ⟨3436748, by rfl⟩ : syracuseStep 4582331 = 6873497) B6873497
theorem B3054887 : Blo 2035435 3054887 := bstep (se 1 (by rfl) ⟨2291165, by rfl⟩ : syracuseStep 3054887 = 4582331) B4582331
theorem B2036591 : Blo 2035435 2036591 := bstep (se 1 (by rfl) ⟨1527443, by rfl⟩ : syracuseStep 2036591 = 3054887) B3054887
theorem B3054893 : Blo 2035435 3054893 := bbase (se 3 (by rfl) ⟨572792, by rfl⟩ : syracuseStep 3054893 = 1145585) (by norm_num)
theorem B2036595 : Blo 2035435 2036595 := bstep (se 1 (by rfl) ⟨1527446, by rfl⟩ : syracuseStep 2036595 = 3054893) B3054893
theorem B4582349 : Blo 2035435 4582349 := bbase (se 3 (by rfl) ⟨859190, by rfl⟩ : syracuseStep 4582349 = 1718381) (by norm_num)
theorem B3054899 : Blo 2035435 3054899 := bstep (se 1 (by rfl) ⟨2291174, by rfl⟩ : syracuseStep 3054899 = 4582349) B4582349
theorem B2036599 : Blo 2035435 2036599 := bstep (se 1 (by rfl) ⟨1527449, by rfl⟩ : syracuseStep 2036599 = 3054899) B3054899
theorem B2577577 : Blo 2035435 2577577 := bbase (se 2 (by rfl) ⟨966591, by rfl⟩ : syracuseStep 2577577 = 1933183) (by norm_num)
theorem B3436769 : Blo 2035435 3436769 := bstep (se 2 (by rfl) ⟨1288788, by rfl⟩ : syracuseStep 3436769 = 2577577) B2577577
theorem B2291179 : Blo 2035435 2291179 := bstep (se 1 (by rfl) ⟨1718384, by rfl⟩ : syracuseStep 2291179 = 3436769) B3436769
theorem B3054905 : Blo 2035435 3054905 := bstep (se 2 (by rfl) ⟨1145589, by rfl⟩ : syracuseStep 3054905 = 2291179) B2291179
theorem B2036603 : Blo 2035435 2036603 := bstep (se 1 (by rfl) ⟨1527452, by rfl⟩ : syracuseStep 2036603 = 3054905) B3054905
theorem B9786757 : Blo 2035435 9786757 := bbase (se 4 (by rfl) ⟨917508, by rfl⟩ : syracuseStep 9786757 = 1835017) (by norm_num)
theorem B13049009 : Blo 2035435 13049009 := bstep (se 2 (by rfl) ⟨4893378, by rfl⟩ : syracuseStep 13049009 = 9786757) B9786757
theorem B8699339 : Blo 2035435 8699339 := bstep (se 1 (by rfl) ⟨6524504, by rfl⟩ : syracuseStep 8699339 = 13049009) B13049009
theorem B23198237 : Blo 2035435 23198237 := bstep (se 3 (by rfl) ⟨4349669, by rfl⟩ : syracuseStep 23198237 = 8699339) B8699339
theorem B15465491 : Blo 2035435 15465491 := bstep (se 1 (by rfl) ⟨11599118, by rfl⟩ : syracuseStep 15465491 = 23198237) B23198237
theorem B10310327 : Blo 2035435 10310327 := bstep (se 1 (by rfl) ⟨7732745, by rfl⟩ : syracuseStep 10310327 = 15465491) B15465491
theorem B6873551 : Blo 2035435 6873551 := bstep (se 1 (by rfl) ⟨5155163, by rfl⟩ : syracuseStep 6873551 = 10310327) B10310327
theorem B4582367 : Blo 2035435 4582367 := bstep (se 1 (by rfl) ⟨3436775, by rfl⟩ : syracuseStep 4582367 = 6873551) B6873551
theorem B3054911 : Blo 2035435 3054911 := bstep (se 1 (by rfl) ⟨2291183, by rfl⟩ : syracuseStep 3054911 = 4582367) B4582367
theorem B2036607 : Blo 2035435 2036607 := bstep (se 1 (by rfl) ⟨1527455, by rfl⟩ : syracuseStep 2036607 = 3054911) B3054911
theorem B3054917 : Blo 2035435 3054917 := bbase (se 4 (by rfl) ⟨286398, by rfl⟩ : syracuseStep 3054917 = 572797) (by norm_num)
theorem B2036611 : Blo 2035435 2036611 := bstep (se 1 (by rfl) ⟨1527458, by rfl⟩ : syracuseStep 2036611 = 3054917) B3054917
theorem B3436789 : Blo 2035435 3436789 := bbase (se 5 (by rfl) ⟨161099, by rfl⟩ : syracuseStep 3436789 = 322199) (by norm_num)
theorem B4582385 : Blo 2035435 4582385 := bstep (se 2 (by rfl) ⟨1718394, by rfl⟩ : syracuseStep 4582385 = 3436789) B3436789
theorem B3054923 : Blo 2035435 3054923 := bstep (se 1 (by rfl) ⟨2291192, by rfl⟩ : syracuseStep 3054923 = 4582385) B4582385
theorem B2036615 : Blo 2035435 2036615 := bstep (se 1 (by rfl) ⟨1527461, by rfl⟩ : syracuseStep 2036615 = 3054923) B3054923
theorem B2291197 : Blo 2035435 2291197 := bbase (se 3 (by rfl) ⟨429599, by rfl⟩ : syracuseStep 2291197 = 859199) (by norm_num)
theorem B3054929 : Blo 2035435 3054929 := bstep (se 2 (by rfl) ⟨1145598, by rfl⟩ : syracuseStep 3054929 = 2291197) B2291197
theorem B2036619 : Blo 2035435 2036619 := bstep (se 1 (by rfl) ⟨1527464, by rfl⟩ : syracuseStep 2036619 = 3054929) B3054929
theorem B6873605 : Blo 2035435 6873605 := bbase (se 4 (by rfl) ⟨644400, by rfl⟩ : syracuseStep 6873605 = 1288801) (by norm_num)
theorem B4582403 : Blo 2035435 4582403 := bstep (se 1 (by rfl) ⟨3436802, by rfl⟩ : syracuseStep 4582403 = 6873605) B6873605
theorem B3054935 : Blo 2035435 3054935 := bstep (se 1 (by rfl) ⟨2291201, by rfl⟩ : syracuseStep 3054935 = 4582403) B4582403
theorem B2036623 : Blo 2035435 2036623 := bstep (se 1 (by rfl) ⟨1527467, by rfl⟩ : syracuseStep 2036623 = 3054935) B3054935
theorem B3054941 : Blo 2035435 3054941 := bbase (se 3 (by rfl) ⟨572801, by rfl⟩ : syracuseStep 3054941 = 1145603) (by norm_num)
theorem B2036627 : Blo 2035435 2036627 := bstep (se 1 (by rfl) ⟨1527470, by rfl⟩ : syracuseStep 2036627 = 3054941) B3054941
theorem B4582421 : Blo 2035435 4582421 := bbase (se 6 (by rfl) ⟨107400, by rfl⟩ : syracuseStep 4582421 = 214801) (by norm_num)
theorem B3054947 : Blo 2035435 3054947 := bstep (se 1 (by rfl) ⟨2291210, by rfl⟩ : syracuseStep 3054947 = 4582421) B4582421
theorem B2036631 : Blo 2035435 2036631 := bstep (se 1 (by rfl) ⟨1527473, by rfl⟩ : syracuseStep 2036631 = 3054947) B3054947
theorem B7732853 : Blo 2035435 7732853 := bbase (se 5 (by rfl) ⟨362477, by rfl⟩ : syracuseStep 7732853 = 724955) (by norm_num)
theorem B5155235 : Blo 2035435 5155235 := bstep (se 1 (by rfl) ⟨3866426, by rfl⟩ : syracuseStep 5155235 = 7732853) B7732853
theorem B3436823 : Blo 2035435 3436823 := bstep (se 1 (by rfl) ⟨2577617, by rfl⟩ : syracuseStep 3436823 = 5155235) B5155235
theorem B2291215 : Blo 2035435 2291215 := bstep (se 1 (by rfl) ⟨1718411, by rfl⟩ : syracuseStep 2291215 = 3436823) B3436823
theorem B3054953 : Blo 2035435 3054953 := bstep (se 2 (by rfl) ⟨1145607, by rfl⟩ : syracuseStep 3054953 = 2291215) B2291215
theorem B2036635 : Blo 2035435 2036635 := bstep (se 1 (by rfl) ⟨1527476, by rfl⟩ : syracuseStep 2036635 = 3054953) B3054953
theorem B2174869 : Blo 2035435 2174869 := bbase (se 6 (by rfl) ⟨50973, by rfl⟩ : syracuseStep 2174869 = 101947) (by norm_num)
theorem B11599301 : Blo 2035435 11599301 := bstep (se 4 (by rfl) ⟨1087434, by rfl⟩ : syracuseStep 11599301 = 2174869) B2174869
theorem B7732867 : Blo 2035435 7732867 := bstep (se 1 (by rfl) ⟨5799650, by rfl⟩ : syracuseStep 7732867 = 11599301) B11599301
theorem B10310489 : Blo 2035435 10310489 := bstep (se 2 (by rfl) ⟨3866433, by rfl⟩ : syracuseStep 10310489 = 7732867) B7732867
theorem B6873659 : Blo 2035435 6873659 := bstep (se 1 (by rfl) ⟨5155244, by rfl⟩ : syracuseStep 6873659 = 10310489) B10310489
theorem B4582439 : Blo 2035435 4582439 := bstep (se 1 (by rfl) ⟨3436829, by rfl⟩ : syracuseStep 4582439 = 6873659) B6873659
theorem B3054959 : Blo 2035435 3054959 := bstep (se 1 (by rfl) ⟨2291219, by rfl⟩ : syracuseStep 3054959 = 4582439) B4582439
theorem B2036639 : Blo 2035435 2036639 := bstep (se 1 (by rfl) ⟨1527479, by rfl⟩ : syracuseStep 2036639 = 3054959) B3054959
theorem B3054965 : Blo 2035435 3054965 := bbase (se 5 (by rfl) ⟨143201, by rfl⟩ : syracuseStep 3054965 = 286403) (by norm_num)
theorem B2036643 : Blo 2035435 2036643 := bstep (se 1 (by rfl) ⟨1527482, by rfl⟩ : syracuseStep 2036643 = 3054965) B3054965
theorem B2899837 : Blo 2035435 2899837 := bbase (se 3 (by rfl) ⟨543719, by rfl⟩ : syracuseStep 2899837 = 1087439) (by norm_num)
theorem B3866449 : Blo 2035435 3866449 := bstep (se 2 (by rfl) ⟨1449918, by rfl⟩ : syracuseStep 3866449 = 2899837) B2899837
theorem B5155265 : Blo 2035435 5155265 := bstep (se 2 (by rfl) ⟨1933224, by rfl⟩ : syracuseStep 5155265 = 3866449) B3866449
theorem B3436843 : Blo 2035435 3436843 := bstep (se 1 (by rfl) ⟨2577632, by rfl⟩ : syracuseStep 3436843 = 5155265) B5155265
theorem B4582457 : Blo 2035435 4582457 := bstep (se 2 (by rfl) ⟨1718421, by rfl⟩ : syracuseStep 4582457 = 3436843) B3436843
theorem B3054971 : Blo 2035435 3054971 := bstep (se 1 (by rfl) ⟨2291228, by rfl⟩ : syracuseStep 3054971 = 4582457) B4582457
theorem B2036647 : Blo 2035435 2036647 := bstep (se 1 (by rfl) ⟨1527485, by rfl⟩ : syracuseStep 2036647 = 3054971) B3054971
theorem B2291233 : Blo 2035435 2291233 := bbase (se 2 (by rfl) ⟨859212, by rfl⟩ : syracuseStep 2291233 = 1718425) (by norm_num)
theorem B3054977 : Blo 2035435 3054977 := bstep (se 2 (by rfl) ⟨1145616, by rfl⟩ : syracuseStep 3054977 = 2291233) B2291233
theorem B2036651 : Blo 2035435 2036651 := bstep (se 1 (by rfl) ⟨1527488, by rfl⟩ : syracuseStep 2036651 = 3054977) B3054977
theorem B5155285 : Blo 2035435 5155285 := bbase (se 7 (by rfl) ⟨60413, by rfl⟩ : syracuseStep 5155285 = 120827) (by norm_num)
theorem B6873713 : Blo 2035435 6873713 := bstep (se 2 (by rfl) ⟨2577642, by rfl⟩ : syracuseStep 6873713 = 5155285) B5155285
theorem B4582475 : Blo 2035435 4582475 := bstep (se 1 (by rfl) ⟨3436856, by rfl⟩ : syracuseStep 4582475 = 6873713) B6873713
theorem B3054983 : Blo 2035435 3054983 := bstep (se 1 (by rfl) ⟨2291237, by rfl⟩ : syracuseStep 3054983 = 4582475) B4582475
theorem B2036655 : Blo 2035435 2036655 := bstep (se 1 (by rfl) ⟨1527491, by rfl⟩ : syracuseStep 2036655 = 3054983) B3054983
theorem B3054989 : Blo 2035435 3054989 := bbase (se 3 (by rfl) ⟨572810, by rfl⟩ : syracuseStep 3054989 = 1145621) (by norm_num)
theorem B2036659 : Blo 2035435 2036659 := bstep (se 1 (by rfl) ⟨1527494, by rfl⟩ : syracuseStep 2036659 = 3054989) B3054989
theorem B4582493 : Blo 2035435 4582493 := bbase (se 3 (by rfl) ⟨859217, by rfl⟩ : syracuseStep 4582493 = 1718435) (by norm_num)
theorem B3054995 : Blo 2035435 3054995 := bstep (se 1 (by rfl) ⟨2291246, by rfl⟩ : syracuseStep 3054995 = 4582493) B4582493
theorem B2036663 : Blo 2035435 2036663 := bstep (se 1 (by rfl) ⟨1527497, by rfl⟩ : syracuseStep 2036663 = 3054995) B3054995
theorem B3436877 : Blo 2035435 3436877 := bbase (se 3 (by rfl) ⟨644414, by rfl⟩ : syracuseStep 3436877 = 1288829) (by norm_num)
theorem B2291251 : Blo 2035435 2291251 := bstep (se 1 (by rfl) ⟨1718438, by rfl⟩ : syracuseStep 2291251 = 3436877) B3436877
theorem B3055001 : Blo 2035435 3055001 := bstep (se 2 (by rfl) ⟨1145625, by rfl⟩ : syracuseStep 3055001 = 2291251) B2291251
theorem B2036667 : Blo 2035435 2036667 := bstep (se 1 (by rfl) ⟨1527500, by rfl⟩ : syracuseStep 2036667 = 3055001) B3055001
theorem B14680597 : Blo 2035435 14680597 := bbase (se 6 (by rfl) ⟨344076, by rfl⟩ : syracuseStep 14680597 = 688153) (by norm_num)
theorem B19574129 : Blo 2035435 19574129 := bstep (se 2 (by rfl) ⟨7340298, by rfl⟩ : syracuseStep 19574129 = 14680597) B14680597
theorem B13049419 : Blo 2035435 13049419 := bstep (se 1 (by rfl) ⟨9787064, by rfl⟩ : syracuseStep 13049419 = 19574129) B19574129
theorem B17399225 : Blo 2035435 17399225 := bstep (se 2 (by rfl) ⟨6524709, by rfl⟩ : syracuseStep 17399225 = 13049419) B13049419
theorem B11599483 : Blo 2035435 11599483 := bstep (se 1 (by rfl) ⟨8699612, by rfl⟩ : syracuseStep 11599483 = 17399225) B17399225
theorem B15465977 : Blo 2035435 15465977 := bstep (se 2 (by rfl) ⟨5799741, by rfl⟩ : syracuseStep 15465977 = 11599483) B11599483
theorem B10310651 : Blo 2035435 10310651 := bstep (se 1 (by rfl) ⟨7732988, by rfl⟩ : syracuseStep 10310651 = 15465977) B15465977
theorem B6873767 : Blo 2035435 6873767 := bstep (se 1 (by rfl) ⟨5155325, by rfl⟩ : syracuseStep 6873767 = 10310651) B10310651
theorem B4582511 : Blo 2035435 4582511 := bstep (se 1 (by rfl) ⟨3436883, by rfl⟩ : syracuseStep 4582511 = 6873767) B6873767
theorem B3055007 : Blo 2035435 3055007 := bstep (se 1 (by rfl) ⟨2291255, by rfl⟩ : syracuseStep 3055007 = 4582511) B4582511
theorem B2036671 : Blo 2035435 2036671 := bstep (se 1 (by rfl) ⟨1527503, by rfl⟩ : syracuseStep 2036671 = 3055007) B3055007
theorem B3055013 : Blo 2035435 3055013 := bbase (se 4 (by rfl) ⟨286407, by rfl⟩ : syracuseStep 3055013 = 572815) (by norm_num)
theorem B2036675 : Blo 2035435 2036675 := bstep (se 1 (by rfl) ⟨1527506, by rfl⟩ : syracuseStep 2036675 = 3055013) B3055013
theorem B2577673 : Blo 2035435 2577673 := bbase (se 2 (by rfl) ⟨966627, by rfl⟩ : syracuseStep 2577673 = 1933255) (by norm_num)
theorem B3436897 : Blo 2035435 3436897 := bstep (se 2 (by rfl) ⟨1288836, by rfl⟩ : syracuseStep 3436897 = 2577673) B2577673
theorem B4582529 : Blo 2035435 4582529 := bstep (se 2 (by rfl) ⟨1718448, by rfl⟩ : syracuseStep 4582529 = 3436897) B3436897
theorem B3055019 : Blo 2035435 3055019 := bstep (se 1 (by rfl) ⟨2291264, by rfl⟩ : syracuseStep 3055019 = 4582529) B4582529
theorem B2036679 : Blo 2035435 2036679 := bstep (se 1 (by rfl) ⟨1527509, by rfl⟩ : syracuseStep 2036679 = 3055019) B3055019
theorem B2291269 : Blo 2035435 2291269 := bbase (se 4 (by rfl) ⟨214806, by rfl⟩ : syracuseStep 2291269 = 429613) (by norm_num)
theorem B3055025 : Blo 2035435 3055025 := bstep (se 2 (by rfl) ⟨1145634, by rfl⟩ : syracuseStep 3055025 = 2291269) B2291269
theorem B2036683 : Blo 2035435 2036683 := bstep (se 1 (by rfl) ⟨1527512, by rfl⟩ : syracuseStep 2036683 = 3055025) B3055025
theorem B3866525 : Blo 2035435 3866525 := bbase (se 3 (by rfl) ⟨724973, by rfl⟩ : syracuseStep 3866525 = 1449947) (by norm_num)
theorem B2577683 : Blo 2035435 2577683 := bstep (se 1 (by rfl) ⟨1933262, by rfl⟩ : syracuseStep 2577683 = 3866525) B3866525
theorem B6873821 : Blo 2035435 6873821 := bstep (se 3 (by rfl) ⟨1288841, by rfl⟩ : syracuseStep 6873821 = 2577683) B2577683
theorem B4582547 : Blo 2035435 4582547 := bstep (se 1 (by rfl) ⟨3436910, by rfl⟩ : syracuseStep 4582547 = 6873821) B6873821
theorem B3055031 : Blo 2035435 3055031 := bstep (se 1 (by rfl) ⟨2291273, by rfl⟩ : syracuseStep 3055031 = 4582547) B4582547
theorem B2036687 : Blo 2035435 2036687 := bstep (se 1 (by rfl) ⟨1527515, by rfl⟩ : syracuseStep 2036687 = 3055031) B3055031
theorem B3055037 : Blo 2035435 3055037 := bbase (se 3 (by rfl) ⟨572819, by rfl⟩ : syracuseStep 3055037 = 1145639) (by norm_num)
theorem B2036691 : Blo 2035435 2036691 := bstep (se 1 (by rfl) ⟨1527518, by rfl⟩ : syracuseStep 2036691 = 3055037) B3055037
theorem B4582565 : Blo 2035435 4582565 := bbase (se 4 (by rfl) ⟨429615, by rfl⟩ : syracuseStep 4582565 = 859231) (by norm_num)
theorem B3055043 : Blo 2035435 3055043 := bstep (se 1 (by rfl) ⟨2291282, by rfl⟩ : syracuseStep 3055043 = 4582565) B4582565
theorem B2036695 : Blo 2035435 2036695 := bstep (se 1 (by rfl) ⟨1527521, by rfl⟩ : syracuseStep 2036695 = 3055043) B3055043
theorem B5155397 : Blo 2035435 5155397 := bbase (se 4 (by rfl) ⟨483318, by rfl⟩ : syracuseStep 5155397 = 966637) (by norm_num)
theorem B3436931 : Blo 2035435 3436931 := bstep (se 1 (by rfl) ⟨2577698, by rfl⟩ : syracuseStep 3436931 = 5155397) B5155397
theorem B2291287 : Blo 2035435 2291287 := bstep (se 1 (by rfl) ⟨1718465, by rfl⟩ : syracuseStep 2291287 = 3436931) B3436931
theorem B3055049 : Blo 2035435 3055049 := bstep (se 2 (by rfl) ⟨1145643, by rfl⟩ : syracuseStep 3055049 = 2291287) B2291287
theorem B2036699 : Blo 2035435 2036699 := bstep (se 1 (by rfl) ⟨1527524, by rfl⟩ : syracuseStep 2036699 = 3055049) B3055049
theorem B2446805 : Blo 2035435 2446805 := bbase (se 7 (by rfl) ⟨28673, by rfl⟩ : syracuseStep 2446805 = 57347) (by norm_num)
theorem B6524813 : Blo 2035435 6524813 := bstep (se 3 (by rfl) ⟨1223402, by rfl⟩ : syracuseStep 6524813 = 2446805) B2446805
theorem B4349875 : Blo 2035435 4349875 := bstep (se 1 (by rfl) ⟨3262406, by rfl⟩ : syracuseStep 4349875 = 6524813) B6524813
theorem B5799833 : Blo 2035435 5799833 := bstep (se 2 (by rfl) ⟨2174937, by rfl⟩ : syracuseStep 5799833 = 4349875) B4349875
theorem B3866555 : Blo 2035435 3866555 := bstep (se 1 (by rfl) ⟨2899916, by rfl⟩ : syracuseStep 3866555 = 5799833) B5799833
theorem B10310813 : Blo 2035435 10310813 := bstep (se 3 (by rfl) ⟨1933277, by rfl⟩ : syracuseStep 10310813 = 3866555) B3866555
theorem B6873875 : Blo 2035435 6873875 := bstep (se 1 (by rfl) ⟨5155406, by rfl⟩ : syracuseStep 6873875 = 10310813) B10310813
theorem B4582583 : Blo 2035435 4582583 := bstep (se 1 (by rfl) ⟨3436937, by rfl⟩ : syracuseStep 4582583 = 6873875) B6873875
theorem B3055055 : Blo 2035435 3055055 := bstep (se 1 (by rfl) ⟨2291291, by rfl⟩ : syracuseStep 3055055 = 4582583) B4582583
theorem B2036703 : Blo 2035435 2036703 := bstep (se 1 (by rfl) ⟨1527527, by rfl⟩ : syracuseStep 2036703 = 3055055) B3055055
theorem B3055061 : Blo 2035435 3055061 := bbase (se 7 (by rfl) ⟨35801, by rfl⟩ : syracuseStep 3055061 = 71603) (by norm_num)
theorem B2036707 : Blo 2035435 2036707 := bstep (se 1 (by rfl) ⟨1527530, by rfl⟩ : syracuseStep 2036707 = 3055061) B3055061
theorem B7733141 : Blo 2035435 7733141 := bbase (se 6 (by rfl) ⟨181245, by rfl⟩ : syracuseStep 7733141 = 362491) (by norm_num)
theorem B5155427 : Blo 2035435 5155427 := bstep (se 1 (by rfl) ⟨3866570, by rfl⟩ : syracuseStep 5155427 = 7733141) B7733141
theorem B3436951 : Blo 2035435 3436951 := bstep (se 1 (by rfl) ⟨2577713, by rfl⟩ : syracuseStep 3436951 = 5155427) B5155427
theorem B4582601 : Blo 2035435 4582601 := bstep (se 2 (by rfl) ⟨1718475, by rfl⟩ : syracuseStep 4582601 = 3436951) B3436951
theorem B3055067 : Blo 2035435 3055067 := bstep (se 1 (by rfl) ⟨2291300, by rfl⟩ : syracuseStep 3055067 = 4582601) B4582601
theorem B2036711 : Blo 2035435 2036711 := bstep (se 1 (by rfl) ⟨1527533, by rfl⟩ : syracuseStep 2036711 = 3055067) B3055067
theorem B2291305 : Blo 2035435 2291305 := bbase (se 2 (by rfl) ⟨859239, by rfl⟩ : syracuseStep 2291305 = 1718479) (by norm_num)
theorem B3055073 : Blo 2035435 3055073 := bstep (se 2 (by rfl) ⟨1145652, by rfl⟩ : syracuseStep 3055073 = 2291305) B2291305
theorem B2036715 : Blo 2035435 2036715 := bstep (se 1 (by rfl) ⟨1527536, by rfl⟩ : syracuseStep 2036715 = 3055073) B3055073
theorem B4349909 : Blo 2035435 4349909 := bbase (se 7 (by rfl) ⟨50975, by rfl⟩ : syracuseStep 4349909 = 101951) (by norm_num)
theorem B11599757 : Blo 2035435 11599757 := bstep (se 3 (by rfl) ⟨2174954, by rfl⟩ : syracuseStep 11599757 = 4349909) B4349909
theorem B7733171 : Blo 2035435 7733171 := bstep (se 1 (by rfl) ⟨5799878, by rfl⟩ : syracuseStep 7733171 = 11599757) B11599757
theorem B5155447 : Blo 2035435 5155447 := bstep (se 1 (by rfl) ⟨3866585, by rfl⟩ : syracuseStep 5155447 = 7733171) B7733171
theorem B6873929 : Blo 2035435 6873929 := bstep (se 2 (by rfl) ⟨2577723, by rfl⟩ : syracuseStep 6873929 = 5155447) B5155447
theorem B4582619 : Blo 2035435 4582619 := bstep (se 1 (by rfl) ⟨3436964, by rfl⟩ : syracuseStep 4582619 = 6873929) B6873929
theorem B3055079 : Blo 2035435 3055079 := bstep (se 1 (by rfl) ⟨2291309, by rfl⟩ : syracuseStep 3055079 = 4582619) B4582619
theorem B2036719 : Blo 2035435 2036719 := bstep (se 1 (by rfl) ⟨1527539, by rfl⟩ : syracuseStep 2036719 = 3055079) B3055079
theorem B3055085 : Blo 2035435 3055085 := bbase (se 3 (by rfl) ⟨572828, by rfl⟩ : syracuseStep 3055085 = 1145657) (by norm_num)
theorem B2036723 : Blo 2035435 2036723 := bstep (se 1 (by rfl) ⟨1527542, by rfl⟩ : syracuseStep 2036723 = 3055085) B3055085
theorem B4582637 : Blo 2035435 4582637 := bbase (se 3 (by rfl) ⟨859244, by rfl⟩ : syracuseStep 4582637 = 1718489) (by norm_num)
theorem B3055091 : Blo 2035435 3055091 := bstep (se 1 (by rfl) ⟨2291318, by rfl⟩ : syracuseStep 3055091 = 4582637) B4582637
theorem B2036727 : Blo 2035435 2036727 := bstep (se 1 (by rfl) ⟨1527545, by rfl⟩ : syracuseStep 2036727 = 3055091) B3055091
theorem B2899957 : Blo 2035435 2899957 := bbase (se 5 (by rfl) ⟨135935, by rfl⟩ : syracuseStep 2899957 = 271871) (by norm_num)
theorem B3866609 : Blo 2035435 3866609 := bstep (se 2 (by rfl) ⟨1449978, by rfl⟩ : syracuseStep 3866609 = 2899957) B2899957
theorem B2577739 : Blo 2035435 2577739 := bstep (se 1 (by rfl) ⟨1933304, by rfl⟩ : syracuseStep 2577739 = 3866609) B3866609
theorem B3436985 : Blo 2035435 3436985 := bstep (se 2 (by rfl) ⟨1288869, by rfl⟩ : syracuseStep 3436985 = 2577739) B2577739
theorem B2291323 : Blo 2035435 2291323 := bstep (se 1 (by rfl) ⟨1718492, by rfl⟩ : syracuseStep 2291323 = 3436985) B3436985
theorem B3055097 : Blo 2035435 3055097 := bstep (se 2 (by rfl) ⟨1145661, by rfl⟩ : syracuseStep 3055097 = 2291323) B2291323
theorem B2036731 : Blo 2035435 2036731 := bstep (se 1 (by rfl) ⟨1527548, by rfl⟩ : syracuseStep 2036731 = 3055097) B3055097
theorem B5297125 : Blo 2035435 5297125 := bbase (se 4 (by rfl) ⟨496605, by rfl⟩ : syracuseStep 5297125 = 993211) (by norm_num)
theorem B7062833 : Blo 2035435 7062833 := bstep (se 2 (by rfl) ⟨2648562, by rfl⟩ : syracuseStep 7062833 = 5297125) B5297125
theorem B18834221 : Blo 2035435 18834221 := bstep (se 3 (by rfl) ⟨3531416, by rfl⟩ : syracuseStep 18834221 = 7062833) B7062833
theorem B12556147 : Blo 2035435 12556147 := bstep (se 1 (by rfl) ⟨9417110, by rfl⟩ : syracuseStep 12556147 = 18834221) B18834221
theorem B16741529 : Blo 2035435 16741529 := bstep (se 2 (by rfl) ⟨6278073, by rfl⟩ : syracuseStep 16741529 = 12556147) B12556147
theorem B11161019 : Blo 2035435 11161019 := bstep (se 1 (by rfl) ⟨8370764, by rfl⟩ : syracuseStep 11161019 = 16741529) B16741529
theorem B7440679 : Blo 2035435 7440679 := bstep (se 1 (by rfl) ⟨5580509, by rfl⟩ : syracuseStep 7440679 = 11161019) B11161019
theorem B39683621 : Blo 2035435 39683621 := bstep (se 4 (by rfl) ⟨3720339, by rfl⟩ : syracuseStep 39683621 = 7440679) B7440679
theorem B26455747 : Blo 2035435 26455747 := bstep (se 1 (by rfl) ⟨19841810, by rfl⟩ : syracuseStep 26455747 = 39683621) B39683621
theorem B35274329 : Blo 2035435 35274329 := bstep (se 2 (by rfl) ⟨13227873, by rfl⟩ : syracuseStep 35274329 = 26455747) B26455747
theorem B23516219 : Blo 2035435 23516219 := bstep (se 1 (by rfl) ⟨17637164, by rfl⟩ : syracuseStep 23516219 = 35274329) B35274329
theorem B15677479 : Blo 2035435 15677479 := bstep (se 1 (by rfl) ⟨11758109, by rfl⟩ : syracuseStep 15677479 = 23516219) B23516219
theorem B20903305 : Blo 2035435 20903305 := bstep (se 2 (by rfl) ⟨7838739, by rfl⟩ : syracuseStep 20903305 = 15677479) B15677479
theorem B27871073 : Blo 2035435 27871073 := bstep (se 2 (by rfl) ⟨10451652, by rfl⟩ : syracuseStep 27871073 = 20903305) B20903305
theorem B18580715 : Blo 2035435 18580715 := bstep (se 1 (by rfl) ⟨13935536, by rfl⟩ : syracuseStep 18580715 = 27871073) B27871073
theorem B12387143 : Blo 2035435 12387143 := bstep (se 1 (by rfl) ⟨9290357, by rfl⟩ : syracuseStep 12387143 = 18580715) B18580715
theorem B8258095 : Blo 2035435 8258095 := bstep (se 1 (by rfl) ⟨6193571, by rfl⟩ : syracuseStep 8258095 = 12387143) B12387143
theorem B44043173 : Blo 2035435 44043173 := bstep (se 4 (by rfl) ⟨4129047, by rfl⟩ : syracuseStep 44043173 = 8258095) B8258095
theorem B29362115 : Blo 2035435 29362115 := bstep (se 1 (by rfl) ⟨22021586, by rfl⟩ : syracuseStep 29362115 = 44043173) B44043173
theorem B78298973 : Blo 2035435 78298973 := bstep (se 3 (by rfl) ⟨14681057, by rfl⟩ : syracuseStep 78298973 = 29362115) B29362115
theorem B52199315 : Blo 2035435 52199315 := bstep (se 1 (by rfl) ⟨39149486, by rfl⟩ : syracuseStep 52199315 = 78298973) B78298973
theorem B34799543 : Blo 2035435 34799543 := bstep (se 1 (by rfl) ⟨26099657, by rfl⟩ : syracuseStep 34799543 = 52199315) B52199315
theorem B23199695 : Blo 2035435 23199695 := bstep (se 1 (by rfl) ⟨17399771, by rfl⟩ : syracuseStep 23199695 = 34799543) B34799543
theorem B15466463 : Blo 2035435 15466463 := bstep (se 1 (by rfl) ⟨11599847, by rfl⟩ : syracuseStep 15466463 = 23199695) B23199695
theorem B10310975 : Blo 2035435 10310975 := bstep (se 1 (by rfl) ⟨7733231, by rfl⟩ : syracuseStep 10310975 = 15466463) B15466463
theorem B6873983 : Blo 2035435 6873983 := bstep (se 1 (by rfl) ⟨5155487, by rfl⟩ : syracuseStep 6873983 = 10310975) B10310975
theorem B4582655 : Blo 2035435 4582655 := bstep (se 1 (by rfl) ⟨3436991, by rfl⟩ : syracuseStep 4582655 = 6873983) B6873983
theorem B3055103 : Blo 2035435 3055103 := bstep (se 1 (by rfl) ⟨2291327, by rfl⟩ : syracuseStep 3055103 = 4582655) B4582655
theorem B2036735 : Blo 2035435 2036735 := bstep (se 1 (by rfl) ⟨1527551, by rfl⟩ : syracuseStep 2036735 = 3055103) B3055103
theorem B3055109 : Blo 2035435 3055109 := bbase (se 4 (by rfl) ⟨286416, by rfl⟩ : syracuseStep 3055109 = 572833) (by norm_num)
theorem B2036739 : Blo 2035435 2036739 := bstep (se 1 (by rfl) ⟨1527554, by rfl⟩ : syracuseStep 2036739 = 3055109) B3055109
theorem B3437005 : Blo 2035435 3437005 := bbase (se 3 (by rfl) ⟨644438, by rfl⟩ : syracuseStep 3437005 = 1288877) (by norm_num)
theorem B4582673 : Blo 2035435 4582673 := bstep (se 2 (by rfl) ⟨1718502, by rfl⟩ : syracuseStep 4582673 = 3437005) B3437005
theorem B3055115 : Blo 2035435 3055115 := bstep (se 1 (by rfl) ⟨2291336, by rfl⟩ : syracuseStep 3055115 = 4582673) B4582673
theorem B2036743 : Blo 2035435 2036743 := bstep (se 1 (by rfl) ⟨1527557, by rfl⟩ : syracuseStep 2036743 = 3055115) B3055115
theorem B2291341 : Blo 2035435 2291341 := bbase (se 3 (by rfl) ⟨429626, by rfl⟩ : syracuseStep 2291341 = 859253) (by norm_num)
theorem B3055121 : Blo 2035435 3055121 := bstep (se 2 (by rfl) ⟨1145670, by rfl⟩ : syracuseStep 3055121 = 2291341) B2291341
theorem B2036747 : Blo 2035435 2036747 := bstep (se 1 (by rfl) ⟨1527560, by rfl⟩ : syracuseStep 2036747 = 3055121) B3055121
theorem B6874037 : Blo 2035435 6874037 := bbase (se 5 (by rfl) ⟨322220, by rfl⟩ : syracuseStep 6874037 = 644441) (by norm_num)
theorem B4582691 : Blo 2035435 4582691 := bstep (se 1 (by rfl) ⟨3437018, by rfl⟩ : syracuseStep 4582691 = 6874037) B6874037
theorem B3055127 : Blo 2035435 3055127 := bstep (se 1 (by rfl) ⟨2291345, by rfl⟩ : syracuseStep 3055127 = 4582691) B4582691
theorem B2036751 : Blo 2035435 2036751 := bstep (se 1 (by rfl) ⟨1527563, by rfl⟩ : syracuseStep 2036751 = 3055127) B3055127
theorem B3055133 : Blo 2035435 3055133 := bbase (se 3 (by rfl) ⟨572837, by rfl⟩ : syracuseStep 3055133 = 1145675) (by norm_num)
theorem B2036755 : Blo 2035435 2036755 := bstep (se 1 (by rfl) ⟨1527566, by rfl⟩ : syracuseStep 2036755 = 3055133) B3055133
theorem B4582709 : Blo 2035435 4582709 := bbase (se 5 (by rfl) ⟨214814, by rfl⟩ : syracuseStep 4582709 = 429629) (by norm_num)
theorem B3055139 : Blo 2035435 3055139 := bstep (se 1 (by rfl) ⟨2291354, by rfl⟩ : syracuseStep 3055139 = 4582709) B4582709
theorem B2036759 : Blo 2035435 2036759 := bstep (se 1 (by rfl) ⟨1527569, by rfl⟩ : syracuseStep 2036759 = 3055139) B3055139
theorem B2092721 : Blo 2035435 2092721 := bbase (se 2 (by rfl) ⟨784770, by rfl⟩ : syracuseStep 2092721 = 1569541) (by norm_num)
theorem B5580589 : Blo 2035435 5580589 := bstep (se 3 (by rfl) ⟨1046360, by rfl⟩ : syracuseStep 5580589 = 2092721) B2092721
theorem B7440785 : Blo 2035435 7440785 := bstep (se 2 (by rfl) ⟨2790294, by rfl⟩ : syracuseStep 7440785 = 5580589) B5580589
theorem B4960523 : Blo 2035435 4960523 := bstep (se 1 (by rfl) ⟨3720392, by rfl⟩ : syracuseStep 4960523 = 7440785) B7440785
theorem B3307015 : Blo 2035435 3307015 := bstep (se 1 (by rfl) ⟨2480261, by rfl⟩ : syracuseStep 3307015 = 4960523) B4960523
theorem B4409353 : Blo 2035435 4409353 := bstep (se 2 (by rfl) ⟨1653507, by rfl⟩ : syracuseStep 4409353 = 3307015) B3307015
theorem B5879137 : Blo 2035435 5879137 := bstep (se 2 (by rfl) ⟨2204676, by rfl⟩ : syracuseStep 5879137 = 4409353) B4409353
theorem B7838849 : Blo 2035435 7838849 := bstep (se 2 (by rfl) ⟨2939568, by rfl⟩ : syracuseStep 7838849 = 5879137) B5879137
theorem B20903597 : Blo 2035435 20903597 := bstep (se 3 (by rfl) ⟨3919424, by rfl⟩ : syracuseStep 20903597 = 7838849) B7838849
theorem B13935731 : Blo 2035435 13935731 := bstep (se 1 (by rfl) ⟨10451798, by rfl⟩ : syracuseStep 13935731 = 20903597) B20903597
theorem B37161949 : Blo 2035435 37161949 := bstep (se 3 (by rfl) ⟨6967865, by rfl⟩ : syracuseStep 37161949 = 13935731) B13935731
theorem B49549265 : Blo 2035435 49549265 := bstep (se 2 (by rfl) ⟨18580974, by rfl⟩ : syracuseStep 49549265 = 37161949) B37161949
theorem B33032843 : Blo 2035435 33032843 := bstep (se 1 (by rfl) ⟨24774632, by rfl⟩ : syracuseStep 33032843 = 49549265) B49549265
theorem B22021895 : Blo 2035435 22021895 := bstep (se 1 (by rfl) ⟨16516421, by rfl⟩ : syracuseStep 22021895 = 33032843) B33032843
theorem B14681263 : Blo 2035435 14681263 := bstep (se 1 (by rfl) ⟨11010947, by rfl⟩ : syracuseStep 14681263 = 22021895) B22021895
theorem B19575017 : Blo 2035435 19575017 := bstep (se 2 (by rfl) ⟨7340631, by rfl⟩ : syracuseStep 19575017 = 14681263) B14681263
theorem B13050011 : Blo 2035435 13050011 := bstep (se 1 (by rfl) ⟨9787508, by rfl⟩ : syracuseStep 13050011 = 19575017) B19575017
theorem B8700007 : Blo 2035435 8700007 := bstep (se 1 (by rfl) ⟨6525005, by rfl⟩ : syracuseStep 8700007 = 13050011) B13050011
theorem B11600009 : Blo 2035435 11600009 := bstep (se 2 (by rfl) ⟨4350003, by rfl⟩ : syracuseStep 11600009 = 8700007) B8700007
theorem B7733339 : Blo 2035435 7733339 := bstep (se 1 (by rfl) ⟨5800004, by rfl⟩ : syracuseStep 7733339 = 11600009) B11600009
theorem B5155559 : Blo 2035435 5155559 := bstep (se 1 (by rfl) ⟨3866669, by rfl⟩ : syracuseStep 5155559 = 7733339) B7733339
theorem B3437039 : Blo 2035435 3437039 := bstep (se 1 (by rfl) ⟨2577779, by rfl⟩ : syracuseStep 3437039 = 5155559) B5155559
theorem B2291359 : Blo 2035435 2291359 := bstep (se 1 (by rfl) ⟨1718519, by rfl⟩ : syracuseStep 2291359 = 3437039) B3437039
theorem B3055145 : Blo 2035435 3055145 := bstep (se 2 (by rfl) ⟨1145679, by rfl⟩ : syracuseStep 3055145 = 2291359) B2291359
theorem B2036763 : Blo 2035435 2036763 := bstep (se 1 (by rfl) ⟨1527572, by rfl⟩ : syracuseStep 2036763 = 3055145) B3055145
theorem B7340645 : Blo 2035435 7340645 := bbase (se 4 (by rfl) ⟨688185, by rfl⟩ : syracuseStep 7340645 = 1376371) (by norm_num)
theorem B19575053 : Blo 2035435 19575053 := bstep (se 3 (by rfl) ⟨3670322, by rfl⟩ : syracuseStep 19575053 = 7340645) B7340645
theorem B13050035 : Blo 2035435 13050035 := bstep (se 1 (by rfl) ⟨9787526, by rfl⟩ : syracuseStep 13050035 = 19575053) B19575053
theorem B8700023 : Blo 2035435 8700023 := bstep (se 1 (by rfl) ⟨6525017, by rfl⟩ : syracuseStep 8700023 = 13050035) B13050035
theorem B5800015 : Blo 2035435 5800015 := bstep (se 1 (by rfl) ⟨4350011, by rfl⟩ : syracuseStep 5800015 = 8700023) B8700023
theorem B7733353 : Blo 2035435 7733353 := bstep (se 2 (by rfl) ⟨2900007, by rfl⟩ : syracuseStep 7733353 = 5800015) B5800015
theorem B10311137 : Blo 2035435 10311137 := bstep (se 2 (by rfl) ⟨3866676, by rfl⟩ : syracuseStep 10311137 = 7733353) B7733353
theorem B6874091 : Blo 2035435 6874091 := bstep (se 1 (by rfl) ⟨5155568, by rfl⟩ : syracuseStep 6874091 = 10311137) B10311137
theorem B4582727 : Blo 2035435 4582727 := bstep (se 1 (by rfl) ⟨3437045, by rfl⟩ : syracuseStep 4582727 = 6874091) B6874091
theorem B3055151 : Blo 2035435 3055151 := bstep (se 1 (by rfl) ⟨2291363, by rfl⟩ : syracuseStep 3055151 = 4582727) B4582727
theorem B2036767 : Blo 2035435 2036767 := bstep (se 1 (by rfl) ⟨1527575, by rfl⟩ : syracuseStep 2036767 = 3055151) B3055151
theorem B3055157 : Blo 2035435 3055157 := bbase (se 5 (by rfl) ⟨143210, by rfl⟩ : syracuseStep 3055157 = 286421) (by norm_num)
theorem B2036771 : Blo 2035435 2036771 := bstep (se 1 (by rfl) ⟨1527578, by rfl⟩ : syracuseStep 2036771 = 3055157) B3055157
theorem B5155589 : Blo 2035435 5155589 := bbase (se 4 (by rfl) ⟨483336, by rfl⟩ : syracuseStep 5155589 = 966673) (by norm_num)
theorem B3437059 : Blo 2035435 3437059 := bstep (se 1 (by rfl) ⟨2577794, by rfl⟩ : syracuseStep 3437059 = 5155589) B5155589
theorem B4582745 : Blo 2035435 4582745 := bstep (se 2 (by rfl) ⟨1718529, by rfl⟩ : syracuseStep 4582745 = 3437059) B3437059
theorem B3055163 : Blo 2035435 3055163 := bstep (se 1 (by rfl) ⟨2291372, by rfl⟩ : syracuseStep 3055163 = 4582745) B4582745
theorem B2036775 : Blo 2035435 2036775 := bstep (se 1 (by rfl) ⟨1527581, by rfl⟩ : syracuseStep 2036775 = 3055163) B3055163
theorem B2291377 : Blo 2035435 2291377 := bbase (se 2 (by rfl) ⟨859266, by rfl⟩ : syracuseStep 2291377 = 1718533) (by norm_num)
theorem B3055169 : Blo 2035435 3055169 := bstep (se 2 (by rfl) ⟨1145688, by rfl⟩ : syracuseStep 3055169 = 2291377) B2291377
theorem B2036779 : Blo 2035435 2036779 := bstep (se 1 (by rfl) ⟨1527584, by rfl⟩ : syracuseStep 2036779 = 3055169) B3055169
theorem B2654165 : Blo 2035435 2654165 := bbase (se 7 (by rfl) ⟨31103, by rfl⟩ : syracuseStep 2654165 = 62207) (by norm_num)
theorem B7077773 : Blo 2035435 7077773 := bstep (se 3 (by rfl) ⟨1327082, by rfl⟩ : syracuseStep 7077773 = 2654165) B2654165
theorem B4718515 : Blo 2035435 4718515 := bstep (se 1 (by rfl) ⟨3538886, by rfl⟩ : syracuseStep 4718515 = 7077773) B7077773
theorem B6291353 : Blo 2035435 6291353 := bstep (se 2 (by rfl) ⟨2359257, by rfl⟩ : syracuseStep 6291353 = 4718515) B4718515
theorem B1073724245 : Blo 2035435 1073724245 := bstep (se 9 (by rfl) ⟨3145676, by rfl⟩ : syracuseStep 1073724245 = 6291353) B6291353
theorem B715816163 : Blo 2035435 715816163 := bstep (se 1 (by rfl) ⟨536862122, by rfl⟩ : syracuseStep 715816163 = 1073724245) B1073724245
theorem B477210775 : Blo 2035435 477210775 := bstep (se 1 (by rfl) ⟨357908081, by rfl⟩ : syracuseStep 477210775 = 715816163) B715816163
theorem B636281033 : Blo 2035435 636281033 := bstep (se 2 (by rfl) ⟨238605387, by rfl⟩ : syracuseStep 636281033 = 477210775) B477210775
theorem B6786997685 : Blo 2035435 6786997685 := bstep (se 5 (by rfl) ⟨318140516, by rfl⟩ : syracuseStep 6786997685 = 636281033) B636281033
theorem B4524665123 : Blo 2035435 4524665123 := bstep (se 1 (by rfl) ⟨3393498842, by rfl⟩ : syracuseStep 4524665123 = 6786997685) B6786997685
theorem B3016443415 : Blo 2035435 3016443415 := bstep (se 1 (by rfl) ⟨2262332561, by rfl⟩ : syracuseStep 3016443415 = 4524665123) B4524665123
theorem B4021924553 : Blo 2035435 4021924553 := bstep (se 2 (by rfl) ⟨1508221707, by rfl⟩ : syracuseStep 4021924553 = 3016443415) B3016443415
theorem B2681283035 : Blo 2035435 2681283035 := bstep (se 1 (by rfl) ⟨2010962276, by rfl⟩ : syracuseStep 2681283035 = 4021924553) B4021924553
theorem B1787522023 : Blo 2035435 1787522023 := bstep (se 1 (by rfl) ⟨1340641517, by rfl⟩ : syracuseStep 1787522023 = 2681283035) B2681283035
theorem B9533450789 : Blo 2035435 9533450789 := bstep (se 4 (by rfl) ⟨893761011, by rfl⟩ : syracuseStep 9533450789 = 1787522023) B1787522023
theorem B6355633859 : Blo 2035435 6355633859 := bstep (se 1 (by rfl) ⟨4766725394, by rfl⟩ : syracuseStep 6355633859 = 9533450789) B9533450789
theorem B4237089239 : Blo 2035435 4237089239 := bstep (se 1 (by rfl) ⟨3177816929, by rfl⟩ : syracuseStep 4237089239 = 6355633859) B6355633859
theorem B2824726159 : Blo 2035435 2824726159 := bstep (se 1 (by rfl) ⟨2118544619, by rfl⟩ : syracuseStep 2824726159 = 4237089239) B4237089239
theorem B3766301545 : Blo 2035435 3766301545 := bstep (se 2 (by rfl) ⟨1412363079, by rfl⟩ : syracuseStep 3766301545 = 2824726159) B2824726159
theorem B5021735393 : Blo 2035435 5021735393 := bstep (se 2 (by rfl) ⟨1883150772, by rfl⟩ : syracuseStep 5021735393 = 3766301545) B3766301545
theorem B3347823595 : Blo 2035435 3347823595 := bstep (se 1 (by rfl) ⟨2510867696, by rfl⟩ : syracuseStep 3347823595 = 5021735393) B5021735393
theorem B4463764793 : Blo 2035435 4463764793 := bstep (se 2 (by rfl) ⟨1673911797, by rfl⟩ : syracuseStep 4463764793 = 3347823595) B3347823595
theorem B2975843195 : Blo 2035435 2975843195 := bstep (se 1 (by rfl) ⟨2231882396, by rfl⟩ : syracuseStep 2975843195 = 4463764793) B4463764793
theorem B1983895463 : Blo 2035435 1983895463 := bstep (se 1 (by rfl) ⟨1487921597, by rfl⟩ : syracuseStep 1983895463 = 2975843195) B2975843195
theorem B5290387901 : Blo 2035435 5290387901 := bstep (se 3 (by rfl) ⟨991947731, by rfl⟩ : syracuseStep 5290387901 = 1983895463) B1983895463
theorem B3526925267 : Blo 2035435 3526925267 := bstep (se 1 (by rfl) ⟨2645193950, by rfl⟩ : syracuseStep 3526925267 = 5290387901) B5290387901
theorem B2351283511 : Blo 2035435 2351283511 := bstep (se 1 (by rfl) ⟨1763462633, by rfl⟩ : syracuseStep 2351283511 = 3526925267) B3526925267
theorem B3135044681 : Blo 2035435 3135044681 := bstep (se 2 (by rfl) ⟨1175641755, by rfl⟩ : syracuseStep 3135044681 = 2351283511) B2351283511
theorem B2090029787 : Blo 2035435 2090029787 := bstep (se 1 (by rfl) ⟨1567522340, by rfl⟩ : syracuseStep 2090029787 = 3135044681) B3135044681
theorem B1393353191 : Blo 2035435 1393353191 := bstep (se 1 (by rfl) ⟨1045014893, by rfl⟩ : syracuseStep 1393353191 = 2090029787) B2090029787
theorem B928902127 : Blo 2035435 928902127 := bstep (se 1 (by rfl) ⟨696676595, by rfl⟩ : syracuseStep 928902127 = 1393353191) B1393353191
theorem B1238536169 : Blo 2035435 1238536169 := bstep (se 2 (by rfl) ⟨464451063, by rfl⟩ : syracuseStep 1238536169 = 928902127) B928902127
theorem B825690779 : Blo 2035435 825690779 := bstep (se 1 (by rfl) ⟨619268084, by rfl⟩ : syracuseStep 825690779 = 1238536169) B1238536169
theorem B550460519 : Blo 2035435 550460519 := bstep (se 1 (by rfl) ⟨412845389, by rfl⟩ : syracuseStep 550460519 = 825690779) B825690779
theorem B366973679 : Blo 2035435 366973679 := bstep (se 1 (by rfl) ⟨275230259, by rfl⟩ : syracuseStep 366973679 = 550460519) B550460519
theorem B978596477 : Blo 2035435 978596477 := bstep (se 3 (by rfl) ⟨183486839, by rfl⟩ : syracuseStep 978596477 = 366973679) B366973679
theorem B652397651 : Blo 2035435 652397651 := bstep (se 1 (by rfl) ⟨489298238, by rfl⟩ : syracuseStep 652397651 = 978596477) B978596477
theorem B434931767 : Blo 2035435 434931767 := bstep (se 1 (by rfl) ⟨326198825, by rfl⟩ : syracuseStep 434931767 = 652397651) B652397651
theorem B289954511 : Blo 2035435 289954511 := bstep (se 1 (by rfl) ⟨217465883, by rfl⟩ : syracuseStep 289954511 = 434931767) B434931767
theorem B193303007 : Blo 2035435 193303007 := bstep (se 1 (by rfl) ⟨144977255, by rfl⟩ : syracuseStep 193303007 = 289954511) B289954511
theorem B128868671 : Blo 2035435 128868671 := bstep (se 1 (by rfl) ⟨96651503, by rfl⟩ : syracuseStep 128868671 = 193303007) B193303007
theorem B343649789 : Blo 2035435 343649789 := bstep (se 3 (by rfl) ⟨64434335, by rfl⟩ : syracuseStep 343649789 = 128868671) B128868671
theorem B229099859 : Blo 2035435 229099859 := bstep (se 1 (by rfl) ⟨171824894, by rfl⟩ : syracuseStep 229099859 = 343649789) B343649789
theorem B152733239 : Blo 2035435 152733239 := bstep (se 1 (by rfl) ⟨114549929, by rfl⟩ : syracuseStep 152733239 = 229099859) B229099859
theorem B101822159 : Blo 2035435 101822159 := bstep (se 1 (by rfl) ⟨76366619, by rfl⟩ : syracuseStep 101822159 = 152733239) B152733239
theorem B67881439 : Blo 2035435 67881439 := bstep (se 1 (by rfl) ⟨50911079, by rfl⟩ : syracuseStep 67881439 = 101822159) B101822159
theorem B90508585 : Blo 2035435 90508585 := bstep (se 2 (by rfl) ⟨33940719, by rfl⟩ : syracuseStep 90508585 = 67881439) B67881439
theorem B120678113 : Blo 2035435 120678113 := bstep (se 2 (by rfl) ⟨45254292, by rfl⟩ : syracuseStep 120678113 = 90508585) B90508585
theorem B80452075 : Blo 2035435 80452075 := bstep (se 1 (by rfl) ⟨60339056, by rfl⟩ : syracuseStep 80452075 = 120678113) B120678113
theorem B107269433 : Blo 2035435 107269433 := bstep (se 2 (by rfl) ⟨40226037, by rfl⟩ : syracuseStep 107269433 = 80452075) B80452075
theorem B71512955 : Blo 2035435 71512955 := bstep (se 1 (by rfl) ⟨53634716, by rfl⟩ : syracuseStep 71512955 = 107269433) B107269433
theorem B47675303 : Blo 2035435 47675303 := bstep (se 1 (by rfl) ⟨35756477, by rfl⟩ : syracuseStep 47675303 = 71512955) B71512955
theorem B31783535 : Blo 2035435 31783535 := bstep (se 1 (by rfl) ⟨23837651, by rfl⟩ : syracuseStep 31783535 = 47675303) B47675303
theorem B21189023 : Blo 2035435 21189023 := bstep (se 1 (by rfl) ⟨15891767, by rfl⟩ : syracuseStep 21189023 = 31783535) B31783535
theorem B14126015 : Blo 2035435 14126015 := bstep (se 1 (by rfl) ⟨10594511, by rfl⟩ : syracuseStep 14126015 = 21189023) B21189023
theorem B9417343 : Blo 2035435 9417343 := bstep (se 1 (by rfl) ⟨7063007, by rfl⟩ : syracuseStep 9417343 = 14126015) B14126015
theorem B12556457 : Blo 2035435 12556457 := bstep (se 2 (by rfl) ⟨4708671, by rfl⟩ : syracuseStep 12556457 = 9417343) B9417343
theorem B8370971 : Blo 2035435 8370971 := bstep (se 1 (by rfl) ⟨6278228, by rfl⟩ : syracuseStep 8370971 = 12556457) B12556457
theorem B5580647 : Blo 2035435 5580647 := bstep (se 1 (by rfl) ⟨4185485, by rfl⟩ : syracuseStep 5580647 = 8370971) B8370971
theorem B3720431 : Blo 2035435 3720431 := bstep (se 1 (by rfl) ⟨2790323, by rfl⟩ : syracuseStep 3720431 = 5580647) B5580647
theorem B9921149 : Blo 2035435 9921149 := bstep (se 3 (by rfl) ⟨1860215, by rfl⟩ : syracuseStep 9921149 = 3720431) B3720431
theorem B6614099 : Blo 2035435 6614099 := bstep (se 1 (by rfl) ⟨4960574, by rfl⟩ : syracuseStep 6614099 = 9921149) B9921149
theorem B4409399 : Blo 2035435 4409399 := bstep (se 1 (by rfl) ⟨3307049, by rfl⟩ : syracuseStep 4409399 = 6614099) B6614099
theorem B2939599 : Blo 2035435 2939599 := bstep (se 1 (by rfl) ⟨2204699, by rfl⟩ : syracuseStep 2939599 = 4409399) B4409399
theorem B3919465 : Blo 2035435 3919465 := bstep (se 2 (by rfl) ⟨1469799, by rfl⟩ : syracuseStep 3919465 = 2939599) B2939599
theorem B5225953 : Blo 2035435 5225953 := bstep (se 2 (by rfl) ⟨1959732, by rfl⟩ : syracuseStep 5225953 = 3919465) B3919465
theorem B6967937 : Blo 2035435 6967937 := bstep (se 2 (by rfl) ⟨2612976, by rfl⟩ : syracuseStep 6967937 = 5225953) B5225953
theorem B4645291 : Blo 2035435 4645291 := bstep (se 1 (by rfl) ⟨3483968, by rfl⟩ : syracuseStep 4645291 = 6967937) B6967937
theorem B6193721 : Blo 2035435 6193721 := bstep (se 2 (by rfl) ⟨2322645, by rfl⟩ : syracuseStep 6193721 = 4645291) B4645291
theorem B4129147 : Blo 2035435 4129147 := bstep (se 1 (by rfl) ⟨3096860, by rfl⟩ : syracuseStep 4129147 = 6193721) B6193721
theorem B5505529 : Blo 2035435 5505529 := bstep (se 2 (by rfl) ⟨2064573, by rfl⟩ : syracuseStep 5505529 = 4129147) B4129147
theorem B7340705 : Blo 2035435 7340705 := bstep (se 2 (by rfl) ⟨2752764, by rfl⟩ : syracuseStep 7340705 = 5505529) B5505529
theorem B4893803 : Blo 2035435 4893803 := bstep (se 1 (by rfl) ⟨3670352, by rfl⟩ : syracuseStep 4893803 = 7340705) B7340705
theorem B3262535 : Blo 2035435 3262535 := bstep (se 1 (by rfl) ⟨2446901, by rfl⟩ : syracuseStep 3262535 = 4893803) B4893803
theorem B2175023 : Blo 2035435 2175023 := bstep (se 1 (by rfl) ⟨1631267, by rfl⟩ : syracuseStep 2175023 = 3262535) B3262535
theorem B5800061 : Blo 2035435 5800061 := bstep (se 3 (by rfl) ⟨1087511, by rfl⟩ : syracuseStep 5800061 = 2175023) B2175023
theorem B3866707 : Blo 2035435 3866707 := bstep (se 1 (by rfl) ⟨2900030, by rfl⟩ : syracuseStep 3866707 = 5800061) B5800061
theorem B5155609 : Blo 2035435 5155609 := bstep (se 2 (by rfl) ⟨1933353, by rfl⟩ : syracuseStep 5155609 = 3866707) B3866707
theorem B6874145 : Blo 2035435 6874145 := bstep (se 2 (by rfl) ⟨2577804, by rfl⟩ : syracuseStep 6874145 = 5155609) B5155609
theorem B4582763 : Blo 2035435 4582763 := bstep (se 1 (by rfl) ⟨3437072, by rfl⟩ : syracuseStep 4582763 = 6874145) B6874145
theorem B3055175 : Blo 2035435 3055175 := bstep (se 1 (by rfl) ⟨2291381, by rfl⟩ : syracuseStep 3055175 = 4582763) B4582763
theorem B2036783 : Blo 2035435 2036783 := bstep (se 1 (by rfl) ⟨1527587, by rfl⟩ : syracuseStep 2036783 = 3055175) B3055175
theorem B3055181 : Blo 2035435 3055181 := bbase (se 3 (by rfl) ⟨572846, by rfl⟩ : syracuseStep 3055181 = 1145693) (by norm_num)
theorem B2036787 : Blo 2035435 2036787 := bstep (se 1 (by rfl) ⟨1527590, by rfl⟩ : syracuseStep 2036787 = 3055181) B3055181
theorem B4582781 : Blo 2035435 4582781 := bbase (se 3 (by rfl) ⟨859271, by rfl⟩ : syracuseStep 4582781 = 1718543) (by norm_num)
theorem B3055187 : Blo 2035435 3055187 := bstep (se 1 (by rfl) ⟨2291390, by rfl⟩ : syracuseStep 3055187 = 4582781) B4582781
theorem B2036791 : Blo 2035435 2036791 := bstep (se 1 (by rfl) ⟨1527593, by rfl⟩ : syracuseStep 2036791 = 3055187) B3055187
theorem B3437093 : Blo 2035435 3437093 := bbase (se 4 (by rfl) ⟨322227, by rfl⟩ : syracuseStep 3437093 = 644455) (by norm_num)
theorem B2291395 : Blo 2035435 2291395 := bstep (se 1 (by rfl) ⟨1718546, by rfl⟩ : syracuseStep 2291395 = 3437093) B3437093
theorem B3055193 : Blo 2035435 3055193 := bstep (se 2 (by rfl) ⟨1145697, by rfl⟩ : syracuseStep 3055193 = 2291395) B2291395
theorem B2036795 : Blo 2035435 2036795 := bstep (se 1 (by rfl) ⟨1527596, by rfl⟩ : syracuseStep 2036795 = 3055193) B3055193
theorem B2900053 : Blo 2035435 2900053 := bbase (se 8 (by rfl) ⟨16992, by rfl⟩ : syracuseStep 2900053 = 33985) (by norm_num)
theorem B15466949 : Blo 2035435 15466949 := bstep (se 4 (by rfl) ⟨1450026, by rfl⟩ : syracuseStep 15466949 = 2900053) B2900053
theorem B10311299 : Blo 2035435 10311299 := bstep (se 1 (by rfl) ⟨7733474, by rfl⟩ : syracuseStep 10311299 = 15466949) B15466949
theorem B6874199 : Blo 2035435 6874199 := bstep (se 1 (by rfl) ⟨5155649, by rfl⟩ : syracuseStep 6874199 = 10311299) B10311299
theorem B4582799 : Blo 2035435 4582799 := bstep (se 1 (by rfl) ⟨3437099, by rfl⟩ : syracuseStep 4582799 = 6874199) B6874199
theorem B3055199 : Blo 2035435 3055199 := bstep (se 1 (by rfl) ⟨2291399, by rfl⟩ : syracuseStep 3055199 = 4582799) B4582799
theorem B2036799 : Blo 2035435 2036799 := bstep (se 1 (by rfl) ⟨1527599, by rfl⟩ : syracuseStep 2036799 = 3055199) B3055199
theorem B3055205 : Blo 2035435 3055205 := bbase (se 4 (by rfl) ⟨286425, by rfl⟩ : syracuseStep 3055205 = 572851) (by norm_num)
theorem B2036803 : Blo 2035435 2036803 := bstep (se 1 (by rfl) ⟨1527602, by rfl⟩ : syracuseStep 2036803 = 3055205) B3055205
theorem B2175049 : Blo 2035435 2175049 := bbase (se 2 (by rfl) ⟨815643, by rfl⟩ : syracuseStep 2175049 = 1631287) (by norm_num)
theorem B2900065 : Blo 2035435 2900065 := bstep (se 2 (by rfl) ⟨1087524, by rfl⟩ : syracuseStep 2900065 = 2175049) B2175049
theorem B3866753 : Blo 2035435 3866753 := bstep (se 2 (by rfl) ⟨1450032, by rfl⟩ : syracuseStep 3866753 = 2900065) B2900065
theorem B2577835 : Blo 2035435 2577835 := bstep (se 1 (by rfl) ⟨1933376, by rfl⟩ : syracuseStep 2577835 = 3866753) B3866753
theorem B3437113 : Blo 2035435 3437113 := bstep (se 2 (by rfl) ⟨1288917, by rfl⟩ : syracuseStep 3437113 = 2577835) B2577835
theorem B4582817 : Blo 2035435 4582817 := bstep (se 2 (by rfl) ⟨1718556, by rfl⟩ : syracuseStep 4582817 = 3437113) B3437113
theorem B3055211 : Blo 2035435 3055211 := bstep (se 1 (by rfl) ⟨2291408, by rfl⟩ : syracuseStep 3055211 = 4582817) B4582817
theorem B2036807 : Blo 2035435 2036807 := bstep (se 1 (by rfl) ⟨1527605, by rfl⟩ : syracuseStep 2036807 = 3055211) B3055211
theorem B2291413 : Blo 2035435 2291413 := bbase (se 7 (by rfl) ⟨26852, by rfl⟩ : syracuseStep 2291413 = 53705) (by norm_num)
theorem B3055217 : Blo 2035435 3055217 := bstep (se 2 (by rfl) ⟨1145706, by rfl⟩ : syracuseStep 3055217 = 2291413) B2291413
theorem B2036811 : Blo 2035435 2036811 := bstep (se 1 (by rfl) ⟨1527608, by rfl⟩ : syracuseStep 2036811 = 3055217) B3055217
theorem B2577845 : Blo 2035435 2577845 := bbase (se 5 (by rfl) ⟨120836, by rfl⟩ : syracuseStep 2577845 = 241673) (by norm_num)
theorem B6874253 : Blo 2035435 6874253 := bstep (se 3 (by rfl) ⟨1288922, by rfl⟩ : syracuseStep 6874253 = 2577845) B2577845
theorem B4582835 : Blo 2035435 4582835 := bstep (se 1 (by rfl) ⟨3437126, by rfl⟩ : syracuseStep 4582835 = 6874253) B6874253
theorem B3055223 : Blo 2035435 3055223 := bstep (se 1 (by rfl) ⟨2291417, by rfl⟩ : syracuseStep 3055223 = 4582835) B4582835
theorem B2036815 : Blo 2035435 2036815 := bstep (se 1 (by rfl) ⟨1527611, by rfl⟩ : syracuseStep 2036815 = 3055223) B3055223
theorem B3055229 : Blo 2035435 3055229 := bbase (se 3 (by rfl) ⟨572855, by rfl⟩ : syracuseStep 3055229 = 1145711) (by norm_num)
theorem B2036819 : Blo 2035435 2036819 := bstep (se 1 (by rfl) ⟨1527614, by rfl⟩ : syracuseStep 2036819 = 3055229) B3055229
theorem B4582853 : Blo 2035435 4582853 := bbase (se 4 (by rfl) ⟨429642, by rfl⟩ : syracuseStep 4582853 = 859285) (by norm_num)
theorem B3055235 : Blo 2035435 3055235 := bstep (se 1 (by rfl) ⟨2291426, by rfl⟩ : syracuseStep 3055235 = 4582853) B4582853
theorem B2036823 : Blo 2035435 2036823 := bstep (se 1 (by rfl) ⟨1527617, by rfl⟩ : syracuseStep 2036823 = 3055235) B3055235
theorem B11758645 : Blo 2035435 11758645 := bbase (se 5 (by rfl) ⟨551186, by rfl⟩ : syracuseStep 11758645 = 1102373) (by norm_num)
theorem B15678193 : Blo 2035435 15678193 := bstep (se 2 (by rfl) ⟨5879322, by rfl⟩ : syracuseStep 15678193 = 11758645) B11758645
theorem B20904257 : Blo 2035435 20904257 := bstep (se 2 (by rfl) ⟨7839096, by rfl⟩ : syracuseStep 20904257 = 15678193) B15678193
theorem B55744685 : Blo 2035435 55744685 := bstep (se 3 (by rfl) ⟨10452128, by rfl⟩ : syracuseStep 55744685 = 20904257) B20904257
theorem B37163123 : Blo 2035435 37163123 := bstep (se 1 (by rfl) ⟨27872342, by rfl⟩ : syracuseStep 37163123 = 55744685) B55744685
theorem B24775415 : Blo 2035435 24775415 := bstep (se 1 (by rfl) ⟨18581561, by rfl⟩ : syracuseStep 24775415 = 37163123) B37163123
theorem B16516943 : Blo 2035435 16516943 := bstep (se 1 (by rfl) ⟨12387707, by rfl⟩ : syracuseStep 16516943 = 24775415) B24775415
theorem B11011295 : Blo 2035435 11011295 := bstep (se 1 (by rfl) ⟨8258471, by rfl⟩ : syracuseStep 11011295 = 16516943) B16516943
theorem B7340863 : Blo 2035435 7340863 := bstep (se 1 (by rfl) ⟨5505647, by rfl⟩ : syracuseStep 7340863 = 11011295) B11011295
theorem B9787817 : Blo 2035435 9787817 := bstep (se 2 (by rfl) ⟨3670431, by rfl⟩ : syracuseStep 9787817 = 7340863) B7340863
theorem B6525211 : Blo 2035435 6525211 := bstep (se 1 (by rfl) ⟨4893908, by rfl⟩ : syracuseStep 6525211 = 9787817) B9787817
theorem B8700281 : Blo 2035435 8700281 := bstep (se 2 (by rfl) ⟨3262605, by rfl⟩ : syracuseStep 8700281 = 6525211) B6525211
theorem B5800187 : Blo 2035435 5800187 := bstep (se 1 (by rfl) ⟨4350140, by rfl⟩ : syracuseStep 5800187 = 8700281) B8700281
theorem B3866791 : Blo 2035435 3866791 := bstep (se 1 (by rfl) ⟨2900093, by rfl⟩ : syracuseStep 3866791 = 5800187) B5800187
theorem B5155721 : Blo 2035435 5155721 := bstep (se 2 (by rfl) ⟨1933395, by rfl⟩ : syracuseStep 5155721 = 3866791) B3866791
theorem B3437147 : Blo 2035435 3437147 := bstep (se 1 (by rfl) ⟨2577860, by rfl⟩ : syracuseStep 3437147 = 5155721) B5155721
theorem B2291431 : Blo 2035435 2291431 := bstep (se 1 (by rfl) ⟨1718573, by rfl⟩ : syracuseStep 2291431 = 3437147) B3437147
theorem B3055241 : Blo 2035435 3055241 := bstep (se 2 (by rfl) ⟨1145715, by rfl⟩ : syracuseStep 3055241 = 2291431) B2291431
theorem B2036827 : Blo 2035435 2036827 := bstep (se 1 (by rfl) ⟨1527620, by rfl⟩ : syracuseStep 2036827 = 3055241) B3055241
theorem B10311461 : Blo 2035435 10311461 := bbase (se 4 (by rfl) ⟨966699, by rfl⟩ : syracuseStep 10311461 = 1933399) (by norm_num)
theorem B6874307 : Blo 2035435 6874307 := bstep (se 1 (by rfl) ⟨5155730, by rfl⟩ : syracuseStep 6874307 = 10311461) B10311461
theorem B4582871 : Blo 2035435 4582871 := bstep (se 1 (by rfl) ⟨3437153, by rfl⟩ : syracuseStep 4582871 = 6874307) B6874307
theorem B3055247 : Blo 2035435 3055247 := bstep (se 1 (by rfl) ⟨2291435, by rfl⟩ : syracuseStep 3055247 = 4582871) B4582871
theorem B2036831 : Blo 2035435 2036831 := bstep (se 1 (by rfl) ⟨1527623, by rfl⟩ : syracuseStep 2036831 = 3055247) B3055247
theorem B3055253 : Blo 2035435 3055253 := bbase (se 6 (by rfl) ⟨71607, by rfl⟩ : syracuseStep 3055253 = 143215) (by norm_num)
theorem B2036835 : Blo 2035435 2036835 := bstep (se 1 (by rfl) ⟨1527626, by rfl⟩ : syracuseStep 2036835 = 3055253) B3055253
theorem B3182029 : Blo 2035435 3182029 := bbase (se 3 (by rfl) ⟨596630, by rfl⟩ : syracuseStep 3182029 = 1193261) (by norm_num)
theorem B67883285 : Blo 2035435 67883285 := bstep (se 6 (by rfl) ⟨1591014, by rfl⟩ : syracuseStep 67883285 = 3182029) B3182029
theorem B45255523 : Blo 2035435 45255523 := bstep (se 1 (by rfl) ⟨33941642, by rfl⟩ : syracuseStep 45255523 = 67883285) B67883285
theorem B60340697 : Blo 2035435 60340697 := bstep (se 2 (by rfl) ⟨22627761, by rfl⟩ : syracuseStep 60340697 = 45255523) B45255523
theorem B40227131 : Blo 2035435 40227131 := bstep (se 1 (by rfl) ⟨30170348, by rfl⟩ : syracuseStep 40227131 = 60340697) B60340697
theorem B26818087 : Blo 2035435 26818087 := bstep (se 1 (by rfl) ⟨20113565, by rfl⟩ : syracuseStep 26818087 = 40227131) B40227131
theorem B35757449 : Blo 2035435 35757449 := bstep (se 2 (by rfl) ⟨13409043, by rfl⟩ : syracuseStep 35757449 = 26818087) B26818087
theorem B23838299 : Blo 2035435 23838299 := bstep (se 1 (by rfl) ⟨17878724, by rfl⟩ : syracuseStep 23838299 = 35757449) B35757449
theorem B15892199 : Blo 2035435 15892199 := bstep (se 1 (by rfl) ⟨11919149, by rfl⟩ : syracuseStep 15892199 = 23838299) B23838299
theorem B10594799 : Blo 2035435 10594799 := bstep (se 1 (by rfl) ⟨7946099, by rfl⟩ : syracuseStep 10594799 = 15892199) B15892199
theorem B7063199 : Blo 2035435 7063199 := bstep (se 1 (by rfl) ⟨5297399, by rfl⟩ : syracuseStep 7063199 = 10594799) B10594799
theorem B4708799 : Blo 2035435 4708799 := bstep (se 1 (by rfl) ⟨3531599, by rfl⟩ : syracuseStep 4708799 = 7063199) B7063199
theorem B3139199 : Blo 2035435 3139199 := bstep (se 1 (by rfl) ⟨2354399, by rfl⟩ : syracuseStep 3139199 = 4708799) B4708799
theorem B2092799 : Blo 2035435 2092799 := bstep (se 1 (by rfl) ⟨1569599, by rfl⟩ : syracuseStep 2092799 = 3139199) B3139199
theorem B5580797 : Blo 2035435 5580797 := bstep (se 3 (by rfl) ⟨1046399, by rfl⟩ : syracuseStep 5580797 = 2092799) B2092799
theorem B14882125 : Blo 2035435 14882125 := bstep (se 3 (by rfl) ⟨2790398, by rfl⟩ : syracuseStep 14882125 = 5580797) B5580797
theorem B19842833 : Blo 2035435 19842833 := bstep (se 2 (by rfl) ⟨7441062, by rfl⟩ : syracuseStep 19842833 = 14882125) B14882125
theorem B13228555 : Blo 2035435 13228555 := bstep (se 1 (by rfl) ⟨9921416, by rfl⟩ : syracuseStep 13228555 = 19842833) B19842833
theorem B17638073 : Blo 2035435 17638073 := bstep (se 2 (by rfl) ⟨6614277, by rfl⟩ : syracuseStep 17638073 = 13228555) B13228555
theorem B11758715 : Blo 2035435 11758715 := bstep (se 1 (by rfl) ⟨8819036, by rfl⟩ : syracuseStep 11758715 = 17638073) B17638073
theorem B7839143 : Blo 2035435 7839143 := bstep (se 1 (by rfl) ⟨5879357, by rfl⟩ : syracuseStep 7839143 = 11758715) B11758715
theorem B5226095 : Blo 2035435 5226095 := bstep (se 1 (by rfl) ⟨3919571, by rfl⟩ : syracuseStep 5226095 = 7839143) B7839143
theorem B3484063 : Blo 2035435 3484063 := bstep (se 1 (by rfl) ⟨2613047, by rfl⟩ : syracuseStep 3484063 = 5226095) B5226095
theorem B18581669 : Blo 2035435 18581669 := bstep (se 4 (by rfl) ⟨1742031, by rfl⟩ : syracuseStep 18581669 = 3484063) B3484063
theorem B12387779 : Blo 2035435 12387779 := bstep (se 1 (by rfl) ⟨9290834, by rfl⟩ : syracuseStep 12387779 = 18581669) B18581669
theorem B8258519 : Blo 2035435 8258519 := bstep (se 1 (by rfl) ⟨6193889, by rfl⟩ : syracuseStep 8258519 = 12387779) B12387779
theorem B5505679 : Blo 2035435 5505679 := bstep (se 1 (by rfl) ⟨4129259, by rfl⟩ : syracuseStep 5505679 = 8258519) B8258519
theorem B7340905 : Blo 2035435 7340905 := bstep (se 2 (by rfl) ⟨2752839, by rfl⟩ : syracuseStep 7340905 = 5505679) B5505679
theorem B9787873 : Blo 2035435 9787873 := bstep (se 2 (by rfl) ⟨3670452, by rfl⟩ : syracuseStep 9787873 = 7340905) B7340905
theorem B13050497 : Blo 2035435 13050497 := bstep (se 2 (by rfl) ⟨4893936, by rfl⟩ : syracuseStep 13050497 = 9787873) B9787873
theorem B8700331 : Blo 2035435 8700331 := bstep (se 1 (by rfl) ⟨6525248, by rfl⟩ : syracuseStep 8700331 = 13050497) B13050497
theorem B11600441 : Blo 2035435 11600441 := bstep (se 2 (by rfl) ⟨4350165, by rfl⟩ : syracuseStep 11600441 = 8700331) B8700331
theorem B7733627 : Blo 2035435 7733627 := bstep (se 1 (by rfl) ⟨5800220, by rfl⟩ : syracuseStep 7733627 = 11600441) B11600441
theorem B5155751 : Blo 2035435 5155751 := bstep (se 1 (by rfl) ⟨3866813, by rfl⟩ : syracuseStep 5155751 = 7733627) B7733627
theorem B3437167 : Blo 2035435 3437167 := bstep (se 1 (by rfl) ⟨2577875, by rfl⟩ : syracuseStep 3437167 = 5155751) B5155751
theorem B4582889 : Blo 2035435 4582889 := bstep (se 2 (by rfl) ⟨1718583, by rfl⟩ : syracuseStep 4582889 = 3437167) B3437167
theorem B3055259 : Blo 2035435 3055259 := bstep (se 1 (by rfl) ⟨2291444, by rfl⟩ : syracuseStep 3055259 = 4582889) B4582889
theorem B2036839 : Blo 2035435 2036839 := bstep (se 1 (by rfl) ⟨1527629, by rfl⟩ : syracuseStep 2036839 = 3055259) B3055259
theorem B2291449 : Blo 2035435 2291449 := bbase (se 2 (by rfl) ⟨859293, by rfl⟩ : syracuseStep 2291449 = 1718587) (by norm_num)
theorem B3055265 : Blo 2035435 3055265 := bstep (se 2 (by rfl) ⟨1145724, by rfl⟩ : syracuseStep 3055265 = 2291449) B2291449
theorem B2036843 : Blo 2035435 2036843 := bstep (se 1 (by rfl) ⟨1527632, by rfl⟩ : syracuseStep 2036843 = 3055265) B3055265
theorem B3262637 : Blo 2035435 3262637 := bbase (se 3 (by rfl) ⟨611744, by rfl⟩ : syracuseStep 3262637 = 1223489) (by norm_num)
theorem B8700365 : Blo 2035435 8700365 := bstep (se 3 (by rfl) ⟨1631318, by rfl⟩ : syracuseStep 8700365 = 3262637) B3262637
theorem B5800243 : Blo 2035435 5800243 := bstep (se 1 (by rfl) ⟨4350182, by rfl⟩ : syracuseStep 5800243 = 8700365) B8700365
theorem B7733657 : Blo 2035435 7733657 := bstep (se 2 (by rfl) ⟨2900121, by rfl⟩ : syracuseStep 7733657 = 5800243) B5800243
theorem B5155771 : Blo 2035435 5155771 := bstep (se 1 (by rfl) ⟨3866828, by rfl⟩ : syracuseStep 5155771 = 7733657) B7733657
theorem B6874361 : Blo 2035435 6874361 := bstep (se 2 (by rfl) ⟨2577885, by rfl⟩ : syracuseStep 6874361 = 5155771) B5155771
theorem B4582907 : Blo 2035435 4582907 := bstep (se 1 (by rfl) ⟨3437180, by rfl⟩ : syracuseStep 4582907 = 6874361) B6874361
theorem B3055271 : Blo 2035435 3055271 := bstep (se 1 (by rfl) ⟨2291453, by rfl⟩ : syracuseStep 3055271 = 4582907) B4582907
theorem B2036847 : Blo 2035435 2036847 := bstep (se 1 (by rfl) ⟨1527635, by rfl⟩ : syracuseStep 2036847 = 3055271) B3055271
theorem B3055277 : Blo 2035435 3055277 := bbase (se 3 (by rfl) ⟨572864, by rfl⟩ : syracuseStep 3055277 = 1145729) (by norm_num)
theorem B2036851 : Blo 2035435 2036851 := bstep (se 1 (by rfl) ⟨1527638, by rfl⟩ : syracuseStep 2036851 = 3055277) B3055277
theorem B4582925 : Blo 2035435 4582925 := bbase (se 3 (by rfl) ⟨859298, by rfl⟩ : syracuseStep 4582925 = 1718597) (by norm_num)
theorem B3055283 : Blo 2035435 3055283 := bstep (se 1 (by rfl) ⟨2291462, by rfl⟩ : syracuseStep 3055283 = 4582925) B4582925
theorem B2036855 : Blo 2035435 2036855 := bstep (se 1 (by rfl) ⟨1527641, by rfl⟩ : syracuseStep 2036855 = 3055283) B3055283
theorem B2577901 : Blo 2035435 2577901 := bbase (se 3 (by rfl) ⟨483356, by rfl⟩ : syracuseStep 2577901 = 966713) (by norm_num)
theorem B3437201 : Blo 2035435 3437201 := bstep (se 2 (by rfl) ⟨1288950, by rfl⟩ : syracuseStep 3437201 = 2577901) B2577901
theorem B2291467 : Blo 2035435 2291467 := bstep (se 1 (by rfl) ⟨1718600, by rfl⟩ : syracuseStep 2291467 = 3437201) B3437201
theorem B3055289 : Blo 2035435 3055289 := bstep (se 2 (by rfl) ⟨1145733, by rfl⟩ : syracuseStep 3055289 = 2291467) B2291467
theorem B2036859 : Blo 2035435 2036859 := bstep (se 1 (by rfl) ⟨1527644, by rfl⟩ : syracuseStep 2036859 = 3055289) B3055289
theorem B6364133 : Blo 2035435 6364133 := bbase (se 4 (by rfl) ⟨596637, by rfl⟩ : syracuseStep 6364133 = 1193275) (by norm_num)
theorem B4242755 : Blo 2035435 4242755 := bstep (se 1 (by rfl) ⟨3182066, by rfl⟩ : syracuseStep 4242755 = 6364133) B6364133
theorem B2828503 : Blo 2035435 2828503 := bstep (se 1 (by rfl) ⟨2121377, by rfl⟩ : syracuseStep 2828503 = 4242755) B4242755
theorem B15085349 : Blo 2035435 15085349 := bstep (se 4 (by rfl) ⟨1414251, by rfl⟩ : syracuseStep 15085349 = 2828503) B2828503
theorem B10056899 : Blo 2035435 10056899 := bstep (se 1 (by rfl) ⟨7542674, by rfl⟩ : syracuseStep 10056899 = 15085349) B15085349
theorem B26818397 : Blo 2035435 26818397 := bstep (se 3 (by rfl) ⟨5028449, by rfl⟩ : syracuseStep 26818397 = 10056899) B10056899
theorem B17878931 : Blo 2035435 17878931 := bstep (se 1 (by rfl) ⟨13409198, by rfl⟩ : syracuseStep 17878931 = 26818397) B26818397
theorem B11919287 : Blo 2035435 11919287 := bstep (se 1 (by rfl) ⟨8939465, by rfl⟩ : syracuseStep 11919287 = 17878931) B17878931
theorem B7946191 : Blo 2035435 7946191 := bstep (se 1 (by rfl) ⟨5959643, by rfl⟩ : syracuseStep 7946191 = 11919287) B11919287
theorem B42379685 : Blo 2035435 42379685 := bstep (se 4 (by rfl) ⟨3973095, by rfl⟩ : syracuseStep 42379685 = 7946191) B7946191
theorem B28253123 : Blo 2035435 28253123 := bstep (se 1 (by rfl) ⟨21189842, by rfl⟩ : syracuseStep 28253123 = 42379685) B42379685
theorem B18835415 : Blo 2035435 18835415 := bstep (se 1 (by rfl) ⟨14126561, by rfl⟩ : syracuseStep 18835415 = 28253123) B28253123
theorem B12556943 : Blo 2035435 12556943 := bstep (se 1 (by rfl) ⟨9417707, by rfl⟩ : syracuseStep 12556943 = 18835415) B18835415
theorem B8371295 : Blo 2035435 8371295 := bstep (se 1 (by rfl) ⟨6278471, by rfl⟩ : syracuseStep 8371295 = 12556943) B12556943
theorem B5580863 : Blo 2035435 5580863 := bstep (se 1 (by rfl) ⟨4185647, by rfl⟩ : syracuseStep 5580863 = 8371295) B8371295
theorem B3720575 : Blo 2035435 3720575 := bstep (se 1 (by rfl) ⟨2790431, by rfl⟩ : syracuseStep 3720575 = 5580863) B5580863
theorem B2480383 : Blo 2035435 2480383 := bstep (se 1 (by rfl) ⟨1860287, by rfl⟩ : syracuseStep 2480383 = 3720575) B3720575
theorem B3307177 : Blo 2035435 3307177 := bstep (se 2 (by rfl) ⟨1240191, by rfl⟩ : syracuseStep 3307177 = 2480383) B2480383
theorem B4409569 : Blo 2035435 4409569 := bstep (se 2 (by rfl) ⟨1653588, by rfl⟩ : syracuseStep 4409569 = 3307177) B3307177
theorem B23517701 : Blo 2035435 23517701 := bstep (se 4 (by rfl) ⟨2204784, by rfl⟩ : syracuseStep 23517701 = 4409569) B4409569
theorem B15678467 : Blo 2035435 15678467 := bstep (se 1 (by rfl) ⟨11758850, by rfl⟩ : syracuseStep 15678467 = 23517701) B23517701
theorem B10452311 : Blo 2035435 10452311 := bstep (se 1 (by rfl) ⟨7839233, by rfl⟩ : syracuseStep 10452311 = 15678467) B15678467
theorem B6968207 : Blo 2035435 6968207 := bstep (se 1 (by rfl) ⟨5226155, by rfl⟩ : syracuseStep 6968207 = 10452311) B10452311
theorem B18581885 : Blo 2035435 18581885 := bstep (se 3 (by rfl) ⟨3484103, by rfl⟩ : syracuseStep 18581885 = 6968207) B6968207
theorem B12387923 : Blo 2035435 12387923 := bstep (se 1 (by rfl) ⟨9290942, by rfl⟩ : syracuseStep 12387923 = 18581885) B18581885
theorem B8258615 : Blo 2035435 8258615 := bstep (se 1 (by rfl) ⟨6193961, by rfl⟩ : syracuseStep 8258615 = 12387923) B12387923
theorem B5505743 : Blo 2035435 5505743 := bstep (se 1 (by rfl) ⟨4129307, by rfl⟩ : syracuseStep 5505743 = 8258615) B8258615
theorem B14681981 : Blo 2035435 14681981 := bstep (se 3 (by rfl) ⟨2752871, by rfl⟩ : syracuseStep 14681981 = 5505743) B5505743
theorem B9787987 : Blo 2035435 9787987 := bstep (se 1 (by rfl) ⟨7340990, by rfl⟩ : syracuseStep 9787987 = 14681981) B14681981
theorem B13050649 : Blo 2035435 13050649 := bstep (se 2 (by rfl) ⟨4893993, by rfl⟩ : syracuseStep 13050649 = 9787987) B9787987
theorem B17400865 : Blo 2035435 17400865 := bstep (se 2 (by rfl) ⟨6525324, by rfl⟩ : syracuseStep 17400865 = 13050649) B13050649
theorem B23201153 : Blo 2035435 23201153 := bstep (se 2 (by rfl) ⟨8700432, by rfl⟩ : syracuseStep 23201153 = 17400865) B17400865
theorem B15467435 : Blo 2035435 15467435 := bstep (se 1 (by rfl) ⟨11600576, by rfl⟩ : syracuseStep 15467435 = 23201153) B23201153
theorem B10311623 : Blo 2035435 10311623 := bstep (se 1 (by rfl) ⟨7733717, by rfl⟩ : syracuseStep 10311623 = 15467435) B15467435
theorem B6874415 : Blo 2035435 6874415 := bstep (se 1 (by rfl) ⟨5155811, by rfl⟩ : syracuseStep 6874415 = 10311623) B10311623
theorem B4582943 : Blo 2035435 4582943 := bstep (se 1 (by rfl) ⟨3437207, by rfl⟩ : syracuseStep 4582943 = 6874415) B6874415
theorem B3055295 : Blo 2035435 3055295 := bstep (se 1 (by rfl) ⟨2291471, by rfl⟩ : syracuseStep 3055295 = 4582943) B4582943
theorem B2036863 : Blo 2035435 2036863 := bstep (se 1 (by rfl) ⟨1527647, by rfl⟩ : syracuseStep 2036863 = 3055295) B3055295
theorem B3055301 : Blo 2035435 3055301 := bbase (se 4 (by rfl) ⟨286434, by rfl⟩ : syracuseStep 3055301 = 572869) (by norm_num)
theorem B2036867 : Blo 2035435 2036867 := bstep (se 1 (by rfl) ⟨1527650, by rfl⟩ : syracuseStep 2036867 = 3055301) B3055301
theorem B3437221 : Blo 2035435 3437221 := bbase (se 4 (by rfl) ⟨322239, by rfl⟩ : syracuseStep 3437221 = 644479) (by norm_num)
theorem B4582961 : Blo 2035435 4582961 := bstep (se 2 (by rfl) ⟨1718610, by rfl⟩ : syracuseStep 4582961 = 3437221) B3437221
theorem B3055307 : Blo 2035435 3055307 := bstep (se 1 (by rfl) ⟨2291480, by rfl⟩ : syracuseStep 3055307 = 4582961) B4582961
theorem B2036871 : Blo 2035435 2036871 := bstep (se 1 (by rfl) ⟨1527653, by rfl⟩ : syracuseStep 2036871 = 3055307) B3055307
theorem B2291485 : Blo 2035435 2291485 := bbase (se 3 (by rfl) ⟨429653, by rfl⟩ : syracuseStep 2291485 = 859307) (by norm_num)
theorem B3055313 : Blo 2035435 3055313 := bstep (se 2 (by rfl) ⟨1145742, by rfl⟩ : syracuseStep 3055313 = 2291485) B2291485
theorem B2036875 : Blo 2035435 2036875 := bstep (se 1 (by rfl) ⟨1527656, by rfl⟩ : syracuseStep 2036875 = 3055313) B3055313
theorem B6874469 : Blo 2035435 6874469 := bbase (se 4 (by rfl) ⟨644481, by rfl⟩ : syracuseStep 6874469 = 1288963) (by norm_num)
theorem B4582979 : Blo 2035435 4582979 := bstep (se 1 (by rfl) ⟨3437234, by rfl⟩ : syracuseStep 4582979 = 6874469) B6874469
theorem B3055319 : Blo 2035435 3055319 := bstep (se 1 (by rfl) ⟨2291489, by rfl⟩ : syracuseStep 3055319 = 4582979) B4582979
theorem B2036879 : Blo 2035435 2036879 := bstep (se 1 (by rfl) ⟨1527659, by rfl⟩ : syracuseStep 2036879 = 3055319) B3055319
theorem B3055325 : Blo 2035435 3055325 := bbase (se 3 (by rfl) ⟨572873, by rfl⟩ : syracuseStep 3055325 = 1145747) (by norm_num)
theorem B2036883 : Blo 2035435 2036883 := bstep (se 1 (by rfl) ⟨1527662, by rfl⟩ : syracuseStep 2036883 = 3055325) B3055325
theorem B4582997 : Blo 2035435 4582997 := bbase (se 8 (by rfl) ⟨26853, by rfl⟩ : syracuseStep 4582997 = 53707) (by norm_num)
theorem B3055331 : Blo 2035435 3055331 := bstep (se 1 (by rfl) ⟨2291498, by rfl⟩ : syracuseStep 3055331 = 4582997) B4582997
theorem B2036887 : Blo 2035435 2036887 := bstep (se 1 (by rfl) ⟨1527665, by rfl⟩ : syracuseStep 2036887 = 3055331) B3055331
theorem B4350277 : Blo 2035435 4350277 := bbase (se 4 (by rfl) ⟨407838, by rfl⟩ : syracuseStep 4350277 = 815677) (by norm_num)
theorem B5800369 : Blo 2035435 5800369 := bstep (se 2 (by rfl) ⟨2175138, by rfl⟩ : syracuseStep 5800369 = 4350277) B4350277
theorem B7733825 : Blo 2035435 7733825 := bstep (se 2 (by rfl) ⟨2900184, by rfl⟩ : syracuseStep 7733825 = 5800369) B5800369
theorem B5155883 : Blo 2035435 5155883 := bstep (se 1 (by rfl) ⟨3866912, by rfl⟩ : syracuseStep 5155883 = 7733825) B7733825
theorem B3437255 : Blo 2035435 3437255 := bstep (se 1 (by rfl) ⟨2577941, by rfl⟩ : syracuseStep 3437255 = 5155883) B5155883
theorem B2291503 : Blo 2035435 2291503 := bstep (se 1 (by rfl) ⟨1718627, by rfl⟩ : syracuseStep 2291503 = 3437255) B3437255
theorem B3055337 : Blo 2035435 3055337 := bstep (se 2 (by rfl) ⟨1145751, by rfl⟩ : syracuseStep 3055337 = 2291503) B2291503
theorem B2036891 : Blo 2035435 2036891 := bstep (se 1 (by rfl) ⟨1527668, by rfl⟩ : syracuseStep 2036891 = 3055337) B3055337
theorem B4129373 : Blo 2035435 4129373 := bbase (se 3 (by rfl) ⟨774257, by rfl⟩ : syracuseStep 4129373 = 1548515) (by norm_num)
theorem B2752915 : Blo 2035435 2752915 := bstep (se 1 (by rfl) ⟨2064686, by rfl⟩ : syracuseStep 2752915 = 4129373) B4129373
theorem B3670553 : Blo 2035435 3670553 := bstep (se 2 (by rfl) ⟨1376457, by rfl⟩ : syracuseStep 3670553 = 2752915) B2752915
theorem B9788141 : Blo 2035435 9788141 := bstep (se 3 (by rfl) ⟨1835276, by rfl⟩ : syracuseStep 9788141 = 3670553) B3670553
theorem B26101709 : Blo 2035435 26101709 := bstep (se 3 (by rfl) ⟨4894070, by rfl⟩ : syracuseStep 26101709 = 9788141) B9788141
theorem B17401139 : Blo 2035435 17401139 := bstep (se 1 (by rfl) ⟨13050854, by rfl⟩ : syracuseStep 17401139 = 26101709) B26101709
theorem B11600759 : Blo 2035435 11600759 := bstep (se 1 (by rfl) ⟨8700569, by rfl⟩ : syracuseStep 11600759 = 17401139) B17401139
theorem B7733839 : Blo 2035435 7733839 := bstep (se 1 (by rfl) ⟨5800379, by rfl⟩ : syracuseStep 7733839 = 11600759) B11600759
theorem B10311785 : Blo 2035435 10311785 := bstep (se 2 (by rfl) ⟨3866919, by rfl⟩ : syracuseStep 10311785 = 7733839) B7733839
theorem B6874523 : Blo 2035435 6874523 := bstep (se 1 (by rfl) ⟨5155892, by rfl⟩ : syracuseStep 6874523 = 10311785) B10311785
theorem B4583015 : Blo 2035435 4583015 := bstep (se 1 (by rfl) ⟨3437261, by rfl⟩ : syracuseStep 4583015 = 6874523) B6874523
theorem B3055343 : Blo 2035435 3055343 := bstep (se 1 (by rfl) ⟨2291507, by rfl⟩ : syracuseStep 3055343 = 4583015) B4583015
theorem B2036895 : Blo 2035435 2036895 := bstep (se 1 (by rfl) ⟨1527671, by rfl⟩ : syracuseStep 2036895 = 3055343) B3055343
theorem B3055349 : Blo 2035435 3055349 := bbase (se 5 (by rfl) ⟨143219, by rfl⟩ : syracuseStep 3055349 = 286439) (by norm_num)
theorem B2036899 : Blo 2035435 2036899 := bstep (se 1 (by rfl) ⟨1527674, by rfl⟩ : syracuseStep 2036899 = 3055349) B3055349
theorem B4645565 : Blo 2035435 4645565 := bbase (se 3 (by rfl) ⟨871043, by rfl⟩ : syracuseStep 4645565 = 1742087) (by norm_num)
theorem B3097043 : Blo 2035435 3097043 := bstep (se 1 (by rfl) ⟨2322782, by rfl⟩ : syracuseStep 3097043 = 4645565) B4645565
theorem B2064695 : Blo 2035435 2064695 := bstep (se 1 (by rfl) ⟨1548521, by rfl⟩ : syracuseStep 2064695 = 3097043) B3097043
theorem B5505853 : Blo 2035435 5505853 := bstep (se 3 (by rfl) ⟨1032347, by rfl⟩ : syracuseStep 5505853 = 2064695) B2064695
theorem B7341137 : Blo 2035435 7341137 := bstep (se 2 (by rfl) ⟨2752926, by rfl⟩ : syracuseStep 7341137 = 5505853) B5505853
theorem B4894091 : Blo 2035435 4894091 := bstep (se 1 (by rfl) ⟨3670568, by rfl⟩ : syracuseStep 4894091 = 7341137) B7341137
theorem B3262727 : Blo 2035435 3262727 := bstep (se 1 (by rfl) ⟨2447045, by rfl⟩ : syracuseStep 3262727 = 4894091) B4894091
theorem B8700605 : Blo 2035435 8700605 := bstep (se 3 (by rfl) ⟨1631363, by rfl⟩ : syracuseStep 8700605 = 3262727) B3262727
theorem B5800403 : Blo 2035435 5800403 := bstep (se 1 (by rfl) ⟨4350302, by rfl⟩ : syracuseStep 5800403 = 8700605) B8700605
theorem B3866935 : Blo 2035435 3866935 := bstep (se 1 (by rfl) ⟨2900201, by rfl⟩ : syracuseStep 3866935 = 5800403) B5800403
theorem B5155913 : Blo 2035435 5155913 := bstep (se 2 (by rfl) ⟨1933467, by rfl⟩ : syracuseStep 5155913 = 3866935) B3866935
theorem B3437275 : Blo 2035435 3437275 := bstep (se 1 (by rfl) ⟨2577956, by rfl⟩ : syracuseStep 3437275 = 5155913) B5155913
theorem B4583033 : Blo 2035435 4583033 := bstep (se 2 (by rfl) ⟨1718637, by rfl⟩ : syracuseStep 4583033 = 3437275) B3437275
theorem B3055355 : Blo 2035435 3055355 := bstep (se 1 (by rfl) ⟨2291516, by rfl⟩ : syracuseStep 3055355 = 4583033) B4583033
theorem B2036903 : Blo 2035435 2036903 := bstep (se 1 (by rfl) ⟨1527677, by rfl⟩ : syracuseStep 2036903 = 3055355) B3055355
theorem B2291521 : Blo 2035435 2291521 := bbase (se 2 (by rfl) ⟨859320, by rfl⟩ : syracuseStep 2291521 = 1718641) (by norm_num)
theorem B3055361 : Blo 2035435 3055361 := bstep (se 2 (by rfl) ⟨1145760, by rfl⟩ : syracuseStep 3055361 = 2291521) B2291521
theorem B2036907 : Blo 2035435 2036907 := bstep (se 1 (by rfl) ⟨1527680, by rfl⟩ : syracuseStep 2036907 = 3055361) B3055361
theorem B5155933 : Blo 2035435 5155933 := bbase (se 3 (by rfl) ⟨966737, by rfl⟩ : syracuseStep 5155933 = 1933475) (by norm_num)
theorem B6874577 : Blo 2035435 6874577 := bstep (se 2 (by rfl) ⟨2577966, by rfl⟩ : syracuseStep 6874577 = 5155933) B5155933
theorem B4583051 : Blo 2035435 4583051 := bstep (se 1 (by rfl) ⟨3437288, by rfl⟩ : syracuseStep 4583051 = 6874577) B6874577
theorem B3055367 : Blo 2035435 3055367 := bstep (se 1 (by rfl) ⟨2291525, by rfl⟩ : syracuseStep 3055367 = 4583051) B4583051
theorem B2036911 : Blo 2035435 2036911 := bstep (se 1 (by rfl) ⟨1527683, by rfl⟩ : syracuseStep 2036911 = 3055367) B3055367
theorem B3055373 : Blo 2035435 3055373 := bbase (se 3 (by rfl) ⟨572882, by rfl⟩ : syracuseStep 3055373 = 1145765) (by norm_num)
theorem B2036915 : Blo 2035435 2036915 := bstep (se 1 (by rfl) ⟨1527686, by rfl⟩ : syracuseStep 2036915 = 3055373) B3055373
theorem B4583069 : Blo 2035435 4583069 := bbase (se 3 (by rfl) ⟨859325, by rfl⟩ : syracuseStep 4583069 = 1718651) (by norm_num)
theorem B3055379 : Blo 2035435 3055379 := bstep (se 1 (by rfl) ⟨2291534, by rfl⟩ : syracuseStep 3055379 = 4583069) B4583069
theorem B2036919 : Blo 2035435 2036919 := bstep (se 1 (by rfl) ⟨1527689, by rfl⟩ : syracuseStep 2036919 = 3055379) B3055379
theorem B3437309 : Blo 2035435 3437309 := bbase (se 3 (by rfl) ⟨644495, by rfl⟩ : syracuseStep 3437309 = 1288991) (by norm_num)
theorem B2291539 : Blo 2035435 2291539 := bstep (se 1 (by rfl) ⟨1718654, by rfl⟩ : syracuseStep 2291539 = 3437309) B3437309
theorem B3055385 : Blo 2035435 3055385 := bstep (se 2 (by rfl) ⟨1145769, by rfl⟩ : syracuseStep 3055385 = 2291539) B2291539
theorem B2036923 : Blo 2035435 2036923 := bstep (se 1 (by rfl) ⟨1527692, by rfl⟩ : syracuseStep 2036923 = 3055385) B3055385
theorem B3262765 : Blo 2035435 3262765 := bbase (se 3 (by rfl) ⟨611768, by rfl⟩ : syracuseStep 3262765 = 1223537) (by norm_num)
theorem B4350353 : Blo 2035435 4350353 := bstep (se 2 (by rfl) ⟨1631382, by rfl⟩ : syracuseStep 4350353 = 3262765) B3262765
theorem B11600941 : Blo 2035435 11600941 := bstep (se 3 (by rfl) ⟨2175176, by rfl⟩ : syracuseStep 11600941 = 4350353) B4350353
theorem B15467921 : Blo 2035435 15467921 := bstep (se 2 (by rfl) ⟨5800470, by rfl⟩ : syracuseStep 15467921 = 11600941) B11600941
theorem B10311947 : Blo 2035435 10311947 := bstep (se 1 (by rfl) ⟨7733960, by rfl⟩ : syracuseStep 10311947 = 15467921) B15467921
theorem B6874631 : Blo 2035435 6874631 := bstep (se 1 (by rfl) ⟨5155973, by rfl⟩ : syracuseStep 6874631 = 10311947) B10311947
theorem B4583087 : Blo 2035435 4583087 := bstep (se 1 (by rfl) ⟨3437315, by rfl⟩ : syracuseStep 4583087 = 6874631) B6874631
theorem B3055391 : Blo 2035435 3055391 := bstep (se 1 (by rfl) ⟨2291543, by rfl⟩ : syracuseStep 3055391 = 4583087) B4583087
theorem B2036927 : Blo 2035435 2036927 := bstep (se 1 (by rfl) ⟨1527695, by rfl⟩ : syracuseStep 2036927 = 3055391) B3055391
theorem B3055397 : Blo 2035435 3055397 := bbase (se 4 (by rfl) ⟨286443, by rfl⟩ : syracuseStep 3055397 = 572887) (by norm_num)
theorem B2036931 : Blo 2035435 2036931 := bstep (se 1 (by rfl) ⟨1527698, by rfl⟩ : syracuseStep 2036931 = 3055397) B3055397
theorem B2577997 : Blo 2035435 2577997 := bbase (se 3 (by rfl) ⟨483374, by rfl⟩ : syracuseStep 2577997 = 966749) (by norm_num)
theorem B3437329 : Blo 2035435 3437329 := bstep (se 2 (by rfl) ⟨1288998, by rfl⟩ : syracuseStep 3437329 = 2577997) B2577997
theorem B4583105 : Blo 2035435 4583105 := bstep (se 2 (by rfl) ⟨1718664, by rfl⟩ : syracuseStep 4583105 = 3437329) B3437329
theorem B3055403 : Blo 2035435 3055403 := bstep (se 1 (by rfl) ⟨2291552, by rfl⟩ : syracuseStep 3055403 = 4583105) B4583105
theorem B2036935 : Blo 2035435 2036935 := bstep (se 1 (by rfl) ⟨1527701, by rfl⟩ : syracuseStep 2036935 = 3055403) B3055403
theorem B2291557 : Blo 2035435 2291557 := bbase (se 4 (by rfl) ⟨214833, by rfl⟩ : syracuseStep 2291557 = 429667) (by norm_num)
theorem B3055409 : Blo 2035435 3055409 := bstep (se 2 (by rfl) ⟨1145778, by rfl⟩ : syracuseStep 3055409 = 2291557) B2291557
theorem B2036939 : Blo 2035435 2036939 := bstep (se 1 (by rfl) ⟨1527704, by rfl⟩ : syracuseStep 2036939 = 3055409) B3055409
theorem B5800517 : Blo 2035435 5800517 := bbase (se 4 (by rfl) ⟨543798, by rfl⟩ : syracuseStep 5800517 = 1087597) (by norm_num)
theorem B3867011 : Blo 2035435 3867011 := bstep (se 1 (by rfl) ⟨2900258, by rfl⟩ : syracuseStep 3867011 = 5800517) B5800517
theorem B2578007 : Blo 2035435 2578007 := bstep (se 1 (by rfl) ⟨1933505, by rfl⟩ : syracuseStep 2578007 = 3867011) B3867011
theorem B6874685 : Blo 2035435 6874685 := bstep (se 3 (by rfl) ⟨1289003, by rfl⟩ : syracuseStep 6874685 = 2578007) B2578007
theorem B4583123 : Blo 2035435 4583123 := bstep (se 1 (by rfl) ⟨3437342, by rfl⟩ : syracuseStep 4583123 = 6874685) B6874685
theorem B3055415 : Blo 2035435 3055415 := bstep (se 1 (by rfl) ⟨2291561, by rfl⟩ : syracuseStep 3055415 = 4583123) B4583123
theorem B2036943 : Blo 2035435 2036943 := bstep (se 1 (by rfl) ⟨1527707, by rfl⟩ : syracuseStep 2036943 = 3055415) B3055415
theorem B3055421 : Blo 2035435 3055421 := bbase (se 3 (by rfl) ⟨572891, by rfl⟩ : syracuseStep 3055421 = 1145783) (by norm_num)
theorem B2036947 : Blo 2035435 2036947 := bstep (se 1 (by rfl) ⟨1527710, by rfl⟩ : syracuseStep 2036947 = 3055421) B3055421
theorem B4583141 : Blo 2035435 4583141 := bbase (se 4 (by rfl) ⟨429669, by rfl⟩ : syracuseStep 4583141 = 859339) (by norm_num)
theorem B3055427 : Blo 2035435 3055427 := bstep (se 1 (by rfl) ⟨2291570, by rfl⟩ : syracuseStep 3055427 = 4583141) B4583141
theorem B2036951 : Blo 2035435 2036951 := bstep (se 1 (by rfl) ⟨1527713, by rfl⟩ : syracuseStep 2036951 = 3055427) B3055427
theorem B5156045 : Blo 2035435 5156045 := bbase (se 3 (by rfl) ⟨966758, by rfl⟩ : syracuseStep 5156045 = 1933517) (by norm_num)
theorem B3437363 : Blo 2035435 3437363 := bstep (se 1 (by rfl) ⟨2578022, by rfl⟩ : syracuseStep 3437363 = 5156045) B5156045
theorem B2291575 : Blo 2035435 2291575 := bstep (se 1 (by rfl) ⟨1718681, by rfl⟩ : syracuseStep 2291575 = 3437363) B3437363
theorem B3055433 : Blo 2035435 3055433 := bstep (se 2 (by rfl) ⟨1145787, by rfl⟩ : syracuseStep 3055433 = 2291575) B2291575
theorem B2036955 : Blo 2035435 2036955 := bstep (se 1 (by rfl) ⟨1527716, by rfl⟩ : syracuseStep 2036955 = 3055433) B3055433
theorem B2447113 : Blo 2035435 2447113 := bbase (se 2 (by rfl) ⟨917667, by rfl⟩ : syracuseStep 2447113 = 1835335) (by norm_num)
theorem B3262817 : Blo 2035435 3262817 := bstep (se 2 (by rfl) ⟨1223556, by rfl⟩ : syracuseStep 3262817 = 2447113) B2447113
theorem B2175211 : Blo 2035435 2175211 := bstep (se 1 (by rfl) ⟨1631408, by rfl⟩ : syracuseStep 2175211 = 3262817) B3262817
theorem B2900281 : Blo 2035435 2900281 := bstep (se 2 (by rfl) ⟨1087605, by rfl⟩ : syracuseStep 2900281 = 2175211) B2175211
theorem B3867041 : Blo 2035435 3867041 := bstep (se 2 (by rfl) ⟨1450140, by rfl⟩ : syracuseStep 3867041 = 2900281) B2900281
theorem B10312109 : Blo 2035435 10312109 := bstep (se 3 (by rfl) ⟨1933520, by rfl⟩ : syracuseStep 10312109 = 3867041) B3867041
theorem B6874739 : Blo 2035435 6874739 := bstep (se 1 (by rfl) ⟨5156054, by rfl⟩ : syracuseStep 6874739 = 10312109) B10312109
theorem B4583159 : Blo 2035435 4583159 := bstep (se 1 (by rfl) ⟨3437369, by rfl⟩ : syracuseStep 4583159 = 6874739) B6874739
theorem B3055439 : Blo 2035435 3055439 := bstep (se 1 (by rfl) ⟨2291579, by rfl⟩ : syracuseStep 3055439 = 4583159) B4583159
theorem B2036959 : Blo 2035435 2036959 := bstep (se 1 (by rfl) ⟨1527719, by rfl⟩ : syracuseStep 2036959 = 3055439) B3055439
theorem B3055445 : Blo 2035435 3055445 := bbase (se 9 (by rfl) ⟨8951, by rfl⟩ : syracuseStep 3055445 = 17903) (by norm_num)
theorem B2036963 : Blo 2035435 2036963 := bstep (se 1 (by rfl) ⟨1527722, by rfl⟩ : syracuseStep 2036963 = 3055445) B3055445
theorem B10595461 : Blo 2035435 10595461 := bbase (se 4 (by rfl) ⟨993324, by rfl⟩ : syracuseStep 10595461 = 1986649) (by norm_num)
theorem B14127281 : Blo 2035435 14127281 := bstep (se 2 (by rfl) ⟨5297730, by rfl⟩ : syracuseStep 14127281 = 10595461) B10595461
theorem B9418187 : Blo 2035435 9418187 := bstep (se 1 (by rfl) ⟨7063640, by rfl⟩ : syracuseStep 9418187 = 14127281) B14127281
theorem B6278791 : Blo 2035435 6278791 := bstep (se 1 (by rfl) ⟨4709093, by rfl⟩ : syracuseStep 6278791 = 9418187) B9418187
theorem B8371721 : Blo 2035435 8371721 := bstep (se 2 (by rfl) ⟨3139395, by rfl⟩ : syracuseStep 8371721 = 6278791) B6278791
theorem B22324589 : Blo 2035435 22324589 := bstep (se 3 (by rfl) ⟨4185860, by rfl⟩ : syracuseStep 22324589 = 8371721) B8371721
theorem B14883059 : Blo 2035435 14883059 := bstep (se 1 (by rfl) ⟨11162294, by rfl⟩ : syracuseStep 14883059 = 22324589) B22324589
theorem B39688157 : Blo 2035435 39688157 := bstep (se 3 (by rfl) ⟨7441529, by rfl⟩ : syracuseStep 39688157 = 14883059) B14883059
theorem B26458771 : Blo 2035435 26458771 := bstep (se 1 (by rfl) ⟨19844078, by rfl⟩ : syracuseStep 26458771 = 39688157) B39688157
theorem B35278361 : Blo 2035435 35278361 := bstep (se 2 (by rfl) ⟨13229385, by rfl⟩ : syracuseStep 35278361 = 26458771) B26458771
theorem B23518907 : Blo 2035435 23518907 := bstep (se 1 (by rfl) ⟨17639180, by rfl⟩ : syracuseStep 23518907 = 35278361) B35278361
theorem B15679271 : Blo 2035435 15679271 := bstep (se 1 (by rfl) ⟨11759453, by rfl⟩ : syracuseStep 15679271 = 23518907) B23518907
theorem B10452847 : Blo 2035435 10452847 := bstep (se 1 (by rfl) ⟨7839635, by rfl⟩ : syracuseStep 10452847 = 15679271) B15679271
theorem B13937129 : Blo 2035435 13937129 := bstep (se 2 (by rfl) ⟨5226423, by rfl⟩ : syracuseStep 13937129 = 10452847) B10452847
theorem B9291419 : Blo 2035435 9291419 := bstep (se 1 (by rfl) ⟨6968564, by rfl⟩ : syracuseStep 9291419 = 13937129) B13937129
theorem B6194279 : Blo 2035435 6194279 := bstep (se 1 (by rfl) ⟨4645709, by rfl⟩ : syracuseStep 6194279 = 9291419) B9291419
theorem B16518077 : Blo 2035435 16518077 := bstep (se 3 (by rfl) ⟨3097139, by rfl⟩ : syracuseStep 16518077 = 6194279) B6194279
theorem B11012051 : Blo 2035435 11012051 := bstep (se 1 (by rfl) ⟨8259038, by rfl⟩ : syracuseStep 11012051 = 16518077) B16518077
theorem B7341367 : Blo 2035435 7341367 := bstep (se 1 (by rfl) ⟨5506025, by rfl⟩ : syracuseStep 7341367 = 11012051) B11012051
theorem B9788489 : Blo 2035435 9788489 := bstep (se 2 (by rfl) ⟨3670683, by rfl⟩ : syracuseStep 9788489 = 7341367) B7341367
theorem B6525659 : Blo 2035435 6525659 := bstep (se 1 (by rfl) ⟨4894244, by rfl⟩ : syracuseStep 6525659 = 9788489) B9788489
theorem B4350439 : Blo 2035435 4350439 := bstep (se 1 (by rfl) ⟨3262829, by rfl⟩ : syracuseStep 4350439 = 6525659) B6525659
theorem B5800585 : Blo 2035435 5800585 := bstep (se 2 (by rfl) ⟨2175219, by rfl⟩ : syracuseStep 5800585 = 4350439) B4350439
theorem B7734113 : Blo 2035435 7734113 := bstep (se 2 (by rfl) ⟨2900292, by rfl⟩ : syracuseStep 7734113 = 5800585) B5800585
theorem B5156075 : Blo 2035435 5156075 := bstep (se 1 (by rfl) ⟨3867056, by rfl⟩ : syracuseStep 5156075 = 7734113) B7734113
theorem B3437383 : Blo 2035435 3437383 := bstep (se 1 (by rfl) ⟨2578037, by rfl⟩ : syracuseStep 3437383 = 5156075) B5156075
theorem B4583177 : Blo 2035435 4583177 := bstep (se 2 (by rfl) ⟨1718691, by rfl⟩ : syracuseStep 4583177 = 3437383) B3437383
theorem B3055451 : Blo 2035435 3055451 := bstep (se 1 (by rfl) ⟨2291588, by rfl⟩ : syracuseStep 3055451 = 4583177) B4583177
theorem B2036967 : Blo 2035435 2036967 := bstep (se 1 (by rfl) ⟨1527725, by rfl⟩ : syracuseStep 2036967 = 3055451) B3055451
theorem B2291593 : Blo 2035435 2291593 := bbase (se 2 (by rfl) ⟨859347, by rfl⟩ : syracuseStep 2291593 = 1718695) (by norm_num)
theorem B3055457 : Blo 2035435 3055457 := bstep (se 2 (by rfl) ⟨1145796, by rfl⟩ : syracuseStep 3055457 = 2291593) B2291593
theorem B2036971 : Blo 2035435 2036971 := bstep (se 1 (by rfl) ⟨1527728, by rfl⟩ : syracuseStep 2036971 = 3055457) B3055457
theorem B79376597 : Blo 2035435 79376597 := bbase (se 7 (by rfl) ⟨930194, by rfl⟩ : syracuseStep 79376597 = 1860389) (by norm_num)
theorem B52917731 : Blo 2035435 52917731 := bstep (se 1 (by rfl) ⟨39688298, by rfl⟩ : syracuseStep 52917731 = 79376597) B79376597
theorem B35278487 : Blo 2035435 35278487 := bstep (se 1 (by rfl) ⟨26458865, by rfl⟩ : syracuseStep 35278487 = 52917731) B52917731
theorem B23518991 : Blo 2035435 23518991 := bstep (se 1 (by rfl) ⟨17639243, by rfl⟩ : syracuseStep 23518991 = 35278487) B35278487
theorem B15679327 : Blo 2035435 15679327 := bstep (se 1 (by rfl) ⟨11759495, by rfl⟩ : syracuseStep 15679327 = 23518991) B23518991
theorem B20905769 : Blo 2035435 20905769 := bstep (se 2 (by rfl) ⟨7839663, by rfl⟩ : syracuseStep 20905769 = 15679327) B15679327
theorem B13937179 : Blo 2035435 13937179 := bstep (se 1 (by rfl) ⟨10452884, by rfl⟩ : syracuseStep 13937179 = 20905769) B20905769
theorem B18582905 : Blo 2035435 18582905 := bstep (se 2 (by rfl) ⟨6968589, by rfl⟩ : syracuseStep 18582905 = 13937179) B13937179
theorem B49554413 : Blo 2035435 49554413 := bstep (se 3 (by rfl) ⟨9291452, by rfl⟩ : syracuseStep 49554413 = 18582905) B18582905
theorem B33036275 : Blo 2035435 33036275 := bstep (se 1 (by rfl) ⟨24777206, by rfl⟩ : syracuseStep 33036275 = 49554413) B49554413
theorem B88096733 : Blo 2035435 88096733 := bstep (se 3 (by rfl) ⟨16518137, by rfl⟩ : syracuseStep 88096733 = 33036275) B33036275
theorem B58731155 : Blo 2035435 58731155 := bstep (se 1 (by rfl) ⟨44048366, by rfl⟩ : syracuseStep 58731155 = 88096733) B88096733
theorem B39154103 : Blo 2035435 39154103 := bstep (se 1 (by rfl) ⟨29365577, by rfl⟩ : syracuseStep 39154103 = 58731155) B58731155
theorem B26102735 : Blo 2035435 26102735 := bstep (se 1 (by rfl) ⟨19577051, by rfl⟩ : syracuseStep 26102735 = 39154103) B39154103
theorem B17401823 : Blo 2035435 17401823 := bstep (se 1 (by rfl) ⟨13051367, by rfl⟩ : syracuseStep 17401823 = 26102735) B26102735
theorem B11601215 : Blo 2035435 11601215 := bstep (se 1 (by rfl) ⟨8700911, by rfl⟩ : syracuseStep 11601215 = 17401823) B17401823
theorem B7734143 : Blo 2035435 7734143 := bstep (se 1 (by rfl) ⟨5800607, by rfl⟩ : syracuseStep 7734143 = 11601215) B11601215
theorem B5156095 : Blo 2035435 5156095 := bstep (se 1 (by rfl) ⟨3867071, by rfl⟩ : syracuseStep 5156095 = 7734143) B7734143
theorem B6874793 : Blo 2035435 6874793 := bstep (se 2 (by rfl) ⟨2578047, by rfl⟩ : syracuseStep 6874793 = 5156095) B5156095
theorem B4583195 : Blo 2035435 4583195 := bstep (se 1 (by rfl) ⟨3437396, by rfl⟩ : syracuseStep 4583195 = 6874793) B6874793
theorem B3055463 : Blo 2035435 3055463 := bstep (se 1 (by rfl) ⟨2291597, by rfl⟩ : syracuseStep 3055463 = 4583195) B4583195
theorem B2036975 : Blo 2035435 2036975 := bstep (se 1 (by rfl) ⟨1527731, by rfl⟩ : syracuseStep 2036975 = 3055463) B3055463
theorem B3055469 : Blo 2035435 3055469 := bbase (se 3 (by rfl) ⟨572900, by rfl⟩ : syracuseStep 3055469 = 1145801) (by norm_num)
theorem B2036979 : Blo 2035435 2036979 := bstep (se 1 (by rfl) ⟨1527734, by rfl⟩ : syracuseStep 2036979 = 3055469) B3055469
theorem B4583213 : Blo 2035435 4583213 := bbase (se 3 (by rfl) ⟨859352, by rfl⟩ : syracuseStep 4583213 = 1718705) (by norm_num)
theorem B3055475 : Blo 2035435 3055475 := bstep (se 1 (by rfl) ⟨2291606, by rfl⟩ : syracuseStep 3055475 = 4583213) B4583213
theorem B2036983 : Blo 2035435 2036983 := bstep (se 1 (by rfl) ⟨1527737, by rfl⟩ : syracuseStep 2036983 = 3055475) B3055475
theorem B8700965 : Blo 2035435 8700965 := bbase (se 4 (by rfl) ⟨815715, by rfl⟩ : syracuseStep 8700965 = 1631431) (by norm_num)
theorem B5800643 : Blo 2035435 5800643 := bstep (se 1 (by rfl) ⟨4350482, by rfl⟩ : syracuseStep 5800643 = 8700965) B8700965
theorem B3867095 : Blo 2035435 3867095 := bstep (se 1 (by rfl) ⟨2900321, by rfl⟩ : syracuseStep 3867095 = 5800643) B5800643
theorem B2578063 : Blo 2035435 2578063 := bstep (se 1 (by rfl) ⟨1933547, by rfl⟩ : syracuseStep 2578063 = 3867095) B3867095
theorem B3437417 : Blo 2035435 3437417 := bstep (se 2 (by rfl) ⟨1289031, by rfl⟩ : syracuseStep 3437417 = 2578063) B2578063
theorem B2291611 : Blo 2035435 2291611 := bstep (se 1 (by rfl) ⟨1718708, by rfl⟩ : syracuseStep 2291611 = 3437417) B3437417
theorem B3055481 : Blo 2035435 3055481 := bstep (se 2 (by rfl) ⟨1145805, by rfl⟩ : syracuseStep 3055481 = 2291611) B2291611
theorem B2036987 : Blo 2035435 2036987 := bstep (se 1 (by rfl) ⟨1527740, by rfl⟩ : syracuseStep 2036987 = 3055481) B3055481
theorem B4894301 : Blo 2035435 4894301 := bbase (se 3 (by rfl) ⟨917681, by rfl⟩ : syracuseStep 4894301 = 1835363) (by norm_num)
theorem B13051469 : Blo 2035435 13051469 := bstep (se 3 (by rfl) ⟨2447150, by rfl⟩ : syracuseStep 13051469 = 4894301) B4894301
theorem B34803917 : Blo 2035435 34803917 := bstep (se 3 (by rfl) ⟨6525734, by rfl⟩ : syracuseStep 34803917 = 13051469) B13051469
theorem B23202611 : Blo 2035435 23202611 := bstep (se 1 (by rfl) ⟨17401958, by rfl⟩ : syracuseStep 23202611 = 34803917) B34803917
theorem B15468407 : Blo 2035435 15468407 := bstep (se 1 (by rfl) ⟨11601305, by rfl⟩ : syracuseStep 15468407 = 23202611) B23202611
theorem B10312271 : Blo 2035435 10312271 := bstep (se 1 (by rfl) ⟨7734203, by rfl⟩ : syracuseStep 10312271 = 15468407) B15468407
theorem B6874847 : Blo 2035435 6874847 := bstep (se 1 (by rfl) ⟨5156135, by rfl⟩ : syracuseStep 6874847 = 10312271) B10312271
theorem B4583231 : Blo 2035435 4583231 := bstep (se 1 (by rfl) ⟨3437423, by rfl⟩ : syracuseStep 4583231 = 6874847) B6874847
theorem B3055487 : Blo 2035435 3055487 := bstep (se 1 (by rfl) ⟨2291615, by rfl⟩ : syracuseStep 3055487 = 4583231) B4583231
theorem B2036991 : Blo 2035435 2036991 := bstep (se 1 (by rfl) ⟨1527743, by rfl⟩ : syracuseStep 2036991 = 3055487) B3055487
theorem B3055493 : Blo 2035435 3055493 := bbase (se 4 (by rfl) ⟨286452, by rfl⟩ : syracuseStep 3055493 = 572905) (by norm_num)
theorem B2036995 : Blo 2035435 2036995 := bstep (se 1 (by rfl) ⟨1527746, by rfl⟩ : syracuseStep 2036995 = 3055493) B3055493
theorem B3437437 : Blo 2035435 3437437 := bbase (se 3 (by rfl) ⟨644519, by rfl⟩ : syracuseStep 3437437 = 1289039) (by norm_num)
theorem B4583249 : Blo 2035435 4583249 := bstep (se 2 (by rfl) ⟨1718718, by rfl⟩ : syracuseStep 4583249 = 3437437) B3437437
theorem B3055499 : Blo 2035435 3055499 := bstep (se 1 (by rfl) ⟨2291624, by rfl⟩ : syracuseStep 3055499 = 4583249) B4583249
theorem B2036999 : Blo 2035435 2036999 := bstep (se 1 (by rfl) ⟨1527749, by rfl⟩ : syracuseStep 2036999 = 3055499) B3055499
theorem B2291629 : Blo 2035435 2291629 := bbase (se 3 (by rfl) ⟨429680, by rfl⟩ : syracuseStep 2291629 = 859361) (by norm_num)
theorem B3055505 : Blo 2035435 3055505 := bstep (se 2 (by rfl) ⟨1145814, by rfl⟩ : syracuseStep 3055505 = 2291629) B2291629
theorem B2037003 : Blo 2035435 2037003 := bstep (se 1 (by rfl) ⟨1527752, by rfl⟩ : syracuseStep 2037003 = 3055505) B3055505
theorem B6874901 : Blo 2035435 6874901 := bbase (se 6 (by rfl) ⟨161130, by rfl⟩ : syracuseStep 6874901 = 322261) (by norm_num)
theorem B4583267 : Blo 2035435 4583267 := bstep (se 1 (by rfl) ⟨3437450, by rfl⟩ : syracuseStep 4583267 = 6874901) B6874901
theorem B3055511 : Blo 2035435 3055511 := bstep (se 1 (by rfl) ⟨2291633, by rfl⟩ : syracuseStep 3055511 = 4583267) B4583267
theorem B2037007 : Blo 2035435 2037007 := bstep (se 1 (by rfl) ⟨1527755, by rfl⟩ : syracuseStep 2037007 = 3055511) B3055511
theorem B3055517 : Blo 2035435 3055517 := bbase (se 3 (by rfl) ⟨572909, by rfl⟩ : syracuseStep 3055517 = 1145819) (by norm_num)
theorem B2037011 : Blo 2035435 2037011 := bstep (se 1 (by rfl) ⟨1527758, by rfl⟩ : syracuseStep 2037011 = 3055517) B3055517
theorem B4583285 : Blo 2035435 4583285 := bbase (se 5 (by rfl) ⟨214841, by rfl⟩ : syracuseStep 4583285 = 429683) (by norm_num)
theorem B3055523 : Blo 2035435 3055523 := bstep (se 1 (by rfl) ⟨2291642, by rfl⟩ : syracuseStep 3055523 = 4583285) B4583285
theorem B2037015 : Blo 2035435 2037015 := bstep (se 1 (by rfl) ⟨1527761, by rfl⟩ : syracuseStep 2037015 = 3055523) B3055523
theorem B4645829 : Blo 2035435 4645829 := bbase (se 4 (by rfl) ⟨435546, by rfl⟩ : syracuseStep 4645829 = 871093) (by norm_num)
theorem B3097219 : Blo 2035435 3097219 := bstep (se 1 (by rfl) ⟨2322914, by rfl⟩ : syracuseStep 3097219 = 4645829) B4645829
theorem B4129625 : Blo 2035435 4129625 := bstep (se 2 (by rfl) ⟨1548609, by rfl⟩ : syracuseStep 4129625 = 3097219) B3097219
theorem B2753083 : Blo 2035435 2753083 := bstep (se 1 (by rfl) ⟨2064812, by rfl⟩ : syracuseStep 2753083 = 4129625) B4129625
theorem B3670777 : Blo 2035435 3670777 := bstep (se 2 (by rfl) ⟨1376541, by rfl⟩ : syracuseStep 3670777 = 2753083) B2753083
theorem B19577477 : Blo 2035435 19577477 := bstep (se 4 (by rfl) ⟨1835388, by rfl⟩ : syracuseStep 19577477 = 3670777) B3670777
theorem B13051651 : Blo 2035435 13051651 := bstep (se 1 (by rfl) ⟨9788738, by rfl⟩ : syracuseStep 13051651 = 19577477) B19577477
theorem B17402201 : Blo 2035435 17402201 := bstep (se 2 (by rfl) ⟨6525825, by rfl⟩ : syracuseStep 17402201 = 13051651) B13051651
theorem B11601467 : Blo 2035435 11601467 := bstep (se 1 (by rfl) ⟨8701100, by rfl⟩ : syracuseStep 11601467 = 17402201) B17402201
theorem B7734311 : Blo 2035435 7734311 := bstep (se 1 (by rfl) ⟨5800733, by rfl⟩ : syracuseStep 7734311 = 11601467) B11601467
theorem B5156207 : Blo 2035435 5156207 := bstep (se 1 (by rfl) ⟨3867155, by rfl⟩ : syracuseStep 5156207 = 7734311) B7734311
theorem B3437471 : Blo 2035435 3437471 := bstep (se 1 (by rfl) ⟨2578103, by rfl⟩ : syracuseStep 3437471 = 5156207) B5156207
theorem B2291647 : Blo 2035435 2291647 := bstep (se 1 (by rfl) ⟨1718735, by rfl⟩ : syracuseStep 2291647 = 3437471) B3437471
theorem B3055529 : Blo 2035435 3055529 := bstep (se 2 (by rfl) ⟨1145823, by rfl⟩ : syracuseStep 3055529 = 2291647) B2291647
theorem B2037019 : Blo 2035435 2037019 := bstep (se 1 (by rfl) ⟨1527764, by rfl⟩ : syracuseStep 2037019 = 3055529) B3055529
theorem B7734325 : Blo 2035435 7734325 := bbase (se 5 (by rfl) ⟨362546, by rfl⟩ : syracuseStep 7734325 = 725093) (by norm_num)
theorem B10312433 : Blo 2035435 10312433 := bstep (se 2 (by rfl) ⟨3867162, by rfl⟩ : syracuseStep 10312433 = 7734325) B7734325
theorem B6874955 : Blo 2035435 6874955 := bstep (se 1 (by rfl) ⟨5156216, by rfl⟩ : syracuseStep 6874955 = 10312433) B10312433
theorem B4583303 : Blo 2035435 4583303 := bstep (se 1 (by rfl) ⟨3437477, by rfl⟩ : syracuseStep 4583303 = 6874955) B6874955
theorem B3055535 : Blo 2035435 3055535 := bstep (se 1 (by rfl) ⟨2291651, by rfl⟩ : syracuseStep 3055535 = 4583303) B4583303
theorem B2037023 : Blo 2035435 2037023 := bstep (se 1 (by rfl) ⟨1527767, by rfl⟩ : syracuseStep 2037023 = 3055535) B3055535
theorem B3055541 : Blo 2035435 3055541 := bbase (se 5 (by rfl) ⟨143228, by rfl⟩ : syracuseStep 3055541 = 286457) (by norm_num)
theorem B2037027 : Blo 2035435 2037027 := bstep (se 1 (by rfl) ⟨1527770, by rfl⟩ : syracuseStep 2037027 = 3055541) B3055541
theorem B5156237 : Blo 2035435 5156237 := bbase (se 3 (by rfl) ⟨966794, by rfl⟩ : syracuseStep 5156237 = 1933589) (by norm_num)
theorem B3437491 : Blo 2035435 3437491 := bstep (se 1 (by rfl) ⟨2578118, by rfl⟩ : syracuseStep 3437491 = 5156237) B5156237
theorem B4583321 : Blo 2035435 4583321 := bstep (se 2 (by rfl) ⟨1718745, by rfl⟩ : syracuseStep 4583321 = 3437491) B3437491
theorem B3055547 : Blo 2035435 3055547 := bstep (se 1 (by rfl) ⟨2291660, by rfl⟩ : syracuseStep 3055547 = 4583321) B4583321
theorem B2037031 : Blo 2035435 2037031 := bstep (se 1 (by rfl) ⟨1527773, by rfl⟩ : syracuseStep 2037031 = 3055547) B3055547
theorem B2291665 : Blo 2035435 2291665 := bbase (se 2 (by rfl) ⟨859374, by rfl⟩ : syracuseStep 2291665 = 1718749) (by norm_num)
theorem B3055553 : Blo 2035435 3055553 := bstep (se 2 (by rfl) ⟨1145832, by rfl⟩ : syracuseStep 3055553 = 2291665) B2291665
theorem B2037035 : Blo 2035435 2037035 := bstep (se 1 (by rfl) ⟨1527776, by rfl⟩ : syracuseStep 2037035 = 3055553) B3055553
theorem B2447209 : Blo 2035435 2447209 := bbase (se 2 (by rfl) ⟨917703, by rfl⟩ : syracuseStep 2447209 = 1835407) (by norm_num)
theorem B3262945 : Blo 2035435 3262945 := bstep (se 2 (by rfl) ⟨1223604, by rfl⟩ : syracuseStep 3262945 = 2447209) B2447209
theorem B4350593 : Blo 2035435 4350593 := bstep (se 2 (by rfl) ⟨1631472, by rfl⟩ : syracuseStep 4350593 = 3262945) B3262945
theorem B2900395 : Blo 2035435 2900395 := bstep (se 1 (by rfl) ⟨2175296, by rfl⟩ : syracuseStep 2900395 = 4350593) B4350593
theorem B3867193 : Blo 2035435 3867193 := bstep (se 2 (by rfl) ⟨1450197, by rfl⟩ : syracuseStep 3867193 = 2900395) B2900395
theorem B5156257 : Blo 2035435 5156257 := bstep (se 2 (by rfl) ⟨1933596, by rfl⟩ : syracuseStep 5156257 = 3867193) B3867193
theorem B6875009 : Blo 2035435 6875009 := bstep (se 2 (by rfl) ⟨2578128, by rfl⟩ : syracuseStep 6875009 = 5156257) B5156257
theorem B4583339 : Blo 2035435 4583339 := bstep (se 1 (by rfl) ⟨3437504, by rfl⟩ : syracuseStep 4583339 = 6875009) B6875009
theorem B3055559 : Blo 2035435 3055559 := bstep (se 1 (by rfl) ⟨2291669, by rfl⟩ : syracuseStep 3055559 = 4583339) B4583339
theorem B2037039 : Blo 2035435 2037039 := bstep (se 1 (by rfl) ⟨1527779, by rfl⟩ : syracuseStep 2037039 = 3055559) B3055559
theorem B3055565 : Blo 2035435 3055565 := bbase (se 3 (by rfl) ⟨572918, by rfl⟩ : syracuseStep 3055565 = 1145837) (by norm_num)
theorem B2037043 : Blo 2035435 2037043 := bstep (se 1 (by rfl) ⟨1527782, by rfl⟩ : syracuseStep 2037043 = 3055565) B3055565
theorem B4583357 : Blo 2035435 4583357 := bbase (se 3 (by rfl) ⟨859379, by rfl⟩ : syracuseStep 4583357 = 1718759) (by norm_num)
theorem B3055571 : Blo 2035435 3055571 := bstep (se 1 (by rfl) ⟨2291678, by rfl⟩ : syracuseStep 3055571 = 4583357) B4583357
theorem B2037047 : Blo 2035435 2037047 := bstep (se 1 (by rfl) ⟨1527785, by rfl⟩ : syracuseStep 2037047 = 3055571) B3055571
theorem B3437525 : Blo 2035435 3437525 := bbase (se 7 (by rfl) ⟨40283, by rfl⟩ : syracuseStep 3437525 = 80567) (by norm_num)
theorem B2291683 : Blo 2035435 2291683 := bstep (se 1 (by rfl) ⟨1718762, by rfl⟩ : syracuseStep 2291683 = 3437525) B3437525
theorem B3055577 : Blo 2035435 3055577 := bstep (se 2 (by rfl) ⟨1145841, by rfl⟩ : syracuseStep 3055577 = 2291683) B2291683
theorem B2037051 : Blo 2035435 2037051 := bstep (se 1 (by rfl) ⟨1527788, by rfl⟩ : syracuseStep 2037051 = 3055577) B3055577
theorem B8701253 : Blo 2035435 8701253 := bbase (se 4 (by rfl) ⟨815742, by rfl⟩ : syracuseStep 8701253 = 1631485) (by norm_num)
theorem B5800835 : Blo 2035435 5800835 := bstep (se 1 (by rfl) ⟨4350626, by rfl⟩ : syracuseStep 5800835 = 8701253) B8701253
theorem B15468893 : Blo 2035435 15468893 := bstep (se 3 (by rfl) ⟨2900417, by rfl⟩ : syracuseStep 15468893 = 5800835) B5800835
theorem B10312595 : Blo 2035435 10312595 := bstep (se 1 (by rfl) ⟨7734446, by rfl⟩ : syracuseStep 10312595 = 15468893) B15468893
theorem B6875063 : Blo 2035435 6875063 := bstep (se 1 (by rfl) ⟨5156297, by rfl⟩ : syracuseStep 6875063 = 10312595) B10312595
theorem B4583375 : Blo 2035435 4583375 := bstep (se 1 (by rfl) ⟨3437531, by rfl⟩ : syracuseStep 4583375 = 6875063) B6875063
theorem B3055583 : Blo 2035435 3055583 := bstep (se 1 (by rfl) ⟨2291687, by rfl⟩ : syracuseStep 3055583 = 4583375) B4583375
theorem B2037055 : Blo 2035435 2037055 := bstep (se 1 (by rfl) ⟨1527791, by rfl⟩ : syracuseStep 2037055 = 3055583) B3055583
theorem B3055589 : Blo 2035435 3055589 := bbase (se 4 (by rfl) ⟨286461, by rfl⟩ : syracuseStep 3055589 = 572923) (by norm_num)
theorem B2037059 : Blo 2035435 2037059 := bstep (se 1 (by rfl) ⟨1527794, by rfl⟩ : syracuseStep 2037059 = 3055589) B3055589
theorem B2064857 : Blo 2035435 2064857 := bbase (se 2 (by rfl) ⟨774321, by rfl⟩ : syracuseStep 2064857 = 1548643) (by norm_num)
theorem B22025141 : Blo 2035435 22025141 := bstep (se 5 (by rfl) ⟨1032428, by rfl⟩ : syracuseStep 22025141 = 2064857) B2064857
theorem B14683427 : Blo 2035435 14683427 := bstep (se 1 (by rfl) ⟨11012570, by rfl⟩ : syracuseStep 14683427 = 22025141) B22025141
theorem B9788951 : Blo 2035435 9788951 := bstep (se 1 (by rfl) ⟨7341713, by rfl⟩ : syracuseStep 9788951 = 14683427) B14683427
theorem B6525967 : Blo 2035435 6525967 := bstep (se 1 (by rfl) ⟨4894475, by rfl⟩ : syracuseStep 6525967 = 9788951) B9788951
theorem B8701289 : Blo 2035435 8701289 := bstep (se 2 (by rfl) ⟨3262983, by rfl⟩ : syracuseStep 8701289 = 6525967) B6525967
theorem B5800859 : Blo 2035435 5800859 := bstep (se 1 (by rfl) ⟨4350644, by rfl⟩ : syracuseStep 5800859 = 8701289) B8701289
theorem B3867239 : Blo 2035435 3867239 := bstep (se 1 (by rfl) ⟨2900429, by rfl⟩ : syracuseStep 3867239 = 5800859) B5800859
theorem B2578159 : Blo 2035435 2578159 := bstep (se 1 (by rfl) ⟨1933619, by rfl⟩ : syracuseStep 2578159 = 3867239) B3867239
theorem B3437545 : Blo 2035435 3437545 := bstep (se 2 (by rfl) ⟨1289079, by rfl⟩ : syracuseStep 3437545 = 2578159) B2578159
theorem B4583393 : Blo 2035435 4583393 := bstep (se 2 (by rfl) ⟨1718772, by rfl⟩ : syracuseStep 4583393 = 3437545) B3437545
theorem B3055595 : Blo 2035435 3055595 := bstep (se 1 (by rfl) ⟨2291696, by rfl⟩ : syracuseStep 3055595 = 4583393) B4583393
theorem B2037063 : Blo 2035435 2037063 := bstep (se 1 (by rfl) ⟨1527797, by rfl⟩ : syracuseStep 2037063 = 3055595) B3055595
theorem B2291701 : Blo 2035435 2291701 := bbase (se 5 (by rfl) ⟨107423, by rfl⟩ : syracuseStep 2291701 = 214847) (by norm_num)
theorem B3055601 : Blo 2035435 3055601 := bstep (se 2 (by rfl) ⟨1145850, by rfl⟩ : syracuseStep 3055601 = 2291701) B2291701
theorem B2037067 : Blo 2035435 2037067 := bstep (se 1 (by rfl) ⟨1527800, by rfl⟩ : syracuseStep 2037067 = 3055601) B3055601
theorem B2578169 : Blo 2035435 2578169 := bbase (se 2 (by rfl) ⟨966813, by rfl⟩ : syracuseStep 2578169 = 1933627) (by norm_num)
theorem B6875117 : Blo 2035435 6875117 := bstep (se 3 (by rfl) ⟨1289084, by rfl⟩ : syracuseStep 6875117 = 2578169) B2578169
theorem B4583411 : Blo 2035435 4583411 := bstep (se 1 (by rfl) ⟨3437558, by rfl⟩ : syracuseStep 4583411 = 6875117) B6875117
theorem B3055607 : Blo 2035435 3055607 := bstep (se 1 (by rfl) ⟨2291705, by rfl⟩ : syracuseStep 3055607 = 4583411) B4583411
theorem B2037071 : Blo 2035435 2037071 := bstep (se 1 (by rfl) ⟨1527803, by rfl⟩ : syracuseStep 2037071 = 3055607) B3055607
theorem B3055613 : Blo 2035435 3055613 := bbase (se 3 (by rfl) ⟨572927, by rfl⟩ : syracuseStep 3055613 = 1145855) (by norm_num)
theorem B2037075 : Blo 2035435 2037075 := bstep (se 1 (by rfl) ⟨1527806, by rfl⟩ : syracuseStep 2037075 = 3055613) B3055613
theorem B4583429 : Blo 2035435 4583429 := bbase (se 4 (by rfl) ⟨429696, by rfl⟩ : syracuseStep 4583429 = 859393) (by norm_num)
theorem B3055619 : Blo 2035435 3055619 := bstep (se 1 (by rfl) ⟨2291714, by rfl⟩ : syracuseStep 3055619 = 4583429) B4583429
theorem B2037079 : Blo 2035435 2037079 := bstep (se 1 (by rfl) ⟨1527809, by rfl⟩ : syracuseStep 2037079 = 3055619) B3055619
theorem B3867277 : Blo 2035435 3867277 := bbase (se 3 (by rfl) ⟨725114, by rfl⟩ : syracuseStep 3867277 = 1450229) (by norm_num)
theorem B5156369 : Blo 2035435 5156369 := bstep (se 2 (by rfl) ⟨1933638, by rfl⟩ : syracuseStep 5156369 = 3867277) B3867277
theorem B3437579 : Blo 2035435 3437579 := bstep (se 1 (by rfl) ⟨2578184, by rfl⟩ : syracuseStep 3437579 = 5156369) B5156369
theorem B2291719 : Blo 2035435 2291719 := bstep (se 1 (by rfl) ⟨1718789, by rfl⟩ : syracuseStep 2291719 = 3437579) B3437579
theorem B3055625 : Blo 2035435 3055625 := bstep (se 2 (by rfl) ⟨1145859, by rfl⟩ : syracuseStep 3055625 = 2291719) B2291719
theorem B2037083 : Blo 2035435 2037083 := bstep (se 1 (by rfl) ⟨1527812, by rfl⟩ : syracuseStep 2037083 = 3055625) B3055625
theorem B10312757 : Blo 2035435 10312757 := bbase (se 5 (by rfl) ⟨483410, by rfl⟩ : syracuseStep 10312757 = 966821) (by norm_num)
theorem B6875171 : Blo 2035435 6875171 := bstep (se 1 (by rfl) ⟨5156378, by rfl⟩ : syracuseStep 6875171 = 10312757) B10312757
theorem B4583447 : Blo 2035435 4583447 := bstep (se 1 (by rfl) ⟨3437585, by rfl⟩ : syracuseStep 4583447 = 6875171) B6875171
theorem B3055631 : Blo 2035435 3055631 := bstep (se 1 (by rfl) ⟨2291723, by rfl⟩ : syracuseStep 3055631 = 4583447) B4583447
theorem B2037087 : Blo 2035435 2037087 := bstep (se 1 (by rfl) ⟨1527815, by rfl⟩ : syracuseStep 2037087 = 3055631) B3055631
theorem B3055637 : Blo 2035435 3055637 := bbase (se 6 (by rfl) ⟨71616, by rfl⟩ : syracuseStep 3055637 = 143233) (by norm_num)
theorem B2037091 : Blo 2035435 2037091 := bstep (se 1 (by rfl) ⟨1527818, by rfl⟩ : syracuseStep 2037091 = 3055637) B3055637
theorem B4709389 : Blo 2035435 4709389 := bbase (se 3 (by rfl) ⟨883010, by rfl⟩ : syracuseStep 4709389 = 1766021) (by norm_num)
theorem B6279185 : Blo 2035435 6279185 := bstep (se 2 (by rfl) ⟨2354694, by rfl⟩ : syracuseStep 6279185 = 4709389) B4709389
theorem B4186123 : Blo 2035435 4186123 := bstep (se 1 (by rfl) ⟨3139592, by rfl⟩ : syracuseStep 4186123 = 6279185) B6279185
theorem B89303957 : Blo 2035435 89303957 := bstep (se 6 (by rfl) ⟨2093061, by rfl⟩ : syracuseStep 89303957 = 4186123) B4186123
theorem B59535971 : Blo 2035435 59535971 := bstep (se 1 (by rfl) ⟨44651978, by rfl⟩ : syracuseStep 59535971 = 89303957) B89303957
theorem B39690647 : Blo 2035435 39690647 := bstep (se 1 (by rfl) ⟨29767985, by rfl⟩ : syracuseStep 39690647 = 59535971) B59535971
theorem B26460431 : Blo 2035435 26460431 := bstep (se 1 (by rfl) ⟨19845323, by rfl⟩ : syracuseStep 26460431 = 39690647) B39690647
theorem B17640287 : Blo 2035435 17640287 := bstep (se 1 (by rfl) ⟨13230215, by rfl⟩ : syracuseStep 17640287 = 26460431) B26460431
theorem B11760191 : Blo 2035435 11760191 := bstep (se 1 (by rfl) ⟨8820143, by rfl⟩ : syracuseStep 11760191 = 17640287) B17640287
theorem B7840127 : Blo 2035435 7840127 := bstep (se 1 (by rfl) ⟨5880095, by rfl⟩ : syracuseStep 7840127 = 11760191) B11760191
theorem B5226751 : Blo 2035435 5226751 := bstep (se 1 (by rfl) ⟨3920063, by rfl⟩ : syracuseStep 5226751 = 7840127) B7840127
theorem B6969001 : Blo 2035435 6969001 := bstep (se 2 (by rfl) ⟨2613375, by rfl⟩ : syracuseStep 6969001 = 5226751) B5226751
theorem B9292001 : Blo 2035435 9292001 := bstep (se 2 (by rfl) ⟨3484500, by rfl⟩ : syracuseStep 9292001 = 6969001) B6969001
theorem B24778669 : Blo 2035435 24778669 := bstep (se 3 (by rfl) ⟨4646000, by rfl⟩ : syracuseStep 24778669 = 9292001) B9292001
theorem B33038225 : Blo 2035435 33038225 := bstep (se 2 (by rfl) ⟨12389334, by rfl⟩ : syracuseStep 33038225 = 24778669) B24778669
theorem B22025483 : Blo 2035435 22025483 := bstep (se 1 (by rfl) ⟨16519112, by rfl⟩ : syracuseStep 22025483 = 33038225) B33038225
theorem B14683655 : Blo 2035435 14683655 := bstep (se 1 (by rfl) ⟨11012741, by rfl⟩ : syracuseStep 14683655 = 22025483) B22025483
theorem B9789103 : Blo 2035435 9789103 := bstep (se 1 (by rfl) ⟨7341827, by rfl⟩ : syracuseStep 9789103 = 14683655) B14683655
theorem B13052137 : Blo 2035435 13052137 := bstep (se 2 (by rfl) ⟨4894551, by rfl⟩ : syracuseStep 13052137 = 9789103) B9789103
theorem B17402849 : Blo 2035435 17402849 := bstep (se 2 (by rfl) ⟨6526068, by rfl⟩ : syracuseStep 17402849 = 13052137) B13052137
theorem B11601899 : Blo 2035435 11601899 := bstep (se 1 (by rfl) ⟨8701424, by rfl⟩ : syracuseStep 11601899 = 17402849) B17402849
theorem B7734599 : Blo 2035435 7734599 := bstep (se 1 (by rfl) ⟨5800949, by rfl⟩ : syracuseStep 7734599 = 11601899) B11601899
theorem B5156399 : Blo 2035435 5156399 := bstep (se 1 (by rfl) ⟨3867299, by rfl⟩ : syracuseStep 5156399 = 7734599) B7734599
theorem B3437599 : Blo 2035435 3437599 := bstep (se 1 (by rfl) ⟨2578199, by rfl⟩ : syracuseStep 3437599 = 5156399) B5156399
theorem B4583465 : Blo 2035435 4583465 := bstep (se 2 (by rfl) ⟨1718799, by rfl⟩ : syracuseStep 4583465 = 3437599) B3437599
theorem B3055643 : Blo 2035435 3055643 := bstep (se 1 (by rfl) ⟨2291732, by rfl⟩ : syracuseStep 3055643 = 4583465) B4583465
theorem B2037095 : Blo 2035435 2037095 := bstep (se 1 (by rfl) ⟨1527821, by rfl⟩ : syracuseStep 2037095 = 3055643) B3055643
theorem B2291737 : Blo 2035435 2291737 := bbase (se 2 (by rfl) ⟨859401, by rfl⟩ : syracuseStep 2291737 = 1718803) (by norm_num)
theorem B3055649 : Blo 2035435 3055649 := bstep (se 2 (by rfl) ⟨1145868, by rfl⟩ : syracuseStep 3055649 = 2291737) B2291737
theorem B2037099 : Blo 2035435 2037099 := bstep (se 1 (by rfl) ⟨1527824, by rfl⟩ : syracuseStep 2037099 = 3055649) B3055649
theorem B7734629 : Blo 2035435 7734629 := bbase (se 4 (by rfl) ⟨725121, by rfl⟩ : syracuseStep 7734629 = 1450243) (by norm_num)
theorem B5156419 : Blo 2035435 5156419 := bstep (se 1 (by rfl) ⟨3867314, by rfl⟩ : syracuseStep 5156419 = 7734629) B7734629
theorem B6875225 : Blo 2035435 6875225 := bstep (se 2 (by rfl) ⟨2578209, by rfl⟩ : syracuseStep 6875225 = 5156419) B5156419
theorem B4583483 : Blo 2035435 4583483 := bstep (se 1 (by rfl) ⟨3437612, by rfl⟩ : syracuseStep 4583483 = 6875225) B6875225
theorem B3055655 : Blo 2035435 3055655 := bstep (se 1 (by rfl) ⟨2291741, by rfl⟩ : syracuseStep 3055655 = 4583483) B4583483
theorem B2037103 : Blo 2035435 2037103 := bstep (se 1 (by rfl) ⟨1527827, by rfl⟩ : syracuseStep 2037103 = 3055655) B3055655
theorem B3055661 : Blo 2035435 3055661 := bbase (se 3 (by rfl) ⟨572936, by rfl⟩ : syracuseStep 3055661 = 1145873) (by norm_num)
theorem B2037107 : Blo 2035435 2037107 := bstep (se 1 (by rfl) ⟨1527830, by rfl⟩ : syracuseStep 2037107 = 3055661) B3055661
theorem B4583501 : Blo 2035435 4583501 := bbase (se 3 (by rfl) ⟨859406, by rfl⟩ : syracuseStep 4583501 = 1718813) (by norm_num)
theorem B3055667 : Blo 2035435 3055667 := bstep (se 1 (by rfl) ⟨2291750, by rfl⟩ : syracuseStep 3055667 = 4583501) B4583501
theorem B2037111 : Blo 2035435 2037111 := bstep (se 1 (by rfl) ⟨1527833, by rfl⟩ : syracuseStep 2037111 = 3055667) B3055667
theorem B2578225 : Blo 2035435 2578225 := bbase (se 2 (by rfl) ⟨966834, by rfl⟩ : syracuseStep 2578225 = 1933669) (by norm_num)
theorem B3437633 : Blo 2035435 3437633 := bstep (se 2 (by rfl) ⟨1289112, by rfl⟩ : syracuseStep 3437633 = 2578225) B2578225
theorem B2291755 : Blo 2035435 2291755 := bstep (se 1 (by rfl) ⟨1718816, by rfl⟩ : syracuseStep 2291755 = 3437633) B3437633
theorem B3055673 : Blo 2035435 3055673 := bstep (se 2 (by rfl) ⟨1145877, by rfl⟩ : syracuseStep 3055673 = 2291755) B2291755
theorem B2037115 : Blo 2035435 2037115 := bstep (se 1 (by rfl) ⟨1527836, by rfl⟩ : syracuseStep 2037115 = 3055673) B3055673
theorem B3670957 : Blo 2035435 3670957 := bbase (se 3 (by rfl) ⟨688304, by rfl⟩ : syracuseStep 3670957 = 1376609) (by norm_num)
theorem B4894609 : Blo 2035435 4894609 := bstep (se 2 (by rfl) ⟨1835478, by rfl⟩ : syracuseStep 4894609 = 3670957) B3670957
theorem B6526145 : Blo 2035435 6526145 := bstep (se 2 (by rfl) ⟨2447304, by rfl⟩ : syracuseStep 6526145 = 4894609) B4894609
theorem B4350763 : Blo 2035435 4350763 := bstep (se 1 (by rfl) ⟨3263072, by rfl⟩ : syracuseStep 4350763 = 6526145) B6526145
theorem B23204069 : Blo 2035435 23204069 := bstep (se 4 (by rfl) ⟨2175381, by rfl⟩ : syracuseStep 23204069 = 4350763) B4350763
theorem B15469379 : Blo 2035435 15469379 := bstep (se 1 (by rfl) ⟨11602034, by rfl⟩ : syracuseStep 15469379 = 23204069) B23204069
theorem B10312919 : Blo 2035435 10312919 := bstep (se 1 (by rfl) ⟨7734689, by rfl⟩ : syracuseStep 10312919 = 15469379) B15469379
theorem B6875279 : Blo 2035435 6875279 := bstep (se 1 (by rfl) ⟨5156459, by rfl⟩ : syracuseStep 6875279 = 10312919) B10312919
theorem B4583519 : Blo 2035435 4583519 := bstep (se 1 (by rfl) ⟨3437639, by rfl⟩ : syracuseStep 4583519 = 6875279) B6875279
theorem B3055679 : Blo 2035435 3055679 := bstep (se 1 (by rfl) ⟨2291759, by rfl⟩ : syracuseStep 3055679 = 4583519) B4583519
theorem B2037119 : Blo 2035435 2037119 := bstep (se 1 (by rfl) ⟨1527839, by rfl⟩ : syracuseStep 2037119 = 3055679) B3055679
theorem B3055685 : Blo 2035435 3055685 := bbase (se 4 (by rfl) ⟨286470, by rfl⟩ : syracuseStep 3055685 = 572941) (by norm_num)
theorem B2037123 : Blo 2035435 2037123 := bstep (se 1 (by rfl) ⟨1527842, by rfl⟩ : syracuseStep 2037123 = 3055685) B3055685
theorem B3437653 : Blo 2035435 3437653 := bbase (se 8 (by rfl) ⟨20142, by rfl⟩ : syracuseStep 3437653 = 40285) (by norm_num)
theorem B4583537 : Blo 2035435 4583537 := bstep (se 2 (by rfl) ⟨1718826, by rfl⟩ : syracuseStep 4583537 = 3437653) B3437653
theorem B3055691 : Blo 2035435 3055691 := bstep (se 1 (by rfl) ⟨2291768, by rfl⟩ : syracuseStep 3055691 = 4583537) B4583537
theorem B2037127 : Blo 2035435 2037127 := bstep (se 1 (by rfl) ⟨1527845, by rfl⟩ : syracuseStep 2037127 = 3055691) B3055691
theorem B2291773 : Blo 2035435 2291773 := bbase (se 3 (by rfl) ⟨429707, by rfl⟩ : syracuseStep 2291773 = 859415) (by norm_num)
theorem B3055697 : Blo 2035435 3055697 := bstep (se 2 (by rfl) ⟨1145886, by rfl⟩ : syracuseStep 3055697 = 2291773) B2291773
theorem B2037131 : Blo 2035435 2037131 := bstep (se 1 (by rfl) ⟨1527848, by rfl⟩ : syracuseStep 2037131 = 3055697) B3055697
theorem B6875333 : Blo 2035435 6875333 := bbase (se 4 (by rfl) ⟨644562, by rfl⟩ : syracuseStep 6875333 = 1289125) (by norm_num)
theorem B4583555 : Blo 2035435 4583555 := bstep (se 1 (by rfl) ⟨3437666, by rfl⟩ : syracuseStep 4583555 = 6875333) B6875333
theorem B3055703 : Blo 2035435 3055703 := bstep (se 1 (by rfl) ⟨2291777, by rfl⟩ : syracuseStep 3055703 = 4583555) B4583555
theorem B2037135 : Blo 2035435 2037135 := bstep (se 1 (by rfl) ⟨1527851, by rfl⟩ : syracuseStep 2037135 = 3055703) B3055703
theorem B3055709 : Blo 2035435 3055709 := bbase (se 3 (by rfl) ⟨572945, by rfl⟩ : syracuseStep 3055709 = 1145891) (by norm_num)
theorem B2037139 : Blo 2035435 2037139 := bstep (se 1 (by rfl) ⟨1527854, by rfl⟩ : syracuseStep 2037139 = 3055709) B3055709
theorem B4583573 : Blo 2035435 4583573 := bbase (se 6 (by rfl) ⟨107427, by rfl⟩ : syracuseStep 4583573 = 214855) (by norm_num)
theorem B3055715 : Blo 2035435 3055715 := bstep (se 1 (by rfl) ⟨2291786, by rfl⟩ : syracuseStep 3055715 = 4583573) B4583573
theorem B2037143 : Blo 2035435 2037143 := bstep (se 1 (by rfl) ⟨1527857, by rfl⟩ : syracuseStep 2037143 = 3055715) B3055715
theorem B2900549 : Blo 2035435 2900549 := bbase (se 4 (by rfl) ⟨271926, by rfl⟩ : syracuseStep 2900549 = 543853) (by norm_num)
theorem B7734797 : Blo 2035435 7734797 := bstep (se 3 (by rfl) ⟨1450274, by rfl⟩ : syracuseStep 7734797 = 2900549) B2900549
theorem B5156531 : Blo 2035435 5156531 := bstep (se 1 (by rfl) ⟨3867398, by rfl⟩ : syracuseStep 5156531 = 7734797) B7734797
theorem B3437687 : Blo 2035435 3437687 := bstep (se 1 (by rfl) ⟨2578265, by rfl⟩ : syracuseStep 3437687 = 5156531) B5156531
theorem B2291791 : Blo 2035435 2291791 := bstep (se 1 (by rfl) ⟨1718843, by rfl⟩ : syracuseStep 2291791 = 3437687) B3437687
theorem B3055721 : Blo 2035435 3055721 := bstep (se 2 (by rfl) ⟨1145895, by rfl⟩ : syracuseStep 3055721 = 2291791) B2291791
theorem B2037147 : Blo 2035435 2037147 := bstep (se 1 (by rfl) ⟨1527860, by rfl⟩ : syracuseStep 2037147 = 3055721) B3055721
theorem B6194837 : Blo 2035435 6194837 := bbase (se 6 (by rfl) ⟨145191, by rfl⟩ : syracuseStep 6194837 = 290383) (by norm_num)
theorem B16519565 : Blo 2035435 16519565 := bstep (se 3 (by rfl) ⟨3097418, by rfl⟩ : syracuseStep 16519565 = 6194837) B6194837
theorem B44052173 : Blo 2035435 44052173 := bstep (se 3 (by rfl) ⟨8259782, by rfl⟩ : syracuseStep 44052173 = 16519565) B16519565
theorem B29368115 : Blo 2035435 29368115 := bstep (se 1 (by rfl) ⟨22026086, by rfl⟩ : syracuseStep 29368115 = 44052173) B44052173
theorem B19578743 : Blo 2035435 19578743 := bstep (se 1 (by rfl) ⟨14684057, by rfl⟩ : syracuseStep 19578743 = 29368115) B29368115
theorem B13052495 : Blo 2035435 13052495 := bstep (se 1 (by rfl) ⟨9789371, by rfl⟩ : syracuseStep 13052495 = 19578743) B19578743
theorem B8701663 : Blo 2035435 8701663 := bstep (se 1 (by rfl) ⟨6526247, by rfl⟩ : syracuseStep 8701663 = 13052495) B13052495
theorem B11602217 : Blo 2035435 11602217 := bstep (se 2 (by rfl) ⟨4350831, by rfl⟩ : syracuseStep 11602217 = 8701663) B8701663
theorem B7734811 : Blo 2035435 7734811 := bstep (se 1 (by rfl) ⟨5801108, by rfl⟩ : syracuseStep 7734811 = 11602217) B11602217
theorem B10313081 : Blo 2035435 10313081 := bstep (se 2 (by rfl) ⟨3867405, by rfl⟩ : syracuseStep 10313081 = 7734811) B7734811
theorem B6875387 : Blo 2035435 6875387 := bstep (se 1 (by rfl) ⟨5156540, by rfl⟩ : syracuseStep 6875387 = 10313081) B10313081
theorem B4583591 : Blo 2035435 4583591 := bstep (se 1 (by rfl) ⟨3437693, by rfl⟩ : syracuseStep 4583591 = 6875387) B6875387
theorem B3055727 : Blo 2035435 3055727 := bstep (se 1 (by rfl) ⟨2291795, by rfl⟩ : syracuseStep 3055727 = 4583591) B4583591
theorem B2037151 : Blo 2035435 2037151 := bstep (se 1 (by rfl) ⟨1527863, by rfl⟩ : syracuseStep 2037151 = 3055727) B3055727
theorem B3055733 : Blo 2035435 3055733 := bbase (se 5 (by rfl) ⟨143237, by rfl⟩ : syracuseStep 3055733 = 286475) (by norm_num)
theorem B2037155 : Blo 2035435 2037155 := bstep (se 1 (by rfl) ⟨1527866, by rfl⟩ : syracuseStep 2037155 = 3055733) B3055733
theorem B3867421 : Blo 2035435 3867421 := bbase (se 3 (by rfl) ⟨725141, by rfl⟩ : syracuseStep 3867421 = 1450283) (by norm_num)
theorem B5156561 : Blo 2035435 5156561 := bstep (se 2 (by rfl) ⟨1933710, by rfl⟩ : syracuseStep 5156561 = 3867421) B3867421
theorem B3437707 : Blo 2035435 3437707 := bstep (se 1 (by rfl) ⟨2578280, by rfl⟩ : syracuseStep 3437707 = 5156561) B5156561
theorem B4583609 : Blo 2035435 4583609 := bstep (se 2 (by rfl) ⟨1718853, by rfl⟩ : syracuseStep 4583609 = 3437707) B3437707
theorem B3055739 : Blo 2035435 3055739 := bstep (se 1 (by rfl) ⟨2291804, by rfl⟩ : syracuseStep 3055739 = 4583609) B4583609
theorem B2037159 : Blo 2035435 2037159 := bstep (se 1 (by rfl) ⟨1527869, by rfl⟩ : syracuseStep 2037159 = 3055739) B3055739
theorem B2291809 : Blo 2035435 2291809 := bbase (se 2 (by rfl) ⟨859428, by rfl⟩ : syracuseStep 2291809 = 1718857) (by norm_num)
theorem B3055745 : Blo 2035435 3055745 := bstep (se 2 (by rfl) ⟨1145904, by rfl⟩ : syracuseStep 3055745 = 2291809) B2291809
theorem B2037163 : Blo 2035435 2037163 := bstep (se 1 (by rfl) ⟨1527872, by rfl⟩ : syracuseStep 2037163 = 3055745) B3055745
theorem B5156581 : Blo 2035435 5156581 := bbase (se 4 (by rfl) ⟨483429, by rfl⟩ : syracuseStep 5156581 = 966859) (by norm_num)
theorem B6875441 : Blo 2035435 6875441 := bstep (se 2 (by rfl) ⟨2578290, by rfl⟩ : syracuseStep 6875441 = 5156581) B5156581
theorem B4583627 : Blo 2035435 4583627 := bstep (se 1 (by rfl) ⟨3437720, by rfl⟩ : syracuseStep 4583627 = 6875441) B6875441
theorem B3055751 : Blo 2035435 3055751 := bstep (se 1 (by rfl) ⟨2291813, by rfl⟩ : syracuseStep 3055751 = 4583627) B4583627
theorem B2037167 : Blo 2035435 2037167 := bstep (se 1 (by rfl) ⟨1527875, by rfl⟩ : syracuseStep 2037167 = 3055751) B3055751
theorem B3055757 : Blo 2035435 3055757 := bbase (se 3 (by rfl) ⟨572954, by rfl⟩ : syracuseStep 3055757 = 1145909) (by norm_num)
theorem B2037171 : Blo 2035435 2037171 := bstep (se 1 (by rfl) ⟨1527878, by rfl⟩ : syracuseStep 2037171 = 3055757) B3055757
theorem B4583645 : Blo 2035435 4583645 := bbase (se 3 (by rfl) ⟨859433, by rfl⟩ : syracuseStep 4583645 = 1718867) (by norm_num)
theorem B3055763 : Blo 2035435 3055763 := bstep (se 1 (by rfl) ⟨2291822, by rfl⟩ : syracuseStep 3055763 = 4583645) B4583645
theorem B2037175 : Blo 2035435 2037175 := bstep (se 1 (by rfl) ⟨1527881, by rfl⟩ : syracuseStep 2037175 = 3055763) B3055763
theorem B3437741 : Blo 2035435 3437741 := bbase (se 3 (by rfl) ⟨644576, by rfl⟩ : syracuseStep 3437741 = 1289153) (by norm_num)
theorem B2291827 : Blo 2035435 2291827 := bstep (se 1 (by rfl) ⟨1718870, by rfl⟩ : syracuseStep 2291827 = 3437741) B3437741
theorem B3055769 : Blo 2035435 3055769 := bstep (se 2 (by rfl) ⟨1145913, by rfl⟩ : syracuseStep 3055769 = 2291827) B2291827
theorem B2037179 : Blo 2035435 2037179 := bstep (se 1 (by rfl) ⟨1527884, by rfl⟩ : syracuseStep 2037179 = 3055769) B3055769
theorem B10596581 : Blo 2035435 10596581 := bbase (se 4 (by rfl) ⟨993429, by rfl⟩ : syracuseStep 10596581 = 1986859) (by norm_num)
theorem B7064387 : Blo 2035435 7064387 := bstep (se 1 (by rfl) ⟨5298290, by rfl⟩ : syracuseStep 7064387 = 10596581) B10596581
theorem B4709591 : Blo 2035435 4709591 := bstep (se 1 (by rfl) ⟨3532193, by rfl⟩ : syracuseStep 4709591 = 7064387) B7064387
theorem B3139727 : Blo 2035435 3139727 := bstep (se 1 (by rfl) ⟨2354795, by rfl⟩ : syracuseStep 3139727 = 4709591) B4709591
theorem B33490421 : Blo 2035435 33490421 := bstep (se 5 (by rfl) ⟨1569863, by rfl⟩ : syracuseStep 33490421 = 3139727) B3139727
theorem B22326947 : Blo 2035435 22326947 := bstep (se 1 (by rfl) ⟨16745210, by rfl⟩ : syracuseStep 22326947 = 33490421) B33490421
theorem B14884631 : Blo 2035435 14884631 := bstep (se 1 (by rfl) ⟨11163473, by rfl⟩ : syracuseStep 14884631 = 22326947) B22326947
theorem B9923087 : Blo 2035435 9923087 := bstep (se 1 (by rfl) ⟨7442315, by rfl⟩ : syracuseStep 9923087 = 14884631) B14884631
theorem B26461565 : Blo 2035435 26461565 := bstep (se 3 (by rfl) ⟨4961543, by rfl⟩ : syracuseStep 26461565 = 9923087) B9923087
theorem B17641043 : Blo 2035435 17641043 := bstep (se 1 (by rfl) ⟨13230782, by rfl⟩ : syracuseStep 17641043 = 26461565) B26461565
theorem B11760695 : Blo 2035435 11760695 := bstep (se 1 (by rfl) ⟨8820521, by rfl⟩ : syracuseStep 11760695 = 17641043) B17641043
theorem B125447413 : Blo 2035435 125447413 := bstep (se 5 (by rfl) ⟨5880347, by rfl⟩ : syracuseStep 125447413 = 11760695) B11760695
theorem B167263217 : Blo 2035435 167263217 := bstep (se 2 (by rfl) ⟨62723706, by rfl⟩ : syracuseStep 167263217 = 125447413) B125447413
theorem B111508811 : Blo 2035435 111508811 := bstep (se 1 (by rfl) ⟨83631608, by rfl⟩ : syracuseStep 111508811 = 167263217) B167263217
theorem B74339207 : Blo 2035435 74339207 := bstep (se 1 (by rfl) ⟨55754405, by rfl⟩ : syracuseStep 74339207 = 111508811) B111508811
theorem B49559471 : Blo 2035435 49559471 := bstep (se 1 (by rfl) ⟨37169603, by rfl⟩ : syracuseStep 49559471 = 74339207) B74339207
theorem B33039647 : Blo 2035435 33039647 := bstep (se 1 (by rfl) ⟨24779735, by rfl⟩ : syracuseStep 33039647 = 49559471) B49559471
theorem B22026431 : Blo 2035435 22026431 := bstep (se 1 (by rfl) ⟨16519823, by rfl⟩ : syracuseStep 22026431 = 33039647) B33039647
theorem B58737149 : Blo 2035435 58737149 := bstep (se 3 (by rfl) ⟨11013215, by rfl⟩ : syracuseStep 58737149 = 22026431) B22026431
theorem B39158099 : Blo 2035435 39158099 := bstep (se 1 (by rfl) ⟨29368574, by rfl⟩ : syracuseStep 39158099 = 58737149) B58737149
theorem B26105399 : Blo 2035435 26105399 := bstep (se 1 (by rfl) ⟨19579049, by rfl⟩ : syracuseStep 26105399 = 39158099) B39158099
theorem B17403599 : Blo 2035435 17403599 := bstep (se 1 (by rfl) ⟨13052699, by rfl⟩ : syracuseStep 17403599 = 26105399) B26105399
theorem B11602399 : Blo 2035435 11602399 := bstep (se 1 (by rfl) ⟨8701799, by rfl⟩ : syracuseStep 11602399 = 17403599) B17403599
theorem B15469865 : Blo 2035435 15469865 := bstep (se 2 (by rfl) ⟨5801199, by rfl⟩ : syracuseStep 15469865 = 11602399) B11602399
theorem B10313243 : Blo 2035435 10313243 := bstep (se 1 (by rfl) ⟨7734932, by rfl⟩ : syracuseStep 10313243 = 15469865) B15469865
theorem B6875495 : Blo 2035435 6875495 := bstep (se 1 (by rfl) ⟨5156621, by rfl⟩ : syracuseStep 6875495 = 10313243) B10313243
theorem B4583663 : Blo 2035435 4583663 := bstep (se 1 (by rfl) ⟨3437747, by rfl⟩ : syracuseStep 4583663 = 6875495) B6875495
theorem B3055775 : Blo 2035435 3055775 := bstep (se 1 (by rfl) ⟨2291831, by rfl⟩ : syracuseStep 3055775 = 4583663) B4583663
theorem B2037183 : Blo 2035435 2037183 := bstep (se 1 (by rfl) ⟨1527887, by rfl⟩ : syracuseStep 2037183 = 3055775) B3055775
theorem B3055781 : Blo 2035435 3055781 := bbase (se 4 (by rfl) ⟨286479, by rfl⟩ : syracuseStep 3055781 = 572959) (by norm_num)
theorem B2037187 : Blo 2035435 2037187 := bstep (se 1 (by rfl) ⟨1527890, by rfl⟩ : syracuseStep 2037187 = 3055781) B3055781
theorem B2578321 : Blo 2035435 2578321 := bbase (se 2 (by rfl) ⟨966870, by rfl⟩ : syracuseStep 2578321 = 1933741) (by norm_num)
theorem B3437761 : Blo 2035435 3437761 := bstep (se 2 (by rfl) ⟨1289160, by rfl⟩ : syracuseStep 3437761 = 2578321) B2578321
theorem B4583681 : Blo 2035435 4583681 := bstep (se 2 (by rfl) ⟨1718880, by rfl⟩ : syracuseStep 4583681 = 3437761) B3437761
theorem B3055787 : Blo 2035435 3055787 := bstep (se 1 (by rfl) ⟨2291840, by rfl⟩ : syracuseStep 3055787 = 4583681) B4583681
theorem B2037191 : Blo 2035435 2037191 := bstep (se 1 (by rfl) ⟨1527893, by rfl⟩ : syracuseStep 2037191 = 3055787) B3055787
theorem B2291845 : Blo 2035435 2291845 := bbase (se 4 (by rfl) ⟨214860, by rfl⟩ : syracuseStep 2291845 = 429721) (by norm_num)
theorem B3055793 : Blo 2035435 3055793 := bstep (se 2 (by rfl) ⟨1145922, by rfl⟩ : syracuseStep 3055793 = 2291845) B2291845
theorem B2037195 : Blo 2035435 2037195 := bstep (se 1 (by rfl) ⟨1527896, by rfl⟩ : syracuseStep 2037195 = 3055793) B3055793
theorem B9789605 : Blo 2035435 9789605 := bbase (se 4 (by rfl) ⟨917775, by rfl⟩ : syracuseStep 9789605 = 1835551) (by norm_num)
theorem B6526403 : Blo 2035435 6526403 := bstep (se 1 (by rfl) ⟨4894802, by rfl⟩ : syracuseStep 6526403 = 9789605) B9789605
theorem B4350935 : Blo 2035435 4350935 := bstep (se 1 (by rfl) ⟨3263201, by rfl⟩ : syracuseStep 4350935 = 6526403) B6526403
theorem B2900623 : Blo 2035435 2900623 := bstep (se 1 (by rfl) ⟨2175467, by rfl⟩ : syracuseStep 2900623 = 4350935) B4350935
theorem B3867497 : Blo 2035435 3867497 := bstep (se 2 (by rfl) ⟨1450311, by rfl⟩ : syracuseStep 3867497 = 2900623) B2900623
theorem B2578331 : Blo 2035435 2578331 := bstep (se 1 (by rfl) ⟨1933748, by rfl⟩ : syracuseStep 2578331 = 3867497) B3867497
theorem B6875549 : Blo 2035435 6875549 := bstep (se 3 (by rfl) ⟨1289165, by rfl⟩ : syracuseStep 6875549 = 2578331) B2578331
theorem B4583699 : Blo 2035435 4583699 := bstep (se 1 (by rfl) ⟨3437774, by rfl⟩ : syracuseStep 4583699 = 6875549) B6875549
theorem B3055799 : Blo 2035435 3055799 := bstep (se 1 (by rfl) ⟨2291849, by rfl⟩ : syracuseStep 3055799 = 4583699) B4583699
theorem B2037199 : Blo 2035435 2037199 := bstep (se 1 (by rfl) ⟨1527899, by rfl⟩ : syracuseStep 2037199 = 3055799) B3055799
theorem B3055805 : Blo 2035435 3055805 := bbase (se 3 (by rfl) ⟨572963, by rfl⟩ : syracuseStep 3055805 = 1145927) (by norm_num)
theorem B2037203 : Blo 2035435 2037203 := bstep (se 1 (by rfl) ⟨1527902, by rfl⟩ : syracuseStep 2037203 = 3055805) B3055805
theorem B4583717 : Blo 2035435 4583717 := bbase (se 4 (by rfl) ⟨429723, by rfl⟩ : syracuseStep 4583717 = 859447) (by norm_num)
theorem B3055811 : Blo 2035435 3055811 := bstep (se 1 (by rfl) ⟨2291858, by rfl⟩ : syracuseStep 3055811 = 4583717) B4583717
theorem B2037207 : Blo 2035435 2037207 := bstep (se 1 (by rfl) ⟨1527905, by rfl⟩ : syracuseStep 2037207 = 3055811) B3055811
theorem B5156693 : Blo 2035435 5156693 := bbase (se 9 (by rfl) ⟨15107, by rfl⟩ : syracuseStep 5156693 = 30215) (by norm_num)
theorem B3437795 : Blo 2035435 3437795 := bstep (se 1 (by rfl) ⟨2578346, by rfl⟩ : syracuseStep 3437795 = 5156693) B5156693
theorem B2291863 : Blo 2035435 2291863 := bstep (se 1 (by rfl) ⟨1718897, by rfl⟩ : syracuseStep 2291863 = 3437795) B3437795
theorem B3055817 : Blo 2035435 3055817 := bstep (se 2 (by rfl) ⟨1145931, by rfl⟩ : syracuseStep 3055817 = 2291863) B2291863
theorem B2037211 : Blo 2035435 2037211 := bstep (se 1 (by rfl) ⟨1527908, by rfl⟩ : syracuseStep 2037211 = 3055817) B3055817
theorem B6526453 : Blo 2035435 6526453 := bbase (se 5 (by rfl) ⟨305927, by rfl⟩ : syracuseStep 6526453 = 611855) (by norm_num)
theorem B8701937 : Blo 2035435 8701937 := bstep (se 2 (by rfl) ⟨3263226, by rfl⟩ : syracuseStep 8701937 = 6526453) B6526453
theorem B5801291 : Blo 2035435 5801291 := bstep (se 1 (by rfl) ⟨4350968, by rfl⟩ : syracuseStep 5801291 = 8701937) B8701937
theorem B3867527 : Blo 2035435 3867527 := bstep (se 1 (by rfl) ⟨2900645, by rfl⟩ : syracuseStep 3867527 = 5801291) B5801291
theorem B10313405 : Blo 2035435 10313405 := bstep (se 3 (by rfl) ⟨1933763, by rfl⟩ : syracuseStep 10313405 = 3867527) B3867527
theorem B6875603 : Blo 2035435 6875603 := bstep (se 1 (by rfl) ⟨5156702, by rfl⟩ : syracuseStep 6875603 = 10313405) B10313405
theorem B4583735 : Blo 2035435 4583735 := bstep (se 1 (by rfl) ⟨3437801, by rfl⟩ : syracuseStep 4583735 = 6875603) B6875603
theorem B3055823 : Blo 2035435 3055823 := bstep (se 1 (by rfl) ⟨2291867, by rfl⟩ : syracuseStep 3055823 = 4583735) B4583735
theorem B2037215 : Blo 2035435 2037215 := bstep (se 1 (by rfl) ⟨1527911, by rfl⟩ : syracuseStep 2037215 = 3055823) B3055823
theorem B3055829 : Blo 2035435 3055829 := bbase (se 7 (by rfl) ⟨35810, by rfl⟩ : syracuseStep 3055829 = 71621) (by norm_num)
theorem B2037219 : Blo 2035435 2037219 := bstep (se 1 (by rfl) ⟨1527914, by rfl⟩ : syracuseStep 2037219 = 3055829) B3055829
theorem B2175493 : Blo 2035435 2175493 := bbase (se 4 (by rfl) ⟨203952, by rfl⟩ : syracuseStep 2175493 = 407905) (by norm_num)
theorem B2900657 : Blo 2035435 2900657 := bstep (se 2 (by rfl) ⟨1087746, by rfl⟩ : syracuseStep 2900657 = 2175493) B2175493
theorem B7735085 : Blo 2035435 7735085 := bstep (se 3 (by rfl) ⟨1450328, by rfl⟩ : syracuseStep 7735085 = 2900657) B2900657
theorem B5156723 : Blo 2035435 5156723 := bstep (se 1 (by rfl) ⟨3867542, by rfl⟩ : syracuseStep 5156723 = 7735085) B7735085
theorem B3437815 : Blo 2035435 3437815 := bstep (se 1 (by rfl) ⟨2578361, by rfl⟩ : syracuseStep 3437815 = 5156723) B5156723
theorem B4583753 : Blo 2035435 4583753 := bstep (se 2 (by rfl) ⟨1718907, by rfl⟩ : syracuseStep 4583753 = 3437815) B3437815
theorem B3055835 : Blo 2035435 3055835 := bstep (se 1 (by rfl) ⟨2291876, by rfl⟩ : syracuseStep 3055835 = 4583753) B4583753
theorem B2037223 : Blo 2035435 2037223 := bstep (se 1 (by rfl) ⟨1527917, by rfl⟩ : syracuseStep 2037223 = 3055835) B3055835
theorem B2291881 : Blo 2035435 2291881 := bbase (se 2 (by rfl) ⟨859455, by rfl⟩ : syracuseStep 2291881 = 1718911) (by norm_num)
theorem B3055841 : Blo 2035435 3055841 := bstep (se 2 (by rfl) ⟨1145940, by rfl⟩ : syracuseStep 3055841 = 2291881) B2291881
theorem B2037227 : Blo 2035435 2037227 := bstep (se 1 (by rfl) ⟨1527920, by rfl⟩ : syracuseStep 2037227 = 3055841) B3055841
theorem B8702005 : Blo 2035435 8702005 := bbase (se 5 (by rfl) ⟨407906, by rfl⟩ : syracuseStep 8702005 = 815813) (by norm_num)
theorem B11602673 : Blo 2035435 11602673 := bstep (se 2 (by rfl) ⟨4351002, by rfl⟩ : syracuseStep 11602673 = 8702005) B8702005
theorem B7735115 : Blo 2035435 7735115 := bstep (se 1 (by rfl) ⟨5801336, by rfl⟩ : syracuseStep 7735115 = 11602673) B11602673
theorem B5156743 : Blo 2035435 5156743 := bstep (se 1 (by rfl) ⟨3867557, by rfl⟩ : syracuseStep 5156743 = 7735115) B7735115
theorem B6875657 : Blo 2035435 6875657 := bstep (se 2 (by rfl) ⟨2578371, by rfl⟩ : syracuseStep 6875657 = 5156743) B5156743
theorem B4583771 : Blo 2035435 4583771 := bstep (se 1 (by rfl) ⟨3437828, by rfl⟩ : syracuseStep 4583771 = 6875657) B6875657
theorem B3055847 : Blo 2035435 3055847 := bstep (se 1 (by rfl) ⟨2291885, by rfl⟩ : syracuseStep 3055847 = 4583771) B4583771
theorem B2037231 : Blo 2035435 2037231 := bstep (se 1 (by rfl) ⟨1527923, by rfl⟩ : syracuseStep 2037231 = 3055847) B3055847
theorem B3055853 : Blo 2035435 3055853 := bbase (se 3 (by rfl) ⟨572972, by rfl⟩ : syracuseStep 3055853 = 1145945) (by norm_num)
theorem B2037235 : Blo 2035435 2037235 := bstep (se 1 (by rfl) ⟨1527926, by rfl⟩ : syracuseStep 2037235 = 3055853) B3055853
theorem B4583789 : Blo 2035435 4583789 := bbase (se 3 (by rfl) ⟨859460, by rfl⟩ : syracuseStep 4583789 = 1718921) (by norm_num)
theorem B3055859 : Blo 2035435 3055859 := bstep (se 1 (by rfl) ⟨2291894, by rfl⟩ : syracuseStep 3055859 = 4583789) B4583789
theorem B2037239 : Blo 2035435 2037239 := bstep (se 1 (by rfl) ⟨1527929, by rfl⟩ : syracuseStep 2037239 = 3055859) B3055859
theorem B3867581 : Blo 2035435 3867581 := bbase (se 3 (by rfl) ⟨725171, by rfl⟩ : syracuseStep 3867581 = 1450343) (by norm_num)
theorem B2578387 : Blo 2035435 2578387 := bstep (se 1 (by rfl) ⟨1933790, by rfl⟩ : syracuseStep 2578387 = 3867581) B3867581
theorem B3437849 : Blo 2035435 3437849 := bstep (se 2 (by rfl) ⟨1289193, by rfl⟩ : syracuseStep 3437849 = 2578387) B2578387
theorem B2291899 : Blo 2035435 2291899 := bstep (se 1 (by rfl) ⟨1718924, by rfl⟩ : syracuseStep 2291899 = 3437849) B3437849
theorem B3055865 : Blo 2035435 3055865 := bstep (se 2 (by rfl) ⟨1145949, by rfl⟩ : syracuseStep 3055865 = 2291899) B2291899
theorem B2037243 : Blo 2035435 2037243 := bstep (se 1 (by rfl) ⟨1527932, by rfl⟩ : syracuseStep 2037243 = 3055865) B3055865
theorem B52212437 : Blo 2035435 52212437 := bbase (se 7 (by rfl) ⟨611864, by rfl⟩ : syracuseStep 52212437 = 1223729) (by norm_num)
theorem B34808291 : Blo 2035435 34808291 := bstep (se 1 (by rfl) ⟨26106218, by rfl⟩ : syracuseStep 34808291 = 52212437) B52212437
theorem B23205527 : Blo 2035435 23205527 := bstep (se 1 (by rfl) ⟨17404145, by rfl⟩ : syracuseStep 23205527 = 34808291) B34808291
theorem B15470351 : Blo 2035435 15470351 := bstep (se 1 (by rfl) ⟨11602763, by rfl⟩ : syracuseStep 15470351 = 23205527) B23205527
theorem B10313567 : Blo 2035435 10313567 := bstep (se 1 (by rfl) ⟨7735175, by rfl⟩ : syracuseStep 10313567 = 15470351) B15470351
theorem B6875711 : Blo 2035435 6875711 := bstep (se 1 (by rfl) ⟨5156783, by rfl⟩ : syracuseStep 6875711 = 10313567) B10313567
theorem B4583807 : Blo 2035435 4583807 := bstep (se 1 (by rfl) ⟨3437855, by rfl⟩ : syracuseStep 4583807 = 6875711) B6875711
theorem B3055871 : Blo 2035435 3055871 := bstep (se 1 (by rfl) ⟨2291903, by rfl⟩ : syracuseStep 3055871 = 4583807) B4583807
theorem B2037247 : Blo 2035435 2037247 := bstep (se 1 (by rfl) ⟨1527935, by rfl⟩ : syracuseStep 2037247 = 3055871) B3055871
theorem B3055877 : Blo 2035435 3055877 := bbase (se 4 (by rfl) ⟨286488, by rfl⟩ : syracuseStep 3055877 = 572977) (by norm_num)
theorem B2037251 : Blo 2035435 2037251 := bstep (se 1 (by rfl) ⟨1527938, by rfl⟩ : syracuseStep 2037251 = 3055877) B3055877
theorem B3437869 : Blo 2035435 3437869 := bbase (se 3 (by rfl) ⟨644600, by rfl⟩ : syracuseStep 3437869 = 1289201) (by norm_num)
theorem B4583825 : Blo 2035435 4583825 := bstep (se 2 (by rfl) ⟨1718934, by rfl⟩ : syracuseStep 4583825 = 3437869) B3437869
theorem B3055883 : Blo 2035435 3055883 := bstep (se 1 (by rfl) ⟨2291912, by rfl⟩ : syracuseStep 3055883 = 4583825) B4583825
theorem B2037255 : Blo 2035435 2037255 := bstep (se 1 (by rfl) ⟨1527941, by rfl⟩ : syracuseStep 2037255 = 3055883) B3055883
theorem B2291917 : Blo 2035435 2291917 := bbase (se 3 (by rfl) ⟨429734, by rfl⟩ : syracuseStep 2291917 = 859469) (by norm_num)
theorem B3055889 : Blo 2035435 3055889 := bstep (se 2 (by rfl) ⟨1145958, by rfl⟩ : syracuseStep 3055889 = 2291917) B2291917
theorem B2037259 : Blo 2035435 2037259 := bstep (se 1 (by rfl) ⟨1527944, by rfl⟩ : syracuseStep 2037259 = 3055889) B3055889
theorem B6875765 : Blo 2035435 6875765 := bbase (se 5 (by rfl) ⟨322301, by rfl⟩ : syracuseStep 6875765 = 644603) (by norm_num)
theorem B4583843 : Blo 2035435 4583843 := bstep (se 1 (by rfl) ⟨3437882, by rfl⟩ : syracuseStep 4583843 = 6875765) B6875765
theorem B3055895 : Blo 2035435 3055895 := bstep (se 1 (by rfl) ⟨2291921, by rfl⟩ : syracuseStep 3055895 = 4583843) B4583843
theorem B2037263 : Blo 2035435 2037263 := bstep (se 1 (by rfl) ⟨1527947, by rfl⟩ : syracuseStep 2037263 = 3055895) B3055895
theorem B3055901 : Blo 2035435 3055901 := bbase (se 3 (by rfl) ⟨572981, by rfl⟩ : syracuseStep 3055901 = 1145963) (by norm_num)
theorem B2037267 : Blo 2035435 2037267 := bstep (se 1 (by rfl) ⟨1527950, by rfl⟩ : syracuseStep 2037267 = 3055901) B3055901
theorem B4583861 : Blo 2035435 4583861 := bbase (se 5 (by rfl) ⟨214868, by rfl⟩ : syracuseStep 4583861 = 429737) (by norm_num)
theorem B3055907 : Blo 2035435 3055907 := bstep (se 1 (by rfl) ⟨2291930, by rfl⟩ : syracuseStep 3055907 = 4583861) B4583861
theorem B2037271 : Blo 2035435 2037271 := bstep (se 1 (by rfl) ⟨1527953, by rfl⟩ : syracuseStep 2037271 = 3055907) B3055907
theorem B4646413 : Blo 2035435 4646413 := bbase (se 3 (by rfl) ⟨871202, by rfl⟩ : syracuseStep 4646413 = 1742405) (by norm_num)
theorem B6195217 : Blo 2035435 6195217 := bstep (se 2 (by rfl) ⟨2323206, by rfl⟩ : syracuseStep 6195217 = 4646413) B4646413
theorem B8260289 : Blo 2035435 8260289 := bstep (se 2 (by rfl) ⟨3097608, by rfl⟩ : syracuseStep 8260289 = 6195217) B6195217
theorem B5506859 : Blo 2035435 5506859 := bstep (se 1 (by rfl) ⟨4130144, by rfl⟩ : syracuseStep 5506859 = 8260289) B8260289
theorem B3671239 : Blo 2035435 3671239 := bstep (se 1 (by rfl) ⟨2753429, by rfl⟩ : syracuseStep 3671239 = 5506859) B5506859
theorem B4894985 : Blo 2035435 4894985 := bstep (se 2 (by rfl) ⟨1835619, by rfl⟩ : syracuseStep 4894985 = 3671239) B3671239
theorem B3263323 : Blo 2035435 3263323 := bstep (se 1 (by rfl) ⟨2447492, by rfl⟩ : syracuseStep 3263323 = 4894985) B4894985
theorem B4351097 : Blo 2035435 4351097 := bstep (se 2 (by rfl) ⟨1631661, by rfl⟩ : syracuseStep 4351097 = 3263323) B3263323
theorem B11602925 : Blo 2035435 11602925 := bstep (se 3 (by rfl) ⟨2175548, by rfl⟩ : syracuseStep 11602925 = 4351097) B4351097
theorem B7735283 : Blo 2035435 7735283 := bstep (se 1 (by rfl) ⟨5801462, by rfl⟩ : syracuseStep 7735283 = 11602925) B11602925
theorem B5156855 : Blo 2035435 5156855 := bstep (se 1 (by rfl) ⟨3867641, by rfl⟩ : syracuseStep 5156855 = 7735283) B7735283
theorem B3437903 : Blo 2035435 3437903 := bstep (se 1 (by rfl) ⟨2578427, by rfl⟩ : syracuseStep 3437903 = 5156855) B5156855
theorem B2291935 : Blo 2035435 2291935 := bstep (se 1 (by rfl) ⟨1718951, by rfl⟩ : syracuseStep 2291935 = 3437903) B3437903
theorem B3055913 : Blo 2035435 3055913 := bstep (se 2 (by rfl) ⟨1145967, by rfl⟩ : syracuseStep 3055913 = 2291935) B2291935
theorem B2037275 : Blo 2035435 2037275 := bstep (se 1 (by rfl) ⟨1527956, by rfl⟩ : syracuseStep 2037275 = 3055913) B3055913
theorem B2447497 : Blo 2035435 2447497 := bbase (se 2 (by rfl) ⟨917811, by rfl⟩ : syracuseStep 2447497 = 1835623) (by norm_num)
theorem B3263329 : Blo 2035435 3263329 := bstep (se 2 (by rfl) ⟨1223748, by rfl⟩ : syracuseStep 3263329 = 2447497) B2447497
theorem B4351105 : Blo 2035435 4351105 := bstep (se 2 (by rfl) ⟨1631664, by rfl⟩ : syracuseStep 4351105 = 3263329) B3263329
theorem B5801473 : Blo 2035435 5801473 := bstep (se 2 (by rfl) ⟨2175552, by rfl⟩ : syracuseStep 5801473 = 4351105) B4351105
theorem B7735297 : Blo 2035435 7735297 := bstep (se 2 (by rfl) ⟨2900736, by rfl⟩ : syracuseStep 7735297 = 5801473) B5801473
theorem B10313729 : Blo 2035435 10313729 := bstep (se 2 (by rfl) ⟨3867648, by rfl⟩ : syracuseStep 10313729 = 7735297) B7735297
theorem B6875819 : Blo 2035435 6875819 := bstep (se 1 (by rfl) ⟨5156864, by rfl⟩ : syracuseStep 6875819 = 10313729) B10313729
theorem B4583879 : Blo 2035435 4583879 := bstep (se 1 (by rfl) ⟨3437909, by rfl⟩ : syracuseStep 4583879 = 6875819) B6875819
theorem B3055919 : Blo 2035435 3055919 := bstep (se 1 (by rfl) ⟨2291939, by rfl⟩ : syracuseStep 3055919 = 4583879) B4583879
theorem B2037279 : Blo 2035435 2037279 := bstep (se 1 (by rfl) ⟨1527959, by rfl⟩ : syracuseStep 2037279 = 3055919) B3055919
theorem B3055925 : Blo 2035435 3055925 := bbase (se 5 (by rfl) ⟨143246, by rfl⟩ : syracuseStep 3055925 = 286493) (by norm_num)
theorem B2037283 : Blo 2035435 2037283 := bstep (se 1 (by rfl) ⟨1527962, by rfl⟩ : syracuseStep 2037283 = 3055925) B3055925
theorem B5156885 : Blo 2035435 5156885 := bbase (se 6 (by rfl) ⟨120864, by rfl⟩ : syracuseStep 5156885 = 241729) (by norm_num)
theorem B3437923 : Blo 2035435 3437923 := bstep (se 1 (by rfl) ⟨2578442, by rfl⟩ : syracuseStep 3437923 = 5156885) B5156885
theorem B4583897 : Blo 2035435 4583897 := bstep (se 2 (by rfl) ⟨1718961, by rfl⟩ : syracuseStep 4583897 = 3437923) B3437923
theorem B3055931 : Blo 2035435 3055931 := bstep (se 1 (by rfl) ⟨2291948, by rfl⟩ : syracuseStep 3055931 = 4583897) B4583897
theorem B2037287 : Blo 2035435 2037287 := bstep (se 1 (by rfl) ⟨1527965, by rfl⟩ : syracuseStep 2037287 = 3055931) B3055931
theorem B2291953 : Blo 2035435 2291953 := bbase (se 2 (by rfl) ⟨859482, by rfl⟩ : syracuseStep 2291953 = 1718965) (by norm_num)
theorem B3055937 : Blo 2035435 3055937 := bstep (se 2 (by rfl) ⟨1145976, by rfl⟩ : syracuseStep 3055937 = 2291953) B2291953
theorem B2037291 : Blo 2035435 2037291 := bstep (se 1 (by rfl) ⟨1527968, by rfl⟩ : syracuseStep 2037291 = 3055937) B3055937
theorem B3139901 : Blo 2035435 3139901 := bbase (se 3 (by rfl) ⟨588731, by rfl⟩ : syracuseStep 3139901 = 1177463) (by norm_num)
theorem B2093267 : Blo 2035435 2093267 := bstep (se 1 (by rfl) ⟨1569950, by rfl⟩ : syracuseStep 2093267 = 3139901) B3139901
theorem B5582045 : Blo 2035435 5582045 := bstep (se 3 (by rfl) ⟨1046633, by rfl⟩ : syracuseStep 5582045 = 2093267) B2093267
theorem B3721363 : Blo 2035435 3721363 := bstep (se 1 (by rfl) ⟨2791022, by rfl⟩ : syracuseStep 3721363 = 5582045) B5582045
theorem B19847269 : Blo 2035435 19847269 := bstep (se 4 (by rfl) ⟨1860681, by rfl⟩ : syracuseStep 19847269 = 3721363) B3721363
theorem B26463025 : Blo 2035435 26463025 := bstep (se 2 (by rfl) ⟨9923634, by rfl⟩ : syracuseStep 26463025 = 19847269) B19847269
theorem B35284033 : Blo 2035435 35284033 := bstep (se 2 (by rfl) ⟨13231512, by rfl⟩ : syracuseStep 35284033 = 26463025) B26463025
theorem B47045377 : Blo 2035435 47045377 := bstep (se 2 (by rfl) ⟨17642016, by rfl⟩ : syracuseStep 47045377 = 35284033) B35284033
theorem B62727169 : Blo 2035435 62727169 := bstep (se 2 (by rfl) ⟨23522688, by rfl⟩ : syracuseStep 62727169 = 47045377) B47045377
theorem B83636225 : Blo 2035435 83636225 := bstep (se 2 (by rfl) ⟨31363584, by rfl⟩ : syracuseStep 83636225 = 62727169) B62727169
theorem B55757483 : Blo 2035435 55757483 := bstep (se 1 (by rfl) ⟨41818112, by rfl⟩ : syracuseStep 55757483 = 83636225) B83636225
theorem B37171655 : Blo 2035435 37171655 := bstep (se 1 (by rfl) ⟨27878741, by rfl⟩ : syracuseStep 37171655 = 55757483) B55757483
theorem B24781103 : Blo 2035435 24781103 := bstep (se 1 (by rfl) ⟨18585827, by rfl⟩ : syracuseStep 24781103 = 37171655) B37171655
theorem B16520735 : Blo 2035435 16520735 := bstep (se 1 (by rfl) ⟨12390551, by rfl⟩ : syracuseStep 16520735 = 24781103) B24781103
theorem B11013823 : Blo 2035435 11013823 := bstep (se 1 (by rfl) ⟨8260367, by rfl⟩ : syracuseStep 11013823 = 16520735) B16520735
theorem B14685097 : Blo 2035435 14685097 := bstep (se 2 (by rfl) ⟨5506911, by rfl⟩ : syracuseStep 14685097 = 11013823) B11013823
theorem B19580129 : Blo 2035435 19580129 := bstep (se 2 (by rfl) ⟨7342548, by rfl⟩ : syracuseStep 19580129 = 14685097) B14685097
theorem B13053419 : Blo 2035435 13053419 := bstep (se 1 (by rfl) ⟨9790064, by rfl⟩ : syracuseStep 13053419 = 19580129) B19580129
theorem B8702279 : Blo 2035435 8702279 := bstep (se 1 (by rfl) ⟨6526709, by rfl⟩ : syracuseStep 8702279 = 13053419) B13053419
theorem B5801519 : Blo 2035435 5801519 := bstep (se 1 (by rfl) ⟨4351139, by rfl⟩ : syracuseStep 5801519 = 8702279) B8702279
theorem B3867679 : Blo 2035435 3867679 := bstep (se 1 (by rfl) ⟨2900759, by rfl⟩ : syracuseStep 3867679 = 5801519) B5801519
theorem B5156905 : Blo 2035435 5156905 := bstep (se 2 (by rfl) ⟨1933839, by rfl⟩ : syracuseStep 5156905 = 3867679) B3867679
theorem B6875873 : Blo 2035435 6875873 := bstep (se 2 (by rfl) ⟨2578452, by rfl⟩ : syracuseStep 6875873 = 5156905) B5156905
theorem B4583915 : Blo 2035435 4583915 := bstep (se 1 (by rfl) ⟨3437936, by rfl⟩ : syracuseStep 4583915 = 6875873) B6875873
theorem B3055943 : Blo 2035435 3055943 := bstep (se 1 (by rfl) ⟨2291957, by rfl⟩ : syracuseStep 3055943 = 4583915) B4583915
theorem B2037295 : Blo 2035435 2037295 := bstep (se 1 (by rfl) ⟨1527971, by rfl⟩ : syracuseStep 2037295 = 3055943) B3055943
theorem B3055949 : Blo 2035435 3055949 := bbase (se 3 (by rfl) ⟨572990, by rfl⟩ : syracuseStep 3055949 = 1145981) (by norm_num)
theorem B2037299 : Blo 2035435 2037299 := bstep (se 1 (by rfl) ⟨1527974, by rfl⟩ : syracuseStep 2037299 = 3055949) B3055949
theorem B4583933 : Blo 2035435 4583933 := bbase (se 3 (by rfl) ⟨859487, by rfl⟩ : syracuseStep 4583933 = 1718975) (by norm_num)
theorem B3055955 : Blo 2035435 3055955 := bstep (se 1 (by rfl) ⟨2291966, by rfl⟩ : syracuseStep 3055955 = 4583933) B4583933
theorem B2037303 : Blo 2035435 2037303 := bstep (se 1 (by rfl) ⟨1527977, by rfl⟩ : syracuseStep 2037303 = 3055955) B3055955
theorem B3437957 : Blo 2035435 3437957 := bbase (se 4 (by rfl) ⟨322308, by rfl⟩ : syracuseStep 3437957 = 644617) (by norm_num)
theorem B2291971 : Blo 2035435 2291971 := bstep (se 1 (by rfl) ⟨1718978, by rfl⟩ : syracuseStep 2291971 = 3437957) B3437957
theorem B3055961 : Blo 2035435 3055961 := bstep (se 2 (by rfl) ⟨1145985, by rfl⟩ : syracuseStep 3055961 = 2291971) B2291971
theorem B2037307 : Blo 2035435 2037307 := bstep (se 1 (by rfl) ⟨1527980, by rfl⟩ : syracuseStep 2037307 = 3055961) B3055961
theorem B15470837 : Blo 2035435 15470837 := bbase (se 5 (by rfl) ⟨725195, by rfl⟩ : syracuseStep 15470837 = 1450391) (by norm_num)
theorem B10313891 : Blo 2035435 10313891 := bstep (se 1 (by rfl) ⟨7735418, by rfl⟩ : syracuseStep 10313891 = 15470837) B15470837
theorem B6875927 : Blo 2035435 6875927 := bstep (se 1 (by rfl) ⟨5156945, by rfl⟩ : syracuseStep 6875927 = 10313891) B10313891
theorem B4583951 : Blo 2035435 4583951 := bstep (se 1 (by rfl) ⟨3437963, by rfl⟩ : syracuseStep 4583951 = 6875927) B6875927
theorem B3055967 : Blo 2035435 3055967 := bstep (se 1 (by rfl) ⟨2291975, by rfl⟩ : syracuseStep 3055967 = 4583951) B4583951
theorem B2037311 : Blo 2035435 2037311 := bstep (se 1 (by rfl) ⟨1527983, by rfl⟩ : syracuseStep 2037311 = 3055967) B3055967
theorem B3055973 : Blo 2035435 3055973 := bbase (se 4 (by rfl) ⟨286497, by rfl⟩ : syracuseStep 3055973 = 572995) (by norm_num)
theorem B2037315 : Blo 2035435 2037315 := bstep (se 1 (by rfl) ⟨1527986, by rfl⟩ : syracuseStep 2037315 = 3055973) B3055973
theorem B3867725 : Blo 2035435 3867725 := bbase (se 3 (by rfl) ⟨725198, by rfl⟩ : syracuseStep 3867725 = 1450397) (by norm_num)
theorem B2578483 : Blo 2035435 2578483 := bstep (se 1 (by rfl) ⟨1933862, by rfl⟩ : syracuseStep 2578483 = 3867725) B3867725
theorem B3437977 : Blo 2035435 3437977 := bstep (se 2 (by rfl) ⟨1289241, by rfl⟩ : syracuseStep 3437977 = 2578483) B2578483
theorem B4583969 : Blo 2035435 4583969 := bstep (se 2 (by rfl) ⟨1718988, by rfl⟩ : syracuseStep 4583969 = 3437977) B3437977
theorem B3055979 : Blo 2035435 3055979 := bstep (se 1 (by rfl) ⟨2291984, by rfl⟩ : syracuseStep 3055979 = 4583969) B4583969
theorem B2037319 : Blo 2035435 2037319 := bstep (se 1 (by rfl) ⟨1527989, by rfl⟩ : syracuseStep 2037319 = 3055979) B3055979
theorem B2291989 : Blo 2035435 2291989 := bbase (se 6 (by rfl) ⟨53718, by rfl⟩ : syracuseStep 2291989 = 107437) (by norm_num)
theorem B3055985 : Blo 2035435 3055985 := bstep (se 2 (by rfl) ⟨1145994, by rfl⟩ : syracuseStep 3055985 = 2291989) B2291989
theorem B2037323 : Blo 2035435 2037323 := bstep (se 1 (by rfl) ⟨1527992, by rfl⟩ : syracuseStep 2037323 = 3055985) B3055985
theorem B2578493 : Blo 2035435 2578493 := bbase (se 3 (by rfl) ⟨483467, by rfl⟩ : syracuseStep 2578493 = 966935) (by norm_num)
theorem B6875981 : Blo 2035435 6875981 := bstep (se 3 (by rfl) ⟨1289246, by rfl⟩ : syracuseStep 6875981 = 2578493) B2578493
theorem B4583987 : Blo 2035435 4583987 := bstep (se 1 (by rfl) ⟨3437990, by rfl⟩ : syracuseStep 4583987 = 6875981) B6875981
theorem B3055991 : Blo 2035435 3055991 := bstep (se 1 (by rfl) ⟨2291993, by rfl⟩ : syracuseStep 3055991 = 4583987) B4583987
theorem B2037327 : Blo 2035435 2037327 := bstep (se 1 (by rfl) ⟨1527995, by rfl⟩ : syracuseStep 2037327 = 3055991) B3055991
theorem B3055997 : Blo 2035435 3055997 := bbase (se 3 (by rfl) ⟨572999, by rfl⟩ : syracuseStep 3055997 = 1145999) (by norm_num)
theorem B2037331 : Blo 2035435 2037331 := bstep (se 1 (by rfl) ⟨1527998, by rfl⟩ : syracuseStep 2037331 = 3055997) B3055997
theorem B4584005 : Blo 2035435 4584005 := bbase (se 4 (by rfl) ⟨429750, by rfl⟩ : syracuseStep 4584005 = 859501) (by norm_num)
theorem B3056003 : Blo 2035435 3056003 := bstep (se 1 (by rfl) ⟨2292002, by rfl⟩ : syracuseStep 3056003 = 4584005) B4584005
theorem B2037335 : Blo 2035435 2037335 := bstep (se 1 (by rfl) ⟨1528001, by rfl⟩ : syracuseStep 2037335 = 3056003) B3056003
theorem B2175617 : Blo 2035435 2175617 := bbase (se 2 (by rfl) ⟨815856, by rfl⟩ : syracuseStep 2175617 = 1631713) (by norm_num)
theorem B5801645 : Blo 2035435 5801645 := bstep (se 3 (by rfl) ⟨1087808, by rfl⟩ : syracuseStep 5801645 = 2175617) B2175617
theorem B3867763 : Blo 2035435 3867763 := bstep (se 1 (by rfl) ⟨2900822, by rfl⟩ : syracuseStep 3867763 = 5801645) B5801645
theorem B5157017 : Blo 2035435 5157017 := bstep (se 2 (by rfl) ⟨1933881, by rfl⟩ : syracuseStep 5157017 = 3867763) B3867763
theorem B3438011 : Blo 2035435 3438011 := bstep (se 1 (by rfl) ⟨2578508, by rfl⟩ : syracuseStep 3438011 = 5157017) B5157017
theorem B2292007 : Blo 2035435 2292007 := bstep (se 1 (by rfl) ⟨1719005, by rfl⟩ : syracuseStep 2292007 = 3438011) B3438011
theorem B3056009 : Blo 2035435 3056009 := bstep (se 2 (by rfl) ⟨1146003, by rfl⟩ : syracuseStep 3056009 = 2292007) B2292007
theorem B2037339 : Blo 2035435 2037339 := bstep (se 1 (by rfl) ⟨1528004, by rfl⟩ : syracuseStep 2037339 = 3056009) B3056009
theorem B10314053 : Blo 2035435 10314053 := bbase (se 4 (by rfl) ⟨966942, by rfl⟩ : syracuseStep 10314053 = 1933885) (by norm_num)
theorem B6876035 : Blo 2035435 6876035 := bstep (se 1 (by rfl) ⟨5157026, by rfl⟩ : syracuseStep 6876035 = 10314053) B10314053
theorem B4584023 : Blo 2035435 4584023 := bstep (se 1 (by rfl) ⟨3438017, by rfl⟩ : syracuseStep 4584023 = 6876035) B6876035
theorem B3056015 : Blo 2035435 3056015 := bstep (se 1 (by rfl) ⟨2292011, by rfl⟩ : syracuseStep 3056015 = 4584023) B4584023
theorem B2037343 : Blo 2035435 2037343 := bstep (se 1 (by rfl) ⟨1528007, by rfl⟩ : syracuseStep 2037343 = 3056015) B3056015
theorem B3056021 : Blo 2035435 3056021 := bbase (se 6 (by rfl) ⟨71625, by rfl⟩ : syracuseStep 3056021 = 143251) (by norm_num)
theorem B2037347 : Blo 2035435 2037347 := bstep (se 1 (by rfl) ⟨1528010, by rfl⟩ : syracuseStep 2037347 = 3056021) B3056021
theorem B2205313 : Blo 2035435 2205313 := bbase (se 2 (by rfl) ⟨826992, by rfl⟩ : syracuseStep 2205313 = 1653985) (by norm_num)
theorem B11761669 : Blo 2035435 11761669 := bstep (se 4 (by rfl) ⟨1102656, by rfl⟩ : syracuseStep 11761669 = 2205313) B2205313
theorem B62728901 : Blo 2035435 62728901 := bstep (se 4 (by rfl) ⟨5880834, by rfl⟩ : syracuseStep 62728901 = 11761669) B11761669
theorem B41819267 : Blo 2035435 41819267 := bstep (se 1 (by rfl) ⟨31364450, by rfl⟩ : syracuseStep 41819267 = 62728901) B62728901
theorem B27879511 : Blo 2035435 27879511 := bstep (se 1 (by rfl) ⟨20909633, by rfl⟩ : syracuseStep 27879511 = 41819267) B41819267
theorem B37172681 : Blo 2035435 37172681 := bstep (se 2 (by rfl) ⟨13939755, by rfl⟩ : syracuseStep 37172681 = 27879511) B27879511
theorem B24781787 : Blo 2035435 24781787 := bstep (se 1 (by rfl) ⟨18586340, by rfl⟩ : syracuseStep 24781787 = 37172681) B37172681
theorem B16521191 : Blo 2035435 16521191 := bstep (se 1 (by rfl) ⟨12390893, by rfl⟩ : syracuseStep 16521191 = 24781787) B24781787
theorem B11014127 : Blo 2035435 11014127 := bstep (se 1 (by rfl) ⟨8260595, by rfl⟩ : syracuseStep 11014127 = 16521191) B16521191
theorem B7342751 : Blo 2035435 7342751 := bstep (se 1 (by rfl) ⟨5507063, by rfl⟩ : syracuseStep 7342751 = 11014127) B11014127
theorem B4895167 : Blo 2035435 4895167 := bstep (se 1 (by rfl) ⟨3671375, by rfl⟩ : syracuseStep 4895167 = 7342751) B7342751
theorem B6526889 : Blo 2035435 6526889 := bstep (se 2 (by rfl) ⟨2447583, by rfl⟩ : syracuseStep 6526889 = 4895167) B4895167
theorem B4351259 : Blo 2035435 4351259 := bstep (se 1 (by rfl) ⟨3263444, by rfl⟩ : syracuseStep 4351259 = 6526889) B6526889
theorem B11603357 : Blo 2035435 11603357 := bstep (se 3 (by rfl) ⟨2175629, by rfl⟩ : syracuseStep 11603357 = 4351259) B4351259
theorem B7735571 : Blo 2035435 7735571 := bstep (se 1 (by rfl) ⟨5801678, by rfl⟩ : syracuseStep 7735571 = 11603357) B11603357
theorem B5157047 : Blo 2035435 5157047 := bstep (se 1 (by rfl) ⟨3867785, by rfl⟩ : syracuseStep 5157047 = 7735571) B7735571
theorem B3438031 : Blo 2035435 3438031 := bstep (se 1 (by rfl) ⟨2578523, by rfl⟩ : syracuseStep 3438031 = 5157047) B5157047
theorem B4584041 : Blo 2035435 4584041 := bstep (se 2 (by rfl) ⟨1719015, by rfl⟩ : syracuseStep 4584041 = 3438031) B3438031
theorem B3056027 : Blo 2035435 3056027 := bstep (se 1 (by rfl) ⟨2292020, by rfl⟩ : syracuseStep 3056027 = 4584041) B4584041
theorem B2037351 : Blo 2035435 2037351 := bstep (se 1 (by rfl) ⟨1528013, by rfl⟩ : syracuseStep 2037351 = 3056027) B3056027
theorem B2292025 : Blo 2035435 2292025 := bbase (se 2 (by rfl) ⟨859509, by rfl⟩ : syracuseStep 2292025 = 1719019) (by norm_num)
theorem B3056033 : Blo 2035435 3056033 := bstep (se 2 (by rfl) ⟨1146012, by rfl⟩ : syracuseStep 3056033 = 2292025) B2292025
theorem B2037355 : Blo 2035435 2037355 := bstep (se 1 (by rfl) ⟨1528016, by rfl⟩ : syracuseStep 2037355 = 3056033) B3056033
theorem B5801701 : Blo 2035435 5801701 := bbase (se 4 (by rfl) ⟨543909, by rfl⟩ : syracuseStep 5801701 = 1087819) (by norm_num)
theorem B7735601 : Blo 2035435 7735601 := bstep (se 2 (by rfl) ⟨2900850, by rfl⟩ : syracuseStep 7735601 = 5801701) B5801701
theorem B5157067 : Blo 2035435 5157067 := bstep (se 1 (by rfl) ⟨3867800, by rfl⟩ : syracuseStep 5157067 = 7735601) B7735601
theorem B6876089 : Blo 2035435 6876089 := bstep (se 2 (by rfl) ⟨2578533, by rfl⟩ : syracuseStep 6876089 = 5157067) B5157067
theorem B4584059 : Blo 2035435 4584059 := bstep (se 1 (by rfl) ⟨3438044, by rfl⟩ : syracuseStep 4584059 = 6876089) B6876089
theorem B3056039 : Blo 2035435 3056039 := bstep (se 1 (by rfl) ⟨2292029, by rfl⟩ : syracuseStep 3056039 = 4584059) B4584059
theorem B2037359 : Blo 2035435 2037359 := bstep (se 1 (by rfl) ⟨1528019, by rfl⟩ : syracuseStep 2037359 = 3056039) B3056039
theorem B3056045 : Blo 2035435 3056045 := bbase (se 3 (by rfl) ⟨573008, by rfl⟩ : syracuseStep 3056045 = 1146017) (by norm_num)
theorem B2037363 : Blo 2035435 2037363 := bstep (se 1 (by rfl) ⟨1528022, by rfl⟩ : syracuseStep 2037363 = 3056045) B3056045
theorem B4584077 : Blo 2035435 4584077 := bbase (se 3 (by rfl) ⟨859514, by rfl⟩ : syracuseStep 4584077 = 1719029) (by norm_num)
theorem B3056051 : Blo 2035435 3056051 := bstep (se 1 (by rfl) ⟨2292038, by rfl⟩ : syracuseStep 3056051 = 4584077) B4584077
theorem B2037367 : Blo 2035435 2037367 := bstep (se 1 (by rfl) ⟨1528025, by rfl⟩ : syracuseStep 2037367 = 3056051) B3056051
theorem B2578549 : Blo 2035435 2578549 := bbase (se 5 (by rfl) ⟨120869, by rfl⟩ : syracuseStep 2578549 = 241739) (by norm_num)
theorem B3438065 : Blo 2035435 3438065 := bstep (se 2 (by rfl) ⟨1289274, by rfl⟩ : syracuseStep 3438065 = 2578549) B2578549
theorem B2292043 : Blo 2035435 2292043 := bstep (se 1 (by rfl) ⟨1719032, by rfl⟩ : syracuseStep 2292043 = 3438065) B3438065
theorem B3056057 : Blo 2035435 3056057 := bstep (se 2 (by rfl) ⟨1146021, by rfl⟩ : syracuseStep 3056057 = 2292043) B2292043
theorem B2037371 : Blo 2035435 2037371 := bstep (se 1 (by rfl) ⟨1528028, by rfl⟩ : syracuseStep 2037371 = 3056057) B3056057
theorem B4410677 : Blo 2035435 4410677 := bbase (se 5 (by rfl) ⟨206750, by rfl⟩ : syracuseStep 4410677 = 413501) (by norm_num)
theorem B2940451 : Blo 2035435 2940451 := bstep (se 1 (by rfl) ⟨2205338, by rfl⟩ : syracuseStep 2940451 = 4410677) B4410677
theorem B15682405 : Blo 2035435 15682405 := bstep (se 4 (by rfl) ⟨1470225, by rfl⟩ : syracuseStep 15682405 = 2940451) B2940451
theorem B20909873 : Blo 2035435 20909873 := bstep (se 2 (by rfl) ⟨7841202, by rfl⟩ : syracuseStep 20909873 = 15682405) B15682405
theorem B55759661 : Blo 2035435 55759661 := bstep (se 3 (by rfl) ⟨10454936, by rfl⟩ : syracuseStep 55759661 = 20909873) B20909873
theorem B37173107 : Blo 2035435 37173107 := bstep (se 1 (by rfl) ⟨27879830, by rfl⟩ : syracuseStep 37173107 = 55759661) B55759661
theorem B24782071 : Blo 2035435 24782071 := bstep (se 1 (by rfl) ⟨18586553, by rfl⟩ : syracuseStep 24782071 = 37173107) B37173107
theorem B33042761 : Blo 2035435 33042761 := bstep (se 2 (by rfl) ⟨12391035, by rfl⟩ : syracuseStep 33042761 = 24782071) B24782071
theorem B22028507 : Blo 2035435 22028507 := bstep (se 1 (by rfl) ⟨16521380, by rfl⟩ : syracuseStep 22028507 = 33042761) B33042761
theorem B14685671 : Blo 2035435 14685671 := bstep (se 1 (by rfl) ⟨11014253, by rfl⟩ : syracuseStep 14685671 = 22028507) B22028507
theorem B39161789 : Blo 2035435 39161789 := bstep (se 3 (by rfl) ⟨7342835, by rfl⟩ : syracuseStep 39161789 = 14685671) B14685671
theorem B26107859 : Blo 2035435 26107859 := bstep (se 1 (by rfl) ⟨19580894, by rfl⟩ : syracuseStep 26107859 = 39161789) B39161789
theorem B17405239 : Blo 2035435 17405239 := bstep (se 1 (by rfl) ⟨13053929, by rfl⟩ : syracuseStep 17405239 = 26107859) B26107859
theorem B23206985 : Blo 2035435 23206985 := bstep (se 2 (by rfl) ⟨8702619, by rfl⟩ : syracuseStep 23206985 = 17405239) B17405239
theorem B15471323 : Blo 2035435 15471323 := bstep (se 1 (by rfl) ⟨11603492, by rfl⟩ : syracuseStep 15471323 = 23206985) B23206985
theorem B10314215 : Blo 2035435 10314215 := bstep (se 1 (by rfl) ⟨7735661, by rfl⟩ : syracuseStep 10314215 = 15471323) B15471323
theorem B6876143 : Blo 2035435 6876143 := bstep (se 1 (by rfl) ⟨5157107, by rfl⟩ : syracuseStep 6876143 = 10314215) B10314215
theorem B4584095 : Blo 2035435 4584095 := bstep (se 1 (by rfl) ⟨3438071, by rfl⟩ : syracuseStep 4584095 = 6876143) B6876143
theorem B3056063 : Blo 2035435 3056063 := bstep (se 1 (by rfl) ⟨2292047, by rfl⟩ : syracuseStep 3056063 = 4584095) B4584095
theorem B2037375 : Blo 2035435 2037375 := bstep (se 1 (by rfl) ⟨1528031, by rfl⟩ : syracuseStep 2037375 = 3056063) B3056063
theorem B3056069 : Blo 2035435 3056069 := bbase (se 4 (by rfl) ⟨286506, by rfl⟩ : syracuseStep 3056069 = 573013) (by norm_num)
theorem B2037379 : Blo 2035435 2037379 := bstep (se 1 (by rfl) ⟨1528034, by rfl⟩ : syracuseStep 2037379 = 3056069) B3056069
theorem B3438085 : Blo 2035435 3438085 := bbase (se 4 (by rfl) ⟨322320, by rfl⟩ : syracuseStep 3438085 = 644641) (by norm_num)
theorem B4584113 : Blo 2035435 4584113 := bstep (se 2 (by rfl) ⟨1719042, by rfl⟩ : syracuseStep 4584113 = 3438085) B3438085
theorem B3056075 : Blo 2035435 3056075 := bstep (se 1 (by rfl) ⟨2292056, by rfl⟩ : syracuseStep 3056075 = 4584113) B4584113
theorem B2037383 : Blo 2035435 2037383 := bstep (se 1 (by rfl) ⟨1528037, by rfl⟩ : syracuseStep 2037383 = 3056075) B3056075
theorem B2292061 : Blo 2035435 2292061 := bbase (se 3 (by rfl) ⟨429761, by rfl⟩ : syracuseStep 2292061 = 859523) (by norm_num)
theorem B3056081 : Blo 2035435 3056081 := bstep (se 2 (by rfl) ⟨1146030, by rfl⟩ : syracuseStep 3056081 = 2292061) B2292061
theorem B2037387 : Blo 2035435 2037387 := bstep (se 1 (by rfl) ⟨1528040, by rfl⟩ : syracuseStep 2037387 = 3056081) B3056081
theorem B6876197 : Blo 2035435 6876197 := bbase (se 4 (by rfl) ⟨644643, by rfl⟩ : syracuseStep 6876197 = 1289287) (by norm_num)
theorem B4584131 : Blo 2035435 4584131 := bstep (se 1 (by rfl) ⟨3438098, by rfl⟩ : syracuseStep 4584131 = 6876197) B6876197
theorem B3056087 : Blo 2035435 3056087 := bstep (se 1 (by rfl) ⟨2292065, by rfl⟩ : syracuseStep 3056087 = 4584131) B4584131
theorem B2037391 : Blo 2035435 2037391 := bstep (se 1 (by rfl) ⟨1528043, by rfl⟩ : syracuseStep 2037391 = 3056087) B3056087
theorem B3056093 : Blo 2035435 3056093 := bbase (se 3 (by rfl) ⟨573017, by rfl⟩ : syracuseStep 3056093 = 1146035) (by norm_num)
theorem B2037395 : Blo 2035435 2037395 := bstep (se 1 (by rfl) ⟨1528046, by rfl⟩ : syracuseStep 2037395 = 3056093) B3056093
theorem B4584149 : Blo 2035435 4584149 := bbase (se 7 (by rfl) ⟨53720, by rfl⟩ : syracuseStep 4584149 = 107441) (by norm_num)
theorem B3056099 : Blo 2035435 3056099 := bstep (se 1 (by rfl) ⟨2292074, by rfl⟩ : syracuseStep 3056099 = 4584149) B4584149
theorem B2037399 : Blo 2035435 2037399 := bstep (se 1 (by rfl) ⟨1528049, by rfl⟩ : syracuseStep 2037399 = 3056099) B3056099
theorem B8702741 : Blo 2035435 8702741 := bbase (se 6 (by rfl) ⟨203970, by rfl⟩ : syracuseStep 8702741 = 407941) (by norm_num)
theorem B5801827 : Blo 2035435 5801827 := bstep (se 1 (by rfl) ⟨4351370, by rfl⟩ : syracuseStep 5801827 = 8702741) B8702741
theorem B7735769 : Blo 2035435 7735769 := bstep (se 2 (by rfl) ⟨2900913, by rfl⟩ : syracuseStep 7735769 = 5801827) B5801827
theorem B5157179 : Blo 2035435 5157179 := bstep (se 1 (by rfl) ⟨3867884, by rfl⟩ : syracuseStep 5157179 = 7735769) B7735769
theorem B3438119 : Blo 2035435 3438119 := bstep (se 1 (by rfl) ⟨2578589, by rfl⟩ : syracuseStep 3438119 = 5157179) B5157179
theorem B2292079 : Blo 2035435 2292079 := bstep (se 1 (by rfl) ⟨1719059, by rfl⟩ : syracuseStep 2292079 = 3438119) B3438119
theorem B3056105 : Blo 2035435 3056105 := bstep (se 2 (by rfl) ⟨1146039, by rfl⟩ : syracuseStep 3056105 = 2292079) B2292079
theorem B2037403 : Blo 2035435 2037403 := bstep (se 1 (by rfl) ⟨1528052, by rfl⟩ : syracuseStep 2037403 = 3056105) B3056105
theorem B18840437 : Blo 2035435 18840437 := bbase (se 5 (by rfl) ⟨883145, by rfl⟩ : syracuseStep 18840437 = 1766291) (by norm_num)
theorem B12560291 : Blo 2035435 12560291 := bstep (se 1 (by rfl) ⟨9420218, by rfl⟩ : syracuseStep 12560291 = 18840437) B18840437
theorem B8373527 : Blo 2035435 8373527 := bstep (se 1 (by rfl) ⟨6280145, by rfl⟩ : syracuseStep 8373527 = 12560291) B12560291
theorem B5582351 : Blo 2035435 5582351 := bstep (se 1 (by rfl) ⟨4186763, by rfl⟩ : syracuseStep 5582351 = 8373527) B8373527
theorem B14886269 : Blo 2035435 14886269 := bstep (se 3 (by rfl) ⟨2791175, by rfl⟩ : syracuseStep 14886269 = 5582351) B5582351
theorem B9924179 : Blo 2035435 9924179 := bstep (se 1 (by rfl) ⟨7443134, by rfl⟩ : syracuseStep 9924179 = 14886269) B14886269
theorem B26464477 : Blo 2035435 26464477 := bstep (se 3 (by rfl) ⟨4962089, by rfl⟩ : syracuseStep 26464477 = 9924179) B9924179
theorem B35285969 : Blo 2035435 35285969 := bstep (se 2 (by rfl) ⟨13232238, by rfl⟩ : syracuseStep 35285969 = 26464477) B26464477
theorem B94095917 : Blo 2035435 94095917 := bstep (se 3 (by rfl) ⟨17642984, by rfl⟩ : syracuseStep 94095917 = 35285969) B35285969
theorem B62730611 : Blo 2035435 62730611 := bstep (se 1 (by rfl) ⟨47047958, by rfl⟩ : syracuseStep 62730611 = 94095917) B94095917
theorem B41820407 : Blo 2035435 41820407 := bstep (se 1 (by rfl) ⟨31365305, by rfl⟩ : syracuseStep 41820407 = 62730611) B62730611
theorem B27880271 : Blo 2035435 27880271 := bstep (se 1 (by rfl) ⟨20910203, by rfl⟩ : syracuseStep 27880271 = 41820407) B41820407
theorem B18586847 : Blo 2035435 18586847 := bstep (se 1 (by rfl) ⟨13940135, by rfl⟩ : syracuseStep 18586847 = 27880271) B27880271
theorem B12391231 : Blo 2035435 12391231 := bstep (se 1 (by rfl) ⟨9293423, by rfl⟩ : syracuseStep 12391231 = 18586847) B18586847
theorem B16521641 : Blo 2035435 16521641 := bstep (se 2 (by rfl) ⟨6195615, by rfl⟩ : syracuseStep 16521641 = 12391231) B12391231
theorem B11014427 : Blo 2035435 11014427 := bstep (se 1 (by rfl) ⟨8260820, by rfl⟩ : syracuseStep 11014427 = 16521641) B16521641
theorem B29371805 : Blo 2035435 29371805 := bstep (se 3 (by rfl) ⟨5507213, by rfl⟩ : syracuseStep 29371805 = 11014427) B11014427
theorem B19581203 : Blo 2035435 19581203 := bstep (se 1 (by rfl) ⟨14685902, by rfl⟩ : syracuseStep 19581203 = 29371805) B29371805
theorem B13054135 : Blo 2035435 13054135 := bstep (se 1 (by rfl) ⟨9790601, by rfl⟩ : syracuseStep 13054135 = 19581203) B19581203
theorem B17405513 : Blo 2035435 17405513 := bstep (se 2 (by rfl) ⟨6527067, by rfl⟩ : syracuseStep 17405513 = 13054135) B13054135
theorem B11603675 : Blo 2035435 11603675 := bstep (se 1 (by rfl) ⟨8702756, by rfl⟩ : syracuseStep 11603675 = 17405513) B17405513
theorem B7735783 : Blo 2035435 7735783 := bstep (se 1 (by rfl) ⟨5801837, by rfl⟩ : syracuseStep 7735783 = 11603675) B11603675
theorem B10314377 : Blo 2035435 10314377 := bstep (se 2 (by rfl) ⟨3867891, by rfl⟩ : syracuseStep 10314377 = 7735783) B7735783
theorem B6876251 : Blo 2035435 6876251 := bstep (se 1 (by rfl) ⟨5157188, by rfl⟩ : syracuseStep 6876251 = 10314377) B10314377
theorem B4584167 : Blo 2035435 4584167 := bstep (se 1 (by rfl) ⟨3438125, by rfl⟩ : syracuseStep 4584167 = 6876251) B6876251
theorem B3056111 : Blo 2035435 3056111 := bstep (se 1 (by rfl) ⟨2292083, by rfl⟩ : syracuseStep 3056111 = 4584167) B4584167
theorem B2037407 : Blo 2035435 2037407 := bstep (se 1 (by rfl) ⟨1528055, by rfl⟩ : syracuseStep 2037407 = 3056111) B3056111
theorem B3056117 : Blo 2035435 3056117 := bbase (se 5 (by rfl) ⟨143255, by rfl⟩ : syracuseStep 3056117 = 286511) (by norm_num)
theorem B2037411 : Blo 2035435 2037411 := bstep (se 1 (by rfl) ⟨1528058, by rfl⟩ : syracuseStep 2037411 = 3056117) B3056117
theorem B5801861 : Blo 2035435 5801861 := bbase (se 4 (by rfl) ⟨543924, by rfl⟩ : syracuseStep 5801861 = 1087849) (by norm_num)
theorem B3867907 : Blo 2035435 3867907 := bstep (se 1 (by rfl) ⟨2900930, by rfl⟩ : syracuseStep 3867907 = 5801861) B5801861
theorem B5157209 : Blo 2035435 5157209 := bstep (se 2 (by rfl) ⟨1933953, by rfl⟩ : syracuseStep 5157209 = 3867907) B3867907
theorem B3438139 : Blo 2035435 3438139 := bstep (se 1 (by rfl) ⟨2578604, by rfl⟩ : syracuseStep 3438139 = 5157209) B5157209
theorem B4584185 : Blo 2035435 4584185 := bstep (se 2 (by rfl) ⟨1719069, by rfl⟩ : syracuseStep 4584185 = 3438139) B3438139
theorem B3056123 : Blo 2035435 3056123 := bstep (se 1 (by rfl) ⟨2292092, by rfl⟩ : syracuseStep 3056123 = 4584185) B4584185
theorem B2037415 : Blo 2035435 2037415 := bstep (se 1 (by rfl) ⟨1528061, by rfl⟩ : syracuseStep 2037415 = 3056123) B3056123
theorem B2292097 : Blo 2035435 2292097 := bbase (se 2 (by rfl) ⟨859536, by rfl⟩ : syracuseStep 2292097 = 1719073) (by norm_num)
theorem B3056129 : Blo 2035435 3056129 := bstep (se 2 (by rfl) ⟨1146048, by rfl⟩ : syracuseStep 3056129 = 2292097) B2292097
theorem B2037419 : Blo 2035435 2037419 := bstep (se 1 (by rfl) ⟨1528064, by rfl⟩ : syracuseStep 2037419 = 3056129) B3056129
theorem B5157229 : Blo 2035435 5157229 := bbase (se 3 (by rfl) ⟨966980, by rfl⟩ : syracuseStep 5157229 = 1933961) (by norm_num)
theorem B6876305 : Blo 2035435 6876305 := bstep (se 2 (by rfl) ⟨2578614, by rfl⟩ : syracuseStep 6876305 = 5157229) B5157229
theorem B4584203 : Blo 2035435 4584203 := bstep (se 1 (by rfl) ⟨3438152, by rfl⟩ : syracuseStep 4584203 = 6876305) B6876305
theorem B3056135 : Blo 2035435 3056135 := bstep (se 1 (by rfl) ⟨2292101, by rfl⟩ : syracuseStep 3056135 = 4584203) B4584203
theorem B2037423 : Blo 2035435 2037423 := bstep (se 1 (by rfl) ⟨1528067, by rfl⟩ : syracuseStep 2037423 = 3056135) B3056135
theorem B3056141 : Blo 2035435 3056141 := bbase (se 3 (by rfl) ⟨573026, by rfl⟩ : syracuseStep 3056141 = 1146053) (by norm_num)
theorem B2037427 : Blo 2035435 2037427 := bstep (se 1 (by rfl) ⟨1528070, by rfl⟩ : syracuseStep 2037427 = 3056141) B3056141
theorem B4584221 : Blo 2035435 4584221 := bbase (se 3 (by rfl) ⟨859541, by rfl⟩ : syracuseStep 4584221 = 1719083) (by norm_num)
theorem B3056147 : Blo 2035435 3056147 := bstep (se 1 (by rfl) ⟨2292110, by rfl⟩ : syracuseStep 3056147 = 4584221) B4584221
theorem B2037431 : Blo 2035435 2037431 := bstep (se 1 (by rfl) ⟨1528073, by rfl⟩ : syracuseStep 2037431 = 3056147) B3056147
theorem B3438173 : Blo 2035435 3438173 := bbase (se 3 (by rfl) ⟨644657, by rfl⟩ : syracuseStep 3438173 = 1289315) (by norm_num)
theorem B2292115 : Blo 2035435 2292115 := bstep (se 1 (by rfl) ⟨1719086, by rfl⟩ : syracuseStep 2292115 = 3438173) B3438173
theorem B3056153 : Blo 2035435 3056153 := bstep (se 2 (by rfl) ⟨1146057, by rfl⟩ : syracuseStep 3056153 = 2292115) B2292115
theorem B2037435 : Blo 2035435 2037435 := bstep (se 1 (by rfl) ⟨1528076, by rfl⟩ : syracuseStep 2037435 = 3056153) B3056153
theorem C0 (j : ℕ) (h1 : 508858 ≤ j) (h2 : j ≤ 509358) : Blo 2035435 (4 * j + 3) := by
  interval_cases j
  · exact B2035435
  · exact B2035439
  · exact B2035443
  · exact B2035447
  · exact B2035451
  · exact B2035455
  · exact B2035459
  · exact B2035463
  · exact B2035467
  · exact B2035471
  · exact B2035475
  · exact B2035479
  · exact B2035483
  · exact B2035487
  · exact B2035491
  · exact B2035495
  · exact B2035499
  · exact B2035503
  · exact B2035507
  · exact B2035511
  · exact B2035515
  · exact B2035519
  · exact B2035523
  · exact B2035527
  · exact B2035531
  · exact B2035535
  · exact B2035539
  · exact B2035543
  · exact B2035547
  · exact B2035551
  · exact B2035555
  · exact B2035559
  · exact B2035563
  · exact B2035567
  · exact B2035571
  · exact B2035575
  · exact B2035579
  · exact B2035583
  · exact B2035587
  · exact B2035591
  · exact B2035595
  · exact B2035599
  · exact B2035603
  · exact B2035607
  · exact B2035611
  · exact B2035615
  · exact B2035619
  · exact B2035623
  · exact B2035627
  · exact B2035631
  · exact B2035635
  · exact B2035639
  · exact B2035643
  · exact B2035647
  · exact B2035651
  · exact B2035655
  · exact B2035659
  · exact B2035663
  · exact B2035667
  · exact B2035671
  · exact B2035675
  · exact B2035679
  · exact B2035683
  · exact B2035687
  · exact B2035691
  · exact B2035695
  · exact B2035699
  · exact B2035703
  · exact B2035707
  · exact B2035711
  · exact B2035715
  · exact B2035719
  · exact B2035723
  · exact B2035727
  · exact B2035731
  · exact B2035735
  · exact B2035739
  · exact B2035743
  · exact B2035747
  · exact B2035751
  · exact B2035755
  · exact B2035759
  · exact B2035763
  · exact B2035767
  · exact B2035771
  · exact B2035775
  · exact B2035779
  · exact B2035783
  · exact B2035787
  · exact B2035791
  · exact B2035795
  · exact B2035799
  · exact B2035803
  · exact B2035807
  · exact B2035811
  · exact B2035815
  · exact B2035819
  · exact B2035823
  · exact B2035827
  · exact B2035831
  · exact B2035835
  · exact B2035839
  · exact B2035843
  · exact B2035847
  · exact B2035851
  · exact B2035855
  · exact B2035859
  · exact B2035863
  · exact B2035867
  · exact B2035871
  · exact B2035875
  · exact B2035879
  · exact B2035883
  · exact B2035887
  · exact B2035891
  · exact B2035895
  · exact B2035899
  · exact B2035903
  · exact B2035907
  · exact B2035911
  · exact B2035915
  · exact B2035919
  · exact B2035923
  · exact B2035927
  · exact B2035931
  · exact B2035935
  · exact B2035939
  · exact B2035943
  · exact B2035947
  · exact B2035951
  · exact B2035955
  · exact B2035959
  · exact B2035963
  · exact B2035967
  · exact B2035971
  · exact B2035975
  · exact B2035979
  · exact B2035983
  · exact B2035987
  · exact B2035991
  · exact B2035995
  · exact B2035999
  · exact B2036003
  · exact B2036007
  · exact B2036011
  · exact B2036015
  · exact B2036019
  · exact B2036023
  · exact B2036027
  · exact B2036031
  · exact B2036035
  · exact B2036039
  · exact B2036043
  · exact B2036047
  · exact B2036051
  · exact B2036055
  · exact B2036059
  · exact B2036063
  · exact B2036067
  · exact B2036071
  · exact B2036075
  · exact B2036079
  · exact B2036083
  · exact B2036087
  · exact B2036091
  · exact B2036095
  · exact B2036099
  · exact B2036103
  · exact B2036107
  · exact B2036111
  · exact B2036115
  · exact B2036119
  · exact B2036123
  · exact B2036127
  · exact B2036131
  · exact B2036135
  · exact B2036139
  · exact B2036143
  · exact B2036147
  · exact B2036151
  · exact B2036155
  · exact B2036159
  · exact B2036163
  · exact B2036167
  · exact B2036171
  · exact B2036175
  · exact B2036179
  · exact B2036183
  · exact B2036187
  · exact B2036191
  · exact B2036195
  · exact B2036199
  · exact B2036203
  · exact B2036207
  · exact B2036211
  · exact B2036215
  · exact B2036219
  · exact B2036223
  · exact B2036227
  · exact B2036231
  · exact B2036235
  · exact B2036239
  · exact B2036243
  · exact B2036247
  · exact B2036251
  · exact B2036255
  · exact B2036259
  · exact B2036263
  · exact B2036267
  · exact B2036271
  · exact B2036275
  · exact B2036279
  · exact B2036283
  · exact B2036287
  · exact B2036291
  · exact B2036295
  · exact B2036299
  · exact B2036303
  · exact B2036307
  · exact B2036311
  · exact B2036315
  · exact B2036319
  · exact B2036323
  · exact B2036327
  · exact B2036331
  · exact B2036335
  · exact B2036339
  · exact B2036343
  · exact B2036347
  · exact B2036351
  · exact B2036355
  · exact B2036359
  · exact B2036363
  · exact B2036367
  · exact B2036371
  · exact B2036375
  · exact B2036379
  · exact B2036383
  · exact B2036387
  · exact B2036391
  · exact B2036395
  · exact B2036399
  · exact B2036403
  · exact B2036407
  · exact B2036411
  · exact B2036415
  · exact B2036419
  · exact B2036423
  · exact B2036427
  · exact B2036431
  · exact B2036435
  · exact B2036439
  · exact B2036443
  · exact B2036447
  · exact B2036451
  · exact B2036455
  · exact B2036459
  · exact B2036463
  · exact B2036467
  · exact B2036471
  · exact B2036475
  · exact B2036479
  · exact B2036483
  · exact B2036487
  · exact B2036491
  · exact B2036495
  · exact B2036499
  · exact B2036503
  · exact B2036507
  · exact B2036511
  · exact B2036515
  · exact B2036519
  · exact B2036523
  · exact B2036527
  · exact B2036531
  · exact B2036535
  · exact B2036539
  · exact B2036543
  · exact B2036547
  · exact B2036551
  · exact B2036555
  · exact B2036559
  · exact B2036563
  · exact B2036567
  · exact B2036571
  · exact B2036575
  · exact B2036579
  · exact B2036583
  · exact B2036587
  · exact B2036591
  · exact B2036595
  · exact B2036599
  · exact B2036603
  · exact B2036607
  · exact B2036611
  · exact B2036615
  · exact B2036619
  · exact B2036623
  · exact B2036627
  · exact B2036631
  · exact B2036635
  · exact B2036639
  · exact B2036643
  · exact B2036647
  · exact B2036651
  · exact B2036655
  · exact B2036659
  · exact B2036663
  · exact B2036667
  · exact B2036671
  · exact B2036675
  · exact B2036679
  · exact B2036683
  · exact B2036687
  · exact B2036691
  · exact B2036695
  · exact B2036699
  · exact B2036703
  · exact B2036707
  · exact B2036711
  · exact B2036715
  · exact B2036719
  · exact B2036723
  · exact B2036727
  · exact B2036731
  · exact B2036735
  · exact B2036739
  · exact B2036743
  · exact B2036747
  · exact B2036751
  · exact B2036755
  · exact B2036759
  · exact B2036763
  · exact B2036767
  · exact B2036771
  · exact B2036775
  · exact B2036779
  · exact B2036783
  · exact B2036787
  · exact B2036791
  · exact B2036795
  · exact B2036799
  · exact B2036803
  · exact B2036807
  · exact B2036811
  · exact B2036815
  · exact B2036819
  · exact B2036823
  · exact B2036827
  · exact B2036831
  · exact B2036835
  · exact B2036839
  · exact B2036843
  · exact B2036847
  · exact B2036851
  · exact B2036855
  · exact B2036859
  · exact B2036863
  · exact B2036867
  · exact B2036871
  · exact B2036875
  · exact B2036879
  · exact B2036883
  · exact B2036887
  · exact B2036891
  · exact B2036895
  · exact B2036899
  · exact B2036903
  · exact B2036907
  · exact B2036911
  · exact B2036915
  · exact B2036919
  · exact B2036923
  · exact B2036927
  · exact B2036931
  · exact B2036935
  · exact B2036939
  · exact B2036943
  · exact B2036947
  · exact B2036951
  · exact B2036955
  · exact B2036959
  · exact B2036963
  · exact B2036967
  · exact B2036971
  · exact B2036975
  · exact B2036979
  · exact B2036983
  · exact B2036987
  · exact B2036991
  · exact B2036995
  · exact B2036999
  · exact B2037003
  · exact B2037007
  · exact B2037011
  · exact B2037015
  · exact B2037019
  · exact B2037023
  · exact B2037027
  · exact B2037031
  · exact B2037035
  · exact B2037039
  · exact B2037043
  · exact B2037047
  · exact B2037051
  · exact B2037055
  · exact B2037059
  · exact B2037063
  · exact B2037067
  · exact B2037071
  · exact B2037075
  · exact B2037079
  · exact B2037083
  · exact B2037087
  · exact B2037091
  · exact B2037095
  · exact B2037099
  · exact B2037103
  · exact B2037107
  · exact B2037111
  · exact B2037115
  · exact B2037119
  · exact B2037123
  · exact B2037127
  · exact B2037131
  · exact B2037135
  · exact B2037139
  · exact B2037143
  · exact B2037147
  · exact B2037151
  · exact B2037155
  · exact B2037159
  · exact B2037163
  · exact B2037167
  · exact B2037171
  · exact B2037175
  · exact B2037179
  · exact B2037183
  · exact B2037187
  · exact B2037191
  · exact B2037195
  · exact B2037199
  · exact B2037203
  · exact B2037207
  · exact B2037211
  · exact B2037215
  · exact B2037219
  · exact B2037223
  · exact B2037227
  · exact B2037231
  · exact B2037235
  · exact B2037239
  · exact B2037243
  · exact B2037247
  · exact B2037251
  · exact B2037255
  · exact B2037259
  · exact B2037263
  · exact B2037267
  · exact B2037271
  · exact B2037275
  · exact B2037279
  · exact B2037283
  · exact B2037287
  · exact B2037291
  · exact B2037295
  · exact B2037299
  · exact B2037303
  · exact B2037307
  · exact B2037311
  · exact B2037315
  · exact B2037319
  · exact B2037323
  · exact B2037327
  · exact B2037331
  · exact B2037335
  · exact B2037339
  · exact B2037343
  · exact B2037347
  · exact B2037351
  · exact B2037355
  · exact B2037359
  · exact B2037363
  · exact B2037367
  · exact B2037371
  · exact B2037375
  · exact B2037379
  · exact B2037383
  · exact B2037387
  · exact B2037391
  · exact B2037395
  · exact B2037399
  · exact B2037403
  · exact B2037407
  · exact B2037411
  · exact B2037415
  · exact B2037419
  · exact B2037423
  · exact B2037427
  · exact B2037431
  · exact B2037435
theorem solution (m : ℕ) (hlo : 2035435 ≤ m) (hhi : m ≤ 2037435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 508858 ≤ j := by omega
    have hj2 : j ≤ 509358 := by omega
    have hb : Blo 2035435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
