-- Prove2me | solution 1 for syracuse_descends_range_2183435_2185435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:59.28532+00:00
-- url     : https://prove2.me/submissions/84a3ca8c-5e51-48bd-af09-fcc52a135968

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

theorem B2456365 : Blo 2183435 2456365 := bbase (se 3 (by rfl) ⟨460568, by rfl⟩ : syracuseStep 2456365 = 921137) (by norm_num)
theorem B3275153 : Blo 2183435 3275153 := bstep (se 2 (by rfl) ⟨1228182, by rfl⟩ : syracuseStep 3275153 = 2456365) B2456365
theorem B2183435 : Blo 2183435 2183435 := bstep (se 1 (by rfl) ⟨1637576, by rfl⟩ : syracuseStep 2183435 = 3275153) B3275153
theorem B7369109 : Blo 2183435 7369109 := bbase (se 6 (by rfl) ⟨172713, by rfl⟩ : syracuseStep 7369109 = 345427) (by norm_num)
theorem B4912739 : Blo 2183435 4912739 := bstep (se 1 (by rfl) ⟨3684554, by rfl⟩ : syracuseStep 4912739 = 7369109) B7369109
theorem B3275159 : Blo 2183435 3275159 := bstep (se 1 (by rfl) ⟨2456369, by rfl⟩ : syracuseStep 3275159 = 4912739) B4912739
theorem B2183439 : Blo 2183435 2183439 := bstep (se 1 (by rfl) ⟨1637579, by rfl⟩ : syracuseStep 2183439 = 3275159) B3275159
theorem B3275165 : Blo 2183435 3275165 := bbase (se 3 (by rfl) ⟨614093, by rfl⟩ : syracuseStep 3275165 = 1228187) (by norm_num)
theorem B2183443 : Blo 2183435 2183443 := bstep (se 1 (by rfl) ⟨1637582, by rfl⟩ : syracuseStep 2183443 = 3275165) B3275165
theorem B4912757 : Blo 2183435 4912757 := bbase (se 5 (by rfl) ⟨230285, by rfl⟩ : syracuseStep 4912757 = 460571) (by norm_num)
theorem B3275171 : Blo 2183435 3275171 := bstep (se 1 (by rfl) ⟨2456378, by rfl⟩ : syracuseStep 3275171 = 4912757) B4912757
theorem B2183447 : Blo 2183435 2183447 := bstep (se 1 (by rfl) ⟨1637585, by rfl⟩ : syracuseStep 2183447 = 3275171) B3275171
theorem B4259029 : Blo 2183435 4259029 := bbase (se 7 (by rfl) ⟨49910, by rfl⟩ : syracuseStep 4259029 = 99821) (by norm_num)
theorem B5678705 : Blo 2183435 5678705 := bstep (se 2 (by rfl) ⟨2129514, by rfl⟩ : syracuseStep 5678705 = 4259029) B4259029
theorem B15143213 : Blo 2183435 15143213 := bstep (se 3 (by rfl) ⟨2839352, by rfl⟩ : syracuseStep 15143213 = 5678705) B5678705
theorem B10095475 : Blo 2183435 10095475 := bstep (se 1 (by rfl) ⟨7571606, by rfl⟩ : syracuseStep 10095475 = 15143213) B15143213
theorem B13460633 : Blo 2183435 13460633 := bstep (se 2 (by rfl) ⟨5047737, by rfl⟩ : syracuseStep 13460633 = 10095475) B10095475
theorem B8973755 : Blo 2183435 8973755 := bstep (se 1 (by rfl) ⟨6730316, by rfl⟩ : syracuseStep 8973755 = 13460633) B13460633
theorem B5982503 : Blo 2183435 5982503 := bstep (se 1 (by rfl) ⟨4486877, by rfl⟩ : syracuseStep 5982503 = 8973755) B8973755
theorem B63813365 : Blo 2183435 63813365 := bstep (se 5 (by rfl) ⟨2991251, by rfl⟩ : syracuseStep 63813365 = 5982503) B5982503
theorem B42542243 : Blo 2183435 42542243 := bstep (se 1 (by rfl) ⟨31906682, by rfl⟩ : syracuseStep 42542243 = 63813365) B63813365
theorem B28361495 : Blo 2183435 28361495 := bstep (se 1 (by rfl) ⟨21271121, by rfl⟩ : syracuseStep 28361495 = 42542243) B42542243
theorem B18907663 : Blo 2183435 18907663 := bstep (se 1 (by rfl) ⟨14180747, by rfl⟩ : syracuseStep 18907663 = 28361495) B28361495
theorem B25210217 : Blo 2183435 25210217 := bstep (se 2 (by rfl) ⟨9453831, by rfl⟩ : syracuseStep 25210217 = 18907663) B18907663
theorem B16806811 : Blo 2183435 16806811 := bstep (se 1 (by rfl) ⟨12605108, by rfl⟩ : syracuseStep 16806811 = 25210217) B25210217
theorem B22409081 : Blo 2183435 22409081 := bstep (se 2 (by rfl) ⟨8403405, by rfl⟩ : syracuseStep 22409081 = 16806811) B16806811
theorem B14939387 : Blo 2183435 14939387 := bstep (se 1 (by rfl) ⟨11204540, by rfl⟩ : syracuseStep 14939387 = 22409081) B22409081
theorem B9959591 : Blo 2183435 9959591 := bstep (se 1 (by rfl) ⟨7469693, by rfl⟩ : syracuseStep 9959591 = 14939387) B14939387
theorem B6639727 : Blo 2183435 6639727 := bstep (se 1 (by rfl) ⟨4979795, by rfl⟩ : syracuseStep 6639727 = 9959591) B9959591
theorem B8852969 : Blo 2183435 8852969 := bstep (se 2 (by rfl) ⟨3319863, by rfl⟩ : syracuseStep 8852969 = 6639727) B6639727
theorem B5901979 : Blo 2183435 5901979 := bstep (se 1 (by rfl) ⟨4426484, by rfl⟩ : syracuseStep 5901979 = 8852969) B8852969
theorem B7869305 : Blo 2183435 7869305 := bstep (se 2 (by rfl) ⟨2950989, by rfl⟩ : syracuseStep 7869305 = 5901979) B5901979
theorem B5246203 : Blo 2183435 5246203 := bstep (se 1 (by rfl) ⟨3934652, by rfl⟩ : syracuseStep 5246203 = 7869305) B7869305
theorem B6994937 : Blo 2183435 6994937 := bstep (se 2 (by rfl) ⟨2623101, by rfl⟩ : syracuseStep 6994937 = 5246203) B5246203
theorem B18653165 : Blo 2183435 18653165 := bstep (se 3 (by rfl) ⟨3497468, by rfl⟩ : syracuseStep 18653165 = 6994937) B6994937
theorem B12435443 : Blo 2183435 12435443 := bstep (se 1 (by rfl) ⟨9326582, by rfl⟩ : syracuseStep 12435443 = 18653165) B18653165
theorem B8290295 : Blo 2183435 8290295 := bstep (se 1 (by rfl) ⟨6217721, by rfl⟩ : syracuseStep 8290295 = 12435443) B12435443
theorem B5526863 : Blo 2183435 5526863 := bstep (se 1 (by rfl) ⟨4145147, by rfl⟩ : syracuseStep 5526863 = 8290295) B8290295
theorem B3684575 : Blo 2183435 3684575 := bstep (se 1 (by rfl) ⟨2763431, by rfl⟩ : syracuseStep 3684575 = 5526863) B5526863
theorem B2456383 : Blo 2183435 2456383 := bstep (se 1 (by rfl) ⟨1842287, by rfl⟩ : syracuseStep 2456383 = 3684575) B3684575
theorem B3275177 : Blo 2183435 3275177 := bstep (se 2 (by rfl) ⟨1228191, by rfl⟩ : syracuseStep 3275177 = 2456383) B2456383
theorem B2183451 : Blo 2183435 2183451 := bstep (se 1 (by rfl) ⟨1637588, by rfl⟩ : syracuseStep 2183451 = 3275177) B3275177
theorem B8290309 : Blo 2183435 8290309 := bbase (se 4 (by rfl) ⟨777216, by rfl⟩ : syracuseStep 8290309 = 1554433) (by norm_num)
theorem B11053745 : Blo 2183435 11053745 := bstep (se 2 (by rfl) ⟨4145154, by rfl⟩ : syracuseStep 11053745 = 8290309) B8290309
theorem B7369163 : Blo 2183435 7369163 := bstep (se 1 (by rfl) ⟨5526872, by rfl⟩ : syracuseStep 7369163 = 11053745) B11053745
theorem B4912775 : Blo 2183435 4912775 := bstep (se 1 (by rfl) ⟨3684581, by rfl⟩ : syracuseStep 4912775 = 7369163) B7369163
theorem B3275183 : Blo 2183435 3275183 := bstep (se 1 (by rfl) ⟨2456387, by rfl⟩ : syracuseStep 3275183 = 4912775) B4912775
theorem B2183455 : Blo 2183435 2183455 := bstep (se 1 (by rfl) ⟨1637591, by rfl⟩ : syracuseStep 2183455 = 3275183) B3275183
theorem B3275189 : Blo 2183435 3275189 := bbase (se 5 (by rfl) ⟨153524, by rfl⟩ : syracuseStep 3275189 = 307049) (by norm_num)
theorem B2183459 : Blo 2183435 2183459 := bstep (se 1 (by rfl) ⟨1637594, by rfl⟩ : syracuseStep 2183459 = 3275189) B3275189
theorem B5526893 : Blo 2183435 5526893 := bbase (se 3 (by rfl) ⟨1036292, by rfl⟩ : syracuseStep 5526893 = 2072585) (by norm_num)
theorem B3684595 : Blo 2183435 3684595 := bstep (se 1 (by rfl) ⟨2763446, by rfl⟩ : syracuseStep 3684595 = 5526893) B5526893
theorem B4912793 : Blo 2183435 4912793 := bstep (se 2 (by rfl) ⟨1842297, by rfl⟩ : syracuseStep 4912793 = 3684595) B3684595
theorem B3275195 : Blo 2183435 3275195 := bstep (se 1 (by rfl) ⟨2456396, by rfl⟩ : syracuseStep 3275195 = 4912793) B4912793
theorem B2183463 : Blo 2183435 2183463 := bstep (se 1 (by rfl) ⟨1637597, by rfl⟩ : syracuseStep 2183463 = 3275195) B3275195
theorem B2456401 : Blo 2183435 2456401 := bbase (se 2 (by rfl) ⟨921150, by rfl⟩ : syracuseStep 2456401 = 1842301) (by norm_num)
theorem B3275201 : Blo 2183435 3275201 := bstep (se 2 (by rfl) ⟨1228200, by rfl⟩ : syracuseStep 3275201 = 2456401) B2456401
theorem B2183467 : Blo 2183435 2183467 := bstep (se 1 (by rfl) ⟨1637600, by rfl⟩ : syracuseStep 2183467 = 3275201) B3275201
theorem B3497501 : Blo 2183435 3497501 := bbase (se 3 (by rfl) ⟨655781, by rfl⟩ : syracuseStep 3497501 = 1311563) (by norm_num)
theorem B2331667 : Blo 2183435 2331667 := bstep (se 1 (by rfl) ⟨1748750, by rfl⟩ : syracuseStep 2331667 = 3497501) B3497501
theorem B3108889 : Blo 2183435 3108889 := bstep (se 2 (by rfl) ⟨1165833, by rfl⟩ : syracuseStep 3108889 = 2331667) B2331667
theorem B4145185 : Blo 2183435 4145185 := bstep (se 2 (by rfl) ⟨1554444, by rfl⟩ : syracuseStep 4145185 = 3108889) B3108889
theorem B5526913 : Blo 2183435 5526913 := bstep (se 2 (by rfl) ⟨2072592, by rfl⟩ : syracuseStep 5526913 = 4145185) B4145185
theorem B7369217 : Blo 2183435 7369217 := bstep (se 2 (by rfl) ⟨2763456, by rfl⟩ : syracuseStep 7369217 = 5526913) B5526913
theorem B4912811 : Blo 2183435 4912811 := bstep (se 1 (by rfl) ⟨3684608, by rfl⟩ : syracuseStep 4912811 = 7369217) B7369217
theorem B3275207 : Blo 2183435 3275207 := bstep (se 1 (by rfl) ⟨2456405, by rfl⟩ : syracuseStep 3275207 = 4912811) B4912811
theorem B2183471 : Blo 2183435 2183471 := bstep (se 1 (by rfl) ⟨1637603, by rfl⟩ : syracuseStep 2183471 = 3275207) B3275207
theorem B3275213 : Blo 2183435 3275213 := bbase (se 3 (by rfl) ⟨614102, by rfl⟩ : syracuseStep 3275213 = 1228205) (by norm_num)
theorem B2183475 : Blo 2183435 2183475 := bstep (se 1 (by rfl) ⟨1637606, by rfl⟩ : syracuseStep 2183475 = 3275213) B3275213
theorem B4912829 : Blo 2183435 4912829 := bbase (se 3 (by rfl) ⟨921155, by rfl⟩ : syracuseStep 4912829 = 1842311) (by norm_num)
theorem B3275219 : Blo 2183435 3275219 := bstep (se 1 (by rfl) ⟨2456414, by rfl⟩ : syracuseStep 3275219 = 4912829) B4912829
theorem B2183479 : Blo 2183435 2183479 := bstep (se 1 (by rfl) ⟨1637609, by rfl⟩ : syracuseStep 2183479 = 3275219) B3275219
theorem B3684629 : Blo 2183435 3684629 := bbase (se 6 (by rfl) ⟨86358, by rfl⟩ : syracuseStep 3684629 = 172717) (by norm_num)
theorem B2456419 : Blo 2183435 2456419 := bstep (se 1 (by rfl) ⟨1842314, by rfl⟩ : syracuseStep 2456419 = 3684629) B3684629
theorem B3275225 : Blo 2183435 3275225 := bstep (se 2 (by rfl) ⟨1228209, by rfl⟩ : syracuseStep 3275225 = 2456419) B2456419
theorem B2183483 : Blo 2183435 2183483 := bstep (se 1 (by rfl) ⟨1637612, by rfl⟩ : syracuseStep 2183483 = 3275225) B3275225
theorem B3545245 : Blo 2183435 3545245 := bbase (se 3 (by rfl) ⟨664733, by rfl⟩ : syracuseStep 3545245 = 1329467) (by norm_num)
theorem B4726993 : Blo 2183435 4726993 := bstep (se 2 (by rfl) ⟨1772622, by rfl⟩ : syracuseStep 4726993 = 3545245) B3545245
theorem B6302657 : Blo 2183435 6302657 := bstep (se 2 (by rfl) ⟨2363496, by rfl⟩ : syracuseStep 6302657 = 4726993) B4726993
theorem B16807085 : Blo 2183435 16807085 := bstep (se 3 (by rfl) ⟨3151328, by rfl⟩ : syracuseStep 16807085 = 6302657) B6302657
theorem B11204723 : Blo 2183435 11204723 := bstep (se 1 (by rfl) ⟨8403542, by rfl⟩ : syracuseStep 11204723 = 16807085) B16807085
theorem B7469815 : Blo 2183435 7469815 := bstep (se 1 (by rfl) ⟨5602361, by rfl⟩ : syracuseStep 7469815 = 11204723) B11204723
theorem B9959753 : Blo 2183435 9959753 := bstep (se 2 (by rfl) ⟨3734907, by rfl⟩ : syracuseStep 9959753 = 7469815) B7469815
theorem B6639835 : Blo 2183435 6639835 := bstep (se 1 (by rfl) ⟨4979876, by rfl⟩ : syracuseStep 6639835 = 9959753) B9959753
theorem B8853113 : Blo 2183435 8853113 := bstep (se 2 (by rfl) ⟨3319917, by rfl⟩ : syracuseStep 8853113 = 6639835) B6639835
theorem B5902075 : Blo 2183435 5902075 := bstep (se 1 (by rfl) ⟨4426556, by rfl⟩ : syracuseStep 5902075 = 8853113) B8853113
theorem B31477733 : Blo 2183435 31477733 := bstep (se 4 (by rfl) ⟨2951037, by rfl⟩ : syracuseStep 31477733 = 5902075) B5902075
theorem B20985155 : Blo 2183435 20985155 := bstep (se 1 (by rfl) ⟨15738866, by rfl⟩ : syracuseStep 20985155 = 31477733) B31477733
theorem B13990103 : Blo 2183435 13990103 := bstep (se 1 (by rfl) ⟨10492577, by rfl⟩ : syracuseStep 13990103 = 20985155) B20985155
theorem B9326735 : Blo 2183435 9326735 := bstep (se 1 (by rfl) ⟨6995051, by rfl⟩ : syracuseStep 9326735 = 13990103) B13990103
theorem B6217823 : Blo 2183435 6217823 := bstep (se 1 (by rfl) ⟨4663367, by rfl⟩ : syracuseStep 6217823 = 9326735) B9326735
theorem B16580861 : Blo 2183435 16580861 := bstep (se 3 (by rfl) ⟨3108911, by rfl⟩ : syracuseStep 16580861 = 6217823) B6217823
theorem B11053907 : Blo 2183435 11053907 := bstep (se 1 (by rfl) ⟨8290430, by rfl⟩ : syracuseStep 11053907 = 16580861) B16580861
theorem B7369271 : Blo 2183435 7369271 := bstep (se 1 (by rfl) ⟨5526953, by rfl⟩ : syracuseStep 7369271 = 11053907) B11053907
theorem B4912847 : Blo 2183435 4912847 := bstep (se 1 (by rfl) ⟨3684635, by rfl⟩ : syracuseStep 4912847 = 7369271) B7369271
theorem B3275231 : Blo 2183435 3275231 := bstep (se 1 (by rfl) ⟨2456423, by rfl⟩ : syracuseStep 3275231 = 4912847) B4912847
theorem B2183487 : Blo 2183435 2183487 := bstep (se 1 (by rfl) ⟨1637615, by rfl⟩ : syracuseStep 2183487 = 3275231) B3275231
theorem B3275237 : Blo 2183435 3275237 := bbase (se 4 (by rfl) ⟨307053, by rfl⟩ : syracuseStep 3275237 = 614107) (by norm_num)
theorem B2183491 : Blo 2183435 2183491 := bstep (se 1 (by rfl) ⟨1637618, by rfl⟩ : syracuseStep 2183491 = 3275237) B3275237
theorem B5246309 : Blo 2183435 5246309 := bbase (se 4 (by rfl) ⟨491841, by rfl⟩ : syracuseStep 5246309 = 983683) (by norm_num)
theorem B13990157 : Blo 2183435 13990157 := bstep (se 3 (by rfl) ⟨2623154, by rfl⟩ : syracuseStep 13990157 = 5246309) B5246309
theorem B9326771 : Blo 2183435 9326771 := bstep (se 1 (by rfl) ⟨6995078, by rfl⟩ : syracuseStep 9326771 = 13990157) B13990157
theorem B6217847 : Blo 2183435 6217847 := bstep (se 1 (by rfl) ⟨4663385, by rfl⟩ : syracuseStep 6217847 = 9326771) B9326771
theorem B4145231 : Blo 2183435 4145231 := bstep (se 1 (by rfl) ⟨3108923, by rfl⟩ : syracuseStep 4145231 = 6217847) B6217847
theorem B2763487 : Blo 2183435 2763487 := bstep (se 1 (by rfl) ⟨2072615, by rfl⟩ : syracuseStep 2763487 = 4145231) B4145231
theorem B3684649 : Blo 2183435 3684649 := bstep (se 2 (by rfl) ⟨1381743, by rfl⟩ : syracuseStep 3684649 = 2763487) B2763487
theorem B4912865 : Blo 2183435 4912865 := bstep (se 2 (by rfl) ⟨1842324, by rfl⟩ : syracuseStep 4912865 = 3684649) B3684649
theorem B3275243 : Blo 2183435 3275243 := bstep (se 1 (by rfl) ⟨2456432, by rfl⟩ : syracuseStep 3275243 = 4912865) B4912865
theorem B2183495 : Blo 2183435 2183495 := bstep (se 1 (by rfl) ⟨1637621, by rfl⟩ : syracuseStep 2183495 = 3275243) B3275243
theorem B2456437 : Blo 2183435 2456437 := bbase (se 5 (by rfl) ⟨115145, by rfl⟩ : syracuseStep 2456437 = 230291) (by norm_num)
theorem B3275249 : Blo 2183435 3275249 := bstep (se 2 (by rfl) ⟨1228218, by rfl⟩ : syracuseStep 3275249 = 2456437) B2456437
theorem B2183499 : Blo 2183435 2183499 := bstep (se 1 (by rfl) ⟨1637624, by rfl⟩ : syracuseStep 2183499 = 3275249) B3275249
theorem B2763497 : Blo 2183435 2763497 := bbase (se 2 (by rfl) ⟨1036311, by rfl⟩ : syracuseStep 2763497 = 2072623) (by norm_num)
theorem B7369325 : Blo 2183435 7369325 := bstep (se 3 (by rfl) ⟨1381748, by rfl⟩ : syracuseStep 7369325 = 2763497) B2763497
theorem B4912883 : Blo 2183435 4912883 := bstep (se 1 (by rfl) ⟨3684662, by rfl⟩ : syracuseStep 4912883 = 7369325) B7369325
theorem B3275255 : Blo 2183435 3275255 := bstep (se 1 (by rfl) ⟨2456441, by rfl⟩ : syracuseStep 3275255 = 4912883) B4912883
theorem B2183503 : Blo 2183435 2183503 := bstep (se 1 (by rfl) ⟨1637627, by rfl⟩ : syracuseStep 2183503 = 3275255) B3275255
theorem B3275261 : Blo 2183435 3275261 := bbase (se 3 (by rfl) ⟨614111, by rfl⟩ : syracuseStep 3275261 = 1228223) (by norm_num)
theorem B2183507 : Blo 2183435 2183507 := bstep (se 1 (by rfl) ⟨1637630, by rfl⟩ : syracuseStep 2183507 = 3275261) B3275261
theorem B4912901 : Blo 2183435 4912901 := bbase (se 4 (by rfl) ⟨460584, by rfl⟩ : syracuseStep 4912901 = 921169) (by norm_num)
theorem B3275267 : Blo 2183435 3275267 := bstep (se 1 (by rfl) ⟨2456450, by rfl⟩ : syracuseStep 3275267 = 4912901) B4912901
theorem B2183511 : Blo 2183435 2183511 := bstep (se 1 (by rfl) ⟨1637633, by rfl⟩ : syracuseStep 2183511 = 3275267) B3275267
theorem B4145269 : Blo 2183435 4145269 := bbase (se 5 (by rfl) ⟨194309, by rfl⟩ : syracuseStep 4145269 = 388619) (by norm_num)
theorem B5527025 : Blo 2183435 5527025 := bstep (se 2 (by rfl) ⟨2072634, by rfl⟩ : syracuseStep 5527025 = 4145269) B4145269
theorem B3684683 : Blo 2183435 3684683 := bstep (se 1 (by rfl) ⟨2763512, by rfl⟩ : syracuseStep 3684683 = 5527025) B5527025
theorem B2456455 : Blo 2183435 2456455 := bstep (se 1 (by rfl) ⟨1842341, by rfl⟩ : syracuseStep 2456455 = 3684683) B3684683
theorem B3275273 : Blo 2183435 3275273 := bstep (se 2 (by rfl) ⟨1228227, by rfl⟩ : syracuseStep 3275273 = 2456455) B2456455
theorem B2183515 : Blo 2183435 2183515 := bstep (se 1 (by rfl) ⟨1637636, by rfl⟩ : syracuseStep 2183515 = 3275273) B3275273
theorem B11054069 : Blo 2183435 11054069 := bbase (se 5 (by rfl) ⟨518159, by rfl⟩ : syracuseStep 11054069 = 1036319) (by norm_num)
theorem B7369379 : Blo 2183435 7369379 := bstep (se 1 (by rfl) ⟨5527034, by rfl⟩ : syracuseStep 7369379 = 11054069) B11054069
theorem B4912919 : Blo 2183435 4912919 := bstep (se 1 (by rfl) ⟨3684689, by rfl⟩ : syracuseStep 4912919 = 7369379) B7369379
theorem B3275279 : Blo 2183435 3275279 := bstep (se 1 (by rfl) ⟨2456459, by rfl⟩ : syracuseStep 3275279 = 4912919) B4912919
theorem B2183519 : Blo 2183435 2183519 := bstep (se 1 (by rfl) ⟨1637639, by rfl⟩ : syracuseStep 2183519 = 3275279) B3275279
theorem B3275285 : Blo 2183435 3275285 := bbase (se 6 (by rfl) ⟨76764, by rfl⟩ : syracuseStep 3275285 = 153529) (by norm_num)
theorem B2183523 : Blo 2183435 2183523 := bstep (se 1 (by rfl) ⟨1637642, by rfl⟩ : syracuseStep 2183523 = 3275285) B3275285
theorem B18653813 : Blo 2183435 18653813 := bbase (se 5 (by rfl) ⟨874397, by rfl⟩ : syracuseStep 18653813 = 1748795) (by norm_num)
theorem B12435875 : Blo 2183435 12435875 := bstep (se 1 (by rfl) ⟨9326906, by rfl⟩ : syracuseStep 12435875 = 18653813) B18653813
theorem B8290583 : Blo 2183435 8290583 := bstep (se 1 (by rfl) ⟨6217937, by rfl⟩ : syracuseStep 8290583 = 12435875) B12435875
theorem B5527055 : Blo 2183435 5527055 := bstep (se 1 (by rfl) ⟨4145291, by rfl⟩ : syracuseStep 5527055 = 8290583) B8290583
theorem B3684703 : Blo 2183435 3684703 := bstep (se 1 (by rfl) ⟨2763527, by rfl⟩ : syracuseStep 3684703 = 5527055) B5527055
theorem B4912937 : Blo 2183435 4912937 := bstep (se 2 (by rfl) ⟨1842351, by rfl⟩ : syracuseStep 4912937 = 3684703) B3684703
theorem B3275291 : Blo 2183435 3275291 := bstep (se 1 (by rfl) ⟨2456468, by rfl⟩ : syracuseStep 3275291 = 4912937) B4912937
theorem B2183527 : Blo 2183435 2183527 := bstep (se 1 (by rfl) ⟨1637645, by rfl⟩ : syracuseStep 2183527 = 3275291) B3275291
theorem B2456473 : Blo 2183435 2456473 := bbase (se 2 (by rfl) ⟨921177, by rfl⟩ : syracuseStep 2456473 = 1842355) (by norm_num)
theorem B3275297 : Blo 2183435 3275297 := bstep (se 2 (by rfl) ⟨1228236, by rfl⟩ : syracuseStep 3275297 = 2456473) B2456473
theorem B2183531 : Blo 2183435 2183531 := bstep (se 1 (by rfl) ⟨1637648, by rfl⟩ : syracuseStep 2183531 = 3275297) B3275297
theorem B8290613 : Blo 2183435 8290613 := bbase (se 5 (by rfl) ⟨388622, by rfl⟩ : syracuseStep 8290613 = 777245) (by norm_num)
theorem B5527075 : Blo 2183435 5527075 := bstep (se 1 (by rfl) ⟨4145306, by rfl⟩ : syracuseStep 5527075 = 8290613) B8290613
theorem B7369433 : Blo 2183435 7369433 := bstep (se 2 (by rfl) ⟨2763537, by rfl⟩ : syracuseStep 7369433 = 5527075) B5527075
theorem B4912955 : Blo 2183435 4912955 := bstep (se 1 (by rfl) ⟨3684716, by rfl⟩ : syracuseStep 4912955 = 7369433) B7369433
theorem B3275303 : Blo 2183435 3275303 := bstep (se 1 (by rfl) ⟨2456477, by rfl⟩ : syracuseStep 3275303 = 4912955) B4912955
theorem B2183535 : Blo 2183435 2183535 := bstep (se 1 (by rfl) ⟨1637651, by rfl⟩ : syracuseStep 2183535 = 3275303) B3275303
theorem B3275309 : Blo 2183435 3275309 := bbase (se 3 (by rfl) ⟨614120, by rfl⟩ : syracuseStep 3275309 = 1228241) (by norm_num)
theorem B2183539 : Blo 2183435 2183539 := bstep (se 1 (by rfl) ⟨1637654, by rfl⟩ : syracuseStep 2183539 = 3275309) B3275309
theorem B4912973 : Blo 2183435 4912973 := bbase (se 3 (by rfl) ⟨921182, by rfl⟩ : syracuseStep 4912973 = 1842365) (by norm_num)
theorem B3275315 : Blo 2183435 3275315 := bstep (se 1 (by rfl) ⟨2456486, by rfl⟩ : syracuseStep 3275315 = 4912973) B4912973
theorem B2183543 : Blo 2183435 2183543 := bstep (se 1 (by rfl) ⟨1637657, by rfl⟩ : syracuseStep 2183543 = 3275315) B3275315
theorem B2763553 : Blo 2183435 2763553 := bbase (se 2 (by rfl) ⟨1036332, by rfl⟩ : syracuseStep 2763553 = 2072665) (by norm_num)
theorem B3684737 : Blo 2183435 3684737 := bstep (se 2 (by rfl) ⟨1381776, by rfl⟩ : syracuseStep 3684737 = 2763553) B2763553
theorem B2456491 : Blo 2183435 2456491 := bstep (se 1 (by rfl) ⟨1842368, by rfl⟩ : syracuseStep 2456491 = 3684737) B3684737
theorem B3275321 : Blo 2183435 3275321 := bstep (se 2 (by rfl) ⟨1228245, by rfl⟩ : syracuseStep 3275321 = 2456491) B2456491
theorem B2183547 : Blo 2183435 2183547 := bstep (se 1 (by rfl) ⟨1637660, by rfl⟩ : syracuseStep 2183547 = 3275321) B3275321
theorem B24872021 : Blo 2183435 24872021 := bbase (se 8 (by rfl) ⟨145734, by rfl⟩ : syracuseStep 24872021 = 291469) (by norm_num)
theorem B16581347 : Blo 2183435 16581347 := bstep (se 1 (by rfl) ⟨12436010, by rfl⟩ : syracuseStep 16581347 = 24872021) B24872021
theorem B11054231 : Blo 2183435 11054231 := bstep (se 1 (by rfl) ⟨8290673, by rfl⟩ : syracuseStep 11054231 = 16581347) B16581347
theorem B7369487 : Blo 2183435 7369487 := bstep (se 1 (by rfl) ⟨5527115, by rfl⟩ : syracuseStep 7369487 = 11054231) B11054231
theorem B4912991 : Blo 2183435 4912991 := bstep (se 1 (by rfl) ⟨3684743, by rfl⟩ : syracuseStep 4912991 = 7369487) B7369487
theorem B3275327 : Blo 2183435 3275327 := bstep (se 1 (by rfl) ⟨2456495, by rfl⟩ : syracuseStep 3275327 = 4912991) B4912991
theorem B2183551 : Blo 2183435 2183551 := bstep (se 1 (by rfl) ⟨1637663, by rfl⟩ : syracuseStep 2183551 = 3275327) B3275327
theorem B3275333 : Blo 2183435 3275333 := bbase (se 4 (by rfl) ⟨307062, by rfl⟩ : syracuseStep 3275333 = 614125) (by norm_num)
theorem B2183555 : Blo 2183435 2183555 := bstep (se 1 (by rfl) ⟨1637666, by rfl⟩ : syracuseStep 2183555 = 3275333) B3275333
theorem B3684757 : Blo 2183435 3684757 := bbase (se 6 (by rfl) ⟨86361, by rfl⟩ : syracuseStep 3684757 = 172723) (by norm_num)
theorem B4913009 : Blo 2183435 4913009 := bstep (se 2 (by rfl) ⟨1842378, by rfl⟩ : syracuseStep 4913009 = 3684757) B3684757
theorem B3275339 : Blo 2183435 3275339 := bstep (se 1 (by rfl) ⟨2456504, by rfl⟩ : syracuseStep 3275339 = 4913009) B4913009
theorem B2183559 : Blo 2183435 2183559 := bstep (se 1 (by rfl) ⟨1637669, by rfl⟩ : syracuseStep 2183559 = 3275339) B3275339
theorem B2456509 : Blo 2183435 2456509 := bbase (se 3 (by rfl) ⟨460595, by rfl⟩ : syracuseStep 2456509 = 921191) (by norm_num)
theorem B3275345 : Blo 2183435 3275345 := bstep (se 2 (by rfl) ⟨1228254, by rfl⟩ : syracuseStep 3275345 = 2456509) B2456509
theorem B2183563 : Blo 2183435 2183563 := bstep (se 1 (by rfl) ⟨1637672, by rfl⟩ : syracuseStep 2183563 = 3275345) B3275345
theorem B7369541 : Blo 2183435 7369541 := bbase (se 4 (by rfl) ⟨690894, by rfl⟩ : syracuseStep 7369541 = 1381789) (by norm_num)
theorem B4913027 : Blo 2183435 4913027 := bstep (se 1 (by rfl) ⟨3684770, by rfl⟩ : syracuseStep 4913027 = 7369541) B7369541
theorem B3275351 : Blo 2183435 3275351 := bstep (se 1 (by rfl) ⟨2456513, by rfl⟩ : syracuseStep 3275351 = 4913027) B4913027
theorem B2183567 : Blo 2183435 2183567 := bstep (se 1 (by rfl) ⟨1637675, by rfl⟩ : syracuseStep 2183567 = 3275351) B3275351
theorem B3275357 : Blo 2183435 3275357 := bbase (se 3 (by rfl) ⟨614129, by rfl⟩ : syracuseStep 3275357 = 1228259) (by norm_num)
theorem B2183571 : Blo 2183435 2183571 := bstep (se 1 (by rfl) ⟨1637678, by rfl⟩ : syracuseStep 2183571 = 3275357) B3275357
theorem B4913045 : Blo 2183435 4913045 := bbase (se 6 (by rfl) ⟨115149, by rfl⟩ : syracuseStep 4913045 = 230299) (by norm_num)
theorem B3275363 : Blo 2183435 3275363 := bstep (se 1 (by rfl) ⟨2456522, by rfl⟩ : syracuseStep 3275363 = 4913045) B4913045
theorem B2183575 : Blo 2183435 2183575 := bstep (se 1 (by rfl) ⟨1637681, by rfl⟩ : syracuseStep 2183575 = 3275363) B3275363
theorem B4663565 : Blo 2183435 4663565 := bbase (se 3 (by rfl) ⟨874418, by rfl⟩ : syracuseStep 4663565 = 1748837) (by norm_num)
theorem B3109043 : Blo 2183435 3109043 := bstep (se 1 (by rfl) ⟨2331782, by rfl⟩ : syracuseStep 3109043 = 4663565) B4663565
theorem B8290781 : Blo 2183435 8290781 := bstep (se 3 (by rfl) ⟨1554521, by rfl⟩ : syracuseStep 8290781 = 3109043) B3109043
theorem B5527187 : Blo 2183435 5527187 := bstep (se 1 (by rfl) ⟨4145390, by rfl⟩ : syracuseStep 5527187 = 8290781) B8290781
theorem B3684791 : Blo 2183435 3684791 := bstep (se 1 (by rfl) ⟨2763593, by rfl⟩ : syracuseStep 3684791 = 5527187) B5527187
theorem B2456527 : Blo 2183435 2456527 := bstep (se 1 (by rfl) ⟨1842395, by rfl⟩ : syracuseStep 2456527 = 3684791) B3684791
theorem B3275369 : Blo 2183435 3275369 := bstep (se 2 (by rfl) ⟨1228263, by rfl⟩ : syracuseStep 3275369 = 2456527) B2456527
theorem B2183579 : Blo 2183435 2183579 := bstep (se 1 (by rfl) ⟨1637684, by rfl⟩ : syracuseStep 2183579 = 3275369) B3275369
theorem B34539157 : Blo 2183435 34539157 := bbase (se 6 (by rfl) ⟨809511, by rfl⟩ : syracuseStep 34539157 = 1619023) (by norm_num)
theorem B46052209 : Blo 2183435 46052209 := bstep (se 2 (by rfl) ⟨17269578, by rfl⟩ : syracuseStep 46052209 = 34539157) B34539157
theorem B61402945 : Blo 2183435 61402945 := bstep (se 2 (by rfl) ⟨23026104, by rfl⟩ : syracuseStep 61402945 = 46052209) B46052209
theorem B81870593 : Blo 2183435 81870593 := bstep (se 2 (by rfl) ⟨30701472, by rfl⟩ : syracuseStep 81870593 = 61402945) B61402945
theorem B218321581 : Blo 2183435 218321581 := bstep (se 3 (by rfl) ⟨40935296, by rfl⟩ : syracuseStep 218321581 = 81870593) B81870593
theorem B291095441 : Blo 2183435 291095441 := bstep (se 2 (by rfl) ⟨109160790, by rfl⟩ : syracuseStep 291095441 = 218321581) B218321581
theorem B194063627 : Blo 2183435 194063627 := bstep (se 1 (by rfl) ⟨145547720, by rfl⟩ : syracuseStep 194063627 = 291095441) B291095441
theorem B517503005 : Blo 2183435 517503005 := bstep (se 3 (by rfl) ⟨97031813, by rfl⟩ : syracuseStep 517503005 = 194063627) B194063627
theorem B345002003 : Blo 2183435 345002003 := bstep (se 1 (by rfl) ⟨258751502, by rfl⟩ : syracuseStep 345002003 = 517503005) B517503005
theorem B230001335 : Blo 2183435 230001335 := bstep (se 1 (by rfl) ⟨172501001, by rfl⟩ : syracuseStep 230001335 = 345002003) B345002003
theorem B153334223 : Blo 2183435 153334223 := bstep (se 1 (by rfl) ⟨115000667, by rfl⟩ : syracuseStep 153334223 = 230001335) B230001335
theorem B102222815 : Blo 2183435 102222815 := bstep (se 1 (by rfl) ⟨76667111, by rfl⟩ : syracuseStep 102222815 = 153334223) B153334223
theorem B272594173 : Blo 2183435 272594173 := bstep (se 3 (by rfl) ⟨51111407, by rfl⟩ : syracuseStep 272594173 = 102222815) B102222815
theorem B363458897 : Blo 2183435 363458897 := bstep (se 2 (by rfl) ⟨136297086, by rfl⟩ : syracuseStep 363458897 = 272594173) B272594173
theorem B242305931 : Blo 2183435 242305931 := bstep (se 1 (by rfl) ⟨181729448, by rfl⟩ : syracuseStep 242305931 = 363458897) B363458897
theorem B646149149 : Blo 2183435 646149149 := bstep (se 3 (by rfl) ⟨121152965, by rfl⟩ : syracuseStep 646149149 = 242305931) B242305931
theorem B430766099 : Blo 2183435 430766099 := bstep (se 1 (by rfl) ⟨323074574, by rfl⟩ : syracuseStep 430766099 = 646149149) B646149149
theorem B287177399 : Blo 2183435 287177399 := bstep (se 1 (by rfl) ⟨215383049, by rfl⟩ : syracuseStep 287177399 = 430766099) B430766099
theorem B191451599 : Blo 2183435 191451599 := bstep (se 1 (by rfl) ⟨143588699, by rfl⟩ : syracuseStep 191451599 = 287177399) B287177399
theorem B127634399 : Blo 2183435 127634399 := bstep (se 1 (by rfl) ⟨95725799, by rfl⟩ : syracuseStep 127634399 = 191451599) B191451599
theorem B85089599 : Blo 2183435 85089599 := bstep (se 1 (by rfl) ⟨63817199, by rfl⟩ : syracuseStep 85089599 = 127634399) B127634399
theorem B56726399 : Blo 2183435 56726399 := bstep (se 1 (by rfl) ⟨42544799, by rfl⟩ : syracuseStep 56726399 = 85089599) B85089599
theorem B37817599 : Blo 2183435 37817599 := bstep (se 1 (by rfl) ⟨28363199, by rfl⟩ : syracuseStep 37817599 = 56726399) B56726399
theorem B50423465 : Blo 2183435 50423465 := bstep (se 2 (by rfl) ⟨18908799, by rfl⟩ : syracuseStep 50423465 = 37817599) B37817599
theorem B33615643 : Blo 2183435 33615643 := bstep (se 1 (by rfl) ⟨25211732, by rfl⟩ : syracuseStep 33615643 = 50423465) B50423465
theorem B44820857 : Blo 2183435 44820857 := bstep (se 2 (by rfl) ⟨16807821, by rfl⟩ : syracuseStep 44820857 = 33615643) B33615643
theorem B29880571 : Blo 2183435 29880571 := bstep (se 1 (by rfl) ⟨22410428, by rfl⟩ : syracuseStep 29880571 = 44820857) B44820857
theorem B39840761 : Blo 2183435 39840761 := bstep (se 2 (by rfl) ⟨14940285, by rfl⟩ : syracuseStep 39840761 = 29880571) B29880571
theorem B26560507 : Blo 2183435 26560507 := bstep (se 1 (by rfl) ⟨19920380, by rfl⟩ : syracuseStep 26560507 = 39840761) B39840761
theorem B35414009 : Blo 2183435 35414009 := bstep (se 2 (by rfl) ⟨13280253, by rfl⟩ : syracuseStep 35414009 = 26560507) B26560507
theorem B23609339 : Blo 2183435 23609339 := bstep (se 1 (by rfl) ⟨17707004, by rfl⟩ : syracuseStep 23609339 = 35414009) B35414009
theorem B15739559 : Blo 2183435 15739559 := bstep (se 1 (by rfl) ⟨11804669, by rfl⟩ : syracuseStep 15739559 = 23609339) B23609339
theorem B10493039 : Blo 2183435 10493039 := bstep (se 1 (by rfl) ⟨7869779, by rfl⟩ : syracuseStep 10493039 = 15739559) B15739559
theorem B6995359 : Blo 2183435 6995359 := bstep (se 1 (by rfl) ⟨5246519, by rfl⟩ : syracuseStep 6995359 = 10493039) B10493039
theorem B9327145 : Blo 2183435 9327145 := bstep (se 2 (by rfl) ⟨3497679, by rfl⟩ : syracuseStep 9327145 = 6995359) B6995359
theorem B12436193 : Blo 2183435 12436193 := bstep (se 2 (by rfl) ⟨4663572, by rfl⟩ : syracuseStep 12436193 = 9327145) B9327145
theorem B8290795 : Blo 2183435 8290795 := bstep (se 1 (by rfl) ⟨6218096, by rfl⟩ : syracuseStep 8290795 = 12436193) B12436193
theorem B11054393 : Blo 2183435 11054393 := bstep (se 2 (by rfl) ⟨4145397, by rfl⟩ : syracuseStep 11054393 = 8290795) B8290795
theorem B7369595 : Blo 2183435 7369595 := bstep (se 1 (by rfl) ⟨5527196, by rfl⟩ : syracuseStep 7369595 = 11054393) B11054393
theorem B4913063 : Blo 2183435 4913063 := bstep (se 1 (by rfl) ⟨3684797, by rfl⟩ : syracuseStep 4913063 = 7369595) B7369595
theorem B3275375 : Blo 2183435 3275375 := bstep (se 1 (by rfl) ⟨2456531, by rfl⟩ : syracuseStep 3275375 = 4913063) B4913063
theorem B2183583 : Blo 2183435 2183583 := bstep (se 1 (by rfl) ⟨1637687, by rfl⟩ : syracuseStep 2183583 = 3275375) B3275375
theorem B3275381 : Blo 2183435 3275381 := bbase (se 5 (by rfl) ⟨153533, by rfl⟩ : syracuseStep 3275381 = 307067) (by norm_num)
theorem B2183587 : Blo 2183435 2183587 := bstep (se 1 (by rfl) ⟨1637690, by rfl⟩ : syracuseStep 2183587 = 3275381) B3275381
theorem B4145413 : Blo 2183435 4145413 := bbase (se 4 (by rfl) ⟨388632, by rfl⟩ : syracuseStep 4145413 = 777265) (by norm_num)
theorem B5527217 : Blo 2183435 5527217 := bstep (se 2 (by rfl) ⟨2072706, by rfl⟩ : syracuseStep 5527217 = 4145413) B4145413
theorem B3684811 : Blo 2183435 3684811 := bstep (se 1 (by rfl) ⟨2763608, by rfl⟩ : syracuseStep 3684811 = 5527217) B5527217
theorem B4913081 : Blo 2183435 4913081 := bstep (se 2 (by rfl) ⟨1842405, by rfl⟩ : syracuseStep 4913081 = 3684811) B3684811
theorem B3275387 : Blo 2183435 3275387 := bstep (se 1 (by rfl) ⟨2456540, by rfl⟩ : syracuseStep 3275387 = 4913081) B4913081
theorem B2183591 : Blo 2183435 2183591 := bstep (se 1 (by rfl) ⟨1637693, by rfl⟩ : syracuseStep 2183591 = 3275387) B3275387
theorem B2456545 : Blo 2183435 2456545 := bbase (se 2 (by rfl) ⟨921204, by rfl⟩ : syracuseStep 2456545 = 1842409) (by norm_num)
theorem B3275393 : Blo 2183435 3275393 := bstep (se 2 (by rfl) ⟨1228272, by rfl⟩ : syracuseStep 3275393 = 2456545) B2456545
theorem B2183595 : Blo 2183435 2183595 := bstep (se 1 (by rfl) ⟨1637696, by rfl⟩ : syracuseStep 2183595 = 3275393) B3275393
theorem B5527237 : Blo 2183435 5527237 := bbase (se 4 (by rfl) ⟨518178, by rfl⟩ : syracuseStep 5527237 = 1036357) (by norm_num)
theorem B7369649 : Blo 2183435 7369649 := bstep (se 2 (by rfl) ⟨2763618, by rfl⟩ : syracuseStep 7369649 = 5527237) B5527237
theorem B4913099 : Blo 2183435 4913099 := bstep (se 1 (by rfl) ⟨3684824, by rfl⟩ : syracuseStep 4913099 = 7369649) B7369649
theorem B3275399 : Blo 2183435 3275399 := bstep (se 1 (by rfl) ⟨2456549, by rfl⟩ : syracuseStep 3275399 = 4913099) B4913099
theorem B2183599 : Blo 2183435 2183599 := bstep (se 1 (by rfl) ⟨1637699, by rfl⟩ : syracuseStep 2183599 = 3275399) B3275399
theorem B3275405 : Blo 2183435 3275405 := bbase (se 3 (by rfl) ⟨614138, by rfl⟩ : syracuseStep 3275405 = 1228277) (by norm_num)
theorem B2183603 : Blo 2183435 2183603 := bstep (se 1 (by rfl) ⟨1637702, by rfl⟩ : syracuseStep 2183603 = 3275405) B3275405
theorem B4913117 : Blo 2183435 4913117 := bbase (se 3 (by rfl) ⟨921209, by rfl⟩ : syracuseStep 4913117 = 1842419) (by norm_num)
theorem B3275411 : Blo 2183435 3275411 := bstep (se 1 (by rfl) ⟨2456558, by rfl⟩ : syracuseStep 3275411 = 4913117) B4913117
theorem B2183607 : Blo 2183435 2183607 := bstep (se 1 (by rfl) ⟨1637705, by rfl⟩ : syracuseStep 2183607 = 3275411) B3275411
theorem B3684845 : Blo 2183435 3684845 := bbase (se 3 (by rfl) ⟨690908, by rfl⟩ : syracuseStep 3684845 = 1381817) (by norm_num)
theorem B2456563 : Blo 2183435 2456563 := bstep (se 1 (by rfl) ⟨1842422, by rfl⟩ : syracuseStep 2456563 = 3684845) B3684845
theorem B3275417 : Blo 2183435 3275417 := bstep (se 2 (by rfl) ⟨1228281, by rfl⟩ : syracuseStep 3275417 = 2456563) B2456563
theorem B2183611 : Blo 2183435 2183611 := bstep (se 1 (by rfl) ⟨1637708, by rfl⟩ : syracuseStep 2183611 = 3275417) B3275417
theorem B27981845 : Blo 2183435 27981845 := bbase (se 6 (by rfl) ⟨655824, by rfl⟩ : syracuseStep 27981845 = 1311649) (by norm_num)
theorem B18654563 : Blo 2183435 18654563 := bstep (se 1 (by rfl) ⟨13990922, by rfl⟩ : syracuseStep 18654563 = 27981845) B27981845
theorem B12436375 : Blo 2183435 12436375 := bstep (se 1 (by rfl) ⟨9327281, by rfl⟩ : syracuseStep 12436375 = 18654563) B18654563
theorem B16581833 : Blo 2183435 16581833 := bstep (se 2 (by rfl) ⟨6218187, by rfl⟩ : syracuseStep 16581833 = 12436375) B12436375
theorem B11054555 : Blo 2183435 11054555 := bstep (se 1 (by rfl) ⟨8290916, by rfl⟩ : syracuseStep 11054555 = 16581833) B16581833
theorem B7369703 : Blo 2183435 7369703 := bstep (se 1 (by rfl) ⟨5527277, by rfl⟩ : syracuseStep 7369703 = 11054555) B11054555
theorem B4913135 : Blo 2183435 4913135 := bstep (se 1 (by rfl) ⟨3684851, by rfl⟩ : syracuseStep 4913135 = 7369703) B7369703
theorem B3275423 : Blo 2183435 3275423 := bstep (se 1 (by rfl) ⟨2456567, by rfl⟩ : syracuseStep 3275423 = 4913135) B4913135
theorem B2183615 : Blo 2183435 2183615 := bstep (se 1 (by rfl) ⟨1637711, by rfl⟩ : syracuseStep 2183615 = 3275423) B3275423
theorem B3275429 : Blo 2183435 3275429 := bbase (se 4 (by rfl) ⟨307071, by rfl⟩ : syracuseStep 3275429 = 614143) (by norm_num)
theorem B2183619 : Blo 2183435 2183619 := bstep (se 1 (by rfl) ⟨1637714, by rfl⟩ : syracuseStep 2183619 = 3275429) B3275429
theorem B2763649 : Blo 2183435 2763649 := bbase (se 2 (by rfl) ⟨1036368, by rfl⟩ : syracuseStep 2763649 = 2072737) (by norm_num)
theorem B3684865 : Blo 2183435 3684865 := bstep (se 2 (by rfl) ⟨1381824, by rfl⟩ : syracuseStep 3684865 = 2763649) B2763649
theorem B4913153 : Blo 2183435 4913153 := bstep (se 2 (by rfl) ⟨1842432, by rfl⟩ : syracuseStep 4913153 = 3684865) B3684865
theorem B3275435 : Blo 2183435 3275435 := bstep (se 1 (by rfl) ⟨2456576, by rfl⟩ : syracuseStep 3275435 = 4913153) B4913153
theorem B2183623 : Blo 2183435 2183623 := bstep (se 1 (by rfl) ⟨1637717, by rfl⟩ : syracuseStep 2183623 = 3275435) B3275435
theorem B2456581 : Blo 2183435 2456581 := bbase (se 4 (by rfl) ⟨230304, by rfl⟩ : syracuseStep 2456581 = 460609) (by norm_num)
theorem B3275441 : Blo 2183435 3275441 := bstep (se 2 (by rfl) ⟨1228290, by rfl⟩ : syracuseStep 3275441 = 2456581) B2456581
theorem B2183627 : Blo 2183435 2183627 := bstep (se 1 (by rfl) ⟨1637720, by rfl⟩ : syracuseStep 2183627 = 3275441) B3275441
theorem B3109117 : Blo 2183435 3109117 := bbase (se 3 (by rfl) ⟨582959, by rfl⟩ : syracuseStep 3109117 = 1165919) (by norm_num)
theorem B4145489 : Blo 2183435 4145489 := bstep (se 2 (by rfl) ⟨1554558, by rfl⟩ : syracuseStep 4145489 = 3109117) B3109117
theorem B2763659 : Blo 2183435 2763659 := bstep (se 1 (by rfl) ⟨2072744, by rfl⟩ : syracuseStep 2763659 = 4145489) B4145489
theorem B7369757 : Blo 2183435 7369757 := bstep (se 3 (by rfl) ⟨1381829, by rfl⟩ : syracuseStep 7369757 = 2763659) B2763659
theorem B4913171 : Blo 2183435 4913171 := bstep (se 1 (by rfl) ⟨3684878, by rfl⟩ : syracuseStep 4913171 = 7369757) B7369757
theorem B3275447 : Blo 2183435 3275447 := bstep (se 1 (by rfl) ⟨2456585, by rfl⟩ : syracuseStep 3275447 = 4913171) B4913171
theorem B2183631 : Blo 2183435 2183631 := bstep (se 1 (by rfl) ⟨1637723, by rfl⟩ : syracuseStep 2183631 = 3275447) B3275447
theorem B3275453 : Blo 2183435 3275453 := bbase (se 3 (by rfl) ⟨614147, by rfl⟩ : syracuseStep 3275453 = 1228295) (by norm_num)
theorem B2183635 : Blo 2183435 2183635 := bstep (se 1 (by rfl) ⟨1637726, by rfl⟩ : syracuseStep 2183635 = 3275453) B3275453
theorem B4913189 : Blo 2183435 4913189 := bbase (se 4 (by rfl) ⟨460611, by rfl⟩ : syracuseStep 4913189 = 921223) (by norm_num)
theorem B3275459 : Blo 2183435 3275459 := bstep (se 1 (by rfl) ⟨2456594, by rfl⟩ : syracuseStep 3275459 = 4913189) B4913189
theorem B2183639 : Blo 2183435 2183639 := bstep (se 1 (by rfl) ⟨1637729, by rfl⟩ : syracuseStep 2183639 = 3275459) B3275459
theorem B5527349 : Blo 2183435 5527349 := bbase (se 5 (by rfl) ⟨259094, by rfl⟩ : syracuseStep 5527349 = 518189) (by norm_num)
theorem B3684899 : Blo 2183435 3684899 := bstep (se 1 (by rfl) ⟨2763674, by rfl⟩ : syracuseStep 3684899 = 5527349) B5527349
theorem B2456599 : Blo 2183435 2456599 := bstep (se 1 (by rfl) ⟨1842449, by rfl⟩ : syracuseStep 2456599 = 3684899) B3684899
theorem B3275465 : Blo 2183435 3275465 := bstep (se 2 (by rfl) ⟨1228299, by rfl⟩ : syracuseStep 3275465 = 2456599) B2456599
theorem B2183643 : Blo 2183435 2183643 := bstep (se 1 (by rfl) ⟨1637732, by rfl⟩ : syracuseStep 2183643 = 3275465) B3275465
theorem B15740021 : Blo 2183435 15740021 := bbase (se 5 (by rfl) ⟨737813, by rfl⟩ : syracuseStep 15740021 = 1475627) (by norm_num)
theorem B10493347 : Blo 2183435 10493347 := bstep (se 1 (by rfl) ⟨7870010, by rfl⟩ : syracuseStep 10493347 = 15740021) B15740021
theorem B13991129 : Blo 2183435 13991129 := bstep (se 2 (by rfl) ⟨5246673, by rfl⟩ : syracuseStep 13991129 = 10493347) B10493347
theorem B9327419 : Blo 2183435 9327419 := bstep (se 1 (by rfl) ⟨6995564, by rfl⟩ : syracuseStep 9327419 = 13991129) B13991129
theorem B6218279 : Blo 2183435 6218279 := bstep (se 1 (by rfl) ⟨4663709, by rfl⟩ : syracuseStep 6218279 = 9327419) B9327419
theorem B4145519 : Blo 2183435 4145519 := bstep (se 1 (by rfl) ⟨3109139, by rfl⟩ : syracuseStep 4145519 = 6218279) B6218279
theorem B11054717 : Blo 2183435 11054717 := bstep (se 3 (by rfl) ⟨2072759, by rfl⟩ : syracuseStep 11054717 = 4145519) B4145519
theorem B7369811 : Blo 2183435 7369811 := bstep (se 1 (by rfl) ⟨5527358, by rfl⟩ : syracuseStep 7369811 = 11054717) B11054717
theorem B4913207 : Blo 2183435 4913207 := bstep (se 1 (by rfl) ⟨3684905, by rfl⟩ : syracuseStep 4913207 = 7369811) B7369811
theorem B3275471 : Blo 2183435 3275471 := bstep (se 1 (by rfl) ⟨2456603, by rfl⟩ : syracuseStep 3275471 = 4913207) B4913207
theorem B2183647 : Blo 2183435 2183647 := bstep (se 1 (by rfl) ⟨1637735, by rfl⟩ : syracuseStep 2183647 = 3275471) B3275471
theorem B3275477 : Blo 2183435 3275477 := bbase (se 7 (by rfl) ⟨38384, by rfl⟩ : syracuseStep 3275477 = 76769) (by norm_num)
theorem B2183651 : Blo 2183435 2183651 := bstep (se 1 (by rfl) ⟨1637738, by rfl⟩ : syracuseStep 2183651 = 3275477) B3275477
theorem B2213449 : Blo 2183435 2213449 := bbase (se 2 (by rfl) ⟨830043, by rfl⟩ : syracuseStep 2213449 = 1660087) (by norm_num)
theorem B11805061 : Blo 2183435 11805061 := bstep (se 4 (by rfl) ⟨1106724, by rfl⟩ : syracuseStep 11805061 = 2213449) B2213449
theorem B15740081 : Blo 2183435 15740081 := bstep (se 2 (by rfl) ⟨5902530, by rfl⟩ : syracuseStep 15740081 = 11805061) B11805061
theorem B10493387 : Blo 2183435 10493387 := bstep (se 1 (by rfl) ⟨7870040, by rfl⟩ : syracuseStep 10493387 = 15740081) B15740081
theorem B6995591 : Blo 2183435 6995591 := bstep (se 1 (by rfl) ⟨5246693, by rfl⟩ : syracuseStep 6995591 = 10493387) B10493387
theorem B4663727 : Blo 2183435 4663727 := bstep (se 1 (by rfl) ⟨3497795, by rfl⟩ : syracuseStep 4663727 = 6995591) B6995591
theorem B3109151 : Blo 2183435 3109151 := bstep (se 1 (by rfl) ⟨2331863, by rfl⟩ : syracuseStep 3109151 = 4663727) B4663727
theorem B8291069 : Blo 2183435 8291069 := bstep (se 3 (by rfl) ⟨1554575, by rfl⟩ : syracuseStep 8291069 = 3109151) B3109151
theorem B5527379 : Blo 2183435 5527379 := bstep (se 1 (by rfl) ⟨4145534, by rfl⟩ : syracuseStep 5527379 = 8291069) B8291069
theorem B3684919 : Blo 2183435 3684919 := bstep (se 1 (by rfl) ⟨2763689, by rfl⟩ : syracuseStep 3684919 = 5527379) B5527379
theorem B4913225 : Blo 2183435 4913225 := bstep (se 2 (by rfl) ⟨1842459, by rfl⟩ : syracuseStep 4913225 = 3684919) B3684919
theorem B3275483 : Blo 2183435 3275483 := bstep (se 1 (by rfl) ⟨2456612, by rfl⟩ : syracuseStep 3275483 = 4913225) B4913225
theorem B2183655 : Blo 2183435 2183655 := bstep (se 1 (by rfl) ⟨1637741, by rfl⟩ : syracuseStep 2183655 = 3275483) B3275483
theorem B2456617 : Blo 2183435 2456617 := bbase (se 2 (by rfl) ⟨921231, by rfl⟩ : syracuseStep 2456617 = 1842463) (by norm_num)
theorem B3275489 : Blo 2183435 3275489 := bstep (se 2 (by rfl) ⟨1228308, by rfl⟩ : syracuseStep 3275489 = 2456617) B2456617
theorem B2183659 : Blo 2183435 2183659 := bstep (se 1 (by rfl) ⟨1637744, by rfl⟩ : syracuseStep 2183659 = 3275489) B3275489
theorem B3194581 : Blo 2183435 3194581 := bbase (se 7 (by rfl) ⟨37436, by rfl⟩ : syracuseStep 3194581 = 74873) (by norm_num)
theorem B4259441 : Blo 2183435 4259441 := bstep (se 2 (by rfl) ⟨1597290, by rfl⟩ : syracuseStep 4259441 = 3194581) B3194581
theorem B2839627 : Blo 2183435 2839627 := bstep (se 1 (by rfl) ⟨2129720, by rfl⟩ : syracuseStep 2839627 = 4259441) B4259441
theorem B3786169 : Blo 2183435 3786169 := bstep (se 2 (by rfl) ⟨1419813, by rfl⟩ : syracuseStep 3786169 = 2839627) B2839627
theorem B5048225 : Blo 2183435 5048225 := bstep (se 2 (by rfl) ⟨1893084, by rfl⟩ : syracuseStep 5048225 = 3786169) B3786169
theorem B215390933 : Blo 2183435 215390933 := bstep (se 7 (by rfl) ⟨2524112, by rfl⟩ : syracuseStep 215390933 = 5048225) B5048225
theorem B143593955 : Blo 2183435 143593955 := bstep (se 1 (by rfl) ⟨107695466, by rfl⟩ : syracuseStep 143593955 = 215390933) B215390933
theorem B95729303 : Blo 2183435 95729303 := bstep (se 1 (by rfl) ⟨71796977, by rfl⟩ : syracuseStep 95729303 = 143593955) B143593955
theorem B63819535 : Blo 2183435 63819535 := bstep (se 1 (by rfl) ⟨47864651, by rfl⟩ : syracuseStep 63819535 = 95729303) B95729303
theorem B85092713 : Blo 2183435 85092713 := bstep (se 2 (by rfl) ⟨31909767, by rfl⟩ : syracuseStep 85092713 = 63819535) B63819535
theorem B56728475 : Blo 2183435 56728475 := bstep (se 1 (by rfl) ⟨42546356, by rfl⟩ : syracuseStep 56728475 = 85092713) B85092713
theorem B37818983 : Blo 2183435 37818983 := bstep (se 1 (by rfl) ⟨28364237, by rfl⟩ : syracuseStep 37818983 = 56728475) B56728475
theorem B25212655 : Blo 2183435 25212655 := bstep (se 1 (by rfl) ⟨18909491, by rfl⟩ : syracuseStep 25212655 = 37818983) B37818983
theorem B33616873 : Blo 2183435 33616873 := bstep (se 2 (by rfl) ⟨12606327, by rfl⟩ : syracuseStep 33616873 = 25212655) B25212655
theorem B44822497 : Blo 2183435 44822497 := bstep (se 2 (by rfl) ⟨16808436, by rfl⟩ : syracuseStep 44822497 = 33616873) B33616873
theorem B59763329 : Blo 2183435 59763329 := bstep (se 2 (by rfl) ⟨22411248, by rfl⟩ : syracuseStep 59763329 = 44822497) B44822497
theorem B39842219 : Blo 2183435 39842219 := bstep (se 1 (by rfl) ⟨29881664, by rfl⟩ : syracuseStep 39842219 = 59763329) B59763329
theorem B106245917 : Blo 2183435 106245917 := bstep (se 3 (by rfl) ⟨19921109, by rfl⟩ : syracuseStep 106245917 = 39842219) B39842219
theorem B70830611 : Blo 2183435 70830611 := bstep (se 1 (by rfl) ⟨53122958, by rfl⟩ : syracuseStep 70830611 = 106245917) B106245917
theorem B47220407 : Blo 2183435 47220407 := bstep (se 1 (by rfl) ⟨35415305, by rfl⟩ : syracuseStep 47220407 = 70830611) B70830611
theorem B31480271 : Blo 2183435 31480271 := bstep (se 1 (by rfl) ⟨23610203, by rfl⟩ : syracuseStep 31480271 = 47220407) B47220407
theorem B20986847 : Blo 2183435 20986847 := bstep (se 1 (by rfl) ⟨15740135, by rfl⟩ : syracuseStep 20986847 = 31480271) B31480271
theorem B13991231 : Blo 2183435 13991231 := bstep (se 1 (by rfl) ⟨10493423, by rfl⟩ : syracuseStep 13991231 = 20986847) B20986847
theorem B9327487 : Blo 2183435 9327487 := bstep (se 1 (by rfl) ⟨6995615, by rfl⟩ : syracuseStep 9327487 = 13991231) B13991231
theorem B12436649 : Blo 2183435 12436649 := bstep (se 2 (by rfl) ⟨4663743, by rfl⟩ : syracuseStep 12436649 = 9327487) B9327487
theorem B8291099 : Blo 2183435 8291099 := bstep (se 1 (by rfl) ⟨6218324, by rfl⟩ : syracuseStep 8291099 = 12436649) B12436649
theorem B5527399 : Blo 2183435 5527399 := bstep (se 1 (by rfl) ⟨4145549, by rfl⟩ : syracuseStep 5527399 = 8291099) B8291099
theorem B7369865 : Blo 2183435 7369865 := bstep (se 2 (by rfl) ⟨2763699, by rfl⟩ : syracuseStep 7369865 = 5527399) B5527399
theorem B4913243 : Blo 2183435 4913243 := bstep (se 1 (by rfl) ⟨3684932, by rfl⟩ : syracuseStep 4913243 = 7369865) B7369865
theorem B3275495 : Blo 2183435 3275495 := bstep (se 1 (by rfl) ⟨2456621, by rfl⟩ : syracuseStep 3275495 = 4913243) B4913243
theorem B2183663 : Blo 2183435 2183663 := bstep (se 1 (by rfl) ⟨1637747, by rfl⟩ : syracuseStep 2183663 = 3275495) B3275495
theorem B3275501 : Blo 2183435 3275501 := bbase (se 3 (by rfl) ⟨614156, by rfl⟩ : syracuseStep 3275501 = 1228313) (by norm_num)
theorem B2183667 : Blo 2183435 2183667 := bstep (se 1 (by rfl) ⟨1637750, by rfl⟩ : syracuseStep 2183667 = 3275501) B3275501
theorem B4913261 : Blo 2183435 4913261 := bbase (se 3 (by rfl) ⟨921236, by rfl⟩ : syracuseStep 4913261 = 1842473) (by norm_num)
theorem B3275507 : Blo 2183435 3275507 := bstep (se 1 (by rfl) ⟨2456630, by rfl⟩ : syracuseStep 3275507 = 4913261) B4913261
theorem B2183671 : Blo 2183435 2183671 := bstep (se 1 (by rfl) ⟨1637753, by rfl⟩ : syracuseStep 2183671 = 3275507) B3275507
theorem B4145573 : Blo 2183435 4145573 := bbase (se 4 (by rfl) ⟨388647, by rfl⟩ : syracuseStep 4145573 = 777295) (by norm_num)
theorem B2763715 : Blo 2183435 2763715 := bstep (se 1 (by rfl) ⟨2072786, by rfl⟩ : syracuseStep 2763715 = 4145573) B4145573
theorem B3684953 : Blo 2183435 3684953 := bstep (se 2 (by rfl) ⟨1381857, by rfl⟩ : syracuseStep 3684953 = 2763715) B2763715
theorem B2456635 : Blo 2183435 2456635 := bstep (se 1 (by rfl) ⟨1842476, by rfl⟩ : syracuseStep 2456635 = 3684953) B3684953
theorem B3275513 : Blo 2183435 3275513 := bstep (se 2 (by rfl) ⟨1228317, by rfl⟩ : syracuseStep 3275513 = 2456635) B2456635
theorem B2183675 : Blo 2183435 2183675 := bstep (se 1 (by rfl) ⟨1637756, by rfl⟩ : syracuseStep 2183675 = 3275513) B3275513
theorem B2490157 : Blo 2183435 2490157 := bbase (se 3 (by rfl) ⟨466904, by rfl⟩ : syracuseStep 2490157 = 933809) (by norm_num)
theorem B3320209 : Blo 2183435 3320209 := bstep (se 2 (by rfl) ⟨1245078, by rfl⟩ : syracuseStep 3320209 = 2490157) B2490157
theorem B17707781 : Blo 2183435 17707781 := bstep (se 4 (by rfl) ⟨1660104, by rfl⟩ : syracuseStep 17707781 = 3320209) B3320209
theorem B11805187 : Blo 2183435 11805187 := bstep (se 1 (by rfl) ⟨8853890, by rfl⟩ : syracuseStep 11805187 = 17707781) B17707781
theorem B15740249 : Blo 2183435 15740249 := bstep (se 2 (by rfl) ⟨5902593, by rfl⟩ : syracuseStep 15740249 = 11805187) B11805187
theorem B41973997 : Blo 2183435 41973997 := bstep (se 3 (by rfl) ⟨7870124, by rfl⟩ : syracuseStep 41973997 = 15740249) B15740249
theorem B55965329 : Blo 2183435 55965329 := bstep (se 2 (by rfl) ⟨20986998, by rfl⟩ : syracuseStep 55965329 = 41973997) B41973997
theorem B37310219 : Blo 2183435 37310219 := bstep (se 1 (by rfl) ⟨27982664, by rfl⟩ : syracuseStep 37310219 = 55965329) B55965329
theorem B24873479 : Blo 2183435 24873479 := bstep (se 1 (by rfl) ⟨18655109, by rfl⟩ : syracuseStep 24873479 = 37310219) B37310219
theorem B16582319 : Blo 2183435 16582319 := bstep (se 1 (by rfl) ⟨12436739, by rfl⟩ : syracuseStep 16582319 = 24873479) B24873479
theorem B11054879 : Blo 2183435 11054879 := bstep (se 1 (by rfl) ⟨8291159, by rfl⟩ : syracuseStep 11054879 = 16582319) B16582319
theorem B7369919 : Blo 2183435 7369919 := bstep (se 1 (by rfl) ⟨5527439, by rfl⟩ : syracuseStep 7369919 = 11054879) B11054879
theorem B4913279 : Blo 2183435 4913279 := bstep (se 1 (by rfl) ⟨3684959, by rfl⟩ : syracuseStep 4913279 = 7369919) B7369919
theorem B3275519 : Blo 2183435 3275519 := bstep (se 1 (by rfl) ⟨2456639, by rfl⟩ : syracuseStep 3275519 = 4913279) B4913279
theorem B2183679 : Blo 2183435 2183679 := bstep (se 1 (by rfl) ⟨1637759, by rfl⟩ : syracuseStep 2183679 = 3275519) B3275519
theorem B3275525 : Blo 2183435 3275525 := bbase (se 4 (by rfl) ⟨307080, by rfl⟩ : syracuseStep 3275525 = 614161) (by norm_num)
theorem B2183683 : Blo 2183435 2183683 := bstep (se 1 (by rfl) ⟨1637762, by rfl⟩ : syracuseStep 2183683 = 3275525) B3275525
theorem B3684973 : Blo 2183435 3684973 := bbase (se 3 (by rfl) ⟨690932, by rfl⟩ : syracuseStep 3684973 = 1381865) (by norm_num)
theorem B4913297 : Blo 2183435 4913297 := bstep (se 2 (by rfl) ⟨1842486, by rfl⟩ : syracuseStep 4913297 = 3684973) B3684973
theorem B3275531 : Blo 2183435 3275531 := bstep (se 1 (by rfl) ⟨2456648, by rfl⟩ : syracuseStep 3275531 = 4913297) B4913297
theorem B2183687 : Blo 2183435 2183687 := bstep (se 1 (by rfl) ⟨1637765, by rfl⟩ : syracuseStep 2183687 = 3275531) B3275531
theorem B2456653 : Blo 2183435 2456653 := bbase (se 3 (by rfl) ⟨460622, by rfl⟩ : syracuseStep 2456653 = 921245) (by norm_num)
theorem B3275537 : Blo 2183435 3275537 := bstep (se 2 (by rfl) ⟨1228326, by rfl⟩ : syracuseStep 3275537 = 2456653) B2456653
theorem B2183691 : Blo 2183435 2183691 := bstep (se 1 (by rfl) ⟨1637768, by rfl⟩ : syracuseStep 2183691 = 3275537) B3275537
theorem B7369973 : Blo 2183435 7369973 := bbase (se 5 (by rfl) ⟨345467, by rfl⟩ : syracuseStep 7369973 = 690935) (by norm_num)
theorem B4913315 : Blo 2183435 4913315 := bstep (se 1 (by rfl) ⟨3684986, by rfl⟩ : syracuseStep 4913315 = 7369973) B7369973
theorem B3275543 : Blo 2183435 3275543 := bstep (se 1 (by rfl) ⟨2456657, by rfl⟩ : syracuseStep 3275543 = 4913315) B4913315
theorem B2183695 : Blo 2183435 2183695 := bstep (se 1 (by rfl) ⟨1637771, by rfl⟩ : syracuseStep 2183695 = 3275543) B3275543
theorem B3275549 : Blo 2183435 3275549 := bbase (se 3 (by rfl) ⟨614165, by rfl⟩ : syracuseStep 3275549 = 1228331) (by norm_num)
theorem B2183699 : Blo 2183435 2183699 := bstep (se 1 (by rfl) ⟨1637774, by rfl⟩ : syracuseStep 2183699 = 3275549) B3275549
theorem B4913333 : Blo 2183435 4913333 := bbase (se 5 (by rfl) ⟨230312, by rfl⟩ : syracuseStep 4913333 = 460625) (by norm_num)
theorem B3275555 : Blo 2183435 3275555 := bstep (se 1 (by rfl) ⟨2456666, by rfl⟩ : syracuseStep 3275555 = 4913333) B4913333
theorem B2183703 : Blo 2183435 2183703 := bstep (se 1 (by rfl) ⟨1637777, by rfl⟩ : syracuseStep 2183703 = 3275555) B3275555
theorem B7870229 : Blo 2183435 7870229 := bbase (se 6 (by rfl) ⟨184458, by rfl⟩ : syracuseStep 7870229 = 368917) (by norm_num)
theorem B5246819 : Blo 2183435 5246819 := bstep (se 1 (by rfl) ⟨3935114, by rfl⟩ : syracuseStep 5246819 = 7870229) B7870229
theorem B3497879 : Blo 2183435 3497879 := bstep (se 1 (by rfl) ⟨2623409, by rfl⟩ : syracuseStep 3497879 = 5246819) B5246819
theorem B2331919 : Blo 2183435 2331919 := bstep (se 1 (by rfl) ⟨1748939, by rfl⟩ : syracuseStep 2331919 = 3497879) B3497879
theorem B12436901 : Blo 2183435 12436901 := bstep (se 4 (by rfl) ⟨1165959, by rfl⟩ : syracuseStep 12436901 = 2331919) B2331919
theorem B8291267 : Blo 2183435 8291267 := bstep (se 1 (by rfl) ⟨6218450, by rfl⟩ : syracuseStep 8291267 = 12436901) B12436901
theorem B5527511 : Blo 2183435 5527511 := bstep (se 1 (by rfl) ⟨4145633, by rfl⟩ : syracuseStep 5527511 = 8291267) B8291267
theorem B3685007 : Blo 2183435 3685007 := bstep (se 1 (by rfl) ⟨2763755, by rfl⟩ : syracuseStep 3685007 = 5527511) B5527511
theorem B2456671 : Blo 2183435 2456671 := bstep (se 1 (by rfl) ⟨1842503, by rfl⟩ : syracuseStep 2456671 = 3685007) B3685007
theorem B3275561 : Blo 2183435 3275561 := bstep (se 2 (by rfl) ⟨1228335, by rfl⟩ : syracuseStep 3275561 = 2456671) B2456671
theorem B2183707 : Blo 2183435 2183707 := bstep (se 1 (by rfl) ⟨1637780, by rfl⟩ : syracuseStep 2183707 = 3275561) B3275561
theorem B3497885 : Blo 2183435 3497885 := bbase (se 3 (by rfl) ⟨655853, by rfl⟩ : syracuseStep 3497885 = 1311707) (by norm_num)
theorem B2331923 : Blo 2183435 2331923 := bstep (se 1 (by rfl) ⟨1748942, by rfl⟩ : syracuseStep 2331923 = 3497885) B3497885
theorem B6218461 : Blo 2183435 6218461 := bstep (se 3 (by rfl) ⟨1165961, by rfl⟩ : syracuseStep 6218461 = 2331923) B2331923
theorem B8291281 : Blo 2183435 8291281 := bstep (se 2 (by rfl) ⟨3109230, by rfl⟩ : syracuseStep 8291281 = 6218461) B6218461
theorem B11055041 : Blo 2183435 11055041 := bstep (se 2 (by rfl) ⟨4145640, by rfl⟩ : syracuseStep 11055041 = 8291281) B8291281
theorem B7370027 : Blo 2183435 7370027 := bstep (se 1 (by rfl) ⟨5527520, by rfl⟩ : syracuseStep 7370027 = 11055041) B11055041
theorem B4913351 : Blo 2183435 4913351 := bstep (se 1 (by rfl) ⟨3685013, by rfl⟩ : syracuseStep 4913351 = 7370027) B7370027
theorem B3275567 : Blo 2183435 3275567 := bstep (se 1 (by rfl) ⟨2456675, by rfl⟩ : syracuseStep 3275567 = 4913351) B4913351
theorem B2183711 : Blo 2183435 2183711 := bstep (se 1 (by rfl) ⟨1637783, by rfl⟩ : syracuseStep 2183711 = 3275567) B3275567
theorem B3275573 : Blo 2183435 3275573 := bbase (se 5 (by rfl) ⟨153542, by rfl⟩ : syracuseStep 3275573 = 307085) (by norm_num)
theorem B2183715 : Blo 2183435 2183715 := bstep (se 1 (by rfl) ⟨1637786, by rfl⟩ : syracuseStep 2183715 = 3275573) B3275573
theorem B5527541 : Blo 2183435 5527541 := bbase (se 5 (by rfl) ⟨259103, by rfl⟩ : syracuseStep 5527541 = 518207) (by norm_num)
theorem B3685027 : Blo 2183435 3685027 := bstep (se 1 (by rfl) ⟨2763770, by rfl⟩ : syracuseStep 3685027 = 5527541) B5527541
theorem B4913369 : Blo 2183435 4913369 := bstep (se 2 (by rfl) ⟨1842513, by rfl⟩ : syracuseStep 4913369 = 3685027) B3685027
theorem B3275579 : Blo 2183435 3275579 := bstep (se 1 (by rfl) ⟨2456684, by rfl⟩ : syracuseStep 3275579 = 4913369) B4913369
theorem B2183719 : Blo 2183435 2183719 := bstep (se 1 (by rfl) ⟨1637789, by rfl⟩ : syracuseStep 2183719 = 3275579) B3275579
theorem B2456689 : Blo 2183435 2456689 := bbase (se 2 (by rfl) ⟨921258, by rfl⟩ : syracuseStep 2456689 = 1842517) (by norm_num)
theorem B3275585 : Blo 2183435 3275585 := bstep (se 2 (by rfl) ⟨1228344, by rfl⟩ : syracuseStep 3275585 = 2456689) B2456689
theorem B2183723 : Blo 2183435 2183723 := bstep (se 1 (by rfl) ⟨1637792, by rfl⟩ : syracuseStep 2183723 = 3275585) B3275585
theorem B2623433 : Blo 2183435 2623433 := bbase (se 2 (by rfl) ⟨983787, by rfl⟩ : syracuseStep 2623433 = 1967575) (by norm_num)
theorem B6995821 : Blo 2183435 6995821 := bstep (se 3 (by rfl) ⟨1311716, by rfl⟩ : syracuseStep 6995821 = 2623433) B2623433
theorem B9327761 : Blo 2183435 9327761 := bstep (se 2 (by rfl) ⟨3497910, by rfl⟩ : syracuseStep 9327761 = 6995821) B6995821
theorem B6218507 : Blo 2183435 6218507 := bstep (se 1 (by rfl) ⟨4663880, by rfl⟩ : syracuseStep 6218507 = 9327761) B9327761
theorem B4145671 : Blo 2183435 4145671 := bstep (se 1 (by rfl) ⟨3109253, by rfl⟩ : syracuseStep 4145671 = 6218507) B6218507
theorem B5527561 : Blo 2183435 5527561 := bstep (se 2 (by rfl) ⟨2072835, by rfl⟩ : syracuseStep 5527561 = 4145671) B4145671
theorem B7370081 : Blo 2183435 7370081 := bstep (se 2 (by rfl) ⟨2763780, by rfl⟩ : syracuseStep 7370081 = 5527561) B5527561
theorem B4913387 : Blo 2183435 4913387 := bstep (se 1 (by rfl) ⟨3685040, by rfl⟩ : syracuseStep 4913387 = 7370081) B7370081
theorem B3275591 : Blo 2183435 3275591 := bstep (se 1 (by rfl) ⟨2456693, by rfl⟩ : syracuseStep 3275591 = 4913387) B4913387
theorem B2183727 : Blo 2183435 2183727 := bstep (se 1 (by rfl) ⟨1637795, by rfl⟩ : syracuseStep 2183727 = 3275591) B3275591
theorem B3275597 : Blo 2183435 3275597 := bbase (se 3 (by rfl) ⟨614174, by rfl⟩ : syracuseStep 3275597 = 1228349) (by norm_num)
theorem B2183731 : Blo 2183435 2183731 := bstep (se 1 (by rfl) ⟨1637798, by rfl⟩ : syracuseStep 2183731 = 3275597) B3275597
theorem B4913405 : Blo 2183435 4913405 := bbase (se 3 (by rfl) ⟨921263, by rfl⟩ : syracuseStep 4913405 = 1842527) (by norm_num)
theorem B3275603 : Blo 2183435 3275603 := bstep (se 1 (by rfl) ⟨2456702, by rfl⟩ : syracuseStep 3275603 = 4913405) B4913405
theorem B2183735 : Blo 2183435 2183735 := bstep (se 1 (by rfl) ⟨1637801, by rfl⟩ : syracuseStep 2183735 = 3275603) B3275603
theorem B3685061 : Blo 2183435 3685061 := bbase (se 4 (by rfl) ⟨345474, by rfl⟩ : syracuseStep 3685061 = 690949) (by norm_num)
theorem B2456707 : Blo 2183435 2456707 := bstep (se 1 (by rfl) ⟨1842530, by rfl⟩ : syracuseStep 2456707 = 3685061) B3685061
theorem B3275609 : Blo 2183435 3275609 := bstep (se 2 (by rfl) ⟨1228353, by rfl⟩ : syracuseStep 3275609 = 2456707) B2456707
theorem B2183739 : Blo 2183435 2183739 := bstep (se 1 (by rfl) ⟨1637804, by rfl⟩ : syracuseStep 2183739 = 3275609) B3275609
theorem B16582805 : Blo 2183435 16582805 := bbase (se 6 (by rfl) ⟨388659, by rfl⟩ : syracuseStep 16582805 = 777319) (by norm_num)
theorem B11055203 : Blo 2183435 11055203 := bstep (se 1 (by rfl) ⟨8291402, by rfl⟩ : syracuseStep 11055203 = 16582805) B16582805
theorem B7370135 : Blo 2183435 7370135 := bstep (se 1 (by rfl) ⟨5527601, by rfl⟩ : syracuseStep 7370135 = 11055203) B11055203
theorem B4913423 : Blo 2183435 4913423 := bstep (se 1 (by rfl) ⟨3685067, by rfl⟩ : syracuseStep 4913423 = 7370135) B7370135
theorem B3275615 : Blo 2183435 3275615 := bstep (se 1 (by rfl) ⟨2456711, by rfl⟩ : syracuseStep 3275615 = 4913423) B4913423
theorem B2183743 : Blo 2183435 2183743 := bstep (se 1 (by rfl) ⟨1637807, by rfl⟩ : syracuseStep 2183743 = 3275615) B3275615
theorem B3275621 : Blo 2183435 3275621 := bbase (se 4 (by rfl) ⟨307089, by rfl⟩ : syracuseStep 3275621 = 614179) (by norm_num)
theorem B2183747 : Blo 2183435 2183747 := bstep (se 1 (by rfl) ⟨1637810, by rfl⟩ : syracuseStep 2183747 = 3275621) B3275621
theorem B4145717 : Blo 2183435 4145717 := bbase (se 5 (by rfl) ⟨194330, by rfl⟩ : syracuseStep 4145717 = 388661) (by norm_num)
theorem B2763811 : Blo 2183435 2763811 := bstep (se 1 (by rfl) ⟨2072858, by rfl⟩ : syracuseStep 2763811 = 4145717) B4145717
theorem B3685081 : Blo 2183435 3685081 := bstep (se 2 (by rfl) ⟨1381905, by rfl⟩ : syracuseStep 3685081 = 2763811) B2763811
theorem B4913441 : Blo 2183435 4913441 := bstep (se 2 (by rfl) ⟨1842540, by rfl⟩ : syracuseStep 4913441 = 3685081) B3685081
theorem B3275627 : Blo 2183435 3275627 := bstep (se 1 (by rfl) ⟨2456720, by rfl⟩ : syracuseStep 3275627 = 4913441) B4913441
theorem B2183751 : Blo 2183435 2183751 := bstep (se 1 (by rfl) ⟨1637813, by rfl⟩ : syracuseStep 2183751 = 3275627) B3275627
theorem B2456725 : Blo 2183435 2456725 := bbase (se 6 (by rfl) ⟨57579, by rfl⟩ : syracuseStep 2456725 = 115159) (by norm_num)
theorem B3275633 : Blo 2183435 3275633 := bstep (se 2 (by rfl) ⟨1228362, by rfl⟩ : syracuseStep 3275633 = 2456725) B2456725
theorem B2183755 : Blo 2183435 2183755 := bstep (se 1 (by rfl) ⟨1637816, by rfl⟩ : syracuseStep 2183755 = 3275633) B3275633
theorem B2763821 : Blo 2183435 2763821 := bbase (se 3 (by rfl) ⟨518216, by rfl⟩ : syracuseStep 2763821 = 1036433) (by norm_num)
theorem B7370189 : Blo 2183435 7370189 := bstep (se 3 (by rfl) ⟨1381910, by rfl⟩ : syracuseStep 7370189 = 2763821) B2763821
theorem B4913459 : Blo 2183435 4913459 := bstep (se 1 (by rfl) ⟨3685094, by rfl⟩ : syracuseStep 4913459 = 7370189) B7370189
theorem B3275639 : Blo 2183435 3275639 := bstep (se 1 (by rfl) ⟨2456729, by rfl⟩ : syracuseStep 3275639 = 4913459) B4913459
theorem B2183759 : Blo 2183435 2183759 := bstep (se 1 (by rfl) ⟨1637819, by rfl⟩ : syracuseStep 2183759 = 3275639) B3275639
theorem B3275645 : Blo 2183435 3275645 := bbase (se 3 (by rfl) ⟨614183, by rfl⟩ : syracuseStep 3275645 = 1228367) (by norm_num)
theorem B2183763 : Blo 2183435 2183763 := bstep (se 1 (by rfl) ⟨1637822, by rfl⟩ : syracuseStep 2183763 = 3275645) B3275645
theorem B4913477 : Blo 2183435 4913477 := bbase (se 4 (by rfl) ⟨460638, by rfl⟩ : syracuseStep 4913477 = 921277) (by norm_num)
theorem B3275651 : Blo 2183435 3275651 := bstep (se 1 (by rfl) ⟨2456738, by rfl⟩ : syracuseStep 3275651 = 4913477) B4913477
theorem B2183767 : Blo 2183435 2183767 := bstep (se 1 (by rfl) ⟨1637825, by rfl⟩ : syracuseStep 2183767 = 3275651) B3275651
theorem B28365653 : Blo 2183435 28365653 := bbase (se 9 (by rfl) ⟨83102, by rfl⟩ : syracuseStep 28365653 = 166205) (by norm_num)
theorem B18910435 : Blo 2183435 18910435 := bstep (se 1 (by rfl) ⟨14182826, by rfl⟩ : syracuseStep 18910435 = 28365653) B28365653
theorem B25213913 : Blo 2183435 25213913 := bstep (se 2 (by rfl) ⟨9455217, by rfl⟩ : syracuseStep 25213913 = 18910435) B18910435
theorem B16809275 : Blo 2183435 16809275 := bstep (se 1 (by rfl) ⟨12606956, by rfl⟩ : syracuseStep 16809275 = 25213913) B25213913
theorem B11206183 : Blo 2183435 11206183 := bstep (se 1 (by rfl) ⟨8404637, by rfl⟩ : syracuseStep 11206183 = 16809275) B16809275
theorem B14941577 : Blo 2183435 14941577 := bstep (se 2 (by rfl) ⟨5603091, by rfl⟩ : syracuseStep 14941577 = 11206183) B11206183
theorem B9961051 : Blo 2183435 9961051 := bstep (se 1 (by rfl) ⟨7470788, by rfl⟩ : syracuseStep 9961051 = 14941577) B14941577
theorem B13281401 : Blo 2183435 13281401 := bstep (se 2 (by rfl) ⟨4980525, by rfl⟩ : syracuseStep 13281401 = 9961051) B9961051
theorem B8854267 : Blo 2183435 8854267 := bstep (se 1 (by rfl) ⟨6640700, by rfl⟩ : syracuseStep 8854267 = 13281401) B13281401
theorem B11805689 : Blo 2183435 11805689 := bstep (se 2 (by rfl) ⟨4427133, by rfl⟩ : syracuseStep 11805689 = 8854267) B8854267
theorem B7870459 : Blo 2183435 7870459 := bstep (se 1 (by rfl) ⟨5902844, by rfl⟩ : syracuseStep 7870459 = 11805689) B11805689
theorem B10493945 : Blo 2183435 10493945 := bstep (se 2 (by rfl) ⟨3935229, by rfl⟩ : syracuseStep 10493945 = 7870459) B7870459
theorem B6995963 : Blo 2183435 6995963 := bstep (se 1 (by rfl) ⟨5246972, by rfl⟩ : syracuseStep 6995963 = 10493945) B10493945
theorem B4663975 : Blo 2183435 4663975 := bstep (se 1 (by rfl) ⟨3497981, by rfl⟩ : syracuseStep 4663975 = 6995963) B6995963
theorem B6218633 : Blo 2183435 6218633 := bstep (se 2 (by rfl) ⟨2331987, by rfl⟩ : syracuseStep 6218633 = 4663975) B4663975
theorem B4145755 : Blo 2183435 4145755 := bstep (se 1 (by rfl) ⟨3109316, by rfl⟩ : syracuseStep 4145755 = 6218633) B6218633
theorem B5527673 : Blo 2183435 5527673 := bstep (se 2 (by rfl) ⟨2072877, by rfl⟩ : syracuseStep 5527673 = 4145755) B4145755
theorem B3685115 : Blo 2183435 3685115 := bstep (se 1 (by rfl) ⟨2763836, by rfl⟩ : syracuseStep 3685115 = 5527673) B5527673
theorem B2456743 : Blo 2183435 2456743 := bstep (se 1 (by rfl) ⟨1842557, by rfl⟩ : syracuseStep 2456743 = 3685115) B3685115
theorem B3275657 : Blo 2183435 3275657 := bstep (se 2 (by rfl) ⟨1228371, by rfl⟩ : syracuseStep 3275657 = 2456743) B2456743
theorem B2183771 : Blo 2183435 2183771 := bstep (se 1 (by rfl) ⟨1637828, by rfl⟩ : syracuseStep 2183771 = 3275657) B3275657
theorem B11055365 : Blo 2183435 11055365 := bbase (se 4 (by rfl) ⟨1036440, by rfl⟩ : syracuseStep 11055365 = 2072881) (by norm_num)
theorem B7370243 : Blo 2183435 7370243 := bstep (se 1 (by rfl) ⟨5527682, by rfl⟩ : syracuseStep 7370243 = 11055365) B11055365
theorem B4913495 : Blo 2183435 4913495 := bstep (se 1 (by rfl) ⟨3685121, by rfl⟩ : syracuseStep 4913495 = 7370243) B7370243
theorem B3275663 : Blo 2183435 3275663 := bstep (se 1 (by rfl) ⟨2456747, by rfl⟩ : syracuseStep 3275663 = 4913495) B4913495
theorem B2183775 : Blo 2183435 2183775 := bstep (se 1 (by rfl) ⟨1637831, by rfl⟩ : syracuseStep 2183775 = 3275663) B3275663
theorem B3275669 : Blo 2183435 3275669 := bbase (se 6 (by rfl) ⟨76773, by rfl⟩ : syracuseStep 3275669 = 153547) (by norm_num)
theorem B2183779 : Blo 2183435 2183779 := bstep (se 1 (by rfl) ⟨1637834, by rfl⟩ : syracuseStep 2183779 = 3275669) B3275669
theorem B12437333 : Blo 2183435 12437333 := bbase (se 9 (by rfl) ⟨36437, by rfl⟩ : syracuseStep 12437333 = 72875) (by norm_num)
theorem B8291555 : Blo 2183435 8291555 := bstep (se 1 (by rfl) ⟨6218666, by rfl⟩ : syracuseStep 8291555 = 12437333) B12437333
theorem B5527703 : Blo 2183435 5527703 := bstep (se 1 (by rfl) ⟨4145777, by rfl⟩ : syracuseStep 5527703 = 8291555) B8291555
theorem B3685135 : Blo 2183435 3685135 := bstep (se 1 (by rfl) ⟨2763851, by rfl⟩ : syracuseStep 3685135 = 5527703) B5527703
theorem B4913513 : Blo 2183435 4913513 := bstep (se 2 (by rfl) ⟨1842567, by rfl⟩ : syracuseStep 4913513 = 3685135) B3685135
theorem B3275675 : Blo 2183435 3275675 := bstep (se 1 (by rfl) ⟨2456756, by rfl⟩ : syracuseStep 3275675 = 4913513) B4913513
theorem B2183783 : Blo 2183435 2183783 := bstep (se 1 (by rfl) ⟨1637837, by rfl⟩ : syracuseStep 2183783 = 3275675) B3275675
theorem B2456761 : Blo 2183435 2456761 := bbase (se 2 (by rfl) ⟨921285, by rfl⟩ : syracuseStep 2456761 = 1842571) (by norm_num)
theorem B3275681 : Blo 2183435 3275681 := bstep (se 2 (by rfl) ⟨1228380, by rfl⟩ : syracuseStep 3275681 = 2456761) B2456761
theorem B2183787 : Blo 2183435 2183787 := bstep (se 1 (by rfl) ⟨1637840, by rfl⟩ : syracuseStep 2183787 = 3275681) B3275681
theorem B3498013 : Blo 2183435 3498013 := bbase (se 3 (by rfl) ⟨655877, by rfl⟩ : syracuseStep 3498013 = 1311755) (by norm_num)
theorem B4664017 : Blo 2183435 4664017 := bstep (se 2 (by rfl) ⟨1749006, by rfl⟩ : syracuseStep 4664017 = 3498013) B3498013
theorem B6218689 : Blo 2183435 6218689 := bstep (se 2 (by rfl) ⟨2332008, by rfl⟩ : syracuseStep 6218689 = 4664017) B4664017
theorem B8291585 : Blo 2183435 8291585 := bstep (se 2 (by rfl) ⟨3109344, by rfl⟩ : syracuseStep 8291585 = 6218689) B6218689
theorem B5527723 : Blo 2183435 5527723 := bstep (se 1 (by rfl) ⟨4145792, by rfl⟩ : syracuseStep 5527723 = 8291585) B8291585
theorem B7370297 : Blo 2183435 7370297 := bstep (se 2 (by rfl) ⟨2763861, by rfl⟩ : syracuseStep 7370297 = 5527723) B5527723
theorem B4913531 : Blo 2183435 4913531 := bstep (se 1 (by rfl) ⟨3685148, by rfl⟩ : syracuseStep 4913531 = 7370297) B7370297
theorem B3275687 : Blo 2183435 3275687 := bstep (se 1 (by rfl) ⟨2456765, by rfl⟩ : syracuseStep 3275687 = 4913531) B4913531
theorem B2183791 : Blo 2183435 2183791 := bstep (se 1 (by rfl) ⟨1637843, by rfl⟩ : syracuseStep 2183791 = 3275687) B3275687
theorem B3275693 : Blo 2183435 3275693 := bbase (se 3 (by rfl) ⟨614192, by rfl⟩ : syracuseStep 3275693 = 1228385) (by norm_num)
theorem B2183795 : Blo 2183435 2183795 := bstep (se 1 (by rfl) ⟨1637846, by rfl⟩ : syracuseStep 2183795 = 3275693) B3275693
theorem B4913549 : Blo 2183435 4913549 := bbase (se 3 (by rfl) ⟨921290, by rfl⟩ : syracuseStep 4913549 = 1842581) (by norm_num)
theorem B3275699 : Blo 2183435 3275699 := bstep (se 1 (by rfl) ⟨2456774, by rfl⟩ : syracuseStep 3275699 = 4913549) B4913549
theorem B2183799 : Blo 2183435 2183799 := bstep (se 1 (by rfl) ⟨1637849, by rfl⟩ : syracuseStep 2183799 = 3275699) B3275699
theorem B2763877 : Blo 2183435 2763877 := bbase (se 4 (by rfl) ⟨259113, by rfl⟩ : syracuseStep 2763877 = 518227) (by norm_num)
theorem B3685169 : Blo 2183435 3685169 := bstep (se 2 (by rfl) ⟨1381938, by rfl⟩ : syracuseStep 3685169 = 2763877) B2763877
theorem B2456779 : Blo 2183435 2456779 := bstep (se 1 (by rfl) ⟨1842584, by rfl⟩ : syracuseStep 2456779 = 3685169) B3685169
theorem B3275705 : Blo 2183435 3275705 := bstep (se 2 (by rfl) ⟨1228389, by rfl⟩ : syracuseStep 3275705 = 2456779) B2456779
theorem B2183803 : Blo 2183435 2183803 := bstep (se 1 (by rfl) ⟨1637852, by rfl⟩ : syracuseStep 2183803 = 3275705) B3275705
theorem B3935293 : Blo 2183435 3935293 := bbase (se 3 (by rfl) ⟨737867, by rfl⟩ : syracuseStep 3935293 = 1475735) (by norm_num)
theorem B20988229 : Blo 2183435 20988229 := bstep (se 4 (by rfl) ⟨1967646, by rfl⟩ : syracuseStep 20988229 = 3935293) B3935293
theorem B27984305 : Blo 2183435 27984305 := bstep (se 2 (by rfl) ⟨10494114, by rfl⟩ : syracuseStep 27984305 = 20988229) B20988229
theorem B18656203 : Blo 2183435 18656203 := bstep (se 1 (by rfl) ⟨13992152, by rfl⟩ : syracuseStep 18656203 = 27984305) B27984305
theorem B24874937 : Blo 2183435 24874937 := bstep (se 2 (by rfl) ⟨9328101, by rfl⟩ : syracuseStep 24874937 = 18656203) B18656203
theorem B16583291 : Blo 2183435 16583291 := bstep (se 1 (by rfl) ⟨12437468, by rfl⟩ : syracuseStep 16583291 = 24874937) B24874937
theorem B11055527 : Blo 2183435 11055527 := bstep (se 1 (by rfl) ⟨8291645, by rfl⟩ : syracuseStep 11055527 = 16583291) B16583291
theorem B7370351 : Blo 2183435 7370351 := bstep (se 1 (by rfl) ⟨5527763, by rfl⟩ : syracuseStep 7370351 = 11055527) B11055527
theorem B4913567 : Blo 2183435 4913567 := bstep (se 1 (by rfl) ⟨3685175, by rfl⟩ : syracuseStep 4913567 = 7370351) B7370351
theorem B3275711 : Blo 2183435 3275711 := bstep (se 1 (by rfl) ⟨2456783, by rfl⟩ : syracuseStep 3275711 = 4913567) B4913567
theorem B2183807 : Blo 2183435 2183807 := bstep (se 1 (by rfl) ⟨1637855, by rfl⟩ : syracuseStep 2183807 = 3275711) B3275711
theorem B3275717 : Blo 2183435 3275717 := bbase (se 4 (by rfl) ⟨307098, by rfl⟩ : syracuseStep 3275717 = 614197) (by norm_num)
theorem B2183811 : Blo 2183435 2183811 := bstep (se 1 (by rfl) ⟨1637858, by rfl⟩ : syracuseStep 2183811 = 3275717) B3275717
theorem B3685189 : Blo 2183435 3685189 := bbase (se 4 (by rfl) ⟨345486, by rfl⟩ : syracuseStep 3685189 = 690973) (by norm_num)
theorem B4913585 : Blo 2183435 4913585 := bstep (se 2 (by rfl) ⟨1842594, by rfl⟩ : syracuseStep 4913585 = 3685189) B3685189
theorem B3275723 : Blo 2183435 3275723 := bstep (se 1 (by rfl) ⟨2456792, by rfl⟩ : syracuseStep 3275723 = 4913585) B4913585
theorem B2183815 : Blo 2183435 2183815 := bstep (se 1 (by rfl) ⟨1637861, by rfl⟩ : syracuseStep 2183815 = 3275723) B3275723
theorem B2456797 : Blo 2183435 2456797 := bbase (se 3 (by rfl) ⟨460649, by rfl⟩ : syracuseStep 2456797 = 921299) (by norm_num)
theorem B3275729 : Blo 2183435 3275729 := bstep (se 2 (by rfl) ⟨1228398, by rfl⟩ : syracuseStep 3275729 = 2456797) B2456797
theorem B2183819 : Blo 2183435 2183819 := bstep (se 1 (by rfl) ⟨1637864, by rfl⟩ : syracuseStep 2183819 = 3275729) B3275729
theorem B7370405 : Blo 2183435 7370405 := bbase (se 4 (by rfl) ⟨690975, by rfl⟩ : syracuseStep 7370405 = 1381951) (by norm_num)
theorem B4913603 : Blo 2183435 4913603 := bstep (se 1 (by rfl) ⟨3685202, by rfl⟩ : syracuseStep 4913603 = 7370405) B7370405
theorem B3275735 : Blo 2183435 3275735 := bstep (se 1 (by rfl) ⟨2456801, by rfl⟩ : syracuseStep 3275735 = 4913603) B4913603
theorem B2183823 : Blo 2183435 2183823 := bstep (se 1 (by rfl) ⟨1637867, by rfl⟩ : syracuseStep 2183823 = 3275735) B3275735
theorem B3275741 : Blo 2183435 3275741 := bbase (se 3 (by rfl) ⟨614201, by rfl⟩ : syracuseStep 3275741 = 1228403) (by norm_num)
theorem B2183827 : Blo 2183435 2183827 := bstep (se 1 (by rfl) ⟨1637870, by rfl⟩ : syracuseStep 2183827 = 3275741) B3275741
theorem B4913621 : Blo 2183435 4913621 := bbase (se 7 (by rfl) ⟨57581, by rfl⟩ : syracuseStep 4913621 = 115163) (by norm_num)
theorem B3275747 : Blo 2183435 3275747 := bstep (se 1 (by rfl) ⟨2456810, by rfl⟩ : syracuseStep 3275747 = 4913621) B4913621
theorem B2183831 : Blo 2183435 2183831 := bstep (se 1 (by rfl) ⟨1637873, by rfl⟩ : syracuseStep 2183831 = 3275747) B3275747
theorem B8975333 : Blo 2183435 8975333 := bbase (se 4 (by rfl) ⟨841437, by rfl⟩ : syracuseStep 8975333 = 1682875) (by norm_num)
theorem B23934221 : Blo 2183435 23934221 := bstep (se 3 (by rfl) ⟨4487666, by rfl⟩ : syracuseStep 23934221 = 8975333) B8975333
theorem B15956147 : Blo 2183435 15956147 := bstep (se 1 (by rfl) ⟨11967110, by rfl⟩ : syracuseStep 15956147 = 23934221) B23934221
theorem B42549725 : Blo 2183435 42549725 := bstep (se 3 (by rfl) ⟨7978073, by rfl⟩ : syracuseStep 42549725 = 15956147) B15956147
theorem B28366483 : Blo 2183435 28366483 := bstep (se 1 (by rfl) ⟨21274862, by rfl⟩ : syracuseStep 28366483 = 42549725) B42549725
theorem B37821977 : Blo 2183435 37821977 := bstep (se 2 (by rfl) ⟨14183241, by rfl⟩ : syracuseStep 37821977 = 28366483) B28366483
theorem B25214651 : Blo 2183435 25214651 := bstep (se 1 (by rfl) ⟨18910988, by rfl⟩ : syracuseStep 25214651 = 37821977) B37821977
theorem B16809767 : Blo 2183435 16809767 := bstep (se 1 (by rfl) ⟨12607325, by rfl⟩ : syracuseStep 16809767 = 25214651) B25214651
theorem B11206511 : Blo 2183435 11206511 := bstep (se 1 (by rfl) ⟨8404883, by rfl⟩ : syracuseStep 11206511 = 16809767) B16809767
theorem B7471007 : Blo 2183435 7471007 := bstep (se 1 (by rfl) ⟨5603255, by rfl⟩ : syracuseStep 7471007 = 11206511) B11206511
theorem B4980671 : Blo 2183435 4980671 := bstep (se 1 (by rfl) ⟨3735503, by rfl⟩ : syracuseStep 4980671 = 7471007) B7471007
theorem B3320447 : Blo 2183435 3320447 := bstep (se 1 (by rfl) ⟨2490335, by rfl⟩ : syracuseStep 3320447 = 4980671) B4980671
theorem B8854525 : Blo 2183435 8854525 := bstep (se 3 (by rfl) ⟨1660223, by rfl⟩ : syracuseStep 8854525 = 3320447) B3320447
theorem B47224133 : Blo 2183435 47224133 := bstep (se 4 (by rfl) ⟨4427262, by rfl⟩ : syracuseStep 47224133 = 8854525) B8854525
theorem B31482755 : Blo 2183435 31482755 := bstep (se 1 (by rfl) ⟨23612066, by rfl⟩ : syracuseStep 31482755 = 47224133) B47224133
theorem B20988503 : Blo 2183435 20988503 := bstep (se 1 (by rfl) ⟨15741377, by rfl⟩ : syracuseStep 20988503 = 31482755) B31482755
theorem B13992335 : Blo 2183435 13992335 := bstep (se 1 (by rfl) ⟨10494251, by rfl⟩ : syracuseStep 13992335 = 20988503) B20988503
theorem B9328223 : Blo 2183435 9328223 := bstep (se 1 (by rfl) ⟨6996167, by rfl⟩ : syracuseStep 9328223 = 13992335) B13992335
theorem B6218815 : Blo 2183435 6218815 := bstep (se 1 (by rfl) ⟨4664111, by rfl⟩ : syracuseStep 6218815 = 9328223) B9328223
theorem B8291753 : Blo 2183435 8291753 := bstep (se 2 (by rfl) ⟨3109407, by rfl⟩ : syracuseStep 8291753 = 6218815) B6218815
theorem B5527835 : Blo 2183435 5527835 := bstep (se 1 (by rfl) ⟨4145876, by rfl⟩ : syracuseStep 5527835 = 8291753) B8291753
theorem B3685223 : Blo 2183435 3685223 := bstep (se 1 (by rfl) ⟨2763917, by rfl⟩ : syracuseStep 3685223 = 5527835) B5527835
theorem B2456815 : Blo 2183435 2456815 := bstep (se 1 (by rfl) ⟨1842611, by rfl⟩ : syracuseStep 2456815 = 3685223) B3685223
theorem B3275753 : Blo 2183435 3275753 := bstep (se 2 (by rfl) ⟨1228407, by rfl⟩ : syracuseStep 3275753 = 2456815) B2456815
theorem B2183835 : Blo 2183435 2183835 := bstep (se 1 (by rfl) ⟨1637876, by rfl⟩ : syracuseStep 2183835 = 3275753) B3275753
theorem B3320453 : Blo 2183435 3320453 := bbase (se 4 (by rfl) ⟨311292, by rfl⟩ : syracuseStep 3320453 = 622585) (by norm_num)
theorem B8854541 : Blo 2183435 8854541 := bstep (se 3 (by rfl) ⟨1660226, by rfl⟩ : syracuseStep 8854541 = 3320453) B3320453
theorem B5903027 : Blo 2183435 5903027 := bstep (se 1 (by rfl) ⟨4427270, by rfl⟩ : syracuseStep 5903027 = 8854541) B8854541
theorem B3935351 : Blo 2183435 3935351 := bstep (se 1 (by rfl) ⟨2951513, by rfl⟩ : syracuseStep 3935351 = 5903027) B5903027
theorem B10494269 : Blo 2183435 10494269 := bstep (se 3 (by rfl) ⟨1967675, by rfl⟩ : syracuseStep 10494269 = 3935351) B3935351
theorem B6996179 : Blo 2183435 6996179 := bstep (se 1 (by rfl) ⟨5247134, by rfl⟩ : syracuseStep 6996179 = 10494269) B10494269
theorem B18656477 : Blo 2183435 18656477 := bstep (se 3 (by rfl) ⟨3498089, by rfl⟩ : syracuseStep 18656477 = 6996179) B6996179
theorem B12437651 : Blo 2183435 12437651 := bstep (se 1 (by rfl) ⟨9328238, by rfl⟩ : syracuseStep 12437651 = 18656477) B18656477
theorem B8291767 : Blo 2183435 8291767 := bstep (se 1 (by rfl) ⟨6218825, by rfl⟩ : syracuseStep 8291767 = 12437651) B12437651
theorem B11055689 : Blo 2183435 11055689 := bstep (se 2 (by rfl) ⟨4145883, by rfl⟩ : syracuseStep 11055689 = 8291767) B8291767
theorem B7370459 : Blo 2183435 7370459 := bstep (se 1 (by rfl) ⟨5527844, by rfl⟩ : syracuseStep 7370459 = 11055689) B11055689
theorem B4913639 : Blo 2183435 4913639 := bstep (se 1 (by rfl) ⟨3685229, by rfl⟩ : syracuseStep 4913639 = 7370459) B7370459
theorem B3275759 : Blo 2183435 3275759 := bstep (se 1 (by rfl) ⟨2456819, by rfl⟩ : syracuseStep 3275759 = 4913639) B4913639
theorem B2183839 : Blo 2183435 2183839 := bstep (se 1 (by rfl) ⟨1637879, by rfl⟩ : syracuseStep 2183839 = 3275759) B3275759
theorem B3275765 : Blo 2183435 3275765 := bbase (se 5 (by rfl) ⟨153551, by rfl⟩ : syracuseStep 3275765 = 307103) (by norm_num)
theorem B2183843 : Blo 2183435 2183843 := bstep (se 1 (by rfl) ⟨1637882, by rfl⟩ : syracuseStep 2183843 = 3275765) B3275765
theorem B2951525 : Blo 2183435 2951525 := bbase (se 4 (by rfl) ⟨276705, by rfl⟩ : syracuseStep 2951525 = 553411) (by norm_num)
theorem B7870733 : Blo 2183435 7870733 := bstep (se 3 (by rfl) ⟨1475762, by rfl⟩ : syracuseStep 7870733 = 2951525) B2951525
theorem B5247155 : Blo 2183435 5247155 := bstep (se 1 (by rfl) ⟨3935366, by rfl⟩ : syracuseStep 5247155 = 7870733) B7870733
theorem B3498103 : Blo 2183435 3498103 := bstep (se 1 (by rfl) ⟨2623577, by rfl⟩ : syracuseStep 3498103 = 5247155) B5247155
theorem B4664137 : Blo 2183435 4664137 := bstep (se 2 (by rfl) ⟨1749051, by rfl⟩ : syracuseStep 4664137 = 3498103) B3498103
theorem B6218849 : Blo 2183435 6218849 := bstep (se 2 (by rfl) ⟨2332068, by rfl⟩ : syracuseStep 6218849 = 4664137) B4664137
theorem B4145899 : Blo 2183435 4145899 := bstep (se 1 (by rfl) ⟨3109424, by rfl⟩ : syracuseStep 4145899 = 6218849) B6218849
theorem B5527865 : Blo 2183435 5527865 := bstep (se 2 (by rfl) ⟨2072949, by rfl⟩ : syracuseStep 5527865 = 4145899) B4145899
theorem B3685243 : Blo 2183435 3685243 := bstep (se 1 (by rfl) ⟨2763932, by rfl⟩ : syracuseStep 3685243 = 5527865) B5527865
theorem B4913657 : Blo 2183435 4913657 := bstep (se 2 (by rfl) ⟨1842621, by rfl⟩ : syracuseStep 4913657 = 3685243) B3685243
theorem B3275771 : Blo 2183435 3275771 := bstep (se 1 (by rfl) ⟨2456828, by rfl⟩ : syracuseStep 3275771 = 4913657) B4913657
theorem B2183847 : Blo 2183435 2183847 := bstep (se 1 (by rfl) ⟨1637885, by rfl⟩ : syracuseStep 2183847 = 3275771) B3275771
theorem B2456833 : Blo 2183435 2456833 := bbase (se 2 (by rfl) ⟨921312, by rfl⟩ : syracuseStep 2456833 = 1842625) (by norm_num)
theorem B3275777 : Blo 2183435 3275777 := bstep (se 2 (by rfl) ⟨1228416, by rfl⟩ : syracuseStep 3275777 = 2456833) B2456833
theorem B2183851 : Blo 2183435 2183851 := bstep (se 1 (by rfl) ⟨1637888, by rfl⟩ : syracuseStep 2183851 = 3275777) B3275777
theorem B5527885 : Blo 2183435 5527885 := bbase (se 3 (by rfl) ⟨1036478, by rfl⟩ : syracuseStep 5527885 = 2072957) (by norm_num)
theorem B7370513 : Blo 2183435 7370513 := bstep (se 2 (by rfl) ⟨2763942, by rfl⟩ : syracuseStep 7370513 = 5527885) B5527885
theorem B4913675 : Blo 2183435 4913675 := bstep (se 1 (by rfl) ⟨3685256, by rfl⟩ : syracuseStep 4913675 = 7370513) B7370513
theorem B3275783 : Blo 2183435 3275783 := bstep (se 1 (by rfl) ⟨2456837, by rfl⟩ : syracuseStep 3275783 = 4913675) B4913675
theorem B2183855 : Blo 2183435 2183855 := bstep (se 1 (by rfl) ⟨1637891, by rfl⟩ : syracuseStep 2183855 = 3275783) B3275783
theorem B3275789 : Blo 2183435 3275789 := bbase (se 3 (by rfl) ⟨614210, by rfl⟩ : syracuseStep 3275789 = 1228421) (by norm_num)
theorem B2183859 : Blo 2183435 2183859 := bstep (se 1 (by rfl) ⟨1637894, by rfl⟩ : syracuseStep 2183859 = 3275789) B3275789
theorem B4913693 : Blo 2183435 4913693 := bbase (se 3 (by rfl) ⟨921317, by rfl⟩ : syracuseStep 4913693 = 1842635) (by norm_num)
theorem B3275795 : Blo 2183435 3275795 := bstep (se 1 (by rfl) ⟨2456846, by rfl⟩ : syracuseStep 3275795 = 4913693) B4913693
theorem B2183863 : Blo 2183435 2183863 := bstep (se 1 (by rfl) ⟨1637897, by rfl⟩ : syracuseStep 2183863 = 3275795) B3275795
theorem B3685277 : Blo 2183435 3685277 := bbase (se 3 (by rfl) ⟨690989, by rfl⟩ : syracuseStep 3685277 = 1381979) (by norm_num)
theorem B2456851 : Blo 2183435 2456851 := bstep (se 1 (by rfl) ⟨1842638, by rfl⟩ : syracuseStep 2456851 = 3685277) B3685277
theorem B3275801 : Blo 2183435 3275801 := bstep (se 2 (by rfl) ⟨1228425, by rfl⟩ : syracuseStep 3275801 = 2456851) B2456851
theorem B2183867 : Blo 2183435 2183867 := bstep (se 1 (by rfl) ⟨1637900, by rfl⟩ : syracuseStep 2183867 = 3275801) B3275801
theorem B3545869 : Blo 2183435 3545869 := bbase (se 3 (by rfl) ⟨664850, by rfl⟩ : syracuseStep 3545869 = 1329701) (by norm_num)
theorem B4727825 : Blo 2183435 4727825 := bstep (se 2 (by rfl) ⟨1772934, by rfl⟩ : syracuseStep 4727825 = 3545869) B3545869
theorem B3151883 : Blo 2183435 3151883 := bstep (se 1 (by rfl) ⟨2363912, by rfl⟩ : syracuseStep 3151883 = 4727825) B4727825
theorem B8405021 : Blo 2183435 8405021 := bstep (se 3 (by rfl) ⟨1575941, by rfl⟩ : syracuseStep 8405021 = 3151883) B3151883
theorem B5603347 : Blo 2183435 5603347 := bstep (se 1 (by rfl) ⟨4202510, by rfl⟩ : syracuseStep 5603347 = 8405021) B8405021
theorem B7471129 : Blo 2183435 7471129 := bstep (se 2 (by rfl) ⟨2801673, by rfl⟩ : syracuseStep 7471129 = 5603347) B5603347
theorem B9961505 : Blo 2183435 9961505 := bstep (se 2 (by rfl) ⟨3735564, by rfl⟩ : syracuseStep 9961505 = 7471129) B7471129
theorem B6641003 : Blo 2183435 6641003 := bstep (se 1 (by rfl) ⟨4980752, by rfl⟩ : syracuseStep 6641003 = 9961505) B9961505
theorem B4427335 : Blo 2183435 4427335 := bstep (se 1 (by rfl) ⟨3320501, by rfl⟩ : syracuseStep 4427335 = 6641003) B6641003
theorem B5903113 : Blo 2183435 5903113 := bstep (se 2 (by rfl) ⟨2213667, by rfl⟩ : syracuseStep 5903113 = 4427335) B4427335
theorem B7870817 : Blo 2183435 7870817 := bstep (se 2 (by rfl) ⟨2951556, by rfl⟩ : syracuseStep 7870817 = 5903113) B5903113
theorem B20988845 : Blo 2183435 20988845 := bstep (se 3 (by rfl) ⟨3935408, by rfl⟩ : syracuseStep 20988845 = 7870817) B7870817
theorem B13992563 : Blo 2183435 13992563 := bstep (se 1 (by rfl) ⟨10494422, by rfl⟩ : syracuseStep 13992563 = 20988845) B20988845
theorem B9328375 : Blo 2183435 9328375 := bstep (se 1 (by rfl) ⟨6996281, by rfl⟩ : syracuseStep 9328375 = 13992563) B13992563
theorem B12437833 : Blo 2183435 12437833 := bstep (se 2 (by rfl) ⟨4664187, by rfl⟩ : syracuseStep 12437833 = 9328375) B9328375
theorem B16583777 : Blo 2183435 16583777 := bstep (se 2 (by rfl) ⟨6218916, by rfl⟩ : syracuseStep 16583777 = 12437833) B12437833
theorem B11055851 : Blo 2183435 11055851 := bstep (se 1 (by rfl) ⟨8291888, by rfl⟩ : syracuseStep 11055851 = 16583777) B16583777
theorem B7370567 : Blo 2183435 7370567 := bstep (se 1 (by rfl) ⟨5527925, by rfl⟩ : syracuseStep 7370567 = 11055851) B11055851
theorem B4913711 : Blo 2183435 4913711 := bstep (se 1 (by rfl) ⟨3685283, by rfl⟩ : syracuseStep 4913711 = 7370567) B7370567
theorem B3275807 : Blo 2183435 3275807 := bstep (se 1 (by rfl) ⟨2456855, by rfl⟩ : syracuseStep 3275807 = 4913711) B4913711
theorem B2183871 : Blo 2183435 2183871 := bstep (se 1 (by rfl) ⟨1637903, by rfl⟩ : syracuseStep 2183871 = 3275807) B3275807
theorem B3275813 : Blo 2183435 3275813 := bbase (se 4 (by rfl) ⟨307107, by rfl⟩ : syracuseStep 3275813 = 614215) (by norm_num)
theorem B2183875 : Blo 2183435 2183875 := bstep (se 1 (by rfl) ⟨1637906, by rfl⟩ : syracuseStep 2183875 = 3275813) B3275813
theorem B2763973 : Blo 2183435 2763973 := bbase (se 4 (by rfl) ⟨259122, by rfl⟩ : syracuseStep 2763973 = 518245) (by norm_num)
theorem B3685297 : Blo 2183435 3685297 := bstep (se 2 (by rfl) ⟨1381986, by rfl⟩ : syracuseStep 3685297 = 2763973) B2763973
theorem B4913729 : Blo 2183435 4913729 := bstep (se 2 (by rfl) ⟨1842648, by rfl⟩ : syracuseStep 4913729 = 3685297) B3685297
theorem B3275819 : Blo 2183435 3275819 := bstep (se 1 (by rfl) ⟨2456864, by rfl⟩ : syracuseStep 3275819 = 4913729) B4913729
theorem B2183879 : Blo 2183435 2183879 := bstep (se 1 (by rfl) ⟨1637909, by rfl⟩ : syracuseStep 2183879 = 3275819) B3275819
theorem B2456869 : Blo 2183435 2456869 := bbase (se 4 (by rfl) ⟨230331, by rfl⟩ : syracuseStep 2456869 = 460663) (by norm_num)
theorem B3275825 : Blo 2183435 3275825 := bstep (se 2 (by rfl) ⟨1228434, by rfl⟩ : syracuseStep 3275825 = 2456869) B2456869
theorem B2183883 : Blo 2183435 2183883 := bstep (se 1 (by rfl) ⟨1637912, by rfl⟩ : syracuseStep 2183883 = 3275825) B3275825
theorem B12954005 : Blo 2183435 12954005 := bbase (se 6 (by rfl) ⟨303609, by rfl⟩ : syracuseStep 12954005 = 607219) (by norm_num)
theorem B8636003 : Blo 2183435 8636003 := bstep (se 1 (by rfl) ⟨6477002, by rfl⟩ : syracuseStep 8636003 = 12954005) B12954005
theorem B5757335 : Blo 2183435 5757335 := bstep (se 1 (by rfl) ⟨4318001, by rfl⟩ : syracuseStep 5757335 = 8636003) B8636003
theorem B3838223 : Blo 2183435 3838223 := bstep (se 1 (by rfl) ⟨2878667, by rfl⟩ : syracuseStep 3838223 = 5757335) B5757335
theorem B10235261 : Blo 2183435 10235261 := bstep (se 3 (by rfl) ⟨1919111, by rfl⟩ : syracuseStep 10235261 = 3838223) B3838223
theorem B6823507 : Blo 2183435 6823507 := bstep (se 1 (by rfl) ⟨5117630, by rfl⟩ : syracuseStep 6823507 = 10235261) B10235261
theorem B9098009 : Blo 2183435 9098009 := bstep (se 2 (by rfl) ⟨3411753, by rfl⟩ : syracuseStep 9098009 = 6823507) B6823507
theorem B6065339 : Blo 2183435 6065339 := bstep (se 1 (by rfl) ⟨4549004, by rfl⟩ : syracuseStep 6065339 = 9098009) B9098009
theorem B16174237 : Blo 2183435 16174237 := bstep (se 3 (by rfl) ⟨3032669, by rfl⟩ : syracuseStep 16174237 = 6065339) B6065339
theorem B21565649 : Blo 2183435 21565649 := bstep (se 2 (by rfl) ⟨8087118, by rfl⟩ : syracuseStep 21565649 = 16174237) B16174237
theorem B14377099 : Blo 2183435 14377099 := bstep (se 1 (by rfl) ⟨10782824, by rfl⟩ : syracuseStep 14377099 = 21565649) B21565649
theorem B19169465 : Blo 2183435 19169465 := bstep (se 2 (by rfl) ⟨7188549, by rfl⟩ : syracuseStep 19169465 = 14377099) B14377099
theorem B51118573 : Blo 2183435 51118573 := bstep (se 3 (by rfl) ⟨9584732, by rfl⟩ : syracuseStep 51118573 = 19169465) B19169465
theorem B68158097 : Blo 2183435 68158097 := bstep (se 2 (by rfl) ⟨25559286, by rfl⟩ : syracuseStep 68158097 = 51118573) B51118573
theorem B45438731 : Blo 2183435 45438731 := bstep (se 1 (by rfl) ⟨34079048, by rfl⟩ : syracuseStep 45438731 = 68158097) B68158097
theorem B30292487 : Blo 2183435 30292487 := bstep (se 1 (by rfl) ⟨22719365, by rfl⟩ : syracuseStep 30292487 = 45438731) B45438731
theorem B20194991 : Blo 2183435 20194991 := bstep (se 1 (by rfl) ⟨15146243, by rfl⟩ : syracuseStep 20194991 = 30292487) B30292487
theorem B13463327 : Blo 2183435 13463327 := bstep (se 1 (by rfl) ⟨10097495, by rfl⟩ : syracuseStep 13463327 = 20194991) B20194991
theorem B8975551 : Blo 2183435 8975551 := bstep (se 1 (by rfl) ⟨6731663, by rfl⟩ : syracuseStep 8975551 = 13463327) B13463327
theorem B11967401 : Blo 2183435 11967401 := bstep (se 2 (by rfl) ⟨4487775, by rfl⟩ : syracuseStep 11967401 = 8975551) B8975551
theorem B7978267 : Blo 2183435 7978267 := bstep (se 1 (by rfl) ⟨5983700, by rfl⟩ : syracuseStep 7978267 = 11967401) B11967401
theorem B10637689 : Blo 2183435 10637689 := bstep (se 2 (by rfl) ⟨3989133, by rfl⟩ : syracuseStep 10637689 = 7978267) B7978267
theorem B14183585 : Blo 2183435 14183585 := bstep (se 2 (by rfl) ⟨5318844, by rfl⟩ : syracuseStep 14183585 = 10637689) B10637689
theorem B9455723 : Blo 2183435 9455723 := bstep (se 1 (by rfl) ⟨7091792, by rfl⟩ : syracuseStep 9455723 = 14183585) B14183585
theorem B6303815 : Blo 2183435 6303815 := bstep (se 1 (by rfl) ⟨4727861, by rfl⟩ : syracuseStep 6303815 = 9455723) B9455723
theorem B4202543 : Blo 2183435 4202543 := bstep (se 1 (by rfl) ⟨3151907, by rfl⟩ : syracuseStep 4202543 = 6303815) B6303815
theorem B11206781 : Blo 2183435 11206781 := bstep (se 3 (by rfl) ⟨2101271, by rfl⟩ : syracuseStep 11206781 = 4202543) B4202543
theorem B7471187 : Blo 2183435 7471187 := bstep (se 1 (by rfl) ⟨5603390, by rfl⟩ : syracuseStep 7471187 = 11206781) B11206781
theorem B4980791 : Blo 2183435 4980791 := bstep (se 1 (by rfl) ⟨3735593, by rfl⟩ : syracuseStep 4980791 = 7471187) B7471187
theorem B3320527 : Blo 2183435 3320527 := bstep (se 1 (by rfl) ⟨2490395, by rfl⟩ : syracuseStep 3320527 = 4980791) B4980791
theorem B4427369 : Blo 2183435 4427369 := bstep (se 2 (by rfl) ⟨1660263, by rfl⟩ : syracuseStep 4427369 = 3320527) B3320527
theorem B2951579 : Blo 2183435 2951579 := bstep (se 1 (by rfl) ⟨2213684, by rfl⟩ : syracuseStep 2951579 = 4427369) B4427369
theorem B7870877 : Blo 2183435 7870877 := bstep (se 3 (by rfl) ⟨1475789, by rfl⟩ : syracuseStep 7870877 = 2951579) B2951579
theorem B5247251 : Blo 2183435 5247251 := bstep (se 1 (by rfl) ⟨3935438, by rfl⟩ : syracuseStep 5247251 = 7870877) B7870877
theorem B3498167 : Blo 2183435 3498167 := bstep (se 1 (by rfl) ⟨2623625, by rfl⟩ : syracuseStep 3498167 = 5247251) B5247251
theorem B9328445 : Blo 2183435 9328445 := bstep (se 3 (by rfl) ⟨1749083, by rfl⟩ : syracuseStep 9328445 = 3498167) B3498167
theorem B6218963 : Blo 2183435 6218963 := bstep (se 1 (by rfl) ⟨4664222, by rfl⟩ : syracuseStep 6218963 = 9328445) B9328445
theorem B4145975 : Blo 2183435 4145975 := bstep (se 1 (by rfl) ⟨3109481, by rfl⟩ : syracuseStep 4145975 = 6218963) B6218963
theorem B2763983 : Blo 2183435 2763983 := bstep (se 1 (by rfl) ⟨2072987, by rfl⟩ : syracuseStep 2763983 = 4145975) B4145975
theorem B7370621 : Blo 2183435 7370621 := bstep (se 3 (by rfl) ⟨1381991, by rfl⟩ : syracuseStep 7370621 = 2763983) B2763983
theorem B4913747 : Blo 2183435 4913747 := bstep (se 1 (by rfl) ⟨3685310, by rfl⟩ : syracuseStep 4913747 = 7370621) B7370621
theorem B3275831 : Blo 2183435 3275831 := bstep (se 1 (by rfl) ⟨2456873, by rfl⟩ : syracuseStep 3275831 = 4913747) B4913747
theorem B2183887 : Blo 2183435 2183887 := bstep (se 1 (by rfl) ⟨1637915, by rfl⟩ : syracuseStep 2183887 = 3275831) B3275831
theorem B3275837 : Blo 2183435 3275837 := bbase (se 3 (by rfl) ⟨614219, by rfl⟩ : syracuseStep 3275837 = 1228439) (by norm_num)
theorem B2183891 : Blo 2183435 2183891 := bstep (se 1 (by rfl) ⟨1637918, by rfl⟩ : syracuseStep 2183891 = 3275837) B3275837
theorem B4913765 : Blo 2183435 4913765 := bbase (se 4 (by rfl) ⟨460665, by rfl⟩ : syracuseStep 4913765 = 921331) (by norm_num)
theorem B3275843 : Blo 2183435 3275843 := bstep (se 1 (by rfl) ⟨2456882, by rfl⟩ : syracuseStep 3275843 = 4913765) B4913765
theorem B2183895 : Blo 2183435 2183895 := bstep (se 1 (by rfl) ⟨1637921, by rfl⟩ : syracuseStep 2183895 = 3275843) B3275843
theorem B5527997 : Blo 2183435 5527997 := bbase (se 3 (by rfl) ⟨1036499, by rfl⟩ : syracuseStep 5527997 = 2072999) (by norm_num)
theorem B3685331 : Blo 2183435 3685331 := bstep (se 1 (by rfl) ⟨2763998, by rfl⟩ : syracuseStep 3685331 = 5527997) B5527997
theorem B2456887 : Blo 2183435 2456887 := bstep (se 1 (by rfl) ⟨1842665, by rfl⟩ : syracuseStep 2456887 = 3685331) B3685331
theorem B3275849 : Blo 2183435 3275849 := bstep (se 2 (by rfl) ⟨1228443, by rfl⟩ : syracuseStep 3275849 = 2456887) B2456887
theorem B2183899 : Blo 2183435 2183899 := bstep (se 1 (by rfl) ⟨1637924, by rfl⟩ : syracuseStep 2183899 = 3275849) B3275849
theorem B4146005 : Blo 2183435 4146005 := bbase (se 9 (by rfl) ⟨12146, by rfl⟩ : syracuseStep 4146005 = 24293) (by norm_num)
theorem B11056013 : Blo 2183435 11056013 := bstep (se 3 (by rfl) ⟨2073002, by rfl⟩ : syracuseStep 11056013 = 4146005) B4146005
theorem B7370675 : Blo 2183435 7370675 := bstep (se 1 (by rfl) ⟨5528006, by rfl⟩ : syracuseStep 7370675 = 11056013) B11056013
theorem B4913783 : Blo 2183435 4913783 := bstep (se 1 (by rfl) ⟨3685337, by rfl⟩ : syracuseStep 4913783 = 7370675) B7370675
theorem B3275855 : Blo 2183435 3275855 := bstep (se 1 (by rfl) ⟨2456891, by rfl⟩ : syracuseStep 3275855 = 4913783) B4913783
theorem B2183903 : Blo 2183435 2183903 := bstep (se 1 (by rfl) ⟨1637927, by rfl⟩ : syracuseStep 2183903 = 3275855) B3275855
theorem B3275861 : Blo 2183435 3275861 := bbase (se 8 (by rfl) ⟨19194, by rfl⟩ : syracuseStep 3275861 = 38389) (by norm_num)
theorem B2183907 : Blo 2183435 2183907 := bstep (se 1 (by rfl) ⟨1637930, by rfl⟩ : syracuseStep 2183907 = 3275861) B3275861
theorem B13992821 : Blo 2183435 13992821 := bbase (se 5 (by rfl) ⟨655913, by rfl⟩ : syracuseStep 13992821 = 1311827) (by norm_num)
theorem B9328547 : Blo 2183435 9328547 := bstep (se 1 (by rfl) ⟨6996410, by rfl⟩ : syracuseStep 9328547 = 13992821) B13992821
theorem B6219031 : Blo 2183435 6219031 := bstep (se 1 (by rfl) ⟨4664273, by rfl⟩ : syracuseStep 6219031 = 9328547) B9328547
theorem B8292041 : Blo 2183435 8292041 := bstep (se 2 (by rfl) ⟨3109515, by rfl⟩ : syracuseStep 8292041 = 6219031) B6219031
theorem B5528027 : Blo 2183435 5528027 := bstep (se 1 (by rfl) ⟨4146020, by rfl⟩ : syracuseStep 5528027 = 8292041) B8292041
theorem B3685351 : Blo 2183435 3685351 := bstep (se 1 (by rfl) ⟨2764013, by rfl⟩ : syracuseStep 3685351 = 5528027) B5528027
theorem B4913801 : Blo 2183435 4913801 := bstep (se 2 (by rfl) ⟨1842675, by rfl⟩ : syracuseStep 4913801 = 3685351) B3685351
theorem B3275867 : Blo 2183435 3275867 := bstep (se 1 (by rfl) ⟨2456900, by rfl⟩ : syracuseStep 3275867 = 4913801) B4913801
theorem B2183911 : Blo 2183435 2183911 := bstep (se 1 (by rfl) ⟨1637933, by rfl⟩ : syracuseStep 2183911 = 3275867) B3275867
theorem B2456905 : Blo 2183435 2456905 := bbase (se 2 (by rfl) ⟨921339, by rfl⟩ : syracuseStep 2456905 = 1842679) (by norm_num)
theorem B3275873 : Blo 2183435 3275873 := bstep (se 2 (by rfl) ⟨1228452, by rfl⟩ : syracuseStep 3275873 = 2456905) B2456905
theorem B2183915 : Blo 2183435 2183915 := bstep (se 1 (by rfl) ⟨1637936, by rfl⟩ : syracuseStep 2183915 = 3275873) B3275873
theorem B19923445 : Blo 2183435 19923445 := bbase (se 5 (by rfl) ⟨933911, by rfl⟩ : syracuseStep 19923445 = 1867823) (by norm_num)
theorem B26564593 : Blo 2183435 26564593 := bstep (se 2 (by rfl) ⟨9961722, by rfl⟩ : syracuseStep 26564593 = 19923445) B19923445
theorem B35419457 : Blo 2183435 35419457 := bstep (se 2 (by rfl) ⟨13282296, by rfl⟩ : syracuseStep 35419457 = 26564593) B26564593
theorem B23612971 : Blo 2183435 23612971 := bstep (se 1 (by rfl) ⟨17709728, by rfl⟩ : syracuseStep 23612971 = 35419457) B35419457
theorem B31483961 : Blo 2183435 31483961 := bstep (se 2 (by rfl) ⟨11806485, by rfl⟩ : syracuseStep 31483961 = 23612971) B23612971
theorem B20989307 : Blo 2183435 20989307 := bstep (se 1 (by rfl) ⟨15741980, by rfl⟩ : syracuseStep 20989307 = 31483961) B31483961
theorem B13992871 : Blo 2183435 13992871 := bstep (se 1 (by rfl) ⟨10494653, by rfl⟩ : syracuseStep 13992871 = 20989307) B20989307
theorem B18657161 : Blo 2183435 18657161 := bstep (se 2 (by rfl) ⟨6996435, by rfl⟩ : syracuseStep 18657161 = 13992871) B13992871
theorem B12438107 : Blo 2183435 12438107 := bstep (se 1 (by rfl) ⟨9328580, by rfl⟩ : syracuseStep 12438107 = 18657161) B18657161
theorem B8292071 : Blo 2183435 8292071 := bstep (se 1 (by rfl) ⟨6219053, by rfl⟩ : syracuseStep 8292071 = 12438107) B12438107
theorem B5528047 : Blo 2183435 5528047 := bstep (se 1 (by rfl) ⟨4146035, by rfl⟩ : syracuseStep 5528047 = 8292071) B8292071
theorem B7370729 : Blo 2183435 7370729 := bstep (se 2 (by rfl) ⟨2764023, by rfl⟩ : syracuseStep 7370729 = 5528047) B5528047
theorem B4913819 : Blo 2183435 4913819 := bstep (se 1 (by rfl) ⟨3685364, by rfl⟩ : syracuseStep 4913819 = 7370729) B7370729
theorem B3275879 : Blo 2183435 3275879 := bstep (se 1 (by rfl) ⟨2456909, by rfl⟩ : syracuseStep 3275879 = 4913819) B4913819
theorem B2183919 : Blo 2183435 2183919 := bstep (se 1 (by rfl) ⟨1637939, by rfl⟩ : syracuseStep 2183919 = 3275879) B3275879
theorem B3275885 : Blo 2183435 3275885 := bbase (se 3 (by rfl) ⟨614228, by rfl⟩ : syracuseStep 3275885 = 1228457) (by norm_num)
theorem B2183923 : Blo 2183435 2183923 := bstep (se 1 (by rfl) ⟨1637942, by rfl⟩ : syracuseStep 2183923 = 3275885) B3275885
theorem B4913837 : Blo 2183435 4913837 := bbase (se 3 (by rfl) ⟨921344, by rfl⟩ : syracuseStep 4913837 = 1842689) (by norm_num)
theorem B3275891 : Blo 2183435 3275891 := bstep (se 1 (by rfl) ⟨2456918, by rfl⟩ : syracuseStep 3275891 = 4913837) B4913837
theorem B2183927 : Blo 2183435 2183927 := bstep (se 1 (by rfl) ⟨1637945, by rfl⟩ : syracuseStep 2183927 = 3275891) B3275891
theorem B4664317 : Blo 2183435 4664317 := bbase (se 3 (by rfl) ⟨874559, by rfl⟩ : syracuseStep 4664317 = 1749119) (by norm_num)
theorem B6219089 : Blo 2183435 6219089 := bstep (se 2 (by rfl) ⟨2332158, by rfl⟩ : syracuseStep 6219089 = 4664317) B4664317
theorem B4146059 : Blo 2183435 4146059 := bstep (se 1 (by rfl) ⟨3109544, by rfl⟩ : syracuseStep 4146059 = 6219089) B6219089
theorem B2764039 : Blo 2183435 2764039 := bstep (se 1 (by rfl) ⟨2073029, by rfl⟩ : syracuseStep 2764039 = 4146059) B4146059
theorem B3685385 : Blo 2183435 3685385 := bstep (se 2 (by rfl) ⟨1382019, by rfl⟩ : syracuseStep 3685385 = 2764039) B2764039
theorem B2456923 : Blo 2183435 2456923 := bstep (se 1 (by rfl) ⟨1842692, by rfl⟩ : syracuseStep 2456923 = 3685385) B3685385
theorem B3275897 : Blo 2183435 3275897 := bstep (se 2 (by rfl) ⟨1228461, by rfl⟩ : syracuseStep 3275897 = 2456923) B2456923
theorem B2183931 : Blo 2183435 2183931 := bstep (se 1 (by rfl) ⟨1637948, by rfl⟩ : syracuseStep 2183931 = 3275897) B3275897
theorem B7573285 : Blo 2183435 7573285 := bbase (se 4 (by rfl) ⟨709995, by rfl⟩ : syracuseStep 7573285 = 1419991) (by norm_num)
theorem B10097713 : Blo 2183435 10097713 := bstep (se 2 (by rfl) ⟨3786642, by rfl⟩ : syracuseStep 10097713 = 7573285) B7573285
theorem B13463617 : Blo 2183435 13463617 := bstep (se 2 (by rfl) ⟨5048856, by rfl⟩ : syracuseStep 13463617 = 10097713) B10097713
theorem B17951489 : Blo 2183435 17951489 := bstep (se 2 (by rfl) ⟨6731808, by rfl⟩ : syracuseStep 17951489 = 13463617) B13463617
theorem B11967659 : Blo 2183435 11967659 := bstep (se 1 (by rfl) ⟨8975744, by rfl⟩ : syracuseStep 11967659 = 17951489) B17951489
theorem B7978439 : Blo 2183435 7978439 := bstep (se 1 (by rfl) ⟨5983829, by rfl⟩ : syracuseStep 7978439 = 11967659) B11967659
theorem B5318959 : Blo 2183435 5318959 := bstep (se 1 (by rfl) ⟨3989219, by rfl⟩ : syracuseStep 5318959 = 7978439) B7978439
theorem B7091945 : Blo 2183435 7091945 := bstep (se 2 (by rfl) ⟨2659479, by rfl⟩ : syracuseStep 7091945 = 5318959) B5318959
theorem B4727963 : Blo 2183435 4727963 := bstep (se 1 (by rfl) ⟨3545972, by rfl⟩ : syracuseStep 4727963 = 7091945) B7091945
theorem B3151975 : Blo 2183435 3151975 := bstep (se 1 (by rfl) ⟨2363981, by rfl⟩ : syracuseStep 3151975 = 4727963) B4727963
theorem B4202633 : Blo 2183435 4202633 := bstep (se 2 (by rfl) ⟨1575987, by rfl⟩ : syracuseStep 4202633 = 3151975) B3151975
theorem B2801755 : Blo 2183435 2801755 := bstep (se 1 (by rfl) ⟨2101316, by rfl⟩ : syracuseStep 2801755 = 4202633) B4202633
theorem B14942693 : Blo 2183435 14942693 := bstep (se 4 (by rfl) ⟨1400877, by rfl⟩ : syracuseStep 14942693 = 2801755) B2801755
theorem B9961795 : Blo 2183435 9961795 := bstep (se 1 (by rfl) ⟨7471346, by rfl⟩ : syracuseStep 9961795 = 14942693) B14942693
theorem B13282393 : Blo 2183435 13282393 := bstep (se 2 (by rfl) ⟨4980897, by rfl⟩ : syracuseStep 13282393 = 9961795) B9961795
theorem B17709857 : Blo 2183435 17709857 := bstep (se 2 (by rfl) ⟨6641196, by rfl⟩ : syracuseStep 17709857 = 13282393) B13282393
theorem B11806571 : Blo 2183435 11806571 := bstep (se 1 (by rfl) ⟨8854928, by rfl⟩ : syracuseStep 11806571 = 17709857) B17709857
theorem B31484189 : Blo 2183435 31484189 := bstep (se 3 (by rfl) ⟨5903285, by rfl⟩ : syracuseStep 31484189 = 11806571) B11806571
theorem B20989459 : Blo 2183435 20989459 := bstep (se 1 (by rfl) ⟨15742094, by rfl⟩ : syracuseStep 20989459 = 31484189) B31484189
theorem B27985945 : Blo 2183435 27985945 := bstep (se 2 (by rfl) ⟨10494729, by rfl⟩ : syracuseStep 27985945 = 20989459) B20989459
theorem B37314593 : Blo 2183435 37314593 := bstep (se 2 (by rfl) ⟨13992972, by rfl⟩ : syracuseStep 37314593 = 27985945) B27985945
theorem B24876395 : Blo 2183435 24876395 := bstep (se 1 (by rfl) ⟨18657296, by rfl⟩ : syracuseStep 24876395 = 37314593) B37314593
theorem B16584263 : Blo 2183435 16584263 := bstep (se 1 (by rfl) ⟨12438197, by rfl⟩ : syracuseStep 16584263 = 24876395) B24876395
theorem B11056175 : Blo 2183435 11056175 := bstep (se 1 (by rfl) ⟨8292131, by rfl⟩ : syracuseStep 11056175 = 16584263) B16584263
theorem B7370783 : Blo 2183435 7370783 := bstep (se 1 (by rfl) ⟨5528087, by rfl⟩ : syracuseStep 7370783 = 11056175) B11056175
theorem B4913855 : Blo 2183435 4913855 := bstep (se 1 (by rfl) ⟨3685391, by rfl⟩ : syracuseStep 4913855 = 7370783) B7370783
theorem B3275903 : Blo 2183435 3275903 := bstep (se 1 (by rfl) ⟨2456927, by rfl⟩ : syracuseStep 3275903 = 4913855) B4913855
theorem B2183935 : Blo 2183435 2183935 := bstep (se 1 (by rfl) ⟨1637951, by rfl⟩ : syracuseStep 2183935 = 3275903) B3275903
theorem B3275909 : Blo 2183435 3275909 := bbase (se 4 (by rfl) ⟨307116, by rfl⟩ : syracuseStep 3275909 = 614233) (by norm_num)
theorem B2183939 : Blo 2183435 2183939 := bstep (se 1 (by rfl) ⟨1637954, by rfl⟩ : syracuseStep 2183939 = 3275909) B3275909
theorem B3685405 : Blo 2183435 3685405 := bbase (se 3 (by rfl) ⟨691013, by rfl⟩ : syracuseStep 3685405 = 1382027) (by norm_num)
theorem B4913873 : Blo 2183435 4913873 := bstep (se 2 (by rfl) ⟨1842702, by rfl⟩ : syracuseStep 4913873 = 3685405) B3685405
theorem B3275915 : Blo 2183435 3275915 := bstep (se 1 (by rfl) ⟨2456936, by rfl⟩ : syracuseStep 3275915 = 4913873) B4913873
theorem B2183943 : Blo 2183435 2183943 := bstep (se 1 (by rfl) ⟨1637957, by rfl⟩ : syracuseStep 2183943 = 3275915) B3275915
theorem B2456941 : Blo 2183435 2456941 := bbase (se 3 (by rfl) ⟨460676, by rfl⟩ : syracuseStep 2456941 = 921353) (by norm_num)
theorem B3275921 : Blo 2183435 3275921 := bstep (se 2 (by rfl) ⟨1228470, by rfl⟩ : syracuseStep 3275921 = 2456941) B2456941
theorem B2183947 : Blo 2183435 2183947 := bstep (se 1 (by rfl) ⟨1637960, by rfl⟩ : syracuseStep 2183947 = 3275921) B3275921
theorem B7370837 : Blo 2183435 7370837 := bbase (se 8 (by rfl) ⟨43188, by rfl⟩ : syracuseStep 7370837 = 86377) (by norm_num)
theorem B4913891 : Blo 2183435 4913891 := bstep (se 1 (by rfl) ⟨3685418, by rfl⟩ : syracuseStep 4913891 = 7370837) B7370837
theorem B3275927 : Blo 2183435 3275927 := bstep (se 1 (by rfl) ⟨2456945, by rfl⟩ : syracuseStep 3275927 = 4913891) B4913891
theorem B2183951 : Blo 2183435 2183951 := bstep (se 1 (by rfl) ⟨1637963, by rfl⟩ : syracuseStep 2183951 = 3275927) B3275927
theorem B3275933 : Blo 2183435 3275933 := bbase (se 3 (by rfl) ⟨614237, by rfl⟩ : syracuseStep 3275933 = 1228475) (by norm_num)
theorem B2183955 : Blo 2183435 2183955 := bstep (se 1 (by rfl) ⟨1637966, by rfl⟩ : syracuseStep 2183955 = 3275933) B3275933
theorem B4913909 : Blo 2183435 4913909 := bbase (se 5 (by rfl) ⟨230339, by rfl⟩ : syracuseStep 4913909 = 460679) (by norm_num)
theorem B3275939 : Blo 2183435 3275939 := bstep (se 1 (by rfl) ⟨2456954, by rfl⟩ : syracuseStep 3275939 = 4913909) B4913909
theorem B2183959 : Blo 2183435 2183959 := bstep (se 1 (by rfl) ⟨1637969, by rfl⟩ : syracuseStep 2183959 = 3275939) B3275939
theorem B8855045 : Blo 2183435 8855045 := bbase (se 4 (by rfl) ⟨830160, by rfl⟩ : syracuseStep 8855045 = 1660321) (by norm_num)
theorem B5903363 : Blo 2183435 5903363 := bstep (se 1 (by rfl) ⟨4427522, by rfl⟩ : syracuseStep 5903363 = 8855045) B8855045
theorem B3935575 : Blo 2183435 3935575 := bstep (se 1 (by rfl) ⟨2951681, by rfl⟩ : syracuseStep 3935575 = 5903363) B5903363
theorem B5247433 : Blo 2183435 5247433 := bstep (se 2 (by rfl) ⟨1967787, by rfl⟩ : syracuseStep 5247433 = 3935575) B3935575
theorem B27986309 : Blo 2183435 27986309 := bstep (se 4 (by rfl) ⟨2623716, by rfl⟩ : syracuseStep 27986309 = 5247433) B5247433
theorem B18657539 : Blo 2183435 18657539 := bstep (se 1 (by rfl) ⟨13993154, by rfl⟩ : syracuseStep 18657539 = 27986309) B27986309
theorem B12438359 : Blo 2183435 12438359 := bstep (se 1 (by rfl) ⟨9328769, by rfl⟩ : syracuseStep 12438359 = 18657539) B18657539
theorem B8292239 : Blo 2183435 8292239 := bstep (se 1 (by rfl) ⟨6219179, by rfl⟩ : syracuseStep 8292239 = 12438359) B12438359
theorem B5528159 : Blo 2183435 5528159 := bstep (se 1 (by rfl) ⟨4146119, by rfl⟩ : syracuseStep 5528159 = 8292239) B8292239
theorem B3685439 : Blo 2183435 3685439 := bstep (se 1 (by rfl) ⟨2764079, by rfl⟩ : syracuseStep 3685439 = 5528159) B5528159
theorem B2456959 : Blo 2183435 2456959 := bstep (se 1 (by rfl) ⟨1842719, by rfl⟩ : syracuseStep 2456959 = 3685439) B3685439
theorem B3275945 : Blo 2183435 3275945 := bstep (se 2 (by rfl) ⟨1228479, by rfl⟩ : syracuseStep 3275945 = 2456959) B2456959
theorem B2183963 : Blo 2183435 2183963 := bstep (se 1 (by rfl) ⟨1637972, by rfl⟩ : syracuseStep 2183963 = 3275945) B3275945
theorem B4980973 : Blo 2183435 4980973 := bbase (se 3 (by rfl) ⟨933932, by rfl⟩ : syracuseStep 4980973 = 1867865) (by norm_num)
theorem B6641297 : Blo 2183435 6641297 := bstep (se 2 (by rfl) ⟨2490486, by rfl⟩ : syracuseStep 6641297 = 4980973) B4980973
theorem B4427531 : Blo 2183435 4427531 := bstep (se 1 (by rfl) ⟨3320648, by rfl⟩ : syracuseStep 4427531 = 6641297) B6641297
theorem B2951687 : Blo 2183435 2951687 := bstep (se 1 (by rfl) ⟨2213765, by rfl⟩ : syracuseStep 2951687 = 4427531) B4427531
theorem B7871165 : Blo 2183435 7871165 := bstep (se 3 (by rfl) ⟨1475843, by rfl⟩ : syracuseStep 7871165 = 2951687) B2951687
theorem B5247443 : Blo 2183435 5247443 := bstep (se 1 (by rfl) ⟨3935582, by rfl⟩ : syracuseStep 5247443 = 7871165) B7871165
theorem B3498295 : Blo 2183435 3498295 := bstep (se 1 (by rfl) ⟨2623721, by rfl⟩ : syracuseStep 3498295 = 5247443) B5247443
theorem B4664393 : Blo 2183435 4664393 := bstep (se 2 (by rfl) ⟨1749147, by rfl⟩ : syracuseStep 4664393 = 3498295) B3498295
theorem B3109595 : Blo 2183435 3109595 := bstep (se 1 (by rfl) ⟨2332196, by rfl⟩ : syracuseStep 3109595 = 4664393) B4664393
theorem B8292253 : Blo 2183435 8292253 := bstep (se 3 (by rfl) ⟨1554797, by rfl⟩ : syracuseStep 8292253 = 3109595) B3109595
theorem B11056337 : Blo 2183435 11056337 := bstep (se 2 (by rfl) ⟨4146126, by rfl⟩ : syracuseStep 11056337 = 8292253) B8292253
theorem B7370891 : Blo 2183435 7370891 := bstep (se 1 (by rfl) ⟨5528168, by rfl⟩ : syracuseStep 7370891 = 11056337) B11056337
theorem B4913927 : Blo 2183435 4913927 := bstep (se 1 (by rfl) ⟨3685445, by rfl⟩ : syracuseStep 4913927 = 7370891) B7370891
theorem B3275951 : Blo 2183435 3275951 := bstep (se 1 (by rfl) ⟨2456963, by rfl⟩ : syracuseStep 3275951 = 4913927) B4913927
theorem B2183967 : Blo 2183435 2183967 := bstep (se 1 (by rfl) ⟨1637975, by rfl⟩ : syracuseStep 2183967 = 3275951) B3275951
theorem B3275957 : Blo 2183435 3275957 := bbase (se 5 (by rfl) ⟨153560, by rfl⟩ : syracuseStep 3275957 = 307121) (by norm_num)
theorem B2183971 : Blo 2183435 2183971 := bstep (se 1 (by rfl) ⟨1637978, by rfl⟩ : syracuseStep 2183971 = 3275957) B3275957
theorem B5528189 : Blo 2183435 5528189 := bbase (se 3 (by rfl) ⟨1036535, by rfl⟩ : syracuseStep 5528189 = 2073071) (by norm_num)
theorem B3685459 : Blo 2183435 3685459 := bstep (se 1 (by rfl) ⟨2764094, by rfl⟩ : syracuseStep 3685459 = 5528189) B5528189
theorem B4913945 : Blo 2183435 4913945 := bstep (se 2 (by rfl) ⟨1842729, by rfl⟩ : syracuseStep 4913945 = 3685459) B3685459
theorem B3275963 : Blo 2183435 3275963 := bstep (se 1 (by rfl) ⟨2456972, by rfl⟩ : syracuseStep 3275963 = 4913945) B4913945
theorem B2183975 : Blo 2183435 2183975 := bstep (se 1 (by rfl) ⟨1637981, by rfl⟩ : syracuseStep 2183975 = 3275963) B3275963
theorem B2456977 : Blo 2183435 2456977 := bbase (se 2 (by rfl) ⟨921366, by rfl⟩ : syracuseStep 2456977 = 1842733) (by norm_num)
theorem B3275969 : Blo 2183435 3275969 := bstep (se 2 (by rfl) ⟨1228488, by rfl⟩ : syracuseStep 3275969 = 2456977) B2456977
theorem B2183979 : Blo 2183435 2183979 := bstep (se 1 (by rfl) ⟨1637984, by rfl⟩ : syracuseStep 2183979 = 3275969) B3275969
theorem B4146157 : Blo 2183435 4146157 := bbase (se 3 (by rfl) ⟨777404, by rfl⟩ : syracuseStep 4146157 = 1554809) (by norm_num)
theorem B5528209 : Blo 2183435 5528209 := bstep (se 2 (by rfl) ⟨2073078, by rfl⟩ : syracuseStep 5528209 = 4146157) B4146157
theorem B7370945 : Blo 2183435 7370945 := bstep (se 2 (by rfl) ⟨2764104, by rfl⟩ : syracuseStep 7370945 = 5528209) B5528209
theorem B4913963 : Blo 2183435 4913963 := bstep (se 1 (by rfl) ⟨3685472, by rfl⟩ : syracuseStep 4913963 = 7370945) B7370945
theorem B3275975 : Blo 2183435 3275975 := bstep (se 1 (by rfl) ⟨2456981, by rfl⟩ : syracuseStep 3275975 = 4913963) B4913963
theorem B2183983 : Blo 2183435 2183983 := bstep (se 1 (by rfl) ⟨1637987, by rfl⟩ : syracuseStep 2183983 = 3275975) B3275975
theorem B3275981 : Blo 2183435 3275981 := bbase (se 3 (by rfl) ⟨614246, by rfl⟩ : syracuseStep 3275981 = 1228493) (by norm_num)
theorem B2183987 : Blo 2183435 2183987 := bstep (se 1 (by rfl) ⟨1637990, by rfl⟩ : syracuseStep 2183987 = 3275981) B3275981
theorem B4913981 : Blo 2183435 4913981 := bbase (se 3 (by rfl) ⟨921371, by rfl⟩ : syracuseStep 4913981 = 1842743) (by norm_num)
theorem B3275987 : Blo 2183435 3275987 := bstep (se 1 (by rfl) ⟨2456990, by rfl⟩ : syracuseStep 3275987 = 4913981) B4913981
theorem B2183991 : Blo 2183435 2183991 := bstep (se 1 (by rfl) ⟨1637993, by rfl⟩ : syracuseStep 2183991 = 3275987) B3275987
theorem B3685493 : Blo 2183435 3685493 := bbase (se 5 (by rfl) ⟨172757, by rfl⟩ : syracuseStep 3685493 = 345515) (by norm_num)
theorem B2456995 : Blo 2183435 2456995 := bstep (se 1 (by rfl) ⟨1842746, by rfl⟩ : syracuseStep 2456995 = 3685493) B3685493
theorem B3275993 : Blo 2183435 3275993 := bstep (se 2 (by rfl) ⟨1228497, by rfl⟩ : syracuseStep 3275993 = 2456995) B2456995
theorem B2183995 : Blo 2183435 2183995 := bstep (se 1 (by rfl) ⟨1637996, by rfl⟩ : syracuseStep 2183995 = 3275993) B3275993
theorem B4664461 : Blo 2183435 4664461 := bbase (se 3 (by rfl) ⟨874586, by rfl⟩ : syracuseStep 4664461 = 1749173) (by norm_num)
theorem B6219281 : Blo 2183435 6219281 := bstep (se 2 (by rfl) ⟨2332230, by rfl⟩ : syracuseStep 6219281 = 4664461) B4664461
theorem B16584749 : Blo 2183435 16584749 := bstep (se 3 (by rfl) ⟨3109640, by rfl⟩ : syracuseStep 16584749 = 6219281) B6219281
theorem B11056499 : Blo 2183435 11056499 := bstep (se 1 (by rfl) ⟨8292374, by rfl⟩ : syracuseStep 11056499 = 16584749) B16584749
theorem B7370999 : Blo 2183435 7370999 := bstep (se 1 (by rfl) ⟨5528249, by rfl⟩ : syracuseStep 7370999 = 11056499) B11056499
theorem B4913999 : Blo 2183435 4913999 := bstep (se 1 (by rfl) ⟨3685499, by rfl⟩ : syracuseStep 4913999 = 7370999) B7370999
theorem B3275999 : Blo 2183435 3275999 := bstep (se 1 (by rfl) ⟨2456999, by rfl⟩ : syracuseStep 3275999 = 4913999) B4913999
theorem B2183999 : Blo 2183435 2183999 := bstep (se 1 (by rfl) ⟨1637999, by rfl⟩ : syracuseStep 2183999 = 3275999) B3275999
theorem B3276005 : Blo 2183435 3276005 := bbase (se 4 (by rfl) ⟨307125, by rfl⟩ : syracuseStep 3276005 = 614251) (by norm_num)
theorem B2184003 : Blo 2183435 2184003 := bstep (se 1 (by rfl) ⟨1638002, by rfl⟩ : syracuseStep 2184003 = 3276005) B3276005
theorem B5465269 : Blo 2183435 5465269 := bbase (se 5 (by rfl) ⟨256184, by rfl⟩ : syracuseStep 5465269 = 512369) (by norm_num)
theorem B7287025 : Blo 2183435 7287025 := bstep (se 2 (by rfl) ⟨2732634, by rfl⟩ : syracuseStep 7287025 = 5465269) B5465269
theorem B9716033 : Blo 2183435 9716033 := bstep (se 2 (by rfl) ⟨3643512, by rfl⟩ : syracuseStep 9716033 = 7287025) B7287025
theorem B6477355 : Blo 2183435 6477355 := bstep (se 1 (by rfl) ⟨4858016, by rfl⟩ : syracuseStep 6477355 = 9716033) B9716033
theorem B8636473 : Blo 2183435 8636473 := bstep (se 2 (by rfl) ⟨3238677, by rfl⟩ : syracuseStep 8636473 = 6477355) B6477355
theorem B11515297 : Blo 2183435 11515297 := bstep (se 2 (by rfl) ⟨4318236, by rfl⟩ : syracuseStep 11515297 = 8636473) B8636473
theorem B15353729 : Blo 2183435 15353729 := bstep (se 2 (by rfl) ⟨5757648, by rfl⟩ : syracuseStep 15353729 = 11515297) B11515297
theorem B10235819 : Blo 2183435 10235819 := bstep (se 1 (by rfl) ⟨7676864, by rfl⟩ : syracuseStep 10235819 = 15353729) B15353729
theorem B27295517 : Blo 2183435 27295517 := bstep (se 3 (by rfl) ⟨5117909, by rfl⟩ : syracuseStep 27295517 = 10235819) B10235819
theorem B18197011 : Blo 2183435 18197011 := bstep (se 1 (by rfl) ⟨13647758, by rfl⟩ : syracuseStep 18197011 = 27295517) B27295517
theorem B24262681 : Blo 2183435 24262681 := bstep (se 2 (by rfl) ⟨9098505, by rfl⟩ : syracuseStep 24262681 = 18197011) B18197011
theorem B32350241 : Blo 2183435 32350241 := bstep (se 2 (by rfl) ⟨12131340, by rfl⟩ : syracuseStep 32350241 = 24262681) B24262681
theorem B21566827 : Blo 2183435 21566827 := bstep (se 1 (by rfl) ⟨16175120, by rfl⟩ : syracuseStep 21566827 = 32350241) B32350241
theorem B115023077 : Blo 2183435 115023077 := bstep (se 4 (by rfl) ⟨10783413, by rfl⟩ : syracuseStep 115023077 = 21566827) B21566827
theorem B76682051 : Blo 2183435 76682051 := bstep (se 1 (by rfl) ⟨57511538, by rfl⟩ : syracuseStep 76682051 = 115023077) B115023077
theorem B51121367 : Blo 2183435 51121367 := bstep (se 1 (by rfl) ⟨38341025, by rfl⟩ : syracuseStep 51121367 = 76682051) B76682051
theorem B34080911 : Blo 2183435 34080911 := bstep (se 1 (by rfl) ⟨25560683, by rfl⟩ : syracuseStep 34080911 = 51121367) B51121367
theorem B22720607 : Blo 2183435 22720607 := bstep (se 1 (by rfl) ⟨17040455, by rfl⟩ : syracuseStep 22720607 = 34080911) B34080911
theorem B15147071 : Blo 2183435 15147071 := bstep (se 1 (by rfl) ⟨11360303, by rfl⟩ : syracuseStep 15147071 = 22720607) B22720607
theorem B10098047 : Blo 2183435 10098047 := bstep (se 1 (by rfl) ⟨7573535, by rfl⟩ : syracuseStep 10098047 = 15147071) B15147071
theorem B6732031 : Blo 2183435 6732031 := bstep (se 1 (by rfl) ⟨5049023, by rfl⟩ : syracuseStep 6732031 = 10098047) B10098047
theorem B8976041 : Blo 2183435 8976041 := bstep (se 2 (by rfl) ⟨3366015, by rfl⟩ : syracuseStep 8976041 = 6732031) B6732031
theorem B5984027 : Blo 2183435 5984027 := bstep (se 1 (by rfl) ⟨4488020, by rfl⟩ : syracuseStep 5984027 = 8976041) B8976041
theorem B3989351 : Blo 2183435 3989351 := bstep (se 1 (by rfl) ⟨2992013, by rfl⟩ : syracuseStep 3989351 = 5984027) B5984027
theorem B10638269 : Blo 2183435 10638269 := bstep (se 3 (by rfl) ⟨1994675, by rfl⟩ : syracuseStep 10638269 = 3989351) B3989351
theorem B7092179 : Blo 2183435 7092179 := bstep (se 1 (by rfl) ⟨5319134, by rfl⟩ : syracuseStep 7092179 = 10638269) B10638269
theorem B4728119 : Blo 2183435 4728119 := bstep (se 1 (by rfl) ⟨3546089, by rfl⟩ : syracuseStep 4728119 = 7092179) B7092179
theorem B12608317 : Blo 2183435 12608317 := bstep (se 3 (by rfl) ⟨2364059, by rfl⟩ : syracuseStep 12608317 = 4728119) B4728119
theorem B67244357 : Blo 2183435 67244357 := bstep (se 4 (by rfl) ⟨6304158, by rfl⟩ : syracuseStep 67244357 = 12608317) B12608317
theorem B44829571 : Blo 2183435 44829571 := bstep (se 1 (by rfl) ⟨33622178, by rfl⟩ : syracuseStep 44829571 = 67244357) B67244357
theorem B59772761 : Blo 2183435 59772761 := bstep (se 2 (by rfl) ⟨22414785, by rfl⟩ : syracuseStep 59772761 = 44829571) B44829571
theorem B39848507 : Blo 2183435 39848507 := bstep (se 1 (by rfl) ⟨29886380, by rfl⟩ : syracuseStep 39848507 = 59772761) B59772761
theorem B26565671 : Blo 2183435 26565671 := bstep (se 1 (by rfl) ⟨19924253, by rfl⟩ : syracuseStep 26565671 = 39848507) B39848507
theorem B17710447 : Blo 2183435 17710447 := bstep (se 1 (by rfl) ⟨13282835, by rfl⟩ : syracuseStep 17710447 = 26565671) B26565671
theorem B23613929 : Blo 2183435 23613929 := bstep (se 2 (by rfl) ⟨8855223, by rfl⟩ : syracuseStep 23613929 = 17710447) B17710447
theorem B15742619 : Blo 2183435 15742619 := bstep (se 1 (by rfl) ⟨11806964, by rfl⟩ : syracuseStep 15742619 = 23613929) B23613929
theorem B10495079 : Blo 2183435 10495079 := bstep (se 1 (by rfl) ⟨7871309, by rfl⟩ : syracuseStep 10495079 = 15742619) B15742619
theorem B6996719 : Blo 2183435 6996719 := bstep (se 1 (by rfl) ⟨5247539, by rfl⟩ : syracuseStep 6996719 = 10495079) B10495079
theorem B4664479 : Blo 2183435 4664479 := bstep (se 1 (by rfl) ⟨3498359, by rfl⟩ : syracuseStep 4664479 = 6996719) B6996719
theorem B6219305 : Blo 2183435 6219305 := bstep (se 2 (by rfl) ⟨2332239, by rfl⟩ : syracuseStep 6219305 = 4664479) B4664479
theorem B4146203 : Blo 2183435 4146203 := bstep (se 1 (by rfl) ⟨3109652, by rfl⟩ : syracuseStep 4146203 = 6219305) B6219305
theorem B2764135 : Blo 2183435 2764135 := bstep (se 1 (by rfl) ⟨2073101, by rfl⟩ : syracuseStep 2764135 = 4146203) B4146203
theorem B3685513 : Blo 2183435 3685513 := bstep (se 2 (by rfl) ⟨1382067, by rfl⟩ : syracuseStep 3685513 = 2764135) B2764135
theorem B4914017 : Blo 2183435 4914017 := bstep (se 2 (by rfl) ⟨1842756, by rfl⟩ : syracuseStep 4914017 = 3685513) B3685513
theorem B3276011 : Blo 2183435 3276011 := bstep (se 1 (by rfl) ⟨2457008, by rfl⟩ : syracuseStep 3276011 = 4914017) B4914017
theorem B2184007 : Blo 2183435 2184007 := bstep (se 1 (by rfl) ⟨1638005, by rfl⟩ : syracuseStep 2184007 = 3276011) B3276011
theorem B2457013 : Blo 2183435 2457013 := bbase (se 5 (by rfl) ⟨115172, by rfl⟩ : syracuseStep 2457013 = 230345) (by norm_num)
theorem B3276017 : Blo 2183435 3276017 := bstep (se 2 (by rfl) ⟨1228506, by rfl⟩ : syracuseStep 3276017 = 2457013) B2457013
theorem B2184011 : Blo 2183435 2184011 := bstep (se 1 (by rfl) ⟨1638008, by rfl⟩ : syracuseStep 2184011 = 3276017) B3276017
theorem B2764145 : Blo 2183435 2764145 := bbase (se 2 (by rfl) ⟨1036554, by rfl⟩ : syracuseStep 2764145 = 2073109) (by norm_num)
theorem B7371053 : Blo 2183435 7371053 := bstep (se 3 (by rfl) ⟨1382072, by rfl⟩ : syracuseStep 7371053 = 2764145) B2764145
theorem B4914035 : Blo 2183435 4914035 := bstep (se 1 (by rfl) ⟨3685526, by rfl⟩ : syracuseStep 4914035 = 7371053) B7371053
theorem B3276023 : Blo 2183435 3276023 := bstep (se 1 (by rfl) ⟨2457017, by rfl⟩ : syracuseStep 3276023 = 4914035) B4914035
theorem B2184015 : Blo 2183435 2184015 := bstep (se 1 (by rfl) ⟨1638011, by rfl⟩ : syracuseStep 2184015 = 3276023) B3276023
theorem B3276029 : Blo 2183435 3276029 := bbase (se 3 (by rfl) ⟨614255, by rfl⟩ : syracuseStep 3276029 = 1228511) (by norm_num)
theorem B2184019 : Blo 2183435 2184019 := bstep (se 1 (by rfl) ⟨1638014, by rfl⟩ : syracuseStep 2184019 = 3276029) B3276029
theorem B4914053 : Blo 2183435 4914053 := bbase (se 4 (by rfl) ⟨460692, by rfl⟩ : syracuseStep 4914053 = 921385) (by norm_num)
theorem B3276035 : Blo 2183435 3276035 := bstep (se 1 (by rfl) ⟨2457026, by rfl⟩ : syracuseStep 3276035 = 4914053) B4914053
theorem B2184023 : Blo 2183435 2184023 := bstep (se 1 (by rfl) ⟨1638017, by rfl⟩ : syracuseStep 2184023 = 3276035) B3276035
theorem B2332261 : Blo 2183435 2332261 := bbase (se 4 (by rfl) ⟨218649, by rfl⟩ : syracuseStep 2332261 = 437299) (by norm_num)
theorem B3109681 : Blo 2183435 3109681 := bstep (se 2 (by rfl) ⟨1166130, by rfl⟩ : syracuseStep 3109681 = 2332261) B2332261
theorem B4146241 : Blo 2183435 4146241 := bstep (se 2 (by rfl) ⟨1554840, by rfl⟩ : syracuseStep 4146241 = 3109681) B3109681
theorem B5528321 : Blo 2183435 5528321 := bstep (se 2 (by rfl) ⟨2073120, by rfl⟩ : syracuseStep 5528321 = 4146241) B4146241
theorem B3685547 : Blo 2183435 3685547 := bstep (se 1 (by rfl) ⟨2764160, by rfl⟩ : syracuseStep 3685547 = 5528321) B5528321
theorem B2457031 : Blo 2183435 2457031 := bstep (se 1 (by rfl) ⟨1842773, by rfl⟩ : syracuseStep 2457031 = 3685547) B3685547
theorem B3276041 : Blo 2183435 3276041 := bstep (se 2 (by rfl) ⟨1228515, by rfl⟩ : syracuseStep 3276041 = 2457031) B2457031
theorem B2184027 : Blo 2183435 2184027 := bstep (se 1 (by rfl) ⟨1638020, by rfl⟩ : syracuseStep 2184027 = 3276041) B3276041
theorem B11056661 : Blo 2183435 11056661 := bbase (se 6 (by rfl) ⟨259140, by rfl⟩ : syracuseStep 11056661 = 518281) (by norm_num)
theorem B7371107 : Blo 2183435 7371107 := bstep (se 1 (by rfl) ⟨5528330, by rfl⟩ : syracuseStep 7371107 = 11056661) B11056661
theorem B4914071 : Blo 2183435 4914071 := bstep (se 1 (by rfl) ⟨3685553, by rfl⟩ : syracuseStep 4914071 = 7371107) B7371107
theorem B3276047 : Blo 2183435 3276047 := bstep (se 1 (by rfl) ⟨2457035, by rfl⟩ : syracuseStep 3276047 = 4914071) B4914071
theorem B2184031 : Blo 2183435 2184031 := bstep (se 1 (by rfl) ⟨1638023, by rfl⟩ : syracuseStep 2184031 = 3276047) B3276047
theorem B3276053 : Blo 2183435 3276053 := bbase (se 6 (by rfl) ⟨76782, by rfl⟩ : syracuseStep 3276053 = 153565) (by norm_num)
theorem B2184035 : Blo 2183435 2184035 := bstep (se 1 (by rfl) ⟨1638026, by rfl⟩ : syracuseStep 2184035 = 3276053) B3276053
theorem B4488085 : Blo 2183435 4488085 := bbase (se 6 (by rfl) ⟨105189, by rfl⟩ : syracuseStep 4488085 = 210379) (by norm_num)
theorem B5984113 : Blo 2183435 5984113 := bstep (se 2 (by rfl) ⟨2244042, by rfl⟩ : syracuseStep 5984113 = 4488085) B4488085
theorem B7978817 : Blo 2183435 7978817 := bstep (se 2 (by rfl) ⟨2992056, by rfl⟩ : syracuseStep 7978817 = 5984113) B5984113
theorem B5319211 : Blo 2183435 5319211 := bstep (se 1 (by rfl) ⟨3989408, by rfl⟩ : syracuseStep 5319211 = 7978817) B7978817
theorem B7092281 : Blo 2183435 7092281 := bstep (se 2 (by rfl) ⟨2659605, by rfl⟩ : syracuseStep 7092281 = 5319211) B5319211
theorem B18912749 : Blo 2183435 18912749 := bstep (se 3 (by rfl) ⟨3546140, by rfl⟩ : syracuseStep 18912749 = 7092281) B7092281
theorem B50433997 : Blo 2183435 50433997 := bstep (se 3 (by rfl) ⟨9456374, by rfl⟩ : syracuseStep 50433997 = 18912749) B18912749
theorem B67245329 : Blo 2183435 67245329 := bstep (se 2 (by rfl) ⟨25216998, by rfl⟩ : syracuseStep 67245329 = 50433997) B50433997
theorem B44830219 : Blo 2183435 44830219 := bstep (se 1 (by rfl) ⟨33622664, by rfl⟩ : syracuseStep 44830219 = 67245329) B67245329
theorem B59773625 : Blo 2183435 59773625 := bstep (se 2 (by rfl) ⟨22415109, by rfl⟩ : syracuseStep 59773625 = 44830219) B44830219
theorem B39849083 : Blo 2183435 39849083 := bstep (se 1 (by rfl) ⟨29886812, by rfl⟩ : syracuseStep 39849083 = 59773625) B59773625
theorem B26566055 : Blo 2183435 26566055 := bstep (se 1 (by rfl) ⟨19924541, by rfl⟩ : syracuseStep 26566055 = 39849083) B39849083
theorem B17710703 : Blo 2183435 17710703 := bstep (se 1 (by rfl) ⟨13283027, by rfl⟩ : syracuseStep 17710703 = 26566055) B26566055
theorem B11807135 : Blo 2183435 11807135 := bstep (se 1 (by rfl) ⟨8855351, by rfl⟩ : syracuseStep 11807135 = 17710703) B17710703
theorem B7871423 : Blo 2183435 7871423 := bstep (se 1 (by rfl) ⟨5903567, by rfl⟩ : syracuseStep 7871423 = 11807135) B11807135
theorem B20990461 : Blo 2183435 20990461 := bstep (se 3 (by rfl) ⟨3935711, by rfl⟩ : syracuseStep 20990461 = 7871423) B7871423
theorem B27987281 : Blo 2183435 27987281 := bstep (se 2 (by rfl) ⟨10495230, by rfl⟩ : syracuseStep 27987281 = 20990461) B20990461
theorem B18658187 : Blo 2183435 18658187 := bstep (se 1 (by rfl) ⟨13993640, by rfl⟩ : syracuseStep 18658187 = 27987281) B27987281
theorem B12438791 : Blo 2183435 12438791 := bstep (se 1 (by rfl) ⟨9329093, by rfl⟩ : syracuseStep 12438791 = 18658187) B18658187
theorem B8292527 : Blo 2183435 8292527 := bstep (se 1 (by rfl) ⟨6219395, by rfl⟩ : syracuseStep 8292527 = 12438791) B12438791
theorem B5528351 : Blo 2183435 5528351 := bstep (se 1 (by rfl) ⟨4146263, by rfl⟩ : syracuseStep 5528351 = 8292527) B8292527
theorem B3685567 : Blo 2183435 3685567 := bstep (se 1 (by rfl) ⟨2764175, by rfl⟩ : syracuseStep 3685567 = 5528351) B5528351
theorem B4914089 : Blo 2183435 4914089 := bstep (se 2 (by rfl) ⟨1842783, by rfl⟩ : syracuseStep 4914089 = 3685567) B3685567
theorem B3276059 : Blo 2183435 3276059 := bstep (se 1 (by rfl) ⟨2457044, by rfl⟩ : syracuseStep 3276059 = 4914089) B4914089
theorem B2184039 : Blo 2183435 2184039 := bstep (se 1 (by rfl) ⟨1638029, by rfl⟩ : syracuseStep 2184039 = 3276059) B3276059
theorem B2457049 : Blo 2183435 2457049 := bbase (se 2 (by rfl) ⟨921393, by rfl⟩ : syracuseStep 2457049 = 1842787) (by norm_num)
theorem B3276065 : Blo 2183435 3276065 := bstep (se 2 (by rfl) ⟨1228524, by rfl⟩ : syracuseStep 3276065 = 2457049) B2457049
theorem B2184043 : Blo 2183435 2184043 := bstep (se 1 (by rfl) ⟨1638032, by rfl⟩ : syracuseStep 2184043 = 3276065) B3276065
theorem B3109709 : Blo 2183435 3109709 := bbase (se 3 (by rfl) ⟨583070, by rfl⟩ : syracuseStep 3109709 = 1166141) (by norm_num)
theorem B8292557 : Blo 2183435 8292557 := bstep (se 3 (by rfl) ⟨1554854, by rfl⟩ : syracuseStep 8292557 = 3109709) B3109709
theorem B5528371 : Blo 2183435 5528371 := bstep (se 1 (by rfl) ⟨4146278, by rfl⟩ : syracuseStep 5528371 = 8292557) B8292557
theorem B7371161 : Blo 2183435 7371161 := bstep (se 2 (by rfl) ⟨2764185, by rfl⟩ : syracuseStep 7371161 = 5528371) B5528371
theorem B4914107 : Blo 2183435 4914107 := bstep (se 1 (by rfl) ⟨3685580, by rfl⟩ : syracuseStep 4914107 = 7371161) B7371161
theorem B3276071 : Blo 2183435 3276071 := bstep (se 1 (by rfl) ⟨2457053, by rfl⟩ : syracuseStep 3276071 = 4914107) B4914107
theorem B2184047 : Blo 2183435 2184047 := bstep (se 1 (by rfl) ⟨1638035, by rfl⟩ : syracuseStep 2184047 = 3276071) B3276071
theorem B3276077 : Blo 2183435 3276077 := bbase (se 3 (by rfl) ⟨614264, by rfl⟩ : syracuseStep 3276077 = 1228529) (by norm_num)
theorem B2184051 : Blo 2183435 2184051 := bstep (se 1 (by rfl) ⟨1638038, by rfl⟩ : syracuseStep 2184051 = 3276077) B3276077
theorem B4914125 : Blo 2183435 4914125 := bbase (se 3 (by rfl) ⟨921398, by rfl⟩ : syracuseStep 4914125 = 1842797) (by norm_num)
theorem B3276083 : Blo 2183435 3276083 := bstep (se 1 (by rfl) ⟨2457062, by rfl⟩ : syracuseStep 3276083 = 4914125) B4914125
theorem B2184055 : Blo 2183435 2184055 := bstep (se 1 (by rfl) ⟨1638041, by rfl⟩ : syracuseStep 2184055 = 3276083) B3276083
theorem B2764201 : Blo 2183435 2764201 := bbase (se 2 (by rfl) ⟨1036575, by rfl⟩ : syracuseStep 2764201 = 2073151) (by norm_num)
theorem B3685601 : Blo 2183435 3685601 := bstep (se 2 (by rfl) ⟨1382100, by rfl⟩ : syracuseStep 3685601 = 2764201) B2764201
theorem B2457067 : Blo 2183435 2457067 := bstep (se 1 (by rfl) ⟨1842800, by rfl⟩ : syracuseStep 2457067 = 3685601) B3685601
theorem B3276089 : Blo 2183435 3276089 := bstep (se 2 (by rfl) ⟨1228533, by rfl⟩ : syracuseStep 3276089 = 2457067) B2457067
theorem B2184059 : Blo 2183435 2184059 := bstep (se 1 (by rfl) ⟨1638044, by rfl⟩ : syracuseStep 2184059 = 3276089) B3276089
theorem B7871509 : Blo 2183435 7871509 := bbase (se 6 (by rfl) ⟨184488, by rfl⟩ : syracuseStep 7871509 = 368977) (by norm_num)
theorem B10495345 : Blo 2183435 10495345 := bstep (se 2 (by rfl) ⟨3935754, by rfl⟩ : syracuseStep 10495345 = 7871509) B7871509
theorem B13993793 : Blo 2183435 13993793 := bstep (se 2 (by rfl) ⟨5247672, by rfl⟩ : syracuseStep 13993793 = 10495345) B10495345
theorem B9329195 : Blo 2183435 9329195 := bstep (se 1 (by rfl) ⟨6996896, by rfl⟩ : syracuseStep 9329195 = 13993793) B13993793
theorem B24877853 : Blo 2183435 24877853 := bstep (se 3 (by rfl) ⟨4664597, by rfl⟩ : syracuseStep 24877853 = 9329195) B9329195
theorem B16585235 : Blo 2183435 16585235 := bstep (se 1 (by rfl) ⟨12438926, by rfl⟩ : syracuseStep 16585235 = 24877853) B24877853
theorem B11056823 : Blo 2183435 11056823 := bstep (se 1 (by rfl) ⟨8292617, by rfl⟩ : syracuseStep 11056823 = 16585235) B16585235
theorem B7371215 : Blo 2183435 7371215 := bstep (se 1 (by rfl) ⟨5528411, by rfl⟩ : syracuseStep 7371215 = 11056823) B11056823
theorem B4914143 : Blo 2183435 4914143 := bstep (se 1 (by rfl) ⟨3685607, by rfl⟩ : syracuseStep 4914143 = 7371215) B7371215
theorem B3276095 : Blo 2183435 3276095 := bstep (se 1 (by rfl) ⟨2457071, by rfl⟩ : syracuseStep 3276095 = 4914143) B4914143
theorem B2184063 : Blo 2183435 2184063 := bstep (se 1 (by rfl) ⟨1638047, by rfl⟩ : syracuseStep 2184063 = 3276095) B3276095
theorem B3276101 : Blo 2183435 3276101 := bbase (se 4 (by rfl) ⟨307134, by rfl⟩ : syracuseStep 3276101 = 614269) (by norm_num)
theorem B2184067 : Blo 2183435 2184067 := bstep (se 1 (by rfl) ⟨1638050, by rfl⟩ : syracuseStep 2184067 = 3276101) B3276101
theorem B3685621 : Blo 2183435 3685621 := bbase (se 5 (by rfl) ⟨172763, by rfl⟩ : syracuseStep 3685621 = 345527) (by norm_num)
theorem B4914161 : Blo 2183435 4914161 := bstep (se 2 (by rfl) ⟨1842810, by rfl⟩ : syracuseStep 4914161 = 3685621) B3685621
theorem B3276107 : Blo 2183435 3276107 := bstep (se 1 (by rfl) ⟨2457080, by rfl⟩ : syracuseStep 3276107 = 4914161) B4914161
theorem B2184071 : Blo 2183435 2184071 := bstep (se 1 (by rfl) ⟨1638053, by rfl⟩ : syracuseStep 2184071 = 3276107) B3276107
theorem B2457085 : Blo 2183435 2457085 := bbase (se 3 (by rfl) ⟨460703, by rfl⟩ : syracuseStep 2457085 = 921407) (by norm_num)
theorem B3276113 : Blo 2183435 3276113 := bstep (se 2 (by rfl) ⟨1228542, by rfl⟩ : syracuseStep 3276113 = 2457085) B2457085
theorem B2184075 : Blo 2183435 2184075 := bstep (se 1 (by rfl) ⟨1638056, by rfl⟩ : syracuseStep 2184075 = 3276113) B3276113
theorem B7371269 : Blo 2183435 7371269 := bbase (se 4 (by rfl) ⟨691056, by rfl⟩ : syracuseStep 7371269 = 1382113) (by norm_num)
theorem B4914179 : Blo 2183435 4914179 := bstep (se 1 (by rfl) ⟨3685634, by rfl⟩ : syracuseStep 4914179 = 7371269) B7371269
theorem B3276119 : Blo 2183435 3276119 := bstep (se 1 (by rfl) ⟨2457089, by rfl⟩ : syracuseStep 3276119 = 4914179) B4914179
theorem B2184079 : Blo 2183435 2184079 := bstep (se 1 (by rfl) ⟨1638059, by rfl⟩ : syracuseStep 2184079 = 3276119) B3276119
theorem B3276125 : Blo 2183435 3276125 := bbase (se 3 (by rfl) ⟨614273, by rfl⟩ : syracuseStep 3276125 = 1228547) (by norm_num)
theorem B2184083 : Blo 2183435 2184083 := bstep (se 1 (by rfl) ⟨1638062, by rfl⟩ : syracuseStep 2184083 = 3276125) B3276125
theorem B4914197 : Blo 2183435 4914197 := bbase (se 6 (by rfl) ⟨115176, by rfl⟩ : syracuseStep 4914197 = 230353) (by norm_num)
theorem B3276131 : Blo 2183435 3276131 := bstep (se 1 (by rfl) ⟨2457098, by rfl⟩ : syracuseStep 3276131 = 4914197) B4914197
theorem B2184087 : Blo 2183435 2184087 := bstep (se 1 (by rfl) ⟨1638065, by rfl⟩ : syracuseStep 2184087 = 3276131) B3276131
theorem B8292725 : Blo 2183435 8292725 := bbase (se 5 (by rfl) ⟨388721, by rfl⟩ : syracuseStep 8292725 = 777443) (by norm_num)
theorem B5528483 : Blo 2183435 5528483 := bstep (se 1 (by rfl) ⟨4146362, by rfl⟩ : syracuseStep 5528483 = 8292725) B8292725
theorem B3685655 : Blo 2183435 3685655 := bstep (se 1 (by rfl) ⟨2764241, by rfl⟩ : syracuseStep 3685655 = 5528483) B5528483
theorem B2457103 : Blo 2183435 2457103 := bstep (se 1 (by rfl) ⟨1842827, by rfl⟩ : syracuseStep 2457103 = 3685655) B3685655
theorem B3276137 : Blo 2183435 3276137 := bstep (se 2 (by rfl) ⟨1228551, by rfl⟩ : syracuseStep 3276137 = 2457103) B2457103
theorem B2184091 : Blo 2183435 2184091 := bstep (se 1 (by rfl) ⟨1638068, by rfl⟩ : syracuseStep 2184091 = 3276137) B3276137
theorem B2332333 : Blo 2183435 2332333 := bbase (se 3 (by rfl) ⟨437312, by rfl⟩ : syracuseStep 2332333 = 874625) (by norm_num)
theorem B12439109 : Blo 2183435 12439109 := bstep (se 4 (by rfl) ⟨1166166, by rfl⟩ : syracuseStep 12439109 = 2332333) B2332333
theorem B8292739 : Blo 2183435 8292739 := bstep (se 1 (by rfl) ⟨6219554, by rfl⟩ : syracuseStep 8292739 = 12439109) B12439109
theorem B11056985 : Blo 2183435 11056985 := bstep (se 2 (by rfl) ⟨4146369, by rfl⟩ : syracuseStep 11056985 = 8292739) B8292739
theorem B7371323 : Blo 2183435 7371323 := bstep (se 1 (by rfl) ⟨5528492, by rfl⟩ : syracuseStep 7371323 = 11056985) B11056985
theorem B4914215 : Blo 2183435 4914215 := bstep (se 1 (by rfl) ⟨3685661, by rfl⟩ : syracuseStep 4914215 = 7371323) B7371323
theorem B3276143 : Blo 2183435 3276143 := bstep (se 1 (by rfl) ⟨2457107, by rfl⟩ : syracuseStep 3276143 = 4914215) B4914215
theorem B2184095 : Blo 2183435 2184095 := bstep (se 1 (by rfl) ⟨1638071, by rfl⟩ : syracuseStep 2184095 = 3276143) B3276143
theorem B3276149 : Blo 2183435 3276149 := bbase (se 5 (by rfl) ⟨153569, by rfl⟩ : syracuseStep 3276149 = 307139) (by norm_num)
theorem B2184099 : Blo 2183435 2184099 := bstep (se 1 (by rfl) ⟨1638074, by rfl⟩ : syracuseStep 2184099 = 3276149) B3276149
theorem B3109789 : Blo 2183435 3109789 := bbase (se 3 (by rfl) ⟨583085, by rfl⟩ : syracuseStep 3109789 = 1166171) (by norm_num)
theorem B4146385 : Blo 2183435 4146385 := bstep (se 2 (by rfl) ⟨1554894, by rfl⟩ : syracuseStep 4146385 = 3109789) B3109789
theorem B5528513 : Blo 2183435 5528513 := bstep (se 2 (by rfl) ⟨2073192, by rfl⟩ : syracuseStep 5528513 = 4146385) B4146385
theorem B3685675 : Blo 2183435 3685675 := bstep (se 1 (by rfl) ⟨2764256, by rfl⟩ : syracuseStep 3685675 = 5528513) B5528513
theorem B4914233 : Blo 2183435 4914233 := bstep (se 2 (by rfl) ⟨1842837, by rfl⟩ : syracuseStep 4914233 = 3685675) B3685675
theorem B3276155 : Blo 2183435 3276155 := bstep (se 1 (by rfl) ⟨2457116, by rfl⟩ : syracuseStep 3276155 = 4914233) B4914233
theorem B2184103 : Blo 2183435 2184103 := bstep (se 1 (by rfl) ⟨1638077, by rfl⟩ : syracuseStep 2184103 = 3276155) B3276155
theorem B2457121 : Blo 2183435 2457121 := bbase (se 2 (by rfl) ⟨921420, by rfl⟩ : syracuseStep 2457121 = 1842841) (by norm_num)
theorem B3276161 : Blo 2183435 3276161 := bstep (se 2 (by rfl) ⟨1228560, by rfl⟩ : syracuseStep 3276161 = 2457121) B2457121
theorem B2184107 : Blo 2183435 2184107 := bstep (se 1 (by rfl) ⟨1638080, by rfl⟩ : syracuseStep 2184107 = 3276161) B3276161
theorem B5528533 : Blo 2183435 5528533 := bbase (se 7 (by rfl) ⟨64787, by rfl⟩ : syracuseStep 5528533 = 129575) (by norm_num)
theorem B7371377 : Blo 2183435 7371377 := bstep (se 2 (by rfl) ⟨2764266, by rfl⟩ : syracuseStep 7371377 = 5528533) B5528533
theorem B4914251 : Blo 2183435 4914251 := bstep (se 1 (by rfl) ⟨3685688, by rfl⟩ : syracuseStep 4914251 = 7371377) B7371377
theorem B3276167 : Blo 2183435 3276167 := bstep (se 1 (by rfl) ⟨2457125, by rfl⟩ : syracuseStep 3276167 = 4914251) B4914251
theorem B2184111 : Blo 2183435 2184111 := bstep (se 1 (by rfl) ⟨1638083, by rfl⟩ : syracuseStep 2184111 = 3276167) B3276167
theorem B3276173 : Blo 2183435 3276173 := bbase (se 3 (by rfl) ⟨614282, by rfl⟩ : syracuseStep 3276173 = 1228565) (by norm_num)
theorem B2184115 : Blo 2183435 2184115 := bstep (se 1 (by rfl) ⟨1638086, by rfl⟩ : syracuseStep 2184115 = 3276173) B3276173
theorem B4914269 : Blo 2183435 4914269 := bbase (se 3 (by rfl) ⟨921425, by rfl⟩ : syracuseStep 4914269 = 1842851) (by norm_num)
theorem B3276179 : Blo 2183435 3276179 := bstep (se 1 (by rfl) ⟨2457134, by rfl⟩ : syracuseStep 3276179 = 4914269) B4914269
theorem B2184119 : Blo 2183435 2184119 := bstep (se 1 (by rfl) ⟨1638089, by rfl⟩ : syracuseStep 2184119 = 3276179) B3276179
theorem B3685709 : Blo 2183435 3685709 := bbase (se 3 (by rfl) ⟨691070, by rfl⟩ : syracuseStep 3685709 = 1382141) (by norm_num)
theorem B2457139 : Blo 2183435 2457139 := bstep (se 1 (by rfl) ⟨1842854, by rfl⟩ : syracuseStep 2457139 = 3685709) B3685709
theorem B3276185 : Blo 2183435 3276185 := bstep (se 2 (by rfl) ⟨1228569, by rfl⟩ : syracuseStep 3276185 = 2457139) B2457139
theorem B2184123 : Blo 2183435 2184123 := bstep (se 1 (by rfl) ⟨1638092, by rfl⟩ : syracuseStep 2184123 = 3276185) B3276185
theorem B2244133 : Blo 2183435 2244133 := bbase (se 4 (by rfl) ⟨210387, by rfl⟩ : syracuseStep 2244133 = 420775) (by norm_num)
theorem B2992177 : Blo 2183435 2992177 := bstep (se 2 (by rfl) ⟨1122066, by rfl⟩ : syracuseStep 2992177 = 2244133) B2244133
theorem B3989569 : Blo 2183435 3989569 := bstep (se 2 (by rfl) ⟨1496088, by rfl⟩ : syracuseStep 3989569 = 2992177) B2992177
theorem B5319425 : Blo 2183435 5319425 := bstep (se 2 (by rfl) ⟨1994784, by rfl⟩ : syracuseStep 5319425 = 3989569) B3989569
theorem B14185133 : Blo 2183435 14185133 := bstep (se 3 (by rfl) ⟨2659712, by rfl⟩ : syracuseStep 14185133 = 5319425) B5319425
theorem B9456755 : Blo 2183435 9456755 := bstep (se 1 (by rfl) ⟨7092566, by rfl⟩ : syracuseStep 9456755 = 14185133) B14185133
theorem B25218013 : Blo 2183435 25218013 := bstep (se 3 (by rfl) ⟨4728377, by rfl⟩ : syracuseStep 25218013 = 9456755) B9456755
theorem B33624017 : Blo 2183435 33624017 := bstep (se 2 (by rfl) ⟨12609006, by rfl⟩ : syracuseStep 33624017 = 25218013) B25218013
theorem B22416011 : Blo 2183435 22416011 := bstep (se 1 (by rfl) ⟨16812008, by rfl⟩ : syracuseStep 22416011 = 33624017) B33624017
theorem B14944007 : Blo 2183435 14944007 := bstep (se 1 (by rfl) ⟨11208005, by rfl⟩ : syracuseStep 14944007 = 22416011) B22416011
theorem B9962671 : Blo 2183435 9962671 := bstep (se 1 (by rfl) ⟨7472003, by rfl⟩ : syracuseStep 9962671 = 14944007) B14944007
theorem B13283561 : Blo 2183435 13283561 := bstep (se 2 (by rfl) ⟨4981335, by rfl⟩ : syracuseStep 13283561 = 9962671) B9962671
theorem B35422829 : Blo 2183435 35422829 := bstep (se 3 (by rfl) ⟨6641780, by rfl⟩ : syracuseStep 35422829 = 13283561) B13283561
theorem B23615219 : Blo 2183435 23615219 := bstep (se 1 (by rfl) ⟨17711414, by rfl⟩ : syracuseStep 23615219 = 35422829) B35422829
theorem B15743479 : Blo 2183435 15743479 := bstep (se 1 (by rfl) ⟨11807609, by rfl⟩ : syracuseStep 15743479 = 23615219) B23615219
theorem B20991305 : Blo 2183435 20991305 := bstep (se 2 (by rfl) ⟨7871739, by rfl⟩ : syracuseStep 20991305 = 15743479) B15743479
theorem B13994203 : Blo 2183435 13994203 := bstep (se 1 (by rfl) ⟨10495652, by rfl⟩ : syracuseStep 13994203 = 20991305) B20991305
theorem B18658937 : Blo 2183435 18658937 := bstep (se 2 (by rfl) ⟨6997101, by rfl⟩ : syracuseStep 18658937 = 13994203) B13994203
theorem B12439291 : Blo 2183435 12439291 := bstep (se 1 (by rfl) ⟨9329468, by rfl⟩ : syracuseStep 12439291 = 18658937) B18658937
theorem B16585721 : Blo 2183435 16585721 := bstep (se 2 (by rfl) ⟨6219645, by rfl⟩ : syracuseStep 16585721 = 12439291) B12439291
theorem B11057147 : Blo 2183435 11057147 := bstep (se 1 (by rfl) ⟨8292860, by rfl⟩ : syracuseStep 11057147 = 16585721) B16585721
theorem B7371431 : Blo 2183435 7371431 := bstep (se 1 (by rfl) ⟨5528573, by rfl⟩ : syracuseStep 7371431 = 11057147) B11057147
theorem B4914287 : Blo 2183435 4914287 := bstep (se 1 (by rfl) ⟨3685715, by rfl⟩ : syracuseStep 4914287 = 7371431) B7371431
theorem B3276191 : Blo 2183435 3276191 := bstep (se 1 (by rfl) ⟨2457143, by rfl⟩ : syracuseStep 3276191 = 4914287) B4914287
theorem B2184127 : Blo 2183435 2184127 := bstep (se 1 (by rfl) ⟨1638095, by rfl⟩ : syracuseStep 2184127 = 3276191) B3276191
theorem B3276197 : Blo 2183435 3276197 := bbase (se 4 (by rfl) ⟨307143, by rfl⟩ : syracuseStep 3276197 = 614287) (by norm_num)
theorem B2184131 : Blo 2183435 2184131 := bstep (se 1 (by rfl) ⟨1638098, by rfl⟩ : syracuseStep 2184131 = 3276197) B3276197
theorem B2764297 : Blo 2183435 2764297 := bbase (se 2 (by rfl) ⟨1036611, by rfl⟩ : syracuseStep 2764297 = 2073223) (by norm_num)
theorem B3685729 : Blo 2183435 3685729 := bstep (se 2 (by rfl) ⟨1382148, by rfl⟩ : syracuseStep 3685729 = 2764297) B2764297
theorem B4914305 : Blo 2183435 4914305 := bstep (se 2 (by rfl) ⟨1842864, by rfl⟩ : syracuseStep 4914305 = 3685729) B3685729
theorem B3276203 : Blo 2183435 3276203 := bstep (se 1 (by rfl) ⟨2457152, by rfl⟩ : syracuseStep 3276203 = 4914305) B4914305
theorem B2184135 : Blo 2183435 2184135 := bstep (se 1 (by rfl) ⟨1638101, by rfl⟩ : syracuseStep 2184135 = 3276203) B3276203
theorem B2457157 : Blo 2183435 2457157 := bbase (se 4 (by rfl) ⟨230358, by rfl⟩ : syracuseStep 2457157 = 460717) (by norm_num)
theorem B3276209 : Blo 2183435 3276209 := bstep (se 2 (by rfl) ⟨1228578, by rfl⟩ : syracuseStep 3276209 = 2457157) B2457157
theorem B2184139 : Blo 2183435 2184139 := bstep (se 1 (by rfl) ⟨1638104, by rfl⟩ : syracuseStep 2184139 = 3276209) B3276209
theorem B4146461 : Blo 2183435 4146461 := bbase (se 3 (by rfl) ⟨777461, by rfl⟩ : syracuseStep 4146461 = 1554923) (by norm_num)
theorem B2764307 : Blo 2183435 2764307 := bstep (se 1 (by rfl) ⟨2073230, by rfl⟩ : syracuseStep 2764307 = 4146461) B4146461
theorem B7371485 : Blo 2183435 7371485 := bstep (se 3 (by rfl) ⟨1382153, by rfl⟩ : syracuseStep 7371485 = 2764307) B2764307
theorem B4914323 : Blo 2183435 4914323 := bstep (se 1 (by rfl) ⟨3685742, by rfl⟩ : syracuseStep 4914323 = 7371485) B7371485
theorem B3276215 : Blo 2183435 3276215 := bstep (se 1 (by rfl) ⟨2457161, by rfl⟩ : syracuseStep 3276215 = 4914323) B4914323
theorem B2184143 : Blo 2183435 2184143 := bstep (se 1 (by rfl) ⟨1638107, by rfl⟩ : syracuseStep 2184143 = 3276215) B3276215
theorem B3276221 : Blo 2183435 3276221 := bbase (se 3 (by rfl) ⟨614291, by rfl⟩ : syracuseStep 3276221 = 1228583) (by norm_num)
theorem B2184147 : Blo 2183435 2184147 := bstep (se 1 (by rfl) ⟨1638110, by rfl⟩ : syracuseStep 2184147 = 3276221) B3276221
theorem B4914341 : Blo 2183435 4914341 := bbase (se 4 (by rfl) ⟨460719, by rfl⟩ : syracuseStep 4914341 = 921439) (by norm_num)
theorem B3276227 : Blo 2183435 3276227 := bstep (se 1 (by rfl) ⟨2457170, by rfl⟩ : syracuseStep 3276227 = 4914341) B4914341
theorem B2184151 : Blo 2183435 2184151 := bstep (se 1 (by rfl) ⟨1638113, by rfl⟩ : syracuseStep 2184151 = 3276227) B3276227
theorem B5528645 : Blo 2183435 5528645 := bbase (se 4 (by rfl) ⟨518310, by rfl⟩ : syracuseStep 5528645 = 1036621) (by norm_num)
theorem B3685763 : Blo 2183435 3685763 := bstep (se 1 (by rfl) ⟨2764322, by rfl⟩ : syracuseStep 3685763 = 5528645) B5528645
theorem B2457175 : Blo 2183435 2457175 := bstep (se 1 (by rfl) ⟨1842881, by rfl⟩ : syracuseStep 2457175 = 3685763) B3685763
theorem B3276233 : Blo 2183435 3276233 := bstep (se 2 (by rfl) ⟨1228587, by rfl⟩ : syracuseStep 3276233 = 2457175) B2457175
theorem B2184155 : Blo 2183435 2184155 := bstep (se 1 (by rfl) ⟨1638116, by rfl⟩ : syracuseStep 2184155 = 3276233) B3276233
theorem B6997205 : Blo 2183435 6997205 := bbase (se 7 (by rfl) ⟨81998, by rfl⟩ : syracuseStep 6997205 = 163997) (by norm_num)
theorem B4664803 : Blo 2183435 4664803 := bstep (se 1 (by rfl) ⟨3498602, by rfl⟩ : syracuseStep 4664803 = 6997205) B6997205
theorem B6219737 : Blo 2183435 6219737 := bstep (se 2 (by rfl) ⟨2332401, by rfl⟩ : syracuseStep 6219737 = 4664803) B4664803
theorem B4146491 : Blo 2183435 4146491 := bstep (se 1 (by rfl) ⟨3109868, by rfl⟩ : syracuseStep 4146491 = 6219737) B6219737
theorem B11057309 : Blo 2183435 11057309 := bstep (se 3 (by rfl) ⟨2073245, by rfl⟩ : syracuseStep 11057309 = 4146491) B4146491
theorem B7371539 : Blo 2183435 7371539 := bstep (se 1 (by rfl) ⟨5528654, by rfl⟩ : syracuseStep 7371539 = 11057309) B11057309
theorem B4914359 : Blo 2183435 4914359 := bstep (se 1 (by rfl) ⟨3685769, by rfl⟩ : syracuseStep 4914359 = 7371539) B7371539
theorem B3276239 : Blo 2183435 3276239 := bstep (se 1 (by rfl) ⟨2457179, by rfl⟩ : syracuseStep 3276239 = 4914359) B4914359
theorem B2184159 : Blo 2183435 2184159 := bstep (se 1 (by rfl) ⟨1638119, by rfl⟩ : syracuseStep 2184159 = 3276239) B3276239
theorem B3276245 : Blo 2183435 3276245 := bbase (se 7 (by rfl) ⟨38393, by rfl⟩ : syracuseStep 3276245 = 76787) (by norm_num)
theorem B2184163 : Blo 2183435 2184163 := bstep (se 1 (by rfl) ⟨1638122, by rfl⟩ : syracuseStep 2184163 = 3276245) B3276245
theorem B8293013 : Blo 2183435 8293013 := bbase (se 6 (by rfl) ⟨194367, by rfl⟩ : syracuseStep 8293013 = 388735) (by norm_num)
theorem B5528675 : Blo 2183435 5528675 := bstep (se 1 (by rfl) ⟨4146506, by rfl⟩ : syracuseStep 5528675 = 8293013) B8293013
theorem B3685783 : Blo 2183435 3685783 := bstep (se 1 (by rfl) ⟨2764337, by rfl⟩ : syracuseStep 3685783 = 5528675) B5528675
theorem B4914377 : Blo 2183435 4914377 := bstep (se 2 (by rfl) ⟨1842891, by rfl⟩ : syracuseStep 4914377 = 3685783) B3685783
theorem B3276251 : Blo 2183435 3276251 := bstep (se 1 (by rfl) ⟨2457188, by rfl⟩ : syracuseStep 3276251 = 4914377) B4914377
theorem B2184167 : Blo 2183435 2184167 := bstep (se 1 (by rfl) ⟨1638125, by rfl⟩ : syracuseStep 2184167 = 3276251) B3276251
theorem B2457193 : Blo 2183435 2457193 := bbase (se 2 (by rfl) ⟨921447, by rfl⟩ : syracuseStep 2457193 = 1842895) (by norm_num)
theorem B3276257 : Blo 2183435 3276257 := bstep (se 2 (by rfl) ⟨1228596, by rfl⟩ : syracuseStep 3276257 = 2457193) B2457193
theorem B2184171 : Blo 2183435 2184171 := bstep (se 1 (by rfl) ⟨1638128, by rfl⟩ : syracuseStep 2184171 = 3276257) B3276257
theorem B4664837 : Blo 2183435 4664837 := bbase (se 4 (by rfl) ⟨437328, by rfl⟩ : syracuseStep 4664837 = 874657) (by norm_num)
theorem B12439565 : Blo 2183435 12439565 := bstep (se 3 (by rfl) ⟨2332418, by rfl⟩ : syracuseStep 12439565 = 4664837) B4664837
theorem B8293043 : Blo 2183435 8293043 := bstep (se 1 (by rfl) ⟨6219782, by rfl⟩ : syracuseStep 8293043 = 12439565) B12439565
theorem B5528695 : Blo 2183435 5528695 := bstep (se 1 (by rfl) ⟨4146521, by rfl⟩ : syracuseStep 5528695 = 8293043) B8293043
theorem B7371593 : Blo 2183435 7371593 := bstep (se 2 (by rfl) ⟨2764347, by rfl⟩ : syracuseStep 7371593 = 5528695) B5528695
theorem B4914395 : Blo 2183435 4914395 := bstep (se 1 (by rfl) ⟨3685796, by rfl⟩ : syracuseStep 4914395 = 7371593) B7371593
theorem B3276263 : Blo 2183435 3276263 := bstep (se 1 (by rfl) ⟨2457197, by rfl⟩ : syracuseStep 3276263 = 4914395) B4914395
theorem B2184175 : Blo 2183435 2184175 := bstep (se 1 (by rfl) ⟨1638131, by rfl⟩ : syracuseStep 2184175 = 3276263) B3276263
theorem B3276269 : Blo 2183435 3276269 := bbase (se 3 (by rfl) ⟨614300, by rfl⟩ : syracuseStep 3276269 = 1228601) (by norm_num)
theorem B2184179 : Blo 2183435 2184179 := bstep (se 1 (by rfl) ⟨1638134, by rfl⟩ : syracuseStep 2184179 = 3276269) B3276269
theorem B4914413 : Blo 2183435 4914413 := bbase (se 3 (by rfl) ⟨921452, by rfl⟩ : syracuseStep 4914413 = 1842905) (by norm_num)
theorem B3276275 : Blo 2183435 3276275 := bstep (se 1 (by rfl) ⟨2457206, by rfl⟩ : syracuseStep 3276275 = 4914413) B4914413
theorem B2184183 : Blo 2183435 2184183 := bstep (se 1 (by rfl) ⟨1638137, by rfl⟩ : syracuseStep 2184183 = 3276275) B3276275
theorem B3109909 : Blo 2183435 3109909 := bbase (se 6 (by rfl) ⟨72888, by rfl⟩ : syracuseStep 3109909 = 145777) (by norm_num)
theorem B4146545 : Blo 2183435 4146545 := bstep (se 2 (by rfl) ⟨1554954, by rfl⟩ : syracuseStep 4146545 = 3109909) B3109909
theorem B2764363 : Blo 2183435 2764363 := bstep (se 1 (by rfl) ⟨2073272, by rfl⟩ : syracuseStep 2764363 = 4146545) B4146545
theorem B3685817 : Blo 2183435 3685817 := bstep (se 2 (by rfl) ⟨1382181, by rfl⟩ : syracuseStep 3685817 = 2764363) B2764363
theorem B2457211 : Blo 2183435 2457211 := bstep (se 1 (by rfl) ⟨1842908, by rfl⟩ : syracuseStep 2457211 = 3685817) B3685817
theorem B3276281 : Blo 2183435 3276281 := bstep (se 2 (by rfl) ⟨1228605, by rfl⟩ : syracuseStep 3276281 = 2457211) B2457211
theorem B2184187 : Blo 2183435 2184187 := bstep (se 1 (by rfl) ⟨1638140, by rfl⟩ : syracuseStep 2184187 = 3276281) B3276281
theorem B17953589 : Blo 2183435 17953589 := bbase (se 5 (by rfl) ⟨841574, by rfl⟩ : syracuseStep 17953589 = 1683149) (by norm_num)
theorem B11969059 : Blo 2183435 11969059 := bstep (se 1 (by rfl) ⟨8976794, by rfl⟩ : syracuseStep 11969059 = 17953589) B17953589
theorem B15958745 : Blo 2183435 15958745 := bstep (se 2 (by rfl) ⟨5984529, by rfl⟩ : syracuseStep 15958745 = 11969059) B11969059
theorem B10639163 : Blo 2183435 10639163 := bstep (se 1 (by rfl) ⟨7979372, by rfl⟩ : syracuseStep 10639163 = 15958745) B15958745
theorem B7092775 : Blo 2183435 7092775 := bstep (se 1 (by rfl) ⟨5319581, by rfl⟩ : syracuseStep 7092775 = 10639163) B10639163
theorem B9457033 : Blo 2183435 9457033 := bstep (se 2 (by rfl) ⟨3546387, by rfl⟩ : syracuseStep 9457033 = 7092775) B7092775
theorem B12609377 : Blo 2183435 12609377 := bstep (se 2 (by rfl) ⟨4728516, by rfl⟩ : syracuseStep 12609377 = 9457033) B9457033
theorem B8406251 : Blo 2183435 8406251 := bstep (se 1 (by rfl) ⟨6304688, by rfl⟩ : syracuseStep 8406251 = 12609377) B12609377
theorem B5604167 : Blo 2183435 5604167 := bstep (se 1 (by rfl) ⟨4203125, by rfl⟩ : syracuseStep 5604167 = 8406251) B8406251
theorem B3736111 : Blo 2183435 3736111 := bstep (se 1 (by rfl) ⟨2802083, by rfl⟩ : syracuseStep 3736111 = 5604167) B5604167
theorem B4981481 : Blo 2183435 4981481 := bstep (se 2 (by rfl) ⟨1868055, by rfl⟩ : syracuseStep 4981481 = 3736111) B3736111
theorem B53135797 : Blo 2183435 53135797 := bstep (se 5 (by rfl) ⟨2490740, by rfl⟩ : syracuseStep 53135797 = 4981481) B4981481
theorem B70847729 : Blo 2183435 70847729 := bstep (se 2 (by rfl) ⟨26567898, by rfl⟩ : syracuseStep 70847729 = 53135797) B53135797
theorem B47231819 : Blo 2183435 47231819 := bstep (se 1 (by rfl) ⟨35423864, by rfl⟩ : syracuseStep 47231819 = 70847729) B70847729
theorem B31487879 : Blo 2183435 31487879 := bstep (se 1 (by rfl) ⟨23615909, by rfl⟩ : syracuseStep 31487879 = 47231819) B47231819
theorem B83967677 : Blo 2183435 83967677 := bstep (se 3 (by rfl) ⟨15743939, by rfl⟩ : syracuseStep 83967677 = 31487879) B31487879
theorem B55978451 : Blo 2183435 55978451 := bstep (se 1 (by rfl) ⟨41983838, by rfl⟩ : syracuseStep 55978451 = 83967677) B83967677
theorem B37318967 : Blo 2183435 37318967 := bstep (se 1 (by rfl) ⟨27989225, by rfl⟩ : syracuseStep 37318967 = 55978451) B55978451
theorem B24879311 : Blo 2183435 24879311 := bstep (se 1 (by rfl) ⟨18659483, by rfl⟩ : syracuseStep 24879311 = 37318967) B37318967
theorem B16586207 : Blo 2183435 16586207 := bstep (se 1 (by rfl) ⟨12439655, by rfl⟩ : syracuseStep 16586207 = 24879311) B24879311
theorem B11057471 : Blo 2183435 11057471 := bstep (se 1 (by rfl) ⟨8293103, by rfl⟩ : syracuseStep 11057471 = 16586207) B16586207
theorem B7371647 : Blo 2183435 7371647 := bstep (se 1 (by rfl) ⟨5528735, by rfl⟩ : syracuseStep 7371647 = 11057471) B11057471
theorem B4914431 : Blo 2183435 4914431 := bstep (se 1 (by rfl) ⟨3685823, by rfl⟩ : syracuseStep 4914431 = 7371647) B7371647
theorem B3276287 : Blo 2183435 3276287 := bstep (se 1 (by rfl) ⟨2457215, by rfl⟩ : syracuseStep 3276287 = 4914431) B4914431
theorem B2184191 : Blo 2183435 2184191 := bstep (se 1 (by rfl) ⟨1638143, by rfl⟩ : syracuseStep 2184191 = 3276287) B3276287
theorem B3276293 : Blo 2183435 3276293 := bbase (se 4 (by rfl) ⟨307152, by rfl⟩ : syracuseStep 3276293 = 614305) (by norm_num)
theorem B2184195 : Blo 2183435 2184195 := bstep (se 1 (by rfl) ⟨1638146, by rfl⟩ : syracuseStep 2184195 = 3276293) B3276293
theorem B3685837 : Blo 2183435 3685837 := bbase (se 3 (by rfl) ⟨691094, by rfl⟩ : syracuseStep 3685837 = 1382189) (by norm_num)
theorem B4914449 : Blo 2183435 4914449 := bstep (se 2 (by rfl) ⟨1842918, by rfl⟩ : syracuseStep 4914449 = 3685837) B3685837
theorem B3276299 : Blo 2183435 3276299 := bstep (se 1 (by rfl) ⟨2457224, by rfl⟩ : syracuseStep 3276299 = 4914449) B4914449
theorem B2184199 : Blo 2183435 2184199 := bstep (se 1 (by rfl) ⟨1638149, by rfl⟩ : syracuseStep 2184199 = 3276299) B3276299
theorem B2457229 : Blo 2183435 2457229 := bbase (se 3 (by rfl) ⟨460730, by rfl⟩ : syracuseStep 2457229 = 921461) (by norm_num)
theorem B3276305 : Blo 2183435 3276305 := bstep (se 2 (by rfl) ⟨1228614, by rfl⟩ : syracuseStep 3276305 = 2457229) B2457229
theorem B2184203 : Blo 2183435 2184203 := bstep (se 1 (by rfl) ⟨1638152, by rfl⟩ : syracuseStep 2184203 = 3276305) B3276305
theorem B7371701 : Blo 2183435 7371701 := bbase (se 5 (by rfl) ⟨345548, by rfl⟩ : syracuseStep 7371701 = 691097) (by norm_num)
theorem B4914467 : Blo 2183435 4914467 := bstep (se 1 (by rfl) ⟨3685850, by rfl⟩ : syracuseStep 4914467 = 7371701) B7371701
theorem B3276311 : Blo 2183435 3276311 := bstep (se 1 (by rfl) ⟨2457233, by rfl⟩ : syracuseStep 3276311 = 4914467) B4914467
theorem B2184207 : Blo 2183435 2184207 := bstep (se 1 (by rfl) ⟨1638155, by rfl⟩ : syracuseStep 2184207 = 3276311) B3276311
theorem B3276317 : Blo 2183435 3276317 := bbase (se 3 (by rfl) ⟨614309, by rfl⟩ : syracuseStep 3276317 = 1228619) (by norm_num)
theorem B2184211 : Blo 2183435 2184211 := bstep (se 1 (by rfl) ⟨1638158, by rfl⟩ : syracuseStep 2184211 = 3276317) B3276317
theorem B4914485 : Blo 2183435 4914485 := bbase (se 5 (by rfl) ⟨230366, by rfl⟩ : syracuseStep 4914485 = 460733) (by norm_num)
theorem B3276323 : Blo 2183435 3276323 := bstep (se 1 (by rfl) ⟨2457242, by rfl⟩ : syracuseStep 3276323 = 4914485) B4914485
theorem B2184215 : Blo 2183435 2184215 := bstep (se 1 (by rfl) ⟨1638161, by rfl⟩ : syracuseStep 2184215 = 3276323) B3276323
theorem B4203181 : Blo 2183435 4203181 := bbase (se 3 (by rfl) ⟨788096, by rfl⟩ : syracuseStep 4203181 = 1576193) (by norm_num)
theorem B5604241 : Blo 2183435 5604241 := bstep (se 2 (by rfl) ⟨2101590, by rfl⟩ : syracuseStep 5604241 = 4203181) B4203181
theorem B7472321 : Blo 2183435 7472321 := bstep (se 2 (by rfl) ⟨2802120, by rfl⟩ : syracuseStep 7472321 = 5604241) B5604241
theorem B4981547 : Blo 2183435 4981547 := bstep (se 1 (by rfl) ⟨3736160, by rfl⟩ : syracuseStep 4981547 = 7472321) B7472321
theorem B3321031 : Blo 2183435 3321031 := bstep (se 1 (by rfl) ⟨2490773, by rfl⟩ : syracuseStep 3321031 = 4981547) B4981547
theorem B4428041 : Blo 2183435 4428041 := bstep (se 2 (by rfl) ⟨1660515, by rfl⟩ : syracuseStep 4428041 = 3321031) B3321031
theorem B11808109 : Blo 2183435 11808109 := bstep (se 3 (by rfl) ⟨2214020, by rfl⟩ : syracuseStep 11808109 = 4428041) B4428041
theorem B15744145 : Blo 2183435 15744145 := bstep (se 2 (by rfl) ⟨5904054, by rfl⟩ : syracuseStep 15744145 = 11808109) B11808109
theorem B20992193 : Blo 2183435 20992193 := bstep (se 2 (by rfl) ⟨7872072, by rfl⟩ : syracuseStep 20992193 = 15744145) B15744145
theorem B13994795 : Blo 2183435 13994795 := bstep (se 1 (by rfl) ⟨10496096, by rfl⟩ : syracuseStep 13994795 = 20992193) B20992193
theorem B9329863 : Blo 2183435 9329863 := bstep (se 1 (by rfl) ⟨6997397, by rfl⟩ : syracuseStep 9329863 = 13994795) B13994795
theorem B12439817 : Blo 2183435 12439817 := bstep (se 2 (by rfl) ⟨4664931, by rfl⟩ : syracuseStep 12439817 = 9329863) B9329863
theorem B8293211 : Blo 2183435 8293211 := bstep (se 1 (by rfl) ⟨6219908, by rfl⟩ : syracuseStep 8293211 = 12439817) B12439817
theorem B5528807 : Blo 2183435 5528807 := bstep (se 1 (by rfl) ⟨4146605, by rfl⟩ : syracuseStep 5528807 = 8293211) B8293211
theorem B3685871 : Blo 2183435 3685871 := bstep (se 1 (by rfl) ⟨2764403, by rfl⟩ : syracuseStep 3685871 = 5528807) B5528807
theorem B2457247 : Blo 2183435 2457247 := bstep (se 1 (by rfl) ⟨1842935, by rfl⟩ : syracuseStep 2457247 = 3685871) B3685871
theorem B3276329 : Blo 2183435 3276329 := bstep (se 2 (by rfl) ⟨1228623, by rfl⟩ : syracuseStep 3276329 = 2457247) B2457247
theorem B2184219 : Blo 2183435 2184219 := bstep (se 1 (by rfl) ⟨1638164, by rfl⟩ : syracuseStep 2184219 = 3276329) B3276329
theorem B3321037 : Blo 2183435 3321037 := bbase (se 3 (by rfl) ⟨622694, by rfl⟩ : syracuseStep 3321037 = 1245389) (by norm_num)
theorem B4428049 : Blo 2183435 4428049 := bstep (se 2 (by rfl) ⟨1660518, by rfl⟩ : syracuseStep 4428049 = 3321037) B3321037
theorem B5904065 : Blo 2183435 5904065 := bstep (se 2 (by rfl) ⟨2214024, by rfl⟩ : syracuseStep 5904065 = 4428049) B4428049
theorem B3936043 : Blo 2183435 3936043 := bstep (se 1 (by rfl) ⟨2952032, by rfl⟩ : syracuseStep 3936043 = 5904065) B5904065
theorem B20992229 : Blo 2183435 20992229 := bstep (se 4 (by rfl) ⟨1968021, by rfl⟩ : syracuseStep 20992229 = 3936043) B3936043
theorem B13994819 : Blo 2183435 13994819 := bstep (se 1 (by rfl) ⟨10496114, by rfl⟩ : syracuseStep 13994819 = 20992229) B20992229
theorem B9329879 : Blo 2183435 9329879 := bstep (se 1 (by rfl) ⟨6997409, by rfl⟩ : syracuseStep 9329879 = 13994819) B13994819
theorem B6219919 : Blo 2183435 6219919 := bstep (se 1 (by rfl) ⟨4664939, by rfl⟩ : syracuseStep 6219919 = 9329879) B9329879
theorem B8293225 : Blo 2183435 8293225 := bstep (se 2 (by rfl) ⟨3109959, by rfl⟩ : syracuseStep 8293225 = 6219919) B6219919
theorem B11057633 : Blo 2183435 11057633 := bstep (se 2 (by rfl) ⟨4146612, by rfl⟩ : syracuseStep 11057633 = 8293225) B8293225
theorem B7371755 : Blo 2183435 7371755 := bstep (se 1 (by rfl) ⟨5528816, by rfl⟩ : syracuseStep 7371755 = 11057633) B11057633
theorem B4914503 : Blo 2183435 4914503 := bstep (se 1 (by rfl) ⟨3685877, by rfl⟩ : syracuseStep 4914503 = 7371755) B7371755
theorem B3276335 : Blo 2183435 3276335 := bstep (se 1 (by rfl) ⟨2457251, by rfl⟩ : syracuseStep 3276335 = 4914503) B4914503
theorem B2184223 : Blo 2183435 2184223 := bstep (se 1 (by rfl) ⟨1638167, by rfl⟩ : syracuseStep 2184223 = 3276335) B3276335
theorem B3276341 : Blo 2183435 3276341 := bbase (se 5 (by rfl) ⟨153578, by rfl⟩ : syracuseStep 3276341 = 307157) (by norm_num)
theorem B2184227 : Blo 2183435 2184227 := bstep (se 1 (by rfl) ⟨1638170, by rfl⟩ : syracuseStep 2184227 = 3276341) B3276341
theorem B5528837 : Blo 2183435 5528837 := bbase (se 4 (by rfl) ⟨518328, by rfl⟩ : syracuseStep 5528837 = 1036657) (by norm_num)
theorem B3685891 : Blo 2183435 3685891 := bstep (se 1 (by rfl) ⟨2764418, by rfl⟩ : syracuseStep 3685891 = 5528837) B5528837
theorem B4914521 : Blo 2183435 4914521 := bstep (se 2 (by rfl) ⟨1842945, by rfl⟩ : syracuseStep 4914521 = 3685891) B3685891
theorem B3276347 : Blo 2183435 3276347 := bstep (se 1 (by rfl) ⟨2457260, by rfl⟩ : syracuseStep 3276347 = 4914521) B4914521
theorem B2184231 : Blo 2183435 2184231 := bstep (se 1 (by rfl) ⟨1638173, by rfl⟩ : syracuseStep 2184231 = 3276347) B3276347
theorem B2457265 : Blo 2183435 2457265 := bbase (se 2 (by rfl) ⟨921474, by rfl⟩ : syracuseStep 2457265 = 1842949) (by norm_num)
theorem B3276353 : Blo 2183435 3276353 := bstep (se 2 (by rfl) ⟨1228632, by rfl⟩ : syracuseStep 3276353 = 2457265) B2457265
theorem B2184235 : Blo 2183435 2184235 := bstep (se 1 (by rfl) ⟨1638176, by rfl⟩ : syracuseStep 2184235 = 3276353) B3276353
theorem B2490797 : Blo 2183435 2490797 := bbase (se 3 (by rfl) ⟨467024, by rfl⟩ : syracuseStep 2490797 = 934049) (by norm_num)
theorem B6642125 : Blo 2183435 6642125 := bstep (se 3 (by rfl) ⟨1245398, by rfl⟩ : syracuseStep 6642125 = 2490797) B2490797
theorem B4428083 : Blo 2183435 4428083 := bstep (se 1 (by rfl) ⟨3321062, by rfl⟩ : syracuseStep 4428083 = 6642125) B6642125
theorem B2952055 : Blo 2183435 2952055 := bstep (se 1 (by rfl) ⟨2214041, by rfl⟩ : syracuseStep 2952055 = 4428083) B4428083
theorem B3936073 : Blo 2183435 3936073 := bstep (se 2 (by rfl) ⟨1476027, by rfl⟩ : syracuseStep 3936073 = 2952055) B2952055
theorem B5248097 : Blo 2183435 5248097 := bstep (se 2 (by rfl) ⟨1968036, by rfl⟩ : syracuseStep 5248097 = 3936073) B3936073
theorem B3498731 : Blo 2183435 3498731 := bstep (se 1 (by rfl) ⟨2624048, by rfl⟩ : syracuseStep 3498731 = 5248097) B5248097
theorem B2332487 : Blo 2183435 2332487 := bstep (se 1 (by rfl) ⟨1749365, by rfl⟩ : syracuseStep 2332487 = 3498731) B3498731
theorem B6219965 : Blo 2183435 6219965 := bstep (se 3 (by rfl) ⟨1166243, by rfl⟩ : syracuseStep 6219965 = 2332487) B2332487
theorem B4146643 : Blo 2183435 4146643 := bstep (se 1 (by rfl) ⟨3109982, by rfl⟩ : syracuseStep 4146643 = 6219965) B6219965
theorem B5528857 : Blo 2183435 5528857 := bstep (se 2 (by rfl) ⟨2073321, by rfl⟩ : syracuseStep 5528857 = 4146643) B4146643
theorem B7371809 : Blo 2183435 7371809 := bstep (se 2 (by rfl) ⟨2764428, by rfl⟩ : syracuseStep 7371809 = 5528857) B5528857
theorem B4914539 : Blo 2183435 4914539 := bstep (se 1 (by rfl) ⟨3685904, by rfl⟩ : syracuseStep 4914539 = 7371809) B7371809
theorem B3276359 : Blo 2183435 3276359 := bstep (se 1 (by rfl) ⟨2457269, by rfl⟩ : syracuseStep 3276359 = 4914539) B4914539
theorem B2184239 : Blo 2183435 2184239 := bstep (se 1 (by rfl) ⟨1638179, by rfl⟩ : syracuseStep 2184239 = 3276359) B3276359
theorem B3276365 : Blo 2183435 3276365 := bbase (se 3 (by rfl) ⟨614318, by rfl⟩ : syracuseStep 3276365 = 1228637) (by norm_num)
theorem B2184243 : Blo 2183435 2184243 := bstep (se 1 (by rfl) ⟨1638182, by rfl⟩ : syracuseStep 2184243 = 3276365) B3276365
theorem B4914557 : Blo 2183435 4914557 := bbase (se 3 (by rfl) ⟨921479, by rfl⟩ : syracuseStep 4914557 = 1842959) (by norm_num)
theorem B3276371 : Blo 2183435 3276371 := bstep (se 1 (by rfl) ⟨2457278, by rfl⟩ : syracuseStep 3276371 = 4914557) B4914557
theorem B2184247 : Blo 2183435 2184247 := bstep (se 1 (by rfl) ⟨1638185, by rfl⟩ : syracuseStep 2184247 = 3276371) B3276371
theorem B3685925 : Blo 2183435 3685925 := bbase (se 4 (by rfl) ⟨345555, by rfl⟩ : syracuseStep 3685925 = 691111) (by norm_num)
theorem B2457283 : Blo 2183435 2457283 := bstep (se 1 (by rfl) ⟨1842962, by rfl⟩ : syracuseStep 2457283 = 3685925) B3685925
theorem B3276377 : Blo 2183435 3276377 := bstep (se 2 (by rfl) ⟨1228641, by rfl⟩ : syracuseStep 3276377 = 2457283) B2457283
theorem B2184251 : Blo 2183435 2184251 := bstep (se 1 (by rfl) ⟨1638188, by rfl⟩ : syracuseStep 2184251 = 3276377) B3276377
theorem B3110005 : Blo 2183435 3110005 := bbase (se 5 (by rfl) ⟨145781, by rfl⟩ : syracuseStep 3110005 = 291563) (by norm_num)
theorem B16586693 : Blo 2183435 16586693 := bstep (se 4 (by rfl) ⟨1555002, by rfl⟩ : syracuseStep 16586693 = 3110005) B3110005
theorem B11057795 : Blo 2183435 11057795 := bstep (se 1 (by rfl) ⟨8293346, by rfl⟩ : syracuseStep 11057795 = 16586693) B16586693
theorem B7371863 : Blo 2183435 7371863 := bstep (se 1 (by rfl) ⟨5528897, by rfl⟩ : syracuseStep 7371863 = 11057795) B11057795
theorem B4914575 : Blo 2183435 4914575 := bstep (se 1 (by rfl) ⟨3685931, by rfl⟩ : syracuseStep 4914575 = 7371863) B7371863
theorem B3276383 : Blo 2183435 3276383 := bstep (se 1 (by rfl) ⟨2457287, by rfl⟩ : syracuseStep 3276383 = 4914575) B4914575
theorem B2184255 : Blo 2183435 2184255 := bstep (se 1 (by rfl) ⟨1638191, by rfl⟩ : syracuseStep 2184255 = 3276383) B3276383
theorem B3276389 : Blo 2183435 3276389 := bbase (se 4 (by rfl) ⟨307161, by rfl⟩ : syracuseStep 3276389 = 614323) (by norm_num)
theorem B2184259 : Blo 2183435 2184259 := bstep (se 1 (by rfl) ⟨1638194, by rfl⟩ : syracuseStep 2184259 = 3276389) B3276389
theorem B2332513 : Blo 2183435 2332513 := bbase (se 2 (by rfl) ⟨874692, by rfl⟩ : syracuseStep 2332513 = 1749385) (by norm_num)
theorem B3110017 : Blo 2183435 3110017 := bstep (se 2 (by rfl) ⟨1166256, by rfl⟩ : syracuseStep 3110017 = 2332513) B2332513
theorem B4146689 : Blo 2183435 4146689 := bstep (se 2 (by rfl) ⟨1555008, by rfl⟩ : syracuseStep 4146689 = 3110017) B3110017
theorem B2764459 : Blo 2183435 2764459 := bstep (se 1 (by rfl) ⟨2073344, by rfl⟩ : syracuseStep 2764459 = 4146689) B4146689
theorem B3685945 : Blo 2183435 3685945 := bstep (se 2 (by rfl) ⟨1382229, by rfl⟩ : syracuseStep 3685945 = 2764459) B2764459
theorem B4914593 : Blo 2183435 4914593 := bstep (se 2 (by rfl) ⟨1842972, by rfl⟩ : syracuseStep 4914593 = 3685945) B3685945
theorem B3276395 : Blo 2183435 3276395 := bstep (se 1 (by rfl) ⟨2457296, by rfl⟩ : syracuseStep 3276395 = 4914593) B4914593
theorem B2184263 : Blo 2183435 2184263 := bstep (se 1 (by rfl) ⟨1638197, by rfl⟩ : syracuseStep 2184263 = 3276395) B3276395
theorem B2457301 : Blo 2183435 2457301 := bbase (se 7 (by rfl) ⟨28796, by rfl⟩ : syracuseStep 2457301 = 57593) (by norm_num)
theorem B3276401 : Blo 2183435 3276401 := bstep (se 2 (by rfl) ⟨1228650, by rfl⟩ : syracuseStep 3276401 = 2457301) B2457301
theorem B2184267 : Blo 2183435 2184267 := bstep (se 1 (by rfl) ⟨1638200, by rfl⟩ : syracuseStep 2184267 = 3276401) B3276401
theorem B2764469 : Blo 2183435 2764469 := bbase (se 5 (by rfl) ⟨129584, by rfl⟩ : syracuseStep 2764469 = 259169) (by norm_num)
theorem B7371917 : Blo 2183435 7371917 := bstep (se 3 (by rfl) ⟨1382234, by rfl⟩ : syracuseStep 7371917 = 2764469) B2764469
theorem B4914611 : Blo 2183435 4914611 := bstep (se 1 (by rfl) ⟨3685958, by rfl⟩ : syracuseStep 4914611 = 7371917) B7371917
theorem B3276407 : Blo 2183435 3276407 := bstep (se 1 (by rfl) ⟨2457305, by rfl⟩ : syracuseStep 3276407 = 4914611) B4914611
theorem B2184271 : Blo 2183435 2184271 := bstep (se 1 (by rfl) ⟨1638203, by rfl⟩ : syracuseStep 2184271 = 3276407) B3276407
theorem B3276413 : Blo 2183435 3276413 := bbase (se 3 (by rfl) ⟨614327, by rfl⟩ : syracuseStep 3276413 = 1228655) (by norm_num)
theorem B2184275 : Blo 2183435 2184275 := bstep (se 1 (by rfl) ⟨1638206, by rfl⟩ : syracuseStep 2184275 = 3276413) B3276413
theorem B4914629 : Blo 2183435 4914629 := bbase (se 4 (by rfl) ⟨460746, by rfl⟩ : syracuseStep 4914629 = 921493) (by norm_num)
theorem B3276419 : Blo 2183435 3276419 := bstep (se 1 (by rfl) ⟨2457314, by rfl⟩ : syracuseStep 3276419 = 4914629) B4914629
theorem B2184279 : Blo 2183435 2184279 := bstep (se 1 (by rfl) ⟨1638209, by rfl⟩ : syracuseStep 2184279 = 3276419) B3276419
theorem B10496405 : Blo 2183435 10496405 := bbase (se 6 (by rfl) ⟨246009, by rfl⟩ : syracuseStep 10496405 = 492019) (by norm_num)
theorem B6997603 : Blo 2183435 6997603 := bstep (se 1 (by rfl) ⟨5248202, by rfl⟩ : syracuseStep 6997603 = 10496405) B10496405
theorem B9330137 : Blo 2183435 9330137 := bstep (se 2 (by rfl) ⟨3498801, by rfl⟩ : syracuseStep 9330137 = 6997603) B6997603
theorem B6220091 : Blo 2183435 6220091 := bstep (se 1 (by rfl) ⟨4665068, by rfl⟩ : syracuseStep 6220091 = 9330137) B9330137
theorem B4146727 : Blo 2183435 4146727 := bstep (se 1 (by rfl) ⟨3110045, by rfl⟩ : syracuseStep 4146727 = 6220091) B6220091
theorem B5528969 : Blo 2183435 5528969 := bstep (se 2 (by rfl) ⟨2073363, by rfl⟩ : syracuseStep 5528969 = 4146727) B4146727
theorem B3685979 : Blo 2183435 3685979 := bstep (se 1 (by rfl) ⟨2764484, by rfl⟩ : syracuseStep 3685979 = 5528969) B5528969
theorem B2457319 : Blo 2183435 2457319 := bstep (se 1 (by rfl) ⟨1842989, by rfl⟩ : syracuseStep 2457319 = 3685979) B3685979
theorem B3276425 : Blo 2183435 3276425 := bstep (se 2 (by rfl) ⟨1228659, by rfl⟩ : syracuseStep 3276425 = 2457319) B2457319
theorem B2184283 : Blo 2183435 2184283 := bstep (se 1 (by rfl) ⟨1638212, by rfl⟩ : syracuseStep 2184283 = 3276425) B3276425
theorem B11057957 : Blo 2183435 11057957 := bbase (se 4 (by rfl) ⟨1036683, by rfl⟩ : syracuseStep 11057957 = 2073367) (by norm_num)
theorem B7371971 : Blo 2183435 7371971 := bstep (se 1 (by rfl) ⟨5528978, by rfl⟩ : syracuseStep 7371971 = 11057957) B11057957
theorem B4914647 : Blo 2183435 4914647 := bstep (se 1 (by rfl) ⟨3685985, by rfl⟩ : syracuseStep 4914647 = 7371971) B7371971
theorem B3276431 : Blo 2183435 3276431 := bstep (se 1 (by rfl) ⟨2457323, by rfl⟩ : syracuseStep 3276431 = 4914647) B4914647
theorem B2184287 : Blo 2183435 2184287 := bstep (se 1 (by rfl) ⟨1638215, by rfl⟩ : syracuseStep 2184287 = 3276431) B3276431
theorem B3276437 : Blo 2183435 3276437 := bbase (se 6 (by rfl) ⟨76791, by rfl⟩ : syracuseStep 3276437 = 153583) (by norm_num)
theorem B2184291 : Blo 2183435 2184291 := bstep (se 1 (by rfl) ⟨1638218, by rfl⟩ : syracuseStep 2184291 = 3276437) B3276437
theorem B3936173 : Blo 2183435 3936173 := bbase (se 3 (by rfl) ⟨738032, by rfl⟩ : syracuseStep 3936173 = 1476065) (by norm_num)
theorem B10496461 : Blo 2183435 10496461 := bstep (se 3 (by rfl) ⟨1968086, by rfl⟩ : syracuseStep 10496461 = 3936173) B3936173
theorem B13995281 : Blo 2183435 13995281 := bstep (se 2 (by rfl) ⟨5248230, by rfl⟩ : syracuseStep 13995281 = 10496461) B10496461
theorem B9330187 : Blo 2183435 9330187 := bstep (se 1 (by rfl) ⟨6997640, by rfl⟩ : syracuseStep 9330187 = 13995281) B13995281
theorem B12440249 : Blo 2183435 12440249 := bstep (se 2 (by rfl) ⟨4665093, by rfl⟩ : syracuseStep 12440249 = 9330187) B9330187
theorem B8293499 : Blo 2183435 8293499 := bstep (se 1 (by rfl) ⟨6220124, by rfl⟩ : syracuseStep 8293499 = 12440249) B12440249
theorem B5528999 : Blo 2183435 5528999 := bstep (se 1 (by rfl) ⟨4146749, by rfl⟩ : syracuseStep 5528999 = 8293499) B8293499
theorem B3685999 : Blo 2183435 3685999 := bstep (se 1 (by rfl) ⟨2764499, by rfl⟩ : syracuseStep 3685999 = 5528999) B5528999
theorem B4914665 : Blo 2183435 4914665 := bstep (se 2 (by rfl) ⟨1842999, by rfl⟩ : syracuseStep 4914665 = 3685999) B3685999
theorem B3276443 : Blo 2183435 3276443 := bstep (se 1 (by rfl) ⟨2457332, by rfl⟩ : syracuseStep 3276443 = 4914665) B4914665
theorem B2184295 : Blo 2183435 2184295 := bstep (se 1 (by rfl) ⟨1638221, by rfl⟩ : syracuseStep 2184295 = 3276443) B3276443
theorem B2457337 : Blo 2183435 2457337 := bbase (se 2 (by rfl) ⟨921501, by rfl⟩ : syracuseStep 2457337 = 1843003) (by norm_num)
theorem B3276449 : Blo 2183435 3276449 := bstep (se 2 (by rfl) ⟨1228668, by rfl⟩ : syracuseStep 3276449 = 2457337) B2457337
theorem B2184299 : Blo 2183435 2184299 := bstep (se 1 (by rfl) ⟨1638224, by rfl⟩ : syracuseStep 2184299 = 3276449) B3276449
theorem B2624125 : Blo 2183435 2624125 := bbase (se 3 (by rfl) ⟨492023, by rfl⟩ : syracuseStep 2624125 = 984047) (by norm_num)
theorem B3498833 : Blo 2183435 3498833 := bstep (se 2 (by rfl) ⟨1312062, by rfl⟩ : syracuseStep 3498833 = 2624125) B2624125
theorem B9330221 : Blo 2183435 9330221 := bstep (se 3 (by rfl) ⟨1749416, by rfl⟩ : syracuseStep 9330221 = 3498833) B3498833
theorem B6220147 : Blo 2183435 6220147 := bstep (se 1 (by rfl) ⟨4665110, by rfl⟩ : syracuseStep 6220147 = 9330221) B9330221
theorem B8293529 : Blo 2183435 8293529 := bstep (se 2 (by rfl) ⟨3110073, by rfl⟩ : syracuseStep 8293529 = 6220147) B6220147
theorem B5529019 : Blo 2183435 5529019 := bstep (se 1 (by rfl) ⟨4146764, by rfl⟩ : syracuseStep 5529019 = 8293529) B8293529
theorem B7372025 : Blo 2183435 7372025 := bstep (se 2 (by rfl) ⟨2764509, by rfl⟩ : syracuseStep 7372025 = 5529019) B5529019
theorem B4914683 : Blo 2183435 4914683 := bstep (se 1 (by rfl) ⟨3686012, by rfl⟩ : syracuseStep 4914683 = 7372025) B7372025
theorem B3276455 : Blo 2183435 3276455 := bstep (se 1 (by rfl) ⟨2457341, by rfl⟩ : syracuseStep 3276455 = 4914683) B4914683
theorem B2184303 : Blo 2183435 2184303 := bstep (se 1 (by rfl) ⟨1638227, by rfl⟩ : syracuseStep 2184303 = 3276455) B3276455
theorem B3276461 : Blo 2183435 3276461 := bbase (se 3 (by rfl) ⟨614336, by rfl⟩ : syracuseStep 3276461 = 1228673) (by norm_num)
theorem B2184307 : Blo 2183435 2184307 := bstep (se 1 (by rfl) ⟨1638230, by rfl⟩ : syracuseStep 2184307 = 3276461) B3276461
theorem B4914701 : Blo 2183435 4914701 := bbase (se 3 (by rfl) ⟨921506, by rfl⟩ : syracuseStep 4914701 = 1843013) (by norm_num)
theorem B3276467 : Blo 2183435 3276467 := bstep (se 1 (by rfl) ⟨2457350, by rfl⟩ : syracuseStep 3276467 = 4914701) B4914701
theorem B2184311 : Blo 2183435 2184311 := bstep (se 1 (by rfl) ⟨1638233, by rfl⟩ : syracuseStep 2184311 = 3276467) B3276467
theorem B2764525 : Blo 2183435 2764525 := bbase (se 3 (by rfl) ⟨518348, by rfl⟩ : syracuseStep 2764525 = 1036697) (by norm_num)
theorem B3686033 : Blo 2183435 3686033 := bstep (se 2 (by rfl) ⟨1382262, by rfl⟩ : syracuseStep 3686033 = 2764525) B2764525
theorem B2457355 : Blo 2183435 2457355 := bstep (se 1 (by rfl) ⟨1843016, by rfl⟩ : syracuseStep 2457355 = 3686033) B3686033
theorem B3276473 : Blo 2183435 3276473 := bstep (se 2 (by rfl) ⟨1228677, by rfl⟩ : syracuseStep 3276473 = 2457355) B2457355
theorem B2184315 : Blo 2183435 2184315 := bstep (se 1 (by rfl) ⟨1638236, by rfl⟩ : syracuseStep 2184315 = 3276473) B3276473
theorem B79708373 : Blo 2183435 79708373 := bbase (se 7 (by rfl) ⟨934082, by rfl⟩ : syracuseStep 79708373 = 1868165) (by norm_num)
theorem B53138915 : Blo 2183435 53138915 := bstep (se 1 (by rfl) ⟨39854186, by rfl⟩ : syracuseStep 53138915 = 79708373) B79708373
theorem B35425943 : Blo 2183435 35425943 := bstep (se 1 (by rfl) ⟨26569457, by rfl⟩ : syracuseStep 35425943 = 53138915) B53138915
theorem B23617295 : Blo 2183435 23617295 := bstep (se 1 (by rfl) ⟨17712971, by rfl⟩ : syracuseStep 23617295 = 35425943) B35425943
theorem B15744863 : Blo 2183435 15744863 := bstep (se 1 (by rfl) ⟨11808647, by rfl⟩ : syracuseStep 15744863 = 23617295) B23617295
theorem B10496575 : Blo 2183435 10496575 := bstep (se 1 (by rfl) ⟨7872431, by rfl⟩ : syracuseStep 10496575 = 15744863) B15744863
theorem B13995433 : Blo 2183435 13995433 := bstep (se 2 (by rfl) ⟨5248287, by rfl⟩ : syracuseStep 13995433 = 10496575) B10496575
theorem B18660577 : Blo 2183435 18660577 := bstep (se 2 (by rfl) ⟨6997716, by rfl⟩ : syracuseStep 18660577 = 13995433) B13995433
theorem B24880769 : Blo 2183435 24880769 := bstep (se 2 (by rfl) ⟨9330288, by rfl⟩ : syracuseStep 24880769 = 18660577) B18660577
theorem B16587179 : Blo 2183435 16587179 := bstep (se 1 (by rfl) ⟨12440384, by rfl⟩ : syracuseStep 16587179 = 24880769) B24880769
theorem B11058119 : Blo 2183435 11058119 := bstep (se 1 (by rfl) ⟨8293589, by rfl⟩ : syracuseStep 11058119 = 16587179) B16587179
theorem B7372079 : Blo 2183435 7372079 := bstep (se 1 (by rfl) ⟨5529059, by rfl⟩ : syracuseStep 7372079 = 11058119) B11058119
theorem B4914719 : Blo 2183435 4914719 := bstep (se 1 (by rfl) ⟨3686039, by rfl⟩ : syracuseStep 4914719 = 7372079) B7372079
theorem B3276479 : Blo 2183435 3276479 := bstep (se 1 (by rfl) ⟨2457359, by rfl⟩ : syracuseStep 3276479 = 4914719) B4914719
theorem B2184319 : Blo 2183435 2184319 := bstep (se 1 (by rfl) ⟨1638239, by rfl⟩ : syracuseStep 2184319 = 3276479) B3276479
theorem B3276485 : Blo 2183435 3276485 := bbase (se 4 (by rfl) ⟨307170, by rfl⟩ : syracuseStep 3276485 = 614341) (by norm_num)
theorem B2184323 : Blo 2183435 2184323 := bstep (se 1 (by rfl) ⟨1638242, by rfl⟩ : syracuseStep 2184323 = 3276485) B3276485
theorem B3686053 : Blo 2183435 3686053 := bbase (se 4 (by rfl) ⟨345567, by rfl⟩ : syracuseStep 3686053 = 691135) (by norm_num)
theorem B4914737 : Blo 2183435 4914737 := bstep (se 2 (by rfl) ⟨1843026, by rfl⟩ : syracuseStep 4914737 = 3686053) B3686053
theorem B3276491 : Blo 2183435 3276491 := bstep (se 1 (by rfl) ⟨2457368, by rfl⟩ : syracuseStep 3276491 = 4914737) B4914737
theorem B2184327 : Blo 2183435 2184327 := bstep (se 1 (by rfl) ⟨1638245, by rfl⟩ : syracuseStep 2184327 = 3276491) B3276491
theorem B2457373 : Blo 2183435 2457373 := bbase (se 3 (by rfl) ⟨460757, by rfl⟩ : syracuseStep 2457373 = 921515) (by norm_num)
theorem B3276497 : Blo 2183435 3276497 := bstep (se 2 (by rfl) ⟨1228686, by rfl⟩ : syracuseStep 3276497 = 2457373) B2457373
theorem B2184331 : Blo 2183435 2184331 := bstep (se 1 (by rfl) ⟨1638248, by rfl⟩ : syracuseStep 2184331 = 3276497) B3276497
theorem B7372133 : Blo 2183435 7372133 := bbase (se 4 (by rfl) ⟨691137, by rfl⟩ : syracuseStep 7372133 = 1382275) (by norm_num)
theorem B4914755 : Blo 2183435 4914755 := bstep (se 1 (by rfl) ⟨3686066, by rfl⟩ : syracuseStep 4914755 = 7372133) B7372133
theorem B3276503 : Blo 2183435 3276503 := bstep (se 1 (by rfl) ⟨2457377, by rfl⟩ : syracuseStep 3276503 = 4914755) B4914755
theorem B2184335 : Blo 2183435 2184335 := bstep (se 1 (by rfl) ⟨1638251, by rfl⟩ : syracuseStep 2184335 = 3276503) B3276503
theorem B3276509 : Blo 2183435 3276509 := bbase (se 3 (by rfl) ⟨614345, by rfl⟩ : syracuseStep 3276509 = 1228691) (by norm_num)
theorem B2184339 : Blo 2183435 2184339 := bstep (se 1 (by rfl) ⟨1638254, by rfl⟩ : syracuseStep 2184339 = 3276509) B3276509
theorem B4914773 : Blo 2183435 4914773 := bbase (se 8 (by rfl) ⟨28797, by rfl⟩ : syracuseStep 4914773 = 57595) (by norm_num)
theorem B3276515 : Blo 2183435 3276515 := bstep (se 1 (by rfl) ⟨2457386, by rfl⟩ : syracuseStep 3276515 = 4914773) B4914773
theorem B2184343 : Blo 2183435 2184343 := bstep (se 1 (by rfl) ⟨1638257, by rfl⟩ : syracuseStep 2184343 = 3276515) B3276515
theorem B4665205 : Blo 2183435 4665205 := bbase (se 5 (by rfl) ⟨218681, by rfl⟩ : syracuseStep 4665205 = 437363) (by norm_num)
theorem B6220273 : Blo 2183435 6220273 := bstep (se 2 (by rfl) ⟨2332602, by rfl⟩ : syracuseStep 6220273 = 4665205) B4665205
theorem B8293697 : Blo 2183435 8293697 := bstep (se 2 (by rfl) ⟨3110136, by rfl⟩ : syracuseStep 8293697 = 6220273) B6220273
theorem B5529131 : Blo 2183435 5529131 := bstep (se 1 (by rfl) ⟨4146848, by rfl⟩ : syracuseStep 5529131 = 8293697) B8293697
theorem B3686087 : Blo 2183435 3686087 := bstep (se 1 (by rfl) ⟨2764565, by rfl⟩ : syracuseStep 3686087 = 5529131) B5529131
theorem B2457391 : Blo 2183435 2457391 := bstep (se 1 (by rfl) ⟨1843043, by rfl⟩ : syracuseStep 2457391 = 3686087) B3686087
theorem B3276521 : Blo 2183435 3276521 := bstep (se 2 (by rfl) ⟨1228695, by rfl⟩ : syracuseStep 3276521 = 2457391) B2457391
theorem B2184347 : Blo 2183435 2184347 := bstep (se 1 (by rfl) ⟨1638260, by rfl⟩ : syracuseStep 2184347 = 3276521) B3276521
theorem B11808821 : Blo 2183435 11808821 := bbase (se 5 (by rfl) ⟨553538, by rfl⟩ : syracuseStep 11808821 = 1107077) (by norm_num)
theorem B7872547 : Blo 2183435 7872547 := bstep (se 1 (by rfl) ⟨5904410, by rfl⟩ : syracuseStep 7872547 = 11808821) B11808821
theorem B10496729 : Blo 2183435 10496729 := bstep (se 2 (by rfl) ⟨3936273, by rfl⟩ : syracuseStep 10496729 = 7872547) B7872547
theorem B27991277 : Blo 2183435 27991277 := bstep (se 3 (by rfl) ⟨5248364, by rfl⟩ : syracuseStep 27991277 = 10496729) B10496729
theorem B18660851 : Blo 2183435 18660851 := bstep (se 1 (by rfl) ⟨13995638, by rfl⟩ : syracuseStep 18660851 = 27991277) B27991277
theorem B12440567 : Blo 2183435 12440567 := bstep (se 1 (by rfl) ⟨9330425, by rfl⟩ : syracuseStep 12440567 = 18660851) B18660851
theorem B8293711 : Blo 2183435 8293711 := bstep (se 1 (by rfl) ⟨6220283, by rfl⟩ : syracuseStep 8293711 = 12440567) B12440567
theorem B11058281 : Blo 2183435 11058281 := bstep (se 2 (by rfl) ⟨4146855, by rfl⟩ : syracuseStep 11058281 = 8293711) B8293711
theorem B7372187 : Blo 2183435 7372187 := bstep (se 1 (by rfl) ⟨5529140, by rfl⟩ : syracuseStep 7372187 = 11058281) B11058281
theorem B4914791 : Blo 2183435 4914791 := bstep (se 1 (by rfl) ⟨3686093, by rfl⟩ : syracuseStep 4914791 = 7372187) B7372187
theorem B3276527 : Blo 2183435 3276527 := bstep (se 1 (by rfl) ⟨2457395, by rfl⟩ : syracuseStep 3276527 = 4914791) B4914791
theorem B2184351 : Blo 2183435 2184351 := bstep (se 1 (by rfl) ⟨1638263, by rfl⟩ : syracuseStep 2184351 = 3276527) B3276527
theorem B3276533 : Blo 2183435 3276533 := bbase (se 5 (by rfl) ⟨153587, by rfl⟩ : syracuseStep 3276533 = 307175) (by norm_num)
theorem B2184355 : Blo 2183435 2184355 := bstep (se 1 (by rfl) ⟨1638266, by rfl⟩ : syracuseStep 2184355 = 3276533) B3276533
theorem B3321245 : Blo 2183435 3321245 := bbase (se 3 (by rfl) ⟨622733, by rfl⟩ : syracuseStep 3321245 = 1245467) (by norm_num)
theorem B2214163 : Blo 2183435 2214163 := bstep (se 1 (by rfl) ⟨1660622, by rfl⟩ : syracuseStep 2214163 = 3321245) B3321245
theorem B2952217 : Blo 2183435 2952217 := bstep (se 2 (by rfl) ⟨1107081, by rfl⟩ : syracuseStep 2952217 = 2214163) B2214163
theorem B3936289 : Blo 2183435 3936289 := bstep (se 2 (by rfl) ⟨1476108, by rfl⟩ : syracuseStep 3936289 = 2952217) B2952217
theorem B5248385 : Blo 2183435 5248385 := bstep (se 2 (by rfl) ⟨1968144, by rfl⟩ : syracuseStep 5248385 = 3936289) B3936289
theorem B3498923 : Blo 2183435 3498923 := bstep (se 1 (by rfl) ⟨2624192, by rfl⟩ : syracuseStep 3498923 = 5248385) B5248385
theorem B9330461 : Blo 2183435 9330461 := bstep (se 3 (by rfl) ⟨1749461, by rfl⟩ : syracuseStep 9330461 = 3498923) B3498923
theorem B6220307 : Blo 2183435 6220307 := bstep (se 1 (by rfl) ⟨4665230, by rfl⟩ : syracuseStep 6220307 = 9330461) B9330461
theorem B4146871 : Blo 2183435 4146871 := bstep (se 1 (by rfl) ⟨3110153, by rfl⟩ : syracuseStep 4146871 = 6220307) B6220307
theorem B5529161 : Blo 2183435 5529161 := bstep (se 2 (by rfl) ⟨2073435, by rfl⟩ : syracuseStep 5529161 = 4146871) B4146871
theorem B3686107 : Blo 2183435 3686107 := bstep (se 1 (by rfl) ⟨2764580, by rfl⟩ : syracuseStep 3686107 = 5529161) B5529161
theorem B4914809 : Blo 2183435 4914809 := bstep (se 2 (by rfl) ⟨1843053, by rfl⟩ : syracuseStep 4914809 = 3686107) B3686107
theorem B3276539 : Blo 2183435 3276539 := bstep (se 1 (by rfl) ⟨2457404, by rfl⟩ : syracuseStep 3276539 = 4914809) B4914809
theorem B2184359 : Blo 2183435 2184359 := bstep (se 1 (by rfl) ⟨1638269, by rfl⟩ : syracuseStep 2184359 = 3276539) B3276539
theorem B2457409 : Blo 2183435 2457409 := bbase (se 2 (by rfl) ⟨921528, by rfl⟩ : syracuseStep 2457409 = 1843057) (by norm_num)
theorem B3276545 : Blo 2183435 3276545 := bstep (se 2 (by rfl) ⟨1228704, by rfl⟩ : syracuseStep 3276545 = 2457409) B2457409
theorem B2184363 : Blo 2183435 2184363 := bstep (se 1 (by rfl) ⟨1638272, by rfl⟩ : syracuseStep 2184363 = 3276545) B3276545
theorem B5529181 : Blo 2183435 5529181 := bbase (se 3 (by rfl) ⟨1036721, by rfl⟩ : syracuseStep 5529181 = 2073443) (by norm_num)
theorem B7372241 : Blo 2183435 7372241 := bstep (se 2 (by rfl) ⟨2764590, by rfl⟩ : syracuseStep 7372241 = 5529181) B5529181
theorem B4914827 : Blo 2183435 4914827 := bstep (se 1 (by rfl) ⟨3686120, by rfl⟩ : syracuseStep 4914827 = 7372241) B7372241
theorem B3276551 : Blo 2183435 3276551 := bstep (se 1 (by rfl) ⟨2457413, by rfl⟩ : syracuseStep 3276551 = 4914827) B4914827
theorem B2184367 : Blo 2183435 2184367 := bstep (se 1 (by rfl) ⟨1638275, by rfl⟩ : syracuseStep 2184367 = 3276551) B3276551
theorem B3276557 : Blo 2183435 3276557 := bbase (se 3 (by rfl) ⟨614354, by rfl⟩ : syracuseStep 3276557 = 1228709) (by norm_num)
theorem B2184371 : Blo 2183435 2184371 := bstep (se 1 (by rfl) ⟨1638278, by rfl⟩ : syracuseStep 2184371 = 3276557) B3276557
theorem B4914845 : Blo 2183435 4914845 := bbase (se 3 (by rfl) ⟨921533, by rfl⟩ : syracuseStep 4914845 = 1843067) (by norm_num)
theorem B3276563 : Blo 2183435 3276563 := bstep (se 1 (by rfl) ⟨2457422, by rfl⟩ : syracuseStep 3276563 = 4914845) B4914845
theorem B2184375 : Blo 2183435 2184375 := bstep (se 1 (by rfl) ⟨1638281, by rfl⟩ : syracuseStep 2184375 = 3276563) B3276563
theorem B3686141 : Blo 2183435 3686141 := bbase (se 3 (by rfl) ⟨691151, by rfl⟩ : syracuseStep 3686141 = 1382303) (by norm_num)
theorem B2457427 : Blo 2183435 2457427 := bstep (se 1 (by rfl) ⟨1843070, by rfl⟩ : syracuseStep 2457427 = 3686141) B3686141
theorem B3276569 : Blo 2183435 3276569 := bstep (se 2 (by rfl) ⟨1228713, by rfl⟩ : syracuseStep 3276569 = 2457427) B2457427
theorem B2184379 : Blo 2183435 2184379 := bstep (se 1 (by rfl) ⟨1638284, by rfl⟩ : syracuseStep 2184379 = 3276569) B3276569
theorem B2624221 : Blo 2183435 2624221 := bbase (se 3 (by rfl) ⟨492041, by rfl⟩ : syracuseStep 2624221 = 984083) (by norm_num)
theorem B3498961 : Blo 2183435 3498961 := bstep (se 2 (by rfl) ⟨1312110, by rfl⟩ : syracuseStep 3498961 = 2624221) B2624221
theorem B4665281 : Blo 2183435 4665281 := bstep (se 2 (by rfl) ⟨1749480, by rfl⟩ : syracuseStep 4665281 = 3498961) B3498961
theorem B12440749 : Blo 2183435 12440749 := bstep (se 3 (by rfl) ⟨2332640, by rfl⟩ : syracuseStep 12440749 = 4665281) B4665281
theorem B16587665 : Blo 2183435 16587665 := bstep (se 2 (by rfl) ⟨6220374, by rfl⟩ : syracuseStep 16587665 = 12440749) B12440749
theorem B11058443 : Blo 2183435 11058443 := bstep (se 1 (by rfl) ⟨8293832, by rfl⟩ : syracuseStep 11058443 = 16587665) B16587665
theorem B7372295 : Blo 2183435 7372295 := bstep (se 1 (by rfl) ⟨5529221, by rfl⟩ : syracuseStep 7372295 = 11058443) B11058443
theorem B4914863 : Blo 2183435 4914863 := bstep (se 1 (by rfl) ⟨3686147, by rfl⟩ : syracuseStep 4914863 = 7372295) B7372295
theorem B3276575 : Blo 2183435 3276575 := bstep (se 1 (by rfl) ⟨2457431, by rfl⟩ : syracuseStep 3276575 = 4914863) B4914863
theorem B2184383 : Blo 2183435 2184383 := bstep (se 1 (by rfl) ⟨1638287, by rfl⟩ : syracuseStep 2184383 = 3276575) B3276575
theorem B3276581 : Blo 2183435 3276581 := bbase (se 4 (by rfl) ⟨307179, by rfl⟩ : syracuseStep 3276581 = 614359) (by norm_num)
theorem B2184387 : Blo 2183435 2184387 := bstep (se 1 (by rfl) ⟨1638290, by rfl⟩ : syracuseStep 2184387 = 3276581) B3276581
theorem B2764621 : Blo 2183435 2764621 := bbase (se 3 (by rfl) ⟨518366, by rfl⟩ : syracuseStep 2764621 = 1036733) (by norm_num)
theorem B3686161 : Blo 2183435 3686161 := bstep (se 2 (by rfl) ⟨1382310, by rfl⟩ : syracuseStep 3686161 = 2764621) B2764621
theorem B4914881 : Blo 2183435 4914881 := bstep (se 2 (by rfl) ⟨1843080, by rfl⟩ : syracuseStep 4914881 = 3686161) B3686161
theorem B3276587 : Blo 2183435 3276587 := bstep (se 1 (by rfl) ⟨2457440, by rfl⟩ : syracuseStep 3276587 = 4914881) B4914881
theorem B2184391 : Blo 2183435 2184391 := bstep (se 1 (by rfl) ⟨1638293, by rfl⟩ : syracuseStep 2184391 = 3276587) B3276587
theorem B2457445 : Blo 2183435 2457445 := bbase (se 4 (by rfl) ⟨230385, by rfl⟩ : syracuseStep 2457445 = 460771) (by norm_num)
theorem B3276593 : Blo 2183435 3276593 := bstep (se 2 (by rfl) ⟨1228722, by rfl⟩ : syracuseStep 3276593 = 2457445) B2457445
theorem B2184395 : Blo 2183435 2184395 := bstep (se 1 (by rfl) ⟨1638296, by rfl⟩ : syracuseStep 2184395 = 3276593) B3276593
theorem B6220421 : Blo 2183435 6220421 := bbase (se 4 (by rfl) ⟨583164, by rfl⟩ : syracuseStep 6220421 = 1166329) (by norm_num)
theorem B4146947 : Blo 2183435 4146947 := bstep (se 1 (by rfl) ⟨3110210, by rfl⟩ : syracuseStep 4146947 = 6220421) B6220421
theorem B2764631 : Blo 2183435 2764631 := bstep (se 1 (by rfl) ⟨2073473, by rfl⟩ : syracuseStep 2764631 = 4146947) B4146947
theorem B7372349 : Blo 2183435 7372349 := bstep (se 3 (by rfl) ⟨1382315, by rfl⟩ : syracuseStep 7372349 = 2764631) B2764631
theorem B4914899 : Blo 2183435 4914899 := bstep (se 1 (by rfl) ⟨3686174, by rfl⟩ : syracuseStep 4914899 = 7372349) B7372349
theorem B3276599 : Blo 2183435 3276599 := bstep (se 1 (by rfl) ⟨2457449, by rfl⟩ : syracuseStep 3276599 = 4914899) B4914899
theorem B2184399 : Blo 2183435 2184399 := bstep (se 1 (by rfl) ⟨1638299, by rfl⟩ : syracuseStep 2184399 = 3276599) B3276599
theorem B3276605 : Blo 2183435 3276605 := bbase (se 3 (by rfl) ⟨614363, by rfl⟩ : syracuseStep 3276605 = 1228727) (by norm_num)
theorem B2184403 : Blo 2183435 2184403 := bstep (se 1 (by rfl) ⟨1638302, by rfl⟩ : syracuseStep 2184403 = 3276605) B3276605
theorem B4914917 : Blo 2183435 4914917 := bbase (se 4 (by rfl) ⟨460773, by rfl⟩ : syracuseStep 4914917 = 921547) (by norm_num)
theorem B3276611 : Blo 2183435 3276611 := bstep (se 1 (by rfl) ⟨2457458, by rfl⟩ : syracuseStep 3276611 = 4914917) B4914917
theorem B2184407 : Blo 2183435 2184407 := bstep (se 1 (by rfl) ⟨1638305, by rfl⟩ : syracuseStep 2184407 = 3276611) B3276611
theorem B5529293 : Blo 2183435 5529293 := bbase (se 3 (by rfl) ⟨1036742, by rfl⟩ : syracuseStep 5529293 = 2073485) (by norm_num)
theorem B3686195 : Blo 2183435 3686195 := bstep (se 1 (by rfl) ⟨2764646, by rfl⟩ : syracuseStep 3686195 = 5529293) B5529293
theorem B2457463 : Blo 2183435 2457463 := bstep (se 1 (by rfl) ⟨1843097, by rfl⟩ : syracuseStep 2457463 = 3686195) B3686195
theorem B3276617 : Blo 2183435 3276617 := bstep (se 2 (by rfl) ⟨1228731, by rfl⟩ : syracuseStep 3276617 = 2457463) B2457463
theorem B2184411 : Blo 2183435 2184411 := bstep (se 1 (by rfl) ⟨1638308, by rfl⟩ : syracuseStep 2184411 = 3276617) B3276617
theorem B3499013 : Blo 2183435 3499013 := bbase (se 4 (by rfl) ⟨328032, by rfl⟩ : syracuseStep 3499013 = 656065) (by norm_num)
theorem B2332675 : Blo 2183435 2332675 := bstep (se 1 (by rfl) ⟨1749506, by rfl⟩ : syracuseStep 2332675 = 3499013) B3499013
theorem B3110233 : Blo 2183435 3110233 := bstep (se 2 (by rfl) ⟨1166337, by rfl⟩ : syracuseStep 3110233 = 2332675) B2332675
theorem B4146977 : Blo 2183435 4146977 := bstep (se 2 (by rfl) ⟨1555116, by rfl⟩ : syracuseStep 4146977 = 3110233) B3110233
theorem B11058605 : Blo 2183435 11058605 := bstep (se 3 (by rfl) ⟨2073488, by rfl⟩ : syracuseStep 11058605 = 4146977) B4146977
theorem B7372403 : Blo 2183435 7372403 := bstep (se 1 (by rfl) ⟨5529302, by rfl⟩ : syracuseStep 7372403 = 11058605) B11058605
theorem B4914935 : Blo 2183435 4914935 := bstep (se 1 (by rfl) ⟨3686201, by rfl⟩ : syracuseStep 4914935 = 7372403) B7372403
theorem B3276623 : Blo 2183435 3276623 := bstep (se 1 (by rfl) ⟨2457467, by rfl⟩ : syracuseStep 3276623 = 4914935) B4914935
theorem B2184415 : Blo 2183435 2184415 := bstep (se 1 (by rfl) ⟨1638311, by rfl⟩ : syracuseStep 2184415 = 3276623) B3276623
theorem B3276629 : Blo 2183435 3276629 := bbase (se 9 (by rfl) ⟨9599, by rfl⟩ : syracuseStep 3276629 = 19199) (by norm_num)
theorem B2184419 : Blo 2183435 2184419 := bstep (se 1 (by rfl) ⟨1638314, by rfl⟩ : syracuseStep 2184419 = 3276629) B3276629
theorem B10497077 : Blo 2183435 10497077 := bbase (se 5 (by rfl) ⟨492050, by rfl⟩ : syracuseStep 10497077 = 984101) (by norm_num)
theorem B6998051 : Blo 2183435 6998051 := bstep (se 1 (by rfl) ⟨5248538, by rfl⟩ : syracuseStep 6998051 = 10497077) B10497077
theorem B4665367 : Blo 2183435 4665367 := bstep (se 1 (by rfl) ⟨3499025, by rfl⟩ : syracuseStep 4665367 = 6998051) B6998051
theorem B6220489 : Blo 2183435 6220489 := bstep (se 2 (by rfl) ⟨2332683, by rfl⟩ : syracuseStep 6220489 = 4665367) B4665367
theorem B8293985 : Blo 2183435 8293985 := bstep (se 2 (by rfl) ⟨3110244, by rfl⟩ : syracuseStep 8293985 = 6220489) B6220489
theorem B5529323 : Blo 2183435 5529323 := bstep (se 1 (by rfl) ⟨4146992, by rfl⟩ : syracuseStep 5529323 = 8293985) B8293985
theorem B3686215 : Blo 2183435 3686215 := bstep (se 1 (by rfl) ⟨2764661, by rfl⟩ : syracuseStep 3686215 = 5529323) B5529323
theorem B4914953 : Blo 2183435 4914953 := bstep (se 2 (by rfl) ⟨1843107, by rfl⟩ : syracuseStep 4914953 = 3686215) B3686215
theorem B3276635 : Blo 2183435 3276635 := bstep (se 1 (by rfl) ⟨2457476, by rfl⟩ : syracuseStep 3276635 = 4914953) B4914953
theorem B2184423 : Blo 2183435 2184423 := bstep (se 1 (by rfl) ⟨1638317, by rfl⟩ : syracuseStep 2184423 = 3276635) B3276635
theorem B2457481 : Blo 2183435 2457481 := bbase (se 2 (by rfl) ⟨921555, by rfl⟩ : syracuseStep 2457481 = 1843111) (by norm_num)
theorem B3276641 : Blo 2183435 3276641 := bstep (se 2 (by rfl) ⟨1228740, by rfl⟩ : syracuseStep 3276641 = 2457481) B2457481
theorem B2184427 : Blo 2183435 2184427 := bstep (se 1 (by rfl) ⟨1638320, by rfl⟩ : syracuseStep 2184427 = 3276641) B3276641
theorem B5320165 : Blo 2183435 5320165 := bbase (se 4 (by rfl) ⟨498765, by rfl⟩ : syracuseStep 5320165 = 997531) (by norm_num)
theorem B7093553 : Blo 2183435 7093553 := bstep (se 2 (by rfl) ⟨2660082, by rfl⟩ : syracuseStep 7093553 = 5320165) B5320165
theorem B18916141 : Blo 2183435 18916141 := bstep (se 3 (by rfl) ⟨3546776, by rfl⟩ : syracuseStep 18916141 = 7093553) B7093553
theorem B25221521 : Blo 2183435 25221521 := bstep (se 2 (by rfl) ⟨9458070, by rfl⟩ : syracuseStep 25221521 = 18916141) B18916141
theorem B16814347 : Blo 2183435 16814347 := bstep (se 1 (by rfl) ⟨12610760, by rfl⟩ : syracuseStep 16814347 = 25221521) B25221521
theorem B358706069 : Blo 2183435 358706069 := bstep (se 6 (by rfl) ⟨8407173, by rfl⟩ : syracuseStep 358706069 = 16814347) B16814347
theorem B239137379 : Blo 2183435 239137379 := bstep (se 1 (by rfl) ⟨179353034, by rfl⟩ : syracuseStep 239137379 = 358706069) B358706069
theorem B159424919 : Blo 2183435 159424919 := bstep (se 1 (by rfl) ⟨119568689, by rfl⟩ : syracuseStep 159424919 = 239137379) B239137379
theorem B106283279 : Blo 2183435 106283279 := bstep (se 1 (by rfl) ⟨79712459, by rfl⟩ : syracuseStep 106283279 = 159424919) B159424919
theorem B70855519 : Blo 2183435 70855519 := bstep (se 1 (by rfl) ⟨53141639, by rfl⟩ : syracuseStep 70855519 = 106283279) B106283279
theorem B94474025 : Blo 2183435 94474025 := bstep (se 2 (by rfl) ⟨35427759, by rfl⟩ : syracuseStep 94474025 = 70855519) B70855519
theorem B62982683 : Blo 2183435 62982683 := bstep (se 1 (by rfl) ⟨47237012, by rfl⟩ : syracuseStep 62982683 = 94474025) B94474025
theorem B41988455 : Blo 2183435 41988455 := bstep (se 1 (by rfl) ⟨31491341, by rfl⟩ : syracuseStep 41988455 = 62982683) B62982683
theorem B27992303 : Blo 2183435 27992303 := bstep (se 1 (by rfl) ⟨20994227, by rfl⟩ : syracuseStep 27992303 = 41988455) B41988455
theorem B18661535 : Blo 2183435 18661535 := bstep (se 1 (by rfl) ⟨13996151, by rfl⟩ : syracuseStep 18661535 = 27992303) B27992303
theorem B12441023 : Blo 2183435 12441023 := bstep (se 1 (by rfl) ⟨9330767, by rfl⟩ : syracuseStep 12441023 = 18661535) B18661535
theorem B8294015 : Blo 2183435 8294015 := bstep (se 1 (by rfl) ⟨6220511, by rfl⟩ : syracuseStep 8294015 = 12441023) B12441023
theorem B5529343 : Blo 2183435 5529343 := bstep (se 1 (by rfl) ⟨4147007, by rfl⟩ : syracuseStep 5529343 = 8294015) B8294015
theorem B7372457 : Blo 2183435 7372457 := bstep (se 2 (by rfl) ⟨2764671, by rfl⟩ : syracuseStep 7372457 = 5529343) B5529343
theorem B4914971 : Blo 2183435 4914971 := bstep (se 1 (by rfl) ⟨3686228, by rfl⟩ : syracuseStep 4914971 = 7372457) B7372457
theorem B3276647 : Blo 2183435 3276647 := bstep (se 1 (by rfl) ⟨2457485, by rfl⟩ : syracuseStep 3276647 = 4914971) B4914971
theorem B2184431 : Blo 2183435 2184431 := bstep (se 1 (by rfl) ⟨1638323, by rfl⟩ : syracuseStep 2184431 = 3276647) B3276647
theorem B3276653 : Blo 2183435 3276653 := bbase (se 3 (by rfl) ⟨614372, by rfl⟩ : syracuseStep 3276653 = 1228745) (by norm_num)
theorem B2184435 : Blo 2183435 2184435 := bstep (se 1 (by rfl) ⟨1638326, by rfl⟩ : syracuseStep 2184435 = 3276653) B3276653
theorem B4914989 : Blo 2183435 4914989 := bbase (se 3 (by rfl) ⟨921560, by rfl⟩ : syracuseStep 4914989 = 1843121) (by norm_num)
theorem B3276659 : Blo 2183435 3276659 := bstep (se 1 (by rfl) ⟨2457494, by rfl⟩ : syracuseStep 3276659 = 4914989) B4914989
theorem B2184439 : Blo 2183435 2184439 := bstep (se 1 (by rfl) ⟨1638329, by rfl⟩ : syracuseStep 2184439 = 3276659) B3276659
theorem B9330821 : Blo 2183435 9330821 := bbase (se 4 (by rfl) ⟨874764, by rfl⟩ : syracuseStep 9330821 = 1749529) (by norm_num)
theorem B6220547 : Blo 2183435 6220547 := bstep (se 1 (by rfl) ⟨4665410, by rfl⟩ : syracuseStep 6220547 = 9330821) B9330821
theorem B4147031 : Blo 2183435 4147031 := bstep (se 1 (by rfl) ⟨3110273, by rfl⟩ : syracuseStep 4147031 = 6220547) B6220547
theorem B2764687 : Blo 2183435 2764687 := bstep (se 1 (by rfl) ⟨2073515, by rfl⟩ : syracuseStep 2764687 = 4147031) B4147031
theorem B3686249 : Blo 2183435 3686249 := bstep (se 2 (by rfl) ⟨1382343, by rfl⟩ : syracuseStep 3686249 = 2764687) B2764687
theorem B2457499 : Blo 2183435 2457499 := bstep (se 1 (by rfl) ⟨1843124, by rfl⟩ : syracuseStep 2457499 = 3686249) B3686249
theorem B3276665 : Blo 2183435 3276665 := bstep (se 2 (by rfl) ⟨1228749, by rfl⟩ : syracuseStep 3276665 = 2457499) B2457499
theorem B2184443 : Blo 2183435 2184443 := bstep (se 1 (by rfl) ⟨1638332, by rfl⟩ : syracuseStep 2184443 = 3276665) B3276665
theorem B9964133 : Blo 2183435 9964133 := bbase (se 4 (by rfl) ⟨934137, by rfl⟩ : syracuseStep 9964133 = 1868275) (by norm_num)
theorem B6642755 : Blo 2183435 6642755 := bstep (se 1 (by rfl) ⟨4982066, by rfl⟩ : syracuseStep 6642755 = 9964133) B9964133
theorem B4428503 : Blo 2183435 4428503 := bstep (se 1 (by rfl) ⟨3321377, by rfl⟩ : syracuseStep 4428503 = 6642755) B6642755
theorem B2952335 : Blo 2183435 2952335 := bstep (se 1 (by rfl) ⟨2214251, by rfl⟩ : syracuseStep 2952335 = 4428503) B4428503
theorem B7872893 : Blo 2183435 7872893 := bstep (se 3 (by rfl) ⟨1476167, by rfl⟩ : syracuseStep 7872893 = 2952335) B2952335
theorem B5248595 : Blo 2183435 5248595 := bstep (se 1 (by rfl) ⟨3936446, by rfl⟩ : syracuseStep 5248595 = 7872893) B7872893
theorem B13996253 : Blo 2183435 13996253 := bstep (se 3 (by rfl) ⟨2624297, by rfl⟩ : syracuseStep 13996253 = 5248595) B5248595
theorem B37323341 : Blo 2183435 37323341 := bstep (se 3 (by rfl) ⟨6998126, by rfl⟩ : syracuseStep 37323341 = 13996253) B13996253
theorem B24882227 : Blo 2183435 24882227 := bstep (se 1 (by rfl) ⟨18661670, by rfl⟩ : syracuseStep 24882227 = 37323341) B37323341
theorem B16588151 : Blo 2183435 16588151 := bstep (se 1 (by rfl) ⟨12441113, by rfl⟩ : syracuseStep 16588151 = 24882227) B24882227
theorem B11058767 : Blo 2183435 11058767 := bstep (se 1 (by rfl) ⟨8294075, by rfl⟩ : syracuseStep 11058767 = 16588151) B16588151
theorem B7372511 : Blo 2183435 7372511 := bstep (se 1 (by rfl) ⟨5529383, by rfl⟩ : syracuseStep 7372511 = 11058767) B11058767
theorem B4915007 : Blo 2183435 4915007 := bstep (se 1 (by rfl) ⟨3686255, by rfl⟩ : syracuseStep 4915007 = 7372511) B7372511
theorem B3276671 : Blo 2183435 3276671 := bstep (se 1 (by rfl) ⟨2457503, by rfl⟩ : syracuseStep 3276671 = 4915007) B4915007
theorem B2184447 : Blo 2183435 2184447 := bstep (se 1 (by rfl) ⟨1638335, by rfl⟩ : syracuseStep 2184447 = 3276671) B3276671
theorem B3276677 : Blo 2183435 3276677 := bbase (se 4 (by rfl) ⟨307188, by rfl⟩ : syracuseStep 3276677 = 614377) (by norm_num)
theorem B2184451 : Blo 2183435 2184451 := bstep (se 1 (by rfl) ⟨1638338, by rfl⟩ : syracuseStep 2184451 = 3276677) B3276677
theorem B3686269 : Blo 2183435 3686269 := bbase (se 3 (by rfl) ⟨691175, by rfl⟩ : syracuseStep 3686269 = 1382351) (by norm_num)
theorem B4915025 : Blo 2183435 4915025 := bstep (se 2 (by rfl) ⟨1843134, by rfl⟩ : syracuseStep 4915025 = 3686269) B3686269
theorem B3276683 : Blo 2183435 3276683 := bstep (se 1 (by rfl) ⟨2457512, by rfl⟩ : syracuseStep 3276683 = 4915025) B4915025
theorem B2184455 : Blo 2183435 2184455 := bstep (se 1 (by rfl) ⟨1638341, by rfl⟩ : syracuseStep 2184455 = 3276683) B3276683
theorem B2457517 : Blo 2183435 2457517 := bbase (se 3 (by rfl) ⟨460784, by rfl⟩ : syracuseStep 2457517 = 921569) (by norm_num)
theorem B3276689 : Blo 2183435 3276689 := bstep (se 2 (by rfl) ⟨1228758, by rfl⟩ : syracuseStep 3276689 = 2457517) B2457517
theorem B2184459 : Blo 2183435 2184459 := bstep (se 1 (by rfl) ⟨1638344, by rfl⟩ : syracuseStep 2184459 = 3276689) B3276689
theorem B7372565 : Blo 2183435 7372565 := bbase (se 6 (by rfl) ⟨172794, by rfl⟩ : syracuseStep 7372565 = 345589) (by norm_num)
theorem B4915043 : Blo 2183435 4915043 := bstep (se 1 (by rfl) ⟨3686282, by rfl⟩ : syracuseStep 4915043 = 7372565) B7372565
theorem B3276695 : Blo 2183435 3276695 := bstep (se 1 (by rfl) ⟨2457521, by rfl⟩ : syracuseStep 3276695 = 4915043) B4915043
theorem B2184463 : Blo 2183435 2184463 := bstep (se 1 (by rfl) ⟨1638347, by rfl⟩ : syracuseStep 2184463 = 3276695) B3276695
theorem B3276701 : Blo 2183435 3276701 := bbase (se 3 (by rfl) ⟨614381, by rfl⟩ : syracuseStep 3276701 = 1228763) (by norm_num)
theorem B2184467 : Blo 2183435 2184467 := bstep (se 1 (by rfl) ⟨1638350, by rfl⟩ : syracuseStep 2184467 = 3276701) B3276701
theorem B4915061 : Blo 2183435 4915061 := bbase (se 5 (by rfl) ⟨230393, by rfl⟩ : syracuseStep 4915061 = 460787) (by norm_num)
theorem B3276707 : Blo 2183435 3276707 := bstep (se 1 (by rfl) ⟨2457530, by rfl⟩ : syracuseStep 3276707 = 4915061) B4915061
theorem B2184471 : Blo 2183435 2184471 := bstep (se 1 (by rfl) ⟨1638353, by rfl⟩ : syracuseStep 2184471 = 3276707) B3276707
theorem B11809493 : Blo 2183435 11809493 := bbase (se 7 (by rfl) ⟨138392, by rfl⟩ : syracuseStep 11809493 = 276785) (by norm_num)
theorem B7872995 : Blo 2183435 7872995 := bstep (se 1 (by rfl) ⟨5904746, by rfl⟩ : syracuseStep 7872995 = 11809493) B11809493
theorem B20994653 : Blo 2183435 20994653 := bstep (se 3 (by rfl) ⟨3936497, by rfl⟩ : syracuseStep 20994653 = 7872995) B7872995
theorem B13996435 : Blo 2183435 13996435 := bstep (se 1 (by rfl) ⟨10497326, by rfl⟩ : syracuseStep 13996435 = 20994653) B20994653
theorem B18661913 : Blo 2183435 18661913 := bstep (se 2 (by rfl) ⟨6998217, by rfl⟩ : syracuseStep 18661913 = 13996435) B13996435
theorem B12441275 : Blo 2183435 12441275 := bstep (se 1 (by rfl) ⟨9330956, by rfl⟩ : syracuseStep 12441275 = 18661913) B18661913
theorem B8294183 : Blo 2183435 8294183 := bstep (se 1 (by rfl) ⟨6220637, by rfl⟩ : syracuseStep 8294183 = 12441275) B12441275
theorem B5529455 : Blo 2183435 5529455 := bstep (se 1 (by rfl) ⟨4147091, by rfl⟩ : syracuseStep 5529455 = 8294183) B8294183
theorem B3686303 : Blo 2183435 3686303 := bstep (se 1 (by rfl) ⟨2764727, by rfl⟩ : syracuseStep 3686303 = 5529455) B5529455
theorem B2457535 : Blo 2183435 2457535 := bstep (se 1 (by rfl) ⟨1843151, by rfl⟩ : syracuseStep 2457535 = 3686303) B3686303
theorem B3276713 : Blo 2183435 3276713 := bstep (se 2 (by rfl) ⟨1228767, by rfl⟩ : syracuseStep 3276713 = 2457535) B2457535
theorem B2184475 : Blo 2183435 2184475 := bstep (se 1 (by rfl) ⟨1638356, by rfl⟩ : syracuseStep 2184475 = 3276713) B3276713
theorem B8294197 : Blo 2183435 8294197 := bbase (se 5 (by rfl) ⟨388790, by rfl⟩ : syracuseStep 8294197 = 777581) (by norm_num)
theorem B11058929 : Blo 2183435 11058929 := bstep (se 2 (by rfl) ⟨4147098, by rfl⟩ : syracuseStep 11058929 = 8294197) B8294197
theorem B7372619 : Blo 2183435 7372619 := bstep (se 1 (by rfl) ⟨5529464, by rfl⟩ : syracuseStep 7372619 = 11058929) B11058929
theorem B4915079 : Blo 2183435 4915079 := bstep (se 1 (by rfl) ⟨3686309, by rfl⟩ : syracuseStep 4915079 = 7372619) B7372619
theorem B3276719 : Blo 2183435 3276719 := bstep (se 1 (by rfl) ⟨2457539, by rfl⟩ : syracuseStep 3276719 = 4915079) B4915079
theorem B2184479 : Blo 2183435 2184479 := bstep (se 1 (by rfl) ⟨1638359, by rfl⟩ : syracuseStep 2184479 = 3276719) B3276719
theorem B3276725 : Blo 2183435 3276725 := bbase (se 5 (by rfl) ⟨153596, by rfl⟩ : syracuseStep 3276725 = 307193) (by norm_num)
theorem B2184483 : Blo 2183435 2184483 := bstep (se 1 (by rfl) ⟨1638362, by rfl⟩ : syracuseStep 2184483 = 3276725) B3276725
theorem B5529485 : Blo 2183435 5529485 := bbase (se 3 (by rfl) ⟨1036778, by rfl⟩ : syracuseStep 5529485 = 2073557) (by norm_num)
theorem B3686323 : Blo 2183435 3686323 := bstep (se 1 (by rfl) ⟨2764742, by rfl⟩ : syracuseStep 3686323 = 5529485) B5529485
theorem B4915097 : Blo 2183435 4915097 := bstep (se 2 (by rfl) ⟨1843161, by rfl⟩ : syracuseStep 4915097 = 3686323) B3686323
theorem B3276731 : Blo 2183435 3276731 := bstep (se 1 (by rfl) ⟨2457548, by rfl⟩ : syracuseStep 3276731 = 4915097) B4915097
theorem B2184487 : Blo 2183435 2184487 := bstep (se 1 (by rfl) ⟨1638365, by rfl⟩ : syracuseStep 2184487 = 3276731) B3276731
theorem B2457553 : Blo 2183435 2457553 := bbase (se 2 (by rfl) ⟨921582, by rfl⟩ : syracuseStep 2457553 = 1843165) (by norm_num)
theorem B3276737 : Blo 2183435 3276737 := bstep (se 2 (by rfl) ⟨1228776, by rfl⟩ : syracuseStep 3276737 = 2457553) B2457553
theorem B2184491 : Blo 2183435 2184491 := bstep (se 1 (by rfl) ⟨1638368, by rfl⟩ : syracuseStep 2184491 = 3276737) B3276737
theorem B3499141 : Blo 2183435 3499141 := bbase (se 4 (by rfl) ⟨328044, by rfl⟩ : syracuseStep 3499141 = 656089) (by norm_num)
theorem B4665521 : Blo 2183435 4665521 := bstep (se 2 (by rfl) ⟨1749570, by rfl⟩ : syracuseStep 4665521 = 3499141) B3499141
theorem B3110347 : Blo 2183435 3110347 := bstep (se 1 (by rfl) ⟨2332760, by rfl⟩ : syracuseStep 3110347 = 4665521) B4665521
theorem B4147129 : Blo 2183435 4147129 := bstep (se 2 (by rfl) ⟨1555173, by rfl⟩ : syracuseStep 4147129 = 3110347) B3110347
theorem B5529505 : Blo 2183435 5529505 := bstep (se 2 (by rfl) ⟨2073564, by rfl⟩ : syracuseStep 5529505 = 4147129) B4147129
theorem B7372673 : Blo 2183435 7372673 := bstep (se 2 (by rfl) ⟨2764752, by rfl⟩ : syracuseStep 7372673 = 5529505) B5529505
theorem B4915115 : Blo 2183435 4915115 := bstep (se 1 (by rfl) ⟨3686336, by rfl⟩ : syracuseStep 4915115 = 7372673) B7372673
theorem B3276743 : Blo 2183435 3276743 := bstep (se 1 (by rfl) ⟨2457557, by rfl⟩ : syracuseStep 3276743 = 4915115) B4915115
theorem B2184495 : Blo 2183435 2184495 := bstep (se 1 (by rfl) ⟨1638371, by rfl⟩ : syracuseStep 2184495 = 3276743) B3276743
theorem B3276749 : Blo 2183435 3276749 := bbase (se 3 (by rfl) ⟨614390, by rfl⟩ : syracuseStep 3276749 = 1228781) (by norm_num)
theorem B2184499 : Blo 2183435 2184499 := bstep (se 1 (by rfl) ⟨1638374, by rfl⟩ : syracuseStep 2184499 = 3276749) B3276749
theorem B4915133 : Blo 2183435 4915133 := bbase (se 3 (by rfl) ⟨921587, by rfl⟩ : syracuseStep 4915133 = 1843175) (by norm_num)
theorem B3276755 : Blo 2183435 3276755 := bstep (se 1 (by rfl) ⟨2457566, by rfl⟩ : syracuseStep 3276755 = 4915133) B4915133
theorem B2184503 : Blo 2183435 2184503 := bstep (se 1 (by rfl) ⟨1638377, by rfl⟩ : syracuseStep 2184503 = 3276755) B3276755
theorem B3686357 : Blo 2183435 3686357 := bbase (se 7 (by rfl) ⟨43199, by rfl⟩ : syracuseStep 3686357 = 86399) (by norm_num)
theorem B2457571 : Blo 2183435 2457571 := bstep (se 1 (by rfl) ⟨1843178, by rfl⟩ : syracuseStep 2457571 = 3686357) B3686357
theorem B3276761 : Blo 2183435 3276761 := bstep (se 2 (by rfl) ⟨1228785, by rfl⟩ : syracuseStep 3276761 = 2457571) B2457571
theorem B2184507 : Blo 2183435 2184507 := bstep (se 1 (by rfl) ⟨1638380, by rfl⟩ : syracuseStep 2184507 = 3276761) B3276761
theorem B9331109 : Blo 2183435 9331109 := bbase (se 4 (by rfl) ⟨874791, by rfl⟩ : syracuseStep 9331109 = 1749583) (by norm_num)
theorem B6220739 : Blo 2183435 6220739 := bstep (se 1 (by rfl) ⟨4665554, by rfl⟩ : syracuseStep 6220739 = 9331109) B9331109
theorem B16588637 : Blo 2183435 16588637 := bstep (se 3 (by rfl) ⟨3110369, by rfl⟩ : syracuseStep 16588637 = 6220739) B6220739
theorem B11059091 : Blo 2183435 11059091 := bstep (se 1 (by rfl) ⟨8294318, by rfl⟩ : syracuseStep 11059091 = 16588637) B16588637
theorem B7372727 : Blo 2183435 7372727 := bstep (se 1 (by rfl) ⟨5529545, by rfl⟩ : syracuseStep 7372727 = 11059091) B11059091
theorem B4915151 : Blo 2183435 4915151 := bstep (se 1 (by rfl) ⟨3686363, by rfl⟩ : syracuseStep 4915151 = 7372727) B7372727
theorem B3276767 : Blo 2183435 3276767 := bstep (se 1 (by rfl) ⟨2457575, by rfl⟩ : syracuseStep 3276767 = 4915151) B4915151
theorem B2184511 : Blo 2183435 2184511 := bstep (se 1 (by rfl) ⟨1638383, by rfl⟩ : syracuseStep 2184511 = 3276767) B3276767
theorem B3276773 : Blo 2183435 3276773 := bbase (se 4 (by rfl) ⟨307197, by rfl⟩ : syracuseStep 3276773 = 614395) (by norm_num)
theorem B2184515 : Blo 2183435 2184515 := bstep (se 1 (by rfl) ⟨1638386, by rfl⟩ : syracuseStep 2184515 = 3276773) B3276773
theorem B2214325 : Blo 2183435 2214325 := bbase (se 5 (by rfl) ⟨103796, by rfl⟩ : syracuseStep 2214325 = 207593) (by norm_num)
theorem B2952433 : Blo 2183435 2952433 := bstep (se 2 (by rfl) ⟨1107162, by rfl⟩ : syracuseStep 2952433 = 2214325) B2214325
theorem B15746309 : Blo 2183435 15746309 := bstep (se 4 (by rfl) ⟨1476216, by rfl⟩ : syracuseStep 15746309 = 2952433) B2952433
theorem B10497539 : Blo 2183435 10497539 := bstep (se 1 (by rfl) ⟨7873154, by rfl⟩ : syracuseStep 10497539 = 15746309) B15746309
theorem B6998359 : Blo 2183435 6998359 := bstep (se 1 (by rfl) ⟨5248769, by rfl⟩ : syracuseStep 6998359 = 10497539) B10497539
theorem B9331145 : Blo 2183435 9331145 := bstep (se 2 (by rfl) ⟨3499179, by rfl⟩ : syracuseStep 9331145 = 6998359) B6998359
theorem B6220763 : Blo 2183435 6220763 := bstep (se 1 (by rfl) ⟨4665572, by rfl⟩ : syracuseStep 6220763 = 9331145) B9331145
theorem B4147175 : Blo 2183435 4147175 := bstep (se 1 (by rfl) ⟨3110381, by rfl⟩ : syracuseStep 4147175 = 6220763) B6220763
theorem B2764783 : Blo 2183435 2764783 := bstep (se 1 (by rfl) ⟨2073587, by rfl⟩ : syracuseStep 2764783 = 4147175) B4147175
theorem B3686377 : Blo 2183435 3686377 := bstep (se 2 (by rfl) ⟨1382391, by rfl⟩ : syracuseStep 3686377 = 2764783) B2764783
theorem B4915169 : Blo 2183435 4915169 := bstep (se 2 (by rfl) ⟨1843188, by rfl⟩ : syracuseStep 4915169 = 3686377) B3686377
theorem B3276779 : Blo 2183435 3276779 := bstep (se 1 (by rfl) ⟨2457584, by rfl⟩ : syracuseStep 3276779 = 4915169) B4915169
theorem B2184519 : Blo 2183435 2184519 := bstep (se 1 (by rfl) ⟨1638389, by rfl⟩ : syracuseStep 2184519 = 3276779) B3276779
theorem B2457589 : Blo 2183435 2457589 := bbase (se 5 (by rfl) ⟨115199, by rfl⟩ : syracuseStep 2457589 = 230399) (by norm_num)
theorem B3276785 : Blo 2183435 3276785 := bstep (se 2 (by rfl) ⟨1228794, by rfl⟩ : syracuseStep 3276785 = 2457589) B2457589
theorem B2184523 : Blo 2183435 2184523 := bstep (se 1 (by rfl) ⟨1638392, by rfl⟩ : syracuseStep 2184523 = 3276785) B3276785
theorem B2764793 : Blo 2183435 2764793 := bbase (se 2 (by rfl) ⟨1036797, by rfl⟩ : syracuseStep 2764793 = 2073595) (by norm_num)
theorem B7372781 : Blo 2183435 7372781 := bstep (se 3 (by rfl) ⟨1382396, by rfl⟩ : syracuseStep 7372781 = 2764793) B2764793
theorem B4915187 : Blo 2183435 4915187 := bstep (se 1 (by rfl) ⟨3686390, by rfl⟩ : syracuseStep 4915187 = 7372781) B7372781
theorem B3276791 : Blo 2183435 3276791 := bstep (se 1 (by rfl) ⟨2457593, by rfl⟩ : syracuseStep 3276791 = 4915187) B4915187
theorem B2184527 : Blo 2183435 2184527 := bstep (se 1 (by rfl) ⟨1638395, by rfl⟩ : syracuseStep 2184527 = 3276791) B3276791
theorem B3276797 : Blo 2183435 3276797 := bbase (se 3 (by rfl) ⟨614399, by rfl⟩ : syracuseStep 3276797 = 1228799) (by norm_num)
theorem B2184531 : Blo 2183435 2184531 := bstep (se 1 (by rfl) ⟨1638398, by rfl⟩ : syracuseStep 2184531 = 3276797) B3276797
theorem B4915205 : Blo 2183435 4915205 := bbase (se 4 (by rfl) ⟨460800, by rfl⟩ : syracuseStep 4915205 = 921601) (by norm_num)
theorem B3276803 : Blo 2183435 3276803 := bstep (se 1 (by rfl) ⟨2457602, by rfl⟩ : syracuseStep 3276803 = 4915205) B4915205
theorem B2184535 : Blo 2183435 2184535 := bstep (se 1 (by rfl) ⟨1638401, by rfl⟩ : syracuseStep 2184535 = 3276803) B3276803
theorem B4147213 : Blo 2183435 4147213 := bbase (se 3 (by rfl) ⟨777602, by rfl⟩ : syracuseStep 4147213 = 1555205) (by norm_num)
theorem B5529617 : Blo 2183435 5529617 := bstep (se 2 (by rfl) ⟨2073606, by rfl⟩ : syracuseStep 5529617 = 4147213) B4147213
theorem B3686411 : Blo 2183435 3686411 := bstep (se 1 (by rfl) ⟨2764808, by rfl⟩ : syracuseStep 3686411 = 5529617) B5529617
theorem B2457607 : Blo 2183435 2457607 := bstep (se 1 (by rfl) ⟨1843205, by rfl⟩ : syracuseStep 2457607 = 3686411) B3686411
theorem B3276809 : Blo 2183435 3276809 := bstep (se 2 (by rfl) ⟨1228803, by rfl⟩ : syracuseStep 3276809 = 2457607) B2457607
theorem B2184539 : Blo 2183435 2184539 := bstep (se 1 (by rfl) ⟨1638404, by rfl⟩ : syracuseStep 2184539 = 3276809) B3276809
theorem B11059253 : Blo 2183435 11059253 := bbase (se 5 (by rfl) ⟨518402, by rfl⟩ : syracuseStep 11059253 = 1036805) (by norm_num)
theorem B7372835 : Blo 2183435 7372835 := bstep (se 1 (by rfl) ⟨5529626, by rfl⟩ : syracuseStep 7372835 = 11059253) B11059253
theorem B4915223 : Blo 2183435 4915223 := bstep (se 1 (by rfl) ⟨3686417, by rfl⟩ : syracuseStep 4915223 = 7372835) B7372835
theorem B3276815 : Blo 2183435 3276815 := bstep (se 1 (by rfl) ⟨2457611, by rfl⟩ : syracuseStep 3276815 = 4915223) B4915223
theorem B2184543 : Blo 2183435 2184543 := bstep (se 1 (by rfl) ⟨1638407, by rfl⟩ : syracuseStep 2184543 = 3276815) B3276815
theorem B3276821 : Blo 2183435 3276821 := bbase (se 6 (by rfl) ⟨76800, by rfl⟩ : syracuseStep 3276821 = 153601) (by norm_num)
theorem B2184547 : Blo 2183435 2184547 := bstep (se 1 (by rfl) ⟨1638410, by rfl⟩ : syracuseStep 2184547 = 3276821) B3276821
theorem B3787709 : Blo 2183435 3787709 := bbase (se 3 (by rfl) ⟨710195, by rfl⟩ : syracuseStep 3787709 = 1420391) (by norm_num)
theorem B10100557 : Blo 2183435 10100557 := bstep (se 3 (by rfl) ⟨1893854, by rfl⟩ : syracuseStep 10100557 = 3787709) B3787709
theorem B53869637 : Blo 2183435 53869637 := bstep (se 4 (by rfl) ⟨5050278, by rfl⟩ : syracuseStep 53869637 = 10100557) B10100557
theorem B143652365 : Blo 2183435 143652365 := bstep (se 3 (by rfl) ⟨26934818, by rfl⟩ : syracuseStep 143652365 = 53869637) B53869637
theorem B95768243 : Blo 2183435 95768243 := bstep (se 1 (by rfl) ⟨71826182, by rfl⟩ : syracuseStep 95768243 = 143652365) B143652365
theorem B63845495 : Blo 2183435 63845495 := bstep (se 1 (by rfl) ⟨47884121, by rfl⟩ : syracuseStep 63845495 = 95768243) B95768243
theorem B42563663 : Blo 2183435 42563663 := bstep (se 1 (by rfl) ⟨31922747, by rfl⟩ : syracuseStep 42563663 = 63845495) B63845495
theorem B28375775 : Blo 2183435 28375775 := bstep (se 1 (by rfl) ⟨21281831, by rfl⟩ : syracuseStep 28375775 = 42563663) B42563663
theorem B18917183 : Blo 2183435 18917183 := bstep (se 1 (by rfl) ⟨14187887, by rfl⟩ : syracuseStep 18917183 = 28375775) B28375775
theorem B50445821 : Blo 2183435 50445821 := bstep (se 3 (by rfl) ⟨9458591, by rfl⟩ : syracuseStep 50445821 = 18917183) B18917183
theorem B33630547 : Blo 2183435 33630547 := bstep (se 1 (by rfl) ⟨25222910, by rfl⟩ : syracuseStep 33630547 = 50445821) B50445821
theorem B44840729 : Blo 2183435 44840729 := bstep (se 2 (by rfl) ⟨16815273, by rfl⟩ : syracuseStep 44840729 = 33630547) B33630547
theorem B29893819 : Blo 2183435 29893819 := bstep (se 1 (by rfl) ⟨22420364, by rfl⟩ : syracuseStep 29893819 = 44840729) B44840729
theorem B39858425 : Blo 2183435 39858425 := bstep (se 2 (by rfl) ⟨14946909, by rfl⟩ : syracuseStep 39858425 = 29893819) B29893819
theorem B26572283 : Blo 2183435 26572283 := bstep (se 1 (by rfl) ⟨19929212, by rfl⟩ : syracuseStep 26572283 = 39858425) B39858425
theorem B17714855 : Blo 2183435 17714855 := bstep (se 1 (by rfl) ⟨13286141, by rfl⟩ : syracuseStep 17714855 = 26572283) B26572283
theorem B11809903 : Blo 2183435 11809903 := bstep (se 1 (by rfl) ⟨8857427, by rfl⟩ : syracuseStep 11809903 = 17714855) B17714855
theorem B15746537 : Blo 2183435 15746537 := bstep (se 2 (by rfl) ⟨5904951, by rfl⟩ : syracuseStep 15746537 = 11809903) B11809903
theorem B10497691 : Blo 2183435 10497691 := bstep (se 1 (by rfl) ⟨7873268, by rfl⟩ : syracuseStep 10497691 = 15746537) B15746537
theorem B13996921 : Blo 2183435 13996921 := bstep (se 2 (by rfl) ⟨5248845, by rfl⟩ : syracuseStep 13996921 = 10497691) B10497691
theorem B18662561 : Blo 2183435 18662561 := bstep (se 2 (by rfl) ⟨6998460, by rfl⟩ : syracuseStep 18662561 = 13996921) B13996921
theorem B12441707 : Blo 2183435 12441707 := bstep (se 1 (by rfl) ⟨9331280, by rfl⟩ : syracuseStep 12441707 = 18662561) B18662561
theorem B8294471 : Blo 2183435 8294471 := bstep (se 1 (by rfl) ⟨6220853, by rfl⟩ : syracuseStep 8294471 = 12441707) B12441707
theorem B5529647 : Blo 2183435 5529647 := bstep (se 1 (by rfl) ⟨4147235, by rfl⟩ : syracuseStep 5529647 = 8294471) B8294471
theorem B3686431 : Blo 2183435 3686431 := bstep (se 1 (by rfl) ⟨2764823, by rfl⟩ : syracuseStep 3686431 = 5529647) B5529647
theorem B4915241 : Blo 2183435 4915241 := bstep (se 2 (by rfl) ⟨1843215, by rfl⟩ : syracuseStep 4915241 = 3686431) B3686431
theorem B3276827 : Blo 2183435 3276827 := bstep (se 1 (by rfl) ⟨2457620, by rfl⟩ : syracuseStep 3276827 = 4915241) B4915241
theorem B2184551 : Blo 2183435 2184551 := bstep (se 1 (by rfl) ⟨1638413, by rfl⟩ : syracuseStep 2184551 = 3276827) B3276827
theorem B2457625 : Blo 2183435 2457625 := bbase (se 2 (by rfl) ⟨921609, by rfl⟩ : syracuseStep 2457625 = 1843219) (by norm_num)
theorem B3276833 : Blo 2183435 3276833 := bstep (se 2 (by rfl) ⟨1228812, by rfl⟩ : syracuseStep 3276833 = 2457625) B2457625
theorem B2184555 : Blo 2183435 2184555 := bstep (se 1 (by rfl) ⟨1638416, by rfl⟩ : syracuseStep 2184555 = 3276833) B3276833
theorem B8294501 : Blo 2183435 8294501 := bbase (se 4 (by rfl) ⟨777609, by rfl⟩ : syracuseStep 8294501 = 1555219) (by norm_num)
theorem B5529667 : Blo 2183435 5529667 := bstep (se 1 (by rfl) ⟨4147250, by rfl⟩ : syracuseStep 5529667 = 8294501) B8294501
theorem B7372889 : Blo 2183435 7372889 := bstep (se 2 (by rfl) ⟨2764833, by rfl⟩ : syracuseStep 7372889 = 5529667) B5529667
theorem B4915259 : Blo 2183435 4915259 := bstep (se 1 (by rfl) ⟨3686444, by rfl⟩ : syracuseStep 4915259 = 7372889) B7372889
theorem B3276839 : Blo 2183435 3276839 := bstep (se 1 (by rfl) ⟨2457629, by rfl⟩ : syracuseStep 3276839 = 4915259) B4915259
theorem B2184559 : Blo 2183435 2184559 := bstep (se 1 (by rfl) ⟨1638419, by rfl⟩ : syracuseStep 2184559 = 3276839) B3276839
theorem B3276845 : Blo 2183435 3276845 := bbase (se 3 (by rfl) ⟨614408, by rfl⟩ : syracuseStep 3276845 = 1228817) (by norm_num)
theorem B2184563 : Blo 2183435 2184563 := bstep (se 1 (by rfl) ⟨1638422, by rfl⟩ : syracuseStep 2184563 = 3276845) B3276845
theorem B4915277 : Blo 2183435 4915277 := bbase (se 3 (by rfl) ⟨921614, by rfl⟩ : syracuseStep 4915277 = 1843229) (by norm_num)
theorem B3276851 : Blo 2183435 3276851 := bstep (se 1 (by rfl) ⟨2457638, by rfl⟩ : syracuseStep 3276851 = 4915277) B4915277
theorem B2184567 : Blo 2183435 2184567 := bstep (se 1 (by rfl) ⟨1638425, by rfl⟩ : syracuseStep 2184567 = 3276851) B3276851
theorem B2764849 : Blo 2183435 2764849 := bbase (se 2 (by rfl) ⟨1036818, by rfl⟩ : syracuseStep 2764849 = 2073637) (by norm_num)
theorem B3686465 : Blo 2183435 3686465 := bstep (se 2 (by rfl) ⟨1382424, by rfl⟩ : syracuseStep 3686465 = 2764849) B2764849
theorem B2457643 : Blo 2183435 2457643 := bstep (se 1 (by rfl) ⟨1843232, by rfl⟩ : syracuseStep 2457643 = 3686465) B3686465
theorem B3276857 : Blo 2183435 3276857 := bstep (se 2 (by rfl) ⟨1228821, by rfl⟩ : syracuseStep 3276857 = 2457643) B2457643
theorem B2184571 : Blo 2183435 2184571 := bstep (se 1 (by rfl) ⟨1638428, by rfl⟩ : syracuseStep 2184571 = 3276857) B3276857
theorem B8857525 : Blo 2183435 8857525 := bbase (se 5 (by rfl) ⟨415196, by rfl⟩ : syracuseStep 8857525 = 830393) (by norm_num)
theorem B11810033 : Blo 2183435 11810033 := bstep (se 2 (by rfl) ⟨4428762, by rfl⟩ : syracuseStep 11810033 = 8857525) B8857525
theorem B7873355 : Blo 2183435 7873355 := bstep (se 1 (by rfl) ⟨5905016, by rfl⟩ : syracuseStep 7873355 = 11810033) B11810033
theorem B5248903 : Blo 2183435 5248903 := bstep (se 1 (by rfl) ⟨3936677, by rfl⟩ : syracuseStep 5248903 = 7873355) B7873355
theorem B6998537 : Blo 2183435 6998537 := bstep (se 2 (by rfl) ⟨2624451, by rfl⟩ : syracuseStep 6998537 = 5248903) B5248903
theorem B4665691 : Blo 2183435 4665691 := bstep (se 1 (by rfl) ⟨3499268, by rfl⟩ : syracuseStep 4665691 = 6998537) B6998537
theorem B24883685 : Blo 2183435 24883685 := bstep (se 4 (by rfl) ⟨2332845, by rfl⟩ : syracuseStep 24883685 = 4665691) B4665691
theorem B16589123 : Blo 2183435 16589123 := bstep (se 1 (by rfl) ⟨12441842, by rfl⟩ : syracuseStep 16589123 = 24883685) B24883685
theorem B11059415 : Blo 2183435 11059415 := bstep (se 1 (by rfl) ⟨8294561, by rfl⟩ : syracuseStep 11059415 = 16589123) B16589123
theorem B7372943 : Blo 2183435 7372943 := bstep (se 1 (by rfl) ⟨5529707, by rfl⟩ : syracuseStep 7372943 = 11059415) B11059415
theorem B4915295 : Blo 2183435 4915295 := bstep (se 1 (by rfl) ⟨3686471, by rfl⟩ : syracuseStep 4915295 = 7372943) B7372943
theorem B3276863 : Blo 2183435 3276863 := bstep (se 1 (by rfl) ⟨2457647, by rfl⟩ : syracuseStep 3276863 = 4915295) B4915295
theorem B2184575 : Blo 2183435 2184575 := bstep (se 1 (by rfl) ⟨1638431, by rfl⟩ : syracuseStep 2184575 = 3276863) B3276863
theorem B3276869 : Blo 2183435 3276869 := bbase (se 4 (by rfl) ⟨307206, by rfl⟩ : syracuseStep 3276869 = 614413) (by norm_num)
theorem B2184579 : Blo 2183435 2184579 := bstep (se 1 (by rfl) ⟨1638434, by rfl⟩ : syracuseStep 2184579 = 3276869) B3276869
theorem B3686485 : Blo 2183435 3686485 := bbase (se 8 (by rfl) ⟨21600, by rfl⟩ : syracuseStep 3686485 = 43201) (by norm_num)
theorem B4915313 : Blo 2183435 4915313 := bstep (se 2 (by rfl) ⟨1843242, by rfl⟩ : syracuseStep 4915313 = 3686485) B3686485
theorem B3276875 : Blo 2183435 3276875 := bstep (se 1 (by rfl) ⟨2457656, by rfl⟩ : syracuseStep 3276875 = 4915313) B4915313
theorem B2184583 : Blo 2183435 2184583 := bstep (se 1 (by rfl) ⟨1638437, by rfl⟩ : syracuseStep 2184583 = 3276875) B3276875
theorem B2457661 : Blo 2183435 2457661 := bbase (se 3 (by rfl) ⟨460811, by rfl⟩ : syracuseStep 2457661 = 921623) (by norm_num)
theorem B3276881 : Blo 2183435 3276881 := bstep (se 2 (by rfl) ⟨1228830, by rfl⟩ : syracuseStep 3276881 = 2457661) B2457661
theorem B2184587 : Blo 2183435 2184587 := bstep (se 1 (by rfl) ⟨1638440, by rfl⟩ : syracuseStep 2184587 = 3276881) B3276881
theorem B7372997 : Blo 2183435 7372997 := bbase (se 4 (by rfl) ⟨691218, by rfl⟩ : syracuseStep 7372997 = 1382437) (by norm_num)
theorem B4915331 : Blo 2183435 4915331 := bstep (se 1 (by rfl) ⟨3686498, by rfl⟩ : syracuseStep 4915331 = 7372997) B7372997
theorem B3276887 : Blo 2183435 3276887 := bstep (se 1 (by rfl) ⟨2457665, by rfl⟩ : syracuseStep 3276887 = 4915331) B4915331
theorem B2184591 : Blo 2183435 2184591 := bstep (se 1 (by rfl) ⟨1638443, by rfl⟩ : syracuseStep 2184591 = 3276887) B3276887
theorem B3276893 : Blo 2183435 3276893 := bbase (se 3 (by rfl) ⟨614417, by rfl⟩ : syracuseStep 3276893 = 1228835) (by norm_num)
theorem B2184595 : Blo 2183435 2184595 := bstep (se 1 (by rfl) ⟨1638446, by rfl⟩ : syracuseStep 2184595 = 3276893) B3276893
theorem B4915349 : Blo 2183435 4915349 := bbase (se 6 (by rfl) ⟨115203, by rfl⟩ : syracuseStep 4915349 = 230407) (by norm_num)
theorem B3276899 : Blo 2183435 3276899 := bstep (se 1 (by rfl) ⟨2457674, by rfl⟩ : syracuseStep 3276899 = 4915349) B4915349
theorem B2184599 : Blo 2183435 2184599 := bstep (se 1 (by rfl) ⟨1638449, by rfl⟩ : syracuseStep 2184599 = 3276899) B3276899
theorem B3110501 : Blo 2183435 3110501 := bbase (se 4 (by rfl) ⟨291609, by rfl⟩ : syracuseStep 3110501 = 583219) (by norm_num)
theorem B8294669 : Blo 2183435 8294669 := bstep (se 3 (by rfl) ⟨1555250, by rfl⟩ : syracuseStep 8294669 = 3110501) B3110501
theorem B5529779 : Blo 2183435 5529779 := bstep (se 1 (by rfl) ⟨4147334, by rfl⟩ : syracuseStep 5529779 = 8294669) B8294669
theorem B3686519 : Blo 2183435 3686519 := bstep (se 1 (by rfl) ⟨2764889, by rfl⟩ : syracuseStep 3686519 = 5529779) B5529779
theorem B2457679 : Blo 2183435 2457679 := bstep (se 1 (by rfl) ⟨1843259, by rfl⟩ : syracuseStep 2457679 = 3686519) B3686519
theorem B3276905 : Blo 2183435 3276905 := bstep (se 2 (by rfl) ⟨1228839, by rfl⟩ : syracuseStep 3276905 = 2457679) B2457679
theorem B2184603 : Blo 2183435 2184603 := bstep (se 1 (by rfl) ⟨1638452, by rfl⟩ : syracuseStep 2184603 = 3276905) B3276905
theorem B2660297 : Blo 2183435 2660297 := bbase (se 2 (by rfl) ⟨997611, by rfl⟩ : syracuseStep 2660297 = 1995223) (by norm_num)
theorem B7094125 : Blo 2183435 7094125 := bstep (se 3 (by rfl) ⟨1330148, by rfl⟩ : syracuseStep 7094125 = 2660297) B2660297
theorem B37835333 : Blo 2183435 37835333 := bstep (se 4 (by rfl) ⟨3547062, by rfl⟩ : syracuseStep 37835333 = 7094125) B7094125
theorem B25223555 : Blo 2183435 25223555 := bstep (se 1 (by rfl) ⟨18917666, by rfl⟩ : syracuseStep 25223555 = 37835333) B37835333
theorem B16815703 : Blo 2183435 16815703 := bstep (se 1 (by rfl) ⟨12611777, by rfl⟩ : syracuseStep 16815703 = 25223555) B25223555
theorem B22420937 : Blo 2183435 22420937 := bstep (se 2 (by rfl) ⟨8407851, by rfl⟩ : syracuseStep 22420937 = 16815703) B16815703
theorem B14947291 : Blo 2183435 14947291 := bstep (se 1 (by rfl) ⟨11210468, by rfl⟩ : syracuseStep 14947291 = 22420937) B22420937
theorem B19929721 : Blo 2183435 19929721 := bstep (se 2 (by rfl) ⟨7473645, by rfl⟩ : syracuseStep 19929721 = 14947291) B14947291
theorem B26572961 : Blo 2183435 26572961 := bstep (se 2 (by rfl) ⟨9964860, by rfl⟩ : syracuseStep 26572961 = 19929721) B19929721
theorem B70861229 : Blo 2183435 70861229 := bstep (se 3 (by rfl) ⟨13286480, by rfl⟩ : syracuseStep 70861229 = 26572961) B26572961
theorem B47240819 : Blo 2183435 47240819 := bstep (se 1 (by rfl) ⟨35430614, by rfl⟩ : syracuseStep 47240819 = 70861229) B70861229
theorem B31493879 : Blo 2183435 31493879 := bstep (se 1 (by rfl) ⟨23620409, by rfl⟩ : syracuseStep 31493879 = 47240819) B47240819
theorem B20995919 : Blo 2183435 20995919 := bstep (se 1 (by rfl) ⟨15746939, by rfl⟩ : syracuseStep 20995919 = 31493879) B31493879
theorem B13997279 : Blo 2183435 13997279 := bstep (se 1 (by rfl) ⟨10497959, by rfl⟩ : syracuseStep 13997279 = 20995919) B20995919
theorem B9331519 : Blo 2183435 9331519 := bstep (se 1 (by rfl) ⟨6998639, by rfl⟩ : syracuseStep 9331519 = 13997279) B13997279
theorem B12442025 : Blo 2183435 12442025 := bstep (se 2 (by rfl) ⟨4665759, by rfl⟩ : syracuseStep 12442025 = 9331519) B9331519
theorem B8294683 : Blo 2183435 8294683 := bstep (se 1 (by rfl) ⟨6221012, by rfl⟩ : syracuseStep 8294683 = 12442025) B12442025
theorem B11059577 : Blo 2183435 11059577 := bstep (se 2 (by rfl) ⟨4147341, by rfl⟩ : syracuseStep 11059577 = 8294683) B8294683
theorem B7373051 : Blo 2183435 7373051 := bstep (se 1 (by rfl) ⟨5529788, by rfl⟩ : syracuseStep 7373051 = 11059577) B11059577
theorem B4915367 : Blo 2183435 4915367 := bstep (se 1 (by rfl) ⟨3686525, by rfl⟩ : syracuseStep 4915367 = 7373051) B7373051
theorem B3276911 : Blo 2183435 3276911 := bstep (se 1 (by rfl) ⟨2457683, by rfl⟩ : syracuseStep 3276911 = 4915367) B4915367
theorem B2184607 : Blo 2183435 2184607 := bstep (se 1 (by rfl) ⟨1638455, by rfl⟩ : syracuseStep 2184607 = 3276911) B3276911
theorem B3276917 : Blo 2183435 3276917 := bbase (se 5 (by rfl) ⟨153605, by rfl⟩ : syracuseStep 3276917 = 307211) (by norm_num)
theorem B2184611 : Blo 2183435 2184611 := bstep (se 1 (by rfl) ⟨1638458, by rfl⟩ : syracuseStep 2184611 = 3276917) B3276917
theorem B4147357 : Blo 2183435 4147357 := bbase (se 3 (by rfl) ⟨777629, by rfl⟩ : syracuseStep 4147357 = 1555259) (by norm_num)
theorem B5529809 : Blo 2183435 5529809 := bstep (se 2 (by rfl) ⟨2073678, by rfl⟩ : syracuseStep 5529809 = 4147357) B4147357
theorem B3686539 : Blo 2183435 3686539 := bstep (se 1 (by rfl) ⟨2764904, by rfl⟩ : syracuseStep 3686539 = 5529809) B5529809
theorem B4915385 : Blo 2183435 4915385 := bstep (se 2 (by rfl) ⟨1843269, by rfl⟩ : syracuseStep 4915385 = 3686539) B3686539
theorem B3276923 : Blo 2183435 3276923 := bstep (se 1 (by rfl) ⟨2457692, by rfl⟩ : syracuseStep 3276923 = 4915385) B4915385
theorem B2184615 : Blo 2183435 2184615 := bstep (se 1 (by rfl) ⟨1638461, by rfl⟩ : syracuseStep 2184615 = 3276923) B3276923
theorem B2457697 : Blo 2183435 2457697 := bbase (se 2 (by rfl) ⟨921636, by rfl⟩ : syracuseStep 2457697 = 1843273) (by norm_num)
theorem B3276929 : Blo 2183435 3276929 := bstep (se 2 (by rfl) ⟨1228848, by rfl⟩ : syracuseStep 3276929 = 2457697) B2457697
theorem B2184619 : Blo 2183435 2184619 := bstep (se 1 (by rfl) ⟨1638464, by rfl⟩ : syracuseStep 2184619 = 3276929) B3276929
theorem B5529829 : Blo 2183435 5529829 := bbase (se 4 (by rfl) ⟨518421, by rfl⟩ : syracuseStep 5529829 = 1036843) (by norm_num)
theorem B7373105 : Blo 2183435 7373105 := bstep (se 2 (by rfl) ⟨2764914, by rfl⟩ : syracuseStep 7373105 = 5529829) B5529829
theorem B4915403 : Blo 2183435 4915403 := bstep (se 1 (by rfl) ⟨3686552, by rfl⟩ : syracuseStep 4915403 = 7373105) B7373105
theorem B3276935 : Blo 2183435 3276935 := bstep (se 1 (by rfl) ⟨2457701, by rfl⟩ : syracuseStep 3276935 = 4915403) B4915403
theorem B2184623 : Blo 2183435 2184623 := bstep (se 1 (by rfl) ⟨1638467, by rfl⟩ : syracuseStep 2184623 = 3276935) B3276935
theorem B3276941 : Blo 2183435 3276941 := bbase (se 3 (by rfl) ⟨614426, by rfl⟩ : syracuseStep 3276941 = 1228853) (by norm_num)
theorem B2184627 : Blo 2183435 2184627 := bstep (se 1 (by rfl) ⟨1638470, by rfl⟩ : syracuseStep 2184627 = 3276941) B3276941
theorem B4915421 : Blo 2183435 4915421 := bbase (se 3 (by rfl) ⟨921641, by rfl⟩ : syracuseStep 4915421 = 1843283) (by norm_num)
theorem B3276947 : Blo 2183435 3276947 := bstep (se 1 (by rfl) ⟨2457710, by rfl⟩ : syracuseStep 3276947 = 4915421) B4915421
theorem B2184631 : Blo 2183435 2184631 := bstep (se 1 (by rfl) ⟨1638473, by rfl⟩ : syracuseStep 2184631 = 3276947) B3276947
theorem B3686573 : Blo 2183435 3686573 := bbase (se 3 (by rfl) ⟨691232, by rfl⟩ : syracuseStep 3686573 = 1382465) (by norm_num)
theorem B2457715 : Blo 2183435 2457715 := bstep (se 1 (by rfl) ⟨1843286, by rfl⟩ : syracuseStep 2457715 = 3686573) B3686573
theorem B3276953 : Blo 2183435 3276953 := bstep (se 2 (by rfl) ⟨1228857, by rfl⟩ : syracuseStep 3276953 = 2457715) B2457715
theorem B2184635 : Blo 2183435 2184635 := bstep (se 1 (by rfl) ⟨1638476, by rfl⟩ : syracuseStep 2184635 = 3276953) B3276953
theorem B10100965 : Blo 2183435 10100965 := bbase (se 4 (by rfl) ⟨946965, by rfl⟩ : syracuseStep 10100965 = 1893931) (by norm_num)
theorem B13467953 : Blo 2183435 13467953 := bstep (se 2 (by rfl) ⟨5050482, by rfl⟩ : syracuseStep 13467953 = 10100965) B10100965
theorem B8978635 : Blo 2183435 8978635 := bstep (se 1 (by rfl) ⟨6733976, by rfl⟩ : syracuseStep 8978635 = 13467953) B13467953
theorem B11971513 : Blo 2183435 11971513 := bstep (se 2 (by rfl) ⟨4489317, by rfl⟩ : syracuseStep 11971513 = 8978635) B8978635
theorem B15962017 : Blo 2183435 15962017 := bstep (se 2 (by rfl) ⟨5985756, by rfl⟩ : syracuseStep 15962017 = 11971513) B11971513
theorem B21282689 : Blo 2183435 21282689 := bstep (se 2 (by rfl) ⟨7981008, by rfl⟩ : syracuseStep 21282689 = 15962017) B15962017
theorem B14188459 : Blo 2183435 14188459 := bstep (se 1 (by rfl) ⟨10641344, by rfl⟩ : syracuseStep 14188459 = 21282689) B21282689
theorem B18917945 : Blo 2183435 18917945 := bstep (se 2 (by rfl) ⟨7094229, by rfl⟩ : syracuseStep 18917945 = 14188459) B14188459
theorem B12611963 : Blo 2183435 12611963 := bstep (se 1 (by rfl) ⟨9458972, by rfl⟩ : syracuseStep 12611963 = 18917945) B18917945
theorem B8407975 : Blo 2183435 8407975 := bstep (se 1 (by rfl) ⟨6305981, by rfl⟩ : syracuseStep 8407975 = 12611963) B12611963
theorem B11210633 : Blo 2183435 11210633 := bstep (se 2 (by rfl) ⟨4203987, by rfl⟩ : syracuseStep 11210633 = 8407975) B8407975
theorem B7473755 : Blo 2183435 7473755 := bstep (se 1 (by rfl) ⟨5605316, by rfl⟩ : syracuseStep 7473755 = 11210633) B11210633
theorem B19930013 : Blo 2183435 19930013 := bstep (se 3 (by rfl) ⟨3736877, by rfl⟩ : syracuseStep 19930013 = 7473755) B7473755
theorem B13286675 : Blo 2183435 13286675 := bstep (se 1 (by rfl) ⟨9965006, by rfl⟩ : syracuseStep 13286675 = 19930013) B19930013
theorem B8857783 : Blo 2183435 8857783 := bstep (se 1 (by rfl) ⟨6643337, by rfl⟩ : syracuseStep 8857783 = 13286675) B13286675
theorem B11810377 : Blo 2183435 11810377 := bstep (se 2 (by rfl) ⟨4428891, by rfl⟩ : syracuseStep 11810377 = 8857783) B8857783
theorem B62988677 : Blo 2183435 62988677 := bstep (se 4 (by rfl) ⟨5905188, by rfl⟩ : syracuseStep 62988677 = 11810377) B11810377
theorem B41992451 : Blo 2183435 41992451 := bstep (se 1 (by rfl) ⟨31494338, by rfl⟩ : syracuseStep 41992451 = 62988677) B62988677
theorem B27994967 : Blo 2183435 27994967 := bstep (se 1 (by rfl) ⟨20996225, by rfl⟩ : syracuseStep 27994967 = 41992451) B41992451
theorem B18663311 : Blo 2183435 18663311 := bstep (se 1 (by rfl) ⟨13997483, by rfl⟩ : syracuseStep 18663311 = 27994967) B27994967
theorem B12442207 : Blo 2183435 12442207 := bstep (se 1 (by rfl) ⟨9331655, by rfl⟩ : syracuseStep 12442207 = 18663311) B18663311
theorem B16589609 : Blo 2183435 16589609 := bstep (se 2 (by rfl) ⟨6221103, by rfl⟩ : syracuseStep 16589609 = 12442207) B12442207
theorem B11059739 : Blo 2183435 11059739 := bstep (se 1 (by rfl) ⟨8294804, by rfl⟩ : syracuseStep 11059739 = 16589609) B16589609
theorem B7373159 : Blo 2183435 7373159 := bstep (se 1 (by rfl) ⟨5529869, by rfl⟩ : syracuseStep 7373159 = 11059739) B11059739
theorem B4915439 : Blo 2183435 4915439 := bstep (se 1 (by rfl) ⟨3686579, by rfl⟩ : syracuseStep 4915439 = 7373159) B7373159
theorem B3276959 : Blo 2183435 3276959 := bstep (se 1 (by rfl) ⟨2457719, by rfl⟩ : syracuseStep 3276959 = 4915439) B4915439
theorem B2184639 : Blo 2183435 2184639 := bstep (se 1 (by rfl) ⟨1638479, by rfl⟩ : syracuseStep 2184639 = 3276959) B3276959
theorem B3276965 : Blo 2183435 3276965 := bbase (se 4 (by rfl) ⟨307215, by rfl⟩ : syracuseStep 3276965 = 614431) (by norm_num)
theorem B2184643 : Blo 2183435 2184643 := bstep (se 1 (by rfl) ⟨1638482, by rfl⟩ : syracuseStep 2184643 = 3276965) B3276965
theorem B2764945 : Blo 2183435 2764945 := bbase (se 2 (by rfl) ⟨1036854, by rfl⟩ : syracuseStep 2764945 = 2073709) (by norm_num)
theorem B3686593 : Blo 2183435 3686593 := bstep (se 2 (by rfl) ⟨1382472, by rfl⟩ : syracuseStep 3686593 = 2764945) B2764945
theorem B4915457 : Blo 2183435 4915457 := bstep (se 2 (by rfl) ⟨1843296, by rfl⟩ : syracuseStep 4915457 = 3686593) B3686593
theorem B3276971 : Blo 2183435 3276971 := bstep (se 1 (by rfl) ⟨2457728, by rfl⟩ : syracuseStep 3276971 = 4915457) B4915457
theorem B2184647 : Blo 2183435 2184647 := bstep (se 1 (by rfl) ⟨1638485, by rfl⟩ : syracuseStep 2184647 = 3276971) B3276971
theorem B2457733 : Blo 2183435 2457733 := bbase (se 4 (by rfl) ⟨230412, by rfl⟩ : syracuseStep 2457733 = 460825) (by norm_num)
theorem B3276977 : Blo 2183435 3276977 := bstep (se 2 (by rfl) ⟨1228866, by rfl⟩ : syracuseStep 3276977 = 2457733) B2457733
theorem B2184651 : Blo 2183435 2184651 := bstep (se 1 (by rfl) ⟨1638488, by rfl⟩ : syracuseStep 2184651 = 3276977) B3276977
theorem B16816085 : Blo 2183435 16816085 := bbase (se 7 (by rfl) ⟨197063, by rfl⟩ : syracuseStep 16816085 = 394127) (by norm_num)
theorem B11210723 : Blo 2183435 11210723 := bstep (se 1 (by rfl) ⟨8408042, by rfl⟩ : syracuseStep 11210723 = 16816085) B16816085
theorem B7473815 : Blo 2183435 7473815 := bstep (se 1 (by rfl) ⟨5605361, by rfl⟩ : syracuseStep 7473815 = 11210723) B11210723
theorem B4982543 : Blo 2183435 4982543 := bstep (se 1 (by rfl) ⟨3736907, by rfl⟩ : syracuseStep 4982543 = 7473815) B7473815
theorem B3321695 : Blo 2183435 3321695 := bstep (se 1 (by rfl) ⟨2491271, by rfl⟩ : syracuseStep 3321695 = 4982543) B4982543
theorem B2214463 : Blo 2183435 2214463 := bstep (se 1 (by rfl) ⟨1660847, by rfl⟩ : syracuseStep 2214463 = 3321695) B3321695
theorem B2952617 : Blo 2183435 2952617 := bstep (se 2 (by rfl) ⟨1107231, by rfl⟩ : syracuseStep 2952617 = 2214463) B2214463
theorem B7873645 : Blo 2183435 7873645 := bstep (se 3 (by rfl) ⟨1476308, by rfl⟩ : syracuseStep 7873645 = 2952617) B2952617
theorem B10498193 : Blo 2183435 10498193 := bstep (se 2 (by rfl) ⟨3936822, by rfl⟩ : syracuseStep 10498193 = 7873645) B7873645
theorem B6998795 : Blo 2183435 6998795 := bstep (se 1 (by rfl) ⟨5249096, by rfl⟩ : syracuseStep 6998795 = 10498193) B10498193
theorem B4665863 : Blo 2183435 4665863 := bstep (se 1 (by rfl) ⟨3499397, by rfl⟩ : syracuseStep 4665863 = 6998795) B6998795
theorem B3110575 : Blo 2183435 3110575 := bstep (se 1 (by rfl) ⟨2332931, by rfl⟩ : syracuseStep 3110575 = 4665863) B4665863
theorem B4147433 : Blo 2183435 4147433 := bstep (se 2 (by rfl) ⟨1555287, by rfl⟩ : syracuseStep 4147433 = 3110575) B3110575
theorem B2764955 : Blo 2183435 2764955 := bstep (se 1 (by rfl) ⟨2073716, by rfl⟩ : syracuseStep 2764955 = 4147433) B4147433
theorem B7373213 : Blo 2183435 7373213 := bstep (se 3 (by rfl) ⟨1382477, by rfl⟩ : syracuseStep 7373213 = 2764955) B2764955
theorem B4915475 : Blo 2183435 4915475 := bstep (se 1 (by rfl) ⟨3686606, by rfl⟩ : syracuseStep 4915475 = 7373213) B7373213
theorem B3276983 : Blo 2183435 3276983 := bstep (se 1 (by rfl) ⟨2457737, by rfl⟩ : syracuseStep 3276983 = 4915475) B4915475
theorem B2184655 : Blo 2183435 2184655 := bstep (se 1 (by rfl) ⟨1638491, by rfl⟩ : syracuseStep 2184655 = 3276983) B3276983
theorem B3276989 : Blo 2183435 3276989 := bbase (se 3 (by rfl) ⟨614435, by rfl⟩ : syracuseStep 3276989 = 1228871) (by norm_num)
theorem B2184659 : Blo 2183435 2184659 := bstep (se 1 (by rfl) ⟨1638494, by rfl⟩ : syracuseStep 2184659 = 3276989) B3276989
theorem B4915493 : Blo 2183435 4915493 := bbase (se 4 (by rfl) ⟨460827, by rfl⟩ : syracuseStep 4915493 = 921655) (by norm_num)
theorem B3276995 : Blo 2183435 3276995 := bstep (se 1 (by rfl) ⟨2457746, by rfl⟩ : syracuseStep 3276995 = 4915493) B4915493
theorem B2184663 : Blo 2183435 2184663 := bstep (se 1 (by rfl) ⟨1638497, by rfl⟩ : syracuseStep 2184663 = 3276995) B3276995
theorem B5529941 : Blo 2183435 5529941 := bbase (se 10 (by rfl) ⟨8100, by rfl⟩ : syracuseStep 5529941 = 16201) (by norm_num)
theorem B3686627 : Blo 2183435 3686627 := bstep (se 1 (by rfl) ⟨2764970, by rfl⟩ : syracuseStep 3686627 = 5529941) B5529941
theorem B2457751 : Blo 2183435 2457751 := bstep (se 1 (by rfl) ⟨1843313, by rfl⟩ : syracuseStep 2457751 = 3686627) B3686627
theorem B3277001 : Blo 2183435 3277001 := bstep (se 2 (by rfl) ⟨1228875, by rfl⟩ : syracuseStep 3277001 = 2457751) B2457751
theorem B2184667 : Blo 2183435 2184667 := bstep (se 1 (by rfl) ⟨1638500, by rfl⟩ : syracuseStep 2184667 = 3277001) B3277001
theorem B2802701 : Blo 2183435 2802701 := bbase (se 3 (by rfl) ⟨525506, by rfl⟩ : syracuseStep 2802701 = 1051013) (by norm_num)
theorem B7473869 : Blo 2183435 7473869 := bstep (se 3 (by rfl) ⟨1401350, by rfl⟩ : syracuseStep 7473869 = 2802701) B2802701
theorem B4982579 : Blo 2183435 4982579 := bstep (se 1 (by rfl) ⟨3736934, by rfl⟩ : syracuseStep 4982579 = 7473869) B7473869
theorem B3321719 : Blo 2183435 3321719 := bstep (se 1 (by rfl) ⟨2491289, by rfl⟩ : syracuseStep 3321719 = 4982579) B4982579
theorem B2214479 : Blo 2183435 2214479 := bstep (se 1 (by rfl) ⟨1660859, by rfl⟩ : syracuseStep 2214479 = 3321719) B3321719
theorem B5905277 : Blo 2183435 5905277 := bstep (se 3 (by rfl) ⟨1107239, by rfl⟩ : syracuseStep 5905277 = 2214479) B2214479
theorem B3936851 : Blo 2183435 3936851 := bstep (se 1 (by rfl) ⟨2952638, by rfl⟩ : syracuseStep 3936851 = 5905277) B5905277
theorem B2624567 : Blo 2183435 2624567 := bstep (se 1 (by rfl) ⟨1968425, by rfl⟩ : syracuseStep 2624567 = 3936851) B3936851
theorem B6998845 : Blo 2183435 6998845 := bstep (se 3 (by rfl) ⟨1312283, by rfl⟩ : syracuseStep 6998845 = 2624567) B2624567
theorem B9331793 : Blo 2183435 9331793 := bstep (se 2 (by rfl) ⟨3499422, by rfl⟩ : syracuseStep 9331793 = 6998845) B6998845
theorem B6221195 : Blo 2183435 6221195 := bstep (se 1 (by rfl) ⟨4665896, by rfl⟩ : syracuseStep 6221195 = 9331793) B9331793
theorem B4147463 : Blo 2183435 4147463 := bstep (se 1 (by rfl) ⟨3110597, by rfl⟩ : syracuseStep 4147463 = 6221195) B6221195
theorem B11059901 : Blo 2183435 11059901 := bstep (se 3 (by rfl) ⟨2073731, by rfl⟩ : syracuseStep 11059901 = 4147463) B4147463
theorem B7373267 : Blo 2183435 7373267 := bstep (se 1 (by rfl) ⟨5529950, by rfl⟩ : syracuseStep 7373267 = 11059901) B11059901
theorem B4915511 : Blo 2183435 4915511 := bstep (se 1 (by rfl) ⟨3686633, by rfl⟩ : syracuseStep 4915511 = 7373267) B7373267
theorem B3277007 : Blo 2183435 3277007 := bstep (se 1 (by rfl) ⟨2457755, by rfl⟩ : syracuseStep 3277007 = 4915511) B4915511
theorem B2184671 : Blo 2183435 2184671 := bstep (se 1 (by rfl) ⟨1638503, by rfl⟩ : syracuseStep 2184671 = 3277007) B3277007
theorem B3277013 : Blo 2183435 3277013 := bbase (se 7 (by rfl) ⟨38402, by rfl⟩ : syracuseStep 3277013 = 76805) (by norm_num)
theorem B2184675 : Blo 2183435 2184675 := bstep (se 1 (by rfl) ⟨1638506, by rfl⟩ : syracuseStep 2184675 = 3277013) B3277013
theorem B2332957 : Blo 2183435 2332957 := bbase (se 3 (by rfl) ⟨437429, by rfl⟩ : syracuseStep 2332957 = 874859) (by norm_num)
theorem B3110609 : Blo 2183435 3110609 := bstep (se 2 (by rfl) ⟨1166478, by rfl⟩ : syracuseStep 3110609 = 2332957) B2332957
theorem B8294957 : Blo 2183435 8294957 := bstep (se 3 (by rfl) ⟨1555304, by rfl⟩ : syracuseStep 8294957 = 3110609) B3110609
theorem B5529971 : Blo 2183435 5529971 := bstep (se 1 (by rfl) ⟨4147478, by rfl⟩ : syracuseStep 5529971 = 8294957) B8294957
theorem B3686647 : Blo 2183435 3686647 := bstep (se 1 (by rfl) ⟨2764985, by rfl⟩ : syracuseStep 3686647 = 5529971) B5529971
theorem B4915529 : Blo 2183435 4915529 := bstep (se 2 (by rfl) ⟨1843323, by rfl⟩ : syracuseStep 4915529 = 3686647) B3686647
theorem B3277019 : Blo 2183435 3277019 := bstep (se 1 (by rfl) ⟨2457764, by rfl⟩ : syracuseStep 3277019 = 4915529) B4915529
theorem B2184679 : Blo 2183435 2184679 := bstep (se 1 (by rfl) ⟨1638509, by rfl⟩ : syracuseStep 2184679 = 3277019) B3277019
theorem B2457769 : Blo 2183435 2457769 := bbase (se 2 (by rfl) ⟨921663, by rfl⟩ : syracuseStep 2457769 = 1843327) (by norm_num)
theorem B3277025 : Blo 2183435 3277025 := bstep (se 2 (by rfl) ⟨1228884, by rfl⟩ : syracuseStep 3277025 = 2457769) B2457769
theorem B2184683 : Blo 2183435 2184683 := bstep (se 1 (by rfl) ⟨1638512, by rfl⟩ : syracuseStep 2184683 = 3277025) B3277025
theorem B9331861 : Blo 2183435 9331861 := bbase (se 6 (by rfl) ⟨218715, by rfl⟩ : syracuseStep 9331861 = 437431) (by norm_num)
theorem B12442481 : Blo 2183435 12442481 := bstep (se 2 (by rfl) ⟨4665930, by rfl⟩ : syracuseStep 12442481 = 9331861) B9331861
theorem B8294987 : Blo 2183435 8294987 := bstep (se 1 (by rfl) ⟨6221240, by rfl⟩ : syracuseStep 8294987 = 12442481) B12442481
theorem B5529991 : Blo 2183435 5529991 := bstep (se 1 (by rfl) ⟨4147493, by rfl⟩ : syracuseStep 5529991 = 8294987) B8294987
theorem B7373321 : Blo 2183435 7373321 := bstep (se 2 (by rfl) ⟨2764995, by rfl⟩ : syracuseStep 7373321 = 5529991) B5529991
theorem B4915547 : Blo 2183435 4915547 := bstep (se 1 (by rfl) ⟨3686660, by rfl⟩ : syracuseStep 4915547 = 7373321) B7373321
theorem B3277031 : Blo 2183435 3277031 := bstep (se 1 (by rfl) ⟨2457773, by rfl⟩ : syracuseStep 3277031 = 4915547) B4915547
theorem B2184687 : Blo 2183435 2184687 := bstep (se 1 (by rfl) ⟨1638515, by rfl⟩ : syracuseStep 2184687 = 3277031) B3277031
theorem B3277037 : Blo 2183435 3277037 := bbase (se 3 (by rfl) ⟨614444, by rfl⟩ : syracuseStep 3277037 = 1228889) (by norm_num)
theorem B2184691 : Blo 2183435 2184691 := bstep (se 1 (by rfl) ⟨1638518, by rfl⟩ : syracuseStep 2184691 = 3277037) B3277037
theorem B4915565 : Blo 2183435 4915565 := bbase (se 3 (by rfl) ⟨921668, by rfl⟩ : syracuseStep 4915565 = 1843337) (by norm_num)
theorem B3277043 : Blo 2183435 3277043 := bstep (se 1 (by rfl) ⟨2457782, by rfl⟩ : syracuseStep 3277043 = 4915565) B4915565
theorem B2184695 : Blo 2183435 2184695 := bstep (se 1 (by rfl) ⟨1638521, by rfl⟩ : syracuseStep 2184695 = 3277043) B3277043
theorem B4147517 : Blo 2183435 4147517 := bbase (se 3 (by rfl) ⟨777659, by rfl⟩ : syracuseStep 4147517 = 1555319) (by norm_num)
theorem B2765011 : Blo 2183435 2765011 := bstep (se 1 (by rfl) ⟨2073758, by rfl⟩ : syracuseStep 2765011 = 4147517) B4147517
theorem B3686681 : Blo 2183435 3686681 := bstep (se 2 (by rfl) ⟨1382505, by rfl⟩ : syracuseStep 3686681 = 2765011) B2765011
theorem B2457787 : Blo 2183435 2457787 := bstep (se 1 (by rfl) ⟨1843340, by rfl⟩ : syracuseStep 2457787 = 3686681) B3686681
theorem B3277049 : Blo 2183435 3277049 := bstep (se 2 (by rfl) ⟨1228893, by rfl⟩ : syracuseStep 3277049 = 2457787) B2457787
theorem B2184699 : Blo 2183435 2184699 := bstep (se 1 (by rfl) ⟨1638524, by rfl⟩ : syracuseStep 2184699 = 3277049) B3277049
theorem B2624605 : Blo 2183435 2624605 := bbase (se 3 (by rfl) ⟨492113, by rfl⟩ : syracuseStep 2624605 = 984227) (by norm_num)
theorem B55991573 : Blo 2183435 55991573 := bstep (se 6 (by rfl) ⟨1312302, by rfl⟩ : syracuseStep 55991573 = 2624605) B2624605
theorem B37327715 : Blo 2183435 37327715 := bstep (se 1 (by rfl) ⟨27995786, by rfl⟩ : syracuseStep 37327715 = 55991573) B55991573
theorem B24885143 : Blo 2183435 24885143 := bstep (se 1 (by rfl) ⟨18663857, by rfl⟩ : syracuseStep 24885143 = 37327715) B37327715
theorem B16590095 : Blo 2183435 16590095 := bstep (se 1 (by rfl) ⟨12442571, by rfl⟩ : syracuseStep 16590095 = 24885143) B24885143
theorem B11060063 : Blo 2183435 11060063 := bstep (se 1 (by rfl) ⟨8295047, by rfl⟩ : syracuseStep 11060063 = 16590095) B16590095
theorem B7373375 : Blo 2183435 7373375 := bstep (se 1 (by rfl) ⟨5530031, by rfl⟩ : syracuseStep 7373375 = 11060063) B11060063
theorem B4915583 : Blo 2183435 4915583 := bstep (se 1 (by rfl) ⟨3686687, by rfl⟩ : syracuseStep 4915583 = 7373375) B7373375
theorem B3277055 : Blo 2183435 3277055 := bstep (se 1 (by rfl) ⟨2457791, by rfl⟩ : syracuseStep 3277055 = 4915583) B4915583
theorem B2184703 : Blo 2183435 2184703 := bstep (se 1 (by rfl) ⟨1638527, by rfl⟩ : syracuseStep 2184703 = 3277055) B3277055
theorem B3277061 : Blo 2183435 3277061 := bbase (se 4 (by rfl) ⟨307224, by rfl⟩ : syracuseStep 3277061 = 614449) (by norm_num)
theorem B2184707 : Blo 2183435 2184707 := bstep (se 1 (by rfl) ⟨1638530, by rfl⟩ : syracuseStep 2184707 = 3277061) B3277061
theorem B3686701 : Blo 2183435 3686701 := bbase (se 3 (by rfl) ⟨691256, by rfl⟩ : syracuseStep 3686701 = 1382513) (by norm_num)
theorem B4915601 : Blo 2183435 4915601 := bstep (se 2 (by rfl) ⟨1843350, by rfl⟩ : syracuseStep 4915601 = 3686701) B3686701
theorem B3277067 : Blo 2183435 3277067 := bstep (se 1 (by rfl) ⟨2457800, by rfl⟩ : syracuseStep 3277067 = 4915601) B4915601
theorem B2184711 : Blo 2183435 2184711 := bstep (se 1 (by rfl) ⟨1638533, by rfl⟩ : syracuseStep 2184711 = 3277067) B3277067
theorem B2457805 : Blo 2183435 2457805 := bbase (se 3 (by rfl) ⟨460838, by rfl⟩ : syracuseStep 2457805 = 921677) (by norm_num)
theorem B3277073 : Blo 2183435 3277073 := bstep (se 2 (by rfl) ⟨1228902, by rfl⟩ : syracuseStep 3277073 = 2457805) B2457805
theorem B2184715 : Blo 2183435 2184715 := bstep (se 1 (by rfl) ⟨1638536, by rfl⟩ : syracuseStep 2184715 = 3277073) B3277073
theorem B7373429 : Blo 2183435 7373429 := bbase (se 5 (by rfl) ⟨345629, by rfl⟩ : syracuseStep 7373429 = 691259) (by norm_num)
theorem B4915619 : Blo 2183435 4915619 := bstep (se 1 (by rfl) ⟨3686714, by rfl⟩ : syracuseStep 4915619 = 7373429) B7373429
theorem B3277079 : Blo 2183435 3277079 := bstep (se 1 (by rfl) ⟨2457809, by rfl⟩ : syracuseStep 3277079 = 4915619) B4915619
theorem B2184719 : Blo 2183435 2184719 := bstep (se 1 (by rfl) ⟨1638539, by rfl⟩ : syracuseStep 2184719 = 3277079) B3277079
theorem B3277085 : Blo 2183435 3277085 := bbase (se 3 (by rfl) ⟨614453, by rfl⟩ : syracuseStep 3277085 = 1228907) (by norm_num)
theorem B2184723 : Blo 2183435 2184723 := bstep (se 1 (by rfl) ⟨1638542, by rfl⟩ : syracuseStep 2184723 = 3277085) B3277085
theorem B4915637 : Blo 2183435 4915637 := bbase (se 5 (by rfl) ⟨230420, by rfl⟩ : syracuseStep 4915637 = 460841) (by norm_num)
theorem B3277091 : Blo 2183435 3277091 := bstep (se 1 (by rfl) ⟨2457818, by rfl⟩ : syracuseStep 3277091 = 4915637) B4915637
theorem B2184727 : Blo 2183435 2184727 := bstep (se 1 (by rfl) ⟨1638545, by rfl⟩ : syracuseStep 2184727 = 3277091) B3277091
theorem B2660449 : Blo 2183435 2660449 := bbase (se 2 (by rfl) ⟨997668, by rfl⟩ : syracuseStep 2660449 = 1995337) (by norm_num)
theorem B3547265 : Blo 2183435 3547265 := bstep (se 2 (by rfl) ⟨1330224, by rfl⟩ : syracuseStep 3547265 = 2660449) B2660449
theorem B37837493 : Blo 2183435 37837493 := bstep (se 5 (by rfl) ⟨1773632, by rfl⟩ : syracuseStep 37837493 = 3547265) B3547265
theorem B25224995 : Blo 2183435 25224995 := bstep (se 1 (by rfl) ⟨18918746, by rfl⟩ : syracuseStep 25224995 = 37837493) B37837493
theorem B16816663 : Blo 2183435 16816663 := bstep (se 1 (by rfl) ⟨12612497, by rfl⟩ : syracuseStep 16816663 = 25224995) B25224995
theorem B89688869 : Blo 2183435 89688869 := bstep (se 4 (by rfl) ⟨8408331, by rfl⟩ : syracuseStep 89688869 = 16816663) B16816663
theorem B59792579 : Blo 2183435 59792579 := bstep (se 1 (by rfl) ⟨44844434, by rfl⟩ : syracuseStep 59792579 = 89688869) B89688869
theorem B39861719 : Blo 2183435 39861719 := bstep (se 1 (by rfl) ⟨29896289, by rfl⟩ : syracuseStep 39861719 = 59792579) B59792579
theorem B26574479 : Blo 2183435 26574479 := bstep (se 1 (by rfl) ⟨19930859, by rfl⟩ : syracuseStep 26574479 = 39861719) B39861719
theorem B17716319 : Blo 2183435 17716319 := bstep (se 1 (by rfl) ⟨13287239, by rfl⟩ : syracuseStep 17716319 = 26574479) B26574479
theorem B11810879 : Blo 2183435 11810879 := bstep (se 1 (by rfl) ⟨8858159, by rfl⟩ : syracuseStep 11810879 = 17716319) B17716319
theorem B7873919 : Blo 2183435 7873919 := bstep (se 1 (by rfl) ⟨5905439, by rfl⟩ : syracuseStep 7873919 = 11810879) B11810879
theorem B5249279 : Blo 2183435 5249279 := bstep (se 1 (by rfl) ⟨3936959, by rfl⟩ : syracuseStep 5249279 = 7873919) B7873919
theorem B3499519 : Blo 2183435 3499519 := bstep (se 1 (by rfl) ⟨2624639, by rfl⟩ : syracuseStep 3499519 = 5249279) B5249279
theorem B4666025 : Blo 2183435 4666025 := bstep (se 2 (by rfl) ⟨1749759, by rfl⟩ : syracuseStep 4666025 = 3499519) B3499519
theorem B12442733 : Blo 2183435 12442733 := bstep (se 3 (by rfl) ⟨2333012, by rfl⟩ : syracuseStep 12442733 = 4666025) B4666025
theorem B8295155 : Blo 2183435 8295155 := bstep (se 1 (by rfl) ⟨6221366, by rfl⟩ : syracuseStep 8295155 = 12442733) B12442733
theorem B5530103 : Blo 2183435 5530103 := bstep (se 1 (by rfl) ⟨4147577, by rfl⟩ : syracuseStep 5530103 = 8295155) B8295155
theorem B3686735 : Blo 2183435 3686735 := bstep (se 1 (by rfl) ⟨2765051, by rfl⟩ : syracuseStep 3686735 = 5530103) B5530103
theorem B2457823 : Blo 2183435 2457823 := bstep (se 1 (by rfl) ⟨1843367, by rfl⟩ : syracuseStep 2457823 = 3686735) B3686735
theorem B3277097 : Blo 2183435 3277097 := bstep (se 2 (by rfl) ⟨1228911, by rfl⟩ : syracuseStep 3277097 = 2457823) B2457823
theorem B2184731 : Blo 2183435 2184731 := bstep (se 1 (by rfl) ⟨1638548, by rfl⟩ : syracuseStep 2184731 = 3277097) B3277097
theorem B3499525 : Blo 2183435 3499525 := bbase (se 4 (by rfl) ⟨328080, by rfl⟩ : syracuseStep 3499525 = 656161) (by norm_num)
theorem B4666033 : Blo 2183435 4666033 := bstep (se 2 (by rfl) ⟨1749762, by rfl⟩ : syracuseStep 4666033 = 3499525) B3499525
theorem B6221377 : Blo 2183435 6221377 := bstep (se 2 (by rfl) ⟨2333016, by rfl⟩ : syracuseStep 6221377 = 4666033) B4666033
theorem B8295169 : Blo 2183435 8295169 := bstep (se 2 (by rfl) ⟨3110688, by rfl⟩ : syracuseStep 8295169 = 6221377) B6221377
theorem B11060225 : Blo 2183435 11060225 := bstep (se 2 (by rfl) ⟨4147584, by rfl⟩ : syracuseStep 11060225 = 8295169) B8295169
theorem B7373483 : Blo 2183435 7373483 := bstep (se 1 (by rfl) ⟨5530112, by rfl⟩ : syracuseStep 7373483 = 11060225) B11060225
theorem B4915655 : Blo 2183435 4915655 := bstep (se 1 (by rfl) ⟨3686741, by rfl⟩ : syracuseStep 4915655 = 7373483) B7373483
theorem B3277103 : Blo 2183435 3277103 := bstep (se 1 (by rfl) ⟨2457827, by rfl⟩ : syracuseStep 3277103 = 4915655) B4915655
theorem B2184735 : Blo 2183435 2184735 := bstep (se 1 (by rfl) ⟨1638551, by rfl⟩ : syracuseStep 2184735 = 3277103) B3277103
theorem B3277109 : Blo 2183435 3277109 := bbase (se 5 (by rfl) ⟨153614, by rfl⟩ : syracuseStep 3277109 = 307229) (by norm_num)
theorem B2184739 : Blo 2183435 2184739 := bstep (se 1 (by rfl) ⟨1638554, by rfl⟩ : syracuseStep 2184739 = 3277109) B3277109
theorem B5530133 : Blo 2183435 5530133 := bbase (se 6 (by rfl) ⟨129612, by rfl⟩ : syracuseStep 5530133 = 259225) (by norm_num)
theorem B3686755 : Blo 2183435 3686755 := bstep (se 1 (by rfl) ⟨2765066, by rfl⟩ : syracuseStep 3686755 = 5530133) B5530133
theorem B4915673 : Blo 2183435 4915673 := bstep (se 2 (by rfl) ⟨1843377, by rfl⟩ : syracuseStep 4915673 = 3686755) B3686755
theorem B3277115 : Blo 2183435 3277115 := bstep (se 1 (by rfl) ⟨2457836, by rfl⟩ : syracuseStep 3277115 = 4915673) B4915673
theorem B2184743 : Blo 2183435 2184743 := bstep (se 1 (by rfl) ⟨1638557, by rfl⟩ : syracuseStep 2184743 = 3277115) B3277115
theorem B2457841 : Blo 2183435 2457841 := bbase (se 2 (by rfl) ⟨921690, by rfl⟩ : syracuseStep 2457841 = 1843381) (by norm_num)
theorem B3277121 : Blo 2183435 3277121 := bstep (se 2 (by rfl) ⟨1228920, by rfl⟩ : syracuseStep 3277121 = 2457841) B2457841
theorem B2184747 : Blo 2183435 2184747 := bstep (se 1 (by rfl) ⟨1638560, by rfl⟩ : syracuseStep 2184747 = 3277121) B3277121
theorem B2660473 : Blo 2183435 2660473 := bbase (se 2 (by rfl) ⟨997677, by rfl⟩ : syracuseStep 2660473 = 1995355) (by norm_num)
theorem B3547297 : Blo 2183435 3547297 := bstep (se 2 (by rfl) ⟨1330236, by rfl⟩ : syracuseStep 3547297 = 2660473) B2660473
theorem B18918917 : Blo 2183435 18918917 := bstep (se 4 (by rfl) ⟨1773648, by rfl⟩ : syracuseStep 18918917 = 3547297) B3547297
theorem B12612611 : Blo 2183435 12612611 := bstep (se 1 (by rfl) ⟨9459458, by rfl⟩ : syracuseStep 12612611 = 18918917) B18918917
theorem B33633629 : Blo 2183435 33633629 := bstep (se 3 (by rfl) ⟨6306305, by rfl⟩ : syracuseStep 33633629 = 12612611) B12612611
theorem B22422419 : Blo 2183435 22422419 := bstep (se 1 (by rfl) ⟨16816814, by rfl⟩ : syracuseStep 22422419 = 33633629) B33633629
theorem B14948279 : Blo 2183435 14948279 := bstep (se 1 (by rfl) ⟨11211209, by rfl⟩ : syracuseStep 14948279 = 22422419) B22422419
theorem B9965519 : Blo 2183435 9965519 := bstep (se 1 (by rfl) ⟨7474139, by rfl⟩ : syracuseStep 9965519 = 14948279) B14948279
theorem B6643679 : Blo 2183435 6643679 := bstep (se 1 (by rfl) ⟨4982759, by rfl⟩ : syracuseStep 6643679 = 9965519) B9965519
theorem B17716477 : Blo 2183435 17716477 := bstep (se 3 (by rfl) ⟨3321839, by rfl⟩ : syracuseStep 17716477 = 6643679) B6643679
theorem B23621969 : Blo 2183435 23621969 := bstep (se 2 (by rfl) ⟨8858238, by rfl⟩ : syracuseStep 23621969 = 17716477) B17716477
theorem B15747979 : Blo 2183435 15747979 := bstep (se 1 (by rfl) ⟨11810984, by rfl⟩ : syracuseStep 15747979 = 23621969) B23621969
theorem B20997305 : Blo 2183435 20997305 := bstep (se 2 (by rfl) ⟨7873989, by rfl⟩ : syracuseStep 20997305 = 15747979) B15747979
theorem B13998203 : Blo 2183435 13998203 := bstep (se 1 (by rfl) ⟨10498652, by rfl⟩ : syracuseStep 13998203 = 20997305) B20997305
theorem B9332135 : Blo 2183435 9332135 := bstep (se 1 (by rfl) ⟨6999101, by rfl⟩ : syracuseStep 9332135 = 13998203) B13998203
theorem B6221423 : Blo 2183435 6221423 := bstep (se 1 (by rfl) ⟨4666067, by rfl⟩ : syracuseStep 6221423 = 9332135) B9332135
theorem B4147615 : Blo 2183435 4147615 := bstep (se 1 (by rfl) ⟨3110711, by rfl⟩ : syracuseStep 4147615 = 6221423) B6221423
theorem B5530153 : Blo 2183435 5530153 := bstep (se 2 (by rfl) ⟨2073807, by rfl⟩ : syracuseStep 5530153 = 4147615) B4147615
theorem B7373537 : Blo 2183435 7373537 := bstep (se 2 (by rfl) ⟨2765076, by rfl⟩ : syracuseStep 7373537 = 5530153) B5530153
theorem B4915691 : Blo 2183435 4915691 := bstep (se 1 (by rfl) ⟨3686768, by rfl⟩ : syracuseStep 4915691 = 7373537) B7373537
theorem B3277127 : Blo 2183435 3277127 := bstep (se 1 (by rfl) ⟨2457845, by rfl⟩ : syracuseStep 3277127 = 4915691) B4915691
theorem B2184751 : Blo 2183435 2184751 := bstep (se 1 (by rfl) ⟨1638563, by rfl⟩ : syracuseStep 2184751 = 3277127) B3277127
theorem B3277133 : Blo 2183435 3277133 := bbase (se 3 (by rfl) ⟨614462, by rfl⟩ : syracuseStep 3277133 = 1228925) (by norm_num)
theorem B2184755 : Blo 2183435 2184755 := bstep (se 1 (by rfl) ⟨1638566, by rfl⟩ : syracuseStep 2184755 = 3277133) B3277133
theorem B4915709 : Blo 2183435 4915709 := bbase (se 3 (by rfl) ⟨921695, by rfl⟩ : syracuseStep 4915709 = 1843391) (by norm_num)
theorem B3277139 : Blo 2183435 3277139 := bstep (se 1 (by rfl) ⟨2457854, by rfl⟩ : syracuseStep 3277139 = 4915709) B4915709
theorem B2184759 : Blo 2183435 2184759 := bstep (se 1 (by rfl) ⟨1638569, by rfl⟩ : syracuseStep 2184759 = 3277139) B3277139
theorem B3686789 : Blo 2183435 3686789 := bbase (se 4 (by rfl) ⟨345636, by rfl⟩ : syracuseStep 3686789 = 691273) (by norm_num)
theorem B2457859 : Blo 2183435 2457859 := bstep (se 1 (by rfl) ⟨1843394, by rfl⟩ : syracuseStep 2457859 = 3686789) B3686789
theorem B3277145 : Blo 2183435 3277145 := bstep (se 2 (by rfl) ⟨1228929, by rfl⟩ : syracuseStep 3277145 = 2457859) B2457859
theorem B2184763 : Blo 2183435 2184763 := bstep (se 1 (by rfl) ⟨1638572, by rfl⟩ : syracuseStep 2184763 = 3277145) B3277145
theorem B16590581 : Blo 2183435 16590581 := bbase (se 5 (by rfl) ⟨777683, by rfl⟩ : syracuseStep 16590581 = 1555367) (by norm_num)
theorem B11060387 : Blo 2183435 11060387 := bstep (se 1 (by rfl) ⟨8295290, by rfl⟩ : syracuseStep 11060387 = 16590581) B16590581
theorem B7373591 : Blo 2183435 7373591 := bstep (se 1 (by rfl) ⟨5530193, by rfl⟩ : syracuseStep 7373591 = 11060387) B11060387
theorem B4915727 : Blo 2183435 4915727 := bstep (se 1 (by rfl) ⟨3686795, by rfl⟩ : syracuseStep 4915727 = 7373591) B7373591
theorem B3277151 : Blo 2183435 3277151 := bstep (se 1 (by rfl) ⟨2457863, by rfl⟩ : syracuseStep 3277151 = 4915727) B4915727
theorem B2184767 : Blo 2183435 2184767 := bstep (se 1 (by rfl) ⟨1638575, by rfl⟩ : syracuseStep 2184767 = 3277151) B3277151
theorem B3277157 : Blo 2183435 3277157 := bbase (se 4 (by rfl) ⟨307233, by rfl⟩ : syracuseStep 3277157 = 614467) (by norm_num)
theorem B2184771 : Blo 2183435 2184771 := bstep (se 1 (by rfl) ⟨1638578, by rfl⟩ : syracuseStep 2184771 = 3277157) B3277157
theorem B4147661 : Blo 2183435 4147661 := bbase (se 3 (by rfl) ⟨777686, by rfl⟩ : syracuseStep 4147661 = 1555373) (by norm_num)
theorem B2765107 : Blo 2183435 2765107 := bstep (se 1 (by rfl) ⟨2073830, by rfl⟩ : syracuseStep 2765107 = 4147661) B4147661
theorem B3686809 : Blo 2183435 3686809 := bstep (se 2 (by rfl) ⟨1382553, by rfl⟩ : syracuseStep 3686809 = 2765107) B2765107
theorem B4915745 : Blo 2183435 4915745 := bstep (se 2 (by rfl) ⟨1843404, by rfl⟩ : syracuseStep 4915745 = 3686809) B3686809
theorem B3277163 : Blo 2183435 3277163 := bstep (se 1 (by rfl) ⟨2457872, by rfl⟩ : syracuseStep 3277163 = 4915745) B4915745
theorem B2184775 : Blo 2183435 2184775 := bstep (se 1 (by rfl) ⟨1638581, by rfl⟩ : syracuseStep 2184775 = 3277163) B3277163
theorem B2457877 : Blo 2183435 2457877 := bbase (se 6 (by rfl) ⟨57606, by rfl⟩ : syracuseStep 2457877 = 115213) (by norm_num)
theorem B3277169 : Blo 2183435 3277169 := bstep (se 2 (by rfl) ⟨1228938, by rfl⟩ : syracuseStep 3277169 = 2457877) B2457877
theorem B2184779 : Blo 2183435 2184779 := bstep (se 1 (by rfl) ⟨1638584, by rfl⟩ : syracuseStep 2184779 = 3277169) B3277169
theorem B2765117 : Blo 2183435 2765117 := bbase (se 3 (by rfl) ⟨518459, by rfl⟩ : syracuseStep 2765117 = 1036919) (by norm_num)
theorem B7373645 : Blo 2183435 7373645 := bstep (se 3 (by rfl) ⟨1382558, by rfl⟩ : syracuseStep 7373645 = 2765117) B2765117
theorem B4915763 : Blo 2183435 4915763 := bstep (se 1 (by rfl) ⟨3686822, by rfl⟩ : syracuseStep 4915763 = 7373645) B7373645
theorem B3277175 : Blo 2183435 3277175 := bstep (se 1 (by rfl) ⟨2457881, by rfl⟩ : syracuseStep 3277175 = 4915763) B4915763
theorem B2184783 : Blo 2183435 2184783 := bstep (se 1 (by rfl) ⟨1638587, by rfl⟩ : syracuseStep 2184783 = 3277175) B3277175
theorem B3277181 : Blo 2183435 3277181 := bbase (se 3 (by rfl) ⟨614471, by rfl⟩ : syracuseStep 3277181 = 1228943) (by norm_num)
theorem B2184787 : Blo 2183435 2184787 := bstep (se 1 (by rfl) ⟨1638590, by rfl⟩ : syracuseStep 2184787 = 3277181) B3277181
theorem B4915781 : Blo 2183435 4915781 := bbase (se 4 (by rfl) ⟨460854, by rfl⟩ : syracuseStep 4915781 = 921709) (by norm_num)
theorem B3277187 : Blo 2183435 3277187 := bstep (se 1 (by rfl) ⟨2457890, by rfl⟩ : syracuseStep 3277187 = 4915781) B4915781
theorem B2184791 : Blo 2183435 2184791 := bstep (se 1 (by rfl) ⟨1638593, by rfl⟩ : syracuseStep 2184791 = 3277187) B3277187
theorem B2333081 : Blo 2183435 2333081 := bbase (se 2 (by rfl) ⟨874905, by rfl⟩ : syracuseStep 2333081 = 1749811) (by norm_num)
theorem B6221549 : Blo 2183435 6221549 := bstep (se 3 (by rfl) ⟨1166540, by rfl⟩ : syracuseStep 6221549 = 2333081) B2333081
theorem B4147699 : Blo 2183435 4147699 := bstep (se 1 (by rfl) ⟨3110774, by rfl⟩ : syracuseStep 4147699 = 6221549) B6221549
theorem B5530265 : Blo 2183435 5530265 := bstep (se 2 (by rfl) ⟨2073849, by rfl⟩ : syracuseStep 5530265 = 4147699) B4147699
theorem B3686843 : Blo 2183435 3686843 := bstep (se 1 (by rfl) ⟨2765132, by rfl⟩ : syracuseStep 3686843 = 5530265) B5530265
theorem B2457895 : Blo 2183435 2457895 := bstep (se 1 (by rfl) ⟨1843421, by rfl⟩ : syracuseStep 2457895 = 3686843) B3686843
theorem B3277193 : Blo 2183435 3277193 := bstep (se 2 (by rfl) ⟨1228947, by rfl⟩ : syracuseStep 3277193 = 2457895) B2457895
theorem B2184795 : Blo 2183435 2184795 := bstep (se 1 (by rfl) ⟨1638596, by rfl⟩ : syracuseStep 2184795 = 3277193) B3277193
theorem B11060549 : Blo 2183435 11060549 := bbase (se 4 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 11060549 = 2073853) (by norm_num)
theorem B7373699 : Blo 2183435 7373699 := bstep (se 1 (by rfl) ⟨5530274, by rfl⟩ : syracuseStep 7373699 = 11060549) B11060549
theorem B4915799 : Blo 2183435 4915799 := bstep (se 1 (by rfl) ⟨3686849, by rfl⟩ : syracuseStep 4915799 = 7373699) B7373699
theorem B3277199 : Blo 2183435 3277199 := bstep (se 1 (by rfl) ⟨2457899, by rfl⟩ : syracuseStep 3277199 = 4915799) B4915799
theorem B2184799 : Blo 2183435 2184799 := bstep (se 1 (by rfl) ⟨1638599, by rfl⟩ : syracuseStep 2184799 = 3277199) B3277199
theorem B3277205 : Blo 2183435 3277205 := bbase (se 6 (by rfl) ⟨76809, by rfl⟩ : syracuseStep 3277205 = 153619) (by norm_num)
theorem B2184803 : Blo 2183435 2184803 := bstep (se 1 (by rfl) ⟨1638602, by rfl⟩ : syracuseStep 2184803 = 3277205) B3277205
theorem B5249461 : Blo 2183435 5249461 := bbase (se 5 (by rfl) ⟨246068, by rfl⟩ : syracuseStep 5249461 = 492137) (by norm_num)
theorem B6999281 : Blo 2183435 6999281 := bstep (se 2 (by rfl) ⟨2624730, by rfl⟩ : syracuseStep 6999281 = 5249461) B5249461
theorem B4666187 : Blo 2183435 4666187 := bstep (se 1 (by rfl) ⟨3499640, by rfl⟩ : syracuseStep 4666187 = 6999281) B6999281
theorem B12443165 : Blo 2183435 12443165 := bstep (se 3 (by rfl) ⟨2333093, by rfl⟩ : syracuseStep 12443165 = 4666187) B4666187
theorem B8295443 : Blo 2183435 8295443 := bstep (se 1 (by rfl) ⟨6221582, by rfl⟩ : syracuseStep 8295443 = 12443165) B12443165
theorem B5530295 : Blo 2183435 5530295 := bstep (se 1 (by rfl) ⟨4147721, by rfl⟩ : syracuseStep 5530295 = 8295443) B8295443
theorem B3686863 : Blo 2183435 3686863 := bstep (se 1 (by rfl) ⟨2765147, by rfl⟩ : syracuseStep 3686863 = 5530295) B5530295
theorem B4915817 : Blo 2183435 4915817 := bstep (se 2 (by rfl) ⟨1843431, by rfl⟩ : syracuseStep 4915817 = 3686863) B3686863
theorem B3277211 : Blo 2183435 3277211 := bstep (se 1 (by rfl) ⟨2457908, by rfl⟩ : syracuseStep 3277211 = 4915817) B4915817
theorem B2184807 : Blo 2183435 2184807 := bstep (se 1 (by rfl) ⟨1638605, by rfl⟩ : syracuseStep 2184807 = 3277211) B3277211
theorem B2457913 : Blo 2183435 2457913 := bbase (se 2 (by rfl) ⟨921717, by rfl⟩ : syracuseStep 2457913 = 1843435) (by norm_num)
theorem B3277217 : Blo 2183435 3277217 := bstep (se 2 (by rfl) ⟨1228956, by rfl⟩ : syracuseStep 3277217 = 2457913) B2457913
theorem B2184811 : Blo 2183435 2184811 := bstep (se 1 (by rfl) ⟨1638608, by rfl⟩ : syracuseStep 2184811 = 3277217) B3277217
theorem B6221605 : Blo 2183435 6221605 := bbase (se 4 (by rfl) ⟨583275, by rfl⟩ : syracuseStep 6221605 = 1166551) (by norm_num)
theorem B8295473 : Blo 2183435 8295473 := bstep (se 2 (by rfl) ⟨3110802, by rfl⟩ : syracuseStep 8295473 = 6221605) B6221605
theorem B5530315 : Blo 2183435 5530315 := bstep (se 1 (by rfl) ⟨4147736, by rfl⟩ : syracuseStep 5530315 = 8295473) B8295473
theorem B7373753 : Blo 2183435 7373753 := bstep (se 2 (by rfl) ⟨2765157, by rfl⟩ : syracuseStep 7373753 = 5530315) B5530315
theorem B4915835 : Blo 2183435 4915835 := bstep (se 1 (by rfl) ⟨3686876, by rfl⟩ : syracuseStep 4915835 = 7373753) B7373753
theorem B3277223 : Blo 2183435 3277223 := bstep (se 1 (by rfl) ⟨2457917, by rfl⟩ : syracuseStep 3277223 = 4915835) B4915835
theorem B2184815 : Blo 2183435 2184815 := bstep (se 1 (by rfl) ⟨1638611, by rfl⟩ : syracuseStep 2184815 = 3277223) B3277223
theorem B3277229 : Blo 2183435 3277229 := bbase (se 3 (by rfl) ⟨614480, by rfl⟩ : syracuseStep 3277229 = 1228961) (by norm_num)
theorem B2184819 : Blo 2183435 2184819 := bstep (se 1 (by rfl) ⟨1638614, by rfl⟩ : syracuseStep 2184819 = 3277229) B3277229
theorem B4915853 : Blo 2183435 4915853 := bbase (se 3 (by rfl) ⟨921722, by rfl⟩ : syracuseStep 4915853 = 1843445) (by norm_num)
theorem B3277235 : Blo 2183435 3277235 := bstep (se 1 (by rfl) ⟨2457926, by rfl⟩ : syracuseStep 3277235 = 4915853) B4915853
theorem B2184823 : Blo 2183435 2184823 := bstep (se 1 (by rfl) ⟨1638617, by rfl⟩ : syracuseStep 2184823 = 3277235) B3277235
theorem B2765173 : Blo 2183435 2765173 := bbase (se 5 (by rfl) ⟨129617, by rfl⟩ : syracuseStep 2765173 = 259235) (by norm_num)
theorem B3686897 : Blo 2183435 3686897 := bstep (se 2 (by rfl) ⟨1382586, by rfl⟩ : syracuseStep 3686897 = 2765173) B2765173
theorem B2457931 : Blo 2183435 2457931 := bstep (se 1 (by rfl) ⟨1843448, by rfl⟩ : syracuseStep 2457931 = 3686897) B3686897
theorem B3277241 : Blo 2183435 3277241 := bstep (se 2 (by rfl) ⟨1228965, by rfl⟩ : syracuseStep 3277241 = 2457931) B2457931
theorem B2184827 : Blo 2183435 2184827 := bstep (se 1 (by rfl) ⟨1638620, by rfl⟩ : syracuseStep 2184827 = 3277241) B3277241
theorem B4982941 : Blo 2183435 4982941 := bbase (se 3 (by rfl) ⟨934301, by rfl⟩ : syracuseStep 4982941 = 1868603) (by norm_num)
theorem B26575685 : Blo 2183435 26575685 := bstep (se 4 (by rfl) ⟨2491470, by rfl⟩ : syracuseStep 26575685 = 4982941) B4982941
theorem B17717123 : Blo 2183435 17717123 := bstep (se 1 (by rfl) ⟨13287842, by rfl⟩ : syracuseStep 17717123 = 26575685) B26575685
theorem B11811415 : Blo 2183435 11811415 := bstep (se 1 (by rfl) ⟨8858561, by rfl⟩ : syracuseStep 11811415 = 17717123) B17717123
theorem B15748553 : Blo 2183435 15748553 := bstep (se 2 (by rfl) ⟨5905707, by rfl⟩ : syracuseStep 15748553 = 11811415) B11811415
theorem B41996141 : Blo 2183435 41996141 := bstep (se 3 (by rfl) ⟨7874276, by rfl⟩ : syracuseStep 41996141 = 15748553) B15748553
theorem B27997427 : Blo 2183435 27997427 := bstep (se 1 (by rfl) ⟨20998070, by rfl⟩ : syracuseStep 27997427 = 41996141) B41996141
theorem B18664951 : Blo 2183435 18664951 := bstep (se 1 (by rfl) ⟨13998713, by rfl⟩ : syracuseStep 18664951 = 27997427) B27997427
theorem B24886601 : Blo 2183435 24886601 := bstep (se 2 (by rfl) ⟨9332475, by rfl⟩ : syracuseStep 24886601 = 18664951) B18664951
theorem B16591067 : Blo 2183435 16591067 := bstep (se 1 (by rfl) ⟨12443300, by rfl⟩ : syracuseStep 16591067 = 24886601) B24886601
theorem B11060711 : Blo 2183435 11060711 := bstep (se 1 (by rfl) ⟨8295533, by rfl⟩ : syracuseStep 11060711 = 16591067) B16591067
theorem B7373807 : Blo 2183435 7373807 := bstep (se 1 (by rfl) ⟨5530355, by rfl⟩ : syracuseStep 7373807 = 11060711) B11060711
theorem B4915871 : Blo 2183435 4915871 := bstep (se 1 (by rfl) ⟨3686903, by rfl⟩ : syracuseStep 4915871 = 7373807) B7373807
theorem B3277247 : Blo 2183435 3277247 := bstep (se 1 (by rfl) ⟨2457935, by rfl⟩ : syracuseStep 3277247 = 4915871) B4915871
theorem B2184831 : Blo 2183435 2184831 := bstep (se 1 (by rfl) ⟨1638623, by rfl⟩ : syracuseStep 2184831 = 3277247) B3277247
theorem B3277253 : Blo 2183435 3277253 := bbase (se 4 (by rfl) ⟨307242, by rfl⟩ : syracuseStep 3277253 = 614485) (by norm_num)
theorem B2184835 : Blo 2183435 2184835 := bstep (se 1 (by rfl) ⟨1638626, by rfl⟩ : syracuseStep 2184835 = 3277253) B3277253
theorem B3686917 : Blo 2183435 3686917 := bbase (se 4 (by rfl) ⟨345648, by rfl⟩ : syracuseStep 3686917 = 691297) (by norm_num)
theorem B4915889 : Blo 2183435 4915889 := bstep (se 2 (by rfl) ⟨1843458, by rfl⟩ : syracuseStep 4915889 = 3686917) B3686917
theorem B3277259 : Blo 2183435 3277259 := bstep (se 1 (by rfl) ⟨2457944, by rfl⟩ : syracuseStep 3277259 = 4915889) B4915889
theorem B2184839 : Blo 2183435 2184839 := bstep (se 1 (by rfl) ⟨1638629, by rfl⟩ : syracuseStep 2184839 = 3277259) B3277259
theorem B2457949 : Blo 2183435 2457949 := bbase (se 3 (by rfl) ⟨460865, by rfl⟩ : syracuseStep 2457949 = 921731) (by norm_num)
theorem B3277265 : Blo 2183435 3277265 := bstep (se 2 (by rfl) ⟨1228974, by rfl⟩ : syracuseStep 3277265 = 2457949) B2457949
theorem B2184843 : Blo 2183435 2184843 := bstep (se 1 (by rfl) ⟨1638632, by rfl⟩ : syracuseStep 2184843 = 3277265) B3277265
theorem B7373861 : Blo 2183435 7373861 := bbase (se 4 (by rfl) ⟨691299, by rfl⟩ : syracuseStep 7373861 = 1382599) (by norm_num)
theorem B4915907 : Blo 2183435 4915907 := bstep (se 1 (by rfl) ⟨3686930, by rfl⟩ : syracuseStep 4915907 = 7373861) B7373861
theorem B3277271 : Blo 2183435 3277271 := bstep (se 1 (by rfl) ⟨2457953, by rfl⟩ : syracuseStep 3277271 = 4915907) B4915907
theorem B2184847 : Blo 2183435 2184847 := bstep (se 1 (by rfl) ⟨1638635, by rfl⟩ : syracuseStep 2184847 = 3277271) B3277271
theorem B3277277 : Blo 2183435 3277277 := bbase (se 3 (by rfl) ⟨614489, by rfl⟩ : syracuseStep 3277277 = 1228979) (by norm_num)
theorem B2184851 : Blo 2183435 2184851 := bstep (se 1 (by rfl) ⟨1638638, by rfl⟩ : syracuseStep 2184851 = 3277277) B3277277
theorem B4915925 : Blo 2183435 4915925 := bbase (se 7 (by rfl) ⟨57608, by rfl⟩ : syracuseStep 4915925 = 115217) (by norm_num)
theorem B3277283 : Blo 2183435 3277283 := bstep (se 1 (by rfl) ⟨2457962, by rfl⟩ : syracuseStep 3277283 = 4915925) B4915925
theorem B2184855 : Blo 2183435 2184855 := bstep (se 1 (by rfl) ⟨1638641, by rfl⟩ : syracuseStep 2184855 = 3277283) B3277283
theorem B9332597 : Blo 2183435 9332597 := bbase (se 5 (by rfl) ⟨437465, by rfl⟩ : syracuseStep 9332597 = 874931) (by norm_num)
theorem B6221731 : Blo 2183435 6221731 := bstep (se 1 (by rfl) ⟨4666298, by rfl⟩ : syracuseStep 6221731 = 9332597) B9332597
theorem B8295641 : Blo 2183435 8295641 := bstep (se 2 (by rfl) ⟨3110865, by rfl⟩ : syracuseStep 8295641 = 6221731) B6221731
theorem B5530427 : Blo 2183435 5530427 := bstep (se 1 (by rfl) ⟨4147820, by rfl⟩ : syracuseStep 5530427 = 8295641) B8295641
theorem B3686951 : Blo 2183435 3686951 := bstep (se 1 (by rfl) ⟨2765213, by rfl⟩ : syracuseStep 3686951 = 5530427) B5530427
theorem B2457967 : Blo 2183435 2457967 := bstep (se 1 (by rfl) ⟨1843475, by rfl⟩ : syracuseStep 2457967 = 3686951) B3686951
theorem B3277289 : Blo 2183435 3277289 := bstep (se 2 (by rfl) ⟨1228983, by rfl⟩ : syracuseStep 3277289 = 2457967) B2457967
theorem B2184859 : Blo 2183435 2184859 := bstep (se 1 (by rfl) ⟨1638644, by rfl⟩ : syracuseStep 2184859 = 3277289) B3277289
theorem B8408837 : Blo 2183435 8408837 := bbase (se 4 (by rfl) ⟨788328, by rfl⟩ : syracuseStep 8408837 = 1576657) (by norm_num)
theorem B5605891 : Blo 2183435 5605891 := bstep (se 1 (by rfl) ⟨4204418, by rfl⟩ : syracuseStep 5605891 = 8408837) B8408837
theorem B29898085 : Blo 2183435 29898085 := bstep (se 4 (by rfl) ⟨2802945, by rfl⟩ : syracuseStep 29898085 = 5605891) B5605891
theorem B39864113 : Blo 2183435 39864113 := bstep (se 2 (by rfl) ⟨14949042, by rfl⟩ : syracuseStep 39864113 = 29898085) B29898085
theorem B26576075 : Blo 2183435 26576075 := bstep (se 1 (by rfl) ⟨19932056, by rfl⟩ : syracuseStep 26576075 = 39864113) B39864113
theorem B17717383 : Blo 2183435 17717383 := bstep (se 1 (by rfl) ⟨13288037, by rfl⟩ : syracuseStep 17717383 = 26576075) B26576075
theorem B23623177 : Blo 2183435 23623177 := bstep (se 2 (by rfl) ⟨8858691, by rfl⟩ : syracuseStep 23623177 = 17717383) B17717383
theorem B31497569 : Blo 2183435 31497569 := bstep (se 2 (by rfl) ⟨11811588, by rfl⟩ : syracuseStep 31497569 = 23623177) B23623177
theorem B20998379 : Blo 2183435 20998379 := bstep (se 1 (by rfl) ⟨15748784, by rfl⟩ : syracuseStep 20998379 = 31497569) B31497569
theorem B13998919 : Blo 2183435 13998919 := bstep (se 1 (by rfl) ⟨10499189, by rfl⟩ : syracuseStep 13998919 = 20998379) B20998379
theorem B18665225 : Blo 2183435 18665225 := bstep (se 2 (by rfl) ⟨6999459, by rfl⟩ : syracuseStep 18665225 = 13998919) B13998919
theorem B12443483 : Blo 2183435 12443483 := bstep (se 1 (by rfl) ⟨9332612, by rfl⟩ : syracuseStep 12443483 = 18665225) B18665225
theorem B8295655 : Blo 2183435 8295655 := bstep (se 1 (by rfl) ⟨6221741, by rfl⟩ : syracuseStep 8295655 = 12443483) B12443483
theorem B11060873 : Blo 2183435 11060873 := bstep (se 2 (by rfl) ⟨4147827, by rfl⟩ : syracuseStep 11060873 = 8295655) B8295655
theorem B7373915 : Blo 2183435 7373915 := bstep (se 1 (by rfl) ⟨5530436, by rfl⟩ : syracuseStep 7373915 = 11060873) B11060873
theorem B4915943 : Blo 2183435 4915943 := bstep (se 1 (by rfl) ⟨3686957, by rfl⟩ : syracuseStep 4915943 = 7373915) B7373915
theorem B3277295 : Blo 2183435 3277295 := bstep (se 1 (by rfl) ⟨2457971, by rfl⟩ : syracuseStep 3277295 = 4915943) B4915943
theorem B2184863 : Blo 2183435 2184863 := bstep (se 1 (by rfl) ⟨1638647, by rfl⟩ : syracuseStep 2184863 = 3277295) B3277295
theorem B3277301 : Blo 2183435 3277301 := bbase (se 5 (by rfl) ⟨153623, by rfl⟩ : syracuseStep 3277301 = 307247) (by norm_num)
theorem B2184867 : Blo 2183435 2184867 := bstep (se 1 (by rfl) ⟨1638650, by rfl⟩ : syracuseStep 2184867 = 3277301) B3277301
theorem B6221765 : Blo 2183435 6221765 := bbase (se 4 (by rfl) ⟨583290, by rfl⟩ : syracuseStep 6221765 = 1166581) (by norm_num)
theorem B4147843 : Blo 2183435 4147843 := bstep (se 1 (by rfl) ⟨3110882, by rfl⟩ : syracuseStep 4147843 = 6221765) B6221765
theorem B5530457 : Blo 2183435 5530457 := bstep (se 2 (by rfl) ⟨2073921, by rfl⟩ : syracuseStep 5530457 = 4147843) B4147843
theorem B3686971 : Blo 2183435 3686971 := bstep (se 1 (by rfl) ⟨2765228, by rfl⟩ : syracuseStep 3686971 = 5530457) B5530457
theorem B4915961 : Blo 2183435 4915961 := bstep (se 2 (by rfl) ⟨1843485, by rfl⟩ : syracuseStep 4915961 = 3686971) B3686971
theorem B3277307 : Blo 2183435 3277307 := bstep (se 1 (by rfl) ⟨2457980, by rfl⟩ : syracuseStep 3277307 = 4915961) B4915961
theorem B2184871 : Blo 2183435 2184871 := bstep (se 1 (by rfl) ⟨1638653, by rfl⟩ : syracuseStep 2184871 = 3277307) B3277307
theorem B2457985 : Blo 2183435 2457985 := bbase (se 2 (by rfl) ⟨921744, by rfl⟩ : syracuseStep 2457985 = 1843489) (by norm_num)
theorem B3277313 : Blo 2183435 3277313 := bstep (se 2 (by rfl) ⟨1228992, by rfl⟩ : syracuseStep 3277313 = 2457985) B2457985
theorem B2184875 : Blo 2183435 2184875 := bstep (se 1 (by rfl) ⟨1638656, by rfl⟩ : syracuseStep 2184875 = 3277313) B3277313
theorem B5530477 : Blo 2183435 5530477 := bbase (se 3 (by rfl) ⟨1036964, by rfl⟩ : syracuseStep 5530477 = 2073929) (by norm_num)
theorem B7373969 : Blo 2183435 7373969 := bstep (se 2 (by rfl) ⟨2765238, by rfl⟩ : syracuseStep 7373969 = 5530477) B5530477
theorem B4915979 : Blo 2183435 4915979 := bstep (se 1 (by rfl) ⟨3686984, by rfl⟩ : syracuseStep 4915979 = 7373969) B7373969
theorem B3277319 : Blo 2183435 3277319 := bstep (se 1 (by rfl) ⟨2457989, by rfl⟩ : syracuseStep 3277319 = 4915979) B4915979
theorem B2184879 : Blo 2183435 2184879 := bstep (se 1 (by rfl) ⟨1638659, by rfl⟩ : syracuseStep 2184879 = 3277319) B3277319
theorem B3277325 : Blo 2183435 3277325 := bbase (se 3 (by rfl) ⟨614498, by rfl⟩ : syracuseStep 3277325 = 1228997) (by norm_num)
theorem B2184883 : Blo 2183435 2184883 := bstep (se 1 (by rfl) ⟨1638662, by rfl⟩ : syracuseStep 2184883 = 3277325) B3277325
theorem B4915997 : Blo 2183435 4915997 := bbase (se 3 (by rfl) ⟨921749, by rfl⟩ : syracuseStep 4915997 = 1843499) (by norm_num)
theorem B3277331 : Blo 2183435 3277331 := bstep (se 1 (by rfl) ⟨2457998, by rfl⟩ : syracuseStep 3277331 = 4915997) B4915997
theorem B2184887 : Blo 2183435 2184887 := bstep (se 1 (by rfl) ⟨1638665, by rfl⟩ : syracuseStep 2184887 = 3277331) B3277331
theorem B3687005 : Blo 2183435 3687005 := bbase (se 3 (by rfl) ⟨691313, by rfl⟩ : syracuseStep 3687005 = 1382627) (by norm_num)
theorem B2458003 : Blo 2183435 2458003 := bstep (se 1 (by rfl) ⟨1843502, by rfl⟩ : syracuseStep 2458003 = 3687005) B3687005
theorem B3277337 : Blo 2183435 3277337 := bstep (se 2 (by rfl) ⟨1229001, by rfl⟩ : syracuseStep 3277337 = 2458003) B2458003
theorem B2184891 : Blo 2183435 2184891 := bstep (se 1 (by rfl) ⟨1638668, by rfl⟩ : syracuseStep 2184891 = 3277337) B3277337
theorem B3499781 : Blo 2183435 3499781 := bbase (se 4 (by rfl) ⟨328104, by rfl⟩ : syracuseStep 3499781 = 656209) (by norm_num)
theorem B9332749 : Blo 2183435 9332749 := bstep (se 3 (by rfl) ⟨1749890, by rfl⟩ : syracuseStep 9332749 = 3499781) B3499781
theorem B12443665 : Blo 2183435 12443665 := bstep (se 2 (by rfl) ⟨4666374, by rfl⟩ : syracuseStep 12443665 = 9332749) B9332749
theorem B16591553 : Blo 2183435 16591553 := bstep (se 2 (by rfl) ⟨6221832, by rfl⟩ : syracuseStep 16591553 = 12443665) B12443665
theorem B11061035 : Blo 2183435 11061035 := bstep (se 1 (by rfl) ⟨8295776, by rfl⟩ : syracuseStep 11061035 = 16591553) B16591553
theorem B7374023 : Blo 2183435 7374023 := bstep (se 1 (by rfl) ⟨5530517, by rfl⟩ : syracuseStep 7374023 = 11061035) B11061035
theorem B4916015 : Blo 2183435 4916015 := bstep (se 1 (by rfl) ⟨3687011, by rfl⟩ : syracuseStep 4916015 = 7374023) B7374023
theorem B3277343 : Blo 2183435 3277343 := bstep (se 1 (by rfl) ⟨2458007, by rfl⟩ : syracuseStep 3277343 = 4916015) B4916015
theorem B2184895 : Blo 2183435 2184895 := bstep (se 1 (by rfl) ⟨1638671, by rfl⟩ : syracuseStep 2184895 = 3277343) B3277343
theorem B3277349 : Blo 2183435 3277349 := bbase (se 4 (by rfl) ⟨307251, by rfl⟩ : syracuseStep 3277349 = 614503) (by norm_num)
theorem B2184899 : Blo 2183435 2184899 := bstep (se 1 (by rfl) ⟨1638674, by rfl⟩ : syracuseStep 2184899 = 3277349) B3277349
theorem B2765269 : Blo 2183435 2765269 := bbase (se 7 (by rfl) ⟨32405, by rfl⟩ : syracuseStep 2765269 = 64811) (by norm_num)
theorem B3687025 : Blo 2183435 3687025 := bstep (se 2 (by rfl) ⟨1382634, by rfl⟩ : syracuseStep 3687025 = 2765269) B2765269
theorem B4916033 : Blo 2183435 4916033 := bstep (se 2 (by rfl) ⟨1843512, by rfl⟩ : syracuseStep 4916033 = 3687025) B3687025
theorem B3277355 : Blo 2183435 3277355 := bstep (se 1 (by rfl) ⟨2458016, by rfl⟩ : syracuseStep 3277355 = 4916033) B4916033
theorem B2184903 : Blo 2183435 2184903 := bstep (se 1 (by rfl) ⟨1638677, by rfl⟩ : syracuseStep 2184903 = 3277355) B3277355
theorem B2458021 : Blo 2183435 2458021 := bbase (se 4 (by rfl) ⟨230439, by rfl⟩ : syracuseStep 2458021 = 460879) (by norm_num)
theorem B3277361 : Blo 2183435 3277361 := bstep (se 2 (by rfl) ⟨1229010, by rfl⟩ : syracuseStep 3277361 = 2458021) B2458021
theorem B2184907 : Blo 2183435 2184907 := bstep (se 1 (by rfl) ⟨1638680, by rfl⟩ : syracuseStep 2184907 = 3277361) B3277361
theorem B4983125 : Blo 2183435 4983125 := bbase (se 10 (by rfl) ⟨7299, by rfl⟩ : syracuseStep 4983125 = 14599) (by norm_num)
theorem B13288333 : Blo 2183435 13288333 := bstep (se 3 (by rfl) ⟨2491562, by rfl⟩ : syracuseStep 13288333 = 4983125) B4983125
theorem B17717777 : Blo 2183435 17717777 := bstep (se 2 (by rfl) ⟨6644166, by rfl⟩ : syracuseStep 17717777 = 13288333) B13288333
theorem B11811851 : Blo 2183435 11811851 := bstep (se 1 (by rfl) ⟨8858888, by rfl⟩ : syracuseStep 11811851 = 17717777) B17717777
theorem B7874567 : Blo 2183435 7874567 := bstep (se 1 (by rfl) ⟨5905925, by rfl⟩ : syracuseStep 7874567 = 11811851) B11811851
theorem B5249711 : Blo 2183435 5249711 := bstep (se 1 (by rfl) ⟨3937283, by rfl⟩ : syracuseStep 5249711 = 7874567) B7874567
theorem B13999229 : Blo 2183435 13999229 := bstep (se 3 (by rfl) ⟨2624855, by rfl⟩ : syracuseStep 13999229 = 5249711) B5249711
theorem B9332819 : Blo 2183435 9332819 := bstep (se 1 (by rfl) ⟨6999614, by rfl⟩ : syracuseStep 9332819 = 13999229) B13999229
theorem B6221879 : Blo 2183435 6221879 := bstep (se 1 (by rfl) ⟨4666409, by rfl⟩ : syracuseStep 6221879 = 9332819) B9332819
theorem B4147919 : Blo 2183435 4147919 := bstep (se 1 (by rfl) ⟨3110939, by rfl⟩ : syracuseStep 4147919 = 6221879) B6221879
theorem B2765279 : Blo 2183435 2765279 := bstep (se 1 (by rfl) ⟨2073959, by rfl⟩ : syracuseStep 2765279 = 4147919) B4147919
theorem B7374077 : Blo 2183435 7374077 := bstep (se 3 (by rfl) ⟨1382639, by rfl⟩ : syracuseStep 7374077 = 2765279) B2765279
theorem B4916051 : Blo 2183435 4916051 := bstep (se 1 (by rfl) ⟨3687038, by rfl⟩ : syracuseStep 4916051 = 7374077) B7374077
theorem B3277367 : Blo 2183435 3277367 := bstep (se 1 (by rfl) ⟨2458025, by rfl⟩ : syracuseStep 3277367 = 4916051) B4916051
theorem B2184911 : Blo 2183435 2184911 := bstep (se 1 (by rfl) ⟨1638683, by rfl⟩ : syracuseStep 2184911 = 3277367) B3277367
theorem B3277373 : Blo 2183435 3277373 := bbase (se 3 (by rfl) ⟨614507, by rfl⟩ : syracuseStep 3277373 = 1229015) (by norm_num)
theorem B2184915 : Blo 2183435 2184915 := bstep (se 1 (by rfl) ⟨1638686, by rfl⟩ : syracuseStep 2184915 = 3277373) B3277373
theorem B4916069 : Blo 2183435 4916069 := bbase (se 4 (by rfl) ⟨460881, by rfl⟩ : syracuseStep 4916069 = 921763) (by norm_num)
theorem B3277379 : Blo 2183435 3277379 := bstep (se 1 (by rfl) ⟨2458034, by rfl⟩ : syracuseStep 3277379 = 4916069) B4916069
theorem B2184919 : Blo 2183435 2184919 := bstep (se 1 (by rfl) ⟨1638689, by rfl⟩ : syracuseStep 2184919 = 3277379) B3277379
theorem B5530589 : Blo 2183435 5530589 := bbase (se 3 (by rfl) ⟨1036985, by rfl⟩ : syracuseStep 5530589 = 2073971) (by norm_num)
theorem B3687059 : Blo 2183435 3687059 := bstep (se 1 (by rfl) ⟨2765294, by rfl⟩ : syracuseStep 3687059 = 5530589) B5530589
theorem B2458039 : Blo 2183435 2458039 := bstep (se 1 (by rfl) ⟨1843529, by rfl⟩ : syracuseStep 2458039 = 3687059) B3687059
theorem B3277385 : Blo 2183435 3277385 := bstep (se 2 (by rfl) ⟨1229019, by rfl⟩ : syracuseStep 3277385 = 2458039) B2458039
theorem B2184923 : Blo 2183435 2184923 := bstep (se 1 (by rfl) ⟨1638692, by rfl⟩ : syracuseStep 2184923 = 3277385) B3277385
theorem B4147949 : Blo 2183435 4147949 := bbase (se 3 (by rfl) ⟨777740, by rfl⟩ : syracuseStep 4147949 = 1555481) (by norm_num)
theorem B11061197 : Blo 2183435 11061197 := bstep (se 3 (by rfl) ⟨2073974, by rfl⟩ : syracuseStep 11061197 = 4147949) B4147949
theorem B7374131 : Blo 2183435 7374131 := bstep (se 1 (by rfl) ⟨5530598, by rfl⟩ : syracuseStep 7374131 = 11061197) B11061197
theorem B4916087 : Blo 2183435 4916087 := bstep (se 1 (by rfl) ⟨3687065, by rfl⟩ : syracuseStep 4916087 = 7374131) B7374131
theorem B3277391 : Blo 2183435 3277391 := bstep (se 1 (by rfl) ⟨2458043, by rfl⟩ : syracuseStep 3277391 = 4916087) B4916087
theorem B2184927 : Blo 2183435 2184927 := bstep (se 1 (by rfl) ⟨1638695, by rfl⟩ : syracuseStep 2184927 = 3277391) B3277391
theorem B3277397 : Blo 2183435 3277397 := bbase (se 8 (by rfl) ⟨19203, by rfl⟩ : syracuseStep 3277397 = 38407) (by norm_num)
theorem B2184931 : Blo 2183435 2184931 := bstep (se 1 (by rfl) ⟨1638698, by rfl⟩ : syracuseStep 2184931 = 3277397) B3277397
theorem B4429493 : Blo 2183435 4429493 := bbase (se 5 (by rfl) ⟨207632, by rfl⟩ : syracuseStep 4429493 = 415265) (by norm_num)
theorem B2952995 : Blo 2183435 2952995 := bstep (se 1 (by rfl) ⟨2214746, by rfl⟩ : syracuseStep 2952995 = 4429493) B4429493
theorem B7874653 : Blo 2183435 7874653 := bstep (se 3 (by rfl) ⟨1476497, by rfl⟩ : syracuseStep 7874653 = 2952995) B2952995
theorem B10499537 : Blo 2183435 10499537 := bstep (se 2 (by rfl) ⟨3937326, by rfl⟩ : syracuseStep 10499537 = 7874653) B7874653
theorem B6999691 : Blo 2183435 6999691 := bstep (se 1 (by rfl) ⟨5249768, by rfl⟩ : syracuseStep 6999691 = 10499537) B10499537
theorem B9332921 : Blo 2183435 9332921 := bstep (se 2 (by rfl) ⟨3499845, by rfl⟩ : syracuseStep 9332921 = 6999691) B6999691
theorem B6221947 : Blo 2183435 6221947 := bstep (se 1 (by rfl) ⟨4666460, by rfl⟩ : syracuseStep 6221947 = 9332921) B9332921
theorem B8295929 : Blo 2183435 8295929 := bstep (se 2 (by rfl) ⟨3110973, by rfl⟩ : syracuseStep 8295929 = 6221947) B6221947
theorem B5530619 : Blo 2183435 5530619 := bstep (se 1 (by rfl) ⟨4147964, by rfl⟩ : syracuseStep 5530619 = 8295929) B8295929
theorem B3687079 : Blo 2183435 3687079 := bstep (se 1 (by rfl) ⟨2765309, by rfl⟩ : syracuseStep 3687079 = 5530619) B5530619
theorem B4916105 : Blo 2183435 4916105 := bstep (se 2 (by rfl) ⟨1843539, by rfl⟩ : syracuseStep 4916105 = 3687079) B3687079
theorem B3277403 : Blo 2183435 3277403 := bstep (se 1 (by rfl) ⟨2458052, by rfl⟩ : syracuseStep 3277403 = 4916105) B4916105
theorem B2184935 : Blo 2183435 2184935 := bstep (se 1 (by rfl) ⟨1638701, by rfl⟩ : syracuseStep 2184935 = 3277403) B3277403
theorem B2458057 : Blo 2183435 2458057 := bbase (se 2 (by rfl) ⟨921771, by rfl⟩ : syracuseStep 2458057 = 1843543) (by norm_num)
theorem B3277409 : Blo 2183435 3277409 := bstep (se 2 (by rfl) ⟨1229028, by rfl⟩ : syracuseStep 3277409 = 2458057) B2458057
theorem B2184939 : Blo 2183435 2184939 := bstep (se 1 (by rfl) ⟨1638704, by rfl⟩ : syracuseStep 2184939 = 3277409) B3277409
theorem B18665909 : Blo 2183435 18665909 := bbase (se 5 (by rfl) ⟨874964, by rfl⟩ : syracuseStep 18665909 = 1749929) (by norm_num)
theorem B12443939 : Blo 2183435 12443939 := bstep (se 1 (by rfl) ⟨9332954, by rfl⟩ : syracuseStep 12443939 = 18665909) B18665909
theorem B8295959 : Blo 2183435 8295959 := bstep (se 1 (by rfl) ⟨6221969, by rfl⟩ : syracuseStep 8295959 = 12443939) B12443939
theorem B5530639 : Blo 2183435 5530639 := bstep (se 1 (by rfl) ⟨4147979, by rfl⟩ : syracuseStep 5530639 = 8295959) B8295959
theorem B7374185 : Blo 2183435 7374185 := bstep (se 2 (by rfl) ⟨2765319, by rfl⟩ : syracuseStep 7374185 = 5530639) B5530639
theorem B4916123 : Blo 2183435 4916123 := bstep (se 1 (by rfl) ⟨3687092, by rfl⟩ : syracuseStep 4916123 = 7374185) B7374185
theorem B3277415 : Blo 2183435 3277415 := bstep (se 1 (by rfl) ⟨2458061, by rfl⟩ : syracuseStep 3277415 = 4916123) B4916123
theorem B2184943 : Blo 2183435 2184943 := bstep (se 1 (by rfl) ⟨1638707, by rfl⟩ : syracuseStep 2184943 = 3277415) B3277415
theorem B3277421 : Blo 2183435 3277421 := bbase (se 3 (by rfl) ⟨614516, by rfl⟩ : syracuseStep 3277421 = 1229033) (by norm_num)
theorem B2184947 : Blo 2183435 2184947 := bstep (se 1 (by rfl) ⟨1638710, by rfl⟩ : syracuseStep 2184947 = 3277421) B3277421
theorem B4916141 : Blo 2183435 4916141 := bbase (se 3 (by rfl) ⟨921776, by rfl⟩ : syracuseStep 4916141 = 1843553) (by norm_num)
theorem B3277427 : Blo 2183435 3277427 := bstep (se 1 (by rfl) ⟨2458070, by rfl⟩ : syracuseStep 3277427 = 4916141) B4916141
theorem B2184951 : Blo 2183435 2184951 := bstep (se 1 (by rfl) ⟨1638713, by rfl⟩ : syracuseStep 2184951 = 3277427) B3277427
theorem B6222005 : Blo 2183435 6222005 := bbase (se 5 (by rfl) ⟨291656, by rfl⟩ : syracuseStep 6222005 = 583313) (by norm_num)
theorem B4148003 : Blo 2183435 4148003 := bstep (se 1 (by rfl) ⟨3111002, by rfl⟩ : syracuseStep 4148003 = 6222005) B6222005
theorem B2765335 : Blo 2183435 2765335 := bstep (se 1 (by rfl) ⟨2074001, by rfl⟩ : syracuseStep 2765335 = 4148003) B4148003
theorem B3687113 : Blo 2183435 3687113 := bstep (se 2 (by rfl) ⟨1382667, by rfl⟩ : syracuseStep 3687113 = 2765335) B2765335
theorem B2458075 : Blo 2183435 2458075 := bstep (se 1 (by rfl) ⟨1843556, by rfl⟩ : syracuseStep 2458075 = 3687113) B3687113
theorem B3277433 : Blo 2183435 3277433 := bstep (se 2 (by rfl) ⟨1229037, by rfl⟩ : syracuseStep 3277433 = 2458075) B2458075
theorem B2184955 : Blo 2183435 2184955 := bstep (se 1 (by rfl) ⟨1638716, by rfl⟩ : syracuseStep 2184955 = 3277433) B3277433
theorem B7095269 : Blo 2183435 7095269 := bbase (se 4 (by rfl) ⟨665181, by rfl⟩ : syracuseStep 7095269 = 1330363) (by norm_num)
theorem B4730179 : Blo 2183435 4730179 := bstep (se 1 (by rfl) ⟨3547634, by rfl⟩ : syracuseStep 4730179 = 7095269) B7095269
theorem B6306905 : Blo 2183435 6306905 := bstep (se 2 (by rfl) ⟨2365089, by rfl⟩ : syracuseStep 6306905 = 4730179) B4730179
theorem B4204603 : Blo 2183435 4204603 := bstep (se 1 (by rfl) ⟨3153452, by rfl⟩ : syracuseStep 4204603 = 6306905) B6306905
theorem B5606137 : Blo 2183435 5606137 := bstep (se 2 (by rfl) ⟨2102301, by rfl⟩ : syracuseStep 5606137 = 4204603) B4204603
theorem B7474849 : Blo 2183435 7474849 := bstep (se 2 (by rfl) ⟨2803068, by rfl⟩ : syracuseStep 7474849 = 5606137) B5606137
theorem B39865861 : Blo 2183435 39865861 := bstep (se 4 (by rfl) ⟨3737424, by rfl⟩ : syracuseStep 39865861 = 7474849) B7474849
theorem B53154481 : Blo 2183435 53154481 := bstep (se 2 (by rfl) ⟨19932930, by rfl⟩ : syracuseStep 53154481 = 39865861) B39865861
theorem B70872641 : Blo 2183435 70872641 := bstep (se 2 (by rfl) ⟨26577240, by rfl⟩ : syracuseStep 70872641 = 53154481) B53154481
theorem B47248427 : Blo 2183435 47248427 := bstep (se 1 (by rfl) ⟨35436320, by rfl⟩ : syracuseStep 47248427 = 70872641) B70872641
theorem B31498951 : Blo 2183435 31498951 := bstep (se 1 (by rfl) ⟨23624213, by rfl⟩ : syracuseStep 31498951 = 47248427) B47248427
theorem B41998601 : Blo 2183435 41998601 := bstep (se 2 (by rfl) ⟨15749475, by rfl⟩ : syracuseStep 41998601 = 31498951) B31498951
theorem B27999067 : Blo 2183435 27999067 := bstep (se 1 (by rfl) ⟨20999300, by rfl⟩ : syracuseStep 27999067 = 41998601) B41998601
theorem B37332089 : Blo 2183435 37332089 := bstep (se 2 (by rfl) ⟨13999533, by rfl⟩ : syracuseStep 37332089 = 27999067) B27999067
theorem B24888059 : Blo 2183435 24888059 := bstep (se 1 (by rfl) ⟨18666044, by rfl⟩ : syracuseStep 24888059 = 37332089) B37332089
theorem B16592039 : Blo 2183435 16592039 := bstep (se 1 (by rfl) ⟨12444029, by rfl⟩ : syracuseStep 16592039 = 24888059) B24888059
theorem B11061359 : Blo 2183435 11061359 := bstep (se 1 (by rfl) ⟨8296019, by rfl⟩ : syracuseStep 11061359 = 16592039) B16592039
theorem B7374239 : Blo 2183435 7374239 := bstep (se 1 (by rfl) ⟨5530679, by rfl⟩ : syracuseStep 7374239 = 11061359) B11061359
theorem B4916159 : Blo 2183435 4916159 := bstep (se 1 (by rfl) ⟨3687119, by rfl⟩ : syracuseStep 4916159 = 7374239) B7374239
theorem B3277439 : Blo 2183435 3277439 := bstep (se 1 (by rfl) ⟨2458079, by rfl⟩ : syracuseStep 3277439 = 4916159) B4916159
theorem B2184959 : Blo 2183435 2184959 := bstep (se 1 (by rfl) ⟨1638719, by rfl⟩ : syracuseStep 2184959 = 3277439) B3277439
theorem B3277445 : Blo 2183435 3277445 := bbase (se 4 (by rfl) ⟨307260, by rfl⟩ : syracuseStep 3277445 = 614521) (by norm_num)
theorem B2184963 : Blo 2183435 2184963 := bstep (se 1 (by rfl) ⟨1638722, by rfl⟩ : syracuseStep 2184963 = 3277445) B3277445
theorem B3687133 : Blo 2183435 3687133 := bbase (se 3 (by rfl) ⟨691337, by rfl⟩ : syracuseStep 3687133 = 1382675) (by norm_num)
theorem B4916177 : Blo 2183435 4916177 := bstep (se 2 (by rfl) ⟨1843566, by rfl⟩ : syracuseStep 4916177 = 3687133) B3687133
theorem B3277451 : Blo 2183435 3277451 := bstep (se 1 (by rfl) ⟨2458088, by rfl⟩ : syracuseStep 3277451 = 4916177) B4916177
theorem B2184967 : Blo 2183435 2184967 := bstep (se 1 (by rfl) ⟨1638725, by rfl⟩ : syracuseStep 2184967 = 3277451) B3277451
theorem B2458093 : Blo 2183435 2458093 := bbase (se 3 (by rfl) ⟨460892, by rfl⟩ : syracuseStep 2458093 = 921785) (by norm_num)
theorem B3277457 : Blo 2183435 3277457 := bstep (se 2 (by rfl) ⟨1229046, by rfl⟩ : syracuseStep 3277457 = 2458093) B2458093
theorem B2184971 : Blo 2183435 2184971 := bstep (se 1 (by rfl) ⟨1638728, by rfl⟩ : syracuseStep 2184971 = 3277457) B3277457
theorem B7374293 : Blo 2183435 7374293 := bbase (se 7 (by rfl) ⟨86417, by rfl⟩ : syracuseStep 7374293 = 172835) (by norm_num)
theorem B4916195 : Blo 2183435 4916195 := bstep (se 1 (by rfl) ⟨3687146, by rfl⟩ : syracuseStep 4916195 = 7374293) B7374293
theorem B3277463 : Blo 2183435 3277463 := bstep (se 1 (by rfl) ⟨2458097, by rfl⟩ : syracuseStep 3277463 = 4916195) B4916195
theorem B2184975 : Blo 2183435 2184975 := bstep (se 1 (by rfl) ⟨1638731, by rfl⟩ : syracuseStep 2184975 = 3277463) B3277463
theorem B3277469 : Blo 2183435 3277469 := bbase (se 3 (by rfl) ⟨614525, by rfl⟩ : syracuseStep 3277469 = 1229051) (by norm_num)
theorem B2184979 : Blo 2183435 2184979 := bstep (se 1 (by rfl) ⟨1638734, by rfl⟩ : syracuseStep 2184979 = 3277469) B3277469
theorem B4916213 : Blo 2183435 4916213 := bbase (se 5 (by rfl) ⟨230447, by rfl⟩ : syracuseStep 4916213 = 460895) (by norm_num)
theorem B3277475 : Blo 2183435 3277475 := bstep (se 1 (by rfl) ⟨2458106, by rfl⟩ : syracuseStep 3277475 = 4916213) B4916213
theorem B2184983 : Blo 2183435 2184983 := bstep (se 1 (by rfl) ⟨1638737, by rfl⟩ : syracuseStep 2184983 = 3277475) B3277475
theorem B2803105 : Blo 2183435 2803105 := bbase (se 2 (by rfl) ⟨1051164, by rfl⟩ : syracuseStep 2803105 = 2102329) (by norm_num)
theorem B14949893 : Blo 2183435 14949893 := bstep (se 4 (by rfl) ⟨1401552, by rfl⟩ : syracuseStep 14949893 = 2803105) B2803105
theorem B9966595 : Blo 2183435 9966595 := bstep (se 1 (by rfl) ⟨7474946, by rfl⟩ : syracuseStep 9966595 = 14949893) B14949893
theorem B13288793 : Blo 2183435 13288793 := bstep (se 2 (by rfl) ⟨4983297, by rfl⟩ : syracuseStep 13288793 = 9966595) B9966595
theorem B35436781 : Blo 2183435 35436781 := bstep (se 3 (by rfl) ⟨6644396, by rfl⟩ : syracuseStep 35436781 = 13288793) B13288793
theorem B47249041 : Blo 2183435 47249041 := bstep (se 2 (by rfl) ⟨17718390, by rfl⟩ : syracuseStep 47249041 = 35436781) B35436781
theorem B62998721 : Blo 2183435 62998721 := bstep (se 2 (by rfl) ⟨23624520, by rfl⟩ : syracuseStep 62998721 = 47249041) B47249041
theorem B41999147 : Blo 2183435 41999147 := bstep (se 1 (by rfl) ⟨31499360, by rfl⟩ : syracuseStep 41999147 = 62998721) B62998721
theorem B27999431 : Blo 2183435 27999431 := bstep (se 1 (by rfl) ⟨20999573, by rfl⟩ : syracuseStep 27999431 = 41999147) B41999147
theorem B18666287 : Blo 2183435 18666287 := bstep (se 1 (by rfl) ⟨13999715, by rfl⟩ : syracuseStep 18666287 = 27999431) B27999431
theorem B12444191 : Blo 2183435 12444191 := bstep (se 1 (by rfl) ⟨9333143, by rfl⟩ : syracuseStep 12444191 = 18666287) B18666287
theorem B8296127 : Blo 2183435 8296127 := bstep (se 1 (by rfl) ⟨6222095, by rfl⟩ : syracuseStep 8296127 = 12444191) B12444191
theorem B5530751 : Blo 2183435 5530751 := bstep (se 1 (by rfl) ⟨4148063, by rfl⟩ : syracuseStep 5530751 = 8296127) B8296127
theorem B3687167 : Blo 2183435 3687167 := bstep (se 1 (by rfl) ⟨2765375, by rfl⟩ : syracuseStep 3687167 = 5530751) B5530751
theorem B2458111 : Blo 2183435 2458111 := bstep (se 1 (by rfl) ⟨1843583, by rfl⟩ : syracuseStep 2458111 = 3687167) B3687167
theorem B3277481 : Blo 2183435 3277481 := bstep (se 2 (by rfl) ⟨1229055, by rfl⟩ : syracuseStep 3277481 = 2458111) B2458111
theorem B2184987 : Blo 2183435 2184987 := bstep (se 1 (by rfl) ⟨1638740, by rfl⟩ : syracuseStep 2184987 = 3277481) B3277481
theorem B3111053 : Blo 2183435 3111053 := bbase (se 3 (by rfl) ⟨583322, by rfl⟩ : syracuseStep 3111053 = 1166645) (by norm_num)
theorem B8296141 : Blo 2183435 8296141 := bstep (se 3 (by rfl) ⟨1555526, by rfl⟩ : syracuseStep 8296141 = 3111053) B3111053
theorem B11061521 : Blo 2183435 11061521 := bstep (se 2 (by rfl) ⟨4148070, by rfl⟩ : syracuseStep 11061521 = 8296141) B8296141
theorem B7374347 : Blo 2183435 7374347 := bstep (se 1 (by rfl) ⟨5530760, by rfl⟩ : syracuseStep 7374347 = 11061521) B11061521
theorem B4916231 : Blo 2183435 4916231 := bstep (se 1 (by rfl) ⟨3687173, by rfl⟩ : syracuseStep 4916231 = 7374347) B7374347
theorem B3277487 : Blo 2183435 3277487 := bstep (se 1 (by rfl) ⟨2458115, by rfl⟩ : syracuseStep 3277487 = 4916231) B4916231
theorem B2184991 : Blo 2183435 2184991 := bstep (se 1 (by rfl) ⟨1638743, by rfl⟩ : syracuseStep 2184991 = 3277487) B3277487
theorem B3277493 : Blo 2183435 3277493 := bbase (se 5 (by rfl) ⟨153632, by rfl⟩ : syracuseStep 3277493 = 307265) (by norm_num)
theorem B2184995 : Blo 2183435 2184995 := bstep (se 1 (by rfl) ⟨1638746, by rfl⟩ : syracuseStep 2184995 = 3277493) B3277493
theorem B5530781 : Blo 2183435 5530781 := bbase (se 3 (by rfl) ⟨1037021, by rfl⟩ : syracuseStep 5530781 = 2074043) (by norm_num)
theorem B3687187 : Blo 2183435 3687187 := bstep (se 1 (by rfl) ⟨2765390, by rfl⟩ : syracuseStep 3687187 = 5530781) B5530781
theorem B4916249 : Blo 2183435 4916249 := bstep (se 2 (by rfl) ⟨1843593, by rfl⟩ : syracuseStep 4916249 = 3687187) B3687187
theorem B3277499 : Blo 2183435 3277499 := bstep (se 1 (by rfl) ⟨2458124, by rfl⟩ : syracuseStep 3277499 = 4916249) B4916249
theorem B2184999 : Blo 2183435 2184999 := bstep (se 1 (by rfl) ⟨1638749, by rfl⟩ : syracuseStep 2184999 = 3277499) B3277499
theorem B2458129 : Blo 2183435 2458129 := bbase (se 2 (by rfl) ⟨921798, by rfl⟩ : syracuseStep 2458129 = 1843597) (by norm_num)
theorem B3277505 : Blo 2183435 3277505 := bstep (se 2 (by rfl) ⟨1229064, by rfl⟩ : syracuseStep 3277505 = 2458129) B2458129
theorem B2185003 : Blo 2183435 2185003 := bstep (se 1 (by rfl) ⟨1638752, by rfl⟩ : syracuseStep 2185003 = 3277505) B3277505
theorem B4148101 : Blo 2183435 4148101 := bbase (se 4 (by rfl) ⟨388884, by rfl⟩ : syracuseStep 4148101 = 777769) (by norm_num)
theorem B5530801 : Blo 2183435 5530801 := bstep (se 2 (by rfl) ⟨2074050, by rfl⟩ : syracuseStep 5530801 = 4148101) B4148101
theorem B7374401 : Blo 2183435 7374401 := bstep (se 2 (by rfl) ⟨2765400, by rfl⟩ : syracuseStep 7374401 = 5530801) B5530801
theorem B4916267 : Blo 2183435 4916267 := bstep (se 1 (by rfl) ⟨3687200, by rfl⟩ : syracuseStep 4916267 = 7374401) B7374401
theorem B3277511 : Blo 2183435 3277511 := bstep (se 1 (by rfl) ⟨2458133, by rfl⟩ : syracuseStep 3277511 = 4916267) B4916267
theorem B2185007 : Blo 2183435 2185007 := bstep (se 1 (by rfl) ⟨1638755, by rfl⟩ : syracuseStep 2185007 = 3277511) B3277511
theorem B3277517 : Blo 2183435 3277517 := bbase (se 3 (by rfl) ⟨614534, by rfl⟩ : syracuseStep 3277517 = 1229069) (by norm_num)
theorem B2185011 : Blo 2183435 2185011 := bstep (se 1 (by rfl) ⟨1638758, by rfl⟩ : syracuseStep 2185011 = 3277517) B3277517
theorem B4916285 : Blo 2183435 4916285 := bbase (se 3 (by rfl) ⟨921803, by rfl⟩ : syracuseStep 4916285 = 1843607) (by norm_num)
theorem B3277523 : Blo 2183435 3277523 := bstep (se 1 (by rfl) ⟨2458142, by rfl⟩ : syracuseStep 3277523 = 4916285) B4916285
theorem B2185015 : Blo 2183435 2185015 := bstep (se 1 (by rfl) ⟨1638761, by rfl⟩ : syracuseStep 2185015 = 3277523) B3277523
theorem B3687221 : Blo 2183435 3687221 := bbase (se 5 (by rfl) ⟨172838, by rfl⟩ : syracuseStep 3687221 = 345677) (by norm_num)
theorem B2458147 : Blo 2183435 2458147 := bstep (se 1 (by rfl) ⟨1843610, by rfl⟩ : syracuseStep 2458147 = 3687221) B3687221
theorem B3277529 : Blo 2183435 3277529 := bstep (se 2 (by rfl) ⟨1229073, by rfl⟩ : syracuseStep 3277529 = 2458147) B2458147
theorem B2185019 : Blo 2183435 2185019 := bstep (se 1 (by rfl) ⟨1638764, by rfl⟩ : syracuseStep 2185019 = 3277529) B3277529
theorem B6222197 : Blo 2183435 6222197 := bbase (se 5 (by rfl) ⟨291665, by rfl⟩ : syracuseStep 6222197 = 583331) (by norm_num)
theorem B16592525 : Blo 2183435 16592525 := bstep (se 3 (by rfl) ⟨3111098, by rfl⟩ : syracuseStep 16592525 = 6222197) B6222197
theorem B11061683 : Blo 2183435 11061683 := bstep (se 1 (by rfl) ⟨8296262, by rfl⟩ : syracuseStep 11061683 = 16592525) B16592525
theorem B7374455 : Blo 2183435 7374455 := bstep (se 1 (by rfl) ⟨5530841, by rfl⟩ : syracuseStep 7374455 = 11061683) B11061683
theorem B4916303 : Blo 2183435 4916303 := bstep (se 1 (by rfl) ⟨3687227, by rfl⟩ : syracuseStep 4916303 = 7374455) B7374455
theorem B3277535 : Blo 2183435 3277535 := bstep (se 1 (by rfl) ⟨2458151, by rfl⟩ : syracuseStep 3277535 = 4916303) B4916303
theorem B2185023 : Blo 2183435 2185023 := bstep (se 1 (by rfl) ⟨1638767, by rfl⟩ : syracuseStep 2185023 = 3277535) B3277535
theorem B3277541 : Blo 2183435 3277541 := bbase (se 4 (by rfl) ⟨307269, by rfl⟩ : syracuseStep 3277541 = 614539) (by norm_num)
theorem B2185027 : Blo 2183435 2185027 := bstep (se 1 (by rfl) ⟨1638770, by rfl⟩ : syracuseStep 2185027 = 3277541) B3277541
theorem B2333333 : Blo 2183435 2333333 := bbase (se 6 (by rfl) ⟨54687, by rfl⟩ : syracuseStep 2333333 = 109375) (by norm_num)
theorem B6222221 : Blo 2183435 6222221 := bstep (se 3 (by rfl) ⟨1166666, by rfl⟩ : syracuseStep 6222221 = 2333333) B2333333
theorem B4148147 : Blo 2183435 4148147 := bstep (se 1 (by rfl) ⟨3111110, by rfl⟩ : syracuseStep 4148147 = 6222221) B6222221
theorem B2765431 : Blo 2183435 2765431 := bstep (se 1 (by rfl) ⟨2074073, by rfl⟩ : syracuseStep 2765431 = 4148147) B4148147
theorem B3687241 : Blo 2183435 3687241 := bstep (se 2 (by rfl) ⟨1382715, by rfl⟩ : syracuseStep 3687241 = 2765431) B2765431
theorem B4916321 : Blo 2183435 4916321 := bstep (se 2 (by rfl) ⟨1843620, by rfl⟩ : syracuseStep 4916321 = 3687241) B3687241
theorem B3277547 : Blo 2183435 3277547 := bstep (se 1 (by rfl) ⟨2458160, by rfl⟩ : syracuseStep 3277547 = 4916321) B4916321
theorem B2185031 : Blo 2183435 2185031 := bstep (se 1 (by rfl) ⟨1638773, by rfl⟩ : syracuseStep 2185031 = 3277547) B3277547
theorem B2458165 : Blo 2183435 2458165 := bbase (se 5 (by rfl) ⟨115226, by rfl⟩ : syracuseStep 2458165 = 230453) (by norm_num)
theorem B3277553 : Blo 2183435 3277553 := bstep (se 2 (by rfl) ⟨1229082, by rfl⟩ : syracuseStep 3277553 = 2458165) B2458165
theorem B2185035 : Blo 2183435 2185035 := bstep (se 1 (by rfl) ⟨1638776, by rfl⟩ : syracuseStep 2185035 = 3277553) B3277553
theorem B2765441 : Blo 2183435 2765441 := bbase (se 2 (by rfl) ⟨1037040, by rfl⟩ : syracuseStep 2765441 = 2074081) (by norm_num)
theorem B7374509 : Blo 2183435 7374509 := bstep (se 3 (by rfl) ⟨1382720, by rfl⟩ : syracuseStep 7374509 = 2765441) B2765441
theorem B4916339 : Blo 2183435 4916339 := bstep (se 1 (by rfl) ⟨3687254, by rfl⟩ : syracuseStep 4916339 = 7374509) B7374509
theorem B3277559 : Blo 2183435 3277559 := bstep (se 1 (by rfl) ⟨2458169, by rfl⟩ : syracuseStep 3277559 = 4916339) B4916339
theorem B2185039 : Blo 2183435 2185039 := bstep (se 1 (by rfl) ⟨1638779, by rfl⟩ : syracuseStep 2185039 = 3277559) B3277559
theorem B3277565 : Blo 2183435 3277565 := bbase (se 3 (by rfl) ⟨614543, by rfl⟩ : syracuseStep 3277565 = 1229087) (by norm_num)
theorem B2185043 : Blo 2183435 2185043 := bstep (se 1 (by rfl) ⟨1638782, by rfl⟩ : syracuseStep 2185043 = 3277565) B3277565
theorem B4916357 : Blo 2183435 4916357 := bbase (se 4 (by rfl) ⟨460908, by rfl⟩ : syracuseStep 4916357 = 921817) (by norm_num)
theorem B3277571 : Blo 2183435 3277571 := bstep (se 1 (by rfl) ⟨2458178, by rfl⟩ : syracuseStep 3277571 = 4916357) B4916357
theorem B2185047 : Blo 2183435 2185047 := bstep (se 1 (by rfl) ⟨1638785, by rfl⟩ : syracuseStep 2185047 = 3277571) B3277571
theorem B4666709 : Blo 2183435 4666709 := bbase (se 13 (by rfl) ⟨854, by rfl⟩ : syracuseStep 4666709 = 1709) (by norm_num)
theorem B3111139 : Blo 2183435 3111139 := bstep (se 1 (by rfl) ⟨2333354, by rfl⟩ : syracuseStep 3111139 = 4666709) B4666709
theorem B4148185 : Blo 2183435 4148185 := bstep (se 2 (by rfl) ⟨1555569, by rfl⟩ : syracuseStep 4148185 = 3111139) B3111139
theorem B5530913 : Blo 2183435 5530913 := bstep (se 2 (by rfl) ⟨2074092, by rfl⟩ : syracuseStep 5530913 = 4148185) B4148185
theorem B3687275 : Blo 2183435 3687275 := bstep (se 1 (by rfl) ⟨2765456, by rfl⟩ : syracuseStep 3687275 = 5530913) B5530913
theorem B2458183 : Blo 2183435 2458183 := bstep (se 1 (by rfl) ⟨1843637, by rfl⟩ : syracuseStep 2458183 = 3687275) B3687275
theorem B3277577 : Blo 2183435 3277577 := bstep (se 2 (by rfl) ⟨1229091, by rfl⟩ : syracuseStep 3277577 = 2458183) B2458183
theorem B2185051 : Blo 2183435 2185051 := bstep (se 1 (by rfl) ⟨1638788, by rfl⟩ : syracuseStep 2185051 = 3277577) B3277577
theorem B11061845 : Blo 2183435 11061845 := bbase (se 8 (by rfl) ⟨64815, by rfl⟩ : syracuseStep 11061845 = 129631) (by norm_num)
theorem B7374563 : Blo 2183435 7374563 := bstep (se 1 (by rfl) ⟨5530922, by rfl⟩ : syracuseStep 7374563 = 11061845) B11061845
theorem B4916375 : Blo 2183435 4916375 := bstep (se 1 (by rfl) ⟨3687281, by rfl⟩ : syracuseStep 4916375 = 7374563) B7374563
theorem B3277583 : Blo 2183435 3277583 := bstep (se 1 (by rfl) ⟨2458187, by rfl⟩ : syracuseStep 3277583 = 4916375) B4916375
theorem B2185055 : Blo 2183435 2185055 := bstep (se 1 (by rfl) ⟨1638791, by rfl⟩ : syracuseStep 2185055 = 3277583) B3277583
theorem B3277589 : Blo 2183435 3277589 := bbase (se 6 (by rfl) ⟨76818, by rfl⟩ : syracuseStep 3277589 = 153637) (by norm_num)
theorem B2185059 : Blo 2183435 2185059 := bstep (se 1 (by rfl) ⟨1638794, by rfl⟩ : syracuseStep 2185059 = 3277589) B3277589
theorem B4320325 : Blo 2183435 4320325 := bbase (se 4 (by rfl) ⟨405030, by rfl⟩ : syracuseStep 4320325 = 810061) (by norm_num)
theorem B5760433 : Blo 2183435 5760433 := bstep (se 2 (by rfl) ⟨2160162, by rfl⟩ : syracuseStep 5760433 = 4320325) B4320325
theorem B7680577 : Blo 2183435 7680577 := bstep (se 2 (by rfl) ⟨2880216, by rfl⟩ : syracuseStep 7680577 = 5760433) B5760433
theorem B10240769 : Blo 2183435 10240769 := bstep (se 2 (by rfl) ⟨3840288, by rfl⟩ : syracuseStep 10240769 = 7680577) B7680577
theorem B6827179 : Blo 2183435 6827179 := bstep (se 1 (by rfl) ⟨5120384, by rfl⟩ : syracuseStep 6827179 = 10240769) B10240769
theorem B9102905 : Blo 2183435 9102905 := bstep (se 2 (by rfl) ⟨3413589, by rfl⟩ : syracuseStep 9102905 = 6827179) B6827179
theorem B6068603 : Blo 2183435 6068603 := bstep (se 1 (by rfl) ⟨4551452, by rfl⟩ : syracuseStep 6068603 = 9102905) B9102905
theorem B4045735 : Blo 2183435 4045735 := bstep (se 1 (by rfl) ⟨3034301, by rfl⟩ : syracuseStep 4045735 = 6068603) B6068603
theorem B5394313 : Blo 2183435 5394313 := bstep (se 2 (by rfl) ⟨2022867, by rfl⟩ : syracuseStep 5394313 = 4045735) B4045735
theorem B7192417 : Blo 2183435 7192417 := bstep (se 2 (by rfl) ⟨2697156, by rfl⟩ : syracuseStep 7192417 = 5394313) B5394313
theorem B9589889 : Blo 2183435 9589889 := bstep (se 2 (by rfl) ⟨3596208, by rfl⟩ : syracuseStep 9589889 = 7192417) B7192417
theorem B6393259 : Blo 2183435 6393259 := bstep (se 1 (by rfl) ⟨4794944, by rfl⟩ : syracuseStep 6393259 = 9589889) B9589889
theorem B34097381 : Blo 2183435 34097381 := bstep (se 4 (by rfl) ⟨3196629, by rfl⟩ : syracuseStep 34097381 = 6393259) B6393259
theorem B22731587 : Blo 2183435 22731587 := bstep (se 1 (by rfl) ⟨17048690, by rfl⟩ : syracuseStep 22731587 = 34097381) B34097381
theorem B15154391 : Blo 2183435 15154391 := bstep (se 1 (by rfl) ⟨11365793, by rfl⟩ : syracuseStep 15154391 = 22731587) B22731587
theorem B10102927 : Blo 2183435 10102927 := bstep (se 1 (by rfl) ⟨7577195, by rfl⟩ : syracuseStep 10102927 = 15154391) B15154391
theorem B13470569 : Blo 2183435 13470569 := bstep (se 2 (by rfl) ⟨5051463, by rfl⟩ : syracuseStep 13470569 = 10102927) B10102927
theorem B8980379 : Blo 2183435 8980379 := bstep (se 1 (by rfl) ⟨6735284, by rfl⟩ : syracuseStep 8980379 = 13470569) B13470569
theorem B5986919 : Blo 2183435 5986919 := bstep (se 1 (by rfl) ⟨4490189, by rfl⟩ : syracuseStep 5986919 = 8980379) B8980379
theorem B3991279 : Blo 2183435 3991279 := bstep (se 1 (by rfl) ⟨2993459, by rfl⟩ : syracuseStep 3991279 = 5986919) B5986919
theorem B5321705 : Blo 2183435 5321705 := bstep (se 2 (by rfl) ⟨1995639, by rfl⟩ : syracuseStep 5321705 = 3991279) B3991279
theorem B14191213 : Blo 2183435 14191213 := bstep (se 3 (by rfl) ⟨2660852, by rfl⟩ : syracuseStep 14191213 = 5321705) B5321705
theorem B18921617 : Blo 2183435 18921617 := bstep (se 2 (by rfl) ⟨7095606, by rfl⟩ : syracuseStep 18921617 = 14191213) B14191213
theorem B12614411 : Blo 2183435 12614411 := bstep (se 1 (by rfl) ⟨9460808, by rfl⟩ : syracuseStep 12614411 = 18921617) B18921617
theorem B33638429 : Blo 2183435 33638429 := bstep (se 3 (by rfl) ⟨6307205, by rfl⟩ : syracuseStep 33638429 = 12614411) B12614411
theorem B22425619 : Blo 2183435 22425619 := bstep (se 1 (by rfl) ⟨16819214, by rfl⟩ : syracuseStep 22425619 = 33638429) B33638429
theorem B29900825 : Blo 2183435 29900825 := bstep (se 2 (by rfl) ⟨11212809, by rfl⟩ : syracuseStep 29900825 = 22425619) B22425619
theorem B19933883 : Blo 2183435 19933883 := bstep (se 1 (by rfl) ⟨14950412, by rfl⟩ : syracuseStep 19933883 = 29900825) B29900825
theorem B13289255 : Blo 2183435 13289255 := bstep (se 1 (by rfl) ⟨9966941, by rfl⟩ : syracuseStep 13289255 = 19933883) B19933883
theorem B8859503 : Blo 2183435 8859503 := bstep (se 1 (by rfl) ⟨6644627, by rfl⟩ : syracuseStep 8859503 = 13289255) B13289255
theorem B23625341 : Blo 2183435 23625341 := bstep (se 3 (by rfl) ⟨4429751, by rfl⟩ : syracuseStep 23625341 = 8859503) B8859503
theorem B15750227 : Blo 2183435 15750227 := bstep (se 1 (by rfl) ⟨11812670, by rfl⟩ : syracuseStep 15750227 = 23625341) B23625341
theorem B42000605 : Blo 2183435 42000605 := bstep (se 3 (by rfl) ⟨7875113, by rfl⟩ : syracuseStep 42000605 = 15750227) B15750227
theorem B28000403 : Blo 2183435 28000403 := bstep (se 1 (by rfl) ⟨21000302, by rfl⟩ : syracuseStep 28000403 = 42000605) B42000605
theorem B18666935 : Blo 2183435 18666935 := bstep (se 1 (by rfl) ⟨14000201, by rfl⟩ : syracuseStep 18666935 = 28000403) B28000403
theorem B12444623 : Blo 2183435 12444623 := bstep (se 1 (by rfl) ⟨9333467, by rfl⟩ : syracuseStep 12444623 = 18666935) B18666935
theorem B8296415 : Blo 2183435 8296415 := bstep (se 1 (by rfl) ⟨6222311, by rfl⟩ : syracuseStep 8296415 = 12444623) B12444623
theorem B5530943 : Blo 2183435 5530943 := bstep (se 1 (by rfl) ⟨4148207, by rfl⟩ : syracuseStep 5530943 = 8296415) B8296415
theorem B3687295 : Blo 2183435 3687295 := bstep (se 1 (by rfl) ⟨2765471, by rfl⟩ : syracuseStep 3687295 = 5530943) B5530943
theorem B4916393 : Blo 2183435 4916393 := bstep (se 2 (by rfl) ⟨1843647, by rfl⟩ : syracuseStep 4916393 = 3687295) B3687295
theorem B3277595 : Blo 2183435 3277595 := bstep (se 1 (by rfl) ⟨2458196, by rfl⟩ : syracuseStep 3277595 = 4916393) B4916393
theorem B2185063 : Blo 2183435 2185063 := bstep (se 1 (by rfl) ⟨1638797, by rfl⟩ : syracuseStep 2185063 = 3277595) B3277595
theorem B2458201 : Blo 2183435 2458201 := bbase (se 2 (by rfl) ⟨921825, by rfl⟩ : syracuseStep 2458201 = 1843651) (by norm_num)
theorem B3277601 : Blo 2183435 3277601 := bstep (se 2 (by rfl) ⟨1229100, by rfl⟩ : syracuseStep 3277601 = 2458201) B2458201
theorem B2185067 : Blo 2183435 2185067 := bstep (se 1 (by rfl) ⟨1638800, by rfl⟩ : syracuseStep 2185067 = 3277601) B3277601
theorem B2803213 : Blo 2183435 2803213 := bbase (se 3 (by rfl) ⟨525602, by rfl⟩ : syracuseStep 2803213 = 1051205) (by norm_num)
theorem B14950469 : Blo 2183435 14950469 := bstep (se 4 (by rfl) ⟨1401606, by rfl⟩ : syracuseStep 14950469 = 2803213) B2803213
theorem B9966979 : Blo 2183435 9966979 := bstep (se 1 (by rfl) ⟨7475234, by rfl⟩ : syracuseStep 9966979 = 14950469) B14950469
theorem B53157221 : Blo 2183435 53157221 := bstep (se 4 (by rfl) ⟨4983489, by rfl⟩ : syracuseStep 53157221 = 9966979) B9966979
theorem B35438147 : Blo 2183435 35438147 := bstep (se 1 (by rfl) ⟨26578610, by rfl⟩ : syracuseStep 35438147 = 53157221) B53157221
theorem B23625431 : Blo 2183435 23625431 := bstep (se 1 (by rfl) ⟨17719073, by rfl⟩ : syracuseStep 23625431 = 35438147) B35438147
theorem B15750287 : Blo 2183435 15750287 := bstep (se 1 (by rfl) ⟨11812715, by rfl⟩ : syracuseStep 15750287 = 23625431) B23625431
theorem B10500191 : Blo 2183435 10500191 := bstep (se 1 (by rfl) ⟨7875143, by rfl⟩ : syracuseStep 10500191 = 15750287) B15750287
theorem B7000127 : Blo 2183435 7000127 := bstep (se 1 (by rfl) ⟨5250095, by rfl⟩ : syracuseStep 7000127 = 10500191) B10500191
theorem B4666751 : Blo 2183435 4666751 := bstep (se 1 (by rfl) ⟨3500063, by rfl⟩ : syracuseStep 4666751 = 7000127) B7000127
theorem B3111167 : Blo 2183435 3111167 := bstep (se 1 (by rfl) ⟨2333375, by rfl⟩ : syracuseStep 3111167 = 4666751) B4666751
theorem B8296445 : Blo 2183435 8296445 := bstep (se 3 (by rfl) ⟨1555583, by rfl⟩ : syracuseStep 8296445 = 3111167) B3111167
theorem B5530963 : Blo 2183435 5530963 := bstep (se 1 (by rfl) ⟨4148222, by rfl⟩ : syracuseStep 5530963 = 8296445) B8296445
theorem B7374617 : Blo 2183435 7374617 := bstep (se 2 (by rfl) ⟨2765481, by rfl⟩ : syracuseStep 7374617 = 5530963) B5530963
theorem B4916411 : Blo 2183435 4916411 := bstep (se 1 (by rfl) ⟨3687308, by rfl⟩ : syracuseStep 4916411 = 7374617) B7374617
theorem B3277607 : Blo 2183435 3277607 := bstep (se 1 (by rfl) ⟨2458205, by rfl⟩ : syracuseStep 3277607 = 4916411) B4916411
theorem B2185071 : Blo 2183435 2185071 := bstep (se 1 (by rfl) ⟨1638803, by rfl⟩ : syracuseStep 2185071 = 3277607) B3277607
theorem B3277613 : Blo 2183435 3277613 := bbase (se 3 (by rfl) ⟨614552, by rfl⟩ : syracuseStep 3277613 = 1229105) (by norm_num)
theorem B2185075 : Blo 2183435 2185075 := bstep (se 1 (by rfl) ⟨1638806, by rfl⟩ : syracuseStep 2185075 = 3277613) B3277613
theorem B4916429 : Blo 2183435 4916429 := bbase (se 3 (by rfl) ⟨921830, by rfl⟩ : syracuseStep 4916429 = 1843661) (by norm_num)
theorem B3277619 : Blo 2183435 3277619 := bstep (se 1 (by rfl) ⟨2458214, by rfl⟩ : syracuseStep 3277619 = 4916429) B4916429
theorem B2185079 : Blo 2183435 2185079 := bstep (se 1 (by rfl) ⟨1638809, by rfl⟩ : syracuseStep 2185079 = 3277619) B3277619
theorem B2765497 : Blo 2183435 2765497 := bbase (se 2 (by rfl) ⟨1037061, by rfl⟩ : syracuseStep 2765497 = 2074123) (by norm_num)
theorem B3687329 : Blo 2183435 3687329 := bstep (se 2 (by rfl) ⟨1382748, by rfl⟩ : syracuseStep 3687329 = 2765497) B2765497
theorem B2458219 : Blo 2183435 2458219 := bstep (se 1 (by rfl) ⟨1843664, by rfl⟩ : syracuseStep 2458219 = 3687329) B3687329
theorem B3277625 : Blo 2183435 3277625 := bstep (se 2 (by rfl) ⟨1229109, by rfl⟩ : syracuseStep 3277625 = 2458219) B2458219
theorem B2185083 : Blo 2183435 2185083 := bstep (se 1 (by rfl) ⟨1638812, by rfl⟩ : syracuseStep 2185083 = 3277625) B3277625
theorem B5250133 : Blo 2183435 5250133 := bbase (se 8 (by rfl) ⟨30762, by rfl⟩ : syracuseStep 5250133 = 61525) (by norm_num)
theorem B7000177 : Blo 2183435 7000177 := bstep (se 2 (by rfl) ⟨2625066, by rfl⟩ : syracuseStep 7000177 = 5250133) B5250133
theorem B9333569 : Blo 2183435 9333569 := bstep (se 2 (by rfl) ⟨3500088, by rfl⟩ : syracuseStep 9333569 = 7000177) B7000177
theorem B24889517 : Blo 2183435 24889517 := bstep (se 3 (by rfl) ⟨4666784, by rfl⟩ : syracuseStep 24889517 = 9333569) B9333569
theorem B16593011 : Blo 2183435 16593011 := bstep (se 1 (by rfl) ⟨12444758, by rfl⟩ : syracuseStep 16593011 = 24889517) B24889517
theorem B11062007 : Blo 2183435 11062007 := bstep (se 1 (by rfl) ⟨8296505, by rfl⟩ : syracuseStep 11062007 = 16593011) B16593011
theorem B7374671 : Blo 2183435 7374671 := bstep (se 1 (by rfl) ⟨5531003, by rfl⟩ : syracuseStep 7374671 = 11062007) B11062007
theorem B4916447 : Blo 2183435 4916447 := bstep (se 1 (by rfl) ⟨3687335, by rfl⟩ : syracuseStep 4916447 = 7374671) B7374671
theorem B3277631 : Blo 2183435 3277631 := bstep (se 1 (by rfl) ⟨2458223, by rfl⟩ : syracuseStep 3277631 = 4916447) B4916447
theorem B2185087 : Blo 2183435 2185087 := bstep (se 1 (by rfl) ⟨1638815, by rfl⟩ : syracuseStep 2185087 = 3277631) B3277631
theorem B3277637 : Blo 2183435 3277637 := bbase (se 4 (by rfl) ⟨307278, by rfl⟩ : syracuseStep 3277637 = 614557) (by norm_num)
theorem B2185091 : Blo 2183435 2185091 := bstep (se 1 (by rfl) ⟨1638818, by rfl⟩ : syracuseStep 2185091 = 3277637) B3277637
theorem B3687349 : Blo 2183435 3687349 := bbase (se 5 (by rfl) ⟨172844, by rfl⟩ : syracuseStep 3687349 = 345689) (by norm_num)
theorem B4916465 : Blo 2183435 4916465 := bstep (se 2 (by rfl) ⟨1843674, by rfl⟩ : syracuseStep 4916465 = 3687349) B3687349
theorem B3277643 : Blo 2183435 3277643 := bstep (se 1 (by rfl) ⟨2458232, by rfl⟩ : syracuseStep 3277643 = 4916465) B4916465
theorem B2185095 : Blo 2183435 2185095 := bstep (se 1 (by rfl) ⟨1638821, by rfl⟩ : syracuseStep 2185095 = 3277643) B3277643
theorem B2458237 : Blo 2183435 2458237 := bbase (se 3 (by rfl) ⟨460919, by rfl⟩ : syracuseStep 2458237 = 921839) (by norm_num)
theorem B3277649 : Blo 2183435 3277649 := bstep (se 2 (by rfl) ⟨1229118, by rfl⟩ : syracuseStep 3277649 = 2458237) B2458237
theorem B2185099 : Blo 2183435 2185099 := bstep (se 1 (by rfl) ⟨1638824, by rfl⟩ : syracuseStep 2185099 = 3277649) B3277649
theorem B7374725 : Blo 2183435 7374725 := bbase (se 4 (by rfl) ⟨691380, by rfl⟩ : syracuseStep 7374725 = 1382761) (by norm_num)
theorem B4916483 : Blo 2183435 4916483 := bstep (se 1 (by rfl) ⟨3687362, by rfl⟩ : syracuseStep 4916483 = 7374725) B7374725
theorem B3277655 : Blo 2183435 3277655 := bstep (se 1 (by rfl) ⟨2458241, by rfl⟩ : syracuseStep 3277655 = 4916483) B4916483
theorem B2185103 : Blo 2183435 2185103 := bstep (se 1 (by rfl) ⟨1638827, by rfl⟩ : syracuseStep 2185103 = 3277655) B3277655
theorem B3277661 : Blo 2183435 3277661 := bbase (se 3 (by rfl) ⟨614561, by rfl⟩ : syracuseStep 3277661 = 1229123) (by norm_num)
theorem B2185107 : Blo 2183435 2185107 := bstep (se 1 (by rfl) ⟨1638830, by rfl⟩ : syracuseStep 2185107 = 3277661) B3277661
theorem B4916501 : Blo 2183435 4916501 := bbase (se 6 (by rfl) ⟨115230, by rfl⟩ : syracuseStep 4916501 = 230461) (by norm_num)
theorem B3277667 : Blo 2183435 3277667 := bstep (se 1 (by rfl) ⟨2458250, by rfl⟩ : syracuseStep 3277667 = 4916501) B4916501
theorem B2185111 : Blo 2183435 2185111 := bstep (se 1 (by rfl) ⟨1638833, by rfl⟩ : syracuseStep 2185111 = 3277667) B3277667
theorem B8296613 : Blo 2183435 8296613 := bbase (se 4 (by rfl) ⟨777807, by rfl⟩ : syracuseStep 8296613 = 1555615) (by norm_num)
theorem B5531075 : Blo 2183435 5531075 := bstep (se 1 (by rfl) ⟨4148306, by rfl⟩ : syracuseStep 5531075 = 8296613) B8296613
theorem B3687383 : Blo 2183435 3687383 := bstep (se 1 (by rfl) ⟨2765537, by rfl⟩ : syracuseStep 3687383 = 5531075) B5531075
theorem B2458255 : Blo 2183435 2458255 := bstep (se 1 (by rfl) ⟨1843691, by rfl⟩ : syracuseStep 2458255 = 3687383) B3687383
theorem B3277673 : Blo 2183435 3277673 := bstep (se 2 (by rfl) ⟨1229127, by rfl⟩ : syracuseStep 3277673 = 2458255) B2458255
theorem B2185115 : Blo 2183435 2185115 := bstep (se 1 (by rfl) ⟨1638836, by rfl⟩ : syracuseStep 2185115 = 3277673) B3277673
theorem B4666853 : Blo 2183435 4666853 := bbase (se 4 (by rfl) ⟨437517, by rfl⟩ : syracuseStep 4666853 = 875035) (by norm_num)
theorem B12444941 : Blo 2183435 12444941 := bstep (se 3 (by rfl) ⟨2333426, by rfl⟩ : syracuseStep 12444941 = 4666853) B4666853
theorem B8296627 : Blo 2183435 8296627 := bstep (se 1 (by rfl) ⟨6222470, by rfl⟩ : syracuseStep 8296627 = 12444941) B12444941
theorem B11062169 : Blo 2183435 11062169 := bstep (se 2 (by rfl) ⟨4148313, by rfl⟩ : syracuseStep 11062169 = 8296627) B8296627
theorem B7374779 : Blo 2183435 7374779 := bstep (se 1 (by rfl) ⟨5531084, by rfl⟩ : syracuseStep 7374779 = 11062169) B11062169
theorem B4916519 : Blo 2183435 4916519 := bstep (se 1 (by rfl) ⟨3687389, by rfl⟩ : syracuseStep 4916519 = 7374779) B7374779
theorem B3277679 : Blo 2183435 3277679 := bstep (se 1 (by rfl) ⟨2458259, by rfl⟩ : syracuseStep 3277679 = 4916519) B4916519
theorem B2185119 : Blo 2183435 2185119 := bstep (se 1 (by rfl) ⟨1638839, by rfl⟩ : syracuseStep 2185119 = 3277679) B3277679
theorem B3277685 : Blo 2183435 3277685 := bbase (se 5 (by rfl) ⟨153641, by rfl⟩ : syracuseStep 3277685 = 307283) (by norm_num)
theorem B2185123 : Blo 2183435 2185123 := bstep (se 1 (by rfl) ⟨1638842, by rfl⟩ : syracuseStep 2185123 = 3277685) B3277685
theorem B7475429 : Blo 2183435 7475429 := bbase (se 4 (by rfl) ⟨700821, by rfl⟩ : syracuseStep 7475429 = 1401643) (by norm_num)
theorem B4983619 : Blo 2183435 4983619 := bstep (se 1 (by rfl) ⟨3737714, by rfl⟩ : syracuseStep 4983619 = 7475429) B7475429
theorem B6644825 : Blo 2183435 6644825 := bstep (se 2 (by rfl) ⟨2491809, by rfl⟩ : syracuseStep 6644825 = 4983619) B4983619
theorem B4429883 : Blo 2183435 4429883 := bstep (se 1 (by rfl) ⟨3322412, by rfl⟩ : syracuseStep 4429883 = 6644825) B6644825
theorem B2953255 : Blo 2183435 2953255 := bstep (se 1 (by rfl) ⟨2214941, by rfl⟩ : syracuseStep 2953255 = 4429883) B4429883
theorem B3937673 : Blo 2183435 3937673 := bstep (se 2 (by rfl) ⟨1476627, by rfl⟩ : syracuseStep 3937673 = 2953255) B2953255
theorem B10500461 : Blo 2183435 10500461 := bstep (se 3 (by rfl) ⟨1968836, by rfl⟩ : syracuseStep 10500461 = 3937673) B3937673
theorem B7000307 : Blo 2183435 7000307 := bstep (se 1 (by rfl) ⟨5250230, by rfl⟩ : syracuseStep 7000307 = 10500461) B10500461
theorem B4666871 : Blo 2183435 4666871 := bstep (se 1 (by rfl) ⟨3500153, by rfl⟩ : syracuseStep 4666871 = 7000307) B7000307
theorem B3111247 : Blo 2183435 3111247 := bstep (se 1 (by rfl) ⟨2333435, by rfl⟩ : syracuseStep 3111247 = 4666871) B4666871
theorem B4148329 : Blo 2183435 4148329 := bstep (se 2 (by rfl) ⟨1555623, by rfl⟩ : syracuseStep 4148329 = 3111247) B3111247
theorem B5531105 : Blo 2183435 5531105 := bstep (se 2 (by rfl) ⟨2074164, by rfl⟩ : syracuseStep 5531105 = 4148329) B4148329
theorem B3687403 : Blo 2183435 3687403 := bstep (se 1 (by rfl) ⟨2765552, by rfl⟩ : syracuseStep 3687403 = 5531105) B5531105
theorem B4916537 : Blo 2183435 4916537 := bstep (se 2 (by rfl) ⟨1843701, by rfl⟩ : syracuseStep 4916537 = 3687403) B3687403
theorem B3277691 : Blo 2183435 3277691 := bstep (se 1 (by rfl) ⟨2458268, by rfl⟩ : syracuseStep 3277691 = 4916537) B4916537
theorem B2185127 : Blo 2183435 2185127 := bstep (se 1 (by rfl) ⟨1638845, by rfl⟩ : syracuseStep 2185127 = 3277691) B3277691
theorem B2458273 : Blo 2183435 2458273 := bbase (se 2 (by rfl) ⟨921852, by rfl⟩ : syracuseStep 2458273 = 1843705) (by norm_num)
theorem B3277697 : Blo 2183435 3277697 := bstep (se 2 (by rfl) ⟨1229136, by rfl⟩ : syracuseStep 3277697 = 2458273) B2458273
theorem B2185131 : Blo 2183435 2185131 := bstep (se 1 (by rfl) ⟨1638848, by rfl⟩ : syracuseStep 2185131 = 3277697) B3277697
theorem B5531125 : Blo 2183435 5531125 := bbase (se 5 (by rfl) ⟨259271, by rfl⟩ : syracuseStep 5531125 = 518543) (by norm_num)
theorem B7374833 : Blo 2183435 7374833 := bstep (se 2 (by rfl) ⟨2765562, by rfl⟩ : syracuseStep 7374833 = 5531125) B5531125
theorem B4916555 : Blo 2183435 4916555 := bstep (se 1 (by rfl) ⟨3687416, by rfl⟩ : syracuseStep 4916555 = 7374833) B7374833
theorem B3277703 : Blo 2183435 3277703 := bstep (se 1 (by rfl) ⟨2458277, by rfl⟩ : syracuseStep 3277703 = 4916555) B4916555
theorem B2185135 : Blo 2183435 2185135 := bstep (se 1 (by rfl) ⟨1638851, by rfl⟩ : syracuseStep 2185135 = 3277703) B3277703
theorem B3277709 : Blo 2183435 3277709 := bbase (se 3 (by rfl) ⟨614570, by rfl⟩ : syracuseStep 3277709 = 1229141) (by norm_num)
theorem B2185139 : Blo 2183435 2185139 := bstep (se 1 (by rfl) ⟨1638854, by rfl⟩ : syracuseStep 2185139 = 3277709) B3277709
theorem B4916573 : Blo 2183435 4916573 := bbase (se 3 (by rfl) ⟨921857, by rfl⟩ : syracuseStep 4916573 = 1843715) (by norm_num)
theorem B3277715 : Blo 2183435 3277715 := bstep (se 1 (by rfl) ⟨2458286, by rfl⟩ : syracuseStep 3277715 = 4916573) B4916573
theorem B2185143 : Blo 2183435 2185143 := bstep (se 1 (by rfl) ⟨1638857, by rfl⟩ : syracuseStep 2185143 = 3277715) B3277715
theorem B3687437 : Blo 2183435 3687437 := bbase (se 3 (by rfl) ⟨691394, by rfl⟩ : syracuseStep 3687437 = 1382789) (by norm_num)
theorem B2458291 : Blo 2183435 2458291 := bstep (se 1 (by rfl) ⟨1843718, by rfl⟩ : syracuseStep 2458291 = 3687437) B3687437
theorem B3277721 : Blo 2183435 3277721 := bstep (se 2 (by rfl) ⟨1229145, by rfl⟩ : syracuseStep 3277721 = 2458291) B2458291
theorem B2185147 : Blo 2183435 2185147 := bstep (se 1 (by rfl) ⟨1638860, by rfl⟩ : syracuseStep 2185147 = 3277721) B3277721
theorem B2430281 : Blo 2183435 2430281 := bbase (se 2 (by rfl) ⟨911355, by rfl⟩ : syracuseStep 2430281 = 1822711) (by norm_num)
theorem B6480749 : Blo 2183435 6480749 := bstep (se 3 (by rfl) ⟨1215140, by rfl⟩ : syracuseStep 6480749 = 2430281) B2430281
theorem B4320499 : Blo 2183435 4320499 := bstep (se 1 (by rfl) ⟨3240374, by rfl⟩ : syracuseStep 4320499 = 6480749) B6480749
theorem B5760665 : Blo 2183435 5760665 := bstep (se 2 (by rfl) ⟨2160249, by rfl⟩ : syracuseStep 5760665 = 4320499) B4320499
theorem B3840443 : Blo 2183435 3840443 := bstep (se 1 (by rfl) ⟨2880332, by rfl⟩ : syracuseStep 3840443 = 5760665) B5760665
theorem B2560295 : Blo 2183435 2560295 := bstep (se 1 (by rfl) ⟨1920221, by rfl⟩ : syracuseStep 2560295 = 3840443) B3840443
theorem B6827453 : Blo 2183435 6827453 := bstep (se 3 (by rfl) ⟨1280147, by rfl⟩ : syracuseStep 6827453 = 2560295) B2560295
theorem B4551635 : Blo 2183435 4551635 := bstep (se 1 (by rfl) ⟨3413726, by rfl⟩ : syracuseStep 4551635 = 6827453) B6827453
theorem B3034423 : Blo 2183435 3034423 := bstep (se 1 (by rfl) ⟨2275817, by rfl⟩ : syracuseStep 3034423 = 4551635) B4551635
theorem B4045897 : Blo 2183435 4045897 := bstep (se 2 (by rfl) ⟨1517211, by rfl⟩ : syracuseStep 4045897 = 3034423) B3034423
theorem B5394529 : Blo 2183435 5394529 := bstep (se 2 (by rfl) ⟨2022948, by rfl⟩ : syracuseStep 5394529 = 4045897) B4045897
theorem B28770821 : Blo 2183435 28770821 := bstep (se 4 (by rfl) ⟨2697264, by rfl⟩ : syracuseStep 28770821 = 5394529) B5394529
theorem B19180547 : Blo 2183435 19180547 := bstep (se 1 (by rfl) ⟨14385410, by rfl⟩ : syracuseStep 19180547 = 28770821) B28770821
theorem B12787031 : Blo 2183435 12787031 := bstep (se 1 (by rfl) ⟨9590273, by rfl⟩ : syracuseStep 12787031 = 19180547) B19180547
theorem B8524687 : Blo 2183435 8524687 := bstep (se 1 (by rfl) ⟨6393515, by rfl⟩ : syracuseStep 8524687 = 12787031) B12787031
theorem B11366249 : Blo 2183435 11366249 := bstep (se 2 (by rfl) ⟨4262343, by rfl⟩ : syracuseStep 11366249 = 8524687) B8524687
theorem B30309997 : Blo 2183435 30309997 := bstep (se 3 (by rfl) ⟨5683124, by rfl⟩ : syracuseStep 30309997 = 11366249) B11366249
theorem B40413329 : Blo 2183435 40413329 := bstep (se 2 (by rfl) ⟨15154998, by rfl⟩ : syracuseStep 40413329 = 30309997) B30309997
theorem B26942219 : Blo 2183435 26942219 := bstep (se 1 (by rfl) ⟨20206664, by rfl⟩ : syracuseStep 26942219 = 40413329) B40413329
theorem B17961479 : Blo 2183435 17961479 := bstep (se 1 (by rfl) ⟨13471109, by rfl⟩ : syracuseStep 17961479 = 26942219) B26942219
theorem B11974319 : Blo 2183435 11974319 := bstep (se 1 (by rfl) ⟨8980739, by rfl⟩ : syracuseStep 11974319 = 17961479) B17961479
theorem B7982879 : Blo 2183435 7982879 := bstep (se 1 (by rfl) ⟨5987159, by rfl⟩ : syracuseStep 7982879 = 11974319) B11974319
theorem B85150709 : Blo 2183435 85150709 := bstep (se 5 (by rfl) ⟨3991439, by rfl⟩ : syracuseStep 85150709 = 7982879) B7982879
theorem B56767139 : Blo 2183435 56767139 := bstep (se 1 (by rfl) ⟨42575354, by rfl⟩ : syracuseStep 56767139 = 85150709) B85150709
theorem B37844759 : Blo 2183435 37844759 := bstep (se 1 (by rfl) ⟨28383569, by rfl⟩ : syracuseStep 37844759 = 56767139) B56767139
theorem B100919357 : Blo 2183435 100919357 := bstep (se 3 (by rfl) ⟨18922379, by rfl⟩ : syracuseStep 100919357 = 37844759) B37844759
theorem B67279571 : Blo 2183435 67279571 := bstep (se 1 (by rfl) ⟨50459678, by rfl⟩ : syracuseStep 67279571 = 100919357) B100919357
theorem B44853047 : Blo 2183435 44853047 := bstep (se 1 (by rfl) ⟨33639785, by rfl⟩ : syracuseStep 44853047 = 67279571) B67279571
theorem B29902031 : Blo 2183435 29902031 := bstep (se 1 (by rfl) ⟨22426523, by rfl⟩ : syracuseStep 29902031 = 44853047) B44853047
theorem B19934687 : Blo 2183435 19934687 := bstep (se 1 (by rfl) ⟨14951015, by rfl⟩ : syracuseStep 19934687 = 29902031) B29902031
theorem B13289791 : Blo 2183435 13289791 := bstep (se 1 (by rfl) ⟨9967343, by rfl⟩ : syracuseStep 13289791 = 19934687) B19934687
theorem B17719721 : Blo 2183435 17719721 := bstep (se 2 (by rfl) ⟨6644895, by rfl⟩ : syracuseStep 17719721 = 13289791) B13289791
theorem B11813147 : Blo 2183435 11813147 := bstep (se 1 (by rfl) ⟨8859860, by rfl⟩ : syracuseStep 11813147 = 17719721) B17719721
theorem B7875431 : Blo 2183435 7875431 := bstep (se 1 (by rfl) ⟨5906573, by rfl⟩ : syracuseStep 7875431 = 11813147) B11813147
theorem B5250287 : Blo 2183435 5250287 := bstep (se 1 (by rfl) ⟨3937715, by rfl⟩ : syracuseStep 5250287 = 7875431) B7875431
theorem B3500191 : Blo 2183435 3500191 := bstep (se 1 (by rfl) ⟨2625143, by rfl⟩ : syracuseStep 3500191 = 5250287) B5250287
theorem B18667685 : Blo 2183435 18667685 := bstep (se 4 (by rfl) ⟨1750095, by rfl⟩ : syracuseStep 18667685 = 3500191) B3500191
theorem B12445123 : Blo 2183435 12445123 := bstep (se 1 (by rfl) ⟨9333842, by rfl⟩ : syracuseStep 12445123 = 18667685) B18667685
theorem B16593497 : Blo 2183435 16593497 := bstep (se 2 (by rfl) ⟨6222561, by rfl⟩ : syracuseStep 16593497 = 12445123) B12445123
theorem B11062331 : Blo 2183435 11062331 := bstep (se 1 (by rfl) ⟨8296748, by rfl⟩ : syracuseStep 11062331 = 16593497) B16593497
theorem B7374887 : Blo 2183435 7374887 := bstep (se 1 (by rfl) ⟨5531165, by rfl⟩ : syracuseStep 7374887 = 11062331) B11062331
theorem B4916591 : Blo 2183435 4916591 := bstep (se 1 (by rfl) ⟨3687443, by rfl⟩ : syracuseStep 4916591 = 7374887) B7374887
theorem B3277727 : Blo 2183435 3277727 := bstep (se 1 (by rfl) ⟨2458295, by rfl⟩ : syracuseStep 3277727 = 4916591) B4916591
theorem B2185151 : Blo 2183435 2185151 := bstep (se 1 (by rfl) ⟨1638863, by rfl⟩ : syracuseStep 2185151 = 3277727) B3277727
theorem B3277733 : Blo 2183435 3277733 := bbase (se 4 (by rfl) ⟨307287, by rfl⟩ : syracuseStep 3277733 = 614575) (by norm_num)
theorem B2185155 : Blo 2183435 2185155 := bstep (se 1 (by rfl) ⟨1638866, by rfl⟩ : syracuseStep 2185155 = 3277733) B3277733
theorem B2765593 : Blo 2183435 2765593 := bbase (se 2 (by rfl) ⟨1037097, by rfl⟩ : syracuseStep 2765593 = 2074195) (by norm_num)
theorem B3687457 : Blo 2183435 3687457 := bstep (se 2 (by rfl) ⟨1382796, by rfl⟩ : syracuseStep 3687457 = 2765593) B2765593
theorem B4916609 : Blo 2183435 4916609 := bstep (se 2 (by rfl) ⟨1843728, by rfl⟩ : syracuseStep 4916609 = 3687457) B3687457
theorem B3277739 : Blo 2183435 3277739 := bstep (se 1 (by rfl) ⟨2458304, by rfl⟩ : syracuseStep 3277739 = 4916609) B4916609
theorem B2185159 : Blo 2183435 2185159 := bstep (se 1 (by rfl) ⟨1638869, by rfl⟩ : syracuseStep 2185159 = 3277739) B3277739
theorem B2458309 : Blo 2183435 2458309 := bbase (se 4 (by rfl) ⟨230466, by rfl⟩ : syracuseStep 2458309 = 460933) (by norm_num)
theorem B3277745 : Blo 2183435 3277745 := bstep (se 2 (by rfl) ⟨1229154, by rfl⟩ : syracuseStep 3277745 = 2458309) B2458309
theorem B2185163 : Blo 2183435 2185163 := bstep (se 1 (by rfl) ⟨1638872, by rfl⟩ : syracuseStep 2185163 = 3277745) B3277745
theorem B4148405 : Blo 2183435 4148405 := bbase (se 5 (by rfl) ⟨194456, by rfl⟩ : syracuseStep 4148405 = 388913) (by norm_num)
theorem B2765603 : Blo 2183435 2765603 := bstep (se 1 (by rfl) ⟨2074202, by rfl⟩ : syracuseStep 2765603 = 4148405) B4148405
theorem B7374941 : Blo 2183435 7374941 := bstep (se 3 (by rfl) ⟨1382801, by rfl⟩ : syracuseStep 7374941 = 2765603) B2765603
theorem B4916627 : Blo 2183435 4916627 := bstep (se 1 (by rfl) ⟨3687470, by rfl⟩ : syracuseStep 4916627 = 7374941) B7374941
theorem B3277751 : Blo 2183435 3277751 := bstep (se 1 (by rfl) ⟨2458313, by rfl⟩ : syracuseStep 3277751 = 4916627) B4916627
theorem B2185167 : Blo 2183435 2185167 := bstep (se 1 (by rfl) ⟨1638875, by rfl⟩ : syracuseStep 2185167 = 3277751) B3277751
theorem B3277757 : Blo 2183435 3277757 := bbase (se 3 (by rfl) ⟨614579, by rfl⟩ : syracuseStep 3277757 = 1229159) (by norm_num)
theorem B2185171 : Blo 2183435 2185171 := bstep (se 1 (by rfl) ⟨1638878, by rfl⟩ : syracuseStep 2185171 = 3277757) B3277757
theorem B4916645 : Blo 2183435 4916645 := bbase (se 4 (by rfl) ⟨460935, by rfl⟩ : syracuseStep 4916645 = 921871) (by norm_num)
theorem B3277763 : Blo 2183435 3277763 := bstep (se 1 (by rfl) ⟨2458322, by rfl⟩ : syracuseStep 3277763 = 4916645) B4916645
theorem B2185175 : Blo 2183435 2185175 := bstep (se 1 (by rfl) ⟨1638881, by rfl⟩ : syracuseStep 2185175 = 3277763) B3277763
theorem B5531237 : Blo 2183435 5531237 := bbase (se 4 (by rfl) ⟨518553, by rfl⟩ : syracuseStep 5531237 = 1037107) (by norm_num)
theorem B3687491 : Blo 2183435 3687491 := bstep (se 1 (by rfl) ⟨2765618, by rfl⟩ : syracuseStep 3687491 = 5531237) B5531237
theorem B2458327 : Blo 2183435 2458327 := bstep (se 1 (by rfl) ⟨1843745, by rfl⟩ : syracuseStep 2458327 = 3687491) B3687491
theorem B3277769 : Blo 2183435 3277769 := bstep (se 2 (by rfl) ⟨1229163, by rfl⟩ : syracuseStep 3277769 = 2458327) B2458327
theorem B2185179 : Blo 2183435 2185179 := bstep (se 1 (by rfl) ⟨1638884, by rfl⟩ : syracuseStep 2185179 = 3277769) B3277769
theorem B5250365 : Blo 2183435 5250365 := bbase (se 3 (by rfl) ⟨984443, by rfl⟩ : syracuseStep 5250365 = 1968887) (by norm_num)
theorem B3500243 : Blo 2183435 3500243 := bstep (se 1 (by rfl) ⟨2625182, by rfl⟩ : syracuseStep 3500243 = 5250365) B5250365
theorem B2333495 : Blo 2183435 2333495 := bstep (se 1 (by rfl) ⟨1750121, by rfl⟩ : syracuseStep 2333495 = 3500243) B3500243
theorem B6222653 : Blo 2183435 6222653 := bstep (se 3 (by rfl) ⟨1166747, by rfl⟩ : syracuseStep 6222653 = 2333495) B2333495
theorem B4148435 : Blo 2183435 4148435 := bstep (se 1 (by rfl) ⟨3111326, by rfl⟩ : syracuseStep 4148435 = 6222653) B6222653
theorem B11062493 : Blo 2183435 11062493 := bstep (se 3 (by rfl) ⟨2074217, by rfl⟩ : syracuseStep 11062493 = 4148435) B4148435
theorem B7374995 : Blo 2183435 7374995 := bstep (se 1 (by rfl) ⟨5531246, by rfl⟩ : syracuseStep 7374995 = 11062493) B11062493
theorem B4916663 : Blo 2183435 4916663 := bstep (se 1 (by rfl) ⟨3687497, by rfl⟩ : syracuseStep 4916663 = 7374995) B7374995
theorem B3277775 : Blo 2183435 3277775 := bstep (se 1 (by rfl) ⟨2458331, by rfl⟩ : syracuseStep 3277775 = 4916663) B4916663
theorem B2185183 : Blo 2183435 2185183 := bstep (se 1 (by rfl) ⟨1638887, by rfl⟩ : syracuseStep 2185183 = 3277775) B3277775
theorem B3277781 : Blo 2183435 3277781 := bbase (se 7 (by rfl) ⟨38411, by rfl⟩ : syracuseStep 3277781 = 76823) (by norm_num)
theorem B2185187 : Blo 2183435 2185187 := bstep (se 1 (by rfl) ⟨1638890, by rfl⟩ : syracuseStep 2185187 = 3277781) B3277781
theorem B8296901 : Blo 2183435 8296901 := bbase (se 4 (by rfl) ⟨777834, by rfl⟩ : syracuseStep 8296901 = 1555669) (by norm_num)
theorem B5531267 : Blo 2183435 5531267 := bstep (se 1 (by rfl) ⟨4148450, by rfl⟩ : syracuseStep 5531267 = 8296901) B8296901
theorem B3687511 : Blo 2183435 3687511 := bstep (se 1 (by rfl) ⟨2765633, by rfl⟩ : syracuseStep 3687511 = 5531267) B5531267
theorem B4916681 : Blo 2183435 4916681 := bstep (se 2 (by rfl) ⟨1843755, by rfl⟩ : syracuseStep 4916681 = 3687511) B3687511
theorem B3277787 : Blo 2183435 3277787 := bstep (se 1 (by rfl) ⟨2458340, by rfl⟩ : syracuseStep 3277787 = 4916681) B4916681
theorem B2185191 : Blo 2183435 2185191 := bstep (se 1 (by rfl) ⟨1638893, by rfl⟩ : syracuseStep 2185191 = 3277787) B3277787
theorem B2458345 : Blo 2183435 2458345 := bbase (se 2 (by rfl) ⟨921879, by rfl⟩ : syracuseStep 2458345 = 1843759) (by norm_num)
theorem B3277793 : Blo 2183435 3277793 := bstep (se 2 (by rfl) ⟨1229172, by rfl⟩ : syracuseStep 3277793 = 2458345) B2458345
theorem B2185195 : Blo 2183435 2185195 := bstep (se 1 (by rfl) ⟨1638896, by rfl⟩ : syracuseStep 2185195 = 3277793) B3277793
theorem B12445397 : Blo 2183435 12445397 := bbase (se 7 (by rfl) ⟨145844, by rfl⟩ : syracuseStep 12445397 = 291689) (by norm_num)
theorem B8296931 : Blo 2183435 8296931 := bstep (se 1 (by rfl) ⟨6222698, by rfl⟩ : syracuseStep 8296931 = 12445397) B12445397
theorem B5531287 : Blo 2183435 5531287 := bstep (se 1 (by rfl) ⟨4148465, by rfl⟩ : syracuseStep 5531287 = 8296931) B8296931
theorem B7375049 : Blo 2183435 7375049 := bstep (se 2 (by rfl) ⟨2765643, by rfl⟩ : syracuseStep 7375049 = 5531287) B5531287
theorem B4916699 : Blo 2183435 4916699 := bstep (se 1 (by rfl) ⟨3687524, by rfl⟩ : syracuseStep 4916699 = 7375049) B7375049
theorem B3277799 : Blo 2183435 3277799 := bstep (se 1 (by rfl) ⟨2458349, by rfl⟩ : syracuseStep 3277799 = 4916699) B4916699
theorem B2185199 : Blo 2183435 2185199 := bstep (se 1 (by rfl) ⟨1638899, by rfl⟩ : syracuseStep 2185199 = 3277799) B3277799
theorem B3277805 : Blo 2183435 3277805 := bbase (se 3 (by rfl) ⟨614588, by rfl⟩ : syracuseStep 3277805 = 1229177) (by norm_num)
theorem B2185203 : Blo 2183435 2185203 := bstep (se 1 (by rfl) ⟨1638902, by rfl⟩ : syracuseStep 2185203 = 3277805) B3277805
theorem B4916717 : Blo 2183435 4916717 := bbase (se 3 (by rfl) ⟨921884, by rfl⟩ : syracuseStep 4916717 = 1843769) (by norm_num)
theorem B3277811 : Blo 2183435 3277811 := bstep (se 1 (by rfl) ⟨2458358, by rfl⟩ : syracuseStep 3277811 = 4916717) B4916717
theorem B2185207 : Blo 2183435 2185207 := bstep (se 1 (by rfl) ⟨1638905, by rfl⟩ : syracuseStep 2185207 = 3277811) B3277811
theorem B3322541 : Blo 2183435 3322541 := bbase (se 3 (by rfl) ⟨622976, by rfl⟩ : syracuseStep 3322541 = 1245953) (by norm_num)
theorem B2215027 : Blo 2183435 2215027 := bstep (se 1 (by rfl) ⟨1661270, by rfl⟩ : syracuseStep 2215027 = 3322541) B3322541
theorem B2953369 : Blo 2183435 2953369 := bstep (se 2 (by rfl) ⟨1107513, by rfl⟩ : syracuseStep 2953369 = 2215027) B2215027
theorem B3937825 : Blo 2183435 3937825 := bstep (se 2 (by rfl) ⟨1476684, by rfl⟩ : syracuseStep 3937825 = 2953369) B2953369
theorem B5250433 : Blo 2183435 5250433 := bstep (se 2 (by rfl) ⟨1968912, by rfl⟩ : syracuseStep 5250433 = 3937825) B3937825
theorem B7000577 : Blo 2183435 7000577 := bstep (se 2 (by rfl) ⟨2625216, by rfl⟩ : syracuseStep 7000577 = 5250433) B5250433
theorem B4667051 : Blo 2183435 4667051 := bstep (se 1 (by rfl) ⟨3500288, by rfl⟩ : syracuseStep 4667051 = 7000577) B7000577
theorem B3111367 : Blo 2183435 3111367 := bstep (se 1 (by rfl) ⟨2333525, by rfl⟩ : syracuseStep 3111367 = 4667051) B4667051
theorem B4148489 : Blo 2183435 4148489 := bstep (se 2 (by rfl) ⟨1555683, by rfl⟩ : syracuseStep 4148489 = 3111367) B3111367
theorem B2765659 : Blo 2183435 2765659 := bstep (se 1 (by rfl) ⟨2074244, by rfl⟩ : syracuseStep 2765659 = 4148489) B4148489
theorem B3687545 : Blo 2183435 3687545 := bstep (se 2 (by rfl) ⟨1382829, by rfl⟩ : syracuseStep 3687545 = 2765659) B2765659
theorem B2458363 : Blo 2183435 2458363 := bstep (se 1 (by rfl) ⟨1843772, by rfl⟩ : syracuseStep 2458363 = 3687545) B3687545
theorem B3277817 : Blo 2183435 3277817 := bstep (se 2 (by rfl) ⟨1229181, by rfl⟩ : syracuseStep 3277817 = 2458363) B2458363
theorem B2185211 : Blo 2183435 2185211 := bstep (se 1 (by rfl) ⟨1638908, by rfl⟩ : syracuseStep 2185211 = 3277817) B3277817
theorem B5322077 : Blo 2183435 5322077 := bbase (se 3 (by rfl) ⟨997889, by rfl⟩ : syracuseStep 5322077 = 1995779) (by norm_num)
theorem B3548051 : Blo 2183435 3548051 := bstep (se 1 (by rfl) ⟨2661038, by rfl⟩ : syracuseStep 3548051 = 5322077) B5322077
theorem B2365367 : Blo 2183435 2365367 := bstep (se 1 (by rfl) ⟨1774025, by rfl⟩ : syracuseStep 2365367 = 3548051) B3548051
theorem B6307645 : Blo 2183435 6307645 := bstep (se 3 (by rfl) ⟨1182683, by rfl⟩ : syracuseStep 6307645 = 2365367) B2365367
theorem B8410193 : Blo 2183435 8410193 := bstep (se 2 (by rfl) ⟨3153822, by rfl⟩ : syracuseStep 8410193 = 6307645) B6307645
theorem B5606795 : Blo 2183435 5606795 := bstep (se 1 (by rfl) ⟨4205096, by rfl⟩ : syracuseStep 5606795 = 8410193) B8410193
theorem B3737863 : Blo 2183435 3737863 := bstep (se 1 (by rfl) ⟨2803397, by rfl⟩ : syracuseStep 3737863 = 5606795) B5606795
theorem B4983817 : Blo 2183435 4983817 := bstep (se 2 (by rfl) ⟨1868931, by rfl⟩ : syracuseStep 4983817 = 3737863) B3737863
theorem B6645089 : Blo 2183435 6645089 := bstep (se 2 (by rfl) ⟨2491908, by rfl⟩ : syracuseStep 6645089 = 4983817) B4983817
theorem B4430059 : Blo 2183435 4430059 := bstep (se 1 (by rfl) ⟨3322544, by rfl⟩ : syracuseStep 4430059 = 6645089) B6645089
theorem B23626981 : Blo 2183435 23626981 := bstep (se 4 (by rfl) ⟨2215029, by rfl⟩ : syracuseStep 23626981 = 4430059) B4430059
theorem B126010565 : Blo 2183435 126010565 := bstep (se 4 (by rfl) ⟨11813490, by rfl⟩ : syracuseStep 126010565 = 23626981) B23626981
theorem B84007043 : Blo 2183435 84007043 := bstep (se 1 (by rfl) ⟨63005282, by rfl⟩ : syracuseStep 84007043 = 126010565) B126010565
theorem B56004695 : Blo 2183435 56004695 := bstep (se 1 (by rfl) ⟨42003521, by rfl⟩ : syracuseStep 56004695 = 84007043) B84007043
theorem B37336463 : Blo 2183435 37336463 := bstep (se 1 (by rfl) ⟨28002347, by rfl⟩ : syracuseStep 37336463 = 56004695) B56004695
theorem B24890975 : Blo 2183435 24890975 := bstep (se 1 (by rfl) ⟨18668231, by rfl⟩ : syracuseStep 24890975 = 37336463) B37336463
theorem B16593983 : Blo 2183435 16593983 := bstep (se 1 (by rfl) ⟨12445487, by rfl⟩ : syracuseStep 16593983 = 24890975) B24890975
theorem B11062655 : Blo 2183435 11062655 := bstep (se 1 (by rfl) ⟨8296991, by rfl⟩ : syracuseStep 11062655 = 16593983) B16593983
theorem B7375103 : Blo 2183435 7375103 := bstep (se 1 (by rfl) ⟨5531327, by rfl⟩ : syracuseStep 7375103 = 11062655) B11062655
theorem B4916735 : Blo 2183435 4916735 := bstep (se 1 (by rfl) ⟨3687551, by rfl⟩ : syracuseStep 4916735 = 7375103) B7375103
theorem B3277823 : Blo 2183435 3277823 := bstep (se 1 (by rfl) ⟨2458367, by rfl⟩ : syracuseStep 3277823 = 4916735) B4916735
theorem B2185215 : Blo 2183435 2185215 := bstep (se 1 (by rfl) ⟨1638911, by rfl⟩ : syracuseStep 2185215 = 3277823) B3277823
theorem B3277829 : Blo 2183435 3277829 := bbase (se 4 (by rfl) ⟨307296, by rfl⟩ : syracuseStep 3277829 = 614593) (by norm_num)
theorem B2185219 : Blo 2183435 2185219 := bstep (se 1 (by rfl) ⟨1638914, by rfl⟩ : syracuseStep 2185219 = 3277829) B3277829
theorem B3687565 : Blo 2183435 3687565 := bbase (se 3 (by rfl) ⟨691418, by rfl⟩ : syracuseStep 3687565 = 1382837) (by norm_num)
theorem B4916753 : Blo 2183435 4916753 := bstep (se 2 (by rfl) ⟨1843782, by rfl⟩ : syracuseStep 4916753 = 3687565) B3687565
theorem B3277835 : Blo 2183435 3277835 := bstep (se 1 (by rfl) ⟨2458376, by rfl⟩ : syracuseStep 3277835 = 4916753) B4916753
theorem B2185223 : Blo 2183435 2185223 := bstep (se 1 (by rfl) ⟨1638917, by rfl⟩ : syracuseStep 2185223 = 3277835) B3277835
theorem B2458381 : Blo 2183435 2458381 := bbase (se 3 (by rfl) ⟨460946, by rfl⟩ : syracuseStep 2458381 = 921893) (by norm_num)
theorem B3277841 : Blo 2183435 3277841 := bstep (se 2 (by rfl) ⟨1229190, by rfl⟩ : syracuseStep 3277841 = 2458381) B2458381
theorem B2185227 : Blo 2183435 2185227 := bstep (se 1 (by rfl) ⟨1638920, by rfl⟩ : syracuseStep 2185227 = 3277841) B3277841
theorem B7375157 : Blo 2183435 7375157 := bbase (se 5 (by rfl) ⟨345710, by rfl⟩ : syracuseStep 7375157 = 691421) (by norm_num)
theorem B4916771 : Blo 2183435 4916771 := bstep (se 1 (by rfl) ⟨3687578, by rfl⟩ : syracuseStep 4916771 = 7375157) B7375157
theorem B3277847 : Blo 2183435 3277847 := bstep (se 1 (by rfl) ⟨2458385, by rfl⟩ : syracuseStep 3277847 = 4916771) B4916771
theorem B2185231 : Blo 2183435 2185231 := bstep (se 1 (by rfl) ⟨1638923, by rfl⟩ : syracuseStep 2185231 = 3277847) B3277847
theorem B3277853 : Blo 2183435 3277853 := bbase (se 3 (by rfl) ⟨614597, by rfl⟩ : syracuseStep 3277853 = 1229195) (by norm_num)
theorem B2185235 : Blo 2183435 2185235 := bstep (se 1 (by rfl) ⟨1638926, by rfl⟩ : syracuseStep 2185235 = 3277853) B3277853
theorem B4916789 : Blo 2183435 4916789 := bbase (se 5 (by rfl) ⟨230474, by rfl⟩ : syracuseStep 4916789 = 460949) (by norm_num)
theorem B3277859 : Blo 2183435 3277859 := bstep (se 1 (by rfl) ⟨2458394, by rfl⟩ : syracuseStep 3277859 = 4916789) B4916789
theorem B2185239 : Blo 2183435 2185239 := bstep (se 1 (by rfl) ⟨1638929, by rfl⟩ : syracuseStep 2185239 = 3277859) B3277859
theorem B5250509 : Blo 2183435 5250509 := bbase (se 3 (by rfl) ⟨984470, by rfl⟩ : syracuseStep 5250509 = 1968941) (by norm_num)
theorem B3500339 : Blo 2183435 3500339 := bstep (se 1 (by rfl) ⟨2625254, by rfl⟩ : syracuseStep 3500339 = 5250509) B5250509
theorem B9334237 : Blo 2183435 9334237 := bstep (se 3 (by rfl) ⟨1750169, by rfl⟩ : syracuseStep 9334237 = 3500339) B3500339
theorem B12445649 : Blo 2183435 12445649 := bstep (se 2 (by rfl) ⟨4667118, by rfl⟩ : syracuseStep 12445649 = 9334237) B9334237
theorem B8297099 : Blo 2183435 8297099 := bstep (se 1 (by rfl) ⟨6222824, by rfl⟩ : syracuseStep 8297099 = 12445649) B12445649
theorem B5531399 : Blo 2183435 5531399 := bstep (se 1 (by rfl) ⟨4148549, by rfl⟩ : syracuseStep 5531399 = 8297099) B8297099
theorem B3687599 : Blo 2183435 3687599 := bstep (se 1 (by rfl) ⟨2765699, by rfl⟩ : syracuseStep 3687599 = 5531399) B5531399
theorem B2458399 : Blo 2183435 2458399 := bstep (se 1 (by rfl) ⟨1843799, by rfl⟩ : syracuseStep 2458399 = 3687599) B3687599
theorem B3277865 : Blo 2183435 3277865 := bstep (se 2 (by rfl) ⟨1229199, by rfl⟩ : syracuseStep 3277865 = 2458399) B2458399
theorem B2185243 : Blo 2183435 2185243 := bstep (se 1 (by rfl) ⟨1638932, by rfl⟩ : syracuseStep 2185243 = 3277865) B3277865
theorem B4983893 : Blo 2183435 4983893 := bbase (se 8 (by rfl) ⟨29202, by rfl⟩ : syracuseStep 4983893 = 58405) (by norm_num)
theorem B3322595 : Blo 2183435 3322595 := bstep (se 1 (by rfl) ⟨2491946, by rfl⟩ : syracuseStep 3322595 = 4983893) B4983893
theorem B2215063 : Blo 2183435 2215063 := bstep (se 1 (by rfl) ⟨1661297, by rfl⟩ : syracuseStep 2215063 = 3322595) B3322595
theorem B2953417 : Blo 2183435 2953417 := bstep (se 2 (by rfl) ⟨1107531, by rfl⟩ : syracuseStep 2953417 = 2215063) B2215063
theorem B3937889 : Blo 2183435 3937889 := bstep (se 2 (by rfl) ⟨1476708, by rfl⟩ : syracuseStep 3937889 = 2953417) B2953417
theorem B2625259 : Blo 2183435 2625259 := bstep (se 1 (by rfl) ⟨1968944, by rfl⟩ : syracuseStep 2625259 = 3937889) B3937889
theorem B3500345 : Blo 2183435 3500345 := bstep (se 2 (by rfl) ⟨1312629, by rfl⟩ : syracuseStep 3500345 = 2625259) B2625259
theorem B9334253 : Blo 2183435 9334253 := bstep (se 3 (by rfl) ⟨1750172, by rfl⟩ : syracuseStep 9334253 = 3500345) B3500345
theorem B6222835 : Blo 2183435 6222835 := bstep (se 1 (by rfl) ⟨4667126, by rfl⟩ : syracuseStep 6222835 = 9334253) B9334253
theorem B8297113 : Blo 2183435 8297113 := bstep (se 2 (by rfl) ⟨3111417, by rfl⟩ : syracuseStep 8297113 = 6222835) B6222835
theorem B11062817 : Blo 2183435 11062817 := bstep (se 2 (by rfl) ⟨4148556, by rfl⟩ : syracuseStep 11062817 = 8297113) B8297113
theorem B7375211 : Blo 2183435 7375211 := bstep (se 1 (by rfl) ⟨5531408, by rfl⟩ : syracuseStep 7375211 = 11062817) B11062817
theorem B4916807 : Blo 2183435 4916807 := bstep (se 1 (by rfl) ⟨3687605, by rfl⟩ : syracuseStep 4916807 = 7375211) B7375211
theorem B3277871 : Blo 2183435 3277871 := bstep (se 1 (by rfl) ⟨2458403, by rfl⟩ : syracuseStep 3277871 = 4916807) B4916807
theorem B2185247 : Blo 2183435 2185247 := bstep (se 1 (by rfl) ⟨1638935, by rfl⟩ : syracuseStep 2185247 = 3277871) B3277871
theorem B3277877 : Blo 2183435 3277877 := bbase (se 5 (by rfl) ⟨153650, by rfl⟩ : syracuseStep 3277877 = 307301) (by norm_num)
theorem B2185251 : Blo 2183435 2185251 := bstep (se 1 (by rfl) ⟨1638938, by rfl⟩ : syracuseStep 2185251 = 3277877) B3277877
theorem B5531429 : Blo 2183435 5531429 := bbase (se 4 (by rfl) ⟨518571, by rfl⟩ : syracuseStep 5531429 = 1037143) (by norm_num)
theorem B3687619 : Blo 2183435 3687619 := bstep (se 1 (by rfl) ⟨2765714, by rfl⟩ : syracuseStep 3687619 = 5531429) B5531429
theorem B4916825 : Blo 2183435 4916825 := bstep (se 2 (by rfl) ⟨1843809, by rfl⟩ : syracuseStep 4916825 = 3687619) B3687619
theorem B3277883 : Blo 2183435 3277883 := bstep (se 1 (by rfl) ⟨2458412, by rfl⟩ : syracuseStep 3277883 = 4916825) B4916825
theorem B2185255 : Blo 2183435 2185255 := bstep (se 1 (by rfl) ⟨1638941, by rfl⟩ : syracuseStep 2185255 = 3277883) B3277883
theorem B2458417 : Blo 2183435 2458417 := bbase (se 2 (by rfl) ⟨921906, by rfl⟩ : syracuseStep 2458417 = 1843813) (by norm_num)
theorem B3277889 : Blo 2183435 3277889 := bstep (se 2 (by rfl) ⟨1229208, by rfl⟩ : syracuseStep 3277889 = 2458417) B2458417
theorem B2185259 : Blo 2183435 2185259 := bstep (se 1 (by rfl) ⟨1638944, by rfl⟩ : syracuseStep 2185259 = 3277889) B3277889
theorem B5250557 : Blo 2183435 5250557 := bbase (se 3 (by rfl) ⟨984479, by rfl⟩ : syracuseStep 5250557 = 1968959) (by norm_num)
theorem B3500371 : Blo 2183435 3500371 := bstep (se 1 (by rfl) ⟨2625278, by rfl⟩ : syracuseStep 3500371 = 5250557) B5250557
theorem B4667161 : Blo 2183435 4667161 := bstep (se 2 (by rfl) ⟨1750185, by rfl⟩ : syracuseStep 4667161 = 3500371) B3500371
theorem B6222881 : Blo 2183435 6222881 := bstep (se 2 (by rfl) ⟨2333580, by rfl⟩ : syracuseStep 6222881 = 4667161) B4667161
theorem B4148587 : Blo 2183435 4148587 := bstep (se 1 (by rfl) ⟨3111440, by rfl⟩ : syracuseStep 4148587 = 6222881) B6222881
theorem B5531449 : Blo 2183435 5531449 := bstep (se 2 (by rfl) ⟨2074293, by rfl⟩ : syracuseStep 5531449 = 4148587) B4148587
theorem B7375265 : Blo 2183435 7375265 := bstep (se 2 (by rfl) ⟨2765724, by rfl⟩ : syracuseStep 7375265 = 5531449) B5531449
theorem B4916843 : Blo 2183435 4916843 := bstep (se 1 (by rfl) ⟨3687632, by rfl⟩ : syracuseStep 4916843 = 7375265) B7375265
theorem B3277895 : Blo 2183435 3277895 := bstep (se 1 (by rfl) ⟨2458421, by rfl⟩ : syracuseStep 3277895 = 4916843) B4916843
theorem B2185263 : Blo 2183435 2185263 := bstep (se 1 (by rfl) ⟨1638947, by rfl⟩ : syracuseStep 2185263 = 3277895) B3277895
theorem B3277901 : Blo 2183435 3277901 := bbase (se 3 (by rfl) ⟨614606, by rfl⟩ : syracuseStep 3277901 = 1229213) (by norm_num)
theorem B2185267 : Blo 2183435 2185267 := bstep (se 1 (by rfl) ⟨1638950, by rfl⟩ : syracuseStep 2185267 = 3277901) B3277901
theorem B4916861 : Blo 2183435 4916861 := bbase (se 3 (by rfl) ⟨921911, by rfl⟩ : syracuseStep 4916861 = 1843823) (by norm_num)
theorem B3277907 : Blo 2183435 3277907 := bstep (se 1 (by rfl) ⟨2458430, by rfl⟩ : syracuseStep 3277907 = 4916861) B4916861
theorem B2185271 : Blo 2183435 2185271 := bstep (se 1 (by rfl) ⟨1638953, by rfl⟩ : syracuseStep 2185271 = 3277907) B3277907
theorem B3687653 : Blo 2183435 3687653 := bbase (se 4 (by rfl) ⟨345717, by rfl⟩ : syracuseStep 3687653 = 691435) (by norm_num)
theorem B2458435 : Blo 2183435 2458435 := bstep (se 1 (by rfl) ⟨1843826, by rfl⟩ : syracuseStep 2458435 = 3687653) B3687653
theorem B3277913 : Blo 2183435 3277913 := bstep (se 2 (by rfl) ⟨1229217, by rfl⟩ : syracuseStep 3277913 = 2458435) B2458435
theorem B2185275 : Blo 2183435 2185275 := bstep (se 1 (by rfl) ⟨1638956, by rfl⟩ : syracuseStep 2185275 = 3277913) B3277913
theorem B7875893 : Blo 2183435 7875893 := bbase (se 5 (by rfl) ⟨369182, by rfl⟩ : syracuseStep 7875893 = 738365) (by norm_num)
theorem B5250595 : Blo 2183435 5250595 := bstep (se 1 (by rfl) ⟨3937946, by rfl⟩ : syracuseStep 5250595 = 7875893) B7875893
theorem B7000793 : Blo 2183435 7000793 := bstep (se 2 (by rfl) ⟨2625297, by rfl⟩ : syracuseStep 7000793 = 5250595) B5250595
theorem B4667195 : Blo 2183435 4667195 := bstep (se 1 (by rfl) ⟨3500396, by rfl⟩ : syracuseStep 4667195 = 7000793) B7000793
theorem B3111463 : Blo 2183435 3111463 := bstep (se 1 (by rfl) ⟨2333597, by rfl⟩ : syracuseStep 3111463 = 4667195) B4667195
theorem B16594469 : Blo 2183435 16594469 := bstep (se 4 (by rfl) ⟨1555731, by rfl⟩ : syracuseStep 16594469 = 3111463) B3111463
theorem B11062979 : Blo 2183435 11062979 := bstep (se 1 (by rfl) ⟨8297234, by rfl⟩ : syracuseStep 11062979 = 16594469) B16594469
theorem B7375319 : Blo 2183435 7375319 := bstep (se 1 (by rfl) ⟨5531489, by rfl⟩ : syracuseStep 7375319 = 11062979) B11062979
theorem B4916879 : Blo 2183435 4916879 := bstep (se 1 (by rfl) ⟨3687659, by rfl⟩ : syracuseStep 4916879 = 7375319) B7375319
theorem B3277919 : Blo 2183435 3277919 := bstep (se 1 (by rfl) ⟨2458439, by rfl⟩ : syracuseStep 3277919 = 4916879) B4916879
theorem B2185279 : Blo 2183435 2185279 := bstep (se 1 (by rfl) ⟨1638959, by rfl⟩ : syracuseStep 2185279 = 3277919) B3277919
theorem B3277925 : Blo 2183435 3277925 := bbase (se 4 (by rfl) ⟨307305, by rfl⟩ : syracuseStep 3277925 = 614611) (by norm_num)
theorem B2185283 : Blo 2183435 2185283 := bstep (se 1 (by rfl) ⟨1638962, by rfl⟩ : syracuseStep 2185283 = 3277925) B3277925
theorem B4667213 : Blo 2183435 4667213 := bbase (se 3 (by rfl) ⟨875102, by rfl⟩ : syracuseStep 4667213 = 1750205) (by norm_num)
theorem B3111475 : Blo 2183435 3111475 := bstep (se 1 (by rfl) ⟨2333606, by rfl⟩ : syracuseStep 3111475 = 4667213) B4667213
theorem B4148633 : Blo 2183435 4148633 := bstep (se 2 (by rfl) ⟨1555737, by rfl⟩ : syracuseStep 4148633 = 3111475) B3111475
theorem B2765755 : Blo 2183435 2765755 := bstep (se 1 (by rfl) ⟨2074316, by rfl⟩ : syracuseStep 2765755 = 4148633) B4148633
theorem B3687673 : Blo 2183435 3687673 := bstep (se 2 (by rfl) ⟨1382877, by rfl⟩ : syracuseStep 3687673 = 2765755) B2765755
theorem B4916897 : Blo 2183435 4916897 := bstep (se 2 (by rfl) ⟨1843836, by rfl⟩ : syracuseStep 4916897 = 3687673) B3687673
theorem B3277931 : Blo 2183435 3277931 := bstep (se 1 (by rfl) ⟨2458448, by rfl⟩ : syracuseStep 3277931 = 4916897) B4916897
theorem B2185287 : Blo 2183435 2185287 := bstep (se 1 (by rfl) ⟨1638965, by rfl⟩ : syracuseStep 2185287 = 3277931) B3277931
theorem B2458453 : Blo 2183435 2458453 := bbase (se 9 (by rfl) ⟨7202, by rfl⟩ : syracuseStep 2458453 = 14405) (by norm_num)
theorem B3277937 : Blo 2183435 3277937 := bstep (se 2 (by rfl) ⟨1229226, by rfl⟩ : syracuseStep 3277937 = 2458453) B2458453
theorem B2185291 : Blo 2183435 2185291 := bstep (se 1 (by rfl) ⟨1638968, by rfl⟩ : syracuseStep 2185291 = 3277937) B3277937
theorem B2765765 : Blo 2183435 2765765 := bbase (se 4 (by rfl) ⟨259290, by rfl⟩ : syracuseStep 2765765 = 518581) (by norm_num)
theorem B7375373 : Blo 2183435 7375373 := bstep (se 3 (by rfl) ⟨1382882, by rfl⟩ : syracuseStep 7375373 = 2765765) B2765765
theorem B4916915 : Blo 2183435 4916915 := bstep (se 1 (by rfl) ⟨3687686, by rfl⟩ : syracuseStep 4916915 = 7375373) B7375373
theorem B3277943 : Blo 2183435 3277943 := bstep (se 1 (by rfl) ⟨2458457, by rfl⟩ : syracuseStep 3277943 = 4916915) B4916915
theorem B2185295 : Blo 2183435 2185295 := bstep (se 1 (by rfl) ⟨1638971, by rfl⟩ : syracuseStep 2185295 = 3277943) B3277943
theorem B3277949 : Blo 2183435 3277949 := bbase (se 3 (by rfl) ⟨614615, by rfl⟩ : syracuseStep 3277949 = 1229231) (by norm_num)
theorem B2185299 : Blo 2183435 2185299 := bstep (se 1 (by rfl) ⟨1638974, by rfl⟩ : syracuseStep 2185299 = 3277949) B3277949
theorem B4916933 : Blo 2183435 4916933 := bbase (se 4 (by rfl) ⟨460962, by rfl⟩ : syracuseStep 4916933 = 921925) (by norm_num)
theorem B3277955 : Blo 2183435 3277955 := bstep (se 1 (by rfl) ⟨2458466, by rfl⟩ : syracuseStep 3277955 = 4916933) B4916933
theorem B2185303 : Blo 2183435 2185303 := bstep (se 1 (by rfl) ⟨1638977, by rfl⟩ : syracuseStep 2185303 = 3277955) B3277955
theorem B8981381 : Blo 2183435 8981381 := bbase (se 4 (by rfl) ⟨842004, by rfl⟩ : syracuseStep 8981381 = 1684009) (by norm_num)
theorem B23950349 : Blo 2183435 23950349 := bstep (se 3 (by rfl) ⟨4490690, by rfl⟩ : syracuseStep 23950349 = 8981381) B8981381
theorem B15966899 : Blo 2183435 15966899 := bstep (se 1 (by rfl) ⟨11975174, by rfl⟩ : syracuseStep 15966899 = 23950349) B23950349
theorem B10644599 : Blo 2183435 10644599 := bstep (se 1 (by rfl) ⟨7983449, by rfl⟩ : syracuseStep 10644599 = 15966899) B15966899
theorem B28385597 : Blo 2183435 28385597 := bstep (se 3 (by rfl) ⟨5322299, by rfl⟩ : syracuseStep 28385597 = 10644599) B10644599
theorem B75694925 : Blo 2183435 75694925 := bstep (se 3 (by rfl) ⟨14192798, by rfl⟩ : syracuseStep 75694925 = 28385597) B28385597
theorem B50463283 : Blo 2183435 50463283 := bstep (se 1 (by rfl) ⟨37847462, by rfl⟩ : syracuseStep 50463283 = 75694925) B75694925
theorem B67284377 : Blo 2183435 67284377 := bstep (se 2 (by rfl) ⟨25231641, by rfl⟩ : syracuseStep 67284377 = 50463283) B50463283
theorem B44856251 : Blo 2183435 44856251 := bstep (se 1 (by rfl) ⟨33642188, by rfl⟩ : syracuseStep 44856251 = 67284377) B67284377
theorem B29904167 : Blo 2183435 29904167 := bstep (se 1 (by rfl) ⟨22428125, by rfl⟩ : syracuseStep 29904167 = 44856251) B44856251
theorem B79744445 : Blo 2183435 79744445 := bstep (se 3 (by rfl) ⟨14952083, by rfl⟩ : syracuseStep 79744445 = 29904167) B29904167
theorem B53162963 : Blo 2183435 53162963 := bstep (se 1 (by rfl) ⟨39872222, by rfl⟩ : syracuseStep 53162963 = 79744445) B79744445
theorem B35441975 : Blo 2183435 35441975 := bstep (se 1 (by rfl) ⟨26581481, by rfl⟩ : syracuseStep 35441975 = 53162963) B53162963
theorem B23627983 : Blo 2183435 23627983 := bstep (se 1 (by rfl) ⟨17720987, by rfl⟩ : syracuseStep 23627983 = 35441975) B35441975
theorem B31503977 : Blo 2183435 31503977 := bstep (se 2 (by rfl) ⟨11813991, by rfl⟩ : syracuseStep 31503977 = 23627983) B23627983
theorem B21002651 : Blo 2183435 21002651 := bstep (se 1 (by rfl) ⟨15751988, by rfl⟩ : syracuseStep 21002651 = 31503977) B31503977
theorem B14001767 : Blo 2183435 14001767 := bstep (se 1 (by rfl) ⟨10501325, by rfl⟩ : syracuseStep 14001767 = 21002651) B21002651
theorem B9334511 : Blo 2183435 9334511 := bstep (se 1 (by rfl) ⟨7000883, by rfl⟩ : syracuseStep 9334511 = 14001767) B14001767
theorem B6223007 : Blo 2183435 6223007 := bstep (se 1 (by rfl) ⟨4667255, by rfl⟩ : syracuseStep 6223007 = 9334511) B9334511
theorem B4148671 : Blo 2183435 4148671 := bstep (se 1 (by rfl) ⟨3111503, by rfl⟩ : syracuseStep 4148671 = 6223007) B6223007
theorem B5531561 : Blo 2183435 5531561 := bstep (se 2 (by rfl) ⟨2074335, by rfl⟩ : syracuseStep 5531561 = 4148671) B4148671
theorem B3687707 : Blo 2183435 3687707 := bstep (se 1 (by rfl) ⟨2765780, by rfl⟩ : syracuseStep 3687707 = 5531561) B5531561
theorem B2458471 : Blo 2183435 2458471 := bstep (se 1 (by rfl) ⟨1843853, by rfl⟩ : syracuseStep 2458471 = 3687707) B3687707
theorem B3277961 : Blo 2183435 3277961 := bstep (se 2 (by rfl) ⟨1229235, by rfl⟩ : syracuseStep 3277961 = 2458471) B2458471
theorem B2185307 : Blo 2183435 2185307 := bstep (se 1 (by rfl) ⟨1638980, by rfl⟩ : syracuseStep 2185307 = 3277961) B3277961
theorem B11063141 : Blo 2183435 11063141 := bbase (se 4 (by rfl) ⟨1037169, by rfl⟩ : syracuseStep 11063141 = 2074339) (by norm_num)
theorem B7375427 : Blo 2183435 7375427 := bstep (se 1 (by rfl) ⟨5531570, by rfl⟩ : syracuseStep 7375427 = 11063141) B11063141
theorem B4916951 : Blo 2183435 4916951 := bstep (se 1 (by rfl) ⟨3687713, by rfl⟩ : syracuseStep 4916951 = 7375427) B7375427
theorem B3277967 : Blo 2183435 3277967 := bstep (se 1 (by rfl) ⟨2458475, by rfl⟩ : syracuseStep 3277967 = 4916951) B4916951
theorem B2185311 : Blo 2183435 2185311 := bstep (se 1 (by rfl) ⟨1638983, by rfl⟩ : syracuseStep 2185311 = 3277967) B3277967
theorem B3277973 : Blo 2183435 3277973 := bbase (se 6 (by rfl) ⟨76827, by rfl⟩ : syracuseStep 3277973 = 153655) (by norm_num)
theorem B2185315 : Blo 2183435 2185315 := bstep (se 1 (by rfl) ⟨1638986, by rfl⟩ : syracuseStep 2185315 = 3277973) B3277973
theorem B7876037 : Blo 2183435 7876037 := bbase (se 4 (by rfl) ⟨738378, by rfl⟩ : syracuseStep 7876037 = 1476757) (by norm_num)
theorem B5250691 : Blo 2183435 5250691 := bstep (se 1 (by rfl) ⟨3938018, by rfl⟩ : syracuseStep 5250691 = 7876037) B7876037
theorem B7000921 : Blo 2183435 7000921 := bstep (se 2 (by rfl) ⟨2625345, by rfl⟩ : syracuseStep 7000921 = 5250691) B5250691
theorem B9334561 : Blo 2183435 9334561 := bstep (se 2 (by rfl) ⟨3500460, by rfl⟩ : syracuseStep 9334561 = 7000921) B7000921
theorem B12446081 : Blo 2183435 12446081 := bstep (se 2 (by rfl) ⟨4667280, by rfl⟩ : syracuseStep 12446081 = 9334561) B9334561
theorem B8297387 : Blo 2183435 8297387 := bstep (se 1 (by rfl) ⟨6223040, by rfl⟩ : syracuseStep 8297387 = 12446081) B12446081
theorem B5531591 : Blo 2183435 5531591 := bstep (se 1 (by rfl) ⟨4148693, by rfl⟩ : syracuseStep 5531591 = 8297387) B8297387
theorem B3687727 : Blo 2183435 3687727 := bstep (se 1 (by rfl) ⟨2765795, by rfl⟩ : syracuseStep 3687727 = 5531591) B5531591
theorem B4916969 : Blo 2183435 4916969 := bstep (se 2 (by rfl) ⟨1843863, by rfl⟩ : syracuseStep 4916969 = 3687727) B3687727
theorem B3277979 : Blo 2183435 3277979 := bstep (se 1 (by rfl) ⟨2458484, by rfl⟩ : syracuseStep 3277979 = 4916969) B4916969
theorem B2185319 : Blo 2183435 2185319 := bstep (se 1 (by rfl) ⟨1638989, by rfl⟩ : syracuseStep 2185319 = 3277979) B3277979
theorem B2458489 : Blo 2183435 2458489 := bbase (se 2 (by rfl) ⟨921933, by rfl⟩ : syracuseStep 2458489 = 1843867) (by norm_num)
theorem B3277985 : Blo 2183435 3277985 := bstep (se 2 (by rfl) ⟨1229244, by rfl⟩ : syracuseStep 3277985 = 2458489) B2458489
theorem B2185323 : Blo 2183435 2185323 := bstep (se 1 (by rfl) ⟨1638992, by rfl⟩ : syracuseStep 2185323 = 3277985) B3277985
theorem B2953525 : Blo 2183435 2953525 := bbase (se 5 (by rfl) ⟨138446, by rfl⟩ : syracuseStep 2953525 = 276893) (by norm_num)
theorem B3938033 : Blo 2183435 3938033 := bstep (se 2 (by rfl) ⟨1476762, by rfl⟩ : syracuseStep 3938033 = 2953525) B2953525
theorem B2625355 : Blo 2183435 2625355 := bstep (se 1 (by rfl) ⟨1969016, by rfl⟩ : syracuseStep 2625355 = 3938033) B3938033
theorem B14001893 : Blo 2183435 14001893 := bstep (se 4 (by rfl) ⟨1312677, by rfl⟩ : syracuseStep 14001893 = 2625355) B2625355
theorem B9334595 : Blo 2183435 9334595 := bstep (se 1 (by rfl) ⟨7000946, by rfl⟩ : syracuseStep 9334595 = 14001893) B14001893
theorem B6223063 : Blo 2183435 6223063 := bstep (se 1 (by rfl) ⟨4667297, by rfl⟩ : syracuseStep 6223063 = 9334595) B9334595
theorem B8297417 : Blo 2183435 8297417 := bstep (se 2 (by rfl) ⟨3111531, by rfl⟩ : syracuseStep 8297417 = 6223063) B6223063
theorem B5531611 : Blo 2183435 5531611 := bstep (se 1 (by rfl) ⟨4148708, by rfl⟩ : syracuseStep 5531611 = 8297417) B8297417
theorem B7375481 : Blo 2183435 7375481 := bstep (se 2 (by rfl) ⟨2765805, by rfl⟩ : syracuseStep 7375481 = 5531611) B5531611
theorem B4916987 : Blo 2183435 4916987 := bstep (se 1 (by rfl) ⟨3687740, by rfl⟩ : syracuseStep 4916987 = 7375481) B7375481
theorem B3277991 : Blo 2183435 3277991 := bstep (se 1 (by rfl) ⟨2458493, by rfl⟩ : syracuseStep 3277991 = 4916987) B4916987
theorem B2185327 : Blo 2183435 2185327 := bstep (se 1 (by rfl) ⟨1638995, by rfl⟩ : syracuseStep 2185327 = 3277991) B3277991
theorem B3277997 : Blo 2183435 3277997 := bbase (se 3 (by rfl) ⟨614624, by rfl⟩ : syracuseStep 3277997 = 1229249) (by norm_num)
theorem B2185331 : Blo 2183435 2185331 := bstep (se 1 (by rfl) ⟨1638998, by rfl⟩ : syracuseStep 2185331 = 3277997) B3277997
theorem B4917005 : Blo 2183435 4917005 := bbase (se 3 (by rfl) ⟨921938, by rfl⟩ : syracuseStep 4917005 = 1843877) (by norm_num)
theorem B3278003 : Blo 2183435 3278003 := bstep (se 1 (by rfl) ⟨2458502, by rfl⟩ : syracuseStep 3278003 = 4917005) B4917005
theorem B2185335 : Blo 2183435 2185335 := bstep (se 1 (by rfl) ⟨1639001, by rfl⟩ : syracuseStep 2185335 = 3278003) B3278003
theorem B2765821 : Blo 2183435 2765821 := bbase (se 3 (by rfl) ⟨518591, by rfl⟩ : syracuseStep 2765821 = 1037183) (by norm_num)
theorem B3687761 : Blo 2183435 3687761 := bstep (se 2 (by rfl) ⟨1382910, by rfl⟩ : syracuseStep 3687761 = 2765821) B2765821
theorem B2458507 : Blo 2183435 2458507 := bstep (se 1 (by rfl) ⟨1843880, by rfl⟩ : syracuseStep 2458507 = 3687761) B3687761
theorem B3278009 : Blo 2183435 3278009 := bstep (se 2 (by rfl) ⟨1229253, by rfl⟩ : syracuseStep 3278009 = 2458507) B2458507
theorem B2185339 : Blo 2183435 2185339 := bstep (se 1 (by rfl) ⟨1639004, by rfl⟩ : syracuseStep 2185339 = 3278009) B3278009
theorem B7000997 : Blo 2183435 7000997 := bbase (se 4 (by rfl) ⟨656343, by rfl⟩ : syracuseStep 7000997 = 1312687) (by norm_num)
theorem B18669325 : Blo 2183435 18669325 := bstep (se 3 (by rfl) ⟨3500498, by rfl⟩ : syracuseStep 18669325 = 7000997) B7000997
theorem B24892433 : Blo 2183435 24892433 := bstep (se 2 (by rfl) ⟨9334662, by rfl⟩ : syracuseStep 24892433 = 18669325) B18669325
theorem B16594955 : Blo 2183435 16594955 := bstep (se 1 (by rfl) ⟨12446216, by rfl⟩ : syracuseStep 16594955 = 24892433) B24892433
theorem B11063303 : Blo 2183435 11063303 := bstep (se 1 (by rfl) ⟨8297477, by rfl⟩ : syracuseStep 11063303 = 16594955) B16594955
theorem B7375535 : Blo 2183435 7375535 := bstep (se 1 (by rfl) ⟨5531651, by rfl⟩ : syracuseStep 7375535 = 11063303) B11063303
theorem B4917023 : Blo 2183435 4917023 := bstep (se 1 (by rfl) ⟨3687767, by rfl⟩ : syracuseStep 4917023 = 7375535) B7375535
theorem B3278015 : Blo 2183435 3278015 := bstep (se 1 (by rfl) ⟨2458511, by rfl⟩ : syracuseStep 3278015 = 4917023) B4917023
theorem B2185343 : Blo 2183435 2185343 := bstep (se 1 (by rfl) ⟨1639007, by rfl⟩ : syracuseStep 2185343 = 3278015) B3278015
theorem B3278021 : Blo 2183435 3278021 := bbase (se 4 (by rfl) ⟨307314, by rfl⟩ : syracuseStep 3278021 = 614629) (by norm_num)
theorem B2185347 : Blo 2183435 2185347 := bstep (se 1 (by rfl) ⟨1639010, by rfl⟩ : syracuseStep 2185347 = 3278021) B3278021
theorem B3687781 : Blo 2183435 3687781 := bbase (se 4 (by rfl) ⟨345729, by rfl⟩ : syracuseStep 3687781 = 691459) (by norm_num)
theorem B4917041 : Blo 2183435 4917041 := bstep (se 2 (by rfl) ⟨1843890, by rfl⟩ : syracuseStep 4917041 = 3687781) B3687781
theorem B3278027 : Blo 2183435 3278027 := bstep (se 1 (by rfl) ⟨2458520, by rfl⟩ : syracuseStep 3278027 = 4917041) B4917041
theorem B2185351 : Blo 2183435 2185351 := bstep (se 1 (by rfl) ⟨1639013, by rfl⟩ : syracuseStep 2185351 = 3278027) B3278027
theorem B2458525 : Blo 2183435 2458525 := bbase (se 3 (by rfl) ⟨460973, by rfl⟩ : syracuseStep 2458525 = 921947) (by norm_num)
theorem B3278033 : Blo 2183435 3278033 := bstep (se 2 (by rfl) ⟨1229262, by rfl⟩ : syracuseStep 3278033 = 2458525) B2458525
theorem B2185355 : Blo 2183435 2185355 := bstep (se 1 (by rfl) ⟨1639016, by rfl⟩ : syracuseStep 2185355 = 3278033) B3278033
theorem B7375589 : Blo 2183435 7375589 := bbase (se 4 (by rfl) ⟨691461, by rfl⟩ : syracuseStep 7375589 = 1382923) (by norm_num)
theorem B4917059 : Blo 2183435 4917059 := bstep (se 1 (by rfl) ⟨3687794, by rfl⟩ : syracuseStep 4917059 = 7375589) B7375589
theorem B3278039 : Blo 2183435 3278039 := bstep (se 1 (by rfl) ⟨2458529, by rfl⟩ : syracuseStep 3278039 = 4917059) B4917059
theorem B2185359 : Blo 2183435 2185359 := bstep (se 1 (by rfl) ⟨1639019, by rfl⟩ : syracuseStep 2185359 = 3278039) B3278039
theorem B3278045 : Blo 2183435 3278045 := bbase (se 3 (by rfl) ⟨614633, by rfl⟩ : syracuseStep 3278045 = 1229267) (by norm_num)
theorem B2185363 : Blo 2183435 2185363 := bstep (se 1 (by rfl) ⟨1639022, by rfl⟩ : syracuseStep 2185363 = 3278045) B3278045
theorem B4917077 : Blo 2183435 4917077 := bbase (se 9 (by rfl) ⟨14405, by rfl⟩ : syracuseStep 4917077 = 28811) (by norm_num)
theorem B3278051 : Blo 2183435 3278051 := bstep (se 1 (by rfl) ⟨2458538, by rfl⟩ : syracuseStep 3278051 = 4917077) B4917077
theorem B2185367 : Blo 2183435 2185367 := bstep (se 1 (by rfl) ⟨1639025, by rfl⟩ : syracuseStep 2185367 = 3278051) B3278051
theorem B6223189 : Blo 2183435 6223189 := bbase (se 13 (by rfl) ⟨1139, by rfl⟩ : syracuseStep 6223189 = 2279) (by norm_num)
theorem B8297585 : Blo 2183435 8297585 := bstep (se 2 (by rfl) ⟨3111594, by rfl⟩ : syracuseStep 8297585 = 6223189) B6223189
theorem B5531723 : Blo 2183435 5531723 := bstep (se 1 (by rfl) ⟨4148792, by rfl⟩ : syracuseStep 5531723 = 8297585) B8297585
theorem B3687815 : Blo 2183435 3687815 := bstep (se 1 (by rfl) ⟨2765861, by rfl⟩ : syracuseStep 3687815 = 5531723) B5531723
theorem B2458543 : Blo 2183435 2458543 := bstep (se 1 (by rfl) ⟨1843907, by rfl⟩ : syracuseStep 2458543 = 3687815) B3687815
theorem B3278057 : Blo 2183435 3278057 := bstep (se 2 (by rfl) ⟨1229271, by rfl⟩ : syracuseStep 3278057 = 2458543) B2458543
theorem B2185371 : Blo 2183435 2185371 := bstep (se 1 (by rfl) ⟨1639028, by rfl⟩ : syracuseStep 2185371 = 3278057) B3278057
theorem B5683709 : Blo 2183435 5683709 := bbase (se 3 (by rfl) ⟨1065695, by rfl⟩ : syracuseStep 5683709 = 2131391) (by norm_num)
theorem B3789139 : Blo 2183435 3789139 := bstep (se 1 (by rfl) ⟨2841854, by rfl⟩ : syracuseStep 3789139 = 5683709) B5683709
theorem B5052185 : Blo 2183435 5052185 := bstep (se 2 (by rfl) ⟨1894569, by rfl⟩ : syracuseStep 5052185 = 3789139) B3789139
theorem B3368123 : Blo 2183435 3368123 := bstep (se 1 (by rfl) ⟨2526092, by rfl⟩ : syracuseStep 3368123 = 5052185) B5052185
theorem B2245415 : Blo 2183435 2245415 := bstep (se 1 (by rfl) ⟨1684061, by rfl⟩ : syracuseStep 2245415 = 3368123) B3368123
theorem B5987773 : Blo 2183435 5987773 := bstep (se 3 (by rfl) ⟨1122707, by rfl⟩ : syracuseStep 5987773 = 2245415) B2245415
theorem B7983697 : Blo 2183435 7983697 := bstep (se 2 (by rfl) ⟨2993886, by rfl⟩ : syracuseStep 7983697 = 5987773) B5987773
theorem B10644929 : Blo 2183435 10644929 := bstep (se 2 (by rfl) ⟨3991848, by rfl⟩ : syracuseStep 10644929 = 7983697) B7983697
theorem B7096619 : Blo 2183435 7096619 := bstep (se 1 (by rfl) ⟨5322464, by rfl⟩ : syracuseStep 7096619 = 10644929) B10644929
theorem B4731079 : Blo 2183435 4731079 := bstep (se 1 (by rfl) ⟨3548309, by rfl⟩ : syracuseStep 4731079 = 7096619) B7096619
theorem B6308105 : Blo 2183435 6308105 := bstep (se 2 (by rfl) ⟨2365539, by rfl⟩ : syracuseStep 6308105 = 4731079) B4731079
theorem B16821613 : Blo 2183435 16821613 := bstep (se 3 (by rfl) ⟨3154052, by rfl⟩ : syracuseStep 16821613 = 6308105) B6308105
theorem B89715269 : Blo 2183435 89715269 := bstep (se 4 (by rfl) ⟨8410806, by rfl⟩ : syracuseStep 89715269 = 16821613) B16821613
theorem B59810179 : Blo 2183435 59810179 := bstep (se 1 (by rfl) ⟨44857634, by rfl⟩ : syracuseStep 59810179 = 89715269) B89715269
theorem B79746905 : Blo 2183435 79746905 := bstep (se 2 (by rfl) ⟨29905089, by rfl⟩ : syracuseStep 79746905 = 59810179) B59810179
theorem B53164603 : Blo 2183435 53164603 := bstep (se 1 (by rfl) ⟨39873452, by rfl⟩ : syracuseStep 53164603 = 79746905) B79746905
theorem B70886137 : Blo 2183435 70886137 := bstep (se 2 (by rfl) ⟨26582301, by rfl⟩ : syracuseStep 70886137 = 53164603) B53164603
theorem B94514849 : Blo 2183435 94514849 := bstep (se 2 (by rfl) ⟨35443068, by rfl⟩ : syracuseStep 94514849 = 70886137) B70886137
theorem B63009899 : Blo 2183435 63009899 := bstep (se 1 (by rfl) ⟨47257424, by rfl⟩ : syracuseStep 63009899 = 94514849) B94514849
theorem B42006599 : Blo 2183435 42006599 := bstep (se 1 (by rfl) ⟨31504949, by rfl⟩ : syracuseStep 42006599 = 63009899) B63009899
theorem B28004399 : Blo 2183435 28004399 := bstep (se 1 (by rfl) ⟨21003299, by rfl⟩ : syracuseStep 28004399 = 42006599) B42006599
theorem B18669599 : Blo 2183435 18669599 := bstep (se 1 (by rfl) ⟨14002199, by rfl⟩ : syracuseStep 18669599 = 28004399) B28004399
theorem B12446399 : Blo 2183435 12446399 := bstep (se 1 (by rfl) ⟨9334799, by rfl⟩ : syracuseStep 12446399 = 18669599) B18669599
theorem B8297599 : Blo 2183435 8297599 := bstep (se 1 (by rfl) ⟨6223199, by rfl⟩ : syracuseStep 8297599 = 12446399) B12446399
theorem B11063465 : Blo 2183435 11063465 := bstep (se 2 (by rfl) ⟨4148799, by rfl⟩ : syracuseStep 11063465 = 8297599) B8297599
theorem B7375643 : Blo 2183435 7375643 := bstep (se 1 (by rfl) ⟨5531732, by rfl⟩ : syracuseStep 7375643 = 11063465) B11063465
theorem B4917095 : Blo 2183435 4917095 := bstep (se 1 (by rfl) ⟨3687821, by rfl⟩ : syracuseStep 4917095 = 7375643) B7375643
theorem B3278063 : Blo 2183435 3278063 := bstep (se 1 (by rfl) ⟨2458547, by rfl⟩ : syracuseStep 3278063 = 4917095) B4917095
theorem B2185375 : Blo 2183435 2185375 := bstep (se 1 (by rfl) ⟨1639031, by rfl⟩ : syracuseStep 2185375 = 3278063) B3278063
theorem B3278069 : Blo 2183435 3278069 := bbase (se 5 (by rfl) ⟨153659, by rfl⟩ : syracuseStep 3278069 = 307319) (by norm_num)
theorem B2185379 : Blo 2183435 2185379 := bstep (se 1 (by rfl) ⟨1639034, by rfl⟩ : syracuseStep 2185379 = 3278069) B3278069
theorem B5250845 : Blo 2183435 5250845 := bbase (se 3 (by rfl) ⟨984533, by rfl⟩ : syracuseStep 5250845 = 1969067) (by norm_num)
theorem B14002253 : Blo 2183435 14002253 := bstep (se 3 (by rfl) ⟨2625422, by rfl⟩ : syracuseStep 14002253 = 5250845) B5250845
theorem B9334835 : Blo 2183435 9334835 := bstep (se 1 (by rfl) ⟨7001126, by rfl⟩ : syracuseStep 9334835 = 14002253) B14002253
theorem B6223223 : Blo 2183435 6223223 := bstep (se 1 (by rfl) ⟨4667417, by rfl⟩ : syracuseStep 6223223 = 9334835) B9334835
theorem B4148815 : Blo 2183435 4148815 := bstep (se 1 (by rfl) ⟨3111611, by rfl⟩ : syracuseStep 4148815 = 6223223) B6223223
theorem B5531753 : Blo 2183435 5531753 := bstep (se 2 (by rfl) ⟨2074407, by rfl⟩ : syracuseStep 5531753 = 4148815) B4148815
theorem B3687835 : Blo 2183435 3687835 := bstep (se 1 (by rfl) ⟨2765876, by rfl⟩ : syracuseStep 3687835 = 5531753) B5531753
theorem B4917113 : Blo 2183435 4917113 := bstep (se 2 (by rfl) ⟨1843917, by rfl⟩ : syracuseStep 4917113 = 3687835) B3687835
theorem B3278075 : Blo 2183435 3278075 := bstep (se 1 (by rfl) ⟨2458556, by rfl⟩ : syracuseStep 3278075 = 4917113) B4917113
theorem B2185383 : Blo 2183435 2185383 := bstep (se 1 (by rfl) ⟨1639037, by rfl⟩ : syracuseStep 2185383 = 3278075) B3278075
theorem B2458561 : Blo 2183435 2458561 := bbase (se 2 (by rfl) ⟨921960, by rfl⟩ : syracuseStep 2458561 = 1843921) (by norm_num)
theorem B3278081 : Blo 2183435 3278081 := bstep (se 2 (by rfl) ⟨1229280, by rfl⟩ : syracuseStep 3278081 = 2458561) B2458561
theorem B2185387 : Blo 2183435 2185387 := bstep (se 1 (by rfl) ⟨1639040, by rfl⟩ : syracuseStep 2185387 = 3278081) B3278081
theorem B5531773 : Blo 2183435 5531773 := bbase (se 3 (by rfl) ⟨1037207, by rfl⟩ : syracuseStep 5531773 = 2074415) (by norm_num)
theorem B7375697 : Blo 2183435 7375697 := bstep (se 2 (by rfl) ⟨2765886, by rfl⟩ : syracuseStep 7375697 = 5531773) B5531773
theorem B4917131 : Blo 2183435 4917131 := bstep (se 1 (by rfl) ⟨3687848, by rfl⟩ : syracuseStep 4917131 = 7375697) B7375697
theorem B3278087 : Blo 2183435 3278087 := bstep (se 1 (by rfl) ⟨2458565, by rfl⟩ : syracuseStep 3278087 = 4917131) B4917131
theorem B2185391 : Blo 2183435 2185391 := bstep (se 1 (by rfl) ⟨1639043, by rfl⟩ : syracuseStep 2185391 = 3278087) B3278087
theorem B3278093 : Blo 2183435 3278093 := bbase (se 3 (by rfl) ⟨614642, by rfl⟩ : syracuseStep 3278093 = 1229285) (by norm_num)
theorem B2185395 : Blo 2183435 2185395 := bstep (se 1 (by rfl) ⟨1639046, by rfl⟩ : syracuseStep 2185395 = 3278093) B3278093
theorem B4917149 : Blo 2183435 4917149 := bbase (se 3 (by rfl) ⟨921965, by rfl⟩ : syracuseStep 4917149 = 1843931) (by norm_num)
theorem B3278099 : Blo 2183435 3278099 := bstep (se 1 (by rfl) ⟨2458574, by rfl⟩ : syracuseStep 3278099 = 4917149) B4917149
theorem B2185399 : Blo 2183435 2185399 := bstep (se 1 (by rfl) ⟨1639049, by rfl⟩ : syracuseStep 2185399 = 3278099) B3278099
theorem B3687869 : Blo 2183435 3687869 := bbase (se 3 (by rfl) ⟨691475, by rfl⟩ : syracuseStep 3687869 = 1382951) (by norm_num)
theorem B2458579 : Blo 2183435 2458579 := bstep (se 1 (by rfl) ⟨1843934, by rfl⟩ : syracuseStep 2458579 = 3687869) B3687869
theorem B3278105 : Blo 2183435 3278105 := bstep (se 2 (by rfl) ⟨1229289, by rfl⟩ : syracuseStep 3278105 = 2458579) B2458579
theorem B2185403 : Blo 2183435 2185403 := bstep (se 1 (by rfl) ⟨1639052, by rfl⟩ : syracuseStep 2185403 = 3278105) B3278105
theorem B12446581 : Blo 2183435 12446581 := bbase (se 5 (by rfl) ⟨583433, by rfl⟩ : syracuseStep 12446581 = 1166867) (by norm_num)
theorem B16595441 : Blo 2183435 16595441 := bstep (se 2 (by rfl) ⟨6223290, by rfl⟩ : syracuseStep 16595441 = 12446581) B12446581
theorem B11063627 : Blo 2183435 11063627 := bstep (se 1 (by rfl) ⟨8297720, by rfl⟩ : syracuseStep 11063627 = 16595441) B16595441
theorem B7375751 : Blo 2183435 7375751 := bstep (se 1 (by rfl) ⟨5531813, by rfl⟩ : syracuseStep 7375751 = 11063627) B11063627
theorem B4917167 : Blo 2183435 4917167 := bstep (se 1 (by rfl) ⟨3687875, by rfl⟩ : syracuseStep 4917167 = 7375751) B7375751
theorem B3278111 : Blo 2183435 3278111 := bstep (se 1 (by rfl) ⟨2458583, by rfl⟩ : syracuseStep 3278111 = 4917167) B4917167
theorem B2185407 : Blo 2183435 2185407 := bstep (se 1 (by rfl) ⟨1639055, by rfl⟩ : syracuseStep 2185407 = 3278111) B3278111
theorem B3278117 : Blo 2183435 3278117 := bbase (se 4 (by rfl) ⟨307323, by rfl⟩ : syracuseStep 3278117 = 614647) (by norm_num)
theorem B2185411 : Blo 2183435 2185411 := bstep (se 1 (by rfl) ⟨1639058, by rfl⟩ : syracuseStep 2185411 = 3278117) B3278117
theorem B2765917 : Blo 2183435 2765917 := bbase (se 3 (by rfl) ⟨518609, by rfl⟩ : syracuseStep 2765917 = 1037219) (by norm_num)
theorem B3687889 : Blo 2183435 3687889 := bstep (se 2 (by rfl) ⟨1382958, by rfl⟩ : syracuseStep 3687889 = 2765917) B2765917
theorem B4917185 : Blo 2183435 4917185 := bstep (se 2 (by rfl) ⟨1843944, by rfl⟩ : syracuseStep 4917185 = 3687889) B3687889
theorem B3278123 : Blo 2183435 3278123 := bstep (se 1 (by rfl) ⟨2458592, by rfl⟩ : syracuseStep 3278123 = 4917185) B4917185
theorem B2185415 : Blo 2183435 2185415 := bstep (se 1 (by rfl) ⟨1639061, by rfl⟩ : syracuseStep 2185415 = 3278123) B3278123
theorem B2458597 : Blo 2183435 2458597 := bbase (se 4 (by rfl) ⟨230493, by rfl⟩ : syracuseStep 2458597 = 460987) (by norm_num)
theorem B3278129 : Blo 2183435 3278129 := bstep (se 2 (by rfl) ⟨1229298, by rfl⟩ : syracuseStep 3278129 = 2458597) B2458597
theorem B2185419 : Blo 2183435 2185419 := bstep (se 1 (by rfl) ⟨1639064, by rfl⟩ : syracuseStep 2185419 = 3278129) B3278129
theorem B3548389 : Blo 2183435 3548389 := bbase (se 4 (by rfl) ⟨332661, by rfl⟩ : syracuseStep 3548389 = 665323) (by norm_num)
theorem B4731185 : Blo 2183435 4731185 := bstep (se 2 (by rfl) ⟨1774194, by rfl⟩ : syracuseStep 4731185 = 3548389) B3548389
theorem B3154123 : Blo 2183435 3154123 := bstep (se 1 (by rfl) ⟨2365592, by rfl⟩ : syracuseStep 3154123 = 4731185) B4731185
theorem B16821989 : Blo 2183435 16821989 := bstep (se 4 (by rfl) ⟨1577061, by rfl⟩ : syracuseStep 16821989 = 3154123) B3154123
theorem B11214659 : Blo 2183435 11214659 := bstep (se 1 (by rfl) ⟨8410994, by rfl⟩ : syracuseStep 11214659 = 16821989) B16821989
theorem B29905757 : Blo 2183435 29905757 := bstep (se 3 (by rfl) ⟨5607329, by rfl⟩ : syracuseStep 29905757 = 11214659) B11214659
theorem B19937171 : Blo 2183435 19937171 := bstep (se 1 (by rfl) ⟨14952878, by rfl⟩ : syracuseStep 19937171 = 29905757) B29905757
theorem B13291447 : Blo 2183435 13291447 := bstep (se 1 (by rfl) ⟨9968585, by rfl⟩ : syracuseStep 13291447 = 19937171) B19937171
theorem B17721929 : Blo 2183435 17721929 := bstep (se 2 (by rfl) ⟨6645723, by rfl⟩ : syracuseStep 17721929 = 13291447) B13291447
theorem B11814619 : Blo 2183435 11814619 := bstep (se 1 (by rfl) ⟨8860964, by rfl⟩ : syracuseStep 11814619 = 17721929) B17721929
theorem B15752825 : Blo 2183435 15752825 := bstep (se 2 (by rfl) ⟨5907309, by rfl⟩ : syracuseStep 15752825 = 11814619) B11814619
theorem B10501883 : Blo 2183435 10501883 := bstep (se 1 (by rfl) ⟨7876412, by rfl⟩ : syracuseStep 10501883 = 15752825) B15752825
theorem B7001255 : Blo 2183435 7001255 := bstep (se 1 (by rfl) ⟨5250941, by rfl⟩ : syracuseStep 7001255 = 10501883) B10501883
theorem B4667503 : Blo 2183435 4667503 := bstep (se 1 (by rfl) ⟨3500627, by rfl⟩ : syracuseStep 4667503 = 7001255) B7001255
theorem B6223337 : Blo 2183435 6223337 := bstep (se 2 (by rfl) ⟨2333751, by rfl⟩ : syracuseStep 6223337 = 4667503) B4667503
theorem B4148891 : Blo 2183435 4148891 := bstep (se 1 (by rfl) ⟨3111668, by rfl⟩ : syracuseStep 4148891 = 6223337) B6223337
theorem B2765927 : Blo 2183435 2765927 := bstep (se 1 (by rfl) ⟨2074445, by rfl⟩ : syracuseStep 2765927 = 4148891) B4148891
theorem B7375805 : Blo 2183435 7375805 := bstep (se 3 (by rfl) ⟨1382963, by rfl⟩ : syracuseStep 7375805 = 2765927) B2765927
theorem B4917203 : Blo 2183435 4917203 := bstep (se 1 (by rfl) ⟨3687902, by rfl⟩ : syracuseStep 4917203 = 7375805) B7375805
theorem B3278135 : Blo 2183435 3278135 := bstep (se 1 (by rfl) ⟨2458601, by rfl⟩ : syracuseStep 3278135 = 4917203) B4917203
theorem B2185423 : Blo 2183435 2185423 := bstep (se 1 (by rfl) ⟨1639067, by rfl⟩ : syracuseStep 2185423 = 3278135) B3278135
theorem B3278141 : Blo 2183435 3278141 := bbase (se 3 (by rfl) ⟨614651, by rfl⟩ : syracuseStep 3278141 = 1229303) (by norm_num)
theorem B2185427 : Blo 2183435 2185427 := bstep (se 1 (by rfl) ⟨1639070, by rfl⟩ : syracuseStep 2185427 = 3278141) B3278141
theorem B4917221 : Blo 2183435 4917221 := bbase (se 4 (by rfl) ⟨460989, by rfl⟩ : syracuseStep 4917221 = 921979) (by norm_num)
theorem B3278147 : Blo 2183435 3278147 := bstep (se 1 (by rfl) ⟨2458610, by rfl⟩ : syracuseStep 3278147 = 4917221) B4917221
theorem B2185431 : Blo 2183435 2185431 := bstep (se 1 (by rfl) ⟨1639073, by rfl⟩ : syracuseStep 2185431 = 3278147) B3278147
theorem B5531885 : Blo 2183435 5531885 := bbase (se 3 (by rfl) ⟨1037228, by rfl⟩ : syracuseStep 5531885 = 2074457) (by norm_num)
theorem B3687923 : Blo 2183435 3687923 := bstep (se 1 (by rfl) ⟨2765942, by rfl⟩ : syracuseStep 3687923 = 5531885) B5531885
theorem B2458615 : Blo 2183435 2458615 := bstep (se 1 (by rfl) ⟨1843961, by rfl⟩ : syracuseStep 2458615 = 3687923) B3687923
theorem B3278153 : Blo 2183435 3278153 := bstep (se 2 (by rfl) ⟨1229307, by rfl⟩ : syracuseStep 3278153 = 2458615) B2458615
theorem B2185435 : Blo 2183435 2185435 := bstep (se 1 (by rfl) ⟨1639076, by rfl⟩ : syracuseStep 2185435 = 3278153) B3278153
theorem C0 (j : ℕ) (h1 : 545858 ≤ j) (h2 : j ≤ 546358) : Blo 2183435 (4 * j + 3) := by
  interval_cases j
  · exact B2183435
  · exact B2183439
  · exact B2183443
  · exact B2183447
  · exact B2183451
  · exact B2183455
  · exact B2183459
  · exact B2183463
  · exact B2183467
  · exact B2183471
  · exact B2183475
  · exact B2183479
  · exact B2183483
  · exact B2183487
  · exact B2183491
  · exact B2183495
  · exact B2183499
  · exact B2183503
  · exact B2183507
  · exact B2183511
  · exact B2183515
  · exact B2183519
  · exact B2183523
  · exact B2183527
  · exact B2183531
  · exact B2183535
  · exact B2183539
  · exact B2183543
  · exact B2183547
  · exact B2183551
  · exact B2183555
  · exact B2183559
  · exact B2183563
  · exact B2183567
  · exact B2183571
  · exact B2183575
  · exact B2183579
  · exact B2183583
  · exact B2183587
  · exact B2183591
  · exact B2183595
  · exact B2183599
  · exact B2183603
  · exact B2183607
  · exact B2183611
  · exact B2183615
  · exact B2183619
  · exact B2183623
  · exact B2183627
  · exact B2183631
  · exact B2183635
  · exact B2183639
  · exact B2183643
  · exact B2183647
  · exact B2183651
  · exact B2183655
  · exact B2183659
  · exact B2183663
  · exact B2183667
  · exact B2183671
  · exact B2183675
  · exact B2183679
  · exact B2183683
  · exact B2183687
  · exact B2183691
  · exact B2183695
  · exact B2183699
  · exact B2183703
  · exact B2183707
  · exact B2183711
  · exact B2183715
  · exact B2183719
  · exact B2183723
  · exact B2183727
  · exact B2183731
  · exact B2183735
  · exact B2183739
  · exact B2183743
  · exact B2183747
  · exact B2183751
  · exact B2183755
  · exact B2183759
  · exact B2183763
  · exact B2183767
  · exact B2183771
  · exact B2183775
  · exact B2183779
  · exact B2183783
  · exact B2183787
  · exact B2183791
  · exact B2183795
  · exact B2183799
  · exact B2183803
  · exact B2183807
  · exact B2183811
  · exact B2183815
  · exact B2183819
  · exact B2183823
  · exact B2183827
  · exact B2183831
  · exact B2183835
  · exact B2183839
  · exact B2183843
  · exact B2183847
  · exact B2183851
  · exact B2183855
  · exact B2183859
  · exact B2183863
  · exact B2183867
  · exact B2183871
  · exact B2183875
  · exact B2183879
  · exact B2183883
  · exact B2183887
  · exact B2183891
  · exact B2183895
  · exact B2183899
  · exact B2183903
  · exact B2183907
  · exact B2183911
  · exact B2183915
  · exact B2183919
  · exact B2183923
  · exact B2183927
  · exact B2183931
  · exact B2183935
  · exact B2183939
  · exact B2183943
  · exact B2183947
  · exact B2183951
  · exact B2183955
  · exact B2183959
  · exact B2183963
  · exact B2183967
  · exact B2183971
  · exact B2183975
  · exact B2183979
  · exact B2183983
  · exact B2183987
  · exact B2183991
  · exact B2183995
  · exact B2183999
  · exact B2184003
  · exact B2184007
  · exact B2184011
  · exact B2184015
  · exact B2184019
  · exact B2184023
  · exact B2184027
  · exact B2184031
  · exact B2184035
  · exact B2184039
  · exact B2184043
  · exact B2184047
  · exact B2184051
  · exact B2184055
  · exact B2184059
  · exact B2184063
  · exact B2184067
  · exact B2184071
  · exact B2184075
  · exact B2184079
  · exact B2184083
  · exact B2184087
  · exact B2184091
  · exact B2184095
  · exact B2184099
  · exact B2184103
  · exact B2184107
  · exact B2184111
  · exact B2184115
  · exact B2184119
  · exact B2184123
  · exact B2184127
  · exact B2184131
  · exact B2184135
  · exact B2184139
  · exact B2184143
  · exact B2184147
  · exact B2184151
  · exact B2184155
  · exact B2184159
  · exact B2184163
  · exact B2184167
  · exact B2184171
  · exact B2184175
  · exact B2184179
  · exact B2184183
  · exact B2184187
  · exact B2184191
  · exact B2184195
  · exact B2184199
  · exact B2184203
  · exact B2184207
  · exact B2184211
  · exact B2184215
  · exact B2184219
  · exact B2184223
  · exact B2184227
  · exact B2184231
  · exact B2184235
  · exact B2184239
  · exact B2184243
  · exact B2184247
  · exact B2184251
  · exact B2184255
  · exact B2184259
  · exact B2184263
  · exact B2184267
  · exact B2184271
  · exact B2184275
  · exact B2184279
  · exact B2184283
  · exact B2184287
  · exact B2184291
  · exact B2184295
  · exact B2184299
  · exact B2184303
  · exact B2184307
  · exact B2184311
  · exact B2184315
  · exact B2184319
  · exact B2184323
  · exact B2184327
  · exact B2184331
  · exact B2184335
  · exact B2184339
  · exact B2184343
  · exact B2184347
  · exact B2184351
  · exact B2184355
  · exact B2184359
  · exact B2184363
  · exact B2184367
  · exact B2184371
  · exact B2184375
  · exact B2184379
  · exact B2184383
  · exact B2184387
  · exact B2184391
  · exact B2184395
  · exact B2184399
  · exact B2184403
  · exact B2184407
  · exact B2184411
  · exact B2184415
  · exact B2184419
  · exact B2184423
  · exact B2184427
  · exact B2184431
  · exact B2184435
  · exact B2184439
  · exact B2184443
  · exact B2184447
  · exact B2184451
  · exact B2184455
  · exact B2184459
  · exact B2184463
  · exact B2184467
  · exact B2184471
  · exact B2184475
  · exact B2184479
  · exact B2184483
  · exact B2184487
  · exact B2184491
  · exact B2184495
  · exact B2184499
  · exact B2184503
  · exact B2184507
  · exact B2184511
  · exact B2184515
  · exact B2184519
  · exact B2184523
  · exact B2184527
  · exact B2184531
  · exact B2184535
  · exact B2184539
  · exact B2184543
  · exact B2184547
  · exact B2184551
  · exact B2184555
  · exact B2184559
  · exact B2184563
  · exact B2184567
  · exact B2184571
  · exact B2184575
  · exact B2184579
  · exact B2184583
  · exact B2184587
  · exact B2184591
  · exact B2184595
  · exact B2184599
  · exact B2184603
  · exact B2184607
  · exact B2184611
  · exact B2184615
  · exact B2184619
  · exact B2184623
  · exact B2184627
  · exact B2184631
  · exact B2184635
  · exact B2184639
  · exact B2184643
  · exact B2184647
  · exact B2184651
  · exact B2184655
  · exact B2184659
  · exact B2184663
  · exact B2184667
  · exact B2184671
  · exact B2184675
  · exact B2184679
  · exact B2184683
  · exact B2184687
  · exact B2184691
  · exact B2184695
  · exact B2184699
  · exact B2184703
  · exact B2184707
  · exact B2184711
  · exact B2184715
  · exact B2184719
  · exact B2184723
  · exact B2184727
  · exact B2184731
  · exact B2184735
  · exact B2184739
  · exact B2184743
  · exact B2184747
  · exact B2184751
  · exact B2184755
  · exact B2184759
  · exact B2184763
  · exact B2184767
  · exact B2184771
  · exact B2184775
  · exact B2184779
  · exact B2184783
  · exact B2184787
  · exact B2184791
  · exact B2184795
  · exact B2184799
  · exact B2184803
  · exact B2184807
  · exact B2184811
  · exact B2184815
  · exact B2184819
  · exact B2184823
  · exact B2184827
  · exact B2184831
  · exact B2184835
  · exact B2184839
  · exact B2184843
  · exact B2184847
  · exact B2184851
  · exact B2184855
  · exact B2184859
  · exact B2184863
  · exact B2184867
  · exact B2184871
  · exact B2184875
  · exact B2184879
  · exact B2184883
  · exact B2184887
  · exact B2184891
  · exact B2184895
  · exact B2184899
  · exact B2184903
  · exact B2184907
  · exact B2184911
  · exact B2184915
  · exact B2184919
  · exact B2184923
  · exact B2184927
  · exact B2184931
  · exact B2184935
  · exact B2184939
  · exact B2184943
  · exact B2184947
  · exact B2184951
  · exact B2184955
  · exact B2184959
  · exact B2184963
  · exact B2184967
  · exact B2184971
  · exact B2184975
  · exact B2184979
  · exact B2184983
  · exact B2184987
  · exact B2184991
  · exact B2184995
  · exact B2184999
  · exact B2185003
  · exact B2185007
  · exact B2185011
  · exact B2185015
  · exact B2185019
  · exact B2185023
  · exact B2185027
  · exact B2185031
  · exact B2185035
  · exact B2185039
  · exact B2185043
  · exact B2185047
  · exact B2185051
  · exact B2185055
  · exact B2185059
  · exact B2185063
  · exact B2185067
  · exact B2185071
  · exact B2185075
  · exact B2185079
  · exact B2185083
  · exact B2185087
  · exact B2185091
  · exact B2185095
  · exact B2185099
  · exact B2185103
  · exact B2185107
  · exact B2185111
  · exact B2185115
  · exact B2185119
  · exact B2185123
  · exact B2185127
  · exact B2185131
  · exact B2185135
  · exact B2185139
  · exact B2185143
  · exact B2185147
  · exact B2185151
  · exact B2185155
  · exact B2185159
  · exact B2185163
  · exact B2185167
  · exact B2185171
  · exact B2185175
  · exact B2185179
  · exact B2185183
  · exact B2185187
  · exact B2185191
  · exact B2185195
  · exact B2185199
  · exact B2185203
  · exact B2185207
  · exact B2185211
  · exact B2185215
  · exact B2185219
  · exact B2185223
  · exact B2185227
  · exact B2185231
  · exact B2185235
  · exact B2185239
  · exact B2185243
  · exact B2185247
  · exact B2185251
  · exact B2185255
  · exact B2185259
  · exact B2185263
  · exact B2185267
  · exact B2185271
  · exact B2185275
  · exact B2185279
  · exact B2185283
  · exact B2185287
  · exact B2185291
  · exact B2185295
  · exact B2185299
  · exact B2185303
  · exact B2185307
  · exact B2185311
  · exact B2185315
  · exact B2185319
  · exact B2185323
  · exact B2185327
  · exact B2185331
  · exact B2185335
  · exact B2185339
  · exact B2185343
  · exact B2185347
  · exact B2185351
  · exact B2185355
  · exact B2185359
  · exact B2185363
  · exact B2185367
  · exact B2185371
  · exact B2185375
  · exact B2185379
  · exact B2185383
  · exact B2185387
  · exact B2185391
  · exact B2185395
  · exact B2185399
  · exact B2185403
  · exact B2185407
  · exact B2185411
  · exact B2185415
  · exact B2185419
  · exact B2185423
  · exact B2185427
  · exact B2185431
  · exact B2185435
theorem solution (m : ℕ) (hlo : 2183435 ≤ m) (hhi : m ≤ 2185435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 545858 ≤ j := by omega
    have hj2 : j ≤ 546358 := by omega
    have hb : Blo 2183435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
