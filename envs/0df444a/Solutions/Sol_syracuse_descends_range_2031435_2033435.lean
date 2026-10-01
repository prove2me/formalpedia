-- Prove2me | solution 1 for syracuse_descends_range_2031435_2033435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:49:04.643854+00:00
-- url     : https://prove2.me/submissions/ad1c9b16-b19c-49af-8b8a-859ef0ba588c

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

theorem B2285365 : Blo 2031435 2285365 := bbase (se 5 (by rfl) ⟨107126, by rfl⟩ : syracuseStep 2285365 = 214253) (by norm_num)
theorem B3047153 : Blo 2031435 3047153 := bstep (se 2 (by rfl) ⟨1142682, by rfl⟩ : syracuseStep 3047153 = 2285365) B2285365
theorem B2031435 : Blo 2031435 2031435 := bstep (se 1 (by rfl) ⟨1523576, by rfl⟩ : syracuseStep 2031435 = 3047153) B3047153
theorem B2571041 : Blo 2031435 2571041 := bbase (se 2 (by rfl) ⟨964140, by rfl⟩ : syracuseStep 2571041 = 1928281) (by norm_num)
theorem B6856109 : Blo 2031435 6856109 := bstep (se 3 (by rfl) ⟨1285520, by rfl⟩ : syracuseStep 6856109 = 2571041) B2571041
theorem B4570739 : Blo 2031435 4570739 := bstep (se 1 (by rfl) ⟨3428054, by rfl⟩ : syracuseStep 4570739 = 6856109) B6856109
theorem B3047159 : Blo 2031435 3047159 := bstep (se 1 (by rfl) ⟨2285369, by rfl⟩ : syracuseStep 3047159 = 4570739) B4570739
theorem B2031439 : Blo 2031435 2031439 := bstep (se 1 (by rfl) ⟨1523579, by rfl⟩ : syracuseStep 2031439 = 3047159) B3047159
theorem B3047165 : Blo 2031435 3047165 := bbase (se 3 (by rfl) ⟨571343, by rfl⟩ : syracuseStep 3047165 = 1142687) (by norm_num)
theorem B2031443 : Blo 2031435 2031443 := bstep (se 1 (by rfl) ⟨1523582, by rfl⟩ : syracuseStep 2031443 = 3047165) B3047165
theorem B4570757 : Blo 2031435 4570757 := bbase (se 4 (by rfl) ⟨428508, by rfl⟩ : syracuseStep 4570757 = 857017) (by norm_num)
theorem B3047171 : Blo 2031435 3047171 := bstep (se 1 (by rfl) ⟨2285378, by rfl⟩ : syracuseStep 3047171 = 4570757) B4570757
theorem B2031447 : Blo 2031435 2031447 := bstep (se 1 (by rfl) ⟨1523585, by rfl⟩ : syracuseStep 2031447 = 3047171) B3047171
theorem B6507989 : Blo 2031435 6507989 := bbase (se 7 (by rfl) ⟨76265, by rfl⟩ : syracuseStep 6507989 = 152531) (by norm_num)
theorem B4338659 : Blo 2031435 4338659 := bstep (se 1 (by rfl) ⟨3253994, by rfl⟩ : syracuseStep 4338659 = 6507989) B6507989
theorem B2892439 : Blo 2031435 2892439 := bstep (se 1 (by rfl) ⟨2169329, by rfl⟩ : syracuseStep 2892439 = 4338659) B4338659
theorem B3856585 : Blo 2031435 3856585 := bstep (se 2 (by rfl) ⟨1446219, by rfl⟩ : syracuseStep 3856585 = 2892439) B2892439
theorem B5142113 : Blo 2031435 5142113 := bstep (se 2 (by rfl) ⟨1928292, by rfl⟩ : syracuseStep 5142113 = 3856585) B3856585
theorem B3428075 : Blo 2031435 3428075 := bstep (se 1 (by rfl) ⟨2571056, by rfl⟩ : syracuseStep 3428075 = 5142113) B5142113
theorem B2285383 : Blo 2031435 2285383 := bstep (se 1 (by rfl) ⟨1714037, by rfl⟩ : syracuseStep 2285383 = 3428075) B3428075
theorem B3047177 : Blo 2031435 3047177 := bstep (se 2 (by rfl) ⟨1142691, by rfl⟩ : syracuseStep 3047177 = 2285383) B2285383
theorem B2031451 : Blo 2031435 2031451 := bstep (se 1 (by rfl) ⟨1523588, by rfl⟩ : syracuseStep 2031451 = 3047177) B3047177
theorem B10284245 : Blo 2031435 10284245 := bbase (se 7 (by rfl) ⟨120518, by rfl⟩ : syracuseStep 10284245 = 241037) (by norm_num)
theorem B6856163 : Blo 2031435 6856163 := bstep (se 1 (by rfl) ⟨5142122, by rfl⟩ : syracuseStep 6856163 = 10284245) B10284245
theorem B4570775 : Blo 2031435 4570775 := bstep (se 1 (by rfl) ⟨3428081, by rfl⟩ : syracuseStep 4570775 = 6856163) B6856163
theorem B3047183 : Blo 2031435 3047183 := bstep (se 1 (by rfl) ⟨2285387, by rfl⟩ : syracuseStep 3047183 = 4570775) B4570775
theorem B2031455 : Blo 2031435 2031455 := bstep (se 1 (by rfl) ⟨1523591, by rfl⟩ : syracuseStep 2031455 = 3047183) B3047183
theorem B3047189 : Blo 2031435 3047189 := bbase (se 6 (by rfl) ⟨71418, by rfl⟩ : syracuseStep 3047189 = 142837) (by norm_num)
theorem B2031459 : Blo 2031435 2031459 := bstep (se 1 (by rfl) ⟨1523594, by rfl⟩ : syracuseStep 2031459 = 3047189) B3047189
theorem B6949733 : Blo 2031435 6949733 := bbase (se 4 (by rfl) ⟨651537, by rfl⟩ : syracuseStep 6949733 = 1303075) (by norm_num)
theorem B18532621 : Blo 2031435 18532621 := bstep (se 3 (by rfl) ⟨3474866, by rfl⟩ : syracuseStep 18532621 = 6949733) B6949733
theorem B98840645 : Blo 2031435 98840645 := bstep (se 4 (by rfl) ⟨9266310, by rfl⟩ : syracuseStep 98840645 = 18532621) B18532621
theorem B65893763 : Blo 2031435 65893763 := bstep (se 1 (by rfl) ⟨49420322, by rfl⟩ : syracuseStep 65893763 = 98840645) B98840645
theorem B43929175 : Blo 2031435 43929175 := bstep (se 1 (by rfl) ⟨32946881, by rfl⟩ : syracuseStep 43929175 = 65893763) B65893763
theorem B58572233 : Blo 2031435 58572233 := bstep (se 2 (by rfl) ⟨21964587, by rfl⟩ : syracuseStep 58572233 = 43929175) B43929175
theorem B39048155 : Blo 2031435 39048155 := bstep (se 1 (by rfl) ⟨29286116, by rfl⟩ : syracuseStep 39048155 = 58572233) B58572233
theorem B26032103 : Blo 2031435 26032103 := bstep (se 1 (by rfl) ⟨19524077, by rfl⟩ : syracuseStep 26032103 = 39048155) B39048155
theorem B17354735 : Blo 2031435 17354735 := bstep (se 1 (by rfl) ⟨13016051, by rfl⟩ : syracuseStep 17354735 = 26032103) B26032103
theorem B11569823 : Blo 2031435 11569823 := bstep (se 1 (by rfl) ⟨8677367, by rfl⟩ : syracuseStep 11569823 = 17354735) B17354735
theorem B7713215 : Blo 2031435 7713215 := bstep (se 1 (by rfl) ⟨5784911, by rfl⟩ : syracuseStep 7713215 = 11569823) B11569823
theorem B5142143 : Blo 2031435 5142143 := bstep (se 1 (by rfl) ⟨3856607, by rfl⟩ : syracuseStep 5142143 = 7713215) B7713215
theorem B3428095 : Blo 2031435 3428095 := bstep (se 1 (by rfl) ⟨2571071, by rfl⟩ : syracuseStep 3428095 = 5142143) B5142143
theorem B4570793 : Blo 2031435 4570793 := bstep (se 2 (by rfl) ⟨1714047, by rfl⟩ : syracuseStep 4570793 = 3428095) B3428095
theorem B3047195 : Blo 2031435 3047195 := bstep (se 1 (by rfl) ⟨2285396, by rfl⟩ : syracuseStep 3047195 = 4570793) B4570793
theorem B2031463 : Blo 2031435 2031463 := bstep (se 1 (by rfl) ⟨1523597, by rfl⟩ : syracuseStep 2031463 = 3047195) B3047195
theorem B2285401 : Blo 2031435 2285401 := bbase (se 2 (by rfl) ⟨857025, by rfl⟩ : syracuseStep 2285401 = 1714051) (by norm_num)
theorem B3047201 : Blo 2031435 3047201 := bstep (se 2 (by rfl) ⟨1142700, by rfl⟩ : syracuseStep 3047201 = 2285401) B2285401
theorem B2031467 : Blo 2031435 2031467 := bstep (se 1 (by rfl) ⟨1523600, by rfl⟩ : syracuseStep 2031467 = 3047201) B3047201
theorem B4338701 : Blo 2031435 4338701 := bbase (se 3 (by rfl) ⟨813506, by rfl⟩ : syracuseStep 4338701 = 1627013) (by norm_num)
theorem B2892467 : Blo 2031435 2892467 := bstep (se 1 (by rfl) ⟨2169350, by rfl⟩ : syracuseStep 2892467 = 4338701) B4338701
theorem B7713245 : Blo 2031435 7713245 := bstep (se 3 (by rfl) ⟨1446233, by rfl⟩ : syracuseStep 7713245 = 2892467) B2892467
theorem B5142163 : Blo 2031435 5142163 := bstep (se 1 (by rfl) ⟨3856622, by rfl⟩ : syracuseStep 5142163 = 7713245) B7713245
theorem B6856217 : Blo 2031435 6856217 := bstep (se 2 (by rfl) ⟨2571081, by rfl⟩ : syracuseStep 6856217 = 5142163) B5142163
theorem B4570811 : Blo 2031435 4570811 := bstep (se 1 (by rfl) ⟨3428108, by rfl⟩ : syracuseStep 4570811 = 6856217) B6856217
theorem B3047207 : Blo 2031435 3047207 := bstep (se 1 (by rfl) ⟨2285405, by rfl⟩ : syracuseStep 3047207 = 4570811) B4570811
theorem B2031471 : Blo 2031435 2031471 := bstep (se 1 (by rfl) ⟨1523603, by rfl⟩ : syracuseStep 2031471 = 3047207) B3047207
theorem B3047213 : Blo 2031435 3047213 := bbase (se 3 (by rfl) ⟨571352, by rfl⟩ : syracuseStep 3047213 = 1142705) (by norm_num)
theorem B2031475 : Blo 2031435 2031475 := bstep (se 1 (by rfl) ⟨1523606, by rfl⟩ : syracuseStep 2031475 = 3047213) B3047213
theorem B4570829 : Blo 2031435 4570829 := bbase (se 3 (by rfl) ⟨857030, by rfl⟩ : syracuseStep 4570829 = 1714061) (by norm_num)
theorem B3047219 : Blo 2031435 3047219 := bstep (se 1 (by rfl) ⟨2285414, by rfl⟩ : syracuseStep 3047219 = 4570829) B4570829
theorem B2031479 : Blo 2031435 2031479 := bstep (se 1 (by rfl) ⟨1523609, by rfl⟩ : syracuseStep 2031479 = 3047219) B3047219
theorem B2571097 : Blo 2031435 2571097 := bbase (se 2 (by rfl) ⟨964161, by rfl⟩ : syracuseStep 2571097 = 1928323) (by norm_num)
theorem B3428129 : Blo 2031435 3428129 := bstep (se 2 (by rfl) ⟨1285548, by rfl⟩ : syracuseStep 3428129 = 2571097) B2571097
theorem B2285419 : Blo 2031435 2285419 := bstep (se 1 (by rfl) ⟨1714064, by rfl⟩ : syracuseStep 2285419 = 3428129) B3428129
theorem B3047225 : Blo 2031435 3047225 := bstep (se 2 (by rfl) ⟨1142709, by rfl⟩ : syracuseStep 3047225 = 2285419) B2285419
theorem B2031483 : Blo 2031435 2031483 := bstep (se 1 (by rfl) ⟨1523612, by rfl⟩ : syracuseStep 2031483 = 3047225) B3047225
theorem B4881077 : Blo 2031435 4881077 := bbase (se 5 (by rfl) ⟨228800, by rfl⟩ : syracuseStep 4881077 = 457601) (by norm_num)
theorem B3254051 : Blo 2031435 3254051 := bstep (se 1 (by rfl) ⟨2440538, by rfl⟩ : syracuseStep 3254051 = 4881077) B4881077
theorem B8677469 : Blo 2031435 8677469 := bstep (se 3 (by rfl) ⟨1627025, by rfl⟩ : syracuseStep 8677469 = 3254051) B3254051
theorem B23139917 : Blo 2031435 23139917 := bstep (se 3 (by rfl) ⟨4338734, by rfl⟩ : syracuseStep 23139917 = 8677469) B8677469
theorem B15426611 : Blo 2031435 15426611 := bstep (se 1 (by rfl) ⟨11569958, by rfl⟩ : syracuseStep 15426611 = 23139917) B23139917
theorem B10284407 : Blo 2031435 10284407 := bstep (se 1 (by rfl) ⟨7713305, by rfl⟩ : syracuseStep 10284407 = 15426611) B15426611
theorem B6856271 : Blo 2031435 6856271 := bstep (se 1 (by rfl) ⟨5142203, by rfl⟩ : syracuseStep 6856271 = 10284407) B10284407
theorem B4570847 : Blo 2031435 4570847 := bstep (se 1 (by rfl) ⟨3428135, by rfl⟩ : syracuseStep 4570847 = 6856271) B6856271
theorem B3047231 : Blo 2031435 3047231 := bstep (se 1 (by rfl) ⟨2285423, by rfl⟩ : syracuseStep 3047231 = 4570847) B4570847
theorem B2031487 : Blo 2031435 2031487 := bstep (se 1 (by rfl) ⟨1523615, by rfl⟩ : syracuseStep 2031487 = 3047231) B3047231
theorem B3047237 : Blo 2031435 3047237 := bbase (se 4 (by rfl) ⟨285678, by rfl⟩ : syracuseStep 3047237 = 571357) (by norm_num)
theorem B2031491 : Blo 2031435 2031491 := bstep (se 1 (by rfl) ⟨1523618, by rfl⟩ : syracuseStep 2031491 = 3047237) B3047237
theorem B3428149 : Blo 2031435 3428149 := bbase (se 5 (by rfl) ⟨160694, by rfl⟩ : syracuseStep 3428149 = 321389) (by norm_num)
theorem B4570865 : Blo 2031435 4570865 := bstep (se 2 (by rfl) ⟨1714074, by rfl⟩ : syracuseStep 4570865 = 3428149) B3428149
theorem B3047243 : Blo 2031435 3047243 := bstep (se 1 (by rfl) ⟨2285432, by rfl⟩ : syracuseStep 3047243 = 4570865) B4570865
theorem B2031495 : Blo 2031435 2031495 := bstep (se 1 (by rfl) ⟨1523621, by rfl⟩ : syracuseStep 2031495 = 3047243) B3047243
theorem B2285437 : Blo 2031435 2285437 := bbase (se 3 (by rfl) ⟨428519, by rfl⟩ : syracuseStep 2285437 = 857039) (by norm_num)
theorem B3047249 : Blo 2031435 3047249 := bstep (se 2 (by rfl) ⟨1142718, by rfl⟩ : syracuseStep 3047249 = 2285437) B2285437
theorem B2031499 : Blo 2031435 2031499 := bstep (se 1 (by rfl) ⟨1523624, by rfl⟩ : syracuseStep 2031499 = 3047249) B3047249
theorem B6856325 : Blo 2031435 6856325 := bbase (se 4 (by rfl) ⟨642780, by rfl⟩ : syracuseStep 6856325 = 1285561) (by norm_num)
theorem B4570883 : Blo 2031435 4570883 := bstep (se 1 (by rfl) ⟨3428162, by rfl⟩ : syracuseStep 4570883 = 6856325) B6856325
theorem B3047255 : Blo 2031435 3047255 := bstep (se 1 (by rfl) ⟨2285441, by rfl⟩ : syracuseStep 3047255 = 4570883) B4570883
theorem B2031503 : Blo 2031435 2031503 := bstep (se 1 (by rfl) ⟨1523627, by rfl⟩ : syracuseStep 2031503 = 3047255) B3047255
theorem B3047261 : Blo 2031435 3047261 := bbase (se 3 (by rfl) ⟨571361, by rfl⟩ : syracuseStep 3047261 = 1142723) (by norm_num)
theorem B2031507 : Blo 2031435 2031507 := bstep (se 1 (by rfl) ⟨1523630, by rfl⟩ : syracuseStep 2031507 = 3047261) B3047261
theorem B4570901 : Blo 2031435 4570901 := bbase (se 6 (by rfl) ⟨107130, by rfl⟩ : syracuseStep 4570901 = 214261) (by norm_num)
theorem B3047267 : Blo 2031435 3047267 := bstep (se 1 (by rfl) ⟨2285450, by rfl⟩ : syracuseStep 3047267 = 4570901) B4570901
theorem B2031511 : Blo 2031435 2031511 := bstep (se 1 (by rfl) ⟨1523633, by rfl⟩ : syracuseStep 2031511 = 3047267) B3047267
theorem B7713413 : Blo 2031435 7713413 := bbase (se 4 (by rfl) ⟨723132, by rfl⟩ : syracuseStep 7713413 = 1446265) (by norm_num)
theorem B5142275 : Blo 2031435 5142275 := bstep (se 1 (by rfl) ⟨3856706, by rfl⟩ : syracuseStep 5142275 = 7713413) B7713413
theorem B3428183 : Blo 2031435 3428183 := bstep (se 1 (by rfl) ⟨2571137, by rfl⟩ : syracuseStep 3428183 = 5142275) B5142275
theorem B2285455 : Blo 2031435 2285455 := bstep (se 1 (by rfl) ⟨1714091, by rfl⟩ : syracuseStep 2285455 = 3428183) B3428183
theorem B3047273 : Blo 2031435 3047273 := bstep (se 2 (by rfl) ⟨1142727, by rfl⟩ : syracuseStep 3047273 = 2285455) B2285455
theorem B2031515 : Blo 2031435 2031515 := bstep (se 1 (by rfl) ⟨1523636, by rfl⟩ : syracuseStep 2031515 = 3047273) B3047273
theorem B2440577 : Blo 2031435 2440577 := bbase (se 2 (by rfl) ⟨915216, by rfl⟩ : syracuseStep 2440577 = 1830433) (by norm_num)
theorem B6508205 : Blo 2031435 6508205 := bstep (se 3 (by rfl) ⟨1220288, by rfl⟩ : syracuseStep 6508205 = 2440577) B2440577
theorem B4338803 : Blo 2031435 4338803 := bstep (se 1 (by rfl) ⟨3254102, by rfl⟩ : syracuseStep 4338803 = 6508205) B6508205
theorem B11570141 : Blo 2031435 11570141 := bstep (se 3 (by rfl) ⟨2169401, by rfl⟩ : syracuseStep 11570141 = 4338803) B4338803
theorem B7713427 : Blo 2031435 7713427 := bstep (se 1 (by rfl) ⟨5785070, by rfl⟩ : syracuseStep 7713427 = 11570141) B11570141
theorem B10284569 : Blo 2031435 10284569 := bstep (se 2 (by rfl) ⟨3856713, by rfl⟩ : syracuseStep 10284569 = 7713427) B7713427
theorem B6856379 : Blo 2031435 6856379 := bstep (se 1 (by rfl) ⟨5142284, by rfl⟩ : syracuseStep 6856379 = 10284569) B10284569
theorem B4570919 : Blo 2031435 4570919 := bstep (se 1 (by rfl) ⟨3428189, by rfl⟩ : syracuseStep 4570919 = 6856379) B6856379
theorem B3047279 : Blo 2031435 3047279 := bstep (se 1 (by rfl) ⟨2285459, by rfl⟩ : syracuseStep 3047279 = 4570919) B4570919
theorem B2031519 : Blo 2031435 2031519 := bstep (se 1 (by rfl) ⟨1523639, by rfl⟩ : syracuseStep 2031519 = 3047279) B3047279
theorem B3047285 : Blo 2031435 3047285 := bbase (se 5 (by rfl) ⟨142841, by rfl⟩ : syracuseStep 3047285 = 285683) (by norm_num)
theorem B2031523 : Blo 2031435 2031523 := bstep (se 1 (by rfl) ⟨1523642, by rfl⟩ : syracuseStep 2031523 = 3047285) B3047285
theorem B4338821 : Blo 2031435 4338821 := bbase (se 4 (by rfl) ⟨406764, by rfl⟩ : syracuseStep 4338821 = 813529) (by norm_num)
theorem B2892547 : Blo 2031435 2892547 := bstep (se 1 (by rfl) ⟨2169410, by rfl⟩ : syracuseStep 2892547 = 4338821) B4338821
theorem B3856729 : Blo 2031435 3856729 := bstep (se 2 (by rfl) ⟨1446273, by rfl⟩ : syracuseStep 3856729 = 2892547) B2892547
theorem B5142305 : Blo 2031435 5142305 := bstep (se 2 (by rfl) ⟨1928364, by rfl⟩ : syracuseStep 5142305 = 3856729) B3856729
theorem B3428203 : Blo 2031435 3428203 := bstep (se 1 (by rfl) ⟨2571152, by rfl⟩ : syracuseStep 3428203 = 5142305) B5142305
theorem B4570937 : Blo 2031435 4570937 := bstep (se 2 (by rfl) ⟨1714101, by rfl⟩ : syracuseStep 4570937 = 3428203) B3428203
theorem B3047291 : Blo 2031435 3047291 := bstep (se 1 (by rfl) ⟨2285468, by rfl⟩ : syracuseStep 3047291 = 4570937) B4570937
theorem B2031527 : Blo 2031435 2031527 := bstep (se 1 (by rfl) ⟨1523645, by rfl⟩ : syracuseStep 2031527 = 3047291) B3047291
theorem B2285473 : Blo 2031435 2285473 := bbase (se 2 (by rfl) ⟨857052, by rfl⟩ : syracuseStep 2285473 = 1714105) (by norm_num)
theorem B3047297 : Blo 2031435 3047297 := bstep (se 2 (by rfl) ⟨1142736, by rfl⟩ : syracuseStep 3047297 = 2285473) B2285473
theorem B2031531 : Blo 2031435 2031531 := bstep (se 1 (by rfl) ⟨1523648, by rfl⟩ : syracuseStep 2031531 = 3047297) B3047297
theorem B5142325 : Blo 2031435 5142325 := bbase (se 5 (by rfl) ⟨241046, by rfl⟩ : syracuseStep 5142325 = 482093) (by norm_num)
theorem B6856433 : Blo 2031435 6856433 := bstep (se 2 (by rfl) ⟨2571162, by rfl⟩ : syracuseStep 6856433 = 5142325) B5142325
theorem B4570955 : Blo 2031435 4570955 := bstep (se 1 (by rfl) ⟨3428216, by rfl⟩ : syracuseStep 4570955 = 6856433) B6856433
theorem B3047303 : Blo 2031435 3047303 := bstep (se 1 (by rfl) ⟨2285477, by rfl⟩ : syracuseStep 3047303 = 4570955) B4570955
theorem B2031535 : Blo 2031435 2031535 := bstep (se 1 (by rfl) ⟨1523651, by rfl⟩ : syracuseStep 2031535 = 3047303) B3047303
theorem B3047309 : Blo 2031435 3047309 := bbase (se 3 (by rfl) ⟨571370, by rfl⟩ : syracuseStep 3047309 = 1142741) (by norm_num)
theorem B2031539 : Blo 2031435 2031539 := bstep (se 1 (by rfl) ⟨1523654, by rfl⟩ : syracuseStep 2031539 = 3047309) B3047309
theorem B4570973 : Blo 2031435 4570973 := bbase (se 3 (by rfl) ⟨857057, by rfl⟩ : syracuseStep 4570973 = 1714115) (by norm_num)
theorem B3047315 : Blo 2031435 3047315 := bstep (se 1 (by rfl) ⟨2285486, by rfl⟩ : syracuseStep 3047315 = 4570973) B4570973
theorem B2031543 : Blo 2031435 2031543 := bstep (se 1 (by rfl) ⟨1523657, by rfl⟩ : syracuseStep 2031543 = 3047315) B3047315
theorem B3428237 : Blo 2031435 3428237 := bbase (se 3 (by rfl) ⟨642794, by rfl⟩ : syracuseStep 3428237 = 1285589) (by norm_num)
theorem B2285491 : Blo 2031435 2285491 := bstep (se 1 (by rfl) ⟨1714118, by rfl⟩ : syracuseStep 2285491 = 3428237) B3428237
theorem B3047321 : Blo 2031435 3047321 := bstep (se 2 (by rfl) ⟨1142745, by rfl⟩ : syracuseStep 3047321 = 2285491) B2285491
theorem B2031547 : Blo 2031435 2031547 := bstep (se 1 (by rfl) ⟨1523660, by rfl⟩ : syracuseStep 2031547 = 3047321) B3047321
theorem B4633357 : Blo 2031435 4633357 := bbase (se 3 (by rfl) ⟨868754, by rfl⟩ : syracuseStep 4633357 = 1737509) (by norm_num)
theorem B6177809 : Blo 2031435 6177809 := bstep (se 2 (by rfl) ⟨2316678, by rfl⟩ : syracuseStep 6177809 = 4633357) B4633357
theorem B4118539 : Blo 2031435 4118539 := bstep (se 1 (by rfl) ⟨3088904, by rfl⟩ : syracuseStep 4118539 = 6177809) B6177809
theorem B5491385 : Blo 2031435 5491385 := bstep (se 2 (by rfl) ⟨2059269, by rfl⟩ : syracuseStep 5491385 = 4118539) B4118539
theorem B3660923 : Blo 2031435 3660923 := bstep (se 1 (by rfl) ⟨2745692, by rfl⟩ : syracuseStep 3660923 = 5491385) B5491385
theorem B9762461 : Blo 2031435 9762461 := bstep (se 3 (by rfl) ⟨1830461, by rfl⟩ : syracuseStep 9762461 = 3660923) B3660923
theorem B6508307 : Blo 2031435 6508307 := bstep (se 1 (by rfl) ⟨4881230, by rfl⟩ : syracuseStep 6508307 = 9762461) B9762461
theorem B17355485 : Blo 2031435 17355485 := bstep (se 3 (by rfl) ⟨3254153, by rfl⟩ : syracuseStep 17355485 = 6508307) B6508307
theorem B11570323 : Blo 2031435 11570323 := bstep (se 1 (by rfl) ⟨8677742, by rfl⟩ : syracuseStep 11570323 = 17355485) B17355485
theorem B15427097 : Blo 2031435 15427097 := bstep (se 2 (by rfl) ⟨5785161, by rfl⟩ : syracuseStep 15427097 = 11570323) B11570323
theorem B10284731 : Blo 2031435 10284731 := bstep (se 1 (by rfl) ⟨7713548, by rfl⟩ : syracuseStep 10284731 = 15427097) B15427097
theorem B6856487 : Blo 2031435 6856487 := bstep (se 1 (by rfl) ⟨5142365, by rfl⟩ : syracuseStep 6856487 = 10284731) B10284731
theorem B4570991 : Blo 2031435 4570991 := bstep (se 1 (by rfl) ⟨3428243, by rfl⟩ : syracuseStep 4570991 = 6856487) B6856487
theorem B3047327 : Blo 2031435 3047327 := bstep (se 1 (by rfl) ⟨2285495, by rfl⟩ : syracuseStep 3047327 = 4570991) B4570991
theorem B2031551 : Blo 2031435 2031551 := bstep (se 1 (by rfl) ⟨1523663, by rfl⟩ : syracuseStep 2031551 = 3047327) B3047327
theorem B3047333 : Blo 2031435 3047333 := bbase (se 4 (by rfl) ⟨285687, by rfl⟩ : syracuseStep 3047333 = 571375) (by norm_num)
theorem B2031555 : Blo 2031435 2031555 := bstep (se 1 (by rfl) ⟨1523666, by rfl⟩ : syracuseStep 2031555 = 3047333) B3047333
theorem B2571193 : Blo 2031435 2571193 := bbase (se 2 (by rfl) ⟨964197, by rfl⟩ : syracuseStep 2571193 = 1928395) (by norm_num)
theorem B3428257 : Blo 2031435 3428257 := bstep (se 2 (by rfl) ⟨1285596, by rfl⟩ : syracuseStep 3428257 = 2571193) B2571193
theorem B4571009 : Blo 2031435 4571009 := bstep (se 2 (by rfl) ⟨1714128, by rfl⟩ : syracuseStep 4571009 = 3428257) B3428257
theorem B3047339 : Blo 2031435 3047339 := bstep (se 1 (by rfl) ⟨2285504, by rfl⟩ : syracuseStep 3047339 = 4571009) B4571009
theorem B2031559 : Blo 2031435 2031559 := bstep (se 1 (by rfl) ⟨1523669, by rfl⟩ : syracuseStep 2031559 = 3047339) B3047339
theorem B2285509 : Blo 2031435 2285509 := bbase (se 4 (by rfl) ⟨214266, by rfl⟩ : syracuseStep 2285509 = 428533) (by norm_num)
theorem B3047345 : Blo 2031435 3047345 := bstep (se 2 (by rfl) ⟨1142754, by rfl⟩ : syracuseStep 3047345 = 2285509) B2285509
theorem B2031563 : Blo 2031435 2031563 := bstep (se 1 (by rfl) ⟨1523672, by rfl⟩ : syracuseStep 2031563 = 3047345) B3047345
theorem B3856805 : Blo 2031435 3856805 := bbase (se 4 (by rfl) ⟨361575, by rfl⟩ : syracuseStep 3856805 = 723151) (by norm_num)
theorem B2571203 : Blo 2031435 2571203 := bstep (se 1 (by rfl) ⟨1928402, by rfl⟩ : syracuseStep 2571203 = 3856805) B3856805
theorem B6856541 : Blo 2031435 6856541 := bstep (se 3 (by rfl) ⟨1285601, by rfl⟩ : syracuseStep 6856541 = 2571203) B2571203
theorem B4571027 : Blo 2031435 4571027 := bstep (se 1 (by rfl) ⟨3428270, by rfl⟩ : syracuseStep 4571027 = 6856541) B6856541
theorem B3047351 : Blo 2031435 3047351 := bstep (se 1 (by rfl) ⟨2285513, by rfl⟩ : syracuseStep 3047351 = 4571027) B4571027
theorem B2031567 : Blo 2031435 2031567 := bstep (se 1 (by rfl) ⟨1523675, by rfl⟩ : syracuseStep 2031567 = 3047351) B3047351
theorem B3047357 : Blo 2031435 3047357 := bbase (se 3 (by rfl) ⟨571379, by rfl⟩ : syracuseStep 3047357 = 1142759) (by norm_num)
theorem B2031571 : Blo 2031435 2031571 := bstep (se 1 (by rfl) ⟨1523678, by rfl⟩ : syracuseStep 2031571 = 3047357) B3047357
theorem B4571045 : Blo 2031435 4571045 := bbase (se 4 (by rfl) ⟨428535, by rfl⟩ : syracuseStep 4571045 = 857071) (by norm_num)
theorem B3047363 : Blo 2031435 3047363 := bstep (se 1 (by rfl) ⟨2285522, by rfl⟩ : syracuseStep 3047363 = 4571045) B4571045
theorem B2031575 : Blo 2031435 2031575 := bstep (se 1 (by rfl) ⟨1523681, by rfl⟩ : syracuseStep 2031575 = 3047363) B3047363
theorem B5142437 : Blo 2031435 5142437 := bbase (se 4 (by rfl) ⟨482103, by rfl⟩ : syracuseStep 5142437 = 964207) (by norm_num)
theorem B3428291 : Blo 2031435 3428291 := bstep (se 1 (by rfl) ⟨2571218, by rfl⟩ : syracuseStep 3428291 = 5142437) B5142437
theorem B2285527 : Blo 2031435 2285527 := bstep (se 1 (by rfl) ⟨1714145, by rfl⟩ : syracuseStep 2285527 = 3428291) B3428291
theorem B3047369 : Blo 2031435 3047369 := bstep (se 2 (by rfl) ⟨1142763, by rfl⟩ : syracuseStep 3047369 = 2285527) B2285527
theorem B2031579 : Blo 2031435 2031579 := bstep (se 1 (by rfl) ⟨1523684, by rfl⟩ : syracuseStep 2031579 = 3047369) B3047369
theorem B5785253 : Blo 2031435 5785253 := bbase (se 4 (by rfl) ⟨542367, by rfl⟩ : syracuseStep 5785253 = 1084735) (by norm_num)
theorem B3856835 : Blo 2031435 3856835 := bstep (se 1 (by rfl) ⟨2892626, by rfl⟩ : syracuseStep 3856835 = 5785253) B5785253
theorem B10284893 : Blo 2031435 10284893 := bstep (se 3 (by rfl) ⟨1928417, by rfl⟩ : syracuseStep 10284893 = 3856835) B3856835
theorem B6856595 : Blo 2031435 6856595 := bstep (se 1 (by rfl) ⟨5142446, by rfl⟩ : syracuseStep 6856595 = 10284893) B10284893
theorem B4571063 : Blo 2031435 4571063 := bstep (se 1 (by rfl) ⟨3428297, by rfl⟩ : syracuseStep 4571063 = 6856595) B6856595
theorem B3047375 : Blo 2031435 3047375 := bstep (se 1 (by rfl) ⟨2285531, by rfl⟩ : syracuseStep 3047375 = 4571063) B4571063
theorem B2031583 : Blo 2031435 2031583 := bstep (se 1 (by rfl) ⟨1523687, by rfl⟩ : syracuseStep 2031583 = 3047375) B3047375
theorem B3047381 : Blo 2031435 3047381 := bbase (se 7 (by rfl) ⟨35711, by rfl⟩ : syracuseStep 3047381 = 71423) (by norm_num)
theorem B2031587 : Blo 2031435 2031587 := bstep (se 1 (by rfl) ⟨1523690, by rfl⟩ : syracuseStep 2031587 = 3047381) B3047381
theorem B7713701 : Blo 2031435 7713701 := bbase (se 4 (by rfl) ⟨723159, by rfl⟩ : syracuseStep 7713701 = 1446319) (by norm_num)
theorem B5142467 : Blo 2031435 5142467 := bstep (se 1 (by rfl) ⟨3856850, by rfl⟩ : syracuseStep 5142467 = 7713701) B7713701
theorem B3428311 : Blo 2031435 3428311 := bstep (se 1 (by rfl) ⟨2571233, by rfl⟩ : syracuseStep 3428311 = 5142467) B5142467
theorem B4571081 : Blo 2031435 4571081 := bstep (se 2 (by rfl) ⟨1714155, by rfl⟩ : syracuseStep 4571081 = 3428311) B3428311
theorem B3047387 : Blo 2031435 3047387 := bstep (se 1 (by rfl) ⟨2285540, by rfl⟩ : syracuseStep 3047387 = 4571081) B4571081
theorem B2031591 : Blo 2031435 2031591 := bstep (se 1 (by rfl) ⟨1523693, by rfl⟩ : syracuseStep 2031591 = 3047387) B3047387
theorem B2285545 : Blo 2031435 2285545 := bbase (se 2 (by rfl) ⟨857079, by rfl⟩ : syracuseStep 2285545 = 1714159) (by norm_num)
theorem B3047393 : Blo 2031435 3047393 := bstep (se 2 (by rfl) ⟨1142772, by rfl⟩ : syracuseStep 3047393 = 2285545) B2285545
theorem B2031595 : Blo 2031435 2031595 := bstep (se 1 (by rfl) ⟨1523696, by rfl⟩ : syracuseStep 2031595 = 3047393) B3047393
theorem B7322021 : Blo 2031435 7322021 := bbase (se 4 (by rfl) ⟨686439, by rfl⟩ : syracuseStep 7322021 = 1372879) (by norm_num)
theorem B4881347 : Blo 2031435 4881347 := bstep (se 1 (by rfl) ⟨3661010, by rfl⟩ : syracuseStep 4881347 = 7322021) B7322021
theorem B3254231 : Blo 2031435 3254231 := bstep (se 1 (by rfl) ⟨2440673, by rfl⟩ : syracuseStep 3254231 = 4881347) B4881347
theorem B2169487 : Blo 2031435 2169487 := bstep (se 1 (by rfl) ⟨1627115, by rfl⟩ : syracuseStep 2169487 = 3254231) B3254231
theorem B11570597 : Blo 2031435 11570597 := bstep (se 4 (by rfl) ⟨1084743, by rfl⟩ : syracuseStep 11570597 = 2169487) B2169487
theorem B7713731 : Blo 2031435 7713731 := bstep (se 1 (by rfl) ⟨5785298, by rfl⟩ : syracuseStep 7713731 = 11570597) B11570597
theorem B5142487 : Blo 2031435 5142487 := bstep (se 1 (by rfl) ⟨3856865, by rfl⟩ : syracuseStep 5142487 = 7713731) B7713731
theorem B6856649 : Blo 2031435 6856649 := bstep (se 2 (by rfl) ⟨2571243, by rfl⟩ : syracuseStep 6856649 = 5142487) B5142487
theorem B4571099 : Blo 2031435 4571099 := bstep (se 1 (by rfl) ⟨3428324, by rfl⟩ : syracuseStep 4571099 = 6856649) B6856649
theorem B3047399 : Blo 2031435 3047399 := bstep (se 1 (by rfl) ⟨2285549, by rfl⟩ : syracuseStep 3047399 = 4571099) B4571099
theorem B2031599 : Blo 2031435 2031599 := bstep (se 1 (by rfl) ⟨1523699, by rfl⟩ : syracuseStep 2031599 = 3047399) B3047399
theorem B3047405 : Blo 2031435 3047405 := bbase (se 3 (by rfl) ⟨571388, by rfl⟩ : syracuseStep 3047405 = 1142777) (by norm_num)
theorem B2031603 : Blo 2031435 2031603 := bstep (se 1 (by rfl) ⟨1523702, by rfl⟩ : syracuseStep 2031603 = 3047405) B3047405
theorem B4571117 : Blo 2031435 4571117 := bbase (se 3 (by rfl) ⟨857084, by rfl⟩ : syracuseStep 4571117 = 1714169) (by norm_num)
theorem B3047411 : Blo 2031435 3047411 := bstep (se 1 (by rfl) ⟨2285558, by rfl⟩ : syracuseStep 3047411 = 4571117) B4571117
theorem B2031607 : Blo 2031435 2031607 := bstep (se 1 (by rfl) ⟨1523705, by rfl⟩ : syracuseStep 2031607 = 3047411) B3047411
theorem B6950245 : Blo 2031435 6950245 := bbase (se 4 (by rfl) ⟨651585, by rfl⟩ : syracuseStep 6950245 = 1303171) (by norm_num)
theorem B9266993 : Blo 2031435 9266993 := bstep (se 2 (by rfl) ⟨3475122, by rfl⟩ : syracuseStep 9266993 = 6950245) B6950245
theorem B6177995 : Blo 2031435 6177995 := bstep (se 1 (by rfl) ⟨4633496, by rfl⟩ : syracuseStep 6177995 = 9266993) B9266993
theorem B4118663 : Blo 2031435 4118663 := bstep (se 1 (by rfl) ⟨3088997, by rfl⟩ : syracuseStep 4118663 = 6177995) B6177995
theorem B2745775 : Blo 2031435 2745775 := bstep (se 1 (by rfl) ⟨2059331, by rfl⟩ : syracuseStep 2745775 = 4118663) B4118663
theorem B3661033 : Blo 2031435 3661033 := bstep (se 2 (by rfl) ⟨1372887, by rfl⟩ : syracuseStep 3661033 = 2745775) B2745775
theorem B4881377 : Blo 2031435 4881377 := bstep (se 2 (by rfl) ⟨1830516, by rfl⟩ : syracuseStep 4881377 = 3661033) B3661033
theorem B3254251 : Blo 2031435 3254251 := bstep (se 1 (by rfl) ⟨2440688, by rfl⟩ : syracuseStep 3254251 = 4881377) B4881377
theorem B4339001 : Blo 2031435 4339001 := bstep (se 2 (by rfl) ⟨1627125, by rfl⟩ : syracuseStep 4339001 = 3254251) B3254251
theorem B2892667 : Blo 2031435 2892667 := bstep (se 1 (by rfl) ⟨2169500, by rfl⟩ : syracuseStep 2892667 = 4339001) B4339001
theorem B3856889 : Blo 2031435 3856889 := bstep (se 2 (by rfl) ⟨1446333, by rfl⟩ : syracuseStep 3856889 = 2892667) B2892667
theorem B2571259 : Blo 2031435 2571259 := bstep (se 1 (by rfl) ⟨1928444, by rfl⟩ : syracuseStep 2571259 = 3856889) B3856889
theorem B3428345 : Blo 2031435 3428345 := bstep (se 2 (by rfl) ⟨1285629, by rfl⟩ : syracuseStep 3428345 = 2571259) B2571259
theorem B2285563 : Blo 2031435 2285563 := bstep (se 1 (by rfl) ⟨1714172, by rfl⟩ : syracuseStep 2285563 = 3428345) B3428345
theorem B3047417 : Blo 2031435 3047417 := bstep (se 2 (by rfl) ⟨1142781, by rfl⟩ : syracuseStep 3047417 = 2285563) B2285563
theorem B2031611 : Blo 2031435 2031611 := bstep (se 1 (by rfl) ⟨1523708, by rfl⟩ : syracuseStep 2031611 = 3047417) B3047417
theorem B4760797 : Blo 2031435 4760797 := bbase (se 3 (by rfl) ⟨892649, by rfl⟩ : syracuseStep 4760797 = 1785299) (by norm_num)
theorem B6347729 : Blo 2031435 6347729 := bstep (se 2 (by rfl) ⟨2380398, by rfl⟩ : syracuseStep 6347729 = 4760797) B4760797
theorem B4231819 : Blo 2031435 4231819 := bstep (se 1 (by rfl) ⟨3173864, by rfl⟩ : syracuseStep 4231819 = 6347729) B6347729
theorem B5642425 : Blo 2031435 5642425 := bstep (se 2 (by rfl) ⟨2115909, by rfl⟩ : syracuseStep 5642425 = 4231819) B4231819
theorem B7523233 : Blo 2031435 7523233 := bstep (se 2 (by rfl) ⟨2821212, by rfl⟩ : syracuseStep 7523233 = 5642425) B5642425
theorem B160495637 : Blo 2031435 160495637 := bstep (se 6 (by rfl) ⟨3761616, by rfl⟩ : syracuseStep 160495637 = 7523233) B7523233
theorem B1711953461 : Blo 2031435 1711953461 := bstep (se 5 (by rfl) ⟨80247818, by rfl⟩ : syracuseStep 1711953461 = 160495637) B160495637
theorem B1141302307 : Blo 2031435 1141302307 := bstep (se 1 (by rfl) ⟨855976730, by rfl⟩ : syracuseStep 1141302307 = 1711953461) B1711953461
theorem B1521736409 : Blo 2031435 1521736409 := bstep (se 2 (by rfl) ⟨570651153, by rfl⟩ : syracuseStep 1521736409 = 1141302307) B1141302307
theorem B4057963757 : Blo 2031435 4057963757 := bstep (se 3 (by rfl) ⟨760868204, by rfl⟩ : syracuseStep 4057963757 = 1521736409) B1521736409
theorem B2705309171 : Blo 2031435 2705309171 := bstep (se 1 (by rfl) ⟨2028981878, by rfl⟩ : syracuseStep 2705309171 = 4057963757) B4057963757
theorem B1803539447 : Blo 2031435 1803539447 := bstep (se 1 (by rfl) ⟨1352654585, by rfl⟩ : syracuseStep 1803539447 = 2705309171) B2705309171
theorem B1202359631 : Blo 2031435 1202359631 := bstep (se 1 (by rfl) ⟨901769723, by rfl⟩ : syracuseStep 1202359631 = 1803539447) B1803539447
theorem B3206292349 : Blo 2031435 3206292349 := bstep (se 3 (by rfl) ⟨601179815, by rfl⟩ : syracuseStep 3206292349 = 1202359631) B1202359631
theorem B4275056465 : Blo 2031435 4275056465 := bstep (se 2 (by rfl) ⟨1603146174, by rfl⟩ : syracuseStep 4275056465 = 3206292349) B3206292349
theorem B2850037643 : Blo 2031435 2850037643 := bstep (se 1 (by rfl) ⟨2137528232, by rfl⟩ : syracuseStep 2850037643 = 4275056465) B4275056465
theorem B1900025095 : Blo 2031435 1900025095 := bstep (se 1 (by rfl) ⟨1425018821, by rfl⟩ : syracuseStep 1900025095 = 2850037643) B2850037643
theorem B2533366793 : Blo 2031435 2533366793 := bstep (se 2 (by rfl) ⟨950012547, by rfl⟩ : syracuseStep 2533366793 = 1900025095) B1900025095
theorem B1688911195 : Blo 2031435 1688911195 := bstep (se 1 (by rfl) ⟨1266683396, by rfl⟩ : syracuseStep 1688911195 = 2533366793) B2533366793
theorem B2251881593 : Blo 2031435 2251881593 := bstep (se 2 (by rfl) ⟨844455597, by rfl⟩ : syracuseStep 2251881593 = 1688911195) B1688911195
theorem B1501254395 : Blo 2031435 1501254395 := bstep (se 1 (by rfl) ⟨1125940796, by rfl⟩ : syracuseStep 1501254395 = 2251881593) B2251881593
theorem B1000836263 : Blo 2031435 1000836263 := bstep (se 1 (by rfl) ⟨750627197, by rfl⟩ : syracuseStep 1000836263 = 1501254395) B1501254395
theorem B667224175 : Blo 2031435 667224175 := bstep (se 1 (by rfl) ⟨500418131, by rfl⟩ : syracuseStep 667224175 = 1000836263) B1000836263
theorem B889632233 : Blo 2031435 889632233 := bstep (se 2 (by rfl) ⟨333612087, by rfl⟩ : syracuseStep 889632233 = 667224175) B667224175
theorem B593088155 : Blo 2031435 593088155 := bstep (se 1 (by rfl) ⟨444816116, by rfl⟩ : syracuseStep 593088155 = 889632233) B889632233
theorem B395392103 : Blo 2031435 395392103 := bstep (se 1 (by rfl) ⟨296544077, by rfl⟩ : syracuseStep 395392103 = 593088155) B593088155
theorem B263594735 : Blo 2031435 263594735 := bstep (se 1 (by rfl) ⟨197696051, by rfl⟩ : syracuseStep 263594735 = 395392103) B395392103
theorem B175729823 : Blo 2031435 175729823 := bstep (se 1 (by rfl) ⟨131797367, by rfl⟩ : syracuseStep 175729823 = 263594735) B263594735
theorem B117153215 : Blo 2031435 117153215 := bstep (se 1 (by rfl) ⟨87864911, by rfl⟩ : syracuseStep 117153215 = 175729823) B175729823
theorem B78102143 : Blo 2031435 78102143 := bstep (se 1 (by rfl) ⟨58576607, by rfl⟩ : syracuseStep 78102143 = 117153215) B117153215
theorem B52068095 : Blo 2031435 52068095 := bstep (se 1 (by rfl) ⟨39051071, by rfl⟩ : syracuseStep 52068095 = 78102143) B78102143
theorem B34712063 : Blo 2031435 34712063 := bstep (se 1 (by rfl) ⟨26034047, by rfl⟩ : syracuseStep 34712063 = 52068095) B52068095
theorem B23141375 : Blo 2031435 23141375 := bstep (se 1 (by rfl) ⟨17356031, by rfl⟩ : syracuseStep 23141375 = 34712063) B34712063
theorem B15427583 : Blo 2031435 15427583 := bstep (se 1 (by rfl) ⟨11570687, by rfl⟩ : syracuseStep 15427583 = 23141375) B23141375
theorem B10285055 : Blo 2031435 10285055 := bstep (se 1 (by rfl) ⟨7713791, by rfl⟩ : syracuseStep 10285055 = 15427583) B15427583
theorem B6856703 : Blo 2031435 6856703 := bstep (se 1 (by rfl) ⟨5142527, by rfl⟩ : syracuseStep 6856703 = 10285055) B10285055
theorem B4571135 : Blo 2031435 4571135 := bstep (se 1 (by rfl) ⟨3428351, by rfl⟩ : syracuseStep 4571135 = 6856703) B6856703
theorem B3047423 : Blo 2031435 3047423 := bstep (se 1 (by rfl) ⟨2285567, by rfl⟩ : syracuseStep 3047423 = 4571135) B4571135
theorem B2031615 : Blo 2031435 2031615 := bstep (se 1 (by rfl) ⟨1523711, by rfl⟩ : syracuseStep 2031615 = 3047423) B3047423
theorem B3047429 : Blo 2031435 3047429 := bbase (se 4 (by rfl) ⟨285696, by rfl⟩ : syracuseStep 3047429 = 571393) (by norm_num)
theorem B2031619 : Blo 2031435 2031619 := bstep (se 1 (by rfl) ⟨1523714, by rfl⟩ : syracuseStep 2031619 = 3047429) B3047429
theorem B3428365 : Blo 2031435 3428365 := bbase (se 3 (by rfl) ⟨642818, by rfl⟩ : syracuseStep 3428365 = 1285637) (by norm_num)
theorem B4571153 : Blo 2031435 4571153 := bstep (se 2 (by rfl) ⟨1714182, by rfl⟩ : syracuseStep 4571153 = 3428365) B3428365
theorem B3047435 : Blo 2031435 3047435 := bstep (se 1 (by rfl) ⟨2285576, by rfl⟩ : syracuseStep 3047435 = 4571153) B4571153
theorem B2031623 : Blo 2031435 2031623 := bstep (se 1 (by rfl) ⟨1523717, by rfl⟩ : syracuseStep 2031623 = 3047435) B3047435
theorem B2285581 : Blo 2031435 2285581 := bbase (se 3 (by rfl) ⟨428546, by rfl⟩ : syracuseStep 2285581 = 857093) (by norm_num)
theorem B3047441 : Blo 2031435 3047441 := bstep (se 2 (by rfl) ⟨1142790, by rfl⟩ : syracuseStep 3047441 = 2285581) B2285581
theorem B2031627 : Blo 2031435 2031627 := bstep (se 1 (by rfl) ⟨1523720, by rfl⟩ : syracuseStep 2031627 = 3047441) B3047441
theorem B6856757 : Blo 2031435 6856757 := bbase (se 5 (by rfl) ⟨321410, by rfl⟩ : syracuseStep 6856757 = 642821) (by norm_num)
theorem B4571171 : Blo 2031435 4571171 := bstep (se 1 (by rfl) ⟨3428378, by rfl⟩ : syracuseStep 4571171 = 6856757) B6856757
theorem B3047447 : Blo 2031435 3047447 := bstep (se 1 (by rfl) ⟨2285585, by rfl⟩ : syracuseStep 3047447 = 4571171) B4571171
theorem B2031631 : Blo 2031435 2031631 := bstep (se 1 (by rfl) ⟨1523723, by rfl⟩ : syracuseStep 2031631 = 3047447) B3047447
theorem B3047453 : Blo 2031435 3047453 := bbase (se 3 (by rfl) ⟨571397, by rfl⟩ : syracuseStep 3047453 = 1142795) (by norm_num)
theorem B2031635 : Blo 2031435 2031635 := bstep (se 1 (by rfl) ⟨1523726, by rfl⟩ : syracuseStep 2031635 = 3047453) B3047453
theorem B4571189 : Blo 2031435 4571189 := bbase (se 5 (by rfl) ⟨214274, by rfl⟩ : syracuseStep 4571189 = 428549) (by norm_num)
theorem B3047459 : Blo 2031435 3047459 := bstep (se 1 (by rfl) ⟨2285594, by rfl⟩ : syracuseStep 3047459 = 4571189) B4571189
theorem B2031639 : Blo 2031435 2031639 := bstep (se 1 (by rfl) ⟨1523729, by rfl⟩ : syracuseStep 2031639 = 3047459) B3047459
theorem B3089045 : Blo 2031435 3089045 := bbase (se 6 (by rfl) ⟨72399, by rfl⟩ : syracuseStep 3089045 = 144799) (by norm_num)
theorem B2059363 : Blo 2031435 2059363 := bstep (se 1 (by rfl) ⟨1544522, by rfl⟩ : syracuseStep 2059363 = 3089045) B3089045
theorem B10983269 : Blo 2031435 10983269 := bstep (se 4 (by rfl) ⟨1029681, by rfl⟩ : syracuseStep 10983269 = 2059363) B2059363
theorem B7322179 : Blo 2031435 7322179 := bstep (se 1 (by rfl) ⟨5491634, by rfl⟩ : syracuseStep 7322179 = 10983269) B10983269
theorem B9762905 : Blo 2031435 9762905 := bstep (se 2 (by rfl) ⟨3661089, by rfl⟩ : syracuseStep 9762905 = 7322179) B7322179
theorem B6508603 : Blo 2031435 6508603 := bstep (se 1 (by rfl) ⟨4881452, by rfl⟩ : syracuseStep 6508603 = 9762905) B9762905
theorem B8678137 : Blo 2031435 8678137 := bstep (se 2 (by rfl) ⟨3254301, by rfl⟩ : syracuseStep 8678137 = 6508603) B6508603
theorem B11570849 : Blo 2031435 11570849 := bstep (se 2 (by rfl) ⟨4339068, by rfl⟩ : syracuseStep 11570849 = 8678137) B8678137
theorem B7713899 : Blo 2031435 7713899 := bstep (se 1 (by rfl) ⟨5785424, by rfl⟩ : syracuseStep 7713899 = 11570849) B11570849
theorem B5142599 : Blo 2031435 5142599 := bstep (se 1 (by rfl) ⟨3856949, by rfl⟩ : syracuseStep 5142599 = 7713899) B7713899
theorem B3428399 : Blo 2031435 3428399 := bstep (se 1 (by rfl) ⟨2571299, by rfl⟩ : syracuseStep 3428399 = 5142599) B5142599
theorem B2285599 : Blo 2031435 2285599 := bstep (se 1 (by rfl) ⟨1714199, by rfl⟩ : syracuseStep 2285599 = 3428399) B3428399
theorem B3047465 : Blo 2031435 3047465 := bstep (se 2 (by rfl) ⟨1142799, by rfl⟩ : syracuseStep 3047465 = 2285599) B2285599
theorem B2031643 : Blo 2031435 2031643 := bstep (se 1 (by rfl) ⟨1523732, by rfl⟩ : syracuseStep 2031643 = 3047465) B3047465
theorem B17593109 : Blo 2031435 17593109 := bbase (se 6 (by rfl) ⟨412338, by rfl⟩ : syracuseStep 17593109 = 824677) (by norm_num)
theorem B11728739 : Blo 2031435 11728739 := bstep (se 1 (by rfl) ⟨8796554, by rfl⟩ : syracuseStep 11728739 = 17593109) B17593109
theorem B31276637 : Blo 2031435 31276637 := bstep (se 3 (by rfl) ⟨5864369, by rfl⟩ : syracuseStep 31276637 = 11728739) B11728739
theorem B20851091 : Blo 2031435 20851091 := bstep (se 1 (by rfl) ⟨15638318, by rfl⟩ : syracuseStep 20851091 = 31276637) B31276637
theorem B13900727 : Blo 2031435 13900727 := bstep (se 1 (by rfl) ⟨10425545, by rfl⟩ : syracuseStep 13900727 = 20851091) B20851091
theorem B9267151 : Blo 2031435 9267151 := bstep (se 1 (by rfl) ⟨6950363, by rfl⟩ : syracuseStep 9267151 = 13900727) B13900727
theorem B12356201 : Blo 2031435 12356201 := bstep (se 2 (by rfl) ⟨4633575, by rfl⟩ : syracuseStep 12356201 = 9267151) B9267151
theorem B8237467 : Blo 2031435 8237467 := bstep (se 1 (by rfl) ⟨6178100, by rfl⟩ : syracuseStep 8237467 = 12356201) B12356201
theorem B10983289 : Blo 2031435 10983289 := bstep (se 2 (by rfl) ⟨4118733, by rfl⟩ : syracuseStep 10983289 = 8237467) B8237467
theorem B14644385 : Blo 2031435 14644385 := bstep (se 2 (by rfl) ⟨5491644, by rfl⟩ : syracuseStep 14644385 = 10983289) B10983289
theorem B9762923 : Blo 2031435 9762923 := bstep (se 1 (by rfl) ⟨7322192, by rfl⟩ : syracuseStep 9762923 = 14644385) B14644385
theorem B6508615 : Blo 2031435 6508615 := bstep (se 1 (by rfl) ⟨4881461, by rfl⟩ : syracuseStep 6508615 = 9762923) B9762923
theorem B8678153 : Blo 2031435 8678153 := bstep (se 2 (by rfl) ⟨3254307, by rfl⟩ : syracuseStep 8678153 = 6508615) B6508615
theorem B5785435 : Blo 2031435 5785435 := bstep (se 1 (by rfl) ⟨4339076, by rfl⟩ : syracuseStep 5785435 = 8678153) B8678153
theorem B7713913 : Blo 2031435 7713913 := bstep (se 2 (by rfl) ⟨2892717, by rfl⟩ : syracuseStep 7713913 = 5785435) B5785435
theorem B10285217 : Blo 2031435 10285217 := bstep (se 2 (by rfl) ⟨3856956, by rfl⟩ : syracuseStep 10285217 = 7713913) B7713913
theorem B6856811 : Blo 2031435 6856811 := bstep (se 1 (by rfl) ⟨5142608, by rfl⟩ : syracuseStep 6856811 = 10285217) B10285217
theorem B4571207 : Blo 2031435 4571207 := bstep (se 1 (by rfl) ⟨3428405, by rfl⟩ : syracuseStep 4571207 = 6856811) B6856811
theorem B3047471 : Blo 2031435 3047471 := bstep (se 1 (by rfl) ⟨2285603, by rfl⟩ : syracuseStep 3047471 = 4571207) B4571207
theorem B2031647 : Blo 2031435 2031647 := bstep (se 1 (by rfl) ⟨1523735, by rfl⟩ : syracuseStep 2031647 = 3047471) B3047471
theorem B3047477 : Blo 2031435 3047477 := bbase (se 5 (by rfl) ⟨142850, by rfl⟩ : syracuseStep 3047477 = 285701) (by norm_num)
theorem B2031651 : Blo 2031435 2031651 := bstep (se 1 (by rfl) ⟨1523738, by rfl⟩ : syracuseStep 2031651 = 3047477) B3047477
theorem B5142629 : Blo 2031435 5142629 := bbase (se 4 (by rfl) ⟨482121, by rfl⟩ : syracuseStep 5142629 = 964243) (by norm_num)
theorem B3428419 : Blo 2031435 3428419 := bstep (se 1 (by rfl) ⟨2571314, by rfl⟩ : syracuseStep 3428419 = 5142629) B5142629
theorem B4571225 : Blo 2031435 4571225 := bstep (se 2 (by rfl) ⟨1714209, by rfl⟩ : syracuseStep 4571225 = 3428419) B3428419
theorem B3047483 : Blo 2031435 3047483 := bstep (se 1 (by rfl) ⟨2285612, by rfl⟩ : syracuseStep 3047483 = 4571225) B4571225
theorem B2031655 : Blo 2031435 2031655 := bstep (se 1 (by rfl) ⟨1523741, by rfl⟩ : syracuseStep 2031655 = 3047483) B3047483
theorem B2285617 : Blo 2031435 2285617 := bbase (se 2 (by rfl) ⟨857106, by rfl⟩ : syracuseStep 2285617 = 1714213) (by norm_num)
theorem B3047489 : Blo 2031435 3047489 := bstep (se 2 (by rfl) ⟨1142808, by rfl⟩ : syracuseStep 3047489 = 2285617) B2285617
theorem B2031659 : Blo 2031435 2031659 := bstep (se 1 (by rfl) ⟨1523744, by rfl⟩ : syracuseStep 2031659 = 3047489) B3047489
theorem B4633613 : Blo 2031435 4633613 := bbase (se 3 (by rfl) ⟨868802, by rfl⟩ : syracuseStep 4633613 = 1737605) (by norm_num)
theorem B3089075 : Blo 2031435 3089075 := bstep (se 1 (by rfl) ⟨2316806, by rfl⟩ : syracuseStep 3089075 = 4633613) B4633613
theorem B8237533 : Blo 2031435 8237533 := bstep (se 3 (by rfl) ⟨1544537, by rfl⟩ : syracuseStep 8237533 = 3089075) B3089075
theorem B10983377 : Blo 2031435 10983377 := bstep (se 2 (by rfl) ⟨4118766, by rfl⟩ : syracuseStep 10983377 = 8237533) B8237533
theorem B7322251 : Blo 2031435 7322251 := bstep (se 1 (by rfl) ⟨5491688, by rfl⟩ : syracuseStep 7322251 = 10983377) B10983377
theorem B9763001 : Blo 2031435 9763001 := bstep (se 2 (by rfl) ⟨3661125, by rfl⟩ : syracuseStep 9763001 = 7322251) B7322251
theorem B6508667 : Blo 2031435 6508667 := bstep (se 1 (by rfl) ⟨4881500, by rfl⟩ : syracuseStep 6508667 = 9763001) B9763001
theorem B4339111 : Blo 2031435 4339111 := bstep (se 1 (by rfl) ⟨3254333, by rfl⟩ : syracuseStep 4339111 = 6508667) B6508667
theorem B5785481 : Blo 2031435 5785481 := bstep (se 2 (by rfl) ⟨2169555, by rfl⟩ : syracuseStep 5785481 = 4339111) B4339111
theorem B3856987 : Blo 2031435 3856987 := bstep (se 1 (by rfl) ⟨2892740, by rfl⟩ : syracuseStep 3856987 = 5785481) B5785481
theorem B5142649 : Blo 2031435 5142649 := bstep (se 2 (by rfl) ⟨1928493, by rfl⟩ : syracuseStep 5142649 = 3856987) B3856987
theorem B6856865 : Blo 2031435 6856865 := bstep (se 2 (by rfl) ⟨2571324, by rfl⟩ : syracuseStep 6856865 = 5142649) B5142649
theorem B4571243 : Blo 2031435 4571243 := bstep (se 1 (by rfl) ⟨3428432, by rfl⟩ : syracuseStep 4571243 = 6856865) B6856865
theorem B3047495 : Blo 2031435 3047495 := bstep (se 1 (by rfl) ⟨2285621, by rfl⟩ : syracuseStep 3047495 = 4571243) B4571243
theorem B2031663 : Blo 2031435 2031663 := bstep (se 1 (by rfl) ⟨1523747, by rfl⟩ : syracuseStep 2031663 = 3047495) B3047495
theorem B3047501 : Blo 2031435 3047501 := bbase (se 3 (by rfl) ⟨571406, by rfl⟩ : syracuseStep 3047501 = 1142813) (by norm_num)
theorem B2031667 : Blo 2031435 2031667 := bstep (se 1 (by rfl) ⟨1523750, by rfl⟩ : syracuseStep 2031667 = 3047501) B3047501
theorem B4571261 : Blo 2031435 4571261 := bbase (se 3 (by rfl) ⟨857111, by rfl⟩ : syracuseStep 4571261 = 1714223) (by norm_num)
theorem B3047507 : Blo 2031435 3047507 := bstep (se 1 (by rfl) ⟨2285630, by rfl⟩ : syracuseStep 3047507 = 4571261) B4571261
theorem B2031671 : Blo 2031435 2031671 := bstep (se 1 (by rfl) ⟨1523753, by rfl⟩ : syracuseStep 2031671 = 3047507) B3047507
theorem B3428453 : Blo 2031435 3428453 := bbase (se 4 (by rfl) ⟨321417, by rfl⟩ : syracuseStep 3428453 = 642835) (by norm_num)
theorem B2285635 : Blo 2031435 2285635 := bstep (se 1 (by rfl) ⟨1714226, by rfl⟩ : syracuseStep 2285635 = 3428453) B3428453
theorem B3047513 : Blo 2031435 3047513 := bstep (se 2 (by rfl) ⟨1142817, by rfl⟩ : syracuseStep 3047513 = 2285635) B2285635
theorem B2031675 : Blo 2031435 2031675 := bstep (se 1 (by rfl) ⟨1523756, by rfl⟩ : syracuseStep 2031675 = 3047513) B3047513
theorem B7322309 : Blo 2031435 7322309 := bbase (se 4 (by rfl) ⟨686466, by rfl⟩ : syracuseStep 7322309 = 1372933) (by norm_num)
theorem B4881539 : Blo 2031435 4881539 := bstep (se 1 (by rfl) ⟨3661154, by rfl⟩ : syracuseStep 4881539 = 7322309) B7322309
theorem B3254359 : Blo 2031435 3254359 := bstep (se 1 (by rfl) ⟨2440769, by rfl⟩ : syracuseStep 3254359 = 4881539) B4881539
theorem B4339145 : Blo 2031435 4339145 := bstep (se 2 (by rfl) ⟨1627179, by rfl⟩ : syracuseStep 4339145 = 3254359) B3254359
theorem B2892763 : Blo 2031435 2892763 := bstep (se 1 (by rfl) ⟨2169572, by rfl⟩ : syracuseStep 2892763 = 4339145) B4339145
theorem B15428069 : Blo 2031435 15428069 := bstep (se 4 (by rfl) ⟨1446381, by rfl⟩ : syracuseStep 15428069 = 2892763) B2892763
theorem B10285379 : Blo 2031435 10285379 := bstep (se 1 (by rfl) ⟨7714034, by rfl⟩ : syracuseStep 10285379 = 15428069) B15428069
theorem B6856919 : Blo 2031435 6856919 := bstep (se 1 (by rfl) ⟨5142689, by rfl⟩ : syracuseStep 6856919 = 10285379) B10285379
theorem B4571279 : Blo 2031435 4571279 := bstep (se 1 (by rfl) ⟨3428459, by rfl⟩ : syracuseStep 4571279 = 6856919) B6856919
theorem B3047519 : Blo 2031435 3047519 := bstep (se 1 (by rfl) ⟨2285639, by rfl⟩ : syracuseStep 3047519 = 4571279) B4571279
theorem B2031679 : Blo 2031435 2031679 := bstep (se 1 (by rfl) ⟨1523759, by rfl⟩ : syracuseStep 2031679 = 3047519) B3047519
theorem B3047525 : Blo 2031435 3047525 := bbase (se 4 (by rfl) ⟨285705, by rfl⟩ : syracuseStep 3047525 = 571411) (by norm_num)
theorem B2031683 : Blo 2031435 2031683 := bstep (se 1 (by rfl) ⟨1523762, by rfl⟩ : syracuseStep 2031683 = 3047525) B3047525
theorem B10983509 : Blo 2031435 10983509 := bbase (se 8 (by rfl) ⟨64356, by rfl⟩ : syracuseStep 10983509 = 128713) (by norm_num)
theorem B7322339 : Blo 2031435 7322339 := bstep (se 1 (by rfl) ⟨5491754, by rfl⟩ : syracuseStep 7322339 = 10983509) B10983509
theorem B4881559 : Blo 2031435 4881559 := bstep (se 1 (by rfl) ⟨3661169, by rfl⟩ : syracuseStep 4881559 = 7322339) B7322339
theorem B6508745 : Blo 2031435 6508745 := bstep (se 2 (by rfl) ⟨2440779, by rfl⟩ : syracuseStep 6508745 = 4881559) B4881559
theorem B4339163 : Blo 2031435 4339163 := bstep (se 1 (by rfl) ⟨3254372, by rfl⟩ : syracuseStep 4339163 = 6508745) B6508745
theorem B2892775 : Blo 2031435 2892775 := bstep (se 1 (by rfl) ⟨2169581, by rfl⟩ : syracuseStep 2892775 = 4339163) B4339163
theorem B3857033 : Blo 2031435 3857033 := bstep (se 2 (by rfl) ⟨1446387, by rfl⟩ : syracuseStep 3857033 = 2892775) B2892775
theorem B2571355 : Blo 2031435 2571355 := bstep (se 1 (by rfl) ⟨1928516, by rfl⟩ : syracuseStep 2571355 = 3857033) B3857033
theorem B3428473 : Blo 2031435 3428473 := bstep (se 2 (by rfl) ⟨1285677, by rfl⟩ : syracuseStep 3428473 = 2571355) B2571355
theorem B4571297 : Blo 2031435 4571297 := bstep (se 2 (by rfl) ⟨1714236, by rfl⟩ : syracuseStep 4571297 = 3428473) B3428473
theorem B3047531 : Blo 2031435 3047531 := bstep (se 1 (by rfl) ⟨2285648, by rfl⟩ : syracuseStep 3047531 = 4571297) B4571297
theorem B2031687 : Blo 2031435 2031687 := bstep (se 1 (by rfl) ⟨1523765, by rfl⟩ : syracuseStep 2031687 = 3047531) B3047531
theorem B2285653 : Blo 2031435 2285653 := bbase (se 8 (by rfl) ⟨13392, by rfl⟩ : syracuseStep 2285653 = 26785) (by norm_num)
theorem B3047537 : Blo 2031435 3047537 := bstep (se 2 (by rfl) ⟨1142826, by rfl⟩ : syracuseStep 3047537 = 2285653) B2285653
theorem B2031691 : Blo 2031435 2031691 := bstep (se 1 (by rfl) ⟨1523768, by rfl⟩ : syracuseStep 2031691 = 3047537) B3047537
theorem B2571365 : Blo 2031435 2571365 := bbase (se 4 (by rfl) ⟨241065, by rfl⟩ : syracuseStep 2571365 = 482131) (by norm_num)
theorem B6856973 : Blo 2031435 6856973 := bstep (se 3 (by rfl) ⟨1285682, by rfl⟩ : syracuseStep 6856973 = 2571365) B2571365
theorem B4571315 : Blo 2031435 4571315 := bstep (se 1 (by rfl) ⟨3428486, by rfl⟩ : syracuseStep 4571315 = 6856973) B6856973
theorem B3047543 : Blo 2031435 3047543 := bstep (se 1 (by rfl) ⟨2285657, by rfl⟩ : syracuseStep 3047543 = 4571315) B4571315
theorem B2031695 : Blo 2031435 2031695 := bstep (se 1 (by rfl) ⟨1523771, by rfl⟩ : syracuseStep 2031695 = 3047543) B3047543
theorem B3047549 : Blo 2031435 3047549 := bbase (se 3 (by rfl) ⟨571415, by rfl⟩ : syracuseStep 3047549 = 1142831) (by norm_num)
theorem B2031699 : Blo 2031435 2031699 := bstep (se 1 (by rfl) ⟨1523774, by rfl⟩ : syracuseStep 2031699 = 3047549) B3047549
theorem B4571333 : Blo 2031435 4571333 := bbase (se 4 (by rfl) ⟨428562, by rfl⟩ : syracuseStep 4571333 = 857125) (by norm_num)
theorem B3047555 : Blo 2031435 3047555 := bstep (se 1 (by rfl) ⟨2285666, by rfl⟩ : syracuseStep 3047555 = 4571333) B4571333
theorem B2031703 : Blo 2031435 2031703 := bstep (se 1 (by rfl) ⟨1523777, by rfl⟩ : syracuseStep 2031703 = 3047555) B3047555
theorem B3661205 : Blo 2031435 3661205 := bbase (se 6 (by rfl) ⟨85809, by rfl⟩ : syracuseStep 3661205 = 171619) (by norm_num)
theorem B9763213 : Blo 2031435 9763213 := bstep (se 3 (by rfl) ⟨1830602, by rfl⟩ : syracuseStep 9763213 = 3661205) B3661205
theorem B13017617 : Blo 2031435 13017617 := bstep (se 2 (by rfl) ⟨4881606, by rfl⟩ : syracuseStep 13017617 = 9763213) B9763213
theorem B8678411 : Blo 2031435 8678411 := bstep (se 1 (by rfl) ⟨6508808, by rfl⟩ : syracuseStep 8678411 = 13017617) B13017617
theorem B5785607 : Blo 2031435 5785607 := bstep (se 1 (by rfl) ⟨4339205, by rfl⟩ : syracuseStep 5785607 = 8678411) B8678411
theorem B3857071 : Blo 2031435 3857071 := bstep (se 1 (by rfl) ⟨2892803, by rfl⟩ : syracuseStep 3857071 = 5785607) B5785607
theorem B5142761 : Blo 2031435 5142761 := bstep (se 2 (by rfl) ⟨1928535, by rfl⟩ : syracuseStep 5142761 = 3857071) B3857071
theorem B3428507 : Blo 2031435 3428507 := bstep (se 1 (by rfl) ⟨2571380, by rfl⟩ : syracuseStep 3428507 = 5142761) B5142761
theorem B2285671 : Blo 2031435 2285671 := bstep (se 1 (by rfl) ⟨1714253, by rfl⟩ : syracuseStep 2285671 = 3428507) B3428507
theorem B3047561 : Blo 2031435 3047561 := bstep (se 2 (by rfl) ⟨1142835, by rfl⟩ : syracuseStep 3047561 = 2285671) B2285671
theorem B2031707 : Blo 2031435 2031707 := bstep (se 1 (by rfl) ⟨1523780, by rfl⟩ : syracuseStep 2031707 = 3047561) B3047561
theorem B10285541 : Blo 2031435 10285541 := bbase (se 4 (by rfl) ⟨964269, by rfl⟩ : syracuseStep 10285541 = 1928539) (by norm_num)
theorem B6857027 : Blo 2031435 6857027 := bstep (se 1 (by rfl) ⟨5142770, by rfl⟩ : syracuseStep 6857027 = 10285541) B10285541
theorem B4571351 : Blo 2031435 4571351 := bstep (se 1 (by rfl) ⟨3428513, by rfl⟩ : syracuseStep 4571351 = 6857027) B6857027
theorem B3047567 : Blo 2031435 3047567 := bstep (se 1 (by rfl) ⟨2285675, by rfl⟩ : syracuseStep 3047567 = 4571351) B4571351
theorem B2031711 : Blo 2031435 2031711 := bstep (se 1 (by rfl) ⟨1523783, by rfl⟩ : syracuseStep 2031711 = 3047567) B3047567
theorem B3047573 : Blo 2031435 3047573 := bbase (se 6 (by rfl) ⟨71427, by rfl⟩ : syracuseStep 3047573 = 142855) (by norm_num)
theorem B2031715 : Blo 2031435 2031715 := bstep (se 1 (by rfl) ⟨1523786, by rfl⟩ : syracuseStep 2031715 = 3047573) B3047573
theorem B7322453 : Blo 2031435 7322453 := bbase (se 9 (by rfl) ⟨21452, by rfl⟩ : syracuseStep 7322453 = 42905) (by norm_num)
theorem B4881635 : Blo 2031435 4881635 := bstep (se 1 (by rfl) ⟨3661226, by rfl⟩ : syracuseStep 4881635 = 7322453) B7322453
theorem B3254423 : Blo 2031435 3254423 := bstep (se 1 (by rfl) ⟨2440817, by rfl⟩ : syracuseStep 3254423 = 4881635) B4881635
theorem B8678461 : Blo 2031435 8678461 := bstep (se 3 (by rfl) ⟨1627211, by rfl⟩ : syracuseStep 8678461 = 3254423) B3254423
theorem B11571281 : Blo 2031435 11571281 := bstep (se 2 (by rfl) ⟨4339230, by rfl⟩ : syracuseStep 11571281 = 8678461) B8678461
theorem B7714187 : Blo 2031435 7714187 := bstep (se 1 (by rfl) ⟨5785640, by rfl⟩ : syracuseStep 7714187 = 11571281) B11571281
theorem B5142791 : Blo 2031435 5142791 := bstep (se 1 (by rfl) ⟨3857093, by rfl⟩ : syracuseStep 5142791 = 7714187) B7714187
theorem B3428527 : Blo 2031435 3428527 := bstep (se 1 (by rfl) ⟨2571395, by rfl⟩ : syracuseStep 3428527 = 5142791) B5142791
theorem B4571369 : Blo 2031435 4571369 := bstep (se 2 (by rfl) ⟨1714263, by rfl⟩ : syracuseStep 4571369 = 3428527) B3428527
theorem B3047579 : Blo 2031435 3047579 := bstep (se 1 (by rfl) ⟨2285684, by rfl⟩ : syracuseStep 3047579 = 4571369) B4571369
theorem B2031719 : Blo 2031435 2031719 := bstep (se 1 (by rfl) ⟨1523789, by rfl⟩ : syracuseStep 2031719 = 3047579) B3047579
theorem B2285689 : Blo 2031435 2285689 := bbase (se 2 (by rfl) ⟨857133, by rfl⟩ : syracuseStep 2285689 = 1714267) (by norm_num)
theorem B3047585 : Blo 2031435 3047585 := bstep (se 2 (by rfl) ⟨1142844, by rfl⟩ : syracuseStep 3047585 = 2285689) B2285689
theorem B2031723 : Blo 2031435 2031723 := bstep (se 1 (by rfl) ⟨1523792, by rfl⟩ : syracuseStep 2031723 = 3047585) B3047585
theorem B15638933 : Blo 2031435 15638933 := bbase (se 6 (by rfl) ⟨366537, by rfl⟩ : syracuseStep 15638933 = 733075) (by norm_num)
theorem B41703821 : Blo 2031435 41703821 := bstep (se 3 (by rfl) ⟨7819466, by rfl⟩ : syracuseStep 41703821 = 15638933) B15638933
theorem B27802547 : Blo 2031435 27802547 := bstep (se 1 (by rfl) ⟨20851910, by rfl⟩ : syracuseStep 27802547 = 41703821) B41703821
theorem B18535031 : Blo 2031435 18535031 := bstep (se 1 (by rfl) ⟨13901273, by rfl⟩ : syracuseStep 18535031 = 27802547) B27802547
theorem B12356687 : Blo 2031435 12356687 := bstep (se 1 (by rfl) ⟨9267515, by rfl⟩ : syracuseStep 12356687 = 18535031) B18535031
theorem B8237791 : Blo 2031435 8237791 := bstep (se 1 (by rfl) ⟨6178343, by rfl⟩ : syracuseStep 8237791 = 12356687) B12356687
theorem B43934885 : Blo 2031435 43934885 := bstep (se 4 (by rfl) ⟨4118895, by rfl⟩ : syracuseStep 43934885 = 8237791) B8237791
theorem B29289923 : Blo 2031435 29289923 := bstep (se 1 (by rfl) ⟨21967442, by rfl⟩ : syracuseStep 29289923 = 43934885) B43934885
theorem B19526615 : Blo 2031435 19526615 := bstep (se 1 (by rfl) ⟨14644961, by rfl⟩ : syracuseStep 19526615 = 29289923) B29289923
theorem B13017743 : Blo 2031435 13017743 := bstep (se 1 (by rfl) ⟨9763307, by rfl⟩ : syracuseStep 13017743 = 19526615) B19526615
theorem B8678495 : Blo 2031435 8678495 := bstep (se 1 (by rfl) ⟨6508871, by rfl⟩ : syracuseStep 8678495 = 13017743) B13017743
theorem B5785663 : Blo 2031435 5785663 := bstep (se 1 (by rfl) ⟨4339247, by rfl⟩ : syracuseStep 5785663 = 8678495) B8678495
theorem B7714217 : Blo 2031435 7714217 := bstep (se 2 (by rfl) ⟨2892831, by rfl⟩ : syracuseStep 7714217 = 5785663) B5785663
theorem B5142811 : Blo 2031435 5142811 := bstep (se 1 (by rfl) ⟨3857108, by rfl⟩ : syracuseStep 5142811 = 7714217) B7714217
theorem B6857081 : Blo 2031435 6857081 := bstep (se 2 (by rfl) ⟨2571405, by rfl⟩ : syracuseStep 6857081 = 5142811) B5142811
theorem B4571387 : Blo 2031435 4571387 := bstep (se 1 (by rfl) ⟨3428540, by rfl⟩ : syracuseStep 4571387 = 6857081) B6857081
theorem B3047591 : Blo 2031435 3047591 := bstep (se 1 (by rfl) ⟨2285693, by rfl⟩ : syracuseStep 3047591 = 4571387) B4571387
theorem B2031727 : Blo 2031435 2031727 := bstep (se 1 (by rfl) ⟨1523795, by rfl⟩ : syracuseStep 2031727 = 3047591) B3047591
theorem B3047597 : Blo 2031435 3047597 := bbase (se 3 (by rfl) ⟨571424, by rfl⟩ : syracuseStep 3047597 = 1142849) (by norm_num)
theorem B2031731 : Blo 2031435 2031731 := bstep (se 1 (by rfl) ⟨1523798, by rfl⟩ : syracuseStep 2031731 = 3047597) B3047597
theorem B4571405 : Blo 2031435 4571405 := bbase (se 3 (by rfl) ⟨857138, by rfl⟩ : syracuseStep 4571405 = 1714277) (by norm_num)
theorem B3047603 : Blo 2031435 3047603 := bstep (se 1 (by rfl) ⟨2285702, by rfl⟩ : syracuseStep 3047603 = 4571405) B4571405
theorem B2031735 : Blo 2031435 2031735 := bstep (se 1 (by rfl) ⟨1523801, by rfl⟩ : syracuseStep 2031735 = 3047603) B3047603
theorem B2571421 : Blo 2031435 2571421 := bbase (se 3 (by rfl) ⟨482141, by rfl⟩ : syracuseStep 2571421 = 964283) (by norm_num)
theorem B3428561 : Blo 2031435 3428561 := bstep (se 2 (by rfl) ⟨1285710, by rfl⟩ : syracuseStep 3428561 = 2571421) B2571421
theorem B2285707 : Blo 2031435 2285707 := bstep (se 1 (by rfl) ⟨1714280, by rfl⟩ : syracuseStep 2285707 = 3428561) B3428561
theorem B3047609 : Blo 2031435 3047609 := bstep (se 2 (by rfl) ⟨1142853, by rfl⟩ : syracuseStep 3047609 = 2285707) B2285707
theorem B2031739 : Blo 2031435 2031739 := bstep (se 1 (by rfl) ⟨1523804, by rfl⟩ : syracuseStep 2031739 = 3047609) B3047609
theorem B3254461 : Blo 2031435 3254461 := bbase (se 3 (by rfl) ⟨610211, by rfl⟩ : syracuseStep 3254461 = 1220423) (by norm_num)
theorem B17357125 : Blo 2031435 17357125 := bstep (se 4 (by rfl) ⟨1627230, by rfl⟩ : syracuseStep 17357125 = 3254461) B3254461
theorem B23142833 : Blo 2031435 23142833 := bstep (se 2 (by rfl) ⟨8678562, by rfl⟩ : syracuseStep 23142833 = 17357125) B17357125
theorem B15428555 : Blo 2031435 15428555 := bstep (se 1 (by rfl) ⟨11571416, by rfl⟩ : syracuseStep 15428555 = 23142833) B23142833
theorem B10285703 : Blo 2031435 10285703 := bstep (se 1 (by rfl) ⟨7714277, by rfl⟩ : syracuseStep 10285703 = 15428555) B15428555
theorem B6857135 : Blo 2031435 6857135 := bstep (se 1 (by rfl) ⟨5142851, by rfl⟩ : syracuseStep 6857135 = 10285703) B10285703
theorem B4571423 : Blo 2031435 4571423 := bstep (se 1 (by rfl) ⟨3428567, by rfl⟩ : syracuseStep 4571423 = 6857135) B6857135
theorem B3047615 : Blo 2031435 3047615 := bstep (se 1 (by rfl) ⟨2285711, by rfl⟩ : syracuseStep 3047615 = 4571423) B4571423
theorem B2031743 : Blo 2031435 2031743 := bstep (se 1 (by rfl) ⟨1523807, by rfl⟩ : syracuseStep 2031743 = 3047615) B3047615
theorem B3047621 : Blo 2031435 3047621 := bbase (se 4 (by rfl) ⟨285714, by rfl⟩ : syracuseStep 3047621 = 571429) (by norm_num)
theorem B2031747 : Blo 2031435 2031747 := bstep (se 1 (by rfl) ⟨1523810, by rfl⟩ : syracuseStep 2031747 = 3047621) B3047621
theorem B3428581 : Blo 2031435 3428581 := bbase (se 4 (by rfl) ⟨321429, by rfl⟩ : syracuseStep 3428581 = 642859) (by norm_num)
theorem B4571441 : Blo 2031435 4571441 := bstep (se 2 (by rfl) ⟨1714290, by rfl⟩ : syracuseStep 4571441 = 3428581) B3428581
theorem B3047627 : Blo 2031435 3047627 := bstep (se 1 (by rfl) ⟨2285720, by rfl⟩ : syracuseStep 3047627 = 4571441) B4571441
theorem B2031751 : Blo 2031435 2031751 := bstep (se 1 (by rfl) ⟨1523813, by rfl⟩ : syracuseStep 2031751 = 3047627) B3047627
theorem B2285725 : Blo 2031435 2285725 := bbase (se 3 (by rfl) ⟨428573, by rfl⟩ : syracuseStep 2285725 = 857147) (by norm_num)
theorem B3047633 : Blo 2031435 3047633 := bstep (se 2 (by rfl) ⟨1142862, by rfl⟩ : syracuseStep 3047633 = 2285725) B2285725
theorem B2031755 : Blo 2031435 2031755 := bstep (se 1 (by rfl) ⟨1523816, by rfl⟩ : syracuseStep 2031755 = 3047633) B3047633
theorem B6857189 : Blo 2031435 6857189 := bbase (se 4 (by rfl) ⟨642861, by rfl⟩ : syracuseStep 6857189 = 1285723) (by norm_num)
theorem B4571459 : Blo 2031435 4571459 := bstep (se 1 (by rfl) ⟨3428594, by rfl⟩ : syracuseStep 4571459 = 6857189) B6857189
theorem B3047639 : Blo 2031435 3047639 := bstep (se 1 (by rfl) ⟨2285729, by rfl⟩ : syracuseStep 3047639 = 4571459) B4571459
theorem B2031759 : Blo 2031435 2031759 := bstep (se 1 (by rfl) ⟨1523819, by rfl⟩ : syracuseStep 2031759 = 3047639) B3047639
theorem B3047645 : Blo 2031435 3047645 := bbase (se 3 (by rfl) ⟨571433, by rfl⟩ : syracuseStep 3047645 = 1142867) (by norm_num)
theorem B2031763 : Blo 2031435 2031763 := bstep (se 1 (by rfl) ⟨1523822, by rfl⟩ : syracuseStep 2031763 = 3047645) B3047645
theorem B4571477 : Blo 2031435 4571477 := bbase (se 10 (by rfl) ⟨6696, by rfl⟩ : syracuseStep 4571477 = 13393) (by norm_num)
theorem B3047651 : Blo 2031435 3047651 := bstep (se 1 (by rfl) ⟨2285738, by rfl⟩ : syracuseStep 3047651 = 4571477) B4571477
theorem B2031767 : Blo 2031435 2031767 := bstep (se 1 (by rfl) ⟨1523825, by rfl⟩ : syracuseStep 2031767 = 3047651) B3047651
theorem B4633861 : Blo 2031435 4633861 := bbase (se 4 (by rfl) ⟨434424, by rfl⟩ : syracuseStep 4633861 = 868849) (by norm_num)
theorem B6178481 : Blo 2031435 6178481 := bstep (se 2 (by rfl) ⟨2316930, by rfl⟩ : syracuseStep 6178481 = 4633861) B4633861
theorem B4118987 : Blo 2031435 4118987 := bstep (se 1 (by rfl) ⟨3089240, by rfl⟩ : syracuseStep 4118987 = 6178481) B6178481
theorem B2745991 : Blo 2031435 2745991 := bstep (se 1 (by rfl) ⟨2059493, by rfl⟩ : syracuseStep 2745991 = 4118987) B4118987
theorem B3661321 : Blo 2031435 3661321 := bstep (se 2 (by rfl) ⟨1372995, by rfl⟩ : syracuseStep 3661321 = 2745991) B2745991
theorem B4881761 : Blo 2031435 4881761 := bstep (se 2 (by rfl) ⟨1830660, by rfl⟩ : syracuseStep 4881761 = 3661321) B3661321
theorem B3254507 : Blo 2031435 3254507 := bstep (se 1 (by rfl) ⟨2440880, by rfl⟩ : syracuseStep 3254507 = 4881761) B4881761
theorem B2169671 : Blo 2031435 2169671 := bstep (se 1 (by rfl) ⟨1627253, by rfl⟩ : syracuseStep 2169671 = 3254507) B3254507
theorem B5785789 : Blo 2031435 5785789 := bstep (se 3 (by rfl) ⟨1084835, by rfl⟩ : syracuseStep 5785789 = 2169671) B2169671
theorem B7714385 : Blo 2031435 7714385 := bstep (se 2 (by rfl) ⟨2892894, by rfl⟩ : syracuseStep 7714385 = 5785789) B5785789
theorem B5142923 : Blo 2031435 5142923 := bstep (se 1 (by rfl) ⟨3857192, by rfl⟩ : syracuseStep 5142923 = 7714385) B7714385
theorem B3428615 : Blo 2031435 3428615 := bstep (se 1 (by rfl) ⟨2571461, by rfl⟩ : syracuseStep 3428615 = 5142923) B5142923
theorem B2285743 : Blo 2031435 2285743 := bstep (se 1 (by rfl) ⟨1714307, by rfl⟩ : syracuseStep 2285743 = 3428615) B3428615
theorem B3047657 : Blo 2031435 3047657 := bstep (se 2 (by rfl) ⟨1142871, by rfl⟩ : syracuseStep 3047657 = 2285743) B2285743
theorem B2031771 : Blo 2031435 2031771 := bstep (se 1 (by rfl) ⟨1523828, by rfl⟩ : syracuseStep 2031771 = 3047657) B3047657
theorem B3089245 : Blo 2031435 3089245 := bbase (se 3 (by rfl) ⟨579233, by rfl⟩ : syracuseStep 3089245 = 1158467) (by norm_num)
theorem B4118993 : Blo 2031435 4118993 := bstep (se 2 (by rfl) ⟨1544622, by rfl⟩ : syracuseStep 4118993 = 3089245) B3089245
theorem B2745995 : Blo 2031435 2745995 := bstep (se 1 (by rfl) ⟨2059496, by rfl⟩ : syracuseStep 2745995 = 4118993) B4118993
theorem B7322653 : Blo 2031435 7322653 := bstep (se 3 (by rfl) ⟨1372997, by rfl⟩ : syracuseStep 7322653 = 2745995) B2745995
theorem B39054149 : Blo 2031435 39054149 := bstep (se 4 (by rfl) ⟨3661326, by rfl⟩ : syracuseStep 39054149 = 7322653) B7322653
theorem B26036099 : Blo 2031435 26036099 := bstep (se 1 (by rfl) ⟨19527074, by rfl⟩ : syracuseStep 26036099 = 39054149) B39054149
theorem B17357399 : Blo 2031435 17357399 := bstep (se 1 (by rfl) ⟨13018049, by rfl⟩ : syracuseStep 17357399 = 26036099) B26036099
theorem B11571599 : Blo 2031435 11571599 := bstep (se 1 (by rfl) ⟨8678699, by rfl⟩ : syracuseStep 11571599 = 17357399) B17357399
theorem B7714399 : Blo 2031435 7714399 := bstep (se 1 (by rfl) ⟨5785799, by rfl⟩ : syracuseStep 7714399 = 11571599) B11571599
theorem B10285865 : Blo 2031435 10285865 := bstep (se 2 (by rfl) ⟨3857199, by rfl⟩ : syracuseStep 10285865 = 7714399) B7714399
theorem B6857243 : Blo 2031435 6857243 := bstep (se 1 (by rfl) ⟨5142932, by rfl⟩ : syracuseStep 6857243 = 10285865) B10285865
theorem B4571495 : Blo 2031435 4571495 := bstep (se 1 (by rfl) ⟨3428621, by rfl⟩ : syracuseStep 4571495 = 6857243) B6857243
theorem B3047663 : Blo 2031435 3047663 := bstep (se 1 (by rfl) ⟨2285747, by rfl⟩ : syracuseStep 3047663 = 4571495) B4571495
theorem B2031775 : Blo 2031435 2031775 := bstep (se 1 (by rfl) ⟨1523831, by rfl⟩ : syracuseStep 2031775 = 3047663) B3047663
theorem B3047669 : Blo 2031435 3047669 := bbase (se 5 (by rfl) ⟨142859, by rfl⟩ : syracuseStep 3047669 = 285719) (by norm_num)
theorem B2031779 : Blo 2031435 2031779 := bstep (se 1 (by rfl) ⟨1523834, by rfl⟩ : syracuseStep 2031779 = 3047669) B3047669
theorem B7819685 : Blo 2031435 7819685 := bbase (se 4 (by rfl) ⟨733095, by rfl⟩ : syracuseStep 7819685 = 1466191) (by norm_num)
theorem B5213123 : Blo 2031435 5213123 := bstep (se 1 (by rfl) ⟨3909842, by rfl⟩ : syracuseStep 5213123 = 7819685) B7819685
theorem B3475415 : Blo 2031435 3475415 := bstep (se 1 (by rfl) ⟨2606561, by rfl⟩ : syracuseStep 3475415 = 5213123) B5213123
theorem B2316943 : Blo 2031435 2316943 := bstep (se 1 (by rfl) ⟨1737707, by rfl⟩ : syracuseStep 2316943 = 3475415) B3475415
theorem B12357029 : Blo 2031435 12357029 := bstep (se 4 (by rfl) ⟨1158471, by rfl⟩ : syracuseStep 12357029 = 2316943) B2316943
theorem B8238019 : Blo 2031435 8238019 := bstep (se 1 (by rfl) ⟨6178514, by rfl⟩ : syracuseStep 8238019 = 12357029) B12357029
theorem B10984025 : Blo 2031435 10984025 := bstep (se 2 (by rfl) ⟨4119009, by rfl⟩ : syracuseStep 10984025 = 8238019) B8238019
theorem B29290733 : Blo 2031435 29290733 := bstep (se 3 (by rfl) ⟨5492012, by rfl⟩ : syracuseStep 29290733 = 10984025) B10984025
theorem B19527155 : Blo 2031435 19527155 := bstep (se 1 (by rfl) ⟨14645366, by rfl⟩ : syracuseStep 19527155 = 29290733) B29290733
theorem B13018103 : Blo 2031435 13018103 := bstep (se 1 (by rfl) ⟨9763577, by rfl⟩ : syracuseStep 13018103 = 19527155) B19527155
theorem B8678735 : Blo 2031435 8678735 := bstep (se 1 (by rfl) ⟨6509051, by rfl⟩ : syracuseStep 8678735 = 13018103) B13018103
theorem B5785823 : Blo 2031435 5785823 := bstep (se 1 (by rfl) ⟨4339367, by rfl⟩ : syracuseStep 5785823 = 8678735) B8678735
theorem B3857215 : Blo 2031435 3857215 := bstep (se 1 (by rfl) ⟨2892911, by rfl⟩ : syracuseStep 3857215 = 5785823) B5785823
theorem B5142953 : Blo 2031435 5142953 := bstep (se 2 (by rfl) ⟨1928607, by rfl⟩ : syracuseStep 5142953 = 3857215) B3857215
theorem B3428635 : Blo 2031435 3428635 := bstep (se 1 (by rfl) ⟨2571476, by rfl⟩ : syracuseStep 3428635 = 5142953) B5142953
theorem B4571513 : Blo 2031435 4571513 := bstep (se 2 (by rfl) ⟨1714317, by rfl⟩ : syracuseStep 4571513 = 3428635) B3428635
theorem B3047675 : Blo 2031435 3047675 := bstep (se 1 (by rfl) ⟨2285756, by rfl⟩ : syracuseStep 3047675 = 4571513) B4571513
theorem B2031783 : Blo 2031435 2031783 := bstep (se 1 (by rfl) ⟨1523837, by rfl⟩ : syracuseStep 2031783 = 3047675) B3047675
theorem B2285761 : Blo 2031435 2285761 := bbase (se 2 (by rfl) ⟨857160, by rfl⟩ : syracuseStep 2285761 = 1714321) (by norm_num)
theorem B3047681 : Blo 2031435 3047681 := bstep (se 2 (by rfl) ⟨1142880, by rfl⟩ : syracuseStep 3047681 = 2285761) B2285761
theorem B2031787 : Blo 2031435 2031787 := bstep (se 1 (by rfl) ⟨1523840, by rfl⟩ : syracuseStep 2031787 = 3047681) B3047681
theorem B5142973 : Blo 2031435 5142973 := bbase (se 3 (by rfl) ⟨964307, by rfl⟩ : syracuseStep 5142973 = 1928615) (by norm_num)
theorem B6857297 : Blo 2031435 6857297 := bstep (se 2 (by rfl) ⟨2571486, by rfl⟩ : syracuseStep 6857297 = 5142973) B5142973
theorem B4571531 : Blo 2031435 4571531 := bstep (se 1 (by rfl) ⟨3428648, by rfl⟩ : syracuseStep 4571531 = 6857297) B6857297
theorem B3047687 : Blo 2031435 3047687 := bstep (se 1 (by rfl) ⟨2285765, by rfl⟩ : syracuseStep 3047687 = 4571531) B4571531
theorem B2031791 : Blo 2031435 2031791 := bstep (se 1 (by rfl) ⟨1523843, by rfl⟩ : syracuseStep 2031791 = 3047687) B3047687
theorem B3047693 : Blo 2031435 3047693 := bbase (se 3 (by rfl) ⟨571442, by rfl⟩ : syracuseStep 3047693 = 1142885) (by norm_num)
theorem B2031795 : Blo 2031435 2031795 := bstep (se 1 (by rfl) ⟨1523846, by rfl⟩ : syracuseStep 2031795 = 3047693) B3047693
theorem B4571549 : Blo 2031435 4571549 := bbase (se 3 (by rfl) ⟨857165, by rfl⟩ : syracuseStep 4571549 = 1714331) (by norm_num)
theorem B3047699 : Blo 2031435 3047699 := bstep (se 1 (by rfl) ⟨2285774, by rfl⟩ : syracuseStep 3047699 = 4571549) B4571549
theorem B2031799 : Blo 2031435 2031799 := bstep (se 1 (by rfl) ⟨1523849, by rfl⟩ : syracuseStep 2031799 = 3047699) B3047699
theorem B3428669 : Blo 2031435 3428669 := bbase (se 3 (by rfl) ⟨642875, by rfl⟩ : syracuseStep 3428669 = 1285751) (by norm_num)
theorem B2285779 : Blo 2031435 2285779 := bstep (se 1 (by rfl) ⟨1714334, by rfl⟩ : syracuseStep 2285779 = 3428669) B3428669
theorem B3047705 : Blo 2031435 3047705 := bstep (se 2 (by rfl) ⟨1142889, by rfl⟩ : syracuseStep 3047705 = 2285779) B2285779
theorem B2031803 : Blo 2031435 2031803 := bstep (se 1 (by rfl) ⟨1523852, by rfl⟩ : syracuseStep 2031803 = 3047705) B3047705
theorem B2169709 : Blo 2031435 2169709 := bbase (se 3 (by rfl) ⟨406820, by rfl⟩ : syracuseStep 2169709 = 813641) (by norm_num)
theorem B11571781 : Blo 2031435 11571781 := bstep (se 4 (by rfl) ⟨1084854, by rfl⟩ : syracuseStep 11571781 = 2169709) B2169709
theorem B15429041 : Blo 2031435 15429041 := bstep (se 2 (by rfl) ⟨5785890, by rfl⟩ : syracuseStep 15429041 = 11571781) B11571781
theorem B10286027 : Blo 2031435 10286027 := bstep (se 1 (by rfl) ⟨7714520, by rfl⟩ : syracuseStep 10286027 = 15429041) B15429041
theorem B6857351 : Blo 2031435 6857351 := bstep (se 1 (by rfl) ⟨5143013, by rfl⟩ : syracuseStep 6857351 = 10286027) B10286027
theorem B4571567 : Blo 2031435 4571567 := bstep (se 1 (by rfl) ⟨3428675, by rfl⟩ : syracuseStep 4571567 = 6857351) B6857351
theorem B3047711 : Blo 2031435 3047711 := bstep (se 1 (by rfl) ⟨2285783, by rfl⟩ : syracuseStep 3047711 = 4571567) B4571567
theorem B2031807 : Blo 2031435 2031807 := bstep (se 1 (by rfl) ⟨1523855, by rfl⟩ : syracuseStep 2031807 = 3047711) B3047711
theorem B3047717 : Blo 2031435 3047717 := bbase (se 4 (by rfl) ⟨285723, by rfl⟩ : syracuseStep 3047717 = 571447) (by norm_num)
theorem B2031811 : Blo 2031435 2031811 := bstep (se 1 (by rfl) ⟨1523858, by rfl⟩ : syracuseStep 2031811 = 3047717) B3047717
theorem B2571517 : Blo 2031435 2571517 := bbase (se 3 (by rfl) ⟨482159, by rfl⟩ : syracuseStep 2571517 = 964319) (by norm_num)
theorem B3428689 : Blo 2031435 3428689 := bstep (se 2 (by rfl) ⟨1285758, by rfl⟩ : syracuseStep 3428689 = 2571517) B2571517
theorem B4571585 : Blo 2031435 4571585 := bstep (se 2 (by rfl) ⟨1714344, by rfl⟩ : syracuseStep 4571585 = 3428689) B3428689
theorem B3047723 : Blo 2031435 3047723 := bstep (se 1 (by rfl) ⟨2285792, by rfl⟩ : syracuseStep 3047723 = 4571585) B4571585
theorem B2031815 : Blo 2031435 2031815 := bstep (se 1 (by rfl) ⟨1523861, by rfl⟩ : syracuseStep 2031815 = 3047723) B3047723
theorem B2285797 : Blo 2031435 2285797 := bbase (se 4 (by rfl) ⟨214293, by rfl⟩ : syracuseStep 2285797 = 428587) (by norm_num)
theorem B3047729 : Blo 2031435 3047729 := bstep (se 2 (by rfl) ⟨1142898, by rfl⟩ : syracuseStep 3047729 = 2285797) B2285797
theorem B2031819 : Blo 2031435 2031819 := bstep (se 1 (by rfl) ⟨1523864, by rfl⟩ : syracuseStep 2031819 = 3047729) B3047729
theorem B4339453 : Blo 2031435 4339453 := bbase (se 3 (by rfl) ⟨813647, by rfl⟩ : syracuseStep 4339453 = 1627295) (by norm_num)
theorem B5785937 : Blo 2031435 5785937 := bstep (se 2 (by rfl) ⟨2169726, by rfl⟩ : syracuseStep 5785937 = 4339453) B4339453
theorem B3857291 : Blo 2031435 3857291 := bstep (se 1 (by rfl) ⟨2892968, by rfl⟩ : syracuseStep 3857291 = 5785937) B5785937
theorem B2571527 : Blo 2031435 2571527 := bstep (se 1 (by rfl) ⟨1928645, by rfl⟩ : syracuseStep 2571527 = 3857291) B3857291
theorem B6857405 : Blo 2031435 6857405 := bstep (se 3 (by rfl) ⟨1285763, by rfl⟩ : syracuseStep 6857405 = 2571527) B2571527
theorem B4571603 : Blo 2031435 4571603 := bstep (se 1 (by rfl) ⟨3428702, by rfl⟩ : syracuseStep 4571603 = 6857405) B6857405
theorem B3047735 : Blo 2031435 3047735 := bstep (se 1 (by rfl) ⟨2285801, by rfl⟩ : syracuseStep 3047735 = 4571603) B4571603
theorem B2031823 : Blo 2031435 2031823 := bstep (se 1 (by rfl) ⟨1523867, by rfl⟩ : syracuseStep 2031823 = 3047735) B3047735
theorem B3047741 : Blo 2031435 3047741 := bbase (se 3 (by rfl) ⟨571451, by rfl⟩ : syracuseStep 3047741 = 1142903) (by norm_num)
theorem B2031827 : Blo 2031435 2031827 := bstep (se 1 (by rfl) ⟨1523870, by rfl⟩ : syracuseStep 2031827 = 3047741) B3047741
theorem B4571621 : Blo 2031435 4571621 := bbase (se 4 (by rfl) ⟨428589, by rfl⟩ : syracuseStep 4571621 = 857179) (by norm_num)
theorem B3047747 : Blo 2031435 3047747 := bstep (se 1 (by rfl) ⟨2285810, by rfl⟩ : syracuseStep 3047747 = 4571621) B4571621
theorem B2031831 : Blo 2031435 2031831 := bstep (se 1 (by rfl) ⟨1523873, by rfl⟩ : syracuseStep 2031831 = 3047747) B3047747
theorem B5143085 : Blo 2031435 5143085 := bbase (se 3 (by rfl) ⟨964328, by rfl⟩ : syracuseStep 5143085 = 1928657) (by norm_num)
theorem B3428723 : Blo 2031435 3428723 := bstep (se 1 (by rfl) ⟨2571542, by rfl⟩ : syracuseStep 3428723 = 5143085) B5143085
theorem B2285815 : Blo 2031435 2285815 := bstep (se 1 (by rfl) ⟨1714361, by rfl⟩ : syracuseStep 2285815 = 3428723) B3428723
theorem B3047753 : Blo 2031435 3047753 := bstep (se 2 (by rfl) ⟨1142907, by rfl⟩ : syracuseStep 3047753 = 2285815) B2285815
theorem B2031835 : Blo 2031435 2031835 := bstep (se 1 (by rfl) ⟨1523876, by rfl⟩ : syracuseStep 2031835 = 3047753) B3047753
theorem B7045861 : Blo 2031435 7045861 := bbase (se 4 (by rfl) ⟨660549, by rfl⟩ : syracuseStep 7045861 = 1321099) (by norm_num)
theorem B9394481 : Blo 2031435 9394481 := bstep (se 2 (by rfl) ⟨3522930, by rfl⟩ : syracuseStep 9394481 = 7045861) B7045861
theorem B25051949 : Blo 2031435 25051949 := bstep (se 3 (by rfl) ⟨4697240, by rfl⟩ : syracuseStep 25051949 = 9394481) B9394481
theorem B16701299 : Blo 2031435 16701299 := bstep (se 1 (by rfl) ⟨12525974, by rfl⟩ : syracuseStep 16701299 = 25051949) B25051949
theorem B11134199 : Blo 2031435 11134199 := bstep (se 1 (by rfl) ⟨8350649, by rfl⟩ : syracuseStep 11134199 = 16701299) B16701299
theorem B7422799 : Blo 2031435 7422799 := bstep (se 1 (by rfl) ⟨5567099, by rfl⟩ : syracuseStep 7422799 = 11134199) B11134199
theorem B9897065 : Blo 2031435 9897065 := bstep (se 2 (by rfl) ⟨3711399, by rfl⟩ : syracuseStep 9897065 = 7422799) B7422799
theorem B6598043 : Blo 2031435 6598043 := bstep (se 1 (by rfl) ⟨4948532, by rfl⟩ : syracuseStep 6598043 = 9897065) B9897065
theorem B4398695 : Blo 2031435 4398695 := bstep (se 1 (by rfl) ⟨3299021, by rfl⟩ : syracuseStep 4398695 = 6598043) B6598043
theorem B2932463 : Blo 2031435 2932463 := bstep (se 1 (by rfl) ⟨2199347, by rfl⟩ : syracuseStep 2932463 = 4398695) B4398695
theorem B7819901 : Blo 2031435 7819901 := bstep (se 3 (by rfl) ⟨1466231, by rfl⟩ : syracuseStep 7819901 = 2932463) B2932463
theorem B5213267 : Blo 2031435 5213267 := bstep (se 1 (by rfl) ⟨3909950, by rfl⟩ : syracuseStep 5213267 = 7819901) B7819901
theorem B3475511 : Blo 2031435 3475511 := bstep (se 1 (by rfl) ⟨2606633, by rfl⟩ : syracuseStep 3475511 = 5213267) B5213267
theorem B2317007 : Blo 2031435 2317007 := bstep (se 1 (by rfl) ⟨1737755, by rfl⟩ : syracuseStep 2317007 = 3475511) B3475511
theorem B6178685 : Blo 2031435 6178685 := bstep (se 3 (by rfl) ⟨1158503, by rfl⟩ : syracuseStep 6178685 = 2317007) B2317007
theorem B16476493 : Blo 2031435 16476493 := bstep (se 3 (by rfl) ⟨3089342, by rfl⟩ : syracuseStep 16476493 = 6178685) B6178685
theorem B21968657 : Blo 2031435 21968657 := bstep (se 2 (by rfl) ⟨8238246, by rfl⟩ : syracuseStep 21968657 = 16476493) B16476493
theorem B14645771 : Blo 2031435 14645771 := bstep (se 1 (by rfl) ⟨10984328, by rfl⟩ : syracuseStep 14645771 = 21968657) B21968657
theorem B9763847 : Blo 2031435 9763847 := bstep (se 1 (by rfl) ⟨7322885, by rfl⟩ : syracuseStep 9763847 = 14645771) B14645771
theorem B6509231 : Blo 2031435 6509231 := bstep (se 1 (by rfl) ⟨4881923, by rfl⟩ : syracuseStep 6509231 = 9763847) B9763847
theorem B4339487 : Blo 2031435 4339487 := bstep (se 1 (by rfl) ⟨3254615, by rfl⟩ : syracuseStep 4339487 = 6509231) B6509231
theorem B2892991 : Blo 2031435 2892991 := bstep (se 1 (by rfl) ⟨2169743, by rfl⟩ : syracuseStep 2892991 = 4339487) B4339487
theorem B3857321 : Blo 2031435 3857321 := bstep (se 2 (by rfl) ⟨1446495, by rfl⟩ : syracuseStep 3857321 = 2892991) B2892991
theorem B10286189 : Blo 2031435 10286189 := bstep (se 3 (by rfl) ⟨1928660, by rfl⟩ : syracuseStep 10286189 = 3857321) B3857321
theorem B6857459 : Blo 2031435 6857459 := bstep (se 1 (by rfl) ⟨5143094, by rfl⟩ : syracuseStep 6857459 = 10286189) B10286189
theorem B4571639 : Blo 2031435 4571639 := bstep (se 1 (by rfl) ⟨3428729, by rfl⟩ : syracuseStep 4571639 = 6857459) B6857459
theorem B3047759 : Blo 2031435 3047759 := bstep (se 1 (by rfl) ⟨2285819, by rfl⟩ : syracuseStep 3047759 = 4571639) B4571639
theorem B2031839 : Blo 2031435 2031839 := bstep (se 1 (by rfl) ⟨1523879, by rfl⟩ : syracuseStep 2031839 = 3047759) B3047759
theorem B3047765 : Blo 2031435 3047765 := bbase (se 10 (by rfl) ⟨4464, by rfl⟩ : syracuseStep 3047765 = 8929) (by norm_num)
theorem B2031843 : Blo 2031435 2031843 := bstep (se 1 (by rfl) ⟨1523882, by rfl⟩ : syracuseStep 2031843 = 3047765) B3047765
theorem B5786005 : Blo 2031435 5786005 := bbase (se 6 (by rfl) ⟨135609, by rfl⟩ : syracuseStep 5786005 = 271219) (by norm_num)
theorem B7714673 : Blo 2031435 7714673 := bstep (se 2 (by rfl) ⟨2893002, by rfl⟩ : syracuseStep 7714673 = 5786005) B5786005
theorem B5143115 : Blo 2031435 5143115 := bstep (se 1 (by rfl) ⟨3857336, by rfl⟩ : syracuseStep 5143115 = 7714673) B7714673
theorem B3428743 : Blo 2031435 3428743 := bstep (se 1 (by rfl) ⟨2571557, by rfl⟩ : syracuseStep 3428743 = 5143115) B5143115
theorem B4571657 : Blo 2031435 4571657 := bstep (se 2 (by rfl) ⟨1714371, by rfl⟩ : syracuseStep 4571657 = 3428743) B3428743
theorem B3047771 : Blo 2031435 3047771 := bstep (se 1 (by rfl) ⟨2285828, by rfl⟩ : syracuseStep 3047771 = 4571657) B4571657
theorem B2031847 : Blo 2031435 2031847 := bstep (se 1 (by rfl) ⟨1523885, by rfl⟩ : syracuseStep 2031847 = 3047771) B3047771
theorem B2285833 : Blo 2031435 2285833 := bbase (se 2 (by rfl) ⟨857187, by rfl⟩ : syracuseStep 2285833 = 1714375) (by norm_num)
theorem B3047777 : Blo 2031435 3047777 := bstep (se 2 (by rfl) ⟨1142916, by rfl⟩ : syracuseStep 3047777 = 2285833) B2285833
theorem B2031851 : Blo 2031435 2031851 := bstep (se 1 (by rfl) ⟨1523888, by rfl⟩ : syracuseStep 2031851 = 3047777) B3047777
theorem B9394549 : Blo 2031435 9394549 := bbase (se 5 (by rfl) ⟨440369, by rfl⟩ : syracuseStep 9394549 = 880739) (by norm_num)
theorem B50104261 : Blo 2031435 50104261 := bstep (se 4 (by rfl) ⟨4697274, by rfl⟩ : syracuseStep 50104261 = 9394549) B9394549
theorem B66805681 : Blo 2031435 66805681 := bstep (se 2 (by rfl) ⟨25052130, by rfl⟩ : syracuseStep 66805681 = 50104261) B50104261
theorem B89074241 : Blo 2031435 89074241 := bstep (se 2 (by rfl) ⟨33402840, by rfl⟩ : syracuseStep 89074241 = 66805681) B66805681
theorem B59382827 : Blo 2031435 59382827 := bstep (se 1 (by rfl) ⟨44537120, by rfl⟩ : syracuseStep 59382827 = 89074241) B89074241
theorem B39588551 : Blo 2031435 39588551 := bstep (se 1 (by rfl) ⟨29691413, by rfl⟩ : syracuseStep 39588551 = 59382827) B59382827
theorem B26392367 : Blo 2031435 26392367 := bstep (se 1 (by rfl) ⟨19794275, by rfl⟩ : syracuseStep 26392367 = 39588551) B39588551
theorem B17594911 : Blo 2031435 17594911 := bstep (se 1 (by rfl) ⟨13196183, by rfl⟩ : syracuseStep 17594911 = 26392367) B26392367
theorem B23459881 : Blo 2031435 23459881 := bstep (se 2 (by rfl) ⟨8797455, by rfl⟩ : syracuseStep 23459881 = 17594911) B17594911
theorem B31279841 : Blo 2031435 31279841 := bstep (se 2 (by rfl) ⟨11729940, by rfl⟩ : syracuseStep 31279841 = 23459881) B23459881
theorem B20853227 : Blo 2031435 20853227 := bstep (se 1 (by rfl) ⟨15639920, by rfl⟩ : syracuseStep 20853227 = 31279841) B31279841
theorem B13902151 : Blo 2031435 13902151 := bstep (se 1 (by rfl) ⟨10426613, by rfl⟩ : syracuseStep 13902151 = 20853227) B20853227
theorem B18536201 : Blo 2031435 18536201 := bstep (se 2 (by rfl) ⟨6951075, by rfl⟩ : syracuseStep 18536201 = 13902151) B13902151
theorem B12357467 : Blo 2031435 12357467 := bstep (se 1 (by rfl) ⟨9268100, by rfl⟩ : syracuseStep 12357467 = 18536201) B18536201
theorem B8238311 : Blo 2031435 8238311 := bstep (se 1 (by rfl) ⟨6178733, by rfl⟩ : syracuseStep 8238311 = 12357467) B12357467
theorem B5492207 : Blo 2031435 5492207 := bstep (se 1 (by rfl) ⟨4119155, by rfl⟩ : syracuseStep 5492207 = 8238311) B8238311
theorem B3661471 : Blo 2031435 3661471 := bstep (se 1 (by rfl) ⟨2746103, by rfl⟩ : syracuseStep 3661471 = 5492207) B5492207
theorem B4881961 : Blo 2031435 4881961 := bstep (se 2 (by rfl) ⟨1830735, by rfl⟩ : syracuseStep 4881961 = 3661471) B3661471
theorem B26037125 : Blo 2031435 26037125 := bstep (se 4 (by rfl) ⟨2440980, by rfl⟩ : syracuseStep 26037125 = 4881961) B4881961
theorem B17358083 : Blo 2031435 17358083 := bstep (se 1 (by rfl) ⟨13018562, by rfl⟩ : syracuseStep 17358083 = 26037125) B26037125
theorem B11572055 : Blo 2031435 11572055 := bstep (se 1 (by rfl) ⟨8679041, by rfl⟩ : syracuseStep 11572055 = 17358083) B17358083
theorem B7714703 : Blo 2031435 7714703 := bstep (se 1 (by rfl) ⟨5786027, by rfl⟩ : syracuseStep 7714703 = 11572055) B11572055
theorem B5143135 : Blo 2031435 5143135 := bstep (se 1 (by rfl) ⟨3857351, by rfl⟩ : syracuseStep 5143135 = 7714703) B7714703
theorem B6857513 : Blo 2031435 6857513 := bstep (se 2 (by rfl) ⟨2571567, by rfl⟩ : syracuseStep 6857513 = 5143135) B5143135
theorem B4571675 : Blo 2031435 4571675 := bstep (se 1 (by rfl) ⟨3428756, by rfl⟩ : syracuseStep 4571675 = 6857513) B6857513
theorem B3047783 : Blo 2031435 3047783 := bstep (se 1 (by rfl) ⟨2285837, by rfl⟩ : syracuseStep 3047783 = 4571675) B4571675
theorem B2031855 : Blo 2031435 2031855 := bstep (se 1 (by rfl) ⟨1523891, by rfl⟩ : syracuseStep 2031855 = 3047783) B3047783
theorem B3047789 : Blo 2031435 3047789 := bbase (se 3 (by rfl) ⟨571460, by rfl⟩ : syracuseStep 3047789 = 1142921) (by norm_num)
theorem B2031859 : Blo 2031435 2031859 := bstep (se 1 (by rfl) ⟨1523894, by rfl⟩ : syracuseStep 2031859 = 3047789) B3047789
theorem B4571693 : Blo 2031435 4571693 := bbase (se 3 (by rfl) ⟨857192, by rfl⟩ : syracuseStep 4571693 = 1714385) (by norm_num)
theorem B3047795 : Blo 2031435 3047795 := bstep (se 1 (by rfl) ⟨2285846, by rfl⟩ : syracuseStep 3047795 = 4571693) B4571693
theorem B2031863 : Blo 2031435 2031863 := bstep (se 1 (by rfl) ⟨1523897, by rfl⟩ : syracuseStep 2031863 = 3047795) B3047795
theorem B7045957 : Blo 2031435 7045957 := bbase (se 4 (by rfl) ⟨660558, by rfl⟩ : syracuseStep 7045957 = 1321117) (by norm_num)
theorem B37578437 : Blo 2031435 37578437 := bstep (se 4 (by rfl) ⟨3522978, by rfl⟩ : syracuseStep 37578437 = 7045957) B7045957
theorem B25052291 : Blo 2031435 25052291 := bstep (se 1 (by rfl) ⟨18789218, by rfl⟩ : syracuseStep 25052291 = 37578437) B37578437
theorem B16701527 : Blo 2031435 16701527 := bstep (se 1 (by rfl) ⟨12526145, by rfl⟩ : syracuseStep 16701527 = 25052291) B25052291
theorem B11134351 : Blo 2031435 11134351 := bstep (se 1 (by rfl) ⟨8350763, by rfl⟩ : syracuseStep 11134351 = 16701527) B16701527
theorem B14845801 : Blo 2031435 14845801 := bstep (se 2 (by rfl) ⟨5567175, by rfl⟩ : syracuseStep 14845801 = 11134351) B11134351
theorem B19794401 : Blo 2031435 19794401 := bstep (se 2 (by rfl) ⟨7422900, by rfl⟩ : syracuseStep 19794401 = 14845801) B14845801
theorem B13196267 : Blo 2031435 13196267 := bstep (se 1 (by rfl) ⟨9897200, by rfl⟩ : syracuseStep 13196267 = 19794401) B19794401
theorem B8797511 : Blo 2031435 8797511 := bstep (se 1 (by rfl) ⟨6598133, by rfl⟩ : syracuseStep 8797511 = 13196267) B13196267
theorem B5865007 : Blo 2031435 5865007 := bstep (se 1 (by rfl) ⟨4398755, by rfl⟩ : syracuseStep 5865007 = 8797511) B8797511
theorem B7820009 : Blo 2031435 7820009 := bstep (se 2 (by rfl) ⟨2932503, by rfl⟩ : syracuseStep 7820009 = 5865007) B5865007
theorem B5213339 : Blo 2031435 5213339 := bstep (se 1 (by rfl) ⟨3910004, by rfl⟩ : syracuseStep 5213339 = 7820009) B7820009
theorem B3475559 : Blo 2031435 3475559 := bstep (se 1 (by rfl) ⟨2606669, by rfl⟩ : syracuseStep 3475559 = 5213339) B5213339
theorem B9268157 : Blo 2031435 9268157 := bstep (se 3 (by rfl) ⟨1737779, by rfl⟩ : syracuseStep 9268157 = 3475559) B3475559
theorem B6178771 : Blo 2031435 6178771 := bstep (se 1 (by rfl) ⟨4634078, by rfl⟩ : syracuseStep 6178771 = 9268157) B9268157
theorem B8238361 : Blo 2031435 8238361 := bstep (se 2 (by rfl) ⟨3089385, by rfl⟩ : syracuseStep 8238361 = 6178771) B6178771
theorem B10984481 : Blo 2031435 10984481 := bstep (se 2 (by rfl) ⟨4119180, by rfl⟩ : syracuseStep 10984481 = 8238361) B8238361
theorem B7322987 : Blo 2031435 7322987 := bstep (se 1 (by rfl) ⟨5492240, by rfl⟩ : syracuseStep 7322987 = 10984481) B10984481
theorem B19527965 : Blo 2031435 19527965 := bstep (se 3 (by rfl) ⟨3661493, by rfl⟩ : syracuseStep 19527965 = 7322987) B7322987
theorem B13018643 : Blo 2031435 13018643 := bstep (se 1 (by rfl) ⟨9763982, by rfl⟩ : syracuseStep 13018643 = 19527965) B19527965
theorem B8679095 : Blo 2031435 8679095 := bstep (se 1 (by rfl) ⟨6509321, by rfl⟩ : syracuseStep 8679095 = 13018643) B13018643
theorem B5786063 : Blo 2031435 5786063 := bstep (se 1 (by rfl) ⟨4339547, by rfl⟩ : syracuseStep 5786063 = 8679095) B8679095
theorem B3857375 : Blo 2031435 3857375 := bstep (se 1 (by rfl) ⟨2893031, by rfl⟩ : syracuseStep 3857375 = 5786063) B5786063
theorem B2571583 : Blo 2031435 2571583 := bstep (se 1 (by rfl) ⟨1928687, by rfl⟩ : syracuseStep 2571583 = 3857375) B3857375
theorem B3428777 : Blo 2031435 3428777 := bstep (se 2 (by rfl) ⟨1285791, by rfl⟩ : syracuseStep 3428777 = 2571583) B2571583
theorem B2285851 : Blo 2031435 2285851 := bstep (se 1 (by rfl) ⟨1714388, by rfl⟩ : syracuseStep 2285851 = 3428777) B3428777
theorem B3047801 : Blo 2031435 3047801 := bstep (se 2 (by rfl) ⟨1142925, by rfl⟩ : syracuseStep 3047801 = 2285851) B2285851
theorem B2031867 : Blo 2031435 2031867 := bstep (se 1 (by rfl) ⟨1523900, by rfl⟩ : syracuseStep 2031867 = 3047801) B3047801
theorem B34716437 : Blo 2031435 34716437 := bbase (se 6 (by rfl) ⟨813666, by rfl⟩ : syracuseStep 34716437 = 1627333) (by norm_num)
theorem B23144291 : Blo 2031435 23144291 := bstep (se 1 (by rfl) ⟨17358218, by rfl⟩ : syracuseStep 23144291 = 34716437) B34716437
theorem B15429527 : Blo 2031435 15429527 := bstep (se 1 (by rfl) ⟨11572145, by rfl⟩ : syracuseStep 15429527 = 23144291) B23144291
theorem B10286351 : Blo 2031435 10286351 := bstep (se 1 (by rfl) ⟨7714763, by rfl⟩ : syracuseStep 10286351 = 15429527) B15429527
theorem B6857567 : Blo 2031435 6857567 := bstep (se 1 (by rfl) ⟨5143175, by rfl⟩ : syracuseStep 6857567 = 10286351) B10286351
theorem B4571711 : Blo 2031435 4571711 := bstep (se 1 (by rfl) ⟨3428783, by rfl⟩ : syracuseStep 4571711 = 6857567) B6857567
theorem B3047807 : Blo 2031435 3047807 := bstep (se 1 (by rfl) ⟨2285855, by rfl⟩ : syracuseStep 3047807 = 4571711) B4571711
theorem B2031871 : Blo 2031435 2031871 := bstep (se 1 (by rfl) ⟨1523903, by rfl⟩ : syracuseStep 2031871 = 3047807) B3047807
theorem B3047813 : Blo 2031435 3047813 := bbase (se 4 (by rfl) ⟨285732, by rfl⟩ : syracuseStep 3047813 = 571465) (by norm_num)
theorem B2031875 : Blo 2031435 2031875 := bstep (se 1 (by rfl) ⟨1523906, by rfl⟩ : syracuseStep 2031875 = 3047813) B3047813
theorem B3428797 : Blo 2031435 3428797 := bbase (se 3 (by rfl) ⟨642899, by rfl⟩ : syracuseStep 3428797 = 1285799) (by norm_num)
theorem B4571729 : Blo 2031435 4571729 := bstep (se 2 (by rfl) ⟨1714398, by rfl⟩ : syracuseStep 4571729 = 3428797) B3428797
theorem B3047819 : Blo 2031435 3047819 := bstep (se 1 (by rfl) ⟨2285864, by rfl⟩ : syracuseStep 3047819 = 4571729) B4571729
theorem B2031879 : Blo 2031435 2031879 := bstep (se 1 (by rfl) ⟨1523909, by rfl⟩ : syracuseStep 2031879 = 3047819) B3047819
theorem B2285869 : Blo 2031435 2285869 := bbase (se 3 (by rfl) ⟨428600, by rfl⟩ : syracuseStep 2285869 = 857201) (by norm_num)
theorem B3047825 : Blo 2031435 3047825 := bstep (se 2 (by rfl) ⟨1142934, by rfl⟩ : syracuseStep 3047825 = 2285869) B2285869
theorem B2031883 : Blo 2031435 2031883 := bstep (se 1 (by rfl) ⟨1523912, by rfl⟩ : syracuseStep 2031883 = 3047825) B3047825
theorem B6857621 : Blo 2031435 6857621 := bbase (se 6 (by rfl) ⟨160725, by rfl⟩ : syracuseStep 6857621 = 321451) (by norm_num)
theorem B4571747 : Blo 2031435 4571747 := bstep (se 1 (by rfl) ⟨3428810, by rfl⟩ : syracuseStep 4571747 = 6857621) B6857621
theorem B3047831 : Blo 2031435 3047831 := bstep (se 1 (by rfl) ⟨2285873, by rfl⟩ : syracuseStep 3047831 = 4571747) B4571747
theorem B2031887 : Blo 2031435 2031887 := bstep (se 1 (by rfl) ⟨1523915, by rfl⟩ : syracuseStep 2031887 = 3047831) B3047831
theorem B3047837 : Blo 2031435 3047837 := bbase (se 3 (by rfl) ⟨571469, by rfl⟩ : syracuseStep 3047837 = 1142939) (by norm_num)
theorem B2031891 : Blo 2031435 2031891 := bstep (se 1 (by rfl) ⟨1523918, by rfl⟩ : syracuseStep 2031891 = 3047837) B3047837
theorem B4571765 : Blo 2031435 4571765 := bbase (se 5 (by rfl) ⟨214301, by rfl⟩ : syracuseStep 4571765 = 428603) (by norm_num)
theorem B3047843 : Blo 2031435 3047843 := bstep (se 1 (by rfl) ⟨2285882, by rfl⟩ : syracuseStep 3047843 = 4571765) B4571765
theorem B2031895 : Blo 2031435 2031895 := bstep (se 1 (by rfl) ⟨1523921, by rfl⟩ : syracuseStep 2031895 = 3047843) B3047843
theorem B3475613 : Blo 2031435 3475613 := bbase (se 3 (by rfl) ⟨651677, by rfl⟩ : syracuseStep 3475613 = 1303355) (by norm_num)
theorem B9268301 : Blo 2031435 9268301 := bstep (se 3 (by rfl) ⟨1737806, by rfl⟩ : syracuseStep 9268301 = 3475613) B3475613
theorem B24715469 : Blo 2031435 24715469 := bstep (se 3 (by rfl) ⟨4634150, by rfl⟩ : syracuseStep 24715469 = 9268301) B9268301
theorem B16476979 : Blo 2031435 16476979 := bstep (se 1 (by rfl) ⟨12357734, by rfl⟩ : syracuseStep 16476979 = 24715469) B24715469
theorem B21969305 : Blo 2031435 21969305 := bstep (se 2 (by rfl) ⟨8238489, by rfl⟩ : syracuseStep 21969305 = 16476979) B16476979
theorem B14646203 : Blo 2031435 14646203 := bstep (se 1 (by rfl) ⟨10984652, by rfl⟩ : syracuseStep 14646203 = 21969305) B21969305
theorem B9764135 : Blo 2031435 9764135 := bstep (se 1 (by rfl) ⟨7323101, by rfl⟩ : syracuseStep 9764135 = 14646203) B14646203
theorem B6509423 : Blo 2031435 6509423 := bstep (se 1 (by rfl) ⟨4882067, by rfl⟩ : syracuseStep 6509423 = 9764135) B9764135
theorem B17358461 : Blo 2031435 17358461 := bstep (se 3 (by rfl) ⟨3254711, by rfl⟩ : syracuseStep 17358461 = 6509423) B6509423
theorem B11572307 : Blo 2031435 11572307 := bstep (se 1 (by rfl) ⟨8679230, by rfl⟩ : syracuseStep 11572307 = 17358461) B17358461
theorem B7714871 : Blo 2031435 7714871 := bstep (se 1 (by rfl) ⟨5786153, by rfl⟩ : syracuseStep 7714871 = 11572307) B11572307
theorem B5143247 : Blo 2031435 5143247 := bstep (se 1 (by rfl) ⟨3857435, by rfl⟩ : syracuseStep 5143247 = 7714871) B7714871
theorem B3428831 : Blo 2031435 3428831 := bstep (se 1 (by rfl) ⟨2571623, by rfl⟩ : syracuseStep 3428831 = 5143247) B5143247
theorem B2285887 : Blo 2031435 2285887 := bstep (se 1 (by rfl) ⟨1714415, by rfl⟩ : syracuseStep 2285887 = 3428831) B3428831
theorem B3047849 : Blo 2031435 3047849 := bstep (se 2 (by rfl) ⟨1142943, by rfl⟩ : syracuseStep 3047849 = 2285887) B2285887
theorem B2031899 : Blo 2031435 2031899 := bstep (se 1 (by rfl) ⟨1523924, by rfl⟩ : syracuseStep 2031899 = 3047849) B3047849
theorem B7714885 : Blo 2031435 7714885 := bbase (se 4 (by rfl) ⟨723270, by rfl⟩ : syracuseStep 7714885 = 1446541) (by norm_num)
theorem B10286513 : Blo 2031435 10286513 := bstep (se 2 (by rfl) ⟨3857442, by rfl⟩ : syracuseStep 10286513 = 7714885) B7714885
theorem B6857675 : Blo 2031435 6857675 := bstep (se 1 (by rfl) ⟨5143256, by rfl⟩ : syracuseStep 6857675 = 10286513) B10286513
theorem B4571783 : Blo 2031435 4571783 := bstep (se 1 (by rfl) ⟨3428837, by rfl⟩ : syracuseStep 4571783 = 6857675) B6857675
theorem B3047855 : Blo 2031435 3047855 := bstep (se 1 (by rfl) ⟨2285891, by rfl⟩ : syracuseStep 3047855 = 4571783) B4571783
theorem B2031903 : Blo 2031435 2031903 := bstep (se 1 (by rfl) ⟨1523927, by rfl⟩ : syracuseStep 2031903 = 3047855) B3047855
theorem B3047861 : Blo 2031435 3047861 := bbase (se 5 (by rfl) ⟨142868, by rfl⟩ : syracuseStep 3047861 = 285737) (by norm_num)
theorem B2031907 : Blo 2031435 2031907 := bstep (se 1 (by rfl) ⟨1523930, by rfl⟩ : syracuseStep 2031907 = 3047861) B3047861
theorem B5143277 : Blo 2031435 5143277 := bbase (se 3 (by rfl) ⟨964364, by rfl⟩ : syracuseStep 5143277 = 1928729) (by norm_num)
theorem B3428851 : Blo 2031435 3428851 := bstep (se 1 (by rfl) ⟨2571638, by rfl⟩ : syracuseStep 3428851 = 5143277) B5143277
theorem B4571801 : Blo 2031435 4571801 := bstep (se 2 (by rfl) ⟨1714425, by rfl⟩ : syracuseStep 4571801 = 3428851) B3428851
theorem B3047867 : Blo 2031435 3047867 := bstep (se 1 (by rfl) ⟨2285900, by rfl⟩ : syracuseStep 3047867 = 4571801) B4571801
theorem B2031911 : Blo 2031435 2031911 := bstep (se 1 (by rfl) ⟨1523933, by rfl⟩ : syracuseStep 2031911 = 3047867) B3047867
theorem B2285905 : Blo 2031435 2285905 := bbase (se 2 (by rfl) ⟨857214, by rfl⟩ : syracuseStep 2285905 = 1714429) (by norm_num)
theorem B3047873 : Blo 2031435 3047873 := bstep (se 2 (by rfl) ⟨1142952, by rfl⟩ : syracuseStep 3047873 = 2285905) B2285905
theorem B2031915 : Blo 2031435 2031915 := bstep (se 1 (by rfl) ⟨1523936, by rfl⟩ : syracuseStep 2031915 = 3047873) B3047873
theorem B2169829 : Blo 2031435 2169829 := bbase (se 4 (by rfl) ⟨203421, by rfl⟩ : syracuseStep 2169829 = 406843) (by norm_num)
theorem B2893105 : Blo 2031435 2893105 := bstep (se 2 (by rfl) ⟨1084914, by rfl⟩ : syracuseStep 2893105 = 2169829) B2169829
theorem B3857473 : Blo 2031435 3857473 := bstep (se 2 (by rfl) ⟨1446552, by rfl⟩ : syracuseStep 3857473 = 2893105) B2893105
theorem B5143297 : Blo 2031435 5143297 := bstep (se 2 (by rfl) ⟨1928736, by rfl⟩ : syracuseStep 5143297 = 3857473) B3857473
theorem B6857729 : Blo 2031435 6857729 := bstep (se 2 (by rfl) ⟨2571648, by rfl⟩ : syracuseStep 6857729 = 5143297) B5143297
theorem B4571819 : Blo 2031435 4571819 := bstep (se 1 (by rfl) ⟨3428864, by rfl⟩ : syracuseStep 4571819 = 6857729) B6857729
theorem B3047879 : Blo 2031435 3047879 := bstep (se 1 (by rfl) ⟨2285909, by rfl⟩ : syracuseStep 3047879 = 4571819) B4571819
theorem B2031919 : Blo 2031435 2031919 := bstep (se 1 (by rfl) ⟨1523939, by rfl⟩ : syracuseStep 2031919 = 3047879) B3047879
theorem B3047885 : Blo 2031435 3047885 := bbase (se 3 (by rfl) ⟨571478, by rfl⟩ : syracuseStep 3047885 = 1142957) (by norm_num)
theorem B2031923 : Blo 2031435 2031923 := bstep (se 1 (by rfl) ⟨1523942, by rfl⟩ : syracuseStep 2031923 = 3047885) B3047885
theorem B4571837 : Blo 2031435 4571837 := bbase (se 3 (by rfl) ⟨857219, by rfl⟩ : syracuseStep 4571837 = 1714439) (by norm_num)
theorem B3047891 : Blo 2031435 3047891 := bstep (se 1 (by rfl) ⟨2285918, by rfl⟩ : syracuseStep 3047891 = 4571837) B4571837
theorem B2031927 : Blo 2031435 2031927 := bstep (se 1 (by rfl) ⟨1523945, by rfl⟩ : syracuseStep 2031927 = 3047891) B3047891
theorem B3428885 : Blo 2031435 3428885 := bbase (se 6 (by rfl) ⟨80364, by rfl⟩ : syracuseStep 3428885 = 160729) (by norm_num)
theorem B2285923 : Blo 2031435 2285923 := bstep (se 1 (by rfl) ⟨1714442, by rfl⟩ : syracuseStep 2285923 = 3428885) B3428885
theorem B3047897 : Blo 2031435 3047897 := bstep (se 2 (by rfl) ⟨1142961, by rfl⟩ : syracuseStep 3047897 = 2285923) B2285923
theorem B2031931 : Blo 2031435 2031931 := bstep (se 1 (by rfl) ⟨1523948, by rfl⟩ : syracuseStep 2031931 = 3047897) B3047897
theorem B6951349 : Blo 2031435 6951349 := bbase (se 5 (by rfl) ⟨325844, by rfl⟩ : syracuseStep 6951349 = 651689) (by norm_num)
theorem B9268465 : Blo 2031435 9268465 := bstep (se 2 (by rfl) ⟨3475674, by rfl⟩ : syracuseStep 9268465 = 6951349) B6951349
theorem B12357953 : Blo 2031435 12357953 := bstep (se 2 (by rfl) ⟨4634232, by rfl⟩ : syracuseStep 12357953 = 9268465) B9268465
theorem B8238635 : Blo 2031435 8238635 := bstep (se 1 (by rfl) ⟨6178976, by rfl⟩ : syracuseStep 8238635 = 12357953) B12357953
theorem B5492423 : Blo 2031435 5492423 := bstep (se 1 (by rfl) ⟨4119317, by rfl⟩ : syracuseStep 5492423 = 8238635) B8238635
theorem B3661615 : Blo 2031435 3661615 := bstep (se 1 (by rfl) ⟨2746211, by rfl⟩ : syracuseStep 3661615 = 5492423) B5492423
theorem B19528613 : Blo 2031435 19528613 := bstep (se 4 (by rfl) ⟨1830807, by rfl⟩ : syracuseStep 19528613 = 3661615) B3661615
theorem B13019075 : Blo 2031435 13019075 := bstep (se 1 (by rfl) ⟨9764306, by rfl⟩ : syracuseStep 13019075 = 19528613) B19528613
theorem B8679383 : Blo 2031435 8679383 := bstep (se 1 (by rfl) ⟨6509537, by rfl⟩ : syracuseStep 8679383 = 13019075) B13019075
theorem B5786255 : Blo 2031435 5786255 := bstep (se 1 (by rfl) ⟨4339691, by rfl⟩ : syracuseStep 5786255 = 8679383) B8679383
theorem B15430013 : Blo 2031435 15430013 := bstep (se 3 (by rfl) ⟨2893127, by rfl⟩ : syracuseStep 15430013 = 5786255) B5786255
theorem B10286675 : Blo 2031435 10286675 := bstep (se 1 (by rfl) ⟨7715006, by rfl⟩ : syracuseStep 10286675 = 15430013) B15430013
theorem B6857783 : Blo 2031435 6857783 := bstep (se 1 (by rfl) ⟨5143337, by rfl⟩ : syracuseStep 6857783 = 10286675) B10286675
theorem B4571855 : Blo 2031435 4571855 := bstep (se 1 (by rfl) ⟨3428891, by rfl⟩ : syracuseStep 4571855 = 6857783) B6857783
theorem B3047903 : Blo 2031435 3047903 := bstep (se 1 (by rfl) ⟨2285927, by rfl⟩ : syracuseStep 3047903 = 4571855) B4571855
theorem B2031935 : Blo 2031435 2031935 := bstep (se 1 (by rfl) ⟨1523951, by rfl⟩ : syracuseStep 2031935 = 3047903) B3047903
theorem B3047909 : Blo 2031435 3047909 := bbase (se 4 (by rfl) ⟨285741, by rfl⟩ : syracuseStep 3047909 = 571483) (by norm_num)
theorem B2031939 : Blo 2031435 2031939 := bstep (se 1 (by rfl) ⟨1523954, by rfl⟩ : syracuseStep 2031939 = 3047909) B3047909
theorem B5213533 : Blo 2031435 5213533 := bbase (se 3 (by rfl) ⟨977537, by rfl⟩ : syracuseStep 5213533 = 1955075) (by norm_num)
theorem B6951377 : Blo 2031435 6951377 := bstep (se 2 (by rfl) ⟨2606766, by rfl⟩ : syracuseStep 6951377 = 5213533) B5213533
theorem B18537005 : Blo 2031435 18537005 := bstep (se 3 (by rfl) ⟨3475688, by rfl⟩ : syracuseStep 18537005 = 6951377) B6951377
theorem B12358003 : Blo 2031435 12358003 := bstep (se 1 (by rfl) ⟨9268502, by rfl⟩ : syracuseStep 12358003 = 18537005) B18537005
theorem B16477337 : Blo 2031435 16477337 := bstep (se 2 (by rfl) ⟨6179001, by rfl⟩ : syracuseStep 16477337 = 12358003) B12358003
theorem B10984891 : Blo 2031435 10984891 := bstep (se 1 (by rfl) ⟨8238668, by rfl⟩ : syracuseStep 10984891 = 16477337) B16477337
theorem B14646521 : Blo 2031435 14646521 := bstep (se 2 (by rfl) ⟨5492445, by rfl⟩ : syracuseStep 14646521 = 10984891) B10984891
theorem B9764347 : Blo 2031435 9764347 := bstep (se 1 (by rfl) ⟨7323260, by rfl⟩ : syracuseStep 9764347 = 14646521) B14646521
theorem B13019129 : Blo 2031435 13019129 := bstep (se 2 (by rfl) ⟨4882173, by rfl⟩ : syracuseStep 13019129 = 9764347) B9764347
theorem B8679419 : Blo 2031435 8679419 := bstep (se 1 (by rfl) ⟨6509564, by rfl⟩ : syracuseStep 8679419 = 13019129) B13019129
theorem B5786279 : Blo 2031435 5786279 := bstep (se 1 (by rfl) ⟨4339709, by rfl⟩ : syracuseStep 5786279 = 8679419) B8679419
theorem B3857519 : Blo 2031435 3857519 := bstep (se 1 (by rfl) ⟨2893139, by rfl⟩ : syracuseStep 3857519 = 5786279) B5786279
theorem B2571679 : Blo 2031435 2571679 := bstep (se 1 (by rfl) ⟨1928759, by rfl⟩ : syracuseStep 2571679 = 3857519) B3857519
theorem B3428905 : Blo 2031435 3428905 := bstep (se 2 (by rfl) ⟨1285839, by rfl⟩ : syracuseStep 3428905 = 2571679) B2571679
theorem B4571873 : Blo 2031435 4571873 := bstep (se 2 (by rfl) ⟨1714452, by rfl⟩ : syracuseStep 4571873 = 3428905) B3428905
theorem B3047915 : Blo 2031435 3047915 := bstep (se 1 (by rfl) ⟨2285936, by rfl⟩ : syracuseStep 3047915 = 4571873) B4571873
theorem B2031943 : Blo 2031435 2031943 := bstep (se 1 (by rfl) ⟨1523957, by rfl⟩ : syracuseStep 2031943 = 3047915) B3047915
theorem B2285941 : Blo 2031435 2285941 := bbase (se 5 (by rfl) ⟨107153, by rfl⟩ : syracuseStep 2285941 = 214307) (by norm_num)
theorem B3047921 : Blo 2031435 3047921 := bstep (se 2 (by rfl) ⟨1142970, by rfl⟩ : syracuseStep 3047921 = 2285941) B2285941
theorem B2031947 : Blo 2031435 2031947 := bstep (se 1 (by rfl) ⟨1523960, by rfl⟩ : syracuseStep 2031947 = 3047921) B3047921
theorem B2571689 : Blo 2031435 2571689 := bbase (se 2 (by rfl) ⟨964383, by rfl⟩ : syracuseStep 2571689 = 1928767) (by norm_num)
theorem B6857837 : Blo 2031435 6857837 := bstep (se 3 (by rfl) ⟨1285844, by rfl⟩ : syracuseStep 6857837 = 2571689) B2571689
theorem B4571891 : Blo 2031435 4571891 := bstep (se 1 (by rfl) ⟨3428918, by rfl⟩ : syracuseStep 4571891 = 6857837) B6857837
theorem B3047927 : Blo 2031435 3047927 := bstep (se 1 (by rfl) ⟨2285945, by rfl⟩ : syracuseStep 3047927 = 4571891) B4571891
theorem B2031951 : Blo 2031435 2031951 := bstep (se 1 (by rfl) ⟨1523963, by rfl⟩ : syracuseStep 2031951 = 3047927) B3047927
theorem B3047933 : Blo 2031435 3047933 := bbase (se 3 (by rfl) ⟨571487, by rfl⟩ : syracuseStep 3047933 = 1142975) (by norm_num)
theorem B2031955 : Blo 2031435 2031955 := bstep (se 1 (by rfl) ⟨1523966, by rfl⟩ : syracuseStep 2031955 = 3047933) B3047933
theorem B4571909 : Blo 2031435 4571909 := bbase (se 4 (by rfl) ⟨428616, by rfl⟩ : syracuseStep 4571909 = 857233) (by norm_num)
theorem B3047939 : Blo 2031435 3047939 := bstep (se 1 (by rfl) ⟨2285954, by rfl⟩ : syracuseStep 3047939 = 4571909) B4571909
theorem B2031959 : Blo 2031435 2031959 := bstep (se 1 (by rfl) ⟨1523969, by rfl⟩ : syracuseStep 2031959 = 3047939) B3047939
theorem B3857557 : Blo 2031435 3857557 := bbase (se 6 (by rfl) ⟨90411, by rfl⟩ : syracuseStep 3857557 = 180823) (by norm_num)
theorem B5143409 : Blo 2031435 5143409 := bstep (se 2 (by rfl) ⟨1928778, by rfl⟩ : syracuseStep 5143409 = 3857557) B3857557
theorem B3428939 : Blo 2031435 3428939 := bstep (se 1 (by rfl) ⟨2571704, by rfl⟩ : syracuseStep 3428939 = 5143409) B5143409
theorem B2285959 : Blo 2031435 2285959 := bstep (se 1 (by rfl) ⟨1714469, by rfl⟩ : syracuseStep 2285959 = 3428939) B3428939
theorem B3047945 : Blo 2031435 3047945 := bstep (se 2 (by rfl) ⟨1142979, by rfl⟩ : syracuseStep 3047945 = 2285959) B2285959
theorem B2031963 : Blo 2031435 2031963 := bstep (se 1 (by rfl) ⟨1523972, by rfl⟩ : syracuseStep 2031963 = 3047945) B3047945
theorem B10286837 : Blo 2031435 10286837 := bbase (se 5 (by rfl) ⟨482195, by rfl⟩ : syracuseStep 10286837 = 964391) (by norm_num)
theorem B6857891 : Blo 2031435 6857891 := bstep (se 1 (by rfl) ⟨5143418, by rfl⟩ : syracuseStep 6857891 = 10286837) B10286837
theorem B4571927 : Blo 2031435 4571927 := bstep (se 1 (by rfl) ⟨3428945, by rfl⟩ : syracuseStep 4571927 = 6857891) B6857891
theorem B3047951 : Blo 2031435 3047951 := bstep (se 1 (by rfl) ⟨2285963, by rfl⟩ : syracuseStep 3047951 = 4571927) B4571927
theorem B2031967 : Blo 2031435 2031967 := bstep (se 1 (by rfl) ⟨1523975, by rfl⟩ : syracuseStep 2031967 = 3047951) B3047951
theorem B3047957 : Blo 2031435 3047957 := bbase (se 6 (by rfl) ⟨71436, by rfl⟩ : syracuseStep 3047957 = 142873) (by norm_num)
theorem B2031971 : Blo 2031435 2031971 := bstep (se 1 (by rfl) ⟨1523978, by rfl⟩ : syracuseStep 2031971 = 3047957) B3047957
theorem B2441125 : Blo 2031435 2441125 := bbase (se 4 (by rfl) ⟨228855, by rfl⟩ : syracuseStep 2441125 = 457711) (by norm_num)
theorem B3254833 : Blo 2031435 3254833 := bstep (se 2 (by rfl) ⟨1220562, by rfl⟩ : syracuseStep 3254833 = 2441125) B2441125
theorem B17359109 : Blo 2031435 17359109 := bstep (se 4 (by rfl) ⟨1627416, by rfl⟩ : syracuseStep 17359109 = 3254833) B3254833
theorem B11572739 : Blo 2031435 11572739 := bstep (se 1 (by rfl) ⟨8679554, by rfl⟩ : syracuseStep 11572739 = 17359109) B17359109
theorem B7715159 : Blo 2031435 7715159 := bstep (se 1 (by rfl) ⟨5786369, by rfl⟩ : syracuseStep 7715159 = 11572739) B11572739
theorem B5143439 : Blo 2031435 5143439 := bstep (se 1 (by rfl) ⟨3857579, by rfl⟩ : syracuseStep 5143439 = 7715159) B7715159
theorem B3428959 : Blo 2031435 3428959 := bstep (se 1 (by rfl) ⟨2571719, by rfl⟩ : syracuseStep 3428959 = 5143439) B5143439
theorem B4571945 : Blo 2031435 4571945 := bstep (se 2 (by rfl) ⟨1714479, by rfl⟩ : syracuseStep 4571945 = 3428959) B3428959
theorem B3047963 : Blo 2031435 3047963 := bstep (se 1 (by rfl) ⟨2285972, by rfl⟩ : syracuseStep 3047963 = 4571945) B4571945
theorem B2031975 : Blo 2031435 2031975 := bstep (se 1 (by rfl) ⟨1523981, by rfl⟩ : syracuseStep 2031975 = 3047963) B3047963
theorem B2285977 : Blo 2031435 2285977 := bbase (se 2 (by rfl) ⟨857241, by rfl⟩ : syracuseStep 2285977 = 1714483) (by norm_num)
theorem B3047969 : Blo 2031435 3047969 := bstep (se 2 (by rfl) ⟨1142988, by rfl⟩ : syracuseStep 3047969 = 2285977) B2285977
theorem B2031979 : Blo 2031435 2031979 := bstep (se 1 (by rfl) ⟨1523984, by rfl⟩ : syracuseStep 2031979 = 3047969) B3047969
theorem B7715189 : Blo 2031435 7715189 := bbase (se 5 (by rfl) ⟨361649, by rfl⟩ : syracuseStep 7715189 = 723299) (by norm_num)
theorem B5143459 : Blo 2031435 5143459 := bstep (se 1 (by rfl) ⟨3857594, by rfl⟩ : syracuseStep 5143459 = 7715189) B7715189
theorem B6857945 : Blo 2031435 6857945 := bstep (se 2 (by rfl) ⟨2571729, by rfl⟩ : syracuseStep 6857945 = 5143459) B5143459
theorem B4571963 : Blo 2031435 4571963 := bstep (se 1 (by rfl) ⟨3428972, by rfl⟩ : syracuseStep 4571963 = 6857945) B6857945
theorem B3047975 : Blo 2031435 3047975 := bstep (se 1 (by rfl) ⟨2285981, by rfl⟩ : syracuseStep 3047975 = 4571963) B4571963
theorem B2031983 : Blo 2031435 2031983 := bstep (se 1 (by rfl) ⟨1523987, by rfl⟩ : syracuseStep 2031983 = 3047975) B3047975
theorem B3047981 : Blo 2031435 3047981 := bbase (se 3 (by rfl) ⟨571496, by rfl⟩ : syracuseStep 3047981 = 1142993) (by norm_num)
theorem B2031987 : Blo 2031435 2031987 := bstep (se 1 (by rfl) ⟨1523990, by rfl⟩ : syracuseStep 2031987 = 3047981) B3047981
theorem B4571981 : Blo 2031435 4571981 := bbase (se 3 (by rfl) ⟨857246, by rfl⟩ : syracuseStep 4571981 = 1714493) (by norm_num)
theorem B3047987 : Blo 2031435 3047987 := bstep (se 1 (by rfl) ⟨2285990, by rfl⟩ : syracuseStep 3047987 = 4571981) B4571981
theorem B2031991 : Blo 2031435 2031991 := bstep (se 1 (by rfl) ⟨1523993, by rfl⟩ : syracuseStep 2031991 = 3047987) B3047987
theorem B2571745 : Blo 2031435 2571745 := bbase (se 2 (by rfl) ⟨964404, by rfl⟩ : syracuseStep 2571745 = 1928809) (by norm_num)
theorem B3428993 : Blo 2031435 3428993 := bstep (se 2 (by rfl) ⟨1285872, by rfl⟩ : syracuseStep 3428993 = 2571745) B2571745
theorem B2285995 : Blo 2031435 2285995 := bstep (se 1 (by rfl) ⟨1714496, by rfl⟩ : syracuseStep 2285995 = 3428993) B3428993
theorem B3047993 : Blo 2031435 3047993 := bstep (se 2 (by rfl) ⟨1142997, by rfl⟩ : syracuseStep 3047993 = 2285995) B2285995
theorem B2031995 : Blo 2031435 2031995 := bstep (se 1 (by rfl) ⟨1523996, by rfl⟩ : syracuseStep 2031995 = 3047993) B3047993
theorem B23145749 : Blo 2031435 23145749 := bbase (se 6 (by rfl) ⟨542478, by rfl⟩ : syracuseStep 23145749 = 1084957) (by norm_num)
theorem B15430499 : Blo 2031435 15430499 := bstep (se 1 (by rfl) ⟨11572874, by rfl⟩ : syracuseStep 15430499 = 23145749) B23145749
theorem B10286999 : Blo 2031435 10286999 := bstep (se 1 (by rfl) ⟨7715249, by rfl⟩ : syracuseStep 10286999 = 15430499) B15430499
theorem B6857999 : Blo 2031435 6857999 := bstep (se 1 (by rfl) ⟨5143499, by rfl⟩ : syracuseStep 6857999 = 10286999) B10286999
theorem B4571999 : Blo 2031435 4571999 := bstep (se 1 (by rfl) ⟨3428999, by rfl⟩ : syracuseStep 4571999 = 6857999) B6857999
theorem B3047999 : Blo 2031435 3047999 := bstep (se 1 (by rfl) ⟨2285999, by rfl⟩ : syracuseStep 3047999 = 4571999) B4571999
theorem B2031999 : Blo 2031435 2031999 := bstep (se 1 (by rfl) ⟨1523999, by rfl⟩ : syracuseStep 2031999 = 3047999) B3047999
theorem B3048005 : Blo 2031435 3048005 := bbase (se 4 (by rfl) ⟨285750, by rfl⟩ : syracuseStep 3048005 = 571501) (by norm_num)
theorem B2032003 : Blo 2031435 2032003 := bstep (se 1 (by rfl) ⟨1524002, by rfl⟩ : syracuseStep 2032003 = 3048005) B3048005
theorem B3429013 : Blo 2031435 3429013 := bbase (se 6 (by rfl) ⟨80367, by rfl⟩ : syracuseStep 3429013 = 160735) (by norm_num)
theorem B4572017 : Blo 2031435 4572017 := bstep (se 2 (by rfl) ⟨1714506, by rfl⟩ : syracuseStep 4572017 = 3429013) B3429013
theorem B3048011 : Blo 2031435 3048011 := bstep (se 1 (by rfl) ⟨2286008, by rfl⟩ : syracuseStep 3048011 = 4572017) B4572017
theorem B2032007 : Blo 2031435 2032007 := bstep (se 1 (by rfl) ⟨1524005, by rfl⟩ : syracuseStep 2032007 = 3048011) B3048011
theorem B2286013 : Blo 2031435 2286013 := bbase (se 3 (by rfl) ⟨428627, by rfl⟩ : syracuseStep 2286013 = 857255) (by norm_num)
theorem B3048017 : Blo 2031435 3048017 := bstep (se 2 (by rfl) ⟨1143006, by rfl⟩ : syracuseStep 3048017 = 2286013) B2286013
theorem B2032011 : Blo 2031435 2032011 := bstep (se 1 (by rfl) ⟨1524008, by rfl⟩ : syracuseStep 2032011 = 3048017) B3048017
theorem B6858053 : Blo 2031435 6858053 := bbase (se 4 (by rfl) ⟨642942, by rfl⟩ : syracuseStep 6858053 = 1285885) (by norm_num)
theorem B4572035 : Blo 2031435 4572035 := bstep (se 1 (by rfl) ⟨3429026, by rfl⟩ : syracuseStep 4572035 = 6858053) B6858053
theorem B3048023 : Blo 2031435 3048023 := bstep (se 1 (by rfl) ⟨2286017, by rfl⟩ : syracuseStep 3048023 = 4572035) B4572035
theorem B2032015 : Blo 2031435 2032015 := bstep (se 1 (by rfl) ⟨1524011, by rfl⟩ : syracuseStep 2032015 = 3048023) B3048023
theorem B3048029 : Blo 2031435 3048029 := bbase (se 3 (by rfl) ⟨571505, by rfl⟩ : syracuseStep 3048029 = 1143011) (by norm_num)
theorem B2032019 : Blo 2031435 2032019 := bstep (se 1 (by rfl) ⟨1524014, by rfl⟩ : syracuseStep 2032019 = 3048029) B3048029
theorem B4572053 : Blo 2031435 4572053 := bbase (se 6 (by rfl) ⟨107157, by rfl⟩ : syracuseStep 4572053 = 214315) (by norm_num)
theorem B3048035 : Blo 2031435 3048035 := bstep (se 1 (by rfl) ⟨2286026, by rfl⟩ : syracuseStep 3048035 = 4572053) B4572053
theorem B2032023 : Blo 2031435 2032023 := bstep (se 1 (by rfl) ⟨1524017, by rfl⟩ : syracuseStep 2032023 = 3048035) B3048035
theorem B3254917 : Blo 2031435 3254917 := bbase (se 4 (by rfl) ⟨305148, by rfl⟩ : syracuseStep 3254917 = 610297) (by norm_num)
theorem B4339889 : Blo 2031435 4339889 := bstep (se 2 (by rfl) ⟨1627458, by rfl⟩ : syracuseStep 4339889 = 3254917) B3254917
theorem B2893259 : Blo 2031435 2893259 := bstep (se 1 (by rfl) ⟨2169944, by rfl⟩ : syracuseStep 2893259 = 4339889) B4339889
theorem B7715357 : Blo 2031435 7715357 := bstep (se 3 (by rfl) ⟨1446629, by rfl⟩ : syracuseStep 7715357 = 2893259) B2893259
theorem B5143571 : Blo 2031435 5143571 := bstep (se 1 (by rfl) ⟨3857678, by rfl⟩ : syracuseStep 5143571 = 7715357) B7715357
theorem B3429047 : Blo 2031435 3429047 := bstep (se 1 (by rfl) ⟨2571785, by rfl⟩ : syracuseStep 3429047 = 5143571) B5143571
theorem B2286031 : Blo 2031435 2286031 := bstep (se 1 (by rfl) ⟨1714523, by rfl⟩ : syracuseStep 2286031 = 3429047) B3429047
theorem B3048041 : Blo 2031435 3048041 := bstep (se 2 (by rfl) ⟨1143015, by rfl⟩ : syracuseStep 3048041 = 2286031) B2286031
theorem B2032027 : Blo 2031435 2032027 := bstep (se 1 (by rfl) ⟨1524020, by rfl⟩ : syracuseStep 2032027 = 3048041) B3048041
theorem B6509845 : Blo 2031435 6509845 := bbase (se 6 (by rfl) ⟨152574, by rfl⟩ : syracuseStep 6509845 = 305149) (by norm_num)
theorem B8679793 : Blo 2031435 8679793 := bstep (se 2 (by rfl) ⟨3254922, by rfl⟩ : syracuseStep 8679793 = 6509845) B6509845
theorem B11573057 : Blo 2031435 11573057 := bstep (se 2 (by rfl) ⟨4339896, by rfl⟩ : syracuseStep 11573057 = 8679793) B8679793
theorem B7715371 : Blo 2031435 7715371 := bstep (se 1 (by rfl) ⟨5786528, by rfl⟩ : syracuseStep 7715371 = 11573057) B11573057
theorem B10287161 : Blo 2031435 10287161 := bstep (se 2 (by rfl) ⟨3857685, by rfl⟩ : syracuseStep 10287161 = 7715371) B7715371
theorem B6858107 : Blo 2031435 6858107 := bstep (se 1 (by rfl) ⟨5143580, by rfl⟩ : syracuseStep 6858107 = 10287161) B10287161
theorem B4572071 : Blo 2031435 4572071 := bstep (se 1 (by rfl) ⟨3429053, by rfl⟩ : syracuseStep 4572071 = 6858107) B6858107
theorem B3048047 : Blo 2031435 3048047 := bstep (se 1 (by rfl) ⟨2286035, by rfl⟩ : syracuseStep 3048047 = 4572071) B4572071
theorem B2032031 : Blo 2031435 2032031 := bstep (se 1 (by rfl) ⟨1524023, by rfl⟩ : syracuseStep 2032031 = 3048047) B3048047
theorem B3048053 : Blo 2031435 3048053 := bbase (se 5 (by rfl) ⟨142877, by rfl⟩ : syracuseStep 3048053 = 285755) (by norm_num)
theorem B2032035 : Blo 2031435 2032035 := bstep (se 1 (by rfl) ⟨1524026, by rfl⟩ : syracuseStep 2032035 = 3048053) B3048053
theorem B3857701 : Blo 2031435 3857701 := bbase (se 4 (by rfl) ⟨361659, by rfl⟩ : syracuseStep 3857701 = 723319) (by norm_num)
theorem B5143601 : Blo 2031435 5143601 := bstep (se 2 (by rfl) ⟨1928850, by rfl⟩ : syracuseStep 5143601 = 3857701) B3857701
theorem B3429067 : Blo 2031435 3429067 := bstep (se 1 (by rfl) ⟨2571800, by rfl⟩ : syracuseStep 3429067 = 5143601) B5143601
theorem B4572089 : Blo 2031435 4572089 := bstep (se 2 (by rfl) ⟨1714533, by rfl⟩ : syracuseStep 4572089 = 3429067) B3429067
theorem B3048059 : Blo 2031435 3048059 := bstep (se 1 (by rfl) ⟨2286044, by rfl⟩ : syracuseStep 3048059 = 4572089) B4572089
theorem B2032039 : Blo 2031435 2032039 := bstep (se 1 (by rfl) ⟨1524029, by rfl⟩ : syracuseStep 2032039 = 3048059) B3048059
theorem B2286049 : Blo 2031435 2286049 := bbase (se 2 (by rfl) ⟨857268, by rfl⟩ : syracuseStep 2286049 = 1714537) (by norm_num)
theorem B3048065 : Blo 2031435 3048065 := bstep (se 2 (by rfl) ⟨1143024, by rfl⟩ : syracuseStep 3048065 = 2286049) B2286049
theorem B2032043 : Blo 2031435 2032043 := bstep (se 1 (by rfl) ⟨1524032, by rfl⟩ : syracuseStep 2032043 = 3048065) B3048065
theorem B5143621 : Blo 2031435 5143621 := bbase (se 4 (by rfl) ⟨482214, by rfl⟩ : syracuseStep 5143621 = 964429) (by norm_num)
theorem B6858161 : Blo 2031435 6858161 := bstep (se 2 (by rfl) ⟨2571810, by rfl⟩ : syracuseStep 6858161 = 5143621) B5143621
theorem B4572107 : Blo 2031435 4572107 := bstep (se 1 (by rfl) ⟨3429080, by rfl⟩ : syracuseStep 4572107 = 6858161) B6858161
theorem B3048071 : Blo 2031435 3048071 := bstep (se 1 (by rfl) ⟨2286053, by rfl⟩ : syracuseStep 3048071 = 4572107) B4572107
theorem B2032047 : Blo 2031435 2032047 := bstep (se 1 (by rfl) ⟨1524035, by rfl⟩ : syracuseStep 2032047 = 3048071) B3048071
theorem B3048077 : Blo 2031435 3048077 := bbase (se 3 (by rfl) ⟨571514, by rfl⟩ : syracuseStep 3048077 = 1143029) (by norm_num)
theorem B2032051 : Blo 2031435 2032051 := bstep (se 1 (by rfl) ⟨1524038, by rfl⟩ : syracuseStep 2032051 = 3048077) B3048077
theorem B4572125 : Blo 2031435 4572125 := bbase (se 3 (by rfl) ⟨857273, by rfl⟩ : syracuseStep 4572125 = 1714547) (by norm_num)
theorem B3048083 : Blo 2031435 3048083 := bstep (se 1 (by rfl) ⟨2286062, by rfl⟩ : syracuseStep 3048083 = 4572125) B4572125
theorem B2032055 : Blo 2031435 2032055 := bstep (se 1 (by rfl) ⟨1524041, by rfl⟩ : syracuseStep 2032055 = 3048083) B3048083
theorem B3429101 : Blo 2031435 3429101 := bbase (se 3 (by rfl) ⟨642956, by rfl⟩ : syracuseStep 3429101 = 1285913) (by norm_num)
theorem B2286067 : Blo 2031435 2286067 := bstep (se 1 (by rfl) ⟨1714550, by rfl⟩ : syracuseStep 2286067 = 3429101) B3429101
theorem B3048089 : Blo 2031435 3048089 := bstep (se 2 (by rfl) ⟨1143033, by rfl⟩ : syracuseStep 3048089 = 2286067) B2286067
theorem B2032059 : Blo 2031435 2032059 := bstep (se 1 (by rfl) ⟨1524044, by rfl⟩ : syracuseStep 2032059 = 3048089) B3048089
theorem B6179365 : Blo 2031435 6179365 := bbase (se 4 (by rfl) ⟨579315, by rfl⟩ : syracuseStep 6179365 = 1158631) (by norm_num)
theorem B8239153 : Blo 2031435 8239153 := bstep (se 2 (by rfl) ⟨3089682, by rfl⟩ : syracuseStep 8239153 = 6179365) B6179365
theorem B10985537 : Blo 2031435 10985537 := bstep (se 2 (by rfl) ⟨4119576, by rfl⟩ : syracuseStep 10985537 = 8239153) B8239153
theorem B7323691 : Blo 2031435 7323691 := bstep (se 1 (by rfl) ⟨5492768, by rfl⟩ : syracuseStep 7323691 = 10985537) B10985537
theorem B9764921 : Blo 2031435 9764921 := bstep (se 2 (by rfl) ⟨3661845, by rfl⟩ : syracuseStep 9764921 = 7323691) B7323691
theorem B26039789 : Blo 2031435 26039789 := bstep (se 3 (by rfl) ⟨4882460, by rfl⟩ : syracuseStep 26039789 = 9764921) B9764921
theorem B17359859 : Blo 2031435 17359859 := bstep (se 1 (by rfl) ⟨13019894, by rfl⟩ : syracuseStep 17359859 = 26039789) B26039789
theorem B11573239 : Blo 2031435 11573239 := bstep (se 1 (by rfl) ⟨8679929, by rfl⟩ : syracuseStep 11573239 = 17359859) B17359859
theorem B15430985 : Blo 2031435 15430985 := bstep (se 2 (by rfl) ⟨5786619, by rfl⟩ : syracuseStep 15430985 = 11573239) B11573239
theorem B10287323 : Blo 2031435 10287323 := bstep (se 1 (by rfl) ⟨7715492, by rfl⟩ : syracuseStep 10287323 = 15430985) B15430985
theorem B6858215 : Blo 2031435 6858215 := bstep (se 1 (by rfl) ⟨5143661, by rfl⟩ : syracuseStep 6858215 = 10287323) B10287323
theorem B4572143 : Blo 2031435 4572143 := bstep (se 1 (by rfl) ⟨3429107, by rfl⟩ : syracuseStep 4572143 = 6858215) B6858215
theorem B3048095 : Blo 2031435 3048095 := bstep (se 1 (by rfl) ⟨2286071, by rfl⟩ : syracuseStep 3048095 = 4572143) B4572143
theorem B2032063 : Blo 2031435 2032063 := bstep (se 1 (by rfl) ⟨1524047, by rfl⟩ : syracuseStep 2032063 = 3048095) B3048095
theorem B3048101 : Blo 2031435 3048101 := bbase (se 4 (by rfl) ⟨285759, by rfl⟩ : syracuseStep 3048101 = 571519) (by norm_num)
theorem B2032067 : Blo 2031435 2032067 := bstep (se 1 (by rfl) ⟨1524050, by rfl⟩ : syracuseStep 2032067 = 3048101) B3048101
theorem B2571841 : Blo 2031435 2571841 := bbase (se 2 (by rfl) ⟨964440, by rfl⟩ : syracuseStep 2571841 = 1928881) (by norm_num)
theorem B3429121 : Blo 2031435 3429121 := bstep (se 2 (by rfl) ⟨1285920, by rfl⟩ : syracuseStep 3429121 = 2571841) B2571841
theorem B4572161 : Blo 2031435 4572161 := bstep (se 2 (by rfl) ⟨1714560, by rfl⟩ : syracuseStep 4572161 = 3429121) B3429121
theorem B3048107 : Blo 2031435 3048107 := bstep (se 1 (by rfl) ⟨2286080, by rfl⟩ : syracuseStep 3048107 = 4572161) B4572161
theorem B2032071 : Blo 2031435 2032071 := bstep (se 1 (by rfl) ⟨1524053, by rfl⟩ : syracuseStep 2032071 = 3048107) B3048107
theorem B2286085 : Blo 2031435 2286085 := bbase (se 4 (by rfl) ⟨214320, by rfl⟩ : syracuseStep 2286085 = 428641) (by norm_num)
theorem B3048113 : Blo 2031435 3048113 := bstep (se 2 (by rfl) ⟨1143042, by rfl⟩ : syracuseStep 3048113 = 2286085) B2286085
theorem B2032075 : Blo 2031435 2032075 := bstep (se 1 (by rfl) ⟨1524056, by rfl⟩ : syracuseStep 2032075 = 3048113) B3048113
theorem B2893333 : Blo 2031435 2893333 := bbase (se 6 (by rfl) ⟨67812, by rfl⟩ : syracuseStep 2893333 = 135625) (by norm_num)
theorem B3857777 : Blo 2031435 3857777 := bstep (se 2 (by rfl) ⟨1446666, by rfl⟩ : syracuseStep 3857777 = 2893333) B2893333
theorem B2571851 : Blo 2031435 2571851 := bstep (se 1 (by rfl) ⟨1928888, by rfl⟩ : syracuseStep 2571851 = 3857777) B3857777
theorem B6858269 : Blo 2031435 6858269 := bstep (se 3 (by rfl) ⟨1285925, by rfl⟩ : syracuseStep 6858269 = 2571851) B2571851
theorem B4572179 : Blo 2031435 4572179 := bstep (se 1 (by rfl) ⟨3429134, by rfl⟩ : syracuseStep 4572179 = 6858269) B6858269
theorem B3048119 : Blo 2031435 3048119 := bstep (se 1 (by rfl) ⟨2286089, by rfl⟩ : syracuseStep 3048119 = 4572179) B4572179
theorem B2032079 : Blo 2031435 2032079 := bstep (se 1 (by rfl) ⟨1524059, by rfl⟩ : syracuseStep 2032079 = 3048119) B3048119
theorem B3048125 : Blo 2031435 3048125 := bbase (se 3 (by rfl) ⟨571523, by rfl⟩ : syracuseStep 3048125 = 1143047) (by norm_num)
theorem B2032083 : Blo 2031435 2032083 := bstep (se 1 (by rfl) ⟨1524062, by rfl⟩ : syracuseStep 2032083 = 3048125) B3048125
theorem B4572197 : Blo 2031435 4572197 := bbase (se 4 (by rfl) ⟨428643, by rfl⟩ : syracuseStep 4572197 = 857287) (by norm_num)
theorem B3048131 : Blo 2031435 3048131 := bstep (se 1 (by rfl) ⟨2286098, by rfl⟩ : syracuseStep 3048131 = 4572197) B4572197
theorem B2032087 : Blo 2031435 2032087 := bstep (se 1 (by rfl) ⟨1524065, by rfl⟩ : syracuseStep 2032087 = 3048131) B3048131
theorem B5143733 : Blo 2031435 5143733 := bbase (se 5 (by rfl) ⟨241112, by rfl⟩ : syracuseStep 5143733 = 482225) (by norm_num)
theorem B3429155 : Blo 2031435 3429155 := bstep (se 1 (by rfl) ⟨2571866, by rfl⟩ : syracuseStep 3429155 = 5143733) B5143733
theorem B2286103 : Blo 2031435 2286103 := bstep (se 1 (by rfl) ⟨1714577, by rfl⟩ : syracuseStep 2286103 = 3429155) B3429155
theorem B3048137 : Blo 2031435 3048137 := bstep (se 2 (by rfl) ⟨1143051, by rfl⟩ : syracuseStep 3048137 = 2286103) B2286103
theorem B2032091 : Blo 2031435 2032091 := bstep (se 1 (by rfl) ⟨1524068, by rfl⟩ : syracuseStep 2032091 = 3048137) B3048137
theorem B2441269 : Blo 2031435 2441269 := bbase (se 5 (by rfl) ⟨114434, by rfl⟩ : syracuseStep 2441269 = 228869) (by norm_num)
theorem B13020101 : Blo 2031435 13020101 := bstep (se 4 (by rfl) ⟨1220634, by rfl⟩ : syracuseStep 13020101 = 2441269) B2441269
theorem B8680067 : Blo 2031435 8680067 := bstep (se 1 (by rfl) ⟨6510050, by rfl⟩ : syracuseStep 8680067 = 13020101) B13020101
theorem B5786711 : Blo 2031435 5786711 := bstep (se 1 (by rfl) ⟨4340033, by rfl⟩ : syracuseStep 5786711 = 8680067) B8680067
theorem B3857807 : Blo 2031435 3857807 := bstep (se 1 (by rfl) ⟨2893355, by rfl⟩ : syracuseStep 3857807 = 5786711) B5786711
theorem B10287485 : Blo 2031435 10287485 := bstep (se 3 (by rfl) ⟨1928903, by rfl⟩ : syracuseStep 10287485 = 3857807) B3857807
theorem B6858323 : Blo 2031435 6858323 := bstep (se 1 (by rfl) ⟨5143742, by rfl⟩ : syracuseStep 6858323 = 10287485) B10287485
theorem B4572215 : Blo 2031435 4572215 := bstep (se 1 (by rfl) ⟨3429161, by rfl⟩ : syracuseStep 4572215 = 6858323) B6858323
theorem B3048143 : Blo 2031435 3048143 := bstep (se 1 (by rfl) ⟨2286107, by rfl⟩ : syracuseStep 3048143 = 4572215) B4572215
theorem B2032095 : Blo 2031435 2032095 := bstep (se 1 (by rfl) ⟨1524071, by rfl⟩ : syracuseStep 2032095 = 3048143) B3048143
theorem B3048149 : Blo 2031435 3048149 := bbase (se 7 (by rfl) ⟨35720, by rfl⟩ : syracuseStep 3048149 = 71441) (by norm_num)
theorem B2032099 : Blo 2031435 2032099 := bstep (se 1 (by rfl) ⟨1524074, by rfl⟩ : syracuseStep 2032099 = 3048149) B3048149
theorem B6598901 : Blo 2031435 6598901 := bbase (se 5 (by rfl) ⟨309323, by rfl⟩ : syracuseStep 6598901 = 618647) (by norm_num)
theorem B4399267 : Blo 2031435 4399267 := bstep (se 1 (by rfl) ⟨3299450, by rfl⟩ : syracuseStep 4399267 = 6598901) B6598901
theorem B5865689 : Blo 2031435 5865689 := bstep (se 2 (by rfl) ⟨2199633, by rfl⟩ : syracuseStep 5865689 = 4399267) B4399267
theorem B3910459 : Blo 2031435 3910459 := bstep (se 1 (by rfl) ⟨2932844, by rfl⟩ : syracuseStep 3910459 = 5865689) B5865689
theorem B5213945 : Blo 2031435 5213945 := bstep (se 2 (by rfl) ⟨1955229, by rfl⟩ : syracuseStep 5213945 = 3910459) B3910459
theorem B3475963 : Blo 2031435 3475963 := bstep (se 1 (by rfl) ⟨2606972, by rfl⟩ : syracuseStep 3475963 = 5213945) B5213945
theorem B18538469 : Blo 2031435 18538469 := bstep (se 4 (by rfl) ⟨1737981, by rfl⟩ : syracuseStep 18538469 = 3475963) B3475963
theorem B12358979 : Blo 2031435 12358979 := bstep (se 1 (by rfl) ⟨9269234, by rfl⟩ : syracuseStep 12358979 = 18538469) B18538469
theorem B8239319 : Blo 2031435 8239319 := bstep (se 1 (by rfl) ⟨6179489, by rfl⟩ : syracuseStep 8239319 = 12358979) B12358979
theorem B5492879 : Blo 2031435 5492879 := bstep (se 1 (by rfl) ⟨4119659, by rfl⟩ : syracuseStep 5492879 = 8239319) B8239319
theorem B3661919 : Blo 2031435 3661919 := bstep (se 1 (by rfl) ⟨2746439, by rfl⟩ : syracuseStep 3661919 = 5492879) B5492879
theorem B2441279 : Blo 2031435 2441279 := bstep (se 1 (by rfl) ⟨1830959, by rfl⟩ : syracuseStep 2441279 = 3661919) B3661919
theorem B6510077 : Blo 2031435 6510077 := bstep (se 3 (by rfl) ⟨1220639, by rfl⟩ : syracuseStep 6510077 = 2441279) B2441279
theorem B4340051 : Blo 2031435 4340051 := bstep (se 1 (by rfl) ⟨3255038, by rfl⟩ : syracuseStep 4340051 = 6510077) B6510077
theorem B2893367 : Blo 2031435 2893367 := bstep (se 1 (by rfl) ⟨2170025, by rfl⟩ : syracuseStep 2893367 = 4340051) B4340051
theorem B7715645 : Blo 2031435 7715645 := bstep (se 3 (by rfl) ⟨1446683, by rfl⟩ : syracuseStep 7715645 = 2893367) B2893367
theorem B5143763 : Blo 2031435 5143763 := bstep (se 1 (by rfl) ⟨3857822, by rfl⟩ : syracuseStep 5143763 = 7715645) B7715645
theorem B3429175 : Blo 2031435 3429175 := bstep (se 1 (by rfl) ⟨2571881, by rfl⟩ : syracuseStep 3429175 = 5143763) B5143763
theorem B4572233 : Blo 2031435 4572233 := bstep (se 2 (by rfl) ⟨1714587, by rfl⟩ : syracuseStep 4572233 = 3429175) B3429175
theorem B3048155 : Blo 2031435 3048155 := bstep (se 1 (by rfl) ⟨2286116, by rfl⟩ : syracuseStep 3048155 = 4572233) B4572233
theorem B2032103 : Blo 2031435 2032103 := bstep (se 1 (by rfl) ⟨1524077, by rfl⟩ : syracuseStep 2032103 = 3048155) B3048155
theorem B2286121 : Blo 2031435 2286121 := bbase (se 2 (by rfl) ⟨857295, by rfl⟩ : syracuseStep 2286121 = 1714591) (by norm_num)
theorem B3048161 : Blo 2031435 3048161 := bstep (se 2 (by rfl) ⟨1143060, by rfl⟩ : syracuseStep 3048161 = 2286121) B2286121
theorem B2032107 : Blo 2031435 2032107 := bstep (se 1 (by rfl) ⟨1524080, by rfl⟩ : syracuseStep 2032107 = 3048161) B3048161
theorem B2059837 : Blo 2031435 2059837 := bbase (se 3 (by rfl) ⟨386219, by rfl⟩ : syracuseStep 2059837 = 772439) (by norm_num)
theorem B10985797 : Blo 2031435 10985797 := bstep (se 4 (by rfl) ⟨1029918, by rfl⟩ : syracuseStep 10985797 = 2059837) B2059837
theorem B14647729 : Blo 2031435 14647729 := bstep (se 2 (by rfl) ⟨5492898, by rfl⟩ : syracuseStep 14647729 = 10985797) B10985797
theorem B19530305 : Blo 2031435 19530305 := bstep (se 2 (by rfl) ⟨7323864, by rfl⟩ : syracuseStep 19530305 = 14647729) B14647729
theorem B13020203 : Blo 2031435 13020203 := bstep (se 1 (by rfl) ⟨9765152, by rfl⟩ : syracuseStep 13020203 = 19530305) B19530305
theorem B8680135 : Blo 2031435 8680135 := bstep (se 1 (by rfl) ⟨6510101, by rfl⟩ : syracuseStep 8680135 = 13020203) B13020203
theorem B11573513 : Blo 2031435 11573513 := bstep (se 2 (by rfl) ⟨4340067, by rfl⟩ : syracuseStep 11573513 = 8680135) B8680135
theorem B7715675 : Blo 2031435 7715675 := bstep (se 1 (by rfl) ⟨5786756, by rfl⟩ : syracuseStep 7715675 = 11573513) B11573513
theorem B5143783 : Blo 2031435 5143783 := bstep (se 1 (by rfl) ⟨3857837, by rfl⟩ : syracuseStep 5143783 = 7715675) B7715675
theorem B6858377 : Blo 2031435 6858377 := bstep (se 2 (by rfl) ⟨2571891, by rfl⟩ : syracuseStep 6858377 = 5143783) B5143783
theorem B4572251 : Blo 2031435 4572251 := bstep (se 1 (by rfl) ⟨3429188, by rfl⟩ : syracuseStep 4572251 = 6858377) B6858377
theorem B3048167 : Blo 2031435 3048167 := bstep (se 1 (by rfl) ⟨2286125, by rfl⟩ : syracuseStep 3048167 = 4572251) B4572251
theorem B2032111 : Blo 2031435 2032111 := bstep (se 1 (by rfl) ⟨1524083, by rfl⟩ : syracuseStep 2032111 = 3048167) B3048167
theorem B3048173 : Blo 2031435 3048173 := bbase (se 3 (by rfl) ⟨571532, by rfl⟩ : syracuseStep 3048173 = 1143065) (by norm_num)
theorem B2032115 : Blo 2031435 2032115 := bstep (se 1 (by rfl) ⟨1524086, by rfl⟩ : syracuseStep 2032115 = 3048173) B3048173
theorem B4572269 : Blo 2031435 4572269 := bbase (se 3 (by rfl) ⟨857300, by rfl⟩ : syracuseStep 4572269 = 1714601) (by norm_num)
theorem B3048179 : Blo 2031435 3048179 := bstep (se 1 (by rfl) ⟨2286134, by rfl⟩ : syracuseStep 3048179 = 4572269) B4572269
theorem B2032119 : Blo 2031435 2032119 := bstep (se 1 (by rfl) ⟨1524089, by rfl⟩ : syracuseStep 2032119 = 3048179) B3048179
theorem B3857861 : Blo 2031435 3857861 := bbase (se 4 (by rfl) ⟨361674, by rfl⟩ : syracuseStep 3857861 = 723349) (by norm_num)
theorem B2571907 : Blo 2031435 2571907 := bstep (se 1 (by rfl) ⟨1928930, by rfl⟩ : syracuseStep 2571907 = 3857861) B3857861
theorem B3429209 : Blo 2031435 3429209 := bstep (se 2 (by rfl) ⟨1285953, by rfl⟩ : syracuseStep 3429209 = 2571907) B2571907
theorem B2286139 : Blo 2031435 2286139 := bstep (se 1 (by rfl) ⟨1714604, by rfl⟩ : syracuseStep 2286139 = 3429209) B3429209
theorem B3048185 : Blo 2031435 3048185 := bstep (se 2 (by rfl) ⟨1143069, by rfl⟩ : syracuseStep 3048185 = 2286139) B2286139
theorem B2032123 : Blo 2031435 2032123 := bstep (se 1 (by rfl) ⟨1524092, by rfl⟩ : syracuseStep 2032123 = 3048185) B3048185
theorem B2059853 : Blo 2031435 2059853 := bbase (se 3 (by rfl) ⟨386222, by rfl⟩ : syracuseStep 2059853 = 772445) (by norm_num)
theorem B5492941 : Blo 2031435 5492941 := bstep (se 3 (by rfl) ⟨1029926, by rfl⟩ : syracuseStep 5492941 = 2059853) B2059853
theorem B29295685 : Blo 2031435 29295685 := bstep (se 4 (by rfl) ⟨2746470, by rfl⟩ : syracuseStep 29295685 = 5492941) B5492941
theorem B39060913 : Blo 2031435 39060913 := bstep (se 2 (by rfl) ⟨14647842, by rfl⟩ : syracuseStep 39060913 = 29295685) B29295685
theorem B52081217 : Blo 2031435 52081217 := bstep (se 2 (by rfl) ⟨19530456, by rfl⟩ : syracuseStep 52081217 = 39060913) B39060913
theorem B34720811 : Blo 2031435 34720811 := bstep (se 1 (by rfl) ⟨26040608, by rfl⟩ : syracuseStep 34720811 = 52081217) B52081217
theorem B23147207 : Blo 2031435 23147207 := bstep (se 1 (by rfl) ⟨17360405, by rfl⟩ : syracuseStep 23147207 = 34720811) B34720811
theorem B15431471 : Blo 2031435 15431471 := bstep (se 1 (by rfl) ⟨11573603, by rfl⟩ : syracuseStep 15431471 = 23147207) B23147207
theorem B10287647 : Blo 2031435 10287647 := bstep (se 1 (by rfl) ⟨7715735, by rfl⟩ : syracuseStep 10287647 = 15431471) B15431471
theorem B6858431 : Blo 2031435 6858431 := bstep (se 1 (by rfl) ⟨5143823, by rfl⟩ : syracuseStep 6858431 = 10287647) B10287647
theorem B4572287 : Blo 2031435 4572287 := bstep (se 1 (by rfl) ⟨3429215, by rfl⟩ : syracuseStep 4572287 = 6858431) B6858431
theorem B3048191 : Blo 2031435 3048191 := bstep (se 1 (by rfl) ⟨2286143, by rfl⟩ : syracuseStep 3048191 = 4572287) B4572287
theorem B2032127 : Blo 2031435 2032127 := bstep (se 1 (by rfl) ⟨1524095, by rfl⟩ : syracuseStep 2032127 = 3048191) B3048191
theorem B3048197 : Blo 2031435 3048197 := bbase (se 4 (by rfl) ⟨285768, by rfl⟩ : syracuseStep 3048197 = 571537) (by norm_num)
theorem B2032131 : Blo 2031435 2032131 := bstep (se 1 (by rfl) ⟨1524098, by rfl⟩ : syracuseStep 2032131 = 3048197) B3048197
theorem B3429229 : Blo 2031435 3429229 := bbase (se 3 (by rfl) ⟨642980, by rfl⟩ : syracuseStep 3429229 = 1285961) (by norm_num)
theorem B4572305 : Blo 2031435 4572305 := bstep (se 2 (by rfl) ⟨1714614, by rfl⟩ : syracuseStep 4572305 = 3429229) B3429229
theorem B3048203 : Blo 2031435 3048203 := bstep (se 1 (by rfl) ⟨2286152, by rfl⟩ : syracuseStep 3048203 = 4572305) B4572305
theorem B2032135 : Blo 2031435 2032135 := bstep (se 1 (by rfl) ⟨1524101, by rfl⟩ : syracuseStep 2032135 = 3048203) B3048203
theorem B2286157 : Blo 2031435 2286157 := bbase (se 3 (by rfl) ⟨428654, by rfl⟩ : syracuseStep 2286157 = 857309) (by norm_num)
theorem B3048209 : Blo 2031435 3048209 := bstep (se 2 (by rfl) ⟨1143078, by rfl⟩ : syracuseStep 3048209 = 2286157) B2286157
theorem B2032139 : Blo 2031435 2032139 := bstep (se 1 (by rfl) ⟨1524104, by rfl⟩ : syracuseStep 2032139 = 3048209) B3048209
theorem B6858485 : Blo 2031435 6858485 := bbase (se 5 (by rfl) ⟨321491, by rfl⟩ : syracuseStep 6858485 = 642983) (by norm_num)
theorem B4572323 : Blo 2031435 4572323 := bstep (se 1 (by rfl) ⟨3429242, by rfl⟩ : syracuseStep 4572323 = 6858485) B6858485
theorem B3048215 : Blo 2031435 3048215 := bstep (se 1 (by rfl) ⟨2286161, by rfl⟩ : syracuseStep 3048215 = 4572323) B4572323
theorem B2032143 : Blo 2031435 2032143 := bstep (se 1 (by rfl) ⟨1524107, by rfl⟩ : syracuseStep 2032143 = 3048215) B3048215
theorem B3048221 : Blo 2031435 3048221 := bbase (se 3 (by rfl) ⟨571541, by rfl⟩ : syracuseStep 3048221 = 1143083) (by norm_num)
theorem B2032147 : Blo 2031435 2032147 := bstep (se 1 (by rfl) ⟨1524110, by rfl⟩ : syracuseStep 2032147 = 3048221) B3048221
theorem B4572341 : Blo 2031435 4572341 := bbase (se 5 (by rfl) ⟨214328, by rfl⟩ : syracuseStep 4572341 = 428657) (by norm_num)
theorem B3048227 : Blo 2031435 3048227 := bstep (se 1 (by rfl) ⟨2286170, by rfl⟩ : syracuseStep 3048227 = 4572341) B4572341
theorem B2032151 : Blo 2031435 2032151 := bstep (se 1 (by rfl) ⟨1524113, by rfl⟩ : syracuseStep 2032151 = 3048227) B3048227
theorem B2170081 : Blo 2031435 2170081 := bbase (se 2 (by rfl) ⟨813780, by rfl⟩ : syracuseStep 2170081 = 1627561) (by norm_num)
theorem B11573765 : Blo 2031435 11573765 := bstep (se 4 (by rfl) ⟨1085040, by rfl⟩ : syracuseStep 11573765 = 2170081) B2170081
theorem B7715843 : Blo 2031435 7715843 := bstep (se 1 (by rfl) ⟨5786882, by rfl⟩ : syracuseStep 7715843 = 11573765) B11573765
theorem B5143895 : Blo 2031435 5143895 := bstep (se 1 (by rfl) ⟨3857921, by rfl⟩ : syracuseStep 5143895 = 7715843) B7715843
theorem B3429263 : Blo 2031435 3429263 := bstep (se 1 (by rfl) ⟨2571947, by rfl⟩ : syracuseStep 3429263 = 5143895) B5143895
theorem B2286175 : Blo 2031435 2286175 := bstep (se 1 (by rfl) ⟨1714631, by rfl⟩ : syracuseStep 2286175 = 3429263) B3429263
theorem B3048233 : Blo 2031435 3048233 := bstep (se 2 (by rfl) ⟨1143087, by rfl⟩ : syracuseStep 3048233 = 2286175) B2286175
theorem B2032155 : Blo 2031435 2032155 := bstep (se 1 (by rfl) ⟨1524116, by rfl⟩ : syracuseStep 2032155 = 3048233) B3048233
theorem B2170085 : Blo 2031435 2170085 := bbase (se 4 (by rfl) ⟨203445, by rfl⟩ : syracuseStep 2170085 = 406891) (by norm_num)
theorem B5786893 : Blo 2031435 5786893 := bstep (se 3 (by rfl) ⟨1085042, by rfl⟩ : syracuseStep 5786893 = 2170085) B2170085
theorem B7715857 : Blo 2031435 7715857 := bstep (se 2 (by rfl) ⟨2893446, by rfl⟩ : syracuseStep 7715857 = 5786893) B5786893
theorem B10287809 : Blo 2031435 10287809 := bstep (se 2 (by rfl) ⟨3857928, by rfl⟩ : syracuseStep 10287809 = 7715857) B7715857
theorem B6858539 : Blo 2031435 6858539 := bstep (se 1 (by rfl) ⟨5143904, by rfl⟩ : syracuseStep 6858539 = 10287809) B10287809
theorem B4572359 : Blo 2031435 4572359 := bstep (se 1 (by rfl) ⟨3429269, by rfl⟩ : syracuseStep 4572359 = 6858539) B6858539
theorem B3048239 : Blo 2031435 3048239 := bstep (se 1 (by rfl) ⟨2286179, by rfl⟩ : syracuseStep 3048239 = 4572359) B4572359
theorem B2032159 : Blo 2031435 2032159 := bstep (se 1 (by rfl) ⟨1524119, by rfl⟩ : syracuseStep 2032159 = 3048239) B3048239
theorem B3048245 : Blo 2031435 3048245 := bbase (se 5 (by rfl) ⟨142886, by rfl⟩ : syracuseStep 3048245 = 285773) (by norm_num)
theorem B2032163 : Blo 2031435 2032163 := bstep (se 1 (by rfl) ⟨1524122, by rfl⟩ : syracuseStep 2032163 = 3048245) B3048245
theorem B5143925 : Blo 2031435 5143925 := bbase (se 5 (by rfl) ⟨241121, by rfl⟩ : syracuseStep 5143925 = 482243) (by norm_num)
theorem B3429283 : Blo 2031435 3429283 := bstep (se 1 (by rfl) ⟨2571962, by rfl⟩ : syracuseStep 3429283 = 5143925) B5143925
theorem B4572377 : Blo 2031435 4572377 := bstep (se 2 (by rfl) ⟨1714641, by rfl⟩ : syracuseStep 4572377 = 3429283) B3429283
theorem B3048251 : Blo 2031435 3048251 := bstep (se 1 (by rfl) ⟨2286188, by rfl⟩ : syracuseStep 3048251 = 4572377) B4572377
theorem B2032167 : Blo 2031435 2032167 := bstep (se 1 (by rfl) ⟨1524125, by rfl⟩ : syracuseStep 2032167 = 3048251) B3048251
theorem B2286193 : Blo 2031435 2286193 := bbase (se 2 (by rfl) ⟨857322, by rfl⟩ : syracuseStep 2286193 = 1714645) (by norm_num)
theorem B3048257 : Blo 2031435 3048257 := bstep (se 2 (by rfl) ⟨1143096, by rfl⟩ : syracuseStep 3048257 = 2286193) B2286193
theorem B2032171 : Blo 2031435 2032171 := bstep (se 1 (by rfl) ⟨1524128, by rfl⟩ : syracuseStep 2032171 = 3048257) B3048257
theorem B9765461 : Blo 2031435 9765461 := bbase (se 8 (by rfl) ⟨57219, by rfl⟩ : syracuseStep 9765461 = 114439) (by norm_num)
theorem B6510307 : Blo 2031435 6510307 := bstep (se 1 (by rfl) ⟨4882730, by rfl⟩ : syracuseStep 6510307 = 9765461) B9765461
theorem B8680409 : Blo 2031435 8680409 := bstep (se 2 (by rfl) ⟨3255153, by rfl⟩ : syracuseStep 8680409 = 6510307) B6510307
theorem B5786939 : Blo 2031435 5786939 := bstep (se 1 (by rfl) ⟨4340204, by rfl⟩ : syracuseStep 5786939 = 8680409) B8680409
theorem B3857959 : Blo 2031435 3857959 := bstep (se 1 (by rfl) ⟨2893469, by rfl⟩ : syracuseStep 3857959 = 5786939) B5786939
theorem B5143945 : Blo 2031435 5143945 := bstep (se 2 (by rfl) ⟨1928979, by rfl⟩ : syracuseStep 5143945 = 3857959) B3857959
theorem B6858593 : Blo 2031435 6858593 := bstep (se 2 (by rfl) ⟨2571972, by rfl⟩ : syracuseStep 6858593 = 5143945) B5143945
theorem B4572395 : Blo 2031435 4572395 := bstep (se 1 (by rfl) ⟨3429296, by rfl⟩ : syracuseStep 4572395 = 6858593) B6858593
theorem B3048263 : Blo 2031435 3048263 := bstep (se 1 (by rfl) ⟨2286197, by rfl⟩ : syracuseStep 3048263 = 4572395) B4572395
theorem B2032175 : Blo 2031435 2032175 := bstep (se 1 (by rfl) ⟨1524131, by rfl⟩ : syracuseStep 2032175 = 3048263) B3048263
theorem B3048269 : Blo 2031435 3048269 := bbase (se 3 (by rfl) ⟨571550, by rfl⟩ : syracuseStep 3048269 = 1143101) (by norm_num)
theorem B2032179 : Blo 2031435 2032179 := bstep (se 1 (by rfl) ⟨1524134, by rfl⟩ : syracuseStep 2032179 = 3048269) B3048269
theorem B4572413 : Blo 2031435 4572413 := bbase (se 3 (by rfl) ⟨857327, by rfl⟩ : syracuseStep 4572413 = 1714655) (by norm_num)
theorem B3048275 : Blo 2031435 3048275 := bstep (se 1 (by rfl) ⟨2286206, by rfl⟩ : syracuseStep 3048275 = 4572413) B4572413
theorem B2032183 : Blo 2031435 2032183 := bstep (se 1 (by rfl) ⟨1524137, by rfl⟩ : syracuseStep 2032183 = 3048275) B3048275
theorem B3429317 : Blo 2031435 3429317 := bbase (se 4 (by rfl) ⟨321498, by rfl⟩ : syracuseStep 3429317 = 642997) (by norm_num)
theorem B2286211 : Blo 2031435 2286211 := bstep (se 1 (by rfl) ⟨1714658, by rfl⟩ : syracuseStep 2286211 = 3429317) B3429317
theorem B3048281 : Blo 2031435 3048281 := bstep (se 2 (by rfl) ⟨1143105, by rfl⟩ : syracuseStep 3048281 = 2286211) B2286211
theorem B2032187 : Blo 2031435 2032187 := bstep (se 1 (by rfl) ⟨1524140, by rfl⟩ : syracuseStep 2032187 = 3048281) B3048281
theorem B15431957 : Blo 2031435 15431957 := bbase (se 6 (by rfl) ⟨361686, by rfl⟩ : syracuseStep 15431957 = 723373) (by norm_num)
theorem B10287971 : Blo 2031435 10287971 := bstep (se 1 (by rfl) ⟨7715978, by rfl⟩ : syracuseStep 10287971 = 15431957) B15431957
theorem B6858647 : Blo 2031435 6858647 := bstep (se 1 (by rfl) ⟨5143985, by rfl⟩ : syracuseStep 6858647 = 10287971) B10287971
theorem B4572431 : Blo 2031435 4572431 := bstep (se 1 (by rfl) ⟨3429323, by rfl⟩ : syracuseStep 4572431 = 6858647) B6858647
theorem B3048287 : Blo 2031435 3048287 := bstep (se 1 (by rfl) ⟨2286215, by rfl⟩ : syracuseStep 3048287 = 4572431) B4572431
theorem B2032191 : Blo 2031435 2032191 := bstep (se 1 (by rfl) ⟨1524143, by rfl⟩ : syracuseStep 2032191 = 3048287) B3048287
theorem B3048293 : Blo 2031435 3048293 := bbase (se 4 (by rfl) ⟨285777, by rfl⟩ : syracuseStep 3048293 = 571555) (by norm_num)
theorem B2032195 : Blo 2031435 2032195 := bstep (se 1 (by rfl) ⟨1524146, by rfl⟩ : syracuseStep 2032195 = 3048293) B3048293
theorem B3858005 : Blo 2031435 3858005 := bbase (se 8 (by rfl) ⟨22605, by rfl⟩ : syracuseStep 3858005 = 45211) (by norm_num)
theorem B2572003 : Blo 2031435 2572003 := bstep (se 1 (by rfl) ⟨1929002, by rfl⟩ : syracuseStep 2572003 = 3858005) B3858005
theorem B3429337 : Blo 2031435 3429337 := bstep (se 2 (by rfl) ⟨1286001, by rfl⟩ : syracuseStep 3429337 = 2572003) B2572003
theorem B4572449 : Blo 2031435 4572449 := bstep (se 2 (by rfl) ⟨1714668, by rfl⟩ : syracuseStep 4572449 = 3429337) B3429337
theorem B3048299 : Blo 2031435 3048299 := bstep (se 1 (by rfl) ⟨2286224, by rfl⟩ : syracuseStep 3048299 = 4572449) B4572449
theorem B2032199 : Blo 2031435 2032199 := bstep (se 1 (by rfl) ⟨1524149, by rfl⟩ : syracuseStep 2032199 = 3048299) B3048299
theorem B2286229 : Blo 2031435 2286229 := bbase (se 6 (by rfl) ⟨53583, by rfl⟩ : syracuseStep 2286229 = 107167) (by norm_num)
theorem B3048305 : Blo 2031435 3048305 := bstep (se 2 (by rfl) ⟨1143114, by rfl⟩ : syracuseStep 3048305 = 2286229) B2286229
theorem B2032203 : Blo 2031435 2032203 := bstep (se 1 (by rfl) ⟨1524152, by rfl⟩ : syracuseStep 2032203 = 3048305) B3048305
theorem B2572013 : Blo 2031435 2572013 := bbase (se 3 (by rfl) ⟨482252, by rfl⟩ : syracuseStep 2572013 = 964505) (by norm_num)
theorem B6858701 : Blo 2031435 6858701 := bstep (se 3 (by rfl) ⟨1286006, by rfl⟩ : syracuseStep 6858701 = 2572013) B2572013
theorem B4572467 : Blo 2031435 4572467 := bstep (se 1 (by rfl) ⟨3429350, by rfl⟩ : syracuseStep 4572467 = 6858701) B6858701
theorem B3048311 : Blo 2031435 3048311 := bstep (se 1 (by rfl) ⟨2286233, by rfl⟩ : syracuseStep 3048311 = 4572467) B4572467
theorem B2032207 : Blo 2031435 2032207 := bstep (se 1 (by rfl) ⟨1524155, by rfl⟩ : syracuseStep 2032207 = 3048311) B3048311
theorem B3048317 : Blo 2031435 3048317 := bbase (se 3 (by rfl) ⟨571559, by rfl⟩ : syracuseStep 3048317 = 1143119) (by norm_num)
theorem B2032211 : Blo 2031435 2032211 := bstep (se 1 (by rfl) ⟨1524158, by rfl⟩ : syracuseStep 2032211 = 3048317) B3048317
theorem B4572485 : Blo 2031435 4572485 := bbase (se 4 (by rfl) ⟨428670, by rfl⟩ : syracuseStep 4572485 = 857341) (by norm_num)
theorem B3048323 : Blo 2031435 3048323 := bstep (se 1 (by rfl) ⟨2286242, by rfl⟩ : syracuseStep 3048323 = 4572485) B4572485
theorem B2032215 : Blo 2031435 2032215 := bstep (se 1 (by rfl) ⟨1524161, by rfl⟩ : syracuseStep 2032215 = 3048323) B3048323
theorem B4882837 : Blo 2031435 4882837 := bbase (se 6 (by rfl) ⟨114441, by rfl⟩ : syracuseStep 4882837 = 228883) (by norm_num)
theorem B6510449 : Blo 2031435 6510449 := bstep (se 2 (by rfl) ⟨2441418, by rfl⟩ : syracuseStep 6510449 = 4882837) B4882837
theorem B4340299 : Blo 2031435 4340299 := bstep (se 1 (by rfl) ⟨3255224, by rfl⟩ : syracuseStep 4340299 = 6510449) B6510449
theorem B5787065 : Blo 2031435 5787065 := bstep (se 2 (by rfl) ⟨2170149, by rfl⟩ : syracuseStep 5787065 = 4340299) B4340299
theorem B3858043 : Blo 2031435 3858043 := bstep (se 1 (by rfl) ⟨2893532, by rfl⟩ : syracuseStep 3858043 = 5787065) B5787065
theorem B5144057 : Blo 2031435 5144057 := bstep (se 2 (by rfl) ⟨1929021, by rfl⟩ : syracuseStep 5144057 = 3858043) B3858043
theorem B3429371 : Blo 2031435 3429371 := bstep (se 1 (by rfl) ⟨2572028, by rfl⟩ : syracuseStep 3429371 = 5144057) B5144057
theorem B2286247 : Blo 2031435 2286247 := bstep (se 1 (by rfl) ⟨1714685, by rfl⟩ : syracuseStep 2286247 = 3429371) B3429371
theorem B3048329 : Blo 2031435 3048329 := bstep (se 2 (by rfl) ⟨1143123, by rfl⟩ : syracuseStep 3048329 = 2286247) B2286247
theorem B2032219 : Blo 2031435 2032219 := bstep (se 1 (by rfl) ⟨1524164, by rfl⟩ : syracuseStep 2032219 = 3048329) B3048329
theorem B10288133 : Blo 2031435 10288133 := bbase (se 4 (by rfl) ⟨964512, by rfl⟩ : syracuseStep 10288133 = 1929025) (by norm_num)
theorem B6858755 : Blo 2031435 6858755 := bstep (se 1 (by rfl) ⟨5144066, by rfl⟩ : syracuseStep 6858755 = 10288133) B10288133
theorem B4572503 : Blo 2031435 4572503 := bstep (se 1 (by rfl) ⟨3429377, by rfl⟩ : syracuseStep 4572503 = 6858755) B6858755
theorem B3048335 : Blo 2031435 3048335 := bstep (se 1 (by rfl) ⟨2286251, by rfl⟩ : syracuseStep 3048335 = 4572503) B4572503
theorem B2032223 : Blo 2031435 2032223 := bstep (se 1 (by rfl) ⟨1524167, by rfl⟩ : syracuseStep 2032223 = 3048335) B3048335
theorem B3048341 : Blo 2031435 3048341 := bbase (se 6 (by rfl) ⟨71445, by rfl⟩ : syracuseStep 3048341 = 142891) (by norm_num)
theorem B2032227 : Blo 2031435 2032227 := bstep (se 1 (by rfl) ⟨1524170, by rfl⟩ : syracuseStep 2032227 = 3048341) B3048341
theorem B11574197 : Blo 2031435 11574197 := bbase (se 5 (by rfl) ⟨542540, by rfl⟩ : syracuseStep 11574197 = 1085081) (by norm_num)
theorem B7716131 : Blo 2031435 7716131 := bstep (se 1 (by rfl) ⟨5787098, by rfl⟩ : syracuseStep 7716131 = 11574197) B11574197
theorem B5144087 : Blo 2031435 5144087 := bstep (se 1 (by rfl) ⟨3858065, by rfl⟩ : syracuseStep 5144087 = 7716131) B7716131
theorem B3429391 : Blo 2031435 3429391 := bstep (se 1 (by rfl) ⟨2572043, by rfl⟩ : syracuseStep 3429391 = 5144087) B5144087
theorem B4572521 : Blo 2031435 4572521 := bstep (se 2 (by rfl) ⟨1714695, by rfl⟩ : syracuseStep 4572521 = 3429391) B3429391
theorem B3048347 : Blo 2031435 3048347 := bstep (se 1 (by rfl) ⟨2286260, by rfl⟩ : syracuseStep 3048347 = 4572521) B4572521
theorem B2032231 : Blo 2031435 2032231 := bstep (se 1 (by rfl) ⟨1524173, by rfl⟩ : syracuseStep 2032231 = 3048347) B3048347
theorem B2286265 : Blo 2031435 2286265 := bbase (se 2 (by rfl) ⟨857349, by rfl⟩ : syracuseStep 2286265 = 1714699) (by norm_num)
theorem B3048353 : Blo 2031435 3048353 := bstep (se 2 (by rfl) ⟨1143132, by rfl⟩ : syracuseStep 3048353 = 2286265) B2286265
theorem B2032235 : Blo 2031435 2032235 := bstep (se 1 (by rfl) ⟨1524176, by rfl⟩ : syracuseStep 2032235 = 3048353) B3048353
theorem B4340341 : Blo 2031435 4340341 := bbase (se 5 (by rfl) ⟨203453, by rfl⟩ : syracuseStep 4340341 = 406907) (by norm_num)
theorem B5787121 : Blo 2031435 5787121 := bstep (se 2 (by rfl) ⟨2170170, by rfl⟩ : syracuseStep 5787121 = 4340341) B4340341
theorem B7716161 : Blo 2031435 7716161 := bstep (se 2 (by rfl) ⟨2893560, by rfl⟩ : syracuseStep 7716161 = 5787121) B5787121
theorem B5144107 : Blo 2031435 5144107 := bstep (se 1 (by rfl) ⟨3858080, by rfl⟩ : syracuseStep 5144107 = 7716161) B7716161
theorem B6858809 : Blo 2031435 6858809 := bstep (se 2 (by rfl) ⟨2572053, by rfl⟩ : syracuseStep 6858809 = 5144107) B5144107
theorem B4572539 : Blo 2031435 4572539 := bstep (se 1 (by rfl) ⟨3429404, by rfl⟩ : syracuseStep 4572539 = 6858809) B6858809
theorem B3048359 : Blo 2031435 3048359 := bstep (se 1 (by rfl) ⟨2286269, by rfl⟩ : syracuseStep 3048359 = 4572539) B4572539
theorem B2032239 : Blo 2031435 2032239 := bstep (se 1 (by rfl) ⟨1524179, by rfl⟩ : syracuseStep 2032239 = 3048359) B3048359
theorem B3048365 : Blo 2031435 3048365 := bbase (se 3 (by rfl) ⟨571568, by rfl⟩ : syracuseStep 3048365 = 1143137) (by norm_num)
theorem B2032243 : Blo 2031435 2032243 := bstep (se 1 (by rfl) ⟨1524182, by rfl⟩ : syracuseStep 2032243 = 3048365) B3048365
theorem B4572557 : Blo 2031435 4572557 := bbase (se 3 (by rfl) ⟨857354, by rfl⟩ : syracuseStep 4572557 = 1714709) (by norm_num)
theorem B3048371 : Blo 2031435 3048371 := bstep (se 1 (by rfl) ⟨2286278, by rfl⟩ : syracuseStep 3048371 = 4572557) B4572557
theorem B2032247 : Blo 2031435 2032247 := bstep (se 1 (by rfl) ⟨1524185, by rfl⟩ : syracuseStep 2032247 = 3048371) B3048371
theorem B2572069 : Blo 2031435 2572069 := bbase (se 4 (by rfl) ⟨241131, by rfl⟩ : syracuseStep 2572069 = 482263) (by norm_num)
theorem B3429425 : Blo 2031435 3429425 := bstep (se 2 (by rfl) ⟨1286034, by rfl⟩ : syracuseStep 3429425 = 2572069) B2572069
theorem B2286283 : Blo 2031435 2286283 := bstep (se 1 (by rfl) ⟨1714712, by rfl⟩ : syracuseStep 2286283 = 3429425) B3429425
theorem B3048377 : Blo 2031435 3048377 := bstep (se 2 (by rfl) ⟨1143141, by rfl⟩ : syracuseStep 3048377 = 2286283) B2286283
theorem B2032251 : Blo 2031435 2032251 := bstep (se 1 (by rfl) ⟨1524188, by rfl⟩ : syracuseStep 2032251 = 3048377) B3048377
theorem B19798165 : Blo 2031435 19798165 := bbase (se 6 (by rfl) ⟨464019, by rfl⟩ : syracuseStep 19798165 = 928039) (by norm_num)
theorem B105590213 : Blo 2031435 105590213 := bstep (se 4 (by rfl) ⟨9899082, by rfl⟩ : syracuseStep 105590213 = 19798165) B19798165
theorem B70393475 : Blo 2031435 70393475 := bstep (se 1 (by rfl) ⟨52795106, by rfl⟩ : syracuseStep 70393475 = 105590213) B105590213
theorem B46928983 : Blo 2031435 46928983 := bstep (se 1 (by rfl) ⟨35196737, by rfl⟩ : syracuseStep 46928983 = 70393475) B70393475
theorem B62571977 : Blo 2031435 62571977 := bstep (se 2 (by rfl) ⟨23464491, by rfl⟩ : syracuseStep 62571977 = 46928983) B46928983
theorem B41714651 : Blo 2031435 41714651 := bstep (se 1 (by rfl) ⟨31285988, by rfl⟩ : syracuseStep 41714651 = 62571977) B62571977
theorem B27809767 : Blo 2031435 27809767 := bstep (se 1 (by rfl) ⟨20857325, by rfl⟩ : syracuseStep 27809767 = 41714651) B41714651
theorem B37079689 : Blo 2031435 37079689 := bstep (se 2 (by rfl) ⟨13904883, by rfl⟩ : syracuseStep 37079689 = 27809767) B27809767
theorem B49439585 : Blo 2031435 49439585 := bstep (se 2 (by rfl) ⟨18539844, by rfl⟩ : syracuseStep 49439585 = 37079689) B37079689
theorem B32959723 : Blo 2031435 32959723 := bstep (se 1 (by rfl) ⟨24719792, by rfl⟩ : syracuseStep 32959723 = 49439585) B49439585
theorem B43946297 : Blo 2031435 43946297 := bstep (se 2 (by rfl) ⟨16479861, by rfl⟩ : syracuseStep 43946297 = 32959723) B32959723
theorem B29297531 : Blo 2031435 29297531 := bstep (se 1 (by rfl) ⟨21973148, by rfl⟩ : syracuseStep 29297531 = 43946297) B43946297
theorem B19531687 : Blo 2031435 19531687 := bstep (se 1 (by rfl) ⟨14648765, by rfl⟩ : syracuseStep 19531687 = 29297531) B29297531
theorem B26042249 : Blo 2031435 26042249 := bstep (se 2 (by rfl) ⟨9765843, by rfl⟩ : syracuseStep 26042249 = 19531687) B19531687
theorem B17361499 : Blo 2031435 17361499 := bstep (se 1 (by rfl) ⟨13021124, by rfl⟩ : syracuseStep 17361499 = 26042249) B26042249
theorem B23148665 : Blo 2031435 23148665 := bstep (se 2 (by rfl) ⟨8680749, by rfl⟩ : syracuseStep 23148665 = 17361499) B17361499
theorem B15432443 : Blo 2031435 15432443 := bstep (se 1 (by rfl) ⟨11574332, by rfl⟩ : syracuseStep 15432443 = 23148665) B23148665
theorem B10288295 : Blo 2031435 10288295 := bstep (se 1 (by rfl) ⟨7716221, by rfl⟩ : syracuseStep 10288295 = 15432443) B15432443
theorem B6858863 : Blo 2031435 6858863 := bstep (se 1 (by rfl) ⟨5144147, by rfl⟩ : syracuseStep 6858863 = 10288295) B10288295
theorem B4572575 : Blo 2031435 4572575 := bstep (se 1 (by rfl) ⟨3429431, by rfl⟩ : syracuseStep 4572575 = 6858863) B6858863
theorem B3048383 : Blo 2031435 3048383 := bstep (se 1 (by rfl) ⟨2286287, by rfl⟩ : syracuseStep 3048383 = 4572575) B4572575
theorem B2032255 : Blo 2031435 2032255 := bstep (se 1 (by rfl) ⟨1524191, by rfl⟩ : syracuseStep 2032255 = 3048383) B3048383
theorem B3048389 : Blo 2031435 3048389 := bbase (se 4 (by rfl) ⟨285786, by rfl⟩ : syracuseStep 3048389 = 571573) (by norm_num)
theorem B2032259 : Blo 2031435 2032259 := bstep (se 1 (by rfl) ⟨1524194, by rfl⟩ : syracuseStep 2032259 = 3048389) B3048389
theorem B3429445 : Blo 2031435 3429445 := bbase (se 4 (by rfl) ⟨321510, by rfl⟩ : syracuseStep 3429445 = 643021) (by norm_num)
theorem B4572593 : Blo 2031435 4572593 := bstep (se 2 (by rfl) ⟨1714722, by rfl⟩ : syracuseStep 4572593 = 3429445) B3429445
theorem B3048395 : Blo 2031435 3048395 := bstep (se 1 (by rfl) ⟨2286296, by rfl⟩ : syracuseStep 3048395 = 4572593) B4572593
theorem B2032263 : Blo 2031435 2032263 := bstep (se 1 (by rfl) ⟨1524197, by rfl⟩ : syracuseStep 2032263 = 3048395) B3048395
theorem B2286301 : Blo 2031435 2286301 := bbase (se 3 (by rfl) ⟨428681, by rfl⟩ : syracuseStep 2286301 = 857363) (by norm_num)
theorem B3048401 : Blo 2031435 3048401 := bstep (se 2 (by rfl) ⟨1143150, by rfl⟩ : syracuseStep 3048401 = 2286301) B2286301
theorem B2032267 : Blo 2031435 2032267 := bstep (se 1 (by rfl) ⟨1524200, by rfl⟩ : syracuseStep 2032267 = 3048401) B3048401
theorem B6858917 : Blo 2031435 6858917 := bbase (se 4 (by rfl) ⟨643023, by rfl⟩ : syracuseStep 6858917 = 1286047) (by norm_num)
theorem B4572611 : Blo 2031435 4572611 := bstep (se 1 (by rfl) ⟨3429458, by rfl⟩ : syracuseStep 4572611 = 6858917) B6858917
theorem B3048407 : Blo 2031435 3048407 := bstep (se 1 (by rfl) ⟨2286305, by rfl⟩ : syracuseStep 3048407 = 4572611) B4572611
theorem B2032271 : Blo 2031435 2032271 := bstep (se 1 (by rfl) ⟨1524203, by rfl⟩ : syracuseStep 2032271 = 3048407) B3048407
theorem B3048413 : Blo 2031435 3048413 := bbase (se 3 (by rfl) ⟨571577, by rfl⟩ : syracuseStep 3048413 = 1143155) (by norm_num)
theorem B2032275 : Blo 2031435 2032275 := bstep (se 1 (by rfl) ⟨1524206, by rfl⟩ : syracuseStep 2032275 = 3048413) B3048413
theorem B4572629 : Blo 2031435 4572629 := bbase (se 7 (by rfl) ⟨53585, by rfl⟩ : syracuseStep 4572629 = 107171) (by norm_num)
theorem B3048419 : Blo 2031435 3048419 := bstep (se 1 (by rfl) ⟨2286314, by rfl⟩ : syracuseStep 3048419 = 4572629) B4572629
theorem B2032279 : Blo 2031435 2032279 := bstep (se 1 (by rfl) ⟨1524209, by rfl⟩ : syracuseStep 2032279 = 3048419) B3048419
theorem B9270053 : Blo 2031435 9270053 := bbase (se 4 (by rfl) ⟨869067, by rfl⟩ : syracuseStep 9270053 = 1738135) (by norm_num)
theorem B6180035 : Blo 2031435 6180035 := bstep (se 1 (by rfl) ⟨4635026, by rfl⟩ : syracuseStep 6180035 = 9270053) B9270053
theorem B16480093 : Blo 2031435 16480093 := bstep (se 3 (by rfl) ⟨3090017, by rfl⟩ : syracuseStep 16480093 = 6180035) B6180035
theorem B21973457 : Blo 2031435 21973457 := bstep (se 2 (by rfl) ⟨8240046, by rfl⟩ : syracuseStep 21973457 = 16480093) B16480093
theorem B14648971 : Blo 2031435 14648971 := bstep (se 1 (by rfl) ⟨10986728, by rfl⟩ : syracuseStep 14648971 = 21973457) B21973457
theorem B19531961 : Blo 2031435 19531961 := bstep (se 2 (by rfl) ⟨7324485, by rfl⟩ : syracuseStep 19531961 = 14648971) B14648971
theorem B13021307 : Blo 2031435 13021307 := bstep (se 1 (by rfl) ⟨9765980, by rfl⟩ : syracuseStep 13021307 = 19531961) B19531961
theorem B8680871 : Blo 2031435 8680871 := bstep (se 1 (by rfl) ⟨6510653, by rfl⟩ : syracuseStep 8680871 = 13021307) B13021307
theorem B5787247 : Blo 2031435 5787247 := bstep (se 1 (by rfl) ⟨4340435, by rfl⟩ : syracuseStep 5787247 = 8680871) B8680871
theorem B7716329 : Blo 2031435 7716329 := bstep (se 2 (by rfl) ⟨2893623, by rfl⟩ : syracuseStep 7716329 = 5787247) B5787247
theorem B5144219 : Blo 2031435 5144219 := bstep (se 1 (by rfl) ⟨3858164, by rfl⟩ : syracuseStep 5144219 = 7716329) B7716329
theorem B3429479 : Blo 2031435 3429479 := bstep (se 1 (by rfl) ⟨2572109, by rfl⟩ : syracuseStep 3429479 = 5144219) B5144219
theorem B2286319 : Blo 2031435 2286319 := bstep (se 1 (by rfl) ⟨1714739, by rfl⟩ : syracuseStep 2286319 = 3429479) B3429479
theorem B3048425 : Blo 2031435 3048425 := bstep (se 2 (by rfl) ⟨1143159, by rfl⟩ : syracuseStep 3048425 = 2286319) B2286319
theorem B2032283 : Blo 2031435 2032283 := bstep (se 1 (by rfl) ⟨1524212, by rfl⟩ : syracuseStep 2032283 = 3048425) B3048425
theorem B3262141 : Blo 2031435 3262141 := bbase (se 3 (by rfl) ⟨611651, by rfl⟩ : syracuseStep 3262141 = 1223303) (by norm_num)
theorem B4349521 : Blo 2031435 4349521 := bstep (se 2 (by rfl) ⟨1631070, by rfl⟩ : syracuseStep 4349521 = 3262141) B3262141
theorem B5799361 : Blo 2031435 5799361 := bstep (se 2 (by rfl) ⟨2174760, by rfl⟩ : syracuseStep 5799361 = 4349521) B4349521
theorem B7732481 : Blo 2031435 7732481 := bstep (se 2 (by rfl) ⟨2899680, by rfl⟩ : syracuseStep 7732481 = 5799361) B5799361
theorem B20619949 : Blo 2031435 20619949 := bstep (se 3 (by rfl) ⟨3866240, by rfl⟩ : syracuseStep 20619949 = 7732481) B7732481
theorem B27493265 : Blo 2031435 27493265 := bstep (se 2 (by rfl) ⟨10309974, by rfl⟩ : syracuseStep 27493265 = 20619949) B20619949
theorem B18328843 : Blo 2031435 18328843 := bstep (se 1 (by rfl) ⟨13746632, by rfl⟩ : syracuseStep 18328843 = 27493265) B27493265
theorem B24438457 : Blo 2031435 24438457 := bstep (se 2 (by rfl) ⟨9164421, by rfl⟩ : syracuseStep 24438457 = 18328843) B18328843
theorem B32584609 : Blo 2031435 32584609 := bstep (se 2 (by rfl) ⟨12219228, by rfl⟩ : syracuseStep 32584609 = 24438457) B24438457
theorem B43446145 : Blo 2031435 43446145 := bstep (se 2 (by rfl) ⟨16292304, by rfl⟩ : syracuseStep 43446145 = 32584609) B32584609
theorem B57928193 : Blo 2031435 57928193 := bstep (se 2 (by rfl) ⟨21723072, by rfl⟩ : syracuseStep 57928193 = 43446145) B43446145
theorem B38618795 : Blo 2031435 38618795 := bstep (se 1 (by rfl) ⟨28964096, by rfl⟩ : syracuseStep 38618795 = 57928193) B57928193
theorem B25745863 : Blo 2031435 25745863 := bstep (se 1 (by rfl) ⟨19309397, by rfl⟩ : syracuseStep 25745863 = 38618795) B38618795
theorem B34327817 : Blo 2031435 34327817 := bstep (se 2 (by rfl) ⟨12872931, by rfl⟩ : syracuseStep 34327817 = 25745863) B25745863
theorem B22885211 : Blo 2031435 22885211 := bstep (se 1 (by rfl) ⟨17163908, by rfl⟩ : syracuseStep 22885211 = 34327817) B34327817
theorem B61027229 : Blo 2031435 61027229 := bstep (se 3 (by rfl) ⟨11442605, by rfl⟩ : syracuseStep 61027229 = 22885211) B22885211
theorem B162739277 : Blo 2031435 162739277 := bstep (se 3 (by rfl) ⟨30513614, by rfl⟩ : syracuseStep 162739277 = 61027229) B61027229
theorem B108492851 : Blo 2031435 108492851 := bstep (se 1 (by rfl) ⟨81369638, by rfl⟩ : syracuseStep 108492851 = 162739277) B162739277
theorem B72328567 : Blo 2031435 72328567 := bstep (se 1 (by rfl) ⟨54246425, by rfl⟩ : syracuseStep 72328567 = 108492851) B108492851
theorem B96438089 : Blo 2031435 96438089 := bstep (se 2 (by rfl) ⟨36164283, by rfl⟩ : syracuseStep 96438089 = 72328567) B72328567
theorem B64292059 : Blo 2031435 64292059 := bstep (se 1 (by rfl) ⟨48219044, by rfl⟩ : syracuseStep 64292059 = 96438089) B96438089
theorem B342890981 : Blo 2031435 342890981 := bstep (se 4 (by rfl) ⟨32146029, by rfl⟩ : syracuseStep 342890981 = 64292059) B64292059
theorem B228593987 : Blo 2031435 228593987 := bstep (se 1 (by rfl) ⟨171445490, by rfl⟩ : syracuseStep 228593987 = 342890981) B342890981
theorem B152395991 : Blo 2031435 152395991 := bstep (se 1 (by rfl) ⟨114296993, by rfl⟩ : syracuseStep 152395991 = 228593987) B228593987
theorem B101597327 : Blo 2031435 101597327 := bstep (se 1 (by rfl) ⟨76197995, by rfl⟩ : syracuseStep 101597327 = 152395991) B152395991
theorem B67731551 : Blo 2031435 67731551 := bstep (se 1 (by rfl) ⟨50798663, by rfl⟩ : syracuseStep 67731551 = 101597327) B101597327
theorem B45154367 : Blo 2031435 45154367 := bstep (se 1 (by rfl) ⟨33865775, by rfl⟩ : syracuseStep 45154367 = 67731551) B67731551
theorem B30102911 : Blo 2031435 30102911 := bstep (se 1 (by rfl) ⟨22577183, by rfl⟩ : syracuseStep 30102911 = 45154367) B45154367
theorem B20068607 : Blo 2031435 20068607 := bstep (se 1 (by rfl) ⟨15051455, by rfl⟩ : syracuseStep 20068607 = 30102911) B30102911
theorem B53516285 : Blo 2031435 53516285 := bstep (se 3 (by rfl) ⟨10034303, by rfl⟩ : syracuseStep 53516285 = 20068607) B20068607
theorem B35677523 : Blo 2031435 35677523 := bstep (se 1 (by rfl) ⟨26758142, by rfl⟩ : syracuseStep 35677523 = 53516285) B53516285
theorem B23785015 : Blo 2031435 23785015 := bstep (se 1 (by rfl) ⟨17838761, by rfl⟩ : syracuseStep 23785015 = 35677523) B35677523
theorem B31713353 : Blo 2031435 31713353 := bstep (se 2 (by rfl) ⟨11892507, by rfl⟩ : syracuseStep 31713353 = 23785015) B23785015
theorem B21142235 : Blo 2031435 21142235 := bstep (se 1 (by rfl) ⟨15856676, by rfl⟩ : syracuseStep 21142235 = 31713353) B31713353
theorem B14094823 : Blo 2031435 14094823 := bstep (se 1 (by rfl) ⟨10571117, by rfl⟩ : syracuseStep 14094823 = 21142235) B21142235
theorem B18793097 : Blo 2031435 18793097 := bstep (se 2 (by rfl) ⟨7047411, by rfl⟩ : syracuseStep 18793097 = 14094823) B14094823
theorem B12528731 : Blo 2031435 12528731 := bstep (se 1 (by rfl) ⟨9396548, by rfl⟩ : syracuseStep 12528731 = 18793097) B18793097
theorem B8352487 : Blo 2031435 8352487 := bstep (se 1 (by rfl) ⟨6264365, by rfl⟩ : syracuseStep 8352487 = 12528731) B12528731
theorem B11136649 : Blo 2031435 11136649 := bstep (se 2 (by rfl) ⟨4176243, by rfl⟩ : syracuseStep 11136649 = 8352487) B8352487
theorem B14848865 : Blo 2031435 14848865 := bstep (se 2 (by rfl) ⟨5568324, by rfl⟩ : syracuseStep 14848865 = 11136649) B11136649
theorem B9899243 : Blo 2031435 9899243 := bstep (se 1 (by rfl) ⟨7424432, by rfl⟩ : syracuseStep 9899243 = 14848865) B14848865
theorem B6599495 : Blo 2031435 6599495 := bstep (se 1 (by rfl) ⟨4949621, by rfl⟩ : syracuseStep 6599495 = 9899243) B9899243
theorem B17598653 : Blo 2031435 17598653 := bstep (se 3 (by rfl) ⟨3299747, by rfl⟩ : syracuseStep 17598653 = 6599495) B6599495
theorem B11732435 : Blo 2031435 11732435 := bstep (se 1 (by rfl) ⟨8799326, by rfl⟩ : syracuseStep 11732435 = 17598653) B17598653
theorem B7821623 : Blo 2031435 7821623 := bstep (se 1 (by rfl) ⟨5866217, by rfl⟩ : syracuseStep 7821623 = 11732435) B11732435
theorem B20857661 : Blo 2031435 20857661 := bstep (se 3 (by rfl) ⟨3910811, by rfl⟩ : syracuseStep 20857661 = 7821623) B7821623
theorem B13905107 : Blo 2031435 13905107 := bstep (se 1 (by rfl) ⟨10428830, by rfl⟩ : syracuseStep 13905107 = 20857661) B20857661
theorem B9270071 : Blo 2031435 9270071 := bstep (se 1 (by rfl) ⟨6952553, by rfl⟩ : syracuseStep 9270071 = 13905107) B13905107
theorem B6180047 : Blo 2031435 6180047 := bstep (se 1 (by rfl) ⟨4635035, by rfl⟩ : syracuseStep 6180047 = 9270071) B9270071
theorem B4120031 : Blo 2031435 4120031 := bstep (se 1 (by rfl) ⟨3090023, by rfl⟩ : syracuseStep 4120031 = 6180047) B6180047
theorem B10986749 : Blo 2031435 10986749 := bstep (se 3 (by rfl) ⟨2060015, by rfl⟩ : syracuseStep 10986749 = 4120031) B4120031
theorem B7324499 : Blo 2031435 7324499 := bstep (se 1 (by rfl) ⟨5493374, by rfl⟩ : syracuseStep 7324499 = 10986749) B10986749
theorem B4882999 : Blo 2031435 4882999 := bstep (se 1 (by rfl) ⟨3662249, by rfl⟩ : syracuseStep 4882999 = 7324499) B7324499
theorem B6510665 : Blo 2031435 6510665 := bstep (se 2 (by rfl) ⟨2441499, by rfl⟩ : syracuseStep 6510665 = 4882999) B4882999
theorem B17361773 : Blo 2031435 17361773 := bstep (se 3 (by rfl) ⟨3255332, by rfl⟩ : syracuseStep 17361773 = 6510665) B6510665
theorem B11574515 : Blo 2031435 11574515 := bstep (se 1 (by rfl) ⟨8680886, by rfl⟩ : syracuseStep 11574515 = 17361773) B17361773
theorem B7716343 : Blo 2031435 7716343 := bstep (se 1 (by rfl) ⟨5787257, by rfl⟩ : syracuseStep 7716343 = 11574515) B11574515
theorem B10288457 : Blo 2031435 10288457 := bstep (se 2 (by rfl) ⟨3858171, by rfl⟩ : syracuseStep 10288457 = 7716343) B7716343
theorem B6858971 : Blo 2031435 6858971 := bstep (se 1 (by rfl) ⟨5144228, by rfl⟩ : syracuseStep 6858971 = 10288457) B10288457
theorem B4572647 : Blo 2031435 4572647 := bstep (se 1 (by rfl) ⟨3429485, by rfl⟩ : syracuseStep 4572647 = 6858971) B6858971
theorem B3048431 : Blo 2031435 3048431 := bstep (se 1 (by rfl) ⟨2286323, by rfl⟩ : syracuseStep 3048431 = 4572647) B4572647
theorem B2032287 : Blo 2031435 2032287 := bstep (se 1 (by rfl) ⟨1524215, by rfl⟩ : syracuseStep 2032287 = 3048431) B3048431
theorem B3048437 : Blo 2031435 3048437 := bbase (se 5 (by rfl) ⟨142895, by rfl⟩ : syracuseStep 3048437 = 285791) (by norm_num)
theorem B2032291 : Blo 2031435 2032291 := bstep (se 1 (by rfl) ⟨1524218, by rfl⟩ : syracuseStep 2032291 = 3048437) B3048437
theorem B4340461 : Blo 2031435 4340461 := bbase (se 3 (by rfl) ⟨813836, by rfl⟩ : syracuseStep 4340461 = 1627673) (by norm_num)
theorem B5787281 : Blo 2031435 5787281 := bstep (se 2 (by rfl) ⟨2170230, by rfl⟩ : syracuseStep 5787281 = 4340461) B4340461
theorem B3858187 : Blo 2031435 3858187 := bstep (se 1 (by rfl) ⟨2893640, by rfl⟩ : syracuseStep 3858187 = 5787281) B5787281
theorem B5144249 : Blo 2031435 5144249 := bstep (se 2 (by rfl) ⟨1929093, by rfl⟩ : syracuseStep 5144249 = 3858187) B3858187
theorem B3429499 : Blo 2031435 3429499 := bstep (se 1 (by rfl) ⟨2572124, by rfl⟩ : syracuseStep 3429499 = 5144249) B5144249
theorem B4572665 : Blo 2031435 4572665 := bstep (se 2 (by rfl) ⟨1714749, by rfl⟩ : syracuseStep 4572665 = 3429499) B3429499
theorem B3048443 : Blo 2031435 3048443 := bstep (se 1 (by rfl) ⟨2286332, by rfl⟩ : syracuseStep 3048443 = 4572665) B4572665
theorem B2032295 : Blo 2031435 2032295 := bstep (se 1 (by rfl) ⟨1524221, by rfl⟩ : syracuseStep 2032295 = 3048443) B3048443
theorem B2286337 : Blo 2031435 2286337 := bbase (se 2 (by rfl) ⟨857376, by rfl⟩ : syracuseStep 2286337 = 1714753) (by norm_num)
theorem B3048449 : Blo 2031435 3048449 := bstep (se 2 (by rfl) ⟨1143168, by rfl⟩ : syracuseStep 3048449 = 2286337) B2286337
theorem B2032299 : Blo 2031435 2032299 := bstep (se 1 (by rfl) ⟨1524224, by rfl⟩ : syracuseStep 2032299 = 3048449) B3048449
theorem B5144269 : Blo 2031435 5144269 := bbase (se 3 (by rfl) ⟨964550, by rfl⟩ : syracuseStep 5144269 = 1929101) (by norm_num)
theorem B6859025 : Blo 2031435 6859025 := bstep (se 2 (by rfl) ⟨2572134, by rfl⟩ : syracuseStep 6859025 = 5144269) B5144269
theorem B4572683 : Blo 2031435 4572683 := bstep (se 1 (by rfl) ⟨3429512, by rfl⟩ : syracuseStep 4572683 = 6859025) B6859025
theorem B3048455 : Blo 2031435 3048455 := bstep (se 1 (by rfl) ⟨2286341, by rfl⟩ : syracuseStep 3048455 = 4572683) B4572683
theorem B2032303 : Blo 2031435 2032303 := bstep (se 1 (by rfl) ⟨1524227, by rfl⟩ : syracuseStep 2032303 = 3048455) B3048455
theorem B3048461 : Blo 2031435 3048461 := bbase (se 3 (by rfl) ⟨571586, by rfl⟩ : syracuseStep 3048461 = 1143173) (by norm_num)
theorem B2032307 : Blo 2031435 2032307 := bstep (se 1 (by rfl) ⟨1524230, by rfl⟩ : syracuseStep 2032307 = 3048461) B3048461
theorem B4572701 : Blo 2031435 4572701 := bbase (se 3 (by rfl) ⟨857381, by rfl⟩ : syracuseStep 4572701 = 1714763) (by norm_num)
theorem B3048467 : Blo 2031435 3048467 := bstep (se 1 (by rfl) ⟨2286350, by rfl⟩ : syracuseStep 3048467 = 4572701) B4572701
theorem B2032311 : Blo 2031435 2032311 := bstep (se 1 (by rfl) ⟨1524233, by rfl⟩ : syracuseStep 2032311 = 3048467) B3048467
theorem B3429533 : Blo 2031435 3429533 := bbase (se 3 (by rfl) ⟨643037, by rfl⟩ : syracuseStep 3429533 = 1286075) (by norm_num)
theorem B2286355 : Blo 2031435 2286355 := bstep (se 1 (by rfl) ⟨1714766, by rfl⟩ : syracuseStep 2286355 = 3429533) B3429533
theorem B3048473 : Blo 2031435 3048473 := bstep (se 2 (by rfl) ⟨1143177, by rfl⟩ : syracuseStep 3048473 = 2286355) B2286355
theorem B2032315 : Blo 2031435 2032315 := bstep (se 1 (by rfl) ⟨1524236, by rfl⟩ : syracuseStep 2032315 = 3048473) B3048473
theorem B3218285 : Blo 2031435 3218285 := bbase (se 3 (by rfl) ⟨603428, by rfl⟩ : syracuseStep 3218285 = 1206857) (by norm_num)
theorem B2145523 : Blo 2031435 2145523 := bstep (se 1 (by rfl) ⟨1609142, by rfl⟩ : syracuseStep 2145523 = 3218285) B3218285
theorem B2860697 : Blo 2031435 2860697 := bstep (se 2 (by rfl) ⟨1072761, by rfl⟩ : syracuseStep 2860697 = 2145523) B2145523
theorem B7628525 : Blo 2031435 7628525 := bstep (se 3 (by rfl) ⟨1430348, by rfl⟩ : syracuseStep 7628525 = 2860697) B2860697
theorem B5085683 : Blo 2031435 5085683 := bstep (se 1 (by rfl) ⟨3814262, by rfl⟩ : syracuseStep 5085683 = 7628525) B7628525
theorem B3390455 : Blo 2031435 3390455 := bstep (se 1 (by rfl) ⟨2542841, by rfl⟩ : syracuseStep 3390455 = 5085683) B5085683
theorem B2260303 : Blo 2031435 2260303 := bstep (se 1 (by rfl) ⟨1695227, by rfl⟩ : syracuseStep 2260303 = 3390455) B3390455
theorem B12054949 : Blo 2031435 12054949 := bstep (se 4 (by rfl) ⟨1130151, by rfl⟩ : syracuseStep 12054949 = 2260303) B2260303
theorem B64293061 : Blo 2031435 64293061 := bstep (se 4 (by rfl) ⟨6027474, by rfl⟩ : syracuseStep 64293061 = 12054949) B12054949
theorem B85724081 : Blo 2031435 85724081 := bstep (se 2 (by rfl) ⟨32146530, by rfl⟩ : syracuseStep 85724081 = 64293061) B64293061
theorem B57149387 : Blo 2031435 57149387 := bstep (se 1 (by rfl) ⟨42862040, by rfl⟩ : syracuseStep 57149387 = 85724081) B85724081
theorem B38099591 : Blo 2031435 38099591 := bstep (se 1 (by rfl) ⟨28574693, by rfl⟩ : syracuseStep 38099591 = 57149387) B57149387
theorem B25399727 : Blo 2031435 25399727 := bstep (se 1 (by rfl) ⟨19049795, by rfl⟩ : syracuseStep 25399727 = 38099591) B38099591
theorem B16933151 : Blo 2031435 16933151 := bstep (se 1 (by rfl) ⟨12699863, by rfl⟩ : syracuseStep 16933151 = 25399727) B25399727
theorem B11288767 : Blo 2031435 11288767 := bstep (se 1 (by rfl) ⟨8466575, by rfl⟩ : syracuseStep 11288767 = 16933151) B16933151
theorem B15051689 : Blo 2031435 15051689 := bstep (se 2 (by rfl) ⟨5644383, by rfl⟩ : syracuseStep 15051689 = 11288767) B11288767
theorem B10034459 : Blo 2031435 10034459 := bstep (se 1 (by rfl) ⟨7525844, by rfl⟩ : syracuseStep 10034459 = 15051689) B15051689
theorem B6689639 : Blo 2031435 6689639 := bstep (se 1 (by rfl) ⟨5017229, by rfl⟩ : syracuseStep 6689639 = 10034459) B10034459
theorem B17839037 : Blo 2031435 17839037 := bstep (se 3 (by rfl) ⟨3344819, by rfl⟩ : syracuseStep 17839037 = 6689639) B6689639
theorem B11892691 : Blo 2031435 11892691 := bstep (se 1 (by rfl) ⟨8919518, by rfl⟩ : syracuseStep 11892691 = 17839037) B17839037
theorem B15856921 : Blo 2031435 15856921 := bstep (se 2 (by rfl) ⟨5946345, by rfl⟩ : syracuseStep 15856921 = 11892691) B11892691
theorem B21142561 : Blo 2031435 21142561 := bstep (se 2 (by rfl) ⟨7928460, by rfl⟩ : syracuseStep 21142561 = 15856921) B15856921
theorem B28190081 : Blo 2031435 28190081 := bstep (se 2 (by rfl) ⟨10571280, by rfl⟩ : syracuseStep 28190081 = 21142561) B21142561
theorem B18793387 : Blo 2031435 18793387 := bstep (se 1 (by rfl) ⟨14095040, by rfl⟩ : syracuseStep 18793387 = 28190081) B28190081
theorem B25057849 : Blo 2031435 25057849 := bstep (se 2 (by rfl) ⟨9396693, by rfl⟩ : syracuseStep 25057849 = 18793387) B18793387
theorem B33410465 : Blo 2031435 33410465 := bstep (se 2 (by rfl) ⟨12528924, by rfl⟩ : syracuseStep 33410465 = 25057849) B25057849
theorem B22273643 : Blo 2031435 22273643 := bstep (se 1 (by rfl) ⟨16705232, by rfl⟩ : syracuseStep 22273643 = 33410465) B33410465
theorem B14849095 : Blo 2031435 14849095 := bstep (se 1 (by rfl) ⟨11136821, by rfl⟩ : syracuseStep 14849095 = 22273643) B22273643
theorem B19798793 : Blo 2031435 19798793 := bstep (se 2 (by rfl) ⟨7424547, by rfl⟩ : syracuseStep 19798793 = 14849095) B14849095
theorem B13199195 : Blo 2031435 13199195 := bstep (se 1 (by rfl) ⟨9899396, by rfl⟩ : syracuseStep 13199195 = 19798793) B19798793
theorem B8799463 : Blo 2031435 8799463 := bstep (se 1 (by rfl) ⟨6599597, by rfl⟩ : syracuseStep 8799463 = 13199195) B13199195
theorem B11732617 : Blo 2031435 11732617 := bstep (se 2 (by rfl) ⟨4399731, by rfl⟩ : syracuseStep 11732617 = 8799463) B8799463
theorem B15643489 : Blo 2031435 15643489 := bstep (se 2 (by rfl) ⟨5866308, by rfl⟩ : syracuseStep 15643489 = 11732617) B11732617
theorem B20857985 : Blo 2031435 20857985 := bstep (se 2 (by rfl) ⟨7821744, by rfl⟩ : syracuseStep 20857985 = 15643489) B15643489
theorem B13905323 : Blo 2031435 13905323 := bstep (se 1 (by rfl) ⟨10428992, by rfl⟩ : syracuseStep 13905323 = 20857985) B20857985
theorem B9270215 : Blo 2031435 9270215 := bstep (se 1 (by rfl) ⟨6952661, by rfl⟩ : syracuseStep 9270215 = 13905323) B13905323
theorem B6180143 : Blo 2031435 6180143 := bstep (se 1 (by rfl) ⟨4635107, by rfl⟩ : syracuseStep 6180143 = 9270215) B9270215
theorem B65921525 : Blo 2031435 65921525 := bstep (se 5 (by rfl) ⟨3090071, by rfl⟩ : syracuseStep 65921525 = 6180143) B6180143
theorem B43947683 : Blo 2031435 43947683 := bstep (se 1 (by rfl) ⟨32960762, by rfl⟩ : syracuseStep 43947683 = 65921525) B65921525
theorem B29298455 : Blo 2031435 29298455 := bstep (se 1 (by rfl) ⟨21973841, by rfl⟩ : syracuseStep 29298455 = 43947683) B43947683
theorem B19532303 : Blo 2031435 19532303 := bstep (se 1 (by rfl) ⟨14649227, by rfl⟩ : syracuseStep 19532303 = 29298455) B29298455
theorem B13021535 : Blo 2031435 13021535 := bstep (se 1 (by rfl) ⟨9766151, by rfl⟩ : syracuseStep 13021535 = 19532303) B19532303
theorem B8681023 : Blo 2031435 8681023 := bstep (se 1 (by rfl) ⟨6510767, by rfl⟩ : syracuseStep 8681023 = 13021535) B13021535
theorem B11574697 : Blo 2031435 11574697 := bstep (se 2 (by rfl) ⟨4340511, by rfl⟩ : syracuseStep 11574697 = 8681023) B8681023
theorem B15432929 : Blo 2031435 15432929 := bstep (se 2 (by rfl) ⟨5787348, by rfl⟩ : syracuseStep 15432929 = 11574697) B11574697
theorem B10288619 : Blo 2031435 10288619 := bstep (se 1 (by rfl) ⟨7716464, by rfl⟩ : syracuseStep 10288619 = 15432929) B15432929
theorem B6859079 : Blo 2031435 6859079 := bstep (se 1 (by rfl) ⟨5144309, by rfl⟩ : syracuseStep 6859079 = 10288619) B10288619
theorem B4572719 : Blo 2031435 4572719 := bstep (se 1 (by rfl) ⟨3429539, by rfl⟩ : syracuseStep 4572719 = 6859079) B6859079
theorem B3048479 : Blo 2031435 3048479 := bstep (se 1 (by rfl) ⟨2286359, by rfl⟩ : syracuseStep 3048479 = 4572719) B4572719
theorem B2032319 : Blo 2031435 2032319 := bstep (se 1 (by rfl) ⟨1524239, by rfl⟩ : syracuseStep 2032319 = 3048479) B3048479
theorem B3048485 : Blo 2031435 3048485 := bbase (se 4 (by rfl) ⟨285795, by rfl⟩ : syracuseStep 3048485 = 571591) (by norm_num)
theorem B2032323 : Blo 2031435 2032323 := bstep (se 1 (by rfl) ⟨1524242, by rfl⟩ : syracuseStep 2032323 = 3048485) B3048485
theorem B2572165 : Blo 2031435 2572165 := bbase (se 4 (by rfl) ⟨241140, by rfl⟩ : syracuseStep 2572165 = 482281) (by norm_num)
theorem B3429553 : Blo 2031435 3429553 := bstep (se 2 (by rfl) ⟨1286082, by rfl⟩ : syracuseStep 3429553 = 2572165) B2572165
theorem B4572737 : Blo 2031435 4572737 := bstep (se 2 (by rfl) ⟨1714776, by rfl⟩ : syracuseStep 4572737 = 3429553) B3429553
theorem B3048491 : Blo 2031435 3048491 := bstep (se 1 (by rfl) ⟨2286368, by rfl⟩ : syracuseStep 3048491 = 4572737) B4572737
theorem B2032327 : Blo 2031435 2032327 := bstep (se 1 (by rfl) ⟨1524245, by rfl⟩ : syracuseStep 2032327 = 3048491) B3048491
theorem B2286373 : Blo 2031435 2286373 := bbase (se 4 (by rfl) ⟨214347, by rfl⟩ : syracuseStep 2286373 = 428695) (by norm_num)
theorem B3048497 : Blo 2031435 3048497 := bstep (se 2 (by rfl) ⟨1143186, by rfl⟩ : syracuseStep 3048497 = 2286373) B2286373
theorem B2032331 : Blo 2031435 2032331 := bstep (se 1 (by rfl) ⟨1524248, by rfl⟩ : syracuseStep 2032331 = 3048497) B3048497
theorem B8681093 : Blo 2031435 8681093 := bbase (se 4 (by rfl) ⟨813852, by rfl⟩ : syracuseStep 8681093 = 1627705) (by norm_num)
theorem B5787395 : Blo 2031435 5787395 := bstep (se 1 (by rfl) ⟨4340546, by rfl⟩ : syracuseStep 5787395 = 8681093) B8681093
theorem B3858263 : Blo 2031435 3858263 := bstep (se 1 (by rfl) ⟨2893697, by rfl⟩ : syracuseStep 3858263 = 5787395) B5787395
theorem B2572175 : Blo 2031435 2572175 := bstep (se 1 (by rfl) ⟨1929131, by rfl⟩ : syracuseStep 2572175 = 3858263) B3858263
theorem B6859133 : Blo 2031435 6859133 := bstep (se 3 (by rfl) ⟨1286087, by rfl⟩ : syracuseStep 6859133 = 2572175) B2572175
theorem B4572755 : Blo 2031435 4572755 := bstep (se 1 (by rfl) ⟨3429566, by rfl⟩ : syracuseStep 4572755 = 6859133) B6859133
theorem B3048503 : Blo 2031435 3048503 := bstep (se 1 (by rfl) ⟨2286377, by rfl⟩ : syracuseStep 3048503 = 4572755) B4572755
theorem B2032335 : Blo 2031435 2032335 := bstep (se 1 (by rfl) ⟨1524251, by rfl⟩ : syracuseStep 2032335 = 3048503) B3048503
theorem B3048509 : Blo 2031435 3048509 := bbase (se 3 (by rfl) ⟨571595, by rfl⟩ : syracuseStep 3048509 = 1143191) (by norm_num)
theorem B2032339 : Blo 2031435 2032339 := bstep (se 1 (by rfl) ⟨1524254, by rfl⟩ : syracuseStep 2032339 = 3048509) B3048509
theorem B4572773 : Blo 2031435 4572773 := bbase (se 4 (by rfl) ⟨428697, by rfl⟩ : syracuseStep 4572773 = 857395) (by norm_num)
theorem B3048515 : Blo 2031435 3048515 := bstep (se 1 (by rfl) ⟨2286386, by rfl⟩ : syracuseStep 3048515 = 4572773) B4572773
theorem B2032343 : Blo 2031435 2032343 := bstep (se 1 (by rfl) ⟨1524257, by rfl⟩ : syracuseStep 2032343 = 3048515) B3048515
theorem B5144381 : Blo 2031435 5144381 := bbase (se 3 (by rfl) ⟨964571, by rfl⟩ : syracuseStep 5144381 = 1929143) (by norm_num)
theorem B3429587 : Blo 2031435 3429587 := bstep (se 1 (by rfl) ⟨2572190, by rfl⟩ : syracuseStep 3429587 = 5144381) B5144381
theorem B2286391 : Blo 2031435 2286391 := bstep (se 1 (by rfl) ⟨1714793, by rfl⟩ : syracuseStep 2286391 = 3429587) B3429587
theorem B3048521 : Blo 2031435 3048521 := bstep (se 2 (by rfl) ⟨1143195, by rfl⟩ : syracuseStep 3048521 = 2286391) B2286391
theorem B2032347 : Blo 2031435 2032347 := bstep (se 1 (by rfl) ⟨1524260, by rfl⟩ : syracuseStep 2032347 = 3048521) B3048521
theorem B3858293 : Blo 2031435 3858293 := bbase (se 5 (by rfl) ⟨180857, by rfl⟩ : syracuseStep 3858293 = 361715) (by norm_num)
theorem B10288781 : Blo 2031435 10288781 := bstep (se 3 (by rfl) ⟨1929146, by rfl⟩ : syracuseStep 10288781 = 3858293) B3858293
theorem B6859187 : Blo 2031435 6859187 := bstep (se 1 (by rfl) ⟨5144390, by rfl⟩ : syracuseStep 6859187 = 10288781) B10288781
theorem B4572791 : Blo 2031435 4572791 := bstep (se 1 (by rfl) ⟨3429593, by rfl⟩ : syracuseStep 4572791 = 6859187) B6859187
theorem B3048527 : Blo 2031435 3048527 := bstep (se 1 (by rfl) ⟨2286395, by rfl⟩ : syracuseStep 3048527 = 4572791) B4572791
theorem B2032351 : Blo 2031435 2032351 := bstep (se 1 (by rfl) ⟨1524263, by rfl⟩ : syracuseStep 2032351 = 3048527) B3048527
theorem B3048533 : Blo 2031435 3048533 := bbase (se 8 (by rfl) ⟨17862, by rfl⟩ : syracuseStep 3048533 = 35725) (by norm_num)
theorem B2032355 : Blo 2031435 2032355 := bstep (se 1 (by rfl) ⟨1524266, by rfl⟩ : syracuseStep 2032355 = 3048533) B3048533
theorem B3090133 : Blo 2031435 3090133 := bbase (se 7 (by rfl) ⟨36212, by rfl⟩ : syracuseStep 3090133 = 72425) (by norm_num)
theorem B16480709 : Blo 2031435 16480709 := bstep (se 4 (by rfl) ⟨1545066, by rfl⟩ : syracuseStep 16480709 = 3090133) B3090133
theorem B10987139 : Blo 2031435 10987139 := bstep (se 1 (by rfl) ⟨8240354, by rfl⟩ : syracuseStep 10987139 = 16480709) B16480709
theorem B7324759 : Blo 2031435 7324759 := bstep (se 1 (by rfl) ⟨5493569, by rfl⟩ : syracuseStep 7324759 = 10987139) B10987139
theorem B9766345 : Blo 2031435 9766345 := bstep (se 2 (by rfl) ⟨3662379, by rfl⟩ : syracuseStep 9766345 = 7324759) B7324759
theorem B13021793 : Blo 2031435 13021793 := bstep (se 2 (by rfl) ⟨4883172, by rfl⟩ : syracuseStep 13021793 = 9766345) B9766345
theorem B8681195 : Blo 2031435 8681195 := bstep (se 1 (by rfl) ⟨6510896, by rfl⟩ : syracuseStep 8681195 = 13021793) B13021793
theorem B5787463 : Blo 2031435 5787463 := bstep (se 1 (by rfl) ⟨4340597, by rfl⟩ : syracuseStep 5787463 = 8681195) B8681195
theorem B7716617 : Blo 2031435 7716617 := bstep (se 2 (by rfl) ⟨2893731, by rfl⟩ : syracuseStep 7716617 = 5787463) B5787463
theorem B5144411 : Blo 2031435 5144411 := bstep (se 1 (by rfl) ⟨3858308, by rfl⟩ : syracuseStep 5144411 = 7716617) B7716617
theorem B3429607 : Blo 2031435 3429607 := bstep (se 1 (by rfl) ⟨2572205, by rfl⟩ : syracuseStep 3429607 = 5144411) B5144411
theorem B4572809 : Blo 2031435 4572809 := bstep (se 2 (by rfl) ⟨1714803, by rfl⟩ : syracuseStep 4572809 = 3429607) B3429607
theorem B3048539 : Blo 2031435 3048539 := bstep (se 1 (by rfl) ⟨2286404, by rfl⟩ : syracuseStep 3048539 = 4572809) B4572809
theorem B2032359 : Blo 2031435 2032359 := bstep (se 1 (by rfl) ⟨1524269, by rfl⟩ : syracuseStep 2032359 = 3048539) B3048539
theorem B2286409 : Blo 2031435 2286409 := bbase (se 2 (by rfl) ⟨857403, by rfl⟩ : syracuseStep 2286409 = 1714807) (by norm_num)
theorem B3048545 : Blo 2031435 3048545 := bstep (se 2 (by rfl) ⟨1143204, by rfl⟩ : syracuseStep 3048545 = 2286409) B2286409
theorem B2032363 : Blo 2031435 2032363 := bstep (se 1 (by rfl) ⟨1524272, by rfl⟩ : syracuseStep 2032363 = 3048545) B3048545
theorem B2317609 : Blo 2031435 2317609 := bbase (se 2 (by rfl) ⟨869103, by rfl⟩ : syracuseStep 2317609 = 1738207) (by norm_num)
theorem B3090145 : Blo 2031435 3090145 := bstep (se 2 (by rfl) ⟨1158804, by rfl⟩ : syracuseStep 3090145 = 2317609) B2317609
theorem B4120193 : Blo 2031435 4120193 := bstep (se 2 (by rfl) ⟨1545072, by rfl⟩ : syracuseStep 4120193 = 3090145) B3090145
theorem B10987181 : Blo 2031435 10987181 := bstep (se 3 (by rfl) ⟨2060096, by rfl⟩ : syracuseStep 10987181 = 4120193) B4120193
theorem B7324787 : Blo 2031435 7324787 := bstep (se 1 (by rfl) ⟨5493590, by rfl⟩ : syracuseStep 7324787 = 10987181) B10987181
theorem B19532765 : Blo 2031435 19532765 := bstep (se 3 (by rfl) ⟨3662393, by rfl⟩ : syracuseStep 19532765 = 7324787) B7324787
theorem B13021843 : Blo 2031435 13021843 := bstep (se 1 (by rfl) ⟨9766382, by rfl⟩ : syracuseStep 13021843 = 19532765) B19532765
theorem B17362457 : Blo 2031435 17362457 := bstep (se 2 (by rfl) ⟨6510921, by rfl⟩ : syracuseStep 17362457 = 13021843) B13021843
theorem B11574971 : Blo 2031435 11574971 := bstep (se 1 (by rfl) ⟨8681228, by rfl⟩ : syracuseStep 11574971 = 17362457) B17362457
theorem B7716647 : Blo 2031435 7716647 := bstep (se 1 (by rfl) ⟨5787485, by rfl⟩ : syracuseStep 7716647 = 11574971) B11574971
theorem B5144431 : Blo 2031435 5144431 := bstep (se 1 (by rfl) ⟨3858323, by rfl⟩ : syracuseStep 5144431 = 7716647) B7716647
theorem B6859241 : Blo 2031435 6859241 := bstep (se 2 (by rfl) ⟨2572215, by rfl⟩ : syracuseStep 6859241 = 5144431) B5144431
theorem B4572827 : Blo 2031435 4572827 := bstep (se 1 (by rfl) ⟨3429620, by rfl⟩ : syracuseStep 4572827 = 6859241) B6859241
theorem B3048551 : Blo 2031435 3048551 := bstep (se 1 (by rfl) ⟨2286413, by rfl⟩ : syracuseStep 3048551 = 4572827) B4572827
theorem B2032367 : Blo 2031435 2032367 := bstep (se 1 (by rfl) ⟨1524275, by rfl⟩ : syracuseStep 2032367 = 3048551) B3048551
theorem B3048557 : Blo 2031435 3048557 := bbase (se 3 (by rfl) ⟨571604, by rfl⟩ : syracuseStep 3048557 = 1143209) (by norm_num)
theorem B2032371 : Blo 2031435 2032371 := bstep (se 1 (by rfl) ⟨1524278, by rfl⟩ : syracuseStep 2032371 = 3048557) B3048557
theorem B4572845 : Blo 2031435 4572845 := bbase (se 3 (by rfl) ⟨857408, by rfl⟩ : syracuseStep 4572845 = 1714817) (by norm_num)
theorem B3048563 : Blo 2031435 3048563 := bstep (se 1 (by rfl) ⟨2286422, by rfl⟩ : syracuseStep 3048563 = 4572845) B4572845
theorem B2032375 : Blo 2031435 2032375 := bstep (se 1 (by rfl) ⟨1524281, by rfl⟩ : syracuseStep 2032375 = 3048563) B3048563
theorem B2746813 : Blo 2031435 2746813 := bbase (se 3 (by rfl) ⟨515027, by rfl⟩ : syracuseStep 2746813 = 1030055) (by norm_num)
theorem B3662417 : Blo 2031435 3662417 := bstep (se 2 (by rfl) ⟨1373406, by rfl⟩ : syracuseStep 3662417 = 2746813) B2746813
theorem B2441611 : Blo 2031435 2441611 := bstep (se 1 (by rfl) ⟨1831208, by rfl⟩ : syracuseStep 2441611 = 3662417) B3662417
theorem B3255481 : Blo 2031435 3255481 := bstep (se 2 (by rfl) ⟨1220805, by rfl⟩ : syracuseStep 3255481 = 2441611) B2441611
theorem B4340641 : Blo 2031435 4340641 := bstep (se 2 (by rfl) ⟨1627740, by rfl⟩ : syracuseStep 4340641 = 3255481) B3255481
theorem B5787521 : Blo 2031435 5787521 := bstep (se 2 (by rfl) ⟨2170320, by rfl⟩ : syracuseStep 5787521 = 4340641) B4340641
theorem B3858347 : Blo 2031435 3858347 := bstep (se 1 (by rfl) ⟨2893760, by rfl⟩ : syracuseStep 3858347 = 5787521) B5787521
theorem B2572231 : Blo 2031435 2572231 := bstep (se 1 (by rfl) ⟨1929173, by rfl⟩ : syracuseStep 2572231 = 3858347) B3858347
theorem B3429641 : Blo 2031435 3429641 := bstep (se 2 (by rfl) ⟨1286115, by rfl⟩ : syracuseStep 3429641 = 2572231) B2572231
theorem B2286427 : Blo 2031435 2286427 := bstep (se 1 (by rfl) ⟨1714820, by rfl⟩ : syracuseStep 2286427 = 3429641) B3429641
theorem B3048569 : Blo 2031435 3048569 := bstep (se 2 (by rfl) ⟨1143213, by rfl⟩ : syracuseStep 3048569 = 2286427) B2286427
theorem B2032379 : Blo 2031435 2032379 := bstep (se 1 (by rfl) ⟨1524284, by rfl⟩ : syracuseStep 2032379 = 3048569) B3048569
theorem B19532917 : Blo 2031435 19532917 := bbase (se 5 (by rfl) ⟨915605, by rfl⟩ : syracuseStep 19532917 = 1831211) (by norm_num)
theorem B26043889 : Blo 2031435 26043889 := bstep (se 2 (by rfl) ⟨9766458, by rfl⟩ : syracuseStep 26043889 = 19532917) B19532917
theorem B34725185 : Blo 2031435 34725185 := bstep (se 2 (by rfl) ⟨13021944, by rfl⟩ : syracuseStep 34725185 = 26043889) B26043889
theorem B23150123 : Blo 2031435 23150123 := bstep (se 1 (by rfl) ⟨17362592, by rfl⟩ : syracuseStep 23150123 = 34725185) B34725185
theorem B15433415 : Blo 2031435 15433415 := bstep (se 1 (by rfl) ⟨11575061, by rfl⟩ : syracuseStep 15433415 = 23150123) B23150123
theorem B10288943 : Blo 2031435 10288943 := bstep (se 1 (by rfl) ⟨7716707, by rfl⟩ : syracuseStep 10288943 = 15433415) B15433415
theorem B6859295 : Blo 2031435 6859295 := bstep (se 1 (by rfl) ⟨5144471, by rfl⟩ : syracuseStep 6859295 = 10288943) B10288943
theorem B4572863 : Blo 2031435 4572863 := bstep (se 1 (by rfl) ⟨3429647, by rfl⟩ : syracuseStep 4572863 = 6859295) B6859295
theorem B3048575 : Blo 2031435 3048575 := bstep (se 1 (by rfl) ⟨2286431, by rfl⟩ : syracuseStep 3048575 = 4572863) B4572863
theorem B2032383 : Blo 2031435 2032383 := bstep (se 1 (by rfl) ⟨1524287, by rfl⟩ : syracuseStep 2032383 = 3048575) B3048575
theorem B3048581 : Blo 2031435 3048581 := bbase (se 4 (by rfl) ⟨285804, by rfl⟩ : syracuseStep 3048581 = 571609) (by norm_num)
theorem B2032387 : Blo 2031435 2032387 := bstep (se 1 (by rfl) ⟨1524290, by rfl⟩ : syracuseStep 2032387 = 3048581) B3048581
theorem B3429661 : Blo 2031435 3429661 := bbase (se 3 (by rfl) ⟨643061, by rfl⟩ : syracuseStep 3429661 = 1286123) (by norm_num)
theorem B4572881 : Blo 2031435 4572881 := bstep (se 2 (by rfl) ⟨1714830, by rfl⟩ : syracuseStep 4572881 = 3429661) B3429661
theorem B3048587 : Blo 2031435 3048587 := bstep (se 1 (by rfl) ⟨2286440, by rfl⟩ : syracuseStep 3048587 = 4572881) B4572881
theorem B2032391 : Blo 2031435 2032391 := bstep (se 1 (by rfl) ⟨1524293, by rfl⟩ : syracuseStep 2032391 = 3048587) B3048587
theorem B2286445 : Blo 2031435 2286445 := bbase (se 3 (by rfl) ⟨428708, by rfl⟩ : syracuseStep 2286445 = 857417) (by norm_num)
theorem B3048593 : Blo 2031435 3048593 := bstep (se 2 (by rfl) ⟨1143222, by rfl⟩ : syracuseStep 3048593 = 2286445) B2286445
theorem B2032395 : Blo 2031435 2032395 := bstep (se 1 (by rfl) ⟨1524296, by rfl⟩ : syracuseStep 2032395 = 3048593) B3048593
theorem B6859349 : Blo 2031435 6859349 := bbase (se 8 (by rfl) ⟨40191, by rfl⟩ : syracuseStep 6859349 = 80383) (by norm_num)
theorem B4572899 : Blo 2031435 4572899 := bstep (se 1 (by rfl) ⟨3429674, by rfl⟩ : syracuseStep 4572899 = 6859349) B6859349
theorem B3048599 : Blo 2031435 3048599 := bstep (se 1 (by rfl) ⟨2286449, by rfl⟩ : syracuseStep 3048599 = 4572899) B4572899
theorem B2032399 : Blo 2031435 2032399 := bstep (se 1 (by rfl) ⟨1524299, by rfl⟩ : syracuseStep 2032399 = 3048599) B3048599
theorem B3048605 : Blo 2031435 3048605 := bbase (se 3 (by rfl) ⟨571613, by rfl⟩ : syracuseStep 3048605 = 1143227) (by norm_num)
theorem B2032403 : Blo 2031435 2032403 := bstep (se 1 (by rfl) ⟨1524302, by rfl⟩ : syracuseStep 2032403 = 3048605) B3048605
theorem B4572917 : Blo 2031435 4572917 := bbase (se 5 (by rfl) ⟨214355, by rfl⟩ : syracuseStep 4572917 = 428711) (by norm_num)
theorem B3048611 : Blo 2031435 3048611 := bstep (se 1 (by rfl) ⟨2286458, by rfl⟩ : syracuseStep 3048611 = 4572917) B4572917
theorem B2032407 : Blo 2031435 2032407 := bstep (se 1 (by rfl) ⟨1524305, by rfl⟩ : syracuseStep 2032407 = 3048611) B3048611
theorem B4399933 : Blo 2031435 4399933 := bbase (se 3 (by rfl) ⟨824987, by rfl⟩ : syracuseStep 4399933 = 1649975) (by norm_num)
theorem B5866577 : Blo 2031435 5866577 := bstep (se 2 (by rfl) ⟨2199966, by rfl⟩ : syracuseStep 5866577 = 4399933) B4399933
theorem B3911051 : Blo 2031435 3911051 := bstep (se 1 (by rfl) ⟨2933288, by rfl⟩ : syracuseStep 3911051 = 5866577) B5866577
theorem B10429469 : Blo 2031435 10429469 := bstep (se 3 (by rfl) ⟨1955525, by rfl⟩ : syracuseStep 10429469 = 3911051) B3911051
theorem B6952979 : Blo 2031435 6952979 := bstep (se 1 (by rfl) ⟨5214734, by rfl⟩ : syracuseStep 6952979 = 10429469) B10429469
theorem B4635319 : Blo 2031435 4635319 := bstep (se 1 (by rfl) ⟨3476489, by rfl⟩ : syracuseStep 4635319 = 6952979) B6952979
theorem B6180425 : Blo 2031435 6180425 := bstep (se 2 (by rfl) ⟨2317659, by rfl⟩ : syracuseStep 6180425 = 4635319) B4635319
theorem B4120283 : Blo 2031435 4120283 := bstep (se 1 (by rfl) ⟨3090212, by rfl⟩ : syracuseStep 4120283 = 6180425) B6180425
theorem B2746855 : Blo 2031435 2746855 := bstep (se 1 (by rfl) ⟨2060141, by rfl⟩ : syracuseStep 2746855 = 4120283) B4120283
theorem B14649893 : Blo 2031435 14649893 := bstep (se 4 (by rfl) ⟨1373427, by rfl⟩ : syracuseStep 14649893 = 2746855) B2746855
theorem B9766595 : Blo 2031435 9766595 := bstep (se 1 (by rfl) ⟨7324946, by rfl⟩ : syracuseStep 9766595 = 14649893) B14649893
theorem B26044253 : Blo 2031435 26044253 := bstep (se 3 (by rfl) ⟨4883297, by rfl⟩ : syracuseStep 26044253 = 9766595) B9766595
theorem B17362835 : Blo 2031435 17362835 := bstep (se 1 (by rfl) ⟨13022126, by rfl⟩ : syracuseStep 17362835 = 26044253) B26044253
theorem B11575223 : Blo 2031435 11575223 := bstep (se 1 (by rfl) ⟨8681417, by rfl⟩ : syracuseStep 11575223 = 17362835) B17362835
theorem B7716815 : Blo 2031435 7716815 := bstep (se 1 (by rfl) ⟨5787611, by rfl⟩ : syracuseStep 7716815 = 11575223) B11575223
theorem B5144543 : Blo 2031435 5144543 := bstep (se 1 (by rfl) ⟨3858407, by rfl⟩ : syracuseStep 5144543 = 7716815) B7716815
theorem B3429695 : Blo 2031435 3429695 := bstep (se 1 (by rfl) ⟨2572271, by rfl⟩ : syracuseStep 3429695 = 5144543) B5144543
theorem B2286463 : Blo 2031435 2286463 := bstep (se 1 (by rfl) ⟨1714847, by rfl⟩ : syracuseStep 2286463 = 3429695) B3429695
theorem B3048617 : Blo 2031435 3048617 := bstep (se 2 (by rfl) ⟨1143231, by rfl⟩ : syracuseStep 3048617 = 2286463) B2286463
theorem B2032411 : Blo 2031435 2032411 := bstep (se 1 (by rfl) ⟨1524308, by rfl⟩ : syracuseStep 2032411 = 3048617) B3048617
theorem B4340717 : Blo 2031435 4340717 := bbase (se 3 (by rfl) ⟨813884, by rfl⟩ : syracuseStep 4340717 = 1627769) (by norm_num)
theorem B2893811 : Blo 2031435 2893811 := bstep (se 1 (by rfl) ⟨2170358, by rfl⟩ : syracuseStep 2893811 = 4340717) B4340717
theorem B7716829 : Blo 2031435 7716829 := bstep (se 3 (by rfl) ⟨1446905, by rfl⟩ : syracuseStep 7716829 = 2893811) B2893811
theorem B10289105 : Blo 2031435 10289105 := bstep (se 2 (by rfl) ⟨3858414, by rfl⟩ : syracuseStep 10289105 = 7716829) B7716829
theorem B6859403 : Blo 2031435 6859403 := bstep (se 1 (by rfl) ⟨5144552, by rfl⟩ : syracuseStep 6859403 = 10289105) B10289105
theorem B4572935 : Blo 2031435 4572935 := bstep (se 1 (by rfl) ⟨3429701, by rfl⟩ : syracuseStep 4572935 = 6859403) B6859403
theorem B3048623 : Blo 2031435 3048623 := bstep (se 1 (by rfl) ⟨2286467, by rfl⟩ : syracuseStep 3048623 = 4572935) B4572935
theorem B2032415 : Blo 2031435 2032415 := bstep (se 1 (by rfl) ⟨1524311, by rfl⟩ : syracuseStep 2032415 = 3048623) B3048623
theorem B3048629 : Blo 2031435 3048629 := bbase (se 5 (by rfl) ⟨142904, by rfl⟩ : syracuseStep 3048629 = 285809) (by norm_num)
theorem B2032419 : Blo 2031435 2032419 := bstep (se 1 (by rfl) ⟨1524314, by rfl⟩ : syracuseStep 2032419 = 3048629) B3048629
theorem B5144573 : Blo 2031435 5144573 := bbase (se 3 (by rfl) ⟨964607, by rfl⟩ : syracuseStep 5144573 = 1929215) (by norm_num)
theorem B3429715 : Blo 2031435 3429715 := bstep (se 1 (by rfl) ⟨2572286, by rfl⟩ : syracuseStep 3429715 = 5144573) B5144573
theorem B4572953 : Blo 2031435 4572953 := bstep (se 2 (by rfl) ⟨1714857, by rfl⟩ : syracuseStep 4572953 = 3429715) B3429715
theorem B3048635 : Blo 2031435 3048635 := bstep (se 1 (by rfl) ⟨2286476, by rfl⟩ : syracuseStep 3048635 = 4572953) B4572953
theorem B2032423 : Blo 2031435 2032423 := bstep (se 1 (by rfl) ⟨1524317, by rfl⟩ : syracuseStep 2032423 = 3048635) B3048635
theorem B2286481 : Blo 2031435 2286481 := bbase (se 2 (by rfl) ⟨857430, by rfl⟩ : syracuseStep 2286481 = 1714861) (by norm_num)
theorem B3048641 : Blo 2031435 3048641 := bstep (se 2 (by rfl) ⟨1143240, by rfl⟩ : syracuseStep 3048641 = 2286481) B2286481
theorem B2032427 : Blo 2031435 2032427 := bstep (se 1 (by rfl) ⟨1524320, by rfl⟩ : syracuseStep 2032427 = 3048641) B3048641
theorem B3858445 : Blo 2031435 3858445 := bbase (se 3 (by rfl) ⟨723458, by rfl⟩ : syracuseStep 3858445 = 1446917) (by norm_num)
theorem B5144593 : Blo 2031435 5144593 := bstep (se 2 (by rfl) ⟨1929222, by rfl⟩ : syracuseStep 5144593 = 3858445) B3858445
theorem B6859457 : Blo 2031435 6859457 := bstep (se 2 (by rfl) ⟨2572296, by rfl⟩ : syracuseStep 6859457 = 5144593) B5144593
theorem B4572971 : Blo 2031435 4572971 := bstep (se 1 (by rfl) ⟨3429728, by rfl⟩ : syracuseStep 4572971 = 6859457) B6859457
theorem B3048647 : Blo 2031435 3048647 := bstep (se 1 (by rfl) ⟨2286485, by rfl⟩ : syracuseStep 3048647 = 4572971) B4572971
theorem B2032431 : Blo 2031435 2032431 := bstep (se 1 (by rfl) ⟨1524323, by rfl⟩ : syracuseStep 2032431 = 3048647) B3048647
theorem B3048653 : Blo 2031435 3048653 := bbase (se 3 (by rfl) ⟨571622, by rfl⟩ : syracuseStep 3048653 = 1143245) (by norm_num)
theorem B2032435 : Blo 2031435 2032435 := bstep (se 1 (by rfl) ⟨1524326, by rfl⟩ : syracuseStep 2032435 = 3048653) B3048653
theorem B4572989 : Blo 2031435 4572989 := bbase (se 3 (by rfl) ⟨857435, by rfl⟩ : syracuseStep 4572989 = 1714871) (by norm_num)
theorem B3048659 : Blo 2031435 3048659 := bstep (se 1 (by rfl) ⟨2286494, by rfl⟩ : syracuseStep 3048659 = 4572989) B4572989
theorem B2032439 : Blo 2031435 2032439 := bstep (se 1 (by rfl) ⟨1524329, by rfl⟩ : syracuseStep 2032439 = 3048659) B3048659
theorem B3429749 : Blo 2031435 3429749 := bbase (se 5 (by rfl) ⟨160769, by rfl⟩ : syracuseStep 3429749 = 321539) (by norm_num)
theorem B2286499 : Blo 2031435 2286499 := bstep (se 1 (by rfl) ⟨1714874, by rfl⟩ : syracuseStep 2286499 = 3429749) B3429749
theorem B3048665 : Blo 2031435 3048665 := bstep (se 2 (by rfl) ⟨1143249, by rfl⟩ : syracuseStep 3048665 = 2286499) B2286499
theorem B2032443 : Blo 2031435 2032443 := bstep (se 1 (by rfl) ⟨1524332, by rfl⟩ : syracuseStep 2032443 = 3048665) B3048665
theorem B3255589 : Blo 2031435 3255589 := bbase (se 4 (by rfl) ⟨305211, by rfl⟩ : syracuseStep 3255589 = 610423) (by norm_num)
theorem B4340785 : Blo 2031435 4340785 := bstep (se 2 (by rfl) ⟨1627794, by rfl⟩ : syracuseStep 4340785 = 3255589) B3255589
theorem B5787713 : Blo 2031435 5787713 := bstep (se 2 (by rfl) ⟨2170392, by rfl⟩ : syracuseStep 5787713 = 4340785) B4340785
theorem B15433901 : Blo 2031435 15433901 := bstep (se 3 (by rfl) ⟨2893856, by rfl⟩ : syracuseStep 15433901 = 5787713) B5787713
theorem B10289267 : Blo 2031435 10289267 := bstep (se 1 (by rfl) ⟨7716950, by rfl⟩ : syracuseStep 10289267 = 15433901) B15433901
theorem B6859511 : Blo 2031435 6859511 := bstep (se 1 (by rfl) ⟨5144633, by rfl⟩ : syracuseStep 6859511 = 10289267) B10289267
theorem B4573007 : Blo 2031435 4573007 := bstep (se 1 (by rfl) ⟨3429755, by rfl⟩ : syracuseStep 4573007 = 6859511) B6859511
theorem B3048671 : Blo 2031435 3048671 := bstep (se 1 (by rfl) ⟨2286503, by rfl⟩ : syracuseStep 3048671 = 4573007) B4573007
theorem B2032447 : Blo 2031435 2032447 := bstep (se 1 (by rfl) ⟨1524335, by rfl⟩ : syracuseStep 2032447 = 3048671) B3048671
theorem B3048677 : Blo 2031435 3048677 := bbase (se 4 (by rfl) ⟨285813, by rfl⟩ : syracuseStep 3048677 = 571627) (by norm_num)
theorem B2032451 : Blo 2031435 2032451 := bstep (se 1 (by rfl) ⟨1524338, by rfl⟩ : syracuseStep 2032451 = 3048677) B3048677
theorem B6511205 : Blo 2031435 6511205 := bbase (se 4 (by rfl) ⟨610425, by rfl⟩ : syracuseStep 6511205 = 1220851) (by norm_num)
theorem B4340803 : Blo 2031435 4340803 := bstep (se 1 (by rfl) ⟨3255602, by rfl⟩ : syracuseStep 4340803 = 6511205) B6511205
theorem B5787737 : Blo 2031435 5787737 := bstep (se 2 (by rfl) ⟨2170401, by rfl⟩ : syracuseStep 5787737 = 4340803) B4340803
theorem B3858491 : Blo 2031435 3858491 := bstep (se 1 (by rfl) ⟨2893868, by rfl⟩ : syracuseStep 3858491 = 5787737) B5787737
theorem B2572327 : Blo 2031435 2572327 := bstep (se 1 (by rfl) ⟨1929245, by rfl⟩ : syracuseStep 2572327 = 3858491) B3858491
theorem B3429769 : Blo 2031435 3429769 := bstep (se 2 (by rfl) ⟨1286163, by rfl⟩ : syracuseStep 3429769 = 2572327) B2572327
theorem B4573025 : Blo 2031435 4573025 := bstep (se 2 (by rfl) ⟨1714884, by rfl⟩ : syracuseStep 4573025 = 3429769) B3429769
theorem B3048683 : Blo 2031435 3048683 := bstep (se 1 (by rfl) ⟨2286512, by rfl⟩ : syracuseStep 3048683 = 4573025) B4573025
theorem B2032455 : Blo 2031435 2032455 := bstep (se 1 (by rfl) ⟨1524341, by rfl⟩ : syracuseStep 2032455 = 3048683) B3048683
theorem B2286517 : Blo 2031435 2286517 := bbase (se 5 (by rfl) ⟨107180, by rfl⟩ : syracuseStep 2286517 = 214361) (by norm_num)
theorem B3048689 : Blo 2031435 3048689 := bstep (se 2 (by rfl) ⟨1143258, by rfl⟩ : syracuseStep 3048689 = 2286517) B2286517
theorem B2032459 : Blo 2031435 2032459 := bstep (se 1 (by rfl) ⟨1524344, by rfl⟩ : syracuseStep 2032459 = 3048689) B3048689
theorem B2572337 : Blo 2031435 2572337 := bbase (se 2 (by rfl) ⟨964626, by rfl⟩ : syracuseStep 2572337 = 1929253) (by norm_num)
theorem B6859565 : Blo 2031435 6859565 := bstep (se 3 (by rfl) ⟨1286168, by rfl⟩ : syracuseStep 6859565 = 2572337) B2572337
theorem B4573043 : Blo 2031435 4573043 := bstep (se 1 (by rfl) ⟨3429782, by rfl⟩ : syracuseStep 4573043 = 6859565) B6859565
theorem B3048695 : Blo 2031435 3048695 := bstep (se 1 (by rfl) ⟨2286521, by rfl⟩ : syracuseStep 3048695 = 4573043) B4573043
theorem B2032463 : Blo 2031435 2032463 := bstep (se 1 (by rfl) ⟨1524347, by rfl⟩ : syracuseStep 2032463 = 3048695) B3048695
theorem B3048701 : Blo 2031435 3048701 := bbase (se 3 (by rfl) ⟨571631, by rfl⟩ : syracuseStep 3048701 = 1143263) (by norm_num)
theorem B2032467 : Blo 2031435 2032467 := bstep (se 1 (by rfl) ⟨1524350, by rfl⟩ : syracuseStep 2032467 = 3048701) B3048701
theorem B4573061 : Blo 2031435 4573061 := bbase (se 4 (by rfl) ⟨428724, by rfl⟩ : syracuseStep 4573061 = 857449) (by norm_num)
theorem B3048707 : Blo 2031435 3048707 := bstep (se 1 (by rfl) ⟨2286530, by rfl⟩ : syracuseStep 3048707 = 4573061) B4573061
theorem B2032471 : Blo 2031435 2032471 := bstep (se 1 (by rfl) ⟨1524353, by rfl⟩ : syracuseStep 2032471 = 3048707) B3048707
theorem B4883453 : Blo 2031435 4883453 := bbase (se 3 (by rfl) ⟨915647, by rfl⟩ : syracuseStep 4883453 = 1831295) (by norm_num)
theorem B3255635 : Blo 2031435 3255635 := bstep (se 1 (by rfl) ⟨2441726, by rfl⟩ : syracuseStep 3255635 = 4883453) B4883453
theorem B2170423 : Blo 2031435 2170423 := bstep (se 1 (by rfl) ⟨1627817, by rfl⟩ : syracuseStep 2170423 = 3255635) B3255635
theorem B2893897 : Blo 2031435 2893897 := bstep (se 2 (by rfl) ⟨1085211, by rfl⟩ : syracuseStep 2893897 = 2170423) B2170423
theorem B3858529 : Blo 2031435 3858529 := bstep (se 2 (by rfl) ⟨1446948, by rfl⟩ : syracuseStep 3858529 = 2893897) B2893897
theorem B5144705 : Blo 2031435 5144705 := bstep (se 2 (by rfl) ⟨1929264, by rfl⟩ : syracuseStep 5144705 = 3858529) B3858529
theorem B3429803 : Blo 2031435 3429803 := bstep (se 1 (by rfl) ⟨2572352, by rfl⟩ : syracuseStep 3429803 = 5144705) B5144705
theorem B2286535 : Blo 2031435 2286535 := bstep (se 1 (by rfl) ⟨1714901, by rfl⟩ : syracuseStep 2286535 = 3429803) B3429803
theorem B3048713 : Blo 2031435 3048713 := bstep (se 2 (by rfl) ⟨1143267, by rfl⟩ : syracuseStep 3048713 = 2286535) B2286535
theorem B2032475 : Blo 2031435 2032475 := bstep (se 1 (by rfl) ⟨1524356, by rfl⟩ : syracuseStep 2032475 = 3048713) B3048713
theorem B10289429 : Blo 2031435 10289429 := bbase (se 6 (by rfl) ⟨241158, by rfl⟩ : syracuseStep 10289429 = 482317) (by norm_num)
theorem B6859619 : Blo 2031435 6859619 := bstep (se 1 (by rfl) ⟨5144714, by rfl⟩ : syracuseStep 6859619 = 10289429) B10289429
theorem B4573079 : Blo 2031435 4573079 := bstep (se 1 (by rfl) ⟨3429809, by rfl⟩ : syracuseStep 4573079 = 6859619) B6859619
theorem B3048719 : Blo 2031435 3048719 := bstep (se 1 (by rfl) ⟨2286539, by rfl⟩ : syracuseStep 3048719 = 4573079) B4573079
theorem B2032479 : Blo 2031435 2032479 := bstep (se 1 (by rfl) ⟨1524359, by rfl⟩ : syracuseStep 2032479 = 3048719) B3048719
theorem B3048725 : Blo 2031435 3048725 := bbase (se 6 (by rfl) ⟨71454, by rfl⟩ : syracuseStep 3048725 = 142909) (by norm_num)
theorem B2032483 : Blo 2031435 2032483 := bstep (se 1 (by rfl) ⟨1524362, by rfl⟩ : syracuseStep 2032483 = 3048725) B3048725
theorem B3175229 : Blo 2031435 3175229 := bbase (se 3 (by rfl) ⟨595355, by rfl⟩ : syracuseStep 3175229 = 1190711) (by norm_num)
theorem B2116819 : Blo 2031435 2116819 := bstep (se 1 (by rfl) ⟨1587614, by rfl⟩ : syracuseStep 2116819 = 3175229) B3175229
theorem B11289701 : Blo 2031435 11289701 := bstep (se 4 (by rfl) ⟨1058409, by rfl⟩ : syracuseStep 11289701 = 2116819) B2116819
theorem B7526467 : Blo 2031435 7526467 := bstep (se 1 (by rfl) ⟨5644850, by rfl⟩ : syracuseStep 7526467 = 11289701) B11289701
theorem B10035289 : Blo 2031435 10035289 := bstep (se 2 (by rfl) ⟨3763233, by rfl⟩ : syracuseStep 10035289 = 7526467) B7526467
theorem B13380385 : Blo 2031435 13380385 := bstep (se 2 (by rfl) ⟨5017644, by rfl⟩ : syracuseStep 13380385 = 10035289) B10035289
theorem B17840513 : Blo 2031435 17840513 := bstep (se 2 (by rfl) ⟨6690192, by rfl⟩ : syracuseStep 17840513 = 13380385) B13380385
theorem B47574701 : Blo 2031435 47574701 := bstep (se 3 (by rfl) ⟨8920256, by rfl⟩ : syracuseStep 47574701 = 17840513) B17840513
theorem B31716467 : Blo 2031435 31716467 := bstep (se 1 (by rfl) ⟨23787350, by rfl⟩ : syracuseStep 31716467 = 47574701) B47574701
theorem B21144311 : Blo 2031435 21144311 := bstep (se 1 (by rfl) ⟨15858233, by rfl⟩ : syracuseStep 21144311 = 31716467) B31716467
theorem B14096207 : Blo 2031435 14096207 := bstep (se 1 (by rfl) ⟨10572155, by rfl⟩ : syracuseStep 14096207 = 21144311) B21144311
theorem B9397471 : Blo 2031435 9397471 := bstep (se 1 (by rfl) ⟨7048103, by rfl⟩ : syracuseStep 9397471 = 14096207) B14096207
theorem B12529961 : Blo 2031435 12529961 := bstep (se 2 (by rfl) ⟨4698735, by rfl⟩ : syracuseStep 12529961 = 9397471) B9397471
theorem B8353307 : Blo 2031435 8353307 := bstep (se 1 (by rfl) ⟨6264980, by rfl⟩ : syracuseStep 8353307 = 12529961) B12529961
theorem B22275485 : Blo 2031435 22275485 := bstep (se 3 (by rfl) ⟨4176653, by rfl⟩ : syracuseStep 22275485 = 8353307) B8353307
theorem B14850323 : Blo 2031435 14850323 := bstep (se 1 (by rfl) ⟨11137742, by rfl⟩ : syracuseStep 14850323 = 22275485) B22275485
theorem B9900215 : Blo 2031435 9900215 := bstep (se 1 (by rfl) ⟨7425161, by rfl⟩ : syracuseStep 9900215 = 14850323) B14850323
theorem B6600143 : Blo 2031435 6600143 := bstep (se 1 (by rfl) ⟨4950107, by rfl⟩ : syracuseStep 6600143 = 9900215) B9900215
theorem B17600381 : Blo 2031435 17600381 := bstep (se 3 (by rfl) ⟨3300071, by rfl⟩ : syracuseStep 17600381 = 6600143) B6600143
theorem B11733587 : Blo 2031435 11733587 := bstep (se 1 (by rfl) ⟨8800190, by rfl⟩ : syracuseStep 11733587 = 17600381) B17600381
theorem B7822391 : Blo 2031435 7822391 := bstep (se 1 (by rfl) ⟨5866793, by rfl⟩ : syracuseStep 7822391 = 11733587) B11733587
theorem B20859709 : Blo 2031435 20859709 := bstep (se 3 (by rfl) ⟨3911195, by rfl⟩ : syracuseStep 20859709 = 7822391) B7822391
theorem B27812945 : Blo 2031435 27812945 := bstep (se 2 (by rfl) ⟨10429854, by rfl⟩ : syracuseStep 27812945 = 20859709) B20859709
theorem B18541963 : Blo 2031435 18541963 := bstep (se 1 (by rfl) ⟨13906472, by rfl⟩ : syracuseStep 18541963 = 27812945) B27812945
theorem B98890469 : Blo 2031435 98890469 := bstep (se 4 (by rfl) ⟨9270981, by rfl⟩ : syracuseStep 98890469 = 18541963) B18541963
theorem B65926979 : Blo 2031435 65926979 := bstep (se 1 (by rfl) ⟨49445234, by rfl⟩ : syracuseStep 65926979 = 98890469) B98890469
theorem B43951319 : Blo 2031435 43951319 := bstep (se 1 (by rfl) ⟨32963489, by rfl⟩ : syracuseStep 43951319 = 65926979) B65926979
theorem B29300879 : Blo 2031435 29300879 := bstep (se 1 (by rfl) ⟨21975659, by rfl⟩ : syracuseStep 29300879 = 43951319) B43951319
theorem B19533919 : Blo 2031435 19533919 := bstep (se 1 (by rfl) ⟨14650439, by rfl⟩ : syracuseStep 19533919 = 29300879) B29300879
theorem B26045225 : Blo 2031435 26045225 := bstep (se 2 (by rfl) ⟨9766959, by rfl⟩ : syracuseStep 26045225 = 19533919) B19533919
theorem B17363483 : Blo 2031435 17363483 := bstep (se 1 (by rfl) ⟨13022612, by rfl⟩ : syracuseStep 17363483 = 26045225) B26045225
theorem B11575655 : Blo 2031435 11575655 := bstep (se 1 (by rfl) ⟨8681741, by rfl⟩ : syracuseStep 11575655 = 17363483) B17363483
theorem B7717103 : Blo 2031435 7717103 := bstep (se 1 (by rfl) ⟨5787827, by rfl⟩ : syracuseStep 7717103 = 11575655) B11575655
theorem B5144735 : Blo 2031435 5144735 := bstep (se 1 (by rfl) ⟨3858551, by rfl⟩ : syracuseStep 5144735 = 7717103) B7717103
theorem B3429823 : Blo 2031435 3429823 := bstep (se 1 (by rfl) ⟨2572367, by rfl⟩ : syracuseStep 3429823 = 5144735) B5144735
theorem B4573097 : Blo 2031435 4573097 := bstep (se 2 (by rfl) ⟨1714911, by rfl⟩ : syracuseStep 4573097 = 3429823) B3429823
theorem B3048731 : Blo 2031435 3048731 := bstep (se 1 (by rfl) ⟨2286548, by rfl⟩ : syracuseStep 3048731 = 4573097) B4573097
theorem B2032487 : Blo 2031435 2032487 := bstep (se 1 (by rfl) ⟨1524365, by rfl⟩ : syracuseStep 2032487 = 3048731) B3048731
theorem B2286553 : Blo 2031435 2286553 := bbase (se 2 (by rfl) ⟨857457, by rfl⟩ : syracuseStep 2286553 = 1714915) (by norm_num)
theorem B3048737 : Blo 2031435 3048737 := bstep (se 2 (by rfl) ⟨1143276, by rfl⟩ : syracuseStep 3048737 = 2286553) B2286553
theorem B2032491 : Blo 2031435 2032491 := bstep (se 1 (by rfl) ⟨1524368, by rfl⟩ : syracuseStep 2032491 = 3048737) B3048737
theorem B2893925 : Blo 2031435 2893925 := bbase (se 4 (by rfl) ⟨271305, by rfl⟩ : syracuseStep 2893925 = 542611) (by norm_num)
theorem B7717133 : Blo 2031435 7717133 := bstep (se 3 (by rfl) ⟨1446962, by rfl⟩ : syracuseStep 7717133 = 2893925) B2893925
theorem B5144755 : Blo 2031435 5144755 := bstep (se 1 (by rfl) ⟨3858566, by rfl⟩ : syracuseStep 5144755 = 7717133) B7717133
theorem B6859673 : Blo 2031435 6859673 := bstep (se 2 (by rfl) ⟨2572377, by rfl⟩ : syracuseStep 6859673 = 5144755) B5144755
theorem B4573115 : Blo 2031435 4573115 := bstep (se 1 (by rfl) ⟨3429836, by rfl⟩ : syracuseStep 4573115 = 6859673) B6859673
theorem B3048743 : Blo 2031435 3048743 := bstep (se 1 (by rfl) ⟨2286557, by rfl⟩ : syracuseStep 3048743 = 4573115) B4573115
theorem B2032495 : Blo 2031435 2032495 := bstep (se 1 (by rfl) ⟨1524371, by rfl⟩ : syracuseStep 2032495 = 3048743) B3048743
theorem B3048749 : Blo 2031435 3048749 := bbase (se 3 (by rfl) ⟨571640, by rfl⟩ : syracuseStep 3048749 = 1143281) (by norm_num)
theorem B2032499 : Blo 2031435 2032499 := bstep (se 1 (by rfl) ⟨1524374, by rfl⟩ : syracuseStep 2032499 = 3048749) B3048749
theorem B4573133 : Blo 2031435 4573133 := bbase (se 3 (by rfl) ⟨857462, by rfl⟩ : syracuseStep 4573133 = 1714925) (by norm_num)
theorem B3048755 : Blo 2031435 3048755 := bstep (se 1 (by rfl) ⟨2286566, by rfl⟩ : syracuseStep 3048755 = 4573133) B4573133
theorem B2032503 : Blo 2031435 2032503 := bstep (se 1 (by rfl) ⟨1524377, by rfl⟩ : syracuseStep 2032503 = 3048755) B3048755
theorem B2572393 : Blo 2031435 2572393 := bbase (se 2 (by rfl) ⟨964647, by rfl⟩ : syracuseStep 2572393 = 1929295) (by norm_num)
theorem B3429857 : Blo 2031435 3429857 := bstep (se 2 (by rfl) ⟨1286196, by rfl⟩ : syracuseStep 3429857 = 2572393) B2572393
theorem B2286571 : Blo 2031435 2286571 := bstep (se 1 (by rfl) ⟨1714928, by rfl⟩ : syracuseStep 2286571 = 3429857) B3429857
theorem B3048761 : Blo 2031435 3048761 := bstep (se 2 (by rfl) ⟨1143285, by rfl⟩ : syracuseStep 3048761 = 2286571) B2286571
theorem B2032507 : Blo 2031435 2032507 := bstep (se 1 (by rfl) ⟨1524380, by rfl⟩ : syracuseStep 2032507 = 3048761) B3048761
theorem B3662653 : Blo 2031435 3662653 := bbase (se 3 (by rfl) ⟨686747, by rfl⟩ : syracuseStep 3662653 = 1373495) (by norm_num)
theorem B4883537 : Blo 2031435 4883537 := bstep (se 2 (by rfl) ⟨1831326, by rfl⟩ : syracuseStep 4883537 = 3662653) B3662653
theorem B13022765 : Blo 2031435 13022765 := bstep (se 3 (by rfl) ⟨2441768, by rfl⟩ : syracuseStep 13022765 = 4883537) B4883537
theorem B8681843 : Blo 2031435 8681843 := bstep (se 1 (by rfl) ⟨6511382, by rfl⟩ : syracuseStep 8681843 = 13022765) B13022765
theorem B23151581 : Blo 2031435 23151581 := bstep (se 3 (by rfl) ⟨4340921, by rfl⟩ : syracuseStep 23151581 = 8681843) B8681843
theorem B15434387 : Blo 2031435 15434387 := bstep (se 1 (by rfl) ⟨11575790, by rfl⟩ : syracuseStep 15434387 = 23151581) B23151581
theorem B10289591 : Blo 2031435 10289591 := bstep (se 1 (by rfl) ⟨7717193, by rfl⟩ : syracuseStep 10289591 = 15434387) B15434387
theorem B6859727 : Blo 2031435 6859727 := bstep (se 1 (by rfl) ⟨5144795, by rfl⟩ : syracuseStep 6859727 = 10289591) B10289591
theorem B4573151 : Blo 2031435 4573151 := bstep (se 1 (by rfl) ⟨3429863, by rfl⟩ : syracuseStep 4573151 = 6859727) B6859727
theorem B3048767 : Blo 2031435 3048767 := bstep (se 1 (by rfl) ⟨2286575, by rfl⟩ : syracuseStep 3048767 = 4573151) B4573151
theorem B2032511 : Blo 2031435 2032511 := bstep (se 1 (by rfl) ⟨1524383, by rfl⟩ : syracuseStep 2032511 = 3048767) B3048767
theorem B3048773 : Blo 2031435 3048773 := bbase (se 4 (by rfl) ⟨285822, by rfl⟩ : syracuseStep 3048773 = 571645) (by norm_num)
theorem B2032515 : Blo 2031435 2032515 := bstep (se 1 (by rfl) ⟨1524386, by rfl⟩ : syracuseStep 2032515 = 3048773) B3048773
theorem B3429877 : Blo 2031435 3429877 := bbase (se 5 (by rfl) ⟨160775, by rfl⟩ : syracuseStep 3429877 = 321551) (by norm_num)
theorem B4573169 : Blo 2031435 4573169 := bstep (se 2 (by rfl) ⟨1714938, by rfl⟩ : syracuseStep 4573169 = 3429877) B3429877
theorem B3048779 : Blo 2031435 3048779 := bstep (se 1 (by rfl) ⟨2286584, by rfl⟩ : syracuseStep 3048779 = 4573169) B4573169
theorem B2032519 : Blo 2031435 2032519 := bstep (se 1 (by rfl) ⟨1524389, by rfl⟩ : syracuseStep 2032519 = 3048779) B3048779
theorem B2286589 : Blo 2031435 2286589 := bbase (se 3 (by rfl) ⟨428735, by rfl⟩ : syracuseStep 2286589 = 857471) (by norm_num)
theorem B3048785 : Blo 2031435 3048785 := bstep (se 2 (by rfl) ⟨1143294, by rfl⟩ : syracuseStep 3048785 = 2286589) B2286589
theorem B2032523 : Blo 2031435 2032523 := bstep (se 1 (by rfl) ⟨1524392, by rfl⟩ : syracuseStep 2032523 = 3048785) B3048785
theorem B6859781 : Blo 2031435 6859781 := bbase (se 4 (by rfl) ⟨643104, by rfl⟩ : syracuseStep 6859781 = 1286209) (by norm_num)
theorem B4573187 : Blo 2031435 4573187 := bstep (se 1 (by rfl) ⟨3429890, by rfl⟩ : syracuseStep 4573187 = 6859781) B6859781
theorem B3048791 : Blo 2031435 3048791 := bstep (se 1 (by rfl) ⟨2286593, by rfl⟩ : syracuseStep 3048791 = 4573187) B4573187
theorem B2032527 : Blo 2031435 2032527 := bstep (se 1 (by rfl) ⟨1524395, by rfl⟩ : syracuseStep 2032527 = 3048791) B3048791
theorem B3048797 : Blo 2031435 3048797 := bbase (se 3 (by rfl) ⟨571649, by rfl⟩ : syracuseStep 3048797 = 1143299) (by norm_num)
theorem B2032531 : Blo 2031435 2032531 := bstep (se 1 (by rfl) ⟨1524398, by rfl⟩ : syracuseStep 2032531 = 3048797) B3048797
theorem B4573205 : Blo 2031435 4573205 := bbase (se 6 (by rfl) ⟨107184, by rfl⟩ : syracuseStep 4573205 = 214369) (by norm_num)
theorem B3048803 : Blo 2031435 3048803 := bstep (se 1 (by rfl) ⟨2286602, by rfl⟩ : syracuseStep 3048803 = 4573205) B4573205
theorem B2032535 : Blo 2031435 2032535 := bstep (se 1 (by rfl) ⟨1524401, by rfl⟩ : syracuseStep 2032535 = 3048803) B3048803
theorem B7717301 : Blo 2031435 7717301 := bbase (se 5 (by rfl) ⟨361748, by rfl⟩ : syracuseStep 7717301 = 723497) (by norm_num)
theorem B5144867 : Blo 2031435 5144867 := bstep (se 1 (by rfl) ⟨3858650, by rfl⟩ : syracuseStep 5144867 = 7717301) B7717301
theorem B3429911 : Blo 2031435 3429911 := bstep (se 1 (by rfl) ⟨2572433, by rfl⟩ : syracuseStep 3429911 = 5144867) B5144867
theorem B2286607 : Blo 2031435 2286607 := bstep (se 1 (by rfl) ⟨1714955, by rfl⟩ : syracuseStep 2286607 = 3429911) B3429911
theorem B3048809 : Blo 2031435 3048809 := bstep (se 2 (by rfl) ⟨1143303, by rfl⟩ : syracuseStep 3048809 = 2286607) B2286607
theorem B2032539 : Blo 2031435 2032539 := bstep (se 1 (by rfl) ⟨1524404, by rfl⟩ : syracuseStep 2032539 = 3048809) B3048809
theorem B4950245 : Blo 2031435 4950245 := bbase (se 4 (by rfl) ⟨464085, by rfl⟩ : syracuseStep 4950245 = 928171) (by norm_num)
theorem B13200653 : Blo 2031435 13200653 := bstep (se 3 (by rfl) ⟨2475122, by rfl⟩ : syracuseStep 13200653 = 4950245) B4950245
theorem B8800435 : Blo 2031435 8800435 := bstep (se 1 (by rfl) ⟨6600326, by rfl⟩ : syracuseStep 8800435 = 13200653) B13200653
theorem B11733913 : Blo 2031435 11733913 := bstep (se 2 (by rfl) ⟨4400217, by rfl⟩ : syracuseStep 11733913 = 8800435) B8800435
theorem B62580869 : Blo 2031435 62580869 := bstep (se 4 (by rfl) ⟨5866956, by rfl⟩ : syracuseStep 62580869 = 11733913) B11733913
theorem B41720579 : Blo 2031435 41720579 := bstep (se 1 (by rfl) ⟨31290434, by rfl⟩ : syracuseStep 41720579 = 62580869) B62580869
theorem B27813719 : Blo 2031435 27813719 := bstep (se 1 (by rfl) ⟨20860289, by rfl⟩ : syracuseStep 27813719 = 41720579) B41720579
theorem B18542479 : Blo 2031435 18542479 := bstep (se 1 (by rfl) ⟨13906859, by rfl⟩ : syracuseStep 18542479 = 27813719) B27813719
theorem B24723305 : Blo 2031435 24723305 := bstep (se 2 (by rfl) ⟨9271239, by rfl⟩ : syracuseStep 24723305 = 18542479) B18542479
theorem B16482203 : Blo 2031435 16482203 := bstep (se 1 (by rfl) ⟨12361652, by rfl⟩ : syracuseStep 16482203 = 24723305) B24723305
theorem B10988135 : Blo 2031435 10988135 := bstep (se 1 (by rfl) ⟨8241101, by rfl⟩ : syracuseStep 10988135 = 16482203) B16482203
theorem B7325423 : Blo 2031435 7325423 := bstep (se 1 (by rfl) ⟨5494067, by rfl⟩ : syracuseStep 7325423 = 10988135) B10988135
theorem B4883615 : Blo 2031435 4883615 := bstep (se 1 (by rfl) ⟨3662711, by rfl⟩ : syracuseStep 4883615 = 7325423) B7325423
theorem B3255743 : Blo 2031435 3255743 := bstep (se 1 (by rfl) ⟨2441807, by rfl⟩ : syracuseStep 3255743 = 4883615) B4883615
theorem B2170495 : Blo 2031435 2170495 := bstep (se 1 (by rfl) ⟨1627871, by rfl⟩ : syracuseStep 2170495 = 3255743) B3255743
theorem B11575973 : Blo 2031435 11575973 := bstep (se 4 (by rfl) ⟨1085247, by rfl⟩ : syracuseStep 11575973 = 2170495) B2170495
theorem B7717315 : Blo 2031435 7717315 := bstep (se 1 (by rfl) ⟨5787986, by rfl⟩ : syracuseStep 7717315 = 11575973) B11575973
theorem B10289753 : Blo 2031435 10289753 := bstep (se 2 (by rfl) ⟨3858657, by rfl⟩ : syracuseStep 10289753 = 7717315) B7717315
theorem B6859835 : Blo 2031435 6859835 := bstep (se 1 (by rfl) ⟨5144876, by rfl⟩ : syracuseStep 6859835 = 10289753) B10289753
theorem B4573223 : Blo 2031435 4573223 := bstep (se 1 (by rfl) ⟨3429917, by rfl⟩ : syracuseStep 4573223 = 6859835) B6859835
theorem B3048815 : Blo 2031435 3048815 := bstep (se 1 (by rfl) ⟨2286611, by rfl⟩ : syracuseStep 3048815 = 4573223) B4573223
theorem B2032543 : Blo 2031435 2032543 := bstep (se 1 (by rfl) ⟨1524407, by rfl⟩ : syracuseStep 2032543 = 3048815) B3048815
theorem B3048821 : Blo 2031435 3048821 := bbase (se 5 (by rfl) ⟨142913, by rfl⟩ : syracuseStep 3048821 = 285827) (by norm_num)
theorem B2032547 : Blo 2031435 2032547 := bstep (se 1 (by rfl) ⟨1524410, by rfl⟩ : syracuseStep 2032547 = 3048821) B3048821
theorem B2894005 : Blo 2031435 2894005 := bbase (se 5 (by rfl) ⟨135656, by rfl⟩ : syracuseStep 2894005 = 271313) (by norm_num)
theorem B3858673 : Blo 2031435 3858673 := bstep (se 2 (by rfl) ⟨1447002, by rfl⟩ : syracuseStep 3858673 = 2894005) B2894005
theorem B5144897 : Blo 2031435 5144897 := bstep (se 2 (by rfl) ⟨1929336, by rfl⟩ : syracuseStep 5144897 = 3858673) B3858673
theorem B3429931 : Blo 2031435 3429931 := bstep (se 1 (by rfl) ⟨2572448, by rfl⟩ : syracuseStep 3429931 = 5144897) B5144897
theorem B4573241 : Blo 2031435 4573241 := bstep (se 2 (by rfl) ⟨1714965, by rfl⟩ : syracuseStep 4573241 = 3429931) B3429931
theorem B3048827 : Blo 2031435 3048827 := bstep (se 1 (by rfl) ⟨2286620, by rfl⟩ : syracuseStep 3048827 = 4573241) B4573241
theorem B2032551 : Blo 2031435 2032551 := bstep (se 1 (by rfl) ⟨1524413, by rfl⟩ : syracuseStep 2032551 = 3048827) B3048827
theorem B2286625 : Blo 2031435 2286625 := bbase (se 2 (by rfl) ⟨857484, by rfl⟩ : syracuseStep 2286625 = 1714969) (by norm_num)
theorem B3048833 : Blo 2031435 3048833 := bstep (se 2 (by rfl) ⟨1143312, by rfl⟩ : syracuseStep 3048833 = 2286625) B2286625
theorem B2032555 : Blo 2031435 2032555 := bstep (se 1 (by rfl) ⟨1524416, by rfl⟩ : syracuseStep 2032555 = 3048833) B3048833
theorem B5144917 : Blo 2031435 5144917 := bbase (se 10 (by rfl) ⟨7536, by rfl⟩ : syracuseStep 5144917 = 15073) (by norm_num)
theorem B6859889 : Blo 2031435 6859889 := bstep (se 2 (by rfl) ⟨2572458, by rfl⟩ : syracuseStep 6859889 = 5144917) B5144917
theorem B4573259 : Blo 2031435 4573259 := bstep (se 1 (by rfl) ⟨3429944, by rfl⟩ : syracuseStep 4573259 = 6859889) B6859889
theorem B3048839 : Blo 2031435 3048839 := bstep (se 1 (by rfl) ⟨2286629, by rfl⟩ : syracuseStep 3048839 = 4573259) B4573259
theorem B2032559 : Blo 2031435 2032559 := bstep (se 1 (by rfl) ⟨1524419, by rfl⟩ : syracuseStep 2032559 = 3048839) B3048839
theorem B3048845 : Blo 2031435 3048845 := bbase (se 3 (by rfl) ⟨571658, by rfl⟩ : syracuseStep 3048845 = 1143317) (by norm_num)
theorem B2032563 : Blo 2031435 2032563 := bstep (se 1 (by rfl) ⟨1524422, by rfl⟩ : syracuseStep 2032563 = 3048845) B3048845
theorem B4573277 : Blo 2031435 4573277 := bbase (se 3 (by rfl) ⟨857489, by rfl⟩ : syracuseStep 4573277 = 1714979) (by norm_num)
theorem B3048851 : Blo 2031435 3048851 := bstep (se 1 (by rfl) ⟨2286638, by rfl⟩ : syracuseStep 3048851 = 4573277) B4573277
theorem B2032567 : Blo 2031435 2032567 := bstep (se 1 (by rfl) ⟨1524425, by rfl⟩ : syracuseStep 2032567 = 3048851) B3048851
theorem B3429965 : Blo 2031435 3429965 := bbase (se 3 (by rfl) ⟨643118, by rfl⟩ : syracuseStep 3429965 = 1286237) (by norm_num)
theorem B2286643 : Blo 2031435 2286643 := bstep (se 1 (by rfl) ⟨1714982, by rfl⟩ : syracuseStep 2286643 = 3429965) B3429965
theorem B3048857 : Blo 2031435 3048857 := bstep (se 2 (by rfl) ⟨1143321, by rfl⟩ : syracuseStep 3048857 = 2286643) B2286643
theorem B2032571 : Blo 2031435 2032571 := bstep (se 1 (by rfl) ⟨1524428, by rfl⟩ : syracuseStep 2032571 = 3048857) B3048857
theorem B3911365 : Blo 2031435 3911365 := bbase (se 4 (by rfl) ⟨366690, by rfl⟩ : syracuseStep 3911365 = 733381) (by norm_num)
theorem B5215153 : Blo 2031435 5215153 := bstep (se 2 (by rfl) ⟨1955682, by rfl⟩ : syracuseStep 5215153 = 3911365) B3911365
theorem B6953537 : Blo 2031435 6953537 := bstep (se 2 (by rfl) ⟨2607576, by rfl⟩ : syracuseStep 6953537 = 5215153) B5215153
theorem B18542765 : Blo 2031435 18542765 := bstep (se 3 (by rfl) ⟨3476768, by rfl⟩ : syracuseStep 18542765 = 6953537) B6953537
theorem B12361843 : Blo 2031435 12361843 := bstep (se 1 (by rfl) ⟨9271382, by rfl⟩ : syracuseStep 12361843 = 18542765) B18542765
theorem B16482457 : Blo 2031435 16482457 := bstep (se 2 (by rfl) ⟨6180921, by rfl⟩ : syracuseStep 16482457 = 12361843) B12361843
theorem B21976609 : Blo 2031435 21976609 := bstep (se 2 (by rfl) ⟨8241228, by rfl⟩ : syracuseStep 21976609 = 16482457) B16482457
theorem B29302145 : Blo 2031435 29302145 := bstep (se 2 (by rfl) ⟨10988304, by rfl⟩ : syracuseStep 29302145 = 21976609) B21976609
theorem B19534763 : Blo 2031435 19534763 := bstep (se 1 (by rfl) ⟨14651072, by rfl⟩ : syracuseStep 19534763 = 29302145) B29302145
theorem B13023175 : Blo 2031435 13023175 := bstep (se 1 (by rfl) ⟨9767381, by rfl⟩ : syracuseStep 13023175 = 19534763) B19534763
theorem B17364233 : Blo 2031435 17364233 := bstep (se 2 (by rfl) ⟨6511587, by rfl⟩ : syracuseStep 17364233 = 13023175) B13023175
theorem B11576155 : Blo 2031435 11576155 := bstep (se 1 (by rfl) ⟨8682116, by rfl⟩ : syracuseStep 11576155 = 17364233) B17364233
theorem B15434873 : Blo 2031435 15434873 := bstep (se 2 (by rfl) ⟨5788077, by rfl⟩ : syracuseStep 15434873 = 11576155) B11576155
theorem B10289915 : Blo 2031435 10289915 := bstep (se 1 (by rfl) ⟨7717436, by rfl⟩ : syracuseStep 10289915 = 15434873) B15434873
theorem B6859943 : Blo 2031435 6859943 := bstep (se 1 (by rfl) ⟨5144957, by rfl⟩ : syracuseStep 6859943 = 10289915) B10289915
theorem B4573295 : Blo 2031435 4573295 := bstep (se 1 (by rfl) ⟨3429971, by rfl⟩ : syracuseStep 4573295 = 6859943) B6859943
theorem B3048863 : Blo 2031435 3048863 := bstep (se 1 (by rfl) ⟨2286647, by rfl⟩ : syracuseStep 3048863 = 4573295) B4573295
theorem B2032575 : Blo 2031435 2032575 := bstep (se 1 (by rfl) ⟨1524431, by rfl⟩ : syracuseStep 2032575 = 3048863) B3048863
theorem B3048869 : Blo 2031435 3048869 := bbase (se 4 (by rfl) ⟨285831, by rfl⟩ : syracuseStep 3048869 = 571663) (by norm_num)
theorem B2032579 : Blo 2031435 2032579 := bstep (se 1 (by rfl) ⟨1524434, by rfl⟩ : syracuseStep 2032579 = 3048869) B3048869
theorem B2572489 : Blo 2031435 2572489 := bbase (se 2 (by rfl) ⟨964683, by rfl⟩ : syracuseStep 2572489 = 1929367) (by norm_num)
theorem B3429985 : Blo 2031435 3429985 := bstep (se 2 (by rfl) ⟨1286244, by rfl⟩ : syracuseStep 3429985 = 2572489) B2572489
theorem B4573313 : Blo 2031435 4573313 := bstep (se 2 (by rfl) ⟨1714992, by rfl⟩ : syracuseStep 4573313 = 3429985) B3429985
theorem B3048875 : Blo 2031435 3048875 := bstep (se 1 (by rfl) ⟨2286656, by rfl⟩ : syracuseStep 3048875 = 4573313) B4573313
theorem B2032583 : Blo 2031435 2032583 := bstep (se 1 (by rfl) ⟨1524437, by rfl⟩ : syracuseStep 2032583 = 3048875) B3048875
theorem B2286661 : Blo 2031435 2286661 := bbase (se 4 (by rfl) ⟨214374, by rfl⟩ : syracuseStep 2286661 = 428749) (by norm_num)
theorem B3048881 : Blo 2031435 3048881 := bstep (se 2 (by rfl) ⟨1143330, by rfl⟩ : syracuseStep 3048881 = 2286661) B2286661
theorem B2032587 : Blo 2031435 2032587 := bstep (se 1 (by rfl) ⟨1524440, by rfl⟩ : syracuseStep 2032587 = 3048881) B3048881
theorem B3858749 : Blo 2031435 3858749 := bbase (se 3 (by rfl) ⟨723515, by rfl⟩ : syracuseStep 3858749 = 1447031) (by norm_num)
theorem B2572499 : Blo 2031435 2572499 := bstep (se 1 (by rfl) ⟨1929374, by rfl⟩ : syracuseStep 2572499 = 3858749) B3858749
theorem B6859997 : Blo 2031435 6859997 := bstep (se 3 (by rfl) ⟨1286249, by rfl⟩ : syracuseStep 6859997 = 2572499) B2572499
theorem B4573331 : Blo 2031435 4573331 := bstep (se 1 (by rfl) ⟨3429998, by rfl⟩ : syracuseStep 4573331 = 6859997) B6859997
theorem B3048887 : Blo 2031435 3048887 := bstep (se 1 (by rfl) ⟨2286665, by rfl⟩ : syracuseStep 3048887 = 4573331) B4573331
theorem B2032591 : Blo 2031435 2032591 := bstep (se 1 (by rfl) ⟨1524443, by rfl⟩ : syracuseStep 2032591 = 3048887) B3048887
theorem B3048893 : Blo 2031435 3048893 := bbase (se 3 (by rfl) ⟨571667, by rfl⟩ : syracuseStep 3048893 = 1143335) (by norm_num)
theorem B2032595 : Blo 2031435 2032595 := bstep (se 1 (by rfl) ⟨1524446, by rfl⟩ : syracuseStep 2032595 = 3048893) B3048893
theorem B4573349 : Blo 2031435 4573349 := bbase (se 4 (by rfl) ⟨428751, by rfl⟩ : syracuseStep 4573349 = 857503) (by norm_num)
theorem B3048899 : Blo 2031435 3048899 := bstep (se 1 (by rfl) ⟨2286674, by rfl⟩ : syracuseStep 3048899 = 4573349) B4573349
theorem B2032599 : Blo 2031435 2032599 := bstep (se 1 (by rfl) ⟨1524449, by rfl⟩ : syracuseStep 2032599 = 3048899) B3048899
theorem B5145029 : Blo 2031435 5145029 := bbase (se 4 (by rfl) ⟨482346, by rfl⟩ : syracuseStep 5145029 = 964693) (by norm_num)
theorem B3430019 : Blo 2031435 3430019 := bstep (se 1 (by rfl) ⟨2572514, by rfl⟩ : syracuseStep 3430019 = 5145029) B5145029
theorem B2286679 : Blo 2031435 2286679 := bstep (se 1 (by rfl) ⟨1715009, by rfl⟩ : syracuseStep 2286679 = 3430019) B3430019
theorem B3048905 : Blo 2031435 3048905 := bstep (se 2 (by rfl) ⟨1143339, by rfl⟩ : syracuseStep 3048905 = 2286679) B2286679
theorem B2032603 : Blo 2031435 2032603 := bstep (se 1 (by rfl) ⟨1524452, by rfl⟩ : syracuseStep 2032603 = 3048905) B3048905
theorem B7325653 : Blo 2031435 7325653 := bbase (se 7 (by rfl) ⟨85847, by rfl⟩ : syracuseStep 7325653 = 171695) (by norm_num)
theorem B9767537 : Blo 2031435 9767537 := bstep (se 2 (by rfl) ⟨3662826, by rfl⟩ : syracuseStep 9767537 = 7325653) B7325653
theorem B6511691 : Blo 2031435 6511691 := bstep (se 1 (by rfl) ⟨4883768, by rfl⟩ : syracuseStep 6511691 = 9767537) B9767537
theorem B4341127 : Blo 2031435 4341127 := bstep (se 1 (by rfl) ⟨3255845, by rfl⟩ : syracuseStep 4341127 = 6511691) B6511691
theorem B5788169 : Blo 2031435 5788169 := bstep (se 2 (by rfl) ⟨2170563, by rfl⟩ : syracuseStep 5788169 = 4341127) B4341127
theorem B3858779 : Blo 2031435 3858779 := bstep (se 1 (by rfl) ⟨2894084, by rfl⟩ : syracuseStep 3858779 = 5788169) B5788169
theorem B10290077 : Blo 2031435 10290077 := bstep (se 3 (by rfl) ⟨1929389, by rfl⟩ : syracuseStep 10290077 = 3858779) B3858779
theorem B6860051 : Blo 2031435 6860051 := bstep (se 1 (by rfl) ⟨5145038, by rfl⟩ : syracuseStep 6860051 = 10290077) B10290077
theorem B4573367 : Blo 2031435 4573367 := bstep (se 1 (by rfl) ⟨3430025, by rfl⟩ : syracuseStep 4573367 = 6860051) B6860051
theorem B3048911 : Blo 2031435 3048911 := bstep (se 1 (by rfl) ⟨2286683, by rfl⟩ : syracuseStep 3048911 = 4573367) B4573367
theorem B2032607 : Blo 2031435 2032607 := bstep (se 1 (by rfl) ⟨1524455, by rfl⟩ : syracuseStep 2032607 = 3048911) B3048911
theorem B3048917 : Blo 2031435 3048917 := bbase (se 7 (by rfl) ⟨35729, by rfl⟩ : syracuseStep 3048917 = 71459) (by norm_num)
theorem B2032611 : Blo 2031435 2032611 := bstep (se 1 (by rfl) ⟨1524458, by rfl⟩ : syracuseStep 2032611 = 3048917) B3048917
theorem B7717589 : Blo 2031435 7717589 := bbase (se 7 (by rfl) ⟨90440, by rfl⟩ : syracuseStep 7717589 = 180881) (by norm_num)
theorem B5145059 : Blo 2031435 5145059 := bstep (se 1 (by rfl) ⟨3858794, by rfl⟩ : syracuseStep 5145059 = 7717589) B7717589
theorem B3430039 : Blo 2031435 3430039 := bstep (se 1 (by rfl) ⟨2572529, by rfl⟩ : syracuseStep 3430039 = 5145059) B5145059
theorem B4573385 : Blo 2031435 4573385 := bstep (se 2 (by rfl) ⟨1715019, by rfl⟩ : syracuseStep 4573385 = 3430039) B3430039
theorem B3048923 : Blo 2031435 3048923 := bstep (se 1 (by rfl) ⟨2286692, by rfl⟩ : syracuseStep 3048923 = 4573385) B4573385
theorem B2032615 : Blo 2031435 2032615 := bstep (se 1 (by rfl) ⟨1524461, by rfl⟩ : syracuseStep 2032615 = 3048923) B3048923
theorem B2286697 : Blo 2031435 2286697 := bbase (se 2 (by rfl) ⟨857511, by rfl⟩ : syracuseStep 2286697 = 1715023) (by norm_num)
theorem B3048929 : Blo 2031435 3048929 := bstep (se 2 (by rfl) ⟨1143348, by rfl⟩ : syracuseStep 3048929 = 2286697) B2286697
theorem B2032619 : Blo 2031435 2032619 := bstep (se 1 (by rfl) ⟨1524464, by rfl⟩ : syracuseStep 2032619 = 3048929) B3048929
theorem B2317901 : Blo 2031435 2317901 := bbase (se 3 (by rfl) ⟨434606, by rfl⟩ : syracuseStep 2317901 = 869213) (by norm_num)
theorem B24724277 : Blo 2031435 24724277 := bstep (se 5 (by rfl) ⟨1158950, by rfl⟩ : syracuseStep 24724277 = 2317901) B2317901
theorem B16482851 : Blo 2031435 16482851 := bstep (se 1 (by rfl) ⟨12362138, by rfl⟩ : syracuseStep 16482851 = 24724277) B24724277
theorem B10988567 : Blo 2031435 10988567 := bstep (se 1 (by rfl) ⟨8241425, by rfl⟩ : syracuseStep 10988567 = 16482851) B16482851
theorem B7325711 : Blo 2031435 7325711 := bstep (se 1 (by rfl) ⟨5494283, by rfl⟩ : syracuseStep 7325711 = 10988567) B10988567
theorem B4883807 : Blo 2031435 4883807 := bstep (se 1 (by rfl) ⟨3662855, by rfl⟩ : syracuseStep 4883807 = 7325711) B7325711
theorem B3255871 : Blo 2031435 3255871 := bstep (se 1 (by rfl) ⟨2441903, by rfl⟩ : syracuseStep 3255871 = 4883807) B4883807
theorem B4341161 : Blo 2031435 4341161 := bstep (se 2 (by rfl) ⟨1627935, by rfl⟩ : syracuseStep 4341161 = 3255871) B3255871
theorem B11576429 : Blo 2031435 11576429 := bstep (se 3 (by rfl) ⟨2170580, by rfl⟩ : syracuseStep 11576429 = 4341161) B4341161
theorem B7717619 : Blo 2031435 7717619 := bstep (se 1 (by rfl) ⟨5788214, by rfl⟩ : syracuseStep 7717619 = 11576429) B11576429
theorem B5145079 : Blo 2031435 5145079 := bstep (se 1 (by rfl) ⟨3858809, by rfl⟩ : syracuseStep 5145079 = 7717619) B7717619
theorem B6860105 : Blo 2031435 6860105 := bstep (se 2 (by rfl) ⟨2572539, by rfl⟩ : syracuseStep 6860105 = 5145079) B5145079
theorem B4573403 : Blo 2031435 4573403 := bstep (se 1 (by rfl) ⟨3430052, by rfl⟩ : syracuseStep 4573403 = 6860105) B6860105
theorem B3048935 : Blo 2031435 3048935 := bstep (se 1 (by rfl) ⟨2286701, by rfl⟩ : syracuseStep 3048935 = 4573403) B4573403
theorem B2032623 : Blo 2031435 2032623 := bstep (se 1 (by rfl) ⟨1524467, by rfl⟩ : syracuseStep 2032623 = 3048935) B3048935
theorem B3048941 : Blo 2031435 3048941 := bbase (se 3 (by rfl) ⟨571676, by rfl⟩ : syracuseStep 3048941 = 1143353) (by norm_num)
theorem B2032627 : Blo 2031435 2032627 := bstep (se 1 (by rfl) ⟨1524470, by rfl⟩ : syracuseStep 2032627 = 3048941) B3048941
theorem B4573421 : Blo 2031435 4573421 := bbase (se 3 (by rfl) ⟨857516, by rfl⟩ : syracuseStep 4573421 = 1715033) (by norm_num)
theorem B3048947 : Blo 2031435 3048947 := bstep (se 1 (by rfl) ⟨2286710, by rfl⟩ : syracuseStep 3048947 = 4573421) B4573421
theorem B2032631 : Blo 2031435 2032631 := bstep (se 1 (by rfl) ⟨1524473, by rfl⟩ : syracuseStep 2032631 = 3048947) B3048947
theorem B2894125 : Blo 2031435 2894125 := bbase (se 3 (by rfl) ⟨542648, by rfl⟩ : syracuseStep 2894125 = 1085297) (by norm_num)
theorem B3858833 : Blo 2031435 3858833 := bstep (se 2 (by rfl) ⟨1447062, by rfl⟩ : syracuseStep 3858833 = 2894125) B2894125
theorem B2572555 : Blo 2031435 2572555 := bstep (se 1 (by rfl) ⟨1929416, by rfl⟩ : syracuseStep 2572555 = 3858833) B3858833
theorem B3430073 : Blo 2031435 3430073 := bstep (se 2 (by rfl) ⟨1286277, by rfl⟩ : syracuseStep 3430073 = 2572555) B2572555
theorem B2286715 : Blo 2031435 2286715 := bstep (se 1 (by rfl) ⟨1715036, by rfl⟩ : syracuseStep 2286715 = 3430073) B3430073
theorem B3048953 : Blo 2031435 3048953 := bstep (se 2 (by rfl) ⟨1143357, by rfl⟩ : syracuseStep 3048953 = 2286715) B2286715
theorem B2032635 : Blo 2031435 2032635 := bstep (se 1 (by rfl) ⟨1524476, by rfl⟩ : syracuseStep 2032635 = 3048953) B3048953
theorem B5494325 : Blo 2031435 5494325 := bbase (se 5 (by rfl) ⟨257546, by rfl⟩ : syracuseStep 5494325 = 515093) (by norm_num)
theorem B14651533 : Blo 2031435 14651533 := bstep (se 3 (by rfl) ⟨2747162, by rfl⟩ : syracuseStep 14651533 = 5494325) B5494325
theorem B78141509 : Blo 2031435 78141509 := bstep (se 4 (by rfl) ⟨7325766, by rfl⟩ : syracuseStep 78141509 = 14651533) B14651533
theorem B52094339 : Blo 2031435 52094339 := bstep (se 1 (by rfl) ⟨39070754, by rfl⟩ : syracuseStep 52094339 = 78141509) B78141509
theorem B34729559 : Blo 2031435 34729559 := bstep (se 1 (by rfl) ⟨26047169, by rfl⟩ : syracuseStep 34729559 = 52094339) B52094339
theorem B23153039 : Blo 2031435 23153039 := bstep (se 1 (by rfl) ⟨17364779, by rfl⟩ : syracuseStep 23153039 = 34729559) B34729559
theorem B15435359 : Blo 2031435 15435359 := bstep (se 1 (by rfl) ⟨11576519, by rfl⟩ : syracuseStep 15435359 = 23153039) B23153039
theorem B10290239 : Blo 2031435 10290239 := bstep (se 1 (by rfl) ⟨7717679, by rfl⟩ : syracuseStep 10290239 = 15435359) B15435359
theorem B6860159 : Blo 2031435 6860159 := bstep (se 1 (by rfl) ⟨5145119, by rfl⟩ : syracuseStep 6860159 = 10290239) B10290239
theorem B4573439 : Blo 2031435 4573439 := bstep (se 1 (by rfl) ⟨3430079, by rfl⟩ : syracuseStep 4573439 = 6860159) B6860159
theorem B3048959 : Blo 2031435 3048959 := bstep (se 1 (by rfl) ⟨2286719, by rfl⟩ : syracuseStep 3048959 = 4573439) B4573439
theorem B2032639 : Blo 2031435 2032639 := bstep (se 1 (by rfl) ⟨1524479, by rfl⟩ : syracuseStep 2032639 = 3048959) B3048959
theorem B3048965 : Blo 2031435 3048965 := bbase (se 4 (by rfl) ⟨285840, by rfl⟩ : syracuseStep 3048965 = 571681) (by norm_num)
theorem B2032643 : Blo 2031435 2032643 := bstep (se 1 (by rfl) ⟨1524482, by rfl⟩ : syracuseStep 2032643 = 3048965) B3048965
theorem B3430093 : Blo 2031435 3430093 := bbase (se 3 (by rfl) ⟨643142, by rfl⟩ : syracuseStep 3430093 = 1286285) (by norm_num)
theorem B4573457 : Blo 2031435 4573457 := bstep (se 2 (by rfl) ⟨1715046, by rfl⟩ : syracuseStep 4573457 = 3430093) B3430093
theorem B3048971 : Blo 2031435 3048971 := bstep (se 1 (by rfl) ⟨2286728, by rfl⟩ : syracuseStep 3048971 = 4573457) B4573457
theorem B2032647 : Blo 2031435 2032647 := bstep (se 1 (by rfl) ⟨1524485, by rfl⟩ : syracuseStep 2032647 = 3048971) B3048971
theorem B2286733 : Blo 2031435 2286733 := bbase (se 3 (by rfl) ⟨428762, by rfl⟩ : syracuseStep 2286733 = 857525) (by norm_num)
theorem B3048977 : Blo 2031435 3048977 := bstep (se 2 (by rfl) ⟨1143366, by rfl⟩ : syracuseStep 3048977 = 2286733) B2286733
theorem B2032651 : Blo 2031435 2032651 := bstep (se 1 (by rfl) ⟨1524488, by rfl⟩ : syracuseStep 2032651 = 3048977) B3048977
theorem B6860213 : Blo 2031435 6860213 := bbase (se 5 (by rfl) ⟨321572, by rfl⟩ : syracuseStep 6860213 = 643145) (by norm_num)
theorem B4573475 : Blo 2031435 4573475 := bstep (se 1 (by rfl) ⟨3430106, by rfl⟩ : syracuseStep 4573475 = 6860213) B6860213
theorem B3048983 : Blo 2031435 3048983 := bstep (se 1 (by rfl) ⟨2286737, by rfl⟩ : syracuseStep 3048983 = 4573475) B4573475
theorem B2032655 : Blo 2031435 2032655 := bstep (se 1 (by rfl) ⟨1524491, by rfl⟩ : syracuseStep 2032655 = 3048983) B3048983
theorem B3048989 : Blo 2031435 3048989 := bbase (se 3 (by rfl) ⟨571685, by rfl⟩ : syracuseStep 3048989 = 1143371) (by norm_num)
theorem B2032659 : Blo 2031435 2032659 := bstep (se 1 (by rfl) ⟨1524494, by rfl⟩ : syracuseStep 2032659 = 3048989) B3048989
theorem B4573493 : Blo 2031435 4573493 := bbase (se 5 (by rfl) ⟨214382, by rfl⟩ : syracuseStep 4573493 = 428765) (by norm_num)
theorem B3048995 : Blo 2031435 3048995 := bstep (se 1 (by rfl) ⟨2286746, by rfl⟩ : syracuseStep 3048995 = 4573493) B4573493
theorem B2032663 : Blo 2031435 2032663 := bstep (se 1 (by rfl) ⟨1524497, by rfl⟩ : syracuseStep 2032663 = 3048995) B3048995
theorem B2060401 : Blo 2031435 2060401 := bbase (se 2 (by rfl) ⟨772650, by rfl⟩ : syracuseStep 2060401 = 1545301) (by norm_num)
theorem B2747201 : Blo 2031435 2747201 := bstep (se 2 (by rfl) ⟨1030200, by rfl⟩ : syracuseStep 2747201 = 2060401) B2060401
theorem B29303477 : Blo 2031435 29303477 := bstep (se 5 (by rfl) ⟨1373600, by rfl⟩ : syracuseStep 29303477 = 2747201) B2747201
theorem B19535651 : Blo 2031435 19535651 := bstep (se 1 (by rfl) ⟨14651738, by rfl⟩ : syracuseStep 19535651 = 29303477) B29303477
theorem B13023767 : Blo 2031435 13023767 := bstep (se 1 (by rfl) ⟨9767825, by rfl⟩ : syracuseStep 13023767 = 19535651) B19535651
theorem B8682511 : Blo 2031435 8682511 := bstep (se 1 (by rfl) ⟨6511883, by rfl⟩ : syracuseStep 8682511 = 13023767) B13023767
theorem B11576681 : Blo 2031435 11576681 := bstep (se 2 (by rfl) ⟨4341255, by rfl⟩ : syracuseStep 11576681 = 8682511) B8682511
theorem B7717787 : Blo 2031435 7717787 := bstep (se 1 (by rfl) ⟨5788340, by rfl⟩ : syracuseStep 7717787 = 11576681) B11576681
theorem B5145191 : Blo 2031435 5145191 := bstep (se 1 (by rfl) ⟨3858893, by rfl⟩ : syracuseStep 5145191 = 7717787) B7717787
theorem B3430127 : Blo 2031435 3430127 := bstep (se 1 (by rfl) ⟨2572595, by rfl⟩ : syracuseStep 3430127 = 5145191) B5145191
theorem B2286751 : Blo 2031435 2286751 := bstep (se 1 (by rfl) ⟨1715063, by rfl⟩ : syracuseStep 2286751 = 3430127) B3430127
theorem B3049001 : Blo 2031435 3049001 := bstep (se 2 (by rfl) ⟨1143375, by rfl⟩ : syracuseStep 3049001 = 2286751) B2286751
theorem B2032667 : Blo 2031435 2032667 := bstep (se 1 (by rfl) ⟨1524500, by rfl⟩ : syracuseStep 2032667 = 3049001) B3049001
theorem B28194965 : Blo 2031435 28194965 := bbase (se 6 (by rfl) ⟨660819, by rfl⟩ : syracuseStep 28194965 = 1321639) (by norm_num)
theorem B18796643 : Blo 2031435 18796643 := bstep (se 1 (by rfl) ⟨14097482, by rfl⟩ : syracuseStep 18796643 = 28194965) B28194965
theorem B12531095 : Blo 2031435 12531095 := bstep (se 1 (by rfl) ⟨9398321, by rfl⟩ : syracuseStep 12531095 = 18796643) B18796643
theorem B8354063 : Blo 2031435 8354063 := bstep (se 1 (by rfl) ⟨6265547, by rfl⟩ : syracuseStep 8354063 = 12531095) B12531095
theorem B22277501 : Blo 2031435 22277501 := bstep (se 3 (by rfl) ⟨4177031, by rfl⟩ : syracuseStep 22277501 = 8354063) B8354063
theorem B14851667 : Blo 2031435 14851667 := bstep (se 1 (by rfl) ⟨11138750, by rfl⟩ : syracuseStep 14851667 = 22277501) B22277501
theorem B9901111 : Blo 2031435 9901111 := bstep (se 1 (by rfl) ⟨7425833, by rfl⟩ : syracuseStep 9901111 = 14851667) B14851667
theorem B13201481 : Blo 2031435 13201481 := bstep (se 2 (by rfl) ⟨4950555, by rfl⟩ : syracuseStep 13201481 = 9901111) B9901111
theorem B8800987 : Blo 2031435 8800987 := bstep (se 1 (by rfl) ⟨6600740, by rfl⟩ : syracuseStep 8800987 = 13201481) B13201481
theorem B11734649 : Blo 2031435 11734649 := bstep (se 2 (by rfl) ⟨4400493, by rfl⟩ : syracuseStep 11734649 = 8800987) B8800987
theorem B7823099 : Blo 2031435 7823099 := bstep (se 1 (by rfl) ⟨5867324, by rfl⟩ : syracuseStep 7823099 = 11734649) B11734649
theorem B20861597 : Blo 2031435 20861597 := bstep (se 3 (by rfl) ⟨3911549, by rfl⟩ : syracuseStep 20861597 = 7823099) B7823099
theorem B55630925 : Blo 2031435 55630925 := bstep (se 3 (by rfl) ⟨10430798, by rfl⟩ : syracuseStep 55630925 = 20861597) B20861597
theorem B37087283 : Blo 2031435 37087283 := bstep (se 1 (by rfl) ⟨27815462, by rfl⟩ : syracuseStep 37087283 = 55630925) B55630925
theorem B24724855 : Blo 2031435 24724855 := bstep (se 1 (by rfl) ⟨18543641, by rfl⟩ : syracuseStep 24724855 = 37087283) B37087283
theorem B32966473 : Blo 2031435 32966473 := bstep (se 2 (by rfl) ⟨12362427, by rfl⟩ : syracuseStep 32966473 = 24724855) B24724855
theorem B43955297 : Blo 2031435 43955297 := bstep (se 2 (by rfl) ⟨16483236, by rfl⟩ : syracuseStep 43955297 = 32966473) B32966473
theorem B29303531 : Blo 2031435 29303531 := bstep (se 1 (by rfl) ⟨21977648, by rfl⟩ : syracuseStep 29303531 = 43955297) B43955297
theorem B19535687 : Blo 2031435 19535687 := bstep (se 1 (by rfl) ⟨14651765, by rfl⟩ : syracuseStep 19535687 = 29303531) B29303531
theorem B13023791 : Blo 2031435 13023791 := bstep (se 1 (by rfl) ⟨9767843, by rfl⟩ : syracuseStep 13023791 = 19535687) B19535687
theorem B8682527 : Blo 2031435 8682527 := bstep (se 1 (by rfl) ⟨6511895, by rfl⟩ : syracuseStep 8682527 = 13023791) B13023791
theorem B5788351 : Blo 2031435 5788351 := bstep (se 1 (by rfl) ⟨4341263, by rfl⟩ : syracuseStep 5788351 = 8682527) B8682527
theorem B7717801 : Blo 2031435 7717801 := bstep (se 2 (by rfl) ⟨2894175, by rfl⟩ : syracuseStep 7717801 = 5788351) B5788351
theorem B10290401 : Blo 2031435 10290401 := bstep (se 2 (by rfl) ⟨3858900, by rfl⟩ : syracuseStep 10290401 = 7717801) B7717801
theorem B6860267 : Blo 2031435 6860267 := bstep (se 1 (by rfl) ⟨5145200, by rfl⟩ : syracuseStep 6860267 = 10290401) B10290401
theorem B4573511 : Blo 2031435 4573511 := bstep (se 1 (by rfl) ⟨3430133, by rfl⟩ : syracuseStep 4573511 = 6860267) B6860267
theorem B3049007 : Blo 2031435 3049007 := bstep (se 1 (by rfl) ⟨2286755, by rfl⟩ : syracuseStep 3049007 = 4573511) B4573511
theorem B2032671 : Blo 2031435 2032671 := bstep (se 1 (by rfl) ⟨1524503, by rfl⟩ : syracuseStep 2032671 = 3049007) B3049007
theorem B3049013 : Blo 2031435 3049013 := bbase (se 5 (by rfl) ⟨142922, by rfl⟩ : syracuseStep 3049013 = 285845) (by norm_num)
theorem B2032675 : Blo 2031435 2032675 := bstep (se 1 (by rfl) ⟨1524506, by rfl⟩ : syracuseStep 2032675 = 3049013) B3049013
theorem B5145221 : Blo 2031435 5145221 := bbase (se 4 (by rfl) ⟨482364, by rfl⟩ : syracuseStep 5145221 = 964729) (by norm_num)
theorem B3430147 : Blo 2031435 3430147 := bstep (se 1 (by rfl) ⟨2572610, by rfl⟩ : syracuseStep 3430147 = 5145221) B5145221
theorem B4573529 : Blo 2031435 4573529 := bstep (se 2 (by rfl) ⟨1715073, by rfl⟩ : syracuseStep 4573529 = 3430147) B3430147
theorem B3049019 : Blo 2031435 3049019 := bstep (se 1 (by rfl) ⟨2286764, by rfl⟩ : syracuseStep 3049019 = 4573529) B4573529
theorem B2032679 : Blo 2031435 2032679 := bstep (se 1 (by rfl) ⟨1524509, by rfl⟩ : syracuseStep 2032679 = 3049019) B3049019
theorem B2286769 : Blo 2031435 2286769 := bbase (se 2 (by rfl) ⟨857538, by rfl⟩ : syracuseStep 2286769 = 1715077) (by norm_num)
theorem B3049025 : Blo 2031435 3049025 := bstep (se 2 (by rfl) ⟨1143384, by rfl⟩ : syracuseStep 3049025 = 2286769) B2286769
theorem B2032683 : Blo 2031435 2032683 := bstep (se 1 (by rfl) ⟨1524512, by rfl⟩ : syracuseStep 2032683 = 3049025) B3049025
theorem B2170649 : Blo 2031435 2170649 := bbase (se 2 (by rfl) ⟨813993, by rfl⟩ : syracuseStep 2170649 = 1627987) (by norm_num)
theorem B5788397 : Blo 2031435 5788397 := bstep (se 3 (by rfl) ⟨1085324, by rfl⟩ : syracuseStep 5788397 = 2170649) B2170649
theorem B3858931 : Blo 2031435 3858931 := bstep (se 1 (by rfl) ⟨2894198, by rfl⟩ : syracuseStep 3858931 = 5788397) B5788397
theorem B5145241 : Blo 2031435 5145241 := bstep (se 2 (by rfl) ⟨1929465, by rfl⟩ : syracuseStep 5145241 = 3858931) B3858931
theorem B6860321 : Blo 2031435 6860321 := bstep (se 2 (by rfl) ⟨2572620, by rfl⟩ : syracuseStep 6860321 = 5145241) B5145241
theorem B4573547 : Blo 2031435 4573547 := bstep (se 1 (by rfl) ⟨3430160, by rfl⟩ : syracuseStep 4573547 = 6860321) B6860321
theorem B3049031 : Blo 2031435 3049031 := bstep (se 1 (by rfl) ⟨2286773, by rfl⟩ : syracuseStep 3049031 = 4573547) B4573547
theorem B2032687 : Blo 2031435 2032687 := bstep (se 1 (by rfl) ⟨1524515, by rfl⟩ : syracuseStep 2032687 = 3049031) B3049031
theorem B3049037 : Blo 2031435 3049037 := bbase (se 3 (by rfl) ⟨571694, by rfl⟩ : syracuseStep 3049037 = 1143389) (by norm_num)
theorem B2032691 : Blo 2031435 2032691 := bstep (se 1 (by rfl) ⟨1524518, by rfl⟩ : syracuseStep 2032691 = 3049037) B3049037
theorem B4573565 : Blo 2031435 4573565 := bbase (se 3 (by rfl) ⟨857543, by rfl⟩ : syracuseStep 4573565 = 1715087) (by norm_num)
theorem B3049043 : Blo 2031435 3049043 := bstep (se 1 (by rfl) ⟨2286782, by rfl⟩ : syracuseStep 3049043 = 4573565) B4573565
theorem B2032695 : Blo 2031435 2032695 := bstep (se 1 (by rfl) ⟨1524521, by rfl⟩ : syracuseStep 2032695 = 3049043) B3049043
theorem B3430181 : Blo 2031435 3430181 := bbase (se 4 (by rfl) ⟨321579, by rfl⟩ : syracuseStep 3430181 = 643159) (by norm_num)
theorem B2286787 : Blo 2031435 2286787 := bstep (se 1 (by rfl) ⟨1715090, by rfl⟩ : syracuseStep 2286787 = 3430181) B3430181
theorem B3049049 : Blo 2031435 3049049 := bstep (se 2 (by rfl) ⟨1143393, by rfl⟩ : syracuseStep 3049049 = 2286787) B2286787
theorem B2032699 : Blo 2031435 2032699 := bstep (se 1 (by rfl) ⟨1524524, by rfl⟩ : syracuseStep 2032699 = 3049049) B3049049
theorem B2894221 : Blo 2031435 2894221 := bbase (se 3 (by rfl) ⟨542666, by rfl⟩ : syracuseStep 2894221 = 1085333) (by norm_num)
theorem B15435845 : Blo 2031435 15435845 := bstep (se 4 (by rfl) ⟨1447110, by rfl⟩ : syracuseStep 15435845 = 2894221) B2894221
theorem B10290563 : Blo 2031435 10290563 := bstep (se 1 (by rfl) ⟨7717922, by rfl⟩ : syracuseStep 10290563 = 15435845) B15435845
theorem B6860375 : Blo 2031435 6860375 := bstep (se 1 (by rfl) ⟨5145281, by rfl⟩ : syracuseStep 6860375 = 10290563) B10290563
theorem B4573583 : Blo 2031435 4573583 := bstep (se 1 (by rfl) ⟨3430187, by rfl⟩ : syracuseStep 4573583 = 6860375) B6860375
theorem B3049055 : Blo 2031435 3049055 := bstep (se 1 (by rfl) ⟨2286791, by rfl⟩ : syracuseStep 3049055 = 4573583) B4573583
theorem B2032703 : Blo 2031435 2032703 := bstep (se 1 (by rfl) ⟨1524527, by rfl⟩ : syracuseStep 2032703 = 3049055) B3049055
theorem B3049061 : Blo 2031435 3049061 := bbase (se 4 (by rfl) ⟨285849, by rfl⟩ : syracuseStep 3049061 = 571699) (by norm_num)
theorem B2032707 : Blo 2031435 2032707 := bstep (se 1 (by rfl) ⟨1524530, by rfl⟩ : syracuseStep 2032707 = 3049061) B3049061
theorem B3256013 : Blo 2031435 3256013 := bbase (se 3 (by rfl) ⟨610502, by rfl⟩ : syracuseStep 3256013 = 1221005) (by norm_num)
theorem B2170675 : Blo 2031435 2170675 := bstep (se 1 (by rfl) ⟨1628006, by rfl⟩ : syracuseStep 2170675 = 3256013) B3256013
theorem B2894233 : Blo 2031435 2894233 := bstep (se 2 (by rfl) ⟨1085337, by rfl⟩ : syracuseStep 2894233 = 2170675) B2170675
theorem B3858977 : Blo 2031435 3858977 := bstep (se 2 (by rfl) ⟨1447116, by rfl⟩ : syracuseStep 3858977 = 2894233) B2894233
theorem B2572651 : Blo 2031435 2572651 := bstep (se 1 (by rfl) ⟨1929488, by rfl⟩ : syracuseStep 2572651 = 3858977) B3858977
theorem B3430201 : Blo 2031435 3430201 := bstep (se 2 (by rfl) ⟨1286325, by rfl⟩ : syracuseStep 3430201 = 2572651) B2572651
theorem B4573601 : Blo 2031435 4573601 := bstep (se 2 (by rfl) ⟨1715100, by rfl⟩ : syracuseStep 4573601 = 3430201) B3430201
theorem B3049067 : Blo 2031435 3049067 := bstep (se 1 (by rfl) ⟨2286800, by rfl⟩ : syracuseStep 3049067 = 4573601) B4573601
theorem B2032711 : Blo 2031435 2032711 := bstep (se 1 (by rfl) ⟨1524533, by rfl⟩ : syracuseStep 2032711 = 3049067) B3049067
theorem B2286805 : Blo 2031435 2286805 := bbase (se 7 (by rfl) ⟨26798, by rfl⟩ : syracuseStep 2286805 = 53597) (by norm_num)
theorem B3049073 : Blo 2031435 3049073 := bstep (se 2 (by rfl) ⟨1143402, by rfl⟩ : syracuseStep 3049073 = 2286805) B2286805
theorem B2032715 : Blo 2031435 2032715 := bstep (se 1 (by rfl) ⟨1524536, by rfl⟩ : syracuseStep 2032715 = 3049073) B3049073
theorem B2572661 : Blo 2031435 2572661 := bbase (se 5 (by rfl) ⟨120593, by rfl⟩ : syracuseStep 2572661 = 241187) (by norm_num)
theorem B6860429 : Blo 2031435 6860429 := bstep (se 3 (by rfl) ⟨1286330, by rfl⟩ : syracuseStep 6860429 = 2572661) B2572661
theorem B4573619 : Blo 2031435 4573619 := bstep (se 1 (by rfl) ⟨3430214, by rfl⟩ : syracuseStep 4573619 = 6860429) B6860429
theorem B3049079 : Blo 2031435 3049079 := bstep (se 1 (by rfl) ⟨2286809, by rfl⟩ : syracuseStep 3049079 = 4573619) B4573619
theorem B2032719 : Blo 2031435 2032719 := bstep (se 1 (by rfl) ⟨1524539, by rfl⟩ : syracuseStep 2032719 = 3049079) B3049079
theorem B3049085 : Blo 2031435 3049085 := bbase (se 3 (by rfl) ⟨571703, by rfl⟩ : syracuseStep 3049085 = 1143407) (by norm_num)
theorem B2032723 : Blo 2031435 2032723 := bstep (se 1 (by rfl) ⟨1524542, by rfl⟩ : syracuseStep 2032723 = 3049085) B3049085
theorem B4573637 : Blo 2031435 4573637 := bbase (se 4 (by rfl) ⟨428778, by rfl⟩ : syracuseStep 4573637 = 857557) (by norm_num)
theorem B3049091 : Blo 2031435 3049091 := bstep (se 1 (by rfl) ⟨2286818, by rfl⟩ : syracuseStep 3049091 = 4573637) B4573637
theorem B2032727 : Blo 2031435 2032727 := bstep (se 1 (by rfl) ⟨1524545, by rfl⟩ : syracuseStep 2032727 = 3049091) B3049091
theorem B7326101 : Blo 2031435 7326101 := bbase (se 6 (by rfl) ⟨171705, by rfl⟩ : syracuseStep 7326101 = 343411) (by norm_num)
theorem B4884067 : Blo 2031435 4884067 := bstep (se 1 (by rfl) ⟨3663050, by rfl⟩ : syracuseStep 4884067 = 7326101) B7326101
theorem B6512089 : Blo 2031435 6512089 := bstep (se 2 (by rfl) ⟨2442033, by rfl⟩ : syracuseStep 6512089 = 4884067) B4884067
theorem B8682785 : Blo 2031435 8682785 := bstep (se 2 (by rfl) ⟨3256044, by rfl⟩ : syracuseStep 8682785 = 6512089) B6512089
theorem B5788523 : Blo 2031435 5788523 := bstep (se 1 (by rfl) ⟨4341392, by rfl⟩ : syracuseStep 5788523 = 8682785) B8682785
theorem B3859015 : Blo 2031435 3859015 := bstep (se 1 (by rfl) ⟨2894261, by rfl⟩ : syracuseStep 3859015 = 5788523) B5788523
theorem B5145353 : Blo 2031435 5145353 := bstep (se 2 (by rfl) ⟨1929507, by rfl⟩ : syracuseStep 5145353 = 3859015) B3859015
theorem B3430235 : Blo 2031435 3430235 := bstep (se 1 (by rfl) ⟨2572676, by rfl⟩ : syracuseStep 3430235 = 5145353) B5145353
theorem B2286823 : Blo 2031435 2286823 := bstep (se 1 (by rfl) ⟨1715117, by rfl⟩ : syracuseStep 2286823 = 3430235) B3430235
theorem B3049097 : Blo 2031435 3049097 := bstep (se 2 (by rfl) ⟨1143411, by rfl⟩ : syracuseStep 3049097 = 2286823) B2286823
theorem B2032731 : Blo 2031435 2032731 := bstep (se 1 (by rfl) ⟨1524548, by rfl⟩ : syracuseStep 2032731 = 3049097) B3049097
theorem B10290725 : Blo 2031435 10290725 := bbase (se 4 (by rfl) ⟨964755, by rfl⟩ : syracuseStep 10290725 = 1929511) (by norm_num)
theorem B6860483 : Blo 2031435 6860483 := bstep (se 1 (by rfl) ⟨5145362, by rfl⟩ : syracuseStep 6860483 = 10290725) B10290725
theorem B4573655 : Blo 2031435 4573655 := bstep (se 1 (by rfl) ⟨3430241, by rfl⟩ : syracuseStep 4573655 = 6860483) B6860483
theorem B3049103 : Blo 2031435 3049103 := bstep (se 1 (by rfl) ⟨2286827, by rfl⟩ : syracuseStep 3049103 = 4573655) B4573655
theorem B2032735 : Blo 2031435 2032735 := bstep (se 1 (by rfl) ⟨1524551, by rfl⟩ : syracuseStep 2032735 = 3049103) B3049103
theorem B3049109 : Blo 2031435 3049109 := bbase (se 6 (by rfl) ⟨71463, by rfl⟩ : syracuseStep 3049109 = 142927) (by norm_num)
theorem B2032739 : Blo 2031435 2032739 := bstep (se 1 (by rfl) ⟨1524554, by rfl⟩ : syracuseStep 2032739 = 3049109) B3049109
theorem B2679437 : Blo 2031435 2679437 := bbase (se 3 (by rfl) ⟨502394, by rfl⟩ : syracuseStep 2679437 = 1004789) (by norm_num)
theorem B7145165 : Blo 2031435 7145165 := bstep (se 3 (by rfl) ⟨1339718, by rfl⟩ : syracuseStep 7145165 = 2679437) B2679437
theorem B4763443 : Blo 2031435 4763443 := bstep (se 1 (by rfl) ⟨3572582, by rfl⟩ : syracuseStep 4763443 = 7145165) B7145165
theorem B6351257 : Blo 2031435 6351257 := bstep (se 2 (by rfl) ⟨2381721, by rfl⟩ : syracuseStep 6351257 = 4763443) B4763443
theorem B16936685 : Blo 2031435 16936685 := bstep (se 3 (by rfl) ⟨3175628, by rfl⟩ : syracuseStep 16936685 = 6351257) B6351257
theorem B11291123 : Blo 2031435 11291123 := bstep (se 1 (by rfl) ⟨8468342, by rfl⟩ : syracuseStep 11291123 = 16936685) B16936685
theorem B7527415 : Blo 2031435 7527415 := bstep (se 1 (by rfl) ⟨5645561, by rfl⟩ : syracuseStep 7527415 = 11291123) B11291123
theorem B10036553 : Blo 2031435 10036553 := bstep (se 2 (by rfl) ⟨3763707, by rfl⟩ : syracuseStep 10036553 = 7527415) B7527415
theorem B26764141 : Blo 2031435 26764141 := bstep (se 3 (by rfl) ⟨5018276, by rfl⟩ : syracuseStep 26764141 = 10036553) B10036553
theorem B35685521 : Blo 2031435 35685521 := bstep (se 2 (by rfl) ⟨13382070, by rfl⟩ : syracuseStep 35685521 = 26764141) B26764141
theorem B23790347 : Blo 2031435 23790347 := bstep (se 1 (by rfl) ⟨17842760, by rfl⟩ : syracuseStep 23790347 = 35685521) B35685521
theorem B15860231 : Blo 2031435 15860231 := bstep (se 1 (by rfl) ⟨11895173, by rfl⟩ : syracuseStep 15860231 = 23790347) B23790347
theorem B10573487 : Blo 2031435 10573487 := bstep (se 1 (by rfl) ⟨7930115, by rfl⟩ : syracuseStep 10573487 = 15860231) B15860231
theorem B7048991 : Blo 2031435 7048991 := bstep (se 1 (by rfl) ⟨5286743, by rfl⟩ : syracuseStep 7048991 = 10573487) B10573487
theorem B18797309 : Blo 2031435 18797309 := bstep (se 3 (by rfl) ⟨3524495, by rfl⟩ : syracuseStep 18797309 = 7048991) B7048991
theorem B12531539 : Blo 2031435 12531539 := bstep (se 1 (by rfl) ⟨9398654, by rfl⟩ : syracuseStep 12531539 = 18797309) B18797309
theorem B8354359 : Blo 2031435 8354359 := bstep (se 1 (by rfl) ⟨6265769, by rfl⟩ : syracuseStep 8354359 = 12531539) B12531539
theorem B44556581 : Blo 2031435 44556581 := bstep (se 4 (by rfl) ⟨4177179, by rfl⟩ : syracuseStep 44556581 = 8354359) B8354359
theorem B29704387 : Blo 2031435 29704387 := bstep (se 1 (by rfl) ⟨22278290, by rfl⟩ : syracuseStep 29704387 = 44556581) B44556581
theorem B39605849 : Blo 2031435 39605849 := bstep (se 2 (by rfl) ⟨14852193, by rfl⟩ : syracuseStep 39605849 = 29704387) B29704387
theorem B26403899 : Blo 2031435 26403899 := bstep (se 1 (by rfl) ⟨19802924, by rfl⟩ : syracuseStep 26403899 = 39605849) B39605849
theorem B70410397 : Blo 2031435 70410397 := bstep (se 3 (by rfl) ⟨13201949, by rfl⟩ : syracuseStep 70410397 = 26403899) B26403899
theorem B93880529 : Blo 2031435 93880529 := bstep (se 2 (by rfl) ⟨35205198, by rfl⟩ : syracuseStep 93880529 = 70410397) B70410397
theorem B62587019 : Blo 2031435 62587019 := bstep (se 1 (by rfl) ⟨46940264, by rfl⟩ : syracuseStep 62587019 = 93880529) B93880529
theorem B41724679 : Blo 2031435 41724679 := bstep (se 1 (by rfl) ⟨31293509, by rfl⟩ : syracuseStep 41724679 = 62587019) B62587019
theorem B55632905 : Blo 2031435 55632905 := bstep (se 2 (by rfl) ⟨20862339, by rfl⟩ : syracuseStep 55632905 = 41724679) B41724679
theorem B37088603 : Blo 2031435 37088603 := bstep (se 1 (by rfl) ⟨27816452, by rfl⟩ : syracuseStep 37088603 = 55632905) B55632905
theorem B24725735 : Blo 2031435 24725735 := bstep (se 1 (by rfl) ⟨18544301, by rfl⟩ : syracuseStep 24725735 = 37088603) B37088603
theorem B16483823 : Blo 2031435 16483823 := bstep (se 1 (by rfl) ⟨12362867, by rfl⟩ : syracuseStep 16483823 = 24725735) B24725735
theorem B10989215 : Blo 2031435 10989215 := bstep (se 1 (by rfl) ⟨8241911, by rfl⟩ : syracuseStep 10989215 = 16483823) B16483823
theorem B7326143 : Blo 2031435 7326143 := bstep (se 1 (by rfl) ⟨5494607, by rfl⟩ : syracuseStep 7326143 = 10989215) B10989215
theorem B4884095 : Blo 2031435 4884095 := bstep (se 1 (by rfl) ⟨3663071, by rfl⟩ : syracuseStep 4884095 = 7326143) B7326143
theorem B13024253 : Blo 2031435 13024253 := bstep (se 3 (by rfl) ⟨2442047, by rfl⟩ : syracuseStep 13024253 = 4884095) B4884095
theorem B8682835 : Blo 2031435 8682835 := bstep (se 1 (by rfl) ⟨6512126, by rfl⟩ : syracuseStep 8682835 = 13024253) B13024253
theorem B11577113 : Blo 2031435 11577113 := bstep (se 2 (by rfl) ⟨4341417, by rfl⟩ : syracuseStep 11577113 = 8682835) B8682835
theorem B7718075 : Blo 2031435 7718075 := bstep (se 1 (by rfl) ⟨5788556, by rfl⟩ : syracuseStep 7718075 = 11577113) B11577113
theorem B5145383 : Blo 2031435 5145383 := bstep (se 1 (by rfl) ⟨3859037, by rfl⟩ : syracuseStep 5145383 = 7718075) B7718075
theorem B3430255 : Blo 2031435 3430255 := bstep (se 1 (by rfl) ⟨2572691, by rfl⟩ : syracuseStep 3430255 = 5145383) B5145383
theorem B4573673 : Blo 2031435 4573673 := bstep (se 2 (by rfl) ⟨1715127, by rfl⟩ : syracuseStep 4573673 = 3430255) B3430255
theorem B3049115 : Blo 2031435 3049115 := bstep (se 1 (by rfl) ⟨2286836, by rfl⟩ : syracuseStep 3049115 = 4573673) B4573673
theorem B2032743 : Blo 2031435 2032743 := bstep (se 1 (by rfl) ⟨1524557, by rfl⟩ : syracuseStep 2032743 = 3049115) B3049115
theorem B2286841 : Blo 2031435 2286841 := bbase (se 2 (by rfl) ⟨857565, by rfl⟩ : syracuseStep 2286841 = 1715131) (by norm_num)
theorem B3049121 : Blo 2031435 3049121 := bstep (se 2 (by rfl) ⟨1143420, by rfl⟩ : syracuseStep 3049121 = 2286841) B2286841
theorem B2032747 : Blo 2031435 2032747 := bstep (se 1 (by rfl) ⟨1524560, by rfl⟩ : syracuseStep 2032747 = 3049121) B3049121
theorem B8682869 : Blo 2031435 8682869 := bbase (se 5 (by rfl) ⟨407009, by rfl⟩ : syracuseStep 8682869 = 814019) (by norm_num)
theorem B5788579 : Blo 2031435 5788579 := bstep (se 1 (by rfl) ⟨4341434, by rfl⟩ : syracuseStep 5788579 = 8682869) B8682869
theorem B7718105 : Blo 2031435 7718105 := bstep (se 2 (by rfl) ⟨2894289, by rfl⟩ : syracuseStep 7718105 = 5788579) B5788579
theorem B5145403 : Blo 2031435 5145403 := bstep (se 1 (by rfl) ⟨3859052, by rfl⟩ : syracuseStep 5145403 = 7718105) B7718105
theorem B6860537 : Blo 2031435 6860537 := bstep (se 2 (by rfl) ⟨2572701, by rfl⟩ : syracuseStep 6860537 = 5145403) B5145403
theorem B4573691 : Blo 2031435 4573691 := bstep (se 1 (by rfl) ⟨3430268, by rfl⟩ : syracuseStep 4573691 = 6860537) B6860537
theorem B3049127 : Blo 2031435 3049127 := bstep (se 1 (by rfl) ⟨2286845, by rfl⟩ : syracuseStep 3049127 = 4573691) B4573691
theorem B2032751 : Blo 2031435 2032751 := bstep (se 1 (by rfl) ⟨1524563, by rfl⟩ : syracuseStep 2032751 = 3049127) B3049127
theorem B3049133 : Blo 2031435 3049133 := bbase (se 3 (by rfl) ⟨571712, by rfl⟩ : syracuseStep 3049133 = 1143425) (by norm_num)
theorem B2032755 : Blo 2031435 2032755 := bstep (se 1 (by rfl) ⟨1524566, by rfl⟩ : syracuseStep 2032755 = 3049133) B3049133
theorem B4573709 : Blo 2031435 4573709 := bbase (se 3 (by rfl) ⟨857570, by rfl⟩ : syracuseStep 4573709 = 1715141) (by norm_num)
theorem B3049139 : Blo 2031435 3049139 := bstep (se 1 (by rfl) ⟨2286854, by rfl⟩ : syracuseStep 3049139 = 4573709) B4573709
theorem B2032759 : Blo 2031435 2032759 := bstep (se 1 (by rfl) ⟨1524569, by rfl⟩ : syracuseStep 2032759 = 3049139) B3049139
theorem B2572717 : Blo 2031435 2572717 := bbase (se 3 (by rfl) ⟨482384, by rfl⟩ : syracuseStep 2572717 = 964769) (by norm_num)
theorem B3430289 : Blo 2031435 3430289 := bstep (se 2 (by rfl) ⟨1286358, by rfl⟩ : syracuseStep 3430289 = 2572717) B2572717
theorem B2286859 : Blo 2031435 2286859 := bstep (se 1 (by rfl) ⟨1715144, by rfl⟩ : syracuseStep 2286859 = 3430289) B3430289
theorem B3049145 : Blo 2031435 3049145 := bstep (se 2 (by rfl) ⟨1143429, by rfl⟩ : syracuseStep 3049145 = 2286859) B2286859
theorem B2032763 : Blo 2031435 2032763 := bstep (se 1 (by rfl) ⟨1524572, by rfl⟩ : syracuseStep 2032763 = 3049145) B3049145
theorem B13024405 : Blo 2031435 13024405 := bbase (se 6 (by rfl) ⟨305259, by rfl⟩ : syracuseStep 13024405 = 610519) (by norm_num)
theorem B17365873 : Blo 2031435 17365873 := bstep (se 2 (by rfl) ⟨6512202, by rfl⟩ : syracuseStep 17365873 = 13024405) B13024405
theorem B23154497 : Blo 2031435 23154497 := bstep (se 2 (by rfl) ⟨8682936, by rfl⟩ : syracuseStep 23154497 = 17365873) B17365873
theorem B15436331 : Blo 2031435 15436331 := bstep (se 1 (by rfl) ⟨11577248, by rfl⟩ : syracuseStep 15436331 = 23154497) B23154497
theorem B10290887 : Blo 2031435 10290887 := bstep (se 1 (by rfl) ⟨7718165, by rfl⟩ : syracuseStep 10290887 = 15436331) B15436331
theorem B6860591 : Blo 2031435 6860591 := bstep (se 1 (by rfl) ⟨5145443, by rfl⟩ : syracuseStep 6860591 = 10290887) B10290887
theorem B4573727 : Blo 2031435 4573727 := bstep (se 1 (by rfl) ⟨3430295, by rfl⟩ : syracuseStep 4573727 = 6860591) B6860591
theorem B3049151 : Blo 2031435 3049151 := bstep (se 1 (by rfl) ⟨2286863, by rfl⟩ : syracuseStep 3049151 = 4573727) B4573727
theorem B2032767 : Blo 2031435 2032767 := bstep (se 1 (by rfl) ⟨1524575, by rfl⟩ : syracuseStep 2032767 = 3049151) B3049151
theorem B3049157 : Blo 2031435 3049157 := bbase (se 4 (by rfl) ⟨285858, by rfl⟩ : syracuseStep 3049157 = 571717) (by norm_num)
theorem B2032771 : Blo 2031435 2032771 := bstep (se 1 (by rfl) ⟨1524578, by rfl⟩ : syracuseStep 2032771 = 3049157) B3049157
theorem B3430309 : Blo 2031435 3430309 := bbase (se 4 (by rfl) ⟨321591, by rfl⟩ : syracuseStep 3430309 = 643183) (by norm_num)
theorem B4573745 : Blo 2031435 4573745 := bstep (se 2 (by rfl) ⟨1715154, by rfl⟩ : syracuseStep 4573745 = 3430309) B3430309
theorem B3049163 : Blo 2031435 3049163 := bstep (se 1 (by rfl) ⟨2286872, by rfl⟩ : syracuseStep 3049163 = 4573745) B4573745
theorem B2032775 : Blo 2031435 2032775 := bstep (se 1 (by rfl) ⟨1524581, by rfl⟩ : syracuseStep 2032775 = 3049163) B3049163
theorem B2286877 : Blo 2031435 2286877 := bbase (se 3 (by rfl) ⟨428789, by rfl⟩ : syracuseStep 2286877 = 857579) (by norm_num)
theorem B3049169 : Blo 2031435 3049169 := bstep (se 2 (by rfl) ⟨1143438, by rfl⟩ : syracuseStep 3049169 = 2286877) B2286877
theorem B2032779 : Blo 2031435 2032779 := bstep (se 1 (by rfl) ⟨1524584, by rfl⟩ : syracuseStep 2032779 = 3049169) B3049169
theorem B6860645 : Blo 2031435 6860645 := bbase (se 4 (by rfl) ⟨643185, by rfl⟩ : syracuseStep 6860645 = 1286371) (by norm_num)
theorem B4573763 : Blo 2031435 4573763 := bstep (se 1 (by rfl) ⟨3430322, by rfl⟩ : syracuseStep 4573763 = 6860645) B6860645
theorem B3049175 : Blo 2031435 3049175 := bstep (se 1 (by rfl) ⟨2286881, by rfl⟩ : syracuseStep 3049175 = 4573763) B4573763
theorem B2032783 : Blo 2031435 2032783 := bstep (se 1 (by rfl) ⟨1524587, by rfl⟩ : syracuseStep 2032783 = 3049175) B3049175
theorem B3049181 : Blo 2031435 3049181 := bbase (se 3 (by rfl) ⟨571721, by rfl⟩ : syracuseStep 3049181 = 1143443) (by norm_num)
theorem B2032787 : Blo 2031435 2032787 := bstep (se 1 (by rfl) ⟨1524590, by rfl⟩ : syracuseStep 2032787 = 3049181) B3049181
theorem B4573781 : Blo 2031435 4573781 := bbase (se 8 (by rfl) ⟨26799, by rfl⟩ : syracuseStep 4573781 = 53599) (by norm_num)
theorem B3049187 : Blo 2031435 3049187 := bstep (se 1 (by rfl) ⟨2286890, by rfl⟩ : syracuseStep 3049187 = 4573781) B4573781
theorem B2032791 : Blo 2031435 2032791 := bstep (se 1 (by rfl) ⟨1524593, by rfl⟩ : syracuseStep 2032791 = 3049187) B3049187
theorem B4884221 : Blo 2031435 4884221 := bbase (se 3 (by rfl) ⟨915791, by rfl⟩ : syracuseStep 4884221 = 1831583) (by norm_num)
theorem B3256147 : Blo 2031435 3256147 := bstep (se 1 (by rfl) ⟨2442110, by rfl⟩ : syracuseStep 3256147 = 4884221) B4884221
theorem B4341529 : Blo 2031435 4341529 := bstep (se 2 (by rfl) ⟨1628073, by rfl⟩ : syracuseStep 4341529 = 3256147) B3256147
theorem B5788705 : Blo 2031435 5788705 := bstep (se 2 (by rfl) ⟨2170764, by rfl⟩ : syracuseStep 5788705 = 4341529) B4341529
theorem B7718273 : Blo 2031435 7718273 := bstep (se 2 (by rfl) ⟨2894352, by rfl⟩ : syracuseStep 7718273 = 5788705) B5788705
theorem B5145515 : Blo 2031435 5145515 := bstep (se 1 (by rfl) ⟨3859136, by rfl⟩ : syracuseStep 5145515 = 7718273) B7718273
theorem B3430343 : Blo 2031435 3430343 := bstep (se 1 (by rfl) ⟨2572757, by rfl⟩ : syracuseStep 3430343 = 5145515) B5145515
theorem B2286895 : Blo 2031435 2286895 := bstep (se 1 (by rfl) ⟨1715171, by rfl⟩ : syracuseStep 2286895 = 3430343) B3430343
theorem B3049193 : Blo 2031435 3049193 := bstep (se 2 (by rfl) ⟨1143447, by rfl⟩ : syracuseStep 3049193 = 2286895) B2286895
theorem B2032795 : Blo 2031435 2032795 := bstep (se 1 (by rfl) ⟨1524596, by rfl⟩ : syracuseStep 2032795 = 3049193) B3049193
theorem B4884229 : Blo 2031435 4884229 := bbase (se 4 (by rfl) ⟨457896, by rfl⟩ : syracuseStep 4884229 = 915793) (by norm_num)
theorem B26049221 : Blo 2031435 26049221 := bstep (se 4 (by rfl) ⟨2442114, by rfl⟩ : syracuseStep 26049221 = 4884229) B4884229
theorem B17366147 : Blo 2031435 17366147 := bstep (se 1 (by rfl) ⟨13024610, by rfl⟩ : syracuseStep 17366147 = 26049221) B26049221
theorem B11577431 : Blo 2031435 11577431 := bstep (se 1 (by rfl) ⟨8683073, by rfl⟩ : syracuseStep 11577431 = 17366147) B17366147
theorem B7718287 : Blo 2031435 7718287 := bstep (se 1 (by rfl) ⟨5788715, by rfl⟩ : syracuseStep 7718287 = 11577431) B11577431
theorem B10291049 : Blo 2031435 10291049 := bstep (se 2 (by rfl) ⟨3859143, by rfl⟩ : syracuseStep 10291049 = 7718287) B7718287
theorem B6860699 : Blo 2031435 6860699 := bstep (se 1 (by rfl) ⟨5145524, by rfl⟩ : syracuseStep 6860699 = 10291049) B10291049
theorem B4573799 : Blo 2031435 4573799 := bstep (se 1 (by rfl) ⟨3430349, by rfl⟩ : syracuseStep 4573799 = 6860699) B6860699
theorem B3049199 : Blo 2031435 3049199 := bstep (se 1 (by rfl) ⟨2286899, by rfl⟩ : syracuseStep 3049199 = 4573799) B4573799
theorem B2032799 : Blo 2031435 2032799 := bstep (se 1 (by rfl) ⟨1524599, by rfl⟩ : syracuseStep 2032799 = 3049199) B3049199
theorem B3049205 : Blo 2031435 3049205 := bbase (se 5 (by rfl) ⟨142931, by rfl⟩ : syracuseStep 3049205 = 285863) (by norm_num)
theorem B2032803 : Blo 2031435 2032803 := bstep (se 1 (by rfl) ⟨1524602, by rfl⟩ : syracuseStep 2032803 = 3049205) B3049205
theorem B8683109 : Blo 2031435 8683109 := bbase (se 4 (by rfl) ⟨814041, by rfl⟩ : syracuseStep 8683109 = 1628083) (by norm_num)
theorem B5788739 : Blo 2031435 5788739 := bstep (se 1 (by rfl) ⟨4341554, by rfl⟩ : syracuseStep 5788739 = 8683109) B8683109
theorem B3859159 : Blo 2031435 3859159 := bstep (se 1 (by rfl) ⟨2894369, by rfl⟩ : syracuseStep 3859159 = 5788739) B5788739
theorem B5145545 : Blo 2031435 5145545 := bstep (se 2 (by rfl) ⟨1929579, by rfl⟩ : syracuseStep 5145545 = 3859159) B3859159
theorem B3430363 : Blo 2031435 3430363 := bstep (se 1 (by rfl) ⟨2572772, by rfl⟩ : syracuseStep 3430363 = 5145545) B5145545
theorem B4573817 : Blo 2031435 4573817 := bstep (se 2 (by rfl) ⟨1715181, by rfl⟩ : syracuseStep 4573817 = 3430363) B3430363
theorem B3049211 : Blo 2031435 3049211 := bstep (se 1 (by rfl) ⟨2286908, by rfl⟩ : syracuseStep 3049211 = 4573817) B4573817
theorem B2032807 : Blo 2031435 2032807 := bstep (se 1 (by rfl) ⟨1524605, by rfl⟩ : syracuseStep 2032807 = 3049211) B3049211
theorem B2286913 : Blo 2031435 2286913 := bbase (se 2 (by rfl) ⟨857592, by rfl⟩ : syracuseStep 2286913 = 1715185) (by norm_num)
theorem B3049217 : Blo 2031435 3049217 := bstep (se 2 (by rfl) ⟨1143456, by rfl⟩ : syracuseStep 3049217 = 2286913) B2286913
theorem B2032811 : Blo 2031435 2032811 := bstep (se 1 (by rfl) ⟨1524608, by rfl⟩ : syracuseStep 2032811 = 3049217) B3049217
theorem B5145565 : Blo 2031435 5145565 := bbase (se 3 (by rfl) ⟨964793, by rfl⟩ : syracuseStep 5145565 = 1929587) (by norm_num)
theorem B6860753 : Blo 2031435 6860753 := bstep (se 2 (by rfl) ⟨2572782, by rfl⟩ : syracuseStep 6860753 = 5145565) B5145565
theorem B4573835 : Blo 2031435 4573835 := bstep (se 1 (by rfl) ⟨3430376, by rfl⟩ : syracuseStep 4573835 = 6860753) B6860753
theorem B3049223 : Blo 2031435 3049223 := bstep (se 1 (by rfl) ⟨2286917, by rfl⟩ : syracuseStep 3049223 = 4573835) B4573835
theorem B2032815 : Blo 2031435 2032815 := bstep (se 1 (by rfl) ⟨1524611, by rfl⟩ : syracuseStep 2032815 = 3049223) B3049223
theorem B3049229 : Blo 2031435 3049229 := bbase (se 3 (by rfl) ⟨571730, by rfl⟩ : syracuseStep 3049229 = 1143461) (by norm_num)
theorem B2032819 : Blo 2031435 2032819 := bstep (se 1 (by rfl) ⟨1524614, by rfl⟩ : syracuseStep 2032819 = 3049229) B3049229
theorem B4573853 : Blo 2031435 4573853 := bbase (se 3 (by rfl) ⟨857597, by rfl⟩ : syracuseStep 4573853 = 1715195) (by norm_num)
theorem B3049235 : Blo 2031435 3049235 := bstep (se 1 (by rfl) ⟨2286926, by rfl⟩ : syracuseStep 3049235 = 4573853) B4573853
theorem B2032823 : Blo 2031435 2032823 := bstep (se 1 (by rfl) ⟨1524617, by rfl⟩ : syracuseStep 2032823 = 3049235) B3049235
theorem B3430397 : Blo 2031435 3430397 := bbase (se 3 (by rfl) ⟨643199, by rfl⟩ : syracuseStep 3430397 = 1286399) (by norm_num)
theorem B2286931 : Blo 2031435 2286931 := bstep (se 1 (by rfl) ⟨1715198, by rfl⟩ : syracuseStep 2286931 = 3430397) B3430397
theorem B3049241 : Blo 2031435 3049241 := bstep (se 2 (by rfl) ⟨1143465, by rfl⟩ : syracuseStep 3049241 = 2286931) B2286931
theorem B2032827 : Blo 2031435 2032827 := bstep (se 1 (by rfl) ⟨1524620, by rfl⟩ : syracuseStep 2032827 = 3049241) B3049241
theorem B4341605 : Blo 2031435 4341605 := bbase (se 4 (by rfl) ⟨407025, by rfl⟩ : syracuseStep 4341605 = 814051) (by norm_num)
theorem B11577613 : Blo 2031435 11577613 := bstep (se 3 (by rfl) ⟨2170802, by rfl⟩ : syracuseStep 11577613 = 4341605) B4341605
theorem B15436817 : Blo 2031435 15436817 := bstep (se 2 (by rfl) ⟨5788806, by rfl⟩ : syracuseStep 15436817 = 11577613) B11577613
theorem B10291211 : Blo 2031435 10291211 := bstep (se 1 (by rfl) ⟨7718408, by rfl⟩ : syracuseStep 10291211 = 15436817) B15436817
theorem B6860807 : Blo 2031435 6860807 := bstep (se 1 (by rfl) ⟨5145605, by rfl⟩ : syracuseStep 6860807 = 10291211) B10291211
theorem B4573871 : Blo 2031435 4573871 := bstep (se 1 (by rfl) ⟨3430403, by rfl⟩ : syracuseStep 4573871 = 6860807) B6860807
theorem B3049247 : Blo 2031435 3049247 := bstep (se 1 (by rfl) ⟨2286935, by rfl⟩ : syracuseStep 3049247 = 4573871) B4573871
theorem B2032831 : Blo 2031435 2032831 := bstep (se 1 (by rfl) ⟨1524623, by rfl⟩ : syracuseStep 2032831 = 3049247) B3049247
theorem B3049253 : Blo 2031435 3049253 := bbase (se 4 (by rfl) ⟨285867, by rfl⟩ : syracuseStep 3049253 = 571735) (by norm_num)
theorem B2032835 : Blo 2031435 2032835 := bstep (se 1 (by rfl) ⟨1524626, by rfl⟩ : syracuseStep 2032835 = 3049253) B3049253
theorem B2572813 : Blo 2031435 2572813 := bbase (se 3 (by rfl) ⟨482402, by rfl⟩ : syracuseStep 2572813 = 964805) (by norm_num)
theorem B3430417 : Blo 2031435 3430417 := bstep (se 2 (by rfl) ⟨1286406, by rfl⟩ : syracuseStep 3430417 = 2572813) B2572813
theorem B4573889 : Blo 2031435 4573889 := bstep (se 2 (by rfl) ⟨1715208, by rfl⟩ : syracuseStep 4573889 = 3430417) B3430417
theorem B3049259 : Blo 2031435 3049259 := bstep (se 1 (by rfl) ⟨2286944, by rfl⟩ : syracuseStep 3049259 = 4573889) B4573889
theorem B2032839 : Blo 2031435 2032839 := bstep (se 1 (by rfl) ⟨1524629, by rfl⟩ : syracuseStep 2032839 = 3049259) B3049259
theorem B2286949 : Blo 2031435 2286949 := bbase (se 4 (by rfl) ⟨214401, by rfl⟩ : syracuseStep 2286949 = 428803) (by norm_num)
theorem B3049265 : Blo 2031435 3049265 := bstep (se 2 (by rfl) ⟨1143474, by rfl⟩ : syracuseStep 3049265 = 2286949) B2286949
theorem B2032843 : Blo 2031435 2032843 := bstep (se 1 (by rfl) ⟨1524632, by rfl⟩ : syracuseStep 2032843 = 3049265) B3049265
theorem B5788853 : Blo 2031435 5788853 := bbase (se 5 (by rfl) ⟨271352, by rfl⟩ : syracuseStep 5788853 = 542705) (by norm_num)
theorem B3859235 : Blo 2031435 3859235 := bstep (se 1 (by rfl) ⟨2894426, by rfl⟩ : syracuseStep 3859235 = 5788853) B5788853
theorem B2572823 : Blo 2031435 2572823 := bstep (se 1 (by rfl) ⟨1929617, by rfl⟩ : syracuseStep 2572823 = 3859235) B3859235
theorem B6860861 : Blo 2031435 6860861 := bstep (se 3 (by rfl) ⟨1286411, by rfl⟩ : syracuseStep 6860861 = 2572823) B2572823
theorem B4573907 : Blo 2031435 4573907 := bstep (se 1 (by rfl) ⟨3430430, by rfl⟩ : syracuseStep 4573907 = 6860861) B6860861
theorem B3049271 : Blo 2031435 3049271 := bstep (se 1 (by rfl) ⟨2286953, by rfl⟩ : syracuseStep 3049271 = 4573907) B4573907
theorem B2032847 : Blo 2031435 2032847 := bstep (se 1 (by rfl) ⟨1524635, by rfl⟩ : syracuseStep 2032847 = 3049271) B3049271
theorem B3049277 : Blo 2031435 3049277 := bbase (se 3 (by rfl) ⟨571739, by rfl⟩ : syracuseStep 3049277 = 1143479) (by norm_num)
theorem B2032851 : Blo 2031435 2032851 := bstep (se 1 (by rfl) ⟨1524638, by rfl⟩ : syracuseStep 2032851 = 3049277) B3049277
theorem B4573925 : Blo 2031435 4573925 := bbase (se 4 (by rfl) ⟨428805, by rfl⟩ : syracuseStep 4573925 = 857611) (by norm_num)
theorem B3049283 : Blo 2031435 3049283 := bstep (se 1 (by rfl) ⟨2286962, by rfl⟩ : syracuseStep 3049283 = 4573925) B4573925
theorem B2032855 : Blo 2031435 2032855 := bstep (se 1 (by rfl) ⟨1524641, by rfl⟩ : syracuseStep 2032855 = 3049283) B3049283
theorem B5145677 : Blo 2031435 5145677 := bbase (se 3 (by rfl) ⟨964814, by rfl⟩ : syracuseStep 5145677 = 1929629) (by norm_num)
theorem B3430451 : Blo 2031435 3430451 := bstep (se 1 (by rfl) ⟨2572838, by rfl⟩ : syracuseStep 3430451 = 5145677) B5145677
theorem B2286967 : Blo 2031435 2286967 := bstep (se 1 (by rfl) ⟨1715225, by rfl⟩ : syracuseStep 2286967 = 3430451) B3430451
theorem B3049289 : Blo 2031435 3049289 := bstep (se 2 (by rfl) ⟨1143483, by rfl⟩ : syracuseStep 3049289 = 2286967) B2286967
theorem B2032859 : Blo 2031435 2032859 := bstep (se 1 (by rfl) ⟨1524644, by rfl⟩ : syracuseStep 2032859 = 3049289) B3049289
theorem B2170837 : Blo 2031435 2170837 := bbase (se 7 (by rfl) ⟨25439, by rfl⟩ : syracuseStep 2170837 = 50879) (by norm_num)
theorem B2894449 : Blo 2031435 2894449 := bstep (se 2 (by rfl) ⟨1085418, by rfl⟩ : syracuseStep 2894449 = 2170837) B2170837
theorem B3859265 : Blo 2031435 3859265 := bstep (se 2 (by rfl) ⟨1447224, by rfl⟩ : syracuseStep 3859265 = 2894449) B2894449
theorem B10291373 : Blo 2031435 10291373 := bstep (se 3 (by rfl) ⟨1929632, by rfl⟩ : syracuseStep 10291373 = 3859265) B3859265
theorem B6860915 : Blo 2031435 6860915 := bstep (se 1 (by rfl) ⟨5145686, by rfl⟩ : syracuseStep 6860915 = 10291373) B10291373
theorem B4573943 : Blo 2031435 4573943 := bstep (se 1 (by rfl) ⟨3430457, by rfl⟩ : syracuseStep 4573943 = 6860915) B6860915
theorem B3049295 : Blo 2031435 3049295 := bstep (se 1 (by rfl) ⟨2286971, by rfl⟩ : syracuseStep 3049295 = 4573943) B4573943
theorem B2032863 : Blo 2031435 2032863 := bstep (se 1 (by rfl) ⟨1524647, by rfl⟩ : syracuseStep 2032863 = 3049295) B3049295
theorem B3049301 : Blo 2031435 3049301 := bbase (se 9 (by rfl) ⟨8933, by rfl⟩ : syracuseStep 3049301 = 17867) (by norm_num)
theorem B2032867 : Blo 2031435 2032867 := bstep (se 1 (by rfl) ⟨1524650, by rfl⟩ : syracuseStep 2032867 = 3049301) B3049301
theorem B2747477 : Blo 2031435 2747477 := bbase (se 8 (by rfl) ⟨16098, by rfl⟩ : syracuseStep 2747477 = 32197) (by norm_num)
theorem B7326605 : Blo 2031435 7326605 := bstep (se 3 (by rfl) ⟨1373738, by rfl⟩ : syracuseStep 7326605 = 2747477) B2747477
theorem B4884403 : Blo 2031435 4884403 := bstep (se 1 (by rfl) ⟨3663302, by rfl⟩ : syracuseStep 4884403 = 7326605) B7326605
theorem B6512537 : Blo 2031435 6512537 := bstep (se 2 (by rfl) ⟨2442201, by rfl⟩ : syracuseStep 6512537 = 4884403) B4884403
theorem B4341691 : Blo 2031435 4341691 := bstep (se 1 (by rfl) ⟨3256268, by rfl⟩ : syracuseStep 4341691 = 6512537) B6512537
theorem B5788921 : Blo 2031435 5788921 := bstep (se 2 (by rfl) ⟨2170845, by rfl⟩ : syracuseStep 5788921 = 4341691) B4341691
theorem B7718561 : Blo 2031435 7718561 := bstep (se 2 (by rfl) ⟨2894460, by rfl⟩ : syracuseStep 7718561 = 5788921) B5788921
theorem B5145707 : Blo 2031435 5145707 := bstep (se 1 (by rfl) ⟨3859280, by rfl⟩ : syracuseStep 5145707 = 7718561) B7718561
theorem B3430471 : Blo 2031435 3430471 := bstep (se 1 (by rfl) ⟨2572853, by rfl⟩ : syracuseStep 3430471 = 5145707) B5145707
theorem B4573961 : Blo 2031435 4573961 := bstep (se 2 (by rfl) ⟨1715235, by rfl⟩ : syracuseStep 4573961 = 3430471) B3430471
theorem B3049307 : Blo 2031435 3049307 := bstep (se 1 (by rfl) ⟨2286980, by rfl⟩ : syracuseStep 3049307 = 4573961) B4573961
theorem B2032871 : Blo 2031435 2032871 := bstep (se 1 (by rfl) ⟨1524653, by rfl⟩ : syracuseStep 2032871 = 3049307) B3049307
theorem B2286985 : Blo 2031435 2286985 := bbase (se 2 (by rfl) ⟨857619, by rfl⟩ : syracuseStep 2286985 = 1715239) (by norm_num)
theorem B3049313 : Blo 2031435 3049313 := bstep (se 2 (by rfl) ⟨1143492, by rfl⟩ : syracuseStep 3049313 = 2286985) B2286985
theorem B2032875 : Blo 2031435 2032875 := bstep (se 1 (by rfl) ⟨1524656, by rfl⟩ : syracuseStep 2032875 = 3049313) B3049313
theorem B13202837 : Blo 2031435 13202837 := bbase (se 6 (by rfl) ⟨309441, by rfl⟩ : syracuseStep 13202837 = 618883) (by norm_num)
theorem B8801891 : Blo 2031435 8801891 := bstep (se 1 (by rfl) ⟨6601418, by rfl⟩ : syracuseStep 8801891 = 13202837) B13202837
theorem B5867927 : Blo 2031435 5867927 := bstep (se 1 (by rfl) ⟨4400945, by rfl⟩ : syracuseStep 5867927 = 8801891) B8801891
theorem B3911951 : Blo 2031435 3911951 := bstep (se 1 (by rfl) ⟨2933963, by rfl⟩ : syracuseStep 3911951 = 5867927) B5867927
theorem B2607967 : Blo 2031435 2607967 := bstep (se 1 (by rfl) ⟨1955975, by rfl⟩ : syracuseStep 2607967 = 3911951) B3911951
theorem B3477289 : Blo 2031435 3477289 := bstep (se 2 (by rfl) ⟨1303983, by rfl⟩ : syracuseStep 3477289 = 2607967) B2607967
theorem B4636385 : Blo 2031435 4636385 := bstep (se 2 (by rfl) ⟨1738644, by rfl⟩ : syracuseStep 4636385 = 3477289) B3477289
theorem B3090923 : Blo 2031435 3090923 := bstep (se 1 (by rfl) ⟨2318192, by rfl⟩ : syracuseStep 3090923 = 4636385) B4636385
theorem B32969845 : Blo 2031435 32969845 := bstep (se 5 (by rfl) ⟨1545461, by rfl⟩ : syracuseStep 32969845 = 3090923) B3090923
theorem B43959793 : Blo 2031435 43959793 := bstep (se 2 (by rfl) ⟨16484922, by rfl⟩ : syracuseStep 43959793 = 32969845) B32969845
theorem B58613057 : Blo 2031435 58613057 := bstep (se 2 (by rfl) ⟨21979896, by rfl⟩ : syracuseStep 58613057 = 43959793) B43959793
theorem B39075371 : Blo 2031435 39075371 := bstep (se 1 (by rfl) ⟨29306528, by rfl⟩ : syracuseStep 39075371 = 58613057) B58613057
theorem B26050247 : Blo 2031435 26050247 := bstep (se 1 (by rfl) ⟨19537685, by rfl⟩ : syracuseStep 26050247 = 39075371) B39075371
theorem B17366831 : Blo 2031435 17366831 := bstep (se 1 (by rfl) ⟨13025123, by rfl⟩ : syracuseStep 17366831 = 26050247) B26050247
theorem B11577887 : Blo 2031435 11577887 := bstep (se 1 (by rfl) ⟨8683415, by rfl⟩ : syracuseStep 11577887 = 17366831) B17366831
theorem B7718591 : Blo 2031435 7718591 := bstep (se 1 (by rfl) ⟨5788943, by rfl⟩ : syracuseStep 7718591 = 11577887) B11577887
theorem B5145727 : Blo 2031435 5145727 := bstep (se 1 (by rfl) ⟨3859295, by rfl⟩ : syracuseStep 5145727 = 7718591) B7718591
theorem B6860969 : Blo 2031435 6860969 := bstep (se 2 (by rfl) ⟨2572863, by rfl⟩ : syracuseStep 6860969 = 5145727) B5145727
theorem B4573979 : Blo 2031435 4573979 := bstep (se 1 (by rfl) ⟨3430484, by rfl⟩ : syracuseStep 4573979 = 6860969) B6860969
theorem B3049319 : Blo 2031435 3049319 := bstep (se 1 (by rfl) ⟨2286989, by rfl⟩ : syracuseStep 3049319 = 4573979) B4573979
theorem B2032879 : Blo 2031435 2032879 := bstep (se 1 (by rfl) ⟨1524659, by rfl⟩ : syracuseStep 2032879 = 3049319) B3049319
theorem B3049325 : Blo 2031435 3049325 := bbase (se 3 (by rfl) ⟨571748, by rfl⟩ : syracuseStep 3049325 = 1143497) (by norm_num)
theorem B2032883 : Blo 2031435 2032883 := bstep (se 1 (by rfl) ⟨1524662, by rfl⟩ : syracuseStep 2032883 = 3049325) B3049325
theorem B4573997 : Blo 2031435 4573997 := bbase (se 3 (by rfl) ⟨857624, by rfl⟩ : syracuseStep 4573997 = 1715249) (by norm_num)
theorem B3049331 : Blo 2031435 3049331 := bstep (se 1 (by rfl) ⟨2286998, by rfl⟩ : syracuseStep 3049331 = 4573997) B4573997
theorem B2032887 : Blo 2031435 2032887 := bstep (se 1 (by rfl) ⟨1524665, by rfl⟩ : syracuseStep 2032887 = 3049331) B3049331
theorem B3256301 : Blo 2031435 3256301 := bbase (se 3 (by rfl) ⟨610556, by rfl⟩ : syracuseStep 3256301 = 1221113) (by norm_num)
theorem B8683469 : Blo 2031435 8683469 := bstep (se 3 (by rfl) ⟨1628150, by rfl⟩ : syracuseStep 8683469 = 3256301) B3256301
theorem B5788979 : Blo 2031435 5788979 := bstep (se 1 (by rfl) ⟨4341734, by rfl⟩ : syracuseStep 5788979 = 8683469) B8683469
theorem B3859319 : Blo 2031435 3859319 := bstep (se 1 (by rfl) ⟨2894489, by rfl⟩ : syracuseStep 3859319 = 5788979) B5788979
theorem B2572879 : Blo 2031435 2572879 := bstep (se 1 (by rfl) ⟨1929659, by rfl⟩ : syracuseStep 2572879 = 3859319) B3859319
theorem B3430505 : Blo 2031435 3430505 := bstep (se 2 (by rfl) ⟨1286439, by rfl⟩ : syracuseStep 3430505 = 2572879) B2572879
theorem B2287003 : Blo 2031435 2287003 := bstep (se 1 (by rfl) ⟨1715252, by rfl⟩ : syracuseStep 2287003 = 3430505) B3430505
theorem B3049337 : Blo 2031435 3049337 := bstep (se 2 (by rfl) ⟨1143501, by rfl⟩ : syracuseStep 3049337 = 2287003) B2287003
theorem B2032891 : Blo 2031435 2032891 := bstep (se 1 (by rfl) ⟨1524668, by rfl⟩ : syracuseStep 2032891 = 3049337) B3049337
theorem B3911981 : Blo 2031435 3911981 := bbase (se 3 (by rfl) ⟨733496, by rfl⟩ : syracuseStep 3911981 = 1466993) (by norm_num)
theorem B10431949 : Blo 2031435 10431949 := bstep (se 3 (by rfl) ⟨1955990, by rfl⟩ : syracuseStep 10431949 = 3911981) B3911981
theorem B13909265 : Blo 2031435 13909265 := bstep (se 2 (by rfl) ⟨5215974, by rfl⟩ : syracuseStep 13909265 = 10431949) B10431949
theorem B9272843 : Blo 2031435 9272843 := bstep (se 1 (by rfl) ⟨6954632, by rfl⟩ : syracuseStep 9272843 = 13909265) B13909265
theorem B6181895 : Blo 2031435 6181895 := bstep (se 1 (by rfl) ⟨4636421, by rfl⟩ : syracuseStep 6181895 = 9272843) B9272843
theorem B4121263 : Blo 2031435 4121263 := bstep (se 1 (by rfl) ⟨3090947, by rfl⟩ : syracuseStep 4121263 = 6181895) B6181895
theorem B21980069 : Blo 2031435 21980069 := bstep (se 4 (by rfl) ⟨2060631, by rfl⟩ : syracuseStep 21980069 = 4121263) B4121263
theorem B14653379 : Blo 2031435 14653379 := bstep (se 1 (by rfl) ⟨10990034, by rfl⟩ : syracuseStep 14653379 = 21980069) B21980069
theorem B9768919 : Blo 2031435 9768919 := bstep (se 1 (by rfl) ⟨7326689, by rfl⟩ : syracuseStep 9768919 = 14653379) B14653379
theorem B13025225 : Blo 2031435 13025225 := bstep (se 2 (by rfl) ⟨4884459, by rfl⟩ : syracuseStep 13025225 = 9768919) B9768919
theorem B34733933 : Blo 2031435 34733933 := bstep (se 3 (by rfl) ⟨6512612, by rfl⟩ : syracuseStep 34733933 = 13025225) B13025225
theorem B23155955 : Blo 2031435 23155955 := bstep (se 1 (by rfl) ⟨17366966, by rfl⟩ : syracuseStep 23155955 = 34733933) B34733933
theorem B15437303 : Blo 2031435 15437303 := bstep (se 1 (by rfl) ⟨11577977, by rfl⟩ : syracuseStep 15437303 = 23155955) B23155955
theorem B10291535 : Blo 2031435 10291535 := bstep (se 1 (by rfl) ⟨7718651, by rfl⟩ : syracuseStep 10291535 = 15437303) B15437303
theorem B6861023 : Blo 2031435 6861023 := bstep (se 1 (by rfl) ⟨5145767, by rfl⟩ : syracuseStep 6861023 = 10291535) B10291535
theorem B4574015 : Blo 2031435 4574015 := bstep (se 1 (by rfl) ⟨3430511, by rfl⟩ : syracuseStep 4574015 = 6861023) B6861023
theorem B3049343 : Blo 2031435 3049343 := bstep (se 1 (by rfl) ⟨2287007, by rfl⟩ : syracuseStep 3049343 = 4574015) B4574015
theorem B2032895 : Blo 2031435 2032895 := bstep (se 1 (by rfl) ⟨1524671, by rfl⟩ : syracuseStep 2032895 = 3049343) B3049343
theorem B3049349 : Blo 2031435 3049349 := bbase (se 4 (by rfl) ⟨285876, by rfl⟩ : syracuseStep 3049349 = 571753) (by norm_num)
theorem B2032899 : Blo 2031435 2032899 := bstep (se 1 (by rfl) ⟨1524674, by rfl⟩ : syracuseStep 2032899 = 3049349) B3049349
theorem B3430525 : Blo 2031435 3430525 := bbase (se 3 (by rfl) ⟨643223, by rfl⟩ : syracuseStep 3430525 = 1286447) (by norm_num)
theorem B4574033 : Blo 2031435 4574033 := bstep (se 2 (by rfl) ⟨1715262, by rfl⟩ : syracuseStep 4574033 = 3430525) B3430525
theorem B3049355 : Blo 2031435 3049355 := bstep (se 1 (by rfl) ⟨2287016, by rfl⟩ : syracuseStep 3049355 = 4574033) B4574033
theorem B2032903 : Blo 2031435 2032903 := bstep (se 1 (by rfl) ⟨1524677, by rfl⟩ : syracuseStep 2032903 = 3049355) B3049355
theorem B2287021 : Blo 2031435 2287021 := bbase (se 3 (by rfl) ⟨428816, by rfl⟩ : syracuseStep 2287021 = 857633) (by norm_num)
theorem B3049361 : Blo 2031435 3049361 := bstep (se 2 (by rfl) ⟨1143510, by rfl⟩ : syracuseStep 3049361 = 2287021) B2287021
theorem B2032907 : Blo 2031435 2032907 := bstep (se 1 (by rfl) ⟨1524680, by rfl⟩ : syracuseStep 2032907 = 3049361) B3049361
theorem B6861077 : Blo 2031435 6861077 := bbase (se 6 (by rfl) ⟨160806, by rfl⟩ : syracuseStep 6861077 = 321613) (by norm_num)
theorem B4574051 : Blo 2031435 4574051 := bstep (se 1 (by rfl) ⟨3430538, by rfl⟩ : syracuseStep 4574051 = 6861077) B6861077
theorem B3049367 : Blo 2031435 3049367 := bstep (se 1 (by rfl) ⟨2287025, by rfl⟩ : syracuseStep 3049367 = 4574051) B4574051
theorem B2032911 : Blo 2031435 2032911 := bstep (se 1 (by rfl) ⟨1524683, by rfl⟩ : syracuseStep 2032911 = 3049367) B3049367
theorem B3049373 : Blo 2031435 3049373 := bbase (se 3 (by rfl) ⟨571757, by rfl⟩ : syracuseStep 3049373 = 1143515) (by norm_num)
theorem B2032915 : Blo 2031435 2032915 := bstep (se 1 (by rfl) ⟨1524686, by rfl⟩ : syracuseStep 2032915 = 3049373) B3049373
theorem B4574069 : Blo 2031435 4574069 := bbase (se 5 (by rfl) ⟨214409, by rfl⟩ : syracuseStep 4574069 = 428819) (by norm_num)
theorem B3049379 : Blo 2031435 3049379 := bstep (se 1 (by rfl) ⟨2287034, by rfl⟩ : syracuseStep 3049379 = 4574069) B4574069
theorem B2032919 : Blo 2031435 2032919 := bstep (se 1 (by rfl) ⟨1524689, by rfl⟩ : syracuseStep 2032919 = 3049379) B3049379
theorem B5948117 : Blo 2031435 5948117 := bbase (se 7 (by rfl) ⟨69704, by rfl⟩ : syracuseStep 5948117 = 139409) (by norm_num)
theorem B3965411 : Blo 2031435 3965411 := bstep (se 1 (by rfl) ⟨2974058, by rfl⟩ : syracuseStep 3965411 = 5948117) B5948117
theorem B2643607 : Blo 2031435 2643607 := bstep (se 1 (by rfl) ⟨1982705, by rfl⟩ : syracuseStep 2643607 = 3965411) B3965411
theorem B3524809 : Blo 2031435 3524809 := bstep (se 2 (by rfl) ⟨1321803, by rfl⟩ : syracuseStep 3524809 = 2643607) B2643607
theorem B4699745 : Blo 2031435 4699745 := bstep (se 2 (by rfl) ⟨1762404, by rfl⟩ : syracuseStep 4699745 = 3524809) B3524809
theorem B3133163 : Blo 2031435 3133163 := bstep (se 1 (by rfl) ⟨2349872, by rfl⟩ : syracuseStep 3133163 = 4699745) B4699745
theorem B2088775 : Blo 2031435 2088775 := bstep (se 1 (by rfl) ⟨1566581, by rfl⟩ : syracuseStep 2088775 = 3133163) B3133163
theorem B2785033 : Blo 2031435 2785033 := bstep (se 2 (by rfl) ⟨1044387, by rfl⟩ : syracuseStep 2785033 = 2088775) B2088775
theorem B14853509 : Blo 2031435 14853509 := bstep (se 4 (by rfl) ⟨1392516, by rfl⟩ : syracuseStep 14853509 = 2785033) B2785033
theorem B9902339 : Blo 2031435 9902339 := bstep (se 1 (by rfl) ⟨7426754, by rfl⟩ : syracuseStep 9902339 = 14853509) B14853509
theorem B6601559 : Blo 2031435 6601559 := bstep (se 1 (by rfl) ⟨4951169, by rfl⟩ : syracuseStep 6601559 = 9902339) B9902339
theorem B17604157 : Blo 2031435 17604157 := bstep (se 3 (by rfl) ⟨3300779, by rfl⟩ : syracuseStep 17604157 = 6601559) B6601559
theorem B23472209 : Blo 2031435 23472209 := bstep (se 2 (by rfl) ⟨8802078, by rfl⟩ : syracuseStep 23472209 = 17604157) B17604157
theorem B15648139 : Blo 2031435 15648139 := bstep (se 1 (by rfl) ⟨11736104, by rfl⟩ : syracuseStep 15648139 = 23472209) B23472209
theorem B20864185 : Blo 2031435 20864185 := bstep (se 2 (by rfl) ⟨7824069, by rfl⟩ : syracuseStep 20864185 = 15648139) B15648139
theorem B111275653 : Blo 2031435 111275653 := bstep (se 4 (by rfl) ⟨10432092, by rfl⟩ : syracuseStep 111275653 = 20864185) B20864185
theorem B148367537 : Blo 2031435 148367537 := bstep (se 2 (by rfl) ⟨55637826, by rfl⟩ : syracuseStep 148367537 = 111275653) B111275653
theorem B98911691 : Blo 2031435 98911691 := bstep (se 1 (by rfl) ⟨74183768, by rfl⟩ : syracuseStep 98911691 = 148367537) B148367537
theorem B65941127 : Blo 2031435 65941127 := bstep (se 1 (by rfl) ⟨49455845, by rfl⟩ : syracuseStep 65941127 = 98911691) B98911691
theorem B43960751 : Blo 2031435 43960751 := bstep (se 1 (by rfl) ⟨32970563, by rfl⟩ : syracuseStep 43960751 = 65941127) B65941127
theorem B29307167 : Blo 2031435 29307167 := bstep (se 1 (by rfl) ⟨21980375, by rfl⟩ : syracuseStep 29307167 = 43960751) B43960751
theorem B19538111 : Blo 2031435 19538111 := bstep (se 1 (by rfl) ⟨14653583, by rfl⟩ : syracuseStep 19538111 = 29307167) B29307167
theorem B13025407 : Blo 2031435 13025407 := bstep (se 1 (by rfl) ⟨9769055, by rfl⟩ : syracuseStep 13025407 = 19538111) B19538111
theorem B17367209 : Blo 2031435 17367209 := bstep (se 2 (by rfl) ⟨6512703, by rfl⟩ : syracuseStep 17367209 = 13025407) B13025407
theorem B11578139 : Blo 2031435 11578139 := bstep (se 1 (by rfl) ⟨8683604, by rfl⟩ : syracuseStep 11578139 = 17367209) B17367209
theorem B7718759 : Blo 2031435 7718759 := bstep (se 1 (by rfl) ⟨5789069, by rfl⟩ : syracuseStep 7718759 = 11578139) B11578139
theorem B5145839 : Blo 2031435 5145839 := bstep (se 1 (by rfl) ⟨3859379, by rfl⟩ : syracuseStep 5145839 = 7718759) B7718759
theorem B3430559 : Blo 2031435 3430559 := bstep (se 1 (by rfl) ⟨2572919, by rfl⟩ : syracuseStep 3430559 = 5145839) B5145839
theorem B2287039 : Blo 2031435 2287039 := bstep (se 1 (by rfl) ⟨1715279, by rfl⟩ : syracuseStep 2287039 = 3430559) B3430559
theorem B3049385 : Blo 2031435 3049385 := bstep (se 2 (by rfl) ⟨1143519, by rfl⟩ : syracuseStep 3049385 = 2287039) B2287039
theorem B2032923 : Blo 2031435 2032923 := bstep (se 1 (by rfl) ⟨1524692, by rfl⟩ : syracuseStep 2032923 = 3049385) B3049385
theorem B7718773 : Blo 2031435 7718773 := bbase (se 5 (by rfl) ⟨361817, by rfl⟩ : syracuseStep 7718773 = 723635) (by norm_num)
theorem B10291697 : Blo 2031435 10291697 := bstep (se 2 (by rfl) ⟨3859386, by rfl⟩ : syracuseStep 10291697 = 7718773) B7718773
theorem B6861131 : Blo 2031435 6861131 := bstep (se 1 (by rfl) ⟨5145848, by rfl⟩ : syracuseStep 6861131 = 10291697) B10291697
theorem B4574087 : Blo 2031435 4574087 := bstep (se 1 (by rfl) ⟨3430565, by rfl⟩ : syracuseStep 4574087 = 6861131) B6861131
theorem B3049391 : Blo 2031435 3049391 := bstep (se 1 (by rfl) ⟨2287043, by rfl⟩ : syracuseStep 3049391 = 4574087) B4574087
theorem B2032927 : Blo 2031435 2032927 := bstep (se 1 (by rfl) ⟨1524695, by rfl⟩ : syracuseStep 2032927 = 3049391) B3049391
theorem B3049397 : Blo 2031435 3049397 := bbase (se 5 (by rfl) ⟨142940, by rfl⟩ : syracuseStep 3049397 = 285881) (by norm_num)
theorem B2032931 : Blo 2031435 2032931 := bstep (se 1 (by rfl) ⟨1524698, by rfl⟩ : syracuseStep 2032931 = 3049397) B3049397
theorem B5145869 : Blo 2031435 5145869 := bbase (se 3 (by rfl) ⟨964850, by rfl⟩ : syracuseStep 5145869 = 1929701) (by norm_num)
theorem B3430579 : Blo 2031435 3430579 := bstep (se 1 (by rfl) ⟨2572934, by rfl⟩ : syracuseStep 3430579 = 5145869) B5145869
theorem B4574105 : Blo 2031435 4574105 := bstep (se 2 (by rfl) ⟨1715289, by rfl⟩ : syracuseStep 4574105 = 3430579) B3430579
theorem B3049403 : Blo 2031435 3049403 := bstep (se 1 (by rfl) ⟨2287052, by rfl⟩ : syracuseStep 3049403 = 4574105) B4574105
theorem B2032935 : Blo 2031435 2032935 := bstep (se 1 (by rfl) ⟨1524701, by rfl⟩ : syracuseStep 2032935 = 3049403) B3049403
theorem B2287057 : Blo 2031435 2287057 := bbase (se 2 (by rfl) ⟨857646, by rfl⟩ : syracuseStep 2287057 = 1715293) (by norm_num)
theorem B3049409 : Blo 2031435 3049409 := bstep (se 2 (by rfl) ⟨1143528, by rfl⟩ : syracuseStep 3049409 = 2287057) B2287057
theorem B2032939 : Blo 2031435 2032939 := bstep (se 1 (by rfl) ⟨1524704, by rfl⟩ : syracuseStep 2032939 = 3049409) B3049409
theorem B4341845 : Blo 2031435 4341845 := bbase (se 8 (by rfl) ⟨25440, by rfl⟩ : syracuseStep 4341845 = 50881) (by norm_num)
theorem B2894563 : Blo 2031435 2894563 := bstep (se 1 (by rfl) ⟨2170922, by rfl⟩ : syracuseStep 2894563 = 4341845) B4341845
theorem B3859417 : Blo 2031435 3859417 := bstep (se 2 (by rfl) ⟨1447281, by rfl⟩ : syracuseStep 3859417 = 2894563) B2894563
theorem B5145889 : Blo 2031435 5145889 := bstep (se 2 (by rfl) ⟨1929708, by rfl⟩ : syracuseStep 5145889 = 3859417) B3859417
theorem B6861185 : Blo 2031435 6861185 := bstep (se 2 (by rfl) ⟨2572944, by rfl⟩ : syracuseStep 6861185 = 5145889) B5145889
theorem B4574123 : Blo 2031435 4574123 := bstep (se 1 (by rfl) ⟨3430592, by rfl⟩ : syracuseStep 4574123 = 6861185) B6861185
theorem B3049415 : Blo 2031435 3049415 := bstep (se 1 (by rfl) ⟨2287061, by rfl⟩ : syracuseStep 3049415 = 4574123) B4574123
theorem B2032943 : Blo 2031435 2032943 := bstep (se 1 (by rfl) ⟨1524707, by rfl⟩ : syracuseStep 2032943 = 3049415) B3049415
theorem B3049421 : Blo 2031435 3049421 := bbase (se 3 (by rfl) ⟨571766, by rfl⟩ : syracuseStep 3049421 = 1143533) (by norm_num)
theorem B2032947 : Blo 2031435 2032947 := bstep (se 1 (by rfl) ⟨1524710, by rfl⟩ : syracuseStep 2032947 = 3049421) B3049421
theorem B4574141 : Blo 2031435 4574141 := bbase (se 3 (by rfl) ⟨857651, by rfl⟩ : syracuseStep 4574141 = 1715303) (by norm_num)
theorem B3049427 : Blo 2031435 3049427 := bstep (se 1 (by rfl) ⟨2287070, by rfl⟩ : syracuseStep 3049427 = 4574141) B4574141
theorem B2032951 : Blo 2031435 2032951 := bstep (se 1 (by rfl) ⟨1524713, by rfl⟩ : syracuseStep 2032951 = 3049427) B3049427
theorem B3430613 : Blo 2031435 3430613 := bbase (se 7 (by rfl) ⟨40202, by rfl⟩ : syracuseStep 3430613 = 80405) (by norm_num)
theorem B2287075 : Blo 2031435 2287075 := bstep (se 1 (by rfl) ⟨1715306, by rfl⟩ : syracuseStep 2287075 = 3430613) B3430613
theorem B3049433 : Blo 2031435 3049433 := bstep (se 2 (by rfl) ⟨1143537, by rfl⟩ : syracuseStep 3049433 = 2287075) B2287075
theorem B2032955 : Blo 2031435 2032955 := bstep (se 1 (by rfl) ⟨1524716, by rfl⟩ : syracuseStep 2032955 = 3049433) B3049433
theorem B3663461 : Blo 2031435 3663461 := bbase (se 4 (by rfl) ⟨343449, by rfl⟩ : syracuseStep 3663461 = 686899) (by norm_num)
theorem B2442307 : Blo 2031435 2442307 := bstep (se 1 (by rfl) ⟨1831730, by rfl⟩ : syracuseStep 2442307 = 3663461) B3663461
theorem B3256409 : Blo 2031435 3256409 := bstep (se 2 (by rfl) ⟨1221153, by rfl⟩ : syracuseStep 3256409 = 2442307) B2442307
theorem B8683757 : Blo 2031435 8683757 := bstep (se 3 (by rfl) ⟨1628204, by rfl⟩ : syracuseStep 8683757 = 3256409) B3256409
theorem B5789171 : Blo 2031435 5789171 := bstep (se 1 (by rfl) ⟨4341878, by rfl⟩ : syracuseStep 5789171 = 8683757) B8683757
theorem B15437789 : Blo 2031435 15437789 := bstep (se 3 (by rfl) ⟨2894585, by rfl⟩ : syracuseStep 15437789 = 5789171) B5789171
theorem B10291859 : Blo 2031435 10291859 := bstep (se 1 (by rfl) ⟨7718894, by rfl⟩ : syracuseStep 10291859 = 15437789) B15437789
theorem B6861239 : Blo 2031435 6861239 := bstep (se 1 (by rfl) ⟨5145929, by rfl⟩ : syracuseStep 6861239 = 10291859) B10291859
theorem B4574159 : Blo 2031435 4574159 := bstep (se 1 (by rfl) ⟨3430619, by rfl⟩ : syracuseStep 4574159 = 6861239) B6861239
theorem B3049439 : Blo 2031435 3049439 := bstep (se 1 (by rfl) ⟨2287079, by rfl⟩ : syracuseStep 3049439 = 4574159) B4574159
theorem B2032959 : Blo 2031435 2032959 := bstep (se 1 (by rfl) ⟨1524719, by rfl⟩ : syracuseStep 2032959 = 3049439) B3049439
theorem B3049445 : Blo 2031435 3049445 := bbase (se 4 (by rfl) ⟨285885, by rfl⟩ : syracuseStep 3049445 = 571771) (by norm_num)
theorem B2032963 : Blo 2031435 2032963 := bstep (se 1 (by rfl) ⟨1524722, by rfl⟩ : syracuseStep 2032963 = 3049445) B3049445
theorem B2442317 : Blo 2031435 2442317 := bbase (se 3 (by rfl) ⟨457934, by rfl⟩ : syracuseStep 2442317 = 915869) (by norm_num)
theorem B6512845 : Blo 2031435 6512845 := bstep (se 3 (by rfl) ⟨1221158, by rfl⟩ : syracuseStep 6512845 = 2442317) B2442317
theorem B8683793 : Blo 2031435 8683793 := bstep (se 2 (by rfl) ⟨3256422, by rfl⟩ : syracuseStep 8683793 = 6512845) B6512845
theorem B5789195 : Blo 2031435 5789195 := bstep (se 1 (by rfl) ⟨4341896, by rfl⟩ : syracuseStep 5789195 = 8683793) B8683793
theorem B3859463 : Blo 2031435 3859463 := bstep (se 1 (by rfl) ⟨2894597, by rfl⟩ : syracuseStep 3859463 = 5789195) B5789195
theorem B2572975 : Blo 2031435 2572975 := bstep (se 1 (by rfl) ⟨1929731, by rfl⟩ : syracuseStep 2572975 = 3859463) B3859463
theorem B3430633 : Blo 2031435 3430633 := bstep (se 2 (by rfl) ⟨1286487, by rfl⟩ : syracuseStep 3430633 = 2572975) B2572975
theorem B4574177 : Blo 2031435 4574177 := bstep (se 2 (by rfl) ⟨1715316, by rfl⟩ : syracuseStep 4574177 = 3430633) B3430633
theorem B3049451 : Blo 2031435 3049451 := bstep (se 1 (by rfl) ⟨2287088, by rfl⟩ : syracuseStep 3049451 = 4574177) B4574177
theorem B2032967 : Blo 2031435 2032967 := bstep (se 1 (by rfl) ⟨1524725, by rfl⟩ : syracuseStep 2032967 = 3049451) B3049451
theorem B2287093 : Blo 2031435 2287093 := bbase (se 5 (by rfl) ⟨107207, by rfl⟩ : syracuseStep 2287093 = 214415) (by norm_num)
theorem B3049457 : Blo 2031435 3049457 := bstep (se 2 (by rfl) ⟨1143546, by rfl⟩ : syracuseStep 3049457 = 2287093) B2287093
theorem B2032971 : Blo 2031435 2032971 := bstep (se 1 (by rfl) ⟨1524728, by rfl⟩ : syracuseStep 2032971 = 3049457) B3049457
theorem B2572985 : Blo 2031435 2572985 := bbase (se 2 (by rfl) ⟨964869, by rfl⟩ : syracuseStep 2572985 = 1929739) (by norm_num)
theorem B6861293 : Blo 2031435 6861293 := bstep (se 3 (by rfl) ⟨1286492, by rfl⟩ : syracuseStep 6861293 = 2572985) B2572985
theorem B4574195 : Blo 2031435 4574195 := bstep (se 1 (by rfl) ⟨3430646, by rfl⟩ : syracuseStep 4574195 = 6861293) B6861293
theorem B3049463 : Blo 2031435 3049463 := bstep (se 1 (by rfl) ⟨2287097, by rfl⟩ : syracuseStep 3049463 = 4574195) B4574195
theorem B2032975 : Blo 2031435 2032975 := bstep (se 1 (by rfl) ⟨1524731, by rfl⟩ : syracuseStep 2032975 = 3049463) B3049463
theorem B3049469 : Blo 2031435 3049469 := bbase (se 3 (by rfl) ⟨571775, by rfl⟩ : syracuseStep 3049469 = 1143551) (by norm_num)
theorem B2032979 : Blo 2031435 2032979 := bstep (se 1 (by rfl) ⟨1524734, by rfl⟩ : syracuseStep 2032979 = 3049469) B3049469
theorem B4574213 : Blo 2031435 4574213 := bbase (se 4 (by rfl) ⟨428832, by rfl⟩ : syracuseStep 4574213 = 857665) (by norm_num)
theorem B3049475 : Blo 2031435 3049475 := bstep (se 1 (by rfl) ⟨2287106, by rfl⟩ : syracuseStep 3049475 = 4574213) B4574213
theorem B2032983 : Blo 2031435 2032983 := bstep (se 1 (by rfl) ⟨1524737, by rfl⟩ : syracuseStep 2032983 = 3049475) B3049475
theorem B3859501 : Blo 2031435 3859501 := bbase (se 3 (by rfl) ⟨723656, by rfl⟩ : syracuseStep 3859501 = 1447313) (by norm_num)
theorem B5146001 : Blo 2031435 5146001 := bstep (se 2 (by rfl) ⟨1929750, by rfl⟩ : syracuseStep 5146001 = 3859501) B3859501
theorem B3430667 : Blo 2031435 3430667 := bstep (se 1 (by rfl) ⟨2573000, by rfl⟩ : syracuseStep 3430667 = 5146001) B5146001
theorem B2287111 : Blo 2031435 2287111 := bstep (se 1 (by rfl) ⟨1715333, by rfl⟩ : syracuseStep 2287111 = 3430667) B3430667
theorem B3049481 : Blo 2031435 3049481 := bstep (se 2 (by rfl) ⟨1143555, by rfl⟩ : syracuseStep 3049481 = 2287111) B2287111
theorem B2032987 : Blo 2031435 2032987 := bstep (se 1 (by rfl) ⟨1524740, by rfl⟩ : syracuseStep 2032987 = 3049481) B3049481
theorem B10292021 : Blo 2031435 10292021 := bbase (se 5 (by rfl) ⟨482438, by rfl⟩ : syracuseStep 10292021 = 964877) (by norm_num)
theorem B6861347 : Blo 2031435 6861347 := bstep (se 1 (by rfl) ⟨5146010, by rfl⟩ : syracuseStep 6861347 = 10292021) B10292021
theorem B4574231 : Blo 2031435 4574231 := bstep (se 1 (by rfl) ⟨3430673, by rfl⟩ : syracuseStep 4574231 = 6861347) B6861347
theorem B3049487 : Blo 2031435 3049487 := bstep (se 1 (by rfl) ⟨2287115, by rfl⟩ : syracuseStep 3049487 = 4574231) B4574231
theorem B2032991 : Blo 2031435 2032991 := bstep (se 1 (by rfl) ⟨1524743, by rfl⟩ : syracuseStep 2032991 = 3049487) B3049487
theorem B3049493 : Blo 2031435 3049493 := bbase (se 6 (by rfl) ⟨71472, by rfl⟩ : syracuseStep 3049493 = 142945) (by norm_num)
theorem B2032995 : Blo 2031435 2032995 := bstep (se 1 (by rfl) ⟨1524746, by rfl⟩ : syracuseStep 2032995 = 3049493) B3049493
theorem B3663533 : Blo 2031435 3663533 := bbase (se 3 (by rfl) ⟨686912, by rfl⟩ : syracuseStep 3663533 = 1373825) (by norm_num)
theorem B2442355 : Blo 2031435 2442355 := bstep (se 1 (by rfl) ⟨1831766, by rfl⟩ : syracuseStep 2442355 = 3663533) B3663533
theorem B13025893 : Blo 2031435 13025893 := bstep (se 4 (by rfl) ⟨1221177, by rfl⟩ : syracuseStep 13025893 = 2442355) B2442355
theorem B17367857 : Blo 2031435 17367857 := bstep (se 2 (by rfl) ⟨6512946, by rfl⟩ : syracuseStep 17367857 = 13025893) B13025893
theorem B11578571 : Blo 2031435 11578571 := bstep (se 1 (by rfl) ⟨8683928, by rfl⟩ : syracuseStep 11578571 = 17367857) B17367857
theorem B7719047 : Blo 2031435 7719047 := bstep (se 1 (by rfl) ⟨5789285, by rfl⟩ : syracuseStep 7719047 = 11578571) B11578571
theorem B5146031 : Blo 2031435 5146031 := bstep (se 1 (by rfl) ⟨3859523, by rfl⟩ : syracuseStep 5146031 = 7719047) B7719047
theorem B3430687 : Blo 2031435 3430687 := bstep (se 1 (by rfl) ⟨2573015, by rfl⟩ : syracuseStep 3430687 = 5146031) B5146031
theorem B4574249 : Blo 2031435 4574249 := bstep (se 2 (by rfl) ⟨1715343, by rfl⟩ : syracuseStep 4574249 = 3430687) B3430687
theorem B3049499 : Blo 2031435 3049499 := bstep (se 1 (by rfl) ⟨2287124, by rfl⟩ : syracuseStep 3049499 = 4574249) B4574249
theorem B2032999 : Blo 2031435 2032999 := bstep (se 1 (by rfl) ⟨1524749, by rfl⟩ : syracuseStep 2032999 = 3049499) B3049499
theorem B2287129 : Blo 2031435 2287129 := bbase (se 2 (by rfl) ⟨857673, by rfl⟩ : syracuseStep 2287129 = 1715347) (by norm_num)
theorem B3049505 : Blo 2031435 3049505 := bstep (se 2 (by rfl) ⟨1143564, by rfl⟩ : syracuseStep 3049505 = 2287129) B2287129
theorem B2033003 : Blo 2031435 2033003 := bstep (se 1 (by rfl) ⟨1524752, by rfl⟩ : syracuseStep 2033003 = 3049505) B3049505
theorem B7719077 : Blo 2031435 7719077 := bbase (se 4 (by rfl) ⟨723663, by rfl⟩ : syracuseStep 7719077 = 1447327) (by norm_num)
theorem B5146051 : Blo 2031435 5146051 := bstep (se 1 (by rfl) ⟨3859538, by rfl⟩ : syracuseStep 5146051 = 7719077) B7719077
theorem B6861401 : Blo 2031435 6861401 := bstep (se 2 (by rfl) ⟨2573025, by rfl⟩ : syracuseStep 6861401 = 5146051) B5146051
theorem B4574267 : Blo 2031435 4574267 := bstep (se 1 (by rfl) ⟨3430700, by rfl⟩ : syracuseStep 4574267 = 6861401) B6861401
theorem B3049511 : Blo 2031435 3049511 := bstep (se 1 (by rfl) ⟨2287133, by rfl⟩ : syracuseStep 3049511 = 4574267) B4574267
theorem B2033007 : Blo 2031435 2033007 := bstep (se 1 (by rfl) ⟨1524755, by rfl⟩ : syracuseStep 2033007 = 3049511) B3049511
theorem B3049517 : Blo 2031435 3049517 := bbase (se 3 (by rfl) ⟨571784, by rfl⟩ : syracuseStep 3049517 = 1143569) (by norm_num)
theorem B2033011 : Blo 2031435 2033011 := bstep (se 1 (by rfl) ⟨1524758, by rfl⟩ : syracuseStep 2033011 = 3049517) B3049517
theorem B4574285 : Blo 2031435 4574285 := bbase (se 3 (by rfl) ⟨857678, by rfl⟩ : syracuseStep 4574285 = 1715357) (by norm_num)
theorem B3049523 : Blo 2031435 3049523 := bstep (se 1 (by rfl) ⟨2287142, by rfl⟩ : syracuseStep 3049523 = 4574285) B4574285
theorem B2033015 : Blo 2031435 2033015 := bstep (se 1 (by rfl) ⟨1524761, by rfl⟩ : syracuseStep 2033015 = 3049523) B3049523
theorem B2573041 : Blo 2031435 2573041 := bbase (se 2 (by rfl) ⟨964890, by rfl⟩ : syracuseStep 2573041 = 1929781) (by norm_num)
theorem B3430721 : Blo 2031435 3430721 := bstep (se 2 (by rfl) ⟨1286520, by rfl⟩ : syracuseStep 3430721 = 2573041) B2573041
theorem B2287147 : Blo 2031435 2287147 := bstep (se 1 (by rfl) ⟨1715360, by rfl⟩ : syracuseStep 2287147 = 3430721) B3430721
theorem B3049529 : Blo 2031435 3049529 := bstep (se 2 (by rfl) ⟨1143573, by rfl⟩ : syracuseStep 3049529 = 2287147) B2287147
theorem B2033019 : Blo 2031435 2033019 := bstep (se 1 (by rfl) ⟨1524764, by rfl⟩ : syracuseStep 2033019 = 3049529) B3049529
theorem B5646341 : Blo 2031435 5646341 := bbase (se 4 (by rfl) ⟨529344, by rfl⟩ : syracuseStep 5646341 = 1058689) (by norm_num)
theorem B3764227 : Blo 2031435 3764227 := bstep (se 1 (by rfl) ⟨2823170, by rfl⟩ : syracuseStep 3764227 = 5646341) B5646341
theorem B5018969 : Blo 2031435 5018969 := bstep (se 2 (by rfl) ⟨1882113, by rfl⟩ : syracuseStep 5018969 = 3764227) B3764227
theorem B13383917 : Blo 2031435 13383917 := bstep (se 3 (by rfl) ⟨2509484, by rfl⟩ : syracuseStep 13383917 = 5018969) B5018969
theorem B8922611 : Blo 2031435 8922611 := bstep (se 1 (by rfl) ⟨6691958, by rfl⟩ : syracuseStep 8922611 = 13383917) B13383917
theorem B5948407 : Blo 2031435 5948407 := bstep (se 1 (by rfl) ⟨4461305, by rfl⟩ : syracuseStep 5948407 = 8922611) B8922611
theorem B7931209 : Blo 2031435 7931209 := bstep (se 2 (by rfl) ⟨2974203, by rfl⟩ : syracuseStep 7931209 = 5948407) B5948407
theorem B10574945 : Blo 2031435 10574945 := bstep (se 2 (by rfl) ⟨3965604, by rfl⟩ : syracuseStep 10574945 = 7931209) B7931209
theorem B7049963 : Blo 2031435 7049963 := bstep (se 1 (by rfl) ⟨5287472, by rfl⟩ : syracuseStep 7049963 = 10574945) B10574945
theorem B18799901 : Blo 2031435 18799901 := bstep (se 3 (by rfl) ⟨3524981, by rfl⟩ : syracuseStep 18799901 = 7049963) B7049963
theorem B12533267 : Blo 2031435 12533267 := bstep (se 1 (by rfl) ⟨9399950, by rfl⟩ : syracuseStep 12533267 = 18799901) B18799901
theorem B8355511 : Blo 2031435 8355511 := bstep (se 1 (by rfl) ⟨6266633, by rfl⟩ : syracuseStep 8355511 = 12533267) B12533267
theorem B11140681 : Blo 2031435 11140681 := bstep (se 2 (by rfl) ⟨4177755, by rfl⟩ : syracuseStep 11140681 = 8355511) B8355511
theorem B14854241 : Blo 2031435 14854241 := bstep (se 2 (by rfl) ⟨5570340, by rfl⟩ : syracuseStep 14854241 = 11140681) B11140681
theorem B9902827 : Blo 2031435 9902827 := bstep (se 1 (by rfl) ⟨7427120, by rfl⟩ : syracuseStep 9902827 = 14854241) B14854241
theorem B13203769 : Blo 2031435 13203769 := bstep (se 2 (by rfl) ⟨4951413, by rfl⟩ : syracuseStep 13203769 = 9902827) B9902827
theorem B17605025 : Blo 2031435 17605025 := bstep (se 2 (by rfl) ⟨6601884, by rfl⟩ : syracuseStep 17605025 = 13203769) B13203769
theorem B11736683 : Blo 2031435 11736683 := bstep (se 1 (by rfl) ⟨8802512, by rfl⟩ : syracuseStep 11736683 = 17605025) B17605025
theorem B7824455 : Blo 2031435 7824455 := bstep (se 1 (by rfl) ⟨5868341, by rfl⟩ : syracuseStep 7824455 = 11736683) B11736683
theorem B5216303 : Blo 2031435 5216303 := bstep (se 1 (by rfl) ⟨3912227, by rfl⟩ : syracuseStep 5216303 = 7824455) B7824455
theorem B3477535 : Blo 2031435 3477535 := bstep (se 1 (by rfl) ⟨2608151, by rfl⟩ : syracuseStep 3477535 = 5216303) B5216303
theorem B74187413 : Blo 2031435 74187413 := bstep (se 6 (by rfl) ⟨1738767, by rfl⟩ : syracuseStep 74187413 = 3477535) B3477535
theorem B49458275 : Blo 2031435 49458275 := bstep (se 1 (by rfl) ⟨37093706, by rfl⟩ : syracuseStep 49458275 = 74187413) B74187413
theorem B32972183 : Blo 2031435 32972183 := bstep (se 1 (by rfl) ⟨24729137, by rfl⟩ : syracuseStep 32972183 = 49458275) B49458275
theorem B21981455 : Blo 2031435 21981455 := bstep (se 1 (by rfl) ⟨16486091, by rfl⟩ : syracuseStep 21981455 = 32972183) B32972183
theorem B14654303 : Blo 2031435 14654303 := bstep (se 1 (by rfl) ⟨10990727, by rfl⟩ : syracuseStep 14654303 = 21981455) B21981455
theorem B9769535 : Blo 2031435 9769535 := bstep (se 1 (by rfl) ⟨7327151, by rfl⟩ : syracuseStep 9769535 = 14654303) B14654303
theorem B6513023 : Blo 2031435 6513023 := bstep (se 1 (by rfl) ⟨4884767, by rfl⟩ : syracuseStep 6513023 = 9769535) B9769535
theorem B4342015 : Blo 2031435 4342015 := bstep (se 1 (by rfl) ⟨3256511, by rfl⟩ : syracuseStep 4342015 = 6513023) B6513023
theorem B23157413 : Blo 2031435 23157413 := bstep (se 4 (by rfl) ⟨2171007, by rfl⟩ : syracuseStep 23157413 = 4342015) B4342015
theorem B15438275 : Blo 2031435 15438275 := bstep (se 1 (by rfl) ⟨11578706, by rfl⟩ : syracuseStep 15438275 = 23157413) B23157413
theorem B10292183 : Blo 2031435 10292183 := bstep (se 1 (by rfl) ⟨7719137, by rfl⟩ : syracuseStep 10292183 = 15438275) B15438275
theorem B6861455 : Blo 2031435 6861455 := bstep (se 1 (by rfl) ⟨5146091, by rfl⟩ : syracuseStep 6861455 = 10292183) B10292183
theorem B4574303 : Blo 2031435 4574303 := bstep (se 1 (by rfl) ⟨3430727, by rfl⟩ : syracuseStep 4574303 = 6861455) B6861455
theorem B3049535 : Blo 2031435 3049535 := bstep (se 1 (by rfl) ⟨2287151, by rfl⟩ : syracuseStep 3049535 = 4574303) B4574303
theorem B2033023 : Blo 2031435 2033023 := bstep (se 1 (by rfl) ⟨1524767, by rfl⟩ : syracuseStep 2033023 = 3049535) B3049535
theorem B3049541 : Blo 2031435 3049541 := bbase (se 4 (by rfl) ⟨285894, by rfl⟩ : syracuseStep 3049541 = 571789) (by norm_num)
theorem B2033027 : Blo 2031435 2033027 := bstep (se 1 (by rfl) ⟨1524770, by rfl⟩ : syracuseStep 2033027 = 3049541) B3049541
theorem B3430741 : Blo 2031435 3430741 := bbase (se 10 (by rfl) ⟨5025, by rfl⟩ : syracuseStep 3430741 = 10051) (by norm_num)
theorem B4574321 : Blo 2031435 4574321 := bstep (se 2 (by rfl) ⟨1715370, by rfl⟩ : syracuseStep 4574321 = 3430741) B3430741
theorem B3049547 : Blo 2031435 3049547 := bstep (se 1 (by rfl) ⟨2287160, by rfl⟩ : syracuseStep 3049547 = 4574321) B4574321
theorem B2033031 : Blo 2031435 2033031 := bstep (se 1 (by rfl) ⟨1524773, by rfl⟩ : syracuseStep 2033031 = 3049547) B3049547
theorem B2287165 : Blo 2031435 2287165 := bbase (se 3 (by rfl) ⟨428843, by rfl⟩ : syracuseStep 2287165 = 857687) (by norm_num)
theorem B3049553 : Blo 2031435 3049553 := bstep (se 2 (by rfl) ⟨1143582, by rfl⟩ : syracuseStep 3049553 = 2287165) B2287165
theorem B2033035 : Blo 2031435 2033035 := bstep (se 1 (by rfl) ⟨1524776, by rfl⟩ : syracuseStep 2033035 = 3049553) B3049553
theorem B6861509 : Blo 2031435 6861509 := bbase (se 4 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 6861509 = 1286533) (by norm_num)
theorem B4574339 : Blo 2031435 4574339 := bstep (se 1 (by rfl) ⟨3430754, by rfl⟩ : syracuseStep 4574339 = 6861509) B6861509
theorem B3049559 : Blo 2031435 3049559 := bstep (se 1 (by rfl) ⟨2287169, by rfl⟩ : syracuseStep 3049559 = 4574339) B4574339
theorem B2033039 : Blo 2031435 2033039 := bstep (se 1 (by rfl) ⟨1524779, by rfl⟩ : syracuseStep 2033039 = 3049559) B3049559
theorem B3049565 : Blo 2031435 3049565 := bbase (se 3 (by rfl) ⟨571793, by rfl⟩ : syracuseStep 3049565 = 1143587) (by norm_num)
theorem B2033043 : Blo 2031435 2033043 := bstep (se 1 (by rfl) ⟨1524782, by rfl⟩ : syracuseStep 2033043 = 3049565) B3049565
theorem B4574357 : Blo 2031435 4574357 := bbase (se 6 (by rfl) ⟨107211, by rfl⟩ : syracuseStep 4574357 = 214423) (by norm_num)
theorem B3049571 : Blo 2031435 3049571 := bstep (se 1 (by rfl) ⟨2287178, by rfl⟩ : syracuseStep 3049571 = 4574357) B4574357
theorem B2033047 : Blo 2031435 2033047 := bstep (se 1 (by rfl) ⟨1524785, by rfl⟩ : syracuseStep 2033047 = 3049571) B3049571
theorem B2894717 : Blo 2031435 2894717 := bbase (se 3 (by rfl) ⟨542759, by rfl⟩ : syracuseStep 2894717 = 1085519) (by norm_num)
theorem B7719245 : Blo 2031435 7719245 := bstep (se 3 (by rfl) ⟨1447358, by rfl⟩ : syracuseStep 7719245 = 2894717) B2894717
theorem B5146163 : Blo 2031435 5146163 := bstep (se 1 (by rfl) ⟨3859622, by rfl⟩ : syracuseStep 5146163 = 7719245) B7719245
theorem B3430775 : Blo 2031435 3430775 := bstep (se 1 (by rfl) ⟨2573081, by rfl⟩ : syracuseStep 3430775 = 5146163) B5146163
theorem B2287183 : Blo 2031435 2287183 := bstep (se 1 (by rfl) ⟨1715387, by rfl⟩ : syracuseStep 2287183 = 3430775) B3430775
theorem B3049577 : Blo 2031435 3049577 := bstep (se 2 (by rfl) ⟨1143591, by rfl⟩ : syracuseStep 3049577 = 2287183) B2287183
theorem B2033051 : Blo 2031435 2033051 := bstep (se 1 (by rfl) ⟨1524788, by rfl⟩ : syracuseStep 2033051 = 3049577) B3049577
theorem B2747725 : Blo 2031435 2747725 := bbase (se 3 (by rfl) ⟨515198, by rfl⟩ : syracuseStep 2747725 = 1030397) (by norm_num)
theorem B14654533 : Blo 2031435 14654533 := bstep (se 4 (by rfl) ⟨1373862, by rfl⟩ : syracuseStep 14654533 = 2747725) B2747725
theorem B19539377 : Blo 2031435 19539377 := bstep (se 2 (by rfl) ⟨7327266, by rfl⟩ : syracuseStep 19539377 = 14654533) B14654533
theorem B13026251 : Blo 2031435 13026251 := bstep (se 1 (by rfl) ⟨9769688, by rfl⟩ : syracuseStep 13026251 = 19539377) B19539377
theorem B8684167 : Blo 2031435 8684167 := bstep (se 1 (by rfl) ⟨6513125, by rfl⟩ : syracuseStep 8684167 = 13026251) B13026251
theorem B11578889 : Blo 2031435 11578889 := bstep (se 2 (by rfl) ⟨4342083, by rfl⟩ : syracuseStep 11578889 = 8684167) B8684167
theorem B7719259 : Blo 2031435 7719259 := bstep (se 1 (by rfl) ⟨5789444, by rfl⟩ : syracuseStep 7719259 = 11578889) B11578889
theorem B10292345 : Blo 2031435 10292345 := bstep (se 2 (by rfl) ⟨3859629, by rfl⟩ : syracuseStep 10292345 = 7719259) B7719259
theorem B6861563 : Blo 2031435 6861563 := bstep (se 1 (by rfl) ⟨5146172, by rfl⟩ : syracuseStep 6861563 = 10292345) B10292345
theorem B4574375 : Blo 2031435 4574375 := bstep (se 1 (by rfl) ⟨3430781, by rfl⟩ : syracuseStep 4574375 = 6861563) B6861563
theorem B3049583 : Blo 2031435 3049583 := bstep (se 1 (by rfl) ⟨2287187, by rfl⟩ : syracuseStep 3049583 = 4574375) B4574375
theorem B2033055 : Blo 2031435 2033055 := bstep (se 1 (by rfl) ⟨1524791, by rfl⟩ : syracuseStep 2033055 = 3049583) B3049583
theorem B3049589 : Blo 2031435 3049589 := bbase (se 5 (by rfl) ⟨142949, by rfl⟩ : syracuseStep 3049589 = 285899) (by norm_num)
theorem B2033059 : Blo 2031435 2033059 := bstep (se 1 (by rfl) ⟨1524794, by rfl⟩ : syracuseStep 2033059 = 3049589) B3049589
theorem B3859645 : Blo 2031435 3859645 := bbase (se 3 (by rfl) ⟨723683, by rfl⟩ : syracuseStep 3859645 = 1447367) (by norm_num)
theorem B5146193 : Blo 2031435 5146193 := bstep (se 2 (by rfl) ⟨1929822, by rfl⟩ : syracuseStep 5146193 = 3859645) B3859645
theorem B3430795 : Blo 2031435 3430795 := bstep (se 1 (by rfl) ⟨2573096, by rfl⟩ : syracuseStep 3430795 = 5146193) B5146193
theorem B4574393 : Blo 2031435 4574393 := bstep (se 2 (by rfl) ⟨1715397, by rfl⟩ : syracuseStep 4574393 = 3430795) B3430795
theorem B3049595 : Blo 2031435 3049595 := bstep (se 1 (by rfl) ⟨2287196, by rfl⟩ : syracuseStep 3049595 = 4574393) B4574393
theorem B2033063 : Blo 2031435 2033063 := bstep (se 1 (by rfl) ⟨1524797, by rfl⟩ : syracuseStep 2033063 = 3049595) B3049595
theorem B2287201 : Blo 2031435 2287201 := bbase (se 2 (by rfl) ⟨857700, by rfl⟩ : syracuseStep 2287201 = 1715401) (by norm_num)
theorem B3049601 : Blo 2031435 3049601 := bstep (se 2 (by rfl) ⟨1143600, by rfl⟩ : syracuseStep 3049601 = 2287201) B2287201
theorem B2033067 : Blo 2031435 2033067 := bstep (se 1 (by rfl) ⟨1524800, by rfl⟩ : syracuseStep 2033067 = 3049601) B3049601
theorem B5146213 : Blo 2031435 5146213 := bbase (se 4 (by rfl) ⟨482457, by rfl⟩ : syracuseStep 5146213 = 964915) (by norm_num)
theorem B6861617 : Blo 2031435 6861617 := bstep (se 2 (by rfl) ⟨2573106, by rfl⟩ : syracuseStep 6861617 = 5146213) B5146213
theorem B4574411 : Blo 2031435 4574411 := bstep (se 1 (by rfl) ⟨3430808, by rfl⟩ : syracuseStep 4574411 = 6861617) B6861617
theorem B3049607 : Blo 2031435 3049607 := bstep (se 1 (by rfl) ⟨2287205, by rfl⟩ : syracuseStep 3049607 = 4574411) B4574411
theorem B2033071 : Blo 2031435 2033071 := bstep (se 1 (by rfl) ⟨1524803, by rfl⟩ : syracuseStep 2033071 = 3049607) B3049607
theorem B3049613 : Blo 2031435 3049613 := bbase (se 3 (by rfl) ⟨571802, by rfl⟩ : syracuseStep 3049613 = 1143605) (by norm_num)
theorem B2033075 : Blo 2031435 2033075 := bstep (se 1 (by rfl) ⟨1524806, by rfl⟩ : syracuseStep 2033075 = 3049613) B3049613
theorem B4574429 : Blo 2031435 4574429 := bbase (se 3 (by rfl) ⟨857705, by rfl⟩ : syracuseStep 4574429 = 1715411) (by norm_num)
theorem B3049619 : Blo 2031435 3049619 := bstep (se 1 (by rfl) ⟨2287214, by rfl⟩ : syracuseStep 3049619 = 4574429) B4574429
theorem B2033079 : Blo 2031435 2033079 := bstep (se 1 (by rfl) ⟨1524809, by rfl⟩ : syracuseStep 2033079 = 3049619) B3049619
theorem B3430829 : Blo 2031435 3430829 := bbase (se 3 (by rfl) ⟨643280, by rfl⟩ : syracuseStep 3430829 = 1286561) (by norm_num)
theorem B2287219 : Blo 2031435 2287219 := bstep (se 1 (by rfl) ⟨1715414, by rfl⟩ : syracuseStep 2287219 = 3430829) B3430829
theorem B3049625 : Blo 2031435 3049625 := bstep (se 2 (by rfl) ⟨1143609, by rfl⟩ : syracuseStep 3049625 = 2287219) B2287219
theorem B2033083 : Blo 2031435 2033083 := bstep (se 1 (by rfl) ⟨1524812, by rfl⟩ : syracuseStep 2033083 = 3049625) B3049625
theorem B37094869 : Blo 2031435 37094869 := bbase (se 7 (by rfl) ⟨434705, by rfl⟩ : syracuseStep 37094869 = 869411) (by norm_num)
theorem B49459825 : Blo 2031435 49459825 := bstep (se 2 (by rfl) ⟨18547434, by rfl⟩ : syracuseStep 49459825 = 37094869) B37094869
theorem B65946433 : Blo 2031435 65946433 := bstep (se 2 (by rfl) ⟨24729912, by rfl⟩ : syracuseStep 65946433 = 49459825) B49459825
theorem B87928577 : Blo 2031435 87928577 := bstep (se 2 (by rfl) ⟨32973216, by rfl⟩ : syracuseStep 87928577 = 65946433) B65946433
theorem B58619051 : Blo 2031435 58619051 := bstep (se 1 (by rfl) ⟨43964288, by rfl⟩ : syracuseStep 58619051 = 87928577) B87928577
theorem B39079367 : Blo 2031435 39079367 := bstep (se 1 (by rfl) ⟨29309525, by rfl⟩ : syracuseStep 39079367 = 58619051) B58619051
theorem B26052911 : Blo 2031435 26052911 := bstep (se 1 (by rfl) ⟨19539683, by rfl⟩ : syracuseStep 26052911 = 39079367) B39079367
theorem B17368607 : Blo 2031435 17368607 := bstep (se 1 (by rfl) ⟨13026455, by rfl⟩ : syracuseStep 17368607 = 26052911) B26052911
theorem B11579071 : Blo 2031435 11579071 := bstep (se 1 (by rfl) ⟨8684303, by rfl⟩ : syracuseStep 11579071 = 17368607) B17368607
theorem B15438761 : Blo 2031435 15438761 := bstep (se 2 (by rfl) ⟨5789535, by rfl⟩ : syracuseStep 15438761 = 11579071) B11579071
theorem B10292507 : Blo 2031435 10292507 := bstep (se 1 (by rfl) ⟨7719380, by rfl⟩ : syracuseStep 10292507 = 15438761) B15438761
theorem B6861671 : Blo 2031435 6861671 := bstep (se 1 (by rfl) ⟨5146253, by rfl⟩ : syracuseStep 6861671 = 10292507) B10292507
theorem B4574447 : Blo 2031435 4574447 := bstep (se 1 (by rfl) ⟨3430835, by rfl⟩ : syracuseStep 4574447 = 6861671) B6861671
theorem B3049631 : Blo 2031435 3049631 := bstep (se 1 (by rfl) ⟨2287223, by rfl⟩ : syracuseStep 3049631 = 4574447) B4574447
theorem B2033087 : Blo 2031435 2033087 := bstep (se 1 (by rfl) ⟨1524815, by rfl⟩ : syracuseStep 2033087 = 3049631) B3049631
theorem B3049637 : Blo 2031435 3049637 := bbase (se 4 (by rfl) ⟨285903, by rfl⟩ : syracuseStep 3049637 = 571807) (by norm_num)
theorem B2033091 : Blo 2031435 2033091 := bstep (se 1 (by rfl) ⟨1524818, by rfl⟩ : syracuseStep 2033091 = 3049637) B3049637
theorem B2573137 : Blo 2031435 2573137 := bbase (se 2 (by rfl) ⟨964926, by rfl⟩ : syracuseStep 2573137 = 1929853) (by norm_num)
theorem B3430849 : Blo 2031435 3430849 := bstep (se 2 (by rfl) ⟨1286568, by rfl⟩ : syracuseStep 3430849 = 2573137) B2573137
theorem B4574465 : Blo 2031435 4574465 := bstep (se 2 (by rfl) ⟨1715424, by rfl⟩ : syracuseStep 4574465 = 3430849) B3430849
theorem B3049643 : Blo 2031435 3049643 := bstep (se 1 (by rfl) ⟨2287232, by rfl⟩ : syracuseStep 3049643 = 4574465) B4574465
theorem B2033095 : Blo 2031435 2033095 := bstep (se 1 (by rfl) ⟨1524821, by rfl⟩ : syracuseStep 2033095 = 3049643) B3049643
theorem B2287237 : Blo 2031435 2287237 := bbase (se 4 (by rfl) ⟨214428, by rfl⟩ : syracuseStep 2287237 = 428857) (by norm_num)
theorem B3049649 : Blo 2031435 3049649 := bstep (se 2 (by rfl) ⟨1143618, by rfl⟩ : syracuseStep 3049649 = 2287237) B2287237
theorem B2033099 : Blo 2031435 2033099 := bstep (se 1 (by rfl) ⟨1524824, by rfl⟩ : syracuseStep 2033099 = 3049649) B3049649
theorem B9273797 : Blo 2031435 9273797 := bbase (se 4 (by rfl) ⟨869418, by rfl⟩ : syracuseStep 9273797 = 1738837) (by norm_num)
theorem B6182531 : Blo 2031435 6182531 := bstep (se 1 (by rfl) ⟨4636898, by rfl⟩ : syracuseStep 6182531 = 9273797) B9273797
theorem B4121687 : Blo 2031435 4121687 := bstep (se 1 (by rfl) ⟨3091265, by rfl⟩ : syracuseStep 4121687 = 6182531) B6182531
theorem B2747791 : Blo 2031435 2747791 := bstep (se 1 (by rfl) ⟨2060843, by rfl⟩ : syracuseStep 2747791 = 4121687) B4121687
theorem B3663721 : Blo 2031435 3663721 := bstep (se 2 (by rfl) ⟨1373895, by rfl⟩ : syracuseStep 3663721 = 2747791) B2747791
theorem B4884961 : Blo 2031435 4884961 := bstep (se 2 (by rfl) ⟨1831860, by rfl⟩ : syracuseStep 4884961 = 3663721) B3663721
theorem B6513281 : Blo 2031435 6513281 := bstep (se 2 (by rfl) ⟨2442480, by rfl⟩ : syracuseStep 6513281 = 4884961) B4884961
theorem B4342187 : Blo 2031435 4342187 := bstep (se 1 (by rfl) ⟨3256640, by rfl⟩ : syracuseStep 4342187 = 6513281) B6513281
theorem B2894791 : Blo 2031435 2894791 := bstep (se 1 (by rfl) ⟨2171093, by rfl⟩ : syracuseStep 2894791 = 4342187) B4342187
theorem B3859721 : Blo 2031435 3859721 := bstep (se 2 (by rfl) ⟨1447395, by rfl⟩ : syracuseStep 3859721 = 2894791) B2894791
theorem B2573147 : Blo 2031435 2573147 := bstep (se 1 (by rfl) ⟨1929860, by rfl⟩ : syracuseStep 2573147 = 3859721) B3859721
theorem B6861725 : Blo 2031435 6861725 := bstep (se 3 (by rfl) ⟨1286573, by rfl⟩ : syracuseStep 6861725 = 2573147) B2573147
theorem B4574483 : Blo 2031435 4574483 := bstep (se 1 (by rfl) ⟨3430862, by rfl⟩ : syracuseStep 4574483 = 6861725) B6861725
theorem B3049655 : Blo 2031435 3049655 := bstep (se 1 (by rfl) ⟨2287241, by rfl⟩ : syracuseStep 3049655 = 4574483) B4574483
theorem B2033103 : Blo 2031435 2033103 := bstep (se 1 (by rfl) ⟨1524827, by rfl⟩ : syracuseStep 2033103 = 3049655) B3049655
theorem B3049661 : Blo 2031435 3049661 := bbase (se 3 (by rfl) ⟨571811, by rfl⟩ : syracuseStep 3049661 = 1143623) (by norm_num)
theorem B2033107 : Blo 2031435 2033107 := bstep (se 1 (by rfl) ⟨1524830, by rfl⟩ : syracuseStep 2033107 = 3049661) B3049661
theorem B4574501 : Blo 2031435 4574501 := bbase (se 4 (by rfl) ⟨428859, by rfl⟩ : syracuseStep 4574501 = 857719) (by norm_num)
theorem B3049667 : Blo 2031435 3049667 := bstep (se 1 (by rfl) ⟨2287250, by rfl⟩ : syracuseStep 3049667 = 4574501) B4574501
theorem B2033111 : Blo 2031435 2033111 := bstep (se 1 (by rfl) ⟨1524833, by rfl⟩ : syracuseStep 2033111 = 3049667) B3049667
theorem B5146325 : Blo 2031435 5146325 := bbase (se 7 (by rfl) ⟨60308, by rfl⟩ : syracuseStep 5146325 = 120617) (by norm_num)
theorem B3430883 : Blo 2031435 3430883 := bstep (se 1 (by rfl) ⟨2573162, by rfl⟩ : syracuseStep 3430883 = 5146325) B5146325
theorem B2287255 : Blo 2031435 2287255 := bstep (se 1 (by rfl) ⟨1715441, by rfl⟩ : syracuseStep 2287255 = 3430883) B3430883
theorem B3049673 : Blo 2031435 3049673 := bstep (se 2 (by rfl) ⟨1143627, by rfl⟩ : syracuseStep 3049673 = 2287255) B2287255
theorem B2033115 : Blo 2031435 2033115 := bstep (se 1 (by rfl) ⟨1524836, by rfl⟩ : syracuseStep 2033115 = 3049673) B3049673
theorem B3663749 : Blo 2031435 3663749 := bbase (se 4 (by rfl) ⟨343476, by rfl⟩ : syracuseStep 3663749 = 686953) (by norm_num)
theorem B9769997 : Blo 2031435 9769997 := bstep (se 3 (by rfl) ⟨1831874, by rfl⟩ : syracuseStep 9769997 = 3663749) B3663749
theorem B6513331 : Blo 2031435 6513331 := bstep (se 1 (by rfl) ⟨4884998, by rfl⟩ : syracuseStep 6513331 = 9769997) B9769997
theorem B8684441 : Blo 2031435 8684441 := bstep (se 2 (by rfl) ⟨3256665, by rfl⟩ : syracuseStep 8684441 = 6513331) B6513331
theorem B5789627 : Blo 2031435 5789627 := bstep (se 1 (by rfl) ⟨4342220, by rfl⟩ : syracuseStep 5789627 = 8684441) B8684441
theorem B3859751 : Blo 2031435 3859751 := bstep (se 1 (by rfl) ⟨2894813, by rfl⟩ : syracuseStep 3859751 = 5789627) B5789627
theorem B10292669 : Blo 2031435 10292669 := bstep (se 3 (by rfl) ⟨1929875, by rfl⟩ : syracuseStep 10292669 = 3859751) B3859751
theorem B6861779 : Blo 2031435 6861779 := bstep (se 1 (by rfl) ⟨5146334, by rfl⟩ : syracuseStep 6861779 = 10292669) B10292669
theorem B4574519 : Blo 2031435 4574519 := bstep (se 1 (by rfl) ⟨3430889, by rfl⟩ : syracuseStep 4574519 = 6861779) B6861779
theorem B3049679 : Blo 2031435 3049679 := bstep (se 1 (by rfl) ⟨2287259, by rfl⟩ : syracuseStep 3049679 = 4574519) B4574519
theorem B2033119 : Blo 2031435 2033119 := bstep (se 1 (by rfl) ⟨1524839, by rfl⟩ : syracuseStep 2033119 = 3049679) B3049679
theorem B3049685 : Blo 2031435 3049685 := bbase (se 7 (by rfl) ⟨35738, by rfl⟩ : syracuseStep 3049685 = 71477) (by norm_num)
theorem B2033123 : Blo 2031435 2033123 := bstep (se 1 (by rfl) ⟨1524842, by rfl⟩ : syracuseStep 2033123 = 3049685) B3049685
theorem B27821717 : Blo 2031435 27821717 := bbase (se 6 (by rfl) ⟨652071, by rfl⟩ : syracuseStep 27821717 = 1304143) (by norm_num)
theorem B18547811 : Blo 2031435 18547811 := bstep (se 1 (by rfl) ⟨13910858, by rfl⟩ : syracuseStep 18547811 = 27821717) B27821717
theorem B12365207 : Blo 2031435 12365207 := bstep (se 1 (by rfl) ⟨9273905, by rfl⟩ : syracuseStep 12365207 = 18547811) B18547811
theorem B8243471 : Blo 2031435 8243471 := bstep (se 1 (by rfl) ⟨6182603, by rfl⟩ : syracuseStep 8243471 = 12365207) B12365207
theorem B5495647 : Blo 2031435 5495647 := bstep (se 1 (by rfl) ⟨4121735, by rfl⟩ : syracuseStep 5495647 = 8243471) B8243471
theorem B7327529 : Blo 2031435 7327529 := bstep (se 2 (by rfl) ⟨2747823, by rfl⟩ : syracuseStep 7327529 = 5495647) B5495647
theorem B4885019 : Blo 2031435 4885019 := bstep (se 1 (by rfl) ⟨3663764, by rfl⟩ : syracuseStep 4885019 = 7327529) B7327529
theorem B3256679 : Blo 2031435 3256679 := bstep (se 1 (by rfl) ⟨2442509, by rfl⟩ : syracuseStep 3256679 = 4885019) B4885019
theorem B2171119 : Blo 2031435 2171119 := bstep (se 1 (by rfl) ⟨1628339, by rfl⟩ : syracuseStep 2171119 = 3256679) B3256679
theorem B2894825 : Blo 2031435 2894825 := bstep (se 2 (by rfl) ⟨1085559, by rfl⟩ : syracuseStep 2894825 = 2171119) B2171119
theorem B7719533 : Blo 2031435 7719533 := bstep (se 3 (by rfl) ⟨1447412, by rfl⟩ : syracuseStep 7719533 = 2894825) B2894825
theorem B5146355 : Blo 2031435 5146355 := bstep (se 1 (by rfl) ⟨3859766, by rfl⟩ : syracuseStep 5146355 = 7719533) B7719533
theorem B3430903 : Blo 2031435 3430903 := bstep (se 1 (by rfl) ⟨2573177, by rfl⟩ : syracuseStep 3430903 = 5146355) B5146355
theorem B4574537 : Blo 2031435 4574537 := bstep (se 2 (by rfl) ⟨1715451, by rfl⟩ : syracuseStep 4574537 = 3430903) B3430903
theorem B3049691 : Blo 2031435 3049691 := bstep (se 1 (by rfl) ⟨2287268, by rfl⟩ : syracuseStep 3049691 = 4574537) B4574537
theorem B2033127 : Blo 2031435 2033127 := bstep (se 1 (by rfl) ⟨1524845, by rfl⟩ : syracuseStep 2033127 = 3049691) B3049691
theorem B2287273 : Blo 2031435 2287273 := bbase (se 2 (by rfl) ⟨857727, by rfl⟩ : syracuseStep 2287273 = 1715455) (by norm_num)
theorem B3049697 : Blo 2031435 3049697 := bstep (se 2 (by rfl) ⟨1143636, by rfl⟩ : syracuseStep 3049697 = 2287273) B2287273
theorem B2033131 : Blo 2031435 2033131 := bstep (se 1 (by rfl) ⟨1524848, by rfl⟩ : syracuseStep 2033131 = 3049697) B3049697
theorem B4885037 : Blo 2031435 4885037 := bbase (se 3 (by rfl) ⟨915944, by rfl⟩ : syracuseStep 4885037 = 1831889) (by norm_num)
theorem B3256691 : Blo 2031435 3256691 := bstep (se 1 (by rfl) ⟨2442518, by rfl⟩ : syracuseStep 3256691 = 4885037) B4885037
theorem B8684509 : Blo 2031435 8684509 := bstep (se 3 (by rfl) ⟨1628345, by rfl⟩ : syracuseStep 8684509 = 3256691) B3256691
theorem B11579345 : Blo 2031435 11579345 := bstep (se 2 (by rfl) ⟨4342254, by rfl⟩ : syracuseStep 11579345 = 8684509) B8684509
theorem B7719563 : Blo 2031435 7719563 := bstep (se 1 (by rfl) ⟨5789672, by rfl⟩ : syracuseStep 7719563 = 11579345) B11579345
theorem B5146375 : Blo 2031435 5146375 := bstep (se 1 (by rfl) ⟨3859781, by rfl⟩ : syracuseStep 5146375 = 7719563) B7719563
theorem B6861833 : Blo 2031435 6861833 := bstep (se 2 (by rfl) ⟨2573187, by rfl⟩ : syracuseStep 6861833 = 5146375) B5146375
theorem B4574555 : Blo 2031435 4574555 := bstep (se 1 (by rfl) ⟨3430916, by rfl⟩ : syracuseStep 4574555 = 6861833) B6861833
theorem B3049703 : Blo 2031435 3049703 := bstep (se 1 (by rfl) ⟨2287277, by rfl⟩ : syracuseStep 3049703 = 4574555) B4574555
theorem B2033135 : Blo 2031435 2033135 := bstep (se 1 (by rfl) ⟨1524851, by rfl⟩ : syracuseStep 2033135 = 3049703) B3049703
theorem B3049709 : Blo 2031435 3049709 := bbase (se 3 (by rfl) ⟨571820, by rfl⟩ : syracuseStep 3049709 = 1143641) (by norm_num)
theorem B2033139 : Blo 2031435 2033139 := bstep (se 1 (by rfl) ⟨1524854, by rfl⟩ : syracuseStep 2033139 = 3049709) B3049709
theorem B4574573 : Blo 2031435 4574573 := bbase (se 3 (by rfl) ⟨857732, by rfl⟩ : syracuseStep 4574573 = 1715465) (by norm_num)
theorem B3049715 : Blo 2031435 3049715 := bstep (se 1 (by rfl) ⟨2287286, by rfl⟩ : syracuseStep 3049715 = 4574573) B4574573
theorem B2033143 : Blo 2031435 2033143 := bstep (se 1 (by rfl) ⟨1524857, by rfl⟩ : syracuseStep 2033143 = 3049715) B3049715
theorem B3859805 : Blo 2031435 3859805 := bbase (se 3 (by rfl) ⟨723713, by rfl⟩ : syracuseStep 3859805 = 1447427) (by norm_num)
theorem B2573203 : Blo 2031435 2573203 := bstep (se 1 (by rfl) ⟨1929902, by rfl⟩ : syracuseStep 2573203 = 3859805) B3859805
theorem B3430937 : Blo 2031435 3430937 := bstep (se 2 (by rfl) ⟨1286601, by rfl⟩ : syracuseStep 3430937 = 2573203) B2573203
theorem B2287291 : Blo 2031435 2287291 := bstep (se 1 (by rfl) ⟨1715468, by rfl⟩ : syracuseStep 2287291 = 3430937) B3430937
theorem B3049721 : Blo 2031435 3049721 := bstep (se 2 (by rfl) ⟨1143645, by rfl⟩ : syracuseStep 3049721 = 2287291) B2287291
theorem B2033147 : Blo 2031435 2033147 := bstep (se 1 (by rfl) ⟨1524860, by rfl⟩ : syracuseStep 2033147 = 3049721) B3049721
theorem B9770149 : Blo 2031435 9770149 := bbase (se 4 (by rfl) ⟨915951, by rfl⟩ : syracuseStep 9770149 = 1831903) (by norm_num)
theorem B52107461 : Blo 2031435 52107461 := bstep (se 4 (by rfl) ⟨4885074, by rfl⟩ : syracuseStep 52107461 = 9770149) B9770149
theorem B34738307 : Blo 2031435 34738307 := bstep (se 1 (by rfl) ⟨26053730, by rfl⟩ : syracuseStep 34738307 = 52107461) B52107461
theorem B23158871 : Blo 2031435 23158871 := bstep (se 1 (by rfl) ⟨17369153, by rfl⟩ : syracuseStep 23158871 = 34738307) B34738307
theorem B15439247 : Blo 2031435 15439247 := bstep (se 1 (by rfl) ⟨11579435, by rfl⟩ : syracuseStep 15439247 = 23158871) B23158871
theorem B10292831 : Blo 2031435 10292831 := bstep (se 1 (by rfl) ⟨7719623, by rfl⟩ : syracuseStep 10292831 = 15439247) B15439247
theorem B6861887 : Blo 2031435 6861887 := bstep (se 1 (by rfl) ⟨5146415, by rfl⟩ : syracuseStep 6861887 = 10292831) B10292831
theorem B4574591 : Blo 2031435 4574591 := bstep (se 1 (by rfl) ⟨3430943, by rfl⟩ : syracuseStep 4574591 = 6861887) B6861887
theorem B3049727 : Blo 2031435 3049727 := bstep (se 1 (by rfl) ⟨2287295, by rfl⟩ : syracuseStep 3049727 = 4574591) B4574591
theorem B2033151 : Blo 2031435 2033151 := bstep (se 1 (by rfl) ⟨1524863, by rfl⟩ : syracuseStep 2033151 = 3049727) B3049727
theorem B3049733 : Blo 2031435 3049733 := bbase (se 4 (by rfl) ⟨285912, by rfl⟩ : syracuseStep 3049733 = 571825) (by norm_num)
theorem B2033155 : Blo 2031435 2033155 := bstep (se 1 (by rfl) ⟨1524866, by rfl⟩ : syracuseStep 2033155 = 3049733) B3049733
theorem B3430957 : Blo 2031435 3430957 := bbase (se 3 (by rfl) ⟨643304, by rfl⟩ : syracuseStep 3430957 = 1286609) (by norm_num)
theorem B4574609 : Blo 2031435 4574609 := bstep (se 2 (by rfl) ⟨1715478, by rfl⟩ : syracuseStep 4574609 = 3430957) B3430957
theorem B3049739 : Blo 2031435 3049739 := bstep (se 1 (by rfl) ⟨2287304, by rfl⟩ : syracuseStep 3049739 = 4574609) B4574609
theorem B2033159 : Blo 2031435 2033159 := bstep (se 1 (by rfl) ⟨1524869, by rfl⟩ : syracuseStep 2033159 = 3049739) B3049739
theorem B2287309 : Blo 2031435 2287309 := bbase (se 3 (by rfl) ⟨428870, by rfl⟩ : syracuseStep 2287309 = 857741) (by norm_num)
theorem B3049745 : Blo 2031435 3049745 := bstep (se 2 (by rfl) ⟨1143654, by rfl⟩ : syracuseStep 3049745 = 2287309) B2287309
theorem B2033163 : Blo 2031435 2033163 := bstep (se 1 (by rfl) ⟨1524872, by rfl⟩ : syracuseStep 2033163 = 3049745) B3049745
theorem B6861941 : Blo 2031435 6861941 := bbase (se 5 (by rfl) ⟨321653, by rfl⟩ : syracuseStep 6861941 = 643307) (by norm_num)
theorem B4574627 : Blo 2031435 4574627 := bstep (se 1 (by rfl) ⟨3430970, by rfl⟩ : syracuseStep 4574627 = 6861941) B6861941
theorem B3049751 : Blo 2031435 3049751 := bstep (se 1 (by rfl) ⟨2287313, by rfl⟩ : syracuseStep 3049751 = 4574627) B4574627
theorem B2033167 : Blo 2031435 2033167 := bstep (se 1 (by rfl) ⟨1524875, by rfl⟩ : syracuseStep 2033167 = 3049751) B3049751
theorem B3049757 : Blo 2031435 3049757 := bbase (se 3 (by rfl) ⟨571829, by rfl⟩ : syracuseStep 3049757 = 1143659) (by norm_num)
theorem B2033171 : Blo 2031435 2033171 := bstep (se 1 (by rfl) ⟨1524878, by rfl⟩ : syracuseStep 2033171 = 3049757) B3049757
theorem B4574645 : Blo 2031435 4574645 := bbase (se 5 (by rfl) ⟨214436, by rfl⟩ : syracuseStep 4574645 = 428873) (by norm_num)
theorem B3049763 : Blo 2031435 3049763 := bstep (se 1 (by rfl) ⟨2287322, by rfl⟩ : syracuseStep 3049763 = 4574645) B4574645
theorem B2033175 : Blo 2031435 2033175 := bstep (se 1 (by rfl) ⟨1524881, by rfl⟩ : syracuseStep 2033175 = 3049763) B3049763
theorem B4342349 : Blo 2031435 4342349 := bbase (se 3 (by rfl) ⟨814190, by rfl⟩ : syracuseStep 4342349 = 1628381) (by norm_num)
theorem B11579597 : Blo 2031435 11579597 := bstep (se 3 (by rfl) ⟨2171174, by rfl⟩ : syracuseStep 11579597 = 4342349) B4342349
theorem B7719731 : Blo 2031435 7719731 := bstep (se 1 (by rfl) ⟨5789798, by rfl⟩ : syracuseStep 7719731 = 11579597) B11579597
theorem B5146487 : Blo 2031435 5146487 := bstep (se 1 (by rfl) ⟨3859865, by rfl⟩ : syracuseStep 5146487 = 7719731) B7719731
theorem B3430991 : Blo 2031435 3430991 := bstep (se 1 (by rfl) ⟨2573243, by rfl⟩ : syracuseStep 3430991 = 5146487) B5146487
theorem B2287327 : Blo 2031435 2287327 := bstep (se 1 (by rfl) ⟨1715495, by rfl⟩ : syracuseStep 2287327 = 3430991) B3430991
theorem B3049769 : Blo 2031435 3049769 := bstep (se 2 (by rfl) ⟨1143663, by rfl⟩ : syracuseStep 3049769 = 2287327) B2287327
theorem B2033179 : Blo 2031435 2033179 := bstep (se 1 (by rfl) ⟨1524884, by rfl⟩ : syracuseStep 2033179 = 3049769) B3049769
theorem B4342357 : Blo 2031435 4342357 := bbase (se 8 (by rfl) ⟨25443, by rfl⟩ : syracuseStep 4342357 = 50887) (by norm_num)
theorem B5789809 : Blo 2031435 5789809 := bstep (se 2 (by rfl) ⟨2171178, by rfl⟩ : syracuseStep 5789809 = 4342357) B4342357
theorem B7719745 : Blo 2031435 7719745 := bstep (se 2 (by rfl) ⟨2894904, by rfl⟩ : syracuseStep 7719745 = 5789809) B5789809
theorem B10292993 : Blo 2031435 10292993 := bstep (se 2 (by rfl) ⟨3859872, by rfl⟩ : syracuseStep 10292993 = 7719745) B7719745
theorem B6861995 : Blo 2031435 6861995 := bstep (se 1 (by rfl) ⟨5146496, by rfl⟩ : syracuseStep 6861995 = 10292993) B10292993
theorem B4574663 : Blo 2031435 4574663 := bstep (se 1 (by rfl) ⟨3430997, by rfl⟩ : syracuseStep 4574663 = 6861995) B6861995
theorem B3049775 : Blo 2031435 3049775 := bstep (se 1 (by rfl) ⟨2287331, by rfl⟩ : syracuseStep 3049775 = 4574663) B4574663
theorem B2033183 : Blo 2031435 2033183 := bstep (se 1 (by rfl) ⟨1524887, by rfl⟩ : syracuseStep 2033183 = 3049775) B3049775
theorem B3049781 : Blo 2031435 3049781 := bbase (se 5 (by rfl) ⟨142958, by rfl⟩ : syracuseStep 3049781 = 285917) (by norm_num)
theorem B2033187 : Blo 2031435 2033187 := bstep (se 1 (by rfl) ⟨1524890, by rfl⟩ : syracuseStep 2033187 = 3049781) B3049781
theorem B5146517 : Blo 2031435 5146517 := bbase (se 6 (by rfl) ⟨120621, by rfl⟩ : syracuseStep 5146517 = 241243) (by norm_num)
theorem B3431011 : Blo 2031435 3431011 := bstep (se 1 (by rfl) ⟨2573258, by rfl⟩ : syracuseStep 3431011 = 5146517) B5146517
theorem B4574681 : Blo 2031435 4574681 := bstep (se 2 (by rfl) ⟨1715505, by rfl⟩ : syracuseStep 4574681 = 3431011) B3431011
theorem B3049787 : Blo 2031435 3049787 := bstep (se 1 (by rfl) ⟨2287340, by rfl⟩ : syracuseStep 3049787 = 4574681) B4574681
theorem B2033191 : Blo 2031435 2033191 := bstep (se 1 (by rfl) ⟨1524893, by rfl⟩ : syracuseStep 2033191 = 3049787) B3049787
theorem B2287345 : Blo 2031435 2287345 := bbase (se 2 (by rfl) ⟨857754, by rfl⟩ : syracuseStep 2287345 = 1715509) (by norm_num)
theorem B3049793 : Blo 2031435 3049793 := bstep (se 2 (by rfl) ⟨1143672, by rfl⟩ : syracuseStep 3049793 = 2287345) B2287345
theorem B2033195 : Blo 2031435 2033195 := bstep (se 1 (by rfl) ⟨1524896, by rfl⟩ : syracuseStep 2033195 = 3049793) B3049793
theorem B4178117 : Blo 2031435 4178117 := bbase (se 4 (by rfl) ⟨391698, by rfl⟩ : syracuseStep 4178117 = 783397) (by norm_num)
theorem B2785411 : Blo 2031435 2785411 := bstep (se 1 (by rfl) ⟨2089058, by rfl⟩ : syracuseStep 2785411 = 4178117) B4178117
theorem B14855525 : Blo 2031435 14855525 := bstep (se 4 (by rfl) ⟨1392705, by rfl⟩ : syracuseStep 14855525 = 2785411) B2785411
theorem B9903683 : Blo 2031435 9903683 := bstep (se 1 (by rfl) ⟨7427762, by rfl⟩ : syracuseStep 9903683 = 14855525) B14855525
theorem B6602455 : Blo 2031435 6602455 := bstep (se 1 (by rfl) ⟨4951841, by rfl⟩ : syracuseStep 6602455 = 9903683) B9903683
theorem B8803273 : Blo 2031435 8803273 := bstep (se 2 (by rfl) ⟨3301227, by rfl⟩ : syracuseStep 8803273 = 6602455) B6602455
theorem B187803157 : Blo 2031435 187803157 := bstep (se 6 (by rfl) ⟨4401636, by rfl⟩ : syracuseStep 187803157 = 8803273) B8803273
theorem B250404209 : Blo 2031435 250404209 := bstep (se 2 (by rfl) ⟨93901578, by rfl⟩ : syracuseStep 250404209 = 187803157) B187803157
theorem B166936139 : Blo 2031435 166936139 := bstep (se 1 (by rfl) ⟨125202104, by rfl⟩ : syracuseStep 166936139 = 250404209) B250404209
theorem B111290759 : Blo 2031435 111290759 := bstep (se 1 (by rfl) ⟨83468069, by rfl⟩ : syracuseStep 111290759 = 166936139) B166936139
theorem B74193839 : Blo 2031435 74193839 := bstep (se 1 (by rfl) ⟨55645379, by rfl⟩ : syracuseStep 74193839 = 111290759) B111290759
theorem B49462559 : Blo 2031435 49462559 := bstep (se 1 (by rfl) ⟨37096919, by rfl⟩ : syracuseStep 49462559 = 74193839) B74193839
theorem B32975039 : Blo 2031435 32975039 := bstep (se 1 (by rfl) ⟨24731279, by rfl⟩ : syracuseStep 32975039 = 49462559) B49462559
theorem B21983359 : Blo 2031435 21983359 := bstep (se 1 (by rfl) ⟨16487519, by rfl⟩ : syracuseStep 21983359 = 32975039) B32975039
theorem B29311145 : Blo 2031435 29311145 := bstep (se 2 (by rfl) ⟨10991679, by rfl⟩ : syracuseStep 29311145 = 21983359) B21983359
theorem B19540763 : Blo 2031435 19540763 := bstep (se 1 (by rfl) ⟨14655572, by rfl⟩ : syracuseStep 19540763 = 29311145) B29311145
theorem B13027175 : Blo 2031435 13027175 := bstep (se 1 (by rfl) ⟨9770381, by rfl⟩ : syracuseStep 13027175 = 19540763) B19540763
theorem B8684783 : Blo 2031435 8684783 := bstep (se 1 (by rfl) ⟨6513587, by rfl⟩ : syracuseStep 8684783 = 13027175) B13027175
theorem B5789855 : Blo 2031435 5789855 := bstep (se 1 (by rfl) ⟨4342391, by rfl⟩ : syracuseStep 5789855 = 8684783) B8684783
theorem B3859903 : Blo 2031435 3859903 := bstep (se 1 (by rfl) ⟨2894927, by rfl⟩ : syracuseStep 3859903 = 5789855) B5789855
theorem B5146537 : Blo 2031435 5146537 := bstep (se 2 (by rfl) ⟨1929951, by rfl⟩ : syracuseStep 5146537 = 3859903) B3859903
theorem B6862049 : Blo 2031435 6862049 := bstep (se 2 (by rfl) ⟨2573268, by rfl⟩ : syracuseStep 6862049 = 5146537) B5146537
theorem B4574699 : Blo 2031435 4574699 := bstep (se 1 (by rfl) ⟨3431024, by rfl⟩ : syracuseStep 4574699 = 6862049) B6862049
theorem B3049799 : Blo 2031435 3049799 := bstep (se 1 (by rfl) ⟨2287349, by rfl⟩ : syracuseStep 3049799 = 4574699) B4574699
theorem B2033199 : Blo 2031435 2033199 := bstep (se 1 (by rfl) ⟨1524899, by rfl⟩ : syracuseStep 2033199 = 3049799) B3049799
theorem B3049805 : Blo 2031435 3049805 := bbase (se 3 (by rfl) ⟨571838, by rfl⟩ : syracuseStep 3049805 = 1143677) (by norm_num)
theorem B2033203 : Blo 2031435 2033203 := bstep (se 1 (by rfl) ⟨1524902, by rfl⟩ : syracuseStep 2033203 = 3049805) B3049805
theorem B4574717 : Blo 2031435 4574717 := bbase (se 3 (by rfl) ⟨857759, by rfl⟩ : syracuseStep 4574717 = 1715519) (by norm_num)
theorem B3049811 : Blo 2031435 3049811 := bstep (se 1 (by rfl) ⟨2287358, by rfl⟩ : syracuseStep 3049811 = 4574717) B4574717
theorem B2033207 : Blo 2031435 2033207 := bstep (se 1 (by rfl) ⟨1524905, by rfl⟩ : syracuseStep 2033207 = 3049811) B3049811
theorem B3431045 : Blo 2031435 3431045 := bbase (se 4 (by rfl) ⟨321660, by rfl⟩ : syracuseStep 3431045 = 643321) (by norm_num)
theorem B2287363 : Blo 2031435 2287363 := bstep (se 1 (by rfl) ⟨1715522, by rfl⟩ : syracuseStep 2287363 = 3431045) B3431045
theorem B3049817 : Blo 2031435 3049817 := bstep (se 2 (by rfl) ⟨1143681, by rfl⟩ : syracuseStep 3049817 = 2287363) B2287363
theorem B2033211 : Blo 2031435 2033211 := bstep (se 1 (by rfl) ⟨1524908, by rfl⟩ : syracuseStep 2033211 = 3049817) B3049817
theorem B15439733 : Blo 2031435 15439733 := bbase (se 5 (by rfl) ⟨723737, by rfl⟩ : syracuseStep 15439733 = 1447475) (by norm_num)
theorem B10293155 : Blo 2031435 10293155 := bstep (se 1 (by rfl) ⟨7719866, by rfl⟩ : syracuseStep 10293155 = 15439733) B15439733
theorem B6862103 : Blo 2031435 6862103 := bstep (se 1 (by rfl) ⟨5146577, by rfl⟩ : syracuseStep 6862103 = 10293155) B10293155
theorem B4574735 : Blo 2031435 4574735 := bstep (se 1 (by rfl) ⟨3431051, by rfl⟩ : syracuseStep 4574735 = 6862103) B6862103
theorem B3049823 : Blo 2031435 3049823 := bstep (se 1 (by rfl) ⟨2287367, by rfl⟩ : syracuseStep 3049823 = 4574735) B4574735
theorem B2033215 : Blo 2031435 2033215 := bstep (se 1 (by rfl) ⟨1524911, by rfl⟩ : syracuseStep 2033215 = 3049823) B3049823
theorem B3049829 : Blo 2031435 3049829 := bbase (se 4 (by rfl) ⟨285921, by rfl⟩ : syracuseStep 3049829 = 571843) (by norm_num)
theorem B2033219 : Blo 2031435 2033219 := bstep (se 1 (by rfl) ⟨1524914, by rfl⟩ : syracuseStep 2033219 = 3049829) B3049829
theorem B3859949 : Blo 2031435 3859949 := bbase (se 3 (by rfl) ⟨723740, by rfl⟩ : syracuseStep 3859949 = 1447481) (by norm_num)
theorem B2573299 : Blo 2031435 2573299 := bstep (se 1 (by rfl) ⟨1929974, by rfl⟩ : syracuseStep 2573299 = 3859949) B3859949
theorem B3431065 : Blo 2031435 3431065 := bstep (se 2 (by rfl) ⟨1286649, by rfl⟩ : syracuseStep 3431065 = 2573299) B2573299
theorem B4574753 : Blo 2031435 4574753 := bstep (se 2 (by rfl) ⟨1715532, by rfl⟩ : syracuseStep 4574753 = 3431065) B3431065
theorem B3049835 : Blo 2031435 3049835 := bstep (se 1 (by rfl) ⟨2287376, by rfl⟩ : syracuseStep 3049835 = 4574753) B4574753
theorem B2033223 : Blo 2031435 2033223 := bstep (se 1 (by rfl) ⟨1524917, by rfl⟩ : syracuseStep 2033223 = 3049835) B3049835
theorem B2287381 : Blo 2031435 2287381 := bbase (se 6 (by rfl) ⟨53610, by rfl⟩ : syracuseStep 2287381 = 107221) (by norm_num)
theorem B3049841 : Blo 2031435 3049841 := bstep (se 2 (by rfl) ⟨1143690, by rfl⟩ : syracuseStep 3049841 = 2287381) B2287381
theorem B2033227 : Blo 2031435 2033227 := bstep (se 1 (by rfl) ⟨1524920, by rfl⟩ : syracuseStep 2033227 = 3049841) B3049841
theorem B2573309 : Blo 2031435 2573309 := bbase (se 3 (by rfl) ⟨482495, by rfl⟩ : syracuseStep 2573309 = 964991) (by norm_num)
theorem B6862157 : Blo 2031435 6862157 := bstep (se 3 (by rfl) ⟨1286654, by rfl⟩ : syracuseStep 6862157 = 2573309) B2573309
theorem B4574771 : Blo 2031435 4574771 := bstep (se 1 (by rfl) ⟨3431078, by rfl⟩ : syracuseStep 4574771 = 6862157) B6862157
theorem B3049847 : Blo 2031435 3049847 := bstep (se 1 (by rfl) ⟨2287385, by rfl⟩ : syracuseStep 3049847 = 4574771) B4574771
theorem B2033231 : Blo 2031435 2033231 := bstep (se 1 (by rfl) ⟨1524923, by rfl⟩ : syracuseStep 2033231 = 3049847) B3049847
theorem B3049853 : Blo 2031435 3049853 := bbase (se 3 (by rfl) ⟨571847, by rfl⟩ : syracuseStep 3049853 = 1143695) (by norm_num)
theorem B2033235 : Blo 2031435 2033235 := bstep (se 1 (by rfl) ⟨1524926, by rfl⟩ : syracuseStep 2033235 = 3049853) B3049853
theorem B4574789 : Blo 2031435 4574789 := bbase (se 4 (by rfl) ⟨428886, by rfl⟩ : syracuseStep 4574789 = 857773) (by norm_num)
theorem B3049859 : Blo 2031435 3049859 := bstep (se 1 (by rfl) ⟨2287394, by rfl⟩ : syracuseStep 3049859 = 4574789) B4574789
theorem B2033239 : Blo 2031435 2033239 := bstep (se 1 (by rfl) ⟨1524929, by rfl⟩ : syracuseStep 2033239 = 3049859) B3049859
theorem B2442649 : Blo 2031435 2442649 := bbase (se 2 (by rfl) ⟨915993, by rfl⟩ : syracuseStep 2442649 = 1831987) (by norm_num)
theorem B3256865 : Blo 2031435 3256865 := bstep (se 2 (by rfl) ⟨1221324, by rfl⟩ : syracuseStep 3256865 = 2442649) B2442649
theorem B2171243 : Blo 2031435 2171243 := bstep (se 1 (by rfl) ⟨1628432, by rfl⟩ : syracuseStep 2171243 = 3256865) B3256865
theorem B5789981 : Blo 2031435 5789981 := bstep (se 3 (by rfl) ⟨1085621, by rfl⟩ : syracuseStep 5789981 = 2171243) B2171243
theorem B3859987 : Blo 2031435 3859987 := bstep (se 1 (by rfl) ⟨2894990, by rfl⟩ : syracuseStep 3859987 = 5789981) B5789981
theorem B5146649 : Blo 2031435 5146649 := bstep (se 2 (by rfl) ⟨1929993, by rfl⟩ : syracuseStep 5146649 = 3859987) B3859987
theorem B3431099 : Blo 2031435 3431099 := bstep (se 1 (by rfl) ⟨2573324, by rfl⟩ : syracuseStep 3431099 = 5146649) B5146649
theorem B2287399 : Blo 2031435 2287399 := bstep (se 1 (by rfl) ⟨1715549, by rfl⟩ : syracuseStep 2287399 = 3431099) B3431099
theorem B3049865 : Blo 2031435 3049865 := bstep (se 2 (by rfl) ⟨1143699, by rfl⟩ : syracuseStep 3049865 = 2287399) B2287399
theorem B2033243 : Blo 2031435 2033243 := bstep (se 1 (by rfl) ⟨1524932, by rfl⟩ : syracuseStep 2033243 = 3049865) B3049865
theorem B10293317 : Blo 2031435 10293317 := bbase (se 4 (by rfl) ⟨964998, by rfl⟩ : syracuseStep 10293317 = 1929997) (by norm_num)
theorem B6862211 : Blo 2031435 6862211 := bstep (se 1 (by rfl) ⟨5146658, by rfl⟩ : syracuseStep 6862211 = 10293317) B10293317
theorem B4574807 : Blo 2031435 4574807 := bstep (se 1 (by rfl) ⟨3431105, by rfl⟩ : syracuseStep 4574807 = 6862211) B6862211
theorem B3049871 : Blo 2031435 3049871 := bstep (se 1 (by rfl) ⟨2287403, by rfl⟩ : syracuseStep 3049871 = 4574807) B4574807
theorem B2033247 : Blo 2031435 2033247 := bstep (se 1 (by rfl) ⟨1524935, by rfl⟩ : syracuseStep 2033247 = 3049871) B3049871
theorem B3049877 : Blo 2031435 3049877 := bbase (se 6 (by rfl) ⟨71481, by rfl⟩ : syracuseStep 3049877 = 142963) (by norm_num)
theorem B2033251 : Blo 2031435 2033251 := bstep (se 1 (by rfl) ⟨1524938, by rfl⟩ : syracuseStep 2033251 = 3049877) B3049877
theorem B41735189 : Blo 2031435 41735189 := bbase (se 6 (by rfl) ⟨978168, by rfl⟩ : syracuseStep 41735189 = 1956337) (by norm_num)
theorem B27823459 : Blo 2031435 27823459 := bstep (se 1 (by rfl) ⟨20867594, by rfl⟩ : syracuseStep 27823459 = 41735189) B41735189
theorem B37097945 : Blo 2031435 37097945 := bstep (se 2 (by rfl) ⟨13911729, by rfl⟩ : syracuseStep 37097945 = 27823459) B27823459
theorem B24731963 : Blo 2031435 24731963 := bstep (se 1 (by rfl) ⟨18548972, by rfl⟩ : syracuseStep 24731963 = 37097945) B37097945
theorem B16487975 : Blo 2031435 16487975 := bstep (se 1 (by rfl) ⟨12365981, by rfl⟩ : syracuseStep 16487975 = 24731963) B24731963
theorem B10991983 : Blo 2031435 10991983 := bstep (se 1 (by rfl) ⟨8243987, by rfl⟩ : syracuseStep 10991983 = 16487975) B16487975
theorem B14655977 : Blo 2031435 14655977 := bstep (se 2 (by rfl) ⟨5495991, by rfl⟩ : syracuseStep 14655977 = 10991983) B10991983
theorem B9770651 : Blo 2031435 9770651 := bstep (se 1 (by rfl) ⟨7327988, by rfl⟩ : syracuseStep 9770651 = 14655977) B14655977
theorem B6513767 : Blo 2031435 6513767 := bstep (se 1 (by rfl) ⟨4885325, by rfl⟩ : syracuseStep 6513767 = 9770651) B9770651
theorem B4342511 : Blo 2031435 4342511 := bstep (se 1 (by rfl) ⟨3256883, by rfl⟩ : syracuseStep 4342511 = 6513767) B6513767
theorem B11580029 : Blo 2031435 11580029 := bstep (se 3 (by rfl) ⟨2171255, by rfl⟩ : syracuseStep 11580029 = 4342511) B4342511
theorem B7720019 : Blo 2031435 7720019 := bstep (se 1 (by rfl) ⟨5790014, by rfl⟩ : syracuseStep 7720019 = 11580029) B11580029
theorem B5146679 : Blo 2031435 5146679 := bstep (se 1 (by rfl) ⟨3860009, by rfl⟩ : syracuseStep 5146679 = 7720019) B7720019
theorem B3431119 : Blo 2031435 3431119 := bstep (se 1 (by rfl) ⟨2573339, by rfl⟩ : syracuseStep 3431119 = 5146679) B5146679
theorem B4574825 : Blo 2031435 4574825 := bstep (se 2 (by rfl) ⟨1715559, by rfl⟩ : syracuseStep 4574825 = 3431119) B3431119
theorem B3049883 : Blo 2031435 3049883 := bstep (se 1 (by rfl) ⟨2287412, by rfl⟩ : syracuseStep 3049883 = 4574825) B4574825
theorem B2033255 : Blo 2031435 2033255 := bstep (se 1 (by rfl) ⟨1524941, by rfl⟩ : syracuseStep 2033255 = 3049883) B3049883
theorem B2287417 : Blo 2031435 2287417 := bbase (se 2 (by rfl) ⟨857781, by rfl⟩ : syracuseStep 2287417 = 1715563) (by norm_num)
theorem B3049889 : Blo 2031435 3049889 := bstep (se 2 (by rfl) ⟨1143708, by rfl⟩ : syracuseStep 3049889 = 2287417) B2287417
theorem B2033259 : Blo 2031435 2033259 := bstep (se 1 (by rfl) ⟨1524944, by rfl⟩ : syracuseStep 2033259 = 3049889) B3049889
theorem B5790037 : Blo 2031435 5790037 := bbase (se 10 (by rfl) ⟨8481, by rfl⟩ : syracuseStep 5790037 = 16963) (by norm_num)
theorem B7720049 : Blo 2031435 7720049 := bstep (se 2 (by rfl) ⟨2895018, by rfl⟩ : syracuseStep 7720049 = 5790037) B5790037
theorem B5146699 : Blo 2031435 5146699 := bstep (se 1 (by rfl) ⟨3860024, by rfl⟩ : syracuseStep 5146699 = 7720049) B7720049
theorem B6862265 : Blo 2031435 6862265 := bstep (se 2 (by rfl) ⟨2573349, by rfl⟩ : syracuseStep 6862265 = 5146699) B5146699
theorem B4574843 : Blo 2031435 4574843 := bstep (se 1 (by rfl) ⟨3431132, by rfl⟩ : syracuseStep 4574843 = 6862265) B6862265
theorem B3049895 : Blo 2031435 3049895 := bstep (se 1 (by rfl) ⟨2287421, by rfl⟩ : syracuseStep 3049895 = 4574843) B4574843
theorem B2033263 : Blo 2031435 2033263 := bstep (se 1 (by rfl) ⟨1524947, by rfl⟩ : syracuseStep 2033263 = 3049895) B3049895
theorem B3049901 : Blo 2031435 3049901 := bbase (se 3 (by rfl) ⟨571856, by rfl⟩ : syracuseStep 3049901 = 1143713) (by norm_num)
theorem B2033267 : Blo 2031435 2033267 := bstep (se 1 (by rfl) ⟨1524950, by rfl⟩ : syracuseStep 2033267 = 3049901) B3049901
theorem B4574861 : Blo 2031435 4574861 := bbase (se 3 (by rfl) ⟨857786, by rfl⟩ : syracuseStep 4574861 = 1715573) (by norm_num)
theorem B3049907 : Blo 2031435 3049907 := bstep (se 1 (by rfl) ⟨2287430, by rfl⟩ : syracuseStep 3049907 = 4574861) B4574861
theorem B2033271 : Blo 2031435 2033271 := bstep (se 1 (by rfl) ⟨1524953, by rfl⟩ : syracuseStep 2033271 = 3049907) B3049907
theorem B2573365 : Blo 2031435 2573365 := bbase (se 5 (by rfl) ⟨120626, by rfl⟩ : syracuseStep 2573365 = 241253) (by norm_num)
theorem B3431153 : Blo 2031435 3431153 := bstep (se 2 (by rfl) ⟨1286682, by rfl⟩ : syracuseStep 3431153 = 2573365) B2573365
theorem B2287435 : Blo 2031435 2287435 := bstep (se 1 (by rfl) ⟨1715576, by rfl⟩ : syracuseStep 2287435 = 3431153) B3431153
theorem B3049913 : Blo 2031435 3049913 := bstep (se 2 (by rfl) ⟨1143717, by rfl⟩ : syracuseStep 3049913 = 2287435) B2287435
theorem B2033275 : Blo 2031435 2033275 := bstep (se 1 (by rfl) ⟨1524956, by rfl⟩ : syracuseStep 2033275 = 3049913) B3049913
theorem B3477973 : Blo 2031435 3477973 := bbase (se 7 (by rfl) ⟨40757, by rfl⟩ : syracuseStep 3477973 = 81515) (by norm_num)
theorem B4637297 : Blo 2031435 4637297 := bstep (se 2 (by rfl) ⟨1738986, by rfl⟩ : syracuseStep 4637297 = 3477973) B3477973
theorem B12366125 : Blo 2031435 12366125 := bstep (se 3 (by rfl) ⟨2318648, by rfl⟩ : syracuseStep 12366125 = 4637297) B4637297
theorem B8244083 : Blo 2031435 8244083 := bstep (se 1 (by rfl) ⟨6183062, by rfl⟩ : syracuseStep 8244083 = 12366125) B12366125
theorem B5496055 : Blo 2031435 5496055 := bstep (se 1 (by rfl) ⟨4122041, by rfl⟩ : syracuseStep 5496055 = 8244083) B8244083
theorem B29312293 : Blo 2031435 29312293 := bstep (se 4 (by rfl) ⟨2748027, by rfl⟩ : syracuseStep 29312293 = 5496055) B5496055
theorem B39083057 : Blo 2031435 39083057 := bstep (se 2 (by rfl) ⟨14656146, by rfl⟩ : syracuseStep 39083057 = 29312293) B29312293
theorem B26055371 : Blo 2031435 26055371 := bstep (se 1 (by rfl) ⟨19541528, by rfl⟩ : syracuseStep 26055371 = 39083057) B39083057
theorem B17370247 : Blo 2031435 17370247 := bstep (se 1 (by rfl) ⟨13027685, by rfl⟩ : syracuseStep 17370247 = 26055371) B26055371
theorem B23160329 : Blo 2031435 23160329 := bstep (se 2 (by rfl) ⟨8685123, by rfl⟩ : syracuseStep 23160329 = 17370247) B17370247
theorem B15440219 : Blo 2031435 15440219 := bstep (se 1 (by rfl) ⟨11580164, by rfl⟩ : syracuseStep 15440219 = 23160329) B23160329
theorem B10293479 : Blo 2031435 10293479 := bstep (se 1 (by rfl) ⟨7720109, by rfl⟩ : syracuseStep 10293479 = 15440219) B15440219
theorem B6862319 : Blo 2031435 6862319 := bstep (se 1 (by rfl) ⟨5146739, by rfl⟩ : syracuseStep 6862319 = 10293479) B10293479
theorem B4574879 : Blo 2031435 4574879 := bstep (se 1 (by rfl) ⟨3431159, by rfl⟩ : syracuseStep 4574879 = 6862319) B6862319
theorem B3049919 : Blo 2031435 3049919 := bstep (se 1 (by rfl) ⟨2287439, by rfl⟩ : syracuseStep 3049919 = 4574879) B4574879
theorem B2033279 : Blo 2031435 2033279 := bstep (se 1 (by rfl) ⟨1524959, by rfl⟩ : syracuseStep 2033279 = 3049919) B3049919
theorem B3049925 : Blo 2031435 3049925 := bbase (se 4 (by rfl) ⟨285930, by rfl⟩ : syracuseStep 3049925 = 571861) (by norm_num)
theorem B2033283 : Blo 2031435 2033283 := bstep (se 1 (by rfl) ⟨1524962, by rfl⟩ : syracuseStep 2033283 = 3049925) B3049925
theorem B3431173 : Blo 2031435 3431173 := bbase (se 4 (by rfl) ⟨321672, by rfl⟩ : syracuseStep 3431173 = 643345) (by norm_num)
theorem B4574897 : Blo 2031435 4574897 := bstep (se 2 (by rfl) ⟨1715586, by rfl⟩ : syracuseStep 4574897 = 3431173) B3431173
theorem B3049931 : Blo 2031435 3049931 := bstep (se 1 (by rfl) ⟨2287448, by rfl⟩ : syracuseStep 3049931 = 4574897) B4574897
theorem B2033287 : Blo 2031435 2033287 := bstep (se 1 (by rfl) ⟨1524965, by rfl⟩ : syracuseStep 2033287 = 3049931) B3049931
theorem B2287453 : Blo 2031435 2287453 := bbase (se 3 (by rfl) ⟨428897, by rfl⟩ : syracuseStep 2287453 = 857795) (by norm_num)
theorem B3049937 : Blo 2031435 3049937 := bstep (se 2 (by rfl) ⟨1143726, by rfl⟩ : syracuseStep 3049937 = 2287453) B2287453
theorem B2033291 : Blo 2031435 2033291 := bstep (se 1 (by rfl) ⟨1524968, by rfl⟩ : syracuseStep 2033291 = 3049937) B3049937
theorem B6862373 : Blo 2031435 6862373 := bbase (se 4 (by rfl) ⟨643347, by rfl⟩ : syracuseStep 6862373 = 1286695) (by norm_num)
theorem B4574915 : Blo 2031435 4574915 := bstep (se 1 (by rfl) ⟨3431186, by rfl⟩ : syracuseStep 4574915 = 6862373) B6862373
theorem B3049943 : Blo 2031435 3049943 := bstep (se 1 (by rfl) ⟨2287457, by rfl⟩ : syracuseStep 3049943 = 4574915) B4574915
theorem B2033295 : Blo 2031435 2033295 := bstep (se 1 (by rfl) ⟨1524971, by rfl⟩ : syracuseStep 2033295 = 3049943) B3049943
theorem B3049949 : Blo 2031435 3049949 := bbase (se 3 (by rfl) ⟨571865, by rfl⟩ : syracuseStep 3049949 = 1143731) (by norm_num)
theorem B2033299 : Blo 2031435 2033299 := bstep (se 1 (by rfl) ⟨1524974, by rfl⟩ : syracuseStep 2033299 = 3049949) B3049949
theorem B4574933 : Blo 2031435 4574933 := bbase (se 7 (by rfl) ⟨53612, by rfl⟩ : syracuseStep 4574933 = 107225) (by norm_num)
theorem B3049955 : Blo 2031435 3049955 := bstep (se 1 (by rfl) ⟨2287466, by rfl⟩ : syracuseStep 3049955 = 4574933) B4574933
theorem B2033303 : Blo 2031435 2033303 := bstep (se 1 (by rfl) ⟨1524977, by rfl⟩ : syracuseStep 2033303 = 3049955) B3049955
theorem B5496133 : Blo 2031435 5496133 := bbase (se 4 (by rfl) ⟨515262, by rfl⟩ : syracuseStep 5496133 = 1030525) (by norm_num)
theorem B7328177 : Blo 2031435 7328177 := bstep (se 2 (by rfl) ⟨2748066, by rfl⟩ : syracuseStep 7328177 = 5496133) B5496133
theorem B4885451 : Blo 2031435 4885451 := bstep (se 1 (by rfl) ⟨3664088, by rfl⟩ : syracuseStep 4885451 = 7328177) B7328177
theorem B3256967 : Blo 2031435 3256967 := bstep (se 1 (by rfl) ⟨2442725, by rfl⟩ : syracuseStep 3256967 = 4885451) B4885451
theorem B8685245 : Blo 2031435 8685245 := bstep (se 3 (by rfl) ⟨1628483, by rfl⟩ : syracuseStep 8685245 = 3256967) B3256967
theorem B5790163 : Blo 2031435 5790163 := bstep (se 1 (by rfl) ⟨4342622, by rfl⟩ : syracuseStep 5790163 = 8685245) B8685245
theorem B7720217 : Blo 2031435 7720217 := bstep (se 2 (by rfl) ⟨2895081, by rfl⟩ : syracuseStep 7720217 = 5790163) B5790163
theorem B5146811 : Blo 2031435 5146811 := bstep (se 1 (by rfl) ⟨3860108, by rfl⟩ : syracuseStep 5146811 = 7720217) B7720217
theorem B3431207 : Blo 2031435 3431207 := bstep (se 1 (by rfl) ⟨2573405, by rfl⟩ : syracuseStep 3431207 = 5146811) B5146811
theorem B2287471 : Blo 2031435 2287471 := bstep (se 1 (by rfl) ⟨1715603, by rfl⟩ : syracuseStep 2287471 = 3431207) B3431207
theorem B3049961 : Blo 2031435 3049961 := bstep (se 2 (by rfl) ⟨1143735, by rfl⟩ : syracuseStep 3049961 = 2287471) B2287471
theorem B2033307 : Blo 2031435 2033307 := bstep (se 1 (by rfl) ⟨1524980, by rfl⟩ : syracuseStep 2033307 = 3049961) B3049961
theorem B4952117 : Blo 2031435 4952117 := bbase (se 5 (by rfl) ⟨232130, by rfl⟩ : syracuseStep 4952117 = 464261) (by norm_num)
theorem B3301411 : Blo 2031435 3301411 := bstep (se 1 (by rfl) ⟨2476058, by rfl⟩ : syracuseStep 3301411 = 4952117) B4952117
theorem B4401881 : Blo 2031435 4401881 := bstep (se 2 (by rfl) ⟨1650705, by rfl⟩ : syracuseStep 4401881 = 3301411) B3301411
theorem B2934587 : Blo 2031435 2934587 := bstep (se 1 (by rfl) ⟨2200940, by rfl⟩ : syracuseStep 2934587 = 4401881) B4401881
theorem B7825565 : Blo 2031435 7825565 := bstep (se 3 (by rfl) ⟨1467293, by rfl⟩ : syracuseStep 7825565 = 2934587) B2934587
theorem B5217043 : Blo 2031435 5217043 := bstep (se 1 (by rfl) ⟨3912782, by rfl⟩ : syracuseStep 5217043 = 7825565) B7825565
theorem B6956057 : Blo 2031435 6956057 := bstep (se 2 (by rfl) ⟨2608521, by rfl⟩ : syracuseStep 6956057 = 5217043) B5217043
theorem B4637371 : Blo 2031435 4637371 := bstep (se 1 (by rfl) ⟨3478028, by rfl⟩ : syracuseStep 4637371 = 6956057) B6956057
theorem B6183161 : Blo 2031435 6183161 := bstep (se 2 (by rfl) ⟨2318685, by rfl⟩ : syracuseStep 6183161 = 4637371) B4637371
theorem B4122107 : Blo 2031435 4122107 := bstep (se 1 (by rfl) ⟨3091580, by rfl⟩ : syracuseStep 4122107 = 6183161) B6183161
theorem B2748071 : Blo 2031435 2748071 := bstep (se 1 (by rfl) ⟨2061053, by rfl⟩ : syracuseStep 2748071 = 4122107) B4122107
theorem B7328189 : Blo 2031435 7328189 := bstep (se 3 (by rfl) ⟨1374035, by rfl⟩ : syracuseStep 7328189 = 2748071) B2748071
theorem B19541837 : Blo 2031435 19541837 := bstep (se 3 (by rfl) ⟨3664094, by rfl⟩ : syracuseStep 19541837 = 7328189) B7328189
theorem B13027891 : Blo 2031435 13027891 := bstep (se 1 (by rfl) ⟨9770918, by rfl⟩ : syracuseStep 13027891 = 19541837) B19541837
theorem B17370521 : Blo 2031435 17370521 := bstep (se 2 (by rfl) ⟨6513945, by rfl⟩ : syracuseStep 17370521 = 13027891) B13027891
theorem B11580347 : Blo 2031435 11580347 := bstep (se 1 (by rfl) ⟨8685260, by rfl⟩ : syracuseStep 11580347 = 17370521) B17370521
theorem B7720231 : Blo 2031435 7720231 := bstep (se 1 (by rfl) ⟨5790173, by rfl⟩ : syracuseStep 7720231 = 11580347) B11580347
theorem B10293641 : Blo 2031435 10293641 := bstep (se 2 (by rfl) ⟨3860115, by rfl⟩ : syracuseStep 10293641 = 7720231) B7720231
theorem B6862427 : Blo 2031435 6862427 := bstep (se 1 (by rfl) ⟨5146820, by rfl⟩ : syracuseStep 6862427 = 10293641) B10293641
theorem B4574951 : Blo 2031435 4574951 := bstep (se 1 (by rfl) ⟨3431213, by rfl⟩ : syracuseStep 4574951 = 6862427) B6862427
theorem B3049967 : Blo 2031435 3049967 := bstep (se 1 (by rfl) ⟨2287475, by rfl⟩ : syracuseStep 3049967 = 4574951) B4574951
theorem B2033311 : Blo 2031435 2033311 := bstep (se 1 (by rfl) ⟨1524983, by rfl⟩ : syracuseStep 2033311 = 3049967) B3049967
theorem B3049973 : Blo 2031435 3049973 := bbase (se 5 (by rfl) ⟨142967, by rfl⟩ : syracuseStep 3049973 = 285935) (by norm_num)
theorem B2033315 : Blo 2031435 2033315 := bstep (se 1 (by rfl) ⟨1524986, by rfl⟩ : syracuseStep 2033315 = 3049973) B3049973
theorem B5790197 : Blo 2031435 5790197 := bbase (se 5 (by rfl) ⟨271415, by rfl⟩ : syracuseStep 5790197 = 542831) (by norm_num)
theorem B3860131 : Blo 2031435 3860131 := bstep (se 1 (by rfl) ⟨2895098, by rfl⟩ : syracuseStep 3860131 = 5790197) B5790197
theorem B5146841 : Blo 2031435 5146841 := bstep (se 2 (by rfl) ⟨1930065, by rfl⟩ : syracuseStep 5146841 = 3860131) B3860131
theorem B3431227 : Blo 2031435 3431227 := bstep (se 1 (by rfl) ⟨2573420, by rfl⟩ : syracuseStep 3431227 = 5146841) B5146841
theorem B4574969 : Blo 2031435 4574969 := bstep (se 2 (by rfl) ⟨1715613, by rfl⟩ : syracuseStep 4574969 = 3431227) B3431227
theorem B3049979 : Blo 2031435 3049979 := bstep (se 1 (by rfl) ⟨2287484, by rfl⟩ : syracuseStep 3049979 = 4574969) B4574969
theorem B2033319 : Blo 2031435 2033319 := bstep (se 1 (by rfl) ⟨1524989, by rfl⟩ : syracuseStep 2033319 = 3049979) B3049979
theorem B2287489 : Blo 2031435 2287489 := bbase (se 2 (by rfl) ⟨857808, by rfl⟩ : syracuseStep 2287489 = 1715617) (by norm_num)
theorem B3049985 : Blo 2031435 3049985 := bstep (se 2 (by rfl) ⟨1143744, by rfl⟩ : syracuseStep 3049985 = 2287489) B2287489
theorem B2033323 : Blo 2031435 2033323 := bstep (se 1 (by rfl) ⟨1524992, by rfl⟩ : syracuseStep 2033323 = 3049985) B3049985
theorem B5146861 : Blo 2031435 5146861 := bbase (se 3 (by rfl) ⟨965036, by rfl⟩ : syracuseStep 5146861 = 1930073) (by norm_num)
theorem B6862481 : Blo 2031435 6862481 := bstep (se 2 (by rfl) ⟨2573430, by rfl⟩ : syracuseStep 6862481 = 5146861) B5146861
theorem B4574987 : Blo 2031435 4574987 := bstep (se 1 (by rfl) ⟨3431240, by rfl⟩ : syracuseStep 4574987 = 6862481) B6862481
theorem B3049991 : Blo 2031435 3049991 := bstep (se 1 (by rfl) ⟨2287493, by rfl⟩ : syracuseStep 3049991 = 4574987) B4574987
theorem B2033327 : Blo 2031435 2033327 := bstep (se 1 (by rfl) ⟨1524995, by rfl⟩ : syracuseStep 2033327 = 3049991) B3049991
theorem B3049997 : Blo 2031435 3049997 := bbase (se 3 (by rfl) ⟨571874, by rfl⟩ : syracuseStep 3049997 = 1143749) (by norm_num)
theorem B2033331 : Blo 2031435 2033331 := bstep (se 1 (by rfl) ⟨1524998, by rfl⟩ : syracuseStep 2033331 = 3049997) B3049997
theorem B4575005 : Blo 2031435 4575005 := bbase (se 3 (by rfl) ⟨857813, by rfl⟩ : syracuseStep 4575005 = 1715627) (by norm_num)
theorem B3050003 : Blo 2031435 3050003 := bstep (se 1 (by rfl) ⟨2287502, by rfl⟩ : syracuseStep 3050003 = 4575005) B4575005
theorem B2033335 : Blo 2031435 2033335 := bstep (se 1 (by rfl) ⟨1525001, by rfl⟩ : syracuseStep 2033335 = 3050003) B3050003
theorem B3431261 : Blo 2031435 3431261 := bbase (se 3 (by rfl) ⟨643361, by rfl⟩ : syracuseStep 3431261 = 1286723) (by norm_num)
theorem B2287507 : Blo 2031435 2287507 := bstep (se 1 (by rfl) ⟨1715630, by rfl⟩ : syracuseStep 2287507 = 3431261) B3431261
theorem B3050009 : Blo 2031435 3050009 := bstep (se 2 (by rfl) ⟨1143753, by rfl⟩ : syracuseStep 3050009 = 2287507) B2287507
theorem B2033339 : Blo 2031435 2033339 := bstep (se 1 (by rfl) ⟨1525004, by rfl⟩ : syracuseStep 2033339 = 3050009) B3050009
theorem B8685397 : Blo 2031435 8685397 := bbase (se 9 (by rfl) ⟨25445, by rfl⟩ : syracuseStep 8685397 = 50891) (by norm_num)
theorem B11580529 : Blo 2031435 11580529 := bstep (se 2 (by rfl) ⟨4342698, by rfl⟩ : syracuseStep 11580529 = 8685397) B8685397
theorem B15440705 : Blo 2031435 15440705 := bstep (se 2 (by rfl) ⟨5790264, by rfl⟩ : syracuseStep 15440705 = 11580529) B11580529
theorem B10293803 : Blo 2031435 10293803 := bstep (se 1 (by rfl) ⟨7720352, by rfl⟩ : syracuseStep 10293803 = 15440705) B15440705
theorem B6862535 : Blo 2031435 6862535 := bstep (se 1 (by rfl) ⟨5146901, by rfl⟩ : syracuseStep 6862535 = 10293803) B10293803
theorem B4575023 : Blo 2031435 4575023 := bstep (se 1 (by rfl) ⟨3431267, by rfl⟩ : syracuseStep 4575023 = 6862535) B6862535
theorem B3050015 : Blo 2031435 3050015 := bstep (se 1 (by rfl) ⟨2287511, by rfl⟩ : syracuseStep 3050015 = 4575023) B4575023
theorem B2033343 : Blo 2031435 2033343 := bstep (se 1 (by rfl) ⟨1525007, by rfl⟩ : syracuseStep 2033343 = 3050015) B3050015
theorem B3050021 : Blo 2031435 3050021 := bbase (se 4 (by rfl) ⟨285939, by rfl⟩ : syracuseStep 3050021 = 571879) (by norm_num)
theorem B2033347 : Blo 2031435 2033347 := bstep (se 1 (by rfl) ⟨1525010, by rfl⟩ : syracuseStep 2033347 = 3050021) B3050021
theorem B2573461 : Blo 2031435 2573461 := bbase (se 6 (by rfl) ⟨60315, by rfl⟩ : syracuseStep 2573461 = 120631) (by norm_num)
theorem B3431281 : Blo 2031435 3431281 := bstep (se 2 (by rfl) ⟨1286730, by rfl⟩ : syracuseStep 3431281 = 2573461) B2573461
theorem B4575041 : Blo 2031435 4575041 := bstep (se 2 (by rfl) ⟨1715640, by rfl⟩ : syracuseStep 4575041 = 3431281) B3431281
theorem B3050027 : Blo 2031435 3050027 := bstep (se 1 (by rfl) ⟨2287520, by rfl⟩ : syracuseStep 3050027 = 4575041) B4575041
theorem B2033351 : Blo 2031435 2033351 := bstep (se 1 (by rfl) ⟨1525013, by rfl⟩ : syracuseStep 2033351 = 3050027) B3050027
theorem B2287525 : Blo 2031435 2287525 := bbase (se 4 (by rfl) ⟨214455, by rfl⟩ : syracuseStep 2287525 = 428911) (by norm_num)
theorem B3050033 : Blo 2031435 3050033 := bstep (se 2 (by rfl) ⟨1143762, by rfl⟩ : syracuseStep 3050033 = 2287525) B2287525
theorem B2033355 : Blo 2031435 2033355 := bstep (se 1 (by rfl) ⟨1525016, by rfl⟩ : syracuseStep 2033355 = 3050033) B3050033
theorem B2476117 : Blo 2031435 2476117 := bbase (se 8 (by rfl) ⟨14508, by rfl⟩ : syracuseStep 2476117 = 29017) (by norm_num)
theorem B3301489 : Blo 2031435 3301489 := bstep (se 2 (by rfl) ⟨1238058, by rfl⟩ : syracuseStep 3301489 = 2476117) B2476117
theorem B4401985 : Blo 2031435 4401985 := bstep (se 2 (by rfl) ⟨1650744, by rfl⟩ : syracuseStep 4401985 = 3301489) B3301489
theorem B5869313 : Blo 2031435 5869313 := bstep (se 2 (by rfl) ⟨2200992, by rfl⟩ : syracuseStep 5869313 = 4401985) B4401985
theorem B3912875 : Blo 2031435 3912875 := bstep (se 1 (by rfl) ⟨2934656, by rfl⟩ : syracuseStep 3912875 = 5869313) B5869313
theorem B2608583 : Blo 2031435 2608583 := bstep (se 1 (by rfl) ⟨1956437, by rfl⟩ : syracuseStep 2608583 = 3912875) B3912875
theorem B6956221 : Blo 2031435 6956221 := bstep (se 3 (by rfl) ⟨1304291, by rfl⟩ : syracuseStep 6956221 = 2608583) B2608583
theorem B9274961 : Blo 2031435 9274961 := bstep (se 2 (by rfl) ⟨3478110, by rfl⟩ : syracuseStep 9274961 = 6956221) B6956221
theorem B6183307 : Blo 2031435 6183307 := bstep (se 1 (by rfl) ⟨4637480, by rfl⟩ : syracuseStep 6183307 = 9274961) B9274961
theorem B32977637 : Blo 2031435 32977637 := bstep (se 4 (by rfl) ⟨3091653, by rfl⟩ : syracuseStep 32977637 = 6183307) B6183307
theorem B21985091 : Blo 2031435 21985091 := bstep (se 1 (by rfl) ⟨16488818, by rfl⟩ : syracuseStep 21985091 = 32977637) B32977637
theorem B14656727 : Blo 2031435 14656727 := bstep (se 1 (by rfl) ⟨10992545, by rfl⟩ : syracuseStep 14656727 = 21985091) B21985091
theorem B9771151 : Blo 2031435 9771151 := bstep (se 1 (by rfl) ⟨7328363, by rfl⟩ : syracuseStep 9771151 = 14656727) B14656727
theorem B13028201 : Blo 2031435 13028201 := bstep (se 2 (by rfl) ⟨4885575, by rfl⟩ : syracuseStep 13028201 = 9771151) B9771151
theorem B8685467 : Blo 2031435 8685467 := bstep (se 1 (by rfl) ⟨6514100, by rfl⟩ : syracuseStep 8685467 = 13028201) B13028201
theorem B5790311 : Blo 2031435 5790311 := bstep (se 1 (by rfl) ⟨4342733, by rfl⟩ : syracuseStep 5790311 = 8685467) B8685467
theorem B3860207 : Blo 2031435 3860207 := bstep (se 1 (by rfl) ⟨2895155, by rfl⟩ : syracuseStep 3860207 = 5790311) B5790311
theorem B2573471 : Blo 2031435 2573471 := bstep (se 1 (by rfl) ⟨1930103, by rfl⟩ : syracuseStep 2573471 = 3860207) B3860207
theorem B6862589 : Blo 2031435 6862589 := bstep (se 3 (by rfl) ⟨1286735, by rfl⟩ : syracuseStep 6862589 = 2573471) B2573471
theorem B4575059 : Blo 2031435 4575059 := bstep (se 1 (by rfl) ⟨3431294, by rfl⟩ : syracuseStep 4575059 = 6862589) B6862589
theorem B3050039 : Blo 2031435 3050039 := bstep (se 1 (by rfl) ⟨2287529, by rfl⟩ : syracuseStep 3050039 = 4575059) B4575059
theorem B2033359 : Blo 2031435 2033359 := bstep (se 1 (by rfl) ⟨1525019, by rfl⟩ : syracuseStep 2033359 = 3050039) B3050039
theorem B3050045 : Blo 2031435 3050045 := bbase (se 3 (by rfl) ⟨571883, by rfl⟩ : syracuseStep 3050045 = 1143767) (by norm_num)
theorem B2033363 : Blo 2031435 2033363 := bstep (se 1 (by rfl) ⟨1525022, by rfl⟩ : syracuseStep 2033363 = 3050045) B3050045
theorem B4575077 : Blo 2031435 4575077 := bbase (se 4 (by rfl) ⟨428913, by rfl⟩ : syracuseStep 4575077 = 857827) (by norm_num)
theorem B3050051 : Blo 2031435 3050051 := bstep (se 1 (by rfl) ⟨2287538, by rfl⟩ : syracuseStep 3050051 = 4575077) B4575077
theorem B2033367 : Blo 2031435 2033367 := bstep (se 1 (by rfl) ⟨1525025, by rfl⟩ : syracuseStep 2033367 = 3050051) B3050051
theorem B5146973 : Blo 2031435 5146973 := bbase (se 3 (by rfl) ⟨965057, by rfl⟩ : syracuseStep 5146973 = 1930115) (by norm_num)
theorem B3431315 : Blo 2031435 3431315 := bstep (se 1 (by rfl) ⟨2573486, by rfl⟩ : syracuseStep 3431315 = 5146973) B5146973
theorem B2287543 : Blo 2031435 2287543 := bstep (se 1 (by rfl) ⟨1715657, by rfl⟩ : syracuseStep 2287543 = 3431315) B3431315
theorem B3050057 : Blo 2031435 3050057 := bstep (se 2 (by rfl) ⟨1143771, by rfl⟩ : syracuseStep 3050057 = 2287543) B2287543
theorem B2033371 : Blo 2031435 2033371 := bstep (se 1 (by rfl) ⟨1525028, by rfl⟩ : syracuseStep 2033371 = 3050057) B3050057
theorem B3860237 : Blo 2031435 3860237 := bbase (se 3 (by rfl) ⟨723794, by rfl⟩ : syracuseStep 3860237 = 1447589) (by norm_num)
theorem B10293965 : Blo 2031435 10293965 := bstep (se 3 (by rfl) ⟨1930118, by rfl⟩ : syracuseStep 10293965 = 3860237) B3860237
theorem B6862643 : Blo 2031435 6862643 := bstep (se 1 (by rfl) ⟨5146982, by rfl⟩ : syracuseStep 6862643 = 10293965) B10293965
theorem B4575095 : Blo 2031435 4575095 := bstep (se 1 (by rfl) ⟨3431321, by rfl⟩ : syracuseStep 4575095 = 6862643) B6862643
theorem B3050063 : Blo 2031435 3050063 := bstep (se 1 (by rfl) ⟨2287547, by rfl⟩ : syracuseStep 3050063 = 4575095) B4575095
theorem B2033375 : Blo 2031435 2033375 := bstep (se 1 (by rfl) ⟨1525031, by rfl⟩ : syracuseStep 2033375 = 3050063) B3050063
theorem B3050069 : Blo 2031435 3050069 := bbase (se 8 (by rfl) ⟨17871, by rfl⟩ : syracuseStep 3050069 = 35743) (by norm_num)
theorem B2033379 : Blo 2031435 2033379 := bstep (se 1 (by rfl) ⟨1525034, by rfl⟩ : syracuseStep 2033379 = 3050069) B3050069
theorem B3714221 : Blo 2031435 3714221 := bbase (se 3 (by rfl) ⟨696416, by rfl⟩ : syracuseStep 3714221 = 1392833) (by norm_num)
theorem B9904589 : Blo 2031435 9904589 := bstep (se 3 (by rfl) ⟨1857110, by rfl⟩ : syracuseStep 9904589 = 3714221) B3714221
theorem B6603059 : Blo 2031435 6603059 := bstep (se 1 (by rfl) ⟨4952294, by rfl⟩ : syracuseStep 6603059 = 9904589) B9904589
theorem B4402039 : Blo 2031435 4402039 := bstep (se 1 (by rfl) ⟨3301529, by rfl⟩ : syracuseStep 4402039 = 6603059) B6603059
theorem B5869385 : Blo 2031435 5869385 := bstep (se 2 (by rfl) ⟨2201019, by rfl⟩ : syracuseStep 5869385 = 4402039) B4402039
theorem B3912923 : Blo 2031435 3912923 := bstep (se 1 (by rfl) ⟨2934692, by rfl⟩ : syracuseStep 3912923 = 5869385) B5869385
theorem B2608615 : Blo 2031435 2608615 := bstep (se 1 (by rfl) ⟨1956461, by rfl⟩ : syracuseStep 2608615 = 3912923) B3912923
theorem B3478153 : Blo 2031435 3478153 := bstep (se 2 (by rfl) ⟨1304307, by rfl⟩ : syracuseStep 3478153 = 2608615) B2608615
theorem B4637537 : Blo 2031435 4637537 := bstep (se 2 (by rfl) ⟨1739076, by rfl⟩ : syracuseStep 4637537 = 3478153) B3478153
theorem B3091691 : Blo 2031435 3091691 := bstep (se 1 (by rfl) ⟨2318768, by rfl⟩ : syracuseStep 3091691 = 4637537) B4637537
theorem B2061127 : Blo 2031435 2061127 := bstep (se 1 (by rfl) ⟨1545845, by rfl⟩ : syracuseStep 2061127 = 3091691) B3091691
theorem B2748169 : Blo 2031435 2748169 := bstep (se 2 (by rfl) ⟨1030563, by rfl⟩ : syracuseStep 2748169 = 2061127) B2061127
theorem B3664225 : Blo 2031435 3664225 := bstep (se 2 (by rfl) ⟨1374084, by rfl⟩ : syracuseStep 3664225 = 2748169) B2748169
theorem B4885633 : Blo 2031435 4885633 := bstep (se 2 (by rfl) ⟨1832112, by rfl⟩ : syracuseStep 4885633 = 3664225) B3664225
theorem B6514177 : Blo 2031435 6514177 := bstep (se 2 (by rfl) ⟨2442816, by rfl⟩ : syracuseStep 6514177 = 4885633) B4885633
theorem B8685569 : Blo 2031435 8685569 := bstep (se 2 (by rfl) ⟨3257088, by rfl⟩ : syracuseStep 8685569 = 6514177) B6514177
theorem B5790379 : Blo 2031435 5790379 := bstep (se 1 (by rfl) ⟨4342784, by rfl⟩ : syracuseStep 5790379 = 8685569) B8685569
theorem B7720505 : Blo 2031435 7720505 := bstep (se 2 (by rfl) ⟨2895189, by rfl⟩ : syracuseStep 7720505 = 5790379) B5790379
theorem B5147003 : Blo 2031435 5147003 := bstep (se 1 (by rfl) ⟨3860252, by rfl⟩ : syracuseStep 5147003 = 7720505) B7720505
theorem B3431335 : Blo 2031435 3431335 := bstep (se 1 (by rfl) ⟨2573501, by rfl⟩ : syracuseStep 3431335 = 5147003) B5147003
theorem B4575113 : Blo 2031435 4575113 := bstep (se 2 (by rfl) ⟨1715667, by rfl⟩ : syracuseStep 4575113 = 3431335) B3431335
theorem B3050075 : Blo 2031435 3050075 := bstep (se 1 (by rfl) ⟨2287556, by rfl⟩ : syracuseStep 3050075 = 4575113) B4575113
theorem B2033383 : Blo 2031435 2033383 := bstep (se 1 (by rfl) ⟨1525037, by rfl⟩ : syracuseStep 2033383 = 3050075) B3050075
theorem B2287561 : Blo 2031435 2287561 := bbase (se 2 (by rfl) ⟨857835, by rfl⟩ : syracuseStep 2287561 = 1715671) (by norm_num)
theorem B3050081 : Blo 2031435 3050081 := bstep (se 2 (by rfl) ⟨1143780, by rfl⟩ : syracuseStep 3050081 = 2287561) B2287561
theorem B2033387 : Blo 2031435 2033387 := bstep (se 1 (by rfl) ⟨1525040, by rfl⟩ : syracuseStep 2033387 = 3050081) B3050081
theorem B3257101 : Blo 2031435 3257101 := bbase (se 3 (by rfl) ⟨610706, by rfl⟩ : syracuseStep 3257101 = 1221413) (by norm_num)
theorem B17371205 : Blo 2031435 17371205 := bstep (se 4 (by rfl) ⟨1628550, by rfl⟩ : syracuseStep 17371205 = 3257101) B3257101
theorem B11580803 : Blo 2031435 11580803 := bstep (se 1 (by rfl) ⟨8685602, by rfl⟩ : syracuseStep 11580803 = 17371205) B17371205
theorem B7720535 : Blo 2031435 7720535 := bstep (se 1 (by rfl) ⟨5790401, by rfl⟩ : syracuseStep 7720535 = 11580803) B11580803
theorem B5147023 : Blo 2031435 5147023 := bstep (se 1 (by rfl) ⟨3860267, by rfl⟩ : syracuseStep 5147023 = 7720535) B7720535
theorem B6862697 : Blo 2031435 6862697 := bstep (se 2 (by rfl) ⟨2573511, by rfl⟩ : syracuseStep 6862697 = 5147023) B5147023
theorem B4575131 : Blo 2031435 4575131 := bstep (se 1 (by rfl) ⟨3431348, by rfl⟩ : syracuseStep 4575131 = 6862697) B6862697
theorem B3050087 : Blo 2031435 3050087 := bstep (se 1 (by rfl) ⟨2287565, by rfl⟩ : syracuseStep 3050087 = 4575131) B4575131
theorem B2033391 : Blo 2031435 2033391 := bstep (se 1 (by rfl) ⟨1525043, by rfl⟩ : syracuseStep 2033391 = 3050087) B3050087
theorem B3050093 : Blo 2031435 3050093 := bbase (se 3 (by rfl) ⟨571892, by rfl⟩ : syracuseStep 3050093 = 1143785) (by norm_num)
theorem B2033395 : Blo 2031435 2033395 := bstep (se 1 (by rfl) ⟨1525046, by rfl⟩ : syracuseStep 2033395 = 3050093) B3050093
theorem B4575149 : Blo 2031435 4575149 := bbase (se 3 (by rfl) ⟨857840, by rfl⟩ : syracuseStep 4575149 = 1715681) (by norm_num)
theorem B3050099 : Blo 2031435 3050099 := bstep (se 1 (by rfl) ⟨2287574, by rfl⟩ : syracuseStep 3050099 = 4575149) B4575149
theorem B2033399 : Blo 2031435 2033399 := bstep (se 1 (by rfl) ⟨1525049, by rfl⟩ : syracuseStep 2033399 = 3050099) B3050099
theorem B5790437 : Blo 2031435 5790437 := bbase (se 4 (by rfl) ⟨542853, by rfl⟩ : syracuseStep 5790437 = 1085707) (by norm_num)
theorem B3860291 : Blo 2031435 3860291 := bstep (se 1 (by rfl) ⟨2895218, by rfl⟩ : syracuseStep 3860291 = 5790437) B5790437
theorem B2573527 : Blo 2031435 2573527 := bstep (se 1 (by rfl) ⟨1930145, by rfl⟩ : syracuseStep 2573527 = 3860291) B3860291
theorem B3431369 : Blo 2031435 3431369 := bstep (se 2 (by rfl) ⟨1286763, by rfl⟩ : syracuseStep 3431369 = 2573527) B2573527
theorem B2287579 : Blo 2031435 2287579 := bstep (se 1 (by rfl) ⟨1715684, by rfl⟩ : syracuseStep 2287579 = 3431369) B3431369
theorem B3050105 : Blo 2031435 3050105 := bstep (se 2 (by rfl) ⟨1143789, by rfl⟩ : syracuseStep 3050105 = 2287579) B2287579
theorem B2033403 : Blo 2031435 2033403 := bstep (se 1 (by rfl) ⟨1525052, by rfl⟩ : syracuseStep 2033403 = 3050105) B3050105
theorem B4122301 : Blo 2031435 4122301 := bbase (se 3 (by rfl) ⟨772931, by rfl⟩ : syracuseStep 4122301 = 1545863) (by norm_num)
theorem B5496401 : Blo 2031435 5496401 := bstep (se 2 (by rfl) ⟨2061150, by rfl⟩ : syracuseStep 5496401 = 4122301) B4122301
theorem B14657069 : Blo 2031435 14657069 := bstep (se 3 (by rfl) ⟨2748200, by rfl⟩ : syracuseStep 14657069 = 5496401) B5496401
theorem B39085517 : Blo 2031435 39085517 := bstep (se 3 (by rfl) ⟨7328534, by rfl⟩ : syracuseStep 39085517 = 14657069) B14657069
theorem B26057011 : Blo 2031435 26057011 := bstep (se 1 (by rfl) ⟨19542758, by rfl⟩ : syracuseStep 26057011 = 39085517) B39085517
theorem B34742681 : Blo 2031435 34742681 := bstep (se 2 (by rfl) ⟨13028505, by rfl⟩ : syracuseStep 34742681 = 26057011) B26057011
theorem B23161787 : Blo 2031435 23161787 := bstep (se 1 (by rfl) ⟨17371340, by rfl⟩ : syracuseStep 23161787 = 34742681) B34742681
theorem B15441191 : Blo 2031435 15441191 := bstep (se 1 (by rfl) ⟨11580893, by rfl⟩ : syracuseStep 15441191 = 23161787) B23161787
theorem B10294127 : Blo 2031435 10294127 := bstep (se 1 (by rfl) ⟨7720595, by rfl⟩ : syracuseStep 10294127 = 15441191) B15441191
theorem B6862751 : Blo 2031435 6862751 := bstep (se 1 (by rfl) ⟨5147063, by rfl⟩ : syracuseStep 6862751 = 10294127) B10294127
theorem B4575167 : Blo 2031435 4575167 := bstep (se 1 (by rfl) ⟨3431375, by rfl⟩ : syracuseStep 4575167 = 6862751) B6862751
theorem B3050111 : Blo 2031435 3050111 := bstep (se 1 (by rfl) ⟨2287583, by rfl⟩ : syracuseStep 3050111 = 4575167) B4575167
theorem B2033407 : Blo 2031435 2033407 := bstep (se 1 (by rfl) ⟨1525055, by rfl⟩ : syracuseStep 2033407 = 3050111) B3050111
theorem B3050117 : Blo 2031435 3050117 := bbase (se 4 (by rfl) ⟨285948, by rfl⟩ : syracuseStep 3050117 = 571897) (by norm_num)
theorem B2033411 : Blo 2031435 2033411 := bstep (se 1 (by rfl) ⟨1525058, by rfl⟩ : syracuseStep 2033411 = 3050117) B3050117
theorem B3431389 : Blo 2031435 3431389 := bbase (se 3 (by rfl) ⟨643385, by rfl⟩ : syracuseStep 3431389 = 1286771) (by norm_num)
theorem B4575185 : Blo 2031435 4575185 := bstep (se 2 (by rfl) ⟨1715694, by rfl⟩ : syracuseStep 4575185 = 3431389) B3431389
theorem B3050123 : Blo 2031435 3050123 := bstep (se 1 (by rfl) ⟨2287592, by rfl⟩ : syracuseStep 3050123 = 4575185) B4575185
theorem B2033415 : Blo 2031435 2033415 := bstep (se 1 (by rfl) ⟨1525061, by rfl⟩ : syracuseStep 2033415 = 3050123) B3050123
theorem B2287597 : Blo 2031435 2287597 := bbase (se 3 (by rfl) ⟨428924, by rfl⟩ : syracuseStep 2287597 = 857849) (by norm_num)
theorem B3050129 : Blo 2031435 3050129 := bstep (se 2 (by rfl) ⟨1143798, by rfl⟩ : syracuseStep 3050129 = 2287597) B2287597
theorem B2033419 : Blo 2031435 2033419 := bstep (se 1 (by rfl) ⟨1525064, by rfl⟩ : syracuseStep 2033419 = 3050129) B3050129
theorem B6862805 : Blo 2031435 6862805 := bbase (se 7 (by rfl) ⟨80423, by rfl⟩ : syracuseStep 6862805 = 160847) (by norm_num)
theorem B4575203 : Blo 2031435 4575203 := bstep (se 1 (by rfl) ⟨3431402, by rfl⟩ : syracuseStep 4575203 = 6862805) B6862805
theorem B3050135 : Blo 2031435 3050135 := bstep (se 1 (by rfl) ⟨2287601, by rfl⟩ : syracuseStep 3050135 = 4575203) B4575203
theorem B2033423 : Blo 2031435 2033423 := bstep (se 1 (by rfl) ⟨1525067, by rfl⟩ : syracuseStep 2033423 = 3050135) B3050135
theorem B3050141 : Blo 2031435 3050141 := bbase (se 3 (by rfl) ⟨571901, by rfl⟩ : syracuseStep 3050141 = 1143803) (by norm_num)
theorem B2033427 : Blo 2031435 2033427 := bstep (se 1 (by rfl) ⟨1525070, by rfl⟩ : syracuseStep 2033427 = 3050141) B3050141
theorem B4575221 : Blo 2031435 4575221 := bbase (se 5 (by rfl) ⟨214463, by rfl⟩ : syracuseStep 4575221 = 428927) (by norm_num)
theorem B3050147 : Blo 2031435 3050147 := bstep (se 1 (by rfl) ⟨2287610, by rfl⟩ : syracuseStep 3050147 = 4575221) B4575221
theorem B2033431 : Blo 2031435 2033431 := bstep (se 1 (by rfl) ⟨1525073, by rfl⟩ : syracuseStep 2033431 = 3050147) B3050147
theorem B9660149 : Blo 2031435 9660149 := bbase (se 5 (by rfl) ⟨452819, by rfl⟩ : syracuseStep 9660149 = 905639) (by norm_num)
theorem B6440099 : Blo 2031435 6440099 := bstep (se 1 (by rfl) ⟨4830074, by rfl⟩ : syracuseStep 6440099 = 9660149) B9660149
theorem B68694389 : Blo 2031435 68694389 := bstep (se 5 (by rfl) ⟨3220049, by rfl⟩ : syracuseStep 68694389 = 6440099) B6440099
theorem B45796259 : Blo 2031435 45796259 := bstep (se 1 (by rfl) ⟨34347194, by rfl⟩ : syracuseStep 45796259 = 68694389) B68694389
theorem B30530839 : Blo 2031435 30530839 := bstep (se 1 (by rfl) ⟨22898129, by rfl⟩ : syracuseStep 30530839 = 45796259) B45796259
theorem B40707785 : Blo 2031435 40707785 := bstep (se 2 (by rfl) ⟨15265419, by rfl⟩ : syracuseStep 40707785 = 30530839) B30530839
theorem B108554093 : Blo 2031435 108554093 := bstep (se 3 (by rfl) ⟨20353892, by rfl⟩ : syracuseStep 108554093 = 40707785) B40707785
theorem B72369395 : Blo 2031435 72369395 := bstep (se 1 (by rfl) ⟨54277046, by rfl⟩ : syracuseStep 72369395 = 108554093) B108554093
theorem B48246263 : Blo 2031435 48246263 := bstep (se 1 (by rfl) ⟨36184697, by rfl⟩ : syracuseStep 48246263 = 72369395) B72369395
theorem B32164175 : Blo 2031435 32164175 := bstep (se 1 (by rfl) ⟨24123131, by rfl⟩ : syracuseStep 32164175 = 48246263) B48246263
theorem B85771133 : Blo 2031435 85771133 := bstep (se 3 (by rfl) ⟨16082087, by rfl⟩ : syracuseStep 85771133 = 32164175) B32164175
theorem B57180755 : Blo 2031435 57180755 := bstep (se 1 (by rfl) ⟨42885566, by rfl⟩ : syracuseStep 57180755 = 85771133) B85771133
theorem B38120503 : Blo 2031435 38120503 := bstep (se 1 (by rfl) ⟨28590377, by rfl⟩ : syracuseStep 38120503 = 57180755) B57180755
theorem B50827337 : Blo 2031435 50827337 := bstep (se 2 (by rfl) ⟨19060251, by rfl⟩ : syracuseStep 50827337 = 38120503) B38120503
theorem B33884891 : Blo 2031435 33884891 := bstep (se 1 (by rfl) ⟨25413668, by rfl⟩ : syracuseStep 33884891 = 50827337) B50827337
theorem B22589927 : Blo 2031435 22589927 := bstep (se 1 (by rfl) ⟨16942445, by rfl⟩ : syracuseStep 22589927 = 33884891) B33884891
theorem B15059951 : Blo 2031435 15059951 := bstep (se 1 (by rfl) ⟨11294963, by rfl⟩ : syracuseStep 15059951 = 22589927) B22589927
theorem B10039967 : Blo 2031435 10039967 := bstep (se 1 (by rfl) ⟨7529975, by rfl⟩ : syracuseStep 10039967 = 15059951) B15059951
theorem B6693311 : Blo 2031435 6693311 := bstep (se 1 (by rfl) ⟨5019983, by rfl⟩ : syracuseStep 6693311 = 10039967) B10039967
theorem B17848829 : Blo 2031435 17848829 := bstep (se 3 (by rfl) ⟨3346655, by rfl⟩ : syracuseStep 17848829 = 6693311) B6693311
theorem B47596877 : Blo 2031435 47596877 := bstep (se 3 (by rfl) ⟨8924414, by rfl⟩ : syracuseStep 47596877 = 17848829) B17848829
theorem B507700021 : Blo 2031435 507700021 := bstep (se 5 (by rfl) ⟨23798438, by rfl⟩ : syracuseStep 507700021 = 47596877) B47596877
theorem B676933361 : Blo 2031435 676933361 := bstep (se 2 (by rfl) ⟨253850010, by rfl⟩ : syracuseStep 676933361 = 507700021) B507700021
theorem B451288907 : Blo 2031435 451288907 := bstep (se 1 (by rfl) ⟨338466680, by rfl⟩ : syracuseStep 451288907 = 676933361) B676933361
theorem B300859271 : Blo 2031435 300859271 := bstep (se 1 (by rfl) ⟨225644453, by rfl⟩ : syracuseStep 300859271 = 451288907) B451288907
theorem B200572847 : Blo 2031435 200572847 := bstep (se 1 (by rfl) ⟨150429635, by rfl⟩ : syracuseStep 200572847 = 300859271) B300859271
theorem B133715231 : Blo 2031435 133715231 := bstep (se 1 (by rfl) ⟨100286423, by rfl⟩ : syracuseStep 133715231 = 200572847) B200572847
theorem B89143487 : Blo 2031435 89143487 := bstep (se 1 (by rfl) ⟨66857615, by rfl⟩ : syracuseStep 89143487 = 133715231) B133715231
theorem B59428991 : Blo 2031435 59428991 := bstep (se 1 (by rfl) ⟨44571743, by rfl⟩ : syracuseStep 59428991 = 89143487) B89143487
theorem B158477309 : Blo 2031435 158477309 := bstep (se 3 (by rfl) ⟨29714495, by rfl⟩ : syracuseStep 158477309 = 59428991) B59428991
theorem B105651539 : Blo 2031435 105651539 := bstep (se 1 (by rfl) ⟨79238654, by rfl⟩ : syracuseStep 105651539 = 158477309) B158477309
theorem B70434359 : Blo 2031435 70434359 := bstep (se 1 (by rfl) ⟨52825769, by rfl⟩ : syracuseStep 70434359 = 105651539) B105651539
theorem B46956239 : Blo 2031435 46956239 := bstep (se 1 (by rfl) ⟨35217179, by rfl⟩ : syracuseStep 46956239 = 70434359) B70434359
theorem B31304159 : Blo 2031435 31304159 := bstep (se 1 (by rfl) ⟨23478119, by rfl⟩ : syracuseStep 31304159 = 46956239) B46956239
theorem B20869439 : Blo 2031435 20869439 := bstep (se 1 (by rfl) ⟨15652079, by rfl⟩ : syracuseStep 20869439 = 31304159) B31304159
theorem B222607349 : Blo 2031435 222607349 := bstep (se 5 (by rfl) ⟨10434719, by rfl⟩ : syracuseStep 222607349 = 20869439) B20869439
theorem B148404899 : Blo 2031435 148404899 := bstep (se 1 (by rfl) ⟨111303674, by rfl⟩ : syracuseStep 148404899 = 222607349) B222607349
theorem B98936599 : Blo 2031435 98936599 := bstep (se 1 (by rfl) ⟨74202449, by rfl⟩ : syracuseStep 98936599 = 148404899) B148404899
theorem B131915465 : Blo 2031435 131915465 := bstep (se 2 (by rfl) ⟨49468299, by rfl⟩ : syracuseStep 131915465 = 98936599) B98936599
theorem B87943643 : Blo 2031435 87943643 := bstep (se 1 (by rfl) ⟨65957732, by rfl⟩ : syracuseStep 87943643 = 131915465) B131915465
theorem B58629095 : Blo 2031435 58629095 := bstep (se 1 (by rfl) ⟨43971821, by rfl⟩ : syracuseStep 58629095 = 87943643) B87943643
theorem B39086063 : Blo 2031435 39086063 := bstep (se 1 (by rfl) ⟨29314547, by rfl⟩ : syracuseStep 39086063 = 58629095) B58629095
theorem B26057375 : Blo 2031435 26057375 := bstep (se 1 (by rfl) ⟨19543031, by rfl⟩ : syracuseStep 26057375 = 39086063) B39086063
theorem B17371583 : Blo 2031435 17371583 := bstep (se 1 (by rfl) ⟨13028687, by rfl⟩ : syracuseStep 17371583 = 26057375) B26057375
theorem B11581055 : Blo 2031435 11581055 := bstep (se 1 (by rfl) ⟨8685791, by rfl⟩ : syracuseStep 11581055 = 17371583) B17371583
theorem B7720703 : Blo 2031435 7720703 := bstep (se 1 (by rfl) ⟨5790527, by rfl⟩ : syracuseStep 7720703 = 11581055) B11581055
theorem B5147135 : Blo 2031435 5147135 := bstep (se 1 (by rfl) ⟨3860351, by rfl⟩ : syracuseStep 5147135 = 7720703) B7720703
theorem B3431423 : Blo 2031435 3431423 := bstep (se 1 (by rfl) ⟨2573567, by rfl⟩ : syracuseStep 3431423 = 5147135) B5147135
theorem B2287615 : Blo 2031435 2287615 := bstep (se 1 (by rfl) ⟨1715711, by rfl⟩ : syracuseStep 2287615 = 3431423) B3431423
theorem B3050153 : Blo 2031435 3050153 := bstep (se 2 (by rfl) ⟨1143807, by rfl⟩ : syracuseStep 3050153 = 2287615) B2287615
theorem B2033435 : Blo 2031435 2033435 := bstep (se 1 (by rfl) ⟨1525076, by rfl⟩ : syracuseStep 2033435 = 3050153) B3050153
theorem C0 (j : ℕ) (h1 : 507858 ≤ j) (h2 : j ≤ 508358) : Blo 2031435 (4 * j + 3) := by
  interval_cases j
  · exact B2031435
  · exact B2031439
  · exact B2031443
  · exact B2031447
  · exact B2031451
  · exact B2031455
  · exact B2031459
  · exact B2031463
  · exact B2031467
  · exact B2031471
  · exact B2031475
  · exact B2031479
  · exact B2031483
  · exact B2031487
  · exact B2031491
  · exact B2031495
  · exact B2031499
  · exact B2031503
  · exact B2031507
  · exact B2031511
  · exact B2031515
  · exact B2031519
  · exact B2031523
  · exact B2031527
  · exact B2031531
  · exact B2031535
  · exact B2031539
  · exact B2031543
  · exact B2031547
  · exact B2031551
  · exact B2031555
  · exact B2031559
  · exact B2031563
  · exact B2031567
  · exact B2031571
  · exact B2031575
  · exact B2031579
  · exact B2031583
  · exact B2031587
  · exact B2031591
  · exact B2031595
  · exact B2031599
  · exact B2031603
  · exact B2031607
  · exact B2031611
  · exact B2031615
  · exact B2031619
  · exact B2031623
  · exact B2031627
  · exact B2031631
  · exact B2031635
  · exact B2031639
  · exact B2031643
  · exact B2031647
  · exact B2031651
  · exact B2031655
  · exact B2031659
  · exact B2031663
  · exact B2031667
  · exact B2031671
  · exact B2031675
  · exact B2031679
  · exact B2031683
  · exact B2031687
  · exact B2031691
  · exact B2031695
  · exact B2031699
  · exact B2031703
  · exact B2031707
  · exact B2031711
  · exact B2031715
  · exact B2031719
  · exact B2031723
  · exact B2031727
  · exact B2031731
  · exact B2031735
  · exact B2031739
  · exact B2031743
  · exact B2031747
  · exact B2031751
  · exact B2031755
  · exact B2031759
  · exact B2031763
  · exact B2031767
  · exact B2031771
  · exact B2031775
  · exact B2031779
  · exact B2031783
  · exact B2031787
  · exact B2031791
  · exact B2031795
  · exact B2031799
  · exact B2031803
  · exact B2031807
  · exact B2031811
  · exact B2031815
  · exact B2031819
  · exact B2031823
  · exact B2031827
  · exact B2031831
  · exact B2031835
  · exact B2031839
  · exact B2031843
  · exact B2031847
  · exact B2031851
  · exact B2031855
  · exact B2031859
  · exact B2031863
  · exact B2031867
  · exact B2031871
  · exact B2031875
  · exact B2031879
  · exact B2031883
  · exact B2031887
  · exact B2031891
  · exact B2031895
  · exact B2031899
  · exact B2031903
  · exact B2031907
  · exact B2031911
  · exact B2031915
  · exact B2031919
  · exact B2031923
  · exact B2031927
  · exact B2031931
  · exact B2031935
  · exact B2031939
  · exact B2031943
  · exact B2031947
  · exact B2031951
  · exact B2031955
  · exact B2031959
  · exact B2031963
  · exact B2031967
  · exact B2031971
  · exact B2031975
  · exact B2031979
  · exact B2031983
  · exact B2031987
  · exact B2031991
  · exact B2031995
  · exact B2031999
  · exact B2032003
  · exact B2032007
  · exact B2032011
  · exact B2032015
  · exact B2032019
  · exact B2032023
  · exact B2032027
  · exact B2032031
  · exact B2032035
  · exact B2032039
  · exact B2032043
  · exact B2032047
  · exact B2032051
  · exact B2032055
  · exact B2032059
  · exact B2032063
  · exact B2032067
  · exact B2032071
  · exact B2032075
  · exact B2032079
  · exact B2032083
  · exact B2032087
  · exact B2032091
  · exact B2032095
  · exact B2032099
  · exact B2032103
  · exact B2032107
  · exact B2032111
  · exact B2032115
  · exact B2032119
  · exact B2032123
  · exact B2032127
  · exact B2032131
  · exact B2032135
  · exact B2032139
  · exact B2032143
  · exact B2032147
  · exact B2032151
  · exact B2032155
  · exact B2032159
  · exact B2032163
  · exact B2032167
  · exact B2032171
  · exact B2032175
  · exact B2032179
  · exact B2032183
  · exact B2032187
  · exact B2032191
  · exact B2032195
  · exact B2032199
  · exact B2032203
  · exact B2032207
  · exact B2032211
  · exact B2032215
  · exact B2032219
  · exact B2032223
  · exact B2032227
  · exact B2032231
  · exact B2032235
  · exact B2032239
  · exact B2032243
  · exact B2032247
  · exact B2032251
  · exact B2032255
  · exact B2032259
  · exact B2032263
  · exact B2032267
  · exact B2032271
  · exact B2032275
  · exact B2032279
  · exact B2032283
  · exact B2032287
  · exact B2032291
  · exact B2032295
  · exact B2032299
  · exact B2032303
  · exact B2032307
  · exact B2032311
  · exact B2032315
  · exact B2032319
  · exact B2032323
  · exact B2032327
  · exact B2032331
  · exact B2032335
  · exact B2032339
  · exact B2032343
  · exact B2032347
  · exact B2032351
  · exact B2032355
  · exact B2032359
  · exact B2032363
  · exact B2032367
  · exact B2032371
  · exact B2032375
  · exact B2032379
  · exact B2032383
  · exact B2032387
  · exact B2032391
  · exact B2032395
  · exact B2032399
  · exact B2032403
  · exact B2032407
  · exact B2032411
  · exact B2032415
  · exact B2032419
  · exact B2032423
  · exact B2032427
  · exact B2032431
  · exact B2032435
  · exact B2032439
  · exact B2032443
  · exact B2032447
  · exact B2032451
  · exact B2032455
  · exact B2032459
  · exact B2032463
  · exact B2032467
  · exact B2032471
  · exact B2032475
  · exact B2032479
  · exact B2032483
  · exact B2032487
  · exact B2032491
  · exact B2032495
  · exact B2032499
  · exact B2032503
  · exact B2032507
  · exact B2032511
  · exact B2032515
  · exact B2032519
  · exact B2032523
  · exact B2032527
  · exact B2032531
  · exact B2032535
  · exact B2032539
  · exact B2032543
  · exact B2032547
  · exact B2032551
  · exact B2032555
  · exact B2032559
  · exact B2032563
  · exact B2032567
  · exact B2032571
  · exact B2032575
  · exact B2032579
  · exact B2032583
  · exact B2032587
  · exact B2032591
  · exact B2032595
  · exact B2032599
  · exact B2032603
  · exact B2032607
  · exact B2032611
  · exact B2032615
  · exact B2032619
  · exact B2032623
  · exact B2032627
  · exact B2032631
  · exact B2032635
  · exact B2032639
  · exact B2032643
  · exact B2032647
  · exact B2032651
  · exact B2032655
  · exact B2032659
  · exact B2032663
  · exact B2032667
  · exact B2032671
  · exact B2032675
  · exact B2032679
  · exact B2032683
  · exact B2032687
  · exact B2032691
  · exact B2032695
  · exact B2032699
  · exact B2032703
  · exact B2032707
  · exact B2032711
  · exact B2032715
  · exact B2032719
  · exact B2032723
  · exact B2032727
  · exact B2032731
  · exact B2032735
  · exact B2032739
  · exact B2032743
  · exact B2032747
  · exact B2032751
  · exact B2032755
  · exact B2032759
  · exact B2032763
  · exact B2032767
  · exact B2032771
  · exact B2032775
  · exact B2032779
  · exact B2032783
  · exact B2032787
  · exact B2032791
  · exact B2032795
  · exact B2032799
  · exact B2032803
  · exact B2032807
  · exact B2032811
  · exact B2032815
  · exact B2032819
  · exact B2032823
  · exact B2032827
  · exact B2032831
  · exact B2032835
  · exact B2032839
  · exact B2032843
  · exact B2032847
  · exact B2032851
  · exact B2032855
  · exact B2032859
  · exact B2032863
  · exact B2032867
  · exact B2032871
  · exact B2032875
  · exact B2032879
  · exact B2032883
  · exact B2032887
  · exact B2032891
  · exact B2032895
  · exact B2032899
  · exact B2032903
  · exact B2032907
  · exact B2032911
  · exact B2032915
  · exact B2032919
  · exact B2032923
  · exact B2032927
  · exact B2032931
  · exact B2032935
  · exact B2032939
  · exact B2032943
  · exact B2032947
  · exact B2032951
  · exact B2032955
  · exact B2032959
  · exact B2032963
  · exact B2032967
  · exact B2032971
  · exact B2032975
  · exact B2032979
  · exact B2032983
  · exact B2032987
  · exact B2032991
  · exact B2032995
  · exact B2032999
  · exact B2033003
  · exact B2033007
  · exact B2033011
  · exact B2033015
  · exact B2033019
  · exact B2033023
  · exact B2033027
  · exact B2033031
  · exact B2033035
  · exact B2033039
  · exact B2033043
  · exact B2033047
  · exact B2033051
  · exact B2033055
  · exact B2033059
  · exact B2033063
  · exact B2033067
  · exact B2033071
  · exact B2033075
  · exact B2033079
  · exact B2033083
  · exact B2033087
  · exact B2033091
  · exact B2033095
  · exact B2033099
  · exact B2033103
  · exact B2033107
  · exact B2033111
  · exact B2033115
  · exact B2033119
  · exact B2033123
  · exact B2033127
  · exact B2033131
  · exact B2033135
  · exact B2033139
  · exact B2033143
  · exact B2033147
  · exact B2033151
  · exact B2033155
  · exact B2033159
  · exact B2033163
  · exact B2033167
  · exact B2033171
  · exact B2033175
  · exact B2033179
  · exact B2033183
  · exact B2033187
  · exact B2033191
  · exact B2033195
  · exact B2033199
  · exact B2033203
  · exact B2033207
  · exact B2033211
  · exact B2033215
  · exact B2033219
  · exact B2033223
  · exact B2033227
  · exact B2033231
  · exact B2033235
  · exact B2033239
  · exact B2033243
  · exact B2033247
  · exact B2033251
  · exact B2033255
  · exact B2033259
  · exact B2033263
  · exact B2033267
  · exact B2033271
  · exact B2033275
  · exact B2033279
  · exact B2033283
  · exact B2033287
  · exact B2033291
  · exact B2033295
  · exact B2033299
  · exact B2033303
  · exact B2033307
  · exact B2033311
  · exact B2033315
  · exact B2033319
  · exact B2033323
  · exact B2033327
  · exact B2033331
  · exact B2033335
  · exact B2033339
  · exact B2033343
  · exact B2033347
  · exact B2033351
  · exact B2033355
  · exact B2033359
  · exact B2033363
  · exact B2033367
  · exact B2033371
  · exact B2033375
  · exact B2033379
  · exact B2033383
  · exact B2033387
  · exact B2033391
  · exact B2033395
  · exact B2033399
  · exact B2033403
  · exact B2033407
  · exact B2033411
  · exact B2033415
  · exact B2033419
  · exact B2033423
  · exact B2033427
  · exact B2033431
  · exact B2033435
theorem solution (m : ℕ) (hlo : 2031435 ≤ m) (hhi : m ≤ 2033435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 507858 ≤ j := by omega
    have hj2 : j ≤ 508358 := by omega
    have hb : Blo 2031435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
