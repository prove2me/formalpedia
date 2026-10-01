-- Prove2me | solution 1 for syracuse_descends_range_2051435_2053435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:49:28.48925+00:00
-- url     : https://prove2.me/submissions/43e78e03-ff48-4cba-bc00-b79df3444e5f

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

theorem B2307865 : Blo 2051435 2307865 := bbase (se 2 (by rfl) ⟨865449, by rfl⟩ : syracuseStep 2307865 = 1730899) (by norm_num)
theorem B3077153 : Blo 2051435 3077153 := bstep (se 2 (by rfl) ⟨1153932, by rfl⟩ : syracuseStep 3077153 = 2307865) B2307865
theorem B2051435 : Blo 2051435 2051435 := bstep (se 1 (by rfl) ⟨1538576, by rfl⟩ : syracuseStep 2051435 = 3077153) B3077153
theorem B7789061 : Blo 2051435 7789061 := bbase (se 4 (by rfl) ⟨730224, by rfl⟩ : syracuseStep 7789061 = 1460449) (by norm_num)
theorem B5192707 : Blo 2051435 5192707 := bstep (se 1 (by rfl) ⟨3894530, by rfl⟩ : syracuseStep 5192707 = 7789061) B7789061
theorem B6923609 : Blo 2051435 6923609 := bstep (se 2 (by rfl) ⟨2596353, by rfl⟩ : syracuseStep 6923609 = 5192707) B5192707
theorem B4615739 : Blo 2051435 4615739 := bstep (se 1 (by rfl) ⟨3461804, by rfl⟩ : syracuseStep 4615739 = 6923609) B6923609
theorem B3077159 : Blo 2051435 3077159 := bstep (se 1 (by rfl) ⟨2307869, by rfl⟩ : syracuseStep 3077159 = 4615739) B4615739
theorem B2051439 : Blo 2051435 2051439 := bstep (se 1 (by rfl) ⟨1538579, by rfl⟩ : syracuseStep 2051439 = 3077159) B3077159
theorem B3077165 : Blo 2051435 3077165 := bbase (se 3 (by rfl) ⟨576968, by rfl⟩ : syracuseStep 3077165 = 1153937) (by norm_num)
theorem B2051443 : Blo 2051435 2051443 := bstep (se 1 (by rfl) ⟨1538582, by rfl⟩ : syracuseStep 2051443 = 3077165) B3077165
theorem B4615757 : Blo 2051435 4615757 := bbase (se 3 (by rfl) ⟨865454, by rfl⟩ : syracuseStep 4615757 = 1730909) (by norm_num)
theorem B3077171 : Blo 2051435 3077171 := bstep (se 1 (by rfl) ⟨2307878, by rfl⟩ : syracuseStep 3077171 = 4615757) B4615757
theorem B2051447 : Blo 2051435 2051447 := bstep (se 1 (by rfl) ⟨1538585, by rfl⟩ : syracuseStep 2051447 = 3077171) B3077171
theorem B2596369 : Blo 2051435 2596369 := bbase (se 2 (by rfl) ⟨973638, by rfl⟩ : syracuseStep 2596369 = 1947277) (by norm_num)
theorem B3461825 : Blo 2051435 3461825 := bstep (se 2 (by rfl) ⟨1298184, by rfl⟩ : syracuseStep 3461825 = 2596369) B2596369
theorem B2307883 : Blo 2051435 2307883 := bstep (se 1 (by rfl) ⟨1730912, by rfl⟩ : syracuseStep 2307883 = 3461825) B3461825
theorem B3077177 : Blo 2051435 3077177 := bstep (se 2 (by rfl) ⟨1153941, by rfl⟩ : syracuseStep 3077177 = 2307883) B2307883
theorem B2051451 : Blo 2051435 2051451 := bstep (se 1 (by rfl) ⟨1538588, by rfl⟩ : syracuseStep 2051451 = 3077177) B3077177
theorem B4381381 : Blo 2051435 4381381 := bbase (se 4 (by rfl) ⟨410754, by rfl⟩ : syracuseStep 4381381 = 821509) (by norm_num)
theorem B23367365 : Blo 2051435 23367365 := bstep (se 4 (by rfl) ⟨2190690, by rfl⟩ : syracuseStep 23367365 = 4381381) B4381381
theorem B15578243 : Blo 2051435 15578243 := bstep (se 1 (by rfl) ⟨11683682, by rfl⟩ : syracuseStep 15578243 = 23367365) B23367365
theorem B10385495 : Blo 2051435 10385495 := bstep (se 1 (by rfl) ⟨7789121, by rfl⟩ : syracuseStep 10385495 = 15578243) B15578243
theorem B6923663 : Blo 2051435 6923663 := bstep (se 1 (by rfl) ⟨5192747, by rfl⟩ : syracuseStep 6923663 = 10385495) B10385495
theorem B4615775 : Blo 2051435 4615775 := bstep (se 1 (by rfl) ⟨3461831, by rfl⟩ : syracuseStep 4615775 = 6923663) B6923663
theorem B3077183 : Blo 2051435 3077183 := bstep (se 1 (by rfl) ⟨2307887, by rfl⟩ : syracuseStep 3077183 = 4615775) B4615775
theorem B2051455 : Blo 2051435 2051455 := bstep (se 1 (by rfl) ⟨1538591, by rfl⟩ : syracuseStep 2051455 = 3077183) B3077183
theorem B3077189 : Blo 2051435 3077189 := bbase (se 4 (by rfl) ⟨288486, by rfl⟩ : syracuseStep 3077189 = 576973) (by norm_num)
theorem B2051459 : Blo 2051435 2051459 := bstep (se 1 (by rfl) ⟨1538594, by rfl⟩ : syracuseStep 2051459 = 3077189) B3077189
theorem B3461845 : Blo 2051435 3461845 := bbase (se 7 (by rfl) ⟨40568, by rfl⟩ : syracuseStep 3461845 = 81137) (by norm_num)
theorem B4615793 : Blo 2051435 4615793 := bstep (se 2 (by rfl) ⟨1730922, by rfl⟩ : syracuseStep 4615793 = 3461845) B3461845
theorem B3077195 : Blo 2051435 3077195 := bstep (se 1 (by rfl) ⟨2307896, by rfl⟩ : syracuseStep 3077195 = 4615793) B4615793
theorem B2051463 : Blo 2051435 2051463 := bstep (se 1 (by rfl) ⟨1538597, by rfl⟩ : syracuseStep 2051463 = 3077195) B3077195
theorem B2307901 : Blo 2051435 2307901 := bbase (se 3 (by rfl) ⟨432731, by rfl⟩ : syracuseStep 2307901 = 865463) (by norm_num)
theorem B3077201 : Blo 2051435 3077201 := bstep (se 2 (by rfl) ⟨1153950, by rfl⟩ : syracuseStep 3077201 = 2307901) B2307901
theorem B2051467 : Blo 2051435 2051467 := bstep (se 1 (by rfl) ⟨1538600, by rfl⟩ : syracuseStep 2051467 = 3077201) B3077201
theorem B6923717 : Blo 2051435 6923717 := bbase (se 4 (by rfl) ⟨649098, by rfl⟩ : syracuseStep 6923717 = 1298197) (by norm_num)
theorem B4615811 : Blo 2051435 4615811 := bstep (se 1 (by rfl) ⟨3461858, by rfl⟩ : syracuseStep 4615811 = 6923717) B6923717
theorem B3077207 : Blo 2051435 3077207 := bstep (se 1 (by rfl) ⟨2307905, by rfl⟩ : syracuseStep 3077207 = 4615811) B4615811
theorem B2051471 : Blo 2051435 2051471 := bstep (se 1 (by rfl) ⟨1538603, by rfl⟩ : syracuseStep 2051471 = 3077207) B3077207
theorem B3077213 : Blo 2051435 3077213 := bbase (se 3 (by rfl) ⟨576977, by rfl⟩ : syracuseStep 3077213 = 1153955) (by norm_num)
theorem B2051475 : Blo 2051435 2051475 := bstep (se 1 (by rfl) ⟨1538606, by rfl⟩ : syracuseStep 2051475 = 3077213) B3077213
theorem B4615829 : Blo 2051435 4615829 := bbase (se 6 (by rfl) ⟨108183, by rfl⟩ : syracuseStep 4615829 = 216367) (by norm_num)
theorem B3077219 : Blo 2051435 3077219 := bstep (se 1 (by rfl) ⟨2307914, by rfl⟩ : syracuseStep 3077219 = 4615829) B4615829
theorem B2051479 : Blo 2051435 2051479 := bstep (se 1 (by rfl) ⟨1538609, by rfl⟩ : syracuseStep 2051479 = 3077219) B3077219
theorem B2190721 : Blo 2051435 2190721 := bbase (se 2 (by rfl) ⟨821520, by rfl⟩ : syracuseStep 2190721 = 1643041) (by norm_num)
theorem B2920961 : Blo 2051435 2920961 := bstep (se 2 (by rfl) ⟨1095360, by rfl⟩ : syracuseStep 2920961 = 2190721) B2190721
theorem B7789229 : Blo 2051435 7789229 := bstep (se 3 (by rfl) ⟨1460480, by rfl⟩ : syracuseStep 7789229 = 2920961) B2920961
theorem B5192819 : Blo 2051435 5192819 := bstep (se 1 (by rfl) ⟨3894614, by rfl⟩ : syracuseStep 5192819 = 7789229) B7789229
theorem B3461879 : Blo 2051435 3461879 := bstep (se 1 (by rfl) ⟨2596409, by rfl⟩ : syracuseStep 3461879 = 5192819) B5192819
theorem B2307919 : Blo 2051435 2307919 := bstep (se 1 (by rfl) ⟨1730939, by rfl⟩ : syracuseStep 2307919 = 3461879) B3461879
theorem B3077225 : Blo 2051435 3077225 := bstep (se 2 (by rfl) ⟨1153959, by rfl⟩ : syracuseStep 3077225 = 2307919) B2307919
theorem B2051483 : Blo 2051435 2051483 := bstep (se 1 (by rfl) ⟨1538612, by rfl⟩ : syracuseStep 2051483 = 3077225) B3077225
theorem B75882581 : Blo 2051435 75882581 := bbase (se 8 (by rfl) ⟨444624, by rfl⟩ : syracuseStep 75882581 = 889249) (by norm_num)
theorem B50588387 : Blo 2051435 50588387 := bstep (se 1 (by rfl) ⟨37941290, by rfl⟩ : syracuseStep 50588387 = 75882581) B75882581
theorem B33725591 : Blo 2051435 33725591 := bstep (se 1 (by rfl) ⟨25294193, by rfl⟩ : syracuseStep 33725591 = 50588387) B50588387
theorem B22483727 : Blo 2051435 22483727 := bstep (se 1 (by rfl) ⟨16862795, by rfl⟩ : syracuseStep 22483727 = 33725591) B33725591
theorem B14989151 : Blo 2051435 14989151 := bstep (se 1 (by rfl) ⟨11241863, by rfl⟩ : syracuseStep 14989151 = 22483727) B22483727
theorem B39971069 : Blo 2051435 39971069 := bstep (se 3 (by rfl) ⟨7494575, by rfl⟩ : syracuseStep 39971069 = 14989151) B14989151
theorem B26647379 : Blo 2051435 26647379 := bstep (se 1 (by rfl) ⟨19985534, by rfl⟩ : syracuseStep 26647379 = 39971069) B39971069
theorem B17764919 : Blo 2051435 17764919 := bstep (se 1 (by rfl) ⟨13323689, by rfl⟩ : syracuseStep 17764919 = 26647379) B26647379
theorem B11843279 : Blo 2051435 11843279 := bstep (se 1 (by rfl) ⟨8882459, by rfl⟩ : syracuseStep 11843279 = 17764919) B17764919
theorem B7895519 : Blo 2051435 7895519 := bstep (se 1 (by rfl) ⟨5921639, by rfl⟩ : syracuseStep 7895519 = 11843279) B11843279
theorem B5263679 : Blo 2051435 5263679 := bstep (se 1 (by rfl) ⟨3947759, by rfl⟩ : syracuseStep 5263679 = 7895519) B7895519
theorem B3509119 : Blo 2051435 3509119 := bstep (se 1 (by rfl) ⟨2631839, by rfl⟩ : syracuseStep 3509119 = 5263679) B5263679
theorem B4678825 : Blo 2051435 4678825 := bstep (se 2 (by rfl) ⟨1754559, by rfl⟩ : syracuseStep 4678825 = 3509119) B3509119
theorem B6238433 : Blo 2051435 6238433 := bstep (se 2 (by rfl) ⟨2339412, by rfl⟩ : syracuseStep 6238433 = 4678825) B4678825
theorem B4158955 : Blo 2051435 4158955 := bstep (se 1 (by rfl) ⟨3119216, by rfl⟩ : syracuseStep 4158955 = 6238433) B6238433
theorem B5545273 : Blo 2051435 5545273 := bstep (se 2 (by rfl) ⟨2079477, by rfl⟩ : syracuseStep 5545273 = 4158955) B4158955
theorem B7393697 : Blo 2051435 7393697 := bstep (se 2 (by rfl) ⟨2772636, by rfl⟩ : syracuseStep 7393697 = 5545273) B5545273
theorem B4929131 : Blo 2051435 4929131 := bstep (se 1 (by rfl) ⟨3696848, by rfl⟩ : syracuseStep 4929131 = 7393697) B7393697
theorem B13144349 : Blo 2051435 13144349 := bstep (se 3 (by rfl) ⟨2464565, by rfl⟩ : syracuseStep 13144349 = 4929131) B4929131
theorem B8762899 : Blo 2051435 8762899 := bstep (se 1 (by rfl) ⟨6572174, by rfl⟩ : syracuseStep 8762899 = 13144349) B13144349
theorem B11683865 : Blo 2051435 11683865 := bstep (se 2 (by rfl) ⟨4381449, by rfl⟩ : syracuseStep 11683865 = 8762899) B8762899
theorem B7789243 : Blo 2051435 7789243 := bstep (se 1 (by rfl) ⟨5841932, by rfl⟩ : syracuseStep 7789243 = 11683865) B11683865
theorem B10385657 : Blo 2051435 10385657 := bstep (se 2 (by rfl) ⟨3894621, by rfl⟩ : syracuseStep 10385657 = 7789243) B7789243
theorem B6923771 : Blo 2051435 6923771 := bstep (se 1 (by rfl) ⟨5192828, by rfl⟩ : syracuseStep 6923771 = 10385657) B10385657
theorem B4615847 : Blo 2051435 4615847 := bstep (se 1 (by rfl) ⟨3461885, by rfl⟩ : syracuseStep 4615847 = 6923771) B6923771
theorem B3077231 : Blo 2051435 3077231 := bstep (se 1 (by rfl) ⟨2307923, by rfl⟩ : syracuseStep 3077231 = 4615847) B4615847
theorem B2051487 : Blo 2051435 2051487 := bstep (se 1 (by rfl) ⟨1538615, by rfl⟩ : syracuseStep 2051487 = 3077231) B3077231
theorem B3077237 : Blo 2051435 3077237 := bbase (se 5 (by rfl) ⟨144245, by rfl⟩ : syracuseStep 3077237 = 288491) (by norm_num)
theorem B2051491 : Blo 2051435 2051491 := bstep (se 1 (by rfl) ⟨1538618, by rfl⟩ : syracuseStep 2051491 = 3077237) B3077237
theorem B3894637 : Blo 2051435 3894637 := bbase (se 3 (by rfl) ⟨730244, by rfl⟩ : syracuseStep 3894637 = 1460489) (by norm_num)
theorem B5192849 : Blo 2051435 5192849 := bstep (se 2 (by rfl) ⟨1947318, by rfl⟩ : syracuseStep 5192849 = 3894637) B3894637
theorem B3461899 : Blo 2051435 3461899 := bstep (se 1 (by rfl) ⟨2596424, by rfl⟩ : syracuseStep 3461899 = 5192849) B5192849
theorem B4615865 : Blo 2051435 4615865 := bstep (se 2 (by rfl) ⟨1730949, by rfl⟩ : syracuseStep 4615865 = 3461899) B3461899
theorem B3077243 : Blo 2051435 3077243 := bstep (se 1 (by rfl) ⟨2307932, by rfl⟩ : syracuseStep 3077243 = 4615865) B4615865
theorem B2051495 : Blo 2051435 2051495 := bstep (se 1 (by rfl) ⟨1538621, by rfl⟩ : syracuseStep 2051495 = 3077243) B3077243
theorem B2307937 : Blo 2051435 2307937 := bbase (se 2 (by rfl) ⟨865476, by rfl⟩ : syracuseStep 2307937 = 1730953) (by norm_num)
theorem B3077249 : Blo 2051435 3077249 := bstep (se 2 (by rfl) ⟨1153968, by rfl⟩ : syracuseStep 3077249 = 2307937) B2307937
theorem B2051499 : Blo 2051435 2051499 := bstep (se 1 (by rfl) ⟨1538624, by rfl⟩ : syracuseStep 2051499 = 3077249) B3077249
theorem B5192869 : Blo 2051435 5192869 := bbase (se 4 (by rfl) ⟨486831, by rfl⟩ : syracuseStep 5192869 = 973663) (by norm_num)
theorem B6923825 : Blo 2051435 6923825 := bstep (se 2 (by rfl) ⟨2596434, by rfl⟩ : syracuseStep 6923825 = 5192869) B5192869
theorem B4615883 : Blo 2051435 4615883 := bstep (se 1 (by rfl) ⟨3461912, by rfl⟩ : syracuseStep 4615883 = 6923825) B6923825
theorem B3077255 : Blo 2051435 3077255 := bstep (se 1 (by rfl) ⟨2307941, by rfl⟩ : syracuseStep 3077255 = 4615883) B4615883
theorem B2051503 : Blo 2051435 2051503 := bstep (se 1 (by rfl) ⟨1538627, by rfl⟩ : syracuseStep 2051503 = 3077255) B3077255
theorem B3077261 : Blo 2051435 3077261 := bbase (se 3 (by rfl) ⟨576986, by rfl⟩ : syracuseStep 3077261 = 1153973) (by norm_num)
theorem B2051507 : Blo 2051435 2051507 := bstep (se 1 (by rfl) ⟨1538630, by rfl⟩ : syracuseStep 2051507 = 3077261) B3077261
theorem B4615901 : Blo 2051435 4615901 := bbase (se 3 (by rfl) ⟨865481, by rfl⟩ : syracuseStep 4615901 = 1730963) (by norm_num)
theorem B3077267 : Blo 2051435 3077267 := bstep (se 1 (by rfl) ⟨2307950, by rfl⟩ : syracuseStep 3077267 = 4615901) B4615901
theorem B2051511 : Blo 2051435 2051511 := bstep (se 1 (by rfl) ⟨1538633, by rfl⟩ : syracuseStep 2051511 = 3077267) B3077267
theorem B3461933 : Blo 2051435 3461933 := bbase (se 3 (by rfl) ⟨649112, by rfl⟩ : syracuseStep 3461933 = 1298225) (by norm_num)
theorem B2307955 : Blo 2051435 2307955 := bstep (se 1 (by rfl) ⟨1730966, by rfl⟩ : syracuseStep 2307955 = 3461933) B3461933
theorem B3077273 : Blo 2051435 3077273 := bstep (se 2 (by rfl) ⟨1153977, by rfl⟩ : syracuseStep 3077273 = 2307955) B2307955
theorem B2051515 : Blo 2051435 2051515 := bstep (se 1 (by rfl) ⟨1538636, by rfl⟩ : syracuseStep 2051515 = 3077273) B3077273
theorem B3330973 : Blo 2051435 3330973 := bbase (se 3 (by rfl) ⟨624557, by rfl⟩ : syracuseStep 3330973 = 1249115) (by norm_num)
theorem B17765189 : Blo 2051435 17765189 := bstep (se 4 (by rfl) ⟨1665486, by rfl⟩ : syracuseStep 17765189 = 3330973) B3330973
theorem B11843459 : Blo 2051435 11843459 := bstep (se 1 (by rfl) ⟨8882594, by rfl⟩ : syracuseStep 11843459 = 17765189) B17765189
theorem B7895639 : Blo 2051435 7895639 := bstep (se 1 (by rfl) ⟨5921729, by rfl⟩ : syracuseStep 7895639 = 11843459) B11843459
theorem B5263759 : Blo 2051435 5263759 := bstep (se 1 (by rfl) ⟨3947819, by rfl⟩ : syracuseStep 5263759 = 7895639) B7895639
theorem B7018345 : Blo 2051435 7018345 := bstep (se 2 (by rfl) ⟨2631879, by rfl⟩ : syracuseStep 7018345 = 5263759) B5263759
theorem B37431173 : Blo 2051435 37431173 := bstep (se 4 (by rfl) ⟨3509172, by rfl⟩ : syracuseStep 37431173 = 7018345) B7018345
theorem B24954115 : Blo 2051435 24954115 := bstep (se 1 (by rfl) ⟨18715586, by rfl⟩ : syracuseStep 24954115 = 37431173) B37431173
theorem B33272153 : Blo 2051435 33272153 := bstep (se 2 (by rfl) ⟨12477057, by rfl⟩ : syracuseStep 33272153 = 24954115) B24954115
theorem B22181435 : Blo 2051435 22181435 := bstep (se 1 (by rfl) ⟨16636076, by rfl⟩ : syracuseStep 22181435 = 33272153) B33272153
theorem B14787623 : Blo 2051435 14787623 := bstep (se 1 (by rfl) ⟨11090717, by rfl⟩ : syracuseStep 14787623 = 22181435) B22181435
theorem B39433661 : Blo 2051435 39433661 := bstep (se 3 (by rfl) ⟨7393811, by rfl⟩ : syracuseStep 39433661 = 14787623) B14787623
theorem B26289107 : Blo 2051435 26289107 := bstep (se 1 (by rfl) ⟨19716830, by rfl⟩ : syracuseStep 26289107 = 39433661) B39433661
theorem B17526071 : Blo 2051435 17526071 := bstep (se 1 (by rfl) ⟨13144553, by rfl⟩ : syracuseStep 17526071 = 26289107) B26289107
theorem B11684047 : Blo 2051435 11684047 := bstep (se 1 (by rfl) ⟨8763035, by rfl⟩ : syracuseStep 11684047 = 17526071) B17526071
theorem B15578729 : Blo 2051435 15578729 := bstep (se 2 (by rfl) ⟨5842023, by rfl⟩ : syracuseStep 15578729 = 11684047) B11684047
theorem B10385819 : Blo 2051435 10385819 := bstep (se 1 (by rfl) ⟨7789364, by rfl⟩ : syracuseStep 10385819 = 15578729) B15578729
theorem B6923879 : Blo 2051435 6923879 := bstep (se 1 (by rfl) ⟨5192909, by rfl⟩ : syracuseStep 6923879 = 10385819) B10385819
theorem B4615919 : Blo 2051435 4615919 := bstep (se 1 (by rfl) ⟨3461939, by rfl⟩ : syracuseStep 4615919 = 6923879) B6923879
theorem B3077279 : Blo 2051435 3077279 := bstep (se 1 (by rfl) ⟨2307959, by rfl⟩ : syracuseStep 3077279 = 4615919) B4615919
theorem B2051519 : Blo 2051435 2051519 := bstep (se 1 (by rfl) ⟨1538639, by rfl⟩ : syracuseStep 2051519 = 3077279) B3077279
theorem B3077285 : Blo 2051435 3077285 := bbase (se 4 (by rfl) ⟨288495, by rfl⟩ : syracuseStep 3077285 = 576991) (by norm_num)
theorem B2051523 : Blo 2051435 2051523 := bstep (se 1 (by rfl) ⟨1538642, by rfl⟩ : syracuseStep 2051523 = 3077285) B3077285
theorem B2596465 : Blo 2051435 2596465 := bbase (se 2 (by rfl) ⟨973674, by rfl⟩ : syracuseStep 2596465 = 1947349) (by norm_num)
theorem B3461953 : Blo 2051435 3461953 := bstep (se 2 (by rfl) ⟨1298232, by rfl⟩ : syracuseStep 3461953 = 2596465) B2596465
theorem B4615937 : Blo 2051435 4615937 := bstep (se 2 (by rfl) ⟨1730976, by rfl⟩ : syracuseStep 4615937 = 3461953) B3461953
theorem B3077291 : Blo 2051435 3077291 := bstep (se 1 (by rfl) ⟨2307968, by rfl⟩ : syracuseStep 3077291 = 4615937) B4615937
theorem B2051527 : Blo 2051435 2051527 := bstep (se 1 (by rfl) ⟨1538645, by rfl⟩ : syracuseStep 2051527 = 3077291) B3077291
theorem B2307973 : Blo 2051435 2307973 := bbase (se 4 (by rfl) ⟨216372, by rfl⟩ : syracuseStep 2307973 = 432745) (by norm_num)
theorem B3077297 : Blo 2051435 3077297 := bstep (se 2 (by rfl) ⟨1153986, by rfl⟩ : syracuseStep 3077297 = 2307973) B2307973
theorem B2051531 : Blo 2051435 2051531 := bstep (se 1 (by rfl) ⟨1538648, by rfl⟩ : syracuseStep 2051531 = 3077297) B3077297
theorem B3286165 : Blo 2051435 3286165 := bbase (se 6 (by rfl) ⟨77019, by rfl⟩ : syracuseStep 3286165 = 154039) (by norm_num)
theorem B4381553 : Blo 2051435 4381553 := bstep (se 2 (by rfl) ⟨1643082, by rfl⟩ : syracuseStep 4381553 = 3286165) B3286165
theorem B2921035 : Blo 2051435 2921035 := bstep (se 1 (by rfl) ⟨2190776, by rfl⟩ : syracuseStep 2921035 = 4381553) B4381553
theorem B3894713 : Blo 2051435 3894713 := bstep (se 2 (by rfl) ⟨1460517, by rfl⟩ : syracuseStep 3894713 = 2921035) B2921035
theorem B2596475 : Blo 2051435 2596475 := bstep (se 1 (by rfl) ⟨1947356, by rfl⟩ : syracuseStep 2596475 = 3894713) B3894713
theorem B6923933 : Blo 2051435 6923933 := bstep (se 3 (by rfl) ⟨1298237, by rfl⟩ : syracuseStep 6923933 = 2596475) B2596475
theorem B4615955 : Blo 2051435 4615955 := bstep (se 1 (by rfl) ⟨3461966, by rfl⟩ : syracuseStep 4615955 = 6923933) B6923933
theorem B3077303 : Blo 2051435 3077303 := bstep (se 1 (by rfl) ⟨2307977, by rfl⟩ : syracuseStep 3077303 = 4615955) B4615955
theorem B2051535 : Blo 2051435 2051535 := bstep (se 1 (by rfl) ⟨1538651, by rfl⟩ : syracuseStep 2051535 = 3077303) B3077303
theorem B3077309 : Blo 2051435 3077309 := bbase (se 3 (by rfl) ⟨576995, by rfl⟩ : syracuseStep 3077309 = 1153991) (by norm_num)
theorem B2051539 : Blo 2051435 2051539 := bstep (se 1 (by rfl) ⟨1538654, by rfl⟩ : syracuseStep 2051539 = 3077309) B3077309
theorem B4615973 : Blo 2051435 4615973 := bbase (se 4 (by rfl) ⟨432747, by rfl⟩ : syracuseStep 4615973 = 865495) (by norm_num)
theorem B3077315 : Blo 2051435 3077315 := bstep (se 1 (by rfl) ⟨2307986, by rfl⟩ : syracuseStep 3077315 = 4615973) B4615973
theorem B2051543 : Blo 2051435 2051543 := bstep (se 1 (by rfl) ⟨1538657, by rfl⟩ : syracuseStep 2051543 = 3077315) B3077315
theorem B5192981 : Blo 2051435 5192981 := bbase (se 6 (by rfl) ⟨121710, by rfl⟩ : syracuseStep 5192981 = 243421) (by norm_num)
theorem B3461987 : Blo 2051435 3461987 := bstep (se 1 (by rfl) ⟨2596490, by rfl⟩ : syracuseStep 3461987 = 5192981) B5192981
theorem B2307991 : Blo 2051435 2307991 := bstep (se 1 (by rfl) ⟨1730993, by rfl⟩ : syracuseStep 2307991 = 3461987) B3461987
theorem B3077321 : Blo 2051435 3077321 := bstep (se 2 (by rfl) ⟨1153995, by rfl⟩ : syracuseStep 3077321 = 2307991) B2307991
theorem B2051547 : Blo 2051435 2051547 := bstep (se 1 (by rfl) ⟨1538660, by rfl⟩ : syracuseStep 2051547 = 3077321) B3077321
theorem B8763173 : Blo 2051435 8763173 := bbase (se 4 (by rfl) ⟨821547, by rfl⟩ : syracuseStep 8763173 = 1643095) (by norm_num)
theorem B5842115 : Blo 2051435 5842115 := bstep (se 1 (by rfl) ⟨4381586, by rfl⟩ : syracuseStep 5842115 = 8763173) B8763173
theorem B3894743 : Blo 2051435 3894743 := bstep (se 1 (by rfl) ⟨2921057, by rfl⟩ : syracuseStep 3894743 = 5842115) B5842115
theorem B10385981 : Blo 2051435 10385981 := bstep (se 3 (by rfl) ⟨1947371, by rfl⟩ : syracuseStep 10385981 = 3894743) B3894743
theorem B6923987 : Blo 2051435 6923987 := bstep (se 1 (by rfl) ⟨5192990, by rfl⟩ : syracuseStep 6923987 = 10385981) B10385981
theorem B4615991 : Blo 2051435 4615991 := bstep (se 1 (by rfl) ⟨3461993, by rfl⟩ : syracuseStep 4615991 = 6923987) B6923987
theorem B3077327 : Blo 2051435 3077327 := bstep (se 1 (by rfl) ⟨2307995, by rfl⟩ : syracuseStep 3077327 = 4615991) B4615991
theorem B2051551 : Blo 2051435 2051551 := bstep (se 1 (by rfl) ⟨1538663, by rfl⟩ : syracuseStep 2051551 = 3077327) B3077327
theorem B3077333 : Blo 2051435 3077333 := bbase (se 7 (by rfl) ⟨36062, by rfl⟩ : syracuseStep 3077333 = 72125) (by norm_num)
theorem B2051555 : Blo 2051435 2051555 := bstep (se 1 (by rfl) ⟨1538666, by rfl⟩ : syracuseStep 2051555 = 3077333) B3077333
theorem B2921069 : Blo 2051435 2921069 := bbase (se 3 (by rfl) ⟨547700, by rfl⟩ : syracuseStep 2921069 = 1095401) (by norm_num)
theorem B7789517 : Blo 2051435 7789517 := bstep (se 3 (by rfl) ⟨1460534, by rfl⟩ : syracuseStep 7789517 = 2921069) B2921069
theorem B5193011 : Blo 2051435 5193011 := bstep (se 1 (by rfl) ⟨3894758, by rfl⟩ : syracuseStep 5193011 = 7789517) B7789517
theorem B3462007 : Blo 2051435 3462007 := bstep (se 1 (by rfl) ⟨2596505, by rfl⟩ : syracuseStep 3462007 = 5193011) B5193011
theorem B4616009 : Blo 2051435 4616009 := bstep (se 2 (by rfl) ⟨1731003, by rfl⟩ : syracuseStep 4616009 = 3462007) B3462007
theorem B3077339 : Blo 2051435 3077339 := bstep (se 1 (by rfl) ⟨2308004, by rfl⟩ : syracuseStep 3077339 = 4616009) B4616009
theorem B2051559 : Blo 2051435 2051559 := bstep (se 1 (by rfl) ⟨1538669, by rfl⟩ : syracuseStep 2051559 = 3077339) B3077339
theorem B2308009 : Blo 2051435 2308009 := bbase (se 2 (by rfl) ⟨865503, by rfl⟩ : syracuseStep 2308009 = 1731007) (by norm_num)
theorem B3077345 : Blo 2051435 3077345 := bstep (se 2 (by rfl) ⟨1154004, by rfl⟩ : syracuseStep 3077345 = 2308009) B2308009
theorem B2051563 : Blo 2051435 2051563 := bstep (se 1 (by rfl) ⟨1538672, by rfl⟩ : syracuseStep 2051563 = 3077345) B3077345
theorem B4159117 : Blo 2051435 4159117 := bbase (se 3 (by rfl) ⟨779834, by rfl⟩ : syracuseStep 4159117 = 1559669) (by norm_num)
theorem B22181957 : Blo 2051435 22181957 := bstep (se 4 (by rfl) ⟨2079558, by rfl⟩ : syracuseStep 22181957 = 4159117) B4159117
theorem B14787971 : Blo 2051435 14787971 := bstep (se 1 (by rfl) ⟨11090978, by rfl⟩ : syracuseStep 14787971 = 22181957) B22181957
theorem B9858647 : Blo 2051435 9858647 := bstep (se 1 (by rfl) ⟨7393985, by rfl⟩ : syracuseStep 9858647 = 14787971) B14787971
theorem B6572431 : Blo 2051435 6572431 := bstep (se 1 (by rfl) ⟨4929323, by rfl⟩ : syracuseStep 6572431 = 9858647) B9858647
theorem B8763241 : Blo 2051435 8763241 := bstep (se 2 (by rfl) ⟨3286215, by rfl⟩ : syracuseStep 8763241 = 6572431) B6572431
theorem B11684321 : Blo 2051435 11684321 := bstep (se 2 (by rfl) ⟨4381620, by rfl⟩ : syracuseStep 11684321 = 8763241) B8763241
theorem B7789547 : Blo 2051435 7789547 := bstep (se 1 (by rfl) ⟨5842160, by rfl⟩ : syracuseStep 7789547 = 11684321) B11684321
theorem B5193031 : Blo 2051435 5193031 := bstep (se 1 (by rfl) ⟨3894773, by rfl⟩ : syracuseStep 5193031 = 7789547) B7789547
theorem B6924041 : Blo 2051435 6924041 := bstep (se 2 (by rfl) ⟨2596515, by rfl⟩ : syracuseStep 6924041 = 5193031) B5193031
theorem B4616027 : Blo 2051435 4616027 := bstep (se 1 (by rfl) ⟨3462020, by rfl⟩ : syracuseStep 4616027 = 6924041) B6924041
theorem B3077351 : Blo 2051435 3077351 := bstep (se 1 (by rfl) ⟨2308013, by rfl⟩ : syracuseStep 3077351 = 4616027) B4616027
theorem B2051567 : Blo 2051435 2051567 := bstep (se 1 (by rfl) ⟨1538675, by rfl⟩ : syracuseStep 2051567 = 3077351) B3077351
theorem B3077357 : Blo 2051435 3077357 := bbase (se 3 (by rfl) ⟨577004, by rfl⟩ : syracuseStep 3077357 = 1154009) (by norm_num)
theorem B2051571 : Blo 2051435 2051571 := bstep (se 1 (by rfl) ⟨1538678, by rfl⟩ : syracuseStep 2051571 = 3077357) B3077357
theorem B4616045 : Blo 2051435 4616045 := bbase (se 3 (by rfl) ⟨865508, by rfl⟩ : syracuseStep 4616045 = 1731017) (by norm_num)
theorem B3077363 : Blo 2051435 3077363 := bstep (se 1 (by rfl) ⟨2308022, by rfl⟩ : syracuseStep 3077363 = 4616045) B4616045
theorem B2051575 : Blo 2051435 2051575 := bstep (se 1 (by rfl) ⟨1538681, by rfl⟩ : syracuseStep 2051575 = 3077363) B3077363
theorem B3894797 : Blo 2051435 3894797 := bbase (se 3 (by rfl) ⟨730274, by rfl⟩ : syracuseStep 3894797 = 1460549) (by norm_num)
theorem B2596531 : Blo 2051435 2596531 := bstep (se 1 (by rfl) ⟨1947398, by rfl⟩ : syracuseStep 2596531 = 3894797) B3894797
theorem B3462041 : Blo 2051435 3462041 := bstep (se 2 (by rfl) ⟨1298265, by rfl⟩ : syracuseStep 3462041 = 2596531) B2596531
theorem B2308027 : Blo 2051435 2308027 := bstep (se 1 (by rfl) ⟨1731020, by rfl⟩ : syracuseStep 2308027 = 3462041) B3462041
theorem B3077369 : Blo 2051435 3077369 := bstep (se 2 (by rfl) ⟨1154013, by rfl⟩ : syracuseStep 3077369 = 2308027) B2308027
theorem B2051579 : Blo 2051435 2051579 := bstep (se 1 (by rfl) ⟨1538684, by rfl⟩ : syracuseStep 2051579 = 3077369) B3077369
theorem B3697021 : Blo 2051435 3697021 := bbase (se 3 (by rfl) ⟨693191, by rfl⟩ : syracuseStep 3697021 = 1386383) (by norm_num)
theorem B19717445 : Blo 2051435 19717445 := bstep (se 4 (by rfl) ⟨1848510, by rfl⟩ : syracuseStep 19717445 = 3697021) B3697021
theorem B52579853 : Blo 2051435 52579853 := bstep (se 3 (by rfl) ⟨9858722, by rfl⟩ : syracuseStep 52579853 = 19717445) B19717445
theorem B35053235 : Blo 2051435 35053235 := bstep (se 1 (by rfl) ⟨26289926, by rfl⟩ : syracuseStep 35053235 = 52579853) B52579853
theorem B23368823 : Blo 2051435 23368823 := bstep (se 1 (by rfl) ⟨17526617, by rfl⟩ : syracuseStep 23368823 = 35053235) B35053235
theorem B15579215 : Blo 2051435 15579215 := bstep (se 1 (by rfl) ⟨11684411, by rfl⟩ : syracuseStep 15579215 = 23368823) B23368823
theorem B10386143 : Blo 2051435 10386143 := bstep (se 1 (by rfl) ⟨7789607, by rfl⟩ : syracuseStep 10386143 = 15579215) B15579215
theorem B6924095 : Blo 2051435 6924095 := bstep (se 1 (by rfl) ⟨5193071, by rfl⟩ : syracuseStep 6924095 = 10386143) B10386143
theorem B4616063 : Blo 2051435 4616063 := bstep (se 1 (by rfl) ⟨3462047, by rfl⟩ : syracuseStep 4616063 = 6924095) B6924095
theorem B3077375 : Blo 2051435 3077375 := bstep (se 1 (by rfl) ⟨2308031, by rfl⟩ : syracuseStep 3077375 = 4616063) B4616063
theorem B2051583 : Blo 2051435 2051583 := bstep (se 1 (by rfl) ⟨1538687, by rfl⟩ : syracuseStep 2051583 = 3077375) B3077375
theorem B3077381 : Blo 2051435 3077381 := bbase (se 4 (by rfl) ⟨288504, by rfl⟩ : syracuseStep 3077381 = 577009) (by norm_num)
theorem B2051587 : Blo 2051435 2051587 := bstep (se 1 (by rfl) ⟨1538690, by rfl⟩ : syracuseStep 2051587 = 3077381) B3077381
theorem B3462061 : Blo 2051435 3462061 := bbase (se 3 (by rfl) ⟨649136, by rfl⟩ : syracuseStep 3462061 = 1298273) (by norm_num)
theorem B4616081 : Blo 2051435 4616081 := bstep (se 2 (by rfl) ⟨1731030, by rfl⟩ : syracuseStep 4616081 = 3462061) B3462061
theorem B3077387 : Blo 2051435 3077387 := bstep (se 1 (by rfl) ⟨2308040, by rfl⟩ : syracuseStep 3077387 = 4616081) B4616081
theorem B2051591 : Blo 2051435 2051591 := bstep (se 1 (by rfl) ⟨1538693, by rfl⟩ : syracuseStep 2051591 = 3077387) B3077387
theorem B2308045 : Blo 2051435 2308045 := bbase (se 3 (by rfl) ⟨432758, by rfl⟩ : syracuseStep 2308045 = 865517) (by norm_num)
theorem B3077393 : Blo 2051435 3077393 := bstep (se 2 (by rfl) ⟨1154022, by rfl⟩ : syracuseStep 3077393 = 2308045) B2308045
theorem B2051595 : Blo 2051435 2051595 := bstep (se 1 (by rfl) ⟨1538696, by rfl⟩ : syracuseStep 2051595 = 3077393) B3077393
theorem B6924149 : Blo 2051435 6924149 := bbase (se 5 (by rfl) ⟨324569, by rfl⟩ : syracuseStep 6924149 = 649139) (by norm_num)
theorem B4616099 : Blo 2051435 4616099 := bstep (se 1 (by rfl) ⟨3462074, by rfl⟩ : syracuseStep 4616099 = 6924149) B6924149
theorem B3077399 : Blo 2051435 3077399 := bstep (se 1 (by rfl) ⟨2308049, by rfl⟩ : syracuseStep 3077399 = 4616099) B4616099
theorem B2051599 : Blo 2051435 2051599 := bstep (se 1 (by rfl) ⟨1538699, by rfl⟩ : syracuseStep 2051599 = 3077399) B3077399
theorem B3077405 : Blo 2051435 3077405 := bbase (se 3 (by rfl) ⟨577013, by rfl⟩ : syracuseStep 3077405 = 1154027) (by norm_num)
theorem B2051603 : Blo 2051435 2051603 := bstep (se 1 (by rfl) ⟨1538702, by rfl⟩ : syracuseStep 2051603 = 3077405) B3077405
theorem B4616117 : Blo 2051435 4616117 := bbase (se 5 (by rfl) ⟨216380, by rfl⟩ : syracuseStep 4616117 = 432761) (by norm_num)
theorem B3077411 : Blo 2051435 3077411 := bstep (se 1 (by rfl) ⟨2308058, by rfl⟩ : syracuseStep 3077411 = 4616117) B4616117
theorem B2051607 : Blo 2051435 2051607 := bstep (se 1 (by rfl) ⟨1538705, by rfl⟩ : syracuseStep 2051607 = 3077411) B3077411
theorem B2772805 : Blo 2051435 2772805 := bbase (se 4 (by rfl) ⟨259950, by rfl⟩ : syracuseStep 2772805 = 519901) (by norm_num)
theorem B3697073 : Blo 2051435 3697073 := bstep (se 2 (by rfl) ⟨1386402, by rfl⟩ : syracuseStep 3697073 = 2772805) B2772805
theorem B2464715 : Blo 2051435 2464715 := bstep (se 1 (by rfl) ⟨1848536, by rfl⟩ : syracuseStep 2464715 = 3697073) B3697073
theorem B6572573 : Blo 2051435 6572573 := bstep (se 3 (by rfl) ⟨1232357, by rfl⟩ : syracuseStep 6572573 = 2464715) B2464715
theorem B4381715 : Blo 2051435 4381715 := bstep (se 1 (by rfl) ⟨3286286, by rfl⟩ : syracuseStep 4381715 = 6572573) B6572573
theorem B11684573 : Blo 2051435 11684573 := bstep (se 3 (by rfl) ⟨2190857, by rfl⟩ : syracuseStep 11684573 = 4381715) B4381715
theorem B7789715 : Blo 2051435 7789715 := bstep (se 1 (by rfl) ⟨5842286, by rfl⟩ : syracuseStep 7789715 = 11684573) B11684573
theorem B5193143 : Blo 2051435 5193143 := bstep (se 1 (by rfl) ⟨3894857, by rfl⟩ : syracuseStep 5193143 = 7789715) B7789715
theorem B3462095 : Blo 2051435 3462095 := bstep (se 1 (by rfl) ⟨2596571, by rfl⟩ : syracuseStep 3462095 = 5193143) B5193143
theorem B2308063 : Blo 2051435 2308063 := bstep (se 1 (by rfl) ⟨1731047, by rfl⟩ : syracuseStep 2308063 = 3462095) B3462095
theorem B3077417 : Blo 2051435 3077417 := bstep (se 2 (by rfl) ⟨1154031, by rfl⟩ : syracuseStep 3077417 = 2308063) B2308063
theorem B2051611 : Blo 2051435 2051611 := bstep (se 1 (by rfl) ⟨1538708, by rfl⟩ : syracuseStep 2051611 = 3077417) B3077417
theorem B3948005 : Blo 2051435 3948005 := bbase (se 4 (by rfl) ⟨370125, by rfl⟩ : syracuseStep 3948005 = 740251) (by norm_num)
theorem B10528013 : Blo 2051435 10528013 := bstep (se 3 (by rfl) ⟨1974002, by rfl⟩ : syracuseStep 10528013 = 3948005) B3948005
theorem B28074701 : Blo 2051435 28074701 := bstep (se 3 (by rfl) ⟨5264006, by rfl⟩ : syracuseStep 28074701 = 10528013) B10528013
theorem B18716467 : Blo 2051435 18716467 := bstep (se 1 (by rfl) ⟨14037350, by rfl⟩ : syracuseStep 18716467 = 28074701) B28074701
theorem B24955289 : Blo 2051435 24955289 := bstep (se 2 (by rfl) ⟨9358233, by rfl⟩ : syracuseStep 24955289 = 18716467) B18716467
theorem B16636859 : Blo 2051435 16636859 := bstep (se 1 (by rfl) ⟨12477644, by rfl⟩ : syracuseStep 16636859 = 24955289) B24955289
theorem B11091239 : Blo 2051435 11091239 := bstep (se 1 (by rfl) ⟨8318429, by rfl⟩ : syracuseStep 11091239 = 16636859) B16636859
theorem B7394159 : Blo 2051435 7394159 := bstep (se 1 (by rfl) ⟨5545619, by rfl⟩ : syracuseStep 7394159 = 11091239) B11091239
theorem B4929439 : Blo 2051435 4929439 := bstep (se 1 (by rfl) ⟨3697079, by rfl⟩ : syracuseStep 4929439 = 7394159) B7394159
theorem B6572585 : Blo 2051435 6572585 := bstep (se 2 (by rfl) ⟨2464719, by rfl⟩ : syracuseStep 6572585 = 4929439) B4929439
theorem B4381723 : Blo 2051435 4381723 := bstep (se 1 (by rfl) ⟨3286292, by rfl⟩ : syracuseStep 4381723 = 6572585) B6572585
theorem B5842297 : Blo 2051435 5842297 := bstep (se 2 (by rfl) ⟨2190861, by rfl⟩ : syracuseStep 5842297 = 4381723) B4381723
theorem B7789729 : Blo 2051435 7789729 := bstep (se 2 (by rfl) ⟨2921148, by rfl⟩ : syracuseStep 7789729 = 5842297) B5842297
theorem B10386305 : Blo 2051435 10386305 := bstep (se 2 (by rfl) ⟨3894864, by rfl⟩ : syracuseStep 10386305 = 7789729) B7789729
theorem B6924203 : Blo 2051435 6924203 := bstep (se 1 (by rfl) ⟨5193152, by rfl⟩ : syracuseStep 6924203 = 10386305) B10386305
theorem B4616135 : Blo 2051435 4616135 := bstep (se 1 (by rfl) ⟨3462101, by rfl⟩ : syracuseStep 4616135 = 6924203) B6924203
theorem B3077423 : Blo 2051435 3077423 := bstep (se 1 (by rfl) ⟨2308067, by rfl⟩ : syracuseStep 3077423 = 4616135) B4616135
theorem B2051615 : Blo 2051435 2051615 := bstep (se 1 (by rfl) ⟨1538711, by rfl⟩ : syracuseStep 2051615 = 3077423) B3077423
theorem B3077429 : Blo 2051435 3077429 := bbase (se 5 (by rfl) ⟨144254, by rfl⟩ : syracuseStep 3077429 = 288509) (by norm_num)
theorem B2051619 : Blo 2051435 2051619 := bstep (se 1 (by rfl) ⟨1538714, by rfl⟩ : syracuseStep 2051619 = 3077429) B3077429
theorem B5193173 : Blo 2051435 5193173 := bbase (se 7 (by rfl) ⟨60857, by rfl⟩ : syracuseStep 5193173 = 121715) (by norm_num)
theorem B3462115 : Blo 2051435 3462115 := bstep (se 1 (by rfl) ⟨2596586, by rfl⟩ : syracuseStep 3462115 = 5193173) B5193173
theorem B4616153 : Blo 2051435 4616153 := bstep (se 2 (by rfl) ⟨1731057, by rfl⟩ : syracuseStep 4616153 = 3462115) B3462115
theorem B3077435 : Blo 2051435 3077435 := bstep (se 1 (by rfl) ⟨2308076, by rfl⟩ : syracuseStep 3077435 = 4616153) B4616153
theorem B2051623 : Blo 2051435 2051623 := bstep (se 1 (by rfl) ⟨1538717, by rfl⟩ : syracuseStep 2051623 = 3077435) B3077435
theorem B2308081 : Blo 2051435 2308081 := bbase (se 2 (by rfl) ⟨865530, by rfl⟩ : syracuseStep 2308081 = 1731061) (by norm_num)
theorem B3077441 : Blo 2051435 3077441 := bstep (se 2 (by rfl) ⟨1154040, by rfl⟩ : syracuseStep 3077441 = 2308081) B2308081
theorem B2051627 : Blo 2051435 2051627 := bstep (se 1 (by rfl) ⟨1538720, by rfl⟩ : syracuseStep 2051627 = 3077441) B3077441
theorem B14037461 : Blo 2051435 14037461 := bbase (se 7 (by rfl) ⟨164501, by rfl⟩ : syracuseStep 14037461 = 329003) (by norm_num)
theorem B9358307 : Blo 2051435 9358307 := bstep (se 1 (by rfl) ⟨7018730, by rfl⟩ : syracuseStep 9358307 = 14037461) B14037461
theorem B6238871 : Blo 2051435 6238871 := bstep (se 1 (by rfl) ⟨4679153, by rfl⟩ : syracuseStep 6238871 = 9358307) B9358307
theorem B4159247 : Blo 2051435 4159247 := bstep (se 1 (by rfl) ⟨3119435, by rfl⟩ : syracuseStep 4159247 = 6238871) B6238871
theorem B11091325 : Blo 2051435 11091325 := bstep (se 3 (by rfl) ⟨2079623, by rfl⟩ : syracuseStep 11091325 = 4159247) B4159247
theorem B14788433 : Blo 2051435 14788433 := bstep (se 2 (by rfl) ⟨5545662, by rfl⟩ : syracuseStep 14788433 = 11091325) B11091325
theorem B9858955 : Blo 2051435 9858955 := bstep (se 1 (by rfl) ⟨7394216, by rfl⟩ : syracuseStep 9858955 = 14788433) B14788433
theorem B13145273 : Blo 2051435 13145273 := bstep (se 2 (by rfl) ⟨4929477, by rfl⟩ : syracuseStep 13145273 = 9858955) B9858955
theorem B8763515 : Blo 2051435 8763515 := bstep (se 1 (by rfl) ⟨6572636, by rfl⟩ : syracuseStep 8763515 = 13145273) B13145273
theorem B5842343 : Blo 2051435 5842343 := bstep (se 1 (by rfl) ⟨4381757, by rfl⟩ : syracuseStep 5842343 = 8763515) B8763515
theorem B3894895 : Blo 2051435 3894895 := bstep (se 1 (by rfl) ⟨2921171, by rfl⟩ : syracuseStep 3894895 = 5842343) B5842343
theorem B5193193 : Blo 2051435 5193193 := bstep (se 2 (by rfl) ⟨1947447, by rfl⟩ : syracuseStep 5193193 = 3894895) B3894895
theorem B6924257 : Blo 2051435 6924257 := bstep (se 2 (by rfl) ⟨2596596, by rfl⟩ : syracuseStep 6924257 = 5193193) B5193193
theorem B4616171 : Blo 2051435 4616171 := bstep (se 1 (by rfl) ⟨3462128, by rfl⟩ : syracuseStep 4616171 = 6924257) B6924257
theorem B3077447 : Blo 2051435 3077447 := bstep (se 1 (by rfl) ⟨2308085, by rfl⟩ : syracuseStep 3077447 = 4616171) B4616171
theorem B2051631 : Blo 2051435 2051631 := bstep (se 1 (by rfl) ⟨1538723, by rfl⟩ : syracuseStep 2051631 = 3077447) B3077447
theorem B3077453 : Blo 2051435 3077453 := bbase (se 3 (by rfl) ⟨577022, by rfl⟩ : syracuseStep 3077453 = 1154045) (by norm_num)
theorem B2051635 : Blo 2051435 2051635 := bstep (se 1 (by rfl) ⟨1538726, by rfl⟩ : syracuseStep 2051635 = 3077453) B3077453
theorem B4616189 : Blo 2051435 4616189 := bbase (se 3 (by rfl) ⟨865535, by rfl⟩ : syracuseStep 4616189 = 1731071) (by norm_num)
theorem B3077459 : Blo 2051435 3077459 := bstep (se 1 (by rfl) ⟨2308094, by rfl⟩ : syracuseStep 3077459 = 4616189) B4616189
theorem B2051639 : Blo 2051435 2051639 := bstep (se 1 (by rfl) ⟨1538729, by rfl⟩ : syracuseStep 2051639 = 3077459) B3077459
theorem B3462149 : Blo 2051435 3462149 := bbase (se 4 (by rfl) ⟨324576, by rfl⟩ : syracuseStep 3462149 = 649153) (by norm_num)
theorem B2308099 : Blo 2051435 2308099 := bstep (se 1 (by rfl) ⟨1731074, by rfl⟩ : syracuseStep 2308099 = 3462149) B3462149
theorem B3077465 : Blo 2051435 3077465 := bstep (se 2 (by rfl) ⟨1154049, by rfl⟩ : syracuseStep 3077465 = 2308099) B2308099
theorem B2051643 : Blo 2051435 2051643 := bstep (se 1 (by rfl) ⟨1538732, by rfl⟩ : syracuseStep 2051643 = 3077465) B3077465
theorem B15579701 : Blo 2051435 15579701 := bbase (se 5 (by rfl) ⟨730298, by rfl⟩ : syracuseStep 15579701 = 1460597) (by norm_num)
theorem B10386467 : Blo 2051435 10386467 := bstep (se 1 (by rfl) ⟨7789850, by rfl⟩ : syracuseStep 10386467 = 15579701) B15579701
theorem B6924311 : Blo 2051435 6924311 := bstep (se 1 (by rfl) ⟨5193233, by rfl⟩ : syracuseStep 6924311 = 10386467) B10386467
theorem B4616207 : Blo 2051435 4616207 := bstep (se 1 (by rfl) ⟨3462155, by rfl⟩ : syracuseStep 4616207 = 6924311) B6924311
theorem B3077471 : Blo 2051435 3077471 := bstep (se 1 (by rfl) ⟨2308103, by rfl⟩ : syracuseStep 3077471 = 4616207) B4616207
theorem B2051647 : Blo 2051435 2051647 := bstep (se 1 (by rfl) ⟨1538735, by rfl⟩ : syracuseStep 2051647 = 3077471) B3077471
theorem B3077477 : Blo 2051435 3077477 := bbase (se 4 (by rfl) ⟨288513, by rfl⟩ : syracuseStep 3077477 = 577027) (by norm_num)
theorem B2051651 : Blo 2051435 2051651 := bstep (se 1 (by rfl) ⟨1538738, by rfl⟩ : syracuseStep 2051651 = 3077477) B3077477
theorem B3894941 : Blo 2051435 3894941 := bbase (se 3 (by rfl) ⟨730301, by rfl⟩ : syracuseStep 3894941 = 1460603) (by norm_num)
theorem B2596627 : Blo 2051435 2596627 := bstep (se 1 (by rfl) ⟨1947470, by rfl⟩ : syracuseStep 2596627 = 3894941) B3894941
theorem B3462169 : Blo 2051435 3462169 := bstep (se 2 (by rfl) ⟨1298313, by rfl⟩ : syracuseStep 3462169 = 2596627) B2596627
theorem B4616225 : Blo 2051435 4616225 := bstep (se 2 (by rfl) ⟨1731084, by rfl⟩ : syracuseStep 4616225 = 3462169) B3462169
theorem B3077483 : Blo 2051435 3077483 := bstep (se 1 (by rfl) ⟨2308112, by rfl⟩ : syracuseStep 3077483 = 4616225) B4616225
theorem B2051655 : Blo 2051435 2051655 := bstep (se 1 (by rfl) ⟨1538741, by rfl⟩ : syracuseStep 2051655 = 3077483) B3077483
theorem B2308117 : Blo 2051435 2308117 := bbase (se 6 (by rfl) ⟨54096, by rfl⟩ : syracuseStep 2308117 = 108193) (by norm_num)
theorem B3077489 : Blo 2051435 3077489 := bstep (se 2 (by rfl) ⟨1154058, by rfl⟩ : syracuseStep 3077489 = 2308117) B2308117
theorem B2051659 : Blo 2051435 2051659 := bstep (se 1 (by rfl) ⟨1538744, by rfl⟩ : syracuseStep 2051659 = 3077489) B3077489
theorem B2596637 : Blo 2051435 2596637 := bbase (se 3 (by rfl) ⟨486869, by rfl⟩ : syracuseStep 2596637 = 973739) (by norm_num)
theorem B6924365 : Blo 2051435 6924365 := bstep (se 3 (by rfl) ⟨1298318, by rfl⟩ : syracuseStep 6924365 = 2596637) B2596637
theorem B4616243 : Blo 2051435 4616243 := bstep (se 1 (by rfl) ⟨3462182, by rfl⟩ : syracuseStep 4616243 = 6924365) B6924365
theorem B3077495 : Blo 2051435 3077495 := bstep (se 1 (by rfl) ⟨2308121, by rfl⟩ : syracuseStep 3077495 = 4616243) B4616243
theorem B2051663 : Blo 2051435 2051663 := bstep (se 1 (by rfl) ⟨1538747, by rfl⟩ : syracuseStep 2051663 = 3077495) B3077495
theorem B3077501 : Blo 2051435 3077501 := bbase (se 3 (by rfl) ⟨577031, by rfl⟩ : syracuseStep 3077501 = 1154063) (by norm_num)
theorem B2051667 : Blo 2051435 2051667 := bstep (se 1 (by rfl) ⟨1538750, by rfl⟩ : syracuseStep 2051667 = 3077501) B3077501
theorem B4616261 : Blo 2051435 4616261 := bbase (se 4 (by rfl) ⟨432774, by rfl⟩ : syracuseStep 4616261 = 865549) (by norm_num)
theorem B3077507 : Blo 2051435 3077507 := bstep (se 1 (by rfl) ⟨2308130, by rfl⟩ : syracuseStep 3077507 = 4616261) B4616261
theorem B2051671 : Blo 2051435 2051671 := bstep (se 1 (by rfl) ⟨1538753, by rfl⟩ : syracuseStep 2051671 = 3077507) B3077507
theorem B5842469 : Blo 2051435 5842469 := bbase (se 4 (by rfl) ⟨547731, by rfl⟩ : syracuseStep 5842469 = 1095463) (by norm_num)
theorem B3894979 : Blo 2051435 3894979 := bstep (se 1 (by rfl) ⟨2921234, by rfl⟩ : syracuseStep 3894979 = 5842469) B5842469
theorem B5193305 : Blo 2051435 5193305 := bstep (se 2 (by rfl) ⟨1947489, by rfl⟩ : syracuseStep 5193305 = 3894979) B3894979
theorem B3462203 : Blo 2051435 3462203 := bstep (se 1 (by rfl) ⟨2596652, by rfl⟩ : syracuseStep 3462203 = 5193305) B5193305
theorem B2308135 : Blo 2051435 2308135 := bstep (se 1 (by rfl) ⟨1731101, by rfl⟩ : syracuseStep 2308135 = 3462203) B3462203
theorem B3077513 : Blo 2051435 3077513 := bstep (se 2 (by rfl) ⟨1154067, by rfl⟩ : syracuseStep 3077513 = 2308135) B2308135
theorem B2051675 : Blo 2051435 2051675 := bstep (se 1 (by rfl) ⟨1538756, by rfl⟩ : syracuseStep 2051675 = 3077513) B3077513
theorem B10386629 : Blo 2051435 10386629 := bbase (se 4 (by rfl) ⟨973746, by rfl⟩ : syracuseStep 10386629 = 1947493) (by norm_num)
theorem B6924419 : Blo 2051435 6924419 := bstep (se 1 (by rfl) ⟨5193314, by rfl⟩ : syracuseStep 6924419 = 10386629) B10386629
theorem B4616279 : Blo 2051435 4616279 := bstep (se 1 (by rfl) ⟨3462209, by rfl⟩ : syracuseStep 4616279 = 6924419) B6924419
theorem B3077519 : Blo 2051435 3077519 := bstep (se 1 (by rfl) ⟨2308139, by rfl⟩ : syracuseStep 3077519 = 4616279) B4616279
theorem B2051679 : Blo 2051435 2051679 := bstep (se 1 (by rfl) ⟨1538759, by rfl⟩ : syracuseStep 2051679 = 3077519) B3077519
theorem B3077525 : Blo 2051435 3077525 := bbase (se 6 (by rfl) ⟨72129, by rfl⟩ : syracuseStep 3077525 = 144259) (by norm_num)
theorem B2051683 : Blo 2051435 2051683 := bstep (se 1 (by rfl) ⟨1538762, by rfl⟩ : syracuseStep 2051683 = 3077525) B3077525
theorem B4381877 : Blo 2051435 4381877 := bbase (se 5 (by rfl) ⟨205400, by rfl⟩ : syracuseStep 4381877 = 410801) (by norm_num)
theorem B11685005 : Blo 2051435 11685005 := bstep (se 3 (by rfl) ⟨2190938, by rfl⟩ : syracuseStep 11685005 = 4381877) B4381877
theorem B7790003 : Blo 2051435 7790003 := bstep (se 1 (by rfl) ⟨5842502, by rfl⟩ : syracuseStep 7790003 = 11685005) B11685005
theorem B5193335 : Blo 2051435 5193335 := bstep (se 1 (by rfl) ⟨3895001, by rfl⟩ : syracuseStep 5193335 = 7790003) B7790003
theorem B3462223 : Blo 2051435 3462223 := bstep (se 1 (by rfl) ⟨2596667, by rfl⟩ : syracuseStep 3462223 = 5193335) B5193335
theorem B4616297 : Blo 2051435 4616297 := bstep (se 2 (by rfl) ⟨1731111, by rfl⟩ : syracuseStep 4616297 = 3462223) B3462223
theorem B3077531 : Blo 2051435 3077531 := bstep (se 1 (by rfl) ⟨2308148, by rfl⟩ : syracuseStep 3077531 = 4616297) B4616297
theorem B2051687 : Blo 2051435 2051687 := bstep (se 1 (by rfl) ⟨1538765, by rfl⟩ : syracuseStep 2051687 = 3077531) B3077531
theorem B2308153 : Blo 2051435 2308153 := bbase (se 2 (by rfl) ⟨865557, by rfl⟩ : syracuseStep 2308153 = 1731115) (by norm_num)
theorem B3077537 : Blo 2051435 3077537 := bstep (se 2 (by rfl) ⟨1154076, by rfl⟩ : syracuseStep 3077537 = 2308153) B2308153
theorem B2051691 : Blo 2051435 2051691 := bstep (se 1 (by rfl) ⟨1538768, by rfl⟩ : syracuseStep 2051691 = 3077537) B3077537
theorem B3286421 : Blo 2051435 3286421 := bbase (se 6 (by rfl) ⟨77025, by rfl⟩ : syracuseStep 3286421 = 154051) (by norm_num)
theorem B2190947 : Blo 2051435 2190947 := bstep (se 1 (by rfl) ⟨1643210, by rfl⟩ : syracuseStep 2190947 = 3286421) B3286421
theorem B5842525 : Blo 2051435 5842525 := bstep (se 3 (by rfl) ⟨1095473, by rfl⟩ : syracuseStep 5842525 = 2190947) B2190947
theorem B7790033 : Blo 2051435 7790033 := bstep (se 2 (by rfl) ⟨2921262, by rfl⟩ : syracuseStep 7790033 = 5842525) B5842525
theorem B5193355 : Blo 2051435 5193355 := bstep (se 1 (by rfl) ⟨3895016, by rfl⟩ : syracuseStep 5193355 = 7790033) B7790033
theorem B6924473 : Blo 2051435 6924473 := bstep (se 2 (by rfl) ⟨2596677, by rfl⟩ : syracuseStep 6924473 = 5193355) B5193355
theorem B4616315 : Blo 2051435 4616315 := bstep (se 1 (by rfl) ⟨3462236, by rfl⟩ : syracuseStep 4616315 = 6924473) B6924473
theorem B3077543 : Blo 2051435 3077543 := bstep (se 1 (by rfl) ⟨2308157, by rfl⟩ : syracuseStep 3077543 = 4616315) B4616315
theorem B2051695 : Blo 2051435 2051695 := bstep (se 1 (by rfl) ⟨1538771, by rfl⟩ : syracuseStep 2051695 = 3077543) B3077543
theorem B3077549 : Blo 2051435 3077549 := bbase (se 3 (by rfl) ⟨577040, by rfl⟩ : syracuseStep 3077549 = 1154081) (by norm_num)
theorem B2051699 : Blo 2051435 2051699 := bstep (se 1 (by rfl) ⟨1538774, by rfl⟩ : syracuseStep 2051699 = 3077549) B3077549
theorem B4616333 : Blo 2051435 4616333 := bbase (se 3 (by rfl) ⟨865562, by rfl⟩ : syracuseStep 4616333 = 1731125) (by norm_num)
theorem B3077555 : Blo 2051435 3077555 := bstep (se 1 (by rfl) ⟨2308166, by rfl⟩ : syracuseStep 3077555 = 4616333) B4616333
theorem B2051703 : Blo 2051435 2051703 := bstep (se 1 (by rfl) ⟨1538777, by rfl⟩ : syracuseStep 2051703 = 3077555) B3077555
theorem B2596693 : Blo 2051435 2596693 := bbase (se 9 (by rfl) ⟨7607, by rfl⟩ : syracuseStep 2596693 = 15215) (by norm_num)
theorem B3462257 : Blo 2051435 3462257 := bstep (se 2 (by rfl) ⟨1298346, by rfl⟩ : syracuseStep 3462257 = 2596693) B2596693
theorem B2308171 : Blo 2051435 2308171 := bstep (se 1 (by rfl) ⟨1731128, by rfl⟩ : syracuseStep 2308171 = 3462257) B3462257
theorem B3077561 : Blo 2051435 3077561 := bstep (se 2 (by rfl) ⟨1154085, by rfl⟩ : syracuseStep 3077561 = 2308171) B2308171
theorem B2051707 : Blo 2051435 2051707 := bstep (se 1 (by rfl) ⟨1538780, by rfl⟩ : syracuseStep 2051707 = 3077561) B3077561
theorem B2251157 : Blo 2051435 2251157 := bbase (se 6 (by rfl) ⟨52761, by rfl⟩ : syracuseStep 2251157 = 105523) (by norm_num)
theorem B6003085 : Blo 2051435 6003085 := bstep (se 3 (by rfl) ⟨1125578, by rfl⟩ : syracuseStep 6003085 = 2251157) B2251157
theorem B8004113 : Blo 2051435 8004113 := bstep (se 2 (by rfl) ⟨3001542, by rfl⟩ : syracuseStep 8004113 = 6003085) B6003085
theorem B5336075 : Blo 2051435 5336075 := bstep (se 1 (by rfl) ⟨4002056, by rfl⟩ : syracuseStep 5336075 = 8004113) B8004113
theorem B14229533 : Blo 2051435 14229533 := bstep (se 3 (by rfl) ⟨2668037, by rfl⟩ : syracuseStep 14229533 = 5336075) B5336075
theorem B37945421 : Blo 2051435 37945421 := bstep (se 3 (by rfl) ⟨7114766, by rfl⟩ : syracuseStep 37945421 = 14229533) B14229533
theorem B25296947 : Blo 2051435 25296947 := bstep (se 1 (by rfl) ⟨18972710, by rfl⟩ : syracuseStep 25296947 = 37945421) B37945421
theorem B16864631 : Blo 2051435 16864631 := bstep (se 1 (by rfl) ⟨12648473, by rfl⟩ : syracuseStep 16864631 = 25296947) B25296947
theorem B11243087 : Blo 2051435 11243087 := bstep (se 1 (by rfl) ⟨8432315, by rfl⟩ : syracuseStep 11243087 = 16864631) B16864631
theorem B7495391 : Blo 2051435 7495391 := bstep (se 1 (by rfl) ⟨5621543, by rfl⟩ : syracuseStep 7495391 = 11243087) B11243087
theorem B4996927 : Blo 2051435 4996927 := bstep (se 1 (by rfl) ⟨3747695, by rfl⟩ : syracuseStep 4996927 = 7495391) B7495391
theorem B6662569 : Blo 2051435 6662569 := bstep (se 2 (by rfl) ⟨2498463, by rfl⟩ : syracuseStep 6662569 = 4996927) B4996927
theorem B8883425 : Blo 2051435 8883425 := bstep (se 2 (by rfl) ⟨3331284, by rfl⟩ : syracuseStep 8883425 = 6662569) B6662569
theorem B5922283 : Blo 2051435 5922283 := bstep (se 1 (by rfl) ⟨4441712, by rfl⟩ : syracuseStep 5922283 = 8883425) B8883425
theorem B7896377 : Blo 2051435 7896377 := bstep (se 2 (by rfl) ⟨2961141, by rfl⟩ : syracuseStep 7896377 = 5922283) B5922283
theorem B21057005 : Blo 2051435 21057005 := bstep (se 3 (by rfl) ⟨3948188, by rfl⟩ : syracuseStep 21057005 = 7896377) B7896377
theorem B14038003 : Blo 2051435 14038003 := bstep (se 1 (by rfl) ⟨10528502, by rfl⟩ : syracuseStep 14038003 = 21057005) B21057005
theorem B18717337 : Blo 2051435 18717337 := bstep (se 2 (by rfl) ⟨7019001, by rfl⟩ : syracuseStep 18717337 = 14038003) B14038003
theorem B99825797 : Blo 2051435 99825797 := bstep (se 4 (by rfl) ⟨9358668, by rfl⟩ : syracuseStep 99825797 = 18717337) B18717337
theorem B66550531 : Blo 2051435 66550531 := bstep (se 1 (by rfl) ⟨49912898, by rfl⟩ : syracuseStep 66550531 = 99825797) B99825797
theorem B88734041 : Blo 2051435 88734041 := bstep (se 2 (by rfl) ⟨33275265, by rfl⟩ : syracuseStep 88734041 = 66550531) B66550531
theorem B59156027 : Blo 2051435 59156027 := bstep (se 1 (by rfl) ⟨44367020, by rfl⟩ : syracuseStep 59156027 = 88734041) B88734041
theorem B39437351 : Blo 2051435 39437351 := bstep (se 1 (by rfl) ⟨29578013, by rfl⟩ : syracuseStep 39437351 = 59156027) B59156027
theorem B26291567 : Blo 2051435 26291567 := bstep (se 1 (by rfl) ⟨19718675, by rfl⟩ : syracuseStep 26291567 = 39437351) B39437351
theorem B17527711 : Blo 2051435 17527711 := bstep (se 1 (by rfl) ⟨13145783, by rfl⟩ : syracuseStep 17527711 = 26291567) B26291567
theorem B23370281 : Blo 2051435 23370281 := bstep (se 2 (by rfl) ⟨8763855, by rfl⟩ : syracuseStep 23370281 = 17527711) B17527711
theorem B15580187 : Blo 2051435 15580187 := bstep (se 1 (by rfl) ⟨11685140, by rfl⟩ : syracuseStep 15580187 = 23370281) B23370281
theorem B10386791 : Blo 2051435 10386791 := bstep (se 1 (by rfl) ⟨7790093, by rfl⟩ : syracuseStep 10386791 = 15580187) B15580187
theorem B6924527 : Blo 2051435 6924527 := bstep (se 1 (by rfl) ⟨5193395, by rfl⟩ : syracuseStep 6924527 = 10386791) B10386791
theorem B4616351 : Blo 2051435 4616351 := bstep (se 1 (by rfl) ⟨3462263, by rfl⟩ : syracuseStep 4616351 = 6924527) B6924527
theorem B3077567 : Blo 2051435 3077567 := bstep (se 1 (by rfl) ⟨2308175, by rfl⟩ : syracuseStep 3077567 = 4616351) B4616351
theorem B2051711 : Blo 2051435 2051711 := bstep (se 1 (by rfl) ⟨1538783, by rfl⟩ : syracuseStep 2051711 = 3077567) B3077567
theorem B3077573 : Blo 2051435 3077573 := bbase (se 4 (by rfl) ⟨288522, by rfl⟩ : syracuseStep 3077573 = 577045) (by norm_num)
theorem B2051715 : Blo 2051435 2051715 := bstep (se 1 (by rfl) ⟨1538786, by rfl⟩ : syracuseStep 2051715 = 3077573) B3077573
theorem B3462277 : Blo 2051435 3462277 := bbase (se 4 (by rfl) ⟨324588, by rfl⟩ : syracuseStep 3462277 = 649177) (by norm_num)
theorem B4616369 : Blo 2051435 4616369 := bstep (se 2 (by rfl) ⟨1731138, by rfl⟩ : syracuseStep 4616369 = 3462277) B3462277
theorem B3077579 : Blo 2051435 3077579 := bstep (se 1 (by rfl) ⟨2308184, by rfl⟩ : syracuseStep 3077579 = 4616369) B4616369
theorem B2051719 : Blo 2051435 2051719 := bstep (se 1 (by rfl) ⟨1538789, by rfl⟩ : syracuseStep 2051719 = 3077579) B3077579
theorem B2308189 : Blo 2051435 2308189 := bbase (se 3 (by rfl) ⟨432785, by rfl⟩ : syracuseStep 2308189 = 865571) (by norm_num)
theorem B3077585 : Blo 2051435 3077585 := bstep (se 2 (by rfl) ⟨1154094, by rfl⟩ : syracuseStep 3077585 = 2308189) B2308189
theorem B2051723 : Blo 2051435 2051723 := bstep (se 1 (by rfl) ⟨1538792, by rfl⟩ : syracuseStep 2051723 = 3077585) B3077585
theorem B6924581 : Blo 2051435 6924581 := bbase (se 4 (by rfl) ⟨649179, by rfl⟩ : syracuseStep 6924581 = 1298359) (by norm_num)
theorem B4616387 : Blo 2051435 4616387 := bstep (se 1 (by rfl) ⟨3462290, by rfl⟩ : syracuseStep 4616387 = 6924581) B6924581
theorem B3077591 : Blo 2051435 3077591 := bstep (se 1 (by rfl) ⟨2308193, by rfl⟩ : syracuseStep 3077591 = 4616387) B4616387
theorem B2051727 : Blo 2051435 2051727 := bstep (se 1 (by rfl) ⟨1538795, by rfl⟩ : syracuseStep 2051727 = 3077591) B3077591
theorem B3077597 : Blo 2051435 3077597 := bbase (se 3 (by rfl) ⟨577049, by rfl⟩ : syracuseStep 3077597 = 1154099) (by norm_num)
theorem B2051731 : Blo 2051435 2051731 := bstep (se 1 (by rfl) ⟨1538798, by rfl⟩ : syracuseStep 2051731 = 3077597) B3077597
theorem B4616405 : Blo 2051435 4616405 := bbase (se 7 (by rfl) ⟨54098, by rfl⟩ : syracuseStep 4616405 = 108197) (by norm_num)
theorem B3077603 : Blo 2051435 3077603 := bstep (se 1 (by rfl) ⟨2308202, by rfl⟩ : syracuseStep 3077603 = 4616405) B4616405
theorem B2051735 : Blo 2051435 2051735 := bstep (se 1 (by rfl) ⟨1538801, by rfl⟩ : syracuseStep 2051735 = 3077603) B3077603
theorem B8318933 : Blo 2051435 8318933 := bbase (se 7 (by rfl) ⟨97487, by rfl⟩ : syracuseStep 8318933 = 194975) (by norm_num)
theorem B5545955 : Blo 2051435 5545955 := bstep (se 1 (by rfl) ⟨4159466, by rfl⟩ : syracuseStep 5545955 = 8318933) B8318933
theorem B14789213 : Blo 2051435 14789213 := bstep (se 3 (by rfl) ⟨2772977, by rfl⟩ : syracuseStep 14789213 = 5545955) B5545955
theorem B9859475 : Blo 2051435 9859475 := bstep (se 1 (by rfl) ⟨7394606, by rfl⟩ : syracuseStep 9859475 = 14789213) B14789213
theorem B6572983 : Blo 2051435 6572983 := bstep (se 1 (by rfl) ⟨4929737, by rfl⟩ : syracuseStep 6572983 = 9859475) B9859475
theorem B8763977 : Blo 2051435 8763977 := bstep (se 2 (by rfl) ⟨3286491, by rfl⟩ : syracuseStep 8763977 = 6572983) B6572983
theorem B5842651 : Blo 2051435 5842651 := bstep (se 1 (by rfl) ⟨4381988, by rfl⟩ : syracuseStep 5842651 = 8763977) B8763977
theorem B7790201 : Blo 2051435 7790201 := bstep (se 2 (by rfl) ⟨2921325, by rfl⟩ : syracuseStep 7790201 = 5842651) B5842651
theorem B5193467 : Blo 2051435 5193467 := bstep (se 1 (by rfl) ⟨3895100, by rfl⟩ : syracuseStep 5193467 = 7790201) B7790201
theorem B3462311 : Blo 2051435 3462311 := bstep (se 1 (by rfl) ⟨2596733, by rfl⟩ : syracuseStep 3462311 = 5193467) B5193467
theorem B2308207 : Blo 2051435 2308207 := bstep (se 1 (by rfl) ⟨1731155, by rfl⟩ : syracuseStep 2308207 = 3462311) B3462311
theorem B3077609 : Blo 2051435 3077609 := bstep (se 2 (by rfl) ⟨1154103, by rfl⟩ : syracuseStep 3077609 = 2308207) B2308207
theorem B2051739 : Blo 2051435 2051739 := bstep (se 1 (by rfl) ⟨1538804, by rfl⟩ : syracuseStep 2051739 = 3077609) B3077609
theorem B2464873 : Blo 2051435 2464873 := bbase (se 2 (by rfl) ⟨924327, by rfl⟩ : syracuseStep 2464873 = 1848655) (by norm_num)
theorem B13145989 : Blo 2051435 13145989 := bstep (se 4 (by rfl) ⟨1232436, by rfl⟩ : syracuseStep 13145989 = 2464873) B2464873
theorem B17527985 : Blo 2051435 17527985 := bstep (se 2 (by rfl) ⟨6572994, by rfl⟩ : syracuseStep 17527985 = 13145989) B13145989
theorem B11685323 : Blo 2051435 11685323 := bstep (se 1 (by rfl) ⟨8763992, by rfl⟩ : syracuseStep 11685323 = 17527985) B17527985
theorem B7790215 : Blo 2051435 7790215 := bstep (se 1 (by rfl) ⟨5842661, by rfl⟩ : syracuseStep 7790215 = 11685323) B11685323
theorem B10386953 : Blo 2051435 10386953 := bstep (se 2 (by rfl) ⟨3895107, by rfl⟩ : syracuseStep 10386953 = 7790215) B7790215
theorem B6924635 : Blo 2051435 6924635 := bstep (se 1 (by rfl) ⟨5193476, by rfl⟩ : syracuseStep 6924635 = 10386953) B10386953
theorem B4616423 : Blo 2051435 4616423 := bstep (se 1 (by rfl) ⟨3462317, by rfl⟩ : syracuseStep 4616423 = 6924635) B6924635
theorem B3077615 : Blo 2051435 3077615 := bstep (se 1 (by rfl) ⟨2308211, by rfl⟩ : syracuseStep 3077615 = 4616423) B4616423
theorem B2051743 : Blo 2051435 2051743 := bstep (se 1 (by rfl) ⟨1538807, by rfl⟩ : syracuseStep 2051743 = 3077615) B3077615
theorem B3077621 : Blo 2051435 3077621 := bbase (se 5 (by rfl) ⟨144263, by rfl⟩ : syracuseStep 3077621 = 288527) (by norm_num)
theorem B2051747 : Blo 2051435 2051747 := bstep (se 1 (by rfl) ⟨1538810, by rfl⟩ : syracuseStep 2051747 = 3077621) B3077621
theorem B5264357 : Blo 2051435 5264357 := bbase (se 4 (by rfl) ⟨493533, by rfl⟩ : syracuseStep 5264357 = 987067) (by norm_num)
theorem B14038285 : Blo 2051435 14038285 := bstep (se 3 (by rfl) ⟨2632178, by rfl⟩ : syracuseStep 14038285 = 5264357) B5264357
theorem B18717713 : Blo 2051435 18717713 := bstep (se 2 (by rfl) ⟨7019142, by rfl⟩ : syracuseStep 18717713 = 14038285) B14038285
theorem B12478475 : Blo 2051435 12478475 := bstep (se 1 (by rfl) ⟨9358856, by rfl⟩ : syracuseStep 12478475 = 18717713) B18717713
theorem B8318983 : Blo 2051435 8318983 := bstep (se 1 (by rfl) ⟨6239237, by rfl⟩ : syracuseStep 8318983 = 12478475) B12478475
theorem B11091977 : Blo 2051435 11091977 := bstep (se 2 (by rfl) ⟨4159491, by rfl⟩ : syracuseStep 11091977 = 8318983) B8318983
theorem B7394651 : Blo 2051435 7394651 := bstep (se 1 (by rfl) ⟨5545988, by rfl⟩ : syracuseStep 7394651 = 11091977) B11091977
theorem B4929767 : Blo 2051435 4929767 := bstep (se 1 (by rfl) ⟨3697325, by rfl⟩ : syracuseStep 4929767 = 7394651) B7394651
theorem B3286511 : Blo 2051435 3286511 := bstep (se 1 (by rfl) ⟨2464883, by rfl⟩ : syracuseStep 3286511 = 4929767) B4929767
theorem B2191007 : Blo 2051435 2191007 := bstep (se 1 (by rfl) ⟨1643255, by rfl⟩ : syracuseStep 2191007 = 3286511) B3286511
theorem B5842685 : Blo 2051435 5842685 := bstep (se 3 (by rfl) ⟨1095503, by rfl⟩ : syracuseStep 5842685 = 2191007) B2191007
theorem B3895123 : Blo 2051435 3895123 := bstep (se 1 (by rfl) ⟨2921342, by rfl⟩ : syracuseStep 3895123 = 5842685) B5842685
theorem B5193497 : Blo 2051435 5193497 := bstep (se 2 (by rfl) ⟨1947561, by rfl⟩ : syracuseStep 5193497 = 3895123) B3895123
theorem B3462331 : Blo 2051435 3462331 := bstep (se 1 (by rfl) ⟨2596748, by rfl⟩ : syracuseStep 3462331 = 5193497) B5193497
theorem B4616441 : Blo 2051435 4616441 := bstep (se 2 (by rfl) ⟨1731165, by rfl⟩ : syracuseStep 4616441 = 3462331) B3462331
theorem B3077627 : Blo 2051435 3077627 := bstep (se 1 (by rfl) ⟨2308220, by rfl⟩ : syracuseStep 3077627 = 4616441) B4616441
theorem B2051751 : Blo 2051435 2051751 := bstep (se 1 (by rfl) ⟨1538813, by rfl⟩ : syracuseStep 2051751 = 3077627) B3077627
theorem B2308225 : Blo 2051435 2308225 := bbase (se 2 (by rfl) ⟨865584, by rfl⟩ : syracuseStep 2308225 = 1731169) (by norm_num)
theorem B3077633 : Blo 2051435 3077633 := bstep (se 2 (by rfl) ⟨1154112, by rfl⟩ : syracuseStep 3077633 = 2308225) B2308225
theorem B2051755 : Blo 2051435 2051755 := bstep (se 1 (by rfl) ⟨1538816, by rfl⟩ : syracuseStep 2051755 = 3077633) B3077633
theorem B5193517 : Blo 2051435 5193517 := bbase (se 3 (by rfl) ⟨973784, by rfl⟩ : syracuseStep 5193517 = 1947569) (by norm_num)
theorem B6924689 : Blo 2051435 6924689 := bstep (se 2 (by rfl) ⟨2596758, by rfl⟩ : syracuseStep 6924689 = 5193517) B5193517
theorem B4616459 : Blo 2051435 4616459 := bstep (se 1 (by rfl) ⟨3462344, by rfl⟩ : syracuseStep 4616459 = 6924689) B6924689
theorem B3077639 : Blo 2051435 3077639 := bstep (se 1 (by rfl) ⟨2308229, by rfl⟩ : syracuseStep 3077639 = 4616459) B4616459
theorem B2051759 : Blo 2051435 2051759 := bstep (se 1 (by rfl) ⟨1538819, by rfl⟩ : syracuseStep 2051759 = 3077639) B3077639
theorem B3077645 : Blo 2051435 3077645 := bbase (se 3 (by rfl) ⟨577058, by rfl⟩ : syracuseStep 3077645 = 1154117) (by norm_num)
theorem B2051763 : Blo 2051435 2051763 := bstep (se 1 (by rfl) ⟨1538822, by rfl⟩ : syracuseStep 2051763 = 3077645) B3077645
theorem B4616477 : Blo 2051435 4616477 := bbase (se 3 (by rfl) ⟨865589, by rfl⟩ : syracuseStep 4616477 = 1731179) (by norm_num)
theorem B3077651 : Blo 2051435 3077651 := bstep (se 1 (by rfl) ⟨2308238, by rfl⟩ : syracuseStep 3077651 = 4616477) B4616477
theorem B2051767 : Blo 2051435 2051767 := bstep (se 1 (by rfl) ⟨1538825, by rfl⟩ : syracuseStep 2051767 = 3077651) B3077651
theorem B3462365 : Blo 2051435 3462365 := bbase (se 3 (by rfl) ⟨649193, by rfl⟩ : syracuseStep 3462365 = 1298387) (by norm_num)
theorem B2308243 : Blo 2051435 2308243 := bstep (se 1 (by rfl) ⟨1731182, by rfl⟩ : syracuseStep 2308243 = 3462365) B3462365
theorem B3077657 : Blo 2051435 3077657 := bstep (se 2 (by rfl) ⟨1154121, by rfl⟩ : syracuseStep 3077657 = 2308243) B2308243
theorem B2051771 : Blo 2051435 2051771 := bstep (se 1 (by rfl) ⟨1538828, by rfl⟩ : syracuseStep 2051771 = 3077657) B3077657
theorem B4441853 : Blo 2051435 4441853 := bbase (se 3 (by rfl) ⟨832847, by rfl⟩ : syracuseStep 4441853 = 1665695) (by norm_num)
theorem B2961235 : Blo 2051435 2961235 := bstep (se 1 (by rfl) ⟨2220926, by rfl⟩ : syracuseStep 2961235 = 4441853) B4441853
theorem B3948313 : Blo 2051435 3948313 := bstep (se 2 (by rfl) ⟨1480617, by rfl⟩ : syracuseStep 3948313 = 2961235) B2961235
theorem B5264417 : Blo 2051435 5264417 := bstep (se 2 (by rfl) ⟨1974156, by rfl⟩ : syracuseStep 5264417 = 3948313) B3948313
theorem B3509611 : Blo 2051435 3509611 := bstep (se 1 (by rfl) ⟨2632208, by rfl⟩ : syracuseStep 3509611 = 5264417) B5264417
theorem B18717925 : Blo 2051435 18717925 := bstep (se 4 (by rfl) ⟨1754805, by rfl⟩ : syracuseStep 18717925 = 3509611) B3509611
theorem B24957233 : Blo 2051435 24957233 := bstep (se 2 (by rfl) ⟨9358962, by rfl⟩ : syracuseStep 24957233 = 18717925) B18717925
theorem B16638155 : Blo 2051435 16638155 := bstep (se 1 (by rfl) ⟨12478616, by rfl⟩ : syracuseStep 16638155 = 24957233) B24957233
theorem B11092103 : Blo 2051435 11092103 := bstep (se 1 (by rfl) ⟨8319077, by rfl⟩ : syracuseStep 11092103 = 16638155) B16638155
theorem B7394735 : Blo 2051435 7394735 := bstep (se 1 (by rfl) ⟨5546051, by rfl⟩ : syracuseStep 7394735 = 11092103) B11092103
theorem B4929823 : Blo 2051435 4929823 := bstep (se 1 (by rfl) ⟨3697367, by rfl⟩ : syracuseStep 4929823 = 7394735) B7394735
theorem B6573097 : Blo 2051435 6573097 := bstep (se 2 (by rfl) ⟨2464911, by rfl⟩ : syracuseStep 6573097 = 4929823) B4929823
theorem B8764129 : Blo 2051435 8764129 := bstep (se 2 (by rfl) ⟨3286548, by rfl⟩ : syracuseStep 8764129 = 6573097) B6573097
theorem B11685505 : Blo 2051435 11685505 := bstep (se 2 (by rfl) ⟨4382064, by rfl⟩ : syracuseStep 11685505 = 8764129) B8764129
theorem B15580673 : Blo 2051435 15580673 := bstep (se 2 (by rfl) ⟨5842752, by rfl⟩ : syracuseStep 15580673 = 11685505) B11685505
theorem B10387115 : Blo 2051435 10387115 := bstep (se 1 (by rfl) ⟨7790336, by rfl⟩ : syracuseStep 10387115 = 15580673) B15580673
theorem B6924743 : Blo 2051435 6924743 := bstep (se 1 (by rfl) ⟨5193557, by rfl⟩ : syracuseStep 6924743 = 10387115) B10387115
theorem B4616495 : Blo 2051435 4616495 := bstep (se 1 (by rfl) ⟨3462371, by rfl⟩ : syracuseStep 4616495 = 6924743) B6924743
theorem B3077663 : Blo 2051435 3077663 := bstep (se 1 (by rfl) ⟨2308247, by rfl⟩ : syracuseStep 3077663 = 4616495) B4616495
theorem B2051775 : Blo 2051435 2051775 := bstep (se 1 (by rfl) ⟨1538831, by rfl⟩ : syracuseStep 2051775 = 3077663) B3077663
theorem B3077669 : Blo 2051435 3077669 := bbase (se 4 (by rfl) ⟨288531, by rfl⟩ : syracuseStep 3077669 = 577063) (by norm_num)
theorem B2051779 : Blo 2051435 2051779 := bstep (se 1 (by rfl) ⟨1538834, by rfl⟩ : syracuseStep 2051779 = 3077669) B3077669
theorem B2596789 : Blo 2051435 2596789 := bbase (se 5 (by rfl) ⟨121724, by rfl⟩ : syracuseStep 2596789 = 243449) (by norm_num)
theorem B3462385 : Blo 2051435 3462385 := bstep (se 2 (by rfl) ⟨1298394, by rfl⟩ : syracuseStep 3462385 = 2596789) B2596789
theorem B4616513 : Blo 2051435 4616513 := bstep (se 2 (by rfl) ⟨1731192, by rfl⟩ : syracuseStep 4616513 = 3462385) B3462385
theorem B3077675 : Blo 2051435 3077675 := bstep (se 1 (by rfl) ⟨2308256, by rfl⟩ : syracuseStep 3077675 = 4616513) B4616513
theorem B2051783 : Blo 2051435 2051783 := bstep (se 1 (by rfl) ⟨1538837, by rfl⟩ : syracuseStep 2051783 = 3077675) B3077675
theorem B2308261 : Blo 2051435 2308261 := bbase (se 4 (by rfl) ⟨216399, by rfl⟩ : syracuseStep 2308261 = 432799) (by norm_num)
theorem B3077681 : Blo 2051435 3077681 := bstep (se 2 (by rfl) ⟨1154130, by rfl⟩ : syracuseStep 3077681 = 2308261) B2308261
theorem B2051787 : Blo 2051435 2051787 := bstep (se 1 (by rfl) ⟨1538840, by rfl⟩ : syracuseStep 2051787 = 3077681) B3077681
theorem B8432645 : Blo 2051435 8432645 := bbase (se 4 (by rfl) ⟨790560, by rfl⟩ : syracuseStep 8432645 = 1581121) (by norm_num)
theorem B22487053 : Blo 2051435 22487053 := bstep (se 3 (by rfl) ⟨4216322, by rfl⟩ : syracuseStep 22487053 = 8432645) B8432645
theorem B29982737 : Blo 2051435 29982737 := bstep (se 2 (by rfl) ⟨11243526, by rfl⟩ : syracuseStep 29982737 = 22487053) B22487053
theorem B79953965 : Blo 2051435 79953965 := bstep (se 3 (by rfl) ⟨14991368, by rfl⟩ : syracuseStep 79953965 = 29982737) B29982737
theorem B53302643 : Blo 2051435 53302643 := bstep (se 1 (by rfl) ⟨39976982, by rfl⟩ : syracuseStep 53302643 = 79953965) B79953965
theorem B35535095 : Blo 2051435 35535095 := bstep (se 1 (by rfl) ⟨26651321, by rfl⟩ : syracuseStep 35535095 = 53302643) B53302643
theorem B23690063 : Blo 2051435 23690063 := bstep (se 1 (by rfl) ⟨17767547, by rfl⟩ : syracuseStep 23690063 = 35535095) B35535095
theorem B15793375 : Blo 2051435 15793375 := bstep (se 1 (by rfl) ⟨11845031, by rfl⟩ : syracuseStep 15793375 = 23690063) B23690063
theorem B21057833 : Blo 2051435 21057833 := bstep (se 2 (by rfl) ⟨7896687, by rfl⟩ : syracuseStep 21057833 = 15793375) B15793375
theorem B14038555 : Blo 2051435 14038555 := bstep (se 1 (by rfl) ⟨10528916, by rfl⟩ : syracuseStep 14038555 = 21057833) B21057833
theorem B18718073 : Blo 2051435 18718073 := bstep (se 2 (by rfl) ⟨7019277, by rfl⟩ : syracuseStep 18718073 = 14038555) B14038555
theorem B12478715 : Blo 2051435 12478715 := bstep (se 1 (by rfl) ⟨9359036, by rfl⟩ : syracuseStep 12478715 = 18718073) B18718073
theorem B8319143 : Blo 2051435 8319143 := bstep (se 1 (by rfl) ⟨6239357, by rfl⟩ : syracuseStep 8319143 = 12478715) B12478715
theorem B22184381 : Blo 2051435 22184381 := bstep (se 3 (by rfl) ⟨4159571, by rfl⟩ : syracuseStep 22184381 = 8319143) B8319143
theorem B14789587 : Blo 2051435 14789587 := bstep (se 1 (by rfl) ⟨11092190, by rfl⟩ : syracuseStep 14789587 = 22184381) B22184381
theorem B19719449 : Blo 2051435 19719449 := bstep (se 2 (by rfl) ⟨7394793, by rfl⟩ : syracuseStep 19719449 = 14789587) B14789587
theorem B13146299 : Blo 2051435 13146299 := bstep (se 1 (by rfl) ⟨9859724, by rfl⟩ : syracuseStep 13146299 = 19719449) B19719449
theorem B8764199 : Blo 2051435 8764199 := bstep (se 1 (by rfl) ⟨6573149, by rfl⟩ : syracuseStep 8764199 = 13146299) B13146299
theorem B5842799 : Blo 2051435 5842799 := bstep (se 1 (by rfl) ⟨4382099, by rfl⟩ : syracuseStep 5842799 = 8764199) B8764199
theorem B3895199 : Blo 2051435 3895199 := bstep (se 1 (by rfl) ⟨2921399, by rfl⟩ : syracuseStep 3895199 = 5842799) B5842799
theorem B2596799 : Blo 2051435 2596799 := bstep (se 1 (by rfl) ⟨1947599, by rfl⟩ : syracuseStep 2596799 = 3895199) B3895199
theorem B6924797 : Blo 2051435 6924797 := bstep (se 3 (by rfl) ⟨1298399, by rfl⟩ : syracuseStep 6924797 = 2596799) B2596799
theorem B4616531 : Blo 2051435 4616531 := bstep (se 1 (by rfl) ⟨3462398, by rfl⟩ : syracuseStep 4616531 = 6924797) B6924797
theorem B3077687 : Blo 2051435 3077687 := bstep (se 1 (by rfl) ⟨2308265, by rfl⟩ : syracuseStep 3077687 = 4616531) B4616531
theorem B2051791 : Blo 2051435 2051791 := bstep (se 1 (by rfl) ⟨1538843, by rfl⟩ : syracuseStep 2051791 = 3077687) B3077687
theorem B3077693 : Blo 2051435 3077693 := bbase (se 3 (by rfl) ⟨577067, by rfl⟩ : syracuseStep 3077693 = 1154135) (by norm_num)
theorem B2051795 : Blo 2051435 2051795 := bstep (se 1 (by rfl) ⟨1538846, by rfl⟩ : syracuseStep 2051795 = 3077693) B3077693
theorem B4616549 : Blo 2051435 4616549 := bbase (se 4 (by rfl) ⟨432801, by rfl⟩ : syracuseStep 4616549 = 865603) (by norm_num)
theorem B3077699 : Blo 2051435 3077699 := bstep (se 1 (by rfl) ⟨2308274, by rfl⟩ : syracuseStep 3077699 = 4616549) B4616549
theorem B2051799 : Blo 2051435 2051799 := bstep (se 1 (by rfl) ⟨1538849, by rfl⟩ : syracuseStep 2051799 = 3077699) B3077699
theorem B5193629 : Blo 2051435 5193629 := bbase (se 3 (by rfl) ⟨973805, by rfl⟩ : syracuseStep 5193629 = 1947611) (by norm_num)
theorem B3462419 : Blo 2051435 3462419 := bstep (se 1 (by rfl) ⟨2596814, by rfl⟩ : syracuseStep 3462419 = 5193629) B5193629
theorem B2308279 : Blo 2051435 2308279 := bstep (se 1 (by rfl) ⟨1731209, by rfl⟩ : syracuseStep 2308279 = 3462419) B3462419
theorem B3077705 : Blo 2051435 3077705 := bstep (se 2 (by rfl) ⟨1154139, by rfl⟩ : syracuseStep 3077705 = 2308279) B2308279
theorem B2051803 : Blo 2051435 2051803 := bstep (se 1 (by rfl) ⟨1538852, by rfl⟩ : syracuseStep 2051803 = 3077705) B3077705
theorem B3895229 : Blo 2051435 3895229 := bbase (se 3 (by rfl) ⟨730355, by rfl⟩ : syracuseStep 3895229 = 1460711) (by norm_num)
theorem B10387277 : Blo 2051435 10387277 := bstep (se 3 (by rfl) ⟨1947614, by rfl⟩ : syracuseStep 10387277 = 3895229) B3895229
theorem B6924851 : Blo 2051435 6924851 := bstep (se 1 (by rfl) ⟨5193638, by rfl⟩ : syracuseStep 6924851 = 10387277) B10387277
theorem B4616567 : Blo 2051435 4616567 := bstep (se 1 (by rfl) ⟨3462425, by rfl⟩ : syracuseStep 4616567 = 6924851) B6924851
theorem B3077711 : Blo 2051435 3077711 := bstep (se 1 (by rfl) ⟨2308283, by rfl⟩ : syracuseStep 3077711 = 4616567) B4616567
theorem B2051807 : Blo 2051435 2051807 := bstep (se 1 (by rfl) ⟨1538855, by rfl⟩ : syracuseStep 2051807 = 3077711) B3077711
theorem B3077717 : Blo 2051435 3077717 := bbase (se 8 (by rfl) ⟨18033, by rfl⟩ : syracuseStep 3077717 = 36067) (by norm_num)
theorem B2051811 : Blo 2051435 2051811 := bstep (se 1 (by rfl) ⟨1538858, by rfl⟩ : syracuseStep 2051811 = 3077717) B3077717
theorem B3286613 : Blo 2051435 3286613 := bbase (se 8 (by rfl) ⟨19257, by rfl⟩ : syracuseStep 3286613 = 38515) (by norm_num)
theorem B8764301 : Blo 2051435 8764301 := bstep (se 3 (by rfl) ⟨1643306, by rfl⟩ : syracuseStep 8764301 = 3286613) B3286613
theorem B5842867 : Blo 2051435 5842867 := bstep (se 1 (by rfl) ⟨4382150, by rfl⟩ : syracuseStep 5842867 = 8764301) B8764301
theorem B7790489 : Blo 2051435 7790489 := bstep (se 2 (by rfl) ⟨2921433, by rfl⟩ : syracuseStep 7790489 = 5842867) B5842867
theorem B5193659 : Blo 2051435 5193659 := bstep (se 1 (by rfl) ⟨3895244, by rfl⟩ : syracuseStep 5193659 = 7790489) B7790489
theorem B3462439 : Blo 2051435 3462439 := bstep (se 1 (by rfl) ⟨2596829, by rfl⟩ : syracuseStep 3462439 = 5193659) B5193659
theorem B4616585 : Blo 2051435 4616585 := bstep (se 2 (by rfl) ⟨1731219, by rfl⟩ : syracuseStep 4616585 = 3462439) B3462439
theorem B3077723 : Blo 2051435 3077723 := bstep (se 1 (by rfl) ⟨2308292, by rfl⟩ : syracuseStep 3077723 = 4616585) B4616585
theorem B2051815 : Blo 2051435 2051815 := bstep (se 1 (by rfl) ⟨1538861, by rfl⟩ : syracuseStep 2051815 = 3077723) B3077723
theorem B2308297 : Blo 2051435 2308297 := bbase (se 2 (by rfl) ⟨865611, by rfl⟩ : syracuseStep 2308297 = 1731223) (by norm_num)
theorem B3077729 : Blo 2051435 3077729 := bstep (se 2 (by rfl) ⟨1154148, by rfl⟩ : syracuseStep 3077729 = 2308297) B2308297
theorem B2051819 : Blo 2051435 2051819 := bstep (se 1 (by rfl) ⟨1538864, by rfl⟩ : syracuseStep 2051819 = 3077729) B3077729
theorem B9859877 : Blo 2051435 9859877 := bbase (se 4 (by rfl) ⟨924363, by rfl⟩ : syracuseStep 9859877 = 1848727) (by norm_num)
theorem B6573251 : Blo 2051435 6573251 := bstep (se 1 (by rfl) ⟨4929938, by rfl⟩ : syracuseStep 6573251 = 9859877) B9859877
theorem B17528669 : Blo 2051435 17528669 := bstep (se 3 (by rfl) ⟨3286625, by rfl⟩ : syracuseStep 17528669 = 6573251) B6573251
theorem B11685779 : Blo 2051435 11685779 := bstep (se 1 (by rfl) ⟨8764334, by rfl⟩ : syracuseStep 11685779 = 17528669) B17528669
theorem B7790519 : Blo 2051435 7790519 := bstep (se 1 (by rfl) ⟨5842889, by rfl⟩ : syracuseStep 7790519 = 11685779) B11685779
theorem B5193679 : Blo 2051435 5193679 := bstep (se 1 (by rfl) ⟨3895259, by rfl⟩ : syracuseStep 5193679 = 7790519) B7790519
theorem B6924905 : Blo 2051435 6924905 := bstep (se 2 (by rfl) ⟨2596839, by rfl⟩ : syracuseStep 6924905 = 5193679) B5193679
theorem B4616603 : Blo 2051435 4616603 := bstep (se 1 (by rfl) ⟨3462452, by rfl⟩ : syracuseStep 4616603 = 6924905) B6924905
theorem B3077735 : Blo 2051435 3077735 := bstep (se 1 (by rfl) ⟨2308301, by rfl⟩ : syracuseStep 3077735 = 4616603) B4616603
theorem B2051823 : Blo 2051435 2051823 := bstep (se 1 (by rfl) ⟨1538867, by rfl⟩ : syracuseStep 2051823 = 3077735) B3077735
theorem B3077741 : Blo 2051435 3077741 := bbase (se 3 (by rfl) ⟨577076, by rfl⟩ : syracuseStep 3077741 = 1154153) (by norm_num)
theorem B2051827 : Blo 2051435 2051827 := bstep (se 1 (by rfl) ⟨1538870, by rfl⟩ : syracuseStep 2051827 = 3077741) B3077741
theorem B4616621 : Blo 2051435 4616621 := bbase (se 3 (by rfl) ⟨865616, by rfl⟩ : syracuseStep 4616621 = 1731233) (by norm_num)
theorem B3077747 : Blo 2051435 3077747 := bstep (se 1 (by rfl) ⟨2308310, by rfl⟩ : syracuseStep 3077747 = 4616621) B4616621
theorem B2051831 : Blo 2051435 2051831 := bstep (se 1 (by rfl) ⟨1538873, by rfl⟩ : syracuseStep 2051831 = 3077747) B3077747
theorem B2191097 : Blo 2051435 2191097 := bbase (se 2 (by rfl) ⟨821661, by rfl⟩ : syracuseStep 2191097 = 1643323) (by norm_num)
theorem B5842925 : Blo 2051435 5842925 := bstep (se 3 (by rfl) ⟨1095548, by rfl⟩ : syracuseStep 5842925 = 2191097) B2191097
theorem B3895283 : Blo 2051435 3895283 := bstep (se 1 (by rfl) ⟨2921462, by rfl⟩ : syracuseStep 3895283 = 5842925) B5842925
theorem B2596855 : Blo 2051435 2596855 := bstep (se 1 (by rfl) ⟨1947641, by rfl⟩ : syracuseStep 2596855 = 3895283) B3895283
theorem B3462473 : Blo 2051435 3462473 := bstep (se 2 (by rfl) ⟨1298427, by rfl⟩ : syracuseStep 3462473 = 2596855) B2596855
theorem B2308315 : Blo 2051435 2308315 := bstep (se 1 (by rfl) ⟨1731236, by rfl⟩ : syracuseStep 2308315 = 3462473) B3462473
theorem B3077753 : Blo 2051435 3077753 := bstep (se 2 (by rfl) ⟨1154157, by rfl⟩ : syracuseStep 3077753 = 2308315) B2308315
theorem B2051835 : Blo 2051435 2051835 := bstep (se 1 (by rfl) ⟨1538876, by rfl⟩ : syracuseStep 2051835 = 3077753) B3077753
theorem B71071829 : Blo 2051435 71071829 := bbase (se 8 (by rfl) ⟨416436, by rfl⟩ : syracuseStep 71071829 = 832873) (by norm_num)
theorem B47381219 : Blo 2051435 47381219 := bstep (se 1 (by rfl) ⟨35535914, by rfl⟩ : syracuseStep 47381219 = 71071829) B71071829
theorem B31587479 : Blo 2051435 31587479 := bstep (se 1 (by rfl) ⟨23690609, by rfl⟩ : syracuseStep 31587479 = 47381219) B47381219
theorem B21058319 : Blo 2051435 21058319 := bstep (se 1 (by rfl) ⟨15793739, by rfl⟩ : syracuseStep 21058319 = 31587479) B31587479
theorem B56155517 : Blo 2051435 56155517 := bstep (se 3 (by rfl) ⟨10529159, by rfl⟩ : syracuseStep 56155517 = 21058319) B21058319
theorem B37437011 : Blo 2051435 37437011 := bstep (se 1 (by rfl) ⟨28077758, by rfl⟩ : syracuseStep 37437011 = 56155517) B56155517
theorem B24958007 : Blo 2051435 24958007 := bstep (se 1 (by rfl) ⟨18718505, by rfl⟩ : syracuseStep 24958007 = 37437011) B37437011
theorem B16638671 : Blo 2051435 16638671 := bstep (se 1 (by rfl) ⟨12479003, by rfl⟩ : syracuseStep 16638671 = 24958007) B24958007
theorem B11092447 : Blo 2051435 11092447 := bstep (se 1 (by rfl) ⟨8319335, by rfl⟩ : syracuseStep 11092447 = 16638671) B16638671
theorem B59159717 : Blo 2051435 59159717 := bstep (se 4 (by rfl) ⟨5546223, by rfl⟩ : syracuseStep 59159717 = 11092447) B11092447
theorem B39439811 : Blo 2051435 39439811 := bstep (se 1 (by rfl) ⟨29579858, by rfl⟩ : syracuseStep 39439811 = 59159717) B59159717
theorem B26293207 : Blo 2051435 26293207 := bstep (se 1 (by rfl) ⟨19719905, by rfl⟩ : syracuseStep 26293207 = 39439811) B39439811
theorem B35057609 : Blo 2051435 35057609 := bstep (se 2 (by rfl) ⟨13146603, by rfl⟩ : syracuseStep 35057609 = 26293207) B26293207
theorem B23371739 : Blo 2051435 23371739 := bstep (se 1 (by rfl) ⟨17528804, by rfl⟩ : syracuseStep 23371739 = 35057609) B35057609
theorem B15581159 : Blo 2051435 15581159 := bstep (se 1 (by rfl) ⟨11685869, by rfl⟩ : syracuseStep 15581159 = 23371739) B23371739
theorem B10387439 : Blo 2051435 10387439 := bstep (se 1 (by rfl) ⟨7790579, by rfl⟩ : syracuseStep 10387439 = 15581159) B15581159
theorem B6924959 : Blo 2051435 6924959 := bstep (se 1 (by rfl) ⟨5193719, by rfl⟩ : syracuseStep 6924959 = 10387439) B10387439
theorem B4616639 : Blo 2051435 4616639 := bstep (se 1 (by rfl) ⟨3462479, by rfl⟩ : syracuseStep 4616639 = 6924959) B6924959
theorem B3077759 : Blo 2051435 3077759 := bstep (se 1 (by rfl) ⟨2308319, by rfl⟩ : syracuseStep 3077759 = 4616639) B4616639
theorem B2051839 : Blo 2051435 2051839 := bstep (se 1 (by rfl) ⟨1538879, by rfl⟩ : syracuseStep 2051839 = 3077759) B3077759
theorem B3077765 : Blo 2051435 3077765 := bbase (se 4 (by rfl) ⟨288540, by rfl⟩ : syracuseStep 3077765 = 577081) (by norm_num)
theorem B2051843 : Blo 2051435 2051843 := bstep (se 1 (by rfl) ⟨1538882, by rfl⟩ : syracuseStep 2051843 = 3077765) B3077765
theorem B3462493 : Blo 2051435 3462493 := bbase (se 3 (by rfl) ⟨649217, by rfl⟩ : syracuseStep 3462493 = 1298435) (by norm_num)
theorem B4616657 : Blo 2051435 4616657 := bstep (se 2 (by rfl) ⟨1731246, by rfl⟩ : syracuseStep 4616657 = 3462493) B3462493
theorem B3077771 : Blo 2051435 3077771 := bstep (se 1 (by rfl) ⟨2308328, by rfl⟩ : syracuseStep 3077771 = 4616657) B4616657
theorem B2051847 : Blo 2051435 2051847 := bstep (se 1 (by rfl) ⟨1538885, by rfl⟩ : syracuseStep 2051847 = 3077771) B3077771
theorem B2308333 : Blo 2051435 2308333 := bbase (se 3 (by rfl) ⟨432812, by rfl⟩ : syracuseStep 2308333 = 865625) (by norm_num)
theorem B3077777 : Blo 2051435 3077777 := bstep (se 2 (by rfl) ⟨1154166, by rfl⟩ : syracuseStep 3077777 = 2308333) B2308333
theorem B2051851 : Blo 2051435 2051851 := bstep (se 1 (by rfl) ⟨1538888, by rfl⟩ : syracuseStep 2051851 = 3077777) B3077777
theorem B6925013 : Blo 2051435 6925013 := bbase (se 7 (by rfl) ⟨81152, by rfl⟩ : syracuseStep 6925013 = 162305) (by norm_num)
theorem B4616675 : Blo 2051435 4616675 := bstep (se 1 (by rfl) ⟨3462506, by rfl⟩ : syracuseStep 4616675 = 6925013) B6925013
theorem B3077783 : Blo 2051435 3077783 := bstep (se 1 (by rfl) ⟨2308337, by rfl⟩ : syracuseStep 3077783 = 4616675) B4616675
theorem B2051855 : Blo 2051435 2051855 := bstep (se 1 (by rfl) ⟨1538891, by rfl⟩ : syracuseStep 2051855 = 3077783) B3077783
theorem B3077789 : Blo 2051435 3077789 := bbase (se 3 (by rfl) ⟨577085, by rfl⟩ : syracuseStep 3077789 = 1154171) (by norm_num)
theorem B2051859 : Blo 2051435 2051859 := bstep (se 1 (by rfl) ⟨1538894, by rfl⟩ : syracuseStep 2051859 = 3077789) B3077789
theorem B4616693 : Blo 2051435 4616693 := bbase (se 5 (by rfl) ⟨216407, by rfl⟩ : syracuseStep 4616693 = 432815) (by norm_num)
theorem B3077795 : Blo 2051435 3077795 := bstep (se 1 (by rfl) ⟨2308346, by rfl⟩ : syracuseStep 3077795 = 4616693) B4616693
theorem B2051863 : Blo 2051435 2051863 := bstep (se 1 (by rfl) ⟨1538897, by rfl⟩ : syracuseStep 2051863 = 3077795) B3077795
theorem B21058613 : Blo 2051435 21058613 := bbase (se 5 (by rfl) ⟨987122, by rfl⟩ : syracuseStep 21058613 = 1974245) (by norm_num)
theorem B14039075 : Blo 2051435 14039075 := bstep (se 1 (by rfl) ⟨10529306, by rfl⟩ : syracuseStep 14039075 = 21058613) B21058613
theorem B9359383 : Blo 2051435 9359383 := bstep (se 1 (by rfl) ⟨7019537, by rfl⟩ : syracuseStep 9359383 = 14039075) B14039075
theorem B12479177 : Blo 2051435 12479177 := bstep (se 2 (by rfl) ⟨4679691, by rfl⟩ : syracuseStep 12479177 = 9359383) B9359383
theorem B8319451 : Blo 2051435 8319451 := bstep (se 1 (by rfl) ⟨6239588, by rfl⟩ : syracuseStep 8319451 = 12479177) B12479177
theorem B11092601 : Blo 2051435 11092601 := bstep (se 2 (by rfl) ⟨4159725, by rfl⟩ : syracuseStep 11092601 = 8319451) B8319451
theorem B7395067 : Blo 2051435 7395067 := bstep (se 1 (by rfl) ⟨5546300, by rfl⟩ : syracuseStep 7395067 = 11092601) B11092601
theorem B39440357 : Blo 2051435 39440357 := bstep (se 4 (by rfl) ⟨3697533, by rfl⟩ : syracuseStep 39440357 = 7395067) B7395067
theorem B26293571 : Blo 2051435 26293571 := bstep (se 1 (by rfl) ⟨19720178, by rfl⟩ : syracuseStep 26293571 = 39440357) B39440357
theorem B17529047 : Blo 2051435 17529047 := bstep (se 1 (by rfl) ⟨13146785, by rfl⟩ : syracuseStep 17529047 = 26293571) B26293571
theorem B11686031 : Blo 2051435 11686031 := bstep (se 1 (by rfl) ⟨8764523, by rfl⟩ : syracuseStep 11686031 = 17529047) B17529047
theorem B7790687 : Blo 2051435 7790687 := bstep (se 1 (by rfl) ⟨5843015, by rfl⟩ : syracuseStep 7790687 = 11686031) B11686031
theorem B5193791 : Blo 2051435 5193791 := bstep (se 1 (by rfl) ⟨3895343, by rfl⟩ : syracuseStep 5193791 = 7790687) B7790687
theorem B3462527 : Blo 2051435 3462527 := bstep (se 1 (by rfl) ⟨2596895, by rfl⟩ : syracuseStep 3462527 = 5193791) B5193791
theorem B2308351 : Blo 2051435 2308351 := bstep (se 1 (by rfl) ⟨1731263, by rfl⟩ : syracuseStep 2308351 = 3462527) B3462527
theorem B3077801 : Blo 2051435 3077801 := bstep (se 2 (by rfl) ⟨1154175, by rfl⟩ : syracuseStep 3077801 = 2308351) B2308351
theorem B2051867 : Blo 2051435 2051867 := bstep (se 1 (by rfl) ⟨1538900, by rfl⟩ : syracuseStep 2051867 = 3077801) B3077801
theorem B2632333 : Blo 2051435 2632333 := bbase (se 3 (by rfl) ⟨493562, by rfl⟩ : syracuseStep 2632333 = 987125) (by norm_num)
theorem B3509777 : Blo 2051435 3509777 := bstep (se 2 (by rfl) ⟨1316166, by rfl⟩ : syracuseStep 3509777 = 2632333) B2632333
theorem B2339851 : Blo 2051435 2339851 := bstep (se 1 (by rfl) ⟨1754888, by rfl⟩ : syracuseStep 2339851 = 3509777) B3509777
theorem B3119801 : Blo 2051435 3119801 := bstep (se 2 (by rfl) ⟨1169925, by rfl⟩ : syracuseStep 3119801 = 2339851) B2339851
theorem B8319469 : Blo 2051435 8319469 := bstep (se 3 (by rfl) ⟨1559900, by rfl⟩ : syracuseStep 8319469 = 3119801) B3119801
theorem B11092625 : Blo 2051435 11092625 := bstep (se 2 (by rfl) ⟨4159734, by rfl⟩ : syracuseStep 11092625 = 8319469) B8319469
theorem B7395083 : Blo 2051435 7395083 := bstep (se 1 (by rfl) ⟨5546312, by rfl⟩ : syracuseStep 7395083 = 11092625) B11092625
theorem B4930055 : Blo 2051435 4930055 := bstep (se 1 (by rfl) ⟨3697541, by rfl⟩ : syracuseStep 4930055 = 7395083) B7395083
theorem B3286703 : Blo 2051435 3286703 := bstep (se 1 (by rfl) ⟨2465027, by rfl⟩ : syracuseStep 3286703 = 4930055) B4930055
theorem B2191135 : Blo 2051435 2191135 := bstep (se 1 (by rfl) ⟨1643351, by rfl⟩ : syracuseStep 2191135 = 3286703) B3286703
theorem B2921513 : Blo 2051435 2921513 := bstep (se 2 (by rfl) ⟨1095567, by rfl⟩ : syracuseStep 2921513 = 2191135) B2191135
theorem B7790701 : Blo 2051435 7790701 := bstep (se 3 (by rfl) ⟨1460756, by rfl⟩ : syracuseStep 7790701 = 2921513) B2921513
theorem B10387601 : Blo 2051435 10387601 := bstep (se 2 (by rfl) ⟨3895350, by rfl⟩ : syracuseStep 10387601 = 7790701) B7790701
theorem B6925067 : Blo 2051435 6925067 := bstep (se 1 (by rfl) ⟨5193800, by rfl⟩ : syracuseStep 6925067 = 10387601) B10387601
theorem B4616711 : Blo 2051435 4616711 := bstep (se 1 (by rfl) ⟨3462533, by rfl⟩ : syracuseStep 4616711 = 6925067) B6925067
theorem B3077807 : Blo 2051435 3077807 := bstep (se 1 (by rfl) ⟨2308355, by rfl⟩ : syracuseStep 3077807 = 4616711) B4616711
theorem B2051871 : Blo 2051435 2051871 := bstep (se 1 (by rfl) ⟨1538903, by rfl⟩ : syracuseStep 2051871 = 3077807) B3077807
theorem B3077813 : Blo 2051435 3077813 := bbase (se 5 (by rfl) ⟨144272, by rfl⟩ : syracuseStep 3077813 = 288545) (by norm_num)
theorem B2051875 : Blo 2051435 2051875 := bstep (se 1 (by rfl) ⟨1538906, by rfl⟩ : syracuseStep 2051875 = 3077813) B3077813
theorem B5193821 : Blo 2051435 5193821 := bbase (se 3 (by rfl) ⟨973841, by rfl⟩ : syracuseStep 5193821 = 1947683) (by norm_num)
theorem B3462547 : Blo 2051435 3462547 := bstep (se 1 (by rfl) ⟨2596910, by rfl⟩ : syracuseStep 3462547 = 5193821) B5193821
theorem B4616729 : Blo 2051435 4616729 := bstep (se 2 (by rfl) ⟨1731273, by rfl⟩ : syracuseStep 4616729 = 3462547) B3462547
theorem B3077819 : Blo 2051435 3077819 := bstep (se 1 (by rfl) ⟨2308364, by rfl⟩ : syracuseStep 3077819 = 4616729) B4616729
theorem B2051879 : Blo 2051435 2051879 := bstep (se 1 (by rfl) ⟨1538909, by rfl⟩ : syracuseStep 2051879 = 3077819) B3077819
theorem B2308369 : Blo 2051435 2308369 := bbase (se 2 (by rfl) ⟨865638, by rfl⟩ : syracuseStep 2308369 = 1731277) (by norm_num)
theorem B3077825 : Blo 2051435 3077825 := bstep (se 2 (by rfl) ⟨1154184, by rfl⟩ : syracuseStep 3077825 = 2308369) B2308369
theorem B2051883 : Blo 2051435 2051883 := bstep (se 1 (by rfl) ⟨1538912, by rfl⟩ : syracuseStep 2051883 = 3077825) B3077825
theorem B3895381 : Blo 2051435 3895381 := bbase (se 8 (by rfl) ⟨22824, by rfl⟩ : syracuseStep 3895381 = 45649) (by norm_num)
theorem B5193841 : Blo 2051435 5193841 := bstep (se 2 (by rfl) ⟨1947690, by rfl⟩ : syracuseStep 5193841 = 3895381) B3895381
theorem B6925121 : Blo 2051435 6925121 := bstep (se 2 (by rfl) ⟨2596920, by rfl⟩ : syracuseStep 6925121 = 5193841) B5193841
theorem B4616747 : Blo 2051435 4616747 := bstep (se 1 (by rfl) ⟨3462560, by rfl⟩ : syracuseStep 4616747 = 6925121) B6925121
theorem B3077831 : Blo 2051435 3077831 := bstep (se 1 (by rfl) ⟨2308373, by rfl⟩ : syracuseStep 3077831 = 4616747) B4616747
theorem B2051887 : Blo 2051435 2051887 := bstep (se 1 (by rfl) ⟨1538915, by rfl⟩ : syracuseStep 2051887 = 3077831) B3077831
theorem B3077837 : Blo 2051435 3077837 := bbase (se 3 (by rfl) ⟨577094, by rfl⟩ : syracuseStep 3077837 = 1154189) (by norm_num)
theorem B2051891 : Blo 2051435 2051891 := bstep (se 1 (by rfl) ⟨1538918, by rfl⟩ : syracuseStep 2051891 = 3077837) B3077837
theorem B4616765 : Blo 2051435 4616765 := bbase (se 3 (by rfl) ⟨865643, by rfl⟩ : syracuseStep 4616765 = 1731287) (by norm_num)
theorem B3077843 : Blo 2051435 3077843 := bstep (se 1 (by rfl) ⟨2308382, by rfl⟩ : syracuseStep 3077843 = 4616765) B4616765
theorem B2051895 : Blo 2051435 2051895 := bstep (se 1 (by rfl) ⟨1538921, by rfl⟩ : syracuseStep 2051895 = 3077843) B3077843
theorem B3462581 : Blo 2051435 3462581 := bbase (se 5 (by rfl) ⟨162308, by rfl⟩ : syracuseStep 3462581 = 324617) (by norm_num)
theorem B2308387 : Blo 2051435 2308387 := bstep (se 1 (by rfl) ⟨1731290, by rfl⟩ : syracuseStep 2308387 = 3462581) B3462581
theorem B3077849 : Blo 2051435 3077849 := bstep (se 2 (by rfl) ⟨1154193, by rfl⟩ : syracuseStep 3077849 = 2308387) B2308387
theorem B2051899 : Blo 2051435 2051899 := bstep (se 1 (by rfl) ⟨1538924, by rfl⟩ : syracuseStep 2051899 = 3077849) B3077849
theorem B2191169 : Blo 2051435 2191169 := bbase (se 2 (by rfl) ⟨821688, by rfl⟩ : syracuseStep 2191169 = 1643377) (by norm_num)
theorem B5843117 : Blo 2051435 5843117 := bstep (se 3 (by rfl) ⟨1095584, by rfl⟩ : syracuseStep 5843117 = 2191169) B2191169
theorem B15581645 : Blo 2051435 15581645 := bstep (se 3 (by rfl) ⟨2921558, by rfl⟩ : syracuseStep 15581645 = 5843117) B5843117
theorem B10387763 : Blo 2051435 10387763 := bstep (se 1 (by rfl) ⟨7790822, by rfl⟩ : syracuseStep 10387763 = 15581645) B15581645
theorem B6925175 : Blo 2051435 6925175 := bstep (se 1 (by rfl) ⟨5193881, by rfl⟩ : syracuseStep 6925175 = 10387763) B10387763
theorem B4616783 : Blo 2051435 4616783 := bstep (se 1 (by rfl) ⟨3462587, by rfl⟩ : syracuseStep 4616783 = 6925175) B6925175
theorem B3077855 : Blo 2051435 3077855 := bstep (se 1 (by rfl) ⟨2308391, by rfl⟩ : syracuseStep 3077855 = 4616783) B4616783
theorem B2051903 : Blo 2051435 2051903 := bstep (se 1 (by rfl) ⟨1538927, by rfl⟩ : syracuseStep 2051903 = 3077855) B3077855
theorem B3077861 : Blo 2051435 3077861 := bbase (se 4 (by rfl) ⟨288549, by rfl⟩ : syracuseStep 3077861 = 577099) (by norm_num)
theorem B2051907 : Blo 2051435 2051907 := bstep (se 1 (by rfl) ⟨1538930, by rfl⟩ : syracuseStep 2051907 = 3077861) B3077861
theorem B5843141 : Blo 2051435 5843141 := bbase (se 4 (by rfl) ⟨547794, by rfl⟩ : syracuseStep 5843141 = 1095589) (by norm_num)
theorem B3895427 : Blo 2051435 3895427 := bstep (se 1 (by rfl) ⟨2921570, by rfl⟩ : syracuseStep 3895427 = 5843141) B5843141
theorem B2596951 : Blo 2051435 2596951 := bstep (se 1 (by rfl) ⟨1947713, by rfl⟩ : syracuseStep 2596951 = 3895427) B3895427
theorem B3462601 : Blo 2051435 3462601 := bstep (se 2 (by rfl) ⟨1298475, by rfl⟩ : syracuseStep 3462601 = 2596951) B2596951
theorem B4616801 : Blo 2051435 4616801 := bstep (se 2 (by rfl) ⟨1731300, by rfl⟩ : syracuseStep 4616801 = 3462601) B3462601
theorem B3077867 : Blo 2051435 3077867 := bstep (se 1 (by rfl) ⟨2308400, by rfl⟩ : syracuseStep 3077867 = 4616801) B4616801
theorem B2051911 : Blo 2051435 2051911 := bstep (se 1 (by rfl) ⟨1538933, by rfl⟩ : syracuseStep 2051911 = 3077867) B3077867
theorem B2308405 : Blo 2051435 2308405 := bbase (se 5 (by rfl) ⟨108206, by rfl⟩ : syracuseStep 2308405 = 216413) (by norm_num)
theorem B3077873 : Blo 2051435 3077873 := bstep (se 2 (by rfl) ⟨1154202, by rfl⟩ : syracuseStep 3077873 = 2308405) B2308405
theorem B2051915 : Blo 2051435 2051915 := bstep (se 1 (by rfl) ⟨1538936, by rfl⟩ : syracuseStep 2051915 = 3077873) B3077873
theorem B2596961 : Blo 2051435 2596961 := bbase (se 2 (by rfl) ⟨973860, by rfl⟩ : syracuseStep 2596961 = 1947721) (by norm_num)
theorem B6925229 : Blo 2051435 6925229 := bstep (se 3 (by rfl) ⟨1298480, by rfl⟩ : syracuseStep 6925229 = 2596961) B2596961
theorem B4616819 : Blo 2051435 4616819 := bstep (se 1 (by rfl) ⟨3462614, by rfl⟩ : syracuseStep 4616819 = 6925229) B6925229
theorem B3077879 : Blo 2051435 3077879 := bstep (se 1 (by rfl) ⟨2308409, by rfl⟩ : syracuseStep 3077879 = 4616819) B4616819
theorem B2051919 : Blo 2051435 2051919 := bstep (se 1 (by rfl) ⟨1538939, by rfl⟩ : syracuseStep 2051919 = 3077879) B3077879
theorem B3077885 : Blo 2051435 3077885 := bbase (se 3 (by rfl) ⟨577103, by rfl⟩ : syracuseStep 3077885 = 1154207) (by norm_num)
theorem B2051923 : Blo 2051435 2051923 := bstep (se 1 (by rfl) ⟨1538942, by rfl⟩ : syracuseStep 2051923 = 3077885) B3077885
theorem B4616837 : Blo 2051435 4616837 := bbase (se 4 (by rfl) ⟨432828, by rfl⟩ : syracuseStep 4616837 = 865657) (by norm_num)
theorem B3077891 : Blo 2051435 3077891 := bstep (se 1 (by rfl) ⟨2308418, by rfl⟩ : syracuseStep 3077891 = 4616837) B4616837
theorem B2051927 : Blo 2051435 2051927 := bstep (se 1 (by rfl) ⟨1538945, by rfl⟩ : syracuseStep 2051927 = 3077891) B3077891
theorem B5622149 : Blo 2051435 5622149 := bbase (se 4 (by rfl) ⟨527076, by rfl⟩ : syracuseStep 5622149 = 1054153) (by norm_num)
theorem B3748099 : Blo 2051435 3748099 := bstep (se 1 (by rfl) ⟨2811074, by rfl⟩ : syracuseStep 3748099 = 5622149) B5622149
theorem B4997465 : Blo 2051435 4997465 := bstep (se 2 (by rfl) ⟨1874049, by rfl⟩ : syracuseStep 4997465 = 3748099) B3748099
theorem B3331643 : Blo 2051435 3331643 := bstep (se 1 (by rfl) ⟨2498732, by rfl⟩ : syracuseStep 3331643 = 4997465) B4997465
theorem B35537525 : Blo 2051435 35537525 := bstep (se 5 (by rfl) ⟨1665821, by rfl⟩ : syracuseStep 35537525 = 3331643) B3331643
theorem B23691683 : Blo 2051435 23691683 := bstep (se 1 (by rfl) ⟨17768762, by rfl⟩ : syracuseStep 23691683 = 35537525) B35537525
theorem B15794455 : Blo 2051435 15794455 := bstep (se 1 (by rfl) ⟨11845841, by rfl⟩ : syracuseStep 15794455 = 23691683) B23691683
theorem B21059273 : Blo 2051435 21059273 := bstep (se 2 (by rfl) ⟨7897227, by rfl⟩ : syracuseStep 21059273 = 15794455) B15794455
theorem B14039515 : Blo 2051435 14039515 := bstep (se 1 (by rfl) ⟨10529636, by rfl⟩ : syracuseStep 14039515 = 21059273) B21059273
theorem B18719353 : Blo 2051435 18719353 := bstep (se 2 (by rfl) ⟨7019757, by rfl⟩ : syracuseStep 18719353 = 14039515) B14039515
theorem B24959137 : Blo 2051435 24959137 := bstep (se 2 (by rfl) ⟨9359676, by rfl⟩ : syracuseStep 24959137 = 18719353) B18719353
theorem B33278849 : Blo 2051435 33278849 := bstep (se 2 (by rfl) ⟨12479568, by rfl⟩ : syracuseStep 33278849 = 24959137) B24959137
theorem B22185899 : Blo 2051435 22185899 := bstep (se 1 (by rfl) ⟨16639424, by rfl⟩ : syracuseStep 22185899 = 33278849) B33278849
theorem B14790599 : Blo 2051435 14790599 := bstep (se 1 (by rfl) ⟨11092949, by rfl⟩ : syracuseStep 14790599 = 22185899) B22185899
theorem B9860399 : Blo 2051435 9860399 := bstep (se 1 (by rfl) ⟨7395299, by rfl⟩ : syracuseStep 9860399 = 14790599) B14790599
theorem B6573599 : Blo 2051435 6573599 := bstep (se 1 (by rfl) ⟨4930199, by rfl⟩ : syracuseStep 6573599 = 9860399) B9860399
theorem B4382399 : Blo 2051435 4382399 := bstep (se 1 (by rfl) ⟨3286799, by rfl⟩ : syracuseStep 4382399 = 6573599) B6573599
theorem B2921599 : Blo 2051435 2921599 := bstep (se 1 (by rfl) ⟨2191199, by rfl⟩ : syracuseStep 2921599 = 4382399) B4382399
theorem B3895465 : Blo 2051435 3895465 := bstep (se 2 (by rfl) ⟨1460799, by rfl⟩ : syracuseStep 3895465 = 2921599) B2921599
theorem B5193953 : Blo 2051435 5193953 := bstep (se 2 (by rfl) ⟨1947732, by rfl⟩ : syracuseStep 5193953 = 3895465) B3895465
theorem B3462635 : Blo 2051435 3462635 := bstep (se 1 (by rfl) ⟨2596976, by rfl⟩ : syracuseStep 3462635 = 5193953) B5193953
theorem B2308423 : Blo 2051435 2308423 := bstep (se 1 (by rfl) ⟨1731317, by rfl⟩ : syracuseStep 2308423 = 3462635) B3462635
theorem B3077897 : Blo 2051435 3077897 := bstep (se 2 (by rfl) ⟨1154211, by rfl⟩ : syracuseStep 3077897 = 2308423) B2308423
theorem B2051931 : Blo 2051435 2051931 := bstep (se 1 (by rfl) ⟨1538948, by rfl⟩ : syracuseStep 2051931 = 3077897) B3077897
theorem B10387925 : Blo 2051435 10387925 := bbase (se 7 (by rfl) ⟨121733, by rfl⟩ : syracuseStep 10387925 = 243467) (by norm_num)
theorem B6925283 : Blo 2051435 6925283 := bstep (se 1 (by rfl) ⟨5193962, by rfl⟩ : syracuseStep 6925283 = 10387925) B10387925
theorem B4616855 : Blo 2051435 4616855 := bstep (se 1 (by rfl) ⟨3462641, by rfl⟩ : syracuseStep 4616855 = 6925283) B6925283
theorem B3077903 : Blo 2051435 3077903 := bstep (se 1 (by rfl) ⟨2308427, by rfl⟩ : syracuseStep 3077903 = 4616855) B4616855
theorem B2051935 : Blo 2051435 2051935 := bstep (se 1 (by rfl) ⟨1538951, by rfl⟩ : syracuseStep 2051935 = 3077903) B3077903
theorem B3077909 : Blo 2051435 3077909 := bbase (se 6 (by rfl) ⟨72138, by rfl⟩ : syracuseStep 3077909 = 144277) (by norm_num)
theorem B2051939 : Blo 2051435 2051939 := bstep (se 1 (by rfl) ⟨1538954, by rfl⟩ : syracuseStep 2051939 = 3077909) B3077909
theorem B7019797 : Blo 2051435 7019797 := bbase (se 6 (by rfl) ⟨164526, by rfl⟩ : syracuseStep 7019797 = 329053) (by norm_num)
theorem B9359729 : Blo 2051435 9359729 := bstep (se 2 (by rfl) ⟨3509898, by rfl⟩ : syracuseStep 9359729 = 7019797) B7019797
theorem B6239819 : Blo 2051435 6239819 := bstep (se 1 (by rfl) ⟨4679864, by rfl⟩ : syracuseStep 6239819 = 9359729) B9359729
theorem B4159879 : Blo 2051435 4159879 := bstep (se 1 (by rfl) ⟨3119909, by rfl⟩ : syracuseStep 4159879 = 6239819) B6239819
theorem B88744085 : Blo 2051435 88744085 := bstep (se 6 (by rfl) ⟨2079939, by rfl⟩ : syracuseStep 88744085 = 4159879) B4159879
theorem B59162723 : Blo 2051435 59162723 := bstep (se 1 (by rfl) ⟨44372042, by rfl⟩ : syracuseStep 59162723 = 88744085) B88744085
theorem B39441815 : Blo 2051435 39441815 := bstep (se 1 (by rfl) ⟨29581361, by rfl⟩ : syracuseStep 39441815 = 59162723) B59162723
theorem B26294543 : Blo 2051435 26294543 := bstep (se 1 (by rfl) ⟨19720907, by rfl⟩ : syracuseStep 26294543 = 39441815) B39441815
theorem B17529695 : Blo 2051435 17529695 := bstep (se 1 (by rfl) ⟨13147271, by rfl⟩ : syracuseStep 17529695 = 26294543) B26294543
theorem B11686463 : Blo 2051435 11686463 := bstep (se 1 (by rfl) ⟨8764847, by rfl⟩ : syracuseStep 11686463 = 17529695) B17529695
theorem B7790975 : Blo 2051435 7790975 := bstep (se 1 (by rfl) ⟨5843231, by rfl⟩ : syracuseStep 7790975 = 11686463) B11686463
theorem B5193983 : Blo 2051435 5193983 := bstep (se 1 (by rfl) ⟨3895487, by rfl⟩ : syracuseStep 5193983 = 7790975) B7790975
theorem B3462655 : Blo 2051435 3462655 := bstep (se 1 (by rfl) ⟨2596991, by rfl⟩ : syracuseStep 3462655 = 5193983) B5193983
theorem B4616873 : Blo 2051435 4616873 := bstep (se 2 (by rfl) ⟨1731327, by rfl⟩ : syracuseStep 4616873 = 3462655) B3462655
theorem B3077915 : Blo 2051435 3077915 := bstep (se 1 (by rfl) ⟨2308436, by rfl⟩ : syracuseStep 3077915 = 4616873) B4616873
theorem B2051943 : Blo 2051435 2051943 := bstep (se 1 (by rfl) ⟨1538957, by rfl⟩ : syracuseStep 2051943 = 3077915) B3077915
theorem B2308441 : Blo 2051435 2308441 := bbase (se 2 (by rfl) ⟨865665, by rfl⟩ : syracuseStep 2308441 = 1731331) (by norm_num)
theorem B3077921 : Blo 2051435 3077921 := bstep (se 2 (by rfl) ⟨1154220, by rfl⟩ : syracuseStep 3077921 = 2308441) B2308441
theorem B2051947 : Blo 2051435 2051947 := bstep (se 1 (by rfl) ⟨1538960, by rfl⟩ : syracuseStep 2051947 = 3077921) B3077921
theorem B6239845 : Blo 2051435 6239845 := bbase (se 4 (by rfl) ⟨584985, by rfl⟩ : syracuseStep 6239845 = 1169971) (by norm_num)
theorem B8319793 : Blo 2051435 8319793 := bstep (se 2 (by rfl) ⟨3119922, by rfl⟩ : syracuseStep 8319793 = 6239845) B6239845
theorem B11093057 : Blo 2051435 11093057 := bstep (se 2 (by rfl) ⟨4159896, by rfl⟩ : syracuseStep 11093057 = 8319793) B8319793
theorem B7395371 : Blo 2051435 7395371 := bstep (se 1 (by rfl) ⟨5546528, by rfl⟩ : syracuseStep 7395371 = 11093057) B11093057
theorem B4930247 : Blo 2051435 4930247 := bstep (se 1 (by rfl) ⟨3697685, by rfl⟩ : syracuseStep 4930247 = 7395371) B7395371
theorem B3286831 : Blo 2051435 3286831 := bstep (se 1 (by rfl) ⟨2465123, by rfl⟩ : syracuseStep 3286831 = 4930247) B4930247
theorem B4382441 : Blo 2051435 4382441 := bstep (se 2 (by rfl) ⟨1643415, by rfl⟩ : syracuseStep 4382441 = 3286831) B3286831
theorem B2921627 : Blo 2051435 2921627 := bstep (se 1 (by rfl) ⟨2191220, by rfl⟩ : syracuseStep 2921627 = 4382441) B4382441
theorem B7791005 : Blo 2051435 7791005 := bstep (se 3 (by rfl) ⟨1460813, by rfl⟩ : syracuseStep 7791005 = 2921627) B2921627
theorem B5194003 : Blo 2051435 5194003 := bstep (se 1 (by rfl) ⟨3895502, by rfl⟩ : syracuseStep 5194003 = 7791005) B7791005
theorem B6925337 : Blo 2051435 6925337 := bstep (se 2 (by rfl) ⟨2597001, by rfl⟩ : syracuseStep 6925337 = 5194003) B5194003
theorem B4616891 : Blo 2051435 4616891 := bstep (se 1 (by rfl) ⟨3462668, by rfl⟩ : syracuseStep 4616891 = 6925337) B6925337
theorem B3077927 : Blo 2051435 3077927 := bstep (se 1 (by rfl) ⟨2308445, by rfl⟩ : syracuseStep 3077927 = 4616891) B4616891
theorem B2051951 : Blo 2051435 2051951 := bstep (se 1 (by rfl) ⟨1538963, by rfl⟩ : syracuseStep 2051951 = 3077927) B3077927
theorem B3077933 : Blo 2051435 3077933 := bbase (se 3 (by rfl) ⟨577112, by rfl⟩ : syracuseStep 3077933 = 1154225) (by norm_num)
theorem B2051955 : Blo 2051435 2051955 := bstep (se 1 (by rfl) ⟨1538966, by rfl⟩ : syracuseStep 2051955 = 3077933) B3077933
theorem B4616909 : Blo 2051435 4616909 := bbase (se 3 (by rfl) ⟨865670, by rfl⟩ : syracuseStep 4616909 = 1731341) (by norm_num)
theorem B3077939 : Blo 2051435 3077939 := bstep (se 1 (by rfl) ⟨2308454, by rfl⟩ : syracuseStep 3077939 = 4616909) B4616909
theorem B2051959 : Blo 2051435 2051959 := bstep (se 1 (by rfl) ⟨1538969, by rfl⟩ : syracuseStep 2051959 = 3077939) B3077939
theorem B2597017 : Blo 2051435 2597017 := bbase (se 2 (by rfl) ⟨973881, by rfl⟩ : syracuseStep 2597017 = 1947763) (by norm_num)
theorem B3462689 : Blo 2051435 3462689 := bstep (se 2 (by rfl) ⟨1298508, by rfl⟩ : syracuseStep 3462689 = 2597017) B2597017
theorem B2308459 : Blo 2051435 2308459 := bstep (se 1 (by rfl) ⟨1731344, by rfl⟩ : syracuseStep 2308459 = 3462689) B3462689
theorem B3077945 : Blo 2051435 3077945 := bstep (se 2 (by rfl) ⟨1154229, by rfl⟩ : syracuseStep 3077945 = 2308459) B2308459
theorem B2051963 : Blo 2051435 2051963 := bstep (se 1 (by rfl) ⟨1538972, by rfl⟩ : syracuseStep 2051963 = 3077945) B3077945
theorem B8764949 : Blo 2051435 8764949 := bbase (se 6 (by rfl) ⟨205428, by rfl⟩ : syracuseStep 8764949 = 410857) (by norm_num)
theorem B23373197 : Blo 2051435 23373197 := bstep (se 3 (by rfl) ⟨4382474, by rfl⟩ : syracuseStep 23373197 = 8764949) B8764949
theorem B15582131 : Blo 2051435 15582131 := bstep (se 1 (by rfl) ⟨11686598, by rfl⟩ : syracuseStep 15582131 = 23373197) B23373197
theorem B10388087 : Blo 2051435 10388087 := bstep (se 1 (by rfl) ⟨7791065, by rfl⟩ : syracuseStep 10388087 = 15582131) B15582131
theorem B6925391 : Blo 2051435 6925391 := bstep (se 1 (by rfl) ⟨5194043, by rfl⟩ : syracuseStep 6925391 = 10388087) B10388087
theorem B4616927 : Blo 2051435 4616927 := bstep (se 1 (by rfl) ⟨3462695, by rfl⟩ : syracuseStep 4616927 = 6925391) B6925391
theorem B3077951 : Blo 2051435 3077951 := bstep (se 1 (by rfl) ⟨2308463, by rfl⟩ : syracuseStep 3077951 = 4616927) B4616927
theorem B2051967 : Blo 2051435 2051967 := bstep (se 1 (by rfl) ⟨1538975, by rfl⟩ : syracuseStep 2051967 = 3077951) B3077951
theorem B3077957 : Blo 2051435 3077957 := bbase (se 4 (by rfl) ⟨288558, by rfl⟩ : syracuseStep 3077957 = 577117) (by norm_num)
theorem B2051971 : Blo 2051435 2051971 := bstep (se 1 (by rfl) ⟨1538978, by rfl⟩ : syracuseStep 2051971 = 3077957) B3077957
theorem B3462709 : Blo 2051435 3462709 := bbase (se 5 (by rfl) ⟨162314, by rfl⟩ : syracuseStep 3462709 = 324629) (by norm_num)
theorem B4616945 : Blo 2051435 4616945 := bstep (se 2 (by rfl) ⟨1731354, by rfl⟩ : syracuseStep 4616945 = 3462709) B3462709
theorem B3077963 : Blo 2051435 3077963 := bstep (se 1 (by rfl) ⟨2308472, by rfl⟩ : syracuseStep 3077963 = 4616945) B4616945
theorem B2051975 : Blo 2051435 2051975 := bstep (se 1 (by rfl) ⟨1538981, by rfl⟩ : syracuseStep 2051975 = 3077963) B3077963
theorem B2308477 : Blo 2051435 2308477 := bbase (se 3 (by rfl) ⟨432839, by rfl⟩ : syracuseStep 2308477 = 865679) (by norm_num)
theorem B3077969 : Blo 2051435 3077969 := bstep (se 2 (by rfl) ⟨1154238, by rfl⟩ : syracuseStep 3077969 = 2308477) B2308477
theorem B2051979 : Blo 2051435 2051979 := bstep (se 1 (by rfl) ⟨1538984, by rfl⟩ : syracuseStep 2051979 = 3077969) B3077969
theorem B6925445 : Blo 2051435 6925445 := bbase (se 4 (by rfl) ⟨649260, by rfl⟩ : syracuseStep 6925445 = 1298521) (by norm_num)
theorem B4616963 : Blo 2051435 4616963 := bstep (se 1 (by rfl) ⟨3462722, by rfl⟩ : syracuseStep 4616963 = 6925445) B6925445
theorem B3077975 : Blo 2051435 3077975 := bstep (se 1 (by rfl) ⟨2308481, by rfl⟩ : syracuseStep 3077975 = 4616963) B4616963
theorem B2051983 : Blo 2051435 2051983 := bstep (se 1 (by rfl) ⟨1538987, by rfl⟩ : syracuseStep 2051983 = 3077975) B3077975
theorem B3077981 : Blo 2051435 3077981 := bbase (se 3 (by rfl) ⟨577121, by rfl⟩ : syracuseStep 3077981 = 1154243) (by norm_num)
theorem B2051987 : Blo 2051435 2051987 := bstep (se 1 (by rfl) ⟨1538990, by rfl⟩ : syracuseStep 2051987 = 3077981) B3077981
theorem B4616981 : Blo 2051435 4616981 := bbase (se 6 (by rfl) ⟨108210, by rfl⟩ : syracuseStep 4616981 = 216421) (by norm_num)
theorem B3077987 : Blo 2051435 3077987 := bstep (se 1 (by rfl) ⟨2308490, by rfl⟩ : syracuseStep 3077987 = 4616981) B4616981
theorem B2051991 : Blo 2051435 2051991 := bstep (se 1 (by rfl) ⟨1538993, by rfl⟩ : syracuseStep 2051991 = 3077987) B3077987
theorem B7791173 : Blo 2051435 7791173 := bbase (se 4 (by rfl) ⟨730422, by rfl⟩ : syracuseStep 7791173 = 1460845) (by norm_num)
theorem B5194115 : Blo 2051435 5194115 := bstep (se 1 (by rfl) ⟨3895586, by rfl⟩ : syracuseStep 5194115 = 7791173) B7791173
theorem B3462743 : Blo 2051435 3462743 := bstep (se 1 (by rfl) ⟨2597057, by rfl⟩ : syracuseStep 3462743 = 5194115) B5194115
theorem B2308495 : Blo 2051435 2308495 := bstep (se 1 (by rfl) ⟨1731371, by rfl⟩ : syracuseStep 2308495 = 3462743) B3462743
theorem B3077993 : Blo 2051435 3077993 := bstep (se 2 (by rfl) ⟨1154247, by rfl⟩ : syracuseStep 3077993 = 2308495) B2308495
theorem B2051995 : Blo 2051435 2051995 := bstep (se 1 (by rfl) ⟨1538996, by rfl⟩ : syracuseStep 2051995 = 3077993) B3077993
theorem B6663509 : Blo 2051435 6663509 := bbase (se 11 (by rfl) ⟨4880, by rfl⟩ : syracuseStep 6663509 = 9761) (by norm_num)
theorem B4442339 : Blo 2051435 4442339 := bstep (se 1 (by rfl) ⟨3331754, by rfl⟩ : syracuseStep 4442339 = 6663509) B6663509
theorem B2961559 : Blo 2051435 2961559 := bstep (se 1 (by rfl) ⟨2221169, by rfl⟩ : syracuseStep 2961559 = 4442339) B4442339
theorem B3948745 : Blo 2051435 3948745 := bstep (se 2 (by rfl) ⟨1480779, by rfl⟩ : syracuseStep 3948745 = 2961559) B2961559
theorem B5264993 : Blo 2051435 5264993 := bstep (se 2 (by rfl) ⟨1974372, by rfl⟩ : syracuseStep 5264993 = 3948745) B3948745
theorem B3509995 : Blo 2051435 3509995 := bstep (se 1 (by rfl) ⟨2632496, by rfl⟩ : syracuseStep 3509995 = 5264993) B5264993
theorem B4679993 : Blo 2051435 4679993 := bstep (se 2 (by rfl) ⟨1754997, by rfl⟩ : syracuseStep 4679993 = 3509995) B3509995
theorem B3119995 : Blo 2051435 3119995 := bstep (se 1 (by rfl) ⟨2339996, by rfl⟩ : syracuseStep 3119995 = 4679993) B4679993
theorem B4159993 : Blo 2051435 4159993 := bstep (se 2 (by rfl) ⟨1559997, by rfl⟩ : syracuseStep 4159993 = 3119995) B3119995
theorem B5546657 : Blo 2051435 5546657 := bstep (se 2 (by rfl) ⟨2079996, by rfl⟩ : syracuseStep 5546657 = 4159993) B4159993
theorem B14791085 : Blo 2051435 14791085 := bstep (se 3 (by rfl) ⟨2773328, by rfl⟩ : syracuseStep 14791085 = 5546657) B5546657
theorem B9860723 : Blo 2051435 9860723 := bstep (se 1 (by rfl) ⟨7395542, by rfl⟩ : syracuseStep 9860723 = 14791085) B14791085
theorem B6573815 : Blo 2051435 6573815 := bstep (se 1 (by rfl) ⟨4930361, by rfl⟩ : syracuseStep 6573815 = 9860723) B9860723
theorem B4382543 : Blo 2051435 4382543 := bstep (se 1 (by rfl) ⟨3286907, by rfl⟩ : syracuseStep 4382543 = 6573815) B6573815
theorem B11686781 : Blo 2051435 11686781 := bstep (se 3 (by rfl) ⟨2191271, by rfl⟩ : syracuseStep 11686781 = 4382543) B4382543
theorem B7791187 : Blo 2051435 7791187 := bstep (se 1 (by rfl) ⟨5843390, by rfl⟩ : syracuseStep 7791187 = 11686781) B11686781
theorem B10388249 : Blo 2051435 10388249 := bstep (se 2 (by rfl) ⟨3895593, by rfl⟩ : syracuseStep 10388249 = 7791187) B7791187
theorem B6925499 : Blo 2051435 6925499 := bstep (se 1 (by rfl) ⟨5194124, by rfl⟩ : syracuseStep 6925499 = 10388249) B10388249
theorem B4616999 : Blo 2051435 4616999 := bstep (se 1 (by rfl) ⟨3462749, by rfl⟩ : syracuseStep 4616999 = 6925499) B6925499
theorem B3077999 : Blo 2051435 3077999 := bstep (se 1 (by rfl) ⟨2308499, by rfl⟩ : syracuseStep 3077999 = 4616999) B4616999
theorem B2051999 : Blo 2051435 2051999 := bstep (se 1 (by rfl) ⟨1538999, by rfl⟩ : syracuseStep 2051999 = 3077999) B3077999
theorem B3078005 : Blo 2051435 3078005 := bbase (se 5 (by rfl) ⟨144281, by rfl⟩ : syracuseStep 3078005 = 288563) (by norm_num)
theorem B2052003 : Blo 2051435 2052003 := bstep (se 1 (by rfl) ⟨1539002, by rfl⟩ : syracuseStep 2052003 = 3078005) B3078005
theorem B4680013 : Blo 2051435 4680013 := bbase (se 3 (by rfl) ⟨877502, by rfl⟩ : syracuseStep 4680013 = 1755005) (by norm_num)
theorem B6240017 : Blo 2051435 6240017 := bstep (se 2 (by rfl) ⟨2340006, by rfl⟩ : syracuseStep 6240017 = 4680013) B4680013
theorem B4160011 : Blo 2051435 4160011 := bstep (se 1 (by rfl) ⟨3120008, by rfl⟩ : syracuseStep 4160011 = 6240017) B6240017
theorem B5546681 : Blo 2051435 5546681 := bstep (se 2 (by rfl) ⟨2080005, by rfl⟩ : syracuseStep 5546681 = 4160011) B4160011
theorem B3697787 : Blo 2051435 3697787 := bstep (se 1 (by rfl) ⟨2773340, by rfl⟩ : syracuseStep 3697787 = 5546681) B5546681
theorem B2465191 : Blo 2051435 2465191 := bstep (se 1 (by rfl) ⟨1848893, by rfl⟩ : syracuseStep 2465191 = 3697787) B3697787
theorem B3286921 : Blo 2051435 3286921 := bstep (se 2 (by rfl) ⟨1232595, by rfl⟩ : syracuseStep 3286921 = 2465191) B2465191
theorem B4382561 : Blo 2051435 4382561 := bstep (se 2 (by rfl) ⟨1643460, by rfl⟩ : syracuseStep 4382561 = 3286921) B3286921
theorem B2921707 : Blo 2051435 2921707 := bstep (se 1 (by rfl) ⟨2191280, by rfl⟩ : syracuseStep 2921707 = 4382561) B4382561
theorem B3895609 : Blo 2051435 3895609 := bstep (se 2 (by rfl) ⟨1460853, by rfl⟩ : syracuseStep 3895609 = 2921707) B2921707
theorem B5194145 : Blo 2051435 5194145 := bstep (se 2 (by rfl) ⟨1947804, by rfl⟩ : syracuseStep 5194145 = 3895609) B3895609
theorem B3462763 : Blo 2051435 3462763 := bstep (se 1 (by rfl) ⟨2597072, by rfl⟩ : syracuseStep 3462763 = 5194145) B5194145
theorem B4617017 : Blo 2051435 4617017 := bstep (se 2 (by rfl) ⟨1731381, by rfl⟩ : syracuseStep 4617017 = 3462763) B3462763
theorem B3078011 : Blo 2051435 3078011 := bstep (se 1 (by rfl) ⟨2308508, by rfl⟩ : syracuseStep 3078011 = 4617017) B4617017
theorem B2052007 : Blo 2051435 2052007 := bstep (se 1 (by rfl) ⟨1539005, by rfl⟩ : syracuseStep 2052007 = 3078011) B3078011
theorem B2308513 : Blo 2051435 2308513 := bbase (se 2 (by rfl) ⟨865692, by rfl⟩ : syracuseStep 2308513 = 1731385) (by norm_num)
theorem B3078017 : Blo 2051435 3078017 := bstep (se 2 (by rfl) ⟨1154256, by rfl⟩ : syracuseStep 3078017 = 2308513) B2308513
theorem B2052011 : Blo 2051435 2052011 := bstep (se 1 (by rfl) ⟨1539008, by rfl⟩ : syracuseStep 2052011 = 3078017) B3078017
theorem B5194165 : Blo 2051435 5194165 := bbase (se 5 (by rfl) ⟨243476, by rfl⟩ : syracuseStep 5194165 = 486953) (by norm_num)
theorem B6925553 : Blo 2051435 6925553 := bstep (se 2 (by rfl) ⟨2597082, by rfl⟩ : syracuseStep 6925553 = 5194165) B5194165
theorem B4617035 : Blo 2051435 4617035 := bstep (se 1 (by rfl) ⟨3462776, by rfl⟩ : syracuseStep 4617035 = 6925553) B6925553
theorem B3078023 : Blo 2051435 3078023 := bstep (se 1 (by rfl) ⟨2308517, by rfl⟩ : syracuseStep 3078023 = 4617035) B4617035
theorem B2052015 : Blo 2051435 2052015 := bstep (se 1 (by rfl) ⟨1539011, by rfl⟩ : syracuseStep 2052015 = 3078023) B3078023
theorem B3078029 : Blo 2051435 3078029 := bbase (se 3 (by rfl) ⟨577130, by rfl⟩ : syracuseStep 3078029 = 1154261) (by norm_num)
theorem B2052019 : Blo 2051435 2052019 := bstep (se 1 (by rfl) ⟨1539014, by rfl⟩ : syracuseStep 2052019 = 3078029) B3078029
theorem B4617053 : Blo 2051435 4617053 := bbase (se 3 (by rfl) ⟨865697, by rfl⟩ : syracuseStep 4617053 = 1731395) (by norm_num)
theorem B3078035 : Blo 2051435 3078035 := bstep (se 1 (by rfl) ⟨2308526, by rfl⟩ : syracuseStep 3078035 = 4617053) B4617053
theorem B2052023 : Blo 2051435 2052023 := bstep (se 1 (by rfl) ⟨1539017, by rfl⟩ : syracuseStep 2052023 = 3078035) B3078035
theorem B3462797 : Blo 2051435 3462797 := bbase (se 3 (by rfl) ⟨649274, by rfl⟩ : syracuseStep 3462797 = 1298549) (by norm_num)
theorem B2308531 : Blo 2051435 2308531 := bstep (se 1 (by rfl) ⟨1731398, by rfl⟩ : syracuseStep 2308531 = 3462797) B3462797
theorem B3078041 : Blo 2051435 3078041 := bstep (se 2 (by rfl) ⟨1154265, by rfl⟩ : syracuseStep 3078041 = 2308531) B2308531
theorem B2052027 : Blo 2051435 2052027 := bstep (se 1 (by rfl) ⟨1539020, by rfl⟩ : syracuseStep 2052027 = 3078041) B3078041
theorem B3697829 : Blo 2051435 3697829 := bbase (se 4 (by rfl) ⟨346671, by rfl⟩ : syracuseStep 3697829 = 693343) (by norm_num)
theorem B2465219 : Blo 2051435 2465219 := bstep (se 1 (by rfl) ⟨1848914, by rfl⟩ : syracuseStep 2465219 = 3697829) B3697829
theorem B6573917 : Blo 2051435 6573917 := bstep (se 3 (by rfl) ⟨1232609, by rfl⟩ : syracuseStep 6573917 = 2465219) B2465219
theorem B17530445 : Blo 2051435 17530445 := bstep (se 3 (by rfl) ⟨3286958, by rfl⟩ : syracuseStep 17530445 = 6573917) B6573917
theorem B11686963 : Blo 2051435 11686963 := bstep (se 1 (by rfl) ⟨8765222, by rfl⟩ : syracuseStep 11686963 = 17530445) B17530445
theorem B15582617 : Blo 2051435 15582617 := bstep (se 2 (by rfl) ⟨5843481, by rfl⟩ : syracuseStep 15582617 = 11686963) B11686963
theorem B10388411 : Blo 2051435 10388411 := bstep (se 1 (by rfl) ⟨7791308, by rfl⟩ : syracuseStep 10388411 = 15582617) B15582617
theorem B6925607 : Blo 2051435 6925607 := bstep (se 1 (by rfl) ⟨5194205, by rfl⟩ : syracuseStep 6925607 = 10388411) B10388411
theorem B4617071 : Blo 2051435 4617071 := bstep (se 1 (by rfl) ⟨3462803, by rfl⟩ : syracuseStep 4617071 = 6925607) B6925607
theorem B3078047 : Blo 2051435 3078047 := bstep (se 1 (by rfl) ⟨2308535, by rfl⟩ : syracuseStep 3078047 = 4617071) B4617071
theorem B2052031 : Blo 2051435 2052031 := bstep (se 1 (by rfl) ⟨1539023, by rfl⟩ : syracuseStep 2052031 = 3078047) B3078047
theorem B3078053 : Blo 2051435 3078053 := bbase (se 4 (by rfl) ⟨288567, by rfl⟩ : syracuseStep 3078053 = 577135) (by norm_num)
theorem B2052035 : Blo 2051435 2052035 := bstep (se 1 (by rfl) ⟨1539026, by rfl⟩ : syracuseStep 2052035 = 3078053) B3078053
theorem B2597113 : Blo 2051435 2597113 := bbase (se 2 (by rfl) ⟨973917, by rfl⟩ : syracuseStep 2597113 = 1947835) (by norm_num)
theorem B3462817 : Blo 2051435 3462817 := bstep (se 2 (by rfl) ⟨1298556, by rfl⟩ : syracuseStep 3462817 = 2597113) B2597113
theorem B4617089 : Blo 2051435 4617089 := bstep (se 2 (by rfl) ⟨1731408, by rfl⟩ : syracuseStep 4617089 = 3462817) B3462817
theorem B3078059 : Blo 2051435 3078059 := bstep (se 1 (by rfl) ⟨2308544, by rfl⟩ : syracuseStep 3078059 = 4617089) B4617089
theorem B2052039 : Blo 2051435 2052039 := bstep (se 1 (by rfl) ⟨1539029, by rfl⟩ : syracuseStep 2052039 = 3078059) B3078059
theorem B2308549 : Blo 2051435 2308549 := bbase (se 4 (by rfl) ⟨216426, by rfl⟩ : syracuseStep 2308549 = 432853) (by norm_num)
theorem B3078065 : Blo 2051435 3078065 := bstep (se 2 (by rfl) ⟨1154274, by rfl⟩ : syracuseStep 3078065 = 2308549) B2308549
theorem B2052043 : Blo 2051435 2052043 := bstep (se 1 (by rfl) ⟨1539032, by rfl⟩ : syracuseStep 2052043 = 3078065) B3078065
theorem B3895685 : Blo 2051435 3895685 := bbase (se 4 (by rfl) ⟨365220, by rfl⟩ : syracuseStep 3895685 = 730441) (by norm_num)
theorem B2597123 : Blo 2051435 2597123 := bstep (se 1 (by rfl) ⟨1947842, by rfl⟩ : syracuseStep 2597123 = 3895685) B3895685
theorem B6925661 : Blo 2051435 6925661 := bstep (se 3 (by rfl) ⟨1298561, by rfl⟩ : syracuseStep 6925661 = 2597123) B2597123
theorem B4617107 : Blo 2051435 4617107 := bstep (se 1 (by rfl) ⟨3462830, by rfl⟩ : syracuseStep 4617107 = 6925661) B6925661
theorem B3078071 : Blo 2051435 3078071 := bstep (se 1 (by rfl) ⟨2308553, by rfl⟩ : syracuseStep 3078071 = 4617107) B4617107
theorem B2052047 : Blo 2051435 2052047 := bstep (se 1 (by rfl) ⟨1539035, by rfl⟩ : syracuseStep 2052047 = 3078071) B3078071
theorem B3078077 : Blo 2051435 3078077 := bbase (se 3 (by rfl) ⟨577139, by rfl⟩ : syracuseStep 3078077 = 1154279) (by norm_num)
theorem B2052051 : Blo 2051435 2052051 := bstep (se 1 (by rfl) ⟨1539038, by rfl⟩ : syracuseStep 2052051 = 3078077) B3078077
theorem B4617125 : Blo 2051435 4617125 := bbase (se 4 (by rfl) ⟨432855, by rfl⟩ : syracuseStep 4617125 = 865711) (by norm_num)
theorem B3078083 : Blo 2051435 3078083 := bstep (se 1 (by rfl) ⟨2308562, by rfl⟩ : syracuseStep 3078083 = 4617125) B4617125
theorem B2052055 : Blo 2051435 2052055 := bstep (se 1 (by rfl) ⟨1539041, by rfl⟩ : syracuseStep 2052055 = 3078083) B3078083
theorem B5194277 : Blo 2051435 5194277 := bbase (se 4 (by rfl) ⟨486963, by rfl⟩ : syracuseStep 5194277 = 973927) (by norm_num)
theorem B3462851 : Blo 2051435 3462851 := bstep (se 1 (by rfl) ⟨2597138, by rfl⟩ : syracuseStep 3462851 = 5194277) B5194277
theorem B2308567 : Blo 2051435 2308567 := bstep (se 1 (by rfl) ⟨1731425, by rfl⟩ : syracuseStep 2308567 = 3462851) B3462851
theorem B3078089 : Blo 2051435 3078089 := bstep (se 2 (by rfl) ⟨1154283, by rfl⟩ : syracuseStep 3078089 = 2308567) B2308567
theorem B2052059 : Blo 2051435 2052059 := bstep (se 1 (by rfl) ⟨1539044, by rfl⟩ : syracuseStep 2052059 = 3078089) B3078089
theorem B5843573 : Blo 2051435 5843573 := bbase (se 5 (by rfl) ⟨273917, by rfl⟩ : syracuseStep 5843573 = 547835) (by norm_num)
theorem B3895715 : Blo 2051435 3895715 := bstep (se 1 (by rfl) ⟨2921786, by rfl⟩ : syracuseStep 3895715 = 5843573) B5843573
theorem B10388573 : Blo 2051435 10388573 := bstep (se 3 (by rfl) ⟨1947857, by rfl⟩ : syracuseStep 10388573 = 3895715) B3895715
theorem B6925715 : Blo 2051435 6925715 := bstep (se 1 (by rfl) ⟨5194286, by rfl⟩ : syracuseStep 6925715 = 10388573) B10388573
theorem B4617143 : Blo 2051435 4617143 := bstep (se 1 (by rfl) ⟨3462857, by rfl⟩ : syracuseStep 4617143 = 6925715) B6925715
theorem B3078095 : Blo 2051435 3078095 := bstep (se 1 (by rfl) ⟨2308571, by rfl⟩ : syracuseStep 3078095 = 4617143) B4617143
theorem B2052063 : Blo 2051435 2052063 := bstep (se 1 (by rfl) ⟨1539047, by rfl⟩ : syracuseStep 2052063 = 3078095) B3078095
theorem B3078101 : Blo 2051435 3078101 := bbase (se 7 (by rfl) ⟨36071, by rfl⟩ : syracuseStep 3078101 = 72143) (by norm_num)
theorem B2052067 : Blo 2051435 2052067 := bstep (se 1 (by rfl) ⟨1539050, by rfl⟩ : syracuseStep 2052067 = 3078101) B3078101
theorem B7791461 : Blo 2051435 7791461 := bbase (se 4 (by rfl) ⟨730449, by rfl⟩ : syracuseStep 7791461 = 1460899) (by norm_num)
theorem B5194307 : Blo 2051435 5194307 := bstep (se 1 (by rfl) ⟨3895730, by rfl⟩ : syracuseStep 5194307 = 7791461) B7791461
theorem B3462871 : Blo 2051435 3462871 := bstep (se 1 (by rfl) ⟨2597153, by rfl⟩ : syracuseStep 3462871 = 5194307) B5194307
theorem B4617161 : Blo 2051435 4617161 := bstep (se 2 (by rfl) ⟨1731435, by rfl⟩ : syracuseStep 4617161 = 3462871) B3462871
theorem B3078107 : Blo 2051435 3078107 := bstep (se 1 (by rfl) ⟨2308580, by rfl⟩ : syracuseStep 3078107 = 4617161) B4617161
theorem B2052071 : Blo 2051435 2052071 := bstep (se 1 (by rfl) ⟨1539053, by rfl⟩ : syracuseStep 2052071 = 3078107) B3078107
theorem B2308585 : Blo 2051435 2308585 := bbase (se 2 (by rfl) ⟨865719, by rfl⟩ : syracuseStep 2308585 = 1731439) (by norm_num)
theorem B3078113 : Blo 2051435 3078113 := bstep (se 2 (by rfl) ⟨1154292, by rfl⟩ : syracuseStep 3078113 = 2308585) B2308585
theorem B2052075 : Blo 2051435 2052075 := bstep (se 1 (by rfl) ⟨1539056, by rfl⟩ : syracuseStep 2052075 = 3078113) B3078113
theorem B2191357 : Blo 2051435 2191357 := bbase (se 3 (by rfl) ⟨410879, by rfl⟩ : syracuseStep 2191357 = 821759) (by norm_num)
theorem B11687237 : Blo 2051435 11687237 := bstep (se 4 (by rfl) ⟨1095678, by rfl⟩ : syracuseStep 11687237 = 2191357) B2191357
theorem B7791491 : Blo 2051435 7791491 := bstep (se 1 (by rfl) ⟨5843618, by rfl⟩ : syracuseStep 7791491 = 11687237) B11687237
theorem B5194327 : Blo 2051435 5194327 := bstep (se 1 (by rfl) ⟨3895745, by rfl⟩ : syracuseStep 5194327 = 7791491) B7791491
theorem B6925769 : Blo 2051435 6925769 := bstep (se 2 (by rfl) ⟨2597163, by rfl⟩ : syracuseStep 6925769 = 5194327) B5194327
theorem B4617179 : Blo 2051435 4617179 := bstep (se 1 (by rfl) ⟨3462884, by rfl⟩ : syracuseStep 4617179 = 6925769) B6925769
theorem B3078119 : Blo 2051435 3078119 := bstep (se 1 (by rfl) ⟨2308589, by rfl⟩ : syracuseStep 3078119 = 4617179) B4617179
theorem B2052079 : Blo 2051435 2052079 := bstep (se 1 (by rfl) ⟨1539059, by rfl⟩ : syracuseStep 2052079 = 3078119) B3078119
theorem B3078125 : Blo 2051435 3078125 := bbase (se 3 (by rfl) ⟨577148, by rfl⟩ : syracuseStep 3078125 = 1154297) (by norm_num)
theorem B2052083 : Blo 2051435 2052083 := bstep (se 1 (by rfl) ⟨1539062, by rfl⟩ : syracuseStep 2052083 = 3078125) B3078125
theorem B4617197 : Blo 2051435 4617197 := bbase (se 3 (by rfl) ⟨865724, by rfl⟩ : syracuseStep 4617197 = 1731449) (by norm_num)
theorem B3078131 : Blo 2051435 3078131 := bstep (se 1 (by rfl) ⟨2308598, by rfl⟩ : syracuseStep 3078131 = 4617197) B4617197
theorem B2052087 : Blo 2051435 2052087 := bstep (se 1 (by rfl) ⟨1539065, by rfl⟩ : syracuseStep 2052087 = 3078131) B3078131
theorem B4382741 : Blo 2051435 4382741 := bbase (se 6 (by rfl) ⟨102720, by rfl⟩ : syracuseStep 4382741 = 205441) (by norm_num)
theorem B2921827 : Blo 2051435 2921827 := bstep (se 1 (by rfl) ⟨2191370, by rfl⟩ : syracuseStep 2921827 = 4382741) B4382741
theorem B3895769 : Blo 2051435 3895769 := bstep (se 2 (by rfl) ⟨1460913, by rfl⟩ : syracuseStep 3895769 = 2921827) B2921827
theorem B2597179 : Blo 2051435 2597179 := bstep (se 1 (by rfl) ⟨1947884, by rfl⟩ : syracuseStep 2597179 = 3895769) B3895769
theorem B3462905 : Blo 2051435 3462905 := bstep (se 2 (by rfl) ⟨1298589, by rfl⟩ : syracuseStep 3462905 = 2597179) B2597179
theorem B2308603 : Blo 2051435 2308603 := bstep (se 1 (by rfl) ⟨1731452, by rfl⟩ : syracuseStep 2308603 = 3462905) B3462905
theorem B3078137 : Blo 2051435 3078137 := bstep (se 2 (by rfl) ⟨1154301, by rfl⟩ : syracuseStep 3078137 = 2308603) B2308603
theorem B2052091 : Blo 2051435 2052091 := bstep (se 1 (by rfl) ⟨1539068, by rfl⟩ : syracuseStep 2052091 = 3078137) B3078137
theorem B4997861 : Blo 2051435 4997861 := bbase (se 4 (by rfl) ⟨468549, by rfl⟩ : syracuseStep 4997861 = 937099) (by norm_num)
theorem B53310517 : Blo 2051435 53310517 := bstep (se 5 (by rfl) ⟨2498930, by rfl⟩ : syracuseStep 53310517 = 4997861) B4997861
theorem B284322757 : Blo 2051435 284322757 := bstep (se 4 (by rfl) ⟨26655258, by rfl⟩ : syracuseStep 284322757 = 53310517) B53310517
theorem B379097009 : Blo 2051435 379097009 := bstep (se 2 (by rfl) ⟨142161378, by rfl⟩ : syracuseStep 379097009 = 284322757) B284322757
theorem B252731339 : Blo 2051435 252731339 := bstep (se 1 (by rfl) ⟨189548504, by rfl⟩ : syracuseStep 252731339 = 379097009) B379097009
theorem B168487559 : Blo 2051435 168487559 := bstep (se 1 (by rfl) ⟨126365669, by rfl⟩ : syracuseStep 168487559 = 252731339) B252731339
theorem B112325039 : Blo 2051435 112325039 := bstep (se 1 (by rfl) ⟨84243779, by rfl⟩ : syracuseStep 112325039 = 168487559) B168487559
theorem B74883359 : Blo 2051435 74883359 := bstep (se 1 (by rfl) ⟨56162519, by rfl⟩ : syracuseStep 74883359 = 112325039) B112325039
theorem B49922239 : Blo 2051435 49922239 := bstep (se 1 (by rfl) ⟨37441679, by rfl⟩ : syracuseStep 49922239 = 74883359) B74883359
theorem B66562985 : Blo 2051435 66562985 := bstep (se 2 (by rfl) ⟨24961119, by rfl⟩ : syracuseStep 66562985 = 49922239) B49922239
theorem B177501293 : Blo 2051435 177501293 := bstep (se 3 (by rfl) ⟨33281492, by rfl⟩ : syracuseStep 177501293 = 66562985) B66562985
theorem B118334195 : Blo 2051435 118334195 := bstep (se 1 (by rfl) ⟨88750646, by rfl⟩ : syracuseStep 118334195 = 177501293) B177501293
theorem B78889463 : Blo 2051435 78889463 := bstep (se 1 (by rfl) ⟨59167097, by rfl⟩ : syracuseStep 78889463 = 118334195) B118334195
theorem B52592975 : Blo 2051435 52592975 := bstep (se 1 (by rfl) ⟨39444731, by rfl⟩ : syracuseStep 52592975 = 78889463) B78889463
theorem B35061983 : Blo 2051435 35061983 := bstep (se 1 (by rfl) ⟨26296487, by rfl⟩ : syracuseStep 35061983 = 52592975) B52592975
theorem B23374655 : Blo 2051435 23374655 := bstep (se 1 (by rfl) ⟨17530991, by rfl⟩ : syracuseStep 23374655 = 35061983) B35061983
theorem B15583103 : Blo 2051435 15583103 := bstep (se 1 (by rfl) ⟨11687327, by rfl⟩ : syracuseStep 15583103 = 23374655) B23374655
theorem B10388735 : Blo 2051435 10388735 := bstep (se 1 (by rfl) ⟨7791551, by rfl⟩ : syracuseStep 10388735 = 15583103) B15583103
theorem B6925823 : Blo 2051435 6925823 := bstep (se 1 (by rfl) ⟨5194367, by rfl⟩ : syracuseStep 6925823 = 10388735) B10388735
theorem B4617215 : Blo 2051435 4617215 := bstep (se 1 (by rfl) ⟨3462911, by rfl⟩ : syracuseStep 4617215 = 6925823) B6925823
theorem B3078143 : Blo 2051435 3078143 := bstep (se 1 (by rfl) ⟨2308607, by rfl⟩ : syracuseStep 3078143 = 4617215) B4617215
theorem B2052095 : Blo 2051435 2052095 := bstep (se 1 (by rfl) ⟨1539071, by rfl⟩ : syracuseStep 2052095 = 3078143) B3078143
theorem B3078149 : Blo 2051435 3078149 := bbase (se 4 (by rfl) ⟨288576, by rfl⟩ : syracuseStep 3078149 = 577153) (by norm_num)
theorem B2052099 : Blo 2051435 2052099 := bstep (se 1 (by rfl) ⟨1539074, by rfl⟩ : syracuseStep 2052099 = 3078149) B3078149
theorem B3462925 : Blo 2051435 3462925 := bbase (se 3 (by rfl) ⟨649298, by rfl⟩ : syracuseStep 3462925 = 1298597) (by norm_num)
theorem B4617233 : Blo 2051435 4617233 := bstep (se 2 (by rfl) ⟨1731462, by rfl⟩ : syracuseStep 4617233 = 3462925) B3462925
theorem B3078155 : Blo 2051435 3078155 := bstep (se 1 (by rfl) ⟨2308616, by rfl⟩ : syracuseStep 3078155 = 4617233) B4617233
theorem B2052103 : Blo 2051435 2052103 := bstep (se 1 (by rfl) ⟨1539077, by rfl⟩ : syracuseStep 2052103 = 3078155) B3078155
theorem B2308621 : Blo 2051435 2308621 := bbase (se 3 (by rfl) ⟨432866, by rfl⟩ : syracuseStep 2308621 = 865733) (by norm_num)
theorem B3078161 : Blo 2051435 3078161 := bstep (se 2 (by rfl) ⟨1154310, by rfl⟩ : syracuseStep 3078161 = 2308621) B2308621
theorem B2052107 : Blo 2051435 2052107 := bstep (se 1 (by rfl) ⟨1539080, by rfl⟩ : syracuseStep 2052107 = 3078161) B3078161
theorem B6925877 : Blo 2051435 6925877 := bbase (se 5 (by rfl) ⟨324650, by rfl⟩ : syracuseStep 6925877 = 649301) (by norm_num)
theorem B4617251 : Blo 2051435 4617251 := bstep (se 1 (by rfl) ⟨3462938, by rfl⟩ : syracuseStep 4617251 = 6925877) B6925877
theorem B3078167 : Blo 2051435 3078167 := bstep (se 1 (by rfl) ⟨2308625, by rfl⟩ : syracuseStep 3078167 = 4617251) B4617251
theorem B2052111 : Blo 2051435 2052111 := bstep (se 1 (by rfl) ⟨1539083, by rfl⟩ : syracuseStep 2052111 = 3078167) B3078167
theorem B3078173 : Blo 2051435 3078173 := bbase (se 3 (by rfl) ⟨577157, by rfl⟩ : syracuseStep 3078173 = 1154315) (by norm_num)
theorem B2052115 : Blo 2051435 2052115 := bstep (se 1 (by rfl) ⟨1539086, by rfl⟩ : syracuseStep 2052115 = 3078173) B3078173
theorem B4617269 : Blo 2051435 4617269 := bbase (se 5 (by rfl) ⟨216434, by rfl⟩ : syracuseStep 4617269 = 432869) (by norm_num)
theorem B3078179 : Blo 2051435 3078179 := bstep (se 1 (by rfl) ⟨2308634, by rfl⟩ : syracuseStep 3078179 = 4617269) B4617269
theorem B2052119 : Blo 2051435 2052119 := bstep (se 1 (by rfl) ⟨1539089, by rfl⟩ : syracuseStep 2052119 = 3078179) B3078179
theorem B6574213 : Blo 2051435 6574213 := bbase (se 4 (by rfl) ⟨616332, by rfl⟩ : syracuseStep 6574213 = 1232665) (by norm_num)
theorem B8765617 : Blo 2051435 8765617 := bstep (se 2 (by rfl) ⟨3287106, by rfl⟩ : syracuseStep 8765617 = 6574213) B6574213
theorem B11687489 : Blo 2051435 11687489 := bstep (se 2 (by rfl) ⟨4382808, by rfl⟩ : syracuseStep 11687489 = 8765617) B8765617
theorem B7791659 : Blo 2051435 7791659 := bstep (se 1 (by rfl) ⟨5843744, by rfl⟩ : syracuseStep 7791659 = 11687489) B11687489
theorem B5194439 : Blo 2051435 5194439 := bstep (se 1 (by rfl) ⟨3895829, by rfl⟩ : syracuseStep 5194439 = 7791659) B7791659
theorem B3462959 : Blo 2051435 3462959 := bstep (se 1 (by rfl) ⟨2597219, by rfl⟩ : syracuseStep 3462959 = 5194439) B5194439
theorem B2308639 : Blo 2051435 2308639 := bstep (se 1 (by rfl) ⟨1731479, by rfl⟩ : syracuseStep 2308639 = 3462959) B3462959
theorem B3078185 : Blo 2051435 3078185 := bstep (se 2 (by rfl) ⟨1154319, by rfl⟩ : syracuseStep 3078185 = 2308639) B2308639
theorem B2052123 : Blo 2051435 2052123 := bstep (se 1 (by rfl) ⟨1539092, by rfl⟩ : syracuseStep 2052123 = 3078185) B3078185
theorem B4930669 : Blo 2051435 4930669 := bbase (se 3 (by rfl) ⟨924500, by rfl⟩ : syracuseStep 4930669 = 1849001) (by norm_num)
theorem B6574225 : Blo 2051435 6574225 := bstep (se 2 (by rfl) ⟨2465334, by rfl⟩ : syracuseStep 6574225 = 4930669) B4930669
theorem B8765633 : Blo 2051435 8765633 := bstep (se 2 (by rfl) ⟨3287112, by rfl⟩ : syracuseStep 8765633 = 6574225) B6574225
theorem B5843755 : Blo 2051435 5843755 := bstep (se 1 (by rfl) ⟨4382816, by rfl⟩ : syracuseStep 5843755 = 8765633) B8765633
theorem B7791673 : Blo 2051435 7791673 := bstep (se 2 (by rfl) ⟨2921877, by rfl⟩ : syracuseStep 7791673 = 5843755) B5843755
theorem B10388897 : Blo 2051435 10388897 := bstep (se 2 (by rfl) ⟨3895836, by rfl⟩ : syracuseStep 10388897 = 7791673) B7791673
theorem B6925931 : Blo 2051435 6925931 := bstep (se 1 (by rfl) ⟨5194448, by rfl⟩ : syracuseStep 6925931 = 10388897) B10388897
theorem B4617287 : Blo 2051435 4617287 := bstep (se 1 (by rfl) ⟨3462965, by rfl⟩ : syracuseStep 4617287 = 6925931) B6925931
theorem B3078191 : Blo 2051435 3078191 := bstep (se 1 (by rfl) ⟨2308643, by rfl⟩ : syracuseStep 3078191 = 4617287) B4617287
theorem B2052127 : Blo 2051435 2052127 := bstep (se 1 (by rfl) ⟨1539095, by rfl⟩ : syracuseStep 2052127 = 3078191) B3078191
theorem B3078197 : Blo 2051435 3078197 := bbase (se 5 (by rfl) ⟨144290, by rfl⟩ : syracuseStep 3078197 = 288581) (by norm_num)
theorem B2052131 : Blo 2051435 2052131 := bstep (se 1 (by rfl) ⟨1539098, by rfl⟩ : syracuseStep 2052131 = 3078197) B3078197
theorem B5194469 : Blo 2051435 5194469 := bbase (se 4 (by rfl) ⟨486981, by rfl⟩ : syracuseStep 5194469 = 973963) (by norm_num)
theorem B3462979 : Blo 2051435 3462979 := bstep (se 1 (by rfl) ⟨2597234, by rfl⟩ : syracuseStep 3462979 = 5194469) B5194469
theorem B4617305 : Blo 2051435 4617305 := bstep (se 2 (by rfl) ⟨1731489, by rfl⟩ : syracuseStep 4617305 = 3462979) B3462979
theorem B3078203 : Blo 2051435 3078203 := bstep (se 1 (by rfl) ⟨2308652, by rfl⟩ : syracuseStep 3078203 = 4617305) B4617305
theorem B2052135 : Blo 2051435 2052135 := bstep (se 1 (by rfl) ⟨1539101, by rfl⟩ : syracuseStep 2052135 = 3078203) B3078203
theorem B2308657 : Blo 2051435 2308657 := bbase (se 2 (by rfl) ⟨865746, by rfl⟩ : syracuseStep 2308657 = 1731493) (by norm_num)
theorem B3078209 : Blo 2051435 3078209 := bstep (se 2 (by rfl) ⟨1154328, by rfl⟩ : syracuseStep 3078209 = 2308657) B2308657
theorem B2052139 : Blo 2051435 2052139 := bstep (se 1 (by rfl) ⟨1539104, by rfl⟩ : syracuseStep 2052139 = 3078209) B3078209
theorem B6574277 : Blo 2051435 6574277 := bbase (se 4 (by rfl) ⟨616338, by rfl⟩ : syracuseStep 6574277 = 1232677) (by norm_num)
theorem B4382851 : Blo 2051435 4382851 := bstep (se 1 (by rfl) ⟨3287138, by rfl⟩ : syracuseStep 4382851 = 6574277) B6574277
theorem B5843801 : Blo 2051435 5843801 := bstep (se 2 (by rfl) ⟨2191425, by rfl⟩ : syracuseStep 5843801 = 4382851) B4382851
theorem B3895867 : Blo 2051435 3895867 := bstep (se 1 (by rfl) ⟨2921900, by rfl⟩ : syracuseStep 3895867 = 5843801) B5843801
theorem B5194489 : Blo 2051435 5194489 := bstep (se 2 (by rfl) ⟨1947933, by rfl⟩ : syracuseStep 5194489 = 3895867) B3895867
theorem B6925985 : Blo 2051435 6925985 := bstep (se 2 (by rfl) ⟨2597244, by rfl⟩ : syracuseStep 6925985 = 5194489) B5194489
theorem B4617323 : Blo 2051435 4617323 := bstep (se 1 (by rfl) ⟨3462992, by rfl⟩ : syracuseStep 4617323 = 6925985) B6925985
theorem B3078215 : Blo 2051435 3078215 := bstep (se 1 (by rfl) ⟨2308661, by rfl⟩ : syracuseStep 3078215 = 4617323) B4617323
theorem B2052143 : Blo 2051435 2052143 := bstep (se 1 (by rfl) ⟨1539107, by rfl⟩ : syracuseStep 2052143 = 3078215) B3078215
theorem B3078221 : Blo 2051435 3078221 := bbase (se 3 (by rfl) ⟨577166, by rfl⟩ : syracuseStep 3078221 = 1154333) (by norm_num)
theorem B2052147 : Blo 2051435 2052147 := bstep (se 1 (by rfl) ⟨1539110, by rfl⟩ : syracuseStep 2052147 = 3078221) B3078221
theorem B4617341 : Blo 2051435 4617341 := bbase (se 3 (by rfl) ⟨865751, by rfl⟩ : syracuseStep 4617341 = 1731503) (by norm_num)
theorem B3078227 : Blo 2051435 3078227 := bstep (se 1 (by rfl) ⟨2308670, by rfl⟩ : syracuseStep 3078227 = 4617341) B4617341
theorem B2052151 : Blo 2051435 2052151 := bstep (se 1 (by rfl) ⟨1539113, by rfl⟩ : syracuseStep 2052151 = 3078227) B3078227
theorem B3463013 : Blo 2051435 3463013 := bbase (se 4 (by rfl) ⟨324657, by rfl⟩ : syracuseStep 3463013 = 649315) (by norm_num)
theorem B2308675 : Blo 2051435 2308675 := bstep (se 1 (by rfl) ⟨1731506, by rfl⟩ : syracuseStep 2308675 = 3463013) B3463013
theorem B3078233 : Blo 2051435 3078233 := bstep (se 2 (by rfl) ⟨1154337, by rfl⟩ : syracuseStep 3078233 = 2308675) B2308675
theorem B2052155 : Blo 2051435 2052155 := bstep (se 1 (by rfl) ⟨1539116, by rfl⟩ : syracuseStep 2052155 = 3078233) B3078233
theorem B4382885 : Blo 2051435 4382885 := bbase (se 4 (by rfl) ⟨410895, by rfl⟩ : syracuseStep 4382885 = 821791) (by norm_num)
theorem B2921923 : Blo 2051435 2921923 := bstep (se 1 (by rfl) ⟨2191442, by rfl⟩ : syracuseStep 2921923 = 4382885) B4382885
theorem B15583589 : Blo 2051435 15583589 := bstep (se 4 (by rfl) ⟨1460961, by rfl⟩ : syracuseStep 15583589 = 2921923) B2921923
theorem B10389059 : Blo 2051435 10389059 := bstep (se 1 (by rfl) ⟨7791794, by rfl⟩ : syracuseStep 10389059 = 15583589) B15583589
theorem B6926039 : Blo 2051435 6926039 := bstep (se 1 (by rfl) ⟨5194529, by rfl⟩ : syracuseStep 6926039 = 10389059) B10389059
theorem B4617359 : Blo 2051435 4617359 := bstep (se 1 (by rfl) ⟨3463019, by rfl⟩ : syracuseStep 4617359 = 6926039) B6926039
theorem B3078239 : Blo 2051435 3078239 := bstep (se 1 (by rfl) ⟨2308679, by rfl⟩ : syracuseStep 3078239 = 4617359) B4617359
theorem B2052159 : Blo 2051435 2052159 := bstep (se 1 (by rfl) ⟨1539119, by rfl⟩ : syracuseStep 2052159 = 3078239) B3078239
theorem B3078245 : Blo 2051435 3078245 := bbase (se 4 (by rfl) ⟨288585, by rfl⟩ : syracuseStep 3078245 = 577171) (by norm_num)
theorem B2052163 : Blo 2051435 2052163 := bstep (se 1 (by rfl) ⟨1539122, by rfl⟩ : syracuseStep 2052163 = 3078245) B3078245
theorem B3949069 : Blo 2051435 3949069 := bbase (se 3 (by rfl) ⟨740450, by rfl⟩ : syracuseStep 3949069 = 1480901) (by norm_num)
theorem B5265425 : Blo 2051435 5265425 := bstep (se 2 (by rfl) ⟨1974534, by rfl⟩ : syracuseStep 5265425 = 3949069) B3949069
theorem B14041133 : Blo 2051435 14041133 := bstep (se 3 (by rfl) ⟨2632712, by rfl⟩ : syracuseStep 14041133 = 5265425) B5265425
theorem B9360755 : Blo 2051435 9360755 := bstep (se 1 (by rfl) ⟨7020566, by rfl⟩ : syracuseStep 9360755 = 14041133) B14041133
theorem B6240503 : Blo 2051435 6240503 := bstep (se 1 (by rfl) ⟨4680377, by rfl⟩ : syracuseStep 6240503 = 9360755) B9360755
theorem B4160335 : Blo 2051435 4160335 := bstep (se 1 (by rfl) ⟨3120251, by rfl⟩ : syracuseStep 4160335 = 6240503) B6240503
theorem B5547113 : Blo 2051435 5547113 := bstep (se 2 (by rfl) ⟨2080167, by rfl⟩ : syracuseStep 5547113 = 4160335) B4160335
theorem B3698075 : Blo 2051435 3698075 := bstep (se 1 (by rfl) ⟨2773556, by rfl⟩ : syracuseStep 3698075 = 5547113) B5547113
theorem B9861533 : Blo 2051435 9861533 := bstep (se 3 (by rfl) ⟨1849037, by rfl⟩ : syracuseStep 9861533 = 3698075) B3698075
theorem B6574355 : Blo 2051435 6574355 := bstep (se 1 (by rfl) ⟨4930766, by rfl⟩ : syracuseStep 6574355 = 9861533) B9861533
theorem B4382903 : Blo 2051435 4382903 := bstep (se 1 (by rfl) ⟨3287177, by rfl⟩ : syracuseStep 4382903 = 6574355) B6574355
theorem B2921935 : Blo 2051435 2921935 := bstep (se 1 (by rfl) ⟨2191451, by rfl⟩ : syracuseStep 2921935 = 4382903) B4382903
theorem B3895913 : Blo 2051435 3895913 := bstep (se 2 (by rfl) ⟨1460967, by rfl⟩ : syracuseStep 3895913 = 2921935) B2921935
theorem B2597275 : Blo 2051435 2597275 := bstep (se 1 (by rfl) ⟨1947956, by rfl⟩ : syracuseStep 2597275 = 3895913) B3895913
theorem B3463033 : Blo 2051435 3463033 := bstep (se 2 (by rfl) ⟨1298637, by rfl⟩ : syracuseStep 3463033 = 2597275) B2597275
theorem B4617377 : Blo 2051435 4617377 := bstep (se 2 (by rfl) ⟨1731516, by rfl⟩ : syracuseStep 4617377 = 3463033) B3463033
theorem B3078251 : Blo 2051435 3078251 := bstep (se 1 (by rfl) ⟨2308688, by rfl⟩ : syracuseStep 3078251 = 4617377) B4617377
theorem B2052167 : Blo 2051435 2052167 := bstep (se 1 (by rfl) ⟨1539125, by rfl⟩ : syracuseStep 2052167 = 3078251) B3078251
theorem B2308693 : Blo 2051435 2308693 := bbase (se 8 (by rfl) ⟨13527, by rfl⟩ : syracuseStep 2308693 = 27055) (by norm_num)
theorem B3078257 : Blo 2051435 3078257 := bstep (se 2 (by rfl) ⟨1154346, by rfl⟩ : syracuseStep 3078257 = 2308693) B2308693
theorem B2052171 : Blo 2051435 2052171 := bstep (se 1 (by rfl) ⟨1539128, by rfl⟩ : syracuseStep 2052171 = 3078257) B3078257
theorem B2597285 : Blo 2051435 2597285 := bbase (se 4 (by rfl) ⟨243495, by rfl⟩ : syracuseStep 2597285 = 486991) (by norm_num)
theorem B6926093 : Blo 2051435 6926093 := bstep (se 3 (by rfl) ⟨1298642, by rfl⟩ : syracuseStep 6926093 = 2597285) B2597285
theorem B4617395 : Blo 2051435 4617395 := bstep (se 1 (by rfl) ⟨3463046, by rfl⟩ : syracuseStep 4617395 = 6926093) B6926093
theorem B3078263 : Blo 2051435 3078263 := bstep (se 1 (by rfl) ⟨2308697, by rfl⟩ : syracuseStep 3078263 = 4617395) B4617395
theorem B2052175 : Blo 2051435 2052175 := bstep (se 1 (by rfl) ⟨1539131, by rfl⟩ : syracuseStep 2052175 = 3078263) B3078263
theorem B3078269 : Blo 2051435 3078269 := bbase (se 3 (by rfl) ⟨577175, by rfl⟩ : syracuseStep 3078269 = 1154351) (by norm_num)
theorem B2052179 : Blo 2051435 2052179 := bstep (se 1 (by rfl) ⟨1539134, by rfl⟩ : syracuseStep 2052179 = 3078269) B3078269
theorem B4617413 : Blo 2051435 4617413 := bbase (se 4 (by rfl) ⟨432882, by rfl⟩ : syracuseStep 4617413 = 865765) (by norm_num)
theorem B3078275 : Blo 2051435 3078275 := bstep (se 1 (by rfl) ⟨2308706, by rfl⟩ : syracuseStep 3078275 = 4617413) B4617413
theorem B2052183 : Blo 2051435 2052183 := bstep (se 1 (by rfl) ⟨1539137, by rfl⟩ : syracuseStep 2052183 = 3078275) B3078275
theorem B8434277 : Blo 2051435 8434277 := bbase (se 4 (by rfl) ⟨790713, by rfl⟩ : syracuseStep 8434277 = 1581427) (by norm_num)
theorem B5622851 : Blo 2051435 5622851 := bstep (se 1 (by rfl) ⟨4217138, by rfl⟩ : syracuseStep 5622851 = 8434277) B8434277
theorem B3748567 : Blo 2051435 3748567 := bstep (se 1 (by rfl) ⟨2811425, by rfl⟩ : syracuseStep 3748567 = 5622851) B5622851
theorem B4998089 : Blo 2051435 4998089 := bstep (se 2 (by rfl) ⟨1874283, by rfl⟩ : syracuseStep 4998089 = 3748567) B3748567
theorem B3332059 : Blo 2051435 3332059 := bstep (se 1 (by rfl) ⟨2499044, by rfl⟩ : syracuseStep 3332059 = 4998089) B4998089
theorem B71083925 : Blo 2051435 71083925 := bstep (se 6 (by rfl) ⟨1666029, by rfl⟩ : syracuseStep 71083925 = 3332059) B3332059
theorem B47389283 : Blo 2051435 47389283 := bstep (se 1 (by rfl) ⟨35541962, by rfl⟩ : syracuseStep 47389283 = 71083925) B71083925
theorem B31592855 : Blo 2051435 31592855 := bstep (se 1 (by rfl) ⟨23694641, by rfl⟩ : syracuseStep 31592855 = 47389283) B47389283
theorem B21061903 : Blo 2051435 21061903 := bstep (se 1 (by rfl) ⟨15796427, by rfl⟩ : syracuseStep 21061903 = 31592855) B31592855
theorem B28082537 : Blo 2051435 28082537 := bstep (se 2 (by rfl) ⟨10530951, by rfl⟩ : syracuseStep 28082537 = 21061903) B21061903
theorem B18721691 : Blo 2051435 18721691 := bstep (se 1 (by rfl) ⟨14041268, by rfl⟩ : syracuseStep 18721691 = 28082537) B28082537
theorem B12481127 : Blo 2051435 12481127 := bstep (se 1 (by rfl) ⟨9360845, by rfl⟩ : syracuseStep 12481127 = 18721691) B18721691
theorem B8320751 : Blo 2051435 8320751 := bstep (se 1 (by rfl) ⟨6240563, by rfl⟩ : syracuseStep 8320751 = 12481127) B12481127
theorem B5547167 : Blo 2051435 5547167 := bstep (se 1 (by rfl) ⟨4160375, by rfl⟩ : syracuseStep 5547167 = 8320751) B8320751
theorem B3698111 : Blo 2051435 3698111 := bstep (se 1 (by rfl) ⟨2773583, by rfl⟩ : syracuseStep 3698111 = 5547167) B5547167
theorem B2465407 : Blo 2051435 2465407 := bstep (se 1 (by rfl) ⟨1849055, by rfl⟩ : syracuseStep 2465407 = 3698111) B3698111
theorem B13148837 : Blo 2051435 13148837 := bstep (se 4 (by rfl) ⟨1232703, by rfl⟩ : syracuseStep 13148837 = 2465407) B2465407
theorem B8765891 : Blo 2051435 8765891 := bstep (se 1 (by rfl) ⟨6574418, by rfl⟩ : syracuseStep 8765891 = 13148837) B13148837
theorem B5843927 : Blo 2051435 5843927 := bstep (se 1 (by rfl) ⟨4382945, by rfl⟩ : syracuseStep 5843927 = 8765891) B8765891
theorem B3895951 : Blo 2051435 3895951 := bstep (se 1 (by rfl) ⟨2921963, by rfl⟩ : syracuseStep 3895951 = 5843927) B5843927
theorem B5194601 : Blo 2051435 5194601 := bstep (se 2 (by rfl) ⟨1947975, by rfl⟩ : syracuseStep 5194601 = 3895951) B3895951
theorem B3463067 : Blo 2051435 3463067 := bstep (se 1 (by rfl) ⟨2597300, by rfl⟩ : syracuseStep 3463067 = 5194601) B5194601
theorem B2308711 : Blo 2051435 2308711 := bstep (se 1 (by rfl) ⟨1731533, by rfl⟩ : syracuseStep 2308711 = 3463067) B3463067
theorem B3078281 : Blo 2051435 3078281 := bstep (se 2 (by rfl) ⟨1154355, by rfl⟩ : syracuseStep 3078281 = 2308711) B2308711
theorem B2052187 : Blo 2051435 2052187 := bstep (se 1 (by rfl) ⟨1539140, by rfl⟩ : syracuseStep 2052187 = 3078281) B3078281
theorem B10389221 : Blo 2051435 10389221 := bbase (se 4 (by rfl) ⟨973989, by rfl⟩ : syracuseStep 10389221 = 1947979) (by norm_num)
theorem B6926147 : Blo 2051435 6926147 := bstep (se 1 (by rfl) ⟨5194610, by rfl⟩ : syracuseStep 6926147 = 10389221) B10389221
theorem B4617431 : Blo 2051435 4617431 := bstep (se 1 (by rfl) ⟨3463073, by rfl⟩ : syracuseStep 4617431 = 6926147) B6926147
theorem B3078287 : Blo 2051435 3078287 := bstep (se 1 (by rfl) ⟨2308715, by rfl⟩ : syracuseStep 3078287 = 4617431) B4617431
theorem B2052191 : Blo 2051435 2052191 := bstep (se 1 (by rfl) ⟨1539143, by rfl⟩ : syracuseStep 2052191 = 3078287) B3078287
theorem B3078293 : Blo 2051435 3078293 := bbase (se 6 (by rfl) ⟨72147, by rfl⟩ : syracuseStep 3078293 = 144295) (by norm_num)
theorem B2052195 : Blo 2051435 2052195 := bstep (se 1 (by rfl) ⟨1539146, by rfl⟩ : syracuseStep 2052195 = 3078293) B3078293
theorem B8765941 : Blo 2051435 8765941 := bbase (se 5 (by rfl) ⟨410903, by rfl⟩ : syracuseStep 8765941 = 821807) (by norm_num)
theorem B11687921 : Blo 2051435 11687921 := bstep (se 2 (by rfl) ⟨4382970, by rfl⟩ : syracuseStep 11687921 = 8765941) B8765941
theorem B7791947 : Blo 2051435 7791947 := bstep (se 1 (by rfl) ⟨5843960, by rfl⟩ : syracuseStep 7791947 = 11687921) B11687921
theorem B5194631 : Blo 2051435 5194631 := bstep (se 1 (by rfl) ⟨3895973, by rfl⟩ : syracuseStep 5194631 = 7791947) B7791947
theorem B3463087 : Blo 2051435 3463087 := bstep (se 1 (by rfl) ⟨2597315, by rfl⟩ : syracuseStep 3463087 = 5194631) B5194631
theorem B4617449 : Blo 2051435 4617449 := bstep (se 2 (by rfl) ⟨1731543, by rfl⟩ : syracuseStep 4617449 = 3463087) B3463087
theorem B3078299 : Blo 2051435 3078299 := bstep (se 1 (by rfl) ⟨2308724, by rfl⟩ : syracuseStep 3078299 = 4617449) B4617449
theorem B2052199 : Blo 2051435 2052199 := bstep (se 1 (by rfl) ⟨1539149, by rfl⟩ : syracuseStep 2052199 = 3078299) B3078299
theorem B2308729 : Blo 2051435 2308729 := bbase (se 2 (by rfl) ⟨865773, by rfl⟩ : syracuseStep 2308729 = 1731547) (by norm_num)
theorem B3078305 : Blo 2051435 3078305 := bstep (se 2 (by rfl) ⟨1154364, by rfl⟩ : syracuseStep 3078305 = 2308729) B2308729
theorem B2052203 : Blo 2051435 2052203 := bstep (se 1 (by rfl) ⟨1539152, by rfl⟩ : syracuseStep 2052203 = 3078305) B3078305
theorem B19723445 : Blo 2051435 19723445 := bbase (se 5 (by rfl) ⟨924536, by rfl⟩ : syracuseStep 19723445 = 1849073) (by norm_num)
theorem B13148963 : Blo 2051435 13148963 := bstep (se 1 (by rfl) ⟨9861722, by rfl⟩ : syracuseStep 13148963 = 19723445) B19723445
theorem B8765975 : Blo 2051435 8765975 := bstep (se 1 (by rfl) ⟨6574481, by rfl⟩ : syracuseStep 8765975 = 13148963) B13148963
theorem B5843983 : Blo 2051435 5843983 := bstep (se 1 (by rfl) ⟨4382987, by rfl⟩ : syracuseStep 5843983 = 8765975) B8765975
theorem B7791977 : Blo 2051435 7791977 := bstep (se 2 (by rfl) ⟨2921991, by rfl⟩ : syracuseStep 7791977 = 5843983) B5843983
theorem B5194651 : Blo 2051435 5194651 := bstep (se 1 (by rfl) ⟨3895988, by rfl⟩ : syracuseStep 5194651 = 7791977) B7791977
theorem B6926201 : Blo 2051435 6926201 := bstep (se 2 (by rfl) ⟨2597325, by rfl⟩ : syracuseStep 6926201 = 5194651) B5194651
theorem B4617467 : Blo 2051435 4617467 := bstep (se 1 (by rfl) ⟨3463100, by rfl⟩ : syracuseStep 4617467 = 6926201) B6926201
theorem B3078311 : Blo 2051435 3078311 := bstep (se 1 (by rfl) ⟨2308733, by rfl⟩ : syracuseStep 3078311 = 4617467) B4617467
theorem B2052207 : Blo 2051435 2052207 := bstep (se 1 (by rfl) ⟨1539155, by rfl⟩ : syracuseStep 2052207 = 3078311) B3078311
theorem B3078317 : Blo 2051435 3078317 := bbase (se 3 (by rfl) ⟨577184, by rfl⟩ : syracuseStep 3078317 = 1154369) (by norm_num)
theorem B2052211 : Blo 2051435 2052211 := bstep (se 1 (by rfl) ⟨1539158, by rfl⟩ : syracuseStep 2052211 = 3078317) B3078317
theorem B4617485 : Blo 2051435 4617485 := bbase (se 3 (by rfl) ⟨865778, by rfl⟩ : syracuseStep 4617485 = 1731557) (by norm_num)
theorem B3078323 : Blo 2051435 3078323 := bstep (se 1 (by rfl) ⟨2308742, by rfl⟩ : syracuseStep 3078323 = 4617485) B4617485
theorem B2052215 : Blo 2051435 2052215 := bstep (se 1 (by rfl) ⟨1539161, by rfl⟩ : syracuseStep 2052215 = 3078323) B3078323
theorem B2597341 : Blo 2051435 2597341 := bbase (se 3 (by rfl) ⟨487001, by rfl⟩ : syracuseStep 2597341 = 974003) (by norm_num)
theorem B3463121 : Blo 2051435 3463121 := bstep (se 2 (by rfl) ⟨1298670, by rfl⟩ : syracuseStep 3463121 = 2597341) B2597341
theorem B2308747 : Blo 2051435 2308747 := bstep (se 1 (by rfl) ⟨1731560, by rfl⟩ : syracuseStep 2308747 = 3463121) B3463121
theorem B3078329 : Blo 2051435 3078329 := bstep (se 2 (by rfl) ⟨1154373, by rfl⟩ : syracuseStep 3078329 = 2308747) B2308747
theorem B2052219 : Blo 2051435 2052219 := bstep (se 1 (by rfl) ⟨1539164, by rfl⟩ : syracuseStep 2052219 = 3078329) B3078329
theorem B17532085 : Blo 2051435 17532085 := bbase (se 5 (by rfl) ⟨821816, by rfl⟩ : syracuseStep 17532085 = 1643633) (by norm_num)
theorem B23376113 : Blo 2051435 23376113 := bstep (se 2 (by rfl) ⟨8766042, by rfl⟩ : syracuseStep 23376113 = 17532085) B17532085
theorem B15584075 : Blo 2051435 15584075 := bstep (se 1 (by rfl) ⟨11688056, by rfl⟩ : syracuseStep 15584075 = 23376113) B23376113
theorem B10389383 : Blo 2051435 10389383 := bstep (se 1 (by rfl) ⟨7792037, by rfl⟩ : syracuseStep 10389383 = 15584075) B15584075
theorem B6926255 : Blo 2051435 6926255 := bstep (se 1 (by rfl) ⟨5194691, by rfl⟩ : syracuseStep 6926255 = 10389383) B10389383
theorem B4617503 : Blo 2051435 4617503 := bstep (se 1 (by rfl) ⟨3463127, by rfl⟩ : syracuseStep 4617503 = 6926255) B6926255
theorem B3078335 : Blo 2051435 3078335 := bstep (se 1 (by rfl) ⟨2308751, by rfl⟩ : syracuseStep 3078335 = 4617503) B4617503
theorem B2052223 : Blo 2051435 2052223 := bstep (se 1 (by rfl) ⟨1539167, by rfl⟩ : syracuseStep 2052223 = 3078335) B3078335
theorem B3078341 : Blo 2051435 3078341 := bbase (se 4 (by rfl) ⟨288594, by rfl⟩ : syracuseStep 3078341 = 577189) (by norm_num)
theorem B2052227 : Blo 2051435 2052227 := bstep (se 1 (by rfl) ⟨1539170, by rfl⟩ : syracuseStep 2052227 = 3078341) B3078341
theorem B3463141 : Blo 2051435 3463141 := bbase (se 4 (by rfl) ⟨324669, by rfl⟩ : syracuseStep 3463141 = 649339) (by norm_num)
theorem B4617521 : Blo 2051435 4617521 := bstep (se 2 (by rfl) ⟨1731570, by rfl⟩ : syracuseStep 4617521 = 3463141) B3463141
theorem B3078347 : Blo 2051435 3078347 := bstep (se 1 (by rfl) ⟨2308760, by rfl⟩ : syracuseStep 3078347 = 4617521) B4617521
theorem B2052231 : Blo 2051435 2052231 := bstep (se 1 (by rfl) ⟨1539173, by rfl⟩ : syracuseStep 2052231 = 3078347) B3078347
theorem B2308765 : Blo 2051435 2308765 := bbase (se 3 (by rfl) ⟨432893, by rfl⟩ : syracuseStep 2308765 = 865787) (by norm_num)
theorem B3078353 : Blo 2051435 3078353 := bstep (se 2 (by rfl) ⟨1154382, by rfl⟩ : syracuseStep 3078353 = 2308765) B2308765
theorem B2052235 : Blo 2051435 2052235 := bstep (se 1 (by rfl) ⟨1539176, by rfl⟩ : syracuseStep 2052235 = 3078353) B3078353
theorem B6926309 : Blo 2051435 6926309 := bbase (se 4 (by rfl) ⟨649341, by rfl⟩ : syracuseStep 6926309 = 1298683) (by norm_num)
theorem B4617539 : Blo 2051435 4617539 := bstep (se 1 (by rfl) ⟨3463154, by rfl⟩ : syracuseStep 4617539 = 6926309) B6926309
theorem B3078359 : Blo 2051435 3078359 := bstep (se 1 (by rfl) ⟨2308769, by rfl⟩ : syracuseStep 3078359 = 4617539) B4617539
theorem B2052239 : Blo 2051435 2052239 := bstep (se 1 (by rfl) ⟨1539179, by rfl⟩ : syracuseStep 2052239 = 3078359) B3078359
theorem B3078365 : Blo 2051435 3078365 := bbase (se 3 (by rfl) ⟨577193, by rfl⟩ : syracuseStep 3078365 = 1154387) (by norm_num)
theorem B2052243 : Blo 2051435 2052243 := bstep (se 1 (by rfl) ⟨1539182, by rfl⟩ : syracuseStep 2052243 = 3078365) B3078365
theorem B4617557 : Blo 2051435 4617557 := bbase (se 13 (by rfl) ⟨845, by rfl⟩ : syracuseStep 4617557 = 1691) (by norm_num)
theorem B3078371 : Blo 2051435 3078371 := bstep (se 1 (by rfl) ⟨2308778, by rfl⟩ : syracuseStep 3078371 = 4617557) B4617557
theorem B2052247 : Blo 2051435 2052247 := bstep (se 1 (by rfl) ⟨1539185, by rfl⟩ : syracuseStep 2052247 = 3078371) B3078371
theorem B2191541 : Blo 2051435 2191541 := bbase (se 5 (by rfl) ⟨102728, by rfl⟩ : syracuseStep 2191541 = 205457) (by norm_num)
theorem B5844109 : Blo 2051435 5844109 := bstep (se 3 (by rfl) ⟨1095770, by rfl⟩ : syracuseStep 5844109 = 2191541) B2191541
theorem B7792145 : Blo 2051435 7792145 := bstep (se 2 (by rfl) ⟨2922054, by rfl⟩ : syracuseStep 7792145 = 5844109) B5844109
theorem B5194763 : Blo 2051435 5194763 := bstep (se 1 (by rfl) ⟨3896072, by rfl⟩ : syracuseStep 5194763 = 7792145) B7792145
theorem B3463175 : Blo 2051435 3463175 := bstep (se 1 (by rfl) ⟨2597381, by rfl⟩ : syracuseStep 3463175 = 5194763) B5194763
theorem B2308783 : Blo 2051435 2308783 := bstep (se 1 (by rfl) ⟨1731587, by rfl⟩ : syracuseStep 2308783 = 3463175) B3463175
theorem B3078377 : Blo 2051435 3078377 := bstep (se 2 (by rfl) ⟨1154391, by rfl⟩ : syracuseStep 3078377 = 2308783) B2308783
theorem B2052251 : Blo 2051435 2052251 := bstep (se 1 (by rfl) ⟨1539188, by rfl⟩ : syracuseStep 2052251 = 3078377) B3078377
theorem B9007013 : Blo 2051435 9007013 := bbase (se 4 (by rfl) ⟨844407, by rfl⟩ : syracuseStep 9007013 = 1688815) (by norm_num)
theorem B6004675 : Blo 2051435 6004675 := bstep (se 1 (by rfl) ⟨4503506, by rfl⟩ : syracuseStep 6004675 = 9007013) B9007013
theorem B8006233 : Blo 2051435 8006233 := bstep (se 2 (by rfl) ⟨3002337, by rfl⟩ : syracuseStep 8006233 = 6004675) B6004675
theorem B683198549 : Blo 2051435 683198549 := bstep (se 8 (by rfl) ⟨4003116, by rfl⟩ : syracuseStep 683198549 = 8006233) B8006233
theorem B455465699 : Blo 2051435 455465699 := bstep (se 1 (by rfl) ⟨341599274, by rfl⟩ : syracuseStep 455465699 = 683198549) B683198549
theorem B303643799 : Blo 2051435 303643799 := bstep (se 1 (by rfl) ⟨227732849, by rfl⟩ : syracuseStep 303643799 = 455465699) B455465699
theorem B202429199 : Blo 2051435 202429199 := bstep (se 1 (by rfl) ⟨151821899, by rfl⟩ : syracuseStep 202429199 = 303643799) B303643799
theorem B134952799 : Blo 2051435 134952799 := bstep (se 1 (by rfl) ⟨101214599, by rfl⟩ : syracuseStep 134952799 = 202429199) B202429199
theorem B179937065 : Blo 2051435 179937065 := bstep (se 2 (by rfl) ⟨67476399, by rfl⟩ : syracuseStep 179937065 = 134952799) B134952799
theorem B119958043 : Blo 2051435 119958043 := bstep (se 1 (by rfl) ⟨89968532, by rfl⟩ : syracuseStep 119958043 = 179937065) B179937065
theorem B159944057 : Blo 2051435 159944057 := bstep (se 2 (by rfl) ⟨59979021, by rfl⟩ : syracuseStep 159944057 = 119958043) B119958043
theorem B106629371 : Blo 2051435 106629371 := bstep (se 1 (by rfl) ⟨79972028, by rfl⟩ : syracuseStep 106629371 = 159944057) B159944057
theorem B71086247 : Blo 2051435 71086247 := bstep (se 1 (by rfl) ⟨53314685, by rfl⟩ : syracuseStep 71086247 = 106629371) B106629371
theorem B47390831 : Blo 2051435 47390831 := bstep (se 1 (by rfl) ⟨35543123, by rfl⟩ : syracuseStep 47390831 = 71086247) B71086247
theorem B31593887 : Blo 2051435 31593887 := bstep (se 1 (by rfl) ⟨23695415, by rfl⟩ : syracuseStep 31593887 = 47390831) B47390831
theorem B21062591 : Blo 2051435 21062591 := bstep (se 1 (by rfl) ⟨15796943, by rfl⟩ : syracuseStep 21062591 = 31593887) B31593887
theorem B14041727 : Blo 2051435 14041727 := bstep (se 1 (by rfl) ⟨10531295, by rfl⟩ : syracuseStep 14041727 = 21062591) B21062591
theorem B9361151 : Blo 2051435 9361151 := bstep (se 1 (by rfl) ⟨7020863, by rfl⟩ : syracuseStep 9361151 = 14041727) B14041727
theorem B6240767 : Blo 2051435 6240767 := bstep (se 1 (by rfl) ⟨4680575, by rfl⟩ : syracuseStep 6240767 = 9361151) B9361151
theorem B16642045 : Blo 2051435 16642045 := bstep (se 3 (by rfl) ⟨3120383, by rfl⟩ : syracuseStep 16642045 = 6240767) B6240767
theorem B22189393 : Blo 2051435 22189393 := bstep (se 2 (by rfl) ⟨8321022, by rfl⟩ : syracuseStep 22189393 = 16642045) B16642045
theorem B29585857 : Blo 2051435 29585857 := bstep (se 2 (by rfl) ⟨11094696, by rfl⟩ : syracuseStep 29585857 = 22189393) B22189393
theorem B39447809 : Blo 2051435 39447809 := bstep (se 2 (by rfl) ⟨14792928, by rfl⟩ : syracuseStep 39447809 = 29585857) B29585857
theorem B26298539 : Blo 2051435 26298539 := bstep (se 1 (by rfl) ⟨19723904, by rfl⟩ : syracuseStep 26298539 = 39447809) B39447809
theorem B17532359 : Blo 2051435 17532359 := bstep (se 1 (by rfl) ⟨13149269, by rfl⟩ : syracuseStep 17532359 = 26298539) B26298539
theorem B11688239 : Blo 2051435 11688239 := bstep (se 1 (by rfl) ⟨8766179, by rfl⟩ : syracuseStep 11688239 = 17532359) B17532359
theorem B7792159 : Blo 2051435 7792159 := bstep (se 1 (by rfl) ⟨5844119, by rfl⟩ : syracuseStep 7792159 = 11688239) B11688239
theorem B10389545 : Blo 2051435 10389545 := bstep (se 2 (by rfl) ⟨3896079, by rfl⟩ : syracuseStep 10389545 = 7792159) B7792159
theorem B6926363 : Blo 2051435 6926363 := bstep (se 1 (by rfl) ⟨5194772, by rfl⟩ : syracuseStep 6926363 = 10389545) B10389545
theorem B4617575 : Blo 2051435 4617575 := bstep (se 1 (by rfl) ⟨3463181, by rfl⟩ : syracuseStep 4617575 = 6926363) B6926363
theorem B3078383 : Blo 2051435 3078383 := bstep (se 1 (by rfl) ⟨2308787, by rfl⟩ : syracuseStep 3078383 = 4617575) B4617575
theorem B2052255 : Blo 2051435 2052255 := bstep (se 1 (by rfl) ⟨1539191, by rfl⟩ : syracuseStep 2052255 = 3078383) B3078383
theorem B3078389 : Blo 2051435 3078389 := bbase (se 5 (by rfl) ⟨144299, by rfl⟩ : syracuseStep 3078389 = 288599) (by norm_num)
theorem B2052259 : Blo 2051435 2052259 := bstep (se 1 (by rfl) ⟨1539194, by rfl⟩ : syracuseStep 2052259 = 3078389) B3078389
theorem B3949253 : Blo 2051435 3949253 := bbase (se 4 (by rfl) ⟨370242, by rfl⟩ : syracuseStep 3949253 = 740485) (by norm_num)
theorem B2632835 : Blo 2051435 2632835 := bstep (se 1 (by rfl) ⟨1974626, by rfl⟩ : syracuseStep 2632835 = 3949253) B3949253
theorem B7020893 : Blo 2051435 7020893 := bstep (se 3 (by rfl) ⟨1316417, by rfl⟩ : syracuseStep 7020893 = 2632835) B2632835
theorem B4680595 : Blo 2051435 4680595 := bstep (se 1 (by rfl) ⟨3510446, by rfl⟩ : syracuseStep 4680595 = 7020893) B7020893
theorem B6240793 : Blo 2051435 6240793 := bstep (se 2 (by rfl) ⟨2340297, by rfl⟩ : syracuseStep 6240793 = 4680595) B4680595
theorem B8321057 : Blo 2051435 8321057 := bstep (se 2 (by rfl) ⟨3120396, by rfl⟩ : syracuseStep 8321057 = 6240793) B6240793
theorem B5547371 : Blo 2051435 5547371 := bstep (se 1 (by rfl) ⟨4160528, by rfl⟩ : syracuseStep 5547371 = 8321057) B8321057
theorem B14792989 : Blo 2051435 14792989 := bstep (se 3 (by rfl) ⟨2773685, by rfl⟩ : syracuseStep 14792989 = 5547371) B5547371
theorem B19723985 : Blo 2051435 19723985 := bstep (se 2 (by rfl) ⟨7396494, by rfl⟩ : syracuseStep 19723985 = 14792989) B14792989
theorem B13149323 : Blo 2051435 13149323 := bstep (se 1 (by rfl) ⟨9861992, by rfl⟩ : syracuseStep 13149323 = 19723985) B19723985
theorem B8766215 : Blo 2051435 8766215 := bstep (se 1 (by rfl) ⟨6574661, by rfl⟩ : syracuseStep 8766215 = 13149323) B13149323
theorem B5844143 : Blo 2051435 5844143 := bstep (se 1 (by rfl) ⟨4383107, by rfl⟩ : syracuseStep 5844143 = 8766215) B8766215
theorem B3896095 : Blo 2051435 3896095 := bstep (se 1 (by rfl) ⟨2922071, by rfl⟩ : syracuseStep 3896095 = 5844143) B5844143
theorem B5194793 : Blo 2051435 5194793 := bstep (se 2 (by rfl) ⟨1948047, by rfl⟩ : syracuseStep 5194793 = 3896095) B3896095
theorem B3463195 : Blo 2051435 3463195 := bstep (se 1 (by rfl) ⟨2597396, by rfl⟩ : syracuseStep 3463195 = 5194793) B5194793
theorem B4617593 : Blo 2051435 4617593 := bstep (se 2 (by rfl) ⟨1731597, by rfl⟩ : syracuseStep 4617593 = 3463195) B3463195
theorem B3078395 : Blo 2051435 3078395 := bstep (se 1 (by rfl) ⟨2308796, by rfl⟩ : syracuseStep 3078395 = 4617593) B4617593
theorem B2052263 : Blo 2051435 2052263 := bstep (se 1 (by rfl) ⟨1539197, by rfl⟩ : syracuseStep 2052263 = 3078395) B3078395
theorem B2308801 : Blo 2051435 2308801 := bbase (se 2 (by rfl) ⟨865800, by rfl⟩ : syracuseStep 2308801 = 1731601) (by norm_num)
theorem B3078401 : Blo 2051435 3078401 := bstep (se 2 (by rfl) ⟨1154400, by rfl⟩ : syracuseStep 3078401 = 2308801) B2308801
theorem B2052267 : Blo 2051435 2052267 := bstep (se 1 (by rfl) ⟨1539200, by rfl⟩ : syracuseStep 2052267 = 3078401) B3078401
theorem B5194813 : Blo 2051435 5194813 := bbase (se 3 (by rfl) ⟨974027, by rfl⟩ : syracuseStep 5194813 = 1948055) (by norm_num)
theorem B6926417 : Blo 2051435 6926417 := bstep (se 2 (by rfl) ⟨2597406, by rfl⟩ : syracuseStep 6926417 = 5194813) B5194813
theorem B4617611 : Blo 2051435 4617611 := bstep (se 1 (by rfl) ⟨3463208, by rfl⟩ : syracuseStep 4617611 = 6926417) B6926417
theorem B3078407 : Blo 2051435 3078407 := bstep (se 1 (by rfl) ⟨2308805, by rfl⟩ : syracuseStep 3078407 = 4617611) B4617611
theorem B2052271 : Blo 2051435 2052271 := bstep (se 1 (by rfl) ⟨1539203, by rfl⟩ : syracuseStep 2052271 = 3078407) B3078407
theorem B3078413 : Blo 2051435 3078413 := bbase (se 3 (by rfl) ⟨577202, by rfl⟩ : syracuseStep 3078413 = 1154405) (by norm_num)
theorem B2052275 : Blo 2051435 2052275 := bstep (se 1 (by rfl) ⟨1539206, by rfl⟩ : syracuseStep 2052275 = 3078413) B3078413
theorem B4617629 : Blo 2051435 4617629 := bbase (se 3 (by rfl) ⟨865805, by rfl⟩ : syracuseStep 4617629 = 1731611) (by norm_num)
theorem B3078419 : Blo 2051435 3078419 := bstep (se 1 (by rfl) ⟨2308814, by rfl⟩ : syracuseStep 3078419 = 4617629) B4617629
theorem B2052279 : Blo 2051435 2052279 := bstep (se 1 (by rfl) ⟨1539209, by rfl⟩ : syracuseStep 2052279 = 3078419) B3078419
theorem B3463229 : Blo 2051435 3463229 := bbase (se 3 (by rfl) ⟨649355, by rfl⟩ : syracuseStep 3463229 = 1298711) (by norm_num)
theorem B2308819 : Blo 2051435 2308819 := bstep (se 1 (by rfl) ⟨1731614, by rfl⟩ : syracuseStep 2308819 = 3463229) B3463229
theorem B3078425 : Blo 2051435 3078425 := bstep (se 2 (by rfl) ⟨1154409, by rfl⟩ : syracuseStep 3078425 = 2308819) B2308819
theorem B2052283 : Blo 2051435 2052283 := bstep (se 1 (by rfl) ⟨1539212, by rfl⟩ : syracuseStep 2052283 = 3078425) B3078425
theorem B2080289 : Blo 2051435 2080289 := bbase (se 2 (by rfl) ⟨780108, by rfl⟩ : syracuseStep 2080289 = 1560217) (by norm_num)
theorem B5547437 : Blo 2051435 5547437 := bstep (se 3 (by rfl) ⟨1040144, by rfl⟩ : syracuseStep 5547437 = 2080289) B2080289
theorem B3698291 : Blo 2051435 3698291 := bstep (se 1 (by rfl) ⟨2773718, by rfl⟩ : syracuseStep 3698291 = 5547437) B5547437
theorem B2465527 : Blo 2051435 2465527 := bstep (se 1 (by rfl) ⟨1849145, by rfl⟩ : syracuseStep 2465527 = 3698291) B3698291
theorem B3287369 : Blo 2051435 3287369 := bstep (se 2 (by rfl) ⟨1232763, by rfl⟩ : syracuseStep 3287369 = 2465527) B2465527
theorem B2191579 : Blo 2051435 2191579 := bstep (se 1 (by rfl) ⟨1643684, by rfl⟩ : syracuseStep 2191579 = 3287369) B3287369
theorem B11688421 : Blo 2051435 11688421 := bstep (se 4 (by rfl) ⟨1095789, by rfl⟩ : syracuseStep 11688421 = 2191579) B2191579
theorem B15584561 : Blo 2051435 15584561 := bstep (se 2 (by rfl) ⟨5844210, by rfl⟩ : syracuseStep 15584561 = 11688421) B11688421
theorem B10389707 : Blo 2051435 10389707 := bstep (se 1 (by rfl) ⟨7792280, by rfl⟩ : syracuseStep 10389707 = 15584561) B15584561
theorem B6926471 : Blo 2051435 6926471 := bstep (se 1 (by rfl) ⟨5194853, by rfl⟩ : syracuseStep 6926471 = 10389707) B10389707
theorem B4617647 : Blo 2051435 4617647 := bstep (se 1 (by rfl) ⟨3463235, by rfl⟩ : syracuseStep 4617647 = 6926471) B6926471
theorem B3078431 : Blo 2051435 3078431 := bstep (se 1 (by rfl) ⟨2308823, by rfl⟩ : syracuseStep 3078431 = 4617647) B4617647
theorem B2052287 : Blo 2051435 2052287 := bstep (se 1 (by rfl) ⟨1539215, by rfl⟩ : syracuseStep 2052287 = 3078431) B3078431
theorem B3078437 : Blo 2051435 3078437 := bbase (se 4 (by rfl) ⟨288603, by rfl⟩ : syracuseStep 3078437 = 577207) (by norm_num)
theorem B2052291 : Blo 2051435 2052291 := bstep (se 1 (by rfl) ⟨1539218, by rfl⟩ : syracuseStep 2052291 = 3078437) B3078437
theorem B2597437 : Blo 2051435 2597437 := bbase (se 3 (by rfl) ⟨487019, by rfl⟩ : syracuseStep 2597437 = 974039) (by norm_num)
theorem B3463249 : Blo 2051435 3463249 := bstep (se 2 (by rfl) ⟨1298718, by rfl⟩ : syracuseStep 3463249 = 2597437) B2597437
theorem B4617665 : Blo 2051435 4617665 := bstep (se 2 (by rfl) ⟨1731624, by rfl⟩ : syracuseStep 4617665 = 3463249) B3463249
theorem B3078443 : Blo 2051435 3078443 := bstep (se 1 (by rfl) ⟨2308832, by rfl⟩ : syracuseStep 3078443 = 4617665) B4617665
theorem B2052295 : Blo 2051435 2052295 := bstep (se 1 (by rfl) ⟨1539221, by rfl⟩ : syracuseStep 2052295 = 3078443) B3078443
theorem B2308837 : Blo 2051435 2308837 := bbase (se 4 (by rfl) ⟨216453, by rfl⟩ : syracuseStep 2308837 = 432907) (by norm_num)
theorem B3078449 : Blo 2051435 3078449 := bstep (se 2 (by rfl) ⟨1154418, by rfl⟩ : syracuseStep 3078449 = 2308837) B2308837
theorem B2052299 : Blo 2051435 2052299 := bstep (se 1 (by rfl) ⟨1539224, by rfl⟩ : syracuseStep 2052299 = 3078449) B3078449
theorem B4931093 : Blo 2051435 4931093 := bbase (se 6 (by rfl) ⟨115572, by rfl⟩ : syracuseStep 4931093 = 231145) (by norm_num)
theorem B3287395 : Blo 2051435 3287395 := bstep (se 1 (by rfl) ⟨2465546, by rfl⟩ : syracuseStep 3287395 = 4931093) B4931093
theorem B4383193 : Blo 2051435 4383193 := bstep (se 2 (by rfl) ⟨1643697, by rfl⟩ : syracuseStep 4383193 = 3287395) B3287395
theorem B5844257 : Blo 2051435 5844257 := bstep (se 2 (by rfl) ⟨2191596, by rfl⟩ : syracuseStep 5844257 = 4383193) B4383193
theorem B3896171 : Blo 2051435 3896171 := bstep (se 1 (by rfl) ⟨2922128, by rfl⟩ : syracuseStep 3896171 = 5844257) B5844257
theorem B2597447 : Blo 2051435 2597447 := bstep (se 1 (by rfl) ⟨1948085, by rfl⟩ : syracuseStep 2597447 = 3896171) B3896171
theorem B6926525 : Blo 2051435 6926525 := bstep (se 3 (by rfl) ⟨1298723, by rfl⟩ : syracuseStep 6926525 = 2597447) B2597447
theorem B4617683 : Blo 2051435 4617683 := bstep (se 1 (by rfl) ⟨3463262, by rfl⟩ : syracuseStep 4617683 = 6926525) B6926525
theorem B3078455 : Blo 2051435 3078455 := bstep (se 1 (by rfl) ⟨2308841, by rfl⟩ : syracuseStep 3078455 = 4617683) B4617683
theorem B2052303 : Blo 2051435 2052303 := bstep (se 1 (by rfl) ⟨1539227, by rfl⟩ : syracuseStep 2052303 = 3078455) B3078455
theorem B3078461 : Blo 2051435 3078461 := bbase (se 3 (by rfl) ⟨577211, by rfl⟩ : syracuseStep 3078461 = 1154423) (by norm_num)
theorem B2052307 : Blo 2051435 2052307 := bstep (se 1 (by rfl) ⟨1539230, by rfl⟩ : syracuseStep 2052307 = 3078461) B3078461
theorem B4617701 : Blo 2051435 4617701 := bbase (se 4 (by rfl) ⟨432909, by rfl⟩ : syracuseStep 4617701 = 865819) (by norm_num)
theorem B3078467 : Blo 2051435 3078467 := bstep (se 1 (by rfl) ⟨2308850, by rfl⟩ : syracuseStep 3078467 = 4617701) B4617701
theorem B2052311 : Blo 2051435 2052311 := bstep (se 1 (by rfl) ⟨1539233, by rfl⟩ : syracuseStep 2052311 = 3078467) B3078467
theorem B5194925 : Blo 2051435 5194925 := bbase (se 3 (by rfl) ⟨974048, by rfl⟩ : syracuseStep 5194925 = 1948097) (by norm_num)
theorem B3463283 : Blo 2051435 3463283 := bstep (se 1 (by rfl) ⟨2597462, by rfl⟩ : syracuseStep 3463283 = 5194925) B5194925
theorem B2308855 : Blo 2051435 2308855 := bstep (se 1 (by rfl) ⟨1731641, by rfl⟩ : syracuseStep 2308855 = 3463283) B3463283
theorem B3078473 : Blo 2051435 3078473 := bstep (se 2 (by rfl) ⟨1154427, by rfl⟩ : syracuseStep 3078473 = 2308855) B2308855
theorem B2052315 : Blo 2051435 2052315 := bstep (se 1 (by rfl) ⟨1539236, by rfl⟩ : syracuseStep 2052315 = 3078473) B3078473
theorem B8321285 : Blo 2051435 8321285 := bbase (se 4 (by rfl) ⟨780120, by rfl⟩ : syracuseStep 8321285 = 1560241) (by norm_num)
theorem B5547523 : Blo 2051435 5547523 := bstep (se 1 (by rfl) ⟨4160642, by rfl⟩ : syracuseStep 5547523 = 8321285) B8321285
theorem B7396697 : Blo 2051435 7396697 := bstep (se 2 (by rfl) ⟨2773761, by rfl⟩ : syracuseStep 7396697 = 5547523) B5547523
theorem B4931131 : Blo 2051435 4931131 := bstep (se 1 (by rfl) ⟨3698348, by rfl⟩ : syracuseStep 4931131 = 7396697) B7396697
theorem B6574841 : Blo 2051435 6574841 := bstep (se 2 (by rfl) ⟨2465565, by rfl⟩ : syracuseStep 6574841 = 4931131) B4931131
theorem B4383227 : Blo 2051435 4383227 := bstep (se 1 (by rfl) ⟨3287420, by rfl⟩ : syracuseStep 4383227 = 6574841) B6574841
theorem B2922151 : Blo 2051435 2922151 := bstep (se 1 (by rfl) ⟨2191613, by rfl⟩ : syracuseStep 2922151 = 4383227) B4383227
theorem B3896201 : Blo 2051435 3896201 := bstep (se 2 (by rfl) ⟨1461075, by rfl⟩ : syracuseStep 3896201 = 2922151) B2922151
theorem B10389869 : Blo 2051435 10389869 := bstep (se 3 (by rfl) ⟨1948100, by rfl⟩ : syracuseStep 10389869 = 3896201) B3896201
theorem B6926579 : Blo 2051435 6926579 := bstep (se 1 (by rfl) ⟨5194934, by rfl⟩ : syracuseStep 6926579 = 10389869) B10389869
theorem B4617719 : Blo 2051435 4617719 := bstep (se 1 (by rfl) ⟨3463289, by rfl⟩ : syracuseStep 4617719 = 6926579) B6926579
theorem B3078479 : Blo 2051435 3078479 := bstep (se 1 (by rfl) ⟨2308859, by rfl⟩ : syracuseStep 3078479 = 4617719) B4617719
theorem B2052319 : Blo 2051435 2052319 := bstep (se 1 (by rfl) ⟨1539239, by rfl⟩ : syracuseStep 2052319 = 3078479) B3078479
theorem B3078485 : Blo 2051435 3078485 := bbase (se 10 (by rfl) ⟨4509, by rfl⟩ : syracuseStep 3078485 = 9019) (by norm_num)
theorem B2052323 : Blo 2051435 2052323 := bstep (se 1 (by rfl) ⟨1539242, by rfl⟩ : syracuseStep 2052323 = 3078485) B3078485
theorem B5844325 : Blo 2051435 5844325 := bbase (se 4 (by rfl) ⟨547905, by rfl⟩ : syracuseStep 5844325 = 1095811) (by norm_num)
theorem B7792433 : Blo 2051435 7792433 := bstep (se 2 (by rfl) ⟨2922162, by rfl⟩ : syracuseStep 7792433 = 5844325) B5844325
theorem B5194955 : Blo 2051435 5194955 := bstep (se 1 (by rfl) ⟨3896216, by rfl⟩ : syracuseStep 5194955 = 7792433) B7792433
theorem B3463303 : Blo 2051435 3463303 := bstep (se 1 (by rfl) ⟨2597477, by rfl⟩ : syracuseStep 3463303 = 5194955) B5194955
theorem B4617737 : Blo 2051435 4617737 := bstep (se 2 (by rfl) ⟨1731651, by rfl⟩ : syracuseStep 4617737 = 3463303) B3463303
theorem B3078491 : Blo 2051435 3078491 := bstep (se 1 (by rfl) ⟨2308868, by rfl⟩ : syracuseStep 3078491 = 4617737) B4617737
theorem B2052327 : Blo 2051435 2052327 := bstep (se 1 (by rfl) ⟨1539245, by rfl⟩ : syracuseStep 2052327 = 3078491) B3078491
theorem B2308873 : Blo 2051435 2308873 := bbase (se 2 (by rfl) ⟨865827, by rfl⟩ : syracuseStep 2308873 = 1731655) (by norm_num)
theorem B3078497 : Blo 2051435 3078497 := bstep (se 2 (by rfl) ⟨1154436, by rfl⟩ : syracuseStep 3078497 = 2308873) B2308873
theorem B2052331 : Blo 2051435 2052331 := bstep (se 1 (by rfl) ⟨1539248, by rfl⟩ : syracuseStep 2052331 = 3078497) B3078497
theorem B2080337 : Blo 2051435 2080337 := bbase (se 2 (by rfl) ⟨780126, by rfl⟩ : syracuseStep 2080337 = 1560253) (by norm_num)
theorem B5547565 : Blo 2051435 5547565 := bstep (se 3 (by rfl) ⟨1040168, by rfl⟩ : syracuseStep 5547565 = 2080337) B2080337
theorem B7396753 : Blo 2051435 7396753 := bstep (se 2 (by rfl) ⟨2773782, by rfl⟩ : syracuseStep 7396753 = 5547565) B5547565
theorem B9862337 : Blo 2051435 9862337 := bstep (se 2 (by rfl) ⟨3698376, by rfl⟩ : syracuseStep 9862337 = 7396753) B7396753
theorem B26299565 : Blo 2051435 26299565 := bstep (se 3 (by rfl) ⟨4931168, by rfl⟩ : syracuseStep 26299565 = 9862337) B9862337
theorem B17533043 : Blo 2051435 17533043 := bstep (se 1 (by rfl) ⟨13149782, by rfl⟩ : syracuseStep 17533043 = 26299565) B26299565
theorem B11688695 : Blo 2051435 11688695 := bstep (se 1 (by rfl) ⟨8766521, by rfl⟩ : syracuseStep 11688695 = 17533043) B17533043
theorem B7792463 : Blo 2051435 7792463 := bstep (se 1 (by rfl) ⟨5844347, by rfl⟩ : syracuseStep 7792463 = 11688695) B11688695
theorem B5194975 : Blo 2051435 5194975 := bstep (se 1 (by rfl) ⟨3896231, by rfl⟩ : syracuseStep 5194975 = 7792463) B7792463
theorem B6926633 : Blo 2051435 6926633 := bstep (se 2 (by rfl) ⟨2597487, by rfl⟩ : syracuseStep 6926633 = 5194975) B5194975
theorem B4617755 : Blo 2051435 4617755 := bstep (se 1 (by rfl) ⟨3463316, by rfl⟩ : syracuseStep 4617755 = 6926633) B6926633
theorem B3078503 : Blo 2051435 3078503 := bstep (se 1 (by rfl) ⟨2308877, by rfl⟩ : syracuseStep 3078503 = 4617755) B4617755
theorem B2052335 : Blo 2051435 2052335 := bstep (se 1 (by rfl) ⟨1539251, by rfl⟩ : syracuseStep 2052335 = 3078503) B3078503
theorem B3078509 : Blo 2051435 3078509 := bbase (se 3 (by rfl) ⟨577220, by rfl⟩ : syracuseStep 3078509 = 1154441) (by norm_num)
theorem B2052339 : Blo 2051435 2052339 := bstep (se 1 (by rfl) ⟨1539254, by rfl⟩ : syracuseStep 2052339 = 3078509) B3078509
theorem B4617773 : Blo 2051435 4617773 := bbase (se 3 (by rfl) ⟨865832, by rfl⟩ : syracuseStep 4617773 = 1731665) (by norm_num)
theorem B3078515 : Blo 2051435 3078515 := bstep (se 1 (by rfl) ⟨2308886, by rfl⟩ : syracuseStep 3078515 = 4617773) B4617773
theorem B2052343 : Blo 2051435 2052343 := bstep (se 1 (by rfl) ⟨1539257, by rfl⟩ : syracuseStep 2052343 = 3078515) B3078515
theorem B37446293 : Blo 2051435 37446293 := bbase (se 6 (by rfl) ⟨877647, by rfl⟩ : syracuseStep 37446293 = 1755295) (by norm_num)
theorem B24964195 : Blo 2051435 24964195 := bstep (se 1 (by rfl) ⟨18723146, by rfl⟩ : syracuseStep 24964195 = 37446293) B37446293
theorem B33285593 : Blo 2051435 33285593 := bstep (se 2 (by rfl) ⟨12482097, by rfl⟩ : syracuseStep 33285593 = 24964195) B24964195
theorem B22190395 : Blo 2051435 22190395 := bstep (se 1 (by rfl) ⟨16642796, by rfl⟩ : syracuseStep 22190395 = 33285593) B33285593
theorem B29587193 : Blo 2051435 29587193 := bstep (se 2 (by rfl) ⟨11095197, by rfl⟩ : syracuseStep 29587193 = 22190395) B22190395
theorem B19724795 : Blo 2051435 19724795 := bstep (se 1 (by rfl) ⟨14793596, by rfl⟩ : syracuseStep 19724795 = 29587193) B29587193
theorem B13149863 : Blo 2051435 13149863 := bstep (se 1 (by rfl) ⟨9862397, by rfl⟩ : syracuseStep 13149863 = 19724795) B19724795
theorem B8766575 : Blo 2051435 8766575 := bstep (se 1 (by rfl) ⟨6574931, by rfl⟩ : syracuseStep 8766575 = 13149863) B13149863
theorem B5844383 : Blo 2051435 5844383 := bstep (se 1 (by rfl) ⟨4383287, by rfl⟩ : syracuseStep 5844383 = 8766575) B8766575
theorem B3896255 : Blo 2051435 3896255 := bstep (se 1 (by rfl) ⟨2922191, by rfl⟩ : syracuseStep 3896255 = 5844383) B5844383
theorem B2597503 : Blo 2051435 2597503 := bstep (se 1 (by rfl) ⟨1948127, by rfl⟩ : syracuseStep 2597503 = 3896255) B3896255
theorem B3463337 : Blo 2051435 3463337 := bstep (se 2 (by rfl) ⟨1298751, by rfl⟩ : syracuseStep 3463337 = 2597503) B2597503
theorem B2308891 : Blo 2051435 2308891 := bstep (se 1 (by rfl) ⟨1731668, by rfl⟩ : syracuseStep 2308891 = 3463337) B3463337
theorem B3078521 : Blo 2051435 3078521 := bstep (se 2 (by rfl) ⟨1154445, by rfl⟩ : syracuseStep 3078521 = 2308891) B2308891
theorem B2052347 : Blo 2051435 2052347 := bstep (se 1 (by rfl) ⟨1539260, by rfl⟩ : syracuseStep 2052347 = 3078521) B3078521
theorem B8321413 : Blo 2051435 8321413 := bbase (se 4 (by rfl) ⟨780132, by rfl⟩ : syracuseStep 8321413 = 1560265) (by norm_num)
theorem B11095217 : Blo 2051435 11095217 := bstep (se 2 (by rfl) ⟨4160706, by rfl⟩ : syracuseStep 11095217 = 8321413) B8321413
theorem B7396811 : Blo 2051435 7396811 := bstep (se 1 (by rfl) ⟨5547608, by rfl⟩ : syracuseStep 7396811 = 11095217) B11095217
theorem B4931207 : Blo 2051435 4931207 := bstep (se 1 (by rfl) ⟨3698405, by rfl⟩ : syracuseStep 4931207 = 7396811) B7396811
theorem B3287471 : Blo 2051435 3287471 := bstep (se 1 (by rfl) ⟨2465603, by rfl⟩ : syracuseStep 3287471 = 4931207) B4931207
theorem B35066357 : Blo 2051435 35066357 := bstep (se 5 (by rfl) ⟨1643735, by rfl⟩ : syracuseStep 35066357 = 3287471) B3287471
theorem B23377571 : Blo 2051435 23377571 := bstep (se 1 (by rfl) ⟨17533178, by rfl⟩ : syracuseStep 23377571 = 35066357) B35066357
theorem B15585047 : Blo 2051435 15585047 := bstep (se 1 (by rfl) ⟨11688785, by rfl⟩ : syracuseStep 15585047 = 23377571) B23377571
theorem B10390031 : Blo 2051435 10390031 := bstep (se 1 (by rfl) ⟨7792523, by rfl⟩ : syracuseStep 10390031 = 15585047) B15585047
theorem B6926687 : Blo 2051435 6926687 := bstep (se 1 (by rfl) ⟨5195015, by rfl⟩ : syracuseStep 6926687 = 10390031) B10390031
theorem B4617791 : Blo 2051435 4617791 := bstep (se 1 (by rfl) ⟨3463343, by rfl⟩ : syracuseStep 4617791 = 6926687) B6926687
theorem B3078527 : Blo 2051435 3078527 := bstep (se 1 (by rfl) ⟨2308895, by rfl⟩ : syracuseStep 3078527 = 4617791) B4617791
theorem B2052351 : Blo 2051435 2052351 := bstep (se 1 (by rfl) ⟨1539263, by rfl⟩ : syracuseStep 2052351 = 3078527) B3078527
theorem B3078533 : Blo 2051435 3078533 := bbase (se 4 (by rfl) ⟨288612, by rfl⟩ : syracuseStep 3078533 = 577225) (by norm_num)
theorem B2052355 : Blo 2051435 2052355 := bstep (se 1 (by rfl) ⟨1539266, by rfl⟩ : syracuseStep 2052355 = 3078533) B3078533
theorem B3463357 : Blo 2051435 3463357 := bbase (se 3 (by rfl) ⟨649379, by rfl⟩ : syracuseStep 3463357 = 1298759) (by norm_num)
theorem B4617809 : Blo 2051435 4617809 := bstep (se 2 (by rfl) ⟨1731678, by rfl⟩ : syracuseStep 4617809 = 3463357) B3463357
theorem B3078539 : Blo 2051435 3078539 := bstep (se 1 (by rfl) ⟨2308904, by rfl⟩ : syracuseStep 3078539 = 4617809) B4617809
theorem B2052359 : Blo 2051435 2052359 := bstep (se 1 (by rfl) ⟨1539269, by rfl⟩ : syracuseStep 2052359 = 3078539) B3078539
theorem B2308909 : Blo 2051435 2308909 := bbase (se 3 (by rfl) ⟨432920, by rfl⟩ : syracuseStep 2308909 = 865841) (by norm_num)
theorem B3078545 : Blo 2051435 3078545 := bstep (se 2 (by rfl) ⟨1154454, by rfl⟩ : syracuseStep 3078545 = 2308909) B2308909
theorem B2052363 : Blo 2051435 2052363 := bstep (se 1 (by rfl) ⟨1539272, by rfl⟩ : syracuseStep 2052363 = 3078545) B3078545
theorem B6926741 : Blo 2051435 6926741 := bbase (se 6 (by rfl) ⟨162345, by rfl⟩ : syracuseStep 6926741 = 324691) (by norm_num)
theorem B4617827 : Blo 2051435 4617827 := bstep (se 1 (by rfl) ⟨3463370, by rfl⟩ : syracuseStep 4617827 = 6926741) B6926741
theorem B3078551 : Blo 2051435 3078551 := bstep (se 1 (by rfl) ⟨2308913, by rfl⟩ : syracuseStep 3078551 = 4617827) B4617827
theorem B2052367 : Blo 2051435 2052367 := bstep (se 1 (by rfl) ⟨1539275, by rfl⟩ : syracuseStep 2052367 = 3078551) B3078551
theorem B3078557 : Blo 2051435 3078557 := bbase (se 3 (by rfl) ⟨577229, by rfl⟩ : syracuseStep 3078557 = 1154459) (by norm_num)
theorem B2052371 : Blo 2051435 2052371 := bstep (se 1 (by rfl) ⟨1539278, by rfl⟩ : syracuseStep 2052371 = 3078557) B3078557
theorem B4617845 : Blo 2051435 4617845 := bbase (se 5 (by rfl) ⟨216461, by rfl⟩ : syracuseStep 4617845 = 432923) (by norm_num)
theorem B3078563 : Blo 2051435 3078563 := bstep (se 1 (by rfl) ⟨2308922, by rfl⟩ : syracuseStep 3078563 = 4617845) B4617845
theorem B2052375 : Blo 2051435 2052375 := bstep (se 1 (by rfl) ⟨1539281, by rfl⟩ : syracuseStep 2052375 = 3078563) B3078563
theorem B5547685 : Blo 2051435 5547685 := bbase (se 4 (by rfl) ⟨520095, by rfl⟩ : syracuseStep 5547685 = 1040191) (by norm_num)
theorem B7396913 : Blo 2051435 7396913 := bstep (se 2 (by rfl) ⟨2773842, by rfl⟩ : syracuseStep 7396913 = 5547685) B5547685
theorem B4931275 : Blo 2051435 4931275 := bstep (se 1 (by rfl) ⟨3698456, by rfl⟩ : syracuseStep 4931275 = 7396913) B7396913
theorem B6575033 : Blo 2051435 6575033 := bstep (se 2 (by rfl) ⟨2465637, by rfl⟩ : syracuseStep 6575033 = 4931275) B4931275
theorem B17533421 : Blo 2051435 17533421 := bstep (se 3 (by rfl) ⟨3287516, by rfl⟩ : syracuseStep 17533421 = 6575033) B6575033
theorem B11688947 : Blo 2051435 11688947 := bstep (se 1 (by rfl) ⟨8766710, by rfl⟩ : syracuseStep 11688947 = 17533421) B17533421
theorem B7792631 : Blo 2051435 7792631 := bstep (se 1 (by rfl) ⟨5844473, by rfl⟩ : syracuseStep 7792631 = 11688947) B11688947
theorem B5195087 : Blo 2051435 5195087 := bstep (se 1 (by rfl) ⟨3896315, by rfl⟩ : syracuseStep 5195087 = 7792631) B7792631
theorem B3463391 : Blo 2051435 3463391 := bstep (se 1 (by rfl) ⟨2597543, by rfl⟩ : syracuseStep 3463391 = 5195087) B5195087
theorem B2308927 : Blo 2051435 2308927 := bstep (se 1 (by rfl) ⟨1731695, by rfl⟩ : syracuseStep 2308927 = 3463391) B3463391
theorem B3078569 : Blo 2051435 3078569 := bstep (se 2 (by rfl) ⟨1154463, by rfl⟩ : syracuseStep 3078569 = 2308927) B2308927
theorem B2052379 : Blo 2051435 2052379 := bstep (se 1 (by rfl) ⟨1539284, by rfl⟩ : syracuseStep 2052379 = 3078569) B3078569
theorem B7792645 : Blo 2051435 7792645 := bbase (se 4 (by rfl) ⟨730560, by rfl⟩ : syracuseStep 7792645 = 1461121) (by norm_num)
theorem B10390193 : Blo 2051435 10390193 := bstep (se 2 (by rfl) ⟨3896322, by rfl⟩ : syracuseStep 10390193 = 7792645) B7792645
theorem B6926795 : Blo 2051435 6926795 := bstep (se 1 (by rfl) ⟨5195096, by rfl⟩ : syracuseStep 6926795 = 10390193) B10390193
theorem B4617863 : Blo 2051435 4617863 := bstep (se 1 (by rfl) ⟨3463397, by rfl⟩ : syracuseStep 4617863 = 6926795) B6926795
theorem B3078575 : Blo 2051435 3078575 := bstep (se 1 (by rfl) ⟨2308931, by rfl⟩ : syracuseStep 3078575 = 4617863) B4617863
theorem B2052383 : Blo 2051435 2052383 := bstep (se 1 (by rfl) ⟨1539287, by rfl⟩ : syracuseStep 2052383 = 3078575) B3078575
theorem B3078581 : Blo 2051435 3078581 := bbase (se 5 (by rfl) ⟨144308, by rfl⟩ : syracuseStep 3078581 = 288617) (by norm_num)
theorem B2052387 : Blo 2051435 2052387 := bstep (se 1 (by rfl) ⟨1539290, by rfl⟩ : syracuseStep 2052387 = 3078581) B3078581
theorem B5195117 : Blo 2051435 5195117 := bbase (se 3 (by rfl) ⟨974084, by rfl⟩ : syracuseStep 5195117 = 1948169) (by norm_num)
theorem B3463411 : Blo 2051435 3463411 := bstep (se 1 (by rfl) ⟨2597558, by rfl⟩ : syracuseStep 3463411 = 5195117) B5195117
theorem B4617881 : Blo 2051435 4617881 := bstep (se 2 (by rfl) ⟨1731705, by rfl⟩ : syracuseStep 4617881 = 3463411) B3463411
theorem B3078587 : Blo 2051435 3078587 := bstep (se 1 (by rfl) ⟨2308940, by rfl⟩ : syracuseStep 3078587 = 4617881) B4617881
theorem B2052391 : Blo 2051435 2052391 := bstep (se 1 (by rfl) ⟨1539293, by rfl⟩ : syracuseStep 2052391 = 3078587) B3078587
theorem B2308945 : Blo 2051435 2308945 := bbase (se 2 (by rfl) ⟨865854, by rfl⟩ : syracuseStep 2308945 = 1731709) (by norm_num)
theorem B3078593 : Blo 2051435 3078593 := bstep (se 2 (by rfl) ⟨1154472, by rfl⟩ : syracuseStep 3078593 = 2308945) B2308945
theorem B2052395 : Blo 2051435 2052395 := bstep (se 1 (by rfl) ⟨1539296, by rfl⟩ : syracuseStep 2052395 = 3078593) B3078593
theorem B3287549 : Blo 2051435 3287549 := bbase (se 3 (by rfl) ⟨616415, by rfl⟩ : syracuseStep 3287549 = 1232831) (by norm_num)
theorem B2191699 : Blo 2051435 2191699 := bstep (se 1 (by rfl) ⟨1643774, by rfl⟩ : syracuseStep 2191699 = 3287549) B3287549
theorem B2922265 : Blo 2051435 2922265 := bstep (se 2 (by rfl) ⟨1095849, by rfl⟩ : syracuseStep 2922265 = 2191699) B2191699
theorem B3896353 : Blo 2051435 3896353 := bstep (se 2 (by rfl) ⟨1461132, by rfl⟩ : syracuseStep 3896353 = 2922265) B2922265
theorem B5195137 : Blo 2051435 5195137 := bstep (se 2 (by rfl) ⟨1948176, by rfl⟩ : syracuseStep 5195137 = 3896353) B3896353
theorem B6926849 : Blo 2051435 6926849 := bstep (se 2 (by rfl) ⟨2597568, by rfl⟩ : syracuseStep 6926849 = 5195137) B5195137
theorem B4617899 : Blo 2051435 4617899 := bstep (se 1 (by rfl) ⟨3463424, by rfl⟩ : syracuseStep 4617899 = 6926849) B6926849
theorem B3078599 : Blo 2051435 3078599 := bstep (se 1 (by rfl) ⟨2308949, by rfl⟩ : syracuseStep 3078599 = 4617899) B4617899
theorem B2052399 : Blo 2051435 2052399 := bstep (se 1 (by rfl) ⟨1539299, by rfl⟩ : syracuseStep 2052399 = 3078599) B3078599
theorem B3078605 : Blo 2051435 3078605 := bbase (se 3 (by rfl) ⟨577238, by rfl⟩ : syracuseStep 3078605 = 1154477) (by norm_num)
theorem B2052403 : Blo 2051435 2052403 := bstep (se 1 (by rfl) ⟨1539302, by rfl⟩ : syracuseStep 2052403 = 3078605) B3078605
theorem B4617917 : Blo 2051435 4617917 := bbase (se 3 (by rfl) ⟨865859, by rfl⟩ : syracuseStep 4617917 = 1731719) (by norm_num)
theorem B3078611 : Blo 2051435 3078611 := bstep (se 1 (by rfl) ⟨2308958, by rfl⟩ : syracuseStep 3078611 = 4617917) B4617917
theorem B2052407 : Blo 2051435 2052407 := bstep (se 1 (by rfl) ⟨1539305, by rfl⟩ : syracuseStep 2052407 = 3078611) B3078611
theorem B3463445 : Blo 2051435 3463445 := bbase (se 6 (by rfl) ⟨81174, by rfl⟩ : syracuseStep 3463445 = 162349) (by norm_num)
theorem B2308963 : Blo 2051435 2308963 := bstep (se 1 (by rfl) ⟨1731722, by rfl⟩ : syracuseStep 2308963 = 3463445) B3463445
theorem B3078617 : Blo 2051435 3078617 := bstep (se 2 (by rfl) ⟨1154481, by rfl⟩ : syracuseStep 3078617 = 2308963) B2308963
theorem B2052411 : Blo 2051435 2052411 := bstep (se 1 (by rfl) ⟨1539308, by rfl⟩ : syracuseStep 2052411 = 3078617) B3078617
theorem B5547781 : Blo 2051435 5547781 := bbase (se 4 (by rfl) ⟨520104, by rfl⟩ : syracuseStep 5547781 = 1040209) (by norm_num)
theorem B29588165 : Blo 2051435 29588165 := bstep (se 4 (by rfl) ⟨2773890, by rfl⟩ : syracuseStep 29588165 = 5547781) B5547781
theorem B19725443 : Blo 2051435 19725443 := bstep (se 1 (by rfl) ⟨14794082, by rfl⟩ : syracuseStep 19725443 = 29588165) B29588165
theorem B13150295 : Blo 2051435 13150295 := bstep (se 1 (by rfl) ⟨9862721, by rfl⟩ : syracuseStep 13150295 = 19725443) B19725443
theorem B8766863 : Blo 2051435 8766863 := bstep (se 1 (by rfl) ⟨6575147, by rfl⟩ : syracuseStep 8766863 = 13150295) B13150295
theorem B5844575 : Blo 2051435 5844575 := bstep (se 1 (by rfl) ⟨4383431, by rfl⟩ : syracuseStep 5844575 = 8766863) B8766863
theorem B15585533 : Blo 2051435 15585533 := bstep (se 3 (by rfl) ⟨2922287, by rfl⟩ : syracuseStep 15585533 = 5844575) B5844575
theorem B10390355 : Blo 2051435 10390355 := bstep (se 1 (by rfl) ⟨7792766, by rfl⟩ : syracuseStep 10390355 = 15585533) B15585533
theorem B6926903 : Blo 2051435 6926903 := bstep (se 1 (by rfl) ⟨5195177, by rfl⟩ : syracuseStep 6926903 = 10390355) B10390355
theorem B4617935 : Blo 2051435 4617935 := bstep (se 1 (by rfl) ⟨3463451, by rfl⟩ : syracuseStep 4617935 = 6926903) B6926903
theorem B3078623 : Blo 2051435 3078623 := bstep (se 1 (by rfl) ⟨2308967, by rfl⟩ : syracuseStep 3078623 = 4617935) B4617935
theorem B2052415 : Blo 2051435 2052415 := bstep (se 1 (by rfl) ⟨1539311, by rfl⟩ : syracuseStep 2052415 = 3078623) B3078623
theorem B3078629 : Blo 2051435 3078629 := bbase (se 4 (by rfl) ⟨288621, by rfl⟩ : syracuseStep 3078629 = 577243) (by norm_num)
theorem B2052419 : Blo 2051435 2052419 := bstep (se 1 (by rfl) ⟨1539314, by rfl⟩ : syracuseStep 2052419 = 3078629) B3078629
theorem B4931381 : Blo 2051435 4931381 := bbase (se 5 (by rfl) ⟨231158, by rfl⟩ : syracuseStep 4931381 = 462317) (by norm_num)
theorem B13150349 : Blo 2051435 13150349 := bstep (se 3 (by rfl) ⟨2465690, by rfl⟩ : syracuseStep 13150349 = 4931381) B4931381
theorem B8766899 : Blo 2051435 8766899 := bstep (se 1 (by rfl) ⟨6575174, by rfl⟩ : syracuseStep 8766899 = 13150349) B13150349
theorem B5844599 : Blo 2051435 5844599 := bstep (se 1 (by rfl) ⟨4383449, by rfl⟩ : syracuseStep 5844599 = 8766899) B8766899
theorem B3896399 : Blo 2051435 3896399 := bstep (se 1 (by rfl) ⟨2922299, by rfl⟩ : syracuseStep 3896399 = 5844599) B5844599
theorem B2597599 : Blo 2051435 2597599 := bstep (se 1 (by rfl) ⟨1948199, by rfl⟩ : syracuseStep 2597599 = 3896399) B3896399
theorem B3463465 : Blo 2051435 3463465 := bstep (se 2 (by rfl) ⟨1298799, by rfl⟩ : syracuseStep 3463465 = 2597599) B2597599
theorem B4617953 : Blo 2051435 4617953 := bstep (se 2 (by rfl) ⟨1731732, by rfl⟩ : syracuseStep 4617953 = 3463465) B3463465
theorem B3078635 : Blo 2051435 3078635 := bstep (se 1 (by rfl) ⟨2308976, by rfl⟩ : syracuseStep 3078635 = 4617953) B4617953
theorem B2052423 : Blo 2051435 2052423 := bstep (se 1 (by rfl) ⟨1539317, by rfl⟩ : syracuseStep 2052423 = 3078635) B3078635
theorem B2308981 : Blo 2051435 2308981 := bbase (se 5 (by rfl) ⟨108233, by rfl⟩ : syracuseStep 2308981 = 216467) (by norm_num)
theorem B3078641 : Blo 2051435 3078641 := bstep (se 2 (by rfl) ⟨1154490, by rfl⟩ : syracuseStep 3078641 = 2308981) B2308981
theorem B2052427 : Blo 2051435 2052427 := bstep (se 1 (by rfl) ⟨1539320, by rfl⟩ : syracuseStep 2052427 = 3078641) B3078641
theorem B2597609 : Blo 2051435 2597609 := bbase (se 2 (by rfl) ⟨974103, by rfl⟩ : syracuseStep 2597609 = 1948207) (by norm_num)
theorem B6926957 : Blo 2051435 6926957 := bstep (se 3 (by rfl) ⟨1298804, by rfl⟩ : syracuseStep 6926957 = 2597609) B2597609
theorem B4617971 : Blo 2051435 4617971 := bstep (se 1 (by rfl) ⟨3463478, by rfl⟩ : syracuseStep 4617971 = 6926957) B6926957
theorem B3078647 : Blo 2051435 3078647 := bstep (se 1 (by rfl) ⟨2308985, by rfl⟩ : syracuseStep 3078647 = 4617971) B4617971
theorem B2052431 : Blo 2051435 2052431 := bstep (se 1 (by rfl) ⟨1539323, by rfl⟩ : syracuseStep 2052431 = 3078647) B3078647
theorem B3078653 : Blo 2051435 3078653 := bbase (se 3 (by rfl) ⟨577247, by rfl⟩ : syracuseStep 3078653 = 1154495) (by norm_num)
theorem B2052435 : Blo 2051435 2052435 := bstep (se 1 (by rfl) ⟨1539326, by rfl⟩ : syracuseStep 2052435 = 3078653) B3078653
theorem B4617989 : Blo 2051435 4617989 := bbase (se 4 (by rfl) ⟨432936, by rfl⟩ : syracuseStep 4617989 = 865873) (by norm_num)
theorem B3078659 : Blo 2051435 3078659 := bstep (se 1 (by rfl) ⟨2308994, by rfl⟩ : syracuseStep 3078659 = 4617989) B4617989
theorem B2052439 : Blo 2051435 2052439 := bstep (se 1 (by rfl) ⟨1539329, by rfl⟩ : syracuseStep 2052439 = 3078659) B3078659
theorem B3896437 : Blo 2051435 3896437 := bbase (se 5 (by rfl) ⟨182645, by rfl⟩ : syracuseStep 3896437 = 365291) (by norm_num)
theorem B5195249 : Blo 2051435 5195249 := bstep (se 2 (by rfl) ⟨1948218, by rfl⟩ : syracuseStep 5195249 = 3896437) B3896437
theorem B3463499 : Blo 2051435 3463499 := bstep (se 1 (by rfl) ⟨2597624, by rfl⟩ : syracuseStep 3463499 = 5195249) B5195249
theorem B2308999 : Blo 2051435 2308999 := bstep (se 1 (by rfl) ⟨1731749, by rfl⟩ : syracuseStep 2308999 = 3463499) B3463499
theorem B3078665 : Blo 2051435 3078665 := bstep (se 2 (by rfl) ⟨1154499, by rfl⟩ : syracuseStep 3078665 = 2308999) B2308999
theorem B2052443 : Blo 2051435 2052443 := bstep (se 1 (by rfl) ⟨1539332, by rfl⟩ : syracuseStep 2052443 = 3078665) B3078665
theorem B10390517 : Blo 2051435 10390517 := bbase (se 5 (by rfl) ⟨487055, by rfl⟩ : syracuseStep 10390517 = 974111) (by norm_num)
theorem B6927011 : Blo 2051435 6927011 := bstep (se 1 (by rfl) ⟨5195258, by rfl⟩ : syracuseStep 6927011 = 10390517) B10390517
theorem B4618007 : Blo 2051435 4618007 := bstep (se 1 (by rfl) ⟨3463505, by rfl⟩ : syracuseStep 4618007 = 6927011) B6927011
theorem B3078671 : Blo 2051435 3078671 := bstep (se 1 (by rfl) ⟨2309003, by rfl⟩ : syracuseStep 3078671 = 4618007) B4618007
theorem B2052447 : Blo 2051435 2052447 := bstep (se 1 (by rfl) ⟨1539335, by rfl⟩ : syracuseStep 2052447 = 3078671) B3078671
theorem B3078677 : Blo 2051435 3078677 := bbase (se 6 (by rfl) ⟨72156, by rfl⟩ : syracuseStep 3078677 = 144313) (by norm_num)
theorem B2052451 : Blo 2051435 2052451 := bstep (se 1 (by rfl) ⟨1539338, by rfl⟩ : syracuseStep 2052451 = 3078677) B3078677
theorem B17534069 : Blo 2051435 17534069 := bbase (se 5 (by rfl) ⟨821909, by rfl⟩ : syracuseStep 17534069 = 1643819) (by norm_num)
theorem B11689379 : Blo 2051435 11689379 := bstep (se 1 (by rfl) ⟨8767034, by rfl⟩ : syracuseStep 11689379 = 17534069) B17534069
theorem B7792919 : Blo 2051435 7792919 := bstep (se 1 (by rfl) ⟨5844689, by rfl⟩ : syracuseStep 7792919 = 11689379) B11689379
theorem B5195279 : Blo 2051435 5195279 := bstep (se 1 (by rfl) ⟨3896459, by rfl⟩ : syracuseStep 5195279 = 7792919) B7792919
theorem B3463519 : Blo 2051435 3463519 := bstep (se 1 (by rfl) ⟨2597639, by rfl⟩ : syracuseStep 3463519 = 5195279) B5195279
theorem B4618025 : Blo 2051435 4618025 := bstep (se 2 (by rfl) ⟨1731759, by rfl⟩ : syracuseStep 4618025 = 3463519) B3463519
theorem B3078683 : Blo 2051435 3078683 := bstep (se 1 (by rfl) ⟨2309012, by rfl⟩ : syracuseStep 3078683 = 4618025) B4618025
theorem B2052455 : Blo 2051435 2052455 := bstep (se 1 (by rfl) ⟨1539341, by rfl⟩ : syracuseStep 2052455 = 3078683) B3078683
theorem B2309017 : Blo 2051435 2309017 := bbase (se 2 (by rfl) ⟨865881, by rfl⟩ : syracuseStep 2309017 = 1731763) (by norm_num)
theorem B3078689 : Blo 2051435 3078689 := bstep (se 2 (by rfl) ⟨1154508, by rfl⟩ : syracuseStep 3078689 = 2309017) B2309017
theorem B2052459 : Blo 2051435 2052459 := bstep (se 1 (by rfl) ⟨1539344, by rfl⟩ : syracuseStep 2052459 = 3078689) B3078689
theorem B7792949 : Blo 2051435 7792949 := bbase (se 5 (by rfl) ⟨365294, by rfl⟩ : syracuseStep 7792949 = 730589) (by norm_num)
theorem B5195299 : Blo 2051435 5195299 := bstep (se 1 (by rfl) ⟨3896474, by rfl⟩ : syracuseStep 5195299 = 7792949) B7792949
theorem B6927065 : Blo 2051435 6927065 := bstep (se 2 (by rfl) ⟨2597649, by rfl⟩ : syracuseStep 6927065 = 5195299) B5195299
theorem B4618043 : Blo 2051435 4618043 := bstep (se 1 (by rfl) ⟨3463532, by rfl⟩ : syracuseStep 4618043 = 6927065) B6927065
theorem B3078695 : Blo 2051435 3078695 := bstep (se 1 (by rfl) ⟨2309021, by rfl⟩ : syracuseStep 3078695 = 4618043) B4618043
theorem B2052463 : Blo 2051435 2052463 := bstep (se 1 (by rfl) ⟨1539347, by rfl⟩ : syracuseStep 2052463 = 3078695) B3078695
theorem B3078701 : Blo 2051435 3078701 := bbase (se 3 (by rfl) ⟨577256, by rfl⟩ : syracuseStep 3078701 = 1154513) (by norm_num)
theorem B2052467 : Blo 2051435 2052467 := bstep (se 1 (by rfl) ⟨1539350, by rfl⟩ : syracuseStep 2052467 = 3078701) B3078701
theorem B4618061 : Blo 2051435 4618061 := bbase (se 3 (by rfl) ⟨865886, by rfl⟩ : syracuseStep 4618061 = 1731773) (by norm_num)
theorem B3078707 : Blo 2051435 3078707 := bstep (se 1 (by rfl) ⟨2309030, by rfl⟩ : syracuseStep 3078707 = 4618061) B4618061
theorem B2052471 : Blo 2051435 2052471 := bstep (se 1 (by rfl) ⟨1539353, by rfl⟩ : syracuseStep 2052471 = 3078707) B3078707
theorem B2597665 : Blo 2051435 2597665 := bbase (se 2 (by rfl) ⟨974124, by rfl⟩ : syracuseStep 2597665 = 1948249) (by norm_num)
theorem B3463553 : Blo 2051435 3463553 := bstep (se 2 (by rfl) ⟨1298832, by rfl⟩ : syracuseStep 3463553 = 2597665) B2597665
theorem B2309035 : Blo 2051435 2309035 := bstep (se 1 (by rfl) ⟨1731776, by rfl⟩ : syracuseStep 2309035 = 3463553) B3463553
theorem B3078713 : Blo 2051435 3078713 := bstep (se 2 (by rfl) ⟨1154517, by rfl⟩ : syracuseStep 3078713 = 2309035) B2309035
theorem B2052475 : Blo 2051435 2052475 := bstep (se 1 (by rfl) ⟨1539356, by rfl⟩ : syracuseStep 2052475 = 3078713) B3078713
theorem B23379029 : Blo 2051435 23379029 := bbase (se 8 (by rfl) ⟨136986, by rfl⟩ : syracuseStep 23379029 = 273973) (by norm_num)
theorem B15586019 : Blo 2051435 15586019 := bstep (se 1 (by rfl) ⟨11689514, by rfl⟩ : syracuseStep 15586019 = 23379029) B23379029
theorem B10390679 : Blo 2051435 10390679 := bstep (se 1 (by rfl) ⟨7793009, by rfl⟩ : syracuseStep 10390679 = 15586019) B15586019
theorem B6927119 : Blo 2051435 6927119 := bstep (se 1 (by rfl) ⟨5195339, by rfl⟩ : syracuseStep 6927119 = 10390679) B10390679
theorem B4618079 : Blo 2051435 4618079 := bstep (se 1 (by rfl) ⟨3463559, by rfl⟩ : syracuseStep 4618079 = 6927119) B6927119
theorem B3078719 : Blo 2051435 3078719 := bstep (se 1 (by rfl) ⟨2309039, by rfl⟩ : syracuseStep 3078719 = 4618079) B4618079
theorem B2052479 : Blo 2051435 2052479 := bstep (se 1 (by rfl) ⟨1539359, by rfl⟩ : syracuseStep 2052479 = 3078719) B3078719
theorem B3078725 : Blo 2051435 3078725 := bbase (se 4 (by rfl) ⟨288630, by rfl⟩ : syracuseStep 3078725 = 577261) (by norm_num)
theorem B2052483 : Blo 2051435 2052483 := bstep (se 1 (by rfl) ⟨1539362, by rfl⟩ : syracuseStep 2052483 = 3078725) B3078725
theorem B3463573 : Blo 2051435 3463573 := bbase (se 6 (by rfl) ⟨81177, by rfl⟩ : syracuseStep 3463573 = 162355) (by norm_num)
theorem B4618097 : Blo 2051435 4618097 := bstep (se 2 (by rfl) ⟨1731786, by rfl⟩ : syracuseStep 4618097 = 3463573) B3463573
theorem B3078731 : Blo 2051435 3078731 := bstep (se 1 (by rfl) ⟨2309048, by rfl⟩ : syracuseStep 3078731 = 4618097) B4618097
theorem B2052487 : Blo 2051435 2052487 := bstep (se 1 (by rfl) ⟨1539365, by rfl⟩ : syracuseStep 2052487 = 3078731) B3078731
theorem B2309053 : Blo 2051435 2309053 := bbase (se 3 (by rfl) ⟨432947, by rfl⟩ : syracuseStep 2309053 = 865895) (by norm_num)
theorem B3078737 : Blo 2051435 3078737 := bstep (se 2 (by rfl) ⟨1154526, by rfl⟩ : syracuseStep 3078737 = 2309053) B2309053
theorem B2052491 : Blo 2051435 2052491 := bstep (se 1 (by rfl) ⟨1539368, by rfl⟩ : syracuseStep 2052491 = 3078737) B3078737
theorem B6927173 : Blo 2051435 6927173 := bbase (se 4 (by rfl) ⟨649422, by rfl⟩ : syracuseStep 6927173 = 1298845) (by norm_num)
theorem B4618115 : Blo 2051435 4618115 := bstep (se 1 (by rfl) ⟨3463586, by rfl⟩ : syracuseStep 4618115 = 6927173) B6927173
theorem B3078743 : Blo 2051435 3078743 := bstep (se 1 (by rfl) ⟨2309057, by rfl⟩ : syracuseStep 3078743 = 4618115) B4618115
theorem B2052495 : Blo 2051435 2052495 := bstep (se 1 (by rfl) ⟨1539371, by rfl⟩ : syracuseStep 2052495 = 3078743) B3078743
theorem B3078749 : Blo 2051435 3078749 := bbase (se 3 (by rfl) ⟨577265, by rfl⟩ : syracuseStep 3078749 = 1154531) (by norm_num)
theorem B2052499 : Blo 2051435 2052499 := bstep (se 1 (by rfl) ⟨1539374, by rfl⟩ : syracuseStep 2052499 = 3078749) B3078749
theorem B4618133 : Blo 2051435 4618133 := bbase (se 6 (by rfl) ⟨108237, by rfl⟩ : syracuseStep 4618133 = 216475) (by norm_num)
theorem B3078755 : Blo 2051435 3078755 := bstep (se 1 (by rfl) ⟨2309066, by rfl⟩ : syracuseStep 3078755 = 4618133) B4618133
theorem B2052503 : Blo 2051435 2052503 := bstep (se 1 (by rfl) ⟨1539377, by rfl⟩ : syracuseStep 2052503 = 3078755) B3078755
theorem B4383629 : Blo 2051435 4383629 := bbase (se 3 (by rfl) ⟨821930, by rfl⟩ : syracuseStep 4383629 = 1643861) (by norm_num)
theorem B2922419 : Blo 2051435 2922419 := bstep (se 1 (by rfl) ⟨2191814, by rfl⟩ : syracuseStep 2922419 = 4383629) B4383629
theorem B7793117 : Blo 2051435 7793117 := bstep (se 3 (by rfl) ⟨1461209, by rfl⟩ : syracuseStep 7793117 = 2922419) B2922419
theorem B5195411 : Blo 2051435 5195411 := bstep (se 1 (by rfl) ⟨3896558, by rfl⟩ : syracuseStep 5195411 = 7793117) B7793117
theorem B3463607 : Blo 2051435 3463607 := bstep (se 1 (by rfl) ⟨2597705, by rfl⟩ : syracuseStep 3463607 = 5195411) B5195411
theorem B2309071 : Blo 2051435 2309071 := bstep (se 1 (by rfl) ⟨1731803, by rfl⟩ : syracuseStep 2309071 = 3463607) B3463607
theorem B3078761 : Blo 2051435 3078761 := bstep (se 2 (by rfl) ⟨1154535, by rfl⟩ : syracuseStep 3078761 = 2309071) B2309071
theorem B2052507 : Blo 2051435 2052507 := bstep (se 1 (by rfl) ⟨1539380, by rfl⟩ : syracuseStep 2052507 = 3078761) B3078761
theorem B3120773 : Blo 2051435 3120773 := bbase (se 4 (by rfl) ⟨292572, by rfl⟩ : syracuseStep 3120773 = 585145) (by norm_num)
theorem B33288245 : Blo 2051435 33288245 := bstep (se 5 (by rfl) ⟨1560386, by rfl⟩ : syracuseStep 33288245 = 3120773) B3120773
theorem B22192163 : Blo 2051435 22192163 := bstep (se 1 (by rfl) ⟨16644122, by rfl⟩ : syracuseStep 22192163 = 33288245) B33288245
theorem B14794775 : Blo 2051435 14794775 := bstep (se 1 (by rfl) ⟨11096081, by rfl⟩ : syracuseStep 14794775 = 22192163) B22192163
theorem B9863183 : Blo 2051435 9863183 := bstep (se 1 (by rfl) ⟨7397387, by rfl⟩ : syracuseStep 9863183 = 14794775) B14794775
theorem B6575455 : Blo 2051435 6575455 := bstep (se 1 (by rfl) ⟨4931591, by rfl⟩ : syracuseStep 6575455 = 9863183) B9863183
theorem B8767273 : Blo 2051435 8767273 := bstep (se 2 (by rfl) ⟨3287727, by rfl⟩ : syracuseStep 8767273 = 6575455) B6575455
theorem B11689697 : Blo 2051435 11689697 := bstep (se 2 (by rfl) ⟨4383636, by rfl⟩ : syracuseStep 11689697 = 8767273) B8767273
theorem B7793131 : Blo 2051435 7793131 := bstep (se 1 (by rfl) ⟨5844848, by rfl⟩ : syracuseStep 7793131 = 11689697) B11689697
theorem B10390841 : Blo 2051435 10390841 := bstep (se 2 (by rfl) ⟨3896565, by rfl⟩ : syracuseStep 10390841 = 7793131) B7793131
theorem B6927227 : Blo 2051435 6927227 := bstep (se 1 (by rfl) ⟨5195420, by rfl⟩ : syracuseStep 6927227 = 10390841) B10390841
theorem B4618151 : Blo 2051435 4618151 := bstep (se 1 (by rfl) ⟨3463613, by rfl⟩ : syracuseStep 4618151 = 6927227) B6927227
theorem B3078767 : Blo 2051435 3078767 := bstep (se 1 (by rfl) ⟨2309075, by rfl⟩ : syracuseStep 3078767 = 4618151) B4618151
theorem B2052511 : Blo 2051435 2052511 := bstep (se 1 (by rfl) ⟨1539383, by rfl⟩ : syracuseStep 2052511 = 3078767) B3078767
theorem B3078773 : Blo 2051435 3078773 := bbase (se 5 (by rfl) ⟨144317, by rfl⟩ : syracuseStep 3078773 = 288635) (by norm_num)
theorem B2052515 : Blo 2051435 2052515 := bstep (se 1 (by rfl) ⟨1539386, by rfl⟩ : syracuseStep 2052515 = 3078773) B3078773
theorem B3896581 : Blo 2051435 3896581 := bbase (se 4 (by rfl) ⟨365304, by rfl⟩ : syracuseStep 3896581 = 730609) (by norm_num)
theorem B5195441 : Blo 2051435 5195441 := bstep (se 2 (by rfl) ⟨1948290, by rfl⟩ : syracuseStep 5195441 = 3896581) B3896581
theorem B3463627 : Blo 2051435 3463627 := bstep (se 1 (by rfl) ⟨2597720, by rfl⟩ : syracuseStep 3463627 = 5195441) B5195441
theorem B4618169 : Blo 2051435 4618169 := bstep (se 2 (by rfl) ⟨1731813, by rfl⟩ : syracuseStep 4618169 = 3463627) B3463627
theorem B3078779 : Blo 2051435 3078779 := bstep (se 1 (by rfl) ⟨2309084, by rfl⟩ : syracuseStep 3078779 = 4618169) B4618169
theorem B2052519 : Blo 2051435 2052519 := bstep (se 1 (by rfl) ⟨1539389, by rfl⟩ : syracuseStep 2052519 = 3078779) B3078779
theorem B2309089 : Blo 2051435 2309089 := bbase (se 2 (by rfl) ⟨865908, by rfl⟩ : syracuseStep 2309089 = 1731817) (by norm_num)
theorem B3078785 : Blo 2051435 3078785 := bstep (se 2 (by rfl) ⟨1154544, by rfl⟩ : syracuseStep 3078785 = 2309089) B2309089
theorem B2052523 : Blo 2051435 2052523 := bstep (se 1 (by rfl) ⟨1539392, by rfl⟩ : syracuseStep 2052523 = 3078785) B3078785
theorem B5195461 : Blo 2051435 5195461 := bbase (se 4 (by rfl) ⟨487074, by rfl⟩ : syracuseStep 5195461 = 974149) (by norm_num)
theorem B6927281 : Blo 2051435 6927281 := bstep (se 2 (by rfl) ⟨2597730, by rfl⟩ : syracuseStep 6927281 = 5195461) B5195461
theorem B4618187 : Blo 2051435 4618187 := bstep (se 1 (by rfl) ⟨3463640, by rfl⟩ : syracuseStep 4618187 = 6927281) B6927281
theorem B3078791 : Blo 2051435 3078791 := bstep (se 1 (by rfl) ⟨2309093, by rfl⟩ : syracuseStep 3078791 = 4618187) B4618187
theorem B2052527 : Blo 2051435 2052527 := bstep (se 1 (by rfl) ⟨1539395, by rfl⟩ : syracuseStep 2052527 = 3078791) B3078791
theorem B3078797 : Blo 2051435 3078797 := bbase (se 3 (by rfl) ⟨577274, by rfl⟩ : syracuseStep 3078797 = 1154549) (by norm_num)
theorem B2052531 : Blo 2051435 2052531 := bstep (se 1 (by rfl) ⟨1539398, by rfl⟩ : syracuseStep 2052531 = 3078797) B3078797
theorem B4618205 : Blo 2051435 4618205 := bbase (se 3 (by rfl) ⟨865913, by rfl⟩ : syracuseStep 4618205 = 1731827) (by norm_num)
theorem B3078803 : Blo 2051435 3078803 := bstep (se 1 (by rfl) ⟨2309102, by rfl⟩ : syracuseStep 3078803 = 4618205) B4618205
theorem B2052535 : Blo 2051435 2052535 := bstep (se 1 (by rfl) ⟨1539401, by rfl⟩ : syracuseStep 2052535 = 3078803) B3078803
theorem B3463661 : Blo 2051435 3463661 := bbase (se 3 (by rfl) ⟨649436, by rfl⟩ : syracuseStep 3463661 = 1298873) (by norm_num)
theorem B2309107 : Blo 2051435 2309107 := bstep (se 1 (by rfl) ⟨1731830, by rfl⟩ : syracuseStep 2309107 = 3463661) B3463661
theorem B3078809 : Blo 2051435 3078809 := bstep (se 2 (by rfl) ⟨1154553, by rfl⟩ : syracuseStep 3078809 = 2309107) B2309107
theorem B2052539 : Blo 2051435 2052539 := bstep (se 1 (by rfl) ⟨1539404, by rfl⟩ : syracuseStep 2052539 = 3078809) B3078809
theorem B26302229 : Blo 2051435 26302229 := bbase (se 6 (by rfl) ⟨616458, by rfl⟩ : syracuseStep 26302229 = 1232917) (by norm_num)
theorem B17534819 : Blo 2051435 17534819 := bstep (se 1 (by rfl) ⟨13151114, by rfl⟩ : syracuseStep 17534819 = 26302229) B26302229
theorem B11689879 : Blo 2051435 11689879 := bstep (se 1 (by rfl) ⟨8767409, by rfl⟩ : syracuseStep 11689879 = 17534819) B17534819
theorem B15586505 : Blo 2051435 15586505 := bstep (se 2 (by rfl) ⟨5844939, by rfl⟩ : syracuseStep 15586505 = 11689879) B11689879
theorem B10391003 : Blo 2051435 10391003 := bstep (se 1 (by rfl) ⟨7793252, by rfl⟩ : syracuseStep 10391003 = 15586505) B15586505
theorem B6927335 : Blo 2051435 6927335 := bstep (se 1 (by rfl) ⟨5195501, by rfl⟩ : syracuseStep 6927335 = 10391003) B10391003
theorem B4618223 : Blo 2051435 4618223 := bstep (se 1 (by rfl) ⟨3463667, by rfl⟩ : syracuseStep 4618223 = 6927335) B6927335
theorem B3078815 : Blo 2051435 3078815 := bstep (se 1 (by rfl) ⟨2309111, by rfl⟩ : syracuseStep 3078815 = 4618223) B4618223
theorem B2052543 : Blo 2051435 2052543 := bstep (se 1 (by rfl) ⟨1539407, by rfl⟩ : syracuseStep 2052543 = 3078815) B3078815
theorem B3078821 : Blo 2051435 3078821 := bbase (se 4 (by rfl) ⟨288639, by rfl⟩ : syracuseStep 3078821 = 577279) (by norm_num)
theorem B2052547 : Blo 2051435 2052547 := bstep (se 1 (by rfl) ⟨1539410, by rfl⟩ : syracuseStep 2052547 = 3078821) B3078821
theorem B2597761 : Blo 2051435 2597761 := bbase (se 2 (by rfl) ⟨974160, by rfl⟩ : syracuseStep 2597761 = 1948321) (by norm_num)
theorem B3463681 : Blo 2051435 3463681 := bstep (se 2 (by rfl) ⟨1298880, by rfl⟩ : syracuseStep 3463681 = 2597761) B2597761
theorem B4618241 : Blo 2051435 4618241 := bstep (se 2 (by rfl) ⟨1731840, by rfl⟩ : syracuseStep 4618241 = 3463681) B3463681
theorem B3078827 : Blo 2051435 3078827 := bstep (se 1 (by rfl) ⟨2309120, by rfl⟩ : syracuseStep 3078827 = 4618241) B4618241
theorem B2052551 : Blo 2051435 2052551 := bstep (se 1 (by rfl) ⟨1539413, by rfl⟩ : syracuseStep 2052551 = 3078827) B3078827
theorem B2309125 : Blo 2051435 2309125 := bbase (se 4 (by rfl) ⟨216480, by rfl⟩ : syracuseStep 2309125 = 432961) (by norm_num)
theorem B3078833 : Blo 2051435 3078833 := bstep (se 2 (by rfl) ⟨1154562, by rfl⟩ : syracuseStep 3078833 = 2309125) B2309125
theorem B2052555 : Blo 2051435 2052555 := bstep (se 1 (by rfl) ⟨1539416, by rfl⟩ : syracuseStep 2052555 = 3078833) B3078833
theorem B2922493 : Blo 2051435 2922493 := bbase (se 3 (by rfl) ⟨547967, by rfl⟩ : syracuseStep 2922493 = 1095935) (by norm_num)
theorem B3896657 : Blo 2051435 3896657 := bstep (se 2 (by rfl) ⟨1461246, by rfl⟩ : syracuseStep 3896657 = 2922493) B2922493
theorem B2597771 : Blo 2051435 2597771 := bstep (se 1 (by rfl) ⟨1948328, by rfl⟩ : syracuseStep 2597771 = 3896657) B3896657
theorem B6927389 : Blo 2051435 6927389 := bstep (se 3 (by rfl) ⟨1298885, by rfl⟩ : syracuseStep 6927389 = 2597771) B2597771
theorem B4618259 : Blo 2051435 4618259 := bstep (se 1 (by rfl) ⟨3463694, by rfl⟩ : syracuseStep 4618259 = 6927389) B6927389
theorem B3078839 : Blo 2051435 3078839 := bstep (se 1 (by rfl) ⟨2309129, by rfl⟩ : syracuseStep 3078839 = 4618259) B4618259
theorem B2052559 : Blo 2051435 2052559 := bstep (se 1 (by rfl) ⟨1539419, by rfl⟩ : syracuseStep 2052559 = 3078839) B3078839
theorem B3078845 : Blo 2051435 3078845 := bbase (se 3 (by rfl) ⟨577283, by rfl⟩ : syracuseStep 3078845 = 1154567) (by norm_num)
theorem B2052563 : Blo 2051435 2052563 := bstep (se 1 (by rfl) ⟨1539422, by rfl⟩ : syracuseStep 2052563 = 3078845) B3078845
theorem B4618277 : Blo 2051435 4618277 := bbase (se 4 (by rfl) ⟨432963, by rfl⟩ : syracuseStep 4618277 = 865927) (by norm_num)
theorem B3078851 : Blo 2051435 3078851 := bstep (se 1 (by rfl) ⟨2309138, by rfl⟩ : syracuseStep 3078851 = 4618277) B4618277
theorem B2052567 : Blo 2051435 2052567 := bstep (se 1 (by rfl) ⟨1539425, by rfl⟩ : syracuseStep 2052567 = 3078851) B3078851
theorem B5195573 : Blo 2051435 5195573 := bbase (se 5 (by rfl) ⟨243542, by rfl⟩ : syracuseStep 5195573 = 487085) (by norm_num)
theorem B3463715 : Blo 2051435 3463715 := bstep (se 1 (by rfl) ⟨2597786, by rfl⟩ : syracuseStep 3463715 = 5195573) B5195573
theorem B2309143 : Blo 2051435 2309143 := bstep (se 1 (by rfl) ⟨1731857, by rfl⟩ : syracuseStep 2309143 = 3463715) B3463715
theorem B3078857 : Blo 2051435 3078857 := bstep (se 2 (by rfl) ⟨1154571, by rfl⟩ : syracuseStep 3078857 = 2309143) B2309143
theorem B2052571 : Blo 2051435 2052571 := bstep (se 1 (by rfl) ⟨1539428, by rfl⟩ : syracuseStep 2052571 = 3078857) B3078857
theorem B2499517 : Blo 2051435 2499517 := bbase (se 3 (by rfl) ⟨468659, by rfl⟩ : syracuseStep 2499517 = 937319) (by norm_num)
theorem B13330757 : Blo 2051435 13330757 := bstep (se 4 (by rfl) ⟨1249758, by rfl⟩ : syracuseStep 13330757 = 2499517) B2499517
theorem B8887171 : Blo 2051435 8887171 := bstep (se 1 (by rfl) ⟨6665378, by rfl⟩ : syracuseStep 8887171 = 13330757) B13330757
theorem B11849561 : Blo 2051435 11849561 := bstep (se 2 (by rfl) ⟨4443585, by rfl⟩ : syracuseStep 11849561 = 8887171) B8887171
theorem B7899707 : Blo 2051435 7899707 := bstep (se 1 (by rfl) ⟨5924780, by rfl⟩ : syracuseStep 7899707 = 11849561) B11849561
theorem B5266471 : Blo 2051435 5266471 := bstep (se 1 (by rfl) ⟨3949853, by rfl⟩ : syracuseStep 5266471 = 7899707) B7899707
theorem B7021961 : Blo 2051435 7021961 := bstep (se 2 (by rfl) ⟨2633235, by rfl⟩ : syracuseStep 7021961 = 5266471) B5266471
theorem B4681307 : Blo 2051435 4681307 := bstep (se 1 (by rfl) ⟨3510980, by rfl⟩ : syracuseStep 4681307 = 7021961) B7021961
theorem B3120871 : Blo 2051435 3120871 := bstep (se 1 (by rfl) ⟨2340653, by rfl⟩ : syracuseStep 3120871 = 4681307) B4681307
theorem B4161161 : Blo 2051435 4161161 := bstep (se 2 (by rfl) ⟨1560435, by rfl⟩ : syracuseStep 4161161 = 3120871) B3120871
theorem B2774107 : Blo 2051435 2774107 := bstep (se 1 (by rfl) ⟨2080580, by rfl⟩ : syracuseStep 2774107 = 4161161) B4161161
theorem B14795237 : Blo 2051435 14795237 := bstep (se 4 (by rfl) ⟨1387053, by rfl⟩ : syracuseStep 14795237 = 2774107) B2774107
theorem B9863491 : Blo 2051435 9863491 := bstep (se 1 (by rfl) ⟨7397618, by rfl⟩ : syracuseStep 9863491 = 14795237) B14795237
theorem B13151321 : Blo 2051435 13151321 := bstep (se 2 (by rfl) ⟨4931745, by rfl⟩ : syracuseStep 13151321 = 9863491) B9863491
theorem B8767547 : Blo 2051435 8767547 := bstep (se 1 (by rfl) ⟨6575660, by rfl⟩ : syracuseStep 8767547 = 13151321) B13151321
theorem B5845031 : Blo 2051435 5845031 := bstep (se 1 (by rfl) ⟨4383773, by rfl⟩ : syracuseStep 5845031 = 8767547) B8767547
theorem B3896687 : Blo 2051435 3896687 := bstep (se 1 (by rfl) ⟨2922515, by rfl⟩ : syracuseStep 3896687 = 5845031) B5845031
theorem B10391165 : Blo 2051435 10391165 := bstep (se 3 (by rfl) ⟨1948343, by rfl⟩ : syracuseStep 10391165 = 3896687) B3896687
theorem B6927443 : Blo 2051435 6927443 := bstep (se 1 (by rfl) ⟨5195582, by rfl⟩ : syracuseStep 6927443 = 10391165) B10391165
theorem B4618295 : Blo 2051435 4618295 := bstep (se 1 (by rfl) ⟨3463721, by rfl⟩ : syracuseStep 4618295 = 6927443) B6927443
theorem B3078863 : Blo 2051435 3078863 := bstep (se 1 (by rfl) ⟨2309147, by rfl⟩ : syracuseStep 3078863 = 4618295) B4618295
theorem B2052575 : Blo 2051435 2052575 := bstep (se 1 (by rfl) ⟨1539431, by rfl⟩ : syracuseStep 2052575 = 3078863) B3078863
theorem B3078869 : Blo 2051435 3078869 := bbase (se 7 (by rfl) ⟨36080, by rfl⟩ : syracuseStep 3078869 = 72161) (by norm_num)
theorem B2052579 : Blo 2051435 2052579 := bstep (se 1 (by rfl) ⟨1539434, by rfl⟩ : syracuseStep 2052579 = 3078869) B3078869
theorem B4681325 : Blo 2051435 4681325 := bbase (se 3 (by rfl) ⟨877748, by rfl⟩ : syracuseStep 4681325 = 1755497) (by norm_num)
theorem B12483533 : Blo 2051435 12483533 := bstep (se 3 (by rfl) ⟨2340662, by rfl⟩ : syracuseStep 12483533 = 4681325) B4681325
theorem B8322355 : Blo 2051435 8322355 := bstep (se 1 (by rfl) ⟨6241766, by rfl⟩ : syracuseStep 8322355 = 12483533) B12483533
theorem B11096473 : Blo 2051435 11096473 := bstep (se 2 (by rfl) ⟨4161177, by rfl⟩ : syracuseStep 11096473 = 8322355) B8322355
theorem B14795297 : Blo 2051435 14795297 := bstep (se 2 (by rfl) ⟨5548236, by rfl⟩ : syracuseStep 14795297 = 11096473) B11096473
theorem B9863531 : Blo 2051435 9863531 := bstep (se 1 (by rfl) ⟨7397648, by rfl⟩ : syracuseStep 9863531 = 14795297) B14795297
theorem B6575687 : Blo 2051435 6575687 := bstep (se 1 (by rfl) ⟨4931765, by rfl⟩ : syracuseStep 6575687 = 9863531) B9863531
theorem B4383791 : Blo 2051435 4383791 := bstep (se 1 (by rfl) ⟨3287843, by rfl⟩ : syracuseStep 4383791 = 6575687) B6575687
theorem B2922527 : Blo 2051435 2922527 := bstep (se 1 (by rfl) ⟨2191895, by rfl⟩ : syracuseStep 2922527 = 4383791) B4383791
theorem B7793405 : Blo 2051435 7793405 := bstep (se 3 (by rfl) ⟨1461263, by rfl⟩ : syracuseStep 7793405 = 2922527) B2922527
theorem B5195603 : Blo 2051435 5195603 := bstep (se 1 (by rfl) ⟨3896702, by rfl⟩ : syracuseStep 5195603 = 7793405) B7793405
theorem B3463735 : Blo 2051435 3463735 := bstep (se 1 (by rfl) ⟨2597801, by rfl⟩ : syracuseStep 3463735 = 5195603) B5195603
theorem B4618313 : Blo 2051435 4618313 := bstep (se 2 (by rfl) ⟨1731867, by rfl⟩ : syracuseStep 4618313 = 3463735) B3463735
theorem B3078875 : Blo 2051435 3078875 := bstep (se 1 (by rfl) ⟨2309156, by rfl⟩ : syracuseStep 3078875 = 4618313) B4618313
theorem B2052583 : Blo 2051435 2052583 := bstep (se 1 (by rfl) ⟨1539437, by rfl⟩ : syracuseStep 2052583 = 3078875) B3078875
theorem B2309161 : Blo 2051435 2309161 := bbase (se 2 (by rfl) ⟨865935, by rfl⟩ : syracuseStep 2309161 = 1731871) (by norm_num)
theorem B3078881 : Blo 2051435 3078881 := bstep (se 2 (by rfl) ⟨1154580, by rfl⟩ : syracuseStep 3078881 = 2309161) B2309161
theorem B2052587 : Blo 2051435 2052587 := bstep (se 1 (by rfl) ⟨1539440, by rfl⟩ : syracuseStep 2052587 = 3078881) B3078881
theorem B4745213 : Blo 2051435 4745213 := bbase (se 3 (by rfl) ⟨889727, by rfl⟩ : syracuseStep 4745213 = 1779455) (by norm_num)
theorem B3163475 : Blo 2051435 3163475 := bstep (se 1 (by rfl) ⟨2372606, by rfl⟩ : syracuseStep 3163475 = 4745213) B4745213
theorem B2108983 : Blo 2051435 2108983 := bstep (se 1 (by rfl) ⟨1581737, by rfl⟩ : syracuseStep 2108983 = 3163475) B3163475
theorem B2811977 : Blo 2051435 2811977 := bstep (se 2 (by rfl) ⟨1054491, by rfl⟩ : syracuseStep 2811977 = 2108983) B2108983
theorem B29994421 : Blo 2051435 29994421 := bstep (se 5 (by rfl) ⟨1405988, by rfl⟩ : syracuseStep 29994421 = 2811977) B2811977
theorem B39992561 : Blo 2051435 39992561 := bstep (se 2 (by rfl) ⟨14997210, by rfl⟩ : syracuseStep 39992561 = 29994421) B29994421
theorem B26661707 : Blo 2051435 26661707 := bstep (se 1 (by rfl) ⟨19996280, by rfl⟩ : syracuseStep 26661707 = 39992561) B39992561
theorem B17774471 : Blo 2051435 17774471 := bstep (se 1 (by rfl) ⟨13330853, by rfl⟩ : syracuseStep 17774471 = 26661707) B26661707
theorem B11849647 : Blo 2051435 11849647 := bstep (se 1 (by rfl) ⟨8887235, by rfl⟩ : syracuseStep 11849647 = 17774471) B17774471
theorem B15799529 : Blo 2051435 15799529 := bstep (se 2 (by rfl) ⟨5924823, by rfl⟩ : syracuseStep 15799529 = 11849647) B11849647
theorem B42132077 : Blo 2051435 42132077 := bstep (se 3 (by rfl) ⟨7899764, by rfl⟩ : syracuseStep 42132077 = 15799529) B15799529
theorem B28088051 : Blo 2051435 28088051 := bstep (se 1 (by rfl) ⟨21066038, by rfl⟩ : syracuseStep 28088051 = 42132077) B42132077
theorem B74901469 : Blo 2051435 74901469 := bstep (se 3 (by rfl) ⟨14044025, by rfl⟩ : syracuseStep 74901469 = 28088051) B28088051
theorem B99868625 : Blo 2051435 99868625 := bstep (se 2 (by rfl) ⟨37450734, by rfl⟩ : syracuseStep 99868625 = 74901469) B74901469
theorem B66579083 : Blo 2051435 66579083 := bstep (se 1 (by rfl) ⟨49934312, by rfl⟩ : syracuseStep 66579083 = 99868625) B99868625
theorem B44386055 : Blo 2051435 44386055 := bstep (se 1 (by rfl) ⟨33289541, by rfl⟩ : syracuseStep 44386055 = 66579083) B66579083
theorem B29590703 : Blo 2051435 29590703 := bstep (se 1 (by rfl) ⟨22193027, by rfl⟩ : syracuseStep 29590703 = 44386055) B44386055
theorem B19727135 : Blo 2051435 19727135 := bstep (se 1 (by rfl) ⟨14795351, by rfl⟩ : syracuseStep 19727135 = 29590703) B29590703
theorem B13151423 : Blo 2051435 13151423 := bstep (se 1 (by rfl) ⟨9863567, by rfl⟩ : syracuseStep 13151423 = 19727135) B19727135
theorem B8767615 : Blo 2051435 8767615 := bstep (se 1 (by rfl) ⟨6575711, by rfl⟩ : syracuseStep 8767615 = 13151423) B13151423
theorem B11690153 : Blo 2051435 11690153 := bstep (se 2 (by rfl) ⟨4383807, by rfl⟩ : syracuseStep 11690153 = 8767615) B8767615
theorem B7793435 : Blo 2051435 7793435 := bstep (se 1 (by rfl) ⟨5845076, by rfl⟩ : syracuseStep 7793435 = 11690153) B11690153
theorem B5195623 : Blo 2051435 5195623 := bstep (se 1 (by rfl) ⟨3896717, by rfl⟩ : syracuseStep 5195623 = 7793435) B7793435
theorem B6927497 : Blo 2051435 6927497 := bstep (se 2 (by rfl) ⟨2597811, by rfl⟩ : syracuseStep 6927497 = 5195623) B5195623
theorem B4618331 : Blo 2051435 4618331 := bstep (se 1 (by rfl) ⟨3463748, by rfl⟩ : syracuseStep 4618331 = 6927497) B6927497
theorem B3078887 : Blo 2051435 3078887 := bstep (se 1 (by rfl) ⟨2309165, by rfl⟩ : syracuseStep 3078887 = 4618331) B4618331
theorem B2052591 : Blo 2051435 2052591 := bstep (se 1 (by rfl) ⟨1539443, by rfl⟩ : syracuseStep 2052591 = 3078887) B3078887
theorem B3078893 : Blo 2051435 3078893 := bbase (se 3 (by rfl) ⟨577292, by rfl⟩ : syracuseStep 3078893 = 1154585) (by norm_num)
theorem B2052595 : Blo 2051435 2052595 := bstep (se 1 (by rfl) ⟨1539446, by rfl⟩ : syracuseStep 2052595 = 3078893) B3078893
theorem B4618349 : Blo 2051435 4618349 := bbase (se 3 (by rfl) ⟨865940, by rfl⟩ : syracuseStep 4618349 = 1731881) (by norm_num)
theorem B3078899 : Blo 2051435 3078899 := bstep (se 1 (by rfl) ⟨2309174, by rfl⟩ : syracuseStep 3078899 = 4618349) B4618349
theorem B2052599 : Blo 2051435 2052599 := bstep (se 1 (by rfl) ⟨1539449, by rfl⟩ : syracuseStep 2052599 = 3078899) B3078899
theorem B3896741 : Blo 2051435 3896741 := bbase (se 4 (by rfl) ⟨365319, by rfl⟩ : syracuseStep 3896741 = 730639) (by norm_num)
theorem B2597827 : Blo 2051435 2597827 := bstep (se 1 (by rfl) ⟨1948370, by rfl⟩ : syracuseStep 2597827 = 3896741) B3896741
theorem B3463769 : Blo 2051435 3463769 := bstep (se 2 (by rfl) ⟨1298913, by rfl⟩ : syracuseStep 3463769 = 2597827) B2597827
theorem B2309179 : Blo 2051435 2309179 := bstep (se 1 (by rfl) ⟨1731884, by rfl⟩ : syracuseStep 2309179 = 3463769) B3463769
theorem B3078905 : Blo 2051435 3078905 := bstep (se 2 (by rfl) ⟨1154589, by rfl⟩ : syracuseStep 3078905 = 2309179) B2309179
theorem B2052603 : Blo 2051435 2052603 := bstep (se 1 (by rfl) ⟨1539452, by rfl⟩ : syracuseStep 2052603 = 3078905) B3078905
theorem B2340689 : Blo 2051435 2340689 := bbase (se 2 (by rfl) ⟨877758, by rfl⟩ : syracuseStep 2340689 = 1755517) (by norm_num)
theorem B24967349 : Blo 2051435 24967349 := bstep (se 5 (by rfl) ⟨1170344, by rfl⟩ : syracuseStep 24967349 = 2340689) B2340689
theorem B16644899 : Blo 2051435 16644899 := bstep (se 1 (by rfl) ⟨12483674, by rfl⟩ : syracuseStep 16644899 = 24967349) B24967349
theorem B11096599 : Blo 2051435 11096599 := bstep (se 1 (by rfl) ⟨8322449, by rfl⟩ : syracuseStep 11096599 = 16644899) B16644899
theorem B14795465 : Blo 2051435 14795465 := bstep (se 2 (by rfl) ⟨5548299, by rfl⟩ : syracuseStep 14795465 = 11096599) B11096599
theorem B39454573 : Blo 2051435 39454573 := bstep (se 3 (by rfl) ⟨7397732, by rfl⟩ : syracuseStep 39454573 = 14795465) B14795465
theorem B52606097 : Blo 2051435 52606097 := bstep (se 2 (by rfl) ⟨19727286, by rfl⟩ : syracuseStep 52606097 = 39454573) B39454573
theorem B35070731 : Blo 2051435 35070731 := bstep (se 1 (by rfl) ⟨26303048, by rfl⟩ : syracuseStep 35070731 = 52606097) B52606097
theorem B23380487 : Blo 2051435 23380487 := bstep (se 1 (by rfl) ⟨17535365, by rfl⟩ : syracuseStep 23380487 = 35070731) B35070731
theorem B15586991 : Blo 2051435 15586991 := bstep (se 1 (by rfl) ⟨11690243, by rfl⟩ : syracuseStep 15586991 = 23380487) B23380487
theorem B10391327 : Blo 2051435 10391327 := bstep (se 1 (by rfl) ⟨7793495, by rfl⟩ : syracuseStep 10391327 = 15586991) B15586991
theorem B6927551 : Blo 2051435 6927551 := bstep (se 1 (by rfl) ⟨5195663, by rfl⟩ : syracuseStep 6927551 = 10391327) B10391327
theorem B4618367 : Blo 2051435 4618367 := bstep (se 1 (by rfl) ⟨3463775, by rfl⟩ : syracuseStep 4618367 = 6927551) B6927551
theorem B3078911 : Blo 2051435 3078911 := bstep (se 1 (by rfl) ⟨2309183, by rfl⟩ : syracuseStep 3078911 = 4618367) B4618367
theorem B2052607 : Blo 2051435 2052607 := bstep (se 1 (by rfl) ⟨1539455, by rfl⟩ : syracuseStep 2052607 = 3078911) B3078911
theorem B3078917 : Blo 2051435 3078917 := bbase (se 4 (by rfl) ⟨288648, by rfl⟩ : syracuseStep 3078917 = 577297) (by norm_num)
theorem B2052611 : Blo 2051435 2052611 := bstep (se 1 (by rfl) ⟨1539458, by rfl⟩ : syracuseStep 2052611 = 3078917) B3078917
theorem B3463789 : Blo 2051435 3463789 := bbase (se 3 (by rfl) ⟨649460, by rfl⟩ : syracuseStep 3463789 = 1298921) (by norm_num)
theorem B4618385 : Blo 2051435 4618385 := bstep (se 2 (by rfl) ⟨1731894, by rfl⟩ : syracuseStep 4618385 = 3463789) B3463789
theorem B3078923 : Blo 2051435 3078923 := bstep (se 1 (by rfl) ⟨2309192, by rfl⟩ : syracuseStep 3078923 = 4618385) B4618385
theorem B2052615 : Blo 2051435 2052615 := bstep (se 1 (by rfl) ⟨1539461, by rfl⟩ : syracuseStep 2052615 = 3078923) B3078923
theorem B2309197 : Blo 2051435 2309197 := bbase (se 3 (by rfl) ⟨432974, by rfl⟩ : syracuseStep 2309197 = 865949) (by norm_num)
theorem B3078929 : Blo 2051435 3078929 := bstep (se 2 (by rfl) ⟨1154598, by rfl⟩ : syracuseStep 3078929 = 2309197) B2309197
theorem B2052619 : Blo 2051435 2052619 := bstep (se 1 (by rfl) ⟨1539464, by rfl⟩ : syracuseStep 2052619 = 3078929) B3078929
theorem B6927605 : Blo 2051435 6927605 := bbase (se 5 (by rfl) ⟨324731, by rfl⟩ : syracuseStep 6927605 = 649463) (by norm_num)
theorem B4618403 : Blo 2051435 4618403 := bstep (se 1 (by rfl) ⟨3463802, by rfl⟩ : syracuseStep 4618403 = 6927605) B6927605
theorem B3078935 : Blo 2051435 3078935 := bstep (se 1 (by rfl) ⟨2309201, by rfl⟩ : syracuseStep 3078935 = 4618403) B4618403
theorem B2052623 : Blo 2051435 2052623 := bstep (se 1 (by rfl) ⟨1539467, by rfl⟩ : syracuseStep 2052623 = 3078935) B3078935
theorem B3078941 : Blo 2051435 3078941 := bbase (se 3 (by rfl) ⟨577301, by rfl⟩ : syracuseStep 3078941 = 1154603) (by norm_num)
theorem B2052627 : Blo 2051435 2052627 := bstep (se 1 (by rfl) ⟨1539470, by rfl⟩ : syracuseStep 2052627 = 3078941) B3078941
theorem B4618421 : Blo 2051435 4618421 := bbase (se 5 (by rfl) ⟨216488, by rfl⟩ : syracuseStep 4618421 = 432977) (by norm_num)
theorem B3078947 : Blo 2051435 3078947 := bstep (se 1 (by rfl) ⟨2309210, by rfl⟩ : syracuseStep 3078947 = 4618421) B4618421
theorem B2052631 : Blo 2051435 2052631 := bstep (se 1 (by rfl) ⟨1539473, by rfl⟩ : syracuseStep 2052631 = 3078947) B3078947
theorem B2774189 : Blo 2051435 2774189 := bbase (se 3 (by rfl) ⟨520160, by rfl⟩ : syracuseStep 2774189 = 1040321) (by norm_num)
theorem B7397837 : Blo 2051435 7397837 := bstep (se 3 (by rfl) ⟨1387094, by rfl⟩ : syracuseStep 7397837 = 2774189) B2774189
theorem B4931891 : Blo 2051435 4931891 := bstep (se 1 (by rfl) ⟨3698918, by rfl⟩ : syracuseStep 4931891 = 7397837) B7397837
theorem B3287927 : Blo 2051435 3287927 := bstep (se 1 (by rfl) ⟨2465945, by rfl⟩ : syracuseStep 3287927 = 4931891) B4931891
theorem B2191951 : Blo 2051435 2191951 := bstep (se 1 (by rfl) ⟨1643963, by rfl⟩ : syracuseStep 2191951 = 3287927) B3287927
theorem B11690405 : Blo 2051435 11690405 := bstep (se 4 (by rfl) ⟨1095975, by rfl⟩ : syracuseStep 11690405 = 2191951) B2191951
theorem B7793603 : Blo 2051435 7793603 := bstep (se 1 (by rfl) ⟨5845202, by rfl⟩ : syracuseStep 7793603 = 11690405) B11690405
theorem B5195735 : Blo 2051435 5195735 := bstep (se 1 (by rfl) ⟨3896801, by rfl⟩ : syracuseStep 5195735 = 7793603) B7793603
theorem B3463823 : Blo 2051435 3463823 := bstep (se 1 (by rfl) ⟨2597867, by rfl⟩ : syracuseStep 3463823 = 5195735) B5195735
theorem B2309215 : Blo 2051435 2309215 := bstep (se 1 (by rfl) ⟨1731911, by rfl⟩ : syracuseStep 2309215 = 3463823) B3463823
theorem B3078953 : Blo 2051435 3078953 := bstep (se 2 (by rfl) ⟨1154607, by rfl⟩ : syracuseStep 3078953 = 2309215) B2309215
theorem B2052635 : Blo 2051435 2052635 := bstep (se 1 (by rfl) ⟨1539476, by rfl⟩ : syracuseStep 2052635 = 3078953) B3078953
theorem B3287933 : Blo 2051435 3287933 := bbase (se 3 (by rfl) ⟨616487, by rfl⟩ : syracuseStep 3287933 = 1232975) (by norm_num)
theorem B2191955 : Blo 2051435 2191955 := bstep (se 1 (by rfl) ⟨1643966, by rfl⟩ : syracuseStep 2191955 = 3287933) B3287933
theorem B5845213 : Blo 2051435 5845213 := bstep (se 3 (by rfl) ⟨1095977, by rfl⟩ : syracuseStep 5845213 = 2191955) B2191955
theorem B7793617 : Blo 2051435 7793617 := bstep (se 2 (by rfl) ⟨2922606, by rfl⟩ : syracuseStep 7793617 = 5845213) B5845213
theorem B10391489 : Blo 2051435 10391489 := bstep (se 2 (by rfl) ⟨3896808, by rfl⟩ : syracuseStep 10391489 = 7793617) B7793617
theorem B6927659 : Blo 2051435 6927659 := bstep (se 1 (by rfl) ⟨5195744, by rfl⟩ : syracuseStep 6927659 = 10391489) B10391489
theorem B4618439 : Blo 2051435 4618439 := bstep (se 1 (by rfl) ⟨3463829, by rfl⟩ : syracuseStep 4618439 = 6927659) B6927659
theorem B3078959 : Blo 2051435 3078959 := bstep (se 1 (by rfl) ⟨2309219, by rfl⟩ : syracuseStep 3078959 = 4618439) B4618439
theorem B2052639 : Blo 2051435 2052639 := bstep (se 1 (by rfl) ⟨1539479, by rfl⟩ : syracuseStep 2052639 = 3078959) B3078959
theorem B3078965 : Blo 2051435 3078965 := bbase (se 5 (by rfl) ⟨144326, by rfl⟩ : syracuseStep 3078965 = 288653) (by norm_num)
theorem B2052643 : Blo 2051435 2052643 := bstep (se 1 (by rfl) ⟨1539482, by rfl⟩ : syracuseStep 2052643 = 3078965) B3078965
theorem B5195765 : Blo 2051435 5195765 := bbase (se 5 (by rfl) ⟨243551, by rfl⟩ : syracuseStep 5195765 = 487103) (by norm_num)
theorem B3463843 : Blo 2051435 3463843 := bstep (se 1 (by rfl) ⟨2597882, by rfl⟩ : syracuseStep 3463843 = 5195765) B5195765
theorem B4618457 : Blo 2051435 4618457 := bstep (se 2 (by rfl) ⟨1731921, by rfl⟩ : syracuseStep 4618457 = 3463843) B3463843
theorem B3078971 : Blo 2051435 3078971 := bstep (se 1 (by rfl) ⟨2309228, by rfl⟩ : syracuseStep 3078971 = 4618457) B4618457
theorem B2052647 : Blo 2051435 2052647 := bstep (se 1 (by rfl) ⟨1539485, by rfl⟩ : syracuseStep 2052647 = 3078971) B3078971
theorem B2309233 : Blo 2051435 2309233 := bbase (se 2 (by rfl) ⟨865962, by rfl⟩ : syracuseStep 2309233 = 1731925) (by norm_num)
theorem B3078977 : Blo 2051435 3078977 := bstep (se 2 (by rfl) ⟨1154616, by rfl⟩ : syracuseStep 3078977 = 2309233) B2309233
theorem B2052651 : Blo 2051435 2052651 := bstep (se 1 (by rfl) ⟨1539488, by rfl⟩ : syracuseStep 2052651 = 3078977) B3078977
theorem B2465969 : Blo 2051435 2465969 := bbase (se 2 (by rfl) ⟨924738, by rfl⟩ : syracuseStep 2465969 = 1849477) (by norm_num)
theorem B6575917 : Blo 2051435 6575917 := bstep (se 3 (by rfl) ⟨1232984, by rfl⟩ : syracuseStep 6575917 = 2465969) B2465969
theorem B8767889 : Blo 2051435 8767889 := bstep (se 2 (by rfl) ⟨3287958, by rfl⟩ : syracuseStep 8767889 = 6575917) B6575917
theorem B5845259 : Blo 2051435 5845259 := bstep (se 1 (by rfl) ⟨4383944, by rfl⟩ : syracuseStep 5845259 = 8767889) B8767889
theorem B3896839 : Blo 2051435 3896839 := bstep (se 1 (by rfl) ⟨2922629, by rfl⟩ : syracuseStep 3896839 = 5845259) B5845259
theorem B5195785 : Blo 2051435 5195785 := bstep (se 2 (by rfl) ⟨1948419, by rfl⟩ : syracuseStep 5195785 = 3896839) B3896839
theorem B6927713 : Blo 2051435 6927713 := bstep (se 2 (by rfl) ⟨2597892, by rfl⟩ : syracuseStep 6927713 = 5195785) B5195785
theorem B4618475 : Blo 2051435 4618475 := bstep (se 1 (by rfl) ⟨3463856, by rfl⟩ : syracuseStep 4618475 = 6927713) B6927713
theorem B3078983 : Blo 2051435 3078983 := bstep (se 1 (by rfl) ⟨2309237, by rfl⟩ : syracuseStep 3078983 = 4618475) B4618475
theorem B2052655 : Blo 2051435 2052655 := bstep (se 1 (by rfl) ⟨1539491, by rfl⟩ : syracuseStep 2052655 = 3078983) B3078983
theorem B3078989 : Blo 2051435 3078989 := bbase (se 3 (by rfl) ⟨577310, by rfl⟩ : syracuseStep 3078989 = 1154621) (by norm_num)
theorem B2052659 : Blo 2051435 2052659 := bstep (se 1 (by rfl) ⟨1539494, by rfl⟩ : syracuseStep 2052659 = 3078989) B3078989
theorem B4618493 : Blo 2051435 4618493 := bbase (se 3 (by rfl) ⟨865967, by rfl⟩ : syracuseStep 4618493 = 1731935) (by norm_num)
theorem B3078995 : Blo 2051435 3078995 := bstep (se 1 (by rfl) ⟨2309246, by rfl⟩ : syracuseStep 3078995 = 4618493) B4618493
theorem B2052663 : Blo 2051435 2052663 := bstep (se 1 (by rfl) ⟨1539497, by rfl⟩ : syracuseStep 2052663 = 3078995) B3078995
theorem B3463877 : Blo 2051435 3463877 := bbase (se 4 (by rfl) ⟨324738, by rfl⟩ : syracuseStep 3463877 = 649477) (by norm_num)
theorem B2309251 : Blo 2051435 2309251 := bstep (se 1 (by rfl) ⟨1731938, by rfl⟩ : syracuseStep 2309251 = 3463877) B3463877
theorem B3079001 : Blo 2051435 3079001 := bstep (se 2 (by rfl) ⟨1154625, by rfl⟩ : syracuseStep 3079001 = 2309251) B2309251
theorem B2052667 : Blo 2051435 2052667 := bstep (se 1 (by rfl) ⟨1539500, by rfl⟩ : syracuseStep 2052667 = 3079001) B3079001
theorem B15587477 : Blo 2051435 15587477 := bbase (se 6 (by rfl) ⟨365331, by rfl⟩ : syracuseStep 15587477 = 730663) (by norm_num)
theorem B10391651 : Blo 2051435 10391651 := bstep (se 1 (by rfl) ⟨7793738, by rfl⟩ : syracuseStep 10391651 = 15587477) B15587477
theorem B6927767 : Blo 2051435 6927767 := bstep (se 1 (by rfl) ⟨5195825, by rfl⟩ : syracuseStep 6927767 = 10391651) B10391651
theorem B4618511 : Blo 2051435 4618511 := bstep (se 1 (by rfl) ⟨3463883, by rfl⟩ : syracuseStep 4618511 = 6927767) B6927767
theorem B3079007 : Blo 2051435 3079007 := bstep (se 1 (by rfl) ⟨2309255, by rfl⟩ : syracuseStep 3079007 = 4618511) B4618511
theorem B2052671 : Blo 2051435 2052671 := bstep (se 1 (by rfl) ⟨1539503, by rfl⟩ : syracuseStep 2052671 = 3079007) B3079007
theorem B3079013 : Blo 2051435 3079013 := bbase (se 4 (by rfl) ⟨288657, by rfl⟩ : syracuseStep 3079013 = 577315) (by norm_num)
theorem B2052675 : Blo 2051435 2052675 := bstep (se 1 (by rfl) ⟨1539506, by rfl⟩ : syracuseStep 2052675 = 3079013) B3079013
theorem B3896885 : Blo 2051435 3896885 := bbase (se 5 (by rfl) ⟨182666, by rfl⟩ : syracuseStep 3896885 = 365333) (by norm_num)
theorem B2597923 : Blo 2051435 2597923 := bstep (se 1 (by rfl) ⟨1948442, by rfl⟩ : syracuseStep 2597923 = 3896885) B3896885
theorem B3463897 : Blo 2051435 3463897 := bstep (se 2 (by rfl) ⟨1298961, by rfl⟩ : syracuseStep 3463897 = 2597923) B2597923
theorem B4618529 : Blo 2051435 4618529 := bstep (se 2 (by rfl) ⟨1731948, by rfl⟩ : syracuseStep 4618529 = 3463897) B3463897
theorem B3079019 : Blo 2051435 3079019 := bstep (se 1 (by rfl) ⟨2309264, by rfl⟩ : syracuseStep 3079019 = 4618529) B4618529
theorem B2052679 : Blo 2051435 2052679 := bstep (se 1 (by rfl) ⟨1539509, by rfl⟩ : syracuseStep 2052679 = 3079019) B3079019
theorem B2309269 : Blo 2051435 2309269 := bbase (se 6 (by rfl) ⟨54123, by rfl⟩ : syracuseStep 2309269 = 108247) (by norm_num)
theorem B3079025 : Blo 2051435 3079025 := bstep (se 2 (by rfl) ⟨1154634, by rfl⟩ : syracuseStep 3079025 = 2309269) B2309269
theorem B2052683 : Blo 2051435 2052683 := bstep (se 1 (by rfl) ⟨1539512, by rfl⟩ : syracuseStep 2052683 = 3079025) B3079025
theorem B2597933 : Blo 2051435 2597933 := bbase (se 3 (by rfl) ⟨487112, by rfl⟩ : syracuseStep 2597933 = 974225) (by norm_num)
theorem B6927821 : Blo 2051435 6927821 := bstep (se 3 (by rfl) ⟨1298966, by rfl⟩ : syracuseStep 6927821 = 2597933) B2597933
theorem B4618547 : Blo 2051435 4618547 := bstep (se 1 (by rfl) ⟨3463910, by rfl⟩ : syracuseStep 4618547 = 6927821) B6927821
theorem B3079031 : Blo 2051435 3079031 := bstep (se 1 (by rfl) ⟨2309273, by rfl⟩ : syracuseStep 3079031 = 4618547) B4618547
theorem B2052687 : Blo 2051435 2052687 := bstep (se 1 (by rfl) ⟨1539515, by rfl⟩ : syracuseStep 2052687 = 3079031) B3079031
theorem B3079037 : Blo 2051435 3079037 := bbase (se 3 (by rfl) ⟨577319, by rfl⟩ : syracuseStep 3079037 = 1154639) (by norm_num)
theorem B2052691 : Blo 2051435 2052691 := bstep (se 1 (by rfl) ⟨1539518, by rfl⟩ : syracuseStep 2052691 = 3079037) B3079037
theorem B4618565 : Blo 2051435 4618565 := bbase (se 4 (by rfl) ⟨432990, by rfl⟩ : syracuseStep 4618565 = 865981) (by norm_num)
theorem B3079043 : Blo 2051435 3079043 := bstep (se 1 (by rfl) ⟨2309282, by rfl⟩ : syracuseStep 3079043 = 4618565) B4618565
theorem B2052695 : Blo 2051435 2052695 := bstep (se 1 (by rfl) ⟨1539521, by rfl⟩ : syracuseStep 2052695 = 3079043) B3079043
theorem B4161413 : Blo 2051435 4161413 := bbase (se 4 (by rfl) ⟨390132, by rfl⟩ : syracuseStep 4161413 = 780265) (by norm_num)
theorem B11097101 : Blo 2051435 11097101 := bstep (se 3 (by rfl) ⟨2080706, by rfl⟩ : syracuseStep 11097101 = 4161413) B4161413
theorem B7398067 : Blo 2051435 7398067 := bstep (se 1 (by rfl) ⟨5548550, by rfl⟩ : syracuseStep 7398067 = 11097101) B11097101
theorem B9864089 : Blo 2051435 9864089 := bstep (se 2 (by rfl) ⟨3699033, by rfl⟩ : syracuseStep 9864089 = 7398067) B7398067
theorem B6576059 : Blo 2051435 6576059 := bstep (se 1 (by rfl) ⟨4932044, by rfl⟩ : syracuseStep 6576059 = 9864089) B9864089
theorem B4384039 : Blo 2051435 4384039 := bstep (se 1 (by rfl) ⟨3288029, by rfl⟩ : syracuseStep 4384039 = 6576059) B6576059
theorem B5845385 : Blo 2051435 5845385 := bstep (se 2 (by rfl) ⟨2192019, by rfl⟩ : syracuseStep 5845385 = 4384039) B4384039
theorem B3896923 : Blo 2051435 3896923 := bstep (se 1 (by rfl) ⟨2922692, by rfl⟩ : syracuseStep 3896923 = 5845385) B5845385
theorem B5195897 : Blo 2051435 5195897 := bstep (se 2 (by rfl) ⟨1948461, by rfl⟩ : syracuseStep 5195897 = 3896923) B3896923
theorem B3463931 : Blo 2051435 3463931 := bstep (se 1 (by rfl) ⟨2597948, by rfl⟩ : syracuseStep 3463931 = 5195897) B5195897
theorem B2309287 : Blo 2051435 2309287 := bstep (se 1 (by rfl) ⟨1731965, by rfl⟩ : syracuseStep 2309287 = 3463931) B3463931
theorem B3079049 : Blo 2051435 3079049 := bstep (se 2 (by rfl) ⟨1154643, by rfl⟩ : syracuseStep 3079049 = 2309287) B2309287
theorem B2052699 : Blo 2051435 2052699 := bstep (se 1 (by rfl) ⟨1539524, by rfl⟩ : syracuseStep 2052699 = 3079049) B3079049
theorem B10391813 : Blo 2051435 10391813 := bbase (se 4 (by rfl) ⟨974232, by rfl⟩ : syracuseStep 10391813 = 1948465) (by norm_num)
theorem B6927875 : Blo 2051435 6927875 := bstep (se 1 (by rfl) ⟨5195906, by rfl⟩ : syracuseStep 6927875 = 10391813) B10391813
theorem B4618583 : Blo 2051435 4618583 := bstep (se 1 (by rfl) ⟨3463937, by rfl⟩ : syracuseStep 4618583 = 6927875) B6927875
theorem B3079055 : Blo 2051435 3079055 := bstep (se 1 (by rfl) ⟨2309291, by rfl⟩ : syracuseStep 3079055 = 4618583) B4618583
theorem B2052703 : Blo 2051435 2052703 := bstep (se 1 (by rfl) ⟨1539527, by rfl⟩ : syracuseStep 2052703 = 3079055) B3079055
theorem B3079061 : Blo 2051435 3079061 := bbase (se 6 (by rfl) ⟨72165, by rfl⟩ : syracuseStep 3079061 = 144331) (by norm_num)
theorem B2052707 : Blo 2051435 2052707 := bstep (se 1 (by rfl) ⟨1539530, by rfl⟩ : syracuseStep 2052707 = 3079061) B3079061
theorem B11690837 : Blo 2051435 11690837 := bbase (se 9 (by rfl) ⟨34250, by rfl⟩ : syracuseStep 11690837 = 68501) (by norm_num)
theorem B7793891 : Blo 2051435 7793891 := bstep (se 1 (by rfl) ⟨5845418, by rfl⟩ : syracuseStep 7793891 = 11690837) B11690837
theorem B5195927 : Blo 2051435 5195927 := bstep (se 1 (by rfl) ⟨3896945, by rfl⟩ : syracuseStep 5195927 = 7793891) B7793891
theorem B3463951 : Blo 2051435 3463951 := bstep (se 1 (by rfl) ⟨2597963, by rfl⟩ : syracuseStep 3463951 = 5195927) B5195927
theorem B4618601 : Blo 2051435 4618601 := bstep (se 2 (by rfl) ⟨1731975, by rfl⟩ : syracuseStep 4618601 = 3463951) B3463951
theorem B3079067 : Blo 2051435 3079067 := bstep (se 1 (by rfl) ⟨2309300, by rfl⟩ : syracuseStep 3079067 = 4618601) B4618601
theorem B2052711 : Blo 2051435 2052711 := bstep (se 1 (by rfl) ⟨1539533, by rfl⟩ : syracuseStep 2052711 = 3079067) B3079067
theorem B2309305 : Blo 2051435 2309305 := bbase (se 2 (by rfl) ⟨865989, by rfl⟩ : syracuseStep 2309305 = 1731979) (by norm_num)
theorem B3079073 : Blo 2051435 3079073 := bstep (se 2 (by rfl) ⟨1154652, by rfl⟩ : syracuseStep 3079073 = 2309305) B2309305
theorem B2052715 : Blo 2051435 2052715 := bstep (se 1 (by rfl) ⟨1539536, by rfl⟩ : syracuseStep 2052715 = 3079073) B3079073
theorem B3288061 : Blo 2051435 3288061 := bbase (se 3 (by rfl) ⟨616511, by rfl⟩ : syracuseStep 3288061 = 1233023) (by norm_num)
theorem B4384081 : Blo 2051435 4384081 := bstep (se 2 (by rfl) ⟨1644030, by rfl⟩ : syracuseStep 4384081 = 3288061) B3288061
theorem B5845441 : Blo 2051435 5845441 := bstep (se 2 (by rfl) ⟨2192040, by rfl⟩ : syracuseStep 5845441 = 4384081) B4384081
theorem B7793921 : Blo 2051435 7793921 := bstep (se 2 (by rfl) ⟨2922720, by rfl⟩ : syracuseStep 7793921 = 5845441) B5845441
theorem B5195947 : Blo 2051435 5195947 := bstep (se 1 (by rfl) ⟨3896960, by rfl⟩ : syracuseStep 5195947 = 7793921) B7793921
theorem B6927929 : Blo 2051435 6927929 := bstep (se 2 (by rfl) ⟨2597973, by rfl⟩ : syracuseStep 6927929 = 5195947) B5195947
theorem B4618619 : Blo 2051435 4618619 := bstep (se 1 (by rfl) ⟨3463964, by rfl⟩ : syracuseStep 4618619 = 6927929) B6927929
theorem B3079079 : Blo 2051435 3079079 := bstep (se 1 (by rfl) ⟨2309309, by rfl⟩ : syracuseStep 3079079 = 4618619) B4618619
theorem B2052719 : Blo 2051435 2052719 := bstep (se 1 (by rfl) ⟨1539539, by rfl⟩ : syracuseStep 2052719 = 3079079) B3079079
theorem B3079085 : Blo 2051435 3079085 := bbase (se 3 (by rfl) ⟨577328, by rfl⟩ : syracuseStep 3079085 = 1154657) (by norm_num)
theorem B2052723 : Blo 2051435 2052723 := bstep (se 1 (by rfl) ⟨1539542, by rfl⟩ : syracuseStep 2052723 = 3079085) B3079085
theorem B4618637 : Blo 2051435 4618637 := bbase (se 3 (by rfl) ⟨865994, by rfl⟩ : syracuseStep 4618637 = 1731989) (by norm_num)
theorem B3079091 : Blo 2051435 3079091 := bstep (se 1 (by rfl) ⟨2309318, by rfl⟩ : syracuseStep 3079091 = 4618637) B4618637
theorem B2052727 : Blo 2051435 2052727 := bstep (se 1 (by rfl) ⟨1539545, by rfl⟩ : syracuseStep 2052727 = 3079091) B3079091
theorem B2597989 : Blo 2051435 2597989 := bbase (se 4 (by rfl) ⟨243561, by rfl⟩ : syracuseStep 2597989 = 487123) (by norm_num)
theorem B3463985 : Blo 2051435 3463985 := bstep (se 2 (by rfl) ⟨1298994, by rfl⟩ : syracuseStep 3463985 = 2597989) B2597989
theorem B2309323 : Blo 2051435 2309323 := bstep (se 1 (by rfl) ⟨1731992, by rfl⟩ : syracuseStep 2309323 = 3463985) B3463985
theorem B3079097 : Blo 2051435 3079097 := bstep (se 2 (by rfl) ⟨1154661, by rfl⟩ : syracuseStep 3079097 = 2309323) B2309323
theorem B2052731 : Blo 2051435 2052731 := bstep (se 1 (by rfl) ⟨1539548, by rfl⟩ : syracuseStep 2052731 = 3079097) B3079097
theorem B4161485 : Blo 2051435 4161485 := bbase (se 3 (by rfl) ⟨780278, by rfl⟩ : syracuseStep 4161485 = 1560557) (by norm_num)
theorem B2774323 : Blo 2051435 2774323 := bstep (se 1 (by rfl) ⟨2080742, by rfl⟩ : syracuseStep 2774323 = 4161485) B4161485
theorem B3699097 : Blo 2051435 3699097 := bstep (se 2 (by rfl) ⟨1387161, by rfl⟩ : syracuseStep 3699097 = 2774323) B2774323
theorem B19728517 : Blo 2051435 19728517 := bstep (se 4 (by rfl) ⟨1849548, by rfl⟩ : syracuseStep 19728517 = 3699097) B3699097
theorem B26304689 : Blo 2051435 26304689 := bstep (se 2 (by rfl) ⟨9864258, by rfl⟩ : syracuseStep 26304689 = 19728517) B19728517
theorem B17536459 : Blo 2051435 17536459 := bstep (se 1 (by rfl) ⟨13152344, by rfl⟩ : syracuseStep 17536459 = 26304689) B26304689
theorem B23381945 : Blo 2051435 23381945 := bstep (se 2 (by rfl) ⟨8768229, by rfl⟩ : syracuseStep 23381945 = 17536459) B17536459
theorem B15587963 : Blo 2051435 15587963 := bstep (se 1 (by rfl) ⟨11690972, by rfl⟩ : syracuseStep 15587963 = 23381945) B23381945
theorem B10391975 : Blo 2051435 10391975 := bstep (se 1 (by rfl) ⟨7793981, by rfl⟩ : syracuseStep 10391975 = 15587963) B15587963
theorem B6927983 : Blo 2051435 6927983 := bstep (se 1 (by rfl) ⟨5195987, by rfl⟩ : syracuseStep 6927983 = 10391975) B10391975
theorem B4618655 : Blo 2051435 4618655 := bstep (se 1 (by rfl) ⟨3463991, by rfl⟩ : syracuseStep 4618655 = 6927983) B6927983
theorem B3079103 : Blo 2051435 3079103 := bstep (se 1 (by rfl) ⟨2309327, by rfl⟩ : syracuseStep 3079103 = 4618655) B4618655
theorem B2052735 : Blo 2051435 2052735 := bstep (se 1 (by rfl) ⟨1539551, by rfl⟩ : syracuseStep 2052735 = 3079103) B3079103
theorem B3079109 : Blo 2051435 3079109 := bbase (se 4 (by rfl) ⟨288666, by rfl⟩ : syracuseStep 3079109 = 577333) (by norm_num)
theorem B2052739 : Blo 2051435 2052739 := bstep (se 1 (by rfl) ⟨1539554, by rfl⟩ : syracuseStep 2052739 = 3079109) B3079109
theorem B3464005 : Blo 2051435 3464005 := bbase (se 4 (by rfl) ⟨324750, by rfl⟩ : syracuseStep 3464005 = 649501) (by norm_num)
theorem B4618673 : Blo 2051435 4618673 := bstep (se 2 (by rfl) ⟨1732002, by rfl⟩ : syracuseStep 4618673 = 3464005) B3464005
theorem B3079115 : Blo 2051435 3079115 := bstep (se 1 (by rfl) ⟨2309336, by rfl⟩ : syracuseStep 3079115 = 4618673) B4618673
theorem B2052743 : Blo 2051435 2052743 := bstep (se 1 (by rfl) ⟨1539557, by rfl⟩ : syracuseStep 2052743 = 3079115) B3079115
theorem B2309341 : Blo 2051435 2309341 := bbase (se 3 (by rfl) ⟨433001, by rfl⟩ : syracuseStep 2309341 = 866003) (by norm_num)
theorem B3079121 : Blo 2051435 3079121 := bstep (se 2 (by rfl) ⟨1154670, by rfl⟩ : syracuseStep 3079121 = 2309341) B2309341
theorem B2052747 : Blo 2051435 2052747 := bstep (se 1 (by rfl) ⟨1539560, by rfl⟩ : syracuseStep 2052747 = 3079121) B3079121
theorem B6928037 : Blo 2051435 6928037 := bbase (se 4 (by rfl) ⟨649503, by rfl⟩ : syracuseStep 6928037 = 1299007) (by norm_num)
theorem B4618691 : Blo 2051435 4618691 := bstep (se 1 (by rfl) ⟨3464018, by rfl⟩ : syracuseStep 4618691 = 6928037) B6928037
theorem B3079127 : Blo 2051435 3079127 := bstep (se 1 (by rfl) ⟨2309345, by rfl⟩ : syracuseStep 3079127 = 4618691) B4618691
theorem B2052751 : Blo 2051435 2052751 := bstep (se 1 (by rfl) ⟨1539563, by rfl⟩ : syracuseStep 2052751 = 3079127) B3079127
theorem B3079133 : Blo 2051435 3079133 := bbase (se 3 (by rfl) ⟨577337, by rfl⟩ : syracuseStep 3079133 = 1154675) (by norm_num)
theorem B2052755 : Blo 2051435 2052755 := bstep (se 1 (by rfl) ⟨1539566, by rfl⟩ : syracuseStep 2052755 = 3079133) B3079133
theorem B4618709 : Blo 2051435 4618709 := bbase (se 7 (by rfl) ⟨54125, by rfl⟩ : syracuseStep 4618709 = 108251) (by norm_num)
theorem B3079139 : Blo 2051435 3079139 := bstep (se 1 (by rfl) ⟨2309354, by rfl⟩ : syracuseStep 3079139 = 4618709) B4618709
theorem B2052759 : Blo 2051435 2052759 := bstep (se 1 (by rfl) ⟨1539569, by rfl⟩ : syracuseStep 2052759 = 3079139) B3079139
theorem B3121157 : Blo 2051435 3121157 := bbase (se 4 (by rfl) ⟨292608, by rfl⟩ : syracuseStep 3121157 = 585217) (by norm_num)
theorem B2080771 : Blo 2051435 2080771 := bstep (se 1 (by rfl) ⟨1560578, by rfl⟩ : syracuseStep 2080771 = 3121157) B3121157
theorem B44389781 : Blo 2051435 44389781 := bstep (se 6 (by rfl) ⟨1040385, by rfl⟩ : syracuseStep 44389781 = 2080771) B2080771
theorem B29593187 : Blo 2051435 29593187 := bstep (se 1 (by rfl) ⟨22194890, by rfl⟩ : syracuseStep 29593187 = 44389781) B44389781
theorem B19728791 : Blo 2051435 19728791 := bstep (se 1 (by rfl) ⟨14796593, by rfl⟩ : syracuseStep 19728791 = 29593187) B29593187
theorem B13152527 : Blo 2051435 13152527 := bstep (se 1 (by rfl) ⟨9864395, by rfl⟩ : syracuseStep 13152527 = 19728791) B19728791
theorem B8768351 : Blo 2051435 8768351 := bstep (se 1 (by rfl) ⟨6576263, by rfl⟩ : syracuseStep 8768351 = 13152527) B13152527
theorem B5845567 : Blo 2051435 5845567 := bstep (se 1 (by rfl) ⟨4384175, by rfl⟩ : syracuseStep 5845567 = 8768351) B8768351
theorem B7794089 : Blo 2051435 7794089 := bstep (se 2 (by rfl) ⟨2922783, by rfl⟩ : syracuseStep 7794089 = 5845567) B5845567
theorem B5196059 : Blo 2051435 5196059 := bstep (se 1 (by rfl) ⟨3897044, by rfl⟩ : syracuseStep 5196059 = 7794089) B7794089
theorem B3464039 : Blo 2051435 3464039 := bstep (se 1 (by rfl) ⟨2598029, by rfl⟩ : syracuseStep 3464039 = 5196059) B5196059
theorem B2309359 : Blo 2051435 2309359 := bstep (se 1 (by rfl) ⟨1732019, by rfl⟩ : syracuseStep 2309359 = 3464039) B3464039
theorem B3079145 : Blo 2051435 3079145 := bstep (se 2 (by rfl) ⟨1154679, by rfl⟩ : syracuseStep 3079145 = 2309359) B2309359
theorem B2052763 : Blo 2051435 2052763 := bstep (se 1 (by rfl) ⟨1539572, by rfl⟩ : syracuseStep 2052763 = 3079145) B3079145
theorem B3511309 : Blo 2051435 3511309 := bbase (se 3 (by rfl) ⟨658370, by rfl⟩ : syracuseStep 3511309 = 1316741) (by norm_num)
theorem B4681745 : Blo 2051435 4681745 := bstep (se 2 (by rfl) ⟨1755654, by rfl⟩ : syracuseStep 4681745 = 3511309) B3511309
theorem B3121163 : Blo 2051435 3121163 := bstep (se 1 (by rfl) ⟨2340872, by rfl⟩ : syracuseStep 3121163 = 4681745) B4681745
theorem B2080775 : Blo 2051435 2080775 := bstep (se 1 (by rfl) ⟨1560581, by rfl⟩ : syracuseStep 2080775 = 3121163) B3121163
theorem B5548733 : Blo 2051435 5548733 := bstep (se 3 (by rfl) ⟨1040387, by rfl⟩ : syracuseStep 5548733 = 2080775) B2080775
theorem B3699155 : Blo 2051435 3699155 := bstep (se 1 (by rfl) ⟨2774366, by rfl⟩ : syracuseStep 3699155 = 5548733) B5548733
theorem B9864413 : Blo 2051435 9864413 := bstep (se 3 (by rfl) ⟨1849577, by rfl⟩ : syracuseStep 9864413 = 3699155) B3699155
theorem B6576275 : Blo 2051435 6576275 := bstep (se 1 (by rfl) ⟨4932206, by rfl⟩ : syracuseStep 6576275 = 9864413) B9864413
theorem B17536733 : Blo 2051435 17536733 := bstep (se 3 (by rfl) ⟨3288137, by rfl⟩ : syracuseStep 17536733 = 6576275) B6576275
theorem B11691155 : Blo 2051435 11691155 := bstep (se 1 (by rfl) ⟨8768366, by rfl⟩ : syracuseStep 11691155 = 17536733) B17536733
theorem B7794103 : Blo 2051435 7794103 := bstep (se 1 (by rfl) ⟨5845577, by rfl⟩ : syracuseStep 7794103 = 11691155) B11691155
theorem B10392137 : Blo 2051435 10392137 := bstep (se 2 (by rfl) ⟨3897051, by rfl⟩ : syracuseStep 10392137 = 7794103) B7794103
theorem B6928091 : Blo 2051435 6928091 := bstep (se 1 (by rfl) ⟨5196068, by rfl⟩ : syracuseStep 6928091 = 10392137) B10392137
theorem B4618727 : Blo 2051435 4618727 := bstep (se 1 (by rfl) ⟨3464045, by rfl⟩ : syracuseStep 4618727 = 6928091) B6928091
theorem B3079151 : Blo 2051435 3079151 := bstep (se 1 (by rfl) ⟨2309363, by rfl⟩ : syracuseStep 3079151 = 4618727) B4618727
theorem B2052767 : Blo 2051435 2052767 := bstep (se 1 (by rfl) ⟨1539575, by rfl⟩ : syracuseStep 2052767 = 3079151) B3079151
theorem B3079157 : Blo 2051435 3079157 := bbase (se 5 (by rfl) ⟨144335, by rfl⟩ : syracuseStep 3079157 = 288671) (by norm_num)
theorem B2052771 : Blo 2051435 2052771 := bstep (se 1 (by rfl) ⟨1539578, by rfl⟩ : syracuseStep 2052771 = 3079157) B3079157
theorem B7398341 : Blo 2051435 7398341 := bbase (se 4 (by rfl) ⟨693594, by rfl⟩ : syracuseStep 7398341 = 1387189) (by norm_num)
theorem B4932227 : Blo 2051435 4932227 := bstep (se 1 (by rfl) ⟨3699170, by rfl⟩ : syracuseStep 4932227 = 7398341) B7398341
theorem B3288151 : Blo 2051435 3288151 := bstep (se 1 (by rfl) ⟨2466113, by rfl⟩ : syracuseStep 3288151 = 4932227) B4932227
theorem B4384201 : Blo 2051435 4384201 := bstep (se 2 (by rfl) ⟨1644075, by rfl⟩ : syracuseStep 4384201 = 3288151) B3288151
theorem B5845601 : Blo 2051435 5845601 := bstep (se 2 (by rfl) ⟨2192100, by rfl⟩ : syracuseStep 5845601 = 4384201) B4384201
theorem B3897067 : Blo 2051435 3897067 := bstep (se 1 (by rfl) ⟨2922800, by rfl⟩ : syracuseStep 3897067 = 5845601) B5845601
theorem B5196089 : Blo 2051435 5196089 := bstep (se 2 (by rfl) ⟨1948533, by rfl⟩ : syracuseStep 5196089 = 3897067) B3897067
theorem B3464059 : Blo 2051435 3464059 := bstep (se 1 (by rfl) ⟨2598044, by rfl⟩ : syracuseStep 3464059 = 5196089) B5196089
theorem B4618745 : Blo 2051435 4618745 := bstep (se 2 (by rfl) ⟨1732029, by rfl⟩ : syracuseStep 4618745 = 3464059) B3464059
theorem B3079163 : Blo 2051435 3079163 := bstep (se 1 (by rfl) ⟨2309372, by rfl⟩ : syracuseStep 3079163 = 4618745) B4618745
theorem B2052775 : Blo 2051435 2052775 := bstep (se 1 (by rfl) ⟨1539581, by rfl⟩ : syracuseStep 2052775 = 3079163) B3079163
theorem B2309377 : Blo 2051435 2309377 := bbase (se 2 (by rfl) ⟨866016, by rfl⟩ : syracuseStep 2309377 = 1732033) (by norm_num)
theorem B3079169 : Blo 2051435 3079169 := bstep (se 2 (by rfl) ⟨1154688, by rfl⟩ : syracuseStep 3079169 = 2309377) B2309377
theorem B2052779 : Blo 2051435 2052779 := bstep (se 1 (by rfl) ⟨1539584, by rfl⟩ : syracuseStep 2052779 = 3079169) B3079169
theorem B5196109 : Blo 2051435 5196109 := bbase (se 3 (by rfl) ⟨974270, by rfl⟩ : syracuseStep 5196109 = 1948541) (by norm_num)
theorem B6928145 : Blo 2051435 6928145 := bstep (se 2 (by rfl) ⟨2598054, by rfl⟩ : syracuseStep 6928145 = 5196109) B5196109
theorem B4618763 : Blo 2051435 4618763 := bstep (se 1 (by rfl) ⟨3464072, by rfl⟩ : syracuseStep 4618763 = 6928145) B6928145
theorem B3079175 : Blo 2051435 3079175 := bstep (se 1 (by rfl) ⟨2309381, by rfl⟩ : syracuseStep 3079175 = 4618763) B4618763
theorem B2052783 : Blo 2051435 2052783 := bstep (se 1 (by rfl) ⟨1539587, by rfl⟩ : syracuseStep 2052783 = 3079175) B3079175
theorem B3079181 : Blo 2051435 3079181 := bbase (se 3 (by rfl) ⟨577346, by rfl⟩ : syracuseStep 3079181 = 1154693) (by norm_num)
theorem B2052787 : Blo 2051435 2052787 := bstep (se 1 (by rfl) ⟨1539590, by rfl⟩ : syracuseStep 2052787 = 3079181) B3079181
theorem B4618781 : Blo 2051435 4618781 := bbase (se 3 (by rfl) ⟨866021, by rfl⟩ : syracuseStep 4618781 = 1732043) (by norm_num)
theorem B3079187 : Blo 2051435 3079187 := bstep (se 1 (by rfl) ⟨2309390, by rfl⟩ : syracuseStep 3079187 = 4618781) B4618781
theorem B2052791 : Blo 2051435 2052791 := bstep (se 1 (by rfl) ⟨1539593, by rfl⟩ : syracuseStep 2052791 = 3079187) B3079187
theorem B3464093 : Blo 2051435 3464093 := bbase (se 3 (by rfl) ⟨649517, by rfl⟩ : syracuseStep 3464093 = 1299035) (by norm_num)
theorem B2309395 : Blo 2051435 2309395 := bstep (se 1 (by rfl) ⟨1732046, by rfl⟩ : syracuseStep 2309395 = 3464093) B3464093
theorem B3079193 : Blo 2051435 3079193 := bstep (se 2 (by rfl) ⟨1154697, by rfl⟩ : syracuseStep 3079193 = 2309395) B2309395
theorem B2052795 : Blo 2051435 2052795 := bstep (se 1 (by rfl) ⟨1539596, by rfl⟩ : syracuseStep 2052795 = 3079193) B3079193
theorem B5267045 : Blo 2051435 5267045 := bbase (se 4 (by rfl) ⟨493785, by rfl⟩ : syracuseStep 5267045 = 987571) (by norm_num)
theorem B3511363 : Blo 2051435 3511363 := bstep (se 1 (by rfl) ⟨2633522, by rfl⟩ : syracuseStep 3511363 = 5267045) B5267045
theorem B4681817 : Blo 2051435 4681817 := bstep (se 2 (by rfl) ⟨1755681, by rfl⟩ : syracuseStep 4681817 = 3511363) B3511363
theorem B3121211 : Blo 2051435 3121211 := bstep (se 1 (by rfl) ⟨2340908, by rfl⟩ : syracuseStep 3121211 = 4681817) B4681817
theorem B8323229 : Blo 2051435 8323229 := bstep (se 3 (by rfl) ⟨1560605, by rfl⟩ : syracuseStep 8323229 = 3121211) B3121211
theorem B5548819 : Blo 2051435 5548819 := bstep (se 1 (by rfl) ⟨4161614, by rfl⟩ : syracuseStep 5548819 = 8323229) B8323229
theorem B7398425 : Blo 2051435 7398425 := bstep (se 2 (by rfl) ⟨2774409, by rfl⟩ : syracuseStep 7398425 = 5548819) B5548819
theorem B19729133 : Blo 2051435 19729133 := bstep (se 3 (by rfl) ⟨3699212, by rfl⟩ : syracuseStep 19729133 = 7398425) B7398425
theorem B13152755 : Blo 2051435 13152755 := bstep (se 1 (by rfl) ⟨9864566, by rfl⟩ : syracuseStep 13152755 = 19729133) B19729133
theorem B8768503 : Blo 2051435 8768503 := bstep (se 1 (by rfl) ⟨6576377, by rfl⟩ : syracuseStep 8768503 = 13152755) B13152755
theorem B11691337 : Blo 2051435 11691337 := bstep (se 2 (by rfl) ⟨4384251, by rfl⟩ : syracuseStep 11691337 = 8768503) B8768503
theorem B15588449 : Blo 2051435 15588449 := bstep (se 2 (by rfl) ⟨5845668, by rfl⟩ : syracuseStep 15588449 = 11691337) B11691337
theorem B10392299 : Blo 2051435 10392299 := bstep (se 1 (by rfl) ⟨7794224, by rfl⟩ : syracuseStep 10392299 = 15588449) B15588449
theorem B6928199 : Blo 2051435 6928199 := bstep (se 1 (by rfl) ⟨5196149, by rfl⟩ : syracuseStep 6928199 = 10392299) B10392299
theorem B4618799 : Blo 2051435 4618799 := bstep (se 1 (by rfl) ⟨3464099, by rfl⟩ : syracuseStep 4618799 = 6928199) B6928199
theorem B3079199 : Blo 2051435 3079199 := bstep (se 1 (by rfl) ⟨2309399, by rfl⟩ : syracuseStep 3079199 = 4618799) B4618799
theorem B2052799 : Blo 2051435 2052799 := bstep (se 1 (by rfl) ⟨1539599, by rfl⟩ : syracuseStep 2052799 = 3079199) B3079199
theorem B3079205 : Blo 2051435 3079205 := bbase (se 4 (by rfl) ⟨288675, by rfl⟩ : syracuseStep 3079205 = 577351) (by norm_num)
theorem B2052803 : Blo 2051435 2052803 := bstep (se 1 (by rfl) ⟨1539602, by rfl⟩ : syracuseStep 2052803 = 3079205) B3079205
theorem B2598085 : Blo 2051435 2598085 := bbase (se 4 (by rfl) ⟨243570, by rfl⟩ : syracuseStep 2598085 = 487141) (by norm_num)
theorem B3464113 : Blo 2051435 3464113 := bstep (se 2 (by rfl) ⟨1299042, by rfl⟩ : syracuseStep 3464113 = 2598085) B2598085
theorem B4618817 : Blo 2051435 4618817 := bstep (se 2 (by rfl) ⟨1732056, by rfl⟩ : syracuseStep 4618817 = 3464113) B3464113
theorem B3079211 : Blo 2051435 3079211 := bstep (se 1 (by rfl) ⟨2309408, by rfl⟩ : syracuseStep 3079211 = 4618817) B4618817
theorem B2052807 : Blo 2051435 2052807 := bstep (se 1 (by rfl) ⟨1539605, by rfl⟩ : syracuseStep 2052807 = 3079211) B3079211
theorem B2309413 : Blo 2051435 2309413 := bbase (se 4 (by rfl) ⟨216507, by rfl⟩ : syracuseStep 2309413 = 433015) (by norm_num)
theorem B3079217 : Blo 2051435 3079217 := bstep (se 2 (by rfl) ⟨1154706, by rfl⟩ : syracuseStep 3079217 = 2309413) B2309413
theorem B2052811 : Blo 2051435 2052811 := bstep (se 1 (by rfl) ⟨1539608, by rfl⟩ : syracuseStep 2052811 = 3079217) B3079217
theorem B7398485 : Blo 2051435 7398485 := bbase (se 8 (by rfl) ⟨43350, by rfl⟩ : syracuseStep 7398485 = 86701) (by norm_num)
theorem B4932323 : Blo 2051435 4932323 := bstep (se 1 (by rfl) ⟨3699242, by rfl⟩ : syracuseStep 4932323 = 7398485) B7398485
theorem B3288215 : Blo 2051435 3288215 := bstep (se 1 (by rfl) ⟨2466161, by rfl⟩ : syracuseStep 3288215 = 4932323) B4932323
theorem B8768573 : Blo 2051435 8768573 := bstep (se 3 (by rfl) ⟨1644107, by rfl⟩ : syracuseStep 8768573 = 3288215) B3288215
theorem B5845715 : Blo 2051435 5845715 := bstep (se 1 (by rfl) ⟨4384286, by rfl⟩ : syracuseStep 5845715 = 8768573) B8768573
theorem B3897143 : Blo 2051435 3897143 := bstep (se 1 (by rfl) ⟨2922857, by rfl⟩ : syracuseStep 3897143 = 5845715) B5845715
theorem B2598095 : Blo 2051435 2598095 := bstep (se 1 (by rfl) ⟨1948571, by rfl⟩ : syracuseStep 2598095 = 3897143) B3897143
theorem B6928253 : Blo 2051435 6928253 := bstep (se 3 (by rfl) ⟨1299047, by rfl⟩ : syracuseStep 6928253 = 2598095) B2598095
theorem B4618835 : Blo 2051435 4618835 := bstep (se 1 (by rfl) ⟨3464126, by rfl⟩ : syracuseStep 4618835 = 6928253) B6928253
theorem B3079223 : Blo 2051435 3079223 := bstep (se 1 (by rfl) ⟨2309417, by rfl⟩ : syracuseStep 3079223 = 4618835) B4618835
theorem B2052815 : Blo 2051435 2052815 := bstep (se 1 (by rfl) ⟨1539611, by rfl⟩ : syracuseStep 2052815 = 3079223) B3079223
theorem B3079229 : Blo 2051435 3079229 := bbase (se 3 (by rfl) ⟨577355, by rfl⟩ : syracuseStep 3079229 = 1154711) (by norm_num)
theorem B2052819 : Blo 2051435 2052819 := bstep (se 1 (by rfl) ⟨1539614, by rfl⟩ : syracuseStep 2052819 = 3079229) B3079229
theorem B4618853 : Blo 2051435 4618853 := bbase (se 4 (by rfl) ⟨433017, by rfl⟩ : syracuseStep 4618853 = 866035) (by norm_num)
theorem B3079235 : Blo 2051435 3079235 := bstep (se 1 (by rfl) ⟨2309426, by rfl⟩ : syracuseStep 3079235 = 4618853) B4618853
theorem B2052823 : Blo 2051435 2052823 := bstep (se 1 (by rfl) ⟨1539617, by rfl⟩ : syracuseStep 2052823 = 3079235) B3079235
theorem B5196221 : Blo 2051435 5196221 := bbase (se 3 (by rfl) ⟨974291, by rfl⟩ : syracuseStep 5196221 = 1948583) (by norm_num)
theorem B3464147 : Blo 2051435 3464147 := bstep (se 1 (by rfl) ⟨2598110, by rfl⟩ : syracuseStep 3464147 = 5196221) B5196221
theorem B2309431 : Blo 2051435 2309431 := bstep (se 1 (by rfl) ⟨1732073, by rfl⟩ : syracuseStep 2309431 = 3464147) B3464147
theorem B3079241 : Blo 2051435 3079241 := bstep (se 2 (by rfl) ⟨1154715, by rfl⟩ : syracuseStep 3079241 = 2309431) B2309431
theorem B2052827 : Blo 2051435 2052827 := bstep (se 1 (by rfl) ⟨1539620, by rfl⟩ : syracuseStep 2052827 = 3079241) B3079241
theorem B3897173 : Blo 2051435 3897173 := bbase (se 9 (by rfl) ⟨11417, by rfl⟩ : syracuseStep 3897173 = 22835) (by norm_num)
theorem B10392461 : Blo 2051435 10392461 := bstep (se 3 (by rfl) ⟨1948586, by rfl⟩ : syracuseStep 10392461 = 3897173) B3897173
theorem B6928307 : Blo 2051435 6928307 := bstep (se 1 (by rfl) ⟨5196230, by rfl⟩ : syracuseStep 6928307 = 10392461) B10392461
theorem B4618871 : Blo 2051435 4618871 := bstep (se 1 (by rfl) ⟨3464153, by rfl⟩ : syracuseStep 4618871 = 6928307) B6928307
theorem B3079247 : Blo 2051435 3079247 := bstep (se 1 (by rfl) ⟨2309435, by rfl⟩ : syracuseStep 3079247 = 4618871) B4618871
theorem B2052831 : Blo 2051435 2052831 := bstep (se 1 (by rfl) ⟨1539623, by rfl⟩ : syracuseStep 2052831 = 3079247) B3079247
theorem B3079253 : Blo 2051435 3079253 := bbase (se 8 (by rfl) ⟨18042, by rfl⟩ : syracuseStep 3079253 = 36085) (by norm_num)
theorem B2052835 : Blo 2051435 2052835 := bstep (se 1 (by rfl) ⟨1539626, by rfl⟩ : syracuseStep 2052835 = 3079253) B3079253
theorem B13153013 : Blo 2051435 13153013 := bbase (se 5 (by rfl) ⟨616547, by rfl⟩ : syracuseStep 13153013 = 1233095) (by norm_num)
theorem B8768675 : Blo 2051435 8768675 := bstep (se 1 (by rfl) ⟨6576506, by rfl⟩ : syracuseStep 8768675 = 13153013) B13153013
theorem B5845783 : Blo 2051435 5845783 := bstep (se 1 (by rfl) ⟨4384337, by rfl⟩ : syracuseStep 5845783 = 8768675) B8768675
theorem B7794377 : Blo 2051435 7794377 := bstep (se 2 (by rfl) ⟨2922891, by rfl⟩ : syracuseStep 7794377 = 5845783) B5845783
theorem B5196251 : Blo 2051435 5196251 := bstep (se 1 (by rfl) ⟨3897188, by rfl⟩ : syracuseStep 5196251 = 7794377) B7794377
theorem B3464167 : Blo 2051435 3464167 := bstep (se 1 (by rfl) ⟨2598125, by rfl⟩ : syracuseStep 3464167 = 5196251) B5196251
theorem B4618889 : Blo 2051435 4618889 := bstep (se 2 (by rfl) ⟨1732083, by rfl⟩ : syracuseStep 4618889 = 3464167) B3464167
theorem B3079259 : Blo 2051435 3079259 := bstep (se 1 (by rfl) ⟨2309444, by rfl⟩ : syracuseStep 3079259 = 4618889) B4618889
theorem B2052839 : Blo 2051435 2052839 := bstep (se 1 (by rfl) ⟨1539629, by rfl⟩ : syracuseStep 2052839 = 3079259) B3079259
theorem B2309449 : Blo 2051435 2309449 := bbase (se 2 (by rfl) ⟨866043, by rfl⟩ : syracuseStep 2309449 = 1732087) (by norm_num)
theorem B3079265 : Blo 2051435 3079265 := bstep (se 2 (by rfl) ⟨1154724, by rfl⟩ : syracuseStep 3079265 = 2309449) B2309449
theorem B2052843 : Blo 2051435 2052843 := bstep (se 1 (by rfl) ⟨1539632, by rfl⟩ : syracuseStep 2052843 = 3079265) B3079265
theorem B4218493 : Blo 2051435 4218493 := bbase (se 3 (by rfl) ⟨790967, by rfl⟩ : syracuseStep 4218493 = 1581935) (by norm_num)
theorem B5624657 : Blo 2051435 5624657 := bstep (se 2 (by rfl) ⟨2109246, by rfl⟩ : syracuseStep 5624657 = 4218493) B4218493
theorem B3749771 : Blo 2051435 3749771 := bstep (se 1 (by rfl) ⟨2812328, by rfl⟩ : syracuseStep 3749771 = 5624657) B5624657
theorem B9999389 : Blo 2051435 9999389 := bstep (se 3 (by rfl) ⟨1874885, by rfl⟩ : syracuseStep 9999389 = 3749771) B3749771
theorem B6666259 : Blo 2051435 6666259 := bstep (se 1 (by rfl) ⟨4999694, by rfl⟩ : syracuseStep 6666259 = 9999389) B9999389
theorem B8888345 : Blo 2051435 8888345 := bstep (se 2 (by rfl) ⟨3333129, by rfl⟩ : syracuseStep 8888345 = 6666259) B6666259
theorem B5925563 : Blo 2051435 5925563 := bstep (se 1 (by rfl) ⟨4444172, by rfl⟩ : syracuseStep 5925563 = 8888345) B8888345
theorem B3950375 : Blo 2051435 3950375 := bstep (se 1 (by rfl) ⟨2962781, by rfl⟩ : syracuseStep 3950375 = 5925563) B5925563
theorem B42137333 : Blo 2051435 42137333 := bstep (se 5 (by rfl) ⟨1975187, by rfl⟩ : syracuseStep 42137333 = 3950375) B3950375
theorem B28091555 : Blo 2051435 28091555 := bstep (se 1 (by rfl) ⟨21068666, by rfl⟩ : syracuseStep 28091555 = 42137333) B42137333
theorem B18727703 : Blo 2051435 18727703 := bstep (se 1 (by rfl) ⟨14045777, by rfl⟩ : syracuseStep 18727703 = 28091555) B28091555
theorem B12485135 : Blo 2051435 12485135 := bstep (se 1 (by rfl) ⟨9363851, by rfl⟩ : syracuseStep 12485135 = 18727703) B18727703
theorem B33293693 : Blo 2051435 33293693 := bstep (se 3 (by rfl) ⟨6242567, by rfl⟩ : syracuseStep 33293693 = 12485135) B12485135
theorem B22195795 : Blo 2051435 22195795 := bstep (se 1 (by rfl) ⟨16646846, by rfl⟩ : syracuseStep 22195795 = 33293693) B33293693
theorem B29594393 : Blo 2051435 29594393 := bstep (se 2 (by rfl) ⟨11097897, by rfl⟩ : syracuseStep 29594393 = 22195795) B22195795
theorem B19729595 : Blo 2051435 19729595 := bstep (se 1 (by rfl) ⟨14797196, by rfl⟩ : syracuseStep 19729595 = 29594393) B29594393
theorem B13153063 : Blo 2051435 13153063 := bstep (se 1 (by rfl) ⟨9864797, by rfl⟩ : syracuseStep 13153063 = 19729595) B19729595
theorem B17537417 : Blo 2051435 17537417 := bstep (se 2 (by rfl) ⟨6576531, by rfl⟩ : syracuseStep 17537417 = 13153063) B13153063
theorem B11691611 : Blo 2051435 11691611 := bstep (se 1 (by rfl) ⟨8768708, by rfl⟩ : syracuseStep 11691611 = 17537417) B17537417
theorem B7794407 : Blo 2051435 7794407 := bstep (se 1 (by rfl) ⟨5845805, by rfl⟩ : syracuseStep 7794407 = 11691611) B11691611
theorem B5196271 : Blo 2051435 5196271 := bstep (se 1 (by rfl) ⟨3897203, by rfl⟩ : syracuseStep 5196271 = 7794407) B7794407
theorem B6928361 : Blo 2051435 6928361 := bstep (se 2 (by rfl) ⟨2598135, by rfl⟩ : syracuseStep 6928361 = 5196271) B5196271
theorem B4618907 : Blo 2051435 4618907 := bstep (se 1 (by rfl) ⟨3464180, by rfl⟩ : syracuseStep 4618907 = 6928361) B6928361
theorem B3079271 : Blo 2051435 3079271 := bstep (se 1 (by rfl) ⟨2309453, by rfl⟩ : syracuseStep 3079271 = 4618907) B4618907
theorem B2052847 : Blo 2051435 2052847 := bstep (se 1 (by rfl) ⟨1539635, by rfl⟩ : syracuseStep 2052847 = 3079271) B3079271
theorem B3079277 : Blo 2051435 3079277 := bbase (se 3 (by rfl) ⟨577364, by rfl⟩ : syracuseStep 3079277 = 1154729) (by norm_num)
theorem B2052851 : Blo 2051435 2052851 := bstep (se 1 (by rfl) ⟨1539638, by rfl⟩ : syracuseStep 2052851 = 3079277) B3079277
theorem B4618925 : Blo 2051435 4618925 := bbase (se 3 (by rfl) ⟨866048, by rfl⟩ : syracuseStep 4618925 = 1732097) (by norm_num)
theorem B3079283 : Blo 2051435 3079283 := bstep (se 1 (by rfl) ⟨2309462, by rfl⟩ : syracuseStep 3079283 = 4618925) B4618925
theorem B2052855 : Blo 2051435 2052855 := bstep (se 1 (by rfl) ⟨1539641, by rfl⟩ : syracuseStep 2052855 = 3079283) B3079283
theorem B4384381 : Blo 2051435 4384381 := bbase (se 3 (by rfl) ⟨822071, by rfl⟩ : syracuseStep 4384381 = 1644143) (by norm_num)
theorem B5845841 : Blo 2051435 5845841 := bstep (se 2 (by rfl) ⟨2192190, by rfl⟩ : syracuseStep 5845841 = 4384381) B4384381
theorem B3897227 : Blo 2051435 3897227 := bstep (se 1 (by rfl) ⟨2922920, by rfl⟩ : syracuseStep 3897227 = 5845841) B5845841
theorem B2598151 : Blo 2051435 2598151 := bstep (se 1 (by rfl) ⟨1948613, by rfl⟩ : syracuseStep 2598151 = 3897227) B3897227
theorem B3464201 : Blo 2051435 3464201 := bstep (se 2 (by rfl) ⟨1299075, by rfl⟩ : syracuseStep 3464201 = 2598151) B2598151
theorem B2309467 : Blo 2051435 2309467 := bstep (se 1 (by rfl) ⟨1732100, by rfl⟩ : syracuseStep 2309467 = 3464201) B3464201
theorem B3079289 : Blo 2051435 3079289 := bstep (se 2 (by rfl) ⟨1154733, by rfl⟩ : syracuseStep 3079289 = 2309467) B2309467
theorem B2052859 : Blo 2051435 2052859 := bstep (se 1 (by rfl) ⟨1539644, by rfl⟩ : syracuseStep 2052859 = 3079289) B3079289
theorem B26665237 : Blo 2051435 26665237 := bbase (se 6 (by rfl) ⟨624966, by rfl⟩ : syracuseStep 26665237 = 1249933) (by norm_num)
theorem B35553649 : Blo 2051435 35553649 := bstep (se 2 (by rfl) ⟨13332618, by rfl⟩ : syracuseStep 35553649 = 26665237) B26665237
theorem B47404865 : Blo 2051435 47404865 := bstep (se 2 (by rfl) ⟨17776824, by rfl⟩ : syracuseStep 47404865 = 35553649) B35553649
theorem B126412973 : Blo 2051435 126412973 := bstep (se 3 (by rfl) ⟨23702432, by rfl⟩ : syracuseStep 126412973 = 47404865) B47404865
theorem B84275315 : Blo 2051435 84275315 := bstep (se 1 (by rfl) ⟨63206486, by rfl⟩ : syracuseStep 84275315 = 126412973) B126412973
theorem B56183543 : Blo 2051435 56183543 := bstep (se 1 (by rfl) ⟨42137657, by rfl⟩ : syracuseStep 56183543 = 84275315) B84275315
theorem B37455695 : Blo 2051435 37455695 := bstep (se 1 (by rfl) ⟨28091771, by rfl⟩ : syracuseStep 37455695 = 56183543) B56183543
theorem B24970463 : Blo 2051435 24970463 := bstep (se 1 (by rfl) ⟨18727847, by rfl⟩ : syracuseStep 24970463 = 37455695) B37455695
theorem B16646975 : Blo 2051435 16646975 := bstep (se 1 (by rfl) ⟨12485231, by rfl⟩ : syracuseStep 16646975 = 24970463) B24970463
theorem B11097983 : Blo 2051435 11097983 := bstep (se 1 (by rfl) ⟨8323487, by rfl⟩ : syracuseStep 11097983 = 16646975) B16646975
theorem B29594621 : Blo 2051435 29594621 := bstep (se 3 (by rfl) ⟨5548991, by rfl⟩ : syracuseStep 29594621 = 11097983) B11097983
theorem B19729747 : Blo 2051435 19729747 := bstep (se 1 (by rfl) ⟨14797310, by rfl⟩ : syracuseStep 19729747 = 29594621) B29594621
theorem B26306329 : Blo 2051435 26306329 := bstep (se 2 (by rfl) ⟨9864873, by rfl⟩ : syracuseStep 26306329 = 19729747) B19729747
theorem B35075105 : Blo 2051435 35075105 := bstep (se 2 (by rfl) ⟨13153164, by rfl⟩ : syracuseStep 35075105 = 26306329) B26306329
theorem B23383403 : Blo 2051435 23383403 := bstep (se 1 (by rfl) ⟨17537552, by rfl⟩ : syracuseStep 23383403 = 35075105) B35075105
theorem B15588935 : Blo 2051435 15588935 := bstep (se 1 (by rfl) ⟨11691701, by rfl⟩ : syracuseStep 15588935 = 23383403) B23383403
theorem B10392623 : Blo 2051435 10392623 := bstep (se 1 (by rfl) ⟨7794467, by rfl⟩ : syracuseStep 10392623 = 15588935) B15588935
theorem B6928415 : Blo 2051435 6928415 := bstep (se 1 (by rfl) ⟨5196311, by rfl⟩ : syracuseStep 6928415 = 10392623) B10392623
theorem B4618943 : Blo 2051435 4618943 := bstep (se 1 (by rfl) ⟨3464207, by rfl⟩ : syracuseStep 4618943 = 6928415) B6928415
theorem B3079295 : Blo 2051435 3079295 := bstep (se 1 (by rfl) ⟨2309471, by rfl⟩ : syracuseStep 3079295 = 4618943) B4618943
theorem B2052863 : Blo 2051435 2052863 := bstep (se 1 (by rfl) ⟨1539647, by rfl⟩ : syracuseStep 2052863 = 3079295) B3079295
theorem B3079301 : Blo 2051435 3079301 := bbase (se 4 (by rfl) ⟨288684, by rfl⟩ : syracuseStep 3079301 = 577369) (by norm_num)
theorem B2052867 : Blo 2051435 2052867 := bstep (se 1 (by rfl) ⟨1539650, by rfl⟩ : syracuseStep 2052867 = 3079301) B3079301
theorem B3464221 : Blo 2051435 3464221 := bbase (se 3 (by rfl) ⟨649541, by rfl⟩ : syracuseStep 3464221 = 1299083) (by norm_num)
theorem B4618961 : Blo 2051435 4618961 := bstep (se 2 (by rfl) ⟨1732110, by rfl⟩ : syracuseStep 4618961 = 3464221) B3464221
theorem B3079307 : Blo 2051435 3079307 := bstep (se 1 (by rfl) ⟨2309480, by rfl⟩ : syracuseStep 3079307 = 4618961) B4618961
theorem B2052871 : Blo 2051435 2052871 := bstep (se 1 (by rfl) ⟨1539653, by rfl⟩ : syracuseStep 2052871 = 3079307) B3079307
theorem B2309485 : Blo 2051435 2309485 := bbase (se 3 (by rfl) ⟨433028, by rfl⟩ : syracuseStep 2309485 = 866057) (by norm_num)
theorem B3079313 : Blo 2051435 3079313 := bstep (se 2 (by rfl) ⟨1154742, by rfl⟩ : syracuseStep 3079313 = 2309485) B2309485
theorem B2052875 : Blo 2051435 2052875 := bstep (se 1 (by rfl) ⟨1539656, by rfl⟩ : syracuseStep 2052875 = 3079313) B3079313
theorem B6928469 : Blo 2051435 6928469 := bbase (se 8 (by rfl) ⟨40596, by rfl⟩ : syracuseStep 6928469 = 81193) (by norm_num)
theorem B4618979 : Blo 2051435 4618979 := bstep (se 1 (by rfl) ⟨3464234, by rfl⟩ : syracuseStep 4618979 = 6928469) B6928469
theorem B3079319 : Blo 2051435 3079319 := bstep (se 1 (by rfl) ⟨2309489, by rfl⟩ : syracuseStep 3079319 = 4618979) B4618979
theorem B2052879 : Blo 2051435 2052879 := bstep (se 1 (by rfl) ⟨1539659, by rfl⟩ : syracuseStep 2052879 = 3079319) B3079319
theorem B3079325 : Blo 2051435 3079325 := bbase (se 3 (by rfl) ⟨577373, by rfl⟩ : syracuseStep 3079325 = 1154747) (by norm_num)
theorem B2052883 : Blo 2051435 2052883 := bstep (se 1 (by rfl) ⟨1539662, by rfl⟩ : syracuseStep 2052883 = 3079325) B3079325
theorem B4618997 : Blo 2051435 4618997 := bbase (se 5 (by rfl) ⟨216515, by rfl⟩ : syracuseStep 4618997 = 433031) (by norm_num)
theorem B3079331 : Blo 2051435 3079331 := bstep (se 1 (by rfl) ⟨2309498, by rfl⟩ : syracuseStep 3079331 = 4618997) B4618997
theorem B2052887 : Blo 2051435 2052887 := bstep (se 1 (by rfl) ⟨1539665, by rfl⟩ : syracuseStep 2052887 = 3079331) B3079331
theorem B2080901 : Blo 2051435 2080901 := bbase (se 4 (by rfl) ⟨195084, by rfl⟩ : syracuseStep 2080901 = 390169) (by norm_num)
theorem B5549069 : Blo 2051435 5549069 := bstep (se 3 (by rfl) ⟨1040450, by rfl⟩ : syracuseStep 5549069 = 2080901) B2080901
theorem B3699379 : Blo 2051435 3699379 := bstep (se 1 (by rfl) ⟨2774534, by rfl⟩ : syracuseStep 3699379 = 5549069) B5549069
theorem B4932505 : Blo 2051435 4932505 := bstep (se 2 (by rfl) ⟨1849689, by rfl⟩ : syracuseStep 4932505 = 3699379) B3699379
theorem B26306693 : Blo 2051435 26306693 := bstep (se 4 (by rfl) ⟨2466252, by rfl⟩ : syracuseStep 26306693 = 4932505) B4932505
theorem B17537795 : Blo 2051435 17537795 := bstep (se 1 (by rfl) ⟨13153346, by rfl⟩ : syracuseStep 17537795 = 26306693) B26306693
theorem B11691863 : Blo 2051435 11691863 := bstep (se 1 (by rfl) ⟨8768897, by rfl⟩ : syracuseStep 11691863 = 17537795) B17537795
theorem B7794575 : Blo 2051435 7794575 := bstep (se 1 (by rfl) ⟨5845931, by rfl⟩ : syracuseStep 7794575 = 11691863) B11691863
theorem B5196383 : Blo 2051435 5196383 := bstep (se 1 (by rfl) ⟨3897287, by rfl⟩ : syracuseStep 5196383 = 7794575) B7794575
theorem B3464255 : Blo 2051435 3464255 := bstep (se 1 (by rfl) ⟨2598191, by rfl⟩ : syracuseStep 3464255 = 5196383) B5196383
theorem B2309503 : Blo 2051435 2309503 := bstep (se 1 (by rfl) ⟨1732127, by rfl⟩ : syracuseStep 2309503 = 3464255) B3464255
theorem B3079337 : Blo 2051435 3079337 := bstep (se 2 (by rfl) ⟨1154751, by rfl⟩ : syracuseStep 3079337 = 2309503) B2309503
theorem B2052891 : Blo 2051435 2052891 := bstep (se 1 (by rfl) ⟨1539668, by rfl⟩ : syracuseStep 2052891 = 3079337) B3079337
theorem B7398773 : Blo 2051435 7398773 := bbase (se 5 (by rfl) ⟨346817, by rfl⟩ : syracuseStep 7398773 = 693635) (by norm_num)
theorem B4932515 : Blo 2051435 4932515 := bstep (se 1 (by rfl) ⟨3699386, by rfl⟩ : syracuseStep 4932515 = 7398773) B7398773
theorem B3288343 : Blo 2051435 3288343 := bstep (se 1 (by rfl) ⟨2466257, by rfl⟩ : syracuseStep 3288343 = 4932515) B4932515
theorem B4384457 : Blo 2051435 4384457 := bstep (se 2 (by rfl) ⟨1644171, by rfl⟩ : syracuseStep 4384457 = 3288343) B3288343
theorem B2922971 : Blo 2051435 2922971 := bstep (se 1 (by rfl) ⟨2192228, by rfl⟩ : syracuseStep 2922971 = 4384457) B4384457
theorem B7794589 : Blo 2051435 7794589 := bstep (se 3 (by rfl) ⟨1461485, by rfl⟩ : syracuseStep 7794589 = 2922971) B2922971
theorem B10392785 : Blo 2051435 10392785 := bstep (se 2 (by rfl) ⟨3897294, by rfl⟩ : syracuseStep 10392785 = 7794589) B7794589
theorem B6928523 : Blo 2051435 6928523 := bstep (se 1 (by rfl) ⟨5196392, by rfl⟩ : syracuseStep 6928523 = 10392785) B10392785
theorem B4619015 : Blo 2051435 4619015 := bstep (se 1 (by rfl) ⟨3464261, by rfl⟩ : syracuseStep 4619015 = 6928523) B6928523
theorem B3079343 : Blo 2051435 3079343 := bstep (se 1 (by rfl) ⟨2309507, by rfl⟩ : syracuseStep 3079343 = 4619015) B4619015
theorem B2052895 : Blo 2051435 2052895 := bstep (se 1 (by rfl) ⟨1539671, by rfl⟩ : syracuseStep 2052895 = 3079343) B3079343
theorem B3079349 : Blo 2051435 3079349 := bbase (se 5 (by rfl) ⟨144344, by rfl⟩ : syracuseStep 3079349 = 288689) (by norm_num)
theorem B2052899 : Blo 2051435 2052899 := bstep (se 1 (by rfl) ⟨1539674, by rfl⟩ : syracuseStep 2052899 = 3079349) B3079349
theorem B5196413 : Blo 2051435 5196413 := bbase (se 3 (by rfl) ⟨974327, by rfl⟩ : syracuseStep 5196413 = 1948655) (by norm_num)
theorem B3464275 : Blo 2051435 3464275 := bstep (se 1 (by rfl) ⟨2598206, by rfl⟩ : syracuseStep 3464275 = 5196413) B5196413
theorem B4619033 : Blo 2051435 4619033 := bstep (se 2 (by rfl) ⟨1732137, by rfl⟩ : syracuseStep 4619033 = 3464275) B3464275
theorem B3079355 : Blo 2051435 3079355 := bstep (se 1 (by rfl) ⟨2309516, by rfl⟩ : syracuseStep 3079355 = 4619033) B4619033
theorem B2052903 : Blo 2051435 2052903 := bstep (se 1 (by rfl) ⟨1539677, by rfl⟩ : syracuseStep 2052903 = 3079355) B3079355
theorem B2309521 : Blo 2051435 2309521 := bbase (se 2 (by rfl) ⟨866070, by rfl⟩ : syracuseStep 2309521 = 1732141) (by norm_num)
theorem B3079361 : Blo 2051435 3079361 := bstep (se 2 (by rfl) ⟨1154760, by rfl⟩ : syracuseStep 3079361 = 2309521) B2309521
theorem B2052907 : Blo 2051435 2052907 := bstep (se 1 (by rfl) ⟨1539680, by rfl⟩ : syracuseStep 2052907 = 3079361) B3079361
theorem B3897325 : Blo 2051435 3897325 := bbase (se 3 (by rfl) ⟨730748, by rfl⟩ : syracuseStep 3897325 = 1461497) (by norm_num)
theorem B5196433 : Blo 2051435 5196433 := bstep (se 2 (by rfl) ⟨1948662, by rfl⟩ : syracuseStep 5196433 = 3897325) B3897325
theorem B6928577 : Blo 2051435 6928577 := bstep (se 2 (by rfl) ⟨2598216, by rfl⟩ : syracuseStep 6928577 = 5196433) B5196433
theorem B4619051 : Blo 2051435 4619051 := bstep (se 1 (by rfl) ⟨3464288, by rfl⟩ : syracuseStep 4619051 = 6928577) B6928577
theorem B3079367 : Blo 2051435 3079367 := bstep (se 1 (by rfl) ⟨2309525, by rfl⟩ : syracuseStep 3079367 = 4619051) B4619051
theorem B2052911 : Blo 2051435 2052911 := bstep (se 1 (by rfl) ⟨1539683, by rfl⟩ : syracuseStep 2052911 = 3079367) B3079367
theorem B3079373 : Blo 2051435 3079373 := bbase (se 3 (by rfl) ⟨577382, by rfl⟩ : syracuseStep 3079373 = 1154765) (by norm_num)
theorem B2052915 : Blo 2051435 2052915 := bstep (se 1 (by rfl) ⟨1539686, by rfl⟩ : syracuseStep 2052915 = 3079373) B3079373
theorem B4619069 : Blo 2051435 4619069 := bbase (se 3 (by rfl) ⟨866075, by rfl⟩ : syracuseStep 4619069 = 1732151) (by norm_num)
theorem B3079379 : Blo 2051435 3079379 := bstep (se 1 (by rfl) ⟨2309534, by rfl⟩ : syracuseStep 3079379 = 4619069) B4619069
theorem B2052919 : Blo 2051435 2052919 := bstep (se 1 (by rfl) ⟨1539689, by rfl⟩ : syracuseStep 2052919 = 3079379) B3079379
theorem B3464309 : Blo 2051435 3464309 := bbase (se 5 (by rfl) ⟨162389, by rfl⟩ : syracuseStep 3464309 = 324779) (by norm_num)
theorem B2309539 : Blo 2051435 2309539 := bstep (se 1 (by rfl) ⟨1732154, by rfl⟩ : syracuseStep 2309539 = 3464309) B3464309
theorem B3079385 : Blo 2051435 3079385 := bstep (se 2 (by rfl) ⟨1154769, by rfl⟩ : syracuseStep 3079385 = 2309539) B2309539
theorem B2052923 : Blo 2051435 2052923 := bstep (se 1 (by rfl) ⟨1539692, by rfl⟩ : syracuseStep 2052923 = 3079385) B3079385
theorem B4384525 : Blo 2051435 4384525 := bbase (se 3 (by rfl) ⟨822098, by rfl⟩ : syracuseStep 4384525 = 1644197) (by norm_num)
theorem B5846033 : Blo 2051435 5846033 := bstep (se 2 (by rfl) ⟨2192262, by rfl⟩ : syracuseStep 5846033 = 4384525) B4384525
theorem B15589421 : Blo 2051435 15589421 := bstep (se 3 (by rfl) ⟨2923016, by rfl⟩ : syracuseStep 15589421 = 5846033) B5846033
theorem B10392947 : Blo 2051435 10392947 := bstep (se 1 (by rfl) ⟨7794710, by rfl⟩ : syracuseStep 10392947 = 15589421) B15589421
theorem B6928631 : Blo 2051435 6928631 := bstep (se 1 (by rfl) ⟨5196473, by rfl⟩ : syracuseStep 6928631 = 10392947) B10392947
theorem B4619087 : Blo 2051435 4619087 := bstep (se 1 (by rfl) ⟨3464315, by rfl⟩ : syracuseStep 4619087 = 6928631) B6928631
theorem B3079391 : Blo 2051435 3079391 := bstep (se 1 (by rfl) ⟨2309543, by rfl⟩ : syracuseStep 3079391 = 4619087) B4619087
theorem B2052927 : Blo 2051435 2052927 := bstep (se 1 (by rfl) ⟨1539695, by rfl⟩ : syracuseStep 2052927 = 3079391) B3079391
theorem B3079397 : Blo 2051435 3079397 := bbase (se 4 (by rfl) ⟨288693, by rfl⟩ : syracuseStep 3079397 = 577387) (by norm_num)
theorem B2052931 : Blo 2051435 2052931 := bstep (se 1 (by rfl) ⟨1539698, by rfl⟩ : syracuseStep 2052931 = 3079397) B3079397
theorem B6242837 : Blo 2051435 6242837 := bbase (se 6 (by rfl) ⟨146316, by rfl⟩ : syracuseStep 6242837 = 292633) (by norm_num)
theorem B16647565 : Blo 2051435 16647565 := bstep (se 3 (by rfl) ⟨3121418, by rfl⟩ : syracuseStep 16647565 = 6242837) B6242837
theorem B22196753 : Blo 2051435 22196753 := bstep (se 2 (by rfl) ⟨8323782, by rfl⟩ : syracuseStep 22196753 = 16647565) B16647565
theorem B14797835 : Blo 2051435 14797835 := bstep (se 1 (by rfl) ⟨11098376, by rfl⟩ : syracuseStep 14797835 = 22196753) B22196753
theorem B9865223 : Blo 2051435 9865223 := bstep (se 1 (by rfl) ⟨7398917, by rfl⟩ : syracuseStep 9865223 = 14797835) B14797835
theorem B6576815 : Blo 2051435 6576815 := bstep (se 1 (by rfl) ⟨4932611, by rfl⟩ : syracuseStep 6576815 = 9865223) B9865223
theorem B4384543 : Blo 2051435 4384543 := bstep (se 1 (by rfl) ⟨3288407, by rfl⟩ : syracuseStep 4384543 = 6576815) B6576815
theorem B5846057 : Blo 2051435 5846057 := bstep (se 2 (by rfl) ⟨2192271, by rfl⟩ : syracuseStep 5846057 = 4384543) B4384543
theorem B3897371 : Blo 2051435 3897371 := bstep (se 1 (by rfl) ⟨2923028, by rfl⟩ : syracuseStep 3897371 = 5846057) B5846057
theorem B2598247 : Blo 2051435 2598247 := bstep (se 1 (by rfl) ⟨1948685, by rfl⟩ : syracuseStep 2598247 = 3897371) B3897371
theorem B3464329 : Blo 2051435 3464329 := bstep (se 2 (by rfl) ⟨1299123, by rfl⟩ : syracuseStep 3464329 = 2598247) B2598247
theorem B4619105 : Blo 2051435 4619105 := bstep (se 2 (by rfl) ⟨1732164, by rfl⟩ : syracuseStep 4619105 = 3464329) B3464329
theorem B3079403 : Blo 2051435 3079403 := bstep (se 1 (by rfl) ⟨2309552, by rfl⟩ : syracuseStep 3079403 = 4619105) B4619105
theorem B2052935 : Blo 2051435 2052935 := bstep (se 1 (by rfl) ⟨1539701, by rfl⟩ : syracuseStep 2052935 = 3079403) B3079403
theorem B2309557 : Blo 2051435 2309557 := bbase (se 5 (by rfl) ⟨108260, by rfl⟩ : syracuseStep 2309557 = 216521) (by norm_num)
theorem B3079409 : Blo 2051435 3079409 := bstep (se 2 (by rfl) ⟨1154778, by rfl⟩ : syracuseStep 3079409 = 2309557) B2309557
theorem B2052939 : Blo 2051435 2052939 := bstep (se 1 (by rfl) ⟨1539704, by rfl⟩ : syracuseStep 2052939 = 3079409) B3079409
theorem B2598257 : Blo 2051435 2598257 := bbase (se 2 (by rfl) ⟨974346, by rfl⟩ : syracuseStep 2598257 = 1948693) (by norm_num)
theorem B6928685 : Blo 2051435 6928685 := bstep (se 3 (by rfl) ⟨1299128, by rfl⟩ : syracuseStep 6928685 = 2598257) B2598257
theorem B4619123 : Blo 2051435 4619123 := bstep (se 1 (by rfl) ⟨3464342, by rfl⟩ : syracuseStep 4619123 = 6928685) B6928685
theorem B3079415 : Blo 2051435 3079415 := bstep (se 1 (by rfl) ⟨2309561, by rfl⟩ : syracuseStep 3079415 = 4619123) B4619123
theorem B2052943 : Blo 2051435 2052943 := bstep (se 1 (by rfl) ⟨1539707, by rfl⟩ : syracuseStep 2052943 = 3079415) B3079415
theorem B3079421 : Blo 2051435 3079421 := bbase (se 3 (by rfl) ⟨577391, by rfl⟩ : syracuseStep 3079421 = 1154783) (by norm_num)
theorem B2052947 : Blo 2051435 2052947 := bstep (se 1 (by rfl) ⟨1539710, by rfl⟩ : syracuseStep 2052947 = 3079421) B3079421
theorem B4619141 : Blo 2051435 4619141 := bbase (se 4 (by rfl) ⟨433044, by rfl⟩ : syracuseStep 4619141 = 866089) (by norm_num)
theorem B3079427 : Blo 2051435 3079427 := bstep (se 1 (by rfl) ⟨2309570, by rfl⟩ : syracuseStep 3079427 = 4619141) B4619141
theorem B2052951 : Blo 2051435 2052951 := bstep (se 1 (by rfl) ⟨1539713, by rfl⟩ : syracuseStep 2052951 = 3079427) B3079427
theorem B2192293 : Blo 2051435 2192293 := bbase (se 4 (by rfl) ⟨205527, by rfl⟩ : syracuseStep 2192293 = 411055) (by norm_num)
theorem B2923057 : Blo 2051435 2923057 := bstep (se 2 (by rfl) ⟨1096146, by rfl⟩ : syracuseStep 2923057 = 2192293) B2192293
theorem B3897409 : Blo 2051435 3897409 := bstep (se 2 (by rfl) ⟨1461528, by rfl⟩ : syracuseStep 3897409 = 2923057) B2923057
theorem B5196545 : Blo 2051435 5196545 := bstep (se 2 (by rfl) ⟨1948704, by rfl⟩ : syracuseStep 5196545 = 3897409) B3897409
theorem B3464363 : Blo 2051435 3464363 := bstep (se 1 (by rfl) ⟨2598272, by rfl⟩ : syracuseStep 3464363 = 5196545) B5196545
theorem B2309575 : Blo 2051435 2309575 := bstep (se 1 (by rfl) ⟨1732181, by rfl⟩ : syracuseStep 2309575 = 3464363) B3464363
theorem B3079433 : Blo 2051435 3079433 := bstep (se 2 (by rfl) ⟨1154787, by rfl⟩ : syracuseStep 3079433 = 2309575) B2309575
theorem B2052955 : Blo 2051435 2052955 := bstep (se 1 (by rfl) ⟨1539716, by rfl⟩ : syracuseStep 2052955 = 3079433) B3079433
theorem B10393109 : Blo 2051435 10393109 := bbase (se 6 (by rfl) ⟨243588, by rfl⟩ : syracuseStep 10393109 = 487177) (by norm_num)
theorem B6928739 : Blo 2051435 6928739 := bstep (se 1 (by rfl) ⟨5196554, by rfl⟩ : syracuseStep 6928739 = 10393109) B10393109
theorem B4619159 : Blo 2051435 4619159 := bstep (se 1 (by rfl) ⟨3464369, by rfl⟩ : syracuseStep 4619159 = 6928739) B6928739
theorem B3079439 : Blo 2051435 3079439 := bstep (se 1 (by rfl) ⟨2309579, by rfl⟩ : syracuseStep 3079439 = 4619159) B4619159
theorem B2052959 : Blo 2051435 2052959 := bstep (se 1 (by rfl) ⟨1539719, by rfl⟩ : syracuseStep 2052959 = 3079439) B3079439
theorem B3079445 : Blo 2051435 3079445 := bbase (se 6 (by rfl) ⟨72174, by rfl⟩ : syracuseStep 3079445 = 144349) (by norm_num)
theorem B2052963 : Blo 2051435 2052963 := bstep (se 1 (by rfl) ⟨1539722, by rfl⟩ : syracuseStep 2052963 = 3079445) B3079445
theorem B6242933 : Blo 2051435 6242933 := bbase (se 5 (by rfl) ⟨292637, by rfl⟩ : syracuseStep 6242933 = 585275) (by norm_num)
theorem B16647821 : Blo 2051435 16647821 := bstep (se 3 (by rfl) ⟨3121466, by rfl⟩ : syracuseStep 16647821 = 6242933) B6242933
theorem B11098547 : Blo 2051435 11098547 := bstep (se 1 (by rfl) ⟨8323910, by rfl⟩ : syracuseStep 11098547 = 16647821) B16647821
theorem B7399031 : Blo 2051435 7399031 := bstep (se 1 (by rfl) ⟨5549273, by rfl⟩ : syracuseStep 7399031 = 11098547) B11098547
theorem B19730749 : Blo 2051435 19730749 := bstep (se 3 (by rfl) ⟨3699515, by rfl⟩ : syracuseStep 19730749 = 7399031) B7399031
theorem B26307665 : Blo 2051435 26307665 := bstep (se 2 (by rfl) ⟨9865374, by rfl⟩ : syracuseStep 26307665 = 19730749) B19730749
theorem B17538443 : Blo 2051435 17538443 := bstep (se 1 (by rfl) ⟨13153832, by rfl⟩ : syracuseStep 17538443 = 26307665) B26307665
theorem B11692295 : Blo 2051435 11692295 := bstep (se 1 (by rfl) ⟨8769221, by rfl⟩ : syracuseStep 11692295 = 17538443) B17538443
theorem B7794863 : Blo 2051435 7794863 := bstep (se 1 (by rfl) ⟨5846147, by rfl⟩ : syracuseStep 7794863 = 11692295) B11692295
theorem B5196575 : Blo 2051435 5196575 := bstep (se 1 (by rfl) ⟨3897431, by rfl⟩ : syracuseStep 5196575 = 7794863) B7794863
theorem B3464383 : Blo 2051435 3464383 := bstep (se 1 (by rfl) ⟨2598287, by rfl⟩ : syracuseStep 3464383 = 5196575) B5196575
theorem B4619177 : Blo 2051435 4619177 := bstep (se 2 (by rfl) ⟨1732191, by rfl⟩ : syracuseStep 4619177 = 3464383) B3464383
theorem B3079451 : Blo 2051435 3079451 := bstep (se 1 (by rfl) ⟨2309588, by rfl⟩ : syracuseStep 3079451 = 4619177) B4619177
theorem B2052967 : Blo 2051435 2052967 := bstep (se 1 (by rfl) ⟨1539725, by rfl⟩ : syracuseStep 2052967 = 3079451) B3079451
theorem B2309593 : Blo 2051435 2309593 := bbase (se 2 (by rfl) ⟨866097, by rfl⟩ : syracuseStep 2309593 = 1732195) (by norm_num)
theorem B3079457 : Blo 2051435 3079457 := bstep (se 2 (by rfl) ⟨1154796, by rfl⟩ : syracuseStep 3079457 = 2309593) B2309593
theorem B2052971 : Blo 2051435 2052971 := bstep (se 1 (by rfl) ⟨1539728, by rfl⟩ : syracuseStep 2052971 = 3079457) B3079457
theorem B2923085 : Blo 2051435 2923085 := bbase (se 3 (by rfl) ⟨548078, by rfl⟩ : syracuseStep 2923085 = 1096157) (by norm_num)
theorem B7794893 : Blo 2051435 7794893 := bstep (se 3 (by rfl) ⟨1461542, by rfl⟩ : syracuseStep 7794893 = 2923085) B2923085
theorem B5196595 : Blo 2051435 5196595 := bstep (se 1 (by rfl) ⟨3897446, by rfl⟩ : syracuseStep 5196595 = 7794893) B7794893
theorem B6928793 : Blo 2051435 6928793 := bstep (se 2 (by rfl) ⟨2598297, by rfl⟩ : syracuseStep 6928793 = 5196595) B5196595
theorem B4619195 : Blo 2051435 4619195 := bstep (se 1 (by rfl) ⟨3464396, by rfl⟩ : syracuseStep 4619195 = 6928793) B6928793
theorem B3079463 : Blo 2051435 3079463 := bstep (se 1 (by rfl) ⟨2309597, by rfl⟩ : syracuseStep 3079463 = 4619195) B4619195
theorem B2052975 : Blo 2051435 2052975 := bstep (se 1 (by rfl) ⟨1539731, by rfl⟩ : syracuseStep 2052975 = 3079463) B3079463
theorem B3079469 : Blo 2051435 3079469 := bbase (se 3 (by rfl) ⟨577400, by rfl⟩ : syracuseStep 3079469 = 1154801) (by norm_num)
theorem B2052979 : Blo 2051435 2052979 := bstep (se 1 (by rfl) ⟨1539734, by rfl⟩ : syracuseStep 2052979 = 3079469) B3079469
theorem B4619213 : Blo 2051435 4619213 := bbase (se 3 (by rfl) ⟨866102, by rfl⟩ : syracuseStep 4619213 = 1732205) (by norm_num)
theorem B3079475 : Blo 2051435 3079475 := bstep (se 1 (by rfl) ⟨2309606, by rfl⟩ : syracuseStep 3079475 = 4619213) B4619213
theorem B2052983 : Blo 2051435 2052983 := bstep (se 1 (by rfl) ⟨1539737, by rfl⟩ : syracuseStep 2052983 = 3079475) B3079475
theorem B2598313 : Blo 2051435 2598313 := bbase (se 2 (by rfl) ⟨974367, by rfl⟩ : syracuseStep 2598313 = 1948735) (by norm_num)
theorem B3464417 : Blo 2051435 3464417 := bstep (se 2 (by rfl) ⟨1299156, by rfl⟩ : syracuseStep 3464417 = 2598313) B2598313
theorem B2309611 : Blo 2051435 2309611 := bstep (se 1 (by rfl) ⟨1732208, by rfl⟩ : syracuseStep 2309611 = 3464417) B3464417
theorem B3079481 : Blo 2051435 3079481 := bstep (se 2 (by rfl) ⟨1154805, by rfl⟩ : syracuseStep 3079481 = 2309611) B2309611
theorem B2052987 : Blo 2051435 2052987 := bstep (se 1 (by rfl) ⟨1539740, by rfl⟩ : syracuseStep 2052987 = 3079481) B3079481
theorem B2774669 : Blo 2051435 2774669 := bbase (se 3 (by rfl) ⟨520250, by rfl⟩ : syracuseStep 2774669 = 1040501) (by norm_num)
theorem B7399117 : Blo 2051435 7399117 := bstep (se 3 (by rfl) ⟨1387334, by rfl⟩ : syracuseStep 7399117 = 2774669) B2774669
theorem B9865489 : Blo 2051435 9865489 := bstep (se 2 (by rfl) ⟨3699558, by rfl⟩ : syracuseStep 9865489 = 7399117) B7399117
theorem B13153985 : Blo 2051435 13153985 := bstep (se 2 (by rfl) ⟨4932744, by rfl⟩ : syracuseStep 13153985 = 9865489) B9865489
theorem B8769323 : Blo 2051435 8769323 := bstep (se 1 (by rfl) ⟨6576992, by rfl⟩ : syracuseStep 8769323 = 13153985) B13153985
theorem B23384861 : Blo 2051435 23384861 := bstep (se 3 (by rfl) ⟨4384661, by rfl⟩ : syracuseStep 23384861 = 8769323) B8769323
theorem B15589907 : Blo 2051435 15589907 := bstep (se 1 (by rfl) ⟨11692430, by rfl⟩ : syracuseStep 15589907 = 23384861) B23384861
theorem B10393271 : Blo 2051435 10393271 := bstep (se 1 (by rfl) ⟨7794953, by rfl⟩ : syracuseStep 10393271 = 15589907) B15589907
theorem B6928847 : Blo 2051435 6928847 := bstep (se 1 (by rfl) ⟨5196635, by rfl⟩ : syracuseStep 6928847 = 10393271) B10393271
theorem B4619231 : Blo 2051435 4619231 := bstep (se 1 (by rfl) ⟨3464423, by rfl⟩ : syracuseStep 4619231 = 6928847) B6928847
theorem B3079487 : Blo 2051435 3079487 := bstep (se 1 (by rfl) ⟨2309615, by rfl⟩ : syracuseStep 3079487 = 4619231) B4619231
theorem B2052991 : Blo 2051435 2052991 := bstep (se 1 (by rfl) ⟨1539743, by rfl⟩ : syracuseStep 2052991 = 3079487) B3079487
theorem B3079493 : Blo 2051435 3079493 := bbase (se 4 (by rfl) ⟨288702, by rfl⟩ : syracuseStep 3079493 = 577405) (by norm_num)
theorem B2052995 : Blo 2051435 2052995 := bstep (se 1 (by rfl) ⟨1539746, by rfl⟩ : syracuseStep 2052995 = 3079493) B3079493
theorem B3464437 : Blo 2051435 3464437 := bbase (se 5 (by rfl) ⟨162395, by rfl⟩ : syracuseStep 3464437 = 324791) (by norm_num)
theorem B4619249 : Blo 2051435 4619249 := bstep (se 2 (by rfl) ⟨1732218, by rfl⟩ : syracuseStep 4619249 = 3464437) B3464437
theorem B3079499 : Blo 2051435 3079499 := bstep (se 1 (by rfl) ⟨2309624, by rfl⟩ : syracuseStep 3079499 = 4619249) B4619249
theorem B2052999 : Blo 2051435 2052999 := bstep (se 1 (by rfl) ⟨1539749, by rfl⟩ : syracuseStep 2052999 = 3079499) B3079499
theorem B2309629 : Blo 2051435 2309629 := bbase (se 3 (by rfl) ⟨433055, by rfl⟩ : syracuseStep 2309629 = 866111) (by norm_num)
theorem B3079505 : Blo 2051435 3079505 := bstep (se 2 (by rfl) ⟨1154814, by rfl⟩ : syracuseStep 3079505 = 2309629) B2309629
theorem B2053003 : Blo 2051435 2053003 := bstep (se 1 (by rfl) ⟨1539752, by rfl⟩ : syracuseStep 2053003 = 3079505) B3079505
theorem B6928901 : Blo 2051435 6928901 := bbase (se 4 (by rfl) ⟨649584, by rfl⟩ : syracuseStep 6928901 = 1299169) (by norm_num)
theorem B4619267 : Blo 2051435 4619267 := bstep (se 1 (by rfl) ⟨3464450, by rfl⟩ : syracuseStep 4619267 = 6928901) B6928901
theorem B3079511 : Blo 2051435 3079511 := bstep (se 1 (by rfl) ⟨2309633, by rfl⟩ : syracuseStep 3079511 = 4619267) B4619267
theorem B2053007 : Blo 2051435 2053007 := bstep (se 1 (by rfl) ⟨1539755, by rfl⟩ : syracuseStep 2053007 = 3079511) B3079511
theorem B3079517 : Blo 2051435 3079517 := bbase (se 3 (by rfl) ⟨577409, by rfl⟩ : syracuseStep 3079517 = 1154819) (by norm_num)
theorem B2053011 : Blo 2051435 2053011 := bstep (se 1 (by rfl) ⟨1539758, by rfl⟩ : syracuseStep 2053011 = 3079517) B3079517
theorem B4619285 : Blo 2051435 4619285 := bbase (se 6 (by rfl) ⟨108264, by rfl⟩ : syracuseStep 4619285 = 216529) (by norm_num)
theorem B3079523 : Blo 2051435 3079523 := bstep (se 1 (by rfl) ⟨2309642, by rfl⟩ : syracuseStep 3079523 = 4619285) B4619285
theorem B2053015 : Blo 2051435 2053015 := bstep (se 1 (by rfl) ⟨1539761, by rfl⟩ : syracuseStep 2053015 = 3079523) B3079523
theorem B7795061 : Blo 2051435 7795061 := bbase (se 5 (by rfl) ⟨365393, by rfl⟩ : syracuseStep 7795061 = 730787) (by norm_num)
theorem B5196707 : Blo 2051435 5196707 := bstep (se 1 (by rfl) ⟨3897530, by rfl⟩ : syracuseStep 5196707 = 7795061) B7795061
theorem B3464471 : Blo 2051435 3464471 := bstep (se 1 (by rfl) ⟨2598353, by rfl⟩ : syracuseStep 3464471 = 5196707) B5196707
theorem B2309647 : Blo 2051435 2309647 := bstep (se 1 (by rfl) ⟨1732235, by rfl⟩ : syracuseStep 2309647 = 3464471) B3464471
theorem B3079529 : Blo 2051435 3079529 := bstep (se 2 (by rfl) ⟨1154823, by rfl⟩ : syracuseStep 3079529 = 2309647) B2309647
theorem B2053019 : Blo 2051435 2053019 := bstep (se 1 (by rfl) ⟨1539764, by rfl⟩ : syracuseStep 2053019 = 3079529) B3079529
theorem B2192365 : Blo 2051435 2192365 := bbase (se 3 (by rfl) ⟨411068, by rfl⟩ : syracuseStep 2192365 = 822137) (by norm_num)
theorem B11692613 : Blo 2051435 11692613 := bstep (se 4 (by rfl) ⟨1096182, by rfl⟩ : syracuseStep 11692613 = 2192365) B2192365
theorem B7795075 : Blo 2051435 7795075 := bstep (se 1 (by rfl) ⟨5846306, by rfl⟩ : syracuseStep 7795075 = 11692613) B11692613
theorem B10393433 : Blo 2051435 10393433 := bstep (se 2 (by rfl) ⟨3897537, by rfl⟩ : syracuseStep 10393433 = 7795075) B7795075
theorem B6928955 : Blo 2051435 6928955 := bstep (se 1 (by rfl) ⟨5196716, by rfl⟩ : syracuseStep 6928955 = 10393433) B10393433
theorem B4619303 : Blo 2051435 4619303 := bstep (se 1 (by rfl) ⟨3464477, by rfl⟩ : syracuseStep 4619303 = 6928955) B6928955
theorem B3079535 : Blo 2051435 3079535 := bstep (se 1 (by rfl) ⟨2309651, by rfl⟩ : syracuseStep 3079535 = 4619303) B4619303
theorem B2053023 : Blo 2051435 2053023 := bstep (se 1 (by rfl) ⟨1539767, by rfl⟩ : syracuseStep 2053023 = 3079535) B3079535
theorem B3079541 : Blo 2051435 3079541 := bbase (se 5 (by rfl) ⟨144353, by rfl⟩ : syracuseStep 3079541 = 288707) (by norm_num)
theorem B2053027 : Blo 2051435 2053027 := bstep (se 1 (by rfl) ⟨1539770, by rfl⟩ : syracuseStep 2053027 = 3079541) B3079541
theorem B2923165 : Blo 2051435 2923165 := bbase (se 3 (by rfl) ⟨548093, by rfl⟩ : syracuseStep 2923165 = 1096187) (by norm_num)
theorem B3897553 : Blo 2051435 3897553 := bstep (se 2 (by rfl) ⟨1461582, by rfl⟩ : syracuseStep 3897553 = 2923165) B2923165
theorem B5196737 : Blo 2051435 5196737 := bstep (se 2 (by rfl) ⟨1948776, by rfl⟩ : syracuseStep 5196737 = 3897553) B3897553
theorem B3464491 : Blo 2051435 3464491 := bstep (se 1 (by rfl) ⟨2598368, by rfl⟩ : syracuseStep 3464491 = 5196737) B5196737
theorem B4619321 : Blo 2051435 4619321 := bstep (se 2 (by rfl) ⟨1732245, by rfl⟩ : syracuseStep 4619321 = 3464491) B3464491
theorem B3079547 : Blo 2051435 3079547 := bstep (se 1 (by rfl) ⟨2309660, by rfl⟩ : syracuseStep 3079547 = 4619321) B4619321
theorem B2053031 : Blo 2051435 2053031 := bstep (se 1 (by rfl) ⟨1539773, by rfl⟩ : syracuseStep 2053031 = 3079547) B3079547
theorem B2309665 : Blo 2051435 2309665 := bbase (se 2 (by rfl) ⟨866124, by rfl⟩ : syracuseStep 2309665 = 1732249) (by norm_num)
theorem B3079553 : Blo 2051435 3079553 := bstep (se 2 (by rfl) ⟨1154832, by rfl⟩ : syracuseStep 3079553 = 2309665) B2309665
theorem B2053035 : Blo 2051435 2053035 := bstep (se 1 (by rfl) ⟨1539776, by rfl⟩ : syracuseStep 2053035 = 3079553) B3079553
theorem B5196757 : Blo 2051435 5196757 := bbase (se 7 (by rfl) ⟨60899, by rfl⟩ : syracuseStep 5196757 = 121799) (by norm_num)
theorem B6929009 : Blo 2051435 6929009 := bstep (se 2 (by rfl) ⟨2598378, by rfl⟩ : syracuseStep 6929009 = 5196757) B5196757
theorem B4619339 : Blo 2051435 4619339 := bstep (se 1 (by rfl) ⟨3464504, by rfl⟩ : syracuseStep 4619339 = 6929009) B6929009
theorem B3079559 : Blo 2051435 3079559 := bstep (se 1 (by rfl) ⟨2309669, by rfl⟩ : syracuseStep 3079559 = 4619339) B4619339
theorem B2053039 : Blo 2051435 2053039 := bstep (se 1 (by rfl) ⟨1539779, by rfl⟩ : syracuseStep 2053039 = 3079559) B3079559
theorem B3079565 : Blo 2051435 3079565 := bbase (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) (by norm_num)
theorem B2053043 : Blo 2051435 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B4619357 : Blo 2051435 4619357 := bbase (se 3 (by rfl) ⟨866129, by rfl⟩ : syracuseStep 4619357 = 1732259) (by norm_num)
theorem B3079571 : Blo 2051435 3079571 := bstep (se 1 (by rfl) ⟨2309678, by rfl⟩ : syracuseStep 3079571 = 4619357) B4619357
theorem B2053047 : Blo 2051435 2053047 := bstep (se 1 (by rfl) ⟨1539785, by rfl⟩ : syracuseStep 2053047 = 3079571) B3079571
theorem B3464525 : Blo 2051435 3464525 := bbase (se 3 (by rfl) ⟨649598, by rfl⟩ : syracuseStep 3464525 = 1299197) (by norm_num)
theorem B2309683 : Blo 2051435 2309683 := bstep (se 1 (by rfl) ⟨1732262, by rfl⟩ : syracuseStep 2309683 = 3464525) B3464525
theorem B3079577 : Blo 2051435 3079577 := bstep (se 2 (by rfl) ⟨1154841, by rfl⟩ : syracuseStep 3079577 = 2309683) B2309683
theorem B2053051 : Blo 2051435 2053051 := bstep (se 1 (by rfl) ⟨1539788, by rfl⟩ : syracuseStep 2053051 = 3079577) B3079577
theorem B7706357 : Blo 2051435 7706357 := bbase (se 5 (by rfl) ⟨361235, by rfl⟩ : syracuseStep 7706357 = 722471) (by norm_num)
theorem B5137571 : Blo 2051435 5137571 := bstep (se 1 (by rfl) ⟨3853178, by rfl⟩ : syracuseStep 5137571 = 7706357) B7706357
theorem B3425047 : Blo 2051435 3425047 := bstep (se 1 (by rfl) ⟨2568785, by rfl⟩ : syracuseStep 3425047 = 5137571) B5137571
theorem B18266917 : Blo 2051435 18266917 := bstep (se 4 (by rfl) ⟨1712523, by rfl⟩ : syracuseStep 18266917 = 3425047) B3425047
theorem B24355889 : Blo 2051435 24355889 := bstep (se 2 (by rfl) ⟨9133458, by rfl⟩ : syracuseStep 24355889 = 18266917) B18266917
theorem B16237259 : Blo 2051435 16237259 := bstep (se 1 (by rfl) ⟨12177944, by rfl⟩ : syracuseStep 16237259 = 24355889) B24355889
theorem B10824839 : Blo 2051435 10824839 := bstep (se 1 (by rfl) ⟨8118629, by rfl⟩ : syracuseStep 10824839 = 16237259) B16237259
theorem B7216559 : Blo 2051435 7216559 := bstep (se 1 (by rfl) ⟨5412419, by rfl⟩ : syracuseStep 7216559 = 10824839) B10824839
theorem B4811039 : Blo 2051435 4811039 := bstep (se 1 (by rfl) ⟨3608279, by rfl⟩ : syracuseStep 4811039 = 7216559) B7216559
theorem B3207359 : Blo 2051435 3207359 := bstep (se 1 (by rfl) ⟨2405519, by rfl⟩ : syracuseStep 3207359 = 4811039) B4811039
theorem B8552957 : Blo 2051435 8552957 := bstep (se 3 (by rfl) ⟨1603679, by rfl⟩ : syracuseStep 8552957 = 3207359) B3207359
theorem B91231541 : Blo 2051435 91231541 := bstep (se 5 (by rfl) ⟨4276478, by rfl⟩ : syracuseStep 91231541 = 8552957) B8552957
theorem B60821027 : Blo 2051435 60821027 := bstep (se 1 (by rfl) ⟨45615770, by rfl⟩ : syracuseStep 60821027 = 91231541) B91231541
theorem B40547351 : Blo 2051435 40547351 := bstep (se 1 (by rfl) ⟨30410513, by rfl⟩ : syracuseStep 40547351 = 60821027) B60821027
theorem B27031567 : Blo 2051435 27031567 := bstep (se 1 (by rfl) ⟨20273675, by rfl⟩ : syracuseStep 27031567 = 40547351) B40547351
theorem B36042089 : Blo 2051435 36042089 := bstep (se 2 (by rfl) ⟨13515783, by rfl⟩ : syracuseStep 36042089 = 27031567) B27031567
theorem B384448949 : Blo 2051435 384448949 := bstep (se 5 (by rfl) ⟨18021044, by rfl⟩ : syracuseStep 384448949 = 36042089) B36042089
theorem B256299299 : Blo 2051435 256299299 := bstep (se 1 (by rfl) ⟨192224474, by rfl⟩ : syracuseStep 256299299 = 384448949) B384448949
theorem B170866199 : Blo 2051435 170866199 := bstep (se 1 (by rfl) ⟨128149649, by rfl⟩ : syracuseStep 170866199 = 256299299) B256299299
theorem B113910799 : Blo 2051435 113910799 := bstep (se 1 (by rfl) ⟨85433099, by rfl⟩ : syracuseStep 113910799 = 170866199) B170866199
theorem B151881065 : Blo 2051435 151881065 := bstep (se 2 (by rfl) ⟨56955399, by rfl⟩ : syracuseStep 151881065 = 113910799) B113910799
theorem B101254043 : Blo 2051435 101254043 := bstep (se 1 (by rfl) ⟨75940532, by rfl⟩ : syracuseStep 101254043 = 151881065) B151881065
theorem B67502695 : Blo 2051435 67502695 := bstep (se 1 (by rfl) ⟨50627021, by rfl⟩ : syracuseStep 67502695 = 101254043) B101254043
theorem B90003593 : Blo 2051435 90003593 := bstep (se 2 (by rfl) ⟨33751347, by rfl⟩ : syracuseStep 90003593 = 67502695) B67502695
theorem B240009581 : Blo 2051435 240009581 := bstep (se 3 (by rfl) ⟨45001796, by rfl⟩ : syracuseStep 240009581 = 90003593) B90003593
theorem B640025549 : Blo 2051435 640025549 := bstep (se 3 (by rfl) ⟨120004790, by rfl⟩ : syracuseStep 640025549 = 240009581) B240009581
theorem B426683699 : Blo 2051435 426683699 := bstep (se 1 (by rfl) ⟨320012774, by rfl⟩ : syracuseStep 426683699 = 640025549) B640025549
theorem B284455799 : Blo 2051435 284455799 := bstep (se 1 (by rfl) ⟨213341849, by rfl⟩ : syracuseStep 284455799 = 426683699) B426683699
theorem B189637199 : Blo 2051435 189637199 := bstep (se 1 (by rfl) ⟨142227899, by rfl⟩ : syracuseStep 189637199 = 284455799) B284455799
theorem B126424799 : Blo 2051435 126424799 := bstep (se 1 (by rfl) ⟨94818599, by rfl⟩ : syracuseStep 126424799 = 189637199) B189637199
theorem B84283199 : Blo 2051435 84283199 := bstep (se 1 (by rfl) ⟨63212399, by rfl⟩ : syracuseStep 84283199 = 126424799) B126424799
theorem B56188799 : Blo 2051435 56188799 := bstep (se 1 (by rfl) ⟨42141599, by rfl⟩ : syracuseStep 56188799 = 84283199) B84283199
theorem B37459199 : Blo 2051435 37459199 := bstep (se 1 (by rfl) ⟨28094399, by rfl⟩ : syracuseStep 37459199 = 56188799) B56188799
theorem B24972799 : Blo 2051435 24972799 := bstep (se 1 (by rfl) ⟨18729599, by rfl⟩ : syracuseStep 24972799 = 37459199) B37459199
theorem B33297065 : Blo 2051435 33297065 := bstep (se 2 (by rfl) ⟨12486399, by rfl⟩ : syracuseStep 33297065 = 24972799) B24972799
theorem B22198043 : Blo 2051435 22198043 := bstep (se 1 (by rfl) ⟨16648532, by rfl⟩ : syracuseStep 22198043 = 33297065) B33297065
theorem B14798695 : Blo 2051435 14798695 := bstep (se 1 (by rfl) ⟨11099021, by rfl⟩ : syracuseStep 14798695 = 22198043) B22198043
theorem B19731593 : Blo 2051435 19731593 := bstep (se 2 (by rfl) ⟨7399347, by rfl⟩ : syracuseStep 19731593 = 14798695) B14798695
theorem B13154395 : Blo 2051435 13154395 := bstep (se 1 (by rfl) ⟨9865796, by rfl⟩ : syracuseStep 13154395 = 19731593) B19731593
theorem B17539193 : Blo 2051435 17539193 := bstep (se 2 (by rfl) ⟨6577197, by rfl⟩ : syracuseStep 17539193 = 13154395) B13154395
theorem B11692795 : Blo 2051435 11692795 := bstep (se 1 (by rfl) ⟨8769596, by rfl⟩ : syracuseStep 11692795 = 17539193) B17539193
theorem B15590393 : Blo 2051435 15590393 := bstep (se 2 (by rfl) ⟨5846397, by rfl⟩ : syracuseStep 15590393 = 11692795) B11692795
theorem B10393595 : Blo 2051435 10393595 := bstep (se 1 (by rfl) ⟨7795196, by rfl⟩ : syracuseStep 10393595 = 15590393) B15590393
theorem B6929063 : Blo 2051435 6929063 := bstep (se 1 (by rfl) ⟨5196797, by rfl⟩ : syracuseStep 6929063 = 10393595) B10393595
theorem B4619375 : Blo 2051435 4619375 := bstep (se 1 (by rfl) ⟨3464531, by rfl⟩ : syracuseStep 4619375 = 6929063) B6929063
theorem B3079583 : Blo 2051435 3079583 := bstep (se 1 (by rfl) ⟨2309687, by rfl⟩ : syracuseStep 3079583 = 4619375) B4619375
theorem B2053055 : Blo 2051435 2053055 := bstep (se 1 (by rfl) ⟨1539791, by rfl⟩ : syracuseStep 2053055 = 3079583) B3079583
theorem B3079589 : Blo 2051435 3079589 := bbase (se 4 (by rfl) ⟨288711, by rfl⟩ : syracuseStep 3079589 = 577423) (by norm_num)
theorem B2053059 : Blo 2051435 2053059 := bstep (se 1 (by rfl) ⟨1539794, by rfl⟩ : syracuseStep 2053059 = 3079589) B3079589
theorem B2598409 : Blo 2051435 2598409 := bbase (se 2 (by rfl) ⟨974403, by rfl⟩ : syracuseStep 2598409 = 1948807) (by norm_num)
theorem B3464545 : Blo 2051435 3464545 := bstep (se 2 (by rfl) ⟨1299204, by rfl⟩ : syracuseStep 3464545 = 2598409) B2598409
theorem B4619393 : Blo 2051435 4619393 := bstep (se 2 (by rfl) ⟨1732272, by rfl⟩ : syracuseStep 4619393 = 3464545) B3464545
theorem B3079595 : Blo 2051435 3079595 := bstep (se 1 (by rfl) ⟨2309696, by rfl⟩ : syracuseStep 3079595 = 4619393) B4619393
theorem B2053063 : Blo 2051435 2053063 := bstep (se 1 (by rfl) ⟨1539797, by rfl⟩ : syracuseStep 2053063 = 3079595) B3079595
theorem B2309701 : Blo 2051435 2309701 := bbase (se 4 (by rfl) ⟨216534, by rfl⟩ : syracuseStep 2309701 = 433069) (by norm_num)
theorem B3079601 : Blo 2051435 3079601 := bstep (se 2 (by rfl) ⟨1154850, by rfl⟩ : syracuseStep 3079601 = 2309701) B2309701
theorem B2053067 : Blo 2051435 2053067 := bstep (se 1 (by rfl) ⟨1539800, by rfl⟩ : syracuseStep 2053067 = 3079601) B3079601
theorem B3897629 : Blo 2051435 3897629 := bbase (se 3 (by rfl) ⟨730805, by rfl⟩ : syracuseStep 3897629 = 1461611) (by norm_num)
theorem B2598419 : Blo 2051435 2598419 := bstep (se 1 (by rfl) ⟨1948814, by rfl⟩ : syracuseStep 2598419 = 3897629) B3897629
theorem B6929117 : Blo 2051435 6929117 := bstep (se 3 (by rfl) ⟨1299209, by rfl⟩ : syracuseStep 6929117 = 2598419) B2598419
theorem B4619411 : Blo 2051435 4619411 := bstep (se 1 (by rfl) ⟨3464558, by rfl⟩ : syracuseStep 4619411 = 6929117) B6929117
theorem B3079607 : Blo 2051435 3079607 := bstep (se 1 (by rfl) ⟨2309705, by rfl⟩ : syracuseStep 3079607 = 4619411) B4619411
theorem B2053071 : Blo 2051435 2053071 := bstep (se 1 (by rfl) ⟨1539803, by rfl⟩ : syracuseStep 2053071 = 3079607) B3079607
theorem B3079613 : Blo 2051435 3079613 := bbase (se 3 (by rfl) ⟨577427, by rfl⟩ : syracuseStep 3079613 = 1154855) (by norm_num)
theorem B2053075 : Blo 2051435 2053075 := bstep (se 1 (by rfl) ⟨1539806, by rfl⟩ : syracuseStep 2053075 = 3079613) B3079613
theorem B4619429 : Blo 2051435 4619429 := bbase (se 4 (by rfl) ⟨433071, by rfl⟩ : syracuseStep 4619429 = 866143) (by norm_num)
theorem B3079619 : Blo 2051435 3079619 := bstep (se 1 (by rfl) ⟨2309714, by rfl⟩ : syracuseStep 3079619 = 4619429) B4619429
theorem B2053079 : Blo 2051435 2053079 := bstep (se 1 (by rfl) ⟨1539809, by rfl⟩ : syracuseStep 2053079 = 3079619) B3079619
theorem B5196869 : Blo 2051435 5196869 := bbase (se 4 (by rfl) ⟨487206, by rfl⟩ : syracuseStep 5196869 = 974413) (by norm_num)
theorem B3464579 : Blo 2051435 3464579 := bstep (se 1 (by rfl) ⟨2598434, by rfl⟩ : syracuseStep 3464579 = 5196869) B5196869
theorem B2309719 : Blo 2051435 2309719 := bstep (se 1 (by rfl) ⟨1732289, by rfl⟩ : syracuseStep 2309719 = 3464579) B3464579
theorem B3079625 : Blo 2051435 3079625 := bstep (se 2 (by rfl) ⟨1154859, by rfl⟩ : syracuseStep 3079625 = 2309719) B2309719
theorem B2053083 : Blo 2051435 2053083 := bstep (se 1 (by rfl) ⟨1539812, by rfl⟩ : syracuseStep 2053083 = 3079625) B3079625
theorem B6577301 : Blo 2051435 6577301 := bbase (se 6 (by rfl) ⟨154155, by rfl⟩ : syracuseStep 6577301 = 308311) (by norm_num)
theorem B4384867 : Blo 2051435 4384867 := bstep (se 1 (by rfl) ⟨3288650, by rfl⟩ : syracuseStep 4384867 = 6577301) B6577301
theorem B5846489 : Blo 2051435 5846489 := bstep (se 2 (by rfl) ⟨2192433, by rfl⟩ : syracuseStep 5846489 = 4384867) B4384867
theorem B3897659 : Blo 2051435 3897659 := bstep (se 1 (by rfl) ⟨2923244, by rfl⟩ : syracuseStep 3897659 = 5846489) B5846489
theorem B10393757 : Blo 2051435 10393757 := bstep (se 3 (by rfl) ⟨1948829, by rfl⟩ : syracuseStep 10393757 = 3897659) B3897659
theorem B6929171 : Blo 2051435 6929171 := bstep (se 1 (by rfl) ⟨5196878, by rfl⟩ : syracuseStep 6929171 = 10393757) B10393757
theorem B4619447 : Blo 2051435 4619447 := bstep (se 1 (by rfl) ⟨3464585, by rfl⟩ : syracuseStep 4619447 = 6929171) B6929171
theorem B3079631 : Blo 2051435 3079631 := bstep (se 1 (by rfl) ⟨2309723, by rfl⟩ : syracuseStep 3079631 = 4619447) B4619447
theorem B2053087 : Blo 2051435 2053087 := bstep (se 1 (by rfl) ⟨1539815, by rfl⟩ : syracuseStep 2053087 = 3079631) B3079631
theorem B3079637 : Blo 2051435 3079637 := bbase (se 7 (by rfl) ⟨36089, by rfl⟩ : syracuseStep 3079637 = 72179) (by norm_num)
theorem B2053091 : Blo 2051435 2053091 := bstep (se 1 (by rfl) ⟨1539818, by rfl⟩ : syracuseStep 2053091 = 3079637) B3079637
theorem B7795349 : Blo 2051435 7795349 := bbase (se 6 (by rfl) ⟨182703, by rfl⟩ : syracuseStep 7795349 = 365407) (by norm_num)
theorem B5196899 : Blo 2051435 5196899 := bstep (se 1 (by rfl) ⟨3897674, by rfl⟩ : syracuseStep 5196899 = 7795349) B7795349
theorem B3464599 : Blo 2051435 3464599 := bstep (se 1 (by rfl) ⟨2598449, by rfl⟩ : syracuseStep 3464599 = 5196899) B5196899
theorem B4619465 : Blo 2051435 4619465 := bstep (se 2 (by rfl) ⟨1732299, by rfl⟩ : syracuseStep 4619465 = 3464599) B3464599
theorem B3079643 : Blo 2051435 3079643 := bstep (se 1 (by rfl) ⟨2309732, by rfl⟩ : syracuseStep 3079643 = 4619465) B4619465
theorem B2053095 : Blo 2051435 2053095 := bstep (se 1 (by rfl) ⟨1539821, by rfl⟩ : syracuseStep 2053095 = 3079643) B3079643
theorem B2309737 : Blo 2051435 2309737 := bbase (se 2 (by rfl) ⟨866151, by rfl⟩ : syracuseStep 2309737 = 1732303) (by norm_num)
theorem B3079649 : Blo 2051435 3079649 := bstep (se 2 (by rfl) ⟨1154868, by rfl⟩ : syracuseStep 3079649 = 2309737) B2309737
theorem B2053099 : Blo 2051435 2053099 := bstep (se 1 (by rfl) ⟨1539824, by rfl⟩ : syracuseStep 2053099 = 3079649) B3079649
theorem B4384901 : Blo 2051435 4384901 := bbase (se 4 (by rfl) ⟨411084, by rfl⟩ : syracuseStep 4384901 = 822169) (by norm_num)
theorem B11693069 : Blo 2051435 11693069 := bstep (se 3 (by rfl) ⟨2192450, by rfl⟩ : syracuseStep 11693069 = 4384901) B4384901
theorem B7795379 : Blo 2051435 7795379 := bstep (se 1 (by rfl) ⟨5846534, by rfl⟩ : syracuseStep 7795379 = 11693069) B11693069
theorem B5196919 : Blo 2051435 5196919 := bstep (se 1 (by rfl) ⟨3897689, by rfl⟩ : syracuseStep 5196919 = 7795379) B7795379
theorem B6929225 : Blo 2051435 6929225 := bstep (se 2 (by rfl) ⟨2598459, by rfl⟩ : syracuseStep 6929225 = 5196919) B5196919
theorem B4619483 : Blo 2051435 4619483 := bstep (se 1 (by rfl) ⟨3464612, by rfl⟩ : syracuseStep 4619483 = 6929225) B6929225
theorem B3079655 : Blo 2051435 3079655 := bstep (se 1 (by rfl) ⟨2309741, by rfl⟩ : syracuseStep 3079655 = 4619483) B4619483
theorem B2053103 : Blo 2051435 2053103 := bstep (se 1 (by rfl) ⟨1539827, by rfl⟩ : syracuseStep 2053103 = 3079655) B3079655
theorem B3079661 : Blo 2051435 3079661 := bbase (se 3 (by rfl) ⟨577436, by rfl⟩ : syracuseStep 3079661 = 1154873) (by norm_num)
theorem B2053107 : Blo 2051435 2053107 := bstep (se 1 (by rfl) ⟨1539830, by rfl⟩ : syracuseStep 2053107 = 3079661) B3079661
theorem B4619501 : Blo 2051435 4619501 := bbase (se 3 (by rfl) ⟨866156, by rfl⟩ : syracuseStep 4619501 = 1732313) (by norm_num)
theorem B3079667 : Blo 2051435 3079667 := bstep (se 1 (by rfl) ⟨2309750, by rfl⟩ : syracuseStep 3079667 = 4619501) B4619501
theorem B2053111 : Blo 2051435 2053111 := bstep (se 1 (by rfl) ⟨1539833, by rfl⟩ : syracuseStep 2053111 = 3079667) B3079667
theorem B2923285 : Blo 2051435 2923285 := bbase (se 6 (by rfl) ⟨68514, by rfl⟩ : syracuseStep 2923285 = 137029) (by norm_num)
theorem B3897713 : Blo 2051435 3897713 := bstep (se 2 (by rfl) ⟨1461642, by rfl⟩ : syracuseStep 3897713 = 2923285) B2923285
theorem B2598475 : Blo 2051435 2598475 := bstep (se 1 (by rfl) ⟨1948856, by rfl⟩ : syracuseStep 2598475 = 3897713) B3897713
theorem B3464633 : Blo 2051435 3464633 := bstep (se 2 (by rfl) ⟨1299237, by rfl⟩ : syracuseStep 3464633 = 2598475) B2598475
theorem B2309755 : Blo 2051435 2309755 := bstep (se 1 (by rfl) ⟨1732316, by rfl⟩ : syracuseStep 2309755 = 3464633) B3464633
theorem B3079673 : Blo 2051435 3079673 := bstep (se 2 (by rfl) ⟨1154877, by rfl⟩ : syracuseStep 3079673 = 2309755) B2309755
theorem B2053115 : Blo 2051435 2053115 := bstep (se 1 (by rfl) ⟨1539836, by rfl⟩ : syracuseStep 2053115 = 3079673) B3079673
theorem B7500533 : Blo 2051435 7500533 := bbase (se 5 (by rfl) ⟨351587, by rfl⟩ : syracuseStep 7500533 = 703175) (by norm_num)
theorem B20001421 : Blo 2051435 20001421 := bstep (se 3 (by rfl) ⟨3750266, by rfl⟩ : syracuseStep 20001421 = 7500533) B7500533
theorem B26668561 : Blo 2051435 26668561 := bstep (se 2 (by rfl) ⟨10000710, by rfl⟩ : syracuseStep 26668561 = 20001421) B20001421
theorem B35558081 : Blo 2051435 35558081 := bstep (se 2 (by rfl) ⟨13334280, by rfl⟩ : syracuseStep 35558081 = 26668561) B26668561
theorem B23705387 : Blo 2051435 23705387 := bstep (se 1 (by rfl) ⟨17779040, by rfl⟩ : syracuseStep 23705387 = 35558081) B35558081
theorem B15803591 : Blo 2051435 15803591 := bstep (se 1 (by rfl) ⟨11852693, by rfl⟩ : syracuseStep 15803591 = 23705387) B23705387
theorem B168571637 : Blo 2051435 168571637 := bstep (se 5 (by rfl) ⟨7901795, by rfl⟩ : syracuseStep 168571637 = 15803591) B15803591
theorem B112381091 : Blo 2051435 112381091 := bstep (se 1 (by rfl) ⟨84285818, by rfl⟩ : syracuseStep 112381091 = 168571637) B168571637
theorem B74920727 : Blo 2051435 74920727 := bstep (se 1 (by rfl) ⟨56190545, by rfl⟩ : syracuseStep 74920727 = 112381091) B112381091
theorem B49947151 : Blo 2051435 49947151 := bstep (se 1 (by rfl) ⟨37460363, by rfl⟩ : syracuseStep 49947151 = 74920727) B74920727
theorem B66596201 : Blo 2051435 66596201 := bstep (se 2 (by rfl) ⟨24973575, by rfl⟩ : syracuseStep 66596201 = 49947151) B49947151
theorem B44397467 : Blo 2051435 44397467 := bstep (se 1 (by rfl) ⟨33298100, by rfl⟩ : syracuseStep 44397467 = 66596201) B66596201
theorem B29598311 : Blo 2051435 29598311 := bstep (se 1 (by rfl) ⟨22198733, by rfl⟩ : syracuseStep 29598311 = 44397467) B44397467
theorem B78928829 : Blo 2051435 78928829 := bstep (se 3 (by rfl) ⟨14799155, by rfl⟩ : syracuseStep 78928829 = 29598311) B29598311
theorem B52619219 : Blo 2051435 52619219 := bstep (se 1 (by rfl) ⟨39464414, by rfl⟩ : syracuseStep 52619219 = 78928829) B78928829
theorem B35079479 : Blo 2051435 35079479 := bstep (se 1 (by rfl) ⟨26309609, by rfl⟩ : syracuseStep 35079479 = 52619219) B52619219
theorem B23386319 : Blo 2051435 23386319 := bstep (se 1 (by rfl) ⟨17539739, by rfl⟩ : syracuseStep 23386319 = 35079479) B35079479
theorem B15590879 : Blo 2051435 15590879 := bstep (se 1 (by rfl) ⟨11693159, by rfl⟩ : syracuseStep 15590879 = 23386319) B23386319
theorem B10393919 : Blo 2051435 10393919 := bstep (se 1 (by rfl) ⟨7795439, by rfl⟩ : syracuseStep 10393919 = 15590879) B15590879
theorem B6929279 : Blo 2051435 6929279 := bstep (se 1 (by rfl) ⟨5196959, by rfl⟩ : syracuseStep 6929279 = 10393919) B10393919
theorem B4619519 : Blo 2051435 4619519 := bstep (se 1 (by rfl) ⟨3464639, by rfl⟩ : syracuseStep 4619519 = 6929279) B6929279
theorem B3079679 : Blo 2051435 3079679 := bstep (se 1 (by rfl) ⟨2309759, by rfl⟩ : syracuseStep 3079679 = 4619519) B4619519
theorem B2053119 : Blo 2051435 2053119 := bstep (se 1 (by rfl) ⟨1539839, by rfl⟩ : syracuseStep 2053119 = 3079679) B3079679
theorem B3079685 : Blo 2051435 3079685 := bbase (se 4 (by rfl) ⟨288720, by rfl⟩ : syracuseStep 3079685 = 577441) (by norm_num)
theorem B2053123 : Blo 2051435 2053123 := bstep (se 1 (by rfl) ⟨1539842, by rfl⟩ : syracuseStep 2053123 = 3079685) B3079685
theorem B3464653 : Blo 2051435 3464653 := bbase (se 3 (by rfl) ⟨649622, by rfl⟩ : syracuseStep 3464653 = 1299245) (by norm_num)
theorem B4619537 : Blo 2051435 4619537 := bstep (se 2 (by rfl) ⟨1732326, by rfl⟩ : syracuseStep 4619537 = 3464653) B3464653
theorem B3079691 : Blo 2051435 3079691 := bstep (se 1 (by rfl) ⟨2309768, by rfl⟩ : syracuseStep 3079691 = 4619537) B4619537
theorem B2053127 : Blo 2051435 2053127 := bstep (se 1 (by rfl) ⟨1539845, by rfl⟩ : syracuseStep 2053127 = 3079691) B3079691
theorem B2309773 : Blo 2051435 2309773 := bbase (se 3 (by rfl) ⟨433082, by rfl⟩ : syracuseStep 2309773 = 866165) (by norm_num)
theorem B3079697 : Blo 2051435 3079697 := bstep (se 2 (by rfl) ⟨1154886, by rfl⟩ : syracuseStep 3079697 = 2309773) B2309773
theorem B2053131 : Blo 2051435 2053131 := bstep (se 1 (by rfl) ⟨1539848, by rfl⟩ : syracuseStep 2053131 = 3079697) B3079697
theorem B6929333 : Blo 2051435 6929333 := bbase (se 5 (by rfl) ⟨324812, by rfl⟩ : syracuseStep 6929333 = 649625) (by norm_num)
theorem B4619555 : Blo 2051435 4619555 := bstep (se 1 (by rfl) ⟨3464666, by rfl⟩ : syracuseStep 4619555 = 6929333) B6929333
theorem B3079703 : Blo 2051435 3079703 := bstep (se 1 (by rfl) ⟨2309777, by rfl⟩ : syracuseStep 3079703 = 4619555) B4619555
theorem B2053135 : Blo 2051435 2053135 := bstep (se 1 (by rfl) ⟨1539851, by rfl⟩ : syracuseStep 2053135 = 3079703) B3079703
theorem B3079709 : Blo 2051435 3079709 := bbase (se 3 (by rfl) ⟨577445, by rfl⟩ : syracuseStep 3079709 = 1154891) (by norm_num)
theorem B2053139 : Blo 2051435 2053139 := bstep (se 1 (by rfl) ⟨1539854, by rfl⟩ : syracuseStep 2053139 = 3079709) B3079709
theorem B4619573 : Blo 2051435 4619573 := bbase (se 5 (by rfl) ⟨216542, by rfl⟩ : syracuseStep 4619573 = 433085) (by norm_num)
theorem B3079715 : Blo 2051435 3079715 := bstep (se 1 (by rfl) ⟨2309786, by rfl⟩ : syracuseStep 3079715 = 4619573) B4619573
theorem B2053143 : Blo 2051435 2053143 := bstep (se 1 (by rfl) ⟨1539857, by rfl⟩ : syracuseStep 2053143 = 3079715) B3079715
theorem B2633969 : Blo 2051435 2633969 := bbase (se 2 (by rfl) ⟨987738, by rfl⟩ : syracuseStep 2633969 = 1975477) (by norm_num)
theorem B7023917 : Blo 2051435 7023917 := bstep (se 3 (by rfl) ⟨1316984, by rfl⟩ : syracuseStep 7023917 = 2633969) B2633969
theorem B4682611 : Blo 2051435 4682611 := bstep (se 1 (by rfl) ⟨3511958, by rfl⟩ : syracuseStep 4682611 = 7023917) B7023917
theorem B6243481 : Blo 2051435 6243481 := bstep (se 2 (by rfl) ⟨2341305, by rfl⟩ : syracuseStep 6243481 = 4682611) B4682611
theorem B8324641 : Blo 2051435 8324641 := bstep (se 2 (by rfl) ⟨3121740, by rfl⟩ : syracuseStep 8324641 = 6243481) B6243481
theorem B11099521 : Blo 2051435 11099521 := bstep (se 2 (by rfl) ⟨4162320, by rfl⟩ : syracuseStep 11099521 = 8324641) B8324641
theorem B14799361 : Blo 2051435 14799361 := bstep (se 2 (by rfl) ⟨5549760, by rfl⟩ : syracuseStep 14799361 = 11099521) B11099521
theorem B19732481 : Blo 2051435 19732481 := bstep (se 2 (by rfl) ⟨7399680, by rfl⟩ : syracuseStep 19732481 = 14799361) B14799361
theorem B13154987 : Blo 2051435 13154987 := bstep (se 1 (by rfl) ⟨9866240, by rfl⟩ : syracuseStep 13154987 = 19732481) B19732481
theorem B8769991 : Blo 2051435 8769991 := bstep (se 1 (by rfl) ⟨6577493, by rfl⟩ : syracuseStep 8769991 = 13154987) B13154987
theorem B11693321 : Blo 2051435 11693321 := bstep (se 2 (by rfl) ⟨4384995, by rfl⟩ : syracuseStep 11693321 = 8769991) B8769991
theorem B7795547 : Blo 2051435 7795547 := bstep (se 1 (by rfl) ⟨5846660, by rfl⟩ : syracuseStep 7795547 = 11693321) B11693321
theorem B5197031 : Blo 2051435 5197031 := bstep (se 1 (by rfl) ⟨3897773, by rfl⟩ : syracuseStep 5197031 = 7795547) B7795547
theorem B3464687 : Blo 2051435 3464687 := bstep (se 1 (by rfl) ⟨2598515, by rfl⟩ : syracuseStep 3464687 = 5197031) B5197031
theorem B2309791 : Blo 2051435 2309791 := bstep (se 1 (by rfl) ⟨1732343, by rfl⟩ : syracuseStep 2309791 = 3464687) B3464687
theorem B3079721 : Blo 2051435 3079721 := bstep (se 2 (by rfl) ⟨1154895, by rfl⟩ : syracuseStep 3079721 = 2309791) B2309791
theorem B2053147 : Blo 2051435 2053147 := bstep (se 1 (by rfl) ⟨1539860, by rfl⟩ : syracuseStep 2053147 = 3079721) B3079721
theorem B6243493 : Blo 2051435 6243493 := bbase (se 4 (by rfl) ⟨585327, by rfl⟩ : syracuseStep 6243493 = 1170655) (by norm_num)
theorem B8324657 : Blo 2051435 8324657 := bstep (se 2 (by rfl) ⟨3121746, by rfl⟩ : syracuseStep 8324657 = 6243493) B6243493
theorem B5549771 : Blo 2051435 5549771 := bstep (se 1 (by rfl) ⟨4162328, by rfl⟩ : syracuseStep 5549771 = 8324657) B8324657
theorem B3699847 : Blo 2051435 3699847 := bstep (se 1 (by rfl) ⟨2774885, by rfl⟩ : syracuseStep 3699847 = 5549771) B5549771
theorem B19732517 : Blo 2051435 19732517 := bstep (se 4 (by rfl) ⟨1849923, by rfl⟩ : syracuseStep 19732517 = 3699847) B3699847
theorem B13155011 : Blo 2051435 13155011 := bstep (se 1 (by rfl) ⟨9866258, by rfl⟩ : syracuseStep 13155011 = 19732517) B19732517
theorem B8770007 : Blo 2051435 8770007 := bstep (se 1 (by rfl) ⟨6577505, by rfl⟩ : syracuseStep 8770007 = 13155011) B13155011
theorem B5846671 : Blo 2051435 5846671 := bstep (se 1 (by rfl) ⟨4385003, by rfl⟩ : syracuseStep 5846671 = 8770007) B8770007
theorem B7795561 : Blo 2051435 7795561 := bstep (se 2 (by rfl) ⟨2923335, by rfl⟩ : syracuseStep 7795561 = 5846671) B5846671
theorem B10394081 : Blo 2051435 10394081 := bstep (se 2 (by rfl) ⟨3897780, by rfl⟩ : syracuseStep 10394081 = 7795561) B7795561
theorem B6929387 : Blo 2051435 6929387 := bstep (se 1 (by rfl) ⟨5197040, by rfl⟩ : syracuseStep 6929387 = 10394081) B10394081
theorem B4619591 : Blo 2051435 4619591 := bstep (se 1 (by rfl) ⟨3464693, by rfl⟩ : syracuseStep 4619591 = 6929387) B6929387
theorem B3079727 : Blo 2051435 3079727 := bstep (se 1 (by rfl) ⟨2309795, by rfl⟩ : syracuseStep 3079727 = 4619591) B4619591
theorem B2053151 : Blo 2051435 2053151 := bstep (se 1 (by rfl) ⟨1539863, by rfl⟩ : syracuseStep 2053151 = 3079727) B3079727
theorem B3079733 : Blo 2051435 3079733 := bbase (se 5 (by rfl) ⟨144362, by rfl⟩ : syracuseStep 3079733 = 288725) (by norm_num)
theorem B2053155 : Blo 2051435 2053155 := bstep (se 1 (by rfl) ⟨1539866, by rfl⟩ : syracuseStep 2053155 = 3079733) B3079733
theorem B5197061 : Blo 2051435 5197061 := bbase (se 4 (by rfl) ⟨487224, by rfl⟩ : syracuseStep 5197061 = 974449) (by norm_num)
theorem B3464707 : Blo 2051435 3464707 := bstep (se 1 (by rfl) ⟨2598530, by rfl⟩ : syracuseStep 3464707 = 5197061) B5197061
theorem B4619609 : Blo 2051435 4619609 := bstep (se 2 (by rfl) ⟨1732353, by rfl⟩ : syracuseStep 4619609 = 3464707) B3464707
theorem B3079739 : Blo 2051435 3079739 := bstep (se 1 (by rfl) ⟨2309804, by rfl⟩ : syracuseStep 3079739 = 4619609) B4619609
theorem B2053159 : Blo 2051435 2053159 := bstep (se 1 (by rfl) ⟨1539869, by rfl⟩ : syracuseStep 2053159 = 3079739) B3079739
theorem B2309809 : Blo 2051435 2309809 := bbase (se 2 (by rfl) ⟨866178, by rfl⟩ : syracuseStep 2309809 = 1732357) (by norm_num)
theorem B3079745 : Blo 2051435 3079745 := bstep (se 2 (by rfl) ⟨1154904, by rfl⟩ : syracuseStep 3079745 = 2309809) B2309809
theorem B2053163 : Blo 2051435 2053163 := bstep (se 1 (by rfl) ⟨1539872, by rfl⟩ : syracuseStep 2053163 = 3079745) B3079745
theorem B3699877 : Blo 2051435 3699877 := bbase (se 4 (by rfl) ⟨346863, by rfl⟩ : syracuseStep 3699877 = 693727) (by norm_num)
theorem B4933169 : Blo 2051435 4933169 := bstep (se 2 (by rfl) ⟨1849938, by rfl⟩ : syracuseStep 4933169 = 3699877) B3699877
theorem B3288779 : Blo 2051435 3288779 := bstep (se 1 (by rfl) ⟨2466584, by rfl⟩ : syracuseStep 3288779 = 4933169) B4933169
theorem B2192519 : Blo 2051435 2192519 := bstep (se 1 (by rfl) ⟨1644389, by rfl⟩ : syracuseStep 2192519 = 3288779) B3288779
theorem B5846717 : Blo 2051435 5846717 := bstep (se 3 (by rfl) ⟨1096259, by rfl⟩ : syracuseStep 5846717 = 2192519) B2192519
theorem B3897811 : Blo 2051435 3897811 := bstep (se 1 (by rfl) ⟨2923358, by rfl⟩ : syracuseStep 3897811 = 5846717) B5846717
theorem B5197081 : Blo 2051435 5197081 := bstep (se 2 (by rfl) ⟨1948905, by rfl⟩ : syracuseStep 5197081 = 3897811) B3897811
theorem B6929441 : Blo 2051435 6929441 := bstep (se 2 (by rfl) ⟨2598540, by rfl⟩ : syracuseStep 6929441 = 5197081) B5197081
theorem B4619627 : Blo 2051435 4619627 := bstep (se 1 (by rfl) ⟨3464720, by rfl⟩ : syracuseStep 4619627 = 6929441) B6929441
theorem B3079751 : Blo 2051435 3079751 := bstep (se 1 (by rfl) ⟨2309813, by rfl⟩ : syracuseStep 3079751 = 4619627) B4619627
theorem B2053167 : Blo 2051435 2053167 := bstep (se 1 (by rfl) ⟨1539875, by rfl⟩ : syracuseStep 2053167 = 3079751) B3079751
theorem B3079757 : Blo 2051435 3079757 := bbase (se 3 (by rfl) ⟨577454, by rfl⟩ : syracuseStep 3079757 = 1154909) (by norm_num)
theorem B2053171 : Blo 2051435 2053171 := bstep (se 1 (by rfl) ⟨1539878, by rfl⟩ : syracuseStep 2053171 = 3079757) B3079757
theorem B4619645 : Blo 2051435 4619645 := bbase (se 3 (by rfl) ⟨866183, by rfl⟩ : syracuseStep 4619645 = 1732367) (by norm_num)
theorem B3079763 : Blo 2051435 3079763 := bstep (se 1 (by rfl) ⟨2309822, by rfl⟩ : syracuseStep 3079763 = 4619645) B4619645
theorem B2053175 : Blo 2051435 2053175 := bstep (se 1 (by rfl) ⟨1539881, by rfl⟩ : syracuseStep 2053175 = 3079763) B3079763
theorem B3464741 : Blo 2051435 3464741 := bbase (se 4 (by rfl) ⟨324819, by rfl⟩ : syracuseStep 3464741 = 649639) (by norm_num)
theorem B2309827 : Blo 2051435 2309827 := bstep (se 1 (by rfl) ⟨1732370, by rfl⟩ : syracuseStep 2309827 = 3464741) B3464741
theorem B3079769 : Blo 2051435 3079769 := bstep (se 2 (by rfl) ⟨1154913, by rfl⟩ : syracuseStep 3079769 = 2309827) B2309827
theorem B2053179 : Blo 2051435 2053179 := bstep (se 1 (by rfl) ⟨1539884, by rfl⟩ : syracuseStep 2053179 = 3079769) B3079769
theorem B2923381 : Blo 2051435 2923381 := bbase (se 5 (by rfl) ⟨137033, by rfl⟩ : syracuseStep 2923381 = 274067) (by norm_num)
theorem B15591365 : Blo 2051435 15591365 := bstep (se 4 (by rfl) ⟨1461690, by rfl⟩ : syracuseStep 15591365 = 2923381) B2923381
theorem B10394243 : Blo 2051435 10394243 := bstep (se 1 (by rfl) ⟨7795682, by rfl⟩ : syracuseStep 10394243 = 15591365) B15591365
theorem B6929495 : Blo 2051435 6929495 := bstep (se 1 (by rfl) ⟨5197121, by rfl⟩ : syracuseStep 6929495 = 10394243) B10394243
theorem B4619663 : Blo 2051435 4619663 := bstep (se 1 (by rfl) ⟨3464747, by rfl⟩ : syracuseStep 4619663 = 6929495) B6929495
theorem B3079775 : Blo 2051435 3079775 := bstep (se 1 (by rfl) ⟨2309831, by rfl⟩ : syracuseStep 3079775 = 4619663) B4619663
theorem B2053183 : Blo 2051435 2053183 := bstep (se 1 (by rfl) ⟨1539887, by rfl⟩ : syracuseStep 2053183 = 3079775) B3079775
theorem B3079781 : Blo 2051435 3079781 := bbase (se 4 (by rfl) ⟨288729, by rfl⟩ : syracuseStep 3079781 = 577459) (by norm_num)
theorem B2053187 : Blo 2051435 2053187 := bstep (se 1 (by rfl) ⟨1539890, by rfl⟩ : syracuseStep 2053187 = 3079781) B3079781
theorem B2192545 : Blo 2051435 2192545 := bbase (se 2 (by rfl) ⟨822204, by rfl⟩ : syracuseStep 2192545 = 1644409) (by norm_num)
theorem B2923393 : Blo 2051435 2923393 := bstep (se 2 (by rfl) ⟨1096272, by rfl⟩ : syracuseStep 2923393 = 2192545) B2192545
theorem B3897857 : Blo 2051435 3897857 := bstep (se 2 (by rfl) ⟨1461696, by rfl⟩ : syracuseStep 3897857 = 2923393) B2923393
theorem B2598571 : Blo 2051435 2598571 := bstep (se 1 (by rfl) ⟨1948928, by rfl⟩ : syracuseStep 2598571 = 3897857) B3897857
theorem B3464761 : Blo 2051435 3464761 := bstep (se 2 (by rfl) ⟨1299285, by rfl⟩ : syracuseStep 3464761 = 2598571) B2598571
theorem B4619681 : Blo 2051435 4619681 := bstep (se 2 (by rfl) ⟨1732380, by rfl⟩ : syracuseStep 4619681 = 3464761) B3464761
theorem B3079787 : Blo 2051435 3079787 := bstep (se 1 (by rfl) ⟨2309840, by rfl⟩ : syracuseStep 3079787 = 4619681) B4619681
theorem B2053191 : Blo 2051435 2053191 := bstep (se 1 (by rfl) ⟨1539893, by rfl⟩ : syracuseStep 2053191 = 3079787) B3079787
theorem B2309845 : Blo 2051435 2309845 := bbase (se 7 (by rfl) ⟨27068, by rfl⟩ : syracuseStep 2309845 = 54137) (by norm_num)
theorem B3079793 : Blo 2051435 3079793 := bstep (se 2 (by rfl) ⟨1154922, by rfl⟩ : syracuseStep 3079793 = 2309845) B2309845
theorem B2053195 : Blo 2051435 2053195 := bstep (se 1 (by rfl) ⟨1539896, by rfl⟩ : syracuseStep 2053195 = 3079793) B3079793
theorem B2598581 : Blo 2051435 2598581 := bbase (se 5 (by rfl) ⟨121808, by rfl⟩ : syracuseStep 2598581 = 243617) (by norm_num)
theorem B6929549 : Blo 2051435 6929549 := bstep (se 3 (by rfl) ⟨1299290, by rfl⟩ : syracuseStep 6929549 = 2598581) B2598581
theorem B4619699 : Blo 2051435 4619699 := bstep (se 1 (by rfl) ⟨3464774, by rfl⟩ : syracuseStep 4619699 = 6929549) B6929549
theorem B3079799 : Blo 2051435 3079799 := bstep (se 1 (by rfl) ⟨2309849, by rfl⟩ : syracuseStep 3079799 = 4619699) B4619699
theorem B2053199 : Blo 2051435 2053199 := bstep (se 1 (by rfl) ⟨1539899, by rfl⟩ : syracuseStep 2053199 = 3079799) B3079799
theorem B3079805 : Blo 2051435 3079805 := bbase (se 3 (by rfl) ⟨577463, by rfl⟩ : syracuseStep 3079805 = 1154927) (by norm_num)
theorem B2053203 : Blo 2051435 2053203 := bstep (se 1 (by rfl) ⟨1539902, by rfl⟩ : syracuseStep 2053203 = 3079805) B3079805
theorem B4619717 : Blo 2051435 4619717 := bbase (se 4 (by rfl) ⟨433098, by rfl⟩ : syracuseStep 4619717 = 866197) (by norm_num)
theorem B3079811 : Blo 2051435 3079811 := bstep (se 1 (by rfl) ⟨2309858, by rfl⟩ : syracuseStep 3079811 = 4619717) B4619717
theorem B2053207 : Blo 2051435 2053207 := bstep (se 1 (by rfl) ⟨1539905, by rfl⟩ : syracuseStep 2053207 = 3079811) B3079811
theorem B9866549 : Blo 2051435 9866549 := bbase (se 5 (by rfl) ⟨462494, by rfl⟩ : syracuseStep 9866549 = 924989) (by norm_num)
theorem B6577699 : Blo 2051435 6577699 := bstep (se 1 (by rfl) ⟨4933274, by rfl⟩ : syracuseStep 6577699 = 9866549) B9866549
theorem B8770265 : Blo 2051435 8770265 := bstep (se 2 (by rfl) ⟨3288849, by rfl⟩ : syracuseStep 8770265 = 6577699) B6577699
theorem B5846843 : Blo 2051435 5846843 := bstep (se 1 (by rfl) ⟨4385132, by rfl⟩ : syracuseStep 5846843 = 8770265) B8770265
theorem B3897895 : Blo 2051435 3897895 := bstep (se 1 (by rfl) ⟨2923421, by rfl⟩ : syracuseStep 3897895 = 5846843) B5846843
theorem B5197193 : Blo 2051435 5197193 := bstep (se 2 (by rfl) ⟨1948947, by rfl⟩ : syracuseStep 5197193 = 3897895) B3897895
theorem B3464795 : Blo 2051435 3464795 := bstep (se 1 (by rfl) ⟨2598596, by rfl⟩ : syracuseStep 3464795 = 5197193) B5197193
theorem B2309863 : Blo 2051435 2309863 := bstep (se 1 (by rfl) ⟨1732397, by rfl⟩ : syracuseStep 2309863 = 3464795) B3464795
theorem B3079817 : Blo 2051435 3079817 := bstep (se 2 (by rfl) ⟨1154931, by rfl⟩ : syracuseStep 3079817 = 2309863) B2309863
theorem B2053211 : Blo 2051435 2053211 := bstep (se 1 (by rfl) ⟨1539908, by rfl⟩ : syracuseStep 2053211 = 3079817) B3079817
theorem B10394405 : Blo 2051435 10394405 := bbase (se 4 (by rfl) ⟨974475, by rfl⟩ : syracuseStep 10394405 = 1948951) (by norm_num)
theorem B6929603 : Blo 2051435 6929603 := bstep (se 1 (by rfl) ⟨5197202, by rfl⟩ : syracuseStep 6929603 = 10394405) B10394405
theorem B4619735 : Blo 2051435 4619735 := bstep (se 1 (by rfl) ⟨3464801, by rfl⟩ : syracuseStep 4619735 = 6929603) B6929603
theorem B3079823 : Blo 2051435 3079823 := bstep (se 1 (by rfl) ⟨2309867, by rfl⟩ : syracuseStep 3079823 = 4619735) B4619735
theorem B2053215 : Blo 2051435 2053215 := bstep (se 1 (by rfl) ⟨1539911, by rfl⟩ : syracuseStep 2053215 = 3079823) B3079823
theorem B3079829 : Blo 2051435 3079829 := bbase (se 6 (by rfl) ⟨72183, by rfl⟩ : syracuseStep 3079829 = 144367) (by norm_num)
theorem B2053219 : Blo 2051435 2053219 := bstep (se 1 (by rfl) ⟨1539914, by rfl⟩ : syracuseStep 2053219 = 3079829) B3079829
theorem B3951101 : Blo 2051435 3951101 := bbase (se 3 (by rfl) ⟨740831, by rfl⟩ : syracuseStep 3951101 = 1481663) (by norm_num)
theorem B2634067 : Blo 2051435 2634067 := bstep (se 1 (by rfl) ⟨1975550, by rfl⟩ : syracuseStep 2634067 = 3951101) B3951101
theorem B3512089 : Blo 2051435 3512089 := bstep (se 2 (by rfl) ⟨1317033, by rfl⟩ : syracuseStep 3512089 = 2634067) B2634067
theorem B4682785 : Blo 2051435 4682785 := bstep (se 2 (by rfl) ⟨1756044, by rfl⟩ : syracuseStep 4682785 = 3512089) B3512089
theorem B6243713 : Blo 2051435 6243713 := bstep (se 2 (by rfl) ⟨2341392, by rfl⟩ : syracuseStep 6243713 = 4682785) B4682785
theorem B4162475 : Blo 2051435 4162475 := bstep (se 1 (by rfl) ⟨3121856, by rfl⟩ : syracuseStep 4162475 = 6243713) B6243713
theorem B2774983 : Blo 2051435 2774983 := bstep (se 1 (by rfl) ⟨2081237, by rfl⟩ : syracuseStep 2774983 = 4162475) B4162475
theorem B3699977 : Blo 2051435 3699977 := bstep (se 2 (by rfl) ⟨1387491, by rfl⟩ : syracuseStep 3699977 = 2774983) B2774983
theorem B9866605 : Blo 2051435 9866605 := bstep (se 3 (by rfl) ⟨1849988, by rfl⟩ : syracuseStep 9866605 = 3699977) B3699977
theorem B13155473 : Blo 2051435 13155473 := bstep (se 2 (by rfl) ⟨4933302, by rfl⟩ : syracuseStep 13155473 = 9866605) B9866605
theorem B8770315 : Blo 2051435 8770315 := bstep (se 1 (by rfl) ⟨6577736, by rfl⟩ : syracuseStep 8770315 = 13155473) B13155473
theorem B11693753 : Blo 2051435 11693753 := bstep (se 2 (by rfl) ⟨4385157, by rfl⟩ : syracuseStep 11693753 = 8770315) B8770315
theorem B7795835 : Blo 2051435 7795835 := bstep (se 1 (by rfl) ⟨5846876, by rfl⟩ : syracuseStep 7795835 = 11693753) B11693753
theorem B5197223 : Blo 2051435 5197223 := bstep (se 1 (by rfl) ⟨3897917, by rfl⟩ : syracuseStep 5197223 = 7795835) B7795835
theorem B3464815 : Blo 2051435 3464815 := bstep (se 1 (by rfl) ⟨2598611, by rfl⟩ : syracuseStep 3464815 = 5197223) B5197223
theorem B4619753 : Blo 2051435 4619753 := bstep (se 2 (by rfl) ⟨1732407, by rfl⟩ : syracuseStep 4619753 = 3464815) B3464815
theorem B3079835 : Blo 2051435 3079835 := bstep (se 1 (by rfl) ⟨2309876, by rfl⟩ : syracuseStep 3079835 = 4619753) B4619753
theorem B2053223 : Blo 2051435 2053223 := bstep (se 1 (by rfl) ⟨1539917, by rfl⟩ : syracuseStep 2053223 = 3079835) B3079835
theorem B2309881 : Blo 2051435 2309881 := bbase (se 2 (by rfl) ⟨866205, by rfl⟩ : syracuseStep 2309881 = 1732411) (by norm_num)
theorem B3079841 : Blo 2051435 3079841 := bstep (se 2 (by rfl) ⟨1154940, by rfl⟩ : syracuseStep 3079841 = 2309881) B2309881
theorem B2053227 : Blo 2051435 2053227 := bstep (se 1 (by rfl) ⟨1539920, by rfl⟩ : syracuseStep 2053227 = 3079841) B3079841
theorem B2466661 : Blo 2051435 2466661 := bbase (se 4 (by rfl) ⟨231249, by rfl⟩ : syracuseStep 2466661 = 462499) (by norm_num)
theorem B3288881 : Blo 2051435 3288881 := bstep (se 2 (by rfl) ⟨1233330, by rfl⟩ : syracuseStep 3288881 = 2466661) B2466661
theorem B8770349 : Blo 2051435 8770349 := bstep (se 3 (by rfl) ⟨1644440, by rfl⟩ : syracuseStep 8770349 = 3288881) B3288881
theorem B5846899 : Blo 2051435 5846899 := bstep (se 1 (by rfl) ⟨4385174, by rfl⟩ : syracuseStep 5846899 = 8770349) B8770349
theorem B7795865 : Blo 2051435 7795865 := bstep (se 2 (by rfl) ⟨2923449, by rfl⟩ : syracuseStep 7795865 = 5846899) B5846899
theorem B5197243 : Blo 2051435 5197243 := bstep (se 1 (by rfl) ⟨3897932, by rfl⟩ : syracuseStep 5197243 = 7795865) B7795865
theorem B6929657 : Blo 2051435 6929657 := bstep (se 2 (by rfl) ⟨2598621, by rfl⟩ : syracuseStep 6929657 = 5197243) B5197243
theorem B4619771 : Blo 2051435 4619771 := bstep (se 1 (by rfl) ⟨3464828, by rfl⟩ : syracuseStep 4619771 = 6929657) B6929657
theorem B3079847 : Blo 2051435 3079847 := bstep (se 1 (by rfl) ⟨2309885, by rfl⟩ : syracuseStep 3079847 = 4619771) B4619771
theorem B2053231 : Blo 2051435 2053231 := bstep (se 1 (by rfl) ⟨1539923, by rfl⟩ : syracuseStep 2053231 = 3079847) B3079847
theorem B3079853 : Blo 2051435 3079853 := bbase (se 3 (by rfl) ⟨577472, by rfl⟩ : syracuseStep 3079853 = 1154945) (by norm_num)
theorem B2053235 : Blo 2051435 2053235 := bstep (se 1 (by rfl) ⟨1539926, by rfl⟩ : syracuseStep 2053235 = 3079853) B3079853
theorem B4619789 : Blo 2051435 4619789 := bbase (se 3 (by rfl) ⟨866210, by rfl⟩ : syracuseStep 4619789 = 1732421) (by norm_num)
theorem B3079859 : Blo 2051435 3079859 := bstep (se 1 (by rfl) ⟨2309894, by rfl⟩ : syracuseStep 3079859 = 4619789) B4619789
theorem B2053239 : Blo 2051435 2053239 := bstep (se 1 (by rfl) ⟨1539929, by rfl⟩ : syracuseStep 2053239 = 3079859) B3079859
theorem B2598637 : Blo 2051435 2598637 := bbase (se 3 (by rfl) ⟨487244, by rfl⟩ : syracuseStep 2598637 = 974489) (by norm_num)
theorem B3464849 : Blo 2051435 3464849 := bstep (se 2 (by rfl) ⟨1299318, by rfl⟩ : syracuseStep 3464849 = 2598637) B2598637
theorem B2309899 : Blo 2051435 2309899 := bstep (se 1 (by rfl) ⟨1732424, by rfl⟩ : syracuseStep 2309899 = 3464849) B3464849
theorem B3079865 : Blo 2051435 3079865 := bstep (se 2 (by rfl) ⟨1154949, by rfl⟩ : syracuseStep 3079865 = 2309899) B2309899
theorem B2053243 : Blo 2051435 2053243 := bstep (se 1 (by rfl) ⟨1539932, by rfl⟩ : syracuseStep 2053243 = 3079865) B3079865
theorem B5000669 : Blo 2051435 5000669 := bbase (se 3 (by rfl) ⟨937625, by rfl⟩ : syracuseStep 5000669 = 1875251) (by norm_num)
theorem B3333779 : Blo 2051435 3333779 := bstep (se 1 (by rfl) ⟨2500334, by rfl⟩ : syracuseStep 3333779 = 5000669) B5000669
theorem B2222519 : Blo 2051435 2222519 := bstep (se 1 (by rfl) ⟨1666889, by rfl⟩ : syracuseStep 2222519 = 3333779) B3333779
theorem B5926717 : Blo 2051435 5926717 := bstep (se 3 (by rfl) ⟨1111259, by rfl⟩ : syracuseStep 5926717 = 2222519) B2222519
theorem B7902289 : Blo 2051435 7902289 := bstep (se 2 (by rfl) ⟨2963358, by rfl⟩ : syracuseStep 7902289 = 5926717) B5926717
theorem B42145541 : Blo 2051435 42145541 := bstep (se 4 (by rfl) ⟨3951144, by rfl⟩ : syracuseStep 42145541 = 7902289) B7902289
theorem B28097027 : Blo 2051435 28097027 := bstep (se 1 (by rfl) ⟨21072770, by rfl⟩ : syracuseStep 28097027 = 42145541) B42145541
theorem B18731351 : Blo 2051435 18731351 := bstep (se 1 (by rfl) ⟨14048513, by rfl⟩ : syracuseStep 18731351 = 28097027) B28097027
theorem B49950269 : Blo 2051435 49950269 := bstep (se 3 (by rfl) ⟨9365675, by rfl⟩ : syracuseStep 49950269 = 18731351) B18731351
theorem B33300179 : Blo 2051435 33300179 := bstep (se 1 (by rfl) ⟨24975134, by rfl⟩ : syracuseStep 33300179 = 49950269) B49950269
theorem B22200119 : Blo 2051435 22200119 := bstep (se 1 (by rfl) ⟨16650089, by rfl⟩ : syracuseStep 22200119 = 33300179) B33300179
theorem B14800079 : Blo 2051435 14800079 := bstep (se 1 (by rfl) ⟨11100059, by rfl⟩ : syracuseStep 14800079 = 22200119) B22200119
theorem B9866719 : Blo 2051435 9866719 := bstep (se 1 (by rfl) ⟨7400039, by rfl⟩ : syracuseStep 9866719 = 14800079) B14800079
theorem B13155625 : Blo 2051435 13155625 := bstep (se 2 (by rfl) ⟨4933359, by rfl⟩ : syracuseStep 13155625 = 9866719) B9866719
theorem B17540833 : Blo 2051435 17540833 := bstep (se 2 (by rfl) ⟨6577812, by rfl⟩ : syracuseStep 17540833 = 13155625) B13155625
theorem B23387777 : Blo 2051435 23387777 := bstep (se 2 (by rfl) ⟨8770416, by rfl⟩ : syracuseStep 23387777 = 17540833) B17540833
theorem B15591851 : Blo 2051435 15591851 := bstep (se 1 (by rfl) ⟨11693888, by rfl⟩ : syracuseStep 15591851 = 23387777) B23387777
theorem B10394567 : Blo 2051435 10394567 := bstep (se 1 (by rfl) ⟨7795925, by rfl⟩ : syracuseStep 10394567 = 15591851) B15591851
theorem B6929711 : Blo 2051435 6929711 := bstep (se 1 (by rfl) ⟨5197283, by rfl⟩ : syracuseStep 6929711 = 10394567) B10394567
theorem B4619807 : Blo 2051435 4619807 := bstep (se 1 (by rfl) ⟨3464855, by rfl⟩ : syracuseStep 4619807 = 6929711) B6929711
theorem B3079871 : Blo 2051435 3079871 := bstep (se 1 (by rfl) ⟨2309903, by rfl⟩ : syracuseStep 3079871 = 4619807) B4619807
theorem B2053247 : Blo 2051435 2053247 := bstep (se 1 (by rfl) ⟨1539935, by rfl⟩ : syracuseStep 2053247 = 3079871) B3079871
theorem B3079877 : Blo 2051435 3079877 := bbase (se 4 (by rfl) ⟨288738, by rfl⟩ : syracuseStep 3079877 = 577477) (by norm_num)
theorem B2053251 : Blo 2051435 2053251 := bstep (se 1 (by rfl) ⟨1539938, by rfl⟩ : syracuseStep 2053251 = 3079877) B3079877
theorem B3464869 : Blo 2051435 3464869 := bbase (se 4 (by rfl) ⟨324831, by rfl⟩ : syracuseStep 3464869 = 649663) (by norm_num)
theorem B4619825 : Blo 2051435 4619825 := bstep (se 2 (by rfl) ⟨1732434, by rfl⟩ : syracuseStep 4619825 = 3464869) B3464869
theorem B3079883 : Blo 2051435 3079883 := bstep (se 1 (by rfl) ⟨2309912, by rfl⟩ : syracuseStep 3079883 = 4619825) B4619825
theorem B2053255 : Blo 2051435 2053255 := bstep (se 1 (by rfl) ⟨1539941, by rfl⟩ : syracuseStep 2053255 = 3079883) B3079883
theorem B2309917 : Blo 2051435 2309917 := bbase (se 3 (by rfl) ⟨433109, by rfl⟩ : syracuseStep 2309917 = 866219) (by norm_num)
theorem B3079889 : Blo 2051435 3079889 := bstep (se 2 (by rfl) ⟨1154958, by rfl⟩ : syracuseStep 3079889 = 2309917) B2309917
theorem B2053259 : Blo 2051435 2053259 := bstep (se 1 (by rfl) ⟨1539944, by rfl⟩ : syracuseStep 2053259 = 3079889) B3079889
theorem B6929765 : Blo 2051435 6929765 := bbase (se 4 (by rfl) ⟨649665, by rfl⟩ : syracuseStep 6929765 = 1299331) (by norm_num)
theorem B4619843 : Blo 2051435 4619843 := bstep (se 1 (by rfl) ⟨3464882, by rfl⟩ : syracuseStep 4619843 = 6929765) B6929765
theorem B3079895 : Blo 2051435 3079895 := bstep (se 1 (by rfl) ⟨2309921, by rfl⟩ : syracuseStep 3079895 = 4619843) B4619843
theorem B2053263 : Blo 2051435 2053263 := bstep (se 1 (by rfl) ⟨1539947, by rfl⟩ : syracuseStep 2053263 = 3079895) B3079895
theorem B3079901 : Blo 2051435 3079901 := bbase (se 3 (by rfl) ⟨577481, by rfl⟩ : syracuseStep 3079901 = 1154963) (by norm_num)
theorem B2053267 : Blo 2051435 2053267 := bstep (se 1 (by rfl) ⟨1539950, by rfl⟩ : syracuseStep 2053267 = 3079901) B3079901
theorem B4619861 : Blo 2051435 4619861 := bbase (se 8 (by rfl) ⟨27069, by rfl⟩ : syracuseStep 4619861 = 54139) (by norm_num)
theorem B3079907 : Blo 2051435 3079907 := bstep (se 1 (by rfl) ⟨2309930, by rfl⟩ : syracuseStep 3079907 = 4619861) B4619861
theorem B2053271 : Blo 2051435 2053271 := bstep (se 1 (by rfl) ⟨1539953, by rfl⟩ : syracuseStep 2053271 = 3079907) B3079907
theorem B4385269 : Blo 2051435 4385269 := bbase (se 5 (by rfl) ⟨205559, by rfl⟩ : syracuseStep 4385269 = 411119) (by norm_num)
theorem B5847025 : Blo 2051435 5847025 := bstep (se 2 (by rfl) ⟨2192634, by rfl⟩ : syracuseStep 5847025 = 4385269) B4385269
theorem B7796033 : Blo 2051435 7796033 := bstep (se 2 (by rfl) ⟨2923512, by rfl⟩ : syracuseStep 7796033 = 5847025) B5847025
theorem B5197355 : Blo 2051435 5197355 := bstep (se 1 (by rfl) ⟨3898016, by rfl⟩ : syracuseStep 5197355 = 7796033) B7796033
theorem B3464903 : Blo 2051435 3464903 := bstep (se 1 (by rfl) ⟨2598677, by rfl⟩ : syracuseStep 3464903 = 5197355) B5197355
theorem B2309935 : Blo 2051435 2309935 := bstep (se 1 (by rfl) ⟨1732451, by rfl⟩ : syracuseStep 2309935 = 3464903) B3464903
theorem B3079913 : Blo 2051435 3079913 := bstep (se 2 (by rfl) ⟨1154967, by rfl⟩ : syracuseStep 3079913 = 2309935) B2309935
theorem B2053275 : Blo 2051435 2053275 := bstep (se 1 (by rfl) ⟨1539956, by rfl⟩ : syracuseStep 2053275 = 3079913) B3079913
theorem B6502949 : Blo 2051435 6502949 := bbase (se 4 (by rfl) ⟨609651, by rfl⟩ : syracuseStep 6502949 = 1219303) (by norm_num)
theorem B4335299 : Blo 2051435 4335299 := bstep (se 1 (by rfl) ⟨3251474, by rfl⟩ : syracuseStep 4335299 = 6502949) B6502949
theorem B2890199 : Blo 2051435 2890199 := bstep (se 1 (by rfl) ⟨2167649, by rfl⟩ : syracuseStep 2890199 = 4335299) B4335299
theorem B7707197 : Blo 2051435 7707197 := bstep (se 3 (by rfl) ⟨1445099, by rfl⟩ : syracuseStep 7707197 = 2890199) B2890199
theorem B5138131 : Blo 2051435 5138131 := bstep (se 1 (by rfl) ⟨3853598, by rfl⟩ : syracuseStep 5138131 = 7707197) B7707197
theorem B6850841 : Blo 2051435 6850841 := bstep (se 2 (by rfl) ⟨2569065, by rfl⟩ : syracuseStep 6850841 = 5138131) B5138131
theorem B18268909 : Blo 2051435 18268909 := bstep (se 3 (by rfl) ⟨3425420, by rfl⟩ : syracuseStep 18268909 = 6850841) B6850841
theorem B97434181 : Blo 2051435 97434181 := bstep (se 4 (by rfl) ⟨9134454, by rfl⟩ : syracuseStep 97434181 = 18268909) B18268909
theorem B129912241 : Blo 2051435 129912241 := bstep (se 2 (by rfl) ⟨48717090, by rfl⟩ : syracuseStep 129912241 = 97434181) B97434181
theorem B173216321 : Blo 2051435 173216321 := bstep (se 2 (by rfl) ⟨64956120, by rfl⟩ : syracuseStep 173216321 = 129912241) B129912241
theorem B115477547 : Blo 2051435 115477547 := bstep (se 1 (by rfl) ⟨86608160, by rfl⟩ : syracuseStep 115477547 = 173216321) B173216321
theorem B307940125 : Blo 2051435 307940125 := bstep (se 3 (by rfl) ⟨57738773, by rfl⟩ : syracuseStep 307940125 = 115477547) B115477547
theorem B410586833 : Blo 2051435 410586833 := bstep (se 2 (by rfl) ⟨153970062, by rfl⟩ : syracuseStep 410586833 = 307940125) B307940125
theorem B273724555 : Blo 2051435 273724555 := bstep (se 1 (by rfl) ⟨205293416, by rfl⟩ : syracuseStep 273724555 = 410586833) B410586833
theorem B364966073 : Blo 2051435 364966073 := bstep (se 2 (by rfl) ⟨136862277, by rfl⟩ : syracuseStep 364966073 = 273724555) B273724555
theorem B243310715 : Blo 2051435 243310715 := bstep (se 1 (by rfl) ⟨182483036, by rfl⟩ : syracuseStep 243310715 = 364966073) B364966073
theorem B162207143 : Blo 2051435 162207143 := bstep (se 1 (by rfl) ⟨121655357, by rfl⟩ : syracuseStep 162207143 = 243310715) B243310715
theorem B108138095 : Blo 2051435 108138095 := bstep (se 1 (by rfl) ⟨81103571, by rfl⟩ : syracuseStep 108138095 = 162207143) B162207143
theorem B72092063 : Blo 2051435 72092063 := bstep (se 1 (by rfl) ⟨54069047, by rfl⟩ : syracuseStep 72092063 = 108138095) B108138095
theorem B192245501 : Blo 2051435 192245501 := bstep (se 3 (by rfl) ⟨36046031, by rfl⟩ : syracuseStep 192245501 = 72092063) B72092063
theorem B128163667 : Blo 2051435 128163667 := bstep (se 1 (by rfl) ⟨96122750, by rfl⟩ : syracuseStep 128163667 = 192245501) B192245501
theorem B170884889 : Blo 2051435 170884889 := bstep (se 2 (by rfl) ⟨64081833, by rfl⟩ : syracuseStep 170884889 = 128163667) B128163667
theorem B113923259 : Blo 2051435 113923259 := bstep (se 1 (by rfl) ⟨85442444, by rfl⟩ : syracuseStep 113923259 = 170884889) B170884889
theorem B75948839 : Blo 2051435 75948839 := bstep (se 1 (by rfl) ⟨56961629, by rfl⟩ : syracuseStep 75948839 = 113923259) B113923259
theorem B50632559 : Blo 2051435 50632559 := bstep (se 1 (by rfl) ⟨37974419, by rfl⟩ : syracuseStep 50632559 = 75948839) B75948839
theorem B33755039 : Blo 2051435 33755039 := bstep (se 1 (by rfl) ⟨25316279, by rfl⟩ : syracuseStep 33755039 = 50632559) B50632559
theorem B22503359 : Blo 2051435 22503359 := bstep (se 1 (by rfl) ⟨16877519, by rfl⟩ : syracuseStep 22503359 = 33755039) B33755039
theorem B60008957 : Blo 2051435 60008957 := bstep (se 3 (by rfl) ⟨11251679, by rfl⟩ : syracuseStep 60008957 = 22503359) B22503359
theorem B40005971 : Blo 2051435 40005971 := bstep (se 1 (by rfl) ⟨30004478, by rfl⟩ : syracuseStep 40005971 = 60008957) B60008957
theorem B26670647 : Blo 2051435 26670647 := bstep (se 1 (by rfl) ⟨20002985, by rfl⟩ : syracuseStep 26670647 = 40005971) B40005971
theorem B17780431 : Blo 2051435 17780431 := bstep (se 1 (by rfl) ⟨13335323, by rfl⟩ : syracuseStep 17780431 = 26670647) B26670647
theorem B23707241 : Blo 2051435 23707241 := bstep (se 2 (by rfl) ⟨8890215, by rfl⟩ : syracuseStep 23707241 = 17780431) B17780431
theorem B15804827 : Blo 2051435 15804827 := bstep (se 1 (by rfl) ⟨11853620, by rfl⟩ : syracuseStep 15804827 = 23707241) B23707241
theorem B10536551 : Blo 2051435 10536551 := bstep (se 1 (by rfl) ⟨7902413, by rfl⟩ : syracuseStep 10536551 = 15804827) B15804827
theorem B7024367 : Blo 2051435 7024367 := bstep (se 1 (by rfl) ⟨5268275, by rfl⟩ : syracuseStep 7024367 = 10536551) B10536551
theorem B18731645 : Blo 2051435 18731645 := bstep (se 3 (by rfl) ⟨3512183, by rfl⟩ : syracuseStep 18731645 = 7024367) B7024367
theorem B12487763 : Blo 2051435 12487763 := bstep (se 1 (by rfl) ⟨9365822, by rfl⟩ : syracuseStep 12487763 = 18731645) B18731645
theorem B8325175 : Blo 2051435 8325175 := bstep (se 1 (by rfl) ⟨6243881, by rfl⟩ : syracuseStep 8325175 = 12487763) B12487763
theorem B11100233 : Blo 2051435 11100233 := bstep (se 2 (by rfl) ⟨4162587, by rfl⟩ : syracuseStep 11100233 = 8325175) B8325175
theorem B7400155 : Blo 2051435 7400155 := bstep (se 1 (by rfl) ⟨5550116, by rfl⟩ : syracuseStep 7400155 = 11100233) B11100233
theorem B9866873 : Blo 2051435 9866873 := bstep (se 2 (by rfl) ⟨3700077, by rfl⟩ : syracuseStep 9866873 = 7400155) B7400155
theorem B26311661 : Blo 2051435 26311661 := bstep (se 3 (by rfl) ⟨4933436, by rfl⟩ : syracuseStep 26311661 = 9866873) B9866873
theorem B17541107 : Blo 2051435 17541107 := bstep (se 1 (by rfl) ⟨13155830, by rfl⟩ : syracuseStep 17541107 = 26311661) B26311661
theorem B11694071 : Blo 2051435 11694071 := bstep (se 1 (by rfl) ⟨8770553, by rfl⟩ : syracuseStep 11694071 = 17541107) B17541107
theorem B7796047 : Blo 2051435 7796047 := bstep (se 1 (by rfl) ⟨5847035, by rfl⟩ : syracuseStep 7796047 = 11694071) B11694071
theorem B10394729 : Blo 2051435 10394729 := bstep (se 2 (by rfl) ⟨3898023, by rfl⟩ : syracuseStep 10394729 = 7796047) B7796047
theorem B6929819 : Blo 2051435 6929819 := bstep (se 1 (by rfl) ⟨5197364, by rfl⟩ : syracuseStep 6929819 = 10394729) B10394729
theorem B4619879 : Blo 2051435 4619879 := bstep (se 1 (by rfl) ⟨3464909, by rfl⟩ : syracuseStep 4619879 = 6929819) B6929819
theorem B3079919 : Blo 2051435 3079919 := bstep (se 1 (by rfl) ⟨2309939, by rfl⟩ : syracuseStep 3079919 = 4619879) B4619879
theorem B2053279 : Blo 2051435 2053279 := bstep (se 1 (by rfl) ⟨1539959, by rfl⟩ : syracuseStep 2053279 = 3079919) B3079919
theorem B3079925 : Blo 2051435 3079925 := bbase (se 5 (by rfl) ⟨144371, by rfl⟩ : syracuseStep 3079925 = 288743) (by norm_num)
theorem B2053283 : Blo 2051435 2053283 := bstep (se 1 (by rfl) ⟨1539962, by rfl⟩ : syracuseStep 2053283 = 3079925) B3079925
theorem B3700093 : Blo 2051435 3700093 := bbase (se 3 (by rfl) ⟨693767, by rfl⟩ : syracuseStep 3700093 = 1387535) (by norm_num)
theorem B4933457 : Blo 2051435 4933457 := bstep (se 2 (by rfl) ⟨1850046, by rfl⟩ : syracuseStep 4933457 = 3700093) B3700093
theorem B3288971 : Blo 2051435 3288971 := bstep (se 1 (by rfl) ⟨2466728, by rfl⟩ : syracuseStep 3288971 = 4933457) B4933457
theorem B8770589 : Blo 2051435 8770589 := bstep (se 3 (by rfl) ⟨1644485, by rfl⟩ : syracuseStep 8770589 = 3288971) B3288971
theorem B5847059 : Blo 2051435 5847059 := bstep (se 1 (by rfl) ⟨4385294, by rfl⟩ : syracuseStep 5847059 = 8770589) B8770589
theorem B3898039 : Blo 2051435 3898039 := bstep (se 1 (by rfl) ⟨2923529, by rfl⟩ : syracuseStep 3898039 = 5847059) B5847059
theorem B5197385 : Blo 2051435 5197385 := bstep (se 2 (by rfl) ⟨1949019, by rfl⟩ : syracuseStep 5197385 = 3898039) B3898039
theorem B3464923 : Blo 2051435 3464923 := bstep (se 1 (by rfl) ⟨2598692, by rfl⟩ : syracuseStep 3464923 = 5197385) B5197385
theorem B4619897 : Blo 2051435 4619897 := bstep (se 2 (by rfl) ⟨1732461, by rfl⟩ : syracuseStep 4619897 = 3464923) B3464923
theorem B3079931 : Blo 2051435 3079931 := bstep (se 1 (by rfl) ⟨2309948, by rfl⟩ : syracuseStep 3079931 = 4619897) B4619897
theorem B2053287 : Blo 2051435 2053287 := bstep (se 1 (by rfl) ⟨1539965, by rfl⟩ : syracuseStep 2053287 = 3079931) B3079931
theorem B2309953 : Blo 2051435 2309953 := bbase (se 2 (by rfl) ⟨866232, by rfl⟩ : syracuseStep 2309953 = 1732465) (by norm_num)
theorem B3079937 : Blo 2051435 3079937 := bstep (se 2 (by rfl) ⟨1154976, by rfl⟩ : syracuseStep 3079937 = 2309953) B2309953
theorem B2053291 : Blo 2051435 2053291 := bstep (se 1 (by rfl) ⟨1539968, by rfl⟩ : syracuseStep 2053291 = 3079937) B3079937
theorem B5197405 : Blo 2051435 5197405 := bbase (se 3 (by rfl) ⟨974513, by rfl⟩ : syracuseStep 5197405 = 1949027) (by norm_num)
theorem B6929873 : Blo 2051435 6929873 := bstep (se 2 (by rfl) ⟨2598702, by rfl⟩ : syracuseStep 6929873 = 5197405) B5197405
theorem B4619915 : Blo 2051435 4619915 := bstep (se 1 (by rfl) ⟨3464936, by rfl⟩ : syracuseStep 4619915 = 6929873) B6929873
theorem B3079943 : Blo 2051435 3079943 := bstep (se 1 (by rfl) ⟨2309957, by rfl⟩ : syracuseStep 3079943 = 4619915) B4619915
theorem B2053295 : Blo 2051435 2053295 := bstep (se 1 (by rfl) ⟨1539971, by rfl⟩ : syracuseStep 2053295 = 3079943) B3079943
theorem B3079949 : Blo 2051435 3079949 := bbase (se 3 (by rfl) ⟨577490, by rfl⟩ : syracuseStep 3079949 = 1154981) (by norm_num)
theorem B2053299 : Blo 2051435 2053299 := bstep (se 1 (by rfl) ⟨1539974, by rfl⟩ : syracuseStep 2053299 = 3079949) B3079949
theorem B4619933 : Blo 2051435 4619933 := bbase (se 3 (by rfl) ⟨866237, by rfl⟩ : syracuseStep 4619933 = 1732475) (by norm_num)
theorem B3079955 : Blo 2051435 3079955 := bstep (se 1 (by rfl) ⟨2309966, by rfl⟩ : syracuseStep 3079955 = 4619933) B4619933
theorem B2053303 : Blo 2051435 2053303 := bstep (se 1 (by rfl) ⟨1539977, by rfl⟩ : syracuseStep 2053303 = 3079955) B3079955
theorem B3464957 : Blo 2051435 3464957 := bbase (se 3 (by rfl) ⟨649679, by rfl⟩ : syracuseStep 3464957 = 1299359) (by norm_num)
theorem B2309971 : Blo 2051435 2309971 := bstep (se 1 (by rfl) ⟨1732478, by rfl⟩ : syracuseStep 2309971 = 3464957) B3464957
theorem B3079961 : Blo 2051435 3079961 := bstep (se 2 (by rfl) ⟨1154985, by rfl⟩ : syracuseStep 3079961 = 2309971) B2309971
theorem B2053307 : Blo 2051435 2053307 := bstep (se 1 (by rfl) ⟨1539980, by rfl⟩ : syracuseStep 2053307 = 3079961) B3079961
theorem B2466757 : Blo 2051435 2466757 := bbase (se 4 (by rfl) ⟨231258, by rfl⟩ : syracuseStep 2466757 = 462517) (by norm_num)
theorem B3289009 : Blo 2051435 3289009 := bstep (se 2 (by rfl) ⟨1233378, by rfl⟩ : syracuseStep 3289009 = 2466757) B2466757
theorem B4385345 : Blo 2051435 4385345 := bstep (se 2 (by rfl) ⟨1644504, by rfl⟩ : syracuseStep 4385345 = 3289009) B3289009
theorem B11694253 : Blo 2051435 11694253 := bstep (se 3 (by rfl) ⟨2192672, by rfl⟩ : syracuseStep 11694253 = 4385345) B4385345
theorem B15592337 : Blo 2051435 15592337 := bstep (se 2 (by rfl) ⟨5847126, by rfl⟩ : syracuseStep 15592337 = 11694253) B11694253
theorem B10394891 : Blo 2051435 10394891 := bstep (se 1 (by rfl) ⟨7796168, by rfl⟩ : syracuseStep 10394891 = 15592337) B15592337
theorem B6929927 : Blo 2051435 6929927 := bstep (se 1 (by rfl) ⟨5197445, by rfl⟩ : syracuseStep 6929927 = 10394891) B10394891
theorem B4619951 : Blo 2051435 4619951 := bstep (se 1 (by rfl) ⟨3464963, by rfl⟩ : syracuseStep 4619951 = 6929927) B6929927
theorem B3079967 : Blo 2051435 3079967 := bstep (se 1 (by rfl) ⟨2309975, by rfl⟩ : syracuseStep 3079967 = 4619951) B4619951
theorem B2053311 : Blo 2051435 2053311 := bstep (se 1 (by rfl) ⟨1539983, by rfl⟩ : syracuseStep 2053311 = 3079967) B3079967
theorem B3079973 : Blo 2051435 3079973 := bbase (se 4 (by rfl) ⟨288747, by rfl⟩ : syracuseStep 3079973 = 577495) (by norm_num)
theorem B2053315 : Blo 2051435 2053315 := bstep (se 1 (by rfl) ⟨1539986, by rfl⟩ : syracuseStep 2053315 = 3079973) B3079973
theorem B2598733 : Blo 2051435 2598733 := bbase (se 3 (by rfl) ⟨487262, by rfl⟩ : syracuseStep 2598733 = 974525) (by norm_num)
theorem B3464977 : Blo 2051435 3464977 := bstep (se 2 (by rfl) ⟨1299366, by rfl⟩ : syracuseStep 3464977 = 2598733) B2598733
theorem B4619969 : Blo 2051435 4619969 := bstep (se 2 (by rfl) ⟨1732488, by rfl⟩ : syracuseStep 4619969 = 3464977) B3464977
theorem B3079979 : Blo 2051435 3079979 := bstep (se 1 (by rfl) ⟨2309984, by rfl⟩ : syracuseStep 3079979 = 4619969) B4619969
theorem B2053319 : Blo 2051435 2053319 := bstep (se 1 (by rfl) ⟨1539989, by rfl⟩ : syracuseStep 2053319 = 3079979) B3079979
theorem B2309989 : Blo 2051435 2309989 := bbase (se 4 (by rfl) ⟨216561, by rfl⟩ : syracuseStep 2309989 = 433123) (by norm_num)
theorem B3079985 : Blo 2051435 3079985 := bstep (se 2 (by rfl) ⟨1154994, by rfl⟩ : syracuseStep 3079985 = 2309989) B2309989
theorem B2053323 : Blo 2051435 2053323 := bstep (se 1 (by rfl) ⟨1539992, by rfl⟩ : syracuseStep 2053323 = 3079985) B3079985
theorem B5847173 : Blo 2051435 5847173 := bbase (se 4 (by rfl) ⟨548172, by rfl⟩ : syracuseStep 5847173 = 1096345) (by norm_num)
theorem B3898115 : Blo 2051435 3898115 := bstep (se 1 (by rfl) ⟨2923586, by rfl⟩ : syracuseStep 3898115 = 5847173) B5847173
theorem B2598743 : Blo 2051435 2598743 := bstep (se 1 (by rfl) ⟨1949057, by rfl⟩ : syracuseStep 2598743 = 3898115) B3898115
theorem B6929981 : Blo 2051435 6929981 := bstep (se 3 (by rfl) ⟨1299371, by rfl⟩ : syracuseStep 6929981 = 2598743) B2598743
theorem B4619987 : Blo 2051435 4619987 := bstep (se 1 (by rfl) ⟨3464990, by rfl⟩ : syracuseStep 4619987 = 6929981) B6929981
theorem B3079991 : Blo 2051435 3079991 := bstep (se 1 (by rfl) ⟨2309993, by rfl⟩ : syracuseStep 3079991 = 4619987) B4619987
theorem B2053327 : Blo 2051435 2053327 := bstep (se 1 (by rfl) ⟨1539995, by rfl⟩ : syracuseStep 2053327 = 3079991) B3079991
theorem B3079997 : Blo 2051435 3079997 := bbase (se 3 (by rfl) ⟨577499, by rfl⟩ : syracuseStep 3079997 = 1154999) (by norm_num)
theorem B2053331 : Blo 2051435 2053331 := bstep (se 1 (by rfl) ⟨1539998, by rfl⟩ : syracuseStep 2053331 = 3079997) B3079997
theorem B4620005 : Blo 2051435 4620005 := bbase (se 4 (by rfl) ⟨433125, by rfl⟩ : syracuseStep 4620005 = 866251) (by norm_num)
theorem B3080003 : Blo 2051435 3080003 := bstep (se 1 (by rfl) ⟨2310002, by rfl⟩ : syracuseStep 3080003 = 4620005) B4620005
theorem B2053335 : Blo 2051435 2053335 := bstep (se 1 (by rfl) ⟨1540001, by rfl⟩ : syracuseStep 2053335 = 3080003) B3080003
theorem B5197517 : Blo 2051435 5197517 := bbase (se 3 (by rfl) ⟨974534, by rfl⟩ : syracuseStep 5197517 = 1949069) (by norm_num)
theorem B3465011 : Blo 2051435 3465011 := bstep (se 1 (by rfl) ⟨2598758, by rfl⟩ : syracuseStep 3465011 = 5197517) B5197517
theorem B2310007 : Blo 2051435 2310007 := bstep (se 1 (by rfl) ⟨1732505, by rfl⟩ : syracuseStep 2310007 = 3465011) B3465011
theorem B3080009 : Blo 2051435 3080009 := bstep (se 2 (by rfl) ⟨1155003, by rfl⟩ : syracuseStep 3080009 = 2310007) B2310007
theorem B2053339 : Blo 2051435 2053339 := bstep (se 1 (by rfl) ⟨1540004, by rfl⟩ : syracuseStep 2053339 = 3080009) B3080009
theorem B3289061 : Blo 2051435 3289061 := bbase (se 4 (by rfl) ⟨308349, by rfl⟩ : syracuseStep 3289061 = 616699) (by norm_num)
theorem B2192707 : Blo 2051435 2192707 := bstep (se 1 (by rfl) ⟨1644530, by rfl⟩ : syracuseStep 2192707 = 3289061) B3289061
theorem B2923609 : Blo 2051435 2923609 := bstep (se 2 (by rfl) ⟨1096353, by rfl⟩ : syracuseStep 2923609 = 2192707) B2192707
theorem B3898145 : Blo 2051435 3898145 := bstep (se 2 (by rfl) ⟨1461804, by rfl⟩ : syracuseStep 3898145 = 2923609) B2923609
theorem B10395053 : Blo 2051435 10395053 := bstep (se 3 (by rfl) ⟨1949072, by rfl⟩ : syracuseStep 10395053 = 3898145) B3898145
theorem B6930035 : Blo 2051435 6930035 := bstep (se 1 (by rfl) ⟨5197526, by rfl⟩ : syracuseStep 6930035 = 10395053) B10395053
theorem B4620023 : Blo 2051435 4620023 := bstep (se 1 (by rfl) ⟨3465017, by rfl⟩ : syracuseStep 4620023 = 6930035) B6930035
theorem B3080015 : Blo 2051435 3080015 := bstep (se 1 (by rfl) ⟨2310011, by rfl⟩ : syracuseStep 3080015 = 4620023) B4620023
theorem B2053343 : Blo 2051435 2053343 := bstep (se 1 (by rfl) ⟨1540007, by rfl⟩ : syracuseStep 2053343 = 3080015) B3080015
theorem B3080021 : Blo 2051435 3080021 := bbase (se 9 (by rfl) ⟨9023, by rfl⟩ : syracuseStep 3080021 = 18047) (by norm_num)
theorem B2053347 : Blo 2051435 2053347 := bstep (se 1 (by rfl) ⟨1540010, by rfl⟩ : syracuseStep 2053347 = 3080021) B3080021
theorem B9867221 : Blo 2051435 9867221 := bbase (se 7 (by rfl) ⟨115631, by rfl⟩ : syracuseStep 9867221 = 231263) (by norm_num)
theorem B6578147 : Blo 2051435 6578147 := bstep (se 1 (by rfl) ⟨4933610, by rfl⟩ : syracuseStep 6578147 = 9867221) B9867221
theorem B4385431 : Blo 2051435 4385431 := bstep (se 1 (by rfl) ⟨3289073, by rfl⟩ : syracuseStep 4385431 = 6578147) B6578147
theorem B5847241 : Blo 2051435 5847241 := bstep (se 2 (by rfl) ⟨2192715, by rfl⟩ : syracuseStep 5847241 = 4385431) B4385431
theorem B7796321 : Blo 2051435 7796321 := bstep (se 2 (by rfl) ⟨2923620, by rfl⟩ : syracuseStep 7796321 = 5847241) B5847241
theorem B5197547 : Blo 2051435 5197547 := bstep (se 1 (by rfl) ⟨3898160, by rfl⟩ : syracuseStep 5197547 = 7796321) B7796321
theorem B3465031 : Blo 2051435 3465031 := bstep (se 1 (by rfl) ⟨2598773, by rfl⟩ : syracuseStep 3465031 = 5197547) B5197547
theorem B4620041 : Blo 2051435 4620041 := bstep (se 2 (by rfl) ⟨1732515, by rfl⟩ : syracuseStep 4620041 = 3465031) B3465031
theorem B3080027 : Blo 2051435 3080027 := bstep (se 1 (by rfl) ⟨2310020, by rfl⟩ : syracuseStep 3080027 = 4620041) B4620041
theorem B2053351 : Blo 2051435 2053351 := bstep (se 1 (by rfl) ⟨1540013, by rfl⟩ : syracuseStep 2053351 = 3080027) B3080027
theorem B2310025 : Blo 2051435 2310025 := bbase (se 2 (by rfl) ⟨866259, by rfl⟩ : syracuseStep 2310025 = 1732519) (by norm_num)
theorem B3080033 : Blo 2051435 3080033 := bstep (se 2 (by rfl) ⟨1155012, by rfl⟩ : syracuseStep 3080033 = 2310025) B2310025
theorem B2053355 : Blo 2051435 2053355 := bstep (se 1 (by rfl) ⟨1540016, by rfl⟩ : syracuseStep 2053355 = 3080033) B3080033
theorem B3906325 : Blo 2051435 3906325 := bbase (se 6 (by rfl) ⟨91554, by rfl⟩ : syracuseStep 3906325 = 183109) (by norm_num)
theorem B20833733 : Blo 2051435 20833733 := bstep (se 4 (by rfl) ⟨1953162, by rfl⟩ : syracuseStep 20833733 = 3906325) B3906325
theorem B55556621 : Blo 2051435 55556621 := bstep (se 3 (by rfl) ⟨10416866, by rfl⟩ : syracuseStep 55556621 = 20833733) B20833733
theorem B37037747 : Blo 2051435 37037747 := bstep (se 1 (by rfl) ⟨27778310, by rfl⟩ : syracuseStep 37037747 = 55556621) B55556621
theorem B98767325 : Blo 2051435 98767325 := bstep (se 3 (by rfl) ⟨18518873, by rfl⟩ : syracuseStep 98767325 = 37037747) B37037747
theorem B65844883 : Blo 2051435 65844883 := bstep (se 1 (by rfl) ⟨49383662, by rfl⟩ : syracuseStep 65844883 = 98767325) B98767325
theorem B87793177 : Blo 2051435 87793177 := bstep (se 2 (by rfl) ⟨32922441, by rfl⟩ : syracuseStep 87793177 = 65844883) B65844883
theorem B117057569 : Blo 2051435 117057569 := bstep (se 2 (by rfl) ⟨43896588, by rfl⟩ : syracuseStep 117057569 = 87793177) B87793177
theorem B312153517 : Blo 2051435 312153517 := bstep (se 3 (by rfl) ⟨58528784, by rfl⟩ : syracuseStep 312153517 = 117057569) B117057569
theorem B416204689 : Blo 2051435 416204689 := bstep (se 2 (by rfl) ⟨156076758, by rfl⟩ : syracuseStep 416204689 = 312153517) B312153517
theorem B554939585 : Blo 2051435 554939585 := bstep (se 2 (by rfl) ⟨208102344, by rfl⟩ : syracuseStep 554939585 = 416204689) B416204689
theorem B369959723 : Blo 2051435 369959723 := bstep (se 1 (by rfl) ⟨277469792, by rfl⟩ : syracuseStep 369959723 = 554939585) B554939585
theorem B246639815 : Blo 2051435 246639815 := bstep (se 1 (by rfl) ⟨184979861, by rfl⟩ : syracuseStep 246639815 = 369959723) B369959723
theorem B164426543 : Blo 2051435 164426543 := bstep (se 1 (by rfl) ⟨123319907, by rfl⟩ : syracuseStep 164426543 = 246639815) B246639815
theorem B109617695 : Blo 2051435 109617695 := bstep (se 1 (by rfl) ⟨82213271, by rfl⟩ : syracuseStep 109617695 = 164426543) B164426543
theorem B73078463 : Blo 2051435 73078463 := bstep (se 1 (by rfl) ⟨54808847, by rfl⟩ : syracuseStep 73078463 = 109617695) B109617695
theorem B194875901 : Blo 2051435 194875901 := bstep (se 3 (by rfl) ⟨36539231, by rfl⟩ : syracuseStep 194875901 = 73078463) B73078463
theorem B129917267 : Blo 2051435 129917267 := bstep (se 1 (by rfl) ⟨97437950, by rfl⟩ : syracuseStep 129917267 = 194875901) B194875901
theorem B86611511 : Blo 2051435 86611511 := bstep (se 1 (by rfl) ⟨64958633, by rfl⟩ : syracuseStep 86611511 = 129917267) B129917267
theorem B57741007 : Blo 2051435 57741007 := bstep (se 1 (by rfl) ⟨43305755, by rfl⟩ : syracuseStep 57741007 = 86611511) B86611511
theorem B76988009 : Blo 2051435 76988009 := bstep (se 2 (by rfl) ⟨28870503, by rfl⟩ : syracuseStep 76988009 = 57741007) B57741007
theorem B51325339 : Blo 2051435 51325339 := bstep (se 1 (by rfl) ⟨38494004, by rfl⟩ : syracuseStep 51325339 = 76988009) B76988009
theorem B68433785 : Blo 2051435 68433785 := bstep (se 2 (by rfl) ⟨25662669, by rfl⟩ : syracuseStep 68433785 = 51325339) B51325339
theorem B45622523 : Blo 2051435 45622523 := bstep (se 1 (by rfl) ⟨34216892, by rfl⟩ : syracuseStep 45622523 = 68433785) B68433785
theorem B30415015 : Blo 2051435 30415015 := bstep (se 1 (by rfl) ⟨22811261, by rfl⟩ : syracuseStep 30415015 = 45622523) B45622523
theorem B162213413 : Blo 2051435 162213413 := bstep (se 4 (by rfl) ⟨15207507, by rfl⟩ : syracuseStep 162213413 = 30415015) B30415015
theorem B432569101 : Blo 2051435 432569101 := bstep (se 3 (by rfl) ⟨81106706, by rfl⟩ : syracuseStep 432569101 = 162213413) B162213413
theorem B576758801 : Blo 2051435 576758801 := bstep (se 2 (by rfl) ⟨216284550, by rfl⟩ : syracuseStep 576758801 = 432569101) B432569101
theorem B1538023469 : Blo 2051435 1538023469 := bstep (se 3 (by rfl) ⟨288379400, by rfl⟩ : syracuseStep 1538023469 = 576758801) B576758801
theorem B4101395917 : Blo 2051435 4101395917 := bstep (se 3 (by rfl) ⟨769011734, by rfl⟩ : syracuseStep 4101395917 = 1538023469) B1538023469
theorem B5468527889 : Blo 2051435 5468527889 := bstep (se 2 (by rfl) ⟨2050697958, by rfl⟩ : syracuseStep 5468527889 = 4101395917) B4101395917
theorem B3645685259 : Blo 2051435 3645685259 := bstep (se 1 (by rfl) ⟨2734263944, by rfl⟩ : syracuseStep 3645685259 = 5468527889) B5468527889
theorem B2430456839 : Blo 2051435 2430456839 := bstep (se 1 (by rfl) ⟨1822842629, by rfl⟩ : syracuseStep 2430456839 = 3645685259) B3645685259
theorem B1620304559 : Blo 2051435 1620304559 := bstep (se 1 (by rfl) ⟨1215228419, by rfl⟩ : syracuseStep 1620304559 = 2430456839) B2430456839
theorem B1080203039 : Blo 2051435 1080203039 := bstep (se 1 (by rfl) ⟨810152279, by rfl⟩ : syracuseStep 1080203039 = 1620304559) B1620304559
theorem B720135359 : Blo 2051435 720135359 := bstep (se 1 (by rfl) ⟨540101519, by rfl⟩ : syracuseStep 720135359 = 1080203039) B1080203039
theorem B480090239 : Blo 2051435 480090239 := bstep (se 1 (by rfl) ⟨360067679, by rfl⟩ : syracuseStep 480090239 = 720135359) B720135359
theorem B320060159 : Blo 2051435 320060159 := bstep (se 1 (by rfl) ⟨240045119, by rfl⟩ : syracuseStep 320060159 = 480090239) B480090239
theorem B213373439 : Blo 2051435 213373439 := bstep (se 1 (by rfl) ⟨160030079, by rfl⟩ : syracuseStep 213373439 = 320060159) B320060159
theorem B142248959 : Blo 2051435 142248959 := bstep (se 1 (by rfl) ⟨106686719, by rfl⟩ : syracuseStep 142248959 = 213373439) B213373439
theorem B94832639 : Blo 2051435 94832639 := bstep (se 1 (by rfl) ⟨71124479, by rfl⟩ : syracuseStep 94832639 = 142248959) B142248959
theorem B63221759 : Blo 2051435 63221759 := bstep (se 1 (by rfl) ⟨47416319, by rfl⟩ : syracuseStep 63221759 = 94832639) B94832639
theorem B42147839 : Blo 2051435 42147839 := bstep (se 1 (by rfl) ⟨31610879, by rfl⟩ : syracuseStep 42147839 = 63221759) B63221759
theorem B28098559 : Blo 2051435 28098559 := bstep (se 1 (by rfl) ⟨21073919, by rfl⟩ : syracuseStep 28098559 = 42147839) B42147839
theorem B149858981 : Blo 2051435 149858981 := bstep (se 4 (by rfl) ⟨14049279, by rfl⟩ : syracuseStep 149858981 = 28098559) B28098559
theorem B99905987 : Blo 2051435 99905987 := bstep (se 1 (by rfl) ⟨74929490, by rfl⟩ : syracuseStep 99905987 = 149858981) B149858981
theorem B66603991 : Blo 2051435 66603991 := bstep (se 1 (by rfl) ⟨49952993, by rfl⟩ : syracuseStep 66603991 = 99905987) B99905987
theorem B88805321 : Blo 2051435 88805321 := bstep (se 2 (by rfl) ⟨33301995, by rfl⟩ : syracuseStep 88805321 = 66603991) B66603991
theorem B59203547 : Blo 2051435 59203547 := bstep (se 1 (by rfl) ⟨44402660, by rfl⟩ : syracuseStep 59203547 = 88805321) B88805321
theorem B39469031 : Blo 2051435 39469031 := bstep (se 1 (by rfl) ⟨29601773, by rfl⟩ : syracuseStep 39469031 = 59203547) B59203547
theorem B26312687 : Blo 2051435 26312687 := bstep (se 1 (by rfl) ⟨19734515, by rfl⟩ : syracuseStep 26312687 = 39469031) B39469031
theorem B17541791 : Blo 2051435 17541791 := bstep (se 1 (by rfl) ⟨13156343, by rfl⟩ : syracuseStep 17541791 = 26312687) B26312687
theorem B11694527 : Blo 2051435 11694527 := bstep (se 1 (by rfl) ⟨8770895, by rfl⟩ : syracuseStep 11694527 = 17541791) B17541791
theorem B7796351 : Blo 2051435 7796351 := bstep (se 1 (by rfl) ⟨5847263, by rfl⟩ : syracuseStep 7796351 = 11694527) B11694527
theorem B5197567 : Blo 2051435 5197567 := bstep (se 1 (by rfl) ⟨3898175, by rfl⟩ : syracuseStep 5197567 = 7796351) B7796351
theorem B6930089 : Blo 2051435 6930089 := bstep (se 2 (by rfl) ⟨2598783, by rfl⟩ : syracuseStep 6930089 = 5197567) B5197567
theorem B4620059 : Blo 2051435 4620059 := bstep (se 1 (by rfl) ⟨3465044, by rfl⟩ : syracuseStep 4620059 = 6930089) B6930089
theorem B3080039 : Blo 2051435 3080039 := bstep (se 1 (by rfl) ⟨2310029, by rfl⟩ : syracuseStep 3080039 = 4620059) B4620059
theorem B2053359 : Blo 2051435 2053359 := bstep (se 1 (by rfl) ⟨1540019, by rfl⟩ : syracuseStep 2053359 = 3080039) B3080039
theorem B3080045 : Blo 2051435 3080045 := bbase (se 3 (by rfl) ⟨577508, by rfl⟩ : syracuseStep 3080045 = 1155017) (by norm_num)
theorem B2053363 : Blo 2051435 2053363 := bstep (se 1 (by rfl) ⟨1540022, by rfl⟩ : syracuseStep 2053363 = 3080045) B3080045
theorem B4620077 : Blo 2051435 4620077 := bbase (se 3 (by rfl) ⟨866264, by rfl⟩ : syracuseStep 4620077 = 1732529) (by norm_num)
theorem B3080051 : Blo 2051435 3080051 := bstep (se 1 (by rfl) ⟨2310038, by rfl⟩ : syracuseStep 3080051 = 4620077) B4620077
theorem B2053367 : Blo 2051435 2053367 := bstep (se 1 (by rfl) ⟨1540025, by rfl⟩ : syracuseStep 2053367 = 3080051) B3080051
theorem B8770949 : Blo 2051435 8770949 := bbase (se 4 (by rfl) ⟨822276, by rfl⟩ : syracuseStep 8770949 = 1644553) (by norm_num)
theorem B5847299 : Blo 2051435 5847299 := bstep (se 1 (by rfl) ⟨4385474, by rfl⟩ : syracuseStep 5847299 = 8770949) B8770949
theorem B3898199 : Blo 2051435 3898199 := bstep (se 1 (by rfl) ⟨2923649, by rfl⟩ : syracuseStep 3898199 = 5847299) B5847299
theorem B2598799 : Blo 2051435 2598799 := bstep (se 1 (by rfl) ⟨1949099, by rfl⟩ : syracuseStep 2598799 = 3898199) B3898199
theorem B3465065 : Blo 2051435 3465065 := bstep (se 2 (by rfl) ⟨1299399, by rfl⟩ : syracuseStep 3465065 = 2598799) B2598799
theorem B2310043 : Blo 2051435 2310043 := bstep (se 1 (by rfl) ⟨1732532, by rfl⟩ : syracuseStep 2310043 = 3465065) B3465065
theorem B3080057 : Blo 2051435 3080057 := bstep (se 2 (by rfl) ⟨1155021, by rfl⟩ : syracuseStep 3080057 = 2310043) B2310043
theorem B2053371 : Blo 2051435 2053371 := bstep (se 1 (by rfl) ⟨1540028, by rfl⟩ : syracuseStep 2053371 = 3080057) B3080057
theorem B7400501 : Blo 2051435 7400501 := bbase (se 5 (by rfl) ⟨346898, by rfl⟩ : syracuseStep 7400501 = 693797) (by norm_num)
theorem B4933667 : Blo 2051435 4933667 := bstep (se 1 (by rfl) ⟨3700250, by rfl⟩ : syracuseStep 4933667 = 7400501) B7400501
theorem B13156445 : Blo 2051435 13156445 := bstep (se 3 (by rfl) ⟨2466833, by rfl⟩ : syracuseStep 13156445 = 4933667) B4933667
theorem B35083853 : Blo 2051435 35083853 := bstep (se 3 (by rfl) ⟨6578222, by rfl⟩ : syracuseStep 35083853 = 13156445) B13156445
theorem B23389235 : Blo 2051435 23389235 := bstep (se 1 (by rfl) ⟨17541926, by rfl⟩ : syracuseStep 23389235 = 35083853) B35083853
theorem B15592823 : Blo 2051435 15592823 := bstep (se 1 (by rfl) ⟨11694617, by rfl⟩ : syracuseStep 15592823 = 23389235) B23389235
theorem B10395215 : Blo 2051435 10395215 := bstep (se 1 (by rfl) ⟨7796411, by rfl⟩ : syracuseStep 10395215 = 15592823) B15592823
theorem B6930143 : Blo 2051435 6930143 := bstep (se 1 (by rfl) ⟨5197607, by rfl⟩ : syracuseStep 6930143 = 10395215) B10395215
theorem B4620095 : Blo 2051435 4620095 := bstep (se 1 (by rfl) ⟨3465071, by rfl⟩ : syracuseStep 4620095 = 6930143) B6930143
theorem B3080063 : Blo 2051435 3080063 := bstep (se 1 (by rfl) ⟨2310047, by rfl⟩ : syracuseStep 3080063 = 4620095) B4620095
theorem B2053375 : Blo 2051435 2053375 := bstep (se 1 (by rfl) ⟨1540031, by rfl⟩ : syracuseStep 2053375 = 3080063) B3080063
theorem B3080069 : Blo 2051435 3080069 := bbase (se 4 (by rfl) ⟨288756, by rfl⟩ : syracuseStep 3080069 = 577513) (by norm_num)
theorem B2053379 : Blo 2051435 2053379 := bstep (se 1 (by rfl) ⟨1540034, by rfl⟩ : syracuseStep 2053379 = 3080069) B3080069
theorem B3465085 : Blo 2051435 3465085 := bbase (se 3 (by rfl) ⟨649703, by rfl⟩ : syracuseStep 3465085 = 1299407) (by norm_num)
theorem B4620113 : Blo 2051435 4620113 := bstep (se 2 (by rfl) ⟨1732542, by rfl⟩ : syracuseStep 4620113 = 3465085) B3465085
theorem B3080075 : Blo 2051435 3080075 := bstep (se 1 (by rfl) ⟨2310056, by rfl⟩ : syracuseStep 3080075 = 4620113) B4620113
theorem B2053383 : Blo 2051435 2053383 := bstep (se 1 (by rfl) ⟨1540037, by rfl⟩ : syracuseStep 2053383 = 3080075) B3080075
theorem B2310061 : Blo 2051435 2310061 := bbase (se 3 (by rfl) ⟨433136, by rfl⟩ : syracuseStep 2310061 = 866273) (by norm_num)
theorem B3080081 : Blo 2051435 3080081 := bstep (se 2 (by rfl) ⟨1155030, by rfl⟩ : syracuseStep 3080081 = 2310061) B2310061
theorem B2053387 : Blo 2051435 2053387 := bstep (se 1 (by rfl) ⟨1540040, by rfl⟩ : syracuseStep 2053387 = 3080081) B3080081
theorem B6930197 : Blo 2051435 6930197 := bbase (se 6 (by rfl) ⟨162426, by rfl⟩ : syracuseStep 6930197 = 324853) (by norm_num)
theorem B4620131 : Blo 2051435 4620131 := bstep (se 1 (by rfl) ⟨3465098, by rfl⟩ : syracuseStep 4620131 = 6930197) B6930197
theorem B3080087 : Blo 2051435 3080087 := bstep (se 1 (by rfl) ⟨2310065, by rfl⟩ : syracuseStep 3080087 = 4620131) B4620131
theorem B2053391 : Blo 2051435 2053391 := bstep (se 1 (by rfl) ⟨1540043, by rfl⟩ : syracuseStep 2053391 = 3080087) B3080087
theorem B3080093 : Blo 2051435 3080093 := bbase (se 3 (by rfl) ⟨577517, by rfl⟩ : syracuseStep 3080093 = 1155035) (by norm_num)
theorem B2053395 : Blo 2051435 2053395 := bstep (se 1 (by rfl) ⟨1540046, by rfl⟩ : syracuseStep 2053395 = 3080093) B3080093
theorem B4620149 : Blo 2051435 4620149 := bbase (se 5 (by rfl) ⟨216569, by rfl⟩ : syracuseStep 4620149 = 433139) (by norm_num)
theorem B3080099 : Blo 2051435 3080099 := bstep (se 1 (by rfl) ⟨2310074, by rfl⟩ : syracuseStep 3080099 = 4620149) B4620149
theorem B2053399 : Blo 2051435 2053399 := bstep (se 1 (by rfl) ⟨1540049, by rfl⟩ : syracuseStep 2053399 = 3080099) B3080099
theorem B5626181 : Blo 2051435 5626181 := bbase (se 4 (by rfl) ⟨527454, by rfl⟩ : syracuseStep 5626181 = 1054909) (by norm_num)
theorem B3750787 : Blo 2051435 3750787 := bstep (se 1 (by rfl) ⟨2813090, by rfl⟩ : syracuseStep 3750787 = 5626181) B5626181
theorem B5001049 : Blo 2051435 5001049 := bstep (se 2 (by rfl) ⟨1875393, by rfl⟩ : syracuseStep 5001049 = 3750787) B3750787
theorem B6668065 : Blo 2051435 6668065 := bstep (se 2 (by rfl) ⟨2500524, by rfl⟩ : syracuseStep 6668065 = 5001049) B5001049
theorem B35563013 : Blo 2051435 35563013 := bstep (se 4 (by rfl) ⟨3334032, by rfl⟩ : syracuseStep 35563013 = 6668065) B6668065
theorem B23708675 : Blo 2051435 23708675 := bstep (se 1 (by rfl) ⟨17781506, by rfl⟩ : syracuseStep 23708675 = 35563013) B35563013
theorem B15805783 : Blo 2051435 15805783 := bstep (se 1 (by rfl) ⟨11854337, by rfl⟩ : syracuseStep 15805783 = 23708675) B23708675
theorem B21074377 : Blo 2051435 21074377 := bstep (se 2 (by rfl) ⟨7902891, by rfl⟩ : syracuseStep 21074377 = 15805783) B15805783
theorem B28099169 : Blo 2051435 28099169 := bstep (se 2 (by rfl) ⟨10537188, by rfl⟩ : syracuseStep 28099169 = 21074377) B21074377
theorem B18732779 : Blo 2051435 18732779 := bstep (se 1 (by rfl) ⟨14049584, by rfl⟩ : syracuseStep 18732779 = 28099169) B28099169
theorem B12488519 : Blo 2051435 12488519 := bstep (se 1 (by rfl) ⟨9366389, by rfl⟩ : syracuseStep 12488519 = 18732779) B18732779
theorem B8325679 : Blo 2051435 8325679 := bstep (se 1 (by rfl) ⟨6244259, by rfl⟩ : syracuseStep 8325679 = 12488519) B12488519
theorem B11100905 : Blo 2051435 11100905 := bstep (se 2 (by rfl) ⟨4162839, by rfl⟩ : syracuseStep 11100905 = 8325679) B8325679
theorem B7400603 : Blo 2051435 7400603 := bstep (se 1 (by rfl) ⟨5550452, by rfl⟩ : syracuseStep 7400603 = 11100905) B11100905
theorem B19734941 : Blo 2051435 19734941 := bstep (se 3 (by rfl) ⟨3700301, by rfl⟩ : syracuseStep 19734941 = 7400603) B7400603
theorem B13156627 : Blo 2051435 13156627 := bstep (se 1 (by rfl) ⟨9867470, by rfl⟩ : syracuseStep 13156627 = 19734941) B19734941
theorem B17542169 : Blo 2051435 17542169 := bstep (se 2 (by rfl) ⟨6578313, by rfl⟩ : syracuseStep 17542169 = 13156627) B13156627
theorem B11694779 : Blo 2051435 11694779 := bstep (se 1 (by rfl) ⟨8771084, by rfl⟩ : syracuseStep 11694779 = 17542169) B17542169
theorem B7796519 : Blo 2051435 7796519 := bstep (se 1 (by rfl) ⟨5847389, by rfl⟩ : syracuseStep 7796519 = 11694779) B11694779
theorem B5197679 : Blo 2051435 5197679 := bstep (se 1 (by rfl) ⟨3898259, by rfl⟩ : syracuseStep 5197679 = 7796519) B7796519
theorem B3465119 : Blo 2051435 3465119 := bstep (se 1 (by rfl) ⟨2598839, by rfl⟩ : syracuseStep 3465119 = 5197679) B5197679
theorem B2310079 : Blo 2051435 2310079 := bstep (se 1 (by rfl) ⟨1732559, by rfl⟩ : syracuseStep 2310079 = 3465119) B3465119
theorem B3080105 : Blo 2051435 3080105 := bstep (se 2 (by rfl) ⟨1155039, by rfl⟩ : syracuseStep 3080105 = 2310079) B2310079
theorem B2053403 : Blo 2051435 2053403 := bstep (se 1 (by rfl) ⟨1540052, by rfl⟩ : syracuseStep 2053403 = 3080105) B3080105
theorem B7796533 : Blo 2051435 7796533 := bbase (se 5 (by rfl) ⟨365462, by rfl⟩ : syracuseStep 7796533 = 730925) (by norm_num)
theorem B10395377 : Blo 2051435 10395377 := bstep (se 2 (by rfl) ⟨3898266, by rfl⟩ : syracuseStep 10395377 = 7796533) B7796533
theorem B6930251 : Blo 2051435 6930251 := bstep (se 1 (by rfl) ⟨5197688, by rfl⟩ : syracuseStep 6930251 = 10395377) B10395377
theorem B4620167 : Blo 2051435 4620167 := bstep (se 1 (by rfl) ⟨3465125, by rfl⟩ : syracuseStep 4620167 = 6930251) B6930251
theorem B3080111 : Blo 2051435 3080111 := bstep (se 1 (by rfl) ⟨2310083, by rfl⟩ : syracuseStep 3080111 = 4620167) B4620167
theorem B2053407 : Blo 2051435 2053407 := bstep (se 1 (by rfl) ⟨1540055, by rfl⟩ : syracuseStep 2053407 = 3080111) B3080111
theorem B3080117 : Blo 2051435 3080117 := bbase (se 5 (by rfl) ⟨144380, by rfl⟩ : syracuseStep 3080117 = 288761) (by norm_num)
theorem B2053411 : Blo 2051435 2053411 := bstep (se 1 (by rfl) ⟨1540058, by rfl⟩ : syracuseStep 2053411 = 3080117) B3080117
theorem B5197709 : Blo 2051435 5197709 := bbase (se 3 (by rfl) ⟨974570, by rfl⟩ : syracuseStep 5197709 = 1949141) (by norm_num)
theorem B3465139 : Blo 2051435 3465139 := bstep (se 1 (by rfl) ⟨2598854, by rfl⟩ : syracuseStep 3465139 = 5197709) B5197709
theorem B4620185 : Blo 2051435 4620185 := bstep (se 2 (by rfl) ⟨1732569, by rfl⟩ : syracuseStep 4620185 = 3465139) B3465139
theorem B3080123 : Blo 2051435 3080123 := bstep (se 1 (by rfl) ⟨2310092, by rfl⟩ : syracuseStep 3080123 = 4620185) B4620185
theorem B2053415 : Blo 2051435 2053415 := bstep (se 1 (by rfl) ⟨1540061, by rfl⟩ : syracuseStep 2053415 = 3080123) B3080123
theorem B2310097 : Blo 2051435 2310097 := bbase (se 2 (by rfl) ⟨866286, by rfl⟩ : syracuseStep 2310097 = 1732573) (by norm_num)
theorem B3080129 : Blo 2051435 3080129 := bstep (se 2 (by rfl) ⟨1155048, by rfl⟩ : syracuseStep 3080129 = 2310097) B2310097
theorem B2053419 : Blo 2051435 2053419 := bstep (se 1 (by rfl) ⟨1540064, by rfl⟩ : syracuseStep 2053419 = 3080129) B3080129
theorem B3289189 : Blo 2051435 3289189 := bbase (se 4 (by rfl) ⟨308361, by rfl⟩ : syracuseStep 3289189 = 616723) (by norm_num)
theorem B4385585 : Blo 2051435 4385585 := bstep (se 2 (by rfl) ⟨1644594, by rfl⟩ : syracuseStep 4385585 = 3289189) B3289189
theorem B2923723 : Blo 2051435 2923723 := bstep (se 1 (by rfl) ⟨2192792, by rfl⟩ : syracuseStep 2923723 = 4385585) B4385585
theorem B3898297 : Blo 2051435 3898297 := bstep (se 2 (by rfl) ⟨1461861, by rfl⟩ : syracuseStep 3898297 = 2923723) B2923723
theorem B5197729 : Blo 2051435 5197729 := bstep (se 2 (by rfl) ⟨1949148, by rfl⟩ : syracuseStep 5197729 = 3898297) B3898297
theorem B6930305 : Blo 2051435 6930305 := bstep (se 2 (by rfl) ⟨2598864, by rfl⟩ : syracuseStep 6930305 = 5197729) B5197729
theorem B4620203 : Blo 2051435 4620203 := bstep (se 1 (by rfl) ⟨3465152, by rfl⟩ : syracuseStep 4620203 = 6930305) B6930305
theorem B3080135 : Blo 2051435 3080135 := bstep (se 1 (by rfl) ⟨2310101, by rfl⟩ : syracuseStep 3080135 = 4620203) B4620203
theorem B2053423 : Blo 2051435 2053423 := bstep (se 1 (by rfl) ⟨1540067, by rfl⟩ : syracuseStep 2053423 = 3080135) B3080135
theorem B3080141 : Blo 2051435 3080141 := bbase (se 3 (by rfl) ⟨577526, by rfl⟩ : syracuseStep 3080141 = 1155053) (by norm_num)
theorem B2053427 : Blo 2051435 2053427 := bstep (se 1 (by rfl) ⟨1540070, by rfl⟩ : syracuseStep 2053427 = 3080141) B3080141
theorem B4620221 : Blo 2051435 4620221 := bbase (se 3 (by rfl) ⟨866291, by rfl⟩ : syracuseStep 4620221 = 1732583) (by norm_num)
theorem B3080147 : Blo 2051435 3080147 := bstep (se 1 (by rfl) ⟨2310110, by rfl⟩ : syracuseStep 3080147 = 4620221) B4620221
theorem B2053431 : Blo 2051435 2053431 := bstep (se 1 (by rfl) ⟨1540073, by rfl⟩ : syracuseStep 2053431 = 3080147) B3080147
theorem B3465173 : Blo 2051435 3465173 := bbase (se 7 (by rfl) ⟨40607, by rfl⟩ : syracuseStep 3465173 = 81215) (by norm_num)
theorem B2310115 : Blo 2051435 2310115 := bstep (se 1 (by rfl) ⟨1732586, by rfl⟩ : syracuseStep 2310115 = 3465173) B3465173
theorem B3080153 : Blo 2051435 3080153 := bstep (se 2 (by rfl) ⟨1155057, by rfl⟩ : syracuseStep 3080153 = 2310115) B2310115
theorem B2053435 : Blo 2051435 2053435 := bstep (se 1 (by rfl) ⟨1540076, by rfl⟩ : syracuseStep 2053435 = 3080153) B3080153
theorem C0 (j : ℕ) (h1 : 512858 ≤ j) (h2 : j ≤ 513358) : Blo 2051435 (4 * j + 3) := by
  interval_cases j
  · exact B2051435
  · exact B2051439
  · exact B2051443
  · exact B2051447
  · exact B2051451
  · exact B2051455
  · exact B2051459
  · exact B2051463
  · exact B2051467
  · exact B2051471
  · exact B2051475
  · exact B2051479
  · exact B2051483
  · exact B2051487
  · exact B2051491
  · exact B2051495
  · exact B2051499
  · exact B2051503
  · exact B2051507
  · exact B2051511
  · exact B2051515
  · exact B2051519
  · exact B2051523
  · exact B2051527
  · exact B2051531
  · exact B2051535
  · exact B2051539
  · exact B2051543
  · exact B2051547
  · exact B2051551
  · exact B2051555
  · exact B2051559
  · exact B2051563
  · exact B2051567
  · exact B2051571
  · exact B2051575
  · exact B2051579
  · exact B2051583
  · exact B2051587
  · exact B2051591
  · exact B2051595
  · exact B2051599
  · exact B2051603
  · exact B2051607
  · exact B2051611
  · exact B2051615
  · exact B2051619
  · exact B2051623
  · exact B2051627
  · exact B2051631
  · exact B2051635
  · exact B2051639
  · exact B2051643
  · exact B2051647
  · exact B2051651
  · exact B2051655
  · exact B2051659
  · exact B2051663
  · exact B2051667
  · exact B2051671
  · exact B2051675
  · exact B2051679
  · exact B2051683
  · exact B2051687
  · exact B2051691
  · exact B2051695
  · exact B2051699
  · exact B2051703
  · exact B2051707
  · exact B2051711
  · exact B2051715
  · exact B2051719
  · exact B2051723
  · exact B2051727
  · exact B2051731
  · exact B2051735
  · exact B2051739
  · exact B2051743
  · exact B2051747
  · exact B2051751
  · exact B2051755
  · exact B2051759
  · exact B2051763
  · exact B2051767
  · exact B2051771
  · exact B2051775
  · exact B2051779
  · exact B2051783
  · exact B2051787
  · exact B2051791
  · exact B2051795
  · exact B2051799
  · exact B2051803
  · exact B2051807
  · exact B2051811
  · exact B2051815
  · exact B2051819
  · exact B2051823
  · exact B2051827
  · exact B2051831
  · exact B2051835
  · exact B2051839
  · exact B2051843
  · exact B2051847
  · exact B2051851
  · exact B2051855
  · exact B2051859
  · exact B2051863
  · exact B2051867
  · exact B2051871
  · exact B2051875
  · exact B2051879
  · exact B2051883
  · exact B2051887
  · exact B2051891
  · exact B2051895
  · exact B2051899
  · exact B2051903
  · exact B2051907
  · exact B2051911
  · exact B2051915
  · exact B2051919
  · exact B2051923
  · exact B2051927
  · exact B2051931
  · exact B2051935
  · exact B2051939
  · exact B2051943
  · exact B2051947
  · exact B2051951
  · exact B2051955
  · exact B2051959
  · exact B2051963
  · exact B2051967
  · exact B2051971
  · exact B2051975
  · exact B2051979
  · exact B2051983
  · exact B2051987
  · exact B2051991
  · exact B2051995
  · exact B2051999
  · exact B2052003
  · exact B2052007
  · exact B2052011
  · exact B2052015
  · exact B2052019
  · exact B2052023
  · exact B2052027
  · exact B2052031
  · exact B2052035
  · exact B2052039
  · exact B2052043
  · exact B2052047
  · exact B2052051
  · exact B2052055
  · exact B2052059
  · exact B2052063
  · exact B2052067
  · exact B2052071
  · exact B2052075
  · exact B2052079
  · exact B2052083
  · exact B2052087
  · exact B2052091
  · exact B2052095
  · exact B2052099
  · exact B2052103
  · exact B2052107
  · exact B2052111
  · exact B2052115
  · exact B2052119
  · exact B2052123
  · exact B2052127
  · exact B2052131
  · exact B2052135
  · exact B2052139
  · exact B2052143
  · exact B2052147
  · exact B2052151
  · exact B2052155
  · exact B2052159
  · exact B2052163
  · exact B2052167
  · exact B2052171
  · exact B2052175
  · exact B2052179
  · exact B2052183
  · exact B2052187
  · exact B2052191
  · exact B2052195
  · exact B2052199
  · exact B2052203
  · exact B2052207
  · exact B2052211
  · exact B2052215
  · exact B2052219
  · exact B2052223
  · exact B2052227
  · exact B2052231
  · exact B2052235
  · exact B2052239
  · exact B2052243
  · exact B2052247
  · exact B2052251
  · exact B2052255
  · exact B2052259
  · exact B2052263
  · exact B2052267
  · exact B2052271
  · exact B2052275
  · exact B2052279
  · exact B2052283
  · exact B2052287
  · exact B2052291
  · exact B2052295
  · exact B2052299
  · exact B2052303
  · exact B2052307
  · exact B2052311
  · exact B2052315
  · exact B2052319
  · exact B2052323
  · exact B2052327
  · exact B2052331
  · exact B2052335
  · exact B2052339
  · exact B2052343
  · exact B2052347
  · exact B2052351
  · exact B2052355
  · exact B2052359
  · exact B2052363
  · exact B2052367
  · exact B2052371
  · exact B2052375
  · exact B2052379
  · exact B2052383
  · exact B2052387
  · exact B2052391
  · exact B2052395
  · exact B2052399
  · exact B2052403
  · exact B2052407
  · exact B2052411
  · exact B2052415
  · exact B2052419
  · exact B2052423
  · exact B2052427
  · exact B2052431
  · exact B2052435
  · exact B2052439
  · exact B2052443
  · exact B2052447
  · exact B2052451
  · exact B2052455
  · exact B2052459
  · exact B2052463
  · exact B2052467
  · exact B2052471
  · exact B2052475
  · exact B2052479
  · exact B2052483
  · exact B2052487
  · exact B2052491
  · exact B2052495
  · exact B2052499
  · exact B2052503
  · exact B2052507
  · exact B2052511
  · exact B2052515
  · exact B2052519
  · exact B2052523
  · exact B2052527
  · exact B2052531
  · exact B2052535
  · exact B2052539
  · exact B2052543
  · exact B2052547
  · exact B2052551
  · exact B2052555
  · exact B2052559
  · exact B2052563
  · exact B2052567
  · exact B2052571
  · exact B2052575
  · exact B2052579
  · exact B2052583
  · exact B2052587
  · exact B2052591
  · exact B2052595
  · exact B2052599
  · exact B2052603
  · exact B2052607
  · exact B2052611
  · exact B2052615
  · exact B2052619
  · exact B2052623
  · exact B2052627
  · exact B2052631
  · exact B2052635
  · exact B2052639
  · exact B2052643
  · exact B2052647
  · exact B2052651
  · exact B2052655
  · exact B2052659
  · exact B2052663
  · exact B2052667
  · exact B2052671
  · exact B2052675
  · exact B2052679
  · exact B2052683
  · exact B2052687
  · exact B2052691
  · exact B2052695
  · exact B2052699
  · exact B2052703
  · exact B2052707
  · exact B2052711
  · exact B2052715
  · exact B2052719
  · exact B2052723
  · exact B2052727
  · exact B2052731
  · exact B2052735
  · exact B2052739
  · exact B2052743
  · exact B2052747
  · exact B2052751
  · exact B2052755
  · exact B2052759
  · exact B2052763
  · exact B2052767
  · exact B2052771
  · exact B2052775
  · exact B2052779
  · exact B2052783
  · exact B2052787
  · exact B2052791
  · exact B2052795
  · exact B2052799
  · exact B2052803
  · exact B2052807
  · exact B2052811
  · exact B2052815
  · exact B2052819
  · exact B2052823
  · exact B2052827
  · exact B2052831
  · exact B2052835
  · exact B2052839
  · exact B2052843
  · exact B2052847
  · exact B2052851
  · exact B2052855
  · exact B2052859
  · exact B2052863
  · exact B2052867
  · exact B2052871
  · exact B2052875
  · exact B2052879
  · exact B2052883
  · exact B2052887
  · exact B2052891
  · exact B2052895
  · exact B2052899
  · exact B2052903
  · exact B2052907
  · exact B2052911
  · exact B2052915
  · exact B2052919
  · exact B2052923
  · exact B2052927
  · exact B2052931
  · exact B2052935
  · exact B2052939
  · exact B2052943
  · exact B2052947
  · exact B2052951
  · exact B2052955
  · exact B2052959
  · exact B2052963
  · exact B2052967
  · exact B2052971
  · exact B2052975
  · exact B2052979
  · exact B2052983
  · exact B2052987
  · exact B2052991
  · exact B2052995
  · exact B2052999
  · exact B2053003
  · exact B2053007
  · exact B2053011
  · exact B2053015
  · exact B2053019
  · exact B2053023
  · exact B2053027
  · exact B2053031
  · exact B2053035
  · exact B2053039
  · exact B2053043
  · exact B2053047
  · exact B2053051
  · exact B2053055
  · exact B2053059
  · exact B2053063
  · exact B2053067
  · exact B2053071
  · exact B2053075
  · exact B2053079
  · exact B2053083
  · exact B2053087
  · exact B2053091
  · exact B2053095
  · exact B2053099
  · exact B2053103
  · exact B2053107
  · exact B2053111
  · exact B2053115
  · exact B2053119
  · exact B2053123
  · exact B2053127
  · exact B2053131
  · exact B2053135
  · exact B2053139
  · exact B2053143
  · exact B2053147
  · exact B2053151
  · exact B2053155
  · exact B2053159
  · exact B2053163
  · exact B2053167
  · exact B2053171
  · exact B2053175
  · exact B2053179
  · exact B2053183
  · exact B2053187
  · exact B2053191
  · exact B2053195
  · exact B2053199
  · exact B2053203
  · exact B2053207
  · exact B2053211
  · exact B2053215
  · exact B2053219
  · exact B2053223
  · exact B2053227
  · exact B2053231
  · exact B2053235
  · exact B2053239
  · exact B2053243
  · exact B2053247
  · exact B2053251
  · exact B2053255
  · exact B2053259
  · exact B2053263
  · exact B2053267
  · exact B2053271
  · exact B2053275
  · exact B2053279
  · exact B2053283
  · exact B2053287
  · exact B2053291
  · exact B2053295
  · exact B2053299
  · exact B2053303
  · exact B2053307
  · exact B2053311
  · exact B2053315
  · exact B2053319
  · exact B2053323
  · exact B2053327
  · exact B2053331
  · exact B2053335
  · exact B2053339
  · exact B2053343
  · exact B2053347
  · exact B2053351
  · exact B2053355
  · exact B2053359
  · exact B2053363
  · exact B2053367
  · exact B2053371
  · exact B2053375
  · exact B2053379
  · exact B2053383
  · exact B2053387
  · exact B2053391
  · exact B2053395
  · exact B2053399
  · exact B2053403
  · exact B2053407
  · exact B2053411
  · exact B2053415
  · exact B2053419
  · exact B2053423
  · exact B2053427
  · exact B2053431
  · exact B2053435
theorem solution (m : ℕ) (hlo : 2051435 ≤ m) (hhi : m ≤ 2053435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 512858 ≤ j := by omega
    have hj2 : j ≤ 513358 := by omega
    have hb : Blo 2051435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
