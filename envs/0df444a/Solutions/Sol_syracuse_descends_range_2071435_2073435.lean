-- Prove2me | solution 1 for syracuse_descends_range_2071435_2073435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:06.809837+00:00
-- url     : https://prove2.me/submissions/4c5e0eb8-b17d-4845-8873-7338108140e4

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

theorem B2330365 : Blo 2071435 2330365 := bbase (se 3 (by rfl) ⟨436943, by rfl⟩ : syracuseStep 2330365 = 873887) (by norm_num)
theorem B3107153 : Blo 2071435 3107153 := bstep (se 2 (by rfl) ⟨1165182, by rfl⟩ : syracuseStep 3107153 = 2330365) B2330365
theorem B2071435 : Blo 2071435 2071435 := bstep (se 1 (by rfl) ⟨1553576, by rfl⟩ : syracuseStep 2071435 = 3107153) B3107153
theorem B6991109 : Blo 2071435 6991109 := bbase (se 4 (by rfl) ⟨655416, by rfl⟩ : syracuseStep 6991109 = 1310833) (by norm_num)
theorem B4660739 : Blo 2071435 4660739 := bstep (se 1 (by rfl) ⟨3495554, by rfl⟩ : syracuseStep 4660739 = 6991109) B6991109
theorem B3107159 : Blo 2071435 3107159 := bstep (se 1 (by rfl) ⟨2330369, by rfl⟩ : syracuseStep 3107159 = 4660739) B4660739
theorem B2071439 : Blo 2071435 2071439 := bstep (se 1 (by rfl) ⟨1553579, by rfl⟩ : syracuseStep 2071439 = 3107159) B3107159
theorem B3107165 : Blo 2071435 3107165 := bbase (se 3 (by rfl) ⟨582593, by rfl⟩ : syracuseStep 3107165 = 1165187) (by norm_num)
theorem B2071443 : Blo 2071435 2071443 := bstep (se 1 (by rfl) ⟨1553582, by rfl⟩ : syracuseStep 2071443 = 3107165) B3107165
theorem B4660757 : Blo 2071435 4660757 := bbase (se 6 (by rfl) ⟨109236, by rfl⟩ : syracuseStep 4660757 = 218473) (by norm_num)
theorem B3107171 : Blo 2071435 3107171 := bstep (se 1 (by rfl) ⟨2330378, by rfl⟩ : syracuseStep 3107171 = 4660757) B4660757
theorem B2071447 : Blo 2071435 2071447 := bstep (se 1 (by rfl) ⟨1553585, by rfl⟩ : syracuseStep 2071447 = 3107171) B3107171
theorem B7865045 : Blo 2071435 7865045 := bbase (se 7 (by rfl) ⟨92168, by rfl⟩ : syracuseStep 7865045 = 184337) (by norm_num)
theorem B5243363 : Blo 2071435 5243363 := bstep (se 1 (by rfl) ⟨3932522, by rfl⟩ : syracuseStep 5243363 = 7865045) B7865045
theorem B3495575 : Blo 2071435 3495575 := bstep (se 1 (by rfl) ⟨2621681, by rfl⟩ : syracuseStep 3495575 = 5243363) B5243363
theorem B2330383 : Blo 2071435 2330383 := bstep (se 1 (by rfl) ⟨1747787, by rfl⟩ : syracuseStep 2330383 = 3495575) B3495575
theorem B3107177 : Blo 2071435 3107177 := bstep (se 2 (by rfl) ⟨1165191, by rfl⟩ : syracuseStep 3107177 = 2330383) B2330383
theorem B2071451 : Blo 2071435 2071451 := bstep (se 1 (by rfl) ⟨1553588, by rfl⟩ : syracuseStep 2071451 = 3107177) B3107177
theorem B11797589 : Blo 2071435 11797589 := bbase (se 8 (by rfl) ⟨69126, by rfl⟩ : syracuseStep 11797589 = 138253) (by norm_num)
theorem B7865059 : Blo 2071435 7865059 := bstep (se 1 (by rfl) ⟨5898794, by rfl⟩ : syracuseStep 7865059 = 11797589) B11797589
theorem B10486745 : Blo 2071435 10486745 := bstep (se 2 (by rfl) ⟨3932529, by rfl⟩ : syracuseStep 10486745 = 7865059) B7865059
theorem B6991163 : Blo 2071435 6991163 := bstep (se 1 (by rfl) ⟨5243372, by rfl⟩ : syracuseStep 6991163 = 10486745) B10486745
theorem B4660775 : Blo 2071435 4660775 := bstep (se 1 (by rfl) ⟨3495581, by rfl⟩ : syracuseStep 4660775 = 6991163) B6991163
theorem B3107183 : Blo 2071435 3107183 := bstep (se 1 (by rfl) ⟨2330387, by rfl⟩ : syracuseStep 3107183 = 4660775) B4660775
theorem B2071455 : Blo 2071435 2071455 := bstep (se 1 (by rfl) ⟨1553591, by rfl⟩ : syracuseStep 2071455 = 3107183) B3107183
theorem B3107189 : Blo 2071435 3107189 := bbase (se 5 (by rfl) ⟨145649, by rfl⟩ : syracuseStep 3107189 = 291299) (by norm_num)
theorem B2071459 : Blo 2071435 2071459 := bstep (se 1 (by rfl) ⟨1553594, by rfl⟩ : syracuseStep 2071459 = 3107189) B3107189
theorem B2212057 : Blo 2071435 2212057 := bbase (se 2 (by rfl) ⟨829521, by rfl⟩ : syracuseStep 2212057 = 1659043) (by norm_num)
theorem B2949409 : Blo 2071435 2949409 := bstep (se 2 (by rfl) ⟨1106028, by rfl⟩ : syracuseStep 2949409 = 2212057) B2212057
theorem B3932545 : Blo 2071435 3932545 := bstep (se 2 (by rfl) ⟨1474704, by rfl⟩ : syracuseStep 3932545 = 2949409) B2949409
theorem B5243393 : Blo 2071435 5243393 := bstep (se 2 (by rfl) ⟨1966272, by rfl⟩ : syracuseStep 5243393 = 3932545) B3932545
theorem B3495595 : Blo 2071435 3495595 := bstep (se 1 (by rfl) ⟨2621696, by rfl⟩ : syracuseStep 3495595 = 5243393) B5243393
theorem B4660793 : Blo 2071435 4660793 := bstep (se 2 (by rfl) ⟨1747797, by rfl⟩ : syracuseStep 4660793 = 3495595) B3495595
theorem B3107195 : Blo 2071435 3107195 := bstep (se 1 (by rfl) ⟨2330396, by rfl⟩ : syracuseStep 3107195 = 4660793) B4660793
theorem B2071463 : Blo 2071435 2071463 := bstep (se 1 (by rfl) ⟨1553597, by rfl⟩ : syracuseStep 2071463 = 3107195) B3107195
theorem B2330401 : Blo 2071435 2330401 := bbase (se 2 (by rfl) ⟨873900, by rfl⟩ : syracuseStep 2330401 = 1747801) (by norm_num)
theorem B3107201 : Blo 2071435 3107201 := bstep (se 2 (by rfl) ⟨1165200, by rfl⟩ : syracuseStep 3107201 = 2330401) B2330401
theorem B2071467 : Blo 2071435 2071467 := bstep (se 1 (by rfl) ⟨1553600, by rfl⟩ : syracuseStep 2071467 = 3107201) B3107201
theorem B5243413 : Blo 2071435 5243413 := bbase (se 6 (by rfl) ⟨122892, by rfl⟩ : syracuseStep 5243413 = 245785) (by norm_num)
theorem B6991217 : Blo 2071435 6991217 := bstep (se 2 (by rfl) ⟨2621706, by rfl⟩ : syracuseStep 6991217 = 5243413) B5243413
theorem B4660811 : Blo 2071435 4660811 := bstep (se 1 (by rfl) ⟨3495608, by rfl⟩ : syracuseStep 4660811 = 6991217) B6991217
theorem B3107207 : Blo 2071435 3107207 := bstep (se 1 (by rfl) ⟨2330405, by rfl⟩ : syracuseStep 3107207 = 4660811) B4660811
theorem B2071471 : Blo 2071435 2071471 := bstep (se 1 (by rfl) ⟨1553603, by rfl⟩ : syracuseStep 2071471 = 3107207) B3107207
theorem B3107213 : Blo 2071435 3107213 := bbase (se 3 (by rfl) ⟨582602, by rfl⟩ : syracuseStep 3107213 = 1165205) (by norm_num)
theorem B2071475 : Blo 2071435 2071475 := bstep (se 1 (by rfl) ⟨1553606, by rfl⟩ : syracuseStep 2071475 = 3107213) B3107213
theorem B4660829 : Blo 2071435 4660829 := bbase (se 3 (by rfl) ⟨873905, by rfl⟩ : syracuseStep 4660829 = 1747811) (by norm_num)
theorem B3107219 : Blo 2071435 3107219 := bstep (se 1 (by rfl) ⟨2330414, by rfl⟩ : syracuseStep 3107219 = 4660829) B4660829
theorem B2071479 : Blo 2071435 2071479 := bstep (se 1 (by rfl) ⟨1553609, by rfl⟩ : syracuseStep 2071479 = 3107219) B3107219
theorem B3495629 : Blo 2071435 3495629 := bbase (se 3 (by rfl) ⟨655430, by rfl⟩ : syracuseStep 3495629 = 1310861) (by norm_num)
theorem B2330419 : Blo 2071435 2330419 := bstep (se 1 (by rfl) ⟨1747814, by rfl⟩ : syracuseStep 2330419 = 3495629) B3495629
theorem B3107225 : Blo 2071435 3107225 := bstep (se 2 (by rfl) ⟨1165209, by rfl⟩ : syracuseStep 3107225 = 2330419) B2330419
theorem B2071483 : Blo 2071435 2071483 := bstep (se 1 (by rfl) ⟨1553612, by rfl⟩ : syracuseStep 2071483 = 3107225) B3107225
theorem B4199501 : Blo 2071435 4199501 := bbase (se 3 (by rfl) ⟨787406, by rfl⟩ : syracuseStep 4199501 = 1574813) (by norm_num)
theorem B2799667 : Blo 2071435 2799667 := bstep (se 1 (by rfl) ⟨2099750, by rfl⟩ : syracuseStep 2799667 = 4199501) B4199501
theorem B3732889 : Blo 2071435 3732889 := bstep (se 2 (by rfl) ⟨1399833, by rfl⟩ : syracuseStep 3732889 = 2799667) B2799667
theorem B4977185 : Blo 2071435 4977185 := bstep (se 2 (by rfl) ⟨1866444, by rfl⟩ : syracuseStep 4977185 = 3732889) B3732889
theorem B13272493 : Blo 2071435 13272493 := bstep (se 3 (by rfl) ⟨2488592, by rfl⟩ : syracuseStep 13272493 = 4977185) B4977185
theorem B17696657 : Blo 2071435 17696657 := bstep (se 2 (by rfl) ⟨6636246, by rfl⟩ : syracuseStep 17696657 = 13272493) B13272493
theorem B11797771 : Blo 2071435 11797771 := bstep (se 1 (by rfl) ⟨8848328, by rfl⟩ : syracuseStep 11797771 = 17696657) B17696657
theorem B15730361 : Blo 2071435 15730361 := bstep (se 2 (by rfl) ⟨5898885, by rfl⟩ : syracuseStep 15730361 = 11797771) B11797771
theorem B10486907 : Blo 2071435 10486907 := bstep (se 1 (by rfl) ⟨7865180, by rfl⟩ : syracuseStep 10486907 = 15730361) B15730361
theorem B6991271 : Blo 2071435 6991271 := bstep (se 1 (by rfl) ⟨5243453, by rfl⟩ : syracuseStep 6991271 = 10486907) B10486907
theorem B4660847 : Blo 2071435 4660847 := bstep (se 1 (by rfl) ⟨3495635, by rfl⟩ : syracuseStep 4660847 = 6991271) B6991271
theorem B3107231 : Blo 2071435 3107231 := bstep (se 1 (by rfl) ⟨2330423, by rfl⟩ : syracuseStep 3107231 = 4660847) B4660847
theorem B2071487 : Blo 2071435 2071487 := bstep (se 1 (by rfl) ⟨1553615, by rfl⟩ : syracuseStep 2071487 = 3107231) B3107231
theorem B3107237 : Blo 2071435 3107237 := bbase (se 4 (by rfl) ⟨291303, by rfl⟩ : syracuseStep 3107237 = 582607) (by norm_num)
theorem B2071491 : Blo 2071435 2071491 := bstep (se 1 (by rfl) ⟨1553618, by rfl⟩ : syracuseStep 2071491 = 3107237) B3107237
theorem B2621737 : Blo 2071435 2621737 := bbase (se 2 (by rfl) ⟨983151, by rfl⟩ : syracuseStep 2621737 = 1966303) (by norm_num)
theorem B3495649 : Blo 2071435 3495649 := bstep (se 2 (by rfl) ⟨1310868, by rfl⟩ : syracuseStep 3495649 = 2621737) B2621737
theorem B4660865 : Blo 2071435 4660865 := bstep (se 2 (by rfl) ⟨1747824, by rfl⟩ : syracuseStep 4660865 = 3495649) B3495649
theorem B3107243 : Blo 2071435 3107243 := bstep (se 1 (by rfl) ⟨2330432, by rfl⟩ : syracuseStep 3107243 = 4660865) B4660865
theorem B2071495 : Blo 2071435 2071495 := bstep (se 1 (by rfl) ⟨1553621, by rfl⟩ : syracuseStep 2071495 = 3107243) B3107243
theorem B2330437 : Blo 2071435 2330437 := bbase (se 4 (by rfl) ⟨218478, by rfl⟩ : syracuseStep 2330437 = 436957) (by norm_num)
theorem B3107249 : Blo 2071435 3107249 := bstep (se 2 (by rfl) ⟨1165218, by rfl⟩ : syracuseStep 3107249 = 2330437) B2330437
theorem B2071499 : Blo 2071435 2071499 := bstep (se 1 (by rfl) ⟨1553624, by rfl⟩ : syracuseStep 2071499 = 3107249) B3107249
theorem B3932621 : Blo 2071435 3932621 := bbase (se 3 (by rfl) ⟨737366, by rfl⟩ : syracuseStep 3932621 = 1474733) (by norm_num)
theorem B2621747 : Blo 2071435 2621747 := bstep (se 1 (by rfl) ⟨1966310, by rfl⟩ : syracuseStep 2621747 = 3932621) B3932621
theorem B6991325 : Blo 2071435 6991325 := bstep (se 3 (by rfl) ⟨1310873, by rfl⟩ : syracuseStep 6991325 = 2621747) B2621747
theorem B4660883 : Blo 2071435 4660883 := bstep (se 1 (by rfl) ⟨3495662, by rfl⟩ : syracuseStep 4660883 = 6991325) B6991325
theorem B3107255 : Blo 2071435 3107255 := bstep (se 1 (by rfl) ⟨2330441, by rfl⟩ : syracuseStep 3107255 = 4660883) B4660883
theorem B2071503 : Blo 2071435 2071503 := bstep (se 1 (by rfl) ⟨1553627, by rfl⟩ : syracuseStep 2071503 = 3107255) B3107255
theorem B3107261 : Blo 2071435 3107261 := bbase (se 3 (by rfl) ⟨582611, by rfl⟩ : syracuseStep 3107261 = 1165223) (by norm_num)
theorem B2071507 : Blo 2071435 2071507 := bstep (se 1 (by rfl) ⟨1553630, by rfl⟩ : syracuseStep 2071507 = 3107261) B3107261
theorem B4660901 : Blo 2071435 4660901 := bbase (se 4 (by rfl) ⟨436959, by rfl⟩ : syracuseStep 4660901 = 873919) (by norm_num)
theorem B3107267 : Blo 2071435 3107267 := bstep (se 1 (by rfl) ⟨2330450, by rfl⟩ : syracuseStep 3107267 = 4660901) B4660901
theorem B2071511 : Blo 2071435 2071511 := bstep (se 1 (by rfl) ⟨1553633, by rfl⟩ : syracuseStep 2071511 = 3107267) B3107267
theorem B5243525 : Blo 2071435 5243525 := bbase (se 4 (by rfl) ⟨491580, by rfl⟩ : syracuseStep 5243525 = 983161) (by norm_num)
theorem B3495683 : Blo 2071435 3495683 := bstep (se 1 (by rfl) ⟨2621762, by rfl⟩ : syracuseStep 3495683 = 5243525) B5243525
theorem B2330455 : Blo 2071435 2330455 := bstep (se 1 (by rfl) ⟨1747841, by rfl⟩ : syracuseStep 2330455 = 3495683) B3495683
theorem B3107273 : Blo 2071435 3107273 := bstep (se 2 (by rfl) ⟨1165227, by rfl⟩ : syracuseStep 3107273 = 2330455) B2330455
theorem B2071515 : Blo 2071435 2071515 := bstep (se 1 (by rfl) ⟨1553636, by rfl⟩ : syracuseStep 2071515 = 3107273) B3107273
theorem B2837909 : Blo 2071435 2837909 := bbase (se 6 (by rfl) ⟨66513, by rfl⟩ : syracuseStep 2837909 = 133027) (by norm_num)
theorem B7567757 : Blo 2071435 7567757 := bstep (se 3 (by rfl) ⟨1418954, by rfl⟩ : syracuseStep 7567757 = 2837909) B2837909
theorem B5045171 : Blo 2071435 5045171 := bstep (se 1 (by rfl) ⟨3783878, by rfl⟩ : syracuseStep 5045171 = 7567757) B7567757
theorem B13453789 : Blo 2071435 13453789 := bstep (se 3 (by rfl) ⟨2522585, by rfl⟩ : syracuseStep 13453789 = 5045171) B5045171
theorem B17938385 : Blo 2071435 17938385 := bstep (se 2 (by rfl) ⟨6726894, by rfl⟩ : syracuseStep 17938385 = 13453789) B13453789
theorem B11958923 : Blo 2071435 11958923 := bstep (se 1 (by rfl) ⟨8969192, by rfl⟩ : syracuseStep 11958923 = 17938385) B17938385
theorem B7972615 : Blo 2071435 7972615 := bstep (se 1 (by rfl) ⟨5979461, by rfl⟩ : syracuseStep 7972615 = 11958923) B11958923
theorem B10630153 : Blo 2071435 10630153 := bstep (se 2 (by rfl) ⟨3986307, by rfl⟩ : syracuseStep 10630153 = 7972615) B7972615
theorem B14173537 : Blo 2071435 14173537 := bstep (se 2 (by rfl) ⟨5315076, by rfl⟩ : syracuseStep 14173537 = 10630153) B10630153
theorem B18898049 : Blo 2071435 18898049 := bstep (se 2 (by rfl) ⟨7086768, by rfl⟩ : syracuseStep 18898049 = 14173537) B14173537
theorem B12598699 : Blo 2071435 12598699 := bstep (se 1 (by rfl) ⟨9449024, by rfl⟩ : syracuseStep 12598699 = 18898049) B18898049
theorem B16798265 : Blo 2071435 16798265 := bstep (se 2 (by rfl) ⟨6299349, by rfl⟩ : syracuseStep 16798265 = 12598699) B12598699
theorem B11198843 : Blo 2071435 11198843 := bstep (se 1 (by rfl) ⟨8399132, by rfl⟩ : syracuseStep 11198843 = 16798265) B16798265
theorem B7465895 : Blo 2071435 7465895 := bstep (se 1 (by rfl) ⟨5599421, by rfl⟩ : syracuseStep 7465895 = 11198843) B11198843
theorem B4977263 : Blo 2071435 4977263 := bstep (se 1 (by rfl) ⟨3732947, by rfl⟩ : syracuseStep 4977263 = 7465895) B7465895
theorem B3318175 : Blo 2071435 3318175 := bstep (se 1 (by rfl) ⟨2488631, by rfl⟩ : syracuseStep 3318175 = 4977263) B4977263
theorem B4424233 : Blo 2071435 4424233 := bstep (se 2 (by rfl) ⟨1659087, by rfl⟩ : syracuseStep 4424233 = 3318175) B3318175
theorem B5898977 : Blo 2071435 5898977 := bstep (se 2 (by rfl) ⟨2212116, by rfl⟩ : syracuseStep 5898977 = 4424233) B4424233
theorem B3932651 : Blo 2071435 3932651 := bstep (se 1 (by rfl) ⟨2949488, by rfl⟩ : syracuseStep 3932651 = 5898977) B5898977
theorem B10487069 : Blo 2071435 10487069 := bstep (se 3 (by rfl) ⟨1966325, by rfl⟩ : syracuseStep 10487069 = 3932651) B3932651
theorem B6991379 : Blo 2071435 6991379 := bstep (se 1 (by rfl) ⟨5243534, by rfl⟩ : syracuseStep 6991379 = 10487069) B10487069
theorem B4660919 : Blo 2071435 4660919 := bstep (se 1 (by rfl) ⟨3495689, by rfl⟩ : syracuseStep 4660919 = 6991379) B6991379
theorem B3107279 : Blo 2071435 3107279 := bstep (se 1 (by rfl) ⟨2330459, by rfl⟩ : syracuseStep 3107279 = 4660919) B4660919
theorem B2071519 : Blo 2071435 2071519 := bstep (se 1 (by rfl) ⟨1553639, by rfl⟩ : syracuseStep 2071519 = 3107279) B3107279
theorem B3107285 : Blo 2071435 3107285 := bbase (se 7 (by rfl) ⟨36413, by rfl⟩ : syracuseStep 3107285 = 72827) (by norm_num)
theorem B2071523 : Blo 2071435 2071523 := bstep (se 1 (by rfl) ⟨1553642, by rfl⟩ : syracuseStep 2071523 = 3107285) B3107285
theorem B7865333 : Blo 2071435 7865333 := bbase (se 5 (by rfl) ⟨368687, by rfl⟩ : syracuseStep 7865333 = 737375) (by norm_num)
theorem B5243555 : Blo 2071435 5243555 := bstep (se 1 (by rfl) ⟨3932666, by rfl⟩ : syracuseStep 5243555 = 7865333) B7865333
theorem B3495703 : Blo 2071435 3495703 := bstep (se 1 (by rfl) ⟨2621777, by rfl⟩ : syracuseStep 3495703 = 5243555) B5243555
theorem B4660937 : Blo 2071435 4660937 := bstep (se 2 (by rfl) ⟨1747851, by rfl⟩ : syracuseStep 4660937 = 3495703) B3495703
theorem B3107291 : Blo 2071435 3107291 := bstep (se 1 (by rfl) ⟨2330468, by rfl⟩ : syracuseStep 3107291 = 4660937) B4660937
theorem B2071527 : Blo 2071435 2071527 := bstep (se 1 (by rfl) ⟨1553645, by rfl⟩ : syracuseStep 2071527 = 3107291) B3107291
theorem B2330473 : Blo 2071435 2330473 := bbase (se 2 (by rfl) ⟨873927, by rfl⟩ : syracuseStep 2330473 = 1747855) (by norm_num)
theorem B3107297 : Blo 2071435 3107297 := bstep (se 2 (by rfl) ⟨1165236, by rfl⟩ : syracuseStep 3107297 = 2330473) B2330473
theorem B2071531 : Blo 2071435 2071531 := bstep (se 1 (by rfl) ⟨1553648, by rfl⟩ : syracuseStep 2071531 = 3107297) B3107297
theorem B4977301 : Blo 2071435 4977301 := bbase (se 6 (by rfl) ⟨116655, by rfl⟩ : syracuseStep 4977301 = 233311) (by norm_num)
theorem B6636401 : Blo 2071435 6636401 := bstep (se 2 (by rfl) ⟨2488650, by rfl⟩ : syracuseStep 6636401 = 4977301) B4977301
theorem B4424267 : Blo 2071435 4424267 := bstep (se 1 (by rfl) ⟨3318200, by rfl⟩ : syracuseStep 4424267 = 6636401) B6636401
theorem B11798045 : Blo 2071435 11798045 := bstep (se 3 (by rfl) ⟨2212133, by rfl⟩ : syracuseStep 11798045 = 4424267) B4424267
theorem B7865363 : Blo 2071435 7865363 := bstep (se 1 (by rfl) ⟨5899022, by rfl⟩ : syracuseStep 7865363 = 11798045) B11798045
theorem B5243575 : Blo 2071435 5243575 := bstep (se 1 (by rfl) ⟨3932681, by rfl⟩ : syracuseStep 5243575 = 7865363) B7865363
theorem B6991433 : Blo 2071435 6991433 := bstep (se 2 (by rfl) ⟨2621787, by rfl⟩ : syracuseStep 6991433 = 5243575) B5243575
theorem B4660955 : Blo 2071435 4660955 := bstep (se 1 (by rfl) ⟨3495716, by rfl⟩ : syracuseStep 4660955 = 6991433) B6991433
theorem B3107303 : Blo 2071435 3107303 := bstep (se 1 (by rfl) ⟨2330477, by rfl⟩ : syracuseStep 3107303 = 4660955) B4660955
theorem B2071535 : Blo 2071435 2071535 := bstep (se 1 (by rfl) ⟨1553651, by rfl⟩ : syracuseStep 2071535 = 3107303) B3107303
theorem B3107309 : Blo 2071435 3107309 := bbase (se 3 (by rfl) ⟨582620, by rfl⟩ : syracuseStep 3107309 = 1165241) (by norm_num)
theorem B2071539 : Blo 2071435 2071539 := bstep (se 1 (by rfl) ⟨1553654, by rfl⟩ : syracuseStep 2071539 = 3107309) B3107309
theorem B4660973 : Blo 2071435 4660973 := bbase (se 3 (by rfl) ⟨873932, by rfl⟩ : syracuseStep 4660973 = 1747865) (by norm_num)
theorem B3107315 : Blo 2071435 3107315 := bstep (se 1 (by rfl) ⟨2330486, by rfl⟩ : syracuseStep 3107315 = 4660973) B4660973
theorem B2071543 : Blo 2071435 2071543 := bstep (se 1 (by rfl) ⟨1553657, by rfl⟩ : syracuseStep 2071543 = 3107315) B3107315
theorem B3318221 : Blo 2071435 3318221 := bbase (se 3 (by rfl) ⟨622166, by rfl⟩ : syracuseStep 3318221 = 1244333) (by norm_num)
theorem B2212147 : Blo 2071435 2212147 := bstep (se 1 (by rfl) ⟨1659110, by rfl⟩ : syracuseStep 2212147 = 3318221) B3318221
theorem B2949529 : Blo 2071435 2949529 := bstep (se 2 (by rfl) ⟨1106073, by rfl⟩ : syracuseStep 2949529 = 2212147) B2212147
theorem B3932705 : Blo 2071435 3932705 := bstep (se 2 (by rfl) ⟨1474764, by rfl⟩ : syracuseStep 3932705 = 2949529) B2949529
theorem B2621803 : Blo 2071435 2621803 := bstep (se 1 (by rfl) ⟨1966352, by rfl⟩ : syracuseStep 2621803 = 3932705) B3932705
theorem B3495737 : Blo 2071435 3495737 := bstep (se 2 (by rfl) ⟨1310901, by rfl⟩ : syracuseStep 3495737 = 2621803) B2621803
theorem B2330491 : Blo 2071435 2330491 := bstep (se 1 (by rfl) ⟨1747868, by rfl⟩ : syracuseStep 2330491 = 3495737) B3495737
theorem B3107321 : Blo 2071435 3107321 := bstep (se 2 (by rfl) ⟨1165245, by rfl⟩ : syracuseStep 3107321 = 2330491) B2330491
theorem B2071547 : Blo 2071435 2071547 := bstep (se 1 (by rfl) ⟨1553660, by rfl⟩ : syracuseStep 2071547 = 3107321) B3107321
theorem B3740813 : Blo 2071435 3740813 := bbase (se 3 (by rfl) ⟨701402, by rfl⟩ : syracuseStep 3740813 = 1402805) (by norm_num)
theorem B2493875 : Blo 2071435 2493875 := bstep (se 1 (by rfl) ⟨1870406, by rfl⟩ : syracuseStep 2493875 = 3740813) B3740813
theorem B6650333 : Blo 2071435 6650333 := bstep (se 3 (by rfl) ⟨1246937, by rfl⟩ : syracuseStep 6650333 = 2493875) B2493875
theorem B4433555 : Blo 2071435 4433555 := bstep (se 1 (by rfl) ⟨3325166, by rfl⟩ : syracuseStep 4433555 = 6650333) B6650333
theorem B2955703 : Blo 2071435 2955703 := bstep (se 1 (by rfl) ⟨2216777, by rfl⟩ : syracuseStep 2955703 = 4433555) B4433555
theorem B3940937 : Blo 2071435 3940937 := bstep (se 2 (by rfl) ⟨1477851, by rfl⟩ : syracuseStep 3940937 = 2955703) B2955703
theorem B42036661 : Blo 2071435 42036661 := bstep (se 5 (by rfl) ⟨1970468, by rfl⟩ : syracuseStep 42036661 = 3940937) B3940937
theorem B56048881 : Blo 2071435 56048881 := bstep (se 2 (by rfl) ⟨21018330, by rfl⟩ : syracuseStep 56048881 = 42036661) B42036661
theorem B74731841 : Blo 2071435 74731841 := bstep (se 2 (by rfl) ⟨28024440, by rfl⟩ : syracuseStep 74731841 = 56048881) B56048881
theorem B49821227 : Blo 2071435 49821227 := bstep (se 1 (by rfl) ⟨37365920, by rfl⟩ : syracuseStep 49821227 = 74731841) B74731841
theorem B33214151 : Blo 2071435 33214151 := bstep (se 1 (by rfl) ⟨24910613, by rfl⟩ : syracuseStep 33214151 = 49821227) B49821227
theorem B22142767 : Blo 2071435 22142767 := bstep (se 1 (by rfl) ⟨16607075, by rfl⟩ : syracuseStep 22142767 = 33214151) B33214151
theorem B29523689 : Blo 2071435 29523689 := bstep (se 2 (by rfl) ⟨11071383, by rfl⟩ : syracuseStep 29523689 = 22142767) B22142767
theorem B19682459 : Blo 2071435 19682459 := bstep (se 1 (by rfl) ⟨14761844, by rfl⟩ : syracuseStep 19682459 = 29523689) B29523689
theorem B13121639 : Blo 2071435 13121639 := bstep (se 1 (by rfl) ⟨9841229, by rfl⟩ : syracuseStep 13121639 = 19682459) B19682459
theorem B8747759 : Blo 2071435 8747759 := bstep (se 1 (by rfl) ⟨6560819, by rfl⟩ : syracuseStep 8747759 = 13121639) B13121639
theorem B5831839 : Blo 2071435 5831839 := bstep (se 1 (by rfl) ⟨4373879, by rfl⟩ : syracuseStep 5831839 = 8747759) B8747759
theorem B7775785 : Blo 2071435 7775785 := bstep (se 2 (by rfl) ⟨2915919, by rfl⟩ : syracuseStep 7775785 = 5831839) B5831839
theorem B10367713 : Blo 2071435 10367713 := bstep (se 2 (by rfl) ⟨3887892, by rfl⟩ : syracuseStep 10367713 = 7775785) B7775785
theorem B13823617 : Blo 2071435 13823617 := bstep (se 2 (by rfl) ⟨5183856, by rfl⟩ : syracuseStep 13823617 = 10367713) B10367713
theorem B18431489 : Blo 2071435 18431489 := bstep (se 2 (by rfl) ⟨6911808, by rfl⟩ : syracuseStep 18431489 = 13823617) B13823617
theorem B12287659 : Blo 2071435 12287659 := bstep (se 1 (by rfl) ⟨9215744, by rfl⟩ : syracuseStep 12287659 = 18431489) B18431489
theorem B16383545 : Blo 2071435 16383545 := bstep (se 2 (by rfl) ⟨6143829, by rfl⟩ : syracuseStep 16383545 = 12287659) B12287659
theorem B10922363 : Blo 2071435 10922363 := bstep (se 1 (by rfl) ⟨8191772, by rfl⟩ : syracuseStep 10922363 = 16383545) B16383545
theorem B7281575 : Blo 2071435 7281575 := bstep (se 1 (by rfl) ⟨5461181, by rfl⟩ : syracuseStep 7281575 = 10922363) B10922363
theorem B4854383 : Blo 2071435 4854383 := bstep (se 1 (by rfl) ⟨3640787, by rfl⟩ : syracuseStep 4854383 = 7281575) B7281575
theorem B3236255 : Blo 2071435 3236255 := bstep (se 1 (by rfl) ⟨2427191, by rfl⟩ : syracuseStep 3236255 = 4854383) B4854383
theorem B34520053 : Blo 2071435 34520053 := bstep (se 5 (by rfl) ⟨1618127, by rfl⟩ : syracuseStep 34520053 = 3236255) B3236255
theorem B46026737 : Blo 2071435 46026737 := bstep (se 2 (by rfl) ⟨17260026, by rfl⟩ : syracuseStep 46026737 = 34520053) B34520053
theorem B30684491 : Blo 2071435 30684491 := bstep (se 1 (by rfl) ⟨23013368, by rfl⟩ : syracuseStep 30684491 = 46026737) B46026737
theorem B20456327 : Blo 2071435 20456327 := bstep (se 1 (by rfl) ⟨15342245, by rfl⟩ : syracuseStep 20456327 = 30684491) B30684491
theorem B54550205 : Blo 2071435 54550205 := bstep (se 3 (by rfl) ⟨10228163, by rfl⟩ : syracuseStep 54550205 = 20456327) B20456327
theorem B36366803 : Blo 2071435 36366803 := bstep (se 1 (by rfl) ⟨27275102, by rfl⟩ : syracuseStep 36366803 = 54550205) B54550205
theorem B24244535 : Blo 2071435 24244535 := bstep (se 1 (by rfl) ⟨18183401, by rfl⟩ : syracuseStep 24244535 = 36366803) B36366803
theorem B64652093 : Blo 2071435 64652093 := bstep (se 3 (by rfl) ⟨12122267, by rfl⟩ : syracuseStep 64652093 = 24244535) B24244535
theorem B43101395 : Blo 2071435 43101395 := bstep (se 1 (by rfl) ⟨32326046, by rfl⟩ : syracuseStep 43101395 = 64652093) B64652093
theorem B28734263 : Blo 2071435 28734263 := bstep (se 1 (by rfl) ⟨21550697, by rfl⟩ : syracuseStep 28734263 = 43101395) B43101395
theorem B19156175 : Blo 2071435 19156175 := bstep (se 1 (by rfl) ⟨14367131, by rfl⟩ : syracuseStep 19156175 = 28734263) B28734263
theorem B12770783 : Blo 2071435 12770783 := bstep (se 1 (by rfl) ⟨9578087, by rfl⟩ : syracuseStep 12770783 = 19156175) B19156175
theorem B8513855 : Blo 2071435 8513855 := bstep (se 1 (by rfl) ⟨6385391, by rfl⟩ : syracuseStep 8513855 = 12770783) B12770783
theorem B5675903 : Blo 2071435 5675903 := bstep (se 1 (by rfl) ⟨4256927, by rfl⟩ : syracuseStep 5675903 = 8513855) B8513855
theorem B3783935 : Blo 2071435 3783935 := bstep (se 1 (by rfl) ⟨2837951, by rfl⟩ : syracuseStep 3783935 = 5675903) B5675903
theorem B10090493 : Blo 2071435 10090493 := bstep (se 3 (by rfl) ⟨1891967, by rfl⟩ : syracuseStep 10090493 = 3783935) B3783935
theorem B6726995 : Blo 2071435 6726995 := bstep (se 1 (by rfl) ⟨5045246, by rfl⟩ : syracuseStep 6726995 = 10090493) B10090493
theorem B4484663 : Blo 2071435 4484663 := bstep (se 1 (by rfl) ⟨3363497, by rfl⟩ : syracuseStep 4484663 = 6726995) B6726995
theorem B47836405 : Blo 2071435 47836405 := bstep (se 5 (by rfl) ⟨2242331, by rfl⟩ : syracuseStep 47836405 = 4484663) B4484663
theorem B63781873 : Blo 2071435 63781873 := bstep (se 2 (by rfl) ⟨23918202, by rfl⟩ : syracuseStep 63781873 = 47836405) B47836405
theorem B340169989 : Blo 2071435 340169989 := bstep (se 4 (by rfl) ⟨31890936, by rfl⟩ : syracuseStep 340169989 = 63781873) B63781873
theorem B453559985 : Blo 2071435 453559985 := bstep (se 2 (by rfl) ⟨170084994, by rfl⟩ : syracuseStep 453559985 = 340169989) B340169989
theorem B302373323 : Blo 2071435 302373323 := bstep (se 1 (by rfl) ⟨226779992, by rfl⟩ : syracuseStep 302373323 = 453559985) B453559985
theorem B201582215 : Blo 2071435 201582215 := bstep (se 1 (by rfl) ⟨151186661, by rfl⟩ : syracuseStep 201582215 = 302373323) B302373323
theorem B134388143 : Blo 2071435 134388143 := bstep (se 1 (by rfl) ⟨100791107, by rfl⟩ : syracuseStep 134388143 = 201582215) B201582215
theorem B89592095 : Blo 2071435 89592095 := bstep (se 1 (by rfl) ⟨67194071, by rfl⟩ : syracuseStep 89592095 = 134388143) B134388143
theorem B59728063 : Blo 2071435 59728063 := bstep (se 1 (by rfl) ⟨44796047, by rfl⟩ : syracuseStep 59728063 = 89592095) B89592095
theorem B79637417 : Blo 2071435 79637417 := bstep (se 2 (by rfl) ⟨29864031, by rfl⟩ : syracuseStep 79637417 = 59728063) B59728063
theorem B53091611 : Blo 2071435 53091611 := bstep (se 1 (by rfl) ⟨39818708, by rfl⟩ : syracuseStep 53091611 = 79637417) B79637417
theorem B35394407 : Blo 2071435 35394407 := bstep (se 1 (by rfl) ⟨26545805, by rfl⟩ : syracuseStep 35394407 = 53091611) B53091611
theorem B23596271 : Blo 2071435 23596271 := bstep (se 1 (by rfl) ⟨17697203, by rfl⟩ : syracuseStep 23596271 = 35394407) B35394407
theorem B15730847 : Blo 2071435 15730847 := bstep (se 1 (by rfl) ⟨11798135, by rfl⟩ : syracuseStep 15730847 = 23596271) B23596271
theorem B10487231 : Blo 2071435 10487231 := bstep (se 1 (by rfl) ⟨7865423, by rfl⟩ : syracuseStep 10487231 = 15730847) B15730847
theorem B6991487 : Blo 2071435 6991487 := bstep (se 1 (by rfl) ⟨5243615, by rfl⟩ : syracuseStep 6991487 = 10487231) B10487231
theorem B4660991 : Blo 2071435 4660991 := bstep (se 1 (by rfl) ⟨3495743, by rfl⟩ : syracuseStep 4660991 = 6991487) B6991487
theorem B3107327 : Blo 2071435 3107327 := bstep (se 1 (by rfl) ⟨2330495, by rfl⟩ : syracuseStep 3107327 = 4660991) B4660991
theorem B2071551 : Blo 2071435 2071551 := bstep (se 1 (by rfl) ⟨1553663, by rfl⟩ : syracuseStep 2071551 = 3107327) B3107327
theorem B3107333 : Blo 2071435 3107333 := bbase (se 4 (by rfl) ⟨291312, by rfl⟩ : syracuseStep 3107333 = 582625) (by norm_num)
theorem B2071555 : Blo 2071435 2071555 := bstep (se 1 (by rfl) ⟨1553666, by rfl⟩ : syracuseStep 2071555 = 3107333) B3107333
theorem B3495757 : Blo 2071435 3495757 := bbase (se 3 (by rfl) ⟨655454, by rfl⟩ : syracuseStep 3495757 = 1310909) (by norm_num)
theorem B4661009 : Blo 2071435 4661009 := bstep (se 2 (by rfl) ⟨1747878, by rfl⟩ : syracuseStep 4661009 = 3495757) B3495757
theorem B3107339 : Blo 2071435 3107339 := bstep (se 1 (by rfl) ⟨2330504, by rfl⟩ : syracuseStep 3107339 = 4661009) B4661009
theorem B2071559 : Blo 2071435 2071559 := bstep (se 1 (by rfl) ⟨1553669, by rfl⟩ : syracuseStep 2071559 = 3107339) B3107339
theorem B2330509 : Blo 2071435 2330509 := bbase (se 3 (by rfl) ⟨436970, by rfl⟩ : syracuseStep 2330509 = 873941) (by norm_num)
theorem B3107345 : Blo 2071435 3107345 := bstep (se 2 (by rfl) ⟨1165254, by rfl⟩ : syracuseStep 3107345 = 2330509) B2330509
theorem B2071563 : Blo 2071435 2071563 := bstep (se 1 (by rfl) ⟨1553672, by rfl⟩ : syracuseStep 2071563 = 3107345) B3107345
theorem B6991541 : Blo 2071435 6991541 := bbase (se 5 (by rfl) ⟨327728, by rfl⟩ : syracuseStep 6991541 = 655457) (by norm_num)
theorem B4661027 : Blo 2071435 4661027 := bstep (se 1 (by rfl) ⟨3495770, by rfl⟩ : syracuseStep 4661027 = 6991541) B6991541
theorem B3107351 : Blo 2071435 3107351 := bstep (se 1 (by rfl) ⟨2330513, by rfl⟩ : syracuseStep 3107351 = 4661027) B4661027
theorem B2071567 : Blo 2071435 2071567 := bstep (se 1 (by rfl) ⟨1553675, by rfl⟩ : syracuseStep 2071567 = 3107351) B3107351
theorem B3107357 : Blo 2071435 3107357 := bbase (se 3 (by rfl) ⟨582629, by rfl⟩ : syracuseStep 3107357 = 1165259) (by norm_num)
theorem B2071571 : Blo 2071435 2071571 := bstep (se 1 (by rfl) ⟨1553678, by rfl⟩ : syracuseStep 2071571 = 3107357) B3107357
theorem B4661045 : Blo 2071435 4661045 := bbase (se 5 (by rfl) ⟨218486, by rfl⟩ : syracuseStep 4661045 = 436973) (by norm_num)
theorem B3107363 : Blo 2071435 3107363 := bstep (se 1 (by rfl) ⟨2330522, by rfl⟩ : syracuseStep 3107363 = 4661045) B4661045
theorem B2071575 : Blo 2071435 2071575 := bstep (se 1 (by rfl) ⟨1553681, by rfl⟩ : syracuseStep 2071575 = 3107363) B3107363
theorem B4789109 : Blo 2071435 4789109 := bbase (se 5 (by rfl) ⟨224489, by rfl⟩ : syracuseStep 4789109 = 448979) (by norm_num)
theorem B12770957 : Blo 2071435 12770957 := bstep (se 3 (by rfl) ⟨2394554, by rfl⟩ : syracuseStep 12770957 = 4789109) B4789109
theorem B34055885 : Blo 2071435 34055885 := bstep (se 3 (by rfl) ⟨6385478, by rfl⟩ : syracuseStep 34055885 = 12770957) B12770957
theorem B22703923 : Blo 2071435 22703923 := bstep (se 1 (by rfl) ⟨17027942, by rfl⟩ : syracuseStep 22703923 = 34055885) B34055885
theorem B30271897 : Blo 2071435 30271897 := bstep (se 2 (by rfl) ⟨11351961, by rfl⟩ : syracuseStep 30271897 = 22703923) B22703923
theorem B161450117 : Blo 2071435 161450117 := bstep (se 4 (by rfl) ⟨15135948, by rfl⟩ : syracuseStep 161450117 = 30271897) B30271897
theorem B107633411 : Blo 2071435 107633411 := bstep (se 1 (by rfl) ⟨80725058, by rfl⟩ : syracuseStep 107633411 = 161450117) B161450117
theorem B71755607 : Blo 2071435 71755607 := bstep (se 1 (by rfl) ⟨53816705, by rfl⟩ : syracuseStep 71755607 = 107633411) B107633411
theorem B47837071 : Blo 2071435 47837071 := bstep (se 1 (by rfl) ⟨35877803, by rfl⟩ : syracuseStep 47837071 = 71755607) B71755607
theorem B63782761 : Blo 2071435 63782761 := bstep (se 2 (by rfl) ⟨23918535, by rfl⟩ : syracuseStep 63782761 = 47837071) B47837071
theorem B85043681 : Blo 2071435 85043681 := bstep (se 2 (by rfl) ⟨31891380, by rfl⟩ : syracuseStep 85043681 = 63782761) B63782761
theorem B56695787 : Blo 2071435 56695787 := bstep (se 1 (by rfl) ⟨42521840, by rfl⟩ : syracuseStep 56695787 = 85043681) B85043681
theorem B37797191 : Blo 2071435 37797191 := bstep (se 1 (by rfl) ⟨28347893, by rfl⟩ : syracuseStep 37797191 = 56695787) B56695787
theorem B25198127 : Blo 2071435 25198127 := bstep (se 1 (by rfl) ⟨18898595, by rfl⟩ : syracuseStep 25198127 = 37797191) B37797191
theorem B16798751 : Blo 2071435 16798751 := bstep (se 1 (by rfl) ⟨12599063, by rfl⟩ : syracuseStep 16798751 = 25198127) B25198127
theorem B11199167 : Blo 2071435 11199167 := bstep (se 1 (by rfl) ⟨8399375, by rfl⟩ : syracuseStep 11199167 = 16798751) B16798751
theorem B7466111 : Blo 2071435 7466111 := bstep (se 1 (by rfl) ⟨5599583, by rfl⟩ : syracuseStep 7466111 = 11199167) B11199167
theorem B4977407 : Blo 2071435 4977407 := bstep (se 1 (by rfl) ⟨3733055, by rfl⟩ : syracuseStep 4977407 = 7466111) B7466111
theorem B13273085 : Blo 2071435 13273085 := bstep (se 3 (by rfl) ⟨2488703, by rfl⟩ : syracuseStep 13273085 = 4977407) B4977407
theorem B8848723 : Blo 2071435 8848723 := bstep (se 1 (by rfl) ⟨6636542, by rfl⟩ : syracuseStep 8848723 = 13273085) B13273085
theorem B11798297 : Blo 2071435 11798297 := bstep (se 2 (by rfl) ⟨4424361, by rfl⟩ : syracuseStep 11798297 = 8848723) B8848723
theorem B7865531 : Blo 2071435 7865531 := bstep (se 1 (by rfl) ⟨5899148, by rfl⟩ : syracuseStep 7865531 = 11798297) B11798297
theorem B5243687 : Blo 2071435 5243687 := bstep (se 1 (by rfl) ⟨3932765, by rfl⟩ : syracuseStep 5243687 = 7865531) B7865531
theorem B3495791 : Blo 2071435 3495791 := bstep (se 1 (by rfl) ⟨2621843, by rfl⟩ : syracuseStep 3495791 = 5243687) B5243687
theorem B2330527 : Blo 2071435 2330527 := bstep (se 1 (by rfl) ⟨1747895, by rfl⟩ : syracuseStep 2330527 = 3495791) B3495791
theorem B3107369 : Blo 2071435 3107369 := bstep (se 2 (by rfl) ⟨1165263, by rfl⟩ : syracuseStep 3107369 = 2330527) B2330527
theorem B2071579 : Blo 2071435 2071579 := bstep (se 1 (by rfl) ⟨1553684, by rfl⟩ : syracuseStep 2071579 = 3107369) B3107369
theorem B13273109 : Blo 2071435 13273109 := bbase (se 6 (by rfl) ⟨311088, by rfl⟩ : syracuseStep 13273109 = 622177) (by norm_num)
theorem B8848739 : Blo 2071435 8848739 := bstep (se 1 (by rfl) ⟨6636554, by rfl⟩ : syracuseStep 8848739 = 13273109) B13273109
theorem B5899159 : Blo 2071435 5899159 := bstep (se 1 (by rfl) ⟨4424369, by rfl⟩ : syracuseStep 5899159 = 8848739) B8848739
theorem B7865545 : Blo 2071435 7865545 := bstep (se 2 (by rfl) ⟨2949579, by rfl⟩ : syracuseStep 7865545 = 5899159) B5899159
theorem B10487393 : Blo 2071435 10487393 := bstep (se 2 (by rfl) ⟨3932772, by rfl⟩ : syracuseStep 10487393 = 7865545) B7865545
theorem B6991595 : Blo 2071435 6991595 := bstep (se 1 (by rfl) ⟨5243696, by rfl⟩ : syracuseStep 6991595 = 10487393) B10487393
theorem B4661063 : Blo 2071435 4661063 := bstep (se 1 (by rfl) ⟨3495797, by rfl⟩ : syracuseStep 4661063 = 6991595) B6991595
theorem B3107375 : Blo 2071435 3107375 := bstep (se 1 (by rfl) ⟨2330531, by rfl⟩ : syracuseStep 3107375 = 4661063) B4661063
theorem B2071583 : Blo 2071435 2071583 := bstep (se 1 (by rfl) ⟨1553687, by rfl⟩ : syracuseStep 2071583 = 3107375) B3107375
theorem B3107381 : Blo 2071435 3107381 := bbase (se 5 (by rfl) ⟨145658, by rfl⟩ : syracuseStep 3107381 = 291317) (by norm_num)
theorem B2071587 : Blo 2071435 2071587 := bstep (se 1 (by rfl) ⟨1553690, by rfl⟩ : syracuseStep 2071587 = 3107381) B3107381
theorem B5243717 : Blo 2071435 5243717 := bbase (se 4 (by rfl) ⟨491598, by rfl⟩ : syracuseStep 5243717 = 983197) (by norm_num)
theorem B3495811 : Blo 2071435 3495811 := bstep (se 1 (by rfl) ⟨2621858, by rfl⟩ : syracuseStep 3495811 = 5243717) B5243717
theorem B4661081 : Blo 2071435 4661081 := bstep (se 2 (by rfl) ⟨1747905, by rfl⟩ : syracuseStep 4661081 = 3495811) B3495811
theorem B3107387 : Blo 2071435 3107387 := bstep (se 1 (by rfl) ⟨2330540, by rfl⟩ : syracuseStep 3107387 = 4661081) B4661081
theorem B2071591 : Blo 2071435 2071591 := bstep (se 1 (by rfl) ⟨1553693, by rfl⟩ : syracuseStep 2071591 = 3107387) B3107387
theorem B2330545 : Blo 2071435 2330545 := bbase (se 2 (by rfl) ⟨873954, by rfl⟩ : syracuseStep 2330545 = 1747909) (by norm_num)
theorem B3107393 : Blo 2071435 3107393 := bstep (se 2 (by rfl) ⟨1165272, by rfl⟩ : syracuseStep 3107393 = 2330545) B2330545
theorem B2071595 : Blo 2071435 2071595 := bstep (se 1 (by rfl) ⟨1553696, by rfl⟩ : syracuseStep 2071595 = 3107393) B3107393
theorem B5899205 : Blo 2071435 5899205 := bbase (se 4 (by rfl) ⟨553050, by rfl⟩ : syracuseStep 5899205 = 1106101) (by norm_num)
theorem B3932803 : Blo 2071435 3932803 := bstep (se 1 (by rfl) ⟨2949602, by rfl⟩ : syracuseStep 3932803 = 5899205) B5899205
theorem B5243737 : Blo 2071435 5243737 := bstep (se 2 (by rfl) ⟨1966401, by rfl⟩ : syracuseStep 5243737 = 3932803) B3932803
theorem B6991649 : Blo 2071435 6991649 := bstep (se 2 (by rfl) ⟨2621868, by rfl⟩ : syracuseStep 6991649 = 5243737) B5243737
theorem B4661099 : Blo 2071435 4661099 := bstep (se 1 (by rfl) ⟨3495824, by rfl⟩ : syracuseStep 4661099 = 6991649) B6991649
theorem B3107399 : Blo 2071435 3107399 := bstep (se 1 (by rfl) ⟨2330549, by rfl⟩ : syracuseStep 3107399 = 4661099) B4661099
theorem B2071599 : Blo 2071435 2071599 := bstep (se 1 (by rfl) ⟨1553699, by rfl⟩ : syracuseStep 2071599 = 3107399) B3107399
theorem B3107405 : Blo 2071435 3107405 := bbase (se 3 (by rfl) ⟨582638, by rfl⟩ : syracuseStep 3107405 = 1165277) (by norm_num)
theorem B2071603 : Blo 2071435 2071603 := bstep (se 1 (by rfl) ⟨1553702, by rfl⟩ : syracuseStep 2071603 = 3107405) B3107405
theorem B4661117 : Blo 2071435 4661117 := bbase (se 3 (by rfl) ⟨873959, by rfl⟩ : syracuseStep 4661117 = 1747919) (by norm_num)
theorem B3107411 : Blo 2071435 3107411 := bstep (se 1 (by rfl) ⟨2330558, by rfl⟩ : syracuseStep 3107411 = 4661117) B4661117
theorem B2071607 : Blo 2071435 2071607 := bstep (se 1 (by rfl) ⟨1553705, by rfl⟩ : syracuseStep 2071607 = 3107411) B3107411
theorem B3495845 : Blo 2071435 3495845 := bbase (se 4 (by rfl) ⟨327735, by rfl⟩ : syracuseStep 3495845 = 655471) (by norm_num)
theorem B2330563 : Blo 2071435 2330563 := bstep (se 1 (by rfl) ⟨1747922, by rfl⟩ : syracuseStep 2330563 = 3495845) B3495845
theorem B3107417 : Blo 2071435 3107417 := bstep (se 2 (by rfl) ⟨1165281, by rfl⟩ : syracuseStep 3107417 = 2330563) B2330563
theorem B2071611 : Blo 2071435 2071611 := bstep (se 1 (by rfl) ⟨1553708, by rfl⟩ : syracuseStep 2071611 = 3107417) B3107417
theorem B2099881 : Blo 2071435 2099881 := bbase (se 2 (by rfl) ⟨787455, by rfl⟩ : syracuseStep 2099881 = 1574911) (by norm_num)
theorem B2799841 : Blo 2071435 2799841 := bstep (se 2 (by rfl) ⟨1049940, by rfl⟩ : syracuseStep 2799841 = 2099881) B2099881
theorem B3733121 : Blo 2071435 3733121 := bstep (se 2 (by rfl) ⟨1399920, by rfl⟩ : syracuseStep 3733121 = 2799841) B2799841
theorem B2488747 : Blo 2071435 2488747 := bstep (se 1 (by rfl) ⟨1866560, by rfl⟩ : syracuseStep 2488747 = 3733121) B3733121
theorem B3318329 : Blo 2071435 3318329 := bstep (se 2 (by rfl) ⟨1244373, by rfl⟩ : syracuseStep 3318329 = 2488747) B2488747
theorem B2212219 : Blo 2071435 2212219 := bstep (se 1 (by rfl) ⟨1659164, by rfl⟩ : syracuseStep 2212219 = 3318329) B3318329
theorem B2949625 : Blo 2071435 2949625 := bstep (se 2 (by rfl) ⟨1106109, by rfl⟩ : syracuseStep 2949625 = 2212219) B2212219
theorem B15731333 : Blo 2071435 15731333 := bstep (se 4 (by rfl) ⟨1474812, by rfl⟩ : syracuseStep 15731333 = 2949625) B2949625
theorem B10487555 : Blo 2071435 10487555 := bstep (se 1 (by rfl) ⟨7865666, by rfl⟩ : syracuseStep 10487555 = 15731333) B15731333
theorem B6991703 : Blo 2071435 6991703 := bstep (se 1 (by rfl) ⟨5243777, by rfl⟩ : syracuseStep 6991703 = 10487555) B10487555
theorem B4661135 : Blo 2071435 4661135 := bstep (se 1 (by rfl) ⟨3495851, by rfl⟩ : syracuseStep 4661135 = 6991703) B6991703
theorem B3107423 : Blo 2071435 3107423 := bstep (se 1 (by rfl) ⟨2330567, by rfl⟩ : syracuseStep 3107423 = 4661135) B4661135
theorem B2071615 : Blo 2071435 2071615 := bstep (se 1 (by rfl) ⟨1553711, by rfl⟩ : syracuseStep 2071615 = 3107423) B3107423
theorem B3107429 : Blo 2071435 3107429 := bbase (se 4 (by rfl) ⟨291321, by rfl⟩ : syracuseStep 3107429 = 582643) (by norm_num)
theorem B2071619 : Blo 2071435 2071619 := bstep (se 1 (by rfl) ⟨1553714, by rfl⟩ : syracuseStep 2071619 = 3107429) B3107429
theorem B2949637 : Blo 2071435 2949637 := bbase (se 4 (by rfl) ⟨276528, by rfl⟩ : syracuseStep 2949637 = 553057) (by norm_num)
theorem B3932849 : Blo 2071435 3932849 := bstep (se 2 (by rfl) ⟨1474818, by rfl⟩ : syracuseStep 3932849 = 2949637) B2949637
theorem B2621899 : Blo 2071435 2621899 := bstep (se 1 (by rfl) ⟨1966424, by rfl⟩ : syracuseStep 2621899 = 3932849) B3932849
theorem B3495865 : Blo 2071435 3495865 := bstep (se 2 (by rfl) ⟨1310949, by rfl⟩ : syracuseStep 3495865 = 2621899) B2621899
theorem B4661153 : Blo 2071435 4661153 := bstep (se 2 (by rfl) ⟨1747932, by rfl⟩ : syracuseStep 4661153 = 3495865) B3495865
theorem B3107435 : Blo 2071435 3107435 := bstep (se 1 (by rfl) ⟨2330576, by rfl⟩ : syracuseStep 3107435 = 4661153) B4661153
theorem B2071623 : Blo 2071435 2071623 := bstep (se 1 (by rfl) ⟨1553717, by rfl⟩ : syracuseStep 2071623 = 3107435) B3107435
theorem B2330581 : Blo 2071435 2330581 := bbase (se 7 (by rfl) ⟨27311, by rfl⟩ : syracuseStep 2330581 = 54623) (by norm_num)
theorem B3107441 : Blo 2071435 3107441 := bstep (se 2 (by rfl) ⟨1165290, by rfl⟩ : syracuseStep 3107441 = 2330581) B2330581
theorem B2071627 : Blo 2071435 2071627 := bstep (se 1 (by rfl) ⟨1553720, by rfl⟩ : syracuseStep 2071627 = 3107441) B3107441
theorem B2621909 : Blo 2071435 2621909 := bbase (se 7 (by rfl) ⟨30725, by rfl⟩ : syracuseStep 2621909 = 61451) (by norm_num)
theorem B6991757 : Blo 2071435 6991757 := bstep (se 3 (by rfl) ⟨1310954, by rfl⟩ : syracuseStep 6991757 = 2621909) B2621909
theorem B4661171 : Blo 2071435 4661171 := bstep (se 1 (by rfl) ⟨3495878, by rfl⟩ : syracuseStep 4661171 = 6991757) B6991757
theorem B3107447 : Blo 2071435 3107447 := bstep (se 1 (by rfl) ⟨2330585, by rfl⟩ : syracuseStep 3107447 = 4661171) B4661171
theorem B2071631 : Blo 2071435 2071631 := bstep (se 1 (by rfl) ⟨1553723, by rfl⟩ : syracuseStep 2071631 = 3107447) B3107447
theorem B3107453 : Blo 2071435 3107453 := bbase (se 3 (by rfl) ⟨582647, by rfl⟩ : syracuseStep 3107453 = 1165295) (by norm_num)
theorem B2071635 : Blo 2071435 2071635 := bstep (se 1 (by rfl) ⟨1553726, by rfl⟩ : syracuseStep 2071635 = 3107453) B3107453
theorem B4661189 : Blo 2071435 4661189 := bbase (se 4 (by rfl) ⟨436986, by rfl⟩ : syracuseStep 4661189 = 873973) (by norm_num)
theorem B3107459 : Blo 2071435 3107459 := bstep (se 1 (by rfl) ⟨2330594, by rfl⟩ : syracuseStep 3107459 = 4661189) B4661189
theorem B2071639 : Blo 2071435 2071639 := bstep (se 1 (by rfl) ⟨1553729, by rfl⟩ : syracuseStep 2071639 = 3107459) B3107459
theorem B8848997 : Blo 2071435 8848997 := bbase (se 4 (by rfl) ⟨829593, by rfl⟩ : syracuseStep 8848997 = 1659187) (by norm_num)
theorem B5899331 : Blo 2071435 5899331 := bstep (se 1 (by rfl) ⟨4424498, by rfl⟩ : syracuseStep 5899331 = 8848997) B8848997
theorem B3932887 : Blo 2071435 3932887 := bstep (se 1 (by rfl) ⟨2949665, by rfl⟩ : syracuseStep 3932887 = 5899331) B5899331
theorem B5243849 : Blo 2071435 5243849 := bstep (se 2 (by rfl) ⟨1966443, by rfl⟩ : syracuseStep 5243849 = 3932887) B3932887
theorem B3495899 : Blo 2071435 3495899 := bstep (se 1 (by rfl) ⟨2621924, by rfl⟩ : syracuseStep 3495899 = 5243849) B5243849
theorem B2330599 : Blo 2071435 2330599 := bstep (se 1 (by rfl) ⟨1747949, by rfl⟩ : syracuseStep 2330599 = 3495899) B3495899
theorem B3107465 : Blo 2071435 3107465 := bstep (se 2 (by rfl) ⟨1165299, by rfl⟩ : syracuseStep 3107465 = 2330599) B2330599
theorem B2071643 : Blo 2071435 2071643 := bstep (se 1 (by rfl) ⟨1553732, by rfl⟩ : syracuseStep 2071643 = 3107465) B3107465
theorem B10487717 : Blo 2071435 10487717 := bbase (se 4 (by rfl) ⟨983223, by rfl⟩ : syracuseStep 10487717 = 1966447) (by norm_num)
theorem B6991811 : Blo 2071435 6991811 := bstep (se 1 (by rfl) ⟨5243858, by rfl⟩ : syracuseStep 6991811 = 10487717) B10487717
theorem B4661207 : Blo 2071435 4661207 := bstep (se 1 (by rfl) ⟨3495905, by rfl⟩ : syracuseStep 4661207 = 6991811) B6991811
theorem B3107471 : Blo 2071435 3107471 := bstep (se 1 (by rfl) ⟨2330603, by rfl⟩ : syracuseStep 3107471 = 4661207) B4661207
theorem B2071647 : Blo 2071435 2071647 := bstep (se 1 (by rfl) ⟨1553735, by rfl⟩ : syracuseStep 2071647 = 3107471) B3107471
theorem B3107477 : Blo 2071435 3107477 := bbase (se 6 (by rfl) ⟨72831, by rfl⟩ : syracuseStep 3107477 = 145663) (by norm_num)
theorem B2071651 : Blo 2071435 2071651 := bstep (se 1 (by rfl) ⟨1553738, by rfl⟩ : syracuseStep 2071651 = 3107477) B3107477
theorem B19910357 : Blo 2071435 19910357 := bbase (se 7 (by rfl) ⟨233324, by rfl⟩ : syracuseStep 19910357 = 466649) (by norm_num)
theorem B13273571 : Blo 2071435 13273571 := bstep (se 1 (by rfl) ⟨9955178, by rfl⟩ : syracuseStep 13273571 = 19910357) B19910357
theorem B8849047 : Blo 2071435 8849047 := bstep (se 1 (by rfl) ⟨6636785, by rfl⟩ : syracuseStep 8849047 = 13273571) B13273571
theorem B11798729 : Blo 2071435 11798729 := bstep (se 2 (by rfl) ⟨4424523, by rfl⟩ : syracuseStep 11798729 = 8849047) B8849047
theorem B7865819 : Blo 2071435 7865819 := bstep (se 1 (by rfl) ⟨5899364, by rfl⟩ : syracuseStep 7865819 = 11798729) B11798729
theorem B5243879 : Blo 2071435 5243879 := bstep (se 1 (by rfl) ⟨3932909, by rfl⟩ : syracuseStep 5243879 = 7865819) B7865819
theorem B3495919 : Blo 2071435 3495919 := bstep (se 1 (by rfl) ⟨2621939, by rfl⟩ : syracuseStep 3495919 = 5243879) B5243879
theorem B4661225 : Blo 2071435 4661225 := bstep (se 2 (by rfl) ⟨1747959, by rfl⟩ : syracuseStep 4661225 = 3495919) B3495919
theorem B3107483 : Blo 2071435 3107483 := bstep (se 1 (by rfl) ⟨2330612, by rfl⟩ : syracuseStep 3107483 = 4661225) B4661225
theorem B2071655 : Blo 2071435 2071655 := bstep (se 1 (by rfl) ⟨1553741, by rfl⟩ : syracuseStep 2071655 = 3107483) B3107483
theorem B2330617 : Blo 2071435 2330617 := bbase (se 2 (by rfl) ⟨873981, by rfl⟩ : syracuseStep 2330617 = 1747963) (by norm_num)
theorem B3107489 : Blo 2071435 3107489 := bstep (se 2 (by rfl) ⟨1165308, by rfl⟩ : syracuseStep 3107489 = 2330617) B2330617
theorem B2071659 : Blo 2071435 2071659 := bstep (se 1 (by rfl) ⟨1553744, by rfl⟩ : syracuseStep 2071659 = 3107489) B3107489
theorem B2099929 : Blo 2071435 2099929 := bbase (se 2 (by rfl) ⟨787473, by rfl⟩ : syracuseStep 2099929 = 1574947) (by norm_num)
theorem B2799905 : Blo 2071435 2799905 := bstep (se 2 (by rfl) ⟨1049964, by rfl⟩ : syracuseStep 2799905 = 2099929) B2099929
theorem B7466413 : Blo 2071435 7466413 := bstep (se 3 (by rfl) ⟨1399952, by rfl⟩ : syracuseStep 7466413 = 2799905) B2799905
theorem B9955217 : Blo 2071435 9955217 := bstep (se 2 (by rfl) ⟨3733206, by rfl⟩ : syracuseStep 9955217 = 7466413) B7466413
theorem B6636811 : Blo 2071435 6636811 := bstep (se 1 (by rfl) ⟨4977608, by rfl⟩ : syracuseStep 6636811 = 9955217) B9955217
theorem B8849081 : Blo 2071435 8849081 := bstep (se 2 (by rfl) ⟨3318405, by rfl⟩ : syracuseStep 8849081 = 6636811) B6636811
theorem B5899387 : Blo 2071435 5899387 := bstep (se 1 (by rfl) ⟨4424540, by rfl⟩ : syracuseStep 5899387 = 8849081) B8849081
theorem B7865849 : Blo 2071435 7865849 := bstep (se 2 (by rfl) ⟨2949693, by rfl⟩ : syracuseStep 7865849 = 5899387) B5899387
theorem B5243899 : Blo 2071435 5243899 := bstep (se 1 (by rfl) ⟨3932924, by rfl⟩ : syracuseStep 5243899 = 7865849) B7865849
theorem B6991865 : Blo 2071435 6991865 := bstep (se 2 (by rfl) ⟨2621949, by rfl⟩ : syracuseStep 6991865 = 5243899) B5243899
theorem B4661243 : Blo 2071435 4661243 := bstep (se 1 (by rfl) ⟨3495932, by rfl⟩ : syracuseStep 4661243 = 6991865) B6991865
theorem B3107495 : Blo 2071435 3107495 := bstep (se 1 (by rfl) ⟨2330621, by rfl⟩ : syracuseStep 3107495 = 4661243) B4661243
theorem B2071663 : Blo 2071435 2071663 := bstep (se 1 (by rfl) ⟨1553747, by rfl⟩ : syracuseStep 2071663 = 3107495) B3107495
theorem B3107501 : Blo 2071435 3107501 := bbase (se 3 (by rfl) ⟨582656, by rfl⟩ : syracuseStep 3107501 = 1165313) (by norm_num)
theorem B2071667 : Blo 2071435 2071667 := bstep (se 1 (by rfl) ⟨1553750, by rfl⟩ : syracuseStep 2071667 = 3107501) B3107501
theorem B4661261 : Blo 2071435 4661261 := bbase (se 3 (by rfl) ⟨873986, by rfl⟩ : syracuseStep 4661261 = 1747973) (by norm_num)
theorem B3107507 : Blo 2071435 3107507 := bstep (se 1 (by rfl) ⟨2330630, by rfl⟩ : syracuseStep 3107507 = 4661261) B4661261
theorem B2071671 : Blo 2071435 2071671 := bstep (se 1 (by rfl) ⟨1553753, by rfl⟩ : syracuseStep 2071671 = 3107507) B3107507
theorem B2621965 : Blo 2071435 2621965 := bbase (se 3 (by rfl) ⟨491618, by rfl⟩ : syracuseStep 2621965 = 983237) (by norm_num)
theorem B3495953 : Blo 2071435 3495953 := bstep (se 2 (by rfl) ⟨1310982, by rfl⟩ : syracuseStep 3495953 = 2621965) B2621965
theorem B2330635 : Blo 2071435 2330635 := bstep (se 1 (by rfl) ⟨1747976, by rfl⟩ : syracuseStep 2330635 = 3495953) B3495953
theorem B3107513 : Blo 2071435 3107513 := bstep (se 2 (by rfl) ⟨1165317, by rfl⟩ : syracuseStep 3107513 = 2330635) B2330635
theorem B2071675 : Blo 2071435 2071675 := bstep (se 1 (by rfl) ⟨1553756, by rfl⟩ : syracuseStep 2071675 = 3107513) B3107513
theorem B3149917 : Blo 2071435 3149917 := bbase (se 3 (by rfl) ⟨590609, by rfl⟩ : syracuseStep 3149917 = 1181219) (by norm_num)
theorem B16799557 : Blo 2071435 16799557 := bstep (se 4 (by rfl) ⟨1574958, by rfl⟩ : syracuseStep 16799557 = 3149917) B3149917
theorem B22399409 : Blo 2071435 22399409 := bstep (se 2 (by rfl) ⟨8399778, by rfl⟩ : syracuseStep 22399409 = 16799557) B16799557
theorem B14932939 : Blo 2071435 14932939 := bstep (se 1 (by rfl) ⟨11199704, by rfl⟩ : syracuseStep 14932939 = 22399409) B22399409
theorem B19910585 : Blo 2071435 19910585 := bstep (se 2 (by rfl) ⟨7466469, by rfl⟩ : syracuseStep 19910585 = 14932939) B14932939
theorem B13273723 : Blo 2071435 13273723 := bstep (se 1 (by rfl) ⟨9955292, by rfl⟩ : syracuseStep 13273723 = 19910585) B19910585
theorem B17698297 : Blo 2071435 17698297 := bstep (se 2 (by rfl) ⟨6636861, by rfl⟩ : syracuseStep 17698297 = 13273723) B13273723
theorem B23597729 : Blo 2071435 23597729 := bstep (se 2 (by rfl) ⟨8849148, by rfl⟩ : syracuseStep 23597729 = 17698297) B17698297
theorem B15731819 : Blo 2071435 15731819 := bstep (se 1 (by rfl) ⟨11798864, by rfl⟩ : syracuseStep 15731819 = 23597729) B23597729
theorem B10487879 : Blo 2071435 10487879 := bstep (se 1 (by rfl) ⟨7865909, by rfl⟩ : syracuseStep 10487879 = 15731819) B15731819
theorem B6991919 : Blo 2071435 6991919 := bstep (se 1 (by rfl) ⟨5243939, by rfl⟩ : syracuseStep 6991919 = 10487879) B10487879
theorem B4661279 : Blo 2071435 4661279 := bstep (se 1 (by rfl) ⟨3495959, by rfl⟩ : syracuseStep 4661279 = 6991919) B6991919
theorem B3107519 : Blo 2071435 3107519 := bstep (se 1 (by rfl) ⟨2330639, by rfl⟩ : syracuseStep 3107519 = 4661279) B4661279
theorem B2071679 : Blo 2071435 2071679 := bstep (se 1 (by rfl) ⟨1553759, by rfl⟩ : syracuseStep 2071679 = 3107519) B3107519
theorem B3107525 : Blo 2071435 3107525 := bbase (se 4 (by rfl) ⟨291330, by rfl⟩ : syracuseStep 3107525 = 582661) (by norm_num)
theorem B2071683 : Blo 2071435 2071683 := bstep (se 1 (by rfl) ⟨1553762, by rfl⟩ : syracuseStep 2071683 = 3107525) B3107525
theorem B3495973 : Blo 2071435 3495973 := bbase (se 4 (by rfl) ⟨327747, by rfl⟩ : syracuseStep 3495973 = 655495) (by norm_num)
theorem B4661297 : Blo 2071435 4661297 := bstep (se 2 (by rfl) ⟨1747986, by rfl⟩ : syracuseStep 4661297 = 3495973) B3495973
theorem B3107531 : Blo 2071435 3107531 := bstep (se 1 (by rfl) ⟨2330648, by rfl⟩ : syracuseStep 3107531 = 4661297) B4661297
theorem B2071687 : Blo 2071435 2071687 := bstep (se 1 (by rfl) ⟨1553765, by rfl⟩ : syracuseStep 2071687 = 3107531) B3107531
theorem B2330653 : Blo 2071435 2330653 := bbase (se 3 (by rfl) ⟨436997, by rfl⟩ : syracuseStep 2330653 = 873995) (by norm_num)
theorem B3107537 : Blo 2071435 3107537 := bstep (se 2 (by rfl) ⟨1165326, by rfl⟩ : syracuseStep 3107537 = 2330653) B2330653
theorem B2071691 : Blo 2071435 2071691 := bstep (se 1 (by rfl) ⟨1553768, by rfl⟩ : syracuseStep 2071691 = 3107537) B3107537
theorem B6991973 : Blo 2071435 6991973 := bbase (se 4 (by rfl) ⟨655497, by rfl⟩ : syracuseStep 6991973 = 1310995) (by norm_num)
theorem B4661315 : Blo 2071435 4661315 := bstep (se 1 (by rfl) ⟨3495986, by rfl⟩ : syracuseStep 4661315 = 6991973) B6991973
theorem B3107543 : Blo 2071435 3107543 := bstep (se 1 (by rfl) ⟨2330657, by rfl⟩ : syracuseStep 3107543 = 4661315) B4661315
theorem B2071695 : Blo 2071435 2071695 := bstep (se 1 (by rfl) ⟨1553771, by rfl⟩ : syracuseStep 2071695 = 3107543) B3107543
theorem B3107549 : Blo 2071435 3107549 := bbase (se 3 (by rfl) ⟨582665, by rfl⟩ : syracuseStep 3107549 = 1165331) (by norm_num)
theorem B2071699 : Blo 2071435 2071699 := bstep (se 1 (by rfl) ⟨1553774, by rfl⟩ : syracuseStep 2071699 = 3107549) B3107549
theorem B4661333 : Blo 2071435 4661333 := bbase (se 8 (by rfl) ⟨27312, by rfl⟩ : syracuseStep 4661333 = 54625) (by norm_num)
theorem B3107555 : Blo 2071435 3107555 := bstep (se 1 (by rfl) ⟨2330666, by rfl⟩ : syracuseStep 3107555 = 4661333) B4661333
theorem B2071703 : Blo 2071435 2071703 := bstep (se 1 (by rfl) ⟨1553777, by rfl⟩ : syracuseStep 2071703 = 3107555) B3107555
theorem B2799965 : Blo 2071435 2799965 := bbase (se 3 (by rfl) ⟨524993, by rfl⟩ : syracuseStep 2799965 = 1049987) (by norm_num)
theorem B7466573 : Blo 2071435 7466573 := bstep (se 3 (by rfl) ⟨1399982, by rfl⟩ : syracuseStep 7466573 = 2799965) B2799965
theorem B4977715 : Blo 2071435 4977715 := bstep (se 1 (by rfl) ⟨3733286, by rfl⟩ : syracuseStep 4977715 = 7466573) B7466573
theorem B6636953 : Blo 2071435 6636953 := bstep (se 2 (by rfl) ⟨2488857, by rfl⟩ : syracuseStep 6636953 = 4977715) B4977715
theorem B4424635 : Blo 2071435 4424635 := bstep (se 1 (by rfl) ⟨3318476, by rfl⟩ : syracuseStep 4424635 = 6636953) B6636953
theorem B5899513 : Blo 2071435 5899513 := bstep (se 2 (by rfl) ⟨2212317, by rfl⟩ : syracuseStep 5899513 = 4424635) B4424635
theorem B7866017 : Blo 2071435 7866017 := bstep (se 2 (by rfl) ⟨2949756, by rfl⟩ : syracuseStep 7866017 = 5899513) B5899513
theorem B5244011 : Blo 2071435 5244011 := bstep (se 1 (by rfl) ⟨3933008, by rfl⟩ : syracuseStep 5244011 = 7866017) B7866017
theorem B3496007 : Blo 2071435 3496007 := bstep (se 1 (by rfl) ⟨2622005, by rfl⟩ : syracuseStep 3496007 = 5244011) B5244011
theorem B2330671 : Blo 2071435 2330671 := bstep (se 1 (by rfl) ⟨1748003, by rfl⟩ : syracuseStep 2330671 = 3496007) B3496007
theorem B3107561 : Blo 2071435 3107561 := bstep (se 2 (by rfl) ⟨1165335, by rfl⟩ : syracuseStep 3107561 = 2330671) B2330671
theorem B2071707 : Blo 2071435 2071707 := bstep (se 1 (by rfl) ⟨1553780, by rfl⟩ : syracuseStep 2071707 = 3107561) B3107561
theorem B8399909 : Blo 2071435 8399909 := bbase (se 4 (by rfl) ⟨787491, by rfl⟩ : syracuseStep 8399909 = 1574983) (by norm_num)
theorem B5599939 : Blo 2071435 5599939 := bstep (se 1 (by rfl) ⟨4199954, by rfl⟩ : syracuseStep 5599939 = 8399909) B8399909
theorem B7466585 : Blo 2071435 7466585 := bstep (se 2 (by rfl) ⟨2799969, by rfl⟩ : syracuseStep 7466585 = 5599939) B5599939
theorem B19910893 : Blo 2071435 19910893 := bstep (se 3 (by rfl) ⟨3733292, by rfl⟩ : syracuseStep 19910893 = 7466585) B7466585
theorem B26547857 : Blo 2071435 26547857 := bstep (se 2 (by rfl) ⟨9955446, by rfl⟩ : syracuseStep 26547857 = 19910893) B19910893
theorem B17698571 : Blo 2071435 17698571 := bstep (se 1 (by rfl) ⟨13273928, by rfl⟩ : syracuseStep 17698571 = 26547857) B26547857
theorem B11799047 : Blo 2071435 11799047 := bstep (se 1 (by rfl) ⟨8849285, by rfl⟩ : syracuseStep 11799047 = 17698571) B17698571
theorem B7866031 : Blo 2071435 7866031 := bstep (se 1 (by rfl) ⟨5899523, by rfl⟩ : syracuseStep 7866031 = 11799047) B11799047
theorem B10488041 : Blo 2071435 10488041 := bstep (se 2 (by rfl) ⟨3933015, by rfl⟩ : syracuseStep 10488041 = 7866031) B7866031
theorem B6992027 : Blo 2071435 6992027 := bstep (se 1 (by rfl) ⟨5244020, by rfl⟩ : syracuseStep 6992027 = 10488041) B10488041
theorem B4661351 : Blo 2071435 4661351 := bstep (se 1 (by rfl) ⟨3496013, by rfl⟩ : syracuseStep 4661351 = 6992027) B6992027
theorem B3107567 : Blo 2071435 3107567 := bstep (se 1 (by rfl) ⟨2330675, by rfl⟩ : syracuseStep 3107567 = 4661351) B4661351
theorem B2071711 : Blo 2071435 2071711 := bstep (se 1 (by rfl) ⟨1553783, by rfl⟩ : syracuseStep 2071711 = 3107567) B3107567
theorem B3107573 : Blo 2071435 3107573 := bbase (se 5 (by rfl) ⟨145667, by rfl⟩ : syracuseStep 3107573 = 291335) (by norm_num)
theorem B2071715 : Blo 2071435 2071715 := bstep (se 1 (by rfl) ⟨1553786, by rfl⟩ : syracuseStep 2071715 = 3107573) B3107573
theorem B30273941 : Blo 2071435 30273941 := bbase (se 6 (by rfl) ⟨709545, by rfl⟩ : syracuseStep 30273941 = 1419091) (by norm_num)
theorem B20182627 : Blo 2071435 20182627 := bstep (se 1 (by rfl) ⟨15136970, by rfl⟩ : syracuseStep 20182627 = 30273941) B30273941
theorem B107640677 : Blo 2071435 107640677 := bstep (se 4 (by rfl) ⟨10091313, by rfl⟩ : syracuseStep 107640677 = 20182627) B20182627
theorem B287041805 : Blo 2071435 287041805 := bstep (se 3 (by rfl) ⟨53820338, by rfl⟩ : syracuseStep 287041805 = 107640677) B107640677
theorem B191361203 : Blo 2071435 191361203 := bstep (se 1 (by rfl) ⟨143520902, by rfl⟩ : syracuseStep 191361203 = 287041805) B287041805
theorem B127574135 : Blo 2071435 127574135 := bstep (se 1 (by rfl) ⟨95680601, by rfl⟩ : syracuseStep 127574135 = 191361203) B191361203
theorem B85049423 : Blo 2071435 85049423 := bstep (se 1 (by rfl) ⟨63787067, by rfl⟩ : syracuseStep 85049423 = 127574135) B127574135
theorem B56699615 : Blo 2071435 56699615 := bstep (se 1 (by rfl) ⟨42524711, by rfl⟩ : syracuseStep 56699615 = 85049423) B85049423
theorem B37799743 : Blo 2071435 37799743 := bstep (se 1 (by rfl) ⟨28349807, by rfl⟩ : syracuseStep 37799743 = 56699615) B56699615
theorem B50399657 : Blo 2071435 50399657 := bstep (se 2 (by rfl) ⟨18899871, by rfl⟩ : syracuseStep 50399657 = 37799743) B37799743
theorem B33599771 : Blo 2071435 33599771 := bstep (se 1 (by rfl) ⟨25199828, by rfl⟩ : syracuseStep 33599771 = 50399657) B50399657
theorem B22399847 : Blo 2071435 22399847 := bstep (se 1 (by rfl) ⟨16799885, by rfl⟩ : syracuseStep 22399847 = 33599771) B33599771
theorem B14933231 : Blo 2071435 14933231 := bstep (se 1 (by rfl) ⟨11199923, by rfl⟩ : syracuseStep 14933231 = 22399847) B22399847
theorem B9955487 : Blo 2071435 9955487 := bstep (se 1 (by rfl) ⟨7466615, by rfl⟩ : syracuseStep 9955487 = 14933231) B14933231
theorem B6636991 : Blo 2071435 6636991 := bstep (se 1 (by rfl) ⟨4977743, by rfl⟩ : syracuseStep 6636991 = 9955487) B9955487
theorem B8849321 : Blo 2071435 8849321 := bstep (se 2 (by rfl) ⟨3318495, by rfl⟩ : syracuseStep 8849321 = 6636991) B6636991
theorem B5899547 : Blo 2071435 5899547 := bstep (se 1 (by rfl) ⟨4424660, by rfl⟩ : syracuseStep 5899547 = 8849321) B8849321
theorem B3933031 : Blo 2071435 3933031 := bstep (se 1 (by rfl) ⟨2949773, by rfl⟩ : syracuseStep 3933031 = 5899547) B5899547
theorem B5244041 : Blo 2071435 5244041 := bstep (se 2 (by rfl) ⟨1966515, by rfl⟩ : syracuseStep 5244041 = 3933031) B3933031
theorem B3496027 : Blo 2071435 3496027 := bstep (se 1 (by rfl) ⟨2622020, by rfl⟩ : syracuseStep 3496027 = 5244041) B5244041
theorem B4661369 : Blo 2071435 4661369 := bstep (se 2 (by rfl) ⟨1748013, by rfl⟩ : syracuseStep 4661369 = 3496027) B3496027
theorem B3107579 : Blo 2071435 3107579 := bstep (se 1 (by rfl) ⟨2330684, by rfl⟩ : syracuseStep 3107579 = 4661369) B4661369
theorem B2071719 : Blo 2071435 2071719 := bstep (se 1 (by rfl) ⟨1553789, by rfl⟩ : syracuseStep 2071719 = 3107579) B3107579
theorem B2330689 : Blo 2071435 2330689 := bbase (se 2 (by rfl) ⟨874008, by rfl⟩ : syracuseStep 2330689 = 1748017) (by norm_num)
theorem B3107585 : Blo 2071435 3107585 := bstep (se 2 (by rfl) ⟨1165344, by rfl⟩ : syracuseStep 3107585 = 2330689) B2330689
theorem B2071723 : Blo 2071435 2071723 := bstep (se 1 (by rfl) ⟨1553792, by rfl⟩ : syracuseStep 2071723 = 3107585) B3107585
theorem B5244061 : Blo 2071435 5244061 := bbase (se 3 (by rfl) ⟨983261, by rfl⟩ : syracuseStep 5244061 = 1966523) (by norm_num)
theorem B6992081 : Blo 2071435 6992081 := bstep (se 2 (by rfl) ⟨2622030, by rfl⟩ : syracuseStep 6992081 = 5244061) B5244061
theorem B4661387 : Blo 2071435 4661387 := bstep (se 1 (by rfl) ⟨3496040, by rfl⟩ : syracuseStep 4661387 = 6992081) B6992081
theorem B3107591 : Blo 2071435 3107591 := bstep (se 1 (by rfl) ⟨2330693, by rfl⟩ : syracuseStep 3107591 = 4661387) B4661387
theorem B2071727 : Blo 2071435 2071727 := bstep (se 1 (by rfl) ⟨1553795, by rfl⟩ : syracuseStep 2071727 = 3107591) B3107591
theorem B3107597 : Blo 2071435 3107597 := bbase (se 3 (by rfl) ⟨582674, by rfl⟩ : syracuseStep 3107597 = 1165349) (by norm_num)
theorem B2071731 : Blo 2071435 2071731 := bstep (se 1 (by rfl) ⟨1553798, by rfl⟩ : syracuseStep 2071731 = 3107597) B3107597
theorem B4661405 : Blo 2071435 4661405 := bbase (se 3 (by rfl) ⟨874013, by rfl⟩ : syracuseStep 4661405 = 1748027) (by norm_num)
theorem B3107603 : Blo 2071435 3107603 := bstep (se 1 (by rfl) ⟨2330702, by rfl⟩ : syracuseStep 3107603 = 4661405) B4661405
theorem B2071735 : Blo 2071435 2071735 := bstep (se 1 (by rfl) ⟨1553801, by rfl⟩ : syracuseStep 2071735 = 3107603) B3107603
theorem B3496061 : Blo 2071435 3496061 := bbase (se 3 (by rfl) ⟨655511, by rfl⟩ : syracuseStep 3496061 = 1311023) (by norm_num)
theorem B2330707 : Blo 2071435 2330707 := bstep (se 1 (by rfl) ⟨1748030, by rfl⟩ : syracuseStep 2330707 = 3496061) B3496061
theorem B3107609 : Blo 2071435 3107609 := bstep (se 2 (by rfl) ⟨1165353, by rfl⟩ : syracuseStep 3107609 = 2330707) B2330707
theorem B2071739 : Blo 2071435 2071739 := bstep (se 1 (by rfl) ⟨1553804, by rfl⟩ : syracuseStep 2071739 = 3107609) B3107609
theorem B2800013 : Blo 2071435 2800013 := bbase (se 3 (by rfl) ⟨525002, by rfl⟩ : syracuseStep 2800013 = 1050005) (by norm_num)
theorem B7466701 : Blo 2071435 7466701 := bstep (se 3 (by rfl) ⟨1400006, by rfl⟩ : syracuseStep 7466701 = 2800013) B2800013
theorem B9955601 : Blo 2071435 9955601 := bstep (se 2 (by rfl) ⟨3733350, by rfl⟩ : syracuseStep 9955601 = 7466701) B7466701
theorem B6637067 : Blo 2071435 6637067 := bstep (se 1 (by rfl) ⟨4977800, by rfl⟩ : syracuseStep 6637067 = 9955601) B9955601
theorem B4424711 : Blo 2071435 4424711 := bstep (se 1 (by rfl) ⟨3318533, by rfl⟩ : syracuseStep 4424711 = 6637067) B6637067
theorem B11799229 : Blo 2071435 11799229 := bstep (se 3 (by rfl) ⟨2212355, by rfl⟩ : syracuseStep 11799229 = 4424711) B4424711
theorem B15732305 : Blo 2071435 15732305 := bstep (se 2 (by rfl) ⟨5899614, by rfl⟩ : syracuseStep 15732305 = 11799229) B11799229
theorem B10488203 : Blo 2071435 10488203 := bstep (se 1 (by rfl) ⟨7866152, by rfl⟩ : syracuseStep 10488203 = 15732305) B15732305
theorem B6992135 : Blo 2071435 6992135 := bstep (se 1 (by rfl) ⟨5244101, by rfl⟩ : syracuseStep 6992135 = 10488203) B10488203
theorem B4661423 : Blo 2071435 4661423 := bstep (se 1 (by rfl) ⟨3496067, by rfl⟩ : syracuseStep 4661423 = 6992135) B6992135
theorem B3107615 : Blo 2071435 3107615 := bstep (se 1 (by rfl) ⟨2330711, by rfl⟩ : syracuseStep 3107615 = 4661423) B4661423
theorem B2071743 : Blo 2071435 2071743 := bstep (se 1 (by rfl) ⟨1553807, by rfl⟩ : syracuseStep 2071743 = 3107615) B3107615
theorem B3107621 : Blo 2071435 3107621 := bbase (se 4 (by rfl) ⟨291339, by rfl⟩ : syracuseStep 3107621 = 582679) (by norm_num)
theorem B2071747 : Blo 2071435 2071747 := bstep (se 1 (by rfl) ⟨1553810, by rfl⟩ : syracuseStep 2071747 = 3107621) B3107621
theorem B2622061 : Blo 2071435 2622061 := bbase (se 3 (by rfl) ⟨491636, by rfl⟩ : syracuseStep 2622061 = 983273) (by norm_num)
theorem B3496081 : Blo 2071435 3496081 := bstep (se 2 (by rfl) ⟨1311030, by rfl⟩ : syracuseStep 3496081 = 2622061) B2622061
theorem B4661441 : Blo 2071435 4661441 := bstep (se 2 (by rfl) ⟨1748040, by rfl⟩ : syracuseStep 4661441 = 3496081) B3496081
theorem B3107627 : Blo 2071435 3107627 := bstep (se 1 (by rfl) ⟨2330720, by rfl⟩ : syracuseStep 3107627 = 4661441) B4661441
theorem B2071751 : Blo 2071435 2071751 := bstep (se 1 (by rfl) ⟨1553813, by rfl⟩ : syracuseStep 2071751 = 3107627) B3107627
theorem B2330725 : Blo 2071435 2330725 := bbase (se 4 (by rfl) ⟨218505, by rfl⟩ : syracuseStep 2330725 = 437011) (by norm_num)
theorem B3107633 : Blo 2071435 3107633 := bstep (se 2 (by rfl) ⟨1165362, by rfl⟩ : syracuseStep 3107633 = 2330725) B2330725
theorem B2071755 : Blo 2071435 2071755 := bstep (se 1 (by rfl) ⟨1553816, by rfl⟩ : syracuseStep 2071755 = 3107633) B3107633
theorem B2212373 : Blo 2071435 2212373 := bbase (se 6 (by rfl) ⟨51852, by rfl⟩ : syracuseStep 2212373 = 103705) (by norm_num)
theorem B5899661 : Blo 2071435 5899661 := bstep (se 3 (by rfl) ⟨1106186, by rfl⟩ : syracuseStep 5899661 = 2212373) B2212373
theorem B3933107 : Blo 2071435 3933107 := bstep (se 1 (by rfl) ⟨2949830, by rfl⟩ : syracuseStep 3933107 = 5899661) B5899661
theorem B2622071 : Blo 2071435 2622071 := bstep (se 1 (by rfl) ⟨1966553, by rfl⟩ : syracuseStep 2622071 = 3933107) B3933107
theorem B6992189 : Blo 2071435 6992189 := bstep (se 3 (by rfl) ⟨1311035, by rfl⟩ : syracuseStep 6992189 = 2622071) B2622071
theorem B4661459 : Blo 2071435 4661459 := bstep (se 1 (by rfl) ⟨3496094, by rfl⟩ : syracuseStep 4661459 = 6992189) B6992189
theorem B3107639 : Blo 2071435 3107639 := bstep (se 1 (by rfl) ⟨2330729, by rfl⟩ : syracuseStep 3107639 = 4661459) B4661459
theorem B2071759 : Blo 2071435 2071759 := bstep (se 1 (by rfl) ⟨1553819, by rfl⟩ : syracuseStep 2071759 = 3107639) B3107639
theorem B3107645 : Blo 2071435 3107645 := bbase (se 3 (by rfl) ⟨582683, by rfl⟩ : syracuseStep 3107645 = 1165367) (by norm_num)
theorem B2071763 : Blo 2071435 2071763 := bstep (se 1 (by rfl) ⟨1553822, by rfl⟩ : syracuseStep 2071763 = 3107645) B3107645
theorem B4661477 : Blo 2071435 4661477 := bbase (se 4 (by rfl) ⟨437013, by rfl⟩ : syracuseStep 4661477 = 874027) (by norm_num)
theorem B3107651 : Blo 2071435 3107651 := bstep (se 1 (by rfl) ⟨2330738, by rfl⟩ : syracuseStep 3107651 = 4661477) B4661477
theorem B2071767 : Blo 2071435 2071767 := bstep (se 1 (by rfl) ⟨1553825, by rfl⟩ : syracuseStep 2071767 = 3107651) B3107651
theorem B5244173 : Blo 2071435 5244173 := bbase (se 3 (by rfl) ⟨983282, by rfl⟩ : syracuseStep 5244173 = 1966565) (by norm_num)
theorem B3496115 : Blo 2071435 3496115 := bstep (se 1 (by rfl) ⟨2622086, by rfl⟩ : syracuseStep 3496115 = 5244173) B5244173
theorem B2330743 : Blo 2071435 2330743 := bstep (se 1 (by rfl) ⟨1748057, by rfl⟩ : syracuseStep 2330743 = 3496115) B3496115
theorem B3107657 : Blo 2071435 3107657 := bstep (se 2 (by rfl) ⟨1165371, by rfl⟩ : syracuseStep 3107657 = 2330743) B2330743
theorem B2071771 : Blo 2071435 2071771 := bstep (se 1 (by rfl) ⟨1553828, by rfl⟩ : syracuseStep 2071771 = 3107657) B3107657
theorem B2949853 : Blo 2071435 2949853 := bbase (se 3 (by rfl) ⟨553097, by rfl⟩ : syracuseStep 2949853 = 1106195) (by norm_num)
theorem B3933137 : Blo 2071435 3933137 := bstep (se 2 (by rfl) ⟨1474926, by rfl⟩ : syracuseStep 3933137 = 2949853) B2949853
theorem B10488365 : Blo 2071435 10488365 := bstep (se 3 (by rfl) ⟨1966568, by rfl⟩ : syracuseStep 10488365 = 3933137) B3933137
theorem B6992243 : Blo 2071435 6992243 := bstep (se 1 (by rfl) ⟨5244182, by rfl⟩ : syracuseStep 6992243 = 10488365) B10488365
theorem B4661495 : Blo 2071435 4661495 := bstep (se 1 (by rfl) ⟨3496121, by rfl⟩ : syracuseStep 4661495 = 6992243) B6992243
theorem B3107663 : Blo 2071435 3107663 := bstep (se 1 (by rfl) ⟨2330747, by rfl⟩ : syracuseStep 3107663 = 4661495) B4661495
theorem B2071775 : Blo 2071435 2071775 := bstep (se 1 (by rfl) ⟨1553831, by rfl⟩ : syracuseStep 2071775 = 3107663) B3107663
theorem B3107669 : Blo 2071435 3107669 := bbase (se 9 (by rfl) ⟨9104, by rfl⟩ : syracuseStep 3107669 = 18209) (by norm_num)
theorem B2071779 : Blo 2071435 2071779 := bstep (se 1 (by rfl) ⟨1553834, by rfl⟩ : syracuseStep 2071779 = 3107669) B3107669
theorem B4424797 : Blo 2071435 4424797 := bbase (se 3 (by rfl) ⟨829649, by rfl⟩ : syracuseStep 4424797 = 1659299) (by norm_num)
theorem B5899729 : Blo 2071435 5899729 := bstep (se 2 (by rfl) ⟨2212398, by rfl⟩ : syracuseStep 5899729 = 4424797) B4424797
theorem B7866305 : Blo 2071435 7866305 := bstep (se 2 (by rfl) ⟨2949864, by rfl⟩ : syracuseStep 7866305 = 5899729) B5899729
theorem B5244203 : Blo 2071435 5244203 := bstep (se 1 (by rfl) ⟨3933152, by rfl⟩ : syracuseStep 5244203 = 7866305) B7866305
theorem B3496135 : Blo 2071435 3496135 := bstep (se 1 (by rfl) ⟨2622101, by rfl⟩ : syracuseStep 3496135 = 5244203) B5244203
theorem B4661513 : Blo 2071435 4661513 := bstep (se 2 (by rfl) ⟨1748067, by rfl⟩ : syracuseStep 4661513 = 3496135) B3496135
theorem B3107675 : Blo 2071435 3107675 := bstep (se 1 (by rfl) ⟨2330756, by rfl⟩ : syracuseStep 3107675 = 4661513) B4661513
theorem B2071783 : Blo 2071435 2071783 := bstep (se 1 (by rfl) ⟨1553837, by rfl⟩ : syracuseStep 2071783 = 3107675) B3107675
theorem B2330761 : Blo 2071435 2330761 := bbase (se 2 (by rfl) ⟨874035, by rfl⟩ : syracuseStep 2330761 = 1748071) (by norm_num)
theorem B3107681 : Blo 2071435 3107681 := bstep (se 2 (by rfl) ⟨1165380, by rfl⟩ : syracuseStep 3107681 = 2330761) B2330761
theorem B2071787 : Blo 2071435 2071787 := bstep (se 1 (by rfl) ⟨1553840, by rfl⟩ : syracuseStep 2071787 = 3107681) B3107681
theorem B21263093 : Blo 2071435 21263093 := bbase (se 5 (by rfl) ⟨996707, by rfl⟩ : syracuseStep 21263093 = 1993415) (by norm_num)
theorem B14175395 : Blo 2071435 14175395 := bstep (se 1 (by rfl) ⟨10631546, by rfl⟩ : syracuseStep 14175395 = 21263093) B21263093
theorem B9450263 : Blo 2071435 9450263 := bstep (se 1 (by rfl) ⟨7087697, by rfl⟩ : syracuseStep 9450263 = 14175395) B14175395
theorem B6300175 : Blo 2071435 6300175 := bstep (se 1 (by rfl) ⟨4725131, by rfl⟩ : syracuseStep 6300175 = 9450263) B9450263
theorem B8400233 : Blo 2071435 8400233 := bstep (se 2 (by rfl) ⟨3150087, by rfl⟩ : syracuseStep 8400233 = 6300175) B6300175
theorem B22400621 : Blo 2071435 22400621 := bstep (se 3 (by rfl) ⟨4200116, by rfl⟩ : syracuseStep 22400621 = 8400233) B8400233
theorem B14933747 : Blo 2071435 14933747 := bstep (se 1 (by rfl) ⟨11200310, by rfl⟩ : syracuseStep 14933747 = 22400621) B22400621
theorem B39823325 : Blo 2071435 39823325 := bstep (se 3 (by rfl) ⟨7466873, by rfl⟩ : syracuseStep 39823325 = 14933747) B14933747
theorem B26548883 : Blo 2071435 26548883 := bstep (se 1 (by rfl) ⟨19911662, by rfl⟩ : syracuseStep 26548883 = 39823325) B39823325
theorem B17699255 : Blo 2071435 17699255 := bstep (se 1 (by rfl) ⟨13274441, by rfl⟩ : syracuseStep 17699255 = 26548883) B26548883
theorem B11799503 : Blo 2071435 11799503 := bstep (se 1 (by rfl) ⟨8849627, by rfl⟩ : syracuseStep 11799503 = 17699255) B17699255
theorem B7866335 : Blo 2071435 7866335 := bstep (se 1 (by rfl) ⟨5899751, by rfl⟩ : syracuseStep 7866335 = 11799503) B11799503
theorem B5244223 : Blo 2071435 5244223 := bstep (se 1 (by rfl) ⟨3933167, by rfl⟩ : syracuseStep 5244223 = 7866335) B7866335
theorem B6992297 : Blo 2071435 6992297 := bstep (se 2 (by rfl) ⟨2622111, by rfl⟩ : syracuseStep 6992297 = 5244223) B5244223
theorem B4661531 : Blo 2071435 4661531 := bstep (se 1 (by rfl) ⟨3496148, by rfl⟩ : syracuseStep 4661531 = 6992297) B6992297
theorem B3107687 : Blo 2071435 3107687 := bstep (se 1 (by rfl) ⟨2330765, by rfl⟩ : syracuseStep 3107687 = 4661531) B4661531
theorem B2071791 : Blo 2071435 2071791 := bstep (se 1 (by rfl) ⟨1553843, by rfl⟩ : syracuseStep 2071791 = 3107687) B3107687
theorem B3107693 : Blo 2071435 3107693 := bbase (se 3 (by rfl) ⟨582692, by rfl⟩ : syracuseStep 3107693 = 1165385) (by norm_num)
theorem B2071795 : Blo 2071435 2071795 := bstep (se 1 (by rfl) ⟨1553846, by rfl⟩ : syracuseStep 2071795 = 3107693) B3107693
theorem B4661549 : Blo 2071435 4661549 := bbase (se 3 (by rfl) ⟨874040, by rfl⟩ : syracuseStep 4661549 = 1748081) (by norm_num)
theorem B3107699 : Blo 2071435 3107699 := bstep (se 1 (by rfl) ⟨2330774, by rfl⟩ : syracuseStep 3107699 = 4661549) B4661549
theorem B2071799 : Blo 2071435 2071799 := bstep (se 1 (by rfl) ⟨1553849, by rfl⟩ : syracuseStep 2071799 = 3107699) B3107699
theorem B2488973 : Blo 2071435 2488973 := bbase (se 3 (by rfl) ⟨466682, by rfl⟩ : syracuseStep 2488973 = 933365) (by norm_num)
theorem B6637261 : Blo 2071435 6637261 := bstep (se 3 (by rfl) ⟨1244486, by rfl⟩ : syracuseStep 6637261 = 2488973) B2488973
theorem B8849681 : Blo 2071435 8849681 := bstep (se 2 (by rfl) ⟨3318630, by rfl⟩ : syracuseStep 8849681 = 6637261) B6637261
theorem B5899787 : Blo 2071435 5899787 := bstep (se 1 (by rfl) ⟨4424840, by rfl⟩ : syracuseStep 5899787 = 8849681) B8849681
theorem B3933191 : Blo 2071435 3933191 := bstep (se 1 (by rfl) ⟨2949893, by rfl⟩ : syracuseStep 3933191 = 5899787) B5899787
theorem B2622127 : Blo 2071435 2622127 := bstep (se 1 (by rfl) ⟨1966595, by rfl⟩ : syracuseStep 2622127 = 3933191) B3933191
theorem B3496169 : Blo 2071435 3496169 := bstep (se 2 (by rfl) ⟨1311063, by rfl⟩ : syracuseStep 3496169 = 2622127) B2622127
theorem B2330779 : Blo 2071435 2330779 := bstep (se 1 (by rfl) ⟨1748084, by rfl⟩ : syracuseStep 2330779 = 3496169) B3496169
theorem B3107705 : Blo 2071435 3107705 := bstep (se 2 (by rfl) ⟨1165389, by rfl⟩ : syracuseStep 3107705 = 2330779) B2330779
theorem B2071803 : Blo 2071435 2071803 := bstep (se 1 (by rfl) ⟨1553852, by rfl⟩ : syracuseStep 2071803 = 3107705) B3107705
theorem B2242609 : Blo 2071435 2242609 := bbase (se 2 (by rfl) ⟨840978, by rfl⟩ : syracuseStep 2242609 = 1681957) (by norm_num)
theorem B47842325 : Blo 2071435 47842325 := bstep (se 6 (by rfl) ⟨1121304, by rfl⟩ : syracuseStep 47842325 = 2242609) B2242609
theorem B31894883 : Blo 2071435 31894883 := bstep (se 1 (by rfl) ⟨23921162, by rfl⟩ : syracuseStep 31894883 = 47842325) B47842325
theorem B21263255 : Blo 2071435 21263255 := bstep (se 1 (by rfl) ⟨15947441, by rfl⟩ : syracuseStep 21263255 = 31894883) B31894883
theorem B14175503 : Blo 2071435 14175503 := bstep (se 1 (by rfl) ⟨10631627, by rfl⟩ : syracuseStep 14175503 = 21263255) B21263255
theorem B9450335 : Blo 2071435 9450335 := bstep (se 1 (by rfl) ⟨7087751, by rfl⟩ : syracuseStep 9450335 = 14175503) B14175503
theorem B6300223 : Blo 2071435 6300223 := bstep (se 1 (by rfl) ⟨4725167, by rfl⟩ : syracuseStep 6300223 = 9450335) B9450335
theorem B33601189 : Blo 2071435 33601189 := bstep (se 4 (by rfl) ⟨3150111, by rfl⟩ : syracuseStep 33601189 = 6300223) B6300223
theorem B44801585 : Blo 2071435 44801585 := bstep (se 2 (by rfl) ⟨16800594, by rfl⟩ : syracuseStep 44801585 = 33601189) B33601189
theorem B29867723 : Blo 2071435 29867723 := bstep (se 1 (by rfl) ⟨22400792, by rfl⟩ : syracuseStep 29867723 = 44801585) B44801585
theorem B19911815 : Blo 2071435 19911815 := bstep (se 1 (by rfl) ⟨14933861, by rfl⟩ : syracuseStep 19911815 = 29867723) B29867723
theorem B13274543 : Blo 2071435 13274543 := bstep (se 1 (by rfl) ⟨9955907, by rfl⟩ : syracuseStep 13274543 = 19911815) B19911815
theorem B35398781 : Blo 2071435 35398781 := bstep (se 3 (by rfl) ⟨6637271, by rfl⟩ : syracuseStep 35398781 = 13274543) B13274543
theorem B23599187 : Blo 2071435 23599187 := bstep (se 1 (by rfl) ⟨17699390, by rfl⟩ : syracuseStep 23599187 = 35398781) B35398781
theorem B15732791 : Blo 2071435 15732791 := bstep (se 1 (by rfl) ⟨11799593, by rfl⟩ : syracuseStep 15732791 = 23599187) B23599187
theorem B10488527 : Blo 2071435 10488527 := bstep (se 1 (by rfl) ⟨7866395, by rfl⟩ : syracuseStep 10488527 = 15732791) B15732791
theorem B6992351 : Blo 2071435 6992351 := bstep (se 1 (by rfl) ⟨5244263, by rfl⟩ : syracuseStep 6992351 = 10488527) B10488527
theorem B4661567 : Blo 2071435 4661567 := bstep (se 1 (by rfl) ⟨3496175, by rfl⟩ : syracuseStep 4661567 = 6992351) B6992351
theorem B3107711 : Blo 2071435 3107711 := bstep (se 1 (by rfl) ⟨2330783, by rfl⟩ : syracuseStep 3107711 = 4661567) B4661567
theorem B2071807 : Blo 2071435 2071807 := bstep (se 1 (by rfl) ⟨1553855, by rfl⟩ : syracuseStep 2071807 = 3107711) B3107711
theorem B3107717 : Blo 2071435 3107717 := bbase (se 4 (by rfl) ⟨291348, by rfl⟩ : syracuseStep 3107717 = 582697) (by norm_num)
theorem B2071811 : Blo 2071435 2071811 := bstep (se 1 (by rfl) ⟨1553858, by rfl⟩ : syracuseStep 2071811 = 3107717) B3107717
theorem B3496189 : Blo 2071435 3496189 := bbase (se 3 (by rfl) ⟨655535, by rfl⟩ : syracuseStep 3496189 = 1311071) (by norm_num)
theorem B4661585 : Blo 2071435 4661585 := bstep (se 2 (by rfl) ⟨1748094, by rfl⟩ : syracuseStep 4661585 = 3496189) B3496189
theorem B3107723 : Blo 2071435 3107723 := bstep (se 1 (by rfl) ⟨2330792, by rfl⟩ : syracuseStep 3107723 = 4661585) B4661585
theorem B2071815 : Blo 2071435 2071815 := bstep (se 1 (by rfl) ⟨1553861, by rfl⟩ : syracuseStep 2071815 = 3107723) B3107723
theorem B2330797 : Blo 2071435 2330797 := bbase (se 3 (by rfl) ⟨437024, by rfl⟩ : syracuseStep 2330797 = 874049) (by norm_num)
theorem B3107729 : Blo 2071435 3107729 := bstep (se 2 (by rfl) ⟨1165398, by rfl⟩ : syracuseStep 3107729 = 2330797) B2330797
theorem B2071819 : Blo 2071435 2071819 := bstep (se 1 (by rfl) ⟨1553864, by rfl⟩ : syracuseStep 2071819 = 3107729) B3107729
theorem B6992405 : Blo 2071435 6992405 := bbase (se 6 (by rfl) ⟨163884, by rfl⟩ : syracuseStep 6992405 = 327769) (by norm_num)
theorem B4661603 : Blo 2071435 4661603 := bstep (se 1 (by rfl) ⟨3496202, by rfl⟩ : syracuseStep 4661603 = 6992405) B6992405
theorem B3107735 : Blo 2071435 3107735 := bstep (se 1 (by rfl) ⟨2330801, by rfl⟩ : syracuseStep 3107735 = 4661603) B4661603
theorem B2071823 : Blo 2071435 2071823 := bstep (se 1 (by rfl) ⟨1553867, by rfl⟩ : syracuseStep 2071823 = 3107735) B3107735
theorem B3107741 : Blo 2071435 3107741 := bbase (se 3 (by rfl) ⟨582701, by rfl⟩ : syracuseStep 3107741 = 1165403) (by norm_num)
theorem B2071827 : Blo 2071435 2071827 := bstep (se 1 (by rfl) ⟨1553870, by rfl⟩ : syracuseStep 2071827 = 3107741) B3107741
theorem B4661621 : Blo 2071435 4661621 := bbase (se 5 (by rfl) ⟨218513, by rfl⟩ : syracuseStep 4661621 = 437027) (by norm_num)
theorem B3107747 : Blo 2071435 3107747 := bstep (se 1 (by rfl) ⟨2330810, by rfl⟩ : syracuseStep 3107747 = 4661621) B4661621
theorem B2071831 : Blo 2071435 2071831 := bstep (se 1 (by rfl) ⟨1553873, by rfl⟩ : syracuseStep 2071831 = 3107747) B3107747
theorem B3733517 : Blo 2071435 3733517 := bbase (se 3 (by rfl) ⟨700034, by rfl⟩ : syracuseStep 3733517 = 1400069) (by norm_num)
theorem B2489011 : Blo 2071435 2489011 := bstep (se 1 (by rfl) ⟨1866758, by rfl⟩ : syracuseStep 2489011 = 3733517) B3733517
theorem B13274725 : Blo 2071435 13274725 := bstep (se 4 (by rfl) ⟨1244505, by rfl⟩ : syracuseStep 13274725 = 2489011) B2489011
theorem B17699633 : Blo 2071435 17699633 := bstep (se 2 (by rfl) ⟨6637362, by rfl⟩ : syracuseStep 17699633 = 13274725) B13274725
theorem B11799755 : Blo 2071435 11799755 := bstep (se 1 (by rfl) ⟨8849816, by rfl⟩ : syracuseStep 11799755 = 17699633) B17699633
theorem B7866503 : Blo 2071435 7866503 := bstep (se 1 (by rfl) ⟨5899877, by rfl⟩ : syracuseStep 7866503 = 11799755) B11799755
theorem B5244335 : Blo 2071435 5244335 := bstep (se 1 (by rfl) ⟨3933251, by rfl⟩ : syracuseStep 5244335 = 7866503) B7866503
theorem B3496223 : Blo 2071435 3496223 := bstep (se 1 (by rfl) ⟨2622167, by rfl⟩ : syracuseStep 3496223 = 5244335) B5244335
theorem B2330815 : Blo 2071435 2330815 := bstep (se 1 (by rfl) ⟨1748111, by rfl⟩ : syracuseStep 2330815 = 3496223) B3496223
theorem B3107753 : Blo 2071435 3107753 := bstep (se 2 (by rfl) ⟨1165407, by rfl⟩ : syracuseStep 3107753 = 2330815) B2330815
theorem B2071835 : Blo 2071435 2071835 := bstep (se 1 (by rfl) ⟨1553876, by rfl⟩ : syracuseStep 2071835 = 3107753) B3107753
theorem B7866517 : Blo 2071435 7866517 := bbase (se 6 (by rfl) ⟨184371, by rfl⟩ : syracuseStep 7866517 = 368743) (by norm_num)
theorem B10488689 : Blo 2071435 10488689 := bstep (se 2 (by rfl) ⟨3933258, by rfl⟩ : syracuseStep 10488689 = 7866517) B7866517
theorem B6992459 : Blo 2071435 6992459 := bstep (se 1 (by rfl) ⟨5244344, by rfl⟩ : syracuseStep 6992459 = 10488689) B10488689
theorem B4661639 : Blo 2071435 4661639 := bstep (se 1 (by rfl) ⟨3496229, by rfl⟩ : syracuseStep 4661639 = 6992459) B6992459
theorem B3107759 : Blo 2071435 3107759 := bstep (se 1 (by rfl) ⟨2330819, by rfl⟩ : syracuseStep 3107759 = 4661639) B4661639
theorem B2071839 : Blo 2071435 2071839 := bstep (se 1 (by rfl) ⟨1553879, by rfl⟩ : syracuseStep 2071839 = 3107759) B3107759
theorem B3107765 : Blo 2071435 3107765 := bbase (se 5 (by rfl) ⟨145676, by rfl⟩ : syracuseStep 3107765 = 291353) (by norm_num)
theorem B2071843 : Blo 2071435 2071843 := bstep (se 1 (by rfl) ⟨1553882, by rfl⟩ : syracuseStep 2071843 = 3107765) B3107765
theorem B5244365 : Blo 2071435 5244365 := bbase (se 3 (by rfl) ⟨983318, by rfl⟩ : syracuseStep 5244365 = 1966637) (by norm_num)
theorem B3496243 : Blo 2071435 3496243 := bstep (se 1 (by rfl) ⟨2622182, by rfl⟩ : syracuseStep 3496243 = 5244365) B5244365
theorem B4661657 : Blo 2071435 4661657 := bstep (se 2 (by rfl) ⟨1748121, by rfl⟩ : syracuseStep 4661657 = 3496243) B3496243
theorem B3107771 : Blo 2071435 3107771 := bstep (se 1 (by rfl) ⟨2330828, by rfl⟩ : syracuseStep 3107771 = 4661657) B4661657
theorem B2071847 : Blo 2071435 2071847 := bstep (se 1 (by rfl) ⟨1553885, by rfl⟩ : syracuseStep 2071847 = 3107771) B3107771
theorem B2330833 : Blo 2071435 2330833 := bbase (se 2 (by rfl) ⟨874062, by rfl⟩ : syracuseStep 2330833 = 1748125) (by norm_num)
theorem B3107777 : Blo 2071435 3107777 := bstep (se 2 (by rfl) ⟨1165416, by rfl⟩ : syracuseStep 3107777 = 2330833) B2330833
theorem B2071851 : Blo 2071435 2071851 := bstep (se 1 (by rfl) ⟨1553888, by rfl⟩ : syracuseStep 2071851 = 3107777) B3107777
theorem B2800165 : Blo 2071435 2800165 := bbase (se 4 (by rfl) ⟨262515, by rfl⟩ : syracuseStep 2800165 = 525031) (by norm_num)
theorem B3733553 : Blo 2071435 3733553 := bstep (se 2 (by rfl) ⟨1400082, by rfl⟩ : syracuseStep 3733553 = 2800165) B2800165
theorem B9956141 : Blo 2071435 9956141 := bstep (se 3 (by rfl) ⟨1866776, by rfl⟩ : syracuseStep 9956141 = 3733553) B3733553
theorem B6637427 : Blo 2071435 6637427 := bstep (se 1 (by rfl) ⟨4978070, by rfl⟩ : syracuseStep 6637427 = 9956141) B9956141
theorem B4424951 : Blo 2071435 4424951 := bstep (se 1 (by rfl) ⟨3318713, by rfl⟩ : syracuseStep 4424951 = 6637427) B6637427
theorem B2949967 : Blo 2071435 2949967 := bstep (se 1 (by rfl) ⟨2212475, by rfl⟩ : syracuseStep 2949967 = 4424951) B4424951
theorem B3933289 : Blo 2071435 3933289 := bstep (se 2 (by rfl) ⟨1474983, by rfl⟩ : syracuseStep 3933289 = 2949967) B2949967
theorem B5244385 : Blo 2071435 5244385 := bstep (se 2 (by rfl) ⟨1966644, by rfl⟩ : syracuseStep 5244385 = 3933289) B3933289
theorem B6992513 : Blo 2071435 6992513 := bstep (se 2 (by rfl) ⟨2622192, by rfl⟩ : syracuseStep 6992513 = 5244385) B5244385
theorem B4661675 : Blo 2071435 4661675 := bstep (se 1 (by rfl) ⟨3496256, by rfl⟩ : syracuseStep 4661675 = 6992513) B6992513
theorem B3107783 : Blo 2071435 3107783 := bstep (se 1 (by rfl) ⟨2330837, by rfl⟩ : syracuseStep 3107783 = 4661675) B4661675
theorem B2071855 : Blo 2071435 2071855 := bstep (se 1 (by rfl) ⟨1553891, by rfl⟩ : syracuseStep 2071855 = 3107783) B3107783
theorem B3107789 : Blo 2071435 3107789 := bbase (se 3 (by rfl) ⟨582710, by rfl⟩ : syracuseStep 3107789 = 1165421) (by norm_num)
theorem B2071859 : Blo 2071435 2071859 := bstep (se 1 (by rfl) ⟨1553894, by rfl⟩ : syracuseStep 2071859 = 3107789) B3107789
theorem B4661693 : Blo 2071435 4661693 := bbase (se 3 (by rfl) ⟨874067, by rfl⟩ : syracuseStep 4661693 = 1748135) (by norm_num)
theorem B3107795 : Blo 2071435 3107795 := bstep (se 1 (by rfl) ⟨2330846, by rfl⟩ : syracuseStep 3107795 = 4661693) B4661693
theorem B2071863 : Blo 2071435 2071863 := bstep (se 1 (by rfl) ⟨1553897, by rfl⟩ : syracuseStep 2071863 = 3107795) B3107795
theorem B3496277 : Blo 2071435 3496277 := bbase (se 10 (by rfl) ⟨5121, by rfl⟩ : syracuseStep 3496277 = 10243) (by norm_num)
theorem B2330851 : Blo 2071435 2330851 := bstep (se 1 (by rfl) ⟨1748138, by rfl⟩ : syracuseStep 2330851 = 3496277) B3496277
theorem B3107801 : Blo 2071435 3107801 := bstep (se 2 (by rfl) ⟨1165425, by rfl⟩ : syracuseStep 3107801 = 2330851) B2330851
theorem B2071867 : Blo 2071435 2071867 := bstep (se 1 (by rfl) ⟨1553900, by rfl⟩ : syracuseStep 2071867 = 3107801) B3107801
theorem B6637477 : Blo 2071435 6637477 := bbase (se 4 (by rfl) ⟨622263, by rfl⟩ : syracuseStep 6637477 = 1244527) (by norm_num)
theorem B8849969 : Blo 2071435 8849969 := bstep (se 2 (by rfl) ⟨3318738, by rfl⟩ : syracuseStep 8849969 = 6637477) B6637477
theorem B5899979 : Blo 2071435 5899979 := bstep (se 1 (by rfl) ⟨4424984, by rfl⟩ : syracuseStep 5899979 = 8849969) B8849969
theorem B15733277 : Blo 2071435 15733277 := bstep (se 3 (by rfl) ⟨2949989, by rfl⟩ : syracuseStep 15733277 = 5899979) B5899979
theorem B10488851 : Blo 2071435 10488851 := bstep (se 1 (by rfl) ⟨7866638, by rfl⟩ : syracuseStep 10488851 = 15733277) B15733277
theorem B6992567 : Blo 2071435 6992567 := bstep (se 1 (by rfl) ⟨5244425, by rfl⟩ : syracuseStep 6992567 = 10488851) B10488851
theorem B4661711 : Blo 2071435 4661711 := bstep (se 1 (by rfl) ⟨3496283, by rfl⟩ : syracuseStep 4661711 = 6992567) B6992567
theorem B3107807 : Blo 2071435 3107807 := bstep (se 1 (by rfl) ⟨2330855, by rfl⟩ : syracuseStep 3107807 = 4661711) B4661711
theorem B2071871 : Blo 2071435 2071871 := bstep (se 1 (by rfl) ⟨1553903, by rfl⟩ : syracuseStep 2071871 = 3107807) B3107807
theorem B3107813 : Blo 2071435 3107813 := bbase (se 4 (by rfl) ⟨291357, by rfl⟩ : syracuseStep 3107813 = 582715) (by norm_num)
theorem B2071875 : Blo 2071435 2071875 := bstep (se 1 (by rfl) ⟨1553906, by rfl⟩ : syracuseStep 2071875 = 3107813) B3107813
theorem B8850005 : Blo 2071435 8850005 := bbase (se 8 (by rfl) ⟨51855, by rfl⟩ : syracuseStep 8850005 = 103711) (by norm_num)
theorem B5900003 : Blo 2071435 5900003 := bstep (se 1 (by rfl) ⟨4425002, by rfl⟩ : syracuseStep 5900003 = 8850005) B8850005
theorem B3933335 : Blo 2071435 3933335 := bstep (se 1 (by rfl) ⟨2950001, by rfl⟩ : syracuseStep 3933335 = 5900003) B5900003
theorem B2622223 : Blo 2071435 2622223 := bstep (se 1 (by rfl) ⟨1966667, by rfl⟩ : syracuseStep 2622223 = 3933335) B3933335
theorem B3496297 : Blo 2071435 3496297 := bstep (se 2 (by rfl) ⟨1311111, by rfl⟩ : syracuseStep 3496297 = 2622223) B2622223
theorem B4661729 : Blo 2071435 4661729 := bstep (se 2 (by rfl) ⟨1748148, by rfl⟩ : syracuseStep 4661729 = 3496297) B3496297
theorem B3107819 : Blo 2071435 3107819 := bstep (se 1 (by rfl) ⟨2330864, by rfl⟩ : syracuseStep 3107819 = 4661729) B4661729
theorem B2071879 : Blo 2071435 2071879 := bstep (se 1 (by rfl) ⟨1553909, by rfl⟩ : syracuseStep 2071879 = 3107819) B3107819
theorem B2330869 : Blo 2071435 2330869 := bbase (se 5 (by rfl) ⟨109259, by rfl⟩ : syracuseStep 2330869 = 218519) (by norm_num)
theorem B3107825 : Blo 2071435 3107825 := bstep (se 2 (by rfl) ⟨1165434, by rfl⟩ : syracuseStep 3107825 = 2330869) B2330869
theorem B2071883 : Blo 2071435 2071883 := bstep (se 1 (by rfl) ⟨1553912, by rfl⟩ : syracuseStep 2071883 = 3107825) B3107825
theorem B2622233 : Blo 2071435 2622233 := bbase (se 2 (by rfl) ⟨983337, by rfl⟩ : syracuseStep 2622233 = 1966675) (by norm_num)
theorem B6992621 : Blo 2071435 6992621 := bstep (se 3 (by rfl) ⟨1311116, by rfl⟩ : syracuseStep 6992621 = 2622233) B2622233
theorem B4661747 : Blo 2071435 4661747 := bstep (se 1 (by rfl) ⟨3496310, by rfl⟩ : syracuseStep 4661747 = 6992621) B6992621
theorem B3107831 : Blo 2071435 3107831 := bstep (se 1 (by rfl) ⟨2330873, by rfl⟩ : syracuseStep 3107831 = 4661747) B4661747
theorem B2071887 : Blo 2071435 2071887 := bstep (se 1 (by rfl) ⟨1553915, by rfl⟩ : syracuseStep 2071887 = 3107831) B3107831
theorem B3107837 : Blo 2071435 3107837 := bbase (se 3 (by rfl) ⟨582719, by rfl⟩ : syracuseStep 3107837 = 1165439) (by norm_num)
theorem B2071891 : Blo 2071435 2071891 := bstep (se 1 (by rfl) ⟨1553918, by rfl⟩ : syracuseStep 2071891 = 3107837) B3107837
theorem B4661765 : Blo 2071435 4661765 := bbase (se 4 (by rfl) ⟨437040, by rfl⟩ : syracuseStep 4661765 = 874081) (by norm_num)
theorem B3107843 : Blo 2071435 3107843 := bstep (se 1 (by rfl) ⟨2330882, by rfl⟩ : syracuseStep 3107843 = 4661765) B4661765
theorem B2071895 : Blo 2071435 2071895 := bstep (se 1 (by rfl) ⟨1553921, by rfl⟩ : syracuseStep 2071895 = 3107843) B3107843
theorem B3933373 : Blo 2071435 3933373 := bbase (se 3 (by rfl) ⟨737507, by rfl⟩ : syracuseStep 3933373 = 1475015) (by norm_num)
theorem B5244497 : Blo 2071435 5244497 := bstep (se 2 (by rfl) ⟨1966686, by rfl⟩ : syracuseStep 5244497 = 3933373) B3933373
theorem B3496331 : Blo 2071435 3496331 := bstep (se 1 (by rfl) ⟨2622248, by rfl⟩ : syracuseStep 3496331 = 5244497) B5244497
theorem B2330887 : Blo 2071435 2330887 := bstep (se 1 (by rfl) ⟨1748165, by rfl⟩ : syracuseStep 2330887 = 3496331) B3496331
theorem B3107849 : Blo 2071435 3107849 := bstep (se 2 (by rfl) ⟨1165443, by rfl⟩ : syracuseStep 3107849 = 2330887) B2330887
theorem B2071899 : Blo 2071435 2071899 := bstep (se 1 (by rfl) ⟨1553924, by rfl⟩ : syracuseStep 2071899 = 3107849) B3107849
theorem B10489013 : Blo 2071435 10489013 := bbase (se 5 (by rfl) ⟨491672, by rfl⟩ : syracuseStep 10489013 = 983345) (by norm_num)
theorem B6992675 : Blo 2071435 6992675 := bstep (se 1 (by rfl) ⟨5244506, by rfl⟩ : syracuseStep 6992675 = 10489013) B10489013
theorem B4661783 : Blo 2071435 4661783 := bstep (se 1 (by rfl) ⟨3496337, by rfl⟩ : syracuseStep 4661783 = 6992675) B6992675
theorem B3107855 : Blo 2071435 3107855 := bstep (se 1 (by rfl) ⟨2330891, by rfl⟩ : syracuseStep 3107855 = 4661783) B4661783
theorem B2071903 : Blo 2071435 2071903 := bstep (se 1 (by rfl) ⟨1553927, by rfl⟩ : syracuseStep 2071903 = 3107855) B3107855
theorem B3107861 : Blo 2071435 3107861 := bbase (se 6 (by rfl) ⟨72840, by rfl⟩ : syracuseStep 3107861 = 145681) (by norm_num)
theorem B2071907 : Blo 2071435 2071907 := bstep (se 1 (by rfl) ⟨1553930, by rfl⟩ : syracuseStep 2071907 = 3107861) B3107861
theorem B14934613 : Blo 2071435 14934613 := bbase (se 8 (by rfl) ⟨87507, by rfl⟩ : syracuseStep 14934613 = 175015) (by norm_num)
theorem B19912817 : Blo 2071435 19912817 := bstep (se 2 (by rfl) ⟨7467306, by rfl⟩ : syracuseStep 19912817 = 14934613) B14934613
theorem B13275211 : Blo 2071435 13275211 := bstep (se 1 (by rfl) ⟨9956408, by rfl⟩ : syracuseStep 13275211 = 19912817) B19912817
theorem B17700281 : Blo 2071435 17700281 := bstep (se 2 (by rfl) ⟨6637605, by rfl⟩ : syracuseStep 17700281 = 13275211) B13275211
theorem B11800187 : Blo 2071435 11800187 := bstep (se 1 (by rfl) ⟨8850140, by rfl⟩ : syracuseStep 11800187 = 17700281) B17700281
theorem B7866791 : Blo 2071435 7866791 := bstep (se 1 (by rfl) ⟨5900093, by rfl⟩ : syracuseStep 7866791 = 11800187) B11800187
theorem B5244527 : Blo 2071435 5244527 := bstep (se 1 (by rfl) ⟨3933395, by rfl⟩ : syracuseStep 5244527 = 7866791) B7866791
theorem B3496351 : Blo 2071435 3496351 := bstep (se 1 (by rfl) ⟨2622263, by rfl⟩ : syracuseStep 3496351 = 5244527) B5244527
theorem B4661801 : Blo 2071435 4661801 := bstep (se 2 (by rfl) ⟨1748175, by rfl⟩ : syracuseStep 4661801 = 3496351) B3496351
theorem B3107867 : Blo 2071435 3107867 := bstep (se 1 (by rfl) ⟨2330900, by rfl⟩ : syracuseStep 3107867 = 4661801) B4661801
theorem B2071911 : Blo 2071435 2071911 := bstep (se 1 (by rfl) ⟨1553933, by rfl⟩ : syracuseStep 2071911 = 3107867) B3107867
theorem B2330905 : Blo 2071435 2330905 := bbase (se 2 (by rfl) ⟨874089, by rfl⟩ : syracuseStep 2330905 = 1748179) (by norm_num)
theorem B3107873 : Blo 2071435 3107873 := bstep (se 2 (by rfl) ⟨1165452, by rfl⟩ : syracuseStep 3107873 = 2330905) B2330905
theorem B2071915 : Blo 2071435 2071915 := bstep (se 1 (by rfl) ⟨1553936, by rfl⟩ : syracuseStep 2071915 = 3107873) B3107873
theorem B7866821 : Blo 2071435 7866821 := bbase (se 4 (by rfl) ⟨737514, by rfl⟩ : syracuseStep 7866821 = 1475029) (by norm_num)
theorem B5244547 : Blo 2071435 5244547 := bstep (se 1 (by rfl) ⟨3933410, by rfl⟩ : syracuseStep 5244547 = 7866821) B7866821
theorem B6992729 : Blo 2071435 6992729 := bstep (se 2 (by rfl) ⟨2622273, by rfl⟩ : syracuseStep 6992729 = 5244547) B5244547
theorem B4661819 : Blo 2071435 4661819 := bstep (se 1 (by rfl) ⟨3496364, by rfl⟩ : syracuseStep 4661819 = 6992729) B6992729
theorem B3107879 : Blo 2071435 3107879 := bstep (se 1 (by rfl) ⟨2330909, by rfl⟩ : syracuseStep 3107879 = 4661819) B4661819
theorem B2071919 : Blo 2071435 2071919 := bstep (se 1 (by rfl) ⟨1553939, by rfl⟩ : syracuseStep 2071919 = 3107879) B3107879
theorem B3107885 : Blo 2071435 3107885 := bbase (se 3 (by rfl) ⟨582728, by rfl⟩ : syracuseStep 3107885 = 1165457) (by norm_num)
theorem B2071923 : Blo 2071435 2071923 := bstep (se 1 (by rfl) ⟨1553942, by rfl⟩ : syracuseStep 2071923 = 3107885) B3107885
theorem B4661837 : Blo 2071435 4661837 := bbase (se 3 (by rfl) ⟨874094, by rfl⟩ : syracuseStep 4661837 = 1748189) (by norm_num)
theorem B3107891 : Blo 2071435 3107891 := bstep (se 1 (by rfl) ⟨2330918, by rfl⟩ : syracuseStep 3107891 = 4661837) B4661837
theorem B2071927 : Blo 2071435 2071927 := bstep (se 1 (by rfl) ⟨1553945, by rfl⟩ : syracuseStep 2071927 = 3107891) B3107891
theorem B2622289 : Blo 2071435 2622289 := bbase (se 2 (by rfl) ⟨983358, by rfl⟩ : syracuseStep 2622289 = 1966717) (by norm_num)
theorem B3496385 : Blo 2071435 3496385 := bstep (se 2 (by rfl) ⟨1311144, by rfl⟩ : syracuseStep 3496385 = 2622289) B2622289
theorem B2330923 : Blo 2071435 2330923 := bstep (se 1 (by rfl) ⟨1748192, by rfl⟩ : syracuseStep 2330923 = 3496385) B3496385
theorem B3107897 : Blo 2071435 3107897 := bstep (se 2 (by rfl) ⟨1165461, by rfl⟩ : syracuseStep 3107897 = 2330923) B2330923
theorem B2071931 : Blo 2071435 2071931 := bstep (se 1 (by rfl) ⟨1553948, by rfl⟩ : syracuseStep 2071931 = 3107897) B3107897
theorem B2100205 : Blo 2071435 2100205 := bbase (se 3 (by rfl) ⟨393788, by rfl⟩ : syracuseStep 2100205 = 787577) (by norm_num)
theorem B2800273 : Blo 2071435 2800273 := bstep (se 2 (by rfl) ⟨1050102, by rfl⟩ : syracuseStep 2800273 = 2100205) B2100205
theorem B3733697 : Blo 2071435 3733697 := bstep (se 2 (by rfl) ⟨1400136, by rfl⟩ : syracuseStep 3733697 = 2800273) B2800273
theorem B2489131 : Blo 2071435 2489131 := bstep (se 1 (by rfl) ⟨1866848, by rfl⟩ : syracuseStep 2489131 = 3733697) B3733697
theorem B3318841 : Blo 2071435 3318841 := bstep (se 2 (by rfl) ⟨1244565, by rfl⟩ : syracuseStep 3318841 = 2489131) B2489131
theorem B4425121 : Blo 2071435 4425121 := bstep (se 2 (by rfl) ⟨1659420, by rfl⟩ : syracuseStep 4425121 = 3318841) B3318841
theorem B23600645 : Blo 2071435 23600645 := bstep (se 4 (by rfl) ⟨2212560, by rfl⟩ : syracuseStep 23600645 = 4425121) B4425121
theorem B15733763 : Blo 2071435 15733763 := bstep (se 1 (by rfl) ⟨11800322, by rfl⟩ : syracuseStep 15733763 = 23600645) B23600645
theorem B10489175 : Blo 2071435 10489175 := bstep (se 1 (by rfl) ⟨7866881, by rfl⟩ : syracuseStep 10489175 = 15733763) B15733763
theorem B6992783 : Blo 2071435 6992783 := bstep (se 1 (by rfl) ⟨5244587, by rfl⟩ : syracuseStep 6992783 = 10489175) B10489175
theorem B4661855 : Blo 2071435 4661855 := bstep (se 1 (by rfl) ⟨3496391, by rfl⟩ : syracuseStep 4661855 = 6992783) B6992783
theorem B3107903 : Blo 2071435 3107903 := bstep (se 1 (by rfl) ⟨2330927, by rfl⟩ : syracuseStep 3107903 = 4661855) B4661855
theorem B2071935 : Blo 2071435 2071935 := bstep (se 1 (by rfl) ⟨1553951, by rfl⟩ : syracuseStep 2071935 = 3107903) B3107903
theorem B3107909 : Blo 2071435 3107909 := bbase (se 4 (by rfl) ⟨291366, by rfl⟩ : syracuseStep 3107909 = 582733) (by norm_num)
theorem B2071939 : Blo 2071435 2071939 := bstep (se 1 (by rfl) ⟨1553954, by rfl⟩ : syracuseStep 2071939 = 3107909) B3107909
theorem B3496405 : Blo 2071435 3496405 := bbase (se 7 (by rfl) ⟨40973, by rfl⟩ : syracuseStep 3496405 = 81947) (by norm_num)
theorem B4661873 : Blo 2071435 4661873 := bstep (se 2 (by rfl) ⟨1748202, by rfl⟩ : syracuseStep 4661873 = 3496405) B3496405
theorem B3107915 : Blo 2071435 3107915 := bstep (se 1 (by rfl) ⟨2330936, by rfl⟩ : syracuseStep 3107915 = 4661873) B4661873
theorem B2071943 : Blo 2071435 2071943 := bstep (se 1 (by rfl) ⟨1553957, by rfl⟩ : syracuseStep 2071943 = 3107915) B3107915
theorem B2330941 : Blo 2071435 2330941 := bbase (se 3 (by rfl) ⟨437051, by rfl⟩ : syracuseStep 2330941 = 874103) (by norm_num)
theorem B3107921 : Blo 2071435 3107921 := bstep (se 2 (by rfl) ⟨1165470, by rfl⟩ : syracuseStep 3107921 = 2330941) B2330941
theorem B2071947 : Blo 2071435 2071947 := bstep (se 1 (by rfl) ⟨1553960, by rfl⟩ : syracuseStep 2071947 = 3107921) B3107921
theorem B6992837 : Blo 2071435 6992837 := bbase (se 4 (by rfl) ⟨655578, by rfl⟩ : syracuseStep 6992837 = 1311157) (by norm_num)
theorem B4661891 : Blo 2071435 4661891 := bstep (se 1 (by rfl) ⟨3496418, by rfl⟩ : syracuseStep 4661891 = 6992837) B6992837
theorem B3107927 : Blo 2071435 3107927 := bstep (se 1 (by rfl) ⟨2330945, by rfl⟩ : syracuseStep 3107927 = 4661891) B4661891
theorem B2071951 : Blo 2071435 2071951 := bstep (se 1 (by rfl) ⟨1553963, by rfl⟩ : syracuseStep 2071951 = 3107927) B3107927
theorem B3107933 : Blo 2071435 3107933 := bbase (se 3 (by rfl) ⟨582737, by rfl⟩ : syracuseStep 3107933 = 1165475) (by norm_num)
theorem B2071955 : Blo 2071435 2071955 := bstep (se 1 (by rfl) ⟨1553966, by rfl⟩ : syracuseStep 2071955 = 3107933) B3107933
theorem B4661909 : Blo 2071435 4661909 := bbase (se 6 (by rfl) ⟨109263, by rfl⟩ : syracuseStep 4661909 = 218527) (by norm_num)
theorem B3107939 : Blo 2071435 3107939 := bstep (se 1 (by rfl) ⟨2330954, by rfl⟩ : syracuseStep 3107939 = 4661909) B4661909
theorem B2071959 : Blo 2071435 2071959 := bstep (se 1 (by rfl) ⟨1553969, by rfl⟩ : syracuseStep 2071959 = 3107939) B3107939
theorem B2128889 : Blo 2071435 2128889 := bbase (se 2 (by rfl) ⟨798333, by rfl⟩ : syracuseStep 2128889 = 1596667) (by norm_num)
theorem B5677037 : Blo 2071435 5677037 := bstep (se 3 (by rfl) ⟨1064444, by rfl⟩ : syracuseStep 5677037 = 2128889) B2128889
theorem B3784691 : Blo 2071435 3784691 := bstep (se 1 (by rfl) ⟨2838518, by rfl⟩ : syracuseStep 3784691 = 5677037) B5677037
theorem B10092509 : Blo 2071435 10092509 := bstep (se 3 (by rfl) ⟨1892345, by rfl⟩ : syracuseStep 10092509 = 3784691) B3784691
theorem B6728339 : Blo 2071435 6728339 := bstep (se 1 (by rfl) ⟨5046254, by rfl⟩ : syracuseStep 6728339 = 10092509) B10092509
theorem B4485559 : Blo 2071435 4485559 := bstep (se 1 (by rfl) ⟨3364169, by rfl⟩ : syracuseStep 4485559 = 6728339) B6728339
theorem B5980745 : Blo 2071435 5980745 := bstep (se 2 (by rfl) ⟨2242779, by rfl⟩ : syracuseStep 5980745 = 4485559) B4485559
theorem B3987163 : Blo 2071435 3987163 := bstep (se 1 (by rfl) ⟨2990372, by rfl⟩ : syracuseStep 3987163 = 5980745) B5980745
theorem B21264869 : Blo 2071435 21264869 := bstep (se 4 (by rfl) ⟨1993581, by rfl⟩ : syracuseStep 21264869 = 3987163) B3987163
theorem B14176579 : Blo 2071435 14176579 := bstep (se 1 (by rfl) ⟨10632434, by rfl⟩ : syracuseStep 14176579 = 21264869) B21264869
theorem B18902105 : Blo 2071435 18902105 := bstep (se 2 (by rfl) ⟨7088289, by rfl⟩ : syracuseStep 18902105 = 14176579) B14176579
theorem B12601403 : Blo 2071435 12601403 := bstep (se 1 (by rfl) ⟨9451052, by rfl⟩ : syracuseStep 12601403 = 18902105) B18902105
theorem B8400935 : Blo 2071435 8400935 := bstep (se 1 (by rfl) ⟨6300701, by rfl⟩ : syracuseStep 8400935 = 12601403) B12601403
theorem B5600623 : Blo 2071435 5600623 := bstep (se 1 (by rfl) ⟨4200467, by rfl⟩ : syracuseStep 5600623 = 8400935) B8400935
theorem B7467497 : Blo 2071435 7467497 := bstep (se 2 (by rfl) ⟨2800311, by rfl⟩ : syracuseStep 7467497 = 5600623) B5600623
theorem B4978331 : Blo 2071435 4978331 := bstep (se 1 (by rfl) ⟨3733748, by rfl⟩ : syracuseStep 4978331 = 7467497) B7467497
theorem B3318887 : Blo 2071435 3318887 := bstep (se 1 (by rfl) ⟨2489165, by rfl⟩ : syracuseStep 3318887 = 4978331) B4978331
theorem B2212591 : Blo 2071435 2212591 := bstep (se 1 (by rfl) ⟨1659443, by rfl⟩ : syracuseStep 2212591 = 3318887) B3318887
theorem B2950121 : Blo 2071435 2950121 := bstep (se 2 (by rfl) ⟨1106295, by rfl⟩ : syracuseStep 2950121 = 2212591) B2212591
theorem B7866989 : Blo 2071435 7866989 := bstep (se 3 (by rfl) ⟨1475060, by rfl⟩ : syracuseStep 7866989 = 2950121) B2950121
theorem B5244659 : Blo 2071435 5244659 := bstep (se 1 (by rfl) ⟨3933494, by rfl⟩ : syracuseStep 5244659 = 7866989) B7866989
theorem B3496439 : Blo 2071435 3496439 := bstep (se 1 (by rfl) ⟨2622329, by rfl⟩ : syracuseStep 3496439 = 5244659) B5244659
theorem B2330959 : Blo 2071435 2330959 := bstep (se 1 (by rfl) ⟨1748219, by rfl⟩ : syracuseStep 2330959 = 3496439) B3496439
theorem B3107945 : Blo 2071435 3107945 := bstep (se 2 (by rfl) ⟨1165479, by rfl⟩ : syracuseStep 3107945 = 2330959) B2330959
theorem B2071963 : Blo 2071435 2071963 := bstep (se 1 (by rfl) ⟨1553972, by rfl⟩ : syracuseStep 2071963 = 3107945) B3107945
theorem B9956677 : Blo 2071435 9956677 := bbase (se 4 (by rfl) ⟨933438, by rfl⟩ : syracuseStep 9956677 = 1866877) (by norm_num)
theorem B13275569 : Blo 2071435 13275569 := bstep (se 2 (by rfl) ⟨4978338, by rfl⟩ : syracuseStep 13275569 = 9956677) B9956677
theorem B8850379 : Blo 2071435 8850379 := bstep (se 1 (by rfl) ⟨6637784, by rfl⟩ : syracuseStep 8850379 = 13275569) B13275569
theorem B11800505 : Blo 2071435 11800505 := bstep (se 2 (by rfl) ⟨4425189, by rfl⟩ : syracuseStep 11800505 = 8850379) B8850379
theorem B7867003 : Blo 2071435 7867003 := bstep (se 1 (by rfl) ⟨5900252, by rfl⟩ : syracuseStep 7867003 = 11800505) B11800505
theorem B10489337 : Blo 2071435 10489337 := bstep (se 2 (by rfl) ⟨3933501, by rfl⟩ : syracuseStep 10489337 = 7867003) B7867003
theorem B6992891 : Blo 2071435 6992891 := bstep (se 1 (by rfl) ⟨5244668, by rfl⟩ : syracuseStep 6992891 = 10489337) B10489337
theorem B4661927 : Blo 2071435 4661927 := bstep (se 1 (by rfl) ⟨3496445, by rfl⟩ : syracuseStep 4661927 = 6992891) B6992891
theorem B3107951 : Blo 2071435 3107951 := bstep (se 1 (by rfl) ⟨2330963, by rfl⟩ : syracuseStep 3107951 = 4661927) B4661927
theorem B2071967 : Blo 2071435 2071967 := bstep (se 1 (by rfl) ⟨1553975, by rfl⟩ : syracuseStep 2071967 = 3107951) B3107951
theorem B3107957 : Blo 2071435 3107957 := bbase (se 5 (by rfl) ⟨145685, by rfl⟩ : syracuseStep 3107957 = 291371) (by norm_num)
theorem B2071971 : Blo 2071435 2071971 := bstep (se 1 (by rfl) ⟨1553978, by rfl⟩ : syracuseStep 2071971 = 3107957) B3107957
theorem B3933517 : Blo 2071435 3933517 := bbase (se 3 (by rfl) ⟨737534, by rfl⟩ : syracuseStep 3933517 = 1475069) (by norm_num)
theorem B5244689 : Blo 2071435 5244689 := bstep (se 2 (by rfl) ⟨1966758, by rfl⟩ : syracuseStep 5244689 = 3933517) B3933517
theorem B3496459 : Blo 2071435 3496459 := bstep (se 1 (by rfl) ⟨2622344, by rfl⟩ : syracuseStep 3496459 = 5244689) B5244689
theorem B4661945 : Blo 2071435 4661945 := bstep (se 2 (by rfl) ⟨1748229, by rfl⟩ : syracuseStep 4661945 = 3496459) B3496459
theorem B3107963 : Blo 2071435 3107963 := bstep (se 1 (by rfl) ⟨2330972, by rfl⟩ : syracuseStep 3107963 = 4661945) B4661945
theorem B2071975 : Blo 2071435 2071975 := bstep (se 1 (by rfl) ⟨1553981, by rfl⟩ : syracuseStep 2071975 = 3107963) B3107963
theorem B2330977 : Blo 2071435 2330977 := bbase (se 2 (by rfl) ⟨874116, by rfl⟩ : syracuseStep 2330977 = 1748233) (by norm_num)
theorem B3107969 : Blo 2071435 3107969 := bstep (se 2 (by rfl) ⟨1165488, by rfl⟩ : syracuseStep 3107969 = 2330977) B2330977
theorem B2071979 : Blo 2071435 2071979 := bstep (se 1 (by rfl) ⟨1553984, by rfl⟩ : syracuseStep 2071979 = 3107969) B3107969
theorem B5244709 : Blo 2071435 5244709 := bbase (se 4 (by rfl) ⟨491691, by rfl⟩ : syracuseStep 5244709 = 983383) (by norm_num)
theorem B6992945 : Blo 2071435 6992945 := bstep (se 2 (by rfl) ⟨2622354, by rfl⟩ : syracuseStep 6992945 = 5244709) B5244709
theorem B4661963 : Blo 2071435 4661963 := bstep (se 1 (by rfl) ⟨3496472, by rfl⟩ : syracuseStep 4661963 = 6992945) B6992945
theorem B3107975 : Blo 2071435 3107975 := bstep (se 1 (by rfl) ⟨2330981, by rfl⟩ : syracuseStep 3107975 = 4661963) B4661963
theorem B2071983 : Blo 2071435 2071983 := bstep (se 1 (by rfl) ⟨1553987, by rfl⟩ : syracuseStep 2071983 = 3107975) B3107975
theorem B3107981 : Blo 2071435 3107981 := bbase (se 3 (by rfl) ⟨582746, by rfl⟩ : syracuseStep 3107981 = 1165493) (by norm_num)
theorem B2071987 : Blo 2071435 2071987 := bstep (se 1 (by rfl) ⟨1553990, by rfl⟩ : syracuseStep 2071987 = 3107981) B3107981
theorem B4661981 : Blo 2071435 4661981 := bbase (se 3 (by rfl) ⟨874121, by rfl⟩ : syracuseStep 4661981 = 1748243) (by norm_num)
theorem B3107987 : Blo 2071435 3107987 := bstep (se 1 (by rfl) ⟨2330990, by rfl⟩ : syracuseStep 3107987 = 4661981) B4661981
theorem B2071991 : Blo 2071435 2071991 := bstep (se 1 (by rfl) ⟨1553993, by rfl⟩ : syracuseStep 2071991 = 3107987) B3107987
theorem B3496493 : Blo 2071435 3496493 := bbase (se 3 (by rfl) ⟨655592, by rfl⟩ : syracuseStep 3496493 = 1311185) (by norm_num)
theorem B2330995 : Blo 2071435 2330995 := bstep (se 1 (by rfl) ⟨1748246, by rfl⟩ : syracuseStep 2330995 = 3496493) B3496493
theorem B3107993 : Blo 2071435 3107993 := bstep (se 2 (by rfl) ⟨1165497, by rfl⟩ : syracuseStep 3107993 = 2330995) B2330995
theorem B2071995 : Blo 2071435 2071995 := bstep (se 1 (by rfl) ⟨1553996, by rfl⟩ : syracuseStep 2071995 = 3107993) B3107993
theorem B13640501 : Blo 2071435 13640501 := bbase (se 5 (by rfl) ⟨639398, by rfl⟩ : syracuseStep 13640501 = 1278797) (by norm_num)
theorem B9093667 : Blo 2071435 9093667 := bstep (se 1 (by rfl) ⟨6820250, by rfl⟩ : syracuseStep 9093667 = 13640501) B13640501
theorem B12124889 : Blo 2071435 12124889 := bstep (se 2 (by rfl) ⟨4546833, by rfl⟩ : syracuseStep 12124889 = 9093667) B9093667
theorem B8083259 : Blo 2071435 8083259 := bstep (se 1 (by rfl) ⟨6062444, by rfl⟩ : syracuseStep 8083259 = 12124889) B12124889
theorem B5388839 : Blo 2071435 5388839 := bstep (se 1 (by rfl) ⟨4041629, by rfl⟩ : syracuseStep 5388839 = 8083259) B8083259
theorem B3592559 : Blo 2071435 3592559 := bstep (se 1 (by rfl) ⟨2694419, by rfl⟩ : syracuseStep 3592559 = 5388839) B5388839
theorem B9580157 : Blo 2071435 9580157 := bstep (se 3 (by rfl) ⟨1796279, by rfl⟩ : syracuseStep 9580157 = 3592559) B3592559
theorem B6386771 : Blo 2071435 6386771 := bstep (se 1 (by rfl) ⟨4790078, by rfl⟩ : syracuseStep 6386771 = 9580157) B9580157
theorem B17031389 : Blo 2071435 17031389 := bstep (se 3 (by rfl) ⟨3193385, by rfl⟩ : syracuseStep 17031389 = 6386771) B6386771
theorem B45417037 : Blo 2071435 45417037 := bstep (se 3 (by rfl) ⟨8515694, by rfl⟩ : syracuseStep 45417037 = 17031389) B17031389
theorem B60556049 : Blo 2071435 60556049 := bstep (se 2 (by rfl) ⟨22708518, by rfl⟩ : syracuseStep 60556049 = 45417037) B45417037
theorem B40370699 : Blo 2071435 40370699 := bstep (se 1 (by rfl) ⟨30278024, by rfl⟩ : syracuseStep 40370699 = 60556049) B60556049
theorem B26913799 : Blo 2071435 26913799 := bstep (se 1 (by rfl) ⟨20185349, by rfl⟩ : syracuseStep 26913799 = 40370699) B40370699
theorem B143540261 : Blo 2071435 143540261 := bstep (se 4 (by rfl) ⟨13456899, by rfl⟩ : syracuseStep 143540261 = 26913799) B26913799
theorem B95693507 : Blo 2071435 95693507 := bstep (se 1 (by rfl) ⟨71770130, by rfl⟩ : syracuseStep 95693507 = 143540261) B143540261
theorem B63795671 : Blo 2071435 63795671 := bstep (se 1 (by rfl) ⟨47846753, by rfl⟩ : syracuseStep 63795671 = 95693507) B95693507
theorem B42530447 : Blo 2071435 42530447 := bstep (se 1 (by rfl) ⟨31897835, by rfl⟩ : syracuseStep 42530447 = 63795671) B63795671
theorem B113414525 : Blo 2071435 113414525 := bstep (se 3 (by rfl) ⟨21265223, by rfl⟩ : syracuseStep 113414525 = 42530447) B42530447
theorem B75609683 : Blo 2071435 75609683 := bstep (se 1 (by rfl) ⟨56707262, by rfl⟩ : syracuseStep 75609683 = 113414525) B113414525
theorem B50406455 : Blo 2071435 50406455 := bstep (se 1 (by rfl) ⟨37804841, by rfl⟩ : syracuseStep 50406455 = 75609683) B75609683
theorem B33604303 : Blo 2071435 33604303 := bstep (se 1 (by rfl) ⟨25203227, by rfl⟩ : syracuseStep 33604303 = 50406455) B50406455
theorem B44805737 : Blo 2071435 44805737 := bstep (se 2 (by rfl) ⟨16802151, by rfl⟩ : syracuseStep 44805737 = 33604303) B33604303
theorem B29870491 : Blo 2071435 29870491 := bstep (se 1 (by rfl) ⟨22402868, by rfl⟩ : syracuseStep 29870491 = 44805737) B44805737
theorem B39827321 : Blo 2071435 39827321 := bstep (se 2 (by rfl) ⟨14935245, by rfl⟩ : syracuseStep 39827321 = 29870491) B29870491
theorem B26551547 : Blo 2071435 26551547 := bstep (se 1 (by rfl) ⟨19913660, by rfl⟩ : syracuseStep 26551547 = 39827321) B39827321
theorem B17701031 : Blo 2071435 17701031 := bstep (se 1 (by rfl) ⟨13275773, by rfl⟩ : syracuseStep 17701031 = 26551547) B26551547
theorem B11800687 : Blo 2071435 11800687 := bstep (se 1 (by rfl) ⟨8850515, by rfl⟩ : syracuseStep 11800687 = 17701031) B17701031
theorem B15734249 : Blo 2071435 15734249 := bstep (se 2 (by rfl) ⟨5900343, by rfl⟩ : syracuseStep 15734249 = 11800687) B11800687
theorem B10489499 : Blo 2071435 10489499 := bstep (se 1 (by rfl) ⟨7867124, by rfl⟩ : syracuseStep 10489499 = 15734249) B15734249
theorem B6992999 : Blo 2071435 6992999 := bstep (se 1 (by rfl) ⟨5244749, by rfl⟩ : syracuseStep 6992999 = 10489499) B10489499
theorem B4661999 : Blo 2071435 4661999 := bstep (se 1 (by rfl) ⟨3496499, by rfl⟩ : syracuseStep 4661999 = 6992999) B6992999
theorem B3107999 : Blo 2071435 3107999 := bstep (se 1 (by rfl) ⟨2330999, by rfl⟩ : syracuseStep 3107999 = 4661999) B4661999
theorem B2071999 : Blo 2071435 2071999 := bstep (se 1 (by rfl) ⟨1553999, by rfl⟩ : syracuseStep 2071999 = 3107999) B3107999
theorem B3108005 : Blo 2071435 3108005 := bbase (se 4 (by rfl) ⟨291375, by rfl⟩ : syracuseStep 3108005 = 582751) (by norm_num)
theorem B2072003 : Blo 2071435 2072003 := bstep (se 1 (by rfl) ⟨1554002, by rfl⟩ : syracuseStep 2072003 = 3108005) B3108005
theorem B2622385 : Blo 2071435 2622385 := bbase (se 2 (by rfl) ⟨983394, by rfl⟩ : syracuseStep 2622385 = 1966789) (by norm_num)
theorem B3496513 : Blo 2071435 3496513 := bstep (se 2 (by rfl) ⟨1311192, by rfl⟩ : syracuseStep 3496513 = 2622385) B2622385
theorem B4662017 : Blo 2071435 4662017 := bstep (se 2 (by rfl) ⟨1748256, by rfl⟩ : syracuseStep 4662017 = 3496513) B3496513
theorem B3108011 : Blo 2071435 3108011 := bstep (se 1 (by rfl) ⟨2331008, by rfl⟩ : syracuseStep 3108011 = 4662017) B4662017
theorem B2072007 : Blo 2071435 2072007 := bstep (se 1 (by rfl) ⟨1554005, by rfl⟩ : syracuseStep 2072007 = 3108011) B3108011
theorem B2331013 : Blo 2071435 2331013 := bbase (se 4 (by rfl) ⟨218532, by rfl⟩ : syracuseStep 2331013 = 437065) (by norm_num)
theorem B3108017 : Blo 2071435 3108017 := bstep (se 2 (by rfl) ⟨1165506, by rfl⟩ : syracuseStep 3108017 = 2331013) B2331013
theorem B2072011 : Blo 2071435 2072011 := bstep (se 1 (by rfl) ⟨1554008, by rfl⟩ : syracuseStep 2072011 = 3108017) B3108017
theorem B4425293 : Blo 2071435 4425293 := bbase (se 3 (by rfl) ⟨829742, by rfl⟩ : syracuseStep 4425293 = 1659485) (by norm_num)
theorem B2950195 : Blo 2071435 2950195 := bstep (se 1 (by rfl) ⟨2212646, by rfl⟩ : syracuseStep 2950195 = 4425293) B4425293
theorem B3933593 : Blo 2071435 3933593 := bstep (se 2 (by rfl) ⟨1475097, by rfl⟩ : syracuseStep 3933593 = 2950195) B2950195
theorem B2622395 : Blo 2071435 2622395 := bstep (se 1 (by rfl) ⟨1966796, by rfl⟩ : syracuseStep 2622395 = 3933593) B3933593
theorem B6993053 : Blo 2071435 6993053 := bstep (se 3 (by rfl) ⟨1311197, by rfl⟩ : syracuseStep 6993053 = 2622395) B2622395
theorem B4662035 : Blo 2071435 4662035 := bstep (se 1 (by rfl) ⟨3496526, by rfl⟩ : syracuseStep 4662035 = 6993053) B6993053
theorem B3108023 : Blo 2071435 3108023 := bstep (se 1 (by rfl) ⟨2331017, by rfl⟩ : syracuseStep 3108023 = 4662035) B4662035
theorem B2072015 : Blo 2071435 2072015 := bstep (se 1 (by rfl) ⟨1554011, by rfl⟩ : syracuseStep 2072015 = 3108023) B3108023
theorem B3108029 : Blo 2071435 3108029 := bbase (se 3 (by rfl) ⟨582755, by rfl⟩ : syracuseStep 3108029 = 1165511) (by norm_num)
theorem B2072019 : Blo 2071435 2072019 := bstep (se 1 (by rfl) ⟨1554014, by rfl⟩ : syracuseStep 2072019 = 3108029) B3108029
theorem B4662053 : Blo 2071435 4662053 := bbase (se 4 (by rfl) ⟨437067, by rfl⟩ : syracuseStep 4662053 = 874135) (by norm_num)
theorem B3108035 : Blo 2071435 3108035 := bstep (se 1 (by rfl) ⟨2331026, by rfl⟩ : syracuseStep 3108035 = 4662053) B4662053
theorem B2072023 : Blo 2071435 2072023 := bstep (se 1 (by rfl) ⟨1554017, by rfl⟩ : syracuseStep 2072023 = 3108035) B3108035
theorem B5244821 : Blo 2071435 5244821 := bbase (se 6 (by rfl) ⟨122925, by rfl⟩ : syracuseStep 5244821 = 245851) (by norm_num)
theorem B3496547 : Blo 2071435 3496547 := bstep (se 1 (by rfl) ⟨2622410, by rfl⟩ : syracuseStep 3496547 = 5244821) B5244821
theorem B2331031 : Blo 2071435 2331031 := bstep (se 1 (by rfl) ⟨1748273, by rfl⟩ : syracuseStep 2331031 = 3496547) B3496547
theorem B3108041 : Blo 2071435 3108041 := bstep (se 2 (by rfl) ⟨1165515, by rfl⟩ : syracuseStep 3108041 = 2331031) B2331031
theorem B2072027 : Blo 2071435 2072027 := bstep (se 1 (by rfl) ⟨1554020, by rfl⟩ : syracuseStep 2072027 = 3108041) B3108041
theorem B4978493 : Blo 2071435 4978493 := bbase (se 3 (by rfl) ⟨933467, by rfl⟩ : syracuseStep 4978493 = 1866935) (by norm_num)
theorem B3318995 : Blo 2071435 3318995 := bstep (se 1 (by rfl) ⟨2489246, by rfl⟩ : syracuseStep 3318995 = 4978493) B4978493
theorem B8850653 : Blo 2071435 8850653 := bstep (se 3 (by rfl) ⟨1659497, by rfl⟩ : syracuseStep 8850653 = 3318995) B3318995
theorem B5900435 : Blo 2071435 5900435 := bstep (se 1 (by rfl) ⟨4425326, by rfl⟩ : syracuseStep 5900435 = 8850653) B8850653
theorem B3933623 : Blo 2071435 3933623 := bstep (se 1 (by rfl) ⟨2950217, by rfl⟩ : syracuseStep 3933623 = 5900435) B5900435
theorem B10489661 : Blo 2071435 10489661 := bstep (se 3 (by rfl) ⟨1966811, by rfl⟩ : syracuseStep 10489661 = 3933623) B3933623
theorem B6993107 : Blo 2071435 6993107 := bstep (se 1 (by rfl) ⟨5244830, by rfl⟩ : syracuseStep 6993107 = 10489661) B10489661
theorem B4662071 : Blo 2071435 4662071 := bstep (se 1 (by rfl) ⟨3496553, by rfl⟩ : syracuseStep 4662071 = 6993107) B6993107
theorem B3108047 : Blo 2071435 3108047 := bstep (se 1 (by rfl) ⟨2331035, by rfl⟩ : syracuseStep 3108047 = 4662071) B4662071
theorem B2072031 : Blo 2071435 2072031 := bstep (se 1 (by rfl) ⟨1554023, by rfl⟩ : syracuseStep 2072031 = 3108047) B3108047
theorem B3108053 : Blo 2071435 3108053 := bbase (se 7 (by rfl) ⟨36422, by rfl⟩ : syracuseStep 3108053 = 72845) (by norm_num)
theorem B2072035 : Blo 2071435 2072035 := bstep (se 1 (by rfl) ⟨1554026, by rfl⟩ : syracuseStep 2072035 = 3108053) B3108053
theorem B2950229 : Blo 2071435 2950229 := bbase (se 8 (by rfl) ⟨17286, by rfl⟩ : syracuseStep 2950229 = 34573) (by norm_num)
theorem B7867277 : Blo 2071435 7867277 := bstep (se 3 (by rfl) ⟨1475114, by rfl⟩ : syracuseStep 7867277 = 2950229) B2950229
theorem B5244851 : Blo 2071435 5244851 := bstep (se 1 (by rfl) ⟨3933638, by rfl⟩ : syracuseStep 5244851 = 7867277) B7867277
theorem B3496567 : Blo 2071435 3496567 := bstep (se 1 (by rfl) ⟨2622425, by rfl⟩ : syracuseStep 3496567 = 5244851) B5244851
theorem B4662089 : Blo 2071435 4662089 := bstep (se 2 (by rfl) ⟨1748283, by rfl⟩ : syracuseStep 4662089 = 3496567) B3496567
theorem B3108059 : Blo 2071435 3108059 := bstep (se 1 (by rfl) ⟨2331044, by rfl⟩ : syracuseStep 3108059 = 4662089) B4662089
theorem B2072039 : Blo 2071435 2072039 := bstep (se 1 (by rfl) ⟨1554029, by rfl⟩ : syracuseStep 2072039 = 3108059) B3108059
theorem B2331049 : Blo 2071435 2331049 := bbase (se 2 (by rfl) ⟨874143, by rfl⟩ : syracuseStep 2331049 = 1748287) (by norm_num)
theorem B3108065 : Blo 2071435 3108065 := bstep (se 2 (by rfl) ⟨1165524, by rfl⟩ : syracuseStep 3108065 = 2331049) B2331049
theorem B2072043 : Blo 2071435 2072043 := bstep (se 1 (by rfl) ⟨1554032, by rfl⟩ : syracuseStep 2072043 = 3108065) B3108065
theorem B7467797 : Blo 2071435 7467797 := bbase (se 6 (by rfl) ⟨175026, by rfl⟩ : syracuseStep 7467797 = 350053) (by norm_num)
theorem B4978531 : Blo 2071435 4978531 := bstep (se 1 (by rfl) ⟨3733898, by rfl⟩ : syracuseStep 4978531 = 7467797) B7467797
theorem B6638041 : Blo 2071435 6638041 := bstep (se 2 (by rfl) ⟨2489265, by rfl⟩ : syracuseStep 6638041 = 4978531) B4978531
theorem B8850721 : Blo 2071435 8850721 := bstep (se 2 (by rfl) ⟨3319020, by rfl⟩ : syracuseStep 8850721 = 6638041) B6638041
theorem B11800961 : Blo 2071435 11800961 := bstep (se 2 (by rfl) ⟨4425360, by rfl⟩ : syracuseStep 11800961 = 8850721) B8850721
theorem B7867307 : Blo 2071435 7867307 := bstep (se 1 (by rfl) ⟨5900480, by rfl⟩ : syracuseStep 7867307 = 11800961) B11800961
theorem B5244871 : Blo 2071435 5244871 := bstep (se 1 (by rfl) ⟨3933653, by rfl⟩ : syracuseStep 5244871 = 7867307) B7867307
theorem B6993161 : Blo 2071435 6993161 := bstep (se 2 (by rfl) ⟨2622435, by rfl⟩ : syracuseStep 6993161 = 5244871) B5244871
theorem B4662107 : Blo 2071435 4662107 := bstep (se 1 (by rfl) ⟨3496580, by rfl⟩ : syracuseStep 4662107 = 6993161) B6993161
theorem B3108071 : Blo 2071435 3108071 := bstep (se 1 (by rfl) ⟨2331053, by rfl⟩ : syracuseStep 3108071 = 4662107) B4662107
theorem B2072047 : Blo 2071435 2072047 := bstep (se 1 (by rfl) ⟨1554035, by rfl⟩ : syracuseStep 2072047 = 3108071) B3108071
theorem B3108077 : Blo 2071435 3108077 := bbase (se 3 (by rfl) ⟨582764, by rfl⟩ : syracuseStep 3108077 = 1165529) (by norm_num)
theorem B2072051 : Blo 2071435 2072051 := bstep (se 1 (by rfl) ⟨1554038, by rfl⟩ : syracuseStep 2072051 = 3108077) B3108077
theorem B4662125 : Blo 2071435 4662125 := bbase (se 3 (by rfl) ⟨874148, by rfl⟩ : syracuseStep 4662125 = 1748297) (by norm_num)
theorem B3108083 : Blo 2071435 3108083 := bstep (se 1 (by rfl) ⟨2331062, by rfl⟩ : syracuseStep 3108083 = 4662125) B4662125
theorem B2072055 : Blo 2071435 2072055 := bstep (se 1 (by rfl) ⟨1554041, by rfl⟩ : syracuseStep 2072055 = 3108083) B3108083
theorem B3933677 : Blo 2071435 3933677 := bbase (se 3 (by rfl) ⟨737564, by rfl⟩ : syracuseStep 3933677 = 1475129) (by norm_num)
theorem B2622451 : Blo 2071435 2622451 := bstep (se 1 (by rfl) ⟨1966838, by rfl⟩ : syracuseStep 2622451 = 3933677) B3933677
theorem B3496601 : Blo 2071435 3496601 := bstep (se 2 (by rfl) ⟨1311225, by rfl⟩ : syracuseStep 3496601 = 2622451) B2622451
theorem B2331067 : Blo 2071435 2331067 := bstep (se 1 (by rfl) ⟨1748300, by rfl⟩ : syracuseStep 2331067 = 3496601) B3496601
theorem B3108089 : Blo 2071435 3108089 := bstep (se 2 (by rfl) ⟨1165533, by rfl⟩ : syracuseStep 3108089 = 2331067) B2331067
theorem B2072059 : Blo 2071435 2072059 := bstep (se 1 (by rfl) ⟨1554044, by rfl⟩ : syracuseStep 2072059 = 3108089) B3108089
theorem B2800445 : Blo 2071435 2800445 := bbase (se 3 (by rfl) ⟨525083, by rfl⟩ : syracuseStep 2800445 = 1050167) (by norm_num)
theorem B29871413 : Blo 2071435 29871413 := bstep (se 5 (by rfl) ⟨1400222, by rfl⟩ : syracuseStep 29871413 = 2800445) B2800445
theorem B19914275 : Blo 2071435 19914275 := bstep (se 1 (by rfl) ⟨14935706, by rfl⟩ : syracuseStep 19914275 = 29871413) B29871413
theorem B53104733 : Blo 2071435 53104733 := bstep (se 3 (by rfl) ⟨9957137, by rfl⟩ : syracuseStep 53104733 = 19914275) B19914275
theorem B35403155 : Blo 2071435 35403155 := bstep (se 1 (by rfl) ⟨26552366, by rfl⟩ : syracuseStep 35403155 = 53104733) B53104733
theorem B23602103 : Blo 2071435 23602103 := bstep (se 1 (by rfl) ⟨17701577, by rfl⟩ : syracuseStep 23602103 = 35403155) B35403155
theorem B15734735 : Blo 2071435 15734735 := bstep (se 1 (by rfl) ⟨11801051, by rfl⟩ : syracuseStep 15734735 = 23602103) B23602103
theorem B10489823 : Blo 2071435 10489823 := bstep (se 1 (by rfl) ⟨7867367, by rfl⟩ : syracuseStep 10489823 = 15734735) B15734735
theorem B6993215 : Blo 2071435 6993215 := bstep (se 1 (by rfl) ⟨5244911, by rfl⟩ : syracuseStep 6993215 = 10489823) B10489823
theorem B4662143 : Blo 2071435 4662143 := bstep (se 1 (by rfl) ⟨3496607, by rfl⟩ : syracuseStep 4662143 = 6993215) B6993215
theorem B3108095 : Blo 2071435 3108095 := bstep (se 1 (by rfl) ⟨2331071, by rfl⟩ : syracuseStep 3108095 = 4662143) B4662143
theorem B2072063 : Blo 2071435 2072063 := bstep (se 1 (by rfl) ⟨1554047, by rfl⟩ : syracuseStep 2072063 = 3108095) B3108095
theorem B3108101 : Blo 2071435 3108101 := bbase (se 4 (by rfl) ⟨291384, by rfl⟩ : syracuseStep 3108101 = 582769) (by norm_num)
theorem B2072067 : Blo 2071435 2072067 := bstep (se 1 (by rfl) ⟨1554050, by rfl⟩ : syracuseStep 2072067 = 3108101) B3108101
theorem B3496621 : Blo 2071435 3496621 := bbase (se 3 (by rfl) ⟨655616, by rfl⟩ : syracuseStep 3496621 = 1311233) (by norm_num)
theorem B4662161 : Blo 2071435 4662161 := bstep (se 2 (by rfl) ⟨1748310, by rfl⟩ : syracuseStep 4662161 = 3496621) B3496621
theorem B3108107 : Blo 2071435 3108107 := bstep (se 1 (by rfl) ⟨2331080, by rfl⟩ : syracuseStep 3108107 = 4662161) B4662161
theorem B2072071 : Blo 2071435 2072071 := bstep (se 1 (by rfl) ⟨1554053, by rfl⟩ : syracuseStep 2072071 = 3108107) B3108107
theorem B2331085 : Blo 2071435 2331085 := bbase (se 3 (by rfl) ⟨437078, by rfl⟩ : syracuseStep 2331085 = 874157) (by norm_num)
theorem B3108113 : Blo 2071435 3108113 := bstep (se 2 (by rfl) ⟨1165542, by rfl⟩ : syracuseStep 3108113 = 2331085) B2331085
theorem B2072075 : Blo 2071435 2072075 := bstep (se 1 (by rfl) ⟨1554056, by rfl⟩ : syracuseStep 2072075 = 3108113) B3108113
theorem B6993269 : Blo 2071435 6993269 := bbase (se 5 (by rfl) ⟨327809, by rfl⟩ : syracuseStep 6993269 = 655619) (by norm_num)
theorem B4662179 : Blo 2071435 4662179 := bstep (se 1 (by rfl) ⟨3496634, by rfl⟩ : syracuseStep 4662179 = 6993269) B6993269
theorem B3108119 : Blo 2071435 3108119 := bstep (se 1 (by rfl) ⟨2331089, by rfl⟩ : syracuseStep 3108119 = 4662179) B4662179
theorem B2072079 : Blo 2071435 2072079 := bstep (se 1 (by rfl) ⟨1554059, by rfl⟩ : syracuseStep 2072079 = 3108119) B3108119
theorem B3108125 : Blo 2071435 3108125 := bbase (se 3 (by rfl) ⟨582773, by rfl⟩ : syracuseStep 3108125 = 1165547) (by norm_num)
theorem B2072083 : Blo 2071435 2072083 := bstep (se 1 (by rfl) ⟨1554062, by rfl⟩ : syracuseStep 2072083 = 3108125) B3108125
theorem B4662197 : Blo 2071435 4662197 := bbase (se 5 (by rfl) ⟨218540, by rfl⟩ : syracuseStep 4662197 = 437081) (by norm_num)
theorem B3108131 : Blo 2071435 3108131 := bstep (se 1 (by rfl) ⟨2331098, by rfl⟩ : syracuseStep 3108131 = 4662197) B4662197
theorem B2072087 : Blo 2071435 2072087 := bstep (se 1 (by rfl) ⟨1554065, by rfl⟩ : syracuseStep 2072087 = 3108131) B3108131
theorem B7088725 : Blo 2071435 7088725 := bbase (se 8 (by rfl) ⟨41535, by rfl⟩ : syracuseStep 7088725 = 83071) (by norm_num)
theorem B37806533 : Blo 2071435 37806533 := bstep (se 4 (by rfl) ⟨3544362, by rfl⟩ : syracuseStep 37806533 = 7088725) B7088725
theorem B25204355 : Blo 2071435 25204355 := bstep (se 1 (by rfl) ⟨18903266, by rfl⟩ : syracuseStep 25204355 = 37806533) B37806533
theorem B16802903 : Blo 2071435 16802903 := bstep (se 1 (by rfl) ⟨12602177, by rfl⟩ : syracuseStep 16802903 = 25204355) B25204355
theorem B11201935 : Blo 2071435 11201935 := bstep (se 1 (by rfl) ⟨8401451, by rfl⟩ : syracuseStep 11201935 = 16802903) B16802903
theorem B14935913 : Blo 2071435 14935913 := bstep (se 2 (by rfl) ⟨5600967, by rfl⟩ : syracuseStep 14935913 = 11201935) B11201935
theorem B9957275 : Blo 2071435 9957275 := bstep (se 1 (by rfl) ⟨7467956, by rfl⟩ : syracuseStep 9957275 = 14935913) B14935913
theorem B6638183 : Blo 2071435 6638183 := bstep (se 1 (by rfl) ⟨4978637, by rfl⟩ : syracuseStep 6638183 = 9957275) B9957275
theorem B4425455 : Blo 2071435 4425455 := bstep (se 1 (by rfl) ⟨3319091, by rfl⟩ : syracuseStep 4425455 = 6638183) B6638183
theorem B11801213 : Blo 2071435 11801213 := bstep (se 3 (by rfl) ⟨2212727, by rfl⟩ : syracuseStep 11801213 = 4425455) B4425455
theorem B7867475 : Blo 2071435 7867475 := bstep (se 1 (by rfl) ⟨5900606, by rfl⟩ : syracuseStep 7867475 = 11801213) B11801213
theorem B5244983 : Blo 2071435 5244983 := bstep (se 1 (by rfl) ⟨3933737, by rfl⟩ : syracuseStep 5244983 = 7867475) B7867475
theorem B3496655 : Blo 2071435 3496655 := bstep (se 1 (by rfl) ⟨2622491, by rfl⟩ : syracuseStep 3496655 = 5244983) B5244983
theorem B2331103 : Blo 2071435 2331103 := bstep (se 1 (by rfl) ⟨1748327, by rfl⟩ : syracuseStep 2331103 = 3496655) B3496655
theorem B3108137 : Blo 2071435 3108137 := bstep (se 2 (by rfl) ⟨1165551, by rfl⟩ : syracuseStep 3108137 = 2331103) B2331103
theorem B2072091 : Blo 2071435 2072091 := bstep (se 1 (by rfl) ⟨1554068, by rfl⟩ : syracuseStep 2072091 = 3108137) B3108137
theorem B7088741 : Blo 2071435 7088741 := bbase (se 4 (by rfl) ⟨664569, by rfl⟩ : syracuseStep 7088741 = 1329139) (by norm_num)
theorem B4725827 : Blo 2071435 4725827 := bstep (se 1 (by rfl) ⟨3544370, by rfl⟩ : syracuseStep 4725827 = 7088741) B7088741
theorem B3150551 : Blo 2071435 3150551 := bstep (se 1 (by rfl) ⟨2362913, by rfl⟩ : syracuseStep 3150551 = 4725827) B4725827
theorem B2100367 : Blo 2071435 2100367 := bstep (se 1 (by rfl) ⟨1575275, by rfl⟩ : syracuseStep 2100367 = 3150551) B3150551
theorem B2800489 : Blo 2071435 2800489 := bstep (se 2 (by rfl) ⟨1050183, by rfl⟩ : syracuseStep 2800489 = 2100367) B2100367
theorem B3733985 : Blo 2071435 3733985 := bstep (se 2 (by rfl) ⟨1400244, by rfl⟩ : syracuseStep 3733985 = 2800489) B2800489
theorem B9957293 : Blo 2071435 9957293 := bstep (se 3 (by rfl) ⟨1866992, by rfl⟩ : syracuseStep 9957293 = 3733985) B3733985
theorem B6638195 : Blo 2071435 6638195 := bstep (se 1 (by rfl) ⟨4978646, by rfl⟩ : syracuseStep 6638195 = 9957293) B9957293
theorem B4425463 : Blo 2071435 4425463 := bstep (se 1 (by rfl) ⟨3319097, by rfl⟩ : syracuseStep 4425463 = 6638195) B6638195
theorem B5900617 : Blo 2071435 5900617 := bstep (se 2 (by rfl) ⟨2212731, by rfl⟩ : syracuseStep 5900617 = 4425463) B4425463
theorem B7867489 : Blo 2071435 7867489 := bstep (se 2 (by rfl) ⟨2950308, by rfl⟩ : syracuseStep 7867489 = 5900617) B5900617
theorem B10489985 : Blo 2071435 10489985 := bstep (se 2 (by rfl) ⟨3933744, by rfl⟩ : syracuseStep 10489985 = 7867489) B7867489
theorem B6993323 : Blo 2071435 6993323 := bstep (se 1 (by rfl) ⟨5244992, by rfl⟩ : syracuseStep 6993323 = 10489985) B10489985
theorem B4662215 : Blo 2071435 4662215 := bstep (se 1 (by rfl) ⟨3496661, by rfl⟩ : syracuseStep 4662215 = 6993323) B6993323
theorem B3108143 : Blo 2071435 3108143 := bstep (se 1 (by rfl) ⟨2331107, by rfl⟩ : syracuseStep 3108143 = 4662215) B4662215
theorem B2072095 : Blo 2071435 2072095 := bstep (se 1 (by rfl) ⟨1554071, by rfl⟩ : syracuseStep 2072095 = 3108143) B3108143
theorem B3108149 : Blo 2071435 3108149 := bbase (se 5 (by rfl) ⟨145694, by rfl⟩ : syracuseStep 3108149 = 291389) (by norm_num)
theorem B2072099 : Blo 2071435 2072099 := bstep (se 1 (by rfl) ⟨1554074, by rfl⟩ : syracuseStep 2072099 = 3108149) B3108149
theorem B5245013 : Blo 2071435 5245013 := bbase (se 8 (by rfl) ⟨30732, by rfl⟩ : syracuseStep 5245013 = 61465) (by norm_num)
theorem B3496675 : Blo 2071435 3496675 := bstep (se 1 (by rfl) ⟨2622506, by rfl⟩ : syracuseStep 3496675 = 5245013) B5245013
theorem B4662233 : Blo 2071435 4662233 := bstep (se 2 (by rfl) ⟨1748337, by rfl⟩ : syracuseStep 4662233 = 3496675) B3496675
theorem B3108155 : Blo 2071435 3108155 := bstep (se 1 (by rfl) ⟨2331116, by rfl⟩ : syracuseStep 3108155 = 4662233) B4662233
theorem B2072103 : Blo 2071435 2072103 := bstep (se 1 (by rfl) ⟨1554077, by rfl⟩ : syracuseStep 2072103 = 3108155) B3108155
theorem B2331121 : Blo 2071435 2331121 := bbase (se 2 (by rfl) ⟨874170, by rfl⟩ : syracuseStep 2331121 = 1748341) (by norm_num)
theorem B3108161 : Blo 2071435 3108161 := bstep (se 2 (by rfl) ⟨1165560, by rfl⟩ : syracuseStep 3108161 = 2331121) B2331121
theorem B2072107 : Blo 2071435 2072107 := bstep (se 1 (by rfl) ⟨1554080, by rfl⟩ : syracuseStep 2072107 = 3108161) B3108161
theorem B4978685 : Blo 2071435 4978685 := bbase (se 3 (by rfl) ⟨933503, by rfl⟩ : syracuseStep 4978685 = 1867007) (by norm_num)
theorem B13276493 : Blo 2071435 13276493 := bstep (se 3 (by rfl) ⟨2489342, by rfl⟩ : syracuseStep 13276493 = 4978685) B4978685
theorem B8850995 : Blo 2071435 8850995 := bstep (se 1 (by rfl) ⟨6638246, by rfl⟩ : syracuseStep 8850995 = 13276493) B13276493
theorem B5900663 : Blo 2071435 5900663 := bstep (se 1 (by rfl) ⟨4425497, by rfl⟩ : syracuseStep 5900663 = 8850995) B8850995
theorem B3933775 : Blo 2071435 3933775 := bstep (se 1 (by rfl) ⟨2950331, by rfl⟩ : syracuseStep 3933775 = 5900663) B5900663
theorem B5245033 : Blo 2071435 5245033 := bstep (se 2 (by rfl) ⟨1966887, by rfl⟩ : syracuseStep 5245033 = 3933775) B3933775
theorem B6993377 : Blo 2071435 6993377 := bstep (se 2 (by rfl) ⟨2622516, by rfl⟩ : syracuseStep 6993377 = 5245033) B5245033
theorem B4662251 : Blo 2071435 4662251 := bstep (se 1 (by rfl) ⟨3496688, by rfl⟩ : syracuseStep 4662251 = 6993377) B6993377
theorem B3108167 : Blo 2071435 3108167 := bstep (se 1 (by rfl) ⟨2331125, by rfl⟩ : syracuseStep 3108167 = 4662251) B4662251
theorem B2072111 : Blo 2071435 2072111 := bstep (se 1 (by rfl) ⟨1554083, by rfl⟩ : syracuseStep 2072111 = 3108167) B3108167
theorem B3108173 : Blo 2071435 3108173 := bbase (se 3 (by rfl) ⟨582782, by rfl⟩ : syracuseStep 3108173 = 1165565) (by norm_num)
theorem B2072115 : Blo 2071435 2072115 := bstep (se 1 (by rfl) ⟨1554086, by rfl⟩ : syracuseStep 2072115 = 3108173) B3108173
theorem B4662269 : Blo 2071435 4662269 := bbase (se 3 (by rfl) ⟨874175, by rfl⟩ : syracuseStep 4662269 = 1748351) (by norm_num)
theorem B3108179 : Blo 2071435 3108179 := bstep (se 1 (by rfl) ⟨2331134, by rfl⟩ : syracuseStep 3108179 = 4662269) B4662269
theorem B2072119 : Blo 2071435 2072119 := bstep (se 1 (by rfl) ⟨1554089, by rfl⟩ : syracuseStep 2072119 = 3108179) B3108179
theorem B3496709 : Blo 2071435 3496709 := bbase (se 4 (by rfl) ⟨327816, by rfl⟩ : syracuseStep 3496709 = 655633) (by norm_num)
theorem B2331139 : Blo 2071435 2331139 := bstep (se 1 (by rfl) ⟨1748354, by rfl⟩ : syracuseStep 2331139 = 3496709) B3496709
theorem B3108185 : Blo 2071435 3108185 := bstep (se 2 (by rfl) ⟨1165569, by rfl⟩ : syracuseStep 3108185 = 2331139) B2331139
theorem B2072123 : Blo 2071435 2072123 := bstep (se 1 (by rfl) ⟨1554092, by rfl⟩ : syracuseStep 2072123 = 3108185) B3108185
theorem B15735221 : Blo 2071435 15735221 := bbase (se 5 (by rfl) ⟨737588, by rfl⟩ : syracuseStep 15735221 = 1475177) (by norm_num)
theorem B10490147 : Blo 2071435 10490147 := bstep (se 1 (by rfl) ⟨7867610, by rfl⟩ : syracuseStep 10490147 = 15735221) B15735221
theorem B6993431 : Blo 2071435 6993431 := bstep (se 1 (by rfl) ⟨5245073, by rfl⟩ : syracuseStep 6993431 = 10490147) B10490147
theorem B4662287 : Blo 2071435 4662287 := bstep (se 1 (by rfl) ⟨3496715, by rfl⟩ : syracuseStep 4662287 = 6993431) B6993431
theorem B3108191 : Blo 2071435 3108191 := bstep (se 1 (by rfl) ⟨2331143, by rfl⟩ : syracuseStep 3108191 = 4662287) B4662287
theorem B2072127 : Blo 2071435 2072127 := bstep (se 1 (by rfl) ⟨1554095, by rfl⟩ : syracuseStep 2072127 = 3108191) B3108191
theorem B3108197 : Blo 2071435 3108197 := bbase (se 4 (by rfl) ⟨291393, by rfl⟩ : syracuseStep 3108197 = 582787) (by norm_num)
theorem B2072131 : Blo 2071435 2072131 := bstep (se 1 (by rfl) ⟨1554098, by rfl⟩ : syracuseStep 2072131 = 3108197) B3108197
theorem B3933821 : Blo 2071435 3933821 := bbase (se 3 (by rfl) ⟨737591, by rfl⟩ : syracuseStep 3933821 = 1475183) (by norm_num)
theorem B2622547 : Blo 2071435 2622547 := bstep (se 1 (by rfl) ⟨1966910, by rfl⟩ : syracuseStep 2622547 = 3933821) B3933821
theorem B3496729 : Blo 2071435 3496729 := bstep (se 2 (by rfl) ⟨1311273, by rfl⟩ : syracuseStep 3496729 = 2622547) B2622547
theorem B4662305 : Blo 2071435 4662305 := bstep (se 2 (by rfl) ⟨1748364, by rfl⟩ : syracuseStep 4662305 = 3496729) B3496729
theorem B3108203 : Blo 2071435 3108203 := bstep (se 1 (by rfl) ⟨2331152, by rfl⟩ : syracuseStep 3108203 = 4662305) B4662305
theorem B2072135 : Blo 2071435 2072135 := bstep (se 1 (by rfl) ⟨1554101, by rfl⟩ : syracuseStep 2072135 = 3108203) B3108203
theorem B2331157 : Blo 2071435 2331157 := bbase (se 6 (by rfl) ⟨54636, by rfl⟩ : syracuseStep 2331157 = 109273) (by norm_num)
theorem B3108209 : Blo 2071435 3108209 := bstep (se 2 (by rfl) ⟨1165578, by rfl⟩ : syracuseStep 3108209 = 2331157) B2331157
theorem B2072139 : Blo 2071435 2072139 := bstep (se 1 (by rfl) ⟨1554104, by rfl⟩ : syracuseStep 2072139 = 3108209) B3108209
theorem B2622557 : Blo 2071435 2622557 := bbase (se 3 (by rfl) ⟨491729, by rfl⟩ : syracuseStep 2622557 = 983459) (by norm_num)
theorem B6993485 : Blo 2071435 6993485 := bstep (se 3 (by rfl) ⟨1311278, by rfl⟩ : syracuseStep 6993485 = 2622557) B2622557
theorem B4662323 : Blo 2071435 4662323 := bstep (se 1 (by rfl) ⟨3496742, by rfl⟩ : syracuseStep 4662323 = 6993485) B6993485
theorem B3108215 : Blo 2071435 3108215 := bstep (se 1 (by rfl) ⟨2331161, by rfl⟩ : syracuseStep 3108215 = 4662323) B4662323
theorem B2072143 : Blo 2071435 2072143 := bstep (se 1 (by rfl) ⟨1554107, by rfl⟩ : syracuseStep 2072143 = 3108215) B3108215
theorem B3108221 : Blo 2071435 3108221 := bbase (se 3 (by rfl) ⟨582791, by rfl⟩ : syracuseStep 3108221 = 1165583) (by norm_num)
theorem B2072147 : Blo 2071435 2072147 := bstep (se 1 (by rfl) ⟨1554110, by rfl⟩ : syracuseStep 2072147 = 3108221) B3108221
theorem B4662341 : Blo 2071435 4662341 := bbase (se 4 (by rfl) ⟨437094, by rfl⟩ : syracuseStep 4662341 = 874189) (by norm_num)
theorem B3108227 : Blo 2071435 3108227 := bstep (se 1 (by rfl) ⟨2331170, by rfl⟩ : syracuseStep 3108227 = 4662341) B4662341
theorem B2072151 : Blo 2071435 2072151 := bstep (se 1 (by rfl) ⟨1554113, by rfl⟩ : syracuseStep 2072151 = 3108227) B3108227
theorem B5900789 : Blo 2071435 5900789 := bbase (se 5 (by rfl) ⟨276599, by rfl⟩ : syracuseStep 5900789 = 553199) (by norm_num)
theorem B3933859 : Blo 2071435 3933859 := bstep (se 1 (by rfl) ⟨2950394, by rfl⟩ : syracuseStep 3933859 = 5900789) B5900789
theorem B5245145 : Blo 2071435 5245145 := bstep (se 2 (by rfl) ⟨1966929, by rfl⟩ : syracuseStep 5245145 = 3933859) B3933859
theorem B3496763 : Blo 2071435 3496763 := bstep (se 1 (by rfl) ⟨2622572, by rfl⟩ : syracuseStep 3496763 = 5245145) B5245145
theorem B2331175 : Blo 2071435 2331175 := bstep (se 1 (by rfl) ⟨1748381, by rfl⟩ : syracuseStep 2331175 = 3496763) B3496763
theorem B3108233 : Blo 2071435 3108233 := bstep (se 2 (by rfl) ⟨1165587, by rfl⟩ : syracuseStep 3108233 = 2331175) B2331175
theorem B2072155 : Blo 2071435 2072155 := bstep (se 1 (by rfl) ⟨1554116, by rfl⟩ : syracuseStep 2072155 = 3108233) B3108233
theorem B10490309 : Blo 2071435 10490309 := bbase (se 4 (by rfl) ⟨983466, by rfl⟩ : syracuseStep 10490309 = 1966933) (by norm_num)
theorem B6993539 : Blo 2071435 6993539 := bstep (se 1 (by rfl) ⟨5245154, by rfl⟩ : syracuseStep 6993539 = 10490309) B10490309
theorem B4662359 : Blo 2071435 4662359 := bstep (se 1 (by rfl) ⟨3496769, by rfl⟩ : syracuseStep 4662359 = 6993539) B6993539
theorem B3108239 : Blo 2071435 3108239 := bstep (se 1 (by rfl) ⟨2331179, by rfl⟩ : syracuseStep 3108239 = 4662359) B4662359
theorem B2072159 : Blo 2071435 2072159 := bstep (se 1 (by rfl) ⟨1554119, by rfl⟩ : syracuseStep 2072159 = 3108239) B3108239
theorem B3108245 : Blo 2071435 3108245 := bbase (se 6 (by rfl) ⟨72849, by rfl⟩ : syracuseStep 3108245 = 145699) (by norm_num)
theorem B2072163 : Blo 2071435 2072163 := bstep (se 1 (by rfl) ⟨1554122, by rfl⟩ : syracuseStep 2072163 = 3108245) B3108245
theorem B3319213 : Blo 2071435 3319213 := bbase (se 3 (by rfl) ⟨622352, by rfl⟩ : syracuseStep 3319213 = 1244705) (by norm_num)
theorem B4425617 : Blo 2071435 4425617 := bstep (se 2 (by rfl) ⟨1659606, by rfl⟩ : syracuseStep 4425617 = 3319213) B3319213
theorem B11801645 : Blo 2071435 11801645 := bstep (se 3 (by rfl) ⟨2212808, by rfl⟩ : syracuseStep 11801645 = 4425617) B4425617
theorem B7867763 : Blo 2071435 7867763 := bstep (se 1 (by rfl) ⟨5900822, by rfl⟩ : syracuseStep 7867763 = 11801645) B11801645
theorem B5245175 : Blo 2071435 5245175 := bstep (se 1 (by rfl) ⟨3933881, by rfl⟩ : syracuseStep 5245175 = 7867763) B7867763
theorem B3496783 : Blo 2071435 3496783 := bstep (se 1 (by rfl) ⟨2622587, by rfl⟩ : syracuseStep 3496783 = 5245175) B5245175
theorem B4662377 : Blo 2071435 4662377 := bstep (se 2 (by rfl) ⟨1748391, by rfl⟩ : syracuseStep 4662377 = 3496783) B3496783
theorem B3108251 : Blo 2071435 3108251 := bstep (se 1 (by rfl) ⟨2331188, by rfl⟩ : syracuseStep 3108251 = 4662377) B4662377
theorem B2072167 : Blo 2071435 2072167 := bstep (se 1 (by rfl) ⟨1554125, by rfl⟩ : syracuseStep 2072167 = 3108251) B3108251
theorem B2331193 : Blo 2071435 2331193 := bbase (se 2 (by rfl) ⟨874197, by rfl⟩ : syracuseStep 2331193 = 1748395) (by norm_num)
theorem B3108257 : Blo 2071435 3108257 := bstep (se 2 (by rfl) ⟨1165596, by rfl⟩ : syracuseStep 3108257 = 2331193) B2331193
theorem B2072171 : Blo 2071435 2072171 := bstep (se 1 (by rfl) ⟨1554128, by rfl⟩ : syracuseStep 2072171 = 3108257) B3108257
theorem B2212817 : Blo 2071435 2212817 := bbase (se 2 (by rfl) ⟨829806, by rfl⟩ : syracuseStep 2212817 = 1659613) (by norm_num)
theorem B5900845 : Blo 2071435 5900845 := bstep (se 3 (by rfl) ⟨1106408, by rfl⟩ : syracuseStep 5900845 = 2212817) B2212817
theorem B7867793 : Blo 2071435 7867793 := bstep (se 2 (by rfl) ⟨2950422, by rfl⟩ : syracuseStep 7867793 = 5900845) B5900845
theorem B5245195 : Blo 2071435 5245195 := bstep (se 1 (by rfl) ⟨3933896, by rfl⟩ : syracuseStep 5245195 = 7867793) B7867793
theorem B6993593 : Blo 2071435 6993593 := bstep (se 2 (by rfl) ⟨2622597, by rfl⟩ : syracuseStep 6993593 = 5245195) B5245195
theorem B4662395 : Blo 2071435 4662395 := bstep (se 1 (by rfl) ⟨3496796, by rfl⟩ : syracuseStep 4662395 = 6993593) B6993593
theorem B3108263 : Blo 2071435 3108263 := bstep (se 1 (by rfl) ⟨2331197, by rfl⟩ : syracuseStep 3108263 = 4662395) B4662395
theorem B2072175 : Blo 2071435 2072175 := bstep (se 1 (by rfl) ⟨1554131, by rfl⟩ : syracuseStep 2072175 = 3108263) B3108263
theorem B3108269 : Blo 2071435 3108269 := bbase (se 3 (by rfl) ⟨582800, by rfl⟩ : syracuseStep 3108269 = 1165601) (by norm_num)
theorem B2072179 : Blo 2071435 2072179 := bstep (se 1 (by rfl) ⟨1554134, by rfl⟩ : syracuseStep 2072179 = 3108269) B3108269
theorem B4662413 : Blo 2071435 4662413 := bbase (se 3 (by rfl) ⟨874202, by rfl⟩ : syracuseStep 4662413 = 1748405) (by norm_num)
theorem B3108275 : Blo 2071435 3108275 := bstep (se 1 (by rfl) ⟨2331206, by rfl⟩ : syracuseStep 3108275 = 4662413) B4662413
theorem B2072183 : Blo 2071435 2072183 := bstep (se 1 (by rfl) ⟨1554137, by rfl⟩ : syracuseStep 2072183 = 3108275) B3108275
theorem B2622613 : Blo 2071435 2622613 := bbase (se 6 (by rfl) ⟨61467, by rfl⟩ : syracuseStep 2622613 = 122935) (by norm_num)
theorem B3496817 : Blo 2071435 3496817 := bstep (se 2 (by rfl) ⟨1311306, by rfl⟩ : syracuseStep 3496817 = 2622613) B2622613
theorem B2331211 : Blo 2071435 2331211 := bstep (se 1 (by rfl) ⟨1748408, by rfl⟩ : syracuseStep 2331211 = 3496817) B3496817
theorem B3108281 : Blo 2071435 3108281 := bstep (se 2 (by rfl) ⟨1165605, by rfl⟩ : syracuseStep 3108281 = 2331211) B2331211
theorem B2072187 : Blo 2071435 2072187 := bstep (se 1 (by rfl) ⟨1554140, by rfl⟩ : syracuseStep 2072187 = 3108281) B3108281
theorem B59746517 : Blo 2071435 59746517 := bbase (se 7 (by rfl) ⟨700154, by rfl⟩ : syracuseStep 59746517 = 1400309) (by norm_num)
theorem B39831011 : Blo 2071435 39831011 := bstep (se 1 (by rfl) ⟨29873258, by rfl⟩ : syracuseStep 39831011 = 59746517) B59746517
theorem B26554007 : Blo 2071435 26554007 := bstep (se 1 (by rfl) ⟨19915505, by rfl⟩ : syracuseStep 26554007 = 39831011) B39831011
theorem B17702671 : Blo 2071435 17702671 := bstep (se 1 (by rfl) ⟨13277003, by rfl⟩ : syracuseStep 17702671 = 26554007) B26554007
theorem B23603561 : Blo 2071435 23603561 := bstep (se 2 (by rfl) ⟨8851335, by rfl⟩ : syracuseStep 23603561 = 17702671) B17702671
theorem B15735707 : Blo 2071435 15735707 := bstep (se 1 (by rfl) ⟨11801780, by rfl⟩ : syracuseStep 15735707 = 23603561) B23603561
theorem B10490471 : Blo 2071435 10490471 := bstep (se 1 (by rfl) ⟨7867853, by rfl⟩ : syracuseStep 10490471 = 15735707) B15735707
theorem B6993647 : Blo 2071435 6993647 := bstep (se 1 (by rfl) ⟨5245235, by rfl⟩ : syracuseStep 6993647 = 10490471) B10490471
theorem B4662431 : Blo 2071435 4662431 := bstep (se 1 (by rfl) ⟨3496823, by rfl⟩ : syracuseStep 4662431 = 6993647) B6993647
theorem B3108287 : Blo 2071435 3108287 := bstep (se 1 (by rfl) ⟨2331215, by rfl⟩ : syracuseStep 3108287 = 4662431) B4662431
theorem B2072191 : Blo 2071435 2072191 := bstep (se 1 (by rfl) ⟨1554143, by rfl⟩ : syracuseStep 2072191 = 3108287) B3108287
theorem B3108293 : Blo 2071435 3108293 := bbase (se 4 (by rfl) ⟨291402, by rfl⟩ : syracuseStep 3108293 = 582805) (by norm_num)
theorem B2072195 : Blo 2071435 2072195 := bstep (se 1 (by rfl) ⟨1554146, by rfl⟩ : syracuseStep 2072195 = 3108293) B3108293
theorem B3496837 : Blo 2071435 3496837 := bbase (se 4 (by rfl) ⟨327828, by rfl⟩ : syracuseStep 3496837 = 655657) (by norm_num)
theorem B4662449 : Blo 2071435 4662449 := bstep (se 2 (by rfl) ⟨1748418, by rfl⟩ : syracuseStep 4662449 = 3496837) B3496837
theorem B3108299 : Blo 2071435 3108299 := bstep (se 1 (by rfl) ⟨2331224, by rfl⟩ : syracuseStep 3108299 = 4662449) B4662449
theorem B2072199 : Blo 2071435 2072199 := bstep (se 1 (by rfl) ⟨1554149, by rfl⟩ : syracuseStep 2072199 = 3108299) B3108299
theorem B2331229 : Blo 2071435 2331229 := bbase (se 3 (by rfl) ⟨437105, by rfl⟩ : syracuseStep 2331229 = 874211) (by norm_num)
theorem B3108305 : Blo 2071435 3108305 := bstep (se 2 (by rfl) ⟨1165614, by rfl⟩ : syracuseStep 3108305 = 2331229) B2331229
theorem B2072203 : Blo 2071435 2072203 := bstep (se 1 (by rfl) ⟨1554152, by rfl⟩ : syracuseStep 2072203 = 3108305) B3108305
theorem B6993701 : Blo 2071435 6993701 := bbase (se 4 (by rfl) ⟨655659, by rfl⟩ : syracuseStep 6993701 = 1311319) (by norm_num)
theorem B4662467 : Blo 2071435 4662467 := bstep (se 1 (by rfl) ⟨3496850, by rfl⟩ : syracuseStep 4662467 = 6993701) B6993701
theorem B3108311 : Blo 2071435 3108311 := bstep (se 1 (by rfl) ⟨2331233, by rfl⟩ : syracuseStep 3108311 = 4662467) B4662467
theorem B2072207 : Blo 2071435 2072207 := bstep (se 1 (by rfl) ⟨1554155, by rfl⟩ : syracuseStep 2072207 = 3108311) B3108311
theorem B3108317 : Blo 2071435 3108317 := bbase (se 3 (by rfl) ⟨582809, by rfl⟩ : syracuseStep 3108317 = 1165619) (by norm_num)
theorem B2072211 : Blo 2071435 2072211 := bstep (se 1 (by rfl) ⟨1554158, by rfl⟩ : syracuseStep 2072211 = 3108317) B3108317
theorem B4662485 : Blo 2071435 4662485 := bbase (se 7 (by rfl) ⟨54638, by rfl⟩ : syracuseStep 4662485 = 109277) (by norm_num)
theorem B3108323 : Blo 2071435 3108323 := bstep (se 1 (by rfl) ⟨2331242, by rfl⟩ : syracuseStep 3108323 = 4662485) B4662485
theorem B2072215 : Blo 2071435 2072215 := bstep (se 1 (by rfl) ⟨1554161, by rfl⟩ : syracuseStep 2072215 = 3108323) B3108323
theorem B2100493 : Blo 2071435 2100493 := bbase (se 3 (by rfl) ⟨393842, by rfl⟩ : syracuseStep 2100493 = 787685) (by norm_num)
theorem B2800657 : Blo 2071435 2800657 := bstep (se 2 (by rfl) ⟨1050246, by rfl⟩ : syracuseStep 2800657 = 2100493) B2100493
theorem B3734209 : Blo 2071435 3734209 := bstep (se 2 (by rfl) ⟨1400328, by rfl⟩ : syracuseStep 3734209 = 2800657) B2800657
theorem B4978945 : Blo 2071435 4978945 := bstep (se 2 (by rfl) ⟨1867104, by rfl⟩ : syracuseStep 4978945 = 3734209) B3734209
theorem B6638593 : Blo 2071435 6638593 := bstep (se 2 (by rfl) ⟨2489472, by rfl⟩ : syracuseStep 6638593 = 4978945) B4978945
theorem B8851457 : Blo 2071435 8851457 := bstep (se 2 (by rfl) ⟨3319296, by rfl⟩ : syracuseStep 8851457 = 6638593) B6638593
theorem B5900971 : Blo 2071435 5900971 := bstep (se 1 (by rfl) ⟨4425728, by rfl⟩ : syracuseStep 5900971 = 8851457) B8851457
theorem B7867961 : Blo 2071435 7867961 := bstep (se 2 (by rfl) ⟨2950485, by rfl⟩ : syracuseStep 7867961 = 5900971) B5900971
theorem B5245307 : Blo 2071435 5245307 := bstep (se 1 (by rfl) ⟨3933980, by rfl⟩ : syracuseStep 5245307 = 7867961) B7867961
theorem B3496871 : Blo 2071435 3496871 := bstep (se 1 (by rfl) ⟨2622653, by rfl⟩ : syracuseStep 3496871 = 5245307) B5245307
theorem B2331247 : Blo 2071435 2331247 := bstep (se 1 (by rfl) ⟨1748435, by rfl⟩ : syracuseStep 2331247 = 3496871) B3496871
theorem B3108329 : Blo 2071435 3108329 := bstep (se 2 (by rfl) ⟨1165623, by rfl⟩ : syracuseStep 3108329 = 2331247) B2331247
theorem B2072219 : Blo 2071435 2072219 := bstep (se 1 (by rfl) ⟨1554164, by rfl⟩ : syracuseStep 2072219 = 3108329) B3108329
theorem B4726117 : Blo 2071435 4726117 := bbase (se 4 (by rfl) ⟨443073, by rfl⟩ : syracuseStep 4726117 = 886147) (by norm_num)
theorem B6301489 : Blo 2071435 6301489 := bstep (se 2 (by rfl) ⟨2363058, by rfl⟩ : syracuseStep 6301489 = 4726117) B4726117
theorem B8401985 : Blo 2071435 8401985 := bstep (se 2 (by rfl) ⟨3150744, by rfl⟩ : syracuseStep 8401985 = 6301489) B6301489
theorem B5601323 : Blo 2071435 5601323 := bstep (se 1 (by rfl) ⟨4200992, by rfl⟩ : syracuseStep 5601323 = 8401985) B8401985
theorem B14936861 : Blo 2071435 14936861 := bstep (se 3 (by rfl) ⟨2800661, by rfl⟩ : syracuseStep 14936861 = 5601323) B5601323
theorem B9957907 : Blo 2071435 9957907 := bstep (se 1 (by rfl) ⟨7468430, by rfl⟩ : syracuseStep 9957907 = 14936861) B14936861
theorem B13277209 : Blo 2071435 13277209 := bstep (se 2 (by rfl) ⟨4978953, by rfl⟩ : syracuseStep 13277209 = 9957907) B9957907
theorem B17702945 : Blo 2071435 17702945 := bstep (se 2 (by rfl) ⟨6638604, by rfl⟩ : syracuseStep 17702945 = 13277209) B13277209
theorem B11801963 : Blo 2071435 11801963 := bstep (se 1 (by rfl) ⟨8851472, by rfl⟩ : syracuseStep 11801963 = 17702945) B17702945
theorem B7867975 : Blo 2071435 7867975 := bstep (se 1 (by rfl) ⟨5900981, by rfl⟩ : syracuseStep 7867975 = 11801963) B11801963
theorem B10490633 : Blo 2071435 10490633 := bstep (se 2 (by rfl) ⟨3933987, by rfl⟩ : syracuseStep 10490633 = 7867975) B7867975
theorem B6993755 : Blo 2071435 6993755 := bstep (se 1 (by rfl) ⟨5245316, by rfl⟩ : syracuseStep 6993755 = 10490633) B10490633
theorem B4662503 : Blo 2071435 4662503 := bstep (se 1 (by rfl) ⟨3496877, by rfl⟩ : syracuseStep 4662503 = 6993755) B6993755
theorem B3108335 : Blo 2071435 3108335 := bstep (se 1 (by rfl) ⟨2331251, by rfl⟩ : syracuseStep 3108335 = 4662503) B4662503
theorem B2072223 : Blo 2071435 2072223 := bstep (se 1 (by rfl) ⟨1554167, by rfl⟩ : syracuseStep 2072223 = 3108335) B3108335
theorem B3108341 : Blo 2071435 3108341 := bbase (se 5 (by rfl) ⟨145703, by rfl⟩ : syracuseStep 3108341 = 291407) (by norm_num)
theorem B2072227 : Blo 2071435 2072227 := bstep (se 1 (by rfl) ⟨1554170, by rfl⟩ : syracuseStep 2072227 = 3108341) B3108341
theorem B2212877 : Blo 2071435 2212877 := bbase (se 3 (by rfl) ⟨414914, by rfl⟩ : syracuseStep 2212877 = 829829) (by norm_num)
theorem B5901005 : Blo 2071435 5901005 := bstep (se 3 (by rfl) ⟨1106438, by rfl⟩ : syracuseStep 5901005 = 2212877) B2212877
theorem B3934003 : Blo 2071435 3934003 := bstep (se 1 (by rfl) ⟨2950502, by rfl⟩ : syracuseStep 3934003 = 5901005) B5901005
theorem B5245337 : Blo 2071435 5245337 := bstep (se 2 (by rfl) ⟨1967001, by rfl⟩ : syracuseStep 5245337 = 3934003) B3934003
theorem B3496891 : Blo 2071435 3496891 := bstep (se 1 (by rfl) ⟨2622668, by rfl⟩ : syracuseStep 3496891 = 5245337) B5245337
theorem B4662521 : Blo 2071435 4662521 := bstep (se 2 (by rfl) ⟨1748445, by rfl⟩ : syracuseStep 4662521 = 3496891) B3496891
theorem B3108347 : Blo 2071435 3108347 := bstep (se 1 (by rfl) ⟨2331260, by rfl⟩ : syracuseStep 3108347 = 4662521) B4662521
theorem B2072231 : Blo 2071435 2072231 := bstep (se 1 (by rfl) ⟨1554173, by rfl⟩ : syracuseStep 2072231 = 3108347) B3108347
theorem B2331265 : Blo 2071435 2331265 := bbase (se 2 (by rfl) ⟨874224, by rfl⟩ : syracuseStep 2331265 = 1748449) (by norm_num)
theorem B3108353 : Blo 2071435 3108353 := bstep (se 2 (by rfl) ⟨1165632, by rfl⟩ : syracuseStep 3108353 = 2331265) B2331265
theorem B2072235 : Blo 2071435 2072235 := bstep (se 1 (by rfl) ⟨1554176, by rfl⟩ : syracuseStep 2072235 = 3108353) B3108353
theorem B5245357 : Blo 2071435 5245357 := bbase (se 3 (by rfl) ⟨983504, by rfl⟩ : syracuseStep 5245357 = 1967009) (by norm_num)
theorem B6993809 : Blo 2071435 6993809 := bstep (se 2 (by rfl) ⟨2622678, by rfl⟩ : syracuseStep 6993809 = 5245357) B5245357
theorem B4662539 : Blo 2071435 4662539 := bstep (se 1 (by rfl) ⟨3496904, by rfl⟩ : syracuseStep 4662539 = 6993809) B6993809
theorem B3108359 : Blo 2071435 3108359 := bstep (se 1 (by rfl) ⟨2331269, by rfl⟩ : syracuseStep 3108359 = 4662539) B4662539
theorem B2072239 : Blo 2071435 2072239 := bstep (se 1 (by rfl) ⟨1554179, by rfl⟩ : syracuseStep 2072239 = 3108359) B3108359
theorem B3108365 : Blo 2071435 3108365 := bbase (se 3 (by rfl) ⟨582818, by rfl⟩ : syracuseStep 3108365 = 1165637) (by norm_num)
theorem B2072243 : Blo 2071435 2072243 := bstep (se 1 (by rfl) ⟨1554182, by rfl⟩ : syracuseStep 2072243 = 3108365) B3108365
theorem B4662557 : Blo 2071435 4662557 := bbase (se 3 (by rfl) ⟨874229, by rfl⟩ : syracuseStep 4662557 = 1748459) (by norm_num)
theorem B3108371 : Blo 2071435 3108371 := bstep (se 1 (by rfl) ⟨2331278, by rfl⟩ : syracuseStep 3108371 = 4662557) B4662557
theorem B2072247 : Blo 2071435 2072247 := bstep (se 1 (by rfl) ⟨1554185, by rfl⟩ : syracuseStep 2072247 = 3108371) B3108371
theorem B3496925 : Blo 2071435 3496925 := bbase (se 3 (by rfl) ⟨655673, by rfl⟩ : syracuseStep 3496925 = 1311347) (by norm_num)
theorem B2331283 : Blo 2071435 2331283 := bstep (se 1 (by rfl) ⟨1748462, by rfl⟩ : syracuseStep 2331283 = 3496925) B3496925
theorem B3108377 : Blo 2071435 3108377 := bstep (se 2 (by rfl) ⟨1165641, by rfl⟩ : syracuseStep 3108377 = 2331283) B2331283
theorem B2072251 : Blo 2071435 2072251 := bstep (se 1 (by rfl) ⟨1554188, by rfl⟩ : syracuseStep 2072251 = 3108377) B3108377
theorem B2100529 : Blo 2071435 2100529 := bbase (se 2 (by rfl) ⟨787698, by rfl⟩ : syracuseStep 2100529 = 1575397) (by norm_num)
theorem B2800705 : Blo 2071435 2800705 := bstep (se 2 (by rfl) ⟨1050264, by rfl⟩ : syracuseStep 2800705 = 2100529) B2100529
theorem B3734273 : Blo 2071435 3734273 := bstep (se 2 (by rfl) ⟨1400352, by rfl⟩ : syracuseStep 3734273 = 2800705) B2800705
theorem B9958061 : Blo 2071435 9958061 := bstep (se 3 (by rfl) ⟨1867136, by rfl⟩ : syracuseStep 9958061 = 3734273) B3734273
theorem B6638707 : Blo 2071435 6638707 := bstep (se 1 (by rfl) ⟨4979030, by rfl⟩ : syracuseStep 6638707 = 9958061) B9958061
theorem B8851609 : Blo 2071435 8851609 := bstep (se 2 (by rfl) ⟨3319353, by rfl⟩ : syracuseStep 8851609 = 6638707) B6638707
theorem B11802145 : Blo 2071435 11802145 := bstep (se 2 (by rfl) ⟨4425804, by rfl⟩ : syracuseStep 11802145 = 8851609) B8851609
theorem B15736193 : Blo 2071435 15736193 := bstep (se 2 (by rfl) ⟨5901072, by rfl⟩ : syracuseStep 15736193 = 11802145) B11802145
theorem B10490795 : Blo 2071435 10490795 := bstep (se 1 (by rfl) ⟨7868096, by rfl⟩ : syracuseStep 10490795 = 15736193) B15736193
theorem B6993863 : Blo 2071435 6993863 := bstep (se 1 (by rfl) ⟨5245397, by rfl⟩ : syracuseStep 6993863 = 10490795) B10490795
theorem B4662575 : Blo 2071435 4662575 := bstep (se 1 (by rfl) ⟨3496931, by rfl⟩ : syracuseStep 4662575 = 6993863) B6993863
theorem B3108383 : Blo 2071435 3108383 := bstep (se 1 (by rfl) ⟨2331287, by rfl⟩ : syracuseStep 3108383 = 4662575) B4662575
theorem B2072255 : Blo 2071435 2072255 := bstep (se 1 (by rfl) ⟨1554191, by rfl⟩ : syracuseStep 2072255 = 3108383) B3108383
theorem B3108389 : Blo 2071435 3108389 := bbase (se 4 (by rfl) ⟨291411, by rfl⟩ : syracuseStep 3108389 = 582823) (by norm_num)
theorem B2072259 : Blo 2071435 2072259 := bstep (se 1 (by rfl) ⟨1554194, by rfl⟩ : syracuseStep 2072259 = 3108389) B3108389
theorem B2622709 : Blo 2071435 2622709 := bbase (se 5 (by rfl) ⟨122939, by rfl⟩ : syracuseStep 2622709 = 245879) (by norm_num)
theorem B3496945 : Blo 2071435 3496945 := bstep (se 2 (by rfl) ⟨1311354, by rfl⟩ : syracuseStep 3496945 = 2622709) B2622709
theorem B4662593 : Blo 2071435 4662593 := bstep (se 2 (by rfl) ⟨1748472, by rfl⟩ : syracuseStep 4662593 = 3496945) B3496945
theorem B3108395 : Blo 2071435 3108395 := bstep (se 1 (by rfl) ⟨2331296, by rfl⟩ : syracuseStep 3108395 = 4662593) B4662593
theorem B2072263 : Blo 2071435 2072263 := bstep (se 1 (by rfl) ⟨1554197, by rfl⟩ : syracuseStep 2072263 = 3108395) B3108395
theorem B2331301 : Blo 2071435 2331301 := bbase (se 4 (by rfl) ⟨218559, by rfl⟩ : syracuseStep 2331301 = 437119) (by norm_num)
theorem B3108401 : Blo 2071435 3108401 := bstep (se 2 (by rfl) ⟨1165650, by rfl⟩ : syracuseStep 3108401 = 2331301) B2331301
theorem B2072267 : Blo 2071435 2072267 := bstep (se 1 (by rfl) ⟨1554200, by rfl⟩ : syracuseStep 2072267 = 3108401) B3108401
theorem B21268021 : Blo 2071435 21268021 := bbase (se 5 (by rfl) ⟨996938, by rfl⟩ : syracuseStep 21268021 = 1993877) (by norm_num)
theorem B28357361 : Blo 2071435 28357361 := bstep (se 2 (by rfl) ⟨10634010, by rfl⟩ : syracuseStep 28357361 = 21268021) B21268021
theorem B18904907 : Blo 2071435 18904907 := bstep (se 1 (by rfl) ⟨14178680, by rfl⟩ : syracuseStep 18904907 = 28357361) B28357361
theorem B12603271 : Blo 2071435 12603271 := bstep (se 1 (by rfl) ⟨9452453, by rfl⟩ : syracuseStep 12603271 = 18904907) B18904907
theorem B16804361 : Blo 2071435 16804361 := bstep (se 2 (by rfl) ⟨6301635, by rfl⟩ : syracuseStep 16804361 = 12603271) B12603271
theorem B44811629 : Blo 2071435 44811629 := bstep (se 3 (by rfl) ⟨8402180, by rfl⟩ : syracuseStep 44811629 = 16804361) B16804361
theorem B29874419 : Blo 2071435 29874419 := bstep (se 1 (by rfl) ⟨22405814, by rfl⟩ : syracuseStep 29874419 = 44811629) B44811629
theorem B19916279 : Blo 2071435 19916279 := bstep (se 1 (by rfl) ⟨14937209, by rfl⟩ : syracuseStep 19916279 = 29874419) B29874419
theorem B13277519 : Blo 2071435 13277519 := bstep (se 1 (by rfl) ⟨9958139, by rfl⟩ : syracuseStep 13277519 = 19916279) B19916279
theorem B8851679 : Blo 2071435 8851679 := bstep (se 1 (by rfl) ⟨6638759, by rfl⟩ : syracuseStep 8851679 = 13277519) B13277519
theorem B5901119 : Blo 2071435 5901119 := bstep (se 1 (by rfl) ⟨4425839, by rfl⟩ : syracuseStep 5901119 = 8851679) B8851679
theorem B3934079 : Blo 2071435 3934079 := bstep (se 1 (by rfl) ⟨2950559, by rfl⟩ : syracuseStep 3934079 = 5901119) B5901119
theorem B2622719 : Blo 2071435 2622719 := bstep (se 1 (by rfl) ⟨1967039, by rfl⟩ : syracuseStep 2622719 = 3934079) B3934079
theorem B6993917 : Blo 2071435 6993917 := bstep (se 3 (by rfl) ⟨1311359, by rfl⟩ : syracuseStep 6993917 = 2622719) B2622719
theorem B4662611 : Blo 2071435 4662611 := bstep (se 1 (by rfl) ⟨3496958, by rfl⟩ : syracuseStep 4662611 = 6993917) B6993917
theorem B3108407 : Blo 2071435 3108407 := bstep (se 1 (by rfl) ⟨2331305, by rfl⟩ : syracuseStep 3108407 = 4662611) B4662611
theorem B2072271 : Blo 2071435 2072271 := bstep (se 1 (by rfl) ⟨1554203, by rfl⟩ : syracuseStep 2072271 = 3108407) B3108407
theorem B3108413 : Blo 2071435 3108413 := bbase (se 3 (by rfl) ⟨582827, by rfl⟩ : syracuseStep 3108413 = 1165655) (by norm_num)
theorem B2072275 : Blo 2071435 2072275 := bstep (se 1 (by rfl) ⟨1554206, by rfl⟩ : syracuseStep 2072275 = 3108413) B3108413
theorem B4662629 : Blo 2071435 4662629 := bbase (se 4 (by rfl) ⟨437121, by rfl⟩ : syracuseStep 4662629 = 874243) (by norm_num)
theorem B3108419 : Blo 2071435 3108419 := bstep (se 1 (by rfl) ⟨2331314, by rfl⟩ : syracuseStep 3108419 = 4662629) B4662629
theorem B2072279 : Blo 2071435 2072279 := bstep (se 1 (by rfl) ⟨1554209, by rfl⟩ : syracuseStep 2072279 = 3108419) B3108419
theorem B5245469 : Blo 2071435 5245469 := bbase (se 3 (by rfl) ⟨983525, by rfl⟩ : syracuseStep 5245469 = 1967051) (by norm_num)
theorem B3496979 : Blo 2071435 3496979 := bstep (se 1 (by rfl) ⟨2622734, by rfl⟩ : syracuseStep 3496979 = 5245469) B5245469
theorem B2331319 : Blo 2071435 2331319 := bstep (se 1 (by rfl) ⟨1748489, by rfl⟩ : syracuseStep 2331319 = 3496979) B3496979
theorem B3108425 : Blo 2071435 3108425 := bstep (se 2 (by rfl) ⟨1165659, by rfl⟩ : syracuseStep 3108425 = 2331319) B2331319
theorem B2072283 : Blo 2071435 2072283 := bstep (se 1 (by rfl) ⟨1554212, by rfl⟩ : syracuseStep 2072283 = 3108425) B3108425
theorem B3934109 : Blo 2071435 3934109 := bbase (se 3 (by rfl) ⟨737645, by rfl⟩ : syracuseStep 3934109 = 1475291) (by norm_num)
theorem B10490957 : Blo 2071435 10490957 := bstep (se 3 (by rfl) ⟨1967054, by rfl⟩ : syracuseStep 10490957 = 3934109) B3934109
theorem B6993971 : Blo 2071435 6993971 := bstep (se 1 (by rfl) ⟨5245478, by rfl⟩ : syracuseStep 6993971 = 10490957) B10490957
theorem B4662647 : Blo 2071435 4662647 := bstep (se 1 (by rfl) ⟨3496985, by rfl⟩ : syracuseStep 4662647 = 6993971) B6993971
theorem B3108431 : Blo 2071435 3108431 := bstep (se 1 (by rfl) ⟨2331323, by rfl⟩ : syracuseStep 3108431 = 4662647) B4662647
theorem B2072287 : Blo 2071435 2072287 := bstep (se 1 (by rfl) ⟨1554215, by rfl⟩ : syracuseStep 2072287 = 3108431) B3108431
theorem B3108437 : Blo 2071435 3108437 := bbase (se 8 (by rfl) ⟨18213, by rfl⟩ : syracuseStep 3108437 = 36427) (by norm_num)
theorem B2072291 : Blo 2071435 2072291 := bstep (se 1 (by rfl) ⟨1554218, by rfl⟩ : syracuseStep 2072291 = 3108437) B3108437
theorem B8851781 : Blo 2071435 8851781 := bbase (se 4 (by rfl) ⟨829854, by rfl⟩ : syracuseStep 8851781 = 1659709) (by norm_num)
theorem B5901187 : Blo 2071435 5901187 := bstep (se 1 (by rfl) ⟨4425890, by rfl⟩ : syracuseStep 5901187 = 8851781) B8851781
theorem B7868249 : Blo 2071435 7868249 := bstep (se 2 (by rfl) ⟨2950593, by rfl⟩ : syracuseStep 7868249 = 5901187) B5901187
theorem B5245499 : Blo 2071435 5245499 := bstep (se 1 (by rfl) ⟨3934124, by rfl⟩ : syracuseStep 5245499 = 7868249) B7868249
theorem B3496999 : Blo 2071435 3496999 := bstep (se 1 (by rfl) ⟨2622749, by rfl⟩ : syracuseStep 3496999 = 5245499) B5245499
theorem B4662665 : Blo 2071435 4662665 := bstep (se 2 (by rfl) ⟨1748499, by rfl⟩ : syracuseStep 4662665 = 3496999) B3496999
theorem B3108443 : Blo 2071435 3108443 := bstep (se 1 (by rfl) ⟨2331332, by rfl⟩ : syracuseStep 3108443 = 4662665) B4662665
theorem B2072295 : Blo 2071435 2072295 := bstep (se 1 (by rfl) ⟨1554221, by rfl⟩ : syracuseStep 2072295 = 3108443) B3108443
theorem B2331337 : Blo 2071435 2331337 := bbase (se 2 (by rfl) ⟨874251, by rfl⟩ : syracuseStep 2331337 = 1748503) (by norm_num)
theorem B3108449 : Blo 2071435 3108449 := bstep (se 2 (by rfl) ⟨1165668, by rfl⟩ : syracuseStep 3108449 = 2331337) B2331337
theorem B2072299 : Blo 2071435 2072299 := bstep (se 1 (by rfl) ⟨1554224, by rfl⟩ : syracuseStep 2072299 = 3108449) B3108449
theorem B2489573 : Blo 2071435 2489573 := bbase (se 4 (by rfl) ⟨233397, by rfl⟩ : syracuseStep 2489573 = 466795) (by norm_num)
theorem B6638861 : Blo 2071435 6638861 := bstep (se 3 (by rfl) ⟨1244786, by rfl⟩ : syracuseStep 6638861 = 2489573) B2489573
theorem B17703629 : Blo 2071435 17703629 := bstep (se 3 (by rfl) ⟨3319430, by rfl⟩ : syracuseStep 17703629 = 6638861) B6638861
theorem B11802419 : Blo 2071435 11802419 := bstep (se 1 (by rfl) ⟨8851814, by rfl⟩ : syracuseStep 11802419 = 17703629) B17703629
theorem B7868279 : Blo 2071435 7868279 := bstep (se 1 (by rfl) ⟨5901209, by rfl⟩ : syracuseStep 7868279 = 11802419) B11802419
theorem B5245519 : Blo 2071435 5245519 := bstep (se 1 (by rfl) ⟨3934139, by rfl⟩ : syracuseStep 5245519 = 7868279) B7868279
theorem B6994025 : Blo 2071435 6994025 := bstep (se 2 (by rfl) ⟨2622759, by rfl⟩ : syracuseStep 6994025 = 5245519) B5245519
theorem B4662683 : Blo 2071435 4662683 := bstep (se 1 (by rfl) ⟨3497012, by rfl⟩ : syracuseStep 4662683 = 6994025) B6994025
theorem B3108455 : Blo 2071435 3108455 := bstep (se 1 (by rfl) ⟨2331341, by rfl⟩ : syracuseStep 3108455 = 4662683) B4662683
theorem B2072303 : Blo 2071435 2072303 := bstep (se 1 (by rfl) ⟨1554227, by rfl⟩ : syracuseStep 2072303 = 3108455) B3108455
theorem B3108461 : Blo 2071435 3108461 := bbase (se 3 (by rfl) ⟨582836, by rfl⟩ : syracuseStep 3108461 = 1165673) (by norm_num)
theorem B2072307 : Blo 2071435 2072307 := bstep (se 1 (by rfl) ⟨1554230, by rfl⟩ : syracuseStep 2072307 = 3108461) B3108461
theorem B4662701 : Blo 2071435 4662701 := bbase (se 3 (by rfl) ⟨874256, by rfl⟩ : syracuseStep 4662701 = 1748513) (by norm_num)
theorem B3108467 : Blo 2071435 3108467 := bstep (se 1 (by rfl) ⟨2331350, by rfl⟩ : syracuseStep 3108467 = 4662701) B4662701
theorem B2072311 : Blo 2071435 2072311 := bstep (se 1 (by rfl) ⟨1554233, by rfl⟩ : syracuseStep 2072311 = 3108467) B3108467
theorem B2243161 : Blo 2071435 2243161 := bbase (se 2 (by rfl) ⟨841185, by rfl⟩ : syracuseStep 2243161 = 1682371) (by norm_num)
theorem B2990881 : Blo 2071435 2990881 := bstep (se 2 (by rfl) ⟨1121580, by rfl⟩ : syracuseStep 2990881 = 2243161) B2243161
theorem B3987841 : Blo 2071435 3987841 := bstep (se 2 (by rfl) ⟨1495440, by rfl⟩ : syracuseStep 3987841 = 2990881) B2990881
theorem B5317121 : Blo 2071435 5317121 := bstep (se 2 (by rfl) ⟨1993920, by rfl⟩ : syracuseStep 5317121 = 3987841) B3987841
theorem B14178989 : Blo 2071435 14178989 := bstep (se 3 (by rfl) ⟨2658560, by rfl⟩ : syracuseStep 14178989 = 5317121) B5317121
theorem B9452659 : Blo 2071435 9452659 := bstep (se 1 (by rfl) ⟨7089494, by rfl⟩ : syracuseStep 9452659 = 14178989) B14178989
theorem B12603545 : Blo 2071435 12603545 := bstep (se 2 (by rfl) ⟨4726329, by rfl⟩ : syracuseStep 12603545 = 9452659) B9452659
theorem B8402363 : Blo 2071435 8402363 := bstep (se 1 (by rfl) ⟨6301772, by rfl⟩ : syracuseStep 8402363 = 12603545) B12603545
theorem B5601575 : Blo 2071435 5601575 := bstep (se 1 (by rfl) ⟨4201181, by rfl⟩ : syracuseStep 5601575 = 8402363) B8402363
theorem B3734383 : Blo 2071435 3734383 := bstep (se 1 (by rfl) ⟨2800787, by rfl⟩ : syracuseStep 3734383 = 5601575) B5601575
theorem B4979177 : Blo 2071435 4979177 := bstep (se 2 (by rfl) ⟨1867191, by rfl⟩ : syracuseStep 4979177 = 3734383) B3734383
theorem B3319451 : Blo 2071435 3319451 := bstep (se 1 (by rfl) ⟨2489588, by rfl⟩ : syracuseStep 3319451 = 4979177) B4979177
theorem B2212967 : Blo 2071435 2212967 := bstep (se 1 (by rfl) ⟨1659725, by rfl⟩ : syracuseStep 2212967 = 3319451) B3319451
theorem B5901245 : Blo 2071435 5901245 := bstep (se 3 (by rfl) ⟨1106483, by rfl⟩ : syracuseStep 5901245 = 2212967) B2212967
theorem B3934163 : Blo 2071435 3934163 := bstep (se 1 (by rfl) ⟨2950622, by rfl⟩ : syracuseStep 3934163 = 5901245) B5901245
theorem B2622775 : Blo 2071435 2622775 := bstep (se 1 (by rfl) ⟨1967081, by rfl⟩ : syracuseStep 2622775 = 3934163) B3934163
theorem B3497033 : Blo 2071435 3497033 := bstep (se 2 (by rfl) ⟨1311387, by rfl⟩ : syracuseStep 3497033 = 2622775) B2622775
theorem B2331355 : Blo 2071435 2331355 := bstep (se 1 (by rfl) ⟨1748516, by rfl⟩ : syracuseStep 2331355 = 3497033) B3497033
theorem B3108473 : Blo 2071435 3108473 := bstep (se 2 (by rfl) ⟨1165677, by rfl⟩ : syracuseStep 3108473 = 2331355) B2331355
theorem B2072315 : Blo 2071435 2072315 := bstep (se 1 (by rfl) ⟨1554236, by rfl⟩ : syracuseStep 2072315 = 3108473) B3108473
theorem B3987845 : Blo 2071435 3987845 := bbase (se 4 (by rfl) ⟨373860, by rfl⟩ : syracuseStep 3987845 = 747721) (by norm_num)
theorem B170148053 : Blo 2071435 170148053 := bstep (se 7 (by rfl) ⟨1993922, by rfl⟩ : syracuseStep 170148053 = 3987845) B3987845
theorem B453728141 : Blo 2071435 453728141 := bstep (se 3 (by rfl) ⟨85074026, by rfl⟩ : syracuseStep 453728141 = 170148053) B170148053
theorem B302485427 : Blo 2071435 302485427 := bstep (se 1 (by rfl) ⟨226864070, by rfl⟩ : syracuseStep 302485427 = 453728141) B453728141
theorem B201656951 : Blo 2071435 201656951 := bstep (se 1 (by rfl) ⟨151242713, by rfl⟩ : syracuseStep 201656951 = 302485427) B302485427
theorem B134437967 : Blo 2071435 134437967 := bstep (se 1 (by rfl) ⟨100828475, by rfl⟩ : syracuseStep 134437967 = 201656951) B201656951
theorem B89625311 : Blo 2071435 89625311 := bstep (se 1 (by rfl) ⟨67218983, by rfl⟩ : syracuseStep 89625311 = 134437967) B134437967
theorem B59750207 : Blo 2071435 59750207 := bstep (se 1 (by rfl) ⟨44812655, by rfl⟩ : syracuseStep 59750207 = 89625311) B89625311
theorem B39833471 : Blo 2071435 39833471 := bstep (se 1 (by rfl) ⟨29875103, by rfl⟩ : syracuseStep 39833471 = 59750207) B59750207
theorem B26555647 : Blo 2071435 26555647 := bstep (se 1 (by rfl) ⟨19916735, by rfl⟩ : syracuseStep 26555647 = 39833471) B39833471
theorem B35407529 : Blo 2071435 35407529 := bstep (se 2 (by rfl) ⟨13277823, by rfl⟩ : syracuseStep 35407529 = 26555647) B26555647
theorem B23605019 : Blo 2071435 23605019 := bstep (se 1 (by rfl) ⟨17703764, by rfl⟩ : syracuseStep 23605019 = 35407529) B35407529
theorem B15736679 : Blo 2071435 15736679 := bstep (se 1 (by rfl) ⟨11802509, by rfl⟩ : syracuseStep 15736679 = 23605019) B23605019
theorem B10491119 : Blo 2071435 10491119 := bstep (se 1 (by rfl) ⟨7868339, by rfl⟩ : syracuseStep 10491119 = 15736679) B15736679
theorem B6994079 : Blo 2071435 6994079 := bstep (se 1 (by rfl) ⟨5245559, by rfl⟩ : syracuseStep 6994079 = 10491119) B10491119
theorem B4662719 : Blo 2071435 4662719 := bstep (se 1 (by rfl) ⟨3497039, by rfl⟩ : syracuseStep 4662719 = 6994079) B6994079
theorem B3108479 : Blo 2071435 3108479 := bstep (se 1 (by rfl) ⟨2331359, by rfl⟩ : syracuseStep 3108479 = 4662719) B4662719
theorem B2072319 : Blo 2071435 2072319 := bstep (se 1 (by rfl) ⟨1554239, by rfl⟩ : syracuseStep 2072319 = 3108479) B3108479
theorem B3108485 : Blo 2071435 3108485 := bbase (se 4 (by rfl) ⟨291420, by rfl⟩ : syracuseStep 3108485 = 582841) (by norm_num)
theorem B2072323 : Blo 2071435 2072323 := bstep (se 1 (by rfl) ⟨1554242, by rfl⟩ : syracuseStep 2072323 = 3108485) B3108485
theorem B3497053 : Blo 2071435 3497053 := bbase (se 3 (by rfl) ⟨655697, by rfl⟩ : syracuseStep 3497053 = 1311395) (by norm_num)
theorem B4662737 : Blo 2071435 4662737 := bstep (se 2 (by rfl) ⟨1748526, by rfl⟩ : syracuseStep 4662737 = 3497053) B3497053
theorem B3108491 : Blo 2071435 3108491 := bstep (se 1 (by rfl) ⟨2331368, by rfl⟩ : syracuseStep 3108491 = 4662737) B4662737
theorem B2072327 : Blo 2071435 2072327 := bstep (se 1 (by rfl) ⟨1554245, by rfl⟩ : syracuseStep 2072327 = 3108491) B3108491
theorem B2331373 : Blo 2071435 2331373 := bbase (se 3 (by rfl) ⟨437132, by rfl⟩ : syracuseStep 2331373 = 874265) (by norm_num)
theorem B3108497 : Blo 2071435 3108497 := bstep (se 2 (by rfl) ⟨1165686, by rfl⟩ : syracuseStep 3108497 = 2331373) B2331373
theorem B2072331 : Blo 2071435 2072331 := bstep (se 1 (by rfl) ⟨1554248, by rfl⟩ : syracuseStep 2072331 = 3108497) B3108497
theorem B6994133 : Blo 2071435 6994133 := bbase (se 7 (by rfl) ⟨81962, by rfl⟩ : syracuseStep 6994133 = 163925) (by norm_num)
theorem B4662755 : Blo 2071435 4662755 := bstep (se 1 (by rfl) ⟨3497066, by rfl⟩ : syracuseStep 4662755 = 6994133) B6994133
theorem B3108503 : Blo 2071435 3108503 := bstep (se 1 (by rfl) ⟨2331377, by rfl⟩ : syracuseStep 3108503 = 4662755) B4662755
theorem B2072335 : Blo 2071435 2072335 := bstep (se 1 (by rfl) ⟨1554251, by rfl⟩ : syracuseStep 2072335 = 3108503) B3108503
theorem B3108509 : Blo 2071435 3108509 := bbase (se 3 (by rfl) ⟨582845, by rfl⟩ : syracuseStep 3108509 = 1165691) (by norm_num)
theorem B2072339 : Blo 2071435 2072339 := bstep (se 1 (by rfl) ⟨1554254, by rfl⟩ : syracuseStep 2072339 = 3108509) B3108509
theorem B4662773 : Blo 2071435 4662773 := bbase (se 5 (by rfl) ⟨218567, by rfl⟩ : syracuseStep 4662773 = 437135) (by norm_num)
theorem B3108515 : Blo 2071435 3108515 := bstep (se 1 (by rfl) ⟨2331386, by rfl⟩ : syracuseStep 3108515 = 4662773) B4662773
theorem B2072343 : Blo 2071435 2072343 := bstep (se 1 (by rfl) ⟨1554257, by rfl⟩ : syracuseStep 2072343 = 3108515) B3108515
theorem B114981205 : Blo 2071435 114981205 := bbase (se 10 (by rfl) ⟨168429, by rfl⟩ : syracuseStep 114981205 = 336859) (by norm_num)
theorem B153308273 : Blo 2071435 153308273 := bstep (se 2 (by rfl) ⟨57490602, by rfl⟩ : syracuseStep 153308273 = 114981205) B114981205
theorem B408822061 : Blo 2071435 408822061 := bstep (se 3 (by rfl) ⟨76654136, by rfl⟩ : syracuseStep 408822061 = 153308273) B153308273
theorem B545096081 : Blo 2071435 545096081 := bstep (se 2 (by rfl) ⟨204411030, by rfl⟩ : syracuseStep 545096081 = 408822061) B408822061
theorem B363397387 : Blo 2071435 363397387 := bstep (se 1 (by rfl) ⟨272548040, by rfl⟩ : syracuseStep 363397387 = 545096081) B545096081
theorem B484529849 : Blo 2071435 484529849 := bstep (se 2 (by rfl) ⟨181698693, by rfl⟩ : syracuseStep 484529849 = 363397387) B363397387
theorem B323019899 : Blo 2071435 323019899 := bstep (se 1 (by rfl) ⟨242264924, by rfl⟩ : syracuseStep 323019899 = 484529849) B484529849
theorem B215346599 : Blo 2071435 215346599 := bstep (se 1 (by rfl) ⟨161509949, by rfl⟩ : syracuseStep 215346599 = 323019899) B323019899
theorem B143564399 : Blo 2071435 143564399 := bstep (se 1 (by rfl) ⟨107673299, by rfl⟩ : syracuseStep 143564399 = 215346599) B215346599
theorem B95709599 : Blo 2071435 95709599 := bstep (se 1 (by rfl) ⟨71782199, by rfl⟩ : syracuseStep 95709599 = 143564399) B143564399
theorem B63806399 : Blo 2071435 63806399 := bstep (se 1 (by rfl) ⟨47854799, by rfl⟩ : syracuseStep 63806399 = 95709599) B95709599
theorem B42537599 : Blo 2071435 42537599 := bstep (se 1 (by rfl) ⟨31903199, by rfl⟩ : syracuseStep 42537599 = 63806399) B63806399
theorem B28358399 : Blo 2071435 28358399 := bstep (se 1 (by rfl) ⟨21268799, by rfl⟩ : syracuseStep 28358399 = 42537599) B42537599
theorem B18905599 : Blo 2071435 18905599 := bstep (se 1 (by rfl) ⟨14179199, by rfl⟩ : syracuseStep 18905599 = 28358399) B28358399
theorem B25207465 : Blo 2071435 25207465 := bstep (se 2 (by rfl) ⟨9452799, by rfl⟩ : syracuseStep 25207465 = 18905599) B18905599
theorem B33609953 : Blo 2071435 33609953 := bstep (se 2 (by rfl) ⟨12603732, by rfl⟩ : syracuseStep 33609953 = 25207465) B25207465
theorem B22406635 : Blo 2071435 22406635 := bstep (se 1 (by rfl) ⟨16804976, by rfl⟩ : syracuseStep 22406635 = 33609953) B33609953
theorem B29875513 : Blo 2071435 29875513 := bstep (se 2 (by rfl) ⟨11203317, by rfl⟩ : syracuseStep 29875513 = 22406635) B22406635
theorem B39834017 : Blo 2071435 39834017 := bstep (se 2 (by rfl) ⟨14937756, by rfl⟩ : syracuseStep 39834017 = 29875513) B29875513
theorem B26556011 : Blo 2071435 26556011 := bstep (se 1 (by rfl) ⟨19917008, by rfl⟩ : syracuseStep 26556011 = 39834017) B39834017
theorem B17704007 : Blo 2071435 17704007 := bstep (se 1 (by rfl) ⟨13278005, by rfl⟩ : syracuseStep 17704007 = 26556011) B26556011
theorem B11802671 : Blo 2071435 11802671 := bstep (se 1 (by rfl) ⟨8852003, by rfl⟩ : syracuseStep 11802671 = 17704007) B17704007
theorem B7868447 : Blo 2071435 7868447 := bstep (se 1 (by rfl) ⟨5901335, by rfl⟩ : syracuseStep 7868447 = 11802671) B11802671
theorem B5245631 : Blo 2071435 5245631 := bstep (se 1 (by rfl) ⟨3934223, by rfl⟩ : syracuseStep 5245631 = 7868447) B7868447
theorem B3497087 : Blo 2071435 3497087 := bstep (se 1 (by rfl) ⟨2622815, by rfl⟩ : syracuseStep 3497087 = 5245631) B5245631
theorem B2331391 : Blo 2071435 2331391 := bstep (se 1 (by rfl) ⟨1748543, by rfl⟩ : syracuseStep 2331391 = 3497087) B3497087
theorem B3108521 : Blo 2071435 3108521 := bstep (se 2 (by rfl) ⟨1165695, by rfl⟩ : syracuseStep 3108521 = 2331391) B2331391
theorem B2072347 : Blo 2071435 2072347 := bstep (se 1 (by rfl) ⟨1554260, by rfl⟩ : syracuseStep 2072347 = 3108521) B3108521
theorem B2213005 : Blo 2071435 2213005 := bbase (se 3 (by rfl) ⟨414938, by rfl⟩ : syracuseStep 2213005 = 829877) (by norm_num)
theorem B2950673 : Blo 2071435 2950673 := bstep (se 2 (by rfl) ⟨1106502, by rfl⟩ : syracuseStep 2950673 = 2213005) B2213005
theorem B7868461 : Blo 2071435 7868461 := bstep (se 3 (by rfl) ⟨1475336, by rfl⟩ : syracuseStep 7868461 = 2950673) B2950673
theorem B10491281 : Blo 2071435 10491281 := bstep (se 2 (by rfl) ⟨3934230, by rfl⟩ : syracuseStep 10491281 = 7868461) B7868461
theorem B6994187 : Blo 2071435 6994187 := bstep (se 1 (by rfl) ⟨5245640, by rfl⟩ : syracuseStep 6994187 = 10491281) B10491281
theorem B4662791 : Blo 2071435 4662791 := bstep (se 1 (by rfl) ⟨3497093, by rfl⟩ : syracuseStep 4662791 = 6994187) B6994187
theorem B3108527 : Blo 2071435 3108527 := bstep (se 1 (by rfl) ⟨2331395, by rfl⟩ : syracuseStep 3108527 = 4662791) B4662791
theorem B2072351 : Blo 2071435 2072351 := bstep (se 1 (by rfl) ⟨1554263, by rfl⟩ : syracuseStep 2072351 = 3108527) B3108527
theorem B3108533 : Blo 2071435 3108533 := bbase (se 5 (by rfl) ⟨145712, by rfl⟩ : syracuseStep 3108533 = 291425) (by norm_num)
theorem B2072355 : Blo 2071435 2072355 := bstep (se 1 (by rfl) ⟨1554266, by rfl⟩ : syracuseStep 2072355 = 3108533) B3108533
theorem B5245661 : Blo 2071435 5245661 := bbase (se 3 (by rfl) ⟨983561, by rfl⟩ : syracuseStep 5245661 = 1967123) (by norm_num)
theorem B3497107 : Blo 2071435 3497107 := bstep (se 1 (by rfl) ⟨2622830, by rfl⟩ : syracuseStep 3497107 = 5245661) B5245661
theorem B4662809 : Blo 2071435 4662809 := bstep (se 2 (by rfl) ⟨1748553, by rfl⟩ : syracuseStep 4662809 = 3497107) B3497107
theorem B3108539 : Blo 2071435 3108539 := bstep (se 1 (by rfl) ⟨2331404, by rfl⟩ : syracuseStep 3108539 = 4662809) B4662809
theorem B2072359 : Blo 2071435 2072359 := bstep (se 1 (by rfl) ⟨1554269, by rfl⟩ : syracuseStep 2072359 = 3108539) B3108539
theorem B2331409 : Blo 2071435 2331409 := bbase (se 2 (by rfl) ⟨874278, by rfl⟩ : syracuseStep 2331409 = 1748557) (by norm_num)
theorem B3108545 : Blo 2071435 3108545 := bstep (se 2 (by rfl) ⟨1165704, by rfl⟩ : syracuseStep 3108545 = 2331409) B2331409
theorem B2072363 : Blo 2071435 2072363 := bstep (se 1 (by rfl) ⟨1554272, by rfl⟩ : syracuseStep 2072363 = 3108545) B3108545
theorem B3934261 : Blo 2071435 3934261 := bbase (se 5 (by rfl) ⟨184418, by rfl⟩ : syracuseStep 3934261 = 368837) (by norm_num)
theorem B5245681 : Blo 2071435 5245681 := bstep (se 2 (by rfl) ⟨1967130, by rfl⟩ : syracuseStep 5245681 = 3934261) B3934261
theorem B6994241 : Blo 2071435 6994241 := bstep (se 2 (by rfl) ⟨2622840, by rfl⟩ : syracuseStep 6994241 = 5245681) B5245681
theorem B4662827 : Blo 2071435 4662827 := bstep (se 1 (by rfl) ⟨3497120, by rfl⟩ : syracuseStep 4662827 = 6994241) B6994241
theorem B3108551 : Blo 2071435 3108551 := bstep (se 1 (by rfl) ⟨2331413, by rfl⟩ : syracuseStep 3108551 = 4662827) B4662827
theorem B2072367 : Blo 2071435 2072367 := bstep (se 1 (by rfl) ⟨1554275, by rfl⟩ : syracuseStep 2072367 = 3108551) B3108551
theorem B3108557 : Blo 2071435 3108557 := bbase (se 3 (by rfl) ⟨582854, by rfl⟩ : syracuseStep 3108557 = 1165709) (by norm_num)
theorem B2072371 : Blo 2071435 2072371 := bstep (se 1 (by rfl) ⟨1554278, by rfl⟩ : syracuseStep 2072371 = 3108557) B3108557
theorem B4662845 : Blo 2071435 4662845 := bbase (se 3 (by rfl) ⟨874283, by rfl⟩ : syracuseStep 4662845 = 1748567) (by norm_num)
theorem B3108563 : Blo 2071435 3108563 := bstep (se 1 (by rfl) ⟨2331422, by rfl⟩ : syracuseStep 3108563 = 4662845) B4662845
theorem B2072375 : Blo 2071435 2072375 := bstep (se 1 (by rfl) ⟨1554281, by rfl⟩ : syracuseStep 2072375 = 3108563) B3108563
theorem B3497141 : Blo 2071435 3497141 := bbase (se 5 (by rfl) ⟨163928, by rfl⟩ : syracuseStep 3497141 = 327857) (by norm_num)
theorem B2331427 : Blo 2071435 2331427 := bstep (se 1 (by rfl) ⟨1748570, by rfl⟩ : syracuseStep 2331427 = 3497141) B3497141
theorem B3108569 : Blo 2071435 3108569 := bstep (se 2 (by rfl) ⟨1165713, by rfl⟩ : syracuseStep 3108569 = 2331427) B2331427
theorem B2072379 : Blo 2071435 2072379 := bstep (se 1 (by rfl) ⟨1554284, by rfl⟩ : syracuseStep 2072379 = 3108569) B3108569
theorem B3150989 : Blo 2071435 3150989 := bbase (se 3 (by rfl) ⟨590810, by rfl⟩ : syracuseStep 3150989 = 1181621) (by norm_num)
theorem B2100659 : Blo 2071435 2100659 := bstep (se 1 (by rfl) ⟨1575494, by rfl⟩ : syracuseStep 2100659 = 3150989) B3150989
theorem B5601757 : Blo 2071435 5601757 := bstep (se 3 (by rfl) ⟨1050329, by rfl⟩ : syracuseStep 5601757 = 2100659) B2100659
theorem B7469009 : Blo 2071435 7469009 := bstep (se 2 (by rfl) ⟨2800878, by rfl⟩ : syracuseStep 7469009 = 5601757) B5601757
theorem B4979339 : Blo 2071435 4979339 := bstep (se 1 (by rfl) ⟨3734504, by rfl⟩ : syracuseStep 4979339 = 7469009) B7469009
theorem B3319559 : Blo 2071435 3319559 := bstep (se 1 (by rfl) ⟨2489669, by rfl⟩ : syracuseStep 3319559 = 4979339) B4979339
theorem B2213039 : Blo 2071435 2213039 := bstep (se 1 (by rfl) ⟨1659779, by rfl⟩ : syracuseStep 2213039 = 3319559) B3319559
theorem B5901437 : Blo 2071435 5901437 := bstep (se 3 (by rfl) ⟨1106519, by rfl⟩ : syracuseStep 5901437 = 2213039) B2213039
theorem B15737165 : Blo 2071435 15737165 := bstep (se 3 (by rfl) ⟨2950718, by rfl⟩ : syracuseStep 15737165 = 5901437) B5901437
theorem B10491443 : Blo 2071435 10491443 := bstep (se 1 (by rfl) ⟨7868582, by rfl⟩ : syracuseStep 10491443 = 15737165) B15737165
theorem B6994295 : Blo 2071435 6994295 := bstep (se 1 (by rfl) ⟨5245721, by rfl⟩ : syracuseStep 6994295 = 10491443) B10491443
theorem B4662863 : Blo 2071435 4662863 := bstep (se 1 (by rfl) ⟨3497147, by rfl⟩ : syracuseStep 4662863 = 6994295) B6994295
theorem B3108575 : Blo 2071435 3108575 := bstep (se 1 (by rfl) ⟨2331431, by rfl⟩ : syracuseStep 3108575 = 4662863) B4662863
theorem B2072383 : Blo 2071435 2072383 := bstep (se 1 (by rfl) ⟨1554287, by rfl⟩ : syracuseStep 2072383 = 3108575) B3108575
theorem B3108581 : Blo 2071435 3108581 := bbase (se 4 (by rfl) ⟨291429, by rfl⟩ : syracuseStep 3108581 = 582859) (by norm_num)
theorem B2072387 : Blo 2071435 2072387 := bstep (se 1 (by rfl) ⟨1554290, by rfl⟩ : syracuseStep 2072387 = 3108581) B3108581
theorem B5901461 : Blo 2071435 5901461 := bbase (se 6 (by rfl) ⟨138315, by rfl⟩ : syracuseStep 5901461 = 276631) (by norm_num)
theorem B3934307 : Blo 2071435 3934307 := bstep (se 1 (by rfl) ⟨2950730, by rfl⟩ : syracuseStep 3934307 = 5901461) B5901461
theorem B2622871 : Blo 2071435 2622871 := bstep (se 1 (by rfl) ⟨1967153, by rfl⟩ : syracuseStep 2622871 = 3934307) B3934307
theorem B3497161 : Blo 2071435 3497161 := bstep (se 2 (by rfl) ⟨1311435, by rfl⟩ : syracuseStep 3497161 = 2622871) B2622871
theorem B4662881 : Blo 2071435 4662881 := bstep (se 2 (by rfl) ⟨1748580, by rfl⟩ : syracuseStep 4662881 = 3497161) B3497161
theorem B3108587 : Blo 2071435 3108587 := bstep (se 1 (by rfl) ⟨2331440, by rfl⟩ : syracuseStep 3108587 = 4662881) B4662881
theorem B2072391 : Blo 2071435 2072391 := bstep (se 1 (by rfl) ⟨1554293, by rfl⟩ : syracuseStep 2072391 = 3108587) B3108587
theorem B2331445 : Blo 2071435 2331445 := bbase (se 5 (by rfl) ⟨109286, by rfl⟩ : syracuseStep 2331445 = 218573) (by norm_num)
theorem B3108593 : Blo 2071435 3108593 := bstep (se 2 (by rfl) ⟨1165722, by rfl⟩ : syracuseStep 3108593 = 2331445) B2331445
theorem B2072395 : Blo 2071435 2072395 := bstep (se 1 (by rfl) ⟨1554296, by rfl⟩ : syracuseStep 2072395 = 3108593) B3108593
theorem B2622881 : Blo 2071435 2622881 := bbase (se 2 (by rfl) ⟨983580, by rfl⟩ : syracuseStep 2622881 = 1967161) (by norm_num)
theorem B6994349 : Blo 2071435 6994349 := bstep (se 3 (by rfl) ⟨1311440, by rfl⟩ : syracuseStep 6994349 = 2622881) B2622881
theorem B4662899 : Blo 2071435 4662899 := bstep (se 1 (by rfl) ⟨3497174, by rfl⟩ : syracuseStep 4662899 = 6994349) B6994349
theorem B3108599 : Blo 2071435 3108599 := bstep (se 1 (by rfl) ⟨2331449, by rfl⟩ : syracuseStep 3108599 = 4662899) B4662899
theorem B2072399 : Blo 2071435 2072399 := bstep (se 1 (by rfl) ⟨1554299, by rfl⟩ : syracuseStep 2072399 = 3108599) B3108599
theorem B3108605 : Blo 2071435 3108605 := bbase (se 3 (by rfl) ⟨582863, by rfl⟩ : syracuseStep 3108605 = 1165727) (by norm_num)
theorem B2072403 : Blo 2071435 2072403 := bstep (se 1 (by rfl) ⟨1554302, by rfl⟩ : syracuseStep 2072403 = 3108605) B3108605
theorem B4662917 : Blo 2071435 4662917 := bbase (se 4 (by rfl) ⟨437148, by rfl⟩ : syracuseStep 4662917 = 874297) (by norm_num)
theorem B3108611 : Blo 2071435 3108611 := bstep (se 1 (by rfl) ⟨2331458, by rfl⟩ : syracuseStep 3108611 = 4662917) B4662917
theorem B2072407 : Blo 2071435 2072407 := bstep (se 1 (by rfl) ⟨1554305, by rfl⟩ : syracuseStep 2072407 = 3108611) B3108611
theorem B23928149 : Blo 2071435 23928149 := bbase (se 11 (by rfl) ⟨17525, by rfl⟩ : syracuseStep 23928149 = 35051) (by norm_num)
theorem B15952099 : Blo 2071435 15952099 := bstep (se 1 (by rfl) ⟨11964074, by rfl⟩ : syracuseStep 15952099 = 23928149) B23928149
theorem B21269465 : Blo 2071435 21269465 := bstep (se 2 (by rfl) ⟨7976049, by rfl⟩ : syracuseStep 21269465 = 15952099) B15952099
theorem B14179643 : Blo 2071435 14179643 := bstep (se 1 (by rfl) ⟨10634732, by rfl⟩ : syracuseStep 14179643 = 21269465) B21269465
theorem B9453095 : Blo 2071435 9453095 := bstep (se 1 (by rfl) ⟨7089821, by rfl⟩ : syracuseStep 9453095 = 14179643) B14179643
theorem B6302063 : Blo 2071435 6302063 := bstep (se 1 (by rfl) ⟨4726547, by rfl⟩ : syracuseStep 6302063 = 9453095) B9453095
theorem B16805501 : Blo 2071435 16805501 := bstep (se 3 (by rfl) ⟨3151031, by rfl⟩ : syracuseStep 16805501 = 6302063) B6302063
theorem B11203667 : Blo 2071435 11203667 := bstep (se 1 (by rfl) ⟨8402750, by rfl⟩ : syracuseStep 11203667 = 16805501) B16805501
theorem B7469111 : Blo 2071435 7469111 := bstep (se 1 (by rfl) ⟨5601833, by rfl⟩ : syracuseStep 7469111 = 11203667) B11203667
theorem B4979407 : Blo 2071435 4979407 := bstep (se 1 (by rfl) ⟨3734555, by rfl⟩ : syracuseStep 4979407 = 7469111) B7469111
theorem B6639209 : Blo 2071435 6639209 := bstep (se 2 (by rfl) ⟨2489703, by rfl⟩ : syracuseStep 6639209 = 4979407) B4979407
theorem B4426139 : Blo 2071435 4426139 := bstep (se 1 (by rfl) ⟨3319604, by rfl⟩ : syracuseStep 4426139 = 6639209) B6639209
theorem B2950759 : Blo 2071435 2950759 := bstep (se 1 (by rfl) ⟨2213069, by rfl⟩ : syracuseStep 2950759 = 4426139) B4426139
theorem B3934345 : Blo 2071435 3934345 := bstep (se 2 (by rfl) ⟨1475379, by rfl⟩ : syracuseStep 3934345 = 2950759) B2950759
theorem B5245793 : Blo 2071435 5245793 := bstep (se 2 (by rfl) ⟨1967172, by rfl⟩ : syracuseStep 5245793 = 3934345) B3934345
theorem B3497195 : Blo 2071435 3497195 := bstep (se 1 (by rfl) ⟨2622896, by rfl⟩ : syracuseStep 3497195 = 5245793) B5245793
theorem B2331463 : Blo 2071435 2331463 := bstep (se 1 (by rfl) ⟨1748597, by rfl⟩ : syracuseStep 2331463 = 3497195) B3497195
theorem B3108617 : Blo 2071435 3108617 := bstep (se 2 (by rfl) ⟨1165731, by rfl⟩ : syracuseStep 3108617 = 2331463) B2331463
theorem B2072411 : Blo 2071435 2072411 := bstep (se 1 (by rfl) ⟨1554308, by rfl⟩ : syracuseStep 2072411 = 3108617) B3108617
theorem B10491605 : Blo 2071435 10491605 := bbase (se 7 (by rfl) ⟨122948, by rfl⟩ : syracuseStep 10491605 = 245897) (by norm_num)
theorem B6994403 : Blo 2071435 6994403 := bstep (se 1 (by rfl) ⟨5245802, by rfl⟩ : syracuseStep 6994403 = 10491605) B10491605
theorem B4662935 : Blo 2071435 4662935 := bstep (se 1 (by rfl) ⟨3497201, by rfl⟩ : syracuseStep 4662935 = 6994403) B6994403
theorem B3108623 : Blo 2071435 3108623 := bstep (se 1 (by rfl) ⟨2331467, by rfl⟩ : syracuseStep 3108623 = 4662935) B4662935
theorem B2072415 : Blo 2071435 2072415 := bstep (se 1 (by rfl) ⟨1554311, by rfl⟩ : syracuseStep 2072415 = 3108623) B3108623
theorem B3108629 : Blo 2071435 3108629 := bbase (se 6 (by rfl) ⟨72858, by rfl⟩ : syracuseStep 3108629 = 145717) (by norm_num)
theorem B2072419 : Blo 2071435 2072419 := bstep (se 1 (by rfl) ⟨1554314, by rfl⟩ : syracuseStep 2072419 = 3108629) B3108629
theorem B24254741 : Blo 2071435 24254741 := bbase (se 6 (by rfl) ⟨568470, by rfl⟩ : syracuseStep 24254741 = 1136941) (by norm_num)
theorem B16169827 : Blo 2071435 16169827 := bstep (se 1 (by rfl) ⟨12127370, by rfl⟩ : syracuseStep 16169827 = 24254741) B24254741
theorem B21559769 : Blo 2071435 21559769 := bstep (se 2 (by rfl) ⟨8084913, by rfl⟩ : syracuseStep 21559769 = 16169827) B16169827
theorem B14373179 : Blo 2071435 14373179 := bstep (se 1 (by rfl) ⟨10779884, by rfl⟩ : syracuseStep 14373179 = 21559769) B21559769
theorem B9582119 : Blo 2071435 9582119 := bstep (se 1 (by rfl) ⟨7186589, by rfl⟩ : syracuseStep 9582119 = 14373179) B14373179
theorem B6388079 : Blo 2071435 6388079 := bstep (se 1 (by rfl) ⟨4791059, by rfl⟩ : syracuseStep 6388079 = 9582119) B9582119
theorem B17034877 : Blo 2071435 17034877 := bstep (se 3 (by rfl) ⟨3194039, by rfl⟩ : syracuseStep 17034877 = 6388079) B6388079
theorem B22713169 : Blo 2071435 22713169 := bstep (se 2 (by rfl) ⟨8517438, by rfl⟩ : syracuseStep 22713169 = 17034877) B17034877
theorem B30284225 : Blo 2071435 30284225 := bstep (se 2 (by rfl) ⟨11356584, by rfl⟩ : syracuseStep 30284225 = 22713169) B22713169
theorem B20189483 : Blo 2071435 20189483 := bstep (se 1 (by rfl) ⟨15142112, by rfl⟩ : syracuseStep 20189483 = 30284225) B30284225
theorem B13459655 : Blo 2071435 13459655 := bstep (se 1 (by rfl) ⟨10094741, by rfl⟩ : syracuseStep 13459655 = 20189483) B20189483
theorem B35892413 : Blo 2071435 35892413 := bstep (se 3 (by rfl) ⟨6729827, by rfl⟩ : syracuseStep 35892413 = 13459655) B13459655
theorem B23928275 : Blo 2071435 23928275 := bstep (se 1 (by rfl) ⟨17946206, by rfl⟩ : syracuseStep 23928275 = 35892413) B35892413
theorem B15952183 : Blo 2071435 15952183 := bstep (se 1 (by rfl) ⟨11964137, by rfl⟩ : syracuseStep 15952183 = 23928275) B23928275
theorem B85078309 : Blo 2071435 85078309 := bstep (se 4 (by rfl) ⟨7976091, by rfl⟩ : syracuseStep 85078309 = 15952183) B15952183
theorem B113437745 : Blo 2071435 113437745 := bstep (se 2 (by rfl) ⟨42539154, by rfl⟩ : syracuseStep 113437745 = 85078309) B85078309
theorem B75625163 : Blo 2071435 75625163 := bstep (se 1 (by rfl) ⟨56718872, by rfl⟩ : syracuseStep 75625163 = 113437745) B113437745
theorem B50416775 : Blo 2071435 50416775 := bstep (se 1 (by rfl) ⟨37812581, by rfl⟩ : syracuseStep 50416775 = 75625163) B75625163
theorem B33611183 : Blo 2071435 33611183 := bstep (se 1 (by rfl) ⟨25208387, by rfl⟩ : syracuseStep 33611183 = 50416775) B50416775
theorem B22407455 : Blo 2071435 22407455 := bstep (se 1 (by rfl) ⟨16805591, by rfl⟩ : syracuseStep 22407455 = 33611183) B33611183
theorem B59753213 : Blo 2071435 59753213 := bstep (se 3 (by rfl) ⟨11203727, by rfl⟩ : syracuseStep 59753213 = 22407455) B22407455
theorem B39835475 : Blo 2071435 39835475 := bstep (se 1 (by rfl) ⟨29876606, by rfl⟩ : syracuseStep 39835475 = 59753213) B59753213
theorem B26556983 : Blo 2071435 26556983 := bstep (se 1 (by rfl) ⟨19917737, by rfl⟩ : syracuseStep 26556983 = 39835475) B39835475
theorem B17704655 : Blo 2071435 17704655 := bstep (se 1 (by rfl) ⟨13278491, by rfl⟩ : syracuseStep 17704655 = 26556983) B26556983
theorem B11803103 : Blo 2071435 11803103 := bstep (se 1 (by rfl) ⟨8852327, by rfl⟩ : syracuseStep 11803103 = 17704655) B17704655
theorem B7868735 : Blo 2071435 7868735 := bstep (se 1 (by rfl) ⟨5901551, by rfl⟩ : syracuseStep 7868735 = 11803103) B11803103
theorem B5245823 : Blo 2071435 5245823 := bstep (se 1 (by rfl) ⟨3934367, by rfl⟩ : syracuseStep 5245823 = 7868735) B7868735
theorem B3497215 : Blo 2071435 3497215 := bstep (se 1 (by rfl) ⟨2622911, by rfl⟩ : syracuseStep 3497215 = 5245823) B5245823
theorem B4662953 : Blo 2071435 4662953 := bstep (se 2 (by rfl) ⟨1748607, by rfl⟩ : syracuseStep 4662953 = 3497215) B3497215
theorem B3108635 : Blo 2071435 3108635 := bstep (se 1 (by rfl) ⟨2331476, by rfl⟩ : syracuseStep 3108635 = 4662953) B4662953
theorem B2072423 : Blo 2071435 2072423 := bstep (se 1 (by rfl) ⟨1554317, by rfl⟩ : syracuseStep 2072423 = 3108635) B3108635
theorem B2331481 : Blo 2071435 2331481 := bbase (se 2 (by rfl) ⟨874305, by rfl⟩ : syracuseStep 2331481 = 1748611) (by norm_num)
theorem B3108641 : Blo 2071435 3108641 := bstep (se 2 (by rfl) ⟨1165740, by rfl⟩ : syracuseStep 3108641 = 2331481) B2331481
theorem B2072427 : Blo 2071435 2072427 := bstep (se 1 (by rfl) ⟨1554320, by rfl⟩ : syracuseStep 2072427 = 3108641) B3108641
theorem B4426181 : Blo 2071435 4426181 := bbase (se 4 (by rfl) ⟨414954, by rfl⟩ : syracuseStep 4426181 = 829909) (by norm_num)
theorem B2950787 : Blo 2071435 2950787 := bstep (se 1 (by rfl) ⟨2213090, by rfl⟩ : syracuseStep 2950787 = 4426181) B4426181
theorem B7868765 : Blo 2071435 7868765 := bstep (se 3 (by rfl) ⟨1475393, by rfl⟩ : syracuseStep 7868765 = 2950787) B2950787
theorem B5245843 : Blo 2071435 5245843 := bstep (se 1 (by rfl) ⟨3934382, by rfl⟩ : syracuseStep 5245843 = 7868765) B7868765
theorem B6994457 : Blo 2071435 6994457 := bstep (se 2 (by rfl) ⟨2622921, by rfl⟩ : syracuseStep 6994457 = 5245843) B5245843
theorem B4662971 : Blo 2071435 4662971 := bstep (se 1 (by rfl) ⟨3497228, by rfl⟩ : syracuseStep 4662971 = 6994457) B6994457
theorem B3108647 : Blo 2071435 3108647 := bstep (se 1 (by rfl) ⟨2331485, by rfl⟩ : syracuseStep 3108647 = 4662971) B4662971
theorem B2072431 : Blo 2071435 2072431 := bstep (se 1 (by rfl) ⟨1554323, by rfl⟩ : syracuseStep 2072431 = 3108647) B3108647
theorem B3108653 : Blo 2071435 3108653 := bbase (se 3 (by rfl) ⟨582872, by rfl⟩ : syracuseStep 3108653 = 1165745) (by norm_num)
theorem B2072435 : Blo 2071435 2072435 := bstep (se 1 (by rfl) ⟨1554326, by rfl⟩ : syracuseStep 2072435 = 3108653) B3108653
theorem B4662989 : Blo 2071435 4662989 := bbase (se 3 (by rfl) ⟨874310, by rfl⟩ : syracuseStep 4662989 = 1748621) (by norm_num)
theorem B3108659 : Blo 2071435 3108659 := bstep (se 1 (by rfl) ⟨2331494, by rfl⟩ : syracuseStep 3108659 = 4662989) B4662989
theorem B2072439 : Blo 2071435 2072439 := bstep (se 1 (by rfl) ⟨1554329, by rfl⟩ : syracuseStep 2072439 = 3108659) B3108659
theorem B2622937 : Blo 2071435 2622937 := bbase (se 2 (by rfl) ⟨983601, by rfl⟩ : syracuseStep 2622937 = 1967203) (by norm_num)
theorem B3497249 : Blo 2071435 3497249 := bstep (se 2 (by rfl) ⟨1311468, by rfl⟩ : syracuseStep 3497249 = 2622937) B2622937
theorem B2331499 : Blo 2071435 2331499 := bstep (se 1 (by rfl) ⟨1748624, by rfl⟩ : syracuseStep 2331499 = 3497249) B3497249
theorem B3108665 : Blo 2071435 3108665 := bstep (se 2 (by rfl) ⟨1165749, by rfl⟩ : syracuseStep 3108665 = 2331499) B2331499
theorem B2072443 : Blo 2071435 2072443 := bstep (se 1 (by rfl) ⟨1554332, by rfl⟩ : syracuseStep 2072443 = 3108665) B3108665
theorem B3319661 : Blo 2071435 3319661 := bbase (se 3 (by rfl) ⟨622436, by rfl⟩ : syracuseStep 3319661 = 1244873) (by norm_num)
theorem B8852429 : Blo 2071435 8852429 := bstep (se 3 (by rfl) ⟨1659830, by rfl⟩ : syracuseStep 8852429 = 3319661) B3319661
theorem B23606477 : Blo 2071435 23606477 := bstep (se 3 (by rfl) ⟨4426214, by rfl⟩ : syracuseStep 23606477 = 8852429) B8852429
theorem B15737651 : Blo 2071435 15737651 := bstep (se 1 (by rfl) ⟨11803238, by rfl⟩ : syracuseStep 15737651 = 23606477) B23606477
theorem B10491767 : Blo 2071435 10491767 := bstep (se 1 (by rfl) ⟨7868825, by rfl⟩ : syracuseStep 10491767 = 15737651) B15737651
theorem B6994511 : Blo 2071435 6994511 := bstep (se 1 (by rfl) ⟨5245883, by rfl⟩ : syracuseStep 6994511 = 10491767) B10491767
theorem B4663007 : Blo 2071435 4663007 := bstep (se 1 (by rfl) ⟨3497255, by rfl⟩ : syracuseStep 4663007 = 6994511) B6994511
theorem B3108671 : Blo 2071435 3108671 := bstep (se 1 (by rfl) ⟨2331503, by rfl⟩ : syracuseStep 3108671 = 4663007) B4663007
theorem B2072447 : Blo 2071435 2072447 := bstep (se 1 (by rfl) ⟨1554335, by rfl⟩ : syracuseStep 2072447 = 3108671) B3108671
theorem B3108677 : Blo 2071435 3108677 := bbase (se 4 (by rfl) ⟨291438, by rfl⟩ : syracuseStep 3108677 = 582877) (by norm_num)
theorem B2072451 : Blo 2071435 2072451 := bstep (se 1 (by rfl) ⟨1554338, by rfl⟩ : syracuseStep 2072451 = 3108677) B3108677
theorem B3497269 : Blo 2071435 3497269 := bbase (se 5 (by rfl) ⟨163934, by rfl⟩ : syracuseStep 3497269 = 327869) (by norm_num)
theorem B4663025 : Blo 2071435 4663025 := bstep (se 2 (by rfl) ⟨1748634, by rfl⟩ : syracuseStep 4663025 = 3497269) B3497269
theorem B3108683 : Blo 2071435 3108683 := bstep (se 1 (by rfl) ⟨2331512, by rfl⟩ : syracuseStep 3108683 = 4663025) B4663025
theorem B2072455 : Blo 2071435 2072455 := bstep (se 1 (by rfl) ⟨1554341, by rfl⟩ : syracuseStep 2072455 = 3108683) B3108683
theorem B2331517 : Blo 2071435 2331517 := bbase (se 3 (by rfl) ⟨437159, by rfl⟩ : syracuseStep 2331517 = 874319) (by norm_num)
theorem B3108689 : Blo 2071435 3108689 := bstep (se 2 (by rfl) ⟨1165758, by rfl⟩ : syracuseStep 3108689 = 2331517) B2331517
theorem B2072459 : Blo 2071435 2072459 := bstep (se 1 (by rfl) ⟨1554344, by rfl⟩ : syracuseStep 2072459 = 3108689) B3108689
theorem B6994565 : Blo 2071435 6994565 := bbase (se 4 (by rfl) ⟨655740, by rfl⟩ : syracuseStep 6994565 = 1311481) (by norm_num)
theorem B4663043 : Blo 2071435 4663043 := bstep (se 1 (by rfl) ⟨3497282, by rfl⟩ : syracuseStep 4663043 = 6994565) B6994565
theorem B3108695 : Blo 2071435 3108695 := bstep (se 1 (by rfl) ⟨2331521, by rfl⟩ : syracuseStep 3108695 = 4663043) B4663043
theorem B2072463 : Blo 2071435 2072463 := bstep (se 1 (by rfl) ⟨1554347, by rfl⟩ : syracuseStep 2072463 = 3108695) B3108695
theorem B3108701 : Blo 2071435 3108701 := bbase (se 3 (by rfl) ⟨582881, by rfl⟩ : syracuseStep 3108701 = 1165763) (by norm_num)
theorem B2072467 : Blo 2071435 2072467 := bstep (se 1 (by rfl) ⟨1554350, by rfl⟩ : syracuseStep 2072467 = 3108701) B3108701
theorem B4663061 : Blo 2071435 4663061 := bbase (se 6 (by rfl) ⟨109290, by rfl⟩ : syracuseStep 4663061 = 218581) (by norm_num)
theorem B3108707 : Blo 2071435 3108707 := bstep (se 1 (by rfl) ⟨2331530, by rfl⟩ : syracuseStep 3108707 = 4663061) B4663061
theorem B2072471 : Blo 2071435 2072471 := bstep (se 1 (by rfl) ⟨1554353, by rfl⟩ : syracuseStep 2072471 = 3108707) B3108707
theorem B7868933 : Blo 2071435 7868933 := bbase (se 4 (by rfl) ⟨737712, by rfl⟩ : syracuseStep 7868933 = 1475425) (by norm_num)
theorem B5245955 : Blo 2071435 5245955 := bstep (se 1 (by rfl) ⟨3934466, by rfl⟩ : syracuseStep 5245955 = 7868933) B7868933
theorem B3497303 : Blo 2071435 3497303 := bstep (se 1 (by rfl) ⟨2622977, by rfl⟩ : syracuseStep 3497303 = 5245955) B5245955
theorem B2331535 : Blo 2071435 2331535 := bstep (se 1 (by rfl) ⟨1748651, by rfl⟩ : syracuseStep 2331535 = 3497303) B3497303
theorem B3108713 : Blo 2071435 3108713 := bstep (se 2 (by rfl) ⟨1165767, by rfl⟩ : syracuseStep 3108713 = 2331535) B2331535
theorem B2072475 : Blo 2071435 2072475 := bstep (se 1 (by rfl) ⟨1554356, by rfl⟩ : syracuseStep 2072475 = 3108713) B3108713
theorem B3734677 : Blo 2071435 3734677 := bbase (se 6 (by rfl) ⟨87531, by rfl⟩ : syracuseStep 3734677 = 175063) (by norm_num)
theorem B4979569 : Blo 2071435 4979569 := bstep (se 2 (by rfl) ⟨1867338, by rfl⟩ : syracuseStep 4979569 = 3734677) B3734677
theorem B6639425 : Blo 2071435 6639425 := bstep (se 2 (by rfl) ⟨2489784, by rfl⟩ : syracuseStep 6639425 = 4979569) B4979569
theorem B4426283 : Blo 2071435 4426283 := bstep (se 1 (by rfl) ⟨3319712, by rfl⟩ : syracuseStep 4426283 = 6639425) B6639425
theorem B11803421 : Blo 2071435 11803421 := bstep (se 3 (by rfl) ⟨2213141, by rfl⟩ : syracuseStep 11803421 = 4426283) B4426283
theorem B7868947 : Blo 2071435 7868947 := bstep (se 1 (by rfl) ⟨5901710, by rfl⟩ : syracuseStep 7868947 = 11803421) B11803421
theorem B10491929 : Blo 2071435 10491929 := bstep (se 2 (by rfl) ⟨3934473, by rfl⟩ : syracuseStep 10491929 = 7868947) B7868947
theorem B6994619 : Blo 2071435 6994619 := bstep (se 1 (by rfl) ⟨5245964, by rfl⟩ : syracuseStep 6994619 = 10491929) B10491929
theorem B4663079 : Blo 2071435 4663079 := bstep (se 1 (by rfl) ⟨3497309, by rfl⟩ : syracuseStep 4663079 = 6994619) B6994619
theorem B3108719 : Blo 2071435 3108719 := bstep (se 1 (by rfl) ⟨2331539, by rfl⟩ : syracuseStep 3108719 = 4663079) B4663079
theorem B2072479 : Blo 2071435 2072479 := bstep (se 1 (by rfl) ⟨1554359, by rfl⟩ : syracuseStep 2072479 = 3108719) B3108719
theorem B3108725 : Blo 2071435 3108725 := bbase (se 5 (by rfl) ⟨145721, by rfl⟩ : syracuseStep 3108725 = 291443) (by norm_num)
theorem B2072483 : Blo 2071435 2072483 := bstep (se 1 (by rfl) ⟨1554362, by rfl⟩ : syracuseStep 2072483 = 3108725) B3108725
theorem B4426301 : Blo 2071435 4426301 := bbase (se 3 (by rfl) ⟨829931, by rfl⟩ : syracuseStep 4426301 = 1659863) (by norm_num)
theorem B2950867 : Blo 2071435 2950867 := bstep (se 1 (by rfl) ⟨2213150, by rfl⟩ : syracuseStep 2950867 = 4426301) B4426301
theorem B3934489 : Blo 2071435 3934489 := bstep (se 2 (by rfl) ⟨1475433, by rfl⟩ : syracuseStep 3934489 = 2950867) B2950867
theorem B5245985 : Blo 2071435 5245985 := bstep (se 2 (by rfl) ⟨1967244, by rfl⟩ : syracuseStep 5245985 = 3934489) B3934489
theorem B3497323 : Blo 2071435 3497323 := bstep (se 1 (by rfl) ⟨2622992, by rfl⟩ : syracuseStep 3497323 = 5245985) B5245985
theorem B4663097 : Blo 2071435 4663097 := bstep (se 2 (by rfl) ⟨1748661, by rfl⟩ : syracuseStep 4663097 = 3497323) B3497323
theorem B3108731 : Blo 2071435 3108731 := bstep (se 1 (by rfl) ⟨2331548, by rfl⟩ : syracuseStep 3108731 = 4663097) B4663097
theorem B2072487 : Blo 2071435 2072487 := bstep (se 1 (by rfl) ⟨1554365, by rfl⟩ : syracuseStep 2072487 = 3108731) B3108731
theorem B2331553 : Blo 2071435 2331553 := bbase (se 2 (by rfl) ⟨874332, by rfl⟩ : syracuseStep 2331553 = 1748665) (by norm_num)
theorem B3108737 : Blo 2071435 3108737 := bstep (se 2 (by rfl) ⟨1165776, by rfl⟩ : syracuseStep 3108737 = 2331553) B2331553
theorem B2072491 : Blo 2071435 2072491 := bstep (se 1 (by rfl) ⟨1554368, by rfl⟩ : syracuseStep 2072491 = 3108737) B3108737
theorem B5246005 : Blo 2071435 5246005 := bbase (se 5 (by rfl) ⟨245906, by rfl⟩ : syracuseStep 5246005 = 491813) (by norm_num)
theorem B6994673 : Blo 2071435 6994673 := bstep (se 2 (by rfl) ⟨2623002, by rfl⟩ : syracuseStep 6994673 = 5246005) B5246005
theorem B4663115 : Blo 2071435 4663115 := bstep (se 1 (by rfl) ⟨3497336, by rfl⟩ : syracuseStep 4663115 = 6994673) B6994673
theorem B3108743 : Blo 2071435 3108743 := bstep (se 1 (by rfl) ⟨2331557, by rfl⟩ : syracuseStep 3108743 = 4663115) B4663115
theorem B2072495 : Blo 2071435 2072495 := bstep (se 1 (by rfl) ⟨1554371, by rfl⟩ : syracuseStep 2072495 = 3108743) B3108743
theorem B3108749 : Blo 2071435 3108749 := bbase (se 3 (by rfl) ⟨582890, by rfl⟩ : syracuseStep 3108749 = 1165781) (by norm_num)
theorem B2072499 : Blo 2071435 2072499 := bstep (se 1 (by rfl) ⟨1554374, by rfl⟩ : syracuseStep 2072499 = 3108749) B3108749
theorem B4663133 : Blo 2071435 4663133 := bbase (se 3 (by rfl) ⟨874337, by rfl⟩ : syracuseStep 4663133 = 1748675) (by norm_num)
theorem B3108755 : Blo 2071435 3108755 := bstep (se 1 (by rfl) ⟨2331566, by rfl⟩ : syracuseStep 3108755 = 4663133) B4663133
theorem B2072503 : Blo 2071435 2072503 := bstep (se 1 (by rfl) ⟨1554377, by rfl⟩ : syracuseStep 2072503 = 3108755) B3108755
theorem B3497357 : Blo 2071435 3497357 := bbase (se 3 (by rfl) ⟨655754, by rfl⟩ : syracuseStep 3497357 = 1311509) (by norm_num)
theorem B2331571 : Blo 2071435 2331571 := bstep (se 1 (by rfl) ⟨1748678, by rfl⟩ : syracuseStep 2331571 = 3497357) B3497357
theorem B3108761 : Blo 2071435 3108761 := bstep (se 2 (by rfl) ⟨1165785, by rfl⟩ : syracuseStep 3108761 = 2331571) B2331571
theorem B2072507 : Blo 2071435 2072507 := bstep (se 1 (by rfl) ⟨1554380, by rfl⟩ : syracuseStep 2072507 = 3108761) B3108761
theorem B5186261 : Blo 2071435 5186261 := bbase (se 7 (by rfl) ⟨60776, by rfl⟩ : syracuseStep 5186261 = 121553) (by norm_num)
theorem B3457507 : Blo 2071435 3457507 := bstep (se 1 (by rfl) ⟨2593130, by rfl⟩ : syracuseStep 3457507 = 5186261) B5186261
theorem B4610009 : Blo 2071435 4610009 := bstep (se 2 (by rfl) ⟨1728753, by rfl⟩ : syracuseStep 4610009 = 3457507) B3457507
theorem B3073339 : Blo 2071435 3073339 := bstep (se 1 (by rfl) ⟨2305004, by rfl⟩ : syracuseStep 3073339 = 4610009) B4610009
theorem B4097785 : Blo 2071435 4097785 := bstep (se 2 (by rfl) ⟨1536669, by rfl⟩ : syracuseStep 4097785 = 3073339) B3073339
theorem B5463713 : Blo 2071435 5463713 := bstep (se 2 (by rfl) ⟨2048892, by rfl⟩ : syracuseStep 5463713 = 4097785) B4097785
theorem B14569901 : Blo 2071435 14569901 := bstep (se 3 (by rfl) ⟨2731856, by rfl⟩ : syracuseStep 14569901 = 5463713) B5463713
theorem B9713267 : Blo 2071435 9713267 := bstep (se 1 (by rfl) ⟨7284950, by rfl⟩ : syracuseStep 9713267 = 14569901) B14569901
theorem B6475511 : Blo 2071435 6475511 := bstep (se 1 (by rfl) ⟨4856633, by rfl⟩ : syracuseStep 6475511 = 9713267) B9713267
theorem B4317007 : Blo 2071435 4317007 := bstep (se 1 (by rfl) ⟨3237755, by rfl⟩ : syracuseStep 4317007 = 6475511) B6475511
theorem B5756009 : Blo 2071435 5756009 := bstep (se 2 (by rfl) ⟨2158503, by rfl⟩ : syracuseStep 5756009 = 4317007) B4317007
theorem B15349357 : Blo 2071435 15349357 := bstep (se 3 (by rfl) ⟨2878004, by rfl⟩ : syracuseStep 15349357 = 5756009) B5756009
theorem B81863237 : Blo 2071435 81863237 := bstep (se 4 (by rfl) ⟨7674678, by rfl⟩ : syracuseStep 81863237 = 15349357) B15349357
theorem B54575491 : Blo 2071435 54575491 := bstep (se 1 (by rfl) ⟨40931618, by rfl⟩ : syracuseStep 54575491 = 81863237) B81863237
theorem B72767321 : Blo 2071435 72767321 := bstep (se 2 (by rfl) ⟨27287745, by rfl⟩ : syracuseStep 72767321 = 54575491) B54575491
theorem B48511547 : Blo 2071435 48511547 := bstep (se 1 (by rfl) ⟨36383660, by rfl⟩ : syracuseStep 48511547 = 72767321) B72767321
theorem B32341031 : Blo 2071435 32341031 := bstep (se 1 (by rfl) ⟨24255773, by rfl⟩ : syracuseStep 32341031 = 48511547) B48511547
theorem B21560687 : Blo 2071435 21560687 := bstep (se 1 (by rfl) ⟨16170515, by rfl⟩ : syracuseStep 21560687 = 32341031) B32341031
theorem B14373791 : Blo 2071435 14373791 := bstep (se 1 (by rfl) ⟨10780343, by rfl⟩ : syracuseStep 14373791 = 21560687) B21560687
theorem B9582527 : Blo 2071435 9582527 := bstep (se 1 (by rfl) ⟨7186895, by rfl⟩ : syracuseStep 9582527 = 14373791) B14373791
theorem B6388351 : Blo 2071435 6388351 := bstep (se 1 (by rfl) ⟨4791263, by rfl⟩ : syracuseStep 6388351 = 9582527) B9582527
theorem B34071205 : Blo 2071435 34071205 := bstep (se 4 (by rfl) ⟨3194175, by rfl⟩ : syracuseStep 34071205 = 6388351) B6388351
theorem B45428273 : Blo 2071435 45428273 := bstep (se 2 (by rfl) ⟨17035602, by rfl⟩ : syracuseStep 45428273 = 34071205) B34071205
theorem B30285515 : Blo 2071435 30285515 := bstep (se 1 (by rfl) ⟨22714136, by rfl⟩ : syracuseStep 30285515 = 45428273) B45428273
theorem B20190343 : Blo 2071435 20190343 := bstep (se 1 (by rfl) ⟨15142757, by rfl⟩ : syracuseStep 20190343 = 30285515) B30285515
theorem B26920457 : Blo 2071435 26920457 := bstep (se 2 (by rfl) ⟨10095171, by rfl⟩ : syracuseStep 26920457 = 20190343) B20190343
theorem B17946971 : Blo 2071435 17946971 := bstep (se 1 (by rfl) ⟨13460228, by rfl⟩ : syracuseStep 17946971 = 26920457) B26920457
theorem B11964647 : Blo 2071435 11964647 := bstep (se 1 (by rfl) ⟨8973485, by rfl⟩ : syracuseStep 11964647 = 17946971) B17946971
theorem B7976431 : Blo 2071435 7976431 := bstep (se 1 (by rfl) ⟨5982323, by rfl⟩ : syracuseStep 7976431 = 11964647) B11964647
theorem B10635241 : Blo 2071435 10635241 := bstep (se 2 (by rfl) ⟨3988215, by rfl⟩ : syracuseStep 10635241 = 7976431) B7976431
theorem B14180321 : Blo 2071435 14180321 := bstep (se 2 (by rfl) ⟨5317620, by rfl⟩ : syracuseStep 14180321 = 10635241) B10635241
theorem B9453547 : Blo 2071435 9453547 := bstep (se 1 (by rfl) ⟨7090160, by rfl⟩ : syracuseStep 9453547 = 14180321) B14180321
theorem B12604729 : Blo 2071435 12604729 := bstep (se 2 (by rfl) ⟨4726773, by rfl⟩ : syracuseStep 12604729 = 9453547) B9453547
theorem B16806305 : Blo 2071435 16806305 := bstep (se 2 (by rfl) ⟨6302364, by rfl⟩ : syracuseStep 16806305 = 12604729) B12604729
theorem B11204203 : Blo 2071435 11204203 := bstep (se 1 (by rfl) ⟨8403152, by rfl⟩ : syracuseStep 11204203 = 16806305) B16806305
theorem B14938937 : Blo 2071435 14938937 := bstep (se 2 (by rfl) ⟨5602101, by rfl⟩ : syracuseStep 14938937 = 11204203) B11204203
theorem B9959291 : Blo 2071435 9959291 := bstep (se 1 (by rfl) ⟨7469468, by rfl⟩ : syracuseStep 9959291 = 14938937) B14938937
theorem B6639527 : Blo 2071435 6639527 := bstep (se 1 (by rfl) ⟨4979645, by rfl⟩ : syracuseStep 6639527 = 9959291) B9959291
theorem B17705405 : Blo 2071435 17705405 := bstep (se 3 (by rfl) ⟨3319763, by rfl⟩ : syracuseStep 17705405 = 6639527) B6639527
theorem B11803603 : Blo 2071435 11803603 := bstep (se 1 (by rfl) ⟨8852702, by rfl⟩ : syracuseStep 11803603 = 17705405) B17705405
theorem B15738137 : Blo 2071435 15738137 := bstep (se 2 (by rfl) ⟨5901801, by rfl⟩ : syracuseStep 15738137 = 11803603) B11803603
theorem B10492091 : Blo 2071435 10492091 := bstep (se 1 (by rfl) ⟨7869068, by rfl⟩ : syracuseStep 10492091 = 15738137) B15738137
theorem B6994727 : Blo 2071435 6994727 := bstep (se 1 (by rfl) ⟨5246045, by rfl⟩ : syracuseStep 6994727 = 10492091) B10492091
theorem B4663151 : Blo 2071435 4663151 := bstep (se 1 (by rfl) ⟨3497363, by rfl⟩ : syracuseStep 4663151 = 6994727) B6994727
theorem B3108767 : Blo 2071435 3108767 := bstep (se 1 (by rfl) ⟨2331575, by rfl⟩ : syracuseStep 3108767 = 4663151) B4663151
theorem B2072511 : Blo 2071435 2072511 := bstep (se 1 (by rfl) ⟨1554383, by rfl⟩ : syracuseStep 2072511 = 3108767) B3108767
theorem B3108773 : Blo 2071435 3108773 := bbase (se 4 (by rfl) ⟨291447, by rfl⟩ : syracuseStep 3108773 = 582895) (by norm_num)
theorem B2072515 : Blo 2071435 2072515 := bstep (se 1 (by rfl) ⟨1554386, by rfl⟩ : syracuseStep 2072515 = 3108773) B3108773
theorem B2623033 : Blo 2071435 2623033 := bbase (se 2 (by rfl) ⟨983637, by rfl⟩ : syracuseStep 2623033 = 1967275) (by norm_num)
theorem B3497377 : Blo 2071435 3497377 := bstep (se 2 (by rfl) ⟨1311516, by rfl⟩ : syracuseStep 3497377 = 2623033) B2623033
theorem B4663169 : Blo 2071435 4663169 := bstep (se 2 (by rfl) ⟨1748688, by rfl⟩ : syracuseStep 4663169 = 3497377) B3497377
theorem B3108779 : Blo 2071435 3108779 := bstep (se 1 (by rfl) ⟨2331584, by rfl⟩ : syracuseStep 3108779 = 4663169) B4663169
theorem B2072519 : Blo 2071435 2072519 := bstep (se 1 (by rfl) ⟨1554389, by rfl⟩ : syracuseStep 2072519 = 3108779) B3108779
theorem B2331589 : Blo 2071435 2331589 := bbase (se 4 (by rfl) ⟨218586, by rfl⟩ : syracuseStep 2331589 = 437173) (by norm_num)
theorem B3108785 : Blo 2071435 3108785 := bstep (se 2 (by rfl) ⟨1165794, by rfl⟩ : syracuseStep 3108785 = 2331589) B2331589
theorem B2072523 : Blo 2071435 2072523 := bstep (se 1 (by rfl) ⟨1554392, by rfl⟩ : syracuseStep 2072523 = 3108785) B3108785
theorem B3934565 : Blo 2071435 3934565 := bbase (se 4 (by rfl) ⟨368865, by rfl⟩ : syracuseStep 3934565 = 737731) (by norm_num)
theorem B2623043 : Blo 2071435 2623043 := bstep (se 1 (by rfl) ⟨1967282, by rfl⟩ : syracuseStep 2623043 = 3934565) B3934565
theorem B6994781 : Blo 2071435 6994781 := bstep (se 3 (by rfl) ⟨1311521, by rfl⟩ : syracuseStep 6994781 = 2623043) B2623043
theorem B4663187 : Blo 2071435 4663187 := bstep (se 1 (by rfl) ⟨3497390, by rfl⟩ : syracuseStep 4663187 = 6994781) B6994781
theorem B3108791 : Blo 2071435 3108791 := bstep (se 1 (by rfl) ⟨2331593, by rfl⟩ : syracuseStep 3108791 = 4663187) B4663187
theorem B2072527 : Blo 2071435 2072527 := bstep (se 1 (by rfl) ⟨1554395, by rfl⟩ : syracuseStep 2072527 = 3108791) B3108791
theorem B3108797 : Blo 2071435 3108797 := bbase (se 3 (by rfl) ⟨582899, by rfl⟩ : syracuseStep 3108797 = 1165799) (by norm_num)
theorem B2072531 : Blo 2071435 2072531 := bstep (se 1 (by rfl) ⟨1554398, by rfl⟩ : syracuseStep 2072531 = 3108797) B3108797
theorem B4663205 : Blo 2071435 4663205 := bbase (se 4 (by rfl) ⟨437175, by rfl⟩ : syracuseStep 4663205 = 874351) (by norm_num)
theorem B3108803 : Blo 2071435 3108803 := bstep (se 1 (by rfl) ⟨2331602, by rfl⟩ : syracuseStep 3108803 = 4663205) B4663205
theorem B2072535 : Blo 2071435 2072535 := bstep (se 1 (by rfl) ⟨1554401, by rfl⟩ : syracuseStep 2072535 = 3108803) B3108803
theorem B5246117 : Blo 2071435 5246117 := bbase (se 4 (by rfl) ⟨491823, by rfl⟩ : syracuseStep 5246117 = 983647) (by norm_num)
theorem B3497411 : Blo 2071435 3497411 := bstep (se 1 (by rfl) ⟨2623058, by rfl⟩ : syracuseStep 3497411 = 5246117) B5246117
theorem B2331607 : Blo 2071435 2331607 := bstep (se 1 (by rfl) ⟨1748705, by rfl⟩ : syracuseStep 2331607 = 3497411) B3497411
theorem B3108809 : Blo 2071435 3108809 := bstep (se 2 (by rfl) ⟨1165803, by rfl⟩ : syracuseStep 3108809 = 2331607) B2331607
theorem B2072539 : Blo 2071435 2072539 := bstep (se 1 (by rfl) ⟨1554404, by rfl⟩ : syracuseStep 2072539 = 3108809) B3108809
theorem B5901893 : Blo 2071435 5901893 := bbase (se 4 (by rfl) ⟨553302, by rfl⟩ : syracuseStep 5901893 = 1106605) (by norm_num)
theorem B3934595 : Blo 2071435 3934595 := bstep (se 1 (by rfl) ⟨2950946, by rfl⟩ : syracuseStep 3934595 = 5901893) B5901893
theorem B10492253 : Blo 2071435 10492253 := bstep (se 3 (by rfl) ⟨1967297, by rfl⟩ : syracuseStep 10492253 = 3934595) B3934595
theorem B6994835 : Blo 2071435 6994835 := bstep (se 1 (by rfl) ⟨5246126, by rfl⟩ : syracuseStep 6994835 = 10492253) B10492253
theorem B4663223 : Blo 2071435 4663223 := bstep (se 1 (by rfl) ⟨3497417, by rfl⟩ : syracuseStep 4663223 = 6994835) B6994835
theorem B3108815 : Blo 2071435 3108815 := bstep (se 1 (by rfl) ⟨2331611, by rfl⟩ : syracuseStep 3108815 = 4663223) B4663223
theorem B2072543 : Blo 2071435 2072543 := bstep (se 1 (by rfl) ⟨1554407, by rfl⟩ : syracuseStep 2072543 = 3108815) B3108815
theorem B3108821 : Blo 2071435 3108821 := bbase (se 7 (by rfl) ⟨36431, by rfl⟩ : syracuseStep 3108821 = 72863) (by norm_num)
theorem B2072547 : Blo 2071435 2072547 := bstep (se 1 (by rfl) ⟨1554410, by rfl⟩ : syracuseStep 2072547 = 3108821) B3108821
theorem B7869221 : Blo 2071435 7869221 := bbase (se 4 (by rfl) ⟨737739, by rfl⟩ : syracuseStep 7869221 = 1475479) (by norm_num)
theorem B5246147 : Blo 2071435 5246147 := bstep (se 1 (by rfl) ⟨3934610, by rfl⟩ : syracuseStep 5246147 = 7869221) B7869221
theorem B3497431 : Blo 2071435 3497431 := bstep (se 1 (by rfl) ⟨2623073, by rfl⟩ : syracuseStep 3497431 = 5246147) B5246147
theorem B4663241 : Blo 2071435 4663241 := bstep (se 2 (by rfl) ⟨1748715, by rfl⟩ : syracuseStep 4663241 = 3497431) B3497431
theorem B3108827 : Blo 2071435 3108827 := bstep (se 1 (by rfl) ⟨2331620, by rfl⟩ : syracuseStep 3108827 = 4663241) B4663241
theorem B2072551 : Blo 2071435 2072551 := bstep (se 1 (by rfl) ⟨1554413, by rfl⟩ : syracuseStep 2072551 = 3108827) B3108827
theorem B2331625 : Blo 2071435 2331625 := bbase (se 2 (by rfl) ⟨874359, by rfl⟩ : syracuseStep 2331625 = 1748719) (by norm_num)
theorem B3108833 : Blo 2071435 3108833 := bstep (se 2 (by rfl) ⟨1165812, by rfl⟩ : syracuseStep 3108833 = 2331625) B2331625
theorem B2072555 : Blo 2071435 2072555 := bstep (se 1 (by rfl) ⟨1554416, by rfl⟩ : syracuseStep 2072555 = 3108833) B3108833
theorem B2489881 : Blo 2071435 2489881 := bbase (se 2 (by rfl) ⟨933705, by rfl⟩ : syracuseStep 2489881 = 1867411) (by norm_num)
theorem B3319841 : Blo 2071435 3319841 := bstep (se 2 (by rfl) ⟨1244940, by rfl⟩ : syracuseStep 3319841 = 2489881) B2489881
theorem B2213227 : Blo 2071435 2213227 := bstep (se 1 (by rfl) ⟨1659920, by rfl⟩ : syracuseStep 2213227 = 3319841) B3319841
theorem B11803877 : Blo 2071435 11803877 := bstep (se 4 (by rfl) ⟨1106613, by rfl⟩ : syracuseStep 11803877 = 2213227) B2213227
theorem B7869251 : Blo 2071435 7869251 := bstep (se 1 (by rfl) ⟨5901938, by rfl⟩ : syracuseStep 7869251 = 11803877) B11803877
theorem B5246167 : Blo 2071435 5246167 := bstep (se 1 (by rfl) ⟨3934625, by rfl⟩ : syracuseStep 5246167 = 7869251) B7869251
theorem B6994889 : Blo 2071435 6994889 := bstep (se 2 (by rfl) ⟨2623083, by rfl⟩ : syracuseStep 6994889 = 5246167) B5246167
theorem B4663259 : Blo 2071435 4663259 := bstep (se 1 (by rfl) ⟨3497444, by rfl⟩ : syracuseStep 4663259 = 6994889) B6994889
theorem B3108839 : Blo 2071435 3108839 := bstep (se 1 (by rfl) ⟨2331629, by rfl⟩ : syracuseStep 3108839 = 4663259) B4663259
theorem B2072559 : Blo 2071435 2072559 := bstep (se 1 (by rfl) ⟨1554419, by rfl⟩ : syracuseStep 2072559 = 3108839) B3108839
theorem B3108845 : Blo 2071435 3108845 := bbase (se 3 (by rfl) ⟨582908, by rfl⟩ : syracuseStep 3108845 = 1165817) (by norm_num)
theorem B2072563 : Blo 2071435 2072563 := bstep (se 1 (by rfl) ⟨1554422, by rfl⟩ : syracuseStep 2072563 = 3108845) B3108845
theorem B4663277 : Blo 2071435 4663277 := bbase (se 3 (by rfl) ⟨874364, by rfl⟩ : syracuseStep 4663277 = 1748729) (by norm_num)
theorem B3108851 : Blo 2071435 3108851 := bstep (se 1 (by rfl) ⟨2331638, by rfl⟩ : syracuseStep 3108851 = 4663277) B4663277
theorem B2072567 : Blo 2071435 2072567 := bstep (se 1 (by rfl) ⟨1554425, by rfl⟩ : syracuseStep 2072567 = 3108851) B3108851
theorem B3319861 : Blo 2071435 3319861 := bbase (se 5 (by rfl) ⟨155618, by rfl⟩ : syracuseStep 3319861 = 311237) (by norm_num)
theorem B4426481 : Blo 2071435 4426481 := bstep (se 2 (by rfl) ⟨1659930, by rfl⟩ : syracuseStep 4426481 = 3319861) B3319861
theorem B2950987 : Blo 2071435 2950987 := bstep (se 1 (by rfl) ⟨2213240, by rfl⟩ : syracuseStep 2950987 = 4426481) B4426481
theorem B3934649 : Blo 2071435 3934649 := bstep (se 2 (by rfl) ⟨1475493, by rfl⟩ : syracuseStep 3934649 = 2950987) B2950987
theorem B2623099 : Blo 2071435 2623099 := bstep (se 1 (by rfl) ⟨1967324, by rfl⟩ : syracuseStep 2623099 = 3934649) B3934649
theorem B3497465 : Blo 2071435 3497465 := bstep (se 2 (by rfl) ⟨1311549, by rfl⟩ : syracuseStep 3497465 = 2623099) B2623099
theorem B2331643 : Blo 2071435 2331643 := bstep (se 1 (by rfl) ⟨1748732, by rfl⟩ : syracuseStep 2331643 = 3497465) B3497465
theorem B3108857 : Blo 2071435 3108857 := bstep (se 2 (by rfl) ⟨1165821, by rfl⟩ : syracuseStep 3108857 = 2331643) B2331643
theorem B2072571 : Blo 2071435 2072571 := bstep (se 1 (by rfl) ⟨1554428, by rfl⟩ : syracuseStep 2072571 = 3108857) B3108857
theorem B3996677 : Blo 2071435 3996677 := bbase (se 4 (by rfl) ⟨374688, by rfl⟩ : syracuseStep 3996677 = 749377) (by norm_num)
theorem B2664451 : Blo 2071435 2664451 := bstep (se 1 (by rfl) ⟨1998338, by rfl⟩ : syracuseStep 2664451 = 3996677) B3996677
theorem B3552601 : Blo 2071435 3552601 := bstep (se 2 (by rfl) ⟨1332225, by rfl⟩ : syracuseStep 3552601 = 2664451) B2664451
theorem B4736801 : Blo 2071435 4736801 := bstep (se 2 (by rfl) ⟨1776300, by rfl⟩ : syracuseStep 4736801 = 3552601) B3552601
theorem B3157867 : Blo 2071435 3157867 := bstep (se 1 (by rfl) ⟨2368400, by rfl⟩ : syracuseStep 3157867 = 4736801) B4736801
theorem B4210489 : Blo 2071435 4210489 := bstep (se 2 (by rfl) ⟨1578933, by rfl⟩ : syracuseStep 4210489 = 3157867) B3157867
theorem B22455941 : Blo 2071435 22455941 := bstep (se 4 (by rfl) ⟨2105244, by rfl⟩ : syracuseStep 22455941 = 4210489) B4210489
theorem B59882509 : Blo 2071435 59882509 := bstep (se 3 (by rfl) ⟨11227970, by rfl⟩ : syracuseStep 59882509 = 22455941) B22455941
theorem B319373381 : Blo 2071435 319373381 := bstep (se 4 (by rfl) ⟨29941254, by rfl⟩ : syracuseStep 319373381 = 59882509) B59882509
theorem B212915587 : Blo 2071435 212915587 := bstep (se 1 (by rfl) ⟨159686690, by rfl⟩ : syracuseStep 212915587 = 319373381) B319373381
theorem B283887449 : Blo 2071435 283887449 := bstep (se 2 (by rfl) ⟨106457793, by rfl⟩ : syracuseStep 283887449 = 212915587) B212915587
theorem B189258299 : Blo 2071435 189258299 := bstep (se 1 (by rfl) ⟨141943724, by rfl⟩ : syracuseStep 189258299 = 283887449) B283887449
theorem B126172199 : Blo 2071435 126172199 := bstep (se 1 (by rfl) ⟨94629149, by rfl⟩ : syracuseStep 126172199 = 189258299) B189258299
theorem B336459197 : Blo 2071435 336459197 := bstep (se 3 (by rfl) ⟨63086099, by rfl⟩ : syracuseStep 336459197 = 126172199) B126172199
theorem B224306131 : Blo 2071435 224306131 := bstep (se 1 (by rfl) ⟨168229598, by rfl⟩ : syracuseStep 224306131 = 336459197) B336459197
theorem B299074841 : Blo 2071435 299074841 := bstep (se 2 (by rfl) ⟨112153065, by rfl⟩ : syracuseStep 299074841 = 224306131) B224306131
theorem B199383227 : Blo 2071435 199383227 := bstep (se 1 (by rfl) ⟨149537420, by rfl⟩ : syracuseStep 199383227 = 299074841) B299074841
theorem B132922151 : Blo 2071435 132922151 := bstep (se 1 (by rfl) ⟨99691613, by rfl⟩ : syracuseStep 132922151 = 199383227) B199383227
theorem B88614767 : Blo 2071435 88614767 := bstep (se 1 (by rfl) ⟨66461075, by rfl⟩ : syracuseStep 88614767 = 132922151) B132922151
theorem B236306045 : Blo 2071435 236306045 := bstep (se 3 (by rfl) ⟨44307383, by rfl⟩ : syracuseStep 236306045 = 88614767) B88614767
theorem B630149453 : Blo 2071435 630149453 := bstep (se 3 (by rfl) ⟨118153022, by rfl⟩ : syracuseStep 630149453 = 236306045) B236306045
theorem B420099635 : Blo 2071435 420099635 := bstep (se 1 (by rfl) ⟨315074726, by rfl⟩ : syracuseStep 420099635 = 630149453) B630149453
theorem B1120265693 : Blo 2071435 1120265693 := bstep (se 3 (by rfl) ⟨210049817, by rfl⟩ : syracuseStep 1120265693 = 420099635) B420099635
theorem B746843795 : Blo 2071435 746843795 := bstep (se 1 (by rfl) ⟨560132846, by rfl⟩ : syracuseStep 746843795 = 1120265693) B1120265693
theorem B497895863 : Blo 2071435 497895863 := bstep (se 1 (by rfl) ⟨373421897, by rfl⟩ : syracuseStep 497895863 = 746843795) B746843795
theorem B1327722301 : Blo 2071435 1327722301 := bstep (se 3 (by rfl) ⟨248947931, by rfl⟩ : syracuseStep 1327722301 = 497895863) B497895863
theorem B1770296401 : Blo 2071435 1770296401 := bstep (se 2 (by rfl) ⟨663861150, by rfl⟩ : syracuseStep 1770296401 = 1327722301) B1327722301
theorem B2360395201 : Blo 2071435 2360395201 := bstep (se 2 (by rfl) ⟨885148200, by rfl⟩ : syracuseStep 2360395201 = 1770296401) B1770296401
theorem B3147193601 : Blo 2071435 3147193601 := bstep (se 2 (by rfl) ⟨1180197600, by rfl⟩ : syracuseStep 3147193601 = 2360395201) B2360395201
theorem B2098129067 : Blo 2071435 2098129067 := bstep (se 1 (by rfl) ⟨1573596800, by rfl⟩ : syracuseStep 2098129067 = 3147193601) B3147193601
theorem B1398752711 : Blo 2071435 1398752711 := bstep (se 1 (by rfl) ⟨1049064533, by rfl⟩ : syracuseStep 1398752711 = 2098129067) B2098129067
theorem B932501807 : Blo 2071435 932501807 := bstep (se 1 (by rfl) ⟨699376355, by rfl⟩ : syracuseStep 932501807 = 1398752711) B1398752711
theorem B621667871 : Blo 2071435 621667871 := bstep (se 1 (by rfl) ⟨466250903, by rfl⟩ : syracuseStep 621667871 = 932501807) B932501807
theorem B414445247 : Blo 2071435 414445247 := bstep (se 1 (by rfl) ⟨310833935, by rfl⟩ : syracuseStep 414445247 = 621667871) B621667871
theorem B276296831 : Blo 2071435 276296831 := bstep (se 1 (by rfl) ⟨207222623, by rfl⟩ : syracuseStep 276296831 = 414445247) B414445247
theorem B184197887 : Blo 2071435 184197887 := bstep (se 1 (by rfl) ⟨138148415, by rfl⟩ : syracuseStep 184197887 = 276296831) B276296831
theorem B122798591 : Blo 2071435 122798591 := bstep (se 1 (by rfl) ⟨92098943, by rfl⟩ : syracuseStep 122798591 = 184197887) B184197887
theorem B81865727 : Blo 2071435 81865727 := bstep (se 1 (by rfl) ⟨61399295, by rfl⟩ : syracuseStep 81865727 = 122798591) B122798591
theorem B54577151 : Blo 2071435 54577151 := bstep (se 1 (by rfl) ⟨40932863, by rfl⟩ : syracuseStep 54577151 = 81865727) B81865727
theorem B36384767 : Blo 2071435 36384767 := bstep (se 1 (by rfl) ⟨27288575, by rfl⟩ : syracuseStep 36384767 = 54577151) B54577151
theorem B24256511 : Blo 2071435 24256511 := bstep (se 1 (by rfl) ⟨18192383, by rfl⟩ : syracuseStep 24256511 = 36384767) B36384767
theorem B16171007 : Blo 2071435 16171007 := bstep (se 1 (by rfl) ⟨12128255, by rfl⟩ : syracuseStep 16171007 = 24256511) B24256511
theorem B172490741 : Blo 2071435 172490741 := bstep (se 5 (by rfl) ⟨8085503, by rfl⟩ : syracuseStep 172490741 = 16171007) B16171007
theorem B114993827 : Blo 2071435 114993827 := bstep (se 1 (by rfl) ⟨86245370, by rfl⟩ : syracuseStep 114993827 = 172490741) B172490741
theorem B76662551 : Blo 2071435 76662551 := bstep (se 1 (by rfl) ⟨57496913, by rfl⟩ : syracuseStep 76662551 = 114993827) B114993827
theorem B204433469 : Blo 2071435 204433469 := bstep (se 3 (by rfl) ⟨38331275, by rfl⟩ : syracuseStep 204433469 = 76662551) B76662551
theorem B136288979 : Blo 2071435 136288979 := bstep (se 1 (by rfl) ⟨102216734, by rfl⟩ : syracuseStep 136288979 = 204433469) B204433469
theorem B90859319 : Blo 2071435 90859319 := bstep (se 1 (by rfl) ⟨68144489, by rfl⟩ : syracuseStep 90859319 = 136288979) B136288979
theorem B60572879 : Blo 2071435 60572879 := bstep (se 1 (by rfl) ⟨45429659, by rfl⟩ : syracuseStep 60572879 = 90859319) B90859319
theorem B40381919 : Blo 2071435 40381919 := bstep (se 1 (by rfl) ⟨30286439, by rfl⟩ : syracuseStep 40381919 = 60572879) B60572879
theorem B26921279 : Blo 2071435 26921279 := bstep (se 1 (by rfl) ⟨20190959, by rfl⟩ : syracuseStep 26921279 = 40381919) B40381919
theorem B71790077 : Blo 2071435 71790077 := bstep (se 3 (by rfl) ⟨13460639, by rfl⟩ : syracuseStep 71790077 = 26921279) B26921279
theorem B191440205 : Blo 2071435 191440205 := bstep (se 3 (by rfl) ⟨35895038, by rfl⟩ : syracuseStep 191440205 = 71790077) B71790077
theorem B127626803 : Blo 2071435 127626803 := bstep (se 1 (by rfl) ⟨95720102, by rfl⟩ : syracuseStep 127626803 = 191440205) B191440205
theorem B85084535 : Blo 2071435 85084535 := bstep (se 1 (by rfl) ⟨63813401, by rfl⟩ : syracuseStep 85084535 = 127626803) B127626803
theorem B56723023 : Blo 2071435 56723023 := bstep (se 1 (by rfl) ⟨42542267, by rfl⟩ : syracuseStep 56723023 = 85084535) B85084535
theorem B302522789 : Blo 2071435 302522789 := bstep (se 4 (by rfl) ⟨28361511, by rfl⟩ : syracuseStep 302522789 = 56723023) B56723023
theorem B201681859 : Blo 2071435 201681859 := bstep (se 1 (by rfl) ⟨151261394, by rfl⟩ : syracuseStep 201681859 = 302522789) B302522789
theorem B268909145 : Blo 2071435 268909145 := bstep (se 2 (by rfl) ⟨100840929, by rfl⟩ : syracuseStep 268909145 = 201681859) B201681859
theorem B179272763 : Blo 2071435 179272763 := bstep (se 1 (by rfl) ⟨134454572, by rfl⟩ : syracuseStep 179272763 = 268909145) B268909145
theorem B119515175 : Blo 2071435 119515175 := bstep (se 1 (by rfl) ⟨89636381, by rfl⟩ : syracuseStep 119515175 = 179272763) B179272763
theorem B79676783 : Blo 2071435 79676783 := bstep (se 1 (by rfl) ⟨59757587, by rfl⟩ : syracuseStep 79676783 = 119515175) B119515175
theorem B53117855 : Blo 2071435 53117855 := bstep (se 1 (by rfl) ⟨39838391, by rfl⟩ : syracuseStep 53117855 = 79676783) B79676783
theorem B35411903 : Blo 2071435 35411903 := bstep (se 1 (by rfl) ⟨26558927, by rfl⟩ : syracuseStep 35411903 = 53117855) B53117855
theorem B23607935 : Blo 2071435 23607935 := bstep (se 1 (by rfl) ⟨17705951, by rfl⟩ : syracuseStep 23607935 = 35411903) B35411903
theorem B15738623 : Blo 2071435 15738623 := bstep (se 1 (by rfl) ⟨11803967, by rfl⟩ : syracuseStep 15738623 = 23607935) B23607935
theorem B10492415 : Blo 2071435 10492415 := bstep (se 1 (by rfl) ⟨7869311, by rfl⟩ : syracuseStep 10492415 = 15738623) B15738623
theorem B6994943 : Blo 2071435 6994943 := bstep (se 1 (by rfl) ⟨5246207, by rfl⟩ : syracuseStep 6994943 = 10492415) B10492415
theorem B4663295 : Blo 2071435 4663295 := bstep (se 1 (by rfl) ⟨3497471, by rfl⟩ : syracuseStep 4663295 = 6994943) B6994943
theorem B3108863 : Blo 2071435 3108863 := bstep (se 1 (by rfl) ⟨2331647, by rfl⟩ : syracuseStep 3108863 = 4663295) B4663295
theorem B2072575 : Blo 2071435 2072575 := bstep (se 1 (by rfl) ⟨1554431, by rfl⟩ : syracuseStep 2072575 = 3108863) B3108863
theorem B3108869 : Blo 2071435 3108869 := bbase (se 4 (by rfl) ⟨291456, by rfl⟩ : syracuseStep 3108869 = 582913) (by norm_num)
theorem B2072579 : Blo 2071435 2072579 := bstep (se 1 (by rfl) ⟨1554434, by rfl⟩ : syracuseStep 2072579 = 3108869) B3108869
theorem B3497485 : Blo 2071435 3497485 := bbase (se 3 (by rfl) ⟨655778, by rfl⟩ : syracuseStep 3497485 = 1311557) (by norm_num)
theorem B4663313 : Blo 2071435 4663313 := bstep (se 2 (by rfl) ⟨1748742, by rfl⟩ : syracuseStep 4663313 = 3497485) B3497485
theorem B3108875 : Blo 2071435 3108875 := bstep (se 1 (by rfl) ⟨2331656, by rfl⟩ : syracuseStep 3108875 = 4663313) B4663313
theorem B2072583 : Blo 2071435 2072583 := bstep (se 1 (by rfl) ⟨1554437, by rfl⟩ : syracuseStep 2072583 = 3108875) B3108875
theorem B2331661 : Blo 2071435 2331661 := bbase (se 3 (by rfl) ⟨437186, by rfl⟩ : syracuseStep 2331661 = 874373) (by norm_num)
theorem B3108881 : Blo 2071435 3108881 := bstep (se 2 (by rfl) ⟨1165830, by rfl⟩ : syracuseStep 3108881 = 2331661) B2331661
theorem B2072587 : Blo 2071435 2072587 := bstep (se 1 (by rfl) ⟨1554440, by rfl⟩ : syracuseStep 2072587 = 3108881) B3108881
theorem B6994997 : Blo 2071435 6994997 := bbase (se 5 (by rfl) ⟨327890, by rfl⟩ : syracuseStep 6994997 = 655781) (by norm_num)
theorem B4663331 : Blo 2071435 4663331 := bstep (se 1 (by rfl) ⟨3497498, by rfl⟩ : syracuseStep 4663331 = 6994997) B6994997
theorem B3108887 : Blo 2071435 3108887 := bstep (se 1 (by rfl) ⟨2331665, by rfl⟩ : syracuseStep 3108887 = 4663331) B4663331
theorem B2072591 : Blo 2071435 2072591 := bstep (se 1 (by rfl) ⟨1554443, by rfl⟩ : syracuseStep 2072591 = 3108887) B3108887
theorem B3108893 : Blo 2071435 3108893 := bbase (se 3 (by rfl) ⟨582917, by rfl⟩ : syracuseStep 3108893 = 1165835) (by norm_num)
theorem B2072595 : Blo 2071435 2072595 := bstep (se 1 (by rfl) ⟨1554446, by rfl⟩ : syracuseStep 2072595 = 3108893) B3108893
theorem B4663349 : Blo 2071435 4663349 := bbase (se 5 (by rfl) ⟨218594, by rfl⟩ : syracuseStep 4663349 = 437189) (by norm_num)
theorem B3108899 : Blo 2071435 3108899 := bstep (se 1 (by rfl) ⟨2331674, by rfl⟩ : syracuseStep 3108899 = 4663349) B4663349
theorem B2072599 : Blo 2071435 2072599 := bstep (se 1 (by rfl) ⟨1554449, by rfl⟩ : syracuseStep 2072599 = 3108899) B3108899
theorem B6822245 : Blo 2071435 6822245 := bbase (se 4 (by rfl) ⟨639585, by rfl⟩ : syracuseStep 6822245 = 1279171) (by norm_num)
theorem B4548163 : Blo 2071435 4548163 := bstep (se 1 (by rfl) ⟨3411122, by rfl⟩ : syracuseStep 4548163 = 6822245) B6822245
theorem B6064217 : Blo 2071435 6064217 := bstep (se 2 (by rfl) ⟨2274081, by rfl⟩ : syracuseStep 6064217 = 4548163) B4548163
theorem B4042811 : Blo 2071435 4042811 := bstep (se 1 (by rfl) ⟨3032108, by rfl⟩ : syracuseStep 4042811 = 6064217) B6064217
theorem B2695207 : Blo 2071435 2695207 := bstep (se 1 (by rfl) ⟨2021405, by rfl⟩ : syracuseStep 2695207 = 4042811) B4042811
theorem B3593609 : Blo 2071435 3593609 := bstep (se 2 (by rfl) ⟨1347603, by rfl⟩ : syracuseStep 3593609 = 2695207) B2695207
theorem B2395739 : Blo 2071435 2395739 := bstep (se 1 (by rfl) ⟨1796804, by rfl⟩ : syracuseStep 2395739 = 3593609) B3593609
theorem B6388637 : Blo 2071435 6388637 := bstep (se 3 (by rfl) ⟨1197869, by rfl⟩ : syracuseStep 6388637 = 2395739) B2395739
theorem B17036365 : Blo 2071435 17036365 := bstep (se 3 (by rfl) ⟨3194318, by rfl⟩ : syracuseStep 17036365 = 6388637) B6388637
theorem B22715153 : Blo 2071435 22715153 := bstep (se 2 (by rfl) ⟨8518182, by rfl⟩ : syracuseStep 22715153 = 17036365) B17036365
theorem B15143435 : Blo 2071435 15143435 := bstep (se 1 (by rfl) ⟨11357576, by rfl⟩ : syracuseStep 15143435 = 22715153) B22715153
theorem B10095623 : Blo 2071435 10095623 := bstep (se 1 (by rfl) ⟨7571717, by rfl⟩ : syracuseStep 10095623 = 15143435) B15143435
theorem B6730415 : Blo 2071435 6730415 := bstep (se 1 (by rfl) ⟨5047811, by rfl⟩ : syracuseStep 6730415 = 10095623) B10095623
theorem B4486943 : Blo 2071435 4486943 := bstep (se 1 (by rfl) ⟨3365207, by rfl⟩ : syracuseStep 4486943 = 6730415) B6730415
theorem B2991295 : Blo 2071435 2991295 := bstep (se 1 (by rfl) ⟨2243471, by rfl⟩ : syracuseStep 2991295 = 4486943) B4486943
theorem B15953573 : Blo 2071435 15953573 := bstep (se 4 (by rfl) ⟨1495647, by rfl⟩ : syracuseStep 15953573 = 2991295) B2991295
theorem B10635715 : Blo 2071435 10635715 := bstep (se 1 (by rfl) ⟨7976786, by rfl⟩ : syracuseStep 10635715 = 15953573) B15953573
theorem B14180953 : Blo 2071435 14180953 := bstep (se 2 (by rfl) ⟨5317857, by rfl⟩ : syracuseStep 14180953 = 10635715) B10635715
theorem B18907937 : Blo 2071435 18907937 := bstep (se 2 (by rfl) ⟨7090476, by rfl⟩ : syracuseStep 18907937 = 14180953) B14180953
theorem B12605291 : Blo 2071435 12605291 := bstep (se 1 (by rfl) ⟨9453968, by rfl⟩ : syracuseStep 12605291 = 18907937) B18907937
theorem B8403527 : Blo 2071435 8403527 := bstep (se 1 (by rfl) ⟨6302645, by rfl⟩ : syracuseStep 8403527 = 12605291) B12605291
theorem B22409405 : Blo 2071435 22409405 := bstep (se 3 (by rfl) ⟨4201763, by rfl⟩ : syracuseStep 22409405 = 8403527) B8403527
theorem B14939603 : Blo 2071435 14939603 := bstep (se 1 (by rfl) ⟨11204702, by rfl⟩ : syracuseStep 14939603 = 22409405) B22409405
theorem B9959735 : Blo 2071435 9959735 := bstep (se 1 (by rfl) ⟨7469801, by rfl⟩ : syracuseStep 9959735 = 14939603) B14939603
theorem B6639823 : Blo 2071435 6639823 := bstep (se 1 (by rfl) ⟨4979867, by rfl⟩ : syracuseStep 6639823 = 9959735) B9959735
theorem B8853097 : Blo 2071435 8853097 := bstep (se 2 (by rfl) ⟨3319911, by rfl⟩ : syracuseStep 8853097 = 6639823) B6639823
theorem B11804129 : Blo 2071435 11804129 := bstep (se 2 (by rfl) ⟨4426548, by rfl⟩ : syracuseStep 11804129 = 8853097) B8853097
theorem B7869419 : Blo 2071435 7869419 := bstep (se 1 (by rfl) ⟨5902064, by rfl⟩ : syracuseStep 7869419 = 11804129) B11804129
theorem B5246279 : Blo 2071435 5246279 := bstep (se 1 (by rfl) ⟨3934709, by rfl⟩ : syracuseStep 5246279 = 7869419) B7869419
theorem B3497519 : Blo 2071435 3497519 := bstep (se 1 (by rfl) ⟨2623139, by rfl⟩ : syracuseStep 3497519 = 5246279) B5246279
theorem B2331679 : Blo 2071435 2331679 := bstep (se 1 (by rfl) ⟨1748759, by rfl⟩ : syracuseStep 2331679 = 3497519) B3497519
theorem B3108905 : Blo 2071435 3108905 := bstep (se 2 (by rfl) ⟨1165839, by rfl⟩ : syracuseStep 3108905 = 2331679) B2331679
theorem B2072603 : Blo 2071435 2072603 := bstep (se 1 (by rfl) ⟨1554452, by rfl⟩ : syracuseStep 2072603 = 3108905) B3108905
theorem B3545245 : Blo 2071435 3545245 := bbase (se 3 (by rfl) ⟨664733, by rfl⟩ : syracuseStep 3545245 = 1329467) (by norm_num)
theorem B4726993 : Blo 2071435 4726993 := bstep (se 2 (by rfl) ⟨1772622, by rfl⟩ : syracuseStep 4726993 = 3545245) B3545245
theorem B6302657 : Blo 2071435 6302657 := bstep (se 2 (by rfl) ⟨2363496, by rfl⟩ : syracuseStep 6302657 = 4726993) B4726993
theorem B16807085 : Blo 2071435 16807085 := bstep (se 3 (by rfl) ⟨3151328, by rfl⟩ : syracuseStep 16807085 = 6302657) B6302657
theorem B11204723 : Blo 2071435 11204723 := bstep (se 1 (by rfl) ⟨8403542, by rfl⟩ : syracuseStep 11204723 = 16807085) B16807085
theorem B7469815 : Blo 2071435 7469815 := bstep (se 1 (by rfl) ⟨5602361, by rfl⟩ : syracuseStep 7469815 = 11204723) B11204723
theorem B9959753 : Blo 2071435 9959753 := bstep (se 2 (by rfl) ⟨3734907, by rfl⟩ : syracuseStep 9959753 = 7469815) B7469815
theorem B6639835 : Blo 2071435 6639835 := bstep (se 1 (by rfl) ⟨4979876, by rfl⟩ : syracuseStep 6639835 = 9959753) B9959753
theorem B8853113 : Blo 2071435 8853113 := bstep (se 2 (by rfl) ⟨3319917, by rfl⟩ : syracuseStep 8853113 = 6639835) B6639835
theorem B5902075 : Blo 2071435 5902075 := bstep (se 1 (by rfl) ⟨4426556, by rfl⟩ : syracuseStep 5902075 = 8853113) B8853113
theorem B7869433 : Blo 2071435 7869433 := bstep (se 2 (by rfl) ⟨2951037, by rfl⟩ : syracuseStep 7869433 = 5902075) B5902075
theorem B10492577 : Blo 2071435 10492577 := bstep (se 2 (by rfl) ⟨3934716, by rfl⟩ : syracuseStep 10492577 = 7869433) B7869433
theorem B6995051 : Blo 2071435 6995051 := bstep (se 1 (by rfl) ⟨5246288, by rfl⟩ : syracuseStep 6995051 = 10492577) B10492577
theorem B4663367 : Blo 2071435 4663367 := bstep (se 1 (by rfl) ⟨3497525, by rfl⟩ : syracuseStep 4663367 = 6995051) B6995051
theorem B3108911 : Blo 2071435 3108911 := bstep (se 1 (by rfl) ⟨2331683, by rfl⟩ : syracuseStep 3108911 = 4663367) B4663367
theorem B2072607 : Blo 2071435 2072607 := bstep (se 1 (by rfl) ⟨1554455, by rfl⟩ : syracuseStep 2072607 = 3108911) B3108911
theorem B3108917 : Blo 2071435 3108917 := bbase (se 5 (by rfl) ⟨145730, by rfl⟩ : syracuseStep 3108917 = 291461) (by norm_num)
theorem B2072611 : Blo 2071435 2072611 := bstep (se 1 (by rfl) ⟨1554458, by rfl⟩ : syracuseStep 2072611 = 3108917) B3108917
theorem B5246309 : Blo 2071435 5246309 := bbase (se 4 (by rfl) ⟨491841, by rfl⟩ : syracuseStep 5246309 = 983683) (by norm_num)
theorem B3497539 : Blo 2071435 3497539 := bstep (se 1 (by rfl) ⟨2623154, by rfl⟩ : syracuseStep 3497539 = 5246309) B5246309
theorem B4663385 : Blo 2071435 4663385 := bstep (se 2 (by rfl) ⟨1748769, by rfl⟩ : syracuseStep 4663385 = 3497539) B3497539
theorem B3108923 : Blo 2071435 3108923 := bstep (se 1 (by rfl) ⟨2331692, by rfl⟩ : syracuseStep 3108923 = 4663385) B4663385
theorem B2072615 : Blo 2071435 2072615 := bstep (se 1 (by rfl) ⟨1554461, by rfl⟩ : syracuseStep 2072615 = 3108923) B3108923
theorem B2331697 : Blo 2071435 2331697 := bbase (se 2 (by rfl) ⟨874386, by rfl⟩ : syracuseStep 2331697 = 1748773) (by norm_num)
theorem B3108929 : Blo 2071435 3108929 := bstep (se 2 (by rfl) ⟨1165848, by rfl⟩ : syracuseStep 3108929 = 2331697) B2331697
theorem B2072619 : Blo 2071435 2072619 := bstep (se 1 (by rfl) ⟨1554464, by rfl⟩ : syracuseStep 2072619 = 3108929) B3108929
theorem B22409621 : Blo 2071435 22409621 := bbase (se 6 (by rfl) ⟨525225, by rfl⟩ : syracuseStep 22409621 = 1050451) (by norm_num)
theorem B14939747 : Blo 2071435 14939747 := bstep (se 1 (by rfl) ⟨11204810, by rfl⟩ : syracuseStep 14939747 = 22409621) B22409621
theorem B9959831 : Blo 2071435 9959831 := bstep (se 1 (by rfl) ⟨7469873, by rfl⟩ : syracuseStep 9959831 = 14939747) B14939747
theorem B6639887 : Blo 2071435 6639887 := bstep (se 1 (by rfl) ⟨4979915, by rfl⟩ : syracuseStep 6639887 = 9959831) B9959831
theorem B4426591 : Blo 2071435 4426591 := bstep (se 1 (by rfl) ⟨3319943, by rfl⟩ : syracuseStep 4426591 = 6639887) B6639887
theorem B5902121 : Blo 2071435 5902121 := bstep (se 2 (by rfl) ⟨2213295, by rfl⟩ : syracuseStep 5902121 = 4426591) B4426591
theorem B3934747 : Blo 2071435 3934747 := bstep (se 1 (by rfl) ⟨2951060, by rfl⟩ : syracuseStep 3934747 = 5902121) B5902121
theorem B5246329 : Blo 2071435 5246329 := bstep (se 2 (by rfl) ⟨1967373, by rfl⟩ : syracuseStep 5246329 = 3934747) B3934747
theorem B6995105 : Blo 2071435 6995105 := bstep (se 2 (by rfl) ⟨2623164, by rfl⟩ : syracuseStep 6995105 = 5246329) B5246329
theorem B4663403 : Blo 2071435 4663403 := bstep (se 1 (by rfl) ⟨3497552, by rfl⟩ : syracuseStep 4663403 = 6995105) B6995105
theorem B3108935 : Blo 2071435 3108935 := bstep (se 1 (by rfl) ⟨2331701, by rfl⟩ : syracuseStep 3108935 = 4663403) B4663403
theorem B2072623 : Blo 2071435 2072623 := bstep (se 1 (by rfl) ⟨1554467, by rfl⟩ : syracuseStep 2072623 = 3108935) B3108935
theorem B3108941 : Blo 2071435 3108941 := bbase (se 3 (by rfl) ⟨582926, by rfl⟩ : syracuseStep 3108941 = 1165853) (by norm_num)
theorem B2072627 : Blo 2071435 2072627 := bstep (se 1 (by rfl) ⟨1554470, by rfl⟩ : syracuseStep 2072627 = 3108941) B3108941
theorem B4663421 : Blo 2071435 4663421 := bbase (se 3 (by rfl) ⟨874391, by rfl⟩ : syracuseStep 4663421 = 1748783) (by norm_num)
theorem B3108947 : Blo 2071435 3108947 := bstep (se 1 (by rfl) ⟨2331710, by rfl⟩ : syracuseStep 3108947 = 4663421) B4663421
theorem B2072631 : Blo 2071435 2072631 := bstep (se 1 (by rfl) ⟨1554473, by rfl⟩ : syracuseStep 2072631 = 3108947) B3108947
theorem B3497573 : Blo 2071435 3497573 := bbase (se 4 (by rfl) ⟨327897, by rfl⟩ : syracuseStep 3497573 = 655795) (by norm_num)
theorem B2331715 : Blo 2071435 2331715 := bstep (se 1 (by rfl) ⟨1748786, by rfl⟩ : syracuseStep 2331715 = 3497573) B3497573
theorem B3108953 : Blo 2071435 3108953 := bstep (se 2 (by rfl) ⟨1165857, by rfl⟩ : syracuseStep 3108953 = 2331715) B2331715
theorem B2072635 : Blo 2071435 2072635 := bstep (se 1 (by rfl) ⟨1554476, by rfl⟩ : syracuseStep 2072635 = 3108953) B3108953
theorem B2489977 : Blo 2071435 2489977 := bbase (se 2 (by rfl) ⟨933741, by rfl⟩ : syracuseStep 2489977 = 1867483) (by norm_num)
theorem B3319969 : Blo 2071435 3319969 := bstep (se 2 (by rfl) ⟨1244988, by rfl⟩ : syracuseStep 3319969 = 2489977) B2489977
theorem B4426625 : Blo 2071435 4426625 := bstep (se 2 (by rfl) ⟨1659984, by rfl⟩ : syracuseStep 4426625 = 3319969) B3319969
theorem B2951083 : Blo 2071435 2951083 := bstep (se 1 (by rfl) ⟨2213312, by rfl⟩ : syracuseStep 2951083 = 4426625) B4426625
theorem B15739109 : Blo 2071435 15739109 := bstep (se 4 (by rfl) ⟨1475541, by rfl⟩ : syracuseStep 15739109 = 2951083) B2951083
theorem B10492739 : Blo 2071435 10492739 := bstep (se 1 (by rfl) ⟨7869554, by rfl⟩ : syracuseStep 10492739 = 15739109) B15739109
theorem B6995159 : Blo 2071435 6995159 := bstep (se 1 (by rfl) ⟨5246369, by rfl⟩ : syracuseStep 6995159 = 10492739) B10492739
theorem B4663439 : Blo 2071435 4663439 := bstep (se 1 (by rfl) ⟨3497579, by rfl⟩ : syracuseStep 4663439 = 6995159) B6995159
theorem B3108959 : Blo 2071435 3108959 := bstep (se 1 (by rfl) ⟨2331719, by rfl⟩ : syracuseStep 3108959 = 4663439) B4663439
theorem B2072639 : Blo 2071435 2072639 := bstep (se 1 (by rfl) ⟨1554479, by rfl⟩ : syracuseStep 2072639 = 3108959) B3108959
theorem B3108965 : Blo 2071435 3108965 := bbase (se 4 (by rfl) ⟨291465, by rfl⟩ : syracuseStep 3108965 = 582931) (by norm_num)
theorem B2072643 : Blo 2071435 2072643 := bstep (se 1 (by rfl) ⟨1554482, by rfl⟩ : syracuseStep 2072643 = 3108965) B3108965
theorem B3734981 : Blo 2071435 3734981 := bbase (se 4 (by rfl) ⟨350154, by rfl⟩ : syracuseStep 3734981 = 700309) (by norm_num)
theorem B2489987 : Blo 2071435 2489987 := bstep (se 1 (by rfl) ⟨1867490, by rfl⟩ : syracuseStep 2489987 = 3734981) B3734981
theorem B6639965 : Blo 2071435 6639965 := bstep (se 3 (by rfl) ⟨1244993, by rfl⟩ : syracuseStep 6639965 = 2489987) B2489987
theorem B4426643 : Blo 2071435 4426643 := bstep (se 1 (by rfl) ⟨3319982, by rfl⟩ : syracuseStep 4426643 = 6639965) B6639965
theorem B2951095 : Blo 2071435 2951095 := bstep (se 1 (by rfl) ⟨2213321, by rfl⟩ : syracuseStep 2951095 = 4426643) B4426643
theorem B3934793 : Blo 2071435 3934793 := bstep (se 2 (by rfl) ⟨1475547, by rfl⟩ : syracuseStep 3934793 = 2951095) B2951095
theorem B2623195 : Blo 2071435 2623195 := bstep (se 1 (by rfl) ⟨1967396, by rfl⟩ : syracuseStep 2623195 = 3934793) B3934793
theorem B3497593 : Blo 2071435 3497593 := bstep (se 2 (by rfl) ⟨1311597, by rfl⟩ : syracuseStep 3497593 = 2623195) B2623195
theorem B4663457 : Blo 2071435 4663457 := bstep (se 2 (by rfl) ⟨1748796, by rfl⟩ : syracuseStep 4663457 = 3497593) B3497593
theorem B3108971 : Blo 2071435 3108971 := bstep (se 1 (by rfl) ⟨2331728, by rfl⟩ : syracuseStep 3108971 = 4663457) B4663457
theorem B2072647 : Blo 2071435 2072647 := bstep (se 1 (by rfl) ⟨1554485, by rfl⟩ : syracuseStep 2072647 = 3108971) B3108971
theorem B2331733 : Blo 2071435 2331733 := bbase (se 8 (by rfl) ⟨13662, by rfl⟩ : syracuseStep 2331733 = 27325) (by norm_num)
theorem B3108977 : Blo 2071435 3108977 := bstep (se 2 (by rfl) ⟨1165866, by rfl⟩ : syracuseStep 3108977 = 2331733) B2331733
theorem B2072651 : Blo 2071435 2072651 := bstep (se 1 (by rfl) ⟨1554488, by rfl⟩ : syracuseStep 2072651 = 3108977) B3108977
theorem B2623205 : Blo 2071435 2623205 := bbase (se 4 (by rfl) ⟨245925, by rfl⟩ : syracuseStep 2623205 = 491851) (by norm_num)
theorem B6995213 : Blo 2071435 6995213 := bstep (se 3 (by rfl) ⟨1311602, by rfl⟩ : syracuseStep 6995213 = 2623205) B2623205
theorem B4663475 : Blo 2071435 4663475 := bstep (se 1 (by rfl) ⟨3497606, by rfl⟩ : syracuseStep 4663475 = 6995213) B6995213
theorem B3108983 : Blo 2071435 3108983 := bstep (se 1 (by rfl) ⟨2331737, by rfl⟩ : syracuseStep 3108983 = 4663475) B4663475
theorem B2072655 : Blo 2071435 2072655 := bstep (se 1 (by rfl) ⟨1554491, by rfl⟩ : syracuseStep 2072655 = 3108983) B3108983
theorem B3108989 : Blo 2071435 3108989 := bbase (se 3 (by rfl) ⟨582935, by rfl⟩ : syracuseStep 3108989 = 1165871) (by norm_num)
theorem B2072659 : Blo 2071435 2072659 := bstep (se 1 (by rfl) ⟨1554494, by rfl⟩ : syracuseStep 2072659 = 3108989) B3108989
theorem B4663493 : Blo 2071435 4663493 := bbase (se 4 (by rfl) ⟨437202, by rfl⟩ : syracuseStep 4663493 = 874405) (by norm_num)
theorem B3108995 : Blo 2071435 3108995 := bstep (se 1 (by rfl) ⟨2331746, by rfl⟩ : syracuseStep 3108995 = 4663493) B4663493
theorem B2072663 : Blo 2071435 2072663 := bstep (se 1 (by rfl) ⟨1554497, by rfl⟩ : syracuseStep 2072663 = 3108995) B3108995
theorem B9454261 : Blo 2071435 9454261 := bbase (se 5 (by rfl) ⟨443168, by rfl⟩ : syracuseStep 9454261 = 886337) (by norm_num)
theorem B12605681 : Blo 2071435 12605681 := bstep (se 2 (by rfl) ⟨4727130, by rfl⟩ : syracuseStep 12605681 = 9454261) B9454261
theorem B8403787 : Blo 2071435 8403787 := bstep (se 1 (by rfl) ⟨6302840, by rfl⟩ : syracuseStep 8403787 = 12605681) B12605681
theorem B11205049 : Blo 2071435 11205049 := bstep (se 2 (by rfl) ⟨4201893, by rfl⟩ : syracuseStep 11205049 = 8403787) B8403787
theorem B14940065 : Blo 2071435 14940065 := bstep (se 2 (by rfl) ⟨5602524, by rfl⟩ : syracuseStep 14940065 = 11205049) B11205049
theorem B9960043 : Blo 2071435 9960043 := bstep (se 1 (by rfl) ⟨7470032, by rfl⟩ : syracuseStep 9960043 = 14940065) B14940065
theorem B13280057 : Blo 2071435 13280057 := bstep (se 2 (by rfl) ⟨4980021, by rfl⟩ : syracuseStep 13280057 = 9960043) B9960043
theorem B8853371 : Blo 2071435 8853371 := bstep (se 1 (by rfl) ⟨6640028, by rfl⟩ : syracuseStep 8853371 = 13280057) B13280057
theorem B5902247 : Blo 2071435 5902247 := bstep (se 1 (by rfl) ⟨4426685, by rfl⟩ : syracuseStep 5902247 = 8853371) B8853371
theorem B3934831 : Blo 2071435 3934831 := bstep (se 1 (by rfl) ⟨2951123, by rfl⟩ : syracuseStep 3934831 = 5902247) B5902247
theorem B5246441 : Blo 2071435 5246441 := bstep (se 2 (by rfl) ⟨1967415, by rfl⟩ : syracuseStep 5246441 = 3934831) B3934831
theorem B3497627 : Blo 2071435 3497627 := bstep (se 1 (by rfl) ⟨2623220, by rfl⟩ : syracuseStep 3497627 = 5246441) B5246441
theorem B2331751 : Blo 2071435 2331751 := bstep (se 1 (by rfl) ⟨1748813, by rfl⟩ : syracuseStep 2331751 = 3497627) B3497627
theorem B3109001 : Blo 2071435 3109001 := bstep (se 2 (by rfl) ⟨1165875, by rfl⟩ : syracuseStep 3109001 = 2331751) B2331751
theorem B2072667 : Blo 2071435 2072667 := bstep (se 1 (by rfl) ⟨1554500, by rfl⟩ : syracuseStep 2072667 = 3109001) B3109001
theorem B10492901 : Blo 2071435 10492901 := bbase (se 4 (by rfl) ⟨983709, by rfl⟩ : syracuseStep 10492901 = 1967419) (by norm_num)
theorem B6995267 : Blo 2071435 6995267 := bstep (se 1 (by rfl) ⟨5246450, by rfl⟩ : syracuseStep 6995267 = 10492901) B10492901
theorem B4663511 : Blo 2071435 4663511 := bstep (se 1 (by rfl) ⟨3497633, by rfl⟩ : syracuseStep 4663511 = 6995267) B6995267
theorem B3109007 : Blo 2071435 3109007 := bstep (se 1 (by rfl) ⟨2331755, by rfl⟩ : syracuseStep 3109007 = 4663511) B4663511
theorem B2072671 : Blo 2071435 2072671 := bstep (se 1 (by rfl) ⟨1554503, by rfl⟩ : syracuseStep 2072671 = 3109007) B3109007
theorem B3109013 : Blo 2071435 3109013 := bbase (se 6 (by rfl) ⟨72867, by rfl⟩ : syracuseStep 3109013 = 145735) (by norm_num)
theorem B2072675 : Blo 2071435 2072675 := bstep (se 1 (by rfl) ⟨1554506, by rfl⟩ : syracuseStep 2072675 = 3109013) B3109013
theorem B2490025 : Blo 2071435 2490025 := bbase (se 2 (by rfl) ⟨933759, by rfl⟩ : syracuseStep 2490025 = 1867519) (by norm_num)
theorem B3320033 : Blo 2071435 3320033 := bstep (se 2 (by rfl) ⟨1245012, by rfl⟩ : syracuseStep 3320033 = 2490025) B2490025
theorem B8853421 : Blo 2071435 8853421 := bstep (se 3 (by rfl) ⟨1660016, by rfl⟩ : syracuseStep 8853421 = 3320033) B3320033
theorem B11804561 : Blo 2071435 11804561 := bstep (se 2 (by rfl) ⟨4426710, by rfl⟩ : syracuseStep 11804561 = 8853421) B8853421
theorem B7869707 : Blo 2071435 7869707 := bstep (se 1 (by rfl) ⟨5902280, by rfl⟩ : syracuseStep 7869707 = 11804561) B11804561
theorem B5246471 : Blo 2071435 5246471 := bstep (se 1 (by rfl) ⟨3934853, by rfl⟩ : syracuseStep 5246471 = 7869707) B7869707
theorem B3497647 : Blo 2071435 3497647 := bstep (se 1 (by rfl) ⟨2623235, by rfl⟩ : syracuseStep 3497647 = 5246471) B5246471
theorem B4663529 : Blo 2071435 4663529 := bstep (se 2 (by rfl) ⟨1748823, by rfl⟩ : syracuseStep 4663529 = 3497647) B3497647
theorem B3109019 : Blo 2071435 3109019 := bstep (se 1 (by rfl) ⟨2331764, by rfl⟩ : syracuseStep 3109019 = 4663529) B4663529
theorem B2072679 : Blo 2071435 2072679 := bstep (se 1 (by rfl) ⟨1554509, by rfl⟩ : syracuseStep 2072679 = 3109019) B3109019
theorem B2331769 : Blo 2071435 2331769 := bbase (se 2 (by rfl) ⟨874413, by rfl⟩ : syracuseStep 2331769 = 1748827) (by norm_num)
theorem B3109025 : Blo 2071435 3109025 := bstep (se 2 (by rfl) ⟨1165884, by rfl⟩ : syracuseStep 3109025 = 2331769) B2331769
theorem B2072683 : Blo 2071435 2072683 := bstep (se 1 (by rfl) ⟨1554512, by rfl⟩ : syracuseStep 2072683 = 3109025) B3109025
theorem B16807733 : Blo 2071435 16807733 := bbase (se 5 (by rfl) ⟨787862, by rfl⟩ : syracuseStep 16807733 = 1575725) (by norm_num)
theorem B11205155 : Blo 2071435 11205155 := bstep (se 1 (by rfl) ⟨8403866, by rfl⟩ : syracuseStep 11205155 = 16807733) B16807733
theorem B29880413 : Blo 2071435 29880413 := bstep (se 3 (by rfl) ⟨5602577, by rfl⟩ : syracuseStep 29880413 = 11205155) B11205155
theorem B19920275 : Blo 2071435 19920275 := bstep (se 1 (by rfl) ⟨14940206, by rfl⟩ : syracuseStep 19920275 = 29880413) B29880413
theorem B13280183 : Blo 2071435 13280183 := bstep (se 1 (by rfl) ⟨9960137, by rfl⟩ : syracuseStep 13280183 = 19920275) B19920275
theorem B8853455 : Blo 2071435 8853455 := bstep (se 1 (by rfl) ⟨6640091, by rfl⟩ : syracuseStep 8853455 = 13280183) B13280183
theorem B5902303 : Blo 2071435 5902303 := bstep (se 1 (by rfl) ⟨4426727, by rfl⟩ : syracuseStep 5902303 = 8853455) B8853455
theorem B7869737 : Blo 2071435 7869737 := bstep (se 2 (by rfl) ⟨2951151, by rfl⟩ : syracuseStep 7869737 = 5902303) B5902303
theorem B5246491 : Blo 2071435 5246491 := bstep (se 1 (by rfl) ⟨3934868, by rfl⟩ : syracuseStep 5246491 = 7869737) B7869737
theorem B6995321 : Blo 2071435 6995321 := bstep (se 2 (by rfl) ⟨2623245, by rfl⟩ : syracuseStep 6995321 = 5246491) B5246491
theorem B4663547 : Blo 2071435 4663547 := bstep (se 1 (by rfl) ⟨3497660, by rfl⟩ : syracuseStep 4663547 = 6995321) B6995321
theorem B3109031 : Blo 2071435 3109031 := bstep (se 1 (by rfl) ⟨2331773, by rfl⟩ : syracuseStep 3109031 = 4663547) B4663547
theorem B2072687 : Blo 2071435 2072687 := bstep (se 1 (by rfl) ⟨1554515, by rfl⟩ : syracuseStep 2072687 = 3109031) B3109031
theorem B3109037 : Blo 2071435 3109037 := bbase (se 3 (by rfl) ⟨582944, by rfl⟩ : syracuseStep 3109037 = 1165889) (by norm_num)
theorem B2072691 : Blo 2071435 2072691 := bstep (se 1 (by rfl) ⟨1554518, by rfl⟩ : syracuseStep 2072691 = 3109037) B3109037
theorem B4663565 : Blo 2071435 4663565 := bbase (se 3 (by rfl) ⟨874418, by rfl⟩ : syracuseStep 4663565 = 1748837) (by norm_num)
theorem B3109043 : Blo 2071435 3109043 := bstep (se 1 (by rfl) ⟨2331782, by rfl⟩ : syracuseStep 3109043 = 4663565) B4663565
theorem B2072695 : Blo 2071435 2072695 := bstep (se 1 (by rfl) ⟨1554521, by rfl⟩ : syracuseStep 2072695 = 3109043) B3109043
theorem B2623261 : Blo 2071435 2623261 := bbase (se 3 (by rfl) ⟨491861, by rfl⟩ : syracuseStep 2623261 = 983723) (by norm_num)
theorem B3497681 : Blo 2071435 3497681 := bstep (se 2 (by rfl) ⟨1311630, by rfl⟩ : syracuseStep 3497681 = 2623261) B2623261
theorem B2331787 : Blo 2071435 2331787 := bstep (se 1 (by rfl) ⟨1748840, by rfl⟩ : syracuseStep 2331787 = 3497681) B3497681
theorem B3109049 : Blo 2071435 3109049 := bstep (se 2 (by rfl) ⟨1165893, by rfl⟩ : syracuseStep 3109049 = 2331787) B2331787
theorem B2072699 : Blo 2071435 2072699 := bstep (se 1 (by rfl) ⟨1554524, by rfl⟩ : syracuseStep 2072699 = 3109049) B3109049
theorem B4727213 : Blo 2071435 4727213 := bbase (se 3 (by rfl) ⟨886352, by rfl⟩ : syracuseStep 4727213 = 1772705) (by norm_num)
theorem B3151475 : Blo 2071435 3151475 := bstep (se 1 (by rfl) ⟨2363606, by rfl⟩ : syracuseStep 3151475 = 4727213) B4727213
theorem B2100983 : Blo 2071435 2100983 := bstep (se 1 (by rfl) ⟨1575737, by rfl⟩ : syracuseStep 2100983 = 3151475) B3151475
theorem B5602621 : Blo 2071435 5602621 := bstep (se 3 (by rfl) ⟨1050491, by rfl⟩ : syracuseStep 5602621 = 2100983) B2100983
theorem B7470161 : Blo 2071435 7470161 := bstep (se 2 (by rfl) ⟨2801310, by rfl⟩ : syracuseStep 7470161 = 5602621) B5602621
theorem B4980107 : Blo 2071435 4980107 := bstep (se 1 (by rfl) ⟨3735080, by rfl⟩ : syracuseStep 4980107 = 7470161) B7470161
theorem B3320071 : Blo 2071435 3320071 := bstep (se 1 (by rfl) ⟨2490053, by rfl⟩ : syracuseStep 3320071 = 4980107) B4980107
theorem B17707045 : Blo 2071435 17707045 := bstep (se 4 (by rfl) ⟨1660035, by rfl⟩ : syracuseStep 17707045 = 3320071) B3320071
theorem B23609393 : Blo 2071435 23609393 := bstep (se 2 (by rfl) ⟨8853522, by rfl⟩ : syracuseStep 23609393 = 17707045) B17707045
theorem B15739595 : Blo 2071435 15739595 := bstep (se 1 (by rfl) ⟨11804696, by rfl⟩ : syracuseStep 15739595 = 23609393) B23609393
theorem B10493063 : Blo 2071435 10493063 := bstep (se 1 (by rfl) ⟨7869797, by rfl⟩ : syracuseStep 10493063 = 15739595) B15739595
theorem B6995375 : Blo 2071435 6995375 := bstep (se 1 (by rfl) ⟨5246531, by rfl⟩ : syracuseStep 6995375 = 10493063) B10493063
theorem B4663583 : Blo 2071435 4663583 := bstep (se 1 (by rfl) ⟨3497687, by rfl⟩ : syracuseStep 4663583 = 6995375) B6995375
theorem B3109055 : Blo 2071435 3109055 := bstep (se 1 (by rfl) ⟨2331791, by rfl⟩ : syracuseStep 3109055 = 4663583) B4663583
theorem B2072703 : Blo 2071435 2072703 := bstep (se 1 (by rfl) ⟨1554527, by rfl⟩ : syracuseStep 2072703 = 3109055) B3109055
theorem B3109061 : Blo 2071435 3109061 := bbase (se 4 (by rfl) ⟨291474, by rfl⟩ : syracuseStep 3109061 = 582949) (by norm_num)
theorem B2072707 : Blo 2071435 2072707 := bstep (se 1 (by rfl) ⟨1554530, by rfl⟩ : syracuseStep 2072707 = 3109061) B3109061
theorem B3497701 : Blo 2071435 3497701 := bbase (se 4 (by rfl) ⟨327909, by rfl⟩ : syracuseStep 3497701 = 655819) (by norm_num)
theorem B4663601 : Blo 2071435 4663601 := bstep (se 2 (by rfl) ⟨1748850, by rfl⟩ : syracuseStep 4663601 = 3497701) B3497701
theorem B3109067 : Blo 2071435 3109067 := bstep (se 1 (by rfl) ⟨2331800, by rfl⟩ : syracuseStep 3109067 = 4663601) B4663601
theorem B2072711 : Blo 2071435 2072711 := bstep (se 1 (by rfl) ⟨1554533, by rfl⟩ : syracuseStep 2072711 = 3109067) B3109067
theorem B2331805 : Blo 2071435 2331805 := bbase (se 3 (by rfl) ⟨437213, by rfl⟩ : syracuseStep 2331805 = 874427) (by norm_num)
theorem B3109073 : Blo 2071435 3109073 := bstep (se 2 (by rfl) ⟨1165902, by rfl⟩ : syracuseStep 3109073 = 2331805) B2331805
theorem B2072715 : Blo 2071435 2072715 := bstep (se 1 (by rfl) ⟨1554536, by rfl⟩ : syracuseStep 2072715 = 3109073) B3109073
theorem B6995429 : Blo 2071435 6995429 := bbase (se 4 (by rfl) ⟨655821, by rfl⟩ : syracuseStep 6995429 = 1311643) (by norm_num)
theorem B4663619 : Blo 2071435 4663619 := bstep (se 1 (by rfl) ⟨3497714, by rfl⟩ : syracuseStep 4663619 = 6995429) B6995429
theorem B3109079 : Blo 2071435 3109079 := bstep (se 1 (by rfl) ⟨2331809, by rfl⟩ : syracuseStep 3109079 = 4663619) B4663619
theorem B2072719 : Blo 2071435 2072719 := bstep (se 1 (by rfl) ⟨1554539, by rfl⟩ : syracuseStep 2072719 = 3109079) B3109079
theorem B3109085 : Blo 2071435 3109085 := bbase (se 3 (by rfl) ⟨582953, by rfl⟩ : syracuseStep 3109085 = 1165907) (by norm_num)
theorem B2072723 : Blo 2071435 2072723 := bstep (se 1 (by rfl) ⟨1554542, by rfl⟩ : syracuseStep 2072723 = 3109085) B3109085
theorem B4663637 : Blo 2071435 4663637 := bbase (se 10 (by rfl) ⟨6831, by rfl⟩ : syracuseStep 4663637 = 13663) (by norm_num)
theorem B3109091 : Blo 2071435 3109091 := bstep (se 1 (by rfl) ⟨2331818, by rfl⟩ : syracuseStep 3109091 = 4663637) B4663637
theorem B2072727 : Blo 2071435 2072727 := bstep (se 1 (by rfl) ⟨1554545, by rfl⟩ : syracuseStep 2072727 = 3109091) B3109091
theorem B3320117 : Blo 2071435 3320117 := bbase (se 5 (by rfl) ⟨155630, by rfl⟩ : syracuseStep 3320117 = 311261) (by norm_num)
theorem B2213411 : Blo 2071435 2213411 := bstep (se 1 (by rfl) ⟨1660058, by rfl⟩ : syracuseStep 2213411 = 3320117) B3320117
theorem B5902429 : Blo 2071435 5902429 := bstep (se 3 (by rfl) ⟨1106705, by rfl⟩ : syracuseStep 5902429 = 2213411) B2213411
theorem B7869905 : Blo 2071435 7869905 := bstep (se 2 (by rfl) ⟨2951214, by rfl⟩ : syracuseStep 7869905 = 5902429) B5902429
theorem B5246603 : Blo 2071435 5246603 := bstep (se 1 (by rfl) ⟨3934952, by rfl⟩ : syracuseStep 5246603 = 7869905) B7869905
theorem B3497735 : Blo 2071435 3497735 := bstep (se 1 (by rfl) ⟨2623301, by rfl⟩ : syracuseStep 3497735 = 5246603) B5246603
theorem B2331823 : Blo 2071435 2331823 := bstep (se 1 (by rfl) ⟨1748867, by rfl⟩ : syracuseStep 2331823 = 3497735) B3497735
theorem B3109097 : Blo 2071435 3109097 := bstep (se 2 (by rfl) ⟨1165911, by rfl⟩ : syracuseStep 3109097 = 2331823) B2331823
theorem B2072731 : Blo 2071435 2072731 := bstep (se 1 (by rfl) ⟨1554548, by rfl⟩ : syracuseStep 2072731 = 3109097) B3109097
theorem B25212181 : Blo 2071435 25212181 := bbase (se 6 (by rfl) ⟨590910, by rfl⟩ : syracuseStep 25212181 = 1181821) (by norm_num)
theorem B33616241 : Blo 2071435 33616241 := bstep (se 2 (by rfl) ⟨12606090, by rfl⟩ : syracuseStep 33616241 = 25212181) B25212181
theorem B22410827 : Blo 2071435 22410827 := bstep (se 1 (by rfl) ⟨16808120, by rfl⟩ : syracuseStep 22410827 = 33616241) B33616241
theorem B14940551 : Blo 2071435 14940551 := bstep (se 1 (by rfl) ⟨11205413, by rfl⟩ : syracuseStep 14940551 = 22410827) B22410827
theorem B39841469 : Blo 2071435 39841469 := bstep (se 3 (by rfl) ⟨7470275, by rfl⟩ : syracuseStep 39841469 = 14940551) B14940551
theorem B26560979 : Blo 2071435 26560979 := bstep (se 1 (by rfl) ⟨19920734, by rfl⟩ : syracuseStep 26560979 = 39841469) B39841469
theorem B17707319 : Blo 2071435 17707319 := bstep (se 1 (by rfl) ⟨13280489, by rfl⟩ : syracuseStep 17707319 = 26560979) B26560979
theorem B11804879 : Blo 2071435 11804879 := bstep (se 1 (by rfl) ⟨8853659, by rfl⟩ : syracuseStep 11804879 = 17707319) B17707319
theorem B7869919 : Blo 2071435 7869919 := bstep (se 1 (by rfl) ⟨5902439, by rfl⟩ : syracuseStep 7869919 = 11804879) B11804879
theorem B10493225 : Blo 2071435 10493225 := bstep (se 2 (by rfl) ⟨3934959, by rfl⟩ : syracuseStep 10493225 = 7869919) B7869919
theorem B6995483 : Blo 2071435 6995483 := bstep (se 1 (by rfl) ⟨5246612, by rfl⟩ : syracuseStep 6995483 = 10493225) B10493225
theorem B4663655 : Blo 2071435 4663655 := bstep (se 1 (by rfl) ⟨3497741, by rfl⟩ : syracuseStep 4663655 = 6995483) B6995483
theorem B3109103 : Blo 2071435 3109103 := bstep (se 1 (by rfl) ⟨2331827, by rfl⟩ : syracuseStep 3109103 = 4663655) B4663655
theorem B2072735 : Blo 2071435 2072735 := bstep (se 1 (by rfl) ⟨1554551, by rfl⟩ : syracuseStep 2072735 = 3109103) B3109103
theorem B3109109 : Blo 2071435 3109109 := bbase (se 5 (by rfl) ⟨145739, by rfl⟩ : syracuseStep 3109109 = 291479) (by norm_num)
theorem B2072739 : Blo 2071435 2072739 := bstep (se 1 (by rfl) ⟨1554554, by rfl⟩ : syracuseStep 2072739 = 3109109) B3109109
theorem B5679173 : Blo 2071435 5679173 := bbase (se 4 (by rfl) ⟨532422, by rfl⟩ : syracuseStep 5679173 = 1064845) (by norm_num)
theorem B3786115 : Blo 2071435 3786115 := bstep (se 1 (by rfl) ⟨2839586, by rfl⟩ : syracuseStep 3786115 = 5679173) B5679173
theorem B5048153 : Blo 2071435 5048153 := bstep (se 2 (by rfl) ⟨1893057, by rfl⟩ : syracuseStep 5048153 = 3786115) B3786115
theorem B3365435 : Blo 2071435 3365435 := bstep (se 1 (by rfl) ⟨2524076, by rfl⟩ : syracuseStep 3365435 = 5048153) B5048153
theorem B2243623 : Blo 2071435 2243623 := bstep (se 1 (by rfl) ⟨1682717, by rfl⟩ : syracuseStep 2243623 = 3365435) B3365435
theorem B2991497 : Blo 2071435 2991497 := bstep (se 2 (by rfl) ⟨1121811, by rfl⟩ : syracuseStep 2991497 = 2243623) B2243623
theorem B7977325 : Blo 2071435 7977325 := bstep (se 3 (by rfl) ⟨1495748, by rfl⟩ : syracuseStep 7977325 = 2991497) B2991497
theorem B10636433 : Blo 2071435 10636433 := bstep (se 2 (by rfl) ⟨3988662, by rfl⟩ : syracuseStep 10636433 = 7977325) B7977325
theorem B7090955 : Blo 2071435 7090955 := bstep (se 1 (by rfl) ⟨5318216, by rfl⟩ : syracuseStep 7090955 = 10636433) B10636433
theorem B4727303 : Blo 2071435 4727303 := bstep (se 1 (by rfl) ⟨3545477, by rfl⟩ : syracuseStep 4727303 = 7090955) B7090955
theorem B50424565 : Blo 2071435 50424565 := bstep (se 5 (by rfl) ⟨2363651, by rfl⟩ : syracuseStep 50424565 = 4727303) B4727303
theorem B67232753 : Blo 2071435 67232753 := bstep (se 2 (by rfl) ⟨25212282, by rfl⟩ : syracuseStep 67232753 = 50424565) B50424565
theorem B44821835 : Blo 2071435 44821835 := bstep (se 1 (by rfl) ⟨33616376, by rfl⟩ : syracuseStep 44821835 = 67232753) B67232753
theorem B29881223 : Blo 2071435 29881223 := bstep (se 1 (by rfl) ⟨22410917, by rfl⟩ : syracuseStep 29881223 = 44821835) B44821835
theorem B19920815 : Blo 2071435 19920815 := bstep (se 1 (by rfl) ⟨14940611, by rfl⟩ : syracuseStep 19920815 = 29881223) B29881223
theorem B13280543 : Blo 2071435 13280543 := bstep (se 1 (by rfl) ⟨9960407, by rfl⟩ : syracuseStep 13280543 = 19920815) B19920815
theorem B8853695 : Blo 2071435 8853695 := bstep (se 1 (by rfl) ⟨6640271, by rfl⟩ : syracuseStep 8853695 = 13280543) B13280543
theorem B5902463 : Blo 2071435 5902463 := bstep (se 1 (by rfl) ⟨4426847, by rfl⟩ : syracuseStep 5902463 = 8853695) B8853695
theorem B3934975 : Blo 2071435 3934975 := bstep (se 1 (by rfl) ⟨2951231, by rfl⟩ : syracuseStep 3934975 = 5902463) B5902463
theorem B5246633 : Blo 2071435 5246633 := bstep (se 2 (by rfl) ⟨1967487, by rfl⟩ : syracuseStep 5246633 = 3934975) B3934975
theorem B3497755 : Blo 2071435 3497755 := bstep (se 1 (by rfl) ⟨2623316, by rfl⟩ : syracuseStep 3497755 = 5246633) B5246633
theorem B4663673 : Blo 2071435 4663673 := bstep (se 2 (by rfl) ⟨1748877, by rfl⟩ : syracuseStep 4663673 = 3497755) B3497755
theorem B3109115 : Blo 2071435 3109115 := bstep (se 1 (by rfl) ⟨2331836, by rfl⟩ : syracuseStep 3109115 = 4663673) B4663673
theorem B2072743 : Blo 2071435 2072743 := bstep (se 1 (by rfl) ⟨1554557, by rfl⟩ : syracuseStep 2072743 = 3109115) B3109115
theorem B2331841 : Blo 2071435 2331841 := bbase (se 2 (by rfl) ⟨874440, by rfl⟩ : syracuseStep 2331841 = 1748881) (by norm_num)
theorem B3109121 : Blo 2071435 3109121 := bstep (se 2 (by rfl) ⟨1165920, by rfl⟩ : syracuseStep 3109121 = 2331841) B2331841
theorem B2072747 : Blo 2071435 2072747 := bstep (se 1 (by rfl) ⟨1554560, by rfl⟩ : syracuseStep 2072747 = 3109121) B3109121
theorem B5246653 : Blo 2071435 5246653 := bbase (se 3 (by rfl) ⟨983747, by rfl⟩ : syracuseStep 5246653 = 1967495) (by norm_num)
theorem B6995537 : Blo 2071435 6995537 := bstep (se 2 (by rfl) ⟨2623326, by rfl⟩ : syracuseStep 6995537 = 5246653) B5246653
theorem B4663691 : Blo 2071435 4663691 := bstep (se 1 (by rfl) ⟨3497768, by rfl⟩ : syracuseStep 4663691 = 6995537) B6995537
theorem B3109127 : Blo 2071435 3109127 := bstep (se 1 (by rfl) ⟨2331845, by rfl⟩ : syracuseStep 3109127 = 4663691) B4663691
theorem B2072751 : Blo 2071435 2072751 := bstep (se 1 (by rfl) ⟨1554563, by rfl⟩ : syracuseStep 2072751 = 3109127) B3109127
theorem B3109133 : Blo 2071435 3109133 := bbase (se 3 (by rfl) ⟨582962, by rfl⟩ : syracuseStep 3109133 = 1165925) (by norm_num)
theorem B2072755 : Blo 2071435 2072755 := bstep (se 1 (by rfl) ⟨1554566, by rfl⟩ : syracuseStep 2072755 = 3109133) B3109133
theorem B4663709 : Blo 2071435 4663709 := bbase (se 3 (by rfl) ⟨874445, by rfl⟩ : syracuseStep 4663709 = 1748891) (by norm_num)
theorem B3109139 : Blo 2071435 3109139 := bstep (se 1 (by rfl) ⟨2331854, by rfl⟩ : syracuseStep 3109139 = 4663709) B4663709
theorem B2072759 : Blo 2071435 2072759 := bstep (se 1 (by rfl) ⟨1554569, by rfl⟩ : syracuseStep 2072759 = 3109139) B3109139
theorem B3497789 : Blo 2071435 3497789 := bbase (se 3 (by rfl) ⟨655835, by rfl⟩ : syracuseStep 3497789 = 1311671) (by norm_num)
theorem B2331859 : Blo 2071435 2331859 := bstep (se 1 (by rfl) ⟨1748894, by rfl⟩ : syracuseStep 2331859 = 3497789) B3497789
theorem B3109145 : Blo 2071435 3109145 := bstep (se 2 (by rfl) ⟨1165929, by rfl⟩ : syracuseStep 3109145 = 2331859) B2331859
theorem B2072763 : Blo 2071435 2072763 := bstep (se 1 (by rfl) ⟨1554572, by rfl⟩ : syracuseStep 2072763 = 3109145) B3109145
theorem B2213449 : Blo 2071435 2213449 := bbase (se 2 (by rfl) ⟨830043, by rfl⟩ : syracuseStep 2213449 = 1660087) (by norm_num)
theorem B11805061 : Blo 2071435 11805061 := bstep (se 4 (by rfl) ⟨1106724, by rfl⟩ : syracuseStep 11805061 = 2213449) B2213449
theorem B15740081 : Blo 2071435 15740081 := bstep (se 2 (by rfl) ⟨5902530, by rfl⟩ : syracuseStep 15740081 = 11805061) B11805061
theorem B10493387 : Blo 2071435 10493387 := bstep (se 1 (by rfl) ⟨7870040, by rfl⟩ : syracuseStep 10493387 = 15740081) B15740081
theorem B6995591 : Blo 2071435 6995591 := bstep (se 1 (by rfl) ⟨5246693, by rfl⟩ : syracuseStep 6995591 = 10493387) B10493387
theorem B4663727 : Blo 2071435 4663727 := bstep (se 1 (by rfl) ⟨3497795, by rfl⟩ : syracuseStep 4663727 = 6995591) B6995591
theorem B3109151 : Blo 2071435 3109151 := bstep (se 1 (by rfl) ⟨2331863, by rfl⟩ : syracuseStep 3109151 = 4663727) B4663727
theorem B2072767 : Blo 2071435 2072767 := bstep (se 1 (by rfl) ⟨1554575, by rfl⟩ : syracuseStep 2072767 = 3109151) B3109151
theorem B3109157 : Blo 2071435 3109157 := bbase (se 4 (by rfl) ⟨291483, by rfl⟩ : syracuseStep 3109157 = 582967) (by norm_num)
theorem B2072771 : Blo 2071435 2072771 := bstep (se 1 (by rfl) ⟨1554578, by rfl⟩ : syracuseStep 2072771 = 3109157) B3109157
theorem B2623357 : Blo 2071435 2623357 := bbase (se 3 (by rfl) ⟨491879, by rfl⟩ : syracuseStep 2623357 = 983759) (by norm_num)
theorem B3497809 : Blo 2071435 3497809 := bstep (se 2 (by rfl) ⟨1311678, by rfl⟩ : syracuseStep 3497809 = 2623357) B2623357
theorem B4663745 : Blo 2071435 4663745 := bstep (se 2 (by rfl) ⟨1748904, by rfl⟩ : syracuseStep 4663745 = 3497809) B3497809
theorem B3109163 : Blo 2071435 3109163 := bstep (se 1 (by rfl) ⟨2331872, by rfl⟩ : syracuseStep 3109163 = 4663745) B4663745
theorem B2072775 : Blo 2071435 2072775 := bstep (se 1 (by rfl) ⟨1554581, by rfl⟩ : syracuseStep 2072775 = 3109163) B3109163
theorem B2331877 : Blo 2071435 2331877 := bbase (se 4 (by rfl) ⟨218613, by rfl⟩ : syracuseStep 2331877 = 437227) (by norm_num)
theorem B3109169 : Blo 2071435 3109169 := bstep (se 2 (by rfl) ⟨1165938, by rfl⟩ : syracuseStep 3109169 = 2331877) B2331877
theorem B2072779 : Blo 2071435 2072779 := bstep (se 1 (by rfl) ⟨1554584, by rfl⟩ : syracuseStep 2072779 = 3109169) B3109169
theorem B4426933 : Blo 2071435 4426933 := bbase (se 5 (by rfl) ⟨207512, by rfl⟩ : syracuseStep 4426933 = 415025) (by norm_num)
theorem B5902577 : Blo 2071435 5902577 := bstep (se 2 (by rfl) ⟨2213466, by rfl⟩ : syracuseStep 5902577 = 4426933) B4426933
theorem B3935051 : Blo 2071435 3935051 := bstep (se 1 (by rfl) ⟨2951288, by rfl⟩ : syracuseStep 3935051 = 5902577) B5902577
theorem B2623367 : Blo 2071435 2623367 := bstep (se 1 (by rfl) ⟨1967525, by rfl⟩ : syracuseStep 2623367 = 3935051) B3935051
theorem B6995645 : Blo 2071435 6995645 := bstep (se 3 (by rfl) ⟨1311683, by rfl⟩ : syracuseStep 6995645 = 2623367) B2623367
theorem B4663763 : Blo 2071435 4663763 := bstep (se 1 (by rfl) ⟨3497822, by rfl⟩ : syracuseStep 4663763 = 6995645) B6995645
theorem B3109175 : Blo 2071435 3109175 := bstep (se 1 (by rfl) ⟨2331881, by rfl⟩ : syracuseStep 3109175 = 4663763) B4663763
theorem B2072783 : Blo 2071435 2072783 := bstep (se 1 (by rfl) ⟨1554587, by rfl⟩ : syracuseStep 2072783 = 3109175) B3109175
theorem B3109181 : Blo 2071435 3109181 := bbase (se 3 (by rfl) ⟨582971, by rfl⟩ : syracuseStep 3109181 = 1165943) (by norm_num)
theorem B2072787 : Blo 2071435 2072787 := bstep (se 1 (by rfl) ⟨1554590, by rfl⟩ : syracuseStep 2072787 = 3109181) B3109181
theorem B4663781 : Blo 2071435 4663781 := bbase (se 4 (by rfl) ⟨437229, by rfl⟩ : syracuseStep 4663781 = 874459) (by norm_num)
theorem B3109187 : Blo 2071435 3109187 := bstep (se 1 (by rfl) ⟨2331890, by rfl⟩ : syracuseStep 3109187 = 4663781) B4663781
theorem B2072791 : Blo 2071435 2072791 := bstep (se 1 (by rfl) ⟨1554593, by rfl⟩ : syracuseStep 2072791 = 3109187) B3109187
theorem B5246765 : Blo 2071435 5246765 := bbase (se 3 (by rfl) ⟨983768, by rfl⟩ : syracuseStep 5246765 = 1967537) (by norm_num)
theorem B3497843 : Blo 2071435 3497843 := bstep (se 1 (by rfl) ⟨2623382, by rfl⟩ : syracuseStep 3497843 = 5246765) B5246765
theorem B2331895 : Blo 2071435 2331895 := bstep (se 1 (by rfl) ⟨1748921, by rfl⟩ : syracuseStep 2331895 = 3497843) B3497843
theorem B3109193 : Blo 2071435 3109193 := bstep (se 2 (by rfl) ⟨1165947, by rfl⟩ : syracuseStep 3109193 = 2331895) B2331895
theorem B2072795 : Blo 2071435 2072795 := bstep (se 1 (by rfl) ⟨1554596, by rfl⟩ : syracuseStep 2072795 = 3109193) B3109193
theorem B9960677 : Blo 2071435 9960677 := bbase (se 4 (by rfl) ⟨933813, by rfl⟩ : syracuseStep 9960677 = 1867627) (by norm_num)
theorem B6640451 : Blo 2071435 6640451 := bstep (se 1 (by rfl) ⟨4980338, by rfl⟩ : syracuseStep 6640451 = 9960677) B9960677
theorem B4426967 : Blo 2071435 4426967 := bstep (se 1 (by rfl) ⟨3320225, by rfl⟩ : syracuseStep 4426967 = 6640451) B6640451
theorem B2951311 : Blo 2071435 2951311 := bstep (se 1 (by rfl) ⟨2213483, by rfl⟩ : syracuseStep 2951311 = 4426967) B4426967
theorem B3935081 : Blo 2071435 3935081 := bstep (se 2 (by rfl) ⟨1475655, by rfl⟩ : syracuseStep 3935081 = 2951311) B2951311
theorem B10493549 : Blo 2071435 10493549 := bstep (se 3 (by rfl) ⟨1967540, by rfl⟩ : syracuseStep 10493549 = 3935081) B3935081
theorem B6995699 : Blo 2071435 6995699 := bstep (se 1 (by rfl) ⟨5246774, by rfl⟩ : syracuseStep 6995699 = 10493549) B10493549
theorem B4663799 : Blo 2071435 4663799 := bstep (se 1 (by rfl) ⟨3497849, by rfl⟩ : syracuseStep 4663799 = 6995699) B6995699
theorem B3109199 : Blo 2071435 3109199 := bstep (se 1 (by rfl) ⟨2331899, by rfl⟩ : syracuseStep 3109199 = 4663799) B4663799
theorem B2072799 : Blo 2071435 2072799 := bstep (se 1 (by rfl) ⟨1554599, by rfl⟩ : syracuseStep 2072799 = 3109199) B3109199
theorem B3109205 : Blo 2071435 3109205 := bbase (se 10 (by rfl) ⟨4554, by rfl⟩ : syracuseStep 3109205 = 9109) (by norm_num)
theorem B2072803 : Blo 2071435 2072803 := bstep (se 1 (by rfl) ⟨1554602, by rfl⟩ : syracuseStep 2072803 = 3109205) B3109205
theorem B5902645 : Blo 2071435 5902645 := bbase (se 5 (by rfl) ⟨276686, by rfl⟩ : syracuseStep 5902645 = 553373) (by norm_num)
theorem B7870193 : Blo 2071435 7870193 := bstep (se 2 (by rfl) ⟨2951322, by rfl⟩ : syracuseStep 7870193 = 5902645) B5902645
theorem B5246795 : Blo 2071435 5246795 := bstep (se 1 (by rfl) ⟨3935096, by rfl⟩ : syracuseStep 5246795 = 7870193) B7870193
theorem B3497863 : Blo 2071435 3497863 := bstep (se 1 (by rfl) ⟨2623397, by rfl⟩ : syracuseStep 3497863 = 5246795) B5246795
theorem B4663817 : Blo 2071435 4663817 := bstep (se 2 (by rfl) ⟨1748931, by rfl⟩ : syracuseStep 4663817 = 3497863) B3497863
theorem B3109211 : Blo 2071435 3109211 := bstep (se 1 (by rfl) ⟨2331908, by rfl⟩ : syracuseStep 3109211 = 4663817) B4663817
theorem B2072807 : Blo 2071435 2072807 := bstep (se 1 (by rfl) ⟨1554605, by rfl⟩ : syracuseStep 2072807 = 3109211) B3109211
theorem B2331913 : Blo 2071435 2331913 := bbase (se 2 (by rfl) ⟨874467, by rfl⟩ : syracuseStep 2331913 = 1748935) (by norm_num)
theorem B3109217 : Blo 2071435 3109217 := bstep (se 2 (by rfl) ⟨1165956, by rfl⟩ : syracuseStep 3109217 = 2331913) B2331913
theorem B2072811 : Blo 2071435 2072811 := bstep (se 1 (by rfl) ⟨1554608, by rfl⟩ : syracuseStep 2072811 = 3109217) B3109217
theorem B26562005 : Blo 2071435 26562005 := bbase (se 7 (by rfl) ⟨311273, by rfl⟩ : syracuseStep 26562005 = 622547) (by norm_num)
theorem B17708003 : Blo 2071435 17708003 := bstep (se 1 (by rfl) ⟨13281002, by rfl⟩ : syracuseStep 17708003 = 26562005) B26562005
theorem B11805335 : Blo 2071435 11805335 := bstep (se 1 (by rfl) ⟨8854001, by rfl⟩ : syracuseStep 11805335 = 17708003) B17708003
theorem B7870223 : Blo 2071435 7870223 := bstep (se 1 (by rfl) ⟨5902667, by rfl⟩ : syracuseStep 7870223 = 11805335) B11805335
theorem B5246815 : Blo 2071435 5246815 := bstep (se 1 (by rfl) ⟨3935111, by rfl⟩ : syracuseStep 5246815 = 7870223) B7870223
theorem B6995753 : Blo 2071435 6995753 := bstep (se 2 (by rfl) ⟨2623407, by rfl⟩ : syracuseStep 6995753 = 5246815) B5246815
theorem B4663835 : Blo 2071435 4663835 := bstep (se 1 (by rfl) ⟨3497876, by rfl⟩ : syracuseStep 4663835 = 6995753) B6995753
theorem B3109223 : Blo 2071435 3109223 := bstep (se 1 (by rfl) ⟨2331917, by rfl⟩ : syracuseStep 3109223 = 4663835) B4663835
theorem B2072815 : Blo 2071435 2072815 := bstep (se 1 (by rfl) ⟨1554611, by rfl⟩ : syracuseStep 2072815 = 3109223) B3109223
theorem B3109229 : Blo 2071435 3109229 := bbase (se 3 (by rfl) ⟨582980, by rfl⟩ : syracuseStep 3109229 = 1165961) (by norm_num)
theorem B2072819 : Blo 2071435 2072819 := bstep (se 1 (by rfl) ⟨1554614, by rfl⟩ : syracuseStep 2072819 = 3109229) B3109229
theorem B4663853 : Blo 2071435 4663853 := bbase (se 3 (by rfl) ⟨874472, by rfl⟩ : syracuseStep 4663853 = 1748945) (by norm_num)
theorem B3109235 : Blo 2071435 3109235 := bstep (se 1 (by rfl) ⟨2331926, by rfl⟩ : syracuseStep 3109235 = 4663853) B4663853
theorem B2072823 : Blo 2071435 2072823 := bstep (se 1 (by rfl) ⟨1554617, by rfl⟩ : syracuseStep 2072823 = 3109235) B3109235
theorem B2101109 : Blo 2071435 2101109 := bbase (se 5 (by rfl) ⟨98489, by rfl⟩ : syracuseStep 2101109 = 196979) (by norm_num)
theorem B22411829 : Blo 2071435 22411829 := bstep (se 5 (by rfl) ⟨1050554, by rfl⟩ : syracuseStep 22411829 = 2101109) B2101109
theorem B14941219 : Blo 2071435 14941219 := bstep (se 1 (by rfl) ⟨11205914, by rfl⟩ : syracuseStep 14941219 = 22411829) B22411829
theorem B19921625 : Blo 2071435 19921625 := bstep (se 2 (by rfl) ⟨7470609, by rfl⟩ : syracuseStep 19921625 = 14941219) B14941219
theorem B13281083 : Blo 2071435 13281083 := bstep (se 1 (by rfl) ⟨9960812, by rfl⟩ : syracuseStep 13281083 = 19921625) B19921625
theorem B8854055 : Blo 2071435 8854055 := bstep (se 1 (by rfl) ⟨6640541, by rfl⟩ : syracuseStep 8854055 = 13281083) B13281083
theorem B5902703 : Blo 2071435 5902703 := bstep (se 1 (by rfl) ⟨4427027, by rfl⟩ : syracuseStep 5902703 = 8854055) B8854055
theorem B3935135 : Blo 2071435 3935135 := bstep (se 1 (by rfl) ⟨2951351, by rfl⟩ : syracuseStep 3935135 = 5902703) B5902703
theorem B2623423 : Blo 2071435 2623423 := bstep (se 1 (by rfl) ⟨1967567, by rfl⟩ : syracuseStep 2623423 = 3935135) B3935135
theorem B3497897 : Blo 2071435 3497897 := bstep (se 2 (by rfl) ⟨1311711, by rfl⟩ : syracuseStep 3497897 = 2623423) B2623423
theorem B2331931 : Blo 2071435 2331931 := bstep (se 1 (by rfl) ⟨1748948, by rfl⟩ : syracuseStep 2331931 = 3497897) B3497897
theorem B3109241 : Blo 2071435 3109241 := bstep (se 2 (by rfl) ⟨1165965, by rfl⟩ : syracuseStep 3109241 = 2331931) B2331931
theorem B2072827 : Blo 2071435 2072827 := bstep (se 1 (by rfl) ⟨1554620, by rfl⟩ : syracuseStep 2072827 = 3109241) B3109241
theorem B35416277 : Blo 2071435 35416277 := bbase (se 7 (by rfl) ⟨415034, by rfl⟩ : syracuseStep 35416277 = 830069) (by norm_num)
theorem B23610851 : Blo 2071435 23610851 := bstep (se 1 (by rfl) ⟨17708138, by rfl⟩ : syracuseStep 23610851 = 35416277) B35416277
theorem B15740567 : Blo 2071435 15740567 := bstep (se 1 (by rfl) ⟨11805425, by rfl⟩ : syracuseStep 15740567 = 23610851) B23610851
theorem B10493711 : Blo 2071435 10493711 := bstep (se 1 (by rfl) ⟨7870283, by rfl⟩ : syracuseStep 10493711 = 15740567) B15740567
theorem B6995807 : Blo 2071435 6995807 := bstep (se 1 (by rfl) ⟨5246855, by rfl⟩ : syracuseStep 6995807 = 10493711) B10493711
theorem B4663871 : Blo 2071435 4663871 := bstep (se 1 (by rfl) ⟨3497903, by rfl⟩ : syracuseStep 4663871 = 6995807) B6995807
theorem B3109247 : Blo 2071435 3109247 := bstep (se 1 (by rfl) ⟨2331935, by rfl⟩ : syracuseStep 3109247 = 4663871) B4663871
theorem B2072831 : Blo 2071435 2072831 := bstep (se 1 (by rfl) ⟨1554623, by rfl⟩ : syracuseStep 2072831 = 3109247) B3109247
theorem B3109253 : Blo 2071435 3109253 := bbase (se 4 (by rfl) ⟨291492, by rfl⟩ : syracuseStep 3109253 = 582985) (by norm_num)
theorem B2072835 : Blo 2071435 2072835 := bstep (se 1 (by rfl) ⟨1554626, by rfl⟩ : syracuseStep 2072835 = 3109253) B3109253
theorem B3497917 : Blo 2071435 3497917 := bbase (se 3 (by rfl) ⟨655859, by rfl⟩ : syracuseStep 3497917 = 1311719) (by norm_num)
theorem B4663889 : Blo 2071435 4663889 := bstep (se 2 (by rfl) ⟨1748958, by rfl⟩ : syracuseStep 4663889 = 3497917) B3497917
theorem B3109259 : Blo 2071435 3109259 := bstep (se 1 (by rfl) ⟨2331944, by rfl⟩ : syracuseStep 3109259 = 4663889) B4663889
theorem B2072839 : Blo 2071435 2072839 := bstep (se 1 (by rfl) ⟨1554629, by rfl⟩ : syracuseStep 2072839 = 3109259) B3109259
theorem B2331949 : Blo 2071435 2331949 := bbase (se 3 (by rfl) ⟨437240, by rfl⟩ : syracuseStep 2331949 = 874481) (by norm_num)
theorem B3109265 : Blo 2071435 3109265 := bstep (se 2 (by rfl) ⟨1165974, by rfl⟩ : syracuseStep 3109265 = 2331949) B2331949
theorem B2072843 : Blo 2071435 2072843 := bstep (se 1 (by rfl) ⟨1554632, by rfl⟩ : syracuseStep 2072843 = 3109265) B3109265
theorem B6995861 : Blo 2071435 6995861 := bbase (se 6 (by rfl) ⟨163965, by rfl⟩ : syracuseStep 6995861 = 327931) (by norm_num)
theorem B4663907 : Blo 2071435 4663907 := bstep (se 1 (by rfl) ⟨3497930, by rfl⟩ : syracuseStep 4663907 = 6995861) B6995861
theorem B3109271 : Blo 2071435 3109271 := bstep (se 1 (by rfl) ⟨2331953, by rfl⟩ : syracuseStep 3109271 = 4663907) B4663907
theorem B2072847 : Blo 2071435 2072847 := bstep (se 1 (by rfl) ⟨1554635, by rfl⟩ : syracuseStep 2072847 = 3109271) B3109271
theorem B3109277 : Blo 2071435 3109277 := bbase (se 3 (by rfl) ⟨582989, by rfl⟩ : syracuseStep 3109277 = 1165979) (by norm_num)
theorem B2072851 : Blo 2071435 2072851 := bstep (se 1 (by rfl) ⟨1554638, by rfl⟩ : syracuseStep 2072851 = 3109277) B3109277
theorem B4663925 : Blo 2071435 4663925 := bbase (se 5 (by rfl) ⟨218621, by rfl⟩ : syracuseStep 4663925 = 437243) (by norm_num)
theorem B3109283 : Blo 2071435 3109283 := bstep (se 1 (by rfl) ⟨2331962, by rfl⟩ : syracuseStep 3109283 = 4663925) B4663925
theorem B2072855 : Blo 2071435 2072855 := bstep (se 1 (by rfl) ⟨1554641, by rfl⟩ : syracuseStep 2072855 = 3109283) B3109283
theorem B9960965 : Blo 2071435 9960965 := bbase (se 4 (by rfl) ⟨933840, by rfl⟩ : syracuseStep 9960965 = 1867681) (by norm_num)
theorem B6640643 : Blo 2071435 6640643 := bstep (se 1 (by rfl) ⟨4980482, by rfl⟩ : syracuseStep 6640643 = 9960965) B9960965
theorem B17708381 : Blo 2071435 17708381 := bstep (se 3 (by rfl) ⟨3320321, by rfl⟩ : syracuseStep 17708381 = 6640643) B6640643
theorem B11805587 : Blo 2071435 11805587 := bstep (se 1 (by rfl) ⟨8854190, by rfl⟩ : syracuseStep 11805587 = 17708381) B17708381
theorem B7870391 : Blo 2071435 7870391 := bstep (se 1 (by rfl) ⟨5902793, by rfl⟩ : syracuseStep 7870391 = 11805587) B11805587
theorem B5246927 : Blo 2071435 5246927 := bstep (se 1 (by rfl) ⟨3935195, by rfl⟩ : syracuseStep 5246927 = 7870391) B7870391
theorem B3497951 : Blo 2071435 3497951 := bstep (se 1 (by rfl) ⟨2623463, by rfl⟩ : syracuseStep 3497951 = 5246927) B5246927
theorem B2331967 : Blo 2071435 2331967 := bstep (se 1 (by rfl) ⟨1748975, by rfl⟩ : syracuseStep 2331967 = 3497951) B3497951
theorem B3109289 : Blo 2071435 3109289 := bstep (se 2 (by rfl) ⟨1165983, by rfl⟩ : syracuseStep 3109289 = 2331967) B2331967
theorem B2072859 : Blo 2071435 2072859 := bstep (se 1 (by rfl) ⟨1554644, by rfl⟩ : syracuseStep 2072859 = 3109289) B3109289
theorem B7870405 : Blo 2071435 7870405 := bbase (se 4 (by rfl) ⟨737850, by rfl⟩ : syracuseStep 7870405 = 1475701) (by norm_num)
theorem B10493873 : Blo 2071435 10493873 := bstep (se 2 (by rfl) ⟨3935202, by rfl⟩ : syracuseStep 10493873 = 7870405) B7870405
theorem B6995915 : Blo 2071435 6995915 := bstep (se 1 (by rfl) ⟨5246936, by rfl⟩ : syracuseStep 6995915 = 10493873) B10493873
theorem B4663943 : Blo 2071435 4663943 := bstep (se 1 (by rfl) ⟨3497957, by rfl⟩ : syracuseStep 4663943 = 6995915) B6995915
theorem B3109295 : Blo 2071435 3109295 := bstep (se 1 (by rfl) ⟨2331971, by rfl⟩ : syracuseStep 3109295 = 4663943) B4663943
theorem B2072863 : Blo 2071435 2072863 := bstep (se 1 (by rfl) ⟨1554647, by rfl⟩ : syracuseStep 2072863 = 3109295) B3109295
theorem B3109301 : Blo 2071435 3109301 := bbase (se 5 (by rfl) ⟨145748, by rfl⟩ : syracuseStep 3109301 = 291497) (by norm_num)
theorem B2072867 : Blo 2071435 2072867 := bstep (se 1 (by rfl) ⟨1554650, by rfl⟩ : syracuseStep 2072867 = 3109301) B3109301
theorem B5246957 : Blo 2071435 5246957 := bbase (se 3 (by rfl) ⟨983804, by rfl⟩ : syracuseStep 5246957 = 1967609) (by norm_num)
theorem B3497971 : Blo 2071435 3497971 := bstep (se 1 (by rfl) ⟨2623478, by rfl⟩ : syracuseStep 3497971 = 5246957) B5246957
theorem B4663961 : Blo 2071435 4663961 := bstep (se 2 (by rfl) ⟨1748985, by rfl⟩ : syracuseStep 4663961 = 3497971) B3497971
theorem B3109307 : Blo 2071435 3109307 := bstep (se 1 (by rfl) ⟨2331980, by rfl⟩ : syracuseStep 3109307 = 4663961) B4663961
theorem B2072871 : Blo 2071435 2072871 := bstep (se 1 (by rfl) ⟨1554653, by rfl⟩ : syracuseStep 2072871 = 3109307) B3109307
theorem B2331985 : Blo 2071435 2331985 := bbase (se 2 (by rfl) ⟨874494, by rfl⟩ : syracuseStep 2331985 = 1748989) (by norm_num)
theorem B3109313 : Blo 2071435 3109313 := bstep (se 2 (by rfl) ⟨1165992, by rfl⟩ : syracuseStep 3109313 = 2331985) B2331985
theorem B2072875 : Blo 2071435 2072875 := bstep (se 1 (by rfl) ⟨1554656, by rfl⟩ : syracuseStep 2072875 = 3109313) B3109313
theorem B2213569 : Blo 2071435 2213569 := bbase (se 2 (by rfl) ⟨830088, by rfl⟩ : syracuseStep 2213569 = 1660177) (by norm_num)
theorem B2951425 : Blo 2071435 2951425 := bstep (se 2 (by rfl) ⟨1106784, by rfl⟩ : syracuseStep 2951425 = 2213569) B2213569
theorem B3935233 : Blo 2071435 3935233 := bstep (se 2 (by rfl) ⟨1475712, by rfl⟩ : syracuseStep 3935233 = 2951425) B2951425
theorem B5246977 : Blo 2071435 5246977 := bstep (se 2 (by rfl) ⟨1967616, by rfl⟩ : syracuseStep 5246977 = 3935233) B3935233
theorem B6995969 : Blo 2071435 6995969 := bstep (se 2 (by rfl) ⟨2623488, by rfl⟩ : syracuseStep 6995969 = 5246977) B5246977
theorem B4663979 : Blo 2071435 4663979 := bstep (se 1 (by rfl) ⟨3497984, by rfl⟩ : syracuseStep 4663979 = 6995969) B6995969
theorem B3109319 : Blo 2071435 3109319 := bstep (se 1 (by rfl) ⟨2331989, by rfl⟩ : syracuseStep 3109319 = 4663979) B4663979
theorem B2072879 : Blo 2071435 2072879 := bstep (se 1 (by rfl) ⟨1554659, by rfl⟩ : syracuseStep 2072879 = 3109319) B3109319
theorem B3109325 : Blo 2071435 3109325 := bbase (se 3 (by rfl) ⟨582998, by rfl⟩ : syracuseStep 3109325 = 1165997) (by norm_num)
theorem B2072883 : Blo 2071435 2072883 := bstep (se 1 (by rfl) ⟨1554662, by rfl⟩ : syracuseStep 2072883 = 3109325) B3109325
theorem B4663997 : Blo 2071435 4663997 := bbase (se 3 (by rfl) ⟨874499, by rfl⟩ : syracuseStep 4663997 = 1748999) (by norm_num)
theorem B3109331 : Blo 2071435 3109331 := bstep (se 1 (by rfl) ⟨2331998, by rfl⟩ : syracuseStep 3109331 = 4663997) B4663997
theorem B2072887 : Blo 2071435 2072887 := bstep (se 1 (by rfl) ⟨1554665, by rfl⟩ : syracuseStep 2072887 = 3109331) B3109331
theorem B3498005 : Blo 2071435 3498005 := bbase (se 6 (by rfl) ⟨81984, by rfl⟩ : syracuseStep 3498005 = 163969) (by norm_num)
theorem B2332003 : Blo 2071435 2332003 := bstep (se 1 (by rfl) ⟨1749002, by rfl⟩ : syracuseStep 2332003 = 3498005) B3498005
theorem B3109337 : Blo 2071435 3109337 := bstep (se 2 (by rfl) ⟨1166001, by rfl⟩ : syracuseStep 3109337 = 2332003) B2332003
theorem B2072891 : Blo 2071435 2072891 := bstep (se 1 (by rfl) ⟨1554668, by rfl⟩ : syracuseStep 2072891 = 3109337) B3109337
theorem B10097045 : Blo 2071435 10097045 := bbase (se 6 (by rfl) ⟨236649, by rfl⟩ : syracuseStep 10097045 = 473299) (by norm_num)
theorem B6731363 : Blo 2071435 6731363 := bstep (se 1 (by rfl) ⟨5048522, by rfl⟩ : syracuseStep 6731363 = 10097045) B10097045
theorem B4487575 : Blo 2071435 4487575 := bstep (se 1 (by rfl) ⟨3365681, by rfl⟩ : syracuseStep 4487575 = 6731363) B6731363
theorem B5983433 : Blo 2071435 5983433 := bstep (se 2 (by rfl) ⟨2243787, by rfl⟩ : syracuseStep 5983433 = 4487575) B4487575
theorem B3988955 : Blo 2071435 3988955 := bstep (se 1 (by rfl) ⟨2991716, by rfl⟩ : syracuseStep 3988955 = 5983433) B5983433
theorem B2659303 : Blo 2071435 2659303 := bstep (se 1 (by rfl) ⟨1994477, by rfl⟩ : syracuseStep 2659303 = 3988955) B3988955
theorem B3545737 : Blo 2071435 3545737 := bstep (se 2 (by rfl) ⟨1329651, by rfl⟩ : syracuseStep 3545737 = 2659303) B2659303
theorem B18910597 : Blo 2071435 18910597 := bstep (se 4 (by rfl) ⟨1772868, by rfl⟩ : syracuseStep 18910597 = 3545737) B3545737
theorem B25214129 : Blo 2071435 25214129 := bstep (se 2 (by rfl) ⟨9455298, by rfl⟩ : syracuseStep 25214129 = 18910597) B18910597
theorem B16809419 : Blo 2071435 16809419 := bstep (se 1 (by rfl) ⟨12607064, by rfl⟩ : syracuseStep 16809419 = 25214129) B25214129
theorem B11206279 : Blo 2071435 11206279 := bstep (se 1 (by rfl) ⟨8404709, by rfl⟩ : syracuseStep 11206279 = 16809419) B16809419
theorem B14941705 : Blo 2071435 14941705 := bstep (se 2 (by rfl) ⟨5603139, by rfl⟩ : syracuseStep 14941705 = 11206279) B11206279
theorem B19922273 : Blo 2071435 19922273 := bstep (se 2 (by rfl) ⟨7470852, by rfl⟩ : syracuseStep 19922273 = 14941705) B14941705
theorem B13281515 : Blo 2071435 13281515 := bstep (se 1 (by rfl) ⟨9961136, by rfl⟩ : syracuseStep 13281515 = 19922273) B19922273
theorem B8854343 : Blo 2071435 8854343 := bstep (se 1 (by rfl) ⟨6640757, by rfl⟩ : syracuseStep 8854343 = 13281515) B13281515
theorem B5902895 : Blo 2071435 5902895 := bstep (se 1 (by rfl) ⟨4427171, by rfl⟩ : syracuseStep 5902895 = 8854343) B8854343
theorem B15741053 : Blo 2071435 15741053 := bstep (se 3 (by rfl) ⟨2951447, by rfl⟩ : syracuseStep 15741053 = 5902895) B5902895
theorem B10494035 : Blo 2071435 10494035 := bstep (se 1 (by rfl) ⟨7870526, by rfl⟩ : syracuseStep 10494035 = 15741053) B15741053
theorem B6996023 : Blo 2071435 6996023 := bstep (se 1 (by rfl) ⟨5247017, by rfl⟩ : syracuseStep 6996023 = 10494035) B10494035
theorem B4664015 : Blo 2071435 4664015 := bstep (se 1 (by rfl) ⟨3498011, by rfl⟩ : syracuseStep 4664015 = 6996023) B6996023
theorem B3109343 : Blo 2071435 3109343 := bstep (se 1 (by rfl) ⟨2332007, by rfl⟩ : syracuseStep 3109343 = 4664015) B4664015
theorem B2072895 : Blo 2071435 2072895 := bstep (se 1 (by rfl) ⟨1554671, by rfl⟩ : syracuseStep 2072895 = 3109343) B3109343
theorem B3109349 : Blo 2071435 3109349 := bbase (se 4 (by rfl) ⟨291501, by rfl⟩ : syracuseStep 3109349 = 583003) (by norm_num)
theorem B2072899 : Blo 2071435 2072899 := bstep (se 1 (by rfl) ⟨1554674, by rfl⟩ : syracuseStep 2072899 = 3109349) B3109349
theorem B11206325 : Blo 2071435 11206325 := bbase (se 5 (by rfl) ⟨525296, by rfl⟩ : syracuseStep 11206325 = 1050593) (by norm_num)
theorem B7470883 : Blo 2071435 7470883 := bstep (se 1 (by rfl) ⟨5603162, by rfl⟩ : syracuseStep 7470883 = 11206325) B11206325
theorem B9961177 : Blo 2071435 9961177 := bstep (se 2 (by rfl) ⟨3735441, by rfl⟩ : syracuseStep 9961177 = 7470883) B7470883
theorem B13281569 : Blo 2071435 13281569 := bstep (se 2 (by rfl) ⟨4980588, by rfl⟩ : syracuseStep 13281569 = 9961177) B9961177
theorem B8854379 : Blo 2071435 8854379 := bstep (se 1 (by rfl) ⟨6640784, by rfl⟩ : syracuseStep 8854379 = 13281569) B13281569
theorem B5902919 : Blo 2071435 5902919 := bstep (se 1 (by rfl) ⟨4427189, by rfl⟩ : syracuseStep 5902919 = 8854379) B8854379
theorem B3935279 : Blo 2071435 3935279 := bstep (se 1 (by rfl) ⟨2951459, by rfl⟩ : syracuseStep 3935279 = 5902919) B5902919
theorem B2623519 : Blo 2071435 2623519 := bstep (se 1 (by rfl) ⟨1967639, by rfl⟩ : syracuseStep 2623519 = 3935279) B3935279
theorem B3498025 : Blo 2071435 3498025 := bstep (se 2 (by rfl) ⟨1311759, by rfl⟩ : syracuseStep 3498025 = 2623519) B2623519
theorem B4664033 : Blo 2071435 4664033 := bstep (se 2 (by rfl) ⟨1749012, by rfl⟩ : syracuseStep 4664033 = 3498025) B3498025
theorem B3109355 : Blo 2071435 3109355 := bstep (se 1 (by rfl) ⟨2332016, by rfl⟩ : syracuseStep 3109355 = 4664033) B4664033
theorem B2072903 : Blo 2071435 2072903 := bstep (se 1 (by rfl) ⟨1554677, by rfl⟩ : syracuseStep 2072903 = 3109355) B3109355
theorem B2332021 : Blo 2071435 2332021 := bbase (se 5 (by rfl) ⟨109313, by rfl⟩ : syracuseStep 2332021 = 218627) (by norm_num)
theorem B3109361 : Blo 2071435 3109361 := bstep (se 2 (by rfl) ⟨1166010, by rfl⟩ : syracuseStep 3109361 = 2332021) B2332021
theorem B2072907 : Blo 2071435 2072907 := bstep (se 1 (by rfl) ⟨1554680, by rfl⟩ : syracuseStep 2072907 = 3109361) B3109361
theorem B2623529 : Blo 2071435 2623529 := bbase (se 2 (by rfl) ⟨983823, by rfl⟩ : syracuseStep 2623529 = 1967647) (by norm_num)
theorem B6996077 : Blo 2071435 6996077 := bstep (se 3 (by rfl) ⟨1311764, by rfl⟩ : syracuseStep 6996077 = 2623529) B2623529
theorem B4664051 : Blo 2071435 4664051 := bstep (se 1 (by rfl) ⟨3498038, by rfl⟩ : syracuseStep 4664051 = 6996077) B6996077
theorem B3109367 : Blo 2071435 3109367 := bstep (se 1 (by rfl) ⟨2332025, by rfl⟩ : syracuseStep 3109367 = 4664051) B4664051
theorem B2072911 : Blo 2071435 2072911 := bstep (se 1 (by rfl) ⟨1554683, by rfl⟩ : syracuseStep 2072911 = 3109367) B3109367
theorem B3109373 : Blo 2071435 3109373 := bbase (se 3 (by rfl) ⟨583007, by rfl⟩ : syracuseStep 3109373 = 1166015) (by norm_num)
theorem B2072915 : Blo 2071435 2072915 := bstep (se 1 (by rfl) ⟨1554686, by rfl⟩ : syracuseStep 2072915 = 3109373) B3109373
theorem B4664069 : Blo 2071435 4664069 := bbase (se 4 (by rfl) ⟨437256, by rfl⟩ : syracuseStep 4664069 = 874513) (by norm_num)
theorem B3109379 : Blo 2071435 3109379 := bstep (se 1 (by rfl) ⟨2332034, by rfl⟩ : syracuseStep 3109379 = 4664069) B4664069
theorem B2072919 : Blo 2071435 2072919 := bstep (se 1 (by rfl) ⟨1554689, by rfl⟩ : syracuseStep 2072919 = 3109379) B3109379
theorem B3935317 : Blo 2071435 3935317 := bbase (se 8 (by rfl) ⟨23058, by rfl⟩ : syracuseStep 3935317 = 46117) (by norm_num)
theorem B5247089 : Blo 2071435 5247089 := bstep (se 2 (by rfl) ⟨1967658, by rfl⟩ : syracuseStep 5247089 = 3935317) B3935317
theorem B3498059 : Blo 2071435 3498059 := bstep (se 1 (by rfl) ⟨2623544, by rfl⟩ : syracuseStep 3498059 = 5247089) B5247089
theorem B2332039 : Blo 2071435 2332039 := bstep (se 1 (by rfl) ⟨1749029, by rfl⟩ : syracuseStep 2332039 = 3498059) B3498059
theorem B3109385 : Blo 2071435 3109385 := bstep (se 2 (by rfl) ⟨1166019, by rfl⟩ : syracuseStep 3109385 = 2332039) B2332039
theorem B2072923 : Blo 2071435 2072923 := bstep (se 1 (by rfl) ⟨1554692, by rfl⟩ : syracuseStep 2072923 = 3109385) B3109385
theorem B10494197 : Blo 2071435 10494197 := bbase (se 5 (by rfl) ⟨491915, by rfl⟩ : syracuseStep 10494197 = 983831) (by norm_num)
theorem B6996131 : Blo 2071435 6996131 := bstep (se 1 (by rfl) ⟨5247098, by rfl⟩ : syracuseStep 6996131 = 10494197) B10494197
theorem B4664087 : Blo 2071435 4664087 := bstep (se 1 (by rfl) ⟨3498065, by rfl⟩ : syracuseStep 4664087 = 6996131) B6996131
theorem B3109391 : Blo 2071435 3109391 := bstep (se 1 (by rfl) ⟨2332043, by rfl⟩ : syracuseStep 3109391 = 4664087) B4664087
theorem B2072927 : Blo 2071435 2072927 := bstep (se 1 (by rfl) ⟨1554695, by rfl⟩ : syracuseStep 2072927 = 3109391) B3109391
theorem B3109397 : Blo 2071435 3109397 := bbase (se 6 (by rfl) ⟨72876, by rfl⟩ : syracuseStep 3109397 = 145753) (by norm_num)
theorem B2072931 : Blo 2071435 2072931 := bstep (se 1 (by rfl) ⟨1554698, by rfl⟩ : syracuseStep 2072931 = 3109397) B3109397
theorem B4202437 : Blo 2071435 4202437 := bbase (se 4 (by rfl) ⟨393978, by rfl⟩ : syracuseStep 4202437 = 787957) (by norm_num)
theorem B5603249 : Blo 2071435 5603249 := bstep (se 2 (by rfl) ⟨2101218, by rfl⟩ : syracuseStep 5603249 = 4202437) B4202437
theorem B3735499 : Blo 2071435 3735499 := bstep (se 1 (by rfl) ⟨2801624, by rfl⟩ : syracuseStep 3735499 = 5603249) B5603249
theorem B4980665 : Blo 2071435 4980665 := bstep (se 2 (by rfl) ⟨1867749, by rfl⟩ : syracuseStep 4980665 = 3735499) B3735499
theorem B3320443 : Blo 2071435 3320443 := bstep (se 1 (by rfl) ⟨2490332, by rfl⟩ : syracuseStep 3320443 = 4980665) B4980665
theorem B17709029 : Blo 2071435 17709029 := bstep (se 4 (by rfl) ⟨1660221, by rfl⟩ : syracuseStep 17709029 = 3320443) B3320443
theorem B11806019 : Blo 2071435 11806019 := bstep (se 1 (by rfl) ⟨8854514, by rfl⟩ : syracuseStep 11806019 = 17709029) B17709029
theorem B7870679 : Blo 2071435 7870679 := bstep (se 1 (by rfl) ⟨5903009, by rfl⟩ : syracuseStep 7870679 = 11806019) B11806019
theorem B5247119 : Blo 2071435 5247119 := bstep (se 1 (by rfl) ⟨3935339, by rfl⟩ : syracuseStep 5247119 = 7870679) B7870679
theorem B3498079 : Blo 2071435 3498079 := bstep (se 1 (by rfl) ⟨2623559, by rfl⟩ : syracuseStep 3498079 = 5247119) B5247119
theorem B4664105 : Blo 2071435 4664105 := bstep (se 2 (by rfl) ⟨1749039, by rfl⟩ : syracuseStep 4664105 = 3498079) B3498079
theorem B3109403 : Blo 2071435 3109403 := bstep (se 1 (by rfl) ⟨2332052, by rfl⟩ : syracuseStep 3109403 = 4664105) B4664105
theorem B2072935 : Blo 2071435 2072935 := bstep (se 1 (by rfl) ⟨1554701, by rfl⟩ : syracuseStep 2072935 = 3109403) B3109403
theorem B2332057 : Blo 2071435 2332057 := bbase (se 2 (by rfl) ⟨874521, by rfl⟩ : syracuseStep 2332057 = 1749043) (by norm_num)
theorem B3109409 : Blo 2071435 3109409 := bstep (se 2 (by rfl) ⟨1166028, by rfl⟩ : syracuseStep 3109409 = 2332057) B2332057
theorem B2072939 : Blo 2071435 2072939 := bstep (se 1 (by rfl) ⟨1554704, by rfl⟩ : syracuseStep 2072939 = 3109409) B3109409
theorem B7870709 : Blo 2071435 7870709 := bbase (se 5 (by rfl) ⟨368939, by rfl⟩ : syracuseStep 7870709 = 737879) (by norm_num)
theorem B5247139 : Blo 2071435 5247139 := bstep (se 1 (by rfl) ⟨3935354, by rfl⟩ : syracuseStep 5247139 = 7870709) B7870709
theorem B6996185 : Blo 2071435 6996185 := bstep (se 2 (by rfl) ⟨2623569, by rfl⟩ : syracuseStep 6996185 = 5247139) B5247139
theorem B4664123 : Blo 2071435 4664123 := bstep (se 1 (by rfl) ⟨3498092, by rfl⟩ : syracuseStep 4664123 = 6996185) B6996185
theorem B3109415 : Blo 2071435 3109415 := bstep (se 1 (by rfl) ⟨2332061, by rfl⟩ : syracuseStep 3109415 = 4664123) B4664123
theorem B2072943 : Blo 2071435 2072943 := bstep (se 1 (by rfl) ⟨1554707, by rfl⟩ : syracuseStep 2072943 = 3109415) B3109415
theorem B3109421 : Blo 2071435 3109421 := bbase (se 3 (by rfl) ⟨583016, by rfl⟩ : syracuseStep 3109421 = 1166033) (by norm_num)
theorem B2072947 : Blo 2071435 2072947 := bstep (se 1 (by rfl) ⟨1554710, by rfl⟩ : syracuseStep 2072947 = 3109421) B3109421
theorem B4664141 : Blo 2071435 4664141 := bbase (se 3 (by rfl) ⟨874526, by rfl⟩ : syracuseStep 4664141 = 1749053) (by norm_num)
theorem B3109427 : Blo 2071435 3109427 := bstep (se 1 (by rfl) ⟨2332070, by rfl⟩ : syracuseStep 3109427 = 4664141) B4664141
theorem B2072951 : Blo 2071435 2072951 := bstep (se 1 (by rfl) ⟨1554713, by rfl⟩ : syracuseStep 2072951 = 3109427) B3109427
theorem B2623585 : Blo 2071435 2623585 := bbase (se 2 (by rfl) ⟨983844, by rfl⟩ : syracuseStep 2623585 = 1967689) (by norm_num)
theorem B3498113 : Blo 2071435 3498113 := bstep (se 2 (by rfl) ⟨1311792, by rfl⟩ : syracuseStep 3498113 = 2623585) B2623585
theorem B2332075 : Blo 2071435 2332075 := bstep (se 1 (by rfl) ⟨1749056, by rfl⟩ : syracuseStep 2332075 = 3498113) B3498113
theorem B3109433 : Blo 2071435 3109433 := bstep (se 2 (by rfl) ⟨1166037, by rfl⟩ : syracuseStep 3109433 = 2332075) B2332075
theorem B2072955 : Blo 2071435 2072955 := bstep (se 1 (by rfl) ⟨1554716, by rfl⟩ : syracuseStep 2072955 = 3109433) B3109433
theorem B23612309 : Blo 2071435 23612309 := bbase (se 6 (by rfl) ⟨553413, by rfl⟩ : syracuseStep 23612309 = 1106827) (by norm_num)
theorem B15741539 : Blo 2071435 15741539 := bstep (se 1 (by rfl) ⟨11806154, by rfl⟩ : syracuseStep 15741539 = 23612309) B23612309
theorem B10494359 : Blo 2071435 10494359 := bstep (se 1 (by rfl) ⟨7870769, by rfl⟩ : syracuseStep 10494359 = 15741539) B15741539
theorem B6996239 : Blo 2071435 6996239 := bstep (se 1 (by rfl) ⟨5247179, by rfl⟩ : syracuseStep 6996239 = 10494359) B10494359
theorem B4664159 : Blo 2071435 4664159 := bstep (se 1 (by rfl) ⟨3498119, by rfl⟩ : syracuseStep 4664159 = 6996239) B6996239
theorem B3109439 : Blo 2071435 3109439 := bstep (se 1 (by rfl) ⟨2332079, by rfl⟩ : syracuseStep 3109439 = 4664159) B4664159
theorem B2072959 : Blo 2071435 2072959 := bstep (se 1 (by rfl) ⟨1554719, by rfl⟩ : syracuseStep 2072959 = 3109439) B3109439
theorem B3109445 : Blo 2071435 3109445 := bbase (se 4 (by rfl) ⟨291510, by rfl⟩ : syracuseStep 3109445 = 583021) (by norm_num)
theorem B2072963 : Blo 2071435 2072963 := bstep (se 1 (by rfl) ⟨1554722, by rfl⟩ : syracuseStep 2072963 = 3109445) B3109445
theorem B3498133 : Blo 2071435 3498133 := bbase (se 6 (by rfl) ⟨81987, by rfl⟩ : syracuseStep 3498133 = 163975) (by norm_num)
theorem B4664177 : Blo 2071435 4664177 := bstep (se 2 (by rfl) ⟨1749066, by rfl⟩ : syracuseStep 4664177 = 3498133) B3498133
theorem B3109451 : Blo 2071435 3109451 := bstep (se 1 (by rfl) ⟨2332088, by rfl⟩ : syracuseStep 3109451 = 4664177) B4664177
theorem B2072967 : Blo 2071435 2072967 := bstep (se 1 (by rfl) ⟨1554725, by rfl⟩ : syracuseStep 2072967 = 3109451) B3109451
theorem B2332093 : Blo 2071435 2332093 := bbase (se 3 (by rfl) ⟨437267, by rfl⟩ : syracuseStep 2332093 = 874535) (by norm_num)
theorem B3109457 : Blo 2071435 3109457 := bstep (se 2 (by rfl) ⟨1166046, by rfl⟩ : syracuseStep 3109457 = 2332093) B2332093
theorem B2072971 : Blo 2071435 2072971 := bstep (se 1 (by rfl) ⟨1554728, by rfl⟩ : syracuseStep 2072971 = 3109457) B3109457
theorem B6996293 : Blo 2071435 6996293 := bbase (se 4 (by rfl) ⟨655902, by rfl⟩ : syracuseStep 6996293 = 1311805) (by norm_num)
theorem B4664195 : Blo 2071435 4664195 := bstep (se 1 (by rfl) ⟨3498146, by rfl⟩ : syracuseStep 4664195 = 6996293) B6996293
theorem B3109463 : Blo 2071435 3109463 := bstep (se 1 (by rfl) ⟨2332097, by rfl⟩ : syracuseStep 3109463 = 4664195) B4664195
theorem B2072975 : Blo 2071435 2072975 := bstep (se 1 (by rfl) ⟨1554731, by rfl⟩ : syracuseStep 2072975 = 3109463) B3109463
theorem B3109469 : Blo 2071435 3109469 := bbase (se 3 (by rfl) ⟨583025, by rfl⟩ : syracuseStep 3109469 = 1166051) (by norm_num)
theorem B2072979 : Blo 2071435 2072979 := bstep (se 1 (by rfl) ⟨1554734, by rfl⟩ : syracuseStep 2072979 = 3109469) B3109469
theorem B4664213 : Blo 2071435 4664213 := bbase (se 6 (by rfl) ⟨109317, by rfl⟩ : syracuseStep 4664213 = 218635) (by norm_num)
theorem B3109475 : Blo 2071435 3109475 := bstep (se 1 (by rfl) ⟨2332106, by rfl⟩ : syracuseStep 3109475 = 4664213) B4664213
theorem B2072983 : Blo 2071435 2072983 := bstep (se 1 (by rfl) ⟨1554737, by rfl⟩ : syracuseStep 2072983 = 3109475) B3109475
theorem B12954005 : Blo 2071435 12954005 := bbase (se 6 (by rfl) ⟨303609, by rfl⟩ : syracuseStep 12954005 = 607219) (by norm_num)
theorem B8636003 : Blo 2071435 8636003 := bstep (se 1 (by rfl) ⟨6477002, by rfl⟩ : syracuseStep 8636003 = 12954005) B12954005
theorem B5757335 : Blo 2071435 5757335 := bstep (se 1 (by rfl) ⟨4318001, by rfl⟩ : syracuseStep 5757335 = 8636003) B8636003
theorem B3838223 : Blo 2071435 3838223 := bstep (se 1 (by rfl) ⟨2878667, by rfl⟩ : syracuseStep 3838223 = 5757335) B5757335
theorem B10235261 : Blo 2071435 10235261 := bstep (se 3 (by rfl) ⟨1919111, by rfl⟩ : syracuseStep 10235261 = 3838223) B3838223
theorem B6823507 : Blo 2071435 6823507 := bstep (se 1 (by rfl) ⟨5117630, by rfl⟩ : syracuseStep 6823507 = 10235261) B10235261
theorem B9098009 : Blo 2071435 9098009 := bstep (se 2 (by rfl) ⟨3411753, by rfl⟩ : syracuseStep 9098009 = 6823507) B6823507
theorem B6065339 : Blo 2071435 6065339 := bstep (se 1 (by rfl) ⟨4549004, by rfl⟩ : syracuseStep 6065339 = 9098009) B9098009
theorem B16174237 : Blo 2071435 16174237 := bstep (se 3 (by rfl) ⟨3032669, by rfl⟩ : syracuseStep 16174237 = 6065339) B6065339
theorem B21565649 : Blo 2071435 21565649 := bstep (se 2 (by rfl) ⟨8087118, by rfl⟩ : syracuseStep 21565649 = 16174237) B16174237
theorem B14377099 : Blo 2071435 14377099 := bstep (se 1 (by rfl) ⟨10782824, by rfl⟩ : syracuseStep 14377099 = 21565649) B21565649
theorem B19169465 : Blo 2071435 19169465 := bstep (se 2 (by rfl) ⟨7188549, by rfl⟩ : syracuseStep 19169465 = 14377099) B14377099
theorem B51118573 : Blo 2071435 51118573 := bstep (se 3 (by rfl) ⟨9584732, by rfl⟩ : syracuseStep 51118573 = 19169465) B19169465
theorem B68158097 : Blo 2071435 68158097 := bstep (se 2 (by rfl) ⟨25559286, by rfl⟩ : syracuseStep 68158097 = 51118573) B51118573
theorem B45438731 : Blo 2071435 45438731 := bstep (se 1 (by rfl) ⟨34079048, by rfl⟩ : syracuseStep 45438731 = 68158097) B68158097
theorem B30292487 : Blo 2071435 30292487 := bstep (se 1 (by rfl) ⟨22719365, by rfl⟩ : syracuseStep 30292487 = 45438731) B45438731
theorem B20194991 : Blo 2071435 20194991 := bstep (se 1 (by rfl) ⟨15146243, by rfl⟩ : syracuseStep 20194991 = 30292487) B30292487
theorem B13463327 : Blo 2071435 13463327 := bstep (se 1 (by rfl) ⟨10097495, by rfl⟩ : syracuseStep 13463327 = 20194991) B20194991
theorem B8975551 : Blo 2071435 8975551 := bstep (se 1 (by rfl) ⟨6731663, by rfl⟩ : syracuseStep 8975551 = 13463327) B13463327
theorem B11967401 : Blo 2071435 11967401 := bstep (se 2 (by rfl) ⟨4487775, by rfl⟩ : syracuseStep 11967401 = 8975551) B8975551
theorem B7978267 : Blo 2071435 7978267 := bstep (se 1 (by rfl) ⟨5983700, by rfl⟩ : syracuseStep 7978267 = 11967401) B11967401
theorem B10637689 : Blo 2071435 10637689 := bstep (se 2 (by rfl) ⟨3989133, by rfl⟩ : syracuseStep 10637689 = 7978267) B7978267
theorem B14183585 : Blo 2071435 14183585 := bstep (se 2 (by rfl) ⟨5318844, by rfl⟩ : syracuseStep 14183585 = 10637689) B10637689
theorem B9455723 : Blo 2071435 9455723 := bstep (se 1 (by rfl) ⟨7091792, by rfl⟩ : syracuseStep 9455723 = 14183585) B14183585
theorem B6303815 : Blo 2071435 6303815 := bstep (se 1 (by rfl) ⟨4727861, by rfl⟩ : syracuseStep 6303815 = 9455723) B9455723
theorem B4202543 : Blo 2071435 4202543 := bstep (se 1 (by rfl) ⟨3151907, by rfl⟩ : syracuseStep 4202543 = 6303815) B6303815
theorem B11206781 : Blo 2071435 11206781 := bstep (se 3 (by rfl) ⟨2101271, by rfl⟩ : syracuseStep 11206781 = 4202543) B4202543
theorem B7471187 : Blo 2071435 7471187 := bstep (se 1 (by rfl) ⟨5603390, by rfl⟩ : syracuseStep 7471187 = 11206781) B11206781
theorem B4980791 : Blo 2071435 4980791 := bstep (se 1 (by rfl) ⟨3735593, by rfl⟩ : syracuseStep 4980791 = 7471187) B7471187
theorem B3320527 : Blo 2071435 3320527 := bstep (se 1 (by rfl) ⟨2490395, by rfl⟩ : syracuseStep 3320527 = 4980791) B4980791
theorem B4427369 : Blo 2071435 4427369 := bstep (se 2 (by rfl) ⟨1660263, by rfl⟩ : syracuseStep 4427369 = 3320527) B3320527
theorem B2951579 : Blo 2071435 2951579 := bstep (se 1 (by rfl) ⟨2213684, by rfl⟩ : syracuseStep 2951579 = 4427369) B4427369
theorem B7870877 : Blo 2071435 7870877 := bstep (se 3 (by rfl) ⟨1475789, by rfl⟩ : syracuseStep 7870877 = 2951579) B2951579
theorem B5247251 : Blo 2071435 5247251 := bstep (se 1 (by rfl) ⟨3935438, by rfl⟩ : syracuseStep 5247251 = 7870877) B7870877
theorem B3498167 : Blo 2071435 3498167 := bstep (se 1 (by rfl) ⟨2623625, by rfl⟩ : syracuseStep 3498167 = 5247251) B5247251
theorem B2332111 : Blo 2071435 2332111 := bstep (se 1 (by rfl) ⟨1749083, by rfl⟩ : syracuseStep 2332111 = 3498167) B3498167
theorem B3109481 : Blo 2071435 3109481 := bstep (se 2 (by rfl) ⟨1166055, by rfl⟩ : syracuseStep 3109481 = 2332111) B2332111
theorem B2072987 : Blo 2071435 2072987 := bstep (se 1 (by rfl) ⟨1554740, by rfl⟩ : syracuseStep 2072987 = 3109481) B3109481
theorem B2839925 : Blo 2071435 2839925 := bbase (se 5 (by rfl) ⟨133121, by rfl⟩ : syracuseStep 2839925 = 266243) (by norm_num)
theorem B7573133 : Blo 2071435 7573133 := bstep (se 3 (by rfl) ⟨1419962, by rfl⟩ : syracuseStep 7573133 = 2839925) B2839925
theorem B20195021 : Blo 2071435 20195021 := bstep (se 3 (by rfl) ⟨3786566, by rfl⟩ : syracuseStep 20195021 = 7573133) B7573133
theorem B13463347 : Blo 2071435 13463347 := bstep (se 1 (by rfl) ⟨10097510, by rfl⟩ : syracuseStep 13463347 = 20195021) B20195021
theorem B17951129 : Blo 2071435 17951129 := bstep (se 2 (by rfl) ⟨6731673, by rfl⟩ : syracuseStep 17951129 = 13463347) B13463347
theorem B11967419 : Blo 2071435 11967419 := bstep (se 1 (by rfl) ⟨8975564, by rfl⟩ : syracuseStep 11967419 = 17951129) B17951129
theorem B7978279 : Blo 2071435 7978279 := bstep (se 1 (by rfl) ⟨5983709, by rfl⟩ : syracuseStep 7978279 = 11967419) B11967419
theorem B10637705 : Blo 2071435 10637705 := bstep (se 2 (by rfl) ⟨3989139, by rfl⟩ : syracuseStep 10637705 = 7978279) B7978279
theorem B7091803 : Blo 2071435 7091803 := bstep (se 1 (by rfl) ⟨5318852, by rfl⟩ : syracuseStep 7091803 = 10637705) B10637705
theorem B37822949 : Blo 2071435 37822949 := bstep (se 4 (by rfl) ⟨3545901, by rfl⟩ : syracuseStep 37822949 = 7091803) B7091803
theorem B25215299 : Blo 2071435 25215299 := bstep (se 1 (by rfl) ⟨18911474, by rfl⟩ : syracuseStep 25215299 = 37822949) B37822949
theorem B16810199 : Blo 2071435 16810199 := bstep (se 1 (by rfl) ⟨12607649, by rfl⟩ : syracuseStep 16810199 = 25215299) B25215299
theorem B11206799 : Blo 2071435 11206799 := bstep (se 1 (by rfl) ⟨8405099, by rfl⟩ : syracuseStep 11206799 = 16810199) B16810199
theorem B7471199 : Blo 2071435 7471199 := bstep (se 1 (by rfl) ⟨5603399, by rfl⟩ : syracuseStep 7471199 = 11206799) B11206799
theorem B4980799 : Blo 2071435 4980799 := bstep (se 1 (by rfl) ⟨3735599, by rfl⟩ : syracuseStep 4980799 = 7471199) B7471199
theorem B6641065 : Blo 2071435 6641065 := bstep (se 2 (by rfl) ⟨2490399, by rfl⟩ : syracuseStep 6641065 = 4980799) B4980799
theorem B8854753 : Blo 2071435 8854753 := bstep (se 2 (by rfl) ⟨3320532, by rfl⟩ : syracuseStep 8854753 = 6641065) B6641065
theorem B11806337 : Blo 2071435 11806337 := bstep (se 2 (by rfl) ⟨4427376, by rfl⟩ : syracuseStep 11806337 = 8854753) B8854753
theorem B7870891 : Blo 2071435 7870891 := bstep (se 1 (by rfl) ⟨5903168, by rfl⟩ : syracuseStep 7870891 = 11806337) B11806337
theorem B10494521 : Blo 2071435 10494521 := bstep (se 2 (by rfl) ⟨3935445, by rfl⟩ : syracuseStep 10494521 = 7870891) B7870891
theorem B6996347 : Blo 2071435 6996347 := bstep (se 1 (by rfl) ⟨5247260, by rfl⟩ : syracuseStep 6996347 = 10494521) B10494521
theorem B4664231 : Blo 2071435 4664231 := bstep (se 1 (by rfl) ⟨3498173, by rfl⟩ : syracuseStep 4664231 = 6996347) B6996347
theorem B3109487 : Blo 2071435 3109487 := bstep (se 1 (by rfl) ⟨2332115, by rfl⟩ : syracuseStep 3109487 = 4664231) B4664231
theorem B2072991 : Blo 2071435 2072991 := bstep (se 1 (by rfl) ⟨1554743, by rfl⟩ : syracuseStep 2072991 = 3109487) B3109487
theorem B3109493 : Blo 2071435 3109493 := bbase (se 5 (by rfl) ⟨145757, by rfl⟩ : syracuseStep 3109493 = 291515) (by norm_num)
theorem B2072995 : Blo 2071435 2072995 := bstep (se 1 (by rfl) ⟨1554746, by rfl⟩ : syracuseStep 2072995 = 3109493) B3109493
theorem B3935461 : Blo 2071435 3935461 := bbase (se 4 (by rfl) ⟨368949, by rfl⟩ : syracuseStep 3935461 = 737899) (by norm_num)
theorem B5247281 : Blo 2071435 5247281 := bstep (se 2 (by rfl) ⟨1967730, by rfl⟩ : syracuseStep 5247281 = 3935461) B3935461
theorem B3498187 : Blo 2071435 3498187 := bstep (se 1 (by rfl) ⟨2623640, by rfl⟩ : syracuseStep 3498187 = 5247281) B5247281
theorem B4664249 : Blo 2071435 4664249 := bstep (se 2 (by rfl) ⟨1749093, by rfl⟩ : syracuseStep 4664249 = 3498187) B3498187
theorem B3109499 : Blo 2071435 3109499 := bstep (se 1 (by rfl) ⟨2332124, by rfl⟩ : syracuseStep 3109499 = 4664249) B4664249
theorem B2072999 : Blo 2071435 2072999 := bstep (se 1 (by rfl) ⟨1554749, by rfl⟩ : syracuseStep 2072999 = 3109499) B3109499
theorem B2332129 : Blo 2071435 2332129 := bbase (se 2 (by rfl) ⟨874548, by rfl⟩ : syracuseStep 2332129 = 1749097) (by norm_num)
theorem B3109505 : Blo 2071435 3109505 := bstep (se 2 (by rfl) ⟨1166064, by rfl⟩ : syracuseStep 3109505 = 2332129) B2332129
theorem B2073003 : Blo 2071435 2073003 := bstep (se 1 (by rfl) ⟨1554752, by rfl⟩ : syracuseStep 2073003 = 3109505) B3109505
theorem B5247301 : Blo 2071435 5247301 := bbase (se 4 (by rfl) ⟨491934, by rfl⟩ : syracuseStep 5247301 = 983869) (by norm_num)
theorem B6996401 : Blo 2071435 6996401 := bstep (se 2 (by rfl) ⟨2623650, by rfl⟩ : syracuseStep 6996401 = 5247301) B5247301
theorem B4664267 : Blo 2071435 4664267 := bstep (se 1 (by rfl) ⟨3498200, by rfl⟩ : syracuseStep 4664267 = 6996401) B6996401
theorem B3109511 : Blo 2071435 3109511 := bstep (se 1 (by rfl) ⟨2332133, by rfl⟩ : syracuseStep 3109511 = 4664267) B4664267
theorem B2073007 : Blo 2071435 2073007 := bstep (se 1 (by rfl) ⟨1554755, by rfl⟩ : syracuseStep 2073007 = 3109511) B3109511
theorem B3109517 : Blo 2071435 3109517 := bbase (se 3 (by rfl) ⟨583034, by rfl⟩ : syracuseStep 3109517 = 1166069) (by norm_num)
theorem B2073011 : Blo 2071435 2073011 := bstep (se 1 (by rfl) ⟨1554758, by rfl⟩ : syracuseStep 2073011 = 3109517) B3109517
theorem B4664285 : Blo 2071435 4664285 := bbase (se 3 (by rfl) ⟨874553, by rfl⟩ : syracuseStep 4664285 = 1749107) (by norm_num)
theorem B3109523 : Blo 2071435 3109523 := bstep (se 1 (by rfl) ⟨2332142, by rfl⟩ : syracuseStep 3109523 = 4664285) B4664285
theorem B2073015 : Blo 2071435 2073015 := bstep (se 1 (by rfl) ⟨1554761, by rfl⟩ : syracuseStep 2073015 = 3109523) B3109523
theorem B3498221 : Blo 2071435 3498221 := bbase (se 3 (by rfl) ⟨655916, by rfl⟩ : syracuseStep 3498221 = 1311833) (by norm_num)
theorem B2332147 : Blo 2071435 2332147 := bstep (se 1 (by rfl) ⟨1749110, by rfl⟩ : syracuseStep 2332147 = 3498221) B3498221
theorem B3109529 : Blo 2071435 3109529 := bstep (se 2 (by rfl) ⟨1166073, by rfl⟩ : syracuseStep 3109529 = 2332147) B2332147
theorem B2073019 : Blo 2071435 2073019 := bstep (se 1 (by rfl) ⟨1554764, by rfl⟩ : syracuseStep 2073019 = 3109529) B3109529
theorem B3545957 : Blo 2071435 3545957 := bbase (se 4 (by rfl) ⟨332433, by rfl⟩ : syracuseStep 3545957 = 664867) (by norm_num)
theorem B2363971 : Blo 2071435 2363971 := bstep (se 1 (by rfl) ⟨1772978, by rfl⟩ : syracuseStep 2363971 = 3545957) B3545957
theorem B3151961 : Blo 2071435 3151961 := bstep (se 2 (by rfl) ⟨1181985, by rfl⟩ : syracuseStep 3151961 = 2363971) B2363971
theorem B2101307 : Blo 2071435 2101307 := bstep (se 1 (by rfl) ⟨1575980, by rfl⟩ : syracuseStep 2101307 = 3151961) B3151961
theorem B22413941 : Blo 2071435 22413941 := bstep (se 5 (by rfl) ⟨1050653, by rfl⟩ : syracuseStep 22413941 = 2101307) B2101307
theorem B14942627 : Blo 2071435 14942627 := bstep (se 1 (by rfl) ⟨11206970, by rfl⟩ : syracuseStep 14942627 = 22413941) B22413941
theorem B9961751 : Blo 2071435 9961751 := bstep (se 1 (by rfl) ⟨7471313, by rfl⟩ : syracuseStep 9961751 = 14942627) B14942627
theorem B26564669 : Blo 2071435 26564669 := bstep (se 3 (by rfl) ⟨4980875, by rfl⟩ : syracuseStep 26564669 = 9961751) B9961751
theorem B17709779 : Blo 2071435 17709779 := bstep (se 1 (by rfl) ⟨13282334, by rfl⟩ : syracuseStep 17709779 = 26564669) B26564669
theorem B11806519 : Blo 2071435 11806519 := bstep (se 1 (by rfl) ⟨8854889, by rfl⟩ : syracuseStep 11806519 = 17709779) B17709779
theorem B15742025 : Blo 2071435 15742025 := bstep (se 2 (by rfl) ⟨5903259, by rfl⟩ : syracuseStep 15742025 = 11806519) B11806519
theorem B10494683 : Blo 2071435 10494683 := bstep (se 1 (by rfl) ⟨7871012, by rfl⟩ : syracuseStep 10494683 = 15742025) B15742025
theorem B6996455 : Blo 2071435 6996455 := bstep (se 1 (by rfl) ⟨5247341, by rfl⟩ : syracuseStep 6996455 = 10494683) B10494683
theorem B4664303 : Blo 2071435 4664303 := bstep (se 1 (by rfl) ⟨3498227, by rfl⟩ : syracuseStep 4664303 = 6996455) B6996455
theorem B3109535 : Blo 2071435 3109535 := bstep (se 1 (by rfl) ⟨2332151, by rfl⟩ : syracuseStep 3109535 = 4664303) B4664303
theorem B2073023 : Blo 2071435 2073023 := bstep (se 1 (by rfl) ⟨1554767, by rfl⟩ : syracuseStep 2073023 = 3109535) B3109535
theorem B3109541 : Blo 2071435 3109541 := bbase (se 4 (by rfl) ⟨291519, by rfl⟩ : syracuseStep 3109541 = 583039) (by norm_num)
theorem B2073027 : Blo 2071435 2073027 := bstep (se 1 (by rfl) ⟨1554770, by rfl⟩ : syracuseStep 2073027 = 3109541) B3109541
theorem B2623681 : Blo 2071435 2623681 := bbase (se 2 (by rfl) ⟨983880, by rfl⟩ : syracuseStep 2623681 = 1967761) (by norm_num)
theorem B3498241 : Blo 2071435 3498241 := bstep (se 2 (by rfl) ⟨1311840, by rfl⟩ : syracuseStep 3498241 = 2623681) B2623681
theorem B4664321 : Blo 2071435 4664321 := bstep (se 2 (by rfl) ⟨1749120, by rfl⟩ : syracuseStep 4664321 = 3498241) B3498241
theorem B3109547 : Blo 2071435 3109547 := bstep (se 1 (by rfl) ⟨2332160, by rfl⟩ : syracuseStep 3109547 = 4664321) B4664321
theorem B2073031 : Blo 2071435 2073031 := bstep (se 1 (by rfl) ⟨1554773, by rfl⟩ : syracuseStep 2073031 = 3109547) B3109547
theorem B2332165 : Blo 2071435 2332165 := bbase (se 4 (by rfl) ⟨218640, by rfl⟩ : syracuseStep 2332165 = 437281) (by norm_num)
theorem B3109553 : Blo 2071435 3109553 := bstep (se 2 (by rfl) ⟨1166082, by rfl⟩ : syracuseStep 3109553 = 2332165) B2332165
theorem B2073035 : Blo 2071435 2073035 := bstep (se 1 (by rfl) ⟨1554776, by rfl⟩ : syracuseStep 2073035 = 3109553) B3109553
theorem B2951653 : Blo 2071435 2951653 := bbase (se 4 (by rfl) ⟨276717, by rfl⟩ : syracuseStep 2951653 = 553435) (by norm_num)
theorem B3935537 : Blo 2071435 3935537 := bstep (se 2 (by rfl) ⟨1475826, by rfl⟩ : syracuseStep 3935537 = 2951653) B2951653
theorem B2623691 : Blo 2071435 2623691 := bstep (se 1 (by rfl) ⟨1967768, by rfl⟩ : syracuseStep 2623691 = 3935537) B3935537
theorem B6996509 : Blo 2071435 6996509 := bstep (se 3 (by rfl) ⟨1311845, by rfl⟩ : syracuseStep 6996509 = 2623691) B2623691
theorem B4664339 : Blo 2071435 4664339 := bstep (se 1 (by rfl) ⟨3498254, by rfl⟩ : syracuseStep 4664339 = 6996509) B6996509
theorem B3109559 : Blo 2071435 3109559 := bstep (se 1 (by rfl) ⟨2332169, by rfl⟩ : syracuseStep 3109559 = 4664339) B4664339
theorem B2073039 : Blo 2071435 2073039 := bstep (se 1 (by rfl) ⟨1554779, by rfl⟩ : syracuseStep 2073039 = 3109559) B3109559
theorem B3109565 : Blo 2071435 3109565 := bbase (se 3 (by rfl) ⟨583043, by rfl⟩ : syracuseStep 3109565 = 1166087) (by norm_num)
theorem B2073043 : Blo 2071435 2073043 := bstep (se 1 (by rfl) ⟨1554782, by rfl⟩ : syracuseStep 2073043 = 3109565) B3109565
theorem B4664357 : Blo 2071435 4664357 := bbase (se 4 (by rfl) ⟨437283, by rfl⟩ : syracuseStep 4664357 = 874567) (by norm_num)
theorem B3109571 : Blo 2071435 3109571 := bstep (se 1 (by rfl) ⟨2332178, by rfl⟩ : syracuseStep 3109571 = 4664357) B4664357
theorem B2073047 : Blo 2071435 2073047 := bstep (se 1 (by rfl) ⟨1554785, by rfl⟩ : syracuseStep 2073047 = 3109571) B3109571
theorem B5247413 : Blo 2071435 5247413 := bbase (se 5 (by rfl) ⟨245972, by rfl⟩ : syracuseStep 5247413 = 491945) (by norm_num)
theorem B3498275 : Blo 2071435 3498275 := bstep (se 1 (by rfl) ⟨2623706, by rfl⟩ : syracuseStep 3498275 = 5247413) B5247413
theorem B2332183 : Blo 2071435 2332183 := bstep (se 1 (by rfl) ⟨1749137, by rfl⟩ : syracuseStep 2332183 = 3498275) B3498275
theorem B3109577 : Blo 2071435 3109577 := bstep (se 2 (by rfl) ⟨1166091, by rfl⟩ : syracuseStep 3109577 = 2332183) B2332183
theorem B2073051 : Blo 2071435 2073051 := bstep (se 1 (by rfl) ⟨1554788, by rfl⟩ : syracuseStep 2073051 = 3109577) B3109577
theorem B5603573 : Blo 2071435 5603573 := bbase (se 5 (by rfl) ⟨262667, by rfl⟩ : syracuseStep 5603573 = 525335) (by norm_num)
theorem B3735715 : Blo 2071435 3735715 := bstep (se 1 (by rfl) ⟨2801786, by rfl⟩ : syracuseStep 3735715 = 5603573) B5603573
theorem B4980953 : Blo 2071435 4980953 := bstep (se 2 (by rfl) ⟨1867857, by rfl⟩ : syracuseStep 4980953 = 3735715) B3735715
theorem B13282541 : Blo 2071435 13282541 := bstep (se 3 (by rfl) ⟨2490476, by rfl⟩ : syracuseStep 13282541 = 4980953) B4980953
theorem B8855027 : Blo 2071435 8855027 := bstep (se 1 (by rfl) ⟨6641270, by rfl⟩ : syracuseStep 8855027 = 13282541) B13282541
theorem B5903351 : Blo 2071435 5903351 := bstep (se 1 (by rfl) ⟨4427513, by rfl⟩ : syracuseStep 5903351 = 8855027) B8855027
theorem B3935567 : Blo 2071435 3935567 := bstep (se 1 (by rfl) ⟨2951675, by rfl⟩ : syracuseStep 3935567 = 5903351) B5903351
theorem B10494845 : Blo 2071435 10494845 := bstep (se 3 (by rfl) ⟨1967783, by rfl⟩ : syracuseStep 10494845 = 3935567) B3935567
theorem B6996563 : Blo 2071435 6996563 := bstep (se 1 (by rfl) ⟨5247422, by rfl⟩ : syracuseStep 6996563 = 10494845) B10494845
theorem B4664375 : Blo 2071435 4664375 := bstep (se 1 (by rfl) ⟨3498281, by rfl⟩ : syracuseStep 4664375 = 6996563) B6996563
theorem B3109583 : Blo 2071435 3109583 := bstep (se 1 (by rfl) ⟨2332187, by rfl⟩ : syracuseStep 3109583 = 4664375) B4664375
theorem B2073055 : Blo 2071435 2073055 := bstep (se 1 (by rfl) ⟨1554791, by rfl⟩ : syracuseStep 2073055 = 3109583) B3109583
theorem B3109589 : Blo 2071435 3109589 := bbase (se 7 (by rfl) ⟨36440, by rfl⟩ : syracuseStep 3109589 = 72881) (by norm_num)
theorem B2073059 : Blo 2071435 2073059 := bstep (se 1 (by rfl) ⟨1554794, by rfl⟩ : syracuseStep 2073059 = 3109589) B3109589
theorem B4980973 : Blo 2071435 4980973 := bbase (se 3 (by rfl) ⟨933932, by rfl⟩ : syracuseStep 4980973 = 1867865) (by norm_num)
theorem B6641297 : Blo 2071435 6641297 := bstep (se 2 (by rfl) ⟨2490486, by rfl⟩ : syracuseStep 6641297 = 4980973) B4980973
theorem B4427531 : Blo 2071435 4427531 := bstep (se 1 (by rfl) ⟨3320648, by rfl⟩ : syracuseStep 4427531 = 6641297) B6641297
theorem B2951687 : Blo 2071435 2951687 := bstep (se 1 (by rfl) ⟨2213765, by rfl⟩ : syracuseStep 2951687 = 4427531) B4427531
theorem B7871165 : Blo 2071435 7871165 := bstep (se 3 (by rfl) ⟨1475843, by rfl⟩ : syracuseStep 7871165 = 2951687) B2951687
theorem B5247443 : Blo 2071435 5247443 := bstep (se 1 (by rfl) ⟨3935582, by rfl⟩ : syracuseStep 5247443 = 7871165) B7871165
theorem B3498295 : Blo 2071435 3498295 := bstep (se 1 (by rfl) ⟨2623721, by rfl⟩ : syracuseStep 3498295 = 5247443) B5247443
theorem B4664393 : Blo 2071435 4664393 := bstep (se 2 (by rfl) ⟨1749147, by rfl⟩ : syracuseStep 4664393 = 3498295) B3498295
theorem B3109595 : Blo 2071435 3109595 := bstep (se 1 (by rfl) ⟨2332196, by rfl⟩ : syracuseStep 3109595 = 4664393) B4664393
theorem B2073063 : Blo 2071435 2073063 := bstep (se 1 (by rfl) ⟨1554797, by rfl⟩ : syracuseStep 2073063 = 3109595) B3109595
theorem B2332201 : Blo 2071435 2332201 := bbase (se 2 (by rfl) ⟨874575, by rfl⟩ : syracuseStep 2332201 = 1749151) (by norm_num)
theorem B3109601 : Blo 2071435 3109601 := bstep (se 2 (by rfl) ⟨1166100, by rfl⟩ : syracuseStep 3109601 = 2332201) B2332201
theorem B2073067 : Blo 2071435 2073067 := bstep (se 1 (by rfl) ⟨1554800, by rfl⟩ : syracuseStep 2073067 = 3109601) B3109601
theorem B3989293 : Blo 2071435 3989293 := bbase (se 3 (by rfl) ⟨747992, by rfl⟩ : syracuseStep 3989293 = 1495985) (by norm_num)
theorem B85104917 : Blo 2071435 85104917 := bstep (se 6 (by rfl) ⟨1994646, by rfl⟩ : syracuseStep 85104917 = 3989293) B3989293
theorem B56736611 : Blo 2071435 56736611 := bstep (se 1 (by rfl) ⟨42552458, by rfl⟩ : syracuseStep 56736611 = 85104917) B85104917
theorem B37824407 : Blo 2071435 37824407 := bstep (se 1 (by rfl) ⟨28368305, by rfl⟩ : syracuseStep 37824407 = 56736611) B56736611
theorem B25216271 : Blo 2071435 25216271 := bstep (se 1 (by rfl) ⟨18912203, by rfl⟩ : syracuseStep 25216271 = 37824407) B37824407
theorem B16810847 : Blo 2071435 16810847 := bstep (se 1 (by rfl) ⟨12608135, by rfl⟩ : syracuseStep 16810847 = 25216271) B25216271
theorem B11207231 : Blo 2071435 11207231 := bstep (se 1 (by rfl) ⟨8405423, by rfl⟩ : syracuseStep 11207231 = 16810847) B16810847
theorem B7471487 : Blo 2071435 7471487 := bstep (se 1 (by rfl) ⟨5603615, by rfl⟩ : syracuseStep 7471487 = 11207231) B11207231
theorem B19923965 : Blo 2071435 19923965 := bstep (se 3 (by rfl) ⟨3735743, by rfl⟩ : syracuseStep 19923965 = 7471487) B7471487
theorem B13282643 : Blo 2071435 13282643 := bstep (se 1 (by rfl) ⟨9961982, by rfl⟩ : syracuseStep 13282643 = 19923965) B19923965
theorem B8855095 : Blo 2071435 8855095 := bstep (se 1 (by rfl) ⟨6641321, by rfl⟩ : syracuseStep 8855095 = 13282643) B13282643
theorem B11806793 : Blo 2071435 11806793 := bstep (se 2 (by rfl) ⟨4427547, by rfl⟩ : syracuseStep 11806793 = 8855095) B8855095
theorem B7871195 : Blo 2071435 7871195 := bstep (se 1 (by rfl) ⟨5903396, by rfl⟩ : syracuseStep 7871195 = 11806793) B11806793
theorem B5247463 : Blo 2071435 5247463 := bstep (se 1 (by rfl) ⟨3935597, by rfl⟩ : syracuseStep 5247463 = 7871195) B7871195
theorem B6996617 : Blo 2071435 6996617 := bstep (se 2 (by rfl) ⟨2623731, by rfl⟩ : syracuseStep 6996617 = 5247463) B5247463
theorem B4664411 : Blo 2071435 4664411 := bstep (se 1 (by rfl) ⟨3498308, by rfl⟩ : syracuseStep 4664411 = 6996617) B6996617
theorem B3109607 : Blo 2071435 3109607 := bstep (se 1 (by rfl) ⟨2332205, by rfl⟩ : syracuseStep 3109607 = 4664411) B4664411
theorem B2073071 : Blo 2071435 2073071 := bstep (se 1 (by rfl) ⟨1554803, by rfl⟩ : syracuseStep 2073071 = 3109607) B3109607
theorem B3109613 : Blo 2071435 3109613 := bbase (se 3 (by rfl) ⟨583052, by rfl⟩ : syracuseStep 3109613 = 1166105) (by norm_num)
theorem B2073075 : Blo 2071435 2073075 := bstep (se 1 (by rfl) ⟨1554806, by rfl⟩ : syracuseStep 2073075 = 3109613) B3109613
theorem B4664429 : Blo 2071435 4664429 := bbase (se 3 (by rfl) ⟨874580, by rfl⟩ : syracuseStep 4664429 = 1749161) (by norm_num)
theorem B3109619 : Blo 2071435 3109619 := bstep (se 1 (by rfl) ⟨2332214, by rfl⟩ : syracuseStep 3109619 = 4664429) B4664429
theorem B2073079 : Blo 2071435 2073079 := bstep (se 1 (by rfl) ⟨1554809, by rfl⟩ : syracuseStep 2073079 = 3109619) B3109619
theorem B3935621 : Blo 2071435 3935621 := bbase (se 4 (by rfl) ⟨368964, by rfl⟩ : syracuseStep 3935621 = 737929) (by norm_num)
theorem B2623747 : Blo 2071435 2623747 := bstep (se 1 (by rfl) ⟨1967810, by rfl⟩ : syracuseStep 2623747 = 3935621) B3935621
theorem B3498329 : Blo 2071435 3498329 := bstep (se 2 (by rfl) ⟨1311873, by rfl⟩ : syracuseStep 3498329 = 2623747) B2623747
theorem B2332219 : Blo 2071435 2332219 := bstep (se 1 (by rfl) ⟨1749164, by rfl⟩ : syracuseStep 2332219 = 3498329) B3498329
theorem B3109625 : Blo 2071435 3109625 := bstep (se 2 (by rfl) ⟨1166109, by rfl⟩ : syracuseStep 3109625 = 2332219) B2332219
theorem B2073083 : Blo 2071435 2073083 := bstep (se 1 (by rfl) ⟨1554812, by rfl⟩ : syracuseStep 2073083 = 3109625) B3109625
theorem B4487989 : Blo 2071435 4487989 := bbase (se 5 (by rfl) ⟨210374, by rfl⟩ : syracuseStep 4487989 = 420749) (by norm_num)
theorem B5983985 : Blo 2071435 5983985 := bstep (se 2 (by rfl) ⟨2243994, by rfl⟩ : syracuseStep 5983985 = 4487989) B4487989
theorem B3989323 : Blo 2071435 3989323 := bstep (se 1 (by rfl) ⟨2991992, by rfl⟩ : syracuseStep 3989323 = 5983985) B5983985
theorem B21276389 : Blo 2071435 21276389 := bstep (se 4 (by rfl) ⟨1994661, by rfl⟩ : syracuseStep 21276389 = 3989323) B3989323
theorem B56737037 : Blo 2071435 56737037 := bstep (se 3 (by rfl) ⟨10638194, by rfl⟩ : syracuseStep 56737037 = 21276389) B21276389
theorem B151298765 : Blo 2071435 151298765 := bstep (se 3 (by rfl) ⟨28368518, by rfl⟩ : syracuseStep 151298765 = 56737037) B56737037
theorem B100865843 : Blo 2071435 100865843 := bstep (se 1 (by rfl) ⟨75649382, by rfl⟩ : syracuseStep 100865843 = 151298765) B151298765
theorem B67243895 : Blo 2071435 67243895 := bstep (se 1 (by rfl) ⟨50432921, by rfl⟩ : syracuseStep 67243895 = 100865843) B100865843
theorem B44829263 : Blo 2071435 44829263 := bstep (se 1 (by rfl) ⟨33621947, by rfl⟩ : syracuseStep 44829263 = 67243895) B67243895
theorem B29886175 : Blo 2071435 29886175 := bstep (se 1 (by rfl) ⟨22414631, by rfl⟩ : syracuseStep 29886175 = 44829263) B44829263
theorem B39848233 : Blo 2071435 39848233 := bstep (se 2 (by rfl) ⟨14943087, by rfl⟩ : syracuseStep 39848233 = 29886175) B29886175
theorem B53130977 : Blo 2071435 53130977 := bstep (se 2 (by rfl) ⟨19924116, by rfl⟩ : syracuseStep 53130977 = 39848233) B39848233
theorem B35420651 : Blo 2071435 35420651 := bstep (se 1 (by rfl) ⟨26565488, by rfl⟩ : syracuseStep 35420651 = 53130977) B53130977
theorem B23613767 : Blo 2071435 23613767 := bstep (se 1 (by rfl) ⟨17710325, by rfl⟩ : syracuseStep 23613767 = 35420651) B35420651
theorem B15742511 : Blo 2071435 15742511 := bstep (se 1 (by rfl) ⟨11806883, by rfl⟩ : syracuseStep 15742511 = 23613767) B23613767
theorem B10495007 : Blo 2071435 10495007 := bstep (se 1 (by rfl) ⟨7871255, by rfl⟩ : syracuseStep 10495007 = 15742511) B15742511
theorem B6996671 : Blo 2071435 6996671 := bstep (se 1 (by rfl) ⟨5247503, by rfl⟩ : syracuseStep 6996671 = 10495007) B10495007
theorem B4664447 : Blo 2071435 4664447 := bstep (se 1 (by rfl) ⟨3498335, by rfl⟩ : syracuseStep 4664447 = 6996671) B6996671
theorem B3109631 : Blo 2071435 3109631 := bstep (se 1 (by rfl) ⟨2332223, by rfl⟩ : syracuseStep 3109631 = 4664447) B4664447
theorem B2073087 : Blo 2071435 2073087 := bstep (se 1 (by rfl) ⟨1554815, by rfl⟩ : syracuseStep 2073087 = 3109631) B3109631
theorem B3109637 : Blo 2071435 3109637 := bbase (se 4 (by rfl) ⟨291528, by rfl⟩ : syracuseStep 3109637 = 583057) (by norm_num)
theorem B2073091 : Blo 2071435 2073091 := bstep (se 1 (by rfl) ⟨1554818, by rfl⟩ : syracuseStep 2073091 = 3109637) B3109637
theorem B3498349 : Blo 2071435 3498349 := bbase (se 3 (by rfl) ⟨655940, by rfl⟩ : syracuseStep 3498349 = 1311881) (by norm_num)
theorem B4664465 : Blo 2071435 4664465 := bstep (se 2 (by rfl) ⟨1749174, by rfl⟩ : syracuseStep 4664465 = 3498349) B3498349
theorem B3109643 : Blo 2071435 3109643 := bstep (se 1 (by rfl) ⟨2332232, by rfl⟩ : syracuseStep 3109643 = 4664465) B4664465
theorem B2073095 : Blo 2071435 2073095 := bstep (se 1 (by rfl) ⟨1554821, by rfl⟩ : syracuseStep 2073095 = 3109643) B3109643
theorem B2332237 : Blo 2071435 2332237 := bbase (se 3 (by rfl) ⟨437294, by rfl⟩ : syracuseStep 2332237 = 874589) (by norm_num)
theorem B3109649 : Blo 2071435 3109649 := bstep (se 2 (by rfl) ⟨1166118, by rfl⟩ : syracuseStep 3109649 = 2332237) B2332237
theorem B2073099 : Blo 2071435 2073099 := bstep (se 1 (by rfl) ⟨1554824, by rfl⟩ : syracuseStep 2073099 = 3109649) B3109649
theorem B6996725 : Blo 2071435 6996725 := bbase (se 5 (by rfl) ⟨327971, by rfl⟩ : syracuseStep 6996725 = 655943) (by norm_num)
theorem B4664483 : Blo 2071435 4664483 := bstep (se 1 (by rfl) ⟨3498362, by rfl⟩ : syracuseStep 4664483 = 6996725) B6996725
theorem B3109655 : Blo 2071435 3109655 := bstep (se 1 (by rfl) ⟨2332241, by rfl⟩ : syracuseStep 3109655 = 4664483) B4664483
theorem B2073103 : Blo 2071435 2073103 := bstep (se 1 (by rfl) ⟨1554827, by rfl⟩ : syracuseStep 2073103 = 3109655) B3109655
theorem B3109661 : Blo 2071435 3109661 := bbase (se 3 (by rfl) ⟨583061, by rfl⟩ : syracuseStep 3109661 = 1166123) (by norm_num)
theorem B2073107 : Blo 2071435 2073107 := bstep (se 1 (by rfl) ⟨1554830, by rfl⟩ : syracuseStep 2073107 = 3109661) B3109661
theorem B4664501 : Blo 2071435 4664501 := bbase (se 5 (by rfl) ⟨218648, by rfl⟩ : syracuseStep 4664501 = 437297) (by norm_num)
theorem B3109667 : Blo 2071435 3109667 := bstep (se 1 (by rfl) ⟨2332250, by rfl⟩ : syracuseStep 3109667 = 4664501) B4664501
theorem B2073111 : Blo 2071435 2073111 := bstep (se 1 (by rfl) ⟨1554833, by rfl⟩ : syracuseStep 2073111 = 3109667) B3109667
theorem B2213821 : Blo 2071435 2213821 := bbase (se 3 (by rfl) ⟨415091, by rfl⟩ : syracuseStep 2213821 = 830183) (by norm_num)
theorem B11807045 : Blo 2071435 11807045 := bstep (se 4 (by rfl) ⟨1106910, by rfl⟩ : syracuseStep 11807045 = 2213821) B2213821
theorem B7871363 : Blo 2071435 7871363 := bstep (se 1 (by rfl) ⟨5903522, by rfl⟩ : syracuseStep 7871363 = 11807045) B11807045
theorem B5247575 : Blo 2071435 5247575 := bstep (se 1 (by rfl) ⟨3935681, by rfl⟩ : syracuseStep 5247575 = 7871363) B7871363
theorem B3498383 : Blo 2071435 3498383 := bstep (se 1 (by rfl) ⟨2623787, by rfl⟩ : syracuseStep 3498383 = 5247575) B5247575
theorem B2332255 : Blo 2071435 2332255 := bstep (se 1 (by rfl) ⟨1749191, by rfl⟩ : syracuseStep 2332255 = 3498383) B3498383
theorem B3109673 : Blo 2071435 3109673 := bstep (se 2 (by rfl) ⟨1166127, by rfl⟩ : syracuseStep 3109673 = 2332255) B2332255
theorem B2073115 : Blo 2071435 2073115 := bstep (se 1 (by rfl) ⟨1554836, by rfl⟩ : syracuseStep 2073115 = 3109673) B3109673
theorem B2213825 : Blo 2071435 2213825 := bbase (se 2 (by rfl) ⟨830184, by rfl⟩ : syracuseStep 2213825 = 1660369) (by norm_num)
theorem B5903533 : Blo 2071435 5903533 := bstep (se 3 (by rfl) ⟨1106912, by rfl⟩ : syracuseStep 5903533 = 2213825) B2213825
theorem B7871377 : Blo 2071435 7871377 := bstep (se 2 (by rfl) ⟨2951766, by rfl⟩ : syracuseStep 7871377 = 5903533) B5903533
theorem B10495169 : Blo 2071435 10495169 := bstep (se 2 (by rfl) ⟨3935688, by rfl⟩ : syracuseStep 10495169 = 7871377) B7871377
theorem B6996779 : Blo 2071435 6996779 := bstep (se 1 (by rfl) ⟨5247584, by rfl⟩ : syracuseStep 6996779 = 10495169) B10495169
theorem B4664519 : Blo 2071435 4664519 := bstep (se 1 (by rfl) ⟨3498389, by rfl⟩ : syracuseStep 4664519 = 6996779) B6996779
theorem B3109679 : Blo 2071435 3109679 := bstep (se 1 (by rfl) ⟨2332259, by rfl⟩ : syracuseStep 3109679 = 4664519) B4664519
theorem B2073119 : Blo 2071435 2073119 := bstep (se 1 (by rfl) ⟨1554839, by rfl⟩ : syracuseStep 2073119 = 3109679) B3109679
theorem B3109685 : Blo 2071435 3109685 := bbase (se 5 (by rfl) ⟨145766, by rfl⟩ : syracuseStep 3109685 = 291533) (by norm_num)
theorem B2073123 : Blo 2071435 2073123 := bstep (se 1 (by rfl) ⟨1554842, by rfl⟩ : syracuseStep 2073123 = 3109685) B3109685
theorem B5247605 : Blo 2071435 5247605 := bbase (se 5 (by rfl) ⟨245981, by rfl⟩ : syracuseStep 5247605 = 491963) (by norm_num)
theorem B3498403 : Blo 2071435 3498403 := bstep (se 1 (by rfl) ⟨2623802, by rfl⟩ : syracuseStep 3498403 = 5247605) B5247605
theorem B4664537 : Blo 2071435 4664537 := bstep (se 2 (by rfl) ⟨1749201, by rfl⟩ : syracuseStep 4664537 = 3498403) B3498403
theorem B3109691 : Blo 2071435 3109691 := bstep (se 1 (by rfl) ⟨2332268, by rfl⟩ : syracuseStep 3109691 = 4664537) B4664537
theorem B2073127 : Blo 2071435 2073127 := bstep (se 1 (by rfl) ⟨1554845, by rfl⟩ : syracuseStep 2073127 = 3109691) B3109691
theorem B2332273 : Blo 2071435 2332273 := bbase (se 2 (by rfl) ⟨874602, by rfl⟩ : syracuseStep 2332273 = 1749205) (by norm_num)
theorem B3109697 : Blo 2071435 3109697 := bstep (se 2 (by rfl) ⟨1166136, by rfl⟩ : syracuseStep 3109697 = 2332273) B2332273
theorem B2073131 : Blo 2071435 2073131 := bstep (se 1 (by rfl) ⟨1554848, by rfl⟩ : syracuseStep 2073131 = 3109697) B3109697
theorem B2101421 : Blo 2071435 2101421 := bbase (se 3 (by rfl) ⟨394016, by rfl⟩ : syracuseStep 2101421 = 788033) (by norm_num)
theorem B5603789 : Blo 2071435 5603789 := bstep (se 3 (by rfl) ⟨1050710, by rfl⟩ : syracuseStep 5603789 = 2101421) B2101421
theorem B14943437 : Blo 2071435 14943437 := bstep (se 3 (by rfl) ⟨2801894, by rfl⟩ : syracuseStep 14943437 = 5603789) B5603789
theorem B9962291 : Blo 2071435 9962291 := bstep (se 1 (by rfl) ⟨7471718, by rfl⟩ : syracuseStep 9962291 = 14943437) B14943437
theorem B6641527 : Blo 2071435 6641527 := bstep (se 1 (by rfl) ⟨4981145, by rfl⟩ : syracuseStep 6641527 = 9962291) B9962291
theorem B8855369 : Blo 2071435 8855369 := bstep (se 2 (by rfl) ⟨3320763, by rfl⟩ : syracuseStep 8855369 = 6641527) B6641527
theorem B5903579 : Blo 2071435 5903579 := bstep (se 1 (by rfl) ⟨4427684, by rfl⟩ : syracuseStep 5903579 = 8855369) B8855369
theorem B3935719 : Blo 2071435 3935719 := bstep (se 1 (by rfl) ⟨2951789, by rfl⟩ : syracuseStep 3935719 = 5903579) B5903579
theorem B5247625 : Blo 2071435 5247625 := bstep (se 2 (by rfl) ⟨1967859, by rfl⟩ : syracuseStep 5247625 = 3935719) B3935719
theorem B6996833 : Blo 2071435 6996833 := bstep (se 2 (by rfl) ⟨2623812, by rfl⟩ : syracuseStep 6996833 = 5247625) B5247625
theorem B4664555 : Blo 2071435 4664555 := bstep (se 1 (by rfl) ⟨3498416, by rfl⟩ : syracuseStep 4664555 = 6996833) B6996833
theorem B3109703 : Blo 2071435 3109703 := bstep (se 1 (by rfl) ⟨2332277, by rfl⟩ : syracuseStep 3109703 = 4664555) B4664555
theorem B2073135 : Blo 2071435 2073135 := bstep (se 1 (by rfl) ⟨1554851, by rfl⟩ : syracuseStep 2073135 = 3109703) B3109703
theorem B3109709 : Blo 2071435 3109709 := bbase (se 3 (by rfl) ⟨583070, by rfl⟩ : syracuseStep 3109709 = 1166141) (by norm_num)
theorem B2073139 : Blo 2071435 2073139 := bstep (se 1 (by rfl) ⟨1554854, by rfl⟩ : syracuseStep 2073139 = 3109709) B3109709
theorem B4664573 : Blo 2071435 4664573 := bbase (se 3 (by rfl) ⟨874607, by rfl⟩ : syracuseStep 4664573 = 1749215) (by norm_num)
theorem B3109715 : Blo 2071435 3109715 := bstep (se 1 (by rfl) ⟨2332286, by rfl⟩ : syracuseStep 3109715 = 4664573) B4664573
theorem B2073143 : Blo 2071435 2073143 := bstep (se 1 (by rfl) ⟨1554857, by rfl⟩ : syracuseStep 2073143 = 3109715) B3109715
theorem B3498437 : Blo 2071435 3498437 := bbase (se 4 (by rfl) ⟨327978, by rfl⟩ : syracuseStep 3498437 = 655957) (by norm_num)
theorem B2332291 : Blo 2071435 2332291 := bstep (se 1 (by rfl) ⟨1749218, by rfl⟩ : syracuseStep 2332291 = 3498437) B3498437
theorem B3109721 : Blo 2071435 3109721 := bstep (se 2 (by rfl) ⟨1166145, by rfl⟩ : syracuseStep 3109721 = 2332291) B2332291
theorem B2073147 : Blo 2071435 2073147 := bstep (se 1 (by rfl) ⟨1554860, by rfl⟩ : syracuseStep 2073147 = 3109721) B3109721
theorem B15742997 : Blo 2071435 15742997 := bbase (se 6 (by rfl) ⟨368976, by rfl⟩ : syracuseStep 15742997 = 737953) (by norm_num)
theorem B10495331 : Blo 2071435 10495331 := bstep (se 1 (by rfl) ⟨7871498, by rfl⟩ : syracuseStep 10495331 = 15742997) B15742997
theorem B6996887 : Blo 2071435 6996887 := bstep (se 1 (by rfl) ⟨5247665, by rfl⟩ : syracuseStep 6996887 = 10495331) B10495331
theorem B4664591 : Blo 2071435 4664591 := bstep (se 1 (by rfl) ⟨3498443, by rfl⟩ : syracuseStep 4664591 = 6996887) B6996887
theorem B3109727 : Blo 2071435 3109727 := bstep (se 1 (by rfl) ⟨2332295, by rfl⟩ : syracuseStep 3109727 = 4664591) B4664591
theorem B2073151 : Blo 2071435 2073151 := bstep (se 1 (by rfl) ⟨1554863, by rfl⟩ : syracuseStep 2073151 = 3109727) B3109727
theorem B3109733 : Blo 2071435 3109733 := bbase (se 4 (by rfl) ⟨291537, by rfl⟩ : syracuseStep 3109733 = 583075) (by norm_num)
theorem B2073155 : Blo 2071435 2073155 := bstep (se 1 (by rfl) ⟨1554866, by rfl⟩ : syracuseStep 2073155 = 3109733) B3109733
theorem B3935765 : Blo 2071435 3935765 := bbase (se 6 (by rfl) ⟨92244, by rfl⟩ : syracuseStep 3935765 = 184489) (by norm_num)
theorem B2623843 : Blo 2071435 2623843 := bstep (se 1 (by rfl) ⟨1967882, by rfl⟩ : syracuseStep 2623843 = 3935765) B3935765
theorem B3498457 : Blo 2071435 3498457 := bstep (se 2 (by rfl) ⟨1311921, by rfl⟩ : syracuseStep 3498457 = 2623843) B2623843
theorem B4664609 : Blo 2071435 4664609 := bstep (se 2 (by rfl) ⟨1749228, by rfl⟩ : syracuseStep 4664609 = 3498457) B3498457
theorem B3109739 : Blo 2071435 3109739 := bstep (se 1 (by rfl) ⟨2332304, by rfl⟩ : syracuseStep 3109739 = 4664609) B4664609
theorem B2073159 : Blo 2071435 2073159 := bstep (se 1 (by rfl) ⟨1554869, by rfl⟩ : syracuseStep 2073159 = 3109739) B3109739
theorem B2332309 : Blo 2071435 2332309 := bbase (se 6 (by rfl) ⟨54663, by rfl⟩ : syracuseStep 2332309 = 109327) (by norm_num)
theorem B3109745 : Blo 2071435 3109745 := bstep (se 2 (by rfl) ⟨1166154, by rfl⟩ : syracuseStep 3109745 = 2332309) B2332309
theorem B2073163 : Blo 2071435 2073163 := bstep (se 1 (by rfl) ⟨1554872, by rfl⟩ : syracuseStep 2073163 = 3109745) B3109745
theorem B2623853 : Blo 2071435 2623853 := bbase (se 3 (by rfl) ⟨491972, by rfl⟩ : syracuseStep 2623853 = 983945) (by norm_num)
theorem B6996941 : Blo 2071435 6996941 := bstep (se 3 (by rfl) ⟨1311926, by rfl⟩ : syracuseStep 6996941 = 2623853) B2623853
theorem B4664627 : Blo 2071435 4664627 := bstep (se 1 (by rfl) ⟨3498470, by rfl⟩ : syracuseStep 4664627 = 6996941) B6996941
theorem B3109751 : Blo 2071435 3109751 := bstep (se 1 (by rfl) ⟨2332313, by rfl⟩ : syracuseStep 3109751 = 4664627) B4664627
theorem B2073167 : Blo 2071435 2073167 := bstep (se 1 (by rfl) ⟨1554875, by rfl⟩ : syracuseStep 2073167 = 3109751) B3109751
theorem B3109757 : Blo 2071435 3109757 := bbase (se 3 (by rfl) ⟨583079, by rfl⟩ : syracuseStep 3109757 = 1166159) (by norm_num)
theorem B2073171 : Blo 2071435 2073171 := bstep (se 1 (by rfl) ⟨1554878, by rfl⟩ : syracuseStep 2073171 = 3109757) B3109757
theorem B4664645 : Blo 2071435 4664645 := bbase (se 4 (by rfl) ⟨437310, by rfl⟩ : syracuseStep 4664645 = 874621) (by norm_num)
theorem B3109763 : Blo 2071435 3109763 := bstep (se 1 (by rfl) ⟨2332322, by rfl⟩ : syracuseStep 3109763 = 4664645) B4664645
theorem B2073175 : Blo 2071435 2073175 := bstep (se 1 (by rfl) ⟨1554881, by rfl⟩ : syracuseStep 2073175 = 3109763) B3109763
theorem B6641669 : Blo 2071435 6641669 := bbase (se 4 (by rfl) ⟨622656, by rfl⟩ : syracuseStep 6641669 = 1245313) (by norm_num)
theorem B4427779 : Blo 2071435 4427779 := bstep (se 1 (by rfl) ⟨3320834, by rfl⟩ : syracuseStep 4427779 = 6641669) B6641669
theorem B5903705 : Blo 2071435 5903705 := bstep (se 2 (by rfl) ⟨2213889, by rfl⟩ : syracuseStep 5903705 = 4427779) B4427779
theorem B3935803 : Blo 2071435 3935803 := bstep (se 1 (by rfl) ⟨2951852, by rfl⟩ : syracuseStep 3935803 = 5903705) B5903705
theorem B5247737 : Blo 2071435 5247737 := bstep (se 2 (by rfl) ⟨1967901, by rfl⟩ : syracuseStep 5247737 = 3935803) B3935803
theorem B3498491 : Blo 2071435 3498491 := bstep (se 1 (by rfl) ⟨2623868, by rfl⟩ : syracuseStep 3498491 = 5247737) B5247737
theorem B2332327 : Blo 2071435 2332327 := bstep (se 1 (by rfl) ⟨1749245, by rfl⟩ : syracuseStep 2332327 = 3498491) B3498491
theorem B3109769 : Blo 2071435 3109769 := bstep (se 2 (by rfl) ⟨1166163, by rfl⟩ : syracuseStep 3109769 = 2332327) B2332327
theorem B2073179 : Blo 2071435 2073179 := bstep (se 1 (by rfl) ⟨1554884, by rfl⟩ : syracuseStep 2073179 = 3109769) B3109769
theorem B10495493 : Blo 2071435 10495493 := bbase (se 4 (by rfl) ⟨983952, by rfl⟩ : syracuseStep 10495493 = 1967905) (by norm_num)
theorem B6996995 : Blo 2071435 6996995 := bstep (se 1 (by rfl) ⟨5247746, by rfl⟩ : syracuseStep 6996995 = 10495493) B10495493
theorem B4664663 : Blo 2071435 4664663 := bstep (se 1 (by rfl) ⟨3498497, by rfl⟩ : syracuseStep 4664663 = 6996995) B6996995
theorem B3109775 : Blo 2071435 3109775 := bstep (se 1 (by rfl) ⟨2332331, by rfl⟩ : syracuseStep 3109775 = 4664663) B4664663
theorem B2073183 : Blo 2071435 2073183 := bstep (se 1 (by rfl) ⟨1554887, by rfl⟩ : syracuseStep 2073183 = 3109775) B3109775
theorem B3109781 : Blo 2071435 3109781 := bbase (se 6 (by rfl) ⟨72885, by rfl⟩ : syracuseStep 3109781 = 145771) (by norm_num)
theorem B2073187 : Blo 2071435 2073187 := bstep (se 1 (by rfl) ⟨1554890, by rfl⟩ : syracuseStep 2073187 = 3109781) B3109781
theorem B11807477 : Blo 2071435 11807477 := bbase (se 5 (by rfl) ⟨553475, by rfl⟩ : syracuseStep 11807477 = 1106951) (by norm_num)
theorem B7871651 : Blo 2071435 7871651 := bstep (se 1 (by rfl) ⟨5903738, by rfl⟩ : syracuseStep 7871651 = 11807477) B11807477
theorem B5247767 : Blo 2071435 5247767 := bstep (se 1 (by rfl) ⟨3935825, by rfl⟩ : syracuseStep 5247767 = 7871651) B7871651
theorem B3498511 : Blo 2071435 3498511 := bstep (se 1 (by rfl) ⟨2623883, by rfl⟩ : syracuseStep 3498511 = 5247767) B5247767
theorem B4664681 : Blo 2071435 4664681 := bstep (se 2 (by rfl) ⟨1749255, by rfl⟩ : syracuseStep 4664681 = 3498511) B3498511
theorem B3109787 : Blo 2071435 3109787 := bstep (se 1 (by rfl) ⟨2332340, by rfl⟩ : syracuseStep 3109787 = 4664681) B4664681
theorem B2073191 : Blo 2071435 2073191 := bstep (se 1 (by rfl) ⟨1554893, by rfl⟩ : syracuseStep 2073191 = 3109787) B3109787
theorem B2332345 : Blo 2071435 2332345 := bbase (se 2 (by rfl) ⟨874629, by rfl⟩ : syracuseStep 2332345 = 1749259) (by norm_num)
theorem B3109793 : Blo 2071435 3109793 := bstep (se 2 (by rfl) ⟨1166172, by rfl⟩ : syracuseStep 3109793 = 2332345) B2332345
theorem B2073195 : Blo 2071435 2073195 := bstep (se 1 (by rfl) ⟨1554896, by rfl⟩ : syracuseStep 2073195 = 3109793) B3109793
theorem B4427821 : Blo 2071435 4427821 := bbase (se 3 (by rfl) ⟨830216, by rfl⟩ : syracuseStep 4427821 = 1660433) (by norm_num)
theorem B5903761 : Blo 2071435 5903761 := bstep (se 2 (by rfl) ⟨2213910, by rfl⟩ : syracuseStep 5903761 = 4427821) B4427821
theorem B7871681 : Blo 2071435 7871681 := bstep (se 2 (by rfl) ⟨2951880, by rfl⟩ : syracuseStep 7871681 = 5903761) B5903761
theorem B5247787 : Blo 2071435 5247787 := bstep (se 1 (by rfl) ⟨3935840, by rfl⟩ : syracuseStep 5247787 = 7871681) B7871681
theorem B6997049 : Blo 2071435 6997049 := bstep (se 2 (by rfl) ⟨2623893, by rfl⟩ : syracuseStep 6997049 = 5247787) B5247787
theorem B4664699 : Blo 2071435 4664699 := bstep (se 1 (by rfl) ⟨3498524, by rfl⟩ : syracuseStep 4664699 = 6997049) B6997049
theorem B3109799 : Blo 2071435 3109799 := bstep (se 1 (by rfl) ⟨2332349, by rfl⟩ : syracuseStep 3109799 = 4664699) B4664699
theorem B2073199 : Blo 2071435 2073199 := bstep (se 1 (by rfl) ⟨1554899, by rfl⟩ : syracuseStep 2073199 = 3109799) B3109799
theorem B3109805 : Blo 2071435 3109805 := bbase (se 3 (by rfl) ⟨583088, by rfl⟩ : syracuseStep 3109805 = 1166177) (by norm_num)
theorem B2073203 : Blo 2071435 2073203 := bstep (se 1 (by rfl) ⟨1554902, by rfl⟩ : syracuseStep 2073203 = 3109805) B3109805
theorem B4664717 : Blo 2071435 4664717 := bbase (se 3 (by rfl) ⟨874634, by rfl⟩ : syracuseStep 4664717 = 1749269) (by norm_num)
theorem B3109811 : Blo 2071435 3109811 := bstep (se 1 (by rfl) ⟨2332358, by rfl⟩ : syracuseStep 3109811 = 4664717) B4664717
theorem B2073207 : Blo 2071435 2073207 := bstep (se 1 (by rfl) ⟨1554905, by rfl⟩ : syracuseStep 2073207 = 3109811) B3109811
theorem B2623909 : Blo 2071435 2623909 := bbase (se 4 (by rfl) ⟨245991, by rfl⟩ : syracuseStep 2623909 = 491983) (by norm_num)
theorem B3498545 : Blo 2071435 3498545 := bstep (se 2 (by rfl) ⟨1311954, by rfl⟩ : syracuseStep 3498545 = 2623909) B2623909
theorem B2332363 : Blo 2071435 2332363 := bstep (se 1 (by rfl) ⟨1749272, by rfl⟩ : syracuseStep 2332363 = 3498545) B3498545
theorem B3109817 : Blo 2071435 3109817 := bstep (se 2 (by rfl) ⟨1166181, by rfl⟩ : syracuseStep 3109817 = 2332363) B2332363
theorem B2073211 : Blo 2071435 2073211 := bstep (se 1 (by rfl) ⟨1554908, by rfl⟩ : syracuseStep 2073211 = 3109817) B3109817
theorem B29888021 : Blo 2071435 29888021 := bbase (se 6 (by rfl) ⟨700500, by rfl⟩ : syracuseStep 29888021 = 1401001) (by norm_num)
theorem B19925347 : Blo 2071435 19925347 := bstep (se 1 (by rfl) ⟨14944010, by rfl⟩ : syracuseStep 19925347 = 29888021) B29888021
theorem B26567129 : Blo 2071435 26567129 := bstep (se 2 (by rfl) ⟨9962673, by rfl⟩ : syracuseStep 26567129 = 19925347) B19925347
theorem B17711419 : Blo 2071435 17711419 := bstep (se 1 (by rfl) ⟨13283564, by rfl⟩ : syracuseStep 17711419 = 26567129) B26567129
theorem B23615225 : Blo 2071435 23615225 := bstep (se 2 (by rfl) ⟨8855709, by rfl⟩ : syracuseStep 23615225 = 17711419) B17711419
theorem B15743483 : Blo 2071435 15743483 := bstep (se 1 (by rfl) ⟨11807612, by rfl⟩ : syracuseStep 15743483 = 23615225) B23615225
theorem B10495655 : Blo 2071435 10495655 := bstep (se 1 (by rfl) ⟨7871741, by rfl⟩ : syracuseStep 10495655 = 15743483) B15743483
theorem B6997103 : Blo 2071435 6997103 := bstep (se 1 (by rfl) ⟨5247827, by rfl⟩ : syracuseStep 6997103 = 10495655) B10495655
theorem B4664735 : Blo 2071435 4664735 := bstep (se 1 (by rfl) ⟨3498551, by rfl⟩ : syracuseStep 4664735 = 6997103) B6997103
theorem B3109823 : Blo 2071435 3109823 := bstep (se 1 (by rfl) ⟨2332367, by rfl⟩ : syracuseStep 3109823 = 4664735) B4664735
theorem B2073215 : Blo 2071435 2073215 := bstep (se 1 (by rfl) ⟨1554911, by rfl⟩ : syracuseStep 2073215 = 3109823) B3109823
theorem B3109829 : Blo 2071435 3109829 := bbase (se 4 (by rfl) ⟨291546, by rfl⟩ : syracuseStep 3109829 = 583093) (by norm_num)
theorem B2073219 : Blo 2071435 2073219 := bstep (se 1 (by rfl) ⟨1554914, by rfl⟩ : syracuseStep 2073219 = 3109829) B3109829
theorem B3498565 : Blo 2071435 3498565 := bbase (se 4 (by rfl) ⟨327990, by rfl⟩ : syracuseStep 3498565 = 655981) (by norm_num)
theorem B4664753 : Blo 2071435 4664753 := bstep (se 2 (by rfl) ⟨1749282, by rfl⟩ : syracuseStep 4664753 = 3498565) B3498565
theorem B3109835 : Blo 2071435 3109835 := bstep (se 1 (by rfl) ⟨2332376, by rfl⟩ : syracuseStep 3109835 = 4664753) B4664753
theorem B2073223 : Blo 2071435 2073223 := bstep (se 1 (by rfl) ⟨1554917, by rfl⟩ : syracuseStep 2073223 = 3109835) B3109835
theorem B2332381 : Blo 2071435 2332381 := bbase (se 3 (by rfl) ⟨437321, by rfl⟩ : syracuseStep 2332381 = 874643) (by norm_num)
theorem B3109841 : Blo 2071435 3109841 := bstep (se 2 (by rfl) ⟨1166190, by rfl⟩ : syracuseStep 3109841 = 2332381) B2332381
theorem B2073227 : Blo 2071435 2073227 := bstep (se 1 (by rfl) ⟨1554920, by rfl⟩ : syracuseStep 2073227 = 3109841) B3109841
theorem B6997157 : Blo 2071435 6997157 := bbase (se 4 (by rfl) ⟨655983, by rfl⟩ : syracuseStep 6997157 = 1311967) (by norm_num)
theorem B4664771 : Blo 2071435 4664771 := bstep (se 1 (by rfl) ⟨3498578, by rfl⟩ : syracuseStep 4664771 = 6997157) B6997157
theorem B3109847 : Blo 2071435 3109847 := bstep (se 1 (by rfl) ⟨2332385, by rfl⟩ : syracuseStep 3109847 = 4664771) B4664771
theorem B2073231 : Blo 2071435 2073231 := bstep (se 1 (by rfl) ⟨1554923, by rfl⟩ : syracuseStep 2073231 = 3109847) B3109847
theorem B3109853 : Blo 2071435 3109853 := bbase (se 3 (by rfl) ⟨583097, by rfl⟩ : syracuseStep 3109853 = 1166195) (by norm_num)
theorem B2073235 : Blo 2071435 2073235 := bstep (se 1 (by rfl) ⟨1554926, by rfl⟩ : syracuseStep 2073235 = 3109853) B3109853
theorem B4664789 : Blo 2071435 4664789 := bbase (se 7 (by rfl) ⟨54665, by rfl⟩ : syracuseStep 4664789 = 109331) (by norm_num)
theorem B3109859 : Blo 2071435 3109859 := bstep (se 1 (by rfl) ⟨2332394, by rfl⟩ : syracuseStep 3109859 = 4664789) B4664789
theorem B2073239 : Blo 2071435 2073239 := bstep (se 1 (by rfl) ⟨1554929, by rfl⟩ : syracuseStep 2073239 = 3109859) B3109859
theorem B19925621 : Blo 2071435 19925621 := bbase (se 5 (by rfl) ⟨934013, by rfl⟩ : syracuseStep 19925621 = 1868027) (by norm_num)
theorem B13283747 : Blo 2071435 13283747 := bstep (se 1 (by rfl) ⟨9962810, by rfl⟩ : syracuseStep 13283747 = 19925621) B19925621
theorem B8855831 : Blo 2071435 8855831 := bstep (se 1 (by rfl) ⟨6641873, by rfl⟩ : syracuseStep 8855831 = 13283747) B13283747
theorem B5903887 : Blo 2071435 5903887 := bstep (se 1 (by rfl) ⟨4427915, by rfl⟩ : syracuseStep 5903887 = 8855831) B8855831
theorem B7871849 : Blo 2071435 7871849 := bstep (se 2 (by rfl) ⟨2951943, by rfl⟩ : syracuseStep 7871849 = 5903887) B5903887
theorem B5247899 : Blo 2071435 5247899 := bstep (se 1 (by rfl) ⟨3935924, by rfl⟩ : syracuseStep 5247899 = 7871849) B7871849
theorem B3498599 : Blo 2071435 3498599 := bstep (se 1 (by rfl) ⟨2623949, by rfl⟩ : syracuseStep 3498599 = 5247899) B5247899
theorem B2332399 : Blo 2071435 2332399 := bstep (se 1 (by rfl) ⟨1749299, by rfl⟩ : syracuseStep 2332399 = 3498599) B3498599
theorem B3109865 : Blo 2071435 3109865 := bstep (se 2 (by rfl) ⟨1166199, by rfl⟩ : syracuseStep 3109865 = 2332399) B2332399
theorem B2073243 : Blo 2071435 2073243 := bstep (se 1 (by rfl) ⟨1554932, by rfl⟩ : syracuseStep 2073243 = 3109865) B3109865
theorem B3736061 : Blo 2071435 3736061 := bbase (se 3 (by rfl) ⟨700511, by rfl⟩ : syracuseStep 3736061 = 1401023) (by norm_num)
theorem B2490707 : Blo 2071435 2490707 := bstep (se 1 (by rfl) ⟨1868030, by rfl⟩ : syracuseStep 2490707 = 3736061) B3736061
theorem B6641885 : Blo 2071435 6641885 := bstep (se 3 (by rfl) ⟨1245353, by rfl⟩ : syracuseStep 6641885 = 2490707) B2490707
theorem B17711693 : Blo 2071435 17711693 := bstep (se 3 (by rfl) ⟨3320942, by rfl⟩ : syracuseStep 17711693 = 6641885) B6641885
theorem B11807795 : Blo 2071435 11807795 := bstep (se 1 (by rfl) ⟨8855846, by rfl⟩ : syracuseStep 11807795 = 17711693) B17711693
theorem B7871863 : Blo 2071435 7871863 := bstep (se 1 (by rfl) ⟨5903897, by rfl⟩ : syracuseStep 7871863 = 11807795) B11807795
theorem B10495817 : Blo 2071435 10495817 := bstep (se 2 (by rfl) ⟨3935931, by rfl⟩ : syracuseStep 10495817 = 7871863) B7871863
theorem B6997211 : Blo 2071435 6997211 := bstep (se 1 (by rfl) ⟨5247908, by rfl⟩ : syracuseStep 6997211 = 10495817) B10495817
theorem B4664807 : Blo 2071435 4664807 := bstep (se 1 (by rfl) ⟨3498605, by rfl⟩ : syracuseStep 4664807 = 6997211) B6997211
theorem B3109871 : Blo 2071435 3109871 := bstep (se 1 (by rfl) ⟨2332403, by rfl⟩ : syracuseStep 3109871 = 4664807) B4664807
theorem B2073247 : Blo 2071435 2073247 := bstep (se 1 (by rfl) ⟨1554935, by rfl⟩ : syracuseStep 2073247 = 3109871) B3109871
theorem B3109877 : Blo 2071435 3109877 := bbase (se 5 (by rfl) ⟨145775, by rfl⟩ : syracuseStep 3109877 = 291551) (by norm_num)
theorem B2073251 : Blo 2071435 2073251 := bstep (se 1 (by rfl) ⟨1554938, by rfl⟩ : syracuseStep 2073251 = 3109877) B3109877
theorem B4427941 : Blo 2071435 4427941 := bbase (se 4 (by rfl) ⟨415119, by rfl⟩ : syracuseStep 4427941 = 830239) (by norm_num)
theorem B5903921 : Blo 2071435 5903921 := bstep (se 2 (by rfl) ⟨2213970, by rfl⟩ : syracuseStep 5903921 = 4427941) B4427941
theorem B3935947 : Blo 2071435 3935947 := bstep (se 1 (by rfl) ⟨2951960, by rfl⟩ : syracuseStep 3935947 = 5903921) B5903921
theorem B5247929 : Blo 2071435 5247929 := bstep (se 2 (by rfl) ⟨1967973, by rfl⟩ : syracuseStep 5247929 = 3935947) B3935947
theorem B3498619 : Blo 2071435 3498619 := bstep (se 1 (by rfl) ⟨2623964, by rfl⟩ : syracuseStep 3498619 = 5247929) B5247929
theorem B4664825 : Blo 2071435 4664825 := bstep (se 2 (by rfl) ⟨1749309, by rfl⟩ : syracuseStep 4664825 = 3498619) B3498619
theorem B3109883 : Blo 2071435 3109883 := bstep (se 1 (by rfl) ⟨2332412, by rfl⟩ : syracuseStep 3109883 = 4664825) B4664825
theorem B2073255 : Blo 2071435 2073255 := bstep (se 1 (by rfl) ⟨1554941, by rfl⟩ : syracuseStep 2073255 = 3109883) B3109883
theorem B2332417 : Blo 2071435 2332417 := bbase (se 2 (by rfl) ⟨874656, by rfl⟩ : syracuseStep 2332417 = 1749313) (by norm_num)
theorem B3109889 : Blo 2071435 3109889 := bstep (se 2 (by rfl) ⟨1166208, by rfl⟩ : syracuseStep 3109889 = 2332417) B2332417
theorem B2073259 : Blo 2071435 2073259 := bstep (se 1 (by rfl) ⟨1554944, by rfl⟩ : syracuseStep 2073259 = 3109889) B3109889
theorem B5247949 : Blo 2071435 5247949 := bbase (se 3 (by rfl) ⟨983990, by rfl⟩ : syracuseStep 5247949 = 1967981) (by norm_num)
theorem B6997265 : Blo 2071435 6997265 := bstep (se 2 (by rfl) ⟨2623974, by rfl⟩ : syracuseStep 6997265 = 5247949) B5247949
theorem B4664843 : Blo 2071435 4664843 := bstep (se 1 (by rfl) ⟨3498632, by rfl⟩ : syracuseStep 4664843 = 6997265) B6997265
theorem B3109895 : Blo 2071435 3109895 := bstep (se 1 (by rfl) ⟨2332421, by rfl⟩ : syracuseStep 3109895 = 4664843) B4664843
theorem B2073263 : Blo 2071435 2073263 := bstep (se 1 (by rfl) ⟨1554947, by rfl⟩ : syracuseStep 2073263 = 3109895) B3109895
theorem B3109901 : Blo 2071435 3109901 := bbase (se 3 (by rfl) ⟨583106, by rfl⟩ : syracuseStep 3109901 = 1166213) (by norm_num)
theorem B2073267 : Blo 2071435 2073267 := bstep (se 1 (by rfl) ⟨1554950, by rfl⟩ : syracuseStep 2073267 = 3109901) B3109901
theorem B4664861 : Blo 2071435 4664861 := bbase (se 3 (by rfl) ⟨874661, by rfl⟩ : syracuseStep 4664861 = 1749323) (by norm_num)
theorem B3109907 : Blo 2071435 3109907 := bstep (se 1 (by rfl) ⟨2332430, by rfl⟩ : syracuseStep 3109907 = 4664861) B4664861
theorem B2073271 : Blo 2071435 2073271 := bstep (se 1 (by rfl) ⟨1554953, by rfl⟩ : syracuseStep 2073271 = 3109907) B3109907
theorem B3498653 : Blo 2071435 3498653 := bbase (se 3 (by rfl) ⟨655997, by rfl⟩ : syracuseStep 3498653 = 1311995) (by norm_num)
theorem B2332435 : Blo 2071435 2332435 := bstep (se 1 (by rfl) ⟨1749326, by rfl⟩ : syracuseStep 2332435 = 3498653) B3498653
theorem B3109913 : Blo 2071435 3109913 := bstep (se 2 (by rfl) ⟨1166217, by rfl⟩ : syracuseStep 3109913 = 2332435) B2332435
theorem B2073275 : Blo 2071435 2073275 := bstep (se 1 (by rfl) ⟨1554956, by rfl⟩ : syracuseStep 2073275 = 3109913) B3109913
theorem B4203133 : Blo 2071435 4203133 := bbase (se 3 (by rfl) ⟨788087, by rfl⟩ : syracuseStep 4203133 = 1576175) (by norm_num)
theorem B22416709 : Blo 2071435 22416709 := bstep (se 4 (by rfl) ⟨2101566, by rfl⟩ : syracuseStep 22416709 = 4203133) B4203133
theorem B29888945 : Blo 2071435 29888945 := bstep (se 2 (by rfl) ⟨11208354, by rfl⟩ : syracuseStep 29888945 = 22416709) B22416709
theorem B19925963 : Blo 2071435 19925963 := bstep (se 1 (by rfl) ⟨14944472, by rfl⟩ : syracuseStep 19925963 = 29888945) B29888945
theorem B13283975 : Blo 2071435 13283975 := bstep (se 1 (by rfl) ⟨9962981, by rfl⟩ : syracuseStep 13283975 = 19925963) B19925963
theorem B8855983 : Blo 2071435 8855983 := bstep (se 1 (by rfl) ⟨6641987, by rfl⟩ : syracuseStep 8855983 = 13283975) B13283975
theorem B11807977 : Blo 2071435 11807977 := bstep (se 2 (by rfl) ⟨4427991, by rfl⟩ : syracuseStep 11807977 = 8855983) B8855983
theorem B15743969 : Blo 2071435 15743969 := bstep (se 2 (by rfl) ⟨5903988, by rfl⟩ : syracuseStep 15743969 = 11807977) B11807977
theorem B10495979 : Blo 2071435 10495979 := bstep (se 1 (by rfl) ⟨7871984, by rfl⟩ : syracuseStep 10495979 = 15743969) B15743969
theorem B6997319 : Blo 2071435 6997319 := bstep (se 1 (by rfl) ⟨5247989, by rfl⟩ : syracuseStep 6997319 = 10495979) B10495979
theorem B4664879 : Blo 2071435 4664879 := bstep (se 1 (by rfl) ⟨3498659, by rfl⟩ : syracuseStep 4664879 = 6997319) B6997319
theorem B3109919 : Blo 2071435 3109919 := bstep (se 1 (by rfl) ⟨2332439, by rfl⟩ : syracuseStep 3109919 = 4664879) B4664879
theorem B2073279 : Blo 2071435 2073279 := bstep (se 1 (by rfl) ⟨1554959, by rfl⟩ : syracuseStep 2073279 = 3109919) B3109919
theorem B3109925 : Blo 2071435 3109925 := bbase (se 4 (by rfl) ⟨291555, by rfl⟩ : syracuseStep 3109925 = 583111) (by norm_num)
theorem B2073283 : Blo 2071435 2073283 := bstep (se 1 (by rfl) ⟨1554962, by rfl⟩ : syracuseStep 2073283 = 3109925) B3109925
theorem B2624005 : Blo 2071435 2624005 := bbase (se 4 (by rfl) ⟨246000, by rfl⟩ : syracuseStep 2624005 = 492001) (by norm_num)
theorem B3498673 : Blo 2071435 3498673 := bstep (se 2 (by rfl) ⟨1312002, by rfl⟩ : syracuseStep 3498673 = 2624005) B2624005
theorem B4664897 : Blo 2071435 4664897 := bstep (se 2 (by rfl) ⟨1749336, by rfl⟩ : syracuseStep 4664897 = 3498673) B3498673
theorem B3109931 : Blo 2071435 3109931 := bstep (se 1 (by rfl) ⟨2332448, by rfl⟩ : syracuseStep 3109931 = 4664897) B4664897
theorem B2073287 : Blo 2071435 2073287 := bstep (se 1 (by rfl) ⟨1554965, by rfl⟩ : syracuseStep 2073287 = 3109931) B3109931
theorem B2332453 : Blo 2071435 2332453 := bbase (se 4 (by rfl) ⟨218667, by rfl⟩ : syracuseStep 2332453 = 437335) (by norm_num)
theorem B3109937 : Blo 2071435 3109937 := bstep (se 2 (by rfl) ⟨1166226, by rfl⟩ : syracuseStep 3109937 = 2332453) B2332453
theorem B2073291 : Blo 2071435 2073291 := bstep (se 1 (by rfl) ⟨1554968, by rfl⟩ : syracuseStep 2073291 = 3109937) B3109937
theorem B8856053 : Blo 2071435 8856053 := bbase (se 5 (by rfl) ⟨415127, by rfl⟩ : syracuseStep 8856053 = 830255) (by norm_num)
theorem B5904035 : Blo 2071435 5904035 := bstep (se 1 (by rfl) ⟨4428026, by rfl⟩ : syracuseStep 5904035 = 8856053) B8856053
theorem B3936023 : Blo 2071435 3936023 := bstep (se 1 (by rfl) ⟨2952017, by rfl⟩ : syracuseStep 3936023 = 5904035) B5904035
theorem B2624015 : Blo 2071435 2624015 := bstep (se 1 (by rfl) ⟨1968011, by rfl⟩ : syracuseStep 2624015 = 3936023) B3936023
theorem B6997373 : Blo 2071435 6997373 := bstep (se 3 (by rfl) ⟨1312007, by rfl⟩ : syracuseStep 6997373 = 2624015) B2624015
theorem B4664915 : Blo 2071435 4664915 := bstep (se 1 (by rfl) ⟨3498686, by rfl⟩ : syracuseStep 4664915 = 6997373) B6997373
theorem B3109943 : Blo 2071435 3109943 := bstep (se 1 (by rfl) ⟨2332457, by rfl⟩ : syracuseStep 3109943 = 4664915) B4664915
theorem B2073295 : Blo 2071435 2073295 := bstep (se 1 (by rfl) ⟨1554971, by rfl⟩ : syracuseStep 2073295 = 3109943) B3109943
theorem B3109949 : Blo 2071435 3109949 := bbase (se 3 (by rfl) ⟨583115, by rfl⟩ : syracuseStep 3109949 = 1166231) (by norm_num)
theorem B2073299 : Blo 2071435 2073299 := bstep (se 1 (by rfl) ⟨1554974, by rfl⟩ : syracuseStep 2073299 = 3109949) B3109949
theorem B4664933 : Blo 2071435 4664933 := bbase (se 4 (by rfl) ⟨437337, by rfl⟩ : syracuseStep 4664933 = 874675) (by norm_num)
theorem B3109955 : Blo 2071435 3109955 := bstep (se 1 (by rfl) ⟨2332466, by rfl⟩ : syracuseStep 3109955 = 4664933) B4664933
theorem B2073303 : Blo 2071435 2073303 := bstep (se 1 (by rfl) ⟨1554977, by rfl⟩ : syracuseStep 2073303 = 3109955) B3109955
theorem B5248061 : Blo 2071435 5248061 := bbase (se 3 (by rfl) ⟨984011, by rfl⟩ : syracuseStep 5248061 = 1968023) (by norm_num)
theorem B3498707 : Blo 2071435 3498707 := bstep (se 1 (by rfl) ⟨2624030, by rfl⟩ : syracuseStep 3498707 = 5248061) B5248061
theorem B2332471 : Blo 2071435 2332471 := bstep (se 1 (by rfl) ⟨1749353, by rfl⟩ : syracuseStep 2332471 = 3498707) B3498707
theorem B3109961 : Blo 2071435 3109961 := bstep (se 2 (by rfl) ⟨1166235, by rfl⟩ : syracuseStep 3109961 = 2332471) B2332471
theorem B2073307 : Blo 2071435 2073307 := bstep (se 1 (by rfl) ⟨1554980, by rfl⟩ : syracuseStep 2073307 = 3109961) B3109961
theorem B3936053 : Blo 2071435 3936053 := bbase (se 5 (by rfl) ⟨184502, by rfl⟩ : syracuseStep 3936053 = 369005) (by norm_num)
theorem B10496141 : Blo 2071435 10496141 := bstep (se 3 (by rfl) ⟨1968026, by rfl⟩ : syracuseStep 10496141 = 3936053) B3936053
theorem B6997427 : Blo 2071435 6997427 := bstep (se 1 (by rfl) ⟨5248070, by rfl⟩ : syracuseStep 6997427 = 10496141) B10496141
theorem B4664951 : Blo 2071435 4664951 := bstep (se 1 (by rfl) ⟨3498713, by rfl⟩ : syracuseStep 4664951 = 6997427) B6997427
theorem B3109967 : Blo 2071435 3109967 := bstep (se 1 (by rfl) ⟨2332475, by rfl⟩ : syracuseStep 3109967 = 4664951) B4664951
theorem B2073311 : Blo 2071435 2073311 := bstep (se 1 (by rfl) ⟨1554983, by rfl⟩ : syracuseStep 2073311 = 3109967) B3109967
theorem B3109973 : Blo 2071435 3109973 := bbase (se 8 (by rfl) ⟨18222, by rfl⟩ : syracuseStep 3109973 = 36445) (by norm_num)
theorem B2073315 : Blo 2071435 2073315 := bstep (se 1 (by rfl) ⟨1554986, by rfl⟩ : syracuseStep 2073315 = 3109973) B3109973
theorem B4488493 : Blo 2071435 4488493 := bbase (se 3 (by rfl) ⟨841592, by rfl⟩ : syracuseStep 4488493 = 1683185) (by norm_num)
theorem B5984657 : Blo 2071435 5984657 := bstep (se 2 (by rfl) ⟨2244246, by rfl⟩ : syracuseStep 5984657 = 4488493) B4488493
theorem B3989771 : Blo 2071435 3989771 := bstep (se 1 (by rfl) ⟨2992328, by rfl⟩ : syracuseStep 3989771 = 5984657) B5984657
theorem B2659847 : Blo 2071435 2659847 := bstep (se 1 (by rfl) ⟨1994885, by rfl⟩ : syracuseStep 2659847 = 3989771) B3989771
theorem B28371701 : Blo 2071435 28371701 := bstep (se 5 (by rfl) ⟨1329923, by rfl⟩ : syracuseStep 28371701 = 2659847) B2659847
theorem B18914467 : Blo 2071435 18914467 := bstep (se 1 (by rfl) ⟨14185850, by rfl⟩ : syracuseStep 18914467 = 28371701) B28371701
theorem B25219289 : Blo 2071435 25219289 := bstep (se 2 (by rfl) ⟨9457233, by rfl⟩ : syracuseStep 25219289 = 18914467) B18914467
theorem B16812859 : Blo 2071435 16812859 := bstep (se 1 (by rfl) ⟨12609644, by rfl⟩ : syracuseStep 16812859 = 25219289) B25219289
theorem B22417145 : Blo 2071435 22417145 := bstep (se 2 (by rfl) ⟨8406429, by rfl⟩ : syracuseStep 22417145 = 16812859) B16812859
theorem B14944763 : Blo 2071435 14944763 := bstep (se 1 (by rfl) ⟨11208572, by rfl⟩ : syracuseStep 14944763 = 22417145) B22417145
theorem B9963175 : Blo 2071435 9963175 := bstep (se 1 (by rfl) ⟨7472381, by rfl⟩ : syracuseStep 9963175 = 14944763) B14944763
theorem B13284233 : Blo 2071435 13284233 := bstep (se 2 (by rfl) ⟨4981587, by rfl⟩ : syracuseStep 13284233 = 9963175) B9963175
theorem B8856155 : Blo 2071435 8856155 := bstep (se 1 (by rfl) ⟨6642116, by rfl⟩ : syracuseStep 8856155 = 13284233) B13284233
theorem B5904103 : Blo 2071435 5904103 := bstep (se 1 (by rfl) ⟨4428077, by rfl⟩ : syracuseStep 5904103 = 8856155) B8856155
theorem B7872137 : Blo 2071435 7872137 := bstep (se 2 (by rfl) ⟨2952051, by rfl⟩ : syracuseStep 7872137 = 5904103) B5904103
theorem B5248091 : Blo 2071435 5248091 := bstep (se 1 (by rfl) ⟨3936068, by rfl⟩ : syracuseStep 5248091 = 7872137) B7872137
theorem B3498727 : Blo 2071435 3498727 := bstep (se 1 (by rfl) ⟨2624045, by rfl⟩ : syracuseStep 3498727 = 5248091) B5248091
theorem B4664969 : Blo 2071435 4664969 := bstep (se 2 (by rfl) ⟨1749363, by rfl⟩ : syracuseStep 4664969 = 3498727) B3498727
theorem B3109979 : Blo 2071435 3109979 := bstep (se 1 (by rfl) ⟨2332484, by rfl⟩ : syracuseStep 3109979 = 4664969) B4664969
theorem B2073319 : Blo 2071435 2073319 := bstep (se 1 (by rfl) ⟨1554989, by rfl⟩ : syracuseStep 2073319 = 3109979) B3109979
theorem B2332489 : Blo 2071435 2332489 := bbase (se 2 (by rfl) ⟨874683, by rfl⟩ : syracuseStep 2332489 = 1749367) (by norm_num)
theorem B3109985 : Blo 2071435 3109985 := bstep (se 2 (by rfl) ⟨1166244, by rfl⟩ : syracuseStep 3109985 = 2332489) B2332489
theorem B2073323 : Blo 2071435 2073323 := bstep (se 1 (by rfl) ⟨1554992, by rfl⟩ : syracuseStep 2073323 = 3109985) B3109985
theorem B7979573 : Blo 2071435 7979573 := bbase (se 5 (by rfl) ⟨374042, by rfl⟩ : syracuseStep 7979573 = 748085) (by norm_num)
theorem B5319715 : Blo 2071435 5319715 := bstep (se 1 (by rfl) ⟨3989786, by rfl⟩ : syracuseStep 5319715 = 7979573) B7979573
theorem B7092953 : Blo 2071435 7092953 := bstep (se 2 (by rfl) ⟨2659857, by rfl⟩ : syracuseStep 7092953 = 5319715) B5319715
theorem B4728635 : Blo 2071435 4728635 := bstep (se 1 (by rfl) ⟨3546476, by rfl⟩ : syracuseStep 4728635 = 7092953) B7092953
theorem B3152423 : Blo 2071435 3152423 := bstep (se 1 (by rfl) ⟨2364317, by rfl⟩ : syracuseStep 3152423 = 4728635) B4728635
theorem B8406461 : Blo 2071435 8406461 := bstep (se 3 (by rfl) ⟨1576211, by rfl⟩ : syracuseStep 8406461 = 3152423) B3152423
theorem B22417229 : Blo 2071435 22417229 := bstep (se 3 (by rfl) ⟨4203230, by rfl⟩ : syracuseStep 22417229 = 8406461) B8406461
theorem B14944819 : Blo 2071435 14944819 := bstep (se 1 (by rfl) ⟨11208614, by rfl⟩ : syracuseStep 14944819 = 22417229) B22417229
theorem B19926425 : Blo 2071435 19926425 := bstep (se 2 (by rfl) ⟨7472409, by rfl⟩ : syracuseStep 19926425 = 14944819) B14944819
theorem B13284283 : Blo 2071435 13284283 := bstep (se 1 (by rfl) ⟨9963212, by rfl⟩ : syracuseStep 13284283 = 19926425) B19926425
theorem B17712377 : Blo 2071435 17712377 := bstep (se 2 (by rfl) ⟨6642141, by rfl⟩ : syracuseStep 17712377 = 13284283) B13284283
theorem B11808251 : Blo 2071435 11808251 := bstep (se 1 (by rfl) ⟨8856188, by rfl⟩ : syracuseStep 11808251 = 17712377) B17712377
theorem B7872167 : Blo 2071435 7872167 := bstep (se 1 (by rfl) ⟨5904125, by rfl⟩ : syracuseStep 7872167 = 11808251) B11808251
theorem B5248111 : Blo 2071435 5248111 := bstep (se 1 (by rfl) ⟨3936083, by rfl⟩ : syracuseStep 5248111 = 7872167) B7872167
theorem B6997481 : Blo 2071435 6997481 := bstep (se 2 (by rfl) ⟨2624055, by rfl⟩ : syracuseStep 6997481 = 5248111) B5248111
theorem B4664987 : Blo 2071435 4664987 := bstep (se 1 (by rfl) ⟨3498740, by rfl⟩ : syracuseStep 4664987 = 6997481) B6997481
theorem B3109991 : Blo 2071435 3109991 := bstep (se 1 (by rfl) ⟨2332493, by rfl⟩ : syracuseStep 3109991 = 4664987) B4664987
theorem B2073327 : Blo 2071435 2073327 := bstep (se 1 (by rfl) ⟨1554995, by rfl⟩ : syracuseStep 2073327 = 3109991) B3109991
theorem B3109997 : Blo 2071435 3109997 := bbase (se 3 (by rfl) ⟨583124, by rfl⟩ : syracuseStep 3109997 = 1166249) (by norm_num)
theorem B2073331 : Blo 2071435 2073331 := bstep (se 1 (by rfl) ⟨1554998, by rfl⟩ : syracuseStep 2073331 = 3109997) B3109997
theorem B4665005 : Blo 2071435 4665005 := bbase (se 3 (by rfl) ⟨874688, by rfl⟩ : syracuseStep 4665005 = 1749377) (by norm_num)
theorem B3110003 : Blo 2071435 3110003 := bstep (se 1 (by rfl) ⟨2332502, by rfl⟩ : syracuseStep 3110003 = 4665005) B4665005
theorem B2073335 : Blo 2071435 2073335 := bstep (se 1 (by rfl) ⟨1555001, by rfl⟩ : syracuseStep 2073335 = 3110003) B3110003
theorem B4981637 : Blo 2071435 4981637 := bbase (se 4 (by rfl) ⟨467028, by rfl⟩ : syracuseStep 4981637 = 934057) (by norm_num)
theorem B3321091 : Blo 2071435 3321091 := bstep (se 1 (by rfl) ⟨2490818, by rfl⟩ : syracuseStep 3321091 = 4981637) B4981637
theorem B4428121 : Blo 2071435 4428121 := bstep (se 2 (by rfl) ⟨1660545, by rfl⟩ : syracuseStep 4428121 = 3321091) B3321091
theorem B5904161 : Blo 2071435 5904161 := bstep (se 2 (by rfl) ⟨2214060, by rfl⟩ : syracuseStep 5904161 = 4428121) B4428121
theorem B3936107 : Blo 2071435 3936107 := bstep (se 1 (by rfl) ⟨2952080, by rfl⟩ : syracuseStep 3936107 = 5904161) B5904161
theorem B2624071 : Blo 2071435 2624071 := bstep (se 1 (by rfl) ⟨1968053, by rfl⟩ : syracuseStep 2624071 = 3936107) B3936107
theorem B3498761 : Blo 2071435 3498761 := bstep (se 2 (by rfl) ⟨1312035, by rfl⟩ : syracuseStep 3498761 = 2624071) B2624071
theorem B2332507 : Blo 2071435 2332507 := bstep (se 1 (by rfl) ⟨1749380, by rfl⟩ : syracuseStep 2332507 = 3498761) B3498761
theorem B3110009 : Blo 2071435 3110009 := bstep (se 2 (by rfl) ⟨1166253, by rfl⟩ : syracuseStep 3110009 = 2332507) B2332507
theorem B2073339 : Blo 2071435 2073339 := bstep (se 1 (by rfl) ⟨1555004, by rfl⟩ : syracuseStep 2073339 = 3110009) B3110009
theorem B10237013 : Blo 2071435 10237013 := bbase (se 8 (by rfl) ⟨59982, by rfl⟩ : syracuseStep 10237013 = 119965) (by norm_num)
theorem B6824675 : Blo 2071435 6824675 := bstep (se 1 (by rfl) ⟨5118506, by rfl⟩ : syracuseStep 6824675 = 10237013) B10237013
theorem B18199133 : Blo 2071435 18199133 := bstep (se 3 (by rfl) ⟨3412337, by rfl⟩ : syracuseStep 18199133 = 6824675) B6824675
theorem B12132755 : Blo 2071435 12132755 := bstep (se 1 (by rfl) ⟨9099566, by rfl⟩ : syracuseStep 12132755 = 18199133) B18199133
theorem B8088503 : Blo 2071435 8088503 := bstep (se 1 (by rfl) ⟨6066377, by rfl⟩ : syracuseStep 8088503 = 12132755) B12132755
theorem B21569341 : Blo 2071435 21569341 := bstep (se 3 (by rfl) ⟨4044251, by rfl⟩ : syracuseStep 21569341 = 8088503) B8088503
theorem B28759121 : Blo 2071435 28759121 := bstep (se 2 (by rfl) ⟨10784670, by rfl⟩ : syracuseStep 28759121 = 21569341) B21569341
theorem B19172747 : Blo 2071435 19172747 := bstep (se 1 (by rfl) ⟨14379560, by rfl⟩ : syracuseStep 19172747 = 28759121) B28759121
theorem B51127325 : Blo 2071435 51127325 := bstep (se 3 (by rfl) ⟨9586373, by rfl⟩ : syracuseStep 51127325 = 19172747) B19172747
theorem B34084883 : Blo 2071435 34084883 := bstep (se 1 (by rfl) ⟨25563662, by rfl⟩ : syracuseStep 34084883 = 51127325) B51127325
theorem B22723255 : Blo 2071435 22723255 := bstep (se 1 (by rfl) ⟨17042441, by rfl⟩ : syracuseStep 22723255 = 34084883) B34084883
theorem B30297673 : Blo 2071435 30297673 := bstep (se 2 (by rfl) ⟨11361627, by rfl⟩ : syracuseStep 30297673 = 22723255) B22723255
theorem B40396897 : Blo 2071435 40396897 := bstep (se 2 (by rfl) ⟨15148836, by rfl⟩ : syracuseStep 40396897 = 30297673) B30297673
theorem B53862529 : Blo 2071435 53862529 := bstep (se 2 (by rfl) ⟨20198448, by rfl⟩ : syracuseStep 53862529 = 40396897) B40396897
theorem B71816705 : Blo 2071435 71816705 := bstep (se 2 (by rfl) ⟨26931264, by rfl⟩ : syracuseStep 71816705 = 53862529) B53862529
theorem B47877803 : Blo 2071435 47877803 := bstep (se 1 (by rfl) ⟨35908352, by rfl⟩ : syracuseStep 47877803 = 71816705) B71816705
theorem B31918535 : Blo 2071435 31918535 := bstep (se 1 (by rfl) ⟨23938901, by rfl⟩ : syracuseStep 31918535 = 47877803) B47877803
theorem B21279023 : Blo 2071435 21279023 := bstep (se 1 (by rfl) ⟨15959267, by rfl⟩ : syracuseStep 21279023 = 31918535) B31918535
theorem B14186015 : Blo 2071435 14186015 := bstep (se 1 (by rfl) ⟨10639511, by rfl⟩ : syracuseStep 14186015 = 21279023) B21279023
theorem B9457343 : Blo 2071435 9457343 := bstep (se 1 (by rfl) ⟨7093007, by rfl⟩ : syracuseStep 9457343 = 14186015) B14186015
theorem B6304895 : Blo 2071435 6304895 := bstep (se 1 (by rfl) ⟨4728671, by rfl⟩ : syracuseStep 6304895 = 9457343) B9457343
theorem B4203263 : Blo 2071435 4203263 := bstep (se 1 (by rfl) ⟨3152447, by rfl⟩ : syracuseStep 4203263 = 6304895) B6304895
theorem B2802175 : Blo 2071435 2802175 := bstep (se 1 (by rfl) ⟨2101631, by rfl⟩ : syracuseStep 2802175 = 4203263) B4203263
theorem B14944933 : Blo 2071435 14944933 := bstep (se 4 (by rfl) ⟨1401087, by rfl⟩ : syracuseStep 14944933 = 2802175) B2802175
theorem B19926577 : Blo 2071435 19926577 := bstep (se 2 (by rfl) ⟨7472466, by rfl⟩ : syracuseStep 19926577 = 14944933) B14944933
theorem B26568769 : Blo 2071435 26568769 := bstep (se 2 (by rfl) ⟨9963288, by rfl⟩ : syracuseStep 26568769 = 19926577) B19926577
theorem B35425025 : Blo 2071435 35425025 := bstep (se 2 (by rfl) ⟨13284384, by rfl⟩ : syracuseStep 35425025 = 26568769) B26568769
theorem B23616683 : Blo 2071435 23616683 := bstep (se 1 (by rfl) ⟨17712512, by rfl⟩ : syracuseStep 23616683 = 35425025) B35425025
theorem B15744455 : Blo 2071435 15744455 := bstep (se 1 (by rfl) ⟨11808341, by rfl⟩ : syracuseStep 15744455 = 23616683) B23616683
theorem B10496303 : Blo 2071435 10496303 := bstep (se 1 (by rfl) ⟨7872227, by rfl⟩ : syracuseStep 10496303 = 15744455) B15744455
theorem B6997535 : Blo 2071435 6997535 := bstep (se 1 (by rfl) ⟨5248151, by rfl⟩ : syracuseStep 6997535 = 10496303) B10496303
theorem B4665023 : Blo 2071435 4665023 := bstep (se 1 (by rfl) ⟨3498767, by rfl⟩ : syracuseStep 4665023 = 6997535) B6997535
theorem B3110015 : Blo 2071435 3110015 := bstep (se 1 (by rfl) ⟨2332511, by rfl⟩ : syracuseStep 3110015 = 4665023) B4665023
theorem B2073343 : Blo 2071435 2073343 := bstep (se 1 (by rfl) ⟨1555007, by rfl⟩ : syracuseStep 2073343 = 3110015) B3110015
theorem B3110021 : Blo 2071435 3110021 := bbase (se 4 (by rfl) ⟨291564, by rfl⟩ : syracuseStep 3110021 = 583129) (by norm_num)
theorem B2073347 : Blo 2071435 2073347 := bstep (se 1 (by rfl) ⟨1555010, by rfl⟩ : syracuseStep 2073347 = 3110021) B3110021
theorem B3498781 : Blo 2071435 3498781 := bbase (se 3 (by rfl) ⟨656021, by rfl⟩ : syracuseStep 3498781 = 1312043) (by norm_num)
theorem B4665041 : Blo 2071435 4665041 := bstep (se 2 (by rfl) ⟨1749390, by rfl⟩ : syracuseStep 4665041 = 3498781) B3498781
theorem B3110027 : Blo 2071435 3110027 := bstep (se 1 (by rfl) ⟨2332520, by rfl⟩ : syracuseStep 3110027 = 4665041) B4665041
theorem B2073351 : Blo 2071435 2073351 := bstep (se 1 (by rfl) ⟨1555013, by rfl⟩ : syracuseStep 2073351 = 3110027) B3110027
theorem B2332525 : Blo 2071435 2332525 := bbase (se 3 (by rfl) ⟨437348, by rfl⟩ : syracuseStep 2332525 = 874697) (by norm_num)
theorem B3110033 : Blo 2071435 3110033 := bstep (se 2 (by rfl) ⟨1166262, by rfl⟩ : syracuseStep 3110033 = 2332525) B2332525
theorem B2073355 : Blo 2071435 2073355 := bstep (se 1 (by rfl) ⟨1555016, by rfl⟩ : syracuseStep 2073355 = 3110033) B3110033
theorem B6997589 : Blo 2071435 6997589 := bbase (se 8 (by rfl) ⟨41001, by rfl⟩ : syracuseStep 6997589 = 82003) (by norm_num)
theorem B4665059 : Blo 2071435 4665059 := bstep (se 1 (by rfl) ⟨3498794, by rfl⟩ : syracuseStep 4665059 = 6997589) B6997589
theorem B3110039 : Blo 2071435 3110039 := bstep (se 1 (by rfl) ⟨2332529, by rfl⟩ : syracuseStep 3110039 = 4665059) B4665059
theorem B2073359 : Blo 2071435 2073359 := bstep (se 1 (by rfl) ⟨1555019, by rfl⟩ : syracuseStep 2073359 = 3110039) B3110039
theorem B3110045 : Blo 2071435 3110045 := bbase (se 3 (by rfl) ⟨583133, by rfl⟩ : syracuseStep 3110045 = 1166267) (by norm_num)
theorem B2073363 : Blo 2071435 2073363 := bstep (se 1 (by rfl) ⟨1555022, by rfl⟩ : syracuseStep 2073363 = 3110045) B3110045
theorem B4665077 : Blo 2071435 4665077 := bbase (se 5 (by rfl) ⟨218675, by rfl⟩ : syracuseStep 4665077 = 437351) (by norm_num)
theorem B3110051 : Blo 2071435 3110051 := bstep (se 1 (by rfl) ⟨2332538, by rfl⟩ : syracuseStep 3110051 = 4665077) B4665077
theorem B2073367 : Blo 2071435 2073367 := bstep (se 1 (by rfl) ⟨1555025, by rfl⟩ : syracuseStep 2073367 = 3110051) B3110051
theorem B6304981 : Blo 2071435 6304981 := bbase (se 7 (by rfl) ⟨73886, by rfl⟩ : syracuseStep 6304981 = 147773) (by norm_num)
theorem B8406641 : Blo 2071435 8406641 := bstep (se 2 (by rfl) ⟨3152490, by rfl⟩ : syracuseStep 8406641 = 6304981) B6304981
theorem B5604427 : Blo 2071435 5604427 := bstep (se 1 (by rfl) ⟨4203320, by rfl⟩ : syracuseStep 5604427 = 8406641) B8406641
theorem B7472569 : Blo 2071435 7472569 := bstep (se 2 (by rfl) ⟨2802213, by rfl⟩ : syracuseStep 7472569 = 5604427) B5604427
theorem B9963425 : Blo 2071435 9963425 := bstep (se 2 (by rfl) ⟨3736284, by rfl⟩ : syracuseStep 9963425 = 7472569) B7472569
theorem B26569133 : Blo 2071435 26569133 := bstep (se 3 (by rfl) ⟨4981712, by rfl⟩ : syracuseStep 26569133 = 9963425) B9963425
theorem B17712755 : Blo 2071435 17712755 := bstep (se 1 (by rfl) ⟨13284566, by rfl⟩ : syracuseStep 17712755 = 26569133) B26569133
theorem B11808503 : Blo 2071435 11808503 := bstep (se 1 (by rfl) ⟨8856377, by rfl⟩ : syracuseStep 11808503 = 17712755) B17712755
theorem B7872335 : Blo 2071435 7872335 := bstep (se 1 (by rfl) ⟨5904251, by rfl⟩ : syracuseStep 7872335 = 11808503) B11808503
theorem B5248223 : Blo 2071435 5248223 := bstep (se 1 (by rfl) ⟨3936167, by rfl⟩ : syracuseStep 5248223 = 7872335) B7872335
theorem B3498815 : Blo 2071435 3498815 := bstep (se 1 (by rfl) ⟨2624111, by rfl⟩ : syracuseStep 3498815 = 5248223) B5248223
theorem B2332543 : Blo 2071435 2332543 := bstep (se 1 (by rfl) ⟨1749407, by rfl⟩ : syracuseStep 2332543 = 3498815) B3498815
theorem B3110057 : Blo 2071435 3110057 := bstep (se 2 (by rfl) ⟨1166271, by rfl⟩ : syracuseStep 3110057 = 2332543) B2332543
theorem B2073371 : Blo 2071435 2073371 := bstep (se 1 (by rfl) ⟨1555028, by rfl⟩ : syracuseStep 2073371 = 3110057) B3110057
theorem B4428197 : Blo 2071435 4428197 := bbase (se 4 (by rfl) ⟨415143, by rfl⟩ : syracuseStep 4428197 = 830287) (by norm_num)
theorem B2952131 : Blo 2071435 2952131 := bstep (se 1 (by rfl) ⟨2214098, by rfl⟩ : syracuseStep 2952131 = 4428197) B4428197
theorem B7872349 : Blo 2071435 7872349 := bstep (se 3 (by rfl) ⟨1476065, by rfl⟩ : syracuseStep 7872349 = 2952131) B2952131
theorem B10496465 : Blo 2071435 10496465 := bstep (se 2 (by rfl) ⟨3936174, by rfl⟩ : syracuseStep 10496465 = 7872349) B7872349
theorem B6997643 : Blo 2071435 6997643 := bstep (se 1 (by rfl) ⟨5248232, by rfl⟩ : syracuseStep 6997643 = 10496465) B10496465
theorem B4665095 : Blo 2071435 4665095 := bstep (se 1 (by rfl) ⟨3498821, by rfl⟩ : syracuseStep 4665095 = 6997643) B6997643
theorem B3110063 : Blo 2071435 3110063 := bstep (se 1 (by rfl) ⟨2332547, by rfl⟩ : syracuseStep 3110063 = 4665095) B4665095
theorem B2073375 : Blo 2071435 2073375 := bstep (se 1 (by rfl) ⟨1555031, by rfl⟩ : syracuseStep 2073375 = 3110063) B3110063
theorem B3110069 : Blo 2071435 3110069 := bbase (se 5 (by rfl) ⟨145784, by rfl⟩ : syracuseStep 3110069 = 291569) (by norm_num)
theorem B2073379 : Blo 2071435 2073379 := bstep (se 1 (by rfl) ⟨1555034, by rfl⟩ : syracuseStep 2073379 = 3110069) B3110069
theorem B5248253 : Blo 2071435 5248253 := bbase (se 3 (by rfl) ⟨984047, by rfl⟩ : syracuseStep 5248253 = 1968095) (by norm_num)
theorem B3498835 : Blo 2071435 3498835 := bstep (se 1 (by rfl) ⟨2624126, by rfl⟩ : syracuseStep 3498835 = 5248253) B5248253
theorem B4665113 : Blo 2071435 4665113 := bstep (se 2 (by rfl) ⟨1749417, by rfl⟩ : syracuseStep 4665113 = 3498835) B3498835
theorem B3110075 : Blo 2071435 3110075 := bstep (se 1 (by rfl) ⟨2332556, by rfl⟩ : syracuseStep 3110075 = 4665113) B4665113
theorem B2073383 : Blo 2071435 2073383 := bstep (se 1 (by rfl) ⟨1555037, by rfl⟩ : syracuseStep 2073383 = 3110075) B3110075
theorem B2332561 : Blo 2071435 2332561 := bbase (se 2 (by rfl) ⟨874710, by rfl⟩ : syracuseStep 2332561 = 1749421) (by norm_num)
theorem B3110081 : Blo 2071435 3110081 := bstep (se 2 (by rfl) ⟨1166280, by rfl⟩ : syracuseStep 3110081 = 2332561) B2332561
theorem B2073387 : Blo 2071435 2073387 := bstep (se 1 (by rfl) ⟨1555040, by rfl⟩ : syracuseStep 2073387 = 3110081) B3110081
theorem B3936205 : Blo 2071435 3936205 := bbase (se 3 (by rfl) ⟨738038, by rfl⟩ : syracuseStep 3936205 = 1476077) (by norm_num)
theorem B5248273 : Blo 2071435 5248273 := bstep (se 2 (by rfl) ⟨1968102, by rfl⟩ : syracuseStep 5248273 = 3936205) B3936205
theorem B6997697 : Blo 2071435 6997697 := bstep (se 2 (by rfl) ⟨2624136, by rfl⟩ : syracuseStep 6997697 = 5248273) B5248273
theorem B4665131 : Blo 2071435 4665131 := bstep (se 1 (by rfl) ⟨3498848, by rfl⟩ : syracuseStep 4665131 = 6997697) B6997697
theorem B3110087 : Blo 2071435 3110087 := bstep (se 1 (by rfl) ⟨2332565, by rfl⟩ : syracuseStep 3110087 = 4665131) B4665131
theorem B2073391 : Blo 2071435 2073391 := bstep (se 1 (by rfl) ⟨1555043, by rfl⟩ : syracuseStep 2073391 = 3110087) B3110087
theorem B3110093 : Blo 2071435 3110093 := bbase (se 3 (by rfl) ⟨583142, by rfl⟩ : syracuseStep 3110093 = 1166285) (by norm_num)
theorem B2073395 : Blo 2071435 2073395 := bstep (se 1 (by rfl) ⟨1555046, by rfl⟩ : syracuseStep 2073395 = 3110093) B3110093
theorem B4665149 : Blo 2071435 4665149 := bbase (se 3 (by rfl) ⟨874715, by rfl⟩ : syracuseStep 4665149 = 1749431) (by norm_num)
theorem B3110099 : Blo 2071435 3110099 := bstep (se 1 (by rfl) ⟨2332574, by rfl⟩ : syracuseStep 3110099 = 4665149) B4665149
theorem B2073399 : Blo 2071435 2073399 := bstep (se 1 (by rfl) ⟨1555049, by rfl⟩ : syracuseStep 2073399 = 3110099) B3110099
theorem B3498869 : Blo 2071435 3498869 := bbase (se 5 (by rfl) ⟨164009, by rfl⟩ : syracuseStep 3498869 = 328019) (by norm_num)
theorem B2332579 : Blo 2071435 2332579 := bstep (se 1 (by rfl) ⟨1749434, by rfl⟩ : syracuseStep 2332579 = 3498869) B3498869
theorem B3110105 : Blo 2071435 3110105 := bstep (se 2 (by rfl) ⟨1166289, by rfl⟩ : syracuseStep 3110105 = 2332579) B2332579
theorem B2073403 : Blo 2071435 2073403 := bstep (se 1 (by rfl) ⟨1555052, by rfl⟩ : syracuseStep 2073403 = 3110105) B3110105
theorem B2364409 : Blo 2071435 2364409 := bbase (se 2 (by rfl) ⟨886653, by rfl⟩ : syracuseStep 2364409 = 1773307) (by norm_num)
theorem B12610181 : Blo 2071435 12610181 := bstep (se 4 (by rfl) ⟨1182204, by rfl⟩ : syracuseStep 12610181 = 2364409) B2364409
theorem B8406787 : Blo 2071435 8406787 := bstep (se 1 (by rfl) ⟨6305090, by rfl⟩ : syracuseStep 8406787 = 12610181) B12610181
theorem B11209049 : Blo 2071435 11209049 := bstep (se 2 (by rfl) ⟨4203393, by rfl⟩ : syracuseStep 11209049 = 8406787) B8406787
theorem B7472699 : Blo 2071435 7472699 := bstep (se 1 (by rfl) ⟨5604524, by rfl⟩ : syracuseStep 7472699 = 11209049) B11209049
theorem B4981799 : Blo 2071435 4981799 := bstep (se 1 (by rfl) ⟨3736349, by rfl⟩ : syracuseStep 4981799 = 7472699) B7472699
theorem B3321199 : Blo 2071435 3321199 := bstep (se 1 (by rfl) ⟨2490899, by rfl⟩ : syracuseStep 3321199 = 4981799) B4981799
theorem B4428265 : Blo 2071435 4428265 := bstep (se 2 (by rfl) ⟨1660599, by rfl⟩ : syracuseStep 4428265 = 3321199) B3321199
theorem B5904353 : Blo 2071435 5904353 := bstep (se 2 (by rfl) ⟨2214132, by rfl⟩ : syracuseStep 5904353 = 4428265) B4428265
theorem B15744941 : Blo 2071435 15744941 := bstep (se 3 (by rfl) ⟨2952176, by rfl⟩ : syracuseStep 15744941 = 5904353) B5904353
theorem B10496627 : Blo 2071435 10496627 := bstep (se 1 (by rfl) ⟨7872470, by rfl⟩ : syracuseStep 10496627 = 15744941) B15744941
theorem B6997751 : Blo 2071435 6997751 := bstep (se 1 (by rfl) ⟨5248313, by rfl⟩ : syracuseStep 6997751 = 10496627) B10496627
theorem B4665167 : Blo 2071435 4665167 := bstep (se 1 (by rfl) ⟨3498875, by rfl⟩ : syracuseStep 4665167 = 6997751) B6997751
theorem B3110111 : Blo 2071435 3110111 := bstep (se 1 (by rfl) ⟨2332583, by rfl⟩ : syracuseStep 3110111 = 4665167) B4665167
theorem B2073407 : Blo 2071435 2073407 := bstep (se 1 (by rfl) ⟨1555055, by rfl⟩ : syracuseStep 2073407 = 3110111) B3110111
theorem B3110117 : Blo 2071435 3110117 := bbase (se 4 (by rfl) ⟨291573, by rfl⟩ : syracuseStep 3110117 = 583147) (by norm_num)
theorem B2073411 : Blo 2071435 2073411 := bstep (se 1 (by rfl) ⟨1555058, by rfl⟩ : syracuseStep 2073411 = 3110117) B3110117
theorem B8406821 : Blo 2071435 8406821 := bbase (se 4 (by rfl) ⟨788139, by rfl⟩ : syracuseStep 8406821 = 1576279) (by norm_num)
theorem B5604547 : Blo 2071435 5604547 := bstep (se 1 (by rfl) ⟨4203410, by rfl⟩ : syracuseStep 5604547 = 8406821) B8406821
theorem B7472729 : Blo 2071435 7472729 := bstep (se 2 (by rfl) ⟨2802273, by rfl⟩ : syracuseStep 7472729 = 5604547) B5604547
theorem B4981819 : Blo 2071435 4981819 := bstep (se 1 (by rfl) ⟨3736364, by rfl⟩ : syracuseStep 4981819 = 7472729) B7472729
theorem B6642425 : Blo 2071435 6642425 := bstep (se 2 (by rfl) ⟨2490909, by rfl⟩ : syracuseStep 6642425 = 4981819) B4981819
theorem B4428283 : Blo 2071435 4428283 := bstep (se 1 (by rfl) ⟨3321212, by rfl⟩ : syracuseStep 4428283 = 6642425) B6642425
theorem B5904377 : Blo 2071435 5904377 := bstep (se 2 (by rfl) ⟨2214141, by rfl⟩ : syracuseStep 5904377 = 4428283) B4428283
theorem B3936251 : Blo 2071435 3936251 := bstep (se 1 (by rfl) ⟨2952188, by rfl⟩ : syracuseStep 3936251 = 5904377) B5904377
theorem B2624167 : Blo 2071435 2624167 := bstep (se 1 (by rfl) ⟨1968125, by rfl⟩ : syracuseStep 2624167 = 3936251) B3936251
theorem B3498889 : Blo 2071435 3498889 := bstep (se 2 (by rfl) ⟨1312083, by rfl⟩ : syracuseStep 3498889 = 2624167) B2624167
theorem B4665185 : Blo 2071435 4665185 := bstep (se 2 (by rfl) ⟨1749444, by rfl⟩ : syracuseStep 4665185 = 3498889) B3498889
theorem B3110123 : Blo 2071435 3110123 := bstep (se 1 (by rfl) ⟨2332592, by rfl⟩ : syracuseStep 3110123 = 4665185) B4665185
theorem B2073415 : Blo 2071435 2073415 := bstep (se 1 (by rfl) ⟨1555061, by rfl⟩ : syracuseStep 2073415 = 3110123) B3110123
theorem B2332597 : Blo 2071435 2332597 := bbase (se 5 (by rfl) ⟨109340, by rfl⟩ : syracuseStep 2332597 = 218681) (by norm_num)
theorem B3110129 : Blo 2071435 3110129 := bstep (se 2 (by rfl) ⟨1166298, by rfl⟩ : syracuseStep 3110129 = 2332597) B2332597
theorem B2073419 : Blo 2071435 2073419 := bstep (se 1 (by rfl) ⟨1555064, by rfl⟩ : syracuseStep 2073419 = 3110129) B3110129
theorem B2624177 : Blo 2071435 2624177 := bbase (se 2 (by rfl) ⟨984066, by rfl⟩ : syracuseStep 2624177 = 1968133) (by norm_num)
theorem B6997805 : Blo 2071435 6997805 := bstep (se 3 (by rfl) ⟨1312088, by rfl⟩ : syracuseStep 6997805 = 2624177) B2624177
theorem B4665203 : Blo 2071435 4665203 := bstep (se 1 (by rfl) ⟨3498902, by rfl⟩ : syracuseStep 4665203 = 6997805) B6997805
theorem B3110135 : Blo 2071435 3110135 := bstep (se 1 (by rfl) ⟨2332601, by rfl⟩ : syracuseStep 3110135 = 4665203) B4665203
theorem B2073423 : Blo 2071435 2073423 := bstep (se 1 (by rfl) ⟨1555067, by rfl⟩ : syracuseStep 2073423 = 3110135) B3110135
theorem B3110141 : Blo 2071435 3110141 := bbase (se 3 (by rfl) ⟨583151, by rfl⟩ : syracuseStep 3110141 = 1166303) (by norm_num)
theorem B2073427 : Blo 2071435 2073427 := bstep (se 1 (by rfl) ⟨1555070, by rfl⟩ : syracuseStep 2073427 = 3110141) B3110141
theorem B4665221 : Blo 2071435 4665221 := bbase (se 4 (by rfl) ⟨437364, by rfl⟩ : syracuseStep 4665221 = 874729) (by norm_num)
theorem B3110147 : Blo 2071435 3110147 := bstep (se 1 (by rfl) ⟨2332610, by rfl⟩ : syracuseStep 3110147 = 4665221) B4665221
theorem B2073431 : Blo 2071435 2073431 := bstep (se 1 (by rfl) ⟨1555073, by rfl⟩ : syracuseStep 2073431 = 3110147) B3110147
theorem B3321245 : Blo 2071435 3321245 := bbase (se 3 (by rfl) ⟨622733, by rfl⟩ : syracuseStep 3321245 = 1245467) (by norm_num)
theorem B2214163 : Blo 2071435 2214163 := bstep (se 1 (by rfl) ⟨1660622, by rfl⟩ : syracuseStep 2214163 = 3321245) B3321245
theorem B2952217 : Blo 2071435 2952217 := bstep (se 2 (by rfl) ⟨1107081, by rfl⟩ : syracuseStep 2952217 = 2214163) B2214163
theorem B3936289 : Blo 2071435 3936289 := bstep (se 2 (by rfl) ⟨1476108, by rfl⟩ : syracuseStep 3936289 = 2952217) B2952217
theorem B5248385 : Blo 2071435 5248385 := bstep (se 2 (by rfl) ⟨1968144, by rfl⟩ : syracuseStep 5248385 = 3936289) B3936289
theorem B3498923 : Blo 2071435 3498923 := bstep (se 1 (by rfl) ⟨2624192, by rfl⟩ : syracuseStep 3498923 = 5248385) B5248385
theorem B2332615 : Blo 2071435 2332615 := bstep (se 1 (by rfl) ⟨1749461, by rfl⟩ : syracuseStep 2332615 = 3498923) B3498923
theorem B3110153 : Blo 2071435 3110153 := bstep (se 2 (by rfl) ⟨1166307, by rfl⟩ : syracuseStep 3110153 = 2332615) B2332615
theorem B2073435 : Blo 2071435 2073435 := bstep (se 1 (by rfl) ⟨1555076, by rfl⟩ : syracuseStep 2073435 = 3110153) B3110153
theorem C0 (j : ℕ) (h1 : 517858 ≤ j) (h2 : j ≤ 518358) : Blo 2071435 (4 * j + 3) := by
  interval_cases j
  · exact B2071435
  · exact B2071439
  · exact B2071443
  · exact B2071447
  · exact B2071451
  · exact B2071455
  · exact B2071459
  · exact B2071463
  · exact B2071467
  · exact B2071471
  · exact B2071475
  · exact B2071479
  · exact B2071483
  · exact B2071487
  · exact B2071491
  · exact B2071495
  · exact B2071499
  · exact B2071503
  · exact B2071507
  · exact B2071511
  · exact B2071515
  · exact B2071519
  · exact B2071523
  · exact B2071527
  · exact B2071531
  · exact B2071535
  · exact B2071539
  · exact B2071543
  · exact B2071547
  · exact B2071551
  · exact B2071555
  · exact B2071559
  · exact B2071563
  · exact B2071567
  · exact B2071571
  · exact B2071575
  · exact B2071579
  · exact B2071583
  · exact B2071587
  · exact B2071591
  · exact B2071595
  · exact B2071599
  · exact B2071603
  · exact B2071607
  · exact B2071611
  · exact B2071615
  · exact B2071619
  · exact B2071623
  · exact B2071627
  · exact B2071631
  · exact B2071635
  · exact B2071639
  · exact B2071643
  · exact B2071647
  · exact B2071651
  · exact B2071655
  · exact B2071659
  · exact B2071663
  · exact B2071667
  · exact B2071671
  · exact B2071675
  · exact B2071679
  · exact B2071683
  · exact B2071687
  · exact B2071691
  · exact B2071695
  · exact B2071699
  · exact B2071703
  · exact B2071707
  · exact B2071711
  · exact B2071715
  · exact B2071719
  · exact B2071723
  · exact B2071727
  · exact B2071731
  · exact B2071735
  · exact B2071739
  · exact B2071743
  · exact B2071747
  · exact B2071751
  · exact B2071755
  · exact B2071759
  · exact B2071763
  · exact B2071767
  · exact B2071771
  · exact B2071775
  · exact B2071779
  · exact B2071783
  · exact B2071787
  · exact B2071791
  · exact B2071795
  · exact B2071799
  · exact B2071803
  · exact B2071807
  · exact B2071811
  · exact B2071815
  · exact B2071819
  · exact B2071823
  · exact B2071827
  · exact B2071831
  · exact B2071835
  · exact B2071839
  · exact B2071843
  · exact B2071847
  · exact B2071851
  · exact B2071855
  · exact B2071859
  · exact B2071863
  · exact B2071867
  · exact B2071871
  · exact B2071875
  · exact B2071879
  · exact B2071883
  · exact B2071887
  · exact B2071891
  · exact B2071895
  · exact B2071899
  · exact B2071903
  · exact B2071907
  · exact B2071911
  · exact B2071915
  · exact B2071919
  · exact B2071923
  · exact B2071927
  · exact B2071931
  · exact B2071935
  · exact B2071939
  · exact B2071943
  · exact B2071947
  · exact B2071951
  · exact B2071955
  · exact B2071959
  · exact B2071963
  · exact B2071967
  · exact B2071971
  · exact B2071975
  · exact B2071979
  · exact B2071983
  · exact B2071987
  · exact B2071991
  · exact B2071995
  · exact B2071999
  · exact B2072003
  · exact B2072007
  · exact B2072011
  · exact B2072015
  · exact B2072019
  · exact B2072023
  · exact B2072027
  · exact B2072031
  · exact B2072035
  · exact B2072039
  · exact B2072043
  · exact B2072047
  · exact B2072051
  · exact B2072055
  · exact B2072059
  · exact B2072063
  · exact B2072067
  · exact B2072071
  · exact B2072075
  · exact B2072079
  · exact B2072083
  · exact B2072087
  · exact B2072091
  · exact B2072095
  · exact B2072099
  · exact B2072103
  · exact B2072107
  · exact B2072111
  · exact B2072115
  · exact B2072119
  · exact B2072123
  · exact B2072127
  · exact B2072131
  · exact B2072135
  · exact B2072139
  · exact B2072143
  · exact B2072147
  · exact B2072151
  · exact B2072155
  · exact B2072159
  · exact B2072163
  · exact B2072167
  · exact B2072171
  · exact B2072175
  · exact B2072179
  · exact B2072183
  · exact B2072187
  · exact B2072191
  · exact B2072195
  · exact B2072199
  · exact B2072203
  · exact B2072207
  · exact B2072211
  · exact B2072215
  · exact B2072219
  · exact B2072223
  · exact B2072227
  · exact B2072231
  · exact B2072235
  · exact B2072239
  · exact B2072243
  · exact B2072247
  · exact B2072251
  · exact B2072255
  · exact B2072259
  · exact B2072263
  · exact B2072267
  · exact B2072271
  · exact B2072275
  · exact B2072279
  · exact B2072283
  · exact B2072287
  · exact B2072291
  · exact B2072295
  · exact B2072299
  · exact B2072303
  · exact B2072307
  · exact B2072311
  · exact B2072315
  · exact B2072319
  · exact B2072323
  · exact B2072327
  · exact B2072331
  · exact B2072335
  · exact B2072339
  · exact B2072343
  · exact B2072347
  · exact B2072351
  · exact B2072355
  · exact B2072359
  · exact B2072363
  · exact B2072367
  · exact B2072371
  · exact B2072375
  · exact B2072379
  · exact B2072383
  · exact B2072387
  · exact B2072391
  · exact B2072395
  · exact B2072399
  · exact B2072403
  · exact B2072407
  · exact B2072411
  · exact B2072415
  · exact B2072419
  · exact B2072423
  · exact B2072427
  · exact B2072431
  · exact B2072435
  · exact B2072439
  · exact B2072443
  · exact B2072447
  · exact B2072451
  · exact B2072455
  · exact B2072459
  · exact B2072463
  · exact B2072467
  · exact B2072471
  · exact B2072475
  · exact B2072479
  · exact B2072483
  · exact B2072487
  · exact B2072491
  · exact B2072495
  · exact B2072499
  · exact B2072503
  · exact B2072507
  · exact B2072511
  · exact B2072515
  · exact B2072519
  · exact B2072523
  · exact B2072527
  · exact B2072531
  · exact B2072535
  · exact B2072539
  · exact B2072543
  · exact B2072547
  · exact B2072551
  · exact B2072555
  · exact B2072559
  · exact B2072563
  · exact B2072567
  · exact B2072571
  · exact B2072575
  · exact B2072579
  · exact B2072583
  · exact B2072587
  · exact B2072591
  · exact B2072595
  · exact B2072599
  · exact B2072603
  · exact B2072607
  · exact B2072611
  · exact B2072615
  · exact B2072619
  · exact B2072623
  · exact B2072627
  · exact B2072631
  · exact B2072635
  · exact B2072639
  · exact B2072643
  · exact B2072647
  · exact B2072651
  · exact B2072655
  · exact B2072659
  · exact B2072663
  · exact B2072667
  · exact B2072671
  · exact B2072675
  · exact B2072679
  · exact B2072683
  · exact B2072687
  · exact B2072691
  · exact B2072695
  · exact B2072699
  · exact B2072703
  · exact B2072707
  · exact B2072711
  · exact B2072715
  · exact B2072719
  · exact B2072723
  · exact B2072727
  · exact B2072731
  · exact B2072735
  · exact B2072739
  · exact B2072743
  · exact B2072747
  · exact B2072751
  · exact B2072755
  · exact B2072759
  · exact B2072763
  · exact B2072767
  · exact B2072771
  · exact B2072775
  · exact B2072779
  · exact B2072783
  · exact B2072787
  · exact B2072791
  · exact B2072795
  · exact B2072799
  · exact B2072803
  · exact B2072807
  · exact B2072811
  · exact B2072815
  · exact B2072819
  · exact B2072823
  · exact B2072827
  · exact B2072831
  · exact B2072835
  · exact B2072839
  · exact B2072843
  · exact B2072847
  · exact B2072851
  · exact B2072855
  · exact B2072859
  · exact B2072863
  · exact B2072867
  · exact B2072871
  · exact B2072875
  · exact B2072879
  · exact B2072883
  · exact B2072887
  · exact B2072891
  · exact B2072895
  · exact B2072899
  · exact B2072903
  · exact B2072907
  · exact B2072911
  · exact B2072915
  · exact B2072919
  · exact B2072923
  · exact B2072927
  · exact B2072931
  · exact B2072935
  · exact B2072939
  · exact B2072943
  · exact B2072947
  · exact B2072951
  · exact B2072955
  · exact B2072959
  · exact B2072963
  · exact B2072967
  · exact B2072971
  · exact B2072975
  · exact B2072979
  · exact B2072983
  · exact B2072987
  · exact B2072991
  · exact B2072995
  · exact B2072999
  · exact B2073003
  · exact B2073007
  · exact B2073011
  · exact B2073015
  · exact B2073019
  · exact B2073023
  · exact B2073027
  · exact B2073031
  · exact B2073035
  · exact B2073039
  · exact B2073043
  · exact B2073047
  · exact B2073051
  · exact B2073055
  · exact B2073059
  · exact B2073063
  · exact B2073067
  · exact B2073071
  · exact B2073075
  · exact B2073079
  · exact B2073083
  · exact B2073087
  · exact B2073091
  · exact B2073095
  · exact B2073099
  · exact B2073103
  · exact B2073107
  · exact B2073111
  · exact B2073115
  · exact B2073119
  · exact B2073123
  · exact B2073127
  · exact B2073131
  · exact B2073135
  · exact B2073139
  · exact B2073143
  · exact B2073147
  · exact B2073151
  · exact B2073155
  · exact B2073159
  · exact B2073163
  · exact B2073167
  · exact B2073171
  · exact B2073175
  · exact B2073179
  · exact B2073183
  · exact B2073187
  · exact B2073191
  · exact B2073195
  · exact B2073199
  · exact B2073203
  · exact B2073207
  · exact B2073211
  · exact B2073215
  · exact B2073219
  · exact B2073223
  · exact B2073227
  · exact B2073231
  · exact B2073235
  · exact B2073239
  · exact B2073243
  · exact B2073247
  · exact B2073251
  · exact B2073255
  · exact B2073259
  · exact B2073263
  · exact B2073267
  · exact B2073271
  · exact B2073275
  · exact B2073279
  · exact B2073283
  · exact B2073287
  · exact B2073291
  · exact B2073295
  · exact B2073299
  · exact B2073303
  · exact B2073307
  · exact B2073311
  · exact B2073315
  · exact B2073319
  · exact B2073323
  · exact B2073327
  · exact B2073331
  · exact B2073335
  · exact B2073339
  · exact B2073343
  · exact B2073347
  · exact B2073351
  · exact B2073355
  · exact B2073359
  · exact B2073363
  · exact B2073367
  · exact B2073371
  · exact B2073375
  · exact B2073379
  · exact B2073383
  · exact B2073387
  · exact B2073391
  · exact B2073395
  · exact B2073399
  · exact B2073403
  · exact B2073407
  · exact B2073411
  · exact B2073415
  · exact B2073419
  · exact B2073423
  · exact B2073427
  · exact B2073431
  · exact B2073435
theorem solution (m : ℕ) (hlo : 2071435 ≤ m) (hhi : m ≤ 2073435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 517858 ≤ j := by omega
    have hj2 : j ≤ 518358 := by omega
    have hb : Blo 2071435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
