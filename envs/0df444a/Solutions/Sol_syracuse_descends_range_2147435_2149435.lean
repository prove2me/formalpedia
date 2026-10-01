-- Prove2me | solution 1 for syracuse_descends_range_2147435_2149435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:24.586684+00:00
-- url     : https://prove2.me/submissions/b321401a-5403-418e-ac57-12cf49e8e9b3

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

theorem B2415865 : Blo 2147435 2415865 := bbase (se 2 (by rfl) ⟨905949, by rfl⟩ : syracuseStep 2415865 = 1811899) (by norm_num)
theorem B3221153 : Blo 2147435 3221153 := bstep (se 2 (by rfl) ⟨1207932, by rfl⟩ : syracuseStep 3221153 = 2415865) B2415865
theorem B2147435 : Blo 2147435 2147435 := bstep (se 1 (by rfl) ⟨1610576, by rfl⟩ : syracuseStep 2147435 = 3221153) B3221153
theorem B9172757 : Blo 2147435 9172757 := bbase (se 6 (by rfl) ⟨214986, by rfl⟩ : syracuseStep 9172757 = 429973) (by norm_num)
theorem B6115171 : Blo 2147435 6115171 := bstep (se 1 (by rfl) ⟨4586378, by rfl⟩ : syracuseStep 6115171 = 9172757) B9172757
theorem B8153561 : Blo 2147435 8153561 := bstep (se 2 (by rfl) ⟨3057585, by rfl⟩ : syracuseStep 8153561 = 6115171) B6115171
theorem B5435707 : Blo 2147435 5435707 := bstep (se 1 (by rfl) ⟨4076780, by rfl⟩ : syracuseStep 5435707 = 8153561) B8153561
theorem B7247609 : Blo 2147435 7247609 := bstep (se 2 (by rfl) ⟨2717853, by rfl⟩ : syracuseStep 7247609 = 5435707) B5435707
theorem B4831739 : Blo 2147435 4831739 := bstep (se 1 (by rfl) ⟨3623804, by rfl⟩ : syracuseStep 4831739 = 7247609) B7247609
theorem B3221159 : Blo 2147435 3221159 := bstep (se 1 (by rfl) ⟨2415869, by rfl⟩ : syracuseStep 3221159 = 4831739) B4831739
theorem B2147439 : Blo 2147435 2147439 := bstep (se 1 (by rfl) ⟨1610579, by rfl⟩ : syracuseStep 2147439 = 3221159) B3221159
theorem B3221165 : Blo 2147435 3221165 := bbase (se 3 (by rfl) ⟨603968, by rfl⟩ : syracuseStep 3221165 = 1207937) (by norm_num)
theorem B2147443 : Blo 2147435 2147443 := bstep (se 1 (by rfl) ⟨1610582, by rfl⟩ : syracuseStep 2147443 = 3221165) B3221165
theorem B4831757 : Blo 2147435 4831757 := bbase (se 3 (by rfl) ⟨905954, by rfl⟩ : syracuseStep 4831757 = 1811909) (by norm_num)
theorem B3221171 : Blo 2147435 3221171 := bstep (se 1 (by rfl) ⟨2415878, by rfl⟩ : syracuseStep 3221171 = 4831757) B4831757
theorem B2147447 : Blo 2147435 2147447 := bstep (se 1 (by rfl) ⟨1610585, by rfl⟩ : syracuseStep 2147447 = 3221171) B3221171
theorem B2717869 : Blo 2147435 2717869 := bbase (se 3 (by rfl) ⟨509600, by rfl⟩ : syracuseStep 2717869 = 1019201) (by norm_num)
theorem B3623825 : Blo 2147435 3623825 := bstep (se 2 (by rfl) ⟨1358934, by rfl⟩ : syracuseStep 3623825 = 2717869) B2717869
theorem B2415883 : Blo 2147435 2415883 := bstep (se 1 (by rfl) ⟨1811912, by rfl⟩ : syracuseStep 2415883 = 3623825) B3623825
theorem B3221177 : Blo 2147435 3221177 := bstep (se 2 (by rfl) ⟨1207941, by rfl⟩ : syracuseStep 3221177 = 2415883) B2415883
theorem B2147451 : Blo 2147435 2147451 := bstep (se 1 (by rfl) ⟨1610588, by rfl⟩ : syracuseStep 2147451 = 3221177) B3221177
theorem B2579857 : Blo 2147435 2579857 := bbase (se 2 (by rfl) ⟨967446, by rfl⟩ : syracuseStep 2579857 = 1934893) (by norm_num)
theorem B13759237 : Blo 2147435 13759237 := bstep (se 4 (by rfl) ⟨1289928, by rfl⟩ : syracuseStep 13759237 = 2579857) B2579857
theorem B18345649 : Blo 2147435 18345649 := bstep (se 2 (by rfl) ⟨6879618, by rfl⟩ : syracuseStep 18345649 = 13759237) B13759237
theorem B24460865 : Blo 2147435 24460865 := bstep (se 2 (by rfl) ⟨9172824, by rfl⟩ : syracuseStep 24460865 = 18345649) B18345649
theorem B16307243 : Blo 2147435 16307243 := bstep (se 1 (by rfl) ⟨12230432, by rfl⟩ : syracuseStep 16307243 = 24460865) B24460865
theorem B10871495 : Blo 2147435 10871495 := bstep (se 1 (by rfl) ⟨8153621, by rfl⟩ : syracuseStep 10871495 = 16307243) B16307243
theorem B7247663 : Blo 2147435 7247663 := bstep (se 1 (by rfl) ⟨5435747, by rfl⟩ : syracuseStep 7247663 = 10871495) B10871495
theorem B4831775 : Blo 2147435 4831775 := bstep (se 1 (by rfl) ⟨3623831, by rfl⟩ : syracuseStep 4831775 = 7247663) B7247663
theorem B3221183 : Blo 2147435 3221183 := bstep (se 1 (by rfl) ⟨2415887, by rfl⟩ : syracuseStep 3221183 = 4831775) B4831775
theorem B2147455 : Blo 2147435 2147455 := bstep (se 1 (by rfl) ⟨1610591, by rfl⟩ : syracuseStep 2147455 = 3221183) B3221183
theorem B3221189 : Blo 2147435 3221189 := bbase (se 4 (by rfl) ⟨301986, by rfl⟩ : syracuseStep 3221189 = 603973) (by norm_num)
theorem B2147459 : Blo 2147435 2147459 := bstep (se 1 (by rfl) ⟨1610594, by rfl⟩ : syracuseStep 2147459 = 3221189) B3221189
theorem B3623845 : Blo 2147435 3623845 := bbase (se 4 (by rfl) ⟨339735, by rfl⟩ : syracuseStep 3623845 = 679471) (by norm_num)
theorem B4831793 : Blo 2147435 4831793 := bstep (se 2 (by rfl) ⟨1811922, by rfl⟩ : syracuseStep 4831793 = 3623845) B3623845
theorem B3221195 : Blo 2147435 3221195 := bstep (se 1 (by rfl) ⟨2415896, by rfl⟩ : syracuseStep 3221195 = 4831793) B4831793
theorem B2147463 : Blo 2147435 2147463 := bstep (se 1 (by rfl) ⟨1610597, by rfl⟩ : syracuseStep 2147463 = 3221195) B3221195
theorem B2415901 : Blo 2147435 2415901 := bbase (se 3 (by rfl) ⟨452981, by rfl⟩ : syracuseStep 2415901 = 905963) (by norm_num)
theorem B3221201 : Blo 2147435 3221201 := bstep (se 2 (by rfl) ⟨1207950, by rfl⟩ : syracuseStep 3221201 = 2415901) B2415901
theorem B2147467 : Blo 2147435 2147467 := bstep (se 1 (by rfl) ⟨1610600, by rfl⟩ : syracuseStep 2147467 = 3221201) B3221201
theorem B7247717 : Blo 2147435 7247717 := bbase (se 4 (by rfl) ⟨679473, by rfl⟩ : syracuseStep 7247717 = 1358947) (by norm_num)
theorem B4831811 : Blo 2147435 4831811 := bstep (se 1 (by rfl) ⟨3623858, by rfl⟩ : syracuseStep 4831811 = 7247717) B7247717
theorem B3221207 : Blo 2147435 3221207 := bstep (se 1 (by rfl) ⟨2415905, by rfl⟩ : syracuseStep 3221207 = 4831811) B4831811
theorem B2147471 : Blo 2147435 2147471 := bstep (se 1 (by rfl) ⟨1610603, by rfl⟩ : syracuseStep 2147471 = 3221207) B3221207
theorem B3221213 : Blo 2147435 3221213 := bbase (se 3 (by rfl) ⟨603977, by rfl⟩ : syracuseStep 3221213 = 1207955) (by norm_num)
theorem B2147475 : Blo 2147435 2147475 := bstep (se 1 (by rfl) ⟨1610606, by rfl⟩ : syracuseStep 2147475 = 3221213) B3221213
theorem B4831829 : Blo 2147435 4831829 := bbase (se 8 (by rfl) ⟨28311, by rfl⟩ : syracuseStep 4831829 = 56623) (by norm_num)
theorem B3221219 : Blo 2147435 3221219 := bstep (se 1 (by rfl) ⟨2415914, by rfl⟩ : syracuseStep 3221219 = 4831829) B4831829
theorem B2147479 : Blo 2147435 2147479 := bstep (se 1 (by rfl) ⟨1610609, by rfl⟩ : syracuseStep 2147479 = 3221219) B3221219
theorem B5230181 : Blo 2147435 5230181 := bbase (se 4 (by rfl) ⟨490329, by rfl⟩ : syracuseStep 5230181 = 980659) (by norm_num)
theorem B13947149 : Blo 2147435 13947149 := bstep (se 3 (by rfl) ⟨2615090, by rfl⟩ : syracuseStep 13947149 = 5230181) B5230181
theorem B9298099 : Blo 2147435 9298099 := bstep (se 1 (by rfl) ⟨6973574, by rfl⟩ : syracuseStep 9298099 = 13947149) B13947149
theorem B12397465 : Blo 2147435 12397465 := bstep (se 2 (by rfl) ⟨4649049, by rfl⟩ : syracuseStep 12397465 = 9298099) B9298099
theorem B66119813 : Blo 2147435 66119813 := bstep (se 4 (by rfl) ⟨6198732, by rfl⟩ : syracuseStep 66119813 = 12397465) B12397465
theorem B44079875 : Blo 2147435 44079875 := bstep (se 1 (by rfl) ⟨33059906, by rfl⟩ : syracuseStep 44079875 = 66119813) B66119813
theorem B29386583 : Blo 2147435 29386583 := bstep (se 1 (by rfl) ⟨22039937, by rfl⟩ : syracuseStep 29386583 = 44079875) B44079875
theorem B19591055 : Blo 2147435 19591055 := bstep (se 1 (by rfl) ⟨14693291, by rfl⟩ : syracuseStep 19591055 = 29386583) B29386583
theorem B13060703 : Blo 2147435 13060703 := bstep (se 1 (by rfl) ⟨9795527, by rfl⟩ : syracuseStep 13060703 = 19591055) B19591055
theorem B8707135 : Blo 2147435 8707135 := bstep (se 1 (by rfl) ⟨6530351, by rfl⟩ : syracuseStep 8707135 = 13060703) B13060703
theorem B11609513 : Blo 2147435 11609513 := bstep (se 2 (by rfl) ⟨4353567, by rfl⟩ : syracuseStep 11609513 = 8707135) B8707135
theorem B7739675 : Blo 2147435 7739675 := bstep (se 1 (by rfl) ⟨5804756, by rfl⟩ : syracuseStep 7739675 = 11609513) B11609513
theorem B5159783 : Blo 2147435 5159783 := bstep (se 1 (by rfl) ⟨3869837, by rfl⟩ : syracuseStep 5159783 = 7739675) B7739675
theorem B3439855 : Blo 2147435 3439855 := bstep (se 1 (by rfl) ⟨2579891, by rfl⟩ : syracuseStep 3439855 = 5159783) B5159783
theorem B4586473 : Blo 2147435 4586473 := bstep (se 2 (by rfl) ⟨1719927, by rfl⟩ : syracuseStep 4586473 = 3439855) B3439855
theorem B6115297 : Blo 2147435 6115297 := bstep (se 2 (by rfl) ⟨2293236, by rfl⟩ : syracuseStep 6115297 = 4586473) B4586473
theorem B8153729 : Blo 2147435 8153729 := bstep (se 2 (by rfl) ⟨3057648, by rfl⟩ : syracuseStep 8153729 = 6115297) B6115297
theorem B5435819 : Blo 2147435 5435819 := bstep (se 1 (by rfl) ⟨4076864, by rfl⟩ : syracuseStep 5435819 = 8153729) B8153729
theorem B3623879 : Blo 2147435 3623879 := bstep (se 1 (by rfl) ⟨2717909, by rfl⟩ : syracuseStep 3623879 = 5435819) B5435819
theorem B2415919 : Blo 2147435 2415919 := bstep (se 1 (by rfl) ⟨1811939, by rfl⟩ : syracuseStep 2415919 = 3623879) B3623879
theorem B3221225 : Blo 2147435 3221225 := bstep (se 2 (by rfl) ⟨1207959, by rfl⟩ : syracuseStep 3221225 = 2415919) B2415919
theorem B2147483 : Blo 2147435 2147483 := bstep (se 1 (by rfl) ⟨1610612, by rfl⟩ : syracuseStep 2147483 = 3221225) B3221225
theorem B4964597 : Blo 2147435 4964597 := bbase (se 5 (by rfl) ⟨232715, by rfl⟩ : syracuseStep 4964597 = 465431) (by norm_num)
theorem B3309731 : Blo 2147435 3309731 := bstep (se 1 (by rfl) ⟨2482298, by rfl⟩ : syracuseStep 3309731 = 4964597) B4964597
theorem B2206487 : Blo 2147435 2206487 := bstep (se 1 (by rfl) ⟨1654865, by rfl⟩ : syracuseStep 2206487 = 3309731) B3309731
theorem B5883965 : Blo 2147435 5883965 := bstep (se 3 (by rfl) ⟨1103243, by rfl⟩ : syracuseStep 5883965 = 2206487) B2206487
theorem B3922643 : Blo 2147435 3922643 := bstep (se 1 (by rfl) ⟨2941982, by rfl⟩ : syracuseStep 3922643 = 5883965) B5883965
theorem B2615095 : Blo 2147435 2615095 := bstep (se 1 (by rfl) ⟨1961321, by rfl⟩ : syracuseStep 2615095 = 3922643) B3922643
theorem B13947173 : Blo 2147435 13947173 := bstep (se 4 (by rfl) ⟨1307547, by rfl⟩ : syracuseStep 13947173 = 2615095) B2615095
theorem B9298115 : Blo 2147435 9298115 := bstep (se 1 (by rfl) ⟨6973586, by rfl⟩ : syracuseStep 9298115 = 13947173) B13947173
theorem B6198743 : Blo 2147435 6198743 := bstep (se 1 (by rfl) ⟨4649057, by rfl⟩ : syracuseStep 6198743 = 9298115) B9298115
theorem B4132495 : Blo 2147435 4132495 := bstep (se 1 (by rfl) ⟨3099371, by rfl⟩ : syracuseStep 4132495 = 6198743) B6198743
theorem B5509993 : Blo 2147435 5509993 := bstep (se 2 (by rfl) ⟨2066247, by rfl⟩ : syracuseStep 5509993 = 4132495) B4132495
theorem B7346657 : Blo 2147435 7346657 := bstep (se 2 (by rfl) ⟨2754996, by rfl⟩ : syracuseStep 7346657 = 5509993) B5509993
theorem B19591085 : Blo 2147435 19591085 := bstep (se 3 (by rfl) ⟨3673328, by rfl⟩ : syracuseStep 19591085 = 7346657) B7346657
theorem B13060723 : Blo 2147435 13060723 := bstep (se 1 (by rfl) ⟨9795542, by rfl⟩ : syracuseStep 13060723 = 19591085) B19591085
theorem B17414297 : Blo 2147435 17414297 := bstep (se 2 (by rfl) ⟨6530361, by rfl⟩ : syracuseStep 17414297 = 13060723) B13060723
theorem B11609531 : Blo 2147435 11609531 := bstep (se 1 (by rfl) ⟨8707148, by rfl⟩ : syracuseStep 11609531 = 17414297) B17414297
theorem B7739687 : Blo 2147435 7739687 := bstep (se 1 (by rfl) ⟨5804765, by rfl⟩ : syracuseStep 7739687 = 11609531) B11609531
theorem B5159791 : Blo 2147435 5159791 := bstep (se 1 (by rfl) ⟨3869843, by rfl⟩ : syracuseStep 5159791 = 7739687) B7739687
theorem B27518885 : Blo 2147435 27518885 := bstep (se 4 (by rfl) ⟨2579895, by rfl⟩ : syracuseStep 27518885 = 5159791) B5159791
theorem B18345923 : Blo 2147435 18345923 := bstep (se 1 (by rfl) ⟨13759442, by rfl⟩ : syracuseStep 18345923 = 27518885) B27518885
theorem B12230615 : Blo 2147435 12230615 := bstep (se 1 (by rfl) ⟨9172961, by rfl⟩ : syracuseStep 12230615 = 18345923) B18345923
theorem B8153743 : Blo 2147435 8153743 := bstep (se 1 (by rfl) ⟨6115307, by rfl⟩ : syracuseStep 8153743 = 12230615) B12230615
theorem B10871657 : Blo 2147435 10871657 := bstep (se 2 (by rfl) ⟨4076871, by rfl⟩ : syracuseStep 10871657 = 8153743) B8153743
theorem B7247771 : Blo 2147435 7247771 := bstep (se 1 (by rfl) ⟨5435828, by rfl⟩ : syracuseStep 7247771 = 10871657) B10871657
theorem B4831847 : Blo 2147435 4831847 := bstep (se 1 (by rfl) ⟨3623885, by rfl⟩ : syracuseStep 4831847 = 7247771) B7247771
theorem B3221231 : Blo 2147435 3221231 := bstep (se 1 (by rfl) ⟨2415923, by rfl⟩ : syracuseStep 3221231 = 4831847) B4831847
theorem B2147487 : Blo 2147435 2147487 := bstep (se 1 (by rfl) ⟨1610615, by rfl⟩ : syracuseStep 2147487 = 3221231) B3221231
theorem B3221237 : Blo 2147435 3221237 := bbase (se 5 (by rfl) ⟨150995, by rfl⟩ : syracuseStep 3221237 = 301991) (by norm_num)
theorem B2147491 : Blo 2147435 2147491 := bstep (se 1 (by rfl) ⟨1610618, by rfl⟩ : syracuseStep 2147491 = 3221237) B3221237
theorem B9172997 : Blo 2147435 9172997 := bbase (se 4 (by rfl) ⟨859968, by rfl⟩ : syracuseStep 9172997 = 1719937) (by norm_num)
theorem B6115331 : Blo 2147435 6115331 := bstep (se 1 (by rfl) ⟨4586498, by rfl⟩ : syracuseStep 6115331 = 9172997) B9172997
theorem B4076887 : Blo 2147435 4076887 := bstep (se 1 (by rfl) ⟨3057665, by rfl⟩ : syracuseStep 4076887 = 6115331) B6115331
theorem B5435849 : Blo 2147435 5435849 := bstep (se 2 (by rfl) ⟨2038443, by rfl⟩ : syracuseStep 5435849 = 4076887) B4076887
theorem B3623899 : Blo 2147435 3623899 := bstep (se 1 (by rfl) ⟨2717924, by rfl⟩ : syracuseStep 3623899 = 5435849) B5435849
theorem B4831865 : Blo 2147435 4831865 := bstep (se 2 (by rfl) ⟨1811949, by rfl⟩ : syracuseStep 4831865 = 3623899) B3623899
theorem B3221243 : Blo 2147435 3221243 := bstep (se 1 (by rfl) ⟨2415932, by rfl⟩ : syracuseStep 3221243 = 4831865) B4831865
theorem B2147495 : Blo 2147435 2147495 := bstep (se 1 (by rfl) ⟨1610621, by rfl⟩ : syracuseStep 2147495 = 3221243) B3221243
theorem B2415937 : Blo 2147435 2415937 := bbase (se 2 (by rfl) ⟨905976, by rfl⟩ : syracuseStep 2415937 = 1811953) (by norm_num)
theorem B3221249 : Blo 2147435 3221249 := bstep (se 2 (by rfl) ⟨1207968, by rfl⟩ : syracuseStep 3221249 = 2415937) B2415937
theorem B2147499 : Blo 2147435 2147499 := bstep (se 1 (by rfl) ⟨1610624, by rfl⟩ : syracuseStep 2147499 = 3221249) B3221249
theorem B5435869 : Blo 2147435 5435869 := bbase (se 3 (by rfl) ⟨1019225, by rfl⟩ : syracuseStep 5435869 = 2038451) (by norm_num)
theorem B7247825 : Blo 2147435 7247825 := bstep (se 2 (by rfl) ⟨2717934, by rfl⟩ : syracuseStep 7247825 = 5435869) B5435869
theorem B4831883 : Blo 2147435 4831883 := bstep (se 1 (by rfl) ⟨3623912, by rfl⟩ : syracuseStep 4831883 = 7247825) B7247825
theorem B3221255 : Blo 2147435 3221255 := bstep (se 1 (by rfl) ⟨2415941, by rfl⟩ : syracuseStep 3221255 = 4831883) B4831883
theorem B2147503 : Blo 2147435 2147503 := bstep (se 1 (by rfl) ⟨1610627, by rfl⟩ : syracuseStep 2147503 = 3221255) B3221255
theorem B3221261 : Blo 2147435 3221261 := bbase (se 3 (by rfl) ⟨603986, by rfl⟩ : syracuseStep 3221261 = 1207973) (by norm_num)
theorem B2147507 : Blo 2147435 2147507 := bstep (se 1 (by rfl) ⟨1610630, by rfl⟩ : syracuseStep 2147507 = 3221261) B3221261
theorem B4831901 : Blo 2147435 4831901 := bbase (se 3 (by rfl) ⟨905981, by rfl⟩ : syracuseStep 4831901 = 1811963) (by norm_num)
theorem B3221267 : Blo 2147435 3221267 := bstep (se 1 (by rfl) ⟨2415950, by rfl⟩ : syracuseStep 3221267 = 4831901) B4831901
theorem B2147511 : Blo 2147435 2147511 := bstep (se 1 (by rfl) ⟨1610633, by rfl⟩ : syracuseStep 2147511 = 3221267) B3221267
theorem B3623933 : Blo 2147435 3623933 := bbase (se 3 (by rfl) ⟨679487, by rfl⟩ : syracuseStep 3623933 = 1358975) (by norm_num)
theorem B2415955 : Blo 2147435 2415955 := bstep (se 1 (by rfl) ⟨1811966, by rfl⟩ : syracuseStep 2415955 = 3623933) B3623933
theorem B3221273 : Blo 2147435 3221273 := bstep (se 2 (by rfl) ⟨1207977, by rfl⟩ : syracuseStep 3221273 = 2415955) B2415955
theorem B2147515 : Blo 2147435 2147515 := bstep (se 1 (by rfl) ⟨1610636, by rfl⟩ : syracuseStep 2147515 = 3221273) B3221273
theorem B4586549 : Blo 2147435 4586549 := bbase (se 5 (by rfl) ⟨214994, by rfl⟩ : syracuseStep 4586549 = 429989) (by norm_num)
theorem B12230797 : Blo 2147435 12230797 := bstep (se 3 (by rfl) ⟨2293274, by rfl⟩ : syracuseStep 12230797 = 4586549) B4586549
theorem B16307729 : Blo 2147435 16307729 := bstep (se 2 (by rfl) ⟨6115398, by rfl⟩ : syracuseStep 16307729 = 12230797) B12230797
theorem B10871819 : Blo 2147435 10871819 := bstep (se 1 (by rfl) ⟨8153864, by rfl⟩ : syracuseStep 10871819 = 16307729) B16307729
theorem B7247879 : Blo 2147435 7247879 := bstep (se 1 (by rfl) ⟨5435909, by rfl⟩ : syracuseStep 7247879 = 10871819) B10871819
theorem B4831919 : Blo 2147435 4831919 := bstep (se 1 (by rfl) ⟨3623939, by rfl⟩ : syracuseStep 4831919 = 7247879) B7247879
theorem B3221279 : Blo 2147435 3221279 := bstep (se 1 (by rfl) ⟨2415959, by rfl⟩ : syracuseStep 3221279 = 4831919) B4831919
theorem B2147519 : Blo 2147435 2147519 := bstep (se 1 (by rfl) ⟨1610639, by rfl⟩ : syracuseStep 2147519 = 3221279) B3221279
theorem B3221285 : Blo 2147435 3221285 := bbase (se 4 (by rfl) ⟨301995, by rfl⟩ : syracuseStep 3221285 = 603991) (by norm_num)
theorem B2147523 : Blo 2147435 2147523 := bstep (se 1 (by rfl) ⟨1610642, by rfl⟩ : syracuseStep 2147523 = 3221285) B3221285
theorem B2717965 : Blo 2147435 2717965 := bbase (se 3 (by rfl) ⟨509618, by rfl⟩ : syracuseStep 2717965 = 1019237) (by norm_num)
theorem B3623953 : Blo 2147435 3623953 := bstep (se 2 (by rfl) ⟨1358982, by rfl⟩ : syracuseStep 3623953 = 2717965) B2717965
theorem B4831937 : Blo 2147435 4831937 := bstep (se 2 (by rfl) ⟨1811976, by rfl⟩ : syracuseStep 4831937 = 3623953) B3623953
theorem B3221291 : Blo 2147435 3221291 := bstep (se 1 (by rfl) ⟨2415968, by rfl⟩ : syracuseStep 3221291 = 4831937) B4831937
theorem B2147527 : Blo 2147435 2147527 := bstep (se 1 (by rfl) ⟨1610645, by rfl⟩ : syracuseStep 2147527 = 3221291) B3221291
theorem B2415973 : Blo 2147435 2415973 := bbase (se 4 (by rfl) ⟨226497, by rfl⟩ : syracuseStep 2415973 = 452995) (by norm_num)
theorem B3221297 : Blo 2147435 3221297 := bstep (se 2 (by rfl) ⟨1207986, by rfl⟩ : syracuseStep 3221297 = 2415973) B2415973
theorem B2147531 : Blo 2147435 2147531 := bstep (se 1 (by rfl) ⟨1610648, by rfl⟩ : syracuseStep 2147531 = 3221297) B3221297
theorem B6115445 : Blo 2147435 6115445 := bbase (se 5 (by rfl) ⟨286661, by rfl⟩ : syracuseStep 6115445 = 573323) (by norm_num)
theorem B4076963 : Blo 2147435 4076963 := bstep (se 1 (by rfl) ⟨3057722, by rfl⟩ : syracuseStep 4076963 = 6115445) B6115445
theorem B2717975 : Blo 2147435 2717975 := bstep (se 1 (by rfl) ⟨2038481, by rfl⟩ : syracuseStep 2717975 = 4076963) B4076963
theorem B7247933 : Blo 2147435 7247933 := bstep (se 3 (by rfl) ⟨1358987, by rfl⟩ : syracuseStep 7247933 = 2717975) B2717975
theorem B4831955 : Blo 2147435 4831955 := bstep (se 1 (by rfl) ⟨3623966, by rfl⟩ : syracuseStep 4831955 = 7247933) B7247933
theorem B3221303 : Blo 2147435 3221303 := bstep (se 1 (by rfl) ⟨2415977, by rfl⟩ : syracuseStep 3221303 = 4831955) B4831955
theorem B2147535 : Blo 2147435 2147535 := bstep (se 1 (by rfl) ⟨1610651, by rfl⟩ : syracuseStep 2147535 = 3221303) B3221303
theorem B3221309 : Blo 2147435 3221309 := bbase (se 3 (by rfl) ⟨603995, by rfl⟩ : syracuseStep 3221309 = 1207991) (by norm_num)
theorem B2147539 : Blo 2147435 2147539 := bstep (se 1 (by rfl) ⟨1610654, by rfl⟩ : syracuseStep 2147539 = 3221309) B3221309
theorem B4831973 : Blo 2147435 4831973 := bbase (se 4 (by rfl) ⟨452997, by rfl⟩ : syracuseStep 4831973 = 905995) (by norm_num)
theorem B3221315 : Blo 2147435 3221315 := bstep (se 1 (by rfl) ⟨2415986, by rfl⟩ : syracuseStep 3221315 = 4831973) B4831973
theorem B2147543 : Blo 2147435 2147543 := bstep (se 1 (by rfl) ⟨1610657, by rfl⟩ : syracuseStep 2147543 = 3221315) B3221315
theorem B5435981 : Blo 2147435 5435981 := bbase (se 3 (by rfl) ⟨1019246, by rfl⟩ : syracuseStep 5435981 = 2038493) (by norm_num)
theorem B3623987 : Blo 2147435 3623987 := bstep (se 1 (by rfl) ⟨2717990, by rfl⟩ : syracuseStep 3623987 = 5435981) B5435981
theorem B2415991 : Blo 2147435 2415991 := bstep (se 1 (by rfl) ⟨1811993, by rfl⟩ : syracuseStep 2415991 = 3623987) B3623987
theorem B3221321 : Blo 2147435 3221321 := bstep (se 2 (by rfl) ⟨1207995, by rfl⟩ : syracuseStep 3221321 = 2415991) B2415991
theorem B2147547 : Blo 2147435 2147547 := bstep (se 1 (by rfl) ⟨1610660, by rfl⟩ : syracuseStep 2147547 = 3221321) B3221321
theorem B2293309 : Blo 2147435 2293309 := bbase (se 3 (by rfl) ⟨429995, by rfl⟩ : syracuseStep 2293309 = 859991) (by norm_num)
theorem B3057745 : Blo 2147435 3057745 := bstep (se 2 (by rfl) ⟨1146654, by rfl⟩ : syracuseStep 3057745 = 2293309) B2293309
theorem B4076993 : Blo 2147435 4076993 := bstep (se 2 (by rfl) ⟨1528872, by rfl⟩ : syracuseStep 4076993 = 3057745) B3057745
theorem B10871981 : Blo 2147435 10871981 := bstep (se 3 (by rfl) ⟨2038496, by rfl⟩ : syracuseStep 10871981 = 4076993) B4076993
theorem B7247987 : Blo 2147435 7247987 := bstep (se 1 (by rfl) ⟨5435990, by rfl⟩ : syracuseStep 7247987 = 10871981) B10871981
theorem B4831991 : Blo 2147435 4831991 := bstep (se 1 (by rfl) ⟨3623993, by rfl⟩ : syracuseStep 4831991 = 7247987) B7247987
theorem B3221327 : Blo 2147435 3221327 := bstep (se 1 (by rfl) ⟨2415995, by rfl⟩ : syracuseStep 3221327 = 4831991) B4831991
theorem B2147551 : Blo 2147435 2147551 := bstep (se 1 (by rfl) ⟨1610663, by rfl⟩ : syracuseStep 2147551 = 3221327) B3221327
theorem B3221333 : Blo 2147435 3221333 := bbase (se 9 (by rfl) ⟨9437, by rfl⟩ : syracuseStep 3221333 = 18875) (by norm_num)
theorem B2147555 : Blo 2147435 2147555 := bstep (se 1 (by rfl) ⟨1610666, by rfl⟩ : syracuseStep 2147555 = 3221333) B3221333
theorem B5159965 : Blo 2147435 5159965 := bbase (se 3 (by rfl) ⟨967493, by rfl⟩ : syracuseStep 5159965 = 1934987) (by norm_num)
theorem B6879953 : Blo 2147435 6879953 := bstep (se 2 (by rfl) ⟨2579982, by rfl⟩ : syracuseStep 6879953 = 5159965) B5159965
theorem B4586635 : Blo 2147435 4586635 := bstep (se 1 (by rfl) ⟨3439976, by rfl⟩ : syracuseStep 4586635 = 6879953) B6879953
theorem B6115513 : Blo 2147435 6115513 := bstep (se 2 (by rfl) ⟨2293317, by rfl⟩ : syracuseStep 6115513 = 4586635) B4586635
theorem B8154017 : Blo 2147435 8154017 := bstep (se 2 (by rfl) ⟨3057756, by rfl⟩ : syracuseStep 8154017 = 6115513) B6115513
theorem B5436011 : Blo 2147435 5436011 := bstep (se 1 (by rfl) ⟨4077008, by rfl⟩ : syracuseStep 5436011 = 8154017) B8154017
theorem B3624007 : Blo 2147435 3624007 := bstep (se 1 (by rfl) ⟨2718005, by rfl⟩ : syracuseStep 3624007 = 5436011) B5436011
theorem B4832009 : Blo 2147435 4832009 := bstep (se 2 (by rfl) ⟨1812003, by rfl⟩ : syracuseStep 4832009 = 3624007) B3624007
theorem B3221339 : Blo 2147435 3221339 := bstep (se 1 (by rfl) ⟨2416004, by rfl⟩ : syracuseStep 3221339 = 4832009) B4832009
theorem B2147559 : Blo 2147435 2147559 := bstep (se 1 (by rfl) ⟨1610669, by rfl⟩ : syracuseStep 2147559 = 3221339) B3221339
theorem B2416009 : Blo 2147435 2416009 := bbase (se 2 (by rfl) ⟨906003, by rfl⟩ : syracuseStep 2416009 = 1812007) (by norm_num)
theorem B3221345 : Blo 2147435 3221345 := bstep (se 2 (by rfl) ⟨1208004, by rfl⟩ : syracuseStep 3221345 = 2416009) B2416009
theorem B2147563 : Blo 2147435 2147563 := bstep (se 1 (by rfl) ⟨1610672, by rfl⟩ : syracuseStep 2147563 = 3221345) B3221345
theorem B2723701 : Blo 2147435 2723701 := bbase (se 5 (by rfl) ⟨127673, by rfl⟩ : syracuseStep 2723701 = 255347) (by norm_num)
theorem B3631601 : Blo 2147435 3631601 := bstep (se 2 (by rfl) ⟨1361850, by rfl⟩ : syracuseStep 3631601 = 2723701) B2723701
theorem B2421067 : Blo 2147435 2421067 := bstep (se 1 (by rfl) ⟨1815800, by rfl⟩ : syracuseStep 2421067 = 3631601) B3631601
theorem B3228089 : Blo 2147435 3228089 := bstep (se 2 (by rfl) ⟨1210533, by rfl⟩ : syracuseStep 3228089 = 2421067) B2421067
theorem B8608237 : Blo 2147435 8608237 := bstep (se 3 (by rfl) ⟨1614044, by rfl⟩ : syracuseStep 8608237 = 3228089) B3228089
theorem B45910597 : Blo 2147435 45910597 := bstep (se 4 (by rfl) ⟨4304118, by rfl⟩ : syracuseStep 45910597 = 8608237) B8608237
theorem B61214129 : Blo 2147435 61214129 := bstep (se 2 (by rfl) ⟨22955298, by rfl⟩ : syracuseStep 61214129 = 45910597) B45910597
theorem B40809419 : Blo 2147435 40809419 := bstep (se 1 (by rfl) ⟨30607064, by rfl⟩ : syracuseStep 40809419 = 61214129) B61214129
theorem B27206279 : Blo 2147435 27206279 := bstep (se 1 (by rfl) ⟨20404709, by rfl⟩ : syracuseStep 27206279 = 40809419) B40809419
theorem B18137519 : Blo 2147435 18137519 := bstep (se 1 (by rfl) ⟨13603139, by rfl⟩ : syracuseStep 18137519 = 27206279) B27206279
theorem B12091679 : Blo 2147435 12091679 := bstep (se 1 (by rfl) ⟨9068759, by rfl⟩ : syracuseStep 12091679 = 18137519) B18137519
theorem B8061119 : Blo 2147435 8061119 := bstep (se 1 (by rfl) ⟨6045839, by rfl⟩ : syracuseStep 8061119 = 12091679) B12091679
theorem B5374079 : Blo 2147435 5374079 := bstep (se 1 (by rfl) ⟨4030559, by rfl⟩ : syracuseStep 5374079 = 8061119) B8061119
theorem B3582719 : Blo 2147435 3582719 := bstep (se 1 (by rfl) ⟨2687039, by rfl⟩ : syracuseStep 3582719 = 5374079) B5374079
theorem B2388479 : Blo 2147435 2388479 := bstep (se 1 (by rfl) ⟨1791359, by rfl⟩ : syracuseStep 2388479 = 3582719) B3582719
theorem B6369277 : Blo 2147435 6369277 := bstep (se 3 (by rfl) ⟨1194239, by rfl⟩ : syracuseStep 6369277 = 2388479) B2388479
theorem B8492369 : Blo 2147435 8492369 := bstep (se 2 (by rfl) ⟨3184638, by rfl⟩ : syracuseStep 8492369 = 6369277) B6369277
theorem B22646317 : Blo 2147435 22646317 := bstep (se 3 (by rfl) ⟨4246184, by rfl⟩ : syracuseStep 22646317 = 8492369) B8492369
theorem B30195089 : Blo 2147435 30195089 := bstep (se 2 (by rfl) ⟨11323158, by rfl⟩ : syracuseStep 30195089 = 22646317) B22646317
theorem B20130059 : Blo 2147435 20130059 := bstep (se 1 (by rfl) ⟨15097544, by rfl⟩ : syracuseStep 20130059 = 30195089) B30195089
theorem B13420039 : Blo 2147435 13420039 := bstep (se 1 (by rfl) ⟨10065029, by rfl⟩ : syracuseStep 13420039 = 20130059) B20130059
theorem B17893385 : Blo 2147435 17893385 := bstep (se 2 (by rfl) ⟨6710019, by rfl⟩ : syracuseStep 17893385 = 13420039) B13420039
theorem B11928923 : Blo 2147435 11928923 := bstep (se 1 (by rfl) ⟨8946692, by rfl⟩ : syracuseStep 11928923 = 17893385) B17893385
theorem B7952615 : Blo 2147435 7952615 := bstep (se 1 (by rfl) ⟨5964461, by rfl⟩ : syracuseStep 7952615 = 11928923) B11928923
theorem B5301743 : Blo 2147435 5301743 := bstep (se 1 (by rfl) ⟨3976307, by rfl⟩ : syracuseStep 5301743 = 7952615) B7952615
theorem B56551925 : Blo 2147435 56551925 := bstep (se 5 (by rfl) ⟨2650871, by rfl⟩ : syracuseStep 56551925 = 5301743) B5301743
theorem B37701283 : Blo 2147435 37701283 := bstep (se 1 (by rfl) ⟨28275962, by rfl⟩ : syracuseStep 37701283 = 56551925) B56551925
theorem B50268377 : Blo 2147435 50268377 := bstep (se 2 (by rfl) ⟨18850641, by rfl⟩ : syracuseStep 50268377 = 37701283) B37701283
theorem B33512251 : Blo 2147435 33512251 := bstep (se 1 (by rfl) ⟨25134188, by rfl⟩ : syracuseStep 33512251 = 50268377) B50268377
theorem B44683001 : Blo 2147435 44683001 := bstep (se 2 (by rfl) ⟨16756125, by rfl⟩ : syracuseStep 44683001 = 33512251) B33512251
theorem B29788667 : Blo 2147435 29788667 := bstep (se 1 (by rfl) ⟨22341500, by rfl⟩ : syracuseStep 29788667 = 44683001) B44683001
theorem B19859111 : Blo 2147435 19859111 := bstep (se 1 (by rfl) ⟨14894333, by rfl⟩ : syracuseStep 19859111 = 29788667) B29788667
theorem B13239407 : Blo 2147435 13239407 := bstep (se 1 (by rfl) ⟨9929555, by rfl⟩ : syracuseStep 13239407 = 19859111) B19859111
theorem B35305085 : Blo 2147435 35305085 := bstep (se 3 (by rfl) ⟨6619703, by rfl⟩ : syracuseStep 35305085 = 13239407) B13239407
theorem B94146893 : Blo 2147435 94146893 := bstep (se 3 (by rfl) ⟨17652542, by rfl⟩ : syracuseStep 94146893 = 35305085) B35305085
theorem B62764595 : Blo 2147435 62764595 := bstep (se 1 (by rfl) ⟨47073446, by rfl⟩ : syracuseStep 62764595 = 94146893) B94146893
theorem B41843063 : Blo 2147435 41843063 := bstep (se 1 (by rfl) ⟨31382297, by rfl⟩ : syracuseStep 41843063 = 62764595) B62764595
theorem B27895375 : Blo 2147435 27895375 := bstep (se 1 (by rfl) ⟨20921531, by rfl⟩ : syracuseStep 27895375 = 41843063) B41843063
theorem B37193833 : Blo 2147435 37193833 := bstep (se 2 (by rfl) ⟨13947687, by rfl⟩ : syracuseStep 37193833 = 27895375) B27895375
theorem B49591777 : Blo 2147435 49591777 := bstep (se 2 (by rfl) ⟨18596916, by rfl⟩ : syracuseStep 49591777 = 37193833) B37193833
theorem B66122369 : Blo 2147435 66122369 := bstep (se 2 (by rfl) ⟨24795888, by rfl⟩ : syracuseStep 66122369 = 49591777) B49591777
theorem B44081579 : Blo 2147435 44081579 := bstep (se 1 (by rfl) ⟨33061184, by rfl⟩ : syracuseStep 44081579 = 66122369) B66122369
theorem B29387719 : Blo 2147435 29387719 := bstep (se 1 (by rfl) ⟨22040789, by rfl⟩ : syracuseStep 29387719 = 44081579) B44081579
theorem B39183625 : Blo 2147435 39183625 := bstep (se 2 (by rfl) ⟨14693859, by rfl⟩ : syracuseStep 39183625 = 29387719) B29387719
theorem B52244833 : Blo 2147435 52244833 := bstep (se 2 (by rfl) ⟨19591812, by rfl⟩ : syracuseStep 52244833 = 39183625) B39183625
theorem B69659777 : Blo 2147435 69659777 := bstep (se 2 (by rfl) ⟨26122416, by rfl⟩ : syracuseStep 69659777 = 52244833) B52244833
theorem B46439851 : Blo 2147435 46439851 := bstep (se 1 (by rfl) ⟨34829888, by rfl⟩ : syracuseStep 46439851 = 69659777) B69659777
theorem B61919801 : Blo 2147435 61919801 := bstep (se 2 (by rfl) ⟨23219925, by rfl⟩ : syracuseStep 61919801 = 46439851) B46439851
theorem B41279867 : Blo 2147435 41279867 := bstep (se 1 (by rfl) ⟨30959900, by rfl⟩ : syracuseStep 41279867 = 61919801) B61919801
theorem B27519911 : Blo 2147435 27519911 := bstep (se 1 (by rfl) ⟨20639933, by rfl⟩ : syracuseStep 27519911 = 41279867) B41279867
theorem B18346607 : Blo 2147435 18346607 := bstep (se 1 (by rfl) ⟨13759955, by rfl⟩ : syracuseStep 18346607 = 27519911) B27519911
theorem B12231071 : Blo 2147435 12231071 := bstep (se 1 (by rfl) ⟨9173303, by rfl⟩ : syracuseStep 12231071 = 18346607) B18346607
theorem B8154047 : Blo 2147435 8154047 := bstep (se 1 (by rfl) ⟨6115535, by rfl⟩ : syracuseStep 8154047 = 12231071) B12231071
theorem B5436031 : Blo 2147435 5436031 := bstep (se 1 (by rfl) ⟨4077023, by rfl⟩ : syracuseStep 5436031 = 8154047) B8154047
theorem B7248041 : Blo 2147435 7248041 := bstep (se 2 (by rfl) ⟨2718015, by rfl⟩ : syracuseStep 7248041 = 5436031) B5436031
theorem B4832027 : Blo 2147435 4832027 := bstep (se 1 (by rfl) ⟨3624020, by rfl⟩ : syracuseStep 4832027 = 7248041) B7248041
theorem B3221351 : Blo 2147435 3221351 := bstep (se 1 (by rfl) ⟨2416013, by rfl⟩ : syracuseStep 3221351 = 4832027) B4832027
theorem B2147567 : Blo 2147435 2147567 := bstep (se 1 (by rfl) ⟨1610675, by rfl⟩ : syracuseStep 2147567 = 3221351) B3221351
theorem B3221357 : Blo 2147435 3221357 := bbase (se 3 (by rfl) ⟨604004, by rfl⟩ : syracuseStep 3221357 = 1208009) (by norm_num)
theorem B2147571 : Blo 2147435 2147571 := bstep (se 1 (by rfl) ⟨1610678, by rfl⟩ : syracuseStep 2147571 = 3221357) B3221357
theorem B4832045 : Blo 2147435 4832045 := bbase (se 3 (by rfl) ⟨906008, by rfl⟩ : syracuseStep 4832045 = 1812017) (by norm_num)
theorem B3221363 : Blo 2147435 3221363 := bstep (se 1 (by rfl) ⟨2416022, by rfl⟩ : syracuseStep 3221363 = 4832045) B4832045
theorem B2147575 : Blo 2147435 2147575 := bstep (se 1 (by rfl) ⟨1610681, by rfl⟩ : syracuseStep 2147575 = 3221363) B3221363
theorem B6530645 : Blo 2147435 6530645 := bbase (se 8 (by rfl) ⟨38265, by rfl⟩ : syracuseStep 6530645 = 76531) (by norm_num)
theorem B4353763 : Blo 2147435 4353763 := bstep (se 1 (by rfl) ⟨3265322, by rfl⟩ : syracuseStep 4353763 = 6530645) B6530645
theorem B5805017 : Blo 2147435 5805017 := bstep (se 2 (by rfl) ⟨2176881, by rfl⟩ : syracuseStep 5805017 = 4353763) B4353763
theorem B3870011 : Blo 2147435 3870011 := bstep (se 1 (by rfl) ⟨2902508, by rfl⟩ : syracuseStep 3870011 = 5805017) B5805017
theorem B2580007 : Blo 2147435 2580007 := bstep (se 1 (by rfl) ⟨1935005, by rfl⟩ : syracuseStep 2580007 = 3870011) B3870011
theorem B3440009 : Blo 2147435 3440009 := bstep (se 2 (by rfl) ⟨1290003, by rfl⟩ : syracuseStep 3440009 = 2580007) B2580007
theorem B9173357 : Blo 2147435 9173357 := bstep (se 3 (by rfl) ⟨1720004, by rfl⟩ : syracuseStep 9173357 = 3440009) B3440009
theorem B6115571 : Blo 2147435 6115571 := bstep (se 1 (by rfl) ⟨4586678, by rfl⟩ : syracuseStep 6115571 = 9173357) B9173357
theorem B4077047 : Blo 2147435 4077047 := bstep (se 1 (by rfl) ⟨3057785, by rfl⟩ : syracuseStep 4077047 = 6115571) B6115571
theorem B2718031 : Blo 2147435 2718031 := bstep (se 1 (by rfl) ⟨2038523, by rfl⟩ : syracuseStep 2718031 = 4077047) B4077047
theorem B3624041 : Blo 2147435 3624041 := bstep (se 2 (by rfl) ⟨1359015, by rfl⟩ : syracuseStep 3624041 = 2718031) B2718031
theorem B2416027 : Blo 2147435 2416027 := bstep (se 1 (by rfl) ⟨1812020, by rfl⟩ : syracuseStep 2416027 = 3624041) B3624041
theorem B3221369 : Blo 2147435 3221369 := bstep (se 2 (by rfl) ⟨1208013, by rfl⟩ : syracuseStep 3221369 = 2416027) B2416027
theorem B2147579 : Blo 2147435 2147579 := bstep (se 1 (by rfl) ⟨1610684, by rfl⟩ : syracuseStep 2147579 = 3221369) B3221369
theorem B3673493 : Blo 2147435 3673493 := bbase (se 6 (by rfl) ⟨86097, by rfl⟩ : syracuseStep 3673493 = 172195) (by norm_num)
theorem B2448995 : Blo 2147435 2448995 := bstep (se 1 (by rfl) ⟨1836746, by rfl⟩ : syracuseStep 2448995 = 3673493) B3673493
theorem B6530653 : Blo 2147435 6530653 := bstep (se 3 (by rfl) ⟨1224497, by rfl⟩ : syracuseStep 6530653 = 2448995) B2448995
theorem B8707537 : Blo 2147435 8707537 := bstep (se 2 (by rfl) ⟨3265326, by rfl⟩ : syracuseStep 8707537 = 6530653) B6530653
theorem B11610049 : Blo 2147435 11610049 := bstep (se 2 (by rfl) ⟨4353768, by rfl⟩ : syracuseStep 11610049 = 8707537) B8707537
theorem B15480065 : Blo 2147435 15480065 := bstep (se 2 (by rfl) ⟨5805024, by rfl⟩ : syracuseStep 15480065 = 11610049) B11610049
theorem B10320043 : Blo 2147435 10320043 := bstep (se 1 (by rfl) ⟨7740032, by rfl⟩ : syracuseStep 10320043 = 15480065) B15480065
theorem B13760057 : Blo 2147435 13760057 := bstep (se 2 (by rfl) ⟨5160021, by rfl⟩ : syracuseStep 13760057 = 10320043) B10320043
theorem B36693485 : Blo 2147435 36693485 := bstep (se 3 (by rfl) ⟨6880028, by rfl⟩ : syracuseStep 36693485 = 13760057) B13760057
theorem B24462323 : Blo 2147435 24462323 := bstep (se 1 (by rfl) ⟨18346742, by rfl⟩ : syracuseStep 24462323 = 36693485) B36693485
theorem B16308215 : Blo 2147435 16308215 := bstep (se 1 (by rfl) ⟨12231161, by rfl⟩ : syracuseStep 16308215 = 24462323) B24462323
theorem B10872143 : Blo 2147435 10872143 := bstep (se 1 (by rfl) ⟨8154107, by rfl⟩ : syracuseStep 10872143 = 16308215) B16308215
theorem B7248095 : Blo 2147435 7248095 := bstep (se 1 (by rfl) ⟨5436071, by rfl⟩ : syracuseStep 7248095 = 10872143) B10872143
theorem B4832063 : Blo 2147435 4832063 := bstep (se 1 (by rfl) ⟨3624047, by rfl⟩ : syracuseStep 4832063 = 7248095) B7248095
theorem B3221375 : Blo 2147435 3221375 := bstep (se 1 (by rfl) ⟨2416031, by rfl⟩ : syracuseStep 3221375 = 4832063) B4832063
theorem B2147583 : Blo 2147435 2147583 := bstep (se 1 (by rfl) ⟨1610687, by rfl⟩ : syracuseStep 2147583 = 3221375) B3221375
theorem B3221381 : Blo 2147435 3221381 := bbase (se 4 (by rfl) ⟨302004, by rfl⟩ : syracuseStep 3221381 = 604009) (by norm_num)
theorem B2147587 : Blo 2147435 2147587 := bstep (se 1 (by rfl) ⟨1610690, by rfl⟩ : syracuseStep 2147587 = 3221381) B3221381
theorem B3624061 : Blo 2147435 3624061 := bbase (se 3 (by rfl) ⟨679511, by rfl⟩ : syracuseStep 3624061 = 1359023) (by norm_num)
theorem B4832081 : Blo 2147435 4832081 := bstep (se 2 (by rfl) ⟨1812030, by rfl⟩ : syracuseStep 4832081 = 3624061) B3624061
theorem B3221387 : Blo 2147435 3221387 := bstep (se 1 (by rfl) ⟨2416040, by rfl⟩ : syracuseStep 3221387 = 4832081) B4832081
theorem B2147591 : Blo 2147435 2147591 := bstep (se 1 (by rfl) ⟨1610693, by rfl⟩ : syracuseStep 2147591 = 3221387) B3221387
theorem B2416045 : Blo 2147435 2416045 := bbase (se 3 (by rfl) ⟨453008, by rfl⟩ : syracuseStep 2416045 = 906017) (by norm_num)
theorem B3221393 : Blo 2147435 3221393 := bstep (se 2 (by rfl) ⟨1208022, by rfl⟩ : syracuseStep 3221393 = 2416045) B2416045
theorem B2147595 : Blo 2147435 2147595 := bstep (se 1 (by rfl) ⟨1610696, by rfl⟩ : syracuseStep 2147595 = 3221393) B3221393
theorem B7248149 : Blo 2147435 7248149 := bbase (se 6 (by rfl) ⟨169878, by rfl⟩ : syracuseStep 7248149 = 339757) (by norm_num)
theorem B4832099 : Blo 2147435 4832099 := bstep (se 1 (by rfl) ⟨3624074, by rfl⟩ : syracuseStep 4832099 = 7248149) B7248149
theorem B3221399 : Blo 2147435 3221399 := bstep (se 1 (by rfl) ⟨2416049, by rfl⟩ : syracuseStep 3221399 = 4832099) B4832099
theorem B2147599 : Blo 2147435 2147599 := bstep (se 1 (by rfl) ⟨1610699, by rfl⟩ : syracuseStep 2147599 = 3221399) B3221399
theorem B3221405 : Blo 2147435 3221405 := bbase (se 3 (by rfl) ⟨604013, by rfl⟩ : syracuseStep 3221405 = 1208027) (by norm_num)
theorem B2147603 : Blo 2147435 2147603 := bstep (se 1 (by rfl) ⟨1610702, by rfl⟩ : syracuseStep 2147603 = 3221405) B3221405
theorem B4832117 : Blo 2147435 4832117 := bbase (se 5 (by rfl) ⟨226505, by rfl⟩ : syracuseStep 4832117 = 453011) (by norm_num)
theorem B3221411 : Blo 2147435 3221411 := bstep (se 1 (by rfl) ⟨2416058, by rfl⟩ : syracuseStep 3221411 = 4832117) B4832117
theorem B2147607 : Blo 2147435 2147607 := bstep (se 1 (by rfl) ⟨1610705, by rfl⟩ : syracuseStep 2147607 = 3221411) B3221411
theorem B3723661 : Blo 2147435 3723661 := bbase (se 3 (by rfl) ⟨698186, by rfl⟩ : syracuseStep 3723661 = 1396373) (by norm_num)
theorem B19859525 : Blo 2147435 19859525 := bstep (se 4 (by rfl) ⟨1861830, by rfl⟩ : syracuseStep 19859525 = 3723661) B3723661
theorem B13239683 : Blo 2147435 13239683 := bstep (se 1 (by rfl) ⟨9929762, by rfl⟩ : syracuseStep 13239683 = 19859525) B19859525
theorem B8826455 : Blo 2147435 8826455 := bstep (se 1 (by rfl) ⟨6619841, by rfl⟩ : syracuseStep 8826455 = 13239683) B13239683
theorem B23537213 : Blo 2147435 23537213 := bstep (se 3 (by rfl) ⟨4413227, by rfl⟩ : syracuseStep 23537213 = 8826455) B8826455
theorem B15691475 : Blo 2147435 15691475 := bstep (se 1 (by rfl) ⟨11768606, by rfl⟩ : syracuseStep 15691475 = 23537213) B23537213
theorem B10460983 : Blo 2147435 10460983 := bstep (se 1 (by rfl) ⟨7845737, by rfl⟩ : syracuseStep 10460983 = 15691475) B15691475
theorem B13947977 : Blo 2147435 13947977 := bstep (se 2 (by rfl) ⟨5230491, by rfl⟩ : syracuseStep 13947977 = 10460983) B10460983
theorem B9298651 : Blo 2147435 9298651 := bstep (se 1 (by rfl) ⟨6973988, by rfl⟩ : syracuseStep 9298651 = 13947977) B13947977
theorem B12398201 : Blo 2147435 12398201 := bstep (se 2 (by rfl) ⟨4649325, by rfl⟩ : syracuseStep 12398201 = 9298651) B9298651
theorem B8265467 : Blo 2147435 8265467 := bstep (se 1 (by rfl) ⟨6199100, by rfl⟩ : syracuseStep 8265467 = 12398201) B12398201
theorem B5510311 : Blo 2147435 5510311 := bstep (se 1 (by rfl) ⟨4132733, by rfl⟩ : syracuseStep 5510311 = 8265467) B8265467
theorem B117553301 : Blo 2147435 117553301 := bstep (se 6 (by rfl) ⟨2755155, by rfl⟩ : syracuseStep 117553301 = 5510311) B5510311
theorem B78368867 : Blo 2147435 78368867 := bstep (se 1 (by rfl) ⟨58776650, by rfl⟩ : syracuseStep 78368867 = 117553301) B117553301
theorem B52245911 : Blo 2147435 52245911 := bstep (se 1 (by rfl) ⟨39184433, by rfl⟩ : syracuseStep 52245911 = 78368867) B78368867
theorem B34830607 : Blo 2147435 34830607 := bstep (se 1 (by rfl) ⟨26122955, by rfl⟩ : syracuseStep 34830607 = 52245911) B52245911
theorem B46440809 : Blo 2147435 46440809 := bstep (se 2 (by rfl) ⟨17415303, by rfl⟩ : syracuseStep 46440809 = 34830607) B34830607
theorem B30960539 : Blo 2147435 30960539 := bstep (se 1 (by rfl) ⟨23220404, by rfl⟩ : syracuseStep 30960539 = 46440809) B46440809
theorem B20640359 : Blo 2147435 20640359 := bstep (se 1 (by rfl) ⟨15480269, by rfl⟩ : syracuseStep 20640359 = 30960539) B30960539
theorem B13760239 : Blo 2147435 13760239 := bstep (se 1 (by rfl) ⟨10320179, by rfl⟩ : syracuseStep 13760239 = 20640359) B20640359
theorem B18346985 : Blo 2147435 18346985 := bstep (se 2 (by rfl) ⟨6880119, by rfl⟩ : syracuseStep 18346985 = 13760239) B13760239
theorem B12231323 : Blo 2147435 12231323 := bstep (se 1 (by rfl) ⟨9173492, by rfl⟩ : syracuseStep 12231323 = 18346985) B18346985
theorem B8154215 : Blo 2147435 8154215 := bstep (se 1 (by rfl) ⟨6115661, by rfl⟩ : syracuseStep 8154215 = 12231323) B12231323
theorem B5436143 : Blo 2147435 5436143 := bstep (se 1 (by rfl) ⟨4077107, by rfl⟩ : syracuseStep 5436143 = 8154215) B8154215
theorem B3624095 : Blo 2147435 3624095 := bstep (se 1 (by rfl) ⟨2718071, by rfl⟩ : syracuseStep 3624095 = 5436143) B5436143
theorem B2416063 : Blo 2147435 2416063 := bstep (se 1 (by rfl) ⟨1812047, by rfl⟩ : syracuseStep 2416063 = 3624095) B3624095
theorem B3221417 : Blo 2147435 3221417 := bstep (se 2 (by rfl) ⟨1208031, by rfl⟩ : syracuseStep 3221417 = 2416063) B2416063
theorem B2147611 : Blo 2147435 2147611 := bstep (se 1 (by rfl) ⟨1610708, by rfl⟩ : syracuseStep 2147611 = 3221417) B3221417
theorem B8154229 : Blo 2147435 8154229 := bbase (se 5 (by rfl) ⟨382229, by rfl⟩ : syracuseStep 8154229 = 764459) (by norm_num)
theorem B10872305 : Blo 2147435 10872305 := bstep (se 2 (by rfl) ⟨4077114, by rfl⟩ : syracuseStep 10872305 = 8154229) B8154229
theorem B7248203 : Blo 2147435 7248203 := bstep (se 1 (by rfl) ⟨5436152, by rfl⟩ : syracuseStep 7248203 = 10872305) B10872305
theorem B4832135 : Blo 2147435 4832135 := bstep (se 1 (by rfl) ⟨3624101, by rfl⟩ : syracuseStep 4832135 = 7248203) B7248203
theorem B3221423 : Blo 2147435 3221423 := bstep (se 1 (by rfl) ⟨2416067, by rfl⟩ : syracuseStep 3221423 = 4832135) B4832135
theorem B2147615 : Blo 2147435 2147615 := bstep (se 1 (by rfl) ⟨1610711, by rfl⟩ : syracuseStep 2147615 = 3221423) B3221423
theorem B3221429 : Blo 2147435 3221429 := bbase (se 5 (by rfl) ⟨151004, by rfl⟩ : syracuseStep 3221429 = 302009) (by norm_num)
theorem B2147619 : Blo 2147435 2147619 := bstep (se 1 (by rfl) ⟨1610714, by rfl⟩ : syracuseStep 2147619 = 3221429) B3221429
theorem B5436173 : Blo 2147435 5436173 := bbase (se 3 (by rfl) ⟨1019282, by rfl⟩ : syracuseStep 5436173 = 2038565) (by norm_num)
theorem B3624115 : Blo 2147435 3624115 := bstep (se 1 (by rfl) ⟨2718086, by rfl⟩ : syracuseStep 3624115 = 5436173) B5436173
theorem B4832153 : Blo 2147435 4832153 := bstep (se 2 (by rfl) ⟨1812057, by rfl⟩ : syracuseStep 4832153 = 3624115) B3624115
theorem B3221435 : Blo 2147435 3221435 := bstep (se 1 (by rfl) ⟨2416076, by rfl⟩ : syracuseStep 3221435 = 4832153) B4832153
theorem B2147623 : Blo 2147435 2147623 := bstep (se 1 (by rfl) ⟨1610717, by rfl⟩ : syracuseStep 2147623 = 3221435) B3221435
theorem B2416081 : Blo 2147435 2416081 := bbase (se 2 (by rfl) ⟨906030, by rfl⟩ : syracuseStep 2416081 = 1812061) (by norm_num)
theorem B3221441 : Blo 2147435 3221441 := bstep (se 2 (by rfl) ⟨1208040, by rfl⟩ : syracuseStep 3221441 = 2416081) B2416081
theorem B2147627 : Blo 2147435 2147627 := bstep (se 1 (by rfl) ⟨1610720, by rfl⟩ : syracuseStep 2147627 = 3221441) B3221441
theorem B4586789 : Blo 2147435 4586789 := bbase (se 4 (by rfl) ⟨430011, by rfl⟩ : syracuseStep 4586789 = 860023) (by norm_num)
theorem B3057859 : Blo 2147435 3057859 := bstep (se 1 (by rfl) ⟨2293394, by rfl⟩ : syracuseStep 3057859 = 4586789) B4586789
theorem B4077145 : Blo 2147435 4077145 := bstep (se 2 (by rfl) ⟨1528929, by rfl⟩ : syracuseStep 4077145 = 3057859) B3057859
theorem B5436193 : Blo 2147435 5436193 := bstep (se 2 (by rfl) ⟨2038572, by rfl⟩ : syracuseStep 5436193 = 4077145) B4077145
theorem B7248257 : Blo 2147435 7248257 := bstep (se 2 (by rfl) ⟨2718096, by rfl⟩ : syracuseStep 7248257 = 5436193) B5436193
theorem B4832171 : Blo 2147435 4832171 := bstep (se 1 (by rfl) ⟨3624128, by rfl⟩ : syracuseStep 4832171 = 7248257) B7248257
theorem B3221447 : Blo 2147435 3221447 := bstep (se 1 (by rfl) ⟨2416085, by rfl⟩ : syracuseStep 3221447 = 4832171) B4832171
theorem B2147631 : Blo 2147435 2147631 := bstep (se 1 (by rfl) ⟨1610723, by rfl⟩ : syracuseStep 2147631 = 3221447) B3221447
theorem B3221453 : Blo 2147435 3221453 := bbase (se 3 (by rfl) ⟨604022, by rfl⟩ : syracuseStep 3221453 = 1208045) (by norm_num)
theorem B2147635 : Blo 2147435 2147635 := bstep (se 1 (by rfl) ⟨1610726, by rfl⟩ : syracuseStep 2147635 = 3221453) B3221453
theorem B4832189 : Blo 2147435 4832189 := bbase (se 3 (by rfl) ⟨906035, by rfl⟩ : syracuseStep 4832189 = 1812071) (by norm_num)
theorem B3221459 : Blo 2147435 3221459 := bstep (se 1 (by rfl) ⟨2416094, by rfl⟩ : syracuseStep 3221459 = 4832189) B4832189
theorem B2147639 : Blo 2147435 2147639 := bstep (se 1 (by rfl) ⟨1610729, by rfl⟩ : syracuseStep 2147639 = 3221459) B3221459
theorem B3624149 : Blo 2147435 3624149 := bbase (se 7 (by rfl) ⟨42470, by rfl⟩ : syracuseStep 3624149 = 84941) (by norm_num)
theorem B2416099 : Blo 2147435 2416099 := bstep (se 1 (by rfl) ⟨1812074, by rfl⟩ : syracuseStep 2416099 = 3624149) B3624149
theorem B3221465 : Blo 2147435 3221465 := bstep (se 2 (by rfl) ⟨1208049, by rfl⟩ : syracuseStep 3221465 = 2416099) B2416099
theorem B2147643 : Blo 2147435 2147643 := bstep (se 1 (by rfl) ⟨1610732, by rfl⟩ : syracuseStep 2147643 = 3221465) B3221465
theorem B3440117 : Blo 2147435 3440117 := bbase (se 5 (by rfl) ⟨161255, by rfl⟩ : syracuseStep 3440117 = 322511) (by norm_num)
theorem B9173645 : Blo 2147435 9173645 := bstep (se 3 (by rfl) ⟨1720058, by rfl⟩ : syracuseStep 9173645 = 3440117) B3440117
theorem B6115763 : Blo 2147435 6115763 := bstep (se 1 (by rfl) ⟨4586822, by rfl⟩ : syracuseStep 6115763 = 9173645) B9173645
theorem B16308701 : Blo 2147435 16308701 := bstep (se 3 (by rfl) ⟨3057881, by rfl⟩ : syracuseStep 16308701 = 6115763) B6115763
theorem B10872467 : Blo 2147435 10872467 := bstep (se 1 (by rfl) ⟨8154350, by rfl⟩ : syracuseStep 10872467 = 16308701) B16308701
theorem B7248311 : Blo 2147435 7248311 := bstep (se 1 (by rfl) ⟨5436233, by rfl⟩ : syracuseStep 7248311 = 10872467) B10872467
theorem B4832207 : Blo 2147435 4832207 := bstep (se 1 (by rfl) ⟨3624155, by rfl⟩ : syracuseStep 4832207 = 7248311) B7248311
theorem B3221471 : Blo 2147435 3221471 := bstep (se 1 (by rfl) ⟨2416103, by rfl⟩ : syracuseStep 3221471 = 4832207) B4832207
theorem B2147647 : Blo 2147435 2147647 := bstep (se 1 (by rfl) ⟨1610735, by rfl⟩ : syracuseStep 2147647 = 3221471) B3221471
theorem B3221477 : Blo 2147435 3221477 := bbase (se 4 (by rfl) ⟨302013, by rfl⟩ : syracuseStep 3221477 = 604027) (by norm_num)
theorem B2147651 : Blo 2147435 2147651 := bstep (se 1 (by rfl) ⟨1610738, by rfl⟩ : syracuseStep 2147651 = 3221477) B3221477
theorem B6880261 : Blo 2147435 6880261 := bbase (se 4 (by rfl) ⟨645024, by rfl⟩ : syracuseStep 6880261 = 1290049) (by norm_num)
theorem B9173681 : Blo 2147435 9173681 := bstep (se 2 (by rfl) ⟨3440130, by rfl⟩ : syracuseStep 9173681 = 6880261) B6880261
theorem B6115787 : Blo 2147435 6115787 := bstep (se 1 (by rfl) ⟨4586840, by rfl⟩ : syracuseStep 6115787 = 9173681) B9173681
theorem B4077191 : Blo 2147435 4077191 := bstep (se 1 (by rfl) ⟨3057893, by rfl⟩ : syracuseStep 4077191 = 6115787) B6115787
theorem B2718127 : Blo 2147435 2718127 := bstep (se 1 (by rfl) ⟨2038595, by rfl⟩ : syracuseStep 2718127 = 4077191) B4077191
theorem B3624169 : Blo 2147435 3624169 := bstep (se 2 (by rfl) ⟨1359063, by rfl⟩ : syracuseStep 3624169 = 2718127) B2718127
theorem B4832225 : Blo 2147435 4832225 := bstep (se 2 (by rfl) ⟨1812084, by rfl⟩ : syracuseStep 4832225 = 3624169) B3624169
theorem B3221483 : Blo 2147435 3221483 := bstep (se 1 (by rfl) ⟨2416112, by rfl⟩ : syracuseStep 3221483 = 4832225) B4832225
theorem B2147655 : Blo 2147435 2147655 := bstep (se 1 (by rfl) ⟨1610741, by rfl⟩ : syracuseStep 2147655 = 3221483) B3221483
theorem B2416117 : Blo 2147435 2416117 := bbase (se 5 (by rfl) ⟨113255, by rfl⟩ : syracuseStep 2416117 = 226511) (by norm_num)
theorem B3221489 : Blo 2147435 3221489 := bstep (se 2 (by rfl) ⟨1208058, by rfl⟩ : syracuseStep 3221489 = 2416117) B2416117
theorem B2147659 : Blo 2147435 2147659 := bstep (se 1 (by rfl) ⟨1610744, by rfl⟩ : syracuseStep 2147659 = 3221489) B3221489
theorem B2718137 : Blo 2147435 2718137 := bbase (se 2 (by rfl) ⟨1019301, by rfl⟩ : syracuseStep 2718137 = 2038603) (by norm_num)
theorem B7248365 : Blo 2147435 7248365 := bstep (se 3 (by rfl) ⟨1359068, by rfl⟩ : syracuseStep 7248365 = 2718137) B2718137
theorem B4832243 : Blo 2147435 4832243 := bstep (se 1 (by rfl) ⟨3624182, by rfl⟩ : syracuseStep 4832243 = 7248365) B7248365
theorem B3221495 : Blo 2147435 3221495 := bstep (se 1 (by rfl) ⟨2416121, by rfl⟩ : syracuseStep 3221495 = 4832243) B4832243
theorem B2147663 : Blo 2147435 2147663 := bstep (se 1 (by rfl) ⟨1610747, by rfl⟩ : syracuseStep 2147663 = 3221495) B3221495
theorem B3221501 : Blo 2147435 3221501 := bbase (se 3 (by rfl) ⟨604031, by rfl⟩ : syracuseStep 3221501 = 1208063) (by norm_num)
theorem B2147667 : Blo 2147435 2147667 := bstep (se 1 (by rfl) ⟨1610750, by rfl⟩ : syracuseStep 2147667 = 3221501) B3221501
theorem B4832261 : Blo 2147435 4832261 := bbase (se 4 (by rfl) ⟨453024, by rfl⟩ : syracuseStep 4832261 = 906049) (by norm_num)
theorem B3221507 : Blo 2147435 3221507 := bstep (se 1 (by rfl) ⟨2416130, by rfl⟩ : syracuseStep 3221507 = 4832261) B4832261
theorem B2147671 : Blo 2147435 2147671 := bstep (se 1 (by rfl) ⟨1610753, by rfl⟩ : syracuseStep 2147671 = 3221507) B3221507
theorem B4077229 : Blo 2147435 4077229 := bbase (se 3 (by rfl) ⟨764480, by rfl⟩ : syracuseStep 4077229 = 1528961) (by norm_num)
theorem B5436305 : Blo 2147435 5436305 := bstep (se 2 (by rfl) ⟨2038614, by rfl⟩ : syracuseStep 5436305 = 4077229) B4077229
theorem B3624203 : Blo 2147435 3624203 := bstep (se 1 (by rfl) ⟨2718152, by rfl⟩ : syracuseStep 3624203 = 5436305) B5436305
theorem B2416135 : Blo 2147435 2416135 := bstep (se 1 (by rfl) ⟨1812101, by rfl⟩ : syracuseStep 2416135 = 3624203) B3624203
theorem B3221513 : Blo 2147435 3221513 := bstep (se 2 (by rfl) ⟨1208067, by rfl⟩ : syracuseStep 3221513 = 2416135) B2416135
theorem B2147675 : Blo 2147435 2147675 := bstep (se 1 (by rfl) ⟨1610756, by rfl⟩ : syracuseStep 2147675 = 3221513) B3221513
theorem B10872629 : Blo 2147435 10872629 := bbase (se 5 (by rfl) ⟨509654, by rfl⟩ : syracuseStep 10872629 = 1019309) (by norm_num)
theorem B7248419 : Blo 2147435 7248419 := bstep (se 1 (by rfl) ⟨5436314, by rfl⟩ : syracuseStep 7248419 = 10872629) B10872629
theorem B4832279 : Blo 2147435 4832279 := bstep (se 1 (by rfl) ⟨3624209, by rfl⟩ : syracuseStep 4832279 = 7248419) B7248419
theorem B3221519 : Blo 2147435 3221519 := bstep (se 1 (by rfl) ⟨2416139, by rfl⟩ : syracuseStep 3221519 = 4832279) B4832279
theorem B2147679 : Blo 2147435 2147679 := bstep (se 1 (by rfl) ⟨1610759, by rfl⟩ : syracuseStep 2147679 = 3221519) B3221519
theorem B3221525 : Blo 2147435 3221525 := bbase (se 6 (by rfl) ⟨75504, by rfl⟩ : syracuseStep 3221525 = 151009) (by norm_num)
theorem B2147683 : Blo 2147435 2147683 := bstep (se 1 (by rfl) ⟨1610762, by rfl⟩ : syracuseStep 2147683 = 3221525) B3221525
theorem B13760725 : Blo 2147435 13760725 := bbase (se 7 (by rfl) ⟨161258, by rfl⟩ : syracuseStep 13760725 = 322517) (by norm_num)
theorem B18347633 : Blo 2147435 18347633 := bstep (se 2 (by rfl) ⟨6880362, by rfl⟩ : syracuseStep 18347633 = 13760725) B13760725
theorem B12231755 : Blo 2147435 12231755 := bstep (se 1 (by rfl) ⟨9173816, by rfl⟩ : syracuseStep 12231755 = 18347633) B18347633
theorem B8154503 : Blo 2147435 8154503 := bstep (se 1 (by rfl) ⟨6115877, by rfl⟩ : syracuseStep 8154503 = 12231755) B12231755
theorem B5436335 : Blo 2147435 5436335 := bstep (se 1 (by rfl) ⟨4077251, by rfl⟩ : syracuseStep 5436335 = 8154503) B8154503
theorem B3624223 : Blo 2147435 3624223 := bstep (se 1 (by rfl) ⟨2718167, by rfl⟩ : syracuseStep 3624223 = 5436335) B5436335
theorem B4832297 : Blo 2147435 4832297 := bstep (se 2 (by rfl) ⟨1812111, by rfl⟩ : syracuseStep 4832297 = 3624223) B3624223
theorem B3221531 : Blo 2147435 3221531 := bstep (se 1 (by rfl) ⟨2416148, by rfl⟩ : syracuseStep 3221531 = 4832297) B4832297
theorem B2147687 : Blo 2147435 2147687 := bstep (se 1 (by rfl) ⟨1610765, by rfl⟩ : syracuseStep 2147687 = 3221531) B3221531
theorem B2416153 : Blo 2147435 2416153 := bbase (se 2 (by rfl) ⟨906057, by rfl⟩ : syracuseStep 2416153 = 1812115) (by norm_num)
theorem B3221537 : Blo 2147435 3221537 := bstep (se 2 (by rfl) ⟨1208076, by rfl⟩ : syracuseStep 3221537 = 2416153) B2416153
theorem B2147691 : Blo 2147435 2147691 := bstep (se 1 (by rfl) ⟨1610768, by rfl⟩ : syracuseStep 2147691 = 3221537) B3221537
theorem B8154533 : Blo 2147435 8154533 := bbase (se 4 (by rfl) ⟨764487, by rfl⟩ : syracuseStep 8154533 = 1528975) (by norm_num)
theorem B5436355 : Blo 2147435 5436355 := bstep (se 1 (by rfl) ⟨4077266, by rfl⟩ : syracuseStep 5436355 = 8154533) B8154533
theorem B7248473 : Blo 2147435 7248473 := bstep (se 2 (by rfl) ⟨2718177, by rfl⟩ : syracuseStep 7248473 = 5436355) B5436355
theorem B4832315 : Blo 2147435 4832315 := bstep (se 1 (by rfl) ⟨3624236, by rfl⟩ : syracuseStep 4832315 = 7248473) B7248473
theorem B3221543 : Blo 2147435 3221543 := bstep (se 1 (by rfl) ⟨2416157, by rfl⟩ : syracuseStep 3221543 = 4832315) B4832315
theorem B2147695 : Blo 2147435 2147695 := bstep (se 1 (by rfl) ⟨1610771, by rfl⟩ : syracuseStep 2147695 = 3221543) B3221543
theorem B3221549 : Blo 2147435 3221549 := bbase (se 3 (by rfl) ⟨604040, by rfl⟩ : syracuseStep 3221549 = 1208081) (by norm_num)
theorem B2147699 : Blo 2147435 2147699 := bstep (se 1 (by rfl) ⟨1610774, by rfl⟩ : syracuseStep 2147699 = 3221549) B3221549
theorem B4832333 : Blo 2147435 4832333 := bbase (se 3 (by rfl) ⟨906062, by rfl⟩ : syracuseStep 4832333 = 1812125) (by norm_num)
theorem B3221555 : Blo 2147435 3221555 := bstep (se 1 (by rfl) ⟨2416166, by rfl⟩ : syracuseStep 3221555 = 4832333) B4832333
theorem B2147703 : Blo 2147435 2147703 := bstep (se 1 (by rfl) ⟨1610777, by rfl⟩ : syracuseStep 2147703 = 3221555) B3221555
theorem B2718193 : Blo 2147435 2718193 := bbase (se 2 (by rfl) ⟨1019322, by rfl⟩ : syracuseStep 2718193 = 2038645) (by norm_num)
theorem B3624257 : Blo 2147435 3624257 := bstep (se 2 (by rfl) ⟨1359096, by rfl⟩ : syracuseStep 3624257 = 2718193) B2718193
theorem B2416171 : Blo 2147435 2416171 := bstep (se 1 (by rfl) ⟨1812128, by rfl⟩ : syracuseStep 2416171 = 3624257) B3624257
theorem B3221561 : Blo 2147435 3221561 := bstep (se 2 (by rfl) ⟨1208085, by rfl⟩ : syracuseStep 3221561 = 2416171) B2416171
theorem B2147707 : Blo 2147435 2147707 := bstep (se 1 (by rfl) ⟨1610780, by rfl⟩ : syracuseStep 2147707 = 3221561) B3221561
theorem B9796565 : Blo 2147435 9796565 := bbase (se 7 (by rfl) ⟨114803, by rfl⟩ : syracuseStep 9796565 = 229607) (by norm_num)
theorem B6531043 : Blo 2147435 6531043 := bstep (se 1 (by rfl) ⟨4898282, by rfl⟩ : syracuseStep 6531043 = 9796565) B9796565
theorem B8708057 : Blo 2147435 8708057 := bstep (se 2 (by rfl) ⟨3265521, by rfl⟩ : syracuseStep 8708057 = 6531043) B6531043
theorem B5805371 : Blo 2147435 5805371 := bstep (se 1 (by rfl) ⟨4354028, by rfl⟩ : syracuseStep 5805371 = 8708057) B8708057
theorem B15480989 : Blo 2147435 15480989 := bstep (se 3 (by rfl) ⟨2902685, by rfl⟩ : syracuseStep 15480989 = 5805371) B5805371
theorem B10320659 : Blo 2147435 10320659 := bstep (se 1 (by rfl) ⟨7740494, by rfl⟩ : syracuseStep 10320659 = 15480989) B15480989
theorem B6880439 : Blo 2147435 6880439 := bstep (se 1 (by rfl) ⟨5160329, by rfl⟩ : syracuseStep 6880439 = 10320659) B10320659
theorem B4586959 : Blo 2147435 4586959 := bstep (se 1 (by rfl) ⟨3440219, by rfl⟩ : syracuseStep 4586959 = 6880439) B6880439
theorem B24463781 : Blo 2147435 24463781 := bstep (se 4 (by rfl) ⟨2293479, by rfl⟩ : syracuseStep 24463781 = 4586959) B4586959
theorem B16309187 : Blo 2147435 16309187 := bstep (se 1 (by rfl) ⟨12231890, by rfl⟩ : syracuseStep 16309187 = 24463781) B24463781
theorem B10872791 : Blo 2147435 10872791 := bstep (se 1 (by rfl) ⟨8154593, by rfl⟩ : syracuseStep 10872791 = 16309187) B16309187
theorem B7248527 : Blo 2147435 7248527 := bstep (se 1 (by rfl) ⟨5436395, by rfl⟩ : syracuseStep 7248527 = 10872791) B10872791
theorem B4832351 : Blo 2147435 4832351 := bstep (se 1 (by rfl) ⟨3624263, by rfl⟩ : syracuseStep 4832351 = 7248527) B7248527
theorem B3221567 : Blo 2147435 3221567 := bstep (se 1 (by rfl) ⟨2416175, by rfl⟩ : syracuseStep 3221567 = 4832351) B4832351
theorem B2147711 : Blo 2147435 2147711 := bstep (se 1 (by rfl) ⟨1610783, by rfl⟩ : syracuseStep 2147711 = 3221567) B3221567
theorem B3221573 : Blo 2147435 3221573 := bbase (se 4 (by rfl) ⟨302022, by rfl⟩ : syracuseStep 3221573 = 604045) (by norm_num)
theorem B2147715 : Blo 2147435 2147715 := bstep (se 1 (by rfl) ⟨1610786, by rfl⟩ : syracuseStep 2147715 = 3221573) B3221573
theorem B3624277 : Blo 2147435 3624277 := bbase (se 11 (by rfl) ⟨2654, by rfl⟩ : syracuseStep 3624277 = 5309) (by norm_num)
theorem B4832369 : Blo 2147435 4832369 := bstep (se 2 (by rfl) ⟨1812138, by rfl⟩ : syracuseStep 4832369 = 3624277) B3624277
theorem B3221579 : Blo 2147435 3221579 := bstep (se 1 (by rfl) ⟨2416184, by rfl⟩ : syracuseStep 3221579 = 4832369) B4832369
theorem B2147719 : Blo 2147435 2147719 := bstep (se 1 (by rfl) ⟨1610789, by rfl⟩ : syracuseStep 2147719 = 3221579) B3221579
theorem B2416189 : Blo 2147435 2416189 := bbase (se 3 (by rfl) ⟨453035, by rfl⟩ : syracuseStep 2416189 = 906071) (by norm_num)
theorem B3221585 : Blo 2147435 3221585 := bstep (se 2 (by rfl) ⟨1208094, by rfl⟩ : syracuseStep 3221585 = 2416189) B2416189
theorem B2147723 : Blo 2147435 2147723 := bstep (se 1 (by rfl) ⟨1610792, by rfl⟩ : syracuseStep 2147723 = 3221585) B3221585
theorem B7248581 : Blo 2147435 7248581 := bbase (se 4 (by rfl) ⟨679554, by rfl⟩ : syracuseStep 7248581 = 1359109) (by norm_num)
theorem B4832387 : Blo 2147435 4832387 := bstep (se 1 (by rfl) ⟨3624290, by rfl⟩ : syracuseStep 4832387 = 7248581) B7248581
theorem B3221591 : Blo 2147435 3221591 := bstep (se 1 (by rfl) ⟨2416193, by rfl⟩ : syracuseStep 3221591 = 4832387) B4832387
theorem B2147727 : Blo 2147435 2147727 := bstep (se 1 (by rfl) ⟨1610795, by rfl⟩ : syracuseStep 2147727 = 3221591) B3221591
theorem B3221597 : Blo 2147435 3221597 := bbase (se 3 (by rfl) ⟨604049, by rfl⟩ : syracuseStep 3221597 = 1208099) (by norm_num)
theorem B2147731 : Blo 2147435 2147731 := bstep (se 1 (by rfl) ⟨1610798, by rfl⟩ : syracuseStep 2147731 = 3221597) B3221597
theorem B4832405 : Blo 2147435 4832405 := bbase (se 6 (by rfl) ⟨113259, by rfl⟩ : syracuseStep 4832405 = 226519) (by norm_num)
theorem B3221603 : Blo 2147435 3221603 := bstep (se 1 (by rfl) ⟨2416202, by rfl⟩ : syracuseStep 3221603 = 4832405) B4832405
theorem B2147735 : Blo 2147435 2147735 := bstep (se 1 (by rfl) ⟨1610801, by rfl⟩ : syracuseStep 2147735 = 3221603) B3221603
theorem B3058013 : Blo 2147435 3058013 := bbase (se 3 (by rfl) ⟨573377, by rfl⟩ : syracuseStep 3058013 = 1146755) (by norm_num)
theorem B8154701 : Blo 2147435 8154701 := bstep (se 3 (by rfl) ⟨1529006, by rfl⟩ : syracuseStep 8154701 = 3058013) B3058013
theorem B5436467 : Blo 2147435 5436467 := bstep (se 1 (by rfl) ⟨4077350, by rfl⟩ : syracuseStep 5436467 = 8154701) B8154701
theorem B3624311 : Blo 2147435 3624311 := bstep (se 1 (by rfl) ⟨2718233, by rfl⟩ : syracuseStep 3624311 = 5436467) B5436467
theorem B2416207 : Blo 2147435 2416207 := bstep (se 1 (by rfl) ⟨1812155, by rfl⟩ : syracuseStep 2416207 = 3624311) B3624311
theorem B3221609 : Blo 2147435 3221609 := bstep (se 2 (by rfl) ⟨1208103, by rfl⟩ : syracuseStep 3221609 = 2416207) B2416207
theorem B2147739 : Blo 2147435 2147739 := bstep (se 1 (by rfl) ⟨1610804, by rfl⟩ : syracuseStep 2147739 = 3221609) B3221609
theorem B4354093 : Blo 2147435 4354093 := bbase (se 3 (by rfl) ⟨816392, by rfl⟩ : syracuseStep 4354093 = 1632785) (by norm_num)
theorem B23221829 : Blo 2147435 23221829 := bstep (se 4 (by rfl) ⟨2177046, by rfl⟩ : syracuseStep 23221829 = 4354093) B4354093
theorem B15481219 : Blo 2147435 15481219 := bstep (se 1 (by rfl) ⟨11610914, by rfl⟩ : syracuseStep 15481219 = 23221829) B23221829
theorem B20641625 : Blo 2147435 20641625 := bstep (se 2 (by rfl) ⟨7740609, by rfl⟩ : syracuseStep 20641625 = 15481219) B15481219
theorem B13761083 : Blo 2147435 13761083 := bstep (se 1 (by rfl) ⟨10320812, by rfl⟩ : syracuseStep 13761083 = 20641625) B20641625
theorem B9174055 : Blo 2147435 9174055 := bstep (se 1 (by rfl) ⟨6880541, by rfl⟩ : syracuseStep 9174055 = 13761083) B13761083
theorem B12232073 : Blo 2147435 12232073 := bstep (se 2 (by rfl) ⟨4587027, by rfl⟩ : syracuseStep 12232073 = 9174055) B9174055
theorem B8154715 : Blo 2147435 8154715 := bstep (se 1 (by rfl) ⟨6116036, by rfl⟩ : syracuseStep 8154715 = 12232073) B12232073
theorem B10872953 : Blo 2147435 10872953 := bstep (se 2 (by rfl) ⟨4077357, by rfl⟩ : syracuseStep 10872953 = 8154715) B8154715
theorem B7248635 : Blo 2147435 7248635 := bstep (se 1 (by rfl) ⟨5436476, by rfl⟩ : syracuseStep 7248635 = 10872953) B10872953
theorem B4832423 : Blo 2147435 4832423 := bstep (se 1 (by rfl) ⟨3624317, by rfl⟩ : syracuseStep 4832423 = 7248635) B7248635
theorem B3221615 : Blo 2147435 3221615 := bstep (se 1 (by rfl) ⟨2416211, by rfl⟩ : syracuseStep 3221615 = 4832423) B4832423
theorem B2147743 : Blo 2147435 2147743 := bstep (se 1 (by rfl) ⟨1610807, by rfl⟩ : syracuseStep 2147743 = 3221615) B3221615
theorem B3221621 : Blo 2147435 3221621 := bbase (se 5 (by rfl) ⟨151013, by rfl⟩ : syracuseStep 3221621 = 302027) (by norm_num)
theorem B2147747 : Blo 2147435 2147747 := bstep (se 1 (by rfl) ⟨1610810, by rfl⟩ : syracuseStep 2147747 = 3221621) B3221621
theorem B4077373 : Blo 2147435 4077373 := bbase (se 3 (by rfl) ⟨764507, by rfl⟩ : syracuseStep 4077373 = 1529015) (by norm_num)
theorem B5436497 : Blo 2147435 5436497 := bstep (se 2 (by rfl) ⟨2038686, by rfl⟩ : syracuseStep 5436497 = 4077373) B4077373
theorem B3624331 : Blo 2147435 3624331 := bstep (se 1 (by rfl) ⟨2718248, by rfl⟩ : syracuseStep 3624331 = 5436497) B5436497
theorem B4832441 : Blo 2147435 4832441 := bstep (se 2 (by rfl) ⟨1812165, by rfl⟩ : syracuseStep 4832441 = 3624331) B3624331
theorem B3221627 : Blo 2147435 3221627 := bstep (se 1 (by rfl) ⟨2416220, by rfl⟩ : syracuseStep 3221627 = 4832441) B4832441
theorem B2147751 : Blo 2147435 2147751 := bstep (se 1 (by rfl) ⟨1610813, by rfl⟩ : syracuseStep 2147751 = 3221627) B3221627
theorem B2416225 : Blo 2147435 2416225 := bbase (se 2 (by rfl) ⟨906084, by rfl⟩ : syracuseStep 2416225 = 1812169) (by norm_num)
theorem B3221633 : Blo 2147435 3221633 := bstep (se 2 (by rfl) ⟨1208112, by rfl⟩ : syracuseStep 3221633 = 2416225) B2416225
theorem B2147755 : Blo 2147435 2147755 := bstep (se 1 (by rfl) ⟨1610816, by rfl⟩ : syracuseStep 2147755 = 3221633) B3221633
theorem B5436517 : Blo 2147435 5436517 := bbase (se 4 (by rfl) ⟨509673, by rfl⟩ : syracuseStep 5436517 = 1019347) (by norm_num)
theorem B7248689 : Blo 2147435 7248689 := bstep (se 2 (by rfl) ⟨2718258, by rfl⟩ : syracuseStep 7248689 = 5436517) B5436517
theorem B4832459 : Blo 2147435 4832459 := bstep (se 1 (by rfl) ⟨3624344, by rfl⟩ : syracuseStep 4832459 = 7248689) B7248689
theorem B3221639 : Blo 2147435 3221639 := bstep (se 1 (by rfl) ⟨2416229, by rfl⟩ : syracuseStep 3221639 = 4832459) B4832459
theorem B2147759 : Blo 2147435 2147759 := bstep (se 1 (by rfl) ⟨1610819, by rfl⟩ : syracuseStep 2147759 = 3221639) B3221639
theorem B3221645 : Blo 2147435 3221645 := bbase (se 3 (by rfl) ⟨604058, by rfl⟩ : syracuseStep 3221645 = 1208117) (by norm_num)
theorem B2147763 : Blo 2147435 2147763 := bstep (se 1 (by rfl) ⟨1610822, by rfl⟩ : syracuseStep 2147763 = 3221645) B3221645
theorem B4832477 : Blo 2147435 4832477 := bbase (se 3 (by rfl) ⟨906089, by rfl⟩ : syracuseStep 4832477 = 1812179) (by norm_num)
theorem B3221651 : Blo 2147435 3221651 := bstep (se 1 (by rfl) ⟨2416238, by rfl⟩ : syracuseStep 3221651 = 4832477) B4832477
theorem B2147767 : Blo 2147435 2147767 := bstep (se 1 (by rfl) ⟨1610825, by rfl⟩ : syracuseStep 2147767 = 3221651) B3221651
theorem B3624365 : Blo 2147435 3624365 := bbase (se 3 (by rfl) ⟨679568, by rfl⟩ : syracuseStep 3624365 = 1359137) (by norm_num)
theorem B2416243 : Blo 2147435 2416243 := bstep (se 1 (by rfl) ⟨1812182, by rfl⟩ : syracuseStep 2416243 = 3624365) B3624365
theorem B3221657 : Blo 2147435 3221657 := bstep (se 2 (by rfl) ⟨1208121, by rfl⟩ : syracuseStep 3221657 = 2416243) B2416243
theorem B2147771 : Blo 2147435 2147771 := bstep (se 1 (by rfl) ⟨1610828, by rfl⟩ : syracuseStep 2147771 = 3221657) B3221657
theorem B6199573 : Blo 2147435 6199573 := bbase (se 6 (by rfl) ⟨145302, by rfl⟩ : syracuseStep 6199573 = 290605) (by norm_num)
theorem B8266097 : Blo 2147435 8266097 := bstep (se 2 (by rfl) ⟨3099786, by rfl⟩ : syracuseStep 8266097 = 6199573) B6199573
theorem B22042925 : Blo 2147435 22042925 := bstep (se 3 (by rfl) ⟨4133048, by rfl⟩ : syracuseStep 22042925 = 8266097) B8266097
theorem B14695283 : Blo 2147435 14695283 := bstep (se 1 (by rfl) ⟨11021462, by rfl⟩ : syracuseStep 14695283 = 22042925) B22042925
theorem B9796855 : Blo 2147435 9796855 := bstep (se 1 (by rfl) ⟨7347641, by rfl⟩ : syracuseStep 9796855 = 14695283) B14695283
theorem B13062473 : Blo 2147435 13062473 := bstep (se 2 (by rfl) ⟨4898427, by rfl⟩ : syracuseStep 13062473 = 9796855) B9796855
theorem B8708315 : Blo 2147435 8708315 := bstep (se 1 (by rfl) ⟨6531236, by rfl⟩ : syracuseStep 8708315 = 13062473) B13062473
theorem B92888693 : Blo 2147435 92888693 := bstep (se 5 (by rfl) ⟨4354157, by rfl⟩ : syracuseStep 92888693 = 8708315) B8708315
theorem B61925795 : Blo 2147435 61925795 := bstep (se 1 (by rfl) ⟨46444346, by rfl⟩ : syracuseStep 61925795 = 92888693) B92888693
theorem B41283863 : Blo 2147435 41283863 := bstep (se 1 (by rfl) ⟨30962897, by rfl⟩ : syracuseStep 41283863 = 61925795) B61925795
theorem B27522575 : Blo 2147435 27522575 := bstep (se 1 (by rfl) ⟨20641931, by rfl⟩ : syracuseStep 27522575 = 41283863) B41283863
theorem B18348383 : Blo 2147435 18348383 := bstep (se 1 (by rfl) ⟨13761287, by rfl⟩ : syracuseStep 18348383 = 27522575) B27522575
theorem B12232255 : Blo 2147435 12232255 := bstep (se 1 (by rfl) ⟨9174191, by rfl⟩ : syracuseStep 12232255 = 18348383) B18348383
theorem B16309673 : Blo 2147435 16309673 := bstep (se 2 (by rfl) ⟨6116127, by rfl⟩ : syracuseStep 16309673 = 12232255) B12232255
theorem B10873115 : Blo 2147435 10873115 := bstep (se 1 (by rfl) ⟨8154836, by rfl⟩ : syracuseStep 10873115 = 16309673) B16309673
theorem B7248743 : Blo 2147435 7248743 := bstep (se 1 (by rfl) ⟨5436557, by rfl⟩ : syracuseStep 7248743 = 10873115) B10873115
theorem B4832495 : Blo 2147435 4832495 := bstep (se 1 (by rfl) ⟨3624371, by rfl⟩ : syracuseStep 4832495 = 7248743) B7248743
theorem B3221663 : Blo 2147435 3221663 := bstep (se 1 (by rfl) ⟨2416247, by rfl⟩ : syracuseStep 3221663 = 4832495) B4832495
theorem B2147775 : Blo 2147435 2147775 := bstep (se 1 (by rfl) ⟨1610831, by rfl⟩ : syracuseStep 2147775 = 3221663) B3221663
theorem B3221669 : Blo 2147435 3221669 := bbase (se 4 (by rfl) ⟨302031, by rfl⟩ : syracuseStep 3221669 = 604063) (by norm_num)
theorem B2147779 : Blo 2147435 2147779 := bstep (se 1 (by rfl) ⟨1610834, by rfl⟩ : syracuseStep 2147779 = 3221669) B3221669
theorem B2718289 : Blo 2147435 2718289 := bbase (se 2 (by rfl) ⟨1019358, by rfl⟩ : syracuseStep 2718289 = 2038717) (by norm_num)
theorem B3624385 : Blo 2147435 3624385 := bstep (se 2 (by rfl) ⟨1359144, by rfl⟩ : syracuseStep 3624385 = 2718289) B2718289
theorem B4832513 : Blo 2147435 4832513 := bstep (se 2 (by rfl) ⟨1812192, by rfl⟩ : syracuseStep 4832513 = 3624385) B3624385
theorem B3221675 : Blo 2147435 3221675 := bstep (se 1 (by rfl) ⟨2416256, by rfl⟩ : syracuseStep 3221675 = 4832513) B4832513
theorem B2147783 : Blo 2147435 2147783 := bstep (se 1 (by rfl) ⟨1610837, by rfl⟩ : syracuseStep 2147783 = 3221675) B3221675
theorem B2416261 : Blo 2147435 2416261 := bbase (se 4 (by rfl) ⟨226524, by rfl⟩ : syracuseStep 2416261 = 453049) (by norm_num)
theorem B3221681 : Blo 2147435 3221681 := bstep (se 2 (by rfl) ⟨1208130, by rfl⟩ : syracuseStep 3221681 = 2416261) B2416261
theorem B2147787 : Blo 2147435 2147787 := bstep (se 1 (by rfl) ⟨1610840, by rfl⟩ : syracuseStep 2147787 = 3221681) B3221681
theorem B5805589 : Blo 2147435 5805589 := bbase (se 6 (by rfl) ⟨136068, by rfl⟩ : syracuseStep 5805589 = 272137) (by norm_num)
theorem B7740785 : Blo 2147435 7740785 := bstep (se 2 (by rfl) ⟨2902794, by rfl⟩ : syracuseStep 7740785 = 5805589) B5805589
theorem B5160523 : Blo 2147435 5160523 := bstep (se 1 (by rfl) ⟨3870392, by rfl⟩ : syracuseStep 5160523 = 7740785) B7740785
theorem B6880697 : Blo 2147435 6880697 := bstep (se 2 (by rfl) ⟨2580261, by rfl⟩ : syracuseStep 6880697 = 5160523) B5160523
theorem B4587131 : Blo 2147435 4587131 := bstep (se 1 (by rfl) ⟨3440348, by rfl⟩ : syracuseStep 4587131 = 6880697) B6880697
theorem B3058087 : Blo 2147435 3058087 := bstep (se 1 (by rfl) ⟨2293565, by rfl⟩ : syracuseStep 3058087 = 4587131) B4587131
theorem B4077449 : Blo 2147435 4077449 := bstep (se 2 (by rfl) ⟨1529043, by rfl⟩ : syracuseStep 4077449 = 3058087) B3058087
theorem B2718299 : Blo 2147435 2718299 := bstep (se 1 (by rfl) ⟨2038724, by rfl⟩ : syracuseStep 2718299 = 4077449) B4077449
theorem B7248797 : Blo 2147435 7248797 := bstep (se 3 (by rfl) ⟨1359149, by rfl⟩ : syracuseStep 7248797 = 2718299) B2718299
theorem B4832531 : Blo 2147435 4832531 := bstep (se 1 (by rfl) ⟨3624398, by rfl⟩ : syracuseStep 4832531 = 7248797) B7248797
theorem B3221687 : Blo 2147435 3221687 := bstep (se 1 (by rfl) ⟨2416265, by rfl⟩ : syracuseStep 3221687 = 4832531) B4832531
theorem B2147791 : Blo 2147435 2147791 := bstep (se 1 (by rfl) ⟨1610843, by rfl⟩ : syracuseStep 2147791 = 3221687) B3221687
theorem B3221693 : Blo 2147435 3221693 := bbase (se 3 (by rfl) ⟨604067, by rfl⟩ : syracuseStep 3221693 = 1208135) (by norm_num)
theorem B2147795 : Blo 2147435 2147795 := bstep (se 1 (by rfl) ⟨1610846, by rfl⟩ : syracuseStep 2147795 = 3221693) B3221693
theorem B4832549 : Blo 2147435 4832549 := bbase (se 4 (by rfl) ⟨453051, by rfl⟩ : syracuseStep 4832549 = 906103) (by norm_num)
theorem B3221699 : Blo 2147435 3221699 := bstep (se 1 (by rfl) ⟨2416274, by rfl⟩ : syracuseStep 3221699 = 4832549) B4832549
theorem B2147799 : Blo 2147435 2147799 := bstep (se 1 (by rfl) ⟨1610849, by rfl⟩ : syracuseStep 2147799 = 3221699) B3221699
theorem B5436629 : Blo 2147435 5436629 := bbase (se 7 (by rfl) ⟨63710, by rfl⟩ : syracuseStep 5436629 = 127421) (by norm_num)
theorem B3624419 : Blo 2147435 3624419 := bstep (se 1 (by rfl) ⟨2718314, by rfl⟩ : syracuseStep 3624419 = 5436629) B5436629
theorem B2416279 : Blo 2147435 2416279 := bstep (se 1 (by rfl) ⟨1812209, by rfl⟩ : syracuseStep 2416279 = 3624419) B3624419
theorem B3221705 : Blo 2147435 3221705 := bstep (se 2 (by rfl) ⟨1208139, by rfl⟩ : syracuseStep 3221705 = 2416279) B2416279
theorem B2147803 : Blo 2147435 2147803 := bstep (se 1 (by rfl) ⟨1610852, by rfl⟩ : syracuseStep 2147803 = 3221705) B3221705
theorem B2615485 : Blo 2147435 2615485 := bbase (se 3 (by rfl) ⟨490403, by rfl⟩ : syracuseStep 2615485 = 980807) (by norm_num)
theorem B3487313 : Blo 2147435 3487313 := bstep (se 2 (by rfl) ⟨1307742, by rfl⟩ : syracuseStep 3487313 = 2615485) B2615485
theorem B9299501 : Blo 2147435 9299501 := bstep (se 3 (by rfl) ⟨1743656, by rfl⟩ : syracuseStep 9299501 = 3487313) B3487313
theorem B6199667 : Blo 2147435 6199667 := bstep (se 1 (by rfl) ⟨4649750, by rfl⟩ : syracuseStep 6199667 = 9299501) B9299501
theorem B4133111 : Blo 2147435 4133111 := bstep (se 1 (by rfl) ⟨3099833, by rfl⟩ : syracuseStep 4133111 = 6199667) B6199667
theorem B44086517 : Blo 2147435 44086517 := bstep (se 5 (by rfl) ⟨2066555, by rfl⟩ : syracuseStep 44086517 = 4133111) B4133111
theorem B29391011 : Blo 2147435 29391011 := bstep (se 1 (by rfl) ⟨22043258, by rfl⟩ : syracuseStep 29391011 = 44086517) B44086517
theorem B19594007 : Blo 2147435 19594007 := bstep (se 1 (by rfl) ⟨14695505, by rfl⟩ : syracuseStep 19594007 = 29391011) B29391011
theorem B13062671 : Blo 2147435 13062671 := bstep (se 1 (by rfl) ⟨9797003, by rfl⟩ : syracuseStep 13062671 = 19594007) B19594007
theorem B8708447 : Blo 2147435 8708447 := bstep (se 1 (by rfl) ⟨6531335, by rfl⟩ : syracuseStep 8708447 = 13062671) B13062671
theorem B5805631 : Blo 2147435 5805631 := bstep (se 1 (by rfl) ⟨4354223, by rfl⟩ : syracuseStep 5805631 = 8708447) B8708447
theorem B7740841 : Blo 2147435 7740841 := bstep (se 2 (by rfl) ⟨2902815, by rfl⟩ : syracuseStep 7740841 = 5805631) B5805631
theorem B10321121 : Blo 2147435 10321121 := bstep (se 2 (by rfl) ⟨3870420, by rfl⟩ : syracuseStep 10321121 = 7740841) B7740841
theorem B6880747 : Blo 2147435 6880747 := bstep (se 1 (by rfl) ⟨5160560, by rfl⟩ : syracuseStep 6880747 = 10321121) B10321121
theorem B9174329 : Blo 2147435 9174329 := bstep (se 2 (by rfl) ⟨3440373, by rfl⟩ : syracuseStep 9174329 = 6880747) B6880747
theorem B6116219 : Blo 2147435 6116219 := bstep (se 1 (by rfl) ⟨4587164, by rfl⟩ : syracuseStep 6116219 = 9174329) B9174329
theorem B4077479 : Blo 2147435 4077479 := bstep (se 1 (by rfl) ⟨3058109, by rfl⟩ : syracuseStep 4077479 = 6116219) B6116219
theorem B10873277 : Blo 2147435 10873277 := bstep (se 3 (by rfl) ⟨2038739, by rfl⟩ : syracuseStep 10873277 = 4077479) B4077479
theorem B7248851 : Blo 2147435 7248851 := bstep (se 1 (by rfl) ⟨5436638, by rfl⟩ : syracuseStep 7248851 = 10873277) B10873277
theorem B4832567 : Blo 2147435 4832567 := bstep (se 1 (by rfl) ⟨3624425, by rfl⟩ : syracuseStep 4832567 = 7248851) B7248851
theorem B3221711 : Blo 2147435 3221711 := bstep (se 1 (by rfl) ⟨2416283, by rfl⟩ : syracuseStep 3221711 = 4832567) B4832567
theorem B2147807 : Blo 2147435 2147807 := bstep (se 1 (by rfl) ⟨1610855, by rfl⟩ : syracuseStep 2147807 = 3221711) B3221711
theorem B3221717 : Blo 2147435 3221717 := bbase (se 7 (by rfl) ⟨37754, by rfl⟩ : syracuseStep 3221717 = 75509) (by norm_num)
theorem B2147811 : Blo 2147435 2147811 := bstep (se 1 (by rfl) ⟨1610858, by rfl⟩ : syracuseStep 2147811 = 3221717) B3221717
theorem B5160581 : Blo 2147435 5160581 := bbase (se 4 (by rfl) ⟨483804, by rfl⟩ : syracuseStep 5160581 = 967609) (by norm_num)
theorem B3440387 : Blo 2147435 3440387 := bstep (se 1 (by rfl) ⟨2580290, by rfl⟩ : syracuseStep 3440387 = 5160581) B5160581
theorem B2293591 : Blo 2147435 2293591 := bstep (se 1 (by rfl) ⟨1720193, by rfl⟩ : syracuseStep 2293591 = 3440387) B3440387
theorem B3058121 : Blo 2147435 3058121 := bstep (se 2 (by rfl) ⟨1146795, by rfl⟩ : syracuseStep 3058121 = 2293591) B2293591
theorem B8154989 : Blo 2147435 8154989 := bstep (se 3 (by rfl) ⟨1529060, by rfl⟩ : syracuseStep 8154989 = 3058121) B3058121
theorem B5436659 : Blo 2147435 5436659 := bstep (se 1 (by rfl) ⟨4077494, by rfl⟩ : syracuseStep 5436659 = 8154989) B8154989
theorem B3624439 : Blo 2147435 3624439 := bstep (se 1 (by rfl) ⟨2718329, by rfl⟩ : syracuseStep 3624439 = 5436659) B5436659
theorem B4832585 : Blo 2147435 4832585 := bstep (se 2 (by rfl) ⟨1812219, by rfl⟩ : syracuseStep 4832585 = 3624439) B3624439
theorem B3221723 : Blo 2147435 3221723 := bstep (se 1 (by rfl) ⟨2416292, by rfl⟩ : syracuseStep 3221723 = 4832585) B4832585
theorem B2147815 : Blo 2147435 2147815 := bstep (se 1 (by rfl) ⟨1610861, by rfl⟩ : syracuseStep 2147815 = 3221723) B3221723
theorem B2416297 : Blo 2147435 2416297 := bbase (se 2 (by rfl) ⟨906111, by rfl⟩ : syracuseStep 2416297 = 1812223) (by norm_num)
theorem B3221729 : Blo 2147435 3221729 := bstep (se 2 (by rfl) ⟨1208148, by rfl⟩ : syracuseStep 3221729 = 2416297) B2416297
theorem B2147819 : Blo 2147435 2147819 := bstep (se 1 (by rfl) ⟨1610864, by rfl⟩ : syracuseStep 2147819 = 3221729) B3221729
theorem B11611349 : Blo 2147435 11611349 := bbase (se 7 (by rfl) ⟨136070, by rfl⟩ : syracuseStep 11611349 = 272141) (by norm_num)
theorem B7740899 : Blo 2147435 7740899 := bstep (se 1 (by rfl) ⟨5805674, by rfl⟩ : syracuseStep 7740899 = 11611349) B11611349
theorem B5160599 : Blo 2147435 5160599 := bstep (se 1 (by rfl) ⟨3870449, by rfl⟩ : syracuseStep 5160599 = 7740899) B7740899
theorem B3440399 : Blo 2147435 3440399 := bstep (se 1 (by rfl) ⟨2580299, by rfl⟩ : syracuseStep 3440399 = 5160599) B5160599
theorem B9174397 : Blo 2147435 9174397 := bstep (se 3 (by rfl) ⟨1720199, by rfl⟩ : syracuseStep 9174397 = 3440399) B3440399
theorem B12232529 : Blo 2147435 12232529 := bstep (se 2 (by rfl) ⟨4587198, by rfl⟩ : syracuseStep 12232529 = 9174397) B9174397
theorem B8155019 : Blo 2147435 8155019 := bstep (se 1 (by rfl) ⟨6116264, by rfl⟩ : syracuseStep 8155019 = 12232529) B12232529
theorem B5436679 : Blo 2147435 5436679 := bstep (se 1 (by rfl) ⟨4077509, by rfl⟩ : syracuseStep 5436679 = 8155019) B8155019
theorem B7248905 : Blo 2147435 7248905 := bstep (se 2 (by rfl) ⟨2718339, by rfl⟩ : syracuseStep 7248905 = 5436679) B5436679
theorem B4832603 : Blo 2147435 4832603 := bstep (se 1 (by rfl) ⟨3624452, by rfl⟩ : syracuseStep 4832603 = 7248905) B7248905
theorem B3221735 : Blo 2147435 3221735 := bstep (se 1 (by rfl) ⟨2416301, by rfl⟩ : syracuseStep 3221735 = 4832603) B4832603
theorem B2147823 : Blo 2147435 2147823 := bstep (se 1 (by rfl) ⟨1610867, by rfl⟩ : syracuseStep 2147823 = 3221735) B3221735
theorem B3221741 : Blo 2147435 3221741 := bbase (se 3 (by rfl) ⟨604076, by rfl⟩ : syracuseStep 3221741 = 1208153) (by norm_num)
theorem B2147827 : Blo 2147435 2147827 := bstep (se 1 (by rfl) ⟨1610870, by rfl⟩ : syracuseStep 2147827 = 3221741) B3221741
theorem B4832621 : Blo 2147435 4832621 := bbase (se 3 (by rfl) ⟨906116, by rfl⟩ : syracuseStep 4832621 = 1812233) (by norm_num)
theorem B3221747 : Blo 2147435 3221747 := bstep (se 1 (by rfl) ⟨2416310, by rfl⟩ : syracuseStep 3221747 = 4832621) B4832621
theorem B2147831 : Blo 2147435 2147831 := bstep (se 1 (by rfl) ⟨1610873, by rfl⟩ : syracuseStep 2147831 = 3221747) B3221747
theorem B4077533 : Blo 2147435 4077533 := bbase (se 3 (by rfl) ⟨764537, by rfl⟩ : syracuseStep 4077533 = 1529075) (by norm_num)
theorem B2718355 : Blo 2147435 2718355 := bstep (se 1 (by rfl) ⟨2038766, by rfl⟩ : syracuseStep 2718355 = 4077533) B4077533
theorem B3624473 : Blo 2147435 3624473 := bstep (se 2 (by rfl) ⟨1359177, by rfl⟩ : syracuseStep 3624473 = 2718355) B2718355
theorem B2416315 : Blo 2147435 2416315 := bstep (se 1 (by rfl) ⟨1812236, by rfl⟩ : syracuseStep 2416315 = 3624473) B3624473
theorem B3221753 : Blo 2147435 3221753 := bstep (se 2 (by rfl) ⟨1208157, by rfl⟩ : syracuseStep 3221753 = 2416315) B2416315
theorem B2147835 : Blo 2147435 2147835 := bstep (se 1 (by rfl) ⟨1610876, by rfl⟩ : syracuseStep 2147835 = 3221753) B3221753
theorem B6370085 : Blo 2147435 6370085 := bbase (se 4 (by rfl) ⟨597195, by rfl⟩ : syracuseStep 6370085 = 1194391) (by norm_num)
theorem B4246723 : Blo 2147435 4246723 := bstep (se 1 (by rfl) ⟨3185042, by rfl⟩ : syracuseStep 4246723 = 6370085) B6370085
theorem B5662297 : Blo 2147435 5662297 := bstep (se 2 (by rfl) ⟨2123361, by rfl⟩ : syracuseStep 5662297 = 4246723) B4246723
theorem B7549729 : Blo 2147435 7549729 := bstep (se 2 (by rfl) ⟨2831148, by rfl⟩ : syracuseStep 7549729 = 5662297) B5662297
theorem B161060885 : Blo 2147435 161060885 := bstep (se 6 (by rfl) ⟨3774864, by rfl⟩ : syracuseStep 161060885 = 7549729) B7549729
theorem B107373923 : Blo 2147435 107373923 := bstep (se 1 (by rfl) ⟨80530442, by rfl⟩ : syracuseStep 107373923 = 161060885) B161060885
theorem B71582615 : Blo 2147435 71582615 := bstep (se 1 (by rfl) ⟨53686961, by rfl⟩ : syracuseStep 71582615 = 107373923) B107373923
theorem B47721743 : Blo 2147435 47721743 := bstep (se 1 (by rfl) ⟨35791307, by rfl⟩ : syracuseStep 47721743 = 71582615) B71582615
theorem B31814495 : Blo 2147435 31814495 := bstep (se 1 (by rfl) ⟨23860871, by rfl⟩ : syracuseStep 31814495 = 47721743) B47721743
theorem B21209663 : Blo 2147435 21209663 := bstep (se 1 (by rfl) ⟨15907247, by rfl⟩ : syracuseStep 21209663 = 31814495) B31814495
theorem B14139775 : Blo 2147435 14139775 := bstep (se 1 (by rfl) ⟨10604831, by rfl⟩ : syracuseStep 14139775 = 21209663) B21209663
theorem B75412133 : Blo 2147435 75412133 := bstep (se 4 (by rfl) ⟨7069887, by rfl⟩ : syracuseStep 75412133 = 14139775) B14139775
theorem B50274755 : Blo 2147435 50274755 := bstep (se 1 (by rfl) ⟨37706066, by rfl⟩ : syracuseStep 50274755 = 75412133) B75412133
theorem B33516503 : Blo 2147435 33516503 := bstep (se 1 (by rfl) ⟨25137377, by rfl⟩ : syracuseStep 33516503 = 50274755) B50274755
theorem B22344335 : Blo 2147435 22344335 := bstep (se 1 (by rfl) ⟨16758251, by rfl⟩ : syracuseStep 22344335 = 33516503) B33516503
theorem B14896223 : Blo 2147435 14896223 := bstep (se 1 (by rfl) ⟨11172167, by rfl⟩ : syracuseStep 14896223 = 22344335) B22344335
theorem B9930815 : Blo 2147435 9930815 := bstep (se 1 (by rfl) ⟨7448111, by rfl⟩ : syracuseStep 9930815 = 14896223) B14896223
theorem B6620543 : Blo 2147435 6620543 := bstep (se 1 (by rfl) ⟨4965407, by rfl⟩ : syracuseStep 6620543 = 9930815) B9930815
theorem B4413695 : Blo 2147435 4413695 := bstep (se 1 (by rfl) ⟨3310271, by rfl⟩ : syracuseStep 4413695 = 6620543) B6620543
theorem B47079413 : Blo 2147435 47079413 := bstep (se 5 (by rfl) ⟨2206847, by rfl⟩ : syracuseStep 47079413 = 4413695) B4413695
theorem B31386275 : Blo 2147435 31386275 := bstep (se 1 (by rfl) ⟨23539706, by rfl⟩ : syracuseStep 31386275 = 47079413) B47079413
theorem B20924183 : Blo 2147435 20924183 := bstep (se 1 (by rfl) ⟨15693137, by rfl⟩ : syracuseStep 20924183 = 31386275) B31386275
theorem B55797821 : Blo 2147435 55797821 := bstep (se 3 (by rfl) ⟨10462091, by rfl⟩ : syracuseStep 55797821 = 20924183) B20924183
theorem B37198547 : Blo 2147435 37198547 := bstep (se 1 (by rfl) ⟨27898910, by rfl⟩ : syracuseStep 37198547 = 55797821) B55797821
theorem B24799031 : Blo 2147435 24799031 := bstep (se 1 (by rfl) ⟨18599273, by rfl⟩ : syracuseStep 24799031 = 37198547) B37198547
theorem B16532687 : Blo 2147435 16532687 := bstep (se 1 (by rfl) ⟨12399515, by rfl⟩ : syracuseStep 16532687 = 24799031) B24799031
theorem B44087165 : Blo 2147435 44087165 := bstep (se 3 (by rfl) ⟨8266343, by rfl⟩ : syracuseStep 44087165 = 16532687) B16532687
theorem B29391443 : Blo 2147435 29391443 := bstep (se 1 (by rfl) ⟨22043582, by rfl⟩ : syracuseStep 29391443 = 44087165) B44087165
theorem B19594295 : Blo 2147435 19594295 := bstep (se 1 (by rfl) ⟨14695721, by rfl⟩ : syracuseStep 19594295 = 29391443) B29391443
theorem B13062863 : Blo 2147435 13062863 := bstep (se 1 (by rfl) ⟨9797147, by rfl⟩ : syracuseStep 13062863 = 19594295) B19594295
theorem B8708575 : Blo 2147435 8708575 := bstep (se 1 (by rfl) ⟨6531431, by rfl⟩ : syracuseStep 8708575 = 13062863) B13062863
theorem B11611433 : Blo 2147435 11611433 := bstep (se 2 (by rfl) ⟨4354287, by rfl⟩ : syracuseStep 11611433 = 8708575) B8708575
theorem B7740955 : Blo 2147435 7740955 := bstep (se 1 (by rfl) ⟨5805716, by rfl⟩ : syracuseStep 7740955 = 11611433) B11611433
theorem B10321273 : Blo 2147435 10321273 := bstep (se 2 (by rfl) ⟨3870477, by rfl⟩ : syracuseStep 10321273 = 7740955) B7740955
theorem B55046789 : Blo 2147435 55046789 := bstep (se 4 (by rfl) ⟨5160636, by rfl⟩ : syracuseStep 55046789 = 10321273) B10321273
theorem B36697859 : Blo 2147435 36697859 := bstep (se 1 (by rfl) ⟨27523394, by rfl⟩ : syracuseStep 36697859 = 55046789) B55046789
theorem B24465239 : Blo 2147435 24465239 := bstep (se 1 (by rfl) ⟨18348929, by rfl⟩ : syracuseStep 24465239 = 36697859) B36697859
theorem B16310159 : Blo 2147435 16310159 := bstep (se 1 (by rfl) ⟨12232619, by rfl⟩ : syracuseStep 16310159 = 24465239) B24465239
theorem B10873439 : Blo 2147435 10873439 := bstep (se 1 (by rfl) ⟨8155079, by rfl⟩ : syracuseStep 10873439 = 16310159) B16310159
theorem B7248959 : Blo 2147435 7248959 := bstep (se 1 (by rfl) ⟨5436719, by rfl⟩ : syracuseStep 7248959 = 10873439) B10873439
theorem B4832639 : Blo 2147435 4832639 := bstep (se 1 (by rfl) ⟨3624479, by rfl⟩ : syracuseStep 4832639 = 7248959) B7248959
theorem B3221759 : Blo 2147435 3221759 := bstep (se 1 (by rfl) ⟨2416319, by rfl⟩ : syracuseStep 3221759 = 4832639) B4832639
theorem B2147839 : Blo 2147435 2147839 := bstep (se 1 (by rfl) ⟨1610879, by rfl⟩ : syracuseStep 2147839 = 3221759) B3221759
theorem B3221765 : Blo 2147435 3221765 := bbase (se 4 (by rfl) ⟨302040, by rfl⟩ : syracuseStep 3221765 = 604081) (by norm_num)
theorem B2147843 : Blo 2147435 2147843 := bstep (se 1 (by rfl) ⟨1610882, by rfl⟩ : syracuseStep 2147843 = 3221765) B3221765
theorem B3624493 : Blo 2147435 3624493 := bbase (se 3 (by rfl) ⟨679592, by rfl⟩ : syracuseStep 3624493 = 1359185) (by norm_num)
theorem B4832657 : Blo 2147435 4832657 := bstep (se 2 (by rfl) ⟨1812246, by rfl⟩ : syracuseStep 4832657 = 3624493) B3624493
theorem B3221771 : Blo 2147435 3221771 := bstep (se 1 (by rfl) ⟨2416328, by rfl⟩ : syracuseStep 3221771 = 4832657) B4832657
theorem B2147847 : Blo 2147435 2147847 := bstep (se 1 (by rfl) ⟨1610885, by rfl⟩ : syracuseStep 2147847 = 3221771) B3221771
theorem B2416333 : Blo 2147435 2416333 := bbase (se 3 (by rfl) ⟨453062, by rfl⟩ : syracuseStep 2416333 = 906125) (by norm_num)
theorem B3221777 : Blo 2147435 3221777 := bstep (se 2 (by rfl) ⟨1208166, by rfl⟩ : syracuseStep 3221777 = 2416333) B2416333
theorem B2147851 : Blo 2147435 2147851 := bstep (se 1 (by rfl) ⟨1610888, by rfl⟩ : syracuseStep 2147851 = 3221777) B3221777
theorem B7249013 : Blo 2147435 7249013 := bbase (se 5 (by rfl) ⟨339797, by rfl⟩ : syracuseStep 7249013 = 679595) (by norm_num)
theorem B4832675 : Blo 2147435 4832675 := bstep (se 1 (by rfl) ⟨3624506, by rfl⟩ : syracuseStep 4832675 = 7249013) B7249013
theorem B3221783 : Blo 2147435 3221783 := bstep (se 1 (by rfl) ⟨2416337, by rfl⟩ : syracuseStep 3221783 = 4832675) B4832675
theorem B2147855 : Blo 2147435 2147855 := bstep (se 1 (by rfl) ⟨1610891, by rfl⟩ : syracuseStep 2147855 = 3221783) B3221783
theorem B3221789 : Blo 2147435 3221789 := bbase (se 3 (by rfl) ⟨604085, by rfl⟩ : syracuseStep 3221789 = 1208171) (by norm_num)
theorem B2147859 : Blo 2147435 2147859 := bstep (se 1 (by rfl) ⟨1610894, by rfl⟩ : syracuseStep 2147859 = 3221789) B3221789
theorem B4832693 : Blo 2147435 4832693 := bbase (se 5 (by rfl) ⟨226532, by rfl⟩ : syracuseStep 4832693 = 453065) (by norm_num)
theorem B3221795 : Blo 2147435 3221795 := bstep (se 1 (by rfl) ⟨2416346, by rfl⟩ : syracuseStep 3221795 = 4832693) B4832693
theorem B2147863 : Blo 2147435 2147863 := bstep (se 1 (by rfl) ⟨1610897, by rfl⟩ : syracuseStep 2147863 = 3221795) B3221795
theorem B4587293 : Blo 2147435 4587293 := bbase (se 3 (by rfl) ⟨860117, by rfl⟩ : syracuseStep 4587293 = 1720235) (by norm_num)
theorem B12232781 : Blo 2147435 12232781 := bstep (se 3 (by rfl) ⟨2293646, by rfl⟩ : syracuseStep 12232781 = 4587293) B4587293
theorem B8155187 : Blo 2147435 8155187 := bstep (se 1 (by rfl) ⟨6116390, by rfl⟩ : syracuseStep 8155187 = 12232781) B12232781
theorem B5436791 : Blo 2147435 5436791 := bstep (se 1 (by rfl) ⟨4077593, by rfl⟩ : syracuseStep 5436791 = 8155187) B8155187
theorem B3624527 : Blo 2147435 3624527 := bstep (se 1 (by rfl) ⟨2718395, by rfl⟩ : syracuseStep 3624527 = 5436791) B5436791
theorem B2416351 : Blo 2147435 2416351 := bstep (se 1 (by rfl) ⟨1812263, by rfl⟩ : syracuseStep 2416351 = 3624527) B3624527
theorem B3221801 : Blo 2147435 3221801 := bstep (se 2 (by rfl) ⟨1208175, by rfl⟩ : syracuseStep 3221801 = 2416351) B2416351
theorem B2147867 : Blo 2147435 2147867 := bstep (se 1 (by rfl) ⟨1610900, by rfl⟩ : syracuseStep 2147867 = 3221801) B3221801
theorem B4587301 : Blo 2147435 4587301 := bbase (se 4 (by rfl) ⟨430059, by rfl⟩ : syracuseStep 4587301 = 860119) (by norm_num)
theorem B6116401 : Blo 2147435 6116401 := bstep (se 2 (by rfl) ⟨2293650, by rfl⟩ : syracuseStep 6116401 = 4587301) B4587301
theorem B8155201 : Blo 2147435 8155201 := bstep (se 2 (by rfl) ⟨3058200, by rfl⟩ : syracuseStep 8155201 = 6116401) B6116401
theorem B10873601 : Blo 2147435 10873601 := bstep (se 2 (by rfl) ⟨4077600, by rfl⟩ : syracuseStep 10873601 = 8155201) B8155201
theorem B7249067 : Blo 2147435 7249067 := bstep (se 1 (by rfl) ⟨5436800, by rfl⟩ : syracuseStep 7249067 = 10873601) B10873601
theorem B4832711 : Blo 2147435 4832711 := bstep (se 1 (by rfl) ⟨3624533, by rfl⟩ : syracuseStep 4832711 = 7249067) B7249067
theorem B3221807 : Blo 2147435 3221807 := bstep (se 1 (by rfl) ⟨2416355, by rfl⟩ : syracuseStep 3221807 = 4832711) B4832711
theorem B2147871 : Blo 2147435 2147871 := bstep (se 1 (by rfl) ⟨1610903, by rfl⟩ : syracuseStep 2147871 = 3221807) B3221807
theorem B3221813 : Blo 2147435 3221813 := bbase (se 5 (by rfl) ⟨151022, by rfl⟩ : syracuseStep 3221813 = 302045) (by norm_num)
theorem B2147875 : Blo 2147435 2147875 := bstep (se 1 (by rfl) ⟨1610906, by rfl⟩ : syracuseStep 2147875 = 3221813) B3221813
theorem B5436821 : Blo 2147435 5436821 := bbase (se 6 (by rfl) ⟨127425, by rfl⟩ : syracuseStep 5436821 = 254851) (by norm_num)
theorem B3624547 : Blo 2147435 3624547 := bstep (se 1 (by rfl) ⟨2718410, by rfl⟩ : syracuseStep 3624547 = 5436821) B5436821
theorem B4832729 : Blo 2147435 4832729 := bstep (se 2 (by rfl) ⟨1812273, by rfl⟩ : syracuseStep 4832729 = 3624547) B3624547
theorem B3221819 : Blo 2147435 3221819 := bstep (se 1 (by rfl) ⟨2416364, by rfl⟩ : syracuseStep 3221819 = 4832729) B4832729
theorem B2147879 : Blo 2147435 2147879 := bstep (se 1 (by rfl) ⟨1610909, by rfl⟩ : syracuseStep 2147879 = 3221819) B3221819
theorem B2416369 : Blo 2147435 2416369 := bbase (se 2 (by rfl) ⟨906138, by rfl⟩ : syracuseStep 2416369 = 1812277) (by norm_num)
theorem B3221825 : Blo 2147435 3221825 := bstep (se 2 (by rfl) ⟨1208184, by rfl⟩ : syracuseStep 3221825 = 2416369) B2416369
theorem B2147883 : Blo 2147435 2147883 := bstep (se 1 (by rfl) ⟨1610912, by rfl⟩ : syracuseStep 2147883 = 3221825) B3221825
theorem B13063157 : Blo 2147435 13063157 := bbase (se 5 (by rfl) ⟨612335, by rfl⟩ : syracuseStep 13063157 = 1224671) (by norm_num)
theorem B8708771 : Blo 2147435 8708771 := bstep (se 1 (by rfl) ⟨6531578, by rfl⟩ : syracuseStep 8708771 = 13063157) B13063157
theorem B5805847 : Blo 2147435 5805847 := bstep (se 1 (by rfl) ⟨4354385, by rfl⟩ : syracuseStep 5805847 = 8708771) B8708771
theorem B30964517 : Blo 2147435 30964517 := bstep (se 4 (by rfl) ⟨2902923, by rfl⟩ : syracuseStep 30964517 = 5805847) B5805847
theorem B20643011 : Blo 2147435 20643011 := bstep (se 1 (by rfl) ⟨15482258, by rfl⟩ : syracuseStep 20643011 = 30964517) B30964517
theorem B13762007 : Blo 2147435 13762007 := bstep (se 1 (by rfl) ⟨10321505, by rfl⟩ : syracuseStep 13762007 = 20643011) B20643011
theorem B9174671 : Blo 2147435 9174671 := bstep (se 1 (by rfl) ⟨6881003, by rfl⟩ : syracuseStep 9174671 = 13762007) B13762007
theorem B6116447 : Blo 2147435 6116447 := bstep (se 1 (by rfl) ⟨4587335, by rfl⟩ : syracuseStep 6116447 = 9174671) B9174671
theorem B4077631 : Blo 2147435 4077631 := bstep (se 1 (by rfl) ⟨3058223, by rfl⟩ : syracuseStep 4077631 = 6116447) B6116447
theorem B5436841 : Blo 2147435 5436841 := bstep (se 2 (by rfl) ⟨2038815, by rfl⟩ : syracuseStep 5436841 = 4077631) B4077631
theorem B7249121 : Blo 2147435 7249121 := bstep (se 2 (by rfl) ⟨2718420, by rfl⟩ : syracuseStep 7249121 = 5436841) B5436841
theorem B4832747 : Blo 2147435 4832747 := bstep (se 1 (by rfl) ⟨3624560, by rfl⟩ : syracuseStep 4832747 = 7249121) B7249121
theorem B3221831 : Blo 2147435 3221831 := bstep (se 1 (by rfl) ⟨2416373, by rfl⟩ : syracuseStep 3221831 = 4832747) B4832747
theorem B2147887 : Blo 2147435 2147887 := bstep (se 1 (by rfl) ⟨1610915, by rfl⟩ : syracuseStep 2147887 = 3221831) B3221831
theorem B3221837 : Blo 2147435 3221837 := bbase (se 3 (by rfl) ⟨604094, by rfl⟩ : syracuseStep 3221837 = 1208189) (by norm_num)
theorem B2147891 : Blo 2147435 2147891 := bstep (se 1 (by rfl) ⟨1610918, by rfl⟩ : syracuseStep 2147891 = 3221837) B3221837
theorem B4832765 : Blo 2147435 4832765 := bbase (se 3 (by rfl) ⟨906143, by rfl⟩ : syracuseStep 4832765 = 1812287) (by norm_num)
theorem B3221843 : Blo 2147435 3221843 := bstep (se 1 (by rfl) ⟨2416382, by rfl⟩ : syracuseStep 3221843 = 4832765) B4832765
theorem B2147895 : Blo 2147435 2147895 := bstep (se 1 (by rfl) ⟨1610921, by rfl⟩ : syracuseStep 2147895 = 3221843) B3221843
theorem B3624581 : Blo 2147435 3624581 := bbase (se 4 (by rfl) ⟨339804, by rfl⟩ : syracuseStep 3624581 = 679609) (by norm_num)
theorem B2416387 : Blo 2147435 2416387 := bstep (se 1 (by rfl) ⟨1812290, by rfl⟩ : syracuseStep 2416387 = 3624581) B3624581
theorem B3221849 : Blo 2147435 3221849 := bstep (se 2 (by rfl) ⟨1208193, by rfl⟩ : syracuseStep 3221849 = 2416387) B2416387
theorem B2147899 : Blo 2147435 2147899 := bstep (se 1 (by rfl) ⟨1610924, by rfl⟩ : syracuseStep 2147899 = 3221849) B3221849
theorem B16310645 : Blo 2147435 16310645 := bbase (se 5 (by rfl) ⟨764561, by rfl⟩ : syracuseStep 16310645 = 1529123) (by norm_num)
theorem B10873763 : Blo 2147435 10873763 := bstep (se 1 (by rfl) ⟨8155322, by rfl⟩ : syracuseStep 10873763 = 16310645) B16310645
theorem B7249175 : Blo 2147435 7249175 := bstep (se 1 (by rfl) ⟨5436881, by rfl⟩ : syracuseStep 7249175 = 10873763) B10873763
theorem B4832783 : Blo 2147435 4832783 := bstep (se 1 (by rfl) ⟨3624587, by rfl⟩ : syracuseStep 4832783 = 7249175) B7249175
theorem B3221855 : Blo 2147435 3221855 := bstep (se 1 (by rfl) ⟨2416391, by rfl⟩ : syracuseStep 3221855 = 4832783) B4832783
theorem B2147903 : Blo 2147435 2147903 := bstep (se 1 (by rfl) ⟨1610927, by rfl⟩ : syracuseStep 2147903 = 3221855) B3221855
theorem B3221861 : Blo 2147435 3221861 := bbase (se 4 (by rfl) ⟨302049, by rfl⟩ : syracuseStep 3221861 = 604099) (by norm_num)
theorem B2147907 : Blo 2147435 2147907 := bstep (se 1 (by rfl) ⟨1610930, by rfl⟩ : syracuseStep 2147907 = 3221861) B3221861
theorem B4077677 : Blo 2147435 4077677 := bbase (se 3 (by rfl) ⟨764564, by rfl⟩ : syracuseStep 4077677 = 1529129) (by norm_num)
theorem B2718451 : Blo 2147435 2718451 := bstep (se 1 (by rfl) ⟨2038838, by rfl⟩ : syracuseStep 2718451 = 4077677) B4077677
theorem B3624601 : Blo 2147435 3624601 := bstep (se 2 (by rfl) ⟨1359225, by rfl⟩ : syracuseStep 3624601 = 2718451) B2718451
theorem B4832801 : Blo 2147435 4832801 := bstep (se 2 (by rfl) ⟨1812300, by rfl⟩ : syracuseStep 4832801 = 3624601) B3624601
theorem B3221867 : Blo 2147435 3221867 := bstep (se 1 (by rfl) ⟨2416400, by rfl⟩ : syracuseStep 3221867 = 4832801) B4832801
theorem B2147911 : Blo 2147435 2147911 := bstep (se 1 (by rfl) ⟨1610933, by rfl⟩ : syracuseStep 2147911 = 3221867) B3221867
theorem B2416405 : Blo 2147435 2416405 := bbase (se 6 (by rfl) ⟨56634, by rfl⟩ : syracuseStep 2416405 = 113269) (by norm_num)
theorem B3221873 : Blo 2147435 3221873 := bstep (se 2 (by rfl) ⟨1208202, by rfl⟩ : syracuseStep 3221873 = 2416405) B2416405
theorem B2147915 : Blo 2147435 2147915 := bstep (se 1 (by rfl) ⟨1610936, by rfl⟩ : syracuseStep 2147915 = 3221873) B3221873
theorem B2718461 : Blo 2147435 2718461 := bbase (se 3 (by rfl) ⟨509711, by rfl⟩ : syracuseStep 2718461 = 1019423) (by norm_num)
theorem B7249229 : Blo 2147435 7249229 := bstep (se 3 (by rfl) ⟨1359230, by rfl⟩ : syracuseStep 7249229 = 2718461) B2718461
theorem B4832819 : Blo 2147435 4832819 := bstep (se 1 (by rfl) ⟨3624614, by rfl⟩ : syracuseStep 4832819 = 7249229) B7249229
theorem B3221879 : Blo 2147435 3221879 := bstep (se 1 (by rfl) ⟨2416409, by rfl⟩ : syracuseStep 3221879 = 4832819) B4832819
theorem B2147919 : Blo 2147435 2147919 := bstep (se 1 (by rfl) ⟨1610939, by rfl⟩ : syracuseStep 2147919 = 3221879) B3221879
theorem B3221885 : Blo 2147435 3221885 := bbase (se 3 (by rfl) ⟨604103, by rfl⟩ : syracuseStep 3221885 = 1208207) (by norm_num)
theorem B2147923 : Blo 2147435 2147923 := bstep (se 1 (by rfl) ⟨1610942, by rfl⟩ : syracuseStep 2147923 = 3221885) B3221885
theorem B4832837 : Blo 2147435 4832837 := bbase (se 4 (by rfl) ⟨453078, by rfl⟩ : syracuseStep 4832837 = 906157) (by norm_num)
theorem B3221891 : Blo 2147435 3221891 := bstep (se 1 (by rfl) ⟨2416418, by rfl⟩ : syracuseStep 3221891 = 4832837) B4832837
theorem B2147927 : Blo 2147435 2147927 := bstep (se 1 (by rfl) ⟨1610945, by rfl⟩ : syracuseStep 2147927 = 3221891) B3221891
theorem B3440573 : Blo 2147435 3440573 := bbase (se 3 (by rfl) ⟨645107, by rfl⟩ : syracuseStep 3440573 = 1290215) (by norm_num)
theorem B2293715 : Blo 2147435 2293715 := bstep (se 1 (by rfl) ⟨1720286, by rfl⟩ : syracuseStep 2293715 = 3440573) B3440573
theorem B6116573 : Blo 2147435 6116573 := bstep (se 3 (by rfl) ⟨1146857, by rfl⟩ : syracuseStep 6116573 = 2293715) B2293715
theorem B4077715 : Blo 2147435 4077715 := bstep (se 1 (by rfl) ⟨3058286, by rfl⟩ : syracuseStep 4077715 = 6116573) B6116573
theorem B5436953 : Blo 2147435 5436953 := bstep (se 2 (by rfl) ⟨2038857, by rfl⟩ : syracuseStep 5436953 = 4077715) B4077715
theorem B3624635 : Blo 2147435 3624635 := bstep (se 1 (by rfl) ⟨2718476, by rfl⟩ : syracuseStep 3624635 = 5436953) B5436953
theorem B2416423 : Blo 2147435 2416423 := bstep (se 1 (by rfl) ⟨1812317, by rfl⟩ : syracuseStep 2416423 = 3624635) B3624635
theorem B3221897 : Blo 2147435 3221897 := bstep (se 2 (by rfl) ⟨1208211, by rfl⟩ : syracuseStep 3221897 = 2416423) B2416423
theorem B2147931 : Blo 2147435 2147931 := bstep (se 1 (by rfl) ⟨1610948, by rfl⟩ : syracuseStep 2147931 = 3221897) B3221897
theorem B10873925 : Blo 2147435 10873925 := bbase (se 4 (by rfl) ⟨1019430, by rfl⟩ : syracuseStep 10873925 = 2038861) (by norm_num)
theorem B7249283 : Blo 2147435 7249283 := bstep (se 1 (by rfl) ⟨5436962, by rfl⟩ : syracuseStep 7249283 = 10873925) B10873925
theorem B4832855 : Blo 2147435 4832855 := bstep (se 1 (by rfl) ⟨3624641, by rfl⟩ : syracuseStep 4832855 = 7249283) B7249283
theorem B3221903 : Blo 2147435 3221903 := bstep (se 1 (by rfl) ⟨2416427, by rfl⟩ : syracuseStep 3221903 = 4832855) B4832855
theorem B2147935 : Blo 2147435 2147935 := bstep (se 1 (by rfl) ⟨1610951, by rfl⟩ : syracuseStep 2147935 = 3221903) B3221903
theorem B3221909 : Blo 2147435 3221909 := bbase (se 6 (by rfl) ⟨75513, by rfl⟩ : syracuseStep 3221909 = 151027) (by norm_num)
theorem B2147939 : Blo 2147435 2147939 := bstep (se 1 (by rfl) ⟨1610954, by rfl⟩ : syracuseStep 2147939 = 3221909) B3221909
theorem B3724237 : Blo 2147435 3724237 := bbase (se 3 (by rfl) ⟨698294, by rfl⟩ : syracuseStep 3724237 = 1396589) (by norm_num)
theorem B19862597 : Blo 2147435 19862597 := bstep (se 4 (by rfl) ⟨1862118, by rfl⟩ : syracuseStep 19862597 = 3724237) B3724237
theorem B13241731 : Blo 2147435 13241731 := bstep (se 1 (by rfl) ⟨9931298, by rfl⟩ : syracuseStep 13241731 = 19862597) B19862597
theorem B17655641 : Blo 2147435 17655641 := bstep (se 2 (by rfl) ⟨6620865, by rfl⟩ : syracuseStep 17655641 = 13241731) B13241731
theorem B11770427 : Blo 2147435 11770427 := bstep (se 1 (by rfl) ⟨8827820, by rfl⟩ : syracuseStep 11770427 = 17655641) B17655641
theorem B7846951 : Blo 2147435 7846951 := bstep (se 1 (by rfl) ⟨5885213, by rfl⟩ : syracuseStep 7846951 = 11770427) B11770427
theorem B10462601 : Blo 2147435 10462601 := bstep (se 2 (by rfl) ⟨3923475, by rfl⟩ : syracuseStep 10462601 = 7846951) B7846951
theorem B6975067 : Blo 2147435 6975067 := bstep (se 1 (by rfl) ⟨5231300, by rfl⟩ : syracuseStep 6975067 = 10462601) B10462601
theorem B9300089 : Blo 2147435 9300089 := bstep (se 2 (by rfl) ⟨3487533, by rfl⟩ : syracuseStep 9300089 = 6975067) B6975067
theorem B6200059 : Blo 2147435 6200059 := bstep (se 1 (by rfl) ⟨4650044, by rfl⟩ : syracuseStep 6200059 = 9300089) B9300089
theorem B8266745 : Blo 2147435 8266745 := bstep (se 2 (by rfl) ⟨3100029, by rfl⟩ : syracuseStep 8266745 = 6200059) B6200059
theorem B22044653 : Blo 2147435 22044653 := bstep (se 3 (by rfl) ⟨4133372, by rfl⟩ : syracuseStep 22044653 = 8266745) B8266745
theorem B14696435 : Blo 2147435 14696435 := bstep (se 1 (by rfl) ⟨11022326, by rfl⟩ : syracuseStep 14696435 = 22044653) B22044653
theorem B39190493 : Blo 2147435 39190493 := bstep (se 3 (by rfl) ⟨7348217, by rfl⟩ : syracuseStep 39190493 = 14696435) B14696435
theorem B26126995 : Blo 2147435 26126995 := bstep (se 1 (by rfl) ⟨19595246, by rfl⟩ : syracuseStep 26126995 = 39190493) B39190493
theorem B34835993 : Blo 2147435 34835993 := bstep (se 2 (by rfl) ⟨13063497, by rfl⟩ : syracuseStep 34835993 = 26126995) B26126995
theorem B23223995 : Blo 2147435 23223995 := bstep (se 1 (by rfl) ⟨17417996, by rfl⟩ : syracuseStep 23223995 = 34835993) B34835993
theorem B15482663 : Blo 2147435 15482663 := bstep (se 1 (by rfl) ⟨11611997, by rfl⟩ : syracuseStep 15482663 = 23223995) B23223995
theorem B10321775 : Blo 2147435 10321775 := bstep (se 1 (by rfl) ⟨7741331, by rfl⟩ : syracuseStep 10321775 = 15482663) B15482663
theorem B6881183 : Blo 2147435 6881183 := bstep (se 1 (by rfl) ⟨5160887, by rfl⟩ : syracuseStep 6881183 = 10321775) B10321775
theorem B4587455 : Blo 2147435 4587455 := bstep (se 1 (by rfl) ⟨3440591, by rfl⟩ : syracuseStep 4587455 = 6881183) B6881183
theorem B12233213 : Blo 2147435 12233213 := bstep (se 3 (by rfl) ⟨2293727, by rfl⟩ : syracuseStep 12233213 = 4587455) B4587455
theorem B8155475 : Blo 2147435 8155475 := bstep (se 1 (by rfl) ⟨6116606, by rfl⟩ : syracuseStep 8155475 = 12233213) B12233213
theorem B5436983 : Blo 2147435 5436983 := bstep (se 1 (by rfl) ⟨4077737, by rfl⟩ : syracuseStep 5436983 = 8155475) B8155475
theorem B3624655 : Blo 2147435 3624655 := bstep (se 1 (by rfl) ⟨2718491, by rfl⟩ : syracuseStep 3624655 = 5436983) B5436983
theorem B4832873 : Blo 2147435 4832873 := bstep (se 2 (by rfl) ⟨1812327, by rfl⟩ : syracuseStep 4832873 = 3624655) B3624655
theorem B3221915 : Blo 2147435 3221915 := bstep (se 1 (by rfl) ⟨2416436, by rfl⟩ : syracuseStep 3221915 = 4832873) B4832873
theorem B2147943 : Blo 2147435 2147943 := bstep (se 1 (by rfl) ⟨1610957, by rfl⟩ : syracuseStep 2147943 = 3221915) B3221915
theorem B2416441 : Blo 2147435 2416441 := bbase (se 2 (by rfl) ⟨906165, by rfl⟩ : syracuseStep 2416441 = 1812331) (by norm_num)
theorem B3221921 : Blo 2147435 3221921 := bstep (se 2 (by rfl) ⟨1208220, by rfl⟩ : syracuseStep 3221921 = 2416441) B2416441
theorem B2147947 : Blo 2147435 2147947 := bstep (se 1 (by rfl) ⟨1610960, by rfl⟩ : syracuseStep 2147947 = 3221921) B3221921
theorem B6116629 : Blo 2147435 6116629 := bbase (se 6 (by rfl) ⟨143358, by rfl⟩ : syracuseStep 6116629 = 286717) (by norm_num)
theorem B8155505 : Blo 2147435 8155505 := bstep (se 2 (by rfl) ⟨3058314, by rfl⟩ : syracuseStep 8155505 = 6116629) B6116629
theorem B5437003 : Blo 2147435 5437003 := bstep (se 1 (by rfl) ⟨4077752, by rfl⟩ : syracuseStep 5437003 = 8155505) B8155505
theorem B7249337 : Blo 2147435 7249337 := bstep (se 2 (by rfl) ⟨2718501, by rfl⟩ : syracuseStep 7249337 = 5437003) B5437003
theorem B4832891 : Blo 2147435 4832891 := bstep (se 1 (by rfl) ⟨3624668, by rfl⟩ : syracuseStep 4832891 = 7249337) B7249337
theorem B3221927 : Blo 2147435 3221927 := bstep (se 1 (by rfl) ⟨2416445, by rfl⟩ : syracuseStep 3221927 = 4832891) B4832891
theorem B2147951 : Blo 2147435 2147951 := bstep (se 1 (by rfl) ⟨1610963, by rfl⟩ : syracuseStep 2147951 = 3221927) B3221927
theorem B3221933 : Blo 2147435 3221933 := bbase (se 3 (by rfl) ⟨604112, by rfl⟩ : syracuseStep 3221933 = 1208225) (by norm_num)
theorem B2147955 : Blo 2147435 2147955 := bstep (se 1 (by rfl) ⟨1610966, by rfl⟩ : syracuseStep 2147955 = 3221933) B3221933
theorem B4832909 : Blo 2147435 4832909 := bbase (se 3 (by rfl) ⟨906170, by rfl⟩ : syracuseStep 4832909 = 1812341) (by norm_num)
theorem B3221939 : Blo 2147435 3221939 := bstep (se 1 (by rfl) ⟨2416454, by rfl⟩ : syracuseStep 3221939 = 4832909) B4832909
theorem B2147959 : Blo 2147435 2147959 := bstep (se 1 (by rfl) ⟨1610969, by rfl⟩ : syracuseStep 2147959 = 3221939) B3221939
theorem B2718517 : Blo 2147435 2718517 := bbase (se 5 (by rfl) ⟨127430, by rfl⟩ : syracuseStep 2718517 = 254861) (by norm_num)
theorem B3624689 : Blo 2147435 3624689 := bstep (se 2 (by rfl) ⟨1359258, by rfl⟩ : syracuseStep 3624689 = 2718517) B2718517
theorem B2416459 : Blo 2147435 2416459 := bstep (se 1 (by rfl) ⟨1812344, by rfl⟩ : syracuseStep 2416459 = 3624689) B3624689
theorem B3221945 : Blo 2147435 3221945 := bstep (se 2 (by rfl) ⟨1208229, by rfl⟩ : syracuseStep 3221945 = 2416459) B2416459
theorem B2147963 : Blo 2147435 2147963 := bstep (se 1 (by rfl) ⟨1610972, by rfl⟩ : syracuseStep 2147963 = 3221945) B3221945
theorem B3674149 : Blo 2147435 3674149 := bbase (se 4 (by rfl) ⟨344451, by rfl⟩ : syracuseStep 3674149 = 688903) (by norm_num)
theorem B19595461 : Blo 2147435 19595461 := bstep (se 4 (by rfl) ⟨1837074, by rfl⟩ : syracuseStep 19595461 = 3674149) B3674149
theorem B26127281 : Blo 2147435 26127281 := bstep (se 2 (by rfl) ⟨9797730, by rfl⟩ : syracuseStep 26127281 = 19595461) B19595461
theorem B17418187 : Blo 2147435 17418187 := bstep (se 1 (by rfl) ⟨13063640, by rfl⟩ : syracuseStep 17418187 = 26127281) B26127281
theorem B23224249 : Blo 2147435 23224249 := bstep (se 2 (by rfl) ⟨8709093, by rfl⟩ : syracuseStep 23224249 = 17418187) B17418187
theorem B30965665 : Blo 2147435 30965665 := bstep (se 2 (by rfl) ⟨11612124, by rfl⟩ : syracuseStep 30965665 = 23224249) B23224249
theorem B41287553 : Blo 2147435 41287553 := bstep (se 2 (by rfl) ⟨15482832, by rfl⟩ : syracuseStep 41287553 = 30965665) B30965665
theorem B27525035 : Blo 2147435 27525035 := bstep (se 1 (by rfl) ⟨20643776, by rfl⟩ : syracuseStep 27525035 = 41287553) B41287553
theorem B18350023 : Blo 2147435 18350023 := bstep (se 1 (by rfl) ⟨13762517, by rfl⟩ : syracuseStep 18350023 = 27525035) B27525035
theorem B24466697 : Blo 2147435 24466697 := bstep (se 2 (by rfl) ⟨9175011, by rfl⟩ : syracuseStep 24466697 = 18350023) B18350023
theorem B16311131 : Blo 2147435 16311131 := bstep (se 1 (by rfl) ⟨12233348, by rfl⟩ : syracuseStep 16311131 = 24466697) B24466697
theorem B10874087 : Blo 2147435 10874087 := bstep (se 1 (by rfl) ⟨8155565, by rfl⟩ : syracuseStep 10874087 = 16311131) B16311131
theorem B7249391 : Blo 2147435 7249391 := bstep (se 1 (by rfl) ⟨5437043, by rfl⟩ : syracuseStep 7249391 = 10874087) B10874087
theorem B4832927 : Blo 2147435 4832927 := bstep (se 1 (by rfl) ⟨3624695, by rfl⟩ : syracuseStep 4832927 = 7249391) B7249391
theorem B3221951 : Blo 2147435 3221951 := bstep (se 1 (by rfl) ⟨2416463, by rfl⟩ : syracuseStep 3221951 = 4832927) B4832927
theorem B2147967 : Blo 2147435 2147967 := bstep (se 1 (by rfl) ⟨1610975, by rfl⟩ : syracuseStep 2147967 = 3221951) B3221951
theorem B3221957 : Blo 2147435 3221957 := bbase (se 4 (by rfl) ⟨302058, by rfl⟩ : syracuseStep 3221957 = 604117) (by norm_num)
theorem B2147971 : Blo 2147435 2147971 := bstep (se 1 (by rfl) ⟨1610978, by rfl⟩ : syracuseStep 2147971 = 3221957) B3221957
theorem B3624709 : Blo 2147435 3624709 := bbase (se 4 (by rfl) ⟨339816, by rfl⟩ : syracuseStep 3624709 = 679633) (by norm_num)
theorem B4832945 : Blo 2147435 4832945 := bstep (se 2 (by rfl) ⟨1812354, by rfl⟩ : syracuseStep 4832945 = 3624709) B3624709
theorem B3221963 : Blo 2147435 3221963 := bstep (se 1 (by rfl) ⟨2416472, by rfl⟩ : syracuseStep 3221963 = 4832945) B4832945
theorem B2147975 : Blo 2147435 2147975 := bstep (se 1 (by rfl) ⟨1610981, by rfl⟩ : syracuseStep 2147975 = 3221963) B3221963
theorem B2416477 : Blo 2147435 2416477 := bbase (se 3 (by rfl) ⟨453089, by rfl⟩ : syracuseStep 2416477 = 906179) (by norm_num)
theorem B3221969 : Blo 2147435 3221969 := bstep (se 2 (by rfl) ⟨1208238, by rfl⟩ : syracuseStep 3221969 = 2416477) B2416477
theorem B2147979 : Blo 2147435 2147979 := bstep (se 1 (by rfl) ⟨1610984, by rfl⟩ : syracuseStep 2147979 = 3221969) B3221969
theorem B7249445 : Blo 2147435 7249445 := bbase (se 4 (by rfl) ⟨679635, by rfl⟩ : syracuseStep 7249445 = 1359271) (by norm_num)
theorem B4832963 : Blo 2147435 4832963 := bstep (se 1 (by rfl) ⟨3624722, by rfl⟩ : syracuseStep 4832963 = 7249445) B7249445
theorem B3221975 : Blo 2147435 3221975 := bstep (se 1 (by rfl) ⟨2416481, by rfl⟩ : syracuseStep 3221975 = 4832963) B4832963
theorem B2147983 : Blo 2147435 2147983 := bstep (se 1 (by rfl) ⟨1610987, by rfl⟩ : syracuseStep 2147983 = 3221975) B3221975
theorem B3221981 : Blo 2147435 3221981 := bbase (se 3 (by rfl) ⟨604121, by rfl⟩ : syracuseStep 3221981 = 1208243) (by norm_num)
theorem B2147987 : Blo 2147435 2147987 := bstep (se 1 (by rfl) ⟨1610990, by rfl⟩ : syracuseStep 2147987 = 3221981) B3221981
theorem B4832981 : Blo 2147435 4832981 := bbase (se 7 (by rfl) ⟨56636, by rfl⟩ : syracuseStep 4832981 = 113273) (by norm_num)
theorem B3221987 : Blo 2147435 3221987 := bstep (se 1 (by rfl) ⟨2416490, by rfl⟩ : syracuseStep 3221987 = 4832981) B4832981
theorem B2147991 : Blo 2147435 2147991 := bstep (se 1 (by rfl) ⟨1610993, by rfl⟩ : syracuseStep 2147991 = 3221987) B3221987
theorem B5161013 : Blo 2147435 5161013 := bbase (se 5 (by rfl) ⟨241922, by rfl⟩ : syracuseStep 5161013 = 483845) (by norm_num)
theorem B3440675 : Blo 2147435 3440675 := bstep (se 1 (by rfl) ⟨2580506, by rfl⟩ : syracuseStep 3440675 = 5161013) B5161013
theorem B9175133 : Blo 2147435 9175133 := bstep (se 3 (by rfl) ⟨1720337, by rfl⟩ : syracuseStep 9175133 = 3440675) B3440675
theorem B6116755 : Blo 2147435 6116755 := bstep (se 1 (by rfl) ⟨4587566, by rfl⟩ : syracuseStep 6116755 = 9175133) B9175133
theorem B8155673 : Blo 2147435 8155673 := bstep (se 2 (by rfl) ⟨3058377, by rfl⟩ : syracuseStep 8155673 = 6116755) B6116755
theorem B5437115 : Blo 2147435 5437115 := bstep (se 1 (by rfl) ⟨4077836, by rfl⟩ : syracuseStep 5437115 = 8155673) B8155673
theorem B3624743 : Blo 2147435 3624743 := bstep (se 1 (by rfl) ⟨2718557, by rfl⟩ : syracuseStep 3624743 = 5437115) B5437115
theorem B2416495 : Blo 2147435 2416495 := bstep (se 1 (by rfl) ⟨1812371, by rfl⟩ : syracuseStep 2416495 = 3624743) B3624743
theorem B3221993 : Blo 2147435 3221993 := bstep (se 2 (by rfl) ⟨1208247, by rfl⟩ : syracuseStep 3221993 = 2416495) B2416495
theorem B2147995 : Blo 2147435 2147995 := bstep (se 1 (by rfl) ⟨1610996, by rfl⟩ : syracuseStep 2147995 = 3221993) B3221993
theorem B20644085 : Blo 2147435 20644085 := bbase (se 5 (by rfl) ⟨967691, by rfl⟩ : syracuseStep 20644085 = 1935383) (by norm_num)
theorem B13762723 : Blo 2147435 13762723 := bstep (se 1 (by rfl) ⟨10322042, by rfl⟩ : syracuseStep 13762723 = 20644085) B20644085
theorem B18350297 : Blo 2147435 18350297 := bstep (se 2 (by rfl) ⟨6881361, by rfl⟩ : syracuseStep 18350297 = 13762723) B13762723
theorem B12233531 : Blo 2147435 12233531 := bstep (se 1 (by rfl) ⟨9175148, by rfl⟩ : syracuseStep 12233531 = 18350297) B18350297
theorem B8155687 : Blo 2147435 8155687 := bstep (se 1 (by rfl) ⟨6116765, by rfl⟩ : syracuseStep 8155687 = 12233531) B12233531
theorem B10874249 : Blo 2147435 10874249 := bstep (se 2 (by rfl) ⟨4077843, by rfl⟩ : syracuseStep 10874249 = 8155687) B8155687
theorem B7249499 : Blo 2147435 7249499 := bstep (se 1 (by rfl) ⟨5437124, by rfl⟩ : syracuseStep 7249499 = 10874249) B10874249
theorem B4832999 : Blo 2147435 4832999 := bstep (se 1 (by rfl) ⟨3624749, by rfl⟩ : syracuseStep 4832999 = 7249499) B7249499
theorem B3221999 : Blo 2147435 3221999 := bstep (se 1 (by rfl) ⟨2416499, by rfl⟩ : syracuseStep 3221999 = 4832999) B4832999
theorem B2147999 : Blo 2147435 2147999 := bstep (se 1 (by rfl) ⟨1610999, by rfl⟩ : syracuseStep 2147999 = 3221999) B3221999
theorem B3222005 : Blo 2147435 3222005 := bbase (se 5 (by rfl) ⟨151031, by rfl⟩ : syracuseStep 3222005 = 302063) (by norm_num)
theorem B2148003 : Blo 2147435 2148003 := bstep (se 1 (by rfl) ⟨1611002, by rfl⟩ : syracuseStep 2148003 = 3222005) B3222005
theorem B6116789 : Blo 2147435 6116789 := bbase (se 5 (by rfl) ⟨286724, by rfl⟩ : syracuseStep 6116789 = 573449) (by norm_num)
theorem B4077859 : Blo 2147435 4077859 := bstep (se 1 (by rfl) ⟨3058394, by rfl⟩ : syracuseStep 4077859 = 6116789) B6116789
theorem B5437145 : Blo 2147435 5437145 := bstep (se 2 (by rfl) ⟨2038929, by rfl⟩ : syracuseStep 5437145 = 4077859) B4077859
theorem B3624763 : Blo 2147435 3624763 := bstep (se 1 (by rfl) ⟨2718572, by rfl⟩ : syracuseStep 3624763 = 5437145) B5437145
theorem B4833017 : Blo 2147435 4833017 := bstep (se 2 (by rfl) ⟨1812381, by rfl⟩ : syracuseStep 4833017 = 3624763) B3624763
theorem B3222011 : Blo 2147435 3222011 := bstep (se 1 (by rfl) ⟨2416508, by rfl⟩ : syracuseStep 3222011 = 4833017) B4833017
theorem B2148007 : Blo 2147435 2148007 := bstep (se 1 (by rfl) ⟨1611005, by rfl⟩ : syracuseStep 2148007 = 3222011) B3222011
theorem B2416513 : Blo 2147435 2416513 := bbase (se 2 (by rfl) ⟨906192, by rfl⟩ : syracuseStep 2416513 = 1812385) (by norm_num)
theorem B3222017 : Blo 2147435 3222017 := bstep (se 2 (by rfl) ⟨1208256, by rfl⟩ : syracuseStep 3222017 = 2416513) B2416513
theorem B2148011 : Blo 2147435 2148011 := bstep (se 1 (by rfl) ⟨1611008, by rfl⟩ : syracuseStep 2148011 = 3222017) B3222017
theorem B5437165 : Blo 2147435 5437165 := bbase (se 3 (by rfl) ⟨1019468, by rfl⟩ : syracuseStep 5437165 = 2038937) (by norm_num)
theorem B7249553 : Blo 2147435 7249553 := bstep (se 2 (by rfl) ⟨2718582, by rfl⟩ : syracuseStep 7249553 = 5437165) B5437165
theorem B4833035 : Blo 2147435 4833035 := bstep (se 1 (by rfl) ⟨3624776, by rfl⟩ : syracuseStep 4833035 = 7249553) B7249553
theorem B3222023 : Blo 2147435 3222023 := bstep (se 1 (by rfl) ⟨2416517, by rfl⟩ : syracuseStep 3222023 = 4833035) B4833035
theorem B2148015 : Blo 2147435 2148015 := bstep (se 1 (by rfl) ⟨1611011, by rfl⟩ : syracuseStep 2148015 = 3222023) B3222023
theorem B3222029 : Blo 2147435 3222029 := bbase (se 3 (by rfl) ⟨604130, by rfl⟩ : syracuseStep 3222029 = 1208261) (by norm_num)
theorem B2148019 : Blo 2147435 2148019 := bstep (se 1 (by rfl) ⟨1611014, by rfl⟩ : syracuseStep 2148019 = 3222029) B3222029
theorem B4833053 : Blo 2147435 4833053 := bbase (se 3 (by rfl) ⟨906197, by rfl⟩ : syracuseStep 4833053 = 1812395) (by norm_num)
theorem B3222035 : Blo 2147435 3222035 := bstep (se 1 (by rfl) ⟨2416526, by rfl⟩ : syracuseStep 3222035 = 4833053) B4833053
theorem B2148023 : Blo 2147435 2148023 := bstep (se 1 (by rfl) ⟨1611017, by rfl⟩ : syracuseStep 2148023 = 3222035) B3222035
theorem B3624797 : Blo 2147435 3624797 := bbase (se 3 (by rfl) ⟨679649, by rfl⟩ : syracuseStep 3624797 = 1359299) (by norm_num)
theorem B2416531 : Blo 2147435 2416531 := bstep (se 1 (by rfl) ⟨1812398, by rfl⟩ : syracuseStep 2416531 = 3624797) B3624797
theorem B3222041 : Blo 2147435 3222041 := bstep (se 2 (by rfl) ⟨1208265, by rfl⟩ : syracuseStep 3222041 = 2416531) B2416531
theorem B2148027 : Blo 2147435 2148027 := bstep (se 1 (by rfl) ⟨1611020, by rfl⟩ : syracuseStep 2148027 = 3222041) B3222041
theorem B9175285 : Blo 2147435 9175285 := bbase (se 5 (by rfl) ⟨430091, by rfl⟩ : syracuseStep 9175285 = 860183) (by norm_num)
theorem B12233713 : Blo 2147435 12233713 := bstep (se 2 (by rfl) ⟨4587642, by rfl⟩ : syracuseStep 12233713 = 9175285) B9175285
theorem B16311617 : Blo 2147435 16311617 := bstep (se 2 (by rfl) ⟨6116856, by rfl⟩ : syracuseStep 16311617 = 12233713) B12233713
theorem B10874411 : Blo 2147435 10874411 := bstep (se 1 (by rfl) ⟨8155808, by rfl⟩ : syracuseStep 10874411 = 16311617) B16311617
theorem B7249607 : Blo 2147435 7249607 := bstep (se 1 (by rfl) ⟨5437205, by rfl⟩ : syracuseStep 7249607 = 10874411) B10874411
theorem B4833071 : Blo 2147435 4833071 := bstep (se 1 (by rfl) ⟨3624803, by rfl⟩ : syracuseStep 4833071 = 7249607) B7249607
theorem B3222047 : Blo 2147435 3222047 := bstep (se 1 (by rfl) ⟨2416535, by rfl⟩ : syracuseStep 3222047 = 4833071) B4833071
theorem B2148031 : Blo 2147435 2148031 := bstep (se 1 (by rfl) ⟨1611023, by rfl⟩ : syracuseStep 2148031 = 3222047) B3222047
theorem B3222053 : Blo 2147435 3222053 := bbase (se 4 (by rfl) ⟨302067, by rfl⟩ : syracuseStep 3222053 = 604135) (by norm_num)
theorem B2148035 : Blo 2147435 2148035 := bstep (se 1 (by rfl) ⟨1611026, by rfl⟩ : syracuseStep 2148035 = 3222053) B3222053
theorem B2718613 : Blo 2147435 2718613 := bbase (se 6 (by rfl) ⟨63717, by rfl⟩ : syracuseStep 2718613 = 127435) (by norm_num)
theorem B3624817 : Blo 2147435 3624817 := bstep (se 2 (by rfl) ⟨1359306, by rfl⟩ : syracuseStep 3624817 = 2718613) B2718613
theorem B4833089 : Blo 2147435 4833089 := bstep (se 2 (by rfl) ⟨1812408, by rfl⟩ : syracuseStep 4833089 = 3624817) B3624817
theorem B3222059 : Blo 2147435 3222059 := bstep (se 1 (by rfl) ⟨2416544, by rfl⟩ : syracuseStep 3222059 = 4833089) B4833089
theorem B2148039 : Blo 2147435 2148039 := bstep (se 1 (by rfl) ⟨1611029, by rfl⟩ : syracuseStep 2148039 = 3222059) B3222059
theorem B2416549 : Blo 2147435 2416549 := bbase (se 4 (by rfl) ⟨226551, by rfl⟩ : syracuseStep 2416549 = 453103) (by norm_num)
theorem B3222065 : Blo 2147435 3222065 := bstep (se 2 (by rfl) ⟨1208274, by rfl⟩ : syracuseStep 3222065 = 2416549) B2416549
theorem B2148043 : Blo 2147435 2148043 := bstep (se 1 (by rfl) ⟨1611032, by rfl⟩ : syracuseStep 2148043 = 3222065) B3222065
theorem B15483413 : Blo 2147435 15483413 := bbase (se 6 (by rfl) ⟨362892, by rfl⟩ : syracuseStep 15483413 = 725785) (by norm_num)
theorem B10322275 : Blo 2147435 10322275 := bstep (se 1 (by rfl) ⟨7741706, by rfl⟩ : syracuseStep 10322275 = 15483413) B15483413
theorem B13763033 : Blo 2147435 13763033 := bstep (se 2 (by rfl) ⟨5161137, by rfl⟩ : syracuseStep 13763033 = 10322275) B10322275
theorem B9175355 : Blo 2147435 9175355 := bstep (se 1 (by rfl) ⟨6881516, by rfl⟩ : syracuseStep 9175355 = 13763033) B13763033
theorem B6116903 : Blo 2147435 6116903 := bstep (se 1 (by rfl) ⟨4587677, by rfl⟩ : syracuseStep 6116903 = 9175355) B9175355
theorem B4077935 : Blo 2147435 4077935 := bstep (se 1 (by rfl) ⟨3058451, by rfl⟩ : syracuseStep 4077935 = 6116903) B6116903
theorem B2718623 : Blo 2147435 2718623 := bstep (se 1 (by rfl) ⟨2038967, by rfl⟩ : syracuseStep 2718623 = 4077935) B4077935
theorem B7249661 : Blo 2147435 7249661 := bstep (se 3 (by rfl) ⟨1359311, by rfl⟩ : syracuseStep 7249661 = 2718623) B2718623
theorem B4833107 : Blo 2147435 4833107 := bstep (se 1 (by rfl) ⟨3624830, by rfl⟩ : syracuseStep 4833107 = 7249661) B7249661
theorem B3222071 : Blo 2147435 3222071 := bstep (se 1 (by rfl) ⟨2416553, by rfl⟩ : syracuseStep 3222071 = 4833107) B4833107
theorem B2148047 : Blo 2147435 2148047 := bstep (se 1 (by rfl) ⟨1611035, by rfl⟩ : syracuseStep 2148047 = 3222071) B3222071
theorem B3222077 : Blo 2147435 3222077 := bbase (se 3 (by rfl) ⟨604139, by rfl⟩ : syracuseStep 3222077 = 1208279) (by norm_num)
theorem B2148051 : Blo 2147435 2148051 := bstep (se 1 (by rfl) ⟨1611038, by rfl⟩ : syracuseStep 2148051 = 3222077) B3222077
theorem B4833125 : Blo 2147435 4833125 := bbase (se 4 (by rfl) ⟨453105, by rfl⟩ : syracuseStep 4833125 = 906211) (by norm_num)
theorem B3222083 : Blo 2147435 3222083 := bstep (se 1 (by rfl) ⟨2416562, by rfl⟩ : syracuseStep 3222083 = 4833125) B4833125
theorem B2148055 : Blo 2147435 2148055 := bstep (se 1 (by rfl) ⟨1611041, by rfl⟩ : syracuseStep 2148055 = 3222083) B3222083
theorem B5437277 : Blo 2147435 5437277 := bbase (se 3 (by rfl) ⟨1019489, by rfl⟩ : syracuseStep 5437277 = 2038979) (by norm_num)
theorem B3624851 : Blo 2147435 3624851 := bstep (se 1 (by rfl) ⟨2718638, by rfl⟩ : syracuseStep 3624851 = 5437277) B5437277
theorem B2416567 : Blo 2147435 2416567 := bstep (se 1 (by rfl) ⟨1812425, by rfl⟩ : syracuseStep 2416567 = 3624851) B3624851
theorem B3222089 : Blo 2147435 3222089 := bstep (se 2 (by rfl) ⟨1208283, by rfl⟩ : syracuseStep 3222089 = 2416567) B2416567
theorem B2148059 : Blo 2147435 2148059 := bstep (se 1 (by rfl) ⟨1611044, by rfl⟩ : syracuseStep 2148059 = 3222089) B3222089
theorem B4077965 : Blo 2147435 4077965 := bbase (se 3 (by rfl) ⟨764618, by rfl⟩ : syracuseStep 4077965 = 1529237) (by norm_num)
theorem B10874573 : Blo 2147435 10874573 := bstep (se 3 (by rfl) ⟨2038982, by rfl⟩ : syracuseStep 10874573 = 4077965) B4077965
theorem B7249715 : Blo 2147435 7249715 := bstep (se 1 (by rfl) ⟨5437286, by rfl⟩ : syracuseStep 7249715 = 10874573) B10874573
theorem B4833143 : Blo 2147435 4833143 := bstep (se 1 (by rfl) ⟨3624857, by rfl⟩ : syracuseStep 4833143 = 7249715) B7249715
theorem B3222095 : Blo 2147435 3222095 := bstep (se 1 (by rfl) ⟨2416571, by rfl⟩ : syracuseStep 3222095 = 4833143) B4833143
theorem B2148063 : Blo 2147435 2148063 := bstep (se 1 (by rfl) ⟨1611047, by rfl⟩ : syracuseStep 2148063 = 3222095) B3222095
theorem B3222101 : Blo 2147435 3222101 := bbase (se 8 (by rfl) ⟨18879, by rfl⟩ : syracuseStep 3222101 = 37759) (by norm_num)
theorem B2148067 : Blo 2147435 2148067 := bstep (se 1 (by rfl) ⟨1611050, by rfl⟩ : syracuseStep 2148067 = 3222101) B3222101
theorem B5511493 : Blo 2147435 5511493 := bbase (se 4 (by rfl) ⟨516702, by rfl⟩ : syracuseStep 5511493 = 1033405) (by norm_num)
theorem B7348657 : Blo 2147435 7348657 := bstep (se 2 (by rfl) ⟨2755746, by rfl⟩ : syracuseStep 7348657 = 5511493) B5511493
theorem B9798209 : Blo 2147435 9798209 := bstep (se 2 (by rfl) ⟨3674328, by rfl⟩ : syracuseStep 9798209 = 7348657) B7348657
theorem B6532139 : Blo 2147435 6532139 := bstep (se 1 (by rfl) ⟨4899104, by rfl⟩ : syracuseStep 6532139 = 9798209) B9798209
theorem B4354759 : Blo 2147435 4354759 := bstep (se 1 (by rfl) ⟨3266069, by rfl⟩ : syracuseStep 4354759 = 6532139) B6532139
theorem B5806345 : Blo 2147435 5806345 := bstep (se 2 (by rfl) ⟨2177379, by rfl⟩ : syracuseStep 5806345 = 4354759) B4354759
theorem B7741793 : Blo 2147435 7741793 := bstep (se 2 (by rfl) ⟨2903172, by rfl⟩ : syracuseStep 7741793 = 5806345) B5806345
theorem B5161195 : Blo 2147435 5161195 := bstep (se 1 (by rfl) ⟨3870896, by rfl⟩ : syracuseStep 5161195 = 7741793) B7741793
theorem B6881593 : Blo 2147435 6881593 := bstep (se 2 (by rfl) ⟨2580597, by rfl⟩ : syracuseStep 6881593 = 5161195) B5161195
theorem B9175457 : Blo 2147435 9175457 := bstep (se 2 (by rfl) ⟨3440796, by rfl⟩ : syracuseStep 9175457 = 6881593) B6881593
theorem B6116971 : Blo 2147435 6116971 := bstep (se 1 (by rfl) ⟨4587728, by rfl⟩ : syracuseStep 6116971 = 9175457) B9175457
theorem B8155961 : Blo 2147435 8155961 := bstep (se 2 (by rfl) ⟨3058485, by rfl⟩ : syracuseStep 8155961 = 6116971) B6116971
theorem B5437307 : Blo 2147435 5437307 := bstep (se 1 (by rfl) ⟨4077980, by rfl⟩ : syracuseStep 5437307 = 8155961) B8155961
theorem B3624871 : Blo 2147435 3624871 := bstep (se 1 (by rfl) ⟨2718653, by rfl⟩ : syracuseStep 3624871 = 5437307) B5437307
theorem B4833161 : Blo 2147435 4833161 := bstep (se 2 (by rfl) ⟨1812435, by rfl⟩ : syracuseStep 4833161 = 3624871) B3624871
theorem B3222107 : Blo 2147435 3222107 := bstep (se 1 (by rfl) ⟨2416580, by rfl⟩ : syracuseStep 3222107 = 4833161) B4833161
theorem B2148071 : Blo 2147435 2148071 := bstep (se 1 (by rfl) ⟨1611053, by rfl⟩ : syracuseStep 2148071 = 3222107) B3222107
theorem B2416585 : Blo 2147435 2416585 := bbase (se 2 (by rfl) ⟨906219, by rfl⟩ : syracuseStep 2416585 = 1812439) (by norm_num)
theorem B3222113 : Blo 2147435 3222113 := bstep (se 2 (by rfl) ⟨1208292, by rfl⟩ : syracuseStep 3222113 = 2416585) B2416585
theorem B2148075 : Blo 2147435 2148075 := bstep (se 1 (by rfl) ⟨1611056, by rfl⟩ : syracuseStep 2148075 = 3222113) B3222113
theorem B6200453 : Blo 2147435 6200453 := bbase (se 4 (by rfl) ⟨581292, by rfl⟩ : syracuseStep 6200453 = 1162585) (by norm_num)
theorem B4133635 : Blo 2147435 4133635 := bstep (se 1 (by rfl) ⟨3100226, by rfl⟩ : syracuseStep 4133635 = 6200453) B6200453
theorem B22046053 : Blo 2147435 22046053 := bstep (se 4 (by rfl) ⟨2066817, by rfl⟩ : syracuseStep 22046053 = 4133635) B4133635
theorem B29394737 : Blo 2147435 29394737 := bstep (se 2 (by rfl) ⟨11023026, by rfl⟩ : syracuseStep 29394737 = 22046053) B22046053
theorem B19596491 : Blo 2147435 19596491 := bstep (se 1 (by rfl) ⟨14697368, by rfl⟩ : syracuseStep 19596491 = 29394737) B29394737
theorem B13064327 : Blo 2147435 13064327 := bstep (se 1 (by rfl) ⟨9798245, by rfl⟩ : syracuseStep 13064327 = 19596491) B19596491
theorem B8709551 : Blo 2147435 8709551 := bstep (se 1 (by rfl) ⟨6532163, by rfl⟩ : syracuseStep 8709551 = 13064327) B13064327
theorem B5806367 : Blo 2147435 5806367 := bstep (se 1 (by rfl) ⟨4354775, by rfl⟩ : syracuseStep 5806367 = 8709551) B8709551
theorem B3870911 : Blo 2147435 3870911 := bstep (se 1 (by rfl) ⟨2903183, by rfl⟩ : syracuseStep 3870911 = 5806367) B5806367
theorem B2580607 : Blo 2147435 2580607 := bstep (se 1 (by rfl) ⟨1935455, by rfl⟩ : syracuseStep 2580607 = 3870911) B3870911
theorem B3440809 : Blo 2147435 3440809 := bstep (se 2 (by rfl) ⟨1290303, by rfl⟩ : syracuseStep 3440809 = 2580607) B2580607
theorem B18350981 : Blo 2147435 18350981 := bstep (se 4 (by rfl) ⟨1720404, by rfl⟩ : syracuseStep 18350981 = 3440809) B3440809
theorem B12233987 : Blo 2147435 12233987 := bstep (se 1 (by rfl) ⟨9175490, by rfl⟩ : syracuseStep 12233987 = 18350981) B18350981
theorem B8155991 : Blo 2147435 8155991 := bstep (se 1 (by rfl) ⟨6116993, by rfl⟩ : syracuseStep 8155991 = 12233987) B12233987
theorem B5437327 : Blo 2147435 5437327 := bstep (se 1 (by rfl) ⟨4077995, by rfl⟩ : syracuseStep 5437327 = 8155991) B8155991
theorem B7249769 : Blo 2147435 7249769 := bstep (se 2 (by rfl) ⟨2718663, by rfl⟩ : syracuseStep 7249769 = 5437327) B5437327
theorem B4833179 : Blo 2147435 4833179 := bstep (se 1 (by rfl) ⟨3624884, by rfl⟩ : syracuseStep 4833179 = 7249769) B7249769
theorem B3222119 : Blo 2147435 3222119 := bstep (se 1 (by rfl) ⟨2416589, by rfl⟩ : syracuseStep 3222119 = 4833179) B4833179
theorem B2148079 : Blo 2147435 2148079 := bstep (se 1 (by rfl) ⟨1611059, by rfl⟩ : syracuseStep 2148079 = 3222119) B3222119
theorem B3222125 : Blo 2147435 3222125 := bbase (se 3 (by rfl) ⟨604148, by rfl⟩ : syracuseStep 3222125 = 1208297) (by norm_num)
theorem B2148083 : Blo 2147435 2148083 := bstep (se 1 (by rfl) ⟨1611062, by rfl⟩ : syracuseStep 2148083 = 3222125) B3222125
theorem B4833197 : Blo 2147435 4833197 := bbase (se 3 (by rfl) ⟨906224, by rfl⟩ : syracuseStep 4833197 = 1812449) (by norm_num)
theorem B3222131 : Blo 2147435 3222131 := bstep (se 1 (by rfl) ⟨2416598, by rfl⟩ : syracuseStep 3222131 = 4833197) B4833197
theorem B2148087 : Blo 2147435 2148087 := bstep (se 1 (by rfl) ⟨1611065, by rfl⟩ : syracuseStep 2148087 = 3222131) B3222131
theorem B6117029 : Blo 2147435 6117029 := bbase (se 4 (by rfl) ⟨573471, by rfl⟩ : syracuseStep 6117029 = 1146943) (by norm_num)
theorem B4078019 : Blo 2147435 4078019 := bstep (se 1 (by rfl) ⟨3058514, by rfl⟩ : syracuseStep 4078019 = 6117029) B6117029
theorem B2718679 : Blo 2147435 2718679 := bstep (se 1 (by rfl) ⟨2039009, by rfl⟩ : syracuseStep 2718679 = 4078019) B4078019
theorem B3624905 : Blo 2147435 3624905 := bstep (se 2 (by rfl) ⟨1359339, by rfl⟩ : syracuseStep 3624905 = 2718679) B2718679
theorem B2416603 : Blo 2147435 2416603 := bstep (se 1 (by rfl) ⟨1812452, by rfl⟩ : syracuseStep 2416603 = 3624905) B3624905
theorem B3222137 : Blo 2147435 3222137 := bstep (se 2 (by rfl) ⟨1208301, by rfl⟩ : syracuseStep 3222137 = 2416603) B2416603
theorem B2148091 : Blo 2147435 2148091 := bstep (se 1 (by rfl) ⟨1611068, by rfl⟩ : syracuseStep 2148091 = 3222137) B3222137
theorem B19596629 : Blo 2147435 19596629 := bbase (se 12 (by rfl) ⟨7176, by rfl⟩ : syracuseStep 19596629 = 14353) (by norm_num)
theorem B13064419 : Blo 2147435 13064419 := bstep (se 1 (by rfl) ⟨9798314, by rfl⟩ : syracuseStep 13064419 = 19596629) B19596629
theorem B17419225 : Blo 2147435 17419225 := bstep (se 2 (by rfl) ⟨6532209, by rfl⟩ : syracuseStep 17419225 = 13064419) B13064419
theorem B23225633 : Blo 2147435 23225633 := bstep (se 2 (by rfl) ⟨8709612, by rfl⟩ : syracuseStep 23225633 = 17419225) B17419225
theorem B15483755 : Blo 2147435 15483755 := bstep (se 1 (by rfl) ⟨11612816, by rfl⟩ : syracuseStep 15483755 = 23225633) B23225633
theorem B41290013 : Blo 2147435 41290013 := bstep (se 3 (by rfl) ⟨7741877, by rfl⟩ : syracuseStep 41290013 = 15483755) B15483755
theorem B27526675 : Blo 2147435 27526675 := bstep (se 1 (by rfl) ⟨20645006, by rfl⟩ : syracuseStep 27526675 = 41290013) B41290013
theorem B36702233 : Blo 2147435 36702233 := bstep (se 2 (by rfl) ⟨13763337, by rfl⟩ : syracuseStep 36702233 = 27526675) B27526675
theorem B24468155 : Blo 2147435 24468155 := bstep (se 1 (by rfl) ⟨18351116, by rfl⟩ : syracuseStep 24468155 = 36702233) B36702233
theorem B16312103 : Blo 2147435 16312103 := bstep (se 1 (by rfl) ⟨12234077, by rfl⟩ : syracuseStep 16312103 = 24468155) B24468155
theorem B10874735 : Blo 2147435 10874735 := bstep (se 1 (by rfl) ⟨8156051, by rfl⟩ : syracuseStep 10874735 = 16312103) B16312103
theorem B7249823 : Blo 2147435 7249823 := bstep (se 1 (by rfl) ⟨5437367, by rfl⟩ : syracuseStep 7249823 = 10874735) B10874735
theorem B4833215 : Blo 2147435 4833215 := bstep (se 1 (by rfl) ⟨3624911, by rfl⟩ : syracuseStep 4833215 = 7249823) B7249823
theorem B3222143 : Blo 2147435 3222143 := bstep (se 1 (by rfl) ⟨2416607, by rfl⟩ : syracuseStep 3222143 = 4833215) B4833215
theorem B2148095 : Blo 2147435 2148095 := bstep (se 1 (by rfl) ⟨1611071, by rfl⟩ : syracuseStep 2148095 = 3222143) B3222143
theorem B3222149 : Blo 2147435 3222149 := bbase (se 4 (by rfl) ⟨302076, by rfl⟩ : syracuseStep 3222149 = 604153) (by norm_num)
theorem B2148099 : Blo 2147435 2148099 := bstep (se 1 (by rfl) ⟨1611074, by rfl⟩ : syracuseStep 2148099 = 3222149) B3222149
theorem B3624925 : Blo 2147435 3624925 := bbase (se 3 (by rfl) ⟨679673, by rfl⟩ : syracuseStep 3624925 = 1359347) (by norm_num)
theorem B4833233 : Blo 2147435 4833233 := bstep (se 2 (by rfl) ⟨1812462, by rfl⟩ : syracuseStep 4833233 = 3624925) B3624925
theorem B3222155 : Blo 2147435 3222155 := bstep (se 1 (by rfl) ⟨2416616, by rfl⟩ : syracuseStep 3222155 = 4833233) B4833233
theorem B2148103 : Blo 2147435 2148103 := bstep (se 1 (by rfl) ⟨1611077, by rfl⟩ : syracuseStep 2148103 = 3222155) B3222155
theorem B2416621 : Blo 2147435 2416621 := bbase (se 3 (by rfl) ⟨453116, by rfl⟩ : syracuseStep 2416621 = 906233) (by norm_num)
theorem B3222161 : Blo 2147435 3222161 := bstep (se 2 (by rfl) ⟨1208310, by rfl⟩ : syracuseStep 3222161 = 2416621) B2416621
theorem B2148107 : Blo 2147435 2148107 := bstep (se 1 (by rfl) ⟨1611080, by rfl⟩ : syracuseStep 2148107 = 3222161) B3222161
theorem B7249877 : Blo 2147435 7249877 := bbase (se 7 (by rfl) ⟨84959, by rfl⟩ : syracuseStep 7249877 = 169919) (by norm_num)
theorem B4833251 : Blo 2147435 4833251 := bstep (se 1 (by rfl) ⟨3624938, by rfl⟩ : syracuseStep 4833251 = 7249877) B7249877
theorem B3222167 : Blo 2147435 3222167 := bstep (se 1 (by rfl) ⟨2416625, by rfl⟩ : syracuseStep 3222167 = 4833251) B4833251
theorem B2148111 : Blo 2147435 2148111 := bstep (se 1 (by rfl) ⟨1611083, by rfl⟩ : syracuseStep 2148111 = 3222167) B3222167
theorem B3222173 : Blo 2147435 3222173 := bbase (se 3 (by rfl) ⟨604157, by rfl⟩ : syracuseStep 3222173 = 1208315) (by norm_num)
theorem B2148115 : Blo 2147435 2148115 := bstep (se 1 (by rfl) ⟨1611086, by rfl⟩ : syracuseStep 2148115 = 3222173) B3222173
theorem B4833269 : Blo 2147435 4833269 := bbase (se 5 (by rfl) ⟨226559, by rfl⟩ : syracuseStep 4833269 = 453119) (by norm_num)
theorem B3222179 : Blo 2147435 3222179 := bstep (se 1 (by rfl) ⟨2416634, by rfl⟩ : syracuseStep 3222179 = 4833269) B4833269
theorem B2148119 : Blo 2147435 2148119 := bstep (se 1 (by rfl) ⟨1611089, by rfl⟩ : syracuseStep 2148119 = 3222179) B3222179
theorem B3310709 : Blo 2147435 3310709 := bbase (se 5 (by rfl) ⟨155189, by rfl⟩ : syracuseStep 3310709 = 310379) (by norm_num)
theorem B8828557 : Blo 2147435 8828557 := bstep (se 3 (by rfl) ⟨1655354, by rfl⟩ : syracuseStep 8828557 = 3310709) B3310709
theorem B47085637 : Blo 2147435 47085637 := bstep (se 4 (by rfl) ⟨4414278, by rfl⟩ : syracuseStep 47085637 = 8828557) B8828557
theorem B62780849 : Blo 2147435 62780849 := bstep (se 2 (by rfl) ⟨23542818, by rfl⟩ : syracuseStep 62780849 = 47085637) B47085637
theorem B41853899 : Blo 2147435 41853899 := bstep (se 1 (by rfl) ⟨31390424, by rfl⟩ : syracuseStep 41853899 = 62780849) B62780849
theorem B27902599 : Blo 2147435 27902599 := bstep (se 1 (by rfl) ⟨20926949, by rfl⟩ : syracuseStep 27902599 = 41853899) B41853899
theorem B148813861 : Blo 2147435 148813861 := bstep (se 4 (by rfl) ⟨13951299, by rfl⟩ : syracuseStep 148813861 = 27902599) B27902599
theorem B198418481 : Blo 2147435 198418481 := bstep (se 2 (by rfl) ⟨74406930, by rfl⟩ : syracuseStep 198418481 = 148813861) B148813861
theorem B132278987 : Blo 2147435 132278987 := bstep (se 1 (by rfl) ⟨99209240, by rfl⟩ : syracuseStep 132278987 = 198418481) B198418481
theorem B88185991 : Blo 2147435 88185991 := bstep (se 1 (by rfl) ⟨66139493, by rfl⟩ : syracuseStep 88185991 = 132278987) B132278987
theorem B117581321 : Blo 2147435 117581321 := bstep (se 2 (by rfl) ⟨44092995, by rfl⟩ : syracuseStep 117581321 = 88185991) B88185991
theorem B313550189 : Blo 2147435 313550189 := bstep (se 3 (by rfl) ⟨58790660, by rfl⟩ : syracuseStep 313550189 = 117581321) B117581321
theorem B209033459 : Blo 2147435 209033459 := bstep (se 1 (by rfl) ⟨156775094, by rfl⟩ : syracuseStep 209033459 = 313550189) B313550189
theorem B139355639 : Blo 2147435 139355639 := bstep (se 1 (by rfl) ⟨104516729, by rfl⟩ : syracuseStep 139355639 = 209033459) B209033459
theorem B92903759 : Blo 2147435 92903759 := bstep (se 1 (by rfl) ⟨69677819, by rfl⟩ : syracuseStep 92903759 = 139355639) B139355639
theorem B61935839 : Blo 2147435 61935839 := bstep (se 1 (by rfl) ⟨46451879, by rfl⟩ : syracuseStep 61935839 = 92903759) B92903759
theorem B41290559 : Blo 2147435 41290559 := bstep (se 1 (by rfl) ⟨30967919, by rfl⟩ : syracuseStep 41290559 = 61935839) B61935839
theorem B27527039 : Blo 2147435 27527039 := bstep (se 1 (by rfl) ⟨20645279, by rfl⟩ : syracuseStep 27527039 = 41290559) B41290559
theorem B18351359 : Blo 2147435 18351359 := bstep (se 1 (by rfl) ⟨13763519, by rfl⟩ : syracuseStep 18351359 = 27527039) B27527039
theorem B12234239 : Blo 2147435 12234239 := bstep (se 1 (by rfl) ⟨9175679, by rfl⟩ : syracuseStep 12234239 = 18351359) B18351359
theorem B8156159 : Blo 2147435 8156159 := bstep (se 1 (by rfl) ⟨6117119, by rfl⟩ : syracuseStep 8156159 = 12234239) B12234239
theorem B5437439 : Blo 2147435 5437439 := bstep (se 1 (by rfl) ⟨4078079, by rfl⟩ : syracuseStep 5437439 = 8156159) B8156159
theorem B3624959 : Blo 2147435 3624959 := bstep (se 1 (by rfl) ⟨2718719, by rfl⟩ : syracuseStep 3624959 = 5437439) B5437439
theorem B2416639 : Blo 2147435 2416639 := bstep (se 1 (by rfl) ⟨1812479, by rfl⟩ : syracuseStep 2416639 = 3624959) B3624959
theorem B3222185 : Blo 2147435 3222185 := bstep (se 2 (by rfl) ⟨1208319, by rfl⟩ : syracuseStep 3222185 = 2416639) B2416639
theorem B2148123 : Blo 2147435 2148123 := bstep (se 1 (by rfl) ⟨1611092, by rfl⟩ : syracuseStep 2148123 = 3222185) B3222185
theorem B3058565 : Blo 2147435 3058565 := bbase (se 4 (by rfl) ⟨286740, by rfl⟩ : syracuseStep 3058565 = 573481) (by norm_num)
theorem B8156173 : Blo 2147435 8156173 := bstep (se 3 (by rfl) ⟨1529282, by rfl⟩ : syracuseStep 8156173 = 3058565) B3058565
theorem B10874897 : Blo 2147435 10874897 := bstep (se 2 (by rfl) ⟨4078086, by rfl⟩ : syracuseStep 10874897 = 8156173) B8156173
theorem B7249931 : Blo 2147435 7249931 := bstep (se 1 (by rfl) ⟨5437448, by rfl⟩ : syracuseStep 7249931 = 10874897) B10874897
theorem B4833287 : Blo 2147435 4833287 := bstep (se 1 (by rfl) ⟨3624965, by rfl⟩ : syracuseStep 4833287 = 7249931) B7249931
theorem B3222191 : Blo 2147435 3222191 := bstep (se 1 (by rfl) ⟨2416643, by rfl⟩ : syracuseStep 3222191 = 4833287) B4833287
theorem B2148127 : Blo 2147435 2148127 := bstep (se 1 (by rfl) ⟨1611095, by rfl⟩ : syracuseStep 2148127 = 3222191) B3222191
theorem B3222197 : Blo 2147435 3222197 := bbase (se 5 (by rfl) ⟨151040, by rfl⟩ : syracuseStep 3222197 = 302081) (by norm_num)
theorem B2148131 : Blo 2147435 2148131 := bstep (se 1 (by rfl) ⟨1611098, by rfl⟩ : syracuseStep 2148131 = 3222197) B3222197
theorem B5437469 : Blo 2147435 5437469 := bbase (se 3 (by rfl) ⟨1019525, by rfl⟩ : syracuseStep 5437469 = 2039051) (by norm_num)
theorem B3624979 : Blo 2147435 3624979 := bstep (se 1 (by rfl) ⟨2718734, by rfl⟩ : syracuseStep 3624979 = 5437469) B5437469
theorem B4833305 : Blo 2147435 4833305 := bstep (se 2 (by rfl) ⟨1812489, by rfl⟩ : syracuseStep 4833305 = 3624979) B3624979
theorem B3222203 : Blo 2147435 3222203 := bstep (se 1 (by rfl) ⟨2416652, by rfl⟩ : syracuseStep 3222203 = 4833305) B4833305
theorem B2148135 : Blo 2147435 2148135 := bstep (se 1 (by rfl) ⟨1611101, by rfl⟩ : syracuseStep 2148135 = 3222203) B3222203
theorem B2416657 : Blo 2147435 2416657 := bbase (se 2 (by rfl) ⟨906246, by rfl⟩ : syracuseStep 2416657 = 1812493) (by norm_num)
theorem B3222209 : Blo 2147435 3222209 := bstep (se 2 (by rfl) ⟨1208328, by rfl⟩ : syracuseStep 3222209 = 2416657) B2416657
theorem B2148139 : Blo 2147435 2148139 := bstep (se 1 (by rfl) ⟨1611104, by rfl⟩ : syracuseStep 2148139 = 3222209) B3222209
theorem B4078117 : Blo 2147435 4078117 := bbase (se 4 (by rfl) ⟨382323, by rfl⟩ : syracuseStep 4078117 = 764647) (by norm_num)
theorem B5437489 : Blo 2147435 5437489 := bstep (se 2 (by rfl) ⟨2039058, by rfl⟩ : syracuseStep 5437489 = 4078117) B4078117
theorem B7249985 : Blo 2147435 7249985 := bstep (se 2 (by rfl) ⟨2718744, by rfl⟩ : syracuseStep 7249985 = 5437489) B5437489
theorem B4833323 : Blo 2147435 4833323 := bstep (se 1 (by rfl) ⟨3624992, by rfl⟩ : syracuseStep 4833323 = 7249985) B7249985
theorem B3222215 : Blo 2147435 3222215 := bstep (se 1 (by rfl) ⟨2416661, by rfl⟩ : syracuseStep 3222215 = 4833323) B4833323
theorem B2148143 : Blo 2147435 2148143 := bstep (se 1 (by rfl) ⟨1611107, by rfl⟩ : syracuseStep 2148143 = 3222215) B3222215
theorem B3222221 : Blo 2147435 3222221 := bbase (se 3 (by rfl) ⟨604166, by rfl⟩ : syracuseStep 3222221 = 1208333) (by norm_num)
theorem B2148147 : Blo 2147435 2148147 := bstep (se 1 (by rfl) ⟨1611110, by rfl⟩ : syracuseStep 2148147 = 3222221) B3222221
theorem B4833341 : Blo 2147435 4833341 := bbase (se 3 (by rfl) ⟨906251, by rfl⟩ : syracuseStep 4833341 = 1812503) (by norm_num)
theorem B3222227 : Blo 2147435 3222227 := bstep (se 1 (by rfl) ⟨2416670, by rfl⟩ : syracuseStep 3222227 = 4833341) B4833341
theorem B2148151 : Blo 2147435 2148151 := bstep (se 1 (by rfl) ⟨1611113, by rfl⟩ : syracuseStep 2148151 = 3222227) B3222227
theorem B3625013 : Blo 2147435 3625013 := bbase (se 5 (by rfl) ⟨169922, by rfl⟩ : syracuseStep 3625013 = 339845) (by norm_num)
theorem B2416675 : Blo 2147435 2416675 := bstep (se 1 (by rfl) ⟨1812506, by rfl⟩ : syracuseStep 2416675 = 3625013) B3625013
theorem B3222233 : Blo 2147435 3222233 := bstep (se 2 (by rfl) ⟨1208337, by rfl⟩ : syracuseStep 3222233 = 2416675) B2416675
theorem B2148155 : Blo 2147435 2148155 := bstep (se 1 (by rfl) ⟨1611116, by rfl⟩ : syracuseStep 2148155 = 3222233) B3222233
theorem B6117221 : Blo 2147435 6117221 := bbase (se 4 (by rfl) ⟨573489, by rfl⟩ : syracuseStep 6117221 = 1146979) (by norm_num)
theorem B16312589 : Blo 2147435 16312589 := bstep (se 3 (by rfl) ⟨3058610, by rfl⟩ : syracuseStep 16312589 = 6117221) B6117221
theorem B10875059 : Blo 2147435 10875059 := bstep (se 1 (by rfl) ⟨8156294, by rfl⟩ : syracuseStep 10875059 = 16312589) B16312589
theorem B7250039 : Blo 2147435 7250039 := bstep (se 1 (by rfl) ⟨5437529, by rfl⟩ : syracuseStep 7250039 = 10875059) B10875059
theorem B4833359 : Blo 2147435 4833359 := bstep (se 1 (by rfl) ⟨3625019, by rfl⟩ : syracuseStep 4833359 = 7250039) B7250039
theorem B3222239 : Blo 2147435 3222239 := bstep (se 1 (by rfl) ⟨2416679, by rfl⟩ : syracuseStep 3222239 = 4833359) B4833359
theorem B2148159 : Blo 2147435 2148159 := bstep (se 1 (by rfl) ⟨1611119, by rfl⟩ : syracuseStep 2148159 = 3222239) B3222239
theorem B3222245 : Blo 2147435 3222245 := bbase (se 4 (by rfl) ⟨302085, by rfl⟩ : syracuseStep 3222245 = 604171) (by norm_num)
theorem B2148163 : Blo 2147435 2148163 := bstep (se 1 (by rfl) ⟨1611122, by rfl⟩ : syracuseStep 2148163 = 3222245) B3222245
theorem B4899325 : Blo 2147435 4899325 := bbase (se 3 (by rfl) ⟨918623, by rfl⟩ : syracuseStep 4899325 = 1837247) (by norm_num)
theorem B6532433 : Blo 2147435 6532433 := bstep (se 2 (by rfl) ⟨2449662, by rfl⟩ : syracuseStep 6532433 = 4899325) B4899325
theorem B4354955 : Blo 2147435 4354955 := bstep (se 1 (by rfl) ⟨3266216, by rfl⟩ : syracuseStep 4354955 = 6532433) B6532433
theorem B2903303 : Blo 2147435 2903303 := bstep (se 1 (by rfl) ⟨2177477, by rfl⟩ : syracuseStep 2903303 = 4354955) B4354955
theorem B7742141 : Blo 2147435 7742141 := bstep (se 3 (by rfl) ⟨1451651, by rfl⟩ : syracuseStep 7742141 = 2903303) B2903303
theorem B5161427 : Blo 2147435 5161427 := bstep (se 1 (by rfl) ⟨3871070, by rfl⟩ : syracuseStep 5161427 = 7742141) B7742141
theorem B3440951 : Blo 2147435 3440951 := bstep (se 1 (by rfl) ⟨2580713, by rfl⟩ : syracuseStep 3440951 = 5161427) B5161427
theorem B2293967 : Blo 2147435 2293967 := bstep (se 1 (by rfl) ⟨1720475, by rfl⟩ : syracuseStep 2293967 = 3440951) B3440951
theorem B6117245 : Blo 2147435 6117245 := bstep (se 3 (by rfl) ⟨1146983, by rfl⟩ : syracuseStep 6117245 = 2293967) B2293967
theorem B4078163 : Blo 2147435 4078163 := bstep (se 1 (by rfl) ⟨3058622, by rfl⟩ : syracuseStep 4078163 = 6117245) B6117245
theorem B2718775 : Blo 2147435 2718775 := bstep (se 1 (by rfl) ⟨2039081, by rfl⟩ : syracuseStep 2718775 = 4078163) B4078163
theorem B3625033 : Blo 2147435 3625033 := bstep (se 2 (by rfl) ⟨1359387, by rfl⟩ : syracuseStep 3625033 = 2718775) B2718775
theorem B4833377 : Blo 2147435 4833377 := bstep (se 2 (by rfl) ⟨1812516, by rfl⟩ : syracuseStep 4833377 = 3625033) B3625033
theorem B3222251 : Blo 2147435 3222251 := bstep (se 1 (by rfl) ⟨2416688, by rfl⟩ : syracuseStep 3222251 = 4833377) B4833377
theorem B2148167 : Blo 2147435 2148167 := bstep (se 1 (by rfl) ⟨1611125, by rfl⟩ : syracuseStep 2148167 = 3222251) B3222251
theorem B2416693 : Blo 2147435 2416693 := bbase (se 5 (by rfl) ⟨113282, by rfl⟩ : syracuseStep 2416693 = 226565) (by norm_num)
theorem B3222257 : Blo 2147435 3222257 := bstep (se 2 (by rfl) ⟨1208346, by rfl⟩ : syracuseStep 3222257 = 2416693) B2416693
theorem B2148171 : Blo 2147435 2148171 := bstep (se 1 (by rfl) ⟨1611128, by rfl⟩ : syracuseStep 2148171 = 3222257) B3222257
theorem B2718785 : Blo 2147435 2718785 := bbase (se 2 (by rfl) ⟨1019544, by rfl⟩ : syracuseStep 2718785 = 2039089) (by norm_num)
theorem B7250093 : Blo 2147435 7250093 := bstep (se 3 (by rfl) ⟨1359392, by rfl⟩ : syracuseStep 7250093 = 2718785) B2718785
theorem B4833395 : Blo 2147435 4833395 := bstep (se 1 (by rfl) ⟨3625046, by rfl⟩ : syracuseStep 4833395 = 7250093) B7250093
theorem B3222263 : Blo 2147435 3222263 := bstep (se 1 (by rfl) ⟨2416697, by rfl⟩ : syracuseStep 3222263 = 4833395) B4833395
theorem B2148175 : Blo 2147435 2148175 := bstep (se 1 (by rfl) ⟨1611131, by rfl⟩ : syracuseStep 2148175 = 3222263) B3222263
theorem B3222269 : Blo 2147435 3222269 := bbase (se 3 (by rfl) ⟨604175, by rfl⟩ : syracuseStep 3222269 = 1208351) (by norm_num)
theorem B2148179 : Blo 2147435 2148179 := bstep (se 1 (by rfl) ⟨1611134, by rfl⟩ : syracuseStep 2148179 = 3222269) B3222269
theorem B4833413 : Blo 2147435 4833413 := bbase (se 4 (by rfl) ⟨453132, by rfl⟩ : syracuseStep 4833413 = 906265) (by norm_num)
theorem B3222275 : Blo 2147435 3222275 := bstep (se 1 (by rfl) ⟨2416706, by rfl⟩ : syracuseStep 3222275 = 4833413) B4833413
theorem B2148183 : Blo 2147435 2148183 := bstep (se 1 (by rfl) ⟨1611137, by rfl⟩ : syracuseStep 2148183 = 3222275) B3222275
theorem B7742213 : Blo 2147435 7742213 := bbase (se 4 (by rfl) ⟨725832, by rfl⟩ : syracuseStep 7742213 = 1451665) (by norm_num)
theorem B5161475 : Blo 2147435 5161475 := bstep (se 1 (by rfl) ⟨3871106, by rfl⟩ : syracuseStep 5161475 = 7742213) B7742213
theorem B3440983 : Blo 2147435 3440983 := bstep (se 1 (by rfl) ⟨2580737, by rfl⟩ : syracuseStep 3440983 = 5161475) B5161475
theorem B4587977 : Blo 2147435 4587977 := bstep (se 2 (by rfl) ⟨1720491, by rfl⟩ : syracuseStep 4587977 = 3440983) B3440983
theorem B3058651 : Blo 2147435 3058651 := bstep (se 1 (by rfl) ⟨2293988, by rfl⟩ : syracuseStep 3058651 = 4587977) B4587977
theorem B4078201 : Blo 2147435 4078201 := bstep (se 2 (by rfl) ⟨1529325, by rfl⟩ : syracuseStep 4078201 = 3058651) B3058651
theorem B5437601 : Blo 2147435 5437601 := bstep (se 2 (by rfl) ⟨2039100, by rfl⟩ : syracuseStep 5437601 = 4078201) B4078201
theorem B3625067 : Blo 2147435 3625067 := bstep (se 1 (by rfl) ⟨2718800, by rfl⟩ : syracuseStep 3625067 = 5437601) B5437601
theorem B2416711 : Blo 2147435 2416711 := bstep (se 1 (by rfl) ⟨1812533, by rfl⟩ : syracuseStep 2416711 = 3625067) B3625067
theorem B3222281 : Blo 2147435 3222281 := bstep (se 2 (by rfl) ⟨1208355, by rfl⟩ : syracuseStep 3222281 = 2416711) B2416711
theorem B2148187 : Blo 2147435 2148187 := bstep (se 1 (by rfl) ⟨1611140, by rfl⟩ : syracuseStep 2148187 = 3222281) B3222281
theorem B10875221 : Blo 2147435 10875221 := bbase (se 10 (by rfl) ⟨15930, by rfl⟩ : syracuseStep 10875221 = 31861) (by norm_num)
theorem B7250147 : Blo 2147435 7250147 := bstep (se 1 (by rfl) ⟨5437610, by rfl⟩ : syracuseStep 7250147 = 10875221) B10875221
theorem B4833431 : Blo 2147435 4833431 := bstep (se 1 (by rfl) ⟨3625073, by rfl⟩ : syracuseStep 4833431 = 7250147) B7250147
theorem B3222287 : Blo 2147435 3222287 := bstep (se 1 (by rfl) ⟨2416715, by rfl⟩ : syracuseStep 3222287 = 4833431) B4833431
theorem B2148191 : Blo 2147435 2148191 := bstep (se 1 (by rfl) ⟨1611143, by rfl⟩ : syracuseStep 2148191 = 3222287) B3222287
theorem B3222293 : Blo 2147435 3222293 := bbase (se 6 (by rfl) ⟨75522, by rfl⟩ : syracuseStep 3222293 = 151045) (by norm_num)
theorem B2148195 : Blo 2147435 2148195 := bstep (se 1 (by rfl) ⟨1611146, by rfl⟩ : syracuseStep 2148195 = 3222293) B3222293
theorem B2177509 : Blo 2147435 2177509 := bbase (se 4 (by rfl) ⟨204141, by rfl⟩ : syracuseStep 2177509 = 408283) (by norm_num)
theorem B2903345 : Blo 2147435 2903345 := bstep (se 2 (by rfl) ⟨1088754, by rfl⟩ : syracuseStep 2903345 = 2177509) B2177509
theorem B30969013 : Blo 2147435 30969013 := bstep (se 5 (by rfl) ⟨1451672, by rfl⟩ : syracuseStep 30969013 = 2903345) B2903345
theorem B41292017 : Blo 2147435 41292017 := bstep (se 2 (by rfl) ⟨15484506, by rfl⟩ : syracuseStep 41292017 = 30969013) B30969013
theorem B27528011 : Blo 2147435 27528011 := bstep (se 1 (by rfl) ⟨20646008, by rfl⟩ : syracuseStep 27528011 = 41292017) B41292017
theorem B18352007 : Blo 2147435 18352007 := bstep (se 1 (by rfl) ⟨13764005, by rfl⟩ : syracuseStep 18352007 = 27528011) B27528011
theorem B12234671 : Blo 2147435 12234671 := bstep (se 1 (by rfl) ⟨9176003, by rfl⟩ : syracuseStep 12234671 = 18352007) B18352007
theorem B8156447 : Blo 2147435 8156447 := bstep (se 1 (by rfl) ⟨6117335, by rfl⟩ : syracuseStep 8156447 = 12234671) B12234671
theorem B5437631 : Blo 2147435 5437631 := bstep (se 1 (by rfl) ⟨4078223, by rfl⟩ : syracuseStep 5437631 = 8156447) B8156447
theorem B3625087 : Blo 2147435 3625087 := bstep (se 1 (by rfl) ⟨2718815, by rfl⟩ : syracuseStep 3625087 = 5437631) B5437631
theorem B4833449 : Blo 2147435 4833449 := bstep (se 2 (by rfl) ⟨1812543, by rfl⟩ : syracuseStep 4833449 = 3625087) B3625087
theorem B3222299 : Blo 2147435 3222299 := bstep (se 1 (by rfl) ⟨2416724, by rfl⟩ : syracuseStep 3222299 = 4833449) B4833449
theorem B2148199 : Blo 2147435 2148199 := bstep (se 1 (by rfl) ⟨1611149, by rfl⟩ : syracuseStep 2148199 = 3222299) B3222299
theorem B2416729 : Blo 2147435 2416729 := bbase (se 2 (by rfl) ⟨906273, by rfl⟩ : syracuseStep 2416729 = 1812547) (by norm_num)
theorem B3222305 : Blo 2147435 3222305 := bstep (se 2 (by rfl) ⟨1208364, by rfl⟩ : syracuseStep 3222305 = 2416729) B2416729
theorem B2148203 : Blo 2147435 2148203 := bstep (se 1 (by rfl) ⟨1611152, by rfl⟩ : syracuseStep 2148203 = 3222305) B3222305
theorem B2580761 : Blo 2147435 2580761 := bbase (se 2 (by rfl) ⟨967785, by rfl⟩ : syracuseStep 2580761 = 1935571) (by norm_num)
theorem B6882029 : Blo 2147435 6882029 := bstep (se 3 (by rfl) ⟨1290380, by rfl⟩ : syracuseStep 6882029 = 2580761) B2580761
theorem B4588019 : Blo 2147435 4588019 := bstep (se 1 (by rfl) ⟨3441014, by rfl⟩ : syracuseStep 4588019 = 6882029) B6882029
theorem B3058679 : Blo 2147435 3058679 := bstep (se 1 (by rfl) ⟨2294009, by rfl⟩ : syracuseStep 3058679 = 4588019) B4588019
theorem B8156477 : Blo 2147435 8156477 := bstep (se 3 (by rfl) ⟨1529339, by rfl⟩ : syracuseStep 8156477 = 3058679) B3058679
theorem B5437651 : Blo 2147435 5437651 := bstep (se 1 (by rfl) ⟨4078238, by rfl⟩ : syracuseStep 5437651 = 8156477) B8156477
theorem B7250201 : Blo 2147435 7250201 := bstep (se 2 (by rfl) ⟨2718825, by rfl⟩ : syracuseStep 7250201 = 5437651) B5437651
theorem B4833467 : Blo 2147435 4833467 := bstep (se 1 (by rfl) ⟨3625100, by rfl⟩ : syracuseStep 4833467 = 7250201) B7250201
theorem B3222311 : Blo 2147435 3222311 := bstep (se 1 (by rfl) ⟨2416733, by rfl⟩ : syracuseStep 3222311 = 4833467) B4833467
theorem B2148207 : Blo 2147435 2148207 := bstep (se 1 (by rfl) ⟨1611155, by rfl⟩ : syracuseStep 2148207 = 3222311) B3222311
theorem B3222317 : Blo 2147435 3222317 := bbase (se 3 (by rfl) ⟨604184, by rfl⟩ : syracuseStep 3222317 = 1208369) (by norm_num)
theorem B2148211 : Blo 2147435 2148211 := bstep (se 1 (by rfl) ⟨1611158, by rfl⟩ : syracuseStep 2148211 = 3222317) B3222317
theorem B4833485 : Blo 2147435 4833485 := bbase (se 3 (by rfl) ⟨906278, by rfl⟩ : syracuseStep 4833485 = 1812557) (by norm_num)
theorem B3222323 : Blo 2147435 3222323 := bstep (se 1 (by rfl) ⟨2416742, by rfl⟩ : syracuseStep 3222323 = 4833485) B4833485
theorem B2148215 : Blo 2147435 2148215 := bstep (se 1 (by rfl) ⟨1611161, by rfl⟩ : syracuseStep 2148215 = 3222323) B3222323
theorem B2718841 : Blo 2147435 2718841 := bbase (se 2 (by rfl) ⟨1019565, by rfl⟩ : syracuseStep 2718841 = 2039131) (by norm_num)
theorem B3625121 : Blo 2147435 3625121 := bstep (se 2 (by rfl) ⟨1359420, by rfl⟩ : syracuseStep 3625121 = 2718841) B2718841
theorem B2416747 : Blo 2147435 2416747 := bstep (se 1 (by rfl) ⟨1812560, by rfl⟩ : syracuseStep 2416747 = 3625121) B3625121
theorem B3222329 : Blo 2147435 3222329 := bstep (se 2 (by rfl) ⟨1208373, by rfl⟩ : syracuseStep 3222329 = 2416747) B2416747
theorem B2148219 : Blo 2147435 2148219 := bstep (se 1 (by rfl) ⟨1611164, by rfl⟩ : syracuseStep 2148219 = 3222329) B3222329
theorem B9301301 : Blo 2147435 9301301 := bbase (se 5 (by rfl) ⟨435998, by rfl⟩ : syracuseStep 9301301 = 871997) (by norm_num)
theorem B6200867 : Blo 2147435 6200867 := bstep (se 1 (by rfl) ⟨4650650, by rfl⟩ : syracuseStep 6200867 = 9301301) B9301301
theorem B4133911 : Blo 2147435 4133911 := bstep (se 1 (by rfl) ⟨3100433, by rfl⟩ : syracuseStep 4133911 = 6200867) B6200867
theorem B5511881 : Blo 2147435 5511881 := bstep (se 2 (by rfl) ⟨2066955, by rfl⟩ : syracuseStep 5511881 = 4133911) B4133911
theorem B14698349 : Blo 2147435 14698349 := bstep (se 3 (by rfl) ⟨2755940, by rfl⟩ : syracuseStep 14698349 = 5511881) B5511881
theorem B9798899 : Blo 2147435 9798899 := bstep (se 1 (by rfl) ⟨7349174, by rfl⟩ : syracuseStep 9798899 = 14698349) B14698349
theorem B26130397 : Blo 2147435 26130397 := bstep (se 3 (by rfl) ⟨4899449, by rfl⟩ : syracuseStep 26130397 = 9798899) B9798899
theorem B34840529 : Blo 2147435 34840529 := bstep (se 2 (by rfl) ⟨13065198, by rfl⟩ : syracuseStep 34840529 = 26130397) B26130397
theorem B23227019 : Blo 2147435 23227019 := bstep (se 1 (by rfl) ⟨17420264, by rfl⟩ : syracuseStep 23227019 = 34840529) B34840529
theorem B15484679 : Blo 2147435 15484679 := bstep (se 1 (by rfl) ⟨11613509, by rfl⟩ : syracuseStep 15484679 = 23227019) B23227019
theorem B10323119 : Blo 2147435 10323119 := bstep (se 1 (by rfl) ⟨7742339, by rfl⟩ : syracuseStep 10323119 = 15484679) B15484679
theorem B6882079 : Blo 2147435 6882079 := bstep (se 1 (by rfl) ⟨5161559, by rfl⟩ : syracuseStep 6882079 = 10323119) B10323119
theorem B9176105 : Blo 2147435 9176105 := bstep (se 2 (by rfl) ⟨3441039, by rfl⟩ : syracuseStep 9176105 = 6882079) B6882079
theorem B24469613 : Blo 2147435 24469613 := bstep (se 3 (by rfl) ⟨4588052, by rfl⟩ : syracuseStep 24469613 = 9176105) B9176105
theorem B16313075 : Blo 2147435 16313075 := bstep (se 1 (by rfl) ⟨12234806, by rfl⟩ : syracuseStep 16313075 = 24469613) B24469613
theorem B10875383 : Blo 2147435 10875383 := bstep (se 1 (by rfl) ⟨8156537, by rfl⟩ : syracuseStep 10875383 = 16313075) B16313075
theorem B7250255 : Blo 2147435 7250255 := bstep (se 1 (by rfl) ⟨5437691, by rfl⟩ : syracuseStep 7250255 = 10875383) B10875383
theorem B4833503 : Blo 2147435 4833503 := bstep (se 1 (by rfl) ⟨3625127, by rfl⟩ : syracuseStep 4833503 = 7250255) B7250255
theorem B3222335 : Blo 2147435 3222335 := bstep (se 1 (by rfl) ⟨2416751, by rfl⟩ : syracuseStep 3222335 = 4833503) B4833503
theorem B2148223 : Blo 2147435 2148223 := bstep (se 1 (by rfl) ⟨1611167, by rfl⟩ : syracuseStep 2148223 = 3222335) B3222335
theorem B3222341 : Blo 2147435 3222341 := bbase (se 4 (by rfl) ⟨302094, by rfl⟩ : syracuseStep 3222341 = 604189) (by norm_num)
theorem B2148227 : Blo 2147435 2148227 := bstep (se 1 (by rfl) ⟨1611170, by rfl⟩ : syracuseStep 2148227 = 3222341) B3222341
theorem B3625141 : Blo 2147435 3625141 := bbase (se 5 (by rfl) ⟨169928, by rfl⟩ : syracuseStep 3625141 = 339857) (by norm_num)
theorem B4833521 : Blo 2147435 4833521 := bstep (se 2 (by rfl) ⟨1812570, by rfl⟩ : syracuseStep 4833521 = 3625141) B3625141
theorem B3222347 : Blo 2147435 3222347 := bstep (se 1 (by rfl) ⟨2416760, by rfl⟩ : syracuseStep 3222347 = 4833521) B4833521
theorem B2148231 : Blo 2147435 2148231 := bstep (se 1 (by rfl) ⟨1611173, by rfl⟩ : syracuseStep 2148231 = 3222347) B3222347
theorem B2416765 : Blo 2147435 2416765 := bbase (se 3 (by rfl) ⟨453143, by rfl⟩ : syracuseStep 2416765 = 906287) (by norm_num)
theorem B3222353 : Blo 2147435 3222353 := bstep (se 2 (by rfl) ⟨1208382, by rfl⟩ : syracuseStep 3222353 = 2416765) B2416765
theorem B2148235 : Blo 2147435 2148235 := bstep (se 1 (by rfl) ⟨1611176, by rfl⟩ : syracuseStep 2148235 = 3222353) B3222353
theorem B7250309 : Blo 2147435 7250309 := bbase (se 4 (by rfl) ⟨679716, by rfl⟩ : syracuseStep 7250309 = 1359433) (by norm_num)
theorem B4833539 : Blo 2147435 4833539 := bstep (se 1 (by rfl) ⟨3625154, by rfl⟩ : syracuseStep 4833539 = 7250309) B7250309
theorem B3222359 : Blo 2147435 3222359 := bstep (se 1 (by rfl) ⟨2416769, by rfl⟩ : syracuseStep 3222359 = 4833539) B4833539
theorem B2148239 : Blo 2147435 2148239 := bstep (se 1 (by rfl) ⟨1611179, by rfl⟩ : syracuseStep 2148239 = 3222359) B3222359
theorem B3222365 : Blo 2147435 3222365 := bbase (se 3 (by rfl) ⟨604193, by rfl⟩ : syracuseStep 3222365 = 1208387) (by norm_num)
theorem B2148243 : Blo 2147435 2148243 := bstep (se 1 (by rfl) ⟨1611182, by rfl⟩ : syracuseStep 2148243 = 3222365) B3222365
theorem B4833557 : Blo 2147435 4833557 := bbase (se 6 (by rfl) ⟨113286, by rfl⟩ : syracuseStep 4833557 = 226573) (by norm_num)
theorem B3222371 : Blo 2147435 3222371 := bstep (se 1 (by rfl) ⟨2416778, by rfl⟩ : syracuseStep 3222371 = 4833557) B4833557
theorem B2148247 : Blo 2147435 2148247 := bstep (se 1 (by rfl) ⟨1611185, by rfl⟩ : syracuseStep 2148247 = 3222371) B3222371
theorem B8156645 : Blo 2147435 8156645 := bbase (se 4 (by rfl) ⟨764685, by rfl⟩ : syracuseStep 8156645 = 1529371) (by norm_num)
theorem B5437763 : Blo 2147435 5437763 := bstep (se 1 (by rfl) ⟨4078322, by rfl⟩ : syracuseStep 5437763 = 8156645) B8156645
theorem B3625175 : Blo 2147435 3625175 := bstep (se 1 (by rfl) ⟨2718881, by rfl⟩ : syracuseStep 3625175 = 5437763) B5437763
theorem B2416783 : Blo 2147435 2416783 := bstep (se 1 (by rfl) ⟨1812587, by rfl⟩ : syracuseStep 2416783 = 3625175) B3625175
theorem B3222377 : Blo 2147435 3222377 := bstep (se 2 (by rfl) ⟨1208391, by rfl⟩ : syracuseStep 3222377 = 2416783) B2416783
theorem B2148251 : Blo 2147435 2148251 := bstep (se 1 (by rfl) ⟨1611188, by rfl⟩ : syracuseStep 2148251 = 3222377) B3222377
theorem B5161637 : Blo 2147435 5161637 := bbase (se 4 (by rfl) ⟨483903, by rfl⟩ : syracuseStep 5161637 = 967807) (by norm_num)
theorem B3441091 : Blo 2147435 3441091 := bstep (se 1 (by rfl) ⟨2580818, by rfl⟩ : syracuseStep 3441091 = 5161637) B5161637
theorem B4588121 : Blo 2147435 4588121 := bstep (se 2 (by rfl) ⟨1720545, by rfl⟩ : syracuseStep 4588121 = 3441091) B3441091
theorem B12234989 : Blo 2147435 12234989 := bstep (se 3 (by rfl) ⟨2294060, by rfl⟩ : syracuseStep 12234989 = 4588121) B4588121
theorem B8156659 : Blo 2147435 8156659 := bstep (se 1 (by rfl) ⟨6117494, by rfl⟩ : syracuseStep 8156659 = 12234989) B12234989
theorem B10875545 : Blo 2147435 10875545 := bstep (se 2 (by rfl) ⟨4078329, by rfl⟩ : syracuseStep 10875545 = 8156659) B8156659
theorem B7250363 : Blo 2147435 7250363 := bstep (se 1 (by rfl) ⟨5437772, by rfl⟩ : syracuseStep 7250363 = 10875545) B10875545
theorem B4833575 : Blo 2147435 4833575 := bstep (se 1 (by rfl) ⟨3625181, by rfl⟩ : syracuseStep 4833575 = 7250363) B7250363
theorem B3222383 : Blo 2147435 3222383 := bstep (se 1 (by rfl) ⟨2416787, by rfl⟩ : syracuseStep 3222383 = 4833575) B4833575
theorem B2148255 : Blo 2147435 2148255 := bstep (se 1 (by rfl) ⟨1611191, by rfl⟩ : syracuseStep 2148255 = 3222383) B3222383
theorem B3222389 : Blo 2147435 3222389 := bbase (se 5 (by rfl) ⟨151049, by rfl⟩ : syracuseStep 3222389 = 302099) (by norm_num)
theorem B2148259 : Blo 2147435 2148259 := bstep (se 1 (by rfl) ⟨1611194, by rfl⟩ : syracuseStep 2148259 = 3222389) B3222389
theorem B4355149 : Blo 2147435 4355149 := bbase (se 3 (by rfl) ⟨816590, by rfl⟩ : syracuseStep 4355149 = 1633181) (by norm_num)
theorem B5806865 : Blo 2147435 5806865 := bstep (se 2 (by rfl) ⟨2177574, by rfl⟩ : syracuseStep 5806865 = 4355149) B4355149
theorem B3871243 : Blo 2147435 3871243 := bstep (se 1 (by rfl) ⟨2903432, by rfl⟩ : syracuseStep 3871243 = 5806865) B5806865
theorem B5161657 : Blo 2147435 5161657 := bstep (se 2 (by rfl) ⟨1935621, by rfl⟩ : syracuseStep 5161657 = 3871243) B3871243
theorem B6882209 : Blo 2147435 6882209 := bstep (se 2 (by rfl) ⟨2580828, by rfl⟩ : syracuseStep 6882209 = 5161657) B5161657
theorem B4588139 : Blo 2147435 4588139 := bstep (se 1 (by rfl) ⟨3441104, by rfl⟩ : syracuseStep 4588139 = 6882209) B6882209
theorem B3058759 : Blo 2147435 3058759 := bstep (se 1 (by rfl) ⟨2294069, by rfl⟩ : syracuseStep 3058759 = 4588139) B4588139
theorem B4078345 : Blo 2147435 4078345 := bstep (se 2 (by rfl) ⟨1529379, by rfl⟩ : syracuseStep 4078345 = 3058759) B3058759
theorem B5437793 : Blo 2147435 5437793 := bstep (se 2 (by rfl) ⟨2039172, by rfl⟩ : syracuseStep 5437793 = 4078345) B4078345
theorem B3625195 : Blo 2147435 3625195 := bstep (se 1 (by rfl) ⟨2718896, by rfl⟩ : syracuseStep 3625195 = 5437793) B5437793
theorem B4833593 : Blo 2147435 4833593 := bstep (se 2 (by rfl) ⟨1812597, by rfl⟩ : syracuseStep 4833593 = 3625195) B3625195
theorem B3222395 : Blo 2147435 3222395 := bstep (se 1 (by rfl) ⟨2416796, by rfl⟩ : syracuseStep 3222395 = 4833593) B4833593
theorem B2148263 : Blo 2147435 2148263 := bstep (se 1 (by rfl) ⟨1611197, by rfl⟩ : syracuseStep 2148263 = 3222395) B3222395
theorem B2416801 : Blo 2147435 2416801 := bbase (se 2 (by rfl) ⟨906300, by rfl⟩ : syracuseStep 2416801 = 1812601) (by norm_num)
theorem B3222401 : Blo 2147435 3222401 := bstep (se 2 (by rfl) ⟨1208400, by rfl⟩ : syracuseStep 3222401 = 2416801) B2416801
theorem B2148267 : Blo 2147435 2148267 := bstep (se 1 (by rfl) ⟨1611200, by rfl⟩ : syracuseStep 2148267 = 3222401) B3222401
theorem B5437813 : Blo 2147435 5437813 := bbase (se 5 (by rfl) ⟨254897, by rfl⟩ : syracuseStep 5437813 = 509795) (by norm_num)
theorem B7250417 : Blo 2147435 7250417 := bstep (se 2 (by rfl) ⟨2718906, by rfl⟩ : syracuseStep 7250417 = 5437813) B5437813
theorem B4833611 : Blo 2147435 4833611 := bstep (se 1 (by rfl) ⟨3625208, by rfl⟩ : syracuseStep 4833611 = 7250417) B7250417
theorem B3222407 : Blo 2147435 3222407 := bstep (se 1 (by rfl) ⟨2416805, by rfl⟩ : syracuseStep 3222407 = 4833611) B4833611
theorem B2148271 : Blo 2147435 2148271 := bstep (se 1 (by rfl) ⟨1611203, by rfl⟩ : syracuseStep 2148271 = 3222407) B3222407
theorem B3222413 : Blo 2147435 3222413 := bbase (se 3 (by rfl) ⟨604202, by rfl⟩ : syracuseStep 3222413 = 1208405) (by norm_num)
theorem B2148275 : Blo 2147435 2148275 := bstep (se 1 (by rfl) ⟨1611206, by rfl⟩ : syracuseStep 2148275 = 3222413) B3222413
theorem B4833629 : Blo 2147435 4833629 := bbase (se 3 (by rfl) ⟨906305, by rfl⟩ : syracuseStep 4833629 = 1812611) (by norm_num)
theorem B3222419 : Blo 2147435 3222419 := bstep (se 1 (by rfl) ⟨2416814, by rfl⟩ : syracuseStep 3222419 = 4833629) B4833629
theorem B2148279 : Blo 2147435 2148279 := bstep (se 1 (by rfl) ⟨1611209, by rfl⟩ : syracuseStep 2148279 = 3222419) B3222419
theorem B3625229 : Blo 2147435 3625229 := bbase (se 3 (by rfl) ⟨679730, by rfl⟩ : syracuseStep 3625229 = 1359461) (by norm_num)
theorem B2416819 : Blo 2147435 2416819 := bstep (se 1 (by rfl) ⟨1812614, by rfl⟩ : syracuseStep 2416819 = 3625229) B3625229
theorem B3222425 : Blo 2147435 3222425 := bstep (se 2 (by rfl) ⟨1208409, by rfl⟩ : syracuseStep 3222425 = 2416819) B2416819
theorem B2148283 : Blo 2147435 2148283 := bstep (se 1 (by rfl) ⟨1611212, by rfl⟩ : syracuseStep 2148283 = 3222425) B3222425
theorem B18352757 : Blo 2147435 18352757 := bbase (se 5 (by rfl) ⟨860285, by rfl⟩ : syracuseStep 18352757 = 1720571) (by norm_num)
theorem B12235171 : Blo 2147435 12235171 := bstep (se 1 (by rfl) ⟨9176378, by rfl⟩ : syracuseStep 12235171 = 18352757) B18352757
theorem B16313561 : Blo 2147435 16313561 := bstep (se 2 (by rfl) ⟨6117585, by rfl⟩ : syracuseStep 16313561 = 12235171) B12235171
theorem B10875707 : Blo 2147435 10875707 := bstep (se 1 (by rfl) ⟨8156780, by rfl⟩ : syracuseStep 10875707 = 16313561) B16313561
theorem B7250471 : Blo 2147435 7250471 := bstep (se 1 (by rfl) ⟨5437853, by rfl⟩ : syracuseStep 7250471 = 10875707) B10875707
theorem B4833647 : Blo 2147435 4833647 := bstep (se 1 (by rfl) ⟨3625235, by rfl⟩ : syracuseStep 4833647 = 7250471) B7250471
theorem B3222431 : Blo 2147435 3222431 := bstep (se 1 (by rfl) ⟨2416823, by rfl⟩ : syracuseStep 3222431 = 4833647) B4833647
theorem B2148287 : Blo 2147435 2148287 := bstep (se 1 (by rfl) ⟨1611215, by rfl⟩ : syracuseStep 2148287 = 3222431) B3222431
theorem B3222437 : Blo 2147435 3222437 := bbase (se 4 (by rfl) ⟨302103, by rfl⟩ : syracuseStep 3222437 = 604207) (by norm_num)
theorem B2148291 : Blo 2147435 2148291 := bstep (se 1 (by rfl) ⟨1611218, by rfl⟩ : syracuseStep 2148291 = 3222437) B3222437
theorem B2718937 : Blo 2147435 2718937 := bbase (se 2 (by rfl) ⟨1019601, by rfl⟩ : syracuseStep 2718937 = 2039203) (by norm_num)
theorem B3625249 : Blo 2147435 3625249 := bstep (se 2 (by rfl) ⟨1359468, by rfl⟩ : syracuseStep 3625249 = 2718937) B2718937
theorem B4833665 : Blo 2147435 4833665 := bstep (se 2 (by rfl) ⟨1812624, by rfl⟩ : syracuseStep 4833665 = 3625249) B3625249
theorem B3222443 : Blo 2147435 3222443 := bstep (se 1 (by rfl) ⟨2416832, by rfl⟩ : syracuseStep 3222443 = 4833665) B4833665
theorem B2148295 : Blo 2147435 2148295 := bstep (se 1 (by rfl) ⟨1611221, by rfl⟩ : syracuseStep 2148295 = 3222443) B3222443
theorem B2416837 : Blo 2147435 2416837 := bbase (se 4 (by rfl) ⟨226578, by rfl⟩ : syracuseStep 2416837 = 453157) (by norm_num)
theorem B3222449 : Blo 2147435 3222449 := bstep (se 2 (by rfl) ⟨1208418, by rfl⟩ : syracuseStep 3222449 = 2416837) B2416837
theorem B2148299 : Blo 2147435 2148299 := bstep (se 1 (by rfl) ⟨1611224, by rfl⟩ : syracuseStep 2148299 = 3222449) B3222449
theorem B4078421 : Blo 2147435 4078421 := bbase (se 9 (by rfl) ⟨11948, by rfl⟩ : syracuseStep 4078421 = 23897) (by norm_num)
theorem B2718947 : Blo 2147435 2718947 := bstep (se 1 (by rfl) ⟨2039210, by rfl⟩ : syracuseStep 2718947 = 4078421) B4078421
theorem B7250525 : Blo 2147435 7250525 := bstep (se 3 (by rfl) ⟨1359473, by rfl⟩ : syracuseStep 7250525 = 2718947) B2718947
theorem B4833683 : Blo 2147435 4833683 := bstep (se 1 (by rfl) ⟨3625262, by rfl⟩ : syracuseStep 4833683 = 7250525) B7250525
theorem B3222455 : Blo 2147435 3222455 := bstep (se 1 (by rfl) ⟨2416841, by rfl⟩ : syracuseStep 3222455 = 4833683) B4833683
theorem B2148303 : Blo 2147435 2148303 := bstep (se 1 (by rfl) ⟨1611227, by rfl⟩ : syracuseStep 2148303 = 3222455) B3222455
theorem B3222461 : Blo 2147435 3222461 := bbase (se 3 (by rfl) ⟨604211, by rfl⟩ : syracuseStep 3222461 = 1208423) (by norm_num)
theorem B2148307 : Blo 2147435 2148307 := bstep (se 1 (by rfl) ⟨1611230, by rfl⟩ : syracuseStep 2148307 = 3222461) B3222461
theorem B4833701 : Blo 2147435 4833701 := bbase (se 4 (by rfl) ⟨453159, by rfl⟩ : syracuseStep 4833701 = 906319) (by norm_num)
theorem B3222467 : Blo 2147435 3222467 := bstep (se 1 (by rfl) ⟨2416850, by rfl⟩ : syracuseStep 3222467 = 4833701) B4833701
theorem B2148311 : Blo 2147435 2148311 := bstep (se 1 (by rfl) ⟨1611233, by rfl⟩ : syracuseStep 2148311 = 3222467) B3222467
theorem B5437925 : Blo 2147435 5437925 := bbase (se 4 (by rfl) ⟨509805, by rfl⟩ : syracuseStep 5437925 = 1019611) (by norm_num)
theorem B3625283 : Blo 2147435 3625283 := bstep (se 1 (by rfl) ⟨2718962, by rfl⟩ : syracuseStep 3625283 = 5437925) B5437925
theorem B2416855 : Blo 2147435 2416855 := bstep (se 1 (by rfl) ⟨1812641, by rfl⟩ : syracuseStep 2416855 = 3625283) B3625283
theorem B3222473 : Blo 2147435 3222473 := bstep (se 2 (by rfl) ⟨1208427, by rfl⟩ : syracuseStep 3222473 = 2416855) B2416855
theorem B2148315 : Blo 2147435 2148315 := bstep (se 1 (by rfl) ⟨1611236, by rfl⟩ : syracuseStep 2148315 = 3222473) B3222473
theorem B2294129 : Blo 2147435 2294129 := bbase (se 2 (by rfl) ⟨860298, by rfl⟩ : syracuseStep 2294129 = 1720597) (by norm_num)
theorem B6117677 : Blo 2147435 6117677 := bstep (se 3 (by rfl) ⟨1147064, by rfl⟩ : syracuseStep 6117677 = 2294129) B2294129
theorem B4078451 : Blo 2147435 4078451 := bstep (se 1 (by rfl) ⟨3058838, by rfl⟩ : syracuseStep 4078451 = 6117677) B6117677
theorem B10875869 : Blo 2147435 10875869 := bstep (se 3 (by rfl) ⟨2039225, by rfl⟩ : syracuseStep 10875869 = 4078451) B4078451
theorem B7250579 : Blo 2147435 7250579 := bstep (se 1 (by rfl) ⟨5437934, by rfl⟩ : syracuseStep 7250579 = 10875869) B10875869
theorem B4833719 : Blo 2147435 4833719 := bstep (se 1 (by rfl) ⟨3625289, by rfl⟩ : syracuseStep 4833719 = 7250579) B7250579
theorem B3222479 : Blo 2147435 3222479 := bstep (se 1 (by rfl) ⟨2416859, by rfl⟩ : syracuseStep 3222479 = 4833719) B4833719
theorem B2148319 : Blo 2147435 2148319 := bstep (se 1 (by rfl) ⟨1611239, by rfl⟩ : syracuseStep 2148319 = 3222479) B3222479
theorem B3222485 : Blo 2147435 3222485 := bbase (se 7 (by rfl) ⟨37763, by rfl⟩ : syracuseStep 3222485 = 75527) (by norm_num)
theorem B2148323 : Blo 2147435 2148323 := bstep (se 1 (by rfl) ⟨1611242, by rfl⟩ : syracuseStep 2148323 = 3222485) B3222485
theorem B8156933 : Blo 2147435 8156933 := bbase (se 4 (by rfl) ⟨764712, by rfl⟩ : syracuseStep 8156933 = 1529425) (by norm_num)
theorem B5437955 : Blo 2147435 5437955 := bstep (se 1 (by rfl) ⟨4078466, by rfl⟩ : syracuseStep 5437955 = 8156933) B8156933
theorem B3625303 : Blo 2147435 3625303 := bstep (se 1 (by rfl) ⟨2718977, by rfl⟩ : syracuseStep 3625303 = 5437955) B5437955
theorem B4833737 : Blo 2147435 4833737 := bstep (se 2 (by rfl) ⟨1812651, by rfl⟩ : syracuseStep 4833737 = 3625303) B3625303
theorem B3222491 : Blo 2147435 3222491 := bstep (se 1 (by rfl) ⟨2416868, by rfl⟩ : syracuseStep 3222491 = 4833737) B4833737
theorem B2148327 : Blo 2147435 2148327 := bstep (se 1 (by rfl) ⟨1611245, by rfl⟩ : syracuseStep 2148327 = 3222491) B3222491
theorem B2416873 : Blo 2147435 2416873 := bbase (se 2 (by rfl) ⟨906327, by rfl⟩ : syracuseStep 2416873 = 1812655) (by norm_num)
theorem B3222497 : Blo 2147435 3222497 := bstep (se 2 (by rfl) ⟨1208436, by rfl⟩ : syracuseStep 3222497 = 2416873) B2416873
theorem B2148331 : Blo 2147435 2148331 := bstep (se 1 (by rfl) ⟨1611248, by rfl⟩ : syracuseStep 2148331 = 3222497) B3222497
theorem B12235445 : Blo 2147435 12235445 := bbase (se 5 (by rfl) ⟨573536, by rfl⟩ : syracuseStep 12235445 = 1147073) (by norm_num)
theorem B8156963 : Blo 2147435 8156963 := bstep (se 1 (by rfl) ⟨6117722, by rfl⟩ : syracuseStep 8156963 = 12235445) B12235445
theorem B5437975 : Blo 2147435 5437975 := bstep (se 1 (by rfl) ⟨4078481, by rfl⟩ : syracuseStep 5437975 = 8156963) B8156963
theorem B7250633 : Blo 2147435 7250633 := bstep (se 2 (by rfl) ⟨2718987, by rfl⟩ : syracuseStep 7250633 = 5437975) B5437975
theorem B4833755 : Blo 2147435 4833755 := bstep (se 1 (by rfl) ⟨3625316, by rfl⟩ : syracuseStep 4833755 = 7250633) B7250633
theorem B3222503 : Blo 2147435 3222503 := bstep (se 1 (by rfl) ⟨2416877, by rfl⟩ : syracuseStep 3222503 = 4833755) B4833755
theorem B2148335 : Blo 2147435 2148335 := bstep (se 1 (by rfl) ⟨1611251, by rfl⟩ : syracuseStep 2148335 = 3222503) B3222503
theorem B3222509 : Blo 2147435 3222509 := bbase (se 3 (by rfl) ⟨604220, by rfl⟩ : syracuseStep 3222509 = 1208441) (by norm_num)
theorem B2148339 : Blo 2147435 2148339 := bstep (se 1 (by rfl) ⟨1611254, by rfl⟩ : syracuseStep 2148339 = 3222509) B3222509
theorem B4833773 : Blo 2147435 4833773 := bbase (se 3 (by rfl) ⟨906332, by rfl⟩ : syracuseStep 4833773 = 1812665) (by norm_num)
theorem B3222515 : Blo 2147435 3222515 := bstep (se 1 (by rfl) ⟨2416886, by rfl⟩ : syracuseStep 3222515 = 4833773) B4833773
theorem B2148343 : Blo 2147435 2148343 := bstep (se 1 (by rfl) ⟨1611257, by rfl⟩ : syracuseStep 2148343 = 3222515) B3222515
theorem B2756101 : Blo 2147435 2756101 := bbase (se 4 (by rfl) ⟨258384, by rfl⟩ : syracuseStep 2756101 = 516769) (by norm_num)
theorem B3674801 : Blo 2147435 3674801 := bstep (se 2 (by rfl) ⟨1378050, by rfl⟩ : syracuseStep 3674801 = 2756101) B2756101
theorem B9799469 : Blo 2147435 9799469 := bstep (se 3 (by rfl) ⟨1837400, by rfl⟩ : syracuseStep 9799469 = 3674801) B3674801
theorem B6532979 : Blo 2147435 6532979 := bstep (se 1 (by rfl) ⟨4899734, by rfl⟩ : syracuseStep 6532979 = 9799469) B9799469
theorem B17421277 : Blo 2147435 17421277 := bstep (se 3 (by rfl) ⟨3266489, by rfl⟩ : syracuseStep 17421277 = 6532979) B6532979
theorem B23228369 : Blo 2147435 23228369 := bstep (se 2 (by rfl) ⟨8710638, by rfl⟩ : syracuseStep 23228369 = 17421277) B17421277
theorem B15485579 : Blo 2147435 15485579 := bstep (se 1 (by rfl) ⟨11614184, by rfl⟩ : syracuseStep 15485579 = 23228369) B23228369
theorem B10323719 : Blo 2147435 10323719 := bstep (se 1 (by rfl) ⟨7742789, by rfl⟩ : syracuseStep 10323719 = 15485579) B15485579
theorem B6882479 : Blo 2147435 6882479 := bstep (se 1 (by rfl) ⟨5161859, by rfl⟩ : syracuseStep 6882479 = 10323719) B10323719
theorem B4588319 : Blo 2147435 4588319 := bstep (se 1 (by rfl) ⟨3441239, by rfl⟩ : syracuseStep 4588319 = 6882479) B6882479
theorem B3058879 : Blo 2147435 3058879 := bstep (se 1 (by rfl) ⟨2294159, by rfl⟩ : syracuseStep 3058879 = 4588319) B4588319
theorem B4078505 : Blo 2147435 4078505 := bstep (se 2 (by rfl) ⟨1529439, by rfl⟩ : syracuseStep 4078505 = 3058879) B3058879
theorem B2719003 : Blo 2147435 2719003 := bstep (se 1 (by rfl) ⟨2039252, by rfl⟩ : syracuseStep 2719003 = 4078505) B4078505
theorem B3625337 : Blo 2147435 3625337 := bstep (se 2 (by rfl) ⟨1359501, by rfl⟩ : syracuseStep 3625337 = 2719003) B2719003
theorem B2416891 : Blo 2147435 2416891 := bstep (se 1 (by rfl) ⟨1812668, by rfl⟩ : syracuseStep 2416891 = 3625337) B3625337
theorem B3222521 : Blo 2147435 3222521 := bstep (se 2 (by rfl) ⟨1208445, by rfl⟩ : syracuseStep 3222521 = 2416891) B2416891
theorem B2148347 : Blo 2147435 2148347 := bstep (se 1 (by rfl) ⟨1611260, by rfl⟩ : syracuseStep 2148347 = 3222521) B3222521
theorem B5232293 : Blo 2147435 5232293 := bbase (se 4 (by rfl) ⟨490527, by rfl⟩ : syracuseStep 5232293 = 981055) (by norm_num)
theorem B3488195 : Blo 2147435 3488195 := bstep (se 1 (by rfl) ⟨2616146, by rfl⟩ : syracuseStep 3488195 = 5232293) B5232293
theorem B9301853 : Blo 2147435 9301853 := bstep (se 3 (by rfl) ⟨1744097, by rfl⟩ : syracuseStep 9301853 = 3488195) B3488195
theorem B6201235 : Blo 2147435 6201235 := bstep (se 1 (by rfl) ⟨4650926, by rfl⟩ : syracuseStep 6201235 = 9301853) B9301853
theorem B8268313 : Blo 2147435 8268313 := bstep (se 2 (by rfl) ⟨3100617, by rfl⟩ : syracuseStep 8268313 = 6201235) B6201235
theorem B11024417 : Blo 2147435 11024417 := bstep (se 2 (by rfl) ⟨4134156, by rfl⟩ : syracuseStep 11024417 = 8268313) B8268313
theorem B29398445 : Blo 2147435 29398445 := bstep (se 3 (by rfl) ⟨5512208, by rfl⟩ : syracuseStep 29398445 = 11024417) B11024417
theorem B19598963 : Blo 2147435 19598963 := bstep (se 1 (by rfl) ⟨14699222, by rfl⟩ : syracuseStep 19598963 = 29398445) B29398445
theorem B52263901 : Blo 2147435 52263901 := bstep (se 3 (by rfl) ⟨9799481, by rfl⟩ : syracuseStep 52263901 = 19598963) B19598963
theorem B69685201 : Blo 2147435 69685201 := bstep (se 2 (by rfl) ⟨26131950, by rfl⟩ : syracuseStep 69685201 = 52263901) B52263901
theorem B92913601 : Blo 2147435 92913601 := bstep (se 2 (by rfl) ⟨34842600, by rfl⟩ : syracuseStep 92913601 = 69685201) B69685201
theorem B123884801 : Blo 2147435 123884801 := bstep (se 2 (by rfl) ⟨46456800, by rfl⟩ : syracuseStep 123884801 = 92913601) B92913601
theorem B82589867 : Blo 2147435 82589867 := bstep (se 1 (by rfl) ⟨61942400, by rfl⟩ : syracuseStep 82589867 = 123884801) B123884801
theorem B55059911 : Blo 2147435 55059911 := bstep (se 1 (by rfl) ⟨41294933, by rfl⟩ : syracuseStep 55059911 = 82589867) B82589867
theorem B36706607 : Blo 2147435 36706607 := bstep (se 1 (by rfl) ⟨27529955, by rfl⟩ : syracuseStep 36706607 = 55059911) B55059911
theorem B24471071 : Blo 2147435 24471071 := bstep (se 1 (by rfl) ⟨18353303, by rfl⟩ : syracuseStep 24471071 = 36706607) B36706607
theorem B16314047 : Blo 2147435 16314047 := bstep (se 1 (by rfl) ⟨12235535, by rfl⟩ : syracuseStep 16314047 = 24471071) B24471071
theorem B10876031 : Blo 2147435 10876031 := bstep (se 1 (by rfl) ⟨8157023, by rfl⟩ : syracuseStep 10876031 = 16314047) B16314047
theorem B7250687 : Blo 2147435 7250687 := bstep (se 1 (by rfl) ⟨5438015, by rfl⟩ : syracuseStep 7250687 = 10876031) B10876031
theorem B4833791 : Blo 2147435 4833791 := bstep (se 1 (by rfl) ⟨3625343, by rfl⟩ : syracuseStep 4833791 = 7250687) B7250687
theorem B3222527 : Blo 2147435 3222527 := bstep (se 1 (by rfl) ⟨2416895, by rfl⟩ : syracuseStep 3222527 = 4833791) B4833791
theorem B2148351 : Blo 2147435 2148351 := bstep (se 1 (by rfl) ⟨1611263, by rfl⟩ : syracuseStep 2148351 = 3222527) B3222527
theorem B3222533 : Blo 2147435 3222533 := bbase (se 4 (by rfl) ⟨302112, by rfl⟩ : syracuseStep 3222533 = 604225) (by norm_num)
theorem B2148355 : Blo 2147435 2148355 := bstep (se 1 (by rfl) ⟨1611266, by rfl⟩ : syracuseStep 2148355 = 3222533) B3222533
theorem B3625357 : Blo 2147435 3625357 := bbase (se 3 (by rfl) ⟨679754, by rfl⟩ : syracuseStep 3625357 = 1359509) (by norm_num)
theorem B4833809 : Blo 2147435 4833809 := bstep (se 2 (by rfl) ⟨1812678, by rfl⟩ : syracuseStep 4833809 = 3625357) B3625357
theorem B3222539 : Blo 2147435 3222539 := bstep (se 1 (by rfl) ⟨2416904, by rfl⟩ : syracuseStep 3222539 = 4833809) B4833809
theorem B2148359 : Blo 2147435 2148359 := bstep (se 1 (by rfl) ⟨1611269, by rfl⟩ : syracuseStep 2148359 = 3222539) B3222539
theorem B2416909 : Blo 2147435 2416909 := bbase (se 3 (by rfl) ⟨453170, by rfl⟩ : syracuseStep 2416909 = 906341) (by norm_num)
theorem B3222545 : Blo 2147435 3222545 := bstep (se 2 (by rfl) ⟨1208454, by rfl⟩ : syracuseStep 3222545 = 2416909) B2416909
theorem B2148363 : Blo 2147435 2148363 := bstep (se 1 (by rfl) ⟨1611272, by rfl⟩ : syracuseStep 2148363 = 3222545) B3222545
theorem B7250741 : Blo 2147435 7250741 := bbase (se 5 (by rfl) ⟨339878, by rfl⟩ : syracuseStep 7250741 = 679757) (by norm_num)
theorem B4833827 : Blo 2147435 4833827 := bstep (se 1 (by rfl) ⟨3625370, by rfl⟩ : syracuseStep 4833827 = 7250741) B7250741
theorem B3222551 : Blo 2147435 3222551 := bstep (se 1 (by rfl) ⟨2416913, by rfl⟩ : syracuseStep 3222551 = 4833827) B4833827
theorem B2148367 : Blo 2147435 2148367 := bstep (se 1 (by rfl) ⟨1611275, by rfl⟩ : syracuseStep 2148367 = 3222551) B3222551
theorem B3222557 : Blo 2147435 3222557 := bbase (se 3 (by rfl) ⟨604229, by rfl⟩ : syracuseStep 3222557 = 1208459) (by norm_num)
theorem B2148371 : Blo 2147435 2148371 := bstep (se 1 (by rfl) ⟨1611278, by rfl⟩ : syracuseStep 2148371 = 3222557) B3222557
theorem B4833845 : Blo 2147435 4833845 := bbase (se 5 (by rfl) ⟨226586, by rfl⟩ : syracuseStep 4833845 = 453173) (by norm_num)
theorem B3222563 : Blo 2147435 3222563 := bstep (se 1 (by rfl) ⟨2416922, by rfl⟩ : syracuseStep 3222563 = 4833845) B4833845
theorem B2148375 : Blo 2147435 2148375 := bstep (se 1 (by rfl) ⟨1611281, by rfl⟩ : syracuseStep 2148375 = 3222563) B3222563
theorem B9176773 : Blo 2147435 9176773 := bbase (se 4 (by rfl) ⟨860322, by rfl⟩ : syracuseStep 9176773 = 1720645) (by norm_num)
theorem B12235697 : Blo 2147435 12235697 := bstep (se 2 (by rfl) ⟨4588386, by rfl⟩ : syracuseStep 12235697 = 9176773) B9176773
theorem B8157131 : Blo 2147435 8157131 := bstep (se 1 (by rfl) ⟨6117848, by rfl⟩ : syracuseStep 8157131 = 12235697) B12235697
theorem B5438087 : Blo 2147435 5438087 := bstep (se 1 (by rfl) ⟨4078565, by rfl⟩ : syracuseStep 5438087 = 8157131) B8157131
theorem B3625391 : Blo 2147435 3625391 := bstep (se 1 (by rfl) ⟨2719043, by rfl⟩ : syracuseStep 3625391 = 5438087) B5438087
theorem B2416927 : Blo 2147435 2416927 := bstep (se 1 (by rfl) ⟨1812695, by rfl⟩ : syracuseStep 2416927 = 3625391) B3625391
theorem B3222569 : Blo 2147435 3222569 := bstep (se 2 (by rfl) ⟨1208463, by rfl⟩ : syracuseStep 3222569 = 2416927) B2416927
theorem B2148379 : Blo 2147435 2148379 := bstep (se 1 (by rfl) ⟨1611284, by rfl⟩ : syracuseStep 2148379 = 3222569) B3222569
theorem B9176789 : Blo 2147435 9176789 := bbase (se 7 (by rfl) ⟨107540, by rfl⟩ : syracuseStep 9176789 = 215081) (by norm_num)
theorem B6117859 : Blo 2147435 6117859 := bstep (se 1 (by rfl) ⟨4588394, by rfl⟩ : syracuseStep 6117859 = 9176789) B9176789
theorem B8157145 : Blo 2147435 8157145 := bstep (se 2 (by rfl) ⟨3058929, by rfl⟩ : syracuseStep 8157145 = 6117859) B6117859
theorem B10876193 : Blo 2147435 10876193 := bstep (se 2 (by rfl) ⟨4078572, by rfl⟩ : syracuseStep 10876193 = 8157145) B8157145
theorem B7250795 : Blo 2147435 7250795 := bstep (se 1 (by rfl) ⟨5438096, by rfl⟩ : syracuseStep 7250795 = 10876193) B10876193
theorem B4833863 : Blo 2147435 4833863 := bstep (se 1 (by rfl) ⟨3625397, by rfl⟩ : syracuseStep 4833863 = 7250795) B7250795
theorem B3222575 : Blo 2147435 3222575 := bstep (se 1 (by rfl) ⟨2416931, by rfl⟩ : syracuseStep 3222575 = 4833863) B4833863
theorem B2148383 : Blo 2147435 2148383 := bstep (se 1 (by rfl) ⟨1611287, by rfl⟩ : syracuseStep 2148383 = 3222575) B3222575
theorem B3222581 : Blo 2147435 3222581 := bbase (se 5 (by rfl) ⟨151058, by rfl⟩ : syracuseStep 3222581 = 302117) (by norm_num)
theorem B2148387 : Blo 2147435 2148387 := bstep (se 1 (by rfl) ⟨1611290, by rfl⟩ : syracuseStep 2148387 = 3222581) B3222581
theorem B5438117 : Blo 2147435 5438117 := bbase (se 4 (by rfl) ⟨509823, by rfl⟩ : syracuseStep 5438117 = 1019647) (by norm_num)
theorem B3625411 : Blo 2147435 3625411 := bstep (se 1 (by rfl) ⟨2719058, by rfl⟩ : syracuseStep 3625411 = 5438117) B5438117
theorem B4833881 : Blo 2147435 4833881 := bstep (se 2 (by rfl) ⟨1812705, by rfl⟩ : syracuseStep 4833881 = 3625411) B3625411
theorem B3222587 : Blo 2147435 3222587 := bstep (se 1 (by rfl) ⟨2416940, by rfl⟩ : syracuseStep 3222587 = 4833881) B4833881
theorem B2148391 : Blo 2147435 2148391 := bstep (se 1 (by rfl) ⟨1611293, by rfl⟩ : syracuseStep 2148391 = 3222587) B3222587
theorem B2416945 : Blo 2147435 2416945 := bbase (se 2 (by rfl) ⟨906354, by rfl⟩ : syracuseStep 2416945 = 1812709) (by norm_num)
theorem B3222593 : Blo 2147435 3222593 := bstep (se 2 (by rfl) ⟨1208472, by rfl⟩ : syracuseStep 3222593 = 2416945) B2416945
theorem B2148395 : Blo 2147435 2148395 := bstep (se 1 (by rfl) ⟨1611296, by rfl⟩ : syracuseStep 2148395 = 3222593) B3222593
theorem B4588429 : Blo 2147435 4588429 := bbase (se 3 (by rfl) ⟨860330, by rfl⟩ : syracuseStep 4588429 = 1720661) (by norm_num)
theorem B6117905 : Blo 2147435 6117905 := bstep (se 2 (by rfl) ⟨2294214, by rfl⟩ : syracuseStep 6117905 = 4588429) B4588429
theorem B4078603 : Blo 2147435 4078603 := bstep (se 1 (by rfl) ⟨3058952, by rfl⟩ : syracuseStep 4078603 = 6117905) B6117905
theorem B5438137 : Blo 2147435 5438137 := bstep (se 2 (by rfl) ⟨2039301, by rfl⟩ : syracuseStep 5438137 = 4078603) B4078603
theorem B7250849 : Blo 2147435 7250849 := bstep (se 2 (by rfl) ⟨2719068, by rfl⟩ : syracuseStep 7250849 = 5438137) B5438137
theorem B4833899 : Blo 2147435 4833899 := bstep (se 1 (by rfl) ⟨3625424, by rfl⟩ : syracuseStep 4833899 = 7250849) B7250849
theorem B3222599 : Blo 2147435 3222599 := bstep (se 1 (by rfl) ⟨2416949, by rfl⟩ : syracuseStep 3222599 = 4833899) B4833899
theorem B2148399 : Blo 2147435 2148399 := bstep (se 1 (by rfl) ⟨1611299, by rfl⟩ : syracuseStep 2148399 = 3222599) B3222599
theorem B3222605 : Blo 2147435 3222605 := bbase (se 3 (by rfl) ⟨604238, by rfl⟩ : syracuseStep 3222605 = 1208477) (by norm_num)
theorem B2148403 : Blo 2147435 2148403 := bstep (se 1 (by rfl) ⟨1611302, by rfl⟩ : syracuseStep 2148403 = 3222605) B3222605
theorem B4833917 : Blo 2147435 4833917 := bbase (se 3 (by rfl) ⟨906359, by rfl⟩ : syracuseStep 4833917 = 1812719) (by norm_num)
theorem B3222611 : Blo 2147435 3222611 := bstep (se 1 (by rfl) ⟨2416958, by rfl⟩ : syracuseStep 3222611 = 4833917) B4833917
theorem B2148407 : Blo 2147435 2148407 := bstep (se 1 (by rfl) ⟨1611305, by rfl⟩ : syracuseStep 2148407 = 3222611) B3222611
theorem B3625445 : Blo 2147435 3625445 := bbase (se 4 (by rfl) ⟨339885, by rfl⟩ : syracuseStep 3625445 = 679771) (by norm_num)
theorem B2416963 : Blo 2147435 2416963 := bstep (se 1 (by rfl) ⟨1812722, by rfl⟩ : syracuseStep 2416963 = 3625445) B3625445
theorem B3222617 : Blo 2147435 3222617 := bstep (se 2 (by rfl) ⟨1208481, by rfl⟩ : syracuseStep 3222617 = 2416963) B2416963
theorem B2148411 : Blo 2147435 2148411 := bstep (se 1 (by rfl) ⟨1611308, by rfl⟩ : syracuseStep 2148411 = 3222617) B3222617
theorem B11614549 : Blo 2147435 11614549 := bbase (se 10 (by rfl) ⟨17013, by rfl⟩ : syracuseStep 11614549 = 34027) (by norm_num)
theorem B15486065 : Blo 2147435 15486065 := bstep (se 2 (by rfl) ⟨5807274, by rfl⟩ : syracuseStep 15486065 = 11614549) B11614549
theorem B10324043 : Blo 2147435 10324043 := bstep (se 1 (by rfl) ⟨7743032, by rfl⟩ : syracuseStep 10324043 = 15486065) B15486065
theorem B6882695 : Blo 2147435 6882695 := bstep (se 1 (by rfl) ⟨5162021, by rfl⟩ : syracuseStep 6882695 = 10324043) B10324043
theorem B4588463 : Blo 2147435 4588463 := bstep (se 1 (by rfl) ⟨3441347, by rfl⟩ : syracuseStep 4588463 = 6882695) B6882695
theorem B3058975 : Blo 2147435 3058975 := bstep (se 1 (by rfl) ⟨2294231, by rfl⟩ : syracuseStep 3058975 = 4588463) B4588463
theorem B16314533 : Blo 2147435 16314533 := bstep (se 4 (by rfl) ⟨1529487, by rfl⟩ : syracuseStep 16314533 = 3058975) B3058975
theorem B10876355 : Blo 2147435 10876355 := bstep (se 1 (by rfl) ⟨8157266, by rfl⟩ : syracuseStep 10876355 = 16314533) B16314533
theorem B7250903 : Blo 2147435 7250903 := bstep (se 1 (by rfl) ⟨5438177, by rfl⟩ : syracuseStep 7250903 = 10876355) B10876355
theorem B4833935 : Blo 2147435 4833935 := bstep (se 1 (by rfl) ⟨3625451, by rfl⟩ : syracuseStep 4833935 = 7250903) B7250903
theorem B3222623 : Blo 2147435 3222623 := bstep (se 1 (by rfl) ⟨2416967, by rfl⟩ : syracuseStep 3222623 = 4833935) B4833935
theorem B2148415 : Blo 2147435 2148415 := bstep (se 1 (by rfl) ⟨1611311, by rfl⟩ : syracuseStep 2148415 = 3222623) B3222623
theorem B3222629 : Blo 2147435 3222629 := bbase (se 4 (by rfl) ⟨302121, by rfl⟩ : syracuseStep 3222629 = 604243) (by norm_num)
theorem B2148419 : Blo 2147435 2148419 := bstep (se 1 (by rfl) ⟨1611314, by rfl⟩ : syracuseStep 2148419 = 3222629) B3222629
theorem B2581021 : Blo 2147435 2581021 := bbase (se 3 (by rfl) ⟨483941, by rfl⟩ : syracuseStep 2581021 = 967883) (by norm_num)
theorem B3441361 : Blo 2147435 3441361 := bstep (se 2 (by rfl) ⟨1290510, by rfl⟩ : syracuseStep 3441361 = 2581021) B2581021
theorem B4588481 : Blo 2147435 4588481 := bstep (se 2 (by rfl) ⟨1720680, by rfl⟩ : syracuseStep 4588481 = 3441361) B3441361
theorem B3058987 : Blo 2147435 3058987 := bstep (se 1 (by rfl) ⟨2294240, by rfl⟩ : syracuseStep 3058987 = 4588481) B4588481
theorem B4078649 : Blo 2147435 4078649 := bstep (se 2 (by rfl) ⟨1529493, by rfl⟩ : syracuseStep 4078649 = 3058987) B3058987
theorem B2719099 : Blo 2147435 2719099 := bstep (se 1 (by rfl) ⟨2039324, by rfl⟩ : syracuseStep 2719099 = 4078649) B4078649
theorem B3625465 : Blo 2147435 3625465 := bstep (se 2 (by rfl) ⟨1359549, by rfl⟩ : syracuseStep 3625465 = 2719099) B2719099
theorem B4833953 : Blo 2147435 4833953 := bstep (se 2 (by rfl) ⟨1812732, by rfl⟩ : syracuseStep 4833953 = 3625465) B3625465
theorem B3222635 : Blo 2147435 3222635 := bstep (se 1 (by rfl) ⟨2416976, by rfl⟩ : syracuseStep 3222635 = 4833953) B4833953
theorem B2148423 : Blo 2147435 2148423 := bstep (se 1 (by rfl) ⟨1611317, by rfl⟩ : syracuseStep 2148423 = 3222635) B3222635
theorem B2416981 : Blo 2147435 2416981 := bbase (se 10 (by rfl) ⟨3540, by rfl⟩ : syracuseStep 2416981 = 7081) (by norm_num)
theorem B3222641 : Blo 2147435 3222641 := bstep (se 2 (by rfl) ⟨1208490, by rfl⟩ : syracuseStep 3222641 = 2416981) B2416981
theorem B2148427 : Blo 2147435 2148427 := bstep (se 1 (by rfl) ⟨1611320, by rfl⟩ : syracuseStep 2148427 = 3222641) B3222641
theorem B2719109 : Blo 2147435 2719109 := bbase (se 4 (by rfl) ⟨254916, by rfl⟩ : syracuseStep 2719109 = 509833) (by norm_num)
theorem B7250957 : Blo 2147435 7250957 := bstep (se 3 (by rfl) ⟨1359554, by rfl⟩ : syracuseStep 7250957 = 2719109) B2719109
theorem B4833971 : Blo 2147435 4833971 := bstep (se 1 (by rfl) ⟨3625478, by rfl⟩ : syracuseStep 4833971 = 7250957) B7250957
theorem B3222647 : Blo 2147435 3222647 := bstep (se 1 (by rfl) ⟨2416985, by rfl⟩ : syracuseStep 3222647 = 4833971) B4833971
theorem B2148431 : Blo 2147435 2148431 := bstep (se 1 (by rfl) ⟨1611323, by rfl⟩ : syracuseStep 2148431 = 3222647) B3222647
theorem B3222653 : Blo 2147435 3222653 := bbase (se 3 (by rfl) ⟨604247, by rfl⟩ : syracuseStep 3222653 = 1208495) (by norm_num)
theorem B2148435 : Blo 2147435 2148435 := bstep (se 1 (by rfl) ⟨1611326, by rfl⟩ : syracuseStep 2148435 = 3222653) B3222653
theorem B4833989 : Blo 2147435 4833989 := bbase (se 4 (by rfl) ⟨453186, by rfl⟩ : syracuseStep 4833989 = 906373) (by norm_num)
theorem B3222659 : Blo 2147435 3222659 := bstep (se 1 (by rfl) ⟨2416994, by rfl⟩ : syracuseStep 3222659 = 4833989) B4833989
theorem B2148439 : Blo 2147435 2148439 := bstep (se 1 (by rfl) ⟨1611329, by rfl⟩ : syracuseStep 2148439 = 3222659) B3222659
theorem B3674965 : Blo 2147435 3674965 := bbase (se 9 (by rfl) ⟨10766, by rfl⟩ : syracuseStep 3674965 = 21533) (by norm_num)
theorem B4899953 : Blo 2147435 4899953 := bstep (se 2 (by rfl) ⟨1837482, by rfl⟩ : syracuseStep 4899953 = 3674965) B3674965
theorem B13066541 : Blo 2147435 13066541 := bstep (se 3 (by rfl) ⟨2449976, by rfl⟩ : syracuseStep 13066541 = 4899953) B4899953
theorem B8711027 : Blo 2147435 8711027 := bstep (se 1 (by rfl) ⟨6533270, by rfl⟩ : syracuseStep 8711027 = 13066541) B13066541
theorem B5807351 : Blo 2147435 5807351 := bstep (se 1 (by rfl) ⟨4355513, by rfl⟩ : syracuseStep 5807351 = 8711027) B8711027
theorem B3871567 : Blo 2147435 3871567 := bstep (se 1 (by rfl) ⟨2903675, by rfl⟩ : syracuseStep 3871567 = 5807351) B5807351
theorem B20648357 : Blo 2147435 20648357 := bstep (se 4 (by rfl) ⟨1935783, by rfl⟩ : syracuseStep 20648357 = 3871567) B3871567
theorem B13765571 : Blo 2147435 13765571 := bstep (se 1 (by rfl) ⟨10324178, by rfl⟩ : syracuseStep 13765571 = 20648357) B20648357
theorem B9177047 : Blo 2147435 9177047 := bstep (se 1 (by rfl) ⟨6882785, by rfl⟩ : syracuseStep 9177047 = 13765571) B13765571
theorem B6118031 : Blo 2147435 6118031 := bstep (se 1 (by rfl) ⟨4588523, by rfl⟩ : syracuseStep 6118031 = 9177047) B9177047
theorem B4078687 : Blo 2147435 4078687 := bstep (se 1 (by rfl) ⟨3059015, by rfl⟩ : syracuseStep 4078687 = 6118031) B6118031
theorem B5438249 : Blo 2147435 5438249 := bstep (se 2 (by rfl) ⟨2039343, by rfl⟩ : syracuseStep 5438249 = 4078687) B4078687
theorem B3625499 : Blo 2147435 3625499 := bstep (se 1 (by rfl) ⟨2719124, by rfl⟩ : syracuseStep 3625499 = 5438249) B5438249
theorem B2416999 : Blo 2147435 2416999 := bstep (se 1 (by rfl) ⟨1812749, by rfl⟩ : syracuseStep 2416999 = 3625499) B3625499
theorem B3222665 : Blo 2147435 3222665 := bstep (se 2 (by rfl) ⟨1208499, by rfl⟩ : syracuseStep 3222665 = 2416999) B2416999
theorem B2148443 : Blo 2147435 2148443 := bstep (se 1 (by rfl) ⟨1611332, by rfl⟩ : syracuseStep 2148443 = 3222665) B3222665
theorem B10876517 : Blo 2147435 10876517 := bbase (se 4 (by rfl) ⟨1019673, by rfl⟩ : syracuseStep 10876517 = 2039347) (by norm_num)
theorem B7251011 : Blo 2147435 7251011 := bstep (se 1 (by rfl) ⟨5438258, by rfl⟩ : syracuseStep 7251011 = 10876517) B10876517
theorem B4834007 : Blo 2147435 4834007 := bstep (se 1 (by rfl) ⟨3625505, by rfl⟩ : syracuseStep 4834007 = 7251011) B7251011
theorem B3222671 : Blo 2147435 3222671 := bstep (se 1 (by rfl) ⟨2417003, by rfl⟩ : syracuseStep 3222671 = 4834007) B4834007
theorem B2148447 : Blo 2147435 2148447 := bstep (se 1 (by rfl) ⟨1611335, by rfl⟩ : syracuseStep 2148447 = 3222671) B3222671
theorem B3222677 : Blo 2147435 3222677 := bbase (se 6 (by rfl) ⟨75531, by rfl⟩ : syracuseStep 3222677 = 151063) (by norm_num)
theorem B2148451 : Blo 2147435 2148451 := bstep (se 1 (by rfl) ⟨1611338, by rfl⟩ : syracuseStep 2148451 = 3222677) B3222677
theorem B3266653 : Blo 2147435 3266653 := bbase (se 3 (by rfl) ⟨612497, by rfl⟩ : syracuseStep 3266653 = 1224995) (by norm_num)
theorem B4355537 : Blo 2147435 4355537 := bstep (se 2 (by rfl) ⟨1633326, by rfl⟩ : syracuseStep 4355537 = 3266653) B3266653
theorem B11614765 : Blo 2147435 11614765 := bstep (se 3 (by rfl) ⟨2177768, by rfl⟩ : syracuseStep 11614765 = 4355537) B4355537
theorem B15486353 : Blo 2147435 15486353 := bstep (se 2 (by rfl) ⟨5807382, by rfl⟩ : syracuseStep 15486353 = 11614765) B11614765
theorem B10324235 : Blo 2147435 10324235 := bstep (se 1 (by rfl) ⟨7743176, by rfl⟩ : syracuseStep 10324235 = 15486353) B15486353
theorem B6882823 : Blo 2147435 6882823 := bstep (se 1 (by rfl) ⟨5162117, by rfl⟩ : syracuseStep 6882823 = 10324235) B10324235
theorem B9177097 : Blo 2147435 9177097 := bstep (se 2 (by rfl) ⟨3441411, by rfl⟩ : syracuseStep 9177097 = 6882823) B6882823
theorem B12236129 : Blo 2147435 12236129 := bstep (se 2 (by rfl) ⟨4588548, by rfl⟩ : syracuseStep 12236129 = 9177097) B9177097
theorem B8157419 : Blo 2147435 8157419 := bstep (se 1 (by rfl) ⟨6118064, by rfl⟩ : syracuseStep 8157419 = 12236129) B12236129
theorem B5438279 : Blo 2147435 5438279 := bstep (se 1 (by rfl) ⟨4078709, by rfl⟩ : syracuseStep 5438279 = 8157419) B8157419
theorem B3625519 : Blo 2147435 3625519 := bstep (se 1 (by rfl) ⟨2719139, by rfl⟩ : syracuseStep 3625519 = 5438279) B5438279
theorem B4834025 : Blo 2147435 4834025 := bstep (se 2 (by rfl) ⟨1812759, by rfl⟩ : syracuseStep 4834025 = 3625519) B3625519
theorem B3222683 : Blo 2147435 3222683 := bstep (se 1 (by rfl) ⟨2417012, by rfl⟩ : syracuseStep 3222683 = 4834025) B4834025
theorem B2148455 : Blo 2147435 2148455 := bstep (se 1 (by rfl) ⟨1611341, by rfl⟩ : syracuseStep 2148455 = 3222683) B3222683
theorem B2417017 : Blo 2147435 2417017 := bbase (se 2 (by rfl) ⟨906381, by rfl⟩ : syracuseStep 2417017 = 1812763) (by norm_num)
theorem B3222689 : Blo 2147435 3222689 := bstep (se 2 (by rfl) ⟨1208508, by rfl⟩ : syracuseStep 3222689 = 2417017) B2417017
theorem B2148459 : Blo 2147435 2148459 := bstep (se 1 (by rfl) ⟨1611344, by rfl⟩ : syracuseStep 2148459 = 3222689) B3222689
theorem B7743205 : Blo 2147435 7743205 := bbase (se 4 (by rfl) ⟨725925, by rfl⟩ : syracuseStep 7743205 = 1451851) (by norm_num)
theorem B10324273 : Blo 2147435 10324273 := bstep (se 2 (by rfl) ⟨3871602, by rfl⟩ : syracuseStep 10324273 = 7743205) B7743205
theorem B13765697 : Blo 2147435 13765697 := bstep (se 2 (by rfl) ⟨5162136, by rfl⟩ : syracuseStep 13765697 = 10324273) B10324273
theorem B9177131 : Blo 2147435 9177131 := bstep (se 1 (by rfl) ⟨6882848, by rfl⟩ : syracuseStep 9177131 = 13765697) B13765697
theorem B6118087 : Blo 2147435 6118087 := bstep (se 1 (by rfl) ⟨4588565, by rfl⟩ : syracuseStep 6118087 = 9177131) B9177131
theorem B8157449 : Blo 2147435 8157449 := bstep (se 2 (by rfl) ⟨3059043, by rfl⟩ : syracuseStep 8157449 = 6118087) B6118087
theorem B5438299 : Blo 2147435 5438299 := bstep (se 1 (by rfl) ⟨4078724, by rfl⟩ : syracuseStep 5438299 = 8157449) B8157449
theorem B7251065 : Blo 2147435 7251065 := bstep (se 2 (by rfl) ⟨2719149, by rfl⟩ : syracuseStep 7251065 = 5438299) B5438299
theorem B4834043 : Blo 2147435 4834043 := bstep (se 1 (by rfl) ⟨3625532, by rfl⟩ : syracuseStep 4834043 = 7251065) B7251065
theorem B3222695 : Blo 2147435 3222695 := bstep (se 1 (by rfl) ⟨2417021, by rfl⟩ : syracuseStep 3222695 = 4834043) B4834043
theorem B2148463 : Blo 2147435 2148463 := bstep (se 1 (by rfl) ⟨1611347, by rfl⟩ : syracuseStep 2148463 = 3222695) B3222695
theorem B3222701 : Blo 2147435 3222701 := bbase (se 3 (by rfl) ⟨604256, by rfl⟩ : syracuseStep 3222701 = 1208513) (by norm_num)
theorem B2148467 : Blo 2147435 2148467 := bstep (se 1 (by rfl) ⟨1611350, by rfl⟩ : syracuseStep 2148467 = 3222701) B3222701
theorem B4834061 : Blo 2147435 4834061 := bbase (se 3 (by rfl) ⟨906386, by rfl⟩ : syracuseStep 4834061 = 1812773) (by norm_num)
theorem B3222707 : Blo 2147435 3222707 := bstep (se 1 (by rfl) ⟨2417030, by rfl⟩ : syracuseStep 3222707 = 4834061) B4834061
theorem B2148471 : Blo 2147435 2148471 := bstep (se 1 (by rfl) ⟨1611353, by rfl⟩ : syracuseStep 2148471 = 3222707) B3222707
theorem B2719165 : Blo 2147435 2719165 := bbase (se 3 (by rfl) ⟨509843, by rfl⟩ : syracuseStep 2719165 = 1019687) (by norm_num)
theorem B3625553 : Blo 2147435 3625553 := bstep (se 2 (by rfl) ⟨1359582, by rfl⟩ : syracuseStep 3625553 = 2719165) B2719165
theorem B2417035 : Blo 2147435 2417035 := bstep (se 1 (by rfl) ⟨1812776, by rfl⟩ : syracuseStep 2417035 = 3625553) B3625553
theorem B3222713 : Blo 2147435 3222713 := bstep (se 2 (by rfl) ⟨1208517, by rfl⟩ : syracuseStep 3222713 = 2417035) B2417035
theorem B2148475 : Blo 2147435 2148475 := bstep (se 1 (by rfl) ⟨1611356, by rfl⟩ : syracuseStep 2148475 = 3222713) B3222713
theorem B2450017 : Blo 2147435 2450017 := bbase (se 2 (by rfl) ⟨918756, by rfl⟩ : syracuseStep 2450017 = 1837513) (by norm_num)
theorem B13066757 : Blo 2147435 13066757 := bstep (se 4 (by rfl) ⟨1225008, by rfl⟩ : syracuseStep 13066757 = 2450017) B2450017
theorem B8711171 : Blo 2147435 8711171 := bstep (se 1 (by rfl) ⟨6533378, by rfl⟩ : syracuseStep 8711171 = 13066757) B13066757
theorem B5807447 : Blo 2147435 5807447 := bstep (se 1 (by rfl) ⟨4355585, by rfl⟩ : syracuseStep 5807447 = 8711171) B8711171
theorem B3871631 : Blo 2147435 3871631 := bstep (se 1 (by rfl) ⟨2903723, by rfl⟩ : syracuseStep 3871631 = 5807447) B5807447
theorem B10324349 : Blo 2147435 10324349 := bstep (se 3 (by rfl) ⟨1935815, by rfl⟩ : syracuseStep 10324349 = 3871631) B3871631
theorem B6882899 : Blo 2147435 6882899 := bstep (se 1 (by rfl) ⟨5162174, by rfl⟩ : syracuseStep 6882899 = 10324349) B10324349
theorem B18354397 : Blo 2147435 18354397 := bstep (se 3 (by rfl) ⟨3441449, by rfl⟩ : syracuseStep 18354397 = 6882899) B6882899
theorem B24472529 : Blo 2147435 24472529 := bstep (se 2 (by rfl) ⟨9177198, by rfl⟩ : syracuseStep 24472529 = 18354397) B18354397
theorem B16315019 : Blo 2147435 16315019 := bstep (se 1 (by rfl) ⟨12236264, by rfl⟩ : syracuseStep 16315019 = 24472529) B24472529
theorem B10876679 : Blo 2147435 10876679 := bstep (se 1 (by rfl) ⟨8157509, by rfl⟩ : syracuseStep 10876679 = 16315019) B16315019
theorem B7251119 : Blo 2147435 7251119 := bstep (se 1 (by rfl) ⟨5438339, by rfl⟩ : syracuseStep 7251119 = 10876679) B10876679
theorem B4834079 : Blo 2147435 4834079 := bstep (se 1 (by rfl) ⟨3625559, by rfl⟩ : syracuseStep 4834079 = 7251119) B7251119
theorem B3222719 : Blo 2147435 3222719 := bstep (se 1 (by rfl) ⟨2417039, by rfl⟩ : syracuseStep 3222719 = 4834079) B4834079
theorem B2148479 : Blo 2147435 2148479 := bstep (se 1 (by rfl) ⟨1611359, by rfl⟩ : syracuseStep 2148479 = 3222719) B3222719
theorem B3222725 : Blo 2147435 3222725 := bbase (se 4 (by rfl) ⟨302130, by rfl⟩ : syracuseStep 3222725 = 604261) (by norm_num)
theorem B2148483 : Blo 2147435 2148483 := bstep (se 1 (by rfl) ⟨1611362, by rfl⟩ : syracuseStep 2148483 = 3222725) B3222725
theorem B3625573 : Blo 2147435 3625573 := bbase (se 4 (by rfl) ⟨339897, by rfl⟩ : syracuseStep 3625573 = 679795) (by norm_num)
theorem B4834097 : Blo 2147435 4834097 := bstep (se 2 (by rfl) ⟨1812786, by rfl⟩ : syracuseStep 4834097 = 3625573) B3625573
theorem B3222731 : Blo 2147435 3222731 := bstep (se 1 (by rfl) ⟨2417048, by rfl⟩ : syracuseStep 3222731 = 4834097) B4834097
theorem B2148487 : Blo 2147435 2148487 := bstep (se 1 (by rfl) ⟨1611365, by rfl⟩ : syracuseStep 2148487 = 3222731) B3222731
theorem B2417053 : Blo 2147435 2417053 := bbase (se 3 (by rfl) ⟨453197, by rfl⟩ : syracuseStep 2417053 = 906395) (by norm_num)
theorem B3222737 : Blo 2147435 3222737 := bstep (se 2 (by rfl) ⟨1208526, by rfl⟩ : syracuseStep 3222737 = 2417053) B2417053
theorem B2148491 : Blo 2147435 2148491 := bstep (se 1 (by rfl) ⟨1611368, by rfl⟩ : syracuseStep 2148491 = 3222737) B3222737
theorem B7251173 : Blo 2147435 7251173 := bbase (se 4 (by rfl) ⟨679797, by rfl⟩ : syracuseStep 7251173 = 1359595) (by norm_num)
theorem B4834115 : Blo 2147435 4834115 := bstep (se 1 (by rfl) ⟨3625586, by rfl⟩ : syracuseStep 4834115 = 7251173) B7251173
theorem B3222743 : Blo 2147435 3222743 := bstep (se 1 (by rfl) ⟨2417057, by rfl⟩ : syracuseStep 3222743 = 4834115) B4834115
theorem B2148495 : Blo 2147435 2148495 := bstep (se 1 (by rfl) ⟨1611371, by rfl⟩ : syracuseStep 2148495 = 3222743) B3222743
theorem B3222749 : Blo 2147435 3222749 := bbase (se 3 (by rfl) ⟨604265, by rfl⟩ : syracuseStep 3222749 = 1208531) (by norm_num)
theorem B2148499 : Blo 2147435 2148499 := bstep (se 1 (by rfl) ⟨1611374, by rfl⟩ : syracuseStep 2148499 = 3222749) B3222749
theorem B4834133 : Blo 2147435 4834133 := bbase (se 9 (by rfl) ⟨14162, by rfl⟩ : syracuseStep 4834133 = 28325) (by norm_num)
theorem B3222755 : Blo 2147435 3222755 := bstep (se 1 (by rfl) ⟨2417066, by rfl⟩ : syracuseStep 3222755 = 4834133) B4834133
theorem B2148503 : Blo 2147435 2148503 := bstep (se 1 (by rfl) ⟨1611377, by rfl⟩ : syracuseStep 2148503 = 3222755) B3222755
theorem B6118213 : Blo 2147435 6118213 := bbase (se 4 (by rfl) ⟨573582, by rfl⟩ : syracuseStep 6118213 = 1147165) (by norm_num)
theorem B8157617 : Blo 2147435 8157617 := bstep (se 2 (by rfl) ⟨3059106, by rfl⟩ : syracuseStep 8157617 = 6118213) B6118213
theorem B5438411 : Blo 2147435 5438411 := bstep (se 1 (by rfl) ⟨4078808, by rfl⟩ : syracuseStep 5438411 = 8157617) B8157617
theorem B3625607 : Blo 2147435 3625607 := bstep (se 1 (by rfl) ⟨2719205, by rfl⟩ : syracuseStep 3625607 = 5438411) B5438411
theorem B2417071 : Blo 2147435 2417071 := bstep (se 1 (by rfl) ⟨1812803, by rfl⟩ : syracuseStep 2417071 = 3625607) B3625607
theorem B3222761 : Blo 2147435 3222761 := bstep (se 2 (by rfl) ⟨1208535, by rfl⟩ : syracuseStep 3222761 = 2417071) B2417071
theorem B2148507 : Blo 2147435 2148507 := bstep (se 1 (by rfl) ⟨1611380, by rfl⟩ : syracuseStep 2148507 = 3222761) B3222761
theorem B2983541 : Blo 2147435 2983541 := bbase (se 5 (by rfl) ⟨139853, by rfl⟩ : syracuseStep 2983541 = 279707) (by norm_num)
theorem B7956109 : Blo 2147435 7956109 := bstep (se 3 (by rfl) ⟨1491770, by rfl⟩ : syracuseStep 7956109 = 2983541) B2983541
theorem B42432581 : Blo 2147435 42432581 := bstep (se 4 (by rfl) ⟨3978054, by rfl⟩ : syracuseStep 42432581 = 7956109) B7956109
theorem B28288387 : Blo 2147435 28288387 := bstep (se 1 (by rfl) ⟨21216290, by rfl⟩ : syracuseStep 28288387 = 42432581) B42432581
theorem B37717849 : Blo 2147435 37717849 := bstep (se 2 (by rfl) ⟨14144193, by rfl⟩ : syracuseStep 37717849 = 28288387) B28288387
theorem B50290465 : Blo 2147435 50290465 := bstep (se 2 (by rfl) ⟨18858924, by rfl⟩ : syracuseStep 50290465 = 37717849) B37717849
theorem B67053953 : Blo 2147435 67053953 := bstep (se 2 (by rfl) ⟨25145232, by rfl⟩ : syracuseStep 67053953 = 50290465) B50290465
theorem B178810541 : Blo 2147435 178810541 := bstep (se 3 (by rfl) ⟨33526976, by rfl⟩ : syracuseStep 178810541 = 67053953) B67053953
theorem B119207027 : Blo 2147435 119207027 := bstep (se 1 (by rfl) ⟨89405270, by rfl⟩ : syracuseStep 119207027 = 178810541) B178810541
theorem B317885405 : Blo 2147435 317885405 := bstep (se 3 (by rfl) ⟨59603513, by rfl⟩ : syracuseStep 317885405 = 119207027) B119207027
theorem B847694413 : Blo 2147435 847694413 := bstep (se 3 (by rfl) ⟨158942702, by rfl⟩ : syracuseStep 847694413 = 317885405) B317885405
theorem B1130259217 : Blo 2147435 1130259217 := bstep (se 2 (by rfl) ⟨423847206, by rfl⟩ : syracuseStep 1130259217 = 847694413) B847694413
theorem B1507012289 : Blo 2147435 1507012289 := bstep (se 2 (by rfl) ⟨565129608, by rfl⟩ : syracuseStep 1507012289 = 1130259217) B1130259217
theorem B1004674859 : Blo 2147435 1004674859 := bstep (se 1 (by rfl) ⟨753506144, by rfl⟩ : syracuseStep 1004674859 = 1507012289) B1507012289
theorem B669783239 : Blo 2147435 669783239 := bstep (se 1 (by rfl) ⟨502337429, by rfl⟩ : syracuseStep 669783239 = 1004674859) B1004674859
theorem B446522159 : Blo 2147435 446522159 := bstep (se 1 (by rfl) ⟨334891619, by rfl⟩ : syracuseStep 446522159 = 669783239) B669783239
theorem B297681439 : Blo 2147435 297681439 := bstep (se 1 (by rfl) ⟨223261079, by rfl⟩ : syracuseStep 297681439 = 446522159) B446522159
theorem B396908585 : Blo 2147435 396908585 := bstep (se 2 (by rfl) ⟨148840719, by rfl⟩ : syracuseStep 396908585 = 297681439) B297681439
theorem B264605723 : Blo 2147435 264605723 := bstep (se 1 (by rfl) ⟨198454292, by rfl⟩ : syracuseStep 264605723 = 396908585) B396908585
theorem B176403815 : Blo 2147435 176403815 := bstep (se 1 (by rfl) ⟨132302861, by rfl⟩ : syracuseStep 176403815 = 264605723) B264605723
theorem B117602543 : Blo 2147435 117602543 := bstep (se 1 (by rfl) ⟨88201907, by rfl⟩ : syracuseStep 117602543 = 176403815) B176403815
theorem B78401695 : Blo 2147435 78401695 := bstep (se 1 (by rfl) ⟨58801271, by rfl⟩ : syracuseStep 78401695 = 117602543) B117602543
theorem B104535593 : Blo 2147435 104535593 := bstep (se 2 (by rfl) ⟨39200847, by rfl⟩ : syracuseStep 104535593 = 78401695) B78401695
theorem B69690395 : Blo 2147435 69690395 := bstep (se 1 (by rfl) ⟨52267796, by rfl⟩ : syracuseStep 69690395 = 104535593) B104535593
theorem B46460263 : Blo 2147435 46460263 := bstep (se 1 (by rfl) ⟨34845197, by rfl⟩ : syracuseStep 46460263 = 69690395) B69690395
theorem B61947017 : Blo 2147435 61947017 := bstep (se 2 (by rfl) ⟨23230131, by rfl⟩ : syracuseStep 61947017 = 46460263) B46460263
theorem B41298011 : Blo 2147435 41298011 := bstep (se 1 (by rfl) ⟨30973508, by rfl⟩ : syracuseStep 41298011 = 61947017) B61947017
theorem B27532007 : Blo 2147435 27532007 := bstep (se 1 (by rfl) ⟨20649005, by rfl⟩ : syracuseStep 27532007 = 41298011) B41298011
theorem B18354671 : Blo 2147435 18354671 := bstep (se 1 (by rfl) ⟨13766003, by rfl⟩ : syracuseStep 18354671 = 27532007) B27532007
theorem B12236447 : Blo 2147435 12236447 := bstep (se 1 (by rfl) ⟨9177335, by rfl⟩ : syracuseStep 12236447 = 18354671) B18354671
theorem B8157631 : Blo 2147435 8157631 := bstep (se 1 (by rfl) ⟨6118223, by rfl⟩ : syracuseStep 8157631 = 12236447) B12236447
theorem B10876841 : Blo 2147435 10876841 := bstep (se 2 (by rfl) ⟨4078815, by rfl⟩ : syracuseStep 10876841 = 8157631) B8157631
theorem B7251227 : Blo 2147435 7251227 := bstep (se 1 (by rfl) ⟨5438420, by rfl⟩ : syracuseStep 7251227 = 10876841) B10876841
theorem B4834151 : Blo 2147435 4834151 := bstep (se 1 (by rfl) ⟨3625613, by rfl⟩ : syracuseStep 4834151 = 7251227) B7251227
theorem B3222767 : Blo 2147435 3222767 := bstep (se 1 (by rfl) ⟨2417075, by rfl⟩ : syracuseStep 3222767 = 4834151) B4834151
theorem B2148511 : Blo 2147435 2148511 := bstep (se 1 (by rfl) ⟨1611383, by rfl⟩ : syracuseStep 2148511 = 3222767) B3222767
theorem B3222773 : Blo 2147435 3222773 := bbase (se 5 (by rfl) ⟨151067, by rfl⟩ : syracuseStep 3222773 = 302135) (by norm_num)
theorem B2148515 : Blo 2147435 2148515 := bstep (se 1 (by rfl) ⟨1611386, by rfl⟩ : syracuseStep 2148515 = 3222773) B3222773
theorem B78402005 : Blo 2147435 78402005 := bbase (se 7 (by rfl) ⟨918773, by rfl⟩ : syracuseStep 78402005 = 1837547) (by norm_num)
theorem B52268003 : Blo 2147435 52268003 := bstep (se 1 (by rfl) ⟨39201002, by rfl⟩ : syracuseStep 52268003 = 78402005) B78402005
theorem B34845335 : Blo 2147435 34845335 := bstep (se 1 (by rfl) ⟨26134001, by rfl⟩ : syracuseStep 34845335 = 52268003) B52268003
theorem B23230223 : Blo 2147435 23230223 := bstep (se 1 (by rfl) ⟨17422667, by rfl⟩ : syracuseStep 23230223 = 34845335) B34845335
theorem B15486815 : Blo 2147435 15486815 := bstep (se 1 (by rfl) ⟨11615111, by rfl⟩ : syracuseStep 15486815 = 23230223) B23230223
theorem B10324543 : Blo 2147435 10324543 := bstep (se 1 (by rfl) ⟨7743407, by rfl⟩ : syracuseStep 10324543 = 15486815) B15486815
theorem B13766057 : Blo 2147435 13766057 := bstep (se 2 (by rfl) ⟨5162271, by rfl⟩ : syracuseStep 13766057 = 10324543) B10324543
theorem B9177371 : Blo 2147435 9177371 := bstep (se 1 (by rfl) ⟨6883028, by rfl⟩ : syracuseStep 9177371 = 13766057) B13766057
theorem B6118247 : Blo 2147435 6118247 := bstep (se 1 (by rfl) ⟨4588685, by rfl⟩ : syracuseStep 6118247 = 9177371) B9177371
theorem B4078831 : Blo 2147435 4078831 := bstep (se 1 (by rfl) ⟨3059123, by rfl⟩ : syracuseStep 4078831 = 6118247) B6118247
theorem B5438441 : Blo 2147435 5438441 := bstep (se 2 (by rfl) ⟨2039415, by rfl⟩ : syracuseStep 5438441 = 4078831) B4078831
theorem B3625627 : Blo 2147435 3625627 := bstep (se 1 (by rfl) ⟨2719220, by rfl⟩ : syracuseStep 3625627 = 5438441) B5438441
theorem B4834169 : Blo 2147435 4834169 := bstep (se 2 (by rfl) ⟨1812813, by rfl⟩ : syracuseStep 4834169 = 3625627) B3625627
theorem B3222779 : Blo 2147435 3222779 := bstep (se 1 (by rfl) ⟨2417084, by rfl⟩ : syracuseStep 3222779 = 4834169) B4834169
theorem B2148519 : Blo 2147435 2148519 := bstep (se 1 (by rfl) ⟨1611389, by rfl⟩ : syracuseStep 2148519 = 3222779) B3222779
theorem B2417089 : Blo 2147435 2417089 := bbase (se 2 (by rfl) ⟨906408, by rfl⟩ : syracuseStep 2417089 = 1812817) (by norm_num)
theorem B3222785 : Blo 2147435 3222785 := bstep (se 2 (by rfl) ⟨1208544, by rfl⟩ : syracuseStep 3222785 = 2417089) B2417089
theorem B2148523 : Blo 2147435 2148523 := bstep (se 1 (by rfl) ⟨1611392, by rfl⟩ : syracuseStep 2148523 = 3222785) B3222785
theorem B5438461 : Blo 2147435 5438461 := bbase (se 3 (by rfl) ⟨1019711, by rfl⟩ : syracuseStep 5438461 = 2039423) (by norm_num)
theorem B7251281 : Blo 2147435 7251281 := bstep (se 2 (by rfl) ⟨2719230, by rfl⟩ : syracuseStep 7251281 = 5438461) B5438461
theorem B4834187 : Blo 2147435 4834187 := bstep (se 1 (by rfl) ⟨3625640, by rfl⟩ : syracuseStep 4834187 = 7251281) B7251281
theorem B3222791 : Blo 2147435 3222791 := bstep (se 1 (by rfl) ⟨2417093, by rfl⟩ : syracuseStep 3222791 = 4834187) B4834187
theorem B2148527 : Blo 2147435 2148527 := bstep (se 1 (by rfl) ⟨1611395, by rfl⟩ : syracuseStep 2148527 = 3222791) B3222791
theorem B3222797 : Blo 2147435 3222797 := bbase (se 3 (by rfl) ⟨604274, by rfl⟩ : syracuseStep 3222797 = 1208549) (by norm_num)
theorem B2148531 : Blo 2147435 2148531 := bstep (se 1 (by rfl) ⟨1611398, by rfl⟩ : syracuseStep 2148531 = 3222797) B3222797
theorem B4834205 : Blo 2147435 4834205 := bbase (se 3 (by rfl) ⟨906413, by rfl⟩ : syracuseStep 4834205 = 1812827) (by norm_num)
theorem B3222803 : Blo 2147435 3222803 := bstep (se 1 (by rfl) ⟨2417102, by rfl⟩ : syracuseStep 3222803 = 4834205) B4834205
theorem B2148535 : Blo 2147435 2148535 := bstep (se 1 (by rfl) ⟨1611401, by rfl⟩ : syracuseStep 2148535 = 3222803) B3222803
theorem B3625661 : Blo 2147435 3625661 := bbase (se 3 (by rfl) ⟨679811, by rfl⟩ : syracuseStep 3625661 = 1359623) (by norm_num)
theorem B2417107 : Blo 2147435 2417107 := bstep (se 1 (by rfl) ⟨1812830, by rfl⟩ : syracuseStep 2417107 = 3625661) B3625661
theorem B3222809 : Blo 2147435 3222809 := bstep (se 2 (by rfl) ⟨1208553, by rfl⟩ : syracuseStep 3222809 = 2417107) B2417107
theorem B2148539 : Blo 2147435 2148539 := bstep (se 1 (by rfl) ⟨1611404, by rfl⟩ : syracuseStep 2148539 = 3222809) B3222809
theorem B12236629 : Blo 2147435 12236629 := bbase (se 9 (by rfl) ⟨35849, by rfl⟩ : syracuseStep 12236629 = 71699) (by norm_num)
theorem B16315505 : Blo 2147435 16315505 := bstep (se 2 (by rfl) ⟨6118314, by rfl⟩ : syracuseStep 16315505 = 12236629) B12236629
theorem B10877003 : Blo 2147435 10877003 := bstep (se 1 (by rfl) ⟨8157752, by rfl⟩ : syracuseStep 10877003 = 16315505) B16315505
theorem B7251335 : Blo 2147435 7251335 := bstep (se 1 (by rfl) ⟨5438501, by rfl⟩ : syracuseStep 7251335 = 10877003) B10877003
theorem B4834223 : Blo 2147435 4834223 := bstep (se 1 (by rfl) ⟨3625667, by rfl⟩ : syracuseStep 4834223 = 7251335) B7251335
theorem B3222815 : Blo 2147435 3222815 := bstep (se 1 (by rfl) ⟨2417111, by rfl⟩ : syracuseStep 3222815 = 4834223) B4834223
theorem B2148543 : Blo 2147435 2148543 := bstep (se 1 (by rfl) ⟨1611407, by rfl⟩ : syracuseStep 2148543 = 3222815) B3222815
theorem B3222821 : Blo 2147435 3222821 := bbase (se 4 (by rfl) ⟨302139, by rfl⟩ : syracuseStep 3222821 = 604279) (by norm_num)
theorem B2148547 : Blo 2147435 2148547 := bstep (se 1 (by rfl) ⟨1611410, by rfl⟩ : syracuseStep 2148547 = 3222821) B3222821
theorem B2719261 : Blo 2147435 2719261 := bbase (se 3 (by rfl) ⟨509861, by rfl⟩ : syracuseStep 2719261 = 1019723) (by norm_num)
theorem B3625681 : Blo 2147435 3625681 := bstep (se 2 (by rfl) ⟨1359630, by rfl⟩ : syracuseStep 3625681 = 2719261) B2719261
theorem B4834241 : Blo 2147435 4834241 := bstep (se 2 (by rfl) ⟨1812840, by rfl⟩ : syracuseStep 4834241 = 3625681) B3625681
theorem B3222827 : Blo 2147435 3222827 := bstep (se 1 (by rfl) ⟨2417120, by rfl⟩ : syracuseStep 3222827 = 4834241) B4834241
theorem B2148551 : Blo 2147435 2148551 := bstep (se 1 (by rfl) ⟨1611413, by rfl⟩ : syracuseStep 2148551 = 3222827) B3222827
theorem B2417125 : Blo 2147435 2417125 := bbase (se 4 (by rfl) ⟨226605, by rfl⟩ : syracuseStep 2417125 = 453211) (by norm_num)
theorem B3222833 : Blo 2147435 3222833 := bstep (se 2 (by rfl) ⟨1208562, by rfl⟩ : syracuseStep 3222833 = 2417125) B2417125
theorem B2148555 : Blo 2147435 2148555 := bstep (se 1 (by rfl) ⟨1611416, by rfl⟩ : syracuseStep 2148555 = 3222833) B3222833
theorem B6883157 : Blo 2147435 6883157 := bbase (se 9 (by rfl) ⟨20165, by rfl⟩ : syracuseStep 6883157 = 40331) (by norm_num)
theorem B4588771 : Blo 2147435 4588771 := bstep (se 1 (by rfl) ⟨3441578, by rfl⟩ : syracuseStep 4588771 = 6883157) B6883157
theorem B6118361 : Blo 2147435 6118361 := bstep (se 2 (by rfl) ⟨2294385, by rfl⟩ : syracuseStep 6118361 = 4588771) B4588771
theorem B4078907 : Blo 2147435 4078907 := bstep (se 1 (by rfl) ⟨3059180, by rfl⟩ : syracuseStep 4078907 = 6118361) B6118361
theorem B2719271 : Blo 2147435 2719271 := bstep (se 1 (by rfl) ⟨2039453, by rfl⟩ : syracuseStep 2719271 = 4078907) B4078907
theorem B7251389 : Blo 2147435 7251389 := bstep (se 3 (by rfl) ⟨1359635, by rfl⟩ : syracuseStep 7251389 = 2719271) B2719271
theorem B4834259 : Blo 2147435 4834259 := bstep (se 1 (by rfl) ⟨3625694, by rfl⟩ : syracuseStep 4834259 = 7251389) B7251389
theorem B3222839 : Blo 2147435 3222839 := bstep (se 1 (by rfl) ⟨2417129, by rfl⟩ : syracuseStep 3222839 = 4834259) B4834259
theorem B2148559 : Blo 2147435 2148559 := bstep (se 1 (by rfl) ⟨1611419, by rfl⟩ : syracuseStep 2148559 = 3222839) B3222839
theorem B3222845 : Blo 2147435 3222845 := bbase (se 3 (by rfl) ⟨604283, by rfl⟩ : syracuseStep 3222845 = 1208567) (by norm_num)
theorem B2148563 : Blo 2147435 2148563 := bstep (se 1 (by rfl) ⟨1611422, by rfl⟩ : syracuseStep 2148563 = 3222845) B3222845
theorem B4834277 : Blo 2147435 4834277 := bbase (se 4 (by rfl) ⟨453213, by rfl⟩ : syracuseStep 4834277 = 906427) (by norm_num)
theorem B3222851 : Blo 2147435 3222851 := bstep (se 1 (by rfl) ⟨2417138, by rfl⟩ : syracuseStep 3222851 = 4834277) B4834277
theorem B2148567 : Blo 2147435 2148567 := bstep (se 1 (by rfl) ⟨1611425, by rfl⟩ : syracuseStep 2148567 = 3222851) B3222851
theorem B5438573 : Blo 2147435 5438573 := bbase (se 3 (by rfl) ⟨1019732, by rfl⟩ : syracuseStep 5438573 = 2039465) (by norm_num)
theorem B3625715 : Blo 2147435 3625715 := bstep (se 1 (by rfl) ⟨2719286, by rfl⟩ : syracuseStep 3625715 = 5438573) B5438573
theorem B2417143 : Blo 2147435 2417143 := bstep (se 1 (by rfl) ⟨1812857, by rfl⟩ : syracuseStep 2417143 = 3625715) B3625715
theorem B3222857 : Blo 2147435 3222857 := bstep (se 2 (by rfl) ⟨1208571, by rfl⟩ : syracuseStep 3222857 = 2417143) B2417143
theorem B2148571 : Blo 2147435 2148571 := bstep (se 1 (by rfl) ⟨1611428, by rfl⟩ : syracuseStep 2148571 = 3222857) B3222857
theorem B4588805 : Blo 2147435 4588805 := bbase (se 4 (by rfl) ⟨430200, by rfl⟩ : syracuseStep 4588805 = 860401) (by norm_num)
theorem B3059203 : Blo 2147435 3059203 := bstep (se 1 (by rfl) ⟨2294402, by rfl⟩ : syracuseStep 3059203 = 4588805) B4588805
theorem B4078937 : Blo 2147435 4078937 := bstep (se 2 (by rfl) ⟨1529601, by rfl⟩ : syracuseStep 4078937 = 3059203) B3059203
theorem B10877165 : Blo 2147435 10877165 := bstep (se 3 (by rfl) ⟨2039468, by rfl⟩ : syracuseStep 10877165 = 4078937) B4078937
theorem B7251443 : Blo 2147435 7251443 := bstep (se 1 (by rfl) ⟨5438582, by rfl⟩ : syracuseStep 7251443 = 10877165) B10877165
theorem B4834295 : Blo 2147435 4834295 := bstep (se 1 (by rfl) ⟨3625721, by rfl⟩ : syracuseStep 4834295 = 7251443) B7251443
theorem B3222863 : Blo 2147435 3222863 := bstep (se 1 (by rfl) ⟨2417147, by rfl⟩ : syracuseStep 3222863 = 4834295) B4834295
theorem B2148575 : Blo 2147435 2148575 := bstep (se 1 (by rfl) ⟨1611431, by rfl⟩ : syracuseStep 2148575 = 3222863) B3222863
theorem B3222869 : Blo 2147435 3222869 := bbase (se 11 (by rfl) ⟨2360, by rfl⟩ : syracuseStep 3222869 = 4721) (by norm_num)
theorem B2148579 : Blo 2147435 2148579 := bstep (se 1 (by rfl) ⟨1611434, by rfl⟩ : syracuseStep 2148579 = 3222869) B3222869
theorem B2581213 : Blo 2147435 2581213 := bbase (se 3 (by rfl) ⟨483977, by rfl⟩ : syracuseStep 2581213 = 967955) (by norm_num)
theorem B3441617 : Blo 2147435 3441617 := bstep (se 2 (by rfl) ⟨1290606, by rfl⟩ : syracuseStep 3441617 = 2581213) B2581213
theorem B2294411 : Blo 2147435 2294411 := bstep (se 1 (by rfl) ⟨1720808, by rfl⟩ : syracuseStep 2294411 = 3441617) B3441617
theorem B6118429 : Blo 2147435 6118429 := bstep (se 3 (by rfl) ⟨1147205, by rfl⟩ : syracuseStep 6118429 = 2294411) B2294411
theorem B8157905 : Blo 2147435 8157905 := bstep (se 2 (by rfl) ⟨3059214, by rfl⟩ : syracuseStep 8157905 = 6118429) B6118429
theorem B5438603 : Blo 2147435 5438603 := bstep (se 1 (by rfl) ⟨4078952, by rfl⟩ : syracuseStep 5438603 = 8157905) B8157905
theorem B3625735 : Blo 2147435 3625735 := bstep (se 1 (by rfl) ⟨2719301, by rfl⟩ : syracuseStep 3625735 = 5438603) B5438603
theorem B4834313 : Blo 2147435 4834313 := bstep (se 2 (by rfl) ⟨1812867, by rfl⟩ : syracuseStep 4834313 = 3625735) B3625735
theorem B3222875 : Blo 2147435 3222875 := bstep (se 1 (by rfl) ⟨2417156, by rfl⟩ : syracuseStep 3222875 = 4834313) B4834313
theorem B2148583 : Blo 2147435 2148583 := bstep (se 1 (by rfl) ⟨1611437, by rfl⟩ : syracuseStep 2148583 = 3222875) B3222875
theorem B2417161 : Blo 2147435 2417161 := bbase (se 2 (by rfl) ⟨906435, by rfl⟩ : syracuseStep 2417161 = 1812871) (by norm_num)
theorem B3222881 : Blo 2147435 3222881 := bstep (se 2 (by rfl) ⟨1208580, by rfl⟩ : syracuseStep 3222881 = 2417161) B2417161
theorem B2148587 : Blo 2147435 2148587 := bstep (se 1 (by rfl) ⟨1611440, by rfl⟩ : syracuseStep 2148587 = 3222881) B3222881
theorem B2207621 : Blo 2147435 2207621 := bbase (se 4 (by rfl) ⟨206964, by rfl⟩ : syracuseStep 2207621 = 413929) (by norm_num)
theorem B5886989 : Blo 2147435 5886989 := bstep (se 3 (by rfl) ⟨1103810, by rfl⟩ : syracuseStep 5886989 = 2207621) B2207621
theorem B3924659 : Blo 2147435 3924659 := bstep (se 1 (by rfl) ⟨2943494, by rfl⟩ : syracuseStep 3924659 = 5886989) B5886989
theorem B10465757 : Blo 2147435 10465757 := bstep (se 3 (by rfl) ⟨1962329, by rfl⟩ : syracuseStep 10465757 = 3924659) B3924659
theorem B6977171 : Blo 2147435 6977171 := bstep (se 1 (by rfl) ⟨5232878, by rfl⟩ : syracuseStep 6977171 = 10465757) B10465757
theorem B4651447 : Blo 2147435 4651447 := bstep (se 1 (by rfl) ⟨3488585, by rfl⟩ : syracuseStep 4651447 = 6977171) B6977171
theorem B6201929 : Blo 2147435 6201929 := bstep (se 2 (by rfl) ⟨2325723, by rfl⟩ : syracuseStep 6201929 = 4651447) B4651447
theorem B4134619 : Blo 2147435 4134619 := bstep (se 1 (by rfl) ⟨3100964, by rfl⟩ : syracuseStep 4134619 = 6201929) B6201929
theorem B5512825 : Blo 2147435 5512825 := bstep (se 2 (by rfl) ⟨2067309, by rfl⟩ : syracuseStep 5512825 = 4134619) B4134619
theorem B7350433 : Blo 2147435 7350433 := bstep (se 2 (by rfl) ⟨2756412, by rfl⟩ : syracuseStep 7350433 = 5512825) B5512825
theorem B39202309 : Blo 2147435 39202309 := bstep (se 4 (by rfl) ⟨3675216, by rfl⟩ : syracuseStep 39202309 = 7350433) B7350433
theorem B52269745 : Blo 2147435 52269745 := bstep (se 2 (by rfl) ⟨19601154, by rfl⟩ : syracuseStep 52269745 = 39202309) B39202309
theorem B69692993 : Blo 2147435 69692993 := bstep (se 2 (by rfl) ⟨26134872, by rfl⟩ : syracuseStep 69692993 = 52269745) B52269745
theorem B46461995 : Blo 2147435 46461995 := bstep (se 1 (by rfl) ⟨34846496, by rfl⟩ : syracuseStep 46461995 = 69692993) B69692993
theorem B30974663 : Blo 2147435 30974663 := bstep (se 1 (by rfl) ⟨23230997, by rfl⟩ : syracuseStep 30974663 = 46461995) B46461995
theorem B20649775 : Blo 2147435 20649775 := bstep (se 1 (by rfl) ⟨15487331, by rfl⟩ : syracuseStep 20649775 = 30974663) B30974663
theorem B27533033 : Blo 2147435 27533033 := bstep (se 2 (by rfl) ⟨10324887, by rfl⟩ : syracuseStep 27533033 = 20649775) B20649775
theorem B18355355 : Blo 2147435 18355355 := bstep (se 1 (by rfl) ⟨13766516, by rfl⟩ : syracuseStep 18355355 = 27533033) B27533033
theorem B12236903 : Blo 2147435 12236903 := bstep (se 1 (by rfl) ⟨9177677, by rfl⟩ : syracuseStep 12236903 = 18355355) B18355355
theorem B8157935 : Blo 2147435 8157935 := bstep (se 1 (by rfl) ⟨6118451, by rfl⟩ : syracuseStep 8157935 = 12236903) B12236903
theorem B5438623 : Blo 2147435 5438623 := bstep (se 1 (by rfl) ⟨4078967, by rfl⟩ : syracuseStep 5438623 = 8157935) B8157935
theorem B7251497 : Blo 2147435 7251497 := bstep (se 2 (by rfl) ⟨2719311, by rfl⟩ : syracuseStep 7251497 = 5438623) B5438623
theorem B4834331 : Blo 2147435 4834331 := bstep (se 1 (by rfl) ⟨3625748, by rfl⟩ : syracuseStep 4834331 = 7251497) B7251497
theorem B3222887 : Blo 2147435 3222887 := bstep (se 1 (by rfl) ⟨2417165, by rfl⟩ : syracuseStep 3222887 = 4834331) B4834331
theorem B2148591 : Blo 2147435 2148591 := bstep (se 1 (by rfl) ⟨1611443, by rfl⟩ : syracuseStep 2148591 = 3222887) B3222887
theorem B3222893 : Blo 2147435 3222893 := bbase (se 3 (by rfl) ⟨604292, by rfl⟩ : syracuseStep 3222893 = 1208585) (by norm_num)
theorem B2148595 : Blo 2147435 2148595 := bstep (se 1 (by rfl) ⟨1611446, by rfl⟩ : syracuseStep 2148595 = 3222893) B3222893
theorem B4834349 : Blo 2147435 4834349 := bbase (se 3 (by rfl) ⟨906440, by rfl⟩ : syracuseStep 4834349 = 1812881) (by norm_num)
theorem B3222899 : Blo 2147435 3222899 := bstep (se 1 (by rfl) ⟨2417174, by rfl⟩ : syracuseStep 3222899 = 4834349) B4834349
theorem B2148599 : Blo 2147435 2148599 := bstep (se 1 (by rfl) ⟨1611449, by rfl⟩ : syracuseStep 2148599 = 3222899) B3222899
theorem B2581237 : Blo 2147435 2581237 := bbase (se 5 (by rfl) ⟨120995, by rfl⟩ : syracuseStep 2581237 = 241991) (by norm_num)
theorem B13766597 : Blo 2147435 13766597 := bstep (se 4 (by rfl) ⟨1290618, by rfl⟩ : syracuseStep 13766597 = 2581237) B2581237
theorem B9177731 : Blo 2147435 9177731 := bstep (se 1 (by rfl) ⟨6883298, by rfl⟩ : syracuseStep 9177731 = 13766597) B13766597
theorem B6118487 : Blo 2147435 6118487 := bstep (se 1 (by rfl) ⟨4588865, by rfl⟩ : syracuseStep 6118487 = 9177731) B9177731
theorem B4078991 : Blo 2147435 4078991 := bstep (se 1 (by rfl) ⟨3059243, by rfl⟩ : syracuseStep 4078991 = 6118487) B6118487
theorem B2719327 : Blo 2147435 2719327 := bstep (se 1 (by rfl) ⟨2039495, by rfl⟩ : syracuseStep 2719327 = 4078991) B4078991
theorem B3625769 : Blo 2147435 3625769 := bstep (se 2 (by rfl) ⟨1359663, by rfl⟩ : syracuseStep 3625769 = 2719327) B2719327
theorem B2417179 : Blo 2147435 2417179 := bstep (se 1 (by rfl) ⟨1812884, by rfl⟩ : syracuseStep 2417179 = 3625769) B3625769
theorem B3222905 : Blo 2147435 3222905 := bstep (se 2 (by rfl) ⟨1208589, by rfl⟩ : syracuseStep 3222905 = 2417179) B2417179
theorem B2148603 : Blo 2147435 2148603 := bstep (se 1 (by rfl) ⟨1611452, by rfl⟩ : syracuseStep 2148603 = 3222905) B3222905
theorem B2581241 : Blo 2147435 2581241 := bbase (se 2 (by rfl) ⟨967965, by rfl⟩ : syracuseStep 2581241 = 1935931) (by norm_num)
theorem B6883309 : Blo 2147435 6883309 := bstep (se 3 (by rfl) ⟨1290620, by rfl⟩ : syracuseStep 6883309 = 2581241) B2581241
theorem B36710981 : Blo 2147435 36710981 := bstep (se 4 (by rfl) ⟨3441654, by rfl⟩ : syracuseStep 36710981 = 6883309) B6883309
theorem B24473987 : Blo 2147435 24473987 := bstep (se 1 (by rfl) ⟨18355490, by rfl⟩ : syracuseStep 24473987 = 36710981) B36710981
theorem B16315991 : Blo 2147435 16315991 := bstep (se 1 (by rfl) ⟨12236993, by rfl⟩ : syracuseStep 16315991 = 24473987) B24473987
theorem B10877327 : Blo 2147435 10877327 := bstep (se 1 (by rfl) ⟨8157995, by rfl⟩ : syracuseStep 10877327 = 16315991) B16315991
theorem B7251551 : Blo 2147435 7251551 := bstep (se 1 (by rfl) ⟨5438663, by rfl⟩ : syracuseStep 7251551 = 10877327) B10877327
theorem B4834367 : Blo 2147435 4834367 := bstep (se 1 (by rfl) ⟨3625775, by rfl⟩ : syracuseStep 4834367 = 7251551) B7251551
theorem B3222911 : Blo 2147435 3222911 := bstep (se 1 (by rfl) ⟨2417183, by rfl⟩ : syracuseStep 3222911 = 4834367) B4834367
theorem B2148607 : Blo 2147435 2148607 := bstep (se 1 (by rfl) ⟨1611455, by rfl⟩ : syracuseStep 2148607 = 3222911) B3222911
theorem B3222917 : Blo 2147435 3222917 := bbase (se 4 (by rfl) ⟨302148, by rfl⟩ : syracuseStep 3222917 = 604297) (by norm_num)
theorem B2148611 : Blo 2147435 2148611 := bstep (se 1 (by rfl) ⟨1611458, by rfl⟩ : syracuseStep 2148611 = 3222917) B3222917
theorem B3625789 : Blo 2147435 3625789 := bbase (se 3 (by rfl) ⟨679835, by rfl⟩ : syracuseStep 3625789 = 1359671) (by norm_num)
theorem B4834385 : Blo 2147435 4834385 := bstep (se 2 (by rfl) ⟨1812894, by rfl⟩ : syracuseStep 4834385 = 3625789) B3625789
theorem B3222923 : Blo 2147435 3222923 := bstep (se 1 (by rfl) ⟨2417192, by rfl⟩ : syracuseStep 3222923 = 4834385) B4834385
theorem B2148615 : Blo 2147435 2148615 := bstep (se 1 (by rfl) ⟨1611461, by rfl⟩ : syracuseStep 2148615 = 3222923) B3222923
theorem B2417197 : Blo 2147435 2417197 := bbase (se 3 (by rfl) ⟨453224, by rfl⟩ : syracuseStep 2417197 = 906449) (by norm_num)
theorem B3222929 : Blo 2147435 3222929 := bstep (se 2 (by rfl) ⟨1208598, by rfl⟩ : syracuseStep 3222929 = 2417197) B2417197
theorem B2148619 : Blo 2147435 2148619 := bstep (se 1 (by rfl) ⟨1611464, by rfl⟩ : syracuseStep 2148619 = 3222929) B3222929
theorem B7251605 : Blo 2147435 7251605 := bbase (se 6 (by rfl) ⟨169959, by rfl⟩ : syracuseStep 7251605 = 339919) (by norm_num)
theorem B4834403 : Blo 2147435 4834403 := bstep (se 1 (by rfl) ⟨3625802, by rfl⟩ : syracuseStep 4834403 = 7251605) B7251605
theorem B3222935 : Blo 2147435 3222935 := bstep (se 1 (by rfl) ⟨2417201, by rfl⟩ : syracuseStep 3222935 = 4834403) B4834403
theorem B2148623 : Blo 2147435 2148623 := bstep (se 1 (by rfl) ⟨1611467, by rfl⟩ : syracuseStep 2148623 = 3222935) B3222935
theorem B3222941 : Blo 2147435 3222941 := bbase (se 3 (by rfl) ⟨604301, by rfl⟩ : syracuseStep 3222941 = 1208603) (by norm_num)
theorem B2148627 : Blo 2147435 2148627 := bstep (se 1 (by rfl) ⟨1611470, by rfl⟩ : syracuseStep 2148627 = 3222941) B3222941
theorem B4834421 : Blo 2147435 4834421 := bbase (se 5 (by rfl) ⟨226613, by rfl⟩ : syracuseStep 4834421 = 453227) (by norm_num)
theorem B3222947 : Blo 2147435 3222947 := bstep (se 1 (by rfl) ⟨2417210, by rfl⟩ : syracuseStep 3222947 = 4834421) B4834421
theorem B2148631 : Blo 2147435 2148631 := bstep (se 1 (by rfl) ⟨1611473, by rfl⟩ : syracuseStep 2148631 = 3222947) B3222947
theorem B18355733 : Blo 2147435 18355733 := bbase (se 6 (by rfl) ⟨430212, by rfl⟩ : syracuseStep 18355733 = 860425) (by norm_num)
theorem B12237155 : Blo 2147435 12237155 := bstep (se 1 (by rfl) ⟨9177866, by rfl⟩ : syracuseStep 12237155 = 18355733) B18355733
theorem B8158103 : Blo 2147435 8158103 := bstep (se 1 (by rfl) ⟨6118577, by rfl⟩ : syracuseStep 8158103 = 12237155) B12237155
theorem B5438735 : Blo 2147435 5438735 := bstep (se 1 (by rfl) ⟨4079051, by rfl⟩ : syracuseStep 5438735 = 8158103) B8158103
theorem B3625823 : Blo 2147435 3625823 := bstep (se 1 (by rfl) ⟨2719367, by rfl⟩ : syracuseStep 3625823 = 5438735) B5438735
theorem B2417215 : Blo 2147435 2417215 := bstep (se 1 (by rfl) ⟨1812911, by rfl⟩ : syracuseStep 2417215 = 3625823) B3625823
theorem B3222953 : Blo 2147435 3222953 := bstep (se 2 (by rfl) ⟨1208607, by rfl⟩ : syracuseStep 3222953 = 2417215) B2417215
theorem B2148635 : Blo 2147435 2148635 := bstep (se 1 (by rfl) ⟨1611476, by rfl⟩ : syracuseStep 2148635 = 3222953) B3222953
theorem B8158117 : Blo 2147435 8158117 := bbase (se 4 (by rfl) ⟨764823, by rfl⟩ : syracuseStep 8158117 = 1529647) (by norm_num)
theorem B10877489 : Blo 2147435 10877489 := bstep (se 2 (by rfl) ⟨4079058, by rfl⟩ : syracuseStep 10877489 = 8158117) B8158117
theorem B7251659 : Blo 2147435 7251659 := bstep (se 1 (by rfl) ⟨5438744, by rfl⟩ : syracuseStep 7251659 = 10877489) B10877489
theorem B4834439 : Blo 2147435 4834439 := bstep (se 1 (by rfl) ⟨3625829, by rfl⟩ : syracuseStep 4834439 = 7251659) B7251659
theorem B3222959 : Blo 2147435 3222959 := bstep (se 1 (by rfl) ⟨2417219, by rfl⟩ : syracuseStep 3222959 = 4834439) B4834439
theorem B2148639 : Blo 2147435 2148639 := bstep (se 1 (by rfl) ⟨1611479, by rfl⟩ : syracuseStep 2148639 = 3222959) B3222959
theorem B3222965 : Blo 2147435 3222965 := bbase (se 5 (by rfl) ⟨151076, by rfl⟩ : syracuseStep 3222965 = 302153) (by norm_num)
theorem B2148643 : Blo 2147435 2148643 := bstep (se 1 (by rfl) ⟨1611482, by rfl⟩ : syracuseStep 2148643 = 3222965) B3222965
theorem B5438765 : Blo 2147435 5438765 := bbase (se 3 (by rfl) ⟨1019768, by rfl⟩ : syracuseStep 5438765 = 2039537) (by norm_num)
theorem B3625843 : Blo 2147435 3625843 := bstep (se 1 (by rfl) ⟨2719382, by rfl⟩ : syracuseStep 3625843 = 5438765) B5438765
theorem B4834457 : Blo 2147435 4834457 := bstep (se 2 (by rfl) ⟨1812921, by rfl⟩ : syracuseStep 4834457 = 3625843) B3625843
theorem B3222971 : Blo 2147435 3222971 := bstep (se 1 (by rfl) ⟨2417228, by rfl⟩ : syracuseStep 3222971 = 4834457) B4834457
theorem B2148647 : Blo 2147435 2148647 := bstep (se 1 (by rfl) ⟨1611485, by rfl⟩ : syracuseStep 2148647 = 3222971) B3222971
theorem B2417233 : Blo 2147435 2417233 := bbase (se 2 (by rfl) ⟨906462, by rfl⟩ : syracuseStep 2417233 = 1812925) (by norm_num)
theorem B3222977 : Blo 2147435 3222977 := bstep (se 2 (by rfl) ⟨1208616, by rfl⟩ : syracuseStep 3222977 = 2417233) B2417233
theorem B2148651 : Blo 2147435 2148651 := bstep (se 1 (by rfl) ⟨1611488, by rfl⟩ : syracuseStep 2148651 = 3222977) B3222977
theorem B3059317 : Blo 2147435 3059317 := bbase (se 5 (by rfl) ⟨143405, by rfl⟩ : syracuseStep 3059317 = 286811) (by norm_num)
theorem B4079089 : Blo 2147435 4079089 := bstep (se 2 (by rfl) ⟨1529658, by rfl⟩ : syracuseStep 4079089 = 3059317) B3059317
theorem B5438785 : Blo 2147435 5438785 := bstep (se 2 (by rfl) ⟨2039544, by rfl⟩ : syracuseStep 5438785 = 4079089) B4079089
theorem B7251713 : Blo 2147435 7251713 := bstep (se 2 (by rfl) ⟨2719392, by rfl⟩ : syracuseStep 7251713 = 5438785) B5438785
theorem B4834475 : Blo 2147435 4834475 := bstep (se 1 (by rfl) ⟨3625856, by rfl⟩ : syracuseStep 4834475 = 7251713) B7251713
theorem B3222983 : Blo 2147435 3222983 := bstep (se 1 (by rfl) ⟨2417237, by rfl⟩ : syracuseStep 3222983 = 4834475) B4834475
theorem B2148655 : Blo 2147435 2148655 := bstep (se 1 (by rfl) ⟨1611491, by rfl⟩ : syracuseStep 2148655 = 3222983) B3222983
theorem B3222989 : Blo 2147435 3222989 := bbase (se 3 (by rfl) ⟨604310, by rfl⟩ : syracuseStep 3222989 = 1208621) (by norm_num)
theorem B2148659 : Blo 2147435 2148659 := bstep (se 1 (by rfl) ⟨1611494, by rfl⟩ : syracuseStep 2148659 = 3222989) B3222989
theorem B4834493 : Blo 2147435 4834493 := bbase (se 3 (by rfl) ⟨906467, by rfl⟩ : syracuseStep 4834493 = 1812935) (by norm_num)
theorem B3222995 : Blo 2147435 3222995 := bstep (se 1 (by rfl) ⟨2417246, by rfl⟩ : syracuseStep 3222995 = 4834493) B4834493
theorem B2148663 : Blo 2147435 2148663 := bstep (se 1 (by rfl) ⟨1611497, by rfl⟩ : syracuseStep 2148663 = 3222995) B3222995
theorem B3625877 : Blo 2147435 3625877 := bbase (se 6 (by rfl) ⟨84981, by rfl⟩ : syracuseStep 3625877 = 169963) (by norm_num)
theorem B2417251 : Blo 2147435 2417251 := bstep (se 1 (by rfl) ⟨1812938, by rfl⟩ : syracuseStep 2417251 = 3625877) B3625877
theorem B3223001 : Blo 2147435 3223001 := bstep (se 2 (by rfl) ⟨1208625, by rfl⟩ : syracuseStep 3223001 = 2417251) B2417251
theorem B2148667 : Blo 2147435 2148667 := bstep (se 1 (by rfl) ⟨1611500, by rfl⟩ : syracuseStep 2148667 = 3223001) B3223001
theorem B13767029 : Blo 2147435 13767029 := bbase (se 5 (by rfl) ⟨645329, by rfl⟩ : syracuseStep 13767029 = 1290659) (by norm_num)
theorem B9178019 : Blo 2147435 9178019 := bstep (se 1 (by rfl) ⟨6883514, by rfl⟩ : syracuseStep 9178019 = 13767029) B13767029
theorem B6118679 : Blo 2147435 6118679 := bstep (se 1 (by rfl) ⟨4589009, by rfl⟩ : syracuseStep 6118679 = 9178019) B9178019
theorem B16316477 : Blo 2147435 16316477 := bstep (se 3 (by rfl) ⟨3059339, by rfl⟩ : syracuseStep 16316477 = 6118679) B6118679
theorem B10877651 : Blo 2147435 10877651 := bstep (se 1 (by rfl) ⟨8158238, by rfl⟩ : syracuseStep 10877651 = 16316477) B16316477
theorem B7251767 : Blo 2147435 7251767 := bstep (se 1 (by rfl) ⟨5438825, by rfl⟩ : syracuseStep 7251767 = 10877651) B10877651
theorem B4834511 : Blo 2147435 4834511 := bstep (se 1 (by rfl) ⟨3625883, by rfl⟩ : syracuseStep 4834511 = 7251767) B7251767
theorem B3223007 : Blo 2147435 3223007 := bstep (se 1 (by rfl) ⟨2417255, by rfl⟩ : syracuseStep 3223007 = 4834511) B4834511
theorem B2148671 : Blo 2147435 2148671 := bstep (se 1 (by rfl) ⟨1611503, by rfl⟩ : syracuseStep 2148671 = 3223007) B3223007
theorem B3223013 : Blo 2147435 3223013 := bbase (se 4 (by rfl) ⟨302157, by rfl⟩ : syracuseStep 3223013 = 604315) (by norm_num)
theorem B2148675 : Blo 2147435 2148675 := bstep (se 1 (by rfl) ⟨1611506, by rfl⟩ : syracuseStep 2148675 = 3223013) B3223013
theorem B16539157 : Blo 2147435 16539157 := bbase (se 6 (by rfl) ⟨387636, by rfl⟩ : syracuseStep 16539157 = 775273) (by norm_num)
theorem B22052209 : Blo 2147435 22052209 := bstep (se 2 (by rfl) ⟨8269578, by rfl⟩ : syracuseStep 22052209 = 16539157) B16539157
theorem B29402945 : Blo 2147435 29402945 := bstep (se 2 (by rfl) ⟨11026104, by rfl⟩ : syracuseStep 29402945 = 22052209) B22052209
theorem B19601963 : Blo 2147435 19601963 := bstep (se 1 (by rfl) ⟨14701472, by rfl⟩ : syracuseStep 19601963 = 29402945) B29402945
theorem B13067975 : Blo 2147435 13067975 := bstep (se 1 (by rfl) ⟨9800981, by rfl⟩ : syracuseStep 13067975 = 19601963) B19601963
theorem B8711983 : Blo 2147435 8711983 := bstep (se 1 (by rfl) ⟨6533987, by rfl⟩ : syracuseStep 8711983 = 13067975) B13067975
theorem B11615977 : Blo 2147435 11615977 := bstep (se 2 (by rfl) ⟨4355991, by rfl⟩ : syracuseStep 11615977 = 8711983) B8711983
theorem B15487969 : Blo 2147435 15487969 := bstep (se 2 (by rfl) ⟨5807988, by rfl⟩ : syracuseStep 15487969 = 11615977) B11615977
theorem B20650625 : Blo 2147435 20650625 := bstep (se 2 (by rfl) ⟨7743984, by rfl⟩ : syracuseStep 20650625 = 15487969) B15487969
theorem B13767083 : Blo 2147435 13767083 := bstep (se 1 (by rfl) ⟨10325312, by rfl⟩ : syracuseStep 13767083 = 20650625) B20650625
theorem B9178055 : Blo 2147435 9178055 := bstep (se 1 (by rfl) ⟨6883541, by rfl⟩ : syracuseStep 9178055 = 13767083) B13767083
theorem B6118703 : Blo 2147435 6118703 := bstep (se 1 (by rfl) ⟨4589027, by rfl⟩ : syracuseStep 6118703 = 9178055) B9178055
theorem B4079135 : Blo 2147435 4079135 := bstep (se 1 (by rfl) ⟨3059351, by rfl⟩ : syracuseStep 4079135 = 6118703) B6118703
theorem B2719423 : Blo 2147435 2719423 := bstep (se 1 (by rfl) ⟨2039567, by rfl⟩ : syracuseStep 2719423 = 4079135) B4079135
theorem B3625897 : Blo 2147435 3625897 := bstep (se 2 (by rfl) ⟨1359711, by rfl⟩ : syracuseStep 3625897 = 2719423) B2719423
theorem B4834529 : Blo 2147435 4834529 := bstep (se 2 (by rfl) ⟨1812948, by rfl⟩ : syracuseStep 4834529 = 3625897) B3625897
theorem B3223019 : Blo 2147435 3223019 := bstep (se 1 (by rfl) ⟨2417264, by rfl⟩ : syracuseStep 3223019 = 4834529) B4834529
theorem B2148679 : Blo 2147435 2148679 := bstep (se 1 (by rfl) ⟨1611509, by rfl⟩ : syracuseStep 2148679 = 3223019) B3223019
theorem B2417269 : Blo 2147435 2417269 := bbase (se 5 (by rfl) ⟨113309, by rfl⟩ : syracuseStep 2417269 = 226619) (by norm_num)
theorem B3223025 : Blo 2147435 3223025 := bstep (se 2 (by rfl) ⟨1208634, by rfl⟩ : syracuseStep 3223025 = 2417269) B2417269
theorem B2148683 : Blo 2147435 2148683 := bstep (se 1 (by rfl) ⟨1611512, by rfl⟩ : syracuseStep 2148683 = 3223025) B3223025
theorem B2719433 : Blo 2147435 2719433 := bbase (se 2 (by rfl) ⟨1019787, by rfl⟩ : syracuseStep 2719433 = 2039575) (by norm_num)
theorem B7251821 : Blo 2147435 7251821 := bstep (se 3 (by rfl) ⟨1359716, by rfl⟩ : syracuseStep 7251821 = 2719433) B2719433
theorem B4834547 : Blo 2147435 4834547 := bstep (se 1 (by rfl) ⟨3625910, by rfl⟩ : syracuseStep 4834547 = 7251821) B7251821
theorem B3223031 : Blo 2147435 3223031 := bstep (se 1 (by rfl) ⟨2417273, by rfl⟩ : syracuseStep 3223031 = 4834547) B4834547
theorem B2148687 : Blo 2147435 2148687 := bstep (se 1 (by rfl) ⟨1611515, by rfl⟩ : syracuseStep 2148687 = 3223031) B3223031
theorem B3223037 : Blo 2147435 3223037 := bbase (se 3 (by rfl) ⟨604319, by rfl⟩ : syracuseStep 3223037 = 1208639) (by norm_num)
theorem B2148691 : Blo 2147435 2148691 := bstep (se 1 (by rfl) ⟨1611518, by rfl⟩ : syracuseStep 2148691 = 3223037) B3223037
theorem B4834565 : Blo 2147435 4834565 := bbase (se 4 (by rfl) ⟨453240, by rfl⟩ : syracuseStep 4834565 = 906481) (by norm_num)
theorem B3223043 : Blo 2147435 3223043 := bstep (se 1 (by rfl) ⟨2417282, by rfl⟩ : syracuseStep 3223043 = 4834565) B4834565
theorem B2148695 : Blo 2147435 2148695 := bstep (se 1 (by rfl) ⟨1611521, by rfl⟩ : syracuseStep 2148695 = 3223043) B3223043
theorem B4079173 : Blo 2147435 4079173 := bbase (se 4 (by rfl) ⟨382422, by rfl⟩ : syracuseStep 4079173 = 764845) (by norm_num)
theorem B5438897 : Blo 2147435 5438897 := bstep (se 2 (by rfl) ⟨2039586, by rfl⟩ : syracuseStep 5438897 = 4079173) B4079173
theorem B3625931 : Blo 2147435 3625931 := bstep (se 1 (by rfl) ⟨2719448, by rfl⟩ : syracuseStep 3625931 = 5438897) B5438897
theorem B2417287 : Blo 2147435 2417287 := bstep (se 1 (by rfl) ⟨1812965, by rfl⟩ : syracuseStep 2417287 = 3625931) B3625931
theorem B3223049 : Blo 2147435 3223049 := bstep (se 2 (by rfl) ⟨1208643, by rfl⟩ : syracuseStep 3223049 = 2417287) B2417287
theorem B2148699 : Blo 2147435 2148699 := bstep (se 1 (by rfl) ⟨1611524, by rfl⟩ : syracuseStep 2148699 = 3223049) B3223049
theorem B10877813 : Blo 2147435 10877813 := bbase (se 5 (by rfl) ⟨509897, by rfl⟩ : syracuseStep 10877813 = 1019795) (by norm_num)
theorem B7251875 : Blo 2147435 7251875 := bstep (se 1 (by rfl) ⟨5438906, by rfl⟩ : syracuseStep 7251875 = 10877813) B10877813
theorem B4834583 : Blo 2147435 4834583 := bstep (se 1 (by rfl) ⟨3625937, by rfl⟩ : syracuseStep 4834583 = 7251875) B7251875
theorem B3223055 : Blo 2147435 3223055 := bstep (se 1 (by rfl) ⟨2417291, by rfl⟩ : syracuseStep 3223055 = 4834583) B4834583
theorem B2148703 : Blo 2147435 2148703 := bstep (se 1 (by rfl) ⟨1611527, by rfl⟩ : syracuseStep 2148703 = 3223055) B3223055
theorem B3223061 : Blo 2147435 3223061 := bbase (se 6 (by rfl) ⟨75540, by rfl⟩ : syracuseStep 3223061 = 151081) (by norm_num)
theorem B2148707 : Blo 2147435 2148707 := bstep (se 1 (by rfl) ⟨1611530, by rfl⟩ : syracuseStep 2148707 = 3223061) B3223061
theorem B11616149 : Blo 2147435 11616149 := bbase (se 6 (by rfl) ⟨272253, by rfl⟩ : syracuseStep 11616149 = 544507) (by norm_num)
theorem B7744099 : Blo 2147435 7744099 := bstep (se 1 (by rfl) ⟨5808074, by rfl⟩ : syracuseStep 7744099 = 11616149) B11616149
theorem B10325465 : Blo 2147435 10325465 := bstep (se 2 (by rfl) ⟨3872049, by rfl⟩ : syracuseStep 10325465 = 7744099) B7744099
theorem B6883643 : Blo 2147435 6883643 := bstep (se 1 (by rfl) ⟨5162732, by rfl⟩ : syracuseStep 6883643 = 10325465) B10325465
theorem B18356381 : Blo 2147435 18356381 := bstep (se 3 (by rfl) ⟨3441821, by rfl⟩ : syracuseStep 18356381 = 6883643) B6883643
theorem B12237587 : Blo 2147435 12237587 := bstep (se 1 (by rfl) ⟨9178190, by rfl⟩ : syracuseStep 12237587 = 18356381) B18356381
theorem B8158391 : Blo 2147435 8158391 := bstep (se 1 (by rfl) ⟨6118793, by rfl⟩ : syracuseStep 8158391 = 12237587) B12237587
theorem B5438927 : Blo 2147435 5438927 := bstep (se 1 (by rfl) ⟨4079195, by rfl⟩ : syracuseStep 5438927 = 8158391) B8158391
theorem B3625951 : Blo 2147435 3625951 := bstep (se 1 (by rfl) ⟨2719463, by rfl⟩ : syracuseStep 3625951 = 5438927) B5438927
theorem B4834601 : Blo 2147435 4834601 := bstep (se 2 (by rfl) ⟨1812975, by rfl⟩ : syracuseStep 4834601 = 3625951) B3625951
theorem B3223067 : Blo 2147435 3223067 := bstep (se 1 (by rfl) ⟨2417300, by rfl⟩ : syracuseStep 3223067 = 4834601) B4834601
theorem B2148711 : Blo 2147435 2148711 := bstep (se 1 (by rfl) ⟨1611533, by rfl⟩ : syracuseStep 2148711 = 3223067) B3223067
theorem B2417305 : Blo 2147435 2417305 := bbase (se 2 (by rfl) ⟨906489, by rfl⟩ : syracuseStep 2417305 = 1812979) (by norm_num)
theorem B3223073 : Blo 2147435 3223073 := bstep (se 2 (by rfl) ⟨1208652, by rfl⟩ : syracuseStep 3223073 = 2417305) B2417305
theorem B2148715 : Blo 2147435 2148715 := bstep (se 1 (by rfl) ⟨1611536, by rfl⟩ : syracuseStep 2148715 = 3223073) B3223073
theorem B8158421 : Blo 2147435 8158421 := bbase (se 7 (by rfl) ⟨95606, by rfl⟩ : syracuseStep 8158421 = 191213) (by norm_num)
theorem B5438947 : Blo 2147435 5438947 := bstep (se 1 (by rfl) ⟨4079210, by rfl⟩ : syracuseStep 5438947 = 8158421) B8158421
theorem B7251929 : Blo 2147435 7251929 := bstep (se 2 (by rfl) ⟨2719473, by rfl⟩ : syracuseStep 7251929 = 5438947) B5438947
theorem B4834619 : Blo 2147435 4834619 := bstep (se 1 (by rfl) ⟨3625964, by rfl⟩ : syracuseStep 4834619 = 7251929) B7251929
theorem B3223079 : Blo 2147435 3223079 := bstep (se 1 (by rfl) ⟨2417309, by rfl⟩ : syracuseStep 3223079 = 4834619) B4834619
theorem B2148719 : Blo 2147435 2148719 := bstep (se 1 (by rfl) ⟨1611539, by rfl⟩ : syracuseStep 2148719 = 3223079) B3223079
theorem B3223085 : Blo 2147435 3223085 := bbase (se 3 (by rfl) ⟨604328, by rfl⟩ : syracuseStep 3223085 = 1208657) (by norm_num)
theorem B2148723 : Blo 2147435 2148723 := bstep (se 1 (by rfl) ⟨1611542, by rfl⟩ : syracuseStep 2148723 = 3223085) B3223085
theorem B4834637 : Blo 2147435 4834637 := bbase (se 3 (by rfl) ⟨906494, by rfl⟩ : syracuseStep 4834637 = 1812989) (by norm_num)
theorem B3223091 : Blo 2147435 3223091 := bstep (se 1 (by rfl) ⟨2417318, by rfl⟩ : syracuseStep 3223091 = 4834637) B4834637
theorem B2148727 : Blo 2147435 2148727 := bstep (se 1 (by rfl) ⟨1611545, by rfl⟩ : syracuseStep 2148727 = 3223091) B3223091
theorem B2719489 : Blo 2147435 2719489 := bbase (se 2 (by rfl) ⟨1019808, by rfl⟩ : syracuseStep 2719489 = 2039617) (by norm_num)
theorem B3625985 : Blo 2147435 3625985 := bstep (se 2 (by rfl) ⟨1359744, by rfl⟩ : syracuseStep 3625985 = 2719489) B2719489
theorem B2417323 : Blo 2147435 2417323 := bstep (se 1 (by rfl) ⟨1812992, by rfl⟩ : syracuseStep 2417323 = 3625985) B3625985
theorem B3223097 : Blo 2147435 3223097 := bstep (se 2 (by rfl) ⟨1208661, by rfl⟩ : syracuseStep 3223097 = 2417323) B2417323
theorem B2148731 : Blo 2147435 2148731 := bstep (se 1 (by rfl) ⟨1611548, by rfl⟩ : syracuseStep 2148731 = 3223097) B3223097
theorem B2294573 : Blo 2147435 2294573 := bbase (se 3 (by rfl) ⟨430232, by rfl⟩ : syracuseStep 2294573 = 860465) (by norm_num)
theorem B24475445 : Blo 2147435 24475445 := bstep (se 5 (by rfl) ⟨1147286, by rfl⟩ : syracuseStep 24475445 = 2294573) B2294573
theorem B16316963 : Blo 2147435 16316963 := bstep (se 1 (by rfl) ⟨12237722, by rfl⟩ : syracuseStep 16316963 = 24475445) B24475445
theorem B10877975 : Blo 2147435 10877975 := bstep (se 1 (by rfl) ⟨8158481, by rfl⟩ : syracuseStep 10877975 = 16316963) B16316963
theorem B7251983 : Blo 2147435 7251983 := bstep (se 1 (by rfl) ⟨5438987, by rfl⟩ : syracuseStep 7251983 = 10877975) B10877975
theorem B4834655 : Blo 2147435 4834655 := bstep (se 1 (by rfl) ⟨3625991, by rfl⟩ : syracuseStep 4834655 = 7251983) B7251983
theorem B3223103 : Blo 2147435 3223103 := bstep (se 1 (by rfl) ⟨2417327, by rfl⟩ : syracuseStep 3223103 = 4834655) B4834655
theorem B2148735 : Blo 2147435 2148735 := bstep (se 1 (by rfl) ⟨1611551, by rfl⟩ : syracuseStep 2148735 = 3223103) B3223103
theorem B3223109 : Blo 2147435 3223109 := bbase (se 4 (by rfl) ⟨302166, by rfl⟩ : syracuseStep 3223109 = 604333) (by norm_num)
theorem B2148739 : Blo 2147435 2148739 := bstep (se 1 (by rfl) ⟨1611554, by rfl⟩ : syracuseStep 2148739 = 3223109) B3223109
theorem B3626005 : Blo 2147435 3626005 := bbase (se 6 (by rfl) ⟨84984, by rfl⟩ : syracuseStep 3626005 = 169969) (by norm_num)
theorem B4834673 : Blo 2147435 4834673 := bstep (se 2 (by rfl) ⟨1813002, by rfl⟩ : syracuseStep 4834673 = 3626005) B3626005
theorem B3223115 : Blo 2147435 3223115 := bstep (se 1 (by rfl) ⟨2417336, by rfl⟩ : syracuseStep 3223115 = 4834673) B4834673
theorem B2148743 : Blo 2147435 2148743 := bstep (se 1 (by rfl) ⟨1611557, by rfl⟩ : syracuseStep 2148743 = 3223115) B3223115
theorem B2417341 : Blo 2147435 2417341 := bbase (se 3 (by rfl) ⟨453251, by rfl⟩ : syracuseStep 2417341 = 906503) (by norm_num)
theorem B3223121 : Blo 2147435 3223121 := bstep (se 2 (by rfl) ⟨1208670, by rfl⟩ : syracuseStep 3223121 = 2417341) B2417341
theorem B2148747 : Blo 2147435 2148747 := bstep (se 1 (by rfl) ⟨1611560, by rfl⟩ : syracuseStep 2148747 = 3223121) B3223121
theorem B7252037 : Blo 2147435 7252037 := bbase (se 4 (by rfl) ⟨679878, by rfl⟩ : syracuseStep 7252037 = 1359757) (by norm_num)
theorem B4834691 : Blo 2147435 4834691 := bstep (se 1 (by rfl) ⟨3626018, by rfl⟩ : syracuseStep 4834691 = 7252037) B7252037
theorem B3223127 : Blo 2147435 3223127 := bstep (se 1 (by rfl) ⟨2417345, by rfl⟩ : syracuseStep 3223127 = 4834691) B4834691
theorem B2148751 : Blo 2147435 2148751 := bstep (se 1 (by rfl) ⟨1611563, by rfl⟩ : syracuseStep 2148751 = 3223127) B3223127
theorem B3223133 : Blo 2147435 3223133 := bbase (se 3 (by rfl) ⟨604337, by rfl⟩ : syracuseStep 3223133 = 1208675) (by norm_num)
theorem B2148755 : Blo 2147435 2148755 := bstep (se 1 (by rfl) ⟨1611566, by rfl⟩ : syracuseStep 2148755 = 3223133) B3223133
theorem B4834709 : Blo 2147435 4834709 := bbase (se 6 (by rfl) ⟨113313, by rfl⟩ : syracuseStep 4834709 = 226627) (by norm_num)
theorem B3223139 : Blo 2147435 3223139 := bstep (se 1 (by rfl) ⟨2417354, by rfl⟩ : syracuseStep 3223139 = 4834709) B4834709
theorem B2148759 : Blo 2147435 2148759 := bstep (se 1 (by rfl) ⟨1611569, by rfl⟩ : syracuseStep 2148759 = 3223139) B3223139
theorem B10325717 : Blo 2147435 10325717 := bbase (se 7 (by rfl) ⟨121004, by rfl⟩ : syracuseStep 10325717 = 242009) (by norm_num)
theorem B6883811 : Blo 2147435 6883811 := bstep (se 1 (by rfl) ⟨5162858, by rfl⟩ : syracuseStep 6883811 = 10325717) B10325717
theorem B4589207 : Blo 2147435 4589207 := bstep (se 1 (by rfl) ⟨3441905, by rfl⟩ : syracuseStep 4589207 = 6883811) B6883811
theorem B3059471 : Blo 2147435 3059471 := bstep (se 1 (by rfl) ⟨2294603, by rfl⟩ : syracuseStep 3059471 = 4589207) B4589207
theorem B8158589 : Blo 2147435 8158589 := bstep (se 3 (by rfl) ⟨1529735, by rfl⟩ : syracuseStep 8158589 = 3059471) B3059471
theorem B5439059 : Blo 2147435 5439059 := bstep (se 1 (by rfl) ⟨4079294, by rfl⟩ : syracuseStep 5439059 = 8158589) B8158589
theorem B3626039 : Blo 2147435 3626039 := bstep (se 1 (by rfl) ⟨2719529, by rfl⟩ : syracuseStep 3626039 = 5439059) B5439059
theorem B2417359 : Blo 2147435 2417359 := bstep (se 1 (by rfl) ⟨1813019, by rfl⟩ : syracuseStep 2417359 = 3626039) B3626039
theorem B3223145 : Blo 2147435 3223145 := bstep (se 2 (by rfl) ⟨1208679, by rfl⟩ : syracuseStep 3223145 = 2417359) B2417359
theorem B2148763 : Blo 2147435 2148763 := bstep (se 1 (by rfl) ⟨1611572, by rfl⟩ : syracuseStep 2148763 = 3223145) B3223145
theorem B2178085 : Blo 2147435 2178085 := bbase (se 4 (by rfl) ⟨204195, by rfl⟩ : syracuseStep 2178085 = 408391) (by norm_num)
theorem B2904113 : Blo 2147435 2904113 := bstep (se 2 (by rfl) ⟨1089042, by rfl⟩ : syracuseStep 2904113 = 2178085) B2178085
theorem B7744301 : Blo 2147435 7744301 := bstep (se 3 (by rfl) ⟨1452056, by rfl⟩ : syracuseStep 7744301 = 2904113) B2904113
theorem B5162867 : Blo 2147435 5162867 := bstep (se 1 (by rfl) ⟨3872150, by rfl⟩ : syracuseStep 5162867 = 7744301) B7744301
theorem B3441911 : Blo 2147435 3441911 := bstep (se 1 (by rfl) ⟨2581433, by rfl⟩ : syracuseStep 3441911 = 5162867) B5162867
theorem B9178429 : Blo 2147435 9178429 := bstep (se 3 (by rfl) ⟨1720955, by rfl⟩ : syracuseStep 9178429 = 3441911) B3441911
theorem B12237905 : Blo 2147435 12237905 := bstep (se 2 (by rfl) ⟨4589214, by rfl⟩ : syracuseStep 12237905 = 9178429) B9178429
theorem B8158603 : Blo 2147435 8158603 := bstep (se 1 (by rfl) ⟨6118952, by rfl⟩ : syracuseStep 8158603 = 12237905) B12237905
theorem B10878137 : Blo 2147435 10878137 := bstep (se 2 (by rfl) ⟨4079301, by rfl⟩ : syracuseStep 10878137 = 8158603) B8158603
theorem B7252091 : Blo 2147435 7252091 := bstep (se 1 (by rfl) ⟨5439068, by rfl⟩ : syracuseStep 7252091 = 10878137) B10878137
theorem B4834727 : Blo 2147435 4834727 := bstep (se 1 (by rfl) ⟨3626045, by rfl⟩ : syracuseStep 4834727 = 7252091) B7252091
theorem B3223151 : Blo 2147435 3223151 := bstep (se 1 (by rfl) ⟨2417363, by rfl⟩ : syracuseStep 3223151 = 4834727) B4834727
theorem B2148767 : Blo 2147435 2148767 := bstep (se 1 (by rfl) ⟨1611575, by rfl⟩ : syracuseStep 2148767 = 3223151) B3223151
theorem B3223157 : Blo 2147435 3223157 := bbase (se 5 (by rfl) ⟨151085, by rfl⟩ : syracuseStep 3223157 = 302171) (by norm_num)
theorem B2148771 : Blo 2147435 2148771 := bstep (se 1 (by rfl) ⟨1611578, by rfl⟩ : syracuseStep 2148771 = 3223157) B3223157
theorem B4079317 : Blo 2147435 4079317 := bbase (se 7 (by rfl) ⟨47804, by rfl⟩ : syracuseStep 4079317 = 95609) (by norm_num)
theorem B5439089 : Blo 2147435 5439089 := bstep (se 2 (by rfl) ⟨2039658, by rfl⟩ : syracuseStep 5439089 = 4079317) B4079317
theorem B3626059 : Blo 2147435 3626059 := bstep (se 1 (by rfl) ⟨2719544, by rfl⟩ : syracuseStep 3626059 = 5439089) B5439089
theorem B4834745 : Blo 2147435 4834745 := bstep (se 2 (by rfl) ⟨1813029, by rfl⟩ : syracuseStep 4834745 = 3626059) B3626059
theorem B3223163 : Blo 2147435 3223163 := bstep (se 1 (by rfl) ⟨2417372, by rfl⟩ : syracuseStep 3223163 = 4834745) B4834745
theorem B2148775 : Blo 2147435 2148775 := bstep (se 1 (by rfl) ⟨1611581, by rfl⟩ : syracuseStep 2148775 = 3223163) B3223163
theorem B2417377 : Blo 2147435 2417377 := bbase (se 2 (by rfl) ⟨906516, by rfl⟩ : syracuseStep 2417377 = 1813033) (by norm_num)
theorem B3223169 : Blo 2147435 3223169 := bstep (se 2 (by rfl) ⟨1208688, by rfl⟩ : syracuseStep 3223169 = 2417377) B2417377
theorem B2148779 : Blo 2147435 2148779 := bstep (se 1 (by rfl) ⟨1611584, by rfl⟩ : syracuseStep 2148779 = 3223169) B3223169
theorem B5439109 : Blo 2147435 5439109 := bbase (se 4 (by rfl) ⟨509916, by rfl⟩ : syracuseStep 5439109 = 1019833) (by norm_num)
theorem B7252145 : Blo 2147435 7252145 := bstep (se 2 (by rfl) ⟨2719554, by rfl⟩ : syracuseStep 7252145 = 5439109) B5439109
theorem B4834763 : Blo 2147435 4834763 := bstep (se 1 (by rfl) ⟨3626072, by rfl⟩ : syracuseStep 4834763 = 7252145) B7252145
theorem B3223175 : Blo 2147435 3223175 := bstep (se 1 (by rfl) ⟨2417381, by rfl⟩ : syracuseStep 3223175 = 4834763) B4834763
theorem B2148783 : Blo 2147435 2148783 := bstep (se 1 (by rfl) ⟨1611587, by rfl⟩ : syracuseStep 2148783 = 3223175) B3223175
theorem B3223181 : Blo 2147435 3223181 := bbase (se 3 (by rfl) ⟨604346, by rfl⟩ : syracuseStep 3223181 = 1208693) (by norm_num)
theorem B2148787 : Blo 2147435 2148787 := bstep (se 1 (by rfl) ⟨1611590, by rfl⟩ : syracuseStep 2148787 = 3223181) B3223181
theorem B4834781 : Blo 2147435 4834781 := bbase (se 3 (by rfl) ⟨906521, by rfl⟩ : syracuseStep 4834781 = 1813043) (by norm_num)
theorem B3223187 : Blo 2147435 3223187 := bstep (se 1 (by rfl) ⟨2417390, by rfl⟩ : syracuseStep 3223187 = 4834781) B4834781
theorem B2148791 : Blo 2147435 2148791 := bstep (se 1 (by rfl) ⟨1611593, by rfl⟩ : syracuseStep 2148791 = 3223187) B3223187
theorem B3626093 : Blo 2147435 3626093 := bbase (se 3 (by rfl) ⟨679892, by rfl⟩ : syracuseStep 3626093 = 1359785) (by norm_num)
theorem B2417395 : Blo 2147435 2417395 := bstep (se 1 (by rfl) ⟨1813046, by rfl⟩ : syracuseStep 2417395 = 3626093) B3626093
theorem B3223193 : Blo 2147435 3223193 := bstep (se 2 (by rfl) ⟨1208697, by rfl⟩ : syracuseStep 3223193 = 2417395) B2417395
theorem B2148795 : Blo 2147435 2148795 := bstep (se 1 (by rfl) ⟨1611596, by rfl⟩ : syracuseStep 2148795 = 3223193) B3223193
theorem B4191437 : Blo 2147435 4191437 := bbase (se 3 (by rfl) ⟨785894, by rfl⟩ : syracuseStep 4191437 = 1571789) (by norm_num)
theorem B11177165 : Blo 2147435 11177165 := bstep (se 3 (by rfl) ⟨2095718, by rfl⟩ : syracuseStep 11177165 = 4191437) B4191437
theorem B7451443 : Blo 2147435 7451443 := bstep (se 1 (by rfl) ⟨5588582, by rfl⟩ : syracuseStep 7451443 = 11177165) B11177165
theorem B9935257 : Blo 2147435 9935257 := bstep (se 2 (by rfl) ⟨3725721, by rfl⟩ : syracuseStep 9935257 = 7451443) B7451443
theorem B13247009 : Blo 2147435 13247009 := bstep (se 2 (by rfl) ⟨4967628, by rfl⟩ : syracuseStep 13247009 = 9935257) B9935257
theorem B8831339 : Blo 2147435 8831339 := bstep (se 1 (by rfl) ⟨6623504, by rfl⟩ : syracuseStep 8831339 = 13247009) B13247009
theorem B5887559 : Blo 2147435 5887559 := bstep (se 1 (by rfl) ⟨4415669, by rfl⟩ : syracuseStep 5887559 = 8831339) B8831339
theorem B3925039 : Blo 2147435 3925039 := bstep (se 1 (by rfl) ⟨2943779, by rfl⟩ : syracuseStep 3925039 = 5887559) B5887559
theorem B5233385 : Blo 2147435 5233385 := bstep (se 2 (by rfl) ⟨1962519, by rfl⟩ : syracuseStep 5233385 = 3925039) B3925039
theorem B3488923 : Blo 2147435 3488923 := bstep (se 1 (by rfl) ⟨2616692, by rfl⟩ : syracuseStep 3488923 = 5233385) B5233385
theorem B4651897 : Blo 2147435 4651897 := bstep (se 2 (by rfl) ⟨1744461, by rfl⟩ : syracuseStep 4651897 = 3488923) B3488923
theorem B6202529 : Blo 2147435 6202529 := bstep (se 2 (by rfl) ⟨2325948, by rfl⟩ : syracuseStep 6202529 = 4651897) B4651897
theorem B4135019 : Blo 2147435 4135019 := bstep (se 1 (by rfl) ⟨3101264, by rfl⟩ : syracuseStep 4135019 = 6202529) B6202529
theorem B44106869 : Blo 2147435 44106869 := bstep (se 5 (by rfl) ⟨2067509, by rfl⟩ : syracuseStep 44106869 = 4135019) B4135019
theorem B29404579 : Blo 2147435 29404579 := bstep (se 1 (by rfl) ⟨22053434, by rfl⟩ : syracuseStep 29404579 = 44106869) B44106869
theorem B39206105 : Blo 2147435 39206105 := bstep (se 2 (by rfl) ⟨14702289, by rfl⟩ : syracuseStep 39206105 = 29404579) B29404579
theorem B26137403 : Blo 2147435 26137403 := bstep (se 1 (by rfl) ⟨19603052, by rfl⟩ : syracuseStep 26137403 = 39206105) B39206105
theorem B17424935 : Blo 2147435 17424935 := bstep (se 1 (by rfl) ⟨13068701, by rfl⟩ : syracuseStep 17424935 = 26137403) B26137403
theorem B11616623 : Blo 2147435 11616623 := bstep (se 1 (by rfl) ⟨8712467, by rfl⟩ : syracuseStep 11616623 = 17424935) B17424935
theorem B7744415 : Blo 2147435 7744415 := bstep (se 1 (by rfl) ⟨5808311, by rfl⟩ : syracuseStep 7744415 = 11616623) B11616623
theorem B20651773 : Blo 2147435 20651773 := bstep (se 3 (by rfl) ⟨3872207, by rfl⟩ : syracuseStep 20651773 = 7744415) B7744415
theorem B27535697 : Blo 2147435 27535697 := bstep (se 2 (by rfl) ⟨10325886, by rfl⟩ : syracuseStep 27535697 = 20651773) B20651773
theorem B18357131 : Blo 2147435 18357131 := bstep (se 1 (by rfl) ⟨13767848, by rfl⟩ : syracuseStep 18357131 = 27535697) B27535697
theorem B12238087 : Blo 2147435 12238087 := bstep (se 1 (by rfl) ⟨9178565, by rfl⟩ : syracuseStep 12238087 = 18357131) B18357131
theorem B16317449 : Blo 2147435 16317449 := bstep (se 2 (by rfl) ⟨6119043, by rfl⟩ : syracuseStep 16317449 = 12238087) B12238087
theorem B10878299 : Blo 2147435 10878299 := bstep (se 1 (by rfl) ⟨8158724, by rfl⟩ : syracuseStep 10878299 = 16317449) B16317449
theorem B7252199 : Blo 2147435 7252199 := bstep (se 1 (by rfl) ⟨5439149, by rfl⟩ : syracuseStep 7252199 = 10878299) B10878299
theorem B4834799 : Blo 2147435 4834799 := bstep (se 1 (by rfl) ⟨3626099, by rfl⟩ : syracuseStep 4834799 = 7252199) B7252199
theorem B3223199 : Blo 2147435 3223199 := bstep (se 1 (by rfl) ⟨2417399, by rfl⟩ : syracuseStep 3223199 = 4834799) B4834799
theorem B2148799 : Blo 2147435 2148799 := bstep (se 1 (by rfl) ⟨1611599, by rfl⟩ : syracuseStep 2148799 = 3223199) B3223199
theorem B3223205 : Blo 2147435 3223205 := bbase (se 4 (by rfl) ⟨302175, by rfl⟩ : syracuseStep 3223205 = 604351) (by norm_num)
theorem B2148803 : Blo 2147435 2148803 := bstep (se 1 (by rfl) ⟨1611602, by rfl⟩ : syracuseStep 2148803 = 3223205) B3223205
theorem B2719585 : Blo 2147435 2719585 := bbase (se 2 (by rfl) ⟨1019844, by rfl⟩ : syracuseStep 2719585 = 2039689) (by norm_num)
theorem B3626113 : Blo 2147435 3626113 := bstep (se 2 (by rfl) ⟨1359792, by rfl⟩ : syracuseStep 3626113 = 2719585) B2719585
theorem B4834817 : Blo 2147435 4834817 := bstep (se 2 (by rfl) ⟨1813056, by rfl⟩ : syracuseStep 4834817 = 3626113) B3626113
theorem B3223211 : Blo 2147435 3223211 := bstep (se 1 (by rfl) ⟨2417408, by rfl⟩ : syracuseStep 3223211 = 4834817) B4834817
theorem B2148807 : Blo 2147435 2148807 := bstep (se 1 (by rfl) ⟨1611605, by rfl⟩ : syracuseStep 2148807 = 3223211) B3223211
theorem B2417413 : Blo 2147435 2417413 := bbase (se 4 (by rfl) ⟨226632, by rfl⟩ : syracuseStep 2417413 = 453265) (by norm_num)
theorem B3223217 : Blo 2147435 3223217 := bstep (se 2 (by rfl) ⟨1208706, by rfl⟩ : syracuseStep 3223217 = 2417413) B2417413
theorem B2148811 : Blo 2147435 2148811 := bstep (se 1 (by rfl) ⟨1611608, by rfl⟩ : syracuseStep 2148811 = 3223217) B3223217
theorem B3441989 : Blo 2147435 3441989 := bbase (se 4 (by rfl) ⟨322686, by rfl⟩ : syracuseStep 3441989 = 645373) (by norm_num)
theorem B2294659 : Blo 2147435 2294659 := bstep (se 1 (by rfl) ⟨1720994, by rfl⟩ : syracuseStep 2294659 = 3441989) B3441989
theorem B3059545 : Blo 2147435 3059545 := bstep (se 2 (by rfl) ⟨1147329, by rfl⟩ : syracuseStep 3059545 = 2294659) B2294659
theorem B4079393 : Blo 2147435 4079393 := bstep (se 2 (by rfl) ⟨1529772, by rfl⟩ : syracuseStep 4079393 = 3059545) B3059545
theorem B2719595 : Blo 2147435 2719595 := bstep (se 1 (by rfl) ⟨2039696, by rfl⟩ : syracuseStep 2719595 = 4079393) B4079393
theorem B7252253 : Blo 2147435 7252253 := bstep (se 3 (by rfl) ⟨1359797, by rfl⟩ : syracuseStep 7252253 = 2719595) B2719595
theorem B4834835 : Blo 2147435 4834835 := bstep (se 1 (by rfl) ⟨3626126, by rfl⟩ : syracuseStep 4834835 = 7252253) B7252253
theorem B3223223 : Blo 2147435 3223223 := bstep (se 1 (by rfl) ⟨2417417, by rfl⟩ : syracuseStep 3223223 = 4834835) B4834835
theorem B2148815 : Blo 2147435 2148815 := bstep (se 1 (by rfl) ⟨1611611, by rfl⟩ : syracuseStep 2148815 = 3223223) B3223223
theorem B3223229 : Blo 2147435 3223229 := bbase (se 3 (by rfl) ⟨604355, by rfl⟩ : syracuseStep 3223229 = 1208711) (by norm_num)
theorem B2148819 : Blo 2147435 2148819 := bstep (se 1 (by rfl) ⟨1611614, by rfl⟩ : syracuseStep 2148819 = 3223229) B3223229
theorem B4834853 : Blo 2147435 4834853 := bbase (se 4 (by rfl) ⟨453267, by rfl⟩ : syracuseStep 4834853 = 906535) (by norm_num)
theorem B3223235 : Blo 2147435 3223235 := bstep (se 1 (by rfl) ⟨2417426, by rfl⟩ : syracuseStep 3223235 = 4834853) B4834853
theorem B2148823 : Blo 2147435 2148823 := bstep (se 1 (by rfl) ⟨1611617, by rfl⟩ : syracuseStep 2148823 = 3223235) B3223235
theorem B5439221 : Blo 2147435 5439221 := bbase (se 5 (by rfl) ⟨254963, by rfl⟩ : syracuseStep 5439221 = 509927) (by norm_num)
theorem B3626147 : Blo 2147435 3626147 := bstep (se 1 (by rfl) ⟨2719610, by rfl⟩ : syracuseStep 3626147 = 5439221) B5439221
theorem B2417431 : Blo 2147435 2417431 := bstep (se 1 (by rfl) ⟨1813073, by rfl⟩ : syracuseStep 2417431 = 3626147) B3626147
theorem B3223241 : Blo 2147435 3223241 := bstep (se 2 (by rfl) ⟨1208715, by rfl⟩ : syracuseStep 3223241 = 2417431) B2417431
theorem B2148827 : Blo 2147435 2148827 := bstep (se 1 (by rfl) ⟨1611620, by rfl⟩ : syracuseStep 2148827 = 3223241) B3223241
theorem B4900837 : Blo 2147435 4900837 := bbase (se 4 (by rfl) ⟨459453, by rfl⟩ : syracuseStep 4900837 = 918907) (by norm_num)
theorem B6534449 : Blo 2147435 6534449 := bstep (se 2 (by rfl) ⟨2450418, by rfl⟩ : syracuseStep 6534449 = 4900837) B4900837
theorem B4356299 : Blo 2147435 4356299 := bstep (se 1 (by rfl) ⟨3267224, by rfl⟩ : syracuseStep 4356299 = 6534449) B6534449
theorem B11616797 : Blo 2147435 11616797 := bstep (se 3 (by rfl) ⟨2178149, by rfl⟩ : syracuseStep 11616797 = 4356299) B4356299
theorem B30978125 : Blo 2147435 30978125 := bstep (se 3 (by rfl) ⟨5808398, by rfl⟩ : syracuseStep 30978125 = 11616797) B11616797
theorem B20652083 : Blo 2147435 20652083 := bstep (se 1 (by rfl) ⟨15489062, by rfl⟩ : syracuseStep 20652083 = 30978125) B30978125
theorem B13768055 : Blo 2147435 13768055 := bstep (se 1 (by rfl) ⟨10326041, by rfl⟩ : syracuseStep 13768055 = 20652083) B20652083
theorem B9178703 : Blo 2147435 9178703 := bstep (se 1 (by rfl) ⟨6884027, by rfl⟩ : syracuseStep 9178703 = 13768055) B13768055
theorem B6119135 : Blo 2147435 6119135 := bstep (se 1 (by rfl) ⟨4589351, by rfl⟩ : syracuseStep 6119135 = 9178703) B9178703
theorem B4079423 : Blo 2147435 4079423 := bstep (se 1 (by rfl) ⟨3059567, by rfl⟩ : syracuseStep 4079423 = 6119135) B6119135
theorem B10878461 : Blo 2147435 10878461 := bstep (se 3 (by rfl) ⟨2039711, by rfl⟩ : syracuseStep 10878461 = 4079423) B4079423
theorem B7252307 : Blo 2147435 7252307 := bstep (se 1 (by rfl) ⟨5439230, by rfl⟩ : syracuseStep 7252307 = 10878461) B10878461
theorem B4834871 : Blo 2147435 4834871 := bstep (se 1 (by rfl) ⟨3626153, by rfl⟩ : syracuseStep 4834871 = 7252307) B7252307
theorem B3223247 : Blo 2147435 3223247 := bstep (se 1 (by rfl) ⟨2417435, by rfl⟩ : syracuseStep 3223247 = 4834871) B4834871
theorem B2148831 : Blo 2147435 2148831 := bstep (se 1 (by rfl) ⟨1611623, by rfl⟩ : syracuseStep 2148831 = 3223247) B3223247
theorem B3223253 : Blo 2147435 3223253 := bbase (se 7 (by rfl) ⟨37772, by rfl⟩ : syracuseStep 3223253 = 75545) (by norm_num)
theorem B2148835 : Blo 2147435 2148835 := bstep (se 1 (by rfl) ⟨1611626, by rfl⟩ : syracuseStep 2148835 = 3223253) B3223253
theorem B4356317 : Blo 2147435 4356317 := bbase (se 3 (by rfl) ⟨816809, by rfl⟩ : syracuseStep 4356317 = 1633619) (by norm_num)
theorem B2904211 : Blo 2147435 2904211 := bstep (se 1 (by rfl) ⟨2178158, by rfl⟩ : syracuseStep 2904211 = 4356317) B4356317
theorem B3872281 : Blo 2147435 3872281 := bstep (se 2 (by rfl) ⟨1452105, by rfl⟩ : syracuseStep 3872281 = 2904211) B2904211
theorem B5163041 : Blo 2147435 5163041 := bstep (se 2 (by rfl) ⟨1936140, by rfl⟩ : syracuseStep 5163041 = 3872281) B3872281
theorem B3442027 : Blo 2147435 3442027 := bstep (se 1 (by rfl) ⟨2581520, by rfl⟩ : syracuseStep 3442027 = 5163041) B5163041
theorem B4589369 : Blo 2147435 4589369 := bstep (se 2 (by rfl) ⟨1721013, by rfl⟩ : syracuseStep 4589369 = 3442027) B3442027
theorem B3059579 : Blo 2147435 3059579 := bstep (se 1 (by rfl) ⟨2294684, by rfl⟩ : syracuseStep 3059579 = 4589369) B4589369
theorem B8158877 : Blo 2147435 8158877 := bstep (se 3 (by rfl) ⟨1529789, by rfl⟩ : syracuseStep 8158877 = 3059579) B3059579
theorem B5439251 : Blo 2147435 5439251 := bstep (se 1 (by rfl) ⟨4079438, by rfl⟩ : syracuseStep 5439251 = 8158877) B8158877
theorem B3626167 : Blo 2147435 3626167 := bstep (se 1 (by rfl) ⟨2719625, by rfl⟩ : syracuseStep 3626167 = 5439251) B5439251
theorem B4834889 : Blo 2147435 4834889 := bstep (se 2 (by rfl) ⟨1813083, by rfl⟩ : syracuseStep 4834889 = 3626167) B3626167
theorem B3223259 : Blo 2147435 3223259 := bstep (se 1 (by rfl) ⟨2417444, by rfl⟩ : syracuseStep 3223259 = 4834889) B4834889
theorem B2148839 : Blo 2147435 2148839 := bstep (se 1 (by rfl) ⟨1611629, by rfl⟩ : syracuseStep 2148839 = 3223259) B3223259
theorem B2417449 : Blo 2147435 2417449 := bbase (se 2 (by rfl) ⟨906543, by rfl⟩ : syracuseStep 2417449 = 1813087) (by norm_num)
theorem B3223265 : Blo 2147435 3223265 := bstep (se 2 (by rfl) ⟨1208724, by rfl⟩ : syracuseStep 3223265 = 2417449) B2417449
theorem B2148843 : Blo 2147435 2148843 := bstep (se 1 (by rfl) ⟨1611632, by rfl⟩ : syracuseStep 2148843 = 3223265) B3223265
theorem B2904221 : Blo 2147435 2904221 := bbase (se 3 (by rfl) ⟨544541, by rfl⟩ : syracuseStep 2904221 = 1089083) (by norm_num)
theorem B7744589 : Blo 2147435 7744589 := bstep (se 3 (by rfl) ⟨1452110, by rfl⟩ : syracuseStep 7744589 = 2904221) B2904221
theorem B5163059 : Blo 2147435 5163059 := bstep (se 1 (by rfl) ⟨3872294, by rfl⟩ : syracuseStep 5163059 = 7744589) B7744589
theorem B13768157 : Blo 2147435 13768157 := bstep (se 3 (by rfl) ⟨2581529, by rfl⟩ : syracuseStep 13768157 = 5163059) B5163059
theorem B9178771 : Blo 2147435 9178771 := bstep (se 1 (by rfl) ⟨6884078, by rfl⟩ : syracuseStep 9178771 = 13768157) B13768157
theorem B12238361 : Blo 2147435 12238361 := bstep (se 2 (by rfl) ⟨4589385, by rfl⟩ : syracuseStep 12238361 = 9178771) B9178771
theorem B8158907 : Blo 2147435 8158907 := bstep (se 1 (by rfl) ⟨6119180, by rfl⟩ : syracuseStep 8158907 = 12238361) B12238361
theorem B5439271 : Blo 2147435 5439271 := bstep (se 1 (by rfl) ⟨4079453, by rfl⟩ : syracuseStep 5439271 = 8158907) B8158907
theorem B7252361 : Blo 2147435 7252361 := bstep (se 2 (by rfl) ⟨2719635, by rfl⟩ : syracuseStep 7252361 = 5439271) B5439271
theorem B4834907 : Blo 2147435 4834907 := bstep (se 1 (by rfl) ⟨3626180, by rfl⟩ : syracuseStep 4834907 = 7252361) B7252361
theorem B3223271 : Blo 2147435 3223271 := bstep (se 1 (by rfl) ⟨2417453, by rfl⟩ : syracuseStep 3223271 = 4834907) B4834907
theorem B2148847 : Blo 2147435 2148847 := bstep (se 1 (by rfl) ⟨1611635, by rfl⟩ : syracuseStep 2148847 = 3223271) B3223271
theorem B3223277 : Blo 2147435 3223277 := bbase (se 3 (by rfl) ⟨604364, by rfl⟩ : syracuseStep 3223277 = 1208729) (by norm_num)
theorem B2148851 : Blo 2147435 2148851 := bstep (se 1 (by rfl) ⟨1611638, by rfl⟩ : syracuseStep 2148851 = 3223277) B3223277
theorem B4834925 : Blo 2147435 4834925 := bbase (se 3 (by rfl) ⟨906548, by rfl⟩ : syracuseStep 4834925 = 1813097) (by norm_num)
theorem B3223283 : Blo 2147435 3223283 := bstep (se 1 (by rfl) ⟨2417462, by rfl⟩ : syracuseStep 3223283 = 4834925) B4834925
theorem B2148855 : Blo 2147435 2148855 := bstep (se 1 (by rfl) ⟨1611641, by rfl⟩ : syracuseStep 2148855 = 3223283) B3223283
theorem B4079477 : Blo 2147435 4079477 := bbase (se 5 (by rfl) ⟨191225, by rfl⟩ : syracuseStep 4079477 = 382451) (by norm_num)
theorem B2719651 : Blo 2147435 2719651 := bstep (se 1 (by rfl) ⟨2039738, by rfl⟩ : syracuseStep 2719651 = 4079477) B4079477
theorem B3626201 : Blo 2147435 3626201 := bstep (se 2 (by rfl) ⟨1359825, by rfl⟩ : syracuseStep 3626201 = 2719651) B2719651
theorem B2417467 : Blo 2147435 2417467 := bstep (se 1 (by rfl) ⟨1813100, by rfl⟩ : syracuseStep 2417467 = 3626201) B3626201
theorem B3223289 : Blo 2147435 3223289 := bstep (se 2 (by rfl) ⟨1208733, by rfl⟩ : syracuseStep 3223289 = 2417467) B2417467
theorem B2148859 : Blo 2147435 2148859 := bstep (se 1 (by rfl) ⟨1611644, by rfl⟩ : syracuseStep 2148859 = 3223289) B3223289
theorem B11027045 : Blo 2147435 11027045 := bbase (se 4 (by rfl) ⟨1033785, by rfl⟩ : syracuseStep 11027045 = 2067571) (by norm_num)
theorem B7351363 : Blo 2147435 7351363 := bstep (se 1 (by rfl) ⟨5513522, by rfl⟩ : syracuseStep 7351363 = 11027045) B11027045
theorem B9801817 : Blo 2147435 9801817 := bstep (se 2 (by rfl) ⟨3675681, by rfl⟩ : syracuseStep 9801817 = 7351363) B7351363
theorem B52276357 : Blo 2147435 52276357 := bstep (se 4 (by rfl) ⟨4900908, by rfl⟩ : syracuseStep 52276357 = 9801817) B9801817
theorem B69701809 : Blo 2147435 69701809 := bstep (se 2 (by rfl) ⟨26138178, by rfl⟩ : syracuseStep 69701809 = 52276357) B52276357
theorem B92935745 : Blo 2147435 92935745 := bstep (se 2 (by rfl) ⟨34850904, by rfl⟩ : syracuseStep 92935745 = 69701809) B69701809
theorem B61957163 : Blo 2147435 61957163 := bstep (se 1 (by rfl) ⟨46467872, by rfl⟩ : syracuseStep 61957163 = 92935745) B92935745
theorem B41304775 : Blo 2147435 41304775 := bstep (se 1 (by rfl) ⟨30978581, by rfl⟩ : syracuseStep 41304775 = 61957163) B61957163
theorem B55073033 : Blo 2147435 55073033 := bstep (se 2 (by rfl) ⟨20652387, by rfl⟩ : syracuseStep 55073033 = 41304775) B41304775
theorem B36715355 : Blo 2147435 36715355 := bstep (se 1 (by rfl) ⟨27536516, by rfl⟩ : syracuseStep 36715355 = 55073033) B55073033
theorem B24476903 : Blo 2147435 24476903 := bstep (se 1 (by rfl) ⟨18357677, by rfl⟩ : syracuseStep 24476903 = 36715355) B36715355
theorem B16317935 : Blo 2147435 16317935 := bstep (se 1 (by rfl) ⟨12238451, by rfl⟩ : syracuseStep 16317935 = 24476903) B24476903
theorem B10878623 : Blo 2147435 10878623 := bstep (se 1 (by rfl) ⟨8158967, by rfl⟩ : syracuseStep 10878623 = 16317935) B16317935
theorem B7252415 : Blo 2147435 7252415 := bstep (se 1 (by rfl) ⟨5439311, by rfl⟩ : syracuseStep 7252415 = 10878623) B10878623
theorem B4834943 : Blo 2147435 4834943 := bstep (se 1 (by rfl) ⟨3626207, by rfl⟩ : syracuseStep 4834943 = 7252415) B7252415
theorem B3223295 : Blo 2147435 3223295 := bstep (se 1 (by rfl) ⟨2417471, by rfl⟩ : syracuseStep 3223295 = 4834943) B4834943
theorem B2148863 : Blo 2147435 2148863 := bstep (se 1 (by rfl) ⟨1611647, by rfl⟩ : syracuseStep 2148863 = 3223295) B3223295
theorem B3223301 : Blo 2147435 3223301 := bbase (se 4 (by rfl) ⟨302184, by rfl⟩ : syracuseStep 3223301 = 604369) (by norm_num)
theorem B2148867 : Blo 2147435 2148867 := bstep (se 1 (by rfl) ⟨1611650, by rfl⟩ : syracuseStep 2148867 = 3223301) B3223301
theorem B3626221 : Blo 2147435 3626221 := bbase (se 3 (by rfl) ⟨679916, by rfl⟩ : syracuseStep 3626221 = 1359833) (by norm_num)
theorem B4834961 : Blo 2147435 4834961 := bstep (se 2 (by rfl) ⟨1813110, by rfl⟩ : syracuseStep 4834961 = 3626221) B3626221
theorem B3223307 : Blo 2147435 3223307 := bstep (se 1 (by rfl) ⟨2417480, by rfl⟩ : syracuseStep 3223307 = 4834961) B4834961
theorem B2148871 : Blo 2147435 2148871 := bstep (se 1 (by rfl) ⟨1611653, by rfl⟩ : syracuseStep 2148871 = 3223307) B3223307
theorem B2417485 : Blo 2147435 2417485 := bbase (se 3 (by rfl) ⟨453278, by rfl⟩ : syracuseStep 2417485 = 906557) (by norm_num)
theorem B3223313 : Blo 2147435 3223313 := bstep (se 2 (by rfl) ⟨1208742, by rfl⟩ : syracuseStep 3223313 = 2417485) B2417485
theorem B2148875 : Blo 2147435 2148875 := bstep (se 1 (by rfl) ⟨1611656, by rfl⟩ : syracuseStep 2148875 = 3223313) B3223313
theorem B7252469 : Blo 2147435 7252469 := bbase (se 5 (by rfl) ⟨339959, by rfl⟩ : syracuseStep 7252469 = 679919) (by norm_num)
theorem B4834979 : Blo 2147435 4834979 := bstep (se 1 (by rfl) ⟨3626234, by rfl⟩ : syracuseStep 4834979 = 7252469) B7252469
theorem B3223319 : Blo 2147435 3223319 := bstep (se 1 (by rfl) ⟨2417489, by rfl⟩ : syracuseStep 3223319 = 4834979) B4834979
theorem B2148879 : Blo 2147435 2148879 := bstep (se 1 (by rfl) ⟨1611659, by rfl⟩ : syracuseStep 2148879 = 3223319) B3223319
theorem B3223325 : Blo 2147435 3223325 := bbase (se 3 (by rfl) ⟨604373, by rfl⟩ : syracuseStep 3223325 = 1208747) (by norm_num)
theorem B2148883 : Blo 2147435 2148883 := bstep (se 1 (by rfl) ⟨1611662, by rfl⟩ : syracuseStep 2148883 = 3223325) B3223325
theorem B4834997 : Blo 2147435 4834997 := bbase (se 5 (by rfl) ⟨226640, by rfl⟩ : syracuseStep 4834997 = 453281) (by norm_num)
theorem B3223331 : Blo 2147435 3223331 := bstep (se 1 (by rfl) ⟨2417498, by rfl⟩ : syracuseStep 3223331 = 4834997) B4834997
theorem B2148887 : Blo 2147435 2148887 := bstep (se 1 (by rfl) ⟨1611665, by rfl⟩ : syracuseStep 2148887 = 3223331) B3223331
theorem B12238613 : Blo 2147435 12238613 := bbase (se 6 (by rfl) ⟨286842, by rfl⟩ : syracuseStep 12238613 = 573685) (by norm_num)
theorem B8159075 : Blo 2147435 8159075 := bstep (se 1 (by rfl) ⟨6119306, by rfl⟩ : syracuseStep 8159075 = 12238613) B12238613
theorem B5439383 : Blo 2147435 5439383 := bstep (se 1 (by rfl) ⟨4079537, by rfl⟩ : syracuseStep 5439383 = 8159075) B8159075
theorem B3626255 : Blo 2147435 3626255 := bstep (se 1 (by rfl) ⟨2719691, by rfl⟩ : syracuseStep 3626255 = 5439383) B5439383
theorem B2417503 : Blo 2147435 2417503 := bstep (se 1 (by rfl) ⟨1813127, by rfl⟩ : syracuseStep 2417503 = 3626255) B3626255
theorem B3223337 : Blo 2147435 3223337 := bstep (se 2 (by rfl) ⟨1208751, by rfl⟩ : syracuseStep 3223337 = 2417503) B2417503
theorem B2148891 : Blo 2147435 2148891 := bstep (se 1 (by rfl) ⟨1611668, by rfl⟩ : syracuseStep 2148891 = 3223337) B3223337
theorem B6119317 : Blo 2147435 6119317 := bbase (se 6 (by rfl) ⟨143421, by rfl⟩ : syracuseStep 6119317 = 286843) (by norm_num)
theorem B8159089 : Blo 2147435 8159089 := bstep (se 2 (by rfl) ⟨3059658, by rfl⟩ : syracuseStep 8159089 = 6119317) B6119317
theorem B10878785 : Blo 2147435 10878785 := bstep (se 2 (by rfl) ⟨4079544, by rfl⟩ : syracuseStep 10878785 = 8159089) B8159089
theorem B7252523 : Blo 2147435 7252523 := bstep (se 1 (by rfl) ⟨5439392, by rfl⟩ : syracuseStep 7252523 = 10878785) B10878785
theorem B4835015 : Blo 2147435 4835015 := bstep (se 1 (by rfl) ⟨3626261, by rfl⟩ : syracuseStep 4835015 = 7252523) B7252523
theorem B3223343 : Blo 2147435 3223343 := bstep (se 1 (by rfl) ⟨2417507, by rfl⟩ : syracuseStep 3223343 = 4835015) B4835015
theorem B2148895 : Blo 2147435 2148895 := bstep (se 1 (by rfl) ⟨1611671, by rfl⟩ : syracuseStep 2148895 = 3223343) B3223343
theorem B3223349 : Blo 2147435 3223349 := bbase (se 5 (by rfl) ⟨151094, by rfl⟩ : syracuseStep 3223349 = 302189) (by norm_num)
theorem B2148899 : Blo 2147435 2148899 := bstep (se 1 (by rfl) ⟨1611674, by rfl⟩ : syracuseStep 2148899 = 3223349) B3223349
theorem B5439413 : Blo 2147435 5439413 := bbase (se 5 (by rfl) ⟨254972, by rfl⟩ : syracuseStep 5439413 = 509945) (by norm_num)
theorem B3626275 : Blo 2147435 3626275 := bstep (se 1 (by rfl) ⟨2719706, by rfl⟩ : syracuseStep 3626275 = 5439413) B5439413
theorem B4835033 : Blo 2147435 4835033 := bstep (se 2 (by rfl) ⟨1813137, by rfl⟩ : syracuseStep 4835033 = 3626275) B3626275
theorem B3223355 : Blo 2147435 3223355 := bstep (se 1 (by rfl) ⟨2417516, by rfl⟩ : syracuseStep 3223355 = 4835033) B4835033
theorem B2148903 : Blo 2147435 2148903 := bstep (se 1 (by rfl) ⟨1611677, by rfl⟩ : syracuseStep 2148903 = 3223355) B3223355
theorem B2417521 : Blo 2147435 2417521 := bbase (se 2 (by rfl) ⟨906570, by rfl⟩ : syracuseStep 2417521 = 1813141) (by norm_num)
theorem B3223361 : Blo 2147435 3223361 := bstep (se 2 (by rfl) ⟨1208760, by rfl⟩ : syracuseStep 3223361 = 2417521) B2417521
theorem B2148907 : Blo 2147435 2148907 := bstep (se 1 (by rfl) ⟨1611680, by rfl⟩ : syracuseStep 2148907 = 3223361) B3223361
theorem B9179045 : Blo 2147435 9179045 := bbase (se 4 (by rfl) ⟨860535, by rfl⟩ : syracuseStep 9179045 = 1721071) (by norm_num)
theorem B6119363 : Blo 2147435 6119363 := bstep (se 1 (by rfl) ⟨4589522, by rfl⟩ : syracuseStep 6119363 = 9179045) B9179045
theorem B4079575 : Blo 2147435 4079575 := bstep (se 1 (by rfl) ⟨3059681, by rfl⟩ : syracuseStep 4079575 = 6119363) B6119363
theorem B5439433 : Blo 2147435 5439433 := bstep (se 2 (by rfl) ⟨2039787, by rfl⟩ : syracuseStep 5439433 = 4079575) B4079575
theorem B7252577 : Blo 2147435 7252577 := bstep (se 2 (by rfl) ⟨2719716, by rfl⟩ : syracuseStep 7252577 = 5439433) B5439433
theorem B4835051 : Blo 2147435 4835051 := bstep (se 1 (by rfl) ⟨3626288, by rfl⟩ : syracuseStep 4835051 = 7252577) B7252577
theorem B3223367 : Blo 2147435 3223367 := bstep (se 1 (by rfl) ⟨2417525, by rfl⟩ : syracuseStep 3223367 = 4835051) B4835051
theorem B2148911 : Blo 2147435 2148911 := bstep (se 1 (by rfl) ⟨1611683, by rfl⟩ : syracuseStep 2148911 = 3223367) B3223367
theorem B3223373 : Blo 2147435 3223373 := bbase (se 3 (by rfl) ⟨604382, by rfl⟩ : syracuseStep 3223373 = 1208765) (by norm_num)
theorem B2148915 : Blo 2147435 2148915 := bstep (se 1 (by rfl) ⟨1611686, by rfl⟩ : syracuseStep 2148915 = 3223373) B3223373
theorem B4835069 : Blo 2147435 4835069 := bbase (se 3 (by rfl) ⟨906575, by rfl⟩ : syracuseStep 4835069 = 1813151) (by norm_num)
theorem B3223379 : Blo 2147435 3223379 := bstep (se 1 (by rfl) ⟨2417534, by rfl⟩ : syracuseStep 3223379 = 4835069) B4835069
theorem B2148919 : Blo 2147435 2148919 := bstep (se 1 (by rfl) ⟨1611689, by rfl⟩ : syracuseStep 2148919 = 3223379) B3223379
theorem B3626309 : Blo 2147435 3626309 := bbase (se 4 (by rfl) ⟨339966, by rfl⟩ : syracuseStep 3626309 = 679933) (by norm_num)
theorem B2417539 : Blo 2147435 2417539 := bstep (se 1 (by rfl) ⟨1813154, by rfl⟩ : syracuseStep 2417539 = 3626309) B3626309
theorem B3223385 : Blo 2147435 3223385 := bstep (se 2 (by rfl) ⟨1208769, by rfl⟩ : syracuseStep 3223385 = 2417539) B2417539
theorem B2148923 : Blo 2147435 2148923 := bstep (se 1 (by rfl) ⟨1611692, by rfl⟩ : syracuseStep 2148923 = 3223385) B3223385
theorem B16318421 : Blo 2147435 16318421 := bbase (se 7 (by rfl) ⟨191231, by rfl⟩ : syracuseStep 16318421 = 382463) (by norm_num)
theorem B10878947 : Blo 2147435 10878947 := bstep (se 1 (by rfl) ⟨8159210, by rfl⟩ : syracuseStep 10878947 = 16318421) B16318421
theorem B7252631 : Blo 2147435 7252631 := bstep (se 1 (by rfl) ⟨5439473, by rfl⟩ : syracuseStep 7252631 = 10878947) B10878947
theorem B4835087 : Blo 2147435 4835087 := bstep (se 1 (by rfl) ⟨3626315, by rfl⟩ : syracuseStep 4835087 = 7252631) B7252631
theorem B3223391 : Blo 2147435 3223391 := bstep (se 1 (by rfl) ⟨2417543, by rfl⟩ : syracuseStep 3223391 = 4835087) B4835087
theorem B2148927 : Blo 2147435 2148927 := bstep (se 1 (by rfl) ⟨1611695, by rfl⟩ : syracuseStep 2148927 = 3223391) B3223391
theorem B3223397 : Blo 2147435 3223397 := bbase (se 4 (by rfl) ⟨302193, by rfl⟩ : syracuseStep 3223397 = 604387) (by norm_num)
theorem B2148931 : Blo 2147435 2148931 := bstep (se 1 (by rfl) ⟨1611698, by rfl⟩ : syracuseStep 2148931 = 3223397) B3223397
theorem B4079621 : Blo 2147435 4079621 := bbase (se 4 (by rfl) ⟨382464, by rfl⟩ : syracuseStep 4079621 = 764929) (by norm_num)
theorem B2719747 : Blo 2147435 2719747 := bstep (se 1 (by rfl) ⟨2039810, by rfl⟩ : syracuseStep 2719747 = 4079621) B4079621
theorem B3626329 : Blo 2147435 3626329 := bstep (se 2 (by rfl) ⟨1359873, by rfl⟩ : syracuseStep 3626329 = 2719747) B2719747
theorem B4835105 : Blo 2147435 4835105 := bstep (se 2 (by rfl) ⟨1813164, by rfl⟩ : syracuseStep 4835105 = 3626329) B3626329
theorem B3223403 : Blo 2147435 3223403 := bstep (se 1 (by rfl) ⟨2417552, by rfl⟩ : syracuseStep 3223403 = 4835105) B4835105
theorem B2148935 : Blo 2147435 2148935 := bstep (se 1 (by rfl) ⟨1611701, by rfl⟩ : syracuseStep 2148935 = 3223403) B3223403
theorem B2417557 : Blo 2147435 2417557 := bbase (se 6 (by rfl) ⟨56661, by rfl⟩ : syracuseStep 2417557 = 113323) (by norm_num)
theorem B3223409 : Blo 2147435 3223409 := bstep (se 2 (by rfl) ⟨1208778, by rfl⟩ : syracuseStep 3223409 = 2417557) B2417557
theorem B2148939 : Blo 2147435 2148939 := bstep (se 1 (by rfl) ⟨1611704, by rfl⟩ : syracuseStep 2148939 = 3223409) B3223409
theorem B2719757 : Blo 2147435 2719757 := bbase (se 3 (by rfl) ⟨509954, by rfl⟩ : syracuseStep 2719757 = 1019909) (by norm_num)
theorem B7252685 : Blo 2147435 7252685 := bstep (se 3 (by rfl) ⟨1359878, by rfl⟩ : syracuseStep 7252685 = 2719757) B2719757
theorem B4835123 : Blo 2147435 4835123 := bstep (se 1 (by rfl) ⟨3626342, by rfl⟩ : syracuseStep 4835123 = 7252685) B7252685
theorem B3223415 : Blo 2147435 3223415 := bstep (se 1 (by rfl) ⟨2417561, by rfl⟩ : syracuseStep 3223415 = 4835123) B4835123
theorem B2148943 : Blo 2147435 2148943 := bstep (se 1 (by rfl) ⟨1611707, by rfl⟩ : syracuseStep 2148943 = 3223415) B3223415
theorem B3223421 : Blo 2147435 3223421 := bbase (se 3 (by rfl) ⟨604391, by rfl⟩ : syracuseStep 3223421 = 1208783) (by norm_num)
theorem B2148947 : Blo 2147435 2148947 := bstep (se 1 (by rfl) ⟨1611710, by rfl⟩ : syracuseStep 2148947 = 3223421) B3223421
theorem B4835141 : Blo 2147435 4835141 := bbase (se 4 (by rfl) ⟨453294, by rfl⟩ : syracuseStep 4835141 = 906589) (by norm_num)
theorem B3223427 : Blo 2147435 3223427 := bstep (se 1 (by rfl) ⟨2417570, by rfl⟩ : syracuseStep 3223427 = 4835141) B4835141
theorem B2148951 : Blo 2147435 2148951 := bstep (se 1 (by rfl) ⟨1611713, by rfl⟩ : syracuseStep 2148951 = 3223427) B3223427
theorem B3442213 : Blo 2147435 3442213 := bbase (se 4 (by rfl) ⟨322707, by rfl⟩ : syracuseStep 3442213 = 645415) (by norm_num)
theorem B4589617 : Blo 2147435 4589617 := bstep (se 2 (by rfl) ⟨1721106, by rfl⟩ : syracuseStep 4589617 = 3442213) B3442213
theorem B6119489 : Blo 2147435 6119489 := bstep (se 2 (by rfl) ⟨2294808, by rfl⟩ : syracuseStep 6119489 = 4589617) B4589617
theorem B4079659 : Blo 2147435 4079659 := bstep (se 1 (by rfl) ⟨3059744, by rfl⟩ : syracuseStep 4079659 = 6119489) B6119489
theorem B5439545 : Blo 2147435 5439545 := bstep (se 2 (by rfl) ⟨2039829, by rfl⟩ : syracuseStep 5439545 = 4079659) B4079659
theorem B3626363 : Blo 2147435 3626363 := bstep (se 1 (by rfl) ⟨2719772, by rfl⟩ : syracuseStep 3626363 = 5439545) B5439545
theorem B2417575 : Blo 2147435 2417575 := bstep (se 1 (by rfl) ⟨1813181, by rfl⟩ : syracuseStep 2417575 = 3626363) B3626363
theorem B3223433 : Blo 2147435 3223433 := bstep (se 2 (by rfl) ⟨1208787, by rfl⟩ : syracuseStep 3223433 = 2417575) B2417575
theorem B2148955 : Blo 2147435 2148955 := bstep (se 1 (by rfl) ⟨1611716, by rfl⟩ : syracuseStep 2148955 = 3223433) B3223433
theorem B10879109 : Blo 2147435 10879109 := bbase (se 4 (by rfl) ⟨1019916, by rfl⟩ : syracuseStep 10879109 = 2039833) (by norm_num)
theorem B7252739 : Blo 2147435 7252739 := bstep (se 1 (by rfl) ⟨5439554, by rfl⟩ : syracuseStep 7252739 = 10879109) B10879109
theorem B4835159 : Blo 2147435 4835159 := bstep (se 1 (by rfl) ⟨3626369, by rfl⟩ : syracuseStep 4835159 = 7252739) B7252739
theorem B3223439 : Blo 2147435 3223439 := bstep (se 1 (by rfl) ⟨2417579, by rfl⟩ : syracuseStep 3223439 = 4835159) B4835159
theorem B2148959 : Blo 2147435 2148959 := bstep (se 1 (by rfl) ⟨1611719, by rfl⟩ : syracuseStep 2148959 = 3223439) B3223439
theorem B3223445 : Blo 2147435 3223445 := bbase (se 6 (by rfl) ⟨75549, by rfl⟩ : syracuseStep 3223445 = 151099) (by norm_num)
theorem B2148963 : Blo 2147435 2148963 := bstep (se 1 (by rfl) ⟨1611722, by rfl⟩ : syracuseStep 2148963 = 3223445) B3223445
theorem B2294821 : Blo 2147435 2294821 := bbase (se 4 (by rfl) ⟨215139, by rfl⟩ : syracuseStep 2294821 = 430279) (by norm_num)
theorem B12239045 : Blo 2147435 12239045 := bstep (se 4 (by rfl) ⟨1147410, by rfl⟩ : syracuseStep 12239045 = 2294821) B2294821
theorem B8159363 : Blo 2147435 8159363 := bstep (se 1 (by rfl) ⟨6119522, by rfl⟩ : syracuseStep 8159363 = 12239045) B12239045
theorem B5439575 : Blo 2147435 5439575 := bstep (se 1 (by rfl) ⟨4079681, by rfl⟩ : syracuseStep 5439575 = 8159363) B8159363
theorem B3626383 : Blo 2147435 3626383 := bstep (se 1 (by rfl) ⟨2719787, by rfl⟩ : syracuseStep 3626383 = 5439575) B5439575
theorem B4835177 : Blo 2147435 4835177 := bstep (se 2 (by rfl) ⟨1813191, by rfl⟩ : syracuseStep 4835177 = 3626383) B3626383
theorem B3223451 : Blo 2147435 3223451 := bstep (se 1 (by rfl) ⟨2417588, by rfl⟩ : syracuseStep 3223451 = 4835177) B4835177
theorem B2148967 : Blo 2147435 2148967 := bstep (se 1 (by rfl) ⟨1611725, by rfl⟩ : syracuseStep 2148967 = 3223451) B3223451
theorem B2417593 : Blo 2147435 2417593 := bbase (se 2 (by rfl) ⟨906597, by rfl⟩ : syracuseStep 2417593 = 1813195) (by norm_num)
theorem B3223457 : Blo 2147435 3223457 := bstep (se 2 (by rfl) ⟨1208796, by rfl⟩ : syracuseStep 3223457 = 2417593) B2417593
theorem B2148971 : Blo 2147435 2148971 := bstep (se 1 (by rfl) ⟨1611728, by rfl⟩ : syracuseStep 2148971 = 3223457) B3223457
theorem B7452053 : Blo 2147435 7452053 := bbase (se 6 (by rfl) ⟨174657, by rfl⟩ : syracuseStep 7452053 = 349315) (by norm_num)
theorem B4968035 : Blo 2147435 4968035 := bstep (se 1 (by rfl) ⟨3726026, by rfl⟩ : syracuseStep 4968035 = 7452053) B7452053
theorem B3312023 : Blo 2147435 3312023 := bstep (se 1 (by rfl) ⟨2484017, by rfl⟩ : syracuseStep 3312023 = 4968035) B4968035
theorem B8832061 : Blo 2147435 8832061 := bstep (se 3 (by rfl) ⟨1656011, by rfl⟩ : syracuseStep 8832061 = 3312023) B3312023
theorem B47104325 : Blo 2147435 47104325 := bstep (se 4 (by rfl) ⟨4416030, by rfl⟩ : syracuseStep 47104325 = 8832061) B8832061
theorem B31402883 : Blo 2147435 31402883 := bstep (se 1 (by rfl) ⟨23552162, by rfl⟩ : syracuseStep 31402883 = 47104325) B47104325
theorem B20935255 : Blo 2147435 20935255 := bstep (se 1 (by rfl) ⟨15701441, by rfl⟩ : syracuseStep 20935255 = 31402883) B31402883
theorem B27913673 : Blo 2147435 27913673 := bstep (se 2 (by rfl) ⟨10467627, by rfl⟩ : syracuseStep 27913673 = 20935255) B20935255
theorem B18609115 : Blo 2147435 18609115 := bstep (se 1 (by rfl) ⟨13956836, by rfl⟩ : syracuseStep 18609115 = 27913673) B27913673
theorem B24812153 : Blo 2147435 24812153 := bstep (se 2 (by rfl) ⟨9304557, by rfl⟩ : syracuseStep 24812153 = 18609115) B18609115
theorem B16541435 : Blo 2147435 16541435 := bstep (se 1 (by rfl) ⟨12406076, by rfl⟩ : syracuseStep 16541435 = 24812153) B24812153
theorem B44110493 : Blo 2147435 44110493 := bstep (se 3 (by rfl) ⟨8270717, by rfl⟩ : syracuseStep 44110493 = 16541435) B16541435
theorem B29406995 : Blo 2147435 29406995 := bstep (se 1 (by rfl) ⟨22055246, by rfl⟩ : syracuseStep 29406995 = 44110493) B44110493
theorem B19604663 : Blo 2147435 19604663 := bstep (se 1 (by rfl) ⟨14703497, by rfl⟩ : syracuseStep 19604663 = 29406995) B29406995
theorem B13069775 : Blo 2147435 13069775 := bstep (se 1 (by rfl) ⟨9802331, by rfl⟩ : syracuseStep 13069775 = 19604663) B19604663
theorem B8713183 : Blo 2147435 8713183 := bstep (se 1 (by rfl) ⟨6534887, by rfl⟩ : syracuseStep 8713183 = 13069775) B13069775
theorem B11617577 : Blo 2147435 11617577 := bstep (se 2 (by rfl) ⟨4356591, by rfl⟩ : syracuseStep 11617577 = 8713183) B8713183
theorem B7745051 : Blo 2147435 7745051 := bstep (se 1 (by rfl) ⟨5808788, by rfl⟩ : syracuseStep 7745051 = 11617577) B11617577
theorem B5163367 : Blo 2147435 5163367 := bstep (se 1 (by rfl) ⟨3872525, by rfl⟩ : syracuseStep 5163367 = 7745051) B7745051
theorem B6884489 : Blo 2147435 6884489 := bstep (se 2 (by rfl) ⟨2581683, by rfl⟩ : syracuseStep 6884489 = 5163367) B5163367
theorem B4589659 : Blo 2147435 4589659 := bstep (se 1 (by rfl) ⟨3442244, by rfl⟩ : syracuseStep 4589659 = 6884489) B6884489
theorem B6119545 : Blo 2147435 6119545 := bstep (se 2 (by rfl) ⟨2294829, by rfl⟩ : syracuseStep 6119545 = 4589659) B4589659
theorem B8159393 : Blo 2147435 8159393 := bstep (se 2 (by rfl) ⟨3059772, by rfl⟩ : syracuseStep 8159393 = 6119545) B6119545
theorem B5439595 : Blo 2147435 5439595 := bstep (se 1 (by rfl) ⟨4079696, by rfl⟩ : syracuseStep 5439595 = 8159393) B8159393
theorem B7252793 : Blo 2147435 7252793 := bstep (se 2 (by rfl) ⟨2719797, by rfl⟩ : syracuseStep 7252793 = 5439595) B5439595
theorem B4835195 : Blo 2147435 4835195 := bstep (se 1 (by rfl) ⟨3626396, by rfl⟩ : syracuseStep 4835195 = 7252793) B7252793
theorem B3223463 : Blo 2147435 3223463 := bstep (se 1 (by rfl) ⟨2417597, by rfl⟩ : syracuseStep 3223463 = 4835195) B4835195
theorem B2148975 : Blo 2147435 2148975 := bstep (se 1 (by rfl) ⟨1611731, by rfl⟩ : syracuseStep 2148975 = 3223463) B3223463
theorem B3223469 : Blo 2147435 3223469 := bbase (se 3 (by rfl) ⟨604400, by rfl⟩ : syracuseStep 3223469 = 1208801) (by norm_num)
theorem B2148979 : Blo 2147435 2148979 := bstep (se 1 (by rfl) ⟨1611734, by rfl⟩ : syracuseStep 2148979 = 3223469) B3223469
theorem B4835213 : Blo 2147435 4835213 := bbase (se 3 (by rfl) ⟨906602, by rfl⟩ : syracuseStep 4835213 = 1813205) (by norm_num)
theorem B3223475 : Blo 2147435 3223475 := bstep (se 1 (by rfl) ⟨2417606, by rfl⟩ : syracuseStep 3223475 = 4835213) B4835213
theorem B2148983 : Blo 2147435 2148983 := bstep (se 1 (by rfl) ⟨1611737, by rfl⟩ : syracuseStep 2148983 = 3223475) B3223475
theorem B2719813 : Blo 2147435 2719813 := bbase (se 4 (by rfl) ⟨254982, by rfl⟩ : syracuseStep 2719813 = 509965) (by norm_num)
theorem B3626417 : Blo 2147435 3626417 := bstep (se 2 (by rfl) ⟨1359906, by rfl⟩ : syracuseStep 3626417 = 2719813) B2719813
theorem B2417611 : Blo 2147435 2417611 := bstep (se 1 (by rfl) ⟨1813208, by rfl⟩ : syracuseStep 2417611 = 3626417) B3626417
theorem B3223481 : Blo 2147435 3223481 := bstep (se 2 (by rfl) ⟨1208805, by rfl⟩ : syracuseStep 3223481 = 2417611) B2417611
theorem B2148987 : Blo 2147435 2148987 := bstep (se 1 (by rfl) ⟨1611740, by rfl⟩ : syracuseStep 2148987 = 3223481) B3223481
theorem B14703605 : Blo 2147435 14703605 := bbase (se 5 (by rfl) ⟨689231, by rfl⟩ : syracuseStep 14703605 = 1378463) (by norm_num)
theorem B9802403 : Blo 2147435 9802403 := bstep (se 1 (by rfl) ⟨7351802, by rfl⟩ : syracuseStep 9802403 = 14703605) B14703605
theorem B6534935 : Blo 2147435 6534935 := bstep (se 1 (by rfl) ⟨4901201, by rfl⟩ : syracuseStep 6534935 = 9802403) B9802403
theorem B4356623 : Blo 2147435 4356623 := bstep (se 1 (by rfl) ⟨3267467, by rfl⟩ : syracuseStep 4356623 = 6534935) B6534935
theorem B11617661 : Blo 2147435 11617661 := bstep (se 3 (by rfl) ⟨2178311, by rfl⟩ : syracuseStep 11617661 = 4356623) B4356623
theorem B7745107 : Blo 2147435 7745107 := bstep (se 1 (by rfl) ⟨5808830, by rfl⟩ : syracuseStep 7745107 = 11617661) B11617661
theorem B10326809 : Blo 2147435 10326809 := bstep (se 2 (by rfl) ⟨3872553, by rfl⟩ : syracuseStep 10326809 = 7745107) B7745107
theorem B27538157 : Blo 2147435 27538157 := bstep (se 3 (by rfl) ⟨5163404, by rfl⟩ : syracuseStep 27538157 = 10326809) B10326809
theorem B18358771 : Blo 2147435 18358771 := bstep (se 1 (by rfl) ⟨13769078, by rfl⟩ : syracuseStep 18358771 = 27538157) B27538157
theorem B24478361 : Blo 2147435 24478361 := bstep (se 2 (by rfl) ⟨9179385, by rfl⟩ : syracuseStep 24478361 = 18358771) B18358771
theorem B16318907 : Blo 2147435 16318907 := bstep (se 1 (by rfl) ⟨12239180, by rfl⟩ : syracuseStep 16318907 = 24478361) B24478361
theorem B10879271 : Blo 2147435 10879271 := bstep (se 1 (by rfl) ⟨8159453, by rfl⟩ : syracuseStep 10879271 = 16318907) B16318907
theorem B7252847 : Blo 2147435 7252847 := bstep (se 1 (by rfl) ⟨5439635, by rfl⟩ : syracuseStep 7252847 = 10879271) B10879271
theorem B4835231 : Blo 2147435 4835231 := bstep (se 1 (by rfl) ⟨3626423, by rfl⟩ : syracuseStep 4835231 = 7252847) B7252847
theorem B3223487 : Blo 2147435 3223487 := bstep (se 1 (by rfl) ⟨2417615, by rfl⟩ : syracuseStep 3223487 = 4835231) B4835231
theorem B2148991 : Blo 2147435 2148991 := bstep (se 1 (by rfl) ⟨1611743, by rfl⟩ : syracuseStep 2148991 = 3223487) B3223487
theorem B3223493 : Blo 2147435 3223493 := bbase (se 4 (by rfl) ⟨302202, by rfl⟩ : syracuseStep 3223493 = 604405) (by norm_num)
theorem B2148995 : Blo 2147435 2148995 := bstep (se 1 (by rfl) ⟨1611746, by rfl⟩ : syracuseStep 2148995 = 3223493) B3223493
theorem B3626437 : Blo 2147435 3626437 := bbase (se 4 (by rfl) ⟨339978, by rfl⟩ : syracuseStep 3626437 = 679957) (by norm_num)
theorem B4835249 : Blo 2147435 4835249 := bstep (se 2 (by rfl) ⟨1813218, by rfl⟩ : syracuseStep 4835249 = 3626437) B3626437
theorem B3223499 : Blo 2147435 3223499 := bstep (se 1 (by rfl) ⟨2417624, by rfl⟩ : syracuseStep 3223499 = 4835249) B4835249
theorem B2148999 : Blo 2147435 2148999 := bstep (se 1 (by rfl) ⟨1611749, by rfl⟩ : syracuseStep 2148999 = 3223499) B3223499
theorem B2417629 : Blo 2147435 2417629 := bbase (se 3 (by rfl) ⟨453305, by rfl⟩ : syracuseStep 2417629 = 906611) (by norm_num)
theorem B3223505 : Blo 2147435 3223505 := bstep (se 2 (by rfl) ⟨1208814, by rfl⟩ : syracuseStep 3223505 = 2417629) B2417629
theorem B2149003 : Blo 2147435 2149003 := bstep (se 1 (by rfl) ⟨1611752, by rfl⟩ : syracuseStep 2149003 = 3223505) B3223505
theorem B7252901 : Blo 2147435 7252901 := bbase (se 4 (by rfl) ⟨679959, by rfl⟩ : syracuseStep 7252901 = 1359919) (by norm_num)
theorem B4835267 : Blo 2147435 4835267 := bstep (se 1 (by rfl) ⟨3626450, by rfl⟩ : syracuseStep 4835267 = 7252901) B7252901
theorem B3223511 : Blo 2147435 3223511 := bstep (se 1 (by rfl) ⟨2417633, by rfl⟩ : syracuseStep 3223511 = 4835267) B4835267
theorem B2149007 : Blo 2147435 2149007 := bstep (se 1 (by rfl) ⟨1611755, by rfl⟩ : syracuseStep 2149007 = 3223511) B3223511
theorem B3223517 : Blo 2147435 3223517 := bbase (se 3 (by rfl) ⟨604409, by rfl⟩ : syracuseStep 3223517 = 1208819) (by norm_num)
theorem B2149011 : Blo 2147435 2149011 := bstep (se 1 (by rfl) ⟨1611758, by rfl⟩ : syracuseStep 2149011 = 3223517) B3223517
theorem B4835285 : Blo 2147435 4835285 := bbase (se 7 (by rfl) ⟨56663, by rfl⟩ : syracuseStep 4835285 = 113327) (by norm_num)
theorem B3223523 : Blo 2147435 3223523 := bstep (se 1 (by rfl) ⟨2417642, by rfl⟩ : syracuseStep 3223523 = 4835285) B4835285
theorem B2149015 : Blo 2147435 2149015 := bstep (se 1 (by rfl) ⟨1611761, by rfl⟩ : syracuseStep 2149015 = 3223523) B3223523
theorem B3872605 : Blo 2147435 3872605 := bbase (se 3 (by rfl) ⟨726113, by rfl⟩ : syracuseStep 3872605 = 1452227) (by norm_num)
theorem B5163473 : Blo 2147435 5163473 := bstep (se 2 (by rfl) ⟨1936302, by rfl⟩ : syracuseStep 5163473 = 3872605) B3872605
theorem B13769261 : Blo 2147435 13769261 := bstep (se 3 (by rfl) ⟨2581736, by rfl⟩ : syracuseStep 13769261 = 5163473) B5163473
theorem B9179507 : Blo 2147435 9179507 := bstep (se 1 (by rfl) ⟨6884630, by rfl⟩ : syracuseStep 9179507 = 13769261) B13769261
theorem B6119671 : Blo 2147435 6119671 := bstep (se 1 (by rfl) ⟨4589753, by rfl⟩ : syracuseStep 6119671 = 9179507) B9179507
theorem B8159561 : Blo 2147435 8159561 := bstep (se 2 (by rfl) ⟨3059835, by rfl⟩ : syracuseStep 8159561 = 6119671) B6119671
theorem B5439707 : Blo 2147435 5439707 := bstep (se 1 (by rfl) ⟨4079780, by rfl⟩ : syracuseStep 5439707 = 8159561) B8159561
theorem B3626471 : Blo 2147435 3626471 := bstep (se 1 (by rfl) ⟨2719853, by rfl⟩ : syracuseStep 3626471 = 5439707) B5439707
theorem B2417647 : Blo 2147435 2417647 := bstep (se 1 (by rfl) ⟨1813235, by rfl⟩ : syracuseStep 2417647 = 3626471) B3626471
theorem B3223529 : Blo 2147435 3223529 := bstep (se 2 (by rfl) ⟨1208823, by rfl⟩ : syracuseStep 3223529 = 2417647) B2417647
theorem B2149019 : Blo 2147435 2149019 := bstep (se 1 (by rfl) ⟨1611764, by rfl⟩ : syracuseStep 2149019 = 3223529) B3223529
theorem B2581741 : Blo 2147435 2581741 := bbase (se 3 (by rfl) ⟨484076, by rfl⟩ : syracuseStep 2581741 = 968153) (by norm_num)
theorem B3442321 : Blo 2147435 3442321 := bstep (se 2 (by rfl) ⟨1290870, by rfl⟩ : syracuseStep 3442321 = 2581741) B2581741
theorem B18359045 : Blo 2147435 18359045 := bstep (se 4 (by rfl) ⟨1721160, by rfl⟩ : syracuseStep 18359045 = 3442321) B3442321
theorem B12239363 : Blo 2147435 12239363 := bstep (se 1 (by rfl) ⟨9179522, by rfl⟩ : syracuseStep 12239363 = 18359045) B18359045
theorem B8159575 : Blo 2147435 8159575 := bstep (se 1 (by rfl) ⟨6119681, by rfl⟩ : syracuseStep 8159575 = 12239363) B12239363
theorem B10879433 : Blo 2147435 10879433 := bstep (se 2 (by rfl) ⟨4079787, by rfl⟩ : syracuseStep 10879433 = 8159575) B8159575
theorem B7252955 : Blo 2147435 7252955 := bstep (se 1 (by rfl) ⟨5439716, by rfl⟩ : syracuseStep 7252955 = 10879433) B10879433
theorem B4835303 : Blo 2147435 4835303 := bstep (se 1 (by rfl) ⟨3626477, by rfl⟩ : syracuseStep 4835303 = 7252955) B7252955
theorem B3223535 : Blo 2147435 3223535 := bstep (se 1 (by rfl) ⟨2417651, by rfl⟩ : syracuseStep 3223535 = 4835303) B4835303
theorem B2149023 : Blo 2147435 2149023 := bstep (se 1 (by rfl) ⟨1611767, by rfl⟩ : syracuseStep 2149023 = 3223535) B3223535
theorem B3223541 : Blo 2147435 3223541 := bbase (se 5 (by rfl) ⟨151103, by rfl⟩ : syracuseStep 3223541 = 302207) (by norm_num)
theorem B2149027 : Blo 2147435 2149027 := bstep (se 1 (by rfl) ⟨1611770, by rfl⟩ : syracuseStep 2149027 = 3223541) B3223541
theorem B2178353 : Blo 2147435 2178353 := bbase (se 2 (by rfl) ⟨816882, by rfl⟩ : syracuseStep 2178353 = 1633765) (by norm_num)
theorem B5808941 : Blo 2147435 5808941 := bstep (se 3 (by rfl) ⟨1089176, by rfl⟩ : syracuseStep 5808941 = 2178353) B2178353
theorem B3872627 : Blo 2147435 3872627 := bstep (se 1 (by rfl) ⟨2904470, by rfl⟩ : syracuseStep 3872627 = 5808941) B5808941
theorem B2581751 : Blo 2147435 2581751 := bstep (se 1 (by rfl) ⟨1936313, by rfl⟩ : syracuseStep 2581751 = 3872627) B3872627
theorem B6884669 : Blo 2147435 6884669 := bstep (se 3 (by rfl) ⟨1290875, by rfl⟩ : syracuseStep 6884669 = 2581751) B2581751
theorem B4589779 : Blo 2147435 4589779 := bstep (se 1 (by rfl) ⟨3442334, by rfl⟩ : syracuseStep 4589779 = 6884669) B6884669
theorem B6119705 : Blo 2147435 6119705 := bstep (se 2 (by rfl) ⟨2294889, by rfl⟩ : syracuseStep 6119705 = 4589779) B4589779
theorem B4079803 : Blo 2147435 4079803 := bstep (se 1 (by rfl) ⟨3059852, by rfl⟩ : syracuseStep 4079803 = 6119705) B6119705
theorem B5439737 : Blo 2147435 5439737 := bstep (se 2 (by rfl) ⟨2039901, by rfl⟩ : syracuseStep 5439737 = 4079803) B4079803
theorem B3626491 : Blo 2147435 3626491 := bstep (se 1 (by rfl) ⟨2719868, by rfl⟩ : syracuseStep 3626491 = 5439737) B5439737
theorem B4835321 : Blo 2147435 4835321 := bstep (se 2 (by rfl) ⟨1813245, by rfl⟩ : syracuseStep 4835321 = 3626491) B3626491
theorem B3223547 : Blo 2147435 3223547 := bstep (se 1 (by rfl) ⟨2417660, by rfl⟩ : syracuseStep 3223547 = 4835321) B4835321
theorem B2149031 : Blo 2147435 2149031 := bstep (se 1 (by rfl) ⟨1611773, by rfl⟩ : syracuseStep 2149031 = 3223547) B3223547
theorem B2417665 : Blo 2147435 2417665 := bbase (se 2 (by rfl) ⟨906624, by rfl⟩ : syracuseStep 2417665 = 1813249) (by norm_num)
theorem B3223553 : Blo 2147435 3223553 := bstep (se 2 (by rfl) ⟨1208832, by rfl⟩ : syracuseStep 3223553 = 2417665) B2417665
theorem B2149035 : Blo 2147435 2149035 := bstep (se 1 (by rfl) ⟨1611776, by rfl⟩ : syracuseStep 2149035 = 3223553) B3223553
theorem B5439757 : Blo 2147435 5439757 := bbase (se 3 (by rfl) ⟨1019954, by rfl⟩ : syracuseStep 5439757 = 2039909) (by norm_num)
theorem B7253009 : Blo 2147435 7253009 := bstep (se 2 (by rfl) ⟨2719878, by rfl⟩ : syracuseStep 7253009 = 5439757) B5439757
theorem B4835339 : Blo 2147435 4835339 := bstep (se 1 (by rfl) ⟨3626504, by rfl⟩ : syracuseStep 4835339 = 7253009) B7253009
theorem B3223559 : Blo 2147435 3223559 := bstep (se 1 (by rfl) ⟨2417669, by rfl⟩ : syracuseStep 3223559 = 4835339) B4835339
theorem B2149039 : Blo 2147435 2149039 := bstep (se 1 (by rfl) ⟨1611779, by rfl⟩ : syracuseStep 2149039 = 3223559) B3223559
theorem B3223565 : Blo 2147435 3223565 := bbase (se 3 (by rfl) ⟨604418, by rfl⟩ : syracuseStep 3223565 = 1208837) (by norm_num)
theorem B2149043 : Blo 2147435 2149043 := bstep (se 1 (by rfl) ⟨1611782, by rfl⟩ : syracuseStep 2149043 = 3223565) B3223565
theorem B4835357 : Blo 2147435 4835357 := bbase (se 3 (by rfl) ⟨906629, by rfl⟩ : syracuseStep 4835357 = 1813259) (by norm_num)
theorem B3223571 : Blo 2147435 3223571 := bstep (se 1 (by rfl) ⟨2417678, by rfl⟩ : syracuseStep 3223571 = 4835357) B4835357
theorem B2149047 : Blo 2147435 2149047 := bstep (se 1 (by rfl) ⟨1611785, by rfl⟩ : syracuseStep 2149047 = 3223571) B3223571
theorem B3626525 : Blo 2147435 3626525 := bbase (se 3 (by rfl) ⟨679973, by rfl⟩ : syracuseStep 3626525 = 1359947) (by norm_num)
theorem B2417683 : Blo 2147435 2417683 := bstep (se 1 (by rfl) ⟨1813262, by rfl⟩ : syracuseStep 2417683 = 3626525) B3626525
theorem B3223577 : Blo 2147435 3223577 := bstep (se 2 (by rfl) ⟨1208841, by rfl⟩ : syracuseStep 3223577 = 2417683) B2417683
theorem B2149051 : Blo 2147435 2149051 := bstep (se 1 (by rfl) ⟨1611788, by rfl⟩ : syracuseStep 2149051 = 3223577) B3223577
theorem B3872669 : Blo 2147435 3872669 := bbase (se 3 (by rfl) ⟨726125, by rfl⟩ : syracuseStep 3872669 = 1452251) (by norm_num)
theorem B10327117 : Blo 2147435 10327117 := bstep (se 3 (by rfl) ⟨1936334, by rfl⟩ : syracuseStep 10327117 = 3872669) B3872669
theorem B13769489 : Blo 2147435 13769489 := bstep (se 2 (by rfl) ⟨5163558, by rfl⟩ : syracuseStep 13769489 = 10327117) B10327117
theorem B9179659 : Blo 2147435 9179659 := bstep (se 1 (by rfl) ⟨6884744, by rfl⟩ : syracuseStep 9179659 = 13769489) B13769489
theorem B12239545 : Blo 2147435 12239545 := bstep (se 2 (by rfl) ⟨4589829, by rfl⟩ : syracuseStep 12239545 = 9179659) B9179659
theorem B16319393 : Blo 2147435 16319393 := bstep (se 2 (by rfl) ⟨6119772, by rfl⟩ : syracuseStep 16319393 = 12239545) B12239545
theorem B10879595 : Blo 2147435 10879595 := bstep (se 1 (by rfl) ⟨8159696, by rfl⟩ : syracuseStep 10879595 = 16319393) B16319393
theorem B7253063 : Blo 2147435 7253063 := bstep (se 1 (by rfl) ⟨5439797, by rfl⟩ : syracuseStep 7253063 = 10879595) B10879595
theorem B4835375 : Blo 2147435 4835375 := bstep (se 1 (by rfl) ⟨3626531, by rfl⟩ : syracuseStep 4835375 = 7253063) B7253063
theorem B3223583 : Blo 2147435 3223583 := bstep (se 1 (by rfl) ⟨2417687, by rfl⟩ : syracuseStep 3223583 = 4835375) B4835375
theorem B2149055 : Blo 2147435 2149055 := bstep (se 1 (by rfl) ⟨1611791, by rfl⟩ : syracuseStep 2149055 = 3223583) B3223583
theorem B3223589 : Blo 2147435 3223589 := bbase (se 4 (by rfl) ⟨302211, by rfl⟩ : syracuseStep 3223589 = 604423) (by norm_num)
theorem B2149059 : Blo 2147435 2149059 := bstep (se 1 (by rfl) ⟨1611794, by rfl⟩ : syracuseStep 2149059 = 3223589) B3223589
theorem B2719909 : Blo 2147435 2719909 := bbase (se 4 (by rfl) ⟨254991, by rfl⟩ : syracuseStep 2719909 = 509983) (by norm_num)
theorem B3626545 : Blo 2147435 3626545 := bstep (se 2 (by rfl) ⟨1359954, by rfl⟩ : syracuseStep 3626545 = 2719909) B2719909
theorem B4835393 : Blo 2147435 4835393 := bstep (se 2 (by rfl) ⟨1813272, by rfl⟩ : syracuseStep 4835393 = 3626545) B3626545
theorem B3223595 : Blo 2147435 3223595 := bstep (se 1 (by rfl) ⟨2417696, by rfl⟩ : syracuseStep 3223595 = 4835393) B4835393
theorem B2149063 : Blo 2147435 2149063 := bstep (se 1 (by rfl) ⟨1611797, by rfl⟩ : syracuseStep 2149063 = 3223595) B3223595
theorem B2417701 : Blo 2147435 2417701 := bbase (se 4 (by rfl) ⟨226659, by rfl⟩ : syracuseStep 2417701 = 453319) (by norm_num)
theorem B3223601 : Blo 2147435 3223601 := bstep (se 2 (by rfl) ⟨1208850, by rfl⟩ : syracuseStep 3223601 = 2417701) B2417701
theorem B2149067 : Blo 2147435 2149067 := bstep (se 1 (by rfl) ⟨1611800, by rfl⟩ : syracuseStep 2149067 = 3223601) B3223601
theorem B2450693 : Blo 2147435 2450693 := bbase (se 4 (by rfl) ⟨229752, by rfl⟩ : syracuseStep 2450693 = 459505) (by norm_num)
theorem B6535181 : Blo 2147435 6535181 := bstep (se 3 (by rfl) ⟨1225346, by rfl⟩ : syracuseStep 6535181 = 2450693) B2450693
theorem B4356787 : Blo 2147435 4356787 := bstep (se 1 (by rfl) ⟨3267590, by rfl⟩ : syracuseStep 4356787 = 6535181) B6535181
theorem B5809049 : Blo 2147435 5809049 := bstep (se 2 (by rfl) ⟨2178393, by rfl⟩ : syracuseStep 5809049 = 4356787) B4356787
theorem B3872699 : Blo 2147435 3872699 := bstep (se 1 (by rfl) ⟨2904524, by rfl⟩ : syracuseStep 3872699 = 5809049) B5809049
theorem B2581799 : Blo 2147435 2581799 := bstep (se 1 (by rfl) ⟨1936349, by rfl⟩ : syracuseStep 2581799 = 3872699) B3872699
theorem B6884797 : Blo 2147435 6884797 := bstep (se 3 (by rfl) ⟨1290899, by rfl⟩ : syracuseStep 6884797 = 2581799) B2581799
theorem B9179729 : Blo 2147435 9179729 := bstep (se 2 (by rfl) ⟨3442398, by rfl⟩ : syracuseStep 9179729 = 6884797) B6884797
theorem B6119819 : Blo 2147435 6119819 := bstep (se 1 (by rfl) ⟨4589864, by rfl⟩ : syracuseStep 6119819 = 9179729) B9179729
theorem B4079879 : Blo 2147435 4079879 := bstep (se 1 (by rfl) ⟨3059909, by rfl⟩ : syracuseStep 4079879 = 6119819) B6119819
theorem B2719919 : Blo 2147435 2719919 := bstep (se 1 (by rfl) ⟨2039939, by rfl⟩ : syracuseStep 2719919 = 4079879) B4079879
theorem B7253117 : Blo 2147435 7253117 := bstep (se 3 (by rfl) ⟨1359959, by rfl⟩ : syracuseStep 7253117 = 2719919) B2719919
theorem B4835411 : Blo 2147435 4835411 := bstep (se 1 (by rfl) ⟨3626558, by rfl⟩ : syracuseStep 4835411 = 7253117) B7253117
theorem B3223607 : Blo 2147435 3223607 := bstep (se 1 (by rfl) ⟨2417705, by rfl⟩ : syracuseStep 3223607 = 4835411) B4835411
theorem B2149071 : Blo 2147435 2149071 := bstep (se 1 (by rfl) ⟨1611803, by rfl⟩ : syracuseStep 2149071 = 3223607) B3223607
theorem B3223613 : Blo 2147435 3223613 := bbase (se 3 (by rfl) ⟨604427, by rfl⟩ : syracuseStep 3223613 = 1208855) (by norm_num)
theorem B2149075 : Blo 2147435 2149075 := bstep (se 1 (by rfl) ⟨1611806, by rfl⟩ : syracuseStep 2149075 = 3223613) B3223613
theorem B4835429 : Blo 2147435 4835429 := bbase (se 4 (by rfl) ⟨453321, by rfl⟩ : syracuseStep 4835429 = 906643) (by norm_num)
theorem B3223619 : Blo 2147435 3223619 := bstep (se 1 (by rfl) ⟨2417714, by rfl⟩ : syracuseStep 3223619 = 4835429) B4835429
theorem B2149079 : Blo 2147435 2149079 := bstep (se 1 (by rfl) ⟨1611809, by rfl⟩ : syracuseStep 2149079 = 3223619) B3223619
theorem B5439869 : Blo 2147435 5439869 := bbase (se 3 (by rfl) ⟨1019975, by rfl⟩ : syracuseStep 5439869 = 2039951) (by norm_num)
theorem B3626579 : Blo 2147435 3626579 := bstep (se 1 (by rfl) ⟨2719934, by rfl⟩ : syracuseStep 3626579 = 5439869) B5439869
theorem B2417719 : Blo 2147435 2417719 := bstep (se 1 (by rfl) ⟨1813289, by rfl⟩ : syracuseStep 2417719 = 3626579) B3626579
theorem B3223625 : Blo 2147435 3223625 := bstep (se 2 (by rfl) ⟨1208859, by rfl⟩ : syracuseStep 3223625 = 2417719) B2417719
theorem B2149083 : Blo 2147435 2149083 := bstep (se 1 (by rfl) ⟨1611812, by rfl⟩ : syracuseStep 2149083 = 3223625) B3223625
theorem B4079909 : Blo 2147435 4079909 := bbase (se 4 (by rfl) ⟨382491, by rfl⟩ : syracuseStep 4079909 = 764983) (by norm_num)
theorem B10879757 : Blo 2147435 10879757 := bstep (se 3 (by rfl) ⟨2039954, by rfl⟩ : syracuseStep 10879757 = 4079909) B4079909
theorem B7253171 : Blo 2147435 7253171 := bstep (se 1 (by rfl) ⟨5439878, by rfl⟩ : syracuseStep 7253171 = 10879757) B10879757
theorem B4835447 : Blo 2147435 4835447 := bstep (se 1 (by rfl) ⟨3626585, by rfl⟩ : syracuseStep 4835447 = 7253171) B7253171
theorem B3223631 : Blo 2147435 3223631 := bstep (se 1 (by rfl) ⟨2417723, by rfl⟩ : syracuseStep 3223631 = 4835447) B4835447
theorem B2149087 : Blo 2147435 2149087 := bstep (se 1 (by rfl) ⟨1611815, by rfl⟩ : syracuseStep 2149087 = 3223631) B3223631
theorem B3223637 : Blo 2147435 3223637 := bbase (se 8 (by rfl) ⟨18888, by rfl⟩ : syracuseStep 3223637 = 37777) (by norm_num)
theorem B2149091 : Blo 2147435 2149091 := bstep (se 1 (by rfl) ⟨1611818, by rfl⟩ : syracuseStep 2149091 = 3223637) B3223637
theorem B8713669 : Blo 2147435 8713669 := bbase (se 4 (by rfl) ⟨816906, by rfl⟩ : syracuseStep 8713669 = 1633813) (by norm_num)
theorem B11618225 : Blo 2147435 11618225 := bstep (se 2 (by rfl) ⟨4356834, by rfl⟩ : syracuseStep 11618225 = 8713669) B8713669
theorem B7745483 : Blo 2147435 7745483 := bstep (se 1 (by rfl) ⟨5809112, by rfl⟩ : syracuseStep 7745483 = 11618225) B11618225
theorem B20654621 : Blo 2147435 20654621 := bstep (se 3 (by rfl) ⟨3872741, by rfl⟩ : syracuseStep 20654621 = 7745483) B7745483
theorem B13769747 : Blo 2147435 13769747 := bstep (se 1 (by rfl) ⟨10327310, by rfl⟩ : syracuseStep 13769747 = 20654621) B20654621
theorem B9179831 : Blo 2147435 9179831 := bstep (se 1 (by rfl) ⟨6884873, by rfl⟩ : syracuseStep 9179831 = 13769747) B13769747
theorem B6119887 : Blo 2147435 6119887 := bstep (se 1 (by rfl) ⟨4589915, by rfl⟩ : syracuseStep 6119887 = 9179831) B9179831
theorem B8159849 : Blo 2147435 8159849 := bstep (se 2 (by rfl) ⟨3059943, by rfl⟩ : syracuseStep 8159849 = 6119887) B6119887
theorem B5439899 : Blo 2147435 5439899 := bstep (se 1 (by rfl) ⟨4079924, by rfl⟩ : syracuseStep 5439899 = 8159849) B8159849
theorem B3626599 : Blo 2147435 3626599 := bstep (se 1 (by rfl) ⟨2719949, by rfl⟩ : syracuseStep 3626599 = 5439899) B5439899
theorem B4835465 : Blo 2147435 4835465 := bstep (se 2 (by rfl) ⟨1813299, by rfl⟩ : syracuseStep 4835465 = 3626599) B3626599
theorem B3223643 : Blo 2147435 3223643 := bstep (se 1 (by rfl) ⟨2417732, by rfl⟩ : syracuseStep 3223643 = 4835465) B4835465
theorem B2149095 : Blo 2147435 2149095 := bstep (se 1 (by rfl) ⟨1611821, by rfl⟩ : syracuseStep 2149095 = 3223643) B3223643
theorem B2417737 : Blo 2147435 2417737 := bbase (se 2 (by rfl) ⟨906651, by rfl⟩ : syracuseStep 2417737 = 1813303) (by norm_num)
theorem B3223649 : Blo 2147435 3223649 := bstep (se 2 (by rfl) ⟨1208868, by rfl⟩ : syracuseStep 3223649 = 2417737) B2417737
theorem B2149099 : Blo 2147435 2149099 := bstep (se 1 (by rfl) ⟨1611824, by rfl⟩ : syracuseStep 2149099 = 3223649) B3223649
theorem B2581837 : Blo 2147435 2581837 := bbase (se 3 (by rfl) ⟨484094, by rfl⟩ : syracuseStep 2581837 = 968189) (by norm_num)
theorem B13769797 : Blo 2147435 13769797 := bstep (se 4 (by rfl) ⟨1290918, by rfl⟩ : syracuseStep 13769797 = 2581837) B2581837
theorem B18359729 : Blo 2147435 18359729 := bstep (se 2 (by rfl) ⟨6884898, by rfl⟩ : syracuseStep 18359729 = 13769797) B13769797
theorem B12239819 : Blo 2147435 12239819 := bstep (se 1 (by rfl) ⟨9179864, by rfl⟩ : syracuseStep 12239819 = 18359729) B18359729
theorem B8159879 : Blo 2147435 8159879 := bstep (se 1 (by rfl) ⟨6119909, by rfl⟩ : syracuseStep 8159879 = 12239819) B12239819
theorem B5439919 : Blo 2147435 5439919 := bstep (se 1 (by rfl) ⟨4079939, by rfl⟩ : syracuseStep 5439919 = 8159879) B8159879
theorem B7253225 : Blo 2147435 7253225 := bstep (se 2 (by rfl) ⟨2719959, by rfl⟩ : syracuseStep 7253225 = 5439919) B5439919
theorem B4835483 : Blo 2147435 4835483 := bstep (se 1 (by rfl) ⟨3626612, by rfl⟩ : syracuseStep 4835483 = 7253225) B7253225
theorem B3223655 : Blo 2147435 3223655 := bstep (se 1 (by rfl) ⟨2417741, by rfl⟩ : syracuseStep 3223655 = 4835483) B4835483
theorem B2149103 : Blo 2147435 2149103 := bstep (se 1 (by rfl) ⟨1611827, by rfl⟩ : syracuseStep 2149103 = 3223655) B3223655
theorem B3223661 : Blo 2147435 3223661 := bbase (se 3 (by rfl) ⟨604436, by rfl⟩ : syracuseStep 3223661 = 1208873) (by norm_num)
theorem B2149107 : Blo 2147435 2149107 := bstep (se 1 (by rfl) ⟨1611830, by rfl⟩ : syracuseStep 2149107 = 3223661) B3223661
theorem B4835501 : Blo 2147435 4835501 := bbase (se 3 (by rfl) ⟨906656, by rfl⟩ : syracuseStep 4835501 = 1813313) (by norm_num)
theorem B3223667 : Blo 2147435 3223667 := bstep (se 1 (by rfl) ⟨2417750, by rfl⟩ : syracuseStep 3223667 = 4835501) B4835501
theorem B2149111 : Blo 2147435 2149111 := bstep (se 1 (by rfl) ⟨1611833, by rfl⟩ : syracuseStep 2149111 = 3223667) B3223667
theorem B7745557 : Blo 2147435 7745557 := bbase (se 6 (by rfl) ⟨181536, by rfl⟩ : syracuseStep 7745557 = 363073) (by norm_num)
theorem B10327409 : Blo 2147435 10327409 := bstep (se 2 (by rfl) ⟨3872778, by rfl⟩ : syracuseStep 10327409 = 7745557) B7745557
theorem B6884939 : Blo 2147435 6884939 := bstep (se 1 (by rfl) ⟨5163704, by rfl⟩ : syracuseStep 6884939 = 10327409) B10327409
theorem B4589959 : Blo 2147435 4589959 := bstep (se 1 (by rfl) ⟨3442469, by rfl⟩ : syracuseStep 4589959 = 6884939) B6884939
theorem B6119945 : Blo 2147435 6119945 := bstep (se 2 (by rfl) ⟨2294979, by rfl⟩ : syracuseStep 6119945 = 4589959) B4589959
theorem B4079963 : Blo 2147435 4079963 := bstep (se 1 (by rfl) ⟨3059972, by rfl⟩ : syracuseStep 4079963 = 6119945) B6119945
theorem B2719975 : Blo 2147435 2719975 := bstep (se 1 (by rfl) ⟨2039981, by rfl⟩ : syracuseStep 2719975 = 4079963) B4079963
theorem B3626633 : Blo 2147435 3626633 := bstep (se 2 (by rfl) ⟨1359987, by rfl⟩ : syracuseStep 3626633 = 2719975) B2719975
theorem B2417755 : Blo 2147435 2417755 := bstep (se 1 (by rfl) ⟨1813316, by rfl⟩ : syracuseStep 2417755 = 3626633) B3626633
theorem B3223673 : Blo 2147435 3223673 := bstep (se 2 (by rfl) ⟨1208877, by rfl⟩ : syracuseStep 3223673 = 2417755) B2417755
theorem B2149115 : Blo 2147435 2149115 := bstep (se 1 (by rfl) ⟨1611836, by rfl⟩ : syracuseStep 2149115 = 3223673) B3223673
theorem B27539797 : Blo 2147435 27539797 := bbase (se 10 (by rfl) ⟨40341, by rfl⟩ : syracuseStep 27539797 = 80683) (by norm_num)
theorem B36719729 : Blo 2147435 36719729 := bstep (se 2 (by rfl) ⟨13769898, by rfl⟩ : syracuseStep 36719729 = 27539797) B27539797
theorem B24479819 : Blo 2147435 24479819 := bstep (se 1 (by rfl) ⟨18359864, by rfl⟩ : syracuseStep 24479819 = 36719729) B36719729
theorem B16319879 : Blo 2147435 16319879 := bstep (se 1 (by rfl) ⟨12239909, by rfl⟩ : syracuseStep 16319879 = 24479819) B24479819
theorem B10879919 : Blo 2147435 10879919 := bstep (se 1 (by rfl) ⟨8159939, by rfl⟩ : syracuseStep 10879919 = 16319879) B16319879
theorem B7253279 : Blo 2147435 7253279 := bstep (se 1 (by rfl) ⟨5439959, by rfl⟩ : syracuseStep 7253279 = 10879919) B10879919
theorem B4835519 : Blo 2147435 4835519 := bstep (se 1 (by rfl) ⟨3626639, by rfl⟩ : syracuseStep 4835519 = 7253279) B7253279
theorem B3223679 : Blo 2147435 3223679 := bstep (se 1 (by rfl) ⟨2417759, by rfl⟩ : syracuseStep 3223679 = 4835519) B4835519
theorem B2149119 : Blo 2147435 2149119 := bstep (se 1 (by rfl) ⟨1611839, by rfl⟩ : syracuseStep 2149119 = 3223679) B3223679
theorem B3223685 : Blo 2147435 3223685 := bbase (se 4 (by rfl) ⟨302220, by rfl⟩ : syracuseStep 3223685 = 604441) (by norm_num)
theorem B2149123 : Blo 2147435 2149123 := bstep (se 1 (by rfl) ⟨1611842, by rfl⟩ : syracuseStep 2149123 = 3223685) B3223685
theorem B3626653 : Blo 2147435 3626653 := bbase (se 3 (by rfl) ⟨679997, by rfl⟩ : syracuseStep 3626653 = 1359995) (by norm_num)
theorem B4835537 : Blo 2147435 4835537 := bstep (se 2 (by rfl) ⟨1813326, by rfl⟩ : syracuseStep 4835537 = 3626653) B3626653
theorem B3223691 : Blo 2147435 3223691 := bstep (se 1 (by rfl) ⟨2417768, by rfl⟩ : syracuseStep 3223691 = 4835537) B4835537
theorem B2149127 : Blo 2147435 2149127 := bstep (se 1 (by rfl) ⟨1611845, by rfl⟩ : syracuseStep 2149127 = 3223691) B3223691
theorem B2417773 : Blo 2147435 2417773 := bbase (se 3 (by rfl) ⟨453332, by rfl⟩ : syracuseStep 2417773 = 906665) (by norm_num)
theorem B3223697 : Blo 2147435 3223697 := bstep (se 2 (by rfl) ⟨1208886, by rfl⟩ : syracuseStep 3223697 = 2417773) B2417773
theorem B2149131 : Blo 2147435 2149131 := bstep (se 1 (by rfl) ⟨1611848, by rfl⟩ : syracuseStep 2149131 = 3223697) B3223697
theorem B7253333 : Blo 2147435 7253333 := bbase (se 11 (by rfl) ⟨5312, by rfl⟩ : syracuseStep 7253333 = 10625) (by norm_num)
theorem B4835555 : Blo 2147435 4835555 := bstep (se 1 (by rfl) ⟨3626666, by rfl⟩ : syracuseStep 4835555 = 7253333) B7253333
theorem B3223703 : Blo 2147435 3223703 := bstep (se 1 (by rfl) ⟨2417777, by rfl⟩ : syracuseStep 3223703 = 4835555) B4835555
theorem B2149135 : Blo 2147435 2149135 := bstep (se 1 (by rfl) ⟨1611851, by rfl⟩ : syracuseStep 2149135 = 3223703) B3223703
theorem B3223709 : Blo 2147435 3223709 := bbase (se 3 (by rfl) ⟨604445, by rfl⟩ : syracuseStep 3223709 = 1208891) (by norm_num)
theorem B2149139 : Blo 2147435 2149139 := bstep (se 1 (by rfl) ⟨1611854, by rfl⟩ : syracuseStep 2149139 = 3223709) B3223709
theorem B4835573 : Blo 2147435 4835573 := bbase (se 5 (by rfl) ⟨226667, by rfl⟩ : syracuseStep 4835573 = 453335) (by norm_num)
theorem B3223715 : Blo 2147435 3223715 := bstep (se 1 (by rfl) ⟨2417786, by rfl⟩ : syracuseStep 3223715 = 4835573) B4835573
theorem B2149143 : Blo 2147435 2149143 := bstep (se 1 (by rfl) ⟨1611857, by rfl⟩ : syracuseStep 2149143 = 3223715) B3223715
theorem B5809253 : Blo 2147435 5809253 := bbase (se 4 (by rfl) ⟨544617, by rfl⟩ : syracuseStep 5809253 = 1089235) (by norm_num)
theorem B15491341 : Blo 2147435 15491341 := bstep (se 3 (by rfl) ⟨2904626, by rfl⟩ : syracuseStep 15491341 = 5809253) B5809253
theorem B20655121 : Blo 2147435 20655121 := bstep (se 2 (by rfl) ⟨7745670, by rfl⟩ : syracuseStep 20655121 = 15491341) B15491341
theorem B27540161 : Blo 2147435 27540161 := bstep (se 2 (by rfl) ⟨10327560, by rfl⟩ : syracuseStep 27540161 = 20655121) B20655121
theorem B18360107 : Blo 2147435 18360107 := bstep (se 1 (by rfl) ⟨13770080, by rfl⟩ : syracuseStep 18360107 = 27540161) B27540161
theorem B12240071 : Blo 2147435 12240071 := bstep (se 1 (by rfl) ⟨9180053, by rfl⟩ : syracuseStep 12240071 = 18360107) B18360107
theorem B8160047 : Blo 2147435 8160047 := bstep (se 1 (by rfl) ⟨6120035, by rfl⟩ : syracuseStep 8160047 = 12240071) B12240071
theorem B5440031 : Blo 2147435 5440031 := bstep (se 1 (by rfl) ⟨4080023, by rfl⟩ : syracuseStep 5440031 = 8160047) B8160047
theorem B3626687 : Blo 2147435 3626687 := bstep (se 1 (by rfl) ⟨2720015, by rfl⟩ : syracuseStep 3626687 = 5440031) B5440031
theorem B2417791 : Blo 2147435 2417791 := bstep (se 1 (by rfl) ⟨1813343, by rfl⟩ : syracuseStep 2417791 = 3626687) B3626687
theorem B3223721 : Blo 2147435 3223721 := bstep (se 2 (by rfl) ⟨1208895, by rfl⟩ : syracuseStep 3223721 = 2417791) B2417791
theorem B2149147 : Blo 2147435 2149147 := bstep (se 1 (by rfl) ⟨1611860, by rfl⟩ : syracuseStep 2149147 = 3223721) B3223721
theorem B4356949 : Blo 2147435 4356949 := bbase (se 9 (by rfl) ⟨12764, by rfl⟩ : syracuseStep 4356949 = 25529) (by norm_num)
theorem B5809265 : Blo 2147435 5809265 := bstep (se 2 (by rfl) ⟨2178474, by rfl⟩ : syracuseStep 5809265 = 4356949) B4356949
theorem B3872843 : Blo 2147435 3872843 := bstep (se 1 (by rfl) ⟨2904632, by rfl⟩ : syracuseStep 3872843 = 5809265) B5809265
theorem B2581895 : Blo 2147435 2581895 := bstep (se 1 (by rfl) ⟨1936421, by rfl⟩ : syracuseStep 2581895 = 3872843) B3872843
theorem B6885053 : Blo 2147435 6885053 := bstep (se 3 (by rfl) ⟨1290947, by rfl⟩ : syracuseStep 6885053 = 2581895) B2581895
theorem B4590035 : Blo 2147435 4590035 := bstep (se 1 (by rfl) ⟨3442526, by rfl⟩ : syracuseStep 4590035 = 6885053) B6885053
theorem B3060023 : Blo 2147435 3060023 := bstep (se 1 (by rfl) ⟨2295017, by rfl⟩ : syracuseStep 3060023 = 4590035) B4590035
theorem B8160061 : Blo 2147435 8160061 := bstep (se 3 (by rfl) ⟨1530011, by rfl⟩ : syracuseStep 8160061 = 3060023) B3060023
theorem B10880081 : Blo 2147435 10880081 := bstep (se 2 (by rfl) ⟨4080030, by rfl⟩ : syracuseStep 10880081 = 8160061) B8160061
theorem B7253387 : Blo 2147435 7253387 := bstep (se 1 (by rfl) ⟨5440040, by rfl⟩ : syracuseStep 7253387 = 10880081) B10880081
theorem B4835591 : Blo 2147435 4835591 := bstep (se 1 (by rfl) ⟨3626693, by rfl⟩ : syracuseStep 4835591 = 7253387) B7253387
theorem B3223727 : Blo 2147435 3223727 := bstep (se 1 (by rfl) ⟨2417795, by rfl⟩ : syracuseStep 3223727 = 4835591) B4835591
theorem B2149151 : Blo 2147435 2149151 := bstep (se 1 (by rfl) ⟨1611863, by rfl⟩ : syracuseStep 2149151 = 3223727) B3223727
theorem B3223733 : Blo 2147435 3223733 := bbase (se 5 (by rfl) ⟨151112, by rfl⟩ : syracuseStep 3223733 = 302225) (by norm_num)
theorem B2149155 : Blo 2147435 2149155 := bstep (se 1 (by rfl) ⟨1611866, by rfl⟩ : syracuseStep 2149155 = 3223733) B3223733
theorem B5440061 : Blo 2147435 5440061 := bbase (se 3 (by rfl) ⟨1020011, by rfl⟩ : syracuseStep 5440061 = 2040023) (by norm_num)
theorem B3626707 : Blo 2147435 3626707 := bstep (se 1 (by rfl) ⟨2720030, by rfl⟩ : syracuseStep 3626707 = 5440061) B5440061
theorem B4835609 : Blo 2147435 4835609 := bstep (se 2 (by rfl) ⟨1813353, by rfl⟩ : syracuseStep 4835609 = 3626707) B3626707
theorem B3223739 : Blo 2147435 3223739 := bstep (se 1 (by rfl) ⟨2417804, by rfl⟩ : syracuseStep 3223739 = 4835609) B4835609
theorem B2149159 : Blo 2147435 2149159 := bstep (se 1 (by rfl) ⟨1611869, by rfl⟩ : syracuseStep 2149159 = 3223739) B3223739
theorem B2417809 : Blo 2147435 2417809 := bbase (se 2 (by rfl) ⟨906678, by rfl⟩ : syracuseStep 2417809 = 1813357) (by norm_num)
theorem B3223745 : Blo 2147435 3223745 := bstep (se 2 (by rfl) ⟨1208904, by rfl⟩ : syracuseStep 3223745 = 2417809) B2417809
theorem B2149163 : Blo 2147435 2149163 := bstep (se 1 (by rfl) ⟨1611872, by rfl⟩ : syracuseStep 2149163 = 3223745) B3223745
theorem B4080061 : Blo 2147435 4080061 := bbase (se 3 (by rfl) ⟨765011, by rfl⟩ : syracuseStep 4080061 = 1530023) (by norm_num)
theorem B5440081 : Blo 2147435 5440081 := bstep (se 2 (by rfl) ⟨2040030, by rfl⟩ : syracuseStep 5440081 = 4080061) B4080061
theorem B7253441 : Blo 2147435 7253441 := bstep (se 2 (by rfl) ⟨2720040, by rfl⟩ : syracuseStep 7253441 = 5440081) B5440081
theorem B4835627 : Blo 2147435 4835627 := bstep (se 1 (by rfl) ⟨3626720, by rfl⟩ : syracuseStep 4835627 = 7253441) B7253441
theorem B3223751 : Blo 2147435 3223751 := bstep (se 1 (by rfl) ⟨2417813, by rfl⟩ : syracuseStep 3223751 = 4835627) B4835627
theorem B2149167 : Blo 2147435 2149167 := bstep (se 1 (by rfl) ⟨1611875, by rfl⟩ : syracuseStep 2149167 = 3223751) B3223751
theorem B3223757 : Blo 2147435 3223757 := bbase (se 3 (by rfl) ⟨604454, by rfl⟩ : syracuseStep 3223757 = 1208909) (by norm_num)
theorem B2149171 : Blo 2147435 2149171 := bstep (se 1 (by rfl) ⟨1611878, by rfl⟩ : syracuseStep 2149171 = 3223757) B3223757
theorem B4835645 : Blo 2147435 4835645 := bbase (se 3 (by rfl) ⟨906683, by rfl⟩ : syracuseStep 4835645 = 1813367) (by norm_num)
theorem B3223763 : Blo 2147435 3223763 := bstep (se 1 (by rfl) ⟨2417822, by rfl⟩ : syracuseStep 3223763 = 4835645) B4835645
theorem B2149175 : Blo 2147435 2149175 := bstep (se 1 (by rfl) ⟨1611881, by rfl⟩ : syracuseStep 2149175 = 3223763) B3223763
theorem B3626741 : Blo 2147435 3626741 := bbase (se 5 (by rfl) ⟨170003, by rfl⟩ : syracuseStep 3626741 = 340007) (by norm_num)
theorem B2417827 : Blo 2147435 2417827 := bstep (se 1 (by rfl) ⟨1813370, by rfl⟩ : syracuseStep 2417827 = 3626741) B3626741
theorem B3223769 : Blo 2147435 3223769 := bstep (se 2 (by rfl) ⟨1208913, by rfl⟩ : syracuseStep 3223769 = 2417827) B2417827
theorem B2149179 : Blo 2147435 2149179 := bstep (se 1 (by rfl) ⟨1611884, by rfl⟩ : syracuseStep 2149179 = 3223769) B3223769
theorem B10327733 : Blo 2147435 10327733 := bbase (se 5 (by rfl) ⟨484112, by rfl⟩ : syracuseStep 10327733 = 968225) (by norm_num)
theorem B6885155 : Blo 2147435 6885155 := bstep (se 1 (by rfl) ⟨5163866, by rfl⟩ : syracuseStep 6885155 = 10327733) B10327733
theorem B4590103 : Blo 2147435 4590103 := bstep (se 1 (by rfl) ⟨3442577, by rfl⟩ : syracuseStep 4590103 = 6885155) B6885155
theorem B6120137 : Blo 2147435 6120137 := bstep (se 2 (by rfl) ⟨2295051, by rfl⟩ : syracuseStep 6120137 = 4590103) B4590103
theorem B16320365 : Blo 2147435 16320365 := bstep (se 3 (by rfl) ⟨3060068, by rfl⟩ : syracuseStep 16320365 = 6120137) B6120137
theorem B10880243 : Blo 2147435 10880243 := bstep (se 1 (by rfl) ⟨8160182, by rfl⟩ : syracuseStep 10880243 = 16320365) B16320365
theorem B7253495 : Blo 2147435 7253495 := bstep (se 1 (by rfl) ⟨5440121, by rfl⟩ : syracuseStep 7253495 = 10880243) B10880243
theorem B4835663 : Blo 2147435 4835663 := bstep (se 1 (by rfl) ⟨3626747, by rfl⟩ : syracuseStep 4835663 = 7253495) B7253495
theorem B3223775 : Blo 2147435 3223775 := bstep (se 1 (by rfl) ⟨2417831, by rfl⟩ : syracuseStep 3223775 = 4835663) B4835663
theorem B2149183 : Blo 2147435 2149183 := bstep (se 1 (by rfl) ⟨1611887, by rfl⟩ : syracuseStep 2149183 = 3223775) B3223775
theorem B3223781 : Blo 2147435 3223781 := bbase (se 4 (by rfl) ⟨302229, by rfl⟩ : syracuseStep 3223781 = 604459) (by norm_num)
theorem B2149187 : Blo 2147435 2149187 := bstep (se 1 (by rfl) ⟨1611890, by rfl⟩ : syracuseStep 2149187 = 3223781) B3223781
theorem B11179205 : Blo 2147435 11179205 := bbase (se 4 (by rfl) ⟨1048050, by rfl⟩ : syracuseStep 11179205 = 2096101) (by norm_num)
theorem B7452803 : Blo 2147435 7452803 := bstep (se 1 (by rfl) ⟨5589602, by rfl⟩ : syracuseStep 7452803 = 11179205) B11179205
theorem B19874141 : Blo 2147435 19874141 := bstep (se 3 (by rfl) ⟨3726401, by rfl⟩ : syracuseStep 19874141 = 7452803) B7452803
theorem B13249427 : Blo 2147435 13249427 := bstep (se 1 (by rfl) ⟨9937070, by rfl⟩ : syracuseStep 13249427 = 19874141) B19874141
theorem B35331805 : Blo 2147435 35331805 := bstep (se 3 (by rfl) ⟨6624713, by rfl⟩ : syracuseStep 35331805 = 13249427) B13249427
theorem B47109073 : Blo 2147435 47109073 := bstep (se 2 (by rfl) ⟨17665902, by rfl⟩ : syracuseStep 47109073 = 35331805) B35331805
theorem B62812097 : Blo 2147435 62812097 := bstep (se 2 (by rfl) ⟨23554536, by rfl⟩ : syracuseStep 62812097 = 47109073) B47109073
theorem B41874731 : Blo 2147435 41874731 := bstep (se 1 (by rfl) ⟨31406048, by rfl⟩ : syracuseStep 41874731 = 62812097) B62812097
theorem B27916487 : Blo 2147435 27916487 := bstep (se 1 (by rfl) ⟨20937365, by rfl⟩ : syracuseStep 27916487 = 41874731) B41874731
theorem B18610991 : Blo 2147435 18610991 := bstep (se 1 (by rfl) ⟨13958243, by rfl⟩ : syracuseStep 18610991 = 27916487) B27916487
theorem B12407327 : Blo 2147435 12407327 := bstep (se 1 (by rfl) ⟨9305495, by rfl⟩ : syracuseStep 12407327 = 18610991) B18610991
theorem B8271551 : Blo 2147435 8271551 := bstep (se 1 (by rfl) ⟨6203663, by rfl⟩ : syracuseStep 8271551 = 12407327) B12407327
theorem B5514367 : Blo 2147435 5514367 := bstep (se 1 (by rfl) ⟨4135775, by rfl⟩ : syracuseStep 5514367 = 8271551) B8271551
theorem B7352489 : Blo 2147435 7352489 := bstep (se 2 (by rfl) ⟨2757183, by rfl⟩ : syracuseStep 7352489 = 5514367) B5514367
theorem B19606637 : Blo 2147435 19606637 := bstep (se 3 (by rfl) ⟨3676244, by rfl⟩ : syracuseStep 19606637 = 7352489) B7352489
theorem B13071091 : Blo 2147435 13071091 := bstep (se 1 (by rfl) ⟨9803318, by rfl⟩ : syracuseStep 13071091 = 19606637) B19606637
theorem B17428121 : Blo 2147435 17428121 := bstep (se 2 (by rfl) ⟨6535545, by rfl⟩ : syracuseStep 17428121 = 13071091) B13071091
theorem B11618747 : Blo 2147435 11618747 := bstep (se 1 (by rfl) ⟨8714060, by rfl⟩ : syracuseStep 11618747 = 17428121) B17428121
theorem B7745831 : Blo 2147435 7745831 := bstep (se 1 (by rfl) ⟨5809373, by rfl⟩ : syracuseStep 7745831 = 11618747) B11618747
theorem B5163887 : Blo 2147435 5163887 := bstep (se 1 (by rfl) ⟨3872915, by rfl⟩ : syracuseStep 5163887 = 7745831) B7745831
theorem B3442591 : Blo 2147435 3442591 := bstep (se 1 (by rfl) ⟨2581943, by rfl⟩ : syracuseStep 3442591 = 5163887) B5163887
theorem B4590121 : Blo 2147435 4590121 := bstep (se 2 (by rfl) ⟨1721295, by rfl⟩ : syracuseStep 4590121 = 3442591) B3442591
theorem B6120161 : Blo 2147435 6120161 := bstep (se 2 (by rfl) ⟨2295060, by rfl⟩ : syracuseStep 6120161 = 4590121) B4590121
theorem B4080107 : Blo 2147435 4080107 := bstep (se 1 (by rfl) ⟨3060080, by rfl⟩ : syracuseStep 4080107 = 6120161) B6120161
theorem B2720071 : Blo 2147435 2720071 := bstep (se 1 (by rfl) ⟨2040053, by rfl⟩ : syracuseStep 2720071 = 4080107) B4080107
theorem B3626761 : Blo 2147435 3626761 := bstep (se 2 (by rfl) ⟨1360035, by rfl⟩ : syracuseStep 3626761 = 2720071) B2720071
theorem B4835681 : Blo 2147435 4835681 := bstep (se 2 (by rfl) ⟨1813380, by rfl⟩ : syracuseStep 4835681 = 3626761) B3626761
theorem B3223787 : Blo 2147435 3223787 := bstep (se 1 (by rfl) ⟨2417840, by rfl⟩ : syracuseStep 3223787 = 4835681) B4835681
theorem B2149191 : Blo 2147435 2149191 := bstep (se 1 (by rfl) ⟨1611893, by rfl⟩ : syracuseStep 2149191 = 3223787) B3223787
theorem B2417845 : Blo 2147435 2417845 := bbase (se 5 (by rfl) ⟨113336, by rfl⟩ : syracuseStep 2417845 = 226673) (by norm_num)
theorem B3223793 : Blo 2147435 3223793 := bstep (se 2 (by rfl) ⟨1208922, by rfl⟩ : syracuseStep 3223793 = 2417845) B2417845
theorem B2149195 : Blo 2147435 2149195 := bstep (se 1 (by rfl) ⟨1611896, by rfl⟩ : syracuseStep 2149195 = 3223793) B3223793
theorem B2720081 : Blo 2147435 2720081 := bbase (se 2 (by rfl) ⟨1020030, by rfl⟩ : syracuseStep 2720081 = 2040061) (by norm_num)
theorem B7253549 : Blo 2147435 7253549 := bstep (se 3 (by rfl) ⟨1360040, by rfl⟩ : syracuseStep 7253549 = 2720081) B2720081
theorem B4835699 : Blo 2147435 4835699 := bstep (se 1 (by rfl) ⟨3626774, by rfl⟩ : syracuseStep 4835699 = 7253549) B7253549
theorem B3223799 : Blo 2147435 3223799 := bstep (se 1 (by rfl) ⟨2417849, by rfl⟩ : syracuseStep 3223799 = 4835699) B4835699
theorem B2149199 : Blo 2147435 2149199 := bstep (se 1 (by rfl) ⟨1611899, by rfl⟩ : syracuseStep 2149199 = 3223799) B3223799
theorem B3223805 : Blo 2147435 3223805 := bbase (se 3 (by rfl) ⟨604463, by rfl⟩ : syracuseStep 3223805 = 1208927) (by norm_num)
theorem B2149203 : Blo 2147435 2149203 := bstep (se 1 (by rfl) ⟨1611902, by rfl⟩ : syracuseStep 2149203 = 3223805) B3223805
theorem B4835717 : Blo 2147435 4835717 := bbase (se 4 (by rfl) ⟨453348, by rfl⟩ : syracuseStep 4835717 = 906697) (by norm_num)
theorem B3223811 : Blo 2147435 3223811 := bstep (se 1 (by rfl) ⟨2417858, by rfl⟩ : syracuseStep 3223811 = 4835717) B4835717
theorem B2149207 : Blo 2147435 2149207 := bstep (se 1 (by rfl) ⟨1611905, by rfl⟩ : syracuseStep 2149207 = 3223811) B3223811
theorem B3060109 : Blo 2147435 3060109 := bbase (se 3 (by rfl) ⟨573770, by rfl⟩ : syracuseStep 3060109 = 1147541) (by norm_num)
theorem B4080145 : Blo 2147435 4080145 := bstep (se 2 (by rfl) ⟨1530054, by rfl⟩ : syracuseStep 4080145 = 3060109) B3060109
theorem B5440193 : Blo 2147435 5440193 := bstep (se 2 (by rfl) ⟨2040072, by rfl⟩ : syracuseStep 5440193 = 4080145) B4080145
theorem B3626795 : Blo 2147435 3626795 := bstep (se 1 (by rfl) ⟨2720096, by rfl⟩ : syracuseStep 3626795 = 5440193) B5440193
theorem B2417863 : Blo 2147435 2417863 := bstep (se 1 (by rfl) ⟨1813397, by rfl⟩ : syracuseStep 2417863 = 3626795) B3626795
theorem B3223817 : Blo 2147435 3223817 := bstep (se 2 (by rfl) ⟨1208931, by rfl⟩ : syracuseStep 3223817 = 2417863) B2417863
theorem B2149211 : Blo 2147435 2149211 := bstep (se 1 (by rfl) ⟨1611908, by rfl⟩ : syracuseStep 2149211 = 3223817) B3223817
theorem B10880405 : Blo 2147435 10880405 := bbase (se 6 (by rfl) ⟨255009, by rfl⟩ : syracuseStep 10880405 = 510019) (by norm_num)
theorem B7253603 : Blo 2147435 7253603 := bstep (se 1 (by rfl) ⟨5440202, by rfl⟩ : syracuseStep 7253603 = 10880405) B10880405
theorem B4835735 : Blo 2147435 4835735 := bstep (se 1 (by rfl) ⟨3626801, by rfl⟩ : syracuseStep 4835735 = 7253603) B7253603
theorem B3223823 : Blo 2147435 3223823 := bstep (se 1 (by rfl) ⟨2417867, by rfl⟩ : syracuseStep 3223823 = 4835735) B4835735
theorem B2149215 : Blo 2147435 2149215 := bstep (se 1 (by rfl) ⟨1611911, by rfl⟩ : syracuseStep 2149215 = 3223823) B3223823
theorem B3223829 : Blo 2147435 3223829 := bbase (se 6 (by rfl) ⟨75558, by rfl⟩ : syracuseStep 3223829 = 151117) (by norm_num)
theorem B2149219 : Blo 2147435 2149219 := bstep (se 1 (by rfl) ⟨1611914, by rfl⟩ : syracuseStep 2149219 = 3223829) B3223829
theorem B10327925 : Blo 2147435 10327925 := bbase (se 5 (by rfl) ⟨484121, by rfl⟩ : syracuseStep 10327925 = 968243) (by norm_num)
theorem B27541133 : Blo 2147435 27541133 := bstep (se 3 (by rfl) ⟨5163962, by rfl⟩ : syracuseStep 27541133 = 10327925) B10327925
theorem B18360755 : Blo 2147435 18360755 := bstep (se 1 (by rfl) ⟨13770566, by rfl⟩ : syracuseStep 18360755 = 27541133) B27541133
theorem B12240503 : Blo 2147435 12240503 := bstep (se 1 (by rfl) ⟨9180377, by rfl⟩ : syracuseStep 12240503 = 18360755) B18360755
theorem B8160335 : Blo 2147435 8160335 := bstep (se 1 (by rfl) ⟨6120251, by rfl⟩ : syracuseStep 8160335 = 12240503) B12240503
theorem B5440223 : Blo 2147435 5440223 := bstep (se 1 (by rfl) ⟨4080167, by rfl⟩ : syracuseStep 5440223 = 8160335) B8160335
theorem B3626815 : Blo 2147435 3626815 := bstep (se 1 (by rfl) ⟨2720111, by rfl⟩ : syracuseStep 3626815 = 5440223) B5440223
theorem B4835753 : Blo 2147435 4835753 := bstep (se 2 (by rfl) ⟨1813407, by rfl⟩ : syracuseStep 4835753 = 3626815) B3626815
theorem B3223835 : Blo 2147435 3223835 := bstep (se 1 (by rfl) ⟨2417876, by rfl⟩ : syracuseStep 3223835 = 4835753) B4835753
theorem B2149223 : Blo 2147435 2149223 := bstep (se 1 (by rfl) ⟨1611917, by rfl⟩ : syracuseStep 2149223 = 3223835) B3223835
theorem B2417881 : Blo 2147435 2417881 := bbase (se 2 (by rfl) ⟨906705, by rfl⟩ : syracuseStep 2417881 = 1813411) (by norm_num)
theorem B3223841 : Blo 2147435 3223841 := bstep (se 2 (by rfl) ⟨1208940, by rfl⟩ : syracuseStep 3223841 = 2417881) B2417881
theorem B2149227 : Blo 2147435 2149227 := bstep (se 1 (by rfl) ⟨1611920, by rfl⟩ : syracuseStep 2149227 = 3223841) B3223841
theorem B4135853 : Blo 2147435 4135853 := bbase (se 3 (by rfl) ⟨775472, by rfl⟩ : syracuseStep 4135853 = 1550945) (by norm_num)
theorem B2757235 : Blo 2147435 2757235 := bstep (se 1 (by rfl) ⟨2067926, by rfl⟩ : syracuseStep 2757235 = 4135853) B4135853
theorem B3676313 : Blo 2147435 3676313 := bstep (se 2 (by rfl) ⟨1378617, by rfl⟩ : syracuseStep 3676313 = 2757235) B2757235
theorem B9803501 : Blo 2147435 9803501 := bstep (se 3 (by rfl) ⟨1838156, by rfl⟩ : syracuseStep 9803501 = 3676313) B3676313
theorem B6535667 : Blo 2147435 6535667 := bstep (se 1 (by rfl) ⟨4901750, by rfl⟩ : syracuseStep 6535667 = 9803501) B9803501
theorem B17428445 : Blo 2147435 17428445 := bstep (se 3 (by rfl) ⟨3267833, by rfl⟩ : syracuseStep 17428445 = 6535667) B6535667
theorem B11618963 : Blo 2147435 11618963 := bstep (se 1 (by rfl) ⟨8714222, by rfl⟩ : syracuseStep 11618963 = 17428445) B17428445
theorem B7745975 : Blo 2147435 7745975 := bstep (se 1 (by rfl) ⟨5809481, by rfl⟩ : syracuseStep 7745975 = 11618963) B11618963
theorem B5163983 : Blo 2147435 5163983 := bstep (se 1 (by rfl) ⟨3872987, by rfl⟩ : syracuseStep 5163983 = 7745975) B7745975
theorem B3442655 : Blo 2147435 3442655 := bstep (se 1 (by rfl) ⟨2581991, by rfl⟩ : syracuseStep 3442655 = 5163983) B5163983
theorem B2295103 : Blo 2147435 2295103 := bstep (se 1 (by rfl) ⟨1721327, by rfl⟩ : syracuseStep 2295103 = 3442655) B3442655
theorem B3060137 : Blo 2147435 3060137 := bstep (se 2 (by rfl) ⟨1147551, by rfl⟩ : syracuseStep 3060137 = 2295103) B2295103
theorem B8160365 : Blo 2147435 8160365 := bstep (se 3 (by rfl) ⟨1530068, by rfl⟩ : syracuseStep 8160365 = 3060137) B3060137
theorem B5440243 : Blo 2147435 5440243 := bstep (se 1 (by rfl) ⟨4080182, by rfl⟩ : syracuseStep 5440243 = 8160365) B8160365
theorem B7253657 : Blo 2147435 7253657 := bstep (se 2 (by rfl) ⟨2720121, by rfl⟩ : syracuseStep 7253657 = 5440243) B5440243
theorem B4835771 : Blo 2147435 4835771 := bstep (se 1 (by rfl) ⟨3626828, by rfl⟩ : syracuseStep 4835771 = 7253657) B7253657
theorem B3223847 : Blo 2147435 3223847 := bstep (se 1 (by rfl) ⟨2417885, by rfl⟩ : syracuseStep 3223847 = 4835771) B4835771
theorem B2149231 : Blo 2147435 2149231 := bstep (se 1 (by rfl) ⟨1611923, by rfl⟩ : syracuseStep 2149231 = 3223847) B3223847
theorem B3223853 : Blo 2147435 3223853 := bbase (se 3 (by rfl) ⟨604472, by rfl⟩ : syracuseStep 3223853 = 1208945) (by norm_num)
theorem B2149235 : Blo 2147435 2149235 := bstep (se 1 (by rfl) ⟨1611926, by rfl⟩ : syracuseStep 2149235 = 3223853) B3223853
theorem B4835789 : Blo 2147435 4835789 := bbase (se 3 (by rfl) ⟨906710, by rfl⟩ : syracuseStep 4835789 = 1813421) (by norm_num)
theorem B3223859 : Blo 2147435 3223859 := bstep (se 1 (by rfl) ⟨2417894, by rfl⟩ : syracuseStep 3223859 = 4835789) B4835789
theorem B2149239 : Blo 2147435 2149239 := bstep (se 1 (by rfl) ⟨1611929, by rfl⟩ : syracuseStep 2149239 = 3223859) B3223859
theorem B2720137 : Blo 2147435 2720137 := bbase (se 2 (by rfl) ⟨1020051, by rfl⟩ : syracuseStep 2720137 = 2040103) (by norm_num)
theorem B3626849 : Blo 2147435 3626849 := bstep (se 2 (by rfl) ⟨1360068, by rfl⟩ : syracuseStep 3626849 = 2720137) B2720137
theorem B2417899 : Blo 2147435 2417899 := bstep (se 1 (by rfl) ⟨1813424, by rfl⟩ : syracuseStep 2417899 = 3626849) B3626849
theorem B3223865 : Blo 2147435 3223865 := bstep (se 2 (by rfl) ⟨1208949, by rfl⟩ : syracuseStep 3223865 = 2417899) B2417899
theorem B2149243 : Blo 2147435 2149243 := bstep (se 1 (by rfl) ⟨1611932, by rfl⟩ : syracuseStep 2149243 = 3223865) B3223865
theorem B7352677 : Blo 2147435 7352677 := bbase (se 4 (by rfl) ⟨689313, by rfl⟩ : syracuseStep 7352677 = 1378627) (by norm_num)
theorem B39214277 : Blo 2147435 39214277 := bstep (se 4 (by rfl) ⟨3676338, by rfl⟩ : syracuseStep 39214277 = 7352677) B7352677
theorem B26142851 : Blo 2147435 26142851 := bstep (se 1 (by rfl) ⟨19607138, by rfl⟩ : syracuseStep 26142851 = 39214277) B39214277
theorem B69714269 : Blo 2147435 69714269 := bstep (se 3 (by rfl) ⟨13071425, by rfl⟩ : syracuseStep 69714269 = 26142851) B26142851
theorem B46476179 : Blo 2147435 46476179 := bstep (se 1 (by rfl) ⟨34857134, by rfl⟩ : syracuseStep 46476179 = 69714269) B69714269
theorem B30984119 : Blo 2147435 30984119 := bstep (se 1 (by rfl) ⟨23238089, by rfl⟩ : syracuseStep 30984119 = 46476179) B46476179
theorem B20656079 : Blo 2147435 20656079 := bstep (se 1 (by rfl) ⟨15492059, by rfl⟩ : syracuseStep 20656079 = 30984119) B30984119
theorem B13770719 : Blo 2147435 13770719 := bstep (se 1 (by rfl) ⟨10328039, by rfl⟩ : syracuseStep 13770719 = 20656079) B20656079
theorem B9180479 : Blo 2147435 9180479 := bstep (se 1 (by rfl) ⟨6885359, by rfl⟩ : syracuseStep 9180479 = 13770719) B13770719
theorem B24481277 : Blo 2147435 24481277 := bstep (se 3 (by rfl) ⟨4590239, by rfl⟩ : syracuseStep 24481277 = 9180479) B9180479
theorem B16320851 : Blo 2147435 16320851 := bstep (se 1 (by rfl) ⟨12240638, by rfl⟩ : syracuseStep 16320851 = 24481277) B24481277
theorem B10880567 : Blo 2147435 10880567 := bstep (se 1 (by rfl) ⟨8160425, by rfl⟩ : syracuseStep 10880567 = 16320851) B16320851
theorem B7253711 : Blo 2147435 7253711 := bstep (se 1 (by rfl) ⟨5440283, by rfl⟩ : syracuseStep 7253711 = 10880567) B10880567
theorem B4835807 : Blo 2147435 4835807 := bstep (se 1 (by rfl) ⟨3626855, by rfl⟩ : syracuseStep 4835807 = 7253711) B7253711
theorem B3223871 : Blo 2147435 3223871 := bstep (se 1 (by rfl) ⟨2417903, by rfl⟩ : syracuseStep 3223871 = 4835807) B4835807
theorem B2149247 : Blo 2147435 2149247 := bstep (se 1 (by rfl) ⟨1611935, by rfl⟩ : syracuseStep 2149247 = 3223871) B3223871
theorem B3223877 : Blo 2147435 3223877 := bbase (se 4 (by rfl) ⟨302238, by rfl⟩ : syracuseStep 3223877 = 604477) (by norm_num)
theorem B2149251 : Blo 2147435 2149251 := bstep (se 1 (by rfl) ⟨1611938, by rfl⟩ : syracuseStep 2149251 = 3223877) B3223877
theorem B3626869 : Blo 2147435 3626869 := bbase (se 5 (by rfl) ⟨170009, by rfl⟩ : syracuseStep 3626869 = 340019) (by norm_num)
theorem B4835825 : Blo 2147435 4835825 := bstep (se 2 (by rfl) ⟨1813434, by rfl⟩ : syracuseStep 4835825 = 3626869) B3626869
theorem B3223883 : Blo 2147435 3223883 := bstep (se 1 (by rfl) ⟨2417912, by rfl⟩ : syracuseStep 3223883 = 4835825) B4835825
theorem B2149255 : Blo 2147435 2149255 := bstep (se 1 (by rfl) ⟨1611941, by rfl⟩ : syracuseStep 2149255 = 3223883) B3223883
theorem B2417917 : Blo 2147435 2417917 := bbase (se 3 (by rfl) ⟨453359, by rfl⟩ : syracuseStep 2417917 = 906719) (by norm_num)
theorem B3223889 : Blo 2147435 3223889 := bstep (se 2 (by rfl) ⟨1208958, by rfl⟩ : syracuseStep 3223889 = 2417917) B2417917
theorem B2149259 : Blo 2147435 2149259 := bstep (se 1 (by rfl) ⟨1611944, by rfl⟩ : syracuseStep 2149259 = 3223889) B3223889
theorem B7253765 : Blo 2147435 7253765 := bbase (se 4 (by rfl) ⟨680040, by rfl⟩ : syracuseStep 7253765 = 1360081) (by norm_num)
theorem B4835843 : Blo 2147435 4835843 := bstep (se 1 (by rfl) ⟨3626882, by rfl⟩ : syracuseStep 4835843 = 7253765) B7253765
theorem B3223895 : Blo 2147435 3223895 := bstep (se 1 (by rfl) ⟨2417921, by rfl⟩ : syracuseStep 3223895 = 4835843) B4835843
theorem B2149263 : Blo 2147435 2149263 := bstep (se 1 (by rfl) ⟨1611947, by rfl⟩ : syracuseStep 2149263 = 3223895) B3223895
theorem B3223901 : Blo 2147435 3223901 := bbase (se 3 (by rfl) ⟨604481, by rfl⟩ : syracuseStep 3223901 = 1208963) (by norm_num)
theorem B2149267 : Blo 2147435 2149267 := bstep (se 1 (by rfl) ⟨1611950, by rfl⟩ : syracuseStep 2149267 = 3223901) B3223901
theorem B4835861 : Blo 2147435 4835861 := bbase (se 6 (by rfl) ⟨113340, by rfl⟩ : syracuseStep 4835861 = 226681) (by norm_num)
theorem B3223907 : Blo 2147435 3223907 := bstep (se 1 (by rfl) ⟨2417930, by rfl⟩ : syracuseStep 3223907 = 4835861) B4835861
theorem B2149271 : Blo 2147435 2149271 := bstep (se 1 (by rfl) ⟨1611953, by rfl⟩ : syracuseStep 2149271 = 3223907) B3223907
theorem B8160533 : Blo 2147435 8160533 := bbase (se 6 (by rfl) ⟨191262, by rfl⟩ : syracuseStep 8160533 = 382525) (by norm_num)
theorem B5440355 : Blo 2147435 5440355 := bstep (se 1 (by rfl) ⟨4080266, by rfl⟩ : syracuseStep 5440355 = 8160533) B8160533
theorem B3626903 : Blo 2147435 3626903 := bstep (se 1 (by rfl) ⟨2720177, by rfl⟩ : syracuseStep 3626903 = 5440355) B5440355
theorem B2417935 : Blo 2147435 2417935 := bstep (se 1 (by rfl) ⟨1813451, by rfl⟩ : syracuseStep 2417935 = 3626903) B3626903
theorem B3223913 : Blo 2147435 3223913 := bstep (se 2 (by rfl) ⟨1208967, by rfl⟩ : syracuseStep 3223913 = 2417935) B2417935
theorem B2149275 : Blo 2147435 2149275 := bstep (se 1 (by rfl) ⟨1611956, by rfl⟩ : syracuseStep 2149275 = 3223913) B3223913
theorem B12240821 : Blo 2147435 12240821 := bbase (se 5 (by rfl) ⟨573788, by rfl⟩ : syracuseStep 12240821 = 1147577) (by norm_num)
theorem B8160547 : Blo 2147435 8160547 := bstep (se 1 (by rfl) ⟨6120410, by rfl⟩ : syracuseStep 8160547 = 12240821) B12240821
theorem B10880729 : Blo 2147435 10880729 := bstep (se 2 (by rfl) ⟨4080273, by rfl⟩ : syracuseStep 10880729 = 8160547) B8160547
theorem B7253819 : Blo 2147435 7253819 := bstep (se 1 (by rfl) ⟨5440364, by rfl⟩ : syracuseStep 7253819 = 10880729) B10880729
theorem B4835879 : Blo 2147435 4835879 := bstep (se 1 (by rfl) ⟨3626909, by rfl⟩ : syracuseStep 4835879 = 7253819) B7253819
theorem B3223919 : Blo 2147435 3223919 := bstep (se 1 (by rfl) ⟨2417939, by rfl⟩ : syracuseStep 3223919 = 4835879) B4835879
theorem B2149279 : Blo 2147435 2149279 := bstep (se 1 (by rfl) ⟨1611959, by rfl⟩ : syracuseStep 2149279 = 3223919) B3223919
theorem B3223925 : Blo 2147435 3223925 := bbase (se 5 (by rfl) ⟨151121, by rfl⟩ : syracuseStep 3223925 = 302243) (by norm_num)
theorem B2149283 : Blo 2147435 2149283 := bstep (se 1 (by rfl) ⟨1611962, by rfl⟩ : syracuseStep 2149283 = 3223925) B3223925
theorem B2178613 : Blo 2147435 2178613 := bbase (se 5 (by rfl) ⟨102122, by rfl⟩ : syracuseStep 2178613 = 204245) (by norm_num)
theorem B2904817 : Blo 2147435 2904817 := bstep (se 2 (by rfl) ⟨1089306, by rfl⟩ : syracuseStep 2904817 = 2178613) B2178613
theorem B3873089 : Blo 2147435 3873089 := bstep (se 2 (by rfl) ⟨1452408, by rfl⟩ : syracuseStep 3873089 = 2904817) B2904817
theorem B2582059 : Blo 2147435 2582059 := bstep (se 1 (by rfl) ⟨1936544, by rfl⟩ : syracuseStep 2582059 = 3873089) B3873089
theorem B3442745 : Blo 2147435 3442745 := bstep (se 2 (by rfl) ⟨1291029, by rfl⟩ : syracuseStep 3442745 = 2582059) B2582059
theorem B2295163 : Blo 2147435 2295163 := bstep (se 1 (by rfl) ⟨1721372, by rfl⟩ : syracuseStep 2295163 = 3442745) B3442745
theorem B3060217 : Blo 2147435 3060217 := bstep (se 2 (by rfl) ⟨1147581, by rfl⟩ : syracuseStep 3060217 = 2295163) B2295163
theorem B4080289 : Blo 2147435 4080289 := bstep (se 2 (by rfl) ⟨1530108, by rfl⟩ : syracuseStep 4080289 = 3060217) B3060217
theorem B5440385 : Blo 2147435 5440385 := bstep (se 2 (by rfl) ⟨2040144, by rfl⟩ : syracuseStep 5440385 = 4080289) B4080289
theorem B3626923 : Blo 2147435 3626923 := bstep (se 1 (by rfl) ⟨2720192, by rfl⟩ : syracuseStep 3626923 = 5440385) B5440385
theorem B4835897 : Blo 2147435 4835897 := bstep (se 2 (by rfl) ⟨1813461, by rfl⟩ : syracuseStep 4835897 = 3626923) B3626923
theorem B3223931 : Blo 2147435 3223931 := bstep (se 1 (by rfl) ⟨2417948, by rfl⟩ : syracuseStep 3223931 = 4835897) B4835897
theorem B2149287 : Blo 2147435 2149287 := bstep (se 1 (by rfl) ⟨1611965, by rfl⟩ : syracuseStep 2149287 = 3223931) B3223931
theorem B2417953 : Blo 2147435 2417953 := bbase (se 2 (by rfl) ⟨906732, by rfl⟩ : syracuseStep 2417953 = 1813465) (by norm_num)
theorem B3223937 : Blo 2147435 3223937 := bstep (se 2 (by rfl) ⟨1208976, by rfl⟩ : syracuseStep 3223937 = 2417953) B2417953
theorem B2149291 : Blo 2147435 2149291 := bstep (se 1 (by rfl) ⟨1611968, by rfl⟩ : syracuseStep 2149291 = 3223937) B3223937
theorem B5440405 : Blo 2147435 5440405 := bbase (se 6 (by rfl) ⟨127509, by rfl⟩ : syracuseStep 5440405 = 255019) (by norm_num)
theorem B7253873 : Blo 2147435 7253873 := bstep (se 2 (by rfl) ⟨2720202, by rfl⟩ : syracuseStep 7253873 = 5440405) B5440405
theorem B4835915 : Blo 2147435 4835915 := bstep (se 1 (by rfl) ⟨3626936, by rfl⟩ : syracuseStep 4835915 = 7253873) B7253873
theorem B3223943 : Blo 2147435 3223943 := bstep (se 1 (by rfl) ⟨2417957, by rfl⟩ : syracuseStep 3223943 = 4835915) B4835915
theorem B2149295 : Blo 2147435 2149295 := bstep (se 1 (by rfl) ⟨1611971, by rfl⟩ : syracuseStep 2149295 = 3223943) B3223943
theorem B3223949 : Blo 2147435 3223949 := bbase (se 3 (by rfl) ⟨604490, by rfl⟩ : syracuseStep 3223949 = 1208981) (by norm_num)
theorem B2149299 : Blo 2147435 2149299 := bstep (se 1 (by rfl) ⟨1611974, by rfl⟩ : syracuseStep 2149299 = 3223949) B3223949
theorem B4835933 : Blo 2147435 4835933 := bbase (se 3 (by rfl) ⟨906737, by rfl⟩ : syracuseStep 4835933 = 1813475) (by norm_num)
theorem B3223955 : Blo 2147435 3223955 := bstep (se 1 (by rfl) ⟨2417966, by rfl⟩ : syracuseStep 3223955 = 4835933) B4835933
theorem B2149303 : Blo 2147435 2149303 := bstep (se 1 (by rfl) ⟨1611977, by rfl⟩ : syracuseStep 2149303 = 3223955) B3223955
theorem B3626957 : Blo 2147435 3626957 := bbase (se 3 (by rfl) ⟨680054, by rfl⟩ : syracuseStep 3626957 = 1360109) (by norm_num)
theorem B2417971 : Blo 2147435 2417971 := bstep (se 1 (by rfl) ⟨1813478, by rfl⟩ : syracuseStep 2417971 = 3626957) B3626957
theorem B3223961 : Blo 2147435 3223961 := bstep (se 2 (by rfl) ⟨1208985, by rfl⟩ : syracuseStep 3223961 = 2417971) B2417971
theorem B2149307 : Blo 2147435 2149307 := bstep (se 1 (by rfl) ⟨1611980, by rfl⟩ : syracuseStep 2149307 = 3223961) B3223961
theorem B4653005 : Blo 2147435 4653005 := bbase (se 3 (by rfl) ⟨872438, by rfl⟩ : syracuseStep 4653005 = 1744877) (by norm_num)
theorem B12408013 : Blo 2147435 12408013 := bstep (se 3 (by rfl) ⟨2326502, by rfl⟩ : syracuseStep 12408013 = 4653005) B4653005
theorem B16544017 : Blo 2147435 16544017 := bstep (se 2 (by rfl) ⟨6204006, by rfl⟩ : syracuseStep 16544017 = 12408013) B12408013
theorem B88234757 : Blo 2147435 88234757 := bstep (se 4 (by rfl) ⟨8272008, by rfl⟩ : syracuseStep 88234757 = 16544017) B16544017
theorem B58823171 : Blo 2147435 58823171 := bstep (se 1 (by rfl) ⟨44117378, by rfl⟩ : syracuseStep 58823171 = 88234757) B88234757
theorem B39215447 : Blo 2147435 39215447 := bstep (se 1 (by rfl) ⟨29411585, by rfl⟩ : syracuseStep 39215447 = 58823171) B58823171
theorem B26143631 : Blo 2147435 26143631 := bstep (se 1 (by rfl) ⟨19607723, by rfl⟩ : syracuseStep 26143631 = 39215447) B39215447
theorem B17429087 : Blo 2147435 17429087 := bstep (se 1 (by rfl) ⟨13071815, by rfl⟩ : syracuseStep 17429087 = 26143631) B26143631
theorem B11619391 : Blo 2147435 11619391 := bstep (se 1 (by rfl) ⟨8714543, by rfl⟩ : syracuseStep 11619391 = 17429087) B17429087
theorem B15492521 : Blo 2147435 15492521 := bstep (se 2 (by rfl) ⟨5809695, by rfl⟩ : syracuseStep 15492521 = 11619391) B11619391
theorem B10328347 : Blo 2147435 10328347 := bstep (se 1 (by rfl) ⟨7746260, by rfl⟩ : syracuseStep 10328347 = 15492521) B15492521
theorem B13771129 : Blo 2147435 13771129 := bstep (se 2 (by rfl) ⟨5164173, by rfl⟩ : syracuseStep 13771129 = 10328347) B10328347
theorem B18361505 : Blo 2147435 18361505 := bstep (se 2 (by rfl) ⟨6885564, by rfl⟩ : syracuseStep 18361505 = 13771129) B13771129
theorem B12241003 : Blo 2147435 12241003 := bstep (se 1 (by rfl) ⟨9180752, by rfl⟩ : syracuseStep 12241003 = 18361505) B18361505
theorem B16321337 : Blo 2147435 16321337 := bstep (se 2 (by rfl) ⟨6120501, by rfl⟩ : syracuseStep 16321337 = 12241003) B12241003
theorem B10880891 : Blo 2147435 10880891 := bstep (se 1 (by rfl) ⟨8160668, by rfl⟩ : syracuseStep 10880891 = 16321337) B16321337
theorem B7253927 : Blo 2147435 7253927 := bstep (se 1 (by rfl) ⟨5440445, by rfl⟩ : syracuseStep 7253927 = 10880891) B10880891
theorem B4835951 : Blo 2147435 4835951 := bstep (se 1 (by rfl) ⟨3626963, by rfl⟩ : syracuseStep 4835951 = 7253927) B7253927
theorem B3223967 : Blo 2147435 3223967 := bstep (se 1 (by rfl) ⟨2417975, by rfl⟩ : syracuseStep 3223967 = 4835951) B4835951
theorem B2149311 : Blo 2147435 2149311 := bstep (se 1 (by rfl) ⟨1611983, by rfl⟩ : syracuseStep 2149311 = 3223967) B3223967
theorem B3223973 : Blo 2147435 3223973 := bbase (se 4 (by rfl) ⟨302247, by rfl⟩ : syracuseStep 3223973 = 604495) (by norm_num)
theorem B2149315 : Blo 2147435 2149315 := bstep (se 1 (by rfl) ⟨1611986, by rfl⟩ : syracuseStep 2149315 = 3223973) B3223973
theorem B2720233 : Blo 2147435 2720233 := bbase (se 2 (by rfl) ⟨1020087, by rfl⟩ : syracuseStep 2720233 = 2040175) (by norm_num)
theorem B3626977 : Blo 2147435 3626977 := bstep (se 2 (by rfl) ⟨1360116, by rfl⟩ : syracuseStep 3626977 = 2720233) B2720233
theorem B4835969 : Blo 2147435 4835969 := bstep (se 2 (by rfl) ⟨1813488, by rfl⟩ : syracuseStep 4835969 = 3626977) B3626977
theorem B3223979 : Blo 2147435 3223979 := bstep (se 1 (by rfl) ⟨2417984, by rfl⟩ : syracuseStep 3223979 = 4835969) B4835969
theorem B2149319 : Blo 2147435 2149319 := bstep (se 1 (by rfl) ⟨1611989, by rfl⟩ : syracuseStep 2149319 = 3223979) B3223979
theorem B2417989 : Blo 2147435 2417989 := bbase (se 4 (by rfl) ⟨226686, by rfl⟩ : syracuseStep 2417989 = 453373) (by norm_num)
theorem B3223985 : Blo 2147435 3223985 := bstep (se 2 (by rfl) ⟨1208994, by rfl⟩ : syracuseStep 3223985 = 2417989) B2417989
theorem B2149323 : Blo 2147435 2149323 := bstep (se 1 (by rfl) ⟨1611992, by rfl⟩ : syracuseStep 2149323 = 3223985) B3223985
theorem B4080365 : Blo 2147435 4080365 := bbase (se 3 (by rfl) ⟨765068, by rfl⟩ : syracuseStep 4080365 = 1530137) (by norm_num)
theorem B2720243 : Blo 2147435 2720243 := bstep (se 1 (by rfl) ⟨2040182, by rfl⟩ : syracuseStep 2720243 = 4080365) B4080365
theorem B7253981 : Blo 2147435 7253981 := bstep (se 3 (by rfl) ⟨1360121, by rfl⟩ : syracuseStep 7253981 = 2720243) B2720243
theorem B4835987 : Blo 2147435 4835987 := bstep (se 1 (by rfl) ⟨3626990, by rfl⟩ : syracuseStep 4835987 = 7253981) B7253981
theorem B3223991 : Blo 2147435 3223991 := bstep (se 1 (by rfl) ⟨2417993, by rfl⟩ : syracuseStep 3223991 = 4835987) B4835987
theorem B2149327 : Blo 2147435 2149327 := bstep (se 1 (by rfl) ⟨1611995, by rfl⟩ : syracuseStep 2149327 = 3223991) B3223991
theorem B3223997 : Blo 2147435 3223997 := bbase (se 3 (by rfl) ⟨604499, by rfl⟩ : syracuseStep 3223997 = 1208999) (by norm_num)
theorem B2149331 : Blo 2147435 2149331 := bstep (se 1 (by rfl) ⟨1611998, by rfl⟩ : syracuseStep 2149331 = 3223997) B3223997
theorem B4836005 : Blo 2147435 4836005 := bbase (se 4 (by rfl) ⟨453375, by rfl⟩ : syracuseStep 4836005 = 906751) (by norm_num)
theorem B3224003 : Blo 2147435 3224003 := bstep (se 1 (by rfl) ⟨2418002, by rfl⟩ : syracuseStep 3224003 = 4836005) B4836005
theorem B2149335 : Blo 2147435 2149335 := bstep (se 1 (by rfl) ⟨1612001, by rfl⟩ : syracuseStep 2149335 = 3224003) B3224003
theorem B5440517 : Blo 2147435 5440517 := bbase (se 4 (by rfl) ⟨510048, by rfl⟩ : syracuseStep 5440517 = 1020097) (by norm_num)
theorem B3627011 : Blo 2147435 3627011 := bstep (se 1 (by rfl) ⟨2720258, by rfl⟩ : syracuseStep 3627011 = 5440517) B5440517
theorem B2418007 : Blo 2147435 2418007 := bstep (se 1 (by rfl) ⟨1813505, by rfl⟩ : syracuseStep 2418007 = 3627011) B3627011
theorem B3224009 : Blo 2147435 3224009 := bstep (se 2 (by rfl) ⟨1209003, by rfl⟩ : syracuseStep 3224009 = 2418007) B2418007
theorem B2149339 : Blo 2147435 2149339 := bstep (se 1 (by rfl) ⟨1612004, by rfl⟩ : syracuseStep 2149339 = 3224009) B3224009
theorem B4590445 : Blo 2147435 4590445 := bbase (se 3 (by rfl) ⟨860708, by rfl⟩ : syracuseStep 4590445 = 1721417) (by norm_num)
theorem B6120593 : Blo 2147435 6120593 := bstep (se 2 (by rfl) ⟨2295222, by rfl⟩ : syracuseStep 6120593 = 4590445) B4590445
theorem B4080395 : Blo 2147435 4080395 := bstep (se 1 (by rfl) ⟨3060296, by rfl⟩ : syracuseStep 4080395 = 6120593) B6120593
theorem B10881053 : Blo 2147435 10881053 := bstep (se 3 (by rfl) ⟨2040197, by rfl⟩ : syracuseStep 10881053 = 4080395) B4080395
theorem B7254035 : Blo 2147435 7254035 := bstep (se 1 (by rfl) ⟨5440526, by rfl⟩ : syracuseStep 7254035 = 10881053) B10881053
theorem B4836023 : Blo 2147435 4836023 := bstep (se 1 (by rfl) ⟨3627017, by rfl⟩ : syracuseStep 4836023 = 7254035) B7254035
theorem B3224015 : Blo 2147435 3224015 := bstep (se 1 (by rfl) ⟨2418011, by rfl⟩ : syracuseStep 3224015 = 4836023) B4836023
theorem B2149343 : Blo 2147435 2149343 := bstep (se 1 (by rfl) ⟨1612007, by rfl⟩ : syracuseStep 2149343 = 3224015) B3224015
theorem B3224021 : Blo 2147435 3224021 := bbase (se 7 (by rfl) ⟨37781, by rfl⟩ : syracuseStep 3224021 = 75563) (by norm_num)
theorem B2149347 : Blo 2147435 2149347 := bstep (se 1 (by rfl) ⟨1612010, by rfl⟩ : syracuseStep 2149347 = 3224021) B3224021
theorem B8160821 : Blo 2147435 8160821 := bbase (se 5 (by rfl) ⟨382538, by rfl⟩ : syracuseStep 8160821 = 765077) (by norm_num)
theorem B5440547 : Blo 2147435 5440547 := bstep (se 1 (by rfl) ⟨4080410, by rfl⟩ : syracuseStep 5440547 = 8160821) B8160821
theorem B3627031 : Blo 2147435 3627031 := bstep (se 1 (by rfl) ⟨2720273, by rfl⟩ : syracuseStep 3627031 = 5440547) B5440547
theorem B4836041 : Blo 2147435 4836041 := bstep (se 2 (by rfl) ⟨1813515, by rfl⟩ : syracuseStep 4836041 = 3627031) B3627031
theorem B3224027 : Blo 2147435 3224027 := bstep (se 1 (by rfl) ⟨2418020, by rfl⟩ : syracuseStep 3224027 = 4836041) B4836041
theorem B2149351 : Blo 2147435 2149351 := bstep (se 1 (by rfl) ⟨1612013, by rfl⟩ : syracuseStep 2149351 = 3224027) B3224027
theorem B2418025 : Blo 2147435 2418025 := bbase (se 2 (by rfl) ⟨906759, by rfl⟩ : syracuseStep 2418025 = 1813519) (by norm_num)
theorem B3224033 : Blo 2147435 3224033 := bstep (se 2 (by rfl) ⟨1209012, by rfl⟩ : syracuseStep 3224033 = 2418025) B2418025
theorem B2149355 : Blo 2147435 2149355 := bstep (se 1 (by rfl) ⟨1612016, by rfl⟩ : syracuseStep 2149355 = 3224033) B3224033
theorem B2178685 : Blo 2147435 2178685 := bbase (se 3 (by rfl) ⟨408503, by rfl⟩ : syracuseStep 2178685 = 817007) (by norm_num)
theorem B2904913 : Blo 2147435 2904913 := bstep (se 2 (by rfl) ⟨1089342, by rfl⟩ : syracuseStep 2904913 = 2178685) B2178685
theorem B15492869 : Blo 2147435 15492869 := bstep (se 4 (by rfl) ⟨1452456, by rfl⟩ : syracuseStep 15492869 = 2904913) B2904913
theorem B10328579 : Blo 2147435 10328579 := bstep (se 1 (by rfl) ⟨7746434, by rfl⟩ : syracuseStep 10328579 = 15492869) B15492869
theorem B6885719 : Blo 2147435 6885719 := bstep (se 1 (by rfl) ⟨5164289, by rfl⟩ : syracuseStep 6885719 = 10328579) B10328579
theorem B4590479 : Blo 2147435 4590479 := bstep (se 1 (by rfl) ⟨3442859, by rfl⟩ : syracuseStep 4590479 = 6885719) B6885719
theorem B12241277 : Blo 2147435 12241277 := bstep (se 3 (by rfl) ⟨2295239, by rfl⟩ : syracuseStep 12241277 = 4590479) B4590479
theorem B8160851 : Blo 2147435 8160851 := bstep (se 1 (by rfl) ⟨6120638, by rfl⟩ : syracuseStep 8160851 = 12241277) B12241277
theorem B5440567 : Blo 2147435 5440567 := bstep (se 1 (by rfl) ⟨4080425, by rfl⟩ : syracuseStep 5440567 = 8160851) B8160851
theorem B7254089 : Blo 2147435 7254089 := bstep (se 2 (by rfl) ⟨2720283, by rfl⟩ : syracuseStep 7254089 = 5440567) B5440567
theorem B4836059 : Blo 2147435 4836059 := bstep (se 1 (by rfl) ⟨3627044, by rfl⟩ : syracuseStep 4836059 = 7254089) B7254089
theorem B3224039 : Blo 2147435 3224039 := bstep (se 1 (by rfl) ⟨2418029, by rfl⟩ : syracuseStep 3224039 = 4836059) B4836059
theorem B2149359 : Blo 2147435 2149359 := bstep (se 1 (by rfl) ⟨1612019, by rfl⟩ : syracuseStep 2149359 = 3224039) B3224039
theorem B3224045 : Blo 2147435 3224045 := bbase (se 3 (by rfl) ⟨604508, by rfl⟩ : syracuseStep 3224045 = 1209017) (by norm_num)
theorem B2149363 : Blo 2147435 2149363 := bstep (se 1 (by rfl) ⟨1612022, by rfl⟩ : syracuseStep 2149363 = 3224045) B3224045
theorem B4836077 : Blo 2147435 4836077 := bbase (se 3 (by rfl) ⟨906764, by rfl⟩ : syracuseStep 4836077 = 1813529) (by norm_num)
theorem B3224051 : Blo 2147435 3224051 := bstep (se 1 (by rfl) ⟨2418038, by rfl⟩ : syracuseStep 3224051 = 4836077) B4836077
theorem B2149367 : Blo 2147435 2149367 := bstep (se 1 (by rfl) ⟨1612025, by rfl⟩ : syracuseStep 2149367 = 3224051) B3224051
theorem B2295253 : Blo 2147435 2295253 := bbase (se 7 (by rfl) ⟨26897, by rfl⟩ : syracuseStep 2295253 = 53795) (by norm_num)
theorem B3060337 : Blo 2147435 3060337 := bstep (se 2 (by rfl) ⟨1147626, by rfl⟩ : syracuseStep 3060337 = 2295253) B2295253
theorem B4080449 : Blo 2147435 4080449 := bstep (se 2 (by rfl) ⟨1530168, by rfl⟩ : syracuseStep 4080449 = 3060337) B3060337
theorem B2720299 : Blo 2147435 2720299 := bstep (se 1 (by rfl) ⟨2040224, by rfl⟩ : syracuseStep 2720299 = 4080449) B4080449
theorem B3627065 : Blo 2147435 3627065 := bstep (se 2 (by rfl) ⟨1360149, by rfl⟩ : syracuseStep 3627065 = 2720299) B2720299
theorem B2418043 : Blo 2147435 2418043 := bstep (se 1 (by rfl) ⟨1813532, by rfl⟩ : syracuseStep 2418043 = 3627065) B3627065
theorem B3224057 : Blo 2147435 3224057 := bstep (se 2 (by rfl) ⟨1209021, by rfl⟩ : syracuseStep 3224057 = 2418043) B2418043
theorem B2149371 : Blo 2147435 2149371 := bstep (se 1 (by rfl) ⟨1612028, by rfl⟩ : syracuseStep 2149371 = 3224057) B3224057
theorem B61971925 : Blo 2147435 61971925 := bbase (se 7 (by rfl) ⟨726233, by rfl⟩ : syracuseStep 61971925 = 1452467) (by norm_num)
theorem B82629233 : Blo 2147435 82629233 := bstep (se 2 (by rfl) ⟨30985962, by rfl⟩ : syracuseStep 82629233 = 61971925) B61971925
theorem B55086155 : Blo 2147435 55086155 := bstep (se 1 (by rfl) ⟨41314616, by rfl⟩ : syracuseStep 55086155 = 82629233) B82629233
theorem B36724103 : Blo 2147435 36724103 := bstep (se 1 (by rfl) ⟨27543077, by rfl⟩ : syracuseStep 36724103 = 55086155) B55086155
theorem B24482735 : Blo 2147435 24482735 := bstep (se 1 (by rfl) ⟨18362051, by rfl⟩ : syracuseStep 24482735 = 36724103) B36724103
theorem B16321823 : Blo 2147435 16321823 := bstep (se 1 (by rfl) ⟨12241367, by rfl⟩ : syracuseStep 16321823 = 24482735) B24482735
theorem B10881215 : Blo 2147435 10881215 := bstep (se 1 (by rfl) ⟨8160911, by rfl⟩ : syracuseStep 10881215 = 16321823) B16321823
theorem B7254143 : Blo 2147435 7254143 := bstep (se 1 (by rfl) ⟨5440607, by rfl⟩ : syracuseStep 7254143 = 10881215) B10881215
theorem B4836095 : Blo 2147435 4836095 := bstep (se 1 (by rfl) ⟨3627071, by rfl⟩ : syracuseStep 4836095 = 7254143) B7254143
theorem B3224063 : Blo 2147435 3224063 := bstep (se 1 (by rfl) ⟨2418047, by rfl⟩ : syracuseStep 3224063 = 4836095) B4836095
theorem B2149375 : Blo 2147435 2149375 := bstep (se 1 (by rfl) ⟨1612031, by rfl⟩ : syracuseStep 2149375 = 3224063) B3224063
theorem B3224069 : Blo 2147435 3224069 := bbase (se 4 (by rfl) ⟨302256, by rfl⟩ : syracuseStep 3224069 = 604513) (by norm_num)
theorem B2149379 : Blo 2147435 2149379 := bstep (se 1 (by rfl) ⟨1612034, by rfl⟩ : syracuseStep 2149379 = 3224069) B3224069
theorem B3627085 : Blo 2147435 3627085 := bbase (se 3 (by rfl) ⟨680078, by rfl⟩ : syracuseStep 3627085 = 1360157) (by norm_num)
theorem B4836113 : Blo 2147435 4836113 := bstep (se 2 (by rfl) ⟨1813542, by rfl⟩ : syracuseStep 4836113 = 3627085) B3627085
theorem B3224075 : Blo 2147435 3224075 := bstep (se 1 (by rfl) ⟨2418056, by rfl⟩ : syracuseStep 3224075 = 4836113) B4836113
theorem B2149383 : Blo 2147435 2149383 := bstep (se 1 (by rfl) ⟨1612037, by rfl⟩ : syracuseStep 2149383 = 3224075) B3224075
theorem B2418061 : Blo 2147435 2418061 := bbase (se 3 (by rfl) ⟨453386, by rfl⟩ : syracuseStep 2418061 = 906773) (by norm_num)
theorem B3224081 : Blo 2147435 3224081 := bstep (se 2 (by rfl) ⟨1209030, by rfl⟩ : syracuseStep 3224081 = 2418061) B2418061
theorem B2149387 : Blo 2147435 2149387 := bstep (se 1 (by rfl) ⟨1612040, by rfl⟩ : syracuseStep 2149387 = 3224081) B3224081
theorem B7254197 : Blo 2147435 7254197 := bbase (se 5 (by rfl) ⟨340040, by rfl⟩ : syracuseStep 7254197 = 680081) (by norm_num)
theorem B4836131 : Blo 2147435 4836131 := bstep (se 1 (by rfl) ⟨3627098, by rfl⟩ : syracuseStep 4836131 = 7254197) B7254197
theorem B3224087 : Blo 2147435 3224087 := bstep (se 1 (by rfl) ⟨2418065, by rfl⟩ : syracuseStep 3224087 = 4836131) B4836131
theorem B2149391 : Blo 2147435 2149391 := bstep (se 1 (by rfl) ⟨1612043, by rfl⟩ : syracuseStep 2149391 = 3224087) B3224087
theorem B3224093 : Blo 2147435 3224093 := bbase (se 3 (by rfl) ⟨604517, by rfl⟩ : syracuseStep 3224093 = 1209035) (by norm_num)
theorem B2149395 : Blo 2147435 2149395 := bstep (se 1 (by rfl) ⟨1612046, by rfl⟩ : syracuseStep 2149395 = 3224093) B3224093
theorem B4836149 : Blo 2147435 4836149 := bbase (se 5 (by rfl) ⟨226694, by rfl⟩ : syracuseStep 4836149 = 453389) (by norm_num)
theorem B3224099 : Blo 2147435 3224099 := bstep (se 1 (by rfl) ⟨2418074, by rfl⟩ : syracuseStep 3224099 = 4836149) B4836149
theorem B2149399 : Blo 2147435 2149399 := bstep (se 1 (by rfl) ⟨1612049, by rfl⟩ : syracuseStep 2149399 = 3224099) B3224099
theorem B17466293 : Blo 2147435 17466293 := bbase (se 5 (by rfl) ⟨818732, by rfl⟩ : syracuseStep 17466293 = 1637465) (by norm_num)
theorem B46576781 : Blo 2147435 46576781 := bstep (se 3 (by rfl) ⟨8733146, by rfl⟩ : syracuseStep 46576781 = 17466293) B17466293
theorem B31051187 : Blo 2147435 31051187 := bstep (se 1 (by rfl) ⟨23288390, by rfl⟩ : syracuseStep 31051187 = 46576781) B46576781
theorem B20700791 : Blo 2147435 20700791 := bstep (se 1 (by rfl) ⟨15525593, by rfl⟩ : syracuseStep 20700791 = 31051187) B31051187
theorem B13800527 : Blo 2147435 13800527 := bstep (se 1 (by rfl) ⟨10350395, by rfl⟩ : syracuseStep 13800527 = 20700791) B20700791
theorem B9200351 : Blo 2147435 9200351 := bstep (se 1 (by rfl) ⟨6900263, by rfl⟩ : syracuseStep 9200351 = 13800527) B13800527
theorem B6133567 : Blo 2147435 6133567 := bstep (se 1 (by rfl) ⟨4600175, by rfl⟩ : syracuseStep 6133567 = 9200351) B9200351
theorem B8178089 : Blo 2147435 8178089 := bstep (se 2 (by rfl) ⟨3066783, by rfl⟩ : syracuseStep 8178089 = 6133567) B6133567
theorem B21808237 : Blo 2147435 21808237 := bstep (se 3 (by rfl) ⟨4089044, by rfl⟩ : syracuseStep 21808237 = 8178089) B8178089
theorem B29077649 : Blo 2147435 29077649 := bstep (se 2 (by rfl) ⟨10904118, by rfl⟩ : syracuseStep 29077649 = 21808237) B21808237
theorem B19385099 : Blo 2147435 19385099 := bstep (se 1 (by rfl) ⟨14538824, by rfl⟩ : syracuseStep 19385099 = 29077649) B29077649
theorem B12923399 : Blo 2147435 12923399 := bstep (se 1 (by rfl) ⟨9692549, by rfl⟩ : syracuseStep 12923399 = 19385099) B19385099
theorem B8615599 : Blo 2147435 8615599 := bstep (se 1 (by rfl) ⟨6461699, by rfl⟩ : syracuseStep 8615599 = 12923399) B12923399
theorem B45949861 : Blo 2147435 45949861 := bstep (se 4 (by rfl) ⟨4307799, by rfl⟩ : syracuseStep 45949861 = 8615599) B8615599
theorem B245065925 : Blo 2147435 245065925 := bstep (se 4 (by rfl) ⟨22974930, by rfl⟩ : syracuseStep 245065925 = 45949861) B45949861
theorem B163377283 : Blo 2147435 163377283 := bstep (se 1 (by rfl) ⟨122532962, by rfl⟩ : syracuseStep 163377283 = 245065925) B245065925
theorem B217836377 : Blo 2147435 217836377 := bstep (se 2 (by rfl) ⟨81688641, by rfl⟩ : syracuseStep 217836377 = 163377283) B163377283
theorem B145224251 : Blo 2147435 145224251 := bstep (se 1 (by rfl) ⟨108918188, by rfl⟩ : syracuseStep 145224251 = 217836377) B217836377
theorem B96816167 : Blo 2147435 96816167 := bstep (se 1 (by rfl) ⟨72612125, by rfl⟩ : syracuseStep 96816167 = 145224251) B145224251
theorem B64544111 : Blo 2147435 64544111 := bstep (se 1 (by rfl) ⟨48408083, by rfl⟩ : syracuseStep 64544111 = 96816167) B96816167
theorem B43029407 : Blo 2147435 43029407 := bstep (se 1 (by rfl) ⟨32272055, by rfl⟩ : syracuseStep 43029407 = 64544111) B64544111
theorem B28686271 : Blo 2147435 28686271 := bstep (se 1 (by rfl) ⟨21514703, by rfl⟩ : syracuseStep 28686271 = 43029407) B43029407
theorem B38248361 : Blo 2147435 38248361 := bstep (se 2 (by rfl) ⟨14343135, by rfl⟩ : syracuseStep 38248361 = 28686271) B28686271
theorem B25498907 : Blo 2147435 25498907 := bstep (se 1 (by rfl) ⟨19124180, by rfl⟩ : syracuseStep 25498907 = 38248361) B38248361
theorem B16999271 : Blo 2147435 16999271 := bstep (se 1 (by rfl) ⟨12749453, by rfl⟩ : syracuseStep 16999271 = 25498907) B25498907
theorem B11332847 : Blo 2147435 11332847 := bstep (se 1 (by rfl) ⟨8499635, by rfl⟩ : syracuseStep 11332847 = 16999271) B16999271
theorem B7555231 : Blo 2147435 7555231 := bstep (se 1 (by rfl) ⟨5666423, by rfl⟩ : syracuseStep 7555231 = 11332847) B11332847
theorem B10073641 : Blo 2147435 10073641 := bstep (se 2 (by rfl) ⟨3777615, by rfl⟩ : syracuseStep 10073641 = 7555231) B7555231
theorem B13431521 : Blo 2147435 13431521 := bstep (se 2 (by rfl) ⟨5036820, by rfl⟩ : syracuseStep 13431521 = 10073641) B10073641
theorem B35817389 : Blo 2147435 35817389 := bstep (se 3 (by rfl) ⟨6715760, by rfl⟩ : syracuseStep 35817389 = 13431521) B13431521
theorem B23878259 : Blo 2147435 23878259 := bstep (se 1 (by rfl) ⟨17908694, by rfl⟩ : syracuseStep 23878259 = 35817389) B35817389
theorem B15918839 : Blo 2147435 15918839 := bstep (se 1 (by rfl) ⟨11939129, by rfl⟩ : syracuseStep 15918839 = 23878259) B23878259
theorem B10612559 : Blo 2147435 10612559 := bstep (se 1 (by rfl) ⟨7959419, by rfl⟩ : syracuseStep 10612559 = 15918839) B15918839
theorem B7075039 : Blo 2147435 7075039 := bstep (se 1 (by rfl) ⟨5306279, by rfl⟩ : syracuseStep 7075039 = 10612559) B10612559
theorem B9433385 : Blo 2147435 9433385 := bstep (se 2 (by rfl) ⟨3537519, by rfl⟩ : syracuseStep 9433385 = 7075039) B7075039
theorem B6288923 : Blo 2147435 6288923 := bstep (se 1 (by rfl) ⟨4716692, by rfl⟩ : syracuseStep 6288923 = 9433385) B9433385
theorem B16770461 : Blo 2147435 16770461 := bstep (se 3 (by rfl) ⟨3144461, by rfl⟩ : syracuseStep 16770461 = 6288923) B6288923
theorem B44721229 : Blo 2147435 44721229 := bstep (se 3 (by rfl) ⟨8385230, by rfl⟩ : syracuseStep 44721229 = 16770461) B16770461
theorem B59628305 : Blo 2147435 59628305 := bstep (se 2 (by rfl) ⟨22360614, by rfl⟩ : syracuseStep 59628305 = 44721229) B44721229
theorem B39752203 : Blo 2147435 39752203 := bstep (se 1 (by rfl) ⟨29814152, by rfl⟩ : syracuseStep 39752203 = 59628305) B59628305
theorem B53002937 : Blo 2147435 53002937 := bstep (se 2 (by rfl) ⟨19876101, by rfl⟩ : syracuseStep 53002937 = 39752203) B39752203
theorem B35335291 : Blo 2147435 35335291 := bstep (se 1 (by rfl) ⟨26501468, by rfl⟩ : syracuseStep 35335291 = 53002937) B53002937
theorem B47113721 : Blo 2147435 47113721 := bstep (se 2 (by rfl) ⟨17667645, by rfl⟩ : syracuseStep 47113721 = 35335291) B35335291
theorem B31409147 : Blo 2147435 31409147 := bstep (se 1 (by rfl) ⟨23556860, by rfl⟩ : syracuseStep 31409147 = 47113721) B47113721
theorem B20939431 : Blo 2147435 20939431 := bstep (se 1 (by rfl) ⟨15704573, by rfl⟩ : syracuseStep 20939431 = 31409147) B31409147
theorem B27919241 : Blo 2147435 27919241 := bstep (se 2 (by rfl) ⟨10469715, by rfl⟩ : syracuseStep 27919241 = 20939431) B20939431
theorem B18612827 : Blo 2147435 18612827 := bstep (se 1 (by rfl) ⟨13959620, by rfl⟩ : syracuseStep 18612827 = 27919241) B27919241
theorem B12408551 : Blo 2147435 12408551 := bstep (se 1 (by rfl) ⟨9306413, by rfl⟩ : syracuseStep 12408551 = 18612827) B18612827
theorem B8272367 : Blo 2147435 8272367 := bstep (se 1 (by rfl) ⟨6204275, by rfl⟩ : syracuseStep 8272367 = 12408551) B12408551
theorem B5514911 : Blo 2147435 5514911 := bstep (se 1 (by rfl) ⟨4136183, by rfl⟩ : syracuseStep 5514911 = 8272367) B8272367
theorem B3676607 : Blo 2147435 3676607 := bstep (se 1 (by rfl) ⟨2757455, by rfl⟩ : syracuseStep 3676607 = 5514911) B5514911
theorem B2451071 : Blo 2147435 2451071 := bstep (se 1 (by rfl) ⟨1838303, by rfl⟩ : syracuseStep 2451071 = 3676607) B3676607
theorem B6536189 : Blo 2147435 6536189 := bstep (se 3 (by rfl) ⟨1225535, by rfl⟩ : syracuseStep 6536189 = 2451071) B2451071
theorem B4357459 : Blo 2147435 4357459 := bstep (se 1 (by rfl) ⟨3268094, by rfl⟩ : syracuseStep 4357459 = 6536189) B6536189
theorem B23239781 : Blo 2147435 23239781 := bstep (se 4 (by rfl) ⟨2178729, by rfl⟩ : syracuseStep 23239781 = 4357459) B4357459
theorem B15493187 : Blo 2147435 15493187 := bstep (se 1 (by rfl) ⟨11619890, by rfl⟩ : syracuseStep 15493187 = 23239781) B23239781
theorem B10328791 : Blo 2147435 10328791 := bstep (se 1 (by rfl) ⟨7746593, by rfl⟩ : syracuseStep 10328791 = 15493187) B15493187
theorem B13771721 : Blo 2147435 13771721 := bstep (se 2 (by rfl) ⟨5164395, by rfl⟩ : syracuseStep 13771721 = 10328791) B10328791
theorem B9181147 : Blo 2147435 9181147 := bstep (se 1 (by rfl) ⟨6885860, by rfl⟩ : syracuseStep 9181147 = 13771721) B13771721
theorem B12241529 : Blo 2147435 12241529 := bstep (se 2 (by rfl) ⟨4590573, by rfl⟩ : syracuseStep 12241529 = 9181147) B9181147
theorem B8161019 : Blo 2147435 8161019 := bstep (se 1 (by rfl) ⟨6120764, by rfl⟩ : syracuseStep 8161019 = 12241529) B12241529
theorem B5440679 : Blo 2147435 5440679 := bstep (se 1 (by rfl) ⟨4080509, by rfl⟩ : syracuseStep 5440679 = 8161019) B8161019
theorem B3627119 : Blo 2147435 3627119 := bstep (se 1 (by rfl) ⟨2720339, by rfl⟩ : syracuseStep 3627119 = 5440679) B5440679
theorem B2418079 : Blo 2147435 2418079 := bstep (se 1 (by rfl) ⟨1813559, by rfl⟩ : syracuseStep 2418079 = 3627119) B3627119
theorem B3224105 : Blo 2147435 3224105 := bstep (se 2 (by rfl) ⟨1209039, by rfl⟩ : syracuseStep 3224105 = 2418079) B2418079
theorem B2149403 : Blo 2147435 2149403 := bstep (se 1 (by rfl) ⟨1612052, by rfl⟩ : syracuseStep 2149403 = 3224105) B3224105
theorem B15704597 : Blo 2147435 15704597 := bbase (se 6 (by rfl) ⟨368076, by rfl⟩ : syracuseStep 15704597 = 736153) (by norm_num)
theorem B10469731 : Blo 2147435 10469731 := bstep (se 1 (by rfl) ⟨7852298, by rfl⟩ : syracuseStep 10469731 = 15704597) B15704597
theorem B13959641 : Blo 2147435 13959641 := bstep (se 2 (by rfl) ⟨5234865, by rfl⟩ : syracuseStep 13959641 = 10469731) B10469731
theorem B9306427 : Blo 2147435 9306427 := bstep (se 1 (by rfl) ⟨6979820, by rfl⟩ : syracuseStep 9306427 = 13959641) B13959641
theorem B12408569 : Blo 2147435 12408569 := bstep (se 2 (by rfl) ⟨4653213, by rfl⟩ : syracuseStep 12408569 = 9306427) B9306427
theorem B8272379 : Blo 2147435 8272379 := bstep (se 1 (by rfl) ⟨6204284, by rfl⟩ : syracuseStep 8272379 = 12408569) B12408569
theorem B22059677 : Blo 2147435 22059677 := bstep (se 3 (by rfl) ⟨4136189, by rfl⟩ : syracuseStep 22059677 = 8272379) B8272379
theorem B14706451 : Blo 2147435 14706451 := bstep (se 1 (by rfl) ⟨11029838, by rfl⟩ : syracuseStep 14706451 = 22059677) B22059677
theorem B19608601 : Blo 2147435 19608601 := bstep (se 2 (by rfl) ⟨7353225, by rfl⟩ : syracuseStep 19608601 = 14706451) B14706451
theorem B26144801 : Blo 2147435 26144801 := bstep (se 2 (by rfl) ⟨9804300, by rfl⟩ : syracuseStep 26144801 = 19608601) B19608601
theorem B17429867 : Blo 2147435 17429867 := bstep (se 1 (by rfl) ⟨13072400, by rfl⟩ : syracuseStep 17429867 = 26144801) B26144801
theorem B11619911 : Blo 2147435 11619911 := bstep (se 1 (by rfl) ⟨8714933, by rfl⟩ : syracuseStep 11619911 = 17429867) B17429867
theorem B7746607 : Blo 2147435 7746607 := bstep (se 1 (by rfl) ⟨5809955, by rfl⟩ : syracuseStep 7746607 = 11619911) B11619911
theorem B10328809 : Blo 2147435 10328809 := bstep (se 2 (by rfl) ⟨3873303, by rfl⟩ : syracuseStep 10328809 = 7746607) B7746607
theorem B13771745 : Blo 2147435 13771745 := bstep (se 2 (by rfl) ⟨5164404, by rfl⟩ : syracuseStep 13771745 = 10328809) B10328809
theorem B9181163 : Blo 2147435 9181163 := bstep (se 1 (by rfl) ⟨6885872, by rfl⟩ : syracuseStep 9181163 = 13771745) B13771745
theorem B6120775 : Blo 2147435 6120775 := bstep (se 1 (by rfl) ⟨4590581, by rfl⟩ : syracuseStep 6120775 = 9181163) B9181163
theorem B8161033 : Blo 2147435 8161033 := bstep (se 2 (by rfl) ⟨3060387, by rfl⟩ : syracuseStep 8161033 = 6120775) B6120775
theorem B10881377 : Blo 2147435 10881377 := bstep (se 2 (by rfl) ⟨4080516, by rfl⟩ : syracuseStep 10881377 = 8161033) B8161033
theorem B7254251 : Blo 2147435 7254251 := bstep (se 1 (by rfl) ⟨5440688, by rfl⟩ : syracuseStep 7254251 = 10881377) B10881377
theorem B4836167 : Blo 2147435 4836167 := bstep (se 1 (by rfl) ⟨3627125, by rfl⟩ : syracuseStep 4836167 = 7254251) B7254251
theorem B3224111 : Blo 2147435 3224111 := bstep (se 1 (by rfl) ⟨2418083, by rfl⟩ : syracuseStep 3224111 = 4836167) B4836167
theorem B2149407 : Blo 2147435 2149407 := bstep (se 1 (by rfl) ⟨1612055, by rfl⟩ : syracuseStep 2149407 = 3224111) B3224111
theorem B3224117 : Blo 2147435 3224117 := bbase (se 5 (by rfl) ⟨151130, by rfl⟩ : syracuseStep 3224117 = 302261) (by norm_num)
theorem B2149411 : Blo 2147435 2149411 := bstep (se 1 (by rfl) ⟨1612058, by rfl⟩ : syracuseStep 2149411 = 3224117) B3224117
theorem B5440709 : Blo 2147435 5440709 := bbase (se 4 (by rfl) ⟨510066, by rfl⟩ : syracuseStep 5440709 = 1020133) (by norm_num)
theorem B3627139 : Blo 2147435 3627139 := bstep (se 1 (by rfl) ⟨2720354, by rfl⟩ : syracuseStep 3627139 = 5440709) B5440709
theorem B4836185 : Blo 2147435 4836185 := bstep (se 2 (by rfl) ⟨1813569, by rfl⟩ : syracuseStep 4836185 = 3627139) B3627139
theorem B3224123 : Blo 2147435 3224123 := bstep (se 1 (by rfl) ⟨2418092, by rfl⟩ : syracuseStep 3224123 = 4836185) B4836185
theorem B2149415 : Blo 2147435 2149415 := bstep (se 1 (by rfl) ⟨1612061, by rfl⟩ : syracuseStep 2149415 = 3224123) B3224123
theorem B2418097 : Blo 2147435 2418097 := bbase (se 2 (by rfl) ⟨906786, by rfl⟩ : syracuseStep 2418097 = 1813573) (by norm_num)
theorem B3224129 : Blo 2147435 3224129 := bstep (se 2 (by rfl) ⟨1209048, by rfl⟩ : syracuseStep 3224129 = 2418097) B2418097
theorem B2149419 : Blo 2147435 2149419 := bstep (se 1 (by rfl) ⟨1612064, by rfl⟩ : syracuseStep 2149419 = 3224129) B3224129
theorem B6120821 : Blo 2147435 6120821 := bbase (se 5 (by rfl) ⟨286913, by rfl⟩ : syracuseStep 6120821 = 573827) (by norm_num)
theorem B4080547 : Blo 2147435 4080547 := bstep (se 1 (by rfl) ⟨3060410, by rfl⟩ : syracuseStep 4080547 = 6120821) B6120821
theorem B5440729 : Blo 2147435 5440729 := bstep (se 2 (by rfl) ⟨2040273, by rfl⟩ : syracuseStep 5440729 = 4080547) B4080547
theorem B7254305 : Blo 2147435 7254305 := bstep (se 2 (by rfl) ⟨2720364, by rfl⟩ : syracuseStep 7254305 = 5440729) B5440729
theorem B4836203 : Blo 2147435 4836203 := bstep (se 1 (by rfl) ⟨3627152, by rfl⟩ : syracuseStep 4836203 = 7254305) B7254305
theorem B3224135 : Blo 2147435 3224135 := bstep (se 1 (by rfl) ⟨2418101, by rfl⟩ : syracuseStep 3224135 = 4836203) B4836203
theorem B2149423 : Blo 2147435 2149423 := bstep (se 1 (by rfl) ⟨1612067, by rfl⟩ : syracuseStep 2149423 = 3224135) B3224135
theorem B3224141 : Blo 2147435 3224141 := bbase (se 3 (by rfl) ⟨604526, by rfl⟩ : syracuseStep 3224141 = 1209053) (by norm_num)
theorem B2149427 : Blo 2147435 2149427 := bstep (se 1 (by rfl) ⟨1612070, by rfl⟩ : syracuseStep 2149427 = 3224141) B3224141
theorem B4836221 : Blo 2147435 4836221 := bbase (se 3 (by rfl) ⟨906791, by rfl⟩ : syracuseStep 4836221 = 1813583) (by norm_num)
theorem B3224147 : Blo 2147435 3224147 := bstep (se 1 (by rfl) ⟨2418110, by rfl⟩ : syracuseStep 3224147 = 4836221) B4836221
theorem B2149431 : Blo 2147435 2149431 := bstep (se 1 (by rfl) ⟨1612073, by rfl⟩ : syracuseStep 2149431 = 3224147) B3224147
theorem B3627173 : Blo 2147435 3627173 := bbase (se 4 (by rfl) ⟨340047, by rfl⟩ : syracuseStep 3627173 = 680095) (by norm_num)
theorem B2418115 : Blo 2147435 2418115 := bstep (se 1 (by rfl) ⟨1813586, by rfl⟩ : syracuseStep 2418115 = 3627173) B3627173
theorem B3224153 : Blo 2147435 3224153 := bstep (se 2 (by rfl) ⟨1209057, by rfl⟩ : syracuseStep 3224153 = 2418115) B2418115
theorem B2149435 : Blo 2147435 2149435 := bstep (se 1 (by rfl) ⟨1612076, by rfl⟩ : syracuseStep 2149435 = 3224153) B3224153
theorem C0 (j : ℕ) (h1 : 536858 ≤ j) (h2 : j ≤ 537358) : Blo 2147435 (4 * j + 3) := by
  interval_cases j
  · exact B2147435
  · exact B2147439
  · exact B2147443
  · exact B2147447
  · exact B2147451
  · exact B2147455
  · exact B2147459
  · exact B2147463
  · exact B2147467
  · exact B2147471
  · exact B2147475
  · exact B2147479
  · exact B2147483
  · exact B2147487
  · exact B2147491
  · exact B2147495
  · exact B2147499
  · exact B2147503
  · exact B2147507
  · exact B2147511
  · exact B2147515
  · exact B2147519
  · exact B2147523
  · exact B2147527
  · exact B2147531
  · exact B2147535
  · exact B2147539
  · exact B2147543
  · exact B2147547
  · exact B2147551
  · exact B2147555
  · exact B2147559
  · exact B2147563
  · exact B2147567
  · exact B2147571
  · exact B2147575
  · exact B2147579
  · exact B2147583
  · exact B2147587
  · exact B2147591
  · exact B2147595
  · exact B2147599
  · exact B2147603
  · exact B2147607
  · exact B2147611
  · exact B2147615
  · exact B2147619
  · exact B2147623
  · exact B2147627
  · exact B2147631
  · exact B2147635
  · exact B2147639
  · exact B2147643
  · exact B2147647
  · exact B2147651
  · exact B2147655
  · exact B2147659
  · exact B2147663
  · exact B2147667
  · exact B2147671
  · exact B2147675
  · exact B2147679
  · exact B2147683
  · exact B2147687
  · exact B2147691
  · exact B2147695
  · exact B2147699
  · exact B2147703
  · exact B2147707
  · exact B2147711
  · exact B2147715
  · exact B2147719
  · exact B2147723
  · exact B2147727
  · exact B2147731
  · exact B2147735
  · exact B2147739
  · exact B2147743
  · exact B2147747
  · exact B2147751
  · exact B2147755
  · exact B2147759
  · exact B2147763
  · exact B2147767
  · exact B2147771
  · exact B2147775
  · exact B2147779
  · exact B2147783
  · exact B2147787
  · exact B2147791
  · exact B2147795
  · exact B2147799
  · exact B2147803
  · exact B2147807
  · exact B2147811
  · exact B2147815
  · exact B2147819
  · exact B2147823
  · exact B2147827
  · exact B2147831
  · exact B2147835
  · exact B2147839
  · exact B2147843
  · exact B2147847
  · exact B2147851
  · exact B2147855
  · exact B2147859
  · exact B2147863
  · exact B2147867
  · exact B2147871
  · exact B2147875
  · exact B2147879
  · exact B2147883
  · exact B2147887
  · exact B2147891
  · exact B2147895
  · exact B2147899
  · exact B2147903
  · exact B2147907
  · exact B2147911
  · exact B2147915
  · exact B2147919
  · exact B2147923
  · exact B2147927
  · exact B2147931
  · exact B2147935
  · exact B2147939
  · exact B2147943
  · exact B2147947
  · exact B2147951
  · exact B2147955
  · exact B2147959
  · exact B2147963
  · exact B2147967
  · exact B2147971
  · exact B2147975
  · exact B2147979
  · exact B2147983
  · exact B2147987
  · exact B2147991
  · exact B2147995
  · exact B2147999
  · exact B2148003
  · exact B2148007
  · exact B2148011
  · exact B2148015
  · exact B2148019
  · exact B2148023
  · exact B2148027
  · exact B2148031
  · exact B2148035
  · exact B2148039
  · exact B2148043
  · exact B2148047
  · exact B2148051
  · exact B2148055
  · exact B2148059
  · exact B2148063
  · exact B2148067
  · exact B2148071
  · exact B2148075
  · exact B2148079
  · exact B2148083
  · exact B2148087
  · exact B2148091
  · exact B2148095
  · exact B2148099
  · exact B2148103
  · exact B2148107
  · exact B2148111
  · exact B2148115
  · exact B2148119
  · exact B2148123
  · exact B2148127
  · exact B2148131
  · exact B2148135
  · exact B2148139
  · exact B2148143
  · exact B2148147
  · exact B2148151
  · exact B2148155
  · exact B2148159
  · exact B2148163
  · exact B2148167
  · exact B2148171
  · exact B2148175
  · exact B2148179
  · exact B2148183
  · exact B2148187
  · exact B2148191
  · exact B2148195
  · exact B2148199
  · exact B2148203
  · exact B2148207
  · exact B2148211
  · exact B2148215
  · exact B2148219
  · exact B2148223
  · exact B2148227
  · exact B2148231
  · exact B2148235
  · exact B2148239
  · exact B2148243
  · exact B2148247
  · exact B2148251
  · exact B2148255
  · exact B2148259
  · exact B2148263
  · exact B2148267
  · exact B2148271
  · exact B2148275
  · exact B2148279
  · exact B2148283
  · exact B2148287
  · exact B2148291
  · exact B2148295
  · exact B2148299
  · exact B2148303
  · exact B2148307
  · exact B2148311
  · exact B2148315
  · exact B2148319
  · exact B2148323
  · exact B2148327
  · exact B2148331
  · exact B2148335
  · exact B2148339
  · exact B2148343
  · exact B2148347
  · exact B2148351
  · exact B2148355
  · exact B2148359
  · exact B2148363
  · exact B2148367
  · exact B2148371
  · exact B2148375
  · exact B2148379
  · exact B2148383
  · exact B2148387
  · exact B2148391
  · exact B2148395
  · exact B2148399
  · exact B2148403
  · exact B2148407
  · exact B2148411
  · exact B2148415
  · exact B2148419
  · exact B2148423
  · exact B2148427
  · exact B2148431
  · exact B2148435
  · exact B2148439
  · exact B2148443
  · exact B2148447
  · exact B2148451
  · exact B2148455
  · exact B2148459
  · exact B2148463
  · exact B2148467
  · exact B2148471
  · exact B2148475
  · exact B2148479
  · exact B2148483
  · exact B2148487
  · exact B2148491
  · exact B2148495
  · exact B2148499
  · exact B2148503
  · exact B2148507
  · exact B2148511
  · exact B2148515
  · exact B2148519
  · exact B2148523
  · exact B2148527
  · exact B2148531
  · exact B2148535
  · exact B2148539
  · exact B2148543
  · exact B2148547
  · exact B2148551
  · exact B2148555
  · exact B2148559
  · exact B2148563
  · exact B2148567
  · exact B2148571
  · exact B2148575
  · exact B2148579
  · exact B2148583
  · exact B2148587
  · exact B2148591
  · exact B2148595
  · exact B2148599
  · exact B2148603
  · exact B2148607
  · exact B2148611
  · exact B2148615
  · exact B2148619
  · exact B2148623
  · exact B2148627
  · exact B2148631
  · exact B2148635
  · exact B2148639
  · exact B2148643
  · exact B2148647
  · exact B2148651
  · exact B2148655
  · exact B2148659
  · exact B2148663
  · exact B2148667
  · exact B2148671
  · exact B2148675
  · exact B2148679
  · exact B2148683
  · exact B2148687
  · exact B2148691
  · exact B2148695
  · exact B2148699
  · exact B2148703
  · exact B2148707
  · exact B2148711
  · exact B2148715
  · exact B2148719
  · exact B2148723
  · exact B2148727
  · exact B2148731
  · exact B2148735
  · exact B2148739
  · exact B2148743
  · exact B2148747
  · exact B2148751
  · exact B2148755
  · exact B2148759
  · exact B2148763
  · exact B2148767
  · exact B2148771
  · exact B2148775
  · exact B2148779
  · exact B2148783
  · exact B2148787
  · exact B2148791
  · exact B2148795
  · exact B2148799
  · exact B2148803
  · exact B2148807
  · exact B2148811
  · exact B2148815
  · exact B2148819
  · exact B2148823
  · exact B2148827
  · exact B2148831
  · exact B2148835
  · exact B2148839
  · exact B2148843
  · exact B2148847
  · exact B2148851
  · exact B2148855
  · exact B2148859
  · exact B2148863
  · exact B2148867
  · exact B2148871
  · exact B2148875
  · exact B2148879
  · exact B2148883
  · exact B2148887
  · exact B2148891
  · exact B2148895
  · exact B2148899
  · exact B2148903
  · exact B2148907
  · exact B2148911
  · exact B2148915
  · exact B2148919
  · exact B2148923
  · exact B2148927
  · exact B2148931
  · exact B2148935
  · exact B2148939
  · exact B2148943
  · exact B2148947
  · exact B2148951
  · exact B2148955
  · exact B2148959
  · exact B2148963
  · exact B2148967
  · exact B2148971
  · exact B2148975
  · exact B2148979
  · exact B2148983
  · exact B2148987
  · exact B2148991
  · exact B2148995
  · exact B2148999
  · exact B2149003
  · exact B2149007
  · exact B2149011
  · exact B2149015
  · exact B2149019
  · exact B2149023
  · exact B2149027
  · exact B2149031
  · exact B2149035
  · exact B2149039
  · exact B2149043
  · exact B2149047
  · exact B2149051
  · exact B2149055
  · exact B2149059
  · exact B2149063
  · exact B2149067
  · exact B2149071
  · exact B2149075
  · exact B2149079
  · exact B2149083
  · exact B2149087
  · exact B2149091
  · exact B2149095
  · exact B2149099
  · exact B2149103
  · exact B2149107
  · exact B2149111
  · exact B2149115
  · exact B2149119
  · exact B2149123
  · exact B2149127
  · exact B2149131
  · exact B2149135
  · exact B2149139
  · exact B2149143
  · exact B2149147
  · exact B2149151
  · exact B2149155
  · exact B2149159
  · exact B2149163
  · exact B2149167
  · exact B2149171
  · exact B2149175
  · exact B2149179
  · exact B2149183
  · exact B2149187
  · exact B2149191
  · exact B2149195
  · exact B2149199
  · exact B2149203
  · exact B2149207
  · exact B2149211
  · exact B2149215
  · exact B2149219
  · exact B2149223
  · exact B2149227
  · exact B2149231
  · exact B2149235
  · exact B2149239
  · exact B2149243
  · exact B2149247
  · exact B2149251
  · exact B2149255
  · exact B2149259
  · exact B2149263
  · exact B2149267
  · exact B2149271
  · exact B2149275
  · exact B2149279
  · exact B2149283
  · exact B2149287
  · exact B2149291
  · exact B2149295
  · exact B2149299
  · exact B2149303
  · exact B2149307
  · exact B2149311
  · exact B2149315
  · exact B2149319
  · exact B2149323
  · exact B2149327
  · exact B2149331
  · exact B2149335
  · exact B2149339
  · exact B2149343
  · exact B2149347
  · exact B2149351
  · exact B2149355
  · exact B2149359
  · exact B2149363
  · exact B2149367
  · exact B2149371
  · exact B2149375
  · exact B2149379
  · exact B2149383
  · exact B2149387
  · exact B2149391
  · exact B2149395
  · exact B2149399
  · exact B2149403
  · exact B2149407
  · exact B2149411
  · exact B2149415
  · exact B2149419
  · exact B2149423
  · exact B2149427
  · exact B2149431
  · exact B2149435
theorem solution (m : ℕ) (hlo : 2147435 ≤ m) (hhi : m ≤ 2149435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 536858 ≤ j := by omega
    have hj2 : j ≤ 537358 := by omega
    have hb : Blo 2147435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
