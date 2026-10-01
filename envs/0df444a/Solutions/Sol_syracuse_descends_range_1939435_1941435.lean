-- Prove2me | solution 1 for syracuse_descends_range_1939435_1941435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:29.936568+00:00
-- url     : https://prove2.me/submissions/25ac7e78-e573-41ac-a2c3-a7827d589e9f

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

theorem B2181865 : Blo 1939435 2181865 := bbase (se 2 (by rfl) ⟨818199, by rfl⟩ : syracuseStep 2181865 = 1636399) (by norm_num)
theorem B2909153 : Blo 1939435 2909153 := bstep (se 2 (by rfl) ⟨1090932, by rfl⟩ : syracuseStep 2909153 = 2181865) B2181865
theorem B1939435 : Blo 1939435 1939435 := bstep (se 1 (by rfl) ⟨1454576, by rfl⟩ : syracuseStep 1939435 = 2909153) B2909153
theorem B11045717 : Blo 1939435 11045717 := bbase (se 9 (by rfl) ⟨32360, by rfl⟩ : syracuseStep 11045717 = 64721) (by norm_num)
theorem B7363811 : Blo 1939435 7363811 := bstep (se 1 (by rfl) ⟨5522858, by rfl⟩ : syracuseStep 7363811 = 11045717) B11045717
theorem B4909207 : Blo 1939435 4909207 := bstep (se 1 (by rfl) ⟨3681905, by rfl⟩ : syracuseStep 4909207 = 7363811) B7363811
theorem B6545609 : Blo 1939435 6545609 := bstep (se 2 (by rfl) ⟨2454603, by rfl⟩ : syracuseStep 6545609 = 4909207) B4909207
theorem B4363739 : Blo 1939435 4363739 := bstep (se 1 (by rfl) ⟨3272804, by rfl⟩ : syracuseStep 4363739 = 6545609) B6545609
theorem B2909159 : Blo 1939435 2909159 := bstep (se 1 (by rfl) ⟨2181869, by rfl⟩ : syracuseStep 2909159 = 4363739) B4363739
theorem B1939439 : Blo 1939435 1939439 := bstep (se 1 (by rfl) ⟨1454579, by rfl⟩ : syracuseStep 1939439 = 2909159) B2909159
theorem B2909165 : Blo 1939435 2909165 := bbase (se 3 (by rfl) ⟨545468, by rfl⟩ : syracuseStep 2909165 = 1090937) (by norm_num)
theorem B1939443 : Blo 1939435 1939443 := bstep (se 1 (by rfl) ⟨1454582, by rfl⟩ : syracuseStep 1939443 = 2909165) B2909165
theorem B4363757 : Blo 1939435 4363757 := bbase (se 3 (by rfl) ⟨818204, by rfl⟩ : syracuseStep 4363757 = 1636409) (by norm_num)
theorem B2909171 : Blo 1939435 2909171 := bstep (se 1 (by rfl) ⟨2181878, by rfl⟩ : syracuseStep 2909171 = 4363757) B4363757
theorem B1939447 : Blo 1939435 1939447 := bstep (se 1 (by rfl) ⟨1454585, by rfl⟩ : syracuseStep 1939447 = 2909171) B2909171
theorem B2656981 : Blo 1939435 2656981 := bbase (se 7 (by rfl) ⟨31136, by rfl⟩ : syracuseStep 2656981 = 62273) (by norm_num)
theorem B3542641 : Blo 1939435 3542641 := bstep (se 2 (by rfl) ⟨1328490, by rfl⟩ : syracuseStep 3542641 = 2656981) B2656981
theorem B75576341 : Blo 1939435 75576341 := bstep (se 6 (by rfl) ⟨1771320, by rfl⟩ : syracuseStep 75576341 = 3542641) B3542641
theorem B50384227 : Blo 1939435 50384227 := bstep (se 1 (by rfl) ⟨37788170, by rfl⟩ : syracuseStep 50384227 = 75576341) B75576341
theorem B67178969 : Blo 1939435 67178969 := bstep (se 2 (by rfl) ⟨25192113, by rfl⟩ : syracuseStep 67178969 = 50384227) B50384227
theorem B44785979 : Blo 1939435 44785979 := bstep (se 1 (by rfl) ⟨33589484, by rfl⟩ : syracuseStep 44785979 = 67178969) B67178969
theorem B29857319 : Blo 1939435 29857319 := bstep (se 1 (by rfl) ⟨22392989, by rfl⟩ : syracuseStep 29857319 = 44785979) B44785979
theorem B19904879 : Blo 1939435 19904879 := bstep (se 1 (by rfl) ⟨14928659, by rfl⟩ : syracuseStep 19904879 = 29857319) B29857319
theorem B13269919 : Blo 1939435 13269919 := bstep (se 1 (by rfl) ⟨9952439, by rfl⟩ : syracuseStep 13269919 = 19904879) B19904879
theorem B17693225 : Blo 1939435 17693225 := bstep (se 2 (by rfl) ⟨6634959, by rfl⟩ : syracuseStep 17693225 = 13269919) B13269919
theorem B11795483 : Blo 1939435 11795483 := bstep (se 1 (by rfl) ⟨8846612, by rfl⟩ : syracuseStep 11795483 = 17693225) B17693225
theorem B7863655 : Blo 1939435 7863655 := bstep (se 1 (by rfl) ⟨5897741, by rfl⟩ : syracuseStep 7863655 = 11795483) B11795483
theorem B10484873 : Blo 1939435 10484873 := bstep (se 2 (by rfl) ⟨3931827, by rfl⟩ : syracuseStep 10484873 = 7863655) B7863655
theorem B6989915 : Blo 1939435 6989915 := bstep (se 1 (by rfl) ⟨5242436, by rfl⟩ : syracuseStep 6989915 = 10484873) B10484873
theorem B4659943 : Blo 1939435 4659943 := bstep (se 1 (by rfl) ⟨3494957, by rfl⟩ : syracuseStep 4659943 = 6989915) B6989915
theorem B6213257 : Blo 1939435 6213257 := bstep (se 2 (by rfl) ⟨2329971, by rfl⟩ : syracuseStep 6213257 = 4659943) B4659943
theorem B4142171 : Blo 1939435 4142171 := bstep (se 1 (by rfl) ⟨3106628, by rfl⟩ : syracuseStep 4142171 = 6213257) B6213257
theorem B2761447 : Blo 1939435 2761447 := bstep (se 1 (by rfl) ⟨2071085, by rfl⟩ : syracuseStep 2761447 = 4142171) B4142171
theorem B3681929 : Blo 1939435 3681929 := bstep (se 2 (by rfl) ⟨1380723, by rfl⟩ : syracuseStep 3681929 = 2761447) B2761447
theorem B2454619 : Blo 1939435 2454619 := bstep (se 1 (by rfl) ⟨1840964, by rfl⟩ : syracuseStep 2454619 = 3681929) B3681929
theorem B3272825 : Blo 1939435 3272825 := bstep (se 2 (by rfl) ⟨1227309, by rfl⟩ : syracuseStep 3272825 = 2454619) B2454619
theorem B2181883 : Blo 1939435 2181883 := bstep (se 1 (by rfl) ⟨1636412, by rfl⟩ : syracuseStep 2181883 = 3272825) B3272825
theorem B2909177 : Blo 1939435 2909177 := bstep (se 2 (by rfl) ⟨1090941, by rfl⟩ : syracuseStep 2909177 = 2181883) B2181883
theorem B1939451 : Blo 1939435 1939451 := bstep (se 1 (by rfl) ⟨1454588, by rfl⟩ : syracuseStep 1939451 = 2909177) B2909177
theorem B111838805 : Blo 1939435 111838805 := bbase (se 8 (by rfl) ⟨655305, by rfl⟩ : syracuseStep 111838805 = 1310611) (by norm_num)
theorem B74559203 : Blo 1939435 74559203 := bstep (se 1 (by rfl) ⟨55919402, by rfl⟩ : syracuseStep 74559203 = 111838805) B111838805
theorem B49706135 : Blo 1939435 49706135 := bstep (se 1 (by rfl) ⟨37279601, by rfl⟩ : syracuseStep 49706135 = 74559203) B74559203
theorem B33137423 : Blo 1939435 33137423 := bstep (se 1 (by rfl) ⟨24853067, by rfl⟩ : syracuseStep 33137423 = 49706135) B49706135
theorem B22091615 : Blo 1939435 22091615 := bstep (se 1 (by rfl) ⟨16568711, by rfl⟩ : syracuseStep 22091615 = 33137423) B33137423
theorem B14727743 : Blo 1939435 14727743 := bstep (se 1 (by rfl) ⟨11045807, by rfl⟩ : syracuseStep 14727743 = 22091615) B22091615
theorem B9818495 : Blo 1939435 9818495 := bstep (se 1 (by rfl) ⟨7363871, by rfl⟩ : syracuseStep 9818495 = 14727743) B14727743
theorem B6545663 : Blo 1939435 6545663 := bstep (se 1 (by rfl) ⟨4909247, by rfl⟩ : syracuseStep 6545663 = 9818495) B9818495
theorem B4363775 : Blo 1939435 4363775 := bstep (se 1 (by rfl) ⟨3272831, by rfl⟩ : syracuseStep 4363775 = 6545663) B6545663
theorem B2909183 : Blo 1939435 2909183 := bstep (se 1 (by rfl) ⟨2181887, by rfl⟩ : syracuseStep 2909183 = 4363775) B4363775
theorem B1939455 : Blo 1939435 1939455 := bstep (se 1 (by rfl) ⟨1454591, by rfl⟩ : syracuseStep 1939455 = 2909183) B2909183
theorem B2909189 : Blo 1939435 2909189 := bbase (se 4 (by rfl) ⟨272736, by rfl⟩ : syracuseStep 2909189 = 545473) (by norm_num)
theorem B1939459 : Blo 1939435 1939459 := bstep (se 1 (by rfl) ⟨1454594, by rfl⟩ : syracuseStep 1939459 = 2909189) B2909189
theorem B3272845 : Blo 1939435 3272845 := bbase (se 3 (by rfl) ⟨613658, by rfl⟩ : syracuseStep 3272845 = 1227317) (by norm_num)
theorem B4363793 : Blo 1939435 4363793 := bstep (se 2 (by rfl) ⟨1636422, by rfl⟩ : syracuseStep 4363793 = 3272845) B3272845
theorem B2909195 : Blo 1939435 2909195 := bstep (se 1 (by rfl) ⟨2181896, by rfl⟩ : syracuseStep 2909195 = 4363793) B4363793
theorem B1939463 : Blo 1939435 1939463 := bstep (se 1 (by rfl) ⟨1454597, by rfl⟩ : syracuseStep 1939463 = 2909195) B2909195
theorem B2181901 : Blo 1939435 2181901 := bbase (se 3 (by rfl) ⟨409106, by rfl⟩ : syracuseStep 2181901 = 818213) (by norm_num)
theorem B2909201 : Blo 1939435 2909201 := bstep (se 2 (by rfl) ⟨1090950, by rfl⟩ : syracuseStep 2909201 = 2181901) B2181901
theorem B1939467 : Blo 1939435 1939467 := bstep (se 1 (by rfl) ⟨1454600, by rfl⟩ : syracuseStep 1939467 = 2909201) B2909201
theorem B6545717 : Blo 1939435 6545717 := bbase (se 5 (by rfl) ⟨306830, by rfl⟩ : syracuseStep 6545717 = 613661) (by norm_num)
theorem B4363811 : Blo 1939435 4363811 := bstep (se 1 (by rfl) ⟨3272858, by rfl⟩ : syracuseStep 4363811 = 6545717) B6545717
theorem B2909207 : Blo 1939435 2909207 := bstep (se 1 (by rfl) ⟨2181905, by rfl⟩ : syracuseStep 2909207 = 4363811) B4363811
theorem B1939471 : Blo 1939435 1939471 := bstep (se 1 (by rfl) ⟨1454603, by rfl⟩ : syracuseStep 1939471 = 2909207) B2909207
theorem B2909213 : Blo 1939435 2909213 := bbase (se 3 (by rfl) ⟨545477, by rfl⟩ : syracuseStep 2909213 = 1090955) (by norm_num)
theorem B1939475 : Blo 1939435 1939475 := bstep (se 1 (by rfl) ⟨1454606, by rfl⟩ : syracuseStep 1939475 = 2909213) B2909213
theorem B4363829 : Blo 1939435 4363829 := bbase (se 5 (by rfl) ⟨204554, by rfl⟩ : syracuseStep 4363829 = 409109) (by norm_num)
theorem B2909219 : Blo 1939435 2909219 := bstep (se 1 (by rfl) ⟨2181914, by rfl⟩ : syracuseStep 2909219 = 4363829) B4363829
theorem B1939479 : Blo 1939435 1939479 := bstep (se 1 (by rfl) ⟨1454609, by rfl⟩ : syracuseStep 1939479 = 2909219) B2909219
theorem B2621261 : Blo 1939435 2621261 := bbase (se 3 (by rfl) ⟨491486, by rfl⟩ : syracuseStep 2621261 = 982973) (by norm_num)
theorem B6990029 : Blo 1939435 6990029 := bstep (se 3 (by rfl) ⟨1310630, by rfl⟩ : syracuseStep 6990029 = 2621261) B2621261
theorem B4660019 : Blo 1939435 4660019 := bstep (se 1 (by rfl) ⟨3495014, by rfl⟩ : syracuseStep 4660019 = 6990029) B6990029
theorem B3106679 : Blo 1939435 3106679 := bstep (se 1 (by rfl) ⟨2330009, by rfl⟩ : syracuseStep 3106679 = 4660019) B4660019
theorem B8284477 : Blo 1939435 8284477 := bstep (se 3 (by rfl) ⟨1553339, by rfl⟩ : syracuseStep 8284477 = 3106679) B3106679
theorem B11045969 : Blo 1939435 11045969 := bstep (se 2 (by rfl) ⟨4142238, by rfl⟩ : syracuseStep 11045969 = 8284477) B8284477
theorem B7363979 : Blo 1939435 7363979 := bstep (se 1 (by rfl) ⟨5522984, by rfl⟩ : syracuseStep 7363979 = 11045969) B11045969
theorem B4909319 : Blo 1939435 4909319 := bstep (se 1 (by rfl) ⟨3681989, by rfl⟩ : syracuseStep 4909319 = 7363979) B7363979
theorem B3272879 : Blo 1939435 3272879 := bstep (se 1 (by rfl) ⟨2454659, by rfl⟩ : syracuseStep 3272879 = 4909319) B4909319
theorem B2181919 : Blo 1939435 2181919 := bstep (se 1 (by rfl) ⟨1636439, by rfl⟩ : syracuseStep 2181919 = 3272879) B3272879
theorem B2909225 : Blo 1939435 2909225 := bstep (se 2 (by rfl) ⟨1090959, by rfl⟩ : syracuseStep 2909225 = 2181919) B2181919
theorem B1939483 : Blo 1939435 1939483 := bstep (se 1 (by rfl) ⟨1454612, by rfl⟩ : syracuseStep 1939483 = 2909225) B2909225
theorem B3106685 : Blo 1939435 3106685 := bbase (se 3 (by rfl) ⟨582503, by rfl⟩ : syracuseStep 3106685 = 1165007) (by norm_num)
theorem B8284493 : Blo 1939435 8284493 := bstep (se 3 (by rfl) ⟨1553342, by rfl⟩ : syracuseStep 8284493 = 3106685) B3106685
theorem B5522995 : Blo 1939435 5522995 := bstep (se 1 (by rfl) ⟨4142246, by rfl⟩ : syracuseStep 5522995 = 8284493) B8284493
theorem B7363993 : Blo 1939435 7363993 := bstep (se 2 (by rfl) ⟨2761497, by rfl⟩ : syracuseStep 7363993 = 5522995) B5522995
theorem B9818657 : Blo 1939435 9818657 := bstep (se 2 (by rfl) ⟨3681996, by rfl⟩ : syracuseStep 9818657 = 7363993) B7363993
theorem B6545771 : Blo 1939435 6545771 := bstep (se 1 (by rfl) ⟨4909328, by rfl⟩ : syracuseStep 6545771 = 9818657) B9818657
theorem B4363847 : Blo 1939435 4363847 := bstep (se 1 (by rfl) ⟨3272885, by rfl⟩ : syracuseStep 4363847 = 6545771) B6545771
theorem B2909231 : Blo 1939435 2909231 := bstep (se 1 (by rfl) ⟨2181923, by rfl⟩ : syracuseStep 2909231 = 4363847) B4363847
theorem B1939487 : Blo 1939435 1939487 := bstep (se 1 (by rfl) ⟨1454615, by rfl⟩ : syracuseStep 1939487 = 2909231) B2909231
theorem B2909237 : Blo 1939435 2909237 := bbase (se 5 (by rfl) ⟨136370, by rfl⟩ : syracuseStep 2909237 = 272741) (by norm_num)
theorem B1939491 : Blo 1939435 1939491 := bstep (se 1 (by rfl) ⟨1454618, by rfl⟩ : syracuseStep 1939491 = 2909237) B2909237
theorem B4909349 : Blo 1939435 4909349 := bbase (se 4 (by rfl) ⟨460251, by rfl⟩ : syracuseStep 4909349 = 920503) (by norm_num)
theorem B3272899 : Blo 1939435 3272899 := bstep (se 1 (by rfl) ⟨2454674, by rfl⟩ : syracuseStep 3272899 = 4909349) B4909349
theorem B4363865 : Blo 1939435 4363865 := bstep (se 2 (by rfl) ⟨1636449, by rfl⟩ : syracuseStep 4363865 = 3272899) B3272899
theorem B2909243 : Blo 1939435 2909243 := bstep (se 1 (by rfl) ⟨2181932, by rfl⟩ : syracuseStep 2909243 = 4363865) B4363865
theorem B1939495 : Blo 1939435 1939495 := bstep (se 1 (by rfl) ⟨1454621, by rfl⟩ : syracuseStep 1939495 = 2909243) B2909243
theorem B2181937 : Blo 1939435 2181937 := bbase (se 2 (by rfl) ⟨818226, by rfl⟩ : syracuseStep 2181937 = 1636453) (by norm_num)
theorem B2909249 : Blo 1939435 2909249 := bstep (se 2 (by rfl) ⟨1090968, by rfl⟩ : syracuseStep 2909249 = 2181937) B2181937
theorem B1939499 : Blo 1939435 1939499 := bstep (se 1 (by rfl) ⟨1454624, by rfl⟩ : syracuseStep 1939499 = 2909249) B2909249
theorem B6990101 : Blo 1939435 6990101 := bbase (se 6 (by rfl) ⟨163830, by rfl⟩ : syracuseStep 6990101 = 327661) (by norm_num)
theorem B4660067 : Blo 1939435 4660067 := bstep (se 1 (by rfl) ⟨3495050, by rfl⟩ : syracuseStep 4660067 = 6990101) B6990101
theorem B3106711 : Blo 1939435 3106711 := bstep (se 1 (by rfl) ⟨2330033, by rfl⟩ : syracuseStep 3106711 = 4660067) B4660067
theorem B4142281 : Blo 1939435 4142281 := bstep (se 2 (by rfl) ⟨1553355, by rfl⟩ : syracuseStep 4142281 = 3106711) B3106711
theorem B5523041 : Blo 1939435 5523041 := bstep (se 2 (by rfl) ⟨2071140, by rfl⟩ : syracuseStep 5523041 = 4142281) B4142281
theorem B3682027 : Blo 1939435 3682027 := bstep (se 1 (by rfl) ⟨2761520, by rfl⟩ : syracuseStep 3682027 = 5523041) B5523041
theorem B4909369 : Blo 1939435 4909369 := bstep (se 2 (by rfl) ⟨1841013, by rfl⟩ : syracuseStep 4909369 = 3682027) B3682027
theorem B6545825 : Blo 1939435 6545825 := bstep (se 2 (by rfl) ⟨2454684, by rfl⟩ : syracuseStep 6545825 = 4909369) B4909369
theorem B4363883 : Blo 1939435 4363883 := bstep (se 1 (by rfl) ⟨3272912, by rfl⟩ : syracuseStep 4363883 = 6545825) B6545825
theorem B2909255 : Blo 1939435 2909255 := bstep (se 1 (by rfl) ⟨2181941, by rfl⟩ : syracuseStep 2909255 = 4363883) B4363883
theorem B1939503 : Blo 1939435 1939503 := bstep (se 1 (by rfl) ⟨1454627, by rfl⟩ : syracuseStep 1939503 = 2909255) B2909255
theorem B2909261 : Blo 1939435 2909261 := bbase (se 3 (by rfl) ⟨545486, by rfl⟩ : syracuseStep 2909261 = 1090973) (by norm_num)
theorem B1939507 : Blo 1939435 1939507 := bstep (se 1 (by rfl) ⟨1454630, by rfl⟩ : syracuseStep 1939507 = 2909261) B2909261
theorem B4363901 : Blo 1939435 4363901 := bbase (se 3 (by rfl) ⟨818231, by rfl⟩ : syracuseStep 4363901 = 1636463) (by norm_num)
theorem B2909267 : Blo 1939435 2909267 := bstep (se 1 (by rfl) ⟨2181950, by rfl⟩ : syracuseStep 2909267 = 4363901) B4363901
theorem B1939511 : Blo 1939435 1939511 := bstep (se 1 (by rfl) ⟨1454633, by rfl⟩ : syracuseStep 1939511 = 2909267) B2909267
theorem B3272933 : Blo 1939435 3272933 := bbase (se 4 (by rfl) ⟨306837, by rfl⟩ : syracuseStep 3272933 = 613675) (by norm_num)
theorem B2181955 : Blo 1939435 2181955 := bstep (se 1 (by rfl) ⟨1636466, by rfl⟩ : syracuseStep 2181955 = 3272933) B3272933
theorem B2909273 : Blo 1939435 2909273 := bstep (se 2 (by rfl) ⟨1090977, by rfl⟩ : syracuseStep 2909273 = 2181955) B2181955
theorem B1939515 : Blo 1939435 1939515 := bstep (se 1 (by rfl) ⟨1454636, by rfl⟩ : syracuseStep 1939515 = 2909273) B2909273
theorem B17935253 : Blo 1939435 17935253 := bbase (se 6 (by rfl) ⟨420357, by rfl⟩ : syracuseStep 17935253 = 840715) (by norm_num)
theorem B11956835 : Blo 1939435 11956835 := bstep (se 1 (by rfl) ⟨8967626, by rfl⟩ : syracuseStep 11956835 = 17935253) B17935253
theorem B7971223 : Blo 1939435 7971223 := bstep (se 1 (by rfl) ⟨5978417, by rfl⟩ : syracuseStep 7971223 = 11956835) B11956835
theorem B10628297 : Blo 1939435 10628297 := bstep (se 2 (by rfl) ⟨3985611, by rfl⟩ : syracuseStep 10628297 = 7971223) B7971223
theorem B7085531 : Blo 1939435 7085531 := bstep (se 1 (by rfl) ⟨5314148, by rfl⟩ : syracuseStep 7085531 = 10628297) B10628297
theorem B4723687 : Blo 1939435 4723687 := bstep (se 1 (by rfl) ⟨3542765, by rfl⟩ : syracuseStep 4723687 = 7085531) B7085531
theorem B6298249 : Blo 1939435 6298249 := bstep (se 2 (by rfl) ⟨2361843, by rfl⟩ : syracuseStep 6298249 = 4723687) B4723687
theorem B8397665 : Blo 1939435 8397665 := bstep (se 2 (by rfl) ⟨3149124, by rfl⟩ : syracuseStep 8397665 = 6298249) B6298249
theorem B5598443 : Blo 1939435 5598443 := bstep (se 1 (by rfl) ⟨4198832, by rfl⟩ : syracuseStep 5598443 = 8397665) B8397665
theorem B14929181 : Blo 1939435 14929181 := bstep (se 3 (by rfl) ⟨2799221, by rfl⟩ : syracuseStep 14929181 = 5598443) B5598443
theorem B9952787 : Blo 1939435 9952787 := bstep (se 1 (by rfl) ⟨7464590, by rfl⟩ : syracuseStep 9952787 = 14929181) B14929181
theorem B6635191 : Blo 1939435 6635191 := bstep (se 1 (by rfl) ⟨4976393, by rfl⟩ : syracuseStep 6635191 = 9952787) B9952787
theorem B8846921 : Blo 1939435 8846921 := bstep (se 2 (by rfl) ⟨3317595, by rfl⟩ : syracuseStep 8846921 = 6635191) B6635191
theorem B5897947 : Blo 1939435 5897947 := bstep (se 1 (by rfl) ⟨4423460, by rfl⟩ : syracuseStep 5897947 = 8846921) B8846921
theorem B7863929 : Blo 1939435 7863929 := bstep (se 2 (by rfl) ⟨2948973, by rfl⟩ : syracuseStep 7863929 = 5897947) B5897947
theorem B5242619 : Blo 1939435 5242619 := bstep (se 1 (by rfl) ⟨3931964, by rfl⟩ : syracuseStep 5242619 = 7863929) B7863929
theorem B3495079 : Blo 1939435 3495079 := bstep (se 1 (by rfl) ⟨2621309, by rfl⟩ : syracuseStep 3495079 = 5242619) B5242619
theorem B4660105 : Blo 1939435 4660105 := bstep (se 2 (by rfl) ⟨1747539, by rfl⟩ : syracuseStep 4660105 = 3495079) B3495079
theorem B6213473 : Blo 1939435 6213473 := bstep (se 2 (by rfl) ⟨2330052, by rfl⟩ : syracuseStep 6213473 = 4660105) B4660105
theorem B4142315 : Blo 1939435 4142315 := bstep (se 1 (by rfl) ⟨3106736, by rfl⟩ : syracuseStep 4142315 = 6213473) B6213473
theorem B2761543 : Blo 1939435 2761543 := bstep (se 1 (by rfl) ⟨2071157, by rfl⟩ : syracuseStep 2761543 = 4142315) B4142315
theorem B14728229 : Blo 1939435 14728229 := bstep (se 4 (by rfl) ⟨1380771, by rfl⟩ : syracuseStep 14728229 = 2761543) B2761543
theorem B9818819 : Blo 1939435 9818819 := bstep (se 1 (by rfl) ⟨7364114, by rfl⟩ : syracuseStep 9818819 = 14728229) B14728229
theorem B6545879 : Blo 1939435 6545879 := bstep (se 1 (by rfl) ⟨4909409, by rfl⟩ : syracuseStep 6545879 = 9818819) B9818819
theorem B4363919 : Blo 1939435 4363919 := bstep (se 1 (by rfl) ⟨3272939, by rfl⟩ : syracuseStep 4363919 = 6545879) B6545879
theorem B2909279 : Blo 1939435 2909279 := bstep (se 1 (by rfl) ⟨2181959, by rfl⟩ : syracuseStep 2909279 = 4363919) B4363919
theorem B1939519 : Blo 1939435 1939519 := bstep (se 1 (by rfl) ⟨1454639, by rfl⟩ : syracuseStep 1939519 = 2909279) B2909279
theorem B2909285 : Blo 1939435 2909285 := bbase (se 4 (by rfl) ⟨272745, by rfl⟩ : syracuseStep 2909285 = 545491) (by norm_num)
theorem B1939523 : Blo 1939435 1939523 := bstep (se 1 (by rfl) ⟨1454642, by rfl⟩ : syracuseStep 1939523 = 2909285) B2909285
theorem B4142333 : Blo 1939435 4142333 := bbase (se 3 (by rfl) ⟨776687, by rfl⟩ : syracuseStep 4142333 = 1553375) (by norm_num)
theorem B2761555 : Blo 1939435 2761555 := bstep (se 1 (by rfl) ⟨2071166, by rfl⟩ : syracuseStep 2761555 = 4142333) B4142333
theorem B3682073 : Blo 1939435 3682073 := bstep (se 2 (by rfl) ⟨1380777, by rfl⟩ : syracuseStep 3682073 = 2761555) B2761555
theorem B2454715 : Blo 1939435 2454715 := bstep (se 1 (by rfl) ⟨1841036, by rfl⟩ : syracuseStep 2454715 = 3682073) B3682073
theorem B3272953 : Blo 1939435 3272953 := bstep (se 2 (by rfl) ⟨1227357, by rfl⟩ : syracuseStep 3272953 = 2454715) B2454715
theorem B4363937 : Blo 1939435 4363937 := bstep (se 2 (by rfl) ⟨1636476, by rfl⟩ : syracuseStep 4363937 = 3272953) B3272953
theorem B2909291 : Blo 1939435 2909291 := bstep (se 1 (by rfl) ⟨2181968, by rfl⟩ : syracuseStep 2909291 = 4363937) B4363937
theorem B1939527 : Blo 1939435 1939527 := bstep (se 1 (by rfl) ⟨1454645, by rfl⟩ : syracuseStep 1939527 = 2909291) B2909291
theorem B2181973 : Blo 1939435 2181973 := bbase (se 9 (by rfl) ⟨6392, by rfl⟩ : syracuseStep 2181973 = 12785) (by norm_num)
theorem B2909297 : Blo 1939435 2909297 := bstep (se 2 (by rfl) ⟨1090986, by rfl⟩ : syracuseStep 2909297 = 2181973) B2181973
theorem B1939531 : Blo 1939435 1939531 := bstep (se 1 (by rfl) ⟨1454648, by rfl⟩ : syracuseStep 1939531 = 2909297) B2909297
theorem B2454725 : Blo 1939435 2454725 := bbase (se 4 (by rfl) ⟨230130, by rfl⟩ : syracuseStep 2454725 = 460261) (by norm_num)
theorem B6545933 : Blo 1939435 6545933 := bstep (se 3 (by rfl) ⟨1227362, by rfl⟩ : syracuseStep 6545933 = 2454725) B2454725
theorem B4363955 : Blo 1939435 4363955 := bstep (se 1 (by rfl) ⟨3272966, by rfl⟩ : syracuseStep 4363955 = 6545933) B6545933
theorem B2909303 : Blo 1939435 2909303 := bstep (se 1 (by rfl) ⟨2181977, by rfl⟩ : syracuseStep 2909303 = 4363955) B4363955
theorem B1939535 : Blo 1939435 1939535 := bstep (se 1 (by rfl) ⟨1454651, by rfl⟩ : syracuseStep 1939535 = 2909303) B2909303
theorem B2909309 : Blo 1939435 2909309 := bbase (se 3 (by rfl) ⟨545495, by rfl⟩ : syracuseStep 2909309 = 1090991) (by norm_num)
theorem B1939539 : Blo 1939435 1939539 := bstep (se 1 (by rfl) ⟨1454654, by rfl⟩ : syracuseStep 1939539 = 2909309) B2909309
theorem B4363973 : Blo 1939435 4363973 := bbase (se 4 (by rfl) ⟨409122, by rfl⟩ : syracuseStep 4363973 = 818245) (by norm_num)
theorem B2909315 : Blo 1939435 2909315 := bstep (se 1 (by rfl) ⟨2181986, by rfl⟩ : syracuseStep 2909315 = 4363973) B4363973
theorem B1939543 : Blo 1939435 1939543 := bstep (se 1 (by rfl) ⟨1454657, by rfl⟩ : syracuseStep 1939543 = 2909315) B2909315
theorem B3932021 : Blo 1939435 3932021 := bbase (se 5 (by rfl) ⟨184313, by rfl⟩ : syracuseStep 3932021 = 368627) (by norm_num)
theorem B10485389 : Blo 1939435 10485389 := bstep (se 3 (by rfl) ⟨1966010, by rfl⟩ : syracuseStep 10485389 = 3932021) B3932021
theorem B27961037 : Blo 1939435 27961037 := bstep (se 3 (by rfl) ⟨5242694, by rfl⟩ : syracuseStep 27961037 = 10485389) B10485389
theorem B18640691 : Blo 1939435 18640691 := bstep (se 1 (by rfl) ⟨13980518, by rfl⟩ : syracuseStep 18640691 = 27961037) B27961037
theorem B12427127 : Blo 1939435 12427127 := bstep (se 1 (by rfl) ⟨9320345, by rfl⟩ : syracuseStep 12427127 = 18640691) B18640691
theorem B8284751 : Blo 1939435 8284751 := bstep (se 1 (by rfl) ⟨6213563, by rfl⟩ : syracuseStep 8284751 = 12427127) B12427127
theorem B5523167 : Blo 1939435 5523167 := bstep (se 1 (by rfl) ⟨4142375, by rfl⟩ : syracuseStep 5523167 = 8284751) B8284751
theorem B3682111 : Blo 1939435 3682111 := bstep (se 1 (by rfl) ⟨2761583, by rfl⟩ : syracuseStep 3682111 = 5523167) B5523167
theorem B4909481 : Blo 1939435 4909481 := bstep (se 2 (by rfl) ⟨1841055, by rfl⟩ : syracuseStep 4909481 = 3682111) B3682111
theorem B3272987 : Blo 1939435 3272987 := bstep (se 1 (by rfl) ⟨2454740, by rfl⟩ : syracuseStep 3272987 = 4909481) B4909481
theorem B2181991 : Blo 1939435 2181991 := bstep (se 1 (by rfl) ⟨1636493, by rfl⟩ : syracuseStep 2181991 = 3272987) B3272987
theorem B2909321 : Blo 1939435 2909321 := bstep (se 2 (by rfl) ⟨1090995, by rfl⟩ : syracuseStep 2909321 = 2181991) B2181991
theorem B1939547 : Blo 1939435 1939547 := bstep (se 1 (by rfl) ⟨1454660, by rfl⟩ : syracuseStep 1939547 = 2909321) B2909321
theorem B9818981 : Blo 1939435 9818981 := bbase (se 4 (by rfl) ⟨920529, by rfl⟩ : syracuseStep 9818981 = 1841059) (by norm_num)
theorem B6545987 : Blo 1939435 6545987 := bstep (se 1 (by rfl) ⟨4909490, by rfl⟩ : syracuseStep 6545987 = 9818981) B9818981
theorem B4363991 : Blo 1939435 4363991 := bstep (se 1 (by rfl) ⟨3272993, by rfl⟩ : syracuseStep 4363991 = 6545987) B6545987
theorem B2909327 : Blo 1939435 2909327 := bstep (se 1 (by rfl) ⟨2181995, by rfl⟩ : syracuseStep 2909327 = 4363991) B4363991
theorem B1939551 : Blo 1939435 1939551 := bstep (se 1 (by rfl) ⟨1454663, by rfl⟩ : syracuseStep 1939551 = 2909327) B2909327
theorem B2909333 : Blo 1939435 2909333 := bbase (se 6 (by rfl) ⟨68187, by rfl⟩ : syracuseStep 2909333 = 136375) (by norm_num)
theorem B1939555 : Blo 1939435 1939555 := bstep (se 1 (by rfl) ⟨1454666, by rfl⟩ : syracuseStep 1939555 = 2909333) B2909333
theorem B3030053 : Blo 1939435 3030053 := bbase (se 4 (by rfl) ⟨284067, by rfl⟩ : syracuseStep 3030053 = 568135) (by norm_num)
theorem B8080141 : Blo 1939435 8080141 := bstep (se 3 (by rfl) ⟨1515026, by rfl⟩ : syracuseStep 8080141 = 3030053) B3030053
theorem B10773521 : Blo 1939435 10773521 := bstep (se 2 (by rfl) ⟨4040070, by rfl⟩ : syracuseStep 10773521 = 8080141) B8080141
theorem B7182347 : Blo 1939435 7182347 := bstep (se 1 (by rfl) ⟨5386760, by rfl⟩ : syracuseStep 7182347 = 10773521) B10773521
theorem B19152925 : Blo 1939435 19152925 := bstep (se 3 (by rfl) ⟨3591173, by rfl⟩ : syracuseStep 19152925 = 7182347) B7182347
theorem B102148933 : Blo 1939435 102148933 := bstep (se 4 (by rfl) ⟨9576462, by rfl⟩ : syracuseStep 102148933 = 19152925) B19152925
theorem B136198577 : Blo 1939435 136198577 := bstep (se 2 (by rfl) ⟨51074466, by rfl⟩ : syracuseStep 136198577 = 102148933) B102148933
theorem B90799051 : Blo 1939435 90799051 := bstep (se 1 (by rfl) ⟨68099288, by rfl⟩ : syracuseStep 90799051 = 136198577) B136198577
theorem B121065401 : Blo 1939435 121065401 := bstep (se 2 (by rfl) ⟨45399525, by rfl⟩ : syracuseStep 121065401 = 90799051) B90799051
theorem B80710267 : Blo 1939435 80710267 := bstep (se 1 (by rfl) ⟨60532700, by rfl⟩ : syracuseStep 80710267 = 121065401) B121065401
theorem B107613689 : Blo 1939435 107613689 := bstep (se 2 (by rfl) ⟨40355133, by rfl⟩ : syracuseStep 107613689 = 80710267) B80710267
theorem B286969837 : Blo 1939435 286969837 := bstep (se 3 (by rfl) ⟨53806844, by rfl⟩ : syracuseStep 286969837 = 107613689) B107613689
theorem B382626449 : Blo 1939435 382626449 := bstep (se 2 (by rfl) ⟨143484918, by rfl⟩ : syracuseStep 382626449 = 286969837) B286969837
theorem B255084299 : Blo 1939435 255084299 := bstep (se 1 (by rfl) ⟨191313224, by rfl⟩ : syracuseStep 255084299 = 382626449) B382626449
theorem B170056199 : Blo 1939435 170056199 := bstep (se 1 (by rfl) ⟨127542149, by rfl⟩ : syracuseStep 170056199 = 255084299) B255084299
theorem B113370799 : Blo 1939435 113370799 := bstep (se 1 (by rfl) ⟨85028099, by rfl⟩ : syracuseStep 113370799 = 170056199) B170056199
theorem B151161065 : Blo 1939435 151161065 := bstep (se 2 (by rfl) ⟨56685399, by rfl⟩ : syracuseStep 151161065 = 113370799) B113370799
theorem B100774043 : Blo 1939435 100774043 := bstep (se 1 (by rfl) ⟨75580532, by rfl⟩ : syracuseStep 100774043 = 151161065) B151161065
theorem B67182695 : Blo 1939435 67182695 := bstep (se 1 (by rfl) ⟨50387021, by rfl⟩ : syracuseStep 67182695 = 100774043) B100774043
theorem B44788463 : Blo 1939435 44788463 := bstep (se 1 (by rfl) ⟨33591347, by rfl⟩ : syracuseStep 44788463 = 67182695) B67182695
theorem B29858975 : Blo 1939435 29858975 := bstep (se 1 (by rfl) ⟨22394231, by rfl⟩ : syracuseStep 29858975 = 44788463) B44788463
theorem B19905983 : Blo 1939435 19905983 := bstep (se 1 (by rfl) ⟨14929487, by rfl⟩ : syracuseStep 19905983 = 29858975) B29858975
theorem B13270655 : Blo 1939435 13270655 := bstep (se 1 (by rfl) ⟨9952991, by rfl⟩ : syracuseStep 13270655 = 19905983) B19905983
theorem B8847103 : Blo 1939435 8847103 := bstep (se 1 (by rfl) ⟨6635327, by rfl⟩ : syracuseStep 8847103 = 13270655) B13270655
theorem B11796137 : Blo 1939435 11796137 := bstep (se 2 (by rfl) ⟨4423551, by rfl⟩ : syracuseStep 11796137 = 8847103) B8847103
theorem B7864091 : Blo 1939435 7864091 := bstep (se 1 (by rfl) ⟨5898068, by rfl⟩ : syracuseStep 7864091 = 11796137) B11796137
theorem B5242727 : Blo 1939435 5242727 := bstep (se 1 (by rfl) ⟨3932045, by rfl⟩ : syracuseStep 5242727 = 7864091) B7864091
theorem B3495151 : Blo 1939435 3495151 := bstep (se 1 (by rfl) ⟨2621363, by rfl⟩ : syracuseStep 3495151 = 5242727) B5242727
theorem B4660201 : Blo 1939435 4660201 := bstep (se 2 (by rfl) ⟨1747575, by rfl⟩ : syracuseStep 4660201 = 3495151) B3495151
theorem B6213601 : Blo 1939435 6213601 := bstep (se 2 (by rfl) ⟨2330100, by rfl⟩ : syracuseStep 6213601 = 4660201) B4660201
theorem B8284801 : Blo 1939435 8284801 := bstep (se 2 (by rfl) ⟨3106800, by rfl⟩ : syracuseStep 8284801 = 6213601) B6213601
theorem B11046401 : Blo 1939435 11046401 := bstep (se 2 (by rfl) ⟨4142400, by rfl⟩ : syracuseStep 11046401 = 8284801) B8284801
theorem B7364267 : Blo 1939435 7364267 := bstep (se 1 (by rfl) ⟨5523200, by rfl⟩ : syracuseStep 7364267 = 11046401) B11046401
theorem B4909511 : Blo 1939435 4909511 := bstep (se 1 (by rfl) ⟨3682133, by rfl⟩ : syracuseStep 4909511 = 7364267) B7364267
theorem B3273007 : Blo 1939435 3273007 := bstep (se 1 (by rfl) ⟨2454755, by rfl⟩ : syracuseStep 3273007 = 4909511) B4909511
theorem B4364009 : Blo 1939435 4364009 := bstep (se 2 (by rfl) ⟨1636503, by rfl⟩ : syracuseStep 4364009 = 3273007) B3273007
theorem B2909339 : Blo 1939435 2909339 := bstep (se 1 (by rfl) ⟨2182004, by rfl⟩ : syracuseStep 2909339 = 4364009) B4364009
theorem B1939559 : Blo 1939435 1939559 := bstep (se 1 (by rfl) ⟨1454669, by rfl⟩ : syracuseStep 1939559 = 2909339) B2909339
theorem B2182009 : Blo 1939435 2182009 := bbase (se 2 (by rfl) ⟨818253, by rfl⟩ : syracuseStep 2182009 = 1636507) (by norm_num)
theorem B2909345 : Blo 1939435 2909345 := bstep (se 2 (by rfl) ⟨1091004, by rfl⟩ : syracuseStep 2909345 = 2182009) B2182009
theorem B1939563 : Blo 1939435 1939563 := bstep (se 1 (by rfl) ⟨1454672, by rfl⟩ : syracuseStep 1939563 = 2909345) B2909345
theorem B12427253 : Blo 1939435 12427253 := bbase (se 5 (by rfl) ⟨582527, by rfl⟩ : syracuseStep 12427253 = 1165055) (by norm_num)
theorem B8284835 : Blo 1939435 8284835 := bstep (se 1 (by rfl) ⟨6213626, by rfl⟩ : syracuseStep 8284835 = 12427253) B12427253
theorem B5523223 : Blo 1939435 5523223 := bstep (se 1 (by rfl) ⟨4142417, by rfl⟩ : syracuseStep 5523223 = 8284835) B8284835
theorem B7364297 : Blo 1939435 7364297 := bstep (se 2 (by rfl) ⟨2761611, by rfl⟩ : syracuseStep 7364297 = 5523223) B5523223
theorem B4909531 : Blo 1939435 4909531 := bstep (se 1 (by rfl) ⟨3682148, by rfl⟩ : syracuseStep 4909531 = 7364297) B7364297
theorem B6546041 : Blo 1939435 6546041 := bstep (se 2 (by rfl) ⟨2454765, by rfl⟩ : syracuseStep 6546041 = 4909531) B4909531
theorem B4364027 : Blo 1939435 4364027 := bstep (se 1 (by rfl) ⟨3273020, by rfl⟩ : syracuseStep 4364027 = 6546041) B6546041
theorem B2909351 : Blo 1939435 2909351 := bstep (se 1 (by rfl) ⟨2182013, by rfl⟩ : syracuseStep 2909351 = 4364027) B4364027
theorem B1939567 : Blo 1939435 1939567 := bstep (se 1 (by rfl) ⟨1454675, by rfl⟩ : syracuseStep 1939567 = 2909351) B2909351
theorem B2909357 : Blo 1939435 2909357 := bbase (se 3 (by rfl) ⟨545504, by rfl⟩ : syracuseStep 2909357 = 1091009) (by norm_num)
theorem B1939571 : Blo 1939435 1939571 := bstep (se 1 (by rfl) ⟨1454678, by rfl⟩ : syracuseStep 1939571 = 2909357) B2909357
theorem B4364045 : Blo 1939435 4364045 := bbase (se 3 (by rfl) ⟨818258, by rfl⟩ : syracuseStep 4364045 = 1636517) (by norm_num)
theorem B2909363 : Blo 1939435 2909363 := bstep (se 1 (by rfl) ⟨2182022, by rfl⟩ : syracuseStep 2909363 = 4364045) B4364045
theorem B1939575 : Blo 1939435 1939575 := bstep (se 1 (by rfl) ⟨1454681, by rfl⟩ : syracuseStep 1939575 = 2909363) B2909363
theorem B2454781 : Blo 1939435 2454781 := bbase (se 3 (by rfl) ⟨460271, by rfl⟩ : syracuseStep 2454781 = 920543) (by norm_num)
theorem B3273041 : Blo 1939435 3273041 := bstep (se 2 (by rfl) ⟨1227390, by rfl⟩ : syracuseStep 3273041 = 2454781) B2454781
theorem B2182027 : Blo 1939435 2182027 := bstep (se 1 (by rfl) ⟨1636520, by rfl⟩ : syracuseStep 2182027 = 3273041) B3273041
theorem B2909369 : Blo 1939435 2909369 := bstep (se 2 (by rfl) ⟨1091013, by rfl⟩ : syracuseStep 2909369 = 2182027) B2182027
theorem B1939579 : Blo 1939435 1939579 := bstep (se 1 (by rfl) ⟨1454684, by rfl⟩ : syracuseStep 1939579 = 2909369) B2909369
theorem B2330129 : Blo 1939435 2330129 := bbase (se 2 (by rfl) ⟨873798, by rfl⟩ : syracuseStep 2330129 = 1747597) (by norm_num)
theorem B6213677 : Blo 1939435 6213677 := bstep (se 3 (by rfl) ⟨1165064, by rfl⟩ : syracuseStep 6213677 = 2330129) B2330129
theorem B16569805 : Blo 1939435 16569805 := bstep (se 3 (by rfl) ⟨3106838, by rfl⟩ : syracuseStep 16569805 = 6213677) B6213677
theorem B22093073 : Blo 1939435 22093073 := bstep (se 2 (by rfl) ⟨8284902, by rfl⟩ : syracuseStep 22093073 = 16569805) B16569805
theorem B14728715 : Blo 1939435 14728715 := bstep (se 1 (by rfl) ⟨11046536, by rfl⟩ : syracuseStep 14728715 = 22093073) B22093073
theorem B9819143 : Blo 1939435 9819143 := bstep (se 1 (by rfl) ⟨7364357, by rfl⟩ : syracuseStep 9819143 = 14728715) B14728715
theorem B6546095 : Blo 1939435 6546095 := bstep (se 1 (by rfl) ⟨4909571, by rfl⟩ : syracuseStep 6546095 = 9819143) B9819143
theorem B4364063 : Blo 1939435 4364063 := bstep (se 1 (by rfl) ⟨3273047, by rfl⟩ : syracuseStep 4364063 = 6546095) B6546095
theorem B2909375 : Blo 1939435 2909375 := bstep (se 1 (by rfl) ⟨2182031, by rfl⟩ : syracuseStep 2909375 = 4364063) B4364063
theorem B1939583 : Blo 1939435 1939583 := bstep (se 1 (by rfl) ⟨1454687, by rfl⟩ : syracuseStep 1939583 = 2909375) B2909375
theorem B2909381 : Blo 1939435 2909381 := bbase (se 4 (by rfl) ⟨272754, by rfl⟩ : syracuseStep 2909381 = 545509) (by norm_num)
theorem B1939587 : Blo 1939435 1939587 := bstep (se 1 (by rfl) ⟨1454690, by rfl⟩ : syracuseStep 1939587 = 2909381) B2909381
theorem B3273061 : Blo 1939435 3273061 := bbase (se 4 (by rfl) ⟨306849, by rfl⟩ : syracuseStep 3273061 = 613699) (by norm_num)
theorem B4364081 : Blo 1939435 4364081 := bstep (se 2 (by rfl) ⟨1636530, by rfl⟩ : syracuseStep 4364081 = 3273061) B3273061
theorem B2909387 : Blo 1939435 2909387 := bstep (se 1 (by rfl) ⟨2182040, by rfl⟩ : syracuseStep 2909387 = 4364081) B4364081
theorem B1939591 : Blo 1939435 1939591 := bstep (se 1 (by rfl) ⟨1454693, by rfl⟩ : syracuseStep 1939591 = 2909387) B2909387
theorem B2182045 : Blo 1939435 2182045 := bbase (se 3 (by rfl) ⟨409133, by rfl⟩ : syracuseStep 2182045 = 818267) (by norm_num)
theorem B2909393 : Blo 1939435 2909393 := bstep (se 2 (by rfl) ⟨1091022, by rfl⟩ : syracuseStep 2909393 = 2182045) B2182045
theorem B1939595 : Blo 1939435 1939595 := bstep (se 1 (by rfl) ⟨1454696, by rfl⟩ : syracuseStep 1939595 = 2909393) B2909393
theorem B6546149 : Blo 1939435 6546149 := bbase (se 4 (by rfl) ⟨613701, by rfl⟩ : syracuseStep 6546149 = 1227403) (by norm_num)
theorem B4364099 : Blo 1939435 4364099 := bstep (se 1 (by rfl) ⟨3273074, by rfl⟩ : syracuseStep 4364099 = 6546149) B6546149
theorem B2909399 : Blo 1939435 2909399 := bstep (se 1 (by rfl) ⟨2182049, by rfl⟩ : syracuseStep 2909399 = 4364099) B4364099
theorem B1939599 : Blo 1939435 1939599 := bstep (se 1 (by rfl) ⟨1454699, by rfl⟩ : syracuseStep 1939599 = 2909399) B2909399
theorem B2909405 : Blo 1939435 2909405 := bbase (se 3 (by rfl) ⟨545513, by rfl⟩ : syracuseStep 2909405 = 1091027) (by norm_num)
theorem B1939603 : Blo 1939435 1939603 := bstep (se 1 (by rfl) ⟨1454702, by rfl⟩ : syracuseStep 1939603 = 2909405) B2909405
theorem B4364117 : Blo 1939435 4364117 := bbase (se 9 (by rfl) ⟨12785, by rfl⟩ : syracuseStep 4364117 = 25571) (by norm_num)
theorem B2909411 : Blo 1939435 2909411 := bstep (se 1 (by rfl) ⟨2182058, by rfl⟩ : syracuseStep 2909411 = 4364117) B4364117
theorem B1939607 : Blo 1939435 1939607 := bstep (se 1 (by rfl) ⟨1454705, by rfl⟩ : syracuseStep 1939607 = 2909411) B2909411
theorem B5523349 : Blo 1939435 5523349 := bbase (se 6 (by rfl) ⟨129453, by rfl⟩ : syracuseStep 5523349 = 258907) (by norm_num)
theorem B7364465 : Blo 1939435 7364465 := bstep (se 2 (by rfl) ⟨2761674, by rfl⟩ : syracuseStep 7364465 = 5523349) B5523349
theorem B4909643 : Blo 1939435 4909643 := bstep (se 1 (by rfl) ⟨3682232, by rfl⟩ : syracuseStep 4909643 = 7364465) B7364465
theorem B3273095 : Blo 1939435 3273095 := bstep (se 1 (by rfl) ⟨2454821, by rfl⟩ : syracuseStep 3273095 = 4909643) B4909643
theorem B2182063 : Blo 1939435 2182063 := bstep (se 1 (by rfl) ⟨1636547, by rfl⟩ : syracuseStep 2182063 = 3273095) B3273095
theorem B2909417 : Blo 1939435 2909417 := bstep (se 2 (by rfl) ⟨1091031, by rfl⟩ : syracuseStep 2909417 = 2182063) B2182063
theorem B1939611 : Blo 1939435 1939611 := bstep (se 1 (by rfl) ⟨1454708, by rfl⟩ : syracuseStep 1939611 = 2909417) B2909417
theorem B7566805 : Blo 1939435 7566805 := bbase (se 7 (by rfl) ⟨88673, by rfl⟩ : syracuseStep 7566805 = 177347) (by norm_num)
theorem B10089073 : Blo 1939435 10089073 := bstep (se 2 (by rfl) ⟨3783402, by rfl⟩ : syracuseStep 10089073 = 7566805) B7566805
theorem B13452097 : Blo 1939435 13452097 := bstep (se 2 (by rfl) ⟨5044536, by rfl⟩ : syracuseStep 13452097 = 10089073) B10089073
theorem B17936129 : Blo 1939435 17936129 := bstep (se 2 (by rfl) ⟨6726048, by rfl⟩ : syracuseStep 17936129 = 13452097) B13452097
theorem B11957419 : Blo 1939435 11957419 := bstep (se 1 (by rfl) ⟨8968064, by rfl⟩ : syracuseStep 11957419 = 17936129) B17936129
theorem B15943225 : Blo 1939435 15943225 := bstep (se 2 (by rfl) ⟨5978709, by rfl⟩ : syracuseStep 15943225 = 11957419) B11957419
theorem B21257633 : Blo 1939435 21257633 := bstep (se 2 (by rfl) ⟨7971612, by rfl⟩ : syracuseStep 21257633 = 15943225) B15943225
theorem B14171755 : Blo 1939435 14171755 := bstep (se 1 (by rfl) ⟨10628816, by rfl⟩ : syracuseStep 14171755 = 21257633) B21257633
theorem B18895673 : Blo 1939435 18895673 := bstep (se 2 (by rfl) ⟨7085877, by rfl⟩ : syracuseStep 18895673 = 14171755) B14171755
theorem B12597115 : Blo 1939435 12597115 := bstep (se 1 (by rfl) ⟨9447836, by rfl⟩ : syracuseStep 12597115 = 18895673) B18895673
theorem B16796153 : Blo 1939435 16796153 := bstep (se 2 (by rfl) ⟨6298557, by rfl⟩ : syracuseStep 16796153 = 12597115) B12597115
theorem B11197435 : Blo 1939435 11197435 := bstep (se 1 (by rfl) ⟨8398076, by rfl⟩ : syracuseStep 11197435 = 16796153) B16796153
theorem B14929913 : Blo 1939435 14929913 := bstep (se 2 (by rfl) ⟨5598717, by rfl⟩ : syracuseStep 14929913 = 11197435) B11197435
theorem B9953275 : Blo 1939435 9953275 := bstep (se 1 (by rfl) ⟨7464956, by rfl⟩ : syracuseStep 9953275 = 14929913) B14929913
theorem B13271033 : Blo 1939435 13271033 := bstep (se 2 (by rfl) ⟨4976637, by rfl⟩ : syracuseStep 13271033 = 9953275) B9953275
theorem B8847355 : Blo 1939435 8847355 := bstep (se 1 (by rfl) ⟨6635516, by rfl⟩ : syracuseStep 8847355 = 13271033) B13271033
theorem B11796473 : Blo 1939435 11796473 := bstep (se 2 (by rfl) ⟨4423677, by rfl⟩ : syracuseStep 11796473 = 8847355) B8847355
theorem B31457261 : Blo 1939435 31457261 := bstep (se 3 (by rfl) ⟨5898236, by rfl⟩ : syracuseStep 31457261 = 11796473) B11796473
theorem B83886029 : Blo 1939435 83886029 := bstep (se 3 (by rfl) ⟨15728630, by rfl⟩ : syracuseStep 83886029 = 31457261) B31457261
theorem B55924019 : Blo 1939435 55924019 := bstep (se 1 (by rfl) ⟨41943014, by rfl⟩ : syracuseStep 55924019 = 83886029) B83886029
theorem B37282679 : Blo 1939435 37282679 := bstep (se 1 (by rfl) ⟨27962009, by rfl⟩ : syracuseStep 37282679 = 55924019) B55924019
theorem B24855119 : Blo 1939435 24855119 := bstep (se 1 (by rfl) ⟨18641339, by rfl⟩ : syracuseStep 24855119 = 37282679) B37282679
theorem B16570079 : Blo 1939435 16570079 := bstep (se 1 (by rfl) ⟨12427559, by rfl⟩ : syracuseStep 16570079 = 24855119) B24855119
theorem B11046719 : Blo 1939435 11046719 := bstep (se 1 (by rfl) ⟨8285039, by rfl⟩ : syracuseStep 11046719 = 16570079) B16570079
theorem B7364479 : Blo 1939435 7364479 := bstep (se 1 (by rfl) ⟨5523359, by rfl⟩ : syracuseStep 7364479 = 11046719) B11046719
theorem B9819305 : Blo 1939435 9819305 := bstep (se 2 (by rfl) ⟨3682239, by rfl⟩ : syracuseStep 9819305 = 7364479) B7364479
theorem B6546203 : Blo 1939435 6546203 := bstep (se 1 (by rfl) ⟨4909652, by rfl⟩ : syracuseStep 6546203 = 9819305) B9819305
theorem B4364135 : Blo 1939435 4364135 := bstep (se 1 (by rfl) ⟨3273101, by rfl⟩ : syracuseStep 4364135 = 6546203) B6546203
theorem B2909423 : Blo 1939435 2909423 := bstep (se 1 (by rfl) ⟨2182067, by rfl⟩ : syracuseStep 2909423 = 4364135) B4364135
theorem B1939615 : Blo 1939435 1939615 := bstep (se 1 (by rfl) ⟨1454711, by rfl⟩ : syracuseStep 1939615 = 2909423) B2909423
theorem B2909429 : Blo 1939435 2909429 := bbase (se 5 (by rfl) ⟨136379, by rfl⟩ : syracuseStep 2909429 = 272759) (by norm_num)
theorem B1939619 : Blo 1939435 1939619 := bstep (se 1 (by rfl) ⟨1454714, by rfl⟩ : syracuseStep 1939619 = 2909429) B2909429
theorem B6990533 : Blo 1939435 6990533 := bbase (se 4 (by rfl) ⟨655362, by rfl⟩ : syracuseStep 6990533 = 1310725) (by norm_num)
theorem B4660355 : Blo 1939435 4660355 := bstep (se 1 (by rfl) ⟨3495266, by rfl⟩ : syracuseStep 4660355 = 6990533) B6990533
theorem B12427613 : Blo 1939435 12427613 := bstep (se 3 (by rfl) ⟨2330177, by rfl⟩ : syracuseStep 12427613 = 4660355) B4660355
theorem B8285075 : Blo 1939435 8285075 := bstep (se 1 (by rfl) ⟨6213806, by rfl⟩ : syracuseStep 8285075 = 12427613) B12427613
theorem B5523383 : Blo 1939435 5523383 := bstep (se 1 (by rfl) ⟨4142537, by rfl⟩ : syracuseStep 5523383 = 8285075) B8285075
theorem B3682255 : Blo 1939435 3682255 := bstep (se 1 (by rfl) ⟨2761691, by rfl⟩ : syracuseStep 3682255 = 5523383) B5523383
theorem B4909673 : Blo 1939435 4909673 := bstep (se 2 (by rfl) ⟨1841127, by rfl⟩ : syracuseStep 4909673 = 3682255) B3682255
theorem B3273115 : Blo 1939435 3273115 := bstep (se 1 (by rfl) ⟨2454836, by rfl⟩ : syracuseStep 3273115 = 4909673) B4909673
theorem B4364153 : Blo 1939435 4364153 := bstep (se 2 (by rfl) ⟨1636557, by rfl⟩ : syracuseStep 4364153 = 3273115) B3273115
theorem B2909435 : Blo 1939435 2909435 := bstep (se 1 (by rfl) ⟨2182076, by rfl⟩ : syracuseStep 2909435 = 4364153) B4364153
theorem B1939623 : Blo 1939435 1939623 := bstep (se 1 (by rfl) ⟨1454717, by rfl⟩ : syracuseStep 1939623 = 2909435) B2909435
theorem B2182081 : Blo 1939435 2182081 := bbase (se 2 (by rfl) ⟨818280, by rfl⟩ : syracuseStep 2182081 = 1636561) (by norm_num)
theorem B2909441 : Blo 1939435 2909441 := bstep (se 2 (by rfl) ⟨1091040, by rfl⟩ : syracuseStep 2909441 = 2182081) B2182081
theorem B1939627 : Blo 1939435 1939627 := bstep (se 1 (by rfl) ⟨1454720, by rfl⟩ : syracuseStep 1939627 = 2909441) B2909441
theorem B4909693 : Blo 1939435 4909693 := bbase (se 3 (by rfl) ⟨920567, by rfl⟩ : syracuseStep 4909693 = 1841135) (by norm_num)
theorem B6546257 : Blo 1939435 6546257 := bstep (se 2 (by rfl) ⟨2454846, by rfl⟩ : syracuseStep 6546257 = 4909693) B4909693
theorem B4364171 : Blo 1939435 4364171 := bstep (se 1 (by rfl) ⟨3273128, by rfl⟩ : syracuseStep 4364171 = 6546257) B6546257
theorem B2909447 : Blo 1939435 2909447 := bstep (se 1 (by rfl) ⟨2182085, by rfl⟩ : syracuseStep 2909447 = 4364171) B4364171
theorem B1939631 : Blo 1939435 1939631 := bstep (se 1 (by rfl) ⟨1454723, by rfl⟩ : syracuseStep 1939631 = 2909447) B2909447
theorem B2909453 : Blo 1939435 2909453 := bbase (se 3 (by rfl) ⟨545522, by rfl⟩ : syracuseStep 2909453 = 1091045) (by norm_num)
theorem B1939635 : Blo 1939435 1939635 := bstep (se 1 (by rfl) ⟨1454726, by rfl⟩ : syracuseStep 1939635 = 2909453) B2909453
theorem B4364189 : Blo 1939435 4364189 := bbase (se 3 (by rfl) ⟨818285, by rfl⟩ : syracuseStep 4364189 = 1636571) (by norm_num)
theorem B2909459 : Blo 1939435 2909459 := bstep (se 1 (by rfl) ⟨2182094, by rfl⟩ : syracuseStep 2909459 = 4364189) B4364189
theorem B1939639 : Blo 1939435 1939639 := bstep (se 1 (by rfl) ⟨1454729, by rfl⟩ : syracuseStep 1939639 = 2909459) B2909459
theorem B3273149 : Blo 1939435 3273149 := bbase (se 3 (by rfl) ⟨613715, by rfl⟩ : syracuseStep 3273149 = 1227431) (by norm_num)
theorem B2182099 : Blo 1939435 2182099 := bstep (se 1 (by rfl) ⟨1636574, by rfl⟩ : syracuseStep 2182099 = 3273149) B3273149
theorem B2909465 : Blo 1939435 2909465 := bstep (se 2 (by rfl) ⟨1091049, by rfl⟩ : syracuseStep 2909465 = 2182099) B2182099
theorem B1939643 : Blo 1939435 1939643 := bstep (se 1 (by rfl) ⟨1454732, by rfl⟩ : syracuseStep 1939643 = 2909465) B2909465
theorem B11046901 : Blo 1939435 11046901 := bbase (se 5 (by rfl) ⟨517823, by rfl⟩ : syracuseStep 11046901 = 1035647) (by norm_num)
theorem B14729201 : Blo 1939435 14729201 := bstep (se 2 (by rfl) ⟨5523450, by rfl⟩ : syracuseStep 14729201 = 11046901) B11046901
theorem B9819467 : Blo 1939435 9819467 := bstep (se 1 (by rfl) ⟨7364600, by rfl⟩ : syracuseStep 9819467 = 14729201) B14729201
theorem B6546311 : Blo 1939435 6546311 := bstep (se 1 (by rfl) ⟨4909733, by rfl⟩ : syracuseStep 6546311 = 9819467) B9819467
theorem B4364207 : Blo 1939435 4364207 := bstep (se 1 (by rfl) ⟨3273155, by rfl⟩ : syracuseStep 4364207 = 6546311) B6546311
theorem B2909471 : Blo 1939435 2909471 := bstep (se 1 (by rfl) ⟨2182103, by rfl⟩ : syracuseStep 2909471 = 4364207) B4364207
theorem B1939647 : Blo 1939435 1939647 := bstep (se 1 (by rfl) ⟨1454735, by rfl⟩ : syracuseStep 1939647 = 2909471) B2909471
theorem B2909477 : Blo 1939435 2909477 := bbase (se 4 (by rfl) ⟨272763, by rfl⟩ : syracuseStep 2909477 = 545527) (by norm_num)
theorem B1939651 : Blo 1939435 1939651 := bstep (se 1 (by rfl) ⟨1454738, by rfl⟩ : syracuseStep 1939651 = 2909477) B2909477
theorem B2454877 : Blo 1939435 2454877 := bbase (se 3 (by rfl) ⟨460289, by rfl⟩ : syracuseStep 2454877 = 920579) (by norm_num)
theorem B3273169 : Blo 1939435 3273169 := bstep (se 2 (by rfl) ⟨1227438, by rfl⟩ : syracuseStep 3273169 = 2454877) B2454877
theorem B4364225 : Blo 1939435 4364225 := bstep (se 2 (by rfl) ⟨1636584, by rfl⟩ : syracuseStep 4364225 = 3273169) B3273169
theorem B2909483 : Blo 1939435 2909483 := bstep (se 1 (by rfl) ⟨2182112, by rfl⟩ : syracuseStep 2909483 = 4364225) B4364225
theorem B1939655 : Blo 1939435 1939655 := bstep (se 1 (by rfl) ⟨1454741, by rfl⟩ : syracuseStep 1939655 = 2909483) B2909483
theorem B2182117 : Blo 1939435 2182117 := bbase (se 4 (by rfl) ⟨204573, by rfl⟩ : syracuseStep 2182117 = 409147) (by norm_num)
theorem B2909489 : Blo 1939435 2909489 := bstep (se 2 (by rfl) ⟨1091058, by rfl⟩ : syracuseStep 2909489 = 2182117) B2182117
theorem B1939659 : Blo 1939435 1939659 := bstep (se 1 (by rfl) ⟨1454744, by rfl⟩ : syracuseStep 1939659 = 2909489) B2909489
theorem B9953525 : Blo 1939435 9953525 := bbase (se 5 (by rfl) ⟨466571, by rfl⟩ : syracuseStep 9953525 = 933143) (by norm_num)
theorem B6635683 : Blo 1939435 6635683 := bstep (se 1 (by rfl) ⟨4976762, by rfl⟩ : syracuseStep 6635683 = 9953525) B9953525
theorem B8847577 : Blo 1939435 8847577 := bstep (se 2 (by rfl) ⟨3317841, by rfl⟩ : syracuseStep 8847577 = 6635683) B6635683
theorem B11796769 : Blo 1939435 11796769 := bstep (se 2 (by rfl) ⟨4423788, by rfl⟩ : syracuseStep 11796769 = 8847577) B8847577
theorem B15729025 : Blo 1939435 15729025 := bstep (se 2 (by rfl) ⟨5898384, by rfl⟩ : syracuseStep 15729025 = 11796769) B11796769
theorem B20972033 : Blo 1939435 20972033 := bstep (se 2 (by rfl) ⟨7864512, by rfl⟩ : syracuseStep 20972033 = 15729025) B15729025
theorem B13981355 : Blo 1939435 13981355 := bstep (se 1 (by rfl) ⟨10486016, by rfl⟩ : syracuseStep 13981355 = 20972033) B20972033
theorem B9320903 : Blo 1939435 9320903 := bstep (se 1 (by rfl) ⟨6990677, by rfl⟩ : syracuseStep 9320903 = 13981355) B13981355
theorem B6213935 : Blo 1939435 6213935 := bstep (se 1 (by rfl) ⟨4660451, by rfl⟩ : syracuseStep 6213935 = 9320903) B9320903
theorem B4142623 : Blo 1939435 4142623 := bstep (se 1 (by rfl) ⟨3106967, by rfl⟩ : syracuseStep 4142623 = 6213935) B6213935
theorem B5523497 : Blo 1939435 5523497 := bstep (se 2 (by rfl) ⟨2071311, by rfl⟩ : syracuseStep 5523497 = 4142623) B4142623
theorem B3682331 : Blo 1939435 3682331 := bstep (se 1 (by rfl) ⟨2761748, by rfl⟩ : syracuseStep 3682331 = 5523497) B5523497
theorem B2454887 : Blo 1939435 2454887 := bstep (se 1 (by rfl) ⟨1841165, by rfl⟩ : syracuseStep 2454887 = 3682331) B3682331
theorem B6546365 : Blo 1939435 6546365 := bstep (se 3 (by rfl) ⟨1227443, by rfl⟩ : syracuseStep 6546365 = 2454887) B2454887
theorem B4364243 : Blo 1939435 4364243 := bstep (se 1 (by rfl) ⟨3273182, by rfl⟩ : syracuseStep 4364243 = 6546365) B6546365
theorem B2909495 : Blo 1939435 2909495 := bstep (se 1 (by rfl) ⟨2182121, by rfl⟩ : syracuseStep 2909495 = 4364243) B4364243
theorem B1939663 : Blo 1939435 1939663 := bstep (se 1 (by rfl) ⟨1454747, by rfl⟩ : syracuseStep 1939663 = 2909495) B2909495
theorem B2909501 : Blo 1939435 2909501 := bbase (se 3 (by rfl) ⟨545531, by rfl⟩ : syracuseStep 2909501 = 1091063) (by norm_num)
theorem B1939667 : Blo 1939435 1939667 := bstep (se 1 (by rfl) ⟨1454750, by rfl⟩ : syracuseStep 1939667 = 2909501) B2909501
theorem B4364261 : Blo 1939435 4364261 := bbase (se 4 (by rfl) ⟨409149, by rfl⟩ : syracuseStep 4364261 = 818299) (by norm_num)
theorem B2909507 : Blo 1939435 2909507 := bstep (se 1 (by rfl) ⟨2182130, by rfl⟩ : syracuseStep 2909507 = 4364261) B4364261
theorem B1939671 : Blo 1939435 1939671 := bstep (se 1 (by rfl) ⟨1454753, by rfl⟩ : syracuseStep 1939671 = 2909507) B2909507
theorem B4909805 : Blo 1939435 4909805 := bbase (se 3 (by rfl) ⟨920588, by rfl⟩ : syracuseStep 4909805 = 1841177) (by norm_num)
theorem B3273203 : Blo 1939435 3273203 := bstep (se 1 (by rfl) ⟨2454902, by rfl⟩ : syracuseStep 3273203 = 4909805) B4909805
theorem B2182135 : Blo 1939435 2182135 := bstep (se 1 (by rfl) ⟨1636601, by rfl⟩ : syracuseStep 2182135 = 3273203) B3273203
theorem B2909513 : Blo 1939435 2909513 := bstep (se 2 (by rfl) ⟨1091067, by rfl⟩ : syracuseStep 2909513 = 2182135) B2182135
theorem B1939675 : Blo 1939435 1939675 := bstep (se 1 (by rfl) ⟨1454756, by rfl⟩ : syracuseStep 1939675 = 2909513) B2909513
theorem B2330245 : Blo 1939435 2330245 := bbase (se 4 (by rfl) ⟨218460, by rfl⟩ : syracuseStep 2330245 = 436921) (by norm_num)
theorem B3106993 : Blo 1939435 3106993 := bstep (se 2 (by rfl) ⟨1165122, by rfl⟩ : syracuseStep 3106993 = 2330245) B2330245
theorem B4142657 : Blo 1939435 4142657 := bstep (se 2 (by rfl) ⟨1553496, by rfl⟩ : syracuseStep 4142657 = 3106993) B3106993
theorem B2761771 : Blo 1939435 2761771 := bstep (se 1 (by rfl) ⟨2071328, by rfl⟩ : syracuseStep 2761771 = 4142657) B4142657
theorem B3682361 : Blo 1939435 3682361 := bstep (se 2 (by rfl) ⟨1380885, by rfl⟩ : syracuseStep 3682361 = 2761771) B2761771
theorem B9819629 : Blo 1939435 9819629 := bstep (se 3 (by rfl) ⟨1841180, by rfl⟩ : syracuseStep 9819629 = 3682361) B3682361
theorem B6546419 : Blo 1939435 6546419 := bstep (se 1 (by rfl) ⟨4909814, by rfl⟩ : syracuseStep 6546419 = 9819629) B9819629
theorem B4364279 : Blo 1939435 4364279 := bstep (se 1 (by rfl) ⟨3273209, by rfl⟩ : syracuseStep 4364279 = 6546419) B6546419
theorem B2909519 : Blo 1939435 2909519 := bstep (se 1 (by rfl) ⟨2182139, by rfl⟩ : syracuseStep 2909519 = 4364279) B4364279
theorem B1939679 : Blo 1939435 1939679 := bstep (se 1 (by rfl) ⟨1454759, by rfl⟩ : syracuseStep 1939679 = 2909519) B2909519
theorem B2909525 : Blo 1939435 2909525 := bbase (se 12 (by rfl) ⟨1065, by rfl⟩ : syracuseStep 2909525 = 2131) (by norm_num)
theorem B1939683 : Blo 1939435 1939683 := bstep (se 1 (by rfl) ⟨1454762, by rfl⟩ : syracuseStep 1939683 = 2909525) B2909525
theorem B2071337 : Blo 1939435 2071337 := bbase (se 2 (by rfl) ⟨776751, by rfl⟩ : syracuseStep 2071337 = 1553503) (by norm_num)
theorem B5523565 : Blo 1939435 5523565 := bstep (se 3 (by rfl) ⟨1035668, by rfl⟩ : syracuseStep 5523565 = 2071337) B2071337
theorem B7364753 : Blo 1939435 7364753 := bstep (se 2 (by rfl) ⟨2761782, by rfl⟩ : syracuseStep 7364753 = 5523565) B5523565
theorem B4909835 : Blo 1939435 4909835 := bstep (se 1 (by rfl) ⟨3682376, by rfl⟩ : syracuseStep 4909835 = 7364753) B7364753
theorem B3273223 : Blo 1939435 3273223 := bstep (se 1 (by rfl) ⟨2454917, by rfl⟩ : syracuseStep 3273223 = 4909835) B4909835
theorem B4364297 : Blo 1939435 4364297 := bstep (se 2 (by rfl) ⟨1636611, by rfl⟩ : syracuseStep 4364297 = 3273223) B3273223
theorem B2909531 : Blo 1939435 2909531 := bstep (se 1 (by rfl) ⟨2182148, by rfl⟩ : syracuseStep 2909531 = 4364297) B4364297
theorem B1939687 : Blo 1939435 1939687 := bstep (se 1 (by rfl) ⟨1454765, by rfl⟩ : syracuseStep 1939687 = 2909531) B2909531
theorem B2182153 : Blo 1939435 2182153 := bbase (se 2 (by rfl) ⟨818307, by rfl⟩ : syracuseStep 2182153 = 1636615) (by norm_num)
theorem B2909537 : Blo 1939435 2909537 := bstep (se 2 (by rfl) ⟨1091076, by rfl⟩ : syracuseStep 2909537 = 2182153) B2182153
theorem B1939691 : Blo 1939435 1939691 := bstep (se 1 (by rfl) ⟨1454768, by rfl⟩ : syracuseStep 1939691 = 2909537) B2909537
theorem B22395797 : Blo 1939435 22395797 := bbase (se 6 (by rfl) ⟨524901, by rfl⟩ : syracuseStep 22395797 = 1049803) (by norm_num)
theorem B14930531 : Blo 1939435 14930531 := bstep (se 1 (by rfl) ⟨11197898, by rfl⟩ : syracuseStep 14930531 = 22395797) B22395797
theorem B9953687 : Blo 1939435 9953687 := bstep (se 1 (by rfl) ⟨7465265, by rfl⟩ : syracuseStep 9953687 = 14930531) B14930531
theorem B6635791 : Blo 1939435 6635791 := bstep (se 1 (by rfl) ⟨4976843, by rfl⟩ : syracuseStep 6635791 = 9953687) B9953687
theorem B8847721 : Blo 1939435 8847721 := bstep (se 2 (by rfl) ⟨3317895, by rfl⟩ : syracuseStep 8847721 = 6635791) B6635791
theorem B11796961 : Blo 1939435 11796961 := bstep (se 2 (by rfl) ⟨4423860, by rfl⟩ : syracuseStep 11796961 = 8847721) B8847721
theorem B15729281 : Blo 1939435 15729281 := bstep (se 2 (by rfl) ⟨5898480, by rfl⟩ : syracuseStep 15729281 = 11796961) B11796961
theorem B10486187 : Blo 1939435 10486187 := bstep (se 1 (by rfl) ⟨7864640, by rfl⟩ : syracuseStep 10486187 = 15729281) B15729281
theorem B6990791 : Blo 1939435 6990791 := bstep (se 1 (by rfl) ⟨5243093, by rfl⟩ : syracuseStep 6990791 = 10486187) B10486187
theorem B18642109 : Blo 1939435 18642109 := bstep (se 3 (by rfl) ⟨3495395, by rfl⟩ : syracuseStep 18642109 = 6990791) B6990791
theorem B24856145 : Blo 1939435 24856145 := bstep (se 2 (by rfl) ⟨9321054, by rfl⟩ : syracuseStep 24856145 = 18642109) B18642109
theorem B16570763 : Blo 1939435 16570763 := bstep (se 1 (by rfl) ⟨12428072, by rfl⟩ : syracuseStep 16570763 = 24856145) B24856145
theorem B11047175 : Blo 1939435 11047175 := bstep (se 1 (by rfl) ⟨8285381, by rfl⟩ : syracuseStep 11047175 = 16570763) B16570763
theorem B7364783 : Blo 1939435 7364783 := bstep (se 1 (by rfl) ⟨5523587, by rfl⟩ : syracuseStep 7364783 = 11047175) B11047175
theorem B4909855 : Blo 1939435 4909855 := bstep (se 1 (by rfl) ⟨3682391, by rfl⟩ : syracuseStep 4909855 = 7364783) B7364783
theorem B6546473 : Blo 1939435 6546473 := bstep (se 2 (by rfl) ⟨2454927, by rfl⟩ : syracuseStep 6546473 = 4909855) B4909855
theorem B4364315 : Blo 1939435 4364315 := bstep (se 1 (by rfl) ⟨3273236, by rfl⟩ : syracuseStep 4364315 = 6546473) B6546473
theorem B2909543 : Blo 1939435 2909543 := bstep (se 1 (by rfl) ⟨2182157, by rfl⟩ : syracuseStep 2909543 = 4364315) B4364315
theorem B1939695 : Blo 1939435 1939695 := bstep (se 1 (by rfl) ⟨1454771, by rfl⟩ : syracuseStep 1939695 = 2909543) B2909543
theorem B2909549 : Blo 1939435 2909549 := bbase (se 3 (by rfl) ⟨545540, by rfl⟩ : syracuseStep 2909549 = 1091081) (by norm_num)
theorem B1939699 : Blo 1939435 1939699 := bstep (se 1 (by rfl) ⟨1454774, by rfl⟩ : syracuseStep 1939699 = 2909549) B2909549
theorem B4364333 : Blo 1939435 4364333 := bbase (se 3 (by rfl) ⟨818312, by rfl⟩ : syracuseStep 4364333 = 1636625) (by norm_num)
theorem B2909555 : Blo 1939435 2909555 := bstep (se 1 (by rfl) ⟨2182166, by rfl⟩ : syracuseStep 2909555 = 4364333) B4364333
theorem B1939703 : Blo 1939435 1939703 := bstep (se 1 (by rfl) ⟨1454777, by rfl⟩ : syracuseStep 1939703 = 2909555) B2909555
theorem B4040381 : Blo 1939435 4040381 := bbase (se 3 (by rfl) ⟨757571, by rfl⟩ : syracuseStep 4040381 = 1515143) (by norm_num)
theorem B2693587 : Blo 1939435 2693587 := bstep (se 1 (by rfl) ⟨2020190, by rfl⟩ : syracuseStep 2693587 = 4040381) B4040381
theorem B3591449 : Blo 1939435 3591449 := bstep (se 2 (by rfl) ⟨1346793, by rfl⟩ : syracuseStep 3591449 = 2693587) B2693587
theorem B2394299 : Blo 1939435 2394299 := bstep (se 1 (by rfl) ⟨1795724, by rfl⟩ : syracuseStep 2394299 = 3591449) B3591449
theorem B6384797 : Blo 1939435 6384797 := bstep (se 3 (by rfl) ⟨1197149, by rfl⟩ : syracuseStep 6384797 = 2394299) B2394299
theorem B4256531 : Blo 1939435 4256531 := bstep (se 1 (by rfl) ⟨3192398, by rfl⟩ : syracuseStep 4256531 = 6384797) B6384797
theorem B2837687 : Blo 1939435 2837687 := bstep (se 1 (by rfl) ⟨2128265, by rfl⟩ : syracuseStep 2837687 = 4256531) B4256531
theorem B7567165 : Blo 1939435 7567165 := bstep (se 3 (by rfl) ⟨1418843, by rfl⟩ : syracuseStep 7567165 = 2837687) B2837687
theorem B40358213 : Blo 1939435 40358213 := bstep (se 4 (by rfl) ⟨3783582, by rfl⟩ : syracuseStep 40358213 = 7567165) B7567165
theorem B26905475 : Blo 1939435 26905475 := bstep (se 1 (by rfl) ⟨20179106, by rfl⟩ : syracuseStep 26905475 = 40358213) B40358213
theorem B17936983 : Blo 1939435 17936983 := bstep (se 1 (by rfl) ⟨13452737, by rfl⟩ : syracuseStep 17936983 = 26905475) B26905475
theorem B95663909 : Blo 1939435 95663909 := bstep (se 4 (by rfl) ⟨8968491, by rfl⟩ : syracuseStep 95663909 = 17936983) B17936983
theorem B63775939 : Blo 1939435 63775939 := bstep (se 1 (by rfl) ⟨47831954, by rfl⟩ : syracuseStep 63775939 = 95663909) B95663909
theorem B85034585 : Blo 1939435 85034585 := bstep (se 2 (by rfl) ⟨31887969, by rfl⟩ : syracuseStep 85034585 = 63775939) B63775939
theorem B56689723 : Blo 1939435 56689723 := bstep (se 1 (by rfl) ⟨42517292, by rfl⟩ : syracuseStep 56689723 = 85034585) B85034585
theorem B75586297 : Blo 1939435 75586297 := bstep (se 2 (by rfl) ⟨28344861, by rfl⟩ : syracuseStep 75586297 = 56689723) B56689723
theorem B100781729 : Blo 1939435 100781729 := bstep (se 2 (by rfl) ⟨37793148, by rfl⟩ : syracuseStep 100781729 = 75586297) B75586297
theorem B67187819 : Blo 1939435 67187819 := bstep (se 1 (by rfl) ⟨50390864, by rfl⟩ : syracuseStep 67187819 = 100781729) B100781729
theorem B44791879 : Blo 1939435 44791879 := bstep (se 1 (by rfl) ⟨33593909, by rfl⟩ : syracuseStep 44791879 = 67187819) B67187819
theorem B59722505 : Blo 1939435 59722505 := bstep (se 2 (by rfl) ⟨22395939, by rfl⟩ : syracuseStep 59722505 = 44791879) B44791879
theorem B39815003 : Blo 1939435 39815003 := bstep (se 1 (by rfl) ⟨29861252, by rfl⟩ : syracuseStep 39815003 = 59722505) B59722505
theorem B26543335 : Blo 1939435 26543335 := bstep (se 1 (by rfl) ⟨19907501, by rfl⟩ : syracuseStep 26543335 = 39815003) B39815003
theorem B35391113 : Blo 1939435 35391113 := bstep (se 2 (by rfl) ⟨13271667, by rfl⟩ : syracuseStep 35391113 = 26543335) B26543335
theorem B23594075 : Blo 1939435 23594075 := bstep (se 1 (by rfl) ⟨17695556, by rfl⟩ : syracuseStep 23594075 = 35391113) B35391113
theorem B15729383 : Blo 1939435 15729383 := bstep (se 1 (by rfl) ⟨11797037, by rfl⟩ : syracuseStep 15729383 = 23594075) B23594075
theorem B10486255 : Blo 1939435 10486255 := bstep (se 1 (by rfl) ⟨7864691, by rfl⟩ : syracuseStep 10486255 = 15729383) B15729383
theorem B13981673 : Blo 1939435 13981673 := bstep (se 2 (by rfl) ⟨5243127, by rfl⟩ : syracuseStep 13981673 = 10486255) B10486255
theorem B9321115 : Blo 1939435 9321115 := bstep (se 1 (by rfl) ⟨6990836, by rfl⟩ : syracuseStep 9321115 = 13981673) B13981673
theorem B12428153 : Blo 1939435 12428153 := bstep (se 2 (by rfl) ⟨4660557, by rfl⟩ : syracuseStep 12428153 = 9321115) B9321115
theorem B8285435 : Blo 1939435 8285435 := bstep (se 1 (by rfl) ⟨6214076, by rfl⟩ : syracuseStep 8285435 = 12428153) B12428153
theorem B5523623 : Blo 1939435 5523623 := bstep (se 1 (by rfl) ⟨4142717, by rfl⟩ : syracuseStep 5523623 = 8285435) B8285435
theorem B3682415 : Blo 1939435 3682415 := bstep (se 1 (by rfl) ⟨2761811, by rfl⟩ : syracuseStep 3682415 = 5523623) B5523623
theorem B2454943 : Blo 1939435 2454943 := bstep (se 1 (by rfl) ⟨1841207, by rfl⟩ : syracuseStep 2454943 = 3682415) B3682415
theorem B3273257 : Blo 1939435 3273257 := bstep (se 2 (by rfl) ⟨1227471, by rfl⟩ : syracuseStep 3273257 = 2454943) B2454943
theorem B2182171 : Blo 1939435 2182171 := bstep (se 1 (by rfl) ⟨1636628, by rfl⟩ : syracuseStep 2182171 = 3273257) B3273257
theorem B2909561 : Blo 1939435 2909561 := bstep (se 2 (by rfl) ⟨1091085, by rfl⟩ : syracuseStep 2909561 = 2182171) B2182171
theorem B1939707 : Blo 1939435 1939707 := bstep (se 1 (by rfl) ⟨1454780, by rfl⟩ : syracuseStep 1939707 = 2909561) B2909561
theorem B4976885 : Blo 1939435 4976885 := bbase (se 5 (by rfl) ⟨233291, by rfl⟩ : syracuseStep 4976885 = 466583) (by norm_num)
theorem B3317923 : Blo 1939435 3317923 := bstep (se 1 (by rfl) ⟨2488442, by rfl⟩ : syracuseStep 3317923 = 4976885) B4976885
theorem B4423897 : Blo 1939435 4423897 := bstep (se 2 (by rfl) ⟨1658961, by rfl⟩ : syracuseStep 4423897 = 3317923) B3317923
theorem B5898529 : Blo 1939435 5898529 := bstep (se 2 (by rfl) ⟨2211948, by rfl⟩ : syracuseStep 5898529 = 4423897) B4423897
theorem B7864705 : Blo 1939435 7864705 := bstep (se 2 (by rfl) ⟨2949264, by rfl⟩ : syracuseStep 7864705 = 5898529) B5898529
theorem B10486273 : Blo 1939435 10486273 := bstep (se 2 (by rfl) ⟨3932352, by rfl⟩ : syracuseStep 10486273 = 7864705) B7864705
theorem B13981697 : Blo 1939435 13981697 := bstep (se 2 (by rfl) ⟨5243136, by rfl⟩ : syracuseStep 13981697 = 10486273) B10486273
theorem B9321131 : Blo 1939435 9321131 := bstep (se 1 (by rfl) ⟨6990848, by rfl⟩ : syracuseStep 9321131 = 13981697) B13981697
theorem B6214087 : Blo 1939435 6214087 := bstep (se 1 (by rfl) ⟨4660565, by rfl⟩ : syracuseStep 6214087 = 9321131) B9321131
theorem B33141797 : Blo 1939435 33141797 := bstep (se 4 (by rfl) ⟨3107043, by rfl⟩ : syracuseStep 33141797 = 6214087) B6214087
theorem B22094531 : Blo 1939435 22094531 := bstep (se 1 (by rfl) ⟨16570898, by rfl⟩ : syracuseStep 22094531 = 33141797) B33141797
theorem B14729687 : Blo 1939435 14729687 := bstep (se 1 (by rfl) ⟨11047265, by rfl⟩ : syracuseStep 14729687 = 22094531) B22094531
theorem B9819791 : Blo 1939435 9819791 := bstep (se 1 (by rfl) ⟨7364843, by rfl⟩ : syracuseStep 9819791 = 14729687) B14729687
theorem B6546527 : Blo 1939435 6546527 := bstep (se 1 (by rfl) ⟨4909895, by rfl⟩ : syracuseStep 6546527 = 9819791) B9819791
theorem B4364351 : Blo 1939435 4364351 := bstep (se 1 (by rfl) ⟨3273263, by rfl⟩ : syracuseStep 4364351 = 6546527) B6546527
theorem B2909567 : Blo 1939435 2909567 := bstep (se 1 (by rfl) ⟨2182175, by rfl⟩ : syracuseStep 2909567 = 4364351) B4364351
theorem B1939711 : Blo 1939435 1939711 := bstep (se 1 (by rfl) ⟨1454783, by rfl⟩ : syracuseStep 1939711 = 2909567) B2909567
theorem B2909573 : Blo 1939435 2909573 := bbase (se 4 (by rfl) ⟨272772, by rfl⟩ : syracuseStep 2909573 = 545545) (by norm_num)
theorem B1939715 : Blo 1939435 1939715 := bstep (se 1 (by rfl) ⟨1454786, by rfl⟩ : syracuseStep 1939715 = 2909573) B2909573
theorem B3273277 : Blo 1939435 3273277 := bbase (se 3 (by rfl) ⟨613739, by rfl⟩ : syracuseStep 3273277 = 1227479) (by norm_num)
theorem B4364369 : Blo 1939435 4364369 := bstep (se 2 (by rfl) ⟨1636638, by rfl⟩ : syracuseStep 4364369 = 3273277) B3273277
theorem B2909579 : Blo 1939435 2909579 := bstep (se 1 (by rfl) ⟨2182184, by rfl⟩ : syracuseStep 2909579 = 4364369) B4364369
theorem B1939719 : Blo 1939435 1939719 := bstep (se 1 (by rfl) ⟨1454789, by rfl⟩ : syracuseStep 1939719 = 2909579) B2909579
theorem B2182189 : Blo 1939435 2182189 := bbase (se 3 (by rfl) ⟨409160, by rfl⟩ : syracuseStep 2182189 = 818321) (by norm_num)
theorem B2909585 : Blo 1939435 2909585 := bstep (se 2 (by rfl) ⟨1091094, by rfl⟩ : syracuseStep 2909585 = 2182189) B2182189
theorem B1939723 : Blo 1939435 1939723 := bstep (se 1 (by rfl) ⟨1454792, by rfl⟩ : syracuseStep 1939723 = 2909585) B2909585
theorem B6546581 : Blo 1939435 6546581 := bbase (se 6 (by rfl) ⟨153435, by rfl⟩ : syracuseStep 6546581 = 306871) (by norm_num)
theorem B4364387 : Blo 1939435 4364387 := bstep (se 1 (by rfl) ⟨3273290, by rfl⟩ : syracuseStep 4364387 = 6546581) B6546581
theorem B2909591 : Blo 1939435 2909591 := bstep (se 1 (by rfl) ⟨2182193, by rfl⟩ : syracuseStep 2909591 = 4364387) B4364387
theorem B1939727 : Blo 1939435 1939727 := bstep (se 1 (by rfl) ⟨1454795, by rfl⟩ : syracuseStep 1939727 = 2909591) B2909591
theorem B2909597 : Blo 1939435 2909597 := bbase (se 3 (by rfl) ⟨545549, by rfl⟩ : syracuseStep 2909597 = 1091099) (by norm_num)
theorem B1939731 : Blo 1939435 1939731 := bstep (se 1 (by rfl) ⟨1454798, by rfl⟩ : syracuseStep 1939731 = 2909597) B2909597
theorem B4364405 : Blo 1939435 4364405 := bbase (se 5 (by rfl) ⟨204581, by rfl⟩ : syracuseStep 4364405 = 409163) (by norm_num)
theorem B2909603 : Blo 1939435 2909603 := bstep (se 1 (by rfl) ⟨2182202, by rfl⟩ : syracuseStep 2909603 = 4364405) B4364405
theorem B1939735 : Blo 1939435 1939735 := bstep (se 1 (by rfl) ⟨1454801, by rfl⟩ : syracuseStep 1939735 = 2909603) B2909603
theorem B2330317 : Blo 1939435 2330317 := bbase (se 3 (by rfl) ⟨436934, by rfl⟩ : syracuseStep 2330317 = 873869) (by norm_num)
theorem B3107089 : Blo 1939435 3107089 := bstep (se 2 (by rfl) ⟨1165158, by rfl⟩ : syracuseStep 3107089 = 2330317) B2330317
theorem B16571141 : Blo 1939435 16571141 := bstep (se 4 (by rfl) ⟨1553544, by rfl⟩ : syracuseStep 16571141 = 3107089) B3107089
theorem B11047427 : Blo 1939435 11047427 := bstep (se 1 (by rfl) ⟨8285570, by rfl⟩ : syracuseStep 11047427 = 16571141) B16571141
theorem B7364951 : Blo 1939435 7364951 := bstep (se 1 (by rfl) ⟨5523713, by rfl⟩ : syracuseStep 7364951 = 11047427) B11047427
theorem B4909967 : Blo 1939435 4909967 := bstep (se 1 (by rfl) ⟨3682475, by rfl⟩ : syracuseStep 4909967 = 7364951) B7364951
theorem B3273311 : Blo 1939435 3273311 := bstep (se 1 (by rfl) ⟨2454983, by rfl⟩ : syracuseStep 3273311 = 4909967) B4909967
theorem B2182207 : Blo 1939435 2182207 := bstep (se 1 (by rfl) ⟨1636655, by rfl⟩ : syracuseStep 2182207 = 3273311) B3273311
theorem B2909609 : Blo 1939435 2909609 := bstep (se 2 (by rfl) ⟨1091103, by rfl⟩ : syracuseStep 2909609 = 2182207) B2182207
theorem B1939739 : Blo 1939435 1939739 := bstep (se 1 (by rfl) ⟨1454804, by rfl⟩ : syracuseStep 1939739 = 2909609) B2909609
theorem B7364965 : Blo 1939435 7364965 := bbase (se 4 (by rfl) ⟨690465, by rfl⟩ : syracuseStep 7364965 = 1380931) (by norm_num)
theorem B9819953 : Blo 1939435 9819953 := bstep (se 2 (by rfl) ⟨3682482, by rfl⟩ : syracuseStep 9819953 = 7364965) B7364965
theorem B6546635 : Blo 1939435 6546635 := bstep (se 1 (by rfl) ⟨4909976, by rfl⟩ : syracuseStep 6546635 = 9819953) B9819953
theorem B4364423 : Blo 1939435 4364423 := bstep (se 1 (by rfl) ⟨3273317, by rfl⟩ : syracuseStep 4364423 = 6546635) B6546635
theorem B2909615 : Blo 1939435 2909615 := bstep (se 1 (by rfl) ⟨2182211, by rfl⟩ : syracuseStep 2909615 = 4364423) B4364423
theorem B1939743 : Blo 1939435 1939743 := bstep (se 1 (by rfl) ⟨1454807, by rfl⟩ : syracuseStep 1939743 = 2909615) B2909615
theorem B2909621 : Blo 1939435 2909621 := bbase (se 5 (by rfl) ⟨136388, by rfl⟩ : syracuseStep 2909621 = 272777) (by norm_num)
theorem B1939747 : Blo 1939435 1939747 := bstep (se 1 (by rfl) ⟨1454810, by rfl⟩ : syracuseStep 1939747 = 2909621) B2909621
theorem B4909997 : Blo 1939435 4909997 := bbase (se 3 (by rfl) ⟨920624, by rfl⟩ : syracuseStep 4909997 = 1841249) (by norm_num)
theorem B3273331 : Blo 1939435 3273331 := bstep (se 1 (by rfl) ⟨2454998, by rfl⟩ : syracuseStep 3273331 = 4909997) B4909997
theorem B4364441 : Blo 1939435 4364441 := bstep (se 2 (by rfl) ⟨1636665, by rfl⟩ : syracuseStep 4364441 = 3273331) B3273331
theorem B2909627 : Blo 1939435 2909627 := bstep (se 1 (by rfl) ⟨2182220, by rfl⟩ : syracuseStep 2909627 = 4364441) B4364441
theorem B1939751 : Blo 1939435 1939751 := bstep (se 1 (by rfl) ⟨1454813, by rfl⟩ : syracuseStep 1939751 = 2909627) B2909627
theorem B2182225 : Blo 1939435 2182225 := bbase (se 2 (by rfl) ⟨818334, by rfl⟩ : syracuseStep 2182225 = 1636669) (by norm_num)
theorem B2909633 : Blo 1939435 2909633 := bstep (se 2 (by rfl) ⟨1091112, by rfl⟩ : syracuseStep 2909633 = 2182225) B2182225
theorem B1939755 : Blo 1939435 1939755 := bstep (se 1 (by rfl) ⟨1454816, by rfl⟩ : syracuseStep 1939755 = 2909633) B2909633
theorem B2761885 : Blo 1939435 2761885 := bbase (se 3 (by rfl) ⟨517853, by rfl⟩ : syracuseStep 2761885 = 1035707) (by norm_num)
theorem B3682513 : Blo 1939435 3682513 := bstep (se 2 (by rfl) ⟨1380942, by rfl⟩ : syracuseStep 3682513 = 2761885) B2761885
theorem B4910017 : Blo 1939435 4910017 := bstep (se 2 (by rfl) ⟨1841256, by rfl⟩ : syracuseStep 4910017 = 3682513) B3682513
theorem B6546689 : Blo 1939435 6546689 := bstep (se 2 (by rfl) ⟨2455008, by rfl⟩ : syracuseStep 6546689 = 4910017) B4910017
theorem B4364459 : Blo 1939435 4364459 := bstep (se 1 (by rfl) ⟨3273344, by rfl⟩ : syracuseStep 4364459 = 6546689) B6546689
theorem B2909639 : Blo 1939435 2909639 := bstep (se 1 (by rfl) ⟨2182229, by rfl⟩ : syracuseStep 2909639 = 4364459) B4364459
theorem B1939759 : Blo 1939435 1939759 := bstep (se 1 (by rfl) ⟨1454819, by rfl⟩ : syracuseStep 1939759 = 2909639) B2909639
theorem B2909645 : Blo 1939435 2909645 := bbase (se 3 (by rfl) ⟨545558, by rfl⟩ : syracuseStep 2909645 = 1091117) (by norm_num)
theorem B1939763 : Blo 1939435 1939763 := bstep (se 1 (by rfl) ⟨1454822, by rfl⟩ : syracuseStep 1939763 = 2909645) B2909645
theorem B4364477 : Blo 1939435 4364477 := bbase (se 3 (by rfl) ⟨818339, by rfl⟩ : syracuseStep 4364477 = 1636679) (by norm_num)
theorem B2909651 : Blo 1939435 2909651 := bstep (se 1 (by rfl) ⟨2182238, by rfl⟩ : syracuseStep 2909651 = 4364477) B4364477
theorem B1939767 : Blo 1939435 1939767 := bstep (se 1 (by rfl) ⟨1454825, by rfl⟩ : syracuseStep 1939767 = 2909651) B2909651
theorem B3273365 : Blo 1939435 3273365 := bbase (se 6 (by rfl) ⟨76719, by rfl⟩ : syracuseStep 3273365 = 153439) (by norm_num)
theorem B2182243 : Blo 1939435 2182243 := bstep (se 1 (by rfl) ⟨1636682, by rfl⟩ : syracuseStep 2182243 = 3273365) B3273365
theorem B2909657 : Blo 1939435 2909657 := bstep (se 2 (by rfl) ⟨1091121, by rfl⟩ : syracuseStep 2909657 = 2182243) B2182243
theorem B1939771 : Blo 1939435 1939771 := bstep (se 1 (by rfl) ⟨1454828, by rfl⟩ : syracuseStep 1939771 = 2909657) B2909657
theorem B25196309 : Blo 1939435 25196309 := bbase (se 6 (by rfl) ⟨590538, by rfl⟩ : syracuseStep 25196309 = 1181077) (by norm_num)
theorem B16797539 : Blo 1939435 16797539 := bstep (se 1 (by rfl) ⟨12598154, by rfl⟩ : syracuseStep 16797539 = 25196309) B25196309
theorem B11198359 : Blo 1939435 11198359 := bstep (se 1 (by rfl) ⟨8398769, by rfl⟩ : syracuseStep 11198359 = 16797539) B16797539
theorem B14931145 : Blo 1939435 14931145 := bstep (se 2 (by rfl) ⟨5599179, by rfl⟩ : syracuseStep 14931145 = 11198359) B11198359
theorem B19908193 : Blo 1939435 19908193 := bstep (se 2 (by rfl) ⟨7465572, by rfl⟩ : syracuseStep 19908193 = 14931145) B14931145
theorem B26544257 : Blo 1939435 26544257 := bstep (se 2 (by rfl) ⟨9954096, by rfl⟩ : syracuseStep 26544257 = 19908193) B19908193
theorem B17696171 : Blo 1939435 17696171 := bstep (se 1 (by rfl) ⟨13272128, by rfl⟩ : syracuseStep 17696171 = 26544257) B26544257
theorem B47189789 : Blo 1939435 47189789 := bstep (se 3 (by rfl) ⟨8848085, by rfl⟩ : syracuseStep 47189789 = 17696171) B17696171
theorem B31459859 : Blo 1939435 31459859 := bstep (se 1 (by rfl) ⟨23594894, by rfl⟩ : syracuseStep 31459859 = 47189789) B47189789
theorem B20973239 : Blo 1939435 20973239 := bstep (se 1 (by rfl) ⟨15729929, by rfl⟩ : syracuseStep 20973239 = 31459859) B31459859
theorem B13982159 : Blo 1939435 13982159 := bstep (se 1 (by rfl) ⟨10486619, by rfl⟩ : syracuseStep 13982159 = 20973239) B20973239
theorem B9321439 : Blo 1939435 9321439 := bstep (se 1 (by rfl) ⟨6991079, by rfl⟩ : syracuseStep 9321439 = 13982159) B13982159
theorem B12428585 : Blo 1939435 12428585 := bstep (se 2 (by rfl) ⟨4660719, by rfl⟩ : syracuseStep 12428585 = 9321439) B9321439
theorem B8285723 : Blo 1939435 8285723 := bstep (se 1 (by rfl) ⟨6214292, by rfl⟩ : syracuseStep 8285723 = 12428585) B12428585
theorem B5523815 : Blo 1939435 5523815 := bstep (se 1 (by rfl) ⟨4142861, by rfl⟩ : syracuseStep 5523815 = 8285723) B8285723
theorem B14730173 : Blo 1939435 14730173 := bstep (se 3 (by rfl) ⟨2761907, by rfl⟩ : syracuseStep 14730173 = 5523815) B5523815
theorem B9820115 : Blo 1939435 9820115 := bstep (se 1 (by rfl) ⟨7365086, by rfl⟩ : syracuseStep 9820115 = 14730173) B14730173
theorem B6546743 : Blo 1939435 6546743 := bstep (se 1 (by rfl) ⟨4910057, by rfl⟩ : syracuseStep 6546743 = 9820115) B9820115
theorem B4364495 : Blo 1939435 4364495 := bstep (se 1 (by rfl) ⟨3273371, by rfl⟩ : syracuseStep 4364495 = 6546743) B6546743
theorem B2909663 : Blo 1939435 2909663 := bstep (se 1 (by rfl) ⟨2182247, by rfl⟩ : syracuseStep 2909663 = 4364495) B4364495
theorem B1939775 : Blo 1939435 1939775 := bstep (se 1 (by rfl) ⟨1454831, by rfl⟩ : syracuseStep 1939775 = 2909663) B2909663
theorem B2909669 : Blo 1939435 2909669 := bbase (se 4 (by rfl) ⟨272781, by rfl⟩ : syracuseStep 2909669 = 545563) (by norm_num)
theorem B1939779 : Blo 1939435 1939779 := bstep (se 1 (by rfl) ⟨1454834, by rfl⟩ : syracuseStep 1939779 = 2909669) B2909669
theorem B2362165 : Blo 1939435 2362165 := bbase (se 5 (by rfl) ⟨110726, by rfl⟩ : syracuseStep 2362165 = 221453) (by norm_num)
theorem B12598213 : Blo 1939435 12598213 := bstep (se 4 (by rfl) ⟨1181082, by rfl⟩ : syracuseStep 12598213 = 2362165) B2362165
theorem B16797617 : Blo 1939435 16797617 := bstep (se 2 (by rfl) ⟨6299106, by rfl⟩ : syracuseStep 16797617 = 12598213) B12598213
theorem B11198411 : Blo 1939435 11198411 := bstep (se 1 (by rfl) ⟨8398808, by rfl⟩ : syracuseStep 11198411 = 16797617) B16797617
theorem B7465607 : Blo 1939435 7465607 := bstep (se 1 (by rfl) ⟨5599205, by rfl⟩ : syracuseStep 7465607 = 11198411) B11198411
theorem B4977071 : Blo 1939435 4977071 := bstep (se 1 (by rfl) ⟨3732803, by rfl⟩ : syracuseStep 4977071 = 7465607) B7465607
theorem B3318047 : Blo 1939435 3318047 := bstep (se 1 (by rfl) ⟨2488535, by rfl⟩ : syracuseStep 3318047 = 4977071) B4977071
theorem B2212031 : Blo 1939435 2212031 := bstep (se 1 (by rfl) ⟨1659023, by rfl⟩ : syracuseStep 2212031 = 3318047) B3318047
theorem B5898749 : Blo 1939435 5898749 := bstep (se 3 (by rfl) ⟨1106015, by rfl⟩ : syracuseStep 5898749 = 2212031) B2212031
theorem B62919989 : Blo 1939435 62919989 := bstep (se 5 (by rfl) ⟨2949374, by rfl⟩ : syracuseStep 62919989 = 5898749) B5898749
theorem B41946659 : Blo 1939435 41946659 := bstep (se 1 (by rfl) ⟨31459994, by rfl⟩ : syracuseStep 41946659 = 62919989) B62919989
theorem B27964439 : Blo 1939435 27964439 := bstep (se 1 (by rfl) ⟨20973329, by rfl⟩ : syracuseStep 27964439 = 41946659) B41946659
theorem B18642959 : Blo 1939435 18642959 := bstep (se 1 (by rfl) ⟨13982219, by rfl⟩ : syracuseStep 18642959 = 27964439) B27964439
theorem B12428639 : Blo 1939435 12428639 := bstep (se 1 (by rfl) ⟨9321479, by rfl⟩ : syracuseStep 12428639 = 18642959) B18642959
theorem B8285759 : Blo 1939435 8285759 := bstep (se 1 (by rfl) ⟨6214319, by rfl⟩ : syracuseStep 8285759 = 12428639) B12428639
theorem B5523839 : Blo 1939435 5523839 := bstep (se 1 (by rfl) ⟨4142879, by rfl⟩ : syracuseStep 5523839 = 8285759) B8285759
theorem B3682559 : Blo 1939435 3682559 := bstep (se 1 (by rfl) ⟨2761919, by rfl⟩ : syracuseStep 3682559 = 5523839) B5523839
theorem B2455039 : Blo 1939435 2455039 := bstep (se 1 (by rfl) ⟨1841279, by rfl⟩ : syracuseStep 2455039 = 3682559) B3682559
theorem B3273385 : Blo 1939435 3273385 := bstep (se 2 (by rfl) ⟨1227519, by rfl⟩ : syracuseStep 3273385 = 2455039) B2455039
theorem B4364513 : Blo 1939435 4364513 := bstep (se 2 (by rfl) ⟨1636692, by rfl⟩ : syracuseStep 4364513 = 3273385) B3273385
theorem B2909675 : Blo 1939435 2909675 := bstep (se 1 (by rfl) ⟨2182256, by rfl⟩ : syracuseStep 2909675 = 4364513) B4364513
theorem B1939783 : Blo 1939435 1939783 := bstep (se 1 (by rfl) ⟨1454837, by rfl⟩ : syracuseStep 1939783 = 2909675) B2909675
theorem B2182261 : Blo 1939435 2182261 := bbase (se 5 (by rfl) ⟨102293, by rfl⟩ : syracuseStep 2182261 = 204587) (by norm_num)
theorem B2909681 : Blo 1939435 2909681 := bstep (se 2 (by rfl) ⟨1091130, by rfl⟩ : syracuseStep 2909681 = 2182261) B2182261
theorem B1939787 : Blo 1939435 1939787 := bstep (se 1 (by rfl) ⟨1454840, by rfl⟩ : syracuseStep 1939787 = 2909681) B2909681
theorem B2455049 : Blo 1939435 2455049 := bbase (se 2 (by rfl) ⟨920643, by rfl⟩ : syracuseStep 2455049 = 1841287) (by norm_num)
theorem B6546797 : Blo 1939435 6546797 := bstep (se 3 (by rfl) ⟨1227524, by rfl⟩ : syracuseStep 6546797 = 2455049) B2455049
theorem B4364531 : Blo 1939435 4364531 := bstep (se 1 (by rfl) ⟨3273398, by rfl⟩ : syracuseStep 4364531 = 6546797) B6546797
theorem B2909687 : Blo 1939435 2909687 := bstep (se 1 (by rfl) ⟨2182265, by rfl⟩ : syracuseStep 2909687 = 4364531) B4364531
theorem B1939791 : Blo 1939435 1939791 := bstep (se 1 (by rfl) ⟨1454843, by rfl⟩ : syracuseStep 1939791 = 2909687) B2909687
theorem B2909693 : Blo 1939435 2909693 := bbase (se 3 (by rfl) ⟨545567, by rfl⟩ : syracuseStep 2909693 = 1091135) (by norm_num)
theorem B1939795 : Blo 1939435 1939795 := bstep (se 1 (by rfl) ⟨1454846, by rfl⟩ : syracuseStep 1939795 = 2909693) B2909693
theorem B4364549 : Blo 1939435 4364549 := bbase (se 4 (by rfl) ⟨409176, by rfl⟩ : syracuseStep 4364549 = 818353) (by norm_num)
theorem B2909699 : Blo 1939435 2909699 := bstep (se 1 (by rfl) ⟨2182274, by rfl⟩ : syracuseStep 2909699 = 4364549) B4364549
theorem B1939799 : Blo 1939435 1939799 := bstep (se 1 (by rfl) ⟨1454849, by rfl⟩ : syracuseStep 1939799 = 2909699) B2909699
theorem B3682597 : Blo 1939435 3682597 := bbase (se 4 (by rfl) ⟨345243, by rfl⟩ : syracuseStep 3682597 = 690487) (by norm_num)
theorem B4910129 : Blo 1939435 4910129 := bstep (se 2 (by rfl) ⟨1841298, by rfl⟩ : syracuseStep 4910129 = 3682597) B3682597
theorem B3273419 : Blo 1939435 3273419 := bstep (se 1 (by rfl) ⟨2455064, by rfl⟩ : syracuseStep 3273419 = 4910129) B4910129
theorem B2182279 : Blo 1939435 2182279 := bstep (se 1 (by rfl) ⟨1636709, by rfl⟩ : syracuseStep 2182279 = 3273419) B3273419
theorem B2909705 : Blo 1939435 2909705 := bstep (se 2 (by rfl) ⟨1091139, by rfl⟩ : syracuseStep 2909705 = 2182279) B2182279
theorem B1939803 : Blo 1939435 1939803 := bstep (se 1 (by rfl) ⟨1454852, by rfl⟩ : syracuseStep 1939803 = 2909705) B2909705
theorem B9820277 : Blo 1939435 9820277 := bbase (se 5 (by rfl) ⟨460325, by rfl⟩ : syracuseStep 9820277 = 920651) (by norm_num)
theorem B6546851 : Blo 1939435 6546851 := bstep (se 1 (by rfl) ⟨4910138, by rfl⟩ : syracuseStep 6546851 = 9820277) B9820277
theorem B4364567 : Blo 1939435 4364567 := bstep (se 1 (by rfl) ⟨3273425, by rfl⟩ : syracuseStep 4364567 = 6546851) B6546851
theorem B2909711 : Blo 1939435 2909711 := bstep (se 1 (by rfl) ⟨2182283, by rfl⟩ : syracuseStep 2909711 = 4364567) B4364567
theorem B1939807 : Blo 1939435 1939807 := bstep (se 1 (by rfl) ⟨1454855, by rfl⟩ : syracuseStep 1939807 = 2909711) B2909711
theorem B2909717 : Blo 1939435 2909717 := bbase (se 6 (by rfl) ⟨68196, by rfl⟩ : syracuseStep 2909717 = 136393) (by norm_num)
theorem B1939811 : Blo 1939435 1939811 := bstep (se 1 (by rfl) ⟨1454858, by rfl⟩ : syracuseStep 1939811 = 2909717) B2909717
theorem B6214421 : Blo 1939435 6214421 := bbase (se 6 (by rfl) ⟨145650, by rfl⟩ : syracuseStep 6214421 = 291301) (by norm_num)
theorem B16571789 : Blo 1939435 16571789 := bstep (se 3 (by rfl) ⟨3107210, by rfl⟩ : syracuseStep 16571789 = 6214421) B6214421
theorem B11047859 : Blo 1939435 11047859 := bstep (se 1 (by rfl) ⟨8285894, by rfl⟩ : syracuseStep 11047859 = 16571789) B16571789
theorem B7365239 : Blo 1939435 7365239 := bstep (se 1 (by rfl) ⟨5523929, by rfl⟩ : syracuseStep 7365239 = 11047859) B11047859
theorem B4910159 : Blo 1939435 4910159 := bstep (se 1 (by rfl) ⟨3682619, by rfl⟩ : syracuseStep 4910159 = 7365239) B7365239
theorem B3273439 : Blo 1939435 3273439 := bstep (se 1 (by rfl) ⟨2455079, by rfl⟩ : syracuseStep 3273439 = 4910159) B4910159
theorem B4364585 : Blo 1939435 4364585 := bstep (se 2 (by rfl) ⟨1636719, by rfl⟩ : syracuseStep 4364585 = 3273439) B3273439
theorem B2909723 : Blo 1939435 2909723 := bstep (se 1 (by rfl) ⟨2182292, by rfl⟩ : syracuseStep 2909723 = 4364585) B4364585
theorem B1939815 : Blo 1939435 1939815 := bstep (se 1 (by rfl) ⟨1454861, by rfl⟩ : syracuseStep 1939815 = 2909723) B2909723
theorem B2182297 : Blo 1939435 2182297 := bbase (se 2 (by rfl) ⟨818361, by rfl⟩ : syracuseStep 2182297 = 1636723) (by norm_num)
theorem B2909729 : Blo 1939435 2909729 := bstep (se 2 (by rfl) ⟨1091148, by rfl⟩ : syracuseStep 2909729 = 2182297) B2182297
theorem B1939819 : Blo 1939435 1939819 := bstep (se 1 (by rfl) ⟨1454864, by rfl⟩ : syracuseStep 1939819 = 2909729) B2909729
theorem B7365269 : Blo 1939435 7365269 := bbase (se 6 (by rfl) ⟨172623, by rfl⟩ : syracuseStep 7365269 = 345247) (by norm_num)
theorem B4910179 : Blo 1939435 4910179 := bstep (se 1 (by rfl) ⟨3682634, by rfl⟩ : syracuseStep 4910179 = 7365269) B7365269
theorem B6546905 : Blo 1939435 6546905 := bstep (se 2 (by rfl) ⟨2455089, by rfl⟩ : syracuseStep 6546905 = 4910179) B4910179
theorem B4364603 : Blo 1939435 4364603 := bstep (se 1 (by rfl) ⟨3273452, by rfl⟩ : syracuseStep 4364603 = 6546905) B6546905
theorem B2909735 : Blo 1939435 2909735 := bstep (se 1 (by rfl) ⟨2182301, by rfl⟩ : syracuseStep 2909735 = 4364603) B4364603
theorem B1939823 : Blo 1939435 1939823 := bstep (se 1 (by rfl) ⟨1454867, by rfl⟩ : syracuseStep 1939823 = 2909735) B2909735
theorem B2909741 : Blo 1939435 2909741 := bbase (se 3 (by rfl) ⟨545576, by rfl⟩ : syracuseStep 2909741 = 1091153) (by norm_num)
theorem B1939827 : Blo 1939435 1939827 := bstep (se 1 (by rfl) ⟨1454870, by rfl⟩ : syracuseStep 1939827 = 2909741) B2909741
theorem B4364621 : Blo 1939435 4364621 := bbase (se 3 (by rfl) ⟨818366, by rfl⟩ : syracuseStep 4364621 = 1636733) (by norm_num)
theorem B2909747 : Blo 1939435 2909747 := bstep (se 1 (by rfl) ⟨2182310, by rfl⟩ : syracuseStep 2909747 = 4364621) B4364621
theorem B1939831 : Blo 1939435 1939831 := bstep (se 1 (by rfl) ⟨1454873, by rfl⟩ : syracuseStep 1939831 = 2909747) B2909747
theorem B2455105 : Blo 1939435 2455105 := bbase (se 2 (by rfl) ⟨920664, by rfl⟩ : syracuseStep 2455105 = 1841329) (by norm_num)
theorem B3273473 : Blo 1939435 3273473 := bstep (se 2 (by rfl) ⟨1227552, by rfl⟩ : syracuseStep 3273473 = 2455105) B2455105
theorem B2182315 : Blo 1939435 2182315 := bstep (se 1 (by rfl) ⟨1636736, by rfl⟩ : syracuseStep 2182315 = 3273473) B3273473
theorem B2909753 : Blo 1939435 2909753 := bstep (se 2 (by rfl) ⟨1091157, by rfl⟩ : syracuseStep 2909753 = 2182315) B2182315
theorem B1939835 : Blo 1939435 1939835 := bstep (se 1 (by rfl) ⟨1454876, by rfl⟩ : syracuseStep 1939835 = 2909753) B2909753
theorem B2330437 : Blo 1939435 2330437 := bbase (se 4 (by rfl) ⟨218478, by rfl⟩ : syracuseStep 2330437 = 436957) (by norm_num)
theorem B3107249 : Blo 1939435 3107249 := bstep (se 2 (by rfl) ⟨1165218, by rfl⟩ : syracuseStep 3107249 = 2330437) B2330437
theorem B2071499 : Blo 1939435 2071499 := bstep (se 1 (by rfl) ⟨1553624, by rfl⟩ : syracuseStep 2071499 = 3107249) B3107249
theorem B22095989 : Blo 1939435 22095989 := bstep (se 5 (by rfl) ⟨1035749, by rfl⟩ : syracuseStep 22095989 = 2071499) B2071499
theorem B14730659 : Blo 1939435 14730659 := bstep (se 1 (by rfl) ⟨11047994, by rfl⟩ : syracuseStep 14730659 = 22095989) B22095989
theorem B9820439 : Blo 1939435 9820439 := bstep (se 1 (by rfl) ⟨7365329, by rfl⟩ : syracuseStep 9820439 = 14730659) B14730659
theorem B6546959 : Blo 1939435 6546959 := bstep (se 1 (by rfl) ⟨4910219, by rfl⟩ : syracuseStep 6546959 = 9820439) B9820439
theorem B4364639 : Blo 1939435 4364639 := bstep (se 1 (by rfl) ⟨3273479, by rfl⟩ : syracuseStep 4364639 = 6546959) B6546959
theorem B2909759 : Blo 1939435 2909759 := bstep (se 1 (by rfl) ⟨2182319, by rfl⟩ : syracuseStep 2909759 = 4364639) B4364639
theorem B1939839 : Blo 1939435 1939839 := bstep (se 1 (by rfl) ⟨1454879, by rfl⟩ : syracuseStep 1939839 = 2909759) B2909759
theorem B2909765 : Blo 1939435 2909765 := bbase (se 4 (by rfl) ⟨272790, by rfl⟩ : syracuseStep 2909765 = 545581) (by norm_num)
theorem B1939843 : Blo 1939435 1939843 := bstep (se 1 (by rfl) ⟨1454882, by rfl⟩ : syracuseStep 1939843 = 2909765) B2909765
theorem B3273493 : Blo 1939435 3273493 := bbase (se 6 (by rfl) ⟨76722, by rfl⟩ : syracuseStep 3273493 = 153445) (by norm_num)
theorem B4364657 : Blo 1939435 4364657 := bstep (se 2 (by rfl) ⟨1636746, by rfl⟩ : syracuseStep 4364657 = 3273493) B3273493
theorem B2909771 : Blo 1939435 2909771 := bstep (se 1 (by rfl) ⟨2182328, by rfl⟩ : syracuseStep 2909771 = 4364657) B4364657
theorem B1939847 : Blo 1939435 1939847 := bstep (se 1 (by rfl) ⟨1454885, by rfl⟩ : syracuseStep 1939847 = 2909771) B2909771
theorem B2182333 : Blo 1939435 2182333 := bbase (se 3 (by rfl) ⟨409187, by rfl⟩ : syracuseStep 2182333 = 818375) (by norm_num)
theorem B2909777 : Blo 1939435 2909777 := bstep (se 2 (by rfl) ⟨1091166, by rfl⟩ : syracuseStep 2909777 = 2182333) B2182333
theorem B1939851 : Blo 1939435 1939851 := bstep (se 1 (by rfl) ⟨1454888, by rfl⟩ : syracuseStep 1939851 = 2909777) B2909777
theorem B6547013 : Blo 1939435 6547013 := bbase (se 4 (by rfl) ⟨613782, by rfl⟩ : syracuseStep 6547013 = 1227565) (by norm_num)
theorem B4364675 : Blo 1939435 4364675 := bstep (se 1 (by rfl) ⟨3273506, by rfl⟩ : syracuseStep 4364675 = 6547013) B6547013
theorem B2909783 : Blo 1939435 2909783 := bstep (se 1 (by rfl) ⟨2182337, by rfl⟩ : syracuseStep 2909783 = 4364675) B4364675
theorem B1939855 : Blo 1939435 1939855 := bstep (se 1 (by rfl) ⟨1454891, by rfl⟩ : syracuseStep 1939855 = 2909783) B2909783
theorem B2909789 : Blo 1939435 2909789 := bbase (se 3 (by rfl) ⟨545585, by rfl⟩ : syracuseStep 2909789 = 1091171) (by norm_num)
theorem B1939859 : Blo 1939435 1939859 := bstep (se 1 (by rfl) ⟨1454894, by rfl⟩ : syracuseStep 1939859 = 2909789) B2909789
theorem B4364693 : Blo 1939435 4364693 := bbase (se 6 (by rfl) ⟨102297, by rfl⟩ : syracuseStep 4364693 = 204595) (by norm_num)
theorem B2909795 : Blo 1939435 2909795 := bstep (se 1 (by rfl) ⟨2182346, by rfl⟩ : syracuseStep 2909795 = 4364693) B4364693
theorem B1939863 : Blo 1939435 1939863 := bstep (se 1 (by rfl) ⟨1454897, by rfl⟩ : syracuseStep 1939863 = 2909795) B2909795
theorem B8969237 : Blo 1939435 8969237 := bbase (se 6 (by rfl) ⟨210216, by rfl⟩ : syracuseStep 8969237 = 420433) (by norm_num)
theorem B5979491 : Blo 1939435 5979491 := bstep (se 1 (by rfl) ⟨4484618, by rfl⟩ : syracuseStep 5979491 = 8969237) B8969237
theorem B3986327 : Blo 1939435 3986327 := bstep (se 1 (by rfl) ⟨2989745, by rfl⟩ : syracuseStep 3986327 = 5979491) B5979491
theorem B2657551 : Blo 1939435 2657551 := bstep (se 1 (by rfl) ⟨1993163, by rfl⟩ : syracuseStep 2657551 = 3986327) B3986327
theorem B56694421 : Blo 1939435 56694421 := bstep (se 6 (by rfl) ⟨1328775, by rfl⟩ : syracuseStep 56694421 = 2657551) B2657551
theorem B75592561 : Blo 1939435 75592561 := bstep (se 2 (by rfl) ⟨28347210, by rfl⟩ : syracuseStep 75592561 = 56694421) B56694421
theorem B100790081 : Blo 1939435 100790081 := bstep (se 2 (by rfl) ⟨37796280, by rfl⟩ : syracuseStep 100790081 = 75592561) B75592561
theorem B67193387 : Blo 1939435 67193387 := bstep (se 1 (by rfl) ⟨50395040, by rfl⟩ : syracuseStep 67193387 = 100790081) B100790081
theorem B44795591 : Blo 1939435 44795591 := bstep (se 1 (by rfl) ⟨33596693, by rfl⟩ : syracuseStep 44795591 = 67193387) B67193387
theorem B29863727 : Blo 1939435 29863727 := bstep (se 1 (by rfl) ⟨22397795, by rfl⟩ : syracuseStep 29863727 = 44795591) B44795591
theorem B19909151 : Blo 1939435 19909151 := bstep (se 1 (by rfl) ⟨14931863, by rfl⟩ : syracuseStep 19909151 = 29863727) B29863727
theorem B13272767 : Blo 1939435 13272767 := bstep (se 1 (by rfl) ⟨9954575, by rfl⟩ : syracuseStep 13272767 = 19909151) B19909151
theorem B8848511 : Blo 1939435 8848511 := bstep (se 1 (by rfl) ⟨6636383, by rfl⟩ : syracuseStep 8848511 = 13272767) B13272767
theorem B5899007 : Blo 1939435 5899007 := bstep (se 1 (by rfl) ⟨4424255, by rfl⟩ : syracuseStep 5899007 = 8848511) B8848511
theorem B3932671 : Blo 1939435 3932671 := bstep (se 1 (by rfl) ⟨2949503, by rfl⟩ : syracuseStep 3932671 = 5899007) B5899007
theorem B5243561 : Blo 1939435 5243561 := bstep (se 2 (by rfl) ⟨1966335, by rfl⟩ : syracuseStep 5243561 = 3932671) B3932671
theorem B3495707 : Blo 1939435 3495707 := bstep (se 1 (by rfl) ⟨2621780, by rfl⟩ : syracuseStep 3495707 = 5243561) B5243561
theorem B2330471 : Blo 1939435 2330471 := bstep (se 1 (by rfl) ⟨1747853, by rfl⟩ : syracuseStep 2330471 = 3495707) B3495707
theorem B6214589 : Blo 1939435 6214589 := bstep (se 3 (by rfl) ⟨1165235, by rfl⟩ : syracuseStep 6214589 = 2330471) B2330471
theorem B4143059 : Blo 1939435 4143059 := bstep (se 1 (by rfl) ⟨3107294, by rfl⟩ : syracuseStep 4143059 = 6214589) B6214589
theorem B2762039 : Blo 1939435 2762039 := bstep (se 1 (by rfl) ⟨2071529, by rfl⟩ : syracuseStep 2762039 = 4143059) B4143059
theorem B7365437 : Blo 1939435 7365437 := bstep (se 3 (by rfl) ⟨1381019, by rfl⟩ : syracuseStep 7365437 = 2762039) B2762039
theorem B4910291 : Blo 1939435 4910291 := bstep (se 1 (by rfl) ⟨3682718, by rfl⟩ : syracuseStep 4910291 = 7365437) B7365437
theorem B3273527 : Blo 1939435 3273527 := bstep (se 1 (by rfl) ⟨2455145, by rfl⟩ : syracuseStep 3273527 = 4910291) B4910291
theorem B2182351 : Blo 1939435 2182351 := bstep (se 1 (by rfl) ⟨1636763, by rfl⟩ : syracuseStep 2182351 = 3273527) B3273527
theorem B2909801 : Blo 1939435 2909801 := bstep (se 2 (by rfl) ⟨1091175, by rfl⟩ : syracuseStep 2909801 = 2182351) B2182351
theorem B1939867 : Blo 1939435 1939867 := bstep (se 1 (by rfl) ⟨1454900, by rfl⟩ : syracuseStep 1939867 = 2909801) B2909801
theorem B8286133 : Blo 1939435 8286133 := bbase (se 5 (by rfl) ⟨388412, by rfl⟩ : syracuseStep 8286133 = 776825) (by norm_num)
theorem B11048177 : Blo 1939435 11048177 := bstep (se 2 (by rfl) ⟨4143066, by rfl⟩ : syracuseStep 11048177 = 8286133) B8286133
theorem B7365451 : Blo 1939435 7365451 := bstep (se 1 (by rfl) ⟨5524088, by rfl⟩ : syracuseStep 7365451 = 11048177) B11048177
theorem B9820601 : Blo 1939435 9820601 := bstep (se 2 (by rfl) ⟨3682725, by rfl⟩ : syracuseStep 9820601 = 7365451) B7365451
theorem B6547067 : Blo 1939435 6547067 := bstep (se 1 (by rfl) ⟨4910300, by rfl⟩ : syracuseStep 6547067 = 9820601) B9820601
theorem B4364711 : Blo 1939435 4364711 := bstep (se 1 (by rfl) ⟨3273533, by rfl⟩ : syracuseStep 4364711 = 6547067) B6547067
theorem B2909807 : Blo 1939435 2909807 := bstep (se 1 (by rfl) ⟨2182355, by rfl⟩ : syracuseStep 2909807 = 4364711) B4364711
theorem B1939871 : Blo 1939435 1939871 := bstep (se 1 (by rfl) ⟨1454903, by rfl⟩ : syracuseStep 1939871 = 2909807) B2909807
theorem B2909813 : Blo 1939435 2909813 := bbase (se 5 (by rfl) ⟨136397, by rfl⟩ : syracuseStep 2909813 = 272795) (by norm_num)
theorem B1939875 : Blo 1939435 1939875 := bstep (se 1 (by rfl) ⟨1454906, by rfl⟩ : syracuseStep 1939875 = 2909813) B2909813
theorem B3682741 : Blo 1939435 3682741 := bbase (se 5 (by rfl) ⟨172628, by rfl⟩ : syracuseStep 3682741 = 345257) (by norm_num)
theorem B4910321 : Blo 1939435 4910321 := bstep (se 2 (by rfl) ⟨1841370, by rfl⟩ : syracuseStep 4910321 = 3682741) B3682741
theorem B3273547 : Blo 1939435 3273547 := bstep (se 1 (by rfl) ⟨2455160, by rfl⟩ : syracuseStep 3273547 = 4910321) B4910321
theorem B4364729 : Blo 1939435 4364729 := bstep (se 2 (by rfl) ⟨1636773, by rfl⟩ : syracuseStep 4364729 = 3273547) B3273547
theorem B2909819 : Blo 1939435 2909819 := bstep (se 1 (by rfl) ⟨2182364, by rfl⟩ : syracuseStep 2909819 = 4364729) B4364729
theorem B1939879 : Blo 1939435 1939879 := bstep (se 1 (by rfl) ⟨1454909, by rfl⟩ : syracuseStep 1939879 = 2909819) B2909819
theorem B2182369 : Blo 1939435 2182369 := bbase (se 2 (by rfl) ⟨818388, by rfl⟩ : syracuseStep 2182369 = 1636777) (by norm_num)
theorem B2909825 : Blo 1939435 2909825 := bstep (se 2 (by rfl) ⟨1091184, by rfl⟩ : syracuseStep 2909825 = 2182369) B2182369
theorem B1939883 : Blo 1939435 1939883 := bstep (se 1 (by rfl) ⟨1454912, by rfl⟩ : syracuseStep 1939883 = 2909825) B2909825
theorem B4910341 : Blo 1939435 4910341 := bbase (se 4 (by rfl) ⟨460344, by rfl⟩ : syracuseStep 4910341 = 920689) (by norm_num)
theorem B6547121 : Blo 1939435 6547121 := bstep (se 2 (by rfl) ⟨2455170, by rfl⟩ : syracuseStep 6547121 = 4910341) B4910341
theorem B4364747 : Blo 1939435 4364747 := bstep (se 1 (by rfl) ⟨3273560, by rfl⟩ : syracuseStep 4364747 = 6547121) B6547121
theorem B2909831 : Blo 1939435 2909831 := bstep (se 1 (by rfl) ⟨2182373, by rfl⟩ : syracuseStep 2909831 = 4364747) B4364747
theorem B1939887 : Blo 1939435 1939887 := bstep (se 1 (by rfl) ⟨1454915, by rfl⟩ : syracuseStep 1939887 = 2909831) B2909831
theorem B2909837 : Blo 1939435 2909837 := bbase (se 3 (by rfl) ⟨545594, by rfl⟩ : syracuseStep 2909837 = 1091189) (by norm_num)
theorem B1939891 : Blo 1939435 1939891 := bstep (se 1 (by rfl) ⟨1454918, by rfl⟩ : syracuseStep 1939891 = 2909837) B2909837
theorem B4364765 : Blo 1939435 4364765 := bbase (se 3 (by rfl) ⟨818393, by rfl⟩ : syracuseStep 4364765 = 1636787) (by norm_num)
theorem B2909843 : Blo 1939435 2909843 := bstep (se 1 (by rfl) ⟨2182382, by rfl⟩ : syracuseStep 2909843 = 4364765) B4364765
theorem B1939895 : Blo 1939435 1939895 := bstep (se 1 (by rfl) ⟨1454921, by rfl⟩ : syracuseStep 1939895 = 2909843) B2909843
theorem B3273581 : Blo 1939435 3273581 := bbase (se 3 (by rfl) ⟨613796, by rfl⟩ : syracuseStep 3273581 = 1227593) (by norm_num)
theorem B2182387 : Blo 1939435 2182387 := bstep (se 1 (by rfl) ⟨1636790, by rfl⟩ : syracuseStep 2182387 = 3273581) B3273581
theorem B2909849 : Blo 1939435 2909849 := bstep (se 2 (by rfl) ⟨1091193, by rfl⟩ : syracuseStep 2909849 = 2182387) B2182387
theorem B1939899 : Blo 1939435 1939899 := bstep (se 1 (by rfl) ⟨1454924, by rfl⟩ : syracuseStep 1939899 = 2909849) B2909849
theorem B2394541 : Blo 1939435 2394541 := bbase (se 3 (by rfl) ⟨448976, by rfl⟩ : syracuseStep 2394541 = 897953) (by norm_num)
theorem B3192721 : Blo 1939435 3192721 := bstep (se 2 (by rfl) ⟨1197270, by rfl⟩ : syracuseStep 3192721 = 2394541) B2394541
theorem B68111381 : Blo 1939435 68111381 := bstep (se 6 (by rfl) ⟨1596360, by rfl⟩ : syracuseStep 68111381 = 3192721) B3192721
theorem B181630349 : Blo 1939435 181630349 := bstep (se 3 (by rfl) ⟨34055690, by rfl⟩ : syracuseStep 181630349 = 68111381) B68111381
theorem B121086899 : Blo 1939435 121086899 := bstep (se 1 (by rfl) ⟨90815174, by rfl⟩ : syracuseStep 121086899 = 181630349) B181630349
theorem B80724599 : Blo 1939435 80724599 := bstep (se 1 (by rfl) ⟨60543449, by rfl⟩ : syracuseStep 80724599 = 121086899) B121086899
theorem B53816399 : Blo 1939435 53816399 := bstep (se 1 (by rfl) ⟨40362299, by rfl⟩ : syracuseStep 53816399 = 80724599) B80724599
theorem B35877599 : Blo 1939435 35877599 := bstep (se 1 (by rfl) ⟨26908199, by rfl⟩ : syracuseStep 35877599 = 53816399) B53816399
theorem B23918399 : Blo 1939435 23918399 := bstep (se 1 (by rfl) ⟨17938799, by rfl⟩ : syracuseStep 23918399 = 35877599) B35877599
theorem B15945599 : Blo 1939435 15945599 := bstep (se 1 (by rfl) ⟨11959199, by rfl⟩ : syracuseStep 15945599 = 23918399) B23918399
theorem B10630399 : Blo 1939435 10630399 := bstep (se 1 (by rfl) ⟨7972799, by rfl⟩ : syracuseStep 10630399 = 15945599) B15945599
theorem B14173865 : Blo 1939435 14173865 := bstep (se 2 (by rfl) ⟨5315199, by rfl⟩ : syracuseStep 14173865 = 10630399) B10630399
theorem B9449243 : Blo 1939435 9449243 := bstep (se 1 (by rfl) ⟨7086932, by rfl⟩ : syracuseStep 9449243 = 14173865) B14173865
theorem B6299495 : Blo 1939435 6299495 := bstep (se 1 (by rfl) ⟨4724621, by rfl⟩ : syracuseStep 6299495 = 9449243) B9449243
theorem B4199663 : Blo 1939435 4199663 := bstep (se 1 (by rfl) ⟨3149747, by rfl⟩ : syracuseStep 4199663 = 6299495) B6299495
theorem B2799775 : Blo 1939435 2799775 := bstep (se 1 (by rfl) ⟨2099831, by rfl⟩ : syracuseStep 2799775 = 4199663) B4199663
theorem B3733033 : Blo 1939435 3733033 := bstep (se 2 (by rfl) ⟨1399887, by rfl⟩ : syracuseStep 3733033 = 2799775) B2799775
theorem B4977377 : Blo 1939435 4977377 := bstep (se 2 (by rfl) ⟨1866516, by rfl⟩ : syracuseStep 4977377 = 3733033) B3733033
theorem B3318251 : Blo 1939435 3318251 := bstep (se 1 (by rfl) ⟨2488688, by rfl⟩ : syracuseStep 3318251 = 4977377) B4977377
theorem B8848669 : Blo 1939435 8848669 := bstep (se 3 (by rfl) ⟨1659125, by rfl⟩ : syracuseStep 8848669 = 3318251) B3318251
theorem B11798225 : Blo 1939435 11798225 := bstep (se 2 (by rfl) ⟨4424334, by rfl⟩ : syracuseStep 11798225 = 8848669) B8848669
theorem B7865483 : Blo 1939435 7865483 := bstep (se 1 (by rfl) ⟨5899112, by rfl⟩ : syracuseStep 7865483 = 11798225) B11798225
theorem B20974621 : Blo 1939435 20974621 := bstep (se 3 (by rfl) ⟨3932741, by rfl⟩ : syracuseStep 20974621 = 7865483) B7865483
theorem B27966161 : Blo 1939435 27966161 := bstep (se 2 (by rfl) ⟨10487310, by rfl⟩ : syracuseStep 27966161 = 20974621) B20974621
theorem B18644107 : Blo 1939435 18644107 := bstep (se 1 (by rfl) ⟨13983080, by rfl⟩ : syracuseStep 18644107 = 27966161) B27966161
theorem B24858809 : Blo 1939435 24858809 := bstep (se 2 (by rfl) ⟨9322053, by rfl⟩ : syracuseStep 24858809 = 18644107) B18644107
theorem B16572539 : Blo 1939435 16572539 := bstep (se 1 (by rfl) ⟨12429404, by rfl⟩ : syracuseStep 16572539 = 24858809) B24858809
theorem B11048359 : Blo 1939435 11048359 := bstep (se 1 (by rfl) ⟨8286269, by rfl⟩ : syracuseStep 11048359 = 16572539) B16572539
theorem B14731145 : Blo 1939435 14731145 := bstep (se 2 (by rfl) ⟨5524179, by rfl⟩ : syracuseStep 14731145 = 11048359) B11048359
theorem B9820763 : Blo 1939435 9820763 := bstep (se 1 (by rfl) ⟨7365572, by rfl⟩ : syracuseStep 9820763 = 14731145) B14731145
theorem B6547175 : Blo 1939435 6547175 := bstep (se 1 (by rfl) ⟨4910381, by rfl⟩ : syracuseStep 6547175 = 9820763) B9820763
theorem B4364783 : Blo 1939435 4364783 := bstep (se 1 (by rfl) ⟨3273587, by rfl⟩ : syracuseStep 4364783 = 6547175) B6547175
theorem B2909855 : Blo 1939435 2909855 := bstep (se 1 (by rfl) ⟨2182391, by rfl⟩ : syracuseStep 2909855 = 4364783) B4364783
theorem B1939903 : Blo 1939435 1939903 := bstep (se 1 (by rfl) ⟨1454927, by rfl⟩ : syracuseStep 1939903 = 2909855) B2909855
theorem B2909861 : Blo 1939435 2909861 := bbase (se 4 (by rfl) ⟨272799, by rfl⟩ : syracuseStep 2909861 = 545599) (by norm_num)
theorem B1939907 : Blo 1939435 1939907 := bstep (se 1 (by rfl) ⟨1454930, by rfl⟩ : syracuseStep 1939907 = 2909861) B2909861
theorem B2455201 : Blo 1939435 2455201 := bbase (se 2 (by rfl) ⟨920700, by rfl⟩ : syracuseStep 2455201 = 1841401) (by norm_num)
theorem B3273601 : Blo 1939435 3273601 := bstep (se 2 (by rfl) ⟨1227600, by rfl⟩ : syracuseStep 3273601 = 2455201) B2455201
theorem B4364801 : Blo 1939435 4364801 := bstep (se 2 (by rfl) ⟨1636800, by rfl⟩ : syracuseStep 4364801 = 3273601) B3273601
theorem B2909867 : Blo 1939435 2909867 := bstep (se 1 (by rfl) ⟨2182400, by rfl⟩ : syracuseStep 2909867 = 4364801) B4364801
theorem B1939911 : Blo 1939435 1939911 := bstep (se 1 (by rfl) ⟨1454933, by rfl⟩ : syracuseStep 1939911 = 2909867) B2909867
theorem B2182405 : Blo 1939435 2182405 := bbase (se 4 (by rfl) ⟨204600, by rfl⟩ : syracuseStep 2182405 = 409201) (by norm_num)
theorem B2909873 : Blo 1939435 2909873 := bstep (se 2 (by rfl) ⟨1091202, by rfl⟩ : syracuseStep 2909873 = 2182405) B2182405
theorem B1939915 : Blo 1939435 1939915 := bstep (se 1 (by rfl) ⟨1454936, by rfl⟩ : syracuseStep 1939915 = 2909873) B2909873
theorem B2071585 : Blo 1939435 2071585 := bbase (se 2 (by rfl) ⟨776844, by rfl⟩ : syracuseStep 2071585 = 1553689) (by norm_num)
theorem B2762113 : Blo 1939435 2762113 := bstep (se 2 (by rfl) ⟨1035792, by rfl⟩ : syracuseStep 2762113 = 2071585) B2071585
theorem B3682817 : Blo 1939435 3682817 := bstep (se 2 (by rfl) ⟨1381056, by rfl⟩ : syracuseStep 3682817 = 2762113) B2762113
theorem B2455211 : Blo 1939435 2455211 := bstep (se 1 (by rfl) ⟨1841408, by rfl⟩ : syracuseStep 2455211 = 3682817) B3682817
theorem B6547229 : Blo 1939435 6547229 := bstep (se 3 (by rfl) ⟨1227605, by rfl⟩ : syracuseStep 6547229 = 2455211) B2455211
theorem B4364819 : Blo 1939435 4364819 := bstep (se 1 (by rfl) ⟨3273614, by rfl⟩ : syracuseStep 4364819 = 6547229) B6547229
theorem B2909879 : Blo 1939435 2909879 := bstep (se 1 (by rfl) ⟨2182409, by rfl⟩ : syracuseStep 2909879 = 4364819) B4364819
theorem B1939919 : Blo 1939435 1939919 := bstep (se 1 (by rfl) ⟨1454939, by rfl⟩ : syracuseStep 1939919 = 2909879) B2909879
theorem B2909885 : Blo 1939435 2909885 := bbase (se 3 (by rfl) ⟨545603, by rfl⟩ : syracuseStep 2909885 = 1091207) (by norm_num)
theorem B1939923 : Blo 1939435 1939923 := bstep (se 1 (by rfl) ⟨1454942, by rfl⟩ : syracuseStep 1939923 = 2909885) B2909885
theorem B4364837 : Blo 1939435 4364837 := bbase (se 4 (by rfl) ⟨409203, by rfl⟩ : syracuseStep 4364837 = 818407) (by norm_num)
theorem B2909891 : Blo 1939435 2909891 := bstep (se 1 (by rfl) ⟨2182418, by rfl⟩ : syracuseStep 2909891 = 4364837) B4364837
theorem B1939927 : Blo 1939435 1939927 := bstep (se 1 (by rfl) ⟨1454945, by rfl⟩ : syracuseStep 1939927 = 2909891) B2909891
theorem B4910453 : Blo 1939435 4910453 := bbase (se 5 (by rfl) ⟨230177, by rfl⟩ : syracuseStep 4910453 = 460355) (by norm_num)
theorem B3273635 : Blo 1939435 3273635 := bstep (se 1 (by rfl) ⟨2455226, by rfl⟩ : syracuseStep 3273635 = 4910453) B4910453
theorem B2182423 : Blo 1939435 2182423 := bstep (se 1 (by rfl) ⟨1636817, by rfl⟩ : syracuseStep 2182423 = 3273635) B3273635
theorem B2909897 : Blo 1939435 2909897 := bstep (se 2 (by rfl) ⟨1091211, by rfl⟩ : syracuseStep 2909897 = 2182423) B2182423
theorem B1939931 : Blo 1939435 1939931 := bstep (se 1 (by rfl) ⟨1454948, by rfl⟩ : syracuseStep 1939931 = 2909897) B2909897
theorem B6636613 : Blo 1939435 6636613 := bbase (se 4 (by rfl) ⟨622182, by rfl⟩ : syracuseStep 6636613 = 1244365) (by norm_num)
theorem B8848817 : Blo 1939435 8848817 := bstep (se 2 (by rfl) ⟨3318306, by rfl⟩ : syracuseStep 8848817 = 6636613) B6636613
theorem B5899211 : Blo 1939435 5899211 := bstep (se 1 (by rfl) ⟨4424408, by rfl⟩ : syracuseStep 5899211 = 8848817) B8848817
theorem B3932807 : Blo 1939435 3932807 := bstep (se 1 (by rfl) ⟨2949605, by rfl⟩ : syracuseStep 3932807 = 5899211) B5899211
theorem B10487485 : Blo 1939435 10487485 := bstep (se 3 (by rfl) ⟨1966403, by rfl⟩ : syracuseStep 10487485 = 3932807) B3932807
theorem B13983313 : Blo 1939435 13983313 := bstep (se 2 (by rfl) ⟨5243742, by rfl⟩ : syracuseStep 13983313 = 10487485) B10487485
theorem B18644417 : Blo 1939435 18644417 := bstep (se 2 (by rfl) ⟨6991656, by rfl⟩ : syracuseStep 18644417 = 13983313) B13983313
theorem B12429611 : Blo 1939435 12429611 := bstep (se 1 (by rfl) ⟨9322208, by rfl⟩ : syracuseStep 12429611 = 18644417) B18644417
theorem B8286407 : Blo 1939435 8286407 := bstep (se 1 (by rfl) ⟨6214805, by rfl⟩ : syracuseStep 8286407 = 12429611) B12429611
theorem B5524271 : Blo 1939435 5524271 := bstep (se 1 (by rfl) ⟨4143203, by rfl⟩ : syracuseStep 5524271 = 8286407) B8286407
theorem B3682847 : Blo 1939435 3682847 := bstep (se 1 (by rfl) ⟨2762135, by rfl⟩ : syracuseStep 3682847 = 5524271) B5524271
theorem B9820925 : Blo 1939435 9820925 := bstep (se 3 (by rfl) ⟨1841423, by rfl⟩ : syracuseStep 9820925 = 3682847) B3682847
theorem B6547283 : Blo 1939435 6547283 := bstep (se 1 (by rfl) ⟨4910462, by rfl⟩ : syracuseStep 6547283 = 9820925) B9820925
theorem B4364855 : Blo 1939435 4364855 := bstep (se 1 (by rfl) ⟨3273641, by rfl⟩ : syracuseStep 4364855 = 6547283) B6547283
theorem B2909903 : Blo 1939435 2909903 := bstep (se 1 (by rfl) ⟨2182427, by rfl⟩ : syracuseStep 2909903 = 4364855) B4364855
theorem B1939935 : Blo 1939435 1939935 := bstep (se 1 (by rfl) ⟨1454951, by rfl⟩ : syracuseStep 1939935 = 2909903) B2909903
theorem B2909909 : Blo 1939435 2909909 := bbase (se 7 (by rfl) ⟨34100, by rfl⟩ : syracuseStep 2909909 = 68201) (by norm_num)
theorem B1939939 : Blo 1939435 1939939 := bstep (se 1 (by rfl) ⟨1454954, by rfl⟩ : syracuseStep 1939939 = 2909909) B2909909
theorem B4143221 : Blo 1939435 4143221 := bbase (se 5 (by rfl) ⟨194213, by rfl⟩ : syracuseStep 4143221 = 388427) (by norm_num)
theorem B2762147 : Blo 1939435 2762147 := bstep (se 1 (by rfl) ⟨2071610, by rfl⟩ : syracuseStep 2762147 = 4143221) B4143221
theorem B7365725 : Blo 1939435 7365725 := bstep (se 3 (by rfl) ⟨1381073, by rfl⟩ : syracuseStep 7365725 = 2762147) B2762147
theorem B4910483 : Blo 1939435 4910483 := bstep (se 1 (by rfl) ⟨3682862, by rfl⟩ : syracuseStep 4910483 = 7365725) B7365725
theorem B3273655 : Blo 1939435 3273655 := bstep (se 1 (by rfl) ⟨2455241, by rfl⟩ : syracuseStep 3273655 = 4910483) B4910483
theorem B4364873 : Blo 1939435 4364873 := bstep (se 2 (by rfl) ⟨1636827, by rfl⟩ : syracuseStep 4364873 = 3273655) B3273655
theorem B2909915 : Blo 1939435 2909915 := bstep (se 1 (by rfl) ⟨2182436, by rfl⟩ : syracuseStep 2909915 = 4364873) B4364873
theorem B1939943 : Blo 1939435 1939943 := bstep (se 1 (by rfl) ⟨1454957, by rfl⟩ : syracuseStep 1939943 = 2909915) B2909915
theorem B2182441 : Blo 1939435 2182441 := bbase (se 2 (by rfl) ⟨818415, by rfl⟩ : syracuseStep 2182441 = 1636831) (by norm_num)
theorem B2909921 : Blo 1939435 2909921 := bstep (se 2 (by rfl) ⟨1091220, by rfl⟩ : syracuseStep 2909921 = 2182441) B2182441
theorem B1939947 : Blo 1939435 1939947 := bstep (se 1 (by rfl) ⟨1454960, by rfl⟩ : syracuseStep 1939947 = 2909921) B2909921
theorem B2621893 : Blo 1939435 2621893 := bbase (se 4 (by rfl) ⟨245802, by rfl⟩ : syracuseStep 2621893 = 491605) (by norm_num)
theorem B3495857 : Blo 1939435 3495857 := bstep (se 2 (by rfl) ⟨1310946, by rfl⟩ : syracuseStep 3495857 = 2621893) B2621893
theorem B9322285 : Blo 1939435 9322285 := bstep (se 3 (by rfl) ⟨1747928, by rfl⟩ : syracuseStep 9322285 = 3495857) B3495857
theorem B12429713 : Blo 1939435 12429713 := bstep (se 2 (by rfl) ⟨4661142, by rfl⟩ : syracuseStep 12429713 = 9322285) B9322285
theorem B8286475 : Blo 1939435 8286475 := bstep (se 1 (by rfl) ⟨6214856, by rfl⟩ : syracuseStep 8286475 = 12429713) B12429713
theorem B11048633 : Blo 1939435 11048633 := bstep (se 2 (by rfl) ⟨4143237, by rfl⟩ : syracuseStep 11048633 = 8286475) B8286475
theorem B7365755 : Blo 1939435 7365755 := bstep (se 1 (by rfl) ⟨5524316, by rfl⟩ : syracuseStep 7365755 = 11048633) B11048633
theorem B4910503 : Blo 1939435 4910503 := bstep (se 1 (by rfl) ⟨3682877, by rfl⟩ : syracuseStep 4910503 = 7365755) B7365755
theorem B6547337 : Blo 1939435 6547337 := bstep (se 2 (by rfl) ⟨2455251, by rfl⟩ : syracuseStep 6547337 = 4910503) B4910503
theorem B4364891 : Blo 1939435 4364891 := bstep (se 1 (by rfl) ⟨3273668, by rfl⟩ : syracuseStep 4364891 = 6547337) B6547337
theorem B2909927 : Blo 1939435 2909927 := bstep (se 1 (by rfl) ⟨2182445, by rfl⟩ : syracuseStep 2909927 = 4364891) B4364891
theorem B1939951 : Blo 1939435 1939951 := bstep (se 1 (by rfl) ⟨1454963, by rfl⟩ : syracuseStep 1939951 = 2909927) B2909927
theorem B2909933 : Blo 1939435 2909933 := bbase (se 3 (by rfl) ⟨545612, by rfl⟩ : syracuseStep 2909933 = 1091225) (by norm_num)
theorem B1939955 : Blo 1939435 1939955 := bstep (se 1 (by rfl) ⟨1454966, by rfl⟩ : syracuseStep 1939955 = 2909933) B2909933
theorem B4364909 : Blo 1939435 4364909 := bbase (se 3 (by rfl) ⟨818420, by rfl⟩ : syracuseStep 4364909 = 1636841) (by norm_num)
theorem B2909939 : Blo 1939435 2909939 := bstep (se 1 (by rfl) ⟨2182454, by rfl⟩ : syracuseStep 2909939 = 4364909) B4364909
theorem B1939959 : Blo 1939435 1939959 := bstep (se 1 (by rfl) ⟨1454969, by rfl⟩ : syracuseStep 1939959 = 2909939) B2909939
theorem B3682901 : Blo 1939435 3682901 := bbase (se 8 (by rfl) ⟨21579, by rfl⟩ : syracuseStep 3682901 = 43159) (by norm_num)
theorem B2455267 : Blo 1939435 2455267 := bstep (se 1 (by rfl) ⟨1841450, by rfl⟩ : syracuseStep 2455267 = 3682901) B3682901
theorem B3273689 : Blo 1939435 3273689 := bstep (se 2 (by rfl) ⟨1227633, by rfl⟩ : syracuseStep 3273689 = 2455267) B2455267
theorem B2182459 : Blo 1939435 2182459 := bstep (se 1 (by rfl) ⟨1636844, by rfl⟩ : syracuseStep 2182459 = 3273689) B3273689
theorem B2909945 : Blo 1939435 2909945 := bstep (se 2 (by rfl) ⟨1091229, by rfl⟩ : syracuseStep 2909945 = 2182459) B2182459
theorem B1939963 : Blo 1939435 1939963 := bstep (se 1 (by rfl) ⟨1454972, by rfl⟩ : syracuseStep 1939963 = 2909945) B2909945
theorem B55934165 : Blo 1939435 55934165 := bbase (se 7 (by rfl) ⟨655478, by rfl⟩ : syracuseStep 55934165 = 1310957) (by norm_num)
theorem B37289443 : Blo 1939435 37289443 := bstep (se 1 (by rfl) ⟨27967082, by rfl⟩ : syracuseStep 37289443 = 55934165) B55934165
theorem B49719257 : Blo 1939435 49719257 := bstep (se 2 (by rfl) ⟨18644721, by rfl⟩ : syracuseStep 49719257 = 37289443) B37289443
theorem B33146171 : Blo 1939435 33146171 := bstep (se 1 (by rfl) ⟨24859628, by rfl⟩ : syracuseStep 33146171 = 49719257) B49719257
theorem B22097447 : Blo 1939435 22097447 := bstep (se 1 (by rfl) ⟨16573085, by rfl⟩ : syracuseStep 22097447 = 33146171) B33146171
theorem B14731631 : Blo 1939435 14731631 := bstep (se 1 (by rfl) ⟨11048723, by rfl⟩ : syracuseStep 14731631 = 22097447) B22097447
theorem B9821087 : Blo 1939435 9821087 := bstep (se 1 (by rfl) ⟨7365815, by rfl⟩ : syracuseStep 9821087 = 14731631) B14731631
theorem B6547391 : Blo 1939435 6547391 := bstep (se 1 (by rfl) ⟨4910543, by rfl⟩ : syracuseStep 6547391 = 9821087) B9821087
theorem B4364927 : Blo 1939435 4364927 := bstep (se 1 (by rfl) ⟨3273695, by rfl⟩ : syracuseStep 4364927 = 6547391) B6547391
theorem B2909951 : Blo 1939435 2909951 := bstep (se 1 (by rfl) ⟨2182463, by rfl⟩ : syracuseStep 2909951 = 4364927) B4364927
theorem B1939967 : Blo 1939435 1939967 := bstep (se 1 (by rfl) ⟨1454975, by rfl⟩ : syracuseStep 1939967 = 2909951) B2909951
theorem B2909957 : Blo 1939435 2909957 := bbase (se 4 (by rfl) ⟨272808, by rfl⟩ : syracuseStep 2909957 = 545617) (by norm_num)
theorem B1939971 : Blo 1939435 1939971 := bstep (se 1 (by rfl) ⟨1454978, by rfl⟩ : syracuseStep 1939971 = 2909957) B2909957
theorem B3273709 : Blo 1939435 3273709 := bbase (se 3 (by rfl) ⟨613820, by rfl⟩ : syracuseStep 3273709 = 1227641) (by norm_num)
theorem B4364945 : Blo 1939435 4364945 := bstep (se 2 (by rfl) ⟨1636854, by rfl⟩ : syracuseStep 4364945 = 3273709) B3273709
theorem B2909963 : Blo 1939435 2909963 := bstep (se 1 (by rfl) ⟨2182472, by rfl⟩ : syracuseStep 2909963 = 4364945) B4364945
theorem B1939975 : Blo 1939435 1939975 := bstep (se 1 (by rfl) ⟨1454981, by rfl⟩ : syracuseStep 1939975 = 2909963) B2909963
theorem B2182477 : Blo 1939435 2182477 := bbase (se 3 (by rfl) ⟨409214, by rfl⟩ : syracuseStep 2182477 = 818429) (by norm_num)
theorem B2909969 : Blo 1939435 2909969 := bstep (se 2 (by rfl) ⟨1091238, by rfl⟩ : syracuseStep 2909969 = 2182477) B2182477
theorem B1939979 : Blo 1939435 1939979 := bstep (se 1 (by rfl) ⟨1454984, by rfl⟩ : syracuseStep 1939979 = 2909969) B2909969
theorem B6547445 : Blo 1939435 6547445 := bbase (se 5 (by rfl) ⟨306911, by rfl⟩ : syracuseStep 6547445 = 613823) (by norm_num)
theorem B4364963 : Blo 1939435 4364963 := bstep (se 1 (by rfl) ⟨3273722, by rfl⟩ : syracuseStep 4364963 = 6547445) B6547445
theorem B2909975 : Blo 1939435 2909975 := bstep (se 1 (by rfl) ⟨2182481, by rfl⟩ : syracuseStep 2909975 = 4364963) B4364963
theorem B1939983 : Blo 1939435 1939983 := bstep (se 1 (by rfl) ⟨1454987, by rfl⟩ : syracuseStep 1939983 = 2909975) B2909975
theorem B2909981 : Blo 1939435 2909981 := bbase (se 3 (by rfl) ⟨545621, by rfl⟩ : syracuseStep 2909981 = 1091243) (by norm_num)
theorem B1939987 : Blo 1939435 1939987 := bstep (se 1 (by rfl) ⟨1454990, by rfl⟩ : syracuseStep 1939987 = 2909981) B2909981
theorem B4364981 : Blo 1939435 4364981 := bbase (se 5 (by rfl) ⟨204608, by rfl⟩ : syracuseStep 4364981 = 409217) (by norm_num)
theorem B2909987 : Blo 1939435 2909987 := bstep (se 1 (by rfl) ⟨2182490, by rfl⟩ : syracuseStep 2909987 = 4364981) B4364981
theorem B1939991 : Blo 1939435 1939991 := bstep (se 1 (by rfl) ⟨1454993, by rfl⟩ : syracuseStep 1939991 = 2909987) B2909987
theorem B11048885 : Blo 1939435 11048885 := bbase (se 5 (by rfl) ⟨517916, by rfl⟩ : syracuseStep 11048885 = 1035833) (by norm_num)
theorem B7365923 : Blo 1939435 7365923 := bstep (se 1 (by rfl) ⟨5524442, by rfl⟩ : syracuseStep 7365923 = 11048885) B11048885
theorem B4910615 : Blo 1939435 4910615 := bstep (se 1 (by rfl) ⟨3682961, by rfl⟩ : syracuseStep 4910615 = 7365923) B7365923
theorem B3273743 : Blo 1939435 3273743 := bstep (se 1 (by rfl) ⟨2455307, by rfl⟩ : syracuseStep 3273743 = 4910615) B4910615
theorem B2182495 : Blo 1939435 2182495 := bstep (se 1 (by rfl) ⟨1636871, by rfl⟩ : syracuseStep 2182495 = 3273743) B3273743
theorem B2909993 : Blo 1939435 2909993 := bstep (se 2 (by rfl) ⟨1091247, by rfl⟩ : syracuseStep 2909993 = 2182495) B2182495
theorem B1939995 : Blo 1939435 1939995 := bstep (se 1 (by rfl) ⟨1454996, by rfl⟩ : syracuseStep 1939995 = 2909993) B2909993
theorem B5524453 : Blo 1939435 5524453 := bbase (se 4 (by rfl) ⟨517917, by rfl⟩ : syracuseStep 5524453 = 1035835) (by norm_num)
theorem B7365937 : Blo 1939435 7365937 := bstep (se 2 (by rfl) ⟨2762226, by rfl⟩ : syracuseStep 7365937 = 5524453) B5524453
theorem B9821249 : Blo 1939435 9821249 := bstep (se 2 (by rfl) ⟨3682968, by rfl⟩ : syracuseStep 9821249 = 7365937) B7365937
theorem B6547499 : Blo 1939435 6547499 := bstep (se 1 (by rfl) ⟨4910624, by rfl⟩ : syracuseStep 6547499 = 9821249) B9821249
theorem B4364999 : Blo 1939435 4364999 := bstep (se 1 (by rfl) ⟨3273749, by rfl⟩ : syracuseStep 4364999 = 6547499) B6547499
theorem B2909999 : Blo 1939435 2909999 := bstep (se 1 (by rfl) ⟨2182499, by rfl⟩ : syracuseStep 2909999 = 4364999) B4364999
theorem B1939999 : Blo 1939435 1939999 := bstep (se 1 (by rfl) ⟨1454999, by rfl⟩ : syracuseStep 1939999 = 2909999) B2909999
theorem B2910005 : Blo 1939435 2910005 := bbase (se 5 (by rfl) ⟨136406, by rfl⟩ : syracuseStep 2910005 = 272813) (by norm_num)
theorem B1940003 : Blo 1939435 1940003 := bstep (se 1 (by rfl) ⟨1455002, by rfl⟩ : syracuseStep 1940003 = 2910005) B2910005
theorem B4910645 : Blo 1939435 4910645 := bbase (se 5 (by rfl) ⟨230186, by rfl⟩ : syracuseStep 4910645 = 460373) (by norm_num)
theorem B3273763 : Blo 1939435 3273763 := bstep (se 1 (by rfl) ⟨2455322, by rfl⟩ : syracuseStep 3273763 = 4910645) B4910645
theorem B4365017 : Blo 1939435 4365017 := bstep (se 2 (by rfl) ⟨1636881, by rfl⟩ : syracuseStep 4365017 = 3273763) B3273763
theorem B2910011 : Blo 1939435 2910011 := bstep (se 1 (by rfl) ⟨2182508, by rfl⟩ : syracuseStep 2910011 = 4365017) B4365017
theorem B1940007 : Blo 1939435 1940007 := bstep (se 1 (by rfl) ⟨1455005, by rfl⟩ : syracuseStep 1940007 = 2910011) B2910011
theorem B2182513 : Blo 1939435 2182513 := bbase (se 2 (by rfl) ⟨818442, by rfl⟩ : syracuseStep 2182513 = 1636885) (by norm_num)
theorem B2910017 : Blo 1939435 2910017 := bstep (se 2 (by rfl) ⟨1091256, by rfl⟩ : syracuseStep 2910017 = 2182513) B2182513
theorem B1940011 : Blo 1939435 1940011 := bstep (se 1 (by rfl) ⟨1455008, by rfl⟩ : syracuseStep 1940011 = 2910017) B2910017
theorem B3495973 : Blo 1939435 3495973 := bbase (se 4 (by rfl) ⟨327747, by rfl⟩ : syracuseStep 3495973 = 655495) (by norm_num)
theorem B4661297 : Blo 1939435 4661297 := bstep (se 2 (by rfl) ⟨1747986, by rfl⟩ : syracuseStep 4661297 = 3495973) B3495973
theorem B3107531 : Blo 1939435 3107531 := bstep (se 1 (by rfl) ⟨2330648, by rfl⟩ : syracuseStep 3107531 = 4661297) B4661297
theorem B8286749 : Blo 1939435 8286749 := bstep (se 3 (by rfl) ⟨1553765, by rfl⟩ : syracuseStep 8286749 = 3107531) B3107531
theorem B5524499 : Blo 1939435 5524499 := bstep (se 1 (by rfl) ⟨4143374, by rfl⟩ : syracuseStep 5524499 = 8286749) B8286749
theorem B3682999 : Blo 1939435 3682999 := bstep (se 1 (by rfl) ⟨2762249, by rfl⟩ : syracuseStep 3682999 = 5524499) B5524499
theorem B4910665 : Blo 1939435 4910665 := bstep (se 2 (by rfl) ⟨1841499, by rfl⟩ : syracuseStep 4910665 = 3682999) B3682999
theorem B6547553 : Blo 1939435 6547553 := bstep (se 2 (by rfl) ⟨2455332, by rfl⟩ : syracuseStep 6547553 = 4910665) B4910665
theorem B4365035 : Blo 1939435 4365035 := bstep (se 1 (by rfl) ⟨3273776, by rfl⟩ : syracuseStep 4365035 = 6547553) B6547553
theorem B2910023 : Blo 1939435 2910023 := bstep (se 1 (by rfl) ⟨2182517, by rfl⟩ : syracuseStep 2910023 = 4365035) B4365035
theorem B1940015 : Blo 1939435 1940015 := bstep (se 1 (by rfl) ⟨1455011, by rfl⟩ : syracuseStep 1940015 = 2910023) B2910023
theorem B2910029 : Blo 1939435 2910029 := bbase (se 3 (by rfl) ⟨545630, by rfl⟩ : syracuseStep 2910029 = 1091261) (by norm_num)
theorem B1940019 : Blo 1939435 1940019 := bstep (se 1 (by rfl) ⟨1455014, by rfl⟩ : syracuseStep 1940019 = 2910029) B2910029
theorem B4365053 : Blo 1939435 4365053 := bbase (se 3 (by rfl) ⟨818447, by rfl⟩ : syracuseStep 4365053 = 1636895) (by norm_num)
theorem B2910035 : Blo 1939435 2910035 := bstep (se 1 (by rfl) ⟨2182526, by rfl⟩ : syracuseStep 2910035 = 4365053) B4365053
theorem B1940023 : Blo 1939435 1940023 := bstep (se 1 (by rfl) ⟨1455017, by rfl⟩ : syracuseStep 1940023 = 2910035) B2910035
theorem B3273797 : Blo 1939435 3273797 := bbase (se 4 (by rfl) ⟨306918, by rfl⟩ : syracuseStep 3273797 = 613837) (by norm_num)
theorem B2182531 : Blo 1939435 2182531 := bstep (se 1 (by rfl) ⟨1636898, by rfl⟩ : syracuseStep 2182531 = 3273797) B3273797
theorem B2910041 : Blo 1939435 2910041 := bstep (se 2 (by rfl) ⟨1091265, by rfl⟩ : syracuseStep 2910041 = 2182531) B2182531
theorem B1940027 : Blo 1939435 1940027 := bstep (se 1 (by rfl) ⟨1455020, by rfl⟩ : syracuseStep 1940027 = 2910041) B2910041
theorem B14732117 : Blo 1939435 14732117 := bbase (se 9 (by rfl) ⟨43160, by rfl⟩ : syracuseStep 14732117 = 86321) (by norm_num)
theorem B9821411 : Blo 1939435 9821411 := bstep (se 1 (by rfl) ⟨7366058, by rfl⟩ : syracuseStep 9821411 = 14732117) B14732117
theorem B6547607 : Blo 1939435 6547607 := bstep (se 1 (by rfl) ⟨4910705, by rfl⟩ : syracuseStep 6547607 = 9821411) B9821411
theorem B4365071 : Blo 1939435 4365071 := bstep (se 1 (by rfl) ⟨3273803, by rfl⟩ : syracuseStep 4365071 = 6547607) B6547607
theorem B2910047 : Blo 1939435 2910047 := bstep (se 1 (by rfl) ⟨2182535, by rfl⟩ : syracuseStep 2910047 = 4365071) B4365071
theorem B1940031 : Blo 1939435 1940031 := bstep (se 1 (by rfl) ⟨1455023, by rfl⟩ : syracuseStep 1940031 = 2910047) B2910047
theorem B2910053 : Blo 1939435 2910053 := bbase (se 4 (by rfl) ⟨272817, by rfl⟩ : syracuseStep 2910053 = 545635) (by norm_num)
theorem B1940035 : Blo 1939435 1940035 := bstep (se 1 (by rfl) ⟨1455026, by rfl⟩ : syracuseStep 1940035 = 2910053) B2910053
theorem B3683045 : Blo 1939435 3683045 := bbase (se 4 (by rfl) ⟨345285, by rfl⟩ : syracuseStep 3683045 = 690571) (by norm_num)
theorem B2455363 : Blo 1939435 2455363 := bstep (se 1 (by rfl) ⟨1841522, by rfl⟩ : syracuseStep 2455363 = 3683045) B3683045
theorem B3273817 : Blo 1939435 3273817 := bstep (se 2 (by rfl) ⟨1227681, by rfl⟩ : syracuseStep 3273817 = 2455363) B2455363
theorem B4365089 : Blo 1939435 4365089 := bstep (se 2 (by rfl) ⟨1636908, by rfl⟩ : syracuseStep 4365089 = 3273817) B3273817
theorem B2910059 : Blo 1939435 2910059 := bstep (se 1 (by rfl) ⟨2182544, by rfl⟩ : syracuseStep 2910059 = 4365089) B4365089
theorem B1940039 : Blo 1939435 1940039 := bstep (se 1 (by rfl) ⟨1455029, by rfl⟩ : syracuseStep 1940039 = 2910059) B2910059
theorem B2182549 : Blo 1939435 2182549 := bbase (se 6 (by rfl) ⟨51153, by rfl⟩ : syracuseStep 2182549 = 102307) (by norm_num)
theorem B2910065 : Blo 1939435 2910065 := bstep (se 2 (by rfl) ⟨1091274, by rfl⟩ : syracuseStep 2910065 = 2182549) B2182549
theorem B1940043 : Blo 1939435 1940043 := bstep (se 1 (by rfl) ⟨1455032, by rfl⟩ : syracuseStep 1940043 = 2910065) B2910065
theorem B2455373 : Blo 1939435 2455373 := bbase (se 3 (by rfl) ⟨460382, by rfl⟩ : syracuseStep 2455373 = 920765) (by norm_num)
theorem B6547661 : Blo 1939435 6547661 := bstep (se 3 (by rfl) ⟨1227686, by rfl⟩ : syracuseStep 6547661 = 2455373) B2455373
theorem B4365107 : Blo 1939435 4365107 := bstep (se 1 (by rfl) ⟨3273830, by rfl⟩ : syracuseStep 4365107 = 6547661) B6547661
theorem B2910071 : Blo 1939435 2910071 := bstep (se 1 (by rfl) ⟨2182553, by rfl⟩ : syracuseStep 2910071 = 4365107) B4365107
theorem B1940047 : Blo 1939435 1940047 := bstep (se 1 (by rfl) ⟨1455035, by rfl⟩ : syracuseStep 1940047 = 2910071) B2910071
theorem B2910077 : Blo 1939435 2910077 := bbase (se 3 (by rfl) ⟨545639, by rfl⟩ : syracuseStep 2910077 = 1091279) (by norm_num)
theorem B1940051 : Blo 1939435 1940051 := bstep (se 1 (by rfl) ⟨1455038, by rfl⟩ : syracuseStep 1940051 = 2910077) B2910077
theorem B4365125 : Blo 1939435 4365125 := bbase (se 4 (by rfl) ⟨409230, by rfl⟩ : syracuseStep 4365125 = 818461) (by norm_num)
theorem B2910083 : Blo 1939435 2910083 := bstep (se 1 (by rfl) ⟨2182562, by rfl⟩ : syracuseStep 2910083 = 4365125) B4365125
theorem B1940055 : Blo 1939435 1940055 := bstep (se 1 (by rfl) ⟨1455041, by rfl⟩ : syracuseStep 1940055 = 2910083) B2910083
theorem B4143469 : Blo 1939435 4143469 := bbase (se 3 (by rfl) ⟨776900, by rfl⟩ : syracuseStep 4143469 = 1553801) (by norm_num)
theorem B5524625 : Blo 1939435 5524625 := bstep (se 2 (by rfl) ⟨2071734, by rfl⟩ : syracuseStep 5524625 = 4143469) B4143469
theorem B3683083 : Blo 1939435 3683083 := bstep (se 1 (by rfl) ⟨2762312, by rfl⟩ : syracuseStep 3683083 = 5524625) B5524625
theorem B4910777 : Blo 1939435 4910777 := bstep (se 2 (by rfl) ⟨1841541, by rfl⟩ : syracuseStep 4910777 = 3683083) B3683083
theorem B3273851 : Blo 1939435 3273851 := bstep (se 1 (by rfl) ⟨2455388, by rfl⟩ : syracuseStep 3273851 = 4910777) B4910777
theorem B2182567 : Blo 1939435 2182567 := bstep (se 1 (by rfl) ⟨1636925, by rfl⟩ : syracuseStep 2182567 = 3273851) B3273851
theorem B2910089 : Blo 1939435 2910089 := bstep (se 2 (by rfl) ⟨1091283, by rfl⟩ : syracuseStep 2910089 = 2182567) B2182567
theorem B1940059 : Blo 1939435 1940059 := bstep (se 1 (by rfl) ⟨1455044, by rfl⟩ : syracuseStep 1940059 = 2910089) B2910089
theorem B9821573 : Blo 1939435 9821573 := bbase (se 4 (by rfl) ⟨920772, by rfl⟩ : syracuseStep 9821573 = 1841545) (by norm_num)
theorem B6547715 : Blo 1939435 6547715 := bstep (se 1 (by rfl) ⟨4910786, by rfl⟩ : syracuseStep 6547715 = 9821573) B9821573
theorem B4365143 : Blo 1939435 4365143 := bstep (se 1 (by rfl) ⟨3273857, by rfl⟩ : syracuseStep 4365143 = 6547715) B6547715
theorem B2910095 : Blo 1939435 2910095 := bstep (se 1 (by rfl) ⟨2182571, by rfl⟩ : syracuseStep 2910095 = 4365143) B4365143
theorem B1940063 : Blo 1939435 1940063 := bstep (se 1 (by rfl) ⟨1455047, by rfl⟩ : syracuseStep 1940063 = 2910095) B2910095
theorem B2910101 : Blo 1939435 2910101 := bbase (se 6 (by rfl) ⟨68205, by rfl⟩ : syracuseStep 2910101 = 136411) (by norm_num)
theorem B1940067 : Blo 1939435 1940067 := bstep (se 1 (by rfl) ⟨1455050, by rfl⟩ : syracuseStep 1940067 = 2910101) B2910101
theorem B3107621 : Blo 1939435 3107621 := bbase (se 4 (by rfl) ⟨291339, by rfl⟩ : syracuseStep 3107621 = 582679) (by norm_num)
theorem B2071747 : Blo 1939435 2071747 := bstep (se 1 (by rfl) ⟨1553810, by rfl⟩ : syracuseStep 2071747 = 3107621) B3107621
theorem B11049317 : Blo 1939435 11049317 := bstep (se 4 (by rfl) ⟨1035873, by rfl⟩ : syracuseStep 11049317 = 2071747) B2071747
theorem B7366211 : Blo 1939435 7366211 := bstep (se 1 (by rfl) ⟨5524658, by rfl⟩ : syracuseStep 7366211 = 11049317) B11049317
theorem B4910807 : Blo 1939435 4910807 := bstep (se 1 (by rfl) ⟨3683105, by rfl⟩ : syracuseStep 4910807 = 7366211) B7366211
theorem B3273871 : Blo 1939435 3273871 := bstep (se 1 (by rfl) ⟨2455403, by rfl⟩ : syracuseStep 3273871 = 4910807) B4910807
theorem B4365161 : Blo 1939435 4365161 := bstep (se 2 (by rfl) ⟨1636935, by rfl⟩ : syracuseStep 4365161 = 3273871) B3273871
theorem B2910107 : Blo 1939435 2910107 := bstep (se 1 (by rfl) ⟨2182580, by rfl⟩ : syracuseStep 2910107 = 4365161) B4365161
theorem B1940071 : Blo 1939435 1940071 := bstep (se 1 (by rfl) ⟨1455053, by rfl⟩ : syracuseStep 1940071 = 2910107) B2910107
theorem B2182585 : Blo 1939435 2182585 := bbase (se 2 (by rfl) ⟨818469, by rfl⟩ : syracuseStep 2182585 = 1636939) (by norm_num)
theorem B2910113 : Blo 1939435 2910113 := bstep (se 2 (by rfl) ⟨1091292, by rfl⟩ : syracuseStep 2910113 = 2182585) B2182585
theorem B1940075 : Blo 1939435 1940075 := bstep (se 1 (by rfl) ⟨1455056, by rfl⟩ : syracuseStep 1940075 = 2910113) B2910113
theorem B9322901 : Blo 1939435 9322901 := bbase (se 6 (by rfl) ⟨218505, by rfl⟩ : syracuseStep 9322901 = 437011) (by norm_num)
theorem B6215267 : Blo 1939435 6215267 := bstep (se 1 (by rfl) ⟨4661450, by rfl⟩ : syracuseStep 6215267 = 9322901) B9322901
theorem B4143511 : Blo 1939435 4143511 := bstep (se 1 (by rfl) ⟨3107633, by rfl⟩ : syracuseStep 4143511 = 6215267) B6215267
theorem B5524681 : Blo 1939435 5524681 := bstep (se 2 (by rfl) ⟨2071755, by rfl⟩ : syracuseStep 5524681 = 4143511) B4143511
theorem B7366241 : Blo 1939435 7366241 := bstep (se 2 (by rfl) ⟨2762340, by rfl⟩ : syracuseStep 7366241 = 5524681) B5524681
theorem B4910827 : Blo 1939435 4910827 := bstep (se 1 (by rfl) ⟨3683120, by rfl⟩ : syracuseStep 4910827 = 7366241) B7366241
theorem B6547769 : Blo 1939435 6547769 := bstep (se 2 (by rfl) ⟨2455413, by rfl⟩ : syracuseStep 6547769 = 4910827) B4910827
theorem B4365179 : Blo 1939435 4365179 := bstep (se 1 (by rfl) ⟨3273884, by rfl⟩ : syracuseStep 4365179 = 6547769) B6547769
theorem B2910119 : Blo 1939435 2910119 := bstep (se 1 (by rfl) ⟨2182589, by rfl⟩ : syracuseStep 2910119 = 4365179) B4365179
theorem B1940079 : Blo 1939435 1940079 := bstep (se 1 (by rfl) ⟨1455059, by rfl⟩ : syracuseStep 1940079 = 2910119) B2910119
theorem B2910125 : Blo 1939435 2910125 := bbase (se 3 (by rfl) ⟨545648, by rfl⟩ : syracuseStep 2910125 = 1091297) (by norm_num)
theorem B1940083 : Blo 1939435 1940083 := bstep (se 1 (by rfl) ⟨1455062, by rfl⟩ : syracuseStep 1940083 = 2910125) B2910125
theorem B4365197 : Blo 1939435 4365197 := bbase (se 3 (by rfl) ⟨818474, by rfl⟩ : syracuseStep 4365197 = 1636949) (by norm_num)
theorem B2910131 : Blo 1939435 2910131 := bstep (se 1 (by rfl) ⟨2182598, by rfl⟩ : syracuseStep 2910131 = 4365197) B4365197
theorem B1940087 : Blo 1939435 1940087 := bstep (se 1 (by rfl) ⟨1455065, by rfl⟩ : syracuseStep 1940087 = 2910131) B2910131
theorem B2455429 : Blo 1939435 2455429 := bbase (se 4 (by rfl) ⟨230196, by rfl⟩ : syracuseStep 2455429 = 460393) (by norm_num)
theorem B3273905 : Blo 1939435 3273905 := bstep (se 2 (by rfl) ⟨1227714, by rfl⟩ : syracuseStep 3273905 = 2455429) B2455429
theorem B2182603 : Blo 1939435 2182603 := bstep (se 1 (by rfl) ⟨1636952, by rfl⟩ : syracuseStep 2182603 = 3273905) B3273905
theorem B2910137 : Blo 1939435 2910137 := bstep (se 2 (by rfl) ⟨1091301, by rfl⟩ : syracuseStep 2910137 = 2182603) B2182603
theorem B1940091 : Blo 1939435 1940091 := bstep (se 1 (by rfl) ⟨1455068, by rfl⟩ : syracuseStep 1940091 = 2910137) B2910137
theorem B24861269 : Blo 1939435 24861269 := bbase (se 8 (by rfl) ⟨145671, by rfl⟩ : syracuseStep 24861269 = 291343) (by norm_num)
theorem B16574179 : Blo 1939435 16574179 := bstep (se 1 (by rfl) ⟨12430634, by rfl⟩ : syracuseStep 16574179 = 24861269) B24861269
theorem B22098905 : Blo 1939435 22098905 := bstep (se 2 (by rfl) ⟨8287089, by rfl⟩ : syracuseStep 22098905 = 16574179) B16574179
theorem B14732603 : Blo 1939435 14732603 := bstep (se 1 (by rfl) ⟨11049452, by rfl⟩ : syracuseStep 14732603 = 22098905) B22098905
theorem B9821735 : Blo 1939435 9821735 := bstep (se 1 (by rfl) ⟨7366301, by rfl⟩ : syracuseStep 9821735 = 14732603) B14732603
theorem B6547823 : Blo 1939435 6547823 := bstep (se 1 (by rfl) ⟨4910867, by rfl⟩ : syracuseStep 6547823 = 9821735) B9821735
theorem B4365215 : Blo 1939435 4365215 := bstep (se 1 (by rfl) ⟨3273911, by rfl⟩ : syracuseStep 4365215 = 6547823) B6547823
theorem B2910143 : Blo 1939435 2910143 := bstep (se 1 (by rfl) ⟨2182607, by rfl⟩ : syracuseStep 2910143 = 4365215) B4365215
theorem B1940095 : Blo 1939435 1940095 := bstep (se 1 (by rfl) ⟨1455071, by rfl⟩ : syracuseStep 1940095 = 2910143) B2910143
theorem B2910149 : Blo 1939435 2910149 := bbase (se 4 (by rfl) ⟨272826, by rfl⟩ : syracuseStep 2910149 = 545653) (by norm_num)
theorem B1940099 : Blo 1939435 1940099 := bstep (se 1 (by rfl) ⟨1455074, by rfl⟩ : syracuseStep 1940099 = 2910149) B2910149
theorem B3273925 : Blo 1939435 3273925 := bbase (se 4 (by rfl) ⟨306930, by rfl⟩ : syracuseStep 3273925 = 613861) (by norm_num)
theorem B4365233 : Blo 1939435 4365233 := bstep (se 2 (by rfl) ⟨1636962, by rfl⟩ : syracuseStep 4365233 = 3273925) B3273925
theorem B2910155 : Blo 1939435 2910155 := bstep (se 1 (by rfl) ⟨2182616, by rfl⟩ : syracuseStep 2910155 = 4365233) B4365233
theorem B1940103 : Blo 1939435 1940103 := bstep (se 1 (by rfl) ⟨1455077, by rfl⟩ : syracuseStep 1940103 = 2910155) B2910155
theorem B2182621 : Blo 1939435 2182621 := bbase (se 3 (by rfl) ⟨409241, by rfl⟩ : syracuseStep 2182621 = 818483) (by norm_num)
theorem B2910161 : Blo 1939435 2910161 := bstep (se 2 (by rfl) ⟨1091310, by rfl⟩ : syracuseStep 2910161 = 2182621) B2182621
theorem B1940107 : Blo 1939435 1940107 := bstep (se 1 (by rfl) ⟨1455080, by rfl⟩ : syracuseStep 1940107 = 2910161) B2910161
theorem B6547877 : Blo 1939435 6547877 := bbase (se 4 (by rfl) ⟨613863, by rfl⟩ : syracuseStep 6547877 = 1227727) (by norm_num)
theorem B4365251 : Blo 1939435 4365251 := bstep (se 1 (by rfl) ⟨3273938, by rfl⟩ : syracuseStep 4365251 = 6547877) B6547877
theorem B2910167 : Blo 1939435 2910167 := bstep (se 1 (by rfl) ⟨2182625, by rfl⟩ : syracuseStep 2910167 = 4365251) B4365251
theorem B1940111 : Blo 1939435 1940111 := bstep (se 1 (by rfl) ⟨1455083, by rfl⟩ : syracuseStep 1940111 = 2910167) B2910167
theorem B2910173 : Blo 1939435 2910173 := bbase (se 3 (by rfl) ⟨545657, by rfl⟩ : syracuseStep 2910173 = 1091315) (by norm_num)
theorem B1940115 : Blo 1939435 1940115 := bstep (se 1 (by rfl) ⟨1455086, by rfl⟩ : syracuseStep 1940115 = 2910173) B2910173
theorem B4365269 : Blo 1939435 4365269 := bbase (se 7 (by rfl) ⟨51155, by rfl⟩ : syracuseStep 4365269 = 102311) (by norm_num)
theorem B2910179 : Blo 1939435 2910179 := bstep (se 1 (by rfl) ⟨2182634, by rfl⟩ : syracuseStep 2910179 = 4365269) B4365269
theorem B1940119 : Blo 1939435 1940119 := bstep (se 1 (by rfl) ⟨1455089, by rfl⟩ : syracuseStep 1940119 = 2910179) B2910179
theorem B2800093 : Blo 1939435 2800093 := bbase (se 3 (by rfl) ⟨525017, by rfl⟩ : syracuseStep 2800093 = 1050035) (by norm_num)
theorem B3733457 : Blo 1939435 3733457 := bstep (se 2 (by rfl) ⟨1400046, by rfl⟩ : syracuseStep 3733457 = 2800093) B2800093
theorem B9955885 : Blo 1939435 9955885 := bstep (se 3 (by rfl) ⟨1866728, by rfl⟩ : syracuseStep 9955885 = 3733457) B3733457
theorem B13274513 : Blo 1939435 13274513 := bstep (se 2 (by rfl) ⟨4977942, by rfl⟩ : syracuseStep 13274513 = 9955885) B9955885
theorem B8849675 : Blo 1939435 8849675 := bstep (se 1 (by rfl) ⟨6637256, by rfl⟩ : syracuseStep 8849675 = 13274513) B13274513
theorem B23599133 : Blo 1939435 23599133 := bstep (se 3 (by rfl) ⟨4424837, by rfl⟩ : syracuseStep 23599133 = 8849675) B8849675
theorem B15732755 : Blo 1939435 15732755 := bstep (se 1 (by rfl) ⟨11799566, by rfl⟩ : syracuseStep 15732755 = 23599133) B23599133
theorem B10488503 : Blo 1939435 10488503 := bstep (se 1 (by rfl) ⟨7866377, by rfl⟩ : syracuseStep 10488503 = 15732755) B15732755
theorem B6992335 : Blo 1939435 6992335 := bstep (se 1 (by rfl) ⟨5244251, by rfl⟩ : syracuseStep 6992335 = 10488503) B10488503
theorem B9323113 : Blo 1939435 9323113 := bstep (se 2 (by rfl) ⟨3496167, by rfl⟩ : syracuseStep 9323113 = 6992335) B6992335
theorem B12430817 : Blo 1939435 12430817 := bstep (se 2 (by rfl) ⟨4661556, by rfl⟩ : syracuseStep 12430817 = 9323113) B9323113
theorem B8287211 : Blo 1939435 8287211 := bstep (se 1 (by rfl) ⟨6215408, by rfl⟩ : syracuseStep 8287211 = 12430817) B12430817
theorem B5524807 : Blo 1939435 5524807 := bstep (se 1 (by rfl) ⟨4143605, by rfl⟩ : syracuseStep 5524807 = 8287211) B8287211
theorem B7366409 : Blo 1939435 7366409 := bstep (se 2 (by rfl) ⟨2762403, by rfl⟩ : syracuseStep 7366409 = 5524807) B5524807
theorem B4910939 : Blo 1939435 4910939 := bstep (se 1 (by rfl) ⟨3683204, by rfl⟩ : syracuseStep 4910939 = 7366409) B7366409
theorem B3273959 : Blo 1939435 3273959 := bstep (se 1 (by rfl) ⟨2455469, by rfl⟩ : syracuseStep 3273959 = 4910939) B4910939
theorem B2182639 : Blo 1939435 2182639 := bstep (se 1 (by rfl) ⟨1636979, by rfl⟩ : syracuseStep 2182639 = 3273959) B3273959
theorem B2910185 : Blo 1939435 2910185 := bstep (se 2 (by rfl) ⟨1091319, by rfl⟩ : syracuseStep 2910185 = 2182639) B2182639
theorem B1940123 : Blo 1939435 1940123 := bstep (se 1 (by rfl) ⟨1455092, by rfl⟩ : syracuseStep 1940123 = 2910185) B2910185
theorem B16574453 : Blo 1939435 16574453 := bbase (se 5 (by rfl) ⟨776927, by rfl⟩ : syracuseStep 16574453 = 1553855) (by norm_num)
theorem B11049635 : Blo 1939435 11049635 := bstep (se 1 (by rfl) ⟨8287226, by rfl⟩ : syracuseStep 11049635 = 16574453) B16574453
theorem B7366423 : Blo 1939435 7366423 := bstep (se 1 (by rfl) ⟨5524817, by rfl⟩ : syracuseStep 7366423 = 11049635) B11049635
theorem B9821897 : Blo 1939435 9821897 := bstep (se 2 (by rfl) ⟨3683211, by rfl⟩ : syracuseStep 9821897 = 7366423) B7366423
theorem B6547931 : Blo 1939435 6547931 := bstep (se 1 (by rfl) ⟨4910948, by rfl⟩ : syracuseStep 6547931 = 9821897) B9821897
theorem B4365287 : Blo 1939435 4365287 := bstep (se 1 (by rfl) ⟨3273965, by rfl⟩ : syracuseStep 4365287 = 6547931) B6547931
theorem B2910191 : Blo 1939435 2910191 := bstep (se 1 (by rfl) ⟨2182643, by rfl⟩ : syracuseStep 2910191 = 4365287) B4365287
theorem B1940127 : Blo 1939435 1940127 := bstep (se 1 (by rfl) ⟨1455095, by rfl⟩ : syracuseStep 1940127 = 2910191) B2910191
theorem B2910197 : Blo 1939435 2910197 := bbase (se 5 (by rfl) ⟨136415, by rfl⟩ : syracuseStep 2910197 = 272831) (by norm_num)
theorem B1940131 : Blo 1939435 1940131 := bstep (se 1 (by rfl) ⟨1455098, by rfl⟩ : syracuseStep 1940131 = 2910197) B2910197
theorem B13984757 : Blo 1939435 13984757 := bbase (se 5 (by rfl) ⟨655535, by rfl⟩ : syracuseStep 13984757 = 1311071) (by norm_num)
theorem B9323171 : Blo 1939435 9323171 := bstep (se 1 (by rfl) ⟨6992378, by rfl⟩ : syracuseStep 9323171 = 13984757) B13984757
theorem B6215447 : Blo 1939435 6215447 := bstep (se 1 (by rfl) ⟨4661585, by rfl⟩ : syracuseStep 6215447 = 9323171) B9323171
theorem B4143631 : Blo 1939435 4143631 := bstep (se 1 (by rfl) ⟨3107723, by rfl⟩ : syracuseStep 4143631 = 6215447) B6215447
theorem B5524841 : Blo 1939435 5524841 := bstep (se 2 (by rfl) ⟨2071815, by rfl⟩ : syracuseStep 5524841 = 4143631) B4143631
theorem B3683227 : Blo 1939435 3683227 := bstep (se 1 (by rfl) ⟨2762420, by rfl⟩ : syracuseStep 3683227 = 5524841) B5524841
theorem B4910969 : Blo 1939435 4910969 := bstep (se 2 (by rfl) ⟨1841613, by rfl⟩ : syracuseStep 4910969 = 3683227) B3683227
theorem B3273979 : Blo 1939435 3273979 := bstep (se 1 (by rfl) ⟨2455484, by rfl⟩ : syracuseStep 3273979 = 4910969) B4910969
theorem B4365305 : Blo 1939435 4365305 := bstep (se 2 (by rfl) ⟨1636989, by rfl⟩ : syracuseStep 4365305 = 3273979) B3273979
theorem B2910203 : Blo 1939435 2910203 := bstep (se 1 (by rfl) ⟨2182652, by rfl⟩ : syracuseStep 2910203 = 4365305) B4365305
theorem B1940135 : Blo 1939435 1940135 := bstep (se 1 (by rfl) ⟨1455101, by rfl⟩ : syracuseStep 1940135 = 2910203) B2910203
theorem B2182657 : Blo 1939435 2182657 := bbase (se 2 (by rfl) ⟨818496, by rfl⟩ : syracuseStep 2182657 = 1636993) (by norm_num)
theorem B2910209 : Blo 1939435 2910209 := bstep (se 2 (by rfl) ⟨1091328, by rfl⟩ : syracuseStep 2910209 = 2182657) B2182657
theorem B1940139 : Blo 1939435 1940139 := bstep (se 1 (by rfl) ⟨1455104, by rfl⟩ : syracuseStep 1940139 = 2910209) B2910209
theorem B4910989 : Blo 1939435 4910989 := bbase (se 3 (by rfl) ⟨920810, by rfl⟩ : syracuseStep 4910989 = 1841621) (by norm_num)
theorem B6547985 : Blo 1939435 6547985 := bstep (se 2 (by rfl) ⟨2455494, by rfl⟩ : syracuseStep 6547985 = 4910989) B4910989
theorem B4365323 : Blo 1939435 4365323 := bstep (se 1 (by rfl) ⟨3273992, by rfl⟩ : syracuseStep 4365323 = 6547985) B6547985
theorem B2910215 : Blo 1939435 2910215 := bstep (se 1 (by rfl) ⟨2182661, by rfl⟩ : syracuseStep 2910215 = 4365323) B4365323
theorem B1940143 : Blo 1939435 1940143 := bstep (se 1 (by rfl) ⟨1455107, by rfl⟩ : syracuseStep 1940143 = 2910215) B2910215
theorem B2910221 : Blo 1939435 2910221 := bbase (se 3 (by rfl) ⟨545666, by rfl⟩ : syracuseStep 2910221 = 1091333) (by norm_num)
theorem B1940147 : Blo 1939435 1940147 := bstep (se 1 (by rfl) ⟨1455110, by rfl⟩ : syracuseStep 1940147 = 2910221) B2910221
theorem B4365341 : Blo 1939435 4365341 := bbase (se 3 (by rfl) ⟨818501, by rfl⟩ : syracuseStep 4365341 = 1637003) (by norm_num)
theorem B2910227 : Blo 1939435 2910227 := bstep (se 1 (by rfl) ⟨2182670, by rfl⟩ : syracuseStep 2910227 = 4365341) B4365341
theorem B1940151 : Blo 1939435 1940151 := bstep (se 1 (by rfl) ⟨1455113, by rfl⟩ : syracuseStep 1940151 = 2910227) B2910227
theorem B3274013 : Blo 1939435 3274013 := bbase (se 3 (by rfl) ⟨613877, by rfl⟩ : syracuseStep 3274013 = 1227755) (by norm_num)
theorem B2182675 : Blo 1939435 2182675 := bstep (se 1 (by rfl) ⟨1637006, by rfl⟩ : syracuseStep 2182675 = 3274013) B3274013
theorem B2910233 : Blo 1939435 2910233 := bstep (se 2 (by rfl) ⟨1091337, by rfl⟩ : syracuseStep 2910233 = 2182675) B2182675
theorem B1940155 : Blo 1939435 1940155 := bstep (se 1 (by rfl) ⟨1455116, by rfl⟩ : syracuseStep 1940155 = 2910233) B2910233
theorem B2330821 : Blo 1939435 2330821 := bbase (se 4 (by rfl) ⟨218514, by rfl⟩ : syracuseStep 2330821 = 437029) (by norm_num)
theorem B12431045 : Blo 1939435 12431045 := bstep (se 4 (by rfl) ⟨1165410, by rfl⟩ : syracuseStep 12431045 = 2330821) B2330821
theorem B8287363 : Blo 1939435 8287363 := bstep (se 1 (by rfl) ⟨6215522, by rfl⟩ : syracuseStep 8287363 = 12431045) B12431045
theorem B11049817 : Blo 1939435 11049817 := bstep (se 2 (by rfl) ⟨4143681, by rfl⟩ : syracuseStep 11049817 = 8287363) B8287363
theorem B14733089 : Blo 1939435 14733089 := bstep (se 2 (by rfl) ⟨5524908, by rfl⟩ : syracuseStep 14733089 = 11049817) B11049817
theorem B9822059 : Blo 1939435 9822059 := bstep (se 1 (by rfl) ⟨7366544, by rfl⟩ : syracuseStep 9822059 = 14733089) B14733089
theorem B6548039 : Blo 1939435 6548039 := bstep (se 1 (by rfl) ⟨4911029, by rfl⟩ : syracuseStep 6548039 = 9822059) B9822059
theorem B4365359 : Blo 1939435 4365359 := bstep (se 1 (by rfl) ⟨3274019, by rfl⟩ : syracuseStep 4365359 = 6548039) B6548039
theorem B2910239 : Blo 1939435 2910239 := bstep (se 1 (by rfl) ⟨2182679, by rfl⟩ : syracuseStep 2910239 = 4365359) B4365359
theorem B1940159 : Blo 1939435 1940159 := bstep (se 1 (by rfl) ⟨1455119, by rfl⟩ : syracuseStep 1940159 = 2910239) B2910239
theorem B2910245 : Blo 1939435 2910245 := bbase (se 4 (by rfl) ⟨272835, by rfl⟩ : syracuseStep 2910245 = 545671) (by norm_num)
theorem B1940163 : Blo 1939435 1940163 := bstep (se 1 (by rfl) ⟨1455122, by rfl⟩ : syracuseStep 1940163 = 2910245) B2910245
theorem B2455525 : Blo 1939435 2455525 := bbase (se 4 (by rfl) ⟨230205, by rfl⟩ : syracuseStep 2455525 = 460411) (by norm_num)
theorem B3274033 : Blo 1939435 3274033 := bstep (se 2 (by rfl) ⟨1227762, by rfl⟩ : syracuseStep 3274033 = 2455525) B2455525
theorem B4365377 : Blo 1939435 4365377 := bstep (se 2 (by rfl) ⟨1637016, by rfl⟩ : syracuseStep 4365377 = 3274033) B3274033
theorem B2910251 : Blo 1939435 2910251 := bstep (se 1 (by rfl) ⟨2182688, by rfl⟩ : syracuseStep 2910251 = 4365377) B4365377
theorem B1940167 : Blo 1939435 1940167 := bstep (se 1 (by rfl) ⟨1455125, by rfl⟩ : syracuseStep 1940167 = 2910251) B2910251
theorem B2182693 : Blo 1939435 2182693 := bbase (se 4 (by rfl) ⟨204627, by rfl⟩ : syracuseStep 2182693 = 409255) (by norm_num)
theorem B2910257 : Blo 1939435 2910257 := bstep (se 2 (by rfl) ⟨1091346, by rfl⟩ : syracuseStep 2910257 = 2182693) B2182693
theorem B1940171 : Blo 1939435 1940171 := bstep (se 1 (by rfl) ⟨1455128, by rfl⟩ : syracuseStep 1940171 = 2910257) B2910257
theorem B13985045 : Blo 1939435 13985045 := bbase (se 6 (by rfl) ⟨327774, by rfl⟩ : syracuseStep 13985045 = 655549) (by norm_num)
theorem B9323363 : Blo 1939435 9323363 := bstep (se 1 (by rfl) ⟨6992522, by rfl⟩ : syracuseStep 9323363 = 13985045) B13985045
theorem B6215575 : Blo 1939435 6215575 := bstep (se 1 (by rfl) ⟨4661681, by rfl⟩ : syracuseStep 6215575 = 9323363) B9323363
theorem B8287433 : Blo 1939435 8287433 := bstep (se 2 (by rfl) ⟨3107787, by rfl⟩ : syracuseStep 8287433 = 6215575) B6215575
theorem B5524955 : Blo 1939435 5524955 := bstep (se 1 (by rfl) ⟨4143716, by rfl⟩ : syracuseStep 5524955 = 8287433) B8287433
theorem B3683303 : Blo 1939435 3683303 := bstep (se 1 (by rfl) ⟨2762477, by rfl⟩ : syracuseStep 3683303 = 5524955) B5524955
theorem B2455535 : Blo 1939435 2455535 := bstep (se 1 (by rfl) ⟨1841651, by rfl⟩ : syracuseStep 2455535 = 3683303) B3683303
theorem B6548093 : Blo 1939435 6548093 := bstep (se 3 (by rfl) ⟨1227767, by rfl⟩ : syracuseStep 6548093 = 2455535) B2455535
theorem B4365395 : Blo 1939435 4365395 := bstep (se 1 (by rfl) ⟨3274046, by rfl⟩ : syracuseStep 4365395 = 6548093) B6548093
theorem B2910263 : Blo 1939435 2910263 := bstep (se 1 (by rfl) ⟨2182697, by rfl⟩ : syracuseStep 2910263 = 4365395) B4365395
theorem B1940175 : Blo 1939435 1940175 := bstep (se 1 (by rfl) ⟨1455131, by rfl⟩ : syracuseStep 1940175 = 2910263) B2910263
theorem B2910269 : Blo 1939435 2910269 := bbase (se 3 (by rfl) ⟨545675, by rfl⟩ : syracuseStep 2910269 = 1091351) (by norm_num)
theorem B1940179 : Blo 1939435 1940179 := bstep (se 1 (by rfl) ⟨1455134, by rfl⟩ : syracuseStep 1940179 = 2910269) B2910269
theorem B4365413 : Blo 1939435 4365413 := bbase (se 4 (by rfl) ⟨409257, by rfl⟩ : syracuseStep 4365413 = 818515) (by norm_num)
theorem B2910275 : Blo 1939435 2910275 := bstep (se 1 (by rfl) ⟨2182706, by rfl⟩ : syracuseStep 2910275 = 4365413) B4365413
theorem B1940183 : Blo 1939435 1940183 := bstep (se 1 (by rfl) ⟨1455137, by rfl⟩ : syracuseStep 1940183 = 2910275) B2910275
theorem B4911101 : Blo 1939435 4911101 := bbase (se 3 (by rfl) ⟨920831, by rfl⟩ : syracuseStep 4911101 = 1841663) (by norm_num)
theorem B3274067 : Blo 1939435 3274067 := bstep (se 1 (by rfl) ⟨2455550, by rfl⟩ : syracuseStep 3274067 = 4911101) B4911101
theorem B2182711 : Blo 1939435 2182711 := bstep (se 1 (by rfl) ⟨1637033, by rfl⟩ : syracuseStep 2182711 = 3274067) B3274067
theorem B2910281 : Blo 1939435 2910281 := bstep (se 2 (by rfl) ⟨1091355, by rfl⟩ : syracuseStep 2910281 = 2182711) B2182711
theorem B1940187 : Blo 1939435 1940187 := bstep (se 1 (by rfl) ⟨1455140, by rfl⟩ : syracuseStep 1940187 = 2910281) B2910281
theorem B3683333 : Blo 1939435 3683333 := bbase (se 4 (by rfl) ⟨345312, by rfl⟩ : syracuseStep 3683333 = 690625) (by norm_num)
theorem B9822221 : Blo 1939435 9822221 := bstep (se 3 (by rfl) ⟨1841666, by rfl⟩ : syracuseStep 9822221 = 3683333) B3683333
theorem B6548147 : Blo 1939435 6548147 := bstep (se 1 (by rfl) ⟨4911110, by rfl⟩ : syracuseStep 6548147 = 9822221) B9822221
theorem B4365431 : Blo 1939435 4365431 := bstep (se 1 (by rfl) ⟨3274073, by rfl⟩ : syracuseStep 4365431 = 6548147) B6548147
theorem B2910287 : Blo 1939435 2910287 := bstep (se 1 (by rfl) ⟨2182715, by rfl⟩ : syracuseStep 2910287 = 4365431) B4365431
theorem B1940191 : Blo 1939435 1940191 := bstep (se 1 (by rfl) ⟨1455143, by rfl⟩ : syracuseStep 1940191 = 2910287) B2910287
theorem B2910293 : Blo 1939435 2910293 := bbase (se 8 (by rfl) ⟨17052, by rfl⟩ : syracuseStep 2910293 = 34105) (by norm_num)
theorem B1940195 : Blo 1939435 1940195 := bstep (se 1 (by rfl) ⟨1455146, by rfl⟩ : syracuseStep 1940195 = 2910293) B2910293
theorem B29868821 : Blo 1939435 29868821 := bbase (se 6 (by rfl) ⟨700050, by rfl⟩ : syracuseStep 29868821 = 1400101) (by norm_num)
theorem B19912547 : Blo 1939435 19912547 := bstep (se 1 (by rfl) ⟨14934410, by rfl⟩ : syracuseStep 19912547 = 29868821) B29868821
theorem B13275031 : Blo 1939435 13275031 := bstep (se 1 (by rfl) ⟨9956273, by rfl⟩ : syracuseStep 13275031 = 19912547) B19912547
theorem B17700041 : Blo 1939435 17700041 := bstep (se 2 (by rfl) ⟨6637515, by rfl⟩ : syracuseStep 17700041 = 13275031) B13275031
theorem B11800027 : Blo 1939435 11800027 := bstep (se 1 (by rfl) ⟨8850020, by rfl⟩ : syracuseStep 11800027 = 17700041) B17700041
theorem B15733369 : Blo 1939435 15733369 := bstep (se 2 (by rfl) ⟨5900013, by rfl⟩ : syracuseStep 15733369 = 11800027) B11800027
theorem B20977825 : Blo 1939435 20977825 := bstep (se 2 (by rfl) ⟨7866684, by rfl⟩ : syracuseStep 20977825 = 15733369) B15733369
theorem B27970433 : Blo 1939435 27970433 := bstep (se 2 (by rfl) ⟨10488912, by rfl⟩ : syracuseStep 27970433 = 20977825) B20977825
theorem B18646955 : Blo 1939435 18646955 := bstep (se 1 (by rfl) ⟨13985216, by rfl⟩ : syracuseStep 18646955 = 27970433) B27970433
theorem B12431303 : Blo 1939435 12431303 := bstep (se 1 (by rfl) ⟨9323477, by rfl⟩ : syracuseStep 12431303 = 18646955) B18646955
theorem B8287535 : Blo 1939435 8287535 := bstep (se 1 (by rfl) ⟨6215651, by rfl⟩ : syracuseStep 8287535 = 12431303) B12431303
theorem B5525023 : Blo 1939435 5525023 := bstep (se 1 (by rfl) ⟨4143767, by rfl⟩ : syracuseStep 5525023 = 8287535) B8287535
theorem B7366697 : Blo 1939435 7366697 := bstep (se 2 (by rfl) ⟨2762511, by rfl⟩ : syracuseStep 7366697 = 5525023) B5525023
theorem B4911131 : Blo 1939435 4911131 := bstep (se 1 (by rfl) ⟨3683348, by rfl⟩ : syracuseStep 4911131 = 7366697) B7366697
theorem B3274087 : Blo 1939435 3274087 := bstep (se 1 (by rfl) ⟨2455565, by rfl⟩ : syracuseStep 3274087 = 4911131) B4911131
theorem B4365449 : Blo 1939435 4365449 := bstep (se 2 (by rfl) ⟨1637043, by rfl⟩ : syracuseStep 4365449 = 3274087) B3274087
theorem B2910299 : Blo 1939435 2910299 := bstep (se 1 (by rfl) ⟨2182724, by rfl⟩ : syracuseStep 2910299 = 4365449) B4365449
theorem B1940199 : Blo 1939435 1940199 := bstep (se 1 (by rfl) ⟨1455149, by rfl⟩ : syracuseStep 1940199 = 2910299) B2910299
theorem B2182729 : Blo 1939435 2182729 := bbase (se 2 (by rfl) ⟨818523, by rfl⟩ : syracuseStep 2182729 = 1637047) (by norm_num)
theorem B2910305 : Blo 1939435 2910305 := bstep (se 2 (by rfl) ⟨1091364, by rfl⟩ : syracuseStep 2910305 = 2182729) B2182729
theorem B1940203 : Blo 1939435 1940203 := bstep (se 1 (by rfl) ⟨1455152, by rfl⟩ : syracuseStep 1940203 = 2910305) B2910305
theorem B4978157 : Blo 1939435 4978157 := bbase (se 3 (by rfl) ⟨933404, by rfl⟩ : syracuseStep 4978157 = 1866809) (by norm_num)
theorem B13275085 : Blo 1939435 13275085 := bstep (se 3 (by rfl) ⟨2489078, by rfl⟩ : syracuseStep 13275085 = 4978157) B4978157
theorem B17700113 : Blo 1939435 17700113 := bstep (se 2 (by rfl) ⟨6637542, by rfl⟩ : syracuseStep 17700113 = 13275085) B13275085
theorem B11800075 : Blo 1939435 11800075 := bstep (se 1 (by rfl) ⟨8850056, by rfl⟩ : syracuseStep 11800075 = 17700113) B17700113
theorem B15733433 : Blo 1939435 15733433 := bstep (se 2 (by rfl) ⟨5900037, by rfl⟩ : syracuseStep 15733433 = 11800075) B11800075
theorem B10488955 : Blo 1939435 10488955 := bstep (se 1 (by rfl) ⟨7866716, by rfl⟩ : syracuseStep 10488955 = 15733433) B15733433
theorem B13985273 : Blo 1939435 13985273 := bstep (se 2 (by rfl) ⟨5244477, by rfl⟩ : syracuseStep 13985273 = 10488955) B10488955
theorem B9323515 : Blo 1939435 9323515 := bstep (se 1 (by rfl) ⟨6992636, by rfl⟩ : syracuseStep 9323515 = 13985273) B13985273
theorem B12431353 : Blo 1939435 12431353 := bstep (se 2 (by rfl) ⟨4661757, by rfl⟩ : syracuseStep 12431353 = 9323515) B9323515
theorem B16575137 : Blo 1939435 16575137 := bstep (se 2 (by rfl) ⟨6215676, by rfl⟩ : syracuseStep 16575137 = 12431353) B12431353
theorem B11050091 : Blo 1939435 11050091 := bstep (se 1 (by rfl) ⟨8287568, by rfl⟩ : syracuseStep 11050091 = 16575137) B16575137
theorem B7366727 : Blo 1939435 7366727 := bstep (se 1 (by rfl) ⟨5525045, by rfl⟩ : syracuseStep 7366727 = 11050091) B11050091
theorem B4911151 : Blo 1939435 4911151 := bstep (se 1 (by rfl) ⟨3683363, by rfl⟩ : syracuseStep 4911151 = 7366727) B7366727
theorem B6548201 : Blo 1939435 6548201 := bstep (se 2 (by rfl) ⟨2455575, by rfl⟩ : syracuseStep 6548201 = 4911151) B4911151
theorem B4365467 : Blo 1939435 4365467 := bstep (se 1 (by rfl) ⟨3274100, by rfl⟩ : syracuseStep 4365467 = 6548201) B6548201
theorem B2910311 : Blo 1939435 2910311 := bstep (se 1 (by rfl) ⟨2182733, by rfl⟩ : syracuseStep 2910311 = 4365467) B4365467
theorem B1940207 : Blo 1939435 1940207 := bstep (se 1 (by rfl) ⟨1455155, by rfl⟩ : syracuseStep 1940207 = 2910311) B2910311
theorem B2910317 : Blo 1939435 2910317 := bbase (se 3 (by rfl) ⟨545684, by rfl⟩ : syracuseStep 2910317 = 1091369) (by norm_num)
theorem B1940211 : Blo 1939435 1940211 := bstep (se 1 (by rfl) ⟨1455158, by rfl⟩ : syracuseStep 1940211 = 2910317) B2910317
theorem B4365485 : Blo 1939435 4365485 := bbase (se 3 (by rfl) ⟨818528, by rfl⟩ : syracuseStep 4365485 = 1637057) (by norm_num)
theorem B2910323 : Blo 1939435 2910323 := bstep (se 1 (by rfl) ⟨2182742, by rfl⟩ : syracuseStep 2910323 = 4365485) B4365485
theorem B1940215 : Blo 1939435 1940215 := bstep (se 1 (by rfl) ⟨1455161, by rfl⟩ : syracuseStep 1940215 = 2910323) B2910323
theorem B6215717 : Blo 1939435 6215717 := bbase (se 4 (by rfl) ⟨582723, by rfl⟩ : syracuseStep 6215717 = 1165447) (by norm_num)
theorem B4143811 : Blo 1939435 4143811 := bstep (se 1 (by rfl) ⟨3107858, by rfl⟩ : syracuseStep 4143811 = 6215717) B6215717
theorem B5525081 : Blo 1939435 5525081 := bstep (se 2 (by rfl) ⟨2071905, by rfl⟩ : syracuseStep 5525081 = 4143811) B4143811
theorem B3683387 : Blo 1939435 3683387 := bstep (se 1 (by rfl) ⟨2762540, by rfl⟩ : syracuseStep 3683387 = 5525081) B5525081
theorem B2455591 : Blo 1939435 2455591 := bstep (se 1 (by rfl) ⟨1841693, by rfl⟩ : syracuseStep 2455591 = 3683387) B3683387
theorem B3274121 : Blo 1939435 3274121 := bstep (se 2 (by rfl) ⟨1227795, by rfl⟩ : syracuseStep 3274121 = 2455591) B2455591
theorem B2182747 : Blo 1939435 2182747 := bstep (se 1 (by rfl) ⟨1637060, by rfl⟩ : syracuseStep 2182747 = 3274121) B3274121
theorem B2910329 : Blo 1939435 2910329 := bstep (se 2 (by rfl) ⟨1091373, by rfl⟩ : syracuseStep 2910329 = 2182747) B2182747
theorem B1940219 : Blo 1939435 1940219 := bstep (se 1 (by rfl) ⟨1455164, by rfl⟩ : syracuseStep 1940219 = 2910329) B2910329
theorem B8400709 : Blo 1939435 8400709 := bbase (se 4 (by rfl) ⟨787566, by rfl⟩ : syracuseStep 8400709 = 1575133) (by norm_num)
theorem B11200945 : Blo 1939435 11200945 := bstep (se 2 (by rfl) ⟨4200354, by rfl⟩ : syracuseStep 11200945 = 8400709) B8400709
theorem B14934593 : Blo 1939435 14934593 := bstep (se 2 (by rfl) ⟨5600472, by rfl⟩ : syracuseStep 14934593 = 11200945) B11200945
theorem B9956395 : Blo 1939435 9956395 := bstep (se 1 (by rfl) ⟨7467296, by rfl⟩ : syracuseStep 9956395 = 14934593) B14934593
theorem B13275193 : Blo 1939435 13275193 := bstep (se 2 (by rfl) ⟨4978197, by rfl⟩ : syracuseStep 13275193 = 9956395) B9956395
theorem B17700257 : Blo 1939435 17700257 := bstep (se 2 (by rfl) ⟨6637596, by rfl⟩ : syracuseStep 17700257 = 13275193) B13275193
theorem B11800171 : Blo 1939435 11800171 := bstep (se 1 (by rfl) ⟨8850128, by rfl⟩ : syracuseStep 11800171 = 17700257) B17700257
theorem B15733561 : Blo 1939435 15733561 := bstep (se 2 (by rfl) ⟨5900085, by rfl⟩ : syracuseStep 15733561 = 11800171) B11800171
theorem B20978081 : Blo 1939435 20978081 := bstep (se 2 (by rfl) ⟨7866780, by rfl⟩ : syracuseStep 20978081 = 15733561) B15733561
theorem B13985387 : Blo 1939435 13985387 := bstep (se 1 (by rfl) ⟨10489040, by rfl⟩ : syracuseStep 13985387 = 20978081) B20978081
theorem B9323591 : Blo 1939435 9323591 := bstep (se 1 (by rfl) ⟨6992693, by rfl⟩ : syracuseStep 9323591 = 13985387) B13985387
theorem B24862909 : Blo 1939435 24862909 := bstep (se 3 (by rfl) ⟨4661795, by rfl⟩ : syracuseStep 24862909 = 9323591) B9323591
theorem B33150545 : Blo 1939435 33150545 := bstep (se 2 (by rfl) ⟨12431454, by rfl⟩ : syracuseStep 33150545 = 24862909) B24862909
theorem B22100363 : Blo 1939435 22100363 := bstep (se 1 (by rfl) ⟨16575272, by rfl⟩ : syracuseStep 22100363 = 33150545) B33150545
theorem B14733575 : Blo 1939435 14733575 := bstep (se 1 (by rfl) ⟨11050181, by rfl⟩ : syracuseStep 14733575 = 22100363) B22100363
theorem B9822383 : Blo 1939435 9822383 := bstep (se 1 (by rfl) ⟨7366787, by rfl⟩ : syracuseStep 9822383 = 14733575) B14733575
theorem B6548255 : Blo 1939435 6548255 := bstep (se 1 (by rfl) ⟨4911191, by rfl⟩ : syracuseStep 6548255 = 9822383) B9822383
theorem B4365503 : Blo 1939435 4365503 := bstep (se 1 (by rfl) ⟨3274127, by rfl⟩ : syracuseStep 4365503 = 6548255) B6548255
theorem B2910335 : Blo 1939435 2910335 := bstep (se 1 (by rfl) ⟨2182751, by rfl⟩ : syracuseStep 2910335 = 4365503) B4365503
theorem B1940223 : Blo 1939435 1940223 := bstep (se 1 (by rfl) ⟨1455167, by rfl⟩ : syracuseStep 1940223 = 2910335) B2910335
theorem B2910341 : Blo 1939435 2910341 := bbase (se 4 (by rfl) ⟨272844, by rfl⟩ : syracuseStep 2910341 = 545689) (by norm_num)
theorem B1940227 : Blo 1939435 1940227 := bstep (se 1 (by rfl) ⟨1455170, by rfl⟩ : syracuseStep 1940227 = 2910341) B2910341
theorem B3274141 : Blo 1939435 3274141 := bbase (se 3 (by rfl) ⟨613901, by rfl⟩ : syracuseStep 3274141 = 1227803) (by norm_num)
theorem B4365521 : Blo 1939435 4365521 := bstep (se 2 (by rfl) ⟨1637070, by rfl⟩ : syracuseStep 4365521 = 3274141) B3274141
theorem B2910347 : Blo 1939435 2910347 := bstep (se 1 (by rfl) ⟨2182760, by rfl⟩ : syracuseStep 2910347 = 4365521) B4365521
theorem B1940231 : Blo 1939435 1940231 := bstep (se 1 (by rfl) ⟨1455173, by rfl⟩ : syracuseStep 1940231 = 2910347) B2910347
theorem B2182765 : Blo 1939435 2182765 := bbase (se 3 (by rfl) ⟨409268, by rfl⟩ : syracuseStep 2182765 = 818537) (by norm_num)
theorem B2910353 : Blo 1939435 2910353 := bstep (se 2 (by rfl) ⟨1091382, by rfl⟩ : syracuseStep 2910353 = 2182765) B2182765
theorem B1940235 : Blo 1939435 1940235 := bstep (se 1 (by rfl) ⟨1455176, by rfl⟩ : syracuseStep 1940235 = 2910353) B2910353
theorem B6548309 : Blo 1939435 6548309 := bbase (se 9 (by rfl) ⟨19184, by rfl⟩ : syracuseStep 6548309 = 38369) (by norm_num)
theorem B4365539 : Blo 1939435 4365539 := bstep (se 1 (by rfl) ⟨3274154, by rfl⟩ : syracuseStep 4365539 = 6548309) B6548309
theorem B2910359 : Blo 1939435 2910359 := bstep (se 1 (by rfl) ⟨2182769, by rfl⟩ : syracuseStep 2910359 = 4365539) B4365539
theorem B1940239 : Blo 1939435 1940239 := bstep (se 1 (by rfl) ⟨1455179, by rfl⟩ : syracuseStep 1940239 = 2910359) B2910359
theorem B2910365 : Blo 1939435 2910365 := bbase (se 3 (by rfl) ⟨545693, by rfl⟩ : syracuseStep 2910365 = 1091387) (by norm_num)
theorem B1940243 : Blo 1939435 1940243 := bstep (se 1 (by rfl) ⟨1455182, by rfl⟩ : syracuseStep 1940243 = 2910365) B2910365
theorem B4365557 : Blo 1939435 4365557 := bbase (se 5 (by rfl) ⟨204635, by rfl⟩ : syracuseStep 4365557 = 409271) (by norm_num)
theorem B2910371 : Blo 1939435 2910371 := bstep (se 1 (by rfl) ⟨2182778, by rfl⟩ : syracuseStep 2910371 = 4365557) B4365557
theorem B1940247 : Blo 1939435 1940247 := bstep (se 1 (by rfl) ⟨1455185, by rfl⟩ : syracuseStep 1940247 = 2910371) B2910371
theorem B51092693 : Blo 1939435 51092693 := bbase (se 7 (by rfl) ⟨598742, by rfl⟩ : syracuseStep 51092693 = 1197485) (by norm_num)
theorem B34061795 : Blo 1939435 34061795 := bstep (se 1 (by rfl) ⟨25546346, by rfl⟩ : syracuseStep 34061795 = 51092693) B51092693
theorem B22707863 : Blo 1939435 22707863 := bstep (se 1 (by rfl) ⟨17030897, by rfl⟩ : syracuseStep 22707863 = 34061795) B34061795
theorem B15138575 : Blo 1939435 15138575 := bstep (se 1 (by rfl) ⟨11353931, by rfl⟩ : syracuseStep 15138575 = 22707863) B22707863
theorem B10092383 : Blo 1939435 10092383 := bstep (se 1 (by rfl) ⟨7569287, by rfl⟩ : syracuseStep 10092383 = 15138575) B15138575
theorem B6728255 : Blo 1939435 6728255 := bstep (se 1 (by rfl) ⟨5046191, by rfl⟩ : syracuseStep 6728255 = 10092383) B10092383
theorem B4485503 : Blo 1939435 4485503 := bstep (se 1 (by rfl) ⟨3364127, by rfl⟩ : syracuseStep 4485503 = 6728255) B6728255
theorem B11961341 : Blo 1939435 11961341 := bstep (se 3 (by rfl) ⟨2242751, by rfl⟩ : syracuseStep 11961341 = 4485503) B4485503
theorem B7974227 : Blo 1939435 7974227 := bstep (se 1 (by rfl) ⟨5980670, by rfl⟩ : syracuseStep 7974227 = 11961341) B11961341
theorem B21264605 : Blo 1939435 21264605 := bstep (se 3 (by rfl) ⟨3987113, by rfl⟩ : syracuseStep 21264605 = 7974227) B7974227
theorem B14176403 : Blo 1939435 14176403 := bstep (se 1 (by rfl) ⟨10632302, by rfl⟩ : syracuseStep 14176403 = 21264605) B21264605
theorem B9450935 : Blo 1939435 9450935 := bstep (se 1 (by rfl) ⟨7088201, by rfl⟩ : syracuseStep 9450935 = 14176403) B14176403
theorem B6300623 : Blo 1939435 6300623 := bstep (se 1 (by rfl) ⟨4725467, by rfl⟩ : syracuseStep 6300623 = 9450935) B9450935
theorem B16801661 : Blo 1939435 16801661 := bstep (se 3 (by rfl) ⟨3150311, by rfl⟩ : syracuseStep 16801661 = 6300623) B6300623
theorem B44804429 : Blo 1939435 44804429 := bstep (se 3 (by rfl) ⟨8400830, by rfl⟩ : syracuseStep 44804429 = 16801661) B16801661
theorem B29869619 : Blo 1939435 29869619 := bstep (se 1 (by rfl) ⟨22402214, by rfl⟩ : syracuseStep 29869619 = 44804429) B44804429
theorem B79652317 : Blo 1939435 79652317 := bstep (se 3 (by rfl) ⟨14934809, by rfl⟩ : syracuseStep 79652317 = 29869619) B29869619
theorem B106203089 : Blo 1939435 106203089 := bstep (se 2 (by rfl) ⟨39826158, by rfl⟩ : syracuseStep 106203089 = 79652317) B79652317
theorem B70802059 : Blo 1939435 70802059 := bstep (se 1 (by rfl) ⟨53101544, by rfl⟩ : syracuseStep 70802059 = 106203089) B106203089
theorem B94402745 : Blo 1939435 94402745 := bstep (se 2 (by rfl) ⟨35401029, by rfl⟩ : syracuseStep 94402745 = 70802059) B70802059
theorem B62935163 : Blo 1939435 62935163 := bstep (se 1 (by rfl) ⟨47201372, by rfl⟩ : syracuseStep 62935163 = 94402745) B94402745
theorem B41956775 : Blo 1939435 41956775 := bstep (se 1 (by rfl) ⟨31467581, by rfl⟩ : syracuseStep 41956775 = 62935163) B62935163
theorem B27971183 : Blo 1939435 27971183 := bstep (se 1 (by rfl) ⟨20978387, by rfl⟩ : syracuseStep 27971183 = 41956775) B41956775
theorem B18647455 : Blo 1939435 18647455 := bstep (se 1 (by rfl) ⟨13985591, by rfl⟩ : syracuseStep 18647455 = 27971183) B27971183
theorem B24863273 : Blo 1939435 24863273 := bstep (se 2 (by rfl) ⟨9323727, by rfl⟩ : syracuseStep 24863273 = 18647455) B18647455
theorem B16575515 : Blo 1939435 16575515 := bstep (se 1 (by rfl) ⟨12431636, by rfl⟩ : syracuseStep 16575515 = 24863273) B24863273
theorem B11050343 : Blo 1939435 11050343 := bstep (se 1 (by rfl) ⟨8287757, by rfl⟩ : syracuseStep 11050343 = 16575515) B16575515
theorem B7366895 : Blo 1939435 7366895 := bstep (se 1 (by rfl) ⟨5525171, by rfl⟩ : syracuseStep 7366895 = 11050343) B11050343
theorem B4911263 : Blo 1939435 4911263 := bstep (se 1 (by rfl) ⟨3683447, by rfl⟩ : syracuseStep 4911263 = 7366895) B7366895
theorem B3274175 : Blo 1939435 3274175 := bstep (se 1 (by rfl) ⟨2455631, by rfl⟩ : syracuseStep 3274175 = 4911263) B4911263
theorem B2182783 : Blo 1939435 2182783 := bstep (se 1 (by rfl) ⟨1637087, by rfl⟩ : syracuseStep 2182783 = 3274175) B3274175
theorem B2910377 : Blo 1939435 2910377 := bstep (se 2 (by rfl) ⟨1091391, by rfl⟩ : syracuseStep 2910377 = 2182783) B2182783
theorem B1940251 : Blo 1939435 1940251 := bstep (se 1 (by rfl) ⟨1455188, by rfl⟩ : syracuseStep 1940251 = 2910377) B2910377
theorem B13985621 : Blo 1939435 13985621 := bbase (se 9 (by rfl) ⟨40973, by rfl⟩ : syracuseStep 13985621 = 81947) (by norm_num)
theorem B9323747 : Blo 1939435 9323747 := bstep (se 1 (by rfl) ⟨6992810, by rfl⟩ : syracuseStep 9323747 = 13985621) B13985621
theorem B6215831 : Blo 1939435 6215831 := bstep (se 1 (by rfl) ⟨4661873, by rfl⟩ : syracuseStep 6215831 = 9323747) B9323747
theorem B4143887 : Blo 1939435 4143887 := bstep (se 1 (by rfl) ⟨3107915, by rfl⟩ : syracuseStep 4143887 = 6215831) B6215831
theorem B2762591 : Blo 1939435 2762591 := bstep (se 1 (by rfl) ⟨2071943, by rfl⟩ : syracuseStep 2762591 = 4143887) B4143887
theorem B7366909 : Blo 1939435 7366909 := bstep (se 3 (by rfl) ⟨1381295, by rfl⟩ : syracuseStep 7366909 = 2762591) B2762591
theorem B9822545 : Blo 1939435 9822545 := bstep (se 2 (by rfl) ⟨3683454, by rfl⟩ : syracuseStep 9822545 = 7366909) B7366909
theorem B6548363 : Blo 1939435 6548363 := bstep (se 1 (by rfl) ⟨4911272, by rfl⟩ : syracuseStep 6548363 = 9822545) B9822545
theorem B4365575 : Blo 1939435 4365575 := bstep (se 1 (by rfl) ⟨3274181, by rfl⟩ : syracuseStep 4365575 = 6548363) B6548363
theorem B2910383 : Blo 1939435 2910383 := bstep (se 1 (by rfl) ⟨2182787, by rfl⟩ : syracuseStep 2910383 = 4365575) B4365575
theorem B1940255 : Blo 1939435 1940255 := bstep (se 1 (by rfl) ⟨1455191, by rfl⟩ : syracuseStep 1940255 = 2910383) B2910383
theorem B2910389 : Blo 1939435 2910389 := bbase (se 5 (by rfl) ⟨136424, by rfl⟩ : syracuseStep 2910389 = 272849) (by norm_num)
theorem B1940259 : Blo 1939435 1940259 := bstep (se 1 (by rfl) ⟨1455194, by rfl⟩ : syracuseStep 1940259 = 2910389) B2910389
theorem B4911293 : Blo 1939435 4911293 := bbase (se 3 (by rfl) ⟨920867, by rfl⟩ : syracuseStep 4911293 = 1841735) (by norm_num)
theorem B3274195 : Blo 1939435 3274195 := bstep (se 1 (by rfl) ⟨2455646, by rfl⟩ : syracuseStep 3274195 = 4911293) B4911293
theorem B4365593 : Blo 1939435 4365593 := bstep (se 2 (by rfl) ⟨1637097, by rfl⟩ : syracuseStep 4365593 = 3274195) B3274195
theorem B2910395 : Blo 1939435 2910395 := bstep (se 1 (by rfl) ⟨2182796, by rfl⟩ : syracuseStep 2910395 = 4365593) B4365593
theorem B1940263 : Blo 1939435 1940263 := bstep (se 1 (by rfl) ⟨1455197, by rfl⟩ : syracuseStep 1940263 = 2910395) B2910395
theorem B2182801 : Blo 1939435 2182801 := bbase (se 2 (by rfl) ⟨818550, by rfl⟩ : syracuseStep 2182801 = 1637101) (by norm_num)
theorem B2910401 : Blo 1939435 2910401 := bstep (se 2 (by rfl) ⟨1091400, by rfl⟩ : syracuseStep 2910401 = 2182801) B2182801
theorem B1940267 : Blo 1939435 1940267 := bstep (se 1 (by rfl) ⟨1455200, by rfl⟩ : syracuseStep 1940267 = 2910401) B2910401
theorem B3683485 : Blo 1939435 3683485 := bbase (se 3 (by rfl) ⟨690653, by rfl⟩ : syracuseStep 3683485 = 1381307) (by norm_num)
theorem B4911313 : Blo 1939435 4911313 := bstep (se 2 (by rfl) ⟨1841742, by rfl⟩ : syracuseStep 4911313 = 3683485) B3683485
theorem B6548417 : Blo 1939435 6548417 := bstep (se 2 (by rfl) ⟨2455656, by rfl⟩ : syracuseStep 6548417 = 4911313) B4911313
theorem B4365611 : Blo 1939435 4365611 := bstep (se 1 (by rfl) ⟨3274208, by rfl⟩ : syracuseStep 4365611 = 6548417) B6548417
theorem B2910407 : Blo 1939435 2910407 := bstep (se 1 (by rfl) ⟨2182805, by rfl⟩ : syracuseStep 2910407 = 4365611) B4365611
theorem B1940271 : Blo 1939435 1940271 := bstep (se 1 (by rfl) ⟨1455203, by rfl⟩ : syracuseStep 1940271 = 2910407) B2910407
theorem B2910413 : Blo 1939435 2910413 := bbase (se 3 (by rfl) ⟨545702, by rfl⟩ : syracuseStep 2910413 = 1091405) (by norm_num)
theorem B1940275 : Blo 1939435 1940275 := bstep (se 1 (by rfl) ⟨1455206, by rfl⟩ : syracuseStep 1940275 = 2910413) B2910413
theorem B4365629 : Blo 1939435 4365629 := bbase (se 3 (by rfl) ⟨818555, by rfl⟩ : syracuseStep 4365629 = 1637111) (by norm_num)
theorem B2910419 : Blo 1939435 2910419 := bstep (se 1 (by rfl) ⟨2182814, by rfl⟩ : syracuseStep 2910419 = 4365629) B4365629
theorem B1940279 : Blo 1939435 1940279 := bstep (se 1 (by rfl) ⟨1455209, by rfl⟩ : syracuseStep 1940279 = 2910419) B2910419
theorem B3274229 : Blo 1939435 3274229 := bbase (se 5 (by rfl) ⟨153479, by rfl⟩ : syracuseStep 3274229 = 306959) (by norm_num)
theorem B2182819 : Blo 1939435 2182819 := bstep (se 1 (by rfl) ⟨1637114, by rfl⟩ : syracuseStep 2182819 = 3274229) B3274229
theorem B2910425 : Blo 1939435 2910425 := bstep (se 2 (by rfl) ⟨1091409, by rfl⟩ : syracuseStep 2910425 = 2182819) B2182819
theorem B1940283 : Blo 1939435 1940283 := bstep (se 1 (by rfl) ⟨1455212, by rfl⟩ : syracuseStep 1940283 = 2910425) B2910425
theorem B11800565 : Blo 1939435 11800565 := bbase (se 5 (by rfl) ⟨553151, by rfl⟩ : syracuseStep 11800565 = 1106303) (by norm_num)
theorem B7867043 : Blo 1939435 7867043 := bstep (se 1 (by rfl) ⟨5900282, by rfl⟩ : syracuseStep 7867043 = 11800565) B11800565
theorem B5244695 : Blo 1939435 5244695 := bstep (se 1 (by rfl) ⟨3933521, by rfl⟩ : syracuseStep 5244695 = 7867043) B7867043
theorem B3496463 : Blo 1939435 3496463 := bstep (se 1 (by rfl) ⟨2622347, by rfl⟩ : syracuseStep 3496463 = 5244695) B5244695
theorem B2330975 : Blo 1939435 2330975 := bstep (se 1 (by rfl) ⟨1748231, by rfl⟩ : syracuseStep 2330975 = 3496463) B3496463
theorem B6215933 : Blo 1939435 6215933 := bstep (se 3 (by rfl) ⟨1165487, by rfl⟩ : syracuseStep 6215933 = 2330975) B2330975
theorem B4143955 : Blo 1939435 4143955 := bstep (se 1 (by rfl) ⟨3107966, by rfl⟩ : syracuseStep 4143955 = 6215933) B6215933
theorem B5525273 : Blo 1939435 5525273 := bstep (se 2 (by rfl) ⟨2071977, by rfl⟩ : syracuseStep 5525273 = 4143955) B4143955
theorem B14734061 : Blo 1939435 14734061 := bstep (se 3 (by rfl) ⟨2762636, by rfl⟩ : syracuseStep 14734061 = 5525273) B5525273
theorem B9822707 : Blo 1939435 9822707 := bstep (se 1 (by rfl) ⟨7367030, by rfl⟩ : syracuseStep 9822707 = 14734061) B14734061
theorem B6548471 : Blo 1939435 6548471 := bstep (se 1 (by rfl) ⟨4911353, by rfl⟩ : syracuseStep 6548471 = 9822707) B9822707
theorem B4365647 : Blo 1939435 4365647 := bstep (se 1 (by rfl) ⟨3274235, by rfl⟩ : syracuseStep 4365647 = 6548471) B6548471
theorem B2910431 : Blo 1939435 2910431 := bstep (se 1 (by rfl) ⟨2182823, by rfl⟩ : syracuseStep 2910431 = 4365647) B4365647
theorem B1940287 : Blo 1939435 1940287 := bstep (se 1 (by rfl) ⟨1455215, by rfl⟩ : syracuseStep 1940287 = 2910431) B2910431
theorem B2910437 : Blo 1939435 2910437 := bbase (se 4 (by rfl) ⟨272853, by rfl⟩ : syracuseStep 2910437 = 545707) (by norm_num)
theorem B1940291 : Blo 1939435 1940291 := bstep (se 1 (by rfl) ⟨1455218, by rfl⟩ : syracuseStep 1940291 = 2910437) B2910437
theorem B4143973 : Blo 1939435 4143973 := bbase (se 4 (by rfl) ⟨388497, by rfl⟩ : syracuseStep 4143973 = 776995) (by norm_num)
theorem B5525297 : Blo 1939435 5525297 := bstep (se 2 (by rfl) ⟨2071986, by rfl⟩ : syracuseStep 5525297 = 4143973) B4143973
theorem B3683531 : Blo 1939435 3683531 := bstep (se 1 (by rfl) ⟨2762648, by rfl⟩ : syracuseStep 3683531 = 5525297) B5525297
theorem B2455687 : Blo 1939435 2455687 := bstep (se 1 (by rfl) ⟨1841765, by rfl⟩ : syracuseStep 2455687 = 3683531) B3683531
theorem B3274249 : Blo 1939435 3274249 := bstep (se 2 (by rfl) ⟨1227843, by rfl⟩ : syracuseStep 3274249 = 2455687) B2455687
theorem B4365665 : Blo 1939435 4365665 := bstep (se 2 (by rfl) ⟨1637124, by rfl⟩ : syracuseStep 4365665 = 3274249) B3274249
theorem B2910443 : Blo 1939435 2910443 := bstep (se 1 (by rfl) ⟨2182832, by rfl⟩ : syracuseStep 2910443 = 4365665) B4365665
theorem B1940295 : Blo 1939435 1940295 := bstep (se 1 (by rfl) ⟨1455221, by rfl⟩ : syracuseStep 1940295 = 2910443) B2910443
theorem B2182837 : Blo 1939435 2182837 := bbase (se 5 (by rfl) ⟨102320, by rfl⟩ : syracuseStep 2182837 = 204641) (by norm_num)
theorem B2910449 : Blo 1939435 2910449 := bstep (se 2 (by rfl) ⟨1091418, by rfl⟩ : syracuseStep 2910449 = 2182837) B2182837
theorem B1940299 : Blo 1939435 1940299 := bstep (se 1 (by rfl) ⟨1455224, by rfl⟩ : syracuseStep 1940299 = 2910449) B2910449
theorem B2455697 : Blo 1939435 2455697 := bbase (se 2 (by rfl) ⟨920886, by rfl⟩ : syracuseStep 2455697 = 1841773) (by norm_num)
theorem B6548525 : Blo 1939435 6548525 := bstep (se 3 (by rfl) ⟨1227848, by rfl⟩ : syracuseStep 6548525 = 2455697) B2455697
theorem B4365683 : Blo 1939435 4365683 := bstep (se 1 (by rfl) ⟨3274262, by rfl⟩ : syracuseStep 4365683 = 6548525) B6548525
theorem B2910455 : Blo 1939435 2910455 := bstep (se 1 (by rfl) ⟨2182841, by rfl⟩ : syracuseStep 2910455 = 4365683) B4365683
theorem B1940303 : Blo 1939435 1940303 := bstep (se 1 (by rfl) ⟨1455227, by rfl⟩ : syracuseStep 1940303 = 2910455) B2910455
theorem B2910461 : Blo 1939435 2910461 := bbase (se 3 (by rfl) ⟨545711, by rfl⟩ : syracuseStep 2910461 = 1091423) (by norm_num)
theorem B1940307 : Blo 1939435 1940307 := bstep (se 1 (by rfl) ⟨1455230, by rfl⟩ : syracuseStep 1940307 = 2910461) B2910461
theorem B4365701 : Blo 1939435 4365701 := bbase (se 4 (by rfl) ⟨409284, by rfl⟩ : syracuseStep 4365701 = 818569) (by norm_num)
theorem B2910467 : Blo 1939435 2910467 := bstep (se 1 (by rfl) ⟨2182850, by rfl⟩ : syracuseStep 2910467 = 4365701) B4365701
theorem B1940311 : Blo 1939435 1940311 := bstep (se 1 (by rfl) ⟨1455233, by rfl⟩ : syracuseStep 1940311 = 2910467) B2910467
theorem B2762677 : Blo 1939435 2762677 := bbase (se 5 (by rfl) ⟨129500, by rfl⟩ : syracuseStep 2762677 = 259001) (by norm_num)
theorem B3683569 : Blo 1939435 3683569 := bstep (se 2 (by rfl) ⟨1381338, by rfl⟩ : syracuseStep 3683569 = 2762677) B2762677
theorem B4911425 : Blo 1939435 4911425 := bstep (se 2 (by rfl) ⟨1841784, by rfl⟩ : syracuseStep 4911425 = 3683569) B3683569
theorem B3274283 : Blo 1939435 3274283 := bstep (se 1 (by rfl) ⟨2455712, by rfl⟩ : syracuseStep 3274283 = 4911425) B4911425
theorem B2182855 : Blo 1939435 2182855 := bstep (se 1 (by rfl) ⟨1637141, by rfl⟩ : syracuseStep 2182855 = 3274283) B3274283
theorem B2910473 : Blo 1939435 2910473 := bstep (se 2 (by rfl) ⟨1091427, by rfl⟩ : syracuseStep 2910473 = 2182855) B2182855
theorem B1940315 : Blo 1939435 1940315 := bstep (se 1 (by rfl) ⟨1455236, by rfl⟩ : syracuseStep 1940315 = 2910473) B2910473
theorem B9822869 : Blo 1939435 9822869 := bbase (se 6 (by rfl) ⟨230223, by rfl⟩ : syracuseStep 9822869 = 460447) (by norm_num)
theorem B6548579 : Blo 1939435 6548579 := bstep (se 1 (by rfl) ⟨4911434, by rfl⟩ : syracuseStep 6548579 = 9822869) B9822869
theorem B4365719 : Blo 1939435 4365719 := bstep (se 1 (by rfl) ⟨3274289, by rfl⟩ : syracuseStep 4365719 = 6548579) B6548579
theorem B2910479 : Blo 1939435 2910479 := bstep (se 1 (by rfl) ⟨2182859, by rfl⟩ : syracuseStep 2910479 = 4365719) B4365719
theorem B1940319 : Blo 1939435 1940319 := bstep (se 1 (by rfl) ⟨1455239, by rfl⟩ : syracuseStep 1940319 = 2910479) B2910479
theorem B2910485 : Blo 1939435 2910485 := bbase (se 6 (by rfl) ⟨68214, by rfl⟩ : syracuseStep 2910485 = 136429) (by norm_num)
theorem B1940323 : Blo 1939435 1940323 := bstep (se 1 (by rfl) ⟨1455242, by rfl⟩ : syracuseStep 1940323 = 2910485) B2910485
theorem B7867205 : Blo 1939435 7867205 := bbase (se 4 (by rfl) ⟨737550, by rfl⟩ : syracuseStep 7867205 = 1475101) (by norm_num)
theorem B5244803 : Blo 1939435 5244803 := bstep (se 1 (by rfl) ⟨3933602, by rfl⟩ : syracuseStep 5244803 = 7867205) B7867205
theorem B3496535 : Blo 1939435 3496535 := bstep (se 1 (by rfl) ⟨2622401, by rfl⟩ : syracuseStep 3496535 = 5244803) B5244803
theorem B2331023 : Blo 1939435 2331023 := bstep (se 1 (by rfl) ⟨1748267, by rfl⟩ : syracuseStep 2331023 = 3496535) B3496535
theorem B24864245 : Blo 1939435 24864245 := bstep (se 5 (by rfl) ⟨1165511, by rfl⟩ : syracuseStep 24864245 = 2331023) B2331023
theorem B16576163 : Blo 1939435 16576163 := bstep (se 1 (by rfl) ⟨12432122, by rfl⟩ : syracuseStep 16576163 = 24864245) B24864245
theorem B11050775 : Blo 1939435 11050775 := bstep (se 1 (by rfl) ⟨8288081, by rfl⟩ : syracuseStep 11050775 = 16576163) B16576163
theorem B7367183 : Blo 1939435 7367183 := bstep (se 1 (by rfl) ⟨5525387, by rfl⟩ : syracuseStep 7367183 = 11050775) B11050775
theorem B4911455 : Blo 1939435 4911455 := bstep (se 1 (by rfl) ⟨3683591, by rfl⟩ : syracuseStep 4911455 = 7367183) B7367183
theorem B3274303 : Blo 1939435 3274303 := bstep (se 1 (by rfl) ⟨2455727, by rfl⟩ : syracuseStep 3274303 = 4911455) B4911455
theorem B4365737 : Blo 1939435 4365737 := bstep (se 2 (by rfl) ⟨1637151, by rfl⟩ : syracuseStep 4365737 = 3274303) B3274303
theorem B2910491 : Blo 1939435 2910491 := bstep (se 1 (by rfl) ⟨2182868, by rfl⟩ : syracuseStep 2910491 = 4365737) B4365737
theorem B1940327 : Blo 1939435 1940327 := bstep (se 1 (by rfl) ⟨1455245, by rfl⟩ : syracuseStep 1940327 = 2910491) B2910491
theorem B2182873 : Blo 1939435 2182873 := bbase (se 2 (by rfl) ⟨818577, by rfl⟩ : syracuseStep 2182873 = 1637155) (by norm_num)
theorem B2910497 : Blo 1939435 2910497 := bstep (se 2 (by rfl) ⟨1091436, by rfl⟩ : syracuseStep 2910497 = 2182873) B2182873
theorem B1940331 : Blo 1939435 1940331 := bstep (se 1 (by rfl) ⟨1455248, by rfl⟩ : syracuseStep 1940331 = 2910497) B2910497
theorem B2072029 : Blo 1939435 2072029 := bbase (se 3 (by rfl) ⟨388505, by rfl⟩ : syracuseStep 2072029 = 777011) (by norm_num)
theorem B2762705 : Blo 1939435 2762705 := bstep (se 2 (by rfl) ⟨1036014, by rfl⟩ : syracuseStep 2762705 = 2072029) B2072029
theorem B7367213 : Blo 1939435 7367213 := bstep (se 3 (by rfl) ⟨1381352, by rfl⟩ : syracuseStep 7367213 = 2762705) B2762705
theorem B4911475 : Blo 1939435 4911475 := bstep (se 1 (by rfl) ⟨3683606, by rfl⟩ : syracuseStep 4911475 = 7367213) B7367213
theorem B6548633 : Blo 1939435 6548633 := bstep (se 2 (by rfl) ⟨2455737, by rfl⟩ : syracuseStep 6548633 = 4911475) B4911475
theorem B4365755 : Blo 1939435 4365755 := bstep (se 1 (by rfl) ⟨3274316, by rfl⟩ : syracuseStep 4365755 = 6548633) B6548633
theorem B2910503 : Blo 1939435 2910503 := bstep (se 1 (by rfl) ⟨2182877, by rfl⟩ : syracuseStep 2910503 = 4365755) B4365755
theorem B1940335 : Blo 1939435 1940335 := bstep (se 1 (by rfl) ⟨1455251, by rfl⟩ : syracuseStep 1940335 = 2910503) B2910503
theorem B2910509 : Blo 1939435 2910509 := bbase (se 3 (by rfl) ⟨545720, by rfl⟩ : syracuseStep 2910509 = 1091441) (by norm_num)
theorem B1940339 : Blo 1939435 1940339 := bstep (se 1 (by rfl) ⟨1455254, by rfl⟩ : syracuseStep 1940339 = 2910509) B2910509
theorem B4365773 : Blo 1939435 4365773 := bbase (se 3 (by rfl) ⟨818582, by rfl⟩ : syracuseStep 4365773 = 1637165) (by norm_num)
theorem B2910515 : Blo 1939435 2910515 := bstep (se 1 (by rfl) ⟨2182886, by rfl⟩ : syracuseStep 2910515 = 4365773) B4365773
theorem B1940343 : Blo 1939435 1940343 := bstep (se 1 (by rfl) ⟨1455257, by rfl⟩ : syracuseStep 1940343 = 2910515) B2910515
theorem B2455753 : Blo 1939435 2455753 := bbase (se 2 (by rfl) ⟨920907, by rfl⟩ : syracuseStep 2455753 = 1841815) (by norm_num)
theorem B3274337 : Blo 1939435 3274337 := bstep (se 2 (by rfl) ⟨1227876, by rfl⟩ : syracuseStep 3274337 = 2455753) B2455753
theorem B2182891 : Blo 1939435 2182891 := bstep (se 1 (by rfl) ⟨1637168, by rfl⟩ : syracuseStep 2182891 = 3274337) B3274337
theorem B2910521 : Blo 1939435 2910521 := bstep (se 2 (by rfl) ⟨1091445, by rfl⟩ : syracuseStep 2910521 = 2182891) B2182891
theorem B1940347 : Blo 1939435 1940347 := bstep (se 1 (by rfl) ⟨1455260, by rfl⟩ : syracuseStep 1940347 = 2910521) B2910521
theorem B1966825 : Blo 1939435 1966825 := bbase (se 2 (by rfl) ⟨737559, by rfl⟩ : syracuseStep 1966825 = 1475119) (by norm_num)
theorem B10489733 : Blo 1939435 10489733 := bstep (se 4 (by rfl) ⟨983412, by rfl⟩ : syracuseStep 10489733 = 1966825) B1966825
theorem B6993155 : Blo 1939435 6993155 := bstep (se 1 (by rfl) ⟨5244866, by rfl⟩ : syracuseStep 6993155 = 10489733) B10489733
theorem B18648413 : Blo 1939435 18648413 := bstep (se 3 (by rfl) ⟨3496577, by rfl⟩ : syracuseStep 18648413 = 6993155) B6993155
theorem B12432275 : Blo 1939435 12432275 := bstep (se 1 (by rfl) ⟨9324206, by rfl⟩ : syracuseStep 12432275 = 18648413) B18648413
theorem B8288183 : Blo 1939435 8288183 := bstep (se 1 (by rfl) ⟨6216137, by rfl⟩ : syracuseStep 8288183 = 12432275) B12432275
theorem B22101821 : Blo 1939435 22101821 := bstep (se 3 (by rfl) ⟨4144091, by rfl⟩ : syracuseStep 22101821 = 8288183) B8288183
theorem B14734547 : Blo 1939435 14734547 := bstep (se 1 (by rfl) ⟨11050910, by rfl⟩ : syracuseStep 14734547 = 22101821) B22101821
theorem B9823031 : Blo 1939435 9823031 := bstep (se 1 (by rfl) ⟨7367273, by rfl⟩ : syracuseStep 9823031 = 14734547) B14734547
theorem B6548687 : Blo 1939435 6548687 := bstep (se 1 (by rfl) ⟨4911515, by rfl⟩ : syracuseStep 6548687 = 9823031) B9823031
theorem B4365791 : Blo 1939435 4365791 := bstep (se 1 (by rfl) ⟨3274343, by rfl⟩ : syracuseStep 4365791 = 6548687) B6548687
theorem B2910527 : Blo 1939435 2910527 := bstep (se 1 (by rfl) ⟨2182895, by rfl⟩ : syracuseStep 2910527 = 4365791) B4365791
theorem B1940351 : Blo 1939435 1940351 := bstep (se 1 (by rfl) ⟨1455263, by rfl⟩ : syracuseStep 1940351 = 2910527) B2910527
theorem B2910533 : Blo 1939435 2910533 := bbase (se 4 (by rfl) ⟨272862, by rfl⟩ : syracuseStep 2910533 = 545725) (by norm_num)
theorem B1940355 : Blo 1939435 1940355 := bstep (se 1 (by rfl) ⟨1455266, by rfl⟩ : syracuseStep 1940355 = 2910533) B2910533
theorem B3274357 : Blo 1939435 3274357 := bbase (se 5 (by rfl) ⟨153485, by rfl⟩ : syracuseStep 3274357 = 306971) (by norm_num)
theorem B4365809 : Blo 1939435 4365809 := bstep (se 2 (by rfl) ⟨1637178, by rfl⟩ : syracuseStep 4365809 = 3274357) B3274357
theorem B2910539 : Blo 1939435 2910539 := bstep (se 1 (by rfl) ⟨2182904, by rfl⟩ : syracuseStep 2910539 = 4365809) B4365809
theorem B1940359 : Blo 1939435 1940359 := bstep (se 1 (by rfl) ⟨1455269, by rfl⟩ : syracuseStep 1940359 = 2910539) B2910539
theorem B2182909 : Blo 1939435 2182909 := bbase (se 3 (by rfl) ⟨409295, by rfl⟩ : syracuseStep 2182909 = 818591) (by norm_num)
theorem B2910545 : Blo 1939435 2910545 := bstep (se 2 (by rfl) ⟨1091454, by rfl⟩ : syracuseStep 2910545 = 2182909) B2182909
theorem B1940363 : Blo 1939435 1940363 := bstep (se 1 (by rfl) ⟨1455272, by rfl⟩ : syracuseStep 1940363 = 2910545) B2910545
theorem B6548741 : Blo 1939435 6548741 := bbase (se 4 (by rfl) ⟨613944, by rfl⟩ : syracuseStep 6548741 = 1227889) (by norm_num)
theorem B4365827 : Blo 1939435 4365827 := bstep (se 1 (by rfl) ⟨3274370, by rfl⟩ : syracuseStep 4365827 = 6548741) B6548741
theorem B2910551 : Blo 1939435 2910551 := bstep (se 1 (by rfl) ⟨2182913, by rfl⟩ : syracuseStep 2910551 = 4365827) B4365827
theorem B1940367 : Blo 1939435 1940367 := bstep (se 1 (by rfl) ⟨1455275, by rfl⟩ : syracuseStep 1940367 = 2910551) B2910551
theorem B2910557 : Blo 1939435 2910557 := bbase (se 3 (by rfl) ⟨545729, by rfl⟩ : syracuseStep 2910557 = 1091459) (by norm_num)
theorem B1940371 : Blo 1939435 1940371 := bstep (se 1 (by rfl) ⟨1455278, by rfl⟩ : syracuseStep 1940371 = 2910557) B2910557
theorem B4365845 : Blo 1939435 4365845 := bbase (se 6 (by rfl) ⟨102324, by rfl⟩ : syracuseStep 4365845 = 204649) (by norm_num)
theorem B2910563 : Blo 1939435 2910563 := bstep (se 1 (by rfl) ⟨2182922, by rfl⟩ : syracuseStep 2910563 = 4365845) B4365845
theorem B1940375 : Blo 1939435 1940375 := bstep (se 1 (by rfl) ⟨1455281, by rfl⟩ : syracuseStep 1940375 = 2910563) B2910563
theorem B7367381 : Blo 1939435 7367381 := bbase (se 7 (by rfl) ⟨86336, by rfl⟩ : syracuseStep 7367381 = 172673) (by norm_num)
theorem B4911587 : Blo 1939435 4911587 := bstep (se 1 (by rfl) ⟨3683690, by rfl⟩ : syracuseStep 4911587 = 7367381) B7367381
theorem B3274391 : Blo 1939435 3274391 := bstep (se 1 (by rfl) ⟨2455793, by rfl⟩ : syracuseStep 3274391 = 4911587) B4911587
theorem B2182927 : Blo 1939435 2182927 := bstep (se 1 (by rfl) ⟨1637195, by rfl⟩ : syracuseStep 2182927 = 3274391) B3274391
theorem B2910569 : Blo 1939435 2910569 := bstep (se 2 (by rfl) ⟨1091463, by rfl⟩ : syracuseStep 2910569 = 2182927) B2182927
theorem B1940379 : Blo 1939435 1940379 := bstep (se 1 (by rfl) ⟨1455284, by rfl⟩ : syracuseStep 1940379 = 2910569) B2910569
theorem B11051093 : Blo 1939435 11051093 := bbase (se 8 (by rfl) ⟨64752, by rfl⟩ : syracuseStep 11051093 = 129505) (by norm_num)
theorem B7367395 : Blo 1939435 7367395 := bstep (se 1 (by rfl) ⟨5525546, by rfl⟩ : syracuseStep 7367395 = 11051093) B11051093
theorem B9823193 : Blo 1939435 9823193 := bstep (se 2 (by rfl) ⟨3683697, by rfl⟩ : syracuseStep 9823193 = 7367395) B7367395
theorem B6548795 : Blo 1939435 6548795 := bstep (se 1 (by rfl) ⟨4911596, by rfl⟩ : syracuseStep 6548795 = 9823193) B9823193
theorem B4365863 : Blo 1939435 4365863 := bstep (se 1 (by rfl) ⟨3274397, by rfl⟩ : syracuseStep 4365863 = 6548795) B6548795
theorem B2910575 : Blo 1939435 2910575 := bstep (se 1 (by rfl) ⟨2182931, by rfl⟩ : syracuseStep 2910575 = 4365863) B4365863
theorem B1940383 : Blo 1939435 1940383 := bstep (se 1 (by rfl) ⟨1455287, by rfl⟩ : syracuseStep 1940383 = 2910575) B2910575
theorem B2910581 : Blo 1939435 2910581 := bbase (se 5 (by rfl) ⟨136433, by rfl⟩ : syracuseStep 2910581 = 272867) (by norm_num)
theorem B1940387 : Blo 1939435 1940387 := bstep (se 1 (by rfl) ⟨1455290, by rfl⟩ : syracuseStep 1940387 = 2910581) B2910581
theorem B2072089 : Blo 1939435 2072089 := bbase (se 2 (by rfl) ⟨777033, by rfl⟩ : syracuseStep 2072089 = 1554067) (by norm_num)
theorem B2762785 : Blo 1939435 2762785 := bstep (se 2 (by rfl) ⟨1036044, by rfl⟩ : syracuseStep 2762785 = 2072089) B2072089
theorem B3683713 : Blo 1939435 3683713 := bstep (se 2 (by rfl) ⟨1381392, by rfl⟩ : syracuseStep 3683713 = 2762785) B2762785
theorem B4911617 : Blo 1939435 4911617 := bstep (se 2 (by rfl) ⟨1841856, by rfl⟩ : syracuseStep 4911617 = 3683713) B3683713
theorem B3274411 : Blo 1939435 3274411 := bstep (se 1 (by rfl) ⟨2455808, by rfl⟩ : syracuseStep 3274411 = 4911617) B4911617
theorem B4365881 : Blo 1939435 4365881 := bstep (se 2 (by rfl) ⟨1637205, by rfl⟩ : syracuseStep 4365881 = 3274411) B3274411
theorem B2910587 : Blo 1939435 2910587 := bstep (se 1 (by rfl) ⟨2182940, by rfl⟩ : syracuseStep 2910587 = 4365881) B4365881
theorem B1940391 : Blo 1939435 1940391 := bstep (se 1 (by rfl) ⟨1455293, by rfl⟩ : syracuseStep 1940391 = 2910587) B2910587
theorem B2182945 : Blo 1939435 2182945 := bbase (se 2 (by rfl) ⟨818604, by rfl⟩ : syracuseStep 2182945 = 1637209) (by norm_num)
theorem B2910593 : Blo 1939435 2910593 := bstep (se 2 (by rfl) ⟨1091472, by rfl⟩ : syracuseStep 2910593 = 2182945) B2182945
theorem B1940395 : Blo 1939435 1940395 := bstep (se 1 (by rfl) ⟨1455296, by rfl⟩ : syracuseStep 1940395 = 2910593) B2910593
theorem B4911637 : Blo 1939435 4911637 := bbase (se 6 (by rfl) ⟨115116, by rfl⟩ : syracuseStep 4911637 = 230233) (by norm_num)
theorem B6548849 : Blo 1939435 6548849 := bstep (se 2 (by rfl) ⟨2455818, by rfl⟩ : syracuseStep 6548849 = 4911637) B4911637
theorem B4365899 : Blo 1939435 4365899 := bstep (se 1 (by rfl) ⟨3274424, by rfl⟩ : syracuseStep 4365899 = 6548849) B6548849
theorem B2910599 : Blo 1939435 2910599 := bstep (se 1 (by rfl) ⟨2182949, by rfl⟩ : syracuseStep 2910599 = 4365899) B4365899
theorem B1940399 : Blo 1939435 1940399 := bstep (se 1 (by rfl) ⟨1455299, by rfl⟩ : syracuseStep 1940399 = 2910599) B2910599
theorem B2910605 : Blo 1939435 2910605 := bbase (se 3 (by rfl) ⟨545738, by rfl⟩ : syracuseStep 2910605 = 1091477) (by norm_num)
theorem B1940403 : Blo 1939435 1940403 := bstep (se 1 (by rfl) ⟨1455302, by rfl⟩ : syracuseStep 1940403 = 2910605) B2910605
theorem B4365917 : Blo 1939435 4365917 := bbase (se 3 (by rfl) ⟨818609, by rfl⟩ : syracuseStep 4365917 = 1637219) (by norm_num)
theorem B2910611 : Blo 1939435 2910611 := bstep (se 1 (by rfl) ⟨2182958, by rfl⟩ : syracuseStep 2910611 = 4365917) B4365917
theorem B1940407 : Blo 1939435 1940407 := bstep (se 1 (by rfl) ⟨1455305, by rfl⟩ : syracuseStep 1940407 = 2910611) B2910611
theorem B3274445 : Blo 1939435 3274445 := bbase (se 3 (by rfl) ⟨613958, by rfl⟩ : syracuseStep 3274445 = 1227917) (by norm_num)
theorem B2182963 : Blo 1939435 2182963 := bstep (se 1 (by rfl) ⟨1637222, by rfl⟩ : syracuseStep 2182963 = 3274445) B3274445
theorem B2910617 : Blo 1939435 2910617 := bstep (se 2 (by rfl) ⟨1091481, by rfl⟩ : syracuseStep 2910617 = 2182963) B2182963
theorem B1940411 : Blo 1939435 1940411 := bstep (se 1 (by rfl) ⟨1455308, by rfl⟩ : syracuseStep 1940411 = 2910617) B2910617
theorem B3496693 : Blo 1939435 3496693 := bbase (se 5 (by rfl) ⟨163907, by rfl⟩ : syracuseStep 3496693 = 327815) (by norm_num)
theorem B4662257 : Blo 1939435 4662257 := bstep (se 2 (by rfl) ⟨1748346, by rfl⟩ : syracuseStep 4662257 = 3496693) B3496693
theorem B12432685 : Blo 1939435 12432685 := bstep (se 3 (by rfl) ⟨2331128, by rfl⟩ : syracuseStep 12432685 = 4662257) B4662257
theorem B16576913 : Blo 1939435 16576913 := bstep (se 2 (by rfl) ⟨6216342, by rfl⟩ : syracuseStep 16576913 = 12432685) B12432685
theorem B11051275 : Blo 1939435 11051275 := bstep (se 1 (by rfl) ⟨8288456, by rfl⟩ : syracuseStep 11051275 = 16576913) B16576913
theorem B14735033 : Blo 1939435 14735033 := bstep (se 2 (by rfl) ⟨5525637, by rfl⟩ : syracuseStep 14735033 = 11051275) B11051275
theorem B9823355 : Blo 1939435 9823355 := bstep (se 1 (by rfl) ⟨7367516, by rfl⟩ : syracuseStep 9823355 = 14735033) B14735033
theorem B6548903 : Blo 1939435 6548903 := bstep (se 1 (by rfl) ⟨4911677, by rfl⟩ : syracuseStep 6548903 = 9823355) B9823355
theorem B4365935 : Blo 1939435 4365935 := bstep (se 1 (by rfl) ⟨3274451, by rfl⟩ : syracuseStep 4365935 = 6548903) B6548903
theorem B2910623 : Blo 1939435 2910623 := bstep (se 1 (by rfl) ⟨2182967, by rfl⟩ : syracuseStep 2910623 = 4365935) B4365935
theorem B1940415 : Blo 1939435 1940415 := bstep (se 1 (by rfl) ⟨1455311, by rfl⟩ : syracuseStep 1940415 = 2910623) B2910623
theorem B2910629 : Blo 1939435 2910629 := bbase (se 4 (by rfl) ⟨272871, by rfl⟩ : syracuseStep 2910629 = 545743) (by norm_num)
theorem B1940419 : Blo 1939435 1940419 := bstep (se 1 (by rfl) ⟨1455314, by rfl⟩ : syracuseStep 1940419 = 2910629) B2910629
theorem B2455849 : Blo 1939435 2455849 := bbase (se 2 (by rfl) ⟨920943, by rfl⟩ : syracuseStep 2455849 = 1841887) (by norm_num)
theorem B3274465 : Blo 1939435 3274465 := bstep (se 2 (by rfl) ⟨1227924, by rfl⟩ : syracuseStep 3274465 = 2455849) B2455849
theorem B4365953 : Blo 1939435 4365953 := bstep (se 2 (by rfl) ⟨1637232, by rfl⟩ : syracuseStep 4365953 = 3274465) B3274465
theorem B2910635 : Blo 1939435 2910635 := bstep (se 1 (by rfl) ⟨2182976, by rfl⟩ : syracuseStep 2910635 = 4365953) B4365953
theorem B1940423 : Blo 1939435 1940423 := bstep (se 1 (by rfl) ⟨1455317, by rfl⟩ : syracuseStep 1940423 = 2910635) B2910635
theorem B2182981 : Blo 1939435 2182981 := bbase (se 4 (by rfl) ⟨204654, by rfl⟩ : syracuseStep 2182981 = 409309) (by norm_num)
theorem B2910641 : Blo 1939435 2910641 := bstep (se 2 (by rfl) ⟨1091490, by rfl⟩ : syracuseStep 2910641 = 2182981) B2182981
theorem B1940427 : Blo 1939435 1940427 := bstep (se 1 (by rfl) ⟨1455320, by rfl⟩ : syracuseStep 1940427 = 2910641) B2910641
theorem B3683789 : Blo 1939435 3683789 := bbase (se 3 (by rfl) ⟨690710, by rfl⟩ : syracuseStep 3683789 = 1381421) (by norm_num)
theorem B2455859 : Blo 1939435 2455859 := bstep (se 1 (by rfl) ⟨1841894, by rfl⟩ : syracuseStep 2455859 = 3683789) B3683789
theorem B6548957 : Blo 1939435 6548957 := bstep (se 3 (by rfl) ⟨1227929, by rfl⟩ : syracuseStep 6548957 = 2455859) B2455859
theorem B4365971 : Blo 1939435 4365971 := bstep (se 1 (by rfl) ⟨3274478, by rfl⟩ : syracuseStep 4365971 = 6548957) B6548957
theorem B2910647 : Blo 1939435 2910647 := bstep (se 1 (by rfl) ⟨2182985, by rfl⟩ : syracuseStep 2910647 = 4365971) B4365971
theorem B1940431 : Blo 1939435 1940431 := bstep (se 1 (by rfl) ⟨1455323, by rfl⟩ : syracuseStep 1940431 = 2910647) B2910647
theorem B2910653 : Blo 1939435 2910653 := bbase (se 3 (by rfl) ⟨545747, by rfl⟩ : syracuseStep 2910653 = 1091495) (by norm_num)
theorem B1940435 : Blo 1939435 1940435 := bstep (se 1 (by rfl) ⟨1455326, by rfl⟩ : syracuseStep 1940435 = 2910653) B2910653
theorem B4365989 : Blo 1939435 4365989 := bbase (se 4 (by rfl) ⟨409311, by rfl⟩ : syracuseStep 4365989 = 818623) (by norm_num)
theorem B2910659 : Blo 1939435 2910659 := bstep (se 1 (by rfl) ⟨2182994, by rfl⟩ : syracuseStep 2910659 = 4365989) B4365989
theorem B1940439 : Blo 1939435 1940439 := bstep (se 1 (by rfl) ⟨1455329, by rfl⟩ : syracuseStep 1940439 = 2910659) B2910659
theorem B4911749 : Blo 1939435 4911749 := bbase (se 4 (by rfl) ⟨460476, by rfl⟩ : syracuseStep 4911749 = 920953) (by norm_num)
theorem B3274499 : Blo 1939435 3274499 := bstep (se 1 (by rfl) ⟨2455874, by rfl⟩ : syracuseStep 3274499 = 4911749) B4911749
theorem B2182999 : Blo 1939435 2182999 := bstep (se 1 (by rfl) ⟨1637249, by rfl⟩ : syracuseStep 2182999 = 3274499) B3274499
theorem B2910665 : Blo 1939435 2910665 := bstep (se 2 (by rfl) ⟨1091499, by rfl⟩ : syracuseStep 2910665 = 2182999) B2182999
theorem B1940443 : Blo 1939435 1940443 := bstep (se 1 (by rfl) ⟨1455332, by rfl⟩ : syracuseStep 1940443 = 2910665) B2910665
theorem B2100421 : Blo 1939435 2100421 := bbase (se 4 (by rfl) ⟨196914, by rfl⟩ : syracuseStep 2100421 = 393829) (by norm_num)
theorem B2800561 : Blo 1939435 2800561 := bstep (se 2 (by rfl) ⟨1050210, by rfl⟩ : syracuseStep 2800561 = 2100421) B2100421
theorem B3734081 : Blo 1939435 3734081 := bstep (se 2 (by rfl) ⟨1400280, by rfl⟩ : syracuseStep 3734081 = 2800561) B2800561
theorem B2489387 : Blo 1939435 2489387 := bstep (se 1 (by rfl) ⟨1867040, by rfl⟩ : syracuseStep 2489387 = 3734081) B3734081
theorem B6638365 : Blo 1939435 6638365 := bstep (se 3 (by rfl) ⟨1244693, by rfl⟩ : syracuseStep 6638365 = 2489387) B2489387
theorem B35404613 : Blo 1939435 35404613 := bstep (se 4 (by rfl) ⟨3319182, by rfl⟩ : syracuseStep 35404613 = 6638365) B6638365
theorem B23603075 : Blo 1939435 23603075 := bstep (se 1 (by rfl) ⟨17702306, by rfl⟩ : syracuseStep 23603075 = 35404613) B35404613
theorem B15735383 : Blo 1939435 15735383 := bstep (se 1 (by rfl) ⟨11801537, by rfl⟩ : syracuseStep 15735383 = 23603075) B23603075
theorem B10490255 : Blo 1939435 10490255 := bstep (se 1 (by rfl) ⟨7867691, by rfl⟩ : syracuseStep 10490255 = 15735383) B15735383
theorem B6993503 : Blo 1939435 6993503 := bstep (se 1 (by rfl) ⟨5245127, by rfl⟩ : syracuseStep 6993503 = 10490255) B10490255
theorem B4662335 : Blo 1939435 4662335 := bstep (se 1 (by rfl) ⟨3496751, by rfl⟩ : syracuseStep 4662335 = 6993503) B6993503
theorem B3108223 : Blo 1939435 3108223 := bstep (se 1 (by rfl) ⟨2331167, by rfl⟩ : syracuseStep 3108223 = 4662335) B4662335
theorem B4144297 : Blo 1939435 4144297 := bstep (se 2 (by rfl) ⟨1554111, by rfl⟩ : syracuseStep 4144297 = 3108223) B3108223
theorem B5525729 : Blo 1939435 5525729 := bstep (se 2 (by rfl) ⟨2072148, by rfl⟩ : syracuseStep 5525729 = 4144297) B4144297
theorem B3683819 : Blo 1939435 3683819 := bstep (se 1 (by rfl) ⟨2762864, by rfl⟩ : syracuseStep 3683819 = 5525729) B5525729
theorem B9823517 : Blo 1939435 9823517 := bstep (se 3 (by rfl) ⟨1841909, by rfl⟩ : syracuseStep 9823517 = 3683819) B3683819
theorem B6549011 : Blo 1939435 6549011 := bstep (se 1 (by rfl) ⟨4911758, by rfl⟩ : syracuseStep 6549011 = 9823517) B9823517
theorem B4366007 : Blo 1939435 4366007 := bstep (se 1 (by rfl) ⟨3274505, by rfl⟩ : syracuseStep 4366007 = 6549011) B6549011
theorem B2910671 : Blo 1939435 2910671 := bstep (se 1 (by rfl) ⟨2183003, by rfl⟩ : syracuseStep 2910671 = 4366007) B4366007
theorem B1940447 : Blo 1939435 1940447 := bstep (se 1 (by rfl) ⟨1455335, by rfl⟩ : syracuseStep 1940447 = 2910671) B2910671
theorem B2910677 : Blo 1939435 2910677 := bbase (se 7 (by rfl) ⟨34109, by rfl⟩ : syracuseStep 2910677 = 68219) (by norm_num)
theorem B1940451 : Blo 1939435 1940451 := bstep (se 1 (by rfl) ⟨1455338, by rfl⟩ : syracuseStep 1940451 = 2910677) B2910677
theorem B7367669 : Blo 1939435 7367669 := bbase (se 5 (by rfl) ⟨345359, by rfl⟩ : syracuseStep 7367669 = 690719) (by norm_num)
theorem B4911779 : Blo 1939435 4911779 := bstep (se 1 (by rfl) ⟨3683834, by rfl⟩ : syracuseStep 4911779 = 7367669) B7367669
theorem B3274519 : Blo 1939435 3274519 := bstep (se 1 (by rfl) ⟨2455889, by rfl⟩ : syracuseStep 3274519 = 4911779) B4911779
theorem B4366025 : Blo 1939435 4366025 := bstep (se 2 (by rfl) ⟨1637259, by rfl⟩ : syracuseStep 4366025 = 3274519) B3274519
theorem B2910683 : Blo 1939435 2910683 := bstep (se 1 (by rfl) ⟨2183012, by rfl⟩ : syracuseStep 2910683 = 4366025) B4366025
theorem B1940455 : Blo 1939435 1940455 := bstep (se 1 (by rfl) ⟨1455341, by rfl⟩ : syracuseStep 1940455 = 2910683) B2910683
theorem B2183017 : Blo 1939435 2183017 := bbase (se 2 (by rfl) ⟨818631, by rfl⟩ : syracuseStep 2183017 = 1637263) (by norm_num)
theorem B2910689 : Blo 1939435 2910689 := bstep (se 2 (by rfl) ⟨1091508, by rfl⟩ : syracuseStep 2910689 = 2183017) B2183017
theorem B1940459 : Blo 1939435 1940459 := bstep (se 1 (by rfl) ⟨1455344, by rfl⟩ : syracuseStep 1940459 = 2910689) B2910689
theorem B4662373 : Blo 1939435 4662373 := bbase (se 4 (by rfl) ⟨437097, by rfl⟩ : syracuseStep 4662373 = 874195) (by norm_num)
theorem B6216497 : Blo 1939435 6216497 := bstep (se 2 (by rfl) ⟨2331186, by rfl⟩ : syracuseStep 6216497 = 4662373) B4662373
theorem B4144331 : Blo 1939435 4144331 := bstep (se 1 (by rfl) ⟨3108248, by rfl⟩ : syracuseStep 4144331 = 6216497) B6216497
theorem B11051549 : Blo 1939435 11051549 := bstep (se 3 (by rfl) ⟨2072165, by rfl⟩ : syracuseStep 11051549 = 4144331) B4144331
theorem B7367699 : Blo 1939435 7367699 := bstep (se 1 (by rfl) ⟨5525774, by rfl⟩ : syracuseStep 7367699 = 11051549) B11051549
theorem B4911799 : Blo 1939435 4911799 := bstep (se 1 (by rfl) ⟨3683849, by rfl⟩ : syracuseStep 4911799 = 7367699) B7367699
theorem B6549065 : Blo 1939435 6549065 := bstep (se 2 (by rfl) ⟨2455899, by rfl⟩ : syracuseStep 6549065 = 4911799) B4911799
theorem B4366043 : Blo 1939435 4366043 := bstep (se 1 (by rfl) ⟨3274532, by rfl⟩ : syracuseStep 4366043 = 6549065) B6549065
theorem B2910695 : Blo 1939435 2910695 := bstep (se 1 (by rfl) ⟨2183021, by rfl⟩ : syracuseStep 2910695 = 4366043) B4366043
theorem B1940463 : Blo 1939435 1940463 := bstep (se 1 (by rfl) ⟨1455347, by rfl⟩ : syracuseStep 1940463 = 2910695) B2910695
theorem B2910701 : Blo 1939435 2910701 := bbase (se 3 (by rfl) ⟨545756, by rfl⟩ : syracuseStep 2910701 = 1091513) (by norm_num)
theorem B1940467 : Blo 1939435 1940467 := bstep (se 1 (by rfl) ⟨1455350, by rfl⟩ : syracuseStep 1940467 = 2910701) B2910701
theorem B4366061 : Blo 1939435 4366061 := bbase (se 3 (by rfl) ⟨818636, by rfl⟩ : syracuseStep 4366061 = 1637273) (by norm_num)
theorem B2910707 : Blo 1939435 2910707 := bstep (se 1 (by rfl) ⟨2183030, by rfl⟩ : syracuseStep 2910707 = 4366061) B4366061
theorem B1940471 : Blo 1939435 1940471 := bstep (se 1 (by rfl) ⟨1455353, by rfl⟩ : syracuseStep 1940471 = 2910707) B2910707
theorem B3108269 : Blo 1939435 3108269 := bbase (se 3 (by rfl) ⟨582800, by rfl⟩ : syracuseStep 3108269 = 1165601) (by norm_num)
theorem B2072179 : Blo 1939435 2072179 := bstep (se 1 (by rfl) ⟨1554134, by rfl⟩ : syracuseStep 2072179 = 3108269) B3108269
theorem B2762905 : Blo 1939435 2762905 := bstep (se 2 (by rfl) ⟨1036089, by rfl⟩ : syracuseStep 2762905 = 2072179) B2072179
theorem B3683873 : Blo 1939435 3683873 := bstep (se 2 (by rfl) ⟨1381452, by rfl⟩ : syracuseStep 3683873 = 2762905) B2762905
theorem B2455915 : Blo 1939435 2455915 := bstep (se 1 (by rfl) ⟨1841936, by rfl⟩ : syracuseStep 2455915 = 3683873) B3683873
theorem B3274553 : Blo 1939435 3274553 := bstep (se 2 (by rfl) ⟨1227957, by rfl⟩ : syracuseStep 3274553 = 2455915) B2455915
theorem B2183035 : Blo 1939435 2183035 := bstep (se 1 (by rfl) ⟨1637276, by rfl⟩ : syracuseStep 2183035 = 3274553) B3274553
theorem B2910713 : Blo 1939435 2910713 := bstep (se 2 (by rfl) ⟨1091517, by rfl⟩ : syracuseStep 2910713 = 2183035) B2183035
theorem B1940475 : Blo 1939435 1940475 := bstep (se 1 (by rfl) ⟨1455356, by rfl⟩ : syracuseStep 1940475 = 2910713) B2910713
theorem B4790501 : Blo 1939435 4790501 := bbase (se 4 (by rfl) ⟨449109, by rfl⟩ : syracuseStep 4790501 = 898219) (by norm_num)
theorem B3193667 : Blo 1939435 3193667 := bstep (se 1 (by rfl) ⟨2395250, by rfl⟩ : syracuseStep 3193667 = 4790501) B4790501
theorem B2129111 : Blo 1939435 2129111 := bstep (se 1 (by rfl) ⟨1596833, by rfl⟩ : syracuseStep 2129111 = 3193667) B3193667
theorem B90842069 : Blo 1939435 90842069 := bstep (se 7 (by rfl) ⟨1064555, by rfl⟩ : syracuseStep 90842069 = 2129111) B2129111
theorem B60561379 : Blo 1939435 60561379 := bstep (se 1 (by rfl) ⟨45421034, by rfl⟩ : syracuseStep 60561379 = 90842069) B90842069
theorem B80748505 : Blo 1939435 80748505 := bstep (se 2 (by rfl) ⟨30280689, by rfl⟩ : syracuseStep 80748505 = 60561379) B60561379
theorem B107664673 : Blo 1939435 107664673 := bstep (se 2 (by rfl) ⟨40374252, by rfl⟩ : syracuseStep 107664673 = 80748505) B80748505
theorem B143552897 : Blo 1939435 143552897 := bstep (se 2 (by rfl) ⟨53832336, by rfl⟩ : syracuseStep 143552897 = 107664673) B107664673
theorem B95701931 : Blo 1939435 95701931 := bstep (se 1 (by rfl) ⟨71776448, by rfl⟩ : syracuseStep 95701931 = 143552897) B143552897
theorem B63801287 : Blo 1939435 63801287 := bstep (se 1 (by rfl) ⟨47850965, by rfl⟩ : syracuseStep 63801287 = 95701931) B95701931
theorem B42534191 : Blo 1939435 42534191 := bstep (se 1 (by rfl) ⟨31900643, by rfl⟩ : syracuseStep 42534191 = 63801287) B63801287
theorem B113424509 : Blo 1939435 113424509 := bstep (se 3 (by rfl) ⟨21267095, by rfl⟩ : syracuseStep 113424509 = 42534191) B42534191
theorem B75616339 : Blo 1939435 75616339 := bstep (se 1 (by rfl) ⟨56712254, by rfl⟩ : syracuseStep 75616339 = 113424509) B113424509
theorem B100821785 : Blo 1939435 100821785 := bstep (se 2 (by rfl) ⟨37808169, by rfl⟩ : syracuseStep 100821785 = 75616339) B75616339
theorem B1075432373 : Blo 1939435 1075432373 := bstep (se 5 (by rfl) ⟨50410892, by rfl⟩ : syracuseStep 1075432373 = 100821785) B100821785
theorem B716954915 : Blo 1939435 716954915 := bstep (se 1 (by rfl) ⟨537716186, by rfl⟩ : syracuseStep 716954915 = 1075432373) B1075432373
theorem B477969943 : Blo 1939435 477969943 := bstep (se 1 (by rfl) ⟨358477457, by rfl⟩ : syracuseStep 477969943 = 716954915) B716954915
theorem B637293257 : Blo 1939435 637293257 := bstep (se 2 (by rfl) ⟨238984971, by rfl⟩ : syracuseStep 637293257 = 477969943) B477969943
theorem B424862171 : Blo 1939435 424862171 := bstep (se 1 (by rfl) ⟨318646628, by rfl⟩ : syracuseStep 424862171 = 637293257) B637293257
theorem B283241447 : Blo 1939435 283241447 := bstep (se 1 (by rfl) ⟨212431085, by rfl⟩ : syracuseStep 283241447 = 424862171) B424862171
theorem B188827631 : Blo 1939435 188827631 := bstep (se 1 (by rfl) ⟨141620723, by rfl⟩ : syracuseStep 188827631 = 283241447) B283241447
theorem B125885087 : Blo 1939435 125885087 := bstep (se 1 (by rfl) ⟨94413815, by rfl⟩ : syracuseStep 125885087 = 188827631) B188827631
theorem B83923391 : Blo 1939435 83923391 := bstep (se 1 (by rfl) ⟨62942543, by rfl⟩ : syracuseStep 83923391 = 125885087) B125885087
theorem B55948927 : Blo 1939435 55948927 := bstep (se 1 (by rfl) ⟨41961695, by rfl⟩ : syracuseStep 55948927 = 83923391) B83923391
theorem B74598569 : Blo 1939435 74598569 := bstep (se 2 (by rfl) ⟨27974463, by rfl⟩ : syracuseStep 74598569 = 55948927) B55948927
theorem B49732379 : Blo 1939435 49732379 := bstep (se 1 (by rfl) ⟨37299284, by rfl⟩ : syracuseStep 49732379 = 74598569) B74598569
theorem B33154919 : Blo 1939435 33154919 := bstep (se 1 (by rfl) ⟨24866189, by rfl⟩ : syracuseStep 33154919 = 49732379) B49732379
theorem B22103279 : Blo 1939435 22103279 := bstep (se 1 (by rfl) ⟨16577459, by rfl⟩ : syracuseStep 22103279 = 33154919) B33154919
theorem B14735519 : Blo 1939435 14735519 := bstep (se 1 (by rfl) ⟨11051639, by rfl⟩ : syracuseStep 14735519 = 22103279) B22103279
theorem B9823679 : Blo 1939435 9823679 := bstep (se 1 (by rfl) ⟨7367759, by rfl⟩ : syracuseStep 9823679 = 14735519) B14735519
theorem B6549119 : Blo 1939435 6549119 := bstep (se 1 (by rfl) ⟨4911839, by rfl⟩ : syracuseStep 6549119 = 9823679) B9823679
theorem B4366079 : Blo 1939435 4366079 := bstep (se 1 (by rfl) ⟨3274559, by rfl⟩ : syracuseStep 4366079 = 6549119) B6549119
theorem B2910719 : Blo 1939435 2910719 := bstep (se 1 (by rfl) ⟨2183039, by rfl⟩ : syracuseStep 2910719 = 4366079) B4366079
theorem B1940479 : Blo 1939435 1940479 := bstep (se 1 (by rfl) ⟨1455359, by rfl⟩ : syracuseStep 1940479 = 2910719) B2910719
theorem B2910725 : Blo 1939435 2910725 := bbase (se 4 (by rfl) ⟨272880, by rfl⟩ : syracuseStep 2910725 = 545761) (by norm_num)
theorem B1940483 : Blo 1939435 1940483 := bstep (se 1 (by rfl) ⟨1455362, by rfl⟩ : syracuseStep 1940483 = 2910725) B2910725
theorem B3274573 : Blo 1939435 3274573 := bbase (se 3 (by rfl) ⟨613982, by rfl⟩ : syracuseStep 3274573 = 1227965) (by norm_num)
theorem B4366097 : Blo 1939435 4366097 := bstep (se 2 (by rfl) ⟨1637286, by rfl⟩ : syracuseStep 4366097 = 3274573) B3274573
theorem B2910731 : Blo 1939435 2910731 := bstep (se 1 (by rfl) ⟨2183048, by rfl⟩ : syracuseStep 2910731 = 4366097) B4366097
theorem B1940487 : Blo 1939435 1940487 := bstep (se 1 (by rfl) ⟨1455365, by rfl⟩ : syracuseStep 1940487 = 2910731) B2910731
theorem B2183053 : Blo 1939435 2183053 := bbase (se 3 (by rfl) ⟨409322, by rfl⟩ : syracuseStep 2183053 = 818645) (by norm_num)
theorem B2910737 : Blo 1939435 2910737 := bstep (se 2 (by rfl) ⟨1091526, by rfl⟩ : syracuseStep 2910737 = 2183053) B2183053
theorem B1940491 : Blo 1939435 1940491 := bstep (se 1 (by rfl) ⟨1455368, by rfl⟩ : syracuseStep 1940491 = 2910737) B2910737
theorem B6549173 : Blo 1939435 6549173 := bbase (se 5 (by rfl) ⟨306992, by rfl⟩ : syracuseStep 6549173 = 613985) (by norm_num)
theorem B4366115 : Blo 1939435 4366115 := bstep (se 1 (by rfl) ⟨3274586, by rfl⟩ : syracuseStep 4366115 = 6549173) B6549173
theorem B2910743 : Blo 1939435 2910743 := bstep (se 1 (by rfl) ⟨2183057, by rfl⟩ : syracuseStep 2910743 = 4366115) B4366115
theorem B1940495 : Blo 1939435 1940495 := bstep (se 1 (by rfl) ⟨1455371, by rfl⟩ : syracuseStep 1940495 = 2910743) B2910743
theorem B2910749 : Blo 1939435 2910749 := bbase (se 3 (by rfl) ⟨545765, by rfl⟩ : syracuseStep 2910749 = 1091531) (by norm_num)
theorem B1940499 : Blo 1939435 1940499 := bstep (se 1 (by rfl) ⟨1455374, by rfl⟩ : syracuseStep 1940499 = 2910749) B2910749
theorem B4366133 : Blo 1939435 4366133 := bbase (se 5 (by rfl) ⟨204662, by rfl⟩ : syracuseStep 4366133 = 409325) (by norm_num)
theorem B2910755 : Blo 1939435 2910755 := bstep (se 1 (by rfl) ⟨2183066, by rfl⟩ : syracuseStep 2910755 = 4366133) B4366133
theorem B1940503 : Blo 1939435 1940503 := bstep (se 1 (by rfl) ⟨1455377, by rfl⟩ : syracuseStep 1940503 = 2910755) B2910755
theorem B13277141 : Blo 1939435 13277141 := bbase (se 7 (by rfl) ⟨155591, by rfl⟩ : syracuseStep 13277141 = 311183) (by norm_num)
theorem B8851427 : Blo 1939435 8851427 := bstep (se 1 (by rfl) ⟨6638570, by rfl⟩ : syracuseStep 8851427 = 13277141) B13277141
theorem B5900951 : Blo 1939435 5900951 := bstep (se 1 (by rfl) ⟨4425713, by rfl⟩ : syracuseStep 5900951 = 8851427) B8851427
theorem B15735869 : Blo 1939435 15735869 := bstep (se 3 (by rfl) ⟨2950475, by rfl⟩ : syracuseStep 15735869 = 5900951) B5900951
theorem B10490579 : Blo 1939435 10490579 := bstep (se 1 (by rfl) ⟨7867934, by rfl⟩ : syracuseStep 10490579 = 15735869) B15735869
theorem B6993719 : Blo 1939435 6993719 := bstep (se 1 (by rfl) ⟨5245289, by rfl⟩ : syracuseStep 6993719 = 10490579) B10490579
theorem B4662479 : Blo 1939435 4662479 := bstep (se 1 (by rfl) ⟨3496859, by rfl⟩ : syracuseStep 4662479 = 6993719) B6993719
theorem B12433277 : Blo 1939435 12433277 := bstep (se 3 (by rfl) ⟨2331239, by rfl⟩ : syracuseStep 12433277 = 4662479) B4662479
theorem B8288851 : Blo 1939435 8288851 := bstep (se 1 (by rfl) ⟨6216638, by rfl⟩ : syracuseStep 8288851 = 12433277) B12433277
theorem B11051801 : Blo 1939435 11051801 := bstep (se 2 (by rfl) ⟨4144425, by rfl⟩ : syracuseStep 11051801 = 8288851) B8288851
theorem B7367867 : Blo 1939435 7367867 := bstep (se 1 (by rfl) ⟨5525900, by rfl⟩ : syracuseStep 7367867 = 11051801) B11051801
theorem B4911911 : Blo 1939435 4911911 := bstep (se 1 (by rfl) ⟨3683933, by rfl⟩ : syracuseStep 4911911 = 7367867) B7367867
theorem B3274607 : Blo 1939435 3274607 := bstep (se 1 (by rfl) ⟨2455955, by rfl⟩ : syracuseStep 3274607 = 4911911) B4911911
theorem B2183071 : Blo 1939435 2183071 := bstep (se 1 (by rfl) ⟨1637303, by rfl⟩ : syracuseStep 2183071 = 3274607) B3274607
theorem B2910761 : Blo 1939435 2910761 := bstep (se 2 (by rfl) ⟨1091535, by rfl⟩ : syracuseStep 2910761 = 2183071) B2183071
theorem B1940507 : Blo 1939435 1940507 := bstep (se 1 (by rfl) ⟨1455380, by rfl⟩ : syracuseStep 1940507 = 2910761) B2910761
theorem B12433301 : Blo 1939435 12433301 := bbase (se 6 (by rfl) ⟨291405, by rfl⟩ : syracuseStep 12433301 = 582811) (by norm_num)
theorem B8288867 : Blo 1939435 8288867 := bstep (se 1 (by rfl) ⟨6216650, by rfl⟩ : syracuseStep 8288867 = 12433301) B12433301
theorem B5525911 : Blo 1939435 5525911 := bstep (se 1 (by rfl) ⟨4144433, by rfl⟩ : syracuseStep 5525911 = 8288867) B8288867
theorem B7367881 : Blo 1939435 7367881 := bstep (se 2 (by rfl) ⟨2762955, by rfl⟩ : syracuseStep 7367881 = 5525911) B5525911
theorem B9823841 : Blo 1939435 9823841 := bstep (se 2 (by rfl) ⟨3683940, by rfl⟩ : syracuseStep 9823841 = 7367881) B7367881
theorem B6549227 : Blo 1939435 6549227 := bstep (se 1 (by rfl) ⟨4911920, by rfl⟩ : syracuseStep 6549227 = 9823841) B9823841
theorem B4366151 : Blo 1939435 4366151 := bstep (se 1 (by rfl) ⟨3274613, by rfl⟩ : syracuseStep 4366151 = 6549227) B6549227
theorem B2910767 : Blo 1939435 2910767 := bstep (se 1 (by rfl) ⟨2183075, by rfl⟩ : syracuseStep 2910767 = 4366151) B4366151
theorem B1940511 : Blo 1939435 1940511 := bstep (se 1 (by rfl) ⟨1455383, by rfl⟩ : syracuseStep 1940511 = 2910767) B2910767
theorem B2910773 : Blo 1939435 2910773 := bbase (se 5 (by rfl) ⟨136442, by rfl⟩ : syracuseStep 2910773 = 272885) (by norm_num)
theorem B1940515 : Blo 1939435 1940515 := bstep (se 1 (by rfl) ⟨1455386, by rfl⟩ : syracuseStep 1940515 = 2910773) B2910773
theorem B4911941 : Blo 1939435 4911941 := bbase (se 4 (by rfl) ⟨460494, by rfl⟩ : syracuseStep 4911941 = 920989) (by norm_num)
theorem B3274627 : Blo 1939435 3274627 := bstep (se 1 (by rfl) ⟨2455970, by rfl⟩ : syracuseStep 3274627 = 4911941) B4911941
theorem B4366169 : Blo 1939435 4366169 := bstep (se 2 (by rfl) ⟨1637313, by rfl⟩ : syracuseStep 4366169 = 3274627) B3274627
theorem B2910779 : Blo 1939435 2910779 := bstep (se 1 (by rfl) ⟨2183084, by rfl⟩ : syracuseStep 2910779 = 4366169) B4366169
theorem B1940519 : Blo 1939435 1940519 := bstep (se 1 (by rfl) ⟨1455389, by rfl⟩ : syracuseStep 1940519 = 2910779) B2910779
theorem B2183089 : Blo 1939435 2183089 := bbase (se 2 (by rfl) ⟨818658, by rfl⟩ : syracuseStep 2183089 = 1637317) (by norm_num)
theorem B2910785 : Blo 1939435 2910785 := bstep (se 2 (by rfl) ⟨1091544, by rfl⟩ : syracuseStep 2910785 = 2183089) B2183089
theorem B1940523 : Blo 1939435 1940523 := bstep (se 1 (by rfl) ⟨1455392, by rfl⟩ : syracuseStep 1940523 = 2910785) B2910785
theorem B5525957 : Blo 1939435 5525957 := bbase (se 4 (by rfl) ⟨518058, by rfl⟩ : syracuseStep 5525957 = 1036117) (by norm_num)
theorem B3683971 : Blo 1939435 3683971 := bstep (se 1 (by rfl) ⟨2762978, by rfl⟩ : syracuseStep 3683971 = 5525957) B5525957
theorem B4911961 : Blo 1939435 4911961 := bstep (se 2 (by rfl) ⟨1841985, by rfl⟩ : syracuseStep 4911961 = 3683971) B3683971
theorem B6549281 : Blo 1939435 6549281 := bstep (se 2 (by rfl) ⟨2455980, by rfl⟩ : syracuseStep 6549281 = 4911961) B4911961
theorem B4366187 : Blo 1939435 4366187 := bstep (se 1 (by rfl) ⟨3274640, by rfl⟩ : syracuseStep 4366187 = 6549281) B6549281
theorem B2910791 : Blo 1939435 2910791 := bstep (se 1 (by rfl) ⟨2183093, by rfl⟩ : syracuseStep 2910791 = 4366187) B4366187
theorem B1940527 : Blo 1939435 1940527 := bstep (se 1 (by rfl) ⟨1455395, by rfl⟩ : syracuseStep 1940527 = 2910791) B2910791
theorem B2910797 : Blo 1939435 2910797 := bbase (se 3 (by rfl) ⟨545774, by rfl⟩ : syracuseStep 2910797 = 1091549) (by norm_num)
theorem B1940531 : Blo 1939435 1940531 := bstep (se 1 (by rfl) ⟨1455398, by rfl⟩ : syracuseStep 1940531 = 2910797) B2910797
theorem B4366205 : Blo 1939435 4366205 := bbase (se 3 (by rfl) ⟨818663, by rfl⟩ : syracuseStep 4366205 = 1637327) (by norm_num)
theorem B2910803 : Blo 1939435 2910803 := bstep (se 1 (by rfl) ⟨2183102, by rfl⟩ : syracuseStep 2910803 = 4366205) B4366205
theorem B1940535 : Blo 1939435 1940535 := bstep (se 1 (by rfl) ⟨1455401, by rfl⟩ : syracuseStep 1940535 = 2910803) B2910803
theorem B3274661 : Blo 1939435 3274661 := bbase (se 4 (by rfl) ⟨306999, by rfl⟩ : syracuseStep 3274661 = 613999) (by norm_num)
theorem B2183107 : Blo 1939435 2183107 := bstep (se 1 (by rfl) ⟨1637330, by rfl⟩ : syracuseStep 2183107 = 3274661) B3274661
theorem B2910809 : Blo 1939435 2910809 := bstep (se 2 (by rfl) ⟨1091553, by rfl⟩ : syracuseStep 2910809 = 2183107) B2183107
theorem B1940539 : Blo 1939435 1940539 := bstep (se 1 (by rfl) ⟨1455404, by rfl⟩ : syracuseStep 1940539 = 2910809) B2910809
theorem B3496925 : Blo 1939435 3496925 := bbase (se 3 (by rfl) ⟨655673, by rfl⟩ : syracuseStep 3496925 = 1311347) (by norm_num)
theorem B2331283 : Blo 1939435 2331283 := bstep (se 1 (by rfl) ⟨1748462, by rfl⟩ : syracuseStep 2331283 = 3496925) B3496925
theorem B3108377 : Blo 1939435 3108377 := bstep (se 2 (by rfl) ⟨1165641, by rfl⟩ : syracuseStep 3108377 = 2331283) B2331283
theorem B2072251 : Blo 1939435 2072251 := bstep (se 1 (by rfl) ⟨1554188, by rfl⟩ : syracuseStep 2072251 = 3108377) B3108377
theorem B2763001 : Blo 1939435 2763001 := bstep (se 2 (by rfl) ⟨1036125, by rfl⟩ : syracuseStep 2763001 = 2072251) B2072251
theorem B14736005 : Blo 1939435 14736005 := bstep (se 4 (by rfl) ⟨1381500, by rfl⟩ : syracuseStep 14736005 = 2763001) B2763001
theorem B9824003 : Blo 1939435 9824003 := bstep (se 1 (by rfl) ⟨7368002, by rfl⟩ : syracuseStep 9824003 = 14736005) B14736005
theorem B6549335 : Blo 1939435 6549335 := bstep (se 1 (by rfl) ⟨4912001, by rfl⟩ : syracuseStep 6549335 = 9824003) B9824003
theorem B4366223 : Blo 1939435 4366223 := bstep (se 1 (by rfl) ⟨3274667, by rfl⟩ : syracuseStep 4366223 = 6549335) B6549335
theorem B2910815 : Blo 1939435 2910815 := bstep (se 1 (by rfl) ⟨2183111, by rfl⟩ : syracuseStep 2910815 = 4366223) B4366223
theorem B1940543 : Blo 1939435 1940543 := bstep (se 1 (by rfl) ⟨1455407, by rfl⟩ : syracuseStep 1940543 = 2910815) B2910815
theorem B2910821 : Blo 1939435 2910821 := bbase (se 4 (by rfl) ⟨272889, by rfl⟩ : syracuseStep 2910821 = 545779) (by norm_num)
theorem B1940547 : Blo 1939435 1940547 := bstep (se 1 (by rfl) ⟨1455410, by rfl⟩ : syracuseStep 1940547 = 2910821) B2910821
theorem B2763013 : Blo 1939435 2763013 := bbase (se 4 (by rfl) ⟨259032, by rfl⟩ : syracuseStep 2763013 = 518065) (by norm_num)
theorem B3684017 : Blo 1939435 3684017 := bstep (se 2 (by rfl) ⟨1381506, by rfl⟩ : syracuseStep 3684017 = 2763013) B2763013
theorem B2456011 : Blo 1939435 2456011 := bstep (se 1 (by rfl) ⟨1842008, by rfl⟩ : syracuseStep 2456011 = 3684017) B3684017
theorem B3274681 : Blo 1939435 3274681 := bstep (se 2 (by rfl) ⟨1228005, by rfl⟩ : syracuseStep 3274681 = 2456011) B2456011
theorem B4366241 : Blo 1939435 4366241 := bstep (se 2 (by rfl) ⟨1637340, by rfl⟩ : syracuseStep 4366241 = 3274681) B3274681
theorem B2910827 : Blo 1939435 2910827 := bstep (se 1 (by rfl) ⟨2183120, by rfl⟩ : syracuseStep 2910827 = 4366241) B4366241
theorem B1940551 : Blo 1939435 1940551 := bstep (se 1 (by rfl) ⟨1455413, by rfl⟩ : syracuseStep 1940551 = 2910827) B2910827
theorem B2183125 : Blo 1939435 2183125 := bbase (se 7 (by rfl) ⟨25583, by rfl⟩ : syracuseStep 2183125 = 51167) (by norm_num)
theorem B2910833 : Blo 1939435 2910833 := bstep (se 2 (by rfl) ⟨1091562, by rfl⟩ : syracuseStep 2910833 = 2183125) B2183125
theorem B1940555 : Blo 1939435 1940555 := bstep (se 1 (by rfl) ⟨1455416, by rfl⟩ : syracuseStep 1940555 = 2910833) B2910833
theorem B2456021 : Blo 1939435 2456021 := bbase (se 7 (by rfl) ⟨28781, by rfl⟩ : syracuseStep 2456021 = 57563) (by norm_num)
theorem B6549389 : Blo 1939435 6549389 := bstep (se 3 (by rfl) ⟨1228010, by rfl⟩ : syracuseStep 6549389 = 2456021) B2456021
theorem B4366259 : Blo 1939435 4366259 := bstep (se 1 (by rfl) ⟨3274694, by rfl⟩ : syracuseStep 4366259 = 6549389) B6549389
theorem B2910839 : Blo 1939435 2910839 := bstep (se 1 (by rfl) ⟨2183129, by rfl⟩ : syracuseStep 2910839 = 4366259) B4366259
theorem B1940559 : Blo 1939435 1940559 := bstep (se 1 (by rfl) ⟨1455419, by rfl⟩ : syracuseStep 1940559 = 2910839) B2910839
theorem B2910845 : Blo 1939435 2910845 := bbase (se 3 (by rfl) ⟨545783, by rfl⟩ : syracuseStep 2910845 = 1091567) (by norm_num)
theorem B1940563 : Blo 1939435 1940563 := bstep (se 1 (by rfl) ⟨1455422, by rfl⟩ : syracuseStep 1940563 = 2910845) B2910845
theorem B4366277 : Blo 1939435 4366277 := bbase (se 4 (by rfl) ⟨409338, by rfl⟩ : syracuseStep 4366277 = 818677) (by norm_num)
theorem B2910851 : Blo 1939435 2910851 := bstep (se 1 (by rfl) ⟨2183138, by rfl⟩ : syracuseStep 2910851 = 4366277) B4366277
theorem B1940567 : Blo 1939435 1940567 := bstep (se 1 (by rfl) ⟨1455425, by rfl⟩ : syracuseStep 1940567 = 2910851) B2910851
theorem B8289125 : Blo 1939435 8289125 := bbase (se 4 (by rfl) ⟨777105, by rfl⟩ : syracuseStep 8289125 = 1554211) (by norm_num)
theorem B5526083 : Blo 1939435 5526083 := bstep (se 1 (by rfl) ⟨4144562, by rfl⟩ : syracuseStep 5526083 = 8289125) B8289125
theorem B3684055 : Blo 1939435 3684055 := bstep (se 1 (by rfl) ⟨2763041, by rfl⟩ : syracuseStep 3684055 = 5526083) B5526083
theorem B4912073 : Blo 1939435 4912073 := bstep (se 2 (by rfl) ⟨1842027, by rfl⟩ : syracuseStep 4912073 = 3684055) B3684055
theorem B3274715 : Blo 1939435 3274715 := bstep (se 1 (by rfl) ⟨2456036, by rfl⟩ : syracuseStep 3274715 = 4912073) B4912073
theorem B2183143 : Blo 1939435 2183143 := bstep (se 1 (by rfl) ⟨1637357, by rfl⟩ : syracuseStep 2183143 = 3274715) B3274715
theorem B2910857 : Blo 1939435 2910857 := bstep (se 2 (by rfl) ⟨1091571, by rfl⟩ : syracuseStep 2910857 = 2183143) B2183143
theorem B1940571 : Blo 1939435 1940571 := bstep (se 1 (by rfl) ⟨1455428, by rfl⟩ : syracuseStep 1940571 = 2910857) B2910857
theorem B9824165 : Blo 1939435 9824165 := bbase (se 4 (by rfl) ⟨921015, by rfl⟩ : syracuseStep 9824165 = 1842031) (by norm_num)
theorem B6549443 : Blo 1939435 6549443 := bstep (se 1 (by rfl) ⟨4912082, by rfl⟩ : syracuseStep 6549443 = 9824165) B9824165
theorem B4366295 : Blo 1939435 4366295 := bstep (se 1 (by rfl) ⟨3274721, by rfl⟩ : syracuseStep 4366295 = 6549443) B6549443
theorem B2910863 : Blo 1939435 2910863 := bstep (se 1 (by rfl) ⟨2183147, by rfl⟩ : syracuseStep 2910863 = 4366295) B4366295
theorem B1940575 : Blo 1939435 1940575 := bstep (se 1 (by rfl) ⟨1455431, by rfl⟩ : syracuseStep 1940575 = 2910863) B2910863
theorem B2910869 : Blo 1939435 2910869 := bbase (se 6 (by rfl) ⟨68223, by rfl⟩ : syracuseStep 2910869 = 136447) (by norm_num)
theorem B1940579 : Blo 1939435 1940579 := bstep (se 1 (by rfl) ⟨1455434, by rfl⟩ : syracuseStep 1940579 = 2910869) B2910869
theorem B18650645 : Blo 1939435 18650645 := bbase (se 6 (by rfl) ⟨437124, by rfl⟩ : syracuseStep 18650645 = 874249) (by norm_num)
theorem B12433763 : Blo 1939435 12433763 := bstep (se 1 (by rfl) ⟨9325322, by rfl⟩ : syracuseStep 12433763 = 18650645) B18650645
theorem B8289175 : Blo 1939435 8289175 := bstep (se 1 (by rfl) ⟨6216881, by rfl⟩ : syracuseStep 8289175 = 12433763) B12433763
theorem B11052233 : Blo 1939435 11052233 := bstep (se 2 (by rfl) ⟨4144587, by rfl⟩ : syracuseStep 11052233 = 8289175) B8289175
theorem B7368155 : Blo 1939435 7368155 := bstep (se 1 (by rfl) ⟨5526116, by rfl⟩ : syracuseStep 7368155 = 11052233) B11052233
theorem B4912103 : Blo 1939435 4912103 := bstep (se 1 (by rfl) ⟨3684077, by rfl⟩ : syracuseStep 4912103 = 7368155) B7368155
theorem B3274735 : Blo 1939435 3274735 := bstep (se 1 (by rfl) ⟨2456051, by rfl⟩ : syracuseStep 3274735 = 4912103) B4912103
theorem B4366313 : Blo 1939435 4366313 := bstep (se 2 (by rfl) ⟨1637367, by rfl⟩ : syracuseStep 4366313 = 3274735) B3274735
theorem B2910875 : Blo 1939435 2910875 := bstep (se 1 (by rfl) ⟨2183156, by rfl⟩ : syracuseStep 2910875 = 4366313) B4366313
theorem B1940583 : Blo 1939435 1940583 := bstep (se 1 (by rfl) ⟨1455437, by rfl⟩ : syracuseStep 1940583 = 2910875) B2910875
theorem B2183161 : Blo 1939435 2183161 := bbase (se 2 (by rfl) ⟨818685, by rfl⟩ : syracuseStep 2183161 = 1637371) (by norm_num)
theorem B2910881 : Blo 1939435 2910881 := bstep (se 2 (by rfl) ⟨1091580, by rfl⟩ : syracuseStep 2910881 = 2183161) B2183161
theorem B1940587 : Blo 1939435 1940587 := bstep (se 1 (by rfl) ⟨1455440, by rfl⟩ : syracuseStep 1940587 = 2910881) B2910881
theorem B6994021 : Blo 1939435 6994021 := bbase (se 4 (by rfl) ⟨655689, by rfl⟩ : syracuseStep 6994021 = 1311379) (by norm_num)
theorem B9325361 : Blo 1939435 9325361 := bstep (se 2 (by rfl) ⟨3497010, by rfl⟩ : syracuseStep 9325361 = 6994021) B6994021
theorem B6216907 : Blo 1939435 6216907 := bstep (se 1 (by rfl) ⟨4662680, by rfl⟩ : syracuseStep 6216907 = 9325361) B9325361
theorem B8289209 : Blo 1939435 8289209 := bstep (se 2 (by rfl) ⟨3108453, by rfl⟩ : syracuseStep 8289209 = 6216907) B6216907
theorem B5526139 : Blo 1939435 5526139 := bstep (se 1 (by rfl) ⟨4144604, by rfl⟩ : syracuseStep 5526139 = 8289209) B8289209
theorem B7368185 : Blo 1939435 7368185 := bstep (se 2 (by rfl) ⟨2763069, by rfl⟩ : syracuseStep 7368185 = 5526139) B5526139
theorem B4912123 : Blo 1939435 4912123 := bstep (se 1 (by rfl) ⟨3684092, by rfl⟩ : syracuseStep 4912123 = 7368185) B7368185
theorem B6549497 : Blo 1939435 6549497 := bstep (se 2 (by rfl) ⟨2456061, by rfl⟩ : syracuseStep 6549497 = 4912123) B4912123
theorem B4366331 : Blo 1939435 4366331 := bstep (se 1 (by rfl) ⟨3274748, by rfl⟩ : syracuseStep 4366331 = 6549497) B6549497
theorem B2910887 : Blo 1939435 2910887 := bstep (se 1 (by rfl) ⟨2183165, by rfl⟩ : syracuseStep 2910887 = 4366331) B4366331
theorem B1940591 : Blo 1939435 1940591 := bstep (se 1 (by rfl) ⟨1455443, by rfl⟩ : syracuseStep 1940591 = 2910887) B2910887
theorem B2910893 : Blo 1939435 2910893 := bbase (se 3 (by rfl) ⟨545792, by rfl⟩ : syracuseStep 2910893 = 1091585) (by norm_num)
theorem B1940595 : Blo 1939435 1940595 := bstep (se 1 (by rfl) ⟨1455446, by rfl⟩ : syracuseStep 1940595 = 2910893) B2910893
theorem B4366349 : Blo 1939435 4366349 := bbase (se 3 (by rfl) ⟨818690, by rfl⟩ : syracuseStep 4366349 = 1637381) (by norm_num)
theorem B2910899 : Blo 1939435 2910899 := bstep (se 1 (by rfl) ⟨2183174, by rfl⟩ : syracuseStep 2910899 = 4366349) B4366349
theorem B1940599 : Blo 1939435 1940599 := bstep (se 1 (by rfl) ⟨1455449, by rfl⟩ : syracuseStep 1940599 = 2910899) B2910899
theorem B2456077 : Blo 1939435 2456077 := bbase (se 3 (by rfl) ⟨460514, by rfl⟩ : syracuseStep 2456077 = 921029) (by norm_num)
theorem B3274769 : Blo 1939435 3274769 := bstep (se 2 (by rfl) ⟨1228038, by rfl⟩ : syracuseStep 3274769 = 2456077) B2456077
theorem B2183179 : Blo 1939435 2183179 := bstep (se 1 (by rfl) ⟨1637384, by rfl⟩ : syracuseStep 2183179 = 3274769) B3274769
theorem B2910905 : Blo 1939435 2910905 := bstep (se 2 (by rfl) ⟨1091589, by rfl⟩ : syracuseStep 2910905 = 2183179) B2183179
theorem B1940603 : Blo 1939435 1940603 := bstep (se 1 (by rfl) ⟨1455452, by rfl⟩ : syracuseStep 1940603 = 2910905) B2910905
theorem B23605013 : Blo 1939435 23605013 := bbase (se 6 (by rfl) ⟨553242, by rfl⟩ : syracuseStep 23605013 = 1106485) (by norm_num)
theorem B15736675 : Blo 1939435 15736675 := bstep (se 1 (by rfl) ⟨11802506, by rfl⟩ : syracuseStep 15736675 = 23605013) B23605013
theorem B20982233 : Blo 1939435 20982233 := bstep (se 2 (by rfl) ⟨7868337, by rfl⟩ : syracuseStep 20982233 = 15736675) B15736675
theorem B13988155 : Blo 1939435 13988155 := bstep (se 1 (by rfl) ⟨10491116, by rfl⟩ : syracuseStep 13988155 = 20982233) B20982233
theorem B18650873 : Blo 1939435 18650873 := bstep (se 2 (by rfl) ⟨6994077, by rfl⟩ : syracuseStep 18650873 = 13988155) B13988155
theorem B12433915 : Blo 1939435 12433915 := bstep (se 1 (by rfl) ⟨9325436, by rfl⟩ : syracuseStep 12433915 = 18650873) B18650873
theorem B16578553 : Blo 1939435 16578553 := bstep (se 2 (by rfl) ⟨6216957, by rfl⟩ : syracuseStep 16578553 = 12433915) B12433915
theorem B22104737 : Blo 1939435 22104737 := bstep (se 2 (by rfl) ⟨8289276, by rfl⟩ : syracuseStep 22104737 = 16578553) B16578553
theorem B14736491 : Blo 1939435 14736491 := bstep (se 1 (by rfl) ⟨11052368, by rfl⟩ : syracuseStep 14736491 = 22104737) B22104737
theorem B9824327 : Blo 1939435 9824327 := bstep (se 1 (by rfl) ⟨7368245, by rfl⟩ : syracuseStep 9824327 = 14736491) B14736491
theorem B6549551 : Blo 1939435 6549551 := bstep (se 1 (by rfl) ⟨4912163, by rfl⟩ : syracuseStep 6549551 = 9824327) B9824327
theorem B4366367 : Blo 1939435 4366367 := bstep (se 1 (by rfl) ⟨3274775, by rfl⟩ : syracuseStep 4366367 = 6549551) B6549551
theorem B2910911 : Blo 1939435 2910911 := bstep (se 1 (by rfl) ⟨2183183, by rfl⟩ : syracuseStep 2910911 = 4366367) B4366367
theorem B1940607 : Blo 1939435 1940607 := bstep (se 1 (by rfl) ⟨1455455, by rfl⟩ : syracuseStep 1940607 = 2910911) B2910911
theorem B2910917 : Blo 1939435 2910917 := bbase (se 4 (by rfl) ⟨272898, by rfl⟩ : syracuseStep 2910917 = 545797) (by norm_num)
theorem B1940611 : Blo 1939435 1940611 := bstep (se 1 (by rfl) ⟨1455458, by rfl⟩ : syracuseStep 1940611 = 2910917) B2910917
theorem B3274789 : Blo 1939435 3274789 := bbase (se 4 (by rfl) ⟨307011, by rfl⟩ : syracuseStep 3274789 = 614023) (by norm_num)
theorem B4366385 : Blo 1939435 4366385 := bstep (se 2 (by rfl) ⟨1637394, by rfl⟩ : syracuseStep 4366385 = 3274789) B3274789
theorem B2910923 : Blo 1939435 2910923 := bstep (se 1 (by rfl) ⟨2183192, by rfl⟩ : syracuseStep 2910923 = 4366385) B4366385
theorem B1940615 : Blo 1939435 1940615 := bstep (se 1 (by rfl) ⟨1455461, by rfl⟩ : syracuseStep 1940615 = 2910923) B2910923
theorem B2183197 : Blo 1939435 2183197 := bbase (se 3 (by rfl) ⟨409349, by rfl⟩ : syracuseStep 2183197 = 818699) (by norm_num)
theorem B2910929 : Blo 1939435 2910929 := bstep (se 2 (by rfl) ⟨1091598, by rfl⟩ : syracuseStep 2910929 = 2183197) B2183197
theorem B1940619 : Blo 1939435 1940619 := bstep (se 1 (by rfl) ⟨1455464, by rfl⟩ : syracuseStep 1940619 = 2910929) B2910929
theorem B6549605 : Blo 1939435 6549605 := bbase (se 4 (by rfl) ⟨614025, by rfl⟩ : syracuseStep 6549605 = 1228051) (by norm_num)
theorem B4366403 : Blo 1939435 4366403 := bstep (se 1 (by rfl) ⟨3274802, by rfl⟩ : syracuseStep 4366403 = 6549605) B6549605
theorem B2910935 : Blo 1939435 2910935 := bstep (se 1 (by rfl) ⟨2183201, by rfl⟩ : syracuseStep 2910935 = 4366403) B4366403
theorem B1940623 : Blo 1939435 1940623 := bstep (se 1 (by rfl) ⟨1455467, by rfl⟩ : syracuseStep 1940623 = 2910935) B2910935
theorem B2910941 : Blo 1939435 2910941 := bbase (se 3 (by rfl) ⟨545801, by rfl⟩ : syracuseStep 2910941 = 1091603) (by norm_num)
theorem B1940627 : Blo 1939435 1940627 := bstep (se 1 (by rfl) ⟨1455470, by rfl⟩ : syracuseStep 1940627 = 2910941) B2910941
theorem B4366421 : Blo 1939435 4366421 := bbase (se 8 (by rfl) ⟨25584, by rfl⟩ : syracuseStep 4366421 = 51169) (by norm_num)
theorem B2910947 : Blo 1939435 2910947 := bstep (se 1 (by rfl) ⟨2183210, by rfl⟩ : syracuseStep 2910947 = 4366421) B4366421
theorem B1940631 : Blo 1939435 1940631 := bstep (se 1 (by rfl) ⟨1455473, by rfl⟩ : syracuseStep 1940631 = 2910947) B2910947
theorem B6994181 : Blo 1939435 6994181 := bbase (se 4 (by rfl) ⟨655704, by rfl⟩ : syracuseStep 6994181 = 1311409) (by norm_num)
theorem B4662787 : Blo 1939435 4662787 := bstep (se 1 (by rfl) ⟨3497090, by rfl⟩ : syracuseStep 4662787 = 6994181) B6994181
theorem B6217049 : Blo 1939435 6217049 := bstep (se 2 (by rfl) ⟨2331393, by rfl⟩ : syracuseStep 6217049 = 4662787) B4662787
theorem B4144699 : Blo 1939435 4144699 := bstep (se 1 (by rfl) ⟨3108524, by rfl⟩ : syracuseStep 4144699 = 6217049) B6217049
theorem B5526265 : Blo 1939435 5526265 := bstep (se 2 (by rfl) ⟨2072349, by rfl⟩ : syracuseStep 5526265 = 4144699) B4144699
theorem B7368353 : Blo 1939435 7368353 := bstep (se 2 (by rfl) ⟨2763132, by rfl⟩ : syracuseStep 7368353 = 5526265) B5526265
theorem B4912235 : Blo 1939435 4912235 := bstep (se 1 (by rfl) ⟨3684176, by rfl⟩ : syracuseStep 4912235 = 7368353) B7368353
theorem B3274823 : Blo 1939435 3274823 := bstep (se 1 (by rfl) ⟨2456117, by rfl⟩ : syracuseStep 3274823 = 4912235) B4912235
theorem B2183215 : Blo 1939435 2183215 := bstep (se 1 (by rfl) ⟨1637411, by rfl⟩ : syracuseStep 2183215 = 3274823) B3274823
theorem B2910953 : Blo 1939435 2910953 := bstep (se 2 (by rfl) ⟨1091607, by rfl⟩ : syracuseStep 2910953 = 2183215) B2183215
theorem B1940635 : Blo 1939435 1940635 := bstep (se 1 (by rfl) ⟨1455476, by rfl⟩ : syracuseStep 1940635 = 2910953) B2910953
theorem B1967117 : Blo 1939435 1967117 := bbase (se 3 (by rfl) ⟨368834, by rfl⟩ : syracuseStep 1967117 = 737669) (by norm_num)
theorem B5245645 : Blo 1939435 5245645 := bstep (se 3 (by rfl) ⟨983558, by rfl⟩ : syracuseStep 5245645 = 1967117) B1967117
theorem B6994193 : Blo 1939435 6994193 := bstep (se 2 (by rfl) ⟨2622822, by rfl⟩ : syracuseStep 6994193 = 5245645) B5245645
theorem B18651181 : Blo 1939435 18651181 := bstep (se 3 (by rfl) ⟨3497096, by rfl⟩ : syracuseStep 18651181 = 6994193) B6994193
theorem B24868241 : Blo 1939435 24868241 := bstep (se 2 (by rfl) ⟨9325590, by rfl⟩ : syracuseStep 24868241 = 18651181) B18651181
theorem B16578827 : Blo 1939435 16578827 := bstep (se 1 (by rfl) ⟨12434120, by rfl⟩ : syracuseStep 16578827 = 24868241) B24868241
theorem B11052551 : Blo 1939435 11052551 := bstep (se 1 (by rfl) ⟨8289413, by rfl⟩ : syracuseStep 11052551 = 16578827) B16578827
theorem B7368367 : Blo 1939435 7368367 := bstep (se 1 (by rfl) ⟨5526275, by rfl⟩ : syracuseStep 7368367 = 11052551) B11052551
theorem B9824489 : Blo 1939435 9824489 := bstep (se 2 (by rfl) ⟨3684183, by rfl⟩ : syracuseStep 9824489 = 7368367) B7368367
theorem B6549659 : Blo 1939435 6549659 := bstep (se 1 (by rfl) ⟨4912244, by rfl⟩ : syracuseStep 6549659 = 9824489) B9824489
theorem B4366439 : Blo 1939435 4366439 := bstep (se 1 (by rfl) ⟨3274829, by rfl⟩ : syracuseStep 4366439 = 6549659) B6549659
theorem B2910959 : Blo 1939435 2910959 := bstep (se 1 (by rfl) ⟨2183219, by rfl⟩ : syracuseStep 2910959 = 4366439) B4366439
theorem B1940639 : Blo 1939435 1940639 := bstep (se 1 (by rfl) ⟨1455479, by rfl⟩ : syracuseStep 1940639 = 2910959) B2910959
theorem B2910965 : Blo 1939435 2910965 := bbase (se 5 (by rfl) ⟨136451, by rfl⟩ : syracuseStep 2910965 = 272903) (by norm_num)
theorem B1940643 : Blo 1939435 1940643 := bstep (se 1 (by rfl) ⟨1455482, by rfl⟩ : syracuseStep 1940643 = 2910965) B2910965
theorem B2100637 : Blo 1939435 2100637 := bbase (se 3 (by rfl) ⟨393869, by rfl⟩ : syracuseStep 2100637 = 787739) (by norm_num)
theorem B2800849 : Blo 1939435 2800849 := bstep (se 2 (by rfl) ⟨1050318, by rfl⟩ : syracuseStep 2800849 = 2100637) B2100637
theorem B3734465 : Blo 1939435 3734465 := bstep (se 2 (by rfl) ⟨1400424, by rfl⟩ : syracuseStep 3734465 = 2800849) B2800849
theorem B9958573 : Blo 1939435 9958573 := bstep (se 3 (by rfl) ⟨1867232, by rfl⟩ : syracuseStep 9958573 = 3734465) B3734465
theorem B13278097 : Blo 1939435 13278097 := bstep (se 2 (by rfl) ⟨4979286, by rfl⟩ : syracuseStep 13278097 = 9958573) B9958573
theorem B70816517 : Blo 1939435 70816517 := bstep (se 4 (by rfl) ⟨6639048, by rfl⟩ : syracuseStep 70816517 = 13278097) B13278097
theorem B47211011 : Blo 1939435 47211011 := bstep (se 1 (by rfl) ⟨35408258, by rfl⟩ : syracuseStep 47211011 = 70816517) B70816517
theorem B31474007 : Blo 1939435 31474007 := bstep (se 1 (by rfl) ⟨23605505, by rfl⟩ : syracuseStep 31474007 = 47211011) B47211011
theorem B20982671 : Blo 1939435 20982671 := bstep (se 1 (by rfl) ⟨15737003, by rfl⟩ : syracuseStep 20982671 = 31474007) B31474007
theorem B13988447 : Blo 1939435 13988447 := bstep (se 1 (by rfl) ⟨10491335, by rfl⟩ : syracuseStep 13988447 = 20982671) B20982671
theorem B9325631 : Blo 1939435 9325631 := bstep (se 1 (by rfl) ⟨6994223, by rfl⟩ : syracuseStep 9325631 = 13988447) B13988447
theorem B6217087 : Blo 1939435 6217087 := bstep (se 1 (by rfl) ⟨4662815, by rfl⟩ : syracuseStep 6217087 = 9325631) B9325631
theorem B8289449 : Blo 1939435 8289449 := bstep (se 2 (by rfl) ⟨3108543, by rfl⟩ : syracuseStep 8289449 = 6217087) B6217087
theorem B5526299 : Blo 1939435 5526299 := bstep (se 1 (by rfl) ⟨4144724, by rfl⟩ : syracuseStep 5526299 = 8289449) B8289449
theorem B3684199 : Blo 1939435 3684199 := bstep (se 1 (by rfl) ⟨2763149, by rfl⟩ : syracuseStep 3684199 = 5526299) B5526299
theorem B4912265 : Blo 1939435 4912265 := bstep (se 2 (by rfl) ⟨1842099, by rfl⟩ : syracuseStep 4912265 = 3684199) B3684199
theorem B3274843 : Blo 1939435 3274843 := bstep (se 1 (by rfl) ⟨2456132, by rfl⟩ : syracuseStep 3274843 = 4912265) B4912265
theorem B4366457 : Blo 1939435 4366457 := bstep (se 2 (by rfl) ⟨1637421, by rfl⟩ : syracuseStep 4366457 = 3274843) B3274843
theorem B2910971 : Blo 1939435 2910971 := bstep (se 1 (by rfl) ⟨2183228, by rfl⟩ : syracuseStep 2910971 = 4366457) B4366457
theorem B1940647 : Blo 1939435 1940647 := bstep (se 1 (by rfl) ⟨1455485, by rfl⟩ : syracuseStep 1940647 = 2910971) B2910971
theorem B2183233 : Blo 1939435 2183233 := bbase (se 2 (by rfl) ⟨818712, by rfl⟩ : syracuseStep 2183233 = 1637425) (by norm_num)
theorem B2910977 : Blo 1939435 2910977 := bstep (se 2 (by rfl) ⟨1091616, by rfl⟩ : syracuseStep 2910977 = 2183233) B2183233
theorem B1940651 : Blo 1939435 1940651 := bstep (se 1 (by rfl) ⟨1455488, by rfl⟩ : syracuseStep 1940651 = 2910977) B2910977
theorem B4912285 : Blo 1939435 4912285 := bbase (se 3 (by rfl) ⟨921053, by rfl⟩ : syracuseStep 4912285 = 1842107) (by norm_num)
theorem B6549713 : Blo 1939435 6549713 := bstep (se 2 (by rfl) ⟨2456142, by rfl⟩ : syracuseStep 6549713 = 4912285) B4912285
theorem B4366475 : Blo 1939435 4366475 := bstep (se 1 (by rfl) ⟨3274856, by rfl⟩ : syracuseStep 4366475 = 6549713) B6549713
theorem B2910983 : Blo 1939435 2910983 := bstep (se 1 (by rfl) ⟨2183237, by rfl⟩ : syracuseStep 2910983 = 4366475) B4366475
theorem B1940655 : Blo 1939435 1940655 := bstep (se 1 (by rfl) ⟨1455491, by rfl⟩ : syracuseStep 1940655 = 2910983) B2910983
theorem B2910989 : Blo 1939435 2910989 := bbase (se 3 (by rfl) ⟨545810, by rfl⟩ : syracuseStep 2910989 = 1091621) (by norm_num)
theorem B1940659 : Blo 1939435 1940659 := bstep (se 1 (by rfl) ⟨1455494, by rfl⟩ : syracuseStep 1940659 = 2910989) B2910989
theorem B4366493 : Blo 1939435 4366493 := bbase (se 3 (by rfl) ⟨818717, by rfl⟩ : syracuseStep 4366493 = 1637435) (by norm_num)
theorem B2910995 : Blo 1939435 2910995 := bstep (se 1 (by rfl) ⟨2183246, by rfl⟩ : syracuseStep 2910995 = 4366493) B4366493
theorem B1940663 : Blo 1939435 1940663 := bstep (se 1 (by rfl) ⟨1455497, by rfl⟩ : syracuseStep 1940663 = 2910995) B2910995
theorem B3274877 : Blo 1939435 3274877 := bbase (se 3 (by rfl) ⟨614039, by rfl⟩ : syracuseStep 3274877 = 1228079) (by norm_num)
theorem B2183251 : Blo 1939435 2183251 := bstep (se 1 (by rfl) ⟨1637438, by rfl⟩ : syracuseStep 2183251 = 3274877) B3274877
theorem B2911001 : Blo 1939435 2911001 := bstep (se 2 (by rfl) ⟨1091625, by rfl⟩ : syracuseStep 2911001 = 2183251) B2183251
theorem B1940667 : Blo 1939435 1940667 := bstep (se 1 (by rfl) ⟨1455500, by rfl⟩ : syracuseStep 1940667 = 2911001) B2911001
theorem B6994309 : Blo 1939435 6994309 := bbase (se 4 (by rfl) ⟨655716, by rfl⟩ : syracuseStep 6994309 = 1311433) (by norm_num)
theorem B9325745 : Blo 1939435 9325745 := bstep (se 2 (by rfl) ⟨3497154, by rfl⟩ : syracuseStep 9325745 = 6994309) B6994309
theorem B6217163 : Blo 1939435 6217163 := bstep (se 1 (by rfl) ⟨4662872, by rfl⟩ : syracuseStep 6217163 = 9325745) B9325745
theorem B4144775 : Blo 1939435 4144775 := bstep (se 1 (by rfl) ⟨3108581, by rfl⟩ : syracuseStep 4144775 = 6217163) B6217163
theorem B11052733 : Blo 1939435 11052733 := bstep (se 3 (by rfl) ⟨2072387, by rfl⟩ : syracuseStep 11052733 = 4144775) B4144775
theorem B14736977 : Blo 1939435 14736977 := bstep (se 2 (by rfl) ⟨5526366, by rfl⟩ : syracuseStep 14736977 = 11052733) B11052733
theorem B9824651 : Blo 1939435 9824651 := bstep (se 1 (by rfl) ⟨7368488, by rfl⟩ : syracuseStep 9824651 = 14736977) B14736977
theorem B6549767 : Blo 1939435 6549767 := bstep (se 1 (by rfl) ⟨4912325, by rfl⟩ : syracuseStep 6549767 = 9824651) B9824651
theorem B4366511 : Blo 1939435 4366511 := bstep (se 1 (by rfl) ⟨3274883, by rfl⟩ : syracuseStep 4366511 = 6549767) B6549767
theorem B2911007 : Blo 1939435 2911007 := bstep (se 1 (by rfl) ⟨2183255, by rfl⟩ : syracuseStep 2911007 = 4366511) B4366511
theorem B1940671 : Blo 1939435 1940671 := bstep (se 1 (by rfl) ⟨1455503, by rfl⟩ : syracuseStep 1940671 = 2911007) B2911007
theorem B2911013 : Blo 1939435 2911013 := bbase (se 4 (by rfl) ⟨272907, by rfl⟩ : syracuseStep 2911013 = 545815) (by norm_num)
theorem B1940675 : Blo 1939435 1940675 := bstep (se 1 (by rfl) ⟨1455506, by rfl⟩ : syracuseStep 1940675 = 2911013) B2911013
theorem B2456173 : Blo 1939435 2456173 := bbase (se 3 (by rfl) ⟨460532, by rfl⟩ : syracuseStep 2456173 = 921065) (by norm_num)
theorem B3274897 : Blo 1939435 3274897 := bstep (se 2 (by rfl) ⟨1228086, by rfl⟩ : syracuseStep 3274897 = 2456173) B2456173
theorem B4366529 : Blo 1939435 4366529 := bstep (se 2 (by rfl) ⟨1637448, by rfl⟩ : syracuseStep 4366529 = 3274897) B3274897
theorem B2911019 : Blo 1939435 2911019 := bstep (se 1 (by rfl) ⟨2183264, by rfl⟩ : syracuseStep 2911019 = 4366529) B4366529
theorem B1940679 : Blo 1939435 1940679 := bstep (se 1 (by rfl) ⟨1455509, by rfl⟩ : syracuseStep 1940679 = 2911019) B2911019
theorem B2183269 : Blo 1939435 2183269 := bbase (se 4 (by rfl) ⟨204681, by rfl⟩ : syracuseStep 2183269 = 409363) (by norm_num)
theorem B2911025 : Blo 1939435 2911025 := bstep (se 2 (by rfl) ⟨1091634, by rfl⟩ : syracuseStep 2911025 = 2183269) B2183269
theorem B1940683 : Blo 1939435 1940683 := bstep (se 1 (by rfl) ⟨1455512, by rfl⟩ : syracuseStep 1940683 = 2911025) B2911025
theorem B2072405 : Blo 1939435 2072405 := bbase (se 9 (by rfl) ⟨6071, by rfl⟩ : syracuseStep 2072405 = 12143) (by norm_num)
theorem B5526413 : Blo 1939435 5526413 := bstep (se 3 (by rfl) ⟨1036202, by rfl⟩ : syracuseStep 5526413 = 2072405) B2072405
theorem B3684275 : Blo 1939435 3684275 := bstep (se 1 (by rfl) ⟨2763206, by rfl⟩ : syracuseStep 3684275 = 5526413) B5526413
theorem B2456183 : Blo 1939435 2456183 := bstep (se 1 (by rfl) ⟨1842137, by rfl⟩ : syracuseStep 2456183 = 3684275) B3684275
theorem B6549821 : Blo 1939435 6549821 := bstep (se 3 (by rfl) ⟨1228091, by rfl⟩ : syracuseStep 6549821 = 2456183) B2456183
theorem B4366547 : Blo 1939435 4366547 := bstep (se 1 (by rfl) ⟨3274910, by rfl⟩ : syracuseStep 4366547 = 6549821) B6549821
theorem B2911031 : Blo 1939435 2911031 := bstep (se 1 (by rfl) ⟨2183273, by rfl⟩ : syracuseStep 2911031 = 4366547) B4366547
theorem B1940687 : Blo 1939435 1940687 := bstep (se 1 (by rfl) ⟨1455515, by rfl⟩ : syracuseStep 1940687 = 2911031) B2911031
theorem B2911037 : Blo 1939435 2911037 := bbase (se 3 (by rfl) ⟨545819, by rfl⟩ : syracuseStep 2911037 = 1091639) (by norm_num)
theorem B1940691 : Blo 1939435 1940691 := bstep (se 1 (by rfl) ⟨1455518, by rfl⟩ : syracuseStep 1940691 = 2911037) B2911037
theorem B4366565 : Blo 1939435 4366565 := bbase (se 4 (by rfl) ⟨409365, by rfl⟩ : syracuseStep 4366565 = 818731) (by norm_num)
theorem B2911043 : Blo 1939435 2911043 := bstep (se 1 (by rfl) ⟨2183282, by rfl⟩ : syracuseStep 2911043 = 4366565) B4366565
theorem B1940695 : Blo 1939435 1940695 := bstep (se 1 (by rfl) ⟨1455521, by rfl⟩ : syracuseStep 1940695 = 2911043) B2911043
theorem B4912397 : Blo 1939435 4912397 := bbase (se 3 (by rfl) ⟨921074, by rfl⟩ : syracuseStep 4912397 = 1842149) (by norm_num)
theorem B3274931 : Blo 1939435 3274931 := bstep (se 1 (by rfl) ⟨2456198, by rfl⟩ : syracuseStep 3274931 = 4912397) B4912397
theorem B2183287 : Blo 1939435 2183287 := bstep (se 1 (by rfl) ⟨1637465, by rfl⟩ : syracuseStep 2183287 = 3274931) B3274931
theorem B2911049 : Blo 1939435 2911049 := bstep (se 2 (by rfl) ⟨1091643, by rfl⟩ : syracuseStep 2911049 = 2183287) B2183287
theorem B1940699 : Blo 1939435 1940699 := bstep (se 1 (by rfl) ⟨1455524, by rfl⟩ : syracuseStep 1940699 = 2911049) B2911049
theorem B2763229 : Blo 1939435 2763229 := bbase (se 3 (by rfl) ⟨518105, by rfl⟩ : syracuseStep 2763229 = 1036211) (by norm_num)
theorem B3684305 : Blo 1939435 3684305 := bstep (se 2 (by rfl) ⟨1381614, by rfl⟩ : syracuseStep 3684305 = 2763229) B2763229
theorem B9824813 : Blo 1939435 9824813 := bstep (se 3 (by rfl) ⟨1842152, by rfl⟩ : syracuseStep 9824813 = 3684305) B3684305
theorem B6549875 : Blo 1939435 6549875 := bstep (se 1 (by rfl) ⟨4912406, by rfl⟩ : syracuseStep 6549875 = 9824813) B9824813
theorem B4366583 : Blo 1939435 4366583 := bstep (se 1 (by rfl) ⟨3274937, by rfl⟩ : syracuseStep 4366583 = 6549875) B6549875
theorem B2911055 : Blo 1939435 2911055 := bstep (se 1 (by rfl) ⟨2183291, by rfl⟩ : syracuseStep 2911055 = 4366583) B4366583
theorem B1940703 : Blo 1939435 1940703 := bstep (se 1 (by rfl) ⟨1455527, by rfl⟩ : syracuseStep 1940703 = 2911055) B2911055
theorem B2911061 : Blo 1939435 2911061 := bbase (se 9 (by rfl) ⟨8528, by rfl⟩ : syracuseStep 2911061 = 17057) (by norm_num)
theorem B1940707 : Blo 1939435 1940707 := bstep (se 1 (by rfl) ⟨1455530, by rfl⟩ : syracuseStep 1940707 = 2911061) B2911061
theorem B4144861 : Blo 1939435 4144861 := bbase (se 3 (by rfl) ⟨777161, by rfl⟩ : syracuseStep 4144861 = 1554323) (by norm_num)
theorem B5526481 : Blo 1939435 5526481 := bstep (se 2 (by rfl) ⟨2072430, by rfl⟩ : syracuseStep 5526481 = 4144861) B4144861
theorem B7368641 : Blo 1939435 7368641 := bstep (se 2 (by rfl) ⟨2763240, by rfl⟩ : syracuseStep 7368641 = 5526481) B5526481
theorem B4912427 : Blo 1939435 4912427 := bstep (se 1 (by rfl) ⟨3684320, by rfl⟩ : syracuseStep 4912427 = 7368641) B7368641
theorem B3274951 : Blo 1939435 3274951 := bstep (se 1 (by rfl) ⟨2456213, by rfl⟩ : syracuseStep 3274951 = 4912427) B4912427
theorem B4366601 : Blo 1939435 4366601 := bstep (se 2 (by rfl) ⟨1637475, by rfl⟩ : syracuseStep 4366601 = 3274951) B3274951
theorem B2911067 : Blo 1939435 2911067 := bstep (se 1 (by rfl) ⟨2183300, by rfl⟩ : syracuseStep 2911067 = 4366601) B4366601
theorem B1940711 : Blo 1939435 1940711 := bstep (se 1 (by rfl) ⟨1455533, by rfl⟩ : syracuseStep 1940711 = 2911067) B2911067
theorem B2183305 : Blo 1939435 2183305 := bbase (se 2 (by rfl) ⟨818739, by rfl⟩ : syracuseStep 2183305 = 1637479) (by norm_num)
theorem B2911073 : Blo 1939435 2911073 := bstep (se 2 (by rfl) ⟨1091652, by rfl⟩ : syracuseStep 2911073 = 2183305) B2183305
theorem B1940715 : Blo 1939435 1940715 := bstep (se 1 (by rfl) ⟨1455536, by rfl⟩ : syracuseStep 1940715 = 2911073) B2911073
theorem B20983445 : Blo 1939435 20983445 := bbase (se 6 (by rfl) ⟨491799, by rfl⟩ : syracuseStep 20983445 = 983599) (by norm_num)
theorem B13988963 : Blo 1939435 13988963 := bstep (se 1 (by rfl) ⟨10491722, by rfl⟩ : syracuseStep 13988963 = 20983445) B20983445
theorem B37303901 : Blo 1939435 37303901 := bstep (se 3 (by rfl) ⟨6994481, by rfl⟩ : syracuseStep 37303901 = 13988963) B13988963
theorem B24869267 : Blo 1939435 24869267 := bstep (se 1 (by rfl) ⟨18651950, by rfl⟩ : syracuseStep 24869267 = 37303901) B37303901
theorem B16579511 : Blo 1939435 16579511 := bstep (se 1 (by rfl) ⟨12434633, by rfl⟩ : syracuseStep 16579511 = 24869267) B24869267
theorem B11053007 : Blo 1939435 11053007 := bstep (se 1 (by rfl) ⟨8289755, by rfl⟩ : syracuseStep 11053007 = 16579511) B16579511
theorem B7368671 : Blo 1939435 7368671 := bstep (se 1 (by rfl) ⟨5526503, by rfl⟩ : syracuseStep 7368671 = 11053007) B11053007
theorem B4912447 : Blo 1939435 4912447 := bstep (se 1 (by rfl) ⟨3684335, by rfl⟩ : syracuseStep 4912447 = 7368671) B7368671
theorem B6549929 : Blo 1939435 6549929 := bstep (se 2 (by rfl) ⟨2456223, by rfl⟩ : syracuseStep 6549929 = 4912447) B4912447
theorem B4366619 : Blo 1939435 4366619 := bstep (se 1 (by rfl) ⟨3274964, by rfl⟩ : syracuseStep 4366619 = 6549929) B6549929
theorem B2911079 : Blo 1939435 2911079 := bstep (se 1 (by rfl) ⟨2183309, by rfl⟩ : syracuseStep 2911079 = 4366619) B4366619
theorem B1940719 : Blo 1939435 1940719 := bstep (se 1 (by rfl) ⟨1455539, by rfl⟩ : syracuseStep 1940719 = 2911079) B2911079
theorem B2911085 : Blo 1939435 2911085 := bbase (se 3 (by rfl) ⟨545828, by rfl⟩ : syracuseStep 2911085 = 1091657) (by norm_num)
theorem B1940723 : Blo 1939435 1940723 := bstep (se 1 (by rfl) ⟨1455542, by rfl⟩ : syracuseStep 1940723 = 2911085) B2911085
theorem B4366637 : Blo 1939435 4366637 := bbase (se 3 (by rfl) ⟨818744, by rfl⟩ : syracuseStep 4366637 = 1637489) (by norm_num)
theorem B2911091 : Blo 1939435 2911091 := bstep (se 1 (by rfl) ⟨2183318, by rfl⟩ : syracuseStep 2911091 = 4366637) B4366637
theorem B1940727 : Blo 1939435 1940727 := bstep (se 1 (by rfl) ⟨1455545, by rfl⟩ : syracuseStep 1940727 = 2911091) B2911091
theorem B2331509 : Blo 1939435 2331509 := bbase (se 5 (by rfl) ⟨109289, by rfl⟩ : syracuseStep 2331509 = 218579) (by norm_num)
theorem B6217357 : Blo 1939435 6217357 := bstep (se 3 (by rfl) ⟨1165754, by rfl⟩ : syracuseStep 6217357 = 2331509) B2331509
theorem B8289809 : Blo 1939435 8289809 := bstep (se 2 (by rfl) ⟨3108678, by rfl⟩ : syracuseStep 8289809 = 6217357) B6217357
theorem B5526539 : Blo 1939435 5526539 := bstep (se 1 (by rfl) ⟨4144904, by rfl⟩ : syracuseStep 5526539 = 8289809) B8289809
theorem B3684359 : Blo 1939435 3684359 := bstep (se 1 (by rfl) ⟨2763269, by rfl⟩ : syracuseStep 3684359 = 5526539) B5526539
theorem B2456239 : Blo 1939435 2456239 := bstep (se 1 (by rfl) ⟨1842179, by rfl⟩ : syracuseStep 2456239 = 3684359) B3684359
theorem B3274985 : Blo 1939435 3274985 := bstep (se 2 (by rfl) ⟨1228119, by rfl⟩ : syracuseStep 3274985 = 2456239) B2456239
theorem B2183323 : Blo 1939435 2183323 := bstep (se 1 (by rfl) ⟨1637492, by rfl⟩ : syracuseStep 2183323 = 3274985) B3274985
theorem B2911097 : Blo 1939435 2911097 := bstep (se 2 (by rfl) ⟨1091661, by rfl⟩ : syracuseStep 2911097 = 2183323) B2183323
theorem B1940731 : Blo 1939435 1940731 := bstep (se 1 (by rfl) ⟨1455548, by rfl⟩ : syracuseStep 1940731 = 2911097) B2911097
theorem B18906581 : Blo 1939435 18906581 := bbase (se 7 (by rfl) ⟨221561, by rfl⟩ : syracuseStep 18906581 = 443123) (by norm_num)
theorem B50417549 : Blo 1939435 50417549 := bstep (se 3 (by rfl) ⟨9453290, by rfl⟩ : syracuseStep 50417549 = 18906581) B18906581
theorem B33611699 : Blo 1939435 33611699 := bstep (se 1 (by rfl) ⟨25208774, by rfl⟩ : syracuseStep 33611699 = 50417549) B50417549
theorem B89631197 : Blo 1939435 89631197 := bstep (se 3 (by rfl) ⟨16805849, by rfl⟩ : syracuseStep 89631197 = 33611699) B33611699
theorem B59754131 : Blo 1939435 59754131 := bstep (se 1 (by rfl) ⟨44815598, by rfl⟩ : syracuseStep 59754131 = 89631197) B89631197
theorem B39836087 : Blo 1939435 39836087 := bstep (se 1 (by rfl) ⟨29877065, by rfl⟩ : syracuseStep 39836087 = 59754131) B59754131
theorem B26557391 : Blo 1939435 26557391 := bstep (se 1 (by rfl) ⟨19918043, by rfl⟩ : syracuseStep 26557391 = 39836087) B39836087
theorem B17704927 : Blo 1939435 17704927 := bstep (se 1 (by rfl) ⟨13278695, by rfl⟩ : syracuseStep 17704927 = 26557391) B26557391
theorem B23606569 : Blo 1939435 23606569 := bstep (se 2 (by rfl) ⟨8852463, by rfl⟩ : syracuseStep 23606569 = 17704927) B17704927
theorem B31475425 : Blo 1939435 31475425 := bstep (se 2 (by rfl) ⟨11803284, by rfl⟩ : syracuseStep 31475425 = 23606569) B23606569
theorem B41967233 : Blo 1939435 41967233 := bstep (se 2 (by rfl) ⟨15737712, by rfl⟩ : syracuseStep 41967233 = 31475425) B31475425
theorem B27978155 : Blo 1939435 27978155 := bstep (se 1 (by rfl) ⟨20983616, by rfl⟩ : syracuseStep 27978155 = 41967233) B41967233
theorem B18652103 : Blo 1939435 18652103 := bstep (se 1 (by rfl) ⟨13989077, by rfl⟩ : syracuseStep 18652103 = 27978155) B27978155
theorem B12434735 : Blo 1939435 12434735 := bstep (se 1 (by rfl) ⟨9326051, by rfl⟩ : syracuseStep 12434735 = 18652103) B18652103
theorem B33159293 : Blo 1939435 33159293 := bstep (se 3 (by rfl) ⟨6217367, by rfl⟩ : syracuseStep 33159293 = 12434735) B12434735
theorem B22106195 : Blo 1939435 22106195 := bstep (se 1 (by rfl) ⟨16579646, by rfl⟩ : syracuseStep 22106195 = 33159293) B33159293
theorem B14737463 : Blo 1939435 14737463 := bstep (se 1 (by rfl) ⟨11053097, by rfl⟩ : syracuseStep 14737463 = 22106195) B22106195
theorem B9824975 : Blo 1939435 9824975 := bstep (se 1 (by rfl) ⟨7368731, by rfl⟩ : syracuseStep 9824975 = 14737463) B14737463
theorem B6549983 : Blo 1939435 6549983 := bstep (se 1 (by rfl) ⟨4912487, by rfl⟩ : syracuseStep 6549983 = 9824975) B9824975
theorem B4366655 : Blo 1939435 4366655 := bstep (se 1 (by rfl) ⟨3274991, by rfl⟩ : syracuseStep 4366655 = 6549983) B6549983
theorem B2911103 : Blo 1939435 2911103 := bstep (se 1 (by rfl) ⟨2183327, by rfl⟩ : syracuseStep 2911103 = 4366655) B4366655
theorem B1940735 : Blo 1939435 1940735 := bstep (se 1 (by rfl) ⟨1455551, by rfl⟩ : syracuseStep 1940735 = 2911103) B2911103
theorem B2911109 : Blo 1939435 2911109 := bbase (se 4 (by rfl) ⟨272916, by rfl⟩ : syracuseStep 2911109 = 545833) (by norm_num)
theorem B1940739 : Blo 1939435 1940739 := bstep (se 1 (by rfl) ⟨1455554, by rfl⟩ : syracuseStep 1940739 = 2911109) B2911109
theorem B3275005 : Blo 1939435 3275005 := bbase (se 3 (by rfl) ⟨614063, by rfl⟩ : syracuseStep 3275005 = 1228127) (by norm_num)
theorem B4366673 : Blo 1939435 4366673 := bstep (se 2 (by rfl) ⟨1637502, by rfl⟩ : syracuseStep 4366673 = 3275005) B3275005
theorem B2911115 : Blo 1939435 2911115 := bstep (se 1 (by rfl) ⟨2183336, by rfl⟩ : syracuseStep 2911115 = 4366673) B4366673
theorem B1940743 : Blo 1939435 1940743 := bstep (se 1 (by rfl) ⟨1455557, by rfl⟩ : syracuseStep 1940743 = 2911115) B2911115
theorem B2183341 : Blo 1939435 2183341 := bbase (se 3 (by rfl) ⟨409376, by rfl⟩ : syracuseStep 2183341 = 818753) (by norm_num)
theorem B2911121 : Blo 1939435 2911121 := bstep (se 2 (by rfl) ⟨1091670, by rfl⟩ : syracuseStep 2911121 = 2183341) B2183341
theorem B1940747 : Blo 1939435 1940747 := bstep (se 1 (by rfl) ⟨1455560, by rfl⟩ : syracuseStep 1940747 = 2911121) B2911121
theorem B6550037 : Blo 1939435 6550037 := bbase (se 6 (by rfl) ⟨153516, by rfl⟩ : syracuseStep 6550037 = 307033) (by norm_num)
theorem B4366691 : Blo 1939435 4366691 := bstep (se 1 (by rfl) ⟨3275018, by rfl⟩ : syracuseStep 4366691 = 6550037) B6550037
theorem B2911127 : Blo 1939435 2911127 := bstep (se 1 (by rfl) ⟨2183345, by rfl⟩ : syracuseStep 2911127 = 4366691) B4366691
theorem B1940751 : Blo 1939435 1940751 := bstep (se 1 (by rfl) ⟨1455563, by rfl⟩ : syracuseStep 1940751 = 2911127) B2911127
theorem B2911133 : Blo 1939435 2911133 := bbase (se 3 (by rfl) ⟨545837, by rfl⟩ : syracuseStep 2911133 = 1091675) (by norm_num)
theorem B1940755 : Blo 1939435 1940755 := bstep (se 1 (by rfl) ⟨1455566, by rfl⟩ : syracuseStep 1940755 = 2911133) B2911133
theorem B4366709 : Blo 1939435 4366709 := bbase (se 5 (by rfl) ⟨204689, by rfl⟩ : syracuseStep 4366709 = 409379) (by norm_num)
theorem B2911139 : Blo 1939435 2911139 := bstep (se 1 (by rfl) ⟨2183354, by rfl⟩ : syracuseStep 2911139 = 4366709) B4366709
theorem B1940759 : Blo 1939435 1940759 := bstep (se 1 (by rfl) ⟨1455569, by rfl⟩ : syracuseStep 1940759 = 2911139) B2911139
theorem B8852597 : Blo 1939435 8852597 := bbase (se 5 (by rfl) ⟨414965, by rfl⟩ : syracuseStep 8852597 = 829931) (by norm_num)
theorem B5901731 : Blo 1939435 5901731 := bstep (se 1 (by rfl) ⟨4426298, by rfl⟩ : syracuseStep 5901731 = 8852597) B8852597
theorem B3934487 : Blo 1939435 3934487 := bstep (se 1 (by rfl) ⟨2950865, by rfl⟩ : syracuseStep 3934487 = 5901731) B5901731
theorem B2622991 : Blo 1939435 2622991 := bstep (se 1 (by rfl) ⟨1967243, by rfl⟩ : syracuseStep 2622991 = 3934487) B3934487
theorem B3497321 : Blo 1939435 3497321 := bstep (se 2 (by rfl) ⟨1311495, by rfl⟩ : syracuseStep 3497321 = 2622991) B2622991
theorem B2331547 : Blo 1939435 2331547 := bstep (se 1 (by rfl) ⟨1748660, by rfl⟩ : syracuseStep 2331547 = 3497321) B3497321
theorem B12434917 : Blo 1939435 12434917 := bstep (se 4 (by rfl) ⟨1165773, by rfl⟩ : syracuseStep 12434917 = 2331547) B2331547
theorem B16579889 : Blo 1939435 16579889 := bstep (se 2 (by rfl) ⟨6217458, by rfl⟩ : syracuseStep 16579889 = 12434917) B12434917
theorem B11053259 : Blo 1939435 11053259 := bstep (se 1 (by rfl) ⟨8289944, by rfl⟩ : syracuseStep 11053259 = 16579889) B16579889
theorem B7368839 : Blo 1939435 7368839 := bstep (se 1 (by rfl) ⟨5526629, by rfl⟩ : syracuseStep 7368839 = 11053259) B11053259
theorem B4912559 : Blo 1939435 4912559 := bstep (se 1 (by rfl) ⟨3684419, by rfl⟩ : syracuseStep 4912559 = 7368839) B7368839
theorem B3275039 : Blo 1939435 3275039 := bstep (se 1 (by rfl) ⟨2456279, by rfl⟩ : syracuseStep 3275039 = 4912559) B4912559
theorem B2183359 : Blo 1939435 2183359 := bstep (se 1 (by rfl) ⟨1637519, by rfl⟩ : syracuseStep 2183359 = 3275039) B3275039
theorem B2911145 : Blo 1939435 2911145 := bstep (se 2 (by rfl) ⟨1091679, by rfl⟩ : syracuseStep 2911145 = 2183359) B2183359
theorem B1940763 : Blo 1939435 1940763 := bstep (se 1 (by rfl) ⟨1455572, by rfl⟩ : syracuseStep 1940763 = 2911145) B2911145
theorem B7368853 : Blo 1939435 7368853 := bbase (se 6 (by rfl) ⟨172707, by rfl⟩ : syracuseStep 7368853 = 345415) (by norm_num)
theorem B9825137 : Blo 1939435 9825137 := bstep (se 2 (by rfl) ⟨3684426, by rfl⟩ : syracuseStep 9825137 = 7368853) B7368853
theorem B6550091 : Blo 1939435 6550091 := bstep (se 1 (by rfl) ⟨4912568, by rfl⟩ : syracuseStep 6550091 = 9825137) B9825137
theorem B4366727 : Blo 1939435 4366727 := bstep (se 1 (by rfl) ⟨3275045, by rfl⟩ : syracuseStep 4366727 = 6550091) B6550091
theorem B2911151 : Blo 1939435 2911151 := bstep (se 1 (by rfl) ⟨2183363, by rfl⟩ : syracuseStep 2911151 = 4366727) B4366727
theorem B1940767 : Blo 1939435 1940767 := bstep (se 1 (by rfl) ⟨1455575, by rfl⟩ : syracuseStep 1940767 = 2911151) B2911151
theorem B2911157 : Blo 1939435 2911157 := bbase (se 5 (by rfl) ⟨136460, by rfl⟩ : syracuseStep 2911157 = 272921) (by norm_num)
theorem B1940771 : Blo 1939435 1940771 := bstep (se 1 (by rfl) ⟨1455578, by rfl⟩ : syracuseStep 1940771 = 2911157) B2911157
theorem B4912589 : Blo 1939435 4912589 := bbase (se 3 (by rfl) ⟨921110, by rfl⟩ : syracuseStep 4912589 = 1842221) (by norm_num)
theorem B3275059 : Blo 1939435 3275059 := bstep (se 1 (by rfl) ⟨2456294, by rfl⟩ : syracuseStep 3275059 = 4912589) B4912589
theorem B4366745 : Blo 1939435 4366745 := bstep (se 2 (by rfl) ⟨1637529, by rfl⟩ : syracuseStep 4366745 = 3275059) B3275059
theorem B2911163 : Blo 1939435 2911163 := bstep (se 1 (by rfl) ⟨2183372, by rfl⟩ : syracuseStep 2911163 = 4366745) B4366745
theorem B1940775 : Blo 1939435 1940775 := bstep (se 1 (by rfl) ⟨1455581, by rfl⟩ : syracuseStep 1940775 = 2911163) B2911163
theorem B2183377 : Blo 1939435 2183377 := bbase (se 2 (by rfl) ⟨818766, by rfl⟩ : syracuseStep 2183377 = 1637533) (by norm_num)
theorem B2911169 : Blo 1939435 2911169 := bstep (se 2 (by rfl) ⟨1091688, by rfl⟩ : syracuseStep 2911169 = 2183377) B2183377
theorem B1940779 : Blo 1939435 1940779 := bstep (se 1 (by rfl) ⟨1455584, by rfl⟩ : syracuseStep 1940779 = 2911169) B2911169
theorem B3497357 : Blo 1939435 3497357 := bbase (se 3 (by rfl) ⟨655754, by rfl⟩ : syracuseStep 3497357 = 1311509) (by norm_num)
theorem B9326285 : Blo 1939435 9326285 := bstep (se 3 (by rfl) ⟨1748678, by rfl⟩ : syracuseStep 9326285 = 3497357) B3497357
theorem B6217523 : Blo 1939435 6217523 := bstep (se 1 (by rfl) ⟨4663142, by rfl⟩ : syracuseStep 6217523 = 9326285) B9326285
theorem B4145015 : Blo 1939435 4145015 := bstep (se 1 (by rfl) ⟨3108761, by rfl⟩ : syracuseStep 4145015 = 6217523) B6217523
theorem B2763343 : Blo 1939435 2763343 := bstep (se 1 (by rfl) ⟨2072507, by rfl⟩ : syracuseStep 2763343 = 4145015) B4145015
theorem B3684457 : Blo 1939435 3684457 := bstep (se 2 (by rfl) ⟨1381671, by rfl⟩ : syracuseStep 3684457 = 2763343) B2763343
theorem B4912609 : Blo 1939435 4912609 := bstep (se 2 (by rfl) ⟨1842228, by rfl⟩ : syracuseStep 4912609 = 3684457) B3684457
theorem B6550145 : Blo 1939435 6550145 := bstep (se 2 (by rfl) ⟨2456304, by rfl⟩ : syracuseStep 6550145 = 4912609) B4912609
theorem B4366763 : Blo 1939435 4366763 := bstep (se 1 (by rfl) ⟨3275072, by rfl⟩ : syracuseStep 4366763 = 6550145) B6550145
theorem B2911175 : Blo 1939435 2911175 := bstep (se 1 (by rfl) ⟨2183381, by rfl⟩ : syracuseStep 2911175 = 4366763) B4366763
theorem B1940783 : Blo 1939435 1940783 := bstep (se 1 (by rfl) ⟨1455587, by rfl⟩ : syracuseStep 1940783 = 2911175) B2911175
theorem B2911181 : Blo 1939435 2911181 := bbase (se 3 (by rfl) ⟨545846, by rfl⟩ : syracuseStep 2911181 = 1091693) (by norm_num)
theorem B1940787 : Blo 1939435 1940787 := bstep (se 1 (by rfl) ⟨1455590, by rfl⟩ : syracuseStep 1940787 = 2911181) B2911181
theorem B4366781 : Blo 1939435 4366781 := bbase (se 3 (by rfl) ⟨818771, by rfl⟩ : syracuseStep 4366781 = 1637543) (by norm_num)
theorem B2911187 : Blo 1939435 2911187 := bstep (se 1 (by rfl) ⟨2183390, by rfl⟩ : syracuseStep 2911187 = 4366781) B4366781
theorem B1940791 : Blo 1939435 1940791 := bstep (se 1 (by rfl) ⟨1455593, by rfl⟩ : syracuseStep 1940791 = 2911187) B2911187
theorem B3275093 : Blo 1939435 3275093 := bbase (se 10 (by rfl) ⟨4797, by rfl⟩ : syracuseStep 3275093 = 9595) (by norm_num)
theorem B2183395 : Blo 1939435 2183395 := bstep (se 1 (by rfl) ⟨1637546, by rfl⟩ : syracuseStep 2183395 = 3275093) B3275093
theorem B2911193 : Blo 1939435 2911193 := bstep (se 2 (by rfl) ⟨1091697, by rfl⟩ : syracuseStep 2911193 = 2183395) B2183395
theorem B1940795 : Blo 1939435 1940795 := bstep (se 1 (by rfl) ⟨1455596, by rfl⟩ : syracuseStep 1940795 = 2911193) B2911193
theorem B6217573 : Blo 1939435 6217573 := bbase (se 4 (by rfl) ⟨582897, by rfl⟩ : syracuseStep 6217573 = 1165795) (by norm_num)
theorem B8290097 : Blo 1939435 8290097 := bstep (se 2 (by rfl) ⟨3108786, by rfl⟩ : syracuseStep 8290097 = 6217573) B6217573
theorem B5526731 : Blo 1939435 5526731 := bstep (se 1 (by rfl) ⟨4145048, by rfl⟩ : syracuseStep 5526731 = 8290097) B8290097
theorem B14737949 : Blo 1939435 14737949 := bstep (se 3 (by rfl) ⟨2763365, by rfl⟩ : syracuseStep 14737949 = 5526731) B5526731
theorem B9825299 : Blo 1939435 9825299 := bstep (se 1 (by rfl) ⟨7368974, by rfl⟩ : syracuseStep 9825299 = 14737949) B14737949
theorem B6550199 : Blo 1939435 6550199 := bstep (se 1 (by rfl) ⟨4912649, by rfl⟩ : syracuseStep 6550199 = 9825299) B9825299
theorem B4366799 : Blo 1939435 4366799 := bstep (se 1 (by rfl) ⟨3275099, by rfl⟩ : syracuseStep 4366799 = 6550199) B6550199
theorem B2911199 : Blo 1939435 2911199 := bstep (se 1 (by rfl) ⟨2183399, by rfl⟩ : syracuseStep 2911199 = 4366799) B4366799
theorem B1940799 : Blo 1939435 1940799 := bstep (se 1 (by rfl) ⟨1455599, by rfl⟩ : syracuseStep 1940799 = 2911199) B2911199
theorem B2911205 : Blo 1939435 2911205 := bbase (se 4 (by rfl) ⟨272925, by rfl⟩ : syracuseStep 2911205 = 545851) (by norm_num)
theorem B1940803 : Blo 1939435 1940803 := bstep (se 1 (by rfl) ⟨1455602, by rfl⟩ : syracuseStep 1940803 = 2911205) B2911205
theorem B8290133 : Blo 1939435 8290133 := bbase (se 9 (by rfl) ⟨24287, by rfl⟩ : syracuseStep 8290133 = 48575) (by norm_num)
theorem B5526755 : Blo 1939435 5526755 := bstep (se 1 (by rfl) ⟨4145066, by rfl⟩ : syracuseStep 5526755 = 8290133) B8290133
theorem B3684503 : Blo 1939435 3684503 := bstep (se 1 (by rfl) ⟨2763377, by rfl⟩ : syracuseStep 3684503 = 5526755) B5526755
theorem B2456335 : Blo 1939435 2456335 := bstep (se 1 (by rfl) ⟨1842251, by rfl⟩ : syracuseStep 2456335 = 3684503) B3684503
theorem B3275113 : Blo 1939435 3275113 := bstep (se 2 (by rfl) ⟨1228167, by rfl⟩ : syracuseStep 3275113 = 2456335) B2456335
theorem B4366817 : Blo 1939435 4366817 := bstep (se 2 (by rfl) ⟨1637556, by rfl⟩ : syracuseStep 4366817 = 3275113) B3275113
theorem B2911211 : Blo 1939435 2911211 := bstep (se 1 (by rfl) ⟨2183408, by rfl⟩ : syracuseStep 2911211 = 4366817) B4366817
theorem B1940807 : Blo 1939435 1940807 := bstep (se 1 (by rfl) ⟨1455605, by rfl⟩ : syracuseStep 1940807 = 2911211) B2911211
theorem B2183413 : Blo 1939435 2183413 := bbase (se 5 (by rfl) ⟨102347, by rfl⟩ : syracuseStep 2183413 = 204695) (by norm_num)
theorem B2911217 : Blo 1939435 2911217 := bstep (se 2 (by rfl) ⟨1091706, by rfl⟩ : syracuseStep 2911217 = 2183413) B2183413
theorem B1940811 : Blo 1939435 1940811 := bstep (se 1 (by rfl) ⟨1455608, by rfl⟩ : syracuseStep 1940811 = 2911217) B2911217
theorem B2456345 : Blo 1939435 2456345 := bbase (se 2 (by rfl) ⟨921129, by rfl⟩ : syracuseStep 2456345 = 1842259) (by norm_num)
theorem B6550253 : Blo 1939435 6550253 := bstep (se 3 (by rfl) ⟨1228172, by rfl⟩ : syracuseStep 6550253 = 2456345) B2456345
theorem B4366835 : Blo 1939435 4366835 := bstep (se 1 (by rfl) ⟨3275126, by rfl⟩ : syracuseStep 4366835 = 6550253) B6550253
theorem B2911223 : Blo 1939435 2911223 := bstep (se 1 (by rfl) ⟨2183417, by rfl⟩ : syracuseStep 2911223 = 4366835) B4366835
theorem B1940815 : Blo 1939435 1940815 := bstep (se 1 (by rfl) ⟨1455611, by rfl⟩ : syracuseStep 1940815 = 2911223) B2911223
theorem B2911229 : Blo 1939435 2911229 := bbase (se 3 (by rfl) ⟨545855, by rfl⟩ : syracuseStep 2911229 = 1091711) (by norm_num)
theorem B1940819 : Blo 1939435 1940819 := bstep (se 1 (by rfl) ⟨1455614, by rfl⟩ : syracuseStep 1940819 = 2911229) B2911229
theorem B4366853 : Blo 1939435 4366853 := bbase (se 4 (by rfl) ⟨409392, by rfl⟩ : syracuseStep 4366853 = 818785) (by norm_num)
theorem B2911235 : Blo 1939435 2911235 := bstep (se 1 (by rfl) ⟨2183426, by rfl⟩ : syracuseStep 2911235 = 4366853) B4366853
theorem B1940823 : Blo 1939435 1940823 := bstep (se 1 (by rfl) ⟨1455617, by rfl⟩ : syracuseStep 1940823 = 2911235) B2911235
theorem B3684541 : Blo 1939435 3684541 := bbase (se 3 (by rfl) ⟨690851, by rfl⟩ : syracuseStep 3684541 = 1381703) (by norm_num)
theorem B4912721 : Blo 1939435 4912721 := bstep (se 2 (by rfl) ⟨1842270, by rfl⟩ : syracuseStep 4912721 = 3684541) B3684541
theorem B3275147 : Blo 1939435 3275147 := bstep (se 1 (by rfl) ⟨2456360, by rfl⟩ : syracuseStep 3275147 = 4912721) B4912721
theorem B2183431 : Blo 1939435 2183431 := bstep (se 1 (by rfl) ⟨1637573, by rfl⟩ : syracuseStep 2183431 = 3275147) B3275147
theorem B2911241 : Blo 1939435 2911241 := bstep (se 2 (by rfl) ⟨1091715, by rfl⟩ : syracuseStep 2911241 = 2183431) B2183431
theorem B1940827 : Blo 1939435 1940827 := bstep (se 1 (by rfl) ⟨1455620, by rfl⟩ : syracuseStep 1940827 = 2911241) B2911241
theorem B9825461 : Blo 1939435 9825461 := bbase (se 5 (by rfl) ⟨460568, by rfl⟩ : syracuseStep 9825461 = 921137) (by norm_num)
theorem B6550307 : Blo 1939435 6550307 := bstep (se 1 (by rfl) ⟨4912730, by rfl⟩ : syracuseStep 6550307 = 9825461) B9825461
theorem B4366871 : Blo 1939435 4366871 := bstep (se 1 (by rfl) ⟨3275153, by rfl⟩ : syracuseStep 4366871 = 6550307) B6550307
theorem B2911247 : Blo 1939435 2911247 := bstep (se 1 (by rfl) ⟨2183435, by rfl⟩ : syracuseStep 2911247 = 4366871) B4366871
theorem B1940831 : Blo 1939435 1940831 := bstep (se 1 (by rfl) ⟨1455623, by rfl⟩ : syracuseStep 1940831 = 2911247) B2911247
theorem B2911253 : Blo 1939435 2911253 := bbase (se 6 (by rfl) ⟨68232, by rfl⟩ : syracuseStep 2911253 = 136465) (by norm_num)
theorem B1940835 : Blo 1939435 1940835 := bstep (se 1 (by rfl) ⟨1455626, by rfl⟩ : syracuseStep 1940835 = 2911253) B2911253
theorem B2623093 : Blo 1939435 2623093 := bbase (se 5 (by rfl) ⟨122957, by rfl⟩ : syracuseStep 2623093 = 245915) (by norm_num)
theorem B13989829 : Blo 1939435 13989829 := bstep (se 4 (by rfl) ⟨1311546, by rfl⟩ : syracuseStep 13989829 = 2623093) B2623093
theorem B18653105 : Blo 1939435 18653105 := bstep (se 2 (by rfl) ⟨6994914, by rfl⟩ : syracuseStep 18653105 = 13989829) B13989829
theorem B12435403 : Blo 1939435 12435403 := bstep (se 1 (by rfl) ⟨9326552, by rfl⟩ : syracuseStep 12435403 = 18653105) B18653105
theorem B16580537 : Blo 1939435 16580537 := bstep (se 2 (by rfl) ⟨6217701, by rfl⟩ : syracuseStep 16580537 = 12435403) B12435403
theorem B11053691 : Blo 1939435 11053691 := bstep (se 1 (by rfl) ⟨8290268, by rfl⟩ : syracuseStep 11053691 = 16580537) B16580537
theorem B7369127 : Blo 1939435 7369127 := bstep (se 1 (by rfl) ⟨5526845, by rfl⟩ : syracuseStep 7369127 = 11053691) B11053691
theorem B4912751 : Blo 1939435 4912751 := bstep (se 1 (by rfl) ⟨3684563, by rfl⟩ : syracuseStep 4912751 = 7369127) B7369127
theorem B3275167 : Blo 1939435 3275167 := bstep (se 1 (by rfl) ⟨2456375, by rfl⟩ : syracuseStep 3275167 = 4912751) B4912751
theorem B4366889 : Blo 1939435 4366889 := bstep (se 2 (by rfl) ⟨1637583, by rfl⟩ : syracuseStep 4366889 = 3275167) B3275167
theorem B2911259 : Blo 1939435 2911259 := bstep (se 1 (by rfl) ⟨2183444, by rfl⟩ : syracuseStep 2911259 = 4366889) B4366889
theorem B1940839 : Blo 1939435 1940839 := bstep (se 1 (by rfl) ⟨1455629, by rfl⟩ : syracuseStep 1940839 = 2911259) B2911259
theorem B2183449 : Blo 1939435 2183449 := bbase (se 2 (by rfl) ⟨818793, by rfl⟩ : syracuseStep 2183449 = 1637587) (by norm_num)
theorem B2911265 : Blo 1939435 2911265 := bstep (se 2 (by rfl) ⟨1091724, by rfl⟩ : syracuseStep 2911265 = 2183449) B2183449
theorem B1940843 : Blo 1939435 1940843 := bstep (se 1 (by rfl) ⟨1455632, by rfl⟩ : syracuseStep 1940843 = 2911265) B2911265
theorem B7369157 : Blo 1939435 7369157 := bbase (se 4 (by rfl) ⟨690858, by rfl⟩ : syracuseStep 7369157 = 1381717) (by norm_num)
theorem B4912771 : Blo 1939435 4912771 := bstep (se 1 (by rfl) ⟨3684578, by rfl⟩ : syracuseStep 4912771 = 7369157) B7369157
theorem B6550361 : Blo 1939435 6550361 := bstep (se 2 (by rfl) ⟨2456385, by rfl⟩ : syracuseStep 6550361 = 4912771) B4912771
theorem B4366907 : Blo 1939435 4366907 := bstep (se 1 (by rfl) ⟨3275180, by rfl⟩ : syracuseStep 4366907 = 6550361) B6550361
theorem B2911271 : Blo 1939435 2911271 := bstep (se 1 (by rfl) ⟨2183453, by rfl⟩ : syracuseStep 2911271 = 4366907) B4366907
theorem B1940847 : Blo 1939435 1940847 := bstep (se 1 (by rfl) ⟨1455635, by rfl⟩ : syracuseStep 1940847 = 2911271) B2911271
theorem B2911277 : Blo 1939435 2911277 := bbase (se 3 (by rfl) ⟨545864, by rfl⟩ : syracuseStep 2911277 = 1091729) (by norm_num)
theorem B1940851 : Blo 1939435 1940851 := bstep (se 1 (by rfl) ⟨1455638, by rfl⟩ : syracuseStep 1940851 = 2911277) B2911277
theorem B4366925 : Blo 1939435 4366925 := bbase (se 3 (by rfl) ⟨818798, by rfl⟩ : syracuseStep 4366925 = 1637597) (by norm_num)
theorem B2911283 : Blo 1939435 2911283 := bstep (se 1 (by rfl) ⟨2183462, by rfl⟩ : syracuseStep 2911283 = 4366925) B4366925
theorem B1940855 : Blo 1939435 1940855 := bstep (se 1 (by rfl) ⟨1455641, by rfl⟩ : syracuseStep 1940855 = 2911283) B2911283
theorem B2456401 : Blo 1939435 2456401 := bbase (se 2 (by rfl) ⟨921150, by rfl⟩ : syracuseStep 2456401 = 1842301) (by norm_num)
theorem B3275201 : Blo 1939435 3275201 := bstep (se 2 (by rfl) ⟨1228200, by rfl⟩ : syracuseStep 3275201 = 2456401) B2456401
theorem B2183467 : Blo 1939435 2183467 := bstep (se 1 (by rfl) ⟨1637600, by rfl⟩ : syracuseStep 2183467 = 3275201) B3275201
theorem B2911289 : Blo 1939435 2911289 := bstep (se 2 (by rfl) ⟨1091733, by rfl⟩ : syracuseStep 2911289 = 2183467) B2183467
theorem B1940859 : Blo 1939435 1940859 := bstep (se 1 (by rfl) ⟨1455644, by rfl⟩ : syracuseStep 1940859 = 2911289) B2911289
theorem B3497501 : Blo 1939435 3497501 := bbase (se 3 (by rfl) ⟨655781, by rfl⟩ : syracuseStep 3497501 = 1311563) (by norm_num)
theorem B2331667 : Blo 1939435 2331667 := bstep (se 1 (by rfl) ⟨1748750, by rfl⟩ : syracuseStep 2331667 = 3497501) B3497501
theorem B3108889 : Blo 1939435 3108889 := bstep (se 2 (by rfl) ⟨1165833, by rfl⟩ : syracuseStep 3108889 = 2331667) B2331667
theorem B4145185 : Blo 1939435 4145185 := bstep (se 2 (by rfl) ⟨1554444, by rfl⟩ : syracuseStep 4145185 = 3108889) B3108889
theorem B22107653 : Blo 1939435 22107653 := bstep (se 4 (by rfl) ⟨2072592, by rfl⟩ : syracuseStep 22107653 = 4145185) B4145185
theorem B14738435 : Blo 1939435 14738435 := bstep (se 1 (by rfl) ⟨11053826, by rfl⟩ : syracuseStep 14738435 = 22107653) B22107653
theorem B9825623 : Blo 1939435 9825623 := bstep (se 1 (by rfl) ⟨7369217, by rfl⟩ : syracuseStep 9825623 = 14738435) B14738435
theorem B6550415 : Blo 1939435 6550415 := bstep (se 1 (by rfl) ⟨4912811, by rfl⟩ : syracuseStep 6550415 = 9825623) B9825623
theorem B4366943 : Blo 1939435 4366943 := bstep (se 1 (by rfl) ⟨3275207, by rfl⟩ : syracuseStep 4366943 = 6550415) B6550415
theorem B2911295 : Blo 1939435 2911295 := bstep (se 1 (by rfl) ⟨2183471, by rfl⟩ : syracuseStep 2911295 = 4366943) B4366943
theorem B1940863 : Blo 1939435 1940863 := bstep (se 1 (by rfl) ⟨1455647, by rfl⟩ : syracuseStep 1940863 = 2911295) B2911295
theorem B2911301 : Blo 1939435 2911301 := bbase (se 4 (by rfl) ⟨272934, by rfl⟩ : syracuseStep 2911301 = 545869) (by norm_num)
theorem B1940867 : Blo 1939435 1940867 := bstep (se 1 (by rfl) ⟨1455650, by rfl⟩ : syracuseStep 1940867 = 2911301) B2911301
theorem B3275221 : Blo 1939435 3275221 := bbase (se 7 (by rfl) ⟨38381, by rfl⟩ : syracuseStep 3275221 = 76763) (by norm_num)
theorem B4366961 : Blo 1939435 4366961 := bstep (se 2 (by rfl) ⟨1637610, by rfl⟩ : syracuseStep 4366961 = 3275221) B3275221
theorem B2911307 : Blo 1939435 2911307 := bstep (se 1 (by rfl) ⟨2183480, by rfl⟩ : syracuseStep 2911307 = 4366961) B4366961
theorem B1940871 : Blo 1939435 1940871 := bstep (se 1 (by rfl) ⟨1455653, by rfl⟩ : syracuseStep 1940871 = 2911307) B2911307
theorem B2183485 : Blo 1939435 2183485 := bbase (se 3 (by rfl) ⟨409403, by rfl⟩ : syracuseStep 2183485 = 818807) (by norm_num)
theorem B2911313 : Blo 1939435 2911313 := bstep (se 2 (by rfl) ⟨1091742, by rfl⟩ : syracuseStep 2911313 = 2183485) B2183485
theorem B1940875 : Blo 1939435 1940875 := bstep (se 1 (by rfl) ⟨1455656, by rfl⟩ : syracuseStep 1940875 = 2911313) B2911313
theorem B6550469 : Blo 1939435 6550469 := bbase (se 4 (by rfl) ⟨614106, by rfl⟩ : syracuseStep 6550469 = 1228213) (by norm_num)
theorem B4366979 : Blo 1939435 4366979 := bstep (se 1 (by rfl) ⟨3275234, by rfl⟩ : syracuseStep 4366979 = 6550469) B6550469
theorem B2911319 : Blo 1939435 2911319 := bstep (se 1 (by rfl) ⟨2183489, by rfl⟩ : syracuseStep 2911319 = 4366979) B4366979
theorem B1940879 : Blo 1939435 1940879 := bstep (se 1 (by rfl) ⟨1455659, by rfl⟩ : syracuseStep 1940879 = 2911319) B2911319
theorem B2911325 : Blo 1939435 2911325 := bbase (se 3 (by rfl) ⟨545873, by rfl⟩ : syracuseStep 2911325 = 1091747) (by norm_num)
theorem B1940883 : Blo 1939435 1940883 := bstep (se 1 (by rfl) ⟨1455662, by rfl⟩ : syracuseStep 1940883 = 2911325) B2911325
theorem B4366997 : Blo 1939435 4366997 := bbase (se 6 (by rfl) ⟨102351, by rfl⟩ : syracuseStep 4366997 = 204703) (by norm_num)
theorem B2911331 : Blo 1939435 2911331 := bstep (se 1 (by rfl) ⟨2183498, by rfl⟩ : syracuseStep 2911331 = 4366997) B4366997
theorem B1940887 : Blo 1939435 1940887 := bstep (se 1 (by rfl) ⟨1455665, by rfl⟩ : syracuseStep 1940887 = 2911331) B2911331
theorem B22409621 : Blo 1939435 22409621 := bbase (se 6 (by rfl) ⟨525225, by rfl⟩ : syracuseStep 22409621 = 1050451) (by norm_num)
theorem B14939747 : Blo 1939435 14939747 := bstep (se 1 (by rfl) ⟨11204810, by rfl⟩ : syracuseStep 14939747 = 22409621) B22409621
theorem B9959831 : Blo 1939435 9959831 := bstep (se 1 (by rfl) ⟨7469873, by rfl⟩ : syracuseStep 9959831 = 14939747) B14939747
theorem B6639887 : Blo 1939435 6639887 := bstep (se 1 (by rfl) ⟨4979915, by rfl⟩ : syracuseStep 6639887 = 9959831) B9959831
theorem B4426591 : Blo 1939435 4426591 := bstep (se 1 (by rfl) ⟨3319943, by rfl⟩ : syracuseStep 4426591 = 6639887) B6639887
theorem B5902121 : Blo 1939435 5902121 := bstep (se 2 (by rfl) ⟨2213295, by rfl⟩ : syracuseStep 5902121 = 4426591) B4426591
theorem B3934747 : Blo 1939435 3934747 := bstep (se 1 (by rfl) ⟨2951060, by rfl⟩ : syracuseStep 3934747 = 5902121) B5902121
theorem B5246329 : Blo 1939435 5246329 := bstep (se 2 (by rfl) ⟨1967373, by rfl⟩ : syracuseStep 5246329 = 3934747) B3934747
theorem B6995105 : Blo 1939435 6995105 := bstep (se 2 (by rfl) ⟨2623164, by rfl⟩ : syracuseStep 6995105 = 5246329) B5246329
theorem B4663403 : Blo 1939435 4663403 := bstep (se 1 (by rfl) ⟨3497552, by rfl⟩ : syracuseStep 4663403 = 6995105) B6995105
theorem B3108935 : Blo 1939435 3108935 := bstep (se 1 (by rfl) ⟨2331701, by rfl⟩ : syracuseStep 3108935 = 4663403) B4663403
theorem B2072623 : Blo 1939435 2072623 := bstep (se 1 (by rfl) ⟨1554467, by rfl⟩ : syracuseStep 2072623 = 3108935) B3108935
theorem B2763497 : Blo 1939435 2763497 := bstep (se 2 (by rfl) ⟨1036311, by rfl⟩ : syracuseStep 2763497 = 2072623) B2072623
theorem B7369325 : Blo 1939435 7369325 := bstep (se 3 (by rfl) ⟨1381748, by rfl⟩ : syracuseStep 7369325 = 2763497) B2763497
theorem B4912883 : Blo 1939435 4912883 := bstep (se 1 (by rfl) ⟨3684662, by rfl⟩ : syracuseStep 4912883 = 7369325) B7369325
theorem B3275255 : Blo 1939435 3275255 := bstep (se 1 (by rfl) ⟨2456441, by rfl⟩ : syracuseStep 3275255 = 4912883) B4912883
theorem B2183503 : Blo 1939435 2183503 := bstep (se 1 (by rfl) ⟨1637627, by rfl⟩ : syracuseStep 2183503 = 3275255) B3275255
theorem B2911337 : Blo 1939435 2911337 := bstep (se 2 (by rfl) ⟨1091751, by rfl⟩ : syracuseStep 2911337 = 2183503) B2183503
theorem B1940891 : Blo 1939435 1940891 := bstep (se 1 (by rfl) ⟨1455668, by rfl⟩ : syracuseStep 1940891 = 2911337) B2911337
theorem B9326821 : Blo 1939435 9326821 := bbase (se 4 (by rfl) ⟨874389, by rfl⟩ : syracuseStep 9326821 = 1748779) (by norm_num)
theorem B12435761 : Blo 1939435 12435761 := bstep (se 2 (by rfl) ⟨4663410, by rfl⟩ : syracuseStep 12435761 = 9326821) B9326821
theorem B8290507 : Blo 1939435 8290507 := bstep (se 1 (by rfl) ⟨6217880, by rfl⟩ : syracuseStep 8290507 = 12435761) B12435761
theorem B11054009 : Blo 1939435 11054009 := bstep (se 2 (by rfl) ⟨4145253, by rfl⟩ : syracuseStep 11054009 = 8290507) B8290507
theorem B7369339 : Blo 1939435 7369339 := bstep (se 1 (by rfl) ⟨5527004, by rfl⟩ : syracuseStep 7369339 = 11054009) B11054009
theorem B9825785 : Blo 1939435 9825785 := bstep (se 2 (by rfl) ⟨3684669, by rfl⟩ : syracuseStep 9825785 = 7369339) B7369339
theorem B6550523 : Blo 1939435 6550523 := bstep (se 1 (by rfl) ⟨4912892, by rfl⟩ : syracuseStep 6550523 = 9825785) B9825785
theorem B4367015 : Blo 1939435 4367015 := bstep (se 1 (by rfl) ⟨3275261, by rfl⟩ : syracuseStep 4367015 = 6550523) B6550523
theorem B2911343 : Blo 1939435 2911343 := bstep (se 1 (by rfl) ⟨2183507, by rfl⟩ : syracuseStep 2911343 = 4367015) B4367015
theorem B1940895 : Blo 1939435 1940895 := bstep (se 1 (by rfl) ⟨1455671, by rfl⟩ : syracuseStep 1940895 = 2911343) B2911343
theorem B2911349 : Blo 1939435 2911349 := bbase (se 5 (by rfl) ⟨136469, by rfl⟩ : syracuseStep 2911349 = 272939) (by norm_num)
theorem B1940899 : Blo 1939435 1940899 := bstep (se 1 (by rfl) ⟨1455674, by rfl⟩ : syracuseStep 1940899 = 2911349) B2911349
theorem B3684685 : Blo 1939435 3684685 := bbase (se 3 (by rfl) ⟨690878, by rfl⟩ : syracuseStep 3684685 = 1381757) (by norm_num)
theorem B4912913 : Blo 1939435 4912913 := bstep (se 2 (by rfl) ⟨1842342, by rfl⟩ : syracuseStep 4912913 = 3684685) B3684685
theorem B3275275 : Blo 1939435 3275275 := bstep (se 1 (by rfl) ⟨2456456, by rfl⟩ : syracuseStep 3275275 = 4912913) B4912913
theorem B4367033 : Blo 1939435 4367033 := bstep (se 2 (by rfl) ⟨1637637, by rfl⟩ : syracuseStep 4367033 = 3275275) B3275275
theorem B2911355 : Blo 1939435 2911355 := bstep (se 1 (by rfl) ⟨2183516, by rfl⟩ : syracuseStep 2911355 = 4367033) B4367033
theorem B1940903 : Blo 1939435 1940903 := bstep (se 1 (by rfl) ⟨1455677, by rfl⟩ : syracuseStep 1940903 = 2911355) B2911355
theorem B2183521 : Blo 1939435 2183521 := bbase (se 2 (by rfl) ⟨818820, by rfl⟩ : syracuseStep 2183521 = 1637641) (by norm_num)
theorem B2911361 : Blo 1939435 2911361 := bstep (se 2 (by rfl) ⟨1091760, by rfl⟩ : syracuseStep 2911361 = 2183521) B2183521
theorem B1940907 : Blo 1939435 1940907 := bstep (se 1 (by rfl) ⟨1455680, by rfl⟩ : syracuseStep 1940907 = 2911361) B2911361
theorem B4912933 : Blo 1939435 4912933 := bbase (se 4 (by rfl) ⟨460587, by rfl⟩ : syracuseStep 4912933 = 921175) (by norm_num)
theorem B6550577 : Blo 1939435 6550577 := bstep (se 2 (by rfl) ⟨2456466, by rfl⟩ : syracuseStep 6550577 = 4912933) B4912933
theorem B4367051 : Blo 1939435 4367051 := bstep (se 1 (by rfl) ⟨3275288, by rfl⟩ : syracuseStep 4367051 = 6550577) B6550577
theorem B2911367 : Blo 1939435 2911367 := bstep (se 1 (by rfl) ⟨2183525, by rfl⟩ : syracuseStep 2911367 = 4367051) B4367051
theorem B1940911 : Blo 1939435 1940911 := bstep (se 1 (by rfl) ⟨1455683, by rfl⟩ : syracuseStep 1940911 = 2911367) B2911367
theorem B2911373 : Blo 1939435 2911373 := bbase (se 3 (by rfl) ⟨545882, by rfl⟩ : syracuseStep 2911373 = 1091765) (by norm_num)
theorem B1940915 : Blo 1939435 1940915 := bstep (se 1 (by rfl) ⟨1455686, by rfl⟩ : syracuseStep 1940915 = 2911373) B2911373
theorem B4367069 : Blo 1939435 4367069 := bbase (se 3 (by rfl) ⟨818825, by rfl⟩ : syracuseStep 4367069 = 1637651) (by norm_num)
theorem B2911379 : Blo 1939435 2911379 := bstep (se 1 (by rfl) ⟨2183534, by rfl⟩ : syracuseStep 2911379 = 4367069) B4367069
theorem B1940919 : Blo 1939435 1940919 := bstep (se 1 (by rfl) ⟨1455689, by rfl⟩ : syracuseStep 1940919 = 2911379) B2911379
theorem B3275309 : Blo 1939435 3275309 := bbase (se 3 (by rfl) ⟨614120, by rfl⟩ : syracuseStep 3275309 = 1228241) (by norm_num)
theorem B2183539 : Blo 1939435 2183539 := bstep (se 1 (by rfl) ⟨1637654, by rfl⟩ : syracuseStep 2183539 = 3275309) B3275309
theorem B2911385 : Blo 1939435 2911385 := bstep (se 2 (by rfl) ⟨1091769, by rfl⟩ : syracuseStep 2911385 = 2183539) B2183539
theorem B1940923 : Blo 1939435 1940923 := bstep (se 1 (by rfl) ⟨1455692, by rfl⟩ : syracuseStep 1940923 = 2911385) B2911385
theorem B2243533 : Blo 1939435 2243533 := bbase (se 3 (by rfl) ⟨420662, by rfl⟩ : syracuseStep 2243533 = 841325) (by norm_num)
theorem B2991377 : Blo 1939435 2991377 := bstep (se 2 (by rfl) ⟨1121766, by rfl⟩ : syracuseStep 2991377 = 2243533) B2243533
theorem B7977005 : Blo 1939435 7977005 := bstep (se 3 (by rfl) ⟨1495688, by rfl⟩ : syracuseStep 7977005 = 2991377) B2991377
theorem B5318003 : Blo 1939435 5318003 := bstep (se 1 (by rfl) ⟨3988502, by rfl⟩ : syracuseStep 5318003 = 7977005) B7977005
theorem B3545335 : Blo 1939435 3545335 := bstep (se 1 (by rfl) ⟨2659001, by rfl⟩ : syracuseStep 3545335 = 5318003) B5318003
theorem B18908453 : Blo 1939435 18908453 := bstep (se 4 (by rfl) ⟨1772667, by rfl⟩ : syracuseStep 18908453 = 3545335) B3545335
theorem B12605635 : Blo 1939435 12605635 := bstep (se 1 (by rfl) ⟨9454226, by rfl⟩ : syracuseStep 12605635 = 18908453) B18908453
theorem B16807513 : Blo 1939435 16807513 := bstep (se 2 (by rfl) ⟨6302817, by rfl⟩ : syracuseStep 16807513 = 12605635) B12605635
theorem B22410017 : Blo 1939435 22410017 := bstep (se 2 (by rfl) ⟨8403756, by rfl⟩ : syracuseStep 22410017 = 16807513) B16807513
theorem B14940011 : Blo 1939435 14940011 := bstep (se 1 (by rfl) ⟨11205008, by rfl⟩ : syracuseStep 14940011 = 22410017) B22410017
theorem B9960007 : Blo 1939435 9960007 := bstep (se 1 (by rfl) ⟨7470005, by rfl⟩ : syracuseStep 9960007 = 14940011) B14940011
theorem B13280009 : Blo 1939435 13280009 := bstep (se 2 (by rfl) ⟨4980003, by rfl⟩ : syracuseStep 13280009 = 9960007) B9960007
theorem B35413357 : Blo 1939435 35413357 := bstep (se 3 (by rfl) ⟨6640004, by rfl⟩ : syracuseStep 35413357 = 13280009) B13280009
theorem B47217809 : Blo 1939435 47217809 := bstep (se 2 (by rfl) ⟨17706678, by rfl⟩ : syracuseStep 47217809 = 35413357) B35413357
theorem B31478539 : Blo 1939435 31478539 := bstep (se 1 (by rfl) ⟨23608904, by rfl⟩ : syracuseStep 31478539 = 47217809) B47217809
theorem B41971385 : Blo 1939435 41971385 := bstep (se 2 (by rfl) ⟨15739269, by rfl⟩ : syracuseStep 41971385 = 31478539) B31478539
theorem B27980923 : Blo 1939435 27980923 := bstep (se 1 (by rfl) ⟨20985692, by rfl⟩ : syracuseStep 27980923 = 41971385) B41971385
theorem B37307897 : Blo 1939435 37307897 := bstep (se 2 (by rfl) ⟨13990461, by rfl⟩ : syracuseStep 37307897 = 27980923) B27980923
theorem B24871931 : Blo 1939435 24871931 := bstep (se 1 (by rfl) ⟨18653948, by rfl⟩ : syracuseStep 24871931 = 37307897) B37307897
theorem B16581287 : Blo 1939435 16581287 := bstep (se 1 (by rfl) ⟨12435965, by rfl⟩ : syracuseStep 16581287 = 24871931) B24871931
theorem B11054191 : Blo 1939435 11054191 := bstep (se 1 (by rfl) ⟨8290643, by rfl⟩ : syracuseStep 11054191 = 16581287) B16581287
theorem B14738921 : Blo 1939435 14738921 := bstep (se 2 (by rfl) ⟨5527095, by rfl⟩ : syracuseStep 14738921 = 11054191) B11054191
theorem B9825947 : Blo 1939435 9825947 := bstep (se 1 (by rfl) ⟨7369460, by rfl⟩ : syracuseStep 9825947 = 14738921) B14738921
theorem B6550631 : Blo 1939435 6550631 := bstep (se 1 (by rfl) ⟨4912973, by rfl⟩ : syracuseStep 6550631 = 9825947) B9825947
theorem B4367087 : Blo 1939435 4367087 := bstep (se 1 (by rfl) ⟨3275315, by rfl⟩ : syracuseStep 4367087 = 6550631) B6550631
theorem B2911391 : Blo 1939435 2911391 := bstep (se 1 (by rfl) ⟨2183543, by rfl⟩ : syracuseStep 2911391 = 4367087) B4367087
theorem B1940927 : Blo 1939435 1940927 := bstep (se 1 (by rfl) ⟨1455695, by rfl⟩ : syracuseStep 1940927 = 2911391) B2911391
theorem B2911397 : Blo 1939435 2911397 := bbase (se 4 (by rfl) ⟨272943, by rfl⟩ : syracuseStep 2911397 = 545887) (by norm_num)
theorem B1940931 : Blo 1939435 1940931 := bstep (se 1 (by rfl) ⟨1455698, by rfl⟩ : syracuseStep 1940931 = 2911397) B2911397
theorem B2456497 : Blo 1939435 2456497 := bbase (se 2 (by rfl) ⟨921186, by rfl⟩ : syracuseStep 2456497 = 1842373) (by norm_num)
theorem B3275329 : Blo 1939435 3275329 := bstep (se 2 (by rfl) ⟨1228248, by rfl⟩ : syracuseStep 3275329 = 2456497) B2456497
theorem B4367105 : Blo 1939435 4367105 := bstep (se 2 (by rfl) ⟨1637664, by rfl⟩ : syracuseStep 4367105 = 3275329) B3275329
theorem B2911403 : Blo 1939435 2911403 := bstep (se 1 (by rfl) ⟨2183552, by rfl⟩ : syracuseStep 2911403 = 4367105) B4367105
theorem B1940935 : Blo 1939435 1940935 := bstep (se 1 (by rfl) ⟨1455701, by rfl⟩ : syracuseStep 1940935 = 2911403) B2911403
theorem B2183557 : Blo 1939435 2183557 := bbase (se 4 (by rfl) ⟨204708, by rfl⟩ : syracuseStep 2183557 = 409417) (by norm_num)
theorem B2911409 : Blo 1939435 2911409 := bstep (se 2 (by rfl) ⟨1091778, by rfl⟩ : syracuseStep 2911409 = 2183557) B2183557
theorem B1940939 : Blo 1939435 1940939 := bstep (se 1 (by rfl) ⟨1455704, by rfl⟩ : syracuseStep 1940939 = 2911409) B2911409
theorem B4145357 : Blo 1939435 4145357 := bbase (se 3 (by rfl) ⟨777254, by rfl⟩ : syracuseStep 4145357 = 1554509) (by norm_num)
theorem B2763571 : Blo 1939435 2763571 := bstep (se 1 (by rfl) ⟨2072678, by rfl⟩ : syracuseStep 2763571 = 4145357) B4145357
theorem B3684761 : Blo 1939435 3684761 := bstep (se 2 (by rfl) ⟨1381785, by rfl⟩ : syracuseStep 3684761 = 2763571) B2763571
theorem B2456507 : Blo 1939435 2456507 := bstep (se 1 (by rfl) ⟨1842380, by rfl⟩ : syracuseStep 2456507 = 3684761) B3684761
theorem B6550685 : Blo 1939435 6550685 := bstep (se 3 (by rfl) ⟨1228253, by rfl⟩ : syracuseStep 6550685 = 2456507) B2456507
theorem B4367123 : Blo 1939435 4367123 := bstep (se 1 (by rfl) ⟨3275342, by rfl⟩ : syracuseStep 4367123 = 6550685) B6550685
theorem B2911415 : Blo 1939435 2911415 := bstep (se 1 (by rfl) ⟨2183561, by rfl⟩ : syracuseStep 2911415 = 4367123) B4367123
theorem B1940943 : Blo 1939435 1940943 := bstep (se 1 (by rfl) ⟨1455707, by rfl⟩ : syracuseStep 1940943 = 2911415) B2911415
theorem B2911421 : Blo 1939435 2911421 := bbase (se 3 (by rfl) ⟨545891, by rfl⟩ : syracuseStep 2911421 = 1091783) (by norm_num)
theorem B1940947 : Blo 1939435 1940947 := bstep (se 1 (by rfl) ⟨1455710, by rfl⟩ : syracuseStep 1940947 = 2911421) B2911421
theorem B4367141 : Blo 1939435 4367141 := bbase (se 4 (by rfl) ⟨409419, by rfl⟩ : syracuseStep 4367141 = 818839) (by norm_num)
theorem B2911427 : Blo 1939435 2911427 := bstep (se 1 (by rfl) ⟨2183570, by rfl⟩ : syracuseStep 2911427 = 4367141) B4367141
theorem B1940951 : Blo 1939435 1940951 := bstep (se 1 (by rfl) ⟨1455713, by rfl⟩ : syracuseStep 1940951 = 2911427) B2911427
theorem B4913045 : Blo 1939435 4913045 := bbase (se 6 (by rfl) ⟨115149, by rfl⟩ : syracuseStep 4913045 = 230299) (by norm_num)
theorem B3275363 : Blo 1939435 3275363 := bstep (se 1 (by rfl) ⟨2456522, by rfl⟩ : syracuseStep 3275363 = 4913045) B4913045
theorem B2183575 : Blo 1939435 2183575 := bstep (se 1 (by rfl) ⟨1637681, by rfl⟩ : syracuseStep 2183575 = 3275363) B3275363
theorem B2911433 : Blo 1939435 2911433 := bstep (se 2 (by rfl) ⟨1091787, by rfl⟩ : syracuseStep 2911433 = 2183575) B2183575
theorem B1940955 : Blo 1939435 1940955 := bstep (se 1 (by rfl) ⟨1455716, by rfl⟩ : syracuseStep 1940955 = 2911433) B2911433
theorem B4663565 : Blo 1939435 4663565 := bbase (se 3 (by rfl) ⟨874418, by rfl⟩ : syracuseStep 4663565 = 1748837) (by norm_num)
theorem B3109043 : Blo 1939435 3109043 := bstep (se 1 (by rfl) ⟨2331782, by rfl⟩ : syracuseStep 3109043 = 4663565) B4663565
theorem B8290781 : Blo 1939435 8290781 := bstep (se 3 (by rfl) ⟨1554521, by rfl⟩ : syracuseStep 8290781 = 3109043) B3109043
theorem B5527187 : Blo 1939435 5527187 := bstep (se 1 (by rfl) ⟨4145390, by rfl⟩ : syracuseStep 5527187 = 8290781) B8290781
theorem B3684791 : Blo 1939435 3684791 := bstep (se 1 (by rfl) ⟨2763593, by rfl⟩ : syracuseStep 3684791 = 5527187) B5527187
theorem B9826109 : Blo 1939435 9826109 := bstep (se 3 (by rfl) ⟨1842395, by rfl⟩ : syracuseStep 9826109 = 3684791) B3684791
theorem B6550739 : Blo 1939435 6550739 := bstep (se 1 (by rfl) ⟨4913054, by rfl⟩ : syracuseStep 6550739 = 9826109) B9826109
theorem B4367159 : Blo 1939435 4367159 := bstep (se 1 (by rfl) ⟨3275369, by rfl⟩ : syracuseStep 4367159 = 6550739) B6550739
theorem B2911439 : Blo 1939435 2911439 := bstep (se 1 (by rfl) ⟨2183579, by rfl⟩ : syracuseStep 2911439 = 4367159) B4367159
theorem B1940959 : Blo 1939435 1940959 := bstep (se 1 (by rfl) ⟨1455719, by rfl⟩ : syracuseStep 1940959 = 2911439) B2911439
theorem B2911445 : Blo 1939435 2911445 := bbase (se 7 (by rfl) ⟨34118, by rfl⟩ : syracuseStep 2911445 = 68237) (by norm_num)
theorem B1940963 : Blo 1939435 1940963 := bstep (se 1 (by rfl) ⟨1455722, by rfl⟩ : syracuseStep 1940963 = 2911445) B2911445
theorem B2763605 : Blo 1939435 2763605 := bbase (se 9 (by rfl) ⟨8096, by rfl⟩ : syracuseStep 2763605 = 16193) (by norm_num)
theorem B7369613 : Blo 1939435 7369613 := bstep (se 3 (by rfl) ⟨1381802, by rfl⟩ : syracuseStep 7369613 = 2763605) B2763605
theorem B4913075 : Blo 1939435 4913075 := bstep (se 1 (by rfl) ⟨3684806, by rfl⟩ : syracuseStep 4913075 = 7369613) B7369613
theorem B3275383 : Blo 1939435 3275383 := bstep (se 1 (by rfl) ⟨2456537, by rfl⟩ : syracuseStep 3275383 = 4913075) B4913075
theorem B4367177 : Blo 1939435 4367177 := bstep (se 2 (by rfl) ⟨1637691, by rfl⟩ : syracuseStep 4367177 = 3275383) B3275383
theorem B2911451 : Blo 1939435 2911451 := bstep (se 1 (by rfl) ⟨2183588, by rfl⟩ : syracuseStep 2911451 = 4367177) B4367177
theorem B1940967 : Blo 1939435 1940967 := bstep (se 1 (by rfl) ⟨1455725, by rfl⟩ : syracuseStep 1940967 = 2911451) B2911451
theorem B2183593 : Blo 1939435 2183593 := bbase (se 2 (by rfl) ⟨818847, by rfl⟩ : syracuseStep 2183593 = 1637695) (by norm_num)
theorem B2911457 : Blo 1939435 2911457 := bstep (se 2 (by rfl) ⟨1091796, by rfl⟩ : syracuseStep 2911457 = 2183593) B2183593
theorem B1940971 : Blo 1939435 1940971 := bstep (se 1 (by rfl) ⟨1455728, by rfl⟩ : syracuseStep 1940971 = 2911457) B2911457
theorem B2623277 : Blo 1939435 2623277 := bbase (se 3 (by rfl) ⟨491864, by rfl⟩ : syracuseStep 2623277 = 983729) (by norm_num)
theorem B6995405 : Blo 1939435 6995405 := bstep (se 3 (by rfl) ⟨1311638, by rfl⟩ : syracuseStep 6995405 = 2623277) B2623277
theorem B4663603 : Blo 1939435 4663603 := bstep (se 1 (by rfl) ⟨3497702, by rfl⟩ : syracuseStep 4663603 = 6995405) B6995405
theorem B6218137 : Blo 1939435 6218137 := bstep (se 2 (by rfl) ⟨2331801, by rfl⟩ : syracuseStep 6218137 = 4663603) B4663603
theorem B8290849 : Blo 1939435 8290849 := bstep (se 2 (by rfl) ⟨3109068, by rfl⟩ : syracuseStep 8290849 = 6218137) B6218137
theorem B11054465 : Blo 1939435 11054465 := bstep (se 2 (by rfl) ⟨4145424, by rfl⟩ : syracuseStep 11054465 = 8290849) B8290849
theorem B7369643 : Blo 1939435 7369643 := bstep (se 1 (by rfl) ⟨5527232, by rfl⟩ : syracuseStep 7369643 = 11054465) B11054465
theorem B4913095 : Blo 1939435 4913095 := bstep (se 1 (by rfl) ⟨3684821, by rfl⟩ : syracuseStep 4913095 = 7369643) B7369643
theorem B6550793 : Blo 1939435 6550793 := bstep (se 2 (by rfl) ⟨2456547, by rfl⟩ : syracuseStep 6550793 = 4913095) B4913095
theorem B4367195 : Blo 1939435 4367195 := bstep (se 1 (by rfl) ⟨3275396, by rfl⟩ : syracuseStep 4367195 = 6550793) B6550793
theorem B2911463 : Blo 1939435 2911463 := bstep (se 1 (by rfl) ⟨2183597, by rfl⟩ : syracuseStep 2911463 = 4367195) B4367195
theorem B1940975 : Blo 1939435 1940975 := bstep (se 1 (by rfl) ⟨1455731, by rfl⟩ : syracuseStep 1940975 = 2911463) B2911463
theorem B2911469 : Blo 1939435 2911469 := bbase (se 3 (by rfl) ⟨545900, by rfl⟩ : syracuseStep 2911469 = 1091801) (by norm_num)
theorem B1940979 : Blo 1939435 1940979 := bstep (se 1 (by rfl) ⟨1455734, by rfl⟩ : syracuseStep 1940979 = 2911469) B2911469
theorem B4367213 : Blo 1939435 4367213 := bbase (se 3 (by rfl) ⟨818852, by rfl⟩ : syracuseStep 4367213 = 1637705) (by norm_num)
theorem B2911475 : Blo 1939435 2911475 := bstep (se 1 (by rfl) ⟨2183606, by rfl⟩ : syracuseStep 2911475 = 4367213) B4367213
theorem B1940983 : Blo 1939435 1940983 := bstep (se 1 (by rfl) ⟨1455737, by rfl⟩ : syracuseStep 1940983 = 2911475) B2911475
theorem B3684845 : Blo 1939435 3684845 := bbase (se 3 (by rfl) ⟨690908, by rfl⟩ : syracuseStep 3684845 = 1381817) (by norm_num)
theorem B2456563 : Blo 1939435 2456563 := bstep (se 1 (by rfl) ⟨1842422, by rfl⟩ : syracuseStep 2456563 = 3684845) B3684845
theorem B3275417 : Blo 1939435 3275417 := bstep (se 2 (by rfl) ⟨1228281, by rfl⟩ : syracuseStep 3275417 = 2456563) B2456563
theorem B2183611 : Blo 1939435 2183611 := bstep (se 1 (by rfl) ⟨1637708, by rfl⟩ : syracuseStep 2183611 = 3275417) B3275417
theorem B2911481 : Blo 1939435 2911481 := bstep (se 2 (by rfl) ⟨1091805, by rfl⟩ : syracuseStep 2911481 = 2183611) B2183611
theorem B1940987 : Blo 1939435 1940987 := bstep (se 1 (by rfl) ⟨1455740, by rfl⟩ : syracuseStep 1940987 = 2911481) B2911481
theorem B27981845 : Blo 1939435 27981845 := bbase (se 6 (by rfl) ⟨655824, by rfl⟩ : syracuseStep 27981845 = 1311649) (by norm_num)
theorem B18654563 : Blo 1939435 18654563 := bstep (se 1 (by rfl) ⟨13990922, by rfl⟩ : syracuseStep 18654563 = 27981845) B27981845
theorem B49745501 : Blo 1939435 49745501 := bstep (se 3 (by rfl) ⟨9327281, by rfl⟩ : syracuseStep 49745501 = 18654563) B18654563
theorem B33163667 : Blo 1939435 33163667 := bstep (se 1 (by rfl) ⟨24872750, by rfl⟩ : syracuseStep 33163667 = 49745501) B49745501
theorem B22109111 : Blo 1939435 22109111 := bstep (se 1 (by rfl) ⟨16581833, by rfl⟩ : syracuseStep 22109111 = 33163667) B33163667
theorem B14739407 : Blo 1939435 14739407 := bstep (se 1 (by rfl) ⟨11054555, by rfl⟩ : syracuseStep 14739407 = 22109111) B22109111
theorem B9826271 : Blo 1939435 9826271 := bstep (se 1 (by rfl) ⟨7369703, by rfl⟩ : syracuseStep 9826271 = 14739407) B14739407
theorem B6550847 : Blo 1939435 6550847 := bstep (se 1 (by rfl) ⟨4913135, by rfl⟩ : syracuseStep 6550847 = 9826271) B9826271
theorem B4367231 : Blo 1939435 4367231 := bstep (se 1 (by rfl) ⟨3275423, by rfl⟩ : syracuseStep 4367231 = 6550847) B6550847
theorem B2911487 : Blo 1939435 2911487 := bstep (se 1 (by rfl) ⟨2183615, by rfl⟩ : syracuseStep 2911487 = 4367231) B4367231
theorem B1940991 : Blo 1939435 1940991 := bstep (se 1 (by rfl) ⟨1455743, by rfl⟩ : syracuseStep 1940991 = 2911487) B2911487
theorem B2911493 : Blo 1939435 2911493 := bbase (se 4 (by rfl) ⟨272952, by rfl⟩ : syracuseStep 2911493 = 545905) (by norm_num)
theorem B1940995 : Blo 1939435 1940995 := bstep (se 1 (by rfl) ⟨1455746, by rfl⟩ : syracuseStep 1940995 = 2911493) B2911493
theorem B3275437 : Blo 1939435 3275437 := bbase (se 3 (by rfl) ⟨614144, by rfl⟩ : syracuseStep 3275437 = 1228289) (by norm_num)
theorem B4367249 : Blo 1939435 4367249 := bstep (se 2 (by rfl) ⟨1637718, by rfl⟩ : syracuseStep 4367249 = 3275437) B3275437
theorem B2911499 : Blo 1939435 2911499 := bstep (se 1 (by rfl) ⟨2183624, by rfl⟩ : syracuseStep 2911499 = 4367249) B4367249
theorem B1940999 : Blo 1939435 1940999 := bstep (se 1 (by rfl) ⟨1455749, by rfl⟩ : syracuseStep 1940999 = 2911499) B2911499
theorem B2183629 : Blo 1939435 2183629 := bbase (se 3 (by rfl) ⟨409430, by rfl⟩ : syracuseStep 2183629 = 818861) (by norm_num)
theorem B2911505 : Blo 1939435 2911505 := bstep (se 2 (by rfl) ⟨1091814, by rfl⟩ : syracuseStep 2911505 = 2183629) B2183629
theorem B1941003 : Blo 1939435 1941003 := bstep (se 1 (by rfl) ⟨1455752, by rfl⟩ : syracuseStep 1941003 = 2911505) B2911505
theorem B6550901 : Blo 1939435 6550901 := bbase (se 5 (by rfl) ⟨307073, by rfl⟩ : syracuseStep 6550901 = 614147) (by norm_num)
theorem B4367267 : Blo 1939435 4367267 := bstep (se 1 (by rfl) ⟨3275450, by rfl⟩ : syracuseStep 4367267 = 6550901) B6550901
theorem B2911511 : Blo 1939435 2911511 := bstep (se 1 (by rfl) ⟨2183633, by rfl⟩ : syracuseStep 2911511 = 4367267) B4367267
theorem B1941007 : Blo 1939435 1941007 := bstep (se 1 (by rfl) ⟨1455755, by rfl⟩ : syracuseStep 1941007 = 2911511) B2911511
theorem B2911517 : Blo 1939435 2911517 := bbase (se 3 (by rfl) ⟨545909, by rfl⟩ : syracuseStep 2911517 = 1091819) (by norm_num)
theorem B1941011 : Blo 1939435 1941011 := bstep (se 1 (by rfl) ⟨1455758, by rfl⟩ : syracuseStep 1941011 = 2911517) B2911517
theorem B4367285 : Blo 1939435 4367285 := bbase (se 5 (by rfl) ⟨204716, by rfl⟩ : syracuseStep 4367285 = 409433) (by norm_num)
theorem B2911523 : Blo 1939435 2911523 := bstep (se 1 (by rfl) ⟨2183642, by rfl⟩ : syracuseStep 2911523 = 4367285) B4367285
theorem B1941015 : Blo 1939435 1941015 := bstep (se 1 (by rfl) ⟨1455761, by rfl⟩ : syracuseStep 1941015 = 2911523) B2911523
theorem B15740021 : Blo 1939435 15740021 := bbase (se 5 (by rfl) ⟨737813, by rfl⟩ : syracuseStep 15740021 = 1475627) (by norm_num)
theorem B10493347 : Blo 1939435 10493347 := bstep (se 1 (by rfl) ⟨7870010, by rfl⟩ : syracuseStep 10493347 = 15740021) B15740021
theorem B13991129 : Blo 1939435 13991129 := bstep (se 2 (by rfl) ⟨5246673, by rfl⟩ : syracuseStep 13991129 = 10493347) B10493347
theorem B9327419 : Blo 1939435 9327419 := bstep (se 1 (by rfl) ⟨6995564, by rfl⟩ : syracuseStep 9327419 = 13991129) B13991129
theorem B6218279 : Blo 1939435 6218279 := bstep (se 1 (by rfl) ⟨4663709, by rfl⟩ : syracuseStep 6218279 = 9327419) B9327419
theorem B4145519 : Blo 1939435 4145519 := bstep (se 1 (by rfl) ⟨3109139, by rfl⟩ : syracuseStep 4145519 = 6218279) B6218279
theorem B11054717 : Blo 1939435 11054717 := bstep (se 3 (by rfl) ⟨2072759, by rfl⟩ : syracuseStep 11054717 = 4145519) B4145519
theorem B7369811 : Blo 1939435 7369811 := bstep (se 1 (by rfl) ⟨5527358, by rfl⟩ : syracuseStep 7369811 = 11054717) B11054717
theorem B4913207 : Blo 1939435 4913207 := bstep (se 1 (by rfl) ⟨3684905, by rfl⟩ : syracuseStep 4913207 = 7369811) B7369811
theorem B3275471 : Blo 1939435 3275471 := bstep (se 1 (by rfl) ⟨2456603, by rfl⟩ : syracuseStep 3275471 = 4913207) B4913207
theorem B2183647 : Blo 1939435 2183647 := bstep (se 1 (by rfl) ⟨1637735, by rfl⟩ : syracuseStep 2183647 = 3275471) B3275471
theorem B2911529 : Blo 1939435 2911529 := bstep (se 2 (by rfl) ⟨1091823, by rfl⟩ : syracuseStep 2911529 = 2183647) B2183647
theorem B1941019 : Blo 1939435 1941019 := bstep (se 1 (by rfl) ⟨1455764, by rfl⟩ : syracuseStep 1941019 = 2911529) B2911529
theorem B3497789 : Blo 1939435 3497789 := bbase (se 3 (by rfl) ⟨655835, by rfl⟩ : syracuseStep 3497789 = 1311671) (by norm_num)
theorem B9327437 : Blo 1939435 9327437 := bstep (se 3 (by rfl) ⟨1748894, by rfl⟩ : syracuseStep 9327437 = 3497789) B3497789
theorem B6218291 : Blo 1939435 6218291 := bstep (se 1 (by rfl) ⟨4663718, by rfl⟩ : syracuseStep 6218291 = 9327437) B9327437
theorem B4145527 : Blo 1939435 4145527 := bstep (se 1 (by rfl) ⟨3109145, by rfl⟩ : syracuseStep 4145527 = 6218291) B6218291
theorem B5527369 : Blo 1939435 5527369 := bstep (se 2 (by rfl) ⟨2072763, by rfl⟩ : syracuseStep 5527369 = 4145527) B4145527
theorem B7369825 : Blo 1939435 7369825 := bstep (se 2 (by rfl) ⟨2763684, by rfl⟩ : syracuseStep 7369825 = 5527369) B5527369
theorem B9826433 : Blo 1939435 9826433 := bstep (se 2 (by rfl) ⟨3684912, by rfl⟩ : syracuseStep 9826433 = 7369825) B7369825
theorem B6550955 : Blo 1939435 6550955 := bstep (se 1 (by rfl) ⟨4913216, by rfl⟩ : syracuseStep 6550955 = 9826433) B9826433
theorem B4367303 : Blo 1939435 4367303 := bstep (se 1 (by rfl) ⟨3275477, by rfl⟩ : syracuseStep 4367303 = 6550955) B6550955
theorem B2911535 : Blo 1939435 2911535 := bstep (se 1 (by rfl) ⟨2183651, by rfl⟩ : syracuseStep 2911535 = 4367303) B4367303
theorem B1941023 : Blo 1939435 1941023 := bstep (se 1 (by rfl) ⟨1455767, by rfl⟩ : syracuseStep 1941023 = 2911535) B2911535
theorem B2911541 : Blo 1939435 2911541 := bbase (se 5 (by rfl) ⟨136478, by rfl⟩ : syracuseStep 2911541 = 272957) (by norm_num)
theorem B1941027 : Blo 1939435 1941027 := bstep (se 1 (by rfl) ⟨1455770, by rfl⟩ : syracuseStep 1941027 = 2911541) B2911541
theorem B4913237 : Blo 1939435 4913237 := bbase (se 8 (by rfl) ⟨28788, by rfl⟩ : syracuseStep 4913237 = 57577) (by norm_num)
theorem B3275491 : Blo 1939435 3275491 := bstep (se 1 (by rfl) ⟨2456618, by rfl⟩ : syracuseStep 3275491 = 4913237) B4913237
theorem B4367321 : Blo 1939435 4367321 := bstep (se 2 (by rfl) ⟨1637745, by rfl⟩ : syracuseStep 4367321 = 3275491) B3275491
theorem B2911547 : Blo 1939435 2911547 := bstep (se 1 (by rfl) ⟨2183660, by rfl⟩ : syracuseStep 2911547 = 4367321) B4367321
theorem B1941031 : Blo 1939435 1941031 := bstep (se 1 (by rfl) ⟨1455773, by rfl⟩ : syracuseStep 1941031 = 2911547) B2911547
theorem B2183665 : Blo 1939435 2183665 := bbase (se 2 (by rfl) ⟨818874, by rfl⟩ : syracuseStep 2183665 = 1637749) (by norm_num)
theorem B2911553 : Blo 1939435 2911553 := bstep (se 2 (by rfl) ⟨1091832, by rfl⟩ : syracuseStep 2911553 = 2183665) B2183665
theorem B1941035 : Blo 1939435 1941035 := bstep (se 1 (by rfl) ⟨1455776, by rfl⟩ : syracuseStep 1941035 = 2911553) B2911553
theorem B4663757 : Blo 1939435 4663757 := bbase (se 3 (by rfl) ⟨874454, by rfl⟩ : syracuseStep 4663757 = 1748909) (by norm_num)
theorem B12436685 : Blo 1939435 12436685 := bstep (se 3 (by rfl) ⟨2331878, by rfl⟩ : syracuseStep 12436685 = 4663757) B4663757
theorem B8291123 : Blo 1939435 8291123 := bstep (se 1 (by rfl) ⟨6218342, by rfl⟩ : syracuseStep 8291123 = 12436685) B12436685
theorem B5527415 : Blo 1939435 5527415 := bstep (se 1 (by rfl) ⟨4145561, by rfl⟩ : syracuseStep 5527415 = 8291123) B8291123
theorem B3684943 : Blo 1939435 3684943 := bstep (se 1 (by rfl) ⟨2763707, by rfl⟩ : syracuseStep 3684943 = 5527415) B5527415
theorem B4913257 : Blo 1939435 4913257 := bstep (se 2 (by rfl) ⟨1842471, by rfl⟩ : syracuseStep 4913257 = 3684943) B3684943
theorem B6551009 : Blo 1939435 6551009 := bstep (se 2 (by rfl) ⟨2456628, by rfl⟩ : syracuseStep 6551009 = 4913257) B4913257
theorem B4367339 : Blo 1939435 4367339 := bstep (se 1 (by rfl) ⟨3275504, by rfl⟩ : syracuseStep 4367339 = 6551009) B6551009
theorem B2911559 : Blo 1939435 2911559 := bstep (se 1 (by rfl) ⟨2183669, by rfl⟩ : syracuseStep 2911559 = 4367339) B4367339
theorem B1941039 : Blo 1939435 1941039 := bstep (se 1 (by rfl) ⟨1455779, by rfl⟩ : syracuseStep 1941039 = 2911559) B2911559
theorem B2911565 : Blo 1939435 2911565 := bbase (se 3 (by rfl) ⟨545918, by rfl⟩ : syracuseStep 2911565 = 1091837) (by norm_num)
theorem B1941043 : Blo 1939435 1941043 := bstep (se 1 (by rfl) ⟨1455782, by rfl⟩ : syracuseStep 1941043 = 2911565) B2911565
theorem B4367357 : Blo 1939435 4367357 := bbase (se 3 (by rfl) ⟨818879, by rfl⟩ : syracuseStep 4367357 = 1637759) (by norm_num)
theorem B2911571 : Blo 1939435 2911571 := bstep (se 1 (by rfl) ⟨2183678, by rfl⟩ : syracuseStep 2911571 = 4367357) B4367357
theorem B1941047 : Blo 1939435 1941047 := bstep (se 1 (by rfl) ⟨1455785, by rfl⟩ : syracuseStep 1941047 = 2911571) B2911571
theorem B3275525 : Blo 1939435 3275525 := bbase (se 4 (by rfl) ⟨307080, by rfl⟩ : syracuseStep 3275525 = 614161) (by norm_num)
theorem B2183683 : Blo 1939435 2183683 := bstep (se 1 (by rfl) ⟨1637762, by rfl⟩ : syracuseStep 2183683 = 3275525) B3275525
theorem B2911577 : Blo 1939435 2911577 := bstep (se 2 (by rfl) ⟨1091841, by rfl⟩ : syracuseStep 2911577 = 2183683) B2183683
theorem B1941051 : Blo 1939435 1941051 := bstep (se 1 (by rfl) ⟨1455788, by rfl⟩ : syracuseStep 1941051 = 2911577) B2911577
theorem B14739893 : Blo 1939435 14739893 := bbase (se 5 (by rfl) ⟨690932, by rfl⟩ : syracuseStep 14739893 = 1381865) (by norm_num)
theorem B9826595 : Blo 1939435 9826595 := bstep (se 1 (by rfl) ⟨7369946, by rfl⟩ : syracuseStep 9826595 = 14739893) B14739893
theorem B6551063 : Blo 1939435 6551063 := bstep (se 1 (by rfl) ⟨4913297, by rfl⟩ : syracuseStep 6551063 = 9826595) B9826595
theorem B4367375 : Blo 1939435 4367375 := bstep (se 1 (by rfl) ⟨3275531, by rfl⟩ : syracuseStep 4367375 = 6551063) B6551063
theorem B2911583 : Blo 1939435 2911583 := bstep (se 1 (by rfl) ⟨2183687, by rfl⟩ : syracuseStep 2911583 = 4367375) B4367375
theorem B1941055 : Blo 1939435 1941055 := bstep (se 1 (by rfl) ⟨1455791, by rfl⟩ : syracuseStep 1941055 = 2911583) B2911583
theorem B2911589 : Blo 1939435 2911589 := bbase (se 4 (by rfl) ⟨272961, by rfl⟩ : syracuseStep 2911589 = 545923) (by norm_num)
theorem B1941059 : Blo 1939435 1941059 := bstep (se 1 (by rfl) ⟨1455794, by rfl⟩ : syracuseStep 1941059 = 2911589) B2911589
theorem B3684989 : Blo 1939435 3684989 := bbase (se 3 (by rfl) ⟨690935, by rfl⟩ : syracuseStep 3684989 = 1381871) (by norm_num)
theorem B2456659 : Blo 1939435 2456659 := bstep (se 1 (by rfl) ⟨1842494, by rfl⟩ : syracuseStep 2456659 = 3684989) B3684989
theorem B3275545 : Blo 1939435 3275545 := bstep (se 2 (by rfl) ⟨1228329, by rfl⟩ : syracuseStep 3275545 = 2456659) B2456659
theorem B4367393 : Blo 1939435 4367393 := bstep (se 2 (by rfl) ⟨1637772, by rfl⟩ : syracuseStep 4367393 = 3275545) B3275545
theorem B2911595 : Blo 1939435 2911595 := bstep (se 1 (by rfl) ⟨2183696, by rfl⟩ : syracuseStep 2911595 = 4367393) B4367393
theorem B1941063 : Blo 1939435 1941063 := bstep (se 1 (by rfl) ⟨1455797, by rfl⟩ : syracuseStep 1941063 = 2911595) B2911595
theorem B2183701 : Blo 1939435 2183701 := bbase (se 6 (by rfl) ⟨51180, by rfl⟩ : syracuseStep 2183701 = 102361) (by norm_num)
theorem B2911601 : Blo 1939435 2911601 := bstep (se 2 (by rfl) ⟨1091850, by rfl⟩ : syracuseStep 2911601 = 2183701) B2183701
theorem B1941067 : Blo 1939435 1941067 := bstep (se 1 (by rfl) ⟨1455800, by rfl⟩ : syracuseStep 1941067 = 2911601) B2911601
theorem B2456669 : Blo 1939435 2456669 := bbase (se 3 (by rfl) ⟨460625, by rfl⟩ : syracuseStep 2456669 = 921251) (by norm_num)
theorem B6551117 : Blo 1939435 6551117 := bstep (se 3 (by rfl) ⟨1228334, by rfl⟩ : syracuseStep 6551117 = 2456669) B2456669
theorem B4367411 : Blo 1939435 4367411 := bstep (se 1 (by rfl) ⟨3275558, by rfl⟩ : syracuseStep 4367411 = 6551117) B6551117
theorem B2911607 : Blo 1939435 2911607 := bstep (se 1 (by rfl) ⟨2183705, by rfl⟩ : syracuseStep 2911607 = 4367411) B4367411
theorem B1941071 : Blo 1939435 1941071 := bstep (se 1 (by rfl) ⟨1455803, by rfl⟩ : syracuseStep 1941071 = 2911607) B2911607
theorem B2911613 : Blo 1939435 2911613 := bbase (se 3 (by rfl) ⟨545927, by rfl⟩ : syracuseStep 2911613 = 1091855) (by norm_num)
theorem B1941075 : Blo 1939435 1941075 := bstep (se 1 (by rfl) ⟨1455806, by rfl⟩ : syracuseStep 1941075 = 2911613) B2911613
theorem B4367429 : Blo 1939435 4367429 := bbase (se 4 (by rfl) ⟨409446, by rfl⟩ : syracuseStep 4367429 = 818893) (by norm_num)
theorem B2911619 : Blo 1939435 2911619 := bstep (se 1 (by rfl) ⟨2183714, by rfl⟩ : syracuseStep 2911619 = 4367429) B4367429
theorem B1941079 : Blo 1939435 1941079 := bstep (se 1 (by rfl) ⟨1455809, by rfl⟩ : syracuseStep 1941079 = 2911619) B2911619
theorem B5527541 : Blo 1939435 5527541 := bbase (se 5 (by rfl) ⟨259103, by rfl⟩ : syracuseStep 5527541 = 518207) (by norm_num)
theorem B3685027 : Blo 1939435 3685027 := bstep (se 1 (by rfl) ⟨2763770, by rfl⟩ : syracuseStep 3685027 = 5527541) B5527541
theorem B4913369 : Blo 1939435 4913369 := bstep (se 2 (by rfl) ⟨1842513, by rfl⟩ : syracuseStep 4913369 = 3685027) B3685027
theorem B3275579 : Blo 1939435 3275579 := bstep (se 1 (by rfl) ⟨2456684, by rfl⟩ : syracuseStep 3275579 = 4913369) B4913369
theorem B2183719 : Blo 1939435 2183719 := bstep (se 1 (by rfl) ⟨1637789, by rfl⟩ : syracuseStep 2183719 = 3275579) B3275579
theorem B2911625 : Blo 1939435 2911625 := bstep (se 2 (by rfl) ⟨1091859, by rfl⟩ : syracuseStep 2911625 = 2183719) B2183719
theorem B1941083 : Blo 1939435 1941083 := bstep (se 1 (by rfl) ⟨1455812, by rfl⟩ : syracuseStep 1941083 = 2911625) B2911625
theorem B9826757 : Blo 1939435 9826757 := bbase (se 4 (by rfl) ⟨921258, by rfl⟩ : syracuseStep 9826757 = 1842517) (by norm_num)
theorem B6551171 : Blo 1939435 6551171 := bstep (se 1 (by rfl) ⟨4913378, by rfl⟩ : syracuseStep 6551171 = 9826757) B9826757
theorem B4367447 : Blo 1939435 4367447 := bstep (se 1 (by rfl) ⟨3275585, by rfl⟩ : syracuseStep 4367447 = 6551171) B6551171
theorem B2911631 : Blo 1939435 2911631 := bstep (se 1 (by rfl) ⟨2183723, by rfl⟩ : syracuseStep 2911631 = 4367447) B4367447
theorem B1941087 : Blo 1939435 1941087 := bstep (se 1 (by rfl) ⟨1455815, by rfl⟩ : syracuseStep 1941087 = 2911631) B2911631
theorem B2911637 : Blo 1939435 2911637 := bbase (se 6 (by rfl) ⟨68241, by rfl⟩ : syracuseStep 2911637 = 136483) (by norm_num)
theorem B1941091 : Blo 1939435 1941091 := bstep (se 1 (by rfl) ⟨1455818, by rfl⟩ : syracuseStep 1941091 = 2911637) B2911637
theorem B3109261 : Blo 1939435 3109261 := bbase (se 3 (by rfl) ⟨582986, by rfl⟩ : syracuseStep 3109261 = 1165973) (by norm_num)
theorem B4145681 : Blo 1939435 4145681 := bstep (se 2 (by rfl) ⟨1554630, by rfl⟩ : syracuseStep 4145681 = 3109261) B3109261
theorem B11055149 : Blo 1939435 11055149 := bstep (se 3 (by rfl) ⟨2072840, by rfl⟩ : syracuseStep 11055149 = 4145681) B4145681
theorem B7370099 : Blo 1939435 7370099 := bstep (se 1 (by rfl) ⟨5527574, by rfl⟩ : syracuseStep 7370099 = 11055149) B11055149
theorem B4913399 : Blo 1939435 4913399 := bstep (se 1 (by rfl) ⟨3685049, by rfl⟩ : syracuseStep 4913399 = 7370099) B7370099
theorem B3275599 : Blo 1939435 3275599 := bstep (se 1 (by rfl) ⟨2456699, by rfl⟩ : syracuseStep 3275599 = 4913399) B4913399
theorem B4367465 : Blo 1939435 4367465 := bstep (se 2 (by rfl) ⟨1637799, by rfl⟩ : syracuseStep 4367465 = 3275599) B3275599
theorem B2911643 : Blo 1939435 2911643 := bstep (se 1 (by rfl) ⟨2183732, by rfl⟩ : syracuseStep 2911643 = 4367465) B4367465
theorem B1941095 : Blo 1939435 1941095 := bstep (se 1 (by rfl) ⟨1455821, by rfl⟩ : syracuseStep 1941095 = 2911643) B2911643
theorem B2183737 : Blo 1939435 2183737 := bbase (se 2 (by rfl) ⟨818901, by rfl⟩ : syracuseStep 2183737 = 1637803) (by norm_num)
theorem B2911649 : Blo 1939435 2911649 := bstep (se 2 (by rfl) ⟨1091868, by rfl⟩ : syracuseStep 2911649 = 2183737) B2183737
theorem B1941099 : Blo 1939435 1941099 := bstep (se 1 (by rfl) ⟨1455824, by rfl⟩ : syracuseStep 1941099 = 2911649) B2911649
theorem B2072849 : Blo 1939435 2072849 := bbase (se 2 (by rfl) ⟨777318, by rfl⟩ : syracuseStep 2072849 = 1554637) (by norm_num)
theorem B5527597 : Blo 1939435 5527597 := bstep (se 3 (by rfl) ⟨1036424, by rfl⟩ : syracuseStep 5527597 = 2072849) B2072849
theorem B7370129 : Blo 1939435 7370129 := bstep (se 2 (by rfl) ⟨2763798, by rfl⟩ : syracuseStep 7370129 = 5527597) B5527597
theorem B4913419 : Blo 1939435 4913419 := bstep (se 1 (by rfl) ⟨3685064, by rfl⟩ : syracuseStep 4913419 = 7370129) B7370129
theorem B6551225 : Blo 1939435 6551225 := bstep (se 2 (by rfl) ⟨2456709, by rfl⟩ : syracuseStep 6551225 = 4913419) B4913419
theorem B4367483 : Blo 1939435 4367483 := bstep (se 1 (by rfl) ⟨3275612, by rfl⟩ : syracuseStep 4367483 = 6551225) B6551225
theorem B2911655 : Blo 1939435 2911655 := bstep (se 1 (by rfl) ⟨2183741, by rfl⟩ : syracuseStep 2911655 = 4367483) B4367483
theorem B1941103 : Blo 1939435 1941103 := bstep (se 1 (by rfl) ⟨1455827, by rfl⟩ : syracuseStep 1941103 = 2911655) B2911655
theorem B2911661 : Blo 1939435 2911661 := bbase (se 3 (by rfl) ⟨545936, by rfl⟩ : syracuseStep 2911661 = 1091873) (by norm_num)
theorem B1941107 : Blo 1939435 1941107 := bstep (se 1 (by rfl) ⟨1455830, by rfl⟩ : syracuseStep 1941107 = 2911661) B2911661
theorem B4367501 : Blo 1939435 4367501 := bbase (se 3 (by rfl) ⟨818906, by rfl⟩ : syracuseStep 4367501 = 1637813) (by norm_num)
theorem B2911667 : Blo 1939435 2911667 := bstep (se 1 (by rfl) ⟨2183750, by rfl⟩ : syracuseStep 2911667 = 4367501) B4367501
theorem B1941111 : Blo 1939435 1941111 := bstep (se 1 (by rfl) ⟨1455833, by rfl⟩ : syracuseStep 1941111 = 2911667) B2911667
theorem B2456725 : Blo 1939435 2456725 := bbase (se 6 (by rfl) ⟨57579, by rfl⟩ : syracuseStep 2456725 = 115159) (by norm_num)
theorem B3275633 : Blo 1939435 3275633 := bstep (se 2 (by rfl) ⟨1228362, by rfl⟩ : syracuseStep 3275633 = 2456725) B2456725
theorem B2183755 : Blo 1939435 2183755 := bstep (se 1 (by rfl) ⟨1637816, by rfl⟩ : syracuseStep 2183755 = 3275633) B3275633
theorem B2911673 : Blo 1939435 2911673 := bstep (se 2 (by rfl) ⟨1091877, by rfl⟩ : syracuseStep 2911673 = 2183755) B2183755
theorem B1941115 : Blo 1939435 1941115 := bstep (se 1 (by rfl) ⟨1455836, by rfl⟩ : syracuseStep 1941115 = 2911673) B2911673
theorem B14941493 : Blo 1939435 14941493 := bbase (se 5 (by rfl) ⟨700382, by rfl⟩ : syracuseStep 14941493 = 1400765) (by norm_num)
theorem B9960995 : Blo 1939435 9960995 := bstep (se 1 (by rfl) ⟨7470746, by rfl⟩ : syracuseStep 9960995 = 14941493) B14941493
theorem B6640663 : Blo 1939435 6640663 := bstep (se 1 (by rfl) ⟨4980497, by rfl⟩ : syracuseStep 6640663 = 9960995) B9960995
theorem B8854217 : Blo 1939435 8854217 := bstep (se 2 (by rfl) ⟨3320331, by rfl⟩ : syracuseStep 8854217 = 6640663) B6640663
theorem B5902811 : Blo 1939435 5902811 := bstep (se 1 (by rfl) ⟨4427108, by rfl⟩ : syracuseStep 5902811 = 8854217) B8854217
theorem B3935207 : Blo 1939435 3935207 := bstep (se 1 (by rfl) ⟨2951405, by rfl⟩ : syracuseStep 3935207 = 5902811) B5902811
theorem B2623471 : Blo 1939435 2623471 := bstep (se 1 (by rfl) ⟨1967603, by rfl⟩ : syracuseStep 2623471 = 3935207) B3935207
theorem B55967381 : Blo 1939435 55967381 := bstep (se 6 (by rfl) ⟨1311735, by rfl⟩ : syracuseStep 55967381 = 2623471) B2623471
theorem B37311587 : Blo 1939435 37311587 := bstep (se 1 (by rfl) ⟨27983690, by rfl⟩ : syracuseStep 37311587 = 55967381) B55967381
theorem B24874391 : Blo 1939435 24874391 := bstep (se 1 (by rfl) ⟨18655793, by rfl⟩ : syracuseStep 24874391 = 37311587) B37311587
theorem B16582927 : Blo 1939435 16582927 := bstep (se 1 (by rfl) ⟨12437195, by rfl⟩ : syracuseStep 16582927 = 24874391) B24874391
theorem B22110569 : Blo 1939435 22110569 := bstep (se 2 (by rfl) ⟨8291463, by rfl⟩ : syracuseStep 22110569 = 16582927) B16582927
theorem B14740379 : Blo 1939435 14740379 := bstep (se 1 (by rfl) ⟨11055284, by rfl⟩ : syracuseStep 14740379 = 22110569) B22110569
theorem B9826919 : Blo 1939435 9826919 := bstep (se 1 (by rfl) ⟨7370189, by rfl⟩ : syracuseStep 9826919 = 14740379) B14740379
theorem B6551279 : Blo 1939435 6551279 := bstep (se 1 (by rfl) ⟨4913459, by rfl⟩ : syracuseStep 6551279 = 9826919) B9826919
theorem B4367519 : Blo 1939435 4367519 := bstep (se 1 (by rfl) ⟨3275639, by rfl⟩ : syracuseStep 4367519 = 6551279) B6551279
theorem B2911679 : Blo 1939435 2911679 := bstep (se 1 (by rfl) ⟨2183759, by rfl⟩ : syracuseStep 2911679 = 4367519) B4367519
theorem B1941119 : Blo 1939435 1941119 := bstep (se 1 (by rfl) ⟨1455839, by rfl⟩ : syracuseStep 1941119 = 2911679) B2911679
theorem B2911685 : Blo 1939435 2911685 := bbase (se 4 (by rfl) ⟨272970, by rfl⟩ : syracuseStep 2911685 = 545941) (by norm_num)
theorem B1941123 : Blo 1939435 1941123 := bstep (se 1 (by rfl) ⟨1455842, by rfl⟩ : syracuseStep 1941123 = 2911685) B2911685
theorem B3275653 : Blo 1939435 3275653 := bbase (se 4 (by rfl) ⟨307092, by rfl⟩ : syracuseStep 3275653 = 614185) (by norm_num)
theorem B4367537 : Blo 1939435 4367537 := bstep (se 2 (by rfl) ⟨1637826, by rfl⟩ : syracuseStep 4367537 = 3275653) B3275653
theorem B2911691 : Blo 1939435 2911691 := bstep (se 1 (by rfl) ⟨2183768, by rfl⟩ : syracuseStep 2911691 = 4367537) B4367537
theorem B1941127 : Blo 1939435 1941127 := bstep (se 1 (by rfl) ⟨1455845, by rfl⟩ : syracuseStep 1941127 = 2911691) B2911691
theorem B2183773 : Blo 1939435 2183773 := bbase (se 3 (by rfl) ⟨409457, by rfl⟩ : syracuseStep 2183773 = 818915) (by norm_num)
theorem B2911697 : Blo 1939435 2911697 := bstep (se 2 (by rfl) ⟨1091886, by rfl⟩ : syracuseStep 2911697 = 2183773) B2183773
theorem B1941131 : Blo 1939435 1941131 := bstep (se 1 (by rfl) ⟨1455848, by rfl⟩ : syracuseStep 1941131 = 2911697) B2911697
theorem B6551333 : Blo 1939435 6551333 := bbase (se 4 (by rfl) ⟨614187, by rfl⟩ : syracuseStep 6551333 = 1228375) (by norm_num)
theorem B4367555 : Blo 1939435 4367555 := bstep (se 1 (by rfl) ⟨3275666, by rfl⟩ : syracuseStep 4367555 = 6551333) B6551333
theorem B2911703 : Blo 1939435 2911703 := bstep (se 1 (by rfl) ⟨2183777, by rfl⟩ : syracuseStep 2911703 = 4367555) B4367555
theorem B1941135 : Blo 1939435 1941135 := bstep (se 1 (by rfl) ⟨1455851, by rfl⟩ : syracuseStep 1941135 = 2911703) B2911703
theorem B2911709 : Blo 1939435 2911709 := bbase (se 3 (by rfl) ⟨545945, by rfl⟩ : syracuseStep 2911709 = 1091891) (by norm_num)
theorem B1941139 : Blo 1939435 1941139 := bstep (se 1 (by rfl) ⟨1455854, by rfl⟩ : syracuseStep 1941139 = 2911709) B2911709
theorem B4367573 : Blo 1939435 4367573 := bbase (se 7 (by rfl) ⟨51182, by rfl⟩ : syracuseStep 4367573 = 102365) (by norm_num)
theorem B2911715 : Blo 1939435 2911715 := bstep (se 1 (by rfl) ⟨2183786, by rfl⟩ : syracuseStep 2911715 = 4367573) B4367573
theorem B1941143 : Blo 1939435 1941143 := bstep (se 1 (by rfl) ⟨1455857, by rfl⟩ : syracuseStep 1941143 = 2911715) B2911715
theorem B3498013 : Blo 1939435 3498013 := bbase (se 3 (by rfl) ⟨655877, by rfl⟩ : syracuseStep 3498013 = 1311755) (by norm_num)
theorem B4664017 : Blo 1939435 4664017 := bstep (se 2 (by rfl) ⟨1749006, by rfl⟩ : syracuseStep 4664017 = 3498013) B3498013
theorem B6218689 : Blo 1939435 6218689 := bstep (se 2 (by rfl) ⟨2332008, by rfl⟩ : syracuseStep 6218689 = 4664017) B4664017
theorem B8291585 : Blo 1939435 8291585 := bstep (se 2 (by rfl) ⟨3109344, by rfl⟩ : syracuseStep 8291585 = 6218689) B6218689
theorem B5527723 : Blo 1939435 5527723 := bstep (se 1 (by rfl) ⟨4145792, by rfl⟩ : syracuseStep 5527723 = 8291585) B8291585
theorem B7370297 : Blo 1939435 7370297 := bstep (se 2 (by rfl) ⟨2763861, by rfl⟩ : syracuseStep 7370297 = 5527723) B5527723
theorem B4913531 : Blo 1939435 4913531 := bstep (se 1 (by rfl) ⟨3685148, by rfl⟩ : syracuseStep 4913531 = 7370297) B7370297
theorem B3275687 : Blo 1939435 3275687 := bstep (se 1 (by rfl) ⟨2456765, by rfl⟩ : syracuseStep 3275687 = 4913531) B4913531
theorem B2183791 : Blo 1939435 2183791 := bstep (se 1 (by rfl) ⟨1637843, by rfl⟩ : syracuseStep 2183791 = 3275687) B3275687
theorem B2911721 : Blo 1939435 2911721 := bstep (se 2 (by rfl) ⟨1091895, by rfl⟩ : syracuseStep 2911721 = 2183791) B2183791
theorem B1941147 : Blo 1939435 1941147 := bstep (se 1 (by rfl) ⟨1455860, by rfl⟩ : syracuseStep 1941147 = 2911721) B2911721
theorem B5247029 : Blo 1939435 5247029 := bbase (se 5 (by rfl) ⟨245954, by rfl⟩ : syracuseStep 5247029 = 491909) (by norm_num)
theorem B13992077 : Blo 1939435 13992077 := bstep (se 3 (by rfl) ⟨2623514, by rfl⟩ : syracuseStep 13992077 = 5247029) B5247029
theorem B9328051 : Blo 1939435 9328051 := bstep (se 1 (by rfl) ⟨6996038, by rfl⟩ : syracuseStep 9328051 = 13992077) B13992077
theorem B12437401 : Blo 1939435 12437401 := bstep (se 2 (by rfl) ⟨4664025, by rfl⟩ : syracuseStep 12437401 = 9328051) B9328051
theorem B16583201 : Blo 1939435 16583201 := bstep (se 2 (by rfl) ⟨6218700, by rfl⟩ : syracuseStep 16583201 = 12437401) B12437401
theorem B11055467 : Blo 1939435 11055467 := bstep (se 1 (by rfl) ⟨8291600, by rfl⟩ : syracuseStep 11055467 = 16583201) B16583201
theorem B7370311 : Blo 1939435 7370311 := bstep (se 1 (by rfl) ⟨5527733, by rfl⟩ : syracuseStep 7370311 = 11055467) B11055467
theorem B9827081 : Blo 1939435 9827081 := bstep (se 2 (by rfl) ⟨3685155, by rfl⟩ : syracuseStep 9827081 = 7370311) B7370311
theorem B6551387 : Blo 1939435 6551387 := bstep (se 1 (by rfl) ⟨4913540, by rfl⟩ : syracuseStep 6551387 = 9827081) B9827081
theorem B4367591 : Blo 1939435 4367591 := bstep (se 1 (by rfl) ⟨3275693, by rfl⟩ : syracuseStep 4367591 = 6551387) B6551387
theorem B2911727 : Blo 1939435 2911727 := bstep (se 1 (by rfl) ⟨2183795, by rfl⟩ : syracuseStep 2911727 = 4367591) B4367591
theorem B1941151 : Blo 1939435 1941151 := bstep (se 1 (by rfl) ⟨1455863, by rfl⟩ : syracuseStep 1941151 = 2911727) B2911727
theorem B2911733 : Blo 1939435 2911733 := bbase (se 5 (by rfl) ⟨136487, by rfl⟩ : syracuseStep 2911733 = 272975) (by norm_num)
theorem B1941155 : Blo 1939435 1941155 := bstep (se 1 (by rfl) ⟨1455866, by rfl⟩ : syracuseStep 1941155 = 2911733) B2911733
theorem B2072909 : Blo 1939435 2072909 := bbase (se 3 (by rfl) ⟨388670, by rfl⟩ : syracuseStep 2072909 = 777341) (by norm_num)
theorem B5527757 : Blo 1939435 5527757 := bstep (se 3 (by rfl) ⟨1036454, by rfl⟩ : syracuseStep 5527757 = 2072909) B2072909
theorem B3685171 : Blo 1939435 3685171 := bstep (se 1 (by rfl) ⟨2763878, by rfl⟩ : syracuseStep 3685171 = 5527757) B5527757
theorem B4913561 : Blo 1939435 4913561 := bstep (se 2 (by rfl) ⟨1842585, by rfl⟩ : syracuseStep 4913561 = 3685171) B3685171
theorem B3275707 : Blo 1939435 3275707 := bstep (se 1 (by rfl) ⟨2456780, by rfl⟩ : syracuseStep 3275707 = 4913561) B4913561
theorem B4367609 : Blo 1939435 4367609 := bstep (se 2 (by rfl) ⟨1637853, by rfl⟩ : syracuseStep 4367609 = 3275707) B3275707
theorem B2911739 : Blo 1939435 2911739 := bstep (se 1 (by rfl) ⟨2183804, by rfl⟩ : syracuseStep 2911739 = 4367609) B4367609
theorem B1941159 : Blo 1939435 1941159 := bstep (se 1 (by rfl) ⟨1455869, by rfl⟩ : syracuseStep 1941159 = 2911739) B2911739
theorem B2183809 : Blo 1939435 2183809 := bbase (se 2 (by rfl) ⟨818928, by rfl⟩ : syracuseStep 2183809 = 1637857) (by norm_num)
theorem B2911745 : Blo 1939435 2911745 := bstep (se 2 (by rfl) ⟨1091904, by rfl⟩ : syracuseStep 2911745 = 2183809) B2183809
theorem B1941163 : Blo 1939435 1941163 := bstep (se 1 (by rfl) ⟨1455872, by rfl⟩ : syracuseStep 1941163 = 2911745) B2911745
theorem B4913581 : Blo 1939435 4913581 := bbase (se 3 (by rfl) ⟨921296, by rfl⟩ : syracuseStep 4913581 = 1842593) (by norm_num)
theorem B6551441 : Blo 1939435 6551441 := bstep (se 2 (by rfl) ⟨2456790, by rfl⟩ : syracuseStep 6551441 = 4913581) B4913581
theorem B4367627 : Blo 1939435 4367627 := bstep (se 1 (by rfl) ⟨3275720, by rfl⟩ : syracuseStep 4367627 = 6551441) B6551441
theorem B2911751 : Blo 1939435 2911751 := bstep (se 1 (by rfl) ⟨2183813, by rfl⟩ : syracuseStep 2911751 = 4367627) B4367627
theorem B1941167 : Blo 1939435 1941167 := bstep (se 1 (by rfl) ⟨1455875, by rfl⟩ : syracuseStep 1941167 = 2911751) B2911751
theorem B2911757 : Blo 1939435 2911757 := bbase (se 3 (by rfl) ⟨545954, by rfl⟩ : syracuseStep 2911757 = 1091909) (by norm_num)
theorem B1941171 : Blo 1939435 1941171 := bstep (se 1 (by rfl) ⟨1455878, by rfl⟩ : syracuseStep 1941171 = 2911757) B2911757
theorem B4367645 : Blo 1939435 4367645 := bbase (se 3 (by rfl) ⟨818933, by rfl⟩ : syracuseStep 4367645 = 1637867) (by norm_num)
theorem B2911763 : Blo 1939435 2911763 := bstep (se 1 (by rfl) ⟨2183822, by rfl⟩ : syracuseStep 2911763 = 4367645) B4367645
theorem B1941175 : Blo 1939435 1941175 := bstep (se 1 (by rfl) ⟨1455881, by rfl⟩ : syracuseStep 1941175 = 2911763) B2911763
theorem B3275741 : Blo 1939435 3275741 := bbase (se 3 (by rfl) ⟨614201, by rfl⟩ : syracuseStep 3275741 = 1228403) (by norm_num)
theorem B2183827 : Blo 1939435 2183827 := bstep (se 1 (by rfl) ⟨1637870, by rfl⟩ : syracuseStep 2183827 = 3275741) B3275741
theorem B2911769 : Blo 1939435 2911769 := bstep (se 2 (by rfl) ⟨1091913, by rfl⟩ : syracuseStep 2911769 = 2183827) B2183827
theorem B1941179 : Blo 1939435 1941179 := bstep (se 1 (by rfl) ⟨1455884, by rfl⟩ : syracuseStep 1941179 = 2911769) B2911769
theorem B3498077 : Blo 1939435 3498077 := bbase (se 3 (by rfl) ⟨655889, by rfl⟩ : syracuseStep 3498077 = 1311779) (by norm_num)
theorem B9328205 : Blo 1939435 9328205 := bstep (se 3 (by rfl) ⟨1749038, by rfl⟩ : syracuseStep 9328205 = 3498077) B3498077
theorem B6218803 : Blo 1939435 6218803 := bstep (se 1 (by rfl) ⟨4664102, by rfl⟩ : syracuseStep 6218803 = 9328205) B9328205
theorem B8291737 : Blo 1939435 8291737 := bstep (se 2 (by rfl) ⟨3109401, by rfl⟩ : syracuseStep 8291737 = 6218803) B6218803
theorem B11055649 : Blo 1939435 11055649 := bstep (se 2 (by rfl) ⟨4145868, by rfl⟩ : syracuseStep 11055649 = 8291737) B8291737
theorem B14740865 : Blo 1939435 14740865 := bstep (se 2 (by rfl) ⟨5527824, by rfl⟩ : syracuseStep 14740865 = 11055649) B11055649
theorem B9827243 : Blo 1939435 9827243 := bstep (se 1 (by rfl) ⟨7370432, by rfl⟩ : syracuseStep 9827243 = 14740865) B14740865
theorem B6551495 : Blo 1939435 6551495 := bstep (se 1 (by rfl) ⟨4913621, by rfl⟩ : syracuseStep 6551495 = 9827243) B9827243
theorem B4367663 : Blo 1939435 4367663 := bstep (se 1 (by rfl) ⟨3275747, by rfl⟩ : syracuseStep 4367663 = 6551495) B6551495
theorem B2911775 : Blo 1939435 2911775 := bstep (se 1 (by rfl) ⟨2183831, by rfl⟩ : syracuseStep 2911775 = 4367663) B4367663
theorem B1941183 : Blo 1939435 1941183 := bstep (se 1 (by rfl) ⟨1455887, by rfl⟩ : syracuseStep 1941183 = 2911775) B2911775
theorem B2911781 : Blo 1939435 2911781 := bbase (se 4 (by rfl) ⟨272979, by rfl⟩ : syracuseStep 2911781 = 545959) (by norm_num)
theorem B1941187 : Blo 1939435 1941187 := bstep (se 1 (by rfl) ⟨1455890, by rfl⟩ : syracuseStep 1941187 = 2911781) B2911781
theorem B2456821 : Blo 1939435 2456821 := bbase (se 5 (by rfl) ⟨115163, by rfl⟩ : syracuseStep 2456821 = 230327) (by norm_num)
theorem B3275761 : Blo 1939435 3275761 := bstep (se 2 (by rfl) ⟨1228410, by rfl⟩ : syracuseStep 3275761 = 2456821) B2456821
theorem B4367681 : Blo 1939435 4367681 := bstep (se 2 (by rfl) ⟨1637880, by rfl⟩ : syracuseStep 4367681 = 3275761) B3275761
theorem B2911787 : Blo 1939435 2911787 := bstep (se 1 (by rfl) ⟨2183840, by rfl⟩ : syracuseStep 2911787 = 4367681) B4367681
theorem B1941191 : Blo 1939435 1941191 := bstep (se 1 (by rfl) ⟨1455893, by rfl⟩ : syracuseStep 1941191 = 2911787) B2911787
theorem B2183845 : Blo 1939435 2183845 := bbase (se 4 (by rfl) ⟨204735, by rfl⟩ : syracuseStep 2183845 = 409471) (by norm_num)
theorem B2911793 : Blo 1939435 2911793 := bstep (se 2 (by rfl) ⟨1091922, by rfl⟩ : syracuseStep 2911793 = 2183845) B2183845
theorem B1941195 : Blo 1939435 1941195 := bstep (se 1 (by rfl) ⟨1455896, by rfl⟩ : syracuseStep 1941195 = 2911793) B2911793
theorem B2105633 : Blo 1939435 2105633 := bbase (se 2 (by rfl) ⟨789612, by rfl⟩ : syracuseStep 2105633 = 1579225) (by norm_num)
theorem B5615021 : Blo 1939435 5615021 := bstep (se 3 (by rfl) ⟨1052816, by rfl⟩ : syracuseStep 5615021 = 2105633) B2105633
theorem B3743347 : Blo 1939435 3743347 := bstep (se 1 (by rfl) ⟨2807510, by rfl⟩ : syracuseStep 3743347 = 5615021) B5615021
theorem B4991129 : Blo 1939435 4991129 := bstep (se 2 (by rfl) ⟨1871673, by rfl⟩ : syracuseStep 4991129 = 3743347) B3743347
theorem B3327419 : Blo 1939435 3327419 := bstep (se 1 (by rfl) ⟨2495564, by rfl⟩ : syracuseStep 3327419 = 4991129) B4991129
theorem B2218279 : Blo 1939435 2218279 := bstep (se 1 (by rfl) ⟨1663709, by rfl⟩ : syracuseStep 2218279 = 3327419) B3327419
theorem B2957705 : Blo 1939435 2957705 := bstep (se 2 (by rfl) ⟨1109139, by rfl⟩ : syracuseStep 2957705 = 2218279) B2218279
theorem B1971803 : Blo 1939435 1971803 := bstep (se 1 (by rfl) ⟨1478852, by rfl⟩ : syracuseStep 1971803 = 2957705) B2957705
theorem B5258141 : Blo 1939435 5258141 := bstep (se 3 (by rfl) ⟨985901, by rfl⟩ : syracuseStep 5258141 = 1971803) B1971803
theorem B3505427 : Blo 1939435 3505427 := bstep (se 1 (by rfl) ⟨2629070, by rfl⟩ : syracuseStep 3505427 = 5258141) B5258141
theorem B2336951 : Blo 1939435 2336951 := bstep (se 1 (by rfl) ⟨1752713, by rfl⟩ : syracuseStep 2336951 = 3505427) B3505427
theorem B6231869 : Blo 1939435 6231869 := bstep (se 3 (by rfl) ⟨1168475, by rfl⟩ : syracuseStep 6231869 = 2336951) B2336951
theorem B4154579 : Blo 1939435 4154579 := bstep (se 1 (by rfl) ⟨3115934, by rfl⟩ : syracuseStep 4154579 = 6231869) B6231869
theorem B2769719 : Blo 1939435 2769719 := bstep (se 1 (by rfl) ⟨2077289, by rfl⟩ : syracuseStep 2769719 = 4154579) B4154579
theorem B7385917 : Blo 1939435 7385917 := bstep (se 3 (by rfl) ⟨1384859, by rfl⟩ : syracuseStep 7385917 = 2769719) B2769719
theorem B9847889 : Blo 1939435 9847889 := bstep (se 2 (by rfl) ⟨3692958, by rfl⟩ : syracuseStep 9847889 = 7385917) B7385917
theorem B6565259 : Blo 1939435 6565259 := bstep (se 1 (by rfl) ⟨4923944, by rfl⟩ : syracuseStep 6565259 = 9847889) B9847889
theorem B17507357 : Blo 1939435 17507357 := bstep (se 3 (by rfl) ⟨3282629, by rfl⟩ : syracuseStep 17507357 = 6565259) B6565259
theorem B11671571 : Blo 1939435 11671571 := bstep (se 1 (by rfl) ⟨8753678, by rfl⟩ : syracuseStep 11671571 = 17507357) B17507357
theorem B31124189 : Blo 1939435 31124189 := bstep (se 3 (by rfl) ⟨5835785, by rfl⟩ : syracuseStep 31124189 = 11671571) B11671571
theorem B20749459 : Blo 1939435 20749459 := bstep (se 1 (by rfl) ⟨15562094, by rfl⟩ : syracuseStep 20749459 = 31124189) B31124189
theorem B27665945 : Blo 1939435 27665945 := bstep (se 2 (by rfl) ⟨10374729, by rfl⟩ : syracuseStep 27665945 = 20749459) B20749459
theorem B18443963 : Blo 1939435 18443963 := bstep (se 1 (by rfl) ⟨13832972, by rfl⟩ : syracuseStep 18443963 = 27665945) B27665945
theorem B12295975 : Blo 1939435 12295975 := bstep (se 1 (by rfl) ⟨9221981, by rfl⟩ : syracuseStep 12295975 = 18443963) B18443963
theorem B16394633 : Blo 1939435 16394633 := bstep (se 2 (by rfl) ⟨6147987, by rfl⟩ : syracuseStep 16394633 = 12295975) B12295975
theorem B10929755 : Blo 1939435 10929755 := bstep (se 1 (by rfl) ⟨8197316, by rfl⟩ : syracuseStep 10929755 = 16394633) B16394633
theorem B29146013 : Blo 1939435 29146013 := bstep (se 3 (by rfl) ⟨5464877, by rfl⟩ : syracuseStep 29146013 = 10929755) B10929755
theorem B19430675 : Blo 1939435 19430675 := bstep (se 1 (by rfl) ⟨14573006, by rfl⟩ : syracuseStep 19430675 = 29146013) B29146013
theorem B12953783 : Blo 1939435 12953783 := bstep (se 1 (by rfl) ⟨9715337, by rfl⟩ : syracuseStep 12953783 = 19430675) B19430675
theorem B8635855 : Blo 1939435 8635855 := bstep (se 1 (by rfl) ⟨6476891, by rfl⟩ : syracuseStep 8635855 = 12953783) B12953783
theorem B11514473 : Blo 1939435 11514473 := bstep (se 2 (by rfl) ⟨4317927, by rfl⟩ : syracuseStep 11514473 = 8635855) B8635855
theorem B7676315 : Blo 1939435 7676315 := bstep (se 1 (by rfl) ⟨5757236, by rfl⟩ : syracuseStep 7676315 = 11514473) B11514473
theorem B5117543 : Blo 1939435 5117543 := bstep (se 1 (by rfl) ⟨3838157, by rfl⟩ : syracuseStep 5117543 = 7676315) B7676315
theorem B3411695 : Blo 1939435 3411695 := bstep (se 1 (by rfl) ⟨2558771, by rfl⟩ : syracuseStep 3411695 = 5117543) B5117543
theorem B2274463 : Blo 1939435 2274463 := bstep (se 1 (by rfl) ⟨1705847, by rfl⟩ : syracuseStep 2274463 = 3411695) B3411695
theorem B12130469 : Blo 1939435 12130469 := bstep (se 4 (by rfl) ⟨1137231, by rfl⟩ : syracuseStep 12130469 = 2274463) B2274463
theorem B8086979 : Blo 1939435 8086979 := bstep (se 1 (by rfl) ⟨6065234, by rfl⟩ : syracuseStep 8086979 = 12130469) B12130469
theorem B21565277 : Blo 1939435 21565277 := bstep (se 3 (by rfl) ⟨4043489, by rfl⟩ : syracuseStep 21565277 = 8086979) B8086979
theorem B14376851 : Blo 1939435 14376851 := bstep (se 1 (by rfl) ⟨10782638, by rfl⟩ : syracuseStep 14376851 = 21565277) B21565277
theorem B9584567 : Blo 1939435 9584567 := bstep (se 1 (by rfl) ⟨7188425, by rfl⟩ : syracuseStep 9584567 = 14376851) B14376851
theorem B6389711 : Blo 1939435 6389711 := bstep (se 1 (by rfl) ⟨4792283, by rfl⟩ : syracuseStep 6389711 = 9584567) B9584567
theorem B4259807 : Blo 1939435 4259807 := bstep (se 1 (by rfl) ⟨3194855, by rfl⟩ : syracuseStep 4259807 = 6389711) B6389711
theorem B2839871 : Blo 1939435 2839871 := bstep (se 1 (by rfl) ⟨2129903, by rfl⟩ : syracuseStep 2839871 = 4259807) B4259807
theorem B7572989 : Blo 1939435 7572989 := bstep (se 3 (by rfl) ⟨1419935, by rfl⟩ : syracuseStep 7572989 = 2839871) B2839871
theorem B5048659 : Blo 1939435 5048659 := bstep (se 1 (by rfl) ⟨3786494, by rfl⟩ : syracuseStep 5048659 = 7572989) B7572989
theorem B6731545 : Blo 1939435 6731545 := bstep (se 2 (by rfl) ⟨2524329, by rfl⟩ : syracuseStep 6731545 = 5048659) B5048659
theorem B8975393 : Blo 1939435 8975393 := bstep (se 2 (by rfl) ⟨3365772, by rfl⟩ : syracuseStep 8975393 = 6731545) B6731545
theorem B5983595 : Blo 1939435 5983595 := bstep (se 1 (by rfl) ⟨4487696, by rfl⟩ : syracuseStep 5983595 = 8975393) B8975393
theorem B3989063 : Blo 1939435 3989063 := bstep (se 1 (by rfl) ⟨2991797, by rfl⟩ : syracuseStep 3989063 = 5983595) B5983595
theorem B2659375 : Blo 1939435 2659375 := bstep (se 1 (by rfl) ⟨1994531, by rfl⟩ : syracuseStep 2659375 = 3989063) B3989063
theorem B14183333 : Blo 1939435 14183333 := bstep (se 4 (by rfl) ⟨1329687, by rfl⟩ : syracuseStep 14183333 = 2659375) B2659375
theorem B9455555 : Blo 1939435 9455555 := bstep (se 1 (by rfl) ⟨7091666, by rfl⟩ : syracuseStep 9455555 = 14183333) B14183333
theorem B6303703 : Blo 1939435 6303703 := bstep (se 1 (by rfl) ⟨4727777, by rfl⟩ : syracuseStep 6303703 = 9455555) B9455555
theorem B8404937 : Blo 1939435 8404937 := bstep (se 2 (by rfl) ⟨3151851, by rfl⟩ : syracuseStep 8404937 = 6303703) B6303703
theorem B5603291 : Blo 1939435 5603291 := bstep (se 1 (by rfl) ⟨4202468, by rfl⟩ : syracuseStep 5603291 = 8404937) B8404937
theorem B3735527 : Blo 1939435 3735527 := bstep (se 1 (by rfl) ⟨2801645, by rfl⟩ : syracuseStep 3735527 = 5603291) B5603291
theorem B39845621 : Blo 1939435 39845621 := bstep (se 5 (by rfl) ⟨1867763, by rfl⟩ : syracuseStep 39845621 = 3735527) B3735527
theorem B26563747 : Blo 1939435 26563747 := bstep (se 1 (by rfl) ⟨19922810, by rfl⟩ : syracuseStep 26563747 = 39845621) B39845621
theorem B35418329 : Blo 1939435 35418329 := bstep (se 2 (by rfl) ⟨13281873, by rfl⟩ : syracuseStep 35418329 = 26563747) B26563747
theorem B23612219 : Blo 1939435 23612219 := bstep (se 1 (by rfl) ⟨17709164, by rfl⟩ : syracuseStep 23612219 = 35418329) B35418329
theorem B15741479 : Blo 1939435 15741479 := bstep (se 1 (by rfl) ⟨11806109, by rfl⟩ : syracuseStep 15741479 = 23612219) B23612219
theorem B41977277 : Blo 1939435 41977277 := bstep (se 3 (by rfl) ⟨7870739, by rfl⟩ : syracuseStep 41977277 = 15741479) B15741479
theorem B27984851 : Blo 1939435 27984851 := bstep (se 1 (by rfl) ⟨20988638, by rfl⟩ : syracuseStep 27984851 = 41977277) B41977277
theorem B18656567 : Blo 1939435 18656567 := bstep (se 1 (by rfl) ⟨13992425, by rfl⟩ : syracuseStep 18656567 = 27984851) B27984851
theorem B12437711 : Blo 1939435 12437711 := bstep (se 1 (by rfl) ⟨9328283, by rfl⟩ : syracuseStep 12437711 = 18656567) B18656567
theorem B8291807 : Blo 1939435 8291807 := bstep (se 1 (by rfl) ⟨6218855, by rfl⟩ : syracuseStep 8291807 = 12437711) B12437711
theorem B5527871 : Blo 1939435 5527871 := bstep (se 1 (by rfl) ⟨4145903, by rfl⟩ : syracuseStep 5527871 = 8291807) B8291807
theorem B3685247 : Blo 1939435 3685247 := bstep (se 1 (by rfl) ⟨2763935, by rfl⟩ : syracuseStep 3685247 = 5527871) B5527871
theorem B2456831 : Blo 1939435 2456831 := bstep (se 1 (by rfl) ⟨1842623, by rfl⟩ : syracuseStep 2456831 = 3685247) B3685247
theorem B6551549 : Blo 1939435 6551549 := bstep (se 3 (by rfl) ⟨1228415, by rfl⟩ : syracuseStep 6551549 = 2456831) B2456831
theorem B4367699 : Blo 1939435 4367699 := bstep (se 1 (by rfl) ⟨3275774, by rfl⟩ : syracuseStep 4367699 = 6551549) B6551549
theorem B2911799 : Blo 1939435 2911799 := bstep (se 1 (by rfl) ⟨2183849, by rfl⟩ : syracuseStep 2911799 = 4367699) B4367699
theorem B1941199 : Blo 1939435 1941199 := bstep (se 1 (by rfl) ⟨1455899, by rfl⟩ : syracuseStep 1941199 = 2911799) B2911799
theorem B2911805 : Blo 1939435 2911805 := bbase (se 3 (by rfl) ⟨545963, by rfl⟩ : syracuseStep 2911805 = 1091927) (by norm_num)
theorem B1941203 : Blo 1939435 1941203 := bstep (se 1 (by rfl) ⟨1455902, by rfl⟩ : syracuseStep 1941203 = 2911805) B2911805
theorem B4367717 : Blo 1939435 4367717 := bbase (se 4 (by rfl) ⟨409473, by rfl⟩ : syracuseStep 4367717 = 818947) (by norm_num)
theorem B2911811 : Blo 1939435 2911811 := bstep (se 1 (by rfl) ⟨2183858, by rfl⟩ : syracuseStep 2911811 = 4367717) B4367717
theorem B1941207 : Blo 1939435 1941207 := bstep (se 1 (by rfl) ⟨1455905, by rfl⟩ : syracuseStep 1941207 = 2911811) B2911811
theorem B4913693 : Blo 1939435 4913693 := bbase (se 3 (by rfl) ⟨921317, by rfl⟩ : syracuseStep 4913693 = 1842635) (by norm_num)
theorem B3275795 : Blo 1939435 3275795 := bstep (se 1 (by rfl) ⟨2456846, by rfl⟩ : syracuseStep 3275795 = 4913693) B4913693
theorem B2183863 : Blo 1939435 2183863 := bstep (se 1 (by rfl) ⟨1637897, by rfl⟩ : syracuseStep 2183863 = 3275795) B3275795
theorem B2911817 : Blo 1939435 2911817 := bstep (se 2 (by rfl) ⟨1091931, by rfl⟩ : syracuseStep 2911817 = 2183863) B2183863
theorem B1941211 : Blo 1939435 1941211 := bstep (se 1 (by rfl) ⟨1455908, by rfl⟩ : syracuseStep 1941211 = 2911817) B2911817
theorem B3685277 : Blo 1939435 3685277 := bbase (se 3 (by rfl) ⟨690989, by rfl⟩ : syracuseStep 3685277 = 1381979) (by norm_num)
theorem B9827405 : Blo 1939435 9827405 := bstep (se 3 (by rfl) ⟨1842638, by rfl⟩ : syracuseStep 9827405 = 3685277) B3685277
theorem B6551603 : Blo 1939435 6551603 := bstep (se 1 (by rfl) ⟨4913702, by rfl⟩ : syracuseStep 6551603 = 9827405) B9827405
theorem B4367735 : Blo 1939435 4367735 := bstep (se 1 (by rfl) ⟨3275801, by rfl⟩ : syracuseStep 4367735 = 6551603) B6551603
theorem B2911823 : Blo 1939435 2911823 := bstep (se 1 (by rfl) ⟨2183867, by rfl⟩ : syracuseStep 2911823 = 4367735) B4367735
theorem B1941215 : Blo 1939435 1941215 := bstep (se 1 (by rfl) ⟨1455911, by rfl⟩ : syracuseStep 1941215 = 2911823) B2911823
theorem B2911829 : Blo 1939435 2911829 := bbase (se 8 (by rfl) ⟨17061, by rfl⟩ : syracuseStep 2911829 = 34123) (by norm_num)
theorem B1941219 : Blo 1939435 1941219 := bstep (se 1 (by rfl) ⟨1455914, by rfl⟩ : syracuseStep 1941219 = 2911829) B2911829
theorem B8291909 : Blo 1939435 8291909 := bbase (se 4 (by rfl) ⟨777366, by rfl⟩ : syracuseStep 8291909 = 1554733) (by norm_num)
theorem B5527939 : Blo 1939435 5527939 := bstep (se 1 (by rfl) ⟨4145954, by rfl⟩ : syracuseStep 5527939 = 8291909) B8291909
theorem B7370585 : Blo 1939435 7370585 := bstep (se 2 (by rfl) ⟨2763969, by rfl⟩ : syracuseStep 7370585 = 5527939) B5527939
theorem B4913723 : Blo 1939435 4913723 := bstep (se 1 (by rfl) ⟨3685292, by rfl⟩ : syracuseStep 4913723 = 7370585) B7370585
theorem B3275815 : Blo 1939435 3275815 := bstep (se 1 (by rfl) ⟨2456861, by rfl⟩ : syracuseStep 3275815 = 4913723) B4913723
theorem B4367753 : Blo 1939435 4367753 := bstep (se 2 (by rfl) ⟨1637907, by rfl⟩ : syracuseStep 4367753 = 3275815) B3275815
theorem B2911835 : Blo 1939435 2911835 := bstep (se 1 (by rfl) ⟨2183876, by rfl⟩ : syracuseStep 2911835 = 4367753) B4367753
theorem B1941223 : Blo 1939435 1941223 := bstep (se 1 (by rfl) ⟨1455917, by rfl⟩ : syracuseStep 1941223 = 2911835) B2911835
theorem B2183881 : Blo 1939435 2183881 := bbase (se 2 (by rfl) ⟨818955, by rfl⟩ : syracuseStep 2183881 = 1637911) (by norm_num)
theorem B2911841 : Blo 1939435 2911841 := bstep (se 2 (by rfl) ⟨1091940, by rfl⟩ : syracuseStep 2911841 = 2183881) B2183881
theorem B1941227 : Blo 1939435 1941227 := bstep (se 1 (by rfl) ⟨1455920, by rfl⟩ : syracuseStep 1941227 = 2911841) B2911841
theorem B2332109 : Blo 1939435 2332109 := bbase (se 3 (by rfl) ⟨437270, by rfl⟩ : syracuseStep 2332109 = 874541) (by norm_num)
theorem B6218957 : Blo 1939435 6218957 := bstep (se 3 (by rfl) ⟨1166054, by rfl⟩ : syracuseStep 6218957 = 2332109) B2332109
theorem B16583885 : Blo 1939435 16583885 := bstep (se 3 (by rfl) ⟨3109478, by rfl⟩ : syracuseStep 16583885 = 6218957) B6218957
theorem B11055923 : Blo 1939435 11055923 := bstep (se 1 (by rfl) ⟨8291942, by rfl⟩ : syracuseStep 11055923 = 16583885) B16583885
theorem B7370615 : Blo 1939435 7370615 := bstep (se 1 (by rfl) ⟨5527961, by rfl⟩ : syracuseStep 7370615 = 11055923) B11055923
theorem B4913743 : Blo 1939435 4913743 := bstep (se 1 (by rfl) ⟨3685307, by rfl⟩ : syracuseStep 4913743 = 7370615) B7370615
theorem B6551657 : Blo 1939435 6551657 := bstep (se 2 (by rfl) ⟨2456871, by rfl⟩ : syracuseStep 6551657 = 4913743) B4913743
theorem B4367771 : Blo 1939435 4367771 := bstep (se 1 (by rfl) ⟨3275828, by rfl⟩ : syracuseStep 4367771 = 6551657) B6551657
theorem B2911847 : Blo 1939435 2911847 := bstep (se 1 (by rfl) ⟨2183885, by rfl⟩ : syracuseStep 2911847 = 4367771) B4367771
theorem B1941231 : Blo 1939435 1941231 := bstep (se 1 (by rfl) ⟨1455923, by rfl⟩ : syracuseStep 1941231 = 2911847) B2911847
theorem B2911853 : Blo 1939435 2911853 := bbase (se 3 (by rfl) ⟨545972, by rfl⟩ : syracuseStep 2911853 = 1091945) (by norm_num)
theorem B1941235 : Blo 1939435 1941235 := bstep (se 1 (by rfl) ⟨1455926, by rfl⟩ : syracuseStep 1941235 = 2911853) B2911853
theorem B4367789 : Blo 1939435 4367789 := bbase (se 3 (by rfl) ⟨818960, by rfl⟩ : syracuseStep 4367789 = 1637921) (by norm_num)
theorem B2911859 : Blo 1939435 2911859 := bstep (se 1 (by rfl) ⟨2183894, by rfl⟩ : syracuseStep 2911859 = 4367789) B4367789
theorem B1941239 : Blo 1939435 1941239 := bstep (se 1 (by rfl) ⟨1455929, by rfl⟩ : syracuseStep 1941239 = 2911859) B2911859
theorem B3935461 : Blo 1939435 3935461 := bbase (se 4 (by rfl) ⟨368949, by rfl⟩ : syracuseStep 3935461 = 737899) (by norm_num)
theorem B5247281 : Blo 1939435 5247281 := bstep (se 2 (by rfl) ⟨1967730, by rfl⟩ : syracuseStep 5247281 = 3935461) B3935461
theorem B3498187 : Blo 1939435 3498187 := bstep (se 1 (by rfl) ⟨2623640, by rfl⟩ : syracuseStep 3498187 = 5247281) B5247281
theorem B4664249 : Blo 1939435 4664249 := bstep (se 2 (by rfl) ⟨1749093, by rfl⟩ : syracuseStep 4664249 = 3498187) B3498187
theorem B3109499 : Blo 1939435 3109499 := bstep (se 1 (by rfl) ⟨2332124, by rfl⟩ : syracuseStep 3109499 = 4664249) B4664249
theorem B2072999 : Blo 1939435 2072999 := bstep (se 1 (by rfl) ⟨1554749, by rfl⟩ : syracuseStep 2072999 = 3109499) B3109499
theorem B5527997 : Blo 1939435 5527997 := bstep (se 3 (by rfl) ⟨1036499, by rfl⟩ : syracuseStep 5527997 = 2072999) B2072999
theorem B3685331 : Blo 1939435 3685331 := bstep (se 1 (by rfl) ⟨2763998, by rfl⟩ : syracuseStep 3685331 = 5527997) B5527997
theorem B2456887 : Blo 1939435 2456887 := bstep (se 1 (by rfl) ⟨1842665, by rfl⟩ : syracuseStep 2456887 = 3685331) B3685331
theorem B3275849 : Blo 1939435 3275849 := bstep (se 2 (by rfl) ⟨1228443, by rfl⟩ : syracuseStep 3275849 = 2456887) B2456887
theorem B2183899 : Blo 1939435 2183899 := bstep (se 1 (by rfl) ⟨1637924, by rfl⟩ : syracuseStep 2183899 = 3275849) B3275849
theorem B2911865 : Blo 1939435 2911865 := bstep (se 2 (by rfl) ⟨1091949, by rfl⟩ : syracuseStep 2911865 = 2183899) B2183899
theorem B1941243 : Blo 1939435 1941243 := bstep (se 1 (by rfl) ⟨1455932, by rfl⟩ : syracuseStep 1941243 = 2911865) B2911865
theorem B2991869 : Blo 1939435 2991869 := bbase (se 3 (by rfl) ⟨560975, by rfl⟩ : syracuseStep 2991869 = 1121951) (by norm_num)
theorem B127653077 : Blo 1939435 127653077 := bstep (se 7 (by rfl) ⟨1495934, by rfl⟩ : syracuseStep 127653077 = 2991869) B2991869
theorem B85102051 : Blo 1939435 85102051 := bstep (se 1 (by rfl) ⟨63826538, by rfl⟩ : syracuseStep 85102051 = 127653077) B127653077
theorem B113469401 : Blo 1939435 113469401 := bstep (se 2 (by rfl) ⟨42551025, by rfl⟩ : syracuseStep 113469401 = 85102051) B85102051
theorem B75646267 : Blo 1939435 75646267 := bstep (se 1 (by rfl) ⟨56734700, by rfl⟩ : syracuseStep 75646267 = 113469401) B113469401
theorem B403446757 : Blo 1939435 403446757 := bstep (se 4 (by rfl) ⟨37823133, by rfl⟩ : syracuseStep 403446757 = 75646267) B75646267
theorem B537929009 : Blo 1939435 537929009 := bstep (se 2 (by rfl) ⟨201723378, by rfl⟩ : syracuseStep 537929009 = 403446757) B403446757
theorem B358619339 : Blo 1939435 358619339 := bstep (se 1 (by rfl) ⟨268964504, by rfl⟩ : syracuseStep 358619339 = 537929009) B537929009
theorem B956318237 : Blo 1939435 956318237 := bstep (se 3 (by rfl) ⟨179309669, by rfl⟩ : syracuseStep 956318237 = 358619339) B358619339
theorem B637545491 : Blo 1939435 637545491 := bstep (se 1 (by rfl) ⟨478159118, by rfl⟩ : syracuseStep 637545491 = 956318237) B956318237
theorem B425030327 : Blo 1939435 425030327 := bstep (se 1 (by rfl) ⟨318772745, by rfl⟩ : syracuseStep 425030327 = 637545491) B637545491
theorem B283353551 : Blo 1939435 283353551 := bstep (se 1 (by rfl) ⟨212515163, by rfl⟩ : syracuseStep 283353551 = 425030327) B425030327
theorem B188902367 : Blo 1939435 188902367 := bstep (se 1 (by rfl) ⟨141676775, by rfl⟩ : syracuseStep 188902367 = 283353551) B283353551
theorem B125934911 : Blo 1939435 125934911 := bstep (se 1 (by rfl) ⟨94451183, by rfl⟩ : syracuseStep 125934911 = 188902367) B188902367
theorem B83956607 : Blo 1939435 83956607 := bstep (se 1 (by rfl) ⟨62967455, by rfl⟩ : syracuseStep 83956607 = 125934911) B125934911
theorem B55971071 : Blo 1939435 55971071 := bstep (se 1 (by rfl) ⟨41978303, by rfl⟩ : syracuseStep 55971071 = 83956607) B83956607
theorem B37314047 : Blo 1939435 37314047 := bstep (se 1 (by rfl) ⟨27985535, by rfl⟩ : syracuseStep 37314047 = 55971071) B55971071
theorem B24876031 : Blo 1939435 24876031 := bstep (se 1 (by rfl) ⟨18657023, by rfl⟩ : syracuseStep 24876031 = 37314047) B37314047
theorem B33168041 : Blo 1939435 33168041 := bstep (se 2 (by rfl) ⟨12438015, by rfl⟩ : syracuseStep 33168041 = 24876031) B24876031
theorem B22112027 : Blo 1939435 22112027 := bstep (se 1 (by rfl) ⟨16584020, by rfl⟩ : syracuseStep 22112027 = 33168041) B33168041
theorem B14741351 : Blo 1939435 14741351 := bstep (se 1 (by rfl) ⟨11056013, by rfl⟩ : syracuseStep 14741351 = 22112027) B22112027
theorem B9827567 : Blo 1939435 9827567 := bstep (se 1 (by rfl) ⟨7370675, by rfl⟩ : syracuseStep 9827567 = 14741351) B14741351
theorem B6551711 : Blo 1939435 6551711 := bstep (se 1 (by rfl) ⟨4913783, by rfl⟩ : syracuseStep 6551711 = 9827567) B9827567
theorem B4367807 : Blo 1939435 4367807 := bstep (se 1 (by rfl) ⟨3275855, by rfl⟩ : syracuseStep 4367807 = 6551711) B6551711
theorem B2911871 : Blo 1939435 2911871 := bstep (se 1 (by rfl) ⟨2183903, by rfl⟩ : syracuseStep 2911871 = 4367807) B4367807
theorem B1941247 : Blo 1939435 1941247 := bstep (se 1 (by rfl) ⟨1455935, by rfl⟩ : syracuseStep 1941247 = 2911871) B2911871
theorem B2911877 : Blo 1939435 2911877 := bbase (se 4 (by rfl) ⟨272988, by rfl⟩ : syracuseStep 2911877 = 545977) (by norm_num)
theorem B1941251 : Blo 1939435 1941251 := bstep (se 1 (by rfl) ⟨1455938, by rfl⟩ : syracuseStep 1941251 = 2911877) B2911877
theorem B3275869 : Blo 1939435 3275869 := bbase (se 3 (by rfl) ⟨614225, by rfl⟩ : syracuseStep 3275869 = 1228451) (by norm_num)
theorem B4367825 : Blo 1939435 4367825 := bstep (se 2 (by rfl) ⟨1637934, by rfl⟩ : syracuseStep 4367825 = 3275869) B3275869
theorem B2911883 : Blo 1939435 2911883 := bstep (se 1 (by rfl) ⟨2183912, by rfl⟩ : syracuseStep 2911883 = 4367825) B4367825
theorem B1941255 : Blo 1939435 1941255 := bstep (se 1 (by rfl) ⟨1455941, by rfl⟩ : syracuseStep 1941255 = 2911883) B2911883
theorem B2183917 : Blo 1939435 2183917 := bbase (se 3 (by rfl) ⟨409484, by rfl⟩ : syracuseStep 2183917 = 818969) (by norm_num)
theorem B2911889 : Blo 1939435 2911889 := bstep (se 2 (by rfl) ⟨1091958, by rfl⟩ : syracuseStep 2911889 = 2183917) B2183917
theorem B1941259 : Blo 1939435 1941259 := bstep (se 1 (by rfl) ⟨1455944, by rfl⟩ : syracuseStep 1941259 = 2911889) B2911889
theorem B6551765 : Blo 1939435 6551765 := bbase (se 7 (by rfl) ⟨76778, by rfl⟩ : syracuseStep 6551765 = 153557) (by norm_num)
theorem B4367843 : Blo 1939435 4367843 := bstep (se 1 (by rfl) ⟨3275882, by rfl⟩ : syracuseStep 4367843 = 6551765) B6551765
theorem B2911895 : Blo 1939435 2911895 := bstep (se 1 (by rfl) ⟨2183921, by rfl⟩ : syracuseStep 2911895 = 4367843) B4367843
theorem B1941263 : Blo 1939435 1941263 := bstep (se 1 (by rfl) ⟨1455947, by rfl⟩ : syracuseStep 1941263 = 2911895) B2911895
theorem B2911901 : Blo 1939435 2911901 := bbase (se 3 (by rfl) ⟨545981, by rfl⟩ : syracuseStep 2911901 = 1091963) (by norm_num)
theorem B1941267 : Blo 1939435 1941267 := bstep (se 1 (by rfl) ⟨1455950, by rfl⟩ : syracuseStep 1941267 = 2911901) B2911901
theorem B4367861 : Blo 1939435 4367861 := bbase (se 5 (by rfl) ⟨204743, by rfl⟩ : syracuseStep 4367861 = 409487) (by norm_num)
theorem B2911907 : Blo 1939435 2911907 := bstep (se 1 (by rfl) ⟨2183930, by rfl⟩ : syracuseStep 2911907 = 4367861) B4367861
theorem B1941271 : Blo 1939435 1941271 := bstep (se 1 (by rfl) ⟨1455953, by rfl⟩ : syracuseStep 1941271 = 2911907) B2911907
theorem B7573285 : Blo 1939435 7573285 := bbase (se 4 (by rfl) ⟨709995, by rfl⟩ : syracuseStep 7573285 = 1419991) (by norm_num)
theorem B10097713 : Blo 1939435 10097713 := bstep (se 2 (by rfl) ⟨3786642, by rfl⟩ : syracuseStep 10097713 = 7573285) B7573285
theorem B13463617 : Blo 1939435 13463617 := bstep (se 2 (by rfl) ⟨5048856, by rfl⟩ : syracuseStep 13463617 = 10097713) B10097713
theorem B17951489 : Blo 1939435 17951489 := bstep (se 2 (by rfl) ⟨6731808, by rfl⟩ : syracuseStep 17951489 = 13463617) B13463617
theorem B11967659 : Blo 1939435 11967659 := bstep (se 1 (by rfl) ⟨8975744, by rfl⟩ : syracuseStep 11967659 = 17951489) B17951489
theorem B7978439 : Blo 1939435 7978439 := bstep (se 1 (by rfl) ⟨5983829, by rfl⟩ : syracuseStep 7978439 = 11967659) B11967659
theorem B5318959 : Blo 1939435 5318959 := bstep (se 1 (by rfl) ⟨3989219, by rfl⟩ : syracuseStep 5318959 = 7978439) B7978439
theorem B7091945 : Blo 1939435 7091945 := bstep (se 2 (by rfl) ⟨2659479, by rfl⟩ : syracuseStep 7091945 = 5318959) B5318959
theorem B4727963 : Blo 1939435 4727963 := bstep (se 1 (by rfl) ⟨3545972, by rfl⟩ : syracuseStep 4727963 = 7091945) B7091945
theorem B3151975 : Blo 1939435 3151975 := bstep (se 1 (by rfl) ⟨2363981, by rfl⟩ : syracuseStep 3151975 = 4727963) B4727963
theorem B4202633 : Blo 1939435 4202633 := bstep (se 2 (by rfl) ⟨1575987, by rfl⟩ : syracuseStep 4202633 = 3151975) B3151975
theorem B2801755 : Blo 1939435 2801755 := bstep (se 1 (by rfl) ⟨2101316, by rfl⟩ : syracuseStep 2801755 = 4202633) B4202633
theorem B14942693 : Blo 1939435 14942693 := bstep (se 4 (by rfl) ⟨1400877, by rfl⟩ : syracuseStep 14942693 = 2801755) B2801755
theorem B9961795 : Blo 1939435 9961795 := bstep (se 1 (by rfl) ⟨7471346, by rfl⟩ : syracuseStep 9961795 = 14942693) B14942693
theorem B13282393 : Blo 1939435 13282393 := bstep (se 2 (by rfl) ⟨4980897, by rfl⟩ : syracuseStep 13282393 = 9961795) B9961795
theorem B17709857 : Blo 1939435 17709857 := bstep (se 2 (by rfl) ⟨6641196, by rfl⟩ : syracuseStep 17709857 = 13282393) B13282393
theorem B11806571 : Blo 1939435 11806571 := bstep (se 1 (by rfl) ⟨8854928, by rfl⟩ : syracuseStep 11806571 = 17709857) B17709857
theorem B31484189 : Blo 1939435 31484189 := bstep (se 3 (by rfl) ⟨5903285, by rfl⟩ : syracuseStep 31484189 = 11806571) B11806571
theorem B20989459 : Blo 1939435 20989459 := bstep (se 1 (by rfl) ⟨15742094, by rfl⟩ : syracuseStep 20989459 = 31484189) B31484189
theorem B27985945 : Blo 1939435 27985945 := bstep (se 2 (by rfl) ⟨10494729, by rfl⟩ : syracuseStep 27985945 = 20989459) B20989459
theorem B37314593 : Blo 1939435 37314593 := bstep (se 2 (by rfl) ⟨13992972, by rfl⟩ : syracuseStep 37314593 = 27985945) B27985945
theorem B24876395 : Blo 1939435 24876395 := bstep (se 1 (by rfl) ⟨18657296, by rfl⟩ : syracuseStep 24876395 = 37314593) B37314593
theorem B16584263 : Blo 1939435 16584263 := bstep (se 1 (by rfl) ⟨12438197, by rfl⟩ : syracuseStep 16584263 = 24876395) B24876395
theorem B11056175 : Blo 1939435 11056175 := bstep (se 1 (by rfl) ⟨8292131, by rfl⟩ : syracuseStep 11056175 = 16584263) B16584263
theorem B7370783 : Blo 1939435 7370783 := bstep (se 1 (by rfl) ⟨5528087, by rfl⟩ : syracuseStep 7370783 = 11056175) B11056175
theorem B4913855 : Blo 1939435 4913855 := bstep (se 1 (by rfl) ⟨3685391, by rfl⟩ : syracuseStep 4913855 = 7370783) B7370783
theorem B3275903 : Blo 1939435 3275903 := bstep (se 1 (by rfl) ⟨2456927, by rfl⟩ : syracuseStep 3275903 = 4913855) B4913855
theorem B2183935 : Blo 1939435 2183935 := bstep (se 1 (by rfl) ⟨1637951, by rfl⟩ : syracuseStep 2183935 = 3275903) B3275903
theorem B2911913 : Blo 1939435 2911913 := bstep (se 2 (by rfl) ⟨1091967, by rfl⟩ : syracuseStep 2911913 = 2183935) B2183935
theorem B1941275 : Blo 1939435 1941275 := bstep (se 1 (by rfl) ⟨1455956, by rfl⟩ : syracuseStep 1941275 = 2911913) B2911913
theorem B2073037 : Blo 1939435 2073037 := bbase (se 3 (by rfl) ⟨388694, by rfl⟩ : syracuseStep 2073037 = 777389) (by norm_num)
theorem B2764049 : Blo 1939435 2764049 := bstep (se 2 (by rfl) ⟨1036518, by rfl⟩ : syracuseStep 2764049 = 2073037) B2073037
theorem B7370797 : Blo 1939435 7370797 := bstep (se 3 (by rfl) ⟨1382024, by rfl⟩ : syracuseStep 7370797 = 2764049) B2764049
theorem B9827729 : Blo 1939435 9827729 := bstep (se 2 (by rfl) ⟨3685398, by rfl⟩ : syracuseStep 9827729 = 7370797) B7370797
theorem B6551819 : Blo 1939435 6551819 := bstep (se 1 (by rfl) ⟨4913864, by rfl⟩ : syracuseStep 6551819 = 9827729) B9827729
theorem B4367879 : Blo 1939435 4367879 := bstep (se 1 (by rfl) ⟨3275909, by rfl⟩ : syracuseStep 4367879 = 6551819) B6551819
theorem B2911919 : Blo 1939435 2911919 := bstep (se 1 (by rfl) ⟨2183939, by rfl⟩ : syracuseStep 2911919 = 4367879) B4367879
theorem B1941279 : Blo 1939435 1941279 := bstep (se 1 (by rfl) ⟨1455959, by rfl⟩ : syracuseStep 1941279 = 2911919) B2911919
theorem B2911925 : Blo 1939435 2911925 := bbase (se 5 (by rfl) ⟨136496, by rfl⟩ : syracuseStep 2911925 = 272993) (by norm_num)
theorem B1941283 : Blo 1939435 1941283 := bstep (se 1 (by rfl) ⟨1455962, by rfl⟩ : syracuseStep 1941283 = 2911925) B2911925
theorem B4913885 : Blo 1939435 4913885 := bbase (se 3 (by rfl) ⟨921353, by rfl⟩ : syracuseStep 4913885 = 1842707) (by norm_num)
theorem B3275923 : Blo 1939435 3275923 := bstep (se 1 (by rfl) ⟨2456942, by rfl⟩ : syracuseStep 3275923 = 4913885) B4913885
theorem B4367897 : Blo 1939435 4367897 := bstep (se 2 (by rfl) ⟨1637961, by rfl⟩ : syracuseStep 4367897 = 3275923) B3275923
theorem B2911931 : Blo 1939435 2911931 := bstep (se 1 (by rfl) ⟨2183948, by rfl⟩ : syracuseStep 2911931 = 4367897) B4367897
theorem B1941287 : Blo 1939435 1941287 := bstep (se 1 (by rfl) ⟨1455965, by rfl⟩ : syracuseStep 1941287 = 2911931) B2911931
theorem B2183953 : Blo 1939435 2183953 := bbase (se 2 (by rfl) ⟨818982, by rfl⟩ : syracuseStep 2183953 = 1637965) (by norm_num)
theorem B2911937 : Blo 1939435 2911937 := bstep (se 2 (by rfl) ⟨1091976, by rfl⟩ : syracuseStep 2911937 = 2183953) B2183953
theorem B1941291 : Blo 1939435 1941291 := bstep (se 1 (by rfl) ⟨1455968, by rfl⟩ : syracuseStep 1941291 = 2911937) B2911937
theorem B3685429 : Blo 1939435 3685429 := bbase (se 5 (by rfl) ⟨172754, by rfl⟩ : syracuseStep 3685429 = 345509) (by norm_num)
theorem B4913905 : Blo 1939435 4913905 := bstep (se 2 (by rfl) ⟨1842714, by rfl⟩ : syracuseStep 4913905 = 3685429) B3685429
theorem B6551873 : Blo 1939435 6551873 := bstep (se 2 (by rfl) ⟨2456952, by rfl⟩ : syracuseStep 6551873 = 4913905) B4913905
theorem B4367915 : Blo 1939435 4367915 := bstep (se 1 (by rfl) ⟨3275936, by rfl⟩ : syracuseStep 4367915 = 6551873) B6551873
theorem B2911943 : Blo 1939435 2911943 := bstep (se 1 (by rfl) ⟨2183957, by rfl⟩ : syracuseStep 2911943 = 4367915) B4367915
theorem B1941295 : Blo 1939435 1941295 := bstep (se 1 (by rfl) ⟨1455971, by rfl⟩ : syracuseStep 1941295 = 2911943) B2911943
theorem B2911949 : Blo 1939435 2911949 := bbase (se 3 (by rfl) ⟨545990, by rfl⟩ : syracuseStep 2911949 = 1091981) (by norm_num)
theorem B1941299 : Blo 1939435 1941299 := bstep (se 1 (by rfl) ⟨1455974, by rfl⟩ : syracuseStep 1941299 = 2911949) B2911949
theorem B4367933 : Blo 1939435 4367933 := bbase (se 3 (by rfl) ⟨818987, by rfl⟩ : syracuseStep 4367933 = 1637975) (by norm_num)
theorem B2911955 : Blo 1939435 2911955 := bstep (se 1 (by rfl) ⟨2183966, by rfl⟩ : syracuseStep 2911955 = 4367933) B4367933
theorem B1941303 : Blo 1939435 1941303 := bstep (se 1 (by rfl) ⟨1455977, by rfl⟩ : syracuseStep 1941303 = 2911955) B2911955
theorem B3275957 : Blo 1939435 3275957 := bbase (se 5 (by rfl) ⟨153560, by rfl⟩ : syracuseStep 3275957 = 307121) (by norm_num)
theorem B2183971 : Blo 1939435 2183971 := bstep (se 1 (by rfl) ⟨1637978, by rfl⟩ : syracuseStep 2183971 = 3275957) B3275957
theorem B2911961 : Blo 1939435 2911961 := bstep (se 2 (by rfl) ⟨1091985, by rfl⟩ : syracuseStep 2911961 = 2183971) B2183971
theorem B1941307 : Blo 1939435 1941307 := bstep (se 1 (by rfl) ⟨1455980, by rfl⟩ : syracuseStep 1941307 = 2911961) B2911961
theorem B3989293 : Blo 1939435 3989293 := bbase (se 3 (by rfl) ⟨747992, by rfl⟩ : syracuseStep 3989293 = 1495985) (by norm_num)
theorem B85104917 : Blo 1939435 85104917 := bstep (se 6 (by rfl) ⟨1994646, by rfl⟩ : syracuseStep 85104917 = 3989293) B3989293
theorem B56736611 : Blo 1939435 56736611 := bstep (se 1 (by rfl) ⟨42552458, by rfl⟩ : syracuseStep 56736611 = 85104917) B85104917
theorem B37824407 : Blo 1939435 37824407 := bstep (se 1 (by rfl) ⟨28368305, by rfl⟩ : syracuseStep 37824407 = 56736611) B56736611
theorem B25216271 : Blo 1939435 25216271 := bstep (se 1 (by rfl) ⟨18912203, by rfl⟩ : syracuseStep 25216271 = 37824407) B37824407
theorem B16810847 : Blo 1939435 16810847 := bstep (se 1 (by rfl) ⟨12608135, by rfl⟩ : syracuseStep 16810847 = 25216271) B25216271
theorem B11207231 : Blo 1939435 11207231 := bstep (se 1 (by rfl) ⟨8405423, by rfl⟩ : syracuseStep 11207231 = 16810847) B16810847
theorem B7471487 : Blo 1939435 7471487 := bstep (se 1 (by rfl) ⟨5603615, by rfl⟩ : syracuseStep 7471487 = 11207231) B11207231
theorem B19923965 : Blo 1939435 19923965 := bstep (se 3 (by rfl) ⟨3735743, by rfl⟩ : syracuseStep 19923965 = 7471487) B7471487
theorem B13282643 : Blo 1939435 13282643 := bstep (se 1 (by rfl) ⟨9961982, by rfl⟩ : syracuseStep 13282643 = 19923965) B19923965
theorem B8855095 : Blo 1939435 8855095 := bstep (se 1 (by rfl) ⟨6641321, by rfl⟩ : syracuseStep 8855095 = 13282643) B13282643
theorem B11806793 : Blo 1939435 11806793 := bstep (se 2 (by rfl) ⟨4427547, by rfl⟩ : syracuseStep 11806793 = 8855095) B8855095
theorem B7871195 : Blo 1939435 7871195 := bstep (se 1 (by rfl) ⟨5903396, by rfl⟩ : syracuseStep 7871195 = 11806793) B11806793
theorem B5247463 : Blo 1939435 5247463 := bstep (se 1 (by rfl) ⟨3935597, by rfl⟩ : syracuseStep 5247463 = 7871195) B7871195
theorem B6996617 : Blo 1939435 6996617 := bstep (se 2 (by rfl) ⟨2623731, by rfl⟩ : syracuseStep 6996617 = 5247463) B5247463
theorem B4664411 : Blo 1939435 4664411 := bstep (se 1 (by rfl) ⟨3498308, by rfl⟩ : syracuseStep 4664411 = 6996617) B6996617
theorem B3109607 : Blo 1939435 3109607 := bstep (se 1 (by rfl) ⟨2332205, by rfl⟩ : syracuseStep 3109607 = 4664411) B4664411
theorem B2073071 : Blo 1939435 2073071 := bstep (se 1 (by rfl) ⟨1554803, by rfl⟩ : syracuseStep 2073071 = 3109607) B3109607
theorem B5528189 : Blo 1939435 5528189 := bstep (se 3 (by rfl) ⟨1036535, by rfl⟩ : syracuseStep 5528189 = 2073071) B2073071
theorem B14741837 : Blo 1939435 14741837 := bstep (se 3 (by rfl) ⟨2764094, by rfl⟩ : syracuseStep 14741837 = 5528189) B5528189
theorem B9827891 : Blo 1939435 9827891 := bstep (se 1 (by rfl) ⟨7370918, by rfl⟩ : syracuseStep 9827891 = 14741837) B14741837
theorem B6551927 : Blo 1939435 6551927 := bstep (se 1 (by rfl) ⟨4913945, by rfl⟩ : syracuseStep 6551927 = 9827891) B9827891
theorem B4367951 : Blo 1939435 4367951 := bstep (se 1 (by rfl) ⟨3275963, by rfl⟩ : syracuseStep 4367951 = 6551927) B6551927
theorem B2911967 : Blo 1939435 2911967 := bstep (se 1 (by rfl) ⟨2183975, by rfl⟩ : syracuseStep 2911967 = 4367951) B4367951
theorem B1941311 : Blo 1939435 1941311 := bstep (se 1 (by rfl) ⟨1455983, by rfl⟩ : syracuseStep 1941311 = 2911967) B2911967
theorem B2911973 : Blo 1939435 2911973 := bbase (se 4 (by rfl) ⟨272997, by rfl⟩ : syracuseStep 2911973 = 545995) (by norm_num)
theorem B1941315 : Blo 1939435 1941315 := bstep (se 1 (by rfl) ⟨1455986, by rfl⟩ : syracuseStep 1941315 = 2911973) B2911973
theorem B5528213 : Blo 1939435 5528213 := bbase (se 6 (by rfl) ⟨129567, by rfl⟩ : syracuseStep 5528213 = 259135) (by norm_num)
theorem B3685475 : Blo 1939435 3685475 := bstep (se 1 (by rfl) ⟨2764106, by rfl⟩ : syracuseStep 3685475 = 5528213) B5528213
theorem B2456983 : Blo 1939435 2456983 := bstep (se 1 (by rfl) ⟨1842737, by rfl⟩ : syracuseStep 2456983 = 3685475) B3685475
theorem B3275977 : Blo 1939435 3275977 := bstep (se 2 (by rfl) ⟨1228491, by rfl⟩ : syracuseStep 3275977 = 2456983) B2456983
theorem B4367969 : Blo 1939435 4367969 := bstep (se 2 (by rfl) ⟨1637988, by rfl⟩ : syracuseStep 4367969 = 3275977) B3275977
theorem B2911979 : Blo 1939435 2911979 := bstep (se 1 (by rfl) ⟨2183984, by rfl⟩ : syracuseStep 2911979 = 4367969) B4367969
theorem B1941319 : Blo 1939435 1941319 := bstep (se 1 (by rfl) ⟨1455989, by rfl⟩ : syracuseStep 1941319 = 2911979) B2911979
theorem B2183989 : Blo 1939435 2183989 := bbase (se 5 (by rfl) ⟨102374, by rfl⟩ : syracuseStep 2183989 = 204749) (by norm_num)
theorem B2911985 : Blo 1939435 2911985 := bstep (se 2 (by rfl) ⟨1091994, by rfl⟩ : syracuseStep 2911985 = 2183989) B2183989
theorem B1941323 : Blo 1939435 1941323 := bstep (se 1 (by rfl) ⟨1455992, by rfl⟩ : syracuseStep 1941323 = 2911985) B2911985
theorem B2456993 : Blo 1939435 2456993 := bbase (se 2 (by rfl) ⟨921372, by rfl⟩ : syracuseStep 2456993 = 1842745) (by norm_num)
theorem B6551981 : Blo 1939435 6551981 := bstep (se 3 (by rfl) ⟨1228496, by rfl⟩ : syracuseStep 6551981 = 2456993) B2456993
theorem B4367987 : Blo 1939435 4367987 := bstep (se 1 (by rfl) ⟨3275990, by rfl⟩ : syracuseStep 4367987 = 6551981) B6551981
theorem B2911991 : Blo 1939435 2911991 := bstep (se 1 (by rfl) ⟨2183993, by rfl⟩ : syracuseStep 2911991 = 4367987) B4367987
theorem B1941327 : Blo 1939435 1941327 := bstep (se 1 (by rfl) ⟨1455995, by rfl⟩ : syracuseStep 1941327 = 2911991) B2911991
theorem B2911997 : Blo 1939435 2911997 := bbase (se 3 (by rfl) ⟨545999, by rfl⟩ : syracuseStep 2911997 = 1091999) (by norm_num)
theorem B1941331 : Blo 1939435 1941331 := bstep (se 1 (by rfl) ⟨1455998, by rfl⟩ : syracuseStep 1941331 = 2911997) B2911997
theorem B4368005 : Blo 1939435 4368005 := bbase (se 4 (by rfl) ⟨409500, by rfl⟩ : syracuseStep 4368005 = 819001) (by norm_num)
theorem B2912003 : Blo 1939435 2912003 := bstep (se 1 (by rfl) ⟨2184002, by rfl⟩ : syracuseStep 2912003 = 4368005) B4368005
theorem B1941335 : Blo 1939435 1941335 := bstep (se 1 (by rfl) ⟨1456001, by rfl⟩ : syracuseStep 1941335 = 2912003) B2912003
theorem B5465269 : Blo 1939435 5465269 := bbase (se 5 (by rfl) ⟨256184, by rfl⟩ : syracuseStep 5465269 = 512369) (by norm_num)
theorem B7287025 : Blo 1939435 7287025 := bstep (se 2 (by rfl) ⟨2732634, by rfl⟩ : syracuseStep 7287025 = 5465269) B5465269
theorem B9716033 : Blo 1939435 9716033 := bstep (se 2 (by rfl) ⟨3643512, by rfl⟩ : syracuseStep 9716033 = 7287025) B7287025
theorem B6477355 : Blo 1939435 6477355 := bstep (se 1 (by rfl) ⟨4858016, by rfl⟩ : syracuseStep 6477355 = 9716033) B9716033
theorem B8636473 : Blo 1939435 8636473 := bstep (se 2 (by rfl) ⟨3238677, by rfl⟩ : syracuseStep 8636473 = 6477355) B6477355
theorem B11515297 : Blo 1939435 11515297 := bstep (se 2 (by rfl) ⟨4318236, by rfl⟩ : syracuseStep 11515297 = 8636473) B8636473
theorem B15353729 : Blo 1939435 15353729 := bstep (se 2 (by rfl) ⟨5757648, by rfl⟩ : syracuseStep 15353729 = 11515297) B11515297
theorem B10235819 : Blo 1939435 10235819 := bstep (se 1 (by rfl) ⟨7676864, by rfl⟩ : syracuseStep 10235819 = 15353729) B15353729
theorem B27295517 : Blo 1939435 27295517 := bstep (se 3 (by rfl) ⟨5117909, by rfl⟩ : syracuseStep 27295517 = 10235819) B10235819
theorem B18197011 : Blo 1939435 18197011 := bstep (se 1 (by rfl) ⟨13647758, by rfl⟩ : syracuseStep 18197011 = 27295517) B27295517
theorem B24262681 : Blo 1939435 24262681 := bstep (se 2 (by rfl) ⟨9098505, by rfl⟩ : syracuseStep 24262681 = 18197011) B18197011
theorem B32350241 : Blo 1939435 32350241 := bstep (se 2 (by rfl) ⟨12131340, by rfl⟩ : syracuseStep 32350241 = 24262681) B24262681
theorem B21566827 : Blo 1939435 21566827 := bstep (se 1 (by rfl) ⟨16175120, by rfl⟩ : syracuseStep 21566827 = 32350241) B32350241
theorem B115023077 : Blo 1939435 115023077 := bstep (se 4 (by rfl) ⟨10783413, by rfl⟩ : syracuseStep 115023077 = 21566827) B21566827
theorem B76682051 : Blo 1939435 76682051 := bstep (se 1 (by rfl) ⟨57511538, by rfl⟩ : syracuseStep 76682051 = 115023077) B115023077
theorem B51121367 : Blo 1939435 51121367 := bstep (se 1 (by rfl) ⟨38341025, by rfl⟩ : syracuseStep 51121367 = 76682051) B76682051
theorem B34080911 : Blo 1939435 34080911 := bstep (se 1 (by rfl) ⟨25560683, by rfl⟩ : syracuseStep 34080911 = 51121367) B51121367
theorem B22720607 : Blo 1939435 22720607 := bstep (se 1 (by rfl) ⟨17040455, by rfl⟩ : syracuseStep 22720607 = 34080911) B34080911
theorem B15147071 : Blo 1939435 15147071 := bstep (se 1 (by rfl) ⟨11360303, by rfl⟩ : syracuseStep 15147071 = 22720607) B22720607
theorem B10098047 : Blo 1939435 10098047 := bstep (se 1 (by rfl) ⟨7573535, by rfl⟩ : syracuseStep 10098047 = 15147071) B15147071
theorem B6732031 : Blo 1939435 6732031 := bstep (se 1 (by rfl) ⟨5049023, by rfl⟩ : syracuseStep 6732031 = 10098047) B10098047
theorem B8976041 : Blo 1939435 8976041 := bstep (se 2 (by rfl) ⟨3366015, by rfl⟩ : syracuseStep 8976041 = 6732031) B6732031
theorem B5984027 : Blo 1939435 5984027 := bstep (se 1 (by rfl) ⟨4488020, by rfl⟩ : syracuseStep 5984027 = 8976041) B8976041
theorem B3989351 : Blo 1939435 3989351 := bstep (se 1 (by rfl) ⟨2992013, by rfl⟩ : syracuseStep 3989351 = 5984027) B5984027
theorem B10638269 : Blo 1939435 10638269 := bstep (se 3 (by rfl) ⟨1994675, by rfl⟩ : syracuseStep 10638269 = 3989351) B3989351
theorem B7092179 : Blo 1939435 7092179 := bstep (se 1 (by rfl) ⟨5319134, by rfl⟩ : syracuseStep 7092179 = 10638269) B10638269
theorem B4728119 : Blo 1939435 4728119 := bstep (se 1 (by rfl) ⟨3546089, by rfl⟩ : syracuseStep 4728119 = 7092179) B7092179
theorem B12608317 : Blo 1939435 12608317 := bstep (se 3 (by rfl) ⟨2364059, by rfl⟩ : syracuseStep 12608317 = 4728119) B4728119
theorem B67244357 : Blo 1939435 67244357 := bstep (se 4 (by rfl) ⟨6304158, by rfl⟩ : syracuseStep 67244357 = 12608317) B12608317
theorem B44829571 : Blo 1939435 44829571 := bstep (se 1 (by rfl) ⟨33622178, by rfl⟩ : syracuseStep 44829571 = 67244357) B67244357
theorem B59772761 : Blo 1939435 59772761 := bstep (se 2 (by rfl) ⟨22414785, by rfl⟩ : syracuseStep 59772761 = 44829571) B44829571
theorem B39848507 : Blo 1939435 39848507 := bstep (se 1 (by rfl) ⟨29886380, by rfl⟩ : syracuseStep 39848507 = 59772761) B59772761
theorem B26565671 : Blo 1939435 26565671 := bstep (se 1 (by rfl) ⟨19924253, by rfl⟩ : syracuseStep 26565671 = 39848507) B39848507
theorem B17710447 : Blo 1939435 17710447 := bstep (se 1 (by rfl) ⟨13282835, by rfl⟩ : syracuseStep 17710447 = 26565671) B26565671
theorem B23613929 : Blo 1939435 23613929 := bstep (se 2 (by rfl) ⟨8855223, by rfl⟩ : syracuseStep 23613929 = 17710447) B17710447
theorem B15742619 : Blo 1939435 15742619 := bstep (se 1 (by rfl) ⟨11806964, by rfl⟩ : syracuseStep 15742619 = 23613929) B23613929
theorem B10495079 : Blo 1939435 10495079 := bstep (se 1 (by rfl) ⟨7871309, by rfl⟩ : syracuseStep 10495079 = 15742619) B15742619
theorem B6996719 : Blo 1939435 6996719 := bstep (se 1 (by rfl) ⟨5247539, by rfl⟩ : syracuseStep 6996719 = 10495079) B10495079
theorem B4664479 : Blo 1939435 4664479 := bstep (se 1 (by rfl) ⟨3498359, by rfl⟩ : syracuseStep 4664479 = 6996719) B6996719
theorem B6219305 : Blo 1939435 6219305 := bstep (se 2 (by rfl) ⟨2332239, by rfl⟩ : syracuseStep 6219305 = 4664479) B4664479
theorem B4146203 : Blo 1939435 4146203 := bstep (se 1 (by rfl) ⟨3109652, by rfl⟩ : syracuseStep 4146203 = 6219305) B6219305
theorem B2764135 : Blo 1939435 2764135 := bstep (se 1 (by rfl) ⟨2073101, by rfl⟩ : syracuseStep 2764135 = 4146203) B4146203
theorem B3685513 : Blo 1939435 3685513 := bstep (se 2 (by rfl) ⟨1382067, by rfl⟩ : syracuseStep 3685513 = 2764135) B2764135
theorem B4914017 : Blo 1939435 4914017 := bstep (se 2 (by rfl) ⟨1842756, by rfl⟩ : syracuseStep 4914017 = 3685513) B3685513
theorem B3276011 : Blo 1939435 3276011 := bstep (se 1 (by rfl) ⟨2457008, by rfl⟩ : syracuseStep 3276011 = 4914017) B4914017
theorem B2184007 : Blo 1939435 2184007 := bstep (se 1 (by rfl) ⟨1638005, by rfl⟩ : syracuseStep 2184007 = 3276011) B3276011
theorem B2912009 : Blo 1939435 2912009 := bstep (se 2 (by rfl) ⟨1092003, by rfl⟩ : syracuseStep 2912009 = 2184007) B2184007
theorem B1941339 : Blo 1939435 1941339 := bstep (se 1 (by rfl) ⟨1456004, by rfl⟩ : syracuseStep 1941339 = 2912009) B2912009
theorem B9828053 : Blo 1939435 9828053 := bbase (se 7 (by rfl) ⟨115172, by rfl⟩ : syracuseStep 9828053 = 230345) (by norm_num)
theorem B6552035 : Blo 1939435 6552035 := bstep (se 1 (by rfl) ⟨4914026, by rfl⟩ : syracuseStep 6552035 = 9828053) B9828053
theorem B4368023 : Blo 1939435 4368023 := bstep (se 1 (by rfl) ⟨3276017, by rfl⟩ : syracuseStep 4368023 = 6552035) B6552035
theorem B2912015 : Blo 1939435 2912015 := bstep (se 1 (by rfl) ⟨2184011, by rfl⟩ : syracuseStep 2912015 = 4368023) B4368023
theorem B1941343 : Blo 1939435 1941343 := bstep (se 1 (by rfl) ⟨1456007, by rfl⟩ : syracuseStep 1941343 = 2912015) B2912015
theorem B2912021 : Blo 1939435 2912021 := bbase (se 6 (by rfl) ⟨68250, by rfl⟩ : syracuseStep 2912021 = 136501) (by norm_num)
theorem B1941347 : Blo 1939435 1941347 := bstep (se 1 (by rfl) ⟨1456010, by rfl⟩ : syracuseStep 1941347 = 2912021) B2912021
theorem B4549277 : Blo 1939435 4549277 := bbase (se 3 (by rfl) ⟨852989, by rfl⟩ : syracuseStep 4549277 = 1705979) (by norm_num)
theorem B12131405 : Blo 1939435 12131405 := bstep (se 3 (by rfl) ⟨2274638, by rfl⟩ : syracuseStep 12131405 = 4549277) B4549277
theorem B8087603 : Blo 1939435 8087603 := bstep (se 1 (by rfl) ⟨6065702, by rfl⟩ : syracuseStep 8087603 = 12131405) B12131405
theorem B21566941 : Blo 1939435 21566941 := bstep (se 3 (by rfl) ⟨4043801, by rfl⟩ : syracuseStep 21566941 = 8087603) B8087603
theorem B460094741 : Blo 1939435 460094741 := bstep (se 6 (by rfl) ⟨10783470, by rfl⟩ : syracuseStep 460094741 = 21566941) B21566941
theorem B306729827 : Blo 1939435 306729827 := bstep (se 1 (by rfl) ⟨230047370, by rfl⟩ : syracuseStep 306729827 = 460094741) B460094741
theorem B204486551 : Blo 1939435 204486551 := bstep (se 1 (by rfl) ⟨153364913, by rfl⟩ : syracuseStep 204486551 = 306729827) B306729827
theorem B136324367 : Blo 1939435 136324367 := bstep (se 1 (by rfl) ⟨102243275, by rfl⟩ : syracuseStep 136324367 = 204486551) B204486551
theorem B90882911 : Blo 1939435 90882911 := bstep (se 1 (by rfl) ⟨68162183, by rfl⟩ : syracuseStep 90882911 = 136324367) B136324367
theorem B60588607 : Blo 1939435 60588607 := bstep (se 1 (by rfl) ⟨45441455, by rfl⟩ : syracuseStep 60588607 = 90882911) B90882911
theorem B80784809 : Blo 1939435 80784809 := bstep (se 2 (by rfl) ⟨30294303, by rfl⟩ : syracuseStep 80784809 = 60588607) B60588607
theorem B53856539 : Blo 1939435 53856539 := bstep (se 1 (by rfl) ⟨40392404, by rfl⟩ : syracuseStep 53856539 = 80784809) B80784809
theorem B35904359 : Blo 1939435 35904359 := bstep (se 1 (by rfl) ⟨26928269, by rfl⟩ : syracuseStep 35904359 = 53856539) B53856539
theorem B23936239 : Blo 1939435 23936239 := bstep (se 1 (by rfl) ⟨17952179, by rfl⟩ : syracuseStep 23936239 = 35904359) B35904359
theorem B127659941 : Blo 1939435 127659941 := bstep (se 4 (by rfl) ⟨11968119, by rfl⟩ : syracuseStep 127659941 = 23936239) B23936239
theorem B85106627 : Blo 1939435 85106627 := bstep (se 1 (by rfl) ⟨63829970, by rfl⟩ : syracuseStep 85106627 = 127659941) B127659941
theorem B56737751 : Blo 1939435 56737751 := bstep (se 1 (by rfl) ⟨42553313, by rfl⟩ : syracuseStep 56737751 = 85106627) B85106627
theorem B151300669 : Blo 1939435 151300669 := bstep (se 3 (by rfl) ⟨28368875, by rfl⟩ : syracuseStep 151300669 = 56737751) B56737751
theorem B201734225 : Blo 1939435 201734225 := bstep (se 2 (by rfl) ⟨75650334, by rfl⟩ : syracuseStep 201734225 = 151300669) B151300669
theorem B134489483 : Blo 1939435 134489483 := bstep (se 1 (by rfl) ⟨100867112, by rfl⟩ : syracuseStep 134489483 = 201734225) B201734225
theorem B89659655 : Blo 1939435 89659655 := bstep (se 1 (by rfl) ⟨67244741, by rfl⟩ : syracuseStep 89659655 = 134489483) B134489483
theorem B59773103 : Blo 1939435 59773103 := bstep (se 1 (by rfl) ⟨44829827, by rfl⟩ : syracuseStep 59773103 = 89659655) B89659655
theorem B39848735 : Blo 1939435 39848735 := bstep (se 1 (by rfl) ⟨29886551, by rfl⟩ : syracuseStep 39848735 = 59773103) B59773103
theorem B26565823 : Blo 1939435 26565823 := bstep (se 1 (by rfl) ⟨19924367, by rfl⟩ : syracuseStep 26565823 = 39848735) B39848735
theorem B35421097 : Blo 1939435 35421097 := bstep (se 2 (by rfl) ⟨13282911, by rfl⟩ : syracuseStep 35421097 = 26565823) B26565823
theorem B47228129 : Blo 1939435 47228129 := bstep (se 2 (by rfl) ⟨17710548, by rfl⟩ : syracuseStep 47228129 = 35421097) B35421097
theorem B31485419 : Blo 1939435 31485419 := bstep (se 1 (by rfl) ⟨23614064, by rfl⟩ : syracuseStep 31485419 = 47228129) B47228129
theorem B20990279 : Blo 1939435 20990279 := bstep (se 1 (by rfl) ⟨15742709, by rfl⟩ : syracuseStep 20990279 = 31485419) B31485419
theorem B55974077 : Blo 1939435 55974077 := bstep (se 3 (by rfl) ⟨10495139, by rfl⟩ : syracuseStep 55974077 = 20990279) B20990279
theorem B37316051 : Blo 1939435 37316051 := bstep (se 1 (by rfl) ⟨27987038, by rfl⟩ : syracuseStep 37316051 = 55974077) B55974077
theorem B24877367 : Blo 1939435 24877367 := bstep (se 1 (by rfl) ⟨18658025, by rfl⟩ : syracuseStep 24877367 = 37316051) B37316051
theorem B16584911 : Blo 1939435 16584911 := bstep (se 1 (by rfl) ⟨12438683, by rfl⟩ : syracuseStep 16584911 = 24877367) B24877367
theorem B11056607 : Blo 1939435 11056607 := bstep (se 1 (by rfl) ⟨8292455, by rfl⟩ : syracuseStep 11056607 = 16584911) B16584911
theorem B7371071 : Blo 1939435 7371071 := bstep (se 1 (by rfl) ⟨5528303, by rfl⟩ : syracuseStep 7371071 = 11056607) B11056607
theorem B4914047 : Blo 1939435 4914047 := bstep (se 1 (by rfl) ⟨3685535, by rfl⟩ : syracuseStep 4914047 = 7371071) B7371071
theorem B3276031 : Blo 1939435 3276031 := bstep (se 1 (by rfl) ⟨2457023, by rfl⟩ : syracuseStep 3276031 = 4914047) B4914047
theorem B4368041 : Blo 1939435 4368041 := bstep (se 2 (by rfl) ⟨1638015, by rfl⟩ : syracuseStep 4368041 = 3276031) B3276031
theorem B2912027 : Blo 1939435 2912027 := bstep (se 1 (by rfl) ⟨2184020, by rfl⟩ : syracuseStep 2912027 = 4368041) B4368041
theorem B1941351 : Blo 1939435 1941351 := bstep (se 1 (by rfl) ⟨1456013, by rfl⟩ : syracuseStep 1941351 = 2912027) B2912027
theorem B2184025 : Blo 1939435 2184025 := bbase (se 2 (by rfl) ⟨819009, by rfl⟩ : syracuseStep 2184025 = 1638019) (by norm_num)
theorem B2912033 : Blo 1939435 2912033 := bstep (se 2 (by rfl) ⟨1092012, by rfl⟩ : syracuseStep 2912033 = 2184025) B2184025
theorem B1941355 : Blo 1939435 1941355 := bstep (se 1 (by rfl) ⟨1456016, by rfl⟩ : syracuseStep 1941355 = 2912033) B2912033
theorem B4146245 : Blo 1939435 4146245 := bbase (se 4 (by rfl) ⟨388710, by rfl⟩ : syracuseStep 4146245 = 777421) (by norm_num)
theorem B2764163 : Blo 1939435 2764163 := bstep (se 1 (by rfl) ⟨2073122, by rfl⟩ : syracuseStep 2764163 = 4146245) B4146245
theorem B7371101 : Blo 1939435 7371101 := bstep (se 3 (by rfl) ⟨1382081, by rfl⟩ : syracuseStep 7371101 = 2764163) B2764163
theorem B4914067 : Blo 1939435 4914067 := bstep (se 1 (by rfl) ⟨3685550, by rfl⟩ : syracuseStep 4914067 = 7371101) B7371101
theorem B6552089 : Blo 1939435 6552089 := bstep (se 2 (by rfl) ⟨2457033, by rfl⟩ : syracuseStep 6552089 = 4914067) B4914067
theorem B4368059 : Blo 1939435 4368059 := bstep (se 1 (by rfl) ⟨3276044, by rfl⟩ : syracuseStep 4368059 = 6552089) B6552089
theorem B2912039 : Blo 1939435 2912039 := bstep (se 1 (by rfl) ⟨2184029, by rfl⟩ : syracuseStep 2912039 = 4368059) B4368059
theorem B1941359 : Blo 1939435 1941359 := bstep (se 1 (by rfl) ⟨1456019, by rfl⟩ : syracuseStep 1941359 = 2912039) B2912039
theorem B2912045 : Blo 1939435 2912045 := bbase (se 3 (by rfl) ⟨546008, by rfl⟩ : syracuseStep 2912045 = 1092017) (by norm_num)
theorem B1941363 : Blo 1939435 1941363 := bstep (se 1 (by rfl) ⟨1456022, by rfl⟩ : syracuseStep 1941363 = 2912045) B2912045
theorem B4368077 : Blo 1939435 4368077 := bbase (se 3 (by rfl) ⟨819014, by rfl⟩ : syracuseStep 4368077 = 1638029) (by norm_num)
theorem B2912051 : Blo 1939435 2912051 := bstep (se 1 (by rfl) ⟨2184038, by rfl⟩ : syracuseStep 2912051 = 4368077) B4368077
theorem B1941367 : Blo 1939435 1941367 := bstep (se 1 (by rfl) ⟨1456025, by rfl⟩ : syracuseStep 1941367 = 2912051) B2912051
theorem B2457049 : Blo 1939435 2457049 := bbase (se 2 (by rfl) ⟨921393, by rfl⟩ : syracuseStep 2457049 = 1842787) (by norm_num)
theorem B3276065 : Blo 1939435 3276065 := bstep (se 2 (by rfl) ⟨1228524, by rfl⟩ : syracuseStep 3276065 = 2457049) B2457049
theorem B2184043 : Blo 1939435 2184043 := bstep (se 1 (by rfl) ⟨1638032, by rfl⟩ : syracuseStep 2184043 = 3276065) B3276065
theorem B2912057 : Blo 1939435 2912057 := bstep (se 2 (by rfl) ⟨1092021, by rfl⟩ : syracuseStep 2912057 = 2184043) B2184043
theorem B1941371 : Blo 1939435 1941371 := bstep (se 1 (by rfl) ⟨1456028, by rfl⟩ : syracuseStep 1941371 = 2912057) B2912057
theorem B3109709 : Blo 1939435 3109709 := bbase (se 3 (by rfl) ⟨583070, by rfl⟩ : syracuseStep 3109709 = 1166141) (by norm_num)
theorem B8292557 : Blo 1939435 8292557 := bstep (se 3 (by rfl) ⟨1554854, by rfl⟩ : syracuseStep 8292557 = 3109709) B3109709
theorem B22113485 : Blo 1939435 22113485 := bstep (se 3 (by rfl) ⟨4146278, by rfl⟩ : syracuseStep 22113485 = 8292557) B8292557
theorem B14742323 : Blo 1939435 14742323 := bstep (se 1 (by rfl) ⟨11056742, by rfl⟩ : syracuseStep 14742323 = 22113485) B22113485
theorem B9828215 : Blo 1939435 9828215 := bstep (se 1 (by rfl) ⟨7371161, by rfl⟩ : syracuseStep 9828215 = 14742323) B14742323
theorem B6552143 : Blo 1939435 6552143 := bstep (se 1 (by rfl) ⟨4914107, by rfl⟩ : syracuseStep 6552143 = 9828215) B9828215
theorem B4368095 : Blo 1939435 4368095 := bstep (se 1 (by rfl) ⟨3276071, by rfl⟩ : syracuseStep 4368095 = 6552143) B6552143
theorem B2912063 : Blo 1939435 2912063 := bstep (se 1 (by rfl) ⟨2184047, by rfl⟩ : syracuseStep 2912063 = 4368095) B4368095
theorem B1941375 : Blo 1939435 1941375 := bstep (se 1 (by rfl) ⟨1456031, by rfl⟩ : syracuseStep 1941375 = 2912063) B2912063
theorem B2912069 : Blo 1939435 2912069 := bbase (se 4 (by rfl) ⟨273006, by rfl⟩ : syracuseStep 2912069 = 546013) (by norm_num)
theorem B1941379 : Blo 1939435 1941379 := bstep (se 1 (by rfl) ⟨1456034, by rfl⟩ : syracuseStep 1941379 = 2912069) B2912069
theorem B3276085 : Blo 1939435 3276085 := bbase (se 5 (by rfl) ⟨153566, by rfl⟩ : syracuseStep 3276085 = 307133) (by norm_num)
theorem B4368113 : Blo 1939435 4368113 := bstep (se 2 (by rfl) ⟨1638042, by rfl⟩ : syracuseStep 4368113 = 3276085) B3276085
theorem B2912075 : Blo 1939435 2912075 := bstep (se 1 (by rfl) ⟨2184056, by rfl⟩ : syracuseStep 2912075 = 4368113) B4368113
theorem B1941383 : Blo 1939435 1941383 := bstep (se 1 (by rfl) ⟨1456037, by rfl⟩ : syracuseStep 1941383 = 2912075) B2912075
theorem B2184061 : Blo 1939435 2184061 := bbase (se 3 (by rfl) ⟨409511, by rfl⟩ : syracuseStep 2184061 = 819023) (by norm_num)
theorem B2912081 : Blo 1939435 2912081 := bstep (se 2 (by rfl) ⟨1092030, by rfl⟩ : syracuseStep 2912081 = 2184061) B2184061
theorem B1941387 : Blo 1939435 1941387 := bstep (se 1 (by rfl) ⟨1456040, by rfl⟩ : syracuseStep 1941387 = 2912081) B2912081
theorem B6552197 : Blo 1939435 6552197 := bbase (se 4 (by rfl) ⟨614268, by rfl⟩ : syracuseStep 6552197 = 1228537) (by norm_num)
theorem B4368131 : Blo 1939435 4368131 := bstep (se 1 (by rfl) ⟨3276098, by rfl⟩ : syracuseStep 4368131 = 6552197) B6552197
theorem B2912087 : Blo 1939435 2912087 := bstep (se 1 (by rfl) ⟨2184065, by rfl⟩ : syracuseStep 2912087 = 4368131) B4368131
theorem B1941391 : Blo 1939435 1941391 := bstep (se 1 (by rfl) ⟨1456043, by rfl⟩ : syracuseStep 1941391 = 2912087) B2912087
theorem B2912093 : Blo 1939435 2912093 := bbase (se 3 (by rfl) ⟨546017, by rfl⟩ : syracuseStep 2912093 = 1092035) (by norm_num)
theorem B1941395 : Blo 1939435 1941395 := bstep (se 1 (by rfl) ⟨1456046, by rfl⟩ : syracuseStep 1941395 = 2912093) B2912093
theorem B4368149 : Blo 1939435 4368149 := bbase (se 6 (by rfl) ⟨102378, by rfl⟩ : syracuseStep 4368149 = 204757) (by norm_num)
theorem B2912099 : Blo 1939435 2912099 := bstep (se 1 (by rfl) ⟨2184074, by rfl⟩ : syracuseStep 2912099 = 4368149) B4368149
theorem B1941399 : Blo 1939435 1941399 := bstep (se 1 (by rfl) ⟨1456049, by rfl⟩ : syracuseStep 1941399 = 2912099) B2912099
theorem B7371269 : Blo 1939435 7371269 := bbase (se 4 (by rfl) ⟨691056, by rfl⟩ : syracuseStep 7371269 = 1382113) (by norm_num)
theorem B4914179 : Blo 1939435 4914179 := bstep (se 1 (by rfl) ⟨3685634, by rfl⟩ : syracuseStep 4914179 = 7371269) B7371269
theorem B3276119 : Blo 1939435 3276119 := bstep (se 1 (by rfl) ⟨2457089, by rfl⟩ : syracuseStep 3276119 = 4914179) B4914179
theorem B2184079 : Blo 1939435 2184079 := bstep (se 1 (by rfl) ⟨1638059, by rfl⟩ : syracuseStep 2184079 = 3276119) B3276119
theorem B2912105 : Blo 1939435 2912105 := bstep (se 2 (by rfl) ⟨1092039, by rfl⟩ : syracuseStep 2912105 = 2184079) B2184079
theorem B1941403 : Blo 1939435 1941403 := bstep (se 1 (by rfl) ⟨1456052, by rfl⟩ : syracuseStep 1941403 = 2912105) B2912105
theorem B2623861 : Blo 1939435 2623861 := bbase (se 5 (by rfl) ⟨122993, by rfl⟩ : syracuseStep 2623861 = 245987) (by norm_num)
theorem B3498481 : Blo 1939435 3498481 := bstep (se 2 (by rfl) ⟨1311930, by rfl⟩ : syracuseStep 3498481 = 2623861) B2623861
theorem B4664641 : Blo 1939435 4664641 := bstep (se 2 (by rfl) ⟨1749240, by rfl⟩ : syracuseStep 4664641 = 3498481) B3498481
theorem B6219521 : Blo 1939435 6219521 := bstep (se 2 (by rfl) ⟨2332320, by rfl⟩ : syracuseStep 6219521 = 4664641) B4664641
theorem B4146347 : Blo 1939435 4146347 := bstep (se 1 (by rfl) ⟨3109760, by rfl⟩ : syracuseStep 4146347 = 6219521) B6219521
theorem B11056925 : Blo 1939435 11056925 := bstep (se 3 (by rfl) ⟨2073173, by rfl⟩ : syracuseStep 11056925 = 4146347) B4146347
theorem B7371283 : Blo 1939435 7371283 := bstep (se 1 (by rfl) ⟨5528462, by rfl⟩ : syracuseStep 7371283 = 11056925) B11056925
theorem B9828377 : Blo 1939435 9828377 := bstep (se 2 (by rfl) ⟨3685641, by rfl⟩ : syracuseStep 9828377 = 7371283) B7371283
theorem B6552251 : Blo 1939435 6552251 := bstep (se 1 (by rfl) ⟨4914188, by rfl⟩ : syracuseStep 6552251 = 9828377) B9828377
theorem B4368167 : Blo 1939435 4368167 := bstep (se 1 (by rfl) ⟨3276125, by rfl⟩ : syracuseStep 4368167 = 6552251) B6552251
theorem B2912111 : Blo 1939435 2912111 := bstep (se 1 (by rfl) ⟨2184083, by rfl⟩ : syracuseStep 2912111 = 4368167) B4368167
theorem B1941407 : Blo 1939435 1941407 := bstep (se 1 (by rfl) ⟨1456055, by rfl⟩ : syracuseStep 1941407 = 2912111) B2912111
theorem B2912117 : Blo 1939435 2912117 := bbase (se 5 (by rfl) ⟨136505, by rfl⟩ : syracuseStep 2912117 = 273011) (by norm_num)
theorem B1941411 : Blo 1939435 1941411 := bstep (se 1 (by rfl) ⟨1456058, by rfl⟩ : syracuseStep 1941411 = 2912117) B2912117
theorem B4146365 : Blo 1939435 4146365 := bbase (se 3 (by rfl) ⟨777443, by rfl⟩ : syracuseStep 4146365 = 1554887) (by norm_num)
theorem B2764243 : Blo 1939435 2764243 := bstep (se 1 (by rfl) ⟨2073182, by rfl⟩ : syracuseStep 2764243 = 4146365) B4146365
theorem B3685657 : Blo 1939435 3685657 := bstep (se 2 (by rfl) ⟨1382121, by rfl⟩ : syracuseStep 3685657 = 2764243) B2764243
theorem B4914209 : Blo 1939435 4914209 := bstep (se 2 (by rfl) ⟨1842828, by rfl⟩ : syracuseStep 4914209 = 3685657) B3685657
theorem B3276139 : Blo 1939435 3276139 := bstep (se 1 (by rfl) ⟨2457104, by rfl⟩ : syracuseStep 3276139 = 4914209) B4914209
theorem B4368185 : Blo 1939435 4368185 := bstep (se 2 (by rfl) ⟨1638069, by rfl⟩ : syracuseStep 4368185 = 3276139) B3276139
theorem B2912123 : Blo 1939435 2912123 := bstep (se 1 (by rfl) ⟨2184092, by rfl⟩ : syracuseStep 2912123 = 4368185) B4368185
theorem B1941415 : Blo 1939435 1941415 := bstep (se 1 (by rfl) ⟨1456061, by rfl⟩ : syracuseStep 1941415 = 2912123) B2912123
theorem B2184097 : Blo 1939435 2184097 := bbase (se 2 (by rfl) ⟨819036, by rfl⟩ : syracuseStep 2184097 = 1638073) (by norm_num)
theorem B2912129 : Blo 1939435 2912129 := bstep (se 2 (by rfl) ⟨1092048, by rfl⟩ : syracuseStep 2912129 = 2184097) B2184097
theorem B1941419 : Blo 1939435 1941419 := bstep (se 1 (by rfl) ⟨1456064, by rfl⟩ : syracuseStep 1941419 = 2912129) B2912129
theorem B4914229 : Blo 1939435 4914229 := bbase (se 5 (by rfl) ⟨230354, by rfl⟩ : syracuseStep 4914229 = 460709) (by norm_num)
theorem B6552305 : Blo 1939435 6552305 := bstep (se 2 (by rfl) ⟨2457114, by rfl⟩ : syracuseStep 6552305 = 4914229) B4914229
theorem B4368203 : Blo 1939435 4368203 := bstep (se 1 (by rfl) ⟨3276152, by rfl⟩ : syracuseStep 4368203 = 6552305) B6552305
theorem B2912135 : Blo 1939435 2912135 := bstep (se 1 (by rfl) ⟨2184101, by rfl⟩ : syracuseStep 2912135 = 4368203) B4368203
theorem B1941423 : Blo 1939435 1941423 := bstep (se 1 (by rfl) ⟨1456067, by rfl⟩ : syracuseStep 1941423 = 2912135) B2912135
theorem B2912141 : Blo 1939435 2912141 := bbase (se 3 (by rfl) ⟨546026, by rfl⟩ : syracuseStep 2912141 = 1092053) (by norm_num)
theorem B1941427 : Blo 1939435 1941427 := bstep (se 1 (by rfl) ⟨1456070, by rfl⟩ : syracuseStep 1941427 = 2912141) B2912141
theorem B4368221 : Blo 1939435 4368221 := bbase (se 3 (by rfl) ⟨819041, by rfl⟩ : syracuseStep 4368221 = 1638083) (by norm_num)
theorem B2912147 : Blo 1939435 2912147 := bstep (se 1 (by rfl) ⟨2184110, by rfl⟩ : syracuseStep 2912147 = 4368221) B4368221
theorem B1941431 : Blo 1939435 1941431 := bstep (se 1 (by rfl) ⟨1456073, by rfl⟩ : syracuseStep 1941431 = 2912147) B2912147
theorem B3276173 : Blo 1939435 3276173 := bbase (se 3 (by rfl) ⟨614282, by rfl⟩ : syracuseStep 3276173 = 1228565) (by norm_num)
theorem B2184115 : Blo 1939435 2184115 := bstep (se 1 (by rfl) ⟨1638086, by rfl⟩ : syracuseStep 2184115 = 3276173) B3276173
theorem B2912153 : Blo 1939435 2912153 := bstep (se 2 (by rfl) ⟨1092057, by rfl⟩ : syracuseStep 2912153 = 2184115) B2184115
theorem B1941435 : Blo 1939435 1941435 := bstep (se 1 (by rfl) ⟨1456076, by rfl⟩ : syracuseStep 1941435 = 2912153) B2912153
theorem C0 (j : ℕ) (h1 : 484858 ≤ j) (h2 : j ≤ 485358) : Blo 1939435 (4 * j + 3) := by
  interval_cases j
  · exact B1939435
  · exact B1939439
  · exact B1939443
  · exact B1939447
  · exact B1939451
  · exact B1939455
  · exact B1939459
  · exact B1939463
  · exact B1939467
  · exact B1939471
  · exact B1939475
  · exact B1939479
  · exact B1939483
  · exact B1939487
  · exact B1939491
  · exact B1939495
  · exact B1939499
  · exact B1939503
  · exact B1939507
  · exact B1939511
  · exact B1939515
  · exact B1939519
  · exact B1939523
  · exact B1939527
  · exact B1939531
  · exact B1939535
  · exact B1939539
  · exact B1939543
  · exact B1939547
  · exact B1939551
  · exact B1939555
  · exact B1939559
  · exact B1939563
  · exact B1939567
  · exact B1939571
  · exact B1939575
  · exact B1939579
  · exact B1939583
  · exact B1939587
  · exact B1939591
  · exact B1939595
  · exact B1939599
  · exact B1939603
  · exact B1939607
  · exact B1939611
  · exact B1939615
  · exact B1939619
  · exact B1939623
  · exact B1939627
  · exact B1939631
  · exact B1939635
  · exact B1939639
  · exact B1939643
  · exact B1939647
  · exact B1939651
  · exact B1939655
  · exact B1939659
  · exact B1939663
  · exact B1939667
  · exact B1939671
  · exact B1939675
  · exact B1939679
  · exact B1939683
  · exact B1939687
  · exact B1939691
  · exact B1939695
  · exact B1939699
  · exact B1939703
  · exact B1939707
  · exact B1939711
  · exact B1939715
  · exact B1939719
  · exact B1939723
  · exact B1939727
  · exact B1939731
  · exact B1939735
  · exact B1939739
  · exact B1939743
  · exact B1939747
  · exact B1939751
  · exact B1939755
  · exact B1939759
  · exact B1939763
  · exact B1939767
  · exact B1939771
  · exact B1939775
  · exact B1939779
  · exact B1939783
  · exact B1939787
  · exact B1939791
  · exact B1939795
  · exact B1939799
  · exact B1939803
  · exact B1939807
  · exact B1939811
  · exact B1939815
  · exact B1939819
  · exact B1939823
  · exact B1939827
  · exact B1939831
  · exact B1939835
  · exact B1939839
  · exact B1939843
  · exact B1939847
  · exact B1939851
  · exact B1939855
  · exact B1939859
  · exact B1939863
  · exact B1939867
  · exact B1939871
  · exact B1939875
  · exact B1939879
  · exact B1939883
  · exact B1939887
  · exact B1939891
  · exact B1939895
  · exact B1939899
  · exact B1939903
  · exact B1939907
  · exact B1939911
  · exact B1939915
  · exact B1939919
  · exact B1939923
  · exact B1939927
  · exact B1939931
  · exact B1939935
  · exact B1939939
  · exact B1939943
  · exact B1939947
  · exact B1939951
  · exact B1939955
  · exact B1939959
  · exact B1939963
  · exact B1939967
  · exact B1939971
  · exact B1939975
  · exact B1939979
  · exact B1939983
  · exact B1939987
  · exact B1939991
  · exact B1939995
  · exact B1939999
  · exact B1940003
  · exact B1940007
  · exact B1940011
  · exact B1940015
  · exact B1940019
  · exact B1940023
  · exact B1940027
  · exact B1940031
  · exact B1940035
  · exact B1940039
  · exact B1940043
  · exact B1940047
  · exact B1940051
  · exact B1940055
  · exact B1940059
  · exact B1940063
  · exact B1940067
  · exact B1940071
  · exact B1940075
  · exact B1940079
  · exact B1940083
  · exact B1940087
  · exact B1940091
  · exact B1940095
  · exact B1940099
  · exact B1940103
  · exact B1940107
  · exact B1940111
  · exact B1940115
  · exact B1940119
  · exact B1940123
  · exact B1940127
  · exact B1940131
  · exact B1940135
  · exact B1940139
  · exact B1940143
  · exact B1940147
  · exact B1940151
  · exact B1940155
  · exact B1940159
  · exact B1940163
  · exact B1940167
  · exact B1940171
  · exact B1940175
  · exact B1940179
  · exact B1940183
  · exact B1940187
  · exact B1940191
  · exact B1940195
  · exact B1940199
  · exact B1940203
  · exact B1940207
  · exact B1940211
  · exact B1940215
  · exact B1940219
  · exact B1940223
  · exact B1940227
  · exact B1940231
  · exact B1940235
  · exact B1940239
  · exact B1940243
  · exact B1940247
  · exact B1940251
  · exact B1940255
  · exact B1940259
  · exact B1940263
  · exact B1940267
  · exact B1940271
  · exact B1940275
  · exact B1940279
  · exact B1940283
  · exact B1940287
  · exact B1940291
  · exact B1940295
  · exact B1940299
  · exact B1940303
  · exact B1940307
  · exact B1940311
  · exact B1940315
  · exact B1940319
  · exact B1940323
  · exact B1940327
  · exact B1940331
  · exact B1940335
  · exact B1940339
  · exact B1940343
  · exact B1940347
  · exact B1940351
  · exact B1940355
  · exact B1940359
  · exact B1940363
  · exact B1940367
  · exact B1940371
  · exact B1940375
  · exact B1940379
  · exact B1940383
  · exact B1940387
  · exact B1940391
  · exact B1940395
  · exact B1940399
  · exact B1940403
  · exact B1940407
  · exact B1940411
  · exact B1940415
  · exact B1940419
  · exact B1940423
  · exact B1940427
  · exact B1940431
  · exact B1940435
  · exact B1940439
  · exact B1940443
  · exact B1940447
  · exact B1940451
  · exact B1940455
  · exact B1940459
  · exact B1940463
  · exact B1940467
  · exact B1940471
  · exact B1940475
  · exact B1940479
  · exact B1940483
  · exact B1940487
  · exact B1940491
  · exact B1940495
  · exact B1940499
  · exact B1940503
  · exact B1940507
  · exact B1940511
  · exact B1940515
  · exact B1940519
  · exact B1940523
  · exact B1940527
  · exact B1940531
  · exact B1940535
  · exact B1940539
  · exact B1940543
  · exact B1940547
  · exact B1940551
  · exact B1940555
  · exact B1940559
  · exact B1940563
  · exact B1940567
  · exact B1940571
  · exact B1940575
  · exact B1940579
  · exact B1940583
  · exact B1940587
  · exact B1940591
  · exact B1940595
  · exact B1940599
  · exact B1940603
  · exact B1940607
  · exact B1940611
  · exact B1940615
  · exact B1940619
  · exact B1940623
  · exact B1940627
  · exact B1940631
  · exact B1940635
  · exact B1940639
  · exact B1940643
  · exact B1940647
  · exact B1940651
  · exact B1940655
  · exact B1940659
  · exact B1940663
  · exact B1940667
  · exact B1940671
  · exact B1940675
  · exact B1940679
  · exact B1940683
  · exact B1940687
  · exact B1940691
  · exact B1940695
  · exact B1940699
  · exact B1940703
  · exact B1940707
  · exact B1940711
  · exact B1940715
  · exact B1940719
  · exact B1940723
  · exact B1940727
  · exact B1940731
  · exact B1940735
  · exact B1940739
  · exact B1940743
  · exact B1940747
  · exact B1940751
  · exact B1940755
  · exact B1940759
  · exact B1940763
  · exact B1940767
  · exact B1940771
  · exact B1940775
  · exact B1940779
  · exact B1940783
  · exact B1940787
  · exact B1940791
  · exact B1940795
  · exact B1940799
  · exact B1940803
  · exact B1940807
  · exact B1940811
  · exact B1940815
  · exact B1940819
  · exact B1940823
  · exact B1940827
  · exact B1940831
  · exact B1940835
  · exact B1940839
  · exact B1940843
  · exact B1940847
  · exact B1940851
  · exact B1940855
  · exact B1940859
  · exact B1940863
  · exact B1940867
  · exact B1940871
  · exact B1940875
  · exact B1940879
  · exact B1940883
  · exact B1940887
  · exact B1940891
  · exact B1940895
  · exact B1940899
  · exact B1940903
  · exact B1940907
  · exact B1940911
  · exact B1940915
  · exact B1940919
  · exact B1940923
  · exact B1940927
  · exact B1940931
  · exact B1940935
  · exact B1940939
  · exact B1940943
  · exact B1940947
  · exact B1940951
  · exact B1940955
  · exact B1940959
  · exact B1940963
  · exact B1940967
  · exact B1940971
  · exact B1940975
  · exact B1940979
  · exact B1940983
  · exact B1940987
  · exact B1940991
  · exact B1940995
  · exact B1940999
  · exact B1941003
  · exact B1941007
  · exact B1941011
  · exact B1941015
  · exact B1941019
  · exact B1941023
  · exact B1941027
  · exact B1941031
  · exact B1941035
  · exact B1941039
  · exact B1941043
  · exact B1941047
  · exact B1941051
  · exact B1941055
  · exact B1941059
  · exact B1941063
  · exact B1941067
  · exact B1941071
  · exact B1941075
  · exact B1941079
  · exact B1941083
  · exact B1941087
  · exact B1941091
  · exact B1941095
  · exact B1941099
  · exact B1941103
  · exact B1941107
  · exact B1941111
  · exact B1941115
  · exact B1941119
  · exact B1941123
  · exact B1941127
  · exact B1941131
  · exact B1941135
  · exact B1941139
  · exact B1941143
  · exact B1941147
  · exact B1941151
  · exact B1941155
  · exact B1941159
  · exact B1941163
  · exact B1941167
  · exact B1941171
  · exact B1941175
  · exact B1941179
  · exact B1941183
  · exact B1941187
  · exact B1941191
  · exact B1941195
  · exact B1941199
  · exact B1941203
  · exact B1941207
  · exact B1941211
  · exact B1941215
  · exact B1941219
  · exact B1941223
  · exact B1941227
  · exact B1941231
  · exact B1941235
  · exact B1941239
  · exact B1941243
  · exact B1941247
  · exact B1941251
  · exact B1941255
  · exact B1941259
  · exact B1941263
  · exact B1941267
  · exact B1941271
  · exact B1941275
  · exact B1941279
  · exact B1941283
  · exact B1941287
  · exact B1941291
  · exact B1941295
  · exact B1941299
  · exact B1941303
  · exact B1941307
  · exact B1941311
  · exact B1941315
  · exact B1941319
  · exact B1941323
  · exact B1941327
  · exact B1941331
  · exact B1941335
  · exact B1941339
  · exact B1941343
  · exact B1941347
  · exact B1941351
  · exact B1941355
  · exact B1941359
  · exact B1941363
  · exact B1941367
  · exact B1941371
  · exact B1941375
  · exact B1941379
  · exact B1941383
  · exact B1941387
  · exact B1941391
  · exact B1941395
  · exact B1941399
  · exact B1941403
  · exact B1941407
  · exact B1941411
  · exact B1941415
  · exact B1941419
  · exact B1941423
  · exact B1941427
  · exact B1941431
  · exact B1941435
theorem solution (m : ℕ) (hlo : 1939435 ≤ m) (hhi : m ≤ 1941435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 484858 ≤ j := by omega
    have hj2 : j ≤ 485358 := by omega
    have hb : Blo 1939435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
