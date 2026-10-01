-- Prove2me | solution 1 for syracuse_descends_range_1951435_1953435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:41.694674+00:00
-- url     : https://prove2.me/submissions/15f759e4-5b08-4625-8363-e3a1995ee727

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

theorem B2195365 : Blo 1951435 2195365 := bbase (se 4 (by rfl) ⟨205815, by rfl⟩ : syracuseStep 2195365 = 411631) (by norm_num)
theorem B2927153 : Blo 1951435 2927153 := bstep (se 2 (by rfl) ⟨1097682, by rfl⟩ : syracuseStep 2927153 = 2195365) B2195365
theorem B1951435 : Blo 1951435 1951435 := bstep (se 1 (by rfl) ⟨1463576, by rfl⟩ : syracuseStep 1951435 = 2927153) B2927153
theorem B2503489 : Blo 1951435 2503489 := bbase (se 2 (by rfl) ⟨938808, by rfl⟩ : syracuseStep 2503489 = 1877617) (by norm_num)
theorem B3337985 : Blo 1951435 3337985 := bstep (se 2 (by rfl) ⟨1251744, by rfl⟩ : syracuseStep 3337985 = 2503489) B2503489
theorem B2225323 : Blo 1951435 2225323 := bstep (se 1 (by rfl) ⟨1668992, by rfl⟩ : syracuseStep 2225323 = 3337985) B3337985
theorem B11868389 : Blo 1951435 11868389 := bstep (se 4 (by rfl) ⟨1112661, by rfl⟩ : syracuseStep 11868389 = 2225323) B2225323
theorem B7912259 : Blo 1951435 7912259 := bstep (se 1 (by rfl) ⟨5934194, by rfl⟩ : syracuseStep 7912259 = 11868389) B11868389
theorem B5274839 : Blo 1951435 5274839 := bstep (se 1 (by rfl) ⟨3956129, by rfl⟩ : syracuseStep 5274839 = 7912259) B7912259
theorem B14066237 : Blo 1951435 14066237 := bstep (se 3 (by rfl) ⟨2637419, by rfl⟩ : syracuseStep 14066237 = 5274839) B5274839
theorem B9377491 : Blo 1951435 9377491 := bstep (se 1 (by rfl) ⟨7033118, by rfl⟩ : syracuseStep 9377491 = 14066237) B14066237
theorem B12503321 : Blo 1951435 12503321 := bstep (se 2 (by rfl) ⟨4688745, by rfl⟩ : syracuseStep 12503321 = 9377491) B9377491
theorem B8335547 : Blo 1951435 8335547 := bstep (se 1 (by rfl) ⟨6251660, by rfl⟩ : syracuseStep 8335547 = 12503321) B12503321
theorem B5557031 : Blo 1951435 5557031 := bstep (se 1 (by rfl) ⟨4167773, by rfl⟩ : syracuseStep 5557031 = 8335547) B8335547
theorem B3704687 : Blo 1951435 3704687 := bstep (se 1 (by rfl) ⟨2778515, by rfl⟩ : syracuseStep 3704687 = 5557031) B5557031
theorem B2469791 : Blo 1951435 2469791 := bstep (se 1 (by rfl) ⟨1852343, by rfl⟩ : syracuseStep 2469791 = 3704687) B3704687
theorem B6586109 : Blo 1951435 6586109 := bstep (se 3 (by rfl) ⟨1234895, by rfl⟩ : syracuseStep 6586109 = 2469791) B2469791
theorem B4390739 : Blo 1951435 4390739 := bstep (se 1 (by rfl) ⟨3293054, by rfl⟩ : syracuseStep 4390739 = 6586109) B6586109
theorem B2927159 : Blo 1951435 2927159 := bstep (se 1 (by rfl) ⟨2195369, by rfl⟩ : syracuseStep 2927159 = 4390739) B4390739
theorem B1951439 : Blo 1951435 1951439 := bstep (se 1 (by rfl) ⟨1463579, by rfl⟩ : syracuseStep 1951439 = 2927159) B2927159
theorem B2927165 : Blo 1951435 2927165 := bbase (se 3 (by rfl) ⟨548843, by rfl⟩ : syracuseStep 2927165 = 1097687) (by norm_num)
theorem B1951443 : Blo 1951435 1951443 := bstep (se 1 (by rfl) ⟨1463582, by rfl⟩ : syracuseStep 1951443 = 2927165) B2927165
theorem B4390757 : Blo 1951435 4390757 := bbase (se 4 (by rfl) ⟨411633, by rfl⟩ : syracuseStep 4390757 = 823267) (by norm_num)
theorem B2927171 : Blo 1951435 2927171 := bstep (se 1 (by rfl) ⟨2195378, by rfl⟩ : syracuseStep 2927171 = 4390757) B4390757
theorem B1951447 : Blo 1951435 1951447 := bstep (se 1 (by rfl) ⟨1463585, by rfl⟩ : syracuseStep 1951447 = 2927171) B2927171
theorem B4939613 : Blo 1951435 4939613 := bbase (se 3 (by rfl) ⟨926177, by rfl⟩ : syracuseStep 4939613 = 1852355) (by norm_num)
theorem B3293075 : Blo 1951435 3293075 := bstep (se 1 (by rfl) ⟨2469806, by rfl⟩ : syracuseStep 3293075 = 4939613) B4939613
theorem B2195383 : Blo 1951435 2195383 := bstep (se 1 (by rfl) ⟨1646537, by rfl⟩ : syracuseStep 2195383 = 3293075) B3293075
theorem B2927177 : Blo 1951435 2927177 := bstep (se 2 (by rfl) ⟨1097691, by rfl⟩ : syracuseStep 2927177 = 2195383) B2195383
theorem B1951451 : Blo 1951435 1951451 := bstep (se 1 (by rfl) ⟨1463588, by rfl⟩ : syracuseStep 1951451 = 2927177) B2927177
theorem B3704717 : Blo 1951435 3704717 := bbase (se 3 (by rfl) ⟨694634, by rfl⟩ : syracuseStep 3704717 = 1389269) (by norm_num)
theorem B9879245 : Blo 1951435 9879245 := bstep (se 3 (by rfl) ⟨1852358, by rfl⟩ : syracuseStep 9879245 = 3704717) B3704717
theorem B6586163 : Blo 1951435 6586163 := bstep (se 1 (by rfl) ⟨4939622, by rfl⟩ : syracuseStep 6586163 = 9879245) B9879245
theorem B4390775 : Blo 1951435 4390775 := bstep (se 1 (by rfl) ⟨3293081, by rfl⟩ : syracuseStep 4390775 = 6586163) B6586163
theorem B2927183 : Blo 1951435 2927183 := bstep (se 1 (by rfl) ⟨2195387, by rfl⟩ : syracuseStep 2927183 = 4390775) B4390775
theorem B1951455 : Blo 1951435 1951455 := bstep (se 1 (by rfl) ⟨1463591, by rfl⟩ : syracuseStep 1951455 = 2927183) B2927183
theorem B2927189 : Blo 1951435 2927189 := bbase (se 8 (by rfl) ⟨17151, by rfl⟩ : syracuseStep 2927189 = 34303) (by norm_num)
theorem B1951459 : Blo 1951435 1951459 := bstep (se 1 (by rfl) ⟨1463594, by rfl⟩ : syracuseStep 1951459 = 2927189) B2927189
theorem B7033205 : Blo 1951435 7033205 := bbase (se 5 (by rfl) ⟨329681, by rfl⟩ : syracuseStep 7033205 = 659363) (by norm_num)
theorem B4688803 : Blo 1951435 4688803 := bstep (se 1 (by rfl) ⟨3516602, by rfl⟩ : syracuseStep 4688803 = 7033205) B7033205
theorem B6251737 : Blo 1951435 6251737 := bstep (se 2 (by rfl) ⟨2344401, by rfl⟩ : syracuseStep 6251737 = 4688803) B4688803
theorem B8335649 : Blo 1951435 8335649 := bstep (se 2 (by rfl) ⟨3125868, by rfl⟩ : syracuseStep 8335649 = 6251737) B6251737
theorem B5557099 : Blo 1951435 5557099 := bstep (se 1 (by rfl) ⟨4167824, by rfl⟩ : syracuseStep 5557099 = 8335649) B8335649
theorem B7409465 : Blo 1951435 7409465 := bstep (se 2 (by rfl) ⟨2778549, by rfl⟩ : syracuseStep 7409465 = 5557099) B5557099
theorem B4939643 : Blo 1951435 4939643 := bstep (se 1 (by rfl) ⟨3704732, by rfl⟩ : syracuseStep 4939643 = 7409465) B7409465
theorem B3293095 : Blo 1951435 3293095 := bstep (se 1 (by rfl) ⟨2469821, by rfl⟩ : syracuseStep 3293095 = 4939643) B4939643
theorem B4390793 : Blo 1951435 4390793 := bstep (se 2 (by rfl) ⟨1646547, by rfl⟩ : syracuseStep 4390793 = 3293095) B3293095
theorem B2927195 : Blo 1951435 2927195 := bstep (se 1 (by rfl) ⟨2195396, by rfl⟩ : syracuseStep 2927195 = 4390793) B4390793
theorem B1951463 : Blo 1951435 1951463 := bstep (se 1 (by rfl) ⟨1463597, by rfl⟩ : syracuseStep 1951463 = 2927195) B2927195
theorem B2195401 : Blo 1951435 2195401 := bbase (se 2 (by rfl) ⟨823275, by rfl⟩ : syracuseStep 2195401 = 1646551) (by norm_num)
theorem B2927201 : Blo 1951435 2927201 := bstep (se 2 (by rfl) ⟨1097700, by rfl⟩ : syracuseStep 2927201 = 2195401) B2195401
theorem B1951467 : Blo 1951435 1951467 := bstep (se 1 (by rfl) ⟨1463600, by rfl⟩ : syracuseStep 1951467 = 2927201) B2927201
theorem B5934293 : Blo 1951435 5934293 := bbase (se 7 (by rfl) ⟨69542, by rfl⟩ : syracuseStep 5934293 = 139085) (by norm_num)
theorem B3956195 : Blo 1951435 3956195 := bstep (se 1 (by rfl) ⟨2967146, by rfl⟩ : syracuseStep 3956195 = 5934293) B5934293
theorem B2637463 : Blo 1951435 2637463 := bstep (se 1 (by rfl) ⟨1978097, by rfl⟩ : syracuseStep 2637463 = 3956195) B3956195
theorem B3516617 : Blo 1951435 3516617 := bstep (se 2 (by rfl) ⟨1318731, by rfl⟩ : syracuseStep 3516617 = 2637463) B2637463
theorem B2344411 : Blo 1951435 2344411 := bstep (se 1 (by rfl) ⟨1758308, by rfl⟩ : syracuseStep 2344411 = 3516617) B3516617
theorem B3125881 : Blo 1951435 3125881 := bstep (se 2 (by rfl) ⟨1172205, by rfl⟩ : syracuseStep 3125881 = 2344411) B2344411
theorem B16671365 : Blo 1951435 16671365 := bstep (se 4 (by rfl) ⟨1562940, by rfl⟩ : syracuseStep 16671365 = 3125881) B3125881
theorem B11114243 : Blo 1951435 11114243 := bstep (se 1 (by rfl) ⟨8335682, by rfl⟩ : syracuseStep 11114243 = 16671365) B16671365
theorem B7409495 : Blo 1951435 7409495 := bstep (se 1 (by rfl) ⟨5557121, by rfl⟩ : syracuseStep 7409495 = 11114243) B11114243
theorem B4939663 : Blo 1951435 4939663 := bstep (se 1 (by rfl) ⟨3704747, by rfl⟩ : syracuseStep 4939663 = 7409495) B7409495
theorem B6586217 : Blo 1951435 6586217 := bstep (se 2 (by rfl) ⟨2469831, by rfl⟩ : syracuseStep 6586217 = 4939663) B4939663
theorem B4390811 : Blo 1951435 4390811 := bstep (se 1 (by rfl) ⟨3293108, by rfl⟩ : syracuseStep 4390811 = 6586217) B6586217
theorem B2927207 : Blo 1951435 2927207 := bstep (se 1 (by rfl) ⟨2195405, by rfl⟩ : syracuseStep 2927207 = 4390811) B4390811
theorem B1951471 : Blo 1951435 1951471 := bstep (se 1 (by rfl) ⟨1463603, by rfl⟩ : syracuseStep 1951471 = 2927207) B2927207
theorem B2927213 : Blo 1951435 2927213 := bbase (se 3 (by rfl) ⟨548852, by rfl⟩ : syracuseStep 2927213 = 1097705) (by norm_num)
theorem B1951475 : Blo 1951435 1951475 := bstep (se 1 (by rfl) ⟨1463606, by rfl⟩ : syracuseStep 1951475 = 2927213) B2927213
theorem B4390829 : Blo 1951435 4390829 := bbase (se 3 (by rfl) ⟨823280, by rfl⟩ : syracuseStep 4390829 = 1646561) (by norm_num)
theorem B2927219 : Blo 1951435 2927219 := bstep (se 1 (by rfl) ⟨2195414, by rfl⟩ : syracuseStep 2927219 = 4390829) B4390829
theorem B1951479 : Blo 1951435 1951479 := bstep (se 1 (by rfl) ⟨1463609, by rfl⟩ : syracuseStep 1951479 = 2927219) B2927219
theorem B5557157 : Blo 1951435 5557157 := bbase (se 4 (by rfl) ⟨520983, by rfl⟩ : syracuseStep 5557157 = 1041967) (by norm_num)
theorem B3704771 : Blo 1951435 3704771 := bstep (se 1 (by rfl) ⟨2778578, by rfl⟩ : syracuseStep 3704771 = 5557157) B5557157
theorem B2469847 : Blo 1951435 2469847 := bstep (se 1 (by rfl) ⟨1852385, by rfl⟩ : syracuseStep 2469847 = 3704771) B3704771
theorem B3293129 : Blo 1951435 3293129 := bstep (se 2 (by rfl) ⟨1234923, by rfl⟩ : syracuseStep 3293129 = 2469847) B2469847
theorem B2195419 : Blo 1951435 2195419 := bstep (se 1 (by rfl) ⟨1646564, by rfl⟩ : syracuseStep 2195419 = 3293129) B3293129
theorem B2927225 : Blo 1951435 2927225 := bstep (se 2 (by rfl) ⟨1097709, by rfl⟩ : syracuseStep 2927225 = 2195419) B2195419
theorem B1951483 : Blo 1951435 1951483 := bstep (se 1 (by rfl) ⟨1463612, by rfl⟩ : syracuseStep 1951483 = 2927225) B2927225
theorem B2225377 : Blo 1951435 2225377 := bbase (se 2 (by rfl) ⟨834516, by rfl⟩ : syracuseStep 2225377 = 1669033) (by norm_num)
theorem B11868677 : Blo 1951435 11868677 := bstep (se 4 (by rfl) ⟨1112688, by rfl⟩ : syracuseStep 11868677 = 2225377) B2225377
theorem B7912451 : Blo 1951435 7912451 := bstep (se 1 (by rfl) ⟨5934338, by rfl⟩ : syracuseStep 7912451 = 11868677) B11868677
theorem B21099869 : Blo 1951435 21099869 := bstep (se 3 (by rfl) ⟨3956225, by rfl⟩ : syracuseStep 21099869 = 7912451) B7912451
theorem B14066579 : Blo 1951435 14066579 := bstep (se 1 (by rfl) ⟨10549934, by rfl⟩ : syracuseStep 14066579 = 21099869) B21099869
theorem B37510877 : Blo 1951435 37510877 := bstep (se 3 (by rfl) ⟨7033289, by rfl⟩ : syracuseStep 37510877 = 14066579) B14066579
theorem B25007251 : Blo 1951435 25007251 := bstep (se 1 (by rfl) ⟨18755438, by rfl⟩ : syracuseStep 25007251 = 37510877) B37510877
theorem B33343001 : Blo 1951435 33343001 := bstep (se 2 (by rfl) ⟨12503625, by rfl⟩ : syracuseStep 33343001 = 25007251) B25007251
theorem B22228667 : Blo 1951435 22228667 := bstep (se 1 (by rfl) ⟨16671500, by rfl⟩ : syracuseStep 22228667 = 33343001) B33343001
theorem B14819111 : Blo 1951435 14819111 := bstep (se 1 (by rfl) ⟨11114333, by rfl⟩ : syracuseStep 14819111 = 22228667) B22228667
theorem B9879407 : Blo 1951435 9879407 := bstep (se 1 (by rfl) ⟨7409555, by rfl⟩ : syracuseStep 9879407 = 14819111) B14819111
theorem B6586271 : Blo 1951435 6586271 := bstep (se 1 (by rfl) ⟨4939703, by rfl⟩ : syracuseStep 6586271 = 9879407) B9879407
theorem B4390847 : Blo 1951435 4390847 := bstep (se 1 (by rfl) ⟨3293135, by rfl⟩ : syracuseStep 4390847 = 6586271) B6586271
theorem B2927231 : Blo 1951435 2927231 := bstep (se 1 (by rfl) ⟨2195423, by rfl⟩ : syracuseStep 2927231 = 4390847) B4390847
theorem B1951487 : Blo 1951435 1951487 := bstep (se 1 (by rfl) ⟨1463615, by rfl⟩ : syracuseStep 1951487 = 2927231) B2927231
theorem B2927237 : Blo 1951435 2927237 := bbase (se 4 (by rfl) ⟨274428, by rfl⟩ : syracuseStep 2927237 = 548857) (by norm_num)
theorem B1951491 : Blo 1951435 1951491 := bstep (se 1 (by rfl) ⟨1463618, by rfl⟩ : syracuseStep 1951491 = 2927237) B2927237
theorem B3293149 : Blo 1951435 3293149 := bbase (se 3 (by rfl) ⟨617465, by rfl⟩ : syracuseStep 3293149 = 1234931) (by norm_num)
theorem B4390865 : Blo 1951435 4390865 := bstep (se 2 (by rfl) ⟨1646574, by rfl⟩ : syracuseStep 4390865 = 3293149) B3293149
theorem B2927243 : Blo 1951435 2927243 := bstep (se 1 (by rfl) ⟨2195432, by rfl⟩ : syracuseStep 2927243 = 4390865) B4390865
theorem B1951495 : Blo 1951435 1951495 := bstep (se 1 (by rfl) ⟨1463621, by rfl⟩ : syracuseStep 1951495 = 2927243) B2927243
theorem B2195437 : Blo 1951435 2195437 := bbase (se 3 (by rfl) ⟨411644, by rfl⟩ : syracuseStep 2195437 = 823289) (by norm_num)
theorem B2927249 : Blo 1951435 2927249 := bstep (se 2 (by rfl) ⟨1097718, by rfl⟩ : syracuseStep 2927249 = 2195437) B2195437
theorem B1951499 : Blo 1951435 1951499 := bstep (se 1 (by rfl) ⟨1463624, by rfl⟩ : syracuseStep 1951499 = 2927249) B2927249
theorem B6586325 : Blo 1951435 6586325 := bbase (se 7 (by rfl) ⟨77183, by rfl⟩ : syracuseStep 6586325 = 154367) (by norm_num)
theorem B4390883 : Blo 1951435 4390883 := bstep (se 1 (by rfl) ⟨3293162, by rfl⟩ : syracuseStep 4390883 = 6586325) B6586325
theorem B2927255 : Blo 1951435 2927255 := bstep (se 1 (by rfl) ⟨2195441, by rfl⟩ : syracuseStep 2927255 = 4390883) B4390883
theorem B1951503 : Blo 1951435 1951503 := bstep (se 1 (by rfl) ⟨1463627, by rfl⟩ : syracuseStep 1951503 = 2927255) B2927255
theorem B2927261 : Blo 1951435 2927261 := bbase (se 3 (by rfl) ⟨548861, by rfl⟩ : syracuseStep 2927261 = 1097723) (by norm_num)
theorem B1951507 : Blo 1951435 1951507 := bstep (se 1 (by rfl) ⟨1463630, by rfl⟩ : syracuseStep 1951507 = 2927261) B2927261
theorem B4390901 : Blo 1951435 4390901 := bbase (se 5 (by rfl) ⟨205823, by rfl⟩ : syracuseStep 4390901 = 411647) (by norm_num)
theorem B2927267 : Blo 1951435 2927267 := bstep (se 1 (by rfl) ⟨2195450, by rfl⟩ : syracuseStep 2927267 = 4390901) B4390901
theorem B1951511 : Blo 1951435 1951511 := bstep (se 1 (by rfl) ⟨1463633, by rfl⟩ : syracuseStep 1951511 = 2927267) B2927267
theorem B640917845 : Blo 1951435 640917845 := bbase (se 10 (by rfl) ⟨938844, by rfl⟩ : syracuseStep 640917845 = 1877689) (by norm_num)
theorem B427278563 : Blo 1951435 427278563 := bstep (se 1 (by rfl) ⟨320458922, by rfl⟩ : syracuseStep 427278563 = 640917845) B640917845
theorem B284852375 : Blo 1951435 284852375 := bstep (se 1 (by rfl) ⟨213639281, by rfl⟩ : syracuseStep 284852375 = 427278563) B427278563
theorem B189901583 : Blo 1951435 189901583 := bstep (se 1 (by rfl) ⟨142426187, by rfl⟩ : syracuseStep 189901583 = 284852375) B284852375
theorem B126601055 : Blo 1951435 126601055 := bstep (se 1 (by rfl) ⟨94950791, by rfl⟩ : syracuseStep 126601055 = 189901583) B189901583
theorem B84400703 : Blo 1951435 84400703 := bstep (se 1 (by rfl) ⟨63300527, by rfl⟩ : syracuseStep 84400703 = 126601055) B126601055
theorem B56267135 : Blo 1951435 56267135 := bstep (se 1 (by rfl) ⟨42200351, by rfl⟩ : syracuseStep 56267135 = 84400703) B84400703
theorem B37511423 : Blo 1951435 37511423 := bstep (se 1 (by rfl) ⟨28133567, by rfl⟩ : syracuseStep 37511423 = 56267135) B56267135
theorem B25007615 : Blo 1951435 25007615 := bstep (se 1 (by rfl) ⟨18755711, by rfl⟩ : syracuseStep 25007615 = 37511423) B37511423
theorem B16671743 : Blo 1951435 16671743 := bstep (se 1 (by rfl) ⟨12503807, by rfl⟩ : syracuseStep 16671743 = 25007615) B25007615
theorem B11114495 : Blo 1951435 11114495 := bstep (se 1 (by rfl) ⟨8335871, by rfl⟩ : syracuseStep 11114495 = 16671743) B16671743
theorem B7409663 : Blo 1951435 7409663 := bstep (se 1 (by rfl) ⟨5557247, by rfl⟩ : syracuseStep 7409663 = 11114495) B11114495
theorem B4939775 : Blo 1951435 4939775 := bstep (se 1 (by rfl) ⟨3704831, by rfl⟩ : syracuseStep 4939775 = 7409663) B7409663
theorem B3293183 : Blo 1951435 3293183 := bstep (se 1 (by rfl) ⟨2469887, by rfl⟩ : syracuseStep 3293183 = 4939775) B4939775
theorem B2195455 : Blo 1951435 2195455 := bstep (se 1 (by rfl) ⟨1646591, by rfl⟩ : syracuseStep 2195455 = 3293183) B3293183
theorem B2927273 : Blo 1951435 2927273 := bstep (se 2 (by rfl) ⟨1097727, by rfl⟩ : syracuseStep 2927273 = 2195455) B2195455
theorem B1951515 : Blo 1951435 1951515 := bstep (se 1 (by rfl) ⟨1463636, by rfl⟩ : syracuseStep 1951515 = 2927273) B2927273
theorem B2778629 : Blo 1951435 2778629 := bbase (se 4 (by rfl) ⟨260496, by rfl⟩ : syracuseStep 2778629 = 520993) (by norm_num)
theorem B7409677 : Blo 1951435 7409677 := bstep (se 3 (by rfl) ⟨1389314, by rfl⟩ : syracuseStep 7409677 = 2778629) B2778629
theorem B9879569 : Blo 1951435 9879569 := bstep (se 2 (by rfl) ⟨3704838, by rfl⟩ : syracuseStep 9879569 = 7409677) B7409677
theorem B6586379 : Blo 1951435 6586379 := bstep (se 1 (by rfl) ⟨4939784, by rfl⟩ : syracuseStep 6586379 = 9879569) B9879569
theorem B4390919 : Blo 1951435 4390919 := bstep (se 1 (by rfl) ⟨3293189, by rfl⟩ : syracuseStep 4390919 = 6586379) B6586379
theorem B2927279 : Blo 1951435 2927279 := bstep (se 1 (by rfl) ⟨2195459, by rfl⟩ : syracuseStep 2927279 = 4390919) B4390919
theorem B1951519 : Blo 1951435 1951519 := bstep (se 1 (by rfl) ⟨1463639, by rfl⟩ : syracuseStep 1951519 = 2927279) B2927279
theorem B2927285 : Blo 1951435 2927285 := bbase (se 5 (by rfl) ⟨137216, by rfl⟩ : syracuseStep 2927285 = 274433) (by norm_num)
theorem B1951523 : Blo 1951435 1951523 := bstep (se 1 (by rfl) ⟨1463642, by rfl⟩ : syracuseStep 1951523 = 2927285) B2927285
theorem B4939805 : Blo 1951435 4939805 := bbase (se 3 (by rfl) ⟨926213, by rfl⟩ : syracuseStep 4939805 = 1852427) (by norm_num)
theorem B3293203 : Blo 1951435 3293203 := bstep (se 1 (by rfl) ⟨2469902, by rfl⟩ : syracuseStep 3293203 = 4939805) B4939805
theorem B4390937 : Blo 1951435 4390937 := bstep (se 2 (by rfl) ⟨1646601, by rfl⟩ : syracuseStep 4390937 = 3293203) B3293203
theorem B2927291 : Blo 1951435 2927291 := bstep (se 1 (by rfl) ⟨2195468, by rfl⟩ : syracuseStep 2927291 = 4390937) B4390937
theorem B1951527 : Blo 1951435 1951527 := bstep (se 1 (by rfl) ⟨1463645, by rfl⟩ : syracuseStep 1951527 = 2927291) B2927291
theorem B2195473 : Blo 1951435 2195473 := bbase (se 2 (by rfl) ⟨823302, by rfl⟩ : syracuseStep 2195473 = 1646605) (by norm_num)
theorem B2927297 : Blo 1951435 2927297 := bstep (se 2 (by rfl) ⟨1097736, by rfl⟩ : syracuseStep 2927297 = 2195473) B2195473
theorem B1951531 : Blo 1951435 1951531 := bstep (se 1 (by rfl) ⟨1463648, by rfl⟩ : syracuseStep 1951531 = 2927297) B2927297
theorem B3704869 : Blo 1951435 3704869 := bbase (se 4 (by rfl) ⟨347331, by rfl⟩ : syracuseStep 3704869 = 694663) (by norm_num)
theorem B4939825 : Blo 1951435 4939825 := bstep (se 2 (by rfl) ⟨1852434, by rfl⟩ : syracuseStep 4939825 = 3704869) B3704869
theorem B6586433 : Blo 1951435 6586433 := bstep (se 2 (by rfl) ⟨2469912, by rfl⟩ : syracuseStep 6586433 = 4939825) B4939825
theorem B4390955 : Blo 1951435 4390955 := bstep (se 1 (by rfl) ⟨3293216, by rfl⟩ : syracuseStep 4390955 = 6586433) B6586433
theorem B2927303 : Blo 1951435 2927303 := bstep (se 1 (by rfl) ⟨2195477, by rfl⟩ : syracuseStep 2927303 = 4390955) B4390955
theorem B1951535 : Blo 1951435 1951535 := bstep (se 1 (by rfl) ⟨1463651, by rfl⟩ : syracuseStep 1951535 = 2927303) B2927303
theorem B2927309 : Blo 1951435 2927309 := bbase (se 3 (by rfl) ⟨548870, by rfl⟩ : syracuseStep 2927309 = 1097741) (by norm_num)
theorem B1951539 : Blo 1951435 1951539 := bstep (se 1 (by rfl) ⟨1463654, by rfl⟩ : syracuseStep 1951539 = 2927309) B2927309
theorem B4390973 : Blo 1951435 4390973 := bbase (se 3 (by rfl) ⟨823307, by rfl⟩ : syracuseStep 4390973 = 1646615) (by norm_num)
theorem B2927315 : Blo 1951435 2927315 := bstep (se 1 (by rfl) ⟨2195486, by rfl⟩ : syracuseStep 2927315 = 4390973) B4390973
theorem B1951543 : Blo 1951435 1951543 := bstep (se 1 (by rfl) ⟨1463657, by rfl⟩ : syracuseStep 1951543 = 2927315) B2927315
theorem B3293237 : Blo 1951435 3293237 := bbase (se 5 (by rfl) ⟨154370, by rfl⟩ : syracuseStep 3293237 = 308741) (by norm_num)
theorem B2195491 : Blo 1951435 2195491 := bstep (se 1 (by rfl) ⟨1646618, by rfl⟩ : syracuseStep 2195491 = 3293237) B3293237
theorem B2927321 : Blo 1951435 2927321 := bstep (se 2 (by rfl) ⟨1097745, by rfl⟩ : syracuseStep 2927321 = 2195491) B2195491
theorem B1951547 : Blo 1951435 1951547 := bstep (se 1 (by rfl) ⟨1463660, by rfl⟩ : syracuseStep 1951547 = 2927321) B2927321
theorem B5557349 : Blo 1951435 5557349 := bbase (se 4 (by rfl) ⟨521001, by rfl⟩ : syracuseStep 5557349 = 1042003) (by norm_num)
theorem B14819597 : Blo 1951435 14819597 := bstep (se 3 (by rfl) ⟨2778674, by rfl⟩ : syracuseStep 14819597 = 5557349) B5557349
theorem B9879731 : Blo 1951435 9879731 := bstep (se 1 (by rfl) ⟨7409798, by rfl⟩ : syracuseStep 9879731 = 14819597) B14819597
theorem B6586487 : Blo 1951435 6586487 := bstep (se 1 (by rfl) ⟨4939865, by rfl⟩ : syracuseStep 6586487 = 9879731) B9879731
theorem B4390991 : Blo 1951435 4390991 := bstep (se 1 (by rfl) ⟨3293243, by rfl⟩ : syracuseStep 4390991 = 6586487) B6586487
theorem B2927327 : Blo 1951435 2927327 := bstep (se 1 (by rfl) ⟨2195495, by rfl⟩ : syracuseStep 2927327 = 4390991) B4390991
theorem B1951551 : Blo 1951435 1951551 := bstep (se 1 (by rfl) ⟨1463663, by rfl⟩ : syracuseStep 1951551 = 2927327) B2927327
theorem B2927333 : Blo 1951435 2927333 := bbase (se 4 (by rfl) ⟨274437, by rfl⟩ : syracuseStep 2927333 = 548875) (by norm_num)
theorem B1951555 : Blo 1951435 1951555 := bstep (se 1 (by rfl) ⟨1463666, by rfl⟩ : syracuseStep 1951555 = 2927333) B2927333
theorem B2225461 : Blo 1951435 2225461 := bbase (se 5 (by rfl) ⟨104318, by rfl⟩ : syracuseStep 2225461 = 208637) (by norm_num)
theorem B2967281 : Blo 1951435 2967281 := bstep (se 2 (by rfl) ⟨1112730, by rfl⟩ : syracuseStep 2967281 = 2225461) B2225461
theorem B1978187 : Blo 1951435 1978187 := bstep (se 1 (by rfl) ⟨1483640, by rfl⟩ : syracuseStep 1978187 = 2967281) B2967281
theorem B5275165 : Blo 1951435 5275165 := bstep (se 3 (by rfl) ⟨989093, by rfl⟩ : syracuseStep 5275165 = 1978187) B1978187
theorem B7033553 : Blo 1951435 7033553 := bstep (se 2 (by rfl) ⟨2637582, by rfl⟩ : syracuseStep 7033553 = 5275165) B5275165
theorem B4689035 : Blo 1951435 4689035 := bstep (se 1 (by rfl) ⟨3516776, by rfl⟩ : syracuseStep 4689035 = 7033553) B7033553
theorem B3126023 : Blo 1951435 3126023 := bstep (se 1 (by rfl) ⟨2344517, by rfl⟩ : syracuseStep 3126023 = 4689035) B4689035
theorem B2084015 : Blo 1951435 2084015 := bstep (se 1 (by rfl) ⟨1563011, by rfl⟩ : syracuseStep 2084015 = 3126023) B3126023
theorem B5557373 : Blo 1951435 5557373 := bstep (se 3 (by rfl) ⟨1042007, by rfl⟩ : syracuseStep 5557373 = 2084015) B2084015
theorem B3704915 : Blo 1951435 3704915 := bstep (se 1 (by rfl) ⟨2778686, by rfl⟩ : syracuseStep 3704915 = 5557373) B5557373
theorem B2469943 : Blo 1951435 2469943 := bstep (se 1 (by rfl) ⟨1852457, by rfl⟩ : syracuseStep 2469943 = 3704915) B3704915
theorem B3293257 : Blo 1951435 3293257 := bstep (se 2 (by rfl) ⟨1234971, by rfl⟩ : syracuseStep 3293257 = 2469943) B2469943
theorem B4391009 : Blo 1951435 4391009 := bstep (se 2 (by rfl) ⟨1646628, by rfl⟩ : syracuseStep 4391009 = 3293257) B3293257
theorem B2927339 : Blo 1951435 2927339 := bstep (se 1 (by rfl) ⟨2195504, by rfl⟩ : syracuseStep 2927339 = 4391009) B4391009
theorem B1951559 : Blo 1951435 1951559 := bstep (se 1 (by rfl) ⟨1463669, by rfl⟩ : syracuseStep 1951559 = 2927339) B2927339
theorem B2195509 : Blo 1951435 2195509 := bbase (se 5 (by rfl) ⟨102914, by rfl⟩ : syracuseStep 2195509 = 205829) (by norm_num)
theorem B2927345 : Blo 1951435 2927345 := bstep (se 2 (by rfl) ⟨1097754, by rfl⟩ : syracuseStep 2927345 = 2195509) B2195509
theorem B1951563 : Blo 1951435 1951563 := bstep (se 1 (by rfl) ⟨1463672, by rfl⟩ : syracuseStep 1951563 = 2927345) B2927345
theorem B2469953 : Blo 1951435 2469953 := bbase (se 2 (by rfl) ⟨926232, by rfl⟩ : syracuseStep 2469953 = 1852465) (by norm_num)
theorem B6586541 : Blo 1951435 6586541 := bstep (se 3 (by rfl) ⟨1234976, by rfl⟩ : syracuseStep 6586541 = 2469953) B2469953
theorem B4391027 : Blo 1951435 4391027 := bstep (se 1 (by rfl) ⟨3293270, by rfl⟩ : syracuseStep 4391027 = 6586541) B6586541
theorem B2927351 : Blo 1951435 2927351 := bstep (se 1 (by rfl) ⟨2195513, by rfl⟩ : syracuseStep 2927351 = 4391027) B4391027
theorem B1951567 : Blo 1951435 1951567 := bstep (se 1 (by rfl) ⟨1463675, by rfl⟩ : syracuseStep 1951567 = 2927351) B2927351
theorem B2927357 : Blo 1951435 2927357 := bbase (se 3 (by rfl) ⟨548879, by rfl⟩ : syracuseStep 2927357 = 1097759) (by norm_num)
theorem B1951571 : Blo 1951435 1951571 := bstep (se 1 (by rfl) ⟨1463678, by rfl⟩ : syracuseStep 1951571 = 2927357) B2927357
theorem B4391045 : Blo 1951435 4391045 := bbase (se 4 (by rfl) ⟨411660, by rfl⟩ : syracuseStep 4391045 = 823321) (by norm_num)
theorem B2927363 : Blo 1951435 2927363 := bstep (se 1 (by rfl) ⟨2195522, by rfl⟩ : syracuseStep 2927363 = 4391045) B4391045
theorem B1951575 : Blo 1951435 1951575 := bstep (se 1 (by rfl) ⟨1463681, by rfl⟩ : syracuseStep 1951575 = 2927363) B2927363
theorem B10014677 : Blo 1951435 10014677 := bbase (se 7 (by rfl) ⟨117359, by rfl⟩ : syracuseStep 10014677 = 234719) (by norm_num)
theorem B6676451 : Blo 1951435 6676451 := bstep (se 1 (by rfl) ⟨5007338, by rfl⟩ : syracuseStep 6676451 = 10014677) B10014677
theorem B4450967 : Blo 1951435 4450967 := bstep (se 1 (by rfl) ⟨3338225, by rfl⟩ : syracuseStep 4450967 = 6676451) B6676451
theorem B2967311 : Blo 1951435 2967311 := bstep (se 1 (by rfl) ⟨2225483, by rfl⟩ : syracuseStep 2967311 = 4450967) B4450967
theorem B7912829 : Blo 1951435 7912829 := bstep (se 3 (by rfl) ⟨1483655, by rfl⟩ : syracuseStep 7912829 = 2967311) B2967311
theorem B5275219 : Blo 1951435 5275219 := bstep (se 1 (by rfl) ⟨3956414, by rfl⟩ : syracuseStep 5275219 = 7912829) B7912829
theorem B7033625 : Blo 1951435 7033625 := bstep (se 2 (by rfl) ⟨2637609, by rfl⟩ : syracuseStep 7033625 = 5275219) B5275219
theorem B4689083 : Blo 1951435 4689083 := bstep (se 1 (by rfl) ⟨3516812, by rfl⟩ : syracuseStep 4689083 = 7033625) B7033625
theorem B3126055 : Blo 1951435 3126055 := bstep (se 1 (by rfl) ⟨2344541, by rfl⟩ : syracuseStep 3126055 = 4689083) B4689083
theorem B4168073 : Blo 1951435 4168073 := bstep (se 2 (by rfl) ⟨1563027, by rfl⟩ : syracuseStep 4168073 = 3126055) B3126055
theorem B2778715 : Blo 1951435 2778715 := bstep (se 1 (by rfl) ⟨2084036, by rfl⟩ : syracuseStep 2778715 = 4168073) B4168073
theorem B3704953 : Blo 1951435 3704953 := bstep (se 2 (by rfl) ⟨1389357, by rfl⟩ : syracuseStep 3704953 = 2778715) B2778715
theorem B4939937 : Blo 1951435 4939937 := bstep (se 2 (by rfl) ⟨1852476, by rfl⟩ : syracuseStep 4939937 = 3704953) B3704953
theorem B3293291 : Blo 1951435 3293291 := bstep (se 1 (by rfl) ⟨2469968, by rfl⟩ : syracuseStep 3293291 = 4939937) B4939937
theorem B2195527 : Blo 1951435 2195527 := bstep (se 1 (by rfl) ⟨1646645, by rfl⟩ : syracuseStep 2195527 = 3293291) B3293291
theorem B2927369 : Blo 1951435 2927369 := bstep (se 2 (by rfl) ⟨1097763, by rfl⟩ : syracuseStep 2927369 = 2195527) B2195527
theorem B1951579 : Blo 1951435 1951579 := bstep (se 1 (by rfl) ⟨1463684, by rfl⟩ : syracuseStep 1951579 = 2927369) B2927369
theorem B9879893 : Blo 1951435 9879893 := bbase (se 10 (by rfl) ⟨14472, by rfl⟩ : syracuseStep 9879893 = 28945) (by norm_num)
theorem B6586595 : Blo 1951435 6586595 := bstep (se 1 (by rfl) ⟨4939946, by rfl⟩ : syracuseStep 6586595 = 9879893) B9879893
theorem B4391063 : Blo 1951435 4391063 := bstep (se 1 (by rfl) ⟨3293297, by rfl⟩ : syracuseStep 4391063 = 6586595) B6586595
theorem B2927375 : Blo 1951435 2927375 := bstep (se 1 (by rfl) ⟨2195531, by rfl⟩ : syracuseStep 2927375 = 4391063) B4391063
theorem B1951583 : Blo 1951435 1951583 := bstep (se 1 (by rfl) ⟨1463687, by rfl⟩ : syracuseStep 1951583 = 2927375) B2927375
theorem B2927381 : Blo 1951435 2927381 := bbase (se 6 (by rfl) ⟨68610, by rfl⟩ : syracuseStep 2927381 = 137221) (by norm_num)
theorem B1951587 : Blo 1951435 1951587 := bstep (se 1 (by rfl) ⟨1463690, by rfl⟩ : syracuseStep 1951587 = 2927381) B2927381
theorem B3956437 : Blo 1951435 3956437 := bbase (se 7 (by rfl) ⟨46364, by rfl⟩ : syracuseStep 3956437 = 92729) (by norm_num)
theorem B5275249 : Blo 1951435 5275249 := bstep (se 2 (by rfl) ⟨1978218, by rfl⟩ : syracuseStep 5275249 = 3956437) B3956437
theorem B28134661 : Blo 1951435 28134661 := bstep (se 4 (by rfl) ⟨2637624, by rfl⟩ : syracuseStep 28134661 = 5275249) B5275249
theorem B37512881 : Blo 1951435 37512881 := bstep (se 2 (by rfl) ⟨14067330, by rfl⟩ : syracuseStep 37512881 = 28134661) B28134661
theorem B25008587 : Blo 1951435 25008587 := bstep (se 1 (by rfl) ⟨18756440, by rfl⟩ : syracuseStep 25008587 = 37512881) B37512881
theorem B16672391 : Blo 1951435 16672391 := bstep (se 1 (by rfl) ⟨12504293, by rfl⟩ : syracuseStep 16672391 = 25008587) B25008587
theorem B11114927 : Blo 1951435 11114927 := bstep (se 1 (by rfl) ⟨8336195, by rfl⟩ : syracuseStep 11114927 = 16672391) B16672391
theorem B7409951 : Blo 1951435 7409951 := bstep (se 1 (by rfl) ⟨5557463, by rfl⟩ : syracuseStep 7409951 = 11114927) B11114927
theorem B4939967 : Blo 1951435 4939967 := bstep (se 1 (by rfl) ⟨3704975, by rfl⟩ : syracuseStep 4939967 = 7409951) B7409951
theorem B3293311 : Blo 1951435 3293311 := bstep (se 1 (by rfl) ⟨2469983, by rfl⟩ : syracuseStep 3293311 = 4939967) B4939967
theorem B4391081 : Blo 1951435 4391081 := bstep (se 2 (by rfl) ⟨1646655, by rfl⟩ : syracuseStep 4391081 = 3293311) B3293311
theorem B2927387 : Blo 1951435 2927387 := bstep (se 1 (by rfl) ⟨2195540, by rfl⟩ : syracuseStep 2927387 = 4391081) B4391081
theorem B1951591 : Blo 1951435 1951591 := bstep (se 1 (by rfl) ⟨1463693, by rfl⟩ : syracuseStep 1951591 = 2927387) B2927387
theorem B2195545 : Blo 1951435 2195545 := bbase (se 2 (by rfl) ⟨823329, by rfl⟩ : syracuseStep 2195545 = 1646659) (by norm_num)
theorem B2927393 : Blo 1951435 2927393 := bstep (se 2 (by rfl) ⟨1097772, by rfl⟩ : syracuseStep 2927393 = 2195545) B2195545
theorem B1951595 : Blo 1951435 1951595 := bstep (se 1 (by rfl) ⟨1463696, by rfl⟩ : syracuseStep 1951595 = 2927393) B2927393
theorem B2344565 : Blo 1951435 2344565 := bbase (se 5 (by rfl) ⟨109901, by rfl⟩ : syracuseStep 2344565 = 219803) (by norm_num)
theorem B6252173 : Blo 1951435 6252173 := bstep (se 3 (by rfl) ⟨1172282, by rfl⟩ : syracuseStep 6252173 = 2344565) B2344565
theorem B4168115 : Blo 1951435 4168115 := bstep (se 1 (by rfl) ⟨3126086, by rfl⟩ : syracuseStep 4168115 = 6252173) B6252173
theorem B2778743 : Blo 1951435 2778743 := bstep (se 1 (by rfl) ⟨2084057, by rfl⟩ : syracuseStep 2778743 = 4168115) B4168115
theorem B7409981 : Blo 1951435 7409981 := bstep (se 3 (by rfl) ⟨1389371, by rfl⟩ : syracuseStep 7409981 = 2778743) B2778743
theorem B4939987 : Blo 1951435 4939987 := bstep (se 1 (by rfl) ⟨3704990, by rfl⟩ : syracuseStep 4939987 = 7409981) B7409981
theorem B6586649 : Blo 1951435 6586649 := bstep (se 2 (by rfl) ⟨2469993, by rfl⟩ : syracuseStep 6586649 = 4939987) B4939987
theorem B4391099 : Blo 1951435 4391099 := bstep (se 1 (by rfl) ⟨3293324, by rfl⟩ : syracuseStep 4391099 = 6586649) B6586649
theorem B2927399 : Blo 1951435 2927399 := bstep (se 1 (by rfl) ⟨2195549, by rfl⟩ : syracuseStep 2927399 = 4391099) B4391099
theorem B1951599 : Blo 1951435 1951599 := bstep (se 1 (by rfl) ⟨1463699, by rfl⟩ : syracuseStep 1951599 = 2927399) B2927399
theorem B2927405 : Blo 1951435 2927405 := bbase (se 3 (by rfl) ⟨548888, by rfl⟩ : syracuseStep 2927405 = 1097777) (by norm_num)
theorem B1951603 : Blo 1951435 1951603 := bstep (se 1 (by rfl) ⟨1463702, by rfl⟩ : syracuseStep 1951603 = 2927405) B2927405
theorem B4391117 : Blo 1951435 4391117 := bbase (se 3 (by rfl) ⟨823334, by rfl⟩ : syracuseStep 4391117 = 1646669) (by norm_num)
theorem B2927411 : Blo 1951435 2927411 := bstep (se 1 (by rfl) ⟨2195558, by rfl⟩ : syracuseStep 2927411 = 4391117) B4391117
theorem B1951607 : Blo 1951435 1951607 := bstep (se 1 (by rfl) ⟨1463705, by rfl⟩ : syracuseStep 1951607 = 2927411) B2927411
theorem B2470009 : Blo 1951435 2470009 := bbase (se 2 (by rfl) ⟨926253, by rfl⟩ : syracuseStep 2470009 = 1852507) (by norm_num)
theorem B3293345 : Blo 1951435 3293345 := bstep (se 2 (by rfl) ⟨1235004, by rfl⟩ : syracuseStep 3293345 = 2470009) B2470009
theorem B2195563 : Blo 1951435 2195563 := bstep (se 1 (by rfl) ⟨1646672, by rfl⟩ : syracuseStep 2195563 = 3293345) B3293345
theorem B2927417 : Blo 1951435 2927417 := bstep (se 2 (by rfl) ⟨1097781, by rfl⟩ : syracuseStep 2927417 = 2195563) B2195563
theorem B1951611 : Blo 1951435 1951611 := bstep (se 1 (by rfl) ⟨1463708, by rfl⟩ : syracuseStep 1951611 = 2927417) B2927417
theorem B7511141 : Blo 1951435 7511141 := bbase (se 4 (by rfl) ⟨704169, by rfl⟩ : syracuseStep 7511141 = 1408339) (by norm_num)
theorem B5007427 : Blo 1951435 5007427 := bstep (se 1 (by rfl) ⟨3755570, by rfl⟩ : syracuseStep 5007427 = 7511141) B7511141
theorem B26706277 : Blo 1951435 26706277 := bstep (se 4 (by rfl) ⟨2503713, by rfl⟩ : syracuseStep 26706277 = 5007427) B5007427
theorem B35608369 : Blo 1951435 35608369 := bstep (se 2 (by rfl) ⟨13353138, by rfl⟩ : syracuseStep 35608369 = 26706277) B26706277
theorem B47477825 : Blo 1951435 47477825 := bstep (se 2 (by rfl) ⟨17804184, by rfl⟩ : syracuseStep 47477825 = 35608369) B35608369
theorem B31651883 : Blo 1951435 31651883 := bstep (se 1 (by rfl) ⟨23738912, by rfl⟩ : syracuseStep 31651883 = 47477825) B47477825
theorem B21101255 : Blo 1951435 21101255 := bstep (se 1 (by rfl) ⟨15825941, by rfl⟩ : syracuseStep 21101255 = 31651883) B31651883
theorem B14067503 : Blo 1951435 14067503 := bstep (se 1 (by rfl) ⟨10550627, by rfl⟩ : syracuseStep 14067503 = 21101255) B21101255
theorem B9378335 : Blo 1951435 9378335 := bstep (se 1 (by rfl) ⟨7033751, by rfl⟩ : syracuseStep 9378335 = 14067503) B14067503
theorem B6252223 : Blo 1951435 6252223 := bstep (se 1 (by rfl) ⟨4689167, by rfl⟩ : syracuseStep 6252223 = 9378335) B9378335
theorem B8336297 : Blo 1951435 8336297 := bstep (se 2 (by rfl) ⟨3126111, by rfl⟩ : syracuseStep 8336297 = 6252223) B6252223
theorem B22230125 : Blo 1951435 22230125 := bstep (se 3 (by rfl) ⟨4168148, by rfl⟩ : syracuseStep 22230125 = 8336297) B8336297
theorem B14820083 : Blo 1951435 14820083 := bstep (se 1 (by rfl) ⟨11115062, by rfl⟩ : syracuseStep 14820083 = 22230125) B22230125
theorem B9880055 : Blo 1951435 9880055 := bstep (se 1 (by rfl) ⟨7410041, by rfl⟩ : syracuseStep 9880055 = 14820083) B14820083
theorem B6586703 : Blo 1951435 6586703 := bstep (se 1 (by rfl) ⟨4940027, by rfl⟩ : syracuseStep 6586703 = 9880055) B9880055
theorem B4391135 : Blo 1951435 4391135 := bstep (se 1 (by rfl) ⟨3293351, by rfl⟩ : syracuseStep 4391135 = 6586703) B6586703
theorem B2927423 : Blo 1951435 2927423 := bstep (se 1 (by rfl) ⟨2195567, by rfl⟩ : syracuseStep 2927423 = 4391135) B4391135
theorem B1951615 : Blo 1951435 1951615 := bstep (se 1 (by rfl) ⟨1463711, by rfl⟩ : syracuseStep 1951615 = 2927423) B2927423
theorem B2927429 : Blo 1951435 2927429 := bbase (se 4 (by rfl) ⟨274446, by rfl⟩ : syracuseStep 2927429 = 548893) (by norm_num)
theorem B1951619 : Blo 1951435 1951619 := bstep (se 1 (by rfl) ⟨1463714, by rfl⟩ : syracuseStep 1951619 = 2927429) B2927429
theorem B3293365 : Blo 1951435 3293365 := bbase (se 5 (by rfl) ⟨154376, by rfl⟩ : syracuseStep 3293365 = 308753) (by norm_num)
theorem B4391153 : Blo 1951435 4391153 := bstep (se 2 (by rfl) ⟨1646682, by rfl⟩ : syracuseStep 4391153 = 3293365) B3293365
theorem B2927435 : Blo 1951435 2927435 := bstep (se 1 (by rfl) ⟨2195576, by rfl⟩ : syracuseStep 2927435 = 4391153) B4391153
theorem B1951623 : Blo 1951435 1951623 := bstep (se 1 (by rfl) ⟨1463717, by rfl⟩ : syracuseStep 1951623 = 2927435) B2927435
theorem B2195581 : Blo 1951435 2195581 := bbase (se 3 (by rfl) ⟨411671, by rfl⟩ : syracuseStep 2195581 = 823343) (by norm_num)
theorem B2927441 : Blo 1951435 2927441 := bstep (se 2 (by rfl) ⟨1097790, by rfl⟩ : syracuseStep 2927441 = 2195581) B2195581
theorem B1951627 : Blo 1951435 1951627 := bstep (se 1 (by rfl) ⟨1463720, by rfl⟩ : syracuseStep 1951627 = 2927441) B2927441
theorem B6586757 : Blo 1951435 6586757 := bbase (se 4 (by rfl) ⟨617508, by rfl⟩ : syracuseStep 6586757 = 1235017) (by norm_num)
theorem B4391171 : Blo 1951435 4391171 := bstep (se 1 (by rfl) ⟨3293378, by rfl⟩ : syracuseStep 4391171 = 6586757) B6586757
theorem B2927447 : Blo 1951435 2927447 := bstep (se 1 (by rfl) ⟨2195585, by rfl⟩ : syracuseStep 2927447 = 4391171) B4391171
theorem B1951631 : Blo 1951435 1951631 := bstep (se 1 (by rfl) ⟨1463723, by rfl⟩ : syracuseStep 1951631 = 2927447) B2927447
theorem B2927453 : Blo 1951435 2927453 := bbase (se 3 (by rfl) ⟨548897, by rfl⟩ : syracuseStep 2927453 = 1097795) (by norm_num)
theorem B1951635 : Blo 1951435 1951635 := bstep (se 1 (by rfl) ⟨1463726, by rfl⟩ : syracuseStep 1951635 = 2927453) B2927453
theorem B4391189 : Blo 1951435 4391189 := bbase (se 6 (by rfl) ⟨102918, by rfl⟩ : syracuseStep 4391189 = 205837) (by norm_num)
theorem B2927459 : Blo 1951435 2927459 := bstep (se 1 (by rfl) ⟨2195594, by rfl⟩ : syracuseStep 2927459 = 4391189) B4391189
theorem B1951639 : Blo 1951435 1951639 := bstep (se 1 (by rfl) ⟨1463729, by rfl⟩ : syracuseStep 1951639 = 2927459) B2927459
theorem B7410149 : Blo 1951435 7410149 := bbase (se 4 (by rfl) ⟨694701, by rfl⟩ : syracuseStep 7410149 = 1389403) (by norm_num)
theorem B4940099 : Blo 1951435 4940099 := bstep (se 1 (by rfl) ⟨3705074, by rfl⟩ : syracuseStep 4940099 = 7410149) B7410149
theorem B3293399 : Blo 1951435 3293399 := bstep (se 1 (by rfl) ⟨2470049, by rfl⟩ : syracuseStep 3293399 = 4940099) B4940099
theorem B2195599 : Blo 1951435 2195599 := bstep (se 1 (by rfl) ⟨1646699, by rfl⟩ : syracuseStep 2195599 = 3293399) B3293399
theorem B2927465 : Blo 1951435 2927465 := bstep (se 2 (by rfl) ⟨1097799, by rfl⟩ : syracuseStep 2927465 = 2195599) B2195599
theorem B1951643 : Blo 1951435 1951643 := bstep (se 1 (by rfl) ⟨1463732, by rfl⟩ : syracuseStep 1951643 = 2927465) B2927465
theorem B4689245 : Blo 1951435 4689245 := bbase (se 3 (by rfl) ⟨879233, by rfl⟩ : syracuseStep 4689245 = 1758467) (by norm_num)
theorem B3126163 : Blo 1951435 3126163 := bstep (se 1 (by rfl) ⟨2344622, by rfl⟩ : syracuseStep 3126163 = 4689245) B4689245
theorem B4168217 : Blo 1951435 4168217 := bstep (se 2 (by rfl) ⟨1563081, by rfl⟩ : syracuseStep 4168217 = 3126163) B3126163
theorem B11115245 : Blo 1951435 11115245 := bstep (se 3 (by rfl) ⟨2084108, by rfl⟩ : syracuseStep 11115245 = 4168217) B4168217
theorem B7410163 : Blo 1951435 7410163 := bstep (se 1 (by rfl) ⟨5557622, by rfl⟩ : syracuseStep 7410163 = 11115245) B11115245
theorem B9880217 : Blo 1951435 9880217 := bstep (se 2 (by rfl) ⟨3705081, by rfl⟩ : syracuseStep 9880217 = 7410163) B7410163
theorem B6586811 : Blo 1951435 6586811 := bstep (se 1 (by rfl) ⟨4940108, by rfl⟩ : syracuseStep 6586811 = 9880217) B9880217
theorem B4391207 : Blo 1951435 4391207 := bstep (se 1 (by rfl) ⟨3293405, by rfl⟩ : syracuseStep 4391207 = 6586811) B6586811
theorem B2927471 : Blo 1951435 2927471 := bstep (se 1 (by rfl) ⟨2195603, by rfl⟩ : syracuseStep 2927471 = 4391207) B4391207
theorem B1951647 : Blo 1951435 1951647 := bstep (se 1 (by rfl) ⟨1463735, by rfl⟩ : syracuseStep 1951647 = 2927471) B2927471
theorem B2927477 : Blo 1951435 2927477 := bbase (se 5 (by rfl) ⟨137225, by rfl⟩ : syracuseStep 2927477 = 274451) (by norm_num)
theorem B1951651 : Blo 1951435 1951651 := bstep (se 1 (by rfl) ⟨1463738, by rfl⟩ : syracuseStep 1951651 = 2927477) B2927477
theorem B3516949 : Blo 1951435 3516949 := bbase (se 6 (by rfl) ⟨82428, by rfl⟩ : syracuseStep 3516949 = 164857) (by norm_num)
theorem B4689265 : Blo 1951435 4689265 := bstep (se 2 (by rfl) ⟨1758474, by rfl⟩ : syracuseStep 4689265 = 3516949) B3516949
theorem B6252353 : Blo 1951435 6252353 := bstep (se 2 (by rfl) ⟨2344632, by rfl⟩ : syracuseStep 6252353 = 4689265) B4689265
theorem B4168235 : Blo 1951435 4168235 := bstep (se 1 (by rfl) ⟨3126176, by rfl⟩ : syracuseStep 4168235 = 6252353) B6252353
theorem B2778823 : Blo 1951435 2778823 := bstep (se 1 (by rfl) ⟨2084117, by rfl⟩ : syracuseStep 2778823 = 4168235) B4168235
theorem B3705097 : Blo 1951435 3705097 := bstep (se 2 (by rfl) ⟨1389411, by rfl⟩ : syracuseStep 3705097 = 2778823) B2778823
theorem B4940129 : Blo 1951435 4940129 := bstep (se 2 (by rfl) ⟨1852548, by rfl⟩ : syracuseStep 4940129 = 3705097) B3705097
theorem B3293419 : Blo 1951435 3293419 := bstep (se 1 (by rfl) ⟨2470064, by rfl⟩ : syracuseStep 3293419 = 4940129) B4940129
theorem B4391225 : Blo 1951435 4391225 := bstep (se 2 (by rfl) ⟨1646709, by rfl⟩ : syracuseStep 4391225 = 3293419) B3293419
theorem B2927483 : Blo 1951435 2927483 := bstep (se 1 (by rfl) ⟨2195612, by rfl⟩ : syracuseStep 2927483 = 4391225) B4391225
theorem B1951655 : Blo 1951435 1951655 := bstep (se 1 (by rfl) ⟨1463741, by rfl⟩ : syracuseStep 1951655 = 2927483) B2927483
theorem B2195617 : Blo 1951435 2195617 := bbase (se 2 (by rfl) ⟨823356, by rfl⟩ : syracuseStep 2195617 = 1646713) (by norm_num)
theorem B2927489 : Blo 1951435 2927489 := bstep (se 2 (by rfl) ⟨1097808, by rfl⟩ : syracuseStep 2927489 = 2195617) B2195617
theorem B1951659 : Blo 1951435 1951659 := bstep (se 1 (by rfl) ⟨1463744, by rfl⟩ : syracuseStep 1951659 = 2927489) B2927489
theorem B4940149 : Blo 1951435 4940149 := bbase (se 5 (by rfl) ⟨231569, by rfl⟩ : syracuseStep 4940149 = 463139) (by norm_num)
theorem B6586865 : Blo 1951435 6586865 := bstep (se 2 (by rfl) ⟨2470074, by rfl⟩ : syracuseStep 6586865 = 4940149) B4940149
theorem B4391243 : Blo 1951435 4391243 := bstep (se 1 (by rfl) ⟨3293432, by rfl⟩ : syracuseStep 4391243 = 6586865) B6586865
theorem B2927495 : Blo 1951435 2927495 := bstep (se 1 (by rfl) ⟨2195621, by rfl⟩ : syracuseStep 2927495 = 4391243) B4391243
theorem B1951663 : Blo 1951435 1951663 := bstep (se 1 (by rfl) ⟨1463747, by rfl⟩ : syracuseStep 1951663 = 2927495) B2927495
theorem B2927501 : Blo 1951435 2927501 := bbase (se 3 (by rfl) ⟨548906, by rfl⟩ : syracuseStep 2927501 = 1097813) (by norm_num)
theorem B1951667 : Blo 1951435 1951667 := bstep (se 1 (by rfl) ⟨1463750, by rfl⟩ : syracuseStep 1951667 = 2927501) B2927501
theorem B4391261 : Blo 1951435 4391261 := bbase (se 3 (by rfl) ⟨823361, by rfl⟩ : syracuseStep 4391261 = 1646723) (by norm_num)
theorem B2927507 : Blo 1951435 2927507 := bstep (se 1 (by rfl) ⟨2195630, by rfl⟩ : syracuseStep 2927507 = 4391261) B4391261
theorem B1951671 : Blo 1951435 1951671 := bstep (se 1 (by rfl) ⟨1463753, by rfl⟩ : syracuseStep 1951671 = 2927507) B2927507
theorem B3293453 : Blo 1951435 3293453 := bbase (se 3 (by rfl) ⟨617522, by rfl⟩ : syracuseStep 3293453 = 1235045) (by norm_num)
theorem B2195635 : Blo 1951435 2195635 := bstep (se 1 (by rfl) ⟨1646726, by rfl⟩ : syracuseStep 2195635 = 3293453) B3293453
theorem B2927513 : Blo 1951435 2927513 := bstep (se 2 (by rfl) ⟨1097817, by rfl⟩ : syracuseStep 2927513 = 2195635) B2195635
theorem B1951675 : Blo 1951435 1951675 := bstep (se 1 (by rfl) ⟨1463756, by rfl⟩ : syracuseStep 1951675 = 2927513) B2927513
theorem B16673141 : Blo 1951435 16673141 := bbase (se 5 (by rfl) ⟨781553, by rfl⟩ : syracuseStep 16673141 = 1563107) (by norm_num)
theorem B11115427 : Blo 1951435 11115427 := bstep (se 1 (by rfl) ⟨8336570, by rfl⟩ : syracuseStep 11115427 = 16673141) B16673141
theorem B14820569 : Blo 1951435 14820569 := bstep (se 2 (by rfl) ⟨5557713, by rfl⟩ : syracuseStep 14820569 = 11115427) B11115427
theorem B9880379 : Blo 1951435 9880379 := bstep (se 1 (by rfl) ⟨7410284, by rfl⟩ : syracuseStep 9880379 = 14820569) B14820569
theorem B6586919 : Blo 1951435 6586919 := bstep (se 1 (by rfl) ⟨4940189, by rfl⟩ : syracuseStep 6586919 = 9880379) B9880379
theorem B4391279 : Blo 1951435 4391279 := bstep (se 1 (by rfl) ⟨3293459, by rfl⟩ : syracuseStep 4391279 = 6586919) B6586919
theorem B2927519 : Blo 1951435 2927519 := bstep (se 1 (by rfl) ⟨2195639, by rfl⟩ : syracuseStep 2927519 = 4391279) B4391279
theorem B1951679 : Blo 1951435 1951679 := bstep (se 1 (by rfl) ⟨1463759, by rfl⟩ : syracuseStep 1951679 = 2927519) B2927519
theorem B2927525 : Blo 1951435 2927525 := bbase (se 4 (by rfl) ⟨274455, by rfl⟩ : syracuseStep 2927525 = 548911) (by norm_num)
theorem B1951683 : Blo 1951435 1951683 := bstep (se 1 (by rfl) ⟨1463762, by rfl⟩ : syracuseStep 1951683 = 2927525) B2927525
theorem B2470105 : Blo 1951435 2470105 := bbase (se 2 (by rfl) ⟨926289, by rfl⟩ : syracuseStep 2470105 = 1852579) (by norm_num)
theorem B3293473 : Blo 1951435 3293473 := bstep (se 2 (by rfl) ⟨1235052, by rfl⟩ : syracuseStep 3293473 = 2470105) B2470105
theorem B4391297 : Blo 1951435 4391297 := bstep (se 2 (by rfl) ⟨1646736, by rfl⟩ : syracuseStep 4391297 = 3293473) B3293473
theorem B2927531 : Blo 1951435 2927531 := bstep (se 1 (by rfl) ⟨2195648, by rfl⟩ : syracuseStep 2927531 = 4391297) B4391297
theorem B1951687 : Blo 1951435 1951687 := bstep (se 1 (by rfl) ⟨1463765, by rfl⟩ : syracuseStep 1951687 = 2927531) B2927531
theorem B2195653 : Blo 1951435 2195653 := bbase (se 4 (by rfl) ⟨205842, by rfl⟩ : syracuseStep 2195653 = 411685) (by norm_num)
theorem B2927537 : Blo 1951435 2927537 := bstep (se 2 (by rfl) ⟨1097826, by rfl⟩ : syracuseStep 2927537 = 2195653) B2195653
theorem B1951691 : Blo 1951435 1951691 := bstep (se 1 (by rfl) ⟨1463768, by rfl⟩ : syracuseStep 1951691 = 2927537) B2927537
theorem B3705173 : Blo 1951435 3705173 := bbase (se 10 (by rfl) ⟨5427, by rfl⟩ : syracuseStep 3705173 = 10855) (by norm_num)
theorem B2470115 : Blo 1951435 2470115 := bstep (se 1 (by rfl) ⟨1852586, by rfl⟩ : syracuseStep 2470115 = 3705173) B3705173
theorem B6586973 : Blo 1951435 6586973 := bstep (se 3 (by rfl) ⟨1235057, by rfl⟩ : syracuseStep 6586973 = 2470115) B2470115
theorem B4391315 : Blo 1951435 4391315 := bstep (se 1 (by rfl) ⟨3293486, by rfl⟩ : syracuseStep 4391315 = 6586973) B6586973
theorem B2927543 : Blo 1951435 2927543 := bstep (se 1 (by rfl) ⟨2195657, by rfl⟩ : syracuseStep 2927543 = 4391315) B4391315
theorem B1951695 : Blo 1951435 1951695 := bstep (se 1 (by rfl) ⟨1463771, by rfl⟩ : syracuseStep 1951695 = 2927543) B2927543
theorem B2927549 : Blo 1951435 2927549 := bbase (se 3 (by rfl) ⟨548915, by rfl⟩ : syracuseStep 2927549 = 1097831) (by norm_num)
theorem B1951699 : Blo 1951435 1951699 := bstep (se 1 (by rfl) ⟨1463774, by rfl⟩ : syracuseStep 1951699 = 2927549) B2927549
theorem B4391333 : Blo 1951435 4391333 := bbase (se 4 (by rfl) ⟨411687, by rfl⟩ : syracuseStep 4391333 = 823375) (by norm_num)
theorem B2927555 : Blo 1951435 2927555 := bstep (se 1 (by rfl) ⟨2195666, by rfl⟩ : syracuseStep 2927555 = 4391333) B4391333
theorem B1951703 : Blo 1951435 1951703 := bstep (se 1 (by rfl) ⟨1463777, by rfl⟩ : syracuseStep 1951703 = 2927555) B2927555
theorem B4940261 : Blo 1951435 4940261 := bbase (se 4 (by rfl) ⟨463149, by rfl⟩ : syracuseStep 4940261 = 926299) (by norm_num)
theorem B3293507 : Blo 1951435 3293507 := bstep (se 1 (by rfl) ⟨2470130, by rfl⟩ : syracuseStep 3293507 = 4940261) B4940261
theorem B2195671 : Blo 1951435 2195671 := bstep (se 1 (by rfl) ⟨1646753, by rfl⟩ : syracuseStep 2195671 = 3293507) B3293507
theorem B2927561 : Blo 1951435 2927561 := bstep (se 2 (by rfl) ⟨1097835, by rfl⟩ : syracuseStep 2927561 = 2195671) B2195671
theorem B1951707 : Blo 1951435 1951707 := bstep (se 1 (by rfl) ⟨1463780, by rfl⟩ : syracuseStep 1951707 = 2927561) B2927561
theorem B2084177 : Blo 1951435 2084177 := bbase (se 2 (by rfl) ⟨781566, by rfl⟩ : syracuseStep 2084177 = 1563133) (by norm_num)
theorem B5557805 : Blo 1951435 5557805 := bstep (se 3 (by rfl) ⟨1042088, by rfl⟩ : syracuseStep 5557805 = 2084177) B2084177
theorem B3705203 : Blo 1951435 3705203 := bstep (se 1 (by rfl) ⟨2778902, by rfl⟩ : syracuseStep 3705203 = 5557805) B5557805
theorem B9880541 : Blo 1951435 9880541 := bstep (se 3 (by rfl) ⟨1852601, by rfl⟩ : syracuseStep 9880541 = 3705203) B3705203
theorem B6587027 : Blo 1951435 6587027 := bstep (se 1 (by rfl) ⟨4940270, by rfl⟩ : syracuseStep 6587027 = 9880541) B9880541
theorem B4391351 : Blo 1951435 4391351 := bstep (se 1 (by rfl) ⟨3293513, by rfl⟩ : syracuseStep 4391351 = 6587027) B6587027
theorem B2927567 : Blo 1951435 2927567 := bstep (se 1 (by rfl) ⟨2195675, by rfl⟩ : syracuseStep 2927567 = 4391351) B4391351
theorem B1951711 : Blo 1951435 1951711 := bstep (se 1 (by rfl) ⟨1463783, by rfl⟩ : syracuseStep 1951711 = 2927567) B2927567
theorem B2927573 : Blo 1951435 2927573 := bbase (se 7 (by rfl) ⟨34307, by rfl⟩ : syracuseStep 2927573 = 68615) (by norm_num)
theorem B1951715 : Blo 1951435 1951715 := bstep (se 1 (by rfl) ⟨1463786, by rfl⟩ : syracuseStep 1951715 = 2927573) B2927573
theorem B7410437 : Blo 1951435 7410437 := bbase (se 4 (by rfl) ⟨694728, by rfl⟩ : syracuseStep 7410437 = 1389457) (by norm_num)
theorem B4940291 : Blo 1951435 4940291 := bstep (se 1 (by rfl) ⟨3705218, by rfl⟩ : syracuseStep 4940291 = 7410437) B7410437
theorem B3293527 : Blo 1951435 3293527 := bstep (se 1 (by rfl) ⟨2470145, by rfl⟩ : syracuseStep 3293527 = 4940291) B4940291
theorem B4391369 : Blo 1951435 4391369 := bstep (se 2 (by rfl) ⟨1646763, by rfl⟩ : syracuseStep 4391369 = 3293527) B3293527
theorem B2927579 : Blo 1951435 2927579 := bstep (se 1 (by rfl) ⟨2195684, by rfl⟩ : syracuseStep 2927579 = 4391369) B4391369
theorem B1951719 : Blo 1951435 1951719 := bstep (se 1 (by rfl) ⟨1463789, by rfl⟩ : syracuseStep 1951719 = 2927579) B2927579
theorem B2195689 : Blo 1951435 2195689 := bbase (se 2 (by rfl) ⟨823383, by rfl⟩ : syracuseStep 2195689 = 1646767) (by norm_num)
theorem B2927585 : Blo 1951435 2927585 := bstep (se 2 (by rfl) ⟨1097844, by rfl⟩ : syracuseStep 2927585 = 2195689) B2195689
theorem B1951723 : Blo 1951435 1951723 := bstep (se 1 (by rfl) ⟨1463792, by rfl⟩ : syracuseStep 1951723 = 2927585) B2927585
theorem B11115701 : Blo 1951435 11115701 := bbase (se 5 (by rfl) ⟨521048, by rfl⟩ : syracuseStep 11115701 = 1042097) (by norm_num)
theorem B7410467 : Blo 1951435 7410467 := bstep (se 1 (by rfl) ⟨5557850, by rfl⟩ : syracuseStep 7410467 = 11115701) B11115701
theorem B4940311 : Blo 1951435 4940311 := bstep (se 1 (by rfl) ⟨3705233, by rfl⟩ : syracuseStep 4940311 = 7410467) B7410467
theorem B6587081 : Blo 1951435 6587081 := bstep (se 2 (by rfl) ⟨2470155, by rfl⟩ : syracuseStep 6587081 = 4940311) B4940311
theorem B4391387 : Blo 1951435 4391387 := bstep (se 1 (by rfl) ⟨3293540, by rfl⟩ : syracuseStep 4391387 = 6587081) B6587081
theorem B2927591 : Blo 1951435 2927591 := bstep (se 1 (by rfl) ⟨2195693, by rfl⟩ : syracuseStep 2927591 = 4391387) B4391387
theorem B1951727 : Blo 1951435 1951727 := bstep (se 1 (by rfl) ⟨1463795, by rfl⟩ : syracuseStep 1951727 = 2927591) B2927591
theorem B2927597 : Blo 1951435 2927597 := bbase (se 3 (by rfl) ⟨548924, by rfl⟩ : syracuseStep 2927597 = 1097849) (by norm_num)
theorem B1951731 : Blo 1951435 1951731 := bstep (se 1 (by rfl) ⟨1463798, by rfl⟩ : syracuseStep 1951731 = 2927597) B2927597
theorem B4391405 : Blo 1951435 4391405 := bbase (se 3 (by rfl) ⟨823388, by rfl⟩ : syracuseStep 4391405 = 1646777) (by norm_num)
theorem B2927603 : Blo 1951435 2927603 := bstep (se 1 (by rfl) ⟨2195702, by rfl⟩ : syracuseStep 2927603 = 4391405) B4391405
theorem B1951735 : Blo 1951435 1951735 := bstep (se 1 (by rfl) ⟨1463801, by rfl⟩ : syracuseStep 1951735 = 2927603) B2927603
theorem B7913477 : Blo 1951435 7913477 := bbase (se 4 (by rfl) ⟨741888, by rfl⟩ : syracuseStep 7913477 = 1483777) (by norm_num)
theorem B21102605 : Blo 1951435 21102605 := bstep (se 3 (by rfl) ⟨3956738, by rfl⟩ : syracuseStep 21102605 = 7913477) B7913477
theorem B14068403 : Blo 1951435 14068403 := bstep (se 1 (by rfl) ⟨10551302, by rfl⟩ : syracuseStep 14068403 = 21102605) B21102605
theorem B9378935 : Blo 1951435 9378935 := bstep (se 1 (by rfl) ⟨7034201, by rfl⟩ : syracuseStep 9378935 = 14068403) B14068403
theorem B6252623 : Blo 1951435 6252623 := bstep (se 1 (by rfl) ⟨4689467, by rfl⟩ : syracuseStep 6252623 = 9378935) B9378935
theorem B4168415 : Blo 1951435 4168415 := bstep (se 1 (by rfl) ⟨3126311, by rfl⟩ : syracuseStep 4168415 = 6252623) B6252623
theorem B2778943 : Blo 1951435 2778943 := bstep (se 1 (by rfl) ⟨2084207, by rfl⟩ : syracuseStep 2778943 = 4168415) B4168415
theorem B3705257 : Blo 1951435 3705257 := bstep (se 2 (by rfl) ⟨1389471, by rfl⟩ : syracuseStep 3705257 = 2778943) B2778943
theorem B2470171 : Blo 1951435 2470171 := bstep (se 1 (by rfl) ⟨1852628, by rfl⟩ : syracuseStep 2470171 = 3705257) B3705257
theorem B3293561 : Blo 1951435 3293561 := bstep (se 2 (by rfl) ⟨1235085, by rfl⟩ : syracuseStep 3293561 = 2470171) B2470171
theorem B2195707 : Blo 1951435 2195707 := bstep (se 1 (by rfl) ⟨1646780, by rfl⟩ : syracuseStep 2195707 = 3293561) B3293561
theorem B2927609 : Blo 1951435 2927609 := bstep (se 2 (by rfl) ⟨1097853, by rfl⟩ : syracuseStep 2927609 = 2195707) B2195707
theorem B1951739 : Blo 1951435 1951739 := bstep (se 1 (by rfl) ⟨1463804, by rfl⟩ : syracuseStep 1951739 = 2927609) B2927609
theorem B3565093 : Blo 1951435 3565093 := bbase (se 4 (by rfl) ⟨334227, by rfl⟩ : syracuseStep 3565093 = 668455) (by norm_num)
theorem B4753457 : Blo 1951435 4753457 := bstep (se 2 (by rfl) ⟨1782546, by rfl⟩ : syracuseStep 4753457 = 3565093) B3565093
theorem B3168971 : Blo 1951435 3168971 := bstep (se 1 (by rfl) ⟨2376728, by rfl⟩ : syracuseStep 3168971 = 4753457) B4753457
theorem B2112647 : Blo 1951435 2112647 := bstep (se 1 (by rfl) ⟨1584485, by rfl⟩ : syracuseStep 2112647 = 3168971) B3168971
theorem B5633725 : Blo 1951435 5633725 := bstep (se 3 (by rfl) ⟨1056323, by rfl⟩ : syracuseStep 5633725 = 2112647) B2112647
theorem B7511633 : Blo 1951435 7511633 := bstep (se 2 (by rfl) ⟨2816862, by rfl⟩ : syracuseStep 7511633 = 5633725) B5633725
theorem B5007755 : Blo 1951435 5007755 := bstep (se 1 (by rfl) ⟨3755816, by rfl⟩ : syracuseStep 5007755 = 7511633) B7511633
theorem B13354013 : Blo 1951435 13354013 := bstep (se 3 (by rfl) ⟨2503877, by rfl⟩ : syracuseStep 13354013 = 5007755) B5007755
theorem B8902675 : Blo 1951435 8902675 := bstep (se 1 (by rfl) ⟨6677006, by rfl⟩ : syracuseStep 8902675 = 13354013) B13354013
theorem B11870233 : Blo 1951435 11870233 := bstep (se 2 (by rfl) ⟨4451337, by rfl⟩ : syracuseStep 11870233 = 8902675) B8902675
theorem B63307909 : Blo 1951435 63307909 := bstep (se 4 (by rfl) ⟨5935116, by rfl⟩ : syracuseStep 63307909 = 11870233) B11870233
theorem B84410545 : Blo 1951435 84410545 := bstep (se 2 (by rfl) ⟨31653954, by rfl⟩ : syracuseStep 84410545 = 63307909) B63307909
theorem B112547393 : Blo 1951435 112547393 := bstep (se 2 (by rfl) ⟨42205272, by rfl⟩ : syracuseStep 112547393 = 84410545) B84410545
theorem B75031595 : Blo 1951435 75031595 := bstep (se 1 (by rfl) ⟨56273696, by rfl⟩ : syracuseStep 75031595 = 112547393) B112547393
theorem B50021063 : Blo 1951435 50021063 := bstep (se 1 (by rfl) ⟨37515797, by rfl⟩ : syracuseStep 50021063 = 75031595) B75031595
theorem B33347375 : Blo 1951435 33347375 := bstep (se 1 (by rfl) ⟨25010531, by rfl⟩ : syracuseStep 33347375 = 50021063) B50021063
theorem B22231583 : Blo 1951435 22231583 := bstep (se 1 (by rfl) ⟨16673687, by rfl⟩ : syracuseStep 22231583 = 33347375) B33347375
theorem B14821055 : Blo 1951435 14821055 := bstep (se 1 (by rfl) ⟨11115791, by rfl⟩ : syracuseStep 14821055 = 22231583) B22231583
theorem B9880703 : Blo 1951435 9880703 := bstep (se 1 (by rfl) ⟨7410527, by rfl⟩ : syracuseStep 9880703 = 14821055) B14821055
theorem B6587135 : Blo 1951435 6587135 := bstep (se 1 (by rfl) ⟨4940351, by rfl⟩ : syracuseStep 6587135 = 9880703) B9880703
theorem B4391423 : Blo 1951435 4391423 := bstep (se 1 (by rfl) ⟨3293567, by rfl⟩ : syracuseStep 4391423 = 6587135) B6587135
theorem B2927615 : Blo 1951435 2927615 := bstep (se 1 (by rfl) ⟨2195711, by rfl⟩ : syracuseStep 2927615 = 4391423) B4391423
theorem B1951743 : Blo 1951435 1951743 := bstep (se 1 (by rfl) ⟨1463807, by rfl⟩ : syracuseStep 1951743 = 2927615) B2927615
theorem B2927621 : Blo 1951435 2927621 := bbase (se 4 (by rfl) ⟨274464, by rfl⟩ : syracuseStep 2927621 = 548929) (by norm_num)
theorem B1951747 : Blo 1951435 1951747 := bstep (se 1 (by rfl) ⟨1463810, by rfl⟩ : syracuseStep 1951747 = 2927621) B2927621
theorem B3293581 : Blo 1951435 3293581 := bbase (se 3 (by rfl) ⟨617546, by rfl⟩ : syracuseStep 3293581 = 1235093) (by norm_num)
theorem B4391441 : Blo 1951435 4391441 := bstep (se 2 (by rfl) ⟨1646790, by rfl⟩ : syracuseStep 4391441 = 3293581) B3293581
theorem B2927627 : Blo 1951435 2927627 := bstep (se 1 (by rfl) ⟨2195720, by rfl⟩ : syracuseStep 2927627 = 4391441) B4391441
theorem B1951751 : Blo 1951435 1951751 := bstep (se 1 (by rfl) ⟨1463813, by rfl⟩ : syracuseStep 1951751 = 2927627) B2927627
theorem B2195725 : Blo 1951435 2195725 := bbase (se 3 (by rfl) ⟨411698, by rfl⟩ : syracuseStep 2195725 = 823397) (by norm_num)
theorem B2927633 : Blo 1951435 2927633 := bstep (se 2 (by rfl) ⟨1097862, by rfl⟩ : syracuseStep 2927633 = 2195725) B2195725
theorem B1951755 : Blo 1951435 1951755 := bstep (se 1 (by rfl) ⟨1463816, by rfl⟩ : syracuseStep 1951755 = 2927633) B2927633
theorem B6587189 : Blo 1951435 6587189 := bbase (se 5 (by rfl) ⟨308774, by rfl⟩ : syracuseStep 6587189 = 617549) (by norm_num)
theorem B4391459 : Blo 1951435 4391459 := bstep (se 1 (by rfl) ⟨3293594, by rfl⟩ : syracuseStep 4391459 = 6587189) B6587189
theorem B2927639 : Blo 1951435 2927639 := bstep (se 1 (by rfl) ⟨2195729, by rfl⟩ : syracuseStep 2927639 = 4391459) B4391459
theorem B1951759 : Blo 1951435 1951759 := bstep (se 1 (by rfl) ⟨1463819, by rfl⟩ : syracuseStep 1951759 = 2927639) B2927639
theorem B2927645 : Blo 1951435 2927645 := bbase (se 3 (by rfl) ⟨548933, by rfl⟩ : syracuseStep 2927645 = 1097867) (by norm_num)
theorem B1951763 : Blo 1951435 1951763 := bstep (se 1 (by rfl) ⟨1463822, by rfl⟩ : syracuseStep 1951763 = 2927645) B2927645
theorem B4391477 : Blo 1951435 4391477 := bbase (se 5 (by rfl) ⟨205850, by rfl⟩ : syracuseStep 4391477 = 411701) (by norm_num)
theorem B2927651 : Blo 1951435 2927651 := bstep (se 1 (by rfl) ⟨2195738, by rfl⟩ : syracuseStep 2927651 = 4391477) B4391477
theorem B1951767 : Blo 1951435 1951767 := bstep (se 1 (by rfl) ⟨1463825, by rfl⟩ : syracuseStep 1951767 = 2927651) B2927651
theorem B8336965 : Blo 1951435 8336965 := bbase (se 4 (by rfl) ⟨781590, by rfl⟩ : syracuseStep 8336965 = 1563181) (by norm_num)
theorem B11115953 : Blo 1951435 11115953 := bstep (se 2 (by rfl) ⟨4168482, by rfl⟩ : syracuseStep 11115953 = 8336965) B8336965
theorem B7410635 : Blo 1951435 7410635 := bstep (se 1 (by rfl) ⟨5557976, by rfl⟩ : syracuseStep 7410635 = 11115953) B11115953
theorem B4940423 : Blo 1951435 4940423 := bstep (se 1 (by rfl) ⟨3705317, by rfl⟩ : syracuseStep 4940423 = 7410635) B7410635
theorem B3293615 : Blo 1951435 3293615 := bstep (se 1 (by rfl) ⟨2470211, by rfl⟩ : syracuseStep 3293615 = 4940423) B4940423
theorem B2195743 : Blo 1951435 2195743 := bstep (se 1 (by rfl) ⟨1646807, by rfl⟩ : syracuseStep 2195743 = 3293615) B3293615
theorem B2927657 : Blo 1951435 2927657 := bstep (se 2 (by rfl) ⟨1097871, by rfl⟩ : syracuseStep 2927657 = 2195743) B2195743
theorem B1951771 : Blo 1951435 1951771 := bstep (se 1 (by rfl) ⟨1463828, by rfl⟩ : syracuseStep 1951771 = 2927657) B2927657
theorem B8336981 : Blo 1951435 8336981 := bbase (se 8 (by rfl) ⟨48849, by rfl⟩ : syracuseStep 8336981 = 97699) (by norm_num)
theorem B5557987 : Blo 1951435 5557987 := bstep (se 1 (by rfl) ⟨4168490, by rfl⟩ : syracuseStep 5557987 = 8336981) B8336981
theorem B7410649 : Blo 1951435 7410649 := bstep (se 2 (by rfl) ⟨2778993, by rfl⟩ : syracuseStep 7410649 = 5557987) B5557987
theorem B9880865 : Blo 1951435 9880865 := bstep (se 2 (by rfl) ⟨3705324, by rfl⟩ : syracuseStep 9880865 = 7410649) B7410649
theorem B6587243 : Blo 1951435 6587243 := bstep (se 1 (by rfl) ⟨4940432, by rfl⟩ : syracuseStep 6587243 = 9880865) B9880865
theorem B4391495 : Blo 1951435 4391495 := bstep (se 1 (by rfl) ⟨3293621, by rfl⟩ : syracuseStep 4391495 = 6587243) B6587243
theorem B2927663 : Blo 1951435 2927663 := bstep (se 1 (by rfl) ⟨2195747, by rfl⟩ : syracuseStep 2927663 = 4391495) B4391495
theorem B1951775 : Blo 1951435 1951775 := bstep (se 1 (by rfl) ⟨1463831, by rfl⟩ : syracuseStep 1951775 = 2927663) B2927663
theorem B2927669 : Blo 1951435 2927669 := bbase (se 5 (by rfl) ⟨137234, by rfl⟩ : syracuseStep 2927669 = 274469) (by norm_num)
theorem B1951779 : Blo 1951435 1951779 := bstep (se 1 (by rfl) ⟨1463834, by rfl⟩ : syracuseStep 1951779 = 2927669) B2927669
theorem B4940453 : Blo 1951435 4940453 := bbase (se 4 (by rfl) ⟨463167, by rfl⟩ : syracuseStep 4940453 = 926335) (by norm_num)
theorem B3293635 : Blo 1951435 3293635 := bstep (se 1 (by rfl) ⟨2470226, by rfl⟩ : syracuseStep 3293635 = 4940453) B4940453
theorem B4391513 : Blo 1951435 4391513 := bstep (se 2 (by rfl) ⟨1646817, by rfl⟩ : syracuseStep 4391513 = 3293635) B3293635
theorem B2927675 : Blo 1951435 2927675 := bstep (se 1 (by rfl) ⟨2195756, by rfl⟩ : syracuseStep 2927675 = 4391513) B4391513
theorem B1951783 : Blo 1951435 1951783 := bstep (se 1 (by rfl) ⟨1463837, by rfl⟩ : syracuseStep 1951783 = 2927675) B2927675
theorem B2195761 : Blo 1951435 2195761 := bbase (se 2 (by rfl) ⟨823410, by rfl⟩ : syracuseStep 2195761 = 1646821) (by norm_num)
theorem B2927681 : Blo 1951435 2927681 := bstep (se 2 (by rfl) ⟨1097880, by rfl⟩ : syracuseStep 2927681 = 2195761) B2195761
theorem B1951787 : Blo 1951435 1951787 := bstep (se 1 (by rfl) ⟨1463840, by rfl⟩ : syracuseStep 1951787 = 2927681) B2927681
theorem B4168525 : Blo 1951435 4168525 := bbase (se 3 (by rfl) ⟨781598, by rfl⟩ : syracuseStep 4168525 = 1563197) (by norm_num)
theorem B5558033 : Blo 1951435 5558033 := bstep (se 2 (by rfl) ⟨2084262, by rfl⟩ : syracuseStep 5558033 = 4168525) B4168525
theorem B3705355 : Blo 1951435 3705355 := bstep (se 1 (by rfl) ⟨2779016, by rfl⟩ : syracuseStep 3705355 = 5558033) B5558033
theorem B4940473 : Blo 1951435 4940473 := bstep (se 2 (by rfl) ⟨1852677, by rfl⟩ : syracuseStep 4940473 = 3705355) B3705355
theorem B6587297 : Blo 1951435 6587297 := bstep (se 2 (by rfl) ⟨2470236, by rfl⟩ : syracuseStep 6587297 = 4940473) B4940473
theorem B4391531 : Blo 1951435 4391531 := bstep (se 1 (by rfl) ⟨3293648, by rfl⟩ : syracuseStep 4391531 = 6587297) B6587297
theorem B2927687 : Blo 1951435 2927687 := bstep (se 1 (by rfl) ⟨2195765, by rfl⟩ : syracuseStep 2927687 = 4391531) B4391531
theorem B1951791 : Blo 1951435 1951791 := bstep (se 1 (by rfl) ⟨1463843, by rfl⟩ : syracuseStep 1951791 = 2927687) B2927687
theorem B2927693 : Blo 1951435 2927693 := bbase (se 3 (by rfl) ⟨548942, by rfl⟩ : syracuseStep 2927693 = 1097885) (by norm_num)
theorem B1951795 : Blo 1951435 1951795 := bstep (se 1 (by rfl) ⟨1463846, by rfl⟩ : syracuseStep 1951795 = 2927693) B2927693
theorem B4391549 : Blo 1951435 4391549 := bbase (se 3 (by rfl) ⟨823415, by rfl⟩ : syracuseStep 4391549 = 1646831) (by norm_num)
theorem B2927699 : Blo 1951435 2927699 := bstep (se 1 (by rfl) ⟨2195774, by rfl⟩ : syracuseStep 2927699 = 4391549) B4391549
theorem B1951799 : Blo 1951435 1951799 := bstep (se 1 (by rfl) ⟨1463849, by rfl⟩ : syracuseStep 1951799 = 2927699) B2927699
theorem B3293669 : Blo 1951435 3293669 := bbase (se 4 (by rfl) ⟨308781, by rfl⟩ : syracuseStep 3293669 = 617563) (by norm_num)
theorem B2195779 : Blo 1951435 2195779 := bstep (se 1 (by rfl) ⟨1646834, by rfl⟩ : syracuseStep 2195779 = 3293669) B3293669
theorem B2927705 : Blo 1951435 2927705 := bstep (se 2 (by rfl) ⟨1097889, by rfl⟩ : syracuseStep 2927705 = 2195779) B2195779
theorem B1951803 : Blo 1951435 1951803 := bstep (se 1 (by rfl) ⟨1463852, by rfl⟩ : syracuseStep 1951803 = 2927705) B2927705
theorem B4451485 : Blo 1951435 4451485 := bbase (se 3 (by rfl) ⟨834653, by rfl⟩ : syracuseStep 4451485 = 1669307) (by norm_num)
theorem B5935313 : Blo 1951435 5935313 := bstep (se 2 (by rfl) ⟨2225742, by rfl⟩ : syracuseStep 5935313 = 4451485) B4451485
theorem B15827501 : Blo 1951435 15827501 := bstep (se 3 (by rfl) ⟨2967656, by rfl⟩ : syracuseStep 15827501 = 5935313) B5935313
theorem B10551667 : Blo 1951435 10551667 := bstep (se 1 (by rfl) ⟨7913750, by rfl⟩ : syracuseStep 10551667 = 15827501) B15827501
theorem B14068889 : Blo 1951435 14068889 := bstep (se 2 (by rfl) ⟨5275833, by rfl⟩ : syracuseStep 14068889 = 10551667) B10551667
theorem B9379259 : Blo 1951435 9379259 := bstep (se 1 (by rfl) ⟨7034444, by rfl⟩ : syracuseStep 9379259 = 14068889) B14068889
theorem B6252839 : Blo 1951435 6252839 := bstep (se 1 (by rfl) ⟨4689629, by rfl⟩ : syracuseStep 6252839 = 9379259) B9379259
theorem B4168559 : Blo 1951435 4168559 := bstep (se 1 (by rfl) ⟨3126419, by rfl⟩ : syracuseStep 4168559 = 6252839) B6252839
theorem B2779039 : Blo 1951435 2779039 := bstep (se 1 (by rfl) ⟨2084279, by rfl⟩ : syracuseStep 2779039 = 4168559) B4168559
theorem B14821541 : Blo 1951435 14821541 := bstep (se 4 (by rfl) ⟨1389519, by rfl⟩ : syracuseStep 14821541 = 2779039) B2779039
theorem B9881027 : Blo 1951435 9881027 := bstep (se 1 (by rfl) ⟨7410770, by rfl⟩ : syracuseStep 9881027 = 14821541) B14821541
theorem B6587351 : Blo 1951435 6587351 := bstep (se 1 (by rfl) ⟨4940513, by rfl⟩ : syracuseStep 6587351 = 9881027) B9881027
theorem B4391567 : Blo 1951435 4391567 := bstep (se 1 (by rfl) ⟨3293675, by rfl⟩ : syracuseStep 4391567 = 6587351) B6587351
theorem B2927711 : Blo 1951435 2927711 := bstep (se 1 (by rfl) ⟨2195783, by rfl⟩ : syracuseStep 2927711 = 4391567) B4391567
theorem B1951807 : Blo 1951435 1951807 := bstep (se 1 (by rfl) ⟨1463855, by rfl⟩ : syracuseStep 1951807 = 2927711) B2927711
theorem B2927717 : Blo 1951435 2927717 := bbase (se 4 (by rfl) ⟨274473, by rfl⟩ : syracuseStep 2927717 = 548947) (by norm_num)
theorem B1951811 : Blo 1951435 1951811 := bstep (se 1 (by rfl) ⟨1463858, by rfl⟩ : syracuseStep 1951811 = 2927717) B2927717
theorem B2344825 : Blo 1951435 2344825 := bbase (se 2 (by rfl) ⟨879309, by rfl⟩ : syracuseStep 2344825 = 1758619) (by norm_num)
theorem B3126433 : Blo 1951435 3126433 := bstep (se 2 (by rfl) ⟨1172412, by rfl⟩ : syracuseStep 3126433 = 2344825) B2344825
theorem B4168577 : Blo 1951435 4168577 := bstep (se 2 (by rfl) ⟨1563216, by rfl⟩ : syracuseStep 4168577 = 3126433) B3126433
theorem B2779051 : Blo 1951435 2779051 := bstep (se 1 (by rfl) ⟨2084288, by rfl⟩ : syracuseStep 2779051 = 4168577) B4168577
theorem B3705401 : Blo 1951435 3705401 := bstep (se 2 (by rfl) ⟨1389525, by rfl⟩ : syracuseStep 3705401 = 2779051) B2779051
theorem B2470267 : Blo 1951435 2470267 := bstep (se 1 (by rfl) ⟨1852700, by rfl⟩ : syracuseStep 2470267 = 3705401) B3705401
theorem B3293689 : Blo 1951435 3293689 := bstep (se 2 (by rfl) ⟨1235133, by rfl⟩ : syracuseStep 3293689 = 2470267) B2470267
theorem B4391585 : Blo 1951435 4391585 := bstep (se 2 (by rfl) ⟨1646844, by rfl⟩ : syracuseStep 4391585 = 3293689) B3293689
theorem B2927723 : Blo 1951435 2927723 := bstep (se 1 (by rfl) ⟨2195792, by rfl⟩ : syracuseStep 2927723 = 4391585) B4391585
theorem B1951815 : Blo 1951435 1951815 := bstep (se 1 (by rfl) ⟨1463861, by rfl⟩ : syracuseStep 1951815 = 2927723) B2927723
theorem B2195797 : Blo 1951435 2195797 := bbase (se 10 (by rfl) ⟨3216, by rfl⟩ : syracuseStep 2195797 = 6433) (by norm_num)
theorem B2927729 : Blo 1951435 2927729 := bstep (se 2 (by rfl) ⟨1097898, by rfl⟩ : syracuseStep 2927729 = 2195797) B2195797
theorem B1951819 : Blo 1951435 1951819 := bstep (se 1 (by rfl) ⟨1463864, by rfl⟩ : syracuseStep 1951819 = 2927729) B2927729
theorem B2470277 : Blo 1951435 2470277 := bbase (se 4 (by rfl) ⟨231588, by rfl⟩ : syracuseStep 2470277 = 463177) (by norm_num)
theorem B6587405 : Blo 1951435 6587405 := bstep (se 3 (by rfl) ⟨1235138, by rfl⟩ : syracuseStep 6587405 = 2470277) B2470277
theorem B4391603 : Blo 1951435 4391603 := bstep (se 1 (by rfl) ⟨3293702, by rfl⟩ : syracuseStep 4391603 = 6587405) B6587405
theorem B2927735 : Blo 1951435 2927735 := bstep (se 1 (by rfl) ⟨2195801, by rfl⟩ : syracuseStep 2927735 = 4391603) B4391603
theorem B1951823 : Blo 1951435 1951823 := bstep (se 1 (by rfl) ⟨1463867, by rfl⟩ : syracuseStep 1951823 = 2927735) B2927735
theorem B2927741 : Blo 1951435 2927741 := bbase (se 3 (by rfl) ⟨548951, by rfl⟩ : syracuseStep 2927741 = 1097903) (by norm_num)
theorem B1951827 : Blo 1951435 1951827 := bstep (se 1 (by rfl) ⟨1463870, by rfl⟩ : syracuseStep 1951827 = 2927741) B2927741
theorem B4391621 : Blo 1951435 4391621 := bbase (se 4 (by rfl) ⟨411714, by rfl⟩ : syracuseStep 4391621 = 823429) (by norm_num)
theorem B2927747 : Blo 1951435 2927747 := bstep (se 1 (by rfl) ⟨2195810, by rfl⟩ : syracuseStep 2927747 = 4391621) B4391621
theorem B1951831 : Blo 1951435 1951831 := bstep (se 1 (by rfl) ⟨1463873, by rfl⟩ : syracuseStep 1951831 = 2927747) B2927747
theorem B3956933 : Blo 1951435 3956933 := bbase (se 4 (by rfl) ⟨370962, by rfl⟩ : syracuseStep 3956933 = 741925) (by norm_num)
theorem B2637955 : Blo 1951435 2637955 := bstep (se 1 (by rfl) ⟨1978466, by rfl⟩ : syracuseStep 2637955 = 3956933) B3956933
theorem B3517273 : Blo 1951435 3517273 := bstep (se 2 (by rfl) ⟨1318977, by rfl⟩ : syracuseStep 3517273 = 2637955) B2637955
theorem B18758789 : Blo 1951435 18758789 := bstep (se 4 (by rfl) ⟨1758636, by rfl⟩ : syracuseStep 18758789 = 3517273) B3517273
theorem B12505859 : Blo 1951435 12505859 := bstep (se 1 (by rfl) ⟨9379394, by rfl⟩ : syracuseStep 12505859 = 18758789) B18758789
theorem B8337239 : Blo 1951435 8337239 := bstep (se 1 (by rfl) ⟨6252929, by rfl⟩ : syracuseStep 8337239 = 12505859) B12505859
theorem B5558159 : Blo 1951435 5558159 := bstep (se 1 (by rfl) ⟨4168619, by rfl⟩ : syracuseStep 5558159 = 8337239) B8337239
theorem B3705439 : Blo 1951435 3705439 := bstep (se 1 (by rfl) ⟨2779079, by rfl⟩ : syracuseStep 3705439 = 5558159) B5558159
theorem B4940585 : Blo 1951435 4940585 := bstep (se 2 (by rfl) ⟨1852719, by rfl⟩ : syracuseStep 4940585 = 3705439) B3705439
theorem B3293723 : Blo 1951435 3293723 := bstep (se 1 (by rfl) ⟨2470292, by rfl⟩ : syracuseStep 3293723 = 4940585) B4940585
theorem B2195815 : Blo 1951435 2195815 := bstep (se 1 (by rfl) ⟨1646861, by rfl⟩ : syracuseStep 2195815 = 3293723) B3293723
theorem B2927753 : Blo 1951435 2927753 := bstep (se 2 (by rfl) ⟨1097907, by rfl⟩ : syracuseStep 2927753 = 2195815) B2195815
theorem B1951835 : Blo 1951435 1951835 := bstep (se 1 (by rfl) ⟨1463876, by rfl⟩ : syracuseStep 1951835 = 2927753) B2927753
theorem B9881189 : Blo 1951435 9881189 := bbase (se 4 (by rfl) ⟨926361, by rfl⟩ : syracuseStep 9881189 = 1852723) (by norm_num)
theorem B6587459 : Blo 1951435 6587459 := bstep (se 1 (by rfl) ⟨4940594, by rfl⟩ : syracuseStep 6587459 = 9881189) B9881189
theorem B4391639 : Blo 1951435 4391639 := bstep (se 1 (by rfl) ⟨3293729, by rfl⟩ : syracuseStep 4391639 = 6587459) B6587459
theorem B2927759 : Blo 1951435 2927759 := bstep (se 1 (by rfl) ⟨2195819, by rfl⟩ : syracuseStep 2927759 = 4391639) B4391639
theorem B1951839 : Blo 1951435 1951839 := bstep (se 1 (by rfl) ⟨1463879, by rfl⟩ : syracuseStep 1951839 = 2927759) B2927759
theorem B2927765 : Blo 1951435 2927765 := bbase (se 6 (by rfl) ⟨68619, by rfl⟩ : syracuseStep 2927765 = 137239) (by norm_num)
theorem B1951843 : Blo 1951435 1951843 := bstep (se 1 (by rfl) ⟨1463882, by rfl⟩ : syracuseStep 1951843 = 2927765) B2927765
theorem B11870869 : Blo 1951435 11870869 := bbase (se 6 (by rfl) ⟨278223, by rfl⟩ : syracuseStep 11870869 = 556447) (by norm_num)
theorem B15827825 : Blo 1951435 15827825 := bstep (se 2 (by rfl) ⟨5935434, by rfl⟩ : syracuseStep 15827825 = 11870869) B11870869
theorem B10551883 : Blo 1951435 10551883 := bstep (se 1 (by rfl) ⟨7913912, by rfl⟩ : syracuseStep 10551883 = 15827825) B15827825
theorem B14069177 : Blo 1951435 14069177 := bstep (se 2 (by rfl) ⟨5275941, by rfl⟩ : syracuseStep 14069177 = 10551883) B10551883
theorem B9379451 : Blo 1951435 9379451 := bstep (se 1 (by rfl) ⟨7034588, by rfl⟩ : syracuseStep 9379451 = 14069177) B14069177
theorem B6252967 : Blo 1951435 6252967 := bstep (se 1 (by rfl) ⟨4689725, by rfl⟩ : syracuseStep 6252967 = 9379451) B9379451
theorem B8337289 : Blo 1951435 8337289 := bstep (se 2 (by rfl) ⟨3126483, by rfl⟩ : syracuseStep 8337289 = 6252967) B6252967
theorem B11116385 : Blo 1951435 11116385 := bstep (se 2 (by rfl) ⟨4168644, by rfl⟩ : syracuseStep 11116385 = 8337289) B8337289
theorem B7410923 : Blo 1951435 7410923 := bstep (se 1 (by rfl) ⟨5558192, by rfl⟩ : syracuseStep 7410923 = 11116385) B11116385
theorem B4940615 : Blo 1951435 4940615 := bstep (se 1 (by rfl) ⟨3705461, by rfl⟩ : syracuseStep 4940615 = 7410923) B7410923
theorem B3293743 : Blo 1951435 3293743 := bstep (se 1 (by rfl) ⟨2470307, by rfl⟩ : syracuseStep 3293743 = 4940615) B4940615
theorem B4391657 : Blo 1951435 4391657 := bstep (se 2 (by rfl) ⟨1646871, by rfl⟩ : syracuseStep 4391657 = 3293743) B3293743
theorem B2927771 : Blo 1951435 2927771 := bstep (se 1 (by rfl) ⟨2195828, by rfl⟩ : syracuseStep 2927771 = 4391657) B4391657
theorem B1951847 : Blo 1951435 1951847 := bstep (se 1 (by rfl) ⟨1463885, by rfl⟩ : syracuseStep 1951847 = 2927771) B2927771
theorem B2195833 : Blo 1951435 2195833 := bbase (se 2 (by rfl) ⟨823437, by rfl⟩ : syracuseStep 2195833 = 1646875) (by norm_num)
theorem B2927777 : Blo 1951435 2927777 := bstep (se 2 (by rfl) ⟨1097916, by rfl⟩ : syracuseStep 2927777 = 2195833) B2195833
theorem B1951851 : Blo 1951435 1951851 := bstep (se 1 (by rfl) ⟨1463888, by rfl⟩ : syracuseStep 1951851 = 2927777) B2927777
theorem B8903189 : Blo 1951435 8903189 := bbase (se 6 (by rfl) ⟨208668, by rfl⟩ : syracuseStep 8903189 = 417337) (by norm_num)
theorem B5935459 : Blo 1951435 5935459 := bstep (se 1 (by rfl) ⟨4451594, by rfl⟩ : syracuseStep 5935459 = 8903189) B8903189
theorem B7913945 : Blo 1951435 7913945 := bstep (se 2 (by rfl) ⟨2967729, by rfl⟩ : syracuseStep 7913945 = 5935459) B5935459
theorem B5275963 : Blo 1951435 5275963 := bstep (se 1 (by rfl) ⟨3956972, by rfl⟩ : syracuseStep 5275963 = 7913945) B7913945
theorem B7034617 : Blo 1951435 7034617 := bstep (se 2 (by rfl) ⟨2637981, by rfl⟩ : syracuseStep 7034617 = 5275963) B5275963
theorem B9379489 : Blo 1951435 9379489 := bstep (se 2 (by rfl) ⟨3517308, by rfl⟩ : syracuseStep 9379489 = 7034617) B7034617
theorem B12505985 : Blo 1951435 12505985 := bstep (se 2 (by rfl) ⟨4689744, by rfl⟩ : syracuseStep 12505985 = 9379489) B9379489
theorem B8337323 : Blo 1951435 8337323 := bstep (se 1 (by rfl) ⟨6252992, by rfl⟩ : syracuseStep 8337323 = 12505985) B12505985
theorem B5558215 : Blo 1951435 5558215 := bstep (se 1 (by rfl) ⟨4168661, by rfl⟩ : syracuseStep 5558215 = 8337323) B8337323
theorem B7410953 : Blo 1951435 7410953 := bstep (se 2 (by rfl) ⟨2779107, by rfl⟩ : syracuseStep 7410953 = 5558215) B5558215
theorem B4940635 : Blo 1951435 4940635 := bstep (se 1 (by rfl) ⟨3705476, by rfl⟩ : syracuseStep 4940635 = 7410953) B7410953
theorem B6587513 : Blo 1951435 6587513 := bstep (se 2 (by rfl) ⟨2470317, by rfl⟩ : syracuseStep 6587513 = 4940635) B4940635
theorem B4391675 : Blo 1951435 4391675 := bstep (se 1 (by rfl) ⟨3293756, by rfl⟩ : syracuseStep 4391675 = 6587513) B6587513
theorem B2927783 : Blo 1951435 2927783 := bstep (se 1 (by rfl) ⟨2195837, by rfl⟩ : syracuseStep 2927783 = 4391675) B4391675
theorem B1951855 : Blo 1951435 1951855 := bstep (se 1 (by rfl) ⟨1463891, by rfl⟩ : syracuseStep 1951855 = 2927783) B2927783
theorem B2927789 : Blo 1951435 2927789 := bbase (se 3 (by rfl) ⟨548960, by rfl⟩ : syracuseStep 2927789 = 1097921) (by norm_num)
theorem B1951859 : Blo 1951435 1951859 := bstep (se 1 (by rfl) ⟨1463894, by rfl⟩ : syracuseStep 1951859 = 2927789) B2927789
theorem B4391693 : Blo 1951435 4391693 := bbase (se 3 (by rfl) ⟨823442, by rfl⟩ : syracuseStep 4391693 = 1646885) (by norm_num)
theorem B2927795 : Blo 1951435 2927795 := bstep (se 1 (by rfl) ⟨2195846, by rfl⟩ : syracuseStep 2927795 = 4391693) B4391693
theorem B1951863 : Blo 1951435 1951863 := bstep (se 1 (by rfl) ⟨1463897, by rfl⟩ : syracuseStep 1951863 = 2927795) B2927795
theorem B2470333 : Blo 1951435 2470333 := bbase (se 3 (by rfl) ⟨463187, by rfl⟩ : syracuseStep 2470333 = 926375) (by norm_num)
theorem B3293777 : Blo 1951435 3293777 := bstep (se 2 (by rfl) ⟨1235166, by rfl⟩ : syracuseStep 3293777 = 2470333) B2470333
theorem B2195851 : Blo 1951435 2195851 := bstep (se 1 (by rfl) ⟨1646888, by rfl⟩ : syracuseStep 2195851 = 3293777) B3293777
theorem B2927801 : Blo 1951435 2927801 := bstep (se 2 (by rfl) ⟨1097925, by rfl⟩ : syracuseStep 2927801 = 2195851) B2195851
theorem B1951867 : Blo 1951435 1951867 := bstep (se 1 (by rfl) ⟨1463900, by rfl⟩ : syracuseStep 1951867 = 2927801) B2927801
theorem B3957005 : Blo 1951435 3957005 := bbase (se 3 (by rfl) ⟨741938, by rfl⟩ : syracuseStep 3957005 = 1483877) (by norm_num)
theorem B2638003 : Blo 1951435 2638003 := bstep (se 1 (by rfl) ⟨1978502, by rfl⟩ : syracuseStep 2638003 = 3957005) B3957005
theorem B3517337 : Blo 1951435 3517337 := bstep (se 2 (by rfl) ⟨1319001, by rfl⟩ : syracuseStep 3517337 = 2638003) B2638003
theorem B9379565 : Blo 1951435 9379565 := bstep (se 3 (by rfl) ⟨1758668, by rfl⟩ : syracuseStep 9379565 = 3517337) B3517337
theorem B6253043 : Blo 1951435 6253043 := bstep (se 1 (by rfl) ⟨4689782, by rfl⟩ : syracuseStep 6253043 = 9379565) B9379565
theorem B16674781 : Blo 1951435 16674781 := bstep (se 3 (by rfl) ⟨3126521, by rfl⟩ : syracuseStep 16674781 = 6253043) B6253043
theorem B22233041 : Blo 1951435 22233041 := bstep (se 2 (by rfl) ⟨8337390, by rfl⟩ : syracuseStep 22233041 = 16674781) B16674781
theorem B14822027 : Blo 1951435 14822027 := bstep (se 1 (by rfl) ⟨11116520, by rfl⟩ : syracuseStep 14822027 = 22233041) B22233041
theorem B9881351 : Blo 1951435 9881351 := bstep (se 1 (by rfl) ⟨7411013, by rfl⟩ : syracuseStep 9881351 = 14822027) B14822027
theorem B6587567 : Blo 1951435 6587567 := bstep (se 1 (by rfl) ⟨4940675, by rfl⟩ : syracuseStep 6587567 = 9881351) B9881351
theorem B4391711 : Blo 1951435 4391711 := bstep (se 1 (by rfl) ⟨3293783, by rfl⟩ : syracuseStep 4391711 = 6587567) B6587567
theorem B2927807 : Blo 1951435 2927807 := bstep (se 1 (by rfl) ⟨2195855, by rfl⟩ : syracuseStep 2927807 = 4391711) B4391711
theorem B1951871 : Blo 1951435 1951871 := bstep (se 1 (by rfl) ⟨1463903, by rfl⟩ : syracuseStep 1951871 = 2927807) B2927807
theorem B2927813 : Blo 1951435 2927813 := bbase (se 4 (by rfl) ⟨274482, by rfl⟩ : syracuseStep 2927813 = 548965) (by norm_num)
theorem B1951875 : Blo 1951435 1951875 := bstep (se 1 (by rfl) ⟨1463906, by rfl⟩ : syracuseStep 1951875 = 2927813) B2927813
theorem B3293797 : Blo 1951435 3293797 := bbase (se 4 (by rfl) ⟨308793, by rfl⟩ : syracuseStep 3293797 = 617587) (by norm_num)
theorem B4391729 : Blo 1951435 4391729 := bstep (se 2 (by rfl) ⟨1646898, by rfl⟩ : syracuseStep 4391729 = 3293797) B3293797
theorem B2927819 : Blo 1951435 2927819 := bstep (se 1 (by rfl) ⟨2195864, by rfl⟩ : syracuseStep 2927819 = 4391729) B4391729
theorem B1951879 : Blo 1951435 1951879 := bstep (se 1 (by rfl) ⟨1463909, by rfl⟩ : syracuseStep 1951879 = 2927819) B2927819
theorem B2195869 : Blo 1951435 2195869 := bbase (se 3 (by rfl) ⟨411725, by rfl⟩ : syracuseStep 2195869 = 823451) (by norm_num)
theorem B2927825 : Blo 1951435 2927825 := bstep (se 2 (by rfl) ⟨1097934, by rfl⟩ : syracuseStep 2927825 = 2195869) B2195869
theorem B1951883 : Blo 1951435 1951883 := bstep (se 1 (by rfl) ⟨1463912, by rfl⟩ : syracuseStep 1951883 = 2927825) B2927825
theorem B6587621 : Blo 1951435 6587621 := bbase (se 4 (by rfl) ⟨617589, by rfl⟩ : syracuseStep 6587621 = 1235179) (by norm_num)
theorem B4391747 : Blo 1951435 4391747 := bstep (se 1 (by rfl) ⟨3293810, by rfl⟩ : syracuseStep 4391747 = 6587621) B6587621
theorem B2927831 : Blo 1951435 2927831 := bstep (se 1 (by rfl) ⟨2195873, by rfl⟩ : syracuseStep 2927831 = 4391747) B4391747
theorem B1951887 : Blo 1951435 1951887 := bstep (se 1 (by rfl) ⟨1463915, by rfl⟩ : syracuseStep 1951887 = 2927831) B2927831
theorem B2927837 : Blo 1951435 2927837 := bbase (se 3 (by rfl) ⟨548969, by rfl⟩ : syracuseStep 2927837 = 1097939) (by norm_num)
theorem B1951891 : Blo 1951435 1951891 := bstep (se 1 (by rfl) ⟨1463918, by rfl⟩ : syracuseStep 1951891 = 2927837) B2927837
theorem B4391765 : Blo 1951435 4391765 := bbase (se 9 (by rfl) ⟨12866, by rfl⟩ : syracuseStep 4391765 = 25733) (by norm_num)
theorem B2927843 : Blo 1951435 2927843 := bstep (se 1 (by rfl) ⟨2195882, by rfl⟩ : syracuseStep 2927843 = 4391765) B4391765
theorem B1951895 : Blo 1951435 1951895 := bstep (se 1 (by rfl) ⟨1463921, by rfl⟩ : syracuseStep 1951895 = 2927843) B2927843
theorem B5558341 : Blo 1951435 5558341 := bbase (se 4 (by rfl) ⟨521094, by rfl⟩ : syracuseStep 5558341 = 1042189) (by norm_num)
theorem B7411121 : Blo 1951435 7411121 := bstep (se 2 (by rfl) ⟨2779170, by rfl⟩ : syracuseStep 7411121 = 5558341) B5558341
theorem B4940747 : Blo 1951435 4940747 := bstep (se 1 (by rfl) ⟨3705560, by rfl⟩ : syracuseStep 4940747 = 7411121) B7411121
theorem B3293831 : Blo 1951435 3293831 := bstep (se 1 (by rfl) ⟨2470373, by rfl⟩ : syracuseStep 3293831 = 4940747) B4940747
theorem B2195887 : Blo 1951435 2195887 := bstep (se 1 (by rfl) ⟨1646915, by rfl⟩ : syracuseStep 2195887 = 3293831) B3293831
theorem B2927849 : Blo 1951435 2927849 := bstep (se 2 (by rfl) ⟨1097943, by rfl⟩ : syracuseStep 2927849 = 2195887) B2195887
theorem B1951899 : Blo 1951435 1951899 := bstep (se 1 (by rfl) ⟨1463924, by rfl⟩ : syracuseStep 1951899 = 2927849) B2927849
theorem B4283293 : Blo 1951435 4283293 := bbase (se 3 (by rfl) ⟨803117, by rfl⟩ : syracuseStep 4283293 = 1606235) (by norm_num)
theorem B5711057 : Blo 1951435 5711057 := bstep (se 2 (by rfl) ⟨2141646, by rfl⟩ : syracuseStep 5711057 = 4283293) B4283293
theorem B3807371 : Blo 1951435 3807371 := bstep (se 1 (by rfl) ⟨2855528, by rfl⟩ : syracuseStep 3807371 = 5711057) B5711057
theorem B10152989 : Blo 1951435 10152989 := bstep (se 3 (by rfl) ⟨1903685, by rfl⟩ : syracuseStep 10152989 = 3807371) B3807371
theorem B6768659 : Blo 1951435 6768659 := bstep (se 1 (by rfl) ⟨5076494, by rfl⟩ : syracuseStep 6768659 = 10152989) B10152989
theorem B4512439 : Blo 1951435 4512439 := bstep (se 1 (by rfl) ⟨3384329, by rfl⟩ : syracuseStep 4512439 = 6768659) B6768659
theorem B24066341 : Blo 1951435 24066341 := bstep (se 4 (by rfl) ⟨2256219, by rfl⟩ : syracuseStep 24066341 = 4512439) B4512439
theorem B16044227 : Blo 1951435 16044227 := bstep (se 1 (by rfl) ⟨12033170, by rfl⟩ : syracuseStep 16044227 = 24066341) B24066341
theorem B10696151 : Blo 1951435 10696151 := bstep (se 1 (by rfl) ⟨8022113, by rfl⟩ : syracuseStep 10696151 = 16044227) B16044227
theorem B28523069 : Blo 1951435 28523069 := bstep (se 3 (by rfl) ⟨5348075, by rfl⟩ : syracuseStep 28523069 = 10696151) B10696151
theorem B19015379 : Blo 1951435 19015379 := bstep (se 1 (by rfl) ⟨14261534, by rfl⟩ : syracuseStep 19015379 = 28523069) B28523069
theorem B12676919 : Blo 1951435 12676919 := bstep (se 1 (by rfl) ⟨9507689, by rfl⟩ : syracuseStep 12676919 = 19015379) B19015379
theorem B33805117 : Blo 1951435 33805117 := bstep (se 3 (by rfl) ⟨6338459, by rfl⟩ : syracuseStep 33805117 = 12676919) B12676919
theorem B180293957 : Blo 1951435 180293957 := bstep (se 4 (by rfl) ⟨16902558, by rfl⟩ : syracuseStep 180293957 = 33805117) B33805117
theorem B120195971 : Blo 1951435 120195971 := bstep (se 1 (by rfl) ⟨90146978, by rfl⟩ : syracuseStep 120195971 = 180293957) B180293957
theorem B80130647 : Blo 1951435 80130647 := bstep (se 1 (by rfl) ⟨60097985, by rfl⟩ : syracuseStep 80130647 = 120195971) B120195971
theorem B213681725 : Blo 1951435 213681725 := bstep (se 3 (by rfl) ⟨40065323, by rfl⟩ : syracuseStep 213681725 = 80130647) B80130647
theorem B142454483 : Blo 1951435 142454483 := bstep (se 1 (by rfl) ⟨106840862, by rfl⟩ : syracuseStep 142454483 = 213681725) B213681725
theorem B94969655 : Blo 1951435 94969655 := bstep (se 1 (by rfl) ⟨71227241, by rfl⟩ : syracuseStep 94969655 = 142454483) B142454483
theorem B63313103 : Blo 1951435 63313103 := bstep (se 1 (by rfl) ⟨47484827, by rfl⟩ : syracuseStep 63313103 = 94969655) B94969655
theorem B42208735 : Blo 1951435 42208735 := bstep (se 1 (by rfl) ⟨31656551, by rfl⟩ : syracuseStep 42208735 = 63313103) B63313103
theorem B56278313 : Blo 1951435 56278313 := bstep (se 2 (by rfl) ⟨21104367, by rfl⟩ : syracuseStep 56278313 = 42208735) B42208735
theorem B37518875 : Blo 1951435 37518875 := bstep (se 1 (by rfl) ⟨28139156, by rfl⟩ : syracuseStep 37518875 = 56278313) B56278313
theorem B25012583 : Blo 1951435 25012583 := bstep (se 1 (by rfl) ⟨18759437, by rfl⟩ : syracuseStep 25012583 = 37518875) B37518875
theorem B16675055 : Blo 1951435 16675055 := bstep (se 1 (by rfl) ⟨12506291, by rfl⟩ : syracuseStep 16675055 = 25012583) B25012583
theorem B11116703 : Blo 1951435 11116703 := bstep (se 1 (by rfl) ⟨8337527, by rfl⟩ : syracuseStep 11116703 = 16675055) B16675055
theorem B7411135 : Blo 1951435 7411135 := bstep (se 1 (by rfl) ⟨5558351, by rfl⟩ : syracuseStep 7411135 = 11116703) B11116703
theorem B9881513 : Blo 1951435 9881513 := bstep (se 2 (by rfl) ⟨3705567, by rfl⟩ : syracuseStep 9881513 = 7411135) B7411135
theorem B6587675 : Blo 1951435 6587675 := bstep (se 1 (by rfl) ⟨4940756, by rfl⟩ : syracuseStep 6587675 = 9881513) B9881513
theorem B4391783 : Blo 1951435 4391783 := bstep (se 1 (by rfl) ⟨3293837, by rfl⟩ : syracuseStep 4391783 = 6587675) B6587675
theorem B2927855 : Blo 1951435 2927855 := bstep (se 1 (by rfl) ⟨2195891, by rfl⟩ : syracuseStep 2927855 = 4391783) B4391783
theorem B1951903 : Blo 1951435 1951903 := bstep (se 1 (by rfl) ⟨1463927, by rfl⟩ : syracuseStep 1951903 = 2927855) B2927855
theorem B2927861 : Blo 1951435 2927861 := bbase (se 5 (by rfl) ⟨137243, by rfl⟩ : syracuseStep 2927861 = 274487) (by norm_num)
theorem B1951907 : Blo 1951435 1951907 := bstep (se 1 (by rfl) ⟨1463930, by rfl⟩ : syracuseStep 1951907 = 2927861) B2927861
theorem B2225861 : Blo 1951435 2225861 := bbase (se 4 (by rfl) ⟨208674, by rfl⟩ : syracuseStep 2225861 = 417349) (by norm_num)
theorem B23742517 : Blo 1951435 23742517 := bstep (se 5 (by rfl) ⟨1112930, by rfl⟩ : syracuseStep 23742517 = 2225861) B2225861
theorem B31656689 : Blo 1951435 31656689 := bstep (se 2 (by rfl) ⟨11871258, by rfl⟩ : syracuseStep 31656689 = 23742517) B23742517
theorem B21104459 : Blo 1951435 21104459 := bstep (se 1 (by rfl) ⟨15828344, by rfl⟩ : syracuseStep 21104459 = 31656689) B31656689
theorem B14069639 : Blo 1951435 14069639 := bstep (se 1 (by rfl) ⟨10552229, by rfl⟩ : syracuseStep 14069639 = 21104459) B21104459
theorem B9379759 : Blo 1951435 9379759 := bstep (se 1 (by rfl) ⟨7034819, by rfl⟩ : syracuseStep 9379759 = 14069639) B14069639
theorem B12506345 : Blo 1951435 12506345 := bstep (se 2 (by rfl) ⟨4689879, by rfl⟩ : syracuseStep 12506345 = 9379759) B9379759
theorem B8337563 : Blo 1951435 8337563 := bstep (se 1 (by rfl) ⟨6253172, by rfl⟩ : syracuseStep 8337563 = 12506345) B12506345
theorem B5558375 : Blo 1951435 5558375 := bstep (se 1 (by rfl) ⟨4168781, by rfl⟩ : syracuseStep 5558375 = 8337563) B8337563
theorem B3705583 : Blo 1951435 3705583 := bstep (se 1 (by rfl) ⟨2779187, by rfl⟩ : syracuseStep 3705583 = 5558375) B5558375
theorem B4940777 : Blo 1951435 4940777 := bstep (se 2 (by rfl) ⟨1852791, by rfl⟩ : syracuseStep 4940777 = 3705583) B3705583
theorem B3293851 : Blo 1951435 3293851 := bstep (se 1 (by rfl) ⟨2470388, by rfl⟩ : syracuseStep 3293851 = 4940777) B4940777
theorem B4391801 : Blo 1951435 4391801 := bstep (se 2 (by rfl) ⟨1646925, by rfl⟩ : syracuseStep 4391801 = 3293851) B3293851
theorem B2927867 : Blo 1951435 2927867 := bstep (se 1 (by rfl) ⟨2195900, by rfl⟩ : syracuseStep 2927867 = 4391801) B4391801
theorem B1951911 : Blo 1951435 1951911 := bstep (se 1 (by rfl) ⟨1463933, by rfl⟩ : syracuseStep 1951911 = 2927867) B2927867
theorem B2195905 : Blo 1951435 2195905 := bbase (se 2 (by rfl) ⟨823464, by rfl⟩ : syracuseStep 2195905 = 1646929) (by norm_num)
theorem B2927873 : Blo 1951435 2927873 := bstep (se 2 (by rfl) ⟨1097952, by rfl⟩ : syracuseStep 2927873 = 2195905) B2195905
theorem B1951915 : Blo 1951435 1951915 := bstep (se 1 (by rfl) ⟨1463936, by rfl⟩ : syracuseStep 1951915 = 2927873) B2927873
theorem B4940797 : Blo 1951435 4940797 := bbase (se 3 (by rfl) ⟨926399, by rfl⟩ : syracuseStep 4940797 = 1852799) (by norm_num)
theorem B6587729 : Blo 1951435 6587729 := bstep (se 2 (by rfl) ⟨2470398, by rfl⟩ : syracuseStep 6587729 = 4940797) B4940797
theorem B4391819 : Blo 1951435 4391819 := bstep (se 1 (by rfl) ⟨3293864, by rfl⟩ : syracuseStep 4391819 = 6587729) B6587729
theorem B2927879 : Blo 1951435 2927879 := bstep (se 1 (by rfl) ⟨2195909, by rfl⟩ : syracuseStep 2927879 = 4391819) B4391819
theorem B1951919 : Blo 1951435 1951919 := bstep (se 1 (by rfl) ⟨1463939, by rfl⟩ : syracuseStep 1951919 = 2927879) B2927879
theorem B2927885 : Blo 1951435 2927885 := bbase (se 3 (by rfl) ⟨548978, by rfl⟩ : syracuseStep 2927885 = 1097957) (by norm_num)
theorem B1951923 : Blo 1951435 1951923 := bstep (se 1 (by rfl) ⟨1463942, by rfl⟩ : syracuseStep 1951923 = 2927885) B2927885
theorem B4391837 : Blo 1951435 4391837 := bbase (se 3 (by rfl) ⟨823469, by rfl⟩ : syracuseStep 4391837 = 1646939) (by norm_num)
theorem B2927891 : Blo 1951435 2927891 := bstep (se 1 (by rfl) ⟨2195918, by rfl⟩ : syracuseStep 2927891 = 4391837) B4391837
theorem B1951927 : Blo 1951435 1951927 := bstep (se 1 (by rfl) ⟨1463945, by rfl⟩ : syracuseStep 1951927 = 2927891) B2927891
theorem B3293885 : Blo 1951435 3293885 := bbase (se 3 (by rfl) ⟨617603, by rfl⟩ : syracuseStep 3293885 = 1235207) (by norm_num)
theorem B2195923 : Blo 1951435 2195923 := bstep (se 1 (by rfl) ⟨1646942, by rfl⟩ : syracuseStep 2195923 = 3293885) B3293885
theorem B2927897 : Blo 1951435 2927897 := bstep (se 2 (by rfl) ⟨1097961, by rfl⟩ : syracuseStep 2927897 = 2195923) B2195923
theorem B1951931 : Blo 1951435 1951931 := bstep (se 1 (by rfl) ⟨1463948, by rfl⟩ : syracuseStep 1951931 = 2927897) B2927897
theorem B11116885 : Blo 1951435 11116885 := bbase (se 10 (by rfl) ⟨16284, by rfl⟩ : syracuseStep 11116885 = 32569) (by norm_num)
theorem B14822513 : Blo 1951435 14822513 := bstep (se 2 (by rfl) ⟨5558442, by rfl⟩ : syracuseStep 14822513 = 11116885) B11116885
theorem B9881675 : Blo 1951435 9881675 := bstep (se 1 (by rfl) ⟨7411256, by rfl⟩ : syracuseStep 9881675 = 14822513) B14822513
theorem B6587783 : Blo 1951435 6587783 := bstep (se 1 (by rfl) ⟨4940837, by rfl⟩ : syracuseStep 6587783 = 9881675) B9881675
theorem B4391855 : Blo 1951435 4391855 := bstep (se 1 (by rfl) ⟨3293891, by rfl⟩ : syracuseStep 4391855 = 6587783) B6587783
theorem B2927903 : Blo 1951435 2927903 := bstep (se 1 (by rfl) ⟨2195927, by rfl⟩ : syracuseStep 2927903 = 4391855) B4391855
theorem B1951935 : Blo 1951435 1951935 := bstep (se 1 (by rfl) ⟨1463951, by rfl⟩ : syracuseStep 1951935 = 2927903) B2927903
theorem B2927909 : Blo 1951435 2927909 := bbase (se 4 (by rfl) ⟨274491, by rfl⟩ : syracuseStep 2927909 = 548983) (by norm_num)
theorem B1951939 : Blo 1951435 1951939 := bstep (se 1 (by rfl) ⟨1463954, by rfl⟩ : syracuseStep 1951939 = 2927909) B2927909
theorem B2470429 : Blo 1951435 2470429 := bbase (se 3 (by rfl) ⟨463205, by rfl⟩ : syracuseStep 2470429 = 926411) (by norm_num)
theorem B3293905 : Blo 1951435 3293905 := bstep (se 2 (by rfl) ⟨1235214, by rfl⟩ : syracuseStep 3293905 = 2470429) B2470429
theorem B4391873 : Blo 1951435 4391873 := bstep (se 2 (by rfl) ⟨1646952, by rfl⟩ : syracuseStep 4391873 = 3293905) B3293905
theorem B2927915 : Blo 1951435 2927915 := bstep (se 1 (by rfl) ⟨2195936, by rfl⟩ : syracuseStep 2927915 = 4391873) B4391873
theorem B1951943 : Blo 1951435 1951943 := bstep (se 1 (by rfl) ⟨1463957, by rfl⟩ : syracuseStep 1951943 = 2927915) B2927915
theorem B2195941 : Blo 1951435 2195941 := bbase (se 4 (by rfl) ⟨205869, by rfl⟩ : syracuseStep 2195941 = 411739) (by norm_num)
theorem B2927921 : Blo 1951435 2927921 := bstep (se 2 (by rfl) ⟨1097970, by rfl⟩ : syracuseStep 2927921 = 2195941) B2195941
theorem B1951947 : Blo 1951435 1951947 := bstep (se 1 (by rfl) ⟨1463960, by rfl⟩ : syracuseStep 1951947 = 2927921) B2927921
theorem B6253301 : Blo 1951435 6253301 := bbase (se 5 (by rfl) ⟨293123, by rfl⟩ : syracuseStep 6253301 = 586247) (by norm_num)
theorem B4168867 : Blo 1951435 4168867 := bstep (se 1 (by rfl) ⟨3126650, by rfl⟩ : syracuseStep 4168867 = 6253301) B6253301
theorem B5558489 : Blo 1951435 5558489 := bstep (se 2 (by rfl) ⟨2084433, by rfl⟩ : syracuseStep 5558489 = 4168867) B4168867
theorem B3705659 : Blo 1951435 3705659 := bstep (se 1 (by rfl) ⟨2779244, by rfl⟩ : syracuseStep 3705659 = 5558489) B5558489
theorem B2470439 : Blo 1951435 2470439 := bstep (se 1 (by rfl) ⟨1852829, by rfl⟩ : syracuseStep 2470439 = 3705659) B3705659
theorem B6587837 : Blo 1951435 6587837 := bstep (se 3 (by rfl) ⟨1235219, by rfl⟩ : syracuseStep 6587837 = 2470439) B2470439
theorem B4391891 : Blo 1951435 4391891 := bstep (se 1 (by rfl) ⟨3293918, by rfl⟩ : syracuseStep 4391891 = 6587837) B6587837
theorem B2927927 : Blo 1951435 2927927 := bstep (se 1 (by rfl) ⟨2195945, by rfl⟩ : syracuseStep 2927927 = 4391891) B4391891
theorem B1951951 : Blo 1951435 1951951 := bstep (se 1 (by rfl) ⟨1463963, by rfl⟩ : syracuseStep 1951951 = 2927927) B2927927
theorem B2927933 : Blo 1951435 2927933 := bbase (se 3 (by rfl) ⟨548987, by rfl⟩ : syracuseStep 2927933 = 1097975) (by norm_num)
theorem B1951955 : Blo 1951435 1951955 := bstep (se 1 (by rfl) ⟨1463966, by rfl⟩ : syracuseStep 1951955 = 2927933) B2927933
theorem B4391909 : Blo 1951435 4391909 := bbase (se 4 (by rfl) ⟨411741, by rfl⟩ : syracuseStep 4391909 = 823483) (by norm_num)
theorem B2927939 : Blo 1951435 2927939 := bstep (se 1 (by rfl) ⟨2195954, by rfl⟩ : syracuseStep 2927939 = 4391909) B4391909
theorem B1951959 : Blo 1951435 1951959 := bstep (se 1 (by rfl) ⟨1463969, by rfl⟩ : syracuseStep 1951959 = 2927939) B2927939
theorem B4940909 : Blo 1951435 4940909 := bbase (se 3 (by rfl) ⟨926420, by rfl⟩ : syracuseStep 4940909 = 1852841) (by norm_num)
theorem B3293939 : Blo 1951435 3293939 := bstep (se 1 (by rfl) ⟨2470454, by rfl⟩ : syracuseStep 3293939 = 4940909) B4940909
theorem B2195959 : Blo 1951435 2195959 := bstep (se 1 (by rfl) ⟨1646969, by rfl⟩ : syracuseStep 2195959 = 3293939) B3293939
theorem B2927945 : Blo 1951435 2927945 := bstep (se 2 (by rfl) ⟨1097979, by rfl⟩ : syracuseStep 2927945 = 2195959) B2195959
theorem B1951963 : Blo 1951435 1951963 := bstep (se 1 (by rfl) ⟨1463972, by rfl⟩ : syracuseStep 1951963 = 2927945) B2927945
theorem B4168901 : Blo 1951435 4168901 := bbase (se 4 (by rfl) ⟨390834, by rfl⟩ : syracuseStep 4168901 = 781669) (by norm_num)
theorem B2779267 : Blo 1951435 2779267 := bstep (se 1 (by rfl) ⟨2084450, by rfl⟩ : syracuseStep 2779267 = 4168901) B4168901
theorem B3705689 : Blo 1951435 3705689 := bstep (se 2 (by rfl) ⟨1389633, by rfl⟩ : syracuseStep 3705689 = 2779267) B2779267
theorem B9881837 : Blo 1951435 9881837 := bstep (se 3 (by rfl) ⟨1852844, by rfl⟩ : syracuseStep 9881837 = 3705689) B3705689
theorem B6587891 : Blo 1951435 6587891 := bstep (se 1 (by rfl) ⟨4940918, by rfl⟩ : syracuseStep 6587891 = 9881837) B9881837
theorem B4391927 : Blo 1951435 4391927 := bstep (se 1 (by rfl) ⟨3293945, by rfl⟩ : syracuseStep 4391927 = 6587891) B6587891
theorem B2927951 : Blo 1951435 2927951 := bstep (se 1 (by rfl) ⟨2195963, by rfl⟩ : syracuseStep 2927951 = 4391927) B4391927
theorem B1951967 : Blo 1951435 1951967 := bstep (se 1 (by rfl) ⟨1463975, by rfl⟩ : syracuseStep 1951967 = 2927951) B2927951
theorem B2927957 : Blo 1951435 2927957 := bbase (se 11 (by rfl) ⟨2144, by rfl⟩ : syracuseStep 2927957 = 4289) (by norm_num)
theorem B1951971 : Blo 1951435 1951971 := bstep (se 1 (by rfl) ⟨1463978, by rfl⟩ : syracuseStep 1951971 = 2927957) B2927957
theorem B2345017 : Blo 1951435 2345017 := bbase (se 2 (by rfl) ⟨879381, by rfl⟩ : syracuseStep 2345017 = 1758763) (by norm_num)
theorem B3126689 : Blo 1951435 3126689 := bstep (se 2 (by rfl) ⟨1172508, by rfl⟩ : syracuseStep 3126689 = 2345017) B2345017
theorem B2084459 : Blo 1951435 2084459 := bstep (se 1 (by rfl) ⟨1563344, by rfl⟩ : syracuseStep 2084459 = 3126689) B3126689
theorem B5558557 : Blo 1951435 5558557 := bstep (se 3 (by rfl) ⟨1042229, by rfl⟩ : syracuseStep 5558557 = 2084459) B2084459
theorem B7411409 : Blo 1951435 7411409 := bstep (se 2 (by rfl) ⟨2779278, by rfl⟩ : syracuseStep 7411409 = 5558557) B5558557
theorem B4940939 : Blo 1951435 4940939 := bstep (se 1 (by rfl) ⟨3705704, by rfl⟩ : syracuseStep 4940939 = 7411409) B7411409
theorem B3293959 : Blo 1951435 3293959 := bstep (se 1 (by rfl) ⟨2470469, by rfl⟩ : syracuseStep 3293959 = 4940939) B4940939
theorem B4391945 : Blo 1951435 4391945 := bstep (se 2 (by rfl) ⟨1646979, by rfl⟩ : syracuseStep 4391945 = 3293959) B3293959
theorem B2927963 : Blo 1951435 2927963 := bstep (se 1 (by rfl) ⟨2195972, by rfl⟩ : syracuseStep 2927963 = 4391945) B4391945
theorem B1951975 : Blo 1951435 1951975 := bstep (se 1 (by rfl) ⟨1463981, by rfl⟩ : syracuseStep 1951975 = 2927963) B2927963
theorem B2195977 : Blo 1951435 2195977 := bbase (se 2 (by rfl) ⟨823491, by rfl⟩ : syracuseStep 2195977 = 1646983) (by norm_num)
theorem B2927969 : Blo 1951435 2927969 := bstep (se 2 (by rfl) ⟨1097988, by rfl⟩ : syracuseStep 2927969 = 2195977) B2195977
theorem B1951979 : Blo 1951435 1951979 := bstep (se 1 (by rfl) ⟨1463984, by rfl⟩ : syracuseStep 1951979 = 2927969) B2927969
theorem B7131061 : Blo 1951435 7131061 := bbase (se 5 (by rfl) ⟨334268, by rfl⟩ : syracuseStep 7131061 = 668537) (by norm_num)
theorem B38032325 : Blo 1951435 38032325 := bstep (se 4 (by rfl) ⟨3565530, by rfl⟩ : syracuseStep 38032325 = 7131061) B7131061
theorem B25354883 : Blo 1951435 25354883 := bstep (se 1 (by rfl) ⟨19016162, by rfl⟩ : syracuseStep 25354883 = 38032325) B38032325
theorem B16903255 : Blo 1951435 16903255 := bstep (se 1 (by rfl) ⟨12677441, by rfl⟩ : syracuseStep 16903255 = 25354883) B25354883
theorem B22537673 : Blo 1951435 22537673 := bstep (se 2 (by rfl) ⟨8451627, by rfl⟩ : syracuseStep 22537673 = 16903255) B16903255
theorem B15025115 : Blo 1951435 15025115 := bstep (se 1 (by rfl) ⟨11268836, by rfl⟩ : syracuseStep 15025115 = 22537673) B22537673
theorem B10016743 : Blo 1951435 10016743 := bstep (se 1 (by rfl) ⟨7512557, by rfl⟩ : syracuseStep 10016743 = 15025115) B15025115
theorem B13355657 : Blo 1951435 13355657 := bstep (se 2 (by rfl) ⟨5008371, by rfl⟩ : syracuseStep 13355657 = 10016743) B10016743
theorem B8903771 : Blo 1951435 8903771 := bstep (se 1 (by rfl) ⟨6677828, by rfl⟩ : syracuseStep 8903771 = 13355657) B13355657
theorem B5935847 : Blo 1951435 5935847 := bstep (se 1 (by rfl) ⟨4451885, by rfl⟩ : syracuseStep 5935847 = 8903771) B8903771
theorem B63315701 : Blo 1951435 63315701 := bstep (se 5 (by rfl) ⟨2967923, by rfl⟩ : syracuseStep 63315701 = 5935847) B5935847
theorem B42210467 : Blo 1951435 42210467 := bstep (se 1 (by rfl) ⟨31657850, by rfl⟩ : syracuseStep 42210467 = 63315701) B63315701
theorem B28140311 : Blo 1951435 28140311 := bstep (se 1 (by rfl) ⟨21105233, by rfl⟩ : syracuseStep 28140311 = 42210467) B42210467
theorem B18760207 : Blo 1951435 18760207 := bstep (se 1 (by rfl) ⟨14070155, by rfl⟩ : syracuseStep 18760207 = 28140311) B28140311
theorem B25013609 : Blo 1951435 25013609 := bstep (se 2 (by rfl) ⟨9380103, by rfl⟩ : syracuseStep 25013609 = 18760207) B18760207
theorem B16675739 : Blo 1951435 16675739 := bstep (se 1 (by rfl) ⟨12506804, by rfl⟩ : syracuseStep 16675739 = 25013609) B25013609
theorem B11117159 : Blo 1951435 11117159 := bstep (se 1 (by rfl) ⟨8337869, by rfl⟩ : syracuseStep 11117159 = 16675739) B16675739
theorem B7411439 : Blo 1951435 7411439 := bstep (se 1 (by rfl) ⟨5558579, by rfl⟩ : syracuseStep 7411439 = 11117159) B11117159
theorem B4940959 : Blo 1951435 4940959 := bstep (se 1 (by rfl) ⟨3705719, by rfl⟩ : syracuseStep 4940959 = 7411439) B7411439
theorem B6587945 : Blo 1951435 6587945 := bstep (se 2 (by rfl) ⟨2470479, by rfl⟩ : syracuseStep 6587945 = 4940959) B4940959
theorem B4391963 : Blo 1951435 4391963 := bstep (se 1 (by rfl) ⟨3293972, by rfl⟩ : syracuseStep 4391963 = 6587945) B6587945
theorem B2927975 : Blo 1951435 2927975 := bstep (se 1 (by rfl) ⟨2195981, by rfl⟩ : syracuseStep 2927975 = 4391963) B4391963
theorem B1951983 : Blo 1951435 1951983 := bstep (se 1 (by rfl) ⟨1463987, by rfl⟩ : syracuseStep 1951983 = 2927975) B2927975
theorem B2927981 : Blo 1951435 2927981 := bbase (se 3 (by rfl) ⟨548996, by rfl⟩ : syracuseStep 2927981 = 1097993) (by norm_num)
theorem B1951987 : Blo 1951435 1951987 := bstep (se 1 (by rfl) ⟨1463990, by rfl⟩ : syracuseStep 1951987 = 2927981) B2927981
theorem B4391981 : Blo 1951435 4391981 := bbase (se 3 (by rfl) ⟨823496, by rfl⟩ : syracuseStep 4391981 = 1646993) (by norm_num)
theorem B2927987 : Blo 1951435 2927987 := bstep (se 1 (by rfl) ⟨2195990, by rfl⟩ : syracuseStep 2927987 = 4391981) B4391981
theorem B1951991 : Blo 1951435 1951991 := bstep (se 1 (by rfl) ⟨1463993, by rfl⟩ : syracuseStep 1951991 = 2927987) B2927987
theorem B2345041 : Blo 1951435 2345041 := bbase (se 2 (by rfl) ⟨879390, by rfl⟩ : syracuseStep 2345041 = 1758781) (by norm_num)
theorem B12506885 : Blo 1951435 12506885 := bstep (se 4 (by rfl) ⟨1172520, by rfl⟩ : syracuseStep 12506885 = 2345041) B2345041
theorem B8337923 : Blo 1951435 8337923 := bstep (se 1 (by rfl) ⟨6253442, by rfl⟩ : syracuseStep 8337923 = 12506885) B12506885
theorem B5558615 : Blo 1951435 5558615 := bstep (se 1 (by rfl) ⟨4168961, by rfl⟩ : syracuseStep 5558615 = 8337923) B8337923
theorem B3705743 : Blo 1951435 3705743 := bstep (se 1 (by rfl) ⟨2779307, by rfl⟩ : syracuseStep 3705743 = 5558615) B5558615
theorem B2470495 : Blo 1951435 2470495 := bstep (se 1 (by rfl) ⟨1852871, by rfl⟩ : syracuseStep 2470495 = 3705743) B3705743
theorem B3293993 : Blo 1951435 3293993 := bstep (se 2 (by rfl) ⟨1235247, by rfl⟩ : syracuseStep 3293993 = 2470495) B2470495
theorem B2195995 : Blo 1951435 2195995 := bstep (se 1 (by rfl) ⟨1646996, by rfl⟩ : syracuseStep 2195995 = 3293993) B3293993
theorem B2927993 : Blo 1951435 2927993 := bstep (se 2 (by rfl) ⟨1097997, by rfl⟩ : syracuseStep 2927993 = 2195995) B2195995
theorem B1951995 : Blo 1951435 1951995 := bstep (se 1 (by rfl) ⟨1463996, by rfl⟩ : syracuseStep 1951995 = 2927993) B2927993
theorem B2345045 : Blo 1951435 2345045 := bbase (se 8 (by rfl) ⟨13740, by rfl⟩ : syracuseStep 2345045 = 27481) (by norm_num)
theorem B6253453 : Blo 1951435 6253453 := bstep (se 3 (by rfl) ⟨1172522, by rfl⟩ : syracuseStep 6253453 = 2345045) B2345045
theorem B33351749 : Blo 1951435 33351749 := bstep (se 4 (by rfl) ⟨3126726, by rfl⟩ : syracuseStep 33351749 = 6253453) B6253453
theorem B22234499 : Blo 1951435 22234499 := bstep (se 1 (by rfl) ⟨16675874, by rfl⟩ : syracuseStep 22234499 = 33351749) B33351749
theorem B14822999 : Blo 1951435 14822999 := bstep (se 1 (by rfl) ⟨11117249, by rfl⟩ : syracuseStep 14822999 = 22234499) B22234499
theorem B9881999 : Blo 1951435 9881999 := bstep (se 1 (by rfl) ⟨7411499, by rfl⟩ : syracuseStep 9881999 = 14822999) B14822999
theorem B6587999 : Blo 1951435 6587999 := bstep (se 1 (by rfl) ⟨4940999, by rfl⟩ : syracuseStep 6587999 = 9881999) B9881999
theorem B4391999 : Blo 1951435 4391999 := bstep (se 1 (by rfl) ⟨3293999, by rfl⟩ : syracuseStep 4391999 = 6587999) B6587999
theorem B2927999 : Blo 1951435 2927999 := bstep (se 1 (by rfl) ⟨2195999, by rfl⟩ : syracuseStep 2927999 = 4391999) B4391999
theorem B1951999 : Blo 1951435 1951999 := bstep (se 1 (by rfl) ⟨1463999, by rfl⟩ : syracuseStep 1951999 = 2927999) B2927999
theorem B2928005 : Blo 1951435 2928005 := bbase (se 4 (by rfl) ⟨274500, by rfl⟩ : syracuseStep 2928005 = 549001) (by norm_num)
theorem B1952003 : Blo 1951435 1952003 := bstep (se 1 (by rfl) ⟨1464002, by rfl⟩ : syracuseStep 1952003 = 2928005) B2928005
theorem B3294013 : Blo 1951435 3294013 := bbase (se 3 (by rfl) ⟨617627, by rfl⟩ : syracuseStep 3294013 = 1235255) (by norm_num)
theorem B4392017 : Blo 1951435 4392017 := bstep (se 2 (by rfl) ⟨1647006, by rfl⟩ : syracuseStep 4392017 = 3294013) B3294013
theorem B2928011 : Blo 1951435 2928011 := bstep (se 1 (by rfl) ⟨2196008, by rfl⟩ : syracuseStep 2928011 = 4392017) B4392017
theorem B1952007 : Blo 1951435 1952007 := bstep (se 1 (by rfl) ⟨1464005, by rfl⟩ : syracuseStep 1952007 = 2928011) B2928011
theorem B2196013 : Blo 1951435 2196013 := bbase (se 3 (by rfl) ⟨411752, by rfl⟩ : syracuseStep 2196013 = 823505) (by norm_num)
theorem B2928017 : Blo 1951435 2928017 := bstep (se 2 (by rfl) ⟨1098006, by rfl⟩ : syracuseStep 2928017 = 2196013) B2196013
theorem B1952011 : Blo 1951435 1952011 := bstep (se 1 (by rfl) ⟨1464008, by rfl⟩ : syracuseStep 1952011 = 2928017) B2928017
theorem B6588053 : Blo 1951435 6588053 := bbase (se 6 (by rfl) ⟨154407, by rfl⟩ : syracuseStep 6588053 = 308815) (by norm_num)
theorem B4392035 : Blo 1951435 4392035 := bstep (se 1 (by rfl) ⟨3294026, by rfl⟩ : syracuseStep 4392035 = 6588053) B6588053
theorem B2928023 : Blo 1951435 2928023 := bstep (se 1 (by rfl) ⟨2196017, by rfl⟩ : syracuseStep 2928023 = 4392035) B4392035
theorem B1952015 : Blo 1951435 1952015 := bstep (se 1 (by rfl) ⟨1464011, by rfl⟩ : syracuseStep 1952015 = 2928023) B2928023
theorem B2928029 : Blo 1951435 2928029 := bbase (se 3 (by rfl) ⟨549005, by rfl⟩ : syracuseStep 2928029 = 1098011) (by norm_num)
theorem B1952019 : Blo 1951435 1952019 := bstep (se 1 (by rfl) ⟨1464014, by rfl⟩ : syracuseStep 1952019 = 2928029) B2928029
theorem B4392053 : Blo 1951435 4392053 := bbase (se 5 (by rfl) ⟨205877, by rfl⟩ : syracuseStep 4392053 = 411755) (by norm_num)
theorem B2928035 : Blo 1951435 2928035 := bstep (se 1 (by rfl) ⟨2196026, by rfl⟩ : syracuseStep 2928035 = 4392053) B4392053
theorem B1952023 : Blo 1951435 1952023 := bstep (se 1 (by rfl) ⟨1464017, by rfl⟩ : syracuseStep 1952023 = 2928035) B2928035
theorem B16676117 : Blo 1951435 16676117 := bbase (se 6 (by rfl) ⟨390846, by rfl⟩ : syracuseStep 16676117 = 781693) (by norm_num)
theorem B11117411 : Blo 1951435 11117411 := bstep (se 1 (by rfl) ⟨8338058, by rfl⟩ : syracuseStep 11117411 = 16676117) B16676117
theorem B7411607 : Blo 1951435 7411607 := bstep (se 1 (by rfl) ⟨5558705, by rfl⟩ : syracuseStep 7411607 = 11117411) B11117411
theorem B4941071 : Blo 1951435 4941071 := bstep (se 1 (by rfl) ⟨3705803, by rfl⟩ : syracuseStep 4941071 = 7411607) B7411607
theorem B3294047 : Blo 1951435 3294047 := bstep (se 1 (by rfl) ⟨2470535, by rfl⟩ : syracuseStep 3294047 = 4941071) B4941071
theorem B2196031 : Blo 1951435 2196031 := bstep (se 1 (by rfl) ⟨1647023, by rfl⟩ : syracuseStep 2196031 = 3294047) B3294047
theorem B2928041 : Blo 1951435 2928041 := bstep (se 2 (by rfl) ⟨1098015, by rfl⟩ : syracuseStep 2928041 = 2196031) B2196031
theorem B1952027 : Blo 1951435 1952027 := bstep (se 1 (by rfl) ⟨1464020, by rfl⟩ : syracuseStep 1952027 = 2928041) B2928041
theorem B7411621 : Blo 1951435 7411621 := bbase (se 4 (by rfl) ⟨694839, by rfl⟩ : syracuseStep 7411621 = 1389679) (by norm_num)
theorem B9882161 : Blo 1951435 9882161 := bstep (se 2 (by rfl) ⟨3705810, by rfl⟩ : syracuseStep 9882161 = 7411621) B7411621
theorem B6588107 : Blo 1951435 6588107 := bstep (se 1 (by rfl) ⟨4941080, by rfl⟩ : syracuseStep 6588107 = 9882161) B9882161
theorem B4392071 : Blo 1951435 4392071 := bstep (se 1 (by rfl) ⟨3294053, by rfl⟩ : syracuseStep 4392071 = 6588107) B6588107
theorem B2928047 : Blo 1951435 2928047 := bstep (se 1 (by rfl) ⟨2196035, by rfl⟩ : syracuseStep 2928047 = 4392071) B4392071
theorem B1952031 : Blo 1951435 1952031 := bstep (se 1 (by rfl) ⟨1464023, by rfl⟩ : syracuseStep 1952031 = 2928047) B2928047
theorem B2928053 : Blo 1951435 2928053 := bbase (se 5 (by rfl) ⟨137252, by rfl⟩ : syracuseStep 2928053 = 274505) (by norm_num)
theorem B1952035 : Blo 1951435 1952035 := bstep (se 1 (by rfl) ⟨1464026, by rfl⟩ : syracuseStep 1952035 = 2928053) B2928053
theorem B4941101 : Blo 1951435 4941101 := bbase (se 3 (by rfl) ⟨926456, by rfl⟩ : syracuseStep 4941101 = 1852913) (by norm_num)
theorem B3294067 : Blo 1951435 3294067 := bstep (se 1 (by rfl) ⟨2470550, by rfl⟩ : syracuseStep 3294067 = 4941101) B4941101
theorem B4392089 : Blo 1951435 4392089 := bstep (se 2 (by rfl) ⟨1647033, by rfl⟩ : syracuseStep 4392089 = 3294067) B3294067
theorem B2928059 : Blo 1951435 2928059 := bstep (se 1 (by rfl) ⟨2196044, by rfl⟩ : syracuseStep 2928059 = 4392089) B4392089
theorem B1952039 : Blo 1951435 1952039 := bstep (se 1 (by rfl) ⟨1464029, by rfl⟩ : syracuseStep 1952039 = 2928059) B2928059
theorem B2196049 : Blo 1951435 2196049 := bbase (se 2 (by rfl) ⟨823518, by rfl⟩ : syracuseStep 2196049 = 1647037) (by norm_num)
theorem B2928065 : Blo 1951435 2928065 := bstep (se 2 (by rfl) ⟨1098024, by rfl⟩ : syracuseStep 2928065 = 2196049) B2196049
theorem B1952043 : Blo 1951435 1952043 := bstep (se 1 (by rfl) ⟨1464032, by rfl⟩ : syracuseStep 1952043 = 2928065) B2928065
theorem B2779381 : Blo 1951435 2779381 := bbase (se 5 (by rfl) ⟨130283, by rfl⟩ : syracuseStep 2779381 = 260567) (by norm_num)
theorem B3705841 : Blo 1951435 3705841 := bstep (se 2 (by rfl) ⟨1389690, by rfl⟩ : syracuseStep 3705841 = 2779381) B2779381
theorem B4941121 : Blo 1951435 4941121 := bstep (se 2 (by rfl) ⟨1852920, by rfl⟩ : syracuseStep 4941121 = 3705841) B3705841
theorem B6588161 : Blo 1951435 6588161 := bstep (se 2 (by rfl) ⟨2470560, by rfl⟩ : syracuseStep 6588161 = 4941121) B4941121
theorem B4392107 : Blo 1951435 4392107 := bstep (se 1 (by rfl) ⟨3294080, by rfl⟩ : syracuseStep 4392107 = 6588161) B6588161
theorem B2928071 : Blo 1951435 2928071 := bstep (se 1 (by rfl) ⟨2196053, by rfl⟩ : syracuseStep 2928071 = 4392107) B4392107
theorem B1952047 : Blo 1951435 1952047 := bstep (se 1 (by rfl) ⟨1464035, by rfl⟩ : syracuseStep 1952047 = 2928071) B2928071
theorem B2928077 : Blo 1951435 2928077 := bbase (se 3 (by rfl) ⟨549014, by rfl⟩ : syracuseStep 2928077 = 1098029) (by norm_num)
theorem B1952051 : Blo 1951435 1952051 := bstep (se 1 (by rfl) ⟨1464038, by rfl⟩ : syracuseStep 1952051 = 2928077) B2928077
theorem B4392125 : Blo 1951435 4392125 := bbase (se 3 (by rfl) ⟨823523, by rfl⟩ : syracuseStep 4392125 = 1647047) (by norm_num)
theorem B2928083 : Blo 1951435 2928083 := bstep (se 1 (by rfl) ⟨2196062, by rfl⟩ : syracuseStep 2928083 = 4392125) B4392125
theorem B1952055 : Blo 1951435 1952055 := bstep (se 1 (by rfl) ⟨1464041, by rfl⟩ : syracuseStep 1952055 = 2928083) B2928083
theorem B3294101 : Blo 1951435 3294101 := bbase (se 6 (by rfl) ⟨77205, by rfl⟩ : syracuseStep 3294101 = 154411) (by norm_num)
theorem B2196067 : Blo 1951435 2196067 := bstep (se 1 (by rfl) ⟨1647050, by rfl⟩ : syracuseStep 2196067 = 3294101) B3294101
theorem B2928089 : Blo 1951435 2928089 := bstep (se 2 (by rfl) ⟨1098033, by rfl⟩ : syracuseStep 2928089 = 2196067) B2196067
theorem B1952059 : Blo 1951435 1952059 := bstep (se 1 (by rfl) ⟨1464044, by rfl⟩ : syracuseStep 1952059 = 2928089) B2928089
theorem B12507317 : Blo 1951435 12507317 := bbase (se 5 (by rfl) ⟨586280, by rfl⟩ : syracuseStep 12507317 = 1172561) (by norm_num)
theorem B8338211 : Blo 1951435 8338211 := bstep (se 1 (by rfl) ⟨6253658, by rfl⟩ : syracuseStep 8338211 = 12507317) B12507317
theorem B5558807 : Blo 1951435 5558807 := bstep (se 1 (by rfl) ⟨4169105, by rfl⟩ : syracuseStep 5558807 = 8338211) B8338211
theorem B14823485 : Blo 1951435 14823485 := bstep (se 3 (by rfl) ⟨2779403, by rfl⟩ : syracuseStep 14823485 = 5558807) B5558807
theorem B9882323 : Blo 1951435 9882323 := bstep (se 1 (by rfl) ⟨7411742, by rfl⟩ : syracuseStep 9882323 = 14823485) B14823485
theorem B6588215 : Blo 1951435 6588215 := bstep (se 1 (by rfl) ⟨4941161, by rfl⟩ : syracuseStep 6588215 = 9882323) B9882323
theorem B4392143 : Blo 1951435 4392143 := bstep (se 1 (by rfl) ⟨3294107, by rfl⟩ : syracuseStep 4392143 = 6588215) B6588215
theorem B2928095 : Blo 1951435 2928095 := bstep (se 1 (by rfl) ⟨2196071, by rfl⟩ : syracuseStep 2928095 = 4392143) B4392143
theorem B1952063 : Blo 1951435 1952063 := bstep (se 1 (by rfl) ⟨1464047, by rfl⟩ : syracuseStep 1952063 = 2928095) B2928095
theorem B2928101 : Blo 1951435 2928101 := bbase (se 4 (by rfl) ⟨274509, by rfl⟩ : syracuseStep 2928101 = 549019) (by norm_num)
theorem B1952067 : Blo 1951435 1952067 := bstep (se 1 (by rfl) ⟨1464050, by rfl⟩ : syracuseStep 1952067 = 2928101) B2928101
theorem B2377129 : Blo 1951435 2377129 := bbase (se 2 (by rfl) ⟨891423, by rfl⟩ : syracuseStep 2377129 = 1782847) (by norm_num)
theorem B3169505 : Blo 1951435 3169505 := bstep (se 2 (by rfl) ⟨1188564, by rfl⟩ : syracuseStep 3169505 = 2377129) B2377129
theorem B2113003 : Blo 1951435 2113003 := bstep (se 1 (by rfl) ⟨1584752, by rfl⟩ : syracuseStep 2113003 = 3169505) B3169505
theorem B2817337 : Blo 1951435 2817337 := bstep (se 2 (by rfl) ⟨1056501, by rfl⟩ : syracuseStep 2817337 = 2113003) B2113003
theorem B3756449 : Blo 1951435 3756449 := bstep (se 2 (by rfl) ⟨1408668, by rfl⟩ : syracuseStep 3756449 = 2817337) B2817337
theorem B10017197 : Blo 1951435 10017197 := bstep (se 3 (by rfl) ⟨1878224, by rfl⟩ : syracuseStep 10017197 = 3756449) B3756449
theorem B6678131 : Blo 1951435 6678131 := bstep (se 1 (by rfl) ⟨5008598, by rfl⟩ : syracuseStep 6678131 = 10017197) B10017197
theorem B17808349 : Blo 1951435 17808349 := bstep (se 3 (by rfl) ⟨3339065, by rfl⟩ : syracuseStep 17808349 = 6678131) B6678131
theorem B23744465 : Blo 1951435 23744465 := bstep (se 2 (by rfl) ⟨8904174, by rfl⟩ : syracuseStep 23744465 = 17808349) B17808349
theorem B15829643 : Blo 1951435 15829643 := bstep (se 1 (by rfl) ⟨11872232, by rfl⟩ : syracuseStep 15829643 = 23744465) B23744465
theorem B10553095 : Blo 1951435 10553095 := bstep (se 1 (by rfl) ⟨7914821, by rfl⟩ : syracuseStep 10553095 = 15829643) B15829643
theorem B14070793 : Blo 1951435 14070793 := bstep (se 2 (by rfl) ⟨5276547, by rfl⟩ : syracuseStep 14070793 = 10553095) B10553095
theorem B18761057 : Blo 1951435 18761057 := bstep (se 2 (by rfl) ⟨7035396, by rfl⟩ : syracuseStep 18761057 = 14070793) B14070793
theorem B12507371 : Blo 1951435 12507371 := bstep (se 1 (by rfl) ⟨9380528, by rfl⟩ : syracuseStep 12507371 = 18761057) B18761057
theorem B8338247 : Blo 1951435 8338247 := bstep (se 1 (by rfl) ⟨6253685, by rfl⟩ : syracuseStep 8338247 = 12507371) B12507371
theorem B5558831 : Blo 1951435 5558831 := bstep (se 1 (by rfl) ⟨4169123, by rfl⟩ : syracuseStep 5558831 = 8338247) B8338247
theorem B3705887 : Blo 1951435 3705887 := bstep (se 1 (by rfl) ⟨2779415, by rfl⟩ : syracuseStep 3705887 = 5558831) B5558831
theorem B2470591 : Blo 1951435 2470591 := bstep (se 1 (by rfl) ⟨1852943, by rfl⟩ : syracuseStep 2470591 = 3705887) B3705887
theorem B3294121 : Blo 1951435 3294121 := bstep (se 2 (by rfl) ⟨1235295, by rfl⟩ : syracuseStep 3294121 = 2470591) B2470591
theorem B4392161 : Blo 1951435 4392161 := bstep (se 2 (by rfl) ⟨1647060, by rfl⟩ : syracuseStep 4392161 = 3294121) B3294121
theorem B2928107 : Blo 1951435 2928107 := bstep (se 1 (by rfl) ⟨2196080, by rfl⟩ : syracuseStep 2928107 = 4392161) B4392161
theorem B1952071 : Blo 1951435 1952071 := bstep (se 1 (by rfl) ⟨1464053, by rfl⟩ : syracuseStep 1952071 = 2928107) B2928107
theorem B2196085 : Blo 1951435 2196085 := bbase (se 5 (by rfl) ⟨102941, by rfl⟩ : syracuseStep 2196085 = 205883) (by norm_num)
theorem B2928113 : Blo 1951435 2928113 := bstep (se 2 (by rfl) ⟨1098042, by rfl⟩ : syracuseStep 2928113 = 2196085) B2196085
theorem B1952075 : Blo 1951435 1952075 := bstep (se 1 (by rfl) ⟨1464056, by rfl⟩ : syracuseStep 1952075 = 2928113) B2928113
theorem B2470601 : Blo 1951435 2470601 := bbase (se 2 (by rfl) ⟨926475, by rfl⟩ : syracuseStep 2470601 = 1852951) (by norm_num)
theorem B6588269 : Blo 1951435 6588269 := bstep (se 3 (by rfl) ⟨1235300, by rfl⟩ : syracuseStep 6588269 = 2470601) B2470601
theorem B4392179 : Blo 1951435 4392179 := bstep (se 1 (by rfl) ⟨3294134, by rfl⟩ : syracuseStep 4392179 = 6588269) B6588269
theorem B2928119 : Blo 1951435 2928119 := bstep (se 1 (by rfl) ⟨2196089, by rfl⟩ : syracuseStep 2928119 = 4392179) B4392179
theorem B1952079 : Blo 1951435 1952079 := bstep (se 1 (by rfl) ⟨1464059, by rfl⟩ : syracuseStep 1952079 = 2928119) B2928119
theorem B2928125 : Blo 1951435 2928125 := bbase (se 3 (by rfl) ⟨549023, by rfl⟩ : syracuseStep 2928125 = 1098047) (by norm_num)
theorem B1952083 : Blo 1951435 1952083 := bstep (se 1 (by rfl) ⟨1464062, by rfl⟩ : syracuseStep 1952083 = 2928125) B2928125
theorem B4392197 : Blo 1951435 4392197 := bbase (se 4 (by rfl) ⟨411768, by rfl⟩ : syracuseStep 4392197 = 823537) (by norm_num)
theorem B2928131 : Blo 1951435 2928131 := bstep (se 1 (by rfl) ⟨2196098, by rfl⟩ : syracuseStep 2928131 = 4392197) B4392197
theorem B1952087 : Blo 1951435 1952087 := bstep (se 1 (by rfl) ⟨1464065, by rfl⟩ : syracuseStep 1952087 = 2928131) B2928131
theorem B3705925 : Blo 1951435 3705925 := bbase (se 4 (by rfl) ⟨347430, by rfl⟩ : syracuseStep 3705925 = 694861) (by norm_num)
theorem B4941233 : Blo 1951435 4941233 := bstep (se 2 (by rfl) ⟨1852962, by rfl⟩ : syracuseStep 4941233 = 3705925) B3705925
theorem B3294155 : Blo 1951435 3294155 := bstep (se 1 (by rfl) ⟨2470616, by rfl⟩ : syracuseStep 3294155 = 4941233) B4941233
theorem B2196103 : Blo 1951435 2196103 := bstep (se 1 (by rfl) ⟨1647077, by rfl⟩ : syracuseStep 2196103 = 3294155) B3294155
theorem B2928137 : Blo 1951435 2928137 := bstep (se 2 (by rfl) ⟨1098051, by rfl⟩ : syracuseStep 2928137 = 2196103) B2196103
theorem B1952091 : Blo 1951435 1952091 := bstep (se 1 (by rfl) ⟨1464068, by rfl⟩ : syracuseStep 1952091 = 2928137) B2928137
theorem B9882485 : Blo 1951435 9882485 := bbase (se 5 (by rfl) ⟨463241, by rfl⟩ : syracuseStep 9882485 = 926483) (by norm_num)
theorem B6588323 : Blo 1951435 6588323 := bstep (se 1 (by rfl) ⟨4941242, by rfl⟩ : syracuseStep 6588323 = 9882485) B9882485
theorem B4392215 : Blo 1951435 4392215 := bstep (se 1 (by rfl) ⟨3294161, by rfl⟩ : syracuseStep 4392215 = 6588323) B6588323
theorem B2928143 : Blo 1951435 2928143 := bstep (se 1 (by rfl) ⟨2196107, by rfl⟩ : syracuseStep 2928143 = 4392215) B4392215
theorem B1952095 : Blo 1951435 1952095 := bstep (se 1 (by rfl) ⟨1464071, by rfl⟩ : syracuseStep 1952095 = 2928143) B2928143
theorem B2928149 : Blo 1951435 2928149 := bbase (se 6 (by rfl) ⟨68628, by rfl⟩ : syracuseStep 2928149 = 137257) (by norm_num)
theorem B1952099 : Blo 1951435 1952099 := bstep (se 1 (by rfl) ⟨1464074, by rfl⟩ : syracuseStep 1952099 = 2928149) B2928149
theorem B5936213 : Blo 1951435 5936213 := bbase (se 8 (by rfl) ⟨34782, by rfl⟩ : syracuseStep 5936213 = 69565) (by norm_num)
theorem B15829901 : Blo 1951435 15829901 := bstep (se 3 (by rfl) ⟨2968106, by rfl⟩ : syracuseStep 15829901 = 5936213) B5936213
theorem B10553267 : Blo 1951435 10553267 := bstep (se 1 (by rfl) ⟨7914950, by rfl⟩ : syracuseStep 10553267 = 15829901) B15829901
theorem B7035511 : Blo 1951435 7035511 := bstep (se 1 (by rfl) ⟨5276633, by rfl⟩ : syracuseStep 7035511 = 10553267) B10553267
theorem B9380681 : Blo 1951435 9380681 := bstep (se 2 (by rfl) ⟨3517755, by rfl⟩ : syracuseStep 9380681 = 7035511) B7035511
theorem B6253787 : Blo 1951435 6253787 := bstep (se 1 (by rfl) ⟨4690340, by rfl⟩ : syracuseStep 6253787 = 9380681) B9380681
theorem B16676765 : Blo 1951435 16676765 := bstep (se 3 (by rfl) ⟨3126893, by rfl⟩ : syracuseStep 16676765 = 6253787) B6253787
theorem B11117843 : Blo 1951435 11117843 := bstep (se 1 (by rfl) ⟨8338382, by rfl⟩ : syracuseStep 11117843 = 16676765) B16676765
theorem B7411895 : Blo 1951435 7411895 := bstep (se 1 (by rfl) ⟨5558921, by rfl⟩ : syracuseStep 7411895 = 11117843) B11117843
theorem B4941263 : Blo 1951435 4941263 := bstep (se 1 (by rfl) ⟨3705947, by rfl⟩ : syracuseStep 4941263 = 7411895) B7411895
theorem B3294175 : Blo 1951435 3294175 := bstep (se 1 (by rfl) ⟨2470631, by rfl⟩ : syracuseStep 3294175 = 4941263) B4941263
theorem B4392233 : Blo 1951435 4392233 := bstep (se 2 (by rfl) ⟨1647087, by rfl⟩ : syracuseStep 4392233 = 3294175) B3294175
theorem B2928155 : Blo 1951435 2928155 := bstep (se 1 (by rfl) ⟨2196116, by rfl⟩ : syracuseStep 2928155 = 4392233) B4392233
theorem B1952103 : Blo 1951435 1952103 := bstep (se 1 (by rfl) ⟨1464077, by rfl⟩ : syracuseStep 1952103 = 2928155) B2928155
theorem B2196121 : Blo 1951435 2196121 := bbase (se 2 (by rfl) ⟨823545, by rfl⟩ : syracuseStep 2196121 = 1647091) (by norm_num)
theorem B2928161 : Blo 1951435 2928161 := bstep (se 2 (by rfl) ⟨1098060, by rfl⟩ : syracuseStep 2928161 = 2196121) B2196121
theorem B1952107 : Blo 1951435 1952107 := bstep (se 1 (by rfl) ⟨1464080, by rfl⟩ : syracuseStep 1952107 = 2928161) B2928161
theorem B7411925 : Blo 1951435 7411925 := bbase (se 7 (by rfl) ⟨86858, by rfl⟩ : syracuseStep 7411925 = 173717) (by norm_num)
theorem B4941283 : Blo 1951435 4941283 := bstep (se 1 (by rfl) ⟨3705962, by rfl⟩ : syracuseStep 4941283 = 7411925) B7411925
theorem B6588377 : Blo 1951435 6588377 := bstep (se 2 (by rfl) ⟨2470641, by rfl⟩ : syracuseStep 6588377 = 4941283) B4941283
theorem B4392251 : Blo 1951435 4392251 := bstep (se 1 (by rfl) ⟨3294188, by rfl⟩ : syracuseStep 4392251 = 6588377) B6588377
theorem B2928167 : Blo 1951435 2928167 := bstep (se 1 (by rfl) ⟨2196125, by rfl⟩ : syracuseStep 2928167 = 4392251) B4392251
theorem B1952111 : Blo 1951435 1952111 := bstep (se 1 (by rfl) ⟨1464083, by rfl⟩ : syracuseStep 1952111 = 2928167) B2928167
theorem B2928173 : Blo 1951435 2928173 := bbase (se 3 (by rfl) ⟨549032, by rfl⟩ : syracuseStep 2928173 = 1098065) (by norm_num)
theorem B1952115 : Blo 1951435 1952115 := bstep (se 1 (by rfl) ⟨1464086, by rfl⟩ : syracuseStep 1952115 = 2928173) B2928173
theorem B4392269 : Blo 1951435 4392269 := bbase (se 3 (by rfl) ⟨823550, by rfl⟩ : syracuseStep 4392269 = 1647101) (by norm_num)
theorem B2928179 : Blo 1951435 2928179 := bstep (se 1 (by rfl) ⟨2196134, by rfl⟩ : syracuseStep 2928179 = 4392269) B4392269
theorem B1952119 : Blo 1951435 1952119 := bstep (se 1 (by rfl) ⟨1464089, by rfl⟩ : syracuseStep 1952119 = 2928179) B2928179
theorem B2470657 : Blo 1951435 2470657 := bbase (se 2 (by rfl) ⟨926496, by rfl⟩ : syracuseStep 2470657 = 1852993) (by norm_num)
theorem B3294209 : Blo 1951435 3294209 := bstep (se 2 (by rfl) ⟨1235328, by rfl⟩ : syracuseStep 3294209 = 2470657) B2470657
theorem B2196139 : Blo 1951435 2196139 := bstep (se 1 (by rfl) ⟨1647104, by rfl⟩ : syracuseStep 2196139 = 3294209) B3294209
theorem B2928185 : Blo 1951435 2928185 := bstep (se 2 (by rfl) ⟨1098069, by rfl⟩ : syracuseStep 2928185 = 2196139) B2196139
theorem B1952123 : Blo 1951435 1952123 := bstep (se 1 (by rfl) ⟨1464092, by rfl⟩ : syracuseStep 1952123 = 2928185) B2928185
theorem B2084621 : Blo 1951435 2084621 := bbase (se 3 (by rfl) ⟨390866, by rfl⟩ : syracuseStep 2084621 = 781733) (by norm_num)
theorem B22235957 : Blo 1951435 22235957 := bstep (se 5 (by rfl) ⟨1042310, by rfl⟩ : syracuseStep 22235957 = 2084621) B2084621
theorem B14823971 : Blo 1951435 14823971 := bstep (se 1 (by rfl) ⟨11117978, by rfl⟩ : syracuseStep 14823971 = 22235957) B22235957
theorem B9882647 : Blo 1951435 9882647 := bstep (se 1 (by rfl) ⟨7411985, by rfl⟩ : syracuseStep 9882647 = 14823971) B14823971
theorem B6588431 : Blo 1951435 6588431 := bstep (se 1 (by rfl) ⟨4941323, by rfl⟩ : syracuseStep 6588431 = 9882647) B9882647
theorem B4392287 : Blo 1951435 4392287 := bstep (se 1 (by rfl) ⟨3294215, by rfl⟩ : syracuseStep 4392287 = 6588431) B6588431
theorem B2928191 : Blo 1951435 2928191 := bstep (se 1 (by rfl) ⟨2196143, by rfl⟩ : syracuseStep 2928191 = 4392287) B4392287
theorem B1952127 : Blo 1951435 1952127 := bstep (se 1 (by rfl) ⟨1464095, by rfl⟩ : syracuseStep 1952127 = 2928191) B2928191
theorem B2928197 : Blo 1951435 2928197 := bbase (se 4 (by rfl) ⟨274518, by rfl⟩ : syracuseStep 2928197 = 549037) (by norm_num)
theorem B1952131 : Blo 1951435 1952131 := bstep (se 1 (by rfl) ⟨1464098, by rfl⟩ : syracuseStep 1952131 = 2928197) B2928197
theorem B3294229 : Blo 1951435 3294229 := bbase (se 6 (by rfl) ⟨77208, by rfl⟩ : syracuseStep 3294229 = 154417) (by norm_num)
theorem B4392305 : Blo 1951435 4392305 := bstep (se 2 (by rfl) ⟨1647114, by rfl⟩ : syracuseStep 4392305 = 3294229) B3294229
theorem B2928203 : Blo 1951435 2928203 := bstep (se 1 (by rfl) ⟨2196152, by rfl⟩ : syracuseStep 2928203 = 4392305) B4392305
theorem B1952135 : Blo 1951435 1952135 := bstep (se 1 (by rfl) ⟨1464101, by rfl⟩ : syracuseStep 1952135 = 2928203) B2928203
theorem B2196157 : Blo 1951435 2196157 := bbase (se 3 (by rfl) ⟨411779, by rfl⟩ : syracuseStep 2196157 = 823559) (by norm_num)
theorem B2928209 : Blo 1951435 2928209 := bstep (se 2 (by rfl) ⟨1098078, by rfl⟩ : syracuseStep 2928209 = 2196157) B2196157
theorem B1952139 : Blo 1951435 1952139 := bstep (se 1 (by rfl) ⟨1464104, by rfl⟩ : syracuseStep 1952139 = 2928209) B2928209
theorem B6588485 : Blo 1951435 6588485 := bbase (se 4 (by rfl) ⟨617670, by rfl⟩ : syracuseStep 6588485 = 1235341) (by norm_num)
theorem B4392323 : Blo 1951435 4392323 := bstep (se 1 (by rfl) ⟨3294242, by rfl⟩ : syracuseStep 4392323 = 6588485) B6588485
theorem B2928215 : Blo 1951435 2928215 := bstep (se 1 (by rfl) ⟨2196161, by rfl⟩ : syracuseStep 2928215 = 4392323) B4392323
theorem B1952143 : Blo 1951435 1952143 := bstep (se 1 (by rfl) ⟨1464107, by rfl⟩ : syracuseStep 1952143 = 2928215) B2928215
theorem B2928221 : Blo 1951435 2928221 := bbase (se 3 (by rfl) ⟨549041, by rfl⟩ : syracuseStep 2928221 = 1098083) (by norm_num)
theorem B1952147 : Blo 1951435 1952147 := bstep (se 1 (by rfl) ⟨1464110, by rfl⟩ : syracuseStep 1952147 = 2928221) B2928221
theorem B4392341 : Blo 1951435 4392341 := bbase (se 6 (by rfl) ⟨102945, by rfl⟩ : syracuseStep 4392341 = 205891) (by norm_num)
theorem B2928227 : Blo 1951435 2928227 := bstep (se 1 (by rfl) ⟨2196170, by rfl⟩ : syracuseStep 2928227 = 4392341) B4392341
theorem B1952151 : Blo 1951435 1952151 := bstep (se 1 (by rfl) ⟨1464113, by rfl⟩ : syracuseStep 1952151 = 2928227) B2928227
theorem B9380933 : Blo 1951435 9380933 := bbase (se 4 (by rfl) ⟨879462, by rfl⟩ : syracuseStep 9380933 = 1758925) (by norm_num)
theorem B6253955 : Blo 1951435 6253955 := bstep (se 1 (by rfl) ⟨4690466, by rfl⟩ : syracuseStep 6253955 = 9380933) B9380933
theorem B4169303 : Blo 1951435 4169303 := bstep (se 1 (by rfl) ⟨3126977, by rfl⟩ : syracuseStep 4169303 = 6253955) B6253955
theorem B2779535 : Blo 1951435 2779535 := bstep (se 1 (by rfl) ⟨2084651, by rfl⟩ : syracuseStep 2779535 = 4169303) B4169303
theorem B7412093 : Blo 1951435 7412093 := bstep (se 3 (by rfl) ⟨1389767, by rfl⟩ : syracuseStep 7412093 = 2779535) B2779535
theorem B4941395 : Blo 1951435 4941395 := bstep (se 1 (by rfl) ⟨3706046, by rfl⟩ : syracuseStep 4941395 = 7412093) B7412093
theorem B3294263 : Blo 1951435 3294263 := bstep (se 1 (by rfl) ⟨2470697, by rfl⟩ : syracuseStep 3294263 = 4941395) B4941395
theorem B2196175 : Blo 1951435 2196175 := bstep (se 1 (by rfl) ⟨1647131, by rfl⟩ : syracuseStep 2196175 = 3294263) B3294263
theorem B2928233 : Blo 1951435 2928233 := bstep (se 2 (by rfl) ⟨1098087, by rfl⟩ : syracuseStep 2928233 = 2196175) B2196175
theorem B1952155 : Blo 1951435 1952155 := bstep (se 1 (by rfl) ⟨1464116, by rfl⟩ : syracuseStep 1952155 = 2928233) B2928233
theorem B3957589 : Blo 1951435 3957589 := bbase (se 9 (by rfl) ⟨11594, by rfl⟩ : syracuseStep 3957589 = 23189) (by norm_num)
theorem B5276785 : Blo 1951435 5276785 := bstep (se 2 (by rfl) ⟨1978794, by rfl⟩ : syracuseStep 5276785 = 3957589) B3957589
theorem B7035713 : Blo 1951435 7035713 := bstep (se 2 (by rfl) ⟨2638392, by rfl⟩ : syracuseStep 7035713 = 5276785) B5276785
theorem B4690475 : Blo 1951435 4690475 := bstep (se 1 (by rfl) ⟨3517856, by rfl⟩ : syracuseStep 4690475 = 7035713) B7035713
theorem B3126983 : Blo 1951435 3126983 := bstep (se 1 (by rfl) ⟨2345237, by rfl⟩ : syracuseStep 3126983 = 4690475) B4690475
theorem B8338621 : Blo 1951435 8338621 := bstep (se 3 (by rfl) ⟨1563491, by rfl⟩ : syracuseStep 8338621 = 3126983) B3126983
theorem B11118161 : Blo 1951435 11118161 := bstep (se 2 (by rfl) ⟨4169310, by rfl⟩ : syracuseStep 11118161 = 8338621) B8338621
theorem B7412107 : Blo 1951435 7412107 := bstep (se 1 (by rfl) ⟨5559080, by rfl⟩ : syracuseStep 7412107 = 11118161) B11118161
theorem B9882809 : Blo 1951435 9882809 := bstep (se 2 (by rfl) ⟨3706053, by rfl⟩ : syracuseStep 9882809 = 7412107) B7412107
theorem B6588539 : Blo 1951435 6588539 := bstep (se 1 (by rfl) ⟨4941404, by rfl⟩ : syracuseStep 6588539 = 9882809) B9882809
theorem B4392359 : Blo 1951435 4392359 := bstep (se 1 (by rfl) ⟨3294269, by rfl⟩ : syracuseStep 4392359 = 6588539) B6588539
theorem B2928239 : Blo 1951435 2928239 := bstep (se 1 (by rfl) ⟨2196179, by rfl⟩ : syracuseStep 2928239 = 4392359) B4392359
theorem B1952159 : Blo 1951435 1952159 := bstep (se 1 (by rfl) ⟨1464119, by rfl⟩ : syracuseStep 1952159 = 2928239) B2928239
theorem B2928245 : Blo 1951435 2928245 := bbase (se 5 (by rfl) ⟨137261, by rfl⟩ : syracuseStep 2928245 = 274523) (by norm_num)
theorem B1952163 : Blo 1951435 1952163 := bstep (se 1 (by rfl) ⟨1464122, by rfl⟩ : syracuseStep 1952163 = 2928245) B2928245
theorem B3706069 : Blo 1951435 3706069 := bbase (se 7 (by rfl) ⟨43430, by rfl⟩ : syracuseStep 3706069 = 86861) (by norm_num)
theorem B4941425 : Blo 1951435 4941425 := bstep (se 2 (by rfl) ⟨1853034, by rfl⟩ : syracuseStep 4941425 = 3706069) B3706069
theorem B3294283 : Blo 1951435 3294283 := bstep (se 1 (by rfl) ⟨2470712, by rfl⟩ : syracuseStep 3294283 = 4941425) B4941425
theorem B4392377 : Blo 1951435 4392377 := bstep (se 2 (by rfl) ⟨1647141, by rfl⟩ : syracuseStep 4392377 = 3294283) B3294283
theorem B2928251 : Blo 1951435 2928251 := bstep (se 1 (by rfl) ⟨2196188, by rfl⟩ : syracuseStep 2928251 = 4392377) B4392377
theorem B1952167 : Blo 1951435 1952167 := bstep (se 1 (by rfl) ⟨1464125, by rfl⟩ : syracuseStep 1952167 = 2928251) B2928251
theorem B2196193 : Blo 1951435 2196193 := bbase (se 2 (by rfl) ⟨823572, by rfl⟩ : syracuseStep 2196193 = 1647145) (by norm_num)
theorem B2928257 : Blo 1951435 2928257 := bstep (se 2 (by rfl) ⟨1098096, by rfl⟩ : syracuseStep 2928257 = 2196193) B2196193
theorem B1952171 : Blo 1951435 1952171 := bstep (se 1 (by rfl) ⟨1464128, by rfl⟩ : syracuseStep 1952171 = 2928257) B2928257
theorem B4941445 : Blo 1951435 4941445 := bbase (se 4 (by rfl) ⟨463260, by rfl⟩ : syracuseStep 4941445 = 926521) (by norm_num)
theorem B6588593 : Blo 1951435 6588593 := bstep (se 2 (by rfl) ⟨2470722, by rfl⟩ : syracuseStep 6588593 = 4941445) B4941445
theorem B4392395 : Blo 1951435 4392395 := bstep (se 1 (by rfl) ⟨3294296, by rfl⟩ : syracuseStep 4392395 = 6588593) B6588593
theorem B2928263 : Blo 1951435 2928263 := bstep (se 1 (by rfl) ⟨2196197, by rfl⟩ : syracuseStep 2928263 = 4392395) B4392395
theorem B1952175 : Blo 1951435 1952175 := bstep (se 1 (by rfl) ⟨1464131, by rfl⟩ : syracuseStep 1952175 = 2928263) B2928263
theorem B2928269 : Blo 1951435 2928269 := bbase (se 3 (by rfl) ⟨549050, by rfl⟩ : syracuseStep 2928269 = 1098101) (by norm_num)
theorem B1952179 : Blo 1951435 1952179 := bstep (se 1 (by rfl) ⟨1464134, by rfl⟩ : syracuseStep 1952179 = 2928269) B2928269
theorem B4392413 : Blo 1951435 4392413 := bbase (se 3 (by rfl) ⟨823577, by rfl⟩ : syracuseStep 4392413 = 1647155) (by norm_num)
theorem B2928275 : Blo 1951435 2928275 := bstep (se 1 (by rfl) ⟨2196206, by rfl⟩ : syracuseStep 2928275 = 4392413) B4392413
theorem B1952183 : Blo 1951435 1952183 := bstep (se 1 (by rfl) ⟨1464137, by rfl⟩ : syracuseStep 1952183 = 2928275) B2928275
theorem B3294317 : Blo 1951435 3294317 := bbase (se 3 (by rfl) ⟨617684, by rfl⟩ : syracuseStep 3294317 = 1235369) (by norm_num)
theorem B2196211 : Blo 1951435 2196211 := bstep (se 1 (by rfl) ⟨1647158, by rfl⟩ : syracuseStep 2196211 = 3294317) B3294317
theorem B2928281 : Blo 1951435 2928281 := bstep (se 2 (by rfl) ⟨1098105, by rfl⟩ : syracuseStep 2928281 = 2196211) B2196211
theorem B1952187 : Blo 1951435 1952187 := bstep (se 1 (by rfl) ⟨1464140, by rfl⟩ : syracuseStep 1952187 = 2928281) B2928281
theorem B3957653 : Blo 1951435 3957653 := bbase (se 6 (by rfl) ⟨92757, by rfl⟩ : syracuseStep 3957653 = 185515) (by norm_num)
theorem B10553741 : Blo 1951435 10553741 := bstep (se 3 (by rfl) ⟨1978826, by rfl⟩ : syracuseStep 10553741 = 3957653) B3957653
theorem B7035827 : Blo 1951435 7035827 := bstep (se 1 (by rfl) ⟨5276870, by rfl⟩ : syracuseStep 7035827 = 10553741) B10553741
theorem B18762205 : Blo 1951435 18762205 := bstep (se 3 (by rfl) ⟨3517913, by rfl⟩ : syracuseStep 18762205 = 7035827) B7035827
theorem B25016273 : Blo 1951435 25016273 := bstep (se 2 (by rfl) ⟨9381102, by rfl⟩ : syracuseStep 25016273 = 18762205) B18762205
theorem B16677515 : Blo 1951435 16677515 := bstep (se 1 (by rfl) ⟨12508136, by rfl⟩ : syracuseStep 16677515 = 25016273) B25016273
theorem B11118343 : Blo 1951435 11118343 := bstep (se 1 (by rfl) ⟨8338757, by rfl⟩ : syracuseStep 11118343 = 16677515) B16677515
theorem B14824457 : Blo 1951435 14824457 := bstep (se 2 (by rfl) ⟨5559171, by rfl⟩ : syracuseStep 14824457 = 11118343) B11118343
theorem B9882971 : Blo 1951435 9882971 := bstep (se 1 (by rfl) ⟨7412228, by rfl⟩ : syracuseStep 9882971 = 14824457) B14824457
theorem B6588647 : Blo 1951435 6588647 := bstep (se 1 (by rfl) ⟨4941485, by rfl⟩ : syracuseStep 6588647 = 9882971) B9882971
theorem B4392431 : Blo 1951435 4392431 := bstep (se 1 (by rfl) ⟨3294323, by rfl⟩ : syracuseStep 4392431 = 6588647) B6588647
theorem B2928287 : Blo 1951435 2928287 := bstep (se 1 (by rfl) ⟨2196215, by rfl⟩ : syracuseStep 2928287 = 4392431) B4392431
theorem B1952191 : Blo 1951435 1952191 := bstep (se 1 (by rfl) ⟨1464143, by rfl⟩ : syracuseStep 1952191 = 2928287) B2928287
theorem B2928293 : Blo 1951435 2928293 := bbase (se 4 (by rfl) ⟨274527, by rfl⟩ : syracuseStep 2928293 = 549055) (by norm_num)
theorem B1952195 : Blo 1951435 1952195 := bstep (se 1 (by rfl) ⟨1464146, by rfl⟩ : syracuseStep 1952195 = 2928293) B2928293
theorem B2470753 : Blo 1951435 2470753 := bbase (se 2 (by rfl) ⟨926532, by rfl⟩ : syracuseStep 2470753 = 1853065) (by norm_num)
theorem B3294337 : Blo 1951435 3294337 := bstep (se 2 (by rfl) ⟨1235376, by rfl⟩ : syracuseStep 3294337 = 2470753) B2470753
theorem B4392449 : Blo 1951435 4392449 := bstep (se 2 (by rfl) ⟨1647168, by rfl⟩ : syracuseStep 4392449 = 3294337) B3294337
theorem B2928299 : Blo 1951435 2928299 := bstep (se 1 (by rfl) ⟨2196224, by rfl⟩ : syracuseStep 2928299 = 4392449) B4392449
theorem B1952199 : Blo 1951435 1952199 := bstep (se 1 (by rfl) ⟨1464149, by rfl⟩ : syracuseStep 1952199 = 2928299) B2928299
theorem B2196229 : Blo 1951435 2196229 := bbase (se 4 (by rfl) ⟨205896, by rfl⟩ : syracuseStep 2196229 = 411793) (by norm_num)
theorem B2928305 : Blo 1951435 2928305 := bstep (se 2 (by rfl) ⟨1098114, by rfl⟩ : syracuseStep 2928305 = 2196229) B2196229
theorem B1952203 : Blo 1951435 1952203 := bstep (se 1 (by rfl) ⟨1464152, by rfl⟩ : syracuseStep 1952203 = 2928305) B2928305
theorem B3127061 : Blo 1951435 3127061 := bbase (se 6 (by rfl) ⟨73290, by rfl⟩ : syracuseStep 3127061 = 146581) (by norm_num)
theorem B2084707 : Blo 1951435 2084707 := bstep (se 1 (by rfl) ⟨1563530, by rfl⟩ : syracuseStep 2084707 = 3127061) B3127061
theorem B2779609 : Blo 1951435 2779609 := bstep (se 2 (by rfl) ⟨1042353, by rfl⟩ : syracuseStep 2779609 = 2084707) B2084707
theorem B3706145 : Blo 1951435 3706145 := bstep (se 2 (by rfl) ⟨1389804, by rfl⟩ : syracuseStep 3706145 = 2779609) B2779609
theorem B2470763 : Blo 1951435 2470763 := bstep (se 1 (by rfl) ⟨1853072, by rfl⟩ : syracuseStep 2470763 = 3706145) B3706145
theorem B6588701 : Blo 1951435 6588701 := bstep (se 3 (by rfl) ⟨1235381, by rfl⟩ : syracuseStep 6588701 = 2470763) B2470763
theorem B4392467 : Blo 1951435 4392467 := bstep (se 1 (by rfl) ⟨3294350, by rfl⟩ : syracuseStep 4392467 = 6588701) B6588701
theorem B2928311 : Blo 1951435 2928311 := bstep (se 1 (by rfl) ⟨2196233, by rfl⟩ : syracuseStep 2928311 = 4392467) B4392467
theorem B1952207 : Blo 1951435 1952207 := bstep (se 1 (by rfl) ⟨1464155, by rfl⟩ : syracuseStep 1952207 = 2928311) B2928311
theorem B2928317 : Blo 1951435 2928317 := bbase (se 3 (by rfl) ⟨549059, by rfl⟩ : syracuseStep 2928317 = 1098119) (by norm_num)
theorem B1952211 : Blo 1951435 1952211 := bstep (se 1 (by rfl) ⟨1464158, by rfl⟩ : syracuseStep 1952211 = 2928317) B2928317
theorem B4392485 : Blo 1951435 4392485 := bbase (se 4 (by rfl) ⟨411795, by rfl⟩ : syracuseStep 4392485 = 823591) (by norm_num)
theorem B2928323 : Blo 1951435 2928323 := bstep (se 1 (by rfl) ⟨2196242, by rfl⟩ : syracuseStep 2928323 = 4392485) B4392485
theorem B1952215 : Blo 1951435 1952215 := bstep (se 1 (by rfl) ⟨1464161, by rfl⟩ : syracuseStep 1952215 = 2928323) B2928323
theorem B4941557 : Blo 1951435 4941557 := bbase (se 5 (by rfl) ⟨231635, by rfl⟩ : syracuseStep 4941557 = 463271) (by norm_num)
theorem B3294371 : Blo 1951435 3294371 := bstep (se 1 (by rfl) ⟨2470778, by rfl⟩ : syracuseStep 3294371 = 4941557) B4941557
theorem B2196247 : Blo 1951435 2196247 := bstep (se 1 (by rfl) ⟨1647185, by rfl⟩ : syracuseStep 2196247 = 3294371) B3294371
theorem B2928329 : Blo 1951435 2928329 := bstep (se 2 (by rfl) ⟨1098123, by rfl⟩ : syracuseStep 2928329 = 2196247) B2196247
theorem B1952219 : Blo 1951435 1952219 := bstep (se 1 (by rfl) ⟨1464164, by rfl⟩ : syracuseStep 1952219 = 2928329) B2928329
theorem B3339325 : Blo 1951435 3339325 := bbase (se 3 (by rfl) ⟨626123, by rfl⟩ : syracuseStep 3339325 = 1252247) (by norm_num)
theorem B17809733 : Blo 1951435 17809733 := bstep (se 4 (by rfl) ⟨1669662, by rfl⟩ : syracuseStep 17809733 = 3339325) B3339325
theorem B11873155 : Blo 1951435 11873155 := bstep (se 1 (by rfl) ⟨8904866, by rfl⟩ : syracuseStep 11873155 = 17809733) B17809733
theorem B15830873 : Blo 1951435 15830873 := bstep (se 2 (by rfl) ⟨5936577, by rfl⟩ : syracuseStep 15830873 = 11873155) B11873155
theorem B10553915 : Blo 1951435 10553915 := bstep (se 1 (by rfl) ⟨7915436, by rfl⟩ : syracuseStep 10553915 = 15830873) B15830873
theorem B28143773 : Blo 1951435 28143773 := bstep (se 3 (by rfl) ⟨5276957, by rfl⟩ : syracuseStep 28143773 = 10553915) B10553915
theorem B18762515 : Blo 1951435 18762515 := bstep (se 1 (by rfl) ⟨14071886, by rfl⟩ : syracuseStep 18762515 = 28143773) B28143773
theorem B12508343 : Blo 1951435 12508343 := bstep (se 1 (by rfl) ⟨9381257, by rfl⟩ : syracuseStep 12508343 = 18762515) B18762515
theorem B8338895 : Blo 1951435 8338895 := bstep (se 1 (by rfl) ⟨6254171, by rfl⟩ : syracuseStep 8338895 = 12508343) B12508343
theorem B5559263 : Blo 1951435 5559263 := bstep (se 1 (by rfl) ⟨4169447, by rfl⟩ : syracuseStep 5559263 = 8338895) B8338895
theorem B3706175 : Blo 1951435 3706175 := bstep (se 1 (by rfl) ⟨2779631, by rfl⟩ : syracuseStep 3706175 = 5559263) B5559263
theorem B9883133 : Blo 1951435 9883133 := bstep (se 3 (by rfl) ⟨1853087, by rfl⟩ : syracuseStep 9883133 = 3706175) B3706175
theorem B6588755 : Blo 1951435 6588755 := bstep (se 1 (by rfl) ⟨4941566, by rfl⟩ : syracuseStep 6588755 = 9883133) B9883133
theorem B4392503 : Blo 1951435 4392503 := bstep (se 1 (by rfl) ⟨3294377, by rfl⟩ : syracuseStep 4392503 = 6588755) B6588755
theorem B2928335 : Blo 1951435 2928335 := bstep (se 1 (by rfl) ⟨2196251, by rfl⟩ : syracuseStep 2928335 = 4392503) B4392503
theorem B1952223 : Blo 1951435 1952223 := bstep (se 1 (by rfl) ⟨1464167, by rfl⟩ : syracuseStep 1952223 = 2928335) B2928335
theorem B2928341 : Blo 1951435 2928341 := bbase (se 7 (by rfl) ⟨34316, by rfl⟩ : syracuseStep 2928341 = 68633) (by norm_num)
theorem B1952227 : Blo 1951435 1952227 := bstep (se 1 (by rfl) ⟨1464170, by rfl⟩ : syracuseStep 1952227 = 2928341) B2928341
theorem B5276981 : Blo 1951435 5276981 := bbase (se 5 (by rfl) ⟨247358, by rfl⟩ : syracuseStep 5276981 = 494717) (by norm_num)
theorem B3517987 : Blo 1951435 3517987 := bstep (se 1 (by rfl) ⟨2638490, by rfl⟩ : syracuseStep 3517987 = 5276981) B5276981
theorem B4690649 : Blo 1951435 4690649 := bstep (se 2 (by rfl) ⟨1758993, by rfl⟩ : syracuseStep 4690649 = 3517987) B3517987
theorem B3127099 : Blo 1951435 3127099 := bstep (se 1 (by rfl) ⟨2345324, by rfl⟩ : syracuseStep 3127099 = 4690649) B4690649
theorem B4169465 : Blo 1951435 4169465 := bstep (se 2 (by rfl) ⟨1563549, by rfl⟩ : syracuseStep 4169465 = 3127099) B3127099
theorem B2779643 : Blo 1951435 2779643 := bstep (se 1 (by rfl) ⟨2084732, by rfl⟩ : syracuseStep 2779643 = 4169465) B4169465
theorem B7412381 : Blo 1951435 7412381 := bstep (se 3 (by rfl) ⟨1389821, by rfl⟩ : syracuseStep 7412381 = 2779643) B2779643
theorem B4941587 : Blo 1951435 4941587 := bstep (se 1 (by rfl) ⟨3706190, by rfl⟩ : syracuseStep 4941587 = 7412381) B7412381
theorem B3294391 : Blo 1951435 3294391 := bstep (se 1 (by rfl) ⟨2470793, by rfl⟩ : syracuseStep 3294391 = 4941587) B4941587
theorem B4392521 : Blo 1951435 4392521 := bstep (se 2 (by rfl) ⟨1647195, by rfl⟩ : syracuseStep 4392521 = 3294391) B3294391
theorem B2928347 : Blo 1951435 2928347 := bstep (se 1 (by rfl) ⟨2196260, by rfl⟩ : syracuseStep 2928347 = 4392521) B4392521
theorem B1952231 : Blo 1951435 1952231 := bstep (se 1 (by rfl) ⟨1464173, by rfl⟩ : syracuseStep 1952231 = 2928347) B2928347
theorem B2196265 : Blo 1951435 2196265 := bbase (se 2 (by rfl) ⟨823599, by rfl⟩ : syracuseStep 2196265 = 1647199) (by norm_num)
theorem B2928353 : Blo 1951435 2928353 := bstep (se 2 (by rfl) ⟨1098132, by rfl⟩ : syracuseStep 2928353 = 2196265) B2196265
theorem B1952235 : Blo 1951435 1952235 := bstep (se 1 (by rfl) ⟨1464176, by rfl⟩ : syracuseStep 1952235 = 2928353) B2928353
theorem B3756773 : Blo 1951435 3756773 := bbase (se 4 (by rfl) ⟨352197, by rfl⟩ : syracuseStep 3756773 = 704395) (by norm_num)
theorem B2504515 : Blo 1951435 2504515 := bstep (se 1 (by rfl) ⟨1878386, by rfl⟩ : syracuseStep 2504515 = 3756773) B3756773
theorem B3339353 : Blo 1951435 3339353 := bstep (se 2 (by rfl) ⟨1252257, by rfl⟩ : syracuseStep 3339353 = 2504515) B2504515
theorem B8904941 : Blo 1951435 8904941 := bstep (se 3 (by rfl) ⟨1669676, by rfl⟩ : syracuseStep 8904941 = 3339353) B3339353
theorem B5936627 : Blo 1951435 5936627 := bstep (se 1 (by rfl) ⟨4452470, by rfl⟩ : syracuseStep 5936627 = 8904941) B8904941
theorem B3957751 : Blo 1951435 3957751 := bstep (se 1 (by rfl) ⟨2968313, by rfl⟩ : syracuseStep 3957751 = 5936627) B5936627
theorem B5277001 : Blo 1951435 5277001 := bstep (se 2 (by rfl) ⟨1978875, by rfl⟩ : syracuseStep 5277001 = 3957751) B3957751
theorem B7036001 : Blo 1951435 7036001 := bstep (se 2 (by rfl) ⟨2638500, by rfl⟩ : syracuseStep 7036001 = 5277001) B5277001
theorem B4690667 : Blo 1951435 4690667 := bstep (se 1 (by rfl) ⟨3518000, by rfl⟩ : syracuseStep 4690667 = 7036001) B7036001
theorem B12508445 : Blo 1951435 12508445 := bstep (se 3 (by rfl) ⟨2345333, by rfl⟩ : syracuseStep 12508445 = 4690667) B4690667
theorem B8338963 : Blo 1951435 8338963 := bstep (se 1 (by rfl) ⟨6254222, by rfl⟩ : syracuseStep 8338963 = 12508445) B12508445
theorem B11118617 : Blo 1951435 11118617 := bstep (se 2 (by rfl) ⟨4169481, by rfl⟩ : syracuseStep 11118617 = 8338963) B8338963
theorem B7412411 : Blo 1951435 7412411 := bstep (se 1 (by rfl) ⟨5559308, by rfl⟩ : syracuseStep 7412411 = 11118617) B11118617
theorem B4941607 : Blo 1951435 4941607 := bstep (se 1 (by rfl) ⟨3706205, by rfl⟩ : syracuseStep 4941607 = 7412411) B7412411
theorem B6588809 : Blo 1951435 6588809 := bstep (se 2 (by rfl) ⟨2470803, by rfl⟩ : syracuseStep 6588809 = 4941607) B4941607
theorem B4392539 : Blo 1951435 4392539 := bstep (se 1 (by rfl) ⟨3294404, by rfl⟩ : syracuseStep 4392539 = 6588809) B6588809
theorem B2928359 : Blo 1951435 2928359 := bstep (se 1 (by rfl) ⟨2196269, by rfl⟩ : syracuseStep 2928359 = 4392539) B4392539
theorem B1952239 : Blo 1951435 1952239 := bstep (se 1 (by rfl) ⟨1464179, by rfl⟩ : syracuseStep 1952239 = 2928359) B2928359
theorem B2928365 : Blo 1951435 2928365 := bbase (se 3 (by rfl) ⟨549068, by rfl⟩ : syracuseStep 2928365 = 1098137) (by norm_num)
theorem B1952243 : Blo 1951435 1952243 := bstep (se 1 (by rfl) ⟨1464182, by rfl⟩ : syracuseStep 1952243 = 2928365) B2928365
theorem B4392557 : Blo 1951435 4392557 := bbase (se 3 (by rfl) ⟨823604, by rfl⟩ : syracuseStep 4392557 = 1647209) (by norm_num)
theorem B2928371 : Blo 1951435 2928371 := bstep (se 1 (by rfl) ⟨2196278, by rfl⟩ : syracuseStep 2928371 = 4392557) B4392557
theorem B1952247 : Blo 1951435 1952247 := bstep (se 1 (by rfl) ⟨1464185, by rfl⟩ : syracuseStep 1952247 = 2928371) B2928371
theorem B3706229 : Blo 1951435 3706229 := bbase (se 5 (by rfl) ⟨173729, by rfl⟩ : syracuseStep 3706229 = 347459) (by norm_num)
theorem B2470819 : Blo 1951435 2470819 := bstep (se 1 (by rfl) ⟨1853114, by rfl⟩ : syracuseStep 2470819 = 3706229) B3706229
theorem B3294425 : Blo 1951435 3294425 := bstep (se 2 (by rfl) ⟨1235409, by rfl⟩ : syracuseStep 3294425 = 2470819) B2470819
theorem B2196283 : Blo 1951435 2196283 := bstep (se 1 (by rfl) ⟨1647212, by rfl⟩ : syracuseStep 2196283 = 3294425) B3294425
theorem B2928377 : Blo 1951435 2928377 := bstep (se 2 (by rfl) ⟨1098141, by rfl⟩ : syracuseStep 2928377 = 2196283) B2196283
theorem B1952251 : Blo 1951435 1952251 := bstep (se 1 (by rfl) ⟨1464188, by rfl⟩ : syracuseStep 1952251 = 2928377) B2928377
theorem B5009069 : Blo 1951435 5009069 := bbase (se 3 (by rfl) ⟨939200, by rfl⟩ : syracuseStep 5009069 = 1878401) (by norm_num)
theorem B3339379 : Blo 1951435 3339379 := bstep (se 1 (by rfl) ⟨2504534, by rfl⟩ : syracuseStep 3339379 = 5009069) B5009069
theorem B17810021 : Blo 1951435 17810021 := bstep (se 4 (by rfl) ⟨1669689, by rfl⟩ : syracuseStep 17810021 = 3339379) B3339379
theorem B11873347 : Blo 1951435 11873347 := bstep (se 1 (by rfl) ⟨8905010, by rfl⟩ : syracuseStep 11873347 = 17810021) B17810021
theorem B63324517 : Blo 1951435 63324517 := bstep (se 4 (by rfl) ⟨5936673, by rfl⟩ : syracuseStep 63324517 = 11873347) B11873347
theorem B84432689 : Blo 1951435 84432689 := bstep (se 2 (by rfl) ⟨31662258, by rfl⟩ : syracuseStep 84432689 = 63324517) B63324517
theorem B56288459 : Blo 1951435 56288459 := bstep (se 1 (by rfl) ⟨42216344, by rfl⟩ : syracuseStep 56288459 = 84432689) B84432689
theorem B37525639 : Blo 1951435 37525639 := bstep (se 1 (by rfl) ⟨28144229, by rfl⟩ : syracuseStep 37525639 = 56288459) B56288459
theorem B50034185 : Blo 1951435 50034185 := bstep (se 2 (by rfl) ⟨18762819, by rfl⟩ : syracuseStep 50034185 = 37525639) B37525639
theorem B33356123 : Blo 1951435 33356123 := bstep (se 1 (by rfl) ⟨25017092, by rfl⟩ : syracuseStep 33356123 = 50034185) B50034185
theorem B22237415 : Blo 1951435 22237415 := bstep (se 1 (by rfl) ⟨16678061, by rfl⟩ : syracuseStep 22237415 = 33356123) B33356123
theorem B14824943 : Blo 1951435 14824943 := bstep (se 1 (by rfl) ⟨11118707, by rfl⟩ : syracuseStep 14824943 = 22237415) B22237415
theorem B9883295 : Blo 1951435 9883295 := bstep (se 1 (by rfl) ⟨7412471, by rfl⟩ : syracuseStep 9883295 = 14824943) B14824943
theorem B6588863 : Blo 1951435 6588863 := bstep (se 1 (by rfl) ⟨4941647, by rfl⟩ : syracuseStep 6588863 = 9883295) B9883295
theorem B4392575 : Blo 1951435 4392575 := bstep (se 1 (by rfl) ⟨3294431, by rfl⟩ : syracuseStep 4392575 = 6588863) B6588863
theorem B2928383 : Blo 1951435 2928383 := bstep (se 1 (by rfl) ⟨2196287, by rfl⟩ : syracuseStep 2928383 = 4392575) B4392575
theorem B1952255 : Blo 1951435 1952255 := bstep (se 1 (by rfl) ⟨1464191, by rfl⟩ : syracuseStep 1952255 = 2928383) B2928383
theorem B2928389 : Blo 1951435 2928389 := bbase (se 4 (by rfl) ⟨274536, by rfl⟩ : syracuseStep 2928389 = 549073) (by norm_num)
theorem B1952259 : Blo 1951435 1952259 := bstep (se 1 (by rfl) ⟨1464194, by rfl⟩ : syracuseStep 1952259 = 2928389) B2928389
theorem B3294445 : Blo 1951435 3294445 := bbase (se 3 (by rfl) ⟨617708, by rfl⟩ : syracuseStep 3294445 = 1235417) (by norm_num)
theorem B4392593 : Blo 1951435 4392593 := bstep (se 2 (by rfl) ⟨1647222, by rfl⟩ : syracuseStep 4392593 = 3294445) B3294445
theorem B2928395 : Blo 1951435 2928395 := bstep (se 1 (by rfl) ⟨2196296, by rfl⟩ : syracuseStep 2928395 = 4392593) B4392593
theorem B1952263 : Blo 1951435 1952263 := bstep (se 1 (by rfl) ⟨1464197, by rfl⟩ : syracuseStep 1952263 = 2928395) B2928395
theorem B2196301 : Blo 1951435 2196301 := bbase (se 3 (by rfl) ⟨411806, by rfl⟩ : syracuseStep 2196301 = 823613) (by norm_num)
theorem B2928401 : Blo 1951435 2928401 := bstep (se 2 (by rfl) ⟨1098150, by rfl⟩ : syracuseStep 2928401 = 2196301) B2196301
theorem B1952267 : Blo 1951435 1952267 := bstep (se 1 (by rfl) ⟨1464200, by rfl⟩ : syracuseStep 1952267 = 2928401) B2928401
theorem B6588917 : Blo 1951435 6588917 := bbase (se 5 (by rfl) ⟨308855, by rfl⟩ : syracuseStep 6588917 = 617711) (by norm_num)
theorem B4392611 : Blo 1951435 4392611 := bstep (se 1 (by rfl) ⟨3294458, by rfl⟩ : syracuseStep 4392611 = 6588917) B6588917
theorem B2928407 : Blo 1951435 2928407 := bstep (se 1 (by rfl) ⟨2196305, by rfl⟩ : syracuseStep 2928407 = 4392611) B4392611
theorem B1952271 : Blo 1951435 1952271 := bstep (se 1 (by rfl) ⟨1464203, by rfl⟩ : syracuseStep 1952271 = 2928407) B2928407
theorem B2928413 : Blo 1951435 2928413 := bbase (se 3 (by rfl) ⟨549077, by rfl⟩ : syracuseStep 2928413 = 1098155) (by norm_num)
theorem B1952275 : Blo 1951435 1952275 := bstep (se 1 (by rfl) ⟨1464206, by rfl⟩ : syracuseStep 1952275 = 2928413) B2928413
theorem B4392629 : Blo 1951435 4392629 := bbase (se 5 (by rfl) ⟨205904, by rfl⟩ : syracuseStep 4392629 = 411809) (by norm_num)
theorem B2928419 : Blo 1951435 2928419 := bstep (se 1 (by rfl) ⟨2196314, by rfl⟩ : syracuseStep 2928419 = 4392629) B4392629
theorem B1952279 : Blo 1951435 1952279 := bstep (se 1 (by rfl) ⟨1464209, by rfl⟩ : syracuseStep 1952279 = 2928419) B2928419
theorem B11118869 : Blo 1951435 11118869 := bbase (se 6 (by rfl) ⟨260598, by rfl⟩ : syracuseStep 11118869 = 521197) (by norm_num)
theorem B7412579 : Blo 1951435 7412579 := bstep (se 1 (by rfl) ⟨5559434, by rfl⟩ : syracuseStep 7412579 = 11118869) B11118869
theorem B4941719 : Blo 1951435 4941719 := bstep (se 1 (by rfl) ⟨3706289, by rfl⟩ : syracuseStep 4941719 = 7412579) B7412579
theorem B3294479 : Blo 1951435 3294479 := bstep (se 1 (by rfl) ⟨2470859, by rfl⟩ : syracuseStep 3294479 = 4941719) B4941719
theorem B2196319 : Blo 1951435 2196319 := bstep (se 1 (by rfl) ⟨1647239, by rfl⟩ : syracuseStep 2196319 = 3294479) B3294479
theorem B2928425 : Blo 1951435 2928425 := bstep (se 2 (by rfl) ⟨1098159, by rfl⟩ : syracuseStep 2928425 = 2196319) B2196319
theorem B1952283 : Blo 1951435 1952283 := bstep (se 1 (by rfl) ⟨1464212, by rfl⟩ : syracuseStep 1952283 = 2928425) B2928425
theorem B5559445 : Blo 1951435 5559445 := bbase (se 6 (by rfl) ⟨130299, by rfl⟩ : syracuseStep 5559445 = 260599) (by norm_num)
theorem B7412593 : Blo 1951435 7412593 := bstep (se 2 (by rfl) ⟨2779722, by rfl⟩ : syracuseStep 7412593 = 5559445) B5559445
theorem B9883457 : Blo 1951435 9883457 := bstep (se 2 (by rfl) ⟨3706296, by rfl⟩ : syracuseStep 9883457 = 7412593) B7412593
theorem B6588971 : Blo 1951435 6588971 := bstep (se 1 (by rfl) ⟨4941728, by rfl⟩ : syracuseStep 6588971 = 9883457) B9883457
theorem B4392647 : Blo 1951435 4392647 := bstep (se 1 (by rfl) ⟨3294485, by rfl⟩ : syracuseStep 4392647 = 6588971) B6588971
theorem B2928431 : Blo 1951435 2928431 := bstep (se 1 (by rfl) ⟨2196323, by rfl⟩ : syracuseStep 2928431 = 4392647) B4392647
theorem B1952287 : Blo 1951435 1952287 := bstep (se 1 (by rfl) ⟨1464215, by rfl⟩ : syracuseStep 1952287 = 2928431) B2928431
theorem B2928437 : Blo 1951435 2928437 := bbase (se 5 (by rfl) ⟨137270, by rfl⟩ : syracuseStep 2928437 = 274541) (by norm_num)
theorem B1952291 : Blo 1951435 1952291 := bstep (se 1 (by rfl) ⟨1464218, by rfl⟩ : syracuseStep 1952291 = 2928437) B2928437
theorem B4941749 : Blo 1951435 4941749 := bbase (se 5 (by rfl) ⟨231644, by rfl⟩ : syracuseStep 4941749 = 463289) (by norm_num)
theorem B3294499 : Blo 1951435 3294499 := bstep (se 1 (by rfl) ⟨2470874, by rfl⟩ : syracuseStep 3294499 = 4941749) B4941749
theorem B4392665 : Blo 1951435 4392665 := bstep (se 2 (by rfl) ⟨1647249, by rfl⟩ : syracuseStep 4392665 = 3294499) B3294499
theorem B2928443 : Blo 1951435 2928443 := bstep (se 1 (by rfl) ⟨2196332, by rfl⟩ : syracuseStep 2928443 = 4392665) B4392665
theorem B1952295 : Blo 1951435 1952295 := bstep (se 1 (by rfl) ⟨1464221, by rfl⟩ : syracuseStep 1952295 = 2928443) B2928443
theorem B2196337 : Blo 1951435 2196337 := bbase (se 2 (by rfl) ⟨823626, by rfl⟩ : syracuseStep 2196337 = 1647253) (by norm_num)
theorem B2928449 : Blo 1951435 2928449 := bstep (se 2 (by rfl) ⟨1098168, by rfl⟩ : syracuseStep 2928449 = 2196337) B2196337
theorem B1952299 : Blo 1951435 1952299 := bstep (se 1 (by rfl) ⟨1464224, by rfl⟩ : syracuseStep 1952299 = 2928449) B2928449
theorem B8339237 : Blo 1951435 8339237 := bbase (se 4 (by rfl) ⟨781803, by rfl⟩ : syracuseStep 8339237 = 1563607) (by norm_num)
theorem B5559491 : Blo 1951435 5559491 := bstep (se 1 (by rfl) ⟨4169618, by rfl⟩ : syracuseStep 5559491 = 8339237) B8339237
theorem B3706327 : Blo 1951435 3706327 := bstep (se 1 (by rfl) ⟨2779745, by rfl⟩ : syracuseStep 3706327 = 5559491) B5559491
theorem B4941769 : Blo 1951435 4941769 := bstep (se 2 (by rfl) ⟨1853163, by rfl⟩ : syracuseStep 4941769 = 3706327) B3706327
theorem B6589025 : Blo 1951435 6589025 := bstep (se 2 (by rfl) ⟨2470884, by rfl⟩ : syracuseStep 6589025 = 4941769) B4941769
theorem B4392683 : Blo 1951435 4392683 := bstep (se 1 (by rfl) ⟨3294512, by rfl⟩ : syracuseStep 4392683 = 6589025) B6589025
theorem B2928455 : Blo 1951435 2928455 := bstep (se 1 (by rfl) ⟨2196341, by rfl⟩ : syracuseStep 2928455 = 4392683) B4392683
theorem B1952303 : Blo 1951435 1952303 := bstep (se 1 (by rfl) ⟨1464227, by rfl⟩ : syracuseStep 1952303 = 2928455) B2928455
theorem B2928461 : Blo 1951435 2928461 := bbase (se 3 (by rfl) ⟨549086, by rfl⟩ : syracuseStep 2928461 = 1098173) (by norm_num)
theorem B1952307 : Blo 1951435 1952307 := bstep (se 1 (by rfl) ⟨1464230, by rfl⟩ : syracuseStep 1952307 = 2928461) B2928461
theorem B4392701 : Blo 1951435 4392701 := bbase (se 3 (by rfl) ⟨823631, by rfl⟩ : syracuseStep 4392701 = 1647263) (by norm_num)
theorem B2928467 : Blo 1951435 2928467 := bstep (se 1 (by rfl) ⟨2196350, by rfl⟩ : syracuseStep 2928467 = 4392701) B4392701
theorem B1952311 : Blo 1951435 1952311 := bstep (se 1 (by rfl) ⟨1464233, by rfl⟩ : syracuseStep 1952311 = 2928467) B2928467
theorem B3294533 : Blo 1951435 3294533 := bbase (se 4 (by rfl) ⟨308862, by rfl⟩ : syracuseStep 3294533 = 617725) (by norm_num)
theorem B2196355 : Blo 1951435 2196355 := bstep (se 1 (by rfl) ⟨1647266, by rfl⟩ : syracuseStep 2196355 = 3294533) B3294533
theorem B2928473 : Blo 1951435 2928473 := bstep (se 2 (by rfl) ⟨1098177, by rfl⟩ : syracuseStep 2928473 = 2196355) B2196355
theorem B1952315 : Blo 1951435 1952315 := bstep (se 1 (by rfl) ⟨1464236, by rfl⟩ : syracuseStep 1952315 = 2928473) B2928473
theorem B14825429 : Blo 1951435 14825429 := bbase (se 7 (by rfl) ⟨173735, by rfl⟩ : syracuseStep 14825429 = 347471) (by norm_num)
theorem B9883619 : Blo 1951435 9883619 := bstep (se 1 (by rfl) ⟨7412714, by rfl⟩ : syracuseStep 9883619 = 14825429) B14825429
theorem B6589079 : Blo 1951435 6589079 := bstep (se 1 (by rfl) ⟨4941809, by rfl⟩ : syracuseStep 6589079 = 9883619) B9883619
theorem B4392719 : Blo 1951435 4392719 := bstep (se 1 (by rfl) ⟨3294539, by rfl⟩ : syracuseStep 4392719 = 6589079) B6589079
theorem B2928479 : Blo 1951435 2928479 := bstep (se 1 (by rfl) ⟨2196359, by rfl⟩ : syracuseStep 2928479 = 4392719) B4392719
theorem B1952319 : Blo 1951435 1952319 := bstep (se 1 (by rfl) ⟨1464239, by rfl⟩ : syracuseStep 1952319 = 2928479) B2928479
theorem B2928485 : Blo 1951435 2928485 := bbase (se 4 (by rfl) ⟨274545, by rfl⟩ : syracuseStep 2928485 = 549091) (by norm_num)
theorem B1952323 : Blo 1951435 1952323 := bstep (se 1 (by rfl) ⟨1464242, by rfl⟩ : syracuseStep 1952323 = 2928485) B2928485
theorem B3706373 : Blo 1951435 3706373 := bbase (se 4 (by rfl) ⟨347472, by rfl⟩ : syracuseStep 3706373 = 694945) (by norm_num)
theorem B2470915 : Blo 1951435 2470915 := bstep (se 1 (by rfl) ⟨1853186, by rfl⟩ : syracuseStep 2470915 = 3706373) B3706373
theorem B3294553 : Blo 1951435 3294553 := bstep (se 2 (by rfl) ⟨1235457, by rfl⟩ : syracuseStep 3294553 = 2470915) B2470915
theorem B4392737 : Blo 1951435 4392737 := bstep (se 2 (by rfl) ⟨1647276, by rfl⟩ : syracuseStep 4392737 = 3294553) B3294553
theorem B2928491 : Blo 1951435 2928491 := bstep (se 1 (by rfl) ⟨2196368, by rfl⟩ : syracuseStep 2928491 = 4392737) B4392737
theorem B1952327 : Blo 1951435 1952327 := bstep (se 1 (by rfl) ⟨1464245, by rfl⟩ : syracuseStep 1952327 = 2928491) B2928491
theorem B2196373 : Blo 1951435 2196373 := bbase (se 6 (by rfl) ⟨51477, by rfl⟩ : syracuseStep 2196373 = 102955) (by norm_num)
theorem B2928497 : Blo 1951435 2928497 := bstep (se 2 (by rfl) ⟨1098186, by rfl⟩ : syracuseStep 2928497 = 2196373) B2196373
theorem B1952331 : Blo 1951435 1952331 := bstep (se 1 (by rfl) ⟨1464248, by rfl⟩ : syracuseStep 1952331 = 2928497) B2928497
theorem B2470925 : Blo 1951435 2470925 := bbase (se 3 (by rfl) ⟨463298, by rfl⟩ : syracuseStep 2470925 = 926597) (by norm_num)
theorem B6589133 : Blo 1951435 6589133 := bstep (se 3 (by rfl) ⟨1235462, by rfl⟩ : syracuseStep 6589133 = 2470925) B2470925
theorem B4392755 : Blo 1951435 4392755 := bstep (se 1 (by rfl) ⟨3294566, by rfl⟩ : syracuseStep 4392755 = 6589133) B6589133
theorem B2928503 : Blo 1951435 2928503 := bstep (se 1 (by rfl) ⟨2196377, by rfl⟩ : syracuseStep 2928503 = 4392755) B4392755
theorem B1952335 : Blo 1951435 1952335 := bstep (se 1 (by rfl) ⟨1464251, by rfl⟩ : syracuseStep 1952335 = 2928503) B2928503
theorem B2928509 : Blo 1951435 2928509 := bbase (se 3 (by rfl) ⟨549095, by rfl⟩ : syracuseStep 2928509 = 1098191) (by norm_num)
theorem B1952339 : Blo 1951435 1952339 := bstep (se 1 (by rfl) ⟨1464254, by rfl⟩ : syracuseStep 1952339 = 2928509) B2928509
theorem B4392773 : Blo 1951435 4392773 := bbase (se 4 (by rfl) ⟨411822, by rfl⟩ : syracuseStep 4392773 = 823645) (by norm_num)
theorem B2928515 : Blo 1951435 2928515 := bstep (se 1 (by rfl) ⟨2196386, by rfl⟩ : syracuseStep 2928515 = 4392773) B4392773
theorem B1952343 : Blo 1951435 1952343 := bstep (se 1 (by rfl) ⟨1464257, by rfl⟩ : syracuseStep 1952343 = 2928515) B2928515
theorem B3127285 : Blo 1951435 3127285 := bbase (se 5 (by rfl) ⟨146591, by rfl⟩ : syracuseStep 3127285 = 293183) (by norm_num)
theorem B4169713 : Blo 1951435 4169713 := bstep (se 2 (by rfl) ⟨1563642, by rfl⟩ : syracuseStep 4169713 = 3127285) B3127285
theorem B5559617 : Blo 1951435 5559617 := bstep (se 2 (by rfl) ⟨2084856, by rfl⟩ : syracuseStep 5559617 = 4169713) B4169713
theorem B3706411 : Blo 1951435 3706411 := bstep (se 1 (by rfl) ⟨2779808, by rfl⟩ : syracuseStep 3706411 = 5559617) B5559617
theorem B4941881 : Blo 1951435 4941881 := bstep (se 2 (by rfl) ⟨1853205, by rfl⟩ : syracuseStep 4941881 = 3706411) B3706411
theorem B3294587 : Blo 1951435 3294587 := bstep (se 1 (by rfl) ⟨2470940, by rfl⟩ : syracuseStep 3294587 = 4941881) B4941881
theorem B2196391 : Blo 1951435 2196391 := bstep (se 1 (by rfl) ⟨1647293, by rfl⟩ : syracuseStep 2196391 = 3294587) B3294587
theorem B2928521 : Blo 1951435 2928521 := bstep (se 2 (by rfl) ⟨1098195, by rfl⟩ : syracuseStep 2928521 = 2196391) B2196391
theorem B1952347 : Blo 1951435 1952347 := bstep (se 1 (by rfl) ⟨1464260, by rfl⟩ : syracuseStep 1952347 = 2928521) B2928521
theorem B9883781 : Blo 1951435 9883781 := bbase (se 4 (by rfl) ⟨926604, by rfl⟩ : syracuseStep 9883781 = 1853209) (by norm_num)
theorem B6589187 : Blo 1951435 6589187 := bstep (se 1 (by rfl) ⟨4941890, by rfl⟩ : syracuseStep 6589187 = 9883781) B9883781
theorem B4392791 : Blo 1951435 4392791 := bstep (se 1 (by rfl) ⟨3294593, by rfl⟩ : syracuseStep 4392791 = 6589187) B6589187
theorem B2928527 : Blo 1951435 2928527 := bstep (se 1 (by rfl) ⟨2196395, by rfl⟩ : syracuseStep 2928527 = 4392791) B4392791
theorem B1952351 : Blo 1951435 1952351 := bstep (se 1 (by rfl) ⟨1464263, by rfl⟩ : syracuseStep 1952351 = 2928527) B2928527
theorem B2928533 : Blo 1951435 2928533 := bbase (se 6 (by rfl) ⟨68637, by rfl⟩ : syracuseStep 2928533 = 137275) (by norm_num)
theorem B1952355 : Blo 1951435 1952355 := bstep (se 1 (by rfl) ⟨1464266, by rfl⟩ : syracuseStep 1952355 = 2928533) B2928533
theorem B2084869 : Blo 1951435 2084869 := bbase (se 4 (by rfl) ⟨195456, by rfl⟩ : syracuseStep 2084869 = 390913) (by norm_num)
theorem B11119301 : Blo 1951435 11119301 := bstep (se 4 (by rfl) ⟨1042434, by rfl⟩ : syracuseStep 11119301 = 2084869) B2084869
theorem B7412867 : Blo 1951435 7412867 := bstep (se 1 (by rfl) ⟨5559650, by rfl⟩ : syracuseStep 7412867 = 11119301) B11119301
theorem B4941911 : Blo 1951435 4941911 := bstep (se 1 (by rfl) ⟨3706433, by rfl⟩ : syracuseStep 4941911 = 7412867) B7412867
theorem B3294607 : Blo 1951435 3294607 := bstep (se 1 (by rfl) ⟨2470955, by rfl⟩ : syracuseStep 3294607 = 4941911) B4941911
theorem B4392809 : Blo 1951435 4392809 := bstep (se 2 (by rfl) ⟨1647303, by rfl⟩ : syracuseStep 4392809 = 3294607) B3294607
theorem B2928539 : Blo 1951435 2928539 := bstep (se 1 (by rfl) ⟨2196404, by rfl⟩ : syracuseStep 2928539 = 4392809) B4392809
theorem B1952359 : Blo 1951435 1952359 := bstep (se 1 (by rfl) ⟨1464269, by rfl⟩ : syracuseStep 1952359 = 2928539) B2928539
theorem B2196409 : Blo 1951435 2196409 := bbase (se 2 (by rfl) ⟨823653, by rfl⟩ : syracuseStep 2196409 = 1647307) (by norm_num)
theorem B2928545 : Blo 1951435 2928545 := bstep (se 2 (by rfl) ⟨1098204, by rfl⟩ : syracuseStep 2928545 = 2196409) B2196409
theorem B1952363 : Blo 1951435 1952363 := bstep (se 1 (by rfl) ⟨1464272, by rfl⟩ : syracuseStep 1952363 = 2928545) B2928545
theorem B5349349 : Blo 1951435 5349349 := bbase (se 4 (by rfl) ⟨501501, by rfl⟩ : syracuseStep 5349349 = 1003003) (by norm_num)
theorem B7132465 : Blo 1951435 7132465 := bstep (se 2 (by rfl) ⟨2674674, by rfl⟩ : syracuseStep 7132465 = 5349349) B5349349
theorem B38039813 : Blo 1951435 38039813 := bstep (se 4 (by rfl) ⟨3566232, by rfl⟩ : syracuseStep 38039813 = 7132465) B7132465
theorem B25359875 : Blo 1951435 25359875 := bstep (se 1 (by rfl) ⟨19019906, by rfl⟩ : syracuseStep 25359875 = 38039813) B38039813
theorem B16906583 : Blo 1951435 16906583 := bstep (se 1 (by rfl) ⟨12679937, by rfl⟩ : syracuseStep 16906583 = 25359875) B25359875
theorem B45084221 : Blo 1951435 45084221 := bstep (se 3 (by rfl) ⟨8453291, by rfl⟩ : syracuseStep 45084221 = 16906583) B16906583
theorem B30056147 : Blo 1951435 30056147 := bstep (se 1 (by rfl) ⟨22542110, by rfl⟩ : syracuseStep 30056147 = 45084221) B45084221
theorem B20037431 : Blo 1951435 20037431 := bstep (se 1 (by rfl) ⟨15028073, by rfl⟩ : syracuseStep 20037431 = 30056147) B30056147
theorem B13358287 : Blo 1951435 13358287 := bstep (se 1 (by rfl) ⟨10018715, by rfl⟩ : syracuseStep 13358287 = 20037431) B20037431
theorem B17811049 : Blo 1951435 17811049 := bstep (se 2 (by rfl) ⟨6679143, by rfl⟩ : syracuseStep 17811049 = 13358287) B13358287
theorem B23748065 : Blo 1951435 23748065 := bstep (se 2 (by rfl) ⟨8905524, by rfl⟩ : syracuseStep 23748065 = 17811049) B17811049
theorem B15832043 : Blo 1951435 15832043 := bstep (se 1 (by rfl) ⟨11874032, by rfl⟩ : syracuseStep 15832043 = 23748065) B23748065
theorem B10554695 : Blo 1951435 10554695 := bstep (se 1 (by rfl) ⟨7916021, by rfl⟩ : syracuseStep 10554695 = 15832043) B15832043
theorem B7036463 : Blo 1951435 7036463 := bstep (se 1 (by rfl) ⟨5277347, by rfl⟩ : syracuseStep 7036463 = 10554695) B10554695
theorem B4690975 : Blo 1951435 4690975 := bstep (se 1 (by rfl) ⟨3518231, by rfl⟩ : syracuseStep 4690975 = 7036463) B7036463
theorem B6254633 : Blo 1951435 6254633 := bstep (se 2 (by rfl) ⟨2345487, by rfl⟩ : syracuseStep 6254633 = 4690975) B4690975
theorem B4169755 : Blo 1951435 4169755 := bstep (se 1 (by rfl) ⟨3127316, by rfl⟩ : syracuseStep 4169755 = 6254633) B6254633
theorem B5559673 : Blo 1951435 5559673 := bstep (se 2 (by rfl) ⟨2084877, by rfl⟩ : syracuseStep 5559673 = 4169755) B4169755
theorem B7412897 : Blo 1951435 7412897 := bstep (se 2 (by rfl) ⟨2779836, by rfl⟩ : syracuseStep 7412897 = 5559673) B5559673
theorem B4941931 : Blo 1951435 4941931 := bstep (se 1 (by rfl) ⟨3706448, by rfl⟩ : syracuseStep 4941931 = 7412897) B7412897
theorem B6589241 : Blo 1951435 6589241 := bstep (se 2 (by rfl) ⟨2470965, by rfl⟩ : syracuseStep 6589241 = 4941931) B4941931
theorem B4392827 : Blo 1951435 4392827 := bstep (se 1 (by rfl) ⟨3294620, by rfl⟩ : syracuseStep 4392827 = 6589241) B6589241
theorem B2928551 : Blo 1951435 2928551 := bstep (se 1 (by rfl) ⟨2196413, by rfl⟩ : syracuseStep 2928551 = 4392827) B4392827
theorem B1952367 : Blo 1951435 1952367 := bstep (se 1 (by rfl) ⟨1464275, by rfl⟩ : syracuseStep 1952367 = 2928551) B2928551
theorem B2928557 : Blo 1951435 2928557 := bbase (se 3 (by rfl) ⟨549104, by rfl⟩ : syracuseStep 2928557 = 1098209) (by norm_num)
theorem B1952371 : Blo 1951435 1952371 := bstep (se 1 (by rfl) ⟨1464278, by rfl⟩ : syracuseStep 1952371 = 2928557) B2928557
theorem B4392845 : Blo 1951435 4392845 := bbase (se 3 (by rfl) ⟨823658, by rfl⟩ : syracuseStep 4392845 = 1647317) (by norm_num)
theorem B2928563 : Blo 1951435 2928563 := bstep (se 1 (by rfl) ⟨2196422, by rfl⟩ : syracuseStep 2928563 = 4392845) B4392845
theorem B1952375 : Blo 1951435 1952375 := bstep (se 1 (by rfl) ⟨1464281, by rfl⟩ : syracuseStep 1952375 = 2928563) B2928563
theorem B2470981 : Blo 1951435 2470981 := bbase (se 4 (by rfl) ⟨231654, by rfl⟩ : syracuseStep 2470981 = 463309) (by norm_num)
theorem B3294641 : Blo 1951435 3294641 := bstep (se 2 (by rfl) ⟨1235490, by rfl⟩ : syracuseStep 3294641 = 2470981) B2470981
theorem B2196427 : Blo 1951435 2196427 := bstep (se 1 (by rfl) ⟨1647320, by rfl⟩ : syracuseStep 2196427 = 3294641) B3294641
theorem B2928569 : Blo 1951435 2928569 := bstep (se 2 (by rfl) ⟨1098213, by rfl⟩ : syracuseStep 2928569 = 2196427) B2196427
theorem B1952379 : Blo 1951435 1952379 := bstep (se 1 (by rfl) ⟨1464284, by rfl⟩ : syracuseStep 1952379 = 2928569) B2928569
theorem B5147021 : Blo 1951435 5147021 := bbase (se 3 (by rfl) ⟨965066, by rfl⟩ : syracuseStep 5147021 = 1930133) (by norm_num)
theorem B3431347 : Blo 1951435 3431347 := bstep (se 1 (by rfl) ⟨2573510, by rfl⟩ : syracuseStep 3431347 = 5147021) B5147021
theorem B73202069 : Blo 1951435 73202069 := bstep (se 6 (by rfl) ⟨1715673, by rfl⟩ : syracuseStep 73202069 = 3431347) B3431347
theorem B48801379 : Blo 1951435 48801379 := bstep (se 1 (by rfl) ⟨36601034, by rfl⟩ : syracuseStep 48801379 = 73202069) B73202069
theorem B65068505 : Blo 1951435 65068505 := bstep (se 2 (by rfl) ⟨24400689, by rfl⟩ : syracuseStep 65068505 = 48801379) B48801379
theorem B43379003 : Blo 1951435 43379003 := bstep (se 1 (by rfl) ⟨32534252, by rfl⟩ : syracuseStep 43379003 = 65068505) B65068505
theorem B115677341 : Blo 1951435 115677341 := bstep (se 3 (by rfl) ⟨21689501, by rfl⟩ : syracuseStep 115677341 = 43379003) B43379003
theorem B77118227 : Blo 1951435 77118227 := bstep (se 1 (by rfl) ⟨57838670, by rfl⟩ : syracuseStep 77118227 = 115677341) B115677341
theorem B51412151 : Blo 1951435 51412151 := bstep (se 1 (by rfl) ⟨38559113, by rfl⟩ : syracuseStep 51412151 = 77118227) B77118227
theorem B34274767 : Blo 1951435 34274767 := bstep (se 1 (by rfl) ⟨25706075, by rfl⟩ : syracuseStep 34274767 = 51412151) B51412151
theorem B45699689 : Blo 1951435 45699689 := bstep (se 2 (by rfl) ⟨17137383, by rfl⟩ : syracuseStep 45699689 = 34274767) B34274767
theorem B30466459 : Blo 1951435 30466459 := bstep (se 1 (by rfl) ⟨22849844, by rfl⟩ : syracuseStep 30466459 = 45699689) B45699689
theorem B162487781 : Blo 1951435 162487781 := bstep (se 4 (by rfl) ⟨15233229, by rfl⟩ : syracuseStep 162487781 = 30466459) B30466459
theorem B108325187 : Blo 1951435 108325187 := bstep (se 1 (by rfl) ⟨81243890, by rfl⟩ : syracuseStep 108325187 = 162487781) B162487781
theorem B72216791 : Blo 1951435 72216791 := bstep (se 1 (by rfl) ⟨54162593, by rfl⟩ : syracuseStep 72216791 = 108325187) B108325187
theorem B48144527 : Blo 1951435 48144527 := bstep (se 1 (by rfl) ⟨36108395, by rfl⟩ : syracuseStep 48144527 = 72216791) B72216791
theorem B32096351 : Blo 1951435 32096351 := bstep (se 1 (by rfl) ⟨24072263, by rfl⟩ : syracuseStep 32096351 = 48144527) B48144527
theorem B21397567 : Blo 1951435 21397567 := bstep (se 1 (by rfl) ⟨16048175, by rfl⟩ : syracuseStep 21397567 = 32096351) B32096351
theorem B28530089 : Blo 1951435 28530089 := bstep (se 2 (by rfl) ⟨10698783, by rfl⟩ : syracuseStep 28530089 = 21397567) B21397567
theorem B19020059 : Blo 1951435 19020059 := bstep (se 1 (by rfl) ⟨14265044, by rfl⟩ : syracuseStep 19020059 = 28530089) B28530089
theorem B12680039 : Blo 1951435 12680039 := bstep (se 1 (by rfl) ⟨9510029, by rfl⟩ : syracuseStep 12680039 = 19020059) B19020059
theorem B8453359 : Blo 1951435 8453359 := bstep (se 1 (by rfl) ⟨6340019, by rfl⟩ : syracuseStep 8453359 = 12680039) B12680039
theorem B11271145 : Blo 1951435 11271145 := bstep (se 2 (by rfl) ⟨4226679, by rfl⟩ : syracuseStep 11271145 = 8453359) B8453359
theorem B15028193 : Blo 1951435 15028193 := bstep (se 2 (by rfl) ⟨5635572, by rfl⟩ : syracuseStep 15028193 = 11271145) B11271145
theorem B40075181 : Blo 1951435 40075181 := bstep (se 3 (by rfl) ⟨7514096, by rfl⟩ : syracuseStep 40075181 = 15028193) B15028193
theorem B26716787 : Blo 1951435 26716787 := bstep (se 1 (by rfl) ⟨20037590, by rfl⟩ : syracuseStep 26716787 = 40075181) B40075181
theorem B17811191 : Blo 1951435 17811191 := bstep (se 1 (by rfl) ⟨13358393, by rfl⟩ : syracuseStep 17811191 = 26716787) B26716787
theorem B11874127 : Blo 1951435 11874127 := bstep (se 1 (by rfl) ⟨8905595, by rfl⟩ : syracuseStep 11874127 = 17811191) B17811191
theorem B15832169 : Blo 1951435 15832169 := bstep (se 2 (by rfl) ⟨5937063, by rfl⟩ : syracuseStep 15832169 = 11874127) B11874127
theorem B10554779 : Blo 1951435 10554779 := bstep (se 1 (by rfl) ⟨7916084, by rfl⟩ : syracuseStep 10554779 = 15832169) B15832169
theorem B7036519 : Blo 1951435 7036519 := bstep (se 1 (by rfl) ⟨5277389, by rfl⟩ : syracuseStep 7036519 = 10554779) B10554779
theorem B9382025 : Blo 1951435 9382025 := bstep (se 2 (by rfl) ⟨3518259, by rfl⟩ : syracuseStep 9382025 = 7036519) B7036519
theorem B25018733 : Blo 1951435 25018733 := bstep (se 3 (by rfl) ⟨4691012, by rfl⟩ : syracuseStep 25018733 = 9382025) B9382025
theorem B16679155 : Blo 1951435 16679155 := bstep (se 1 (by rfl) ⟨12509366, by rfl⟩ : syracuseStep 16679155 = 25018733) B25018733
theorem B22238873 : Blo 1951435 22238873 := bstep (se 2 (by rfl) ⟨8339577, by rfl⟩ : syracuseStep 22238873 = 16679155) B16679155
theorem B14825915 : Blo 1951435 14825915 := bstep (se 1 (by rfl) ⟨11119436, by rfl⟩ : syracuseStep 14825915 = 22238873) B22238873
theorem B9883943 : Blo 1951435 9883943 := bstep (se 1 (by rfl) ⟨7412957, by rfl⟩ : syracuseStep 9883943 = 14825915) B14825915
theorem B6589295 : Blo 1951435 6589295 := bstep (se 1 (by rfl) ⟨4941971, by rfl⟩ : syracuseStep 6589295 = 9883943) B9883943
theorem B4392863 : Blo 1951435 4392863 := bstep (se 1 (by rfl) ⟨3294647, by rfl⟩ : syracuseStep 4392863 = 6589295) B6589295
theorem B2928575 : Blo 1951435 2928575 := bstep (se 1 (by rfl) ⟨2196431, by rfl⟩ : syracuseStep 2928575 = 4392863) B4392863
theorem B1952383 : Blo 1951435 1952383 := bstep (se 1 (by rfl) ⟨1464287, by rfl⟩ : syracuseStep 1952383 = 2928575) B2928575
theorem B2928581 : Blo 1951435 2928581 := bbase (se 4 (by rfl) ⟨274554, by rfl⟩ : syracuseStep 2928581 = 549109) (by norm_num)
theorem B1952387 : Blo 1951435 1952387 := bstep (se 1 (by rfl) ⟨1464290, by rfl⟩ : syracuseStep 1952387 = 2928581) B2928581
theorem B3294661 : Blo 1951435 3294661 := bbase (se 4 (by rfl) ⟨308874, by rfl⟩ : syracuseStep 3294661 = 617749) (by norm_num)
theorem B4392881 : Blo 1951435 4392881 := bstep (se 2 (by rfl) ⟨1647330, by rfl⟩ : syracuseStep 4392881 = 3294661) B3294661
theorem B2928587 : Blo 1951435 2928587 := bstep (se 1 (by rfl) ⟨2196440, by rfl⟩ : syracuseStep 2928587 = 4392881) B4392881
theorem B1952391 : Blo 1951435 1952391 := bstep (se 1 (by rfl) ⟨1464293, by rfl⟩ : syracuseStep 1952391 = 2928587) B2928587
theorem B2196445 : Blo 1951435 2196445 := bbase (se 3 (by rfl) ⟨411833, by rfl⟩ : syracuseStep 2196445 = 823667) (by norm_num)
theorem B2928593 : Blo 1951435 2928593 := bstep (se 2 (by rfl) ⟨1098222, by rfl⟩ : syracuseStep 2928593 = 2196445) B2196445
theorem B1952395 : Blo 1951435 1952395 := bstep (se 1 (by rfl) ⟨1464296, by rfl⟩ : syracuseStep 1952395 = 2928593) B2928593
theorem B6589349 : Blo 1951435 6589349 := bbase (se 4 (by rfl) ⟨617751, by rfl⟩ : syracuseStep 6589349 = 1235503) (by norm_num)
theorem B4392899 : Blo 1951435 4392899 := bstep (se 1 (by rfl) ⟨3294674, by rfl⟩ : syracuseStep 4392899 = 6589349) B6589349
theorem B2928599 : Blo 1951435 2928599 := bstep (se 1 (by rfl) ⟨2196449, by rfl⟩ : syracuseStep 2928599 = 4392899) B4392899
theorem B1952399 : Blo 1951435 1952399 := bstep (se 1 (by rfl) ⟨1464299, by rfl⟩ : syracuseStep 1952399 = 2928599) B2928599
theorem B2928605 : Blo 1951435 2928605 := bbase (se 3 (by rfl) ⟨549113, by rfl⟩ : syracuseStep 2928605 = 1098227) (by norm_num)
theorem B1952403 : Blo 1951435 1952403 := bstep (se 1 (by rfl) ⟨1464302, by rfl⟩ : syracuseStep 1952403 = 2928605) B2928605
theorem B4392917 : Blo 1951435 4392917 := bbase (se 7 (by rfl) ⟨51479, by rfl⟩ : syracuseStep 4392917 = 102959) (by norm_num)
theorem B2928611 : Blo 1951435 2928611 := bstep (se 1 (by rfl) ⟨2196458, by rfl⟩ : syracuseStep 2928611 = 4392917) B4392917
theorem B1952407 : Blo 1951435 1952407 := bstep (se 1 (by rfl) ⟨1464305, by rfl⟩ : syracuseStep 1952407 = 2928611) B2928611
theorem B7720645 : Blo 1951435 7720645 := bbase (se 4 (by rfl) ⟨723810, by rfl⟩ : syracuseStep 7720645 = 1447621) (by norm_num)
theorem B10294193 : Blo 1951435 10294193 := bstep (se 2 (by rfl) ⟨3860322, by rfl⟩ : syracuseStep 10294193 = 7720645) B7720645
theorem B6862795 : Blo 1951435 6862795 := bstep (se 1 (by rfl) ⟨5147096, by rfl⟩ : syracuseStep 6862795 = 10294193) B10294193
theorem B36601573 : Blo 1951435 36601573 := bstep (se 4 (by rfl) ⟨3431397, by rfl⟩ : syracuseStep 36601573 = 6862795) B6862795
theorem B48802097 : Blo 1951435 48802097 := bstep (se 2 (by rfl) ⟨18300786, by rfl⟩ : syracuseStep 48802097 = 36601573) B36601573
theorem B32534731 : Blo 1951435 32534731 := bstep (se 1 (by rfl) ⟨24401048, by rfl⟩ : syracuseStep 32534731 = 48802097) B48802097
theorem B43379641 : Blo 1951435 43379641 := bstep (se 2 (by rfl) ⟨16267365, by rfl⟩ : syracuseStep 43379641 = 32534731) B32534731
theorem B57839521 : Blo 1951435 57839521 := bstep (se 2 (by rfl) ⟨21689820, by rfl⟩ : syracuseStep 57839521 = 43379641) B43379641
theorem B77119361 : Blo 1951435 77119361 := bstep (se 2 (by rfl) ⟨28919760, by rfl⟩ : syracuseStep 77119361 = 57839521) B57839521
theorem B51412907 : Blo 1951435 51412907 := bstep (se 1 (by rfl) ⟨38559680, by rfl⟩ : syracuseStep 51412907 = 77119361) B77119361
theorem B137101085 : Blo 1951435 137101085 := bstep (se 3 (by rfl) ⟨25706453, by rfl⟩ : syracuseStep 137101085 = 51412907) B51412907
theorem B91400723 : Blo 1951435 91400723 := bstep (se 1 (by rfl) ⟨68550542, by rfl⟩ : syracuseStep 91400723 = 137101085) B137101085
theorem B60933815 : Blo 1951435 60933815 := bstep (se 1 (by rfl) ⟨45700361, by rfl⟩ : syracuseStep 60933815 = 91400723) B91400723
theorem B40622543 : Blo 1951435 40622543 := bstep (se 1 (by rfl) ⟨30466907, by rfl⟩ : syracuseStep 40622543 = 60933815) B60933815
theorem B27081695 : Blo 1951435 27081695 := bstep (se 1 (by rfl) ⟨20311271, by rfl⟩ : syracuseStep 27081695 = 40622543) B40622543
theorem B18054463 : Blo 1951435 18054463 := bstep (se 1 (by rfl) ⟨13540847, by rfl⟩ : syracuseStep 18054463 = 27081695) B27081695
theorem B24072617 : Blo 1951435 24072617 := bstep (se 2 (by rfl) ⟨9027231, by rfl⟩ : syracuseStep 24072617 = 18054463) B18054463
theorem B16048411 : Blo 1951435 16048411 := bstep (se 1 (by rfl) ⟨12036308, by rfl⟩ : syracuseStep 16048411 = 24072617) B24072617
theorem B342366101 : Blo 1951435 342366101 := bstep (se 6 (by rfl) ⟨8024205, by rfl⟩ : syracuseStep 342366101 = 16048411) B16048411
theorem B228244067 : Blo 1951435 228244067 := bstep (se 1 (by rfl) ⟨171183050, by rfl⟩ : syracuseStep 228244067 = 342366101) B342366101
theorem B152162711 : Blo 1951435 152162711 := bstep (se 1 (by rfl) ⟨114122033, by rfl⟩ : syracuseStep 152162711 = 228244067) B228244067
theorem B101441807 : Blo 1951435 101441807 := bstep (se 1 (by rfl) ⟨76081355, by rfl⟩ : syracuseStep 101441807 = 152162711) B152162711
theorem B67627871 : Blo 1951435 67627871 := bstep (se 1 (by rfl) ⟨50720903, by rfl⟩ : syracuseStep 67627871 = 101441807) B101441807
theorem B45085247 : Blo 1951435 45085247 := bstep (se 1 (by rfl) ⟨33813935, by rfl⟩ : syracuseStep 45085247 = 67627871) B67627871
theorem B30056831 : Blo 1951435 30056831 := bstep (se 1 (by rfl) ⟨22542623, by rfl⟩ : syracuseStep 30056831 = 45085247) B45085247
theorem B20037887 : Blo 1951435 20037887 := bstep (se 1 (by rfl) ⟨15028415, by rfl⟩ : syracuseStep 20037887 = 30056831) B30056831
theorem B13358591 : Blo 1951435 13358591 := bstep (se 1 (by rfl) ⟨10018943, by rfl⟩ : syracuseStep 13358591 = 20037887) B20037887
theorem B8905727 : Blo 1951435 8905727 := bstep (se 1 (by rfl) ⟨6679295, by rfl⟩ : syracuseStep 8905727 = 13358591) B13358591
theorem B5937151 : Blo 1951435 5937151 := bstep (se 1 (by rfl) ⟨4452863, by rfl⟩ : syracuseStep 5937151 = 8905727) B8905727
theorem B7916201 : Blo 1951435 7916201 := bstep (se 2 (by rfl) ⟨2968575, by rfl⟩ : syracuseStep 7916201 = 5937151) B5937151
theorem B5277467 : Blo 1951435 5277467 := bstep (se 1 (by rfl) ⟨3958100, by rfl⟩ : syracuseStep 5277467 = 7916201) B7916201
theorem B3518311 : Blo 1951435 3518311 := bstep (se 1 (by rfl) ⟨2638733, by rfl⟩ : syracuseStep 3518311 = 5277467) B5277467
theorem B4691081 : Blo 1951435 4691081 := bstep (se 2 (by rfl) ⟨1759155, by rfl⟩ : syracuseStep 4691081 = 3518311) B3518311
theorem B12509549 : Blo 1951435 12509549 := bstep (se 3 (by rfl) ⟨2345540, by rfl⟩ : syracuseStep 12509549 = 4691081) B4691081
theorem B8339699 : Blo 1951435 8339699 := bstep (se 1 (by rfl) ⟨6254774, by rfl⟩ : syracuseStep 8339699 = 12509549) B12509549
theorem B5559799 : Blo 1951435 5559799 := bstep (se 1 (by rfl) ⟨4169849, by rfl⟩ : syracuseStep 5559799 = 8339699) B8339699
theorem B7413065 : Blo 1951435 7413065 := bstep (se 2 (by rfl) ⟨2779899, by rfl⟩ : syracuseStep 7413065 = 5559799) B5559799
theorem B4942043 : Blo 1951435 4942043 := bstep (se 1 (by rfl) ⟨3706532, by rfl⟩ : syracuseStep 4942043 = 7413065) B7413065
theorem B3294695 : Blo 1951435 3294695 := bstep (se 1 (by rfl) ⟨2471021, by rfl⟩ : syracuseStep 3294695 = 4942043) B4942043
theorem B2196463 : Blo 1951435 2196463 := bstep (se 1 (by rfl) ⟨1647347, by rfl⟩ : syracuseStep 2196463 = 3294695) B3294695
theorem B2928617 : Blo 1951435 2928617 := bstep (se 2 (by rfl) ⟨1098231, by rfl⟩ : syracuseStep 2928617 = 2196463) B2196463
theorem B1952411 : Blo 1951435 1952411 := bstep (se 1 (by rfl) ⟨1464308, by rfl⟩ : syracuseStep 1952411 = 2928617) B2928617
theorem B2345545 : Blo 1951435 2345545 := bbase (se 2 (by rfl) ⟨879579, by rfl⟩ : syracuseStep 2345545 = 1759159) (by norm_num)
theorem B3127393 : Blo 1951435 3127393 := bstep (se 2 (by rfl) ⟨1172772, by rfl⟩ : syracuseStep 3127393 = 2345545) B2345545
theorem B16679429 : Blo 1951435 16679429 := bstep (se 4 (by rfl) ⟨1563696, by rfl⟩ : syracuseStep 16679429 = 3127393) B3127393
theorem B11119619 : Blo 1951435 11119619 := bstep (se 1 (by rfl) ⟨8339714, by rfl⟩ : syracuseStep 11119619 = 16679429) B16679429
theorem B7413079 : Blo 1951435 7413079 := bstep (se 1 (by rfl) ⟨5559809, by rfl⟩ : syracuseStep 7413079 = 11119619) B11119619
theorem B9884105 : Blo 1951435 9884105 := bstep (se 2 (by rfl) ⟨3706539, by rfl⟩ : syracuseStep 9884105 = 7413079) B7413079
theorem B6589403 : Blo 1951435 6589403 := bstep (se 1 (by rfl) ⟨4942052, by rfl⟩ : syracuseStep 6589403 = 9884105) B9884105
theorem B4392935 : Blo 1951435 4392935 := bstep (se 1 (by rfl) ⟨3294701, by rfl⟩ : syracuseStep 4392935 = 6589403) B6589403
theorem B2928623 : Blo 1951435 2928623 := bstep (se 1 (by rfl) ⟨2196467, by rfl⟩ : syracuseStep 2928623 = 4392935) B4392935
theorem B1952415 : Blo 1951435 1952415 := bstep (se 1 (by rfl) ⟨1464311, by rfl⟩ : syracuseStep 1952415 = 2928623) B2928623
theorem B2928629 : Blo 1951435 2928629 := bbase (se 5 (by rfl) ⟨137279, by rfl⟩ : syracuseStep 2928629 = 274559) (by norm_num)
theorem B1952419 : Blo 1951435 1952419 := bstep (se 1 (by rfl) ⟨1464314, by rfl⟩ : syracuseStep 1952419 = 2928629) B2928629
theorem B3518333 : Blo 1951435 3518333 := bbase (se 3 (by rfl) ⟨659687, by rfl⟩ : syracuseStep 3518333 = 1319375) (by norm_num)
theorem B2345555 : Blo 1951435 2345555 := bstep (se 1 (by rfl) ⟨1759166, by rfl⟩ : syracuseStep 2345555 = 3518333) B3518333
theorem B6254813 : Blo 1951435 6254813 := bstep (se 3 (by rfl) ⟨1172777, by rfl⟩ : syracuseStep 6254813 = 2345555) B2345555
theorem B4169875 : Blo 1951435 4169875 := bstep (se 1 (by rfl) ⟨3127406, by rfl⟩ : syracuseStep 4169875 = 6254813) B6254813
theorem B5559833 : Blo 1951435 5559833 := bstep (se 2 (by rfl) ⟨2084937, by rfl⟩ : syracuseStep 5559833 = 4169875) B4169875
theorem B3706555 : Blo 1951435 3706555 := bstep (se 1 (by rfl) ⟨2779916, by rfl⟩ : syracuseStep 3706555 = 5559833) B5559833
theorem B4942073 : Blo 1951435 4942073 := bstep (se 2 (by rfl) ⟨1853277, by rfl⟩ : syracuseStep 4942073 = 3706555) B3706555
theorem B3294715 : Blo 1951435 3294715 := bstep (se 1 (by rfl) ⟨2471036, by rfl⟩ : syracuseStep 3294715 = 4942073) B4942073
theorem B4392953 : Blo 1951435 4392953 := bstep (se 2 (by rfl) ⟨1647357, by rfl⟩ : syracuseStep 4392953 = 3294715) B3294715
theorem B2928635 : Blo 1951435 2928635 := bstep (se 1 (by rfl) ⟨2196476, by rfl⟩ : syracuseStep 2928635 = 4392953) B4392953
theorem B1952423 : Blo 1951435 1952423 := bstep (se 1 (by rfl) ⟨1464317, by rfl⟩ : syracuseStep 1952423 = 2928635) B2928635
theorem B2196481 : Blo 1951435 2196481 := bbase (se 2 (by rfl) ⟨823680, by rfl⟩ : syracuseStep 2196481 = 1647361) (by norm_num)
theorem B2928641 : Blo 1951435 2928641 := bstep (se 2 (by rfl) ⟨1098240, by rfl⟩ : syracuseStep 2928641 = 2196481) B2196481
theorem B1952427 : Blo 1951435 1952427 := bstep (se 1 (by rfl) ⟨1464320, by rfl⟩ : syracuseStep 1952427 = 2928641) B2928641
theorem B4942093 : Blo 1951435 4942093 := bbase (se 3 (by rfl) ⟨926642, by rfl⟩ : syracuseStep 4942093 = 1853285) (by norm_num)
theorem B6589457 : Blo 1951435 6589457 := bstep (se 2 (by rfl) ⟨2471046, by rfl⟩ : syracuseStep 6589457 = 4942093) B4942093
theorem B4392971 : Blo 1951435 4392971 := bstep (se 1 (by rfl) ⟨3294728, by rfl⟩ : syracuseStep 4392971 = 6589457) B6589457
theorem B2928647 : Blo 1951435 2928647 := bstep (se 1 (by rfl) ⟨2196485, by rfl⟩ : syracuseStep 2928647 = 4392971) B4392971
theorem B1952431 : Blo 1951435 1952431 := bstep (se 1 (by rfl) ⟨1464323, by rfl⟩ : syracuseStep 1952431 = 2928647) B2928647
theorem B2928653 : Blo 1951435 2928653 := bbase (se 3 (by rfl) ⟨549122, by rfl⟩ : syracuseStep 2928653 = 1098245) (by norm_num)
theorem B1952435 : Blo 1951435 1952435 := bstep (se 1 (by rfl) ⟨1464326, by rfl⟩ : syracuseStep 1952435 = 2928653) B2928653
theorem B4392989 : Blo 1951435 4392989 := bbase (se 3 (by rfl) ⟨823685, by rfl⟩ : syracuseStep 4392989 = 1647371) (by norm_num)
theorem B2928659 : Blo 1951435 2928659 := bstep (se 1 (by rfl) ⟨2196494, by rfl⟩ : syracuseStep 2928659 = 4392989) B4392989
theorem B1952439 : Blo 1951435 1952439 := bstep (se 1 (by rfl) ⟨1464329, by rfl⟩ : syracuseStep 1952439 = 2928659) B2928659
theorem B3294749 : Blo 1951435 3294749 := bbase (se 3 (by rfl) ⟨617765, by rfl⟩ : syracuseStep 3294749 = 1235531) (by norm_num)
theorem B2196499 : Blo 1951435 2196499 := bstep (se 1 (by rfl) ⟨1647374, by rfl⟩ : syracuseStep 2196499 = 3294749) B3294749
theorem B2928665 : Blo 1951435 2928665 := bstep (se 2 (by rfl) ⟨1098249, by rfl⟩ : syracuseStep 2928665 = 2196499) B2196499
theorem B1952443 : Blo 1951435 1952443 := bstep (se 1 (by rfl) ⟨1464332, by rfl⟩ : syracuseStep 1952443 = 2928665) B2928665
theorem B3009133 : Blo 1951435 3009133 := bbase (se 3 (by rfl) ⟨564212, by rfl⟩ : syracuseStep 3009133 = 1128425) (by norm_num)
theorem B4012177 : Blo 1951435 4012177 := bstep (se 2 (by rfl) ⟨1504566, by rfl⟩ : syracuseStep 4012177 = 3009133) B3009133
theorem B5349569 : Blo 1951435 5349569 := bstep (se 2 (by rfl) ⟨2006088, by rfl⟩ : syracuseStep 5349569 = 4012177) B4012177
theorem B14265517 : Blo 1951435 14265517 := bstep (se 3 (by rfl) ⟨2674784, by rfl⟩ : syracuseStep 14265517 = 5349569) B5349569
theorem B19020689 : Blo 1951435 19020689 := bstep (se 2 (by rfl) ⟨7132758, by rfl⟩ : syracuseStep 19020689 = 14265517) B14265517
theorem B12680459 : Blo 1951435 12680459 := bstep (se 1 (by rfl) ⟨9510344, by rfl⟩ : syracuseStep 12680459 = 19020689) B19020689
theorem B8453639 : Blo 1951435 8453639 := bstep (se 1 (by rfl) ⟨6340229, by rfl⟩ : syracuseStep 8453639 = 12680459) B12680459
theorem B5635759 : Blo 1951435 5635759 := bstep (se 1 (by rfl) ⟨4226819, by rfl⟩ : syracuseStep 5635759 = 8453639) B8453639
theorem B7514345 : Blo 1951435 7514345 := bstep (se 2 (by rfl) ⟨2817879, by rfl⟩ : syracuseStep 7514345 = 5635759) B5635759
theorem B5009563 : Blo 1951435 5009563 := bstep (se 1 (by rfl) ⟨3757172, by rfl⟩ : syracuseStep 5009563 = 7514345) B7514345
theorem B6679417 : Blo 1951435 6679417 := bstep (se 2 (by rfl) ⟨2504781, by rfl⟩ : syracuseStep 6679417 = 5009563) B5009563
theorem B8905889 : Blo 1951435 8905889 := bstep (se 2 (by rfl) ⟨3339708, by rfl⟩ : syracuseStep 8905889 = 6679417) B6679417
theorem B5937259 : Blo 1951435 5937259 := bstep (se 1 (by rfl) ⟨4452944, by rfl⟩ : syracuseStep 5937259 = 8905889) B8905889
theorem B7916345 : Blo 1951435 7916345 := bstep (se 2 (by rfl) ⟨2968629, by rfl⟩ : syracuseStep 7916345 = 5937259) B5937259
theorem B5277563 : Blo 1951435 5277563 := bstep (se 1 (by rfl) ⟨3958172, by rfl⟩ : syracuseStep 5277563 = 7916345) B7916345
theorem B3518375 : Blo 1951435 3518375 := bstep (se 1 (by rfl) ⟨2638781, by rfl⟩ : syracuseStep 3518375 = 5277563) B5277563
theorem B9382333 : Blo 1951435 9382333 := bstep (se 3 (by rfl) ⟨1759187, by rfl⟩ : syracuseStep 9382333 = 3518375) B3518375
theorem B12509777 : Blo 1951435 12509777 := bstep (se 2 (by rfl) ⟨4691166, by rfl⟩ : syracuseStep 12509777 = 9382333) B9382333
theorem B8339851 : Blo 1951435 8339851 := bstep (se 1 (by rfl) ⟨6254888, by rfl⟩ : syracuseStep 8339851 = 12509777) B12509777
theorem B11119801 : Blo 1951435 11119801 := bstep (se 2 (by rfl) ⟨4169925, by rfl⟩ : syracuseStep 11119801 = 8339851) B8339851
theorem B14826401 : Blo 1951435 14826401 := bstep (se 2 (by rfl) ⟨5559900, by rfl⟩ : syracuseStep 14826401 = 11119801) B11119801
theorem B9884267 : Blo 1951435 9884267 := bstep (se 1 (by rfl) ⟨7413200, by rfl⟩ : syracuseStep 9884267 = 14826401) B14826401
theorem B6589511 : Blo 1951435 6589511 := bstep (se 1 (by rfl) ⟨4942133, by rfl⟩ : syracuseStep 6589511 = 9884267) B9884267
theorem B4393007 : Blo 1951435 4393007 := bstep (se 1 (by rfl) ⟨3294755, by rfl⟩ : syracuseStep 4393007 = 6589511) B6589511
theorem B2928671 : Blo 1951435 2928671 := bstep (se 1 (by rfl) ⟨2196503, by rfl⟩ : syracuseStep 2928671 = 4393007) B4393007
theorem B1952447 : Blo 1951435 1952447 := bstep (se 1 (by rfl) ⟨1464335, by rfl⟩ : syracuseStep 1952447 = 2928671) B2928671
theorem B2928677 : Blo 1951435 2928677 := bbase (se 4 (by rfl) ⟨274563, by rfl⟩ : syracuseStep 2928677 = 549127) (by norm_num)
theorem B1952451 : Blo 1951435 1952451 := bstep (se 1 (by rfl) ⟨1464338, by rfl⟩ : syracuseStep 1952451 = 2928677) B2928677
theorem B2471077 : Blo 1951435 2471077 := bbase (se 4 (by rfl) ⟨231663, by rfl⟩ : syracuseStep 2471077 = 463327) (by norm_num)
theorem B3294769 : Blo 1951435 3294769 := bstep (se 2 (by rfl) ⟨1235538, by rfl⟩ : syracuseStep 3294769 = 2471077) B2471077
theorem B4393025 : Blo 1951435 4393025 := bstep (se 2 (by rfl) ⟨1647384, by rfl⟩ : syracuseStep 4393025 = 3294769) B3294769
theorem B2928683 : Blo 1951435 2928683 := bstep (se 1 (by rfl) ⟨2196512, by rfl⟩ : syracuseStep 2928683 = 4393025) B4393025
theorem B1952455 : Blo 1951435 1952455 := bstep (se 1 (by rfl) ⟨1464341, by rfl⟩ : syracuseStep 1952455 = 2928683) B2928683
theorem B2196517 : Blo 1951435 2196517 := bbase (se 4 (by rfl) ⟨205923, by rfl⟩ : syracuseStep 2196517 = 411847) (by norm_num)
theorem B2928689 : Blo 1951435 2928689 := bstep (se 2 (by rfl) ⟨1098258, by rfl⟩ : syracuseStep 2928689 = 2196517) B2196517
theorem B1952459 : Blo 1951435 1952459 := bstep (se 1 (by rfl) ⟨1464344, by rfl⟩ : syracuseStep 1952459 = 2928689) B2928689
theorem B3518405 : Blo 1951435 3518405 := bbase (se 4 (by rfl) ⟨329850, by rfl⟩ : syracuseStep 3518405 = 659701) (by norm_num)
theorem B2345603 : Blo 1951435 2345603 := bstep (se 1 (by rfl) ⟨1759202, by rfl⟩ : syracuseStep 2345603 = 3518405) B3518405
theorem B6254941 : Blo 1951435 6254941 := bstep (se 3 (by rfl) ⟨1172801, by rfl⟩ : syracuseStep 6254941 = 2345603) B2345603
theorem B8339921 : Blo 1951435 8339921 := bstep (se 2 (by rfl) ⟨3127470, by rfl⟩ : syracuseStep 8339921 = 6254941) B6254941
theorem B5559947 : Blo 1951435 5559947 := bstep (se 1 (by rfl) ⟨4169960, by rfl⟩ : syracuseStep 5559947 = 8339921) B8339921
theorem B3706631 : Blo 1951435 3706631 := bstep (se 1 (by rfl) ⟨2779973, by rfl⟩ : syracuseStep 3706631 = 5559947) B5559947
theorem B2471087 : Blo 1951435 2471087 := bstep (se 1 (by rfl) ⟨1853315, by rfl⟩ : syracuseStep 2471087 = 3706631) B3706631
theorem B6589565 : Blo 1951435 6589565 := bstep (se 3 (by rfl) ⟨1235543, by rfl⟩ : syracuseStep 6589565 = 2471087) B2471087
theorem B4393043 : Blo 1951435 4393043 := bstep (se 1 (by rfl) ⟨3294782, by rfl⟩ : syracuseStep 4393043 = 6589565) B6589565
theorem B2928695 : Blo 1951435 2928695 := bstep (se 1 (by rfl) ⟨2196521, by rfl⟩ : syracuseStep 2928695 = 4393043) B4393043
theorem B1952463 : Blo 1951435 1952463 := bstep (se 1 (by rfl) ⟨1464347, by rfl⟩ : syracuseStep 1952463 = 2928695) B2928695
theorem B2928701 : Blo 1951435 2928701 := bbase (se 3 (by rfl) ⟨549131, by rfl⟩ : syracuseStep 2928701 = 1098263) (by norm_num)
theorem B1952467 : Blo 1951435 1952467 := bstep (se 1 (by rfl) ⟨1464350, by rfl⟩ : syracuseStep 1952467 = 2928701) B2928701
theorem B4393061 : Blo 1951435 4393061 := bbase (se 4 (by rfl) ⟨411849, by rfl⟩ : syracuseStep 4393061 = 823699) (by norm_num)
theorem B2928707 : Blo 1951435 2928707 := bstep (se 1 (by rfl) ⟨2196530, by rfl⟩ : syracuseStep 2928707 = 4393061) B4393061
theorem B1952471 : Blo 1951435 1952471 := bstep (se 1 (by rfl) ⟨1464353, by rfl⟩ : syracuseStep 1952471 = 2928707) B2928707
theorem B4942205 : Blo 1951435 4942205 := bbase (se 3 (by rfl) ⟨926663, by rfl⟩ : syracuseStep 4942205 = 1853327) (by norm_num)
theorem B3294803 : Blo 1951435 3294803 := bstep (se 1 (by rfl) ⟨2471102, by rfl⟩ : syracuseStep 3294803 = 4942205) B4942205
theorem B2196535 : Blo 1951435 2196535 := bstep (se 1 (by rfl) ⟨1647401, by rfl⟩ : syracuseStep 2196535 = 3294803) B3294803
theorem B2928713 : Blo 1951435 2928713 := bstep (se 2 (by rfl) ⟨1098267, by rfl⟩ : syracuseStep 2928713 = 2196535) B2196535
theorem B1952475 : Blo 1951435 1952475 := bstep (se 1 (by rfl) ⟨1464356, by rfl⟩ : syracuseStep 1952475 = 2928713) B2928713
theorem B3706661 : Blo 1951435 3706661 := bbase (se 4 (by rfl) ⟨347499, by rfl⟩ : syracuseStep 3706661 = 694999) (by norm_num)
theorem B9884429 : Blo 1951435 9884429 := bstep (se 3 (by rfl) ⟨1853330, by rfl⟩ : syracuseStep 9884429 = 3706661) B3706661
theorem B6589619 : Blo 1951435 6589619 := bstep (se 1 (by rfl) ⟨4942214, by rfl⟩ : syracuseStep 6589619 = 9884429) B9884429
theorem B4393079 : Blo 1951435 4393079 := bstep (se 1 (by rfl) ⟨3294809, by rfl⟩ : syracuseStep 4393079 = 6589619) B6589619
theorem B2928719 : Blo 1951435 2928719 := bstep (se 1 (by rfl) ⟨2196539, by rfl⟩ : syracuseStep 2928719 = 4393079) B4393079
theorem B1952479 : Blo 1951435 1952479 := bstep (se 1 (by rfl) ⟨1464359, by rfl⟩ : syracuseStep 1952479 = 2928719) B2928719
theorem B2928725 : Blo 1951435 2928725 := bbase (se 8 (by rfl) ⟨17160, by rfl⟩ : syracuseStep 2928725 = 34321) (by norm_num)
theorem B1952483 : Blo 1951435 1952483 := bstep (se 1 (by rfl) ⟨1464362, by rfl⟩ : syracuseStep 1952483 = 2928725) B2928725
theorem B2113453 : Blo 1951435 2113453 := bbase (se 3 (by rfl) ⟨396272, by rfl⟩ : syracuseStep 2113453 = 792545) (by norm_num)
theorem B2817937 : Blo 1951435 2817937 := bstep (se 2 (by rfl) ⟨1056726, by rfl⟩ : syracuseStep 2817937 = 2113453) B2113453
theorem B3757249 : Blo 1951435 3757249 := bstep (se 2 (by rfl) ⟨1408968, by rfl⟩ : syracuseStep 3757249 = 2817937) B2817937
theorem B20038661 : Blo 1951435 20038661 := bstep (se 4 (by rfl) ⟨1878624, by rfl⟩ : syracuseStep 20038661 = 3757249) B3757249
theorem B13359107 : Blo 1951435 13359107 := bstep (se 1 (by rfl) ⟨10019330, by rfl⟩ : syracuseStep 13359107 = 20038661) B20038661
theorem B35624285 : Blo 1951435 35624285 := bstep (se 3 (by rfl) ⟨6679553, by rfl⟩ : syracuseStep 35624285 = 13359107) B13359107
theorem B23749523 : Blo 1951435 23749523 := bstep (se 1 (by rfl) ⟨17812142, by rfl⟩ : syracuseStep 23749523 = 35624285) B35624285
theorem B15833015 : Blo 1951435 15833015 := bstep (se 1 (by rfl) ⟨11874761, by rfl⟩ : syracuseStep 15833015 = 23749523) B23749523
theorem B10555343 : Blo 1951435 10555343 := bstep (se 1 (by rfl) ⟨7916507, by rfl⟩ : syracuseStep 10555343 = 15833015) B15833015
theorem B7036895 : Blo 1951435 7036895 := bstep (se 1 (by rfl) ⟨5277671, by rfl⟩ : syracuseStep 7036895 = 10555343) B10555343
theorem B18765053 : Blo 1951435 18765053 := bstep (se 3 (by rfl) ⟨3518447, by rfl⟩ : syracuseStep 18765053 = 7036895) B7036895
theorem B12510035 : Blo 1951435 12510035 := bstep (se 1 (by rfl) ⟨9382526, by rfl⟩ : syracuseStep 12510035 = 18765053) B18765053
theorem B8340023 : Blo 1951435 8340023 := bstep (se 1 (by rfl) ⟨6255017, by rfl⟩ : syracuseStep 8340023 = 12510035) B12510035
theorem B5560015 : Blo 1951435 5560015 := bstep (se 1 (by rfl) ⟨4170011, by rfl⟩ : syracuseStep 5560015 = 8340023) B8340023
theorem B7413353 : Blo 1951435 7413353 := bstep (se 2 (by rfl) ⟨2780007, by rfl⟩ : syracuseStep 7413353 = 5560015) B5560015
theorem B4942235 : Blo 1951435 4942235 := bstep (se 1 (by rfl) ⟨3706676, by rfl⟩ : syracuseStep 4942235 = 7413353) B7413353
theorem B3294823 : Blo 1951435 3294823 := bstep (se 1 (by rfl) ⟨2471117, by rfl⟩ : syracuseStep 3294823 = 4942235) B4942235
theorem B4393097 : Blo 1951435 4393097 := bstep (se 2 (by rfl) ⟨1647411, by rfl⟩ : syracuseStep 4393097 = 3294823) B3294823
theorem B2928731 : Blo 1951435 2928731 := bstep (se 1 (by rfl) ⟨2196548, by rfl⟩ : syracuseStep 2928731 = 4393097) B4393097
theorem B1952487 : Blo 1951435 1952487 := bstep (se 1 (by rfl) ⟨1464365, by rfl⟩ : syracuseStep 1952487 = 2928731) B2928731
theorem B2196553 : Blo 1951435 2196553 := bbase (se 2 (by rfl) ⟨823707, by rfl⟩ : syracuseStep 2196553 = 1647415) (by norm_num)
theorem B2928737 : Blo 1951435 2928737 := bstep (se 2 (by rfl) ⟨1098276, by rfl⟩ : syracuseStep 2928737 = 2196553) B2196553
theorem B1952491 : Blo 1951435 1952491 := bstep (se 1 (by rfl) ⟨1464368, by rfl⟩ : syracuseStep 1952491 = 2928737) B2928737
theorem B2345641 : Blo 1951435 2345641 := bbase (se 2 (by rfl) ⟨879615, by rfl⟩ : syracuseStep 2345641 = 1759231) (by norm_num)
theorem B12510085 : Blo 1951435 12510085 := bstep (se 4 (by rfl) ⟨1172820, by rfl⟩ : syracuseStep 12510085 = 2345641) B2345641
theorem B16680113 : Blo 1951435 16680113 := bstep (se 2 (by rfl) ⟨6255042, by rfl⟩ : syracuseStep 16680113 = 12510085) B12510085
theorem B11120075 : Blo 1951435 11120075 := bstep (se 1 (by rfl) ⟨8340056, by rfl⟩ : syracuseStep 11120075 = 16680113) B16680113
theorem B7413383 : Blo 1951435 7413383 := bstep (se 1 (by rfl) ⟨5560037, by rfl⟩ : syracuseStep 7413383 = 11120075) B11120075
theorem B4942255 : Blo 1951435 4942255 := bstep (se 1 (by rfl) ⟨3706691, by rfl⟩ : syracuseStep 4942255 = 7413383) B7413383
theorem B6589673 : Blo 1951435 6589673 := bstep (se 2 (by rfl) ⟨2471127, by rfl⟩ : syracuseStep 6589673 = 4942255) B4942255
theorem B4393115 : Blo 1951435 4393115 := bstep (se 1 (by rfl) ⟨3294836, by rfl⟩ : syracuseStep 4393115 = 6589673) B6589673
theorem B2928743 : Blo 1951435 2928743 := bstep (se 1 (by rfl) ⟨2196557, by rfl⟩ : syracuseStep 2928743 = 4393115) B4393115
theorem B1952495 : Blo 1951435 1952495 := bstep (se 1 (by rfl) ⟨1464371, by rfl⟩ : syracuseStep 1952495 = 2928743) B2928743
theorem B2928749 : Blo 1951435 2928749 := bbase (se 3 (by rfl) ⟨549140, by rfl⟩ : syracuseStep 2928749 = 1098281) (by norm_num)
theorem B1952499 : Blo 1951435 1952499 := bstep (se 1 (by rfl) ⟨1464374, by rfl⟩ : syracuseStep 1952499 = 2928749) B2928749
theorem B4393133 : Blo 1951435 4393133 := bbase (se 3 (by rfl) ⟨823712, by rfl⟩ : syracuseStep 4393133 = 1647425) (by norm_num)
theorem B2928755 : Blo 1951435 2928755 := bstep (se 1 (by rfl) ⟨2196566, by rfl⟩ : syracuseStep 2928755 = 4393133) B4393133
theorem B1952503 : Blo 1951435 1952503 := bstep (se 1 (by rfl) ⟨1464377, by rfl⟩ : syracuseStep 1952503 = 2928755) B2928755
theorem B3170213 : Blo 1951435 3170213 := bbase (se 4 (by rfl) ⟨297207, by rfl⟩ : syracuseStep 3170213 = 594415) (by norm_num)
theorem B2113475 : Blo 1951435 2113475 := bstep (se 1 (by rfl) ⟨1585106, by rfl⟩ : syracuseStep 2113475 = 3170213) B3170213
theorem B22543733 : Blo 1951435 22543733 := bstep (se 5 (by rfl) ⟨1056737, by rfl⟩ : syracuseStep 22543733 = 2113475) B2113475
theorem B15029155 : Blo 1951435 15029155 := bstep (se 1 (by rfl) ⟨11271866, by rfl⟩ : syracuseStep 15029155 = 22543733) B22543733
theorem B20038873 : Blo 1951435 20038873 := bstep (se 2 (by rfl) ⟨7514577, by rfl⟩ : syracuseStep 20038873 = 15029155) B15029155
theorem B26718497 : Blo 1951435 26718497 := bstep (se 2 (by rfl) ⟨10019436, by rfl⟩ : syracuseStep 26718497 = 20038873) B20038873
theorem B17812331 : Blo 1951435 17812331 := bstep (se 1 (by rfl) ⟨13359248, by rfl⟩ : syracuseStep 17812331 = 26718497) B26718497
theorem B11874887 : Blo 1951435 11874887 := bstep (se 1 (by rfl) ⟨8906165, by rfl⟩ : syracuseStep 11874887 = 17812331) B17812331
theorem B7916591 : Blo 1951435 7916591 := bstep (se 1 (by rfl) ⟨5937443, by rfl⟩ : syracuseStep 7916591 = 11874887) B11874887
theorem B5277727 : Blo 1951435 5277727 := bstep (se 1 (by rfl) ⟨3958295, by rfl⟩ : syracuseStep 5277727 = 7916591) B7916591
theorem B7036969 : Blo 1951435 7036969 := bstep (se 2 (by rfl) ⟨2638863, by rfl⟩ : syracuseStep 7036969 = 5277727) B5277727
theorem B9382625 : Blo 1951435 9382625 := bstep (se 2 (by rfl) ⟨3518484, by rfl⟩ : syracuseStep 9382625 = 7036969) B7036969
theorem B6255083 : Blo 1951435 6255083 := bstep (se 1 (by rfl) ⟨4691312, by rfl⟩ : syracuseStep 6255083 = 9382625) B9382625
theorem B4170055 : Blo 1951435 4170055 := bstep (se 1 (by rfl) ⟨3127541, by rfl⟩ : syracuseStep 4170055 = 6255083) B6255083
theorem B5560073 : Blo 1951435 5560073 := bstep (se 2 (by rfl) ⟨2085027, by rfl⟩ : syracuseStep 5560073 = 4170055) B4170055
theorem B3706715 : Blo 1951435 3706715 := bstep (se 1 (by rfl) ⟨2780036, by rfl⟩ : syracuseStep 3706715 = 5560073) B5560073
theorem B2471143 : Blo 1951435 2471143 := bstep (se 1 (by rfl) ⟨1853357, by rfl⟩ : syracuseStep 2471143 = 3706715) B3706715
theorem B3294857 : Blo 1951435 3294857 := bstep (se 2 (by rfl) ⟨1235571, by rfl⟩ : syracuseStep 3294857 = 2471143) B2471143
theorem B2196571 : Blo 1951435 2196571 := bstep (se 1 (by rfl) ⟨1647428, by rfl⟩ : syracuseStep 2196571 = 3294857) B3294857
theorem B2928761 : Blo 1951435 2928761 := bstep (se 2 (by rfl) ⟨1098285, by rfl⟩ : syracuseStep 2928761 = 2196571) B2196571
theorem B1952507 : Blo 1951435 1952507 := bstep (se 1 (by rfl) ⟨1464380, by rfl⟩ : syracuseStep 1952507 = 2928761) B2928761
theorem B25020373 : Blo 1951435 25020373 := bbase (se 7 (by rfl) ⟨293207, by rfl⟩ : syracuseStep 25020373 = 586415) (by norm_num)
theorem B33360497 : Blo 1951435 33360497 := bstep (se 2 (by rfl) ⟨12510186, by rfl⟩ : syracuseStep 33360497 = 25020373) B25020373
theorem B22240331 : Blo 1951435 22240331 := bstep (se 1 (by rfl) ⟨16680248, by rfl⟩ : syracuseStep 22240331 = 33360497) B33360497
theorem B14826887 : Blo 1951435 14826887 := bstep (se 1 (by rfl) ⟨11120165, by rfl⟩ : syracuseStep 14826887 = 22240331) B22240331
theorem B9884591 : Blo 1951435 9884591 := bstep (se 1 (by rfl) ⟨7413443, by rfl⟩ : syracuseStep 9884591 = 14826887) B14826887
theorem B6589727 : Blo 1951435 6589727 := bstep (se 1 (by rfl) ⟨4942295, by rfl⟩ : syracuseStep 6589727 = 9884591) B9884591
theorem B4393151 : Blo 1951435 4393151 := bstep (se 1 (by rfl) ⟨3294863, by rfl⟩ : syracuseStep 4393151 = 6589727) B6589727
theorem B2928767 : Blo 1951435 2928767 := bstep (se 1 (by rfl) ⟨2196575, by rfl⟩ : syracuseStep 2928767 = 4393151) B4393151
theorem B1952511 : Blo 1951435 1952511 := bstep (se 1 (by rfl) ⟨1464383, by rfl⟩ : syracuseStep 1952511 = 2928767) B2928767
theorem B2928773 : Blo 1951435 2928773 := bbase (se 4 (by rfl) ⟨274572, by rfl⟩ : syracuseStep 2928773 = 549145) (by norm_num)
theorem B1952515 : Blo 1951435 1952515 := bstep (se 1 (by rfl) ⟨1464386, by rfl⟩ : syracuseStep 1952515 = 2928773) B2928773
theorem B3294877 : Blo 1951435 3294877 := bbase (se 3 (by rfl) ⟨617789, by rfl⟩ : syracuseStep 3294877 = 1235579) (by norm_num)
theorem B4393169 : Blo 1951435 4393169 := bstep (se 2 (by rfl) ⟨1647438, by rfl⟩ : syracuseStep 4393169 = 3294877) B3294877
theorem B2928779 : Blo 1951435 2928779 := bstep (se 1 (by rfl) ⟨2196584, by rfl⟩ : syracuseStep 2928779 = 4393169) B4393169
theorem B1952519 : Blo 1951435 1952519 := bstep (se 1 (by rfl) ⟨1464389, by rfl⟩ : syracuseStep 1952519 = 2928779) B2928779
theorem B2196589 : Blo 1951435 2196589 := bbase (se 3 (by rfl) ⟨411860, by rfl⟩ : syracuseStep 2196589 = 823721) (by norm_num)
theorem B2928785 : Blo 1951435 2928785 := bstep (se 2 (by rfl) ⟨1098294, by rfl⟩ : syracuseStep 2928785 = 2196589) B2196589
theorem B1952523 : Blo 1951435 1952523 := bstep (se 1 (by rfl) ⟨1464392, by rfl⟩ : syracuseStep 1952523 = 2928785) B2928785
theorem B6589781 : Blo 1951435 6589781 := bbase (se 11 (by rfl) ⟨4826, by rfl⟩ : syracuseStep 6589781 = 9653) (by norm_num)
theorem B4393187 : Blo 1951435 4393187 := bstep (se 1 (by rfl) ⟨3294890, by rfl⟩ : syracuseStep 4393187 = 6589781) B6589781
theorem B2928791 : Blo 1951435 2928791 := bstep (se 1 (by rfl) ⟨2196593, by rfl⟩ : syracuseStep 2928791 = 4393187) B4393187
theorem B1952527 : Blo 1951435 1952527 := bstep (se 1 (by rfl) ⟨1464395, by rfl⟩ : syracuseStep 1952527 = 2928791) B2928791
theorem B2928797 : Blo 1951435 2928797 := bbase (se 3 (by rfl) ⟨549149, by rfl⟩ : syracuseStep 2928797 = 1098299) (by norm_num)
theorem B1952531 : Blo 1951435 1952531 := bstep (se 1 (by rfl) ⟨1464398, by rfl⟩ : syracuseStep 1952531 = 2928797) B2928797
theorem B4393205 : Blo 1951435 4393205 := bbase (se 5 (by rfl) ⟨205931, by rfl⟩ : syracuseStep 4393205 = 411863) (by norm_num)
theorem B2928803 : Blo 1951435 2928803 := bstep (se 1 (by rfl) ⟨2196602, by rfl⟩ : syracuseStep 2928803 = 4393205) B4393205
theorem B1952535 : Blo 1951435 1952535 := bstep (se 1 (by rfl) ⟨1464401, by rfl⟩ : syracuseStep 1952535 = 2928803) B2928803
theorem B14074165 : Blo 1951435 14074165 := bbase (se 5 (by rfl) ⟨659726, by rfl⟩ : syracuseStep 14074165 = 1319453) (by norm_num)
theorem B18765553 : Blo 1951435 18765553 := bstep (se 2 (by rfl) ⟨7037082, by rfl⟩ : syracuseStep 18765553 = 14074165) B14074165
theorem B25020737 : Blo 1951435 25020737 := bstep (se 2 (by rfl) ⟨9382776, by rfl⟩ : syracuseStep 25020737 = 18765553) B18765553
theorem B16680491 : Blo 1951435 16680491 := bstep (se 1 (by rfl) ⟨12510368, by rfl⟩ : syracuseStep 16680491 = 25020737) B25020737
theorem B11120327 : Blo 1951435 11120327 := bstep (se 1 (by rfl) ⟨8340245, by rfl⟩ : syracuseStep 11120327 = 16680491) B16680491
theorem B7413551 : Blo 1951435 7413551 := bstep (se 1 (by rfl) ⟨5560163, by rfl⟩ : syracuseStep 7413551 = 11120327) B11120327
theorem B4942367 : Blo 1951435 4942367 := bstep (se 1 (by rfl) ⟨3706775, by rfl⟩ : syracuseStep 4942367 = 7413551) B7413551
theorem B3294911 : Blo 1951435 3294911 := bstep (se 1 (by rfl) ⟨2471183, by rfl⟩ : syracuseStep 3294911 = 4942367) B4942367
theorem B2196607 : Blo 1951435 2196607 := bstep (se 1 (by rfl) ⟨1647455, by rfl⟩ : syracuseStep 2196607 = 3294911) B3294911
theorem B2928809 : Blo 1951435 2928809 := bstep (se 2 (by rfl) ⟨1098303, by rfl⟩ : syracuseStep 2928809 = 2196607) B2196607
theorem B1952539 : Blo 1951435 1952539 := bstep (se 1 (by rfl) ⟨1464404, by rfl⟩ : syracuseStep 1952539 = 2928809) B2928809
theorem B3518549 : Blo 1951435 3518549 := bbase (se 8 (by rfl) ⟨20616, by rfl⟩ : syracuseStep 3518549 = 41233) (by norm_num)
theorem B2345699 : Blo 1951435 2345699 := bstep (se 1 (by rfl) ⟨1759274, by rfl⟩ : syracuseStep 2345699 = 3518549) B3518549
theorem B6255197 : Blo 1951435 6255197 := bstep (se 3 (by rfl) ⟨1172849, by rfl⟩ : syracuseStep 6255197 = 2345699) B2345699
theorem B4170131 : Blo 1951435 4170131 := bstep (se 1 (by rfl) ⟨3127598, by rfl⟩ : syracuseStep 4170131 = 6255197) B6255197
theorem B2780087 : Blo 1951435 2780087 := bstep (se 1 (by rfl) ⟨2085065, by rfl⟩ : syracuseStep 2780087 = 4170131) B4170131
theorem B7413565 : Blo 1951435 7413565 := bstep (se 3 (by rfl) ⟨1390043, by rfl⟩ : syracuseStep 7413565 = 2780087) B2780087
theorem B9884753 : Blo 1951435 9884753 := bstep (se 2 (by rfl) ⟨3706782, by rfl⟩ : syracuseStep 9884753 = 7413565) B7413565
theorem B6589835 : Blo 1951435 6589835 := bstep (se 1 (by rfl) ⟨4942376, by rfl⟩ : syracuseStep 6589835 = 9884753) B9884753
theorem B4393223 : Blo 1951435 4393223 := bstep (se 1 (by rfl) ⟨3294917, by rfl⟩ : syracuseStep 4393223 = 6589835) B6589835
theorem B2928815 : Blo 1951435 2928815 := bstep (se 1 (by rfl) ⟨2196611, by rfl⟩ : syracuseStep 2928815 = 4393223) B4393223
theorem B1952543 : Blo 1951435 1952543 := bstep (se 1 (by rfl) ⟨1464407, by rfl⟩ : syracuseStep 1952543 = 2928815) B2928815
theorem B2928821 : Blo 1951435 2928821 := bbase (se 5 (by rfl) ⟨137288, by rfl⟩ : syracuseStep 2928821 = 274577) (by norm_num)
theorem B1952547 : Blo 1951435 1952547 := bstep (se 1 (by rfl) ⟨1464410, by rfl⟩ : syracuseStep 1952547 = 2928821) B2928821
theorem B4942397 : Blo 1951435 4942397 := bbase (se 3 (by rfl) ⟨926699, by rfl⟩ : syracuseStep 4942397 = 1853399) (by norm_num)
theorem B3294931 : Blo 1951435 3294931 := bstep (se 1 (by rfl) ⟨2471198, by rfl⟩ : syracuseStep 3294931 = 4942397) B4942397
theorem B4393241 : Blo 1951435 4393241 := bstep (se 2 (by rfl) ⟨1647465, by rfl⟩ : syracuseStep 4393241 = 3294931) B3294931
theorem B2928827 : Blo 1951435 2928827 := bstep (se 1 (by rfl) ⟨2196620, by rfl⟩ : syracuseStep 2928827 = 4393241) B4393241
theorem B1952551 : Blo 1951435 1952551 := bstep (se 1 (by rfl) ⟨1464413, by rfl⟩ : syracuseStep 1952551 = 2928827) B2928827
theorem B2196625 : Blo 1951435 2196625 := bbase (se 2 (by rfl) ⟨823734, by rfl⟩ : syracuseStep 2196625 = 1647469) (by norm_num)
theorem B2928833 : Blo 1951435 2928833 := bstep (se 2 (by rfl) ⟨1098312, by rfl⟩ : syracuseStep 2928833 = 2196625) B2196625
theorem B1952555 : Blo 1951435 1952555 := bstep (se 1 (by rfl) ⟨1464416, by rfl⟩ : syracuseStep 1952555 = 2928833) B2928833
theorem B3706813 : Blo 1951435 3706813 := bbase (se 3 (by rfl) ⟨695027, by rfl⟩ : syracuseStep 3706813 = 1390055) (by norm_num)
theorem B4942417 : Blo 1951435 4942417 := bstep (se 2 (by rfl) ⟨1853406, by rfl⟩ : syracuseStep 4942417 = 3706813) B3706813
theorem B6589889 : Blo 1951435 6589889 := bstep (se 2 (by rfl) ⟨2471208, by rfl⟩ : syracuseStep 6589889 = 4942417) B4942417
theorem B4393259 : Blo 1951435 4393259 := bstep (se 1 (by rfl) ⟨3294944, by rfl⟩ : syracuseStep 4393259 = 6589889) B6589889
theorem B2928839 : Blo 1951435 2928839 := bstep (se 1 (by rfl) ⟨2196629, by rfl⟩ : syracuseStep 2928839 = 4393259) B4393259
theorem B1952559 : Blo 1951435 1952559 := bstep (se 1 (by rfl) ⟨1464419, by rfl⟩ : syracuseStep 1952559 = 2928839) B2928839
theorem B2928845 : Blo 1951435 2928845 := bbase (se 3 (by rfl) ⟨549158, by rfl⟩ : syracuseStep 2928845 = 1098317) (by norm_num)
theorem B1952563 : Blo 1951435 1952563 := bstep (se 1 (by rfl) ⟨1464422, by rfl⟩ : syracuseStep 1952563 = 2928845) B2928845
theorem B4393277 : Blo 1951435 4393277 := bbase (se 3 (by rfl) ⟨823739, by rfl⟩ : syracuseStep 4393277 = 1647479) (by norm_num)
theorem B2928851 : Blo 1951435 2928851 := bstep (se 1 (by rfl) ⟨2196638, by rfl⟩ : syracuseStep 2928851 = 4393277) B4393277
theorem B1952567 : Blo 1951435 1952567 := bstep (se 1 (by rfl) ⟨1464425, by rfl⟩ : syracuseStep 1952567 = 2928851) B2928851
theorem B3294965 : Blo 1951435 3294965 := bbase (se 5 (by rfl) ⟨154451, by rfl⟩ : syracuseStep 3294965 = 308903) (by norm_num)
theorem B2196643 : Blo 1951435 2196643 := bstep (se 1 (by rfl) ⟨1647482, by rfl⟩ : syracuseStep 2196643 = 3294965) B3294965
theorem B2928857 : Blo 1951435 2928857 := bstep (se 2 (by rfl) ⟨1098321, by rfl⟩ : syracuseStep 2928857 = 2196643) B2196643
theorem B1952571 : Blo 1951435 1952571 := bstep (se 1 (by rfl) ⟨1464428, by rfl⟩ : syracuseStep 1952571 = 2928857) B2928857
theorem B9382949 : Blo 1951435 9382949 := bbase (se 4 (by rfl) ⟨879651, by rfl⟩ : syracuseStep 9382949 = 1759303) (by norm_num)
theorem B6255299 : Blo 1951435 6255299 := bstep (se 1 (by rfl) ⟨4691474, by rfl⟩ : syracuseStep 6255299 = 9382949) B9382949
theorem B4170199 : Blo 1951435 4170199 := bstep (se 1 (by rfl) ⟨3127649, by rfl⟩ : syracuseStep 4170199 = 6255299) B6255299
theorem B5560265 : Blo 1951435 5560265 := bstep (se 2 (by rfl) ⟨2085099, by rfl⟩ : syracuseStep 5560265 = 4170199) B4170199
theorem B14827373 : Blo 1951435 14827373 := bstep (se 3 (by rfl) ⟨2780132, by rfl⟩ : syracuseStep 14827373 = 5560265) B5560265
theorem B9884915 : Blo 1951435 9884915 := bstep (se 1 (by rfl) ⟨7413686, by rfl⟩ : syracuseStep 9884915 = 14827373) B14827373
theorem B6589943 : Blo 1951435 6589943 := bstep (se 1 (by rfl) ⟨4942457, by rfl⟩ : syracuseStep 6589943 = 9884915) B9884915
theorem B4393295 : Blo 1951435 4393295 := bstep (se 1 (by rfl) ⟨3294971, by rfl⟩ : syracuseStep 4393295 = 6589943) B6589943
theorem B2928863 : Blo 1951435 2928863 := bstep (se 1 (by rfl) ⟨2196647, by rfl⟩ : syracuseStep 2928863 = 4393295) B4393295
theorem B1952575 : Blo 1951435 1952575 := bstep (se 1 (by rfl) ⟨1464431, by rfl⟩ : syracuseStep 1952575 = 2928863) B2928863
theorem B2928869 : Blo 1951435 2928869 := bbase (se 4 (by rfl) ⟨274581, by rfl⟩ : syracuseStep 2928869 = 549163) (by norm_num)
theorem B1952579 : Blo 1951435 1952579 := bstep (se 1 (by rfl) ⟨1464434, by rfl⟩ : syracuseStep 1952579 = 2928869) B2928869
theorem B11875349 : Blo 1951435 11875349 := bbase (se 6 (by rfl) ⟨278328, by rfl⟩ : syracuseStep 11875349 = 556657) (by norm_num)
theorem B7916899 : Blo 1951435 7916899 := bstep (se 1 (by rfl) ⟨5937674, by rfl⟩ : syracuseStep 7916899 = 11875349) B11875349
theorem B10555865 : Blo 1951435 10555865 := bstep (se 2 (by rfl) ⟨3958449, by rfl⟩ : syracuseStep 10555865 = 7916899) B7916899
theorem B7037243 : Blo 1951435 7037243 := bstep (se 1 (by rfl) ⟨5277932, by rfl⟩ : syracuseStep 7037243 = 10555865) B10555865
theorem B4691495 : Blo 1951435 4691495 := bstep (se 1 (by rfl) ⟨3518621, by rfl⟩ : syracuseStep 4691495 = 7037243) B7037243
theorem B3127663 : Blo 1951435 3127663 := bstep (se 1 (by rfl) ⟨2345747, by rfl⟩ : syracuseStep 3127663 = 4691495) B4691495
theorem B4170217 : Blo 1951435 4170217 := bstep (se 2 (by rfl) ⟨1563831, by rfl⟩ : syracuseStep 4170217 = 3127663) B3127663
theorem B5560289 : Blo 1951435 5560289 := bstep (se 2 (by rfl) ⟨2085108, by rfl⟩ : syracuseStep 5560289 = 4170217) B4170217
theorem B3706859 : Blo 1951435 3706859 := bstep (se 1 (by rfl) ⟨2780144, by rfl⟩ : syracuseStep 3706859 = 5560289) B5560289
theorem B2471239 : Blo 1951435 2471239 := bstep (se 1 (by rfl) ⟨1853429, by rfl⟩ : syracuseStep 2471239 = 3706859) B3706859
theorem B3294985 : Blo 1951435 3294985 := bstep (se 2 (by rfl) ⟨1235619, by rfl⟩ : syracuseStep 3294985 = 2471239) B2471239
theorem B4393313 : Blo 1951435 4393313 := bstep (se 2 (by rfl) ⟨1647492, by rfl⟩ : syracuseStep 4393313 = 3294985) B3294985
theorem B2928875 : Blo 1951435 2928875 := bstep (se 1 (by rfl) ⟨2196656, by rfl⟩ : syracuseStep 2928875 = 4393313) B4393313
theorem B1952583 : Blo 1951435 1952583 := bstep (se 1 (by rfl) ⟨1464437, by rfl⟩ : syracuseStep 1952583 = 2928875) B2928875
theorem B2196661 : Blo 1951435 2196661 := bbase (se 5 (by rfl) ⟨102968, by rfl⟩ : syracuseStep 2196661 = 205937) (by norm_num)
theorem B2928881 : Blo 1951435 2928881 := bstep (se 2 (by rfl) ⟨1098330, by rfl⟩ : syracuseStep 2928881 = 2196661) B2196661
theorem B1952587 : Blo 1951435 1952587 := bstep (se 1 (by rfl) ⟨1464440, by rfl⟩ : syracuseStep 1952587 = 2928881) B2928881
theorem B2471249 : Blo 1951435 2471249 := bbase (se 2 (by rfl) ⟨926718, by rfl⟩ : syracuseStep 2471249 = 1853437) (by norm_num)
theorem B6589997 : Blo 1951435 6589997 := bstep (se 3 (by rfl) ⟨1235624, by rfl⟩ : syracuseStep 6589997 = 2471249) B2471249
theorem B4393331 : Blo 1951435 4393331 := bstep (se 1 (by rfl) ⟨3294998, by rfl⟩ : syracuseStep 4393331 = 6589997) B6589997
theorem B2928887 : Blo 1951435 2928887 := bstep (se 1 (by rfl) ⟨2196665, by rfl⟩ : syracuseStep 2928887 = 4393331) B4393331
theorem B1952591 : Blo 1951435 1952591 := bstep (se 1 (by rfl) ⟨1464443, by rfl⟩ : syracuseStep 1952591 = 2928887) B2928887
theorem B2928893 : Blo 1951435 2928893 := bbase (se 3 (by rfl) ⟨549167, by rfl⟩ : syracuseStep 2928893 = 1098335) (by norm_num)
theorem B1952595 : Blo 1951435 1952595 := bstep (se 1 (by rfl) ⟨1464446, by rfl⟩ : syracuseStep 1952595 = 2928893) B2928893
theorem B4393349 : Blo 1951435 4393349 := bbase (se 4 (by rfl) ⟨411876, by rfl⟩ : syracuseStep 4393349 = 823753) (by norm_num)
theorem B2928899 : Blo 1951435 2928899 := bstep (se 1 (by rfl) ⟨2196674, by rfl⟩ : syracuseStep 2928899 = 4393349) B4393349
theorem B1952599 : Blo 1951435 1952599 := bstep (se 1 (by rfl) ⟨1464449, by rfl⟩ : syracuseStep 1952599 = 2928899) B2928899
theorem B2780173 : Blo 1951435 2780173 := bbase (se 3 (by rfl) ⟨521282, by rfl⟩ : syracuseStep 2780173 = 1042565) (by norm_num)
theorem B3706897 : Blo 1951435 3706897 := bstep (se 2 (by rfl) ⟨1390086, by rfl⟩ : syracuseStep 3706897 = 2780173) B2780173
theorem B4942529 : Blo 1951435 4942529 := bstep (se 2 (by rfl) ⟨1853448, by rfl⟩ : syracuseStep 4942529 = 3706897) B3706897
theorem B3295019 : Blo 1951435 3295019 := bstep (se 1 (by rfl) ⟨2471264, by rfl⟩ : syracuseStep 3295019 = 4942529) B4942529
theorem B2196679 : Blo 1951435 2196679 := bstep (se 1 (by rfl) ⟨1647509, by rfl⟩ : syracuseStep 2196679 = 3295019) B3295019
theorem B2928905 : Blo 1951435 2928905 := bstep (se 2 (by rfl) ⟨1098339, by rfl⟩ : syracuseStep 2928905 = 2196679) B2196679
theorem B1952603 : Blo 1951435 1952603 := bstep (se 1 (by rfl) ⟨1464452, by rfl⟩ : syracuseStep 1952603 = 2928905) B2928905
theorem B9885077 : Blo 1951435 9885077 := bbase (se 6 (by rfl) ⟨231681, by rfl⟩ : syracuseStep 9885077 = 463363) (by norm_num)
theorem B6590051 : Blo 1951435 6590051 := bstep (se 1 (by rfl) ⟨4942538, by rfl⟩ : syracuseStep 6590051 = 9885077) B9885077
theorem B4393367 : Blo 1951435 4393367 := bstep (se 1 (by rfl) ⟨3295025, by rfl⟩ : syracuseStep 4393367 = 6590051) B6590051
theorem B2928911 : Blo 1951435 2928911 := bstep (se 1 (by rfl) ⟨2196683, by rfl⟩ : syracuseStep 2928911 = 4393367) B4393367
theorem B1952607 : Blo 1951435 1952607 := bstep (se 1 (by rfl) ⟨1464455, by rfl⟩ : syracuseStep 1952607 = 2928911) B2928911
theorem B2928917 : Blo 1951435 2928917 := bbase (se 6 (by rfl) ⟨68646, by rfl⟩ : syracuseStep 2928917 = 137293) (by norm_num)
theorem B1952611 : Blo 1951435 1952611 := bstep (se 1 (by rfl) ⟨1464458, by rfl⟩ : syracuseStep 1952611 = 2928917) B2928917
theorem B9383141 : Blo 1951435 9383141 := bbase (se 4 (by rfl) ⟨879669, by rfl⟩ : syracuseStep 9383141 = 1759339) (by norm_num)
theorem B25021709 : Blo 1951435 25021709 := bstep (se 3 (by rfl) ⟨4691570, by rfl⟩ : syracuseStep 25021709 = 9383141) B9383141
theorem B16681139 : Blo 1951435 16681139 := bstep (se 1 (by rfl) ⟨12510854, by rfl⟩ : syracuseStep 16681139 = 25021709) B25021709
theorem B11120759 : Blo 1951435 11120759 := bstep (se 1 (by rfl) ⟨8340569, by rfl⟩ : syracuseStep 11120759 = 16681139) B16681139
theorem B7413839 : Blo 1951435 7413839 := bstep (se 1 (by rfl) ⟨5560379, by rfl⟩ : syracuseStep 7413839 = 11120759) B11120759
theorem B4942559 : Blo 1951435 4942559 := bstep (se 1 (by rfl) ⟨3706919, by rfl⟩ : syracuseStep 4942559 = 7413839) B7413839
theorem B3295039 : Blo 1951435 3295039 := bstep (se 1 (by rfl) ⟨2471279, by rfl⟩ : syracuseStep 3295039 = 4942559) B4942559
theorem B4393385 : Blo 1951435 4393385 := bstep (se 2 (by rfl) ⟨1647519, by rfl⟩ : syracuseStep 4393385 = 3295039) B3295039
theorem B2928923 : Blo 1951435 2928923 := bstep (se 1 (by rfl) ⟨2196692, by rfl⟩ : syracuseStep 2928923 = 4393385) B4393385
theorem B1952615 : Blo 1951435 1952615 := bstep (se 1 (by rfl) ⟨1464461, by rfl⟩ : syracuseStep 1952615 = 2928923) B2928923
theorem B2196697 : Blo 1951435 2196697 := bbase (se 2 (by rfl) ⟨823761, by rfl⟩ : syracuseStep 2196697 = 1647523) (by norm_num)
theorem B2928929 : Blo 1951435 2928929 := bstep (se 2 (by rfl) ⟨1098348, by rfl⟩ : syracuseStep 2928929 = 2196697) B2196697
theorem B1952619 : Blo 1951435 1952619 := bstep (se 1 (by rfl) ⟨1464464, by rfl⟩ : syracuseStep 1952619 = 2928929) B2928929
theorem B7917061 : Blo 1951435 7917061 := bbase (se 4 (by rfl) ⟨742224, by rfl⟩ : syracuseStep 7917061 = 1484449) (by norm_num)
theorem B10556081 : Blo 1951435 10556081 := bstep (se 2 (by rfl) ⟨3958530, by rfl⟩ : syracuseStep 10556081 = 7917061) B7917061
theorem B7037387 : Blo 1951435 7037387 := bstep (se 1 (by rfl) ⟨5278040, by rfl⟩ : syracuseStep 7037387 = 10556081) B10556081
theorem B4691591 : Blo 1951435 4691591 := bstep (se 1 (by rfl) ⟨3518693, by rfl⟩ : syracuseStep 4691591 = 7037387) B7037387
theorem B3127727 : Blo 1951435 3127727 := bstep (se 1 (by rfl) ⟨2345795, by rfl⟩ : syracuseStep 3127727 = 4691591) B4691591
theorem B2085151 : Blo 1951435 2085151 := bstep (se 1 (by rfl) ⟨1563863, by rfl⟩ : syracuseStep 2085151 = 3127727) B3127727
theorem B2780201 : Blo 1951435 2780201 := bstep (se 2 (by rfl) ⟨1042575, by rfl⟩ : syracuseStep 2780201 = 2085151) B2085151
theorem B7413869 : Blo 1951435 7413869 := bstep (se 3 (by rfl) ⟨1390100, by rfl⟩ : syracuseStep 7413869 = 2780201) B2780201
theorem B4942579 : Blo 1951435 4942579 := bstep (se 1 (by rfl) ⟨3706934, by rfl⟩ : syracuseStep 4942579 = 7413869) B7413869
theorem B6590105 : Blo 1951435 6590105 := bstep (se 2 (by rfl) ⟨2471289, by rfl⟩ : syracuseStep 6590105 = 4942579) B4942579
theorem B4393403 : Blo 1951435 4393403 := bstep (se 1 (by rfl) ⟨3295052, by rfl⟩ : syracuseStep 4393403 = 6590105) B6590105
theorem B2928935 : Blo 1951435 2928935 := bstep (se 1 (by rfl) ⟨2196701, by rfl⟩ : syracuseStep 2928935 = 4393403) B4393403
theorem B1952623 : Blo 1951435 1952623 := bstep (se 1 (by rfl) ⟨1464467, by rfl⟩ : syracuseStep 1952623 = 2928935) B2928935
theorem B2928941 : Blo 1951435 2928941 := bbase (se 3 (by rfl) ⟨549176, by rfl⟩ : syracuseStep 2928941 = 1098353) (by norm_num)
theorem B1952627 : Blo 1951435 1952627 := bstep (se 1 (by rfl) ⟨1464470, by rfl⟩ : syracuseStep 1952627 = 2928941) B2928941
theorem B4393421 : Blo 1951435 4393421 := bbase (se 3 (by rfl) ⟨823766, by rfl⟩ : syracuseStep 4393421 = 1647533) (by norm_num)
theorem B2928947 : Blo 1951435 2928947 := bstep (se 1 (by rfl) ⟨2196710, by rfl⟩ : syracuseStep 2928947 = 4393421) B4393421
theorem B1952631 : Blo 1951435 1952631 := bstep (se 1 (by rfl) ⟨1464473, by rfl⟩ : syracuseStep 1952631 = 2928947) B2928947
theorem B2471305 : Blo 1951435 2471305 := bbase (se 2 (by rfl) ⟨926739, by rfl⟩ : syracuseStep 2471305 = 1853479) (by norm_num)
theorem B3295073 : Blo 1951435 3295073 := bstep (se 2 (by rfl) ⟨1235652, by rfl⟩ : syracuseStep 3295073 = 2471305) B2471305
theorem B2196715 : Blo 1951435 2196715 := bstep (se 1 (by rfl) ⟨1647536, by rfl⟩ : syracuseStep 2196715 = 3295073) B3295073
theorem B2928953 : Blo 1951435 2928953 := bstep (se 2 (by rfl) ⟨1098357, by rfl⟩ : syracuseStep 2928953 = 2196715) B2196715
theorem B1952635 : Blo 1951435 1952635 := bstep (se 1 (by rfl) ⟨1464476, by rfl⟩ : syracuseStep 1952635 = 2928953) B2928953
theorem B17813525 : Blo 1951435 17813525 := bbase (se 6 (by rfl) ⟨417504, by rfl⟩ : syracuseStep 17813525 = 835009) (by norm_num)
theorem B47502733 : Blo 1951435 47502733 := bstep (se 3 (by rfl) ⟨8906762, by rfl⟩ : syracuseStep 47502733 = 17813525) B17813525
theorem B63336977 : Blo 1951435 63336977 := bstep (se 2 (by rfl) ⟨23751366, by rfl⟩ : syracuseStep 63336977 = 47502733) B47502733
theorem B42224651 : Blo 1951435 42224651 := bstep (se 1 (by rfl) ⟨31668488, by rfl⟩ : syracuseStep 42224651 = 63336977) B63336977
theorem B28149767 : Blo 1951435 28149767 := bstep (se 1 (by rfl) ⟨21112325, by rfl⟩ : syracuseStep 28149767 = 42224651) B42224651
theorem B18766511 : Blo 1951435 18766511 := bstep (se 1 (by rfl) ⟨14074883, by rfl⟩ : syracuseStep 18766511 = 28149767) B28149767
theorem B12511007 : Blo 1951435 12511007 := bstep (se 1 (by rfl) ⟨9383255, by rfl⟩ : syracuseStep 12511007 = 18766511) B18766511
theorem B8340671 : Blo 1951435 8340671 := bstep (se 1 (by rfl) ⟨6255503, by rfl⟩ : syracuseStep 8340671 = 12511007) B12511007
theorem B22241789 : Blo 1951435 22241789 := bstep (se 3 (by rfl) ⟨4170335, by rfl⟩ : syracuseStep 22241789 = 8340671) B8340671
theorem B14827859 : Blo 1951435 14827859 := bstep (se 1 (by rfl) ⟨11120894, by rfl⟩ : syracuseStep 14827859 = 22241789) B22241789
theorem B9885239 : Blo 1951435 9885239 := bstep (se 1 (by rfl) ⟨7413929, by rfl⟩ : syracuseStep 9885239 = 14827859) B14827859
theorem B6590159 : Blo 1951435 6590159 := bstep (se 1 (by rfl) ⟨4942619, by rfl⟩ : syracuseStep 6590159 = 9885239) B9885239
theorem B4393439 : Blo 1951435 4393439 := bstep (se 1 (by rfl) ⟨3295079, by rfl⟩ : syracuseStep 4393439 = 6590159) B6590159
theorem B2928959 : Blo 1951435 2928959 := bstep (se 1 (by rfl) ⟨2196719, by rfl⟩ : syracuseStep 2928959 = 4393439) B4393439
theorem B1952639 : Blo 1951435 1952639 := bstep (se 1 (by rfl) ⟨1464479, by rfl⟩ : syracuseStep 1952639 = 2928959) B2928959
theorem B2928965 : Blo 1951435 2928965 := bbase (se 4 (by rfl) ⟨274590, by rfl⟩ : syracuseStep 2928965 = 549181) (by norm_num)
theorem B1952643 : Blo 1951435 1952643 := bstep (se 1 (by rfl) ⟨1464482, by rfl⟩ : syracuseStep 1952643 = 2928965) B2928965
theorem B3295093 : Blo 1951435 3295093 := bbase (se 5 (by rfl) ⟨154457, by rfl⟩ : syracuseStep 3295093 = 308915) (by norm_num)
theorem B4393457 : Blo 1951435 4393457 := bstep (se 2 (by rfl) ⟨1647546, by rfl⟩ : syracuseStep 4393457 = 3295093) B3295093
theorem B2928971 : Blo 1951435 2928971 := bstep (se 1 (by rfl) ⟨2196728, by rfl⟩ : syracuseStep 2928971 = 4393457) B4393457
theorem B1952647 : Blo 1951435 1952647 := bstep (se 1 (by rfl) ⟨1464485, by rfl⟩ : syracuseStep 1952647 = 2928971) B2928971
theorem B2196733 : Blo 1951435 2196733 := bbase (se 3 (by rfl) ⟨411887, by rfl⟩ : syracuseStep 2196733 = 823775) (by norm_num)
theorem B2928977 : Blo 1951435 2928977 := bstep (se 2 (by rfl) ⟨1098366, by rfl⟩ : syracuseStep 2928977 = 2196733) B2196733
theorem B1952651 : Blo 1951435 1952651 := bstep (se 1 (by rfl) ⟨1464488, by rfl⟩ : syracuseStep 1952651 = 2928977) B2928977
theorem B6590213 : Blo 1951435 6590213 := bbase (se 4 (by rfl) ⟨617832, by rfl⟩ : syracuseStep 6590213 = 1235665) (by norm_num)
theorem B4393475 : Blo 1951435 4393475 := bstep (se 1 (by rfl) ⟨3295106, by rfl⟩ : syracuseStep 4393475 = 6590213) B6590213
theorem B2928983 : Blo 1951435 2928983 := bstep (se 1 (by rfl) ⟨2196737, by rfl⟩ : syracuseStep 2928983 = 4393475) B4393475
theorem B1952655 : Blo 1951435 1952655 := bstep (se 1 (by rfl) ⟨1464491, by rfl⟩ : syracuseStep 1952655 = 2928983) B2928983
theorem B2928989 : Blo 1951435 2928989 := bbase (se 3 (by rfl) ⟨549185, by rfl⟩ : syracuseStep 2928989 = 1098371) (by norm_num)
theorem B1952659 : Blo 1951435 1952659 := bstep (se 1 (by rfl) ⟨1464494, by rfl⟩ : syracuseStep 1952659 = 2928989) B2928989
theorem B4393493 : Blo 1951435 4393493 := bbase (se 6 (by rfl) ⟨102972, by rfl⟩ : syracuseStep 4393493 = 205945) (by norm_num)
theorem B2928995 : Blo 1951435 2928995 := bstep (se 1 (by rfl) ⟨2196746, by rfl⟩ : syracuseStep 2928995 = 4393493) B4393493
theorem B1952663 : Blo 1951435 1952663 := bstep (se 1 (by rfl) ⟨1464497, by rfl⟩ : syracuseStep 1952663 = 2928995) B2928995
theorem B7414037 : Blo 1951435 7414037 := bbase (se 6 (by rfl) ⟨173766, by rfl⟩ : syracuseStep 7414037 = 347533) (by norm_num)
theorem B4942691 : Blo 1951435 4942691 := bstep (se 1 (by rfl) ⟨3707018, by rfl⟩ : syracuseStep 4942691 = 7414037) B7414037
theorem B3295127 : Blo 1951435 3295127 := bstep (se 1 (by rfl) ⟨2471345, by rfl⟩ : syracuseStep 3295127 = 4942691) B4942691
theorem B2196751 : Blo 1951435 2196751 := bstep (se 1 (by rfl) ⟨1647563, by rfl⟩ : syracuseStep 2196751 = 3295127) B3295127
theorem B2929001 : Blo 1951435 2929001 := bstep (se 2 (by rfl) ⟨1098375, by rfl⟩ : syracuseStep 2929001 = 2196751) B2196751
theorem B1952667 : Blo 1951435 1952667 := bstep (se 1 (by rfl) ⟨1464500, by rfl⟩ : syracuseStep 1952667 = 2929001) B2929001
theorem B11121077 : Blo 1951435 11121077 := bbase (se 5 (by rfl) ⟨521300, by rfl⟩ : syracuseStep 11121077 = 1042601) (by norm_num)
theorem B7414051 : Blo 1951435 7414051 := bstep (se 1 (by rfl) ⟨5560538, by rfl⟩ : syracuseStep 7414051 = 11121077) B11121077
theorem B9885401 : Blo 1951435 9885401 := bstep (se 2 (by rfl) ⟨3707025, by rfl⟩ : syracuseStep 9885401 = 7414051) B7414051
theorem B6590267 : Blo 1951435 6590267 := bstep (se 1 (by rfl) ⟨4942700, by rfl⟩ : syracuseStep 6590267 = 9885401) B9885401
theorem B4393511 : Blo 1951435 4393511 := bstep (se 1 (by rfl) ⟨3295133, by rfl⟩ : syracuseStep 4393511 = 6590267) B6590267
theorem B2929007 : Blo 1951435 2929007 := bstep (se 1 (by rfl) ⟨2196755, by rfl⟩ : syracuseStep 2929007 = 4393511) B4393511
theorem B1952671 : Blo 1951435 1952671 := bstep (se 1 (by rfl) ⟨1464503, by rfl⟩ : syracuseStep 1952671 = 2929007) B2929007
theorem B2929013 : Blo 1951435 2929013 := bbase (se 5 (by rfl) ⟨137297, by rfl⟩ : syracuseStep 2929013 = 274595) (by norm_num)
theorem B1952675 : Blo 1951435 1952675 := bstep (se 1 (by rfl) ⟨1464506, by rfl⟩ : syracuseStep 1952675 = 2929013) B2929013
theorem B3958645 : Blo 1951435 3958645 := bbase (se 5 (by rfl) ⟨185561, by rfl⟩ : syracuseStep 3958645 = 371123) (by norm_num)
theorem B5278193 : Blo 1951435 5278193 := bstep (se 2 (by rfl) ⟨1979322, by rfl⟩ : syracuseStep 5278193 = 3958645) B3958645
theorem B3518795 : Blo 1951435 3518795 := bstep (se 1 (by rfl) ⟨2639096, by rfl⟩ : syracuseStep 3518795 = 5278193) B5278193
theorem B2345863 : Blo 1951435 2345863 := bstep (se 1 (by rfl) ⟨1759397, by rfl⟩ : syracuseStep 2345863 = 3518795) B3518795
theorem B3127817 : Blo 1951435 3127817 := bstep (se 2 (by rfl) ⟨1172931, by rfl⟩ : syracuseStep 3127817 = 2345863) B2345863
theorem B2085211 : Blo 1951435 2085211 := bstep (se 1 (by rfl) ⟨1563908, by rfl⟩ : syracuseStep 2085211 = 3127817) B3127817
theorem B2780281 : Blo 1951435 2780281 := bstep (se 2 (by rfl) ⟨1042605, by rfl⟩ : syracuseStep 2780281 = 2085211) B2085211
theorem B3707041 : Blo 1951435 3707041 := bstep (se 2 (by rfl) ⟨1390140, by rfl⟩ : syracuseStep 3707041 = 2780281) B2780281
theorem B4942721 : Blo 1951435 4942721 := bstep (se 2 (by rfl) ⟨1853520, by rfl⟩ : syracuseStep 4942721 = 3707041) B3707041
theorem B3295147 : Blo 1951435 3295147 := bstep (se 1 (by rfl) ⟨2471360, by rfl⟩ : syracuseStep 3295147 = 4942721) B4942721
theorem B4393529 : Blo 1951435 4393529 := bstep (se 2 (by rfl) ⟨1647573, by rfl⟩ : syracuseStep 4393529 = 3295147) B3295147
theorem B2929019 : Blo 1951435 2929019 := bstep (se 1 (by rfl) ⟨2196764, by rfl⟩ : syracuseStep 2929019 = 4393529) B4393529
theorem B1952679 : Blo 1951435 1952679 := bstep (se 1 (by rfl) ⟨1464509, by rfl⟩ : syracuseStep 1952679 = 2929019) B2929019
theorem B2196769 : Blo 1951435 2196769 := bbase (se 2 (by rfl) ⟨823788, by rfl⟩ : syracuseStep 2196769 = 1647577) (by norm_num)
theorem B2929025 : Blo 1951435 2929025 := bstep (se 2 (by rfl) ⟨1098384, by rfl⟩ : syracuseStep 2929025 = 2196769) B2196769
theorem B1952683 : Blo 1951435 1952683 := bstep (se 1 (by rfl) ⟨1464512, by rfl⟩ : syracuseStep 1952683 = 2929025) B2929025
theorem B4942741 : Blo 1951435 4942741 := bbase (se 6 (by rfl) ⟨115845, by rfl⟩ : syracuseStep 4942741 = 231691) (by norm_num)
theorem B6590321 : Blo 1951435 6590321 := bstep (se 2 (by rfl) ⟨2471370, by rfl⟩ : syracuseStep 6590321 = 4942741) B4942741
theorem B4393547 : Blo 1951435 4393547 := bstep (se 1 (by rfl) ⟨3295160, by rfl⟩ : syracuseStep 4393547 = 6590321) B6590321
theorem B2929031 : Blo 1951435 2929031 := bstep (se 1 (by rfl) ⟨2196773, by rfl⟩ : syracuseStep 2929031 = 4393547) B4393547
theorem B1952687 : Blo 1951435 1952687 := bstep (se 1 (by rfl) ⟨1464515, by rfl⟩ : syracuseStep 1952687 = 2929031) B2929031
theorem B2929037 : Blo 1951435 2929037 := bbase (se 3 (by rfl) ⟨549194, by rfl⟩ : syracuseStep 2929037 = 1098389) (by norm_num)
theorem B1952691 : Blo 1951435 1952691 := bstep (se 1 (by rfl) ⟨1464518, by rfl⟩ : syracuseStep 1952691 = 2929037) B2929037
theorem B4393565 : Blo 1951435 4393565 := bbase (se 3 (by rfl) ⟨823793, by rfl⟩ : syracuseStep 4393565 = 1647587) (by norm_num)
theorem B2929043 : Blo 1951435 2929043 := bstep (se 1 (by rfl) ⟨2196782, by rfl⟩ : syracuseStep 2929043 = 4393565) B4393565
theorem B1952695 : Blo 1951435 1952695 := bstep (se 1 (by rfl) ⟨1464521, by rfl⟩ : syracuseStep 1952695 = 2929043) B2929043
theorem B3295181 : Blo 1951435 3295181 := bbase (se 3 (by rfl) ⟨617846, by rfl⟩ : syracuseStep 3295181 = 1235693) (by norm_num)
theorem B2196787 : Blo 1951435 2196787 := bstep (se 1 (by rfl) ⟨1647590, by rfl⟩ : syracuseStep 2196787 = 3295181) B3295181
theorem B2929049 : Blo 1951435 2929049 := bstep (se 2 (by rfl) ⟨1098393, by rfl⟩ : syracuseStep 2929049 = 2196787) B2196787
theorem B1952699 : Blo 1951435 1952699 := bstep (se 1 (by rfl) ⟨1464524, by rfl⟩ : syracuseStep 1952699 = 2929049) B2929049
theorem B5938037 : Blo 1951435 5938037 := bbase (se 5 (by rfl) ⟨278345, by rfl⟩ : syracuseStep 5938037 = 556691) (by norm_num)
theorem B3958691 : Blo 1951435 3958691 := bstep (se 1 (by rfl) ⟨2969018, by rfl⟩ : syracuseStep 3958691 = 5938037) B5938037
theorem B10556509 : Blo 1951435 10556509 := bstep (se 3 (by rfl) ⟨1979345, by rfl⟩ : syracuseStep 10556509 = 3958691) B3958691
theorem B14075345 : Blo 1951435 14075345 := bstep (se 2 (by rfl) ⟨5278254, by rfl⟩ : syracuseStep 14075345 = 10556509) B10556509
theorem B9383563 : Blo 1951435 9383563 := bstep (se 1 (by rfl) ⟨7037672, by rfl⟩ : syracuseStep 9383563 = 14075345) B14075345
theorem B12511417 : Blo 1951435 12511417 := bstep (se 2 (by rfl) ⟨4691781, by rfl⟩ : syracuseStep 12511417 = 9383563) B9383563
theorem B16681889 : Blo 1951435 16681889 := bstep (se 2 (by rfl) ⟨6255708, by rfl⟩ : syracuseStep 16681889 = 12511417) B12511417
theorem B11121259 : Blo 1951435 11121259 := bstep (se 1 (by rfl) ⟨8340944, by rfl⟩ : syracuseStep 11121259 = 16681889) B16681889
theorem B14828345 : Blo 1951435 14828345 := bstep (se 2 (by rfl) ⟨5560629, by rfl⟩ : syracuseStep 14828345 = 11121259) B11121259
theorem B9885563 : Blo 1951435 9885563 := bstep (se 1 (by rfl) ⟨7414172, by rfl⟩ : syracuseStep 9885563 = 14828345) B14828345
theorem B6590375 : Blo 1951435 6590375 := bstep (se 1 (by rfl) ⟨4942781, by rfl⟩ : syracuseStep 6590375 = 9885563) B9885563
theorem B4393583 : Blo 1951435 4393583 := bstep (se 1 (by rfl) ⟨3295187, by rfl⟩ : syracuseStep 4393583 = 6590375) B6590375
theorem B2929055 : Blo 1951435 2929055 := bstep (se 1 (by rfl) ⟨2196791, by rfl⟩ : syracuseStep 2929055 = 4393583) B4393583
theorem B1952703 : Blo 1951435 1952703 := bstep (se 1 (by rfl) ⟨1464527, by rfl⟩ : syracuseStep 1952703 = 2929055) B2929055
theorem B2929061 : Blo 1951435 2929061 := bbase (se 4 (by rfl) ⟨274599, by rfl⟩ : syracuseStep 2929061 = 549199) (by norm_num)
theorem B1952707 : Blo 1951435 1952707 := bstep (se 1 (by rfl) ⟨1464530, by rfl⟩ : syracuseStep 1952707 = 2929061) B2929061
theorem B2471401 : Blo 1951435 2471401 := bbase (se 2 (by rfl) ⟨926775, by rfl⟩ : syracuseStep 2471401 = 1853551) (by norm_num)
theorem B3295201 : Blo 1951435 3295201 := bstep (se 2 (by rfl) ⟨1235700, by rfl⟩ : syracuseStep 3295201 = 2471401) B2471401
theorem B4393601 : Blo 1951435 4393601 := bstep (se 2 (by rfl) ⟨1647600, by rfl⟩ : syracuseStep 4393601 = 3295201) B3295201
theorem B2929067 : Blo 1951435 2929067 := bstep (se 1 (by rfl) ⟨2196800, by rfl⟩ : syracuseStep 2929067 = 4393601) B4393601
theorem B1952711 : Blo 1951435 1952711 := bstep (se 1 (by rfl) ⟨1464533, by rfl⟩ : syracuseStep 1952711 = 2929067) B2929067
theorem B2196805 : Blo 1951435 2196805 := bbase (se 4 (by rfl) ⟨205950, by rfl⟩ : syracuseStep 2196805 = 411901) (by norm_num)
theorem B2929073 : Blo 1951435 2929073 := bstep (se 2 (by rfl) ⟨1098402, by rfl⟩ : syracuseStep 2929073 = 2196805) B2196805
theorem B1952715 : Blo 1951435 1952715 := bstep (se 1 (by rfl) ⟨1464536, by rfl⟩ : syracuseStep 1952715 = 2929073) B2929073
theorem B3707117 : Blo 1951435 3707117 := bbase (se 3 (by rfl) ⟨695084, by rfl⟩ : syracuseStep 3707117 = 1390169) (by norm_num)
theorem B2471411 : Blo 1951435 2471411 := bstep (se 1 (by rfl) ⟨1853558, by rfl⟩ : syracuseStep 2471411 = 3707117) B3707117
theorem B6590429 : Blo 1951435 6590429 := bstep (se 3 (by rfl) ⟨1235705, by rfl⟩ : syracuseStep 6590429 = 2471411) B2471411
theorem B4393619 : Blo 1951435 4393619 := bstep (se 1 (by rfl) ⟨3295214, by rfl⟩ : syracuseStep 4393619 = 6590429) B6590429
theorem B2929079 : Blo 1951435 2929079 := bstep (se 1 (by rfl) ⟨2196809, by rfl⟩ : syracuseStep 2929079 = 4393619) B4393619
theorem B1952719 : Blo 1951435 1952719 := bstep (se 1 (by rfl) ⟨1464539, by rfl⟩ : syracuseStep 1952719 = 2929079) B2929079
theorem B2929085 : Blo 1951435 2929085 := bbase (se 3 (by rfl) ⟨549203, by rfl⟩ : syracuseStep 2929085 = 1098407) (by norm_num)
theorem B1952723 : Blo 1951435 1952723 := bstep (se 1 (by rfl) ⟨1464542, by rfl⟩ : syracuseStep 1952723 = 2929085) B2929085
theorem B4393637 : Blo 1951435 4393637 := bbase (se 4 (by rfl) ⟨411903, by rfl⟩ : syracuseStep 4393637 = 823807) (by norm_num)
theorem B2929091 : Blo 1951435 2929091 := bstep (se 1 (by rfl) ⟨2196818, by rfl⟩ : syracuseStep 2929091 = 4393637) B4393637
theorem B1952727 : Blo 1951435 1952727 := bstep (se 1 (by rfl) ⟨1464545, by rfl⟩ : syracuseStep 1952727 = 2929091) B2929091
theorem B4942853 : Blo 1951435 4942853 := bbase (se 4 (by rfl) ⟨463392, by rfl⟩ : syracuseStep 4942853 = 926785) (by norm_num)
theorem B3295235 : Blo 1951435 3295235 := bstep (se 1 (by rfl) ⟨2471426, by rfl⟩ : syracuseStep 3295235 = 4942853) B4942853
theorem B2196823 : Blo 1951435 2196823 := bstep (se 1 (by rfl) ⟨1647617, by rfl⟩ : syracuseStep 2196823 = 3295235) B3295235
theorem B2929097 : Blo 1951435 2929097 := bstep (se 2 (by rfl) ⟨1098411, by rfl⟩ : syracuseStep 2929097 = 2196823) B2196823
theorem B1952731 : Blo 1951435 1952731 := bstep (se 1 (by rfl) ⟨1464548, by rfl⟩ : syracuseStep 1952731 = 2929097) B2929097
theorem B4170541 : Blo 1951435 4170541 := bbase (se 3 (by rfl) ⟨781976, by rfl⟩ : syracuseStep 4170541 = 1563953) (by norm_num)
theorem B5560721 : Blo 1951435 5560721 := bstep (se 2 (by rfl) ⟨2085270, by rfl⟩ : syracuseStep 5560721 = 4170541) B4170541
theorem B3707147 : Blo 1951435 3707147 := bstep (se 1 (by rfl) ⟨2780360, by rfl⟩ : syracuseStep 3707147 = 5560721) B5560721
theorem B9885725 : Blo 1951435 9885725 := bstep (se 3 (by rfl) ⟨1853573, by rfl⟩ : syracuseStep 9885725 = 3707147) B3707147
theorem B6590483 : Blo 1951435 6590483 := bstep (se 1 (by rfl) ⟨4942862, by rfl⟩ : syracuseStep 6590483 = 9885725) B9885725
theorem B4393655 : Blo 1951435 4393655 := bstep (se 1 (by rfl) ⟨3295241, by rfl⟩ : syracuseStep 4393655 = 6590483) B6590483
theorem B2929103 : Blo 1951435 2929103 := bstep (se 1 (by rfl) ⟨2196827, by rfl⟩ : syracuseStep 2929103 = 4393655) B4393655
theorem B1952735 : Blo 1951435 1952735 := bstep (se 1 (by rfl) ⟨1464551, by rfl⟩ : syracuseStep 1952735 = 2929103) B2929103
theorem B2929109 : Blo 1951435 2929109 := bbase (se 7 (by rfl) ⟨34325, by rfl⟩ : syracuseStep 2929109 = 68651) (by norm_num)
theorem B1952739 : Blo 1951435 1952739 := bstep (se 1 (by rfl) ⟨1464554, by rfl⟩ : syracuseStep 1952739 = 2929109) B2929109
theorem B7414325 : Blo 1951435 7414325 := bbase (se 5 (by rfl) ⟨347546, by rfl⟩ : syracuseStep 7414325 = 695093) (by norm_num)
theorem B4942883 : Blo 1951435 4942883 := bstep (se 1 (by rfl) ⟨3707162, by rfl⟩ : syracuseStep 4942883 = 7414325) B7414325
theorem B3295255 : Blo 1951435 3295255 := bstep (se 1 (by rfl) ⟨2471441, by rfl⟩ : syracuseStep 3295255 = 4942883) B4942883
theorem B4393673 : Blo 1951435 4393673 := bstep (se 2 (by rfl) ⟨1647627, by rfl⟩ : syracuseStep 4393673 = 3295255) B3295255
theorem B2929115 : Blo 1951435 2929115 := bstep (se 1 (by rfl) ⟨2196836, by rfl⟩ : syracuseStep 2929115 = 4393673) B4393673
theorem B1952743 : Blo 1951435 1952743 := bstep (se 1 (by rfl) ⟨1464557, by rfl⟩ : syracuseStep 1952743 = 2929115) B2929115
theorem B2196841 : Blo 1951435 2196841 := bbase (se 2 (by rfl) ⟨823815, by rfl⟩ : syracuseStep 2196841 = 1647631) (by norm_num)
theorem B2929121 : Blo 1951435 2929121 := bstep (se 2 (by rfl) ⟨1098420, by rfl⟩ : syracuseStep 2929121 = 2196841) B2196841
theorem B1952747 : Blo 1951435 1952747 := bstep (se 1 (by rfl) ⟨1464560, by rfl⟩ : syracuseStep 1952747 = 2929121) B2929121
theorem B3958789 : Blo 1951435 3958789 := bbase (se 4 (by rfl) ⟨371136, by rfl⟩ : syracuseStep 3958789 = 742273) (by norm_num)
theorem B5278385 : Blo 1951435 5278385 := bstep (se 2 (by rfl) ⟨1979394, by rfl⟩ : syracuseStep 5278385 = 3958789) B3958789
theorem B14075693 : Blo 1951435 14075693 := bstep (se 3 (by rfl) ⟨2639192, by rfl⟩ : syracuseStep 14075693 = 5278385) B5278385
theorem B9383795 : Blo 1951435 9383795 := bstep (se 1 (by rfl) ⟨7037846, by rfl⟩ : syracuseStep 9383795 = 14075693) B14075693
theorem B6255863 : Blo 1951435 6255863 := bstep (se 1 (by rfl) ⟨4691897, by rfl⟩ : syracuseStep 6255863 = 9383795) B9383795
theorem B4170575 : Blo 1951435 4170575 := bstep (se 1 (by rfl) ⟨3127931, by rfl⟩ : syracuseStep 4170575 = 6255863) B6255863
theorem B11121533 : Blo 1951435 11121533 := bstep (se 3 (by rfl) ⟨2085287, by rfl⟩ : syracuseStep 11121533 = 4170575) B4170575
theorem B7414355 : Blo 1951435 7414355 := bstep (se 1 (by rfl) ⟨5560766, by rfl⟩ : syracuseStep 7414355 = 11121533) B11121533
theorem B4942903 : Blo 1951435 4942903 := bstep (se 1 (by rfl) ⟨3707177, by rfl⟩ : syracuseStep 4942903 = 7414355) B7414355
theorem B6590537 : Blo 1951435 6590537 := bstep (se 2 (by rfl) ⟨2471451, by rfl⟩ : syracuseStep 6590537 = 4942903) B4942903
theorem B4393691 : Blo 1951435 4393691 := bstep (se 1 (by rfl) ⟨3295268, by rfl⟩ : syracuseStep 4393691 = 6590537) B6590537
theorem B2929127 : Blo 1951435 2929127 := bstep (se 1 (by rfl) ⟨2196845, by rfl⟩ : syracuseStep 2929127 = 4393691) B4393691
theorem B1952751 : Blo 1951435 1952751 := bstep (se 1 (by rfl) ⟨1464563, by rfl⟩ : syracuseStep 1952751 = 2929127) B2929127
theorem B2929133 : Blo 1951435 2929133 := bbase (se 3 (by rfl) ⟨549212, by rfl⟩ : syracuseStep 2929133 = 1098425) (by norm_num)
theorem B1952755 : Blo 1951435 1952755 := bstep (se 1 (by rfl) ⟨1464566, by rfl⟩ : syracuseStep 1952755 = 2929133) B2929133
theorem B4393709 : Blo 1951435 4393709 := bbase (se 3 (by rfl) ⟨823820, by rfl⟩ : syracuseStep 4393709 = 1647641) (by norm_num)
theorem B2929139 : Blo 1951435 2929139 := bstep (se 1 (by rfl) ⟨2196854, by rfl⟩ : syracuseStep 2929139 = 4393709) B4393709
theorem B1952759 : Blo 1951435 1952759 := bstep (se 1 (by rfl) ⟨1464569, by rfl⟩ : syracuseStep 1952759 = 2929139) B2929139
theorem B2085301 : Blo 1951435 2085301 := bbase (se 5 (by rfl) ⟨97748, by rfl⟩ : syracuseStep 2085301 = 195497) (by norm_num)
theorem B2780401 : Blo 1951435 2780401 := bstep (se 2 (by rfl) ⟨1042650, by rfl⟩ : syracuseStep 2780401 = 2085301) B2085301
theorem B3707201 : Blo 1951435 3707201 := bstep (se 2 (by rfl) ⟨1390200, by rfl⟩ : syracuseStep 3707201 = 2780401) B2780401
theorem B2471467 : Blo 1951435 2471467 := bstep (se 1 (by rfl) ⟨1853600, by rfl⟩ : syracuseStep 2471467 = 3707201) B3707201
theorem B3295289 : Blo 1951435 3295289 := bstep (se 2 (by rfl) ⟨1235733, by rfl⟩ : syracuseStep 3295289 = 2471467) B2471467
theorem B2196859 : Blo 1951435 2196859 := bstep (se 1 (by rfl) ⟨1647644, by rfl⟩ : syracuseStep 2196859 = 3295289) B3295289
theorem B2929145 : Blo 1951435 2929145 := bstep (se 2 (by rfl) ⟨1098429, by rfl⟩ : syracuseStep 2929145 = 2196859) B2196859
theorem B1952763 : Blo 1951435 1952763 := bstep (se 1 (by rfl) ⟨1464572, by rfl⟩ : syracuseStep 1952763 = 2929145) B2929145
theorem B2006417 : Blo 1951435 2006417 := bbase (se 2 (by rfl) ⟨752406, by rfl⟩ : syracuseStep 2006417 = 1504813) (by norm_num)
theorem B5350445 : Blo 1951435 5350445 := bstep (se 3 (by rfl) ⟨1003208, by rfl⟩ : syracuseStep 5350445 = 2006417) B2006417
theorem B3566963 : Blo 1951435 3566963 := bstep (se 1 (by rfl) ⟨2675222, by rfl⟩ : syracuseStep 3566963 = 5350445) B5350445
theorem B9511901 : Blo 1951435 9511901 := bstep (se 3 (by rfl) ⟨1783481, by rfl⟩ : syracuseStep 9511901 = 3566963) B3566963
theorem B6341267 : Blo 1951435 6341267 := bstep (se 1 (by rfl) ⟨4755950, by rfl⟩ : syracuseStep 6341267 = 9511901) B9511901
theorem B16910045 : Blo 1951435 16910045 := bstep (se 3 (by rfl) ⟨3170633, by rfl⟩ : syracuseStep 16910045 = 6341267) B6341267
theorem B11273363 : Blo 1951435 11273363 := bstep (se 1 (by rfl) ⟨8455022, by rfl⟩ : syracuseStep 11273363 = 16910045) B16910045
theorem B7515575 : Blo 1951435 7515575 := bstep (se 1 (by rfl) ⟨5636681, by rfl⟩ : syracuseStep 7515575 = 11273363) B11273363
theorem B5010383 : Blo 1951435 5010383 := bstep (se 1 (by rfl) ⟨3757787, by rfl⟩ : syracuseStep 5010383 = 7515575) B7515575
theorem B13361021 : Blo 1951435 13361021 := bstep (se 3 (by rfl) ⟨2505191, by rfl⟩ : syracuseStep 13361021 = 5010383) B5010383
theorem B8907347 : Blo 1951435 8907347 := bstep (se 1 (by rfl) ⟨6680510, by rfl⟩ : syracuseStep 8907347 = 13361021) B13361021
theorem B5938231 : Blo 1951435 5938231 := bstep (se 1 (by rfl) ⟨4453673, by rfl⟩ : syracuseStep 5938231 = 8907347) B8907347
theorem B7917641 : Blo 1951435 7917641 := bstep (se 2 (by rfl) ⟨2969115, by rfl⟩ : syracuseStep 7917641 = 5938231) B5938231
theorem B5278427 : Blo 1951435 5278427 := bstep (se 1 (by rfl) ⟨3958820, by rfl⟩ : syracuseStep 5278427 = 7917641) B7917641
theorem B56303221 : Blo 1951435 56303221 := bstep (se 5 (by rfl) ⟨2639213, by rfl⟩ : syracuseStep 56303221 = 5278427) B5278427
theorem B75070961 : Blo 1951435 75070961 := bstep (se 2 (by rfl) ⟨28151610, by rfl⟩ : syracuseStep 75070961 = 56303221) B56303221
theorem B50047307 : Blo 1951435 50047307 := bstep (se 1 (by rfl) ⟨37535480, by rfl⟩ : syracuseStep 50047307 = 75070961) B75070961
theorem B33364871 : Blo 1951435 33364871 := bstep (se 1 (by rfl) ⟨25023653, by rfl⟩ : syracuseStep 33364871 = 50047307) B50047307
theorem B22243247 : Blo 1951435 22243247 := bstep (se 1 (by rfl) ⟨16682435, by rfl⟩ : syracuseStep 22243247 = 33364871) B33364871
theorem B14828831 : Blo 1951435 14828831 := bstep (se 1 (by rfl) ⟨11121623, by rfl⟩ : syracuseStep 14828831 = 22243247) B22243247
theorem B9885887 : Blo 1951435 9885887 := bstep (se 1 (by rfl) ⟨7414415, by rfl⟩ : syracuseStep 9885887 = 14828831) B14828831
theorem B6590591 : Blo 1951435 6590591 := bstep (se 1 (by rfl) ⟨4942943, by rfl⟩ : syracuseStep 6590591 = 9885887) B9885887
theorem B4393727 : Blo 1951435 4393727 := bstep (se 1 (by rfl) ⟨3295295, by rfl⟩ : syracuseStep 4393727 = 6590591) B6590591
theorem B2929151 : Blo 1951435 2929151 := bstep (se 1 (by rfl) ⟨2196863, by rfl⟩ : syracuseStep 2929151 = 4393727) B4393727
theorem B1952767 : Blo 1951435 1952767 := bstep (se 1 (by rfl) ⟨1464575, by rfl⟩ : syracuseStep 1952767 = 2929151) B2929151
theorem B2929157 : Blo 1951435 2929157 := bbase (se 4 (by rfl) ⟨274608, by rfl⟩ : syracuseStep 2929157 = 549217) (by norm_num)
theorem B1952771 : Blo 1951435 1952771 := bstep (se 1 (by rfl) ⟨1464578, by rfl⟩ : syracuseStep 1952771 = 2929157) B2929157
theorem B3295309 : Blo 1951435 3295309 := bbase (se 3 (by rfl) ⟨617870, by rfl⟩ : syracuseStep 3295309 = 1235741) (by norm_num)
theorem B4393745 : Blo 1951435 4393745 := bstep (se 2 (by rfl) ⟨1647654, by rfl⟩ : syracuseStep 4393745 = 3295309) B3295309
theorem B2929163 : Blo 1951435 2929163 := bstep (se 1 (by rfl) ⟨2196872, by rfl⟩ : syracuseStep 2929163 = 4393745) B4393745
theorem B1952775 : Blo 1951435 1952775 := bstep (se 1 (by rfl) ⟨1464581, by rfl⟩ : syracuseStep 1952775 = 2929163) B2929163
theorem B2196877 : Blo 1951435 2196877 := bbase (se 3 (by rfl) ⟨411914, by rfl⟩ : syracuseStep 2196877 = 823829) (by norm_num)
theorem B2929169 : Blo 1951435 2929169 := bstep (se 2 (by rfl) ⟨1098438, by rfl⟩ : syracuseStep 2929169 = 2196877) B2196877
theorem B1952779 : Blo 1951435 1952779 := bstep (se 1 (by rfl) ⟨1464584, by rfl⟩ : syracuseStep 1952779 = 2929169) B2929169
theorem B6590645 : Blo 1951435 6590645 := bbase (se 5 (by rfl) ⟨308936, by rfl⟩ : syracuseStep 6590645 = 617873) (by norm_num)
theorem B4393763 : Blo 1951435 4393763 := bstep (se 1 (by rfl) ⟨3295322, by rfl⟩ : syracuseStep 4393763 = 6590645) B6590645
theorem B2929175 : Blo 1951435 2929175 := bstep (se 1 (by rfl) ⟨2196881, by rfl⟩ : syracuseStep 2929175 = 4393763) B4393763
theorem B1952783 : Blo 1951435 1952783 := bstep (se 1 (by rfl) ⟨1464587, by rfl⟩ : syracuseStep 1952783 = 2929175) B2929175
theorem B2929181 : Blo 1951435 2929181 := bbase (se 3 (by rfl) ⟨549221, by rfl⟩ : syracuseStep 2929181 = 1098443) (by norm_num)
theorem B1952787 : Blo 1951435 1952787 := bstep (se 1 (by rfl) ⟨1464590, by rfl⟩ : syracuseStep 1952787 = 2929181) B2929181
theorem B4393781 : Blo 1951435 4393781 := bbase (se 5 (by rfl) ⟨205958, by rfl⟩ : syracuseStep 4393781 = 411917) (by norm_num)
theorem B2929187 : Blo 1951435 2929187 := bstep (se 1 (by rfl) ⟨2196890, by rfl⟩ : syracuseStep 2929187 = 4393781) B4393781
theorem B1952791 : Blo 1951435 1952791 := bstep (se 1 (by rfl) ⟨1464593, by rfl⟩ : syracuseStep 1952791 = 2929187) B2929187
theorem B5713669 : Blo 1951435 5713669 := bbase (se 4 (by rfl) ⟨535656, by rfl⟩ : syracuseStep 5713669 = 1071313) (by norm_num)
theorem B7618225 : Blo 1951435 7618225 := bstep (se 2 (by rfl) ⟨2856834, by rfl⟩ : syracuseStep 7618225 = 5713669) B5713669
theorem B10157633 : Blo 1951435 10157633 := bstep (se 2 (by rfl) ⟨3809112, by rfl⟩ : syracuseStep 10157633 = 7618225) B7618225
theorem B6771755 : Blo 1951435 6771755 := bstep (se 1 (by rfl) ⟨5078816, by rfl⟩ : syracuseStep 6771755 = 10157633) B10157633
theorem B4514503 : Blo 1951435 4514503 := bstep (se 1 (by rfl) ⟨3385877, by rfl⟩ : syracuseStep 4514503 = 6771755) B6771755
theorem B6019337 : Blo 1951435 6019337 := bstep (se 2 (by rfl) ⟨2257251, by rfl⟩ : syracuseStep 6019337 = 4514503) B4514503
theorem B4012891 : Blo 1951435 4012891 := bstep (se 1 (by rfl) ⟨3009668, by rfl⟩ : syracuseStep 4012891 = 6019337) B6019337
theorem B21402085 : Blo 1951435 21402085 := bstep (se 4 (by rfl) ⟨2006445, by rfl⟩ : syracuseStep 21402085 = 4012891) B4012891
theorem B28536113 : Blo 1951435 28536113 := bstep (se 2 (by rfl) ⟨10701042, by rfl⟩ : syracuseStep 28536113 = 21402085) B21402085
theorem B19024075 : Blo 1951435 19024075 := bstep (se 1 (by rfl) ⟨14268056, by rfl⟩ : syracuseStep 19024075 = 28536113) B28536113
theorem B101461733 : Blo 1951435 101461733 := bstep (se 4 (by rfl) ⟨9512037, by rfl⟩ : syracuseStep 101461733 = 19024075) B19024075
theorem B67641155 : Blo 1951435 67641155 := bstep (se 1 (by rfl) ⟨50730866, by rfl⟩ : syracuseStep 67641155 = 101461733) B101461733
theorem B45094103 : Blo 1951435 45094103 := bstep (se 1 (by rfl) ⟨33820577, by rfl⟩ : syracuseStep 45094103 = 67641155) B67641155
theorem B30062735 : Blo 1951435 30062735 := bstep (se 1 (by rfl) ⟨22547051, by rfl⟩ : syracuseStep 30062735 = 45094103) B45094103
theorem B20041823 : Blo 1951435 20041823 := bstep (se 1 (by rfl) ⟨15031367, by rfl⟩ : syracuseStep 20041823 = 30062735) B30062735
theorem B13361215 : Blo 1951435 13361215 := bstep (se 1 (by rfl) ⟨10020911, by rfl⟩ : syracuseStep 13361215 = 20041823) B20041823
theorem B17814953 : Blo 1951435 17814953 := bstep (se 2 (by rfl) ⟨6680607, by rfl⟩ : syracuseStep 17814953 = 13361215) B13361215
theorem B11876635 : Blo 1951435 11876635 := bstep (se 1 (by rfl) ⟨8907476, by rfl⟩ : syracuseStep 11876635 = 17814953) B17814953
theorem B15835513 : Blo 1951435 15835513 := bstep (se 2 (by rfl) ⟨5938317, by rfl⟩ : syracuseStep 15835513 = 11876635) B11876635
theorem B21114017 : Blo 1951435 21114017 := bstep (se 2 (by rfl) ⟨7917756, by rfl⟩ : syracuseStep 21114017 = 15835513) B15835513
theorem B14076011 : Blo 1951435 14076011 := bstep (se 1 (by rfl) ⟨10557008, by rfl⟩ : syracuseStep 14076011 = 21114017) B21114017
theorem B9384007 : Blo 1951435 9384007 := bstep (se 1 (by rfl) ⟨7038005, by rfl⟩ : syracuseStep 9384007 = 14076011) B14076011
theorem B12512009 : Blo 1951435 12512009 := bstep (se 2 (by rfl) ⟨4692003, by rfl⟩ : syracuseStep 12512009 = 9384007) B9384007
theorem B8341339 : Blo 1951435 8341339 := bstep (se 1 (by rfl) ⟨6256004, by rfl⟩ : syracuseStep 8341339 = 12512009) B12512009
theorem B11121785 : Blo 1951435 11121785 := bstep (se 2 (by rfl) ⟨4170669, by rfl⟩ : syracuseStep 11121785 = 8341339) B8341339
theorem B7414523 : Blo 1951435 7414523 := bstep (se 1 (by rfl) ⟨5560892, by rfl⟩ : syracuseStep 7414523 = 11121785) B11121785
theorem B4943015 : Blo 1951435 4943015 := bstep (se 1 (by rfl) ⟨3707261, by rfl⟩ : syracuseStep 4943015 = 7414523) B7414523
theorem B3295343 : Blo 1951435 3295343 := bstep (se 1 (by rfl) ⟨2471507, by rfl⟩ : syracuseStep 3295343 = 4943015) B4943015
theorem B2196895 : Blo 1951435 2196895 := bstep (se 1 (by rfl) ⟨1647671, by rfl⟩ : syracuseStep 2196895 = 3295343) B3295343
theorem B2929193 : Blo 1951435 2929193 := bstep (se 2 (by rfl) ⟨1098447, by rfl⟩ : syracuseStep 2929193 = 2196895) B2196895
theorem B1952795 : Blo 1951435 1952795 := bstep (se 1 (by rfl) ⟨1464596, by rfl⟩ : syracuseStep 1952795 = 2929193) B2929193
theorem B2969165 : Blo 1951435 2969165 := bbase (se 3 (by rfl) ⟨556718, by rfl⟩ : syracuseStep 2969165 = 1113437) (by norm_num)
theorem B1979443 : Blo 1951435 1979443 := bstep (se 1 (by rfl) ⟨1484582, by rfl⟩ : syracuseStep 1979443 = 2969165) B2969165
theorem B10557029 : Blo 1951435 10557029 := bstep (se 4 (by rfl) ⟨989721, by rfl⟩ : syracuseStep 10557029 = 1979443) B1979443
theorem B7038019 : Blo 1951435 7038019 := bstep (se 1 (by rfl) ⟨5278514, by rfl⟩ : syracuseStep 7038019 = 10557029) B10557029
theorem B9384025 : Blo 1951435 9384025 := bstep (se 2 (by rfl) ⟨3519009, by rfl⟩ : syracuseStep 9384025 = 7038019) B7038019
theorem B12512033 : Blo 1951435 12512033 := bstep (se 2 (by rfl) ⟨4692012, by rfl⟩ : syracuseStep 12512033 = 9384025) B9384025
theorem B8341355 : Blo 1951435 8341355 := bstep (se 1 (by rfl) ⟨6256016, by rfl⟩ : syracuseStep 8341355 = 12512033) B12512033
theorem B5560903 : Blo 1951435 5560903 := bstep (se 1 (by rfl) ⟨4170677, by rfl⟩ : syracuseStep 5560903 = 8341355) B8341355
theorem B7414537 : Blo 1951435 7414537 := bstep (se 2 (by rfl) ⟨2780451, by rfl⟩ : syracuseStep 7414537 = 5560903) B5560903
theorem B9886049 : Blo 1951435 9886049 := bstep (se 2 (by rfl) ⟨3707268, by rfl⟩ : syracuseStep 9886049 = 7414537) B7414537
theorem B6590699 : Blo 1951435 6590699 := bstep (se 1 (by rfl) ⟨4943024, by rfl⟩ : syracuseStep 6590699 = 9886049) B9886049
theorem B4393799 : Blo 1951435 4393799 := bstep (se 1 (by rfl) ⟨3295349, by rfl⟩ : syracuseStep 4393799 = 6590699) B6590699
theorem B2929199 : Blo 1951435 2929199 := bstep (se 1 (by rfl) ⟨2196899, by rfl⟩ : syracuseStep 2929199 = 4393799) B4393799
theorem B1952799 : Blo 1951435 1952799 := bstep (se 1 (by rfl) ⟨1464599, by rfl⟩ : syracuseStep 1952799 = 2929199) B2929199
theorem B2929205 : Blo 1951435 2929205 := bbase (se 5 (by rfl) ⟨137306, by rfl⟩ : syracuseStep 2929205 = 274613) (by norm_num)
theorem B1952803 : Blo 1951435 1952803 := bstep (se 1 (by rfl) ⟨1464602, by rfl⟩ : syracuseStep 1952803 = 2929205) B2929205
theorem B4943045 : Blo 1951435 4943045 := bbase (se 4 (by rfl) ⟨463410, by rfl⟩ : syracuseStep 4943045 = 926821) (by norm_num)
theorem B3295363 : Blo 1951435 3295363 := bstep (se 1 (by rfl) ⟨2471522, by rfl⟩ : syracuseStep 3295363 = 4943045) B4943045
theorem B4393817 : Blo 1951435 4393817 := bstep (se 2 (by rfl) ⟨1647681, by rfl⟩ : syracuseStep 4393817 = 3295363) B3295363
theorem B2929211 : Blo 1951435 2929211 := bstep (se 1 (by rfl) ⟨2196908, by rfl⟩ : syracuseStep 2929211 = 4393817) B4393817
theorem B1952807 : Blo 1951435 1952807 := bstep (se 1 (by rfl) ⟨1464605, by rfl⟩ : syracuseStep 1952807 = 2929211) B2929211
theorem B2196913 : Blo 1951435 2196913 := bbase (se 2 (by rfl) ⟨823842, by rfl⟩ : syracuseStep 2196913 = 1647685) (by norm_num)
theorem B2929217 : Blo 1951435 2929217 := bstep (se 2 (by rfl) ⟨1098456, by rfl⟩ : syracuseStep 2929217 = 2196913) B2196913
theorem B1952811 : Blo 1951435 1952811 := bstep (se 1 (by rfl) ⟨1464608, by rfl⟩ : syracuseStep 1952811 = 2929217) B2929217
theorem B5560949 : Blo 1951435 5560949 := bbase (se 5 (by rfl) ⟨260669, by rfl⟩ : syracuseStep 5560949 = 521339) (by norm_num)
theorem B3707299 : Blo 1951435 3707299 := bstep (se 1 (by rfl) ⟨2780474, by rfl⟩ : syracuseStep 3707299 = 5560949) B5560949
theorem B4943065 : Blo 1951435 4943065 := bstep (se 2 (by rfl) ⟨1853649, by rfl⟩ : syracuseStep 4943065 = 3707299) B3707299
theorem B6590753 : Blo 1951435 6590753 := bstep (se 2 (by rfl) ⟨2471532, by rfl⟩ : syracuseStep 6590753 = 4943065) B4943065
theorem B4393835 : Blo 1951435 4393835 := bstep (se 1 (by rfl) ⟨3295376, by rfl⟩ : syracuseStep 4393835 = 6590753) B6590753
theorem B2929223 : Blo 1951435 2929223 := bstep (se 1 (by rfl) ⟨2196917, by rfl⟩ : syracuseStep 2929223 = 4393835) B4393835
theorem B1952815 : Blo 1951435 1952815 := bstep (se 1 (by rfl) ⟨1464611, by rfl⟩ : syracuseStep 1952815 = 2929223) B2929223
theorem B2929229 : Blo 1951435 2929229 := bbase (se 3 (by rfl) ⟨549230, by rfl⟩ : syracuseStep 2929229 = 1098461) (by norm_num)
theorem B1952819 : Blo 1951435 1952819 := bstep (se 1 (by rfl) ⟨1464614, by rfl⟩ : syracuseStep 1952819 = 2929229) B2929229
theorem B4393853 : Blo 1951435 4393853 := bbase (se 3 (by rfl) ⟨823847, by rfl⟩ : syracuseStep 4393853 = 1647695) (by norm_num)
theorem B2929235 : Blo 1951435 2929235 := bstep (se 1 (by rfl) ⟨2196926, by rfl⟩ : syracuseStep 2929235 = 4393853) B4393853
theorem B1952823 : Blo 1951435 1952823 := bstep (se 1 (by rfl) ⟨1464617, by rfl⟩ : syracuseStep 1952823 = 2929235) B2929235
theorem B3295397 : Blo 1951435 3295397 := bbase (se 4 (by rfl) ⟨308943, by rfl⟩ : syracuseStep 3295397 = 617887) (by norm_num)
theorem B2196931 : Blo 1951435 2196931 := bstep (se 1 (by rfl) ⟨1647698, by rfl⟩ : syracuseStep 2196931 = 3295397) B3295397
theorem B2929241 : Blo 1951435 2929241 := bstep (se 2 (by rfl) ⟨1098465, by rfl⟩ : syracuseStep 2929241 = 2196931) B2196931
theorem B1952827 : Blo 1951435 1952827 := bstep (se 1 (by rfl) ⟨1464620, by rfl⟩ : syracuseStep 1952827 = 2929241) B2929241
theorem B2085373 : Blo 1951435 2085373 := bbase (se 3 (by rfl) ⟨391007, by rfl⟩ : syracuseStep 2085373 = 782015) (by norm_num)
theorem B2780497 : Blo 1951435 2780497 := bstep (se 2 (by rfl) ⟨1042686, by rfl⟩ : syracuseStep 2780497 = 2085373) B2085373
theorem B14829317 : Blo 1951435 14829317 := bstep (se 4 (by rfl) ⟨1390248, by rfl⟩ : syracuseStep 14829317 = 2780497) B2780497
theorem B9886211 : Blo 1951435 9886211 := bstep (se 1 (by rfl) ⟨7414658, by rfl⟩ : syracuseStep 9886211 = 14829317) B14829317
theorem B6590807 : Blo 1951435 6590807 := bstep (se 1 (by rfl) ⟨4943105, by rfl⟩ : syracuseStep 6590807 = 9886211) B9886211
theorem B4393871 : Blo 1951435 4393871 := bstep (se 1 (by rfl) ⟨3295403, by rfl⟩ : syracuseStep 4393871 = 6590807) B6590807
theorem B2929247 : Blo 1951435 2929247 := bstep (se 1 (by rfl) ⟨2196935, by rfl⟩ : syracuseStep 2929247 = 4393871) B4393871
theorem B1952831 : Blo 1951435 1952831 := bstep (se 1 (by rfl) ⟨1464623, by rfl⟩ : syracuseStep 1952831 = 2929247) B2929247
theorem B2929253 : Blo 1951435 2929253 := bbase (se 4 (by rfl) ⟨274617, by rfl⟩ : syracuseStep 2929253 = 549235) (by norm_num)
theorem B1952835 : Blo 1951435 1952835 := bstep (se 1 (by rfl) ⟨1464626, by rfl⟩ : syracuseStep 1952835 = 2929253) B2929253
theorem B2780509 : Blo 1951435 2780509 := bbase (se 3 (by rfl) ⟨521345, by rfl⟩ : syracuseStep 2780509 = 1042691) (by norm_num)
theorem B3707345 : Blo 1951435 3707345 := bstep (se 2 (by rfl) ⟨1390254, by rfl⟩ : syracuseStep 3707345 = 2780509) B2780509
theorem B2471563 : Blo 1951435 2471563 := bstep (se 1 (by rfl) ⟨1853672, by rfl⟩ : syracuseStep 2471563 = 3707345) B3707345
theorem B3295417 : Blo 1951435 3295417 := bstep (se 2 (by rfl) ⟨1235781, by rfl⟩ : syracuseStep 3295417 = 2471563) B2471563
theorem B4393889 : Blo 1951435 4393889 := bstep (se 2 (by rfl) ⟨1647708, by rfl⟩ : syracuseStep 4393889 = 3295417) B3295417
theorem B2929259 : Blo 1951435 2929259 := bstep (se 1 (by rfl) ⟨2196944, by rfl⟩ : syracuseStep 2929259 = 4393889) B4393889
theorem B1952839 : Blo 1951435 1952839 := bstep (se 1 (by rfl) ⟨1464629, by rfl⟩ : syracuseStep 1952839 = 2929259) B2929259
theorem B2196949 : Blo 1951435 2196949 := bbase (se 7 (by rfl) ⟨25745, by rfl⟩ : syracuseStep 2196949 = 51491) (by norm_num)
theorem B2929265 : Blo 1951435 2929265 := bstep (se 2 (by rfl) ⟨1098474, by rfl⟩ : syracuseStep 2929265 = 2196949) B2196949
theorem B1952843 : Blo 1951435 1952843 := bstep (se 1 (by rfl) ⟨1464632, by rfl⟩ : syracuseStep 1952843 = 2929265) B2929265
theorem B2471573 : Blo 1951435 2471573 := bbase (se 6 (by rfl) ⟨57927, by rfl⟩ : syracuseStep 2471573 = 115855) (by norm_num)
theorem B6590861 : Blo 1951435 6590861 := bstep (se 3 (by rfl) ⟨1235786, by rfl⟩ : syracuseStep 6590861 = 2471573) B2471573
theorem B4393907 : Blo 1951435 4393907 := bstep (se 1 (by rfl) ⟨3295430, by rfl⟩ : syracuseStep 4393907 = 6590861) B6590861
theorem B2929271 : Blo 1951435 2929271 := bstep (se 1 (by rfl) ⟨2196953, by rfl⟩ : syracuseStep 2929271 = 4393907) B4393907
theorem B1952847 : Blo 1951435 1952847 := bstep (se 1 (by rfl) ⟨1464635, by rfl⟩ : syracuseStep 1952847 = 2929271) B2929271
theorem B2929277 : Blo 1951435 2929277 := bbase (se 3 (by rfl) ⟨549239, by rfl⟩ : syracuseStep 2929277 = 1098479) (by norm_num)
theorem B1952851 : Blo 1951435 1952851 := bstep (se 1 (by rfl) ⟨1464638, by rfl⟩ : syracuseStep 1952851 = 2929277) B2929277
theorem B4393925 : Blo 1951435 4393925 := bbase (se 4 (by rfl) ⟨411930, by rfl⟩ : syracuseStep 4393925 = 823861) (by norm_num)
theorem B2929283 : Blo 1951435 2929283 := bstep (se 1 (by rfl) ⟨2196962, by rfl⟩ : syracuseStep 2929283 = 4393925) B4393925
theorem B1952855 : Blo 1951435 1952855 := bstep (se 1 (by rfl) ⟨1464641, by rfl⟩ : syracuseStep 1952855 = 2929283) B2929283
theorem B5713861 : Blo 1951435 5713861 := bbase (se 4 (by rfl) ⟨535674, by rfl⟩ : syracuseStep 5713861 = 1071349) (by norm_num)
theorem B7618481 : Blo 1951435 7618481 := bstep (se 2 (by rfl) ⟨2856930, by rfl⟩ : syracuseStep 7618481 = 5713861) B5713861
theorem B5078987 : Blo 1951435 5078987 := bstep (se 1 (by rfl) ⟨3809240, by rfl⟩ : syracuseStep 5078987 = 7618481) B7618481
theorem B3385991 : Blo 1951435 3385991 := bstep (se 1 (by rfl) ⟨2539493, by rfl⟩ : syracuseStep 3385991 = 5078987) B5078987
theorem B2257327 : Blo 1951435 2257327 := bstep (se 1 (by rfl) ⟨1692995, by rfl⟩ : syracuseStep 2257327 = 3385991) B3385991
theorem B12039077 : Blo 1951435 12039077 := bstep (se 4 (by rfl) ⟨1128663, by rfl⟩ : syracuseStep 12039077 = 2257327) B2257327
theorem B8026051 : Blo 1951435 8026051 := bstep (se 1 (by rfl) ⟨6019538, by rfl⟩ : syracuseStep 8026051 = 12039077) B12039077
theorem B10701401 : Blo 1951435 10701401 := bstep (se 2 (by rfl) ⟨4013025, by rfl⟩ : syracuseStep 10701401 = 8026051) B8026051
theorem B28537069 : Blo 1951435 28537069 := bstep (se 3 (by rfl) ⟨5350700, by rfl⟩ : syracuseStep 28537069 = 10701401) B10701401
theorem B38049425 : Blo 1951435 38049425 := bstep (se 2 (by rfl) ⟨14268534, by rfl⟩ : syracuseStep 38049425 = 28537069) B28537069
theorem B25366283 : Blo 1951435 25366283 := bstep (se 1 (by rfl) ⟨19024712, by rfl⟩ : syracuseStep 25366283 = 38049425) B38049425
theorem B16910855 : Blo 1951435 16910855 := bstep (se 1 (by rfl) ⟨12683141, by rfl⟩ : syracuseStep 16910855 = 25366283) B25366283
theorem B11273903 : Blo 1951435 11273903 := bstep (se 1 (by rfl) ⟨8455427, by rfl⟩ : syracuseStep 11273903 = 16910855) B16910855
theorem B7515935 : Blo 1951435 7515935 := bstep (se 1 (by rfl) ⟨5636951, by rfl⟩ : syracuseStep 7515935 = 11273903) B11273903
theorem B5010623 : Blo 1951435 5010623 := bstep (se 1 (by rfl) ⟨3757967, by rfl⟩ : syracuseStep 5010623 = 7515935) B7515935
theorem B3340415 : Blo 1951435 3340415 := bstep (se 1 (by rfl) ⟨2505311, by rfl⟩ : syracuseStep 3340415 = 5010623) B5010623
theorem B2226943 : Blo 1951435 2226943 := bstep (se 1 (by rfl) ⟨1670207, by rfl⟩ : syracuseStep 2226943 = 3340415) B3340415
theorem B11877029 : Blo 1951435 11877029 := bstep (se 4 (by rfl) ⟨1113471, by rfl⟩ : syracuseStep 11877029 = 2226943) B2226943
theorem B7918019 : Blo 1951435 7918019 := bstep (se 1 (by rfl) ⟨5938514, by rfl⟩ : syracuseStep 7918019 = 11877029) B11877029
theorem B5278679 : Blo 1951435 5278679 := bstep (se 1 (by rfl) ⟨3959009, by rfl⟩ : syracuseStep 5278679 = 7918019) B7918019
theorem B3519119 : Blo 1951435 3519119 := bstep (se 1 (by rfl) ⟨2639339, by rfl⟩ : syracuseStep 3519119 = 5278679) B5278679
theorem B2346079 : Blo 1951435 2346079 := bstep (se 1 (by rfl) ⟨1759559, by rfl⟩ : syracuseStep 2346079 = 3519119) B3519119
theorem B3128105 : Blo 1951435 3128105 := bstep (se 2 (by rfl) ⟨1173039, by rfl⟩ : syracuseStep 3128105 = 2346079) B2346079
theorem B8341613 : Blo 1951435 8341613 := bstep (se 3 (by rfl) ⟨1564052, by rfl⟩ : syracuseStep 8341613 = 3128105) B3128105
theorem B5561075 : Blo 1951435 5561075 := bstep (se 1 (by rfl) ⟨4170806, by rfl⟩ : syracuseStep 5561075 = 8341613) B8341613
theorem B3707383 : Blo 1951435 3707383 := bstep (se 1 (by rfl) ⟨2780537, by rfl⟩ : syracuseStep 3707383 = 5561075) B5561075
theorem B4943177 : Blo 1951435 4943177 := bstep (se 2 (by rfl) ⟨1853691, by rfl⟩ : syracuseStep 4943177 = 3707383) B3707383
theorem B3295451 : Blo 1951435 3295451 := bstep (se 1 (by rfl) ⟨2471588, by rfl⟩ : syracuseStep 3295451 = 4943177) B4943177
theorem B2196967 : Blo 1951435 2196967 := bstep (se 1 (by rfl) ⟨1647725, by rfl⟩ : syracuseStep 2196967 = 3295451) B3295451
theorem B2929289 : Blo 1951435 2929289 := bstep (se 2 (by rfl) ⟨1098483, by rfl⟩ : syracuseStep 2929289 = 2196967) B2196967
theorem B1952859 : Blo 1951435 1952859 := bstep (se 1 (by rfl) ⟨1464644, by rfl⟩ : syracuseStep 1952859 = 2929289) B2929289
theorem B9886373 : Blo 1951435 9886373 := bbase (se 4 (by rfl) ⟨926847, by rfl⟩ : syracuseStep 9886373 = 1853695) (by norm_num)
theorem B6590915 : Blo 1951435 6590915 := bstep (se 1 (by rfl) ⟨4943186, by rfl⟩ : syracuseStep 6590915 = 9886373) B9886373
theorem B4393943 : Blo 1951435 4393943 := bstep (se 1 (by rfl) ⟨3295457, by rfl⟩ : syracuseStep 4393943 = 6590915) B6590915
theorem B2929295 : Blo 1951435 2929295 := bstep (se 1 (by rfl) ⟨2196971, by rfl⟩ : syracuseStep 2929295 = 4393943) B4393943
theorem B1952863 : Blo 1951435 1952863 := bstep (se 1 (by rfl) ⟨1464647, by rfl⟩ : syracuseStep 1952863 = 2929295) B2929295
theorem B2929301 : Blo 1951435 2929301 := bbase (se 6 (by rfl) ⟨68655, by rfl⟩ : syracuseStep 2929301 = 137311) (by norm_num)
theorem B1952867 : Blo 1951435 1952867 := bstep (se 1 (by rfl) ⟨1464650, by rfl⟩ : syracuseStep 1952867 = 2929301) B2929301
theorem B18058709 : Blo 1951435 18058709 := bbase (se 7 (by rfl) ⟨211625, by rfl⟩ : syracuseStep 18058709 = 423251) (by norm_num)
theorem B12039139 : Blo 1951435 12039139 := bstep (se 1 (by rfl) ⟨9029354, by rfl⟩ : syracuseStep 12039139 = 18058709) B18058709
theorem B16052185 : Blo 1951435 16052185 := bstep (se 2 (by rfl) ⟨6019569, by rfl⟩ : syracuseStep 16052185 = 12039139) B12039139
theorem B85611653 : Blo 1951435 85611653 := bstep (se 4 (by rfl) ⟨8026092, by rfl⟩ : syracuseStep 85611653 = 16052185) B16052185
theorem B57074435 : Blo 1951435 57074435 := bstep (se 1 (by rfl) ⟨42805826, by rfl⟩ : syracuseStep 57074435 = 85611653) B85611653
theorem B38049623 : Blo 1951435 38049623 := bstep (se 1 (by rfl) ⟨28537217, by rfl⟩ : syracuseStep 38049623 = 57074435) B57074435
theorem B25366415 : Blo 1951435 25366415 := bstep (se 1 (by rfl) ⟨19024811, by rfl⟩ : syracuseStep 25366415 = 38049623) B38049623
theorem B270575093 : Blo 1951435 270575093 := bstep (se 5 (by rfl) ⟨12683207, by rfl⟩ : syracuseStep 270575093 = 25366415) B25366415
theorem B180383395 : Blo 1951435 180383395 := bstep (se 1 (by rfl) ⟨135287546, by rfl⟩ : syracuseStep 180383395 = 270575093) B270575093
theorem B240511193 : Blo 1951435 240511193 := bstep (se 2 (by rfl) ⟨90191697, by rfl⟩ : syracuseStep 240511193 = 180383395) B180383395
theorem B160340795 : Blo 1951435 160340795 := bstep (se 1 (by rfl) ⟨120255596, by rfl⟩ : syracuseStep 160340795 = 240511193) B240511193
theorem B106893863 : Blo 1951435 106893863 := bstep (se 1 (by rfl) ⟨80170397, by rfl⟩ : syracuseStep 106893863 = 160340795) B160340795
theorem B71262575 : Blo 1951435 71262575 := bstep (se 1 (by rfl) ⟨53446931, by rfl⟩ : syracuseStep 71262575 = 106893863) B106893863
theorem B47508383 : Blo 1951435 47508383 := bstep (se 1 (by rfl) ⟨35631287, by rfl⟩ : syracuseStep 47508383 = 71262575) B71262575
theorem B31672255 : Blo 1951435 31672255 := bstep (se 1 (by rfl) ⟨23754191, by rfl⟩ : syracuseStep 31672255 = 47508383) B47508383
theorem B42229673 : Blo 1951435 42229673 := bstep (se 2 (by rfl) ⟨15836127, by rfl⟩ : syracuseStep 42229673 = 31672255) B31672255
theorem B28153115 : Blo 1951435 28153115 := bstep (se 1 (by rfl) ⟨21114836, by rfl⟩ : syracuseStep 28153115 = 42229673) B42229673
theorem B18768743 : Blo 1951435 18768743 := bstep (se 1 (by rfl) ⟨14076557, by rfl⟩ : syracuseStep 18768743 = 28153115) B28153115
theorem B12512495 : Blo 1951435 12512495 := bstep (se 1 (by rfl) ⟨9384371, by rfl⟩ : syracuseStep 12512495 = 18768743) B18768743
theorem B8341663 : Blo 1951435 8341663 := bstep (se 1 (by rfl) ⟨6256247, by rfl⟩ : syracuseStep 8341663 = 12512495) B12512495
theorem B11122217 : Blo 1951435 11122217 := bstep (se 2 (by rfl) ⟨4170831, by rfl⟩ : syracuseStep 11122217 = 8341663) B8341663
theorem B7414811 : Blo 1951435 7414811 := bstep (se 1 (by rfl) ⟨5561108, by rfl⟩ : syracuseStep 7414811 = 11122217) B11122217
theorem B4943207 : Blo 1951435 4943207 := bstep (se 1 (by rfl) ⟨3707405, by rfl⟩ : syracuseStep 4943207 = 7414811) B7414811
theorem B3295471 : Blo 1951435 3295471 := bstep (se 1 (by rfl) ⟨2471603, by rfl⟩ : syracuseStep 3295471 = 4943207) B4943207
theorem B4393961 : Blo 1951435 4393961 := bstep (se 2 (by rfl) ⟨1647735, by rfl⟩ : syracuseStep 4393961 = 3295471) B3295471
theorem B2929307 : Blo 1951435 2929307 := bstep (se 1 (by rfl) ⟨2196980, by rfl⟩ : syracuseStep 2929307 = 4393961) B4393961
theorem B1952871 : Blo 1951435 1952871 := bstep (se 1 (by rfl) ⟨1464653, by rfl⟩ : syracuseStep 1952871 = 2929307) B2929307
theorem B2196985 : Blo 1951435 2196985 := bbase (se 2 (by rfl) ⟨823869, by rfl⟩ : syracuseStep 2196985 = 1647739) (by norm_num)
theorem B2929313 : Blo 1951435 2929313 := bstep (se 2 (by rfl) ⟨1098492, by rfl⟩ : syracuseStep 2929313 = 2196985) B2196985
theorem B1952875 : Blo 1951435 1952875 := bstep (se 1 (by rfl) ⟨1464656, by rfl⟩ : syracuseStep 1952875 = 2929313) B2929313
theorem B4692205 : Blo 1951435 4692205 := bbase (se 3 (by rfl) ⟨879788, by rfl⟩ : syracuseStep 4692205 = 1759577) (by norm_num)
theorem B6256273 : Blo 1951435 6256273 := bstep (se 2 (by rfl) ⟨2346102, by rfl⟩ : syracuseStep 6256273 = 4692205) B4692205
theorem B8341697 : Blo 1951435 8341697 := bstep (se 2 (by rfl) ⟨3128136, by rfl⟩ : syracuseStep 8341697 = 6256273) B6256273
theorem B5561131 : Blo 1951435 5561131 := bstep (se 1 (by rfl) ⟨4170848, by rfl⟩ : syracuseStep 5561131 = 8341697) B8341697
theorem B7414841 : Blo 1951435 7414841 := bstep (se 2 (by rfl) ⟨2780565, by rfl⟩ : syracuseStep 7414841 = 5561131) B5561131
theorem B4943227 : Blo 1951435 4943227 := bstep (se 1 (by rfl) ⟨3707420, by rfl⟩ : syracuseStep 4943227 = 7414841) B7414841
theorem B6590969 : Blo 1951435 6590969 := bstep (se 2 (by rfl) ⟨2471613, by rfl⟩ : syracuseStep 6590969 = 4943227) B4943227
theorem B4393979 : Blo 1951435 4393979 := bstep (se 1 (by rfl) ⟨3295484, by rfl⟩ : syracuseStep 4393979 = 6590969) B6590969
theorem B2929319 : Blo 1951435 2929319 := bstep (se 1 (by rfl) ⟨2196989, by rfl⟩ : syracuseStep 2929319 = 4393979) B4393979
theorem B1952879 : Blo 1951435 1952879 := bstep (se 1 (by rfl) ⟨1464659, by rfl⟩ : syracuseStep 1952879 = 2929319) B2929319
theorem B2929325 : Blo 1951435 2929325 := bbase (se 3 (by rfl) ⟨549248, by rfl⟩ : syracuseStep 2929325 = 1098497) (by norm_num)
theorem B1952883 : Blo 1951435 1952883 := bstep (se 1 (by rfl) ⟨1464662, by rfl⟩ : syracuseStep 1952883 = 2929325) B2929325
theorem B4393997 : Blo 1951435 4393997 := bbase (se 3 (by rfl) ⟨823874, by rfl⟩ : syracuseStep 4393997 = 1647749) (by norm_num)
theorem B2929331 : Blo 1951435 2929331 := bstep (se 1 (by rfl) ⟨2196998, by rfl⟩ : syracuseStep 2929331 = 4393997) B4393997
theorem B1952887 : Blo 1951435 1952887 := bstep (se 1 (by rfl) ⟨1464665, by rfl⟩ : syracuseStep 1952887 = 2929331) B2929331
theorem B2471629 : Blo 1951435 2471629 := bbase (se 3 (by rfl) ⟨463430, by rfl⟩ : syracuseStep 2471629 = 926861) (by norm_num)
theorem B3295505 : Blo 1951435 3295505 := bstep (se 2 (by rfl) ⟨1235814, by rfl⟩ : syracuseStep 3295505 = 2471629) B2471629
theorem B2197003 : Blo 1951435 2197003 := bstep (se 1 (by rfl) ⟨1647752, by rfl⟩ : syracuseStep 2197003 = 3295505) B3295505
theorem B2929337 : Blo 1951435 2929337 := bstep (se 2 (by rfl) ⟨1098501, by rfl⟩ : syracuseStep 2929337 = 2197003) B2197003
theorem B1952891 : Blo 1951435 1952891 := bstep (se 1 (by rfl) ⟨1464668, by rfl⟩ : syracuseStep 1952891 = 2929337) B2929337
theorem B21115093 : Blo 1951435 21115093 := bbase (se 7 (by rfl) ⟨247442, by rfl⟩ : syracuseStep 21115093 = 494885) (by norm_num)
theorem B28153457 : Blo 1951435 28153457 := bstep (se 2 (by rfl) ⟨10557546, by rfl⟩ : syracuseStep 28153457 = 21115093) B21115093
theorem B18768971 : Blo 1951435 18768971 := bstep (se 1 (by rfl) ⟨14076728, by rfl⟩ : syracuseStep 18768971 = 28153457) B28153457
theorem B12512647 : Blo 1951435 12512647 := bstep (se 1 (by rfl) ⟨9384485, by rfl⟩ : syracuseStep 12512647 = 18768971) B18768971
theorem B16683529 : Blo 1951435 16683529 := bstep (se 2 (by rfl) ⟨6256323, by rfl⟩ : syracuseStep 16683529 = 12512647) B12512647
theorem B22244705 : Blo 1951435 22244705 := bstep (se 2 (by rfl) ⟨8341764, by rfl⟩ : syracuseStep 22244705 = 16683529) B16683529
theorem B14829803 : Blo 1951435 14829803 := bstep (se 1 (by rfl) ⟨11122352, by rfl⟩ : syracuseStep 14829803 = 22244705) B22244705
theorem B9886535 : Blo 1951435 9886535 := bstep (se 1 (by rfl) ⟨7414901, by rfl⟩ : syracuseStep 9886535 = 14829803) B14829803
theorem B6591023 : Blo 1951435 6591023 := bstep (se 1 (by rfl) ⟨4943267, by rfl⟩ : syracuseStep 6591023 = 9886535) B9886535
theorem B4394015 : Blo 1951435 4394015 := bstep (se 1 (by rfl) ⟨3295511, by rfl⟩ : syracuseStep 4394015 = 6591023) B6591023
theorem B2929343 : Blo 1951435 2929343 := bstep (se 1 (by rfl) ⟨2197007, by rfl⟩ : syracuseStep 2929343 = 4394015) B4394015
theorem B1952895 : Blo 1951435 1952895 := bstep (se 1 (by rfl) ⟨1464671, by rfl⟩ : syracuseStep 1952895 = 2929343) B2929343
theorem B2929349 : Blo 1951435 2929349 := bbase (se 4 (by rfl) ⟨274626, by rfl⟩ : syracuseStep 2929349 = 549253) (by norm_num)
theorem B1952899 : Blo 1951435 1952899 := bstep (se 1 (by rfl) ⟨1464674, by rfl⟩ : syracuseStep 1952899 = 2929349) B2929349
theorem B3295525 : Blo 1951435 3295525 := bbase (se 4 (by rfl) ⟨308955, by rfl⟩ : syracuseStep 3295525 = 617911) (by norm_num)
theorem B4394033 : Blo 1951435 4394033 := bstep (se 2 (by rfl) ⟨1647762, by rfl⟩ : syracuseStep 4394033 = 3295525) B3295525
theorem B2929355 : Blo 1951435 2929355 := bstep (se 1 (by rfl) ⟨2197016, by rfl⟩ : syracuseStep 2929355 = 4394033) B4394033
theorem B1952903 : Blo 1951435 1952903 := bstep (se 1 (by rfl) ⟨1464677, by rfl⟩ : syracuseStep 1952903 = 2929355) B2929355
theorem B2197021 : Blo 1951435 2197021 := bbase (se 3 (by rfl) ⟨411941, by rfl⟩ : syracuseStep 2197021 = 823883) (by norm_num)
theorem B2929361 : Blo 1951435 2929361 := bstep (se 2 (by rfl) ⟨1098510, by rfl⟩ : syracuseStep 2929361 = 2197021) B2197021
theorem B1952907 : Blo 1951435 1952907 := bstep (se 1 (by rfl) ⟨1464680, by rfl⟩ : syracuseStep 1952907 = 2929361) B2929361
theorem B6591077 : Blo 1951435 6591077 := bbase (se 4 (by rfl) ⟨617913, by rfl⟩ : syracuseStep 6591077 = 1235827) (by norm_num)
theorem B4394051 : Blo 1951435 4394051 := bstep (se 1 (by rfl) ⟨3295538, by rfl⟩ : syracuseStep 4394051 = 6591077) B6591077
theorem B2929367 : Blo 1951435 2929367 := bstep (se 1 (by rfl) ⟨2197025, by rfl⟩ : syracuseStep 2929367 = 4394051) B4394051
theorem B1952911 : Blo 1951435 1952911 := bstep (se 1 (by rfl) ⟨1464683, by rfl⟩ : syracuseStep 1952911 = 2929367) B2929367
theorem B2929373 : Blo 1951435 2929373 := bbase (se 3 (by rfl) ⟨549257, by rfl⟩ : syracuseStep 2929373 = 1098515) (by norm_num)
theorem B1952915 : Blo 1951435 1952915 := bstep (se 1 (by rfl) ⟨1464686, by rfl⟩ : syracuseStep 1952915 = 2929373) B2929373
theorem B4394069 : Blo 1951435 4394069 := bbase (se 8 (by rfl) ⟨25746, by rfl⟩ : syracuseStep 4394069 = 51493) (by norm_num)
theorem B2929379 : Blo 1951435 2929379 := bstep (se 1 (by rfl) ⟨2197034, by rfl⟩ : syracuseStep 2929379 = 4394069) B4394069
theorem B1952919 : Blo 1951435 1952919 := bstep (se 1 (by rfl) ⟨1464689, by rfl⟩ : syracuseStep 1952919 = 2929379) B2929379
theorem B4756333 : Blo 1951435 4756333 := bbase (se 3 (by rfl) ⟨891812, by rfl⟩ : syracuseStep 4756333 = 1783625) (by norm_num)
theorem B6341777 : Blo 1951435 6341777 := bstep (se 2 (by rfl) ⟨2378166, by rfl⟩ : syracuseStep 6341777 = 4756333) B4756333
theorem B4227851 : Blo 1951435 4227851 := bstep (se 1 (by rfl) ⟨3170888, by rfl⟩ : syracuseStep 4227851 = 6341777) B6341777
theorem B2818567 : Blo 1951435 2818567 := bstep (se 1 (by rfl) ⟨2113925, by rfl⟩ : syracuseStep 2818567 = 4227851) B4227851
theorem B3758089 : Blo 1951435 3758089 := bstep (se 2 (by rfl) ⟨1409283, by rfl⟩ : syracuseStep 3758089 = 2818567) B2818567
theorem B5010785 : Blo 1951435 5010785 := bstep (se 2 (by rfl) ⟨1879044, by rfl⟩ : syracuseStep 5010785 = 3758089) B3758089
theorem B3340523 : Blo 1951435 3340523 := bstep (se 1 (by rfl) ⟨2505392, by rfl⟩ : syracuseStep 3340523 = 5010785) B5010785
theorem B8908061 : Blo 1951435 8908061 := bstep (se 3 (by rfl) ⟨1670261, by rfl⟩ : syracuseStep 8908061 = 3340523) B3340523
theorem B23754829 : Blo 1951435 23754829 := bstep (se 3 (by rfl) ⟨4454030, by rfl⟩ : syracuseStep 23754829 = 8908061) B8908061
theorem B31673105 : Blo 1951435 31673105 := bstep (se 2 (by rfl) ⟨11877414, by rfl⟩ : syracuseStep 31673105 = 23754829) B23754829
theorem B21115403 : Blo 1951435 21115403 := bstep (se 1 (by rfl) ⟨15836552, by rfl⟩ : syracuseStep 21115403 = 31673105) B31673105
theorem B14076935 : Blo 1951435 14076935 := bstep (se 1 (by rfl) ⟨10557701, by rfl⟩ : syracuseStep 14076935 = 21115403) B21115403
theorem B9384623 : Blo 1951435 9384623 := bstep (se 1 (by rfl) ⟨7038467, by rfl⟩ : syracuseStep 9384623 = 14076935) B14076935
theorem B6256415 : Blo 1951435 6256415 := bstep (se 1 (by rfl) ⟨4692311, by rfl⟩ : syracuseStep 6256415 = 9384623) B9384623
theorem B4170943 : Blo 1951435 4170943 := bstep (se 1 (by rfl) ⟨3128207, by rfl⟩ : syracuseStep 4170943 = 6256415) B6256415
theorem B5561257 : Blo 1951435 5561257 := bstep (se 2 (by rfl) ⟨2085471, by rfl⟩ : syracuseStep 5561257 = 4170943) B4170943
theorem B7415009 : Blo 1951435 7415009 := bstep (se 2 (by rfl) ⟨2780628, by rfl⟩ : syracuseStep 7415009 = 5561257) B5561257
theorem B4943339 : Blo 1951435 4943339 := bstep (se 1 (by rfl) ⟨3707504, by rfl⟩ : syracuseStep 4943339 = 7415009) B7415009
theorem B3295559 : Blo 1951435 3295559 := bstep (se 1 (by rfl) ⟨2471669, by rfl⟩ : syracuseStep 3295559 = 4943339) B4943339
theorem B2197039 : Blo 1951435 2197039 := bstep (se 1 (by rfl) ⟨1647779, by rfl⟩ : syracuseStep 2197039 = 3295559) B3295559
theorem B2929385 : Blo 1951435 2929385 := bstep (se 2 (by rfl) ⟨1098519, by rfl⟩ : syracuseStep 2929385 = 2197039) B2197039
theorem B1952923 : Blo 1951435 1952923 := bstep (se 1 (by rfl) ⟨1464692, by rfl⟩ : syracuseStep 1952923 = 2929385) B2929385
theorem B4285541 : Blo 1951435 4285541 := bbase (se 4 (by rfl) ⟨401769, by rfl⟩ : syracuseStep 4285541 = 803539) (by norm_num)
theorem B2857027 : Blo 1951435 2857027 := bstep (se 1 (by rfl) ⟨2142770, by rfl⟩ : syracuseStep 2857027 = 4285541) B4285541
theorem B3809369 : Blo 1951435 3809369 := bstep (se 2 (by rfl) ⟨1428513, by rfl⟩ : syracuseStep 3809369 = 2857027) B2857027
theorem B2539579 : Blo 1951435 2539579 := bstep (se 1 (by rfl) ⟨1904684, by rfl⟩ : syracuseStep 2539579 = 3809369) B3809369
theorem B3386105 : Blo 1951435 3386105 := bstep (se 2 (by rfl) ⟨1269789, by rfl⟩ : syracuseStep 3386105 = 2539579) B2539579
theorem B2257403 : Blo 1951435 2257403 := bstep (se 1 (by rfl) ⟨1693052, by rfl⟩ : syracuseStep 2257403 = 3386105) B3386105
theorem B24078965 : Blo 1951435 24078965 := bstep (se 5 (by rfl) ⟨1128701, by rfl⟩ : syracuseStep 24078965 = 2257403) B2257403
theorem B64210573 : Blo 1951435 64210573 := bstep (se 3 (by rfl) ⟨12039482, by rfl⟩ : syracuseStep 64210573 = 24078965) B24078965
theorem B85614097 : Blo 1951435 85614097 := bstep (se 2 (by rfl) ⟨32105286, by rfl⟩ : syracuseStep 85614097 = 64210573) B64210573
theorem B114152129 : Blo 1951435 114152129 := bstep (se 2 (by rfl) ⟨42807048, by rfl⟩ : syracuseStep 114152129 = 85614097) B85614097
theorem B76101419 : Blo 1951435 76101419 := bstep (se 1 (by rfl) ⟨57076064, by rfl⟩ : syracuseStep 76101419 = 114152129) B114152129
theorem B50734279 : Blo 1951435 50734279 := bstep (se 1 (by rfl) ⟨38050709, by rfl⟩ : syracuseStep 50734279 = 76101419) B76101419
theorem B67645705 : Blo 1951435 67645705 := bstep (se 2 (by rfl) ⟨25367139, by rfl⟩ : syracuseStep 67645705 = 50734279) B50734279
theorem B90194273 : Blo 1951435 90194273 := bstep (se 2 (by rfl) ⟨33822852, by rfl⟩ : syracuseStep 90194273 = 67645705) B67645705
theorem B60129515 : Blo 1951435 60129515 := bstep (se 1 (by rfl) ⟨45097136, by rfl⟩ : syracuseStep 60129515 = 90194273) B90194273
theorem B40086343 : Blo 1951435 40086343 := bstep (se 1 (by rfl) ⟨30064757, by rfl⟩ : syracuseStep 40086343 = 60129515) B60129515
theorem B213793829 : Blo 1951435 213793829 := bstep (se 4 (by rfl) ⟨20043171, by rfl⟩ : syracuseStep 213793829 = 40086343) B40086343
theorem B142529219 : Blo 1951435 142529219 := bstep (se 1 (by rfl) ⟨106896914, by rfl⟩ : syracuseStep 142529219 = 213793829) B213793829
theorem B95019479 : Blo 1951435 95019479 := bstep (se 1 (by rfl) ⟨71264609, by rfl⟩ : syracuseStep 95019479 = 142529219) B142529219
theorem B63346319 : Blo 1951435 63346319 := bstep (se 1 (by rfl) ⟨47509739, by rfl⟩ : syracuseStep 63346319 = 95019479) B95019479
theorem B42230879 : Blo 1951435 42230879 := bstep (se 1 (by rfl) ⟨31673159, by rfl⟩ : syracuseStep 42230879 = 63346319) B63346319
theorem B28153919 : Blo 1951435 28153919 := bstep (se 1 (by rfl) ⟨21115439, by rfl⟩ : syracuseStep 28153919 = 42230879) B42230879
theorem B18769279 : Blo 1951435 18769279 := bstep (se 1 (by rfl) ⟨14076959, by rfl⟩ : syracuseStep 18769279 = 28153919) B28153919
theorem B25025705 : Blo 1951435 25025705 := bstep (se 2 (by rfl) ⟨9384639, by rfl⟩ : syracuseStep 25025705 = 18769279) B18769279
theorem B16683803 : Blo 1951435 16683803 := bstep (se 1 (by rfl) ⟨12512852, by rfl⟩ : syracuseStep 16683803 = 25025705) B25025705
theorem B11122535 : Blo 1951435 11122535 := bstep (se 1 (by rfl) ⟨8341901, by rfl⟩ : syracuseStep 11122535 = 16683803) B16683803
theorem B7415023 : Blo 1951435 7415023 := bstep (se 1 (by rfl) ⟨5561267, by rfl⟩ : syracuseStep 7415023 = 11122535) B11122535
theorem B9886697 : Blo 1951435 9886697 := bstep (se 2 (by rfl) ⟨3707511, by rfl⟩ : syracuseStep 9886697 = 7415023) B7415023
theorem B6591131 : Blo 1951435 6591131 := bstep (se 1 (by rfl) ⟨4943348, by rfl⟩ : syracuseStep 6591131 = 9886697) B9886697
theorem B4394087 : Blo 1951435 4394087 := bstep (se 1 (by rfl) ⟨3295565, by rfl⟩ : syracuseStep 4394087 = 6591131) B6591131
theorem B2929391 : Blo 1951435 2929391 := bstep (se 1 (by rfl) ⟨2197043, by rfl⟩ : syracuseStep 2929391 = 4394087) B4394087
theorem B1952927 : Blo 1951435 1952927 := bstep (se 1 (by rfl) ⟨1464695, by rfl⟩ : syracuseStep 1952927 = 2929391) B2929391
theorem B2929397 : Blo 1951435 2929397 := bbase (se 5 (by rfl) ⟨137315, by rfl⟩ : syracuseStep 2929397 = 274631) (by norm_num)
theorem B1952931 : Blo 1951435 1952931 := bstep (se 1 (by rfl) ⟨1464698, by rfl⟩ : syracuseStep 1952931 = 2929397) B2929397
theorem B6256453 : Blo 1951435 6256453 := bbase (se 4 (by rfl) ⟨586542, by rfl⟩ : syracuseStep 6256453 = 1173085) (by norm_num)
theorem B8341937 : Blo 1951435 8341937 := bstep (se 2 (by rfl) ⟨3128226, by rfl⟩ : syracuseStep 8341937 = 6256453) B6256453
theorem B5561291 : Blo 1951435 5561291 := bstep (se 1 (by rfl) ⟨4170968, by rfl⟩ : syracuseStep 5561291 = 8341937) B8341937
theorem B3707527 : Blo 1951435 3707527 := bstep (se 1 (by rfl) ⟨2780645, by rfl⟩ : syracuseStep 3707527 = 5561291) B5561291
theorem B4943369 : Blo 1951435 4943369 := bstep (se 2 (by rfl) ⟨1853763, by rfl⟩ : syracuseStep 4943369 = 3707527) B3707527
theorem B3295579 : Blo 1951435 3295579 := bstep (se 1 (by rfl) ⟨2471684, by rfl⟩ : syracuseStep 3295579 = 4943369) B4943369
theorem B4394105 : Blo 1951435 4394105 := bstep (se 2 (by rfl) ⟨1647789, by rfl⟩ : syracuseStep 4394105 = 3295579) B3295579
theorem B2929403 : Blo 1951435 2929403 := bstep (se 1 (by rfl) ⟨2197052, by rfl⟩ : syracuseStep 2929403 = 4394105) B4394105
theorem B1952935 : Blo 1951435 1952935 := bstep (se 1 (by rfl) ⟨1464701, by rfl⟩ : syracuseStep 1952935 = 2929403) B2929403
theorem B2197057 : Blo 1951435 2197057 := bbase (se 2 (by rfl) ⟨823896, by rfl⟩ : syracuseStep 2197057 = 1647793) (by norm_num)
theorem B2929409 : Blo 1951435 2929409 := bstep (se 2 (by rfl) ⟨1098528, by rfl⟩ : syracuseStep 2929409 = 2197057) B2197057
theorem B1952939 : Blo 1951435 1952939 := bstep (se 1 (by rfl) ⟨1464704, by rfl⟩ : syracuseStep 1952939 = 2929409) B2929409
theorem B4943389 : Blo 1951435 4943389 := bbase (se 3 (by rfl) ⟨926885, by rfl⟩ : syracuseStep 4943389 = 1853771) (by norm_num)
theorem B6591185 : Blo 1951435 6591185 := bstep (se 2 (by rfl) ⟨2471694, by rfl⟩ : syracuseStep 6591185 = 4943389) B4943389
theorem B4394123 : Blo 1951435 4394123 := bstep (se 1 (by rfl) ⟨3295592, by rfl⟩ : syracuseStep 4394123 = 6591185) B6591185
theorem B2929415 : Blo 1951435 2929415 := bstep (se 1 (by rfl) ⟨2197061, by rfl⟩ : syracuseStep 2929415 = 4394123) B4394123
theorem B1952943 : Blo 1951435 1952943 := bstep (se 1 (by rfl) ⟨1464707, by rfl⟩ : syracuseStep 1952943 = 2929415) B2929415
theorem B2929421 : Blo 1951435 2929421 := bbase (se 3 (by rfl) ⟨549266, by rfl⟩ : syracuseStep 2929421 = 1098533) (by norm_num)
theorem B1952947 : Blo 1951435 1952947 := bstep (se 1 (by rfl) ⟨1464710, by rfl⟩ : syracuseStep 1952947 = 2929421) B2929421
theorem B4394141 : Blo 1951435 4394141 := bbase (se 3 (by rfl) ⟨823901, by rfl⟩ : syracuseStep 4394141 = 1647803) (by norm_num)
theorem B2929427 : Blo 1951435 2929427 := bstep (se 1 (by rfl) ⟨2197070, by rfl⟩ : syracuseStep 2929427 = 4394141) B4394141
theorem B1952951 : Blo 1951435 1952951 := bstep (se 1 (by rfl) ⟨1464713, by rfl⟩ : syracuseStep 1952951 = 2929427) B2929427
theorem B3295613 : Blo 1951435 3295613 := bbase (se 3 (by rfl) ⟨617927, by rfl⟩ : syracuseStep 3295613 = 1235855) (by norm_num)
theorem B2197075 : Blo 1951435 2197075 := bstep (se 1 (by rfl) ⟨1647806, by rfl⟩ : syracuseStep 2197075 = 3295613) B3295613
theorem B2929433 : Blo 1951435 2929433 := bstep (se 2 (by rfl) ⟨1098537, by rfl⟩ : syracuseStep 2929433 = 2197075) B2197075
theorem B1952955 : Blo 1951435 1952955 := bstep (se 1 (by rfl) ⟨1464716, by rfl⟩ : syracuseStep 1952955 = 2929433) B2929433
theorem B4692397 : Blo 1951435 4692397 := bbase (se 3 (by rfl) ⟨879824, by rfl⟩ : syracuseStep 4692397 = 1759649) (by norm_num)
theorem B6256529 : Blo 1951435 6256529 := bstep (se 2 (by rfl) ⟨2346198, by rfl⟩ : syracuseStep 6256529 = 4692397) B4692397
theorem B4171019 : Blo 1951435 4171019 := bstep (se 1 (by rfl) ⟨3128264, by rfl⟩ : syracuseStep 4171019 = 6256529) B6256529
theorem B11122717 : Blo 1951435 11122717 := bstep (se 3 (by rfl) ⟨2085509, by rfl⟩ : syracuseStep 11122717 = 4171019) B4171019
theorem B14830289 : Blo 1951435 14830289 := bstep (se 2 (by rfl) ⟨5561358, by rfl⟩ : syracuseStep 14830289 = 11122717) B11122717
theorem B9886859 : Blo 1951435 9886859 := bstep (se 1 (by rfl) ⟨7415144, by rfl⟩ : syracuseStep 9886859 = 14830289) B14830289
theorem B6591239 : Blo 1951435 6591239 := bstep (se 1 (by rfl) ⟨4943429, by rfl⟩ : syracuseStep 6591239 = 9886859) B9886859
theorem B4394159 : Blo 1951435 4394159 := bstep (se 1 (by rfl) ⟨3295619, by rfl⟩ : syracuseStep 4394159 = 6591239) B6591239
theorem B2929439 : Blo 1951435 2929439 := bstep (se 1 (by rfl) ⟨2197079, by rfl⟩ : syracuseStep 2929439 = 4394159) B4394159
theorem B1952959 : Blo 1951435 1952959 := bstep (se 1 (by rfl) ⟨1464719, by rfl⟩ : syracuseStep 1952959 = 2929439) B2929439
theorem B2929445 : Blo 1951435 2929445 := bbase (se 4 (by rfl) ⟨274635, by rfl⟩ : syracuseStep 2929445 = 549271) (by norm_num)
theorem B1952963 : Blo 1951435 1952963 := bstep (se 1 (by rfl) ⟨1464722, by rfl⟩ : syracuseStep 1952963 = 2929445) B2929445
theorem B2471725 : Blo 1951435 2471725 := bbase (se 3 (by rfl) ⟨463448, by rfl⟩ : syracuseStep 2471725 = 926897) (by norm_num)
theorem B3295633 : Blo 1951435 3295633 := bstep (se 2 (by rfl) ⟨1235862, by rfl⟩ : syracuseStep 3295633 = 2471725) B2471725
theorem B4394177 : Blo 1951435 4394177 := bstep (se 2 (by rfl) ⟨1647816, by rfl⟩ : syracuseStep 4394177 = 3295633) B3295633
theorem B2929451 : Blo 1951435 2929451 := bstep (se 1 (by rfl) ⟨2197088, by rfl⟩ : syracuseStep 2929451 = 4394177) B4394177
theorem B1952967 : Blo 1951435 1952967 := bstep (se 1 (by rfl) ⟨1464725, by rfl⟩ : syracuseStep 1952967 = 2929451) B2929451
theorem B2197093 : Blo 1951435 2197093 := bbase (se 4 (by rfl) ⟨205977, by rfl⟩ : syracuseStep 2197093 = 411955) (by norm_num)
theorem B2929457 : Blo 1951435 2929457 := bstep (se 2 (by rfl) ⟨1098546, by rfl⟩ : syracuseStep 2929457 = 2197093) B2197093
theorem B1952971 : Blo 1951435 1952971 := bstep (se 1 (by rfl) ⟨1464728, by rfl⟩ : syracuseStep 1952971 = 2929457) B2929457
theorem B4692437 : Blo 1951435 4692437 := bbase (se 7 (by rfl) ⟨54989, by rfl⟩ : syracuseStep 4692437 = 109979) (by norm_num)
theorem B3128291 : Blo 1951435 3128291 := bstep (se 1 (by rfl) ⟨2346218, by rfl⟩ : syracuseStep 3128291 = 4692437) B4692437
theorem B2085527 : Blo 1951435 2085527 := bstep (se 1 (by rfl) ⟨1564145, by rfl⟩ : syracuseStep 2085527 = 3128291) B3128291
theorem B5561405 : Blo 1951435 5561405 := bstep (se 3 (by rfl) ⟨1042763, by rfl⟩ : syracuseStep 5561405 = 2085527) B2085527
theorem B3707603 : Blo 1951435 3707603 := bstep (se 1 (by rfl) ⟨2780702, by rfl⟩ : syracuseStep 3707603 = 5561405) B5561405
theorem B2471735 : Blo 1951435 2471735 := bstep (se 1 (by rfl) ⟨1853801, by rfl⟩ : syracuseStep 2471735 = 3707603) B3707603
theorem B6591293 : Blo 1951435 6591293 := bstep (se 3 (by rfl) ⟨1235867, by rfl⟩ : syracuseStep 6591293 = 2471735) B2471735
theorem B4394195 : Blo 1951435 4394195 := bstep (se 1 (by rfl) ⟨3295646, by rfl⟩ : syracuseStep 4394195 = 6591293) B6591293
theorem B2929463 : Blo 1951435 2929463 := bstep (se 1 (by rfl) ⟨2197097, by rfl⟩ : syracuseStep 2929463 = 4394195) B4394195
theorem B1952975 : Blo 1951435 1952975 := bstep (se 1 (by rfl) ⟨1464731, by rfl⟩ : syracuseStep 1952975 = 2929463) B2929463
theorem B2929469 : Blo 1951435 2929469 := bbase (se 3 (by rfl) ⟨549275, by rfl⟩ : syracuseStep 2929469 = 1098551) (by norm_num)
theorem B1952979 : Blo 1951435 1952979 := bstep (se 1 (by rfl) ⟨1464734, by rfl⟩ : syracuseStep 1952979 = 2929469) B2929469
theorem B4394213 : Blo 1951435 4394213 := bbase (se 4 (by rfl) ⟨411957, by rfl⟩ : syracuseStep 4394213 = 823915) (by norm_num)
theorem B2929475 : Blo 1951435 2929475 := bstep (se 1 (by rfl) ⟨2197106, by rfl⟩ : syracuseStep 2929475 = 4394213) B4394213
theorem B1952983 : Blo 1951435 1952983 := bstep (se 1 (by rfl) ⟨1464737, by rfl⟩ : syracuseStep 1952983 = 2929475) B2929475
theorem B4943501 : Blo 1951435 4943501 := bbase (se 3 (by rfl) ⟨926906, by rfl⟩ : syracuseStep 4943501 = 1853813) (by norm_num)
theorem B3295667 : Blo 1951435 3295667 := bstep (se 1 (by rfl) ⟨2471750, by rfl⟩ : syracuseStep 3295667 = 4943501) B4943501
theorem B2197111 : Blo 1951435 2197111 := bstep (se 1 (by rfl) ⟨1647833, by rfl⟩ : syracuseStep 2197111 = 3295667) B3295667
theorem B2929481 : Blo 1951435 2929481 := bstep (se 2 (by rfl) ⟨1098555, by rfl⟩ : syracuseStep 2929481 = 2197111) B2197111
theorem B1952987 : Blo 1951435 1952987 := bstep (se 1 (by rfl) ⟨1464740, by rfl⟩ : syracuseStep 1952987 = 2929481) B2929481
theorem B2780725 : Blo 1951435 2780725 := bbase (se 5 (by rfl) ⟨130346, by rfl⟩ : syracuseStep 2780725 = 260693) (by norm_num)
theorem B3707633 : Blo 1951435 3707633 := bstep (se 2 (by rfl) ⟨1390362, by rfl⟩ : syracuseStep 3707633 = 2780725) B2780725
theorem B9887021 : Blo 1951435 9887021 := bstep (se 3 (by rfl) ⟨1853816, by rfl⟩ : syracuseStep 9887021 = 3707633) B3707633
theorem B6591347 : Blo 1951435 6591347 := bstep (se 1 (by rfl) ⟨4943510, by rfl⟩ : syracuseStep 6591347 = 9887021) B9887021
theorem B4394231 : Blo 1951435 4394231 := bstep (se 1 (by rfl) ⟨3295673, by rfl⟩ : syracuseStep 4394231 = 6591347) B6591347
theorem B2929487 : Blo 1951435 2929487 := bstep (se 1 (by rfl) ⟨2197115, by rfl⟩ : syracuseStep 2929487 = 4394231) B4394231
theorem B1952991 : Blo 1951435 1952991 := bstep (se 1 (by rfl) ⟨1464743, by rfl⟩ : syracuseStep 1952991 = 2929487) B2929487
theorem B2929493 : Blo 1951435 2929493 := bbase (se 9 (by rfl) ⟨8582, by rfl⟩ : syracuseStep 2929493 = 17165) (by norm_num)
theorem B1952995 : Blo 1951435 1952995 := bstep (se 1 (by rfl) ⟨1464746, by rfl⟩ : syracuseStep 1952995 = 2929493) B2929493
theorem B3959293 : Blo 1951435 3959293 := bbase (se 3 (by rfl) ⟨742367, by rfl⟩ : syracuseStep 3959293 = 1484735) (by norm_num)
theorem B5279057 : Blo 1951435 5279057 := bstep (se 2 (by rfl) ⟨1979646, by rfl⟩ : syracuseStep 5279057 = 3959293) B3959293
theorem B3519371 : Blo 1951435 3519371 := bstep (se 1 (by rfl) ⟨2639528, by rfl⟩ : syracuseStep 3519371 = 5279057) B5279057
theorem B2346247 : Blo 1951435 2346247 := bstep (se 1 (by rfl) ⟨1759685, by rfl⟩ : syracuseStep 2346247 = 3519371) B3519371
theorem B3128329 : Blo 1951435 3128329 := bstep (se 2 (by rfl) ⟨1173123, by rfl⟩ : syracuseStep 3128329 = 2346247) B2346247
theorem B4171105 : Blo 1951435 4171105 := bstep (se 2 (by rfl) ⟨1564164, by rfl⟩ : syracuseStep 4171105 = 3128329) B3128329
theorem B5561473 : Blo 1951435 5561473 := bstep (se 2 (by rfl) ⟨2085552, by rfl⟩ : syracuseStep 5561473 = 4171105) B4171105
theorem B7415297 : Blo 1951435 7415297 := bstep (se 2 (by rfl) ⟨2780736, by rfl⟩ : syracuseStep 7415297 = 5561473) B5561473
theorem B4943531 : Blo 1951435 4943531 := bstep (se 1 (by rfl) ⟨3707648, by rfl⟩ : syracuseStep 4943531 = 7415297) B7415297
theorem B3295687 : Blo 1951435 3295687 := bstep (se 1 (by rfl) ⟨2471765, by rfl⟩ : syracuseStep 3295687 = 4943531) B4943531
theorem B4394249 : Blo 1951435 4394249 := bstep (se 2 (by rfl) ⟨1647843, by rfl⟩ : syracuseStep 4394249 = 3295687) B3295687
theorem B2929499 : Blo 1951435 2929499 := bstep (se 1 (by rfl) ⟨2197124, by rfl⟩ : syracuseStep 2929499 = 4394249) B4394249
theorem B1952999 : Blo 1951435 1952999 := bstep (se 1 (by rfl) ⟨1464749, by rfl⟩ : syracuseStep 1952999 = 2929499) B2929499
theorem B2197129 : Blo 1951435 2197129 := bbase (se 2 (by rfl) ⟨823923, by rfl⟩ : syracuseStep 2197129 = 1647847) (by norm_num)
theorem B2929505 : Blo 1951435 2929505 := bstep (se 2 (by rfl) ⟨1098564, by rfl⟩ : syracuseStep 2929505 = 2197129) B2197129
theorem B1953003 : Blo 1951435 1953003 := bstep (se 1 (by rfl) ⟨1464752, by rfl⟩ : syracuseStep 1953003 = 2929505) B2929505
theorem B4454221 : Blo 1951435 4454221 := bbase (se 3 (by rfl) ⟨835166, by rfl⟩ : syracuseStep 4454221 = 1670333) (by norm_num)
theorem B5938961 : Blo 1951435 5938961 := bstep (se 2 (by rfl) ⟨2227110, by rfl⟩ : syracuseStep 5938961 = 4454221) B4454221
theorem B15837229 : Blo 1951435 15837229 := bstep (se 3 (by rfl) ⟨2969480, by rfl⟩ : syracuseStep 15837229 = 5938961) B5938961
theorem B21116305 : Blo 1951435 21116305 := bstep (se 2 (by rfl) ⟨7918614, by rfl⟩ : syracuseStep 21116305 = 15837229) B15837229
theorem B28155073 : Blo 1951435 28155073 := bstep (se 2 (by rfl) ⟨10558152, by rfl⟩ : syracuseStep 28155073 = 21116305) B21116305
theorem B37540097 : Blo 1951435 37540097 := bstep (se 2 (by rfl) ⟨14077536, by rfl⟩ : syracuseStep 37540097 = 28155073) B28155073
theorem B25026731 : Blo 1951435 25026731 := bstep (se 1 (by rfl) ⟨18770048, by rfl⟩ : syracuseStep 25026731 = 37540097) B37540097
theorem B16684487 : Blo 1951435 16684487 := bstep (se 1 (by rfl) ⟨12513365, by rfl⟩ : syracuseStep 16684487 = 25026731) B25026731
theorem B11122991 : Blo 1951435 11122991 := bstep (se 1 (by rfl) ⟨8342243, by rfl⟩ : syracuseStep 11122991 = 16684487) B16684487
theorem B7415327 : Blo 1951435 7415327 := bstep (se 1 (by rfl) ⟨5561495, by rfl⟩ : syracuseStep 7415327 = 11122991) B11122991
theorem B4943551 : Blo 1951435 4943551 := bstep (se 1 (by rfl) ⟨3707663, by rfl⟩ : syracuseStep 4943551 = 7415327) B7415327
theorem B6591401 : Blo 1951435 6591401 := bstep (se 2 (by rfl) ⟨2471775, by rfl⟩ : syracuseStep 6591401 = 4943551) B4943551
theorem B4394267 : Blo 1951435 4394267 := bstep (se 1 (by rfl) ⟨3295700, by rfl⟩ : syracuseStep 4394267 = 6591401) B6591401
theorem B2929511 : Blo 1951435 2929511 := bstep (se 1 (by rfl) ⟨2197133, by rfl⟩ : syracuseStep 2929511 = 4394267) B4394267
theorem B1953007 : Blo 1951435 1953007 := bstep (se 1 (by rfl) ⟨1464755, by rfl⟩ : syracuseStep 1953007 = 2929511) B2929511
theorem B2929517 : Blo 1951435 2929517 := bbase (se 3 (by rfl) ⟨549284, by rfl⟩ : syracuseStep 2929517 = 1098569) (by norm_num)
theorem B1953011 : Blo 1951435 1953011 := bstep (se 1 (by rfl) ⟨1464758, by rfl⟩ : syracuseStep 1953011 = 2929517) B2929517
theorem B4394285 : Blo 1951435 4394285 := bbase (se 3 (by rfl) ⟨823928, by rfl⟩ : syracuseStep 4394285 = 1647857) (by norm_num)
theorem B2929523 : Blo 1951435 2929523 := bstep (se 1 (by rfl) ⟨2197142, by rfl⟩ : syracuseStep 2929523 = 4394285) B4394285
theorem B1953015 : Blo 1951435 1953015 := bstep (se 1 (by rfl) ⟨1464761, by rfl⟩ : syracuseStep 1953015 = 2929523) B2929523
theorem B8908501 : Blo 1951435 8908501 := bbase (se 7 (by rfl) ⟨104396, by rfl⟩ : syracuseStep 8908501 = 208793) (by norm_num)
theorem B11878001 : Blo 1951435 11878001 := bstep (se 2 (by rfl) ⟨4454250, by rfl⟩ : syracuseStep 11878001 = 8908501) B8908501
theorem B7918667 : Blo 1951435 7918667 := bstep (se 1 (by rfl) ⟨5939000, by rfl⟩ : syracuseStep 7918667 = 11878001) B11878001
theorem B5279111 : Blo 1951435 5279111 := bstep (se 1 (by rfl) ⟨3959333, by rfl⟩ : syracuseStep 5279111 = 7918667) B7918667
theorem B3519407 : Blo 1951435 3519407 := bstep (se 1 (by rfl) ⟨2639555, by rfl⟩ : syracuseStep 3519407 = 5279111) B5279111
theorem B9385085 : Blo 1951435 9385085 := bstep (se 3 (by rfl) ⟨1759703, by rfl⟩ : syracuseStep 9385085 = 3519407) B3519407
theorem B6256723 : Blo 1951435 6256723 := bstep (se 1 (by rfl) ⟨4692542, by rfl⟩ : syracuseStep 6256723 = 9385085) B9385085
theorem B8342297 : Blo 1951435 8342297 := bstep (se 2 (by rfl) ⟨3128361, by rfl⟩ : syracuseStep 8342297 = 6256723) B6256723
theorem B5561531 : Blo 1951435 5561531 := bstep (se 1 (by rfl) ⟨4171148, by rfl⟩ : syracuseStep 5561531 = 8342297) B8342297
theorem B3707687 : Blo 1951435 3707687 := bstep (se 1 (by rfl) ⟨2780765, by rfl⟩ : syracuseStep 3707687 = 5561531) B5561531
theorem B2471791 : Blo 1951435 2471791 := bstep (se 1 (by rfl) ⟨1853843, by rfl⟩ : syracuseStep 2471791 = 3707687) B3707687
theorem B3295721 : Blo 1951435 3295721 := bstep (se 2 (by rfl) ⟨1235895, by rfl⟩ : syracuseStep 3295721 = 2471791) B2471791
theorem B2197147 : Blo 1951435 2197147 := bstep (se 1 (by rfl) ⟨1647860, by rfl⟩ : syracuseStep 2197147 = 3295721) B3295721
theorem B2929529 : Blo 1951435 2929529 := bstep (se 2 (by rfl) ⟨1098573, by rfl⟩ : syracuseStep 2929529 = 2197147) B2197147
theorem B1953019 : Blo 1951435 1953019 := bstep (se 1 (by rfl) ⟨1464764, by rfl⟩ : syracuseStep 1953019 = 2929529) B2929529
theorem B3340693 : Blo 1951435 3340693 := bbase (se 6 (by rfl) ⟨78297, by rfl⟩ : syracuseStep 3340693 = 156595) (by norm_num)
theorem B17817029 : Blo 1951435 17817029 := bstep (se 4 (by rfl) ⟨1670346, by rfl⟩ : syracuseStep 17817029 = 3340693) B3340693
theorem B11878019 : Blo 1951435 11878019 := bstep (se 1 (by rfl) ⟨8908514, by rfl⟩ : syracuseStep 11878019 = 17817029) B17817029
theorem B7918679 : Blo 1951435 7918679 := bstep (se 1 (by rfl) ⟨5939009, by rfl⟩ : syracuseStep 7918679 = 11878019) B11878019
theorem B21116477 : Blo 1951435 21116477 := bstep (se 3 (by rfl) ⟨3959339, by rfl⟩ : syracuseStep 21116477 = 7918679) B7918679
theorem B14077651 : Blo 1951435 14077651 := bstep (se 1 (by rfl) ⟨10558238, by rfl⟩ : syracuseStep 14077651 = 21116477) B21116477
theorem B18770201 : Blo 1951435 18770201 := bstep (se 2 (by rfl) ⟨7038825, by rfl⟩ : syracuseStep 18770201 = 14077651) B14077651
theorem B12513467 : Blo 1951435 12513467 := bstep (se 1 (by rfl) ⟨9385100, by rfl⟩ : syracuseStep 12513467 = 18770201) B18770201
theorem B33369245 : Blo 1951435 33369245 := bstep (se 3 (by rfl) ⟨6256733, by rfl⟩ : syracuseStep 33369245 = 12513467) B12513467
theorem B22246163 : Blo 1951435 22246163 := bstep (se 1 (by rfl) ⟨16684622, by rfl⟩ : syracuseStep 22246163 = 33369245) B33369245
theorem B14830775 : Blo 1951435 14830775 := bstep (se 1 (by rfl) ⟨11123081, by rfl⟩ : syracuseStep 14830775 = 22246163) B22246163
theorem B9887183 : Blo 1951435 9887183 := bstep (se 1 (by rfl) ⟨7415387, by rfl⟩ : syracuseStep 9887183 = 14830775) B14830775
theorem B6591455 : Blo 1951435 6591455 := bstep (se 1 (by rfl) ⟨4943591, by rfl⟩ : syracuseStep 6591455 = 9887183) B9887183
theorem B4394303 : Blo 1951435 4394303 := bstep (se 1 (by rfl) ⟨3295727, by rfl⟩ : syracuseStep 4394303 = 6591455) B6591455
theorem B2929535 : Blo 1951435 2929535 := bstep (se 1 (by rfl) ⟨2197151, by rfl⟩ : syracuseStep 2929535 = 4394303) B4394303
theorem B1953023 : Blo 1951435 1953023 := bstep (se 1 (by rfl) ⟨1464767, by rfl⟩ : syracuseStep 1953023 = 2929535) B2929535
theorem B2929541 : Blo 1951435 2929541 := bbase (se 4 (by rfl) ⟨274644, by rfl⟩ : syracuseStep 2929541 = 549289) (by norm_num)
theorem B1953027 : Blo 1951435 1953027 := bstep (se 1 (by rfl) ⟨1464770, by rfl⟩ : syracuseStep 1953027 = 2929541) B2929541
theorem B3295741 : Blo 1951435 3295741 := bbase (se 3 (by rfl) ⟨617951, by rfl⟩ : syracuseStep 3295741 = 1235903) (by norm_num)
theorem B4394321 : Blo 1951435 4394321 := bstep (se 2 (by rfl) ⟨1647870, by rfl⟩ : syracuseStep 4394321 = 3295741) B3295741
theorem B2929547 : Blo 1951435 2929547 := bstep (se 1 (by rfl) ⟨2197160, by rfl⟩ : syracuseStep 2929547 = 4394321) B4394321
theorem B1953031 : Blo 1951435 1953031 := bstep (se 1 (by rfl) ⟨1464773, by rfl⟩ : syracuseStep 1953031 = 2929547) B2929547
theorem B2197165 : Blo 1951435 2197165 := bbase (se 3 (by rfl) ⟨411968, by rfl⟩ : syracuseStep 2197165 = 823937) (by norm_num)
theorem B2929553 : Blo 1951435 2929553 := bstep (se 2 (by rfl) ⟨1098582, by rfl⟩ : syracuseStep 2929553 = 2197165) B2197165
theorem B1953035 : Blo 1951435 1953035 := bstep (se 1 (by rfl) ⟨1464776, by rfl⟩ : syracuseStep 1953035 = 2929553) B2929553
theorem B6591509 : Blo 1951435 6591509 := bbase (se 6 (by rfl) ⟨154488, by rfl⟩ : syracuseStep 6591509 = 308977) (by norm_num)
theorem B4394339 : Blo 1951435 4394339 := bstep (se 1 (by rfl) ⟨3295754, by rfl⟩ : syracuseStep 4394339 = 6591509) B6591509
theorem B2929559 : Blo 1951435 2929559 := bstep (se 1 (by rfl) ⟨2197169, by rfl⟩ : syracuseStep 2929559 = 4394339) B4394339
theorem B1953039 : Blo 1951435 1953039 := bstep (se 1 (by rfl) ⟨1464779, by rfl⟩ : syracuseStep 1953039 = 2929559) B2929559
theorem B2929565 : Blo 1951435 2929565 := bbase (se 3 (by rfl) ⟨549293, by rfl⟩ : syracuseStep 2929565 = 1098587) (by norm_num)
theorem B1953043 : Blo 1951435 1953043 := bstep (se 1 (by rfl) ⟨1464782, by rfl⟩ : syracuseStep 1953043 = 2929565) B2929565
theorem B4394357 : Blo 1951435 4394357 := bbase (se 5 (by rfl) ⟨205985, by rfl⟩ : syracuseStep 4394357 = 411971) (by norm_num)
theorem B2929571 : Blo 1951435 2929571 := bstep (se 1 (by rfl) ⟨2197178, by rfl⟩ : syracuseStep 2929571 = 4394357) B4394357
theorem B1953047 : Blo 1951435 1953047 := bstep (se 1 (by rfl) ⟨1464785, by rfl⟩ : syracuseStep 1953047 = 2929571) B2929571
theorem B9385237 : Blo 1951435 9385237 := bbase (se 6 (by rfl) ⟨219966, by rfl⟩ : syracuseStep 9385237 = 439933) (by norm_num)
theorem B12513649 : Blo 1951435 12513649 := bstep (se 2 (by rfl) ⟨4692618, by rfl⟩ : syracuseStep 12513649 = 9385237) B9385237
theorem B16684865 : Blo 1951435 16684865 := bstep (se 2 (by rfl) ⟨6256824, by rfl⟩ : syracuseStep 16684865 = 12513649) B12513649
theorem B11123243 : Blo 1951435 11123243 := bstep (se 1 (by rfl) ⟨8342432, by rfl⟩ : syracuseStep 11123243 = 16684865) B16684865
theorem B7415495 : Blo 1951435 7415495 := bstep (se 1 (by rfl) ⟨5561621, by rfl⟩ : syracuseStep 7415495 = 11123243) B11123243
theorem B4943663 : Blo 1951435 4943663 := bstep (se 1 (by rfl) ⟨3707747, by rfl⟩ : syracuseStep 4943663 = 7415495) B7415495
theorem B3295775 : Blo 1951435 3295775 := bstep (se 1 (by rfl) ⟨2471831, by rfl⟩ : syracuseStep 3295775 = 4943663) B4943663
theorem B2197183 : Blo 1951435 2197183 := bstep (se 1 (by rfl) ⟨1647887, by rfl⟩ : syracuseStep 2197183 = 3295775) B3295775
theorem B2929577 : Blo 1951435 2929577 := bstep (se 2 (by rfl) ⟨1098591, by rfl⟩ : syracuseStep 2929577 = 2197183) B2197183
theorem B1953051 : Blo 1951435 1953051 := bstep (se 1 (by rfl) ⟨1464788, by rfl⟩ : syracuseStep 1953051 = 2929577) B2929577
theorem B7415509 : Blo 1951435 7415509 := bbase (se 7 (by rfl) ⟨86900, by rfl⟩ : syracuseStep 7415509 = 173801) (by norm_num)
theorem B9887345 : Blo 1951435 9887345 := bstep (se 2 (by rfl) ⟨3707754, by rfl⟩ : syracuseStep 9887345 = 7415509) B7415509
theorem B6591563 : Blo 1951435 6591563 := bstep (se 1 (by rfl) ⟨4943672, by rfl⟩ : syracuseStep 6591563 = 9887345) B9887345
theorem B4394375 : Blo 1951435 4394375 := bstep (se 1 (by rfl) ⟨3295781, by rfl⟩ : syracuseStep 4394375 = 6591563) B6591563
theorem B2929583 : Blo 1951435 2929583 := bstep (se 1 (by rfl) ⟨2197187, by rfl⟩ : syracuseStep 2929583 = 4394375) B4394375
theorem B1953055 : Blo 1951435 1953055 := bstep (se 1 (by rfl) ⟨1464791, by rfl⟩ : syracuseStep 1953055 = 2929583) B2929583
theorem B2929589 : Blo 1951435 2929589 := bbase (se 5 (by rfl) ⟨137324, by rfl⟩ : syracuseStep 2929589 = 274649) (by norm_num)
theorem B1953059 : Blo 1951435 1953059 := bstep (se 1 (by rfl) ⟨1464794, by rfl⟩ : syracuseStep 1953059 = 2929589) B2929589
theorem B4943693 : Blo 1951435 4943693 := bbase (se 3 (by rfl) ⟨926942, by rfl⟩ : syracuseStep 4943693 = 1853885) (by norm_num)
theorem B3295795 : Blo 1951435 3295795 := bstep (se 1 (by rfl) ⟨2471846, by rfl⟩ : syracuseStep 3295795 = 4943693) B4943693
theorem B4394393 : Blo 1951435 4394393 := bstep (se 2 (by rfl) ⟨1647897, by rfl⟩ : syracuseStep 4394393 = 3295795) B3295795
theorem B2929595 : Blo 1951435 2929595 := bstep (se 1 (by rfl) ⟨2197196, by rfl⟩ : syracuseStep 2929595 = 4394393) B4394393
theorem B1953063 : Blo 1951435 1953063 := bstep (se 1 (by rfl) ⟨1464797, by rfl⟩ : syracuseStep 1953063 = 2929595) B2929595
theorem B2197201 : Blo 1951435 2197201 := bbase (se 2 (by rfl) ⟨823950, by rfl⟩ : syracuseStep 2197201 = 1647901) (by norm_num)
theorem B2929601 : Blo 1951435 2929601 := bstep (se 2 (by rfl) ⟨1098600, by rfl⟩ : syracuseStep 2929601 = 2197201) B2197201
theorem B1953067 : Blo 1951435 1953067 := bstep (se 1 (by rfl) ⟨1464800, by rfl⟩ : syracuseStep 1953067 = 2929601) B2929601
theorem B2257573 : Blo 1951435 2257573 := bbase (se 4 (by rfl) ⟨211647, by rfl⟩ : syracuseStep 2257573 = 423295) (by norm_num)
theorem B3010097 : Blo 1951435 3010097 := bstep (se 2 (by rfl) ⟨1128786, by rfl⟩ : syracuseStep 3010097 = 2257573) B2257573
theorem B2006731 : Blo 1951435 2006731 := bstep (se 1 (by rfl) ⟨1505048, by rfl⟩ : syracuseStep 2006731 = 3010097) B3010097
theorem B2675641 : Blo 1951435 2675641 := bstep (se 2 (by rfl) ⟨1003365, by rfl⟩ : syracuseStep 2675641 = 2006731) B2006731
theorem B3567521 : Blo 1951435 3567521 := bstep (se 2 (by rfl) ⟨1337820, by rfl⟩ : syracuseStep 3567521 = 2675641) B2675641
theorem B9513389 : Blo 1951435 9513389 := bstep (se 3 (by rfl) ⟨1783760, by rfl⟩ : syracuseStep 9513389 = 3567521) B3567521
theorem B6342259 : Blo 1951435 6342259 := bstep (se 1 (by rfl) ⟨4756694, by rfl⟩ : syracuseStep 6342259 = 9513389) B9513389
theorem B8456345 : Blo 1951435 8456345 := bstep (se 2 (by rfl) ⟨3171129, by rfl⟩ : syracuseStep 8456345 = 6342259) B6342259
theorem B5637563 : Blo 1951435 5637563 := bstep (se 1 (by rfl) ⟨4228172, by rfl⟩ : syracuseStep 5637563 = 8456345) B8456345
theorem B3758375 : Blo 1951435 3758375 := bstep (se 1 (by rfl) ⟨2818781, by rfl⟩ : syracuseStep 3758375 = 5637563) B5637563
theorem B2505583 : Blo 1951435 2505583 := bstep (se 1 (by rfl) ⟨1879187, by rfl⟩ : syracuseStep 2505583 = 3758375) B3758375
theorem B3340777 : Blo 1951435 3340777 := bstep (se 2 (by rfl) ⟨1252791, by rfl⟩ : syracuseStep 3340777 = 2505583) B2505583
theorem B4454369 : Blo 1951435 4454369 := bstep (se 2 (by rfl) ⟨1670388, by rfl⟩ : syracuseStep 4454369 = 3340777) B3340777
theorem B2969579 : Blo 1951435 2969579 := bstep (se 1 (by rfl) ⟨2227184, by rfl⟩ : syracuseStep 2969579 = 4454369) B4454369
theorem B7918877 : Blo 1951435 7918877 := bstep (se 3 (by rfl) ⟨1484789, by rfl⟩ : syracuseStep 7918877 = 2969579) B2969579
theorem B5279251 : Blo 1951435 5279251 := bstep (se 1 (by rfl) ⟨3959438, by rfl⟩ : syracuseStep 5279251 = 7918877) B7918877
theorem B7039001 : Blo 1951435 7039001 := bstep (se 2 (by rfl) ⟨2639625, by rfl⟩ : syracuseStep 7039001 = 5279251) B5279251
theorem B4692667 : Blo 1951435 4692667 := bstep (se 1 (by rfl) ⟨3519500, by rfl⟩ : syracuseStep 4692667 = 7039001) B7039001
theorem B6256889 : Blo 1951435 6256889 := bstep (se 2 (by rfl) ⟨2346333, by rfl⟩ : syracuseStep 6256889 = 4692667) B4692667
theorem B4171259 : Blo 1951435 4171259 := bstep (se 1 (by rfl) ⟨3128444, by rfl⟩ : syracuseStep 4171259 = 6256889) B6256889
theorem B2780839 : Blo 1951435 2780839 := bstep (se 1 (by rfl) ⟨2085629, by rfl⟩ : syracuseStep 2780839 = 4171259) B4171259
theorem B3707785 : Blo 1951435 3707785 := bstep (se 2 (by rfl) ⟨1390419, by rfl⟩ : syracuseStep 3707785 = 2780839) B2780839
theorem B4943713 : Blo 1951435 4943713 := bstep (se 2 (by rfl) ⟨1853892, by rfl⟩ : syracuseStep 4943713 = 3707785) B3707785
theorem B6591617 : Blo 1951435 6591617 := bstep (se 2 (by rfl) ⟨2471856, by rfl⟩ : syracuseStep 6591617 = 4943713) B4943713
theorem B4394411 : Blo 1951435 4394411 := bstep (se 1 (by rfl) ⟨3295808, by rfl⟩ : syracuseStep 4394411 = 6591617) B6591617
theorem B2929607 : Blo 1951435 2929607 := bstep (se 1 (by rfl) ⟨2197205, by rfl⟩ : syracuseStep 2929607 = 4394411) B4394411
theorem B1953071 : Blo 1951435 1953071 := bstep (se 1 (by rfl) ⟨1464803, by rfl⟩ : syracuseStep 1953071 = 2929607) B2929607
theorem B2929613 : Blo 1951435 2929613 := bbase (se 3 (by rfl) ⟨549302, by rfl⟩ : syracuseStep 2929613 = 1098605) (by norm_num)
theorem B1953075 : Blo 1951435 1953075 := bstep (se 1 (by rfl) ⟨1464806, by rfl⟩ : syracuseStep 1953075 = 2929613) B2929613
theorem B4394429 : Blo 1951435 4394429 := bbase (se 3 (by rfl) ⟨823955, by rfl⟩ : syracuseStep 4394429 = 1647911) (by norm_num)
theorem B2929619 : Blo 1951435 2929619 := bstep (se 1 (by rfl) ⟨2197214, by rfl⟩ : syracuseStep 2929619 = 4394429) B4394429
theorem B1953079 : Blo 1951435 1953079 := bstep (se 1 (by rfl) ⟨1464809, by rfl⟩ : syracuseStep 1953079 = 2929619) B2929619
theorem B3295829 : Blo 1951435 3295829 := bbase (se 8 (by rfl) ⟨19311, by rfl⟩ : syracuseStep 3295829 = 38623) (by norm_num)
theorem B2197219 : Blo 1951435 2197219 := bstep (se 1 (by rfl) ⟨1647914, by rfl⟩ : syracuseStep 2197219 = 3295829) B3295829
theorem B2929625 : Blo 1951435 2929625 := bstep (se 2 (by rfl) ⟨1098609, by rfl⟩ : syracuseStep 2929625 = 2197219) B2197219
theorem B1953083 : Blo 1951435 1953083 := bstep (se 1 (by rfl) ⟨1464812, by rfl⟩ : syracuseStep 1953083 = 2929625) B2929625
theorem B4454405 : Blo 1951435 4454405 := bbase (se 4 (by rfl) ⟨417600, by rfl⟩ : syracuseStep 4454405 = 835201) (by norm_num)
theorem B2969603 : Blo 1951435 2969603 := bstep (se 1 (by rfl) ⟨2227202, by rfl⟩ : syracuseStep 2969603 = 4454405) B4454405
theorem B1979735 : Blo 1951435 1979735 := bstep (se 1 (by rfl) ⟨1484801, by rfl⟩ : syracuseStep 1979735 = 2969603) B2969603
theorem B5279293 : Blo 1951435 5279293 := bstep (se 3 (by rfl) ⟨989867, by rfl⟩ : syracuseStep 5279293 = 1979735) B1979735
theorem B7039057 : Blo 1951435 7039057 := bstep (se 2 (by rfl) ⟨2639646, by rfl⟩ : syracuseStep 7039057 = 5279293) B5279293
theorem B9385409 : Blo 1951435 9385409 := bstep (se 2 (by rfl) ⟨3519528, by rfl⟩ : syracuseStep 9385409 = 7039057) B7039057
theorem B6256939 : Blo 1951435 6256939 := bstep (se 1 (by rfl) ⟨4692704, by rfl⟩ : syracuseStep 6256939 = 9385409) B9385409
theorem B8342585 : Blo 1951435 8342585 := bstep (se 2 (by rfl) ⟨3128469, by rfl⟩ : syracuseStep 8342585 = 6256939) B6256939
theorem B5561723 : Blo 1951435 5561723 := bstep (se 1 (by rfl) ⟨4171292, by rfl⟩ : syracuseStep 5561723 = 8342585) B8342585
theorem B14831261 : Blo 1951435 14831261 := bstep (se 3 (by rfl) ⟨2780861, by rfl⟩ : syracuseStep 14831261 = 5561723) B5561723
theorem B9887507 : Blo 1951435 9887507 := bstep (se 1 (by rfl) ⟨7415630, by rfl⟩ : syracuseStep 9887507 = 14831261) B14831261
theorem B6591671 : Blo 1951435 6591671 := bstep (se 1 (by rfl) ⟨4943753, by rfl⟩ : syracuseStep 6591671 = 9887507) B9887507
theorem B4394447 : Blo 1951435 4394447 := bstep (se 1 (by rfl) ⟨3295835, by rfl⟩ : syracuseStep 4394447 = 6591671) B6591671
theorem B2929631 : Blo 1951435 2929631 := bstep (se 1 (by rfl) ⟨2197223, by rfl⟩ : syracuseStep 2929631 = 4394447) B4394447
theorem B1953087 : Blo 1951435 1953087 := bstep (se 1 (by rfl) ⟨1464815, by rfl⟩ : syracuseStep 1953087 = 2929631) B2929631
theorem B2929637 : Blo 1951435 2929637 := bbase (se 4 (by rfl) ⟨274653, by rfl⟩ : syracuseStep 2929637 = 549307) (by norm_num)
theorem B1953091 : Blo 1951435 1953091 := bstep (se 1 (by rfl) ⟨1464818, by rfl⟩ : syracuseStep 1953091 = 2929637) B2929637
theorem B4692725 : Blo 1951435 4692725 := bbase (se 5 (by rfl) ⟨219971, by rfl⟩ : syracuseStep 4692725 = 439943) (by norm_num)
theorem B3128483 : Blo 1951435 3128483 := bstep (se 1 (by rfl) ⟨2346362, by rfl⟩ : syracuseStep 3128483 = 4692725) B4692725
theorem B8342621 : Blo 1951435 8342621 := bstep (se 3 (by rfl) ⟨1564241, by rfl⟩ : syracuseStep 8342621 = 3128483) B3128483
theorem B5561747 : Blo 1951435 5561747 := bstep (se 1 (by rfl) ⟨4171310, by rfl⟩ : syracuseStep 5561747 = 8342621) B8342621
theorem B3707831 : Blo 1951435 3707831 := bstep (se 1 (by rfl) ⟨2780873, by rfl⟩ : syracuseStep 3707831 = 5561747) B5561747
theorem B2471887 : Blo 1951435 2471887 := bstep (se 1 (by rfl) ⟨1853915, by rfl⟩ : syracuseStep 2471887 = 3707831) B3707831
theorem B3295849 : Blo 1951435 3295849 := bstep (se 2 (by rfl) ⟨1235943, by rfl⟩ : syracuseStep 3295849 = 2471887) B2471887
theorem B4394465 : Blo 1951435 4394465 := bstep (se 2 (by rfl) ⟨1647924, by rfl⟩ : syracuseStep 4394465 = 3295849) B3295849
theorem B2929643 : Blo 1951435 2929643 := bstep (se 1 (by rfl) ⟨2197232, by rfl⟩ : syracuseStep 2929643 = 4394465) B4394465
theorem B1953095 : Blo 1951435 1953095 := bstep (se 1 (by rfl) ⟨1464821, by rfl⟩ : syracuseStep 1953095 = 2929643) B2929643
theorem B2197237 : Blo 1951435 2197237 := bbase (se 5 (by rfl) ⟨102995, by rfl⟩ : syracuseStep 2197237 = 205991) (by norm_num)
theorem B2929649 : Blo 1951435 2929649 := bstep (se 2 (by rfl) ⟨1098618, by rfl⟩ : syracuseStep 2929649 = 2197237) B2197237
theorem B1953099 : Blo 1951435 1953099 := bstep (se 1 (by rfl) ⟨1464824, by rfl⟩ : syracuseStep 1953099 = 2929649) B2929649
theorem B2471897 : Blo 1951435 2471897 := bbase (se 2 (by rfl) ⟨926961, by rfl⟩ : syracuseStep 2471897 = 1853923) (by norm_num)
theorem B6591725 : Blo 1951435 6591725 := bstep (se 3 (by rfl) ⟨1235948, by rfl⟩ : syracuseStep 6591725 = 2471897) B2471897
theorem B4394483 : Blo 1951435 4394483 := bstep (se 1 (by rfl) ⟨3295862, by rfl⟩ : syracuseStep 4394483 = 6591725) B6591725
theorem B2929655 : Blo 1951435 2929655 := bstep (se 1 (by rfl) ⟨2197241, by rfl⟩ : syracuseStep 2929655 = 4394483) B4394483
theorem B1953103 : Blo 1951435 1953103 := bstep (se 1 (by rfl) ⟨1464827, by rfl⟩ : syracuseStep 1953103 = 2929655) B2929655
theorem B2929661 : Blo 1951435 2929661 := bbase (se 3 (by rfl) ⟨549311, by rfl⟩ : syracuseStep 2929661 = 1098623) (by norm_num)
theorem B1953107 : Blo 1951435 1953107 := bstep (se 1 (by rfl) ⟨1464830, by rfl⟩ : syracuseStep 1953107 = 2929661) B2929661
theorem B4394501 : Blo 1951435 4394501 := bbase (se 4 (by rfl) ⟨411984, by rfl⟩ : syracuseStep 4394501 = 823969) (by norm_num)
theorem B2929667 : Blo 1951435 2929667 := bstep (se 1 (by rfl) ⟨2197250, by rfl⟩ : syracuseStep 2929667 = 4394501) B4394501
theorem B1953111 : Blo 1951435 1953111 := bstep (se 1 (by rfl) ⟨1464833, by rfl⟩ : syracuseStep 1953111 = 2929667) B2929667
theorem B3707869 : Blo 1951435 3707869 := bbase (se 3 (by rfl) ⟨695225, by rfl⟩ : syracuseStep 3707869 = 1390451) (by norm_num)
theorem B4943825 : Blo 1951435 4943825 := bstep (se 2 (by rfl) ⟨1853934, by rfl⟩ : syracuseStep 4943825 = 3707869) B3707869
theorem B3295883 : Blo 1951435 3295883 := bstep (se 1 (by rfl) ⟨2471912, by rfl⟩ : syracuseStep 3295883 = 4943825) B4943825
theorem B2197255 : Blo 1951435 2197255 := bstep (se 1 (by rfl) ⟨1647941, by rfl⟩ : syracuseStep 2197255 = 3295883) B3295883
theorem B2929673 : Blo 1951435 2929673 := bstep (se 2 (by rfl) ⟨1098627, by rfl⟩ : syracuseStep 2929673 = 2197255) B2197255
theorem B1953115 : Blo 1951435 1953115 := bstep (se 1 (by rfl) ⟨1464836, by rfl⟩ : syracuseStep 1953115 = 2929673) B2929673
theorem B9887669 : Blo 1951435 9887669 := bbase (se 5 (by rfl) ⟨463484, by rfl⟩ : syracuseStep 9887669 = 926969) (by norm_num)
theorem B6591779 : Blo 1951435 6591779 := bstep (se 1 (by rfl) ⟨4943834, by rfl⟩ : syracuseStep 6591779 = 9887669) B9887669
theorem B4394519 : Blo 1951435 4394519 := bstep (se 1 (by rfl) ⟨3295889, by rfl⟩ : syracuseStep 4394519 = 6591779) B6591779
theorem B2929679 : Blo 1951435 2929679 := bstep (se 1 (by rfl) ⟨2197259, by rfl⟩ : syracuseStep 2929679 = 4394519) B4394519
theorem B1953119 : Blo 1951435 1953119 := bstep (se 1 (by rfl) ⟨1464839, by rfl⟩ : syracuseStep 1953119 = 2929679) B2929679
theorem B2929685 : Blo 1951435 2929685 := bbase (se 6 (by rfl) ⟨68664, by rfl⟩ : syracuseStep 2929685 = 137329) (by norm_num)
theorem B1953123 : Blo 1951435 1953123 := bstep (se 1 (by rfl) ⟨1464842, by rfl⟩ : syracuseStep 1953123 = 2929685) B2929685
theorem B3386453 : Blo 1951435 3386453 := bbase (se 8 (by rfl) ⟨19842, by rfl⟩ : syracuseStep 3386453 = 39685) (by norm_num)
theorem B9030541 : Blo 1951435 9030541 := bstep (se 3 (by rfl) ⟨1693226, by rfl⟩ : syracuseStep 9030541 = 3386453) B3386453
theorem B12040721 : Blo 1951435 12040721 := bstep (se 2 (by rfl) ⟨4515270, by rfl⟩ : syracuseStep 12040721 = 9030541) B9030541
theorem B8027147 : Blo 1951435 8027147 := bstep (se 1 (by rfl) ⟨6020360, by rfl⟩ : syracuseStep 8027147 = 12040721) B12040721
theorem B21405725 : Blo 1951435 21405725 := bstep (se 3 (by rfl) ⟨4013573, by rfl⟩ : syracuseStep 21405725 = 8027147) B8027147
theorem B14270483 : Blo 1951435 14270483 := bstep (se 1 (by rfl) ⟨10702862, by rfl⟩ : syracuseStep 14270483 = 21405725) B21405725
theorem B9513655 : Blo 1951435 9513655 := bstep (se 1 (by rfl) ⟨7135241, by rfl⟩ : syracuseStep 9513655 = 14270483) B14270483
theorem B50739493 : Blo 1951435 50739493 := bstep (se 4 (by rfl) ⟨4756827, by rfl⟩ : syracuseStep 50739493 = 9513655) B9513655
theorem B67652657 : Blo 1951435 67652657 := bstep (se 2 (by rfl) ⟨25369746, by rfl⟩ : syracuseStep 67652657 = 50739493) B50739493
theorem B45101771 : Blo 1951435 45101771 := bstep (se 1 (by rfl) ⟨33826328, by rfl⟩ : syracuseStep 45101771 = 67652657) B67652657
theorem B30067847 : Blo 1951435 30067847 := bstep (se 1 (by rfl) ⟨22550885, by rfl⟩ : syracuseStep 30067847 = 45101771) B45101771
theorem B20045231 : Blo 1951435 20045231 := bstep (se 1 (by rfl) ⟨15033923, by rfl⟩ : syracuseStep 20045231 = 30067847) B30067847
theorem B13363487 : Blo 1951435 13363487 := bstep (se 1 (by rfl) ⟨10022615, by rfl⟩ : syracuseStep 13363487 = 20045231) B20045231
theorem B8908991 : Blo 1951435 8908991 := bstep (se 1 (by rfl) ⟨6681743, by rfl⟩ : syracuseStep 8908991 = 13363487) B13363487
theorem B5939327 : Blo 1951435 5939327 := bstep (se 1 (by rfl) ⟨4454495, by rfl⟩ : syracuseStep 5939327 = 8908991) B8908991
theorem B3959551 : Blo 1951435 3959551 := bstep (se 1 (by rfl) ⟨2969663, by rfl⟩ : syracuseStep 3959551 = 5939327) B5939327
theorem B5279401 : Blo 1951435 5279401 := bstep (se 2 (by rfl) ⟨1979775, by rfl⟩ : syracuseStep 5279401 = 3959551) B3959551
theorem B28156805 : Blo 1951435 28156805 := bstep (se 4 (by rfl) ⟨2639700, by rfl⟩ : syracuseStep 28156805 = 5279401) B5279401
theorem B18771203 : Blo 1951435 18771203 := bstep (se 1 (by rfl) ⟨14078402, by rfl⟩ : syracuseStep 18771203 = 28156805) B28156805
theorem B12514135 : Blo 1951435 12514135 := bstep (se 1 (by rfl) ⟨9385601, by rfl⟩ : syracuseStep 12514135 = 18771203) B18771203
theorem B16685513 : Blo 1951435 16685513 := bstep (se 2 (by rfl) ⟨6257067, by rfl⟩ : syracuseStep 16685513 = 12514135) B12514135
theorem B11123675 : Blo 1951435 11123675 := bstep (se 1 (by rfl) ⟨8342756, by rfl⟩ : syracuseStep 11123675 = 16685513) B16685513
theorem B7415783 : Blo 1951435 7415783 := bstep (se 1 (by rfl) ⟨5561837, by rfl⟩ : syracuseStep 7415783 = 11123675) B11123675
theorem B4943855 : Blo 1951435 4943855 := bstep (se 1 (by rfl) ⟨3707891, by rfl⟩ : syracuseStep 4943855 = 7415783) B7415783
theorem B3295903 : Blo 1951435 3295903 := bstep (se 1 (by rfl) ⟨2471927, by rfl⟩ : syracuseStep 3295903 = 4943855) B4943855
theorem B4394537 : Blo 1951435 4394537 := bstep (se 2 (by rfl) ⟨1647951, by rfl⟩ : syracuseStep 4394537 = 3295903) B3295903
theorem B2929691 : Blo 1951435 2929691 := bstep (se 1 (by rfl) ⟨2197268, by rfl⟩ : syracuseStep 2929691 = 4394537) B4394537
theorem B1953127 : Blo 1951435 1953127 := bstep (se 1 (by rfl) ⟨1464845, by rfl⟩ : syracuseStep 1953127 = 2929691) B2929691
theorem B2197273 : Blo 1951435 2197273 := bbase (se 2 (by rfl) ⟨823977, by rfl⟩ : syracuseStep 2197273 = 1647955) (by norm_num)
theorem B2929697 : Blo 1951435 2929697 := bstep (se 2 (by rfl) ⟨1098636, by rfl⟩ : syracuseStep 2929697 = 2197273) B2197273
theorem B1953131 : Blo 1951435 1953131 := bstep (se 1 (by rfl) ⟨1464848, by rfl⟩ : syracuseStep 1953131 = 2929697) B2929697
theorem B7415813 : Blo 1951435 7415813 := bbase (se 4 (by rfl) ⟨695232, by rfl⟩ : syracuseStep 7415813 = 1390465) (by norm_num)
theorem B4943875 : Blo 1951435 4943875 := bstep (se 1 (by rfl) ⟨3707906, by rfl⟩ : syracuseStep 4943875 = 7415813) B7415813
theorem B6591833 : Blo 1951435 6591833 := bstep (se 2 (by rfl) ⟨2471937, by rfl⟩ : syracuseStep 6591833 = 4943875) B4943875
theorem B4394555 : Blo 1951435 4394555 := bstep (se 1 (by rfl) ⟨3295916, by rfl⟩ : syracuseStep 4394555 = 6591833) B6591833
theorem B2929703 : Blo 1951435 2929703 := bstep (se 1 (by rfl) ⟨2197277, by rfl⟩ : syracuseStep 2929703 = 4394555) B4394555
theorem B1953135 : Blo 1951435 1953135 := bstep (se 1 (by rfl) ⟨1464851, by rfl⟩ : syracuseStep 1953135 = 2929703) B2929703
theorem B2929709 : Blo 1951435 2929709 := bbase (se 3 (by rfl) ⟨549320, by rfl⟩ : syracuseStep 2929709 = 1098641) (by norm_num)
theorem B1953139 : Blo 1951435 1953139 := bstep (se 1 (by rfl) ⟨1464854, by rfl⟩ : syracuseStep 1953139 = 2929709) B2929709
theorem B4394573 : Blo 1951435 4394573 := bbase (se 3 (by rfl) ⟨823982, by rfl⟩ : syracuseStep 4394573 = 1647965) (by norm_num)
theorem B2929715 : Blo 1951435 2929715 := bstep (se 1 (by rfl) ⟨2197286, by rfl⟩ : syracuseStep 2929715 = 4394573) B4394573
theorem B1953143 : Blo 1951435 1953143 := bstep (se 1 (by rfl) ⟨1464857, by rfl⟩ : syracuseStep 1953143 = 2929715) B2929715
theorem B2471953 : Blo 1951435 2471953 := bbase (se 2 (by rfl) ⟨926982, by rfl⟩ : syracuseStep 2471953 = 1853965) (by norm_num)
theorem B3295937 : Blo 1951435 3295937 := bstep (se 2 (by rfl) ⟨1235976, by rfl⟩ : syracuseStep 3295937 = 2471953) B2471953
theorem B2197291 : Blo 1951435 2197291 := bstep (se 1 (by rfl) ⟨1647968, by rfl⟩ : syracuseStep 2197291 = 3295937) B3295937
theorem B2929721 : Blo 1951435 2929721 := bstep (se 2 (by rfl) ⟨1098645, by rfl⟩ : syracuseStep 2929721 = 2197291) B2197291
theorem B1953147 : Blo 1951435 1953147 := bstep (se 1 (by rfl) ⟨1464860, by rfl⟩ : syracuseStep 1953147 = 2929721) B2929721
theorem B4171429 : Blo 1951435 4171429 := bbase (se 4 (by rfl) ⟨391071, by rfl⟩ : syracuseStep 4171429 = 782143) (by norm_num)
theorem B22247621 : Blo 1951435 22247621 := bstep (se 4 (by rfl) ⟨2085714, by rfl⟩ : syracuseStep 22247621 = 4171429) B4171429
theorem B14831747 : Blo 1951435 14831747 := bstep (se 1 (by rfl) ⟨11123810, by rfl⟩ : syracuseStep 14831747 = 22247621) B22247621
theorem B9887831 : Blo 1951435 9887831 := bstep (se 1 (by rfl) ⟨7415873, by rfl⟩ : syracuseStep 9887831 = 14831747) B14831747
theorem B6591887 : Blo 1951435 6591887 := bstep (se 1 (by rfl) ⟨4943915, by rfl⟩ : syracuseStep 6591887 = 9887831) B9887831
theorem B4394591 : Blo 1951435 4394591 := bstep (se 1 (by rfl) ⟨3295943, by rfl⟩ : syracuseStep 4394591 = 6591887) B6591887
theorem B2929727 : Blo 1951435 2929727 := bstep (se 1 (by rfl) ⟨2197295, by rfl⟩ : syracuseStep 2929727 = 4394591) B4394591
theorem B1953151 : Blo 1951435 1953151 := bstep (se 1 (by rfl) ⟨1464863, by rfl⟩ : syracuseStep 1953151 = 2929727) B2929727
theorem B2929733 : Blo 1951435 2929733 := bbase (se 4 (by rfl) ⟨274662, by rfl⟩ : syracuseStep 2929733 = 549325) (by norm_num)
theorem B1953155 : Blo 1951435 1953155 := bstep (se 1 (by rfl) ⟨1464866, by rfl⟩ : syracuseStep 1953155 = 2929733) B2929733
theorem B3295957 : Blo 1951435 3295957 := bbase (se 7 (by rfl) ⟨38624, by rfl⟩ : syracuseStep 3295957 = 77249) (by norm_num)
theorem B4394609 : Blo 1951435 4394609 := bstep (se 2 (by rfl) ⟨1647978, by rfl⟩ : syracuseStep 4394609 = 3295957) B3295957
theorem B2929739 : Blo 1951435 2929739 := bstep (se 1 (by rfl) ⟨2197304, by rfl⟩ : syracuseStep 2929739 = 4394609) B4394609
theorem B1953159 : Blo 1951435 1953159 := bstep (se 1 (by rfl) ⟨1464869, by rfl⟩ : syracuseStep 1953159 = 2929739) B2929739
theorem B2197309 : Blo 1951435 2197309 := bbase (se 3 (by rfl) ⟨411995, by rfl⟩ : syracuseStep 2197309 = 823991) (by norm_num)
theorem B2929745 : Blo 1951435 2929745 := bstep (se 2 (by rfl) ⟨1098654, by rfl⟩ : syracuseStep 2929745 = 2197309) B2197309
theorem B1953163 : Blo 1951435 1953163 := bstep (se 1 (by rfl) ⟨1464872, by rfl⟩ : syracuseStep 1953163 = 2929745) B2929745
theorem B6591941 : Blo 1951435 6591941 := bbase (se 4 (by rfl) ⟨617994, by rfl⟩ : syracuseStep 6591941 = 1235989) (by norm_num)
theorem B4394627 : Blo 1951435 4394627 := bstep (se 1 (by rfl) ⟨3295970, by rfl⟩ : syracuseStep 4394627 = 6591941) B6591941
theorem B2929751 : Blo 1951435 2929751 := bstep (se 1 (by rfl) ⟨2197313, by rfl⟩ : syracuseStep 2929751 = 4394627) B4394627
theorem B1953167 : Blo 1951435 1953167 := bstep (se 1 (by rfl) ⟨1464875, by rfl⟩ : syracuseStep 1953167 = 2929751) B2929751
theorem B2929757 : Blo 1951435 2929757 := bbase (se 3 (by rfl) ⟨549329, by rfl⟩ : syracuseStep 2929757 = 1098659) (by norm_num)
theorem B1953171 : Blo 1951435 1953171 := bstep (se 1 (by rfl) ⟨1464878, by rfl⟩ : syracuseStep 1953171 = 2929757) B2929757
theorem B4394645 : Blo 1951435 4394645 := bbase (se 6 (by rfl) ⟨102999, by rfl⟩ : syracuseStep 4394645 = 205999) (by norm_num)
theorem B2929763 : Blo 1951435 2929763 := bstep (se 1 (by rfl) ⟨2197322, by rfl⟩ : syracuseStep 2929763 = 4394645) B4394645
theorem B1953175 : Blo 1951435 1953175 := bstep (se 1 (by rfl) ⟨1464881, by rfl⟩ : syracuseStep 1953175 = 2929763) B2929763
theorem B2085745 : Blo 1951435 2085745 := bbase (se 2 (by rfl) ⟨782154, by rfl⟩ : syracuseStep 2085745 = 1564309) (by norm_num)
theorem B2780993 : Blo 1951435 2780993 := bstep (se 2 (by rfl) ⟨1042872, by rfl⟩ : syracuseStep 2780993 = 2085745) B2085745
theorem B7415981 : Blo 1951435 7415981 := bstep (se 3 (by rfl) ⟨1390496, by rfl⟩ : syracuseStep 7415981 = 2780993) B2780993
theorem B4943987 : Blo 1951435 4943987 := bstep (se 1 (by rfl) ⟨3707990, by rfl⟩ : syracuseStep 4943987 = 7415981) B7415981
theorem B3295991 : Blo 1951435 3295991 := bstep (se 1 (by rfl) ⟨2471993, by rfl⟩ : syracuseStep 3295991 = 4943987) B4943987
theorem B2197327 : Blo 1951435 2197327 := bstep (se 1 (by rfl) ⟨1647995, by rfl⟩ : syracuseStep 2197327 = 3295991) B3295991
theorem B2929769 : Blo 1951435 2929769 := bstep (se 2 (by rfl) ⟨1098663, by rfl⟩ : syracuseStep 2929769 = 2197327) B2197327
theorem B1953179 : Blo 1951435 1953179 := bstep (se 1 (by rfl) ⟨1464884, by rfl⟩ : syracuseStep 1953179 = 2929769) B2929769
theorem B4821869 : Blo 1951435 4821869 := bbase (se 3 (by rfl) ⟨904100, by rfl⟩ : syracuseStep 4821869 = 1808201) (by norm_num)
theorem B3214579 : Blo 1951435 3214579 := bstep (se 1 (by rfl) ⟨2410934, by rfl⟩ : syracuseStep 3214579 = 4821869) B4821869
theorem B4286105 : Blo 1951435 4286105 := bstep (se 2 (by rfl) ⟨1607289, by rfl⟩ : syracuseStep 4286105 = 3214579) B3214579
theorem B2857403 : Blo 1951435 2857403 := bstep (se 1 (by rfl) ⟨2143052, by rfl⟩ : syracuseStep 2857403 = 4286105) B4286105
theorem B7619741 : Blo 1951435 7619741 := bstep (se 3 (by rfl) ⟨1428701, by rfl⟩ : syracuseStep 7619741 = 2857403) B2857403
theorem B5079827 : Blo 1951435 5079827 := bstep (se 1 (by rfl) ⟨3809870, by rfl⟩ : syracuseStep 5079827 = 7619741) B7619741
theorem B3386551 : Blo 1951435 3386551 := bstep (se 1 (by rfl) ⟨2539913, by rfl⟩ : syracuseStep 3386551 = 5079827) B5079827
theorem B4515401 : Blo 1951435 4515401 := bstep (se 2 (by rfl) ⟨1693275, by rfl⟩ : syracuseStep 4515401 = 3386551) B3386551
theorem B3010267 : Blo 1951435 3010267 := bstep (se 1 (by rfl) ⟨2257700, by rfl⟩ : syracuseStep 3010267 = 4515401) B4515401
theorem B16054757 : Blo 1951435 16054757 := bstep (se 4 (by rfl) ⟨1505133, by rfl⟩ : syracuseStep 16054757 = 3010267) B3010267
theorem B10703171 : Blo 1951435 10703171 := bstep (se 1 (by rfl) ⟨8027378, by rfl⟩ : syracuseStep 10703171 = 16054757) B16054757
theorem B7135447 : Blo 1951435 7135447 := bstep (se 1 (by rfl) ⟨5351585, by rfl⟩ : syracuseStep 7135447 = 10703171) B10703171
theorem B9513929 : Blo 1951435 9513929 := bstep (se 2 (by rfl) ⟨3567723, by rfl⟩ : syracuseStep 9513929 = 7135447) B7135447
theorem B6342619 : Blo 1951435 6342619 := bstep (se 1 (by rfl) ⟨4756964, by rfl⟩ : syracuseStep 6342619 = 9513929) B9513929
theorem B8456825 : Blo 1951435 8456825 := bstep (se 2 (by rfl) ⟨3171309, by rfl⟩ : syracuseStep 8456825 = 6342619) B6342619
theorem B22551533 : Blo 1951435 22551533 := bstep (se 3 (by rfl) ⟨4228412, by rfl⟩ : syracuseStep 22551533 = 8456825) B8456825
theorem B15034355 : Blo 1951435 15034355 := bstep (se 1 (by rfl) ⟨11275766, by rfl⟩ : syracuseStep 15034355 = 22551533) B22551533
theorem B10022903 : Blo 1951435 10022903 := bstep (se 1 (by rfl) ⟨7517177, by rfl⟩ : syracuseStep 10022903 = 15034355) B15034355
theorem B6681935 : Blo 1951435 6681935 := bstep (se 1 (by rfl) ⟨5011451, by rfl⟩ : syracuseStep 6681935 = 10022903) B10022903
theorem B4454623 : Blo 1951435 4454623 := bstep (se 1 (by rfl) ⟨3340967, by rfl⟩ : syracuseStep 4454623 = 6681935) B6681935
theorem B5939497 : Blo 1951435 5939497 := bstep (se 2 (by rfl) ⟨2227311, by rfl⟩ : syracuseStep 5939497 = 4454623) B4454623
theorem B7919329 : Blo 1951435 7919329 := bstep (se 2 (by rfl) ⟨2969748, by rfl⟩ : syracuseStep 7919329 = 5939497) B5939497
theorem B10559105 : Blo 1951435 10559105 := bstep (se 2 (by rfl) ⟨3959664, by rfl⟩ : syracuseStep 10559105 = 7919329) B7919329
theorem B7039403 : Blo 1951435 7039403 := bstep (se 1 (by rfl) ⟨5279552, by rfl⟩ : syracuseStep 7039403 = 10559105) B10559105
theorem B4692935 : Blo 1951435 4692935 := bstep (se 1 (by rfl) ⟨3519701, by rfl⟩ : syracuseStep 4692935 = 7039403) B7039403
theorem B12514493 : Blo 1951435 12514493 := bstep (se 3 (by rfl) ⟨2346467, by rfl⟩ : syracuseStep 12514493 = 4692935) B4692935
theorem B8342995 : Blo 1951435 8342995 := bstep (se 1 (by rfl) ⟨6257246, by rfl⟩ : syracuseStep 8342995 = 12514493) B12514493
theorem B11123993 : Blo 1951435 11123993 := bstep (se 2 (by rfl) ⟨4171497, by rfl⟩ : syracuseStep 11123993 = 8342995) B8342995
theorem B7415995 : Blo 1951435 7415995 := bstep (se 1 (by rfl) ⟨5561996, by rfl⟩ : syracuseStep 7415995 = 11123993) B11123993
theorem B9887993 : Blo 1951435 9887993 := bstep (se 2 (by rfl) ⟨3707997, by rfl⟩ : syracuseStep 9887993 = 7415995) B7415995
theorem B6591995 : Blo 1951435 6591995 := bstep (se 1 (by rfl) ⟨4943996, by rfl⟩ : syracuseStep 6591995 = 9887993) B9887993
theorem B4394663 : Blo 1951435 4394663 := bstep (se 1 (by rfl) ⟨3295997, by rfl⟩ : syracuseStep 4394663 = 6591995) B6591995
theorem B2929775 : Blo 1951435 2929775 := bstep (se 1 (by rfl) ⟨2197331, by rfl⟩ : syracuseStep 2929775 = 4394663) B4394663
theorem B1953183 : Blo 1951435 1953183 := bstep (se 1 (by rfl) ⟨1464887, by rfl⟩ : syracuseStep 1953183 = 2929775) B2929775
theorem B2929781 : Blo 1951435 2929781 := bbase (se 5 (by rfl) ⟨137333, by rfl⟩ : syracuseStep 2929781 = 274667) (by norm_num)
theorem B1953187 : Blo 1951435 1953187 := bstep (se 1 (by rfl) ⟨1464890, by rfl⟩ : syracuseStep 1953187 = 2929781) B2929781
theorem B3708013 : Blo 1951435 3708013 := bbase (se 3 (by rfl) ⟨695252, by rfl⟩ : syracuseStep 3708013 = 1390505) (by norm_num)
theorem B4944017 : Blo 1951435 4944017 := bstep (se 2 (by rfl) ⟨1854006, by rfl⟩ : syracuseStep 4944017 = 3708013) B3708013
theorem B3296011 : Blo 1951435 3296011 := bstep (se 1 (by rfl) ⟨2472008, by rfl⟩ : syracuseStep 3296011 = 4944017) B4944017
theorem B4394681 : Blo 1951435 4394681 := bstep (se 2 (by rfl) ⟨1648005, by rfl⟩ : syracuseStep 4394681 = 3296011) B3296011
theorem B2929787 : Blo 1951435 2929787 := bstep (se 1 (by rfl) ⟨2197340, by rfl⟩ : syracuseStep 2929787 = 4394681) B4394681
theorem B1953191 : Blo 1951435 1953191 := bstep (se 1 (by rfl) ⟨1464893, by rfl⟩ : syracuseStep 1953191 = 2929787) B2929787
theorem B2197345 : Blo 1951435 2197345 := bbase (se 2 (by rfl) ⟨824004, by rfl⟩ : syracuseStep 2197345 = 1648009) (by norm_num)
theorem B2929793 : Blo 1951435 2929793 := bstep (se 2 (by rfl) ⟨1098672, by rfl⟩ : syracuseStep 2929793 = 2197345) B2197345
theorem B1953195 : Blo 1951435 1953195 := bstep (se 1 (by rfl) ⟨1464896, by rfl⟩ : syracuseStep 1953195 = 2929793) B2929793
theorem B4944037 : Blo 1951435 4944037 := bbase (se 4 (by rfl) ⟨463503, by rfl⟩ : syracuseStep 4944037 = 927007) (by norm_num)
theorem B6592049 : Blo 1951435 6592049 := bstep (se 2 (by rfl) ⟨2472018, by rfl⟩ : syracuseStep 6592049 = 4944037) B4944037
theorem B4394699 : Blo 1951435 4394699 := bstep (se 1 (by rfl) ⟨3296024, by rfl⟩ : syracuseStep 4394699 = 6592049) B6592049
theorem B2929799 : Blo 1951435 2929799 := bstep (se 1 (by rfl) ⟨2197349, by rfl⟩ : syracuseStep 2929799 = 4394699) B4394699
theorem B1953199 : Blo 1951435 1953199 := bstep (se 1 (by rfl) ⟨1464899, by rfl⟩ : syracuseStep 1953199 = 2929799) B2929799
theorem B2929805 : Blo 1951435 2929805 := bbase (se 3 (by rfl) ⟨549338, by rfl⟩ : syracuseStep 2929805 = 1098677) (by norm_num)
theorem B1953203 : Blo 1951435 1953203 := bstep (se 1 (by rfl) ⟨1464902, by rfl⟩ : syracuseStep 1953203 = 2929805) B2929805
theorem B4394717 : Blo 1951435 4394717 := bbase (se 3 (by rfl) ⟨824009, by rfl⟩ : syracuseStep 4394717 = 1648019) (by norm_num)
theorem B2929811 : Blo 1951435 2929811 := bstep (se 1 (by rfl) ⟨2197358, by rfl⟩ : syracuseStep 2929811 = 4394717) B4394717
theorem B1953207 : Blo 1951435 1953207 := bstep (se 1 (by rfl) ⟨1464905, by rfl⟩ : syracuseStep 1953207 = 2929811) B2929811
theorem B3296045 : Blo 1951435 3296045 := bbase (se 3 (by rfl) ⟨618008, by rfl⟩ : syracuseStep 3296045 = 1236017) (by norm_num)
theorem B2197363 : Blo 1951435 2197363 := bstep (se 1 (by rfl) ⟨1648022, by rfl⟩ : syracuseStep 2197363 = 3296045) B3296045
theorem B2929817 : Blo 1951435 2929817 := bstep (se 2 (by rfl) ⟨1098681, by rfl⟩ : syracuseStep 2929817 = 2197363) B2197363
theorem B1953211 : Blo 1951435 1953211 := bstep (se 1 (by rfl) ⟨1464908, by rfl⟩ : syracuseStep 1953211 = 2929817) B2929817
theorem B2378521 : Blo 1951435 2378521 := bbase (se 2 (by rfl) ⟨891945, by rfl⟩ : syracuseStep 2378521 = 1783891) (by norm_num)
theorem B3171361 : Blo 1951435 3171361 := bstep (se 2 (by rfl) ⟨1189260, by rfl⟩ : syracuseStep 3171361 = 2378521) B2378521
theorem B4228481 : Blo 1951435 4228481 := bstep (se 2 (by rfl) ⟨1585680, by rfl⟩ : syracuseStep 4228481 = 3171361) B3171361
theorem B11275949 : Blo 1951435 11275949 := bstep (se 3 (by rfl) ⟨2114240, by rfl⟩ : syracuseStep 11275949 = 4228481) B4228481
theorem B7517299 : Blo 1951435 7517299 := bstep (se 1 (by rfl) ⟨5637974, by rfl⟩ : syracuseStep 7517299 = 11275949) B11275949
theorem B10023065 : Blo 1951435 10023065 := bstep (se 2 (by rfl) ⟨3758649, by rfl⟩ : syracuseStep 10023065 = 7517299) B7517299
theorem B6682043 : Blo 1951435 6682043 := bstep (se 1 (by rfl) ⟨5011532, by rfl⟩ : syracuseStep 6682043 = 10023065) B10023065
theorem B4454695 : Blo 1951435 4454695 := bstep (se 1 (by rfl) ⟨3341021, by rfl⟩ : syracuseStep 4454695 = 6682043) B6682043
theorem B23758373 : Blo 1951435 23758373 := bstep (se 4 (by rfl) ⟨2227347, by rfl⟩ : syracuseStep 23758373 = 4454695) B4454695
theorem B15838915 : Blo 1951435 15838915 := bstep (se 1 (by rfl) ⟨11879186, by rfl⟩ : syracuseStep 15838915 = 23758373) B23758373
theorem B21118553 : Blo 1951435 21118553 := bstep (se 2 (by rfl) ⟨7919457, by rfl⟩ : syracuseStep 21118553 = 15838915) B15838915
theorem B14079035 : Blo 1951435 14079035 := bstep (se 1 (by rfl) ⟨10559276, by rfl⟩ : syracuseStep 14079035 = 21118553) B21118553
theorem B37544093 : Blo 1951435 37544093 := bstep (se 3 (by rfl) ⟨7039517, by rfl⟩ : syracuseStep 37544093 = 14079035) B14079035
theorem B25029395 : Blo 1951435 25029395 := bstep (se 1 (by rfl) ⟨18772046, by rfl⟩ : syracuseStep 25029395 = 37544093) B37544093
theorem B16686263 : Blo 1951435 16686263 := bstep (se 1 (by rfl) ⟨12514697, by rfl⟩ : syracuseStep 16686263 = 25029395) B25029395
theorem B11124175 : Blo 1951435 11124175 := bstep (se 1 (by rfl) ⟨8343131, by rfl⟩ : syracuseStep 11124175 = 16686263) B16686263
theorem B14832233 : Blo 1951435 14832233 := bstep (se 2 (by rfl) ⟨5562087, by rfl⟩ : syracuseStep 14832233 = 11124175) B11124175
theorem B9888155 : Blo 1951435 9888155 := bstep (se 1 (by rfl) ⟨7416116, by rfl⟩ : syracuseStep 9888155 = 14832233) B14832233
theorem B6592103 : Blo 1951435 6592103 := bstep (se 1 (by rfl) ⟨4944077, by rfl⟩ : syracuseStep 6592103 = 9888155) B9888155
theorem B4394735 : Blo 1951435 4394735 := bstep (se 1 (by rfl) ⟨3296051, by rfl⟩ : syracuseStep 4394735 = 6592103) B6592103
theorem B2929823 : Blo 1951435 2929823 := bstep (se 1 (by rfl) ⟨2197367, by rfl⟩ : syracuseStep 2929823 = 4394735) B4394735
theorem B1953215 : Blo 1951435 1953215 := bstep (se 1 (by rfl) ⟨1464911, by rfl⟩ : syracuseStep 1953215 = 2929823) B2929823
theorem B2929829 : Blo 1951435 2929829 := bbase (se 4 (by rfl) ⟨274671, by rfl⟩ : syracuseStep 2929829 = 549343) (by norm_num)
theorem B1953219 : Blo 1951435 1953219 := bstep (se 1 (by rfl) ⟨1464914, by rfl⟩ : syracuseStep 1953219 = 2929829) B2929829
theorem B2472049 : Blo 1951435 2472049 := bbase (se 2 (by rfl) ⟨927018, by rfl⟩ : syracuseStep 2472049 = 1854037) (by norm_num)
theorem B3296065 : Blo 1951435 3296065 := bstep (se 2 (by rfl) ⟨1236024, by rfl⟩ : syracuseStep 3296065 = 2472049) B2472049
theorem B4394753 : Blo 1951435 4394753 := bstep (se 2 (by rfl) ⟨1648032, by rfl⟩ : syracuseStep 4394753 = 3296065) B3296065
theorem B2929835 : Blo 1951435 2929835 := bstep (se 1 (by rfl) ⟨2197376, by rfl⟩ : syracuseStep 2929835 = 4394753) B4394753
theorem B1953223 : Blo 1951435 1953223 := bstep (se 1 (by rfl) ⟨1464917, by rfl⟩ : syracuseStep 1953223 = 2929835) B2929835
theorem B2197381 : Blo 1951435 2197381 := bbase (se 4 (by rfl) ⟨206004, by rfl⟩ : syracuseStep 2197381 = 412009) (by norm_num)
theorem B2929841 : Blo 1951435 2929841 := bstep (se 2 (by rfl) ⟨1098690, by rfl⟩ : syracuseStep 2929841 = 2197381) B2197381
theorem B1953227 : Blo 1951435 1953227 := bstep (se 1 (by rfl) ⟨1464920, by rfl⟩ : syracuseStep 1953227 = 2929841) B2929841
theorem B3128701 : Blo 1951435 3128701 := bbase (se 3 (by rfl) ⟨586631, by rfl⟩ : syracuseStep 3128701 = 1173263) (by norm_num)
theorem B4171601 : Blo 1951435 4171601 := bstep (se 2 (by rfl) ⟨1564350, by rfl⟩ : syracuseStep 4171601 = 3128701) B3128701
theorem B2781067 : Blo 1951435 2781067 := bstep (se 1 (by rfl) ⟨2085800, by rfl⟩ : syracuseStep 2781067 = 4171601) B4171601
theorem B3708089 : Blo 1951435 3708089 := bstep (se 2 (by rfl) ⟨1390533, by rfl⟩ : syracuseStep 3708089 = 2781067) B2781067
theorem B2472059 : Blo 1951435 2472059 := bstep (se 1 (by rfl) ⟨1854044, by rfl⟩ : syracuseStep 2472059 = 3708089) B3708089
theorem B6592157 : Blo 1951435 6592157 := bstep (se 3 (by rfl) ⟨1236029, by rfl⟩ : syracuseStep 6592157 = 2472059) B2472059
theorem B4394771 : Blo 1951435 4394771 := bstep (se 1 (by rfl) ⟨3296078, by rfl⟩ : syracuseStep 4394771 = 6592157) B6592157
theorem B2929847 : Blo 1951435 2929847 := bstep (se 1 (by rfl) ⟨2197385, by rfl⟩ : syracuseStep 2929847 = 4394771) B4394771
theorem B1953231 : Blo 1951435 1953231 := bstep (se 1 (by rfl) ⟨1464923, by rfl⟩ : syracuseStep 1953231 = 2929847) B2929847
theorem B2929853 : Blo 1951435 2929853 := bbase (se 3 (by rfl) ⟨549347, by rfl⟩ : syracuseStep 2929853 = 1098695) (by norm_num)
theorem B1953235 : Blo 1951435 1953235 := bstep (se 1 (by rfl) ⟨1464926, by rfl⟩ : syracuseStep 1953235 = 2929853) B2929853
theorem B4394789 : Blo 1951435 4394789 := bbase (se 4 (by rfl) ⟨412011, by rfl⟩ : syracuseStep 4394789 = 824023) (by norm_num)
theorem B2929859 : Blo 1951435 2929859 := bstep (se 1 (by rfl) ⟨2197394, by rfl⟩ : syracuseStep 2929859 = 4394789) B4394789
theorem B1953239 : Blo 1951435 1953239 := bstep (se 1 (by rfl) ⟨1464929, by rfl⟩ : syracuseStep 1953239 = 2929859) B2929859
theorem B4944149 : Blo 1951435 4944149 := bbase (se 6 (by rfl) ⟨115878, by rfl⟩ : syracuseStep 4944149 = 231757) (by norm_num)
theorem B3296099 : Blo 1951435 3296099 := bstep (se 1 (by rfl) ⟨2472074, by rfl⟩ : syracuseStep 3296099 = 4944149) B4944149
theorem B2197399 : Blo 1951435 2197399 := bstep (se 1 (by rfl) ⟨1648049, by rfl⟩ : syracuseStep 2197399 = 3296099) B3296099
theorem B2929865 : Blo 1951435 2929865 := bstep (se 2 (by rfl) ⟨1098699, by rfl⟩ : syracuseStep 2929865 = 2197399) B2197399
theorem B1953243 : Blo 1951435 1953243 := bstep (se 1 (by rfl) ⟨1464932, by rfl⟩ : syracuseStep 1953243 = 2929865) B2929865
theorem B8343269 : Blo 1951435 8343269 := bbase (se 4 (by rfl) ⟨782181, by rfl⟩ : syracuseStep 8343269 = 1564363) (by norm_num)
theorem B5562179 : Blo 1951435 5562179 := bstep (se 1 (by rfl) ⟨4171634, by rfl⟩ : syracuseStep 5562179 = 8343269) B8343269
theorem B3708119 : Blo 1951435 3708119 := bstep (se 1 (by rfl) ⟨2781089, by rfl⟩ : syracuseStep 3708119 = 5562179) B5562179
theorem B9888317 : Blo 1951435 9888317 := bstep (se 3 (by rfl) ⟨1854059, by rfl⟩ : syracuseStep 9888317 = 3708119) B3708119
theorem B6592211 : Blo 1951435 6592211 := bstep (se 1 (by rfl) ⟨4944158, by rfl⟩ : syracuseStep 6592211 = 9888317) B9888317
theorem B4394807 : Blo 1951435 4394807 := bstep (se 1 (by rfl) ⟨3296105, by rfl⟩ : syracuseStep 4394807 = 6592211) B6592211
theorem B2929871 : Blo 1951435 2929871 := bstep (se 1 (by rfl) ⟨2197403, by rfl⟩ : syracuseStep 2929871 = 4394807) B4394807
theorem B1953247 : Blo 1951435 1953247 := bstep (se 1 (by rfl) ⟨1464935, by rfl⟩ : syracuseStep 1953247 = 2929871) B2929871
theorem B2929877 : Blo 1951435 2929877 := bbase (se 7 (by rfl) ⟨34334, by rfl⟩ : syracuseStep 2929877 = 68669) (by norm_num)
theorem B1953251 : Blo 1951435 1953251 := bstep (se 1 (by rfl) ⟨1464938, by rfl⟩ : syracuseStep 1953251 = 2929877) B2929877
theorem B2781101 : Blo 1951435 2781101 := bbase (se 3 (by rfl) ⟨521456, by rfl⟩ : syracuseStep 2781101 = 1042913) (by norm_num)
theorem B7416269 : Blo 1951435 7416269 := bstep (se 3 (by rfl) ⟨1390550, by rfl⟩ : syracuseStep 7416269 = 2781101) B2781101
theorem B4944179 : Blo 1951435 4944179 := bstep (se 1 (by rfl) ⟨3708134, by rfl⟩ : syracuseStep 4944179 = 7416269) B7416269
theorem B3296119 : Blo 1951435 3296119 := bstep (se 1 (by rfl) ⟨2472089, by rfl⟩ : syracuseStep 3296119 = 4944179) B4944179
theorem B4394825 : Blo 1951435 4394825 := bstep (se 2 (by rfl) ⟨1648059, by rfl⟩ : syracuseStep 4394825 = 3296119) B3296119
theorem B2929883 : Blo 1951435 2929883 := bstep (se 1 (by rfl) ⟨2197412, by rfl⟩ : syracuseStep 2929883 = 4394825) B4394825
theorem B1953255 : Blo 1951435 1953255 := bstep (se 1 (by rfl) ⟨1464941, by rfl⟩ : syracuseStep 1953255 = 2929883) B2929883
theorem B2197417 : Blo 1951435 2197417 := bbase (se 2 (by rfl) ⟨824031, by rfl⟩ : syracuseStep 2197417 = 1648063) (by norm_num)
theorem B2929889 : Blo 1951435 2929889 := bstep (se 2 (by rfl) ⟨1098708, by rfl⟩ : syracuseStep 2929889 = 2197417) B2197417
theorem B1953259 : Blo 1951435 1953259 := bstep (se 1 (by rfl) ⟨1464944, by rfl⟩ : syracuseStep 1953259 = 2929889) B2929889
theorem B31678613 : Blo 1951435 31678613 := bbase (se 6 (by rfl) ⟨742467, by rfl⟩ : syracuseStep 31678613 = 1484935) (by norm_num)
theorem B21119075 : Blo 1951435 21119075 := bstep (se 1 (by rfl) ⟨15839306, by rfl⟩ : syracuseStep 21119075 = 31678613) B31678613
theorem B14079383 : Blo 1951435 14079383 := bstep (se 1 (by rfl) ⟨10559537, by rfl⟩ : syracuseStep 14079383 = 21119075) B21119075
theorem B9386255 : Blo 1951435 9386255 := bstep (se 1 (by rfl) ⟨7039691, by rfl⟩ : syracuseStep 9386255 = 14079383) B14079383
theorem B6257503 : Blo 1951435 6257503 := bstep (se 1 (by rfl) ⟨4693127, by rfl⟩ : syracuseStep 6257503 = 9386255) B9386255
theorem B8343337 : Blo 1951435 8343337 := bstep (se 2 (by rfl) ⟨3128751, by rfl⟩ : syracuseStep 8343337 = 6257503) B6257503
theorem B11124449 : Blo 1951435 11124449 := bstep (se 2 (by rfl) ⟨4171668, by rfl⟩ : syracuseStep 11124449 = 8343337) B8343337
theorem B7416299 : Blo 1951435 7416299 := bstep (se 1 (by rfl) ⟨5562224, by rfl⟩ : syracuseStep 7416299 = 11124449) B11124449
theorem B4944199 : Blo 1951435 4944199 := bstep (se 1 (by rfl) ⟨3708149, by rfl⟩ : syracuseStep 4944199 = 7416299) B7416299
theorem B6592265 : Blo 1951435 6592265 := bstep (se 2 (by rfl) ⟨2472099, by rfl⟩ : syracuseStep 6592265 = 4944199) B4944199
theorem B4394843 : Blo 1951435 4394843 := bstep (se 1 (by rfl) ⟨3296132, by rfl⟩ : syracuseStep 4394843 = 6592265) B6592265
theorem B2929895 : Blo 1951435 2929895 := bstep (se 1 (by rfl) ⟨2197421, by rfl⟩ : syracuseStep 2929895 = 4394843) B4394843
theorem B1953263 : Blo 1951435 1953263 := bstep (se 1 (by rfl) ⟨1464947, by rfl⟩ : syracuseStep 1953263 = 2929895) B2929895
theorem B2929901 : Blo 1951435 2929901 := bbase (se 3 (by rfl) ⟨549356, by rfl⟩ : syracuseStep 2929901 = 1098713) (by norm_num)
theorem B1953267 : Blo 1951435 1953267 := bstep (se 1 (by rfl) ⟨1464950, by rfl⟩ : syracuseStep 1953267 = 2929901) B2929901
theorem B4394861 : Blo 1951435 4394861 := bbase (se 3 (by rfl) ⟨824036, by rfl⟩ : syracuseStep 4394861 = 1648073) (by norm_num)
theorem B2929907 : Blo 1951435 2929907 := bstep (se 1 (by rfl) ⟨2197430, by rfl⟩ : syracuseStep 2929907 = 4394861) B4394861
theorem B1953271 : Blo 1951435 1953271 := bstep (se 1 (by rfl) ⟨1464953, by rfl⟩ : syracuseStep 1953271 = 2929907) B2929907
theorem B3708173 : Blo 1951435 3708173 := bbase (se 3 (by rfl) ⟨695282, by rfl⟩ : syracuseStep 3708173 = 1390565) (by norm_num)
theorem B2472115 : Blo 1951435 2472115 := bstep (se 1 (by rfl) ⟨1854086, by rfl⟩ : syracuseStep 2472115 = 3708173) B3708173
theorem B3296153 : Blo 1951435 3296153 := bstep (se 2 (by rfl) ⟨1236057, by rfl⟩ : syracuseStep 3296153 = 2472115) B2472115
theorem B2197435 : Blo 1951435 2197435 := bstep (se 1 (by rfl) ⟨1648076, by rfl⟩ : syracuseStep 2197435 = 3296153) B3296153
theorem B2929913 : Blo 1951435 2929913 := bstep (se 2 (by rfl) ⟨1098717, by rfl⟩ : syracuseStep 2929913 = 2197435) B2197435
theorem B1953275 : Blo 1951435 1953275 := bstep (se 1 (by rfl) ⟨1464956, by rfl⟩ : syracuseStep 1953275 = 2929913) B2929913
theorem B18772661 : Blo 1951435 18772661 := bbase (se 5 (by rfl) ⟨879968, by rfl⟩ : syracuseStep 18772661 = 1759937) (by norm_num)
theorem B50060429 : Blo 1951435 50060429 := bstep (se 3 (by rfl) ⟨9386330, by rfl⟩ : syracuseStep 50060429 = 18772661) B18772661
theorem B33373619 : Blo 1951435 33373619 := bstep (se 1 (by rfl) ⟨25030214, by rfl⟩ : syracuseStep 33373619 = 50060429) B50060429
theorem B22249079 : Blo 1951435 22249079 := bstep (se 1 (by rfl) ⟨16686809, by rfl⟩ : syracuseStep 22249079 = 33373619) B33373619
theorem B14832719 : Blo 1951435 14832719 := bstep (se 1 (by rfl) ⟨11124539, by rfl⟩ : syracuseStep 14832719 = 22249079) B22249079
theorem B9888479 : Blo 1951435 9888479 := bstep (se 1 (by rfl) ⟨7416359, by rfl⟩ : syracuseStep 9888479 = 14832719) B14832719
theorem B6592319 : Blo 1951435 6592319 := bstep (se 1 (by rfl) ⟨4944239, by rfl⟩ : syracuseStep 6592319 = 9888479) B9888479
theorem B4394879 : Blo 1951435 4394879 := bstep (se 1 (by rfl) ⟨3296159, by rfl⟩ : syracuseStep 4394879 = 6592319) B6592319
theorem B2929919 : Blo 1951435 2929919 := bstep (se 1 (by rfl) ⟨2197439, by rfl⟩ : syracuseStep 2929919 = 4394879) B4394879
theorem B1953279 : Blo 1951435 1953279 := bstep (se 1 (by rfl) ⟨1464959, by rfl⟩ : syracuseStep 1953279 = 2929919) B2929919
theorem B2929925 : Blo 1951435 2929925 := bbase (se 4 (by rfl) ⟨274680, by rfl⟩ : syracuseStep 2929925 = 549361) (by norm_num)
theorem B1953283 : Blo 1951435 1953283 := bstep (se 1 (by rfl) ⟨1464962, by rfl⟩ : syracuseStep 1953283 = 2929925) B2929925
theorem B3296173 : Blo 1951435 3296173 := bbase (se 3 (by rfl) ⟨618032, by rfl⟩ : syracuseStep 3296173 = 1236065) (by norm_num)
theorem B4394897 : Blo 1951435 4394897 := bstep (se 2 (by rfl) ⟨1648086, by rfl⟩ : syracuseStep 4394897 = 3296173) B3296173
theorem B2929931 : Blo 1951435 2929931 := bstep (se 1 (by rfl) ⟨2197448, by rfl⟩ : syracuseStep 2929931 = 4394897) B4394897
theorem B1953287 : Blo 1951435 1953287 := bstep (se 1 (by rfl) ⟨1464965, by rfl⟩ : syracuseStep 1953287 = 2929931) B2929931
theorem B2197453 : Blo 1951435 2197453 := bbase (se 3 (by rfl) ⟨412022, by rfl⟩ : syracuseStep 2197453 = 824045) (by norm_num)
theorem B2929937 : Blo 1951435 2929937 := bstep (se 2 (by rfl) ⟨1098726, by rfl⟩ : syracuseStep 2929937 = 2197453) B2197453
theorem B1953291 : Blo 1951435 1953291 := bstep (se 1 (by rfl) ⟨1464968, by rfl⟩ : syracuseStep 1953291 = 2929937) B2929937
theorem B6592373 : Blo 1951435 6592373 := bbase (se 5 (by rfl) ⟨309017, by rfl⟩ : syracuseStep 6592373 = 618035) (by norm_num)
theorem B4394915 : Blo 1951435 4394915 := bstep (se 1 (by rfl) ⟨3296186, by rfl⟩ : syracuseStep 4394915 = 6592373) B6592373
theorem B2929943 : Blo 1951435 2929943 := bstep (se 1 (by rfl) ⟨2197457, by rfl⟩ : syracuseStep 2929943 = 4394915) B4394915
theorem B1953295 : Blo 1951435 1953295 := bstep (se 1 (by rfl) ⟨1464971, by rfl⟩ : syracuseStep 1953295 = 2929943) B2929943
theorem B2929949 : Blo 1951435 2929949 := bbase (se 3 (by rfl) ⟨549365, by rfl⟩ : syracuseStep 2929949 = 1098731) (by norm_num)
theorem B1953299 : Blo 1951435 1953299 := bstep (se 1 (by rfl) ⟨1464974, by rfl⟩ : syracuseStep 1953299 = 2929949) B2929949
theorem B4394933 : Blo 1951435 4394933 := bbase (se 5 (by rfl) ⟨206012, by rfl⟩ : syracuseStep 4394933 = 412025) (by norm_num)
theorem B2929955 : Blo 1951435 2929955 := bstep (se 1 (by rfl) ⟨2197466, by rfl⟩ : syracuseStep 2929955 = 4394933) B4394933
theorem B1953303 : Blo 1951435 1953303 := bstep (se 1 (by rfl) ⟨1464977, by rfl⟩ : syracuseStep 1953303 = 2929955) B2929955
theorem B2346617 : Blo 1951435 2346617 := bbase (se 2 (by rfl) ⟨879981, by rfl⟩ : syracuseStep 2346617 = 1759963) (by norm_num)
theorem B6257645 : Blo 1951435 6257645 := bstep (se 3 (by rfl) ⟨1173308, by rfl⟩ : syracuseStep 6257645 = 2346617) B2346617
theorem B4171763 : Blo 1951435 4171763 := bstep (se 1 (by rfl) ⟨3128822, by rfl⟩ : syracuseStep 4171763 = 6257645) B6257645
theorem B11124701 : Blo 1951435 11124701 := bstep (se 3 (by rfl) ⟨2085881, by rfl⟩ : syracuseStep 11124701 = 4171763) B4171763
theorem B7416467 : Blo 1951435 7416467 := bstep (se 1 (by rfl) ⟨5562350, by rfl⟩ : syracuseStep 7416467 = 11124701) B11124701
theorem B4944311 : Blo 1951435 4944311 := bstep (se 1 (by rfl) ⟨3708233, by rfl⟩ : syracuseStep 4944311 = 7416467) B7416467
theorem B3296207 : Blo 1951435 3296207 := bstep (se 1 (by rfl) ⟨2472155, by rfl⟩ : syracuseStep 3296207 = 4944311) B4944311
theorem B2197471 : Blo 1951435 2197471 := bstep (se 1 (by rfl) ⟨1648103, by rfl⟩ : syracuseStep 2197471 = 3296207) B3296207
theorem B2929961 : Blo 1951435 2929961 := bstep (se 2 (by rfl) ⟨1098735, by rfl⟩ : syracuseStep 2929961 = 2197471) B2197471
theorem B1953307 : Blo 1951435 1953307 := bstep (se 1 (by rfl) ⟨1464980, by rfl⟩ : syracuseStep 1953307 = 2929961) B2929961
theorem B2114345 : Blo 1951435 2114345 := bbase (se 2 (by rfl) ⟨792879, by rfl⟩ : syracuseStep 2114345 = 1585759) (by norm_num)
theorem B5638253 : Blo 1951435 5638253 := bstep (se 3 (by rfl) ⟨1057172, by rfl⟩ : syracuseStep 5638253 = 2114345) B2114345
theorem B15035341 : Blo 1951435 15035341 := bstep (se 3 (by rfl) ⟨2819126, by rfl⟩ : syracuseStep 15035341 = 5638253) B5638253
theorem B20047121 : Blo 1951435 20047121 := bstep (se 2 (by rfl) ⟨7517670, by rfl⟩ : syracuseStep 20047121 = 15035341) B15035341
theorem B13364747 : Blo 1951435 13364747 := bstep (se 1 (by rfl) ⟨10023560, by rfl⟩ : syracuseStep 13364747 = 20047121) B20047121
theorem B8909831 : Blo 1951435 8909831 := bstep (se 1 (by rfl) ⟨6682373, by rfl⟩ : syracuseStep 8909831 = 13364747) B13364747
theorem B5939887 : Blo 1951435 5939887 := bstep (se 1 (by rfl) ⟨4454915, by rfl⟩ : syracuseStep 5939887 = 8909831) B8909831
theorem B7919849 : Blo 1951435 7919849 := bstep (se 2 (by rfl) ⟨2969943, by rfl⟩ : syracuseStep 7919849 = 5939887) B5939887
theorem B5279899 : Blo 1951435 5279899 := bstep (se 1 (by rfl) ⟨3959924, by rfl⟩ : syracuseStep 5279899 = 7919849) B7919849
theorem B7039865 : Blo 1951435 7039865 := bstep (se 2 (by rfl) ⟨2639949, by rfl⟩ : syracuseStep 7039865 = 5279899) B5279899
theorem B4693243 : Blo 1951435 4693243 := bstep (se 1 (by rfl) ⟨3519932, by rfl⟩ : syracuseStep 4693243 = 7039865) B7039865
theorem B6257657 : Blo 1951435 6257657 := bstep (se 2 (by rfl) ⟨2346621, by rfl⟩ : syracuseStep 6257657 = 4693243) B4693243
theorem B4171771 : Blo 1951435 4171771 := bstep (se 1 (by rfl) ⟨3128828, by rfl⟩ : syracuseStep 4171771 = 6257657) B6257657
theorem B5562361 : Blo 1951435 5562361 := bstep (se 2 (by rfl) ⟨2085885, by rfl⟩ : syracuseStep 5562361 = 4171771) B4171771
theorem B7416481 : Blo 1951435 7416481 := bstep (se 2 (by rfl) ⟨2781180, by rfl⟩ : syracuseStep 7416481 = 5562361) B5562361
theorem B9888641 : Blo 1951435 9888641 := bstep (se 2 (by rfl) ⟨3708240, by rfl⟩ : syracuseStep 9888641 = 7416481) B7416481
theorem B6592427 : Blo 1951435 6592427 := bstep (se 1 (by rfl) ⟨4944320, by rfl⟩ : syracuseStep 6592427 = 9888641) B9888641
theorem B4394951 : Blo 1951435 4394951 := bstep (se 1 (by rfl) ⟨3296213, by rfl⟩ : syracuseStep 4394951 = 6592427) B6592427
theorem B2929967 : Blo 1951435 2929967 := bstep (se 1 (by rfl) ⟨2197475, by rfl⟩ : syracuseStep 2929967 = 4394951) B4394951
theorem B1953311 : Blo 1951435 1953311 := bstep (se 1 (by rfl) ⟨1464983, by rfl⟩ : syracuseStep 1953311 = 2929967) B2929967
theorem B2929973 : Blo 1951435 2929973 := bbase (se 5 (by rfl) ⟨137342, by rfl⟩ : syracuseStep 2929973 = 274685) (by norm_num)
theorem B1953315 : Blo 1951435 1953315 := bstep (se 1 (by rfl) ⟨1464986, by rfl⟩ : syracuseStep 1953315 = 2929973) B2929973
theorem B4944341 : Blo 1951435 4944341 := bbase (se 7 (by rfl) ⟨57941, by rfl⟩ : syracuseStep 4944341 = 115883) (by norm_num)
theorem B3296227 : Blo 1951435 3296227 := bstep (se 1 (by rfl) ⟨2472170, by rfl⟩ : syracuseStep 3296227 = 4944341) B4944341
theorem B4394969 : Blo 1951435 4394969 := bstep (se 2 (by rfl) ⟨1648113, by rfl⟩ : syracuseStep 4394969 = 3296227) B3296227
theorem B2929979 : Blo 1951435 2929979 := bstep (se 1 (by rfl) ⟨2197484, by rfl⟩ : syracuseStep 2929979 = 4394969) B4394969
theorem B1953319 : Blo 1951435 1953319 := bstep (se 1 (by rfl) ⟨1464989, by rfl⟩ : syracuseStep 1953319 = 2929979) B2929979
theorem B2197489 : Blo 1951435 2197489 := bbase (se 2 (by rfl) ⟨824058, by rfl⟩ : syracuseStep 2197489 = 1648117) (by norm_num)
theorem B2929985 : Blo 1951435 2929985 := bstep (se 2 (by rfl) ⟨1098744, by rfl⟩ : syracuseStep 2929985 = 2197489) B2197489
theorem B1953323 : Blo 1951435 1953323 := bstep (se 1 (by rfl) ⟨1464992, by rfl⟩ : syracuseStep 1953323 = 2929985) B2929985
theorem B3959957 : Blo 1951435 3959957 := bbase (se 6 (by rfl) ⟨92811, by rfl⟩ : syracuseStep 3959957 = 185623) (by norm_num)
theorem B2639971 : Blo 1951435 2639971 := bstep (se 1 (by rfl) ⟨1979978, by rfl⟩ : syracuseStep 2639971 = 3959957) B3959957
theorem B14079845 : Blo 1951435 14079845 := bstep (se 4 (by rfl) ⟨1319985, by rfl⟩ : syracuseStep 14079845 = 2639971) B2639971
theorem B9386563 : Blo 1951435 9386563 := bstep (se 1 (by rfl) ⟨7039922, by rfl⟩ : syracuseStep 9386563 = 14079845) B14079845
theorem B12515417 : Blo 1951435 12515417 := bstep (se 2 (by rfl) ⟨4693281, by rfl⟩ : syracuseStep 12515417 = 9386563) B9386563
theorem B8343611 : Blo 1951435 8343611 := bstep (se 1 (by rfl) ⟨6257708, by rfl⟩ : syracuseStep 8343611 = 12515417) B12515417
theorem B5562407 : Blo 1951435 5562407 := bstep (se 1 (by rfl) ⟨4171805, by rfl⟩ : syracuseStep 5562407 = 8343611) B8343611
theorem B3708271 : Blo 1951435 3708271 := bstep (se 1 (by rfl) ⟨2781203, by rfl⟩ : syracuseStep 3708271 = 5562407) B5562407
theorem B4944361 : Blo 1951435 4944361 := bstep (se 2 (by rfl) ⟨1854135, by rfl⟩ : syracuseStep 4944361 = 3708271) B3708271
theorem B6592481 : Blo 1951435 6592481 := bstep (se 2 (by rfl) ⟨2472180, by rfl⟩ : syracuseStep 6592481 = 4944361) B4944361
theorem B4394987 : Blo 1951435 4394987 := bstep (se 1 (by rfl) ⟨3296240, by rfl⟩ : syracuseStep 4394987 = 6592481) B6592481
theorem B2929991 : Blo 1951435 2929991 := bstep (se 1 (by rfl) ⟨2197493, by rfl⟩ : syracuseStep 2929991 = 4394987) B4394987
theorem B1953327 : Blo 1951435 1953327 := bstep (se 1 (by rfl) ⟨1464995, by rfl⟩ : syracuseStep 1953327 = 2929991) B2929991
theorem B2929997 : Blo 1951435 2929997 := bbase (se 3 (by rfl) ⟨549374, by rfl⟩ : syracuseStep 2929997 = 1098749) (by norm_num)
theorem B1953331 : Blo 1951435 1953331 := bstep (se 1 (by rfl) ⟨1464998, by rfl⟩ : syracuseStep 1953331 = 2929997) B2929997
theorem B4395005 : Blo 1951435 4395005 := bbase (se 3 (by rfl) ⟨824063, by rfl⟩ : syracuseStep 4395005 = 1648127) (by norm_num)
theorem B2930003 : Blo 1951435 2930003 := bstep (se 1 (by rfl) ⟨2197502, by rfl⟩ : syracuseStep 2930003 = 4395005) B4395005
theorem B1953335 : Blo 1951435 1953335 := bstep (se 1 (by rfl) ⟨1465001, by rfl⟩ : syracuseStep 1953335 = 2930003) B2930003
theorem B3296261 : Blo 1951435 3296261 := bbase (se 4 (by rfl) ⟨309024, by rfl⟩ : syracuseStep 3296261 = 618049) (by norm_num)
theorem B2197507 : Blo 1951435 2197507 := bstep (se 1 (by rfl) ⟨1648130, by rfl⟩ : syracuseStep 2197507 = 3296261) B3296261
theorem B2930009 : Blo 1951435 2930009 := bstep (se 2 (by rfl) ⟨1098753, by rfl⟩ : syracuseStep 2930009 = 2197507) B2197507
theorem B1953339 : Blo 1951435 1953339 := bstep (se 1 (by rfl) ⟨1465004, by rfl⟩ : syracuseStep 1953339 = 2930009) B2930009
theorem B14833205 : Blo 1951435 14833205 := bbase (se 5 (by rfl) ⟨695306, by rfl⟩ : syracuseStep 14833205 = 1390613) (by norm_num)
theorem B9888803 : Blo 1951435 9888803 := bstep (se 1 (by rfl) ⟨7416602, by rfl⟩ : syracuseStep 9888803 = 14833205) B14833205
theorem B6592535 : Blo 1951435 6592535 := bstep (se 1 (by rfl) ⟨4944401, by rfl⟩ : syracuseStep 6592535 = 9888803) B9888803
theorem B4395023 : Blo 1951435 4395023 := bstep (se 1 (by rfl) ⟨3296267, by rfl⟩ : syracuseStep 4395023 = 6592535) B6592535
theorem B2930015 : Blo 1951435 2930015 := bstep (se 1 (by rfl) ⟨2197511, by rfl⟩ : syracuseStep 2930015 = 4395023) B4395023
theorem B1953343 : Blo 1951435 1953343 := bstep (se 1 (by rfl) ⟨1465007, by rfl⟩ : syracuseStep 1953343 = 2930015) B2930015
theorem B2930021 : Blo 1951435 2930021 := bbase (se 4 (by rfl) ⟨274689, by rfl⟩ : syracuseStep 2930021 = 549379) (by norm_num)
theorem B1953347 : Blo 1951435 1953347 := bstep (se 1 (by rfl) ⟨1465010, by rfl⟩ : syracuseStep 1953347 = 2930021) B2930021
theorem B3708317 : Blo 1951435 3708317 := bbase (se 3 (by rfl) ⟨695309, by rfl⟩ : syracuseStep 3708317 = 1390619) (by norm_num)
theorem B2472211 : Blo 1951435 2472211 := bstep (se 1 (by rfl) ⟨1854158, by rfl⟩ : syracuseStep 2472211 = 3708317) B3708317
theorem B3296281 : Blo 1951435 3296281 := bstep (se 2 (by rfl) ⟨1236105, by rfl⟩ : syracuseStep 3296281 = 2472211) B2472211
theorem B4395041 : Blo 1951435 4395041 := bstep (se 2 (by rfl) ⟨1648140, by rfl⟩ : syracuseStep 4395041 = 3296281) B3296281
theorem B2930027 : Blo 1951435 2930027 := bstep (se 1 (by rfl) ⟨2197520, by rfl⟩ : syracuseStep 2930027 = 4395041) B4395041
theorem B1953351 : Blo 1951435 1953351 := bstep (se 1 (by rfl) ⟨1465013, by rfl⟩ : syracuseStep 1953351 = 2930027) B2930027
theorem B2197525 : Blo 1951435 2197525 := bbase (se 6 (by rfl) ⟨51504, by rfl⟩ : syracuseStep 2197525 = 103009) (by norm_num)
theorem B2930033 : Blo 1951435 2930033 := bstep (se 2 (by rfl) ⟨1098762, by rfl⟩ : syracuseStep 2930033 = 2197525) B2197525
theorem B1953355 : Blo 1951435 1953355 := bstep (se 1 (by rfl) ⟨1465016, by rfl⟩ : syracuseStep 1953355 = 2930033) B2930033
theorem B2472221 : Blo 1951435 2472221 := bbase (se 3 (by rfl) ⟨463541, by rfl⟩ : syracuseStep 2472221 = 927083) (by norm_num)
theorem B6592589 : Blo 1951435 6592589 := bstep (se 3 (by rfl) ⟨1236110, by rfl⟩ : syracuseStep 6592589 = 2472221) B2472221
theorem B4395059 : Blo 1951435 4395059 := bstep (se 1 (by rfl) ⟨3296294, by rfl⟩ : syracuseStep 4395059 = 6592589) B6592589
theorem B2930039 : Blo 1951435 2930039 := bstep (se 1 (by rfl) ⟨2197529, by rfl⟩ : syracuseStep 2930039 = 4395059) B4395059
theorem B1953359 : Blo 1951435 1953359 := bstep (se 1 (by rfl) ⟨1465019, by rfl⟩ : syracuseStep 1953359 = 2930039) B2930039
theorem B2930045 : Blo 1951435 2930045 := bbase (se 3 (by rfl) ⟨549383, by rfl⟩ : syracuseStep 2930045 = 1098767) (by norm_num)
theorem B1953363 : Blo 1951435 1953363 := bstep (se 1 (by rfl) ⟨1465022, by rfl⟩ : syracuseStep 1953363 = 2930045) B2930045
theorem B4395077 : Blo 1951435 4395077 := bbase (se 4 (by rfl) ⟨412038, by rfl⟩ : syracuseStep 4395077 = 824077) (by norm_num)
theorem B2930051 : Blo 1951435 2930051 := bstep (se 1 (by rfl) ⟨2197538, by rfl⟩ : syracuseStep 2930051 = 4395077) B4395077
theorem B1953367 : Blo 1951435 1953367 := bstep (se 1 (by rfl) ⟨1465025, by rfl⟩ : syracuseStep 1953367 = 2930051) B2930051
theorem B5562533 : Blo 1951435 5562533 := bbase (se 4 (by rfl) ⟨521487, by rfl⟩ : syracuseStep 5562533 = 1042975) (by norm_num)
theorem B3708355 : Blo 1951435 3708355 := bstep (se 1 (by rfl) ⟨2781266, by rfl⟩ : syracuseStep 3708355 = 5562533) B5562533
theorem B4944473 : Blo 1951435 4944473 := bstep (se 2 (by rfl) ⟨1854177, by rfl⟩ : syracuseStep 4944473 = 3708355) B3708355
theorem B3296315 : Blo 1951435 3296315 := bstep (se 1 (by rfl) ⟨2472236, by rfl⟩ : syracuseStep 3296315 = 4944473) B4944473
theorem B2197543 : Blo 1951435 2197543 := bstep (se 1 (by rfl) ⟨1648157, by rfl⟩ : syracuseStep 2197543 = 3296315) B3296315
theorem B2930057 : Blo 1951435 2930057 := bstep (se 2 (by rfl) ⟨1098771, by rfl⟩ : syracuseStep 2930057 = 2197543) B2197543
theorem B1953371 : Blo 1951435 1953371 := bstep (se 1 (by rfl) ⟨1465028, by rfl⟩ : syracuseStep 1953371 = 2930057) B2930057
theorem B9888965 : Blo 1951435 9888965 := bbase (se 4 (by rfl) ⟨927090, by rfl⟩ : syracuseStep 9888965 = 1854181) (by norm_num)
theorem B6592643 : Blo 1951435 6592643 := bstep (se 1 (by rfl) ⟨4944482, by rfl⟩ : syracuseStep 6592643 = 9888965) B9888965
theorem B4395095 : Blo 1951435 4395095 := bstep (se 1 (by rfl) ⟨3296321, by rfl⟩ : syracuseStep 4395095 = 6592643) B6592643
theorem B2930063 : Blo 1951435 2930063 := bstep (se 1 (by rfl) ⟨2197547, by rfl⟩ : syracuseStep 2930063 = 4395095) B4395095
theorem B1953375 : Blo 1951435 1953375 := bstep (se 1 (by rfl) ⟨1465031, by rfl⟩ : syracuseStep 1953375 = 2930063) B2930063
theorem B2930069 : Blo 1951435 2930069 := bbase (se 6 (by rfl) ⟨68673, by rfl⟩ : syracuseStep 2930069 = 137347) (by norm_num)
theorem B1953379 : Blo 1951435 1953379 := bstep (se 1 (by rfl) ⟨1465034, by rfl⟩ : syracuseStep 1953379 = 2930069) B2930069
theorem B4171925 : Blo 1951435 4171925 := bbase (se 6 (by rfl) ⟨97779, by rfl⟩ : syracuseStep 4171925 = 195559) (by norm_num)
theorem B11125133 : Blo 1951435 11125133 := bstep (se 3 (by rfl) ⟨2085962, by rfl⟩ : syracuseStep 11125133 = 4171925) B4171925
theorem B7416755 : Blo 1951435 7416755 := bstep (se 1 (by rfl) ⟨5562566, by rfl⟩ : syracuseStep 7416755 = 11125133) B11125133
theorem B4944503 : Blo 1951435 4944503 := bstep (se 1 (by rfl) ⟨3708377, by rfl⟩ : syracuseStep 4944503 = 7416755) B7416755
theorem B3296335 : Blo 1951435 3296335 := bstep (se 1 (by rfl) ⟨2472251, by rfl⟩ : syracuseStep 3296335 = 4944503) B4944503
theorem B4395113 : Blo 1951435 4395113 := bstep (se 2 (by rfl) ⟨1648167, by rfl⟩ : syracuseStep 4395113 = 3296335) B3296335
theorem B2930075 : Blo 1951435 2930075 := bstep (se 1 (by rfl) ⟨2197556, by rfl⟩ : syracuseStep 2930075 = 4395113) B4395113
theorem B1953383 : Blo 1951435 1953383 := bstep (se 1 (by rfl) ⟨1465037, by rfl⟩ : syracuseStep 1953383 = 2930075) B2930075
theorem B2197561 : Blo 1951435 2197561 := bbase (se 2 (by rfl) ⟨824085, by rfl⟩ : syracuseStep 2197561 = 1648171) (by norm_num)
theorem B2930081 : Blo 1951435 2930081 := bstep (se 2 (by rfl) ⟨1098780, by rfl⟩ : syracuseStep 2930081 = 2197561) B2197561
theorem B1953387 : Blo 1951435 1953387 := bstep (se 1 (by rfl) ⟨1465040, by rfl⟩ : syracuseStep 1953387 = 2930081) B2930081
theorem B3128957 : Blo 1951435 3128957 := bbase (se 3 (by rfl) ⟨586679, by rfl⟩ : syracuseStep 3128957 = 1173359) (by norm_num)
theorem B2085971 : Blo 1951435 2085971 := bstep (se 1 (by rfl) ⟨1564478, by rfl⟩ : syracuseStep 2085971 = 3128957) B3128957
theorem B5562589 : Blo 1951435 5562589 := bstep (se 3 (by rfl) ⟨1042985, by rfl⟩ : syracuseStep 5562589 = 2085971) B2085971
theorem B7416785 : Blo 1951435 7416785 := bstep (se 2 (by rfl) ⟨2781294, by rfl⟩ : syracuseStep 7416785 = 5562589) B5562589
theorem B4944523 : Blo 1951435 4944523 := bstep (se 1 (by rfl) ⟨3708392, by rfl⟩ : syracuseStep 4944523 = 7416785) B7416785
theorem B6592697 : Blo 1951435 6592697 := bstep (se 2 (by rfl) ⟨2472261, by rfl⟩ : syracuseStep 6592697 = 4944523) B4944523
theorem B4395131 : Blo 1951435 4395131 := bstep (se 1 (by rfl) ⟨3296348, by rfl⟩ : syracuseStep 4395131 = 6592697) B6592697
theorem B2930087 : Blo 1951435 2930087 := bstep (se 1 (by rfl) ⟨2197565, by rfl⟩ : syracuseStep 2930087 = 4395131) B4395131
theorem B1953391 : Blo 1951435 1953391 := bstep (se 1 (by rfl) ⟨1465043, by rfl⟩ : syracuseStep 1953391 = 2930087) B2930087
theorem B2930093 : Blo 1951435 2930093 := bbase (se 3 (by rfl) ⟨549392, by rfl⟩ : syracuseStep 2930093 = 1098785) (by norm_num)
theorem B1953395 : Blo 1951435 1953395 := bstep (se 1 (by rfl) ⟨1465046, by rfl⟩ : syracuseStep 1953395 = 2930093) B2930093
theorem B4395149 : Blo 1951435 4395149 := bbase (se 3 (by rfl) ⟨824090, by rfl⟩ : syracuseStep 4395149 = 1648181) (by norm_num)
theorem B2930099 : Blo 1951435 2930099 := bstep (se 1 (by rfl) ⟨2197574, by rfl⟩ : syracuseStep 2930099 = 4395149) B4395149
theorem B1953399 : Blo 1951435 1953399 := bstep (se 1 (by rfl) ⟨1465049, by rfl⟩ : syracuseStep 1953399 = 2930099) B2930099
theorem B2472277 : Blo 1951435 2472277 := bbase (se 10 (by rfl) ⟨3621, by rfl⟩ : syracuseStep 2472277 = 7243) (by norm_num)
theorem B3296369 : Blo 1951435 3296369 := bstep (se 2 (by rfl) ⟨1236138, by rfl⟩ : syracuseStep 3296369 = 2472277) B2472277
theorem B2197579 : Blo 1951435 2197579 := bstep (se 1 (by rfl) ⟨1648184, by rfl⟩ : syracuseStep 2197579 = 3296369) B3296369
theorem B2930105 : Blo 1951435 2930105 := bstep (se 2 (by rfl) ⟨1098789, by rfl⟩ : syracuseStep 2930105 = 2197579) B2197579
theorem B1953403 : Blo 1951435 1953403 := bstep (se 1 (by rfl) ⟨1465052, by rfl⟩ : syracuseStep 1953403 = 2930105) B2930105
theorem B7518037 : Blo 1951435 7518037 := bbase (se 9 (by rfl) ⟨22025, by rfl⟩ : syracuseStep 7518037 = 44051) (by norm_num)
theorem B10024049 : Blo 1951435 10024049 := bstep (se 2 (by rfl) ⟨3759018, by rfl⟩ : syracuseStep 10024049 = 7518037) B7518037
theorem B6682699 : Blo 1951435 6682699 := bstep (se 1 (by rfl) ⟨5012024, by rfl⟩ : syracuseStep 6682699 = 10024049) B10024049
theorem B35641061 : Blo 1951435 35641061 := bstep (se 4 (by rfl) ⟨3341349, by rfl⟩ : syracuseStep 35641061 = 6682699) B6682699
theorem B23760707 : Blo 1951435 23760707 := bstep (se 1 (by rfl) ⟨17820530, by rfl⟩ : syracuseStep 23760707 = 35641061) B35641061
theorem B63361885 : Blo 1951435 63361885 := bstep (se 3 (by rfl) ⟨11880353, by rfl⟩ : syracuseStep 63361885 = 23760707) B23760707
theorem B84482513 : Blo 1951435 84482513 := bstep (se 2 (by rfl) ⟨31680942, by rfl⟩ : syracuseStep 84482513 = 63361885) B63361885
theorem B56321675 : Blo 1951435 56321675 := bstep (se 1 (by rfl) ⟨42241256, by rfl⟩ : syracuseStep 56321675 = 84482513) B84482513
theorem B37547783 : Blo 1951435 37547783 := bstep (se 1 (by rfl) ⟨28160837, by rfl⟩ : syracuseStep 37547783 = 56321675) B56321675
theorem B25031855 : Blo 1951435 25031855 := bstep (se 1 (by rfl) ⟨18773891, by rfl⟩ : syracuseStep 25031855 = 37547783) B37547783
theorem B16687903 : Blo 1951435 16687903 := bstep (se 1 (by rfl) ⟨12515927, by rfl⟩ : syracuseStep 16687903 = 25031855) B25031855
theorem B22250537 : Blo 1951435 22250537 := bstep (se 2 (by rfl) ⟨8343951, by rfl⟩ : syracuseStep 22250537 = 16687903) B16687903
theorem B14833691 : Blo 1951435 14833691 := bstep (se 1 (by rfl) ⟨11125268, by rfl⟩ : syracuseStep 14833691 = 22250537) B22250537
theorem B9889127 : Blo 1951435 9889127 := bstep (se 1 (by rfl) ⟨7416845, by rfl⟩ : syracuseStep 9889127 = 14833691) B14833691
theorem B6592751 : Blo 1951435 6592751 := bstep (se 1 (by rfl) ⟨4944563, by rfl⟩ : syracuseStep 6592751 = 9889127) B9889127
theorem B4395167 : Blo 1951435 4395167 := bstep (se 1 (by rfl) ⟨3296375, by rfl⟩ : syracuseStep 4395167 = 6592751) B6592751
theorem B2930111 : Blo 1951435 2930111 := bstep (se 1 (by rfl) ⟨2197583, by rfl⟩ : syracuseStep 2930111 = 4395167) B4395167
theorem B1953407 : Blo 1951435 1953407 := bstep (se 1 (by rfl) ⟨1465055, by rfl⟩ : syracuseStep 1953407 = 2930111) B2930111
theorem B2930117 : Blo 1951435 2930117 := bbase (se 4 (by rfl) ⟨274698, by rfl⟩ : syracuseStep 2930117 = 549397) (by norm_num)
theorem B1953411 : Blo 1951435 1953411 := bstep (se 1 (by rfl) ⟨1465058, by rfl⟩ : syracuseStep 1953411 = 2930117) B2930117
theorem B3296389 : Blo 1951435 3296389 := bbase (se 4 (by rfl) ⟨309036, by rfl⟩ : syracuseStep 3296389 = 618073) (by norm_num)
theorem B4395185 : Blo 1951435 4395185 := bstep (se 2 (by rfl) ⟨1648194, by rfl⟩ : syracuseStep 4395185 = 3296389) B3296389
theorem B2930123 : Blo 1951435 2930123 := bstep (se 1 (by rfl) ⟨2197592, by rfl⟩ : syracuseStep 2930123 = 4395185) B4395185
theorem B1953415 : Blo 1951435 1953415 := bstep (se 1 (by rfl) ⟨1465061, by rfl⟩ : syracuseStep 1953415 = 2930123) B2930123
theorem B2197597 : Blo 1951435 2197597 := bbase (se 3 (by rfl) ⟨412049, by rfl⟩ : syracuseStep 2197597 = 824099) (by norm_num)
theorem B2930129 : Blo 1951435 2930129 := bstep (se 2 (by rfl) ⟨1098798, by rfl⟩ : syracuseStep 2930129 = 2197597) B2197597
theorem B1953419 : Blo 1951435 1953419 := bstep (se 1 (by rfl) ⟨1465064, by rfl⟩ : syracuseStep 1953419 = 2930129) B2930129
theorem B6592805 : Blo 1951435 6592805 := bbase (se 4 (by rfl) ⟨618075, by rfl⟩ : syracuseStep 6592805 = 1236151) (by norm_num)
theorem B4395203 : Blo 1951435 4395203 := bstep (se 1 (by rfl) ⟨3296402, by rfl⟩ : syracuseStep 4395203 = 6592805) B6592805
theorem B2930135 : Blo 1951435 2930135 := bstep (se 1 (by rfl) ⟨2197601, by rfl⟩ : syracuseStep 2930135 = 4395203) B4395203
theorem B1953423 : Blo 1951435 1953423 := bstep (se 1 (by rfl) ⟨1465067, by rfl⟩ : syracuseStep 1953423 = 2930135) B2930135
theorem B2930141 : Blo 1951435 2930141 := bbase (se 3 (by rfl) ⟨549401, by rfl⟩ : syracuseStep 2930141 = 1098803) (by norm_num)
theorem B1953427 : Blo 1951435 1953427 := bstep (se 1 (by rfl) ⟨1465070, by rfl⟩ : syracuseStep 1953427 = 2930141) B2930141
theorem B4395221 : Blo 1951435 4395221 := bbase (se 7 (by rfl) ⟨51506, by rfl⟩ : syracuseStep 4395221 = 103013) (by norm_num)
theorem B2930147 : Blo 1951435 2930147 := bstep (se 1 (by rfl) ⟨2197610, by rfl⟩ : syracuseStep 2930147 = 4395221) B4395221
theorem B1953431 : Blo 1951435 1953431 := bstep (se 1 (by rfl) ⟨1465073, by rfl⟩ : syracuseStep 1953431 = 2930147) B2930147
theorem B10560469 : Blo 1951435 10560469 := bbase (se 7 (by rfl) ⟨123755, by rfl⟩ : syracuseStep 10560469 = 247511) (by norm_num)
theorem B14080625 : Blo 1951435 14080625 := bstep (se 2 (by rfl) ⟨5280234, by rfl⟩ : syracuseStep 14080625 = 10560469) B10560469
theorem B9387083 : Blo 1951435 9387083 := bstep (se 1 (by rfl) ⟨7040312, by rfl⟩ : syracuseStep 9387083 = 14080625) B14080625
theorem B6258055 : Blo 1951435 6258055 := bstep (se 1 (by rfl) ⟨4693541, by rfl⟩ : syracuseStep 6258055 = 9387083) B9387083
theorem B8344073 : Blo 1951435 8344073 := bstep (se 2 (by rfl) ⟨3129027, by rfl⟩ : syracuseStep 8344073 = 6258055) B6258055
theorem B5562715 : Blo 1951435 5562715 := bstep (se 1 (by rfl) ⟨4172036, by rfl⟩ : syracuseStep 5562715 = 8344073) B8344073
theorem B7416953 : Blo 1951435 7416953 := bstep (se 2 (by rfl) ⟨2781357, by rfl⟩ : syracuseStep 7416953 = 5562715) B5562715
theorem B4944635 : Blo 1951435 4944635 := bstep (se 1 (by rfl) ⟨3708476, by rfl⟩ : syracuseStep 4944635 = 7416953) B7416953
theorem B3296423 : Blo 1951435 3296423 := bstep (se 1 (by rfl) ⟨2472317, by rfl⟩ : syracuseStep 3296423 = 4944635) B4944635
theorem B2197615 : Blo 1951435 2197615 := bstep (se 1 (by rfl) ⟨1648211, by rfl⟩ : syracuseStep 2197615 = 3296423) B3296423
theorem B2930153 : Blo 1951435 2930153 := bstep (se 2 (by rfl) ⟨1098807, by rfl⟩ : syracuseStep 2930153 = 2197615) B2197615
theorem B1953435 : Blo 1951435 1953435 := bstep (se 1 (by rfl) ⟨1465076, by rfl⟩ : syracuseStep 1953435 = 2930153) B2930153
theorem C0 (j : ℕ) (h1 : 487858 ≤ j) (h2 : j ≤ 488358) : Blo 1951435 (4 * j + 3) := by
  interval_cases j
  · exact B1951435
  · exact B1951439
  · exact B1951443
  · exact B1951447
  · exact B1951451
  · exact B1951455
  · exact B1951459
  · exact B1951463
  · exact B1951467
  · exact B1951471
  · exact B1951475
  · exact B1951479
  · exact B1951483
  · exact B1951487
  · exact B1951491
  · exact B1951495
  · exact B1951499
  · exact B1951503
  · exact B1951507
  · exact B1951511
  · exact B1951515
  · exact B1951519
  · exact B1951523
  · exact B1951527
  · exact B1951531
  · exact B1951535
  · exact B1951539
  · exact B1951543
  · exact B1951547
  · exact B1951551
  · exact B1951555
  · exact B1951559
  · exact B1951563
  · exact B1951567
  · exact B1951571
  · exact B1951575
  · exact B1951579
  · exact B1951583
  · exact B1951587
  · exact B1951591
  · exact B1951595
  · exact B1951599
  · exact B1951603
  · exact B1951607
  · exact B1951611
  · exact B1951615
  · exact B1951619
  · exact B1951623
  · exact B1951627
  · exact B1951631
  · exact B1951635
  · exact B1951639
  · exact B1951643
  · exact B1951647
  · exact B1951651
  · exact B1951655
  · exact B1951659
  · exact B1951663
  · exact B1951667
  · exact B1951671
  · exact B1951675
  · exact B1951679
  · exact B1951683
  · exact B1951687
  · exact B1951691
  · exact B1951695
  · exact B1951699
  · exact B1951703
  · exact B1951707
  · exact B1951711
  · exact B1951715
  · exact B1951719
  · exact B1951723
  · exact B1951727
  · exact B1951731
  · exact B1951735
  · exact B1951739
  · exact B1951743
  · exact B1951747
  · exact B1951751
  · exact B1951755
  · exact B1951759
  · exact B1951763
  · exact B1951767
  · exact B1951771
  · exact B1951775
  · exact B1951779
  · exact B1951783
  · exact B1951787
  · exact B1951791
  · exact B1951795
  · exact B1951799
  · exact B1951803
  · exact B1951807
  · exact B1951811
  · exact B1951815
  · exact B1951819
  · exact B1951823
  · exact B1951827
  · exact B1951831
  · exact B1951835
  · exact B1951839
  · exact B1951843
  · exact B1951847
  · exact B1951851
  · exact B1951855
  · exact B1951859
  · exact B1951863
  · exact B1951867
  · exact B1951871
  · exact B1951875
  · exact B1951879
  · exact B1951883
  · exact B1951887
  · exact B1951891
  · exact B1951895
  · exact B1951899
  · exact B1951903
  · exact B1951907
  · exact B1951911
  · exact B1951915
  · exact B1951919
  · exact B1951923
  · exact B1951927
  · exact B1951931
  · exact B1951935
  · exact B1951939
  · exact B1951943
  · exact B1951947
  · exact B1951951
  · exact B1951955
  · exact B1951959
  · exact B1951963
  · exact B1951967
  · exact B1951971
  · exact B1951975
  · exact B1951979
  · exact B1951983
  · exact B1951987
  · exact B1951991
  · exact B1951995
  · exact B1951999
  · exact B1952003
  · exact B1952007
  · exact B1952011
  · exact B1952015
  · exact B1952019
  · exact B1952023
  · exact B1952027
  · exact B1952031
  · exact B1952035
  · exact B1952039
  · exact B1952043
  · exact B1952047
  · exact B1952051
  · exact B1952055
  · exact B1952059
  · exact B1952063
  · exact B1952067
  · exact B1952071
  · exact B1952075
  · exact B1952079
  · exact B1952083
  · exact B1952087
  · exact B1952091
  · exact B1952095
  · exact B1952099
  · exact B1952103
  · exact B1952107
  · exact B1952111
  · exact B1952115
  · exact B1952119
  · exact B1952123
  · exact B1952127
  · exact B1952131
  · exact B1952135
  · exact B1952139
  · exact B1952143
  · exact B1952147
  · exact B1952151
  · exact B1952155
  · exact B1952159
  · exact B1952163
  · exact B1952167
  · exact B1952171
  · exact B1952175
  · exact B1952179
  · exact B1952183
  · exact B1952187
  · exact B1952191
  · exact B1952195
  · exact B1952199
  · exact B1952203
  · exact B1952207
  · exact B1952211
  · exact B1952215
  · exact B1952219
  · exact B1952223
  · exact B1952227
  · exact B1952231
  · exact B1952235
  · exact B1952239
  · exact B1952243
  · exact B1952247
  · exact B1952251
  · exact B1952255
  · exact B1952259
  · exact B1952263
  · exact B1952267
  · exact B1952271
  · exact B1952275
  · exact B1952279
  · exact B1952283
  · exact B1952287
  · exact B1952291
  · exact B1952295
  · exact B1952299
  · exact B1952303
  · exact B1952307
  · exact B1952311
  · exact B1952315
  · exact B1952319
  · exact B1952323
  · exact B1952327
  · exact B1952331
  · exact B1952335
  · exact B1952339
  · exact B1952343
  · exact B1952347
  · exact B1952351
  · exact B1952355
  · exact B1952359
  · exact B1952363
  · exact B1952367
  · exact B1952371
  · exact B1952375
  · exact B1952379
  · exact B1952383
  · exact B1952387
  · exact B1952391
  · exact B1952395
  · exact B1952399
  · exact B1952403
  · exact B1952407
  · exact B1952411
  · exact B1952415
  · exact B1952419
  · exact B1952423
  · exact B1952427
  · exact B1952431
  · exact B1952435
  · exact B1952439
  · exact B1952443
  · exact B1952447
  · exact B1952451
  · exact B1952455
  · exact B1952459
  · exact B1952463
  · exact B1952467
  · exact B1952471
  · exact B1952475
  · exact B1952479
  · exact B1952483
  · exact B1952487
  · exact B1952491
  · exact B1952495
  · exact B1952499
  · exact B1952503
  · exact B1952507
  · exact B1952511
  · exact B1952515
  · exact B1952519
  · exact B1952523
  · exact B1952527
  · exact B1952531
  · exact B1952535
  · exact B1952539
  · exact B1952543
  · exact B1952547
  · exact B1952551
  · exact B1952555
  · exact B1952559
  · exact B1952563
  · exact B1952567
  · exact B1952571
  · exact B1952575
  · exact B1952579
  · exact B1952583
  · exact B1952587
  · exact B1952591
  · exact B1952595
  · exact B1952599
  · exact B1952603
  · exact B1952607
  · exact B1952611
  · exact B1952615
  · exact B1952619
  · exact B1952623
  · exact B1952627
  · exact B1952631
  · exact B1952635
  · exact B1952639
  · exact B1952643
  · exact B1952647
  · exact B1952651
  · exact B1952655
  · exact B1952659
  · exact B1952663
  · exact B1952667
  · exact B1952671
  · exact B1952675
  · exact B1952679
  · exact B1952683
  · exact B1952687
  · exact B1952691
  · exact B1952695
  · exact B1952699
  · exact B1952703
  · exact B1952707
  · exact B1952711
  · exact B1952715
  · exact B1952719
  · exact B1952723
  · exact B1952727
  · exact B1952731
  · exact B1952735
  · exact B1952739
  · exact B1952743
  · exact B1952747
  · exact B1952751
  · exact B1952755
  · exact B1952759
  · exact B1952763
  · exact B1952767
  · exact B1952771
  · exact B1952775
  · exact B1952779
  · exact B1952783
  · exact B1952787
  · exact B1952791
  · exact B1952795
  · exact B1952799
  · exact B1952803
  · exact B1952807
  · exact B1952811
  · exact B1952815
  · exact B1952819
  · exact B1952823
  · exact B1952827
  · exact B1952831
  · exact B1952835
  · exact B1952839
  · exact B1952843
  · exact B1952847
  · exact B1952851
  · exact B1952855
  · exact B1952859
  · exact B1952863
  · exact B1952867
  · exact B1952871
  · exact B1952875
  · exact B1952879
  · exact B1952883
  · exact B1952887
  · exact B1952891
  · exact B1952895
  · exact B1952899
  · exact B1952903
  · exact B1952907
  · exact B1952911
  · exact B1952915
  · exact B1952919
  · exact B1952923
  · exact B1952927
  · exact B1952931
  · exact B1952935
  · exact B1952939
  · exact B1952943
  · exact B1952947
  · exact B1952951
  · exact B1952955
  · exact B1952959
  · exact B1952963
  · exact B1952967
  · exact B1952971
  · exact B1952975
  · exact B1952979
  · exact B1952983
  · exact B1952987
  · exact B1952991
  · exact B1952995
  · exact B1952999
  · exact B1953003
  · exact B1953007
  · exact B1953011
  · exact B1953015
  · exact B1953019
  · exact B1953023
  · exact B1953027
  · exact B1953031
  · exact B1953035
  · exact B1953039
  · exact B1953043
  · exact B1953047
  · exact B1953051
  · exact B1953055
  · exact B1953059
  · exact B1953063
  · exact B1953067
  · exact B1953071
  · exact B1953075
  · exact B1953079
  · exact B1953083
  · exact B1953087
  · exact B1953091
  · exact B1953095
  · exact B1953099
  · exact B1953103
  · exact B1953107
  · exact B1953111
  · exact B1953115
  · exact B1953119
  · exact B1953123
  · exact B1953127
  · exact B1953131
  · exact B1953135
  · exact B1953139
  · exact B1953143
  · exact B1953147
  · exact B1953151
  · exact B1953155
  · exact B1953159
  · exact B1953163
  · exact B1953167
  · exact B1953171
  · exact B1953175
  · exact B1953179
  · exact B1953183
  · exact B1953187
  · exact B1953191
  · exact B1953195
  · exact B1953199
  · exact B1953203
  · exact B1953207
  · exact B1953211
  · exact B1953215
  · exact B1953219
  · exact B1953223
  · exact B1953227
  · exact B1953231
  · exact B1953235
  · exact B1953239
  · exact B1953243
  · exact B1953247
  · exact B1953251
  · exact B1953255
  · exact B1953259
  · exact B1953263
  · exact B1953267
  · exact B1953271
  · exact B1953275
  · exact B1953279
  · exact B1953283
  · exact B1953287
  · exact B1953291
  · exact B1953295
  · exact B1953299
  · exact B1953303
  · exact B1953307
  · exact B1953311
  · exact B1953315
  · exact B1953319
  · exact B1953323
  · exact B1953327
  · exact B1953331
  · exact B1953335
  · exact B1953339
  · exact B1953343
  · exact B1953347
  · exact B1953351
  · exact B1953355
  · exact B1953359
  · exact B1953363
  · exact B1953367
  · exact B1953371
  · exact B1953375
  · exact B1953379
  · exact B1953383
  · exact B1953387
  · exact B1953391
  · exact B1953395
  · exact B1953399
  · exact B1953403
  · exact B1953407
  · exact B1953411
  · exact B1953415
  · exact B1953419
  · exact B1953423
  · exact B1953427
  · exact B1953431
  · exact B1953435
theorem solution (m : ℕ) (hlo : 1951435 ≤ m) (hhi : m ≤ 1953435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 487858 ≤ j := by omega
    have hj2 : j ≤ 488358 := by omega
    have hb : Blo 1951435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
