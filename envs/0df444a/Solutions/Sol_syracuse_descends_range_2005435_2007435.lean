-- Prove2me | solution 1 for syracuse_descends_range_2005435_2007435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:37.627897+00:00
-- url     : https://prove2.me/submissions/1d055568-77c2-4cb4-b640-a0495ec4a1ee

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

theorem B3384173 : Blo 2005435 3384173 := bbase (se 3 (by rfl) ⟨634532, by rfl⟩ : syracuseStep 3384173 = 1269065) (by norm_num)
theorem B2256115 : Blo 2005435 2256115 := bstep (se 1 (by rfl) ⟨1692086, by rfl⟩ : syracuseStep 2256115 = 3384173) B3384173
theorem B3008153 : Blo 2005435 3008153 := bstep (se 2 (by rfl) ⟨1128057, by rfl⟩ : syracuseStep 3008153 = 2256115) B2256115
theorem B2005435 : Blo 2005435 2005435 := bstep (se 1 (by rfl) ⟨1504076, by rfl⟩ : syracuseStep 2005435 = 3008153) B3008153
theorem B4636205 : Blo 2005435 4636205 := bbase (se 3 (by rfl) ⟨869288, by rfl⟩ : syracuseStep 4636205 = 1738577) (by norm_num)
theorem B3090803 : Blo 2005435 3090803 := bstep (se 1 (by rfl) ⟨2318102, by rfl⟩ : syracuseStep 3090803 = 4636205) B4636205
theorem B32968565 : Blo 2005435 32968565 := bstep (se 5 (by rfl) ⟨1545401, by rfl⟩ : syracuseStep 32968565 = 3090803) B3090803
theorem B21979043 : Blo 2005435 21979043 := bstep (se 1 (by rfl) ⟨16484282, by rfl⟩ : syracuseStep 21979043 = 32968565) B32968565
theorem B14652695 : Blo 2005435 14652695 := bstep (se 1 (by rfl) ⟨10989521, by rfl⟩ : syracuseStep 14652695 = 21979043) B21979043
theorem B39073853 : Blo 2005435 39073853 := bstep (se 3 (by rfl) ⟨7326347, by rfl⟩ : syracuseStep 39073853 = 14652695) B14652695
theorem B26049235 : Blo 2005435 26049235 := bstep (se 1 (by rfl) ⟨19536926, by rfl⟩ : syracuseStep 26049235 = 39073853) B39073853
theorem B34732313 : Blo 2005435 34732313 := bstep (se 2 (by rfl) ⟨13024617, by rfl⟩ : syracuseStep 34732313 = 26049235) B26049235
theorem B23154875 : Blo 2005435 23154875 := bstep (se 1 (by rfl) ⟨17366156, by rfl⟩ : syracuseStep 23154875 = 34732313) B34732313
theorem B15436583 : Blo 2005435 15436583 := bstep (se 1 (by rfl) ⟨11577437, by rfl⟩ : syracuseStep 15436583 = 23154875) B23154875
theorem B10291055 : Blo 2005435 10291055 := bstep (se 1 (by rfl) ⟨7718291, by rfl⟩ : syracuseStep 10291055 = 15436583) B15436583
theorem B27442813 : Blo 2005435 27442813 := bstep (se 3 (by rfl) ⟨5145527, by rfl⟩ : syracuseStep 27442813 = 10291055) B10291055
theorem B36590417 : Blo 2005435 36590417 := bstep (se 2 (by rfl) ⟨13721406, by rfl⟩ : syracuseStep 36590417 = 27442813) B27442813
theorem B24393611 : Blo 2005435 24393611 := bstep (se 1 (by rfl) ⟨18295208, by rfl⟩ : syracuseStep 24393611 = 36590417) B36590417
theorem B16262407 : Blo 2005435 16262407 := bstep (se 1 (by rfl) ⟨12196805, by rfl⟩ : syracuseStep 16262407 = 24393611) B24393611
theorem B21683209 : Blo 2005435 21683209 := bstep (se 2 (by rfl) ⟨8131203, by rfl⟩ : syracuseStep 21683209 = 16262407) B16262407
theorem B28910945 : Blo 2005435 28910945 := bstep (se 2 (by rfl) ⟨10841604, by rfl⟩ : syracuseStep 28910945 = 21683209) B21683209
theorem B19273963 : Blo 2005435 19273963 := bstep (se 1 (by rfl) ⟨14455472, by rfl⟩ : syracuseStep 19273963 = 28910945) B28910945
theorem B25698617 : Blo 2005435 25698617 := bstep (se 2 (by rfl) ⟨9636981, by rfl⟩ : syracuseStep 25698617 = 19273963) B19273963
theorem B17132411 : Blo 2005435 17132411 := bstep (se 1 (by rfl) ⟨12849308, by rfl⟩ : syracuseStep 17132411 = 25698617) B25698617
theorem B11421607 : Blo 2005435 11421607 := bstep (se 1 (by rfl) ⟨8566205, by rfl⟩ : syracuseStep 11421607 = 17132411) B17132411
theorem B15228809 : Blo 2005435 15228809 := bstep (se 2 (by rfl) ⟨5710803, by rfl⟩ : syracuseStep 15228809 = 11421607) B11421607
theorem B10152539 : Blo 2005435 10152539 := bstep (se 1 (by rfl) ⟨7614404, by rfl⟩ : syracuseStep 10152539 = 15228809) B15228809
theorem B6768359 : Blo 2005435 6768359 := bstep (se 1 (by rfl) ⟨5076269, by rfl⟩ : syracuseStep 6768359 = 10152539) B10152539
theorem B4512239 : Blo 2005435 4512239 := bstep (se 1 (by rfl) ⟨3384179, by rfl⟩ : syracuseStep 4512239 = 6768359) B6768359
theorem B3008159 : Blo 2005435 3008159 := bstep (se 1 (by rfl) ⟨2256119, by rfl⟩ : syracuseStep 3008159 = 4512239) B4512239
theorem B2005439 : Blo 2005435 2005439 := bstep (se 1 (by rfl) ⟨1504079, by rfl⟩ : syracuseStep 2005439 = 3008159) B3008159
theorem B3008165 : Blo 2005435 3008165 := bbase (se 4 (by rfl) ⟨282015, by rfl⟩ : syracuseStep 3008165 = 564031) (by norm_num)
theorem B2005443 : Blo 2005435 2005443 := bstep (se 1 (by rfl) ⟨1504082, by rfl⟩ : syracuseStep 2005443 = 3008165) B3008165
theorem B2538145 : Blo 2005435 2538145 := bbase (se 2 (by rfl) ⟨951804, by rfl⟩ : syracuseStep 2538145 = 1903609) (by norm_num)
theorem B3384193 : Blo 2005435 3384193 := bstep (se 2 (by rfl) ⟨1269072, by rfl⟩ : syracuseStep 3384193 = 2538145) B2538145
theorem B4512257 : Blo 2005435 4512257 := bstep (se 2 (by rfl) ⟨1692096, by rfl⟩ : syracuseStep 4512257 = 3384193) B3384193
theorem B3008171 : Blo 2005435 3008171 := bstep (se 1 (by rfl) ⟨2256128, by rfl⟩ : syracuseStep 3008171 = 4512257) B4512257
theorem B2005447 : Blo 2005435 2005447 := bstep (se 1 (by rfl) ⟨1504085, by rfl⟩ : syracuseStep 2005447 = 3008171) B3008171
theorem B2256133 : Blo 2005435 2256133 := bbase (se 4 (by rfl) ⟨211512, by rfl⟩ : syracuseStep 2256133 = 423025) (by norm_num)
theorem B3008177 : Blo 2005435 3008177 := bstep (se 2 (by rfl) ⟨1128066, by rfl⟩ : syracuseStep 3008177 = 2256133) B2256133
theorem B2005451 : Blo 2005435 2005451 := bstep (se 1 (by rfl) ⟨1504088, by rfl⟩ : syracuseStep 2005451 = 3008177) B3008177
theorem B2141569 : Blo 2005435 2141569 := bbase (se 2 (by rfl) ⟨803088, by rfl⟩ : syracuseStep 2141569 = 1606177) (by norm_num)
theorem B2855425 : Blo 2005435 2855425 := bstep (se 2 (by rfl) ⟨1070784, by rfl⟩ : syracuseStep 2855425 = 2141569) B2141569
theorem B3807233 : Blo 2005435 3807233 := bstep (se 2 (by rfl) ⟨1427712, by rfl⟩ : syracuseStep 3807233 = 2855425) B2855425
theorem B2538155 : Blo 2005435 2538155 := bstep (se 1 (by rfl) ⟨1903616, by rfl⟩ : syracuseStep 2538155 = 3807233) B3807233
theorem B6768413 : Blo 2005435 6768413 := bstep (se 3 (by rfl) ⟨1269077, by rfl⟩ : syracuseStep 6768413 = 2538155) B2538155
theorem B4512275 : Blo 2005435 4512275 := bstep (se 1 (by rfl) ⟨3384206, by rfl⟩ : syracuseStep 4512275 = 6768413) B6768413
theorem B3008183 : Blo 2005435 3008183 := bstep (se 1 (by rfl) ⟨2256137, by rfl⟩ : syracuseStep 3008183 = 4512275) B4512275
theorem B2005455 : Blo 2005435 2005455 := bstep (se 1 (by rfl) ⟨1504091, by rfl⟩ : syracuseStep 2005455 = 3008183) B3008183
theorem B3008189 : Blo 2005435 3008189 := bbase (se 3 (by rfl) ⟨564035, by rfl⟩ : syracuseStep 3008189 = 1128071) (by norm_num)
theorem B2005459 : Blo 2005435 2005459 := bstep (se 1 (by rfl) ⟨1504094, by rfl⟩ : syracuseStep 2005459 = 3008189) B3008189
theorem B4512293 : Blo 2005435 4512293 := bbase (se 4 (by rfl) ⟨423027, by rfl⟩ : syracuseStep 4512293 = 846055) (by norm_num)
theorem B3008195 : Blo 2005435 3008195 := bstep (se 1 (by rfl) ⟨2256146, by rfl⟩ : syracuseStep 3008195 = 4512293) B4512293
theorem B2005463 : Blo 2005435 2005463 := bstep (se 1 (by rfl) ⟨1504097, by rfl⟩ : syracuseStep 2005463 = 3008195) B3008195
theorem B5076341 : Blo 2005435 5076341 := bbase (se 5 (by rfl) ⟨237953, by rfl⟩ : syracuseStep 5076341 = 475907) (by norm_num)
theorem B3384227 : Blo 2005435 3384227 := bstep (se 1 (by rfl) ⟨2538170, by rfl⟩ : syracuseStep 3384227 = 5076341) B5076341
theorem B2256151 : Blo 2005435 2256151 := bstep (se 1 (by rfl) ⟨1692113, by rfl⟩ : syracuseStep 2256151 = 3384227) B3384227
theorem B3008201 : Blo 2005435 3008201 := bstep (se 2 (by rfl) ⟨1128075, by rfl⟩ : syracuseStep 3008201 = 2256151) B2256151
theorem B2005467 : Blo 2005435 2005467 := bstep (se 1 (by rfl) ⟨1504100, by rfl⟩ : syracuseStep 2005467 = 3008201) B3008201
theorem B6098501 : Blo 2005435 6098501 := bbase (se 4 (by rfl) ⟨571734, by rfl⟩ : syracuseStep 6098501 = 1143469) (by norm_num)
theorem B16262669 : Blo 2005435 16262669 := bstep (se 3 (by rfl) ⟨3049250, by rfl⟩ : syracuseStep 16262669 = 6098501) B6098501
theorem B10841779 : Blo 2005435 10841779 := bstep (se 1 (by rfl) ⟨8131334, by rfl⟩ : syracuseStep 10841779 = 16262669) B16262669
theorem B14455705 : Blo 2005435 14455705 := bstep (se 2 (by rfl) ⟨5420889, by rfl⟩ : syracuseStep 14455705 = 10841779) B10841779
theorem B19274273 : Blo 2005435 19274273 := bstep (se 2 (by rfl) ⟨7227852, by rfl⟩ : syracuseStep 19274273 = 14455705) B14455705
theorem B12849515 : Blo 2005435 12849515 := bstep (se 1 (by rfl) ⟨9637136, by rfl⟩ : syracuseStep 12849515 = 19274273) B19274273
theorem B8566343 : Blo 2005435 8566343 := bstep (se 1 (by rfl) ⟨6424757, by rfl⟩ : syracuseStep 8566343 = 12849515) B12849515
theorem B5710895 : Blo 2005435 5710895 := bstep (se 1 (by rfl) ⟨4283171, by rfl⟩ : syracuseStep 5710895 = 8566343) B8566343
theorem B3807263 : Blo 2005435 3807263 := bstep (se 1 (by rfl) ⟨2855447, by rfl⟩ : syracuseStep 3807263 = 5710895) B5710895
theorem B10152701 : Blo 2005435 10152701 := bstep (se 3 (by rfl) ⟨1903631, by rfl⟩ : syracuseStep 10152701 = 3807263) B3807263
theorem B6768467 : Blo 2005435 6768467 := bstep (se 1 (by rfl) ⟨5076350, by rfl⟩ : syracuseStep 6768467 = 10152701) B10152701
theorem B4512311 : Blo 2005435 4512311 := bstep (se 1 (by rfl) ⟨3384233, by rfl⟩ : syracuseStep 4512311 = 6768467) B6768467
theorem B3008207 : Blo 2005435 3008207 := bstep (se 1 (by rfl) ⟨2256155, by rfl⟩ : syracuseStep 3008207 = 4512311) B4512311
theorem B2005471 : Blo 2005435 2005471 := bstep (se 1 (by rfl) ⟨1504103, by rfl⟩ : syracuseStep 2005471 = 3008207) B3008207
theorem B3008213 : Blo 2005435 3008213 := bbase (se 7 (by rfl) ⟨35252, by rfl⟩ : syracuseStep 3008213 = 70505) (by norm_num)
theorem B2005475 : Blo 2005435 2005475 := bstep (se 1 (by rfl) ⟨1504106, by rfl⟩ : syracuseStep 2005475 = 3008213) B3008213
theorem B4283189 : Blo 2005435 4283189 := bbase (se 5 (by rfl) ⟨200774, by rfl⟩ : syracuseStep 4283189 = 401549) (by norm_num)
theorem B2855459 : Blo 2005435 2855459 := bstep (se 1 (by rfl) ⟨2141594, by rfl⟩ : syracuseStep 2855459 = 4283189) B4283189
theorem B7614557 : Blo 2005435 7614557 := bstep (se 3 (by rfl) ⟨1427729, by rfl⟩ : syracuseStep 7614557 = 2855459) B2855459
theorem B5076371 : Blo 2005435 5076371 := bstep (se 1 (by rfl) ⟨3807278, by rfl⟩ : syracuseStep 5076371 = 7614557) B7614557
theorem B3384247 : Blo 2005435 3384247 := bstep (se 1 (by rfl) ⟨2538185, by rfl⟩ : syracuseStep 3384247 = 5076371) B5076371
theorem B4512329 : Blo 2005435 4512329 := bstep (se 2 (by rfl) ⟨1692123, by rfl⟩ : syracuseStep 4512329 = 3384247) B3384247
theorem B3008219 : Blo 2005435 3008219 := bstep (se 1 (by rfl) ⟨2256164, by rfl⟩ : syracuseStep 3008219 = 4512329) B4512329
theorem B2005479 : Blo 2005435 2005479 := bstep (se 1 (by rfl) ⟨1504109, by rfl⟩ : syracuseStep 2005479 = 3008219) B3008219
theorem B2256169 : Blo 2005435 2256169 := bbase (se 2 (by rfl) ⟨846063, by rfl⟩ : syracuseStep 2256169 = 1692127) (by norm_num)
theorem B3008225 : Blo 2005435 3008225 := bstep (se 2 (by rfl) ⟨1128084, by rfl⟩ : syracuseStep 3008225 = 2256169) B2256169
theorem B2005483 : Blo 2005435 2005483 := bstep (se 1 (by rfl) ⟨1504112, by rfl⟩ : syracuseStep 2005483 = 3008225) B3008225
theorem B5420933 : Blo 2005435 5420933 := bbase (se 4 (by rfl) ⟨508212, by rfl⟩ : syracuseStep 5420933 = 1016425) (by norm_num)
theorem B3613955 : Blo 2005435 3613955 := bstep (se 1 (by rfl) ⟨2710466, by rfl⟩ : syracuseStep 3613955 = 5420933) B5420933
theorem B9637213 : Blo 2005435 9637213 := bstep (se 3 (by rfl) ⟨1806977, by rfl⟩ : syracuseStep 9637213 = 3613955) B3613955
theorem B12849617 : Blo 2005435 12849617 := bstep (se 2 (by rfl) ⟨4818606, by rfl⟩ : syracuseStep 12849617 = 9637213) B9637213
theorem B8566411 : Blo 2005435 8566411 := bstep (se 1 (by rfl) ⟨6424808, by rfl⟩ : syracuseStep 8566411 = 12849617) B12849617
theorem B11421881 : Blo 2005435 11421881 := bstep (se 2 (by rfl) ⟨4283205, by rfl⟩ : syracuseStep 11421881 = 8566411) B8566411
theorem B7614587 : Blo 2005435 7614587 := bstep (se 1 (by rfl) ⟨5710940, by rfl⟩ : syracuseStep 7614587 = 11421881) B11421881
theorem B5076391 : Blo 2005435 5076391 := bstep (se 1 (by rfl) ⟨3807293, by rfl⟩ : syracuseStep 5076391 = 7614587) B7614587
theorem B6768521 : Blo 2005435 6768521 := bstep (se 2 (by rfl) ⟨2538195, by rfl⟩ : syracuseStep 6768521 = 5076391) B5076391
theorem B4512347 : Blo 2005435 4512347 := bstep (se 1 (by rfl) ⟨3384260, by rfl⟩ : syracuseStep 4512347 = 6768521) B6768521
theorem B3008231 : Blo 2005435 3008231 := bstep (se 1 (by rfl) ⟨2256173, by rfl⟩ : syracuseStep 3008231 = 4512347) B4512347
theorem B2005487 : Blo 2005435 2005487 := bstep (se 1 (by rfl) ⟨1504115, by rfl⟩ : syracuseStep 2005487 = 3008231) B3008231
theorem B3008237 : Blo 2005435 3008237 := bbase (se 3 (by rfl) ⟨564044, by rfl⟩ : syracuseStep 3008237 = 1128089) (by norm_num)
theorem B2005491 : Blo 2005435 2005491 := bstep (se 1 (by rfl) ⟨1504118, by rfl⟩ : syracuseStep 2005491 = 3008237) B3008237
theorem B4512365 : Blo 2005435 4512365 := bbase (se 3 (by rfl) ⟨846068, by rfl⟩ : syracuseStep 4512365 = 1692137) (by norm_num)
theorem B3008243 : Blo 2005435 3008243 := bstep (se 1 (by rfl) ⟨2256182, by rfl⟩ : syracuseStep 3008243 = 4512365) B4512365
theorem B2005495 : Blo 2005435 2005495 := bstep (se 1 (by rfl) ⟨1504121, by rfl⟩ : syracuseStep 2005495 = 3008243) B3008243
theorem B3807317 : Blo 2005435 3807317 := bbase (se 8 (by rfl) ⟨22308, by rfl⟩ : syracuseStep 3807317 = 44617) (by norm_num)
theorem B2538211 : Blo 2005435 2538211 := bstep (se 1 (by rfl) ⟨1903658, by rfl⟩ : syracuseStep 2538211 = 3807317) B3807317
theorem B3384281 : Blo 2005435 3384281 := bstep (se 2 (by rfl) ⟨1269105, by rfl⟩ : syracuseStep 3384281 = 2538211) B2538211
theorem B2256187 : Blo 2005435 2256187 := bstep (se 1 (by rfl) ⟨1692140, by rfl⟩ : syracuseStep 2256187 = 3384281) B3384281
theorem B3008249 : Blo 2005435 3008249 := bstep (se 2 (by rfl) ⟨1128093, by rfl⟩ : syracuseStep 3008249 = 2256187) B2256187
theorem B2005499 : Blo 2005435 2005499 := bstep (se 1 (by rfl) ⟨1504124, by rfl⟩ : syracuseStep 2005499 = 3008249) B3008249
theorem B13721845 : Blo 2005435 13721845 := bbase (se 5 (by rfl) ⟨643211, by rfl⟩ : syracuseStep 13721845 = 1286423) (by norm_num)
theorem B18295793 : Blo 2005435 18295793 := bstep (se 2 (by rfl) ⟨6860922, by rfl⟩ : syracuseStep 18295793 = 13721845) B13721845
theorem B12197195 : Blo 2005435 12197195 := bstep (se 1 (by rfl) ⟨9147896, by rfl⟩ : syracuseStep 12197195 = 18295793) B18295793
theorem B8131463 : Blo 2005435 8131463 := bstep (se 1 (by rfl) ⟨6098597, by rfl⟩ : syracuseStep 8131463 = 12197195) B12197195
theorem B5420975 : Blo 2005435 5420975 := bstep (se 1 (by rfl) ⟨4065731, by rfl⟩ : syracuseStep 5420975 = 8131463) B8131463
theorem B57823733 : Blo 2005435 57823733 := bstep (se 5 (by rfl) ⟨2710487, by rfl⟩ : syracuseStep 57823733 = 5420975) B5420975
theorem B38549155 : Blo 2005435 38549155 := bstep (se 1 (by rfl) ⟨28911866, by rfl⟩ : syracuseStep 38549155 = 57823733) B57823733
theorem B51398873 : Blo 2005435 51398873 := bstep (se 2 (by rfl) ⟨19274577, by rfl⟩ : syracuseStep 51398873 = 38549155) B38549155
theorem B34265915 : Blo 2005435 34265915 := bstep (se 1 (by rfl) ⟨25699436, by rfl⟩ : syracuseStep 34265915 = 51398873) B51398873
theorem B22843943 : Blo 2005435 22843943 := bstep (se 1 (by rfl) ⟨17132957, by rfl⟩ : syracuseStep 22843943 = 34265915) B34265915
theorem B15229295 : Blo 2005435 15229295 := bstep (se 1 (by rfl) ⟨11421971, by rfl⟩ : syracuseStep 15229295 = 22843943) B22843943
theorem B10152863 : Blo 2005435 10152863 := bstep (se 1 (by rfl) ⟨7614647, by rfl⟩ : syracuseStep 10152863 = 15229295) B15229295
theorem B6768575 : Blo 2005435 6768575 := bstep (se 1 (by rfl) ⟨5076431, by rfl⟩ : syracuseStep 6768575 = 10152863) B10152863
theorem B4512383 : Blo 2005435 4512383 := bstep (se 1 (by rfl) ⟨3384287, by rfl⟩ : syracuseStep 4512383 = 6768575) B6768575
theorem B3008255 : Blo 2005435 3008255 := bstep (se 1 (by rfl) ⟨2256191, by rfl⟩ : syracuseStep 3008255 = 4512383) B4512383
theorem B2005503 : Blo 2005435 2005503 := bstep (se 1 (by rfl) ⟨1504127, by rfl⟩ : syracuseStep 2005503 = 3008255) B3008255
theorem B3008261 : Blo 2005435 3008261 := bbase (se 4 (by rfl) ⟨282024, by rfl⟩ : syracuseStep 3008261 = 564049) (by norm_num)
theorem B2005507 : Blo 2005435 2005507 := bstep (se 1 (by rfl) ⟨1504130, by rfl⟩ : syracuseStep 2005507 = 3008261) B3008261
theorem B3384301 : Blo 2005435 3384301 := bbase (se 3 (by rfl) ⟨634556, by rfl⟩ : syracuseStep 3384301 = 1269113) (by norm_num)
theorem B4512401 : Blo 2005435 4512401 := bstep (se 2 (by rfl) ⟨1692150, by rfl⟩ : syracuseStep 4512401 = 3384301) B3384301
theorem B3008267 : Blo 2005435 3008267 := bstep (se 1 (by rfl) ⟨2256200, by rfl⟩ : syracuseStep 3008267 = 4512401) B4512401
theorem B2005511 : Blo 2005435 2005511 := bstep (se 1 (by rfl) ⟨1504133, by rfl⟩ : syracuseStep 2005511 = 3008267) B3008267
theorem B2256205 : Blo 2005435 2256205 := bbase (se 3 (by rfl) ⟨423038, by rfl⟩ : syracuseStep 2256205 = 846077) (by norm_num)
theorem B3008273 : Blo 2005435 3008273 := bstep (se 2 (by rfl) ⟨1128102, by rfl⟩ : syracuseStep 3008273 = 2256205) B2256205
theorem B2005515 : Blo 2005435 2005515 := bstep (se 1 (by rfl) ⟨1504136, by rfl⟩ : syracuseStep 2005515 = 3008273) B3008273
theorem B6768629 : Blo 2005435 6768629 := bbase (se 5 (by rfl) ⟨317279, by rfl⟩ : syracuseStep 6768629 = 634559) (by norm_num)
theorem B4512419 : Blo 2005435 4512419 := bstep (se 1 (by rfl) ⟨3384314, by rfl⟩ : syracuseStep 4512419 = 6768629) B6768629
theorem B3008279 : Blo 2005435 3008279 := bstep (se 1 (by rfl) ⟨2256209, by rfl⟩ : syracuseStep 3008279 = 4512419) B4512419
theorem B2005519 : Blo 2005435 2005519 := bstep (se 1 (by rfl) ⟨1504139, by rfl⟩ : syracuseStep 2005519 = 3008279) B3008279
theorem B3008285 : Blo 2005435 3008285 := bbase (se 3 (by rfl) ⟨564053, by rfl⟩ : syracuseStep 3008285 = 1128107) (by norm_num)
theorem B2005523 : Blo 2005435 2005523 := bstep (se 1 (by rfl) ⟨1504142, by rfl⟩ : syracuseStep 2005523 = 3008285) B3008285
theorem B4512437 : Blo 2005435 4512437 := bbase (se 5 (by rfl) ⟨211520, by rfl⟩ : syracuseStep 4512437 = 423041) (by norm_num)
theorem B3008291 : Blo 2005435 3008291 := bstep (se 1 (by rfl) ⟨2256218, by rfl⟩ : syracuseStep 3008291 = 4512437) B4512437
theorem B2005527 : Blo 2005435 2005527 := bstep (se 1 (by rfl) ⟨1504145, by rfl⟩ : syracuseStep 2005527 = 3008291) B3008291
theorem B11422133 : Blo 2005435 11422133 := bbase (se 5 (by rfl) ⟨535412, by rfl⟩ : syracuseStep 11422133 = 1070825) (by norm_num)
theorem B7614755 : Blo 2005435 7614755 := bstep (se 1 (by rfl) ⟨5711066, by rfl⟩ : syracuseStep 7614755 = 11422133) B11422133
theorem B5076503 : Blo 2005435 5076503 := bstep (se 1 (by rfl) ⟨3807377, by rfl⟩ : syracuseStep 5076503 = 7614755) B7614755
theorem B3384335 : Blo 2005435 3384335 := bstep (se 1 (by rfl) ⟨2538251, by rfl⟩ : syracuseStep 3384335 = 5076503) B5076503
theorem B2256223 : Blo 2005435 2256223 := bstep (se 1 (by rfl) ⟨1692167, by rfl⟩ : syracuseStep 2256223 = 3384335) B3384335
theorem B3008297 : Blo 2005435 3008297 := bstep (se 2 (by rfl) ⟨1128111, by rfl⟩ : syracuseStep 3008297 = 2256223) B2256223
theorem B2005531 : Blo 2005435 2005531 := bstep (se 1 (by rfl) ⟨1504148, by rfl⟩ : syracuseStep 2005531 = 3008297) B3008297
theorem B5711077 : Blo 2005435 5711077 := bbase (se 4 (by rfl) ⟨535413, by rfl⟩ : syracuseStep 5711077 = 1070827) (by norm_num)
theorem B7614769 : Blo 2005435 7614769 := bstep (se 2 (by rfl) ⟨2855538, by rfl⟩ : syracuseStep 7614769 = 5711077) B5711077
theorem B10153025 : Blo 2005435 10153025 := bstep (se 2 (by rfl) ⟨3807384, by rfl⟩ : syracuseStep 10153025 = 7614769) B7614769
theorem B6768683 : Blo 2005435 6768683 := bstep (se 1 (by rfl) ⟨5076512, by rfl⟩ : syracuseStep 6768683 = 10153025) B10153025
theorem B4512455 : Blo 2005435 4512455 := bstep (se 1 (by rfl) ⟨3384341, by rfl⟩ : syracuseStep 4512455 = 6768683) B6768683
theorem B3008303 : Blo 2005435 3008303 := bstep (se 1 (by rfl) ⟨2256227, by rfl⟩ : syracuseStep 3008303 = 4512455) B4512455
theorem B2005535 : Blo 2005435 2005535 := bstep (se 1 (by rfl) ⟨1504151, by rfl⟩ : syracuseStep 2005535 = 3008303) B3008303
theorem B3008309 : Blo 2005435 3008309 := bbase (se 5 (by rfl) ⟨141014, by rfl⟩ : syracuseStep 3008309 = 282029) (by norm_num)
theorem B2005539 : Blo 2005435 2005539 := bstep (se 1 (by rfl) ⟨1504154, by rfl⟩ : syracuseStep 2005539 = 3008309) B3008309
theorem B5076533 : Blo 2005435 5076533 := bbase (se 5 (by rfl) ⟨237962, by rfl⟩ : syracuseStep 5076533 = 475925) (by norm_num)
theorem B3384355 : Blo 2005435 3384355 := bstep (se 1 (by rfl) ⟨2538266, by rfl⟩ : syracuseStep 3384355 = 5076533) B5076533
theorem B4512473 : Blo 2005435 4512473 := bstep (se 2 (by rfl) ⟨1692177, by rfl⟩ : syracuseStep 4512473 = 3384355) B3384355
theorem B3008315 : Blo 2005435 3008315 := bstep (se 1 (by rfl) ⟨2256236, by rfl⟩ : syracuseStep 3008315 = 4512473) B4512473
theorem B2005543 : Blo 2005435 2005543 := bstep (se 1 (by rfl) ⟨1504157, by rfl⟩ : syracuseStep 2005543 = 3008315) B3008315
theorem B2256241 : Blo 2005435 2256241 := bbase (se 2 (by rfl) ⟨846090, by rfl⟩ : syracuseStep 2256241 = 1692181) (by norm_num)
theorem B3008321 : Blo 2005435 3008321 := bstep (se 2 (by rfl) ⟨1128120, by rfl⟩ : syracuseStep 3008321 = 2256241) B2256241
theorem B2005547 : Blo 2005435 2005547 := bstep (se 1 (by rfl) ⟨1504160, by rfl⟩ : syracuseStep 2005547 = 3008321) B3008321
theorem B3049373 : Blo 2005435 3049373 := bbase (se 3 (by rfl) ⟨571757, by rfl⟩ : syracuseStep 3049373 = 1143515) (by norm_num)
theorem B8131661 : Blo 2005435 8131661 := bstep (se 3 (by rfl) ⟨1524686, by rfl⟩ : syracuseStep 8131661 = 3049373) B3049373
theorem B5421107 : Blo 2005435 5421107 := bstep (se 1 (by rfl) ⟨4065830, by rfl⟩ : syracuseStep 5421107 = 8131661) B8131661
theorem B3614071 : Blo 2005435 3614071 := bstep (se 1 (by rfl) ⟨2710553, by rfl⟩ : syracuseStep 3614071 = 5421107) B5421107
theorem B4818761 : Blo 2005435 4818761 := bstep (se 2 (by rfl) ⟨1807035, by rfl⟩ : syracuseStep 4818761 = 3614071) B3614071
theorem B3212507 : Blo 2005435 3212507 := bstep (se 1 (by rfl) ⟨2409380, by rfl⟩ : syracuseStep 3212507 = 4818761) B4818761
theorem B8566685 : Blo 2005435 8566685 := bstep (se 3 (by rfl) ⟨1606253, by rfl⟩ : syracuseStep 8566685 = 3212507) B3212507
theorem B5711123 : Blo 2005435 5711123 := bstep (se 1 (by rfl) ⟨4283342, by rfl⟩ : syracuseStep 5711123 = 8566685) B8566685
theorem B3807415 : Blo 2005435 3807415 := bstep (se 1 (by rfl) ⟨2855561, by rfl⟩ : syracuseStep 3807415 = 5711123) B5711123
theorem B5076553 : Blo 2005435 5076553 := bstep (se 2 (by rfl) ⟨1903707, by rfl⟩ : syracuseStep 5076553 = 3807415) B3807415
theorem B6768737 : Blo 2005435 6768737 := bstep (se 2 (by rfl) ⟨2538276, by rfl⟩ : syracuseStep 6768737 = 5076553) B5076553
theorem B4512491 : Blo 2005435 4512491 := bstep (se 1 (by rfl) ⟨3384368, by rfl⟩ : syracuseStep 4512491 = 6768737) B6768737
theorem B3008327 : Blo 2005435 3008327 := bstep (se 1 (by rfl) ⟨2256245, by rfl⟩ : syracuseStep 3008327 = 4512491) B4512491
theorem B2005551 : Blo 2005435 2005551 := bstep (se 1 (by rfl) ⟨1504163, by rfl⟩ : syracuseStep 2005551 = 3008327) B3008327
theorem B3008333 : Blo 2005435 3008333 := bbase (se 3 (by rfl) ⟨564062, by rfl⟩ : syracuseStep 3008333 = 1128125) (by norm_num)
theorem B2005555 : Blo 2005435 2005555 := bstep (se 1 (by rfl) ⟨1504166, by rfl⟩ : syracuseStep 2005555 = 3008333) B3008333
theorem B4512509 : Blo 2005435 4512509 := bbase (se 3 (by rfl) ⟨846095, by rfl⟩ : syracuseStep 4512509 = 1692191) (by norm_num)
theorem B3008339 : Blo 2005435 3008339 := bstep (se 1 (by rfl) ⟨2256254, by rfl⟩ : syracuseStep 3008339 = 4512509) B4512509
theorem B2005559 : Blo 2005435 2005559 := bstep (se 1 (by rfl) ⟨1504169, by rfl⟩ : syracuseStep 2005559 = 3008339) B3008339
theorem B3384389 : Blo 2005435 3384389 := bbase (se 4 (by rfl) ⟨317286, by rfl⟩ : syracuseStep 3384389 = 634573) (by norm_num)
theorem B2256259 : Blo 2005435 2256259 := bstep (se 1 (by rfl) ⟨1692194, by rfl⟩ : syracuseStep 2256259 = 3384389) B3384389
theorem B3008345 : Blo 2005435 3008345 := bstep (se 2 (by rfl) ⟨1128129, by rfl⟩ : syracuseStep 3008345 = 2256259) B2256259
theorem B2005563 : Blo 2005435 2005563 := bstep (se 1 (by rfl) ⟨1504172, by rfl⟩ : syracuseStep 2005563 = 3008345) B3008345
theorem B15229781 : Blo 2005435 15229781 := bbase (se 9 (by rfl) ⟨44618, by rfl⟩ : syracuseStep 15229781 = 89237) (by norm_num)
theorem B10153187 : Blo 2005435 10153187 := bstep (se 1 (by rfl) ⟨7614890, by rfl⟩ : syracuseStep 10153187 = 15229781) B15229781
theorem B6768791 : Blo 2005435 6768791 := bstep (se 1 (by rfl) ⟨5076593, by rfl⟩ : syracuseStep 6768791 = 10153187) B10153187
theorem B4512527 : Blo 2005435 4512527 := bstep (se 1 (by rfl) ⟨3384395, by rfl⟩ : syracuseStep 4512527 = 6768791) B6768791
theorem B3008351 : Blo 2005435 3008351 := bstep (se 1 (by rfl) ⟨2256263, by rfl⟩ : syracuseStep 3008351 = 4512527) B4512527
theorem B2005567 : Blo 2005435 2005567 := bstep (se 1 (by rfl) ⟨1504175, by rfl⟩ : syracuseStep 2005567 = 3008351) B3008351
theorem B3008357 : Blo 2005435 3008357 := bbase (se 4 (by rfl) ⟨282033, by rfl⟩ : syracuseStep 3008357 = 564067) (by norm_num)
theorem B2005571 : Blo 2005435 2005571 := bstep (se 1 (by rfl) ⟨1504178, by rfl⟩ : syracuseStep 2005571 = 3008357) B3008357
theorem B3807461 : Blo 2005435 3807461 := bbase (se 4 (by rfl) ⟨356949, by rfl⟩ : syracuseStep 3807461 = 713899) (by norm_num)
theorem B2538307 : Blo 2005435 2538307 := bstep (se 1 (by rfl) ⟨1903730, by rfl⟩ : syracuseStep 2538307 = 3807461) B3807461
theorem B3384409 : Blo 2005435 3384409 := bstep (se 2 (by rfl) ⟨1269153, by rfl⟩ : syracuseStep 3384409 = 2538307) B2538307
theorem B4512545 : Blo 2005435 4512545 := bstep (se 2 (by rfl) ⟨1692204, by rfl⟩ : syracuseStep 4512545 = 3384409) B3384409
theorem B3008363 : Blo 2005435 3008363 := bstep (se 1 (by rfl) ⟨2256272, by rfl⟩ : syracuseStep 3008363 = 4512545) B4512545
theorem B2005575 : Blo 2005435 2005575 := bstep (se 1 (by rfl) ⟨1504181, by rfl⟩ : syracuseStep 2005575 = 3008363) B3008363
theorem B2256277 : Blo 2005435 2256277 := bbase (se 6 (by rfl) ⟨52881, by rfl⟩ : syracuseStep 2256277 = 105763) (by norm_num)
theorem B3008369 : Blo 2005435 3008369 := bstep (se 2 (by rfl) ⟨1128138, by rfl⟩ : syracuseStep 3008369 = 2256277) B2256277
theorem B2005579 : Blo 2005435 2005579 := bstep (se 1 (by rfl) ⟨1504184, by rfl⟩ : syracuseStep 2005579 = 3008369) B3008369
theorem B2538317 : Blo 2005435 2538317 := bbase (se 3 (by rfl) ⟨475934, by rfl⟩ : syracuseStep 2538317 = 951869) (by norm_num)
theorem B6768845 : Blo 2005435 6768845 := bstep (se 3 (by rfl) ⟨1269158, by rfl⟩ : syracuseStep 6768845 = 2538317) B2538317
theorem B4512563 : Blo 2005435 4512563 := bstep (se 1 (by rfl) ⟨3384422, by rfl⟩ : syracuseStep 4512563 = 6768845) B6768845
theorem B3008375 : Blo 2005435 3008375 := bstep (se 1 (by rfl) ⟨2256281, by rfl⟩ : syracuseStep 3008375 = 4512563) B4512563
theorem B2005583 : Blo 2005435 2005583 := bstep (se 1 (by rfl) ⟨1504187, by rfl⟩ : syracuseStep 2005583 = 3008375) B3008375
theorem B3008381 : Blo 2005435 3008381 := bbase (se 3 (by rfl) ⟨564071, by rfl⟩ : syracuseStep 3008381 = 1128143) (by norm_num)
theorem B2005587 : Blo 2005435 2005587 := bstep (se 1 (by rfl) ⟨1504190, by rfl⟩ : syracuseStep 2005587 = 3008381) B3008381
theorem B4512581 : Blo 2005435 4512581 := bbase (se 4 (by rfl) ⟨423054, by rfl⟩ : syracuseStep 4512581 = 846109) (by norm_num)
theorem B3008387 : Blo 2005435 3008387 := bstep (se 1 (by rfl) ⟨2256290, by rfl⟩ : syracuseStep 3008387 = 4512581) B4512581
theorem B2005591 : Blo 2005435 2005591 := bstep (se 1 (by rfl) ⟨1504193, by rfl⟩ : syracuseStep 2005591 = 3008387) B3008387
theorem B4283437 : Blo 2005435 4283437 := bbase (se 3 (by rfl) ⟨803144, by rfl⟩ : syracuseStep 4283437 = 1606289) (by norm_num)
theorem B5711249 : Blo 2005435 5711249 := bstep (se 2 (by rfl) ⟨2141718, by rfl⟩ : syracuseStep 5711249 = 4283437) B4283437
theorem B3807499 : Blo 2005435 3807499 := bstep (se 1 (by rfl) ⟨2855624, by rfl⟩ : syracuseStep 3807499 = 5711249) B5711249
theorem B5076665 : Blo 2005435 5076665 := bstep (se 2 (by rfl) ⟨1903749, by rfl⟩ : syracuseStep 5076665 = 3807499) B3807499
theorem B3384443 : Blo 2005435 3384443 := bstep (se 1 (by rfl) ⟨2538332, by rfl⟩ : syracuseStep 3384443 = 5076665) B5076665
theorem B2256295 : Blo 2005435 2256295 := bstep (se 1 (by rfl) ⟨1692221, by rfl⟩ : syracuseStep 2256295 = 3384443) B3384443
theorem B3008393 : Blo 2005435 3008393 := bstep (se 2 (by rfl) ⟨1128147, by rfl⟩ : syracuseStep 3008393 = 2256295) B2256295
theorem B2005595 : Blo 2005435 2005595 := bstep (se 1 (by rfl) ⟨1504196, by rfl⟩ : syracuseStep 2005595 = 3008393) B3008393
theorem B10153349 : Blo 2005435 10153349 := bbase (se 4 (by rfl) ⟨951876, by rfl⟩ : syracuseStep 10153349 = 1903753) (by norm_num)
theorem B6768899 : Blo 2005435 6768899 := bstep (se 1 (by rfl) ⟨5076674, by rfl⟩ : syracuseStep 6768899 = 10153349) B10153349
theorem B4512599 : Blo 2005435 4512599 := bstep (se 1 (by rfl) ⟨3384449, by rfl⟩ : syracuseStep 4512599 = 6768899) B6768899
theorem B3008399 : Blo 2005435 3008399 := bstep (se 1 (by rfl) ⟨2256299, by rfl⟩ : syracuseStep 3008399 = 4512599) B4512599
theorem B2005599 : Blo 2005435 2005599 := bstep (se 1 (by rfl) ⟨1504199, by rfl⟩ : syracuseStep 2005599 = 3008399) B3008399
theorem B3008405 : Blo 2005435 3008405 := bbase (se 6 (by rfl) ⟨70509, by rfl⟩ : syracuseStep 3008405 = 141019) (by norm_num)
theorem B2005603 : Blo 2005435 2005603 := bstep (se 1 (by rfl) ⟨1504202, by rfl⟩ : syracuseStep 2005603 = 3008405) B3008405
theorem B3212597 : Blo 2005435 3212597 := bbase (se 5 (by rfl) ⟨150590, by rfl⟩ : syracuseStep 3212597 = 301181) (by norm_num)
theorem B2141731 : Blo 2005435 2141731 := bstep (se 1 (by rfl) ⟨1606298, by rfl⟩ : syracuseStep 2141731 = 3212597) B3212597
theorem B11422565 : Blo 2005435 11422565 := bstep (se 4 (by rfl) ⟨1070865, by rfl⟩ : syracuseStep 11422565 = 2141731) B2141731
theorem B7615043 : Blo 2005435 7615043 := bstep (se 1 (by rfl) ⟨5711282, by rfl⟩ : syracuseStep 7615043 = 11422565) B11422565
theorem B5076695 : Blo 2005435 5076695 := bstep (se 1 (by rfl) ⟨3807521, by rfl⟩ : syracuseStep 5076695 = 7615043) B7615043
theorem B3384463 : Blo 2005435 3384463 := bstep (se 1 (by rfl) ⟨2538347, by rfl⟩ : syracuseStep 3384463 = 5076695) B5076695
theorem B4512617 : Blo 2005435 4512617 := bstep (se 2 (by rfl) ⟨1692231, by rfl⟩ : syracuseStep 4512617 = 3384463) B3384463
theorem B3008411 : Blo 2005435 3008411 := bstep (se 1 (by rfl) ⟨2256308, by rfl⟩ : syracuseStep 3008411 = 4512617) B4512617
theorem B2005607 : Blo 2005435 2005607 := bstep (se 1 (by rfl) ⟨1504205, by rfl⟩ : syracuseStep 2005607 = 3008411) B3008411
theorem B2256313 : Blo 2005435 2256313 := bbase (se 2 (by rfl) ⟨846117, by rfl⟩ : syracuseStep 2256313 = 1692235) (by norm_num)
theorem B3008417 : Blo 2005435 3008417 := bstep (se 2 (by rfl) ⟨1128156, by rfl⟩ : syracuseStep 3008417 = 2256313) B2256313
theorem B2005611 : Blo 2005435 2005611 := bstep (se 1 (by rfl) ⟨1504208, by rfl⟩ : syracuseStep 2005611 = 3008417) B3008417
theorem B9637829 : Blo 2005435 9637829 := bbase (se 4 (by rfl) ⟨903546, by rfl⟩ : syracuseStep 9637829 = 1807093) (by norm_num)
theorem B6425219 : Blo 2005435 6425219 := bstep (se 1 (by rfl) ⟨4818914, by rfl⟩ : syracuseStep 6425219 = 9637829) B9637829
theorem B4283479 : Blo 2005435 4283479 := bstep (se 1 (by rfl) ⟨3212609, by rfl⟩ : syracuseStep 4283479 = 6425219) B6425219
theorem B5711305 : Blo 2005435 5711305 := bstep (se 2 (by rfl) ⟨2141739, by rfl⟩ : syracuseStep 5711305 = 4283479) B4283479
theorem B7615073 : Blo 2005435 7615073 := bstep (se 2 (by rfl) ⟨2855652, by rfl⟩ : syracuseStep 7615073 = 5711305) B5711305
theorem B5076715 : Blo 2005435 5076715 := bstep (se 1 (by rfl) ⟨3807536, by rfl⟩ : syracuseStep 5076715 = 7615073) B7615073
theorem B6768953 : Blo 2005435 6768953 := bstep (se 2 (by rfl) ⟨2538357, by rfl⟩ : syracuseStep 6768953 = 5076715) B5076715
theorem B4512635 : Blo 2005435 4512635 := bstep (se 1 (by rfl) ⟨3384476, by rfl⟩ : syracuseStep 4512635 = 6768953) B6768953
theorem B3008423 : Blo 2005435 3008423 := bstep (se 1 (by rfl) ⟨2256317, by rfl⟩ : syracuseStep 3008423 = 4512635) B4512635
theorem B2005615 : Blo 2005435 2005615 := bstep (se 1 (by rfl) ⟨1504211, by rfl⟩ : syracuseStep 2005615 = 3008423) B3008423
theorem B3008429 : Blo 2005435 3008429 := bbase (se 3 (by rfl) ⟨564080, by rfl⟩ : syracuseStep 3008429 = 1128161) (by norm_num)
theorem B2005619 : Blo 2005435 2005619 := bstep (se 1 (by rfl) ⟨1504214, by rfl⟩ : syracuseStep 2005619 = 3008429) B3008429
theorem B4512653 : Blo 2005435 4512653 := bbase (se 3 (by rfl) ⟨846122, by rfl⟩ : syracuseStep 4512653 = 1692245) (by norm_num)
theorem B3008435 : Blo 2005435 3008435 := bstep (se 1 (by rfl) ⟨2256326, by rfl⟩ : syracuseStep 3008435 = 4512653) B4512653
theorem B2005623 : Blo 2005435 2005623 := bstep (se 1 (by rfl) ⟨1504217, by rfl⟩ : syracuseStep 2005623 = 3008435) B3008435
theorem B2538373 : Blo 2005435 2538373 := bbase (se 4 (by rfl) ⟨237972, by rfl⟩ : syracuseStep 2538373 = 475945) (by norm_num)
theorem B3384497 : Blo 2005435 3384497 := bstep (se 2 (by rfl) ⟨1269186, by rfl⟩ : syracuseStep 3384497 = 2538373) B2538373
theorem B2256331 : Blo 2005435 2256331 := bstep (se 1 (by rfl) ⟨1692248, by rfl⟩ : syracuseStep 2256331 = 3384497) B3384497
theorem B3008441 : Blo 2005435 3008441 := bstep (se 2 (by rfl) ⟨1128165, by rfl⟩ : syracuseStep 3008441 = 2256331) B2256331
theorem B2005627 : Blo 2005435 2005627 := bstep (se 1 (by rfl) ⟨1504220, by rfl⟩ : syracuseStep 2005627 = 3008441) B3008441
theorem B25701077 : Blo 2005435 25701077 := bbase (se 7 (by rfl) ⟨301184, by rfl⟩ : syracuseStep 25701077 = 602369) (by norm_num)
theorem B17134051 : Blo 2005435 17134051 := bstep (se 1 (by rfl) ⟨12850538, by rfl⟩ : syracuseStep 17134051 = 25701077) B25701077
theorem B22845401 : Blo 2005435 22845401 := bstep (se 2 (by rfl) ⟨8567025, by rfl⟩ : syracuseStep 22845401 = 17134051) B17134051
theorem B15230267 : Blo 2005435 15230267 := bstep (se 1 (by rfl) ⟨11422700, by rfl⟩ : syracuseStep 15230267 = 22845401) B22845401
theorem B10153511 : Blo 2005435 10153511 := bstep (se 1 (by rfl) ⟨7615133, by rfl⟩ : syracuseStep 10153511 = 15230267) B15230267
theorem B6769007 : Blo 2005435 6769007 := bstep (se 1 (by rfl) ⟨5076755, by rfl⟩ : syracuseStep 6769007 = 10153511) B10153511
theorem B4512671 : Blo 2005435 4512671 := bstep (se 1 (by rfl) ⟨3384503, by rfl⟩ : syracuseStep 4512671 = 6769007) B6769007
theorem B3008447 : Blo 2005435 3008447 := bstep (se 1 (by rfl) ⟨2256335, by rfl⟩ : syracuseStep 3008447 = 4512671) B4512671
theorem B2005631 : Blo 2005435 2005631 := bstep (se 1 (by rfl) ⟨1504223, by rfl⟩ : syracuseStep 2005631 = 3008447) B3008447
theorem B3008453 : Blo 2005435 3008453 := bbase (se 4 (by rfl) ⟨282042, by rfl⟩ : syracuseStep 3008453 = 564085) (by norm_num)
theorem B2005635 : Blo 2005435 2005635 := bstep (se 1 (by rfl) ⟨1504226, by rfl⟩ : syracuseStep 2005635 = 3008453) B3008453
theorem B3384517 : Blo 2005435 3384517 := bbase (se 4 (by rfl) ⟨317298, by rfl⟩ : syracuseStep 3384517 = 634597) (by norm_num)
theorem B4512689 : Blo 2005435 4512689 := bstep (se 2 (by rfl) ⟨1692258, by rfl⟩ : syracuseStep 4512689 = 3384517) B3384517
theorem B3008459 : Blo 2005435 3008459 := bstep (se 1 (by rfl) ⟨2256344, by rfl⟩ : syracuseStep 3008459 = 4512689) B4512689
theorem B2005639 : Blo 2005435 2005639 := bstep (se 1 (by rfl) ⟨1504229, by rfl⟩ : syracuseStep 2005639 = 3008459) B3008459
theorem B2256349 : Blo 2005435 2256349 := bbase (se 3 (by rfl) ⟨423065, by rfl⟩ : syracuseStep 2256349 = 846131) (by norm_num)
theorem B3008465 : Blo 2005435 3008465 := bstep (se 2 (by rfl) ⟨1128174, by rfl⟩ : syracuseStep 3008465 = 2256349) B2256349
theorem B2005643 : Blo 2005435 2005643 := bstep (se 1 (by rfl) ⟨1504232, by rfl⟩ : syracuseStep 2005643 = 3008465) B3008465
theorem B6769061 : Blo 2005435 6769061 := bbase (se 4 (by rfl) ⟨634599, by rfl⟩ : syracuseStep 6769061 = 1269199) (by norm_num)
theorem B4512707 : Blo 2005435 4512707 := bstep (se 1 (by rfl) ⟨3384530, by rfl⟩ : syracuseStep 4512707 = 6769061) B6769061
theorem B3008471 : Blo 2005435 3008471 := bstep (se 1 (by rfl) ⟨2256353, by rfl⟩ : syracuseStep 3008471 = 4512707) B4512707
theorem B2005647 : Blo 2005435 2005647 := bstep (se 1 (by rfl) ⟨1504235, by rfl⟩ : syracuseStep 2005647 = 3008471) B3008471
theorem B3008477 : Blo 2005435 3008477 := bbase (se 3 (by rfl) ⟨564089, by rfl⟩ : syracuseStep 3008477 = 1128179) (by norm_num)
theorem B2005651 : Blo 2005435 2005651 := bstep (se 1 (by rfl) ⟨1504238, by rfl⟩ : syracuseStep 2005651 = 3008477) B3008477
theorem B4512725 : Blo 2005435 4512725 := bbase (se 7 (by rfl) ⟨52883, by rfl⟩ : syracuseStep 4512725 = 105767) (by norm_num)
theorem B3008483 : Blo 2005435 3008483 := bstep (se 1 (by rfl) ⟨2256362, by rfl⟩ : syracuseStep 3008483 = 4512725) B4512725
theorem B2005655 : Blo 2005435 2005655 := bstep (se 1 (by rfl) ⟨1504241, by rfl⟩ : syracuseStep 2005655 = 3008483) B3008483
theorem B2287153 : Blo 2005435 2287153 := bbase (se 2 (by rfl) ⟨857682, by rfl⟩ : syracuseStep 2287153 = 1715365) (by norm_num)
theorem B3049537 : Blo 2005435 3049537 := bstep (se 2 (by rfl) ⟨1143576, by rfl⟩ : syracuseStep 3049537 = 2287153) B2287153
theorem B4066049 : Blo 2005435 4066049 := bstep (se 2 (by rfl) ⟨1524768, by rfl⟩ : syracuseStep 4066049 = 3049537) B3049537
theorem B10842797 : Blo 2005435 10842797 := bstep (se 3 (by rfl) ⟨2033024, by rfl⟩ : syracuseStep 10842797 = 4066049) B4066049
theorem B7228531 : Blo 2005435 7228531 := bstep (se 1 (by rfl) ⟨5421398, by rfl⟩ : syracuseStep 7228531 = 10842797) B10842797
theorem B9638041 : Blo 2005435 9638041 := bstep (se 2 (by rfl) ⟨3614265, by rfl⟩ : syracuseStep 9638041 = 7228531) B7228531
theorem B12850721 : Blo 2005435 12850721 := bstep (se 2 (by rfl) ⟨4819020, by rfl⟩ : syracuseStep 12850721 = 9638041) B9638041
theorem B8567147 : Blo 2005435 8567147 := bstep (se 1 (by rfl) ⟨6425360, by rfl⟩ : syracuseStep 8567147 = 12850721) B12850721
theorem B5711431 : Blo 2005435 5711431 := bstep (se 1 (by rfl) ⟨4283573, by rfl⟩ : syracuseStep 5711431 = 8567147) B8567147
theorem B7615241 : Blo 2005435 7615241 := bstep (se 2 (by rfl) ⟨2855715, by rfl⟩ : syracuseStep 7615241 = 5711431) B5711431
theorem B5076827 : Blo 2005435 5076827 := bstep (se 1 (by rfl) ⟨3807620, by rfl⟩ : syracuseStep 5076827 = 7615241) B7615241
theorem B3384551 : Blo 2005435 3384551 := bstep (se 1 (by rfl) ⟨2538413, by rfl⟩ : syracuseStep 3384551 = 5076827) B5076827
theorem B2256367 : Blo 2005435 2256367 := bstep (se 1 (by rfl) ⟨1692275, by rfl⟩ : syracuseStep 2256367 = 3384551) B3384551
theorem B3008489 : Blo 2005435 3008489 := bstep (se 2 (by rfl) ⟨1128183, by rfl⟩ : syracuseStep 3008489 = 2256367) B2256367
theorem B2005659 : Blo 2005435 2005659 := bstep (se 1 (by rfl) ⟨1504244, by rfl⟩ : syracuseStep 2005659 = 3008489) B3008489
theorem B17134325 : Blo 2005435 17134325 := bbase (se 5 (by rfl) ⟨803171, by rfl⟩ : syracuseStep 17134325 = 1606343) (by norm_num)
theorem B11422883 : Blo 2005435 11422883 := bstep (se 1 (by rfl) ⟨8567162, by rfl⟩ : syracuseStep 11422883 = 17134325) B17134325
theorem B7615255 : Blo 2005435 7615255 := bstep (se 1 (by rfl) ⟨5711441, by rfl⟩ : syracuseStep 7615255 = 11422883) B11422883
theorem B10153673 : Blo 2005435 10153673 := bstep (se 2 (by rfl) ⟨3807627, by rfl⟩ : syracuseStep 10153673 = 7615255) B7615255
theorem B6769115 : Blo 2005435 6769115 := bstep (se 1 (by rfl) ⟨5076836, by rfl⟩ : syracuseStep 6769115 = 10153673) B10153673
theorem B4512743 : Blo 2005435 4512743 := bstep (se 1 (by rfl) ⟨3384557, by rfl⟩ : syracuseStep 4512743 = 6769115) B6769115
theorem B3008495 : Blo 2005435 3008495 := bstep (se 1 (by rfl) ⟨2256371, by rfl⟩ : syracuseStep 3008495 = 4512743) B4512743
theorem B2005663 : Blo 2005435 2005663 := bstep (se 1 (by rfl) ⟨1504247, by rfl⟩ : syracuseStep 2005663 = 3008495) B3008495
theorem B3008501 : Blo 2005435 3008501 := bbase (se 5 (by rfl) ⟨141023, by rfl⟩ : syracuseStep 3008501 = 282047) (by norm_num)
theorem B2005667 : Blo 2005435 2005667 := bstep (se 1 (by rfl) ⟨1504250, by rfl⟩ : syracuseStep 2005667 = 3008501) B3008501
theorem B4574333 : Blo 2005435 4574333 := bbase (se 3 (by rfl) ⟨857687, by rfl⟩ : syracuseStep 4574333 = 1715375) (by norm_num)
theorem B12198221 : Blo 2005435 12198221 := bstep (se 3 (by rfl) ⟨2287166, by rfl⟩ : syracuseStep 12198221 = 4574333) B4574333
theorem B8132147 : Blo 2005435 8132147 := bstep (se 1 (by rfl) ⟨6099110, by rfl⟩ : syracuseStep 8132147 = 12198221) B12198221
theorem B5421431 : Blo 2005435 5421431 := bstep (se 1 (by rfl) ⟨4066073, by rfl⟩ : syracuseStep 5421431 = 8132147) B8132147
theorem B14457149 : Blo 2005435 14457149 := bstep (se 3 (by rfl) ⟨2710715, by rfl⟩ : syracuseStep 14457149 = 5421431) B5421431
theorem B9638099 : Blo 2005435 9638099 := bstep (se 1 (by rfl) ⟨7228574, by rfl⟩ : syracuseStep 9638099 = 14457149) B14457149
theorem B6425399 : Blo 2005435 6425399 := bstep (se 1 (by rfl) ⟨4819049, by rfl⟩ : syracuseStep 6425399 = 9638099) B9638099
theorem B4283599 : Blo 2005435 4283599 := bstep (se 1 (by rfl) ⟨3212699, by rfl⟩ : syracuseStep 4283599 = 6425399) B6425399
theorem B5711465 : Blo 2005435 5711465 := bstep (se 2 (by rfl) ⟨2141799, by rfl⟩ : syracuseStep 5711465 = 4283599) B4283599
theorem B3807643 : Blo 2005435 3807643 := bstep (se 1 (by rfl) ⟨2855732, by rfl⟩ : syracuseStep 3807643 = 5711465) B5711465
theorem B5076857 : Blo 2005435 5076857 := bstep (se 2 (by rfl) ⟨1903821, by rfl⟩ : syracuseStep 5076857 = 3807643) B3807643
theorem B3384571 : Blo 2005435 3384571 := bstep (se 1 (by rfl) ⟨2538428, by rfl⟩ : syracuseStep 3384571 = 5076857) B5076857
theorem B4512761 : Blo 2005435 4512761 := bstep (se 2 (by rfl) ⟨1692285, by rfl⟩ : syracuseStep 4512761 = 3384571) B3384571
theorem B3008507 : Blo 2005435 3008507 := bstep (se 1 (by rfl) ⟨2256380, by rfl⟩ : syracuseStep 3008507 = 4512761) B4512761
theorem B2005671 : Blo 2005435 2005671 := bstep (se 1 (by rfl) ⟨1504253, by rfl⟩ : syracuseStep 2005671 = 3008507) B3008507
theorem B2256385 : Blo 2005435 2256385 := bbase (se 2 (by rfl) ⟨846144, by rfl⟩ : syracuseStep 2256385 = 1692289) (by norm_num)
theorem B3008513 : Blo 2005435 3008513 := bstep (se 2 (by rfl) ⟨1128192, by rfl⟩ : syracuseStep 3008513 = 2256385) B2256385
theorem B2005675 : Blo 2005435 2005675 := bstep (se 1 (by rfl) ⟨1504256, by rfl⟩ : syracuseStep 2005675 = 3008513) B3008513
theorem B5076877 : Blo 2005435 5076877 := bbase (se 3 (by rfl) ⟨951914, by rfl⟩ : syracuseStep 5076877 = 1903829) (by norm_num)
theorem B6769169 : Blo 2005435 6769169 := bstep (se 2 (by rfl) ⟨2538438, by rfl⟩ : syracuseStep 6769169 = 5076877) B5076877
theorem B4512779 : Blo 2005435 4512779 := bstep (se 1 (by rfl) ⟨3384584, by rfl⟩ : syracuseStep 4512779 = 6769169) B6769169
theorem B3008519 : Blo 2005435 3008519 := bstep (se 1 (by rfl) ⟨2256389, by rfl⟩ : syracuseStep 3008519 = 4512779) B4512779
theorem B2005679 : Blo 2005435 2005679 := bstep (se 1 (by rfl) ⟨1504259, by rfl⟩ : syracuseStep 2005679 = 3008519) B3008519
theorem B3008525 : Blo 2005435 3008525 := bbase (se 3 (by rfl) ⟨564098, by rfl⟩ : syracuseStep 3008525 = 1128197) (by norm_num)
theorem B2005683 : Blo 2005435 2005683 := bstep (se 1 (by rfl) ⟨1504262, by rfl⟩ : syracuseStep 2005683 = 3008525) B3008525
theorem B4512797 : Blo 2005435 4512797 := bbase (se 3 (by rfl) ⟨846149, by rfl⟩ : syracuseStep 4512797 = 1692299) (by norm_num)
theorem B3008531 : Blo 2005435 3008531 := bstep (se 1 (by rfl) ⟨2256398, by rfl⟩ : syracuseStep 3008531 = 4512797) B4512797
theorem B2005687 : Blo 2005435 2005687 := bstep (se 1 (by rfl) ⟨1504265, by rfl⟩ : syracuseStep 2005687 = 3008531) B3008531
theorem B3384605 : Blo 2005435 3384605 := bbase (se 3 (by rfl) ⟨634613, by rfl⟩ : syracuseStep 3384605 = 1269227) (by norm_num)
theorem B2256403 : Blo 2005435 2256403 := bstep (se 1 (by rfl) ⟨1692302, by rfl⟩ : syracuseStep 2256403 = 3384605) B3384605
theorem B3008537 : Blo 2005435 3008537 := bstep (se 2 (by rfl) ⟨1128201, by rfl⟩ : syracuseStep 3008537 = 2256403) B2256403
theorem B2005691 : Blo 2005435 2005691 := bstep (se 1 (by rfl) ⟨1504268, by rfl⟩ : syracuseStep 2005691 = 3008537) B3008537
theorem B2409553 : Blo 2005435 2409553 := bbase (se 2 (by rfl) ⟨903582, by rfl⟩ : syracuseStep 2409553 = 1807165) (by norm_num)
theorem B12850949 : Blo 2005435 12850949 := bstep (se 4 (by rfl) ⟨1204776, by rfl⟩ : syracuseStep 12850949 = 2409553) B2409553
theorem B8567299 : Blo 2005435 8567299 := bstep (se 1 (by rfl) ⟨6425474, by rfl⟩ : syracuseStep 8567299 = 12850949) B12850949
theorem B11423065 : Blo 2005435 11423065 := bstep (se 2 (by rfl) ⟨4283649, by rfl⟩ : syracuseStep 11423065 = 8567299) B8567299
theorem B15230753 : Blo 2005435 15230753 := bstep (se 2 (by rfl) ⟨5711532, by rfl⟩ : syracuseStep 15230753 = 11423065) B11423065
theorem B10153835 : Blo 2005435 10153835 := bstep (se 1 (by rfl) ⟨7615376, by rfl⟩ : syracuseStep 10153835 = 15230753) B15230753
theorem B6769223 : Blo 2005435 6769223 := bstep (se 1 (by rfl) ⟨5076917, by rfl⟩ : syracuseStep 6769223 = 10153835) B10153835
theorem B4512815 : Blo 2005435 4512815 := bstep (se 1 (by rfl) ⟨3384611, by rfl⟩ : syracuseStep 4512815 = 6769223) B6769223
theorem B3008543 : Blo 2005435 3008543 := bstep (se 1 (by rfl) ⟨2256407, by rfl⟩ : syracuseStep 3008543 = 4512815) B4512815
theorem B2005695 : Blo 2005435 2005695 := bstep (se 1 (by rfl) ⟨1504271, by rfl⟩ : syracuseStep 2005695 = 3008543) B3008543
theorem B3008549 : Blo 2005435 3008549 := bbase (se 4 (by rfl) ⟨282051, by rfl⟩ : syracuseStep 3008549 = 564103) (by norm_num)
theorem B2005699 : Blo 2005435 2005699 := bstep (se 1 (by rfl) ⟨1504274, by rfl⟩ : syracuseStep 2005699 = 3008549) B3008549
theorem B2538469 : Blo 2005435 2538469 := bbase (se 4 (by rfl) ⟨237981, by rfl⟩ : syracuseStep 2538469 = 475963) (by norm_num)
theorem B3384625 : Blo 2005435 3384625 := bstep (se 2 (by rfl) ⟨1269234, by rfl⟩ : syracuseStep 3384625 = 2538469) B2538469
theorem B4512833 : Blo 2005435 4512833 := bstep (se 2 (by rfl) ⟨1692312, by rfl⟩ : syracuseStep 4512833 = 3384625) B3384625
theorem B3008555 : Blo 2005435 3008555 := bstep (se 1 (by rfl) ⟨2256416, by rfl⟩ : syracuseStep 3008555 = 4512833) B4512833
theorem B2005703 : Blo 2005435 2005703 := bstep (se 1 (by rfl) ⟨1504277, by rfl⟩ : syracuseStep 2005703 = 3008555) B3008555
theorem B2256421 : Blo 2005435 2256421 := bbase (se 4 (by rfl) ⟨211539, by rfl⟩ : syracuseStep 2256421 = 423079) (by norm_num)
theorem B3008561 : Blo 2005435 3008561 := bstep (se 2 (by rfl) ⟨1128210, by rfl⟩ : syracuseStep 3008561 = 2256421) B2256421
theorem B2005707 : Blo 2005435 2005707 := bstep (se 1 (by rfl) ⟨1504280, by rfl⟩ : syracuseStep 2005707 = 3008561) B3008561
theorem B8132309 : Blo 2005435 8132309 := bbase (se 7 (by rfl) ⟨95300, by rfl⟩ : syracuseStep 8132309 = 190601) (by norm_num)
theorem B5421539 : Blo 2005435 5421539 := bstep (se 1 (by rfl) ⟨4066154, by rfl⟩ : syracuseStep 5421539 = 8132309) B8132309
theorem B14457437 : Blo 2005435 14457437 := bstep (se 3 (by rfl) ⟨2710769, by rfl⟩ : syracuseStep 14457437 = 5421539) B5421539
theorem B9638291 : Blo 2005435 9638291 := bstep (se 1 (by rfl) ⟨7228718, by rfl⟩ : syracuseStep 9638291 = 14457437) B14457437
theorem B6425527 : Blo 2005435 6425527 := bstep (se 1 (by rfl) ⟨4819145, by rfl⟩ : syracuseStep 6425527 = 9638291) B9638291
theorem B8567369 : Blo 2005435 8567369 := bstep (se 2 (by rfl) ⟨3212763, by rfl⟩ : syracuseStep 8567369 = 6425527) B6425527
theorem B5711579 : Blo 2005435 5711579 := bstep (se 1 (by rfl) ⟨4283684, by rfl⟩ : syracuseStep 5711579 = 8567369) B8567369
theorem B3807719 : Blo 2005435 3807719 := bstep (se 1 (by rfl) ⟨2855789, by rfl⟩ : syracuseStep 3807719 = 5711579) B5711579
theorem B2538479 : Blo 2005435 2538479 := bstep (se 1 (by rfl) ⟨1903859, by rfl⟩ : syracuseStep 2538479 = 3807719) B3807719
theorem B6769277 : Blo 2005435 6769277 := bstep (se 3 (by rfl) ⟨1269239, by rfl⟩ : syracuseStep 6769277 = 2538479) B2538479
theorem B4512851 : Blo 2005435 4512851 := bstep (se 1 (by rfl) ⟨3384638, by rfl⟩ : syracuseStep 4512851 = 6769277) B6769277
theorem B3008567 : Blo 2005435 3008567 := bstep (se 1 (by rfl) ⟨2256425, by rfl⟩ : syracuseStep 3008567 = 4512851) B4512851
theorem B2005711 : Blo 2005435 2005711 := bstep (se 1 (by rfl) ⟨1504283, by rfl⟩ : syracuseStep 2005711 = 3008567) B3008567
theorem B3008573 : Blo 2005435 3008573 := bbase (se 3 (by rfl) ⟨564107, by rfl⟩ : syracuseStep 3008573 = 1128215) (by norm_num)
theorem B2005715 : Blo 2005435 2005715 := bstep (se 1 (by rfl) ⟨1504286, by rfl⟩ : syracuseStep 2005715 = 3008573) B3008573
theorem B4512869 : Blo 2005435 4512869 := bbase (se 4 (by rfl) ⟨423081, by rfl⟩ : syracuseStep 4512869 = 846163) (by norm_num)
theorem B3008579 : Blo 2005435 3008579 := bstep (se 1 (by rfl) ⟨2256434, by rfl⟩ : syracuseStep 3008579 = 4512869) B4512869
theorem B2005719 : Blo 2005435 2005719 := bstep (se 1 (by rfl) ⟨1504289, by rfl⟩ : syracuseStep 2005719 = 3008579) B3008579
theorem B5076989 : Blo 2005435 5076989 := bbase (se 3 (by rfl) ⟨951935, by rfl⟩ : syracuseStep 5076989 = 1903871) (by norm_num)
theorem B3384659 : Blo 2005435 3384659 := bstep (se 1 (by rfl) ⟨2538494, by rfl⟩ : syracuseStep 3384659 = 5076989) B5076989
theorem B2256439 : Blo 2005435 2256439 := bstep (se 1 (by rfl) ⟨1692329, by rfl⟩ : syracuseStep 2256439 = 3384659) B3384659
theorem B3008585 : Blo 2005435 3008585 := bstep (se 2 (by rfl) ⟨1128219, by rfl⟩ : syracuseStep 3008585 = 2256439) B2256439
theorem B2005723 : Blo 2005435 2005723 := bstep (se 1 (by rfl) ⟨1504292, by rfl⟩ : syracuseStep 2005723 = 3008585) B3008585
theorem B3807749 : Blo 2005435 3807749 := bbase (se 4 (by rfl) ⟨356976, by rfl⟩ : syracuseStep 3807749 = 713953) (by norm_num)
theorem B10153997 : Blo 2005435 10153997 := bstep (se 3 (by rfl) ⟨1903874, by rfl⟩ : syracuseStep 10153997 = 3807749) B3807749
theorem B6769331 : Blo 2005435 6769331 := bstep (se 1 (by rfl) ⟨5076998, by rfl⟩ : syracuseStep 6769331 = 10153997) B10153997
theorem B4512887 : Blo 2005435 4512887 := bstep (se 1 (by rfl) ⟨3384665, by rfl⟩ : syracuseStep 4512887 = 6769331) B6769331
theorem B3008591 : Blo 2005435 3008591 := bstep (se 1 (by rfl) ⟨2256443, by rfl⟩ : syracuseStep 3008591 = 4512887) B4512887
theorem B2005727 : Blo 2005435 2005727 := bstep (se 1 (by rfl) ⟨1504295, by rfl⟩ : syracuseStep 2005727 = 3008591) B3008591
theorem B3008597 : Blo 2005435 3008597 := bbase (se 8 (by rfl) ⟨17628, by rfl⟩ : syracuseStep 3008597 = 35257) (by norm_num)
theorem B2005731 : Blo 2005435 2005731 := bstep (se 1 (by rfl) ⟨1504298, by rfl⟩ : syracuseStep 2005731 = 3008597) B3008597
theorem B8132405 : Blo 2005435 8132405 := bbase (se 5 (by rfl) ⟨381206, by rfl⟩ : syracuseStep 8132405 = 762413) (by norm_num)
theorem B21686413 : Blo 2005435 21686413 := bstep (se 3 (by rfl) ⟨4066202, by rfl⟩ : syracuseStep 21686413 = 8132405) B8132405
theorem B28915217 : Blo 2005435 28915217 := bstep (se 2 (by rfl) ⟨10843206, by rfl⟩ : syracuseStep 28915217 = 21686413) B21686413
theorem B19276811 : Blo 2005435 19276811 := bstep (se 1 (by rfl) ⟨14457608, by rfl⟩ : syracuseStep 19276811 = 28915217) B28915217
theorem B12851207 : Blo 2005435 12851207 := bstep (se 1 (by rfl) ⟨9638405, by rfl⟩ : syracuseStep 12851207 = 19276811) B19276811
theorem B8567471 : Blo 2005435 8567471 := bstep (se 1 (by rfl) ⟨6425603, by rfl⟩ : syracuseStep 8567471 = 12851207) B12851207
theorem B5711647 : Blo 2005435 5711647 := bstep (se 1 (by rfl) ⟨4283735, by rfl⟩ : syracuseStep 5711647 = 8567471) B8567471
theorem B7615529 : Blo 2005435 7615529 := bstep (se 2 (by rfl) ⟨2855823, by rfl⟩ : syracuseStep 7615529 = 5711647) B5711647
theorem B5077019 : Blo 2005435 5077019 := bstep (se 1 (by rfl) ⟨3807764, by rfl⟩ : syracuseStep 5077019 = 7615529) B7615529
theorem B3384679 : Blo 2005435 3384679 := bstep (se 1 (by rfl) ⟨2538509, by rfl⟩ : syracuseStep 3384679 = 5077019) B5077019
theorem B4512905 : Blo 2005435 4512905 := bstep (se 2 (by rfl) ⟨1692339, by rfl⟩ : syracuseStep 4512905 = 3384679) B3384679
theorem B3008603 : Blo 2005435 3008603 := bstep (se 1 (by rfl) ⟨2256452, by rfl⟩ : syracuseStep 3008603 = 4512905) B4512905
theorem B2005735 : Blo 2005435 2005735 := bstep (se 1 (by rfl) ⟨1504301, by rfl⟩ : syracuseStep 2005735 = 3008603) B3008603
theorem B2256457 : Blo 2005435 2256457 := bbase (se 2 (by rfl) ⟨846171, by rfl⟩ : syracuseStep 2256457 = 1692343) (by norm_num)
theorem B3008609 : Blo 2005435 3008609 := bstep (se 2 (by rfl) ⟨1128228, by rfl⟩ : syracuseStep 3008609 = 2256457) B2256457
theorem B2005739 : Blo 2005435 2005739 := bstep (se 1 (by rfl) ⟨1504304, by rfl⟩ : syracuseStep 2005739 = 3008609) B3008609
theorem B8132437 : Blo 2005435 8132437 := bbase (se 9 (by rfl) ⟨23825, by rfl⟩ : syracuseStep 8132437 = 47651) (by norm_num)
theorem B10843249 : Blo 2005435 10843249 := bstep (se 2 (by rfl) ⟨4066218, by rfl⟩ : syracuseStep 10843249 = 8132437) B8132437
theorem B14457665 : Blo 2005435 14457665 := bstep (se 2 (by rfl) ⟨5421624, by rfl⟩ : syracuseStep 14457665 = 10843249) B10843249
theorem B9638443 : Blo 2005435 9638443 := bstep (se 1 (by rfl) ⟨7228832, by rfl⟩ : syracuseStep 9638443 = 14457665) B14457665
theorem B12851257 : Blo 2005435 12851257 := bstep (se 2 (by rfl) ⟨4819221, by rfl⟩ : syracuseStep 12851257 = 9638443) B9638443
theorem B17135009 : Blo 2005435 17135009 := bstep (se 2 (by rfl) ⟨6425628, by rfl⟩ : syracuseStep 17135009 = 12851257) B12851257
theorem B11423339 : Blo 2005435 11423339 := bstep (se 1 (by rfl) ⟨8567504, by rfl⟩ : syracuseStep 11423339 = 17135009) B17135009
theorem B7615559 : Blo 2005435 7615559 := bstep (se 1 (by rfl) ⟨5711669, by rfl⟩ : syracuseStep 7615559 = 11423339) B11423339
theorem B5077039 : Blo 2005435 5077039 := bstep (se 1 (by rfl) ⟨3807779, by rfl⟩ : syracuseStep 5077039 = 7615559) B7615559
theorem B6769385 : Blo 2005435 6769385 := bstep (se 2 (by rfl) ⟨2538519, by rfl⟩ : syracuseStep 6769385 = 5077039) B5077039
theorem B4512923 : Blo 2005435 4512923 := bstep (se 1 (by rfl) ⟨3384692, by rfl⟩ : syracuseStep 4512923 = 6769385) B6769385
theorem B3008615 : Blo 2005435 3008615 := bstep (se 1 (by rfl) ⟨2256461, by rfl⟩ : syracuseStep 3008615 = 4512923) B4512923
theorem B2005743 : Blo 2005435 2005743 := bstep (se 1 (by rfl) ⟨1504307, by rfl⟩ : syracuseStep 2005743 = 3008615) B3008615
theorem B3008621 : Blo 2005435 3008621 := bbase (se 3 (by rfl) ⟨564116, by rfl⟩ : syracuseStep 3008621 = 1128233) (by norm_num)
theorem B2005747 : Blo 2005435 2005747 := bstep (se 1 (by rfl) ⟨1504310, by rfl⟩ : syracuseStep 2005747 = 3008621) B3008621
theorem B4512941 : Blo 2005435 4512941 := bbase (se 3 (by rfl) ⟨846176, by rfl⟩ : syracuseStep 4512941 = 1692353) (by norm_num)
theorem B3008627 : Blo 2005435 3008627 := bstep (se 1 (by rfl) ⟨2256470, by rfl⟩ : syracuseStep 3008627 = 4512941) B4512941
theorem B2005751 : Blo 2005435 2005751 := bstep (se 1 (by rfl) ⟨1504313, by rfl⟩ : syracuseStep 2005751 = 3008627) B3008627
theorem B6425669 : Blo 2005435 6425669 := bbase (se 4 (by rfl) ⟨602406, by rfl⟩ : syracuseStep 6425669 = 1204813) (by norm_num)
theorem B4283779 : Blo 2005435 4283779 := bstep (se 1 (by rfl) ⟨3212834, by rfl⟩ : syracuseStep 4283779 = 6425669) B6425669
theorem B5711705 : Blo 2005435 5711705 := bstep (se 2 (by rfl) ⟨2141889, by rfl⟩ : syracuseStep 5711705 = 4283779) B4283779
theorem B3807803 : Blo 2005435 3807803 := bstep (se 1 (by rfl) ⟨2855852, by rfl⟩ : syracuseStep 3807803 = 5711705) B5711705
theorem B2538535 : Blo 2005435 2538535 := bstep (se 1 (by rfl) ⟨1903901, by rfl⟩ : syracuseStep 2538535 = 3807803) B3807803
theorem B3384713 : Blo 2005435 3384713 := bstep (se 2 (by rfl) ⟨1269267, by rfl⟩ : syracuseStep 3384713 = 2538535) B2538535
theorem B2256475 : Blo 2005435 2256475 := bstep (se 1 (by rfl) ⟨1692356, by rfl⟩ : syracuseStep 2256475 = 3384713) B3384713
theorem B3008633 : Blo 2005435 3008633 := bstep (se 2 (by rfl) ⟨1128237, by rfl⟩ : syracuseStep 3008633 = 2256475) B2256475
theorem B2005755 : Blo 2005435 2005755 := bstep (se 1 (by rfl) ⟨1504316, by rfl⟩ : syracuseStep 2005755 = 3008633) B3008633
theorem B8132501 : Blo 2005435 8132501 := bbase (se 6 (by rfl) ⟨190605, by rfl⟩ : syracuseStep 8132501 = 381211) (by norm_num)
theorem B21686669 : Blo 2005435 21686669 := bstep (se 3 (by rfl) ⟨4066250, by rfl⟩ : syracuseStep 21686669 = 8132501) B8132501
theorem B14457779 : Blo 2005435 14457779 := bstep (se 1 (by rfl) ⟨10843334, by rfl⟩ : syracuseStep 14457779 = 21686669) B21686669
theorem B9638519 : Blo 2005435 9638519 := bstep (se 1 (by rfl) ⟨7228889, by rfl⟩ : syracuseStep 9638519 = 14457779) B14457779
theorem B25702717 : Blo 2005435 25702717 := bstep (se 3 (by rfl) ⟨4819259, by rfl⟩ : syracuseStep 25702717 = 9638519) B9638519
theorem B34270289 : Blo 2005435 34270289 := bstep (se 2 (by rfl) ⟨12851358, by rfl⟩ : syracuseStep 34270289 = 25702717) B25702717
theorem B22846859 : Blo 2005435 22846859 := bstep (se 1 (by rfl) ⟨17135144, by rfl⟩ : syracuseStep 22846859 = 34270289) B34270289
theorem B15231239 : Blo 2005435 15231239 := bstep (se 1 (by rfl) ⟨11423429, by rfl⟩ : syracuseStep 15231239 = 22846859) B22846859
theorem B10154159 : Blo 2005435 10154159 := bstep (se 1 (by rfl) ⟨7615619, by rfl⟩ : syracuseStep 10154159 = 15231239) B15231239
theorem B6769439 : Blo 2005435 6769439 := bstep (se 1 (by rfl) ⟨5077079, by rfl⟩ : syracuseStep 6769439 = 10154159) B10154159
theorem B4512959 : Blo 2005435 4512959 := bstep (se 1 (by rfl) ⟨3384719, by rfl⟩ : syracuseStep 4512959 = 6769439) B6769439
theorem B3008639 : Blo 2005435 3008639 := bstep (se 1 (by rfl) ⟨2256479, by rfl⟩ : syracuseStep 3008639 = 4512959) B4512959
theorem B2005759 : Blo 2005435 2005759 := bstep (se 1 (by rfl) ⟨1504319, by rfl⟩ : syracuseStep 2005759 = 3008639) B3008639
theorem B3008645 : Blo 2005435 3008645 := bbase (se 4 (by rfl) ⟨282060, by rfl⟩ : syracuseStep 3008645 = 564121) (by norm_num)
theorem B2005763 : Blo 2005435 2005763 := bstep (se 1 (by rfl) ⟨1504322, by rfl⟩ : syracuseStep 2005763 = 3008645) B3008645
theorem B3384733 : Blo 2005435 3384733 := bbase (se 3 (by rfl) ⟨634637, by rfl⟩ : syracuseStep 3384733 = 1269275) (by norm_num)
theorem B4512977 : Blo 2005435 4512977 := bstep (se 2 (by rfl) ⟨1692366, by rfl⟩ : syracuseStep 4512977 = 3384733) B3384733
theorem B3008651 : Blo 2005435 3008651 := bstep (se 1 (by rfl) ⟨2256488, by rfl⟩ : syracuseStep 3008651 = 4512977) B4512977
theorem B2005767 : Blo 2005435 2005767 := bstep (se 1 (by rfl) ⟨1504325, by rfl⟩ : syracuseStep 2005767 = 3008651) B3008651
theorem B2256493 : Blo 2005435 2256493 := bbase (se 3 (by rfl) ⟨423092, by rfl⟩ : syracuseStep 2256493 = 846185) (by norm_num)
theorem B3008657 : Blo 2005435 3008657 := bstep (se 2 (by rfl) ⟨1128246, by rfl⟩ : syracuseStep 3008657 = 2256493) B2256493
theorem B2005771 : Blo 2005435 2005771 := bstep (se 1 (by rfl) ⟨1504328, by rfl⟩ : syracuseStep 2005771 = 3008657) B3008657
theorem B6769493 : Blo 2005435 6769493 := bbase (se 9 (by rfl) ⟨19832, by rfl⟩ : syracuseStep 6769493 = 39665) (by norm_num)
theorem B4512995 : Blo 2005435 4512995 := bstep (se 1 (by rfl) ⟨3384746, by rfl⟩ : syracuseStep 4512995 = 6769493) B6769493
theorem B3008663 : Blo 2005435 3008663 := bstep (se 1 (by rfl) ⟨2256497, by rfl⟩ : syracuseStep 3008663 = 4512995) B4512995
theorem B2005775 : Blo 2005435 2005775 := bstep (se 1 (by rfl) ⟨1504331, by rfl⟩ : syracuseStep 2005775 = 3008663) B3008663
theorem B3008669 : Blo 2005435 3008669 := bbase (se 3 (by rfl) ⟨564125, by rfl⟩ : syracuseStep 3008669 = 1128251) (by norm_num)
theorem B2005779 : Blo 2005435 2005779 := bstep (se 1 (by rfl) ⟨1504334, by rfl⟩ : syracuseStep 2005779 = 3008669) B3008669
theorem B4513013 : Blo 2005435 4513013 := bbase (se 5 (by rfl) ⟨211547, by rfl⟩ : syracuseStep 4513013 = 423095) (by norm_num)
theorem B3008675 : Blo 2005435 3008675 := bstep (se 1 (by rfl) ⟨2256506, by rfl⟩ : syracuseStep 3008675 = 4513013) B4513013
theorem B2005783 : Blo 2005435 2005783 := bstep (se 1 (by rfl) ⟨1504337, by rfl⟩ : syracuseStep 2005783 = 3008675) B3008675
theorem B4178021 : Blo 2005435 4178021 := bbase (se 4 (by rfl) ⟨391689, by rfl⟩ : syracuseStep 4178021 = 783379) (by norm_num)
theorem B11141389 : Blo 2005435 11141389 := bstep (se 3 (by rfl) ⟨2089010, by rfl⟩ : syracuseStep 11141389 = 4178021) B4178021
theorem B14855185 : Blo 2005435 14855185 := bstep (se 2 (by rfl) ⟨5570694, by rfl⟩ : syracuseStep 14855185 = 11141389) B11141389
theorem B19806913 : Blo 2005435 19806913 := bstep (se 2 (by rfl) ⟨7427592, by rfl⟩ : syracuseStep 19806913 = 14855185) B14855185
theorem B105636869 : Blo 2005435 105636869 := bstep (se 4 (by rfl) ⟨9903456, by rfl⟩ : syracuseStep 105636869 = 19806913) B19806913
theorem B70424579 : Blo 2005435 70424579 := bstep (se 1 (by rfl) ⟨52818434, by rfl⟩ : syracuseStep 70424579 = 105636869) B105636869
theorem B46949719 : Blo 2005435 46949719 := bstep (se 1 (by rfl) ⟨35212289, by rfl⟩ : syracuseStep 46949719 = 70424579) B70424579
theorem B62599625 : Blo 2005435 62599625 := bstep (se 2 (by rfl) ⟨23474859, by rfl⟩ : syracuseStep 62599625 = 46949719) B46949719
theorem B41733083 : Blo 2005435 41733083 := bstep (se 1 (by rfl) ⟨31299812, by rfl⟩ : syracuseStep 41733083 = 62599625) B62599625
theorem B27822055 : Blo 2005435 27822055 := bstep (se 1 (by rfl) ⟨20866541, by rfl⟩ : syracuseStep 27822055 = 41733083) B41733083
theorem B37096073 : Blo 2005435 37096073 := bstep (se 2 (by rfl) ⟨13911027, by rfl⟩ : syracuseStep 37096073 = 27822055) B27822055
theorem B24730715 : Blo 2005435 24730715 := bstep (se 1 (by rfl) ⟨18548036, by rfl⟩ : syracuseStep 24730715 = 37096073) B37096073
theorem B65948573 : Blo 2005435 65948573 := bstep (se 3 (by rfl) ⟨12365357, by rfl⟩ : syracuseStep 65948573 = 24730715) B24730715
theorem B43965715 : Blo 2005435 43965715 := bstep (se 1 (by rfl) ⟨32974286, by rfl⟩ : syracuseStep 43965715 = 65948573) B65948573
theorem B58620953 : Blo 2005435 58620953 := bstep (se 2 (by rfl) ⟨21982857, by rfl⟩ : syracuseStep 58620953 = 43965715) B43965715
theorem B156322541 : Blo 2005435 156322541 := bstep (se 3 (by rfl) ⟨29310476, by rfl⟩ : syracuseStep 156322541 = 58620953) B58620953
theorem B104215027 : Blo 2005435 104215027 := bstep (se 1 (by rfl) ⟨78161270, by rfl⟩ : syracuseStep 104215027 = 156322541) B156322541
theorem B138953369 : Blo 2005435 138953369 := bstep (se 2 (by rfl) ⟨52107513, by rfl⟩ : syracuseStep 138953369 = 104215027) B104215027
theorem B92635579 : Blo 2005435 92635579 := bstep (se 1 (by rfl) ⟨69476684, by rfl⟩ : syracuseStep 92635579 = 138953369) B138953369
theorem B494056421 : Blo 2005435 494056421 := bstep (se 4 (by rfl) ⟨46317789, by rfl⟩ : syracuseStep 494056421 = 92635579) B92635579
theorem B329370947 : Blo 2005435 329370947 := bstep (se 1 (by rfl) ⟨247028210, by rfl⟩ : syracuseStep 329370947 = 494056421) B494056421
theorem B219580631 : Blo 2005435 219580631 := bstep (se 1 (by rfl) ⟨164685473, by rfl⟩ : syracuseStep 219580631 = 329370947) B329370947
theorem B146387087 : Blo 2005435 146387087 := bstep (se 1 (by rfl) ⟨109790315, by rfl⟩ : syracuseStep 146387087 = 219580631) B219580631
theorem B97591391 : Blo 2005435 97591391 := bstep (se 1 (by rfl) ⟨73193543, by rfl⟩ : syracuseStep 97591391 = 146387087) B146387087
theorem B65060927 : Blo 2005435 65060927 := bstep (se 1 (by rfl) ⟨48795695, by rfl⟩ : syracuseStep 65060927 = 97591391) B97591391
theorem B43373951 : Blo 2005435 43373951 := bstep (se 1 (by rfl) ⟨32530463, by rfl⟩ : syracuseStep 43373951 = 65060927) B65060927
theorem B28915967 : Blo 2005435 28915967 := bstep (se 1 (by rfl) ⟨21686975, by rfl⟩ : syracuseStep 28915967 = 43373951) B43373951
theorem B19277311 : Blo 2005435 19277311 := bstep (se 1 (by rfl) ⟨14457983, by rfl⟩ : syracuseStep 19277311 = 28915967) B28915967
theorem B25703081 : Blo 2005435 25703081 := bstep (se 2 (by rfl) ⟨9638655, by rfl⟩ : syracuseStep 25703081 = 19277311) B19277311
theorem B17135387 : Blo 2005435 17135387 := bstep (se 1 (by rfl) ⟨12851540, by rfl⟩ : syracuseStep 17135387 = 25703081) B25703081
theorem B11423591 : Blo 2005435 11423591 := bstep (se 1 (by rfl) ⟨8567693, by rfl⟩ : syracuseStep 11423591 = 17135387) B17135387
theorem B7615727 : Blo 2005435 7615727 := bstep (se 1 (by rfl) ⟨5711795, by rfl⟩ : syracuseStep 7615727 = 11423591) B11423591
theorem B5077151 : Blo 2005435 5077151 := bstep (se 1 (by rfl) ⟨3807863, by rfl⟩ : syracuseStep 5077151 = 7615727) B7615727
theorem B3384767 : Blo 2005435 3384767 := bstep (se 1 (by rfl) ⟨2538575, by rfl⟩ : syracuseStep 3384767 = 5077151) B5077151
theorem B2256511 : Blo 2005435 2256511 := bstep (se 1 (by rfl) ⟨1692383, by rfl⟩ : syracuseStep 2256511 = 3384767) B3384767
theorem B3008681 : Blo 2005435 3008681 := bstep (se 2 (by rfl) ⟨1128255, by rfl⟩ : syracuseStep 3008681 = 2256511) B2256511
theorem B2005787 : Blo 2005435 2005787 := bstep (se 1 (by rfl) ⟨1504340, by rfl⟩ : syracuseStep 2005787 = 3008681) B3008681
theorem B2894869 : Blo 2005435 2894869 := bbase (se 6 (by rfl) ⟨67848, by rfl⟩ : syracuseStep 2894869 = 135697) (by norm_num)
theorem B3859825 : Blo 2005435 3859825 := bstep (se 2 (by rfl) ⟨1447434, by rfl⟩ : syracuseStep 3859825 = 2894869) B2894869
theorem B5146433 : Blo 2005435 5146433 := bstep (se 2 (by rfl) ⟨1929912, by rfl⟩ : syracuseStep 5146433 = 3859825) B3859825
theorem B3430955 : Blo 2005435 3430955 := bstep (se 1 (by rfl) ⟨2573216, by rfl⟩ : syracuseStep 3430955 = 5146433) B5146433
theorem B9149213 : Blo 2005435 9149213 := bstep (se 3 (by rfl) ⟨1715477, by rfl⟩ : syracuseStep 9149213 = 3430955) B3430955
theorem B6099475 : Blo 2005435 6099475 := bstep (se 1 (by rfl) ⟨4574606, by rfl⟩ : syracuseStep 6099475 = 9149213) B9149213
theorem B8132633 : Blo 2005435 8132633 := bstep (se 2 (by rfl) ⟨3049737, by rfl⟩ : syracuseStep 8132633 = 6099475) B6099475
theorem B5421755 : Blo 2005435 5421755 := bstep (se 1 (by rfl) ⟨4066316, by rfl⟩ : syracuseStep 5421755 = 8132633) B8132633
theorem B14458013 : Blo 2005435 14458013 := bstep (se 3 (by rfl) ⟨2710877, by rfl⟩ : syracuseStep 14458013 = 5421755) B5421755
theorem B9638675 : Blo 2005435 9638675 := bstep (se 1 (by rfl) ⟨7229006, by rfl⟩ : syracuseStep 9638675 = 14458013) B14458013
theorem B6425783 : Blo 2005435 6425783 := bstep (se 1 (by rfl) ⟨4819337, by rfl⟩ : syracuseStep 6425783 = 9638675) B9638675
theorem B4283855 : Blo 2005435 4283855 := bstep (se 1 (by rfl) ⟨3212891, by rfl⟩ : syracuseStep 4283855 = 6425783) B6425783
theorem B2855903 : Blo 2005435 2855903 := bstep (se 1 (by rfl) ⟨2141927, by rfl⟩ : syracuseStep 2855903 = 4283855) B4283855
theorem B7615741 : Blo 2005435 7615741 := bstep (se 3 (by rfl) ⟨1427951, by rfl⟩ : syracuseStep 7615741 = 2855903) B2855903
theorem B10154321 : Blo 2005435 10154321 := bstep (se 2 (by rfl) ⟨3807870, by rfl⟩ : syracuseStep 10154321 = 7615741) B7615741
theorem B6769547 : Blo 2005435 6769547 := bstep (se 1 (by rfl) ⟨5077160, by rfl⟩ : syracuseStep 6769547 = 10154321) B10154321
theorem B4513031 : Blo 2005435 4513031 := bstep (se 1 (by rfl) ⟨3384773, by rfl⟩ : syracuseStep 4513031 = 6769547) B6769547
theorem B3008687 : Blo 2005435 3008687 := bstep (se 1 (by rfl) ⟨2256515, by rfl⟩ : syracuseStep 3008687 = 4513031) B4513031
theorem B2005791 : Blo 2005435 2005791 := bstep (se 1 (by rfl) ⟨1504343, by rfl⟩ : syracuseStep 2005791 = 3008687) B3008687
theorem B3008693 : Blo 2005435 3008693 := bbase (se 5 (by rfl) ⟨141032, by rfl⟩ : syracuseStep 3008693 = 282065) (by norm_num)
theorem B2005795 : Blo 2005435 2005795 := bstep (se 1 (by rfl) ⟨1504346, by rfl⟩ : syracuseStep 2005795 = 3008693) B3008693
theorem B5077181 : Blo 2005435 5077181 := bbase (se 3 (by rfl) ⟨951971, by rfl⟩ : syracuseStep 5077181 = 1903943) (by norm_num)
theorem B3384787 : Blo 2005435 3384787 := bstep (se 1 (by rfl) ⟨2538590, by rfl⟩ : syracuseStep 3384787 = 5077181) B5077181
theorem B4513049 : Blo 2005435 4513049 := bstep (se 2 (by rfl) ⟨1692393, by rfl⟩ : syracuseStep 4513049 = 3384787) B3384787
theorem B3008699 : Blo 2005435 3008699 := bstep (se 1 (by rfl) ⟨2256524, by rfl⟩ : syracuseStep 3008699 = 4513049) B4513049
theorem B2005799 : Blo 2005435 2005799 := bstep (se 1 (by rfl) ⟨1504349, by rfl⟩ : syracuseStep 2005799 = 3008699) B3008699
theorem B2256529 : Blo 2005435 2256529 := bbase (se 2 (by rfl) ⟨846198, by rfl⟩ : syracuseStep 2256529 = 1692397) (by norm_num)
theorem B3008705 : Blo 2005435 3008705 := bstep (se 2 (by rfl) ⟨1128264, by rfl⟩ : syracuseStep 3008705 = 2256529) B2256529
theorem B2005803 : Blo 2005435 2005803 := bstep (se 1 (by rfl) ⟨1504352, by rfl⟩ : syracuseStep 2005803 = 3008705) B3008705
theorem B3807901 : Blo 2005435 3807901 := bbase (se 3 (by rfl) ⟨713981, by rfl⟩ : syracuseStep 3807901 = 1427963) (by norm_num)
theorem B5077201 : Blo 2005435 5077201 := bstep (se 2 (by rfl) ⟨1903950, by rfl⟩ : syracuseStep 5077201 = 3807901) B3807901
theorem B6769601 : Blo 2005435 6769601 := bstep (se 2 (by rfl) ⟨2538600, by rfl⟩ : syracuseStep 6769601 = 5077201) B5077201
theorem B4513067 : Blo 2005435 4513067 := bstep (se 1 (by rfl) ⟨3384800, by rfl⟩ : syracuseStep 4513067 = 6769601) B6769601
theorem B3008711 : Blo 2005435 3008711 := bstep (se 1 (by rfl) ⟨2256533, by rfl⟩ : syracuseStep 3008711 = 4513067) B4513067
theorem B2005807 : Blo 2005435 2005807 := bstep (se 1 (by rfl) ⟨1504355, by rfl⟩ : syracuseStep 2005807 = 3008711) B3008711
theorem B3008717 : Blo 2005435 3008717 := bbase (se 3 (by rfl) ⟨564134, by rfl⟩ : syracuseStep 3008717 = 1128269) (by norm_num)
theorem B2005811 : Blo 2005435 2005811 := bstep (se 1 (by rfl) ⟨1504358, by rfl⟩ : syracuseStep 2005811 = 3008717) B3008717
theorem B4513085 : Blo 2005435 4513085 := bbase (se 3 (by rfl) ⟨846203, by rfl⟩ : syracuseStep 4513085 = 1692407) (by norm_num)
theorem B3008723 : Blo 2005435 3008723 := bstep (se 1 (by rfl) ⟨2256542, by rfl⟩ : syracuseStep 3008723 = 4513085) B4513085
theorem B2005815 : Blo 2005435 2005815 := bstep (se 1 (by rfl) ⟨1504361, by rfl⟩ : syracuseStep 2005815 = 3008723) B3008723
theorem B3384821 : Blo 2005435 3384821 := bbase (se 5 (by rfl) ⟨158663, by rfl⟩ : syracuseStep 3384821 = 317327) (by norm_num)
theorem B2256547 : Blo 2005435 2256547 := bstep (se 1 (by rfl) ⟨1692410, by rfl⟩ : syracuseStep 2256547 = 3384821) B3384821
theorem B3008729 : Blo 2005435 3008729 := bstep (se 2 (by rfl) ⟨1128273, by rfl⟩ : syracuseStep 3008729 = 2256547) B2256547
theorem B2005819 : Blo 2005435 2005819 := bstep (se 1 (by rfl) ⟨1504364, by rfl⟩ : syracuseStep 2005819 = 3008729) B3008729
theorem B5146517 : Blo 2005435 5146517 := bbase (se 6 (by rfl) ⟨120621, by rfl⟩ : syracuseStep 5146517 = 241243) (by norm_num)
theorem B3431011 : Blo 2005435 3431011 := bstep (se 1 (by rfl) ⟨2573258, by rfl⟩ : syracuseStep 3431011 = 5146517) B5146517
theorem B4574681 : Blo 2005435 4574681 := bstep (se 2 (by rfl) ⟨1715505, by rfl⟩ : syracuseStep 4574681 = 3431011) B3431011
theorem B3049787 : Blo 2005435 3049787 := bstep (se 1 (by rfl) ⟨2287340, by rfl⟩ : syracuseStep 3049787 = 4574681) B4574681
theorem B2033191 : Blo 2005435 2033191 := bstep (se 1 (by rfl) ⟨1524893, by rfl⟩ : syracuseStep 2033191 = 3049787) B3049787
theorem B2710921 : Blo 2005435 2710921 := bstep (se 2 (by rfl) ⟨1016595, by rfl⟩ : syracuseStep 2710921 = 2033191) B2033191
theorem B3614561 : Blo 2005435 3614561 := bstep (se 2 (by rfl) ⟨1355460, by rfl⟩ : syracuseStep 3614561 = 2710921) B2710921
theorem B2409707 : Blo 2005435 2409707 := bstep (se 1 (by rfl) ⟨1807280, by rfl⟩ : syracuseStep 2409707 = 3614561) B3614561
theorem B6425885 : Blo 2005435 6425885 := bstep (se 3 (by rfl) ⟨1204853, by rfl⟩ : syracuseStep 6425885 = 2409707) B2409707
theorem B4283923 : Blo 2005435 4283923 := bstep (se 1 (by rfl) ⟨3212942, by rfl⟩ : syracuseStep 4283923 = 6425885) B6425885
theorem B5711897 : Blo 2005435 5711897 := bstep (se 2 (by rfl) ⟨2141961, by rfl⟩ : syracuseStep 5711897 = 4283923) B4283923
theorem B15231725 : Blo 2005435 15231725 := bstep (se 3 (by rfl) ⟨2855948, by rfl⟩ : syracuseStep 15231725 = 5711897) B5711897
theorem B10154483 : Blo 2005435 10154483 := bstep (se 1 (by rfl) ⟨7615862, by rfl⟩ : syracuseStep 10154483 = 15231725) B15231725
theorem B6769655 : Blo 2005435 6769655 := bstep (se 1 (by rfl) ⟨5077241, by rfl⟩ : syracuseStep 6769655 = 10154483) B10154483
theorem B4513103 : Blo 2005435 4513103 := bstep (se 1 (by rfl) ⟨3384827, by rfl⟩ : syracuseStep 4513103 = 6769655) B6769655
theorem B3008735 : Blo 2005435 3008735 := bstep (se 1 (by rfl) ⟨2256551, by rfl⟩ : syracuseStep 3008735 = 4513103) B4513103
theorem B2005823 : Blo 2005435 2005823 := bstep (se 1 (by rfl) ⟨1504367, by rfl⟩ : syracuseStep 2005823 = 3008735) B3008735
theorem B3008741 : Blo 2005435 3008741 := bbase (se 4 (by rfl) ⟨282069, by rfl⟩ : syracuseStep 3008741 = 564139) (by norm_num)
theorem B2005827 : Blo 2005435 2005827 := bstep (se 1 (by rfl) ⟨1504370, by rfl⟩ : syracuseStep 2005827 = 3008741) B3008741
theorem B4283941 : Blo 2005435 4283941 := bbase (se 4 (by rfl) ⟨401619, by rfl⟩ : syracuseStep 4283941 = 803239) (by norm_num)
theorem B5711921 : Blo 2005435 5711921 := bstep (se 2 (by rfl) ⟨2141970, by rfl⟩ : syracuseStep 5711921 = 4283941) B4283941
theorem B3807947 : Blo 2005435 3807947 := bstep (se 1 (by rfl) ⟨2855960, by rfl⟩ : syracuseStep 3807947 = 5711921) B5711921
theorem B2538631 : Blo 2005435 2538631 := bstep (se 1 (by rfl) ⟨1903973, by rfl⟩ : syracuseStep 2538631 = 3807947) B3807947
theorem B3384841 : Blo 2005435 3384841 := bstep (se 2 (by rfl) ⟨1269315, by rfl⟩ : syracuseStep 3384841 = 2538631) B2538631
theorem B4513121 : Blo 2005435 4513121 := bstep (se 2 (by rfl) ⟨1692420, by rfl⟩ : syracuseStep 4513121 = 3384841) B3384841
theorem B3008747 : Blo 2005435 3008747 := bstep (se 1 (by rfl) ⟨2256560, by rfl⟩ : syracuseStep 3008747 = 4513121) B4513121
theorem B2005831 : Blo 2005435 2005831 := bstep (se 1 (by rfl) ⟨1504373, by rfl⟩ : syracuseStep 2005831 = 3008747) B3008747
theorem B2256565 : Blo 2005435 2256565 := bbase (se 5 (by rfl) ⟨105776, by rfl⟩ : syracuseStep 2256565 = 211553) (by norm_num)
theorem B3008753 : Blo 2005435 3008753 := bstep (se 2 (by rfl) ⟨1128282, by rfl⟩ : syracuseStep 3008753 = 2256565) B2256565
theorem B2005835 : Blo 2005435 2005835 := bstep (se 1 (by rfl) ⟨1504376, by rfl⟩ : syracuseStep 2005835 = 3008753) B3008753
theorem B2538641 : Blo 2005435 2538641 := bbase (se 2 (by rfl) ⟨951990, by rfl⟩ : syracuseStep 2538641 = 1903981) (by norm_num)
theorem B6769709 : Blo 2005435 6769709 := bstep (se 3 (by rfl) ⟨1269320, by rfl⟩ : syracuseStep 6769709 = 2538641) B2538641
theorem B4513139 : Blo 2005435 4513139 := bstep (se 1 (by rfl) ⟨3384854, by rfl⟩ : syracuseStep 4513139 = 6769709) B6769709
theorem B3008759 : Blo 2005435 3008759 := bstep (se 1 (by rfl) ⟨2256569, by rfl⟩ : syracuseStep 3008759 = 4513139) B4513139
theorem B2005839 : Blo 2005435 2005839 := bstep (se 1 (by rfl) ⟨1504379, by rfl⟩ : syracuseStep 2005839 = 3008759) B3008759
theorem B3008765 : Blo 2005435 3008765 := bbase (se 3 (by rfl) ⟨564143, by rfl⟩ : syracuseStep 3008765 = 1128287) (by norm_num)
theorem B2005843 : Blo 2005435 2005843 := bstep (se 1 (by rfl) ⟨1504382, by rfl⟩ : syracuseStep 2005843 = 3008765) B3008765
theorem B4513157 : Blo 2005435 4513157 := bbase (se 4 (by rfl) ⟨423108, by rfl⟩ : syracuseStep 4513157 = 846217) (by norm_num)
theorem B3008771 : Blo 2005435 3008771 := bstep (se 1 (by rfl) ⟨2256578, by rfl⟩ : syracuseStep 3008771 = 4513157) B4513157
theorem B2005847 : Blo 2005435 2005847 := bstep (se 1 (by rfl) ⟨1504385, by rfl⟩ : syracuseStep 2005847 = 3008771) B3008771
theorem B2855989 : Blo 2005435 2855989 := bbase (se 5 (by rfl) ⟨133874, by rfl⟩ : syracuseStep 2855989 = 267749) (by norm_num)
theorem B3807985 : Blo 2005435 3807985 := bstep (se 2 (by rfl) ⟨1427994, by rfl⟩ : syracuseStep 3807985 = 2855989) B2855989
theorem B5077313 : Blo 2005435 5077313 := bstep (se 2 (by rfl) ⟨1903992, by rfl⟩ : syracuseStep 5077313 = 3807985) B3807985
theorem B3384875 : Blo 2005435 3384875 := bstep (se 1 (by rfl) ⟨2538656, by rfl⟩ : syracuseStep 3384875 = 5077313) B5077313
theorem B2256583 : Blo 2005435 2256583 := bstep (se 1 (by rfl) ⟨1692437, by rfl⟩ : syracuseStep 2256583 = 3384875) B3384875
theorem B3008777 : Blo 2005435 3008777 := bstep (se 2 (by rfl) ⟨1128291, by rfl⟩ : syracuseStep 3008777 = 2256583) B2256583
theorem B2005851 : Blo 2005435 2005851 := bstep (se 1 (by rfl) ⟨1504388, by rfl⟩ : syracuseStep 2005851 = 3008777) B3008777
theorem B10154645 : Blo 2005435 10154645 := bbase (se 6 (by rfl) ⟨237999, by rfl⟩ : syracuseStep 10154645 = 475999) (by norm_num)
theorem B6769763 : Blo 2005435 6769763 := bstep (se 1 (by rfl) ⟨5077322, by rfl⟩ : syracuseStep 6769763 = 10154645) B10154645
theorem B4513175 : Blo 2005435 4513175 := bstep (se 1 (by rfl) ⟨3384881, by rfl⟩ : syracuseStep 4513175 = 6769763) B6769763
theorem B3008783 : Blo 2005435 3008783 := bstep (se 1 (by rfl) ⟨2256587, by rfl⟩ : syracuseStep 3008783 = 4513175) B4513175
theorem B2005855 : Blo 2005435 2005855 := bstep (se 1 (by rfl) ⟨1504391, by rfl⟩ : syracuseStep 2005855 = 3008783) B3008783
theorem B3008789 : Blo 2005435 3008789 := bbase (se 6 (by rfl) ⟨70518, by rfl⟩ : syracuseStep 3008789 = 141037) (by norm_num)
theorem B2005859 : Blo 2005435 2005859 := bstep (se 1 (by rfl) ⟨1504394, by rfl⟩ : syracuseStep 2005859 = 3008789) B3008789
theorem B87934805 : Blo 2005435 87934805 := bbase (se 9 (by rfl) ⟨257621, by rfl⟩ : syracuseStep 87934805 = 515243) (by norm_num)
theorem B58623203 : Blo 2005435 58623203 := bstep (se 1 (by rfl) ⟨43967402, by rfl⟩ : syracuseStep 58623203 = 87934805) B87934805
theorem B39082135 : Blo 2005435 39082135 := bstep (se 1 (by rfl) ⟨29311601, by rfl⟩ : syracuseStep 39082135 = 58623203) B58623203
theorem B52109513 : Blo 2005435 52109513 := bstep (se 2 (by rfl) ⟨19541067, by rfl⟩ : syracuseStep 52109513 = 39082135) B39082135
theorem B34739675 : Blo 2005435 34739675 := bstep (se 1 (by rfl) ⟨26054756, by rfl⟩ : syracuseStep 34739675 = 52109513) B52109513
theorem B23159783 : Blo 2005435 23159783 := bstep (se 1 (by rfl) ⟨17369837, by rfl⟩ : syracuseStep 23159783 = 34739675) B34739675
theorem B15439855 : Blo 2005435 15439855 := bstep (se 1 (by rfl) ⟨11579891, by rfl⟩ : syracuseStep 15439855 = 23159783) B23159783
theorem B20586473 : Blo 2005435 20586473 := bstep (se 2 (by rfl) ⟨7719927, by rfl⟩ : syracuseStep 20586473 = 15439855) B15439855
theorem B13724315 : Blo 2005435 13724315 := bstep (se 1 (by rfl) ⟨10293236, by rfl⟩ : syracuseStep 13724315 = 20586473) B20586473
theorem B9149543 : Blo 2005435 9149543 := bstep (se 1 (by rfl) ⟨6862157, by rfl⟩ : syracuseStep 9149543 = 13724315) B13724315
theorem B6099695 : Blo 2005435 6099695 := bstep (se 1 (by rfl) ⟨4574771, by rfl⟩ : syracuseStep 6099695 = 9149543) B9149543
theorem B4066463 : Blo 2005435 4066463 := bstep (se 1 (by rfl) ⟨3049847, by rfl⟩ : syracuseStep 4066463 = 6099695) B6099695
theorem B2710975 : Blo 2005435 2710975 := bstep (se 1 (by rfl) ⟨2033231, by rfl⟩ : syracuseStep 2710975 = 4066463) B4066463
theorem B3614633 : Blo 2005435 3614633 := bstep (se 2 (by rfl) ⟨1355487, by rfl⟩ : syracuseStep 3614633 = 2710975) B2710975
theorem B2409755 : Blo 2005435 2409755 := bstep (se 1 (by rfl) ⟨1807316, by rfl⟩ : syracuseStep 2409755 = 3614633) B3614633
theorem B25704053 : Blo 2005435 25704053 := bstep (se 5 (by rfl) ⟨1204877, by rfl⟩ : syracuseStep 25704053 = 2409755) B2409755
theorem B17136035 : Blo 2005435 17136035 := bstep (se 1 (by rfl) ⟨12852026, by rfl⟩ : syracuseStep 17136035 = 25704053) B25704053
theorem B11424023 : Blo 2005435 11424023 := bstep (se 1 (by rfl) ⟨8568017, by rfl⟩ : syracuseStep 11424023 = 17136035) B17136035
theorem B7616015 : Blo 2005435 7616015 := bstep (se 1 (by rfl) ⟨5712011, by rfl⟩ : syracuseStep 7616015 = 11424023) B11424023
theorem B5077343 : Blo 2005435 5077343 := bstep (se 1 (by rfl) ⟨3808007, by rfl⟩ : syracuseStep 5077343 = 7616015) B7616015
theorem B3384895 : Blo 2005435 3384895 := bstep (se 1 (by rfl) ⟨2538671, by rfl⟩ : syracuseStep 3384895 = 5077343) B5077343
theorem B4513193 : Blo 2005435 4513193 := bstep (se 2 (by rfl) ⟨1692447, by rfl⟩ : syracuseStep 4513193 = 3384895) B3384895
theorem B3008795 : Blo 2005435 3008795 := bstep (se 1 (by rfl) ⟨2256596, by rfl⟩ : syracuseStep 3008795 = 4513193) B4513193
theorem B2005863 : Blo 2005435 2005863 := bstep (se 1 (by rfl) ⟨1504397, by rfl⟩ : syracuseStep 2005863 = 3008795) B3008795
theorem B2256601 : Blo 2005435 2256601 := bbase (se 2 (by rfl) ⟨846225, by rfl⟩ : syracuseStep 2256601 = 1692451) (by norm_num)
theorem B3008801 : Blo 2005435 3008801 := bstep (se 2 (by rfl) ⟨1128300, by rfl⟩ : syracuseStep 3008801 = 2256601) B2256601
theorem B2005867 : Blo 2005435 2005867 := bstep (se 1 (by rfl) ⟨1504400, by rfl⟩ : syracuseStep 2005867 = 3008801) B3008801
theorem B2142013 : Blo 2005435 2142013 := bbase (se 3 (by rfl) ⟨401627, by rfl⟩ : syracuseStep 2142013 = 803255) (by norm_num)
theorem B2856017 : Blo 2005435 2856017 := bstep (se 2 (by rfl) ⟨1071006, by rfl⟩ : syracuseStep 2856017 = 2142013) B2142013
theorem B7616045 : Blo 2005435 7616045 := bstep (se 3 (by rfl) ⟨1428008, by rfl⟩ : syracuseStep 7616045 = 2856017) B2856017
theorem B5077363 : Blo 2005435 5077363 := bstep (se 1 (by rfl) ⟨3808022, by rfl⟩ : syracuseStep 5077363 = 7616045) B7616045
theorem B6769817 : Blo 2005435 6769817 := bstep (se 2 (by rfl) ⟨2538681, by rfl⟩ : syracuseStep 6769817 = 5077363) B5077363
theorem B4513211 : Blo 2005435 4513211 := bstep (se 1 (by rfl) ⟨3384908, by rfl⟩ : syracuseStep 4513211 = 6769817) B6769817
theorem B3008807 : Blo 2005435 3008807 := bstep (se 1 (by rfl) ⟨2256605, by rfl⟩ : syracuseStep 3008807 = 4513211) B4513211
theorem B2005871 : Blo 2005435 2005871 := bstep (se 1 (by rfl) ⟨1504403, by rfl⟩ : syracuseStep 2005871 = 3008807) B3008807
theorem B3008813 : Blo 2005435 3008813 := bbase (se 3 (by rfl) ⟨564152, by rfl⟩ : syracuseStep 3008813 = 1128305) (by norm_num)
theorem B2005875 : Blo 2005435 2005875 := bstep (se 1 (by rfl) ⟨1504406, by rfl⟩ : syracuseStep 2005875 = 3008813) B3008813
theorem B4513229 : Blo 2005435 4513229 := bbase (se 3 (by rfl) ⟨846230, by rfl⟩ : syracuseStep 4513229 = 1692461) (by norm_num)
theorem B3008819 : Blo 2005435 3008819 := bstep (se 1 (by rfl) ⟨2256614, by rfl⟩ : syracuseStep 3008819 = 4513229) B4513229
theorem B2005879 : Blo 2005435 2005879 := bstep (se 1 (by rfl) ⟨1504409, by rfl⟩ : syracuseStep 2005879 = 3008819) B3008819
theorem B2538697 : Blo 2005435 2538697 := bbase (se 2 (by rfl) ⟨952011, by rfl⟩ : syracuseStep 2538697 = 1904023) (by norm_num)
theorem B3384929 : Blo 2005435 3384929 := bstep (se 2 (by rfl) ⟨1269348, by rfl⟩ : syracuseStep 3384929 = 2538697) B2538697
theorem B2256619 : Blo 2005435 2256619 := bstep (se 1 (by rfl) ⟨1692464, by rfl⟩ : syracuseStep 2256619 = 3384929) B3384929
theorem B3008825 : Blo 2005435 3008825 := bstep (se 2 (by rfl) ⟨1128309, by rfl⟩ : syracuseStep 3008825 = 2256619) B2256619
theorem B2005883 : Blo 2005435 2005883 := bstep (se 1 (by rfl) ⟨1504412, by rfl⟩ : syracuseStep 2005883 = 3008825) B3008825
theorem B21983957 : Blo 2005435 21983957 := bbase (se 7 (by rfl) ⟨257624, by rfl⟩ : syracuseStep 21983957 = 515249) (by norm_num)
theorem B14655971 : Blo 2005435 14655971 := bstep (se 1 (by rfl) ⟨10991978, by rfl⟩ : syracuseStep 14655971 = 21983957) B21983957
theorem B9770647 : Blo 2005435 9770647 := bstep (se 1 (by rfl) ⟨7327985, by rfl⟩ : syracuseStep 9770647 = 14655971) B14655971
theorem B13027529 : Blo 2005435 13027529 := bstep (se 2 (by rfl) ⟨4885323, by rfl⟩ : syracuseStep 13027529 = 9770647) B9770647
theorem B8685019 : Blo 2005435 8685019 := bstep (se 1 (by rfl) ⟨6513764, by rfl⟩ : syracuseStep 8685019 = 13027529) B13027529
theorem B11580025 : Blo 2005435 11580025 := bstep (se 2 (by rfl) ⟨4342509, by rfl⟩ : syracuseStep 11580025 = 8685019) B8685019
theorem B15440033 : Blo 2005435 15440033 := bstep (se 2 (by rfl) ⟨5790012, by rfl⟩ : syracuseStep 15440033 = 11580025) B11580025
theorem B10293355 : Blo 2005435 10293355 := bstep (se 1 (by rfl) ⟨7720016, by rfl⟩ : syracuseStep 10293355 = 15440033) B15440033
theorem B13724473 : Blo 2005435 13724473 := bstep (se 2 (by rfl) ⟨5146677, by rfl⟩ : syracuseStep 13724473 = 10293355) B10293355
theorem B18299297 : Blo 2005435 18299297 := bstep (se 2 (by rfl) ⟨6862236, by rfl⟩ : syracuseStep 18299297 = 13724473) B13724473
theorem B12199531 : Blo 2005435 12199531 := bstep (se 1 (by rfl) ⟨9149648, by rfl⟩ : syracuseStep 12199531 = 18299297) B18299297
theorem B16266041 : Blo 2005435 16266041 := bstep (se 2 (by rfl) ⟨6099765, by rfl⟩ : syracuseStep 16266041 = 12199531) B12199531
theorem B10844027 : Blo 2005435 10844027 := bstep (se 1 (by rfl) ⟨8133020, by rfl⟩ : syracuseStep 10844027 = 16266041) B16266041
theorem B7229351 : Blo 2005435 7229351 := bstep (se 1 (by rfl) ⟨5422013, by rfl⟩ : syracuseStep 7229351 = 10844027) B10844027
theorem B19278269 : Blo 2005435 19278269 := bstep (se 3 (by rfl) ⟨3614675, by rfl⟩ : syracuseStep 19278269 = 7229351) B7229351
theorem B12852179 : Blo 2005435 12852179 := bstep (se 1 (by rfl) ⟨9639134, by rfl⟩ : syracuseStep 12852179 = 19278269) B19278269
theorem B8568119 : Blo 2005435 8568119 := bstep (se 1 (by rfl) ⟨6426089, by rfl⟩ : syracuseStep 8568119 = 12852179) B12852179
theorem B22848317 : Blo 2005435 22848317 := bstep (se 3 (by rfl) ⟨4284059, by rfl⟩ : syracuseStep 22848317 = 8568119) B8568119
theorem B15232211 : Blo 2005435 15232211 := bstep (se 1 (by rfl) ⟨11424158, by rfl⟩ : syracuseStep 15232211 = 22848317) B22848317
theorem B10154807 : Blo 2005435 10154807 := bstep (se 1 (by rfl) ⟨7616105, by rfl⟩ : syracuseStep 10154807 = 15232211) B15232211
theorem B6769871 : Blo 2005435 6769871 := bstep (se 1 (by rfl) ⟨5077403, by rfl⟩ : syracuseStep 6769871 = 10154807) B10154807
theorem B4513247 : Blo 2005435 4513247 := bstep (se 1 (by rfl) ⟨3384935, by rfl⟩ : syracuseStep 4513247 = 6769871) B6769871
theorem B3008831 : Blo 2005435 3008831 := bstep (se 1 (by rfl) ⟨2256623, by rfl⟩ : syracuseStep 3008831 = 4513247) B4513247
theorem B2005887 : Blo 2005435 2005887 := bstep (se 1 (by rfl) ⟨1504415, by rfl⟩ : syracuseStep 2005887 = 3008831) B3008831
theorem B3008837 : Blo 2005435 3008837 := bbase (se 4 (by rfl) ⟨282078, by rfl⟩ : syracuseStep 3008837 = 564157) (by norm_num)
theorem B2005891 : Blo 2005435 2005891 := bstep (se 1 (by rfl) ⟨1504418, by rfl⟩ : syracuseStep 2005891 = 3008837) B3008837
theorem B3384949 : Blo 2005435 3384949 := bbase (se 5 (by rfl) ⟨158669, by rfl⟩ : syracuseStep 3384949 = 317339) (by norm_num)
theorem B4513265 : Blo 2005435 4513265 := bstep (se 2 (by rfl) ⟨1692474, by rfl⟩ : syracuseStep 4513265 = 3384949) B3384949
theorem B3008843 : Blo 2005435 3008843 := bstep (se 1 (by rfl) ⟨2256632, by rfl⟩ : syracuseStep 3008843 = 4513265) B4513265
theorem B2005895 : Blo 2005435 2005895 := bstep (se 1 (by rfl) ⟨1504421, by rfl⟩ : syracuseStep 2005895 = 3008843) B3008843
theorem B2256637 : Blo 2005435 2256637 := bbase (se 3 (by rfl) ⟨423119, by rfl⟩ : syracuseStep 2256637 = 846239) (by norm_num)
theorem B3008849 : Blo 2005435 3008849 := bstep (se 2 (by rfl) ⟨1128318, by rfl⟩ : syracuseStep 3008849 = 2256637) B2256637
theorem B2005899 : Blo 2005435 2005899 := bstep (se 1 (by rfl) ⟨1504424, by rfl⟩ : syracuseStep 2005899 = 3008849) B3008849
theorem B6769925 : Blo 2005435 6769925 := bbase (se 4 (by rfl) ⟨634680, by rfl⟩ : syracuseStep 6769925 = 1269361) (by norm_num)
theorem B4513283 : Blo 2005435 4513283 := bstep (se 1 (by rfl) ⟨3384962, by rfl⟩ : syracuseStep 4513283 = 6769925) B6769925
theorem B3008855 : Blo 2005435 3008855 := bstep (se 1 (by rfl) ⟨2256641, by rfl⟩ : syracuseStep 3008855 = 4513283) B4513283
theorem B2005903 : Blo 2005435 2005903 := bstep (se 1 (by rfl) ⟨1504427, by rfl⟩ : syracuseStep 2005903 = 3008855) B3008855
theorem B3008861 : Blo 2005435 3008861 := bbase (se 3 (by rfl) ⟨564161, by rfl⟩ : syracuseStep 3008861 = 1128323) (by norm_num)
theorem B2005907 : Blo 2005435 2005907 := bstep (se 1 (by rfl) ⟨1504430, by rfl⟩ : syracuseStep 2005907 = 3008861) B3008861
theorem B4513301 : Blo 2005435 4513301 := bbase (se 6 (by rfl) ⟨105780, by rfl⟩ : syracuseStep 4513301 = 211561) (by norm_num)
theorem B3008867 : Blo 2005435 3008867 := bstep (se 1 (by rfl) ⟨2256650, by rfl⟩ : syracuseStep 3008867 = 4513301) B4513301
theorem B2005911 : Blo 2005435 2005911 := bstep (se 1 (by rfl) ⟨1504433, by rfl⟩ : syracuseStep 2005911 = 3008867) B3008867
theorem B7616213 : Blo 2005435 7616213 := bbase (se 7 (by rfl) ⟨89252, by rfl⟩ : syracuseStep 7616213 = 178505) (by norm_num)
theorem B5077475 : Blo 2005435 5077475 := bstep (se 1 (by rfl) ⟨3808106, by rfl⟩ : syracuseStep 5077475 = 7616213) B7616213
theorem B3384983 : Blo 2005435 3384983 := bstep (se 1 (by rfl) ⟨2538737, by rfl⟩ : syracuseStep 3384983 = 5077475) B5077475
theorem B2256655 : Blo 2005435 2256655 := bstep (se 1 (by rfl) ⟨1692491, by rfl⟩ : syracuseStep 2256655 = 3384983) B3384983
theorem B3008873 : Blo 2005435 3008873 := bstep (se 2 (by rfl) ⟨1128327, by rfl⟩ : syracuseStep 3008873 = 2256655) B2256655
theorem B2005915 : Blo 2005435 2005915 := bstep (se 1 (by rfl) ⟨1504436, by rfl⟩ : syracuseStep 2005915 = 3008873) B3008873
theorem B11424341 : Blo 2005435 11424341 := bbase (se 8 (by rfl) ⟨66939, by rfl⟩ : syracuseStep 11424341 = 133879) (by norm_num)
theorem B7616227 : Blo 2005435 7616227 := bstep (se 1 (by rfl) ⟨5712170, by rfl⟩ : syracuseStep 7616227 = 11424341) B11424341
theorem B10154969 : Blo 2005435 10154969 := bstep (se 2 (by rfl) ⟨3808113, by rfl⟩ : syracuseStep 10154969 = 7616227) B7616227
theorem B6769979 : Blo 2005435 6769979 := bstep (se 1 (by rfl) ⟨5077484, by rfl⟩ : syracuseStep 6769979 = 10154969) B10154969
theorem B4513319 : Blo 2005435 4513319 := bstep (se 1 (by rfl) ⟨3384989, by rfl⟩ : syracuseStep 4513319 = 6769979) B6769979
theorem B3008879 : Blo 2005435 3008879 := bstep (se 1 (by rfl) ⟨2256659, by rfl⟩ : syracuseStep 3008879 = 4513319) B4513319
theorem B2005919 : Blo 2005435 2005919 := bstep (se 1 (by rfl) ⟨1504439, by rfl⟩ : syracuseStep 2005919 = 3008879) B3008879
theorem B3008885 : Blo 2005435 3008885 := bbase (se 5 (by rfl) ⟨141041, by rfl⟩ : syracuseStep 3008885 = 282083) (by norm_num)
theorem B2005923 : Blo 2005435 2005923 := bstep (se 1 (by rfl) ⟨1504442, by rfl⟩ : syracuseStep 2005923 = 3008885) B3008885
theorem B2142073 : Blo 2005435 2142073 := bbase (se 2 (by rfl) ⟨803277, by rfl⟩ : syracuseStep 2142073 = 1606555) (by norm_num)
theorem B2856097 : Blo 2005435 2856097 := bstep (se 2 (by rfl) ⟨1071036, by rfl⟩ : syracuseStep 2856097 = 2142073) B2142073
theorem B3808129 : Blo 2005435 3808129 := bstep (se 2 (by rfl) ⟨1428048, by rfl⟩ : syracuseStep 3808129 = 2856097) B2856097
theorem B5077505 : Blo 2005435 5077505 := bstep (se 2 (by rfl) ⟨1904064, by rfl⟩ : syracuseStep 5077505 = 3808129) B3808129
theorem B3385003 : Blo 2005435 3385003 := bstep (se 1 (by rfl) ⟨2538752, by rfl⟩ : syracuseStep 3385003 = 5077505) B5077505
theorem B4513337 : Blo 2005435 4513337 := bstep (se 2 (by rfl) ⟨1692501, by rfl⟩ : syracuseStep 4513337 = 3385003) B3385003
theorem B3008891 : Blo 2005435 3008891 := bstep (se 1 (by rfl) ⟨2256668, by rfl⟩ : syracuseStep 3008891 = 4513337) B4513337
theorem B2005927 : Blo 2005435 2005927 := bstep (se 1 (by rfl) ⟨1504445, by rfl⟩ : syracuseStep 2005927 = 3008891) B3008891
theorem B2256673 : Blo 2005435 2256673 := bbase (se 2 (by rfl) ⟨846252, by rfl⟩ : syracuseStep 2256673 = 1692505) (by norm_num)
theorem B3008897 : Blo 2005435 3008897 := bstep (se 2 (by rfl) ⟨1128336, by rfl⟩ : syracuseStep 3008897 = 2256673) B2256673
theorem B2005931 : Blo 2005435 2005931 := bstep (se 1 (by rfl) ⟨1504448, by rfl⟩ : syracuseStep 2005931 = 3008897) B3008897
theorem B5077525 : Blo 2005435 5077525 := bbase (se 6 (by rfl) ⟨119004, by rfl⟩ : syracuseStep 5077525 = 238009) (by norm_num)
theorem B6770033 : Blo 2005435 6770033 := bstep (se 2 (by rfl) ⟨2538762, by rfl⟩ : syracuseStep 6770033 = 5077525) B5077525
theorem B4513355 : Blo 2005435 4513355 := bstep (se 1 (by rfl) ⟨3385016, by rfl⟩ : syracuseStep 4513355 = 6770033) B6770033
theorem B3008903 : Blo 2005435 3008903 := bstep (se 1 (by rfl) ⟨2256677, by rfl⟩ : syracuseStep 3008903 = 4513355) B4513355
theorem B2005935 : Blo 2005435 2005935 := bstep (se 1 (by rfl) ⟨1504451, by rfl⟩ : syracuseStep 2005935 = 3008903) B3008903
theorem B3008909 : Blo 2005435 3008909 := bbase (se 3 (by rfl) ⟨564170, by rfl⟩ : syracuseStep 3008909 = 1128341) (by norm_num)
theorem B2005939 : Blo 2005435 2005939 := bstep (se 1 (by rfl) ⟨1504454, by rfl⟩ : syracuseStep 2005939 = 3008909) B3008909
theorem B4513373 : Blo 2005435 4513373 := bbase (se 3 (by rfl) ⟨846257, by rfl⟩ : syracuseStep 4513373 = 1692515) (by norm_num)
theorem B3008915 : Blo 2005435 3008915 := bstep (se 1 (by rfl) ⟨2256686, by rfl⟩ : syracuseStep 3008915 = 4513373) B4513373
theorem B2005943 : Blo 2005435 2005943 := bstep (se 1 (by rfl) ⟨1504457, by rfl⟩ : syracuseStep 2005943 = 3008915) B3008915
theorem B3385037 : Blo 2005435 3385037 := bbase (se 3 (by rfl) ⟨634694, by rfl⟩ : syracuseStep 3385037 = 1269389) (by norm_num)
theorem B2256691 : Blo 2005435 2256691 := bstep (se 1 (by rfl) ⟨1692518, by rfl⟩ : syracuseStep 2256691 = 3385037) B3385037
theorem B3008921 : Blo 2005435 3008921 := bstep (se 2 (by rfl) ⟨1128345, by rfl⟩ : syracuseStep 3008921 = 2256691) B2256691
theorem B2005947 : Blo 2005435 2005947 := bstep (se 1 (by rfl) ⟨1504460, by rfl⟩ : syracuseStep 2005947 = 3008921) B3008921
theorem B75210581 : Blo 2005435 75210581 := bbase (se 9 (by rfl) ⟨220343, by rfl⟩ : syracuseStep 75210581 = 440687) (by norm_num)
theorem B50140387 : Blo 2005435 50140387 := bstep (se 1 (by rfl) ⟨37605290, by rfl⟩ : syracuseStep 50140387 = 75210581) B75210581
theorem B66853849 : Blo 2005435 66853849 := bstep (se 2 (by rfl) ⟨25070193, by rfl⟩ : syracuseStep 66853849 = 50140387) B50140387
theorem B89138465 : Blo 2005435 89138465 := bstep (se 2 (by rfl) ⟨33426924, by rfl⟩ : syracuseStep 89138465 = 66853849) B66853849
theorem B59425643 : Blo 2005435 59425643 := bstep (se 1 (by rfl) ⟨44569232, by rfl⟩ : syracuseStep 59425643 = 89138465) B89138465
theorem B39617095 : Blo 2005435 39617095 := bstep (se 1 (by rfl) ⟨29712821, by rfl⟩ : syracuseStep 39617095 = 59425643) B59425643
theorem B52822793 : Blo 2005435 52822793 := bstep (se 2 (by rfl) ⟨19808547, by rfl⟩ : syracuseStep 52822793 = 39617095) B39617095
theorem B35215195 : Blo 2005435 35215195 := bstep (se 1 (by rfl) ⟨26411396, by rfl⟩ : syracuseStep 35215195 = 52822793) B52822793
theorem B46953593 : Blo 2005435 46953593 := bstep (se 2 (by rfl) ⟨17607597, by rfl⟩ : syracuseStep 46953593 = 35215195) B35215195
theorem B31302395 : Blo 2005435 31302395 := bstep (se 1 (by rfl) ⟨23476796, by rfl⟩ : syracuseStep 31302395 = 46953593) B46953593
theorem B20868263 : Blo 2005435 20868263 := bstep (se 1 (by rfl) ⟨15651197, by rfl⟩ : syracuseStep 20868263 = 31302395) B31302395
theorem B13912175 : Blo 2005435 13912175 := bstep (se 1 (by rfl) ⟨10434131, by rfl⟩ : syracuseStep 13912175 = 20868263) B20868263
theorem B9274783 : Blo 2005435 9274783 := bstep (se 1 (by rfl) ⟨6956087, by rfl⟩ : syracuseStep 9274783 = 13912175) B13912175
theorem B12366377 : Blo 2005435 12366377 := bstep (se 2 (by rfl) ⟨4637391, by rfl⟩ : syracuseStep 12366377 = 9274783) B9274783
theorem B8244251 : Blo 2005435 8244251 := bstep (se 1 (by rfl) ⟨6183188, by rfl⟩ : syracuseStep 8244251 = 12366377) B12366377
theorem B5496167 : Blo 2005435 5496167 := bstep (se 1 (by rfl) ⟨4122125, by rfl⟩ : syracuseStep 5496167 = 8244251) B8244251
theorem B3664111 : Blo 2005435 3664111 := bstep (se 1 (by rfl) ⟨2748083, by rfl⟩ : syracuseStep 3664111 = 5496167) B5496167
theorem B4885481 : Blo 2005435 4885481 := bstep (se 2 (by rfl) ⟨1832055, by rfl⟩ : syracuseStep 4885481 = 3664111) B3664111
theorem B13027949 : Blo 2005435 13027949 := bstep (se 3 (by rfl) ⟨2442740, by rfl⟩ : syracuseStep 13027949 = 4885481) B4885481
theorem B8685299 : Blo 2005435 8685299 := bstep (se 1 (by rfl) ⟨6513974, by rfl⟩ : syracuseStep 8685299 = 13027949) B13027949
theorem B5790199 : Blo 2005435 5790199 := bstep (se 1 (by rfl) ⟨4342649, by rfl⟩ : syracuseStep 5790199 = 8685299) B8685299
theorem B7720265 : Blo 2005435 7720265 := bstep (se 2 (by rfl) ⟨2895099, by rfl⟩ : syracuseStep 7720265 = 5790199) B5790199
theorem B5146843 : Blo 2005435 5146843 := bstep (se 1 (by rfl) ⟨3860132, by rfl⟩ : syracuseStep 5146843 = 7720265) B7720265
theorem B6862457 : Blo 2005435 6862457 := bstep (se 2 (by rfl) ⟨2573421, by rfl⟩ : syracuseStep 6862457 = 5146843) B5146843
theorem B4574971 : Blo 2005435 4574971 := bstep (se 1 (by rfl) ⟨3431228, by rfl⟩ : syracuseStep 4574971 = 6862457) B6862457
theorem B6099961 : Blo 2005435 6099961 := bstep (se 2 (by rfl) ⟨2287485, by rfl⟩ : syracuseStep 6099961 = 4574971) B4574971
theorem B8133281 : Blo 2005435 8133281 := bstep (se 2 (by rfl) ⟨3049980, by rfl⟩ : syracuseStep 8133281 = 6099961) B6099961
theorem B5422187 : Blo 2005435 5422187 := bstep (se 1 (by rfl) ⟨4066640, by rfl⟩ : syracuseStep 5422187 = 8133281) B8133281
theorem B3614791 : Blo 2005435 3614791 := bstep (se 1 (by rfl) ⟨2711093, by rfl⟩ : syracuseStep 3614791 = 5422187) B5422187
theorem B4819721 : Blo 2005435 4819721 := bstep (se 2 (by rfl) ⟨1807395, by rfl⟩ : syracuseStep 4819721 = 3614791) B3614791
theorem B12852589 : Blo 2005435 12852589 := bstep (se 3 (by rfl) ⟨2409860, by rfl⟩ : syracuseStep 12852589 = 4819721) B4819721
theorem B17136785 : Blo 2005435 17136785 := bstep (se 2 (by rfl) ⟨6426294, by rfl⟩ : syracuseStep 17136785 = 12852589) B12852589
theorem B11424523 : Blo 2005435 11424523 := bstep (se 1 (by rfl) ⟨8568392, by rfl⟩ : syracuseStep 11424523 = 17136785) B17136785
theorem B15232697 : Blo 2005435 15232697 := bstep (se 2 (by rfl) ⟨5712261, by rfl⟩ : syracuseStep 15232697 = 11424523) B11424523
theorem B10155131 : Blo 2005435 10155131 := bstep (se 1 (by rfl) ⟨7616348, by rfl⟩ : syracuseStep 10155131 = 15232697) B15232697
theorem B6770087 : Blo 2005435 6770087 := bstep (se 1 (by rfl) ⟨5077565, by rfl⟩ : syracuseStep 6770087 = 10155131) B10155131
theorem B4513391 : Blo 2005435 4513391 := bstep (se 1 (by rfl) ⟨3385043, by rfl⟩ : syracuseStep 4513391 = 6770087) B6770087
theorem B3008927 : Blo 2005435 3008927 := bstep (se 1 (by rfl) ⟨2256695, by rfl⟩ : syracuseStep 3008927 = 4513391) B4513391
theorem B2005951 : Blo 2005435 2005951 := bstep (se 1 (by rfl) ⟨1504463, by rfl⟩ : syracuseStep 2005951 = 3008927) B3008927
theorem B3008933 : Blo 2005435 3008933 := bbase (se 4 (by rfl) ⟨282087, by rfl⟩ : syracuseStep 3008933 = 564175) (by norm_num)
theorem B2005955 : Blo 2005435 2005955 := bstep (se 1 (by rfl) ⟨1504466, by rfl⟩ : syracuseStep 2005955 = 3008933) B3008933
theorem B2538793 : Blo 2005435 2538793 := bbase (se 2 (by rfl) ⟨952047, by rfl⟩ : syracuseStep 2538793 = 1904095) (by norm_num)
theorem B3385057 : Blo 2005435 3385057 := bstep (se 2 (by rfl) ⟨1269396, by rfl⟩ : syracuseStep 3385057 = 2538793) B2538793
theorem B4513409 : Blo 2005435 4513409 := bstep (se 2 (by rfl) ⟨1692528, by rfl⟩ : syracuseStep 4513409 = 3385057) B3385057
theorem B3008939 : Blo 2005435 3008939 := bstep (se 1 (by rfl) ⟨2256704, by rfl⟩ : syracuseStep 3008939 = 4513409) B4513409
theorem B2005959 : Blo 2005435 2005959 := bstep (se 1 (by rfl) ⟨1504469, by rfl⟩ : syracuseStep 2005959 = 3008939) B3008939
theorem B2256709 : Blo 2005435 2256709 := bbase (se 4 (by rfl) ⟨211566, by rfl⟩ : syracuseStep 2256709 = 423133) (by norm_num)
theorem B3008945 : Blo 2005435 3008945 := bstep (se 2 (by rfl) ⟨1128354, by rfl⟩ : syracuseStep 3008945 = 2256709) B2256709
theorem B2005963 : Blo 2005435 2005963 := bstep (se 1 (by rfl) ⟨1504472, by rfl⟩ : syracuseStep 2005963 = 3008945) B3008945
theorem B3808205 : Blo 2005435 3808205 := bbase (se 3 (by rfl) ⟨714038, by rfl⟩ : syracuseStep 3808205 = 1428077) (by norm_num)
theorem B2538803 : Blo 2005435 2538803 := bstep (se 1 (by rfl) ⟨1904102, by rfl⟩ : syracuseStep 2538803 = 3808205) B3808205
theorem B6770141 : Blo 2005435 6770141 := bstep (se 3 (by rfl) ⟨1269401, by rfl⟩ : syracuseStep 6770141 = 2538803) B2538803
theorem B4513427 : Blo 2005435 4513427 := bstep (se 1 (by rfl) ⟨3385070, by rfl⟩ : syracuseStep 4513427 = 6770141) B6770141
theorem B3008951 : Blo 2005435 3008951 := bstep (se 1 (by rfl) ⟨2256713, by rfl⟩ : syracuseStep 3008951 = 4513427) B4513427
theorem B2005967 : Blo 2005435 2005967 := bstep (se 1 (by rfl) ⟨1504475, by rfl⟩ : syracuseStep 2005967 = 3008951) B3008951
theorem B3008957 : Blo 2005435 3008957 := bbase (se 3 (by rfl) ⟨564179, by rfl⟩ : syracuseStep 3008957 = 1128359) (by norm_num)
theorem B2005971 : Blo 2005435 2005971 := bstep (se 1 (by rfl) ⟨1504478, by rfl⟩ : syracuseStep 2005971 = 3008957) B3008957
theorem B4513445 : Blo 2005435 4513445 := bbase (se 4 (by rfl) ⟨423135, by rfl⟩ : syracuseStep 4513445 = 846271) (by norm_num)
theorem B3008963 : Blo 2005435 3008963 := bstep (se 1 (by rfl) ⟨2256722, by rfl⟩ : syracuseStep 3008963 = 4513445) B4513445
theorem B2005975 : Blo 2005435 2005975 := bstep (se 1 (by rfl) ⟨1504481, by rfl⟩ : syracuseStep 2005975 = 3008963) B3008963
theorem B5077637 : Blo 2005435 5077637 := bbase (se 4 (by rfl) ⟨476028, by rfl⟩ : syracuseStep 5077637 = 952057) (by norm_num)
theorem B3385091 : Blo 2005435 3385091 := bstep (se 1 (by rfl) ⟨2538818, by rfl⟩ : syracuseStep 3385091 = 5077637) B5077637
theorem B2256727 : Blo 2005435 2256727 := bstep (se 1 (by rfl) ⟨1692545, by rfl⟩ : syracuseStep 2256727 = 3385091) B3385091
theorem B3008969 : Blo 2005435 3008969 := bstep (se 2 (by rfl) ⟨1128363, by rfl⟩ : syracuseStep 3008969 = 2256727) B2256727
theorem B2005979 : Blo 2005435 2005979 := bstep (se 1 (by rfl) ⟨1504484, by rfl⟩ : syracuseStep 2005979 = 3008969) B3008969
theorem B2033353 : Blo 2005435 2033353 := bbase (se 2 (by rfl) ⟨762507, by rfl⟩ : syracuseStep 2033353 = 1525015) (by norm_num)
theorem B10844549 : Blo 2005435 10844549 := bstep (se 4 (by rfl) ⟨1016676, by rfl⟩ : syracuseStep 10844549 = 2033353) B2033353
theorem B7229699 : Blo 2005435 7229699 := bstep (se 1 (by rfl) ⟨5422274, by rfl⟩ : syracuseStep 7229699 = 10844549) B10844549
theorem B4819799 : Blo 2005435 4819799 := bstep (se 1 (by rfl) ⟨3614849, by rfl⟩ : syracuseStep 4819799 = 7229699) B7229699
theorem B3213199 : Blo 2005435 3213199 := bstep (se 1 (by rfl) ⟨2409899, by rfl⟩ : syracuseStep 3213199 = 4819799) B4819799
theorem B4284265 : Blo 2005435 4284265 := bstep (se 2 (by rfl) ⟨1606599, by rfl⟩ : syracuseStep 4284265 = 3213199) B3213199
theorem B5712353 : Blo 2005435 5712353 := bstep (se 2 (by rfl) ⟨2142132, by rfl⟩ : syracuseStep 5712353 = 4284265) B4284265
theorem B3808235 : Blo 2005435 3808235 := bstep (se 1 (by rfl) ⟨2856176, by rfl⟩ : syracuseStep 3808235 = 5712353) B5712353
theorem B10155293 : Blo 2005435 10155293 := bstep (se 3 (by rfl) ⟨1904117, by rfl⟩ : syracuseStep 10155293 = 3808235) B3808235
theorem B6770195 : Blo 2005435 6770195 := bstep (se 1 (by rfl) ⟨5077646, by rfl⟩ : syracuseStep 6770195 = 10155293) B10155293
theorem B4513463 : Blo 2005435 4513463 := bstep (se 1 (by rfl) ⟨3385097, by rfl⟩ : syracuseStep 4513463 = 6770195) B6770195
theorem B3008975 : Blo 2005435 3008975 := bstep (se 1 (by rfl) ⟨2256731, by rfl⟩ : syracuseStep 3008975 = 4513463) B4513463
theorem B2005983 : Blo 2005435 2005983 := bstep (se 1 (by rfl) ⟨1504487, by rfl⟩ : syracuseStep 2005983 = 3008975) B3008975
theorem B3008981 : Blo 2005435 3008981 := bbase (se 7 (by rfl) ⟨35261, by rfl⟩ : syracuseStep 3008981 = 70523) (by norm_num)
theorem B2005987 : Blo 2005435 2005987 := bstep (se 1 (by rfl) ⟨1504490, by rfl⟩ : syracuseStep 2005987 = 3008981) B3008981
theorem B7616501 : Blo 2005435 7616501 := bbase (se 5 (by rfl) ⟨357023, by rfl⟩ : syracuseStep 7616501 = 714047) (by norm_num)
theorem B5077667 : Blo 2005435 5077667 := bstep (se 1 (by rfl) ⟨3808250, by rfl⟩ : syracuseStep 5077667 = 7616501) B7616501
theorem B3385111 : Blo 2005435 3385111 := bstep (se 1 (by rfl) ⟨2538833, by rfl⟩ : syracuseStep 3385111 = 5077667) B5077667
theorem B4513481 : Blo 2005435 4513481 := bstep (se 2 (by rfl) ⟨1692555, by rfl⟩ : syracuseStep 4513481 = 3385111) B3385111
theorem B3008987 : Blo 2005435 3008987 := bstep (se 1 (by rfl) ⟨2256740, by rfl⟩ : syracuseStep 3008987 = 4513481) B4513481
theorem B2005991 : Blo 2005435 2005991 := bstep (se 1 (by rfl) ⟨1504493, by rfl⟩ : syracuseStep 2005991 = 3008987) B3008987
theorem B2256745 : Blo 2005435 2256745 := bbase (se 2 (by rfl) ⟨846279, by rfl⟩ : syracuseStep 2256745 = 1692559) (by norm_num)
theorem B3008993 : Blo 2005435 3008993 := bstep (se 2 (by rfl) ⟨1128372, by rfl⟩ : syracuseStep 3008993 = 2256745) B2256745
theorem B2005995 : Blo 2005435 2005995 := bstep (se 1 (by rfl) ⟨1504496, by rfl⟩ : syracuseStep 2005995 = 3008993) B3008993
theorem B4819837 : Blo 2005435 4819837 := bbase (se 3 (by rfl) ⟨903719, by rfl⟩ : syracuseStep 4819837 = 1807439) (by norm_num)
theorem B6426449 : Blo 2005435 6426449 := bstep (se 2 (by rfl) ⟨2409918, by rfl⟩ : syracuseStep 6426449 = 4819837) B4819837
theorem B4284299 : Blo 2005435 4284299 := bstep (se 1 (by rfl) ⟨3213224, by rfl⟩ : syracuseStep 4284299 = 6426449) B6426449
theorem B11424797 : Blo 2005435 11424797 := bstep (se 3 (by rfl) ⟨2142149, by rfl⟩ : syracuseStep 11424797 = 4284299) B4284299
theorem B7616531 : Blo 2005435 7616531 := bstep (se 1 (by rfl) ⟨5712398, by rfl⟩ : syracuseStep 7616531 = 11424797) B11424797
theorem B5077687 : Blo 2005435 5077687 := bstep (se 1 (by rfl) ⟨3808265, by rfl⟩ : syracuseStep 5077687 = 7616531) B7616531
theorem B6770249 : Blo 2005435 6770249 := bstep (se 2 (by rfl) ⟨2538843, by rfl⟩ : syracuseStep 6770249 = 5077687) B5077687
theorem B4513499 : Blo 2005435 4513499 := bstep (se 1 (by rfl) ⟨3385124, by rfl⟩ : syracuseStep 4513499 = 6770249) B6770249
theorem B3008999 : Blo 2005435 3008999 := bstep (se 1 (by rfl) ⟨2256749, by rfl⟩ : syracuseStep 3008999 = 4513499) B4513499
theorem B2005999 : Blo 2005435 2005999 := bstep (se 1 (by rfl) ⟨1504499, by rfl⟩ : syracuseStep 2005999 = 3008999) B3008999
theorem B3009005 : Blo 2005435 3009005 := bbase (se 3 (by rfl) ⟨564188, by rfl⟩ : syracuseStep 3009005 = 1128377) (by norm_num)
theorem B2006003 : Blo 2005435 2006003 := bstep (se 1 (by rfl) ⟨1504502, by rfl⟩ : syracuseStep 2006003 = 3009005) B3009005
theorem B4513517 : Blo 2005435 4513517 := bbase (se 3 (by rfl) ⟨846284, by rfl⟩ : syracuseStep 4513517 = 1692569) (by norm_num)
theorem B3009011 : Blo 2005435 3009011 := bstep (se 1 (by rfl) ⟨2256758, by rfl⟩ : syracuseStep 3009011 = 4513517) B4513517
theorem B2006007 : Blo 2005435 2006007 := bstep (se 1 (by rfl) ⟨1504505, by rfl⟩ : syracuseStep 2006007 = 3009011) B3009011
theorem B3213245 : Blo 2005435 3213245 := bbase (se 3 (by rfl) ⟨602483, by rfl⟩ : syracuseStep 3213245 = 1204967) (by norm_num)
theorem B2142163 : Blo 2005435 2142163 := bstep (se 1 (by rfl) ⟨1606622, by rfl⟩ : syracuseStep 2142163 = 3213245) B3213245
theorem B2856217 : Blo 2005435 2856217 := bstep (se 2 (by rfl) ⟨1071081, by rfl⟩ : syracuseStep 2856217 = 2142163) B2142163
theorem B3808289 : Blo 2005435 3808289 := bstep (se 2 (by rfl) ⟨1428108, by rfl⟩ : syracuseStep 3808289 = 2856217) B2856217
theorem B2538859 : Blo 2005435 2538859 := bstep (se 1 (by rfl) ⟨1904144, by rfl⟩ : syracuseStep 2538859 = 3808289) B3808289
theorem B3385145 : Blo 2005435 3385145 := bstep (se 2 (by rfl) ⟨1269429, by rfl⟩ : syracuseStep 3385145 = 2538859) B2538859
theorem B2256763 : Blo 2005435 2256763 := bstep (se 1 (by rfl) ⟨1692572, by rfl⟩ : syracuseStep 2256763 = 3385145) B3385145
theorem B3009017 : Blo 2005435 3009017 := bstep (se 2 (by rfl) ⟨1128381, by rfl⟩ : syracuseStep 3009017 = 2256763) B2256763
theorem B2006011 : Blo 2005435 2006011 := bstep (se 1 (by rfl) ⟨1504508, by rfl⟩ : syracuseStep 2006011 = 3009017) B3009017
theorem B2442817 : Blo 2005435 2442817 := bbase (se 2 (by rfl) ⟨916056, by rfl⟩ : syracuseStep 2442817 = 1832113) (by norm_num)
theorem B13028357 : Blo 2005435 13028357 := bstep (se 4 (by rfl) ⟨1221408, by rfl⟩ : syracuseStep 13028357 = 2442817) B2442817
theorem B8685571 : Blo 2005435 8685571 := bstep (se 1 (by rfl) ⟨6514178, by rfl⟩ : syracuseStep 8685571 = 13028357) B13028357
theorem B11580761 : Blo 2005435 11580761 := bstep (se 2 (by rfl) ⟨4342785, by rfl⟩ : syracuseStep 11580761 = 8685571) B8685571
theorem B30882029 : Blo 2005435 30882029 := bstep (se 3 (by rfl) ⟨5790380, by rfl⟩ : syracuseStep 30882029 = 11580761) B11580761
theorem B329408309 : Blo 2005435 329408309 := bstep (se 5 (by rfl) ⟨15441014, by rfl⟩ : syracuseStep 329408309 = 30882029) B30882029
theorem B219605539 : Blo 2005435 219605539 := bstep (se 1 (by rfl) ⟨164704154, by rfl⟩ : syracuseStep 219605539 = 329408309) B329408309
theorem B292807385 : Blo 2005435 292807385 := bstep (se 2 (by rfl) ⟨109802769, by rfl⟩ : syracuseStep 292807385 = 219605539) B219605539
theorem B195204923 : Blo 2005435 195204923 := bstep (se 1 (by rfl) ⟨146403692, by rfl⟩ : syracuseStep 195204923 = 292807385) B292807385
theorem B130136615 : Blo 2005435 130136615 := bstep (se 1 (by rfl) ⟨97602461, by rfl⟩ : syracuseStep 130136615 = 195204923) B195204923
theorem B86757743 : Blo 2005435 86757743 := bstep (se 1 (by rfl) ⟨65068307, by rfl⟩ : syracuseStep 86757743 = 130136615) B130136615
theorem B57838495 : Blo 2005435 57838495 := bstep (se 1 (by rfl) ⟨43378871, by rfl⟩ : syracuseStep 57838495 = 86757743) B86757743
theorem B77117993 : Blo 2005435 77117993 := bstep (se 2 (by rfl) ⟨28919247, by rfl⟩ : syracuseStep 77117993 = 57838495) B57838495
theorem B51411995 : Blo 2005435 51411995 := bstep (se 1 (by rfl) ⟨38558996, by rfl⟩ : syracuseStep 51411995 = 77117993) B77117993
theorem B34274663 : Blo 2005435 34274663 := bstep (se 1 (by rfl) ⟨25705997, by rfl⟩ : syracuseStep 34274663 = 51411995) B51411995
theorem B22849775 : Blo 2005435 22849775 := bstep (se 1 (by rfl) ⟨17137331, by rfl⟩ : syracuseStep 22849775 = 34274663) B34274663
theorem B15233183 : Blo 2005435 15233183 := bstep (se 1 (by rfl) ⟨11424887, by rfl⟩ : syracuseStep 15233183 = 22849775) B22849775
theorem B10155455 : Blo 2005435 10155455 := bstep (se 1 (by rfl) ⟨7616591, by rfl⟩ : syracuseStep 10155455 = 15233183) B15233183
theorem B6770303 : Blo 2005435 6770303 := bstep (se 1 (by rfl) ⟨5077727, by rfl⟩ : syracuseStep 6770303 = 10155455) B10155455
theorem B4513535 : Blo 2005435 4513535 := bstep (se 1 (by rfl) ⟨3385151, by rfl⟩ : syracuseStep 4513535 = 6770303) B6770303
theorem B3009023 : Blo 2005435 3009023 := bstep (se 1 (by rfl) ⟨2256767, by rfl⟩ : syracuseStep 3009023 = 4513535) B4513535
theorem B2006015 : Blo 2005435 2006015 := bstep (se 1 (by rfl) ⟨1504511, by rfl⟩ : syracuseStep 2006015 = 3009023) B3009023
theorem B3009029 : Blo 2005435 3009029 := bbase (se 4 (by rfl) ⟨282096, by rfl⟩ : syracuseStep 3009029 = 564193) (by norm_num)
theorem B2006019 : Blo 2005435 2006019 := bstep (se 1 (by rfl) ⟨1504514, by rfl⟩ : syracuseStep 2006019 = 3009029) B3009029
theorem B3385165 : Blo 2005435 3385165 := bbase (se 3 (by rfl) ⟨634718, by rfl⟩ : syracuseStep 3385165 = 1269437) (by norm_num)
theorem B4513553 : Blo 2005435 4513553 := bstep (se 2 (by rfl) ⟨1692582, by rfl⟩ : syracuseStep 4513553 = 3385165) B3385165
theorem B3009035 : Blo 2005435 3009035 := bstep (se 1 (by rfl) ⟨2256776, by rfl⟩ : syracuseStep 3009035 = 4513553) B4513553
theorem B2006023 : Blo 2005435 2006023 := bstep (se 1 (by rfl) ⟨1504517, by rfl⟩ : syracuseStep 2006023 = 3009035) B3009035
theorem B2256781 : Blo 2005435 2256781 := bbase (se 3 (by rfl) ⟨423146, by rfl⟩ : syracuseStep 2256781 = 846293) (by norm_num)
theorem B3009041 : Blo 2005435 3009041 := bstep (se 2 (by rfl) ⟨1128390, by rfl⟩ : syracuseStep 3009041 = 2256781) B2256781
theorem B2006027 : Blo 2005435 2006027 := bstep (se 1 (by rfl) ⟨1504520, by rfl⟩ : syracuseStep 2006027 = 3009041) B3009041
theorem B6770357 : Blo 2005435 6770357 := bbase (se 5 (by rfl) ⟨317360, by rfl⟩ : syracuseStep 6770357 = 634721) (by norm_num)
theorem B4513571 : Blo 2005435 4513571 := bstep (se 1 (by rfl) ⟨3385178, by rfl⟩ : syracuseStep 4513571 = 6770357) B6770357
theorem B3009047 : Blo 2005435 3009047 := bstep (se 1 (by rfl) ⟨2256785, by rfl⟩ : syracuseStep 3009047 = 4513571) B4513571
theorem B2006031 : Blo 2005435 2006031 := bstep (se 1 (by rfl) ⟨1504523, by rfl⟩ : syracuseStep 2006031 = 3009047) B3009047
theorem B3009053 : Blo 2005435 3009053 := bbase (se 3 (by rfl) ⟨564197, by rfl⟩ : syracuseStep 3009053 = 1128395) (by norm_num)
theorem B2006035 : Blo 2005435 2006035 := bstep (se 1 (by rfl) ⟨1504526, by rfl⟩ : syracuseStep 2006035 = 3009053) B3009053
theorem B4513589 : Blo 2005435 4513589 := bbase (se 5 (by rfl) ⟨211574, by rfl⟩ : syracuseStep 4513589 = 423149) (by norm_num)
theorem B3009059 : Blo 2005435 3009059 := bstep (se 1 (by rfl) ⟨2256794, by rfl⟩ : syracuseStep 3009059 = 4513589) B4513589
theorem B2006039 : Blo 2005435 2006039 := bstep (se 1 (by rfl) ⟨1504529, by rfl⟩ : syracuseStep 2006039 = 3009059) B3009059
theorem B18300725 : Blo 2005435 18300725 := bbase (se 5 (by rfl) ⟨857846, by rfl⟩ : syracuseStep 18300725 = 1715693) (by norm_num)
theorem B12200483 : Blo 2005435 12200483 := bstep (se 1 (by rfl) ⟨9150362, by rfl⟩ : syracuseStep 12200483 = 18300725) B18300725
theorem B8133655 : Blo 2005435 8133655 := bstep (se 1 (by rfl) ⟨6100241, by rfl⟩ : syracuseStep 8133655 = 12200483) B12200483
theorem B10844873 : Blo 2005435 10844873 := bstep (se 2 (by rfl) ⟨4066827, by rfl⟩ : syracuseStep 10844873 = 8133655) B8133655
theorem B7229915 : Blo 2005435 7229915 := bstep (se 1 (by rfl) ⟨5422436, by rfl⟩ : syracuseStep 7229915 = 10844873) B10844873
theorem B4819943 : Blo 2005435 4819943 := bstep (se 1 (by rfl) ⟨3614957, by rfl⟩ : syracuseStep 4819943 = 7229915) B7229915
theorem B12853181 : Blo 2005435 12853181 := bstep (se 3 (by rfl) ⟨2409971, by rfl⟩ : syracuseStep 12853181 = 4819943) B4819943
theorem B8568787 : Blo 2005435 8568787 := bstep (se 1 (by rfl) ⟨6426590, by rfl⟩ : syracuseStep 8568787 = 12853181) B12853181
theorem B11425049 : Blo 2005435 11425049 := bstep (se 2 (by rfl) ⟨4284393, by rfl⟩ : syracuseStep 11425049 = 8568787) B8568787
theorem B7616699 : Blo 2005435 7616699 := bstep (se 1 (by rfl) ⟨5712524, by rfl⟩ : syracuseStep 7616699 = 11425049) B11425049
theorem B5077799 : Blo 2005435 5077799 := bstep (se 1 (by rfl) ⟨3808349, by rfl⟩ : syracuseStep 5077799 = 7616699) B7616699
theorem B3385199 : Blo 2005435 3385199 := bstep (se 1 (by rfl) ⟨2538899, by rfl⟩ : syracuseStep 3385199 = 5077799) B5077799
theorem B2256799 : Blo 2005435 2256799 := bstep (se 1 (by rfl) ⟨1692599, by rfl⟩ : syracuseStep 2256799 = 3385199) B3385199
theorem B3009065 : Blo 2005435 3009065 := bstep (se 2 (by rfl) ⟨1128399, by rfl⟩ : syracuseStep 3009065 = 2256799) B2256799
theorem B2006043 : Blo 2005435 2006043 := bstep (se 1 (by rfl) ⟨1504532, by rfl⟩ : syracuseStep 2006043 = 3009065) B3009065
theorem B12853205 : Blo 2005435 12853205 := bbase (se 7 (by rfl) ⟨150623, by rfl⟩ : syracuseStep 12853205 = 301247) (by norm_num)
theorem B8568803 : Blo 2005435 8568803 := bstep (se 1 (by rfl) ⟨6426602, by rfl⟩ : syracuseStep 8568803 = 12853205) B12853205
theorem B5712535 : Blo 2005435 5712535 := bstep (se 1 (by rfl) ⟨4284401, by rfl⟩ : syracuseStep 5712535 = 8568803) B8568803
theorem B7616713 : Blo 2005435 7616713 := bstep (se 2 (by rfl) ⟨2856267, by rfl⟩ : syracuseStep 7616713 = 5712535) B5712535
theorem B10155617 : Blo 2005435 10155617 := bstep (se 2 (by rfl) ⟨3808356, by rfl⟩ : syracuseStep 10155617 = 7616713) B7616713
theorem B6770411 : Blo 2005435 6770411 := bstep (se 1 (by rfl) ⟨5077808, by rfl⟩ : syracuseStep 6770411 = 10155617) B10155617
theorem B4513607 : Blo 2005435 4513607 := bstep (se 1 (by rfl) ⟨3385205, by rfl⟩ : syracuseStep 4513607 = 6770411) B6770411
theorem B3009071 : Blo 2005435 3009071 := bstep (se 1 (by rfl) ⟨2256803, by rfl⟩ : syracuseStep 3009071 = 4513607) B4513607
theorem B2006047 : Blo 2005435 2006047 := bstep (se 1 (by rfl) ⟨1504535, by rfl⟩ : syracuseStep 2006047 = 3009071) B3009071
theorem B3009077 : Blo 2005435 3009077 := bbase (se 5 (by rfl) ⟨141050, by rfl⟩ : syracuseStep 3009077 = 282101) (by norm_num)
theorem B2006051 : Blo 2005435 2006051 := bstep (se 1 (by rfl) ⟨1504538, by rfl⟩ : syracuseStep 2006051 = 3009077) B3009077
theorem B5077829 : Blo 2005435 5077829 := bbase (se 4 (by rfl) ⟨476046, by rfl⟩ : syracuseStep 5077829 = 952093) (by norm_num)
theorem B3385219 : Blo 2005435 3385219 := bstep (se 1 (by rfl) ⟨2538914, by rfl⟩ : syracuseStep 3385219 = 5077829) B5077829
theorem B4513625 : Blo 2005435 4513625 := bstep (se 2 (by rfl) ⟨1692609, by rfl⟩ : syracuseStep 4513625 = 3385219) B3385219
theorem B3009083 : Blo 2005435 3009083 := bstep (se 1 (by rfl) ⟨2256812, by rfl⟩ : syracuseStep 3009083 = 4513625) B4513625
theorem B2006055 : Blo 2005435 2006055 := bstep (se 1 (by rfl) ⟨1504541, by rfl⟩ : syracuseStep 2006055 = 3009083) B3009083
theorem B2256817 : Blo 2005435 2256817 := bbase (se 2 (by rfl) ⟨846306, by rfl⟩ : syracuseStep 2256817 = 1692613) (by norm_num)
theorem B3009089 : Blo 2005435 3009089 := bstep (se 2 (by rfl) ⟨1128408, by rfl⟩ : syracuseStep 3009089 = 2256817) B2256817
theorem B2006059 : Blo 2005435 2006059 := bstep (se 1 (by rfl) ⟨1504544, by rfl⟩ : syracuseStep 2006059 = 3009089) B3009089
theorem B5712581 : Blo 2005435 5712581 := bbase (se 4 (by rfl) ⟨535554, by rfl⟩ : syracuseStep 5712581 = 1071109) (by norm_num)
theorem B3808387 : Blo 2005435 3808387 := bstep (se 1 (by rfl) ⟨2856290, by rfl⟩ : syracuseStep 3808387 = 5712581) B5712581
theorem B5077849 : Blo 2005435 5077849 := bstep (se 2 (by rfl) ⟨1904193, by rfl⟩ : syracuseStep 5077849 = 3808387) B3808387
theorem B6770465 : Blo 2005435 6770465 := bstep (se 2 (by rfl) ⟨2538924, by rfl⟩ : syracuseStep 6770465 = 5077849) B5077849
theorem B4513643 : Blo 2005435 4513643 := bstep (se 1 (by rfl) ⟨3385232, by rfl⟩ : syracuseStep 4513643 = 6770465) B6770465
theorem B3009095 : Blo 2005435 3009095 := bstep (se 1 (by rfl) ⟨2256821, by rfl⟩ : syracuseStep 3009095 = 4513643) B4513643
theorem B2006063 : Blo 2005435 2006063 := bstep (se 1 (by rfl) ⟨1504547, by rfl⟩ : syracuseStep 2006063 = 3009095) B3009095
theorem B3009101 : Blo 2005435 3009101 := bbase (se 3 (by rfl) ⟨564206, by rfl⟩ : syracuseStep 3009101 = 1128413) (by norm_num)
theorem B2006067 : Blo 2005435 2006067 := bstep (se 1 (by rfl) ⟨1504550, by rfl⟩ : syracuseStep 2006067 = 3009101) B3009101
theorem B4513661 : Blo 2005435 4513661 := bbase (se 3 (by rfl) ⟨846311, by rfl⟩ : syracuseStep 4513661 = 1692623) (by norm_num)
theorem B3009107 : Blo 2005435 3009107 := bstep (se 1 (by rfl) ⟨2256830, by rfl⟩ : syracuseStep 3009107 = 4513661) B4513661
theorem B2006071 : Blo 2005435 2006071 := bstep (se 1 (by rfl) ⟨1504553, by rfl⟩ : syracuseStep 2006071 = 3009107) B3009107
theorem B3385253 : Blo 2005435 3385253 := bbase (se 4 (by rfl) ⟨317367, by rfl⟩ : syracuseStep 3385253 = 634735) (by norm_num)
theorem B2256835 : Blo 2005435 2256835 := bstep (se 1 (by rfl) ⟨1692626, by rfl⟩ : syracuseStep 2256835 = 3385253) B3385253
theorem B3009113 : Blo 2005435 3009113 := bstep (se 2 (by rfl) ⟨1128417, by rfl⟩ : syracuseStep 3009113 = 2256835) B2256835
theorem B2006075 : Blo 2005435 2006075 := bstep (se 1 (by rfl) ⟨1504556, by rfl⟩ : syracuseStep 2006075 = 3009113) B3009113
theorem B5147173 : Blo 2005435 5147173 := bbase (se 4 (by rfl) ⟨482547, by rfl⟩ : syracuseStep 5147173 = 965095) (by norm_num)
theorem B6862897 : Blo 2005435 6862897 := bstep (se 2 (by rfl) ⟨2573586, by rfl⟩ : syracuseStep 6862897 = 5147173) B5147173
theorem B9150529 : Blo 2005435 9150529 := bstep (se 2 (by rfl) ⟨3431448, by rfl⟩ : syracuseStep 9150529 = 6862897) B6862897
theorem B12200705 : Blo 2005435 12200705 := bstep (se 2 (by rfl) ⟨4575264, by rfl⟩ : syracuseStep 12200705 = 9150529) B9150529
theorem B8133803 : Blo 2005435 8133803 := bstep (se 1 (by rfl) ⟨6100352, by rfl⟩ : syracuseStep 8133803 = 12200705) B12200705
theorem B5422535 : Blo 2005435 5422535 := bstep (se 1 (by rfl) ⟨4066901, by rfl⟩ : syracuseStep 5422535 = 8133803) B8133803
theorem B3615023 : Blo 2005435 3615023 := bstep (se 1 (by rfl) ⟨2711267, by rfl⟩ : syracuseStep 3615023 = 5422535) B5422535
theorem B2410015 : Blo 2005435 2410015 := bstep (se 1 (by rfl) ⟨1807511, by rfl⟩ : syracuseStep 2410015 = 3615023) B3615023
theorem B3213353 : Blo 2005435 3213353 := bstep (se 2 (by rfl) ⟨1205007, by rfl⟩ : syracuseStep 3213353 = 2410015) B2410015
theorem B2142235 : Blo 2005435 2142235 := bstep (se 1 (by rfl) ⟨1606676, by rfl⟩ : syracuseStep 2142235 = 3213353) B3213353
theorem B2856313 : Blo 2005435 2856313 := bstep (se 2 (by rfl) ⟨1071117, by rfl⟩ : syracuseStep 2856313 = 2142235) B2142235
theorem B15233669 : Blo 2005435 15233669 := bstep (se 4 (by rfl) ⟨1428156, by rfl⟩ : syracuseStep 15233669 = 2856313) B2856313
theorem B10155779 : Blo 2005435 10155779 := bstep (se 1 (by rfl) ⟨7616834, by rfl⟩ : syracuseStep 10155779 = 15233669) B15233669
theorem B6770519 : Blo 2005435 6770519 := bstep (se 1 (by rfl) ⟨5077889, by rfl⟩ : syracuseStep 6770519 = 10155779) B10155779
theorem B4513679 : Blo 2005435 4513679 := bstep (se 1 (by rfl) ⟨3385259, by rfl⟩ : syracuseStep 4513679 = 6770519) B6770519
theorem B3009119 : Blo 2005435 3009119 := bstep (se 1 (by rfl) ⟨2256839, by rfl⟩ : syracuseStep 3009119 = 4513679) B4513679
theorem B2006079 : Blo 2005435 2006079 := bstep (se 1 (by rfl) ⟨1504559, by rfl⟩ : syracuseStep 2006079 = 3009119) B3009119
theorem B3009125 : Blo 2005435 3009125 := bbase (se 4 (by rfl) ⟨282105, by rfl⟩ : syracuseStep 3009125 = 564211) (by norm_num)
theorem B2006083 : Blo 2005435 2006083 := bstep (se 1 (by rfl) ⟨1504562, by rfl⟩ : syracuseStep 2006083 = 3009125) B3009125
theorem B2856325 : Blo 2005435 2856325 := bbase (se 4 (by rfl) ⟨267780, by rfl⟩ : syracuseStep 2856325 = 535561) (by norm_num)
theorem B3808433 : Blo 2005435 3808433 := bstep (se 2 (by rfl) ⟨1428162, by rfl⟩ : syracuseStep 3808433 = 2856325) B2856325
theorem B2538955 : Blo 2005435 2538955 := bstep (se 1 (by rfl) ⟨1904216, by rfl⟩ : syracuseStep 2538955 = 3808433) B3808433
theorem B3385273 : Blo 2005435 3385273 := bstep (se 2 (by rfl) ⟨1269477, by rfl⟩ : syracuseStep 3385273 = 2538955) B2538955
theorem B4513697 : Blo 2005435 4513697 := bstep (se 2 (by rfl) ⟨1692636, by rfl⟩ : syracuseStep 4513697 = 3385273) B3385273
theorem B3009131 : Blo 2005435 3009131 := bstep (se 1 (by rfl) ⟨2256848, by rfl⟩ : syracuseStep 3009131 = 4513697) B4513697
theorem B2006087 : Blo 2005435 2006087 := bstep (se 1 (by rfl) ⟨1504565, by rfl⟩ : syracuseStep 2006087 = 3009131) B3009131
theorem B2256853 : Blo 2005435 2256853 := bbase (se 7 (by rfl) ⟨26447, by rfl⟩ : syracuseStep 2256853 = 52895) (by norm_num)
theorem B3009137 : Blo 2005435 3009137 := bstep (se 2 (by rfl) ⟨1128426, by rfl⟩ : syracuseStep 3009137 = 2256853) B2256853
theorem B2006091 : Blo 2005435 2006091 := bstep (se 1 (by rfl) ⟨1504568, by rfl⟩ : syracuseStep 2006091 = 3009137) B3009137
theorem B2538965 : Blo 2005435 2538965 := bbase (se 7 (by rfl) ⟨29753, by rfl⟩ : syracuseStep 2538965 = 59507) (by norm_num)
theorem B6770573 : Blo 2005435 6770573 := bstep (se 3 (by rfl) ⟨1269482, by rfl⟩ : syracuseStep 6770573 = 2538965) B2538965
theorem B4513715 : Blo 2005435 4513715 := bstep (se 1 (by rfl) ⟨3385286, by rfl⟩ : syracuseStep 4513715 = 6770573) B6770573
theorem B3009143 : Blo 2005435 3009143 := bstep (se 1 (by rfl) ⟨2256857, by rfl⟩ : syracuseStep 3009143 = 4513715) B4513715
theorem B2006095 : Blo 2005435 2006095 := bstep (se 1 (by rfl) ⟨1504571, by rfl⟩ : syracuseStep 2006095 = 3009143) B3009143
theorem B3009149 : Blo 2005435 3009149 := bbase (se 3 (by rfl) ⟨564215, by rfl⟩ : syracuseStep 3009149 = 1128431) (by norm_num)
theorem B2006099 : Blo 2005435 2006099 := bstep (se 1 (by rfl) ⟨1504574, by rfl⟩ : syracuseStep 2006099 = 3009149) B3009149
theorem B4513733 : Blo 2005435 4513733 := bbase (se 4 (by rfl) ⟨423162, by rfl⟩ : syracuseStep 4513733 = 846325) (by norm_num)
theorem B3009155 : Blo 2005435 3009155 := bstep (se 1 (by rfl) ⟨2256866, by rfl⟩ : syracuseStep 3009155 = 4513733) B4513733
theorem B2006103 : Blo 2005435 2006103 := bstep (se 1 (by rfl) ⟨1504577, by rfl⟩ : syracuseStep 2006103 = 3009155) B3009155
theorem B8569061 : Blo 2005435 8569061 := bbase (se 4 (by rfl) ⟨803349, by rfl⟩ : syracuseStep 8569061 = 1606699) (by norm_num)
theorem B5712707 : Blo 2005435 5712707 := bstep (se 1 (by rfl) ⟨4284530, by rfl⟩ : syracuseStep 5712707 = 8569061) B8569061
theorem B3808471 : Blo 2005435 3808471 := bstep (se 1 (by rfl) ⟨2856353, by rfl⟩ : syracuseStep 3808471 = 5712707) B5712707
theorem B5077961 : Blo 2005435 5077961 := bstep (se 2 (by rfl) ⟨1904235, by rfl⟩ : syracuseStep 5077961 = 3808471) B3808471
theorem B3385307 : Blo 2005435 3385307 := bstep (se 1 (by rfl) ⟨2538980, by rfl⟩ : syracuseStep 3385307 = 5077961) B5077961
theorem B2256871 : Blo 2005435 2256871 := bstep (se 1 (by rfl) ⟨1692653, by rfl⟩ : syracuseStep 2256871 = 3385307) B3385307
theorem B3009161 : Blo 2005435 3009161 := bstep (se 2 (by rfl) ⟨1128435, by rfl⟩ : syracuseStep 3009161 = 2256871) B2256871
theorem B2006107 : Blo 2005435 2006107 := bstep (se 1 (by rfl) ⟨1504580, by rfl⟩ : syracuseStep 2006107 = 3009161) B3009161
theorem B10155941 : Blo 2005435 10155941 := bbase (se 4 (by rfl) ⟨952119, by rfl⟩ : syracuseStep 10155941 = 1904239) (by norm_num)
theorem B6770627 : Blo 2005435 6770627 := bstep (se 1 (by rfl) ⟨5077970, by rfl⟩ : syracuseStep 6770627 = 10155941) B10155941
theorem B4513751 : Blo 2005435 4513751 := bstep (se 1 (by rfl) ⟨3385313, by rfl⟩ : syracuseStep 4513751 = 6770627) B6770627
theorem B3009167 : Blo 2005435 3009167 := bstep (se 1 (by rfl) ⟨2256875, by rfl⟩ : syracuseStep 3009167 = 4513751) B4513751
theorem B2006111 : Blo 2005435 2006111 := bstep (se 1 (by rfl) ⟨1504583, by rfl⟩ : syracuseStep 2006111 = 3009167) B3009167
theorem B3009173 : Blo 2005435 3009173 := bbase (se 6 (by rfl) ⟨70527, by rfl⟩ : syracuseStep 3009173 = 141055) (by norm_num)
theorem B2006115 : Blo 2005435 2006115 := bstep (se 1 (by rfl) ⟨1504586, by rfl⟩ : syracuseStep 2006115 = 3009173) B3009173
theorem B19280501 : Blo 2005435 19280501 := bbase (se 5 (by rfl) ⟨903773, by rfl⟩ : syracuseStep 19280501 = 1807547) (by norm_num)
theorem B12853667 : Blo 2005435 12853667 := bstep (se 1 (by rfl) ⟨9640250, by rfl⟩ : syracuseStep 12853667 = 19280501) B19280501
theorem B8569111 : Blo 2005435 8569111 := bstep (se 1 (by rfl) ⟨6426833, by rfl⟩ : syracuseStep 8569111 = 12853667) B12853667
theorem B11425481 : Blo 2005435 11425481 := bstep (se 2 (by rfl) ⟨4284555, by rfl⟩ : syracuseStep 11425481 = 8569111) B8569111
theorem B7616987 : Blo 2005435 7616987 := bstep (se 1 (by rfl) ⟨5712740, by rfl⟩ : syracuseStep 7616987 = 11425481) B11425481
theorem B5077991 : Blo 2005435 5077991 := bstep (se 1 (by rfl) ⟨3808493, by rfl⟩ : syracuseStep 5077991 = 7616987) B7616987
theorem B3385327 : Blo 2005435 3385327 := bstep (se 1 (by rfl) ⟨2538995, by rfl⟩ : syracuseStep 3385327 = 5077991) B5077991
theorem B4513769 : Blo 2005435 4513769 := bstep (se 2 (by rfl) ⟨1692663, by rfl⟩ : syracuseStep 4513769 = 3385327) B3385327
theorem B3009179 : Blo 2005435 3009179 := bstep (se 1 (by rfl) ⟨2256884, by rfl⟩ : syracuseStep 3009179 = 4513769) B4513769
theorem B2006119 : Blo 2005435 2006119 := bstep (se 1 (by rfl) ⟨1504589, by rfl⟩ : syracuseStep 2006119 = 3009179) B3009179
theorem B2256889 : Blo 2005435 2256889 := bbase (se 2 (by rfl) ⟨846333, by rfl⟩ : syracuseStep 2256889 = 1692667) (by norm_num)
theorem B3009185 : Blo 2005435 3009185 := bstep (se 2 (by rfl) ⟨1128444, by rfl⟩ : syracuseStep 3009185 = 2256889) B2256889
theorem B2006123 : Blo 2005435 2006123 := bstep (se 1 (by rfl) ⟨1504592, by rfl⟩ : syracuseStep 2006123 = 3009185) B3009185
theorem B2748325 : Blo 2005435 2748325 := bbase (se 4 (by rfl) ⟨257655, by rfl⟩ : syracuseStep 2748325 = 515311) (by norm_num)
theorem B3664433 : Blo 2005435 3664433 := bstep (se 2 (by rfl) ⟨1374162, by rfl⟩ : syracuseStep 3664433 = 2748325) B2748325
theorem B2442955 : Blo 2005435 2442955 := bstep (se 1 (by rfl) ⟨1832216, by rfl⟩ : syracuseStep 2442955 = 3664433) B3664433
theorem B3257273 : Blo 2005435 3257273 := bstep (se 2 (by rfl) ⟨1221477, by rfl⟩ : syracuseStep 3257273 = 2442955) B2442955
theorem B8686061 : Blo 2005435 8686061 := bstep (se 3 (by rfl) ⟨1628636, by rfl⟩ : syracuseStep 8686061 = 3257273) B3257273
theorem B5790707 : Blo 2005435 5790707 := bstep (se 1 (by rfl) ⟨4343030, by rfl⟩ : syracuseStep 5790707 = 8686061) B8686061
theorem B3860471 : Blo 2005435 3860471 := bstep (se 1 (by rfl) ⟨2895353, by rfl⟩ : syracuseStep 3860471 = 5790707) B5790707
theorem B10294589 : Blo 2005435 10294589 := bstep (se 3 (by rfl) ⟨1930235, by rfl⟩ : syracuseStep 10294589 = 3860471) B3860471
theorem B6863059 : Blo 2005435 6863059 := bstep (se 1 (by rfl) ⟨5147294, by rfl⟩ : syracuseStep 6863059 = 10294589) B10294589
theorem B9150745 : Blo 2005435 9150745 := bstep (se 2 (by rfl) ⟨3431529, by rfl⟩ : syracuseStep 9150745 = 6863059) B6863059
theorem B12200993 : Blo 2005435 12200993 := bstep (se 2 (by rfl) ⟨4575372, by rfl⟩ : syracuseStep 12200993 = 9150745) B9150745
theorem B8133995 : Blo 2005435 8133995 := bstep (se 1 (by rfl) ⟨6100496, by rfl⟩ : syracuseStep 8133995 = 12200993) B12200993
theorem B5422663 : Blo 2005435 5422663 := bstep (se 1 (by rfl) ⟨4066997, by rfl⟩ : syracuseStep 5422663 = 8133995) B8133995
theorem B7230217 : Blo 2005435 7230217 := bstep (se 2 (by rfl) ⟨2711331, by rfl⟩ : syracuseStep 7230217 = 5422663) B5422663
theorem B9640289 : Blo 2005435 9640289 := bstep (se 2 (by rfl) ⟨3615108, by rfl⟩ : syracuseStep 9640289 = 7230217) B7230217
theorem B6426859 : Blo 2005435 6426859 := bstep (se 1 (by rfl) ⟨4820144, by rfl⟩ : syracuseStep 6426859 = 9640289) B9640289
theorem B8569145 : Blo 2005435 8569145 := bstep (se 2 (by rfl) ⟨3213429, by rfl⟩ : syracuseStep 8569145 = 6426859) B6426859
theorem B5712763 : Blo 2005435 5712763 := bstep (se 1 (by rfl) ⟨4284572, by rfl⟩ : syracuseStep 5712763 = 8569145) B8569145
theorem B7617017 : Blo 2005435 7617017 := bstep (se 2 (by rfl) ⟨2856381, by rfl⟩ : syracuseStep 7617017 = 5712763) B5712763
theorem B5078011 : Blo 2005435 5078011 := bstep (se 1 (by rfl) ⟨3808508, by rfl⟩ : syracuseStep 5078011 = 7617017) B7617017
theorem B6770681 : Blo 2005435 6770681 := bstep (se 2 (by rfl) ⟨2539005, by rfl⟩ : syracuseStep 6770681 = 5078011) B5078011
theorem B4513787 : Blo 2005435 4513787 := bstep (se 1 (by rfl) ⟨3385340, by rfl⟩ : syracuseStep 4513787 = 6770681) B6770681
theorem B3009191 : Blo 2005435 3009191 := bstep (se 1 (by rfl) ⟨2256893, by rfl⟩ : syracuseStep 3009191 = 4513787) B4513787
theorem B2006127 : Blo 2005435 2006127 := bstep (se 1 (by rfl) ⟨1504595, by rfl⟩ : syracuseStep 2006127 = 3009191) B3009191
theorem B3009197 : Blo 2005435 3009197 := bbase (se 3 (by rfl) ⟨564224, by rfl⟩ : syracuseStep 3009197 = 1128449) (by norm_num)
theorem B2006131 : Blo 2005435 2006131 := bstep (se 1 (by rfl) ⟨1504598, by rfl⟩ : syracuseStep 2006131 = 3009197) B3009197
theorem B4513805 : Blo 2005435 4513805 := bbase (se 3 (by rfl) ⟨846338, by rfl⟩ : syracuseStep 4513805 = 1692677) (by norm_num)
theorem B3009203 : Blo 2005435 3009203 := bstep (se 1 (by rfl) ⟨2256902, by rfl⟩ : syracuseStep 3009203 = 4513805) B4513805
theorem B2006135 : Blo 2005435 2006135 := bstep (se 1 (by rfl) ⟨1504601, by rfl⟩ : syracuseStep 2006135 = 3009203) B3009203
theorem B2539021 : Blo 2005435 2539021 := bbase (se 3 (by rfl) ⟨476066, by rfl⟩ : syracuseStep 2539021 = 952133) (by norm_num)
theorem B3385361 : Blo 2005435 3385361 := bstep (se 2 (by rfl) ⟨1269510, by rfl⟩ : syracuseStep 3385361 = 2539021) B2539021
theorem B2256907 : Blo 2005435 2256907 := bstep (se 1 (by rfl) ⟨1692680, by rfl⟩ : syracuseStep 2256907 = 3385361) B3385361
theorem B3009209 : Blo 2005435 3009209 := bstep (se 2 (by rfl) ⟨1128453, by rfl⟩ : syracuseStep 3009209 = 2256907) B2256907
theorem B2006139 : Blo 2005435 2006139 := bstep (se 1 (by rfl) ⟨1504604, by rfl⟩ : syracuseStep 2006139 = 3009209) B3009209
theorem B4067029 : Blo 2005435 4067029 := bbase (se 7 (by rfl) ⟨47660, by rfl⟩ : syracuseStep 4067029 = 95321) (by norm_num)
theorem B21690821 : Blo 2005435 21690821 := bstep (se 4 (by rfl) ⟨2033514, by rfl⟩ : syracuseStep 21690821 = 4067029) B4067029
theorem B14460547 : Blo 2005435 14460547 := bstep (se 1 (by rfl) ⟨10845410, by rfl⟩ : syracuseStep 14460547 = 21690821) B21690821
theorem B19280729 : Blo 2005435 19280729 := bstep (se 2 (by rfl) ⟨7230273, by rfl⟩ : syracuseStep 19280729 = 14460547) B14460547
theorem B12853819 : Blo 2005435 12853819 := bstep (se 1 (by rfl) ⟨9640364, by rfl⟩ : syracuseStep 12853819 = 19280729) B19280729
theorem B17138425 : Blo 2005435 17138425 := bstep (se 2 (by rfl) ⟨6426909, by rfl⟩ : syracuseStep 17138425 = 12853819) B12853819
theorem B22851233 : Blo 2005435 22851233 := bstep (se 2 (by rfl) ⟨8569212, by rfl⟩ : syracuseStep 22851233 = 17138425) B17138425
theorem B15234155 : Blo 2005435 15234155 := bstep (se 1 (by rfl) ⟨11425616, by rfl⟩ : syracuseStep 15234155 = 22851233) B22851233
theorem B10156103 : Blo 2005435 10156103 := bstep (se 1 (by rfl) ⟨7617077, by rfl⟩ : syracuseStep 10156103 = 15234155) B15234155
theorem B6770735 : Blo 2005435 6770735 := bstep (se 1 (by rfl) ⟨5078051, by rfl⟩ : syracuseStep 6770735 = 10156103) B10156103
theorem B4513823 : Blo 2005435 4513823 := bstep (se 1 (by rfl) ⟨3385367, by rfl⟩ : syracuseStep 4513823 = 6770735) B6770735
theorem B3009215 : Blo 2005435 3009215 := bstep (se 1 (by rfl) ⟨2256911, by rfl⟩ : syracuseStep 3009215 = 4513823) B4513823
theorem B2006143 : Blo 2005435 2006143 := bstep (se 1 (by rfl) ⟨1504607, by rfl⟩ : syracuseStep 2006143 = 3009215) B3009215
theorem B3009221 : Blo 2005435 3009221 := bbase (se 4 (by rfl) ⟨282114, by rfl⟩ : syracuseStep 3009221 = 564229) (by norm_num)
theorem B2006147 : Blo 2005435 2006147 := bstep (se 1 (by rfl) ⟨1504610, by rfl⟩ : syracuseStep 2006147 = 3009221) B3009221
theorem B3385381 : Blo 2005435 3385381 := bbase (se 4 (by rfl) ⟨317379, by rfl⟩ : syracuseStep 3385381 = 634759) (by norm_num)
theorem B4513841 : Blo 2005435 4513841 := bstep (se 2 (by rfl) ⟨1692690, by rfl⟩ : syracuseStep 4513841 = 3385381) B3385381
theorem B3009227 : Blo 2005435 3009227 := bstep (se 1 (by rfl) ⟨2256920, by rfl⟩ : syracuseStep 3009227 = 4513841) B4513841
theorem B2006151 : Blo 2005435 2006151 := bstep (se 1 (by rfl) ⟨1504613, by rfl⟩ : syracuseStep 2006151 = 3009227) B3009227
theorem B2256925 : Blo 2005435 2256925 := bbase (se 3 (by rfl) ⟨423173, by rfl⟩ : syracuseStep 2256925 = 846347) (by norm_num)
theorem B3009233 : Blo 2005435 3009233 := bstep (se 2 (by rfl) ⟨1128462, by rfl⟩ : syracuseStep 3009233 = 2256925) B2256925
theorem B2006155 : Blo 2005435 2006155 := bstep (se 1 (by rfl) ⟨1504616, by rfl⟩ : syracuseStep 2006155 = 3009233) B3009233
theorem B6770789 : Blo 2005435 6770789 := bbase (se 4 (by rfl) ⟨634761, by rfl⟩ : syracuseStep 6770789 = 1269523) (by norm_num)
theorem B4513859 : Blo 2005435 4513859 := bstep (se 1 (by rfl) ⟨3385394, by rfl⟩ : syracuseStep 4513859 = 6770789) B6770789
theorem B3009239 : Blo 2005435 3009239 := bstep (se 1 (by rfl) ⟨2256929, by rfl⟩ : syracuseStep 3009239 = 4513859) B4513859
theorem B2006159 : Blo 2005435 2006159 := bstep (se 1 (by rfl) ⟨1504619, by rfl⟩ : syracuseStep 2006159 = 3009239) B3009239
theorem B3009245 : Blo 2005435 3009245 := bbase (se 3 (by rfl) ⟨564233, by rfl⟩ : syracuseStep 3009245 = 1128467) (by norm_num)
theorem B2006163 : Blo 2005435 2006163 := bstep (se 1 (by rfl) ⟨1504622, by rfl⟩ : syracuseStep 2006163 = 3009245) B3009245
theorem B4513877 : Blo 2005435 4513877 := bbase (se 8 (by rfl) ⟨26448, by rfl⟩ : syracuseStep 4513877 = 52897) (by norm_num)
theorem B3009251 : Blo 2005435 3009251 := bstep (se 1 (by rfl) ⟨2256938, by rfl⟩ : syracuseStep 3009251 = 4513877) B4513877
theorem B2006167 : Blo 2005435 2006167 := bstep (se 1 (by rfl) ⟨1504625, by rfl⟩ : syracuseStep 2006167 = 3009251) B3009251
theorem B3091933 : Blo 2005435 3091933 := bbase (se 3 (by rfl) ⟨579737, by rfl⟩ : syracuseStep 3091933 = 1159475) (by norm_num)
theorem B4122577 : Blo 2005435 4122577 := bstep (se 2 (by rfl) ⟨1545966, by rfl⟩ : syracuseStep 4122577 = 3091933) B3091933
theorem B5496769 : Blo 2005435 5496769 := bstep (se 2 (by rfl) ⟨2061288, by rfl⟩ : syracuseStep 5496769 = 4122577) B4122577
theorem B7329025 : Blo 2005435 7329025 := bstep (se 2 (by rfl) ⟨2748384, by rfl⟩ : syracuseStep 7329025 = 5496769) B5496769
theorem B39088133 : Blo 2005435 39088133 := bstep (se 4 (by rfl) ⟨3664512, by rfl⟩ : syracuseStep 39088133 = 7329025) B7329025
theorem B26058755 : Blo 2005435 26058755 := bstep (se 1 (by rfl) ⟨19544066, by rfl⟩ : syracuseStep 26058755 = 39088133) B39088133
theorem B17372503 : Blo 2005435 17372503 := bstep (se 1 (by rfl) ⟨13029377, by rfl⟩ : syracuseStep 17372503 = 26058755) B26058755
theorem B23163337 : Blo 2005435 23163337 := bstep (se 2 (by rfl) ⟨8686251, by rfl⟩ : syracuseStep 23163337 = 17372503) B17372503
theorem B30884449 : Blo 2005435 30884449 := bstep (se 2 (by rfl) ⟨11581668, by rfl⟩ : syracuseStep 30884449 = 23163337) B23163337
theorem B41179265 : Blo 2005435 41179265 := bstep (se 2 (by rfl) ⟨15442224, by rfl⟩ : syracuseStep 41179265 = 30884449) B30884449
theorem B27452843 : Blo 2005435 27452843 := bstep (se 1 (by rfl) ⟨20589632, by rfl⟩ : syracuseStep 27452843 = 41179265) B41179265
theorem B18301895 : Blo 2005435 18301895 := bstep (se 1 (by rfl) ⟨13726421, by rfl⟩ : syracuseStep 18301895 = 27452843) B27452843
theorem B12201263 : Blo 2005435 12201263 := bstep (se 1 (by rfl) ⟨9150947, by rfl⟩ : syracuseStep 12201263 = 18301895) B18301895
theorem B8134175 : Blo 2005435 8134175 := bstep (se 1 (by rfl) ⟨6100631, by rfl⟩ : syracuseStep 8134175 = 12201263) B12201263
theorem B5422783 : Blo 2005435 5422783 := bstep (se 1 (by rfl) ⟨4067087, by rfl⟩ : syracuseStep 5422783 = 8134175) B8134175
theorem B7230377 : Blo 2005435 7230377 := bstep (se 2 (by rfl) ⟨2711391, by rfl⟩ : syracuseStep 7230377 = 5422783) B5422783
theorem B4820251 : Blo 2005435 4820251 := bstep (se 1 (by rfl) ⟨3615188, by rfl⟩ : syracuseStep 4820251 = 7230377) B7230377
theorem B6427001 : Blo 2005435 6427001 := bstep (se 2 (by rfl) ⟨2410125, by rfl⟩ : syracuseStep 6427001 = 4820251) B4820251
theorem B4284667 : Blo 2005435 4284667 := bstep (se 1 (by rfl) ⟨3213500, by rfl⟩ : syracuseStep 4284667 = 6427001) B6427001
theorem B5712889 : Blo 2005435 5712889 := bstep (se 2 (by rfl) ⟨2142333, by rfl⟩ : syracuseStep 5712889 = 4284667) B4284667
theorem B7617185 : Blo 2005435 7617185 := bstep (se 2 (by rfl) ⟨2856444, by rfl⟩ : syracuseStep 7617185 = 5712889) B5712889
theorem B5078123 : Blo 2005435 5078123 := bstep (se 1 (by rfl) ⟨3808592, by rfl⟩ : syracuseStep 5078123 = 7617185) B7617185
theorem B3385415 : Blo 2005435 3385415 := bstep (se 1 (by rfl) ⟨2539061, by rfl⟩ : syracuseStep 3385415 = 5078123) B5078123
theorem B2256943 : Blo 2005435 2256943 := bstep (se 1 (by rfl) ⟨1692707, by rfl⟩ : syracuseStep 2256943 = 3385415) B3385415
theorem B3009257 : Blo 2005435 3009257 := bstep (se 2 (by rfl) ⟨1128471, by rfl⟩ : syracuseStep 3009257 = 2256943) B2256943
theorem B2006171 : Blo 2005435 2006171 := bstep (se 1 (by rfl) ⟨1504628, by rfl⟩ : syracuseStep 2006171 = 3009257) B3009257
theorem B7230389 : Blo 2005435 7230389 := bbase (se 5 (by rfl) ⟨338924, by rfl⟩ : syracuseStep 7230389 = 677849) (by norm_num)
theorem B19281037 : Blo 2005435 19281037 := bstep (se 3 (by rfl) ⟨3615194, by rfl⟩ : syracuseStep 19281037 = 7230389) B7230389
theorem B25708049 : Blo 2005435 25708049 := bstep (se 2 (by rfl) ⟨9640518, by rfl⟩ : syracuseStep 25708049 = 19281037) B19281037
theorem B17138699 : Blo 2005435 17138699 := bstep (se 1 (by rfl) ⟨12854024, by rfl⟩ : syracuseStep 17138699 = 25708049) B25708049
theorem B11425799 : Blo 2005435 11425799 := bstep (se 1 (by rfl) ⟨8569349, by rfl⟩ : syracuseStep 11425799 = 17138699) B17138699
theorem B7617199 : Blo 2005435 7617199 := bstep (se 1 (by rfl) ⟨5712899, by rfl⟩ : syracuseStep 7617199 = 11425799) B11425799
theorem B10156265 : Blo 2005435 10156265 := bstep (se 2 (by rfl) ⟨3808599, by rfl⟩ : syracuseStep 10156265 = 7617199) B7617199
theorem B6770843 : Blo 2005435 6770843 := bstep (se 1 (by rfl) ⟨5078132, by rfl⟩ : syracuseStep 6770843 = 10156265) B10156265
theorem B4513895 : Blo 2005435 4513895 := bstep (se 1 (by rfl) ⟨3385421, by rfl⟩ : syracuseStep 4513895 = 6770843) B6770843
theorem B3009263 : Blo 2005435 3009263 := bstep (se 1 (by rfl) ⟨2256947, by rfl⟩ : syracuseStep 3009263 = 4513895) B4513895
theorem B2006175 : Blo 2005435 2006175 := bstep (se 1 (by rfl) ⟨1504631, by rfl⟩ : syracuseStep 2006175 = 3009263) B3009263
theorem B3009269 : Blo 2005435 3009269 := bbase (se 5 (by rfl) ⟨141059, by rfl⟩ : syracuseStep 3009269 = 282119) (by norm_num)
theorem B2006179 : Blo 2005435 2006179 := bstep (se 1 (by rfl) ⟨1504634, by rfl⟩ : syracuseStep 2006179 = 3009269) B3009269
theorem B3478445 : Blo 2005435 3478445 := bbase (se 3 (by rfl) ⟨652208, by rfl⟩ : syracuseStep 3478445 = 1304417) (by norm_num)
theorem B2318963 : Blo 2005435 2318963 := bstep (se 1 (by rfl) ⟨1739222, by rfl⟩ : syracuseStep 2318963 = 3478445) B3478445
theorem B6183901 : Blo 2005435 6183901 := bstep (se 3 (by rfl) ⟨1159481, by rfl⟩ : syracuseStep 6183901 = 2318963) B2318963
theorem B8245201 : Blo 2005435 8245201 := bstep (se 2 (by rfl) ⟨3091950, by rfl⟩ : syracuseStep 8245201 = 6183901) B6183901
theorem B10993601 : Blo 2005435 10993601 := bstep (se 2 (by rfl) ⟨4122600, by rfl⟩ : syracuseStep 10993601 = 8245201) B8245201
theorem B29316269 : Blo 2005435 29316269 := bstep (se 3 (by rfl) ⟨5496800, by rfl⟩ : syracuseStep 29316269 = 10993601) B10993601
theorem B19544179 : Blo 2005435 19544179 := bstep (se 1 (by rfl) ⟨14658134, by rfl⟩ : syracuseStep 19544179 = 29316269) B29316269
theorem B26058905 : Blo 2005435 26058905 := bstep (se 2 (by rfl) ⟨9772089, by rfl⟩ : syracuseStep 26058905 = 19544179) B19544179
theorem B17372603 : Blo 2005435 17372603 := bstep (se 1 (by rfl) ⟨13029452, by rfl⟩ : syracuseStep 17372603 = 26058905) B26058905
theorem B46326941 : Blo 2005435 46326941 := bstep (se 3 (by rfl) ⟨8686301, by rfl⟩ : syracuseStep 46326941 = 17372603) B17372603
theorem B30884627 : Blo 2005435 30884627 := bstep (se 1 (by rfl) ⟨23163470, by rfl⟩ : syracuseStep 30884627 = 46326941) B46326941
theorem B20589751 : Blo 2005435 20589751 := bstep (se 1 (by rfl) ⟨15442313, by rfl⟩ : syracuseStep 20589751 = 30884627) B30884627
theorem B27453001 : Blo 2005435 27453001 := bstep (se 2 (by rfl) ⟨10294875, by rfl⟩ : syracuseStep 27453001 = 20589751) B20589751
theorem B36604001 : Blo 2005435 36604001 := bstep (se 2 (by rfl) ⟨13726500, by rfl⟩ : syracuseStep 36604001 = 27453001) B27453001
theorem B24402667 : Blo 2005435 24402667 := bstep (se 1 (by rfl) ⟨18302000, by rfl⟩ : syracuseStep 24402667 = 36604001) B36604001
theorem B32536889 : Blo 2005435 32536889 := bstep (se 2 (by rfl) ⟨12201333, by rfl⟩ : syracuseStep 32536889 = 24402667) B24402667
theorem B21691259 : Blo 2005435 21691259 := bstep (se 1 (by rfl) ⟨16268444, by rfl⟩ : syracuseStep 21691259 = 32536889) B32536889
theorem B14460839 : Blo 2005435 14460839 := bstep (se 1 (by rfl) ⟨10845629, by rfl⟩ : syracuseStep 14460839 = 21691259) B21691259
theorem B9640559 : Blo 2005435 9640559 := bstep (se 1 (by rfl) ⟨7230419, by rfl⟩ : syracuseStep 9640559 = 14460839) B14460839
theorem B6427039 : Blo 2005435 6427039 := bstep (se 1 (by rfl) ⟨4820279, by rfl⟩ : syracuseStep 6427039 = 9640559) B9640559
theorem B8569385 : Blo 2005435 8569385 := bstep (se 2 (by rfl) ⟨3213519, by rfl⟩ : syracuseStep 8569385 = 6427039) B6427039
theorem B5712923 : Blo 2005435 5712923 := bstep (se 1 (by rfl) ⟨4284692, by rfl⟩ : syracuseStep 5712923 = 8569385) B8569385
theorem B3808615 : Blo 2005435 3808615 := bstep (se 1 (by rfl) ⟨2856461, by rfl⟩ : syracuseStep 3808615 = 5712923) B5712923
theorem B5078153 : Blo 2005435 5078153 := bstep (se 2 (by rfl) ⟨1904307, by rfl⟩ : syracuseStep 5078153 = 3808615) B3808615
theorem B3385435 : Blo 2005435 3385435 := bstep (se 1 (by rfl) ⟨2539076, by rfl⟩ : syracuseStep 3385435 = 5078153) B5078153
theorem B4513913 : Blo 2005435 4513913 := bstep (se 2 (by rfl) ⟨1692717, by rfl⟩ : syracuseStep 4513913 = 3385435) B3385435
theorem B3009275 : Blo 2005435 3009275 := bstep (se 1 (by rfl) ⟨2256956, by rfl⟩ : syracuseStep 3009275 = 4513913) B4513913
theorem B2006183 : Blo 2005435 2006183 := bstep (se 1 (by rfl) ⟨1504637, by rfl⟩ : syracuseStep 2006183 = 3009275) B3009275
theorem B2256961 : Blo 2005435 2256961 := bbase (se 2 (by rfl) ⟨846360, by rfl⟩ : syracuseStep 2256961 = 1692721) (by norm_num)
theorem B3009281 : Blo 2005435 3009281 := bstep (se 2 (by rfl) ⟨1128480, by rfl⟩ : syracuseStep 3009281 = 2256961) B2256961
theorem B2006187 : Blo 2005435 2006187 := bstep (se 1 (by rfl) ⟨1504640, by rfl⟩ : syracuseStep 2006187 = 3009281) B3009281
theorem B5078173 : Blo 2005435 5078173 := bbase (se 3 (by rfl) ⟨952157, by rfl⟩ : syracuseStep 5078173 = 1904315) (by norm_num)
theorem B6770897 : Blo 2005435 6770897 := bstep (se 2 (by rfl) ⟨2539086, by rfl⟩ : syracuseStep 6770897 = 5078173) B5078173
theorem B4513931 : Blo 2005435 4513931 := bstep (se 1 (by rfl) ⟨3385448, by rfl⟩ : syracuseStep 4513931 = 6770897) B6770897
theorem B3009287 : Blo 2005435 3009287 := bstep (se 1 (by rfl) ⟨2256965, by rfl⟩ : syracuseStep 3009287 = 4513931) B4513931
theorem B2006191 : Blo 2005435 2006191 := bstep (se 1 (by rfl) ⟨1504643, by rfl⟩ : syracuseStep 2006191 = 3009287) B3009287
theorem B3009293 : Blo 2005435 3009293 := bbase (se 3 (by rfl) ⟨564242, by rfl⟩ : syracuseStep 3009293 = 1128485) (by norm_num)
theorem B2006195 : Blo 2005435 2006195 := bstep (se 1 (by rfl) ⟨1504646, by rfl⟩ : syracuseStep 2006195 = 3009293) B3009293
theorem B4513949 : Blo 2005435 4513949 := bbase (se 3 (by rfl) ⟨846365, by rfl⟩ : syracuseStep 4513949 = 1692731) (by norm_num)
theorem B3009299 : Blo 2005435 3009299 := bstep (se 1 (by rfl) ⟨2256974, by rfl⟩ : syracuseStep 3009299 = 4513949) B4513949
theorem B2006199 : Blo 2005435 2006199 := bstep (se 1 (by rfl) ⟨1504649, by rfl⟩ : syracuseStep 2006199 = 3009299) B3009299
theorem B3385469 : Blo 2005435 3385469 := bbase (se 3 (by rfl) ⟨634775, by rfl⟩ : syracuseStep 3385469 = 1269551) (by norm_num)
theorem B2256979 : Blo 2005435 2256979 := bstep (se 1 (by rfl) ⟨1692734, by rfl⟩ : syracuseStep 2256979 = 3385469) B3385469
theorem B3009305 : Blo 2005435 3009305 := bstep (se 2 (by rfl) ⟨1128489, by rfl⟩ : syracuseStep 3009305 = 2256979) B2256979
theorem B2006203 : Blo 2005435 2006203 := bstep (se 1 (by rfl) ⟨1504652, by rfl⟩ : syracuseStep 2006203 = 3009305) B3009305
theorem B6514805 : Blo 2005435 6514805 := bbase (se 5 (by rfl) ⟨305381, by rfl⟩ : syracuseStep 6514805 = 610763) (by norm_num)
theorem B4343203 : Blo 2005435 4343203 := bstep (se 1 (by rfl) ⟨3257402, by rfl⟩ : syracuseStep 4343203 = 6514805) B6514805
theorem B5790937 : Blo 2005435 5790937 := bstep (se 2 (by rfl) ⟨2171601, by rfl⟩ : syracuseStep 5790937 = 4343203) B4343203
theorem B7721249 : Blo 2005435 7721249 := bstep (se 2 (by rfl) ⟨2895468, by rfl⟩ : syracuseStep 7721249 = 5790937) B5790937
theorem B20589997 : Blo 2005435 20589997 := bstep (se 3 (by rfl) ⟨3860624, by rfl⟩ : syracuseStep 20589997 = 7721249) B7721249
theorem B27453329 : Blo 2005435 27453329 := bstep (se 2 (by rfl) ⟨10294998, by rfl⟩ : syracuseStep 27453329 = 20589997) B20589997
theorem B18302219 : Blo 2005435 18302219 := bstep (se 1 (by rfl) ⟨13726664, by rfl⟩ : syracuseStep 18302219 = 27453329) B27453329
theorem B12201479 : Blo 2005435 12201479 := bstep (se 1 (by rfl) ⟨9151109, by rfl⟩ : syracuseStep 12201479 = 18302219) B18302219
theorem B8134319 : Blo 2005435 8134319 := bstep (se 1 (by rfl) ⟨6100739, by rfl⟩ : syracuseStep 8134319 = 12201479) B12201479
theorem B5422879 : Blo 2005435 5422879 := bstep (se 1 (by rfl) ⟨4067159, by rfl⟩ : syracuseStep 5422879 = 8134319) B8134319
theorem B7230505 : Blo 2005435 7230505 := bstep (se 2 (by rfl) ⟨2711439, by rfl⟩ : syracuseStep 7230505 = 5422879) B5422879
theorem B9640673 : Blo 2005435 9640673 := bstep (se 2 (by rfl) ⟨3615252, by rfl⟩ : syracuseStep 9640673 = 7230505) B7230505
theorem B6427115 : Blo 2005435 6427115 := bstep (se 1 (by rfl) ⟨4820336, by rfl⟩ : syracuseStep 6427115 = 9640673) B9640673
theorem B4284743 : Blo 2005435 4284743 := bstep (se 1 (by rfl) ⟨3213557, by rfl⟩ : syracuseStep 4284743 = 6427115) B6427115
theorem B11425981 : Blo 2005435 11425981 := bstep (se 3 (by rfl) ⟨2142371, by rfl⟩ : syracuseStep 11425981 = 4284743) B4284743
theorem B15234641 : Blo 2005435 15234641 := bstep (se 2 (by rfl) ⟨5712990, by rfl⟩ : syracuseStep 15234641 = 11425981) B11425981
theorem B10156427 : Blo 2005435 10156427 := bstep (se 1 (by rfl) ⟨7617320, by rfl⟩ : syracuseStep 10156427 = 15234641) B15234641
theorem B6770951 : Blo 2005435 6770951 := bstep (se 1 (by rfl) ⟨5078213, by rfl⟩ : syracuseStep 6770951 = 10156427) B10156427
theorem B4513967 : Blo 2005435 4513967 := bstep (se 1 (by rfl) ⟨3385475, by rfl⟩ : syracuseStep 4513967 = 6770951) B6770951
theorem B3009311 : Blo 2005435 3009311 := bstep (se 1 (by rfl) ⟨2256983, by rfl⟩ : syracuseStep 3009311 = 4513967) B4513967
theorem B2006207 : Blo 2005435 2006207 := bstep (se 1 (by rfl) ⟨1504655, by rfl⟩ : syracuseStep 2006207 = 3009311) B3009311
theorem B3009317 : Blo 2005435 3009317 := bbase (se 4 (by rfl) ⟨282123, by rfl⟩ : syracuseStep 3009317 = 564247) (by norm_num)
theorem B2006211 : Blo 2005435 2006211 := bstep (se 1 (by rfl) ⟨1504658, by rfl⟩ : syracuseStep 2006211 = 3009317) B3009317
theorem B2539117 : Blo 2005435 2539117 := bbase (se 3 (by rfl) ⟨476084, by rfl⟩ : syracuseStep 2539117 = 952169) (by norm_num)
theorem B3385489 : Blo 2005435 3385489 := bstep (se 2 (by rfl) ⟨1269558, by rfl⟩ : syracuseStep 3385489 = 2539117) B2539117
theorem B4513985 : Blo 2005435 4513985 := bstep (se 2 (by rfl) ⟨1692744, by rfl⟩ : syracuseStep 4513985 = 3385489) B3385489
theorem B3009323 : Blo 2005435 3009323 := bstep (se 1 (by rfl) ⟨2256992, by rfl⟩ : syracuseStep 3009323 = 4513985) B4513985
theorem B2006215 : Blo 2005435 2006215 := bstep (se 1 (by rfl) ⟨1504661, by rfl⟩ : syracuseStep 2006215 = 3009323) B3009323
theorem B2256997 : Blo 2005435 2256997 := bbase (se 4 (by rfl) ⟨211593, by rfl⟩ : syracuseStep 2256997 = 423187) (by norm_num)
theorem B3009329 : Blo 2005435 3009329 := bstep (se 2 (by rfl) ⟨1128498, by rfl⟩ : syracuseStep 3009329 = 2256997) B2256997
theorem B2006219 : Blo 2005435 2006219 := bstep (se 1 (by rfl) ⟨1504664, by rfl⟩ : syracuseStep 2006219 = 3009329) B3009329
theorem B2142389 : Blo 2005435 2142389 := bbase (se 5 (by rfl) ⟨100424, by rfl⟩ : syracuseStep 2142389 = 200849) (by norm_num)
theorem B5713037 : Blo 2005435 5713037 := bstep (se 3 (by rfl) ⟨1071194, by rfl⟩ : syracuseStep 5713037 = 2142389) B2142389
theorem B3808691 : Blo 2005435 3808691 := bstep (se 1 (by rfl) ⟨2856518, by rfl⟩ : syracuseStep 3808691 = 5713037) B5713037
theorem B2539127 : Blo 2005435 2539127 := bstep (se 1 (by rfl) ⟨1904345, by rfl⟩ : syracuseStep 2539127 = 3808691) B3808691
theorem B6771005 : Blo 2005435 6771005 := bstep (se 3 (by rfl) ⟨1269563, by rfl⟩ : syracuseStep 6771005 = 2539127) B2539127
theorem B4514003 : Blo 2005435 4514003 := bstep (se 1 (by rfl) ⟨3385502, by rfl⟩ : syracuseStep 4514003 = 6771005) B6771005
theorem B3009335 : Blo 2005435 3009335 := bstep (se 1 (by rfl) ⟨2257001, by rfl⟩ : syracuseStep 3009335 = 4514003) B4514003
theorem B2006223 : Blo 2005435 2006223 := bstep (se 1 (by rfl) ⟨1504667, by rfl⟩ : syracuseStep 2006223 = 3009335) B3009335
theorem B3009341 : Blo 2005435 3009341 := bbase (se 3 (by rfl) ⟨564251, by rfl⟩ : syracuseStep 3009341 = 1128503) (by norm_num)
theorem B2006227 : Blo 2005435 2006227 := bstep (se 1 (by rfl) ⟨1504670, by rfl⟩ : syracuseStep 2006227 = 3009341) B3009341
theorem B4514021 : Blo 2005435 4514021 := bbase (se 4 (by rfl) ⟨423189, by rfl⟩ : syracuseStep 4514021 = 846379) (by norm_num)
theorem B3009347 : Blo 2005435 3009347 := bstep (se 1 (by rfl) ⟨2257010, by rfl⟩ : syracuseStep 3009347 = 4514021) B4514021
theorem B2006231 : Blo 2005435 2006231 := bstep (se 1 (by rfl) ⟨1504673, by rfl⟩ : syracuseStep 2006231 = 3009347) B3009347
theorem B5078285 : Blo 2005435 5078285 := bbase (se 3 (by rfl) ⟨952178, by rfl⟩ : syracuseStep 5078285 = 1904357) (by norm_num)
theorem B3385523 : Blo 2005435 3385523 := bstep (se 1 (by rfl) ⟨2539142, by rfl⟩ : syracuseStep 3385523 = 5078285) B5078285
theorem B2257015 : Blo 2005435 2257015 := bstep (se 1 (by rfl) ⟨1692761, by rfl⟩ : syracuseStep 2257015 = 3385523) B3385523
theorem B3009353 : Blo 2005435 3009353 := bstep (se 2 (by rfl) ⟨1128507, by rfl⟩ : syracuseStep 3009353 = 2257015) B2257015
theorem B2006235 : Blo 2005435 2006235 := bstep (se 1 (by rfl) ⟨1504676, by rfl⟩ : syracuseStep 2006235 = 3009353) B3009353
theorem B2856541 : Blo 2005435 2856541 := bbase (se 3 (by rfl) ⟨535601, by rfl⟩ : syracuseStep 2856541 = 1071203) (by norm_num)
theorem B3808721 : Blo 2005435 3808721 := bstep (se 2 (by rfl) ⟨1428270, by rfl⟩ : syracuseStep 3808721 = 2856541) B2856541
theorem B10156589 : Blo 2005435 10156589 := bstep (se 3 (by rfl) ⟨1904360, by rfl⟩ : syracuseStep 10156589 = 3808721) B3808721
theorem B6771059 : Blo 2005435 6771059 := bstep (se 1 (by rfl) ⟨5078294, by rfl⟩ : syracuseStep 6771059 = 10156589) B10156589
theorem B4514039 : Blo 2005435 4514039 := bstep (se 1 (by rfl) ⟨3385529, by rfl⟩ : syracuseStep 4514039 = 6771059) B6771059
theorem B3009359 : Blo 2005435 3009359 := bstep (se 1 (by rfl) ⟨2257019, by rfl⟩ : syracuseStep 3009359 = 4514039) B4514039
theorem B2006239 : Blo 2005435 2006239 := bstep (se 1 (by rfl) ⟨1504679, by rfl⟩ : syracuseStep 2006239 = 3009359) B3009359
theorem B3009365 : Blo 2005435 3009365 := bbase (se 9 (by rfl) ⟨8816, by rfl⟩ : syracuseStep 3009365 = 17633) (by norm_num)
theorem B2006243 : Blo 2005435 2006243 := bstep (se 1 (by rfl) ⟨1504682, by rfl⟩ : syracuseStep 2006243 = 3009365) B3009365
theorem B4284829 : Blo 2005435 4284829 := bbase (se 3 (by rfl) ⟨803405, by rfl⟩ : syracuseStep 4284829 = 1606811) (by norm_num)
theorem B5713105 : Blo 2005435 5713105 := bstep (se 2 (by rfl) ⟨2142414, by rfl⟩ : syracuseStep 5713105 = 4284829) B4284829
theorem B7617473 : Blo 2005435 7617473 := bstep (se 2 (by rfl) ⟨2856552, by rfl⟩ : syracuseStep 7617473 = 5713105) B5713105
theorem B5078315 : Blo 2005435 5078315 := bstep (se 1 (by rfl) ⟨3808736, by rfl⟩ : syracuseStep 5078315 = 7617473) B7617473
theorem B3385543 : Blo 2005435 3385543 := bstep (se 1 (by rfl) ⟨2539157, by rfl⟩ : syracuseStep 3385543 = 5078315) B5078315
theorem B4514057 : Blo 2005435 4514057 := bstep (se 2 (by rfl) ⟨1692771, by rfl⟩ : syracuseStep 4514057 = 3385543) B3385543
theorem B3009371 : Blo 2005435 3009371 := bstep (se 1 (by rfl) ⟨2257028, by rfl⟩ : syracuseStep 3009371 = 4514057) B4514057
theorem B2006247 : Blo 2005435 2006247 := bstep (se 1 (by rfl) ⟨1504685, by rfl⟩ : syracuseStep 2006247 = 3009371) B3009371
theorem B2257033 : Blo 2005435 2257033 := bbase (se 2 (by rfl) ⟨846387, by rfl⟩ : syracuseStep 2257033 = 1692775) (by norm_num)
theorem B3009377 : Blo 2005435 3009377 := bstep (se 2 (by rfl) ⟨1128516, by rfl⟩ : syracuseStep 3009377 = 2257033) B2257033
theorem B2006251 : Blo 2005435 2006251 := bstep (se 1 (by rfl) ⟨1504688, by rfl⟩ : syracuseStep 2006251 = 3009377) B3009377
theorem B2171653 : Blo 2005435 2171653 := bbase (se 4 (by rfl) ⟨203592, by rfl⟩ : syracuseStep 2171653 = 407185) (by norm_num)
theorem B46328597 : Blo 2005435 46328597 := bstep (se 6 (by rfl) ⟨1085826, by rfl⟩ : syracuseStep 46328597 = 2171653) B2171653
theorem B30885731 : Blo 2005435 30885731 := bstep (se 1 (by rfl) ⟨23164298, by rfl⟩ : syracuseStep 30885731 = 46328597) B46328597
theorem B20590487 : Blo 2005435 20590487 := bstep (se 1 (by rfl) ⟨15442865, by rfl⟩ : syracuseStep 20590487 = 30885731) B30885731
theorem B13726991 : Blo 2005435 13726991 := bstep (se 1 (by rfl) ⟨10295243, by rfl⟩ : syracuseStep 13726991 = 20590487) B20590487
theorem B9151327 : Blo 2005435 9151327 := bstep (se 1 (by rfl) ⟨6863495, by rfl⟩ : syracuseStep 9151327 = 13726991) B13726991
theorem B12201769 : Blo 2005435 12201769 := bstep (se 2 (by rfl) ⟨4575663, by rfl⟩ : syracuseStep 12201769 = 9151327) B9151327
theorem B16269025 : Blo 2005435 16269025 := bstep (se 2 (by rfl) ⟨6100884, by rfl⟩ : syracuseStep 16269025 = 12201769) B12201769
theorem B21692033 : Blo 2005435 21692033 := bstep (se 2 (by rfl) ⟨8134512, by rfl⟩ : syracuseStep 21692033 = 16269025) B16269025
theorem B14461355 : Blo 2005435 14461355 := bstep (se 1 (by rfl) ⟨10846016, by rfl⟩ : syracuseStep 14461355 = 21692033) B21692033
theorem B38563613 : Blo 2005435 38563613 := bstep (se 3 (by rfl) ⟨7230677, by rfl⟩ : syracuseStep 38563613 = 14461355) B14461355
theorem B25709075 : Blo 2005435 25709075 := bstep (se 1 (by rfl) ⟨19281806, by rfl⟩ : syracuseStep 25709075 = 38563613) B38563613
theorem B17139383 : Blo 2005435 17139383 := bstep (se 1 (by rfl) ⟨12854537, by rfl⟩ : syracuseStep 17139383 = 25709075) B25709075
theorem B11426255 : Blo 2005435 11426255 := bstep (se 1 (by rfl) ⟨8569691, by rfl⟩ : syracuseStep 11426255 = 17139383) B17139383
theorem B7617503 : Blo 2005435 7617503 := bstep (se 1 (by rfl) ⟨5713127, by rfl⟩ : syracuseStep 7617503 = 11426255) B11426255
theorem B5078335 : Blo 2005435 5078335 := bstep (se 1 (by rfl) ⟨3808751, by rfl⟩ : syracuseStep 5078335 = 7617503) B7617503
theorem B6771113 : Blo 2005435 6771113 := bstep (se 2 (by rfl) ⟨2539167, by rfl⟩ : syracuseStep 6771113 = 5078335) B5078335
theorem B4514075 : Blo 2005435 4514075 := bstep (se 1 (by rfl) ⟨3385556, by rfl⟩ : syracuseStep 4514075 = 6771113) B6771113
theorem B3009383 : Blo 2005435 3009383 := bstep (se 1 (by rfl) ⟨2257037, by rfl⟩ : syracuseStep 3009383 = 4514075) B4514075
theorem B2006255 : Blo 2005435 2006255 := bstep (se 1 (by rfl) ⟨1504691, by rfl⟩ : syracuseStep 2006255 = 3009383) B3009383
theorem B3009389 : Blo 2005435 3009389 := bbase (se 3 (by rfl) ⟨564260, by rfl⟩ : syracuseStep 3009389 = 1128521) (by norm_num)
theorem B2006259 : Blo 2005435 2006259 := bstep (se 1 (by rfl) ⟨1504694, by rfl⟩ : syracuseStep 2006259 = 3009389) B3009389
theorem B4514093 : Blo 2005435 4514093 := bbase (se 3 (by rfl) ⟨846392, by rfl⟩ : syracuseStep 4514093 = 1692785) (by norm_num)
theorem B3009395 : Blo 2005435 3009395 := bstep (se 1 (by rfl) ⟨2257046, by rfl⟩ : syracuseStep 3009395 = 4514093) B4514093
theorem B2006263 : Blo 2005435 2006263 := bstep (se 1 (by rfl) ⟨1504697, by rfl⟩ : syracuseStep 2006263 = 3009395) B3009395
theorem B2410241 : Blo 2005435 2410241 := bbase (se 2 (by rfl) ⟨903840, by rfl⟩ : syracuseStep 2410241 = 1807681) (by norm_num)
theorem B6427309 : Blo 2005435 6427309 := bstep (se 3 (by rfl) ⟨1205120, by rfl⟩ : syracuseStep 6427309 = 2410241) B2410241
theorem B8569745 : Blo 2005435 8569745 := bstep (se 2 (by rfl) ⟨3213654, by rfl⟩ : syracuseStep 8569745 = 6427309) B6427309
theorem B5713163 : Blo 2005435 5713163 := bstep (se 1 (by rfl) ⟨4284872, by rfl⟩ : syracuseStep 5713163 = 8569745) B8569745
theorem B3808775 : Blo 2005435 3808775 := bstep (se 1 (by rfl) ⟨2856581, by rfl⟩ : syracuseStep 3808775 = 5713163) B5713163
theorem B2539183 : Blo 2005435 2539183 := bstep (se 1 (by rfl) ⟨1904387, by rfl⟩ : syracuseStep 2539183 = 3808775) B3808775
theorem B3385577 : Blo 2005435 3385577 := bstep (se 2 (by rfl) ⟨1269591, by rfl⟩ : syracuseStep 3385577 = 2539183) B2539183
theorem B2257051 : Blo 2005435 2257051 := bstep (se 1 (by rfl) ⟨1692788, by rfl⟩ : syracuseStep 2257051 = 3385577) B3385577
theorem B3009401 : Blo 2005435 3009401 := bstep (se 2 (by rfl) ⟨1128525, by rfl⟩ : syracuseStep 3009401 = 2257051) B2257051
theorem B2006267 : Blo 2005435 2006267 := bstep (se 1 (by rfl) ⟨1504700, by rfl⟩ : syracuseStep 2006267 = 3009401) B3009401
theorem B2443129 : Blo 2005435 2443129 := bbase (se 2 (by rfl) ⟨916173, by rfl⟩ : syracuseStep 2443129 = 1832347) (by norm_num)
theorem B13030021 : Blo 2005435 13030021 := bstep (se 4 (by rfl) ⟨1221564, by rfl⟩ : syracuseStep 13030021 = 2443129) B2443129
theorem B17373361 : Blo 2005435 17373361 := bstep (se 2 (by rfl) ⟨6515010, by rfl⟩ : syracuseStep 17373361 = 13030021) B13030021
theorem B23164481 : Blo 2005435 23164481 := bstep (se 2 (by rfl) ⟨8686680, by rfl⟩ : syracuseStep 23164481 = 17373361) B17373361
theorem B15442987 : Blo 2005435 15442987 := bstep (se 1 (by rfl) ⟨11582240, by rfl⟩ : syracuseStep 15442987 = 23164481) B23164481
theorem B20590649 : Blo 2005435 20590649 := bstep (se 2 (by rfl) ⟨7721493, by rfl⟩ : syracuseStep 20590649 = 15442987) B15442987
theorem B13727099 : Blo 2005435 13727099 := bstep (se 1 (by rfl) ⟨10295324, by rfl⟩ : syracuseStep 13727099 = 20590649) B20590649
theorem B9151399 : Blo 2005435 9151399 := bstep (se 1 (by rfl) ⟨6863549, by rfl⟩ : syracuseStep 9151399 = 13727099) B13727099
theorem B48807461 : Blo 2005435 48807461 := bstep (se 4 (by rfl) ⟨4575699, by rfl⟩ : syracuseStep 48807461 = 9151399) B9151399
theorem B32538307 : Blo 2005435 32538307 := bstep (se 1 (by rfl) ⟨24403730, by rfl⟩ : syracuseStep 32538307 = 48807461) B48807461
theorem B43384409 : Blo 2005435 43384409 := bstep (se 2 (by rfl) ⟨16269153, by rfl⟩ : syracuseStep 43384409 = 32538307) B32538307
theorem B28922939 : Blo 2005435 28922939 := bstep (se 1 (by rfl) ⟨21692204, by rfl⟩ : syracuseStep 28922939 = 43384409) B43384409
theorem B19281959 : Blo 2005435 19281959 := bstep (se 1 (by rfl) ⟨14461469, by rfl⟩ : syracuseStep 19281959 = 28922939) B28922939
theorem B12854639 : Blo 2005435 12854639 := bstep (se 1 (by rfl) ⟨9640979, by rfl⟩ : syracuseStep 12854639 = 19281959) B19281959
theorem B34279037 : Blo 2005435 34279037 := bstep (se 3 (by rfl) ⟨6427319, by rfl⟩ : syracuseStep 34279037 = 12854639) B12854639
theorem B22852691 : Blo 2005435 22852691 := bstep (se 1 (by rfl) ⟨17139518, by rfl⟩ : syracuseStep 22852691 = 34279037) B34279037
theorem B15235127 : Blo 2005435 15235127 := bstep (se 1 (by rfl) ⟨11426345, by rfl⟩ : syracuseStep 15235127 = 22852691) B22852691
theorem B10156751 : Blo 2005435 10156751 := bstep (se 1 (by rfl) ⟨7617563, by rfl⟩ : syracuseStep 10156751 = 15235127) B15235127
theorem B6771167 : Blo 2005435 6771167 := bstep (se 1 (by rfl) ⟨5078375, by rfl⟩ : syracuseStep 6771167 = 10156751) B10156751
theorem B4514111 : Blo 2005435 4514111 := bstep (se 1 (by rfl) ⟨3385583, by rfl⟩ : syracuseStep 4514111 = 6771167) B6771167
theorem B3009407 : Blo 2005435 3009407 := bstep (se 1 (by rfl) ⟨2257055, by rfl⟩ : syracuseStep 3009407 = 4514111) B4514111
theorem B2006271 : Blo 2005435 2006271 := bstep (se 1 (by rfl) ⟨1504703, by rfl⟩ : syracuseStep 2006271 = 3009407) B3009407
theorem B3009413 : Blo 2005435 3009413 := bbase (se 4 (by rfl) ⟨282132, by rfl⟩ : syracuseStep 3009413 = 564265) (by norm_num)
theorem B2006275 : Blo 2005435 2006275 := bstep (se 1 (by rfl) ⟨1504706, by rfl⟩ : syracuseStep 2006275 = 3009413) B3009413
theorem B3385597 : Blo 2005435 3385597 := bbase (se 3 (by rfl) ⟨634799, by rfl⟩ : syracuseStep 3385597 = 1269599) (by norm_num)
theorem B4514129 : Blo 2005435 4514129 := bstep (se 2 (by rfl) ⟨1692798, by rfl⟩ : syracuseStep 4514129 = 3385597) B3385597
theorem B3009419 : Blo 2005435 3009419 := bstep (se 1 (by rfl) ⟨2257064, by rfl⟩ : syracuseStep 3009419 = 4514129) B4514129
theorem B2006279 : Blo 2005435 2006279 := bstep (se 1 (by rfl) ⟨1504709, by rfl⟩ : syracuseStep 2006279 = 3009419) B3009419
theorem B2257069 : Blo 2005435 2257069 := bbase (se 3 (by rfl) ⟨423200, by rfl⟩ : syracuseStep 2257069 = 846401) (by norm_num)
theorem B3009425 : Blo 2005435 3009425 := bstep (se 2 (by rfl) ⟨1128534, by rfl⟩ : syracuseStep 3009425 = 2257069) B2257069
theorem B2006283 : Blo 2005435 2006283 := bstep (se 1 (by rfl) ⟨1504712, by rfl⟩ : syracuseStep 2006283 = 3009425) B3009425
theorem B6771221 : Blo 2005435 6771221 := bbase (se 6 (by rfl) ⟨158700, by rfl⟩ : syracuseStep 6771221 = 317401) (by norm_num)
theorem B4514147 : Blo 2005435 4514147 := bstep (se 1 (by rfl) ⟨3385610, by rfl⟩ : syracuseStep 4514147 = 6771221) B6771221
theorem B3009431 : Blo 2005435 3009431 := bstep (se 1 (by rfl) ⟨2257073, by rfl⟩ : syracuseStep 3009431 = 4514147) B4514147
theorem B2006287 : Blo 2005435 2006287 := bstep (se 1 (by rfl) ⟨1504715, by rfl⟩ : syracuseStep 2006287 = 3009431) B3009431
theorem B3009437 : Blo 2005435 3009437 := bbase (se 3 (by rfl) ⟨564269, by rfl⟩ : syracuseStep 3009437 = 1128539) (by norm_num)
theorem B2006291 : Blo 2005435 2006291 := bstep (se 1 (by rfl) ⟨1504718, by rfl⟩ : syracuseStep 2006291 = 3009437) B3009437
theorem B4514165 : Blo 2005435 4514165 := bbase (se 5 (by rfl) ⟨211601, by rfl⟩ : syracuseStep 4514165 = 423203) (by norm_num)
theorem B3009443 : Blo 2005435 3009443 := bstep (se 1 (by rfl) ⟨2257082, by rfl⟩ : syracuseStep 3009443 = 4514165) B4514165
theorem B2006295 : Blo 2005435 2006295 := bstep (se 1 (by rfl) ⟨1504721, by rfl⟩ : syracuseStep 2006295 = 3009443) B3009443
theorem B2573869 : Blo 2005435 2573869 := bbase (se 3 (by rfl) ⟨482600, by rfl⟩ : syracuseStep 2573869 = 965201) (by norm_num)
theorem B3431825 : Blo 2005435 3431825 := bstep (se 2 (by rfl) ⟨1286934, by rfl⟩ : syracuseStep 3431825 = 2573869) B2573869
theorem B2287883 : Blo 2005435 2287883 := bstep (se 1 (by rfl) ⟨1715912, by rfl⟩ : syracuseStep 2287883 = 3431825) B3431825
theorem B6101021 : Blo 2005435 6101021 := bstep (se 3 (by rfl) ⟨1143941, by rfl⟩ : syracuseStep 6101021 = 2287883) B2287883
theorem B4067347 : Blo 2005435 4067347 := bstep (se 1 (by rfl) ⟨3050510, by rfl⟩ : syracuseStep 4067347 = 6101021) B6101021
theorem B5423129 : Blo 2005435 5423129 := bstep (se 2 (by rfl) ⟨2033673, by rfl⟩ : syracuseStep 5423129 = 4067347) B4067347
theorem B3615419 : Blo 2005435 3615419 := bstep (se 1 (by rfl) ⟨2711564, by rfl⟩ : syracuseStep 3615419 = 5423129) B5423129
theorem B2410279 : Blo 2005435 2410279 := bstep (se 1 (by rfl) ⟨1807709, by rfl⟩ : syracuseStep 2410279 = 3615419) B3615419
theorem B12854821 : Blo 2005435 12854821 := bstep (se 4 (by rfl) ⟨1205139, by rfl⟩ : syracuseStep 12854821 = 2410279) B2410279
theorem B17139761 : Blo 2005435 17139761 := bstep (se 2 (by rfl) ⟨6427410, by rfl⟩ : syracuseStep 17139761 = 12854821) B12854821
theorem B11426507 : Blo 2005435 11426507 := bstep (se 1 (by rfl) ⟨8569880, by rfl⟩ : syracuseStep 11426507 = 17139761) B17139761
theorem B7617671 : Blo 2005435 7617671 := bstep (se 1 (by rfl) ⟨5713253, by rfl⟩ : syracuseStep 7617671 = 11426507) B11426507
theorem B5078447 : Blo 2005435 5078447 := bstep (se 1 (by rfl) ⟨3808835, by rfl⟩ : syracuseStep 5078447 = 7617671) B7617671
theorem B3385631 : Blo 2005435 3385631 := bstep (se 1 (by rfl) ⟨2539223, by rfl⟩ : syracuseStep 3385631 = 5078447) B5078447
theorem B2257087 : Blo 2005435 2257087 := bstep (se 1 (by rfl) ⟨1692815, by rfl⟩ : syracuseStep 2257087 = 3385631) B3385631
theorem B3009449 : Blo 2005435 3009449 := bstep (se 2 (by rfl) ⟨1128543, by rfl⟩ : syracuseStep 3009449 = 2257087) B2257087
theorem B2006299 : Blo 2005435 2006299 := bstep (se 1 (by rfl) ⟨1504724, by rfl⟩ : syracuseStep 2006299 = 3009449) B3009449
theorem B7617685 : Blo 2005435 7617685 := bbase (se 6 (by rfl) ⟨178539, by rfl⟩ : syracuseStep 7617685 = 357079) (by norm_num)
theorem B10156913 : Blo 2005435 10156913 := bstep (se 2 (by rfl) ⟨3808842, by rfl⟩ : syracuseStep 10156913 = 7617685) B7617685
theorem B6771275 : Blo 2005435 6771275 := bstep (se 1 (by rfl) ⟨5078456, by rfl⟩ : syracuseStep 6771275 = 10156913) B10156913
theorem B4514183 : Blo 2005435 4514183 := bstep (se 1 (by rfl) ⟨3385637, by rfl⟩ : syracuseStep 4514183 = 6771275) B6771275
theorem B3009455 : Blo 2005435 3009455 := bstep (se 1 (by rfl) ⟨2257091, by rfl⟩ : syracuseStep 3009455 = 4514183) B4514183
theorem B2006303 : Blo 2005435 2006303 := bstep (se 1 (by rfl) ⟨1504727, by rfl⟩ : syracuseStep 2006303 = 3009455) B3009455
theorem B3009461 : Blo 2005435 3009461 := bbase (se 5 (by rfl) ⟨141068, by rfl⟩ : syracuseStep 3009461 = 282137) (by norm_num)
theorem B2006307 : Blo 2005435 2006307 := bstep (se 1 (by rfl) ⟨1504730, by rfl⟩ : syracuseStep 2006307 = 3009461) B3009461
theorem B5078477 : Blo 2005435 5078477 := bbase (se 3 (by rfl) ⟨952214, by rfl⟩ : syracuseStep 5078477 = 1904429) (by norm_num)
theorem B3385651 : Blo 2005435 3385651 := bstep (se 1 (by rfl) ⟨2539238, by rfl⟩ : syracuseStep 3385651 = 5078477) B5078477
theorem B4514201 : Blo 2005435 4514201 := bstep (se 2 (by rfl) ⟨1692825, by rfl⟩ : syracuseStep 4514201 = 3385651) B3385651
theorem B3009467 : Blo 2005435 3009467 := bstep (se 1 (by rfl) ⟨2257100, by rfl⟩ : syracuseStep 3009467 = 4514201) B4514201
theorem B2006311 : Blo 2005435 2006311 := bstep (se 1 (by rfl) ⟨1504733, by rfl⟩ : syracuseStep 2006311 = 3009467) B3009467
theorem B2257105 : Blo 2005435 2257105 := bbase (se 2 (by rfl) ⟨846414, by rfl⟩ : syracuseStep 2257105 = 1692829) (by norm_num)
theorem B3009473 : Blo 2005435 3009473 := bstep (se 2 (by rfl) ⟨1128552, by rfl⟩ : syracuseStep 3009473 = 2257105) B2257105
theorem B2006315 : Blo 2005435 2006315 := bstep (se 1 (by rfl) ⟨1504736, by rfl⟩ : syracuseStep 2006315 = 3009473) B3009473
theorem B6863717 : Blo 2005435 6863717 := bbase (se 4 (by rfl) ⟨643473, by rfl⟩ : syracuseStep 6863717 = 1286947) (by norm_num)
theorem B18303245 : Blo 2005435 18303245 := bstep (se 3 (by rfl) ⟨3431858, by rfl⟩ : syracuseStep 18303245 = 6863717) B6863717
theorem B12202163 : Blo 2005435 12202163 := bstep (se 1 (by rfl) ⟨9151622, by rfl⟩ : syracuseStep 12202163 = 18303245) B18303245
theorem B8134775 : Blo 2005435 8134775 := bstep (se 1 (by rfl) ⟨6101081, by rfl⟩ : syracuseStep 8134775 = 12202163) B12202163
theorem B5423183 : Blo 2005435 5423183 := bstep (se 1 (by rfl) ⟨4067387, by rfl⟩ : syracuseStep 5423183 = 8134775) B8134775
theorem B3615455 : Blo 2005435 3615455 := bstep (se 1 (by rfl) ⟨2711591, by rfl⟩ : syracuseStep 3615455 = 5423183) B5423183
theorem B9641213 : Blo 2005435 9641213 := bstep (se 3 (by rfl) ⟨1807727, by rfl⟩ : syracuseStep 9641213 = 3615455) B3615455
theorem B6427475 : Blo 2005435 6427475 := bstep (se 1 (by rfl) ⟨4820606, by rfl⟩ : syracuseStep 6427475 = 9641213) B9641213
theorem B4284983 : Blo 2005435 4284983 := bstep (se 1 (by rfl) ⟨3213737, by rfl⟩ : syracuseStep 4284983 = 6427475) B6427475
theorem B2856655 : Blo 2005435 2856655 := bstep (se 1 (by rfl) ⟨2142491, by rfl⟩ : syracuseStep 2856655 = 4284983) B4284983
theorem B3808873 : Blo 2005435 3808873 := bstep (se 2 (by rfl) ⟨1428327, by rfl⟩ : syracuseStep 3808873 = 2856655) B2856655
theorem B5078497 : Blo 2005435 5078497 := bstep (se 2 (by rfl) ⟨1904436, by rfl⟩ : syracuseStep 5078497 = 3808873) B3808873
theorem B6771329 : Blo 2005435 6771329 := bstep (se 2 (by rfl) ⟨2539248, by rfl⟩ : syracuseStep 6771329 = 5078497) B5078497
theorem B4514219 : Blo 2005435 4514219 := bstep (se 1 (by rfl) ⟨3385664, by rfl⟩ : syracuseStep 4514219 = 6771329) B6771329
theorem B3009479 : Blo 2005435 3009479 := bstep (se 1 (by rfl) ⟨2257109, by rfl⟩ : syracuseStep 3009479 = 4514219) B4514219
theorem B2006319 : Blo 2005435 2006319 := bstep (se 1 (by rfl) ⟨1504739, by rfl⟩ : syracuseStep 2006319 = 3009479) B3009479
theorem B3009485 : Blo 2005435 3009485 := bbase (se 3 (by rfl) ⟨564278, by rfl⟩ : syracuseStep 3009485 = 1128557) (by norm_num)
theorem B2006323 : Blo 2005435 2006323 := bstep (se 1 (by rfl) ⟨1504742, by rfl⟩ : syracuseStep 2006323 = 3009485) B3009485
theorem B4514237 : Blo 2005435 4514237 := bbase (se 3 (by rfl) ⟨846419, by rfl⟩ : syracuseStep 4514237 = 1692839) (by norm_num)
theorem B3009491 : Blo 2005435 3009491 := bstep (se 1 (by rfl) ⟨2257118, by rfl⟩ : syracuseStep 3009491 = 4514237) B4514237
theorem B2006327 : Blo 2005435 2006327 := bstep (se 1 (by rfl) ⟨1504745, by rfl⟩ : syracuseStep 2006327 = 3009491) B3009491
theorem B3385685 : Blo 2005435 3385685 := bbase (se 10 (by rfl) ⟨4959, by rfl⟩ : syracuseStep 3385685 = 9919) (by norm_num)
theorem B2257123 : Blo 2005435 2257123 := bstep (se 1 (by rfl) ⟨1692842, by rfl⟩ : syracuseStep 2257123 = 3385685) B3385685
theorem B3009497 : Blo 2005435 3009497 := bstep (se 2 (by rfl) ⟨1128561, by rfl⟩ : syracuseStep 3009497 = 2257123) B2257123
theorem B2006331 : Blo 2005435 2006331 := bstep (se 1 (by rfl) ⟨1504748, by rfl⟩ : syracuseStep 2006331 = 3009497) B3009497
theorem B6427525 : Blo 2005435 6427525 := bbase (se 4 (by rfl) ⟨602580, by rfl⟩ : syracuseStep 6427525 = 1205161) (by norm_num)
theorem B8570033 : Blo 2005435 8570033 := bstep (se 2 (by rfl) ⟨3213762, by rfl⟩ : syracuseStep 8570033 = 6427525) B6427525
theorem B5713355 : Blo 2005435 5713355 := bstep (se 1 (by rfl) ⟨4285016, by rfl⟩ : syracuseStep 5713355 = 8570033) B8570033
theorem B15235613 : Blo 2005435 15235613 := bstep (se 3 (by rfl) ⟨2856677, by rfl⟩ : syracuseStep 15235613 = 5713355) B5713355
theorem B10157075 : Blo 2005435 10157075 := bstep (se 1 (by rfl) ⟨7617806, by rfl⟩ : syracuseStep 10157075 = 15235613) B15235613
theorem B6771383 : Blo 2005435 6771383 := bstep (se 1 (by rfl) ⟨5078537, by rfl⟩ : syracuseStep 6771383 = 10157075) B10157075
theorem B4514255 : Blo 2005435 4514255 := bstep (se 1 (by rfl) ⟨3385691, by rfl⟩ : syracuseStep 4514255 = 6771383) B6771383
theorem B3009503 : Blo 2005435 3009503 := bstep (se 1 (by rfl) ⟨2257127, by rfl⟩ : syracuseStep 3009503 = 4514255) B4514255
theorem B2006335 : Blo 2005435 2006335 := bstep (se 1 (by rfl) ⟨1504751, by rfl⟩ : syracuseStep 2006335 = 3009503) B3009503
theorem B3009509 : Blo 2005435 3009509 := bbase (se 4 (by rfl) ⟨282141, by rfl⟩ : syracuseStep 3009509 = 564283) (by norm_num)
theorem B2006339 : Blo 2005435 2006339 := bstep (se 1 (by rfl) ⟨1504754, by rfl⟩ : syracuseStep 2006339 = 3009509) B3009509
theorem B8570069 : Blo 2005435 8570069 := bbase (se 7 (by rfl) ⟨100430, by rfl⟩ : syracuseStep 8570069 = 200861) (by norm_num)
theorem B5713379 : Blo 2005435 5713379 := bstep (se 1 (by rfl) ⟨4285034, by rfl⟩ : syracuseStep 5713379 = 8570069) B8570069
theorem B3808919 : Blo 2005435 3808919 := bstep (se 1 (by rfl) ⟨2856689, by rfl⟩ : syracuseStep 3808919 = 5713379) B5713379
theorem B2539279 : Blo 2005435 2539279 := bstep (se 1 (by rfl) ⟨1904459, by rfl⟩ : syracuseStep 2539279 = 3808919) B3808919
theorem B3385705 : Blo 2005435 3385705 := bstep (se 2 (by rfl) ⟨1269639, by rfl⟩ : syracuseStep 3385705 = 2539279) B2539279
theorem B4514273 : Blo 2005435 4514273 := bstep (se 2 (by rfl) ⟨1692852, by rfl⟩ : syracuseStep 4514273 = 3385705) B3385705
theorem B3009515 : Blo 2005435 3009515 := bstep (se 1 (by rfl) ⟨2257136, by rfl⟩ : syracuseStep 3009515 = 4514273) B4514273
theorem B2006343 : Blo 2005435 2006343 := bstep (se 1 (by rfl) ⟨1504757, by rfl⟩ : syracuseStep 2006343 = 3009515) B3009515
theorem B2257141 : Blo 2005435 2257141 := bbase (se 5 (by rfl) ⟨105803, by rfl⟩ : syracuseStep 2257141 = 211607) (by norm_num)
theorem B3009521 : Blo 2005435 3009521 := bstep (se 2 (by rfl) ⟨1128570, by rfl⟩ : syracuseStep 3009521 = 2257141) B2257141
theorem B2006347 : Blo 2005435 2006347 := bstep (se 1 (by rfl) ⟨1504760, by rfl⟩ : syracuseStep 2006347 = 3009521) B3009521
theorem B2539289 : Blo 2005435 2539289 := bbase (se 2 (by rfl) ⟨952233, by rfl⟩ : syracuseStep 2539289 = 1904467) (by norm_num)
theorem B6771437 : Blo 2005435 6771437 := bstep (se 3 (by rfl) ⟨1269644, by rfl⟩ : syracuseStep 6771437 = 2539289) B2539289
theorem B4514291 : Blo 2005435 4514291 := bstep (se 1 (by rfl) ⟨3385718, by rfl⟩ : syracuseStep 4514291 = 6771437) B6771437
theorem B3009527 : Blo 2005435 3009527 := bstep (se 1 (by rfl) ⟨2257145, by rfl⟩ : syracuseStep 3009527 = 4514291) B4514291
theorem B2006351 : Blo 2005435 2006351 := bstep (se 1 (by rfl) ⟨1504763, by rfl⟩ : syracuseStep 2006351 = 3009527) B3009527
theorem B3009533 : Blo 2005435 3009533 := bbase (se 3 (by rfl) ⟨564287, by rfl⟩ : syracuseStep 3009533 = 1128575) (by norm_num)
theorem B2006355 : Blo 2005435 2006355 := bstep (se 1 (by rfl) ⟨1504766, by rfl⟩ : syracuseStep 2006355 = 3009533) B3009533
theorem B4514309 : Blo 2005435 4514309 := bbase (se 4 (by rfl) ⟨423216, by rfl⟩ : syracuseStep 4514309 = 846433) (by norm_num)
theorem B3009539 : Blo 2005435 3009539 := bstep (se 1 (by rfl) ⟨2257154, by rfl⟩ : syracuseStep 3009539 = 4514309) B4514309
theorem B2006359 : Blo 2005435 2006359 := bstep (se 1 (by rfl) ⟨1504769, by rfl⟩ : syracuseStep 2006359 = 3009539) B3009539
theorem B3808957 : Blo 2005435 3808957 := bbase (se 3 (by rfl) ⟨714179, by rfl⟩ : syracuseStep 3808957 = 1428359) (by norm_num)
theorem B5078609 : Blo 2005435 5078609 := bstep (se 2 (by rfl) ⟨1904478, by rfl⟩ : syracuseStep 5078609 = 3808957) B3808957
theorem B3385739 : Blo 2005435 3385739 := bstep (se 1 (by rfl) ⟨2539304, by rfl⟩ : syracuseStep 3385739 = 5078609) B5078609
theorem B2257159 : Blo 2005435 2257159 := bstep (se 1 (by rfl) ⟨1692869, by rfl⟩ : syracuseStep 2257159 = 3385739) B3385739
theorem B3009545 : Blo 2005435 3009545 := bstep (se 2 (by rfl) ⟨1128579, by rfl⟩ : syracuseStep 3009545 = 2257159) B2257159
theorem B2006363 : Blo 2005435 2006363 := bstep (se 1 (by rfl) ⟨1504772, by rfl⟩ : syracuseStep 2006363 = 3009545) B3009545
theorem B10157237 : Blo 2005435 10157237 := bbase (se 5 (by rfl) ⟨476120, by rfl⟩ : syracuseStep 10157237 = 952241) (by norm_num)
theorem B6771491 : Blo 2005435 6771491 := bstep (se 1 (by rfl) ⟨5078618, by rfl⟩ : syracuseStep 6771491 = 10157237) B10157237
theorem B4514327 : Blo 2005435 4514327 := bstep (se 1 (by rfl) ⟨3385745, by rfl⟩ : syracuseStep 4514327 = 6771491) B6771491
theorem B3009551 : Blo 2005435 3009551 := bstep (se 1 (by rfl) ⟨2257163, by rfl⟩ : syracuseStep 3009551 = 4514327) B4514327
theorem B2006367 : Blo 2005435 2006367 := bstep (se 1 (by rfl) ⟨1504775, by rfl⟩ : syracuseStep 2006367 = 3009551) B3009551
theorem B3009557 : Blo 2005435 3009557 := bbase (se 6 (by rfl) ⟨70536, by rfl⟩ : syracuseStep 3009557 = 141073) (by norm_num)
theorem B2006371 : Blo 2005435 2006371 := bstep (se 1 (by rfl) ⟨1504778, by rfl⟩ : syracuseStep 2006371 = 3009557) B3009557
theorem B5423333 : Blo 2005435 5423333 := bbase (se 4 (by rfl) ⟨508437, by rfl⟩ : syracuseStep 5423333 = 1016875) (by norm_num)
theorem B14462221 : Blo 2005435 14462221 := bstep (se 3 (by rfl) ⟨2711666, by rfl⟩ : syracuseStep 14462221 = 5423333) B5423333
theorem B19282961 : Blo 2005435 19282961 := bstep (se 2 (by rfl) ⟨7231110, by rfl⟩ : syracuseStep 19282961 = 14462221) B14462221
theorem B12855307 : Blo 2005435 12855307 := bstep (se 1 (by rfl) ⟨9641480, by rfl⟩ : syracuseStep 12855307 = 19282961) B19282961
theorem B17140409 : Blo 2005435 17140409 := bstep (se 2 (by rfl) ⟨6427653, by rfl⟩ : syracuseStep 17140409 = 12855307) B12855307
theorem B11426939 : Blo 2005435 11426939 := bstep (se 1 (by rfl) ⟨8570204, by rfl⟩ : syracuseStep 11426939 = 17140409) B17140409
theorem B7617959 : Blo 2005435 7617959 := bstep (se 1 (by rfl) ⟨5713469, by rfl⟩ : syracuseStep 7617959 = 11426939) B11426939
theorem B5078639 : Blo 2005435 5078639 := bstep (se 1 (by rfl) ⟨3808979, by rfl⟩ : syracuseStep 5078639 = 7617959) B7617959
theorem B3385759 : Blo 2005435 3385759 := bstep (se 1 (by rfl) ⟨2539319, by rfl⟩ : syracuseStep 3385759 = 5078639) B5078639
theorem B4514345 : Blo 2005435 4514345 := bstep (se 2 (by rfl) ⟨1692879, by rfl⟩ : syracuseStep 4514345 = 3385759) B3385759
theorem B3009563 : Blo 2005435 3009563 := bstep (se 1 (by rfl) ⟨2257172, by rfl⟩ : syracuseStep 3009563 = 4514345) B4514345
theorem B2006375 : Blo 2005435 2006375 := bstep (se 1 (by rfl) ⟨1504781, by rfl⟩ : syracuseStep 2006375 = 3009563) B3009563
theorem B2257177 : Blo 2005435 2257177 := bbase (se 2 (by rfl) ⟨846441, by rfl⟩ : syracuseStep 2257177 = 1692883) (by norm_num)
theorem B3009569 : Blo 2005435 3009569 := bstep (se 2 (by rfl) ⟨1128588, by rfl⟩ : syracuseStep 3009569 = 2257177) B2257177
theorem B2006379 : Blo 2005435 2006379 := bstep (se 1 (by rfl) ⟨1504784, by rfl⟩ : syracuseStep 2006379 = 3009569) B3009569
theorem B7617989 : Blo 2005435 7617989 := bbase (se 4 (by rfl) ⟨714186, by rfl⟩ : syracuseStep 7617989 = 1428373) (by norm_num)
theorem B5078659 : Blo 2005435 5078659 := bstep (se 1 (by rfl) ⟨3808994, by rfl⟩ : syracuseStep 5078659 = 7617989) B7617989
theorem B6771545 : Blo 2005435 6771545 := bstep (se 2 (by rfl) ⟨2539329, by rfl⟩ : syracuseStep 6771545 = 5078659) B5078659
theorem B4514363 : Blo 2005435 4514363 := bstep (se 1 (by rfl) ⟨3385772, by rfl⟩ : syracuseStep 4514363 = 6771545) B6771545
theorem B3009575 : Blo 2005435 3009575 := bstep (se 1 (by rfl) ⟨2257181, by rfl⟩ : syracuseStep 3009575 = 4514363) B4514363
theorem B2006383 : Blo 2005435 2006383 := bstep (se 1 (by rfl) ⟨1504787, by rfl⟩ : syracuseStep 2006383 = 3009575) B3009575
theorem B3009581 : Blo 2005435 3009581 := bbase (se 3 (by rfl) ⟨564296, by rfl⟩ : syracuseStep 3009581 = 1128593) (by norm_num)
theorem B2006387 : Blo 2005435 2006387 := bstep (se 1 (by rfl) ⟨1504790, by rfl⟩ : syracuseStep 2006387 = 3009581) B3009581
theorem B4514381 : Blo 2005435 4514381 := bbase (se 3 (by rfl) ⟨846446, by rfl⟩ : syracuseStep 4514381 = 1692893) (by norm_num)
theorem B3009587 : Blo 2005435 3009587 := bstep (se 1 (by rfl) ⟨2257190, by rfl⟩ : syracuseStep 3009587 = 4514381) B4514381
theorem B2006391 : Blo 2005435 2006391 := bstep (se 1 (by rfl) ⟨1504793, by rfl⟩ : syracuseStep 2006391 = 3009587) B3009587
theorem B2539345 : Blo 2005435 2539345 := bbase (se 2 (by rfl) ⟨952254, by rfl⟩ : syracuseStep 2539345 = 1904509) (by norm_num)
theorem B3385793 : Blo 2005435 3385793 := bstep (se 2 (by rfl) ⟨1269672, by rfl⟩ : syracuseStep 3385793 = 2539345) B2539345
theorem B2257195 : Blo 2005435 2257195 := bstep (se 1 (by rfl) ⟨1692896, by rfl⟩ : syracuseStep 2257195 = 3385793) B3385793
theorem B3009593 : Blo 2005435 3009593 := bstep (se 2 (by rfl) ⟨1128597, by rfl⟩ : syracuseStep 3009593 = 2257195) B2257195
theorem B2006395 : Blo 2005435 2006395 := bstep (se 1 (by rfl) ⟨1504796, by rfl⟩ : syracuseStep 2006395 = 3009593) B3009593
theorem B5791493 : Blo 2005435 5791493 := bbase (se 4 (by rfl) ⟨542952, by rfl⟩ : syracuseStep 5791493 = 1085905) (by norm_num)
theorem B3860995 : Blo 2005435 3860995 := bstep (se 1 (by rfl) ⟨2895746, by rfl⟩ : syracuseStep 3860995 = 5791493) B5791493
theorem B5147993 : Blo 2005435 5147993 := bstep (se 2 (by rfl) ⟨1930497, by rfl⟩ : syracuseStep 5147993 = 3860995) B3860995
theorem B13727981 : Blo 2005435 13727981 := bstep (se 3 (by rfl) ⟨2573996, by rfl⟩ : syracuseStep 13727981 = 5147993) B5147993
theorem B9151987 : Blo 2005435 9151987 := bstep (se 1 (by rfl) ⟨6863990, by rfl⟩ : syracuseStep 9151987 = 13727981) B13727981
theorem B12202649 : Blo 2005435 12202649 := bstep (se 2 (by rfl) ⟨4575993, by rfl⟩ : syracuseStep 12202649 = 9151987) B9151987
theorem B8135099 : Blo 2005435 8135099 := bstep (se 1 (by rfl) ⟨6101324, by rfl⟩ : syracuseStep 8135099 = 12202649) B12202649
theorem B5423399 : Blo 2005435 5423399 := bstep (se 1 (by rfl) ⟨4067549, by rfl⟩ : syracuseStep 5423399 = 8135099) B8135099
theorem B3615599 : Blo 2005435 3615599 := bstep (se 1 (by rfl) ⟨2711699, by rfl⟩ : syracuseStep 3615599 = 5423399) B5423399
theorem B2410399 : Blo 2005435 2410399 := bstep (se 1 (by rfl) ⟨1807799, by rfl⟩ : syracuseStep 2410399 = 3615599) B3615599
theorem B3213865 : Blo 2005435 3213865 := bstep (se 2 (by rfl) ⟨1205199, by rfl⟩ : syracuseStep 3213865 = 2410399) B2410399
theorem B4285153 : Blo 2005435 4285153 := bstep (se 2 (by rfl) ⟨1606932, by rfl⟩ : syracuseStep 4285153 = 3213865) B3213865
theorem B22854149 : Blo 2005435 22854149 := bstep (se 4 (by rfl) ⟨2142576, by rfl⟩ : syracuseStep 22854149 = 4285153) B4285153
theorem B15236099 : Blo 2005435 15236099 := bstep (se 1 (by rfl) ⟨11427074, by rfl⟩ : syracuseStep 15236099 = 22854149) B22854149
theorem B10157399 : Blo 2005435 10157399 := bstep (se 1 (by rfl) ⟨7618049, by rfl⟩ : syracuseStep 10157399 = 15236099) B15236099
theorem B6771599 : Blo 2005435 6771599 := bstep (se 1 (by rfl) ⟨5078699, by rfl⟩ : syracuseStep 6771599 = 10157399) B10157399
theorem B4514399 : Blo 2005435 4514399 := bstep (se 1 (by rfl) ⟨3385799, by rfl⟩ : syracuseStep 4514399 = 6771599) B6771599
theorem B3009599 : Blo 2005435 3009599 := bstep (se 1 (by rfl) ⟨2257199, by rfl⟩ : syracuseStep 3009599 = 4514399) B4514399
theorem B2006399 : Blo 2005435 2006399 := bstep (se 1 (by rfl) ⟨1504799, by rfl⟩ : syracuseStep 2006399 = 3009599) B3009599
theorem B3009605 : Blo 2005435 3009605 := bbase (se 4 (by rfl) ⟨282150, by rfl⟩ : syracuseStep 3009605 = 564301) (by norm_num)
theorem B2006403 : Blo 2005435 2006403 := bstep (se 1 (by rfl) ⟨1504802, by rfl⟩ : syracuseStep 2006403 = 3009605) B3009605
theorem B3385813 : Blo 2005435 3385813 := bbase (se 7 (by rfl) ⟨39677, by rfl⟩ : syracuseStep 3385813 = 79355) (by norm_num)
theorem B4514417 : Blo 2005435 4514417 := bstep (se 2 (by rfl) ⟨1692906, by rfl⟩ : syracuseStep 4514417 = 3385813) B3385813
theorem B3009611 : Blo 2005435 3009611 := bstep (se 1 (by rfl) ⟨2257208, by rfl⟩ : syracuseStep 3009611 = 4514417) B4514417
theorem B2006407 : Blo 2005435 2006407 := bstep (se 1 (by rfl) ⟨1504805, by rfl⟩ : syracuseStep 2006407 = 3009611) B3009611
theorem B2257213 : Blo 2005435 2257213 := bbase (se 3 (by rfl) ⟨423227, by rfl⟩ : syracuseStep 2257213 = 846455) (by norm_num)
theorem B3009617 : Blo 2005435 3009617 := bstep (se 2 (by rfl) ⟨1128606, by rfl⟩ : syracuseStep 3009617 = 2257213) B2257213
theorem B2006411 : Blo 2005435 2006411 := bstep (se 1 (by rfl) ⟨1504808, by rfl⟩ : syracuseStep 2006411 = 3009617) B3009617
theorem B6771653 : Blo 2005435 6771653 := bbase (se 4 (by rfl) ⟨634842, by rfl⟩ : syracuseStep 6771653 = 1269685) (by norm_num)
theorem B4514435 : Blo 2005435 4514435 := bstep (se 1 (by rfl) ⟨3385826, by rfl⟩ : syracuseStep 4514435 = 6771653) B6771653
theorem B3009623 : Blo 2005435 3009623 := bstep (se 1 (by rfl) ⟨2257217, by rfl⟩ : syracuseStep 3009623 = 4514435) B4514435
theorem B2006415 : Blo 2005435 2006415 := bstep (se 1 (by rfl) ⟨1504811, by rfl⟩ : syracuseStep 2006415 = 3009623) B3009623
theorem B3009629 : Blo 2005435 3009629 := bbase (se 3 (by rfl) ⟨564305, by rfl⟩ : syracuseStep 3009629 = 1128611) (by norm_num)
theorem B2006419 : Blo 2005435 2006419 := bstep (se 1 (by rfl) ⟨1504814, by rfl⟩ : syracuseStep 2006419 = 3009629) B3009629
theorem B4514453 : Blo 2005435 4514453 := bbase (se 6 (by rfl) ⟨105807, by rfl⟩ : syracuseStep 4514453 = 211615) (by norm_num)
theorem B3009635 : Blo 2005435 3009635 := bstep (se 1 (by rfl) ⟨2257226, by rfl⟩ : syracuseStep 3009635 = 4514453) B4514453
theorem B2006423 : Blo 2005435 2006423 := bstep (se 1 (by rfl) ⟨1504817, by rfl⟩ : syracuseStep 2006423 = 3009635) B3009635
theorem B7231301 : Blo 2005435 7231301 := bbase (se 4 (by rfl) ⟨677934, by rfl⟩ : syracuseStep 7231301 = 1355869) (by norm_num)
theorem B4820867 : Blo 2005435 4820867 := bstep (se 1 (by rfl) ⟨3615650, by rfl⟩ : syracuseStep 4820867 = 7231301) B7231301
theorem B3213911 : Blo 2005435 3213911 := bstep (se 1 (by rfl) ⟨2410433, by rfl⟩ : syracuseStep 3213911 = 4820867) B4820867
theorem B2142607 : Blo 2005435 2142607 := bstep (se 1 (by rfl) ⟨1606955, by rfl⟩ : syracuseStep 2142607 = 3213911) B3213911
theorem B2856809 : Blo 2005435 2856809 := bstep (se 2 (by rfl) ⟨1071303, by rfl⟩ : syracuseStep 2856809 = 2142607) B2142607
theorem B7618157 : Blo 2005435 7618157 := bstep (se 3 (by rfl) ⟨1428404, by rfl⟩ : syracuseStep 7618157 = 2856809) B2856809
theorem B5078771 : Blo 2005435 5078771 := bstep (se 1 (by rfl) ⟨3809078, by rfl⟩ : syracuseStep 5078771 = 7618157) B7618157
theorem B3385847 : Blo 2005435 3385847 := bstep (se 1 (by rfl) ⟨2539385, by rfl⟩ : syracuseStep 3385847 = 5078771) B5078771
theorem B2257231 : Blo 2005435 2257231 := bstep (se 1 (by rfl) ⟨1692923, by rfl⟩ : syracuseStep 2257231 = 3385847) B3385847
theorem B3009641 : Blo 2005435 3009641 := bstep (se 2 (by rfl) ⟨1128615, by rfl⟩ : syracuseStep 3009641 = 2257231) B2257231
theorem B2006427 : Blo 2005435 2006427 := bstep (se 1 (by rfl) ⟨1504820, by rfl⟩ : syracuseStep 2006427 = 3009641) B3009641
theorem B9641749 : Blo 2005435 9641749 := bbase (se 6 (by rfl) ⟨225978, by rfl⟩ : syracuseStep 9641749 = 451957) (by norm_num)
theorem B12855665 : Blo 2005435 12855665 := bstep (se 2 (by rfl) ⟨4820874, by rfl⟩ : syracuseStep 12855665 = 9641749) B9641749
theorem B8570443 : Blo 2005435 8570443 := bstep (se 1 (by rfl) ⟨6427832, by rfl⟩ : syracuseStep 8570443 = 12855665) B12855665
theorem B11427257 : Blo 2005435 11427257 := bstep (se 2 (by rfl) ⟨4285221, by rfl⟩ : syracuseStep 11427257 = 8570443) B8570443
theorem B7618171 : Blo 2005435 7618171 := bstep (se 1 (by rfl) ⟨5713628, by rfl⟩ : syracuseStep 7618171 = 11427257) B11427257
theorem B10157561 : Blo 2005435 10157561 := bstep (se 2 (by rfl) ⟨3809085, by rfl⟩ : syracuseStep 10157561 = 7618171) B7618171
theorem B6771707 : Blo 2005435 6771707 := bstep (se 1 (by rfl) ⟨5078780, by rfl⟩ : syracuseStep 6771707 = 10157561) B10157561
theorem B4514471 : Blo 2005435 4514471 := bstep (se 1 (by rfl) ⟨3385853, by rfl⟩ : syracuseStep 4514471 = 6771707) B6771707
theorem B3009647 : Blo 2005435 3009647 := bstep (se 1 (by rfl) ⟨2257235, by rfl⟩ : syracuseStep 3009647 = 4514471) B4514471
theorem B2006431 : Blo 2005435 2006431 := bstep (se 1 (by rfl) ⟨1504823, by rfl⟩ : syracuseStep 2006431 = 3009647) B3009647
theorem B3009653 : Blo 2005435 3009653 := bbase (se 5 (by rfl) ⟨141077, by rfl⟩ : syracuseStep 3009653 = 282155) (by norm_num)
theorem B2006435 : Blo 2005435 2006435 := bstep (se 1 (by rfl) ⟨1504826, by rfl⟩ : syracuseStep 2006435 = 3009653) B3009653
theorem B3809101 : Blo 2005435 3809101 := bbase (se 3 (by rfl) ⟨714206, by rfl⟩ : syracuseStep 3809101 = 1428413) (by norm_num)
theorem B5078801 : Blo 2005435 5078801 := bstep (se 2 (by rfl) ⟨1904550, by rfl⟩ : syracuseStep 5078801 = 3809101) B3809101
theorem B3385867 : Blo 2005435 3385867 := bstep (se 1 (by rfl) ⟨2539400, by rfl⟩ : syracuseStep 3385867 = 5078801) B5078801
theorem B4514489 : Blo 2005435 4514489 := bstep (se 2 (by rfl) ⟨1692933, by rfl⟩ : syracuseStep 4514489 = 3385867) B3385867
theorem B3009659 : Blo 2005435 3009659 := bstep (se 1 (by rfl) ⟨2257244, by rfl⟩ : syracuseStep 3009659 = 4514489) B4514489
theorem B2006439 : Blo 2005435 2006439 := bstep (se 1 (by rfl) ⟨1504829, by rfl⟩ : syracuseStep 2006439 = 3009659) B3009659
theorem B2257249 : Blo 2005435 2257249 := bbase (se 2 (by rfl) ⟨846468, by rfl⟩ : syracuseStep 2257249 = 1692937) (by norm_num)
theorem B3009665 : Blo 2005435 3009665 := bstep (se 2 (by rfl) ⟨1128624, by rfl⟩ : syracuseStep 3009665 = 2257249) B2257249
theorem B2006443 : Blo 2005435 2006443 := bstep (se 1 (by rfl) ⟨1504832, by rfl⟩ : syracuseStep 2006443 = 3009665) B3009665
theorem B5078821 : Blo 2005435 5078821 := bbase (se 4 (by rfl) ⟨476139, by rfl⟩ : syracuseStep 5078821 = 952279) (by norm_num)
theorem B6771761 : Blo 2005435 6771761 := bstep (se 2 (by rfl) ⟨2539410, by rfl⟩ : syracuseStep 6771761 = 5078821) B5078821
theorem B4514507 : Blo 2005435 4514507 := bstep (se 1 (by rfl) ⟨3385880, by rfl⟩ : syracuseStep 4514507 = 6771761) B6771761
theorem B3009671 : Blo 2005435 3009671 := bstep (se 1 (by rfl) ⟨2257253, by rfl⟩ : syracuseStep 3009671 = 4514507) B4514507
theorem B2006447 : Blo 2005435 2006447 := bstep (se 1 (by rfl) ⟨1504835, by rfl⟩ : syracuseStep 2006447 = 3009671) B3009671
theorem B3009677 : Blo 2005435 3009677 := bbase (se 3 (by rfl) ⟨564314, by rfl⟩ : syracuseStep 3009677 = 1128629) (by norm_num)
theorem B2006451 : Blo 2005435 2006451 := bstep (se 1 (by rfl) ⟨1504838, by rfl⟩ : syracuseStep 2006451 = 3009677) B3009677
theorem B4514525 : Blo 2005435 4514525 := bbase (se 3 (by rfl) ⟨846473, by rfl⟩ : syracuseStep 4514525 = 1692947) (by norm_num)
theorem B3009683 : Blo 2005435 3009683 := bstep (se 1 (by rfl) ⟨2257262, by rfl⟩ : syracuseStep 3009683 = 4514525) B4514525
theorem B2006455 : Blo 2005435 2006455 := bstep (se 1 (by rfl) ⟨1504841, by rfl⟩ : syracuseStep 2006455 = 3009683) B3009683
theorem B3385901 : Blo 2005435 3385901 := bbase (se 3 (by rfl) ⟨634856, by rfl⟩ : syracuseStep 3385901 = 1269713) (by norm_num)
theorem B2257267 : Blo 2005435 2257267 := bstep (se 1 (by rfl) ⟨1692950, by rfl⟩ : syracuseStep 2257267 = 3385901) B3385901
theorem B3009689 : Blo 2005435 3009689 := bstep (se 2 (by rfl) ⟨1128633, by rfl⟩ : syracuseStep 3009689 = 2257267) B2257267
theorem B2006459 : Blo 2005435 2006459 := bstep (se 1 (by rfl) ⟨1504844, by rfl⟩ : syracuseStep 2006459 = 3009689) B3009689
theorem B3665045 : Blo 2005435 3665045 := bbase (se 6 (by rfl) ⟨85899, by rfl⟩ : syracuseStep 3665045 = 171799) (by norm_num)
theorem B9773453 : Blo 2005435 9773453 := bstep (se 3 (by rfl) ⟨1832522, by rfl⟩ : syracuseStep 9773453 = 3665045) B3665045
theorem B6515635 : Blo 2005435 6515635 := bstep (se 1 (by rfl) ⟨4886726, by rfl⟩ : syracuseStep 6515635 = 9773453) B9773453
theorem B8687513 : Blo 2005435 8687513 := bstep (se 2 (by rfl) ⟨3257817, by rfl⟩ : syracuseStep 8687513 = 6515635) B6515635
theorem B5791675 : Blo 2005435 5791675 := bstep (se 1 (by rfl) ⟨4343756, by rfl⟩ : syracuseStep 5791675 = 8687513) B8687513
theorem B7722233 : Blo 2005435 7722233 := bstep (se 2 (by rfl) ⟨2895837, by rfl⟩ : syracuseStep 7722233 = 5791675) B5791675
theorem B5148155 : Blo 2005435 5148155 := bstep (se 1 (by rfl) ⟨3861116, by rfl⟩ : syracuseStep 5148155 = 7722233) B7722233
theorem B13728413 : Blo 2005435 13728413 := bstep (se 3 (by rfl) ⟨2574077, by rfl⟩ : syracuseStep 13728413 = 5148155) B5148155
theorem B9152275 : Blo 2005435 9152275 := bstep (se 1 (by rfl) ⟨6864206, by rfl⟩ : syracuseStep 9152275 = 13728413) B13728413
theorem B12203033 : Blo 2005435 12203033 := bstep (se 2 (by rfl) ⟨4576137, by rfl⟩ : syracuseStep 12203033 = 9152275) B9152275
theorem B32541421 : Blo 2005435 32541421 := bstep (se 3 (by rfl) ⟨6101516, by rfl⟩ : syracuseStep 32541421 = 12203033) B12203033
theorem B43388561 : Blo 2005435 43388561 := bstep (se 2 (by rfl) ⟨16270710, by rfl⟩ : syracuseStep 43388561 = 32541421) B32541421
theorem B28925707 : Blo 2005435 28925707 := bstep (se 1 (by rfl) ⟨21694280, by rfl⟩ : syracuseStep 28925707 = 43388561) B43388561
theorem B38567609 : Blo 2005435 38567609 := bstep (se 2 (by rfl) ⟨14462853, by rfl⟩ : syracuseStep 38567609 = 28925707) B28925707
theorem B25711739 : Blo 2005435 25711739 := bstep (se 1 (by rfl) ⟨19283804, by rfl⟩ : syracuseStep 25711739 = 38567609) B38567609
theorem B17141159 : Blo 2005435 17141159 := bstep (se 1 (by rfl) ⟨12855869, by rfl⟩ : syracuseStep 17141159 = 25711739) B25711739
theorem B11427439 : Blo 2005435 11427439 := bstep (se 1 (by rfl) ⟨8570579, by rfl⟩ : syracuseStep 11427439 = 17141159) B17141159
theorem B15236585 : Blo 2005435 15236585 := bstep (se 2 (by rfl) ⟨5713719, by rfl⟩ : syracuseStep 15236585 = 11427439) B11427439
theorem B10157723 : Blo 2005435 10157723 := bstep (se 1 (by rfl) ⟨7618292, by rfl⟩ : syracuseStep 10157723 = 15236585) B15236585
theorem B6771815 : Blo 2005435 6771815 := bstep (se 1 (by rfl) ⟨5078861, by rfl⟩ : syracuseStep 6771815 = 10157723) B10157723
theorem B4514543 : Blo 2005435 4514543 := bstep (se 1 (by rfl) ⟨3385907, by rfl⟩ : syracuseStep 4514543 = 6771815) B6771815
theorem B3009695 : Blo 2005435 3009695 := bstep (se 1 (by rfl) ⟨2257271, by rfl⟩ : syracuseStep 3009695 = 4514543) B4514543
theorem B2006463 : Blo 2005435 2006463 := bstep (se 1 (by rfl) ⟨1504847, by rfl⟩ : syracuseStep 2006463 = 3009695) B3009695
theorem B3009701 : Blo 2005435 3009701 := bbase (se 4 (by rfl) ⟨282159, by rfl⟩ : syracuseStep 3009701 = 564319) (by norm_num)
theorem B2006467 : Blo 2005435 2006467 := bstep (se 1 (by rfl) ⟨1504850, by rfl⟩ : syracuseStep 2006467 = 3009701) B3009701
theorem B2539441 : Blo 2005435 2539441 := bbase (se 2 (by rfl) ⟨952290, by rfl⟩ : syracuseStep 2539441 = 1904581) (by norm_num)
theorem B3385921 : Blo 2005435 3385921 := bstep (se 2 (by rfl) ⟨1269720, by rfl⟩ : syracuseStep 3385921 = 2539441) B2539441
theorem B4514561 : Blo 2005435 4514561 := bstep (se 2 (by rfl) ⟨1692960, by rfl⟩ : syracuseStep 4514561 = 3385921) B3385921
theorem B3009707 : Blo 2005435 3009707 := bstep (se 1 (by rfl) ⟨2257280, by rfl⟩ : syracuseStep 3009707 = 4514561) B4514561
theorem B2006471 : Blo 2005435 2006471 := bstep (se 1 (by rfl) ⟨1504853, by rfl⟩ : syracuseStep 2006471 = 3009707) B3009707
theorem B2257285 : Blo 2005435 2257285 := bbase (se 4 (by rfl) ⟨211620, by rfl⟩ : syracuseStep 2257285 = 423241) (by norm_num)
theorem B3009713 : Blo 2005435 3009713 := bstep (se 2 (by rfl) ⟨1128642, by rfl⟩ : syracuseStep 3009713 = 2257285) B2257285
theorem B2006475 : Blo 2005435 2006475 := bstep (se 1 (by rfl) ⟨1504856, by rfl⟩ : syracuseStep 2006475 = 3009713) B3009713
theorem B4285325 : Blo 2005435 4285325 := bbase (se 3 (by rfl) ⟨803498, by rfl⟩ : syracuseStep 4285325 = 1606997) (by norm_num)
theorem B2856883 : Blo 2005435 2856883 := bstep (se 1 (by rfl) ⟨2142662, by rfl⟩ : syracuseStep 2856883 = 4285325) B4285325
theorem B3809177 : Blo 2005435 3809177 := bstep (se 2 (by rfl) ⟨1428441, by rfl⟩ : syracuseStep 3809177 = 2856883) B2856883
theorem B2539451 : Blo 2005435 2539451 := bstep (se 1 (by rfl) ⟨1904588, by rfl⟩ : syracuseStep 2539451 = 3809177) B3809177
theorem B6771869 : Blo 2005435 6771869 := bstep (se 3 (by rfl) ⟨1269725, by rfl⟩ : syracuseStep 6771869 = 2539451) B2539451
theorem B4514579 : Blo 2005435 4514579 := bstep (se 1 (by rfl) ⟨3385934, by rfl⟩ : syracuseStep 4514579 = 6771869) B6771869
theorem B3009719 : Blo 2005435 3009719 := bstep (se 1 (by rfl) ⟨2257289, by rfl⟩ : syracuseStep 3009719 = 4514579) B4514579
theorem B2006479 : Blo 2005435 2006479 := bstep (se 1 (by rfl) ⟨1504859, by rfl⟩ : syracuseStep 2006479 = 3009719) B3009719
theorem B3009725 : Blo 2005435 3009725 := bbase (se 3 (by rfl) ⟨564323, by rfl⟩ : syracuseStep 3009725 = 1128647) (by norm_num)
theorem B2006483 : Blo 2005435 2006483 := bstep (se 1 (by rfl) ⟨1504862, by rfl⟩ : syracuseStep 2006483 = 3009725) B3009725
theorem B4514597 : Blo 2005435 4514597 := bbase (se 4 (by rfl) ⟨423243, by rfl⟩ : syracuseStep 4514597 = 846487) (by norm_num)
theorem B3009731 : Blo 2005435 3009731 := bstep (se 1 (by rfl) ⟨2257298, by rfl⟩ : syracuseStep 3009731 = 4514597) B4514597
theorem B2006487 : Blo 2005435 2006487 := bstep (se 1 (by rfl) ⟨1504865, by rfl⟩ : syracuseStep 2006487 = 3009731) B3009731
theorem B5078933 : Blo 2005435 5078933 := bbase (se 6 (by rfl) ⟨119037, by rfl⟩ : syracuseStep 5078933 = 238075) (by norm_num)
theorem B3385955 : Blo 2005435 3385955 := bstep (se 1 (by rfl) ⟨2539466, by rfl⟩ : syracuseStep 3385955 = 5078933) B5078933
theorem B2257303 : Blo 2005435 2257303 := bstep (se 1 (by rfl) ⟨1692977, by rfl⟩ : syracuseStep 2257303 = 3385955) B3385955
theorem B3009737 : Blo 2005435 3009737 := bstep (se 2 (by rfl) ⟨1128651, by rfl⟩ : syracuseStep 3009737 = 2257303) B2257303
theorem B2006491 : Blo 2005435 2006491 := bstep (se 1 (by rfl) ⟨1504868, by rfl⟩ : syracuseStep 2006491 = 3009737) B3009737
theorem B4821029 : Blo 2005435 4821029 := bbase (se 4 (by rfl) ⟨451971, by rfl⟩ : syracuseStep 4821029 = 903943) (by norm_num)
theorem B3214019 : Blo 2005435 3214019 := bstep (se 1 (by rfl) ⟨2410514, by rfl⟩ : syracuseStep 3214019 = 4821029) B4821029
theorem B8570717 : Blo 2005435 8570717 := bstep (se 3 (by rfl) ⟨1607009, by rfl⟩ : syracuseStep 8570717 = 3214019) B3214019
theorem B5713811 : Blo 2005435 5713811 := bstep (se 1 (by rfl) ⟨4285358, by rfl⟩ : syracuseStep 5713811 = 8570717) B8570717
theorem B3809207 : Blo 2005435 3809207 := bstep (se 1 (by rfl) ⟨2856905, by rfl⟩ : syracuseStep 3809207 = 5713811) B5713811
theorem B10157885 : Blo 2005435 10157885 := bstep (se 3 (by rfl) ⟨1904603, by rfl⟩ : syracuseStep 10157885 = 3809207) B3809207
theorem B6771923 : Blo 2005435 6771923 := bstep (se 1 (by rfl) ⟨5078942, by rfl⟩ : syracuseStep 6771923 = 10157885) B10157885
theorem B4514615 : Blo 2005435 4514615 := bstep (se 1 (by rfl) ⟨3385961, by rfl⟩ : syracuseStep 4514615 = 6771923) B6771923
theorem B3009743 : Blo 2005435 3009743 := bstep (se 1 (by rfl) ⟨2257307, by rfl⟩ : syracuseStep 3009743 = 4514615) B4514615
theorem B2006495 : Blo 2005435 2006495 := bstep (se 1 (by rfl) ⟨1504871, by rfl⟩ : syracuseStep 2006495 = 3009743) B3009743
theorem B3009749 : Blo 2005435 3009749 := bbase (se 7 (by rfl) ⟨35270, by rfl⟩ : syracuseStep 3009749 = 70541) (by norm_num)
theorem B2006499 : Blo 2005435 2006499 := bstep (se 1 (by rfl) ⟨1504874, by rfl⟩ : syracuseStep 2006499 = 3009749) B3009749
theorem B2856917 : Blo 2005435 2856917 := bbase (se 7 (by rfl) ⟨33479, by rfl⟩ : syracuseStep 2856917 = 66959) (by norm_num)
theorem B7618445 : Blo 2005435 7618445 := bstep (se 3 (by rfl) ⟨1428458, by rfl⟩ : syracuseStep 7618445 = 2856917) B2856917
theorem B5078963 : Blo 2005435 5078963 := bstep (se 1 (by rfl) ⟨3809222, by rfl⟩ : syracuseStep 5078963 = 7618445) B7618445
theorem B3385975 : Blo 2005435 3385975 := bstep (se 1 (by rfl) ⟨2539481, by rfl⟩ : syracuseStep 3385975 = 5078963) B5078963
theorem B4514633 : Blo 2005435 4514633 := bstep (se 2 (by rfl) ⟨1692987, by rfl⟩ : syracuseStep 4514633 = 3385975) B3385975
theorem B3009755 : Blo 2005435 3009755 := bstep (se 1 (by rfl) ⟨2257316, by rfl⟩ : syracuseStep 3009755 = 4514633) B4514633
theorem B2006503 : Blo 2005435 2006503 := bstep (se 1 (by rfl) ⟨1504877, by rfl⟩ : syracuseStep 2006503 = 3009755) B3009755
theorem B2257321 : Blo 2005435 2257321 := bbase (se 2 (by rfl) ⟨846495, by rfl⟩ : syracuseStep 2257321 = 1692991) (by norm_num)
theorem B3009761 : Blo 2005435 3009761 := bstep (se 2 (by rfl) ⟨1128660, by rfl⟩ : syracuseStep 3009761 = 2257321) B2257321
theorem B2006507 : Blo 2005435 2006507 := bstep (se 1 (by rfl) ⟨1504880, by rfl⟩ : syracuseStep 2006507 = 3009761) B3009761
theorem B5423701 : Blo 2005435 5423701 := bbase (se 8 (by rfl) ⟨31779, by rfl⟩ : syracuseStep 5423701 = 63559) (by norm_num)
theorem B7231601 : Blo 2005435 7231601 := bstep (se 2 (by rfl) ⟨2711850, by rfl⟩ : syracuseStep 7231601 = 5423701) B5423701
theorem B4821067 : Blo 2005435 4821067 := bstep (se 1 (by rfl) ⟨3615800, by rfl⟩ : syracuseStep 4821067 = 7231601) B7231601
theorem B6428089 : Blo 2005435 6428089 := bstep (se 2 (by rfl) ⟨2410533, by rfl⟩ : syracuseStep 6428089 = 4821067) B4821067
theorem B8570785 : Blo 2005435 8570785 := bstep (se 2 (by rfl) ⟨3214044, by rfl⟩ : syracuseStep 8570785 = 6428089) B6428089
theorem B11427713 : Blo 2005435 11427713 := bstep (se 2 (by rfl) ⟨4285392, by rfl⟩ : syracuseStep 11427713 = 8570785) B8570785
theorem B7618475 : Blo 2005435 7618475 := bstep (se 1 (by rfl) ⟨5713856, by rfl⟩ : syracuseStep 7618475 = 11427713) B11427713
theorem B5078983 : Blo 2005435 5078983 := bstep (se 1 (by rfl) ⟨3809237, by rfl⟩ : syracuseStep 5078983 = 7618475) B7618475
theorem B6771977 : Blo 2005435 6771977 := bstep (se 2 (by rfl) ⟨2539491, by rfl⟩ : syracuseStep 6771977 = 5078983) B5078983
theorem B4514651 : Blo 2005435 4514651 := bstep (se 1 (by rfl) ⟨3385988, by rfl⟩ : syracuseStep 4514651 = 6771977) B6771977
theorem B3009767 : Blo 2005435 3009767 := bstep (se 1 (by rfl) ⟨2257325, by rfl⟩ : syracuseStep 3009767 = 4514651) B4514651
theorem B2006511 : Blo 2005435 2006511 := bstep (se 1 (by rfl) ⟨1504883, by rfl⟩ : syracuseStep 2006511 = 3009767) B3009767
theorem B3009773 : Blo 2005435 3009773 := bbase (se 3 (by rfl) ⟨564332, by rfl⟩ : syracuseStep 3009773 = 1128665) (by norm_num)
theorem B2006515 : Blo 2005435 2006515 := bstep (se 1 (by rfl) ⟨1504886, by rfl⟩ : syracuseStep 2006515 = 3009773) B3009773
theorem B4514669 : Blo 2005435 4514669 := bbase (se 3 (by rfl) ⟨846500, by rfl⟩ : syracuseStep 4514669 = 1693001) (by norm_num)
theorem B3009779 : Blo 2005435 3009779 := bstep (se 1 (by rfl) ⟨2257334, by rfl⟩ : syracuseStep 3009779 = 4514669) B4514669
theorem B2006519 : Blo 2005435 2006519 := bstep (se 1 (by rfl) ⟨1504889, by rfl⟩ : syracuseStep 2006519 = 3009779) B3009779
theorem B3809261 : Blo 2005435 3809261 := bbase (se 3 (by rfl) ⟨714236, by rfl⟩ : syracuseStep 3809261 = 1428473) (by norm_num)
theorem B2539507 : Blo 2005435 2539507 := bstep (se 1 (by rfl) ⟨1904630, by rfl⟩ : syracuseStep 2539507 = 3809261) B3809261
theorem B3386009 : Blo 2005435 3386009 := bstep (se 2 (by rfl) ⟨1269753, by rfl⟩ : syracuseStep 3386009 = 2539507) B2539507
theorem B2257339 : Blo 2005435 2257339 := bstep (se 1 (by rfl) ⟨1693004, by rfl⟩ : syracuseStep 2257339 = 3386009) B3386009
theorem B3009785 : Blo 2005435 3009785 := bstep (se 2 (by rfl) ⟨1128669, by rfl⟩ : syracuseStep 3009785 = 2257339) B2257339
theorem B2006523 : Blo 2005435 2006523 := bstep (se 1 (by rfl) ⟨1504892, by rfl⟩ : syracuseStep 2006523 = 3009785) B3009785
theorem B2236285 : Blo 2005435 2236285 := bbase (se 3 (by rfl) ⟨419303, by rfl⟩ : syracuseStep 2236285 = 838607) (by norm_num)
theorem B2981713 : Blo 2005435 2981713 := bstep (se 2 (by rfl) ⟨1118142, by rfl⟩ : syracuseStep 2981713 = 2236285) B2236285
theorem B3975617 : Blo 2005435 3975617 := bstep (se 2 (by rfl) ⟨1490856, by rfl⟩ : syracuseStep 3975617 = 2981713) B2981713
theorem B2650411 : Blo 2005435 2650411 := bstep (se 1 (by rfl) ⟨1987808, by rfl⟩ : syracuseStep 2650411 = 3975617) B3975617
theorem B3533881 : Blo 2005435 3533881 := bstep (se 2 (by rfl) ⟨1325205, by rfl⟩ : syracuseStep 3533881 = 2650411) B2650411
theorem B4711841 : Blo 2005435 4711841 := bstep (se 2 (by rfl) ⟨1766940, by rfl⟩ : syracuseStep 4711841 = 3533881) B3533881
theorem B3141227 : Blo 2005435 3141227 := bstep (se 1 (by rfl) ⟨2355920, by rfl⟩ : syracuseStep 3141227 = 4711841) B4711841
theorem B8376605 : Blo 2005435 8376605 := bstep (se 3 (by rfl) ⟨1570613, by rfl⟩ : syracuseStep 8376605 = 3141227) B3141227
theorem B5584403 : Blo 2005435 5584403 := bstep (se 1 (by rfl) ⟨4188302, by rfl⟩ : syracuseStep 5584403 = 8376605) B8376605
theorem B3722935 : Blo 2005435 3722935 := bstep (se 1 (by rfl) ⟨2792201, by rfl⟩ : syracuseStep 3722935 = 5584403) B5584403
theorem B4963913 : Blo 2005435 4963913 := bstep (se 2 (by rfl) ⟨1861467, by rfl⟩ : syracuseStep 4963913 = 3722935) B3722935
theorem B3309275 : Blo 2005435 3309275 := bstep (se 1 (by rfl) ⟨2481956, by rfl⟩ : syracuseStep 3309275 = 4963913) B4963913
theorem B8824733 : Blo 2005435 8824733 := bstep (se 3 (by rfl) ⟨1654637, by rfl⟩ : syracuseStep 8824733 = 3309275) B3309275
theorem B5883155 : Blo 2005435 5883155 := bstep (se 1 (by rfl) ⟨4412366, by rfl⟩ : syracuseStep 5883155 = 8824733) B8824733
theorem B3922103 : Blo 2005435 3922103 := bstep (se 1 (by rfl) ⟨2941577, by rfl⟩ : syracuseStep 3922103 = 5883155) B5883155
theorem B2614735 : Blo 2005435 2614735 := bstep (se 1 (by rfl) ⟨1961051, by rfl⟩ : syracuseStep 2614735 = 3922103) B3922103
theorem B3486313 : Blo 2005435 3486313 := bstep (se 2 (by rfl) ⟨1307367, by rfl⟩ : syracuseStep 3486313 = 2614735) B2614735
theorem B4648417 : Blo 2005435 4648417 := bstep (se 2 (by rfl) ⟨1743156, by rfl⟩ : syracuseStep 4648417 = 3486313) B3486313
theorem B24791557 : Blo 2005435 24791557 := bstep (se 4 (by rfl) ⟨2324208, by rfl⟩ : syracuseStep 24791557 = 4648417) B4648417
theorem B33055409 : Blo 2005435 33055409 := bstep (se 2 (by rfl) ⟨12395778, by rfl⟩ : syracuseStep 33055409 = 24791557) B24791557
theorem B88147757 : Blo 2005435 88147757 := bstep (se 3 (by rfl) ⟨16527704, by rfl⟩ : syracuseStep 88147757 = 33055409) B33055409
theorem B58765171 : Blo 2005435 58765171 := bstep (se 1 (by rfl) ⟨44073878, by rfl⟩ : syracuseStep 58765171 = 88147757) B88147757
theorem B78353561 : Blo 2005435 78353561 := bstep (se 2 (by rfl) ⟨29382585, by rfl⟩ : syracuseStep 78353561 = 58765171) B58765171
theorem B52235707 : Blo 2005435 52235707 := bstep (se 1 (by rfl) ⟨39176780, by rfl⟩ : syracuseStep 52235707 = 78353561) B78353561
theorem B69647609 : Blo 2005435 69647609 := bstep (se 2 (by rfl) ⟨26117853, by rfl⟩ : syracuseStep 69647609 = 52235707) B52235707
theorem B46431739 : Blo 2005435 46431739 := bstep (se 1 (by rfl) ⟨34823804, by rfl⟩ : syracuseStep 46431739 = 69647609) B69647609
theorem B61908985 : Blo 2005435 61908985 := bstep (se 2 (by rfl) ⟨23215869, by rfl⟩ : syracuseStep 61908985 = 46431739) B46431739
theorem B82545313 : Blo 2005435 82545313 := bstep (se 2 (by rfl) ⟨30954492, by rfl⟩ : syracuseStep 82545313 = 61908985) B61908985
theorem B110060417 : Blo 2005435 110060417 := bstep (se 2 (by rfl) ⟨41272656, by rfl⟩ : syracuseStep 110060417 = 82545313) B82545313
theorem B73373611 : Blo 2005435 73373611 := bstep (se 1 (by rfl) ⟨55030208, by rfl⟩ : syracuseStep 73373611 = 110060417) B110060417
theorem B97831481 : Blo 2005435 97831481 := bstep (se 2 (by rfl) ⟨36686805, by rfl⟩ : syracuseStep 97831481 = 73373611) B73373611
theorem B1043535797 : Blo 2005435 1043535797 := bstep (se 5 (by rfl) ⟨48915740, by rfl⟩ : syracuseStep 1043535797 = 97831481) B97831481
theorem B695690531 : Blo 2005435 695690531 := bstep (se 1 (by rfl) ⟨521767898, by rfl⟩ : syracuseStep 695690531 = 1043535797) B1043535797
theorem B463793687 : Blo 2005435 463793687 := bstep (se 1 (by rfl) ⟨347845265, by rfl⟩ : syracuseStep 463793687 = 695690531) B695690531
theorem B309195791 : Blo 2005435 309195791 := bstep (se 1 (by rfl) ⟨231896843, by rfl⟩ : syracuseStep 309195791 = 463793687) B463793687
theorem B206130527 : Blo 2005435 206130527 := bstep (se 1 (by rfl) ⟨154597895, by rfl⟩ : syracuseStep 206130527 = 309195791) B309195791
theorem B137420351 : Blo 2005435 137420351 := bstep (se 1 (by rfl) ⟨103065263, by rfl⟩ : syracuseStep 137420351 = 206130527) B206130527
theorem B91613567 : Blo 2005435 91613567 := bstep (se 1 (by rfl) ⟨68710175, by rfl⟩ : syracuseStep 91613567 = 137420351) B137420351
theorem B61075711 : Blo 2005435 61075711 := bstep (se 1 (by rfl) ⟨45806783, by rfl⟩ : syracuseStep 61075711 = 91613567) B91613567
theorem B81434281 : Blo 2005435 81434281 := bstep (se 2 (by rfl) ⟨30537855, by rfl⟩ : syracuseStep 81434281 = 61075711) B61075711
theorem B108579041 : Blo 2005435 108579041 := bstep (se 2 (by rfl) ⟨40717140, by rfl⟩ : syracuseStep 108579041 = 81434281) B81434281
theorem B72386027 : Blo 2005435 72386027 := bstep (se 1 (by rfl) ⟨54289520, by rfl⟩ : syracuseStep 72386027 = 108579041) B108579041
theorem B48257351 : Blo 2005435 48257351 := bstep (se 1 (by rfl) ⟨36193013, by rfl⟩ : syracuseStep 48257351 = 72386027) B72386027
theorem B32171567 : Blo 2005435 32171567 := bstep (se 1 (by rfl) ⟨24128675, by rfl⟩ : syracuseStep 32171567 = 48257351) B48257351
theorem B85790845 : Blo 2005435 85790845 := bstep (se 3 (by rfl) ⟨16085783, by rfl⟩ : syracuseStep 85790845 = 32171567) B32171567
theorem B457551173 : Blo 2005435 457551173 := bstep (se 4 (by rfl) ⟨42895422, by rfl⟩ : syracuseStep 457551173 = 85790845) B85790845
theorem B305034115 : Blo 2005435 305034115 := bstep (se 1 (by rfl) ⟨228775586, by rfl⟩ : syracuseStep 305034115 = 457551173) B457551173
theorem B406712153 : Blo 2005435 406712153 := bstep (se 2 (by rfl) ⟨152517057, by rfl⟩ : syracuseStep 406712153 = 305034115) B305034115
theorem B271141435 : Blo 2005435 271141435 := bstep (se 1 (by rfl) ⟨203356076, by rfl⟩ : syracuseStep 271141435 = 406712153) B406712153
theorem B1446087653 : Blo 2005435 1446087653 := bstep (se 4 (by rfl) ⟨135570717, by rfl⟩ : syracuseStep 1446087653 = 271141435) B271141435
theorem B964058435 : Blo 2005435 964058435 := bstep (se 1 (by rfl) ⟨723043826, by rfl⟩ : syracuseStep 964058435 = 1446087653) B1446087653
theorem B642705623 : Blo 2005435 642705623 := bstep (se 1 (by rfl) ⟨482029217, by rfl⟩ : syracuseStep 642705623 = 964058435) B964058435
theorem B428470415 : Blo 2005435 428470415 := bstep (se 1 (by rfl) ⟨321352811, by rfl⟩ : syracuseStep 428470415 = 642705623) B642705623
theorem B285646943 : Blo 2005435 285646943 := bstep (se 1 (by rfl) ⟨214235207, by rfl⟩ : syracuseStep 285646943 = 428470415) B428470415
theorem B761725181 : Blo 2005435 761725181 := bstep (se 3 (by rfl) ⟨142823471, by rfl⟩ : syracuseStep 761725181 = 285646943) B285646943
theorem B507816787 : Blo 2005435 507816787 := bstep (se 1 (by rfl) ⟨380862590, by rfl⟩ : syracuseStep 507816787 = 761725181) B761725181
theorem B677089049 : Blo 2005435 677089049 := bstep (se 2 (by rfl) ⟨253908393, by rfl⟩ : syracuseStep 677089049 = 507816787) B507816787
theorem B1805570797 : Blo 2005435 1805570797 := bstep (se 3 (by rfl) ⟨338544524, by rfl⟩ : syracuseStep 1805570797 = 677089049) B677089049
theorem B2407427729 : Blo 2005435 2407427729 := bstep (se 2 (by rfl) ⟨902785398, by rfl⟩ : syracuseStep 2407427729 = 1805570797) B1805570797
theorem B1604951819 : Blo 2005435 1604951819 := bstep (se 1 (by rfl) ⟨1203713864, by rfl⟩ : syracuseStep 1604951819 = 2407427729) B2407427729
theorem B1069967879 : Blo 2005435 1069967879 := bstep (se 1 (by rfl) ⟨802475909, by rfl⟩ : syracuseStep 1069967879 = 1604951819) B1604951819
theorem B713311919 : Blo 2005435 713311919 := bstep (se 1 (by rfl) ⟨534983939, by rfl⟩ : syracuseStep 713311919 = 1069967879) B1069967879
theorem B475541279 : Blo 2005435 475541279 := bstep (se 1 (by rfl) ⟨356655959, by rfl⟩ : syracuseStep 475541279 = 713311919) B713311919
theorem B317027519 : Blo 2005435 317027519 := bstep (se 1 (by rfl) ⟨237770639, by rfl⟩ : syracuseStep 317027519 = 475541279) B475541279
theorem B211351679 : Blo 2005435 211351679 := bstep (se 1 (by rfl) ⟨158513759, by rfl⟩ : syracuseStep 211351679 = 317027519) B317027519
theorem B140901119 : Blo 2005435 140901119 := bstep (se 1 (by rfl) ⟨105675839, by rfl⟩ : syracuseStep 140901119 = 211351679) B211351679
theorem B93934079 : Blo 2005435 93934079 := bstep (se 1 (by rfl) ⟨70450559, by rfl⟩ : syracuseStep 93934079 = 140901119) B140901119
theorem B62622719 : Blo 2005435 62622719 := bstep (se 1 (by rfl) ⟨46967039, by rfl⟩ : syracuseStep 62622719 = 93934079) B93934079
theorem B41748479 : Blo 2005435 41748479 := bstep (se 1 (by rfl) ⟨31311359, by rfl⟩ : syracuseStep 41748479 = 62622719) B62622719
theorem B27832319 : Blo 2005435 27832319 := bstep (se 1 (by rfl) ⟨20874239, by rfl⟩ : syracuseStep 27832319 = 41748479) B41748479
theorem B18554879 : Blo 2005435 18554879 := bstep (se 1 (by rfl) ⟨13916159, by rfl⟩ : syracuseStep 18554879 = 27832319) B27832319
theorem B12369919 : Blo 2005435 12369919 := bstep (se 1 (by rfl) ⟨9277439, by rfl⟩ : syracuseStep 12369919 = 18554879) B18554879
theorem B16493225 : Blo 2005435 16493225 := bstep (se 2 (by rfl) ⟨6184959, by rfl⟩ : syracuseStep 16493225 = 12369919) B12369919
theorem B175927733 : Blo 2005435 175927733 := bstep (se 5 (by rfl) ⟨8246612, by rfl⟩ : syracuseStep 175927733 = 16493225) B16493225
theorem B117285155 : Blo 2005435 117285155 := bstep (se 1 (by rfl) ⟨87963866, by rfl⟩ : syracuseStep 117285155 = 175927733) B175927733
theorem B78190103 : Blo 2005435 78190103 := bstep (se 1 (by rfl) ⟨58642577, by rfl⟩ : syracuseStep 78190103 = 117285155) B117285155
theorem B52126735 : Blo 2005435 52126735 := bstep (se 1 (by rfl) ⟨39095051, by rfl⟩ : syracuseStep 52126735 = 78190103) B78190103
theorem B69502313 : Blo 2005435 69502313 := bstep (se 2 (by rfl) ⟨26063367, by rfl⟩ : syracuseStep 69502313 = 52126735) B52126735
theorem B46334875 : Blo 2005435 46334875 := bstep (se 1 (by rfl) ⟨34751156, by rfl⟩ : syracuseStep 46334875 = 69502313) B69502313
theorem B61779833 : Blo 2005435 61779833 := bstep (se 2 (by rfl) ⟨23167437, by rfl⟩ : syracuseStep 61779833 = 46334875) B46334875
theorem B41186555 : Blo 2005435 41186555 := bstep (se 1 (by rfl) ⟨30889916, by rfl⟩ : syracuseStep 41186555 = 61779833) B61779833
theorem B27457703 : Blo 2005435 27457703 := bstep (se 1 (by rfl) ⟨20593277, by rfl⟩ : syracuseStep 27457703 = 41186555) B41186555
theorem B18305135 : Blo 2005435 18305135 := bstep (se 1 (by rfl) ⟨13728851, by rfl⟩ : syracuseStep 18305135 = 27457703) B27457703
theorem B12203423 : Blo 2005435 12203423 := bstep (se 1 (by rfl) ⟨9152567, by rfl⟩ : syracuseStep 12203423 = 18305135) B18305135
theorem B8135615 : Blo 2005435 8135615 := bstep (se 1 (by rfl) ⟨6101711, by rfl⟩ : syracuseStep 8135615 = 12203423) B12203423
theorem B5423743 : Blo 2005435 5423743 := bstep (se 1 (by rfl) ⟨4067807, by rfl⟩ : syracuseStep 5423743 = 8135615) B8135615
theorem B28926629 : Blo 2005435 28926629 := bstep (se 4 (by rfl) ⟨2711871, by rfl⟩ : syracuseStep 28926629 = 5423743) B5423743
theorem B19284419 : Blo 2005435 19284419 := bstep (se 1 (by rfl) ⟨14463314, by rfl⟩ : syracuseStep 19284419 = 28926629) B28926629
theorem B51425117 : Blo 2005435 51425117 := bstep (se 3 (by rfl) ⟨9642209, by rfl⟩ : syracuseStep 51425117 = 19284419) B19284419
theorem B34283411 : Blo 2005435 34283411 := bstep (se 1 (by rfl) ⟨25712558, by rfl⟩ : syracuseStep 34283411 = 51425117) B51425117
theorem B22855607 : Blo 2005435 22855607 := bstep (se 1 (by rfl) ⟨17141705, by rfl⟩ : syracuseStep 22855607 = 34283411) B34283411
theorem B15237071 : Blo 2005435 15237071 := bstep (se 1 (by rfl) ⟨11427803, by rfl⟩ : syracuseStep 15237071 = 22855607) B22855607
theorem B10158047 : Blo 2005435 10158047 := bstep (se 1 (by rfl) ⟨7618535, by rfl⟩ : syracuseStep 10158047 = 15237071) B15237071
theorem B6772031 : Blo 2005435 6772031 := bstep (se 1 (by rfl) ⟨5079023, by rfl⟩ : syracuseStep 6772031 = 10158047) B10158047
theorem B4514687 : Blo 2005435 4514687 := bstep (se 1 (by rfl) ⟨3386015, by rfl⟩ : syracuseStep 4514687 = 6772031) B6772031
theorem B3009791 : Blo 2005435 3009791 := bstep (se 1 (by rfl) ⟨2257343, by rfl⟩ : syracuseStep 3009791 = 4514687) B4514687
theorem B2006527 : Blo 2005435 2006527 := bstep (se 1 (by rfl) ⟨1504895, by rfl⟩ : syracuseStep 2006527 = 3009791) B3009791
theorem B3009797 : Blo 2005435 3009797 := bbase (se 4 (by rfl) ⟨282168, by rfl⟩ : syracuseStep 3009797 = 564337) (by norm_num)
theorem B2006531 : Blo 2005435 2006531 := bstep (se 1 (by rfl) ⟨1504898, by rfl⟩ : syracuseStep 2006531 = 3009797) B3009797
theorem B3386029 : Blo 2005435 3386029 := bbase (se 3 (by rfl) ⟨634880, by rfl⟩ : syracuseStep 3386029 = 1269761) (by norm_num)
theorem B4514705 : Blo 2005435 4514705 := bstep (se 2 (by rfl) ⟨1693014, by rfl⟩ : syracuseStep 4514705 = 3386029) B3386029
theorem B3009803 : Blo 2005435 3009803 := bstep (se 1 (by rfl) ⟨2257352, by rfl⟩ : syracuseStep 3009803 = 4514705) B4514705
theorem B2006535 : Blo 2005435 2006535 := bstep (se 1 (by rfl) ⟨1504901, by rfl⟩ : syracuseStep 2006535 = 3009803) B3009803
theorem B2257357 : Blo 2005435 2257357 := bbase (se 3 (by rfl) ⟨423254, by rfl⟩ : syracuseStep 2257357 = 846509) (by norm_num)
theorem B3009809 : Blo 2005435 3009809 := bstep (se 2 (by rfl) ⟨1128678, by rfl⟩ : syracuseStep 3009809 = 2257357) B2257357
theorem B2006539 : Blo 2005435 2006539 := bstep (se 1 (by rfl) ⟨1504904, by rfl⟩ : syracuseStep 2006539 = 3009809) B3009809
theorem B6772085 : Blo 2005435 6772085 := bbase (se 5 (by rfl) ⟨317441, by rfl⟩ : syracuseStep 6772085 = 634883) (by norm_num)
theorem B4514723 : Blo 2005435 4514723 := bstep (se 1 (by rfl) ⟨3386042, by rfl⟩ : syracuseStep 4514723 = 6772085) B6772085
theorem B3009815 : Blo 2005435 3009815 := bstep (se 1 (by rfl) ⟨2257361, by rfl⟩ : syracuseStep 3009815 = 4514723) B4514723
theorem B2006543 : Blo 2005435 2006543 := bstep (se 1 (by rfl) ⟨1504907, by rfl⟩ : syracuseStep 2006543 = 3009815) B3009815
theorem B3009821 : Blo 2005435 3009821 := bbase (se 3 (by rfl) ⟨564341, by rfl⟩ : syracuseStep 3009821 = 1128683) (by norm_num)
theorem B2006547 : Blo 2005435 2006547 := bstep (se 1 (by rfl) ⟨1504910, by rfl⟩ : syracuseStep 2006547 = 3009821) B3009821
theorem B4514741 : Blo 2005435 4514741 := bbase (se 5 (by rfl) ⟨211628, by rfl⟩ : syracuseStep 4514741 = 423257) (by norm_num)
theorem B3009827 : Blo 2005435 3009827 := bstep (se 1 (by rfl) ⟨2257370, by rfl⟩ : syracuseStep 3009827 = 4514741) B4514741
theorem B2006551 : Blo 2005435 2006551 := bstep (se 1 (by rfl) ⟨1504913, by rfl⟩ : syracuseStep 2006551 = 3009827) B3009827
theorem B4576349 : Blo 2005435 4576349 := bbase (se 3 (by rfl) ⟨858065, by rfl⟩ : syracuseStep 4576349 = 1716131) (by norm_num)
theorem B12203597 : Blo 2005435 12203597 := bstep (se 3 (by rfl) ⟨2288174, by rfl⟩ : syracuseStep 12203597 = 4576349) B4576349
theorem B8135731 : Blo 2005435 8135731 := bstep (se 1 (by rfl) ⟨6101798, by rfl⟩ : syracuseStep 8135731 = 12203597) B12203597
theorem B10847641 : Blo 2005435 10847641 := bstep (se 2 (by rfl) ⟨4067865, by rfl⟩ : syracuseStep 10847641 = 8135731) B8135731
theorem B14463521 : Blo 2005435 14463521 := bstep (se 2 (by rfl) ⟨5423820, by rfl⟩ : syracuseStep 14463521 = 10847641) B10847641
theorem B9642347 : Blo 2005435 9642347 := bstep (se 1 (by rfl) ⟨7231760, by rfl⟩ : syracuseStep 9642347 = 14463521) B14463521
theorem B6428231 : Blo 2005435 6428231 := bstep (se 1 (by rfl) ⟨4821173, by rfl⟩ : syracuseStep 6428231 = 9642347) B9642347
theorem B4285487 : Blo 2005435 4285487 := bstep (se 1 (by rfl) ⟨3214115, by rfl⟩ : syracuseStep 4285487 = 6428231) B6428231
theorem B11427965 : Blo 2005435 11427965 := bstep (se 3 (by rfl) ⟨2142743, by rfl⟩ : syracuseStep 11427965 = 4285487) B4285487
theorem B7618643 : Blo 2005435 7618643 := bstep (se 1 (by rfl) ⟨5713982, by rfl⟩ : syracuseStep 7618643 = 11427965) B11427965
theorem B5079095 : Blo 2005435 5079095 := bstep (se 1 (by rfl) ⟨3809321, by rfl⟩ : syracuseStep 5079095 = 7618643) B7618643
theorem B3386063 : Blo 2005435 3386063 := bstep (se 1 (by rfl) ⟨2539547, by rfl⟩ : syracuseStep 3386063 = 5079095) B5079095
theorem B2257375 : Blo 2005435 2257375 := bstep (se 1 (by rfl) ⟨1693031, by rfl⟩ : syracuseStep 2257375 = 3386063) B3386063
theorem B3009833 : Blo 2005435 3009833 := bstep (se 2 (by rfl) ⟨1128687, by rfl⟩ : syracuseStep 3009833 = 2257375) B2257375
theorem B2006555 : Blo 2005435 2006555 := bstep (se 1 (by rfl) ⟨1504916, by rfl⟩ : syracuseStep 2006555 = 3009833) B3009833
theorem B3432269 : Blo 2005435 3432269 := bbase (se 3 (by rfl) ⟨643550, by rfl⟩ : syracuseStep 3432269 = 1287101) (by norm_num)
theorem B2288179 : Blo 2005435 2288179 := bstep (se 1 (by rfl) ⟨1716134, by rfl⟩ : syracuseStep 2288179 = 3432269) B3432269
theorem B12203621 : Blo 2005435 12203621 := bstep (se 4 (by rfl) ⟨1144089, by rfl⟩ : syracuseStep 12203621 = 2288179) B2288179
theorem B8135747 : Blo 2005435 8135747 := bstep (se 1 (by rfl) ⟨6101810, by rfl⟩ : syracuseStep 8135747 = 12203621) B12203621
theorem B5423831 : Blo 2005435 5423831 := bstep (se 1 (by rfl) ⟨4067873, by rfl⟩ : syracuseStep 5423831 = 8135747) B8135747
theorem B3615887 : Blo 2005435 3615887 := bstep (se 1 (by rfl) ⟨2711915, by rfl⟩ : syracuseStep 3615887 = 5423831) B5423831
theorem B9642365 : Blo 2005435 9642365 := bstep (se 3 (by rfl) ⟨1807943, by rfl⟩ : syracuseStep 9642365 = 3615887) B3615887
theorem B6428243 : Blo 2005435 6428243 := bstep (se 1 (by rfl) ⟨4821182, by rfl⟩ : syracuseStep 6428243 = 9642365) B9642365
theorem B4285495 : Blo 2005435 4285495 := bstep (se 1 (by rfl) ⟨3214121, by rfl⟩ : syracuseStep 4285495 = 6428243) B6428243
theorem B5713993 : Blo 2005435 5713993 := bstep (se 2 (by rfl) ⟨2142747, by rfl⟩ : syracuseStep 5713993 = 4285495) B4285495
theorem B7618657 : Blo 2005435 7618657 := bstep (se 2 (by rfl) ⟨2856996, by rfl⟩ : syracuseStep 7618657 = 5713993) B5713993
theorem B10158209 : Blo 2005435 10158209 := bstep (se 2 (by rfl) ⟨3809328, by rfl⟩ : syracuseStep 10158209 = 7618657) B7618657
theorem B6772139 : Blo 2005435 6772139 := bstep (se 1 (by rfl) ⟨5079104, by rfl⟩ : syracuseStep 6772139 = 10158209) B10158209
theorem B4514759 : Blo 2005435 4514759 := bstep (se 1 (by rfl) ⟨3386069, by rfl⟩ : syracuseStep 4514759 = 6772139) B6772139
theorem B3009839 : Blo 2005435 3009839 := bstep (se 1 (by rfl) ⟨2257379, by rfl⟩ : syracuseStep 3009839 = 4514759) B4514759
theorem B2006559 : Blo 2005435 2006559 := bstep (se 1 (by rfl) ⟨1504919, by rfl⟩ : syracuseStep 2006559 = 3009839) B3009839
theorem B3009845 : Blo 2005435 3009845 := bbase (se 5 (by rfl) ⟨141086, by rfl⟩ : syracuseStep 3009845 = 282173) (by norm_num)
theorem B2006563 : Blo 2005435 2006563 := bstep (se 1 (by rfl) ⟨1504922, by rfl⟩ : syracuseStep 2006563 = 3009845) B3009845
theorem B5079125 : Blo 2005435 5079125 := bbase (se 8 (by rfl) ⟨29760, by rfl⟩ : syracuseStep 5079125 = 59521) (by norm_num)
theorem B3386083 : Blo 2005435 3386083 := bstep (se 1 (by rfl) ⟨2539562, by rfl⟩ : syracuseStep 3386083 = 5079125) B5079125
theorem B4514777 : Blo 2005435 4514777 := bstep (se 2 (by rfl) ⟨1693041, by rfl⟩ : syracuseStep 4514777 = 3386083) B3386083
theorem B3009851 : Blo 2005435 3009851 := bstep (se 1 (by rfl) ⟨2257388, by rfl⟩ : syracuseStep 3009851 = 4514777) B4514777
theorem B2006567 : Blo 2005435 2006567 := bstep (se 1 (by rfl) ⟨1504925, by rfl⟩ : syracuseStep 2006567 = 3009851) B3009851
theorem B2257393 : Blo 2005435 2257393 := bbase (se 2 (by rfl) ⟨846522, by rfl⟩ : syracuseStep 2257393 = 1693045) (by norm_num)
theorem B3009857 : Blo 2005435 3009857 := bstep (se 2 (by rfl) ⟨1128696, by rfl⟩ : syracuseStep 3009857 = 2257393) B2257393
theorem B2006571 : Blo 2005435 2006571 := bstep (se 1 (by rfl) ⟨1504928, by rfl⟩ : syracuseStep 2006571 = 3009857) B3009857
theorem B4821221 : Blo 2005435 4821221 := bbase (se 4 (by rfl) ⟨451989, by rfl⟩ : syracuseStep 4821221 = 903979) (by norm_num)
theorem B12856589 : Blo 2005435 12856589 := bstep (se 3 (by rfl) ⟨2410610, by rfl⟩ : syracuseStep 12856589 = 4821221) B4821221
theorem B8571059 : Blo 2005435 8571059 := bstep (se 1 (by rfl) ⟨6428294, by rfl⟩ : syracuseStep 8571059 = 12856589) B12856589
theorem B5714039 : Blo 2005435 5714039 := bstep (se 1 (by rfl) ⟨4285529, by rfl⟩ : syracuseStep 5714039 = 8571059) B8571059
theorem B3809359 : Blo 2005435 3809359 := bstep (se 1 (by rfl) ⟨2857019, by rfl⟩ : syracuseStep 3809359 = 5714039) B5714039
theorem B5079145 : Blo 2005435 5079145 := bstep (se 2 (by rfl) ⟨1904679, by rfl⟩ : syracuseStep 5079145 = 3809359) B3809359
theorem B6772193 : Blo 2005435 6772193 := bstep (se 2 (by rfl) ⟨2539572, by rfl⟩ : syracuseStep 6772193 = 5079145) B5079145
theorem B4514795 : Blo 2005435 4514795 := bstep (se 1 (by rfl) ⟨3386096, by rfl⟩ : syracuseStep 4514795 = 6772193) B6772193
theorem B3009863 : Blo 2005435 3009863 := bstep (se 1 (by rfl) ⟨2257397, by rfl⟩ : syracuseStep 3009863 = 4514795) B4514795
theorem B2006575 : Blo 2005435 2006575 := bstep (se 1 (by rfl) ⟨1504931, by rfl⟩ : syracuseStep 2006575 = 3009863) B3009863
theorem B3009869 : Blo 2005435 3009869 := bbase (se 3 (by rfl) ⟨564350, by rfl⟩ : syracuseStep 3009869 = 1128701) (by norm_num)
theorem B2006579 : Blo 2005435 2006579 := bstep (se 1 (by rfl) ⟨1504934, by rfl⟩ : syracuseStep 2006579 = 3009869) B3009869
theorem B4514813 : Blo 2005435 4514813 := bbase (se 3 (by rfl) ⟨846527, by rfl⟩ : syracuseStep 4514813 = 1693055) (by norm_num)
theorem B3009875 : Blo 2005435 3009875 := bstep (se 1 (by rfl) ⟨2257406, by rfl⟩ : syracuseStep 3009875 = 4514813) B4514813
theorem B2006583 : Blo 2005435 2006583 := bstep (se 1 (by rfl) ⟨1504937, by rfl⟩ : syracuseStep 2006583 = 3009875) B3009875
theorem B3386117 : Blo 2005435 3386117 := bbase (se 4 (by rfl) ⟨317448, by rfl⟩ : syracuseStep 3386117 = 634897) (by norm_num)
theorem B2257411 : Blo 2005435 2257411 := bstep (se 1 (by rfl) ⟨1693058, by rfl⟩ : syracuseStep 2257411 = 3386117) B3386117
theorem B3009881 : Blo 2005435 3009881 := bstep (se 2 (by rfl) ⟨1128705, by rfl⟩ : syracuseStep 3009881 = 2257411) B2257411
theorem B2006587 : Blo 2005435 2006587 := bstep (se 1 (by rfl) ⟨1504940, by rfl⟩ : syracuseStep 2006587 = 3009881) B3009881
theorem B15237557 : Blo 2005435 15237557 := bbase (se 5 (by rfl) ⟨714260, by rfl⟩ : syracuseStep 15237557 = 1428521) (by norm_num)
theorem B10158371 : Blo 2005435 10158371 := bstep (se 1 (by rfl) ⟨7618778, by rfl⟩ : syracuseStep 10158371 = 15237557) B15237557
theorem B6772247 : Blo 2005435 6772247 := bstep (se 1 (by rfl) ⟨5079185, by rfl⟩ : syracuseStep 6772247 = 10158371) B10158371
theorem B4514831 : Blo 2005435 4514831 := bstep (se 1 (by rfl) ⟨3386123, by rfl⟩ : syracuseStep 4514831 = 6772247) B6772247
theorem B3009887 : Blo 2005435 3009887 := bstep (se 1 (by rfl) ⟨2257415, by rfl⟩ : syracuseStep 3009887 = 4514831) B4514831
theorem B2006591 : Blo 2005435 2006591 := bstep (se 1 (by rfl) ⟨1504943, by rfl⟩ : syracuseStep 2006591 = 3009887) B3009887
theorem B3009893 : Blo 2005435 3009893 := bbase (se 4 (by rfl) ⟨282177, by rfl⟩ : syracuseStep 3009893 = 564355) (by norm_num)
theorem B2006595 : Blo 2005435 2006595 := bstep (se 1 (by rfl) ⟨1504946, by rfl⟩ : syracuseStep 2006595 = 3009893) B3009893
theorem B3809405 : Blo 2005435 3809405 := bbase (se 3 (by rfl) ⟨714263, by rfl⟩ : syracuseStep 3809405 = 1428527) (by norm_num)
theorem B2539603 : Blo 2005435 2539603 := bstep (se 1 (by rfl) ⟨1904702, by rfl⟩ : syracuseStep 2539603 = 3809405) B3809405
theorem B3386137 : Blo 2005435 3386137 := bstep (se 2 (by rfl) ⟨1269801, by rfl⟩ : syracuseStep 3386137 = 2539603) B2539603
theorem B4514849 : Blo 2005435 4514849 := bstep (se 2 (by rfl) ⟨1693068, by rfl⟩ : syracuseStep 4514849 = 3386137) B3386137
theorem B3009899 : Blo 2005435 3009899 := bstep (se 1 (by rfl) ⟨2257424, by rfl⟩ : syracuseStep 3009899 = 4514849) B4514849
theorem B2006599 : Blo 2005435 2006599 := bstep (se 1 (by rfl) ⟨1504949, by rfl⟩ : syracuseStep 2006599 = 3009899) B3009899
theorem B2257429 : Blo 2005435 2257429 := bbase (se 6 (by rfl) ⟨52908, by rfl⟩ : syracuseStep 2257429 = 105817) (by norm_num)
theorem B3009905 : Blo 2005435 3009905 := bstep (se 2 (by rfl) ⟨1128714, by rfl⟩ : syracuseStep 3009905 = 2257429) B2257429
theorem B2006603 : Blo 2005435 2006603 := bstep (se 1 (by rfl) ⟨1504952, by rfl⟩ : syracuseStep 2006603 = 3009905) B3009905
theorem B2539613 : Blo 2005435 2539613 := bbase (se 3 (by rfl) ⟨476177, by rfl⟩ : syracuseStep 2539613 = 952355) (by norm_num)
theorem B6772301 : Blo 2005435 6772301 := bstep (se 3 (by rfl) ⟨1269806, by rfl⟩ : syracuseStep 6772301 = 2539613) B2539613
theorem B4514867 : Blo 2005435 4514867 := bstep (se 1 (by rfl) ⟨3386150, by rfl⟩ : syracuseStep 4514867 = 6772301) B6772301
theorem B3009911 : Blo 2005435 3009911 := bstep (se 1 (by rfl) ⟨2257433, by rfl⟩ : syracuseStep 3009911 = 4514867) B4514867
theorem B2006607 : Blo 2005435 2006607 := bstep (se 1 (by rfl) ⟨1504955, by rfl⟩ : syracuseStep 2006607 = 3009911) B3009911
theorem B3009917 : Blo 2005435 3009917 := bbase (se 3 (by rfl) ⟨564359, by rfl⟩ : syracuseStep 3009917 = 1128719) (by norm_num)
theorem B2006611 : Blo 2005435 2006611 := bstep (se 1 (by rfl) ⟨1504958, by rfl⟩ : syracuseStep 2006611 = 3009917) B3009917
theorem B4514885 : Blo 2005435 4514885 := bbase (se 4 (by rfl) ⟨423270, by rfl⟩ : syracuseStep 4514885 = 846541) (by norm_num)
theorem B3009923 : Blo 2005435 3009923 := bstep (se 1 (by rfl) ⟨2257442, by rfl⟩ : syracuseStep 3009923 = 4514885) B4514885
theorem B2006615 : Blo 2005435 2006615 := bstep (se 1 (by rfl) ⟨1504961, by rfl⟩ : syracuseStep 2006615 = 3009923) B3009923
theorem B5714165 : Blo 2005435 5714165 := bbase (se 5 (by rfl) ⟨267851, by rfl⟩ : syracuseStep 5714165 = 535703) (by norm_num)
theorem B3809443 : Blo 2005435 3809443 := bstep (se 1 (by rfl) ⟨2857082, by rfl⟩ : syracuseStep 3809443 = 5714165) B5714165
theorem B5079257 : Blo 2005435 5079257 := bstep (se 2 (by rfl) ⟨1904721, by rfl⟩ : syracuseStep 5079257 = 3809443) B3809443
theorem B3386171 : Blo 2005435 3386171 := bstep (se 1 (by rfl) ⟨2539628, by rfl⟩ : syracuseStep 3386171 = 5079257) B5079257
theorem B2257447 : Blo 2005435 2257447 := bstep (se 1 (by rfl) ⟨1693085, by rfl⟩ : syracuseStep 2257447 = 3386171) B3386171
theorem B3009929 : Blo 2005435 3009929 := bstep (se 2 (by rfl) ⟨1128723, by rfl⟩ : syracuseStep 3009929 = 2257447) B2257447
theorem B2006619 : Blo 2005435 2006619 := bstep (se 1 (by rfl) ⟨1504964, by rfl⟩ : syracuseStep 2006619 = 3009929) B3009929
theorem B10158533 : Blo 2005435 10158533 := bbase (se 4 (by rfl) ⟨952362, by rfl⟩ : syracuseStep 10158533 = 1904725) (by norm_num)
theorem B6772355 : Blo 2005435 6772355 := bstep (se 1 (by rfl) ⟨5079266, by rfl⟩ : syracuseStep 6772355 = 10158533) B10158533
theorem B4514903 : Blo 2005435 4514903 := bstep (se 1 (by rfl) ⟨3386177, by rfl⟩ : syracuseStep 4514903 = 6772355) B6772355
theorem B3009935 : Blo 2005435 3009935 := bstep (se 1 (by rfl) ⟨2257451, by rfl⟩ : syracuseStep 3009935 = 4514903) B4514903
theorem B2006623 : Blo 2005435 2006623 := bstep (se 1 (by rfl) ⟨1504967, by rfl⟩ : syracuseStep 2006623 = 3009935) B3009935
theorem B3009941 : Blo 2005435 3009941 := bbase (se 6 (by rfl) ⟨70545, by rfl⟩ : syracuseStep 3009941 = 141091) (by norm_num)
theorem B2006627 : Blo 2005435 2006627 := bstep (se 1 (by rfl) ⟨1504970, by rfl⟩ : syracuseStep 2006627 = 3009941) B3009941
theorem B3214237 : Blo 2005435 3214237 := bbase (se 3 (by rfl) ⟨602669, by rfl⟩ : syracuseStep 3214237 = 1205339) (by norm_num)
theorem B4285649 : Blo 2005435 4285649 := bstep (se 2 (by rfl) ⟨1607118, by rfl⟩ : syracuseStep 4285649 = 3214237) B3214237
theorem B11428397 : Blo 2005435 11428397 := bstep (se 3 (by rfl) ⟨2142824, by rfl⟩ : syracuseStep 11428397 = 4285649) B4285649
theorem B7618931 : Blo 2005435 7618931 := bstep (se 1 (by rfl) ⟨5714198, by rfl⟩ : syracuseStep 7618931 = 11428397) B11428397
theorem B5079287 : Blo 2005435 5079287 := bstep (se 1 (by rfl) ⟨3809465, by rfl⟩ : syracuseStep 5079287 = 7618931) B7618931
theorem B3386191 : Blo 2005435 3386191 := bstep (se 1 (by rfl) ⟨2539643, by rfl⟩ : syracuseStep 3386191 = 5079287) B5079287
theorem B4514921 : Blo 2005435 4514921 := bstep (se 2 (by rfl) ⟨1693095, by rfl⟩ : syracuseStep 4514921 = 3386191) B3386191
theorem B3009947 : Blo 2005435 3009947 := bstep (se 1 (by rfl) ⟨2257460, by rfl⟩ : syracuseStep 3009947 = 4514921) B4514921
theorem B2006631 : Blo 2005435 2006631 := bstep (se 1 (by rfl) ⟨1504973, by rfl⟩ : syracuseStep 2006631 = 3009947) B3009947
theorem B2257465 : Blo 2005435 2257465 := bbase (se 2 (by rfl) ⟨846549, by rfl⟩ : syracuseStep 2257465 = 1693099) (by norm_num)
theorem B3009953 : Blo 2005435 3009953 := bstep (se 2 (by rfl) ⟨1128732, by rfl⟩ : syracuseStep 3009953 = 2257465) B2257465
theorem B2006635 : Blo 2005435 2006635 := bstep (se 1 (by rfl) ⟨1504976, by rfl⟩ : syracuseStep 2006635 = 3009953) B3009953
theorem B2142833 : Blo 2005435 2142833 := bbase (se 2 (by rfl) ⟨803562, by rfl⟩ : syracuseStep 2142833 = 1607125) (by norm_num)
theorem B5714221 : Blo 2005435 5714221 := bstep (se 3 (by rfl) ⟨1071416, by rfl⟩ : syracuseStep 5714221 = 2142833) B2142833
theorem B7618961 : Blo 2005435 7618961 := bstep (se 2 (by rfl) ⟨2857110, by rfl⟩ : syracuseStep 7618961 = 5714221) B5714221
theorem B5079307 : Blo 2005435 5079307 := bstep (se 1 (by rfl) ⟨3809480, by rfl⟩ : syracuseStep 5079307 = 7618961) B7618961
theorem B6772409 : Blo 2005435 6772409 := bstep (se 2 (by rfl) ⟨2539653, by rfl⟩ : syracuseStep 6772409 = 5079307) B5079307
theorem B4514939 : Blo 2005435 4514939 := bstep (se 1 (by rfl) ⟨3386204, by rfl⟩ : syracuseStep 4514939 = 6772409) B6772409
theorem B3009959 : Blo 2005435 3009959 := bstep (se 1 (by rfl) ⟨2257469, by rfl⟩ : syracuseStep 3009959 = 4514939) B4514939
theorem B2006639 : Blo 2005435 2006639 := bstep (se 1 (by rfl) ⟨1504979, by rfl⟩ : syracuseStep 2006639 = 3009959) B3009959
theorem B3009965 : Blo 2005435 3009965 := bbase (se 3 (by rfl) ⟨564368, by rfl⟩ : syracuseStep 3009965 = 1128737) (by norm_num)
theorem B2006643 : Blo 2005435 2006643 := bstep (se 1 (by rfl) ⟨1504982, by rfl⟩ : syracuseStep 2006643 = 3009965) B3009965
theorem B4514957 : Blo 2005435 4514957 := bbase (se 3 (by rfl) ⟨846554, by rfl⟩ : syracuseStep 4514957 = 1693109) (by norm_num)
theorem B3009971 : Blo 2005435 3009971 := bstep (se 1 (by rfl) ⟨2257478, by rfl⟩ : syracuseStep 3009971 = 4514957) B4514957
theorem B2006647 : Blo 2005435 2006647 := bstep (se 1 (by rfl) ⟨1504985, by rfl⟩ : syracuseStep 2006647 = 3009971) B3009971
theorem B2539669 : Blo 2005435 2539669 := bbase (se 6 (by rfl) ⟨59523, by rfl⟩ : syracuseStep 2539669 = 119047) (by norm_num)
theorem B3386225 : Blo 2005435 3386225 := bstep (se 2 (by rfl) ⟨1269834, by rfl⟩ : syracuseStep 3386225 = 2539669) B2539669
theorem B2257483 : Blo 2005435 2257483 := bstep (se 1 (by rfl) ⟨1693112, by rfl⟩ : syracuseStep 2257483 = 3386225) B3386225
theorem B3009977 : Blo 2005435 3009977 := bstep (se 2 (by rfl) ⟨1128741, by rfl⟩ : syracuseStep 3009977 = 2257483) B2257483
theorem B2006651 : Blo 2005435 2006651 := bstep (se 1 (by rfl) ⟨1504988, by rfl⟩ : syracuseStep 2006651 = 3009977) B3009977
theorem B6102101 : Blo 2005435 6102101 := bbase (se 8 (by rfl) ⟨35754, by rfl⟩ : syracuseStep 6102101 = 71509) (by norm_num)
theorem B4068067 : Blo 2005435 4068067 := bstep (se 1 (by rfl) ⟨3051050, by rfl⟩ : syracuseStep 4068067 = 6102101) B6102101
theorem B5424089 : Blo 2005435 5424089 := bstep (se 2 (by rfl) ⟨2034033, by rfl⟩ : syracuseStep 5424089 = 4068067) B4068067
theorem B57856949 : Blo 2005435 57856949 := bstep (se 5 (by rfl) ⟨2712044, by rfl⟩ : syracuseStep 57856949 = 5424089) B5424089
theorem B38571299 : Blo 2005435 38571299 := bstep (se 1 (by rfl) ⟨28928474, by rfl⟩ : syracuseStep 38571299 = 57856949) B57856949
theorem B25714199 : Blo 2005435 25714199 := bstep (se 1 (by rfl) ⟨19285649, by rfl⟩ : syracuseStep 25714199 = 38571299) B38571299
theorem B17142799 : Blo 2005435 17142799 := bstep (se 1 (by rfl) ⟨12857099, by rfl⟩ : syracuseStep 17142799 = 25714199) B25714199
theorem B22857065 : Blo 2005435 22857065 := bstep (se 2 (by rfl) ⟨8571399, by rfl⟩ : syracuseStep 22857065 = 17142799) B17142799
theorem B15238043 : Blo 2005435 15238043 := bstep (se 1 (by rfl) ⟨11428532, by rfl⟩ : syracuseStep 15238043 = 22857065) B22857065
theorem B10158695 : Blo 2005435 10158695 := bstep (se 1 (by rfl) ⟨7619021, by rfl⟩ : syracuseStep 10158695 = 15238043) B15238043
theorem B6772463 : Blo 2005435 6772463 := bstep (se 1 (by rfl) ⟨5079347, by rfl⟩ : syracuseStep 6772463 = 10158695) B10158695
theorem B4514975 : Blo 2005435 4514975 := bstep (se 1 (by rfl) ⟨3386231, by rfl⟩ : syracuseStep 4514975 = 6772463) B6772463
theorem B3009983 : Blo 2005435 3009983 := bstep (se 1 (by rfl) ⟨2257487, by rfl⟩ : syracuseStep 3009983 = 4514975) B4514975
theorem B2006655 : Blo 2005435 2006655 := bstep (se 1 (by rfl) ⟨1504991, by rfl⟩ : syracuseStep 2006655 = 3009983) B3009983
theorem B3009989 : Blo 2005435 3009989 := bbase (se 4 (by rfl) ⟨282186, by rfl⟩ : syracuseStep 3009989 = 564373) (by norm_num)
theorem B2006659 : Blo 2005435 2006659 := bstep (se 1 (by rfl) ⟨1504994, by rfl⟩ : syracuseStep 2006659 = 3009989) B3009989
theorem B3386245 : Blo 2005435 3386245 := bbase (se 4 (by rfl) ⟨317460, by rfl⟩ : syracuseStep 3386245 = 634921) (by norm_num)
theorem B4514993 : Blo 2005435 4514993 := bstep (se 2 (by rfl) ⟨1693122, by rfl⟩ : syracuseStep 4514993 = 3386245) B3386245
theorem B3009995 : Blo 2005435 3009995 := bstep (se 1 (by rfl) ⟨2257496, by rfl⟩ : syracuseStep 3009995 = 4514993) B4514993
theorem B2006663 : Blo 2005435 2006663 := bstep (se 1 (by rfl) ⟨1504997, by rfl⟩ : syracuseStep 2006663 = 3009995) B3009995
theorem B2257501 : Blo 2005435 2257501 := bbase (se 3 (by rfl) ⟨423281, by rfl⟩ : syracuseStep 2257501 = 846563) (by norm_num)
theorem B3010001 : Blo 2005435 3010001 := bstep (se 2 (by rfl) ⟨1128750, by rfl⟩ : syracuseStep 3010001 = 2257501) B2257501
theorem B2006667 : Blo 2005435 2006667 := bstep (se 1 (by rfl) ⟨1505000, by rfl⟩ : syracuseStep 2006667 = 3010001) B3010001
theorem B6772517 : Blo 2005435 6772517 := bbase (se 4 (by rfl) ⟨634923, by rfl⟩ : syracuseStep 6772517 = 1269847) (by norm_num)
theorem B4515011 : Blo 2005435 4515011 := bstep (se 1 (by rfl) ⟨3386258, by rfl⟩ : syracuseStep 4515011 = 6772517) B6772517
theorem B3010007 : Blo 2005435 3010007 := bstep (se 1 (by rfl) ⟨2257505, by rfl⟩ : syracuseStep 3010007 = 4515011) B4515011
theorem B2006671 : Blo 2005435 2006671 := bstep (se 1 (by rfl) ⟨1505003, by rfl⟩ : syracuseStep 2006671 = 3010007) B3010007
theorem B3010013 : Blo 2005435 3010013 := bbase (se 3 (by rfl) ⟨564377, by rfl⟩ : syracuseStep 3010013 = 1128755) (by norm_num)
theorem B2006675 : Blo 2005435 2006675 := bstep (se 1 (by rfl) ⟨1505006, by rfl⟩ : syracuseStep 2006675 = 3010013) B3010013
theorem B4515029 : Blo 2005435 4515029 := bbase (se 7 (by rfl) ⟨52910, by rfl⟩ : syracuseStep 4515029 = 105821) (by norm_num)
theorem B3010019 : Blo 2005435 3010019 := bstep (se 1 (by rfl) ⟨2257514, by rfl⟩ : syracuseStep 3010019 = 4515029) B4515029
theorem B2006679 : Blo 2005435 2006679 := bstep (se 1 (by rfl) ⟨1505009, by rfl⟩ : syracuseStep 2006679 = 3010019) B3010019
theorem B2574361 : Blo 2005435 2574361 := bbase (se 2 (by rfl) ⟨965385, by rfl⟩ : syracuseStep 2574361 = 1930771) (by norm_num)
theorem B13729925 : Blo 2005435 13729925 := bstep (se 4 (by rfl) ⟨1287180, by rfl⟩ : syracuseStep 13729925 = 2574361) B2574361
theorem B9153283 : Blo 2005435 9153283 := bstep (se 1 (by rfl) ⟨6864962, by rfl⟩ : syracuseStep 9153283 = 13729925) B13729925
theorem B12204377 : Blo 2005435 12204377 := bstep (se 2 (by rfl) ⟨4576641, by rfl⟩ : syracuseStep 12204377 = 9153283) B9153283
theorem B8136251 : Blo 2005435 8136251 := bstep (se 1 (by rfl) ⟨6102188, by rfl⟩ : syracuseStep 8136251 = 12204377) B12204377
theorem B5424167 : Blo 2005435 5424167 := bstep (se 1 (by rfl) ⟨4068125, by rfl⟩ : syracuseStep 5424167 = 8136251) B8136251
theorem B3616111 : Blo 2005435 3616111 := bstep (se 1 (by rfl) ⟨2712083, by rfl⟩ : syracuseStep 3616111 = 5424167) B5424167
theorem B4821481 : Blo 2005435 4821481 := bstep (se 2 (by rfl) ⟨1808055, by rfl⟩ : syracuseStep 4821481 = 3616111) B3616111
theorem B6428641 : Blo 2005435 6428641 := bstep (se 2 (by rfl) ⟨2410740, by rfl⟩ : syracuseStep 6428641 = 4821481) B4821481
theorem B8571521 : Blo 2005435 8571521 := bstep (se 2 (by rfl) ⟨3214320, by rfl⟩ : syracuseStep 8571521 = 6428641) B6428641
theorem B5714347 : Blo 2005435 5714347 := bstep (se 1 (by rfl) ⟨4285760, by rfl⟩ : syracuseStep 5714347 = 8571521) B8571521
theorem B7619129 : Blo 2005435 7619129 := bstep (se 2 (by rfl) ⟨2857173, by rfl⟩ : syracuseStep 7619129 = 5714347) B5714347
theorem B5079419 : Blo 2005435 5079419 := bstep (se 1 (by rfl) ⟨3809564, by rfl⟩ : syracuseStep 5079419 = 7619129) B7619129
theorem B3386279 : Blo 2005435 3386279 := bstep (se 1 (by rfl) ⟨2539709, by rfl⟩ : syracuseStep 3386279 = 5079419) B5079419
theorem B2257519 : Blo 2005435 2257519 := bstep (se 1 (by rfl) ⟨1693139, by rfl⟩ : syracuseStep 2257519 = 3386279) B3386279
theorem B3010025 : Blo 2005435 3010025 := bstep (se 2 (by rfl) ⟨1128759, by rfl⟩ : syracuseStep 3010025 = 2257519) B2257519
theorem B2006683 : Blo 2005435 2006683 := bstep (se 1 (by rfl) ⟨1505012, by rfl⟩ : syracuseStep 2006683 = 3010025) B3010025
theorem B14464469 : Blo 2005435 14464469 := bbase (se 7 (by rfl) ⟨169505, by rfl⟩ : syracuseStep 14464469 = 339011) (by norm_num)
theorem B9642979 : Blo 2005435 9642979 := bstep (se 1 (by rfl) ⟨7232234, by rfl⟩ : syracuseStep 9642979 = 14464469) B14464469
theorem B12857305 : Blo 2005435 12857305 := bstep (se 2 (by rfl) ⟨4821489, by rfl⟩ : syracuseStep 12857305 = 9642979) B9642979
theorem B17143073 : Blo 2005435 17143073 := bstep (se 2 (by rfl) ⟨6428652, by rfl⟩ : syracuseStep 17143073 = 12857305) B12857305
theorem B11428715 : Blo 2005435 11428715 := bstep (se 1 (by rfl) ⟨8571536, by rfl⟩ : syracuseStep 11428715 = 17143073) B17143073
theorem B7619143 : Blo 2005435 7619143 := bstep (se 1 (by rfl) ⟨5714357, by rfl⟩ : syracuseStep 7619143 = 11428715) B11428715
theorem B10158857 : Blo 2005435 10158857 := bstep (se 2 (by rfl) ⟨3809571, by rfl⟩ : syracuseStep 10158857 = 7619143) B7619143
theorem B6772571 : Blo 2005435 6772571 := bstep (se 1 (by rfl) ⟨5079428, by rfl⟩ : syracuseStep 6772571 = 10158857) B10158857
theorem B4515047 : Blo 2005435 4515047 := bstep (se 1 (by rfl) ⟨3386285, by rfl⟩ : syracuseStep 4515047 = 6772571) B6772571
theorem B3010031 : Blo 2005435 3010031 := bstep (se 1 (by rfl) ⟨2257523, by rfl⟩ : syracuseStep 3010031 = 4515047) B4515047
theorem B2006687 : Blo 2005435 2006687 := bstep (se 1 (by rfl) ⟨1505015, by rfl⟩ : syracuseStep 2006687 = 3010031) B3010031
theorem B3010037 : Blo 2005435 3010037 := bbase (se 5 (by rfl) ⟨141095, by rfl⟩ : syracuseStep 3010037 = 282191) (by norm_num)
theorem B2006691 : Blo 2005435 2006691 := bstep (se 1 (by rfl) ⟨1505018, by rfl⟩ : syracuseStep 2006691 = 3010037) B3010037
theorem B2142893 : Blo 2005435 2142893 := bbase (se 3 (by rfl) ⟨401792, by rfl⟩ : syracuseStep 2142893 = 803585) (by norm_num)
theorem B5714381 : Blo 2005435 5714381 := bstep (se 3 (by rfl) ⟨1071446, by rfl⟩ : syracuseStep 5714381 = 2142893) B2142893
theorem B3809587 : Blo 2005435 3809587 := bstep (se 1 (by rfl) ⟨2857190, by rfl⟩ : syracuseStep 3809587 = 5714381) B5714381
theorem B5079449 : Blo 2005435 5079449 := bstep (se 2 (by rfl) ⟨1904793, by rfl⟩ : syracuseStep 5079449 = 3809587) B3809587
theorem B3386299 : Blo 2005435 3386299 := bstep (se 1 (by rfl) ⟨2539724, by rfl⟩ : syracuseStep 3386299 = 5079449) B5079449
theorem B4515065 : Blo 2005435 4515065 := bstep (se 2 (by rfl) ⟨1693149, by rfl⟩ : syracuseStep 4515065 = 3386299) B3386299
theorem B3010043 : Blo 2005435 3010043 := bstep (se 1 (by rfl) ⟨2257532, by rfl⟩ : syracuseStep 3010043 = 4515065) B4515065
theorem B2006695 : Blo 2005435 2006695 := bstep (se 1 (by rfl) ⟨1505021, by rfl⟩ : syracuseStep 2006695 = 3010043) B3010043
theorem B2257537 : Blo 2005435 2257537 := bbase (se 2 (by rfl) ⟨846576, by rfl⟩ : syracuseStep 2257537 = 1693153) (by norm_num)
theorem B3010049 : Blo 2005435 3010049 := bstep (se 2 (by rfl) ⟨1128768, by rfl⟩ : syracuseStep 3010049 = 2257537) B2257537
theorem B2006699 : Blo 2005435 2006699 := bstep (se 1 (by rfl) ⟨1505024, by rfl⟩ : syracuseStep 2006699 = 3010049) B3010049
theorem B5079469 : Blo 2005435 5079469 := bbase (se 3 (by rfl) ⟨952400, by rfl⟩ : syracuseStep 5079469 = 1904801) (by norm_num)
theorem B6772625 : Blo 2005435 6772625 := bstep (se 2 (by rfl) ⟨2539734, by rfl⟩ : syracuseStep 6772625 = 5079469) B5079469
theorem B4515083 : Blo 2005435 4515083 := bstep (se 1 (by rfl) ⟨3386312, by rfl⟩ : syracuseStep 4515083 = 6772625) B6772625
theorem B3010055 : Blo 2005435 3010055 := bstep (se 1 (by rfl) ⟨2257541, by rfl⟩ : syracuseStep 3010055 = 4515083) B4515083
theorem B2006703 : Blo 2005435 2006703 := bstep (se 1 (by rfl) ⟨1505027, by rfl⟩ : syracuseStep 2006703 = 3010055) B3010055
theorem B3010061 : Blo 2005435 3010061 := bbase (se 3 (by rfl) ⟨564386, by rfl⟩ : syracuseStep 3010061 = 1128773) (by norm_num)
theorem B2006707 : Blo 2005435 2006707 := bstep (se 1 (by rfl) ⟨1505030, by rfl⟩ : syracuseStep 2006707 = 3010061) B3010061
theorem B4515101 : Blo 2005435 4515101 := bbase (se 3 (by rfl) ⟨846581, by rfl⟩ : syracuseStep 4515101 = 1693163) (by norm_num)
theorem B3010067 : Blo 2005435 3010067 := bstep (se 1 (by rfl) ⟨2257550, by rfl⟩ : syracuseStep 3010067 = 4515101) B4515101
theorem B2006711 : Blo 2005435 2006711 := bstep (se 1 (by rfl) ⟨1505033, by rfl⟩ : syracuseStep 2006711 = 3010067) B3010067
theorem B3386333 : Blo 2005435 3386333 := bbase (se 3 (by rfl) ⟨634937, by rfl⟩ : syracuseStep 3386333 = 1269875) (by norm_num)
theorem B2257555 : Blo 2005435 2257555 := bstep (se 1 (by rfl) ⟨1693166, by rfl⟩ : syracuseStep 2257555 = 3386333) B3386333
theorem B3010073 : Blo 2005435 3010073 := bstep (se 2 (by rfl) ⟨1128777, by rfl⟩ : syracuseStep 3010073 = 2257555) B2257555
theorem B2006715 : Blo 2005435 2006715 := bstep (se 1 (by rfl) ⟨1505036, by rfl⟩ : syracuseStep 2006715 = 3010073) B3010073
theorem B9153445 : Blo 2005435 9153445 := bbase (se 4 (by rfl) ⟨858135, by rfl⟩ : syracuseStep 9153445 = 1716271) (by norm_num)
theorem B12204593 : Blo 2005435 12204593 := bstep (se 2 (by rfl) ⟨4576722, by rfl⟩ : syracuseStep 12204593 = 9153445) B9153445
theorem B8136395 : Blo 2005435 8136395 := bstep (se 1 (by rfl) ⟨6102296, by rfl⟩ : syracuseStep 8136395 = 12204593) B12204593
theorem B5424263 : Blo 2005435 5424263 := bstep (se 1 (by rfl) ⟨4068197, by rfl⟩ : syracuseStep 5424263 = 8136395) B8136395
theorem B3616175 : Blo 2005435 3616175 := bstep (se 1 (by rfl) ⟨2712131, by rfl⟩ : syracuseStep 3616175 = 5424263) B5424263
theorem B9643133 : Blo 2005435 9643133 := bstep (se 3 (by rfl) ⟨1808087, by rfl⟩ : syracuseStep 9643133 = 3616175) B3616175
theorem B6428755 : Blo 2005435 6428755 := bstep (se 1 (by rfl) ⟨4821566, by rfl⟩ : syracuseStep 6428755 = 9643133) B9643133
theorem B8571673 : Blo 2005435 8571673 := bstep (se 2 (by rfl) ⟨3214377, by rfl⟩ : syracuseStep 8571673 = 6428755) B6428755
theorem B11428897 : Blo 2005435 11428897 := bstep (se 2 (by rfl) ⟨4285836, by rfl⟩ : syracuseStep 11428897 = 8571673) B8571673
theorem B15238529 : Blo 2005435 15238529 := bstep (se 2 (by rfl) ⟨5714448, by rfl⟩ : syracuseStep 15238529 = 11428897) B11428897
theorem B10159019 : Blo 2005435 10159019 := bstep (se 1 (by rfl) ⟨7619264, by rfl⟩ : syracuseStep 10159019 = 15238529) B15238529
theorem B6772679 : Blo 2005435 6772679 := bstep (se 1 (by rfl) ⟨5079509, by rfl⟩ : syracuseStep 6772679 = 10159019) B10159019
theorem B4515119 : Blo 2005435 4515119 := bstep (se 1 (by rfl) ⟨3386339, by rfl⟩ : syracuseStep 4515119 = 6772679) B6772679
theorem B3010079 : Blo 2005435 3010079 := bstep (se 1 (by rfl) ⟨2257559, by rfl⟩ : syracuseStep 3010079 = 4515119) B4515119
theorem B2006719 : Blo 2005435 2006719 := bstep (se 1 (by rfl) ⟨1505039, by rfl⟩ : syracuseStep 2006719 = 3010079) B3010079
theorem B3010085 : Blo 2005435 3010085 := bbase (se 4 (by rfl) ⟨282195, by rfl⟩ : syracuseStep 3010085 = 564391) (by norm_num)
theorem B2006723 : Blo 2005435 2006723 := bstep (se 1 (by rfl) ⟨1505042, by rfl⟩ : syracuseStep 2006723 = 3010085) B3010085
theorem B2539765 : Blo 2005435 2539765 := bbase (se 5 (by rfl) ⟨119051, by rfl⟩ : syracuseStep 2539765 = 238103) (by norm_num)
theorem B3386353 : Blo 2005435 3386353 := bstep (se 2 (by rfl) ⟨1269882, by rfl⟩ : syracuseStep 3386353 = 2539765) B2539765
theorem B4515137 : Blo 2005435 4515137 := bstep (se 2 (by rfl) ⟨1693176, by rfl⟩ : syracuseStep 4515137 = 3386353) B3386353
theorem B3010091 : Blo 2005435 3010091 := bstep (se 1 (by rfl) ⟨2257568, by rfl⟩ : syracuseStep 3010091 = 4515137) B4515137
theorem B2006727 : Blo 2005435 2006727 := bstep (se 1 (by rfl) ⟨1505045, by rfl⟩ : syracuseStep 2006727 = 3010091) B3010091
theorem B2257573 : Blo 2005435 2257573 := bbase (se 4 (by rfl) ⟨211647, by rfl⟩ : syracuseStep 2257573 = 423295) (by norm_num)
theorem B3010097 : Blo 2005435 3010097 := bstep (se 2 (by rfl) ⟨1128786, by rfl⟩ : syracuseStep 3010097 = 2257573) B2257573
theorem B2006731 : Blo 2005435 2006731 := bstep (se 1 (by rfl) ⟨1505048, by rfl⟩ : syracuseStep 2006731 = 3010097) B3010097
theorem B3051173 : Blo 2005435 3051173 := bbase (se 4 (by rfl) ⟨286047, by rfl⟩ : syracuseStep 3051173 = 572095) (by norm_num)
theorem B2034115 : Blo 2005435 2034115 := bstep (se 1 (by rfl) ⟨1525586, by rfl⟩ : syracuseStep 2034115 = 3051173) B3051173
theorem B43394453 : Blo 2005435 43394453 := bstep (se 6 (by rfl) ⟨1017057, by rfl⟩ : syracuseStep 43394453 = 2034115) B2034115
theorem B28929635 : Blo 2005435 28929635 := bstep (se 1 (by rfl) ⟨21697226, by rfl⟩ : syracuseStep 28929635 = 43394453) B43394453
theorem B19286423 : Blo 2005435 19286423 := bstep (se 1 (by rfl) ⟨14464817, by rfl⟩ : syracuseStep 19286423 = 28929635) B28929635
theorem B12857615 : Blo 2005435 12857615 := bstep (se 1 (by rfl) ⟨9643211, by rfl⟩ : syracuseStep 12857615 = 19286423) B19286423
theorem B8571743 : Blo 2005435 8571743 := bstep (se 1 (by rfl) ⟨6428807, by rfl⟩ : syracuseStep 8571743 = 12857615) B12857615
theorem B5714495 : Blo 2005435 5714495 := bstep (se 1 (by rfl) ⟨4285871, by rfl⟩ : syracuseStep 5714495 = 8571743) B8571743
theorem B3809663 : Blo 2005435 3809663 := bstep (se 1 (by rfl) ⟨2857247, by rfl⟩ : syracuseStep 3809663 = 5714495) B5714495
theorem B2539775 : Blo 2005435 2539775 := bstep (se 1 (by rfl) ⟨1904831, by rfl⟩ : syracuseStep 2539775 = 3809663) B3809663
theorem B6772733 : Blo 2005435 6772733 := bstep (se 3 (by rfl) ⟨1269887, by rfl⟩ : syracuseStep 6772733 = 2539775) B2539775
theorem B4515155 : Blo 2005435 4515155 := bstep (se 1 (by rfl) ⟨3386366, by rfl⟩ : syracuseStep 4515155 = 6772733) B6772733
theorem B3010103 : Blo 2005435 3010103 := bstep (se 1 (by rfl) ⟨2257577, by rfl⟩ : syracuseStep 3010103 = 4515155) B4515155
theorem B2006735 : Blo 2005435 2006735 := bstep (se 1 (by rfl) ⟨1505051, by rfl⟩ : syracuseStep 2006735 = 3010103) B3010103
theorem B3010109 : Blo 2005435 3010109 := bbase (se 3 (by rfl) ⟨564395, by rfl⟩ : syracuseStep 3010109 = 1128791) (by norm_num)
theorem B2006739 : Blo 2005435 2006739 := bstep (se 1 (by rfl) ⟨1505054, by rfl⟩ : syracuseStep 2006739 = 3010109) B3010109
theorem B4515173 : Blo 2005435 4515173 := bbase (se 4 (by rfl) ⟨423297, by rfl⟩ : syracuseStep 4515173 = 846595) (by norm_num)
theorem B3010115 : Blo 2005435 3010115 := bstep (se 1 (by rfl) ⟨2257586, by rfl⟩ : syracuseStep 3010115 = 4515173) B4515173
theorem B2006743 : Blo 2005435 2006743 := bstep (se 1 (by rfl) ⟨1505057, by rfl⟩ : syracuseStep 2006743 = 3010115) B3010115
theorem B5079581 : Blo 2005435 5079581 := bbase (se 3 (by rfl) ⟨952421, by rfl⟩ : syracuseStep 5079581 = 1904843) (by norm_num)
theorem B3386387 : Blo 2005435 3386387 := bstep (se 1 (by rfl) ⟨2539790, by rfl⟩ : syracuseStep 3386387 = 5079581) B5079581
theorem B2257591 : Blo 2005435 2257591 := bstep (se 1 (by rfl) ⟨1693193, by rfl⟩ : syracuseStep 2257591 = 3386387) B3386387
theorem B3010121 : Blo 2005435 3010121 := bstep (se 2 (by rfl) ⟨1128795, by rfl⟩ : syracuseStep 3010121 = 2257591) B2257591
theorem B2006747 : Blo 2005435 2006747 := bstep (se 1 (by rfl) ⟨1505060, by rfl⟩ : syracuseStep 2006747 = 3010121) B3010121
theorem B3809693 : Blo 2005435 3809693 := bbase (se 3 (by rfl) ⟨714317, by rfl⟩ : syracuseStep 3809693 = 1428635) (by norm_num)
theorem B10159181 : Blo 2005435 10159181 := bstep (se 3 (by rfl) ⟨1904846, by rfl⟩ : syracuseStep 10159181 = 3809693) B3809693
theorem B6772787 : Blo 2005435 6772787 := bstep (se 1 (by rfl) ⟨5079590, by rfl⟩ : syracuseStep 6772787 = 10159181) B10159181
theorem B4515191 : Blo 2005435 4515191 := bstep (se 1 (by rfl) ⟨3386393, by rfl⟩ : syracuseStep 4515191 = 6772787) B6772787
theorem B3010127 : Blo 2005435 3010127 := bstep (se 1 (by rfl) ⟨2257595, by rfl⟩ : syracuseStep 3010127 = 4515191) B4515191
theorem B2006751 : Blo 2005435 2006751 := bstep (se 1 (by rfl) ⟨1505063, by rfl⟩ : syracuseStep 2006751 = 3010127) B3010127
theorem B3010133 : Blo 2005435 3010133 := bbase (se 8 (by rfl) ⟨17637, by rfl⟩ : syracuseStep 3010133 = 35275) (by norm_num)
theorem B2006755 : Blo 2005435 2006755 := bstep (se 1 (by rfl) ⟨1505066, by rfl⟩ : syracuseStep 2006755 = 3010133) B3010133
theorem B8571845 : Blo 2005435 8571845 := bbase (se 4 (by rfl) ⟨803610, by rfl⟩ : syracuseStep 8571845 = 1607221) (by norm_num)
theorem B5714563 : Blo 2005435 5714563 := bstep (se 1 (by rfl) ⟨4285922, by rfl⟩ : syracuseStep 5714563 = 8571845) B8571845
theorem B7619417 : Blo 2005435 7619417 := bstep (se 2 (by rfl) ⟨2857281, by rfl⟩ : syracuseStep 7619417 = 5714563) B5714563
theorem B5079611 : Blo 2005435 5079611 := bstep (se 1 (by rfl) ⟨3809708, by rfl⟩ : syracuseStep 5079611 = 7619417) B7619417
theorem B3386407 : Blo 2005435 3386407 := bstep (se 1 (by rfl) ⟨2539805, by rfl⟩ : syracuseStep 3386407 = 5079611) B5079611
theorem B4515209 : Blo 2005435 4515209 := bstep (se 2 (by rfl) ⟨1693203, by rfl⟩ : syracuseStep 4515209 = 3386407) B3386407
theorem B3010139 : Blo 2005435 3010139 := bstep (se 1 (by rfl) ⟨2257604, by rfl⟩ : syracuseStep 3010139 = 4515209) B4515209
theorem B2006759 : Blo 2005435 2006759 := bstep (se 1 (by rfl) ⟨1505069, by rfl⟩ : syracuseStep 2006759 = 3010139) B3010139
theorem B2257609 : Blo 2005435 2257609 := bbase (se 2 (by rfl) ⟨846603, by rfl⟩ : syracuseStep 2257609 = 1693207) (by norm_num)
theorem B3010145 : Blo 2005435 3010145 := bstep (se 2 (by rfl) ⟨1128804, by rfl⟩ : syracuseStep 3010145 = 2257609) B2257609
theorem B2006763 : Blo 2005435 2006763 := bstep (se 1 (by rfl) ⟨1505072, by rfl⟩ : syracuseStep 2006763 = 3010145) B3010145
theorem B2410841 : Blo 2005435 2410841 := bbase (se 2 (by rfl) ⟨904065, by rfl⟩ : syracuseStep 2410841 = 1808131) (by norm_num)
theorem B6428909 : Blo 2005435 6428909 := bstep (se 3 (by rfl) ⟨1205420, by rfl⟩ : syracuseStep 6428909 = 2410841) B2410841
theorem B17143757 : Blo 2005435 17143757 := bstep (se 3 (by rfl) ⟨3214454, by rfl⟩ : syracuseStep 17143757 = 6428909) B6428909
theorem B11429171 : Blo 2005435 11429171 := bstep (se 1 (by rfl) ⟨8571878, by rfl⟩ : syracuseStep 11429171 = 17143757) B17143757
theorem B7619447 : Blo 2005435 7619447 := bstep (se 1 (by rfl) ⟨5714585, by rfl⟩ : syracuseStep 7619447 = 11429171) B11429171
theorem B5079631 : Blo 2005435 5079631 := bstep (se 1 (by rfl) ⟨3809723, by rfl⟩ : syracuseStep 5079631 = 7619447) B7619447
theorem B6772841 : Blo 2005435 6772841 := bstep (se 2 (by rfl) ⟨2539815, by rfl⟩ : syracuseStep 6772841 = 5079631) B5079631
theorem B4515227 : Blo 2005435 4515227 := bstep (se 1 (by rfl) ⟨3386420, by rfl⟩ : syracuseStep 4515227 = 6772841) B6772841
theorem B3010151 : Blo 2005435 3010151 := bstep (se 1 (by rfl) ⟨2257613, by rfl⟩ : syracuseStep 3010151 = 4515227) B4515227
theorem B2006767 : Blo 2005435 2006767 := bstep (se 1 (by rfl) ⟨1505075, by rfl⟩ : syracuseStep 2006767 = 3010151) B3010151
theorem B3010157 : Blo 2005435 3010157 := bbase (se 3 (by rfl) ⟨564404, by rfl⟩ : syracuseStep 3010157 = 1128809) (by norm_num)
theorem B2006771 : Blo 2005435 2006771 := bstep (se 1 (by rfl) ⟨1505078, by rfl⟩ : syracuseStep 2006771 = 3010157) B3010157
theorem B4515245 : Blo 2005435 4515245 := bbase (se 3 (by rfl) ⟨846608, by rfl⟩ : syracuseStep 4515245 = 1693217) (by norm_num)
theorem B3010163 : Blo 2005435 3010163 := bstep (se 1 (by rfl) ⟨2257622, by rfl⟩ : syracuseStep 3010163 = 4515245) B4515245
theorem B2006775 : Blo 2005435 2006775 := bstep (se 1 (by rfl) ⟨1505081, by rfl⟩ : syracuseStep 2006775 = 3010163) B3010163
theorem B3616285 : Blo 2005435 3616285 := bbase (se 3 (by rfl) ⟨678053, by rfl⟩ : syracuseStep 3616285 = 1356107) (by norm_num)
theorem B4821713 : Blo 2005435 4821713 := bstep (se 2 (by rfl) ⟨1808142, by rfl⟩ : syracuseStep 4821713 = 3616285) B3616285
theorem B3214475 : Blo 2005435 3214475 := bstep (se 1 (by rfl) ⟨2410856, by rfl⟩ : syracuseStep 3214475 = 4821713) B4821713
theorem B2142983 : Blo 2005435 2142983 := bstep (se 1 (by rfl) ⟨1607237, by rfl⟩ : syracuseStep 2142983 = 3214475) B3214475
theorem B5714621 : Blo 2005435 5714621 := bstep (se 3 (by rfl) ⟨1071491, by rfl⟩ : syracuseStep 5714621 = 2142983) B2142983
theorem B3809747 : Blo 2005435 3809747 := bstep (se 1 (by rfl) ⟨2857310, by rfl⟩ : syracuseStep 3809747 = 5714621) B5714621
theorem B2539831 : Blo 2005435 2539831 := bstep (se 1 (by rfl) ⟨1904873, by rfl⟩ : syracuseStep 2539831 = 3809747) B3809747
theorem B3386441 : Blo 2005435 3386441 := bstep (se 2 (by rfl) ⟨1269915, by rfl⟩ : syracuseStep 3386441 = 2539831) B2539831
theorem B2257627 : Blo 2005435 2257627 := bstep (se 1 (by rfl) ⟨1693220, by rfl⟩ : syracuseStep 2257627 = 3386441) B3386441
theorem B3010169 : Blo 2005435 3010169 := bstep (se 2 (by rfl) ⟨1128813, by rfl⟩ : syracuseStep 3010169 = 2257627) B2257627
theorem B2006779 : Blo 2005435 2006779 := bstep (se 1 (by rfl) ⟨1505084, by rfl⟩ : syracuseStep 2006779 = 3010169) B3010169
theorem B31315349 : Blo 2005435 31315349 := bbase (se 6 (by rfl) ⟨733953, by rfl⟩ : syracuseStep 31315349 = 1467907) (by norm_num)
theorem B83507597 : Blo 2005435 83507597 := bstep (se 3 (by rfl) ⟨15657674, by rfl⟩ : syracuseStep 83507597 = 31315349) B31315349
theorem B55671731 : Blo 2005435 55671731 := bstep (se 1 (by rfl) ⟨41753798, by rfl⟩ : syracuseStep 55671731 = 83507597) B83507597
theorem B37114487 : Blo 2005435 37114487 := bstep (se 1 (by rfl) ⟨27835865, by rfl⟩ : syracuseStep 37114487 = 55671731) B55671731
theorem B24742991 : Blo 2005435 24742991 := bstep (se 1 (by rfl) ⟨18557243, by rfl⟩ : syracuseStep 24742991 = 37114487) B37114487
theorem B16495327 : Blo 2005435 16495327 := bstep (se 1 (by rfl) ⟨12371495, by rfl⟩ : syracuseStep 16495327 = 24742991) B24742991
theorem B21993769 : Blo 2005435 21993769 := bstep (se 2 (by rfl) ⟨8247663, by rfl⟩ : syracuseStep 21993769 = 16495327) B16495327
theorem B29325025 : Blo 2005435 29325025 := bstep (se 2 (by rfl) ⟨10996884, by rfl⟩ : syracuseStep 29325025 = 21993769) B21993769
theorem B39100033 : Blo 2005435 39100033 := bstep (se 2 (by rfl) ⟨14662512, by rfl⟩ : syracuseStep 39100033 = 29325025) B29325025
theorem B52133377 : Blo 2005435 52133377 := bstep (se 2 (by rfl) ⟨19550016, by rfl⟩ : syracuseStep 52133377 = 39100033) B39100033
theorem B69511169 : Blo 2005435 69511169 := bstep (se 2 (by rfl) ⟨26066688, by rfl⟩ : syracuseStep 69511169 = 52133377) B52133377
theorem B46340779 : Blo 2005435 46340779 := bstep (se 1 (by rfl) ⟨34755584, by rfl⟩ : syracuseStep 46340779 = 69511169) B69511169
theorem B61787705 : Blo 2005435 61787705 := bstep (se 2 (by rfl) ⟨23170389, by rfl⟩ : syracuseStep 61787705 = 46340779) B46340779
theorem B164767213 : Blo 2005435 164767213 := bstep (se 3 (by rfl) ⟨30893852, by rfl⟩ : syracuseStep 164767213 = 61787705) B61787705
theorem B219689617 : Blo 2005435 219689617 := bstep (se 2 (by rfl) ⟨82383606, by rfl⟩ : syracuseStep 219689617 = 164767213) B164767213
theorem B292919489 : Blo 2005435 292919489 := bstep (se 2 (by rfl) ⟨109844808, by rfl⟩ : syracuseStep 292919489 = 219689617) B219689617
theorem B195279659 : Blo 2005435 195279659 := bstep (se 1 (by rfl) ⟨146459744, by rfl⟩ : syracuseStep 195279659 = 292919489) B292919489
theorem B130186439 : Blo 2005435 130186439 := bstep (se 1 (by rfl) ⟨97639829, by rfl⟩ : syracuseStep 130186439 = 195279659) B195279659
theorem B86790959 : Blo 2005435 86790959 := bstep (se 1 (by rfl) ⟨65093219, by rfl⟩ : syracuseStep 86790959 = 130186439) B130186439
theorem B57860639 : Blo 2005435 57860639 := bstep (se 1 (by rfl) ⟨43395479, by rfl⟩ : syracuseStep 57860639 = 86790959) B86790959
theorem B38573759 : Blo 2005435 38573759 := bstep (se 1 (by rfl) ⟨28930319, by rfl⟩ : syracuseStep 38573759 = 57860639) B57860639
theorem B25715839 : Blo 2005435 25715839 := bstep (se 1 (by rfl) ⟨19286879, by rfl⟩ : syracuseStep 25715839 = 38573759) B38573759
theorem B34287785 : Blo 2005435 34287785 := bstep (se 2 (by rfl) ⟨12857919, by rfl⟩ : syracuseStep 34287785 = 25715839) B25715839
theorem B22858523 : Blo 2005435 22858523 := bstep (se 1 (by rfl) ⟨17143892, by rfl⟩ : syracuseStep 22858523 = 34287785) B34287785
theorem B15239015 : Blo 2005435 15239015 := bstep (se 1 (by rfl) ⟨11429261, by rfl⟩ : syracuseStep 15239015 = 22858523) B22858523
theorem B10159343 : Blo 2005435 10159343 := bstep (se 1 (by rfl) ⟨7619507, by rfl⟩ : syracuseStep 10159343 = 15239015) B15239015
theorem B6772895 : Blo 2005435 6772895 := bstep (se 1 (by rfl) ⟨5079671, by rfl⟩ : syracuseStep 6772895 = 10159343) B10159343
theorem B4515263 : Blo 2005435 4515263 := bstep (se 1 (by rfl) ⟨3386447, by rfl⟩ : syracuseStep 4515263 = 6772895) B6772895
theorem B3010175 : Blo 2005435 3010175 := bstep (se 1 (by rfl) ⟨2257631, by rfl⟩ : syracuseStep 3010175 = 4515263) B4515263
theorem B2006783 : Blo 2005435 2006783 := bstep (se 1 (by rfl) ⟨1505087, by rfl⟩ : syracuseStep 2006783 = 3010175) B3010175
theorem B3010181 : Blo 2005435 3010181 := bbase (se 4 (by rfl) ⟨282204, by rfl⟩ : syracuseStep 3010181 = 564409) (by norm_num)
theorem B2006787 : Blo 2005435 2006787 := bstep (se 1 (by rfl) ⟨1505090, by rfl⟩ : syracuseStep 2006787 = 3010181) B3010181
theorem B3386461 : Blo 2005435 3386461 := bbase (se 3 (by rfl) ⟨634961, by rfl⟩ : syracuseStep 3386461 = 1269923) (by norm_num)
theorem B4515281 : Blo 2005435 4515281 := bstep (se 2 (by rfl) ⟨1693230, by rfl⟩ : syracuseStep 4515281 = 3386461) B3386461
theorem B3010187 : Blo 2005435 3010187 := bstep (se 1 (by rfl) ⟨2257640, by rfl⟩ : syracuseStep 3010187 = 4515281) B4515281
theorem B2006791 : Blo 2005435 2006791 := bstep (se 1 (by rfl) ⟨1505093, by rfl⟩ : syracuseStep 2006791 = 3010187) B3010187
theorem B2257645 : Blo 2005435 2257645 := bbase (se 3 (by rfl) ⟨423308, by rfl⟩ : syracuseStep 2257645 = 846617) (by norm_num)
theorem B3010193 : Blo 2005435 3010193 := bstep (se 2 (by rfl) ⟨1128822, by rfl⟩ : syracuseStep 3010193 = 2257645) B2257645
theorem B2006795 : Blo 2005435 2006795 := bstep (se 1 (by rfl) ⟨1505096, by rfl⟩ : syracuseStep 2006795 = 3010193) B3010193
theorem B6772949 : Blo 2005435 6772949 := bbase (se 7 (by rfl) ⟨79370, by rfl⟩ : syracuseStep 6772949 = 158741) (by norm_num)
theorem B4515299 : Blo 2005435 4515299 := bstep (se 1 (by rfl) ⟨3386474, by rfl⟩ : syracuseStep 4515299 = 6772949) B6772949
theorem B3010199 : Blo 2005435 3010199 := bstep (se 1 (by rfl) ⟨2257649, by rfl⟩ : syracuseStep 3010199 = 4515299) B4515299
theorem B2006799 : Blo 2005435 2006799 := bstep (se 1 (by rfl) ⟨1505099, by rfl⟩ : syracuseStep 2006799 = 3010199) B3010199
theorem B3010205 : Blo 2005435 3010205 := bbase (se 3 (by rfl) ⟨564413, by rfl⟩ : syracuseStep 3010205 = 1128827) (by norm_num)
theorem B2006803 : Blo 2005435 2006803 := bstep (se 1 (by rfl) ⟨1505102, by rfl⟩ : syracuseStep 2006803 = 3010205) B3010205
theorem B4515317 : Blo 2005435 4515317 := bbase (se 5 (by rfl) ⟨211655, by rfl⟩ : syracuseStep 4515317 = 423311) (by norm_num)
theorem B3010211 : Blo 2005435 3010211 := bstep (se 1 (by rfl) ⟨2257658, by rfl⟩ : syracuseStep 3010211 = 4515317) B4515317
theorem B2006807 : Blo 2005435 2006807 := bstep (se 1 (by rfl) ⟨1505105, by rfl⟩ : syracuseStep 2006807 = 3010211) B3010211
theorem B8247781 : Blo 2005435 8247781 := bbase (se 4 (by rfl) ⟨773229, by rfl⟩ : syracuseStep 8247781 = 1546459) (by norm_num)
theorem B10997041 : Blo 2005435 10997041 := bstep (se 2 (by rfl) ⟨4123890, by rfl⟩ : syracuseStep 10997041 = 8247781) B8247781
theorem B14662721 : Blo 2005435 14662721 := bstep (se 2 (by rfl) ⟨5498520, by rfl⟩ : syracuseStep 14662721 = 10997041) B10997041
theorem B9775147 : Blo 2005435 9775147 := bstep (se 1 (by rfl) ⟨7331360, by rfl⟩ : syracuseStep 9775147 = 14662721) B14662721
theorem B13033529 : Blo 2005435 13033529 := bstep (se 2 (by rfl) ⟨4887573, by rfl⟩ : syracuseStep 13033529 = 9775147) B9775147
theorem B556097237 : Blo 2005435 556097237 := bstep (se 7 (by rfl) ⟨6516764, by rfl⟩ : syracuseStep 556097237 = 13033529) B13033529
theorem B370731491 : Blo 2005435 370731491 := bstep (se 1 (by rfl) ⟨278048618, by rfl⟩ : syracuseStep 370731491 = 556097237) B556097237
theorem B247154327 : Blo 2005435 247154327 := bstep (se 1 (by rfl) ⟨185365745, by rfl⟩ : syracuseStep 247154327 = 370731491) B370731491
theorem B164769551 : Blo 2005435 164769551 := bstep (se 1 (by rfl) ⟨123577163, by rfl⟩ : syracuseStep 164769551 = 247154327) B247154327
theorem B109846367 : Blo 2005435 109846367 := bstep (se 1 (by rfl) ⟨82384775, by rfl⟩ : syracuseStep 109846367 = 164769551) B164769551
theorem B73230911 : Blo 2005435 73230911 := bstep (se 1 (by rfl) ⟨54923183, by rfl⟩ : syracuseStep 73230911 = 109846367) B109846367
theorem B48820607 : Blo 2005435 48820607 := bstep (se 1 (by rfl) ⟨36615455, by rfl⟩ : syracuseStep 48820607 = 73230911) B73230911
theorem B32547071 : Blo 2005435 32547071 := bstep (se 1 (by rfl) ⟨24410303, by rfl⟩ : syracuseStep 32547071 = 48820607) B48820607
theorem B21698047 : Blo 2005435 21698047 := bstep (se 1 (by rfl) ⟨16273535, by rfl⟩ : syracuseStep 21698047 = 32547071) B32547071
theorem B28930729 : Blo 2005435 28930729 := bstep (se 2 (by rfl) ⟨10849023, by rfl⟩ : syracuseStep 28930729 = 21698047) B21698047
theorem B38574305 : Blo 2005435 38574305 := bstep (se 2 (by rfl) ⟨14465364, by rfl⟩ : syracuseStep 38574305 = 28930729) B28930729
theorem B25716203 : Blo 2005435 25716203 := bstep (se 1 (by rfl) ⟨19287152, by rfl⟩ : syracuseStep 25716203 = 38574305) B38574305
theorem B17144135 : Blo 2005435 17144135 := bstep (se 1 (by rfl) ⟨12858101, by rfl⟩ : syracuseStep 17144135 = 25716203) B25716203
theorem B11429423 : Blo 2005435 11429423 := bstep (se 1 (by rfl) ⟨8572067, by rfl⟩ : syracuseStep 11429423 = 17144135) B17144135
theorem B7619615 : Blo 2005435 7619615 := bstep (se 1 (by rfl) ⟨5714711, by rfl⟩ : syracuseStep 7619615 = 11429423) B11429423
theorem B5079743 : Blo 2005435 5079743 := bstep (se 1 (by rfl) ⟨3809807, by rfl⟩ : syracuseStep 5079743 = 7619615) B7619615
theorem B3386495 : Blo 2005435 3386495 := bstep (se 1 (by rfl) ⟨2539871, by rfl⟩ : syracuseStep 3386495 = 5079743) B5079743
theorem B2257663 : Blo 2005435 2257663 := bstep (se 1 (by rfl) ⟨1693247, by rfl⟩ : syracuseStep 2257663 = 3386495) B3386495
theorem B3010217 : Blo 2005435 3010217 := bstep (se 2 (by rfl) ⟨1128831, by rfl⟩ : syracuseStep 3010217 = 2257663) B2257663
theorem B2006811 : Blo 2005435 2006811 := bstep (se 1 (by rfl) ⟨1505108, by rfl⟩ : syracuseStep 2006811 = 3010217) B3010217
theorem B2143021 : Blo 2005435 2143021 := bbase (se 3 (by rfl) ⟨401816, by rfl⟩ : syracuseStep 2143021 = 803633) (by norm_num)
theorem B2857361 : Blo 2005435 2857361 := bstep (se 2 (by rfl) ⟨1071510, by rfl⟩ : syracuseStep 2857361 = 2143021) B2143021
theorem B7619629 : Blo 2005435 7619629 := bstep (se 3 (by rfl) ⟨1428680, by rfl⟩ : syracuseStep 7619629 = 2857361) B2857361
theorem B10159505 : Blo 2005435 10159505 := bstep (se 2 (by rfl) ⟨3809814, by rfl⟩ : syracuseStep 10159505 = 7619629) B7619629
theorem B6773003 : Blo 2005435 6773003 := bstep (se 1 (by rfl) ⟨5079752, by rfl⟩ : syracuseStep 6773003 = 10159505) B10159505
theorem B4515335 : Blo 2005435 4515335 := bstep (se 1 (by rfl) ⟨3386501, by rfl⟩ : syracuseStep 4515335 = 6773003) B6773003
theorem B3010223 : Blo 2005435 3010223 := bstep (se 1 (by rfl) ⟨2257667, by rfl⟩ : syracuseStep 3010223 = 4515335) B4515335
theorem B2006815 : Blo 2005435 2006815 := bstep (se 1 (by rfl) ⟨1505111, by rfl⟩ : syracuseStep 2006815 = 3010223) B3010223
theorem B3010229 : Blo 2005435 3010229 := bbase (se 5 (by rfl) ⟨141104, by rfl⟩ : syracuseStep 3010229 = 282209) (by norm_num)
theorem B2006819 : Blo 2005435 2006819 := bstep (se 1 (by rfl) ⟨1505114, by rfl⟩ : syracuseStep 2006819 = 3010229) B3010229
theorem B5079773 : Blo 2005435 5079773 := bbase (se 3 (by rfl) ⟨952457, by rfl⟩ : syracuseStep 5079773 = 1904915) (by norm_num)
theorem B3386515 : Blo 2005435 3386515 := bstep (se 1 (by rfl) ⟨2539886, by rfl⟩ : syracuseStep 3386515 = 5079773) B5079773
theorem B4515353 : Blo 2005435 4515353 := bstep (se 2 (by rfl) ⟨1693257, by rfl⟩ : syracuseStep 4515353 = 3386515) B3386515
theorem B3010235 : Blo 2005435 3010235 := bstep (se 1 (by rfl) ⟨2257676, by rfl⟩ : syracuseStep 3010235 = 4515353) B4515353
theorem B2006823 : Blo 2005435 2006823 := bstep (se 1 (by rfl) ⟨1505117, by rfl⟩ : syracuseStep 2006823 = 3010235) B3010235
theorem B2257681 : Blo 2005435 2257681 := bbase (se 2 (by rfl) ⟨846630, by rfl⟩ : syracuseStep 2257681 = 1693261) (by norm_num)
theorem B3010241 : Blo 2005435 3010241 := bstep (se 2 (by rfl) ⟨1128840, by rfl⟩ : syracuseStep 3010241 = 2257681) B2257681
theorem B2006827 : Blo 2005435 2006827 := bstep (se 1 (by rfl) ⟨1505120, by rfl⟩ : syracuseStep 2006827 = 3010241) B3010241
theorem B3809845 : Blo 2005435 3809845 := bbase (se 5 (by rfl) ⟨178586, by rfl⟩ : syracuseStep 3809845 = 357173) (by norm_num)
theorem B5079793 : Blo 2005435 5079793 := bstep (se 2 (by rfl) ⟨1904922, by rfl⟩ : syracuseStep 5079793 = 3809845) B3809845
theorem B6773057 : Blo 2005435 6773057 := bstep (se 2 (by rfl) ⟨2539896, by rfl⟩ : syracuseStep 6773057 = 5079793) B5079793
theorem B4515371 : Blo 2005435 4515371 := bstep (se 1 (by rfl) ⟨3386528, by rfl⟩ : syracuseStep 4515371 = 6773057) B6773057
theorem B3010247 : Blo 2005435 3010247 := bstep (se 1 (by rfl) ⟨2257685, by rfl⟩ : syracuseStep 3010247 = 4515371) B4515371
theorem B2006831 : Blo 2005435 2006831 := bstep (se 1 (by rfl) ⟨1505123, by rfl⟩ : syracuseStep 2006831 = 3010247) B3010247
theorem B3010253 : Blo 2005435 3010253 := bbase (se 3 (by rfl) ⟨564422, by rfl⟩ : syracuseStep 3010253 = 1128845) (by norm_num)
theorem B2006835 : Blo 2005435 2006835 := bstep (se 1 (by rfl) ⟨1505126, by rfl⟩ : syracuseStep 2006835 = 3010253) B3010253
theorem B4515389 : Blo 2005435 4515389 := bbase (se 3 (by rfl) ⟨846635, by rfl⟩ : syracuseStep 4515389 = 1693271) (by norm_num)
theorem B3010259 : Blo 2005435 3010259 := bstep (se 1 (by rfl) ⟨2257694, by rfl⟩ : syracuseStep 3010259 = 4515389) B4515389
theorem B2006839 : Blo 2005435 2006839 := bstep (se 1 (by rfl) ⟨1505129, by rfl⟩ : syracuseStep 2006839 = 3010259) B3010259
theorem B3386549 : Blo 2005435 3386549 := bbase (se 5 (by rfl) ⟨158744, by rfl⟩ : syracuseStep 3386549 = 317489) (by norm_num)
theorem B2257699 : Blo 2005435 2257699 := bstep (se 1 (by rfl) ⟨1693274, by rfl⟩ : syracuseStep 2257699 = 3386549) B3386549
theorem B3010265 : Blo 2005435 3010265 := bstep (se 2 (by rfl) ⟨1128849, by rfl⟩ : syracuseStep 3010265 = 2257699) B2257699
theorem B2006843 : Blo 2005435 2006843 := bstep (se 1 (by rfl) ⟨1505132, by rfl⟩ : syracuseStep 2006843 = 3010265) B3010265
theorem B2034229 : Blo 2005435 2034229 := bbase (se 5 (by rfl) ⟨95354, by rfl⟩ : syracuseStep 2034229 = 190709) (by norm_num)
theorem B2712305 : Blo 2005435 2712305 := bstep (se 2 (by rfl) ⟨1017114, by rfl⟩ : syracuseStep 2712305 = 2034229) B2034229
theorem B7232813 : Blo 2005435 7232813 := bstep (se 3 (by rfl) ⟨1356152, by rfl⟩ : syracuseStep 7232813 = 2712305) B2712305
theorem B4821875 : Blo 2005435 4821875 := bstep (se 1 (by rfl) ⟨3616406, by rfl⟩ : syracuseStep 4821875 = 7232813) B7232813
theorem B3214583 : Blo 2005435 3214583 := bstep (se 1 (by rfl) ⟨2410937, by rfl⟩ : syracuseStep 3214583 = 4821875) B4821875
theorem B2143055 : Blo 2005435 2143055 := bstep (se 1 (by rfl) ⟨1607291, by rfl⟩ : syracuseStep 2143055 = 3214583) B3214583
theorem B5714813 : Blo 2005435 5714813 := bstep (se 3 (by rfl) ⟨1071527, by rfl⟩ : syracuseStep 5714813 = 2143055) B2143055
theorem B15239501 : Blo 2005435 15239501 := bstep (se 3 (by rfl) ⟨2857406, by rfl⟩ : syracuseStep 15239501 = 5714813) B5714813
theorem B10159667 : Blo 2005435 10159667 := bstep (se 1 (by rfl) ⟨7619750, by rfl⟩ : syracuseStep 10159667 = 15239501) B15239501
theorem B6773111 : Blo 2005435 6773111 := bstep (se 1 (by rfl) ⟨5079833, by rfl⟩ : syracuseStep 6773111 = 10159667) B10159667
theorem B4515407 : Blo 2005435 4515407 := bstep (se 1 (by rfl) ⟨3386555, by rfl⟩ : syracuseStep 4515407 = 6773111) B6773111
theorem B3010271 : Blo 2005435 3010271 := bstep (se 1 (by rfl) ⟨2257703, by rfl⟩ : syracuseStep 3010271 = 4515407) B4515407
theorem B2006847 : Blo 2005435 2006847 := bstep (se 1 (by rfl) ⟨1505135, by rfl⟩ : syracuseStep 2006847 = 3010271) B3010271
theorem B3010277 : Blo 2005435 3010277 := bbase (se 4 (by rfl) ⟨282213, by rfl⟩ : syracuseStep 3010277 = 564427) (by norm_num)
theorem B2006851 : Blo 2005435 2006851 := bstep (se 1 (by rfl) ⟨1505138, by rfl⟩ : syracuseStep 2006851 = 3010277) B3010277
theorem B5714837 : Blo 2005435 5714837 := bbase (se 6 (by rfl) ⟨133941, by rfl⟩ : syracuseStep 5714837 = 267883) (by norm_num)
theorem B3809891 : Blo 2005435 3809891 := bstep (se 1 (by rfl) ⟨2857418, by rfl⟩ : syracuseStep 3809891 = 5714837) B5714837
theorem B2539927 : Blo 2005435 2539927 := bstep (se 1 (by rfl) ⟨1904945, by rfl⟩ : syracuseStep 2539927 = 3809891) B3809891
theorem B3386569 : Blo 2005435 3386569 := bstep (se 2 (by rfl) ⟨1269963, by rfl⟩ : syracuseStep 3386569 = 2539927) B2539927
theorem B4515425 : Blo 2005435 4515425 := bstep (se 2 (by rfl) ⟨1693284, by rfl⟩ : syracuseStep 4515425 = 3386569) B3386569
theorem B3010283 : Blo 2005435 3010283 := bstep (se 1 (by rfl) ⟨2257712, by rfl⟩ : syracuseStep 3010283 = 4515425) B4515425
theorem B2006855 : Blo 2005435 2006855 := bstep (se 1 (by rfl) ⟨1505141, by rfl⟩ : syracuseStep 2006855 = 3010283) B3010283
theorem B2257717 : Blo 2005435 2257717 := bbase (se 5 (by rfl) ⟨105830, by rfl⟩ : syracuseStep 2257717 = 211661) (by norm_num)
theorem B3010289 : Blo 2005435 3010289 := bstep (se 2 (by rfl) ⟨1128858, by rfl⟩ : syracuseStep 3010289 = 2257717) B2257717
theorem B2006859 : Blo 2005435 2006859 := bstep (se 1 (by rfl) ⟨1505144, by rfl⟩ : syracuseStep 2006859 = 3010289) B3010289
theorem B2539937 : Blo 2005435 2539937 := bbase (se 2 (by rfl) ⟨952476, by rfl⟩ : syracuseStep 2539937 = 1904953) (by norm_num)
theorem B6773165 : Blo 2005435 6773165 := bstep (se 3 (by rfl) ⟨1269968, by rfl⟩ : syracuseStep 6773165 = 2539937) B2539937
theorem B4515443 : Blo 2005435 4515443 := bstep (se 1 (by rfl) ⟨3386582, by rfl⟩ : syracuseStep 4515443 = 6773165) B6773165
theorem B3010295 : Blo 2005435 3010295 := bstep (se 1 (by rfl) ⟨2257721, by rfl⟩ : syracuseStep 3010295 = 4515443) B4515443
theorem B2006863 : Blo 2005435 2006863 := bstep (se 1 (by rfl) ⟨1505147, by rfl⟩ : syracuseStep 2006863 = 3010295) B3010295
theorem B3010301 : Blo 2005435 3010301 := bbase (se 3 (by rfl) ⟨564431, by rfl⟩ : syracuseStep 3010301 = 1128863) (by norm_num)
theorem B2006867 : Blo 2005435 2006867 := bstep (se 1 (by rfl) ⟨1505150, by rfl⟩ : syracuseStep 2006867 = 3010301) B3010301
theorem B4515461 : Blo 2005435 4515461 := bbase (se 4 (by rfl) ⟨423324, by rfl⟩ : syracuseStep 4515461 = 846649) (by norm_num)
theorem B3010307 : Blo 2005435 3010307 := bstep (se 1 (by rfl) ⟨2257730, by rfl⟩ : syracuseStep 3010307 = 4515461) B4515461
theorem B2006871 : Blo 2005435 2006871 := bstep (se 1 (by rfl) ⟨1505153, by rfl⟩ : syracuseStep 2006871 = 3010307) B3010307
theorem B6102773 : Blo 2005435 6102773 := bbase (se 5 (by rfl) ⟨286067, by rfl⟩ : syracuseStep 6102773 = 572135) (by norm_num)
theorem B4068515 : Blo 2005435 4068515 := bstep (se 1 (by rfl) ⟨3051386, by rfl⟩ : syracuseStep 4068515 = 6102773) B6102773
theorem B10849373 : Blo 2005435 10849373 := bstep (se 3 (by rfl) ⟨2034257, by rfl⟩ : syracuseStep 10849373 = 4068515) B4068515
theorem B7232915 : Blo 2005435 7232915 := bstep (se 1 (by rfl) ⟨5424686, by rfl⟩ : syracuseStep 7232915 = 10849373) B10849373
theorem B4821943 : Blo 2005435 4821943 := bstep (se 1 (by rfl) ⟨3616457, by rfl⟩ : syracuseStep 4821943 = 7232915) B7232915
theorem B6429257 : Blo 2005435 6429257 := bstep (se 2 (by rfl) ⟨2410971, by rfl⟩ : syracuseStep 6429257 = 4821943) B4821943
theorem B4286171 : Blo 2005435 4286171 := bstep (se 1 (by rfl) ⟨3214628, by rfl⟩ : syracuseStep 4286171 = 6429257) B6429257
theorem B2857447 : Blo 2005435 2857447 := bstep (se 1 (by rfl) ⟨2143085, by rfl⟩ : syracuseStep 2857447 = 4286171) B4286171
theorem B3809929 : Blo 2005435 3809929 := bstep (se 2 (by rfl) ⟨1428723, by rfl⟩ : syracuseStep 3809929 = 2857447) B2857447
theorem B5079905 : Blo 2005435 5079905 := bstep (se 2 (by rfl) ⟨1904964, by rfl⟩ : syracuseStep 5079905 = 3809929) B3809929
theorem B3386603 : Blo 2005435 3386603 := bstep (se 1 (by rfl) ⟨2539952, by rfl⟩ : syracuseStep 3386603 = 5079905) B5079905
theorem B2257735 : Blo 2005435 2257735 := bstep (se 1 (by rfl) ⟨1693301, by rfl⟩ : syracuseStep 2257735 = 3386603) B3386603
theorem B3010313 : Blo 2005435 3010313 := bstep (se 2 (by rfl) ⟨1128867, by rfl⟩ : syracuseStep 3010313 = 2257735) B2257735
theorem B2006875 : Blo 2005435 2006875 := bstep (se 1 (by rfl) ⟨1505156, by rfl⟩ : syracuseStep 2006875 = 3010313) B3010313
theorem B10159829 : Blo 2005435 10159829 := bbase (se 7 (by rfl) ⟨119060, by rfl⟩ : syracuseStep 10159829 = 238121) (by norm_num)
theorem B6773219 : Blo 2005435 6773219 := bstep (se 1 (by rfl) ⟨5079914, by rfl⟩ : syracuseStep 6773219 = 10159829) B10159829
theorem B4515479 : Blo 2005435 4515479 := bstep (se 1 (by rfl) ⟨3386609, by rfl⟩ : syracuseStep 4515479 = 6773219) B6773219
theorem B3010319 : Blo 2005435 3010319 := bstep (se 1 (by rfl) ⟨2257739, by rfl⟩ : syracuseStep 3010319 = 4515479) B4515479
theorem B2006879 : Blo 2005435 2006879 := bstep (se 1 (by rfl) ⟨1505159, by rfl⟩ : syracuseStep 2006879 = 3010319) B3010319
theorem B3010325 : Blo 2005435 3010325 := bbase (se 6 (by rfl) ⟨70554, by rfl⟩ : syracuseStep 3010325 = 141109) (by norm_num)
theorem B2006883 : Blo 2005435 2006883 := bstep (se 1 (by rfl) ⟨1505162, by rfl⟩ : syracuseStep 2006883 = 3010325) B3010325
theorem B3432829 : Blo 2005435 3432829 := bbase (se 3 (by rfl) ⟨643655, by rfl⟩ : syracuseStep 3432829 = 1287311) (by norm_num)
theorem B4577105 : Blo 2005435 4577105 := bstep (se 2 (by rfl) ⟨1716414, by rfl⟩ : syracuseStep 4577105 = 3432829) B3432829
theorem B12205613 : Blo 2005435 12205613 := bstep (se 3 (by rfl) ⟨2288552, by rfl⟩ : syracuseStep 12205613 = 4577105) B4577105
theorem B32548301 : Blo 2005435 32548301 := bstep (se 3 (by rfl) ⟨6102806, by rfl⟩ : syracuseStep 32548301 = 12205613) B12205613
theorem B21698867 : Blo 2005435 21698867 := bstep (se 1 (by rfl) ⟨16274150, by rfl⟩ : syracuseStep 21698867 = 32548301) B32548301
theorem B57863645 : Blo 2005435 57863645 := bstep (se 3 (by rfl) ⟨10849433, by rfl⟩ : syracuseStep 57863645 = 21698867) B21698867
theorem B38575763 : Blo 2005435 38575763 := bstep (se 1 (by rfl) ⟨28931822, by rfl⟩ : syracuseStep 38575763 = 57863645) B57863645
theorem B25717175 : Blo 2005435 25717175 := bstep (se 1 (by rfl) ⟨19287881, by rfl⟩ : syracuseStep 25717175 = 38575763) B38575763
theorem B17144783 : Blo 2005435 17144783 := bstep (se 1 (by rfl) ⟨12858587, by rfl⟩ : syracuseStep 17144783 = 25717175) B25717175
theorem B11429855 : Blo 2005435 11429855 := bstep (se 1 (by rfl) ⟨8572391, by rfl⟩ : syracuseStep 11429855 = 17144783) B17144783
theorem B7619903 : Blo 2005435 7619903 := bstep (se 1 (by rfl) ⟨5714927, by rfl⟩ : syracuseStep 7619903 = 11429855) B11429855
theorem B5079935 : Blo 2005435 5079935 := bstep (se 1 (by rfl) ⟨3809951, by rfl⟩ : syracuseStep 5079935 = 7619903) B7619903
theorem B3386623 : Blo 2005435 3386623 := bstep (se 1 (by rfl) ⟨2539967, by rfl⟩ : syracuseStep 3386623 = 5079935) B5079935
theorem B4515497 : Blo 2005435 4515497 := bstep (se 2 (by rfl) ⟨1693311, by rfl⟩ : syracuseStep 4515497 = 3386623) B3386623
theorem B3010331 : Blo 2005435 3010331 := bstep (se 1 (by rfl) ⟨2257748, by rfl⟩ : syracuseStep 3010331 = 4515497) B4515497
theorem B2006887 : Blo 2005435 2006887 := bstep (se 1 (by rfl) ⟨1505165, by rfl⟩ : syracuseStep 2006887 = 3010331) B3010331
theorem B2257753 : Blo 2005435 2257753 := bbase (se 2 (by rfl) ⟨846657, by rfl⟩ : syracuseStep 2257753 = 1693315) (by norm_num)
theorem B3010337 : Blo 2005435 3010337 := bstep (se 2 (by rfl) ⟨1128876, by rfl⟩ : syracuseStep 3010337 = 2257753) B2257753
theorem B2006891 : Blo 2005435 2006891 := bstep (se 1 (by rfl) ⟨1505168, by rfl⟩ : syracuseStep 2006891 = 3010337) B3010337
theorem B4286213 : Blo 2005435 4286213 := bbase (se 4 (by rfl) ⟨401832, by rfl⟩ : syracuseStep 4286213 = 803665) (by norm_num)
theorem B2857475 : Blo 2005435 2857475 := bstep (se 1 (by rfl) ⟨2143106, by rfl⟩ : syracuseStep 2857475 = 4286213) B4286213
theorem B7619933 : Blo 2005435 7619933 := bstep (se 3 (by rfl) ⟨1428737, by rfl⟩ : syracuseStep 7619933 = 2857475) B2857475
theorem B5079955 : Blo 2005435 5079955 := bstep (se 1 (by rfl) ⟨3809966, by rfl⟩ : syracuseStep 5079955 = 7619933) B7619933
theorem B6773273 : Blo 2005435 6773273 := bstep (se 2 (by rfl) ⟨2539977, by rfl⟩ : syracuseStep 6773273 = 5079955) B5079955
theorem B4515515 : Blo 2005435 4515515 := bstep (se 1 (by rfl) ⟨3386636, by rfl⟩ : syracuseStep 4515515 = 6773273) B6773273
theorem B3010343 : Blo 2005435 3010343 := bstep (se 1 (by rfl) ⟨2257757, by rfl⟩ : syracuseStep 3010343 = 4515515) B4515515
theorem B2006895 : Blo 2005435 2006895 := bstep (se 1 (by rfl) ⟨1505171, by rfl⟩ : syracuseStep 2006895 = 3010343) B3010343
theorem B3010349 : Blo 2005435 3010349 := bbase (se 3 (by rfl) ⟨564440, by rfl⟩ : syracuseStep 3010349 = 1128881) (by norm_num)
theorem B2006899 : Blo 2005435 2006899 := bstep (se 1 (by rfl) ⟨1505174, by rfl⟩ : syracuseStep 2006899 = 3010349) B3010349
theorem B4515533 : Blo 2005435 4515533 := bbase (se 3 (by rfl) ⟨846662, by rfl⟩ : syracuseStep 4515533 = 1693325) (by norm_num)
theorem B3010355 : Blo 2005435 3010355 := bstep (se 1 (by rfl) ⟨2257766, by rfl⟩ : syracuseStep 3010355 = 4515533) B4515533
theorem B2006903 : Blo 2005435 2006903 := bstep (se 1 (by rfl) ⟨1505177, by rfl⟩ : syracuseStep 2006903 = 3010355) B3010355
theorem B2539993 : Blo 2005435 2539993 := bbase (se 2 (by rfl) ⟨952497, by rfl⟩ : syracuseStep 2539993 = 1904995) (by norm_num)
theorem B3386657 : Blo 2005435 3386657 := bstep (se 2 (by rfl) ⟨1269996, by rfl⟩ : syracuseStep 3386657 = 2539993) B2539993
theorem B2257771 : Blo 2005435 2257771 := bstep (se 1 (by rfl) ⟨1693328, by rfl⟩ : syracuseStep 2257771 = 3386657) B3386657
theorem B3010361 : Blo 2005435 3010361 := bstep (se 2 (by rfl) ⟨1128885, by rfl⟩ : syracuseStep 3010361 = 2257771) B2257771
theorem B2006907 : Blo 2005435 2006907 := bstep (se 1 (by rfl) ⟨1505180, by rfl⟩ : syracuseStep 2006907 = 3010361) B3010361
theorem B3214685 : Blo 2005435 3214685 := bbase (se 3 (by rfl) ⟨602753, by rfl⟩ : syracuseStep 3214685 = 1205507) (by norm_num)
theorem B8572493 : Blo 2005435 8572493 := bstep (se 3 (by rfl) ⟨1607342, by rfl⟩ : syracuseStep 8572493 = 3214685) B3214685
theorem B22859981 : Blo 2005435 22859981 := bstep (se 3 (by rfl) ⟨4286246, by rfl⟩ : syracuseStep 22859981 = 8572493) B8572493
theorem B15239987 : Blo 2005435 15239987 := bstep (se 1 (by rfl) ⟨11429990, by rfl⟩ : syracuseStep 15239987 = 22859981) B22859981
theorem B10159991 : Blo 2005435 10159991 := bstep (se 1 (by rfl) ⟨7619993, by rfl⟩ : syracuseStep 10159991 = 15239987) B15239987
theorem B6773327 : Blo 2005435 6773327 := bstep (se 1 (by rfl) ⟨5079995, by rfl⟩ : syracuseStep 6773327 = 10159991) B10159991
theorem B4515551 : Blo 2005435 4515551 := bstep (se 1 (by rfl) ⟨3386663, by rfl⟩ : syracuseStep 4515551 = 6773327) B6773327
theorem B3010367 : Blo 2005435 3010367 := bstep (se 1 (by rfl) ⟨2257775, by rfl⟩ : syracuseStep 3010367 = 4515551) B4515551
theorem B2006911 : Blo 2005435 2006911 := bstep (se 1 (by rfl) ⟨1505183, by rfl⟩ : syracuseStep 2006911 = 3010367) B3010367
theorem B3010373 : Blo 2005435 3010373 := bbase (se 4 (by rfl) ⟨282222, by rfl⟩ : syracuseStep 3010373 = 564445) (by norm_num)
theorem B2006915 : Blo 2005435 2006915 := bstep (se 1 (by rfl) ⟨1505186, by rfl⟩ : syracuseStep 2006915 = 3010373) B3010373
theorem B3386677 : Blo 2005435 3386677 := bbase (se 5 (by rfl) ⟨158750, by rfl⟩ : syracuseStep 3386677 = 317501) (by norm_num)
theorem B4515569 : Blo 2005435 4515569 := bstep (se 2 (by rfl) ⟨1693338, by rfl⟩ : syracuseStep 4515569 = 3386677) B3386677
theorem B3010379 : Blo 2005435 3010379 := bstep (se 1 (by rfl) ⟨2257784, by rfl⟩ : syracuseStep 3010379 = 4515569) B4515569
theorem B2006919 : Blo 2005435 2006919 := bstep (se 1 (by rfl) ⟨1505189, by rfl⟩ : syracuseStep 2006919 = 3010379) B3010379
theorem B2257789 : Blo 2005435 2257789 := bbase (se 3 (by rfl) ⟨423335, by rfl⟩ : syracuseStep 2257789 = 846671) (by norm_num)
theorem B3010385 : Blo 2005435 3010385 := bstep (se 2 (by rfl) ⟨1128894, by rfl⟩ : syracuseStep 3010385 = 2257789) B2257789
theorem B2006923 : Blo 2005435 2006923 := bstep (se 1 (by rfl) ⟨1505192, by rfl⟩ : syracuseStep 2006923 = 3010385) B3010385
theorem B6773381 : Blo 2005435 6773381 := bbase (se 4 (by rfl) ⟨635004, by rfl⟩ : syracuseStep 6773381 = 1270009) (by norm_num)
theorem B4515587 : Blo 2005435 4515587 := bstep (se 1 (by rfl) ⟨3386690, by rfl⟩ : syracuseStep 4515587 = 6773381) B6773381
theorem B3010391 : Blo 2005435 3010391 := bstep (se 1 (by rfl) ⟨2257793, by rfl⟩ : syracuseStep 3010391 = 4515587) B4515587
theorem B2006927 : Blo 2005435 2006927 := bstep (se 1 (by rfl) ⟨1505195, by rfl⟩ : syracuseStep 2006927 = 3010391) B3010391
theorem B3010397 : Blo 2005435 3010397 := bbase (se 3 (by rfl) ⟨564449, by rfl⟩ : syracuseStep 3010397 = 1128899) (by norm_num)
theorem B2006931 : Blo 2005435 2006931 := bstep (se 1 (by rfl) ⟨1505198, by rfl⟩ : syracuseStep 2006931 = 3010397) B3010397
theorem B4515605 : Blo 2005435 4515605 := bbase (se 6 (by rfl) ⟨105834, by rfl⟩ : syracuseStep 4515605 = 211669) (by norm_num)
theorem B3010403 : Blo 2005435 3010403 := bstep (se 1 (by rfl) ⟨2257802, by rfl⟩ : syracuseStep 3010403 = 4515605) B4515605
theorem B2006935 : Blo 2005435 2006935 := bstep (se 1 (by rfl) ⟨1505201, by rfl⟩ : syracuseStep 2006935 = 3010403) B3010403
theorem B7620101 : Blo 2005435 7620101 := bbase (se 4 (by rfl) ⟨714384, by rfl⟩ : syracuseStep 7620101 = 1428769) (by norm_num)
theorem B5080067 : Blo 2005435 5080067 := bstep (se 1 (by rfl) ⟨3810050, by rfl⟩ : syracuseStep 5080067 = 7620101) B7620101
theorem B3386711 : Blo 2005435 3386711 := bstep (se 1 (by rfl) ⟨2540033, by rfl⟩ : syracuseStep 3386711 = 5080067) B5080067
theorem B2257807 : Blo 2005435 2257807 := bstep (se 1 (by rfl) ⟨1693355, by rfl⟩ : syracuseStep 2257807 = 3386711) B3386711
theorem B3010409 : Blo 2005435 3010409 := bstep (se 2 (by rfl) ⟨1128903, by rfl⟩ : syracuseStep 3010409 = 2257807) B2257807
theorem B2006939 : Blo 2005435 2006939 := bstep (se 1 (by rfl) ⟨1505204, by rfl⟩ : syracuseStep 2006939 = 3010409) B3010409
theorem B5424869 : Blo 2005435 5424869 := bbase (se 4 (by rfl) ⟨508581, by rfl⟩ : syracuseStep 5424869 = 1017163) (by norm_num)
theorem B3616579 : Blo 2005435 3616579 := bstep (se 1 (by rfl) ⟨2712434, by rfl⟩ : syracuseStep 3616579 = 5424869) B5424869
theorem B4822105 : Blo 2005435 4822105 := bstep (se 2 (by rfl) ⟨1808289, by rfl⟩ : syracuseStep 4822105 = 3616579) B3616579
theorem B6429473 : Blo 2005435 6429473 := bstep (se 2 (by rfl) ⟨2411052, by rfl⟩ : syracuseStep 6429473 = 4822105) B4822105
theorem B4286315 : Blo 2005435 4286315 := bstep (se 1 (by rfl) ⟨3214736, by rfl⟩ : syracuseStep 4286315 = 6429473) B6429473
theorem B11430173 : Blo 2005435 11430173 := bstep (se 3 (by rfl) ⟨2143157, by rfl⟩ : syracuseStep 11430173 = 4286315) B4286315
theorem B7620115 : Blo 2005435 7620115 := bstep (se 1 (by rfl) ⟨5715086, by rfl⟩ : syracuseStep 7620115 = 11430173) B11430173
theorem B10160153 : Blo 2005435 10160153 := bstep (se 2 (by rfl) ⟨3810057, by rfl⟩ : syracuseStep 10160153 = 7620115) B7620115
theorem B6773435 : Blo 2005435 6773435 := bstep (se 1 (by rfl) ⟨5080076, by rfl⟩ : syracuseStep 6773435 = 10160153) B10160153
theorem B4515623 : Blo 2005435 4515623 := bstep (se 1 (by rfl) ⟨3386717, by rfl⟩ : syracuseStep 4515623 = 6773435) B6773435
theorem B3010415 : Blo 2005435 3010415 := bstep (se 1 (by rfl) ⟨2257811, by rfl⟩ : syracuseStep 3010415 = 4515623) B4515623
theorem B2006943 : Blo 2005435 2006943 := bstep (se 1 (by rfl) ⟨1505207, by rfl⟩ : syracuseStep 2006943 = 3010415) B3010415
theorem B3010421 : Blo 2005435 3010421 := bbase (se 5 (by rfl) ⟨141113, by rfl⟩ : syracuseStep 3010421 = 282227) (by norm_num)
theorem B2006947 : Blo 2005435 2006947 := bstep (se 1 (by rfl) ⟨1505210, by rfl⟩ : syracuseStep 2006947 = 3010421) B3010421
theorem B4286333 : Blo 2005435 4286333 := bbase (se 3 (by rfl) ⟨803687, by rfl⟩ : syracuseStep 4286333 = 1607375) (by norm_num)
theorem B2857555 : Blo 2005435 2857555 := bstep (se 1 (by rfl) ⟨2143166, by rfl⟩ : syracuseStep 2857555 = 4286333) B4286333
theorem B3810073 : Blo 2005435 3810073 := bstep (se 2 (by rfl) ⟨1428777, by rfl⟩ : syracuseStep 3810073 = 2857555) B2857555
theorem B5080097 : Blo 2005435 5080097 := bstep (se 2 (by rfl) ⟨1905036, by rfl⟩ : syracuseStep 5080097 = 3810073) B3810073
theorem B3386731 : Blo 2005435 3386731 := bstep (se 1 (by rfl) ⟨2540048, by rfl⟩ : syracuseStep 3386731 = 5080097) B5080097
theorem B4515641 : Blo 2005435 4515641 := bstep (se 2 (by rfl) ⟨1693365, by rfl⟩ : syracuseStep 4515641 = 3386731) B3386731
theorem B3010427 : Blo 2005435 3010427 := bstep (se 1 (by rfl) ⟨2257820, by rfl⟩ : syracuseStep 3010427 = 4515641) B4515641
theorem B2006951 : Blo 2005435 2006951 := bstep (se 1 (by rfl) ⟨1505213, by rfl⟩ : syracuseStep 2006951 = 3010427) B3010427
theorem B2257825 : Blo 2005435 2257825 := bbase (se 2 (by rfl) ⟨846684, by rfl⟩ : syracuseStep 2257825 = 1693369) (by norm_num)
theorem B3010433 : Blo 2005435 3010433 := bstep (se 2 (by rfl) ⟨1128912, by rfl⟩ : syracuseStep 3010433 = 2257825) B2257825
theorem B2006955 : Blo 2005435 2006955 := bstep (se 1 (by rfl) ⟨1505216, by rfl⟩ : syracuseStep 2006955 = 3010433) B3010433
theorem B5080117 : Blo 2005435 5080117 := bbase (se 5 (by rfl) ⟨238130, by rfl⟩ : syracuseStep 5080117 = 476261) (by norm_num)
theorem B6773489 : Blo 2005435 6773489 := bstep (se 2 (by rfl) ⟨2540058, by rfl⟩ : syracuseStep 6773489 = 5080117) B5080117
theorem B4515659 : Blo 2005435 4515659 := bstep (se 1 (by rfl) ⟨3386744, by rfl⟩ : syracuseStep 4515659 = 6773489) B6773489
theorem B3010439 : Blo 2005435 3010439 := bstep (se 1 (by rfl) ⟨2257829, by rfl⟩ : syracuseStep 3010439 = 4515659) B4515659
theorem B2006959 : Blo 2005435 2006959 := bstep (se 1 (by rfl) ⟨1505219, by rfl⟩ : syracuseStep 2006959 = 3010439) B3010439
theorem B3010445 : Blo 2005435 3010445 := bbase (se 3 (by rfl) ⟨564458, by rfl⟩ : syracuseStep 3010445 = 1128917) (by norm_num)
theorem B2006963 : Blo 2005435 2006963 := bstep (se 1 (by rfl) ⟨1505222, by rfl⟩ : syracuseStep 2006963 = 3010445) B3010445
theorem B4515677 : Blo 2005435 4515677 := bbase (se 3 (by rfl) ⟨846689, by rfl⟩ : syracuseStep 4515677 = 1693379) (by norm_num)
theorem B3010451 : Blo 2005435 3010451 := bstep (se 1 (by rfl) ⟨2257838, by rfl⟩ : syracuseStep 3010451 = 4515677) B4515677
theorem B2006967 : Blo 2005435 2006967 := bstep (se 1 (by rfl) ⟨1505225, by rfl⟩ : syracuseStep 2006967 = 3010451) B3010451
theorem B3386765 : Blo 2005435 3386765 := bbase (se 3 (by rfl) ⟨635018, by rfl⟩ : syracuseStep 3386765 = 1270037) (by norm_num)
theorem B2257843 : Blo 2005435 2257843 := bstep (se 1 (by rfl) ⟨1693382, by rfl⟩ : syracuseStep 2257843 = 3386765) B3386765
theorem B3010457 : Blo 2005435 3010457 := bstep (se 2 (by rfl) ⟨1128921, by rfl⟩ : syracuseStep 3010457 = 2257843) B2257843
theorem B2006971 : Blo 2005435 2006971 := bstep (se 1 (by rfl) ⟨1505228, by rfl⟩ : syracuseStep 2006971 = 3010457) B3010457
theorem B10849909 : Blo 2005435 10849909 := bbase (se 5 (by rfl) ⟨508589, by rfl⟩ : syracuseStep 10849909 = 1017179) (by norm_num)
theorem B14466545 : Blo 2005435 14466545 := bstep (se 2 (by rfl) ⟨5424954, by rfl⟩ : syracuseStep 14466545 = 10849909) B10849909
theorem B9644363 : Blo 2005435 9644363 := bstep (se 1 (by rfl) ⟨7233272, by rfl⟩ : syracuseStep 9644363 = 14466545) B14466545
theorem B6429575 : Blo 2005435 6429575 := bstep (se 1 (by rfl) ⟨4822181, by rfl⟩ : syracuseStep 6429575 = 9644363) B9644363
theorem B17145533 : Blo 2005435 17145533 := bstep (se 3 (by rfl) ⟨3214787, by rfl⟩ : syracuseStep 17145533 = 6429575) B6429575
theorem B11430355 : Blo 2005435 11430355 := bstep (se 1 (by rfl) ⟨8572766, by rfl⟩ : syracuseStep 11430355 = 17145533) B17145533
theorem B15240473 : Blo 2005435 15240473 := bstep (se 2 (by rfl) ⟨5715177, by rfl⟩ : syracuseStep 15240473 = 11430355) B11430355
theorem B10160315 : Blo 2005435 10160315 := bstep (se 1 (by rfl) ⟨7620236, by rfl⟩ : syracuseStep 10160315 = 15240473) B15240473
theorem B6773543 : Blo 2005435 6773543 := bstep (se 1 (by rfl) ⟨5080157, by rfl⟩ : syracuseStep 6773543 = 10160315) B10160315
theorem B4515695 : Blo 2005435 4515695 := bstep (se 1 (by rfl) ⟨3386771, by rfl⟩ : syracuseStep 4515695 = 6773543) B6773543
theorem B3010463 : Blo 2005435 3010463 := bstep (se 1 (by rfl) ⟨2257847, by rfl⟩ : syracuseStep 3010463 = 4515695) B4515695
theorem B2006975 : Blo 2005435 2006975 := bstep (se 1 (by rfl) ⟨1505231, by rfl⟩ : syracuseStep 2006975 = 3010463) B3010463
theorem B3010469 : Blo 2005435 3010469 := bbase (se 4 (by rfl) ⟨282231, by rfl⟩ : syracuseStep 3010469 = 564463) (by norm_num)
theorem B2006979 : Blo 2005435 2006979 := bstep (se 1 (by rfl) ⟨1505234, by rfl⟩ : syracuseStep 2006979 = 3010469) B3010469
theorem B2540089 : Blo 2005435 2540089 := bbase (se 2 (by rfl) ⟨952533, by rfl⟩ : syracuseStep 2540089 = 1905067) (by norm_num)
theorem B3386785 : Blo 2005435 3386785 := bstep (se 2 (by rfl) ⟨1270044, by rfl⟩ : syracuseStep 3386785 = 2540089) B2540089
theorem B4515713 : Blo 2005435 4515713 := bstep (se 2 (by rfl) ⟨1693392, by rfl⟩ : syracuseStep 4515713 = 3386785) B3386785
theorem B3010475 : Blo 2005435 3010475 := bstep (se 1 (by rfl) ⟨2257856, by rfl⟩ : syracuseStep 3010475 = 4515713) B4515713
theorem B2006983 : Blo 2005435 2006983 := bstep (se 1 (by rfl) ⟨1505237, by rfl⟩ : syracuseStep 2006983 = 3010475) B3010475
theorem B2257861 : Blo 2005435 2257861 := bbase (se 4 (by rfl) ⟨211674, by rfl⟩ : syracuseStep 2257861 = 423349) (by norm_num)
theorem B3010481 : Blo 2005435 3010481 := bstep (se 2 (by rfl) ⟨1128930, by rfl⟩ : syracuseStep 3010481 = 2257861) B2257861
theorem B2006987 : Blo 2005435 2006987 := bstep (se 1 (by rfl) ⟨1505240, by rfl⟩ : syracuseStep 2006987 = 3010481) B3010481
theorem B3810149 : Blo 2005435 3810149 := bbase (se 4 (by rfl) ⟨357201, by rfl⟩ : syracuseStep 3810149 = 714403) (by norm_num)
theorem B2540099 : Blo 2005435 2540099 := bstep (se 1 (by rfl) ⟨1905074, by rfl⟩ : syracuseStep 2540099 = 3810149) B3810149
theorem B6773597 : Blo 2005435 6773597 := bstep (se 3 (by rfl) ⟨1270049, by rfl⟩ : syracuseStep 6773597 = 2540099) B2540099
theorem B4515731 : Blo 2005435 4515731 := bstep (se 1 (by rfl) ⟨3386798, by rfl⟩ : syracuseStep 4515731 = 6773597) B6773597
theorem B3010487 : Blo 2005435 3010487 := bstep (se 1 (by rfl) ⟨2257865, by rfl⟩ : syracuseStep 3010487 = 4515731) B4515731
theorem B2006991 : Blo 2005435 2006991 := bstep (se 1 (by rfl) ⟨1505243, by rfl⟩ : syracuseStep 2006991 = 3010487) B3010487
theorem B3010493 : Blo 2005435 3010493 := bbase (se 3 (by rfl) ⟨564467, by rfl⟩ : syracuseStep 3010493 = 1128935) (by norm_num)
theorem B2006995 : Blo 2005435 2006995 := bstep (se 1 (by rfl) ⟨1505246, by rfl⟩ : syracuseStep 2006995 = 3010493) B3010493
theorem B4515749 : Blo 2005435 4515749 := bbase (se 4 (by rfl) ⟨423351, by rfl⟩ : syracuseStep 4515749 = 846703) (by norm_num)
theorem B3010499 : Blo 2005435 3010499 := bstep (se 1 (by rfl) ⟨2257874, by rfl⟩ : syracuseStep 3010499 = 4515749) B4515749
theorem B2006999 : Blo 2005435 2006999 := bstep (se 1 (by rfl) ⟨1505249, by rfl⟩ : syracuseStep 2006999 = 3010499) B3010499
theorem B5080229 : Blo 2005435 5080229 := bbase (se 4 (by rfl) ⟨476271, by rfl⟩ : syracuseStep 5080229 = 952543) (by norm_num)
theorem B3386819 : Blo 2005435 3386819 := bstep (se 1 (by rfl) ⟨2540114, by rfl⟩ : syracuseStep 3386819 = 5080229) B5080229
theorem B2257879 : Blo 2005435 2257879 := bstep (se 1 (by rfl) ⟨1693409, by rfl⟩ : syracuseStep 2257879 = 3386819) B3386819
theorem B3010505 : Blo 2005435 3010505 := bstep (se 2 (by rfl) ⟨1128939, by rfl⟩ : syracuseStep 3010505 = 2257879) B2257879
theorem B2007003 : Blo 2005435 2007003 := bstep (se 1 (by rfl) ⟨1505252, by rfl⟩ : syracuseStep 2007003 = 3010505) B3010505
theorem B5715269 : Blo 2005435 5715269 := bbase (se 4 (by rfl) ⟨535806, by rfl⟩ : syracuseStep 5715269 = 1071613) (by norm_num)
theorem B3810179 : Blo 2005435 3810179 := bstep (se 1 (by rfl) ⟨2857634, by rfl⟩ : syracuseStep 3810179 = 5715269) B5715269
theorem B10160477 : Blo 2005435 10160477 := bstep (se 3 (by rfl) ⟨1905089, by rfl⟩ : syracuseStep 10160477 = 3810179) B3810179
theorem B6773651 : Blo 2005435 6773651 := bstep (se 1 (by rfl) ⟨5080238, by rfl⟩ : syracuseStep 6773651 = 10160477) B10160477
theorem B4515767 : Blo 2005435 4515767 := bstep (se 1 (by rfl) ⟨3386825, by rfl⟩ : syracuseStep 4515767 = 6773651) B6773651
theorem B3010511 : Blo 2005435 3010511 := bstep (se 1 (by rfl) ⟨2257883, by rfl⟩ : syracuseStep 3010511 = 4515767) B4515767
theorem B2007007 : Blo 2005435 2007007 := bstep (se 1 (by rfl) ⟨1505255, by rfl⟩ : syracuseStep 2007007 = 3010511) B3010511
theorem B3010517 : Blo 2005435 3010517 := bbase (se 7 (by rfl) ⟨35279, by rfl⟩ : syracuseStep 3010517 = 70559) (by norm_num)
theorem B2007011 : Blo 2005435 2007011 := bstep (se 1 (by rfl) ⟨1505258, by rfl⟩ : syracuseStep 2007011 = 3010517) B3010517
theorem B7620389 : Blo 2005435 7620389 := bbase (se 4 (by rfl) ⟨714411, by rfl⟩ : syracuseStep 7620389 = 1428823) (by norm_num)
theorem B5080259 : Blo 2005435 5080259 := bstep (se 1 (by rfl) ⟨3810194, by rfl⟩ : syracuseStep 5080259 = 7620389) B7620389
theorem B3386839 : Blo 2005435 3386839 := bstep (se 1 (by rfl) ⟨2540129, by rfl⟩ : syracuseStep 3386839 = 5080259) B5080259
theorem B4515785 : Blo 2005435 4515785 := bstep (se 2 (by rfl) ⟨1693419, by rfl⟩ : syracuseStep 4515785 = 3386839) B3386839
theorem B3010523 : Blo 2005435 3010523 := bstep (se 1 (by rfl) ⟨2257892, by rfl⟩ : syracuseStep 3010523 = 4515785) B4515785
theorem B2007015 : Blo 2005435 2007015 := bstep (se 1 (by rfl) ⟨1505261, by rfl⟩ : syracuseStep 2007015 = 3010523) B3010523
theorem B2257897 : Blo 2005435 2257897 := bbase (se 2 (by rfl) ⟨846711, by rfl⟩ : syracuseStep 2257897 = 1693423) (by norm_num)
theorem B3010529 : Blo 2005435 3010529 := bstep (se 2 (by rfl) ⟨1128948, by rfl⟩ : syracuseStep 3010529 = 2257897) B2257897
theorem B2007019 : Blo 2005435 2007019 := bstep (se 1 (by rfl) ⟨1505264, by rfl⟩ : syracuseStep 2007019 = 3010529) B3010529
theorem B2411149 : Blo 2005435 2411149 := bbase (se 3 (by rfl) ⟨452090, by rfl⟩ : syracuseStep 2411149 = 904181) (by norm_num)
theorem B3214865 : Blo 2005435 3214865 := bstep (se 2 (by rfl) ⟨1205574, by rfl⟩ : syracuseStep 3214865 = 2411149) B2411149
theorem B2143243 : Blo 2005435 2143243 := bstep (se 1 (by rfl) ⟨1607432, by rfl⟩ : syracuseStep 2143243 = 3214865) B3214865
theorem B11430629 : Blo 2005435 11430629 := bstep (se 4 (by rfl) ⟨1071621, by rfl⟩ : syracuseStep 11430629 = 2143243) B2143243
theorem B7620419 : Blo 2005435 7620419 := bstep (se 1 (by rfl) ⟨5715314, by rfl⟩ : syracuseStep 7620419 = 11430629) B11430629
theorem B5080279 : Blo 2005435 5080279 := bstep (se 1 (by rfl) ⟨3810209, by rfl⟩ : syracuseStep 5080279 = 7620419) B7620419
theorem B6773705 : Blo 2005435 6773705 := bstep (se 2 (by rfl) ⟨2540139, by rfl⟩ : syracuseStep 6773705 = 5080279) B5080279
theorem B4515803 : Blo 2005435 4515803 := bstep (se 1 (by rfl) ⟨3386852, by rfl⟩ : syracuseStep 4515803 = 6773705) B6773705
theorem B3010535 : Blo 2005435 3010535 := bstep (se 1 (by rfl) ⟨2257901, by rfl⟩ : syracuseStep 3010535 = 4515803) B4515803
theorem B2007023 : Blo 2005435 2007023 := bstep (se 1 (by rfl) ⟨1505267, by rfl⟩ : syracuseStep 2007023 = 3010535) B3010535
theorem B3010541 : Blo 2005435 3010541 := bbase (se 3 (by rfl) ⟨564476, by rfl⟩ : syracuseStep 3010541 = 1128953) (by norm_num)
theorem B2007027 : Blo 2005435 2007027 := bstep (se 1 (by rfl) ⟨1505270, by rfl⟩ : syracuseStep 2007027 = 3010541) B3010541
theorem B4515821 : Blo 2005435 4515821 := bbase (se 3 (by rfl) ⟨846716, by rfl⟩ : syracuseStep 4515821 = 1693433) (by norm_num)
theorem B3010547 : Blo 2005435 3010547 := bstep (se 1 (by rfl) ⟨2257910, by rfl⟩ : syracuseStep 3010547 = 4515821) B4515821
theorem B2007031 : Blo 2005435 2007031 := bstep (se 1 (by rfl) ⟨1505273, by rfl⟩ : syracuseStep 2007031 = 3010547) B3010547
theorem B3214885 : Blo 2005435 3214885 := bbase (se 4 (by rfl) ⟨301395, by rfl⟩ : syracuseStep 3214885 = 602791) (by norm_num)
theorem B4286513 : Blo 2005435 4286513 := bstep (se 2 (by rfl) ⟨1607442, by rfl⟩ : syracuseStep 4286513 = 3214885) B3214885
theorem B2857675 : Blo 2005435 2857675 := bstep (se 1 (by rfl) ⟨2143256, by rfl⟩ : syracuseStep 2857675 = 4286513) B4286513
theorem B3810233 : Blo 2005435 3810233 := bstep (se 2 (by rfl) ⟨1428837, by rfl⟩ : syracuseStep 3810233 = 2857675) B2857675
theorem B2540155 : Blo 2005435 2540155 := bstep (se 1 (by rfl) ⟨1905116, by rfl⟩ : syracuseStep 2540155 = 3810233) B3810233
theorem B3386873 : Blo 2005435 3386873 := bstep (se 2 (by rfl) ⟨1270077, by rfl⟩ : syracuseStep 3386873 = 2540155) B2540155
theorem B2257915 : Blo 2005435 2257915 := bstep (se 1 (by rfl) ⟨1693436, by rfl⟩ : syracuseStep 2257915 = 3386873) B3386873
theorem B3010553 : Blo 2005435 3010553 := bstep (se 2 (by rfl) ⟨1128957, by rfl⟩ : syracuseStep 3010553 = 2257915) B2257915
theorem B2007035 : Blo 2005435 2007035 := bstep (se 1 (by rfl) ⟨1505276, by rfl⟩ : syracuseStep 2007035 = 3010553) B3010553
theorem B7936661 : Blo 2005435 7936661 := bbase (se 6 (by rfl) ⟨186015, by rfl⟩ : syracuseStep 7936661 = 372031) (by norm_num)
theorem B21164429 : Blo 2005435 21164429 := bstep (se 3 (by rfl) ⟨3968330, by rfl⟩ : syracuseStep 21164429 = 7936661) B7936661
theorem B56438477 : Blo 2005435 56438477 := bstep (se 3 (by rfl) ⟨10582214, by rfl⟩ : syracuseStep 56438477 = 21164429) B21164429
theorem B37625651 : Blo 2005435 37625651 := bstep (se 1 (by rfl) ⟨28219238, by rfl⟩ : syracuseStep 37625651 = 56438477) B56438477
theorem B25083767 : Blo 2005435 25083767 := bstep (se 1 (by rfl) ⟨18812825, by rfl⟩ : syracuseStep 25083767 = 37625651) B37625651
theorem B66890045 : Blo 2005435 66890045 := bstep (se 3 (by rfl) ⟨12541883, by rfl⟩ : syracuseStep 66890045 = 25083767) B25083767
theorem B44593363 : Blo 2005435 44593363 := bstep (se 1 (by rfl) ⟨33445022, by rfl⟩ : syracuseStep 44593363 = 66890045) B66890045
theorem B59457817 : Blo 2005435 59457817 := bstep (se 2 (by rfl) ⟨22296681, by rfl⟩ : syracuseStep 59457817 = 44593363) B44593363
theorem B317108357 : Blo 2005435 317108357 := bstep (se 4 (by rfl) ⟨29728908, by rfl⟩ : syracuseStep 317108357 = 59457817) B59457817
theorem B211405571 : Blo 2005435 211405571 := bstep (se 1 (by rfl) ⟨158554178, by rfl⟩ : syracuseStep 211405571 = 317108357) B317108357
theorem B140937047 : Blo 2005435 140937047 := bstep (se 1 (by rfl) ⟨105702785, by rfl⟩ : syracuseStep 140937047 = 211405571) B211405571
theorem B93958031 : Blo 2005435 93958031 := bstep (se 1 (by rfl) ⟨70468523, by rfl⟩ : syracuseStep 93958031 = 140937047) B140937047
theorem B62638687 : Blo 2005435 62638687 := bstep (se 1 (by rfl) ⟨46979015, by rfl⟩ : syracuseStep 62638687 = 93958031) B93958031
theorem B334072997 : Blo 2005435 334072997 := bstep (se 4 (by rfl) ⟨31319343, by rfl⟩ : syracuseStep 334072997 = 62638687) B62638687
theorem B222715331 : Blo 2005435 222715331 := bstep (se 1 (by rfl) ⟨167036498, by rfl⟩ : syracuseStep 222715331 = 334072997) B334072997
theorem B148476887 : Blo 2005435 148476887 := bstep (se 1 (by rfl) ⟨111357665, by rfl⟩ : syracuseStep 148476887 = 222715331) B222715331
theorem B98984591 : Blo 2005435 98984591 := bstep (se 1 (by rfl) ⟨74238443, by rfl⟩ : syracuseStep 98984591 = 148476887) B148476887
theorem B65989727 : Blo 2005435 65989727 := bstep (se 1 (by rfl) ⟨49492295, by rfl⟩ : syracuseStep 65989727 = 98984591) B98984591
theorem B43993151 : Blo 2005435 43993151 := bstep (se 1 (by rfl) ⟨32994863, by rfl⟩ : syracuseStep 43993151 = 65989727) B65989727
theorem B29328767 : Blo 2005435 29328767 := bstep (se 1 (by rfl) ⟨21996575, by rfl⟩ : syracuseStep 29328767 = 43993151) B43993151
theorem B19552511 : Blo 2005435 19552511 := bstep (se 1 (by rfl) ⟨14664383, by rfl⟩ : syracuseStep 19552511 = 29328767) B29328767
theorem B13035007 : Blo 2005435 13035007 := bstep (se 1 (by rfl) ⟨9776255, by rfl⟩ : syracuseStep 13035007 = 19552511) B19552511
theorem B17380009 : Blo 2005435 17380009 := bstep (se 2 (by rfl) ⟨6517503, by rfl⟩ : syracuseStep 17380009 = 13035007) B13035007
theorem B23173345 : Blo 2005435 23173345 := bstep (se 2 (by rfl) ⟨8690004, by rfl⟩ : syracuseStep 23173345 = 17380009) B17380009
theorem B30897793 : Blo 2005435 30897793 := bstep (se 2 (by rfl) ⟨11586672, by rfl⟩ : syracuseStep 30897793 = 23173345) B23173345
theorem B164788229 : Blo 2005435 164788229 := bstep (se 4 (by rfl) ⟨15448896, by rfl⟩ : syracuseStep 164788229 = 30897793) B30897793
theorem B439435277 : Blo 2005435 439435277 := bstep (se 3 (by rfl) ⟨82394114, by rfl⟩ : syracuseStep 439435277 = 164788229) B164788229
theorem B292956851 : Blo 2005435 292956851 := bstep (se 1 (by rfl) ⟨219717638, by rfl⟩ : syracuseStep 292956851 = 439435277) B439435277
theorem B195304567 : Blo 2005435 195304567 := bstep (se 1 (by rfl) ⟨146478425, by rfl⟩ : syracuseStep 195304567 = 292956851) B292956851
theorem B260406089 : Blo 2005435 260406089 := bstep (se 2 (by rfl) ⟨97652283, by rfl⟩ : syracuseStep 260406089 = 195304567) B195304567
theorem B173604059 : Blo 2005435 173604059 := bstep (se 1 (by rfl) ⟨130203044, by rfl⟩ : syracuseStep 173604059 = 260406089) B260406089
theorem B115736039 : Blo 2005435 115736039 := bstep (se 1 (by rfl) ⟨86802029, by rfl⟩ : syracuseStep 115736039 = 173604059) B173604059
theorem B77157359 : Blo 2005435 77157359 := bstep (se 1 (by rfl) ⟨57868019, by rfl⟩ : syracuseStep 77157359 = 115736039) B115736039
theorem B51438239 : Blo 2005435 51438239 := bstep (se 1 (by rfl) ⟨38578679, by rfl⟩ : syracuseStep 51438239 = 77157359) B77157359
theorem B34292159 : Blo 2005435 34292159 := bstep (se 1 (by rfl) ⟨25719119, by rfl⟩ : syracuseStep 34292159 = 51438239) B51438239
theorem B22861439 : Blo 2005435 22861439 := bstep (se 1 (by rfl) ⟨17146079, by rfl⟩ : syracuseStep 22861439 = 34292159) B34292159
theorem B15240959 : Blo 2005435 15240959 := bstep (se 1 (by rfl) ⟨11430719, by rfl⟩ : syracuseStep 15240959 = 22861439) B22861439
theorem B10160639 : Blo 2005435 10160639 := bstep (se 1 (by rfl) ⟨7620479, by rfl⟩ : syracuseStep 10160639 = 15240959) B15240959
theorem B6773759 : Blo 2005435 6773759 := bstep (se 1 (by rfl) ⟨5080319, by rfl⟩ : syracuseStep 6773759 = 10160639) B10160639
theorem B4515839 : Blo 2005435 4515839 := bstep (se 1 (by rfl) ⟨3386879, by rfl⟩ : syracuseStep 4515839 = 6773759) B6773759
theorem B3010559 : Blo 2005435 3010559 := bstep (se 1 (by rfl) ⟨2257919, by rfl⟩ : syracuseStep 3010559 = 4515839) B4515839
theorem B2007039 : Blo 2005435 2007039 := bstep (se 1 (by rfl) ⟨1505279, by rfl⟩ : syracuseStep 2007039 = 3010559) B3010559
theorem B3010565 : Blo 2005435 3010565 := bbase (se 4 (by rfl) ⟨282240, by rfl⟩ : syracuseStep 3010565 = 564481) (by norm_num)
theorem B2007043 : Blo 2005435 2007043 := bstep (se 1 (by rfl) ⟨1505282, by rfl⟩ : syracuseStep 2007043 = 3010565) B3010565
theorem B3386893 : Blo 2005435 3386893 := bbase (se 3 (by rfl) ⟨635042, by rfl⟩ : syracuseStep 3386893 = 1270085) (by norm_num)
theorem B4515857 : Blo 2005435 4515857 := bstep (se 2 (by rfl) ⟨1693446, by rfl⟩ : syracuseStep 4515857 = 3386893) B3386893
theorem B3010571 : Blo 2005435 3010571 := bstep (se 1 (by rfl) ⟨2257928, by rfl⟩ : syracuseStep 3010571 = 4515857) B4515857
theorem B2007047 : Blo 2005435 2007047 := bstep (se 1 (by rfl) ⟨1505285, by rfl⟩ : syracuseStep 2007047 = 3010571) B3010571
theorem B2257933 : Blo 2005435 2257933 := bbase (se 3 (by rfl) ⟨423362, by rfl⟩ : syracuseStep 2257933 = 846725) (by norm_num)
theorem B3010577 : Blo 2005435 3010577 := bstep (se 2 (by rfl) ⟨1128966, by rfl⟩ : syracuseStep 3010577 = 2257933) B2257933
theorem B2007051 : Blo 2005435 2007051 := bstep (se 1 (by rfl) ⟨1505288, by rfl⟩ : syracuseStep 2007051 = 3010577) B3010577
theorem B6773813 : Blo 2005435 6773813 := bbase (se 5 (by rfl) ⟨317522, by rfl⟩ : syracuseStep 6773813 = 635045) (by norm_num)
theorem B4515875 : Blo 2005435 4515875 := bstep (se 1 (by rfl) ⟨3386906, by rfl⟩ : syracuseStep 4515875 = 6773813) B6773813
theorem B3010583 : Blo 2005435 3010583 := bstep (se 1 (by rfl) ⟨2257937, by rfl⟩ : syracuseStep 3010583 = 4515875) B4515875
theorem B2007055 : Blo 2005435 2007055 := bstep (se 1 (by rfl) ⟨1505291, by rfl⟩ : syracuseStep 2007055 = 3010583) B3010583
theorem B3010589 : Blo 2005435 3010589 := bbase (se 3 (by rfl) ⟨564485, by rfl⟩ : syracuseStep 3010589 = 1128971) (by norm_num)
theorem B2007059 : Blo 2005435 2007059 := bstep (se 1 (by rfl) ⟨1505294, by rfl⟩ : syracuseStep 2007059 = 3010589) B3010589
theorem B4515893 : Blo 2005435 4515893 := bbase (se 5 (by rfl) ⟨211682, by rfl⟩ : syracuseStep 4515893 = 423365) (by norm_num)
theorem B3010595 : Blo 2005435 3010595 := bstep (se 1 (by rfl) ⟨2257946, by rfl⟩ : syracuseStep 3010595 = 4515893) B4515893
theorem B2007063 : Blo 2005435 2007063 := bstep (se 1 (by rfl) ⟨1505297, by rfl⟩ : syracuseStep 2007063 = 3010595) B3010595
theorem B10299413 : Blo 2005435 10299413 := bbase (se 6 (by rfl) ⟨241392, by rfl⟩ : syracuseStep 10299413 = 482785) (by norm_num)
theorem B6866275 : Blo 2005435 6866275 := bstep (se 1 (by rfl) ⟨5149706, by rfl⟩ : syracuseStep 6866275 = 10299413) B10299413
theorem B9155033 : Blo 2005435 9155033 := bstep (se 2 (by rfl) ⟨3433137, by rfl⟩ : syracuseStep 9155033 = 6866275) B6866275
theorem B6103355 : Blo 2005435 6103355 := bstep (se 1 (by rfl) ⟨4577516, by rfl⟩ : syracuseStep 6103355 = 9155033) B9155033
theorem B16275613 : Blo 2005435 16275613 := bstep (se 3 (by rfl) ⟨3051677, by rfl⟩ : syracuseStep 16275613 = 6103355) B6103355
theorem B21700817 : Blo 2005435 21700817 := bstep (se 2 (by rfl) ⟨8137806, by rfl⟩ : syracuseStep 21700817 = 16275613) B16275613
theorem B14467211 : Blo 2005435 14467211 := bstep (se 1 (by rfl) ⟨10850408, by rfl⟩ : syracuseStep 14467211 = 21700817) B21700817
theorem B9644807 : Blo 2005435 9644807 := bstep (se 1 (by rfl) ⟨7233605, by rfl⟩ : syracuseStep 9644807 = 14467211) B14467211
theorem B6429871 : Blo 2005435 6429871 := bstep (se 1 (by rfl) ⟨4822403, by rfl⟩ : syracuseStep 6429871 = 9644807) B9644807
theorem B8573161 : Blo 2005435 8573161 := bstep (se 2 (by rfl) ⟨3214935, by rfl⟩ : syracuseStep 8573161 = 6429871) B6429871
theorem B11430881 : Blo 2005435 11430881 := bstep (se 2 (by rfl) ⟨4286580, by rfl⟩ : syracuseStep 11430881 = 8573161) B8573161
theorem B7620587 : Blo 2005435 7620587 := bstep (se 1 (by rfl) ⟨5715440, by rfl⟩ : syracuseStep 7620587 = 11430881) B11430881
theorem B5080391 : Blo 2005435 5080391 := bstep (se 1 (by rfl) ⟨3810293, by rfl⟩ : syracuseStep 5080391 = 7620587) B7620587
theorem B3386927 : Blo 2005435 3386927 := bstep (se 1 (by rfl) ⟨2540195, by rfl⟩ : syracuseStep 3386927 = 5080391) B5080391
theorem B2257951 : Blo 2005435 2257951 := bstep (se 1 (by rfl) ⟨1693463, by rfl⟩ : syracuseStep 2257951 = 3386927) B3386927
theorem B3010601 : Blo 2005435 3010601 := bstep (se 2 (by rfl) ⟨1128975, by rfl⟩ : syracuseStep 3010601 = 2257951) B2257951
theorem B2007067 : Blo 2005435 2007067 := bstep (se 1 (by rfl) ⟨1505300, by rfl⟩ : syracuseStep 2007067 = 3010601) B3010601
theorem B2936237 : Blo 2005435 2936237 := bbase (se 3 (by rfl) ⟨550544, by rfl⟩ : syracuseStep 2936237 = 1101089) (by norm_num)
theorem B7829965 : Blo 2005435 7829965 := bstep (se 3 (by rfl) ⟨1468118, by rfl⟩ : syracuseStep 7829965 = 2936237) B2936237
theorem B41759813 : Blo 2005435 41759813 := bstep (se 4 (by rfl) ⟨3914982, by rfl⟩ : syracuseStep 41759813 = 7829965) B7829965
theorem B27839875 : Blo 2005435 27839875 := bstep (se 1 (by rfl) ⟨20879906, by rfl⟩ : syracuseStep 27839875 = 41759813) B41759813
theorem B37119833 : Blo 2005435 37119833 := bstep (se 2 (by rfl) ⟨13919937, by rfl⟩ : syracuseStep 37119833 = 27839875) B27839875
theorem B24746555 : Blo 2005435 24746555 := bstep (se 1 (by rfl) ⟨18559916, by rfl⟩ : syracuseStep 24746555 = 37119833) B37119833
theorem B16497703 : Blo 2005435 16497703 := bstep (se 1 (by rfl) ⟨12373277, by rfl⟩ : syracuseStep 16497703 = 24746555) B24746555
theorem B21996937 : Blo 2005435 21996937 := bstep (se 2 (by rfl) ⟨8248851, by rfl⟩ : syracuseStep 21996937 = 16497703) B16497703
theorem B29329249 : Blo 2005435 29329249 := bstep (se 2 (by rfl) ⟨10998468, by rfl⟩ : syracuseStep 29329249 = 21996937) B21996937
theorem B39105665 : Blo 2005435 39105665 := bstep (se 2 (by rfl) ⟨14664624, by rfl⟩ : syracuseStep 39105665 = 29329249) B29329249
theorem B26070443 : Blo 2005435 26070443 := bstep (se 1 (by rfl) ⟨19552832, by rfl⟩ : syracuseStep 26070443 = 39105665) B39105665
theorem B17380295 : Blo 2005435 17380295 := bstep (se 1 (by rfl) ⟨13035221, by rfl⟩ : syracuseStep 17380295 = 26070443) B26070443
theorem B11586863 : Blo 2005435 11586863 := bstep (se 1 (by rfl) ⟨8690147, by rfl⟩ : syracuseStep 11586863 = 17380295) B17380295
theorem B7724575 : Blo 2005435 7724575 := bstep (se 1 (by rfl) ⟨5793431, by rfl⟩ : syracuseStep 7724575 = 11586863) B11586863
theorem B10299433 : Blo 2005435 10299433 := bstep (se 2 (by rfl) ⟨3862287, by rfl⟩ : syracuseStep 10299433 = 7724575) B7724575
theorem B13732577 : Blo 2005435 13732577 := bstep (se 2 (by rfl) ⟨5149716, by rfl⟩ : syracuseStep 13732577 = 10299433) B10299433
theorem B9155051 : Blo 2005435 9155051 := bstep (se 1 (by rfl) ⟨6866288, by rfl⟩ : syracuseStep 9155051 = 13732577) B13732577
theorem B6103367 : Blo 2005435 6103367 := bstep (se 1 (by rfl) ⟨4577525, by rfl⟩ : syracuseStep 6103367 = 9155051) B9155051
theorem B4068911 : Blo 2005435 4068911 := bstep (se 1 (by rfl) ⟨3051683, by rfl⟩ : syracuseStep 4068911 = 6103367) B6103367
theorem B10850429 : Blo 2005435 10850429 := bstep (se 3 (by rfl) ⟨2034455, by rfl⟩ : syracuseStep 10850429 = 4068911) B4068911
theorem B7233619 : Blo 2005435 7233619 := bstep (se 1 (by rfl) ⟨5425214, by rfl⟩ : syracuseStep 7233619 = 10850429) B10850429
theorem B9644825 : Blo 2005435 9644825 := bstep (se 2 (by rfl) ⟨3616809, by rfl⟩ : syracuseStep 9644825 = 7233619) B7233619
theorem B6429883 : Blo 2005435 6429883 := bstep (se 1 (by rfl) ⟨4822412, by rfl⟩ : syracuseStep 6429883 = 9644825) B9644825
theorem B8573177 : Blo 2005435 8573177 := bstep (se 2 (by rfl) ⟨3214941, by rfl⟩ : syracuseStep 8573177 = 6429883) B6429883
theorem B5715451 : Blo 2005435 5715451 := bstep (se 1 (by rfl) ⟨4286588, by rfl⟩ : syracuseStep 5715451 = 8573177) B8573177
theorem B7620601 : Blo 2005435 7620601 := bstep (se 2 (by rfl) ⟨2857725, by rfl⟩ : syracuseStep 7620601 = 5715451) B5715451
theorem B10160801 : Blo 2005435 10160801 := bstep (se 2 (by rfl) ⟨3810300, by rfl⟩ : syracuseStep 10160801 = 7620601) B7620601
theorem B6773867 : Blo 2005435 6773867 := bstep (se 1 (by rfl) ⟨5080400, by rfl⟩ : syracuseStep 6773867 = 10160801) B10160801
theorem B4515911 : Blo 2005435 4515911 := bstep (se 1 (by rfl) ⟨3386933, by rfl⟩ : syracuseStep 4515911 = 6773867) B6773867
theorem B3010607 : Blo 2005435 3010607 := bstep (se 1 (by rfl) ⟨2257955, by rfl⟩ : syracuseStep 3010607 = 4515911) B4515911
theorem B2007071 : Blo 2005435 2007071 := bstep (se 1 (by rfl) ⟨1505303, by rfl⟩ : syracuseStep 2007071 = 3010607) B3010607
theorem B3010613 : Blo 2005435 3010613 := bbase (se 5 (by rfl) ⟨141122, by rfl⟩ : syracuseStep 3010613 = 282245) (by norm_num)
theorem B2007075 : Blo 2005435 2007075 := bstep (se 1 (by rfl) ⟨1505306, by rfl⟩ : syracuseStep 2007075 = 3010613) B3010613
theorem B5080421 : Blo 2005435 5080421 := bbase (se 4 (by rfl) ⟨476289, by rfl⟩ : syracuseStep 5080421 = 952579) (by norm_num)
theorem B3386947 : Blo 2005435 3386947 := bstep (se 1 (by rfl) ⟨2540210, by rfl⟩ : syracuseStep 3386947 = 5080421) B5080421
theorem B4515929 : Blo 2005435 4515929 := bstep (se 2 (by rfl) ⟨1693473, by rfl⟩ : syracuseStep 4515929 = 3386947) B3386947
theorem B3010619 : Blo 2005435 3010619 := bstep (se 1 (by rfl) ⟨2257964, by rfl⟩ : syracuseStep 3010619 = 4515929) B4515929
theorem B2007079 : Blo 2005435 2007079 := bstep (se 1 (by rfl) ⟨1505309, by rfl⟩ : syracuseStep 2007079 = 3010619) B3010619
theorem B2257969 : Blo 2005435 2257969 := bbase (se 2 (by rfl) ⟨846738, by rfl⟩ : syracuseStep 2257969 = 1693477) (by norm_num)
theorem B3010625 : Blo 2005435 3010625 := bstep (se 2 (by rfl) ⟨1128984, by rfl⟩ : syracuseStep 3010625 = 2257969) B2257969
theorem B2007083 : Blo 2005435 2007083 := bstep (se 1 (by rfl) ⟨1505312, by rfl⟩ : syracuseStep 2007083 = 3010625) B3010625
theorem B2062229 : Blo 2005435 2062229 := bbase (se 6 (by rfl) ⟨48333, by rfl⟩ : syracuseStep 2062229 = 96667) (by norm_num)
theorem B5499277 : Blo 2005435 5499277 := bstep (se 3 (by rfl) ⟨1031114, by rfl⟩ : syracuseStep 5499277 = 2062229) B2062229
theorem B117317909 : Blo 2005435 117317909 := bstep (se 6 (by rfl) ⟨2749638, by rfl⟩ : syracuseStep 117317909 = 5499277) B5499277
theorem B78211939 : Blo 2005435 78211939 := bstep (se 1 (by rfl) ⟨58658954, by rfl⟩ : syracuseStep 78211939 = 117317909) B117317909
theorem B104282585 : Blo 2005435 104282585 := bstep (se 2 (by rfl) ⟨39105969, by rfl⟩ : syracuseStep 104282585 = 78211939) B78211939
theorem B69521723 : Blo 2005435 69521723 := bstep (se 1 (by rfl) ⟨52141292, by rfl⟩ : syracuseStep 69521723 = 104282585) B104282585
theorem B46347815 : Blo 2005435 46347815 := bstep (se 1 (by rfl) ⟨34760861, by rfl⟩ : syracuseStep 46347815 = 69521723) B69521723
theorem B123594173 : Blo 2005435 123594173 := bstep (se 3 (by rfl) ⟨23173907, by rfl⟩ : syracuseStep 123594173 = 46347815) B46347815
theorem B82396115 : Blo 2005435 82396115 := bstep (se 1 (by rfl) ⟨61797086, by rfl⟩ : syracuseStep 82396115 = 123594173) B123594173
theorem B54930743 : Blo 2005435 54930743 := bstep (se 1 (by rfl) ⟨41198057, by rfl⟩ : syracuseStep 54930743 = 82396115) B82396115
theorem B36620495 : Blo 2005435 36620495 := bstep (se 1 (by rfl) ⟨27465371, by rfl⟩ : syracuseStep 36620495 = 54930743) B54930743
theorem B24413663 : Blo 2005435 24413663 := bstep (se 1 (by rfl) ⟨18310247, by rfl⟩ : syracuseStep 24413663 = 36620495) B36620495
theorem B16275775 : Blo 2005435 16275775 := bstep (se 1 (by rfl) ⟨12206831, by rfl⟩ : syracuseStep 16275775 = 24413663) B24413663
theorem B21701033 : Blo 2005435 21701033 := bstep (se 2 (by rfl) ⟨8137887, by rfl⟩ : syracuseStep 21701033 = 16275775) B16275775
theorem B14467355 : Blo 2005435 14467355 := bstep (se 1 (by rfl) ⟨10850516, by rfl⟩ : syracuseStep 14467355 = 21701033) B21701033
theorem B9644903 : Blo 2005435 9644903 := bstep (se 1 (by rfl) ⟨7233677, by rfl⟩ : syracuseStep 9644903 = 14467355) B14467355
theorem B6429935 : Blo 2005435 6429935 := bstep (se 1 (by rfl) ⟨4822451, by rfl⟩ : syracuseStep 6429935 = 9644903) B9644903
theorem B4286623 : Blo 2005435 4286623 := bstep (se 1 (by rfl) ⟨3214967, by rfl⟩ : syracuseStep 4286623 = 6429935) B6429935
theorem B5715497 : Blo 2005435 5715497 := bstep (se 2 (by rfl) ⟨2143311, by rfl⟩ : syracuseStep 5715497 = 4286623) B4286623
theorem B3810331 : Blo 2005435 3810331 := bstep (se 1 (by rfl) ⟨2857748, by rfl⟩ : syracuseStep 3810331 = 5715497) B5715497
theorem B5080441 : Blo 2005435 5080441 := bstep (se 2 (by rfl) ⟨1905165, by rfl⟩ : syracuseStep 5080441 = 3810331) B3810331
theorem B6773921 : Blo 2005435 6773921 := bstep (se 2 (by rfl) ⟨2540220, by rfl⟩ : syracuseStep 6773921 = 5080441) B5080441
theorem B4515947 : Blo 2005435 4515947 := bstep (se 1 (by rfl) ⟨3386960, by rfl⟩ : syracuseStep 4515947 = 6773921) B6773921
theorem B3010631 : Blo 2005435 3010631 := bstep (se 1 (by rfl) ⟨2257973, by rfl⟩ : syracuseStep 3010631 = 4515947) B4515947
theorem B2007087 : Blo 2005435 2007087 := bstep (se 1 (by rfl) ⟨1505315, by rfl⟩ : syracuseStep 2007087 = 3010631) B3010631
theorem B3010637 : Blo 2005435 3010637 := bbase (se 3 (by rfl) ⟨564494, by rfl⟩ : syracuseStep 3010637 = 1128989) (by norm_num)
theorem B2007091 : Blo 2005435 2007091 := bstep (se 1 (by rfl) ⟨1505318, by rfl⟩ : syracuseStep 2007091 = 3010637) B3010637
theorem B4515965 : Blo 2005435 4515965 := bbase (se 3 (by rfl) ⟨846743, by rfl⟩ : syracuseStep 4515965 = 1693487) (by norm_num)
theorem B3010643 : Blo 2005435 3010643 := bstep (se 1 (by rfl) ⟨2257982, by rfl⟩ : syracuseStep 3010643 = 4515965) B4515965
theorem B2007095 : Blo 2005435 2007095 := bstep (se 1 (by rfl) ⟨1505321, by rfl⟩ : syracuseStep 2007095 = 3010643) B3010643
theorem B3386981 : Blo 2005435 3386981 := bbase (se 4 (by rfl) ⟨317529, by rfl⟩ : syracuseStep 3386981 = 635059) (by norm_num)
theorem B2257987 : Blo 2005435 2257987 := bstep (se 1 (by rfl) ⟨1693490, by rfl⟩ : syracuseStep 2257987 = 3386981) B3386981
theorem B3010649 : Blo 2005435 3010649 := bstep (se 2 (by rfl) ⟨1128993, by rfl⟩ : syracuseStep 3010649 = 2257987) B2257987
theorem B2007099 : Blo 2005435 2007099 := bstep (se 1 (by rfl) ⟨1505324, by rfl⟩ : syracuseStep 2007099 = 3010649) B3010649
theorem B2411245 : Blo 2005435 2411245 := bbase (se 3 (by rfl) ⟨452108, by rfl⟩ : syracuseStep 2411245 = 904217) (by norm_num)
theorem B3214993 : Blo 2005435 3214993 := bstep (se 2 (by rfl) ⟨1205622, by rfl⟩ : syracuseStep 3214993 = 2411245) B2411245
theorem B4286657 : Blo 2005435 4286657 := bstep (se 2 (by rfl) ⟨1607496, by rfl⟩ : syracuseStep 4286657 = 3214993) B3214993
theorem B2857771 : Blo 2005435 2857771 := bstep (se 1 (by rfl) ⟨2143328, by rfl⟩ : syracuseStep 2857771 = 4286657) B4286657
theorem B15241445 : Blo 2005435 15241445 := bstep (se 4 (by rfl) ⟨1428885, by rfl⟩ : syracuseStep 15241445 = 2857771) B2857771
theorem B10160963 : Blo 2005435 10160963 := bstep (se 1 (by rfl) ⟨7620722, by rfl⟩ : syracuseStep 10160963 = 15241445) B15241445
theorem B6773975 : Blo 2005435 6773975 := bstep (se 1 (by rfl) ⟨5080481, by rfl⟩ : syracuseStep 6773975 = 10160963) B10160963
theorem B4515983 : Blo 2005435 4515983 := bstep (se 1 (by rfl) ⟨3386987, by rfl⟩ : syracuseStep 4515983 = 6773975) B6773975
theorem B3010655 : Blo 2005435 3010655 := bstep (se 1 (by rfl) ⟨2257991, by rfl⟩ : syracuseStep 3010655 = 4515983) B4515983
theorem B2007103 : Blo 2005435 2007103 := bstep (se 1 (by rfl) ⟨1505327, by rfl⟩ : syracuseStep 2007103 = 3010655) B3010655
theorem B3010661 : Blo 2005435 3010661 := bbase (se 4 (by rfl) ⟨282249, by rfl⟩ : syracuseStep 3010661 = 564499) (by norm_num)
theorem B2007107 : Blo 2005435 2007107 := bstep (se 1 (by rfl) ⟨1505330, by rfl⟩ : syracuseStep 2007107 = 3010661) B3010661
theorem B2034497 : Blo 2005435 2034497 := bbase (se 2 (by rfl) ⟨762936, by rfl⟩ : syracuseStep 2034497 = 1525873) (by norm_num)
theorem B5425325 : Blo 2005435 5425325 := bstep (se 3 (by rfl) ⟨1017248, by rfl⟩ : syracuseStep 5425325 = 2034497) B2034497
theorem B3616883 : Blo 2005435 3616883 := bstep (se 1 (by rfl) ⟨2712662, by rfl⟩ : syracuseStep 3616883 = 5425325) B5425325
theorem B2411255 : Blo 2005435 2411255 := bstep (se 1 (by rfl) ⟨1808441, by rfl⟩ : syracuseStep 2411255 = 3616883) B3616883
theorem B6430013 : Blo 2005435 6430013 := bstep (se 3 (by rfl) ⟨1205627, by rfl⟩ : syracuseStep 6430013 = 2411255) B2411255
theorem B4286675 : Blo 2005435 4286675 := bstep (se 1 (by rfl) ⟨3215006, by rfl⟩ : syracuseStep 4286675 = 6430013) B6430013
theorem B2857783 : Blo 2005435 2857783 := bstep (se 1 (by rfl) ⟨2143337, by rfl⟩ : syracuseStep 2857783 = 4286675) B4286675
theorem B3810377 : Blo 2005435 3810377 := bstep (se 2 (by rfl) ⟨1428891, by rfl⟩ : syracuseStep 3810377 = 2857783) B2857783
theorem B2540251 : Blo 2005435 2540251 := bstep (se 1 (by rfl) ⟨1905188, by rfl⟩ : syracuseStep 2540251 = 3810377) B3810377
theorem B3387001 : Blo 2005435 3387001 := bstep (se 2 (by rfl) ⟨1270125, by rfl⟩ : syracuseStep 3387001 = 2540251) B2540251
theorem B4516001 : Blo 2005435 4516001 := bstep (se 2 (by rfl) ⟨1693500, by rfl⟩ : syracuseStep 4516001 = 3387001) B3387001
theorem B3010667 : Blo 2005435 3010667 := bstep (se 1 (by rfl) ⟨2258000, by rfl⟩ : syracuseStep 3010667 = 4516001) B4516001
theorem B2007111 : Blo 2005435 2007111 := bstep (se 1 (by rfl) ⟨1505333, by rfl⟩ : syracuseStep 2007111 = 3010667) B3010667
theorem B2258005 : Blo 2005435 2258005 := bbase (se 8 (by rfl) ⟨13230, by rfl⟩ : syracuseStep 2258005 = 26461) (by norm_num)
theorem B3010673 : Blo 2005435 3010673 := bstep (se 2 (by rfl) ⟨1129002, by rfl⟩ : syracuseStep 3010673 = 2258005) B2258005
theorem B2007115 : Blo 2005435 2007115 := bstep (se 1 (by rfl) ⟨1505336, by rfl⟩ : syracuseStep 2007115 = 3010673) B3010673
theorem B2540261 : Blo 2005435 2540261 := bbase (se 4 (by rfl) ⟨238149, by rfl⟩ : syracuseStep 2540261 = 476299) (by norm_num)
theorem B6774029 : Blo 2005435 6774029 := bstep (se 3 (by rfl) ⟨1270130, by rfl⟩ : syracuseStep 6774029 = 2540261) B2540261
theorem B4516019 : Blo 2005435 4516019 := bstep (se 1 (by rfl) ⟨3387014, by rfl⟩ : syracuseStep 4516019 = 6774029) B6774029
theorem B3010679 : Blo 2005435 3010679 := bstep (se 1 (by rfl) ⟨2258009, by rfl⟩ : syracuseStep 3010679 = 4516019) B4516019
theorem B2007119 : Blo 2005435 2007119 := bstep (se 1 (by rfl) ⟨1505339, by rfl⟩ : syracuseStep 2007119 = 3010679) B3010679
theorem B3010685 : Blo 2005435 3010685 := bbase (se 3 (by rfl) ⟨564503, by rfl⟩ : syracuseStep 3010685 = 1129007) (by norm_num)
theorem B2007123 : Blo 2005435 2007123 := bstep (se 1 (by rfl) ⟨1505342, by rfl⟩ : syracuseStep 2007123 = 3010685) B3010685
theorem B4516037 : Blo 2005435 4516037 := bbase (se 4 (by rfl) ⟨423378, by rfl⟩ : syracuseStep 4516037 = 846757) (by norm_num)
theorem B3010691 : Blo 2005435 3010691 := bstep (se 1 (by rfl) ⟨2258018, by rfl⟩ : syracuseStep 3010691 = 4516037) B4516037
theorem B2007127 : Blo 2005435 2007127 := bstep (se 1 (by rfl) ⟨1505345, by rfl⟩ : syracuseStep 2007127 = 3010691) B3010691
theorem B7332533 : Blo 2005435 7332533 := bbase (se 5 (by rfl) ⟨343712, by rfl⟩ : syracuseStep 7332533 = 687425) (by norm_num)
theorem B4888355 : Blo 2005435 4888355 := bstep (se 1 (by rfl) ⟨3666266, by rfl⟩ : syracuseStep 4888355 = 7332533) B7332533
theorem B52142453 : Blo 2005435 52142453 := bstep (se 5 (by rfl) ⟨2444177, by rfl⟩ : syracuseStep 52142453 = 4888355) B4888355
theorem B34761635 : Blo 2005435 34761635 := bstep (se 1 (by rfl) ⟨26071226, by rfl⟩ : syracuseStep 34761635 = 52142453) B52142453
theorem B23174423 : Blo 2005435 23174423 := bstep (se 1 (by rfl) ⟨17380817, by rfl⟩ : syracuseStep 23174423 = 34761635) B34761635
theorem B15449615 : Blo 2005435 15449615 := bstep (se 1 (by rfl) ⟨11587211, by rfl⟩ : syracuseStep 15449615 = 23174423) B23174423
theorem B10299743 : Blo 2005435 10299743 := bstep (se 1 (by rfl) ⟨7724807, by rfl⟩ : syracuseStep 10299743 = 15449615) B15449615
theorem B6866495 : Blo 2005435 6866495 := bstep (se 1 (by rfl) ⟨5149871, by rfl⟩ : syracuseStep 6866495 = 10299743) B10299743
theorem B4577663 : Blo 2005435 4577663 := bstep (se 1 (by rfl) ⟨3433247, by rfl⟩ : syracuseStep 4577663 = 6866495) B6866495
theorem B3051775 : Blo 2005435 3051775 := bstep (se 1 (by rfl) ⟨2288831, by rfl⟩ : syracuseStep 3051775 = 4577663) B4577663
theorem B16276133 : Blo 2005435 16276133 := bstep (se 4 (by rfl) ⟨1525887, by rfl⟩ : syracuseStep 16276133 = 3051775) B3051775
theorem B10850755 : Blo 2005435 10850755 := bstep (se 1 (by rfl) ⟨8138066, by rfl⟩ : syracuseStep 10850755 = 16276133) B16276133
theorem B14467673 : Blo 2005435 14467673 := bstep (se 2 (by rfl) ⟨5425377, by rfl⟩ : syracuseStep 14467673 = 10850755) B10850755
theorem B9645115 : Blo 2005435 9645115 := bstep (se 1 (by rfl) ⟨7233836, by rfl⟩ : syracuseStep 9645115 = 14467673) B14467673
theorem B12860153 : Blo 2005435 12860153 := bstep (se 2 (by rfl) ⟨4822557, by rfl⟩ : syracuseStep 12860153 = 9645115) B9645115
theorem B8573435 : Blo 2005435 8573435 := bstep (se 1 (by rfl) ⟨6430076, by rfl⟩ : syracuseStep 8573435 = 12860153) B12860153
theorem B5715623 : Blo 2005435 5715623 := bstep (se 1 (by rfl) ⟨4286717, by rfl⟩ : syracuseStep 5715623 = 8573435) B8573435
theorem B3810415 : Blo 2005435 3810415 := bstep (se 1 (by rfl) ⟨2857811, by rfl⟩ : syracuseStep 3810415 = 5715623) B5715623
theorem B5080553 : Blo 2005435 5080553 := bstep (se 2 (by rfl) ⟨1905207, by rfl⟩ : syracuseStep 5080553 = 3810415) B3810415
theorem B3387035 : Blo 2005435 3387035 := bstep (se 1 (by rfl) ⟨2540276, by rfl⟩ : syracuseStep 3387035 = 5080553) B5080553
theorem B2258023 : Blo 2005435 2258023 := bstep (se 1 (by rfl) ⟨1693517, by rfl⟩ : syracuseStep 2258023 = 3387035) B3387035
theorem B3010697 : Blo 2005435 3010697 := bstep (se 2 (by rfl) ⟨1129011, by rfl⟩ : syracuseStep 3010697 = 2258023) B2258023
theorem B2007131 : Blo 2005435 2007131 := bstep (se 1 (by rfl) ⟨1505348, by rfl⟩ : syracuseStep 2007131 = 3010697) B3010697
theorem B10161125 : Blo 2005435 10161125 := bbase (se 4 (by rfl) ⟨952605, by rfl⟩ : syracuseStep 10161125 = 1905211) (by norm_num)
theorem B6774083 : Blo 2005435 6774083 := bstep (se 1 (by rfl) ⟨5080562, by rfl⟩ : syracuseStep 6774083 = 10161125) B10161125
theorem B4516055 : Blo 2005435 4516055 := bstep (se 1 (by rfl) ⟨3387041, by rfl⟩ : syracuseStep 4516055 = 6774083) B6774083
theorem B3010703 : Blo 2005435 3010703 := bstep (se 1 (by rfl) ⟨2258027, by rfl⟩ : syracuseStep 3010703 = 4516055) B4516055
theorem B2007135 : Blo 2005435 2007135 := bstep (se 1 (by rfl) ⟨1505351, by rfl⟩ : syracuseStep 2007135 = 3010703) B3010703
theorem B3010709 : Blo 2005435 3010709 := bbase (se 6 (by rfl) ⟨70563, by rfl⟩ : syracuseStep 3010709 = 141127) (by norm_num)
theorem B2007139 : Blo 2005435 2007139 := bstep (se 1 (by rfl) ⟨1505354, by rfl⟩ : syracuseStep 2007139 = 3010709) B3010709
theorem B2411293 : Blo 2005435 2411293 := bbase (se 3 (by rfl) ⟨452117, by rfl⟩ : syracuseStep 2411293 = 904235) (by norm_num)
theorem B3215057 : Blo 2005435 3215057 := bstep (se 2 (by rfl) ⟨1205646, by rfl⟩ : syracuseStep 3215057 = 2411293) B2411293
theorem B8573485 : Blo 2005435 8573485 := bstep (se 3 (by rfl) ⟨1607528, by rfl⟩ : syracuseStep 8573485 = 3215057) B3215057
theorem B11431313 : Blo 2005435 11431313 := bstep (se 2 (by rfl) ⟨4286742, by rfl⟩ : syracuseStep 11431313 = 8573485) B8573485
theorem B7620875 : Blo 2005435 7620875 := bstep (se 1 (by rfl) ⟨5715656, by rfl⟩ : syracuseStep 7620875 = 11431313) B11431313
theorem B5080583 : Blo 2005435 5080583 := bstep (se 1 (by rfl) ⟨3810437, by rfl⟩ : syracuseStep 5080583 = 7620875) B7620875
theorem B3387055 : Blo 2005435 3387055 := bstep (se 1 (by rfl) ⟨2540291, by rfl⟩ : syracuseStep 3387055 = 5080583) B5080583
theorem B4516073 : Blo 2005435 4516073 := bstep (se 2 (by rfl) ⟨1693527, by rfl⟩ : syracuseStep 4516073 = 3387055) B3387055
theorem B3010715 : Blo 2005435 3010715 := bstep (se 1 (by rfl) ⟨2258036, by rfl⟩ : syracuseStep 3010715 = 4516073) B4516073
theorem B2007143 : Blo 2005435 2007143 := bstep (se 1 (by rfl) ⟨1505357, by rfl⟩ : syracuseStep 2007143 = 3010715) B3010715
theorem B2258041 : Blo 2005435 2258041 := bbase (se 2 (by rfl) ⟨846765, by rfl⟩ : syracuseStep 2258041 = 1693531) (by norm_num)
theorem B3010721 : Blo 2005435 3010721 := bstep (se 2 (by rfl) ⟨1129020, by rfl⟩ : syracuseStep 3010721 = 2258041) B2258041
theorem B2007147 : Blo 2005435 2007147 := bstep (se 1 (by rfl) ⟨1505360, by rfl⟩ : syracuseStep 2007147 = 3010721) B3010721
theorem B3051805 : Blo 2005435 3051805 := bbase (se 3 (by rfl) ⟨572213, by rfl⟩ : syracuseStep 3051805 = 1144427) (by norm_num)
theorem B4069073 : Blo 2005435 4069073 := bstep (se 2 (by rfl) ⟨1525902, by rfl⟩ : syracuseStep 4069073 = 3051805) B3051805
theorem B10850861 : Blo 2005435 10850861 := bstep (se 3 (by rfl) ⟨2034536, by rfl⟩ : syracuseStep 10850861 = 4069073) B4069073
theorem B28935629 : Blo 2005435 28935629 := bstep (se 3 (by rfl) ⟨5425430, by rfl⟩ : syracuseStep 28935629 = 10850861) B10850861
theorem B19290419 : Blo 2005435 19290419 := bstep (se 1 (by rfl) ⟨14467814, by rfl⟩ : syracuseStep 19290419 = 28935629) B28935629
theorem B12860279 : Blo 2005435 12860279 := bstep (se 1 (by rfl) ⟨9645209, by rfl⟩ : syracuseStep 12860279 = 19290419) B19290419
theorem B8573519 : Blo 2005435 8573519 := bstep (se 1 (by rfl) ⟨6430139, by rfl⟩ : syracuseStep 8573519 = 12860279) B12860279
theorem B5715679 : Blo 2005435 5715679 := bstep (se 1 (by rfl) ⟨4286759, by rfl⟩ : syracuseStep 5715679 = 8573519) B8573519
theorem B7620905 : Blo 2005435 7620905 := bstep (se 2 (by rfl) ⟨2857839, by rfl⟩ : syracuseStep 7620905 = 5715679) B5715679
theorem B5080603 : Blo 2005435 5080603 := bstep (se 1 (by rfl) ⟨3810452, by rfl⟩ : syracuseStep 5080603 = 7620905) B7620905
theorem B6774137 : Blo 2005435 6774137 := bstep (se 2 (by rfl) ⟨2540301, by rfl⟩ : syracuseStep 6774137 = 5080603) B5080603
theorem B4516091 : Blo 2005435 4516091 := bstep (se 1 (by rfl) ⟨3387068, by rfl⟩ : syracuseStep 4516091 = 6774137) B6774137
theorem B3010727 : Blo 2005435 3010727 := bstep (se 1 (by rfl) ⟨2258045, by rfl⟩ : syracuseStep 3010727 = 4516091) B4516091
theorem B2007151 : Blo 2005435 2007151 := bstep (se 1 (by rfl) ⟨1505363, by rfl⟩ : syracuseStep 2007151 = 3010727) B3010727
theorem B3010733 : Blo 2005435 3010733 := bbase (se 3 (by rfl) ⟨564512, by rfl⟩ : syracuseStep 3010733 = 1129025) (by norm_num)
theorem B2007155 : Blo 2005435 2007155 := bstep (se 1 (by rfl) ⟨1505366, by rfl⟩ : syracuseStep 2007155 = 3010733) B3010733
theorem B4516109 : Blo 2005435 4516109 := bbase (se 3 (by rfl) ⟨846770, by rfl⟩ : syracuseStep 4516109 = 1693541) (by norm_num)
theorem B3010739 : Blo 2005435 3010739 := bstep (se 1 (by rfl) ⟨2258054, by rfl⟩ : syracuseStep 3010739 = 4516109) B4516109
theorem B2007159 : Blo 2005435 2007159 := bstep (se 1 (by rfl) ⟨1505369, by rfl⟩ : syracuseStep 2007159 = 3010739) B3010739
theorem B2540317 : Blo 2005435 2540317 := bbase (se 3 (by rfl) ⟨476309, by rfl⟩ : syracuseStep 2540317 = 952619) (by norm_num)
theorem B3387089 : Blo 2005435 3387089 := bstep (se 2 (by rfl) ⟨1270158, by rfl⟩ : syracuseStep 3387089 = 2540317) B2540317
theorem B2258059 : Blo 2005435 2258059 := bstep (se 1 (by rfl) ⟨1693544, by rfl⟩ : syracuseStep 2258059 = 3387089) B3387089
theorem B3010745 : Blo 2005435 3010745 := bstep (se 2 (by rfl) ⟨1129029, by rfl⟩ : syracuseStep 3010745 = 2258059) B2258059
theorem B2007163 : Blo 2005435 2007163 := bstep (se 1 (by rfl) ⟨1505372, by rfl⟩ : syracuseStep 2007163 = 3010745) B3010745
theorem B2034553 : Blo 2005435 2034553 := bbase (se 2 (by rfl) ⟨762957, by rfl⟩ : syracuseStep 2034553 = 1525915) (by norm_num)
theorem B2712737 : Blo 2005435 2712737 := bstep (se 2 (by rfl) ⟨1017276, by rfl⟩ : syracuseStep 2712737 = 2034553) B2034553
theorem B7233965 : Blo 2005435 7233965 := bstep (se 3 (by rfl) ⟨1356368, by rfl⟩ : syracuseStep 7233965 = 2712737) B2712737
theorem B4822643 : Blo 2005435 4822643 := bstep (se 1 (by rfl) ⟨3616982, by rfl⟩ : syracuseStep 4822643 = 7233965) B7233965
theorem B3215095 : Blo 2005435 3215095 := bstep (se 1 (by rfl) ⟨2411321, by rfl⟩ : syracuseStep 3215095 = 4822643) B4822643
theorem B17147173 : Blo 2005435 17147173 := bstep (se 4 (by rfl) ⟨1607547, by rfl⟩ : syracuseStep 17147173 = 3215095) B3215095
theorem B22862897 : Blo 2005435 22862897 := bstep (se 2 (by rfl) ⟨8573586, by rfl⟩ : syracuseStep 22862897 = 17147173) B17147173
theorem B15241931 : Blo 2005435 15241931 := bstep (se 1 (by rfl) ⟨11431448, by rfl⟩ : syracuseStep 15241931 = 22862897) B22862897
theorem B10161287 : Blo 2005435 10161287 := bstep (se 1 (by rfl) ⟨7620965, by rfl⟩ : syracuseStep 10161287 = 15241931) B15241931
theorem B6774191 : Blo 2005435 6774191 := bstep (se 1 (by rfl) ⟨5080643, by rfl⟩ : syracuseStep 6774191 = 10161287) B10161287
theorem B4516127 : Blo 2005435 4516127 := bstep (se 1 (by rfl) ⟨3387095, by rfl⟩ : syracuseStep 4516127 = 6774191) B6774191
theorem B3010751 : Blo 2005435 3010751 := bstep (se 1 (by rfl) ⟨2258063, by rfl⟩ : syracuseStep 3010751 = 4516127) B4516127
theorem B2007167 : Blo 2005435 2007167 := bstep (se 1 (by rfl) ⟨1505375, by rfl⟩ : syracuseStep 2007167 = 3010751) B3010751
theorem B3010757 : Blo 2005435 3010757 := bbase (se 4 (by rfl) ⟨282258, by rfl⟩ : syracuseStep 3010757 = 564517) (by norm_num)
theorem B2007171 : Blo 2005435 2007171 := bstep (se 1 (by rfl) ⟨1505378, by rfl⟩ : syracuseStep 2007171 = 3010757) B3010757
theorem B3387109 : Blo 2005435 3387109 := bbase (se 4 (by rfl) ⟨317541, by rfl⟩ : syracuseStep 3387109 = 635083) (by norm_num)
theorem B4516145 : Blo 2005435 4516145 := bstep (se 2 (by rfl) ⟨1693554, by rfl⟩ : syracuseStep 4516145 = 3387109) B3387109
theorem B3010763 : Blo 2005435 3010763 := bstep (se 1 (by rfl) ⟨2258072, by rfl⟩ : syracuseStep 3010763 = 4516145) B4516145
theorem B2007175 : Blo 2005435 2007175 := bstep (se 1 (by rfl) ⟨1505381, by rfl⟩ : syracuseStep 2007175 = 3010763) B3010763
theorem B2258077 : Blo 2005435 2258077 := bbase (se 3 (by rfl) ⟨423389, by rfl⟩ : syracuseStep 2258077 = 846779) (by norm_num)
theorem B3010769 : Blo 2005435 3010769 := bstep (se 2 (by rfl) ⟨1129038, by rfl⟩ : syracuseStep 3010769 = 2258077) B2258077
theorem B2007179 : Blo 2005435 2007179 := bstep (se 1 (by rfl) ⟨1505384, by rfl⟩ : syracuseStep 2007179 = 3010769) B3010769
theorem B6774245 : Blo 2005435 6774245 := bbase (se 4 (by rfl) ⟨635085, by rfl⟩ : syracuseStep 6774245 = 1270171) (by norm_num)
theorem B4516163 : Blo 2005435 4516163 := bstep (se 1 (by rfl) ⟨3387122, by rfl⟩ : syracuseStep 4516163 = 6774245) B6774245
theorem B3010775 : Blo 2005435 3010775 := bstep (se 1 (by rfl) ⟨2258081, by rfl⟩ : syracuseStep 3010775 = 4516163) B4516163
theorem B2007183 : Blo 2005435 2007183 := bstep (se 1 (by rfl) ⟨1505387, by rfl⟩ : syracuseStep 2007183 = 3010775) B3010775
theorem B3010781 : Blo 2005435 3010781 := bbase (se 3 (by rfl) ⟨564521, by rfl⟩ : syracuseStep 3010781 = 1129043) (by norm_num)
theorem B2007187 : Blo 2005435 2007187 := bstep (se 1 (by rfl) ⟨1505390, by rfl⟩ : syracuseStep 2007187 = 3010781) B3010781
theorem B4516181 : Blo 2005435 4516181 := bbase (se 10 (by rfl) ⟨6615, by rfl⟩ : syracuseStep 4516181 = 13231) (by norm_num)
theorem B3010787 : Blo 2005435 3010787 := bstep (se 1 (by rfl) ⟨2258090, by rfl⟩ : syracuseStep 3010787 = 4516181) B4516181
theorem B2007191 : Blo 2005435 2007191 := bstep (se 1 (by rfl) ⟨1505393, by rfl⟩ : syracuseStep 2007191 = 3010787) B3010787
theorem B3215141 : Blo 2005435 3215141 := bbase (se 4 (by rfl) ⟨301419, by rfl⟩ : syracuseStep 3215141 = 602839) (by norm_num)
theorem B2143427 : Blo 2005435 2143427 := bstep (se 1 (by rfl) ⟨1607570, by rfl⟩ : syracuseStep 2143427 = 3215141) B3215141
theorem B5715805 : Blo 2005435 5715805 := bstep (se 3 (by rfl) ⟨1071713, by rfl⟩ : syracuseStep 5715805 = 2143427) B2143427
theorem B7621073 : Blo 2005435 7621073 := bstep (se 2 (by rfl) ⟨2857902, by rfl⟩ : syracuseStep 7621073 = 5715805) B5715805
theorem B5080715 : Blo 2005435 5080715 := bstep (se 1 (by rfl) ⟨3810536, by rfl⟩ : syracuseStep 5080715 = 7621073) B7621073
theorem B3387143 : Blo 2005435 3387143 := bstep (se 1 (by rfl) ⟨2540357, by rfl⟩ : syracuseStep 3387143 = 5080715) B5080715
theorem B2258095 : Blo 2005435 2258095 := bstep (se 1 (by rfl) ⟨1693571, by rfl⟩ : syracuseStep 2258095 = 3387143) B3387143
theorem B3010793 : Blo 2005435 3010793 := bstep (se 2 (by rfl) ⟨1129047, by rfl⟩ : syracuseStep 3010793 = 2258095) B2258095
theorem B2007195 : Blo 2005435 2007195 := bstep (se 1 (by rfl) ⟨1505396, by rfl⟩ : syracuseStep 2007195 = 3010793) B3010793
theorem B3666389 : Blo 2005435 3666389 := bbase (se 7 (by rfl) ⟨42965, by rfl⟩ : syracuseStep 3666389 = 85931) (by norm_num)
theorem B9777037 : Blo 2005435 9777037 := bstep (se 3 (by rfl) ⟨1833194, by rfl⟩ : syracuseStep 9777037 = 3666389) B3666389
theorem B13036049 : Blo 2005435 13036049 := bstep (se 2 (by rfl) ⟨4888518, by rfl⟩ : syracuseStep 13036049 = 9777037) B9777037
theorem B8690699 : Blo 2005435 8690699 := bstep (se 1 (by rfl) ⟨6518024, by rfl⟩ : syracuseStep 8690699 = 13036049) B13036049
theorem B5793799 : Blo 2005435 5793799 := bstep (se 1 (by rfl) ⟨4345349, by rfl⟩ : syracuseStep 5793799 = 8690699) B8690699
theorem B7725065 : Blo 2005435 7725065 := bstep (se 2 (by rfl) ⟨2896899, by rfl⟩ : syracuseStep 7725065 = 5793799) B5793799
theorem B20600173 : Blo 2005435 20600173 := bstep (se 3 (by rfl) ⟨3862532, by rfl⟩ : syracuseStep 20600173 = 7725065) B7725065
theorem B109867589 : Blo 2005435 109867589 := bstep (se 4 (by rfl) ⟨10300086, by rfl⟩ : syracuseStep 109867589 = 20600173) B20600173
theorem B73245059 : Blo 2005435 73245059 := bstep (se 1 (by rfl) ⟨54933794, by rfl⟩ : syracuseStep 73245059 = 109867589) B109867589
theorem B48830039 : Blo 2005435 48830039 := bstep (se 1 (by rfl) ⟨36622529, by rfl⟩ : syracuseStep 48830039 = 73245059) B73245059
theorem B32553359 : Blo 2005435 32553359 := bstep (se 1 (by rfl) ⟨24415019, by rfl⟩ : syracuseStep 32553359 = 48830039) B48830039
theorem B21702239 : Blo 2005435 21702239 := bstep (se 1 (by rfl) ⟨16276679, by rfl⟩ : syracuseStep 21702239 = 32553359) B32553359
theorem B14468159 : Blo 2005435 14468159 := bstep (se 1 (by rfl) ⟨10851119, by rfl⟩ : syracuseStep 14468159 = 21702239) B21702239
theorem B38581757 : Blo 2005435 38581757 := bstep (se 3 (by rfl) ⟨7234079, by rfl⟩ : syracuseStep 38581757 = 14468159) B14468159
theorem B25721171 : Blo 2005435 25721171 := bstep (se 1 (by rfl) ⟨19290878, by rfl⟩ : syracuseStep 25721171 = 38581757) B38581757
theorem B17147447 : Blo 2005435 17147447 := bstep (se 1 (by rfl) ⟨12860585, by rfl⟩ : syracuseStep 17147447 = 25721171) B25721171
theorem B11431631 : Blo 2005435 11431631 := bstep (se 1 (by rfl) ⟨8573723, by rfl⟩ : syracuseStep 11431631 = 17147447) B17147447
theorem B7621087 : Blo 2005435 7621087 := bstep (se 1 (by rfl) ⟨5715815, by rfl⟩ : syracuseStep 7621087 = 11431631) B11431631
theorem B10161449 : Blo 2005435 10161449 := bstep (se 2 (by rfl) ⟨3810543, by rfl⟩ : syracuseStep 10161449 = 7621087) B7621087
theorem B6774299 : Blo 2005435 6774299 := bstep (se 1 (by rfl) ⟨5080724, by rfl⟩ : syracuseStep 6774299 = 10161449) B10161449
theorem B4516199 : Blo 2005435 4516199 := bstep (se 1 (by rfl) ⟨3387149, by rfl⟩ : syracuseStep 4516199 = 6774299) B6774299
theorem B3010799 : Blo 2005435 3010799 := bstep (se 1 (by rfl) ⟨2258099, by rfl⟩ : syracuseStep 3010799 = 4516199) B4516199
theorem B2007199 : Blo 2005435 2007199 := bstep (se 1 (by rfl) ⟨1505399, by rfl⟩ : syracuseStep 2007199 = 3010799) B3010799
theorem B3010805 : Blo 2005435 3010805 := bbase (se 5 (by rfl) ⟨141131, by rfl⟩ : syracuseStep 3010805 = 282263) (by norm_num)
theorem B2007203 : Blo 2005435 2007203 := bstep (se 1 (by rfl) ⟨1505402, by rfl⟩ : syracuseStep 2007203 = 3010805) B3010805
theorem B3862549 : Blo 2005435 3862549 := bbase (se 6 (by rfl) ⟨90528, by rfl⟩ : syracuseStep 3862549 = 181057) (by norm_num)
theorem B5150065 : Blo 2005435 5150065 := bstep (se 2 (by rfl) ⟨1931274, by rfl⟩ : syracuseStep 5150065 = 3862549) B3862549
theorem B6866753 : Blo 2005435 6866753 := bstep (se 2 (by rfl) ⟨2575032, by rfl⟩ : syracuseStep 6866753 = 5150065) B5150065
theorem B18311341 : Blo 2005435 18311341 := bstep (se 3 (by rfl) ⟨3433376, by rfl⟩ : syracuseStep 18311341 = 6866753) B6866753
theorem B24415121 : Blo 2005435 24415121 := bstep (se 2 (by rfl) ⟨9155670, by rfl⟩ : syracuseStep 24415121 = 18311341) B18311341
theorem B65106989 : Blo 2005435 65106989 := bstep (se 3 (by rfl) ⟨12207560, by rfl⟩ : syracuseStep 65106989 = 24415121) B24415121
theorem B43404659 : Blo 2005435 43404659 := bstep (se 1 (by rfl) ⟨32553494, by rfl⟩ : syracuseStep 43404659 = 65106989) B65106989
theorem B28936439 : Blo 2005435 28936439 := bstep (se 1 (by rfl) ⟨21702329, by rfl⟩ : syracuseStep 28936439 = 43404659) B43404659
theorem B19290959 : Blo 2005435 19290959 := bstep (se 1 (by rfl) ⟨14468219, by rfl⟩ : syracuseStep 19290959 = 28936439) B28936439
theorem B12860639 : Blo 2005435 12860639 := bstep (se 1 (by rfl) ⟨9645479, by rfl⟩ : syracuseStep 12860639 = 19290959) B19290959
theorem B8573759 : Blo 2005435 8573759 := bstep (se 1 (by rfl) ⟨6430319, by rfl⟩ : syracuseStep 8573759 = 12860639) B12860639
theorem B5715839 : Blo 2005435 5715839 := bstep (se 1 (by rfl) ⟨4286879, by rfl⟩ : syracuseStep 5715839 = 8573759) B8573759
theorem B3810559 : Blo 2005435 3810559 := bstep (se 1 (by rfl) ⟨2857919, by rfl⟩ : syracuseStep 3810559 = 5715839) B5715839
theorem B5080745 : Blo 2005435 5080745 := bstep (se 2 (by rfl) ⟨1905279, by rfl⟩ : syracuseStep 5080745 = 3810559) B3810559
theorem B3387163 : Blo 2005435 3387163 := bstep (se 1 (by rfl) ⟨2540372, by rfl⟩ : syracuseStep 3387163 = 5080745) B5080745
theorem B4516217 : Blo 2005435 4516217 := bstep (se 2 (by rfl) ⟨1693581, by rfl⟩ : syracuseStep 4516217 = 3387163) B3387163
theorem B3010811 : Blo 2005435 3010811 := bstep (se 1 (by rfl) ⟨2258108, by rfl⟩ : syracuseStep 3010811 = 4516217) B4516217
theorem B2007207 : Blo 2005435 2007207 := bstep (se 1 (by rfl) ⟨1505405, by rfl⟩ : syracuseStep 2007207 = 3010811) B3010811
theorem B2258113 : Blo 2005435 2258113 := bbase (se 2 (by rfl) ⟨846792, by rfl⟩ : syracuseStep 2258113 = 1693585) (by norm_num)
theorem B3010817 : Blo 2005435 3010817 := bstep (se 2 (by rfl) ⟨1129056, by rfl⟩ : syracuseStep 3010817 = 2258113) B2258113
theorem B2007211 : Blo 2005435 2007211 := bstep (se 1 (by rfl) ⟨1505408, by rfl⟩ : syracuseStep 2007211 = 3010817) B3010817
theorem B5080765 : Blo 2005435 5080765 := bbase (se 3 (by rfl) ⟨952643, by rfl⟩ : syracuseStep 5080765 = 1905287) (by norm_num)
theorem B6774353 : Blo 2005435 6774353 := bstep (se 2 (by rfl) ⟨2540382, by rfl⟩ : syracuseStep 6774353 = 5080765) B5080765
theorem B4516235 : Blo 2005435 4516235 := bstep (se 1 (by rfl) ⟨3387176, by rfl⟩ : syracuseStep 4516235 = 6774353) B6774353
theorem B3010823 : Blo 2005435 3010823 := bstep (se 1 (by rfl) ⟨2258117, by rfl⟩ : syracuseStep 3010823 = 4516235) B4516235
theorem B2007215 : Blo 2005435 2007215 := bstep (se 1 (by rfl) ⟨1505411, by rfl⟩ : syracuseStep 2007215 = 3010823) B3010823
theorem B3010829 : Blo 2005435 3010829 := bbase (se 3 (by rfl) ⟨564530, by rfl⟩ : syracuseStep 3010829 = 1129061) (by norm_num)
theorem B2007219 : Blo 2005435 2007219 := bstep (se 1 (by rfl) ⟨1505414, by rfl⟩ : syracuseStep 2007219 = 3010829) B3010829
theorem B4516253 : Blo 2005435 4516253 := bbase (se 3 (by rfl) ⟨846797, by rfl⟩ : syracuseStep 4516253 = 1693595) (by norm_num)
theorem B3010835 : Blo 2005435 3010835 := bstep (se 1 (by rfl) ⟨2258126, by rfl⟩ : syracuseStep 3010835 = 4516253) B4516253
theorem B2007223 : Blo 2005435 2007223 := bstep (se 1 (by rfl) ⟨1505417, by rfl⟩ : syracuseStep 2007223 = 3010835) B3010835
theorem B3387197 : Blo 2005435 3387197 := bbase (se 3 (by rfl) ⟨635099, by rfl⟩ : syracuseStep 3387197 = 1270199) (by norm_num)
theorem B2258131 : Blo 2005435 2258131 := bstep (se 1 (by rfl) ⟨1693598, by rfl⟩ : syracuseStep 2258131 = 3387197) B3387197
theorem B3010841 : Blo 2005435 3010841 := bstep (se 2 (by rfl) ⟨1129065, by rfl⟩ : syracuseStep 3010841 = 2258131) B2258131
theorem B2007227 : Blo 2005435 2007227 := bstep (se 1 (by rfl) ⟨1505420, by rfl⟩ : syracuseStep 2007227 = 3010841) B3010841
theorem B2143465 : Blo 2005435 2143465 := bbase (se 2 (by rfl) ⟨803799, by rfl⟩ : syracuseStep 2143465 = 1607599) (by norm_num)
theorem B11431813 : Blo 2005435 11431813 := bstep (se 4 (by rfl) ⟨1071732, by rfl⟩ : syracuseStep 11431813 = 2143465) B2143465
theorem B15242417 : Blo 2005435 15242417 := bstep (se 2 (by rfl) ⟨5715906, by rfl⟩ : syracuseStep 15242417 = 11431813) B11431813
theorem B10161611 : Blo 2005435 10161611 := bstep (se 1 (by rfl) ⟨7621208, by rfl⟩ : syracuseStep 10161611 = 15242417) B15242417
theorem B6774407 : Blo 2005435 6774407 := bstep (se 1 (by rfl) ⟨5080805, by rfl⟩ : syracuseStep 6774407 = 10161611) B10161611
theorem B4516271 : Blo 2005435 4516271 := bstep (se 1 (by rfl) ⟨3387203, by rfl⟩ : syracuseStep 4516271 = 6774407) B6774407
theorem B3010847 : Blo 2005435 3010847 := bstep (se 1 (by rfl) ⟨2258135, by rfl⟩ : syracuseStep 3010847 = 4516271) B4516271
theorem B2007231 : Blo 2005435 2007231 := bstep (se 1 (by rfl) ⟨1505423, by rfl⟩ : syracuseStep 2007231 = 3010847) B3010847
theorem B3010853 : Blo 2005435 3010853 := bbase (se 4 (by rfl) ⟨282267, by rfl⟩ : syracuseStep 3010853 = 564535) (by norm_num)
theorem B2007235 : Blo 2005435 2007235 := bstep (se 1 (by rfl) ⟨1505426, by rfl⟩ : syracuseStep 2007235 = 3010853) B3010853
theorem B2540413 : Blo 2005435 2540413 := bbase (se 3 (by rfl) ⟨476327, by rfl⟩ : syracuseStep 2540413 = 952655) (by norm_num)
theorem B3387217 : Blo 2005435 3387217 := bstep (se 2 (by rfl) ⟨1270206, by rfl⟩ : syracuseStep 3387217 = 2540413) B2540413
theorem B4516289 : Blo 2005435 4516289 := bstep (se 2 (by rfl) ⟨1693608, by rfl⟩ : syracuseStep 4516289 = 3387217) B3387217
theorem B3010859 : Blo 2005435 3010859 := bstep (se 1 (by rfl) ⟨2258144, by rfl⟩ : syracuseStep 3010859 = 4516289) B4516289
theorem B2007239 : Blo 2005435 2007239 := bstep (se 1 (by rfl) ⟨1505429, by rfl⟩ : syracuseStep 2007239 = 3010859) B3010859
theorem B2258149 : Blo 2005435 2258149 := bbase (se 4 (by rfl) ⟨211701, by rfl⟩ : syracuseStep 2258149 = 423403) (by norm_num)
theorem B3010865 : Blo 2005435 3010865 := bstep (se 2 (by rfl) ⟨1129074, by rfl⟩ : syracuseStep 3010865 = 2258149) B2258149
theorem B2007243 : Blo 2005435 2007243 := bstep (se 1 (by rfl) ⟨1505432, by rfl⟩ : syracuseStep 2007243 = 3010865) B3010865
theorem B4286965 : Blo 2005435 4286965 := bbase (se 5 (by rfl) ⟨200951, by rfl⟩ : syracuseStep 4286965 = 401903) (by norm_num)
theorem B5715953 : Blo 2005435 5715953 := bstep (se 2 (by rfl) ⟨2143482, by rfl⟩ : syracuseStep 5715953 = 4286965) B4286965
theorem B3810635 : Blo 2005435 3810635 := bstep (se 1 (by rfl) ⟨2857976, by rfl⟩ : syracuseStep 3810635 = 5715953) B5715953
theorem B2540423 : Blo 2005435 2540423 := bstep (se 1 (by rfl) ⟨1905317, by rfl⟩ : syracuseStep 2540423 = 3810635) B3810635
theorem B6774461 : Blo 2005435 6774461 := bstep (se 3 (by rfl) ⟨1270211, by rfl⟩ : syracuseStep 6774461 = 2540423) B2540423
theorem B4516307 : Blo 2005435 4516307 := bstep (se 1 (by rfl) ⟨3387230, by rfl⟩ : syracuseStep 4516307 = 6774461) B6774461
theorem B3010871 : Blo 2005435 3010871 := bstep (se 1 (by rfl) ⟨2258153, by rfl⟩ : syracuseStep 3010871 = 4516307) B4516307
theorem B2007247 : Blo 2005435 2007247 := bstep (se 1 (by rfl) ⟨1505435, by rfl⟩ : syracuseStep 2007247 = 3010871) B3010871
theorem B3010877 : Blo 2005435 3010877 := bbase (se 3 (by rfl) ⟨564539, by rfl⟩ : syracuseStep 3010877 = 1129079) (by norm_num)
theorem B2007251 : Blo 2005435 2007251 := bstep (se 1 (by rfl) ⟨1505438, by rfl⟩ : syracuseStep 2007251 = 3010877) B3010877
theorem B4516325 : Blo 2005435 4516325 := bbase (se 4 (by rfl) ⟨423405, by rfl⟩ : syracuseStep 4516325 = 846811) (by norm_num)
theorem B3010883 : Blo 2005435 3010883 := bstep (se 1 (by rfl) ⟨2258162, by rfl⟩ : syracuseStep 3010883 = 4516325) B4516325
theorem B2007255 : Blo 2005435 2007255 := bstep (se 1 (by rfl) ⟨1505441, by rfl⟩ : syracuseStep 2007255 = 3010883) B3010883
theorem B5080877 : Blo 2005435 5080877 := bbase (se 3 (by rfl) ⟨952664, by rfl⟩ : syracuseStep 5080877 = 1905329) (by norm_num)
theorem B3387251 : Blo 2005435 3387251 := bstep (se 1 (by rfl) ⟨2540438, by rfl⟩ : syracuseStep 3387251 = 5080877) B5080877
theorem B2258167 : Blo 2005435 2258167 := bstep (se 1 (by rfl) ⟨1693625, by rfl⟩ : syracuseStep 2258167 = 3387251) B3387251
theorem B3010889 : Blo 2005435 3010889 := bstep (se 2 (by rfl) ⟨1129083, by rfl⟩ : syracuseStep 3010889 = 2258167) B2258167
theorem B2007259 : Blo 2005435 2007259 := bstep (se 1 (by rfl) ⟨1505444, by rfl⟩ : syracuseStep 2007259 = 3010889) B3010889
theorem B9645749 : Blo 2005435 9645749 := bbase (se 5 (by rfl) ⟨452144, by rfl⟩ : syracuseStep 9645749 = 904289) (by norm_num)
theorem B6430499 : Blo 2005435 6430499 := bstep (se 1 (by rfl) ⟨4822874, by rfl⟩ : syracuseStep 6430499 = 9645749) B9645749
theorem B4286999 : Blo 2005435 4286999 := bstep (se 1 (by rfl) ⟨3215249, by rfl⟩ : syracuseStep 4286999 = 6430499) B6430499
theorem B2857999 : Blo 2005435 2857999 := bstep (se 1 (by rfl) ⟨2143499, by rfl⟩ : syracuseStep 2857999 = 4286999) B4286999
theorem B3810665 : Blo 2005435 3810665 := bstep (se 2 (by rfl) ⟨1428999, by rfl⟩ : syracuseStep 3810665 = 2857999) B2857999
theorem B10161773 : Blo 2005435 10161773 := bstep (se 3 (by rfl) ⟨1905332, by rfl⟩ : syracuseStep 10161773 = 3810665) B3810665
theorem B6774515 : Blo 2005435 6774515 := bstep (se 1 (by rfl) ⟨5080886, by rfl⟩ : syracuseStep 6774515 = 10161773) B10161773
theorem B4516343 : Blo 2005435 4516343 := bstep (se 1 (by rfl) ⟨3387257, by rfl⟩ : syracuseStep 4516343 = 6774515) B6774515
theorem B3010895 : Blo 2005435 3010895 := bstep (se 1 (by rfl) ⟨2258171, by rfl⟩ : syracuseStep 3010895 = 4516343) B4516343
theorem B2007263 : Blo 2005435 2007263 := bstep (se 1 (by rfl) ⟨1505447, by rfl⟩ : syracuseStep 2007263 = 3010895) B3010895
theorem B3010901 : Blo 2005435 3010901 := bbase (se 10 (by rfl) ⟨4410, by rfl⟩ : syracuseStep 3010901 = 8821) (by norm_num)
theorem B2007267 : Blo 2005435 2007267 := bstep (se 1 (by rfl) ⟨1505450, by rfl⟩ : syracuseStep 2007267 = 3010901) B3010901
theorem B5716021 : Blo 2005435 5716021 := bbase (se 5 (by rfl) ⟨267938, by rfl⟩ : syracuseStep 5716021 = 535877) (by norm_num)
theorem B7621361 : Blo 2005435 7621361 := bstep (se 2 (by rfl) ⟨2858010, by rfl⟩ : syracuseStep 7621361 = 5716021) B5716021
theorem B5080907 : Blo 2005435 5080907 := bstep (se 1 (by rfl) ⟨3810680, by rfl⟩ : syracuseStep 5080907 = 7621361) B7621361
theorem B3387271 : Blo 2005435 3387271 := bstep (se 1 (by rfl) ⟨2540453, by rfl⟩ : syracuseStep 3387271 = 5080907) B5080907
theorem B4516361 : Blo 2005435 4516361 := bstep (se 2 (by rfl) ⟨1693635, by rfl⟩ : syracuseStep 4516361 = 3387271) B3387271
theorem B3010907 : Blo 2005435 3010907 := bstep (se 1 (by rfl) ⟨2258180, by rfl⟩ : syracuseStep 3010907 = 4516361) B4516361
theorem B2007271 : Blo 2005435 2007271 := bstep (se 1 (by rfl) ⟨1505453, by rfl⟩ : syracuseStep 2007271 = 3010907) B3010907
theorem B2258185 : Blo 2005435 2258185 := bbase (se 2 (by rfl) ⟨846819, by rfl⟩ : syracuseStep 2258185 = 1693639) (by norm_num)
theorem B3010913 : Blo 2005435 3010913 := bstep (se 2 (by rfl) ⟨1129092, by rfl⟩ : syracuseStep 3010913 = 2258185) B2258185
theorem B2007275 : Blo 2005435 2007275 := bstep (se 1 (by rfl) ⟨1505456, by rfl⟩ : syracuseStep 2007275 = 3010913) B3010913
theorem B25722197 : Blo 2005435 25722197 := bbase (se 11 (by rfl) ⟨18839, by rfl⟩ : syracuseStep 25722197 = 37679) (by norm_num)
theorem B17148131 : Blo 2005435 17148131 := bstep (se 1 (by rfl) ⟨12861098, by rfl⟩ : syracuseStep 17148131 = 25722197) B25722197
theorem B11432087 : Blo 2005435 11432087 := bstep (se 1 (by rfl) ⟨8574065, by rfl⟩ : syracuseStep 11432087 = 17148131) B17148131
theorem B7621391 : Blo 2005435 7621391 := bstep (se 1 (by rfl) ⟨5716043, by rfl⟩ : syracuseStep 7621391 = 11432087) B11432087
theorem B5080927 : Blo 2005435 5080927 := bstep (se 1 (by rfl) ⟨3810695, by rfl⟩ : syracuseStep 5080927 = 7621391) B7621391
theorem B6774569 : Blo 2005435 6774569 := bstep (se 2 (by rfl) ⟨2540463, by rfl⟩ : syracuseStep 6774569 = 5080927) B5080927
theorem B4516379 : Blo 2005435 4516379 := bstep (se 1 (by rfl) ⟨3387284, by rfl⟩ : syracuseStep 4516379 = 6774569) B6774569
theorem B3010919 : Blo 2005435 3010919 := bstep (se 1 (by rfl) ⟨2258189, by rfl⟩ : syracuseStep 3010919 = 4516379) B4516379
theorem B2007279 : Blo 2005435 2007279 := bstep (se 1 (by rfl) ⟨1505459, by rfl⟩ : syracuseStep 2007279 = 3010919) B3010919
theorem B3010925 : Blo 2005435 3010925 := bbase (se 3 (by rfl) ⟨564548, by rfl⟩ : syracuseStep 3010925 = 1129097) (by norm_num)
theorem B2007283 : Blo 2005435 2007283 := bstep (se 1 (by rfl) ⟨1505462, by rfl⟩ : syracuseStep 2007283 = 3010925) B3010925
theorem B4516397 : Blo 2005435 4516397 := bbase (se 3 (by rfl) ⟨846824, by rfl⟩ : syracuseStep 4516397 = 1693649) (by norm_num)
theorem B3010931 : Blo 2005435 3010931 := bstep (se 1 (by rfl) ⟨2258198, by rfl⟩ : syracuseStep 3010931 = 4516397) B4516397
theorem B2007287 : Blo 2005435 2007287 := bstep (se 1 (by rfl) ⟨1505465, by rfl⟩ : syracuseStep 2007287 = 3010931) B3010931
theorem B19821781 : Blo 2005435 19821781 := bbase (se 7 (by rfl) ⟨232286, by rfl⟩ : syracuseStep 19821781 = 464573) (by norm_num)
theorem B26429041 : Blo 2005435 26429041 := bstep (se 2 (by rfl) ⟨9910890, by rfl⟩ : syracuseStep 26429041 = 19821781) B19821781
theorem B35238721 : Blo 2005435 35238721 := bstep (se 2 (by rfl) ⟨13214520, by rfl⟩ : syracuseStep 35238721 = 26429041) B26429041
theorem B46984961 : Blo 2005435 46984961 := bstep (se 2 (by rfl) ⟨17619360, by rfl⟩ : syracuseStep 46984961 = 35238721) B35238721
theorem B31323307 : Blo 2005435 31323307 := bstep (se 1 (by rfl) ⟨23492480, by rfl⟩ : syracuseStep 31323307 = 46984961) B46984961
theorem B41764409 : Blo 2005435 41764409 := bstep (se 2 (by rfl) ⟨15661653, by rfl⟩ : syracuseStep 41764409 = 31323307) B31323307
theorem B27842939 : Blo 2005435 27842939 := bstep (se 1 (by rfl) ⟨20882204, by rfl⟩ : syracuseStep 27842939 = 41764409) B41764409
theorem B18561959 : Blo 2005435 18561959 := bstep (se 1 (by rfl) ⟨13921469, by rfl⟩ : syracuseStep 18561959 = 27842939) B27842939
theorem B12374639 : Blo 2005435 12374639 := bstep (se 1 (by rfl) ⟨9280979, by rfl⟩ : syracuseStep 12374639 = 18561959) B18561959
theorem B8249759 : Blo 2005435 8249759 := bstep (se 1 (by rfl) ⟨6187319, by rfl⟩ : syracuseStep 8249759 = 12374639) B12374639
theorem B5499839 : Blo 2005435 5499839 := bstep (se 1 (by rfl) ⟨4124879, by rfl⟩ : syracuseStep 5499839 = 8249759) B8249759
theorem B3666559 : Blo 2005435 3666559 := bstep (se 1 (by rfl) ⟨2749919, by rfl⟩ : syracuseStep 3666559 = 5499839) B5499839
theorem B4888745 : Blo 2005435 4888745 := bstep (se 2 (by rfl) ⟨1833279, by rfl⟩ : syracuseStep 4888745 = 3666559) B3666559
theorem B3259163 : Blo 2005435 3259163 := bstep (se 1 (by rfl) ⟨2444372, by rfl⟩ : syracuseStep 3259163 = 4888745) B4888745
theorem B8691101 : Blo 2005435 8691101 := bstep (se 3 (by rfl) ⟨1629581, by rfl⟩ : syracuseStep 8691101 = 3259163) B3259163
theorem B5794067 : Blo 2005435 5794067 := bstep (se 1 (by rfl) ⟨4345550, by rfl⟩ : syracuseStep 5794067 = 8691101) B8691101
theorem B3862711 : Blo 2005435 3862711 := bstep (se 1 (by rfl) ⟨2897033, by rfl⟩ : syracuseStep 3862711 = 5794067) B5794067
theorem B20601125 : Blo 2005435 20601125 := bstep (se 4 (by rfl) ⟨1931355, by rfl⟩ : syracuseStep 20601125 = 3862711) B3862711
theorem B13734083 : Blo 2005435 13734083 := bstep (se 1 (by rfl) ⟨10300562, by rfl⟩ : syracuseStep 13734083 = 20601125) B20601125
theorem B36624221 : Blo 2005435 36624221 := bstep (se 3 (by rfl) ⟨6867041, by rfl⟩ : syracuseStep 36624221 = 13734083) B13734083
theorem B24416147 : Blo 2005435 24416147 := bstep (se 1 (by rfl) ⟨18312110, by rfl⟩ : syracuseStep 24416147 = 36624221) B36624221
theorem B16277431 : Blo 2005435 16277431 := bstep (se 1 (by rfl) ⟨12208073, by rfl⟩ : syracuseStep 16277431 = 24416147) B24416147
theorem B21703241 : Blo 2005435 21703241 := bstep (se 2 (by rfl) ⟨8138715, by rfl⟩ : syracuseStep 21703241 = 16277431) B16277431
theorem B14468827 : Blo 2005435 14468827 := bstep (se 1 (by rfl) ⟨10851620, by rfl⟩ : syracuseStep 14468827 = 21703241) B21703241
theorem B19291769 : Blo 2005435 19291769 := bstep (se 2 (by rfl) ⟨7234413, by rfl⟩ : syracuseStep 19291769 = 14468827) B14468827
theorem B12861179 : Blo 2005435 12861179 := bstep (se 1 (by rfl) ⟨9645884, by rfl⟩ : syracuseStep 12861179 = 19291769) B19291769
theorem B8574119 : Blo 2005435 8574119 := bstep (se 1 (by rfl) ⟨6430589, by rfl⟩ : syracuseStep 8574119 = 12861179) B12861179
theorem B5716079 : Blo 2005435 5716079 := bstep (se 1 (by rfl) ⟨4287059, by rfl⟩ : syracuseStep 5716079 = 8574119) B8574119
theorem B3810719 : Blo 2005435 3810719 := bstep (se 1 (by rfl) ⟨2858039, by rfl⟩ : syracuseStep 3810719 = 5716079) B5716079
theorem B2540479 : Blo 2005435 2540479 := bstep (se 1 (by rfl) ⟨1905359, by rfl⟩ : syracuseStep 2540479 = 3810719) B3810719
theorem B3387305 : Blo 2005435 3387305 := bstep (se 2 (by rfl) ⟨1270239, by rfl⟩ : syracuseStep 3387305 = 2540479) B2540479
theorem B2258203 : Blo 2005435 2258203 := bstep (se 1 (by rfl) ⟨1693652, by rfl⟩ : syracuseStep 2258203 = 3387305) B3387305
theorem B3010937 : Blo 2005435 3010937 := bstep (se 2 (by rfl) ⟨1129101, by rfl⟩ : syracuseStep 3010937 = 2258203) B2258203
theorem B2007291 : Blo 2005435 2007291 := bstep (se 1 (by rfl) ⟨1505468, by rfl⟩ : syracuseStep 2007291 = 3010937) B3010937
theorem B34296533 : Blo 2005435 34296533 := bbase (se 7 (by rfl) ⟨401912, by rfl⟩ : syracuseStep 34296533 = 803825) (by norm_num)
theorem B22864355 : Blo 2005435 22864355 := bstep (se 1 (by rfl) ⟨17148266, by rfl⟩ : syracuseStep 22864355 = 34296533) B34296533
theorem B15242903 : Blo 2005435 15242903 := bstep (se 1 (by rfl) ⟨11432177, by rfl⟩ : syracuseStep 15242903 = 22864355) B22864355
theorem B10161935 : Blo 2005435 10161935 := bstep (se 1 (by rfl) ⟨7621451, by rfl⟩ : syracuseStep 10161935 = 15242903) B15242903
theorem B6774623 : Blo 2005435 6774623 := bstep (se 1 (by rfl) ⟨5080967, by rfl⟩ : syracuseStep 6774623 = 10161935) B10161935
theorem B4516415 : Blo 2005435 4516415 := bstep (se 1 (by rfl) ⟨3387311, by rfl⟩ : syracuseStep 4516415 = 6774623) B6774623
theorem B3010943 : Blo 2005435 3010943 := bstep (se 1 (by rfl) ⟨2258207, by rfl⟩ : syracuseStep 3010943 = 4516415) B4516415
theorem B2007295 : Blo 2005435 2007295 := bstep (se 1 (by rfl) ⟨1505471, by rfl⟩ : syracuseStep 2007295 = 3010943) B3010943
theorem B3010949 : Blo 2005435 3010949 := bbase (se 4 (by rfl) ⟨282276, by rfl⟩ : syracuseStep 3010949 = 564553) (by norm_num)
theorem B2007299 : Blo 2005435 2007299 := bstep (se 1 (by rfl) ⟨1505474, by rfl⟩ : syracuseStep 2007299 = 3010949) B3010949
theorem B3387325 : Blo 2005435 3387325 := bbase (se 3 (by rfl) ⟨635123, by rfl⟩ : syracuseStep 3387325 = 1270247) (by norm_num)
theorem B4516433 : Blo 2005435 4516433 := bstep (se 2 (by rfl) ⟨1693662, by rfl⟩ : syracuseStep 4516433 = 3387325) B3387325
theorem B3010955 : Blo 2005435 3010955 := bstep (se 1 (by rfl) ⟨2258216, by rfl⟩ : syracuseStep 3010955 = 4516433) B4516433
theorem B2007303 : Blo 2005435 2007303 := bstep (se 1 (by rfl) ⟨1505477, by rfl⟩ : syracuseStep 2007303 = 3010955) B3010955
theorem B2258221 : Blo 2005435 2258221 := bbase (se 3 (by rfl) ⟨423416, by rfl⟩ : syracuseStep 2258221 = 846833) (by norm_num)
theorem B3010961 : Blo 2005435 3010961 := bstep (se 2 (by rfl) ⟨1129110, by rfl⟩ : syracuseStep 3010961 = 2258221) B2258221
theorem B2007307 : Blo 2005435 2007307 := bstep (se 1 (by rfl) ⟨1505480, by rfl⟩ : syracuseStep 2007307 = 3010961) B3010961
theorem B6774677 : Blo 2005435 6774677 := bbase (se 6 (by rfl) ⟨158781, by rfl⟩ : syracuseStep 6774677 = 317563) (by norm_num)
theorem B4516451 : Blo 2005435 4516451 := bstep (se 1 (by rfl) ⟨3387338, by rfl⟩ : syracuseStep 4516451 = 6774677) B6774677
theorem B3010967 : Blo 2005435 3010967 := bstep (se 1 (by rfl) ⟨2258225, by rfl⟩ : syracuseStep 3010967 = 4516451) B4516451
theorem B2007311 : Blo 2005435 2007311 := bstep (se 1 (by rfl) ⟨1505483, by rfl⟩ : syracuseStep 2007311 = 3010967) B3010967
theorem B3010973 : Blo 2005435 3010973 := bbase (se 3 (by rfl) ⟨564557, by rfl⟩ : syracuseStep 3010973 = 1129115) (by norm_num)
theorem B2007315 : Blo 2005435 2007315 := bstep (se 1 (by rfl) ⟨1505486, by rfl⟩ : syracuseStep 2007315 = 3010973) B3010973
theorem B4516469 : Blo 2005435 4516469 := bbase (se 5 (by rfl) ⟨211709, by rfl⟩ : syracuseStep 4516469 = 423419) (by norm_num)
theorem B3010979 : Blo 2005435 3010979 := bstep (se 1 (by rfl) ⟨2258234, by rfl⟩ : syracuseStep 3010979 = 4516469) B4516469
theorem B2007319 : Blo 2005435 2007319 := bstep (se 1 (by rfl) ⟨1505489, by rfl⟩ : syracuseStep 2007319 = 3010979) B3010979
theorem B9646037 : Blo 2005435 9646037 := bbase (se 7 (by rfl) ⟨113039, by rfl⟩ : syracuseStep 9646037 = 226079) (by norm_num)
theorem B6430691 : Blo 2005435 6430691 := bstep (se 1 (by rfl) ⟨4823018, by rfl⟩ : syracuseStep 6430691 = 9646037) B9646037
theorem B17148509 : Blo 2005435 17148509 := bstep (se 3 (by rfl) ⟨3215345, by rfl⟩ : syracuseStep 17148509 = 6430691) B6430691
theorem B11432339 : Blo 2005435 11432339 := bstep (se 1 (by rfl) ⟨8574254, by rfl⟩ : syracuseStep 11432339 = 17148509) B17148509
theorem B7621559 : Blo 2005435 7621559 := bstep (se 1 (by rfl) ⟨5716169, by rfl⟩ : syracuseStep 7621559 = 11432339) B11432339
theorem B5081039 : Blo 2005435 5081039 := bstep (se 1 (by rfl) ⟨3810779, by rfl⟩ : syracuseStep 5081039 = 7621559) B7621559
theorem B3387359 : Blo 2005435 3387359 := bstep (se 1 (by rfl) ⟨2540519, by rfl⟩ : syracuseStep 3387359 = 5081039) B5081039
theorem B2258239 : Blo 2005435 2258239 := bstep (se 1 (by rfl) ⟨1693679, by rfl⟩ : syracuseStep 2258239 = 3387359) B3387359
theorem B3010985 : Blo 2005435 3010985 := bstep (se 2 (by rfl) ⟨1129119, by rfl⟩ : syracuseStep 3010985 = 2258239) B2258239
theorem B2007323 : Blo 2005435 2007323 := bstep (se 1 (by rfl) ⟨1505492, by rfl⟩ : syracuseStep 2007323 = 3010985) B3010985
theorem B7621573 : Blo 2005435 7621573 := bbase (se 4 (by rfl) ⟨714522, by rfl⟩ : syracuseStep 7621573 = 1429045) (by norm_num)
theorem B10162097 : Blo 2005435 10162097 := bstep (se 2 (by rfl) ⟨3810786, by rfl⟩ : syracuseStep 10162097 = 7621573) B7621573
theorem B6774731 : Blo 2005435 6774731 := bstep (se 1 (by rfl) ⟨5081048, by rfl⟩ : syracuseStep 6774731 = 10162097) B10162097
theorem B4516487 : Blo 2005435 4516487 := bstep (se 1 (by rfl) ⟨3387365, by rfl⟩ : syracuseStep 4516487 = 6774731) B6774731
theorem B3010991 : Blo 2005435 3010991 := bstep (se 1 (by rfl) ⟨2258243, by rfl⟩ : syracuseStep 3010991 = 4516487) B4516487
theorem B2007327 : Blo 2005435 2007327 := bstep (se 1 (by rfl) ⟨1505495, by rfl⟩ : syracuseStep 2007327 = 3010991) B3010991
theorem B3010997 : Blo 2005435 3010997 := bbase (se 5 (by rfl) ⟨141140, by rfl⟩ : syracuseStep 3010997 = 282281) (by norm_num)
theorem B2007331 : Blo 2005435 2007331 := bstep (se 1 (by rfl) ⟨1505498, by rfl⟩ : syracuseStep 2007331 = 3010997) B3010997
theorem B5081069 : Blo 2005435 5081069 := bbase (se 3 (by rfl) ⟨952700, by rfl⟩ : syracuseStep 5081069 = 1905401) (by norm_num)
theorem B3387379 : Blo 2005435 3387379 := bstep (se 1 (by rfl) ⟨2540534, by rfl⟩ : syracuseStep 3387379 = 5081069) B5081069
theorem B4516505 : Blo 2005435 4516505 := bstep (se 2 (by rfl) ⟨1693689, by rfl⟩ : syracuseStep 4516505 = 3387379) B3387379
theorem B3011003 : Blo 2005435 3011003 := bstep (se 1 (by rfl) ⟨2258252, by rfl⟩ : syracuseStep 3011003 = 4516505) B4516505
theorem B2007335 : Blo 2005435 2007335 := bstep (se 1 (by rfl) ⟨1505501, by rfl⟩ : syracuseStep 2007335 = 3011003) B3011003
theorem B2258257 : Blo 2005435 2258257 := bbase (se 2 (by rfl) ⟨846846, by rfl⟩ : syracuseStep 2258257 = 1693693) (by norm_num)
theorem B3011009 : Blo 2005435 3011009 := bstep (se 2 (by rfl) ⟨1129128, by rfl⟩ : syracuseStep 3011009 = 2258257) B2258257
theorem B2007339 : Blo 2005435 2007339 := bstep (se 1 (by rfl) ⟨1505504, by rfl⟩ : syracuseStep 2007339 = 3011009) B3011009
theorem B2143585 : Blo 2005435 2143585 := bbase (se 2 (by rfl) ⟨803844, by rfl⟩ : syracuseStep 2143585 = 1607689) (by norm_num)
theorem B2858113 : Blo 2005435 2858113 := bstep (se 2 (by rfl) ⟨1071792, by rfl⟩ : syracuseStep 2858113 = 2143585) B2143585
theorem B3810817 : Blo 2005435 3810817 := bstep (se 2 (by rfl) ⟨1429056, by rfl⟩ : syracuseStep 3810817 = 2858113) B2858113
theorem B5081089 : Blo 2005435 5081089 := bstep (se 2 (by rfl) ⟨1905408, by rfl⟩ : syracuseStep 5081089 = 3810817) B3810817
theorem B6774785 : Blo 2005435 6774785 := bstep (se 2 (by rfl) ⟨2540544, by rfl⟩ : syracuseStep 6774785 = 5081089) B5081089
theorem B4516523 : Blo 2005435 4516523 := bstep (se 1 (by rfl) ⟨3387392, by rfl⟩ : syracuseStep 4516523 = 6774785) B6774785
theorem B3011015 : Blo 2005435 3011015 := bstep (se 1 (by rfl) ⟨2258261, by rfl⟩ : syracuseStep 3011015 = 4516523) B4516523
theorem B2007343 : Blo 2005435 2007343 := bstep (se 1 (by rfl) ⟨1505507, by rfl⟩ : syracuseStep 2007343 = 3011015) B3011015
theorem B3011021 : Blo 2005435 3011021 := bbase (se 3 (by rfl) ⟨564566, by rfl⟩ : syracuseStep 3011021 = 1129133) (by norm_num)
theorem B2007347 : Blo 2005435 2007347 := bstep (se 1 (by rfl) ⟨1505510, by rfl⟩ : syracuseStep 2007347 = 3011021) B3011021
theorem B4516541 : Blo 2005435 4516541 := bbase (se 3 (by rfl) ⟨846851, by rfl⟩ : syracuseStep 4516541 = 1693703) (by norm_num)
theorem B3011027 : Blo 2005435 3011027 := bstep (se 1 (by rfl) ⟨2258270, by rfl⟩ : syracuseStep 3011027 = 4516541) B4516541
theorem B2007351 : Blo 2005435 2007351 := bstep (se 1 (by rfl) ⟨1505513, by rfl⟩ : syracuseStep 2007351 = 3011027) B3011027
theorem B3387413 : Blo 2005435 3387413 := bbase (se 6 (by rfl) ⟨79392, by rfl⟩ : syracuseStep 3387413 = 158785) (by norm_num)
theorem B2258275 : Blo 2005435 2258275 := bstep (se 1 (by rfl) ⟨1693706, by rfl⟩ : syracuseStep 2258275 = 3387413) B3387413
theorem B3011033 : Blo 2005435 3011033 := bstep (se 2 (by rfl) ⟨1129137, by rfl⟩ : syracuseStep 3011033 = 2258275) B2258275
theorem B2007355 : Blo 2005435 2007355 := bstep (se 1 (by rfl) ⟨1505516, by rfl⟩ : syracuseStep 2007355 = 3011033) B3011033
theorem B3433637 : Blo 2005435 3433637 := bbase (se 4 (by rfl) ⟨321903, by rfl⟩ : syracuseStep 3433637 = 643807) (by norm_num)
theorem B2289091 : Blo 2005435 2289091 := bstep (se 1 (by rfl) ⟨1716818, by rfl⟩ : syracuseStep 2289091 = 3433637) B3433637
theorem B3052121 : Blo 2005435 3052121 := bstep (se 2 (by rfl) ⟨1144545, by rfl⟩ : syracuseStep 3052121 = 2289091) B2289091
theorem B8138989 : Blo 2005435 8138989 := bstep (se 3 (by rfl) ⟨1526060, by rfl⟩ : syracuseStep 8138989 = 3052121) B3052121
theorem B10851985 : Blo 2005435 10851985 := bstep (se 2 (by rfl) ⟨4069494, by rfl⟩ : syracuseStep 10851985 = 8138989) B8138989
theorem B14469313 : Blo 2005435 14469313 := bstep (se 2 (by rfl) ⟨5425992, by rfl⟩ : syracuseStep 14469313 = 10851985) B10851985
theorem B19292417 : Blo 2005435 19292417 := bstep (se 2 (by rfl) ⟨7234656, by rfl⟩ : syracuseStep 19292417 = 14469313) B14469313
theorem B12861611 : Blo 2005435 12861611 := bstep (se 1 (by rfl) ⟨9646208, by rfl⟩ : syracuseStep 12861611 = 19292417) B19292417
theorem B8574407 : Blo 2005435 8574407 := bstep (se 1 (by rfl) ⟨6430805, by rfl⟩ : syracuseStep 8574407 = 12861611) B12861611
theorem B5716271 : Blo 2005435 5716271 := bstep (se 1 (by rfl) ⟨4287203, by rfl⟩ : syracuseStep 5716271 = 8574407) B8574407
theorem B15243389 : Blo 2005435 15243389 := bstep (se 3 (by rfl) ⟨2858135, by rfl⟩ : syracuseStep 15243389 = 5716271) B5716271
theorem B10162259 : Blo 2005435 10162259 := bstep (se 1 (by rfl) ⟨7621694, by rfl⟩ : syracuseStep 10162259 = 15243389) B15243389
theorem B6774839 : Blo 2005435 6774839 := bstep (se 1 (by rfl) ⟨5081129, by rfl⟩ : syracuseStep 6774839 = 10162259) B10162259
theorem B4516559 : Blo 2005435 4516559 := bstep (se 1 (by rfl) ⟨3387419, by rfl⟩ : syracuseStep 4516559 = 6774839) B6774839
theorem B3011039 : Blo 2005435 3011039 := bstep (se 1 (by rfl) ⟨2258279, by rfl⟩ : syracuseStep 3011039 = 4516559) B4516559
theorem B2007359 : Blo 2005435 2007359 := bstep (se 1 (by rfl) ⟨1505519, by rfl⟩ : syracuseStep 2007359 = 3011039) B3011039
theorem B3011045 : Blo 2005435 3011045 := bbase (se 4 (by rfl) ⟨282285, by rfl⟩ : syracuseStep 3011045 = 564571) (by norm_num)
theorem B2007363 : Blo 2005435 2007363 := bstep (se 1 (by rfl) ⟨1505522, by rfl⟩ : syracuseStep 2007363 = 3011045) B3011045
theorem B2062517 : Blo 2005435 2062517 := bbase (se 5 (by rfl) ⟨96680, by rfl⟩ : syracuseStep 2062517 = 193361) (by norm_num)
theorem B5500045 : Blo 2005435 5500045 := bstep (se 3 (by rfl) ⟨1031258, by rfl⟩ : syracuseStep 5500045 = 2062517) B2062517
theorem B29333573 : Blo 2005435 29333573 := bstep (se 4 (by rfl) ⟨2750022, by rfl⟩ : syracuseStep 29333573 = 5500045) B5500045
theorem B19555715 : Blo 2005435 19555715 := bstep (se 1 (by rfl) ⟨14666786, by rfl⟩ : syracuseStep 19555715 = 29333573) B29333573
theorem B13037143 : Blo 2005435 13037143 := bstep (se 1 (by rfl) ⟨9777857, by rfl⟩ : syracuseStep 13037143 = 19555715) B19555715
theorem B17382857 : Blo 2005435 17382857 := bstep (se 2 (by rfl) ⟨6518571, by rfl⟩ : syracuseStep 17382857 = 13037143) B13037143
theorem B46354285 : Blo 2005435 46354285 := bstep (se 3 (by rfl) ⟨8691428, by rfl⟩ : syracuseStep 46354285 = 17382857) B17382857
theorem B61805713 : Blo 2005435 61805713 := bstep (se 2 (by rfl) ⟨23177142, by rfl⟩ : syracuseStep 61805713 = 46354285) B46354285
theorem B82407617 : Blo 2005435 82407617 := bstep (se 2 (by rfl) ⟨30902856, by rfl⟩ : syracuseStep 82407617 = 61805713) B61805713
theorem B54938411 : Blo 2005435 54938411 := bstep (se 1 (by rfl) ⟨41203808, by rfl⟩ : syracuseStep 54938411 = 82407617) B82407617
theorem B36625607 : Blo 2005435 36625607 := bstep (se 1 (by rfl) ⟨27469205, by rfl⟩ : syracuseStep 36625607 = 54938411) B54938411
theorem B24417071 : Blo 2005435 24417071 := bstep (se 1 (by rfl) ⟨18312803, by rfl⟩ : syracuseStep 24417071 = 36625607) B36625607
theorem B16278047 : Blo 2005435 16278047 := bstep (se 1 (by rfl) ⟨12208535, by rfl⟩ : syracuseStep 16278047 = 24417071) B24417071
theorem B10852031 : Blo 2005435 10852031 := bstep (se 1 (by rfl) ⟨8139023, by rfl⟩ : syracuseStep 10852031 = 16278047) B16278047
theorem B7234687 : Blo 2005435 7234687 := bstep (se 1 (by rfl) ⟨5426015, by rfl⟩ : syracuseStep 7234687 = 10852031) B10852031
theorem B9646249 : Blo 2005435 9646249 := bstep (se 2 (by rfl) ⟨3617343, by rfl⟩ : syracuseStep 9646249 = 7234687) B7234687
theorem B12861665 : Blo 2005435 12861665 := bstep (se 2 (by rfl) ⟨4823124, by rfl⟩ : syracuseStep 12861665 = 9646249) B9646249
theorem B8574443 : Blo 2005435 8574443 := bstep (se 1 (by rfl) ⟨6430832, by rfl⟩ : syracuseStep 8574443 = 12861665) B12861665
theorem B5716295 : Blo 2005435 5716295 := bstep (se 1 (by rfl) ⟨4287221, by rfl⟩ : syracuseStep 5716295 = 8574443) B8574443
theorem B3810863 : Blo 2005435 3810863 := bstep (se 1 (by rfl) ⟨2858147, by rfl⟩ : syracuseStep 3810863 = 5716295) B5716295
theorem B2540575 : Blo 2005435 2540575 := bstep (se 1 (by rfl) ⟨1905431, by rfl⟩ : syracuseStep 2540575 = 3810863) B3810863
theorem B3387433 : Blo 2005435 3387433 := bstep (se 2 (by rfl) ⟨1270287, by rfl⟩ : syracuseStep 3387433 = 2540575) B2540575
theorem B4516577 : Blo 2005435 4516577 := bstep (se 2 (by rfl) ⟨1693716, by rfl⟩ : syracuseStep 4516577 = 3387433) B3387433
theorem B3011051 : Blo 2005435 3011051 := bstep (se 1 (by rfl) ⟨2258288, by rfl⟩ : syracuseStep 3011051 = 4516577) B4516577
theorem B2007367 : Blo 2005435 2007367 := bstep (se 1 (by rfl) ⟨1505525, by rfl⟩ : syracuseStep 2007367 = 3011051) B3011051
theorem B2258293 : Blo 2005435 2258293 := bbase (se 5 (by rfl) ⟨105857, by rfl⟩ : syracuseStep 2258293 = 211715) (by norm_num)
theorem B3011057 : Blo 2005435 3011057 := bstep (se 2 (by rfl) ⟨1129146, by rfl⟩ : syracuseStep 3011057 = 2258293) B2258293
theorem B2007371 : Blo 2005435 2007371 := bstep (se 1 (by rfl) ⟨1505528, by rfl⟩ : syracuseStep 2007371 = 3011057) B3011057
theorem B2540585 : Blo 2005435 2540585 := bbase (se 2 (by rfl) ⟨952719, by rfl⟩ : syracuseStep 2540585 = 1905439) (by norm_num)
theorem B6774893 : Blo 2005435 6774893 := bstep (se 3 (by rfl) ⟨1270292, by rfl⟩ : syracuseStep 6774893 = 2540585) B2540585
theorem B4516595 : Blo 2005435 4516595 := bstep (se 1 (by rfl) ⟨3387446, by rfl⟩ : syracuseStep 4516595 = 6774893) B6774893
theorem B3011063 : Blo 2005435 3011063 := bstep (se 1 (by rfl) ⟨2258297, by rfl⟩ : syracuseStep 3011063 = 4516595) B4516595
theorem B2007375 : Blo 2005435 2007375 := bstep (se 1 (by rfl) ⟨1505531, by rfl⟩ : syracuseStep 2007375 = 3011063) B3011063
theorem B3011069 : Blo 2005435 3011069 := bbase (se 3 (by rfl) ⟨564575, by rfl⟩ : syracuseStep 3011069 = 1129151) (by norm_num)
theorem B2007379 : Blo 2005435 2007379 := bstep (se 1 (by rfl) ⟨1505534, by rfl⟩ : syracuseStep 2007379 = 3011069) B3011069
theorem B4516613 : Blo 2005435 4516613 := bbase (se 4 (by rfl) ⟨423432, by rfl⟩ : syracuseStep 4516613 = 846865) (by norm_num)
theorem B3011075 : Blo 2005435 3011075 := bstep (se 1 (by rfl) ⟨2258306, by rfl⟩ : syracuseStep 3011075 = 4516613) B4516613
theorem B2007383 : Blo 2005435 2007383 := bstep (se 1 (by rfl) ⟨1505537, by rfl⟩ : syracuseStep 2007383 = 3011075) B3011075
theorem B3810901 : Blo 2005435 3810901 := bbase (se 8 (by rfl) ⟨22329, by rfl⟩ : syracuseStep 3810901 = 44659) (by norm_num)
theorem B5081201 : Blo 2005435 5081201 := bstep (se 2 (by rfl) ⟨1905450, by rfl⟩ : syracuseStep 5081201 = 3810901) B3810901
theorem B3387467 : Blo 2005435 3387467 := bstep (se 1 (by rfl) ⟨2540600, by rfl⟩ : syracuseStep 3387467 = 5081201) B5081201
theorem B2258311 : Blo 2005435 2258311 := bstep (se 1 (by rfl) ⟨1693733, by rfl⟩ : syracuseStep 2258311 = 3387467) B3387467
theorem B3011081 : Blo 2005435 3011081 := bstep (se 2 (by rfl) ⟨1129155, by rfl⟩ : syracuseStep 3011081 = 2258311) B2258311
theorem B2007387 : Blo 2005435 2007387 := bstep (se 1 (by rfl) ⟨1505540, by rfl⟩ : syracuseStep 2007387 = 3011081) B3011081
theorem B10162421 : Blo 2005435 10162421 := bbase (se 5 (by rfl) ⟨476363, by rfl⟩ : syracuseStep 10162421 = 952727) (by norm_num)
theorem B6774947 : Blo 2005435 6774947 := bstep (se 1 (by rfl) ⟨5081210, by rfl⟩ : syracuseStep 6774947 = 10162421) B10162421
theorem B4516631 : Blo 2005435 4516631 := bstep (se 1 (by rfl) ⟨3387473, by rfl⟩ : syracuseStep 4516631 = 6774947) B6774947
theorem B3011087 : Blo 2005435 3011087 := bstep (se 1 (by rfl) ⟨2258315, by rfl⟩ : syracuseStep 3011087 = 4516631) B4516631
theorem B2007391 : Blo 2005435 2007391 := bstep (se 1 (by rfl) ⟨1505543, by rfl⟩ : syracuseStep 2007391 = 3011087) B3011087
theorem B3011093 : Blo 2005435 3011093 := bbase (se 6 (by rfl) ⟨70572, by rfl⟩ : syracuseStep 3011093 = 141145) (by norm_num)
theorem B2007395 : Blo 2005435 2007395 := bstep (se 1 (by rfl) ⟨1505546, by rfl⟩ : syracuseStep 2007395 = 3011093) B3011093
theorem B6867413 : Blo 2005435 6867413 := bbase (se 7 (by rfl) ⟨80477, by rfl⟩ : syracuseStep 6867413 = 160955) (by norm_num)
theorem B4578275 : Blo 2005435 4578275 := bstep (se 1 (by rfl) ⟨3433706, by rfl⟩ : syracuseStep 4578275 = 6867413) B6867413
theorem B3052183 : Blo 2005435 3052183 := bstep (se 1 (by rfl) ⟨2289137, by rfl⟩ : syracuseStep 3052183 = 4578275) B4578275
theorem B4069577 : Blo 2005435 4069577 := bstep (se 2 (by rfl) ⟨1526091, by rfl⟩ : syracuseStep 4069577 = 3052183) B3052183
theorem B2713051 : Blo 2005435 2713051 := bstep (se 1 (by rfl) ⟨2034788, by rfl⟩ : syracuseStep 2713051 = 4069577) B4069577
theorem B3617401 : Blo 2005435 3617401 := bstep (se 2 (by rfl) ⟨1356525, by rfl⟩ : syracuseStep 3617401 = 2713051) B2713051
theorem B4823201 : Blo 2005435 4823201 := bstep (se 2 (by rfl) ⟨1808700, by rfl⟩ : syracuseStep 4823201 = 3617401) B3617401
theorem B3215467 : Blo 2005435 3215467 := bstep (se 1 (by rfl) ⟨2411600, by rfl⟩ : syracuseStep 3215467 = 4823201) B4823201
theorem B17149157 : Blo 2005435 17149157 := bstep (se 4 (by rfl) ⟨1607733, by rfl⟩ : syracuseStep 17149157 = 3215467) B3215467
theorem B11432771 : Blo 2005435 11432771 := bstep (se 1 (by rfl) ⟨8574578, by rfl⟩ : syracuseStep 11432771 = 17149157) B17149157
theorem B7621847 : Blo 2005435 7621847 := bstep (se 1 (by rfl) ⟨5716385, by rfl⟩ : syracuseStep 7621847 = 11432771) B11432771
theorem B5081231 : Blo 2005435 5081231 := bstep (se 1 (by rfl) ⟨3810923, by rfl⟩ : syracuseStep 5081231 = 7621847) B7621847
theorem B3387487 : Blo 2005435 3387487 := bstep (se 1 (by rfl) ⟨2540615, by rfl⟩ : syracuseStep 3387487 = 5081231) B5081231
theorem B4516649 : Blo 2005435 4516649 := bstep (se 2 (by rfl) ⟨1693743, by rfl⟩ : syracuseStep 4516649 = 3387487) B3387487
theorem B3011099 : Blo 2005435 3011099 := bstep (se 1 (by rfl) ⟨2258324, by rfl⟩ : syracuseStep 3011099 = 4516649) B4516649
theorem B2007399 : Blo 2005435 2007399 := bstep (se 1 (by rfl) ⟨1505549, by rfl⟩ : syracuseStep 2007399 = 3011099) B3011099
theorem B2258329 : Blo 2005435 2258329 := bbase (se 2 (by rfl) ⟨846873, by rfl⟩ : syracuseStep 2258329 = 1693747) (by norm_num)
theorem B3011105 : Blo 2005435 3011105 := bstep (se 2 (by rfl) ⟨1129164, by rfl⟩ : syracuseStep 3011105 = 2258329) B2258329
theorem B2007403 : Blo 2005435 2007403 := bstep (se 1 (by rfl) ⟨1505552, by rfl⟩ : syracuseStep 2007403 = 3011105) B3011105
theorem B7621877 : Blo 2005435 7621877 := bbase (se 5 (by rfl) ⟨357275, by rfl⟩ : syracuseStep 7621877 = 714551) (by norm_num)
theorem B5081251 : Blo 2005435 5081251 := bstep (se 1 (by rfl) ⟨3810938, by rfl⟩ : syracuseStep 5081251 = 7621877) B7621877
theorem B6775001 : Blo 2005435 6775001 := bstep (se 2 (by rfl) ⟨2540625, by rfl⟩ : syracuseStep 6775001 = 5081251) B5081251
theorem B4516667 : Blo 2005435 4516667 := bstep (se 1 (by rfl) ⟨3387500, by rfl⟩ : syracuseStep 4516667 = 6775001) B6775001
theorem B3011111 : Blo 2005435 3011111 := bstep (se 1 (by rfl) ⟨2258333, by rfl⟩ : syracuseStep 3011111 = 4516667) B4516667
theorem B2007407 : Blo 2005435 2007407 := bstep (se 1 (by rfl) ⟨1505555, by rfl⟩ : syracuseStep 2007407 = 3011111) B3011111
theorem B3011117 : Blo 2005435 3011117 := bbase (se 3 (by rfl) ⟨564584, by rfl⟩ : syracuseStep 3011117 = 1129169) (by norm_num)
theorem B2007411 : Blo 2005435 2007411 := bstep (se 1 (by rfl) ⟨1505558, by rfl⟩ : syracuseStep 2007411 = 3011117) B3011117
theorem B4516685 : Blo 2005435 4516685 := bbase (se 3 (by rfl) ⟨846878, by rfl⟩ : syracuseStep 4516685 = 1693757) (by norm_num)
theorem B3011123 : Blo 2005435 3011123 := bstep (se 1 (by rfl) ⟨2258342, by rfl⟩ : syracuseStep 3011123 = 4516685) B4516685
theorem B2007415 : Blo 2005435 2007415 := bstep (se 1 (by rfl) ⟨1505561, by rfl⟩ : syracuseStep 2007415 = 3011123) B3011123
theorem B2540641 : Blo 2005435 2540641 := bbase (se 2 (by rfl) ⟨952740, by rfl⟩ : syracuseStep 2540641 = 1905481) (by norm_num)
theorem B3387521 : Blo 2005435 3387521 := bstep (se 2 (by rfl) ⟨1270320, by rfl⟩ : syracuseStep 3387521 = 2540641) B2540641
theorem B2258347 : Blo 2005435 2258347 := bstep (se 1 (by rfl) ⟨1693760, by rfl⟩ : syracuseStep 2258347 = 3387521) B3387521
theorem B3011129 : Blo 2005435 3011129 := bstep (se 2 (by rfl) ⟨1129173, by rfl⟩ : syracuseStep 3011129 = 2258347) B2258347
theorem B2007419 : Blo 2005435 2007419 := bstep (se 1 (by rfl) ⟨1505564, by rfl⟩ : syracuseStep 2007419 = 3011129) B3011129
theorem B22865813 : Blo 2005435 22865813 := bbase (se 6 (by rfl) ⟨535917, by rfl⟩ : syracuseStep 22865813 = 1071835) (by norm_num)
theorem B15243875 : Blo 2005435 15243875 := bstep (se 1 (by rfl) ⟨11432906, by rfl⟩ : syracuseStep 15243875 = 22865813) B22865813
theorem B10162583 : Blo 2005435 10162583 := bstep (se 1 (by rfl) ⟨7621937, by rfl⟩ : syracuseStep 10162583 = 15243875) B15243875
theorem B6775055 : Blo 2005435 6775055 := bstep (se 1 (by rfl) ⟨5081291, by rfl⟩ : syracuseStep 6775055 = 10162583) B10162583
theorem B4516703 : Blo 2005435 4516703 := bstep (se 1 (by rfl) ⟨3387527, by rfl⟩ : syracuseStep 4516703 = 6775055) B6775055
theorem B3011135 : Blo 2005435 3011135 := bstep (se 1 (by rfl) ⟨2258351, by rfl⟩ : syracuseStep 3011135 = 4516703) B4516703
theorem B2007423 : Blo 2005435 2007423 := bstep (se 1 (by rfl) ⟨1505567, by rfl⟩ : syracuseStep 2007423 = 3011135) B3011135
theorem B3011141 : Blo 2005435 3011141 := bbase (se 4 (by rfl) ⟨282294, by rfl⟩ : syracuseStep 3011141 = 564589) (by norm_num)
theorem B2007427 : Blo 2005435 2007427 := bstep (se 1 (by rfl) ⟨1505570, by rfl⟩ : syracuseStep 2007427 = 3011141) B3011141
theorem B3387541 : Blo 2005435 3387541 := bbase (se 6 (by rfl) ⟨79395, by rfl⟩ : syracuseStep 3387541 = 158791) (by norm_num)
theorem B4516721 : Blo 2005435 4516721 := bstep (se 2 (by rfl) ⟨1693770, by rfl⟩ : syracuseStep 4516721 = 3387541) B3387541
theorem B3011147 : Blo 2005435 3011147 := bstep (se 1 (by rfl) ⟨2258360, by rfl⟩ : syracuseStep 3011147 = 4516721) B4516721
theorem B2007431 : Blo 2005435 2007431 := bstep (se 1 (by rfl) ⟨1505573, by rfl⟩ : syracuseStep 2007431 = 3011147) B3011147
theorem B2258365 : Blo 2005435 2258365 := bbase (se 3 (by rfl) ⟨423443, by rfl⟩ : syracuseStep 2258365 = 846887) (by norm_num)
theorem B3011153 : Blo 2005435 3011153 := bstep (se 2 (by rfl) ⟨1129182, by rfl⟩ : syracuseStep 3011153 = 2258365) B2258365
theorem B2007435 : Blo 2005435 2007435 := bstep (se 1 (by rfl) ⟨1505576, by rfl⟩ : syracuseStep 2007435 = 3011153) B3011153
theorem C0 (j : ℕ) (h1 : 501358 ≤ j) (h2 : j ≤ 501858) : Blo 2005435 (4 * j + 3) := by
  interval_cases j
  · exact B2005435
  · exact B2005439
  · exact B2005443
  · exact B2005447
  · exact B2005451
  · exact B2005455
  · exact B2005459
  · exact B2005463
  · exact B2005467
  · exact B2005471
  · exact B2005475
  · exact B2005479
  · exact B2005483
  · exact B2005487
  · exact B2005491
  · exact B2005495
  · exact B2005499
  · exact B2005503
  · exact B2005507
  · exact B2005511
  · exact B2005515
  · exact B2005519
  · exact B2005523
  · exact B2005527
  · exact B2005531
  · exact B2005535
  · exact B2005539
  · exact B2005543
  · exact B2005547
  · exact B2005551
  · exact B2005555
  · exact B2005559
  · exact B2005563
  · exact B2005567
  · exact B2005571
  · exact B2005575
  · exact B2005579
  · exact B2005583
  · exact B2005587
  · exact B2005591
  · exact B2005595
  · exact B2005599
  · exact B2005603
  · exact B2005607
  · exact B2005611
  · exact B2005615
  · exact B2005619
  · exact B2005623
  · exact B2005627
  · exact B2005631
  · exact B2005635
  · exact B2005639
  · exact B2005643
  · exact B2005647
  · exact B2005651
  · exact B2005655
  · exact B2005659
  · exact B2005663
  · exact B2005667
  · exact B2005671
  · exact B2005675
  · exact B2005679
  · exact B2005683
  · exact B2005687
  · exact B2005691
  · exact B2005695
  · exact B2005699
  · exact B2005703
  · exact B2005707
  · exact B2005711
  · exact B2005715
  · exact B2005719
  · exact B2005723
  · exact B2005727
  · exact B2005731
  · exact B2005735
  · exact B2005739
  · exact B2005743
  · exact B2005747
  · exact B2005751
  · exact B2005755
  · exact B2005759
  · exact B2005763
  · exact B2005767
  · exact B2005771
  · exact B2005775
  · exact B2005779
  · exact B2005783
  · exact B2005787
  · exact B2005791
  · exact B2005795
  · exact B2005799
  · exact B2005803
  · exact B2005807
  · exact B2005811
  · exact B2005815
  · exact B2005819
  · exact B2005823
  · exact B2005827
  · exact B2005831
  · exact B2005835
  · exact B2005839
  · exact B2005843
  · exact B2005847
  · exact B2005851
  · exact B2005855
  · exact B2005859
  · exact B2005863
  · exact B2005867
  · exact B2005871
  · exact B2005875
  · exact B2005879
  · exact B2005883
  · exact B2005887
  · exact B2005891
  · exact B2005895
  · exact B2005899
  · exact B2005903
  · exact B2005907
  · exact B2005911
  · exact B2005915
  · exact B2005919
  · exact B2005923
  · exact B2005927
  · exact B2005931
  · exact B2005935
  · exact B2005939
  · exact B2005943
  · exact B2005947
  · exact B2005951
  · exact B2005955
  · exact B2005959
  · exact B2005963
  · exact B2005967
  · exact B2005971
  · exact B2005975
  · exact B2005979
  · exact B2005983
  · exact B2005987
  · exact B2005991
  · exact B2005995
  · exact B2005999
  · exact B2006003
  · exact B2006007
  · exact B2006011
  · exact B2006015
  · exact B2006019
  · exact B2006023
  · exact B2006027
  · exact B2006031
  · exact B2006035
  · exact B2006039
  · exact B2006043
  · exact B2006047
  · exact B2006051
  · exact B2006055
  · exact B2006059
  · exact B2006063
  · exact B2006067
  · exact B2006071
  · exact B2006075
  · exact B2006079
  · exact B2006083
  · exact B2006087
  · exact B2006091
  · exact B2006095
  · exact B2006099
  · exact B2006103
  · exact B2006107
  · exact B2006111
  · exact B2006115
  · exact B2006119
  · exact B2006123
  · exact B2006127
  · exact B2006131
  · exact B2006135
  · exact B2006139
  · exact B2006143
  · exact B2006147
  · exact B2006151
  · exact B2006155
  · exact B2006159
  · exact B2006163
  · exact B2006167
  · exact B2006171
  · exact B2006175
  · exact B2006179
  · exact B2006183
  · exact B2006187
  · exact B2006191
  · exact B2006195
  · exact B2006199
  · exact B2006203
  · exact B2006207
  · exact B2006211
  · exact B2006215
  · exact B2006219
  · exact B2006223
  · exact B2006227
  · exact B2006231
  · exact B2006235
  · exact B2006239
  · exact B2006243
  · exact B2006247
  · exact B2006251
  · exact B2006255
  · exact B2006259
  · exact B2006263
  · exact B2006267
  · exact B2006271
  · exact B2006275
  · exact B2006279
  · exact B2006283
  · exact B2006287
  · exact B2006291
  · exact B2006295
  · exact B2006299
  · exact B2006303
  · exact B2006307
  · exact B2006311
  · exact B2006315
  · exact B2006319
  · exact B2006323
  · exact B2006327
  · exact B2006331
  · exact B2006335
  · exact B2006339
  · exact B2006343
  · exact B2006347
  · exact B2006351
  · exact B2006355
  · exact B2006359
  · exact B2006363
  · exact B2006367
  · exact B2006371
  · exact B2006375
  · exact B2006379
  · exact B2006383
  · exact B2006387
  · exact B2006391
  · exact B2006395
  · exact B2006399
  · exact B2006403
  · exact B2006407
  · exact B2006411
  · exact B2006415
  · exact B2006419
  · exact B2006423
  · exact B2006427
  · exact B2006431
  · exact B2006435
  · exact B2006439
  · exact B2006443
  · exact B2006447
  · exact B2006451
  · exact B2006455
  · exact B2006459
  · exact B2006463
  · exact B2006467
  · exact B2006471
  · exact B2006475
  · exact B2006479
  · exact B2006483
  · exact B2006487
  · exact B2006491
  · exact B2006495
  · exact B2006499
  · exact B2006503
  · exact B2006507
  · exact B2006511
  · exact B2006515
  · exact B2006519
  · exact B2006523
  · exact B2006527
  · exact B2006531
  · exact B2006535
  · exact B2006539
  · exact B2006543
  · exact B2006547
  · exact B2006551
  · exact B2006555
  · exact B2006559
  · exact B2006563
  · exact B2006567
  · exact B2006571
  · exact B2006575
  · exact B2006579
  · exact B2006583
  · exact B2006587
  · exact B2006591
  · exact B2006595
  · exact B2006599
  · exact B2006603
  · exact B2006607
  · exact B2006611
  · exact B2006615
  · exact B2006619
  · exact B2006623
  · exact B2006627
  · exact B2006631
  · exact B2006635
  · exact B2006639
  · exact B2006643
  · exact B2006647
  · exact B2006651
  · exact B2006655
  · exact B2006659
  · exact B2006663
  · exact B2006667
  · exact B2006671
  · exact B2006675
  · exact B2006679
  · exact B2006683
  · exact B2006687
  · exact B2006691
  · exact B2006695
  · exact B2006699
  · exact B2006703
  · exact B2006707
  · exact B2006711
  · exact B2006715
  · exact B2006719
  · exact B2006723
  · exact B2006727
  · exact B2006731
  · exact B2006735
  · exact B2006739
  · exact B2006743
  · exact B2006747
  · exact B2006751
  · exact B2006755
  · exact B2006759
  · exact B2006763
  · exact B2006767
  · exact B2006771
  · exact B2006775
  · exact B2006779
  · exact B2006783
  · exact B2006787
  · exact B2006791
  · exact B2006795
  · exact B2006799
  · exact B2006803
  · exact B2006807
  · exact B2006811
  · exact B2006815
  · exact B2006819
  · exact B2006823
  · exact B2006827
  · exact B2006831
  · exact B2006835
  · exact B2006839
  · exact B2006843
  · exact B2006847
  · exact B2006851
  · exact B2006855
  · exact B2006859
  · exact B2006863
  · exact B2006867
  · exact B2006871
  · exact B2006875
  · exact B2006879
  · exact B2006883
  · exact B2006887
  · exact B2006891
  · exact B2006895
  · exact B2006899
  · exact B2006903
  · exact B2006907
  · exact B2006911
  · exact B2006915
  · exact B2006919
  · exact B2006923
  · exact B2006927
  · exact B2006931
  · exact B2006935
  · exact B2006939
  · exact B2006943
  · exact B2006947
  · exact B2006951
  · exact B2006955
  · exact B2006959
  · exact B2006963
  · exact B2006967
  · exact B2006971
  · exact B2006975
  · exact B2006979
  · exact B2006983
  · exact B2006987
  · exact B2006991
  · exact B2006995
  · exact B2006999
  · exact B2007003
  · exact B2007007
  · exact B2007011
  · exact B2007015
  · exact B2007019
  · exact B2007023
  · exact B2007027
  · exact B2007031
  · exact B2007035
  · exact B2007039
  · exact B2007043
  · exact B2007047
  · exact B2007051
  · exact B2007055
  · exact B2007059
  · exact B2007063
  · exact B2007067
  · exact B2007071
  · exact B2007075
  · exact B2007079
  · exact B2007083
  · exact B2007087
  · exact B2007091
  · exact B2007095
  · exact B2007099
  · exact B2007103
  · exact B2007107
  · exact B2007111
  · exact B2007115
  · exact B2007119
  · exact B2007123
  · exact B2007127
  · exact B2007131
  · exact B2007135
  · exact B2007139
  · exact B2007143
  · exact B2007147
  · exact B2007151
  · exact B2007155
  · exact B2007159
  · exact B2007163
  · exact B2007167
  · exact B2007171
  · exact B2007175
  · exact B2007179
  · exact B2007183
  · exact B2007187
  · exact B2007191
  · exact B2007195
  · exact B2007199
  · exact B2007203
  · exact B2007207
  · exact B2007211
  · exact B2007215
  · exact B2007219
  · exact B2007223
  · exact B2007227
  · exact B2007231
  · exact B2007235
  · exact B2007239
  · exact B2007243
  · exact B2007247
  · exact B2007251
  · exact B2007255
  · exact B2007259
  · exact B2007263
  · exact B2007267
  · exact B2007271
  · exact B2007275
  · exact B2007279
  · exact B2007283
  · exact B2007287
  · exact B2007291
  · exact B2007295
  · exact B2007299
  · exact B2007303
  · exact B2007307
  · exact B2007311
  · exact B2007315
  · exact B2007319
  · exact B2007323
  · exact B2007327
  · exact B2007331
  · exact B2007335
  · exact B2007339
  · exact B2007343
  · exact B2007347
  · exact B2007351
  · exact B2007355
  · exact B2007359
  · exact B2007363
  · exact B2007367
  · exact B2007371
  · exact B2007375
  · exact B2007379
  · exact B2007383
  · exact B2007387
  · exact B2007391
  · exact B2007395
  · exact B2007399
  · exact B2007403
  · exact B2007407
  · exact B2007411
  · exact B2007415
  · exact B2007419
  · exact B2007423
  · exact B2007427
  · exact B2007431
  · exact B2007435
theorem solution (m : ℕ) (hlo : 2005435 ≤ m) (hhi : m ≤ 2007435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 501358 ≤ j := by omega
    have hj2 : j ≤ 501858 := by omega
    have hb : Blo 2005435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
