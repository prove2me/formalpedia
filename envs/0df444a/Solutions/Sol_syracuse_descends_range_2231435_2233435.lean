-- Prove2me | solution 1 for syracuse_descends_range_2231435_2233435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:49.990781+00:00
-- url     : https://prove2.me/submissions/b66eee4f-3258-4752-83d4-241a98067ed2

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

theorem B2510365 : Blo 2231435 2510365 := bbase (se 3 (by rfl) ⟨470693, by rfl⟩ : syracuseStep 2510365 = 941387) (by norm_num)
theorem B3347153 : Blo 2231435 3347153 := bstep (se 2 (by rfl) ⟨1255182, by rfl⟩ : syracuseStep 3347153 = 2510365) B2510365
theorem B2231435 : Blo 2231435 2231435 := bstep (se 1 (by rfl) ⟨1673576, by rfl⟩ : syracuseStep 2231435 = 3347153) B3347153
theorem B7531109 : Blo 2231435 7531109 := bbase (se 4 (by rfl) ⟨706041, by rfl⟩ : syracuseStep 7531109 = 1412083) (by norm_num)
theorem B5020739 : Blo 2231435 5020739 := bstep (se 1 (by rfl) ⟨3765554, by rfl⟩ : syracuseStep 5020739 = 7531109) B7531109
theorem B3347159 : Blo 2231435 3347159 := bstep (se 1 (by rfl) ⟨2510369, by rfl⟩ : syracuseStep 3347159 = 5020739) B5020739
theorem B2231439 : Blo 2231435 2231439 := bstep (se 1 (by rfl) ⟨1673579, by rfl⟩ : syracuseStep 2231439 = 3347159) B3347159
theorem B3347165 : Blo 2231435 3347165 := bbase (se 3 (by rfl) ⟨627593, by rfl⟩ : syracuseStep 3347165 = 1255187) (by norm_num)
theorem B2231443 : Blo 2231435 2231443 := bstep (se 1 (by rfl) ⟨1673582, by rfl⟩ : syracuseStep 2231443 = 3347165) B3347165
theorem B5020757 : Blo 2231435 5020757 := bbase (se 8 (by rfl) ⟨29418, by rfl⟩ : syracuseStep 5020757 = 58837) (by norm_num)
theorem B3347171 : Blo 2231435 3347171 := bstep (se 1 (by rfl) ⟨2510378, by rfl⟩ : syracuseStep 3347171 = 5020757) B5020757
theorem B2231447 : Blo 2231435 2231447 := bstep (se 1 (by rfl) ⟨1673585, by rfl⟩ : syracuseStep 2231447 = 3347171) B3347171
theorem B9171029 : Blo 2231435 9171029 := bbase (se 8 (by rfl) ⟨53736, by rfl⟩ : syracuseStep 9171029 = 107473) (by norm_num)
theorem B24456077 : Blo 2231435 24456077 := bstep (se 3 (by rfl) ⟨4585514, by rfl⟩ : syracuseStep 24456077 = 9171029) B9171029
theorem B16304051 : Blo 2231435 16304051 := bstep (se 1 (by rfl) ⟨12228038, by rfl⟩ : syracuseStep 16304051 = 24456077) B24456077
theorem B43477469 : Blo 2231435 43477469 := bstep (se 3 (by rfl) ⟨8152025, by rfl⟩ : syracuseStep 43477469 = 16304051) B16304051
theorem B28984979 : Blo 2231435 28984979 := bstep (se 1 (by rfl) ⟨21738734, by rfl⟩ : syracuseStep 28984979 = 43477469) B43477469
theorem B19323319 : Blo 2231435 19323319 := bstep (se 1 (by rfl) ⟨14492489, by rfl⟩ : syracuseStep 19323319 = 28984979) B28984979
theorem B25764425 : Blo 2231435 25764425 := bstep (se 2 (by rfl) ⟨9661659, by rfl⟩ : syracuseStep 25764425 = 19323319) B19323319
theorem B17176283 : Blo 2231435 17176283 := bstep (se 1 (by rfl) ⟨12882212, by rfl⟩ : syracuseStep 17176283 = 25764425) B25764425
theorem B11450855 : Blo 2231435 11450855 := bstep (se 1 (by rfl) ⟨8588141, by rfl⟩ : syracuseStep 11450855 = 17176283) B17176283
theorem B30535613 : Blo 2231435 30535613 := bstep (se 3 (by rfl) ⟨5725427, by rfl⟩ : syracuseStep 30535613 = 11450855) B11450855
theorem B20357075 : Blo 2231435 20357075 := bstep (se 1 (by rfl) ⟨15267806, by rfl⟩ : syracuseStep 20357075 = 30535613) B30535613
theorem B13571383 : Blo 2231435 13571383 := bstep (se 1 (by rfl) ⟨10178537, by rfl⟩ : syracuseStep 13571383 = 20357075) B20357075
theorem B18095177 : Blo 2231435 18095177 := bstep (se 2 (by rfl) ⟨6785691, by rfl⟩ : syracuseStep 18095177 = 13571383) B13571383
theorem B12063451 : Blo 2231435 12063451 := bstep (se 1 (by rfl) ⟨9047588, by rfl⟩ : syracuseStep 12063451 = 18095177) B18095177
theorem B16084601 : Blo 2231435 16084601 := bstep (se 2 (by rfl) ⟨6031725, by rfl⟩ : syracuseStep 16084601 = 12063451) B12063451
theorem B10723067 : Blo 2231435 10723067 := bstep (se 1 (by rfl) ⟨8042300, by rfl⟩ : syracuseStep 10723067 = 16084601) B16084601
theorem B7148711 : Blo 2231435 7148711 := bstep (se 1 (by rfl) ⟨5361533, by rfl⟩ : syracuseStep 7148711 = 10723067) B10723067
theorem B4765807 : Blo 2231435 4765807 := bstep (se 1 (by rfl) ⟨3574355, by rfl⟩ : syracuseStep 4765807 = 7148711) B7148711
theorem B6354409 : Blo 2231435 6354409 := bstep (se 2 (by rfl) ⟨2382903, by rfl⟩ : syracuseStep 6354409 = 4765807) B4765807
theorem B8472545 : Blo 2231435 8472545 := bstep (se 2 (by rfl) ⟨3177204, by rfl⟩ : syracuseStep 8472545 = 6354409) B6354409
theorem B5648363 : Blo 2231435 5648363 := bstep (se 1 (by rfl) ⟨4236272, by rfl⟩ : syracuseStep 5648363 = 8472545) B8472545
theorem B3765575 : Blo 2231435 3765575 := bstep (se 1 (by rfl) ⟨2824181, by rfl⟩ : syracuseStep 3765575 = 5648363) B5648363
theorem B2510383 : Blo 2231435 2510383 := bstep (se 1 (by rfl) ⟨1882787, by rfl⟩ : syracuseStep 2510383 = 3765575) B3765575
theorem B3347177 : Blo 2231435 3347177 := bstep (se 2 (by rfl) ⟨1255191, by rfl⟩ : syracuseStep 3347177 = 2510383) B2510383
theorem B2231451 : Blo 2231435 2231451 := bstep (se 1 (by rfl) ⟨1673588, by rfl⟩ : syracuseStep 2231451 = 3347177) B3347177
theorem B5089277 : Blo 2231435 5089277 := bbase (se 3 (by rfl) ⟨954239, by rfl⟩ : syracuseStep 5089277 = 1908479) (by norm_num)
theorem B3392851 : Blo 2231435 3392851 := bstep (se 1 (by rfl) ⟨2544638, by rfl⟩ : syracuseStep 3392851 = 5089277) B5089277
theorem B4523801 : Blo 2231435 4523801 := bstep (se 2 (by rfl) ⟨1696425, by rfl⟩ : syracuseStep 4523801 = 3392851) B3392851
theorem B48253877 : Blo 2231435 48253877 := bstep (se 5 (by rfl) ⟨2261900, by rfl⟩ : syracuseStep 48253877 = 4523801) B4523801
theorem B32169251 : Blo 2231435 32169251 := bstep (se 1 (by rfl) ⟨24126938, by rfl⟩ : syracuseStep 32169251 = 48253877) B48253877
theorem B21446167 : Blo 2231435 21446167 := bstep (se 1 (by rfl) ⟨16084625, by rfl⟩ : syracuseStep 21446167 = 32169251) B32169251
theorem B28594889 : Blo 2231435 28594889 := bstep (se 2 (by rfl) ⟨10723083, by rfl⟩ : syracuseStep 28594889 = 21446167) B21446167
theorem B19063259 : Blo 2231435 19063259 := bstep (se 1 (by rfl) ⟨14297444, by rfl⟩ : syracuseStep 19063259 = 28594889) B28594889
theorem B12708839 : Blo 2231435 12708839 := bstep (se 1 (by rfl) ⟨9531629, by rfl⟩ : syracuseStep 12708839 = 19063259) B19063259
theorem B8472559 : Blo 2231435 8472559 := bstep (se 1 (by rfl) ⟨6354419, by rfl⟩ : syracuseStep 8472559 = 12708839) B12708839
theorem B11296745 : Blo 2231435 11296745 := bstep (se 2 (by rfl) ⟨4236279, by rfl⟩ : syracuseStep 11296745 = 8472559) B8472559
theorem B7531163 : Blo 2231435 7531163 := bstep (se 1 (by rfl) ⟨5648372, by rfl⟩ : syracuseStep 7531163 = 11296745) B11296745
theorem B5020775 : Blo 2231435 5020775 := bstep (se 1 (by rfl) ⟨3765581, by rfl⟩ : syracuseStep 5020775 = 7531163) B7531163
theorem B3347183 : Blo 2231435 3347183 := bstep (se 1 (by rfl) ⟨2510387, by rfl⟩ : syracuseStep 3347183 = 5020775) B5020775
theorem B2231455 : Blo 2231435 2231455 := bstep (se 1 (by rfl) ⟨1673591, by rfl⟩ : syracuseStep 2231455 = 3347183) B3347183
theorem B3347189 : Blo 2231435 3347189 := bbase (se 5 (by rfl) ⟨156899, by rfl⟩ : syracuseStep 3347189 = 313799) (by norm_num)
theorem B2231459 : Blo 2231435 2231459 := bstep (se 1 (by rfl) ⟨1673594, by rfl⟩ : syracuseStep 2231459 = 3347189) B3347189
theorem B2680781 : Blo 2231435 2680781 := bbase (se 3 (by rfl) ⟨502646, by rfl⟩ : syracuseStep 2680781 = 1005293) (by norm_num)
theorem B7148749 : Blo 2231435 7148749 := bstep (se 3 (by rfl) ⟨1340390, by rfl⟩ : syracuseStep 7148749 = 2680781) B2680781
theorem B9531665 : Blo 2231435 9531665 := bstep (se 2 (by rfl) ⟨3574374, by rfl⟩ : syracuseStep 9531665 = 7148749) B7148749
theorem B6354443 : Blo 2231435 6354443 := bstep (se 1 (by rfl) ⟨4765832, by rfl⟩ : syracuseStep 6354443 = 9531665) B9531665
theorem B4236295 : Blo 2231435 4236295 := bstep (se 1 (by rfl) ⟨3177221, by rfl⟩ : syracuseStep 4236295 = 6354443) B6354443
theorem B5648393 : Blo 2231435 5648393 := bstep (se 2 (by rfl) ⟨2118147, by rfl⟩ : syracuseStep 5648393 = 4236295) B4236295
theorem B3765595 : Blo 2231435 3765595 := bstep (se 1 (by rfl) ⟨2824196, by rfl⟩ : syracuseStep 3765595 = 5648393) B5648393
theorem B5020793 : Blo 2231435 5020793 := bstep (se 2 (by rfl) ⟨1882797, by rfl⟩ : syracuseStep 5020793 = 3765595) B3765595
theorem B3347195 : Blo 2231435 3347195 := bstep (se 1 (by rfl) ⟨2510396, by rfl⟩ : syracuseStep 3347195 = 5020793) B5020793
theorem B2231463 : Blo 2231435 2231463 := bstep (se 1 (by rfl) ⟨1673597, by rfl⟩ : syracuseStep 2231463 = 3347195) B3347195
theorem B2510401 : Blo 2231435 2510401 := bbase (se 2 (by rfl) ⟨941400, by rfl⟩ : syracuseStep 2510401 = 1882801) (by norm_num)
theorem B3347201 : Blo 2231435 3347201 := bstep (se 2 (by rfl) ⟨1255200, by rfl⟩ : syracuseStep 3347201 = 2510401) B2510401
theorem B2231467 : Blo 2231435 2231467 := bstep (se 1 (by rfl) ⟨1673600, by rfl⟩ : syracuseStep 2231467 = 3347201) B3347201
theorem B5648413 : Blo 2231435 5648413 := bbase (se 3 (by rfl) ⟨1059077, by rfl⟩ : syracuseStep 5648413 = 2118155) (by norm_num)
theorem B7531217 : Blo 2231435 7531217 := bstep (se 2 (by rfl) ⟨2824206, by rfl⟩ : syracuseStep 7531217 = 5648413) B5648413
theorem B5020811 : Blo 2231435 5020811 := bstep (se 1 (by rfl) ⟨3765608, by rfl⟩ : syracuseStep 5020811 = 7531217) B7531217
theorem B3347207 : Blo 2231435 3347207 := bstep (se 1 (by rfl) ⟨2510405, by rfl⟩ : syracuseStep 3347207 = 5020811) B5020811
theorem B2231471 : Blo 2231435 2231471 := bstep (se 1 (by rfl) ⟨1673603, by rfl⟩ : syracuseStep 2231471 = 3347207) B3347207
theorem B3347213 : Blo 2231435 3347213 := bbase (se 3 (by rfl) ⟨627602, by rfl⟩ : syracuseStep 3347213 = 1255205) (by norm_num)
theorem B2231475 : Blo 2231435 2231475 := bstep (se 1 (by rfl) ⟨1673606, by rfl⟩ : syracuseStep 2231475 = 3347213) B3347213
theorem B5020829 : Blo 2231435 5020829 := bbase (se 3 (by rfl) ⟨941405, by rfl⟩ : syracuseStep 5020829 = 1882811) (by norm_num)
theorem B3347219 : Blo 2231435 3347219 := bstep (se 1 (by rfl) ⟨2510414, by rfl⟩ : syracuseStep 3347219 = 5020829) B5020829
theorem B2231479 : Blo 2231435 2231479 := bstep (se 1 (by rfl) ⟨1673609, by rfl⟩ : syracuseStep 2231479 = 3347219) B3347219
theorem B3765629 : Blo 2231435 3765629 := bbase (se 3 (by rfl) ⟨706055, by rfl⟩ : syracuseStep 3765629 = 1412111) (by norm_num)
theorem B2510419 : Blo 2231435 2510419 := bstep (se 1 (by rfl) ⟨1882814, by rfl⟩ : syracuseStep 2510419 = 3765629) B3765629
theorem B3347225 : Blo 2231435 3347225 := bstep (se 2 (by rfl) ⟨1255209, by rfl⟩ : syracuseStep 3347225 = 2510419) B2510419
theorem B2231483 : Blo 2231435 2231483 := bstep (se 1 (by rfl) ⟨1673612, by rfl⟩ : syracuseStep 2231483 = 3347225) B3347225
theorem B19854517 : Blo 2231435 19854517 := bbase (se 5 (by rfl) ⟨930680, by rfl⟩ : syracuseStep 19854517 = 1861361) (by norm_num)
theorem B26472689 : Blo 2231435 26472689 := bstep (se 2 (by rfl) ⟨9927258, by rfl⟩ : syracuseStep 26472689 = 19854517) B19854517
theorem B17648459 : Blo 2231435 17648459 := bstep (se 1 (by rfl) ⟨13236344, by rfl⟩ : syracuseStep 17648459 = 26472689) B26472689
theorem B11765639 : Blo 2231435 11765639 := bstep (se 1 (by rfl) ⟨8824229, by rfl⟩ : syracuseStep 11765639 = 17648459) B17648459
theorem B7843759 : Blo 2231435 7843759 := bstep (se 1 (by rfl) ⟨5882819, by rfl⟩ : syracuseStep 7843759 = 11765639) B11765639
theorem B41833381 : Blo 2231435 41833381 := bstep (se 4 (by rfl) ⟨3921879, by rfl⟩ : syracuseStep 41833381 = 7843759) B7843759
theorem B55777841 : Blo 2231435 55777841 := bstep (se 2 (by rfl) ⟨20916690, by rfl⟩ : syracuseStep 55777841 = 41833381) B41833381
theorem B37185227 : Blo 2231435 37185227 := bstep (se 1 (by rfl) ⟨27888920, by rfl⟩ : syracuseStep 37185227 = 55777841) B55777841
theorem B24790151 : Blo 2231435 24790151 := bstep (se 1 (by rfl) ⟨18592613, by rfl⟩ : syracuseStep 24790151 = 37185227) B37185227
theorem B16526767 : Blo 2231435 16526767 := bstep (se 1 (by rfl) ⟨12395075, by rfl⟩ : syracuseStep 16526767 = 24790151) B24790151
theorem B22035689 : Blo 2231435 22035689 := bstep (se 2 (by rfl) ⟨8263383, by rfl⟩ : syracuseStep 22035689 = 16526767) B16526767
theorem B14690459 : Blo 2231435 14690459 := bstep (se 1 (by rfl) ⟨11017844, by rfl⟩ : syracuseStep 14690459 = 22035689) B22035689
theorem B9793639 : Blo 2231435 9793639 := bstep (se 1 (by rfl) ⟨7345229, by rfl⟩ : syracuseStep 9793639 = 14690459) B14690459
theorem B13058185 : Blo 2231435 13058185 := bstep (se 2 (by rfl) ⟨4896819, by rfl⟩ : syracuseStep 13058185 = 9793639) B9793639
theorem B17410913 : Blo 2231435 17410913 := bstep (se 2 (by rfl) ⟨6529092, by rfl⟩ : syracuseStep 17410913 = 13058185) B13058185
theorem B11607275 : Blo 2231435 11607275 := bstep (se 1 (by rfl) ⟨8705456, by rfl⟩ : syracuseStep 11607275 = 17410913) B17410913
theorem B7738183 : Blo 2231435 7738183 := bstep (se 1 (by rfl) ⟨5803637, by rfl⟩ : syracuseStep 7738183 = 11607275) B11607275
theorem B41270309 : Blo 2231435 41270309 := bstep (se 4 (by rfl) ⟨3869091, by rfl⟩ : syracuseStep 41270309 = 7738183) B7738183
theorem B27513539 : Blo 2231435 27513539 := bstep (se 1 (by rfl) ⟨20635154, by rfl⟩ : syracuseStep 27513539 = 41270309) B41270309
theorem B18342359 : Blo 2231435 18342359 := bstep (se 1 (by rfl) ⟨13756769, by rfl⟩ : syracuseStep 18342359 = 27513539) B27513539
theorem B12228239 : Blo 2231435 12228239 := bstep (se 1 (by rfl) ⟨9171179, by rfl⟩ : syracuseStep 12228239 = 18342359) B18342359
theorem B8152159 : Blo 2231435 8152159 := bstep (se 1 (by rfl) ⟨6114119, by rfl⟩ : syracuseStep 8152159 = 12228239) B12228239
theorem B10869545 : Blo 2231435 10869545 := bstep (se 2 (by rfl) ⟨4076079, by rfl⟩ : syracuseStep 10869545 = 8152159) B8152159
theorem B7246363 : Blo 2231435 7246363 := bstep (se 1 (by rfl) ⟨5434772, by rfl⟩ : syracuseStep 7246363 = 10869545) B10869545
theorem B9661817 : Blo 2231435 9661817 := bstep (se 2 (by rfl) ⟨3623181, by rfl⟩ : syracuseStep 9661817 = 7246363) B7246363
theorem B6441211 : Blo 2231435 6441211 := bstep (se 1 (by rfl) ⟨4830908, by rfl⟩ : syracuseStep 6441211 = 9661817) B9661817
theorem B8588281 : Blo 2231435 8588281 := bstep (se 2 (by rfl) ⟨3220605, by rfl⟩ : syracuseStep 8588281 = 6441211) B6441211
theorem B11451041 : Blo 2231435 11451041 := bstep (se 2 (by rfl) ⟨4294140, by rfl⟩ : syracuseStep 11451041 = 8588281) B8588281
theorem B7634027 : Blo 2231435 7634027 := bstep (se 1 (by rfl) ⟨5725520, by rfl⟩ : syracuseStep 7634027 = 11451041) B11451041
theorem B5089351 : Blo 2231435 5089351 := bstep (se 1 (by rfl) ⟨3817013, by rfl⟩ : syracuseStep 5089351 = 7634027) B7634027
theorem B6785801 : Blo 2231435 6785801 := bstep (se 2 (by rfl) ⟨2544675, by rfl⟩ : syracuseStep 6785801 = 5089351) B5089351
theorem B4523867 : Blo 2231435 4523867 := bstep (se 1 (by rfl) ⟨3392900, by rfl⟩ : syracuseStep 4523867 = 6785801) B6785801
theorem B3015911 : Blo 2231435 3015911 := bstep (se 1 (by rfl) ⟨2261933, by rfl⟩ : syracuseStep 3015911 = 4523867) B4523867
theorem B8042429 : Blo 2231435 8042429 := bstep (se 3 (by rfl) ⟨1507955, by rfl⟩ : syracuseStep 8042429 = 3015911) B3015911
theorem B5361619 : Blo 2231435 5361619 := bstep (se 1 (by rfl) ⟨4021214, by rfl⟩ : syracuseStep 5361619 = 8042429) B8042429
theorem B7148825 : Blo 2231435 7148825 := bstep (se 2 (by rfl) ⟨2680809, by rfl⟩ : syracuseStep 7148825 = 5361619) B5361619
theorem B4765883 : Blo 2231435 4765883 := bstep (se 1 (by rfl) ⟨3574412, by rfl⟩ : syracuseStep 4765883 = 7148825) B7148825
theorem B12709021 : Blo 2231435 12709021 := bstep (se 3 (by rfl) ⟨2382941, by rfl⟩ : syracuseStep 12709021 = 4765883) B4765883
theorem B16945361 : Blo 2231435 16945361 := bstep (se 2 (by rfl) ⟨6354510, by rfl⟩ : syracuseStep 16945361 = 12709021) B12709021
theorem B11296907 : Blo 2231435 11296907 := bstep (se 1 (by rfl) ⟨8472680, by rfl⟩ : syracuseStep 11296907 = 16945361) B16945361
theorem B7531271 : Blo 2231435 7531271 := bstep (se 1 (by rfl) ⟨5648453, by rfl⟩ : syracuseStep 7531271 = 11296907) B11296907
theorem B5020847 : Blo 2231435 5020847 := bstep (se 1 (by rfl) ⟨3765635, by rfl⟩ : syracuseStep 5020847 = 7531271) B7531271
theorem B3347231 : Blo 2231435 3347231 := bstep (se 1 (by rfl) ⟨2510423, by rfl⟩ : syracuseStep 3347231 = 5020847) B5020847
theorem B2231487 : Blo 2231435 2231487 := bstep (se 1 (by rfl) ⟨1673615, by rfl⟩ : syracuseStep 2231487 = 3347231) B3347231
theorem B3347237 : Blo 2231435 3347237 := bbase (se 4 (by rfl) ⟨313803, by rfl⟩ : syracuseStep 3347237 = 627607) (by norm_num)
theorem B2231491 : Blo 2231435 2231491 := bstep (se 1 (by rfl) ⟨1673618, by rfl⟩ : syracuseStep 2231491 = 3347237) B3347237
theorem B2824237 : Blo 2231435 2824237 := bbase (se 3 (by rfl) ⟨529544, by rfl⟩ : syracuseStep 2824237 = 1059089) (by norm_num)
theorem B3765649 : Blo 2231435 3765649 := bstep (se 2 (by rfl) ⟨1412118, by rfl⟩ : syracuseStep 3765649 = 2824237) B2824237
theorem B5020865 : Blo 2231435 5020865 := bstep (se 2 (by rfl) ⟨1882824, by rfl⟩ : syracuseStep 5020865 = 3765649) B3765649
theorem B3347243 : Blo 2231435 3347243 := bstep (se 1 (by rfl) ⟨2510432, by rfl⟩ : syracuseStep 3347243 = 5020865) B5020865
theorem B2231495 : Blo 2231435 2231495 := bstep (se 1 (by rfl) ⟨1673621, by rfl⟩ : syracuseStep 2231495 = 3347243) B3347243
theorem B2510437 : Blo 2231435 2510437 := bbase (se 4 (by rfl) ⟨235353, by rfl⟩ : syracuseStep 2510437 = 470707) (by norm_num)
theorem B3347249 : Blo 2231435 3347249 := bstep (se 2 (by rfl) ⟨1255218, by rfl⟩ : syracuseStep 3347249 = 2510437) B2510437
theorem B2231499 : Blo 2231435 2231499 := bstep (se 1 (by rfl) ⟨1673624, by rfl⟩ : syracuseStep 2231499 = 3347249) B3347249
theorem B11451125 : Blo 2231435 11451125 := bbase (se 5 (by rfl) ⟨536771, by rfl⟩ : syracuseStep 11451125 = 1073543) (by norm_num)
theorem B7634083 : Blo 2231435 7634083 := bstep (se 1 (by rfl) ⟨5725562, by rfl⟩ : syracuseStep 7634083 = 11451125) B11451125
theorem B10178777 : Blo 2231435 10178777 := bstep (se 2 (by rfl) ⟨3817041, by rfl⟩ : syracuseStep 10178777 = 7634083) B7634083
theorem B6785851 : Blo 2231435 6785851 := bstep (se 1 (by rfl) ⟨5089388, by rfl⟩ : syracuseStep 6785851 = 10178777) B10178777
theorem B9047801 : Blo 2231435 9047801 := bstep (se 2 (by rfl) ⟨3392925, by rfl⟩ : syracuseStep 9047801 = 6785851) B6785851
theorem B6031867 : Blo 2231435 6031867 := bstep (se 1 (by rfl) ⟨4523900, by rfl⟩ : syracuseStep 6031867 = 9047801) B9047801
theorem B8042489 : Blo 2231435 8042489 := bstep (se 2 (by rfl) ⟨3015933, by rfl⟩ : syracuseStep 8042489 = 6031867) B6031867
theorem B5361659 : Blo 2231435 5361659 := bstep (se 1 (by rfl) ⟨4021244, by rfl⟩ : syracuseStep 5361659 = 8042489) B8042489
theorem B3574439 : Blo 2231435 3574439 := bstep (se 1 (by rfl) ⟨2680829, by rfl⟩ : syracuseStep 3574439 = 5361659) B5361659
theorem B2382959 : Blo 2231435 2382959 := bstep (se 1 (by rfl) ⟨1787219, by rfl⟩ : syracuseStep 2382959 = 3574439) B3574439
theorem B6354557 : Blo 2231435 6354557 := bstep (se 3 (by rfl) ⟨1191479, by rfl⟩ : syracuseStep 6354557 = 2382959) B2382959
theorem B4236371 : Blo 2231435 4236371 := bstep (se 1 (by rfl) ⟨3177278, by rfl⟩ : syracuseStep 4236371 = 6354557) B6354557
theorem B2824247 : Blo 2231435 2824247 := bstep (se 1 (by rfl) ⟨2118185, by rfl⟩ : syracuseStep 2824247 = 4236371) B4236371
theorem B7531325 : Blo 2231435 7531325 := bstep (se 3 (by rfl) ⟨1412123, by rfl⟩ : syracuseStep 7531325 = 2824247) B2824247
theorem B5020883 : Blo 2231435 5020883 := bstep (se 1 (by rfl) ⟨3765662, by rfl⟩ : syracuseStep 5020883 = 7531325) B7531325
theorem B3347255 : Blo 2231435 3347255 := bstep (se 1 (by rfl) ⟨2510441, by rfl⟩ : syracuseStep 3347255 = 5020883) B5020883
theorem B2231503 : Blo 2231435 2231503 := bstep (se 1 (by rfl) ⟨1673627, by rfl⟩ : syracuseStep 2231503 = 3347255) B3347255
theorem B3347261 : Blo 2231435 3347261 := bbase (se 3 (by rfl) ⟨627611, by rfl⟩ : syracuseStep 3347261 = 1255223) (by norm_num)
theorem B2231507 : Blo 2231435 2231507 := bstep (se 1 (by rfl) ⟨1673630, by rfl⟩ : syracuseStep 2231507 = 3347261) B3347261
theorem B5020901 : Blo 2231435 5020901 := bbase (se 4 (by rfl) ⟨470709, by rfl⟩ : syracuseStep 5020901 = 941419) (by norm_num)
theorem B3347267 : Blo 2231435 3347267 := bstep (se 1 (by rfl) ⟨2510450, by rfl⟩ : syracuseStep 3347267 = 5020901) B5020901
theorem B2231511 : Blo 2231435 2231511 := bstep (se 1 (by rfl) ⟨1673633, by rfl⟩ : syracuseStep 2231511 = 3347267) B3347267
theorem B5648525 : Blo 2231435 5648525 := bbase (se 3 (by rfl) ⟨1059098, by rfl⟩ : syracuseStep 5648525 = 2118197) (by norm_num)
theorem B3765683 : Blo 2231435 3765683 := bstep (se 1 (by rfl) ⟨2824262, by rfl⟩ : syracuseStep 3765683 = 5648525) B5648525
theorem B2510455 : Blo 2231435 2510455 := bstep (se 1 (by rfl) ⟨1882841, by rfl⟩ : syracuseStep 2510455 = 3765683) B3765683
theorem B3347273 : Blo 2231435 3347273 := bstep (se 2 (by rfl) ⟨1255227, by rfl⟩ : syracuseStep 3347273 = 2510455) B2510455
theorem B2231515 : Blo 2231435 2231515 := bstep (se 1 (by rfl) ⟨1673636, by rfl⟩ : syracuseStep 2231515 = 3347273) B3347273
theorem B3177301 : Blo 2231435 3177301 := bbase (se 9 (by rfl) ⟨9308, by rfl⟩ : syracuseStep 3177301 = 18617) (by norm_num)
theorem B4236401 : Blo 2231435 4236401 := bstep (se 2 (by rfl) ⟨1588650, by rfl⟩ : syracuseStep 4236401 = 3177301) B3177301
theorem B11297069 : Blo 2231435 11297069 := bstep (se 3 (by rfl) ⟨2118200, by rfl⟩ : syracuseStep 11297069 = 4236401) B4236401
theorem B7531379 : Blo 2231435 7531379 := bstep (se 1 (by rfl) ⟨5648534, by rfl⟩ : syracuseStep 7531379 = 11297069) B11297069
theorem B5020919 : Blo 2231435 5020919 := bstep (se 1 (by rfl) ⟨3765689, by rfl⟩ : syracuseStep 5020919 = 7531379) B7531379
theorem B3347279 : Blo 2231435 3347279 := bstep (se 1 (by rfl) ⟨2510459, by rfl⟩ : syracuseStep 3347279 = 5020919) B5020919
theorem B2231519 : Blo 2231435 2231519 := bstep (se 1 (by rfl) ⟨1673639, by rfl⟩ : syracuseStep 2231519 = 3347279) B3347279
theorem B3347285 : Blo 2231435 3347285 := bbase (se 9 (by rfl) ⟨9806, by rfl⟩ : syracuseStep 3347285 = 19613) (by norm_num)
theorem B2231523 : Blo 2231435 2231523 := bstep (se 1 (by rfl) ⟨1673642, by rfl⟩ : syracuseStep 2231523 = 3347285) B3347285
theorem B3574477 : Blo 2231435 3574477 := bbase (se 3 (by rfl) ⟨670214, by rfl⟩ : syracuseStep 3574477 = 1340429) (by norm_num)
theorem B4765969 : Blo 2231435 4765969 := bstep (se 2 (by rfl) ⟨1787238, by rfl⟩ : syracuseStep 4765969 = 3574477) B3574477
theorem B6354625 : Blo 2231435 6354625 := bstep (se 2 (by rfl) ⟨2382984, by rfl⟩ : syracuseStep 6354625 = 4765969) B4765969
theorem B8472833 : Blo 2231435 8472833 := bstep (se 2 (by rfl) ⟨3177312, by rfl⟩ : syracuseStep 8472833 = 6354625) B6354625
theorem B5648555 : Blo 2231435 5648555 := bstep (se 1 (by rfl) ⟨4236416, by rfl⟩ : syracuseStep 5648555 = 8472833) B8472833
theorem B3765703 : Blo 2231435 3765703 := bstep (se 1 (by rfl) ⟨2824277, by rfl⟩ : syracuseStep 3765703 = 5648555) B5648555
theorem B5020937 : Blo 2231435 5020937 := bstep (se 2 (by rfl) ⟨1882851, by rfl⟩ : syracuseStep 5020937 = 3765703) B3765703
theorem B3347291 : Blo 2231435 3347291 := bstep (se 1 (by rfl) ⟨2510468, by rfl⟩ : syracuseStep 3347291 = 5020937) B5020937
theorem B2231527 : Blo 2231435 2231527 := bstep (se 1 (by rfl) ⟨1673645, by rfl⟩ : syracuseStep 2231527 = 3347291) B3347291
theorem B2510473 : Blo 2231435 2510473 := bbase (se 2 (by rfl) ⟨941427, by rfl⟩ : syracuseStep 2510473 = 1882855) (by norm_num)
theorem B3347297 : Blo 2231435 3347297 := bstep (se 2 (by rfl) ⟨1255236, by rfl⟩ : syracuseStep 3347297 = 2510473) B2510473
theorem B2231531 : Blo 2231435 2231531 := bstep (se 1 (by rfl) ⟨1673648, by rfl⟩ : syracuseStep 2231531 = 3347297) B3347297
theorem B2862821 : Blo 2231435 2862821 := bbase (se 4 (by rfl) ⟨268389, by rfl⟩ : syracuseStep 2862821 = 536779) (by norm_num)
theorem B7634189 : Blo 2231435 7634189 := bstep (se 3 (by rfl) ⟨1431410, by rfl⟩ : syracuseStep 7634189 = 2862821) B2862821
theorem B20357837 : Blo 2231435 20357837 := bstep (se 3 (by rfl) ⟨3817094, by rfl⟩ : syracuseStep 20357837 = 7634189) B7634189
theorem B13571891 : Blo 2231435 13571891 := bstep (se 1 (by rfl) ⟨10178918, by rfl⟩ : syracuseStep 13571891 = 20357837) B20357837
theorem B9047927 : Blo 2231435 9047927 := bstep (se 1 (by rfl) ⟨6785945, by rfl⟩ : syracuseStep 9047927 = 13571891) B13571891
theorem B6031951 : Blo 2231435 6031951 := bstep (se 1 (by rfl) ⟨4523963, by rfl⟩ : syracuseStep 6031951 = 9047927) B9047927
theorem B32170405 : Blo 2231435 32170405 := bstep (se 4 (by rfl) ⟨3015975, by rfl⟩ : syracuseStep 32170405 = 6031951) B6031951
theorem B42893873 : Blo 2231435 42893873 := bstep (se 2 (by rfl) ⟨16085202, by rfl⟩ : syracuseStep 42893873 = 32170405) B32170405
theorem B28595915 : Blo 2231435 28595915 := bstep (se 1 (by rfl) ⟨21446936, by rfl⟩ : syracuseStep 28595915 = 42893873) B42893873
theorem B19063943 : Blo 2231435 19063943 := bstep (se 1 (by rfl) ⟨14297957, by rfl⟩ : syracuseStep 19063943 = 28595915) B28595915
theorem B12709295 : Blo 2231435 12709295 := bstep (se 1 (by rfl) ⟨9531971, by rfl⟩ : syracuseStep 12709295 = 19063943) B19063943
theorem B8472863 : Blo 2231435 8472863 := bstep (se 1 (by rfl) ⟨6354647, by rfl⟩ : syracuseStep 8472863 = 12709295) B12709295
theorem B5648575 : Blo 2231435 5648575 := bstep (se 1 (by rfl) ⟨4236431, by rfl⟩ : syracuseStep 5648575 = 8472863) B8472863
theorem B7531433 : Blo 2231435 7531433 := bstep (se 2 (by rfl) ⟨2824287, by rfl⟩ : syracuseStep 7531433 = 5648575) B5648575
theorem B5020955 : Blo 2231435 5020955 := bstep (se 1 (by rfl) ⟨3765716, by rfl⟩ : syracuseStep 5020955 = 7531433) B7531433
theorem B3347303 : Blo 2231435 3347303 := bstep (se 1 (by rfl) ⟨2510477, by rfl⟩ : syracuseStep 3347303 = 5020955) B5020955
theorem B2231535 : Blo 2231435 2231535 := bstep (se 1 (by rfl) ⟨1673651, by rfl⟩ : syracuseStep 2231535 = 3347303) B3347303
theorem B3347309 : Blo 2231435 3347309 := bbase (se 3 (by rfl) ⟨627620, by rfl⟩ : syracuseStep 3347309 = 1255241) (by norm_num)
theorem B2231539 : Blo 2231435 2231539 := bstep (se 1 (by rfl) ⟨1673654, by rfl⟩ : syracuseStep 2231539 = 3347309) B3347309
theorem B5020973 : Blo 2231435 5020973 := bbase (se 3 (by rfl) ⟨941432, by rfl⟩ : syracuseStep 5020973 = 1882865) (by norm_num)
theorem B3347315 : Blo 2231435 3347315 := bstep (se 1 (by rfl) ⟨2510486, by rfl⟩ : syracuseStep 3347315 = 5020973) B5020973
theorem B2231543 : Blo 2231435 2231543 := bstep (se 1 (by rfl) ⟨1673657, by rfl⟩ : syracuseStep 2231543 = 3347315) B3347315
theorem B18095957 : Blo 2231435 18095957 := bbase (se 9 (by rfl) ⟨53015, by rfl⟩ : syracuseStep 18095957 = 106031) (by norm_num)
theorem B12063971 : Blo 2231435 12063971 := bstep (se 1 (by rfl) ⟨9047978, by rfl⟩ : syracuseStep 12063971 = 18095957) B18095957
theorem B8042647 : Blo 2231435 8042647 := bstep (se 1 (by rfl) ⟨6031985, by rfl⟩ : syracuseStep 8042647 = 12063971) B12063971
theorem B10723529 : Blo 2231435 10723529 := bstep (se 2 (by rfl) ⟨4021323, by rfl⟩ : syracuseStep 10723529 = 8042647) B8042647
theorem B7149019 : Blo 2231435 7149019 := bstep (se 1 (by rfl) ⟨5361764, by rfl⟩ : syracuseStep 7149019 = 10723529) B10723529
theorem B9532025 : Blo 2231435 9532025 := bstep (se 2 (by rfl) ⟨3574509, by rfl⟩ : syracuseStep 9532025 = 7149019) B7149019
theorem B6354683 : Blo 2231435 6354683 := bstep (se 1 (by rfl) ⟨4766012, by rfl⟩ : syracuseStep 6354683 = 9532025) B9532025
theorem B4236455 : Blo 2231435 4236455 := bstep (se 1 (by rfl) ⟨3177341, by rfl⟩ : syracuseStep 4236455 = 6354683) B6354683
theorem B2824303 : Blo 2231435 2824303 := bstep (se 1 (by rfl) ⟨2118227, by rfl⟩ : syracuseStep 2824303 = 4236455) B4236455
theorem B3765737 : Blo 2231435 3765737 := bstep (se 2 (by rfl) ⟨1412151, by rfl⟩ : syracuseStep 3765737 = 2824303) B2824303
theorem B2510491 : Blo 2231435 2510491 := bstep (se 1 (by rfl) ⟨1882868, by rfl⟩ : syracuseStep 2510491 = 3765737) B3765737
theorem B3347321 : Blo 2231435 3347321 := bstep (se 2 (by rfl) ⟨1255245, by rfl⟩ : syracuseStep 3347321 = 2510491) B2510491
theorem B2231547 : Blo 2231435 2231547 := bstep (se 1 (by rfl) ⟨1673660, by rfl⟩ : syracuseStep 2231547 = 3347321) B3347321
theorem B3015997 : Blo 2231435 3015997 := bbase (se 3 (by rfl) ⟨565499, by rfl⟩ : syracuseStep 3015997 = 1130999) (by norm_num)
theorem B16085317 : Blo 2231435 16085317 := bstep (se 4 (by rfl) ⟨1507998, by rfl⟩ : syracuseStep 16085317 = 3015997) B3015997
theorem B21447089 : Blo 2231435 21447089 := bstep (se 2 (by rfl) ⟨8042658, by rfl⟩ : syracuseStep 21447089 = 16085317) B16085317
theorem B14298059 : Blo 2231435 14298059 := bstep (se 1 (by rfl) ⟨10723544, by rfl⟩ : syracuseStep 14298059 = 21447089) B21447089
theorem B38128157 : Blo 2231435 38128157 := bstep (se 3 (by rfl) ⟨7149029, by rfl⟩ : syracuseStep 38128157 = 14298059) B14298059
theorem B25418771 : Blo 2231435 25418771 := bstep (se 1 (by rfl) ⟨19064078, by rfl⟩ : syracuseStep 25418771 = 38128157) B38128157
theorem B16945847 : Blo 2231435 16945847 := bstep (se 1 (by rfl) ⟨12709385, by rfl⟩ : syracuseStep 16945847 = 25418771) B25418771
theorem B11297231 : Blo 2231435 11297231 := bstep (se 1 (by rfl) ⟨8472923, by rfl⟩ : syracuseStep 11297231 = 16945847) B16945847
theorem B7531487 : Blo 2231435 7531487 := bstep (se 1 (by rfl) ⟨5648615, by rfl⟩ : syracuseStep 7531487 = 11297231) B11297231
theorem B5020991 : Blo 2231435 5020991 := bstep (se 1 (by rfl) ⟨3765743, by rfl⟩ : syracuseStep 5020991 = 7531487) B7531487
theorem B3347327 : Blo 2231435 3347327 := bstep (se 1 (by rfl) ⟨2510495, by rfl⟩ : syracuseStep 3347327 = 5020991) B5020991
theorem B2231551 : Blo 2231435 2231551 := bstep (se 1 (by rfl) ⟨1673663, by rfl⟩ : syracuseStep 2231551 = 3347327) B3347327
theorem B3347333 : Blo 2231435 3347333 := bbase (se 4 (by rfl) ⟨313812, by rfl⟩ : syracuseStep 3347333 = 627625) (by norm_num)
theorem B2231555 : Blo 2231435 2231555 := bstep (se 1 (by rfl) ⟨1673666, by rfl⟩ : syracuseStep 2231555 = 3347333) B3347333
theorem B3765757 : Blo 2231435 3765757 := bbase (se 3 (by rfl) ⟨706079, by rfl⟩ : syracuseStep 3765757 = 1412159) (by norm_num)
theorem B5021009 : Blo 2231435 5021009 := bstep (se 2 (by rfl) ⟨1882878, by rfl⟩ : syracuseStep 5021009 = 3765757) B3765757
theorem B3347339 : Blo 2231435 3347339 := bstep (se 1 (by rfl) ⟨2510504, by rfl⟩ : syracuseStep 3347339 = 5021009) B5021009
theorem B2231559 : Blo 2231435 2231559 := bstep (se 1 (by rfl) ⟨1673669, by rfl⟩ : syracuseStep 2231559 = 3347339) B3347339
theorem B2510509 : Blo 2231435 2510509 := bbase (se 3 (by rfl) ⟨470720, by rfl⟩ : syracuseStep 2510509 = 941441) (by norm_num)
theorem B3347345 : Blo 2231435 3347345 := bstep (se 2 (by rfl) ⟨1255254, by rfl⟩ : syracuseStep 3347345 = 2510509) B2510509
theorem B2231563 : Blo 2231435 2231563 := bstep (se 1 (by rfl) ⟨1673672, by rfl⟩ : syracuseStep 2231563 = 3347345) B3347345
theorem B7531541 : Blo 2231435 7531541 := bbase (se 6 (by rfl) ⟨176520, by rfl⟩ : syracuseStep 7531541 = 353041) (by norm_num)
theorem B5021027 : Blo 2231435 5021027 := bstep (se 1 (by rfl) ⟨3765770, by rfl⟩ : syracuseStep 5021027 = 7531541) B7531541
theorem B3347351 : Blo 2231435 3347351 := bstep (se 1 (by rfl) ⟨2510513, by rfl⟩ : syracuseStep 3347351 = 5021027) B5021027
theorem B2231567 : Blo 2231435 2231567 := bstep (se 1 (by rfl) ⟨1673675, by rfl⟩ : syracuseStep 2231567 = 3347351) B3347351
theorem B3347357 : Blo 2231435 3347357 := bbase (se 3 (by rfl) ⟨627629, by rfl⟩ : syracuseStep 3347357 = 1255259) (by norm_num)
theorem B2231571 : Blo 2231435 2231571 := bstep (se 1 (by rfl) ⟨1673678, by rfl⟩ : syracuseStep 2231571 = 3347357) B3347357
theorem B5021045 : Blo 2231435 5021045 := bbase (se 5 (by rfl) ⟨235361, by rfl⟩ : syracuseStep 5021045 = 470723) (by norm_num)
theorem B3347363 : Blo 2231435 3347363 := bstep (se 1 (by rfl) ⟨2510522, by rfl⟩ : syracuseStep 3347363 = 5021045) B5021045
theorem B2231575 : Blo 2231435 2231575 := bstep (se 1 (by rfl) ⟨1673681, by rfl⟩ : syracuseStep 2231575 = 3347363) B3347363
theorem B7634341 : Blo 2231435 7634341 := bbase (se 4 (by rfl) ⟨715719, by rfl⟩ : syracuseStep 7634341 = 1431439) (by norm_num)
theorem B10179121 : Blo 2231435 10179121 := bstep (se 2 (by rfl) ⟨3817170, by rfl⟩ : syracuseStep 10179121 = 7634341) B7634341
theorem B13572161 : Blo 2231435 13572161 := bstep (se 2 (by rfl) ⟨5089560, by rfl⟩ : syracuseStep 13572161 = 10179121) B10179121
theorem B9048107 : Blo 2231435 9048107 := bstep (se 1 (by rfl) ⟨6786080, by rfl⟩ : syracuseStep 9048107 = 13572161) B13572161
theorem B6032071 : Blo 2231435 6032071 := bstep (se 1 (by rfl) ⟨4524053, by rfl⟩ : syracuseStep 6032071 = 9048107) B9048107
theorem B8042761 : Blo 2231435 8042761 := bstep (se 2 (by rfl) ⟨3016035, by rfl⟩ : syracuseStep 8042761 = 6032071) B6032071
theorem B10723681 : Blo 2231435 10723681 := bstep (se 2 (by rfl) ⟨4021380, by rfl⟩ : syracuseStep 10723681 = 8042761) B8042761
theorem B14298241 : Blo 2231435 14298241 := bstep (se 2 (by rfl) ⟨5361840, by rfl⟩ : syracuseStep 14298241 = 10723681) B10723681
theorem B19064321 : Blo 2231435 19064321 := bstep (se 2 (by rfl) ⟨7149120, by rfl⟩ : syracuseStep 19064321 = 14298241) B14298241
theorem B12709547 : Blo 2231435 12709547 := bstep (se 1 (by rfl) ⟨9532160, by rfl⟩ : syracuseStep 12709547 = 19064321) B19064321
theorem B8473031 : Blo 2231435 8473031 := bstep (se 1 (by rfl) ⟨6354773, by rfl⟩ : syracuseStep 8473031 = 12709547) B12709547
theorem B5648687 : Blo 2231435 5648687 := bstep (se 1 (by rfl) ⟨4236515, by rfl⟩ : syracuseStep 5648687 = 8473031) B8473031
theorem B3765791 : Blo 2231435 3765791 := bstep (se 1 (by rfl) ⟨2824343, by rfl⟩ : syracuseStep 3765791 = 5648687) B5648687
theorem B2510527 : Blo 2231435 2510527 := bstep (se 1 (by rfl) ⟨1882895, by rfl⟩ : syracuseStep 2510527 = 3765791) B3765791
theorem B3347369 : Blo 2231435 3347369 := bstep (se 2 (by rfl) ⟨1255263, by rfl⟩ : syracuseStep 3347369 = 2510527) B2510527
theorem B2231579 : Blo 2231435 2231579 := bstep (se 1 (by rfl) ⟨1673684, by rfl⟩ : syracuseStep 2231579 = 3347369) B3347369
theorem B8473045 : Blo 2231435 8473045 := bbase (se 7 (by rfl) ⟨99293, by rfl⟩ : syracuseStep 8473045 = 198587) (by norm_num)
theorem B11297393 : Blo 2231435 11297393 := bstep (se 2 (by rfl) ⟨4236522, by rfl⟩ : syracuseStep 11297393 = 8473045) B8473045
theorem B7531595 : Blo 2231435 7531595 := bstep (se 1 (by rfl) ⟨5648696, by rfl⟩ : syracuseStep 7531595 = 11297393) B11297393
theorem B5021063 : Blo 2231435 5021063 := bstep (se 1 (by rfl) ⟨3765797, by rfl⟩ : syracuseStep 5021063 = 7531595) B7531595
theorem B3347375 : Blo 2231435 3347375 := bstep (se 1 (by rfl) ⟨2510531, by rfl⟩ : syracuseStep 3347375 = 5021063) B5021063
theorem B2231583 : Blo 2231435 2231583 := bstep (se 1 (by rfl) ⟨1673687, by rfl⟩ : syracuseStep 2231583 = 3347375) B3347375
theorem B3347381 : Blo 2231435 3347381 := bbase (se 5 (by rfl) ⟨156908, by rfl⟩ : syracuseStep 3347381 = 313817) (by norm_num)
theorem B2231587 : Blo 2231435 2231587 := bstep (se 1 (by rfl) ⟨1673690, by rfl⟩ : syracuseStep 2231587 = 3347381) B3347381
theorem B5648717 : Blo 2231435 5648717 := bbase (se 3 (by rfl) ⟨1059134, by rfl⟩ : syracuseStep 5648717 = 2118269) (by norm_num)
theorem B3765811 : Blo 2231435 3765811 := bstep (se 1 (by rfl) ⟨2824358, by rfl⟩ : syracuseStep 3765811 = 5648717) B5648717
theorem B5021081 : Blo 2231435 5021081 := bstep (se 2 (by rfl) ⟨1882905, by rfl⟩ : syracuseStep 5021081 = 3765811) B3765811
theorem B3347387 : Blo 2231435 3347387 := bstep (se 1 (by rfl) ⟨2510540, by rfl⟩ : syracuseStep 3347387 = 5021081) B5021081
theorem B2231591 : Blo 2231435 2231591 := bstep (se 1 (by rfl) ⟨1673693, by rfl⟩ : syracuseStep 2231591 = 3347387) B3347387
theorem B2510545 : Blo 2231435 2510545 := bbase (se 2 (by rfl) ⟨941454, by rfl⟩ : syracuseStep 2510545 = 1882909) (by norm_num)
theorem B3347393 : Blo 2231435 3347393 := bstep (se 2 (by rfl) ⟨1255272, by rfl⟩ : syracuseStep 3347393 = 2510545) B2510545
theorem B2231595 : Blo 2231435 2231595 := bstep (se 1 (by rfl) ⟨1673696, by rfl⟩ : syracuseStep 2231595 = 3347393) B3347393
theorem B48915413 : Blo 2231435 48915413 := bbase (se 7 (by rfl) ⟨573227, by rfl⟩ : syracuseStep 48915413 = 1146455) (by norm_num)
theorem B32610275 : Blo 2231435 32610275 := bstep (se 1 (by rfl) ⟨24457706, by rfl⟩ : syracuseStep 32610275 = 48915413) B48915413
theorem B21740183 : Blo 2231435 21740183 := bstep (se 1 (by rfl) ⟨16305137, by rfl⟩ : syracuseStep 21740183 = 32610275) B32610275
theorem B14493455 : Blo 2231435 14493455 := bstep (se 1 (by rfl) ⟨10870091, by rfl⟩ : syracuseStep 14493455 = 21740183) B21740183
theorem B9662303 : Blo 2231435 9662303 := bstep (se 1 (by rfl) ⟨7246727, by rfl⟩ : syracuseStep 9662303 = 14493455) B14493455
theorem B6441535 : Blo 2231435 6441535 := bstep (se 1 (by rfl) ⟨4831151, by rfl⟩ : syracuseStep 6441535 = 9662303) B9662303
theorem B34354853 : Blo 2231435 34354853 := bstep (se 4 (by rfl) ⟨3220767, by rfl⟩ : syracuseStep 34354853 = 6441535) B6441535
theorem B22903235 : Blo 2231435 22903235 := bstep (se 1 (by rfl) ⟨17177426, by rfl⟩ : syracuseStep 22903235 = 34354853) B34354853
theorem B15268823 : Blo 2231435 15268823 := bstep (se 1 (by rfl) ⟨11451617, by rfl⟩ : syracuseStep 15268823 = 22903235) B22903235
theorem B10179215 : Blo 2231435 10179215 := bstep (se 1 (by rfl) ⟨7634411, by rfl⟩ : syracuseStep 10179215 = 15268823) B15268823
theorem B6786143 : Blo 2231435 6786143 := bstep (se 1 (by rfl) ⟨5089607, by rfl⟩ : syracuseStep 6786143 = 10179215) B10179215
theorem B4524095 : Blo 2231435 4524095 := bstep (se 1 (by rfl) ⟨3393071, by rfl⟩ : syracuseStep 4524095 = 6786143) B6786143
theorem B3016063 : Blo 2231435 3016063 := bstep (se 1 (by rfl) ⟨2262047, by rfl⟩ : syracuseStep 3016063 = 4524095) B4524095
theorem B4021417 : Blo 2231435 4021417 := bstep (se 2 (by rfl) ⟨1508031, by rfl⟩ : syracuseStep 4021417 = 3016063) B3016063
theorem B5361889 : Blo 2231435 5361889 := bstep (se 2 (by rfl) ⟨2010708, by rfl⟩ : syracuseStep 5361889 = 4021417) B4021417
theorem B7149185 : Blo 2231435 7149185 := bstep (se 2 (by rfl) ⟨2680944, by rfl⟩ : syracuseStep 7149185 = 5361889) B5361889
theorem B4766123 : Blo 2231435 4766123 := bstep (se 1 (by rfl) ⟨3574592, by rfl⟩ : syracuseStep 4766123 = 7149185) B7149185
theorem B3177415 : Blo 2231435 3177415 := bstep (se 1 (by rfl) ⟨2383061, by rfl⟩ : syracuseStep 3177415 = 4766123) B4766123
theorem B4236553 : Blo 2231435 4236553 := bstep (se 2 (by rfl) ⟨1588707, by rfl⟩ : syracuseStep 4236553 = 3177415) B3177415
theorem B5648737 : Blo 2231435 5648737 := bstep (se 2 (by rfl) ⟨2118276, by rfl⟩ : syracuseStep 5648737 = 4236553) B4236553
theorem B7531649 : Blo 2231435 7531649 := bstep (se 2 (by rfl) ⟨2824368, by rfl⟩ : syracuseStep 7531649 = 5648737) B5648737
theorem B5021099 : Blo 2231435 5021099 := bstep (se 1 (by rfl) ⟨3765824, by rfl⟩ : syracuseStep 5021099 = 7531649) B7531649
theorem B3347399 : Blo 2231435 3347399 := bstep (se 1 (by rfl) ⟨2510549, by rfl⟩ : syracuseStep 3347399 = 5021099) B5021099
theorem B2231599 : Blo 2231435 2231599 := bstep (se 1 (by rfl) ⟨1673699, by rfl⟩ : syracuseStep 2231599 = 3347399) B3347399
theorem B3347405 : Blo 2231435 3347405 := bbase (se 3 (by rfl) ⟨627638, by rfl⟩ : syracuseStep 3347405 = 1255277) (by norm_num)
theorem B2231603 : Blo 2231435 2231603 := bstep (se 1 (by rfl) ⟨1673702, by rfl⟩ : syracuseStep 2231603 = 3347405) B3347405
theorem B5021117 : Blo 2231435 5021117 := bbase (se 3 (by rfl) ⟨941459, by rfl⟩ : syracuseStep 5021117 = 1882919) (by norm_num)
theorem B3347411 : Blo 2231435 3347411 := bstep (se 1 (by rfl) ⟨2510558, by rfl⟩ : syracuseStep 3347411 = 5021117) B5021117
theorem B2231607 : Blo 2231435 2231607 := bstep (se 1 (by rfl) ⟨1673705, by rfl⟩ : syracuseStep 2231607 = 3347411) B3347411
theorem B3765845 : Blo 2231435 3765845 := bbase (se 8 (by rfl) ⟨22065, by rfl⟩ : syracuseStep 3765845 = 44131) (by norm_num)
theorem B2510563 : Blo 2231435 2510563 := bstep (se 1 (by rfl) ⟨1882922, by rfl⟩ : syracuseStep 2510563 = 3765845) B3765845
theorem B3347417 : Blo 2231435 3347417 := bstep (se 2 (by rfl) ⟨1255281, by rfl⟩ : syracuseStep 3347417 = 2510563) B2510563
theorem B2231611 : Blo 2231435 2231611 := bstep (se 1 (by rfl) ⟨1673708, by rfl⟩ : syracuseStep 2231611 = 3347417) B3347417
theorem B4021445 : Blo 2231435 4021445 := bbase (se 4 (by rfl) ⟨377010, by rfl⟩ : syracuseStep 4021445 = 754021) (by norm_num)
theorem B10723853 : Blo 2231435 10723853 := bstep (se 3 (by rfl) ⟨2010722, by rfl⟩ : syracuseStep 10723853 = 4021445) B4021445
theorem B7149235 : Blo 2231435 7149235 := bstep (se 1 (by rfl) ⟨5361926, by rfl⟩ : syracuseStep 7149235 = 10723853) B10723853
theorem B9532313 : Blo 2231435 9532313 := bstep (se 2 (by rfl) ⟨3574617, by rfl⟩ : syracuseStep 9532313 = 7149235) B7149235
theorem B6354875 : Blo 2231435 6354875 := bstep (se 1 (by rfl) ⟨4766156, by rfl⟩ : syracuseStep 6354875 = 9532313) B9532313
theorem B16946333 : Blo 2231435 16946333 := bstep (se 3 (by rfl) ⟨3177437, by rfl⟩ : syracuseStep 16946333 = 6354875) B6354875
theorem B11297555 : Blo 2231435 11297555 := bstep (se 1 (by rfl) ⟨8473166, by rfl⟩ : syracuseStep 11297555 = 16946333) B16946333
theorem B7531703 : Blo 2231435 7531703 := bstep (se 1 (by rfl) ⟨5648777, by rfl⟩ : syracuseStep 7531703 = 11297555) B11297555
theorem B5021135 : Blo 2231435 5021135 := bstep (se 1 (by rfl) ⟨3765851, by rfl⟩ : syracuseStep 5021135 = 7531703) B7531703
theorem B3347423 : Blo 2231435 3347423 := bstep (se 1 (by rfl) ⟨2510567, by rfl⟩ : syracuseStep 3347423 = 5021135) B5021135
theorem B2231615 : Blo 2231435 2231615 := bstep (se 1 (by rfl) ⟨1673711, by rfl⟩ : syracuseStep 2231615 = 3347423) B3347423
theorem B3347429 : Blo 2231435 3347429 := bbase (se 4 (by rfl) ⟨313821, by rfl⟩ : syracuseStep 3347429 = 627643) (by norm_num)
theorem B2231619 : Blo 2231435 2231619 := bstep (se 1 (by rfl) ⟨1673714, by rfl⟩ : syracuseStep 2231619 = 3347429) B3347429
theorem B6618581 : Blo 2231435 6618581 := bbase (se 7 (by rfl) ⟨77561, by rfl⟩ : syracuseStep 6618581 = 155123) (by norm_num)
theorem B4412387 : Blo 2231435 4412387 := bstep (se 1 (by rfl) ⟨3309290, by rfl⟩ : syracuseStep 4412387 = 6618581) B6618581
theorem B2941591 : Blo 2231435 2941591 := bstep (se 1 (by rfl) ⟨2206193, by rfl⟩ : syracuseStep 2941591 = 4412387) B4412387
theorem B3922121 : Blo 2231435 3922121 := bstep (se 2 (by rfl) ⟨1470795, by rfl⟩ : syracuseStep 3922121 = 2941591) B2941591
theorem B2614747 : Blo 2231435 2614747 := bstep (se 1 (by rfl) ⟨1961060, by rfl⟩ : syracuseStep 2614747 = 3922121) B3922121
theorem B3486329 : Blo 2231435 3486329 := bstep (se 2 (by rfl) ⟨1307373, by rfl⟩ : syracuseStep 3486329 = 2614747) B2614747
theorem B2324219 : Blo 2231435 2324219 := bstep (se 1 (by rfl) ⟨1743164, by rfl⟩ : syracuseStep 2324219 = 3486329) B3486329
theorem B6197917 : Blo 2231435 6197917 := bstep (se 3 (by rfl) ⟨1162109, by rfl⟩ : syracuseStep 6197917 = 2324219) B2324219
theorem B8263889 : Blo 2231435 8263889 := bstep (se 2 (by rfl) ⟨3098958, by rfl⟩ : syracuseStep 8263889 = 6197917) B6197917
theorem B5509259 : Blo 2231435 5509259 := bstep (se 1 (by rfl) ⟨4131944, by rfl⟩ : syracuseStep 5509259 = 8263889) B8263889
theorem B3672839 : Blo 2231435 3672839 := bstep (se 1 (by rfl) ⟨2754629, by rfl⟩ : syracuseStep 3672839 = 5509259) B5509259
theorem B2448559 : Blo 2231435 2448559 := bstep (se 1 (by rfl) ⟨1836419, by rfl⟩ : syracuseStep 2448559 = 3672839) B3672839
theorem B13058981 : Blo 2231435 13058981 := bstep (se 4 (by rfl) ⟨1224279, by rfl⟩ : syracuseStep 13058981 = 2448559) B2448559
theorem B8705987 : Blo 2231435 8705987 := bstep (se 1 (by rfl) ⟨6529490, by rfl⟩ : syracuseStep 8705987 = 13058981) B13058981
theorem B5803991 : Blo 2231435 5803991 := bstep (se 1 (by rfl) ⟨4352993, by rfl⟩ : syracuseStep 5803991 = 8705987) B8705987
theorem B3869327 : Blo 2231435 3869327 := bstep (se 1 (by rfl) ⟨2901995, by rfl⟩ : syracuseStep 3869327 = 5803991) B5803991
theorem B10318205 : Blo 2231435 10318205 := bstep (se 3 (by rfl) ⟨1934663, by rfl⟩ : syracuseStep 10318205 = 3869327) B3869327
theorem B27515213 : Blo 2231435 27515213 := bstep (se 3 (by rfl) ⟨5159102, by rfl⟩ : syracuseStep 27515213 = 10318205) B10318205
theorem B18343475 : Blo 2231435 18343475 := bstep (se 1 (by rfl) ⟨13757606, by rfl⟩ : syracuseStep 18343475 = 27515213) B27515213
theorem B12228983 : Blo 2231435 12228983 := bstep (se 1 (by rfl) ⟨9171737, by rfl⟩ : syracuseStep 12228983 = 18343475) B18343475
theorem B8152655 : Blo 2231435 8152655 := bstep (se 1 (by rfl) ⟨6114491, by rfl⟩ : syracuseStep 8152655 = 12228983) B12228983
theorem B21740413 : Blo 2231435 21740413 := bstep (se 3 (by rfl) ⟨4076327, by rfl⟩ : syracuseStep 21740413 = 8152655) B8152655
theorem B28987217 : Blo 2231435 28987217 := bstep (se 2 (by rfl) ⟨10870206, by rfl⟩ : syracuseStep 28987217 = 21740413) B21740413
theorem B19324811 : Blo 2231435 19324811 := bstep (se 1 (by rfl) ⟨14493608, by rfl⟩ : syracuseStep 19324811 = 28987217) B28987217
theorem B12883207 : Blo 2231435 12883207 := bstep (se 1 (by rfl) ⟨9662405, by rfl⟩ : syracuseStep 12883207 = 19324811) B19324811
theorem B17177609 : Blo 2231435 17177609 := bstep (se 2 (by rfl) ⟨6441603, by rfl⟩ : syracuseStep 17177609 = 12883207) B12883207
theorem B45806957 : Blo 2231435 45806957 := bstep (se 3 (by rfl) ⟨8588804, by rfl⟩ : syracuseStep 45806957 = 17177609) B17177609
theorem B30537971 : Blo 2231435 30537971 := bstep (se 1 (by rfl) ⟨22903478, by rfl⟩ : syracuseStep 30537971 = 45806957) B45806957
theorem B20358647 : Blo 2231435 20358647 := bstep (se 1 (by rfl) ⟨15268985, by rfl⟩ : syracuseStep 20358647 = 30537971) B30537971
theorem B13572431 : Blo 2231435 13572431 := bstep (se 1 (by rfl) ⟨10179323, by rfl⟩ : syracuseStep 13572431 = 20358647) B20358647
theorem B9048287 : Blo 2231435 9048287 := bstep (se 1 (by rfl) ⟨6786215, by rfl⟩ : syracuseStep 9048287 = 13572431) B13572431
theorem B6032191 : Blo 2231435 6032191 := bstep (se 1 (by rfl) ⟨4524143, by rfl⟩ : syracuseStep 6032191 = 9048287) B9048287
theorem B8042921 : Blo 2231435 8042921 := bstep (se 2 (by rfl) ⟨3016095, by rfl⟩ : syracuseStep 8042921 = 6032191) B6032191
theorem B5361947 : Blo 2231435 5361947 := bstep (se 1 (by rfl) ⟨4021460, by rfl⟩ : syracuseStep 5361947 = 8042921) B8042921
theorem B3574631 : Blo 2231435 3574631 := bstep (se 1 (by rfl) ⟨2680973, by rfl⟩ : syracuseStep 3574631 = 5361947) B5361947
theorem B9532349 : Blo 2231435 9532349 := bstep (se 3 (by rfl) ⟨1787315, by rfl⟩ : syracuseStep 9532349 = 3574631) B3574631
theorem B6354899 : Blo 2231435 6354899 := bstep (se 1 (by rfl) ⟨4766174, by rfl⟩ : syracuseStep 6354899 = 9532349) B9532349
theorem B4236599 : Blo 2231435 4236599 := bstep (se 1 (by rfl) ⟨3177449, by rfl⟩ : syracuseStep 4236599 = 6354899) B6354899
theorem B2824399 : Blo 2231435 2824399 := bstep (se 1 (by rfl) ⟨2118299, by rfl⟩ : syracuseStep 2824399 = 4236599) B4236599
theorem B3765865 : Blo 2231435 3765865 := bstep (se 2 (by rfl) ⟨1412199, by rfl⟩ : syracuseStep 3765865 = 2824399) B2824399
theorem B5021153 : Blo 2231435 5021153 := bstep (se 2 (by rfl) ⟨1882932, by rfl⟩ : syracuseStep 5021153 = 3765865) B3765865
theorem B3347435 : Blo 2231435 3347435 := bstep (se 1 (by rfl) ⟨2510576, by rfl⟩ : syracuseStep 3347435 = 5021153) B5021153
theorem B2231623 : Blo 2231435 2231623 := bstep (se 1 (by rfl) ⟨1673717, by rfl⟩ : syracuseStep 2231623 = 3347435) B3347435
theorem B2510581 : Blo 2231435 2510581 := bbase (se 5 (by rfl) ⟨117683, by rfl⟩ : syracuseStep 2510581 = 235367) (by norm_num)
theorem B3347441 : Blo 2231435 3347441 := bstep (se 2 (by rfl) ⟨1255290, by rfl⟩ : syracuseStep 3347441 = 2510581) B2510581
theorem B2231627 : Blo 2231435 2231627 := bstep (se 1 (by rfl) ⟨1673720, by rfl⟩ : syracuseStep 2231627 = 3347441) B3347441
theorem B2824409 : Blo 2231435 2824409 := bbase (se 2 (by rfl) ⟨1059153, by rfl⟩ : syracuseStep 2824409 = 2118307) (by norm_num)
theorem B7531757 : Blo 2231435 7531757 := bstep (se 3 (by rfl) ⟨1412204, by rfl⟩ : syracuseStep 7531757 = 2824409) B2824409
theorem B5021171 : Blo 2231435 5021171 := bstep (se 1 (by rfl) ⟨3765878, by rfl⟩ : syracuseStep 5021171 = 7531757) B7531757
theorem B3347447 : Blo 2231435 3347447 := bstep (se 1 (by rfl) ⟨2510585, by rfl⟩ : syracuseStep 3347447 = 5021171) B5021171
theorem B2231631 : Blo 2231435 2231631 := bstep (se 1 (by rfl) ⟨1673723, by rfl⟩ : syracuseStep 2231631 = 3347447) B3347447
theorem B3347453 : Blo 2231435 3347453 := bbase (se 3 (by rfl) ⟨627647, by rfl⟩ : syracuseStep 3347453 = 1255295) (by norm_num)
theorem B2231635 : Blo 2231435 2231635 := bstep (se 1 (by rfl) ⟨1673726, by rfl⟩ : syracuseStep 2231635 = 3347453) B3347453
theorem B5021189 : Blo 2231435 5021189 := bbase (se 4 (by rfl) ⟨470736, by rfl⟩ : syracuseStep 5021189 = 941473) (by norm_num)
theorem B3347459 : Blo 2231435 3347459 := bstep (se 1 (by rfl) ⟨2510594, by rfl⟩ : syracuseStep 3347459 = 5021189) B5021189
theorem B2231639 : Blo 2231435 2231639 := bstep (se 1 (by rfl) ⟨1673729, by rfl⟩ : syracuseStep 2231639 = 3347459) B3347459
theorem B4236637 : Blo 2231435 4236637 := bbase (se 3 (by rfl) ⟨794369, by rfl⟩ : syracuseStep 4236637 = 1588739) (by norm_num)
theorem B5648849 : Blo 2231435 5648849 := bstep (se 2 (by rfl) ⟨2118318, by rfl⟩ : syracuseStep 5648849 = 4236637) B4236637
theorem B3765899 : Blo 2231435 3765899 := bstep (se 1 (by rfl) ⟨2824424, by rfl⟩ : syracuseStep 3765899 = 5648849) B5648849
theorem B2510599 : Blo 2231435 2510599 := bstep (se 1 (by rfl) ⟨1882949, by rfl⟩ : syracuseStep 2510599 = 3765899) B3765899
theorem B3347465 : Blo 2231435 3347465 := bstep (se 2 (by rfl) ⟨1255299, by rfl⟩ : syracuseStep 3347465 = 2510599) B2510599
theorem B2231643 : Blo 2231435 2231643 := bstep (se 1 (by rfl) ⟨1673732, by rfl⟩ : syracuseStep 2231643 = 3347465) B3347465
theorem B11297717 : Blo 2231435 11297717 := bbase (se 5 (by rfl) ⟨529580, by rfl⟩ : syracuseStep 11297717 = 1059161) (by norm_num)
theorem B7531811 : Blo 2231435 7531811 := bstep (se 1 (by rfl) ⟨5648858, by rfl⟩ : syracuseStep 7531811 = 11297717) B11297717
theorem B5021207 : Blo 2231435 5021207 := bstep (se 1 (by rfl) ⟨3765905, by rfl⟩ : syracuseStep 5021207 = 7531811) B7531811
theorem B3347471 : Blo 2231435 3347471 := bstep (se 1 (by rfl) ⟨2510603, by rfl⟩ : syracuseStep 3347471 = 5021207) B5021207
theorem B2231647 : Blo 2231435 2231647 := bstep (se 1 (by rfl) ⟨1673735, by rfl⟩ : syracuseStep 2231647 = 3347471) B3347471
theorem B3347477 : Blo 2231435 3347477 := bbase (se 6 (by rfl) ⟨78456, by rfl⟩ : syracuseStep 3347477 = 156913) (by norm_num)
theorem B2231651 : Blo 2231435 2231651 := bstep (se 1 (by rfl) ⟨1673738, by rfl⟩ : syracuseStep 2231651 = 3347477) B3347477
theorem B4585933 : Blo 2231435 4585933 := bbase (se 3 (by rfl) ⟨859862, by rfl⟩ : syracuseStep 4585933 = 1719725) (by norm_num)
theorem B6114577 : Blo 2231435 6114577 := bstep (se 2 (by rfl) ⟨2292966, by rfl⟩ : syracuseStep 6114577 = 4585933) B4585933
theorem B8152769 : Blo 2231435 8152769 := bstep (se 2 (by rfl) ⟨3057288, by rfl⟩ : syracuseStep 8152769 = 6114577) B6114577
theorem B21740717 : Blo 2231435 21740717 := bstep (se 3 (by rfl) ⟨4076384, by rfl⟩ : syracuseStep 21740717 = 8152769) B8152769
theorem B14493811 : Blo 2231435 14493811 := bstep (se 1 (by rfl) ⟨10870358, by rfl⟩ : syracuseStep 14493811 = 21740717) B21740717
theorem B19325081 : Blo 2231435 19325081 := bstep (se 2 (by rfl) ⟨7246905, by rfl⟩ : syracuseStep 19325081 = 14493811) B14493811
theorem B12883387 : Blo 2231435 12883387 := bstep (se 1 (by rfl) ⟨9662540, by rfl⟩ : syracuseStep 12883387 = 19325081) B19325081
theorem B17177849 : Blo 2231435 17177849 := bstep (se 2 (by rfl) ⟨6441693, by rfl⟩ : syracuseStep 17177849 = 12883387) B12883387
theorem B11451899 : Blo 2231435 11451899 := bstep (se 1 (by rfl) ⟨8588924, by rfl⟩ : syracuseStep 11451899 = 17177849) B17177849
theorem B30538397 : Blo 2231435 30538397 := bstep (se 3 (by rfl) ⟨5725949, by rfl⟩ : syracuseStep 30538397 = 11451899) B11451899
theorem B81435725 : Blo 2231435 81435725 := bstep (se 3 (by rfl) ⟨15269198, by rfl⟩ : syracuseStep 81435725 = 30538397) B30538397
theorem B54290483 : Blo 2231435 54290483 := bstep (se 1 (by rfl) ⟨40717862, by rfl⟩ : syracuseStep 54290483 = 81435725) B81435725
theorem B36193655 : Blo 2231435 36193655 := bstep (se 1 (by rfl) ⟨27145241, by rfl⟩ : syracuseStep 36193655 = 54290483) B54290483
theorem B24129103 : Blo 2231435 24129103 := bstep (se 1 (by rfl) ⟨18096827, by rfl⟩ : syracuseStep 24129103 = 36193655) B36193655
theorem B32172137 : Blo 2231435 32172137 := bstep (se 2 (by rfl) ⟨12064551, by rfl⟩ : syracuseStep 32172137 = 24129103) B24129103
theorem B21448091 : Blo 2231435 21448091 := bstep (se 1 (by rfl) ⟨16086068, by rfl⟩ : syracuseStep 21448091 = 32172137) B32172137
theorem B14298727 : Blo 2231435 14298727 := bstep (se 1 (by rfl) ⟨10724045, by rfl⟩ : syracuseStep 14298727 = 21448091) B21448091
theorem B19064969 : Blo 2231435 19064969 := bstep (se 2 (by rfl) ⟨7149363, by rfl⟩ : syracuseStep 19064969 = 14298727) B14298727
theorem B12709979 : Blo 2231435 12709979 := bstep (se 1 (by rfl) ⟨9532484, by rfl⟩ : syracuseStep 12709979 = 19064969) B19064969
theorem B8473319 : Blo 2231435 8473319 := bstep (se 1 (by rfl) ⟨6354989, by rfl⟩ : syracuseStep 8473319 = 12709979) B12709979
theorem B5648879 : Blo 2231435 5648879 := bstep (se 1 (by rfl) ⟨4236659, by rfl⟩ : syracuseStep 5648879 = 8473319) B8473319
theorem B3765919 : Blo 2231435 3765919 := bstep (se 1 (by rfl) ⟨2824439, by rfl⟩ : syracuseStep 3765919 = 5648879) B5648879
theorem B5021225 : Blo 2231435 5021225 := bstep (se 2 (by rfl) ⟨1882959, by rfl⟩ : syracuseStep 5021225 = 3765919) B3765919
theorem B3347483 : Blo 2231435 3347483 := bstep (se 1 (by rfl) ⟨2510612, by rfl⟩ : syracuseStep 3347483 = 5021225) B5021225
theorem B2231655 : Blo 2231435 2231655 := bstep (se 1 (by rfl) ⟨1673741, by rfl⟩ : syracuseStep 2231655 = 3347483) B3347483
theorem B2510617 : Blo 2231435 2510617 := bbase (se 2 (by rfl) ⟨941481, by rfl⟩ : syracuseStep 2510617 = 1882963) (by norm_num)
theorem B3347489 : Blo 2231435 3347489 := bstep (se 2 (by rfl) ⟨1255308, by rfl⟩ : syracuseStep 3347489 = 2510617) B2510617
theorem B2231659 : Blo 2231435 2231659 := bstep (se 1 (by rfl) ⟨1673744, by rfl⟩ : syracuseStep 2231659 = 3347489) B3347489
theorem B8473349 : Blo 2231435 8473349 := bbase (se 4 (by rfl) ⟨794376, by rfl⟩ : syracuseStep 8473349 = 1588753) (by norm_num)
theorem B5648899 : Blo 2231435 5648899 := bstep (se 1 (by rfl) ⟨4236674, by rfl⟩ : syracuseStep 5648899 = 8473349) B8473349
theorem B7531865 : Blo 2231435 7531865 := bstep (se 2 (by rfl) ⟨2824449, by rfl⟩ : syracuseStep 7531865 = 5648899) B5648899
theorem B5021243 : Blo 2231435 5021243 := bstep (se 1 (by rfl) ⟨3765932, by rfl⟩ : syracuseStep 5021243 = 7531865) B7531865
theorem B3347495 : Blo 2231435 3347495 := bstep (se 1 (by rfl) ⟨2510621, by rfl⟩ : syracuseStep 3347495 = 5021243) B5021243
theorem B2231663 : Blo 2231435 2231663 := bstep (se 1 (by rfl) ⟨1673747, by rfl⟩ : syracuseStep 2231663 = 3347495) B3347495
theorem B3347501 : Blo 2231435 3347501 := bbase (se 3 (by rfl) ⟨627656, by rfl⟩ : syracuseStep 3347501 = 1255313) (by norm_num)
theorem B2231667 : Blo 2231435 2231667 := bstep (se 1 (by rfl) ⟨1673750, by rfl⟩ : syracuseStep 2231667 = 3347501) B3347501
theorem B5021261 : Blo 2231435 5021261 := bbase (se 3 (by rfl) ⟨941486, by rfl⟩ : syracuseStep 5021261 = 1882973) (by norm_num)
theorem B3347507 : Blo 2231435 3347507 := bstep (se 1 (by rfl) ⟨2510630, by rfl⟩ : syracuseStep 3347507 = 5021261) B5021261
theorem B2231671 : Blo 2231435 2231671 := bstep (se 1 (by rfl) ⟨1673753, by rfl⟩ : syracuseStep 2231671 = 3347507) B3347507
theorem B2824465 : Blo 2231435 2824465 := bbase (se 2 (by rfl) ⟨1059174, by rfl⟩ : syracuseStep 2824465 = 2118349) (by norm_num)
theorem B3765953 : Blo 2231435 3765953 := bstep (se 2 (by rfl) ⟨1412232, by rfl⟩ : syracuseStep 3765953 = 2824465) B2824465
theorem B2510635 : Blo 2231435 2510635 := bstep (se 1 (by rfl) ⟨1882976, by rfl⟩ : syracuseStep 2510635 = 3765953) B3765953
theorem B3347513 : Blo 2231435 3347513 := bstep (se 2 (by rfl) ⟨1255317, by rfl⟩ : syracuseStep 3347513 = 2510635) B2510635
theorem B2231675 : Blo 2231435 2231675 := bstep (se 1 (by rfl) ⟨1673756, by rfl⟩ : syracuseStep 2231675 = 3347513) B3347513
theorem B4766293 : Blo 2231435 4766293 := bbase (se 8 (by rfl) ⟨27927, by rfl⟩ : syracuseStep 4766293 = 55855) (by norm_num)
theorem B25420229 : Blo 2231435 25420229 := bstep (se 4 (by rfl) ⟨2383146, by rfl⟩ : syracuseStep 25420229 = 4766293) B4766293
theorem B16946819 : Blo 2231435 16946819 := bstep (se 1 (by rfl) ⟨12710114, by rfl⟩ : syracuseStep 16946819 = 25420229) B25420229
theorem B11297879 : Blo 2231435 11297879 := bstep (se 1 (by rfl) ⟨8473409, by rfl⟩ : syracuseStep 11297879 = 16946819) B16946819
theorem B7531919 : Blo 2231435 7531919 := bstep (se 1 (by rfl) ⟨5648939, by rfl⟩ : syracuseStep 7531919 = 11297879) B11297879
theorem B5021279 : Blo 2231435 5021279 := bstep (se 1 (by rfl) ⟨3765959, by rfl⟩ : syracuseStep 5021279 = 7531919) B7531919
theorem B3347519 : Blo 2231435 3347519 := bstep (se 1 (by rfl) ⟨2510639, by rfl⟩ : syracuseStep 3347519 = 5021279) B5021279
theorem B2231679 : Blo 2231435 2231679 := bstep (se 1 (by rfl) ⟨1673759, by rfl⟩ : syracuseStep 2231679 = 3347519) B3347519
theorem B3347525 : Blo 2231435 3347525 := bbase (se 4 (by rfl) ⟨313830, by rfl⟩ : syracuseStep 3347525 = 627661) (by norm_num)
theorem B2231683 : Blo 2231435 2231683 := bstep (se 1 (by rfl) ⟨1673762, by rfl⟩ : syracuseStep 2231683 = 3347525) B3347525
theorem B3765973 : Blo 2231435 3765973 := bbase (se 7 (by rfl) ⟨44132, by rfl⟩ : syracuseStep 3765973 = 88265) (by norm_num)
theorem B5021297 : Blo 2231435 5021297 := bstep (se 2 (by rfl) ⟨1882986, by rfl⟩ : syracuseStep 5021297 = 3765973) B3765973
theorem B3347531 : Blo 2231435 3347531 := bstep (se 1 (by rfl) ⟨2510648, by rfl⟩ : syracuseStep 3347531 = 5021297) B5021297
theorem B2231687 : Blo 2231435 2231687 := bstep (se 1 (by rfl) ⟨1673765, by rfl⟩ : syracuseStep 2231687 = 3347531) B3347531
theorem B2510653 : Blo 2231435 2510653 := bbase (se 3 (by rfl) ⟨470747, by rfl⟩ : syracuseStep 2510653 = 941495) (by norm_num)
theorem B3347537 : Blo 2231435 3347537 := bstep (se 2 (by rfl) ⟨1255326, by rfl⟩ : syracuseStep 3347537 = 2510653) B2510653
theorem B2231691 : Blo 2231435 2231691 := bstep (se 1 (by rfl) ⟨1673768, by rfl⟩ : syracuseStep 2231691 = 3347537) B3347537
theorem B7531973 : Blo 2231435 7531973 := bbase (se 4 (by rfl) ⟨706122, by rfl⟩ : syracuseStep 7531973 = 1412245) (by norm_num)
theorem B5021315 : Blo 2231435 5021315 := bstep (se 1 (by rfl) ⟨3765986, by rfl⟩ : syracuseStep 5021315 = 7531973) B7531973
theorem B3347543 : Blo 2231435 3347543 := bstep (se 1 (by rfl) ⟨2510657, by rfl⟩ : syracuseStep 3347543 = 5021315) B5021315
theorem B2231695 : Blo 2231435 2231695 := bstep (se 1 (by rfl) ⟨1673771, by rfl⟩ : syracuseStep 2231695 = 3347543) B3347543
theorem B3347549 : Blo 2231435 3347549 := bbase (se 3 (by rfl) ⟨627665, by rfl⟩ : syracuseStep 3347549 = 1255331) (by norm_num)
theorem B2231699 : Blo 2231435 2231699 := bstep (se 1 (by rfl) ⟨1673774, by rfl⟩ : syracuseStep 2231699 = 3347549) B3347549
theorem B5021333 : Blo 2231435 5021333 := bbase (se 6 (by rfl) ⟨117687, by rfl⟩ : syracuseStep 5021333 = 235375) (by norm_num)
theorem B3347555 : Blo 2231435 3347555 := bstep (se 1 (by rfl) ⟨2510666, by rfl⟩ : syracuseStep 3347555 = 5021333) B5021333
theorem B2231703 : Blo 2231435 2231703 := bstep (se 1 (by rfl) ⟨1673777, by rfl⟩ : syracuseStep 2231703 = 3347555) B3347555
theorem B2383177 : Blo 2231435 2383177 := bbase (se 2 (by rfl) ⟨893691, by rfl⟩ : syracuseStep 2383177 = 1787383) (by norm_num)
theorem B3177569 : Blo 2231435 3177569 := bstep (se 2 (by rfl) ⟨1191588, by rfl⟩ : syracuseStep 3177569 = 2383177) B2383177
theorem B8473517 : Blo 2231435 8473517 := bstep (se 3 (by rfl) ⟨1588784, by rfl⟩ : syracuseStep 8473517 = 3177569) B3177569
theorem B5649011 : Blo 2231435 5649011 := bstep (se 1 (by rfl) ⟨4236758, by rfl⟩ : syracuseStep 5649011 = 8473517) B8473517
theorem B3766007 : Blo 2231435 3766007 := bstep (se 1 (by rfl) ⟨2824505, by rfl⟩ : syracuseStep 3766007 = 5649011) B5649011
theorem B2510671 : Blo 2231435 2510671 := bstep (se 1 (by rfl) ⟨1883003, by rfl⟩ : syracuseStep 2510671 = 3766007) B3766007
theorem B3347561 : Blo 2231435 3347561 := bstep (se 2 (by rfl) ⟨1255335, by rfl⟩ : syracuseStep 3347561 = 2510671) B2510671
theorem B2231707 : Blo 2231435 2231707 := bstep (se 1 (by rfl) ⟨1673780, by rfl⟩ : syracuseStep 2231707 = 3347561) B3347561
theorem B5362157 : Blo 2231435 5362157 := bbase (se 3 (by rfl) ⟨1005404, by rfl⟩ : syracuseStep 5362157 = 2010809) (by norm_num)
theorem B14299085 : Blo 2231435 14299085 := bstep (se 3 (by rfl) ⟨2681078, by rfl⟩ : syracuseStep 14299085 = 5362157) B5362157
theorem B9532723 : Blo 2231435 9532723 := bstep (se 1 (by rfl) ⟨7149542, by rfl⟩ : syracuseStep 9532723 = 14299085) B14299085
theorem B12710297 : Blo 2231435 12710297 := bstep (se 2 (by rfl) ⟨4766361, by rfl⟩ : syracuseStep 12710297 = 9532723) B9532723
theorem B8473531 : Blo 2231435 8473531 := bstep (se 1 (by rfl) ⟨6355148, by rfl⟩ : syracuseStep 8473531 = 12710297) B12710297
theorem B11298041 : Blo 2231435 11298041 := bstep (se 2 (by rfl) ⟨4236765, by rfl⟩ : syracuseStep 11298041 = 8473531) B8473531
theorem B7532027 : Blo 2231435 7532027 := bstep (se 1 (by rfl) ⟨5649020, by rfl⟩ : syracuseStep 7532027 = 11298041) B11298041
theorem B5021351 : Blo 2231435 5021351 := bstep (se 1 (by rfl) ⟨3766013, by rfl⟩ : syracuseStep 5021351 = 7532027) B7532027
theorem B3347567 : Blo 2231435 3347567 := bstep (se 1 (by rfl) ⟨2510675, by rfl⟩ : syracuseStep 3347567 = 5021351) B5021351
theorem B2231711 : Blo 2231435 2231711 := bstep (se 1 (by rfl) ⟨1673783, by rfl⟩ : syracuseStep 2231711 = 3347567) B3347567
theorem B3347573 : Blo 2231435 3347573 := bbase (se 5 (by rfl) ⟨156917, by rfl⟩ : syracuseStep 3347573 = 313835) (by norm_num)
theorem B2231715 : Blo 2231435 2231715 := bstep (se 1 (by rfl) ⟨1673786, by rfl⟩ : syracuseStep 2231715 = 3347573) B3347573
theorem B4236781 : Blo 2231435 4236781 := bbase (se 3 (by rfl) ⟨794396, by rfl⟩ : syracuseStep 4236781 = 1588793) (by norm_num)
theorem B5649041 : Blo 2231435 5649041 := bstep (se 2 (by rfl) ⟨2118390, by rfl⟩ : syracuseStep 5649041 = 4236781) B4236781
theorem B3766027 : Blo 2231435 3766027 := bstep (se 1 (by rfl) ⟨2824520, by rfl⟩ : syracuseStep 3766027 = 5649041) B5649041
theorem B5021369 : Blo 2231435 5021369 := bstep (se 2 (by rfl) ⟨1883013, by rfl⟩ : syracuseStep 5021369 = 3766027) B3766027
theorem B3347579 : Blo 2231435 3347579 := bstep (se 1 (by rfl) ⟨2510684, by rfl⟩ : syracuseStep 3347579 = 5021369) B5021369
theorem B2231719 : Blo 2231435 2231719 := bstep (se 1 (by rfl) ⟨1673789, by rfl⟩ : syracuseStep 2231719 = 3347579) B3347579
theorem B2510689 : Blo 2231435 2510689 := bbase (se 2 (by rfl) ⟨941508, by rfl⟩ : syracuseStep 2510689 = 1883017) (by norm_num)
theorem B3347585 : Blo 2231435 3347585 := bstep (se 2 (by rfl) ⟨1255344, by rfl⟩ : syracuseStep 3347585 = 2510689) B2510689
theorem B2231723 : Blo 2231435 2231723 := bstep (se 1 (by rfl) ⟨1673792, by rfl⟩ : syracuseStep 2231723 = 3347585) B3347585
theorem B5649061 : Blo 2231435 5649061 := bbase (se 4 (by rfl) ⟨529599, by rfl⟩ : syracuseStep 5649061 = 1059199) (by norm_num)
theorem B7532081 : Blo 2231435 7532081 := bstep (se 2 (by rfl) ⟨2824530, by rfl⟩ : syracuseStep 7532081 = 5649061) B5649061
theorem B5021387 : Blo 2231435 5021387 := bstep (se 1 (by rfl) ⟨3766040, by rfl⟩ : syracuseStep 5021387 = 7532081) B7532081
theorem B3347591 : Blo 2231435 3347591 := bstep (se 1 (by rfl) ⟨2510693, by rfl⟩ : syracuseStep 3347591 = 5021387) B5021387
theorem B2231727 : Blo 2231435 2231727 := bstep (se 1 (by rfl) ⟨1673795, by rfl⟩ : syracuseStep 2231727 = 3347591) B3347591
theorem B3347597 : Blo 2231435 3347597 := bbase (se 3 (by rfl) ⟨627674, by rfl⟩ : syracuseStep 3347597 = 1255349) (by norm_num)
theorem B2231731 : Blo 2231435 2231731 := bstep (se 1 (by rfl) ⟨1673798, by rfl⟩ : syracuseStep 2231731 = 3347597) B3347597
theorem B5021405 : Blo 2231435 5021405 := bbase (se 3 (by rfl) ⟨941513, by rfl⟩ : syracuseStep 5021405 = 1883027) (by norm_num)
theorem B3347603 : Blo 2231435 3347603 := bstep (se 1 (by rfl) ⟨2510702, by rfl⟩ : syracuseStep 3347603 = 5021405) B5021405
theorem B2231735 : Blo 2231435 2231735 := bstep (se 1 (by rfl) ⟨1673801, by rfl⟩ : syracuseStep 2231735 = 3347603) B3347603
theorem B3766061 : Blo 2231435 3766061 := bbase (se 3 (by rfl) ⟨706136, by rfl⟩ : syracuseStep 3766061 = 1412273) (by norm_num)
theorem B2510707 : Blo 2231435 2510707 := bstep (se 1 (by rfl) ⟨1883030, by rfl⟩ : syracuseStep 2510707 = 3766061) B3766061
theorem B3347609 : Blo 2231435 3347609 := bstep (se 2 (by rfl) ⟨1255353, by rfl⟩ : syracuseStep 3347609 = 2510707) B2510707
theorem B2231739 : Blo 2231435 2231739 := bstep (se 1 (by rfl) ⟨1673804, by rfl⟩ : syracuseStep 2231739 = 3347609) B3347609
theorem B5159381 : Blo 2231435 5159381 := bbase (se 7 (by rfl) ⟨60461, by rfl⟩ : syracuseStep 5159381 = 120923) (by norm_num)
theorem B13758349 : Blo 2231435 13758349 := bstep (se 3 (by rfl) ⟨2579690, by rfl⟩ : syracuseStep 13758349 = 5159381) B5159381
theorem B18344465 : Blo 2231435 18344465 := bstep (se 2 (by rfl) ⟨6879174, by rfl⟩ : syracuseStep 18344465 = 13758349) B13758349
theorem B12229643 : Blo 2231435 12229643 := bstep (se 1 (by rfl) ⟨9172232, by rfl⟩ : syracuseStep 12229643 = 18344465) B18344465
theorem B8153095 : Blo 2231435 8153095 := bstep (se 1 (by rfl) ⟨6114821, by rfl⟩ : syracuseStep 8153095 = 12229643) B12229643
theorem B10870793 : Blo 2231435 10870793 := bstep (se 2 (by rfl) ⟨4076547, by rfl⟩ : syracuseStep 10870793 = 8153095) B8153095
theorem B7247195 : Blo 2231435 7247195 := bstep (se 1 (by rfl) ⟨5435396, by rfl⟩ : syracuseStep 7247195 = 10870793) B10870793
theorem B4831463 : Blo 2231435 4831463 := bstep (se 1 (by rfl) ⟨3623597, by rfl⟩ : syracuseStep 4831463 = 7247195) B7247195
theorem B3220975 : Blo 2231435 3220975 := bstep (se 1 (by rfl) ⟨2415731, by rfl⟩ : syracuseStep 3220975 = 4831463) B4831463
theorem B4294633 : Blo 2231435 4294633 := bstep (se 2 (by rfl) ⟨1610487, by rfl⟩ : syracuseStep 4294633 = 3220975) B3220975
theorem B5726177 : Blo 2231435 5726177 := bstep (se 2 (by rfl) ⟨2147316, by rfl⟩ : syracuseStep 5726177 = 4294633) B4294633
theorem B3817451 : Blo 2231435 3817451 := bstep (se 1 (by rfl) ⟨2863088, by rfl⟩ : syracuseStep 3817451 = 5726177) B5726177
theorem B2544967 : Blo 2231435 2544967 := bstep (se 1 (by rfl) ⟨1908725, by rfl⟩ : syracuseStep 2544967 = 3817451) B3817451
theorem B3393289 : Blo 2231435 3393289 := bstep (se 2 (by rfl) ⟨1272483, by rfl⟩ : syracuseStep 3393289 = 2544967) B2544967
theorem B4524385 : Blo 2231435 4524385 := bstep (se 2 (by rfl) ⟨1696644, by rfl⟩ : syracuseStep 4524385 = 3393289) B3393289
theorem B6032513 : Blo 2231435 6032513 := bstep (se 2 (by rfl) ⟨2262192, by rfl⟩ : syracuseStep 6032513 = 4524385) B4524385
theorem B16086701 : Blo 2231435 16086701 := bstep (se 3 (by rfl) ⟨3016256, by rfl⟩ : syracuseStep 16086701 = 6032513) B6032513
theorem B42897869 : Blo 2231435 42897869 := bstep (se 3 (by rfl) ⟨8043350, by rfl⟩ : syracuseStep 42897869 = 16086701) B16086701
theorem B28598579 : Blo 2231435 28598579 := bstep (se 1 (by rfl) ⟨21448934, by rfl⟩ : syracuseStep 28598579 = 42897869) B42897869
theorem B19065719 : Blo 2231435 19065719 := bstep (se 1 (by rfl) ⟨14299289, by rfl⟩ : syracuseStep 19065719 = 28598579) B28598579
theorem B12710479 : Blo 2231435 12710479 := bstep (se 1 (by rfl) ⟨9532859, by rfl⟩ : syracuseStep 12710479 = 19065719) B19065719
theorem B16947305 : Blo 2231435 16947305 := bstep (se 2 (by rfl) ⟨6355239, by rfl⟩ : syracuseStep 16947305 = 12710479) B12710479
theorem B11298203 : Blo 2231435 11298203 := bstep (se 1 (by rfl) ⟨8473652, by rfl⟩ : syracuseStep 11298203 = 16947305) B16947305
theorem B7532135 : Blo 2231435 7532135 := bstep (se 1 (by rfl) ⟨5649101, by rfl⟩ : syracuseStep 7532135 = 11298203) B11298203
theorem B5021423 : Blo 2231435 5021423 := bstep (se 1 (by rfl) ⟨3766067, by rfl⟩ : syracuseStep 5021423 = 7532135) B7532135
theorem B3347615 : Blo 2231435 3347615 := bstep (se 1 (by rfl) ⟨2510711, by rfl⟩ : syracuseStep 3347615 = 5021423) B5021423
theorem B2231743 : Blo 2231435 2231743 := bstep (se 1 (by rfl) ⟨1673807, by rfl⟩ : syracuseStep 2231743 = 3347615) B3347615
theorem B3347621 : Blo 2231435 3347621 := bbase (se 4 (by rfl) ⟨313839, by rfl⟩ : syracuseStep 3347621 = 627679) (by norm_num)
theorem B2231747 : Blo 2231435 2231747 := bstep (se 1 (by rfl) ⟨1673810, by rfl⟩ : syracuseStep 2231747 = 3347621) B3347621
theorem B2824561 : Blo 2231435 2824561 := bbase (se 2 (by rfl) ⟨1059210, by rfl⟩ : syracuseStep 2824561 = 2118421) (by norm_num)
theorem B3766081 : Blo 2231435 3766081 := bstep (se 2 (by rfl) ⟨1412280, by rfl⟩ : syracuseStep 3766081 = 2824561) B2824561
theorem B5021441 : Blo 2231435 5021441 := bstep (se 2 (by rfl) ⟨1883040, by rfl⟩ : syracuseStep 5021441 = 3766081) B3766081
theorem B3347627 : Blo 2231435 3347627 := bstep (se 1 (by rfl) ⟨2510720, by rfl⟩ : syracuseStep 3347627 = 5021441) B5021441
theorem B2231751 : Blo 2231435 2231751 := bstep (se 1 (by rfl) ⟨1673813, by rfl⟩ : syracuseStep 2231751 = 3347627) B3347627
theorem B2510725 : Blo 2231435 2510725 := bbase (se 4 (by rfl) ⟨235380, by rfl⟩ : syracuseStep 2510725 = 470761) (by norm_num)
theorem B3347633 : Blo 2231435 3347633 := bstep (se 2 (by rfl) ⟨1255362, by rfl⟩ : syracuseStep 3347633 = 2510725) B2510725
theorem B2231755 : Blo 2231435 2231755 := bstep (se 1 (by rfl) ⟨1673816, by rfl⟩ : syracuseStep 2231755 = 3347633) B3347633
theorem B2681137 : Blo 2231435 2681137 := bbase (se 2 (by rfl) ⟨1005426, by rfl⟩ : syracuseStep 2681137 = 2010853) (by norm_num)
theorem B3574849 : Blo 2231435 3574849 := bstep (se 2 (by rfl) ⟨1340568, by rfl⟩ : syracuseStep 3574849 = 2681137) B2681137
theorem B4766465 : Blo 2231435 4766465 := bstep (se 2 (by rfl) ⟨1787424, by rfl⟩ : syracuseStep 4766465 = 3574849) B3574849
theorem B3177643 : Blo 2231435 3177643 := bstep (se 1 (by rfl) ⟨2383232, by rfl⟩ : syracuseStep 3177643 = 4766465) B4766465
theorem B4236857 : Blo 2231435 4236857 := bstep (se 2 (by rfl) ⟨1588821, by rfl⟩ : syracuseStep 4236857 = 3177643) B3177643
theorem B2824571 : Blo 2231435 2824571 := bstep (se 1 (by rfl) ⟨2118428, by rfl⟩ : syracuseStep 2824571 = 4236857) B4236857
theorem B7532189 : Blo 2231435 7532189 := bstep (se 3 (by rfl) ⟨1412285, by rfl⟩ : syracuseStep 7532189 = 2824571) B2824571
theorem B5021459 : Blo 2231435 5021459 := bstep (se 1 (by rfl) ⟨3766094, by rfl⟩ : syracuseStep 5021459 = 7532189) B7532189
theorem B3347639 : Blo 2231435 3347639 := bstep (se 1 (by rfl) ⟨2510729, by rfl⟩ : syracuseStep 3347639 = 5021459) B5021459
theorem B2231759 : Blo 2231435 2231759 := bstep (se 1 (by rfl) ⟨1673819, by rfl⟩ : syracuseStep 2231759 = 3347639) B3347639
theorem B3347645 : Blo 2231435 3347645 := bbase (se 3 (by rfl) ⟨627683, by rfl⟩ : syracuseStep 3347645 = 1255367) (by norm_num)
theorem B2231763 : Blo 2231435 2231763 := bstep (se 1 (by rfl) ⟨1673822, by rfl⟩ : syracuseStep 2231763 = 3347645) B3347645
theorem B5021477 : Blo 2231435 5021477 := bbase (se 4 (by rfl) ⟨470763, by rfl⟩ : syracuseStep 5021477 = 941527) (by norm_num)
theorem B3347651 : Blo 2231435 3347651 := bstep (se 1 (by rfl) ⟨2510738, by rfl⟩ : syracuseStep 3347651 = 5021477) B5021477
theorem B2231767 : Blo 2231435 2231767 := bstep (se 1 (by rfl) ⟨1673825, by rfl⟩ : syracuseStep 2231767 = 3347651) B3347651
theorem B5649173 : Blo 2231435 5649173 := bbase (se 6 (by rfl) ⟨132402, by rfl⟩ : syracuseStep 5649173 = 264805) (by norm_num)
theorem B3766115 : Blo 2231435 3766115 := bstep (se 1 (by rfl) ⟨2824586, by rfl⟩ : syracuseStep 3766115 = 5649173) B5649173
theorem B2510743 : Blo 2231435 2510743 := bstep (se 1 (by rfl) ⟨1883057, by rfl⟩ : syracuseStep 2510743 = 3766115) B3766115
theorem B3347657 : Blo 2231435 3347657 := bstep (se 2 (by rfl) ⟨1255371, by rfl⟩ : syracuseStep 3347657 = 2510743) B2510743
theorem B2231771 : Blo 2231435 2231771 := bstep (se 1 (by rfl) ⟨1673828, by rfl⟩ : syracuseStep 2231771 = 3347657) B3347657
theorem B9532997 : Blo 2231435 9532997 := bbase (se 4 (by rfl) ⟨893718, by rfl⟩ : syracuseStep 9532997 = 1787437) (by norm_num)
theorem B6355331 : Blo 2231435 6355331 := bstep (se 1 (by rfl) ⟨4766498, by rfl⟩ : syracuseStep 6355331 = 9532997) B9532997
theorem B4236887 : Blo 2231435 4236887 := bstep (se 1 (by rfl) ⟨3177665, by rfl⟩ : syracuseStep 4236887 = 6355331) B6355331
theorem B11298365 : Blo 2231435 11298365 := bstep (se 3 (by rfl) ⟨2118443, by rfl⟩ : syracuseStep 11298365 = 4236887) B4236887
theorem B7532243 : Blo 2231435 7532243 := bstep (se 1 (by rfl) ⟨5649182, by rfl⟩ : syracuseStep 7532243 = 11298365) B11298365
theorem B5021495 : Blo 2231435 5021495 := bstep (se 1 (by rfl) ⟨3766121, by rfl⟩ : syracuseStep 5021495 = 7532243) B7532243
theorem B3347663 : Blo 2231435 3347663 := bstep (se 1 (by rfl) ⟨2510747, by rfl⟩ : syracuseStep 3347663 = 5021495) B5021495
theorem B2231775 : Blo 2231435 2231775 := bstep (se 1 (by rfl) ⟨1673831, by rfl⟩ : syracuseStep 2231775 = 3347663) B3347663
theorem B3347669 : Blo 2231435 3347669 := bbase (se 7 (by rfl) ⟨39230, by rfl⟩ : syracuseStep 3347669 = 78461) (by norm_num)
theorem B2231779 : Blo 2231435 2231779 := bstep (se 1 (by rfl) ⟨1673834, by rfl⟩ : syracuseStep 2231779 = 3347669) B3347669
theorem B3177677 : Blo 2231435 3177677 := bbase (se 3 (by rfl) ⟨595814, by rfl⟩ : syracuseStep 3177677 = 1191629) (by norm_num)
theorem B8473805 : Blo 2231435 8473805 := bstep (se 3 (by rfl) ⟨1588838, by rfl⟩ : syracuseStep 8473805 = 3177677) B3177677
theorem B5649203 : Blo 2231435 5649203 := bstep (se 1 (by rfl) ⟨4236902, by rfl⟩ : syracuseStep 5649203 = 8473805) B8473805
theorem B3766135 : Blo 2231435 3766135 := bstep (se 1 (by rfl) ⟨2824601, by rfl⟩ : syracuseStep 3766135 = 5649203) B5649203
theorem B5021513 : Blo 2231435 5021513 := bstep (se 2 (by rfl) ⟨1883067, by rfl⟩ : syracuseStep 5021513 = 3766135) B3766135
theorem B3347675 : Blo 2231435 3347675 := bstep (se 1 (by rfl) ⟨2510756, by rfl⟩ : syracuseStep 3347675 = 5021513) B5021513
theorem B2231783 : Blo 2231435 2231783 := bstep (se 1 (by rfl) ⟨1673837, by rfl⟩ : syracuseStep 2231783 = 3347675) B3347675
theorem B2510761 : Blo 2231435 2510761 := bbase (se 2 (by rfl) ⟨941535, by rfl⟩ : syracuseStep 2510761 = 1883071) (by norm_num)
theorem B3347681 : Blo 2231435 3347681 := bstep (se 2 (by rfl) ⟨1255380, by rfl⟩ : syracuseStep 3347681 = 2510761) B2510761
theorem B2231787 : Blo 2231435 2231787 := bstep (se 1 (by rfl) ⟨1673840, by rfl⟩ : syracuseStep 2231787 = 3347681) B3347681
theorem B4132253 : Blo 2231435 4132253 := bbase (se 3 (by rfl) ⟨774797, by rfl⟩ : syracuseStep 4132253 = 1549595) (by norm_num)
theorem B11019341 : Blo 2231435 11019341 := bstep (se 3 (by rfl) ⟨2066126, by rfl⟩ : syracuseStep 11019341 = 4132253) B4132253
theorem B29384909 : Blo 2231435 29384909 := bstep (se 3 (by rfl) ⟨5509670, by rfl⟩ : syracuseStep 29384909 = 11019341) B11019341
theorem B19589939 : Blo 2231435 19589939 := bstep (se 1 (by rfl) ⟨14692454, by rfl⟩ : syracuseStep 19589939 = 29384909) B29384909
theorem B13059959 : Blo 2231435 13059959 := bstep (se 1 (by rfl) ⟨9794969, by rfl⟩ : syracuseStep 13059959 = 19589939) B19589939
theorem B139306229 : Blo 2231435 139306229 := bstep (se 5 (by rfl) ⟨6529979, by rfl⟩ : syracuseStep 139306229 = 13059959) B13059959
theorem B92870819 : Blo 2231435 92870819 := bstep (se 1 (by rfl) ⟨69653114, by rfl⟩ : syracuseStep 92870819 = 139306229) B139306229
theorem B61913879 : Blo 2231435 61913879 := bstep (se 1 (by rfl) ⟨46435409, by rfl⟩ : syracuseStep 61913879 = 92870819) B92870819
theorem B41275919 : Blo 2231435 41275919 := bstep (se 1 (by rfl) ⟨30956939, by rfl⟩ : syracuseStep 41275919 = 61913879) B61913879
theorem B27517279 : Blo 2231435 27517279 := bstep (se 1 (by rfl) ⟨20637959, by rfl⟩ : syracuseStep 27517279 = 41275919) B41275919
theorem B36689705 : Blo 2231435 36689705 := bstep (se 2 (by rfl) ⟨13758639, by rfl⟩ : syracuseStep 36689705 = 27517279) B27517279
theorem B24459803 : Blo 2231435 24459803 := bstep (se 1 (by rfl) ⟨18344852, by rfl⟩ : syracuseStep 24459803 = 36689705) B36689705
theorem B16306535 : Blo 2231435 16306535 := bstep (se 1 (by rfl) ⟨12229901, by rfl⟩ : syracuseStep 16306535 = 24459803) B24459803
theorem B10871023 : Blo 2231435 10871023 := bstep (se 1 (by rfl) ⟨8153267, by rfl⟩ : syracuseStep 10871023 = 16306535) B16306535
theorem B14494697 : Blo 2231435 14494697 := bstep (se 2 (by rfl) ⟨5435511, by rfl⟩ : syracuseStep 14494697 = 10871023) B10871023
theorem B9663131 : Blo 2231435 9663131 := bstep (se 1 (by rfl) ⟨7247348, by rfl⟩ : syracuseStep 9663131 = 14494697) B14494697
theorem B6442087 : Blo 2231435 6442087 := bstep (se 1 (by rfl) ⟨4831565, by rfl⟩ : syracuseStep 6442087 = 9663131) B9663131
theorem B8589449 : Blo 2231435 8589449 := bstep (se 2 (by rfl) ⟨3221043, by rfl⟩ : syracuseStep 8589449 = 6442087) B6442087
theorem B5726299 : Blo 2231435 5726299 := bstep (se 1 (by rfl) ⟨4294724, by rfl⟩ : syracuseStep 5726299 = 8589449) B8589449
theorem B7635065 : Blo 2231435 7635065 := bstep (se 2 (by rfl) ⟨2863149, by rfl⟩ : syracuseStep 7635065 = 5726299) B5726299
theorem B20360173 : Blo 2231435 20360173 := bstep (se 3 (by rfl) ⟨3817532, by rfl⟩ : syracuseStep 20360173 = 7635065) B7635065
theorem B27146897 : Blo 2231435 27146897 := bstep (se 2 (by rfl) ⟨10180086, by rfl⟩ : syracuseStep 27146897 = 20360173) B20360173
theorem B18097931 : Blo 2231435 18097931 := bstep (se 1 (by rfl) ⟨13573448, by rfl⟩ : syracuseStep 18097931 = 27146897) B27146897
theorem B12065287 : Blo 2231435 12065287 := bstep (se 1 (by rfl) ⟨9048965, by rfl⟩ : syracuseStep 12065287 = 18097931) B18097931
theorem B16087049 : Blo 2231435 16087049 := bstep (se 2 (by rfl) ⟨6032643, by rfl⟩ : syracuseStep 16087049 = 12065287) B12065287
theorem B10724699 : Blo 2231435 10724699 := bstep (se 1 (by rfl) ⟨8043524, by rfl⟩ : syracuseStep 10724699 = 16087049) B16087049
theorem B7149799 : Blo 2231435 7149799 := bstep (se 1 (by rfl) ⟨5362349, by rfl⟩ : syracuseStep 7149799 = 10724699) B10724699
theorem B9533065 : Blo 2231435 9533065 := bstep (se 2 (by rfl) ⟨3574899, by rfl⟩ : syracuseStep 9533065 = 7149799) B7149799
theorem B12710753 : Blo 2231435 12710753 := bstep (se 2 (by rfl) ⟨4766532, by rfl⟩ : syracuseStep 12710753 = 9533065) B9533065
theorem B8473835 : Blo 2231435 8473835 := bstep (se 1 (by rfl) ⟨6355376, by rfl⟩ : syracuseStep 8473835 = 12710753) B12710753
theorem B5649223 : Blo 2231435 5649223 := bstep (se 1 (by rfl) ⟨4236917, by rfl⟩ : syracuseStep 5649223 = 8473835) B8473835
theorem B7532297 : Blo 2231435 7532297 := bstep (se 2 (by rfl) ⟨2824611, by rfl⟩ : syracuseStep 7532297 = 5649223) B5649223
theorem B5021531 : Blo 2231435 5021531 := bstep (se 1 (by rfl) ⟨3766148, by rfl⟩ : syracuseStep 5021531 = 7532297) B7532297
theorem B3347687 : Blo 2231435 3347687 := bstep (se 1 (by rfl) ⟨2510765, by rfl⟩ : syracuseStep 3347687 = 5021531) B5021531
theorem B2231791 : Blo 2231435 2231791 := bstep (se 1 (by rfl) ⟨1673843, by rfl⟩ : syracuseStep 2231791 = 3347687) B3347687
theorem B3347693 : Blo 2231435 3347693 := bbase (se 3 (by rfl) ⟨627692, by rfl⟩ : syracuseStep 3347693 = 1255385) (by norm_num)
theorem B2231795 : Blo 2231435 2231795 := bstep (se 1 (by rfl) ⟨1673846, by rfl⟩ : syracuseStep 2231795 = 3347693) B3347693
theorem B5021549 : Blo 2231435 5021549 := bbase (se 3 (by rfl) ⟨941540, by rfl⟩ : syracuseStep 5021549 = 1883081) (by norm_num)
theorem B3347699 : Blo 2231435 3347699 := bstep (se 1 (by rfl) ⟨2510774, by rfl⟩ : syracuseStep 3347699 = 5021549) B5021549
theorem B2231799 : Blo 2231435 2231799 := bstep (se 1 (by rfl) ⟨1673849, by rfl⟩ : syracuseStep 2231799 = 3347699) B3347699
theorem B4236941 : Blo 2231435 4236941 := bbase (se 3 (by rfl) ⟨794426, by rfl⟩ : syracuseStep 4236941 = 1588853) (by norm_num)
theorem B2824627 : Blo 2231435 2824627 := bstep (se 1 (by rfl) ⟨2118470, by rfl⟩ : syracuseStep 2824627 = 4236941) B4236941
theorem B3766169 : Blo 2231435 3766169 := bstep (se 2 (by rfl) ⟨1412313, by rfl⟩ : syracuseStep 3766169 = 2824627) B2824627
theorem B2510779 : Blo 2231435 2510779 := bstep (se 1 (by rfl) ⟨1883084, by rfl⟩ : syracuseStep 2510779 = 3766169) B3766169
theorem B3347705 : Blo 2231435 3347705 := bstep (se 2 (by rfl) ⟨1255389, by rfl⟩ : syracuseStep 3347705 = 2510779) B2510779
theorem B2231803 : Blo 2231435 2231803 := bstep (se 1 (by rfl) ⟨1673852, by rfl⟩ : syracuseStep 2231803 = 3347705) B3347705
theorem B6786773 : Blo 2231435 6786773 := bbase (se 7 (by rfl) ⟨79532, by rfl⟩ : syracuseStep 6786773 = 159065) (by norm_num)
theorem B4524515 : Blo 2231435 4524515 := bstep (se 1 (by rfl) ⟨3393386, by rfl⟩ : syracuseStep 4524515 = 6786773) B6786773
theorem B3016343 : Blo 2231435 3016343 := bstep (se 1 (by rfl) ⟨2262257, by rfl⟩ : syracuseStep 3016343 = 4524515) B4524515
theorem B8043581 : Blo 2231435 8043581 := bstep (se 3 (by rfl) ⟨1508171, by rfl⟩ : syracuseStep 8043581 = 3016343) B3016343
theorem B21449549 : Blo 2231435 21449549 := bstep (se 3 (by rfl) ⟨4021790, by rfl⟩ : syracuseStep 21449549 = 8043581) B8043581
theorem B57198797 : Blo 2231435 57198797 := bstep (se 3 (by rfl) ⟨10724774, by rfl⟩ : syracuseStep 57198797 = 21449549) B21449549
theorem B38132531 : Blo 2231435 38132531 := bstep (se 1 (by rfl) ⟨28599398, by rfl⟩ : syracuseStep 38132531 = 57198797) B57198797
theorem B25421687 : Blo 2231435 25421687 := bstep (se 1 (by rfl) ⟨19066265, by rfl⟩ : syracuseStep 25421687 = 38132531) B38132531
theorem B16947791 : Blo 2231435 16947791 := bstep (se 1 (by rfl) ⟨12710843, by rfl⟩ : syracuseStep 16947791 = 25421687) B25421687
theorem B11298527 : Blo 2231435 11298527 := bstep (se 1 (by rfl) ⟨8473895, by rfl⟩ : syracuseStep 11298527 = 16947791) B16947791
theorem B7532351 : Blo 2231435 7532351 := bstep (se 1 (by rfl) ⟨5649263, by rfl⟩ : syracuseStep 7532351 = 11298527) B11298527
theorem B5021567 : Blo 2231435 5021567 := bstep (se 1 (by rfl) ⟨3766175, by rfl⟩ : syracuseStep 5021567 = 7532351) B7532351
theorem B3347711 : Blo 2231435 3347711 := bstep (se 1 (by rfl) ⟨2510783, by rfl⟩ : syracuseStep 3347711 = 5021567) B5021567
theorem B2231807 : Blo 2231435 2231807 := bstep (se 1 (by rfl) ⟨1673855, by rfl⟩ : syracuseStep 2231807 = 3347711) B3347711
theorem B3347717 : Blo 2231435 3347717 := bbase (se 4 (by rfl) ⟨313848, by rfl⟩ : syracuseStep 3347717 = 627697) (by norm_num)
theorem B2231811 : Blo 2231435 2231811 := bstep (se 1 (by rfl) ⟨1673858, by rfl⟩ : syracuseStep 2231811 = 3347717) B3347717
theorem B3766189 : Blo 2231435 3766189 := bbase (se 3 (by rfl) ⟨706160, by rfl⟩ : syracuseStep 3766189 = 1412321) (by norm_num)
theorem B5021585 : Blo 2231435 5021585 := bstep (se 2 (by rfl) ⟨1883094, by rfl⟩ : syracuseStep 5021585 = 3766189) B3766189
theorem B3347723 : Blo 2231435 3347723 := bstep (se 1 (by rfl) ⟨2510792, by rfl⟩ : syracuseStep 3347723 = 5021585) B5021585
theorem B2231815 : Blo 2231435 2231815 := bstep (se 1 (by rfl) ⟨1673861, by rfl⟩ : syracuseStep 2231815 = 3347723) B3347723
theorem B2510797 : Blo 2231435 2510797 := bbase (se 3 (by rfl) ⟨470774, by rfl⟩ : syracuseStep 2510797 = 941549) (by norm_num)
theorem B3347729 : Blo 2231435 3347729 := bstep (se 2 (by rfl) ⟨1255398, by rfl⟩ : syracuseStep 3347729 = 2510797) B2510797
theorem B2231819 : Blo 2231435 2231819 := bstep (se 1 (by rfl) ⟨1673864, by rfl⟩ : syracuseStep 2231819 = 3347729) B3347729
theorem B7532405 : Blo 2231435 7532405 := bbase (se 5 (by rfl) ⟨353081, by rfl⟩ : syracuseStep 7532405 = 706163) (by norm_num)
theorem B5021603 : Blo 2231435 5021603 := bstep (se 1 (by rfl) ⟨3766202, by rfl⟩ : syracuseStep 5021603 = 7532405) B7532405
theorem B3347735 : Blo 2231435 3347735 := bstep (se 1 (by rfl) ⟨2510801, by rfl⟩ : syracuseStep 3347735 = 5021603) B5021603
theorem B2231823 : Blo 2231435 2231823 := bstep (se 1 (by rfl) ⟨1673867, by rfl⟩ : syracuseStep 2231823 = 3347735) B3347735
theorem B3347741 : Blo 2231435 3347741 := bbase (se 3 (by rfl) ⟨627701, by rfl⟩ : syracuseStep 3347741 = 1255403) (by norm_num)
theorem B2231827 : Blo 2231435 2231827 := bstep (se 1 (by rfl) ⟨1673870, by rfl⟩ : syracuseStep 2231827 = 3347741) B3347741
theorem B5021621 : Blo 2231435 5021621 := bbase (se 5 (by rfl) ⟨235388, by rfl⟩ : syracuseStep 5021621 = 470777) (by norm_num)
theorem B3347747 : Blo 2231435 3347747 := bstep (se 1 (by rfl) ⟨2510810, by rfl⟩ : syracuseStep 3347747 = 5021621) B5021621
theorem B2231831 : Blo 2231435 2231831 := bstep (se 1 (by rfl) ⟨1673873, by rfl⟩ : syracuseStep 2231831 = 3347747) B3347747
theorem B7149941 : Blo 2231435 7149941 := bbase (se 5 (by rfl) ⟨335153, by rfl⟩ : syracuseStep 7149941 = 670307) (by norm_num)
theorem B4766627 : Blo 2231435 4766627 := bstep (se 1 (by rfl) ⟨3574970, by rfl⟩ : syracuseStep 4766627 = 7149941) B7149941
theorem B12711005 : Blo 2231435 12711005 := bstep (se 3 (by rfl) ⟨2383313, by rfl⟩ : syracuseStep 12711005 = 4766627) B4766627
theorem B8474003 : Blo 2231435 8474003 := bstep (se 1 (by rfl) ⟨6355502, by rfl⟩ : syracuseStep 8474003 = 12711005) B12711005
theorem B5649335 : Blo 2231435 5649335 := bstep (se 1 (by rfl) ⟨4237001, by rfl⟩ : syracuseStep 5649335 = 8474003) B8474003
theorem B3766223 : Blo 2231435 3766223 := bstep (se 1 (by rfl) ⟨2824667, by rfl⟩ : syracuseStep 3766223 = 5649335) B5649335
theorem B2510815 : Blo 2231435 2510815 := bstep (se 1 (by rfl) ⟨1883111, by rfl⟩ : syracuseStep 2510815 = 3766223) B3766223
theorem B3347753 : Blo 2231435 3347753 := bstep (se 2 (by rfl) ⟨1255407, by rfl⟩ : syracuseStep 3347753 = 2510815) B2510815
theorem B2231835 : Blo 2231435 2231835 := bstep (se 1 (by rfl) ⟨1673876, by rfl⟩ : syracuseStep 2231835 = 3347753) B3347753
theorem B4524581 : Blo 2231435 4524581 := bbase (se 4 (by rfl) ⟨424179, by rfl⟩ : syracuseStep 4524581 = 848359) (by norm_num)
theorem B3016387 : Blo 2231435 3016387 := bstep (se 1 (by rfl) ⟨2262290, by rfl⟩ : syracuseStep 3016387 = 4524581) B4524581
theorem B4021849 : Blo 2231435 4021849 := bstep (se 2 (by rfl) ⟨1508193, by rfl⟩ : syracuseStep 4021849 = 3016387) B3016387
theorem B5362465 : Blo 2231435 5362465 := bstep (se 2 (by rfl) ⟨2010924, by rfl⟩ : syracuseStep 5362465 = 4021849) B4021849
theorem B7149953 : Blo 2231435 7149953 := bstep (se 2 (by rfl) ⟨2681232, by rfl⟩ : syracuseStep 7149953 = 5362465) B5362465
theorem B4766635 : Blo 2231435 4766635 := bstep (se 1 (by rfl) ⟨3574976, by rfl⟩ : syracuseStep 4766635 = 7149953) B7149953
theorem B6355513 : Blo 2231435 6355513 := bstep (se 2 (by rfl) ⟨2383317, by rfl⟩ : syracuseStep 6355513 = 4766635) B4766635
theorem B8474017 : Blo 2231435 8474017 := bstep (se 2 (by rfl) ⟨3177756, by rfl⟩ : syracuseStep 8474017 = 6355513) B6355513
theorem B11298689 : Blo 2231435 11298689 := bstep (se 2 (by rfl) ⟨4237008, by rfl⟩ : syracuseStep 11298689 = 8474017) B8474017
theorem B7532459 : Blo 2231435 7532459 := bstep (se 1 (by rfl) ⟨5649344, by rfl⟩ : syracuseStep 7532459 = 11298689) B11298689
theorem B5021639 : Blo 2231435 5021639 := bstep (se 1 (by rfl) ⟨3766229, by rfl⟩ : syracuseStep 5021639 = 7532459) B7532459
theorem B3347759 : Blo 2231435 3347759 := bstep (se 1 (by rfl) ⟨2510819, by rfl⟩ : syracuseStep 3347759 = 5021639) B5021639
theorem B2231839 : Blo 2231435 2231839 := bstep (se 1 (by rfl) ⟨1673879, by rfl⟩ : syracuseStep 2231839 = 3347759) B3347759
theorem B3347765 : Blo 2231435 3347765 := bbase (se 5 (by rfl) ⟨156926, by rfl⟩ : syracuseStep 3347765 = 313853) (by norm_num)
theorem B2231843 : Blo 2231435 2231843 := bstep (se 1 (by rfl) ⟨1673882, by rfl⟩ : syracuseStep 2231843 = 3347765) B3347765
theorem B5649365 : Blo 2231435 5649365 := bbase (se 7 (by rfl) ⟨66203, by rfl⟩ : syracuseStep 5649365 = 132407) (by norm_num)
theorem B3766243 : Blo 2231435 3766243 := bstep (se 1 (by rfl) ⟨2824682, by rfl⟩ : syracuseStep 3766243 = 5649365) B5649365
theorem B5021657 : Blo 2231435 5021657 := bstep (se 2 (by rfl) ⟨1883121, by rfl⟩ : syracuseStep 5021657 = 3766243) B3766243
theorem B3347771 : Blo 2231435 3347771 := bstep (se 1 (by rfl) ⟨2510828, by rfl⟩ : syracuseStep 3347771 = 5021657) B5021657
theorem B2231847 : Blo 2231435 2231847 := bstep (se 1 (by rfl) ⟨1673885, by rfl⟩ : syracuseStep 2231847 = 3347771) B3347771
theorem B2510833 : Blo 2231435 2510833 := bbase (se 2 (by rfl) ⟨941562, by rfl⟩ : syracuseStep 2510833 = 1883125) (by norm_num)
theorem B3347777 : Blo 2231435 3347777 := bstep (se 2 (by rfl) ⟨1255416, by rfl⟩ : syracuseStep 3347777 = 2510833) B2510833
theorem B2231851 : Blo 2231435 2231851 := bstep (se 1 (by rfl) ⟨1673888, by rfl⟩ : syracuseStep 2231851 = 3347777) B3347777
theorem B10747429 : Blo 2231435 10747429 := bbase (se 4 (by rfl) ⟨1007571, by rfl⟩ : syracuseStep 10747429 = 2015143) (by norm_num)
theorem B229278485 : Blo 2231435 229278485 := bstep (se 6 (by rfl) ⟨5373714, by rfl⟩ : syracuseStep 229278485 = 10747429) B10747429
theorem B611409293 : Blo 2231435 611409293 := bstep (se 3 (by rfl) ⟨114639242, by rfl⟩ : syracuseStep 611409293 = 229278485) B229278485
theorem B407606195 : Blo 2231435 407606195 := bstep (se 1 (by rfl) ⟨305704646, by rfl⟩ : syracuseStep 407606195 = 611409293) B611409293
theorem B1086949853 : Blo 2231435 1086949853 := bstep (se 3 (by rfl) ⟨203803097, by rfl⟩ : syracuseStep 1086949853 = 407606195) B407606195
theorem B724633235 : Blo 2231435 724633235 := bstep (se 1 (by rfl) ⟨543474926, by rfl⟩ : syracuseStep 724633235 = 1086949853) B1086949853
theorem B483088823 : Blo 2231435 483088823 := bstep (se 1 (by rfl) ⟨362316617, by rfl⟩ : syracuseStep 483088823 = 724633235) B724633235
theorem B322059215 : Blo 2231435 322059215 := bstep (se 1 (by rfl) ⟨241544411, by rfl⟩ : syracuseStep 322059215 = 483088823) B483088823
theorem B214706143 : Blo 2231435 214706143 := bstep (se 1 (by rfl) ⟨161029607, by rfl⟩ : syracuseStep 214706143 = 322059215) B322059215
theorem B286274857 : Blo 2231435 286274857 := bstep (se 2 (by rfl) ⟨107353071, by rfl⟩ : syracuseStep 286274857 = 214706143) B214706143
theorem B381699809 : Blo 2231435 381699809 := bstep (se 2 (by rfl) ⟨143137428, by rfl⟩ : syracuseStep 381699809 = 286274857) B286274857
theorem B254466539 : Blo 2231435 254466539 := bstep (se 1 (by rfl) ⟨190849904, by rfl⟩ : syracuseStep 254466539 = 381699809) B381699809
theorem B169644359 : Blo 2231435 169644359 := bstep (se 1 (by rfl) ⟨127233269, by rfl⟩ : syracuseStep 169644359 = 254466539) B254466539
theorem B452384957 : Blo 2231435 452384957 := bstep (se 3 (by rfl) ⟨84822179, by rfl⟩ : syracuseStep 452384957 = 169644359) B169644359
theorem B1206359885 : Blo 2231435 1206359885 := bstep (se 3 (by rfl) ⟨226192478, by rfl⟩ : syracuseStep 1206359885 = 452384957) B452384957
theorem B804239923 : Blo 2231435 804239923 := bstep (se 1 (by rfl) ⟨603179942, by rfl⟩ : syracuseStep 804239923 = 1206359885) B1206359885
theorem B1072319897 : Blo 2231435 1072319897 := bstep (se 2 (by rfl) ⟨402119961, by rfl⟩ : syracuseStep 1072319897 = 804239923) B804239923
theorem B714879931 : Blo 2231435 714879931 := bstep (se 1 (by rfl) ⟨536159948, by rfl⟩ : syracuseStep 714879931 = 1072319897) B1072319897
theorem B953173241 : Blo 2231435 953173241 := bstep (se 2 (by rfl) ⟨357439965, by rfl⟩ : syracuseStep 953173241 = 714879931) B714879931
theorem B635448827 : Blo 2231435 635448827 := bstep (se 1 (by rfl) ⟨476586620, by rfl⟩ : syracuseStep 635448827 = 953173241) B953173241
theorem B423632551 : Blo 2231435 423632551 := bstep (se 1 (by rfl) ⟨317724413, by rfl⟩ : syracuseStep 423632551 = 635448827) B635448827
theorem B564843401 : Blo 2231435 564843401 := bstep (se 2 (by rfl) ⟨211816275, by rfl⟩ : syracuseStep 564843401 = 423632551) B423632551
theorem B376562267 : Blo 2231435 376562267 := bstep (se 1 (by rfl) ⟨282421700, by rfl⟩ : syracuseStep 376562267 = 564843401) B564843401
theorem B251041511 : Blo 2231435 251041511 := bstep (se 1 (by rfl) ⟨188281133, by rfl⟩ : syracuseStep 251041511 = 376562267) B376562267
theorem B167361007 : Blo 2231435 167361007 := bstep (se 1 (by rfl) ⟨125520755, by rfl⟩ : syracuseStep 167361007 = 251041511) B251041511
theorem B223148009 : Blo 2231435 223148009 := bstep (se 2 (by rfl) ⟨83680503, by rfl⟩ : syracuseStep 223148009 = 167361007) B167361007
theorem B148765339 : Blo 2231435 148765339 := bstep (se 1 (by rfl) ⟨111574004, by rfl⟩ : syracuseStep 148765339 = 223148009) B223148009
theorem B198353785 : Blo 2231435 198353785 := bstep (se 2 (by rfl) ⟨74382669, by rfl⟩ : syracuseStep 198353785 = 148765339) B148765339
theorem B264471713 : Blo 2231435 264471713 := bstep (se 2 (by rfl) ⟨99176892, by rfl⟩ : syracuseStep 264471713 = 198353785) B198353785
theorem B176314475 : Blo 2231435 176314475 := bstep (se 1 (by rfl) ⟨132235856, by rfl⟩ : syracuseStep 176314475 = 264471713) B264471713
theorem B117542983 : Blo 2231435 117542983 := bstep (se 1 (by rfl) ⟨88157237, by rfl⟩ : syracuseStep 117542983 = 176314475) B176314475
theorem B156723977 : Blo 2231435 156723977 := bstep (se 2 (by rfl) ⟨58771491, by rfl⟩ : syracuseStep 156723977 = 117542983) B117542983
theorem B104482651 : Blo 2231435 104482651 := bstep (se 1 (by rfl) ⟨78361988, by rfl⟩ : syracuseStep 104482651 = 156723977) B156723977
theorem B139310201 : Blo 2231435 139310201 := bstep (se 2 (by rfl) ⟨52241325, by rfl⟩ : syracuseStep 139310201 = 104482651) B104482651
theorem B92873467 : Blo 2231435 92873467 := bstep (se 1 (by rfl) ⟨69655100, by rfl⟩ : syracuseStep 92873467 = 139310201) B139310201
theorem B123831289 : Blo 2231435 123831289 := bstep (se 2 (by rfl) ⟨46436733, by rfl⟩ : syracuseStep 123831289 = 92873467) B92873467
theorem B165108385 : Blo 2231435 165108385 := bstep (se 2 (by rfl) ⟨61915644, by rfl⟩ : syracuseStep 165108385 = 123831289) B123831289
theorem B220144513 : Blo 2231435 220144513 := bstep (se 2 (by rfl) ⟨82554192, by rfl⟩ : syracuseStep 220144513 = 165108385) B165108385
theorem B293526017 : Blo 2231435 293526017 := bstep (se 2 (by rfl) ⟨110072256, by rfl⟩ : syracuseStep 293526017 = 220144513) B220144513
theorem B195684011 : Blo 2231435 195684011 := bstep (se 1 (by rfl) ⟨146763008, by rfl⟩ : syracuseStep 195684011 = 293526017) B293526017
theorem B130456007 : Blo 2231435 130456007 := bstep (se 1 (by rfl) ⟨97842005, by rfl⟩ : syracuseStep 130456007 = 195684011) B195684011
theorem B86970671 : Blo 2231435 86970671 := bstep (se 1 (by rfl) ⟨65228003, by rfl⟩ : syracuseStep 86970671 = 130456007) B130456007
theorem B57980447 : Blo 2231435 57980447 := bstep (se 1 (by rfl) ⟨43485335, by rfl⟩ : syracuseStep 57980447 = 86970671) B86970671
theorem B38653631 : Blo 2231435 38653631 := bstep (se 1 (by rfl) ⟨28990223, by rfl⟩ : syracuseStep 38653631 = 57980447) B57980447
theorem B25769087 : Blo 2231435 25769087 := bstep (se 1 (by rfl) ⟨19326815, by rfl⟩ : syracuseStep 25769087 = 38653631) B38653631
theorem B17179391 : Blo 2231435 17179391 := bstep (se 1 (by rfl) ⟨12884543, by rfl⟩ : syracuseStep 17179391 = 25769087) B25769087
theorem B11452927 : Blo 2231435 11452927 := bstep (se 1 (by rfl) ⟨8589695, by rfl⟩ : syracuseStep 11452927 = 17179391) B17179391
theorem B15270569 : Blo 2231435 15270569 := bstep (se 2 (by rfl) ⟨5726463, by rfl⟩ : syracuseStep 15270569 = 11452927) B11452927
theorem B10180379 : Blo 2231435 10180379 := bstep (se 1 (by rfl) ⟨7635284, by rfl⟩ : syracuseStep 10180379 = 15270569) B15270569
theorem B6786919 : Blo 2231435 6786919 := bstep (se 1 (by rfl) ⟨5090189, by rfl⟩ : syracuseStep 6786919 = 10180379) B10180379
theorem B36196901 : Blo 2231435 36196901 := bstep (se 4 (by rfl) ⟨3393459, by rfl⟩ : syracuseStep 36196901 = 6786919) B6786919
theorem B24131267 : Blo 2231435 24131267 := bstep (se 1 (by rfl) ⟨18098450, by rfl⟩ : syracuseStep 24131267 = 36196901) B36196901
theorem B16087511 : Blo 2231435 16087511 := bstep (se 1 (by rfl) ⟨12065633, by rfl⟩ : syracuseStep 16087511 = 24131267) B24131267
theorem B10725007 : Blo 2231435 10725007 := bstep (se 1 (by rfl) ⟨8043755, by rfl⟩ : syracuseStep 10725007 = 16087511) B16087511
theorem B14300009 : Blo 2231435 14300009 := bstep (se 2 (by rfl) ⟨5362503, by rfl⟩ : syracuseStep 14300009 = 10725007) B10725007
theorem B9533339 : Blo 2231435 9533339 := bstep (se 1 (by rfl) ⟨7150004, by rfl⟩ : syracuseStep 9533339 = 14300009) B14300009
theorem B6355559 : Blo 2231435 6355559 := bstep (se 1 (by rfl) ⟨4766669, by rfl⟩ : syracuseStep 6355559 = 9533339) B9533339
theorem B4237039 : Blo 2231435 4237039 := bstep (se 1 (by rfl) ⟨3177779, by rfl⟩ : syracuseStep 4237039 = 6355559) B6355559
theorem B5649385 : Blo 2231435 5649385 := bstep (se 2 (by rfl) ⟨2118519, by rfl⟩ : syracuseStep 5649385 = 4237039) B4237039
theorem B7532513 : Blo 2231435 7532513 := bstep (se 2 (by rfl) ⟨2824692, by rfl⟩ : syracuseStep 7532513 = 5649385) B5649385
theorem B5021675 : Blo 2231435 5021675 := bstep (se 1 (by rfl) ⟨3766256, by rfl⟩ : syracuseStep 5021675 = 7532513) B7532513
theorem B3347783 : Blo 2231435 3347783 := bstep (se 1 (by rfl) ⟨2510837, by rfl⟩ : syracuseStep 3347783 = 5021675) B5021675
theorem B2231855 : Blo 2231435 2231855 := bstep (se 1 (by rfl) ⟨1673891, by rfl⟩ : syracuseStep 2231855 = 3347783) B3347783
theorem B3347789 : Blo 2231435 3347789 := bbase (se 3 (by rfl) ⟨627710, by rfl⟩ : syracuseStep 3347789 = 1255421) (by norm_num)
theorem B2231859 : Blo 2231435 2231859 := bstep (se 1 (by rfl) ⟨1673894, by rfl⟩ : syracuseStep 2231859 = 3347789) B3347789
theorem B5021693 : Blo 2231435 5021693 := bbase (se 3 (by rfl) ⟨941567, by rfl⟩ : syracuseStep 5021693 = 1883135) (by norm_num)
theorem B3347795 : Blo 2231435 3347795 := bstep (se 1 (by rfl) ⟨2510846, by rfl⟩ : syracuseStep 3347795 = 5021693) B5021693
theorem B2231863 : Blo 2231435 2231863 := bstep (se 1 (by rfl) ⟨1673897, by rfl⟩ : syracuseStep 2231863 = 3347795) B3347795
theorem B3766277 : Blo 2231435 3766277 := bbase (se 4 (by rfl) ⟨353088, by rfl⟩ : syracuseStep 3766277 = 706177) (by norm_num)
theorem B2510851 : Blo 2231435 2510851 := bstep (se 1 (by rfl) ⟨1883138, by rfl⟩ : syracuseStep 2510851 = 3766277) B3766277
theorem B3347801 : Blo 2231435 3347801 := bstep (se 2 (by rfl) ⟨1255425, by rfl⟩ : syracuseStep 3347801 = 2510851) B2510851
theorem B2231867 : Blo 2231435 2231867 := bstep (se 1 (by rfl) ⟨1673900, by rfl⟩ : syracuseStep 2231867 = 3347801) B3347801
theorem B16948277 : Blo 2231435 16948277 := bbase (se 5 (by rfl) ⟨794450, by rfl⟩ : syracuseStep 16948277 = 1588901) (by norm_num)
theorem B11298851 : Blo 2231435 11298851 := bstep (se 1 (by rfl) ⟨8474138, by rfl⟩ : syracuseStep 11298851 = 16948277) B16948277
theorem B7532567 : Blo 2231435 7532567 := bstep (se 1 (by rfl) ⟨5649425, by rfl⟩ : syracuseStep 7532567 = 11298851) B11298851
theorem B5021711 : Blo 2231435 5021711 := bstep (se 1 (by rfl) ⟨3766283, by rfl⟩ : syracuseStep 5021711 = 7532567) B7532567
theorem B3347807 : Blo 2231435 3347807 := bstep (se 1 (by rfl) ⟨2510855, by rfl⟩ : syracuseStep 3347807 = 5021711) B5021711
theorem B2231871 : Blo 2231435 2231871 := bstep (se 1 (by rfl) ⟨1673903, by rfl⟩ : syracuseStep 2231871 = 3347807) B3347807
theorem B3347813 : Blo 2231435 3347813 := bbase (se 4 (by rfl) ⟨313857, by rfl⟩ : syracuseStep 3347813 = 627715) (by norm_num)
theorem B2231875 : Blo 2231435 2231875 := bstep (se 1 (by rfl) ⟨1673906, by rfl⟩ : syracuseStep 2231875 = 3347813) B3347813
theorem B4237085 : Blo 2231435 4237085 := bbase (se 3 (by rfl) ⟨794453, by rfl⟩ : syracuseStep 4237085 = 1588907) (by norm_num)
theorem B2824723 : Blo 2231435 2824723 := bstep (se 1 (by rfl) ⟨2118542, by rfl⟩ : syracuseStep 2824723 = 4237085) B4237085
theorem B3766297 : Blo 2231435 3766297 := bstep (se 2 (by rfl) ⟨1412361, by rfl⟩ : syracuseStep 3766297 = 2824723) B2824723
theorem B5021729 : Blo 2231435 5021729 := bstep (se 2 (by rfl) ⟨1883148, by rfl⟩ : syracuseStep 5021729 = 3766297) B3766297
theorem B3347819 : Blo 2231435 3347819 := bstep (se 1 (by rfl) ⟨2510864, by rfl⟩ : syracuseStep 3347819 = 5021729) B5021729
theorem B2231879 : Blo 2231435 2231879 := bstep (se 1 (by rfl) ⟨1673909, by rfl⟩ : syracuseStep 2231879 = 3347819) B3347819
theorem B2510869 : Blo 2231435 2510869 := bbase (se 6 (by rfl) ⟨58848, by rfl⟩ : syracuseStep 2510869 = 117697) (by norm_num)
theorem B3347825 : Blo 2231435 3347825 := bstep (se 2 (by rfl) ⟨1255434, by rfl⟩ : syracuseStep 3347825 = 2510869) B2510869
theorem B2231883 : Blo 2231435 2231883 := bstep (se 1 (by rfl) ⟨1673912, by rfl⟩ : syracuseStep 2231883 = 3347825) B3347825
theorem B2824733 : Blo 2231435 2824733 := bbase (se 3 (by rfl) ⟨529637, by rfl⟩ : syracuseStep 2824733 = 1059275) (by norm_num)
theorem B7532621 : Blo 2231435 7532621 := bstep (se 3 (by rfl) ⟨1412366, by rfl⟩ : syracuseStep 7532621 = 2824733) B2824733
theorem B5021747 : Blo 2231435 5021747 := bstep (se 1 (by rfl) ⟨3766310, by rfl⟩ : syracuseStep 5021747 = 7532621) B7532621
theorem B3347831 : Blo 2231435 3347831 := bstep (se 1 (by rfl) ⟨2510873, by rfl⟩ : syracuseStep 3347831 = 5021747) B5021747
theorem B2231887 : Blo 2231435 2231887 := bstep (se 1 (by rfl) ⟨1673915, by rfl⟩ : syracuseStep 2231887 = 3347831) B3347831
theorem B3347837 : Blo 2231435 3347837 := bbase (se 3 (by rfl) ⟨627719, by rfl⟩ : syracuseStep 3347837 = 1255439) (by norm_num)
theorem B2231891 : Blo 2231435 2231891 := bstep (se 1 (by rfl) ⟨1673918, by rfl⟩ : syracuseStep 2231891 = 3347837) B3347837
theorem B5021765 : Blo 2231435 5021765 := bbase (se 4 (by rfl) ⟨470790, by rfl⟩ : syracuseStep 5021765 = 941581) (by norm_num)
theorem B3347843 : Blo 2231435 3347843 := bstep (se 1 (by rfl) ⟨2510882, by rfl⟩ : syracuseStep 3347843 = 5021765) B5021765
theorem B2231895 : Blo 2231435 2231895 := bstep (se 1 (by rfl) ⟨1673921, by rfl⟩ : syracuseStep 2231895 = 3347843) B3347843
theorem B6355685 : Blo 2231435 6355685 := bbase (se 4 (by rfl) ⟨595845, by rfl⟩ : syracuseStep 6355685 = 1191691) (by norm_num)
theorem B4237123 : Blo 2231435 4237123 := bstep (se 1 (by rfl) ⟨3177842, by rfl⟩ : syracuseStep 4237123 = 6355685) B6355685
theorem B5649497 : Blo 2231435 5649497 := bstep (se 2 (by rfl) ⟨2118561, by rfl⟩ : syracuseStep 5649497 = 4237123) B4237123
theorem B3766331 : Blo 2231435 3766331 := bstep (se 1 (by rfl) ⟨2824748, by rfl⟩ : syracuseStep 3766331 = 5649497) B5649497
theorem B2510887 : Blo 2231435 2510887 := bstep (se 1 (by rfl) ⟨1883165, by rfl⟩ : syracuseStep 2510887 = 3766331) B3766331
theorem B3347849 : Blo 2231435 3347849 := bstep (se 2 (by rfl) ⟨1255443, by rfl⟩ : syracuseStep 3347849 = 2510887) B2510887
theorem B2231899 : Blo 2231435 2231899 := bstep (se 1 (by rfl) ⟨1673924, by rfl⟩ : syracuseStep 2231899 = 3347849) B3347849
theorem B11299013 : Blo 2231435 11299013 := bbase (se 4 (by rfl) ⟨1059282, by rfl⟩ : syracuseStep 11299013 = 2118565) (by norm_num)
theorem B7532675 : Blo 2231435 7532675 := bstep (se 1 (by rfl) ⟨5649506, by rfl⟩ : syracuseStep 7532675 = 11299013) B11299013
theorem B5021783 : Blo 2231435 5021783 := bstep (se 1 (by rfl) ⟨3766337, by rfl⟩ : syracuseStep 5021783 = 7532675) B7532675
theorem B3347855 : Blo 2231435 3347855 := bstep (se 1 (by rfl) ⟨2510891, by rfl⟩ : syracuseStep 3347855 = 5021783) B5021783
theorem B2231903 : Blo 2231435 2231903 := bstep (se 1 (by rfl) ⟨1673927, by rfl⟩ : syracuseStep 2231903 = 3347855) B3347855
theorem B3347861 : Blo 2231435 3347861 := bbase (se 6 (by rfl) ⟨78465, by rfl⟩ : syracuseStep 3347861 = 156931) (by norm_num)
theorem B2231907 : Blo 2231435 2231907 := bstep (se 1 (by rfl) ⟨1673930, by rfl⟩ : syracuseStep 2231907 = 3347861) B3347861
theorem B4766789 : Blo 2231435 4766789 := bbase (se 4 (by rfl) ⟨446886, by rfl⟩ : syracuseStep 4766789 = 893773) (by norm_num)
theorem B12711437 : Blo 2231435 12711437 := bstep (se 3 (by rfl) ⟨2383394, by rfl⟩ : syracuseStep 12711437 = 4766789) B4766789
theorem B8474291 : Blo 2231435 8474291 := bstep (se 1 (by rfl) ⟨6355718, by rfl⟩ : syracuseStep 8474291 = 12711437) B12711437
theorem B5649527 : Blo 2231435 5649527 := bstep (se 1 (by rfl) ⟨4237145, by rfl⟩ : syracuseStep 5649527 = 8474291) B8474291
theorem B3766351 : Blo 2231435 3766351 := bstep (se 1 (by rfl) ⟨2824763, by rfl⟩ : syracuseStep 3766351 = 5649527) B5649527
theorem B5021801 : Blo 2231435 5021801 := bstep (se 2 (by rfl) ⟨1883175, by rfl⟩ : syracuseStep 5021801 = 3766351) B3766351
theorem B3347867 : Blo 2231435 3347867 := bstep (se 1 (by rfl) ⟨2510900, by rfl⟩ : syracuseStep 3347867 = 5021801) B5021801
theorem B2231911 : Blo 2231435 2231911 := bstep (se 1 (by rfl) ⟨1673933, by rfl⟩ : syracuseStep 2231911 = 3347867) B3347867
theorem B2510905 : Blo 2231435 2510905 := bbase (se 2 (by rfl) ⟨941589, by rfl⟩ : syracuseStep 2510905 = 1883179) (by norm_num)
theorem B3347873 : Blo 2231435 3347873 := bstep (se 2 (by rfl) ⟨1255452, by rfl⟩ : syracuseStep 3347873 = 2510905) B2510905
theorem B2231915 : Blo 2231435 2231915 := bstep (se 1 (by rfl) ⟨1673936, by rfl⟩ : syracuseStep 2231915 = 3347873) B3347873
theorem B2681329 : Blo 2231435 2681329 := bbase (se 2 (by rfl) ⟨1005498, by rfl⟩ : syracuseStep 2681329 = 2010997) (by norm_num)
theorem B3575105 : Blo 2231435 3575105 := bstep (se 2 (by rfl) ⟨1340664, by rfl⟩ : syracuseStep 3575105 = 2681329) B2681329
theorem B2383403 : Blo 2231435 2383403 := bstep (se 1 (by rfl) ⟨1787552, by rfl⟩ : syracuseStep 2383403 = 3575105) B3575105
theorem B6355741 : Blo 2231435 6355741 := bstep (se 3 (by rfl) ⟨1191701, by rfl⟩ : syracuseStep 6355741 = 2383403) B2383403
theorem B8474321 : Blo 2231435 8474321 := bstep (se 2 (by rfl) ⟨3177870, by rfl⟩ : syracuseStep 8474321 = 6355741) B6355741
theorem B5649547 : Blo 2231435 5649547 := bstep (se 1 (by rfl) ⟨4237160, by rfl⟩ : syracuseStep 5649547 = 8474321) B8474321
theorem B7532729 : Blo 2231435 7532729 := bstep (se 2 (by rfl) ⟨2824773, by rfl⟩ : syracuseStep 7532729 = 5649547) B5649547
theorem B5021819 : Blo 2231435 5021819 := bstep (se 1 (by rfl) ⟨3766364, by rfl⟩ : syracuseStep 5021819 = 7532729) B7532729
theorem B3347879 : Blo 2231435 3347879 := bstep (se 1 (by rfl) ⟨2510909, by rfl⟩ : syracuseStep 3347879 = 5021819) B5021819
theorem B2231919 : Blo 2231435 2231919 := bstep (se 1 (by rfl) ⟨1673939, by rfl⟩ : syracuseStep 2231919 = 3347879) B3347879
theorem B3347885 : Blo 2231435 3347885 := bbase (se 3 (by rfl) ⟨627728, by rfl⟩ : syracuseStep 3347885 = 1255457) (by norm_num)
theorem B2231923 : Blo 2231435 2231923 := bstep (se 1 (by rfl) ⟨1673942, by rfl⟩ : syracuseStep 2231923 = 3347885) B3347885
theorem B5021837 : Blo 2231435 5021837 := bbase (se 3 (by rfl) ⟨941594, by rfl⟩ : syracuseStep 5021837 = 1883189) (by norm_num)
theorem B3347891 : Blo 2231435 3347891 := bstep (se 1 (by rfl) ⟨2510918, by rfl⟩ : syracuseStep 3347891 = 5021837) B5021837
theorem B2231927 : Blo 2231435 2231927 := bstep (se 1 (by rfl) ⟨1673945, by rfl⟩ : syracuseStep 2231927 = 3347891) B3347891
theorem B2824789 : Blo 2231435 2824789 := bbase (se 8 (by rfl) ⟨16551, by rfl⟩ : syracuseStep 2824789 = 33103) (by norm_num)
theorem B3766385 : Blo 2231435 3766385 := bstep (se 2 (by rfl) ⟨1412394, by rfl⟩ : syracuseStep 3766385 = 2824789) B2824789
theorem B2510923 : Blo 2231435 2510923 := bstep (se 1 (by rfl) ⟨1883192, by rfl⟩ : syracuseStep 2510923 = 3766385) B3766385
theorem B3347897 : Blo 2231435 3347897 := bstep (se 2 (by rfl) ⟨1255461, by rfl⟩ : syracuseStep 3347897 = 2510923) B2510923
theorem B2231931 : Blo 2231435 2231931 := bstep (se 1 (by rfl) ⟨1673948, by rfl⟩ : syracuseStep 2231931 = 3347897) B3347897
theorem B20639285 : Blo 2231435 20639285 := bbase (se 5 (by rfl) ⟨967466, by rfl⟩ : syracuseStep 20639285 = 1934933) (by norm_num)
theorem B13759523 : Blo 2231435 13759523 := bstep (se 1 (by rfl) ⟨10319642, by rfl⟩ : syracuseStep 13759523 = 20639285) B20639285
theorem B9173015 : Blo 2231435 9173015 := bstep (se 1 (by rfl) ⟨6879761, by rfl⟩ : syracuseStep 9173015 = 13759523) B13759523
theorem B6115343 : Blo 2231435 6115343 := bstep (se 1 (by rfl) ⟨4586507, by rfl⟩ : syracuseStep 6115343 = 9173015) B9173015
theorem B16307581 : Blo 2231435 16307581 := bstep (se 3 (by rfl) ⟨3057671, by rfl⟩ : syracuseStep 16307581 = 6115343) B6115343
theorem B21743441 : Blo 2231435 21743441 := bstep (se 2 (by rfl) ⟨8153790, by rfl⟩ : syracuseStep 21743441 = 16307581) B16307581
theorem B14495627 : Blo 2231435 14495627 := bstep (se 1 (by rfl) ⟨10871720, by rfl⟩ : syracuseStep 14495627 = 21743441) B21743441
theorem B9663751 : Blo 2231435 9663751 := bstep (se 1 (by rfl) ⟨7247813, by rfl⟩ : syracuseStep 9663751 = 14495627) B14495627
theorem B12885001 : Blo 2231435 12885001 := bstep (se 2 (by rfl) ⟨4831875, by rfl⟩ : syracuseStep 12885001 = 9663751) B9663751
theorem B68720005 : Blo 2231435 68720005 := bstep (se 4 (by rfl) ⟨6442500, by rfl⟩ : syracuseStep 68720005 = 12885001) B12885001
theorem B91626673 : Blo 2231435 91626673 := bstep (se 2 (by rfl) ⟨34360002, by rfl⟩ : syracuseStep 91626673 = 68720005) B68720005
theorem B122168897 : Blo 2231435 122168897 := bstep (se 2 (by rfl) ⟨45813336, by rfl⟩ : syracuseStep 122168897 = 91626673) B91626673
theorem B81445931 : Blo 2231435 81445931 := bstep (se 1 (by rfl) ⟨61084448, by rfl⟩ : syracuseStep 81445931 = 122168897) B122168897
theorem B54297287 : Blo 2231435 54297287 := bstep (se 1 (by rfl) ⟨40722965, by rfl⟩ : syracuseStep 54297287 = 81445931) B81445931
theorem B36198191 : Blo 2231435 36198191 := bstep (se 1 (by rfl) ⟨27148643, by rfl⟩ : syracuseStep 36198191 = 54297287) B54297287
theorem B96528509 : Blo 2231435 96528509 := bstep (se 3 (by rfl) ⟨18099095, by rfl⟩ : syracuseStep 96528509 = 36198191) B36198191
theorem B64352339 : Blo 2231435 64352339 := bstep (se 1 (by rfl) ⟨48264254, by rfl⟩ : syracuseStep 64352339 = 96528509) B96528509
theorem B42901559 : Blo 2231435 42901559 := bstep (se 1 (by rfl) ⟨32176169, by rfl⟩ : syracuseStep 42901559 = 64352339) B64352339
theorem B28601039 : Blo 2231435 28601039 := bstep (se 1 (by rfl) ⟨21450779, by rfl⟩ : syracuseStep 28601039 = 42901559) B42901559
theorem B19067359 : Blo 2231435 19067359 := bstep (se 1 (by rfl) ⟨14300519, by rfl⟩ : syracuseStep 19067359 = 28601039) B28601039
theorem B25423145 : Blo 2231435 25423145 := bstep (se 2 (by rfl) ⟨9533679, by rfl⟩ : syracuseStep 25423145 = 19067359) B19067359
theorem B16948763 : Blo 2231435 16948763 := bstep (se 1 (by rfl) ⟨12711572, by rfl⟩ : syracuseStep 16948763 = 25423145) B25423145
theorem B11299175 : Blo 2231435 11299175 := bstep (se 1 (by rfl) ⟨8474381, by rfl⟩ : syracuseStep 11299175 = 16948763) B16948763
theorem B7532783 : Blo 2231435 7532783 := bstep (se 1 (by rfl) ⟨5649587, by rfl⟩ : syracuseStep 7532783 = 11299175) B11299175
theorem B5021855 : Blo 2231435 5021855 := bstep (se 1 (by rfl) ⟨3766391, by rfl⟩ : syracuseStep 5021855 = 7532783) B7532783
theorem B3347903 : Blo 2231435 3347903 := bstep (se 1 (by rfl) ⟨2510927, by rfl⟩ : syracuseStep 3347903 = 5021855) B5021855
theorem B2231935 : Blo 2231435 2231935 := bstep (se 1 (by rfl) ⟨1673951, by rfl⟩ : syracuseStep 2231935 = 3347903) B3347903
theorem B3347909 : Blo 2231435 3347909 := bbase (se 4 (by rfl) ⟨313866, by rfl⟩ : syracuseStep 3347909 = 627733) (by norm_num)
theorem B2231939 : Blo 2231435 2231939 := bstep (se 1 (by rfl) ⟨1673954, by rfl⟩ : syracuseStep 2231939 = 3347909) B3347909
theorem B3766405 : Blo 2231435 3766405 := bbase (se 4 (by rfl) ⟨353100, by rfl⟩ : syracuseStep 3766405 = 706201) (by norm_num)
theorem B5021873 : Blo 2231435 5021873 := bstep (se 2 (by rfl) ⟨1883202, by rfl⟩ : syracuseStep 5021873 = 3766405) B3766405
theorem B3347915 : Blo 2231435 3347915 := bstep (se 1 (by rfl) ⟨2510936, by rfl⟩ : syracuseStep 3347915 = 5021873) B5021873
theorem B2231943 : Blo 2231435 2231943 := bstep (se 1 (by rfl) ⟨1673957, by rfl⟩ : syracuseStep 2231943 = 3347915) B3347915
theorem B2510941 : Blo 2231435 2510941 := bbase (se 3 (by rfl) ⟨470801, by rfl⟩ : syracuseStep 2510941 = 941603) (by norm_num)
theorem B3347921 : Blo 2231435 3347921 := bstep (se 2 (by rfl) ⟨1255470, by rfl⟩ : syracuseStep 3347921 = 2510941) B2510941
theorem B2231947 : Blo 2231435 2231947 := bstep (se 1 (by rfl) ⟨1673960, by rfl⟩ : syracuseStep 2231947 = 3347921) B3347921
theorem B7532837 : Blo 2231435 7532837 := bbase (se 4 (by rfl) ⟨706203, by rfl⟩ : syracuseStep 7532837 = 1412407) (by norm_num)
theorem B5021891 : Blo 2231435 5021891 := bstep (se 1 (by rfl) ⟨3766418, by rfl⟩ : syracuseStep 5021891 = 7532837) B7532837
theorem B3347927 : Blo 2231435 3347927 := bstep (se 1 (by rfl) ⟨2510945, by rfl⟩ : syracuseStep 3347927 = 5021891) B5021891
theorem B2231951 : Blo 2231435 2231951 := bstep (se 1 (by rfl) ⟨1673963, by rfl⟩ : syracuseStep 2231951 = 3347927) B3347927
theorem B3347933 : Blo 2231435 3347933 := bbase (se 3 (by rfl) ⟨627737, by rfl⟩ : syracuseStep 3347933 = 1255475) (by norm_num)
theorem B2231955 : Blo 2231435 2231955 := bstep (se 1 (by rfl) ⟨1673966, by rfl⟩ : syracuseStep 2231955 = 3347933) B3347933
theorem B5021909 : Blo 2231435 5021909 := bbase (se 7 (by rfl) ⟨58850, by rfl⟩ : syracuseStep 5021909 = 117701) (by norm_num)
theorem B3347939 : Blo 2231435 3347939 := bstep (se 1 (by rfl) ⟨2510954, by rfl⟩ : syracuseStep 3347939 = 5021909) B5021909
theorem B2231959 : Blo 2231435 2231959 := bstep (se 1 (by rfl) ⟨1673969, by rfl⟩ : syracuseStep 2231959 = 3347939) B3347939
theorem B24132437 : Blo 2231435 24132437 := bbase (se 9 (by rfl) ⟨70700, by rfl⟩ : syracuseStep 24132437 = 141401) (by norm_num)
theorem B16088291 : Blo 2231435 16088291 := bstep (se 1 (by rfl) ⟨12066218, by rfl⟩ : syracuseStep 16088291 = 24132437) B24132437
theorem B10725527 : Blo 2231435 10725527 := bstep (se 1 (by rfl) ⟨8044145, by rfl⟩ : syracuseStep 10725527 = 16088291) B16088291
theorem B7150351 : Blo 2231435 7150351 := bstep (se 1 (by rfl) ⟨5362763, by rfl⟩ : syracuseStep 7150351 = 10725527) B10725527
theorem B9533801 : Blo 2231435 9533801 := bstep (se 2 (by rfl) ⟨3575175, by rfl⟩ : syracuseStep 9533801 = 7150351) B7150351
theorem B6355867 : Blo 2231435 6355867 := bstep (se 1 (by rfl) ⟨4766900, by rfl⟩ : syracuseStep 6355867 = 9533801) B9533801
theorem B8474489 : Blo 2231435 8474489 := bstep (se 2 (by rfl) ⟨3177933, by rfl⟩ : syracuseStep 8474489 = 6355867) B6355867
theorem B5649659 : Blo 2231435 5649659 := bstep (se 1 (by rfl) ⟨4237244, by rfl⟩ : syracuseStep 5649659 = 8474489) B8474489
theorem B3766439 : Blo 2231435 3766439 := bstep (se 1 (by rfl) ⟨2824829, by rfl⟩ : syracuseStep 3766439 = 5649659) B5649659
theorem B2510959 : Blo 2231435 2510959 := bstep (se 1 (by rfl) ⟨1883219, by rfl⟩ : syracuseStep 2510959 = 3766439) B3766439
theorem B3347945 : Blo 2231435 3347945 := bstep (se 2 (by rfl) ⟨1255479, by rfl⟩ : syracuseStep 3347945 = 2510959) B2510959
theorem B2231963 : Blo 2231435 2231963 := bstep (se 1 (by rfl) ⟨1673972, by rfl⟩ : syracuseStep 2231963 = 3347945) B3347945
theorem B14300725 : Blo 2231435 14300725 := bbase (se 5 (by rfl) ⟨670346, by rfl⟩ : syracuseStep 14300725 = 1340693) (by norm_num)
theorem B19067633 : Blo 2231435 19067633 := bstep (se 2 (by rfl) ⟨7150362, by rfl⟩ : syracuseStep 19067633 = 14300725) B14300725
theorem B12711755 : Blo 2231435 12711755 := bstep (se 1 (by rfl) ⟨9533816, by rfl⟩ : syracuseStep 12711755 = 19067633) B19067633
theorem B8474503 : Blo 2231435 8474503 := bstep (se 1 (by rfl) ⟨6355877, by rfl⟩ : syracuseStep 8474503 = 12711755) B12711755
theorem B11299337 : Blo 2231435 11299337 := bstep (se 2 (by rfl) ⟨4237251, by rfl⟩ : syracuseStep 11299337 = 8474503) B8474503
theorem B7532891 : Blo 2231435 7532891 := bstep (se 1 (by rfl) ⟨5649668, by rfl⟩ : syracuseStep 7532891 = 11299337) B11299337
theorem B5021927 : Blo 2231435 5021927 := bstep (se 1 (by rfl) ⟨3766445, by rfl⟩ : syracuseStep 5021927 = 7532891) B7532891
theorem B3347951 : Blo 2231435 3347951 := bstep (se 1 (by rfl) ⟨2510963, by rfl⟩ : syracuseStep 3347951 = 5021927) B5021927
theorem B2231967 : Blo 2231435 2231967 := bstep (se 1 (by rfl) ⟨1673975, by rfl⟩ : syracuseStep 2231967 = 3347951) B3347951
theorem B3347957 : Blo 2231435 3347957 := bbase (se 5 (by rfl) ⟨156935, by rfl⟩ : syracuseStep 3347957 = 313871) (by norm_num)
theorem B2231971 : Blo 2231435 2231971 := bstep (se 1 (by rfl) ⟨1673978, by rfl⟩ : syracuseStep 2231971 = 3347957) B3347957
theorem B9173189 : Blo 2231435 9173189 := bbase (se 4 (by rfl) ⟨859986, by rfl⟩ : syracuseStep 9173189 = 1719973) (by norm_num)
theorem B24461837 : Blo 2231435 24461837 := bstep (se 3 (by rfl) ⟨4586594, by rfl⟩ : syracuseStep 24461837 = 9173189) B9173189
theorem B16307891 : Blo 2231435 16307891 := bstep (se 1 (by rfl) ⟨12230918, by rfl⟩ : syracuseStep 16307891 = 24461837) B24461837
theorem B10871927 : Blo 2231435 10871927 := bstep (se 1 (by rfl) ⟨8153945, by rfl⟩ : syracuseStep 10871927 = 16307891) B16307891
theorem B7247951 : Blo 2231435 7247951 := bstep (se 1 (by rfl) ⟨5435963, by rfl⟩ : syracuseStep 7247951 = 10871927) B10871927
theorem B4831967 : Blo 2231435 4831967 := bstep (se 1 (by rfl) ⟨3623975, by rfl⟩ : syracuseStep 4831967 = 7247951) B7247951
theorem B3221311 : Blo 2231435 3221311 := bstep (se 1 (by rfl) ⟨2415983, by rfl⟩ : syracuseStep 3221311 = 4831967) B4831967
theorem B4295081 : Blo 2231435 4295081 := bstep (se 2 (by rfl) ⟨1610655, by rfl⟩ : syracuseStep 4295081 = 3221311) B3221311
theorem B2863387 : Blo 2231435 2863387 := bstep (se 1 (by rfl) ⟨2147540, by rfl⟩ : syracuseStep 2863387 = 4295081) B4295081
theorem B3817849 : Blo 2231435 3817849 := bstep (se 2 (by rfl) ⟨1431693, by rfl⟩ : syracuseStep 3817849 = 2863387) B2863387
theorem B5090465 : Blo 2231435 5090465 := bstep (se 2 (by rfl) ⟨1908924, by rfl⟩ : syracuseStep 5090465 = 3817849) B3817849
theorem B13574573 : Blo 2231435 13574573 := bstep (se 3 (by rfl) ⟨2545232, by rfl⟩ : syracuseStep 13574573 = 5090465) B5090465
theorem B9049715 : Blo 2231435 9049715 := bstep (se 1 (by rfl) ⟨6787286, by rfl⟩ : syracuseStep 9049715 = 13574573) B13574573
theorem B6033143 : Blo 2231435 6033143 := bstep (se 1 (by rfl) ⟨4524857, by rfl⟩ : syracuseStep 6033143 = 9049715) B9049715
theorem B4022095 : Blo 2231435 4022095 := bstep (se 1 (by rfl) ⟨3016571, by rfl⟩ : syracuseStep 4022095 = 6033143) B6033143
theorem B5362793 : Blo 2231435 5362793 := bstep (se 2 (by rfl) ⟨2011047, by rfl⟩ : syracuseStep 5362793 = 4022095) B4022095
theorem B3575195 : Blo 2231435 3575195 := bstep (se 1 (by rfl) ⟨2681396, by rfl⟩ : syracuseStep 3575195 = 5362793) B5362793
theorem B2383463 : Blo 2231435 2383463 := bstep (se 1 (by rfl) ⟨1787597, by rfl⟩ : syracuseStep 2383463 = 3575195) B3575195
theorem B6355901 : Blo 2231435 6355901 := bstep (se 3 (by rfl) ⟨1191731, by rfl⟩ : syracuseStep 6355901 = 2383463) B2383463
theorem B4237267 : Blo 2231435 4237267 := bstep (se 1 (by rfl) ⟨3177950, by rfl⟩ : syracuseStep 4237267 = 6355901) B6355901
theorem B5649689 : Blo 2231435 5649689 := bstep (se 2 (by rfl) ⟨2118633, by rfl⟩ : syracuseStep 5649689 = 4237267) B4237267
theorem B3766459 : Blo 2231435 3766459 := bstep (se 1 (by rfl) ⟨2824844, by rfl⟩ : syracuseStep 3766459 = 5649689) B5649689
theorem B5021945 : Blo 2231435 5021945 := bstep (se 2 (by rfl) ⟨1883229, by rfl⟩ : syracuseStep 5021945 = 3766459) B3766459
theorem B3347963 : Blo 2231435 3347963 := bstep (se 1 (by rfl) ⟨2510972, by rfl⟩ : syracuseStep 3347963 = 5021945) B5021945
theorem B2231975 : Blo 2231435 2231975 := bstep (se 1 (by rfl) ⟨1673981, by rfl⟩ : syracuseStep 2231975 = 3347963) B3347963
theorem B2510977 : Blo 2231435 2510977 := bbase (se 2 (by rfl) ⟨941616, by rfl⟩ : syracuseStep 2510977 = 1883233) (by norm_num)
theorem B3347969 : Blo 2231435 3347969 := bstep (se 2 (by rfl) ⟨1255488, by rfl⟩ : syracuseStep 3347969 = 2510977) B2510977
theorem B2231979 : Blo 2231435 2231979 := bstep (se 1 (by rfl) ⟨1673984, by rfl⟩ : syracuseStep 2231979 = 3347969) B3347969
theorem B5649709 : Blo 2231435 5649709 := bbase (se 3 (by rfl) ⟨1059320, by rfl⟩ : syracuseStep 5649709 = 2118641) (by norm_num)
theorem B7532945 : Blo 2231435 7532945 := bstep (se 2 (by rfl) ⟨2824854, by rfl⟩ : syracuseStep 7532945 = 5649709) B5649709
theorem B5021963 : Blo 2231435 5021963 := bstep (se 1 (by rfl) ⟨3766472, by rfl⟩ : syracuseStep 5021963 = 7532945) B7532945
theorem B3347975 : Blo 2231435 3347975 := bstep (se 1 (by rfl) ⟨2510981, by rfl⟩ : syracuseStep 3347975 = 5021963) B5021963
theorem B2231983 : Blo 2231435 2231983 := bstep (se 1 (by rfl) ⟨1673987, by rfl⟩ : syracuseStep 2231983 = 3347975) B3347975
theorem B3347981 : Blo 2231435 3347981 := bbase (se 3 (by rfl) ⟨627746, by rfl⟩ : syracuseStep 3347981 = 1255493) (by norm_num)
theorem B2231987 : Blo 2231435 2231987 := bstep (se 1 (by rfl) ⟨1673990, by rfl⟩ : syracuseStep 2231987 = 3347981) B3347981
theorem B5021981 : Blo 2231435 5021981 := bbase (se 3 (by rfl) ⟨941621, by rfl⟩ : syracuseStep 5021981 = 1883243) (by norm_num)
theorem B3347987 : Blo 2231435 3347987 := bstep (se 1 (by rfl) ⟨2510990, by rfl⟩ : syracuseStep 3347987 = 5021981) B5021981
theorem B2231991 : Blo 2231435 2231991 := bstep (se 1 (by rfl) ⟨1673993, by rfl⟩ : syracuseStep 2231991 = 3347987) B3347987
theorem B3766493 : Blo 2231435 3766493 := bbase (se 3 (by rfl) ⟨706217, by rfl⟩ : syracuseStep 3766493 = 1412435) (by norm_num)
theorem B2510995 : Blo 2231435 2510995 := bstep (se 1 (by rfl) ⟨1883246, by rfl⟩ : syracuseStep 2510995 = 3766493) B3766493
theorem B3347993 : Blo 2231435 3347993 := bstep (se 2 (by rfl) ⟨1255497, by rfl⟩ : syracuseStep 3347993 = 2510995) B2510995
theorem B2231995 : Blo 2231435 2231995 := bstep (se 1 (by rfl) ⟨1673996, by rfl⟩ : syracuseStep 2231995 = 3347993) B3347993
theorem B11453669 : Blo 2231435 11453669 := bbase (se 4 (by rfl) ⟨1073781, by rfl⟩ : syracuseStep 11453669 = 2147563) (by norm_num)
theorem B7635779 : Blo 2231435 7635779 := bstep (se 1 (by rfl) ⟨5726834, by rfl⟩ : syracuseStep 7635779 = 11453669) B11453669
theorem B5090519 : Blo 2231435 5090519 := bstep (se 1 (by rfl) ⟨3817889, by rfl⟩ : syracuseStep 5090519 = 7635779) B7635779
theorem B3393679 : Blo 2231435 3393679 := bstep (se 1 (by rfl) ⟨2545259, by rfl⟩ : syracuseStep 3393679 = 5090519) B5090519
theorem B4524905 : Blo 2231435 4524905 := bstep (se 2 (by rfl) ⟨1696839, by rfl⟩ : syracuseStep 4524905 = 3393679) B3393679
theorem B3016603 : Blo 2231435 3016603 := bstep (se 1 (by rfl) ⟨2262452, by rfl⟩ : syracuseStep 3016603 = 4524905) B4524905
theorem B4022137 : Blo 2231435 4022137 := bstep (se 2 (by rfl) ⟨1508301, by rfl⟩ : syracuseStep 4022137 = 3016603) B3016603
theorem B5362849 : Blo 2231435 5362849 := bstep (se 2 (by rfl) ⟨2011068, by rfl⟩ : syracuseStep 5362849 = 4022137) B4022137
theorem B7150465 : Blo 2231435 7150465 := bstep (se 2 (by rfl) ⟨2681424, by rfl⟩ : syracuseStep 7150465 = 5362849) B5362849
theorem B9533953 : Blo 2231435 9533953 := bstep (se 2 (by rfl) ⟨3575232, by rfl⟩ : syracuseStep 9533953 = 7150465) B7150465
theorem B12711937 : Blo 2231435 12711937 := bstep (se 2 (by rfl) ⟨4766976, by rfl⟩ : syracuseStep 12711937 = 9533953) B9533953
theorem B16949249 : Blo 2231435 16949249 := bstep (se 2 (by rfl) ⟨6355968, by rfl⟩ : syracuseStep 16949249 = 12711937) B12711937
theorem B11299499 : Blo 2231435 11299499 := bstep (se 1 (by rfl) ⟨8474624, by rfl⟩ : syracuseStep 11299499 = 16949249) B16949249
theorem B7532999 : Blo 2231435 7532999 := bstep (se 1 (by rfl) ⟨5649749, by rfl⟩ : syracuseStep 7532999 = 11299499) B11299499
theorem B5021999 : Blo 2231435 5021999 := bstep (se 1 (by rfl) ⟨3766499, by rfl⟩ : syracuseStep 5021999 = 7532999) B7532999
theorem B3347999 : Blo 2231435 3347999 := bstep (se 1 (by rfl) ⟨2510999, by rfl⟩ : syracuseStep 3347999 = 5021999) B5021999
theorem B2231999 : Blo 2231435 2231999 := bstep (se 1 (by rfl) ⟨1673999, by rfl⟩ : syracuseStep 2231999 = 3347999) B3347999
theorem B3348005 : Blo 2231435 3348005 := bbase (se 4 (by rfl) ⟨313875, by rfl⟩ : syracuseStep 3348005 = 627751) (by norm_num)
theorem B2232003 : Blo 2231435 2232003 := bstep (se 1 (by rfl) ⟨1674002, by rfl⟩ : syracuseStep 2232003 = 3348005) B3348005
theorem B2824885 : Blo 2231435 2824885 := bbase (se 5 (by rfl) ⟨132416, by rfl⟩ : syracuseStep 2824885 = 264833) (by norm_num)
theorem B3766513 : Blo 2231435 3766513 := bstep (se 2 (by rfl) ⟨1412442, by rfl⟩ : syracuseStep 3766513 = 2824885) B2824885
theorem B5022017 : Blo 2231435 5022017 := bstep (se 2 (by rfl) ⟨1883256, by rfl⟩ : syracuseStep 5022017 = 3766513) B3766513
theorem B3348011 : Blo 2231435 3348011 := bstep (se 1 (by rfl) ⟨2511008, by rfl⟩ : syracuseStep 3348011 = 5022017) B5022017
theorem B2232007 : Blo 2231435 2232007 := bstep (se 1 (by rfl) ⟨1674005, by rfl⟩ : syracuseStep 2232007 = 3348011) B3348011
theorem B2511013 : Blo 2231435 2511013 := bbase (se 4 (by rfl) ⟨235407, by rfl⟩ : syracuseStep 2511013 = 470815) (by norm_num)
theorem B3348017 : Blo 2231435 3348017 := bstep (se 2 (by rfl) ⟨1255506, by rfl⟩ : syracuseStep 3348017 = 2511013) B2511013
theorem B2232011 : Blo 2231435 2232011 := bstep (se 1 (by rfl) ⟨1674008, by rfl⟩ : syracuseStep 2232011 = 3348017) B3348017
theorem B2902505 : Blo 2231435 2902505 := bbase (se 2 (by rfl) ⟨1088439, by rfl⟩ : syracuseStep 2902505 = 2176879) (by norm_num)
theorem B30960053 : Blo 2231435 30960053 := bstep (se 5 (by rfl) ⟨1451252, by rfl⟩ : syracuseStep 30960053 = 2902505) B2902505
theorem B20640035 : Blo 2231435 20640035 := bstep (se 1 (by rfl) ⟨15480026, by rfl⟩ : syracuseStep 20640035 = 30960053) B30960053
theorem B55040093 : Blo 2231435 55040093 := bstep (se 3 (by rfl) ⟨10320017, by rfl⟩ : syracuseStep 55040093 = 20640035) B20640035
theorem B36693395 : Blo 2231435 36693395 := bstep (se 1 (by rfl) ⟨27520046, by rfl⟩ : syracuseStep 36693395 = 55040093) B55040093
theorem B24462263 : Blo 2231435 24462263 := bstep (se 1 (by rfl) ⟨18346697, by rfl⟩ : syracuseStep 24462263 = 36693395) B36693395
theorem B16308175 : Blo 2231435 16308175 := bstep (se 1 (by rfl) ⟨12231131, by rfl⟩ : syracuseStep 16308175 = 24462263) B24462263
theorem B21744233 : Blo 2231435 21744233 := bstep (se 2 (by rfl) ⟨8154087, by rfl⟩ : syracuseStep 21744233 = 16308175) B16308175
theorem B14496155 : Blo 2231435 14496155 := bstep (se 1 (by rfl) ⟨10872116, by rfl⟩ : syracuseStep 14496155 = 21744233) B21744233
theorem B9664103 : Blo 2231435 9664103 := bstep (se 1 (by rfl) ⟨7248077, by rfl⟩ : syracuseStep 9664103 = 14496155) B14496155
theorem B6442735 : Blo 2231435 6442735 := bstep (se 1 (by rfl) ⟨4832051, by rfl⟩ : syracuseStep 6442735 = 9664103) B9664103
theorem B8590313 : Blo 2231435 8590313 := bstep (se 2 (by rfl) ⟨3221367, by rfl⟩ : syracuseStep 8590313 = 6442735) B6442735
theorem B5726875 : Blo 2231435 5726875 := bstep (se 1 (by rfl) ⟨4295156, by rfl⟩ : syracuseStep 5726875 = 8590313) B8590313
theorem B7635833 : Blo 2231435 7635833 := bstep (se 2 (by rfl) ⟨2863437, by rfl⟩ : syracuseStep 7635833 = 5726875) B5726875
theorem B5090555 : Blo 2231435 5090555 := bstep (se 1 (by rfl) ⟨3817916, by rfl⟩ : syracuseStep 5090555 = 7635833) B7635833
theorem B3393703 : Blo 2231435 3393703 := bstep (se 1 (by rfl) ⟨2545277, by rfl⟩ : syracuseStep 3393703 = 5090555) B5090555
theorem B18099749 : Blo 2231435 18099749 := bstep (se 4 (by rfl) ⟨1696851, by rfl⟩ : syracuseStep 18099749 = 3393703) B3393703
theorem B12066499 : Blo 2231435 12066499 := bstep (se 1 (by rfl) ⟨9049874, by rfl⟩ : syracuseStep 12066499 = 18099749) B18099749
theorem B16088665 : Blo 2231435 16088665 := bstep (se 2 (by rfl) ⟨6033249, by rfl⟩ : syracuseStep 16088665 = 12066499) B12066499
theorem B21451553 : Blo 2231435 21451553 := bstep (se 2 (by rfl) ⟨8044332, by rfl⟩ : syracuseStep 21451553 = 16088665) B16088665
theorem B14301035 : Blo 2231435 14301035 := bstep (se 1 (by rfl) ⟨10725776, by rfl⟩ : syracuseStep 14301035 = 21451553) B21451553
theorem B9534023 : Blo 2231435 9534023 := bstep (se 1 (by rfl) ⟨7150517, by rfl⟩ : syracuseStep 9534023 = 14301035) B14301035
theorem B6356015 : Blo 2231435 6356015 := bstep (se 1 (by rfl) ⟨4767011, by rfl⟩ : syracuseStep 6356015 = 9534023) B9534023
theorem B4237343 : Blo 2231435 4237343 := bstep (se 1 (by rfl) ⟨3178007, by rfl⟩ : syracuseStep 4237343 = 6356015) B6356015
theorem B2824895 : Blo 2231435 2824895 := bstep (se 1 (by rfl) ⟨2118671, by rfl⟩ : syracuseStep 2824895 = 4237343) B4237343
theorem B7533053 : Blo 2231435 7533053 := bstep (se 3 (by rfl) ⟨1412447, by rfl⟩ : syracuseStep 7533053 = 2824895) B2824895
theorem B5022035 : Blo 2231435 5022035 := bstep (se 1 (by rfl) ⟨3766526, by rfl⟩ : syracuseStep 5022035 = 7533053) B7533053
theorem B3348023 : Blo 2231435 3348023 := bstep (se 1 (by rfl) ⟨2511017, by rfl⟩ : syracuseStep 3348023 = 5022035) B5022035
theorem B2232015 : Blo 2231435 2232015 := bstep (se 1 (by rfl) ⟨1674011, by rfl⟩ : syracuseStep 2232015 = 3348023) B3348023
theorem B3348029 : Blo 2231435 3348029 := bbase (se 3 (by rfl) ⟨627755, by rfl⟩ : syracuseStep 3348029 = 1255511) (by norm_num)
theorem B2232019 : Blo 2231435 2232019 := bstep (se 1 (by rfl) ⟨1674014, by rfl⟩ : syracuseStep 2232019 = 3348029) B3348029
theorem B5022053 : Blo 2231435 5022053 := bbase (se 4 (by rfl) ⟨470817, by rfl⟩ : syracuseStep 5022053 = 941635) (by norm_num)
theorem B3348035 : Blo 2231435 3348035 := bstep (se 1 (by rfl) ⟨2511026, by rfl⟩ : syracuseStep 3348035 = 5022053) B5022053
theorem B2232023 : Blo 2231435 2232023 := bstep (se 1 (by rfl) ⟨1674017, by rfl⟩ : syracuseStep 2232023 = 3348035) B3348035
theorem B5649821 : Blo 2231435 5649821 := bbase (se 3 (by rfl) ⟨1059341, by rfl⟩ : syracuseStep 5649821 = 2118683) (by norm_num)
theorem B3766547 : Blo 2231435 3766547 := bstep (se 1 (by rfl) ⟨2824910, by rfl⟩ : syracuseStep 3766547 = 5649821) B5649821
theorem B2511031 : Blo 2231435 2511031 := bstep (se 1 (by rfl) ⟨1883273, by rfl⟩ : syracuseStep 2511031 = 3766547) B3766547
theorem B3348041 : Blo 2231435 3348041 := bstep (se 2 (by rfl) ⟨1255515, by rfl⟩ : syracuseStep 3348041 = 2511031) B2511031
theorem B2232027 : Blo 2231435 2232027 := bstep (se 1 (by rfl) ⟨1674020, by rfl⟩ : syracuseStep 2232027 = 3348041) B3348041
theorem B4237373 : Blo 2231435 4237373 := bbase (se 3 (by rfl) ⟨794507, by rfl⟩ : syracuseStep 4237373 = 1589015) (by norm_num)
theorem B11299661 : Blo 2231435 11299661 := bstep (se 3 (by rfl) ⟨2118686, by rfl⟩ : syracuseStep 11299661 = 4237373) B4237373
theorem B7533107 : Blo 2231435 7533107 := bstep (se 1 (by rfl) ⟨5649830, by rfl⟩ : syracuseStep 7533107 = 11299661) B11299661
theorem B5022071 : Blo 2231435 5022071 := bstep (se 1 (by rfl) ⟨3766553, by rfl⟩ : syracuseStep 5022071 = 7533107) B7533107
theorem B3348047 : Blo 2231435 3348047 := bstep (se 1 (by rfl) ⟨2511035, by rfl⟩ : syracuseStep 3348047 = 5022071) B5022071
theorem B2232031 : Blo 2231435 2232031 := bstep (se 1 (by rfl) ⟨1674023, by rfl⟩ : syracuseStep 2232031 = 3348047) B3348047
theorem B3348053 : Blo 2231435 3348053 := bbase (se 8 (by rfl) ⟨19617, by rfl⟩ : syracuseStep 3348053 = 39235) (by norm_num)
theorem B2232035 : Blo 2231435 2232035 := bstep (se 1 (by rfl) ⟨1674026, by rfl⟩ : syracuseStep 2232035 = 3348053) B3348053
theorem B2681473 : Blo 2231435 2681473 := bbase (se 2 (by rfl) ⟨1005552, by rfl⟩ : syracuseStep 2681473 = 2011105) (by norm_num)
theorem B3575297 : Blo 2231435 3575297 := bstep (se 2 (by rfl) ⟨1340736, by rfl⟩ : syracuseStep 3575297 = 2681473) B2681473
theorem B9534125 : Blo 2231435 9534125 := bstep (se 3 (by rfl) ⟨1787648, by rfl⟩ : syracuseStep 9534125 = 3575297) B3575297
theorem B6356083 : Blo 2231435 6356083 := bstep (se 1 (by rfl) ⟨4767062, by rfl⟩ : syracuseStep 6356083 = 9534125) B9534125
theorem B8474777 : Blo 2231435 8474777 := bstep (se 2 (by rfl) ⟨3178041, by rfl⟩ : syracuseStep 8474777 = 6356083) B6356083
theorem B5649851 : Blo 2231435 5649851 := bstep (se 1 (by rfl) ⟨4237388, by rfl⟩ : syracuseStep 5649851 = 8474777) B8474777
theorem B3766567 : Blo 2231435 3766567 := bstep (se 1 (by rfl) ⟨2824925, by rfl⟩ : syracuseStep 3766567 = 5649851) B5649851
theorem B5022089 : Blo 2231435 5022089 := bstep (se 2 (by rfl) ⟨1883283, by rfl⟩ : syracuseStep 5022089 = 3766567) B3766567
theorem B3348059 : Blo 2231435 3348059 := bstep (se 1 (by rfl) ⟨2511044, by rfl⟩ : syracuseStep 3348059 = 5022089) B5022089
theorem B2232039 : Blo 2231435 2232039 := bstep (se 1 (by rfl) ⟨1674029, by rfl⟩ : syracuseStep 2232039 = 3348059) B3348059
theorem B2511049 : Blo 2231435 2511049 := bbase (se 2 (by rfl) ⟨941643, by rfl⟩ : syracuseStep 2511049 = 1883287) (by norm_num)
theorem B3348065 : Blo 2231435 3348065 := bstep (se 2 (by rfl) ⟨1255524, by rfl⟩ : syracuseStep 3348065 = 2511049) B2511049
theorem B2232043 : Blo 2231435 2232043 := bstep (se 1 (by rfl) ⟨1674032, by rfl⟩ : syracuseStep 2232043 = 3348065) B3348065
theorem B4077101 : Blo 2231435 4077101 := bbase (se 3 (by rfl) ⟨764456, by rfl⟩ : syracuseStep 4077101 = 1528913) (by norm_num)
theorem B10872269 : Blo 2231435 10872269 := bstep (se 3 (by rfl) ⟨2038550, by rfl⟩ : syracuseStep 10872269 = 4077101) B4077101
theorem B7248179 : Blo 2231435 7248179 := bstep (se 1 (by rfl) ⟨5436134, by rfl⟩ : syracuseStep 7248179 = 10872269) B10872269
theorem B4832119 : Blo 2231435 4832119 := bstep (se 1 (by rfl) ⟨3624089, by rfl⟩ : syracuseStep 4832119 = 7248179) B7248179
theorem B25771301 : Blo 2231435 25771301 := bstep (se 4 (by rfl) ⟨2416059, by rfl⟩ : syracuseStep 25771301 = 4832119) B4832119
theorem B17180867 : Blo 2231435 17180867 := bstep (se 1 (by rfl) ⟨12885650, by rfl⟩ : syracuseStep 17180867 = 25771301) B25771301
theorem B45815645 : Blo 2231435 45815645 := bstep (se 3 (by rfl) ⟨8590433, by rfl⟩ : syracuseStep 45815645 = 17180867) B17180867
theorem B30543763 : Blo 2231435 30543763 := bstep (se 1 (by rfl) ⟨22907822, by rfl⟩ : syracuseStep 30543763 = 45815645) B45815645
theorem B40725017 : Blo 2231435 40725017 := bstep (se 2 (by rfl) ⟨15271881, by rfl⟩ : syracuseStep 40725017 = 30543763) B30543763
theorem B27150011 : Blo 2231435 27150011 := bstep (se 1 (by rfl) ⟨20362508, by rfl⟩ : syracuseStep 27150011 = 40725017) B40725017
theorem B18100007 : Blo 2231435 18100007 := bstep (se 1 (by rfl) ⟨13575005, by rfl⟩ : syracuseStep 18100007 = 27150011) B27150011
theorem B12066671 : Blo 2231435 12066671 := bstep (se 1 (by rfl) ⟨9050003, by rfl⟩ : syracuseStep 12066671 = 18100007) B18100007
theorem B8044447 : Blo 2231435 8044447 := bstep (se 1 (by rfl) ⟨6033335, by rfl⟩ : syracuseStep 8044447 = 12066671) B12066671
theorem B10725929 : Blo 2231435 10725929 := bstep (se 2 (by rfl) ⟨4022223, by rfl⟩ : syracuseStep 10725929 = 8044447) B8044447
theorem B7150619 : Blo 2231435 7150619 := bstep (se 1 (by rfl) ⟨5362964, by rfl⟩ : syracuseStep 7150619 = 10725929) B10725929
theorem B19068317 : Blo 2231435 19068317 := bstep (se 3 (by rfl) ⟨3575309, by rfl⟩ : syracuseStep 19068317 = 7150619) B7150619
theorem B12712211 : Blo 2231435 12712211 := bstep (se 1 (by rfl) ⟨9534158, by rfl⟩ : syracuseStep 12712211 = 19068317) B19068317
theorem B8474807 : Blo 2231435 8474807 := bstep (se 1 (by rfl) ⟨6356105, by rfl⟩ : syracuseStep 8474807 = 12712211) B12712211
theorem B5649871 : Blo 2231435 5649871 := bstep (se 1 (by rfl) ⟨4237403, by rfl⟩ : syracuseStep 5649871 = 8474807) B8474807
theorem B7533161 : Blo 2231435 7533161 := bstep (se 2 (by rfl) ⟨2824935, by rfl⟩ : syracuseStep 7533161 = 5649871) B5649871
theorem B5022107 : Blo 2231435 5022107 := bstep (se 1 (by rfl) ⟨3766580, by rfl⟩ : syracuseStep 5022107 = 7533161) B7533161
theorem B3348071 : Blo 2231435 3348071 := bstep (se 1 (by rfl) ⟨2511053, by rfl⟩ : syracuseStep 3348071 = 5022107) B5022107
theorem B2232047 : Blo 2231435 2232047 := bstep (se 1 (by rfl) ⟨1674035, by rfl⟩ : syracuseStep 2232047 = 3348071) B3348071
theorem B3348077 : Blo 2231435 3348077 := bbase (se 3 (by rfl) ⟨627764, by rfl⟩ : syracuseStep 3348077 = 1255529) (by norm_num)
theorem B2232051 : Blo 2231435 2232051 := bstep (se 1 (by rfl) ⟨1674038, by rfl⟩ : syracuseStep 2232051 = 3348077) B3348077
theorem B5022125 : Blo 2231435 5022125 := bbase (se 3 (by rfl) ⟨941648, by rfl⟩ : syracuseStep 5022125 = 1883297) (by norm_num)
theorem B3348083 : Blo 2231435 3348083 := bstep (se 1 (by rfl) ⟨2511062, by rfl⟩ : syracuseStep 3348083 = 5022125) B5022125
theorem B2232055 : Blo 2231435 2232055 := bstep (se 1 (by rfl) ⟨1674041, by rfl⟩ : syracuseStep 2232055 = 3348083) B3348083
theorem B2383553 : Blo 2231435 2383553 := bbase (se 2 (by rfl) ⟨893832, by rfl⟩ : syracuseStep 2383553 = 1787665) (by norm_num)
theorem B6356141 : Blo 2231435 6356141 := bstep (se 3 (by rfl) ⟨1191776, by rfl⟩ : syracuseStep 6356141 = 2383553) B2383553
theorem B4237427 : Blo 2231435 4237427 := bstep (se 1 (by rfl) ⟨3178070, by rfl⟩ : syracuseStep 4237427 = 6356141) B6356141
theorem B2824951 : Blo 2231435 2824951 := bstep (se 1 (by rfl) ⟨2118713, by rfl⟩ : syracuseStep 2824951 = 4237427) B4237427
theorem B3766601 : Blo 2231435 3766601 := bstep (se 2 (by rfl) ⟨1412475, by rfl⟩ : syracuseStep 3766601 = 2824951) B2824951
theorem B2511067 : Blo 2231435 2511067 := bstep (se 1 (by rfl) ⟨1883300, by rfl⟩ : syracuseStep 2511067 = 3766601) B3766601
theorem B3348089 : Blo 2231435 3348089 := bstep (se 2 (by rfl) ⟨1255533, by rfl⟩ : syracuseStep 3348089 = 2511067) B2511067
theorem B2232059 : Blo 2231435 2232059 := bstep (se 1 (by rfl) ⟨1674044, by rfl⟩ : syracuseStep 2232059 = 3348089) B3348089
theorem B3817997 : Blo 2231435 3817997 := bbase (se 3 (by rfl) ⟨715874, by rfl⟩ : syracuseStep 3817997 = 1431749) (by norm_num)
theorem B40725301 : Blo 2231435 40725301 := bstep (se 5 (by rfl) ⟨1908998, by rfl⟩ : syracuseStep 40725301 = 3817997) B3817997
theorem B54300401 : Blo 2231435 54300401 := bstep (se 2 (by rfl) ⟨20362650, by rfl⟩ : syracuseStep 54300401 = 40725301) B40725301
theorem B36200267 : Blo 2231435 36200267 := bstep (se 1 (by rfl) ⟨27150200, by rfl⟩ : syracuseStep 36200267 = 54300401) B54300401
theorem B24133511 : Blo 2231435 24133511 := bstep (se 1 (by rfl) ⟨18100133, by rfl⟩ : syracuseStep 24133511 = 36200267) B36200267
theorem B64356029 : Blo 2231435 64356029 := bstep (se 3 (by rfl) ⟨12066755, by rfl⟩ : syracuseStep 64356029 = 24133511) B24133511
theorem B42904019 : Blo 2231435 42904019 := bstep (se 1 (by rfl) ⟨32178014, by rfl⟩ : syracuseStep 42904019 = 64356029) B64356029
theorem B28602679 : Blo 2231435 28602679 := bstep (se 1 (by rfl) ⟨21452009, by rfl⟩ : syracuseStep 28602679 = 42904019) B42904019
theorem B38136905 : Blo 2231435 38136905 := bstep (se 2 (by rfl) ⟨14301339, by rfl⟩ : syracuseStep 38136905 = 28602679) B28602679
theorem B25424603 : Blo 2231435 25424603 := bstep (se 1 (by rfl) ⟨19068452, by rfl⟩ : syracuseStep 25424603 = 38136905) B38136905
theorem B16949735 : Blo 2231435 16949735 := bstep (se 1 (by rfl) ⟨12712301, by rfl⟩ : syracuseStep 16949735 = 25424603) B25424603
theorem B11299823 : Blo 2231435 11299823 := bstep (se 1 (by rfl) ⟨8474867, by rfl⟩ : syracuseStep 11299823 = 16949735) B16949735
theorem B7533215 : Blo 2231435 7533215 := bstep (se 1 (by rfl) ⟨5649911, by rfl⟩ : syracuseStep 7533215 = 11299823) B11299823
theorem B5022143 : Blo 2231435 5022143 := bstep (se 1 (by rfl) ⟨3766607, by rfl⟩ : syracuseStep 5022143 = 7533215) B7533215
theorem B3348095 : Blo 2231435 3348095 := bstep (se 1 (by rfl) ⟨2511071, by rfl⟩ : syracuseStep 3348095 = 5022143) B5022143
theorem B2232063 : Blo 2231435 2232063 := bstep (se 1 (by rfl) ⟨1674047, by rfl⟩ : syracuseStep 2232063 = 3348095) B3348095
theorem B3348101 : Blo 2231435 3348101 := bbase (se 4 (by rfl) ⟨313884, by rfl⟩ : syracuseStep 3348101 = 627769) (by norm_num)
theorem B2232067 : Blo 2231435 2232067 := bstep (se 1 (by rfl) ⟨1674050, by rfl⟩ : syracuseStep 2232067 = 3348101) B3348101
theorem B3766621 : Blo 2231435 3766621 := bbase (se 3 (by rfl) ⟨706241, by rfl⟩ : syracuseStep 3766621 = 1412483) (by norm_num)
theorem B5022161 : Blo 2231435 5022161 := bstep (se 2 (by rfl) ⟨1883310, by rfl⟩ : syracuseStep 5022161 = 3766621) B3766621
theorem B3348107 : Blo 2231435 3348107 := bstep (se 1 (by rfl) ⟨2511080, by rfl⟩ : syracuseStep 3348107 = 5022161) B5022161
theorem B2232071 : Blo 2231435 2232071 := bstep (se 1 (by rfl) ⟨1674053, by rfl⟩ : syracuseStep 2232071 = 3348107) B3348107
theorem B2511085 : Blo 2231435 2511085 := bbase (se 3 (by rfl) ⟨470828, by rfl⟩ : syracuseStep 2511085 = 941657) (by norm_num)
theorem B3348113 : Blo 2231435 3348113 := bstep (se 2 (by rfl) ⟨1255542, by rfl⟩ : syracuseStep 3348113 = 2511085) B2511085
theorem B2232075 : Blo 2231435 2232075 := bstep (se 1 (by rfl) ⟨1674056, by rfl⟩ : syracuseStep 2232075 = 3348113) B3348113
theorem B7533269 : Blo 2231435 7533269 := bbase (se 7 (by rfl) ⟨88280, by rfl⟩ : syracuseStep 7533269 = 176561) (by norm_num)
theorem B5022179 : Blo 2231435 5022179 := bstep (se 1 (by rfl) ⟨3766634, by rfl⟩ : syracuseStep 5022179 = 7533269) B7533269
theorem B3348119 : Blo 2231435 3348119 := bstep (se 1 (by rfl) ⟨2511089, by rfl⟩ : syracuseStep 3348119 = 5022179) B5022179
theorem B2232079 : Blo 2231435 2232079 := bstep (se 1 (by rfl) ⟨1674059, by rfl⟩ : syracuseStep 2232079 = 3348119) B3348119
theorem B3348125 : Blo 2231435 3348125 := bbase (se 3 (by rfl) ⟨627773, by rfl⟩ : syracuseStep 3348125 = 1255547) (by norm_num)
theorem B2232083 : Blo 2231435 2232083 := bstep (se 1 (by rfl) ⟨1674062, by rfl⟩ : syracuseStep 2232083 = 3348125) B3348125
theorem B5022197 : Blo 2231435 5022197 := bbase (se 5 (by rfl) ⟨235415, by rfl⟩ : syracuseStep 5022197 = 470831) (by norm_num)
theorem B3348131 : Blo 2231435 3348131 := bstep (se 1 (by rfl) ⟨2511098, by rfl⟩ : syracuseStep 3348131 = 5022197) B5022197
theorem B2232087 : Blo 2231435 2232087 := bstep (se 1 (by rfl) ⟨1674065, by rfl⟩ : syracuseStep 2232087 = 3348131) B3348131
theorem B10872485 : Blo 2231435 10872485 := bbase (se 4 (by rfl) ⟨1019295, by rfl⟩ : syracuseStep 10872485 = 2038591) (by norm_num)
theorem B7248323 : Blo 2231435 7248323 := bstep (se 1 (by rfl) ⟨5436242, by rfl⟩ : syracuseStep 7248323 = 10872485) B10872485
theorem B19328861 : Blo 2231435 19328861 := bstep (se 3 (by rfl) ⟨3624161, by rfl⟩ : syracuseStep 19328861 = 7248323) B7248323
theorem B12885907 : Blo 2231435 12885907 := bstep (se 1 (by rfl) ⟨9664430, by rfl⟩ : syracuseStep 12885907 = 19328861) B19328861
theorem B17181209 : Blo 2231435 17181209 := bstep (se 2 (by rfl) ⟨6442953, by rfl⟩ : syracuseStep 17181209 = 12885907) B12885907
theorem B11454139 : Blo 2231435 11454139 := bstep (se 1 (by rfl) ⟨8590604, by rfl⟩ : syracuseStep 11454139 = 17181209) B17181209
theorem B15272185 : Blo 2231435 15272185 := bstep (se 2 (by rfl) ⟨5727069, by rfl⟩ : syracuseStep 15272185 = 11454139) B11454139
theorem B20362913 : Blo 2231435 20362913 := bstep (se 2 (by rfl) ⟨7636092, by rfl⟩ : syracuseStep 20362913 = 15272185) B15272185
theorem B13575275 : Blo 2231435 13575275 := bstep (se 1 (by rfl) ⟨10181456, by rfl⟩ : syracuseStep 13575275 = 20362913) B20362913
theorem B9050183 : Blo 2231435 9050183 := bstep (se 1 (by rfl) ⟨6787637, by rfl⟩ : syracuseStep 9050183 = 13575275) B13575275
theorem B6033455 : Blo 2231435 6033455 := bstep (se 1 (by rfl) ⟨4525091, by rfl⟩ : syracuseStep 6033455 = 9050183) B9050183
theorem B4022303 : Blo 2231435 4022303 := bstep (se 1 (by rfl) ⟨3016727, by rfl⟩ : syracuseStep 4022303 = 6033455) B6033455
theorem B42904565 : Blo 2231435 42904565 := bstep (se 5 (by rfl) ⟨2011151, by rfl⟩ : syracuseStep 42904565 = 4022303) B4022303
theorem B28603043 : Blo 2231435 28603043 := bstep (se 1 (by rfl) ⟨21452282, by rfl⟩ : syracuseStep 28603043 = 42904565) B42904565
theorem B19068695 : Blo 2231435 19068695 := bstep (se 1 (by rfl) ⟨14301521, by rfl⟩ : syracuseStep 19068695 = 28603043) B28603043
theorem B12712463 : Blo 2231435 12712463 := bstep (se 1 (by rfl) ⟨9534347, by rfl⟩ : syracuseStep 12712463 = 19068695) B19068695
theorem B8474975 : Blo 2231435 8474975 := bstep (se 1 (by rfl) ⟨6356231, by rfl⟩ : syracuseStep 8474975 = 12712463) B12712463
theorem B5649983 : Blo 2231435 5649983 := bstep (se 1 (by rfl) ⟨4237487, by rfl⟩ : syracuseStep 5649983 = 8474975) B8474975
theorem B3766655 : Blo 2231435 3766655 := bstep (se 1 (by rfl) ⟨2824991, by rfl⟩ : syracuseStep 3766655 = 5649983) B5649983
theorem B2511103 : Blo 2231435 2511103 := bstep (se 1 (by rfl) ⟨1883327, by rfl⟩ : syracuseStep 2511103 = 3766655) B3766655
theorem B3348137 : Blo 2231435 3348137 := bstep (se 2 (by rfl) ⟨1255551, by rfl⟩ : syracuseStep 3348137 = 2511103) B2511103
theorem B2232091 : Blo 2231435 2232091 := bstep (se 1 (by rfl) ⟨1674068, by rfl⟩ : syracuseStep 2232091 = 3348137) B3348137
theorem B10181477 : Blo 2231435 10181477 := bbase (se 4 (by rfl) ⟨954513, by rfl⟩ : syracuseStep 10181477 = 1909027) (by norm_num)
theorem B6787651 : Blo 2231435 6787651 := bstep (se 1 (by rfl) ⟨5090738, by rfl⟩ : syracuseStep 6787651 = 10181477) B10181477
theorem B9050201 : Blo 2231435 9050201 := bstep (se 2 (by rfl) ⟨3393825, by rfl⟩ : syracuseStep 9050201 = 6787651) B6787651
theorem B6033467 : Blo 2231435 6033467 := bstep (se 1 (by rfl) ⟨4525100, by rfl⟩ : syracuseStep 6033467 = 9050201) B9050201
theorem B4022311 : Blo 2231435 4022311 := bstep (se 1 (by rfl) ⟨3016733, by rfl⟩ : syracuseStep 4022311 = 6033467) B6033467
theorem B5363081 : Blo 2231435 5363081 := bstep (se 2 (by rfl) ⟨2011155, by rfl⟩ : syracuseStep 5363081 = 4022311) B4022311
theorem B3575387 : Blo 2231435 3575387 := bstep (se 1 (by rfl) ⟨2681540, by rfl⟩ : syracuseStep 3575387 = 5363081) B5363081
theorem B2383591 : Blo 2231435 2383591 := bstep (se 1 (by rfl) ⟨1787693, by rfl⟩ : syracuseStep 2383591 = 3575387) B3575387
theorem B3178121 : Blo 2231435 3178121 := bstep (se 2 (by rfl) ⟨1191795, by rfl⟩ : syracuseStep 3178121 = 2383591) B2383591
theorem B8474989 : Blo 2231435 8474989 := bstep (se 3 (by rfl) ⟨1589060, by rfl⟩ : syracuseStep 8474989 = 3178121) B3178121
theorem B11299985 : Blo 2231435 11299985 := bstep (se 2 (by rfl) ⟨4237494, by rfl⟩ : syracuseStep 11299985 = 8474989) B8474989
theorem B7533323 : Blo 2231435 7533323 := bstep (se 1 (by rfl) ⟨5649992, by rfl⟩ : syracuseStep 7533323 = 11299985) B11299985
theorem B5022215 : Blo 2231435 5022215 := bstep (se 1 (by rfl) ⟨3766661, by rfl⟩ : syracuseStep 5022215 = 7533323) B7533323
theorem B3348143 : Blo 2231435 3348143 := bstep (se 1 (by rfl) ⟨2511107, by rfl⟩ : syracuseStep 3348143 = 5022215) B5022215
theorem B2232095 : Blo 2231435 2232095 := bstep (se 1 (by rfl) ⟨1674071, by rfl⟩ : syracuseStep 2232095 = 3348143) B3348143
theorem B3348149 : Blo 2231435 3348149 := bbase (se 5 (by rfl) ⟨156944, by rfl⟩ : syracuseStep 3348149 = 313889) (by norm_num)
theorem B2232099 : Blo 2231435 2232099 := bstep (se 1 (by rfl) ⟨1674074, by rfl⟩ : syracuseStep 2232099 = 3348149) B3348149
theorem B5650013 : Blo 2231435 5650013 := bbase (se 3 (by rfl) ⟨1059377, by rfl⟩ : syracuseStep 5650013 = 2118755) (by norm_num)
theorem B3766675 : Blo 2231435 3766675 := bstep (se 1 (by rfl) ⟨2825006, by rfl⟩ : syracuseStep 3766675 = 5650013) B5650013
theorem B5022233 : Blo 2231435 5022233 := bstep (se 2 (by rfl) ⟨1883337, by rfl⟩ : syracuseStep 5022233 = 3766675) B3766675
theorem B3348155 : Blo 2231435 3348155 := bstep (se 1 (by rfl) ⟨2511116, by rfl⟩ : syracuseStep 3348155 = 5022233) B5022233
theorem B2232103 : Blo 2231435 2232103 := bstep (se 1 (by rfl) ⟨1674077, by rfl⟩ : syracuseStep 2232103 = 3348155) B3348155
theorem B2511121 : Blo 2231435 2511121 := bbase (se 2 (by rfl) ⟨941670, by rfl⟩ : syracuseStep 2511121 = 1883341) (by norm_num)
theorem B3348161 : Blo 2231435 3348161 := bstep (se 2 (by rfl) ⟨1255560, by rfl⟩ : syracuseStep 3348161 = 2511121) B2511121
theorem B2232107 : Blo 2231435 2232107 := bstep (se 1 (by rfl) ⟨1674080, by rfl⟩ : syracuseStep 2232107 = 3348161) B3348161
theorem B4237525 : Blo 2231435 4237525 := bbase (se 7 (by rfl) ⟨49658, by rfl⟩ : syracuseStep 4237525 = 99317) (by norm_num)
theorem B5650033 : Blo 2231435 5650033 := bstep (se 2 (by rfl) ⟨2118762, by rfl⟩ : syracuseStep 5650033 = 4237525) B4237525
theorem B7533377 : Blo 2231435 7533377 := bstep (se 2 (by rfl) ⟨2825016, by rfl⟩ : syracuseStep 7533377 = 5650033) B5650033
theorem B5022251 : Blo 2231435 5022251 := bstep (se 1 (by rfl) ⟨3766688, by rfl⟩ : syracuseStep 5022251 = 7533377) B7533377
theorem B3348167 : Blo 2231435 3348167 := bstep (se 1 (by rfl) ⟨2511125, by rfl⟩ : syracuseStep 3348167 = 5022251) B5022251
theorem B2232111 : Blo 2231435 2232111 := bstep (se 1 (by rfl) ⟨1674083, by rfl⟩ : syracuseStep 2232111 = 3348167) B3348167
theorem B3348173 : Blo 2231435 3348173 := bbase (se 3 (by rfl) ⟨627782, by rfl⟩ : syracuseStep 3348173 = 1255565) (by norm_num)
theorem B2232115 : Blo 2231435 2232115 := bstep (se 1 (by rfl) ⟨1674086, by rfl⟩ : syracuseStep 2232115 = 3348173) B3348173
theorem B5022269 : Blo 2231435 5022269 := bbase (se 3 (by rfl) ⟨941675, by rfl⟩ : syracuseStep 5022269 = 1883351) (by norm_num)
theorem B3348179 : Blo 2231435 3348179 := bstep (se 1 (by rfl) ⟨2511134, by rfl⟩ : syracuseStep 3348179 = 5022269) B5022269
theorem B2232119 : Blo 2231435 2232119 := bstep (se 1 (by rfl) ⟨1674089, by rfl⟩ : syracuseStep 2232119 = 3348179) B3348179
theorem B3766709 : Blo 2231435 3766709 := bbase (se 5 (by rfl) ⟨176564, by rfl⟩ : syracuseStep 3766709 = 353129) (by norm_num)
theorem B2511139 : Blo 2231435 2511139 := bstep (se 1 (by rfl) ⟨1883354, by rfl⟩ : syracuseStep 2511139 = 3766709) B3766709
theorem B3348185 : Blo 2231435 3348185 := bstep (se 2 (by rfl) ⟨1255569, by rfl⟩ : syracuseStep 3348185 = 2511139) B2511139
theorem B2232123 : Blo 2231435 2232123 := bstep (se 1 (by rfl) ⟨1674092, by rfl⟩ : syracuseStep 2232123 = 3348185) B3348185
theorem B2383625 : Blo 2231435 2383625 := bbase (se 2 (by rfl) ⟨893859, by rfl⟩ : syracuseStep 2383625 = 1787719) (by norm_num)
theorem B6356333 : Blo 2231435 6356333 := bstep (se 3 (by rfl) ⟨1191812, by rfl⟩ : syracuseStep 6356333 = 2383625) B2383625
theorem B16950221 : Blo 2231435 16950221 := bstep (se 3 (by rfl) ⟨3178166, by rfl⟩ : syracuseStep 16950221 = 6356333) B6356333
theorem B11300147 : Blo 2231435 11300147 := bstep (se 1 (by rfl) ⟨8475110, by rfl⟩ : syracuseStep 11300147 = 16950221) B16950221
theorem B7533431 : Blo 2231435 7533431 := bstep (se 1 (by rfl) ⟨5650073, by rfl⟩ : syracuseStep 7533431 = 11300147) B11300147
theorem B5022287 : Blo 2231435 5022287 := bstep (se 1 (by rfl) ⟨3766715, by rfl⟩ : syracuseStep 5022287 = 7533431) B7533431
theorem B3348191 : Blo 2231435 3348191 := bstep (se 1 (by rfl) ⟨2511143, by rfl⟩ : syracuseStep 3348191 = 5022287) B5022287
theorem B2232127 : Blo 2231435 2232127 := bstep (se 1 (by rfl) ⟨1674095, by rfl⟩ : syracuseStep 2232127 = 3348191) B3348191
theorem B3348197 : Blo 2231435 3348197 := bbase (se 4 (by rfl) ⟨313893, by rfl⟩ : syracuseStep 3348197 = 627787) (by norm_num)
theorem B2232131 : Blo 2231435 2232131 := bstep (se 1 (by rfl) ⟨1674098, by rfl⟩ : syracuseStep 2232131 = 3348197) B3348197
theorem B6356357 : Blo 2231435 6356357 := bbase (se 4 (by rfl) ⟨595908, by rfl⟩ : syracuseStep 6356357 = 1191817) (by norm_num)
theorem B4237571 : Blo 2231435 4237571 := bstep (se 1 (by rfl) ⟨3178178, by rfl⟩ : syracuseStep 4237571 = 6356357) B6356357
theorem B2825047 : Blo 2231435 2825047 := bstep (se 1 (by rfl) ⟨2118785, by rfl⟩ : syracuseStep 2825047 = 4237571) B4237571
theorem B3766729 : Blo 2231435 3766729 := bstep (se 2 (by rfl) ⟨1412523, by rfl⟩ : syracuseStep 3766729 = 2825047) B2825047
theorem B5022305 : Blo 2231435 5022305 := bstep (se 2 (by rfl) ⟨1883364, by rfl⟩ : syracuseStep 5022305 = 3766729) B3766729
theorem B3348203 : Blo 2231435 3348203 := bstep (se 1 (by rfl) ⟨2511152, by rfl⟩ : syracuseStep 3348203 = 5022305) B5022305
theorem B2232135 : Blo 2231435 2232135 := bstep (se 1 (by rfl) ⟨1674101, by rfl⟩ : syracuseStep 2232135 = 3348203) B3348203
theorem B2511157 : Blo 2231435 2511157 := bbase (se 5 (by rfl) ⟨117710, by rfl⟩ : syracuseStep 2511157 = 235421) (by norm_num)
theorem B3348209 : Blo 2231435 3348209 := bstep (se 2 (by rfl) ⟨1255578, by rfl⟩ : syracuseStep 3348209 = 2511157) B2511157
theorem B2232139 : Blo 2231435 2232139 := bstep (se 1 (by rfl) ⟨1674104, by rfl⟩ : syracuseStep 2232139 = 3348209) B3348209
theorem B2825057 : Blo 2231435 2825057 := bbase (se 2 (by rfl) ⟨1059396, by rfl⟩ : syracuseStep 2825057 = 2118793) (by norm_num)
theorem B7533485 : Blo 2231435 7533485 := bstep (se 3 (by rfl) ⟨1412528, by rfl⟩ : syracuseStep 7533485 = 2825057) B2825057
theorem B5022323 : Blo 2231435 5022323 := bstep (se 1 (by rfl) ⟨3766742, by rfl⟩ : syracuseStep 5022323 = 7533485) B7533485
theorem B3348215 : Blo 2231435 3348215 := bstep (se 1 (by rfl) ⟨2511161, by rfl⟩ : syracuseStep 3348215 = 5022323) B5022323
theorem B2232143 : Blo 2231435 2232143 := bstep (se 1 (by rfl) ⟨1674107, by rfl⟩ : syracuseStep 2232143 = 3348215) B3348215
theorem B3348221 : Blo 2231435 3348221 := bbase (se 3 (by rfl) ⟨627791, by rfl⟩ : syracuseStep 3348221 = 1255583) (by norm_num)
theorem B2232147 : Blo 2231435 2232147 := bstep (se 1 (by rfl) ⟨1674110, by rfl⟩ : syracuseStep 2232147 = 3348221) B3348221
theorem B5022341 : Blo 2231435 5022341 := bbase (se 4 (by rfl) ⟨470844, by rfl⟩ : syracuseStep 5022341 = 941689) (by norm_num)
theorem B3348227 : Blo 2231435 3348227 := bstep (se 1 (by rfl) ⟨2511170, by rfl⟩ : syracuseStep 3348227 = 5022341) B5022341
theorem B2232151 : Blo 2231435 2232151 := bstep (se 1 (by rfl) ⟨1674113, by rfl⟩ : syracuseStep 2232151 = 3348227) B3348227
theorem B3393917 : Blo 2231435 3393917 := bbase (se 3 (by rfl) ⟨636359, by rfl⟩ : syracuseStep 3393917 = 1272719) (by norm_num)
theorem B2262611 : Blo 2231435 2262611 := bstep (se 1 (by rfl) ⟨1696958, by rfl⟩ : syracuseStep 2262611 = 3393917) B3393917
theorem B6033629 : Blo 2231435 6033629 := bstep (se 3 (by rfl) ⟨1131305, by rfl⟩ : syracuseStep 6033629 = 2262611) B2262611
theorem B16089677 : Blo 2231435 16089677 := bstep (se 3 (by rfl) ⟨3016814, by rfl⟩ : syracuseStep 16089677 = 6033629) B6033629
theorem B10726451 : Blo 2231435 10726451 := bstep (se 1 (by rfl) ⟨8044838, by rfl⟩ : syracuseStep 10726451 = 16089677) B16089677
theorem B7150967 : Blo 2231435 7150967 := bstep (se 1 (by rfl) ⟨5363225, by rfl⟩ : syracuseStep 7150967 = 10726451) B10726451
theorem B4767311 : Blo 2231435 4767311 := bstep (se 1 (by rfl) ⟨3575483, by rfl⟩ : syracuseStep 4767311 = 7150967) B7150967
theorem B3178207 : Blo 2231435 3178207 := bstep (se 1 (by rfl) ⟨2383655, by rfl⟩ : syracuseStep 3178207 = 4767311) B4767311
theorem B4237609 : Blo 2231435 4237609 := bstep (se 2 (by rfl) ⟨1589103, by rfl⟩ : syracuseStep 4237609 = 3178207) B3178207
theorem B5650145 : Blo 2231435 5650145 := bstep (se 2 (by rfl) ⟨2118804, by rfl⟩ : syracuseStep 5650145 = 4237609) B4237609
theorem B3766763 : Blo 2231435 3766763 := bstep (se 1 (by rfl) ⟨2825072, by rfl⟩ : syracuseStep 3766763 = 5650145) B5650145
theorem B2511175 : Blo 2231435 2511175 := bstep (se 1 (by rfl) ⟨1883381, by rfl⟩ : syracuseStep 2511175 = 3766763) B3766763
theorem B3348233 : Blo 2231435 3348233 := bstep (se 2 (by rfl) ⟨1255587, by rfl⟩ : syracuseStep 3348233 = 2511175) B2511175
theorem B2232155 : Blo 2231435 2232155 := bstep (se 1 (by rfl) ⟨1674116, by rfl⟩ : syracuseStep 2232155 = 3348233) B3348233
theorem B11300309 : Blo 2231435 11300309 := bbase (se 7 (by rfl) ⟨132425, by rfl⟩ : syracuseStep 11300309 = 264851) (by norm_num)
theorem B7533539 : Blo 2231435 7533539 := bstep (se 1 (by rfl) ⟨5650154, by rfl⟩ : syracuseStep 7533539 = 11300309) B11300309
theorem B5022359 : Blo 2231435 5022359 := bstep (se 1 (by rfl) ⟨3766769, by rfl⟩ : syracuseStep 5022359 = 7533539) B7533539
theorem B3348239 : Blo 2231435 3348239 := bstep (se 1 (by rfl) ⟨2511179, by rfl⟩ : syracuseStep 3348239 = 5022359) B5022359
theorem B2232159 : Blo 2231435 2232159 := bstep (se 1 (by rfl) ⟨1674119, by rfl⟩ : syracuseStep 2232159 = 3348239) B3348239
theorem B3348245 : Blo 2231435 3348245 := bbase (se 6 (by rfl) ⟨78474, by rfl⟩ : syracuseStep 3348245 = 156949) (by norm_num)
theorem B2232163 : Blo 2231435 2232163 := bstep (se 1 (by rfl) ⟨1674122, by rfl⟩ : syracuseStep 2232163 = 3348245) B3348245
theorem B3310093 : Blo 2231435 3310093 := bbase (se 3 (by rfl) ⟨620642, by rfl⟩ : syracuseStep 3310093 = 1241285) (by norm_num)
theorem B4413457 : Blo 2231435 4413457 := bstep (se 2 (by rfl) ⟨1655046, by rfl⟩ : syracuseStep 4413457 = 3310093) B3310093
theorem B23538437 : Blo 2231435 23538437 := bstep (se 4 (by rfl) ⟨2206728, by rfl⟩ : syracuseStep 23538437 = 4413457) B4413457
theorem B15692291 : Blo 2231435 15692291 := bstep (se 1 (by rfl) ⟨11769218, by rfl⟩ : syracuseStep 15692291 = 23538437) B23538437
theorem B10461527 : Blo 2231435 10461527 := bstep (se 1 (by rfl) ⟨7846145, by rfl⟩ : syracuseStep 10461527 = 15692291) B15692291
theorem B6974351 : Blo 2231435 6974351 := bstep (se 1 (by rfl) ⟨5230763, by rfl⟩ : syracuseStep 6974351 = 10461527) B10461527
theorem B4649567 : Blo 2231435 4649567 := bstep (se 1 (by rfl) ⟨3487175, by rfl⟩ : syracuseStep 4649567 = 6974351) B6974351
theorem B12398845 : Blo 2231435 12398845 := bstep (se 3 (by rfl) ⟨2324783, by rfl⟩ : syracuseStep 12398845 = 4649567) B4649567
theorem B16531793 : Blo 2231435 16531793 := bstep (se 2 (by rfl) ⟨6199422, by rfl⟩ : syracuseStep 16531793 = 12398845) B12398845
theorem B11021195 : Blo 2231435 11021195 := bstep (se 1 (by rfl) ⟨8265896, by rfl⟩ : syracuseStep 11021195 = 16531793) B16531793
theorem B29389853 : Blo 2231435 29389853 := bstep (se 3 (by rfl) ⟨5510597, by rfl⟩ : syracuseStep 29389853 = 11021195) B11021195
theorem B19593235 : Blo 2231435 19593235 := bstep (se 1 (by rfl) ⟨14694926, by rfl⟩ : syracuseStep 19593235 = 29389853) B29389853
theorem B104497253 : Blo 2231435 104497253 := bstep (se 4 (by rfl) ⟨9796617, by rfl⟩ : syracuseStep 104497253 = 19593235) B19593235
theorem B69664835 : Blo 2231435 69664835 := bstep (se 1 (by rfl) ⟨52248626, by rfl⟩ : syracuseStep 69664835 = 104497253) B104497253
theorem B46443223 : Blo 2231435 46443223 := bstep (se 1 (by rfl) ⟨34832417, by rfl⟩ : syracuseStep 46443223 = 69664835) B69664835
theorem B61924297 : Blo 2231435 61924297 := bstep (se 2 (by rfl) ⟨23221611, by rfl⟩ : syracuseStep 61924297 = 46443223) B46443223
theorem B82565729 : Blo 2231435 82565729 := bstep (se 2 (by rfl) ⟨30962148, by rfl⟩ : syracuseStep 82565729 = 61924297) B61924297
theorem B55043819 : Blo 2231435 55043819 := bstep (se 1 (by rfl) ⟨41282864, by rfl⟩ : syracuseStep 55043819 = 82565729) B82565729
theorem B36695879 : Blo 2231435 36695879 := bstep (se 1 (by rfl) ⟨27521909, by rfl⟩ : syracuseStep 36695879 = 55043819) B55043819
theorem B24463919 : Blo 2231435 24463919 := bstep (se 1 (by rfl) ⟨18347939, by rfl⟩ : syracuseStep 24463919 = 36695879) B36695879
theorem B16309279 : Blo 2231435 16309279 := bstep (se 1 (by rfl) ⟨12231959, by rfl⟩ : syracuseStep 16309279 = 24463919) B24463919
theorem B21745705 : Blo 2231435 21745705 := bstep (se 2 (by rfl) ⟨8154639, by rfl⟩ : syracuseStep 21745705 = 16309279) B16309279
theorem B28994273 : Blo 2231435 28994273 := bstep (se 2 (by rfl) ⟨10872852, by rfl⟩ : syracuseStep 28994273 = 21745705) B21745705
theorem B19329515 : Blo 2231435 19329515 := bstep (se 1 (by rfl) ⟨14497136, by rfl⟩ : syracuseStep 19329515 = 28994273) B28994273
theorem B12886343 : Blo 2231435 12886343 := bstep (se 1 (by rfl) ⟨9664757, by rfl⟩ : syracuseStep 12886343 = 19329515) B19329515
theorem B8590895 : Blo 2231435 8590895 := bstep (se 1 (by rfl) ⟨6443171, by rfl⟩ : syracuseStep 8590895 = 12886343) B12886343
theorem B5727263 : Blo 2231435 5727263 := bstep (se 1 (by rfl) ⟨4295447, by rfl⟩ : syracuseStep 5727263 = 8590895) B8590895
theorem B15272701 : Blo 2231435 15272701 := bstep (se 3 (by rfl) ⟨2863631, by rfl⟩ : syracuseStep 15272701 = 5727263) B5727263
theorem B81454405 : Blo 2231435 81454405 := bstep (se 4 (by rfl) ⟨7636350, by rfl⟩ : syracuseStep 81454405 = 15272701) B15272701
theorem B108605873 : Blo 2231435 108605873 := bstep (se 2 (by rfl) ⟨40727202, by rfl⟩ : syracuseStep 108605873 = 81454405) B81454405
theorem B72403915 : Blo 2231435 72403915 := bstep (se 1 (by rfl) ⟨54302936, by rfl⟩ : syracuseStep 72403915 = 108605873) B108605873
theorem B96538553 : Blo 2231435 96538553 := bstep (se 2 (by rfl) ⟨36201957, by rfl⟩ : syracuseStep 96538553 = 72403915) B72403915
theorem B64359035 : Blo 2231435 64359035 := bstep (se 1 (by rfl) ⟨48269276, by rfl⟩ : syracuseStep 64359035 = 96538553) B96538553
theorem B42906023 : Blo 2231435 42906023 := bstep (se 1 (by rfl) ⟨32179517, by rfl⟩ : syracuseStep 42906023 = 64359035) B64359035
theorem B28604015 : Blo 2231435 28604015 := bstep (se 1 (by rfl) ⟨21453011, by rfl⟩ : syracuseStep 28604015 = 42906023) B42906023
theorem B19069343 : Blo 2231435 19069343 := bstep (se 1 (by rfl) ⟨14302007, by rfl⟩ : syracuseStep 19069343 = 28604015) B28604015
theorem B12712895 : Blo 2231435 12712895 := bstep (se 1 (by rfl) ⟨9534671, by rfl⟩ : syracuseStep 12712895 = 19069343) B19069343
theorem B8475263 : Blo 2231435 8475263 := bstep (se 1 (by rfl) ⟨6356447, by rfl⟩ : syracuseStep 8475263 = 12712895) B12712895
theorem B5650175 : Blo 2231435 5650175 := bstep (se 1 (by rfl) ⟨4237631, by rfl⟩ : syracuseStep 5650175 = 8475263) B8475263
theorem B3766783 : Blo 2231435 3766783 := bstep (se 1 (by rfl) ⟨2825087, by rfl⟩ : syracuseStep 3766783 = 5650175) B5650175
theorem B5022377 : Blo 2231435 5022377 := bstep (se 2 (by rfl) ⟨1883391, by rfl⟩ : syracuseStep 5022377 = 3766783) B3766783
theorem B3348251 : Blo 2231435 3348251 := bstep (se 1 (by rfl) ⟨2511188, by rfl⟩ : syracuseStep 3348251 = 5022377) B5022377
theorem B2232167 : Blo 2231435 2232167 := bstep (se 1 (by rfl) ⟨1674125, by rfl⟩ : syracuseStep 2232167 = 3348251) B3348251
theorem B2511193 : Blo 2231435 2511193 := bbase (se 2 (by rfl) ⟨941697, by rfl⟩ : syracuseStep 2511193 = 1883395) (by norm_num)
theorem B3348257 : Blo 2231435 3348257 := bstep (se 2 (by rfl) ⟨1255596, by rfl⟩ : syracuseStep 3348257 = 2511193) B2511193
theorem B2232171 : Blo 2231435 2232171 := bstep (se 1 (by rfl) ⟨1674128, by rfl⟩ : syracuseStep 2232171 = 3348257) B3348257
theorem B4587005 : Blo 2231435 4587005 := bbase (se 3 (by rfl) ⟨860063, by rfl⟩ : syracuseStep 4587005 = 1720127) (by norm_num)
theorem B3058003 : Blo 2231435 3058003 := bstep (se 1 (by rfl) ⟨2293502, by rfl⟩ : syracuseStep 3058003 = 4587005) B4587005
theorem B16309349 : Blo 2231435 16309349 := bstep (se 4 (by rfl) ⟨1529001, by rfl⟩ : syracuseStep 16309349 = 3058003) B3058003
theorem B10872899 : Blo 2231435 10872899 := bstep (se 1 (by rfl) ⟨8154674, by rfl⟩ : syracuseStep 10872899 = 16309349) B16309349
theorem B7248599 : Blo 2231435 7248599 := bstep (se 1 (by rfl) ⟨5436449, by rfl⟩ : syracuseStep 7248599 = 10872899) B10872899
theorem B4832399 : Blo 2231435 4832399 := bstep (se 1 (by rfl) ⟨3624299, by rfl⟩ : syracuseStep 4832399 = 7248599) B7248599
theorem B12886397 : Blo 2231435 12886397 := bstep (se 3 (by rfl) ⟨2416199, by rfl⟩ : syracuseStep 12886397 = 4832399) B4832399
theorem B8590931 : Blo 2231435 8590931 := bstep (se 1 (by rfl) ⟨6443198, by rfl⟩ : syracuseStep 8590931 = 12886397) B12886397
theorem B5727287 : Blo 2231435 5727287 := bstep (se 1 (by rfl) ⟨4295465, by rfl⟩ : syracuseStep 5727287 = 8590931) B8590931
theorem B3818191 : Blo 2231435 3818191 := bstep (se 1 (by rfl) ⟨2863643, by rfl⟩ : syracuseStep 3818191 = 5727287) B5727287
theorem B5090921 : Blo 2231435 5090921 := bstep (se 2 (by rfl) ⟨1909095, by rfl⟩ : syracuseStep 5090921 = 3818191) B3818191
theorem B3393947 : Blo 2231435 3393947 := bstep (se 1 (by rfl) ⟨2545460, by rfl⟩ : syracuseStep 3393947 = 5090921) B5090921
theorem B9050525 : Blo 2231435 9050525 := bstep (se 3 (by rfl) ⟨1696973, by rfl⟩ : syracuseStep 9050525 = 3393947) B3393947
theorem B6033683 : Blo 2231435 6033683 := bstep (se 1 (by rfl) ⟨4525262, by rfl⟩ : syracuseStep 6033683 = 9050525) B9050525
theorem B4022455 : Blo 2231435 4022455 := bstep (se 1 (by rfl) ⟨3016841, by rfl⟩ : syracuseStep 4022455 = 6033683) B6033683
theorem B5363273 : Blo 2231435 5363273 := bstep (se 2 (by rfl) ⟨2011227, by rfl⟩ : syracuseStep 5363273 = 4022455) B4022455
theorem B3575515 : Blo 2231435 3575515 := bstep (se 1 (by rfl) ⟨2681636, by rfl⟩ : syracuseStep 3575515 = 5363273) B5363273
theorem B4767353 : Blo 2231435 4767353 := bstep (se 2 (by rfl) ⟨1787757, by rfl⟩ : syracuseStep 4767353 = 3575515) B3575515
theorem B3178235 : Blo 2231435 3178235 := bstep (se 1 (by rfl) ⟨2383676, by rfl⟩ : syracuseStep 3178235 = 4767353) B4767353
theorem B8475293 : Blo 2231435 8475293 := bstep (se 3 (by rfl) ⟨1589117, by rfl⟩ : syracuseStep 8475293 = 3178235) B3178235
theorem B5650195 : Blo 2231435 5650195 := bstep (se 1 (by rfl) ⟨4237646, by rfl⟩ : syracuseStep 5650195 = 8475293) B8475293
theorem B7533593 : Blo 2231435 7533593 := bstep (se 2 (by rfl) ⟨2825097, by rfl⟩ : syracuseStep 7533593 = 5650195) B5650195
theorem B5022395 : Blo 2231435 5022395 := bstep (se 1 (by rfl) ⟨3766796, by rfl⟩ : syracuseStep 5022395 = 7533593) B7533593
theorem B3348263 : Blo 2231435 3348263 := bstep (se 1 (by rfl) ⟨2511197, by rfl⟩ : syracuseStep 3348263 = 5022395) B5022395
theorem B2232175 : Blo 2231435 2232175 := bstep (se 1 (by rfl) ⟨1674131, by rfl⟩ : syracuseStep 2232175 = 3348263) B3348263
theorem B3348269 : Blo 2231435 3348269 := bbase (se 3 (by rfl) ⟨627800, by rfl⟩ : syracuseStep 3348269 = 1255601) (by norm_num)
theorem B2232179 : Blo 2231435 2232179 := bstep (se 1 (by rfl) ⟨1674134, by rfl⟩ : syracuseStep 2232179 = 3348269) B3348269
theorem B5022413 : Blo 2231435 5022413 := bbase (se 3 (by rfl) ⟨941702, by rfl⟩ : syracuseStep 5022413 = 1883405) (by norm_num)
theorem B3348275 : Blo 2231435 3348275 := bstep (se 1 (by rfl) ⟨2511206, by rfl⟩ : syracuseStep 3348275 = 5022413) B5022413
theorem B2232183 : Blo 2231435 2232183 := bstep (se 1 (by rfl) ⟨1674137, by rfl⟩ : syracuseStep 2232183 = 3348275) B3348275
theorem B2825113 : Blo 2231435 2825113 := bbase (se 2 (by rfl) ⟨1059417, by rfl⟩ : syracuseStep 2825113 = 2118835) (by norm_num)
theorem B3766817 : Blo 2231435 3766817 := bstep (se 2 (by rfl) ⟨1412556, by rfl⟩ : syracuseStep 3766817 = 2825113) B2825113
theorem B2511211 : Blo 2231435 2511211 := bstep (se 1 (by rfl) ⟨1883408, by rfl⟩ : syracuseStep 2511211 = 3766817) B3766817
theorem B3348281 : Blo 2231435 3348281 := bstep (se 2 (by rfl) ⟨1255605, by rfl⟩ : syracuseStep 3348281 = 2511211) B2511211
theorem B2232187 : Blo 2231435 2232187 := bstep (se 1 (by rfl) ⟨1674140, by rfl⟩ : syracuseStep 2232187 = 3348281) B3348281
theorem B9534773 : Blo 2231435 9534773 := bbase (se 5 (by rfl) ⟨446942, by rfl⟩ : syracuseStep 9534773 = 893885) (by norm_num)
theorem B25426061 : Blo 2231435 25426061 := bstep (se 3 (by rfl) ⟨4767386, by rfl⟩ : syracuseStep 25426061 = 9534773) B9534773
theorem B16950707 : Blo 2231435 16950707 := bstep (se 1 (by rfl) ⟨12713030, by rfl⟩ : syracuseStep 16950707 = 25426061) B25426061
theorem B11300471 : Blo 2231435 11300471 := bstep (se 1 (by rfl) ⟨8475353, by rfl⟩ : syracuseStep 11300471 = 16950707) B16950707
theorem B7533647 : Blo 2231435 7533647 := bstep (se 1 (by rfl) ⟨5650235, by rfl⟩ : syracuseStep 7533647 = 11300471) B11300471
theorem B5022431 : Blo 2231435 5022431 := bstep (se 1 (by rfl) ⟨3766823, by rfl⟩ : syracuseStep 5022431 = 7533647) B7533647
theorem B3348287 : Blo 2231435 3348287 := bstep (se 1 (by rfl) ⟨2511215, by rfl⟩ : syracuseStep 3348287 = 5022431) B5022431
theorem B2232191 : Blo 2231435 2232191 := bstep (se 1 (by rfl) ⟨1674143, by rfl⟩ : syracuseStep 2232191 = 3348287) B3348287
theorem B3348293 : Blo 2231435 3348293 := bbase (se 4 (by rfl) ⟨313902, by rfl⟩ : syracuseStep 3348293 = 627805) (by norm_num)
theorem B2232195 : Blo 2231435 2232195 := bstep (se 1 (by rfl) ⟨1674146, by rfl⟩ : syracuseStep 2232195 = 3348293) B3348293
theorem B3766837 : Blo 2231435 3766837 := bbase (se 5 (by rfl) ⟨176570, by rfl⟩ : syracuseStep 3766837 = 353141) (by norm_num)
theorem B5022449 : Blo 2231435 5022449 := bstep (se 2 (by rfl) ⟨1883418, by rfl⟩ : syracuseStep 5022449 = 3766837) B3766837
theorem B3348299 : Blo 2231435 3348299 := bstep (se 1 (by rfl) ⟨2511224, by rfl⟩ : syracuseStep 3348299 = 5022449) B5022449
theorem B2232199 : Blo 2231435 2232199 := bstep (se 1 (by rfl) ⟨1674149, by rfl⟩ : syracuseStep 2232199 = 3348299) B3348299
theorem B2511229 : Blo 2231435 2511229 := bbase (se 3 (by rfl) ⟨470855, by rfl⟩ : syracuseStep 2511229 = 941711) (by norm_num)
theorem B3348305 : Blo 2231435 3348305 := bstep (se 2 (by rfl) ⟨1255614, by rfl⟩ : syracuseStep 3348305 = 2511229) B2511229
theorem B2232203 : Blo 2231435 2232203 := bstep (se 1 (by rfl) ⟨1674152, by rfl⟩ : syracuseStep 2232203 = 3348305) B3348305
theorem B7533701 : Blo 2231435 7533701 := bbase (se 4 (by rfl) ⟨706284, by rfl⟩ : syracuseStep 7533701 = 1412569) (by norm_num)
theorem B5022467 : Blo 2231435 5022467 := bstep (se 1 (by rfl) ⟨3766850, by rfl⟩ : syracuseStep 5022467 = 7533701) B7533701
theorem B3348311 : Blo 2231435 3348311 := bstep (se 1 (by rfl) ⟨2511233, by rfl⟩ : syracuseStep 3348311 = 5022467) B5022467
theorem B2232207 : Blo 2231435 2232207 := bstep (se 1 (by rfl) ⟨1674155, by rfl⟩ : syracuseStep 2232207 = 3348311) B3348311
theorem B3348317 : Blo 2231435 3348317 := bbase (se 3 (by rfl) ⟨627809, by rfl⟩ : syracuseStep 3348317 = 1255619) (by norm_num)
theorem B2232211 : Blo 2231435 2232211 := bstep (se 1 (by rfl) ⟨1674158, by rfl⟩ : syracuseStep 2232211 = 3348317) B3348317
theorem B5022485 : Blo 2231435 5022485 := bbase (se 6 (by rfl) ⟨117714, by rfl⟩ : syracuseStep 5022485 = 235429) (by norm_num)
theorem B3348323 : Blo 2231435 3348323 := bstep (se 1 (by rfl) ⟨2511242, by rfl⟩ : syracuseStep 3348323 = 5022485) B5022485
theorem B2232215 : Blo 2231435 2232215 := bstep (se 1 (by rfl) ⟨1674161, by rfl⟩ : syracuseStep 2232215 = 3348323) B3348323
theorem B8475461 : Blo 2231435 8475461 := bbase (se 4 (by rfl) ⟨794574, by rfl⟩ : syracuseStep 8475461 = 1589149) (by norm_num)
theorem B5650307 : Blo 2231435 5650307 := bstep (se 1 (by rfl) ⟨4237730, by rfl⟩ : syracuseStep 5650307 = 8475461) B8475461
theorem B3766871 : Blo 2231435 3766871 := bstep (se 1 (by rfl) ⟨2825153, by rfl⟩ : syracuseStep 3766871 = 5650307) B5650307
theorem B2511247 : Blo 2231435 2511247 := bstep (se 1 (by rfl) ⟨1883435, by rfl⟩ : syracuseStep 2511247 = 3766871) B3766871
theorem B3348329 : Blo 2231435 3348329 := bstep (se 2 (by rfl) ⟨1255623, by rfl⟩ : syracuseStep 3348329 = 2511247) B2511247
theorem B2232219 : Blo 2231435 2232219 := bstep (se 1 (by rfl) ⟨1674164, by rfl⟩ : syracuseStep 2232219 = 3348329) B3348329
theorem B5091029 : Blo 2231435 5091029 := bbase (se 7 (by rfl) ⟨59660, by rfl⟩ : syracuseStep 5091029 = 119321) (by norm_num)
theorem B3394019 : Blo 2231435 3394019 := bstep (se 1 (by rfl) ⟨2545514, by rfl⟩ : syracuseStep 3394019 = 5091029) B5091029
theorem B9050717 : Blo 2231435 9050717 := bstep (se 3 (by rfl) ⟨1697009, by rfl⟩ : syracuseStep 9050717 = 3394019) B3394019
theorem B24135245 : Blo 2231435 24135245 := bstep (se 3 (by rfl) ⟨4525358, by rfl⟩ : syracuseStep 24135245 = 9050717) B9050717
theorem B16090163 : Blo 2231435 16090163 := bstep (se 1 (by rfl) ⟨12067622, by rfl⟩ : syracuseStep 16090163 = 24135245) B24135245
theorem B10726775 : Blo 2231435 10726775 := bstep (se 1 (by rfl) ⟨8045081, by rfl⟩ : syracuseStep 10726775 = 16090163) B16090163
theorem B7151183 : Blo 2231435 7151183 := bstep (se 1 (by rfl) ⟨5363387, by rfl⟩ : syracuseStep 7151183 = 10726775) B10726775
theorem B4767455 : Blo 2231435 4767455 := bstep (se 1 (by rfl) ⟨3575591, by rfl⟩ : syracuseStep 4767455 = 7151183) B7151183
theorem B12713213 : Blo 2231435 12713213 := bstep (se 3 (by rfl) ⟨2383727, by rfl⟩ : syracuseStep 12713213 = 4767455) B4767455
theorem B8475475 : Blo 2231435 8475475 := bstep (se 1 (by rfl) ⟨6356606, by rfl⟩ : syracuseStep 8475475 = 12713213) B12713213
theorem B11300633 : Blo 2231435 11300633 := bstep (se 2 (by rfl) ⟨4237737, by rfl⟩ : syracuseStep 11300633 = 8475475) B8475475
theorem B7533755 : Blo 2231435 7533755 := bstep (se 1 (by rfl) ⟨5650316, by rfl⟩ : syracuseStep 7533755 = 11300633) B11300633
theorem B5022503 : Blo 2231435 5022503 := bstep (se 1 (by rfl) ⟨3766877, by rfl⟩ : syracuseStep 5022503 = 7533755) B7533755
theorem B3348335 : Blo 2231435 3348335 := bstep (se 1 (by rfl) ⟨2511251, by rfl⟩ : syracuseStep 3348335 = 5022503) B5022503
theorem B2232223 : Blo 2231435 2232223 := bstep (se 1 (by rfl) ⟨1674167, by rfl⟩ : syracuseStep 2232223 = 3348335) B3348335
theorem B3348341 : Blo 2231435 3348341 := bbase (se 5 (by rfl) ⟨156953, by rfl⟩ : syracuseStep 3348341 = 313907) (by norm_num)
theorem B2232227 : Blo 2231435 2232227 := bstep (se 1 (by rfl) ⟨1674170, by rfl⟩ : syracuseStep 2232227 = 3348341) B3348341
theorem B3575605 : Blo 2231435 3575605 := bbase (se 5 (by rfl) ⟨167606, by rfl⟩ : syracuseStep 3575605 = 335213) (by norm_num)
theorem B4767473 : Blo 2231435 4767473 := bstep (se 2 (by rfl) ⟨1787802, by rfl⟩ : syracuseStep 4767473 = 3575605) B3575605
theorem B3178315 : Blo 2231435 3178315 := bstep (se 1 (by rfl) ⟨2383736, by rfl⟩ : syracuseStep 3178315 = 4767473) B4767473
theorem B4237753 : Blo 2231435 4237753 := bstep (se 2 (by rfl) ⟨1589157, by rfl⟩ : syracuseStep 4237753 = 3178315) B3178315
theorem B5650337 : Blo 2231435 5650337 := bstep (se 2 (by rfl) ⟨2118876, by rfl⟩ : syracuseStep 5650337 = 4237753) B4237753
theorem B3766891 : Blo 2231435 3766891 := bstep (se 1 (by rfl) ⟨2825168, by rfl⟩ : syracuseStep 3766891 = 5650337) B5650337
theorem B5022521 : Blo 2231435 5022521 := bstep (se 2 (by rfl) ⟨1883445, by rfl⟩ : syracuseStep 5022521 = 3766891) B3766891
theorem B3348347 : Blo 2231435 3348347 := bstep (se 1 (by rfl) ⟨2511260, by rfl⟩ : syracuseStep 3348347 = 5022521) B5022521
theorem B2232231 : Blo 2231435 2232231 := bstep (se 1 (by rfl) ⟨1674173, by rfl⟩ : syracuseStep 2232231 = 3348347) B3348347
theorem B2511265 : Blo 2231435 2511265 := bbase (se 2 (by rfl) ⟨941724, by rfl⟩ : syracuseStep 2511265 = 1883449) (by norm_num)
theorem B3348353 : Blo 2231435 3348353 := bstep (se 2 (by rfl) ⟨1255632, by rfl⟩ : syracuseStep 3348353 = 2511265) B2511265
theorem B2232235 : Blo 2231435 2232235 := bstep (se 1 (by rfl) ⟨1674176, by rfl⟩ : syracuseStep 2232235 = 3348353) B3348353
theorem B5650357 : Blo 2231435 5650357 := bbase (se 5 (by rfl) ⟨264860, by rfl⟩ : syracuseStep 5650357 = 529721) (by norm_num)
theorem B7533809 : Blo 2231435 7533809 := bstep (se 2 (by rfl) ⟨2825178, by rfl⟩ : syracuseStep 7533809 = 5650357) B5650357
theorem B5022539 : Blo 2231435 5022539 := bstep (se 1 (by rfl) ⟨3766904, by rfl⟩ : syracuseStep 5022539 = 7533809) B7533809
theorem B3348359 : Blo 2231435 3348359 := bstep (se 1 (by rfl) ⟨2511269, by rfl⟩ : syracuseStep 3348359 = 5022539) B5022539
theorem B2232239 : Blo 2231435 2232239 := bstep (se 1 (by rfl) ⟨1674179, by rfl⟩ : syracuseStep 2232239 = 3348359) B3348359
theorem B3348365 : Blo 2231435 3348365 := bbase (se 3 (by rfl) ⟨627818, by rfl⟩ : syracuseStep 3348365 = 1255637) (by norm_num)
theorem B2232243 : Blo 2231435 2232243 := bstep (se 1 (by rfl) ⟨1674182, by rfl⟩ : syracuseStep 2232243 = 3348365) B3348365
theorem B5022557 : Blo 2231435 5022557 := bbase (se 3 (by rfl) ⟨941729, by rfl⟩ : syracuseStep 5022557 = 1883459) (by norm_num)
theorem B3348371 : Blo 2231435 3348371 := bstep (se 1 (by rfl) ⟨2511278, by rfl⟩ : syracuseStep 3348371 = 5022557) B5022557
theorem B2232247 : Blo 2231435 2232247 := bstep (se 1 (by rfl) ⟨1674185, by rfl⟩ : syracuseStep 2232247 = 3348371) B3348371
theorem B3766925 : Blo 2231435 3766925 := bbase (se 3 (by rfl) ⟨706298, by rfl⟩ : syracuseStep 3766925 = 1412597) (by norm_num)
theorem B2511283 : Blo 2231435 2511283 := bstep (se 1 (by rfl) ⟨1883462, by rfl⟩ : syracuseStep 2511283 = 3766925) B3766925
theorem B3348377 : Blo 2231435 3348377 := bstep (se 2 (by rfl) ⟨1255641, by rfl⟩ : syracuseStep 3348377 = 2511283) B2511283
theorem B2232251 : Blo 2231435 2232251 := bstep (se 1 (by rfl) ⟨1674188, by rfl⟩ : syracuseStep 2232251 = 3348377) B3348377
theorem B7151285 : Blo 2231435 7151285 := bbase (se 5 (by rfl) ⟨335216, by rfl⟩ : syracuseStep 7151285 = 670433) (by norm_num)
theorem B19070093 : Blo 2231435 19070093 := bstep (se 3 (by rfl) ⟨3575642, by rfl⟩ : syracuseStep 19070093 = 7151285) B7151285
theorem B12713395 : Blo 2231435 12713395 := bstep (se 1 (by rfl) ⟨9535046, by rfl⟩ : syracuseStep 12713395 = 19070093) B19070093
theorem B16951193 : Blo 2231435 16951193 := bstep (se 2 (by rfl) ⟨6356697, by rfl⟩ : syracuseStep 16951193 = 12713395) B12713395
theorem B11300795 : Blo 2231435 11300795 := bstep (se 1 (by rfl) ⟨8475596, by rfl⟩ : syracuseStep 11300795 = 16951193) B16951193
theorem B7533863 : Blo 2231435 7533863 := bstep (se 1 (by rfl) ⟨5650397, by rfl⟩ : syracuseStep 7533863 = 11300795) B11300795
theorem B5022575 : Blo 2231435 5022575 := bstep (se 1 (by rfl) ⟨3766931, by rfl⟩ : syracuseStep 5022575 = 7533863) B7533863
theorem B3348383 : Blo 2231435 3348383 := bstep (se 1 (by rfl) ⟨2511287, by rfl⟩ : syracuseStep 3348383 = 5022575) B5022575
theorem B2232255 : Blo 2231435 2232255 := bstep (se 1 (by rfl) ⟨1674191, by rfl⟩ : syracuseStep 2232255 = 3348383) B3348383
theorem B3348389 : Blo 2231435 3348389 := bbase (se 4 (by rfl) ⟨313911, by rfl⟩ : syracuseStep 3348389 = 627823) (by norm_num)
theorem B2232259 : Blo 2231435 2232259 := bstep (se 1 (by rfl) ⟨1674194, by rfl⟩ : syracuseStep 2232259 = 3348389) B3348389
theorem B2825209 : Blo 2231435 2825209 := bbase (se 2 (by rfl) ⟨1059453, by rfl⟩ : syracuseStep 2825209 = 2118907) (by norm_num)
theorem B3766945 : Blo 2231435 3766945 := bstep (se 2 (by rfl) ⟨1412604, by rfl⟩ : syracuseStep 3766945 = 2825209) B2825209
theorem B5022593 : Blo 2231435 5022593 := bstep (se 2 (by rfl) ⟨1883472, by rfl⟩ : syracuseStep 5022593 = 3766945) B3766945
theorem B3348395 : Blo 2231435 3348395 := bstep (se 1 (by rfl) ⟨2511296, by rfl⟩ : syracuseStep 3348395 = 5022593) B5022593
theorem B2232263 : Blo 2231435 2232263 := bstep (se 1 (by rfl) ⟨1674197, by rfl⟩ : syracuseStep 2232263 = 3348395) B3348395
theorem B2511301 : Blo 2231435 2511301 := bbase (se 4 (by rfl) ⟨235434, by rfl⟩ : syracuseStep 2511301 = 470869) (by norm_num)
theorem B3348401 : Blo 2231435 3348401 := bstep (se 2 (by rfl) ⟨1255650, by rfl⟩ : syracuseStep 3348401 = 2511301) B2511301
theorem B2232267 : Blo 2231435 2232267 := bstep (se 1 (by rfl) ⟨1674200, by rfl⟩ : syracuseStep 2232267 = 3348401) B3348401
theorem B4237829 : Blo 2231435 4237829 := bbase (se 4 (by rfl) ⟨397296, by rfl⟩ : syracuseStep 4237829 = 794593) (by norm_num)
theorem B2825219 : Blo 2231435 2825219 := bstep (se 1 (by rfl) ⟨2118914, by rfl⟩ : syracuseStep 2825219 = 4237829) B4237829
theorem B7533917 : Blo 2231435 7533917 := bstep (se 3 (by rfl) ⟨1412609, by rfl⟩ : syracuseStep 7533917 = 2825219) B2825219
theorem B5022611 : Blo 2231435 5022611 := bstep (se 1 (by rfl) ⟨3766958, by rfl⟩ : syracuseStep 5022611 = 7533917) B7533917
theorem B3348407 : Blo 2231435 3348407 := bstep (se 1 (by rfl) ⟨2511305, by rfl⟩ : syracuseStep 3348407 = 5022611) B5022611
theorem B2232271 : Blo 2231435 2232271 := bstep (se 1 (by rfl) ⟨1674203, by rfl⟩ : syracuseStep 2232271 = 3348407) B3348407
theorem B3348413 : Blo 2231435 3348413 := bbase (se 3 (by rfl) ⟨627827, by rfl⟩ : syracuseStep 3348413 = 1255655) (by norm_num)
theorem B2232275 : Blo 2231435 2232275 := bstep (se 1 (by rfl) ⟨1674206, by rfl⟩ : syracuseStep 2232275 = 3348413) B3348413
theorem B5022629 : Blo 2231435 5022629 := bbase (se 4 (by rfl) ⟨470871, by rfl⟩ : syracuseStep 5022629 = 941743) (by norm_num)
theorem B3348419 : Blo 2231435 3348419 := bstep (se 1 (by rfl) ⟨2511314, by rfl⟩ : syracuseStep 3348419 = 5022629) B5022629
theorem B2232279 : Blo 2231435 2232279 := bstep (se 1 (by rfl) ⟨1674209, by rfl⟩ : syracuseStep 2232279 = 3348419) B3348419
theorem B5650469 : Blo 2231435 5650469 := bbase (se 4 (by rfl) ⟨529731, by rfl⟩ : syracuseStep 5650469 = 1059463) (by norm_num)
theorem B3766979 : Blo 2231435 3766979 := bstep (se 1 (by rfl) ⟨2825234, by rfl⟩ : syracuseStep 3766979 = 5650469) B5650469
theorem B2511319 : Blo 2231435 2511319 := bstep (se 1 (by rfl) ⟨1883489, by rfl⟩ : syracuseStep 2511319 = 3766979) B3766979
theorem B3348425 : Blo 2231435 3348425 := bstep (se 2 (by rfl) ⟨1255659, by rfl⟩ : syracuseStep 3348425 = 2511319) B2511319
theorem B2232283 : Blo 2231435 2232283 := bstep (se 1 (by rfl) ⟨1674212, by rfl⟩ : syracuseStep 2232283 = 3348425) B3348425
theorem B6356789 : Blo 2231435 6356789 := bbase (se 5 (by rfl) ⟨297974, by rfl⟩ : syracuseStep 6356789 = 595949) (by norm_num)
theorem B4237859 : Blo 2231435 4237859 := bstep (se 1 (by rfl) ⟨3178394, by rfl⟩ : syracuseStep 4237859 = 6356789) B6356789
theorem B11300957 : Blo 2231435 11300957 := bstep (se 3 (by rfl) ⟨2118929, by rfl⟩ : syracuseStep 11300957 = 4237859) B4237859
theorem B7533971 : Blo 2231435 7533971 := bstep (se 1 (by rfl) ⟨5650478, by rfl⟩ : syracuseStep 7533971 = 11300957) B11300957
theorem B5022647 : Blo 2231435 5022647 := bstep (se 1 (by rfl) ⟨3766985, by rfl⟩ : syracuseStep 5022647 = 7533971) B7533971
theorem B3348431 : Blo 2231435 3348431 := bstep (se 1 (by rfl) ⟨2511323, by rfl⟩ : syracuseStep 3348431 = 5022647) B5022647
theorem B2232287 : Blo 2231435 2232287 := bstep (se 1 (by rfl) ⟨1674215, by rfl⟩ : syracuseStep 2232287 = 3348431) B3348431
theorem B3348437 : Blo 2231435 3348437 := bbase (se 7 (by rfl) ⟨39239, by rfl⟩ : syracuseStep 3348437 = 78479) (by norm_num)
theorem B2232291 : Blo 2231435 2232291 := bstep (se 1 (by rfl) ⟨1674218, by rfl⟩ : syracuseStep 2232291 = 3348437) B3348437
theorem B8475749 : Blo 2231435 8475749 := bbase (se 4 (by rfl) ⟨794601, by rfl⟩ : syracuseStep 8475749 = 1589203) (by norm_num)
theorem B5650499 : Blo 2231435 5650499 := bstep (se 1 (by rfl) ⟨4237874, by rfl⟩ : syracuseStep 5650499 = 8475749) B8475749
theorem B3766999 : Blo 2231435 3766999 := bstep (se 1 (by rfl) ⟨2825249, by rfl⟩ : syracuseStep 3766999 = 5650499) B5650499
theorem B5022665 : Blo 2231435 5022665 := bstep (se 2 (by rfl) ⟨1883499, by rfl⟩ : syracuseStep 5022665 = 3766999) B3766999
theorem B3348443 : Blo 2231435 3348443 := bstep (se 1 (by rfl) ⟨2511332, by rfl⟩ : syracuseStep 3348443 = 5022665) B5022665
theorem B2232295 : Blo 2231435 2232295 := bstep (se 1 (by rfl) ⟨1674221, by rfl⟩ : syracuseStep 2232295 = 3348443) B3348443
theorem B2511337 : Blo 2231435 2511337 := bbase (se 2 (by rfl) ⟨941751, by rfl⟩ : syracuseStep 2511337 = 1883503) (by norm_num)
theorem B3348449 : Blo 2231435 3348449 := bstep (se 2 (by rfl) ⟨1255668, by rfl⟩ : syracuseStep 3348449 = 2511337) B2511337
theorem B2232299 : Blo 2231435 2232299 := bstep (se 1 (by rfl) ⟨1674224, by rfl⟩ : syracuseStep 2232299 = 3348449) B3348449
theorem B2383813 : Blo 2231435 2383813 := bbase (se 4 (by rfl) ⟨223482, by rfl⟩ : syracuseStep 2383813 = 446965) (by norm_num)
theorem B12713669 : Blo 2231435 12713669 := bstep (se 4 (by rfl) ⟨1191906, by rfl⟩ : syracuseStep 12713669 = 2383813) B2383813
theorem B8475779 : Blo 2231435 8475779 := bstep (se 1 (by rfl) ⟨6356834, by rfl⟩ : syracuseStep 8475779 = 12713669) B12713669
theorem B5650519 : Blo 2231435 5650519 := bstep (se 1 (by rfl) ⟨4237889, by rfl⟩ : syracuseStep 5650519 = 8475779) B8475779
theorem B7534025 : Blo 2231435 7534025 := bstep (se 2 (by rfl) ⟨2825259, by rfl⟩ : syracuseStep 7534025 = 5650519) B5650519
theorem B5022683 : Blo 2231435 5022683 := bstep (se 1 (by rfl) ⟨3767012, by rfl⟩ : syracuseStep 5022683 = 7534025) B7534025
theorem B3348455 : Blo 2231435 3348455 := bstep (se 1 (by rfl) ⟨2511341, by rfl⟩ : syracuseStep 3348455 = 5022683) B5022683
theorem B2232303 : Blo 2231435 2232303 := bstep (se 1 (by rfl) ⟨1674227, by rfl⟩ : syracuseStep 2232303 = 3348455) B3348455
theorem B3348461 : Blo 2231435 3348461 := bbase (se 3 (by rfl) ⟨627836, by rfl⟩ : syracuseStep 3348461 = 1255673) (by norm_num)
theorem B2232307 : Blo 2231435 2232307 := bstep (se 1 (by rfl) ⟨1674230, by rfl⟩ : syracuseStep 2232307 = 3348461) B3348461
theorem B5022701 : Blo 2231435 5022701 := bbase (se 3 (by rfl) ⟨941756, by rfl⟩ : syracuseStep 5022701 = 1883513) (by norm_num)
theorem B3348467 : Blo 2231435 3348467 := bstep (se 1 (by rfl) ⟨2511350, by rfl⟩ : syracuseStep 3348467 = 5022701) B5022701
theorem B2232311 : Blo 2231435 2232311 := bstep (se 1 (by rfl) ⟨1674233, by rfl⟩ : syracuseStep 2232311 = 3348467) B3348467
theorem B4767653 : Blo 2231435 4767653 := bbase (se 4 (by rfl) ⟨446967, by rfl⟩ : syracuseStep 4767653 = 893935) (by norm_num)
theorem B3178435 : Blo 2231435 3178435 := bstep (se 1 (by rfl) ⟨2383826, by rfl⟩ : syracuseStep 3178435 = 4767653) B4767653
theorem B4237913 : Blo 2231435 4237913 := bstep (se 2 (by rfl) ⟨1589217, by rfl⟩ : syracuseStep 4237913 = 3178435) B3178435
theorem B2825275 : Blo 2231435 2825275 := bstep (se 1 (by rfl) ⟨2118956, by rfl⟩ : syracuseStep 2825275 = 4237913) B4237913
theorem B3767033 : Blo 2231435 3767033 := bstep (se 2 (by rfl) ⟨1412637, by rfl⟩ : syracuseStep 3767033 = 2825275) B2825275
theorem B2511355 : Blo 2231435 2511355 := bstep (se 1 (by rfl) ⟨1883516, by rfl⟩ : syracuseStep 2511355 = 3767033) B3767033
theorem B3348473 : Blo 2231435 3348473 := bstep (se 2 (by rfl) ⟨1255677, by rfl⟩ : syracuseStep 3348473 = 2511355) B2511355
theorem B2232315 : Blo 2231435 2232315 := bstep (se 1 (by rfl) ⟨1674236, by rfl⟩ : syracuseStep 2232315 = 3348473) B3348473
theorem B5727653 : Blo 2231435 5727653 := bbase (se 4 (by rfl) ⟨536967, by rfl⟩ : syracuseStep 5727653 = 1073935) (by norm_num)
theorem B3818435 : Blo 2231435 3818435 := bstep (se 1 (by rfl) ⟨2863826, by rfl⟩ : syracuseStep 3818435 = 5727653) B5727653
theorem B10182493 : Blo 2231435 10182493 := bstep (se 3 (by rfl) ⟨1909217, by rfl⟩ : syracuseStep 10182493 = 3818435) B3818435
theorem B13576657 : Blo 2231435 13576657 := bstep (se 2 (by rfl) ⟨5091246, by rfl⟩ : syracuseStep 13576657 = 10182493) B10182493
theorem B18102209 : Blo 2231435 18102209 := bstep (se 2 (by rfl) ⟨6788328, by rfl⟩ : syracuseStep 18102209 = 13576657) B13576657
theorem B193090229 : Blo 2231435 193090229 := bstep (se 5 (by rfl) ⟨9051104, by rfl⟩ : syracuseStep 193090229 = 18102209) B18102209
theorem B128726819 : Blo 2231435 128726819 := bstep (se 1 (by rfl) ⟨96545114, by rfl⟩ : syracuseStep 128726819 = 193090229) B193090229
theorem B85817879 : Blo 2231435 85817879 := bstep (se 1 (by rfl) ⟨64363409, by rfl⟩ : syracuseStep 85817879 = 128726819) B128726819
theorem B57211919 : Blo 2231435 57211919 := bstep (se 1 (by rfl) ⟨42908939, by rfl⟩ : syracuseStep 57211919 = 85817879) B85817879
theorem B38141279 : Blo 2231435 38141279 := bstep (se 1 (by rfl) ⟨28605959, by rfl⟩ : syracuseStep 38141279 = 57211919) B57211919
theorem B25427519 : Blo 2231435 25427519 := bstep (se 1 (by rfl) ⟨19070639, by rfl⟩ : syracuseStep 25427519 = 38141279) B38141279
theorem B16951679 : Blo 2231435 16951679 := bstep (se 1 (by rfl) ⟨12713759, by rfl⟩ : syracuseStep 16951679 = 25427519) B25427519
theorem B11301119 : Blo 2231435 11301119 := bstep (se 1 (by rfl) ⟨8475839, by rfl⟩ : syracuseStep 11301119 = 16951679) B16951679
theorem B7534079 : Blo 2231435 7534079 := bstep (se 1 (by rfl) ⟨5650559, by rfl⟩ : syracuseStep 7534079 = 11301119) B11301119
theorem B5022719 : Blo 2231435 5022719 := bstep (se 1 (by rfl) ⟨3767039, by rfl⟩ : syracuseStep 5022719 = 7534079) B7534079
theorem B3348479 : Blo 2231435 3348479 := bstep (se 1 (by rfl) ⟨2511359, by rfl⟩ : syracuseStep 3348479 = 5022719) B5022719
theorem B2232319 : Blo 2231435 2232319 := bstep (se 1 (by rfl) ⟨1674239, by rfl⟩ : syracuseStep 2232319 = 3348479) B3348479
theorem B3348485 : Blo 2231435 3348485 := bbase (se 4 (by rfl) ⟨313920, by rfl⟩ : syracuseStep 3348485 = 627841) (by norm_num)
theorem B2232323 : Blo 2231435 2232323 := bstep (se 1 (by rfl) ⟨1674242, by rfl⟩ : syracuseStep 2232323 = 3348485) B3348485
theorem B3767053 : Blo 2231435 3767053 := bbase (se 3 (by rfl) ⟨706322, by rfl⟩ : syracuseStep 3767053 = 1412645) (by norm_num)
theorem B5022737 : Blo 2231435 5022737 := bstep (se 2 (by rfl) ⟨1883526, by rfl⟩ : syracuseStep 5022737 = 3767053) B3767053
theorem B3348491 : Blo 2231435 3348491 := bstep (se 1 (by rfl) ⟨2511368, by rfl⟩ : syracuseStep 3348491 = 5022737) B5022737
theorem B2232327 : Blo 2231435 2232327 := bstep (se 1 (by rfl) ⟨1674245, by rfl⟩ : syracuseStep 2232327 = 3348491) B3348491
theorem B2511373 : Blo 2231435 2511373 := bbase (se 3 (by rfl) ⟨470882, by rfl⟩ : syracuseStep 2511373 = 941765) (by norm_num)
theorem B3348497 : Blo 2231435 3348497 := bstep (se 2 (by rfl) ⟨1255686, by rfl⟩ : syracuseStep 3348497 = 2511373) B2511373
theorem B2232331 : Blo 2231435 2232331 := bstep (se 1 (by rfl) ⟨1674248, by rfl⟩ : syracuseStep 2232331 = 3348497) B3348497
theorem B7534133 : Blo 2231435 7534133 := bbase (se 5 (by rfl) ⟨353162, by rfl⟩ : syracuseStep 7534133 = 706325) (by norm_num)
theorem B5022755 : Blo 2231435 5022755 := bstep (se 1 (by rfl) ⟨3767066, by rfl⟩ : syracuseStep 5022755 = 7534133) B7534133
theorem B3348503 : Blo 2231435 3348503 := bstep (se 1 (by rfl) ⟨2511377, by rfl⟩ : syracuseStep 3348503 = 5022755) B5022755
theorem B2232335 : Blo 2231435 2232335 := bstep (se 1 (by rfl) ⟨1674251, by rfl⟩ : syracuseStep 2232335 = 3348503) B3348503
theorem B3348509 : Blo 2231435 3348509 := bbase (se 3 (by rfl) ⟨627845, by rfl⟩ : syracuseStep 3348509 = 1255691) (by norm_num)
theorem B2232339 : Blo 2231435 2232339 := bstep (se 1 (by rfl) ⟨1674254, by rfl⟩ : syracuseStep 2232339 = 3348509) B3348509
theorem B5022773 : Blo 2231435 5022773 := bbase (se 5 (by rfl) ⟨235442, by rfl⟩ : syracuseStep 5022773 = 470885) (by norm_num)
theorem B3348515 : Blo 2231435 3348515 := bstep (se 1 (by rfl) ⟨2511386, by rfl⟩ : syracuseStep 3348515 = 5022773) B5022773
theorem B2232343 : Blo 2231435 2232343 := bstep (se 1 (by rfl) ⟨1674257, by rfl⟩ : syracuseStep 2232343 = 3348515) B3348515
theorem B4022765 : Blo 2231435 4022765 := bbase (se 3 (by rfl) ⟨754268, by rfl⟩ : syracuseStep 4022765 = 1508537) (by norm_num)
theorem B2681843 : Blo 2231435 2681843 := bstep (se 1 (by rfl) ⟨2011382, by rfl⟩ : syracuseStep 2681843 = 4022765) B4022765
theorem B7151581 : Blo 2231435 7151581 := bstep (se 3 (by rfl) ⟨1340921, by rfl⟩ : syracuseStep 7151581 = 2681843) B2681843
theorem B9535441 : Blo 2231435 9535441 := bstep (se 2 (by rfl) ⟨3575790, by rfl⟩ : syracuseStep 9535441 = 7151581) B7151581
theorem B12713921 : Blo 2231435 12713921 := bstep (se 2 (by rfl) ⟨4767720, by rfl⟩ : syracuseStep 12713921 = 9535441) B9535441
theorem B8475947 : Blo 2231435 8475947 := bstep (se 1 (by rfl) ⟨6356960, by rfl⟩ : syracuseStep 8475947 = 12713921) B12713921
theorem B5650631 : Blo 2231435 5650631 := bstep (se 1 (by rfl) ⟨4237973, by rfl⟩ : syracuseStep 5650631 = 8475947) B8475947
theorem B3767087 : Blo 2231435 3767087 := bstep (se 1 (by rfl) ⟨2825315, by rfl⟩ : syracuseStep 3767087 = 5650631) B5650631
theorem B2511391 : Blo 2231435 2511391 := bstep (se 1 (by rfl) ⟨1883543, by rfl⟩ : syracuseStep 2511391 = 3767087) B3767087
theorem B3348521 : Blo 2231435 3348521 := bstep (se 2 (by rfl) ⟨1255695, by rfl⟩ : syracuseStep 3348521 = 2511391) B2511391
theorem B2232347 : Blo 2231435 2232347 := bstep (se 1 (by rfl) ⟨1674260, by rfl⟩ : syracuseStep 2232347 = 3348521) B3348521
theorem B30547925 : Blo 2231435 30547925 := bbase (se 7 (by rfl) ⟨357983, by rfl⟩ : syracuseStep 30547925 = 715967) (by norm_num)
theorem B20365283 : Blo 2231435 20365283 := bstep (se 1 (by rfl) ⟨15273962, by rfl⟩ : syracuseStep 20365283 = 30547925) B30547925
theorem B13576855 : Blo 2231435 13576855 := bstep (se 1 (by rfl) ⟨10182641, by rfl⟩ : syracuseStep 13576855 = 20365283) B20365283
theorem B18102473 : Blo 2231435 18102473 := bstep (se 2 (by rfl) ⟨6788427, by rfl⟩ : syracuseStep 18102473 = 13576855) B13576855
theorem B12068315 : Blo 2231435 12068315 := bstep (se 1 (by rfl) ⟨9051236, by rfl⟩ : syracuseStep 12068315 = 18102473) B18102473
theorem B8045543 : Blo 2231435 8045543 := bstep (se 1 (by rfl) ⟨6034157, by rfl⟩ : syracuseStep 8045543 = 12068315) B12068315
theorem B5363695 : Blo 2231435 5363695 := bstep (se 1 (by rfl) ⟨4022771, by rfl⟩ : syracuseStep 5363695 = 8045543) B8045543
theorem B7151593 : Blo 2231435 7151593 := bstep (se 2 (by rfl) ⟨2681847, by rfl⟩ : syracuseStep 7151593 = 5363695) B5363695
theorem B9535457 : Blo 2231435 9535457 := bstep (se 2 (by rfl) ⟨3575796, by rfl⟩ : syracuseStep 9535457 = 7151593) B7151593
theorem B6356971 : Blo 2231435 6356971 := bstep (se 1 (by rfl) ⟨4767728, by rfl⟩ : syracuseStep 6356971 = 9535457) B9535457
theorem B8475961 : Blo 2231435 8475961 := bstep (se 2 (by rfl) ⟨3178485, by rfl⟩ : syracuseStep 8475961 = 6356971) B6356971
theorem B11301281 : Blo 2231435 11301281 := bstep (se 2 (by rfl) ⟨4237980, by rfl⟩ : syracuseStep 11301281 = 8475961) B8475961
theorem B7534187 : Blo 2231435 7534187 := bstep (se 1 (by rfl) ⟨5650640, by rfl⟩ : syracuseStep 7534187 = 11301281) B11301281
theorem B5022791 : Blo 2231435 5022791 := bstep (se 1 (by rfl) ⟨3767093, by rfl⟩ : syracuseStep 5022791 = 7534187) B7534187
theorem B3348527 : Blo 2231435 3348527 := bstep (se 1 (by rfl) ⟨2511395, by rfl⟩ : syracuseStep 3348527 = 5022791) B5022791
theorem B2232351 : Blo 2231435 2232351 := bstep (se 1 (by rfl) ⟨1674263, by rfl⟩ : syracuseStep 2232351 = 3348527) B3348527
theorem B3348533 : Blo 2231435 3348533 := bbase (se 5 (by rfl) ⟨156962, by rfl⟩ : syracuseStep 3348533 = 313925) (by norm_num)
theorem B2232355 : Blo 2231435 2232355 := bstep (se 1 (by rfl) ⟨1674266, by rfl⟩ : syracuseStep 2232355 = 3348533) B3348533
theorem B5650661 : Blo 2231435 5650661 := bbase (se 4 (by rfl) ⟨529749, by rfl⟩ : syracuseStep 5650661 = 1059499) (by norm_num)
theorem B3767107 : Blo 2231435 3767107 := bstep (se 1 (by rfl) ⟨2825330, by rfl⟩ : syracuseStep 3767107 = 5650661) B5650661
theorem B5022809 : Blo 2231435 5022809 := bstep (se 2 (by rfl) ⟨1883553, by rfl⟩ : syracuseStep 5022809 = 3767107) B3767107
theorem B3348539 : Blo 2231435 3348539 := bstep (se 1 (by rfl) ⟨2511404, by rfl⟩ : syracuseStep 3348539 = 5022809) B5022809
theorem B2232359 : Blo 2231435 2232359 := bstep (se 1 (by rfl) ⟨1674269, by rfl⟩ : syracuseStep 2232359 = 3348539) B3348539
theorem B2511409 : Blo 2231435 2511409 := bbase (se 2 (by rfl) ⟨941778, by rfl⟩ : syracuseStep 2511409 = 1883557) (by norm_num)
theorem B3348545 : Blo 2231435 3348545 := bstep (se 2 (by rfl) ⟨1255704, by rfl⟩ : syracuseStep 3348545 = 2511409) B2511409
theorem B2232363 : Blo 2231435 2232363 := bstep (se 1 (by rfl) ⟨1674272, by rfl⟩ : syracuseStep 2232363 = 3348545) B3348545
theorem B3017101 : Blo 2231435 3017101 := bbase (se 3 (by rfl) ⟨565706, by rfl⟩ : syracuseStep 3017101 = 1131413) (by norm_num)
theorem B4022801 : Blo 2231435 4022801 := bstep (se 2 (by rfl) ⟨1508550, by rfl⟩ : syracuseStep 4022801 = 3017101) B3017101
theorem B2681867 : Blo 2231435 2681867 := bstep (se 1 (by rfl) ⟨2011400, by rfl⟩ : syracuseStep 2681867 = 4022801) B4022801
theorem B7151645 : Blo 2231435 7151645 := bstep (se 3 (by rfl) ⟨1340933, by rfl⟩ : syracuseStep 7151645 = 2681867) B2681867
theorem B4767763 : Blo 2231435 4767763 := bstep (se 1 (by rfl) ⟨3575822, by rfl⟩ : syracuseStep 4767763 = 7151645) B7151645
theorem B6357017 : Blo 2231435 6357017 := bstep (se 2 (by rfl) ⟨2383881, by rfl⟩ : syracuseStep 6357017 = 4767763) B4767763
theorem B4238011 : Blo 2231435 4238011 := bstep (se 1 (by rfl) ⟨3178508, by rfl⟩ : syracuseStep 4238011 = 6357017) B6357017
theorem B5650681 : Blo 2231435 5650681 := bstep (se 2 (by rfl) ⟨2119005, by rfl⟩ : syracuseStep 5650681 = 4238011) B4238011
theorem B7534241 : Blo 2231435 7534241 := bstep (se 2 (by rfl) ⟨2825340, by rfl⟩ : syracuseStep 7534241 = 5650681) B5650681
theorem B5022827 : Blo 2231435 5022827 := bstep (se 1 (by rfl) ⟨3767120, by rfl⟩ : syracuseStep 5022827 = 7534241) B7534241
theorem B3348551 : Blo 2231435 3348551 := bstep (se 1 (by rfl) ⟨2511413, by rfl⟩ : syracuseStep 3348551 = 5022827) B5022827
theorem B2232367 : Blo 2231435 2232367 := bstep (se 1 (by rfl) ⟨1674275, by rfl⟩ : syracuseStep 2232367 = 3348551) B3348551
theorem B3348557 : Blo 2231435 3348557 := bbase (se 3 (by rfl) ⟨627854, by rfl⟩ : syracuseStep 3348557 = 1255709) (by norm_num)
theorem B2232371 : Blo 2231435 2232371 := bstep (se 1 (by rfl) ⟨1674278, by rfl⟩ : syracuseStep 2232371 = 3348557) B3348557
theorem B5022845 : Blo 2231435 5022845 := bbase (se 3 (by rfl) ⟨941783, by rfl⟩ : syracuseStep 5022845 = 1883567) (by norm_num)
theorem B3348563 : Blo 2231435 3348563 := bstep (se 1 (by rfl) ⟨2511422, by rfl⟩ : syracuseStep 3348563 = 5022845) B5022845
theorem B2232375 : Blo 2231435 2232375 := bstep (se 1 (by rfl) ⟨1674281, by rfl⟩ : syracuseStep 2232375 = 3348563) B3348563
theorem B3767141 : Blo 2231435 3767141 := bbase (se 4 (by rfl) ⟨353169, by rfl⟩ : syracuseStep 3767141 = 706339) (by norm_num)
theorem B2511427 : Blo 2231435 2511427 := bstep (se 1 (by rfl) ⟨1883570, by rfl⟩ : syracuseStep 2511427 = 3767141) B3767141
theorem B3348569 : Blo 2231435 3348569 := bstep (se 2 (by rfl) ⟨1255713, by rfl⟩ : syracuseStep 3348569 = 2511427) B2511427
theorem B2232379 : Blo 2231435 2232379 := bstep (se 1 (by rfl) ⟨1674284, by rfl⟩ : syracuseStep 2232379 = 3348569) B3348569
theorem B4767797 : Blo 2231435 4767797 := bbase (se 5 (by rfl) ⟨223490, by rfl⟩ : syracuseStep 4767797 = 446981) (by norm_num)
theorem B3178531 : Blo 2231435 3178531 := bstep (se 1 (by rfl) ⟨2383898, by rfl⟩ : syracuseStep 3178531 = 4767797) B4767797
theorem B16952165 : Blo 2231435 16952165 := bstep (se 4 (by rfl) ⟨1589265, by rfl⟩ : syracuseStep 16952165 = 3178531) B3178531
theorem B11301443 : Blo 2231435 11301443 := bstep (se 1 (by rfl) ⟨8476082, by rfl⟩ : syracuseStep 11301443 = 16952165) B16952165
theorem B7534295 : Blo 2231435 7534295 := bstep (se 1 (by rfl) ⟨5650721, by rfl⟩ : syracuseStep 7534295 = 11301443) B11301443
theorem B5022863 : Blo 2231435 5022863 := bstep (se 1 (by rfl) ⟨3767147, by rfl⟩ : syracuseStep 5022863 = 7534295) B7534295
theorem B3348575 : Blo 2231435 3348575 := bstep (se 1 (by rfl) ⟨2511431, by rfl⟩ : syracuseStep 3348575 = 5022863) B5022863
theorem B2232383 : Blo 2231435 2232383 := bstep (se 1 (by rfl) ⟨1674287, by rfl⟩ : syracuseStep 2232383 = 3348575) B3348575
theorem B3348581 : Blo 2231435 3348581 := bbase (se 4 (by rfl) ⟨313929, by rfl⟩ : syracuseStep 3348581 = 627859) (by norm_num)
theorem B2232387 : Blo 2231435 2232387 := bstep (se 1 (by rfl) ⟨1674290, by rfl⟩ : syracuseStep 2232387 = 3348581) B3348581
theorem B2416433 : Blo 2231435 2416433 := bbase (se 2 (by rfl) ⟨906162, by rfl⟩ : syracuseStep 2416433 = 1812325) (by norm_num)
theorem B6443821 : Blo 2231435 6443821 := bstep (se 3 (by rfl) ⟨1208216, by rfl⟩ : syracuseStep 6443821 = 2416433) B2416433
theorem B8591761 : Blo 2231435 8591761 := bstep (se 2 (by rfl) ⟨3221910, by rfl⟩ : syracuseStep 8591761 = 6443821) B6443821
theorem B11455681 : Blo 2231435 11455681 := bstep (se 2 (by rfl) ⟨4295880, by rfl⟩ : syracuseStep 11455681 = 8591761) B8591761
theorem B15274241 : Blo 2231435 15274241 := bstep (se 2 (by rfl) ⟨5727840, by rfl⟩ : syracuseStep 15274241 = 11455681) B11455681
theorem B10182827 : Blo 2231435 10182827 := bstep (se 1 (by rfl) ⟨7637120, by rfl⟩ : syracuseStep 10182827 = 15274241) B15274241
theorem B6788551 : Blo 2231435 6788551 := bstep (se 1 (by rfl) ⟨5091413, by rfl⟩ : syracuseStep 6788551 = 10182827) B10182827
theorem B9051401 : Blo 2231435 9051401 := bstep (se 2 (by rfl) ⟨3394275, by rfl⟩ : syracuseStep 9051401 = 6788551) B6788551
theorem B6034267 : Blo 2231435 6034267 := bstep (se 1 (by rfl) ⟨4525700, by rfl⟩ : syracuseStep 6034267 = 9051401) B9051401
theorem B8045689 : Blo 2231435 8045689 := bstep (se 2 (by rfl) ⟨3017133, by rfl⟩ : syracuseStep 8045689 = 6034267) B6034267
theorem B10727585 : Blo 2231435 10727585 := bstep (se 2 (by rfl) ⟨4022844, by rfl⟩ : syracuseStep 10727585 = 8045689) B8045689
theorem B7151723 : Blo 2231435 7151723 := bstep (se 1 (by rfl) ⟨5363792, by rfl⟩ : syracuseStep 7151723 = 10727585) B10727585
theorem B4767815 : Blo 2231435 4767815 := bstep (se 1 (by rfl) ⟨3575861, by rfl⟩ : syracuseStep 4767815 = 7151723) B7151723
theorem B3178543 : Blo 2231435 3178543 := bstep (se 1 (by rfl) ⟨2383907, by rfl⟩ : syracuseStep 3178543 = 4767815) B4767815
theorem B4238057 : Blo 2231435 4238057 := bstep (se 2 (by rfl) ⟨1589271, by rfl⟩ : syracuseStep 4238057 = 3178543) B3178543
theorem B2825371 : Blo 2231435 2825371 := bstep (se 1 (by rfl) ⟨2119028, by rfl⟩ : syracuseStep 2825371 = 4238057) B4238057
theorem B3767161 : Blo 2231435 3767161 := bstep (se 2 (by rfl) ⟨1412685, by rfl⟩ : syracuseStep 3767161 = 2825371) B2825371
theorem B5022881 : Blo 2231435 5022881 := bstep (se 2 (by rfl) ⟨1883580, by rfl⟩ : syracuseStep 5022881 = 3767161) B3767161
theorem B3348587 : Blo 2231435 3348587 := bstep (se 1 (by rfl) ⟨2511440, by rfl⟩ : syracuseStep 3348587 = 5022881) B5022881
theorem B2232391 : Blo 2231435 2232391 := bstep (se 1 (by rfl) ⟨1674293, by rfl⟩ : syracuseStep 2232391 = 3348587) B3348587
theorem B2511445 : Blo 2231435 2511445 := bbase (se 8 (by rfl) ⟨14715, by rfl⟩ : syracuseStep 2511445 = 29431) (by norm_num)
theorem B3348593 : Blo 2231435 3348593 := bstep (se 2 (by rfl) ⟨1255722, by rfl⟩ : syracuseStep 3348593 = 2511445) B2511445
theorem B2232395 : Blo 2231435 2232395 := bstep (se 1 (by rfl) ⟨1674296, by rfl⟩ : syracuseStep 2232395 = 3348593) B3348593
theorem B2825381 : Blo 2231435 2825381 := bbase (se 4 (by rfl) ⟨264879, by rfl⟩ : syracuseStep 2825381 = 529759) (by norm_num)
theorem B7534349 : Blo 2231435 7534349 := bstep (se 3 (by rfl) ⟨1412690, by rfl⟩ : syracuseStep 7534349 = 2825381) B2825381
theorem B5022899 : Blo 2231435 5022899 := bstep (se 1 (by rfl) ⟨3767174, by rfl⟩ : syracuseStep 5022899 = 7534349) B7534349
theorem B3348599 : Blo 2231435 3348599 := bstep (se 1 (by rfl) ⟨2511449, by rfl⟩ : syracuseStep 3348599 = 5022899) B5022899
theorem B2232399 : Blo 2231435 2232399 := bstep (se 1 (by rfl) ⟨1674299, by rfl⟩ : syracuseStep 2232399 = 3348599) B3348599
theorem B3348605 : Blo 2231435 3348605 := bbase (se 3 (by rfl) ⟨627863, by rfl⟩ : syracuseStep 3348605 = 1255727) (by norm_num)
theorem B2232403 : Blo 2231435 2232403 := bstep (se 1 (by rfl) ⟨1674302, by rfl⟩ : syracuseStep 2232403 = 3348605) B3348605
theorem B5022917 : Blo 2231435 5022917 := bbase (se 4 (by rfl) ⟨470898, by rfl⟩ : syracuseStep 5022917 = 941797) (by norm_num)
theorem B3348611 : Blo 2231435 3348611 := bstep (se 1 (by rfl) ⟨2511458, by rfl⟩ : syracuseStep 3348611 = 5022917) B5022917
theorem B2232407 : Blo 2231435 2232407 := bstep (se 1 (by rfl) ⟨1674305, by rfl⟩ : syracuseStep 2232407 = 3348611) B3348611
theorem B14303573 : Blo 2231435 14303573 := bbase (se 10 (by rfl) ⟨20952, by rfl⟩ : syracuseStep 14303573 = 41905) (by norm_num)
theorem B9535715 : Blo 2231435 9535715 := bstep (se 1 (by rfl) ⟨7151786, by rfl⟩ : syracuseStep 9535715 = 14303573) B14303573
theorem B6357143 : Blo 2231435 6357143 := bstep (se 1 (by rfl) ⟨4767857, by rfl⟩ : syracuseStep 6357143 = 9535715) B9535715
theorem B4238095 : Blo 2231435 4238095 := bstep (se 1 (by rfl) ⟨3178571, by rfl⟩ : syracuseStep 4238095 = 6357143) B6357143
theorem B5650793 : Blo 2231435 5650793 := bstep (se 2 (by rfl) ⟨2119047, by rfl⟩ : syracuseStep 5650793 = 4238095) B4238095
theorem B3767195 : Blo 2231435 3767195 := bstep (se 1 (by rfl) ⟨2825396, by rfl⟩ : syracuseStep 3767195 = 5650793) B5650793
theorem B2511463 : Blo 2231435 2511463 := bstep (se 1 (by rfl) ⟨1883597, by rfl⟩ : syracuseStep 2511463 = 3767195) B3767195
theorem B3348617 : Blo 2231435 3348617 := bstep (se 2 (by rfl) ⟨1255731, by rfl⟩ : syracuseStep 3348617 = 2511463) B2511463
theorem B2232411 : Blo 2231435 2232411 := bstep (se 1 (by rfl) ⟨1674308, by rfl⟩ : syracuseStep 2232411 = 3348617) B3348617
theorem B11301605 : Blo 2231435 11301605 := bbase (se 4 (by rfl) ⟨1059525, by rfl⟩ : syracuseStep 11301605 = 2119051) (by norm_num)
theorem B7534403 : Blo 2231435 7534403 := bstep (se 1 (by rfl) ⟨5650802, by rfl⟩ : syracuseStep 7534403 = 11301605) B11301605
theorem B5022935 : Blo 2231435 5022935 := bstep (se 1 (by rfl) ⟨3767201, by rfl⟩ : syracuseStep 5022935 = 7534403) B7534403
theorem B3348623 : Blo 2231435 3348623 := bstep (se 1 (by rfl) ⟨2511467, by rfl⟩ : syracuseStep 3348623 = 5022935) B5022935
theorem B2232415 : Blo 2231435 2232415 := bstep (se 1 (by rfl) ⟨1674311, by rfl⟩ : syracuseStep 2232415 = 3348623) B3348623
theorem B3348629 : Blo 2231435 3348629 := bbase (se 6 (by rfl) ⟨78483, by rfl⟩ : syracuseStep 3348629 = 156967) (by norm_num)
theorem B2232419 : Blo 2231435 2232419 := bstep (se 1 (by rfl) ⟨1674314, by rfl⟩ : syracuseStep 2232419 = 3348629) B3348629
theorem B9535765 : Blo 2231435 9535765 := bbase (se 6 (by rfl) ⟨223494, by rfl⟩ : syracuseStep 9535765 = 446989) (by norm_num)
theorem B12714353 : Blo 2231435 12714353 := bstep (se 2 (by rfl) ⟨4767882, by rfl⟩ : syracuseStep 12714353 = 9535765) B9535765
theorem B8476235 : Blo 2231435 8476235 := bstep (se 1 (by rfl) ⟨6357176, by rfl⟩ : syracuseStep 8476235 = 12714353) B12714353
theorem B5650823 : Blo 2231435 5650823 := bstep (se 1 (by rfl) ⟨4238117, by rfl⟩ : syracuseStep 5650823 = 8476235) B8476235
theorem B3767215 : Blo 2231435 3767215 := bstep (se 1 (by rfl) ⟨2825411, by rfl⟩ : syracuseStep 3767215 = 5650823) B5650823
theorem B5022953 : Blo 2231435 5022953 := bstep (se 2 (by rfl) ⟨1883607, by rfl⟩ : syracuseStep 5022953 = 3767215) B3767215
theorem B3348635 : Blo 2231435 3348635 := bstep (se 1 (by rfl) ⟨2511476, by rfl⟩ : syracuseStep 3348635 = 5022953) B5022953
theorem B2232423 : Blo 2231435 2232423 := bstep (se 1 (by rfl) ⟨1674317, by rfl⟩ : syracuseStep 2232423 = 3348635) B3348635
theorem B2511481 : Blo 2231435 2511481 := bbase (se 2 (by rfl) ⟨941805, by rfl⟩ : syracuseStep 2511481 = 1883611) (by norm_num)
theorem B3348641 : Blo 2231435 3348641 := bstep (se 2 (by rfl) ⟨1255740, by rfl⟩ : syracuseStep 3348641 = 2511481) B2511481
theorem B2232427 : Blo 2231435 2232427 := bstep (se 1 (by rfl) ⟨1674320, by rfl⟩ : syracuseStep 2232427 = 3348641) B3348641
theorem B5806093 : Blo 2231435 5806093 := bbase (se 3 (by rfl) ⟨1088642, by rfl⟩ : syracuseStep 5806093 = 2177285) (by norm_num)
theorem B7741457 : Blo 2231435 7741457 := bstep (se 2 (by rfl) ⟨2903046, by rfl⟩ : syracuseStep 7741457 = 5806093) B5806093
theorem B5160971 : Blo 2231435 5160971 := bstep (se 1 (by rfl) ⟨3870728, by rfl⟩ : syracuseStep 5160971 = 7741457) B7741457
theorem B3440647 : Blo 2231435 3440647 := bstep (se 1 (by rfl) ⟨2580485, by rfl⟩ : syracuseStep 3440647 = 5160971) B5160971
theorem B4587529 : Blo 2231435 4587529 := bstep (se 2 (by rfl) ⟨1720323, by rfl⟩ : syracuseStep 4587529 = 3440647) B3440647
theorem B6116705 : Blo 2231435 6116705 := bstep (se 2 (by rfl) ⟨2293764, by rfl⟩ : syracuseStep 6116705 = 4587529) B4587529
theorem B4077803 : Blo 2231435 4077803 := bstep (se 1 (by rfl) ⟨3058352, by rfl⟩ : syracuseStep 4077803 = 6116705) B6116705
theorem B10874141 : Blo 2231435 10874141 := bstep (se 3 (by rfl) ⟨2038901, by rfl⟩ : syracuseStep 10874141 = 4077803) B4077803
theorem B7249427 : Blo 2231435 7249427 := bstep (se 1 (by rfl) ⟨5437070, by rfl⟩ : syracuseStep 7249427 = 10874141) B10874141
theorem B4832951 : Blo 2231435 4832951 := bstep (se 1 (by rfl) ⟨3624713, by rfl⟩ : syracuseStep 4832951 = 7249427) B7249427
theorem B12887869 : Blo 2231435 12887869 := bstep (se 3 (by rfl) ⟨2416475, by rfl⟩ : syracuseStep 12887869 = 4832951) B4832951
theorem B17183825 : Blo 2231435 17183825 := bstep (se 2 (by rfl) ⟨6443934, by rfl⟩ : syracuseStep 17183825 = 12887869) B12887869
theorem B11455883 : Blo 2231435 11455883 := bstep (se 1 (by rfl) ⟨8591912, by rfl⟩ : syracuseStep 11455883 = 17183825) B17183825
theorem B7637255 : Blo 2231435 7637255 := bstep (se 1 (by rfl) ⟨5727941, by rfl⟩ : syracuseStep 7637255 = 11455883) B11455883
theorem B5091503 : Blo 2231435 5091503 := bstep (se 1 (by rfl) ⟨3818627, by rfl⟩ : syracuseStep 5091503 = 7637255) B7637255
theorem B13577341 : Blo 2231435 13577341 := bstep (se 3 (by rfl) ⟨2545751, by rfl⟩ : syracuseStep 13577341 = 5091503) B5091503
theorem B18103121 : Blo 2231435 18103121 := bstep (se 2 (by rfl) ⟨6788670, by rfl⟩ : syracuseStep 18103121 = 13577341) B13577341
theorem B12068747 : Blo 2231435 12068747 := bstep (se 1 (by rfl) ⟨9051560, by rfl⟩ : syracuseStep 12068747 = 18103121) B18103121
theorem B8045831 : Blo 2231435 8045831 := bstep (se 1 (by rfl) ⟨6034373, by rfl⟩ : syracuseStep 8045831 = 12068747) B12068747
theorem B21455549 : Blo 2231435 21455549 := bstep (se 3 (by rfl) ⟨4022915, by rfl⟩ : syracuseStep 21455549 = 8045831) B8045831
theorem B14303699 : Blo 2231435 14303699 := bstep (se 1 (by rfl) ⟨10727774, by rfl⟩ : syracuseStep 14303699 = 21455549) B21455549
theorem B9535799 : Blo 2231435 9535799 := bstep (se 1 (by rfl) ⟨7151849, by rfl⟩ : syracuseStep 9535799 = 14303699) B14303699
theorem B6357199 : Blo 2231435 6357199 := bstep (se 1 (by rfl) ⟨4767899, by rfl⟩ : syracuseStep 6357199 = 9535799) B9535799
theorem B8476265 : Blo 2231435 8476265 := bstep (se 2 (by rfl) ⟨3178599, by rfl⟩ : syracuseStep 8476265 = 6357199) B6357199
theorem B5650843 : Blo 2231435 5650843 := bstep (se 1 (by rfl) ⟨4238132, by rfl⟩ : syracuseStep 5650843 = 8476265) B8476265
theorem B7534457 : Blo 2231435 7534457 := bstep (se 2 (by rfl) ⟨2825421, by rfl⟩ : syracuseStep 7534457 = 5650843) B5650843
theorem B5022971 : Blo 2231435 5022971 := bstep (se 1 (by rfl) ⟨3767228, by rfl⟩ : syracuseStep 5022971 = 7534457) B7534457
theorem B3348647 : Blo 2231435 3348647 := bstep (se 1 (by rfl) ⟨2511485, by rfl⟩ : syracuseStep 3348647 = 5022971) B5022971
theorem B2232431 : Blo 2231435 2232431 := bstep (se 1 (by rfl) ⟨1674323, by rfl⟩ : syracuseStep 2232431 = 3348647) B3348647
theorem B3348653 : Blo 2231435 3348653 := bbase (se 3 (by rfl) ⟨627872, by rfl⟩ : syracuseStep 3348653 = 1255745) (by norm_num)
theorem B2232435 : Blo 2231435 2232435 := bstep (se 1 (by rfl) ⟨1674326, by rfl⟩ : syracuseStep 2232435 = 3348653) B3348653
theorem B5022989 : Blo 2231435 5022989 := bbase (se 3 (by rfl) ⟨941810, by rfl⟩ : syracuseStep 5022989 = 1883621) (by norm_num)
theorem B3348659 : Blo 2231435 3348659 := bstep (se 1 (by rfl) ⟨2511494, by rfl⟩ : syracuseStep 3348659 = 5022989) B5022989
theorem B2232439 : Blo 2231435 2232439 := bstep (se 1 (by rfl) ⟨1674329, by rfl⟩ : syracuseStep 2232439 = 3348659) B3348659
theorem B2825437 : Blo 2231435 2825437 := bbase (se 3 (by rfl) ⟨529769, by rfl⟩ : syracuseStep 2825437 = 1059539) (by norm_num)
theorem B3767249 : Blo 2231435 3767249 := bstep (se 2 (by rfl) ⟨1412718, by rfl⟩ : syracuseStep 3767249 = 2825437) B2825437
theorem B2511499 : Blo 2231435 2511499 := bstep (se 1 (by rfl) ⟨1883624, by rfl⟩ : syracuseStep 2511499 = 3767249) B3767249
theorem B3348665 : Blo 2231435 3348665 := bstep (se 2 (by rfl) ⟨1255749, by rfl⟩ : syracuseStep 3348665 = 2511499) B2511499
theorem B2232443 : Blo 2231435 2232443 := bstep (se 1 (by rfl) ⟨1674332, by rfl⟩ : syracuseStep 2232443 = 3348665) B3348665
theorem B19071733 : Blo 2231435 19071733 := bbase (se 5 (by rfl) ⟨893987, by rfl⟩ : syracuseStep 19071733 = 1787975) (by norm_num)
theorem B25428977 : Blo 2231435 25428977 := bstep (se 2 (by rfl) ⟨9535866, by rfl⟩ : syracuseStep 25428977 = 19071733) B19071733
theorem B16952651 : Blo 2231435 16952651 := bstep (se 1 (by rfl) ⟨12714488, by rfl⟩ : syracuseStep 16952651 = 25428977) B25428977
theorem B11301767 : Blo 2231435 11301767 := bstep (se 1 (by rfl) ⟨8476325, by rfl⟩ : syracuseStep 11301767 = 16952651) B16952651
theorem B7534511 : Blo 2231435 7534511 := bstep (se 1 (by rfl) ⟨5650883, by rfl⟩ : syracuseStep 7534511 = 11301767) B11301767
theorem B5023007 : Blo 2231435 5023007 := bstep (se 1 (by rfl) ⟨3767255, by rfl⟩ : syracuseStep 5023007 = 7534511) B7534511
theorem B3348671 : Blo 2231435 3348671 := bstep (se 1 (by rfl) ⟨2511503, by rfl⟩ : syracuseStep 3348671 = 5023007) B5023007
theorem B2232447 : Blo 2231435 2232447 := bstep (se 1 (by rfl) ⟨1674335, by rfl⟩ : syracuseStep 2232447 = 3348671) B3348671
theorem B3348677 : Blo 2231435 3348677 := bbase (se 4 (by rfl) ⟨313938, by rfl⟩ : syracuseStep 3348677 = 627877) (by norm_num)
theorem B2232451 : Blo 2231435 2232451 := bstep (se 1 (by rfl) ⟨1674338, by rfl⟩ : syracuseStep 2232451 = 3348677) B3348677
theorem B3767269 : Blo 2231435 3767269 := bbase (se 4 (by rfl) ⟨353181, by rfl⟩ : syracuseStep 3767269 = 706363) (by norm_num)
theorem B5023025 : Blo 2231435 5023025 := bstep (se 2 (by rfl) ⟨1883634, by rfl⟩ : syracuseStep 5023025 = 3767269) B3767269
theorem B3348683 : Blo 2231435 3348683 := bstep (se 1 (by rfl) ⟨2511512, by rfl⟩ : syracuseStep 3348683 = 5023025) B5023025
theorem B2232455 : Blo 2231435 2232455 := bstep (se 1 (by rfl) ⟨1674341, by rfl⟩ : syracuseStep 2232455 = 3348683) B3348683
theorem B2511517 : Blo 2231435 2511517 := bbase (se 3 (by rfl) ⟨470909, by rfl⟩ : syracuseStep 2511517 = 941819) (by norm_num)
theorem B3348689 : Blo 2231435 3348689 := bstep (se 2 (by rfl) ⟨1255758, by rfl⟩ : syracuseStep 3348689 = 2511517) B2511517
theorem B2232459 : Blo 2231435 2232459 := bstep (se 1 (by rfl) ⟨1674344, by rfl⟩ : syracuseStep 2232459 = 3348689) B3348689
theorem B7534565 : Blo 2231435 7534565 := bbase (se 4 (by rfl) ⟨706365, by rfl⟩ : syracuseStep 7534565 = 1412731) (by norm_num)
theorem B5023043 : Blo 2231435 5023043 := bstep (se 1 (by rfl) ⟨3767282, by rfl⟩ : syracuseStep 5023043 = 7534565) B7534565
theorem B3348695 : Blo 2231435 3348695 := bstep (se 1 (by rfl) ⟨2511521, by rfl⟩ : syracuseStep 3348695 = 5023043) B5023043
theorem B2232463 : Blo 2231435 2232463 := bstep (se 1 (by rfl) ⟨1674347, by rfl⟩ : syracuseStep 2232463 = 3348695) B3348695
theorem B3348701 : Blo 2231435 3348701 := bbase (se 3 (by rfl) ⟨627881, by rfl⟩ : syracuseStep 3348701 = 1255763) (by norm_num)
theorem B2232467 : Blo 2231435 2232467 := bstep (se 1 (by rfl) ⟨1674350, by rfl⟩ : syracuseStep 2232467 = 3348701) B3348701
theorem B5023061 : Blo 2231435 5023061 := bbase (se 12 (by rfl) ⟨1839, by rfl⟩ : syracuseStep 5023061 = 3679) (by norm_num)
theorem B3348707 : Blo 2231435 3348707 := bstep (se 1 (by rfl) ⟨2511530, by rfl⟩ : syracuseStep 3348707 = 5023061) B5023061
theorem B2232471 : Blo 2231435 2232471 := bstep (se 1 (by rfl) ⟨1674353, by rfl⟩ : syracuseStep 2232471 = 3348707) B3348707
theorem B2383997 : Blo 2231435 2383997 := bbase (se 3 (by rfl) ⟨446999, by rfl⟩ : syracuseStep 2383997 = 893999) (by norm_num)
theorem B6357325 : Blo 2231435 6357325 := bstep (se 3 (by rfl) ⟨1191998, by rfl⟩ : syracuseStep 6357325 = 2383997) B2383997
theorem B8476433 : Blo 2231435 8476433 := bstep (se 2 (by rfl) ⟨3178662, by rfl⟩ : syracuseStep 8476433 = 6357325) B6357325
theorem B5650955 : Blo 2231435 5650955 := bstep (se 1 (by rfl) ⟨4238216, by rfl⟩ : syracuseStep 5650955 = 8476433) B8476433
theorem B3767303 : Blo 2231435 3767303 := bstep (se 1 (by rfl) ⟨2825477, by rfl⟩ : syracuseStep 3767303 = 5650955) B5650955
theorem B2511535 : Blo 2231435 2511535 := bstep (se 1 (by rfl) ⟨1883651, by rfl⟩ : syracuseStep 2511535 = 3767303) B3767303
theorem B3348713 : Blo 2231435 3348713 := bstep (se 2 (by rfl) ⟨1255767, by rfl⟩ : syracuseStep 3348713 = 2511535) B2511535
theorem B2232475 : Blo 2231435 2232475 := bstep (se 1 (by rfl) ⟨1674356, by rfl⟩ : syracuseStep 2232475 = 3348713) B3348713
theorem B4525877 : Blo 2231435 4525877 := bbase (se 5 (by rfl) ⟨212150, by rfl⟩ : syracuseStep 4525877 = 424301) (by norm_num)
theorem B12069005 : Blo 2231435 12069005 := bstep (se 3 (by rfl) ⟨2262938, by rfl⟩ : syracuseStep 12069005 = 4525877) B4525877
theorem B32184013 : Blo 2231435 32184013 := bstep (se 3 (by rfl) ⟨6034502, by rfl⟩ : syracuseStep 32184013 = 12069005) B12069005
theorem B42912017 : Blo 2231435 42912017 := bstep (se 2 (by rfl) ⟨16092006, by rfl⟩ : syracuseStep 42912017 = 32184013) B32184013
theorem B28608011 : Blo 2231435 28608011 := bstep (se 1 (by rfl) ⟨21456008, by rfl⟩ : syracuseStep 28608011 = 42912017) B42912017
theorem B19072007 : Blo 2231435 19072007 := bstep (se 1 (by rfl) ⟨14304005, by rfl⟩ : syracuseStep 19072007 = 28608011) B28608011
theorem B12714671 : Blo 2231435 12714671 := bstep (se 1 (by rfl) ⟨9536003, by rfl⟩ : syracuseStep 12714671 = 19072007) B19072007
theorem B8476447 : Blo 2231435 8476447 := bstep (se 1 (by rfl) ⟨6357335, by rfl⟩ : syracuseStep 8476447 = 12714671) B12714671
theorem B11301929 : Blo 2231435 11301929 := bstep (se 2 (by rfl) ⟨4238223, by rfl⟩ : syracuseStep 11301929 = 8476447) B8476447
theorem B7534619 : Blo 2231435 7534619 := bstep (se 1 (by rfl) ⟨5650964, by rfl⟩ : syracuseStep 7534619 = 11301929) B11301929
theorem B5023079 : Blo 2231435 5023079 := bstep (se 1 (by rfl) ⟨3767309, by rfl⟩ : syracuseStep 5023079 = 7534619) B7534619
theorem B3348719 : Blo 2231435 3348719 := bstep (se 1 (by rfl) ⟨2511539, by rfl⟩ : syracuseStep 3348719 = 5023079) B5023079
theorem B2232479 : Blo 2231435 2232479 := bstep (se 1 (by rfl) ⟨1674359, by rfl⟩ : syracuseStep 2232479 = 3348719) B3348719
theorem B3348725 : Blo 2231435 3348725 := bbase (se 5 (by rfl) ⟨156971, by rfl⟩ : syracuseStep 3348725 = 313943) (by norm_num)
theorem B2232483 : Blo 2231435 2232483 := bstep (se 1 (by rfl) ⟨1674362, by rfl⟩ : syracuseStep 2232483 = 3348725) B3348725
theorem B3394421 : Blo 2231435 3394421 := bbase (se 5 (by rfl) ⟨159113, by rfl⟩ : syracuseStep 3394421 = 318227) (by norm_num)
theorem B2262947 : Blo 2231435 2262947 := bstep (se 1 (by rfl) ⟨1697210, by rfl⟩ : syracuseStep 2262947 = 3394421) B3394421
theorem B24138101 : Blo 2231435 24138101 := bstep (se 5 (by rfl) ⟨1131473, by rfl⟩ : syracuseStep 24138101 = 2262947) B2262947
theorem B16092067 : Blo 2231435 16092067 := bstep (se 1 (by rfl) ⟨12069050, by rfl⟩ : syracuseStep 16092067 = 24138101) B24138101
theorem B21456089 : Blo 2231435 21456089 := bstep (se 2 (by rfl) ⟨8046033, by rfl⟩ : syracuseStep 21456089 = 16092067) B16092067
theorem B14304059 : Blo 2231435 14304059 := bstep (se 1 (by rfl) ⟨10728044, by rfl⟩ : syracuseStep 14304059 = 21456089) B21456089
theorem B9536039 : Blo 2231435 9536039 := bstep (se 1 (by rfl) ⟨7152029, by rfl⟩ : syracuseStep 9536039 = 14304059) B14304059
theorem B6357359 : Blo 2231435 6357359 := bstep (se 1 (by rfl) ⟨4768019, by rfl⟩ : syracuseStep 6357359 = 9536039) B9536039
theorem B4238239 : Blo 2231435 4238239 := bstep (se 1 (by rfl) ⟨3178679, by rfl⟩ : syracuseStep 4238239 = 6357359) B6357359
theorem B5650985 : Blo 2231435 5650985 := bstep (se 2 (by rfl) ⟨2119119, by rfl⟩ : syracuseStep 5650985 = 4238239) B4238239
theorem B3767323 : Blo 2231435 3767323 := bstep (se 1 (by rfl) ⟨2825492, by rfl⟩ : syracuseStep 3767323 = 5650985) B5650985
theorem B5023097 : Blo 2231435 5023097 := bstep (se 2 (by rfl) ⟨1883661, by rfl⟩ : syracuseStep 5023097 = 3767323) B3767323
theorem B3348731 : Blo 2231435 3348731 := bstep (se 1 (by rfl) ⟨2511548, by rfl⟩ : syracuseStep 3348731 = 5023097) B5023097
theorem B2232487 : Blo 2231435 2232487 := bstep (se 1 (by rfl) ⟨1674365, by rfl⟩ : syracuseStep 2232487 = 3348731) B3348731
theorem B2511553 : Blo 2231435 2511553 := bbase (se 2 (by rfl) ⟨941832, by rfl⟩ : syracuseStep 2511553 = 1883665) (by norm_num)
theorem B3348737 : Blo 2231435 3348737 := bstep (se 2 (by rfl) ⟨1255776, by rfl⟩ : syracuseStep 3348737 = 2511553) B2511553
theorem B2232491 : Blo 2231435 2232491 := bstep (se 1 (by rfl) ⟨1674368, by rfl⟩ : syracuseStep 2232491 = 3348737) B3348737
theorem B5651005 : Blo 2231435 5651005 := bbase (se 3 (by rfl) ⟨1059563, by rfl⟩ : syracuseStep 5651005 = 2119127) (by norm_num)
theorem B7534673 : Blo 2231435 7534673 := bstep (se 2 (by rfl) ⟨2825502, by rfl⟩ : syracuseStep 7534673 = 5651005) B5651005
theorem B5023115 : Blo 2231435 5023115 := bstep (se 1 (by rfl) ⟨3767336, by rfl⟩ : syracuseStep 5023115 = 7534673) B7534673
theorem B3348743 : Blo 2231435 3348743 := bstep (se 1 (by rfl) ⟨2511557, by rfl⟩ : syracuseStep 3348743 = 5023115) B5023115
theorem B2232495 : Blo 2231435 2232495 := bstep (se 1 (by rfl) ⟨1674371, by rfl⟩ : syracuseStep 2232495 = 3348743) B3348743
theorem B3348749 : Blo 2231435 3348749 := bbase (se 3 (by rfl) ⟨627890, by rfl⟩ : syracuseStep 3348749 = 1255781) (by norm_num)
theorem B2232499 : Blo 2231435 2232499 := bstep (se 1 (by rfl) ⟨1674374, by rfl⟩ : syracuseStep 2232499 = 3348749) B3348749
theorem B5023133 : Blo 2231435 5023133 := bbase (se 3 (by rfl) ⟨941837, by rfl⟩ : syracuseStep 5023133 = 1883675) (by norm_num)
theorem B3348755 : Blo 2231435 3348755 := bstep (se 1 (by rfl) ⟨2511566, by rfl⟩ : syracuseStep 3348755 = 5023133) B5023133
theorem B2232503 : Blo 2231435 2232503 := bstep (se 1 (by rfl) ⟨1674377, by rfl⟩ : syracuseStep 2232503 = 3348755) B3348755
theorem B3767357 : Blo 2231435 3767357 := bbase (se 3 (by rfl) ⟨706379, by rfl⟩ : syracuseStep 3767357 = 1412759) (by norm_num)
theorem B2511571 : Blo 2231435 2511571 := bstep (se 1 (by rfl) ⟨1883678, by rfl⟩ : syracuseStep 2511571 = 3767357) B3767357
theorem B3348761 : Blo 2231435 3348761 := bstep (se 2 (by rfl) ⟨1255785, by rfl⟩ : syracuseStep 3348761 = 2511571) B2511571
theorem B2232507 : Blo 2231435 2232507 := bstep (se 1 (by rfl) ⟨1674380, by rfl⟩ : syracuseStep 2232507 = 3348761) B3348761
theorem B3576053 : Blo 2231435 3576053 := bbase (se 5 (by rfl) ⟨167627, by rfl⟩ : syracuseStep 3576053 = 335255) (by norm_num)
theorem B2384035 : Blo 2231435 2384035 := bstep (se 1 (by rfl) ⟨1788026, by rfl⟩ : syracuseStep 2384035 = 3576053) B3576053
theorem B12714853 : Blo 2231435 12714853 := bstep (se 4 (by rfl) ⟨1192017, by rfl⟩ : syracuseStep 12714853 = 2384035) B2384035
theorem B16953137 : Blo 2231435 16953137 := bstep (se 2 (by rfl) ⟨6357426, by rfl⟩ : syracuseStep 16953137 = 12714853) B12714853
theorem B11302091 : Blo 2231435 11302091 := bstep (se 1 (by rfl) ⟨8476568, by rfl⟩ : syracuseStep 11302091 = 16953137) B16953137
theorem B7534727 : Blo 2231435 7534727 := bstep (se 1 (by rfl) ⟨5651045, by rfl⟩ : syracuseStep 7534727 = 11302091) B11302091
theorem B5023151 : Blo 2231435 5023151 := bstep (se 1 (by rfl) ⟨3767363, by rfl⟩ : syracuseStep 5023151 = 7534727) B7534727
theorem B3348767 : Blo 2231435 3348767 := bstep (se 1 (by rfl) ⟨2511575, by rfl⟩ : syracuseStep 3348767 = 5023151) B5023151
theorem B2232511 : Blo 2231435 2232511 := bstep (se 1 (by rfl) ⟨1674383, by rfl⟩ : syracuseStep 2232511 = 3348767) B3348767
theorem B3348773 : Blo 2231435 3348773 := bbase (se 4 (by rfl) ⟨313947, by rfl⟩ : syracuseStep 3348773 = 627895) (by norm_num)
theorem B2232515 : Blo 2231435 2232515 := bstep (se 1 (by rfl) ⟨1674386, by rfl⟩ : syracuseStep 2232515 = 3348773) B3348773
theorem B2825533 : Blo 2231435 2825533 := bbase (se 3 (by rfl) ⟨529787, by rfl⟩ : syracuseStep 2825533 = 1059575) (by norm_num)
theorem B3767377 : Blo 2231435 3767377 := bstep (se 2 (by rfl) ⟨1412766, by rfl⟩ : syracuseStep 3767377 = 2825533) B2825533
theorem B5023169 : Blo 2231435 5023169 := bstep (se 2 (by rfl) ⟨1883688, by rfl⟩ : syracuseStep 5023169 = 3767377) B3767377
theorem B3348779 : Blo 2231435 3348779 := bstep (se 1 (by rfl) ⟨2511584, by rfl⟩ : syracuseStep 3348779 = 5023169) B5023169
theorem B2232519 : Blo 2231435 2232519 := bstep (se 1 (by rfl) ⟨1674389, by rfl⟩ : syracuseStep 2232519 = 3348779) B3348779
theorem B2511589 : Blo 2231435 2511589 := bbase (se 4 (by rfl) ⟨235461, by rfl⟩ : syracuseStep 2511589 = 470923) (by norm_num)
theorem B3348785 : Blo 2231435 3348785 := bstep (se 2 (by rfl) ⟨1255794, by rfl⟩ : syracuseStep 3348785 = 2511589) B2511589
theorem B2232523 : Blo 2231435 2232523 := bstep (se 1 (by rfl) ⟨1674392, by rfl⟩ : syracuseStep 2232523 = 3348785) B3348785
theorem B12069269 : Blo 2231435 12069269 := bbase (se 6 (by rfl) ⟨282873, by rfl⟩ : syracuseStep 12069269 = 565747) (by norm_num)
theorem B8046179 : Blo 2231435 8046179 := bstep (se 1 (by rfl) ⟨6034634, by rfl⟩ : syracuseStep 8046179 = 12069269) B12069269
theorem B5364119 : Blo 2231435 5364119 := bstep (se 1 (by rfl) ⟨4023089, by rfl⟩ : syracuseStep 5364119 = 8046179) B8046179
theorem B3576079 : Blo 2231435 3576079 := bstep (se 1 (by rfl) ⟨2682059, by rfl⟩ : syracuseStep 3576079 = 5364119) B5364119
theorem B4768105 : Blo 2231435 4768105 := bstep (se 2 (by rfl) ⟨1788039, by rfl⟩ : syracuseStep 4768105 = 3576079) B3576079
theorem B6357473 : Blo 2231435 6357473 := bstep (se 2 (by rfl) ⟨2384052, by rfl⟩ : syracuseStep 6357473 = 4768105) B4768105
theorem B4238315 : Blo 2231435 4238315 := bstep (se 1 (by rfl) ⟨3178736, by rfl⟩ : syracuseStep 4238315 = 6357473) B6357473
theorem B2825543 : Blo 2231435 2825543 := bstep (se 1 (by rfl) ⟨2119157, by rfl⟩ : syracuseStep 2825543 = 4238315) B4238315
theorem B7534781 : Blo 2231435 7534781 := bstep (se 3 (by rfl) ⟨1412771, by rfl⟩ : syracuseStep 7534781 = 2825543) B2825543
theorem B5023187 : Blo 2231435 5023187 := bstep (se 1 (by rfl) ⟨3767390, by rfl⟩ : syracuseStep 5023187 = 7534781) B7534781
theorem B3348791 : Blo 2231435 3348791 := bstep (se 1 (by rfl) ⟨2511593, by rfl⟩ : syracuseStep 3348791 = 5023187) B5023187
theorem B2232527 : Blo 2231435 2232527 := bstep (se 1 (by rfl) ⟨1674395, by rfl⟩ : syracuseStep 2232527 = 3348791) B3348791
theorem B3348797 : Blo 2231435 3348797 := bbase (se 3 (by rfl) ⟨627899, by rfl⟩ : syracuseStep 3348797 = 1255799) (by norm_num)
theorem B2232531 : Blo 2231435 2232531 := bstep (se 1 (by rfl) ⟨1674398, by rfl⟩ : syracuseStep 2232531 = 3348797) B3348797
theorem B5023205 : Blo 2231435 5023205 := bbase (se 4 (by rfl) ⟨470925, by rfl⟩ : syracuseStep 5023205 = 941851) (by norm_num)
theorem B3348803 : Blo 2231435 3348803 := bstep (se 1 (by rfl) ⟨2511602, by rfl⟩ : syracuseStep 3348803 = 5023205) B5023205
theorem B2232535 : Blo 2231435 2232535 := bstep (se 1 (by rfl) ⟨1674401, by rfl⟩ : syracuseStep 2232535 = 3348803) B3348803
theorem B5651117 : Blo 2231435 5651117 := bbase (se 3 (by rfl) ⟨1059584, by rfl⟩ : syracuseStep 5651117 = 2119169) (by norm_num)
theorem B3767411 : Blo 2231435 3767411 := bstep (se 1 (by rfl) ⟨2825558, by rfl⟩ : syracuseStep 3767411 = 5651117) B5651117
theorem B2511607 : Blo 2231435 2511607 := bstep (se 1 (by rfl) ⟨1883705, by rfl⟩ : syracuseStep 2511607 = 3767411) B3767411
theorem B3348809 : Blo 2231435 3348809 := bstep (se 2 (by rfl) ⟨1255803, by rfl⟩ : syracuseStep 3348809 = 2511607) B2511607
theorem B2232539 : Blo 2231435 2232539 := bstep (se 1 (by rfl) ⟨1674404, by rfl⟩ : syracuseStep 2232539 = 3348809) B3348809
theorem B5364157 : Blo 2231435 5364157 := bbase (se 3 (by rfl) ⟨1005779, by rfl⟩ : syracuseStep 5364157 = 2011559) (by norm_num)
theorem B7152209 : Blo 2231435 7152209 := bstep (se 2 (by rfl) ⟨2682078, by rfl⟩ : syracuseStep 7152209 = 5364157) B5364157
theorem B4768139 : Blo 2231435 4768139 := bstep (se 1 (by rfl) ⟨3576104, by rfl⟩ : syracuseStep 4768139 = 7152209) B7152209
theorem B3178759 : Blo 2231435 3178759 := bstep (se 1 (by rfl) ⟨2384069, by rfl⟩ : syracuseStep 3178759 = 4768139) B4768139
theorem B4238345 : Blo 2231435 4238345 := bstep (se 2 (by rfl) ⟨1589379, by rfl⟩ : syracuseStep 4238345 = 3178759) B3178759
theorem B11302253 : Blo 2231435 11302253 := bstep (se 3 (by rfl) ⟨2119172, by rfl⟩ : syracuseStep 11302253 = 4238345) B4238345
theorem B7534835 : Blo 2231435 7534835 := bstep (se 1 (by rfl) ⟨5651126, by rfl⟩ : syracuseStep 7534835 = 11302253) B11302253
theorem B5023223 : Blo 2231435 5023223 := bstep (se 1 (by rfl) ⟨3767417, by rfl⟩ : syracuseStep 5023223 = 7534835) B7534835
theorem B3348815 : Blo 2231435 3348815 := bstep (se 1 (by rfl) ⟨2511611, by rfl⟩ : syracuseStep 3348815 = 5023223) B5023223
theorem B2232543 : Blo 2231435 2232543 := bstep (se 1 (by rfl) ⟨1674407, by rfl⟩ : syracuseStep 2232543 = 3348815) B3348815
theorem B3348821 : Blo 2231435 3348821 := bbase (se 10 (by rfl) ⟨4905, by rfl⟩ : syracuseStep 3348821 = 9811) (by norm_num)
theorem B2232547 : Blo 2231435 2232547 := bstep (se 1 (by rfl) ⟨1674410, by rfl⟩ : syracuseStep 2232547 = 3348821) B3348821
theorem B6357541 : Blo 2231435 6357541 := bbase (se 4 (by rfl) ⟨596019, by rfl⟩ : syracuseStep 6357541 = 1192039) (by norm_num)
theorem B8476721 : Blo 2231435 8476721 := bstep (se 2 (by rfl) ⟨3178770, by rfl⟩ : syracuseStep 8476721 = 6357541) B6357541
theorem B5651147 : Blo 2231435 5651147 := bstep (se 1 (by rfl) ⟨4238360, by rfl⟩ : syracuseStep 5651147 = 8476721) B8476721
theorem B3767431 : Blo 2231435 3767431 := bstep (se 1 (by rfl) ⟨2825573, by rfl⟩ : syracuseStep 3767431 = 5651147) B5651147
theorem B5023241 : Blo 2231435 5023241 := bstep (se 2 (by rfl) ⟨1883715, by rfl⟩ : syracuseStep 5023241 = 3767431) B3767431
theorem B3348827 : Blo 2231435 3348827 := bstep (se 1 (by rfl) ⟨2511620, by rfl⟩ : syracuseStep 3348827 = 5023241) B5023241
theorem B2232551 : Blo 2231435 2232551 := bstep (se 1 (by rfl) ⟨1674413, by rfl⟩ : syracuseStep 2232551 = 3348827) B3348827
theorem B2511625 : Blo 2231435 2511625 := bbase (se 2 (by rfl) ⟨941859, by rfl⟩ : syracuseStep 2511625 = 1883719) (by norm_num)
theorem B3348833 : Blo 2231435 3348833 := bstep (se 2 (by rfl) ⟨1255812, by rfl⟩ : syracuseStep 3348833 = 2511625) B2511625
theorem B2232555 : Blo 2231435 2232555 := bstep (se 1 (by rfl) ⟨1674416, by rfl⟩ : syracuseStep 2232555 = 3348833) B3348833
theorem B10728389 : Blo 2231435 10728389 := bbase (se 4 (by rfl) ⟨1005786, by rfl⟩ : syracuseStep 10728389 = 2011573) (by norm_num)
theorem B28609037 : Blo 2231435 28609037 := bstep (se 3 (by rfl) ⟨5364194, by rfl⟩ : syracuseStep 28609037 = 10728389) B10728389
theorem B19072691 : Blo 2231435 19072691 := bstep (se 1 (by rfl) ⟨14304518, by rfl⟩ : syracuseStep 19072691 = 28609037) B28609037
theorem B12715127 : Blo 2231435 12715127 := bstep (se 1 (by rfl) ⟨9536345, by rfl⟩ : syracuseStep 12715127 = 19072691) B19072691
theorem B8476751 : Blo 2231435 8476751 := bstep (se 1 (by rfl) ⟨6357563, by rfl⟩ : syracuseStep 8476751 = 12715127) B12715127
theorem B5651167 : Blo 2231435 5651167 := bstep (se 1 (by rfl) ⟨4238375, by rfl⟩ : syracuseStep 5651167 = 8476751) B8476751
theorem B7534889 : Blo 2231435 7534889 := bstep (se 2 (by rfl) ⟨2825583, by rfl⟩ : syracuseStep 7534889 = 5651167) B5651167
theorem B5023259 : Blo 2231435 5023259 := bstep (se 1 (by rfl) ⟨3767444, by rfl⟩ : syracuseStep 5023259 = 7534889) B7534889
theorem B3348839 : Blo 2231435 3348839 := bstep (se 1 (by rfl) ⟨2511629, by rfl⟩ : syracuseStep 3348839 = 5023259) B5023259
theorem B2232559 : Blo 2231435 2232559 := bstep (se 1 (by rfl) ⟨1674419, by rfl⟩ : syracuseStep 2232559 = 3348839) B3348839
theorem B3348845 : Blo 2231435 3348845 := bbase (se 3 (by rfl) ⟨627908, by rfl⟩ : syracuseStep 3348845 = 1255817) (by norm_num)
theorem B2232563 : Blo 2231435 2232563 := bstep (se 1 (by rfl) ⟨1674422, by rfl⟩ : syracuseStep 2232563 = 3348845) B3348845
theorem B5023277 : Blo 2231435 5023277 := bbase (se 3 (by rfl) ⟨941864, by rfl⟩ : syracuseStep 5023277 = 1883729) (by norm_num)
theorem B3348851 : Blo 2231435 3348851 := bstep (se 1 (by rfl) ⟨2511638, by rfl⟩ : syracuseStep 3348851 = 5023277) B5023277
theorem B2232567 : Blo 2231435 2232567 := bstep (se 1 (by rfl) ⟨1674425, by rfl⟩ : syracuseStep 2232567 = 3348851) B3348851
theorem B3394549 : Blo 2231435 3394549 := bbase (se 5 (by rfl) ⟨159119, by rfl⟩ : syracuseStep 3394549 = 318239) (by norm_num)
theorem B4526065 : Blo 2231435 4526065 := bstep (se 2 (by rfl) ⟨1697274, by rfl⟩ : syracuseStep 4526065 = 3394549) B3394549
theorem B6034753 : Blo 2231435 6034753 := bstep (se 2 (by rfl) ⟨2263032, by rfl⟩ : syracuseStep 6034753 = 4526065) B4526065
theorem B32185349 : Blo 2231435 32185349 := bstep (se 4 (by rfl) ⟨3017376, by rfl⟩ : syracuseStep 32185349 = 6034753) B6034753
theorem B21456899 : Blo 2231435 21456899 := bstep (se 1 (by rfl) ⟨16092674, by rfl⟩ : syracuseStep 21456899 = 32185349) B32185349
theorem B14304599 : Blo 2231435 14304599 := bstep (se 1 (by rfl) ⟨10728449, by rfl⟩ : syracuseStep 14304599 = 21456899) B21456899
theorem B9536399 : Blo 2231435 9536399 := bstep (se 1 (by rfl) ⟨7152299, by rfl⟩ : syracuseStep 9536399 = 14304599) B14304599
theorem B6357599 : Blo 2231435 6357599 := bstep (se 1 (by rfl) ⟨4768199, by rfl⟩ : syracuseStep 6357599 = 9536399) B9536399
theorem B4238399 : Blo 2231435 4238399 := bstep (se 1 (by rfl) ⟨3178799, by rfl⟩ : syracuseStep 4238399 = 6357599) B6357599
theorem B2825599 : Blo 2231435 2825599 := bstep (se 1 (by rfl) ⟨2119199, by rfl⟩ : syracuseStep 2825599 = 4238399) B4238399
theorem B3767465 : Blo 2231435 3767465 := bstep (se 2 (by rfl) ⟨1412799, by rfl⟩ : syracuseStep 3767465 = 2825599) B2825599
theorem B2511643 : Blo 2231435 2511643 := bstep (se 1 (by rfl) ⟨1883732, by rfl⟩ : syracuseStep 2511643 = 3767465) B3767465
theorem B3348857 : Blo 2231435 3348857 := bstep (se 2 (by rfl) ⟨1255821, by rfl⟩ : syracuseStep 3348857 = 2511643) B2511643
theorem B2232571 : Blo 2231435 2232571 := bstep (se 1 (by rfl) ⟨1674428, by rfl⟩ : syracuseStep 2232571 = 3348857) B3348857
theorem B6789109 : Blo 2231435 6789109 := bbase (se 5 (by rfl) ⟨318239, by rfl⟩ : syracuseStep 6789109 = 636479) (by norm_num)
theorem B9052145 : Blo 2231435 9052145 := bstep (se 2 (by rfl) ⟨3394554, by rfl⟩ : syracuseStep 9052145 = 6789109) B6789109
theorem B6034763 : Blo 2231435 6034763 := bstep (se 1 (by rfl) ⟨4526072, by rfl⟩ : syracuseStep 6034763 = 9052145) B9052145
theorem B4023175 : Blo 2231435 4023175 := bstep (se 1 (by rfl) ⟨3017381, by rfl⟩ : syracuseStep 4023175 = 6034763) B6034763
theorem B5364233 : Blo 2231435 5364233 := bstep (se 2 (by rfl) ⟨2011587, by rfl⟩ : syracuseStep 5364233 = 4023175) B4023175
theorem B3576155 : Blo 2231435 3576155 := bstep (se 1 (by rfl) ⟨2682116, by rfl⟩ : syracuseStep 3576155 = 5364233) B5364233
theorem B38145653 : Blo 2231435 38145653 := bstep (se 5 (by rfl) ⟨1788077, by rfl⟩ : syracuseStep 38145653 = 3576155) B3576155
theorem B25430435 : Blo 2231435 25430435 := bstep (se 1 (by rfl) ⟨19072826, by rfl⟩ : syracuseStep 25430435 = 38145653) B38145653
theorem B16953623 : Blo 2231435 16953623 := bstep (se 1 (by rfl) ⟨12715217, by rfl⟩ : syracuseStep 16953623 = 25430435) B25430435
theorem B11302415 : Blo 2231435 11302415 := bstep (se 1 (by rfl) ⟨8476811, by rfl⟩ : syracuseStep 11302415 = 16953623) B16953623
theorem B7534943 : Blo 2231435 7534943 := bstep (se 1 (by rfl) ⟨5651207, by rfl⟩ : syracuseStep 7534943 = 11302415) B11302415
theorem B5023295 : Blo 2231435 5023295 := bstep (se 1 (by rfl) ⟨3767471, by rfl⟩ : syracuseStep 5023295 = 7534943) B7534943
theorem B3348863 : Blo 2231435 3348863 := bstep (se 1 (by rfl) ⟨2511647, by rfl⟩ : syracuseStep 3348863 = 5023295) B5023295
theorem B2232575 : Blo 2231435 2232575 := bstep (se 1 (by rfl) ⟨1674431, by rfl⟩ : syracuseStep 2232575 = 3348863) B3348863
theorem B3348869 : Blo 2231435 3348869 := bbase (se 4 (by rfl) ⟨313956, by rfl⟩ : syracuseStep 3348869 = 627913) (by norm_num)
theorem B2232579 : Blo 2231435 2232579 := bstep (se 1 (by rfl) ⟨1674434, by rfl⟩ : syracuseStep 2232579 = 3348869) B3348869
theorem B3767485 : Blo 2231435 3767485 := bbase (se 3 (by rfl) ⟨706403, by rfl⟩ : syracuseStep 3767485 = 1412807) (by norm_num)
theorem B5023313 : Blo 2231435 5023313 := bstep (se 2 (by rfl) ⟨1883742, by rfl⟩ : syracuseStep 5023313 = 3767485) B3767485
theorem B3348875 : Blo 2231435 3348875 := bstep (se 1 (by rfl) ⟨2511656, by rfl⟩ : syracuseStep 3348875 = 5023313) B5023313
theorem B2232583 : Blo 2231435 2232583 := bstep (se 1 (by rfl) ⟨1674437, by rfl⟩ : syracuseStep 2232583 = 3348875) B3348875
theorem B2511661 : Blo 2231435 2511661 := bbase (se 3 (by rfl) ⟨470936, by rfl⟩ : syracuseStep 2511661 = 941873) (by norm_num)
theorem B3348881 : Blo 2231435 3348881 := bstep (se 2 (by rfl) ⟨1255830, by rfl⟩ : syracuseStep 3348881 = 2511661) B2511661
theorem B2232587 : Blo 2231435 2232587 := bstep (se 1 (by rfl) ⟨1674440, by rfl⟩ : syracuseStep 2232587 = 3348881) B3348881
theorem B7534997 : Blo 2231435 7534997 := bbase (se 6 (by rfl) ⟨176601, by rfl⟩ : syracuseStep 7534997 = 353203) (by norm_num)
theorem B5023331 : Blo 2231435 5023331 := bstep (se 1 (by rfl) ⟨3767498, by rfl⟩ : syracuseStep 5023331 = 7534997) B7534997
theorem B3348887 : Blo 2231435 3348887 := bstep (se 1 (by rfl) ⟨2511665, by rfl⟩ : syracuseStep 3348887 = 5023331) B5023331
theorem B2232591 : Blo 2231435 2232591 := bstep (se 1 (by rfl) ⟨1674443, by rfl⟩ : syracuseStep 2232591 = 3348887) B3348887
theorem B3348893 : Blo 2231435 3348893 := bbase (se 3 (by rfl) ⟨627917, by rfl⟩ : syracuseStep 3348893 = 1255835) (by norm_num)
theorem B2232595 : Blo 2231435 2232595 := bstep (se 1 (by rfl) ⟨1674446, by rfl⟩ : syracuseStep 2232595 = 3348893) B3348893
theorem B5023349 : Blo 2231435 5023349 := bbase (se 5 (by rfl) ⟨235469, by rfl⟩ : syracuseStep 5023349 = 470939) (by norm_num)
theorem B3348899 : Blo 2231435 3348899 := bstep (se 1 (by rfl) ⟨2511674, by rfl⟩ : syracuseStep 3348899 = 5023349) B5023349
theorem B2232599 : Blo 2231435 2232599 := bstep (se 1 (by rfl) ⟨1674449, by rfl⟩ : syracuseStep 2232599 = 3348899) B3348899
theorem B5364301 : Blo 2231435 5364301 := bbase (se 3 (by rfl) ⟨1005806, by rfl⟩ : syracuseStep 5364301 = 2011613) (by norm_num)
theorem B7152401 : Blo 2231435 7152401 := bstep (se 2 (by rfl) ⟨2682150, by rfl⟩ : syracuseStep 7152401 = 5364301) B5364301
theorem B19073069 : Blo 2231435 19073069 := bstep (se 3 (by rfl) ⟨3576200, by rfl⟩ : syracuseStep 19073069 = 7152401) B7152401
theorem B12715379 : Blo 2231435 12715379 := bstep (se 1 (by rfl) ⟨9536534, by rfl⟩ : syracuseStep 12715379 = 19073069) B19073069
theorem B8476919 : Blo 2231435 8476919 := bstep (se 1 (by rfl) ⟨6357689, by rfl⟩ : syracuseStep 8476919 = 12715379) B12715379
theorem B5651279 : Blo 2231435 5651279 := bstep (se 1 (by rfl) ⟨4238459, by rfl⟩ : syracuseStep 5651279 = 8476919) B8476919
theorem B3767519 : Blo 2231435 3767519 := bstep (se 1 (by rfl) ⟨2825639, by rfl⟩ : syracuseStep 3767519 = 5651279) B5651279
theorem B2511679 : Blo 2231435 2511679 := bstep (se 1 (by rfl) ⟨1883759, by rfl⟩ : syracuseStep 2511679 = 3767519) B3767519
theorem B3348905 : Blo 2231435 3348905 := bstep (se 2 (by rfl) ⟨1255839, by rfl⟩ : syracuseStep 3348905 = 2511679) B2511679
theorem B2232603 : Blo 2231435 2232603 := bstep (se 1 (by rfl) ⟨1674452, by rfl⟩ : syracuseStep 2232603 = 3348905) B3348905
theorem B8476933 : Blo 2231435 8476933 := bbase (se 4 (by rfl) ⟨794712, by rfl⟩ : syracuseStep 8476933 = 1589425) (by norm_num)
theorem B11302577 : Blo 2231435 11302577 := bstep (se 2 (by rfl) ⟨4238466, by rfl⟩ : syracuseStep 11302577 = 8476933) B8476933
theorem B7535051 : Blo 2231435 7535051 := bstep (se 1 (by rfl) ⟨5651288, by rfl⟩ : syracuseStep 7535051 = 11302577) B11302577
theorem B5023367 : Blo 2231435 5023367 := bstep (se 1 (by rfl) ⟨3767525, by rfl⟩ : syracuseStep 5023367 = 7535051) B7535051
theorem B3348911 : Blo 2231435 3348911 := bstep (se 1 (by rfl) ⟨2511683, by rfl⟩ : syracuseStep 3348911 = 5023367) B5023367
theorem B2232607 : Blo 2231435 2232607 := bstep (se 1 (by rfl) ⟨1674455, by rfl⟩ : syracuseStep 2232607 = 3348911) B3348911
theorem B3348917 : Blo 2231435 3348917 := bbase (se 5 (by rfl) ⟨156980, by rfl⟩ : syracuseStep 3348917 = 313961) (by norm_num)
theorem B2232611 : Blo 2231435 2232611 := bstep (se 1 (by rfl) ⟨1674458, by rfl⟩ : syracuseStep 2232611 = 3348917) B3348917
theorem B5651309 : Blo 2231435 5651309 := bbase (se 3 (by rfl) ⟨1059620, by rfl⟩ : syracuseStep 5651309 = 2119241) (by norm_num)
theorem B3767539 : Blo 2231435 3767539 := bstep (se 1 (by rfl) ⟨2825654, by rfl⟩ : syracuseStep 3767539 = 5651309) B5651309
theorem B5023385 : Blo 2231435 5023385 := bstep (se 2 (by rfl) ⟨1883769, by rfl⟩ : syracuseStep 5023385 = 3767539) B3767539
theorem B3348923 : Blo 2231435 3348923 := bstep (se 1 (by rfl) ⟨2511692, by rfl⟩ : syracuseStep 3348923 = 5023385) B5023385
theorem B2232615 : Blo 2231435 2232615 := bstep (se 1 (by rfl) ⟨1674461, by rfl⟩ : syracuseStep 2232615 = 3348923) B3348923
theorem B2511697 : Blo 2231435 2511697 := bbase (se 2 (by rfl) ⟨941886, by rfl⟩ : syracuseStep 2511697 = 1883773) (by norm_num)
theorem B3348929 : Blo 2231435 3348929 := bstep (se 2 (by rfl) ⟨1255848, by rfl⟩ : syracuseStep 3348929 = 2511697) B2511697
theorem B2232619 : Blo 2231435 2232619 := bstep (se 1 (by rfl) ⟨1674464, by rfl⟩ : syracuseStep 2232619 = 3348929) B3348929
theorem B29000213 : Blo 2231435 29000213 := bbase (se 6 (by rfl) ⟨679692, by rfl⟩ : syracuseStep 29000213 = 1359385) (by norm_num)
theorem B19333475 : Blo 2231435 19333475 := bstep (se 1 (by rfl) ⟨14500106, by rfl⟩ : syracuseStep 19333475 = 29000213) B29000213
theorem B12888983 : Blo 2231435 12888983 := bstep (se 1 (by rfl) ⟨9666737, by rfl⟩ : syracuseStep 12888983 = 19333475) B19333475
theorem B8592655 : Blo 2231435 8592655 := bstep (se 1 (by rfl) ⟨6444491, by rfl⟩ : syracuseStep 8592655 = 12888983) B12888983
theorem B11456873 : Blo 2231435 11456873 := bstep (se 2 (by rfl) ⟨4296327, by rfl⟩ : syracuseStep 11456873 = 8592655) B8592655
theorem B7637915 : Blo 2231435 7637915 := bstep (se 1 (by rfl) ⟨5728436, by rfl⟩ : syracuseStep 7637915 = 11456873) B11456873
theorem B20367773 : Blo 2231435 20367773 := bstep (se 3 (by rfl) ⟨3818957, by rfl⟩ : syracuseStep 20367773 = 7637915) B7637915
theorem B13578515 : Blo 2231435 13578515 := bstep (se 1 (by rfl) ⟨10183886, by rfl⟩ : syracuseStep 13578515 = 20367773) B20367773
theorem B9052343 : Blo 2231435 9052343 := bstep (se 1 (by rfl) ⟨6789257, by rfl⟩ : syracuseStep 9052343 = 13578515) B13578515
theorem B6034895 : Blo 2231435 6034895 := bstep (se 1 (by rfl) ⟨4526171, by rfl⟩ : syracuseStep 6034895 = 9052343) B9052343
theorem B4023263 : Blo 2231435 4023263 := bstep (se 1 (by rfl) ⟨3017447, by rfl⟩ : syracuseStep 4023263 = 6034895) B6034895
theorem B2682175 : Blo 2231435 2682175 := bstep (se 1 (by rfl) ⟨2011631, by rfl⟩ : syracuseStep 2682175 = 4023263) B4023263
theorem B3576233 : Blo 2231435 3576233 := bstep (se 2 (by rfl) ⟨1341087, by rfl⟩ : syracuseStep 3576233 = 2682175) B2682175
theorem B2384155 : Blo 2231435 2384155 := bstep (se 1 (by rfl) ⟨1788116, by rfl⟩ : syracuseStep 2384155 = 3576233) B3576233
theorem B3178873 : Blo 2231435 3178873 := bstep (se 2 (by rfl) ⟨1192077, by rfl⟩ : syracuseStep 3178873 = 2384155) B2384155
theorem B4238497 : Blo 2231435 4238497 := bstep (se 2 (by rfl) ⟨1589436, by rfl⟩ : syracuseStep 4238497 = 3178873) B3178873
theorem B5651329 : Blo 2231435 5651329 := bstep (se 2 (by rfl) ⟨2119248, by rfl⟩ : syracuseStep 5651329 = 4238497) B4238497
theorem B7535105 : Blo 2231435 7535105 := bstep (se 2 (by rfl) ⟨2825664, by rfl⟩ : syracuseStep 7535105 = 5651329) B5651329
theorem B5023403 : Blo 2231435 5023403 := bstep (se 1 (by rfl) ⟨3767552, by rfl⟩ : syracuseStep 5023403 = 7535105) B7535105
theorem B3348935 : Blo 2231435 3348935 := bstep (se 1 (by rfl) ⟨2511701, by rfl⟩ : syracuseStep 3348935 = 5023403) B5023403
theorem B2232623 : Blo 2231435 2232623 := bstep (se 1 (by rfl) ⟨1674467, by rfl⟩ : syracuseStep 2232623 = 3348935) B3348935
theorem B3348941 : Blo 2231435 3348941 := bbase (se 3 (by rfl) ⟨627926, by rfl⟩ : syracuseStep 3348941 = 1255853) (by norm_num)
theorem B2232627 : Blo 2231435 2232627 := bstep (se 1 (by rfl) ⟨1674470, by rfl⟩ : syracuseStep 2232627 = 3348941) B3348941
theorem B5023421 : Blo 2231435 5023421 := bbase (se 3 (by rfl) ⟨941891, by rfl⟩ : syracuseStep 5023421 = 1883783) (by norm_num)
theorem B3348947 : Blo 2231435 3348947 := bstep (se 1 (by rfl) ⟨2511710, by rfl⟩ : syracuseStep 3348947 = 5023421) B5023421
theorem B2232631 : Blo 2231435 2232631 := bstep (se 1 (by rfl) ⟨1674473, by rfl⟩ : syracuseStep 2232631 = 3348947) B3348947
theorem B3767573 : Blo 2231435 3767573 := bbase (se 6 (by rfl) ⟨88302, by rfl⟩ : syracuseStep 3767573 = 176605) (by norm_num)
theorem B2511715 : Blo 2231435 2511715 := bstep (se 1 (by rfl) ⟨1883786, by rfl⟩ : syracuseStep 2511715 = 3767573) B3767573
theorem B3348953 : Blo 2231435 3348953 := bstep (se 2 (by rfl) ⟨1255857, by rfl⟩ : syracuseStep 3348953 = 2511715) B2511715
theorem B2232635 : Blo 2231435 2232635 := bstep (se 1 (by rfl) ⟨1674476, by rfl⟩ : syracuseStep 2232635 = 3348953) B3348953
theorem B2942929 : Blo 2231435 2942929 := bbase (se 2 (by rfl) ⟨1103598, by rfl⟩ : syracuseStep 2942929 = 2207197) (by norm_num)
theorem B3923905 : Blo 2231435 3923905 := bstep (se 2 (by rfl) ⟨1471464, by rfl⟩ : syracuseStep 3923905 = 2942929) B2942929
theorem B5231873 : Blo 2231435 5231873 := bstep (se 2 (by rfl) ⟨1961952, by rfl⟩ : syracuseStep 5231873 = 3923905) B3923905
theorem B3487915 : Blo 2231435 3487915 := bstep (se 1 (by rfl) ⟨2615936, by rfl⟩ : syracuseStep 3487915 = 5231873) B5231873
theorem B4650553 : Blo 2231435 4650553 := bstep (se 2 (by rfl) ⟨1743957, by rfl⟩ : syracuseStep 4650553 = 3487915) B3487915
theorem B24802949 : Blo 2231435 24802949 := bstep (se 4 (by rfl) ⟨2325276, by rfl⟩ : syracuseStep 24802949 = 4650553) B4650553
theorem B16535299 : Blo 2231435 16535299 := bstep (se 1 (by rfl) ⟨12401474, by rfl⟩ : syracuseStep 16535299 = 24802949) B24802949
theorem B22047065 : Blo 2231435 22047065 := bstep (se 2 (by rfl) ⟨8267649, by rfl⟩ : syracuseStep 22047065 = 16535299) B16535299
theorem B14698043 : Blo 2231435 14698043 := bstep (se 1 (by rfl) ⟨11023532, by rfl⟩ : syracuseStep 14698043 = 22047065) B22047065
theorem B9798695 : Blo 2231435 9798695 := bstep (se 1 (by rfl) ⟨7349021, by rfl⟩ : syracuseStep 9798695 = 14698043) B14698043
theorem B6532463 : Blo 2231435 6532463 := bstep (se 1 (by rfl) ⟨4899347, by rfl⟩ : syracuseStep 6532463 = 9798695) B9798695
theorem B4354975 : Blo 2231435 4354975 := bstep (se 1 (by rfl) ⟨3266231, by rfl⟩ : syracuseStep 4354975 = 6532463) B6532463
theorem B23226533 : Blo 2231435 23226533 := bstep (se 4 (by rfl) ⟨2177487, by rfl⟩ : syracuseStep 23226533 = 4354975) B4354975
theorem B15484355 : Blo 2231435 15484355 := bstep (se 1 (by rfl) ⟨11613266, by rfl⟩ : syracuseStep 15484355 = 23226533) B23226533
theorem B10322903 : Blo 2231435 10322903 := bstep (se 1 (by rfl) ⟨7742177, by rfl⟩ : syracuseStep 10322903 = 15484355) B15484355
theorem B6881935 : Blo 2231435 6881935 := bstep (se 1 (by rfl) ⟨5161451, by rfl⟩ : syracuseStep 6881935 = 10322903) B10322903
theorem B9175913 : Blo 2231435 9175913 := bstep (se 2 (by rfl) ⟨3440967, by rfl⟩ : syracuseStep 9175913 = 6881935) B6881935
theorem B6117275 : Blo 2231435 6117275 := bstep (se 1 (by rfl) ⟨4587956, by rfl⟩ : syracuseStep 6117275 = 9175913) B9175913
theorem B4078183 : Blo 2231435 4078183 := bstep (se 1 (by rfl) ⟨3058637, by rfl⟩ : syracuseStep 4078183 = 6117275) B6117275
theorem B5437577 : Blo 2231435 5437577 := bstep (se 2 (by rfl) ⟨2039091, by rfl⟩ : syracuseStep 5437577 = 4078183) B4078183
theorem B14500205 : Blo 2231435 14500205 := bstep (se 3 (by rfl) ⟨2718788, by rfl⟩ : syracuseStep 14500205 = 5437577) B5437577
theorem B9666803 : Blo 2231435 9666803 := bstep (se 1 (by rfl) ⟨7250102, by rfl⟩ : syracuseStep 9666803 = 14500205) B14500205
theorem B6444535 : Blo 2231435 6444535 := bstep (se 1 (by rfl) ⟨4833401, by rfl⟩ : syracuseStep 6444535 = 9666803) B9666803
theorem B8592713 : Blo 2231435 8592713 := bstep (se 2 (by rfl) ⟨3222267, by rfl⟩ : syracuseStep 8592713 = 6444535) B6444535
theorem B5728475 : Blo 2231435 5728475 := bstep (se 1 (by rfl) ⟨4296356, by rfl⟩ : syracuseStep 5728475 = 8592713) B8592713
theorem B3818983 : Blo 2231435 3818983 := bstep (se 1 (by rfl) ⟨2864237, by rfl⟩ : syracuseStep 3818983 = 5728475) B5728475
theorem B5091977 : Blo 2231435 5091977 := bstep (se 2 (by rfl) ⟨1909491, by rfl⟩ : syracuseStep 5091977 = 3818983) B3818983
theorem B13578605 : Blo 2231435 13578605 := bstep (se 3 (by rfl) ⟨2545988, by rfl⟩ : syracuseStep 13578605 = 5091977) B5091977
theorem B9052403 : Blo 2231435 9052403 := bstep (se 1 (by rfl) ⟨6789302, by rfl⟩ : syracuseStep 9052403 = 13578605) B13578605
theorem B24139741 : Blo 2231435 24139741 := bstep (se 3 (by rfl) ⟨4526201, by rfl⟩ : syracuseStep 24139741 = 9052403) B9052403
theorem B32186321 : Blo 2231435 32186321 := bstep (se 2 (by rfl) ⟨12069870, by rfl⟩ : syracuseStep 32186321 = 24139741) B24139741
theorem B21457547 : Blo 2231435 21457547 := bstep (se 1 (by rfl) ⟨16093160, by rfl⟩ : syracuseStep 21457547 = 32186321) B32186321
theorem B14305031 : Blo 2231435 14305031 := bstep (se 1 (by rfl) ⟨10728773, by rfl⟩ : syracuseStep 14305031 = 21457547) B21457547
theorem B9536687 : Blo 2231435 9536687 := bstep (se 1 (by rfl) ⟨7152515, by rfl⟩ : syracuseStep 9536687 = 14305031) B14305031
theorem B6357791 : Blo 2231435 6357791 := bstep (se 1 (by rfl) ⟨4768343, by rfl⟩ : syracuseStep 6357791 = 9536687) B9536687
theorem B16954109 : Blo 2231435 16954109 := bstep (se 3 (by rfl) ⟨3178895, by rfl⟩ : syracuseStep 16954109 = 6357791) B6357791
theorem B11302739 : Blo 2231435 11302739 := bstep (se 1 (by rfl) ⟨8477054, by rfl⟩ : syracuseStep 11302739 = 16954109) B16954109
theorem B7535159 : Blo 2231435 7535159 := bstep (se 1 (by rfl) ⟨5651369, by rfl⟩ : syracuseStep 7535159 = 11302739) B11302739
theorem B5023439 : Blo 2231435 5023439 := bstep (se 1 (by rfl) ⟨3767579, by rfl⟩ : syracuseStep 5023439 = 7535159) B7535159
theorem B3348959 : Blo 2231435 3348959 := bstep (se 1 (by rfl) ⟨2511719, by rfl⟩ : syracuseStep 3348959 = 5023439) B5023439
theorem B2232639 : Blo 2231435 2232639 := bstep (se 1 (by rfl) ⟨1674479, by rfl⟩ : syracuseStep 2232639 = 3348959) B3348959
theorem B3348965 : Blo 2231435 3348965 := bbase (se 4 (by rfl) ⟨313965, by rfl⟩ : syracuseStep 3348965 = 627931) (by norm_num)
theorem B2232643 : Blo 2231435 2232643 := bstep (se 1 (by rfl) ⟨1674482, by rfl⟩ : syracuseStep 2232643 = 3348965) B3348965
theorem B5091997 : Blo 2231435 5091997 := bbase (se 3 (by rfl) ⟨954749, by rfl⟩ : syracuseStep 5091997 = 1909499) (by norm_num)
theorem B6789329 : Blo 2231435 6789329 := bstep (se 2 (by rfl) ⟨2545998, by rfl⟩ : syracuseStep 6789329 = 5091997) B5091997
theorem B4526219 : Blo 2231435 4526219 := bstep (se 1 (by rfl) ⟨3394664, by rfl⟩ : syracuseStep 4526219 = 6789329) B6789329
theorem B12069917 : Blo 2231435 12069917 := bstep (se 3 (by rfl) ⟨2263109, by rfl⟩ : syracuseStep 12069917 = 4526219) B4526219
theorem B8046611 : Blo 2231435 8046611 := bstep (se 1 (by rfl) ⟨6034958, by rfl⟩ : syracuseStep 8046611 = 12069917) B12069917
theorem B5364407 : Blo 2231435 5364407 := bstep (se 1 (by rfl) ⟨4023305, by rfl⟩ : syracuseStep 5364407 = 8046611) B8046611
theorem B14305085 : Blo 2231435 14305085 := bstep (se 3 (by rfl) ⟨2682203, by rfl⟩ : syracuseStep 14305085 = 5364407) B5364407
theorem B9536723 : Blo 2231435 9536723 := bstep (se 1 (by rfl) ⟨7152542, by rfl⟩ : syracuseStep 9536723 = 14305085) B14305085
theorem B6357815 : Blo 2231435 6357815 := bstep (se 1 (by rfl) ⟨4768361, by rfl⟩ : syracuseStep 6357815 = 9536723) B9536723
theorem B4238543 : Blo 2231435 4238543 := bstep (se 1 (by rfl) ⟨3178907, by rfl⟩ : syracuseStep 4238543 = 6357815) B6357815
theorem B2825695 : Blo 2231435 2825695 := bstep (se 1 (by rfl) ⟨2119271, by rfl⟩ : syracuseStep 2825695 = 4238543) B4238543
theorem B3767593 : Blo 2231435 3767593 := bstep (se 2 (by rfl) ⟨1412847, by rfl⟩ : syracuseStep 3767593 = 2825695) B2825695
theorem B5023457 : Blo 2231435 5023457 := bstep (se 2 (by rfl) ⟨1883796, by rfl⟩ : syracuseStep 5023457 = 3767593) B3767593
theorem B3348971 : Blo 2231435 3348971 := bstep (se 1 (by rfl) ⟨2511728, by rfl⟩ : syracuseStep 3348971 = 5023457) B5023457
theorem B2232647 : Blo 2231435 2232647 := bstep (se 1 (by rfl) ⟨1674485, by rfl⟩ : syracuseStep 2232647 = 3348971) B3348971
theorem B2511733 : Blo 2231435 2511733 := bbase (se 5 (by rfl) ⟨117737, by rfl⟩ : syracuseStep 2511733 = 235475) (by norm_num)
theorem B3348977 : Blo 2231435 3348977 := bstep (se 2 (by rfl) ⟨1255866, by rfl⟩ : syracuseStep 3348977 = 2511733) B2511733
theorem B2232651 : Blo 2231435 2232651 := bstep (se 1 (by rfl) ⟨1674488, by rfl⟩ : syracuseStep 2232651 = 3348977) B3348977
theorem B2825705 : Blo 2231435 2825705 := bbase (se 2 (by rfl) ⟨1059639, by rfl⟩ : syracuseStep 2825705 = 2119279) (by norm_num)
theorem B7535213 : Blo 2231435 7535213 := bstep (se 3 (by rfl) ⟨1412852, by rfl⟩ : syracuseStep 7535213 = 2825705) B2825705
theorem B5023475 : Blo 2231435 5023475 := bstep (se 1 (by rfl) ⟨3767606, by rfl⟩ : syracuseStep 5023475 = 7535213) B7535213
theorem B3348983 : Blo 2231435 3348983 := bstep (se 1 (by rfl) ⟨2511737, by rfl⟩ : syracuseStep 3348983 = 5023475) B5023475
theorem B2232655 : Blo 2231435 2232655 := bstep (se 1 (by rfl) ⟨1674491, by rfl⟩ : syracuseStep 2232655 = 3348983) B3348983
theorem B3348989 : Blo 2231435 3348989 := bbase (se 3 (by rfl) ⟨627935, by rfl⟩ : syracuseStep 3348989 = 1255871) (by norm_num)
theorem B2232659 : Blo 2231435 2232659 := bstep (se 1 (by rfl) ⟨1674494, by rfl⟩ : syracuseStep 2232659 = 3348989) B3348989
theorem B5023493 : Blo 2231435 5023493 := bbase (se 4 (by rfl) ⟨470952, by rfl⟩ : syracuseStep 5023493 = 941905) (by norm_num)
theorem B3348995 : Blo 2231435 3348995 := bstep (se 1 (by rfl) ⟨2511746, by rfl⟩ : syracuseStep 3348995 = 5023493) B5023493
theorem B2232663 : Blo 2231435 2232663 := bstep (se 1 (by rfl) ⟨1674497, by rfl⟩ : syracuseStep 2232663 = 3348995) B3348995
theorem B4238581 : Blo 2231435 4238581 := bbase (se 5 (by rfl) ⟨198683, by rfl⟩ : syracuseStep 4238581 = 397367) (by norm_num)
theorem B5651441 : Blo 2231435 5651441 := bstep (se 2 (by rfl) ⟨2119290, by rfl⟩ : syracuseStep 5651441 = 4238581) B4238581
theorem B3767627 : Blo 2231435 3767627 := bstep (se 1 (by rfl) ⟨2825720, by rfl⟩ : syracuseStep 3767627 = 5651441) B5651441
theorem B2511751 : Blo 2231435 2511751 := bstep (se 1 (by rfl) ⟨1883813, by rfl⟩ : syracuseStep 2511751 = 3767627) B3767627
theorem B3349001 : Blo 2231435 3349001 := bstep (se 2 (by rfl) ⟨1255875, by rfl⟩ : syracuseStep 3349001 = 2511751) B2511751
theorem B2232667 : Blo 2231435 2232667 := bstep (se 1 (by rfl) ⟨1674500, by rfl⟩ : syracuseStep 2232667 = 3349001) B3349001
theorem B11302901 : Blo 2231435 11302901 := bbase (se 5 (by rfl) ⟨529823, by rfl⟩ : syracuseStep 11302901 = 1059647) (by norm_num)
theorem B7535267 : Blo 2231435 7535267 := bstep (se 1 (by rfl) ⟨5651450, by rfl⟩ : syracuseStep 7535267 = 11302901) B11302901
theorem B5023511 : Blo 2231435 5023511 := bstep (se 1 (by rfl) ⟨3767633, by rfl⟩ : syracuseStep 5023511 = 7535267) B7535267
theorem B3349007 : Blo 2231435 3349007 := bstep (se 1 (by rfl) ⟨2511755, by rfl⟩ : syracuseStep 3349007 = 5023511) B5023511
theorem B2232671 : Blo 2231435 2232671 := bstep (se 1 (by rfl) ⟨1674503, by rfl⟩ : syracuseStep 2232671 = 3349007) B3349007
theorem B3349013 : Blo 2231435 3349013 := bbase (se 6 (by rfl) ⟨78492, by rfl⟩ : syracuseStep 3349013 = 156985) (by norm_num)
theorem B2232675 : Blo 2231435 2232675 := bstep (se 1 (by rfl) ⟨1674506, by rfl⟩ : syracuseStep 2232675 = 3349013) B3349013
theorem B19073717 : Blo 2231435 19073717 := bbase (se 5 (by rfl) ⟨894080, by rfl⟩ : syracuseStep 19073717 = 1788161) (by norm_num)
theorem B12715811 : Blo 2231435 12715811 := bstep (se 1 (by rfl) ⟨9536858, by rfl⟩ : syracuseStep 12715811 = 19073717) B19073717
theorem B8477207 : Blo 2231435 8477207 := bstep (se 1 (by rfl) ⟨6357905, by rfl⟩ : syracuseStep 8477207 = 12715811) B12715811
theorem B5651471 : Blo 2231435 5651471 := bstep (se 1 (by rfl) ⟨4238603, by rfl⟩ : syracuseStep 5651471 = 8477207) B8477207
theorem B3767647 : Blo 2231435 3767647 := bstep (se 1 (by rfl) ⟨2825735, by rfl⟩ : syracuseStep 3767647 = 5651471) B5651471
theorem B5023529 : Blo 2231435 5023529 := bstep (se 2 (by rfl) ⟨1883823, by rfl⟩ : syracuseStep 5023529 = 3767647) B3767647
theorem B3349019 : Blo 2231435 3349019 := bstep (se 1 (by rfl) ⟨2511764, by rfl⟩ : syracuseStep 3349019 = 5023529) B5023529
theorem B2232679 : Blo 2231435 2232679 := bstep (se 1 (by rfl) ⟨1674509, by rfl⟩ : syracuseStep 2232679 = 3349019) B3349019
theorem B2511769 : Blo 2231435 2511769 := bbase (se 2 (by rfl) ⟨941913, by rfl⟩ : syracuseStep 2511769 = 1883827) (by norm_num)
theorem B3349025 : Blo 2231435 3349025 := bstep (se 2 (by rfl) ⟨1255884, by rfl⟩ : syracuseStep 3349025 = 2511769) B2511769
theorem B2232683 : Blo 2231435 2232683 := bstep (se 1 (by rfl) ⟨1674512, by rfl⟩ : syracuseStep 2232683 = 3349025) B3349025
theorem B8477237 : Blo 2231435 8477237 := bbase (se 5 (by rfl) ⟨397370, by rfl⟩ : syracuseStep 8477237 = 794741) (by norm_num)
theorem B5651491 : Blo 2231435 5651491 := bstep (se 1 (by rfl) ⟨4238618, by rfl⟩ : syracuseStep 5651491 = 8477237) B8477237
theorem B7535321 : Blo 2231435 7535321 := bstep (se 2 (by rfl) ⟨2825745, by rfl⟩ : syracuseStep 7535321 = 5651491) B5651491
theorem B5023547 : Blo 2231435 5023547 := bstep (se 1 (by rfl) ⟨3767660, by rfl⟩ : syracuseStep 5023547 = 7535321) B7535321
theorem B3349031 : Blo 2231435 3349031 := bstep (se 1 (by rfl) ⟨2511773, by rfl⟩ : syracuseStep 3349031 = 5023547) B5023547
theorem B2232687 : Blo 2231435 2232687 := bstep (se 1 (by rfl) ⟨1674515, by rfl⟩ : syracuseStep 2232687 = 3349031) B3349031
theorem B3349037 : Blo 2231435 3349037 := bbase (se 3 (by rfl) ⟨627944, by rfl⟩ : syracuseStep 3349037 = 1255889) (by norm_num)
theorem B2232691 : Blo 2231435 2232691 := bstep (se 1 (by rfl) ⟨1674518, by rfl⟩ : syracuseStep 2232691 = 3349037) B3349037
theorem B5023565 : Blo 2231435 5023565 := bbase (se 3 (by rfl) ⟨941918, by rfl⟩ : syracuseStep 5023565 = 1883837) (by norm_num)
theorem B3349043 : Blo 2231435 3349043 := bstep (se 1 (by rfl) ⟨2511782, by rfl⟩ : syracuseStep 3349043 = 5023565) B5023565
theorem B2232695 : Blo 2231435 2232695 := bstep (se 1 (by rfl) ⟨1674521, by rfl⟩ : syracuseStep 2232695 = 3349043) B3349043
theorem B2825761 : Blo 2231435 2825761 := bbase (se 2 (by rfl) ⟨1059660, by rfl⟩ : syracuseStep 2825761 = 2119321) (by norm_num)
theorem B3767681 : Blo 2231435 3767681 := bstep (se 2 (by rfl) ⟨1412880, by rfl⟩ : syracuseStep 3767681 = 2825761) B2825761
theorem B2511787 : Blo 2231435 2511787 := bstep (se 1 (by rfl) ⟨1883840, by rfl⟩ : syracuseStep 2511787 = 3767681) B3767681
theorem B3349049 : Blo 2231435 3349049 := bstep (se 2 (by rfl) ⟨1255893, by rfl⟩ : syracuseStep 3349049 = 2511787) B2511787
theorem B2232699 : Blo 2231435 2232699 := bstep (se 1 (by rfl) ⟨1674524, by rfl⟩ : syracuseStep 2232699 = 3349049) B3349049
theorem B25431893 : Blo 2231435 25431893 := bbase (se 9 (by rfl) ⟨74507, by rfl⟩ : syracuseStep 25431893 = 149015) (by norm_num)
theorem B16954595 : Blo 2231435 16954595 := bstep (se 1 (by rfl) ⟨12715946, by rfl⟩ : syracuseStep 16954595 = 25431893) B25431893
theorem B11303063 : Blo 2231435 11303063 := bstep (se 1 (by rfl) ⟨8477297, by rfl⟩ : syracuseStep 11303063 = 16954595) B16954595
theorem B7535375 : Blo 2231435 7535375 := bstep (se 1 (by rfl) ⟨5651531, by rfl⟩ : syracuseStep 7535375 = 11303063) B11303063
theorem B5023583 : Blo 2231435 5023583 := bstep (se 1 (by rfl) ⟨3767687, by rfl⟩ : syracuseStep 5023583 = 7535375) B7535375
theorem B3349055 : Blo 2231435 3349055 := bstep (se 1 (by rfl) ⟨2511791, by rfl⟩ : syracuseStep 3349055 = 5023583) B5023583
theorem B2232703 : Blo 2231435 2232703 := bstep (se 1 (by rfl) ⟨1674527, by rfl⟩ : syracuseStep 2232703 = 3349055) B3349055
theorem B3349061 : Blo 2231435 3349061 := bbase (se 4 (by rfl) ⟨313974, by rfl⟩ : syracuseStep 3349061 = 627949) (by norm_num)
theorem B2232707 : Blo 2231435 2232707 := bstep (se 1 (by rfl) ⟨1674530, by rfl⟩ : syracuseStep 2232707 = 3349061) B3349061
theorem B3767701 : Blo 2231435 3767701 := bbase (se 6 (by rfl) ⟨88305, by rfl⟩ : syracuseStep 3767701 = 176611) (by norm_num)
theorem B5023601 : Blo 2231435 5023601 := bstep (se 2 (by rfl) ⟨1883850, by rfl⟩ : syracuseStep 5023601 = 3767701) B3767701
theorem B3349067 : Blo 2231435 3349067 := bstep (se 1 (by rfl) ⟨2511800, by rfl⟩ : syracuseStep 3349067 = 5023601) B5023601
theorem B2232711 : Blo 2231435 2232711 := bstep (se 1 (by rfl) ⟨1674533, by rfl⟩ : syracuseStep 2232711 = 3349067) B3349067
theorem B2511805 : Blo 2231435 2511805 := bbase (se 3 (by rfl) ⟨470963, by rfl⟩ : syracuseStep 2511805 = 941927) (by norm_num)
theorem B3349073 : Blo 2231435 3349073 := bstep (se 2 (by rfl) ⟨1255902, by rfl⟩ : syracuseStep 3349073 = 2511805) B2511805
theorem B2232715 : Blo 2231435 2232715 := bstep (se 1 (by rfl) ⟨1674536, by rfl⟩ : syracuseStep 2232715 = 3349073) B3349073
theorem B7535429 : Blo 2231435 7535429 := bbase (se 4 (by rfl) ⟨706446, by rfl⟩ : syracuseStep 7535429 = 1412893) (by norm_num)
theorem B5023619 : Blo 2231435 5023619 := bstep (se 1 (by rfl) ⟨3767714, by rfl⟩ : syracuseStep 5023619 = 7535429) B7535429
theorem B3349079 : Blo 2231435 3349079 := bstep (se 1 (by rfl) ⟨2511809, by rfl⟩ : syracuseStep 3349079 = 5023619) B5023619
theorem B2232719 : Blo 2231435 2232719 := bstep (se 1 (by rfl) ⟨1674539, by rfl⟩ : syracuseStep 2232719 = 3349079) B3349079
theorem B3349085 : Blo 2231435 3349085 := bbase (se 3 (by rfl) ⟨627953, by rfl⟩ : syracuseStep 3349085 = 1255907) (by norm_num)
theorem B2232723 : Blo 2231435 2232723 := bstep (se 1 (by rfl) ⟨1674542, by rfl⟩ : syracuseStep 2232723 = 3349085) B3349085
theorem B5023637 : Blo 2231435 5023637 := bbase (se 6 (by rfl) ⟨117741, by rfl⟩ : syracuseStep 5023637 = 235483) (by norm_num)
theorem B3349091 : Blo 2231435 3349091 := bstep (se 1 (by rfl) ⟨2511818, by rfl⟩ : syracuseStep 3349091 = 5023637) B5023637
theorem B2232727 : Blo 2231435 2232727 := bstep (se 1 (by rfl) ⟨1674545, by rfl⟩ : syracuseStep 2232727 = 3349091) B3349091
theorem B4768541 : Blo 2231435 4768541 := bbase (se 3 (by rfl) ⟨894101, by rfl⟩ : syracuseStep 4768541 = 1788203) (by norm_num)
theorem B3179027 : Blo 2231435 3179027 := bstep (se 1 (by rfl) ⟨2384270, by rfl⟩ : syracuseStep 3179027 = 4768541) B4768541
theorem B8477405 : Blo 2231435 8477405 := bstep (se 3 (by rfl) ⟨1589513, by rfl⟩ : syracuseStep 8477405 = 3179027) B3179027
theorem B5651603 : Blo 2231435 5651603 := bstep (se 1 (by rfl) ⟨4238702, by rfl⟩ : syracuseStep 5651603 = 8477405) B8477405
theorem B3767735 : Blo 2231435 3767735 := bstep (se 1 (by rfl) ⟨2825801, by rfl⟩ : syracuseStep 3767735 = 5651603) B5651603
theorem B2511823 : Blo 2231435 2511823 := bstep (se 1 (by rfl) ⟨1883867, by rfl⟩ : syracuseStep 2511823 = 3767735) B3767735
theorem B3349097 : Blo 2231435 3349097 := bstep (se 2 (by rfl) ⟨1255911, by rfl⟩ : syracuseStep 3349097 = 2511823) B2511823
theorem B2232731 : Blo 2231435 2232731 := bstep (se 1 (by rfl) ⟨1674548, by rfl⟩ : syracuseStep 2232731 = 3349097) B3349097
theorem B17186165 : Blo 2231435 17186165 := bbase (se 5 (by rfl) ⟨805601, by rfl⟩ : syracuseStep 17186165 = 1611203) (by norm_num)
theorem B11457443 : Blo 2231435 11457443 := bstep (se 1 (by rfl) ⟨8593082, by rfl⟩ : syracuseStep 11457443 = 17186165) B17186165
theorem B7638295 : Blo 2231435 7638295 := bstep (se 1 (by rfl) ⟨5728721, by rfl⟩ : syracuseStep 7638295 = 11457443) B11457443
theorem B10184393 : Blo 2231435 10184393 := bstep (se 2 (by rfl) ⟨3819147, by rfl⟩ : syracuseStep 10184393 = 7638295) B7638295
theorem B6789595 : Blo 2231435 6789595 := bstep (se 1 (by rfl) ⟨5092196, by rfl⟩ : syracuseStep 6789595 = 10184393) B10184393
theorem B9052793 : Blo 2231435 9052793 := bstep (se 2 (by rfl) ⟨3394797, by rfl⟩ : syracuseStep 9052793 = 6789595) B6789595
theorem B6035195 : Blo 2231435 6035195 := bstep (se 1 (by rfl) ⟨4526396, by rfl⟩ : syracuseStep 6035195 = 9052793) B9052793
theorem B16093853 : Blo 2231435 16093853 := bstep (se 3 (by rfl) ⟨3017597, by rfl⟩ : syracuseStep 16093853 = 6035195) B6035195
theorem B10729235 : Blo 2231435 10729235 := bstep (se 1 (by rfl) ⟨8046926, by rfl⟩ : syracuseStep 10729235 = 16093853) B16093853
theorem B7152823 : Blo 2231435 7152823 := bstep (se 1 (by rfl) ⟨5364617, by rfl⟩ : syracuseStep 7152823 = 10729235) B10729235
theorem B9537097 : Blo 2231435 9537097 := bstep (se 2 (by rfl) ⟨3576411, by rfl⟩ : syracuseStep 9537097 = 7152823) B7152823
theorem B12716129 : Blo 2231435 12716129 := bstep (se 2 (by rfl) ⟨4768548, by rfl⟩ : syracuseStep 12716129 = 9537097) B9537097
theorem B8477419 : Blo 2231435 8477419 := bstep (se 1 (by rfl) ⟨6358064, by rfl⟩ : syracuseStep 8477419 = 12716129) B12716129
theorem B11303225 : Blo 2231435 11303225 := bstep (se 2 (by rfl) ⟨4238709, by rfl⟩ : syracuseStep 11303225 = 8477419) B8477419
theorem B7535483 : Blo 2231435 7535483 := bstep (se 1 (by rfl) ⟨5651612, by rfl⟩ : syracuseStep 7535483 = 11303225) B11303225
theorem B5023655 : Blo 2231435 5023655 := bstep (se 1 (by rfl) ⟨3767741, by rfl⟩ : syracuseStep 5023655 = 7535483) B7535483
theorem B3349103 : Blo 2231435 3349103 := bstep (se 1 (by rfl) ⟨2511827, by rfl⟩ : syracuseStep 3349103 = 5023655) B5023655
theorem B2232735 : Blo 2231435 2232735 := bstep (se 1 (by rfl) ⟨1674551, by rfl⟩ : syracuseStep 2232735 = 3349103) B3349103
theorem B3349109 : Blo 2231435 3349109 := bbase (se 5 (by rfl) ⟨156989, by rfl⟩ : syracuseStep 3349109 = 313979) (by norm_num)
theorem B2232739 : Blo 2231435 2232739 := bstep (se 1 (by rfl) ⟨1674554, by rfl⟩ : syracuseStep 2232739 = 3349109) B3349109
theorem B4238725 : Blo 2231435 4238725 := bbase (se 4 (by rfl) ⟨397380, by rfl⟩ : syracuseStep 4238725 = 794761) (by norm_num)
theorem B5651633 : Blo 2231435 5651633 := bstep (se 2 (by rfl) ⟨2119362, by rfl⟩ : syracuseStep 5651633 = 4238725) B4238725
theorem B3767755 : Blo 2231435 3767755 := bstep (se 1 (by rfl) ⟨2825816, by rfl⟩ : syracuseStep 3767755 = 5651633) B5651633
theorem B5023673 : Blo 2231435 5023673 := bstep (se 2 (by rfl) ⟨1883877, by rfl⟩ : syracuseStep 5023673 = 3767755) B3767755
theorem B3349115 : Blo 2231435 3349115 := bstep (se 1 (by rfl) ⟨2511836, by rfl⟩ : syracuseStep 3349115 = 5023673) B5023673
theorem B2232743 : Blo 2231435 2232743 := bstep (se 1 (by rfl) ⟨1674557, by rfl⟩ : syracuseStep 2232743 = 3349115) B3349115
theorem B2511841 : Blo 2231435 2511841 := bbase (se 2 (by rfl) ⟨941940, by rfl⟩ : syracuseStep 2511841 = 1883881) (by norm_num)
theorem B3349121 : Blo 2231435 3349121 := bstep (se 2 (by rfl) ⟨1255920, by rfl⟩ : syracuseStep 3349121 = 2511841) B2511841
theorem B2232747 : Blo 2231435 2232747 := bstep (se 1 (by rfl) ⟨1674560, by rfl⟩ : syracuseStep 2232747 = 3349121) B3349121
theorem B5651653 : Blo 2231435 5651653 := bbase (se 4 (by rfl) ⟨529842, by rfl⟩ : syracuseStep 5651653 = 1059685) (by norm_num)
theorem B7535537 : Blo 2231435 7535537 := bstep (se 2 (by rfl) ⟨2825826, by rfl⟩ : syracuseStep 7535537 = 5651653) B5651653
theorem B5023691 : Blo 2231435 5023691 := bstep (se 1 (by rfl) ⟨3767768, by rfl⟩ : syracuseStep 5023691 = 7535537) B7535537
theorem B3349127 : Blo 2231435 3349127 := bstep (se 1 (by rfl) ⟨2511845, by rfl⟩ : syracuseStep 3349127 = 5023691) B5023691
theorem B2232751 : Blo 2231435 2232751 := bstep (se 1 (by rfl) ⟨1674563, by rfl⟩ : syracuseStep 2232751 = 3349127) B3349127
theorem B3349133 : Blo 2231435 3349133 := bbase (se 3 (by rfl) ⟨627962, by rfl⟩ : syracuseStep 3349133 = 1255925) (by norm_num)
theorem B2232755 : Blo 2231435 2232755 := bstep (se 1 (by rfl) ⟨1674566, by rfl⟩ : syracuseStep 2232755 = 3349133) B3349133
theorem B5023709 : Blo 2231435 5023709 := bbase (se 3 (by rfl) ⟨941945, by rfl⟩ : syracuseStep 5023709 = 1883891) (by norm_num)
theorem B3349139 : Blo 2231435 3349139 := bstep (se 1 (by rfl) ⟨2511854, by rfl⟩ : syracuseStep 3349139 = 5023709) B5023709
theorem B2232759 : Blo 2231435 2232759 := bstep (se 1 (by rfl) ⟨1674569, by rfl⟩ : syracuseStep 2232759 = 3349139) B3349139
theorem B3767789 : Blo 2231435 3767789 := bbase (se 3 (by rfl) ⟨706460, by rfl⟩ : syracuseStep 3767789 = 1412921) (by norm_num)
theorem B2511859 : Blo 2231435 2511859 := bstep (se 1 (by rfl) ⟨1883894, by rfl⟩ : syracuseStep 2511859 = 3767789) B3767789
theorem B3349145 : Blo 2231435 3349145 := bstep (se 2 (by rfl) ⟨1255929, by rfl⟩ : syracuseStep 3349145 = 2511859) B2511859
theorem B2232763 : Blo 2231435 2232763 := bstep (se 1 (by rfl) ⟨1674572, by rfl⟩ : syracuseStep 2232763 = 3349145) B3349145
theorem B12889813 : Blo 2231435 12889813 := bbase (se 7 (by rfl) ⟨151052, by rfl⟩ : syracuseStep 12889813 = 302105) (by norm_num)
theorem B17186417 : Blo 2231435 17186417 := bstep (se 2 (by rfl) ⟨6444906, by rfl⟩ : syracuseStep 17186417 = 12889813) B12889813
theorem B11457611 : Blo 2231435 11457611 := bstep (se 1 (by rfl) ⟨8593208, by rfl⟩ : syracuseStep 11457611 = 17186417) B17186417
theorem B7638407 : Blo 2231435 7638407 := bstep (se 1 (by rfl) ⟨5728805, by rfl⟩ : syracuseStep 7638407 = 11457611) B11457611
theorem B5092271 : Blo 2231435 5092271 := bstep (se 1 (by rfl) ⟨3819203, by rfl⟩ : syracuseStep 5092271 = 7638407) B7638407
theorem B3394847 : Blo 2231435 3394847 := bstep (se 1 (by rfl) ⟨2546135, by rfl⟩ : syracuseStep 3394847 = 5092271) B5092271
theorem B2263231 : Blo 2231435 2263231 := bstep (se 1 (by rfl) ⟨1697423, by rfl⟩ : syracuseStep 2263231 = 3394847) B3394847
theorem B3017641 : Blo 2231435 3017641 := bstep (se 2 (by rfl) ⟨1131615, by rfl⟩ : syracuseStep 3017641 = 2263231) B2263231
theorem B4023521 : Blo 2231435 4023521 := bstep (se 2 (by rfl) ⟨1508820, by rfl⟩ : syracuseStep 4023521 = 3017641) B3017641
theorem B2682347 : Blo 2231435 2682347 := bstep (se 1 (by rfl) ⟨2011760, by rfl⟩ : syracuseStep 2682347 = 4023521) B4023521
theorem B28611701 : Blo 2231435 28611701 := bstep (se 5 (by rfl) ⟨1341173, by rfl⟩ : syracuseStep 28611701 = 2682347) B2682347
theorem B19074467 : Blo 2231435 19074467 := bstep (se 1 (by rfl) ⟨14305850, by rfl⟩ : syracuseStep 19074467 = 28611701) B28611701
theorem B12716311 : Blo 2231435 12716311 := bstep (se 1 (by rfl) ⟨9537233, by rfl⟩ : syracuseStep 12716311 = 19074467) B19074467
theorem B16955081 : Blo 2231435 16955081 := bstep (se 2 (by rfl) ⟨6358155, by rfl⟩ : syracuseStep 16955081 = 12716311) B12716311
theorem B11303387 : Blo 2231435 11303387 := bstep (se 1 (by rfl) ⟨8477540, by rfl⟩ : syracuseStep 11303387 = 16955081) B16955081
theorem B7535591 : Blo 2231435 7535591 := bstep (se 1 (by rfl) ⟨5651693, by rfl⟩ : syracuseStep 7535591 = 11303387) B11303387
theorem B5023727 : Blo 2231435 5023727 := bstep (se 1 (by rfl) ⟨3767795, by rfl⟩ : syracuseStep 5023727 = 7535591) B7535591
theorem B3349151 : Blo 2231435 3349151 := bstep (se 1 (by rfl) ⟨2511863, by rfl⟩ : syracuseStep 3349151 = 5023727) B5023727
theorem B2232767 : Blo 2231435 2232767 := bstep (se 1 (by rfl) ⟨1674575, by rfl⟩ : syracuseStep 2232767 = 3349151) B3349151
theorem B3349157 : Blo 2231435 3349157 := bbase (se 4 (by rfl) ⟨313983, by rfl⟩ : syracuseStep 3349157 = 627967) (by norm_num)
theorem B2232771 : Blo 2231435 2232771 := bstep (se 1 (by rfl) ⟨1674578, by rfl⟩ : syracuseStep 2232771 = 3349157) B3349157
theorem B2825857 : Blo 2231435 2825857 := bbase (se 2 (by rfl) ⟨1059696, by rfl⟩ : syracuseStep 2825857 = 2119393) (by norm_num)
theorem B3767809 : Blo 2231435 3767809 := bstep (se 2 (by rfl) ⟨1412928, by rfl⟩ : syracuseStep 3767809 = 2825857) B2825857
theorem B5023745 : Blo 2231435 5023745 := bstep (se 2 (by rfl) ⟨1883904, by rfl⟩ : syracuseStep 5023745 = 3767809) B3767809
theorem B3349163 : Blo 2231435 3349163 := bstep (se 1 (by rfl) ⟨2511872, by rfl⟩ : syracuseStep 3349163 = 5023745) B5023745
theorem B2232775 : Blo 2231435 2232775 := bstep (se 1 (by rfl) ⟨1674581, by rfl⟩ : syracuseStep 2232775 = 3349163) B3349163
theorem B2511877 : Blo 2231435 2511877 := bbase (se 4 (by rfl) ⟨235488, by rfl⟩ : syracuseStep 2511877 = 470977) (by norm_num)
theorem B3349169 : Blo 2231435 3349169 := bstep (se 2 (by rfl) ⟨1255938, by rfl⟩ : syracuseStep 3349169 = 2511877) B2511877
theorem B2232779 : Blo 2231435 2232779 := bstep (se 1 (by rfl) ⟨1674584, by rfl⟩ : syracuseStep 2232779 = 3349169) B3349169
theorem B3179101 : Blo 2231435 3179101 := bbase (se 3 (by rfl) ⟨596081, by rfl⟩ : syracuseStep 3179101 = 1192163) (by norm_num)
theorem B4238801 : Blo 2231435 4238801 := bstep (se 2 (by rfl) ⟨1589550, by rfl⟩ : syracuseStep 4238801 = 3179101) B3179101
theorem B2825867 : Blo 2231435 2825867 := bstep (se 1 (by rfl) ⟨2119400, by rfl⟩ : syracuseStep 2825867 = 4238801) B4238801
theorem B7535645 : Blo 2231435 7535645 := bstep (se 3 (by rfl) ⟨1412933, by rfl⟩ : syracuseStep 7535645 = 2825867) B2825867
theorem B5023763 : Blo 2231435 5023763 := bstep (se 1 (by rfl) ⟨3767822, by rfl⟩ : syracuseStep 5023763 = 7535645) B7535645
theorem B3349175 : Blo 2231435 3349175 := bstep (se 1 (by rfl) ⟨2511881, by rfl⟩ : syracuseStep 3349175 = 5023763) B5023763
theorem B2232783 : Blo 2231435 2232783 := bstep (se 1 (by rfl) ⟨1674587, by rfl⟩ : syracuseStep 2232783 = 3349175) B3349175
theorem B3349181 : Blo 2231435 3349181 := bbase (se 3 (by rfl) ⟨627971, by rfl⟩ : syracuseStep 3349181 = 1255943) (by norm_num)
theorem B2232787 : Blo 2231435 2232787 := bstep (se 1 (by rfl) ⟨1674590, by rfl⟩ : syracuseStep 2232787 = 3349181) B3349181
theorem B5023781 : Blo 2231435 5023781 := bbase (se 4 (by rfl) ⟨470979, by rfl⟩ : syracuseStep 5023781 = 941959) (by norm_num)
theorem B3349187 : Blo 2231435 3349187 := bstep (se 1 (by rfl) ⟨2511890, by rfl⟩ : syracuseStep 3349187 = 5023781) B5023781
theorem B2232791 : Blo 2231435 2232791 := bstep (se 1 (by rfl) ⟨1674593, by rfl⟩ : syracuseStep 2232791 = 3349187) B3349187
theorem B5651765 : Blo 2231435 5651765 := bbase (se 5 (by rfl) ⟨264926, by rfl⟩ : syracuseStep 5651765 = 529853) (by norm_num)
theorem B3767843 : Blo 2231435 3767843 := bstep (se 1 (by rfl) ⟨2825882, by rfl⟩ : syracuseStep 3767843 = 5651765) B5651765
theorem B2511895 : Blo 2231435 2511895 := bstep (se 1 (by rfl) ⟨1883921, by rfl⟩ : syracuseStep 2511895 = 3767843) B3767843
theorem B3349193 : Blo 2231435 3349193 := bstep (se 2 (by rfl) ⟨1255947, by rfl⟩ : syracuseStep 3349193 = 2511895) B2511895
theorem B2232795 : Blo 2231435 2232795 := bstep (se 1 (by rfl) ⟨1674596, by rfl⟩ : syracuseStep 2232795 = 3349193) B3349193
theorem B22915541 : Blo 2231435 22915541 := bbase (se 7 (by rfl) ⟨268541, by rfl⟩ : syracuseStep 22915541 = 537083) (by norm_num)
theorem B15277027 : Blo 2231435 15277027 := bstep (se 1 (by rfl) ⟨11457770, by rfl⟩ : syracuseStep 15277027 = 22915541) B22915541
theorem B20369369 : Blo 2231435 20369369 := bstep (se 2 (by rfl) ⟨7638513, by rfl⟩ : syracuseStep 20369369 = 15277027) B15277027
theorem B13579579 : Blo 2231435 13579579 := bstep (se 1 (by rfl) ⟨10184684, by rfl⟩ : syracuseStep 13579579 = 20369369) B20369369
theorem B18106105 : Blo 2231435 18106105 := bstep (se 2 (by rfl) ⟨6789789, by rfl⟩ : syracuseStep 18106105 = 13579579) B13579579
theorem B24141473 : Blo 2231435 24141473 := bstep (se 2 (by rfl) ⟨9053052, by rfl⟩ : syracuseStep 24141473 = 18106105) B18106105
theorem B16094315 : Blo 2231435 16094315 := bstep (se 1 (by rfl) ⟨12070736, by rfl⟩ : syracuseStep 16094315 = 24141473) B24141473
theorem B10729543 : Blo 2231435 10729543 := bstep (se 1 (by rfl) ⟨8047157, by rfl⟩ : syracuseStep 10729543 = 16094315) B16094315
theorem B14306057 : Blo 2231435 14306057 := bstep (se 2 (by rfl) ⟨5364771, by rfl⟩ : syracuseStep 14306057 = 10729543) B10729543
theorem B9537371 : Blo 2231435 9537371 := bstep (se 1 (by rfl) ⟨7153028, by rfl⟩ : syracuseStep 9537371 = 14306057) B14306057
theorem B6358247 : Blo 2231435 6358247 := bstep (se 1 (by rfl) ⟨4768685, by rfl⟩ : syracuseStep 6358247 = 9537371) B9537371
theorem B4238831 : Blo 2231435 4238831 := bstep (se 1 (by rfl) ⟨3179123, by rfl⟩ : syracuseStep 4238831 = 6358247) B6358247
theorem B11303549 : Blo 2231435 11303549 := bstep (se 3 (by rfl) ⟨2119415, by rfl⟩ : syracuseStep 11303549 = 4238831) B4238831
theorem B7535699 : Blo 2231435 7535699 := bstep (se 1 (by rfl) ⟨5651774, by rfl⟩ : syracuseStep 7535699 = 11303549) B11303549
theorem B5023799 : Blo 2231435 5023799 := bstep (se 1 (by rfl) ⟨3767849, by rfl⟩ : syracuseStep 5023799 = 7535699) B7535699
theorem B3349199 : Blo 2231435 3349199 := bstep (se 1 (by rfl) ⟨2511899, by rfl⟩ : syracuseStep 3349199 = 5023799) B5023799
theorem B2232799 : Blo 2231435 2232799 := bstep (se 1 (by rfl) ⟨1674599, by rfl⟩ : syracuseStep 2232799 = 3349199) B3349199
theorem B3349205 : Blo 2231435 3349205 := bbase (se 7 (by rfl) ⟨39248, by rfl⟩ : syracuseStep 3349205 = 78497) (by norm_num)
theorem B2232803 : Blo 2231435 2232803 := bstep (se 1 (by rfl) ⟨1674602, by rfl⟩ : syracuseStep 2232803 = 3349205) B3349205
theorem B5807069 : Blo 2231435 5807069 := bbase (se 3 (by rfl) ⟨1088825, by rfl⟩ : syracuseStep 5807069 = 2177651) (by norm_num)
theorem B3871379 : Blo 2231435 3871379 := bstep (se 1 (by rfl) ⟨2903534, by rfl⟩ : syracuseStep 3871379 = 5807069) B5807069
theorem B2580919 : Blo 2231435 2580919 := bstep (se 1 (by rfl) ⟨1935689, by rfl⟩ : syracuseStep 2580919 = 3871379) B3871379
theorem B55059605 : Blo 2231435 55059605 := bstep (se 6 (by rfl) ⟨1290459, by rfl⟩ : syracuseStep 55059605 = 2580919) B2580919
theorem B36706403 : Blo 2231435 36706403 := bstep (se 1 (by rfl) ⟨27529802, by rfl⟩ : syracuseStep 36706403 = 55059605) B55059605
theorem B97883741 : Blo 2231435 97883741 := bstep (se 3 (by rfl) ⟨18353201, by rfl⟩ : syracuseStep 97883741 = 36706403) B36706403
theorem B65255827 : Blo 2231435 65255827 := bstep (se 1 (by rfl) ⟨48941870, by rfl⟩ : syracuseStep 65255827 = 97883741) B97883741
theorem B87007769 : Blo 2231435 87007769 := bstep (se 2 (by rfl) ⟨32627913, by rfl⟩ : syracuseStep 87007769 = 65255827) B65255827
theorem B58005179 : Blo 2231435 58005179 := bstep (se 1 (by rfl) ⟨43503884, by rfl⟩ : syracuseStep 58005179 = 87007769) B87007769
theorem B38670119 : Blo 2231435 38670119 := bstep (se 1 (by rfl) ⟨29002589, by rfl⟩ : syracuseStep 38670119 = 58005179) B58005179
theorem B25780079 : Blo 2231435 25780079 := bstep (se 1 (by rfl) ⟨19335059, by rfl⟩ : syracuseStep 25780079 = 38670119) B38670119
theorem B68746877 : Blo 2231435 68746877 := bstep (se 3 (by rfl) ⟨12890039, by rfl⟩ : syracuseStep 68746877 = 25780079) B25780079
theorem B45831251 : Blo 2231435 45831251 := bstep (se 1 (by rfl) ⟨34373438, by rfl⟩ : syracuseStep 45831251 = 68746877) B68746877
theorem B30554167 : Blo 2231435 30554167 := bstep (se 1 (by rfl) ⟨22915625, by rfl⟩ : syracuseStep 30554167 = 45831251) B45831251
theorem B40738889 : Blo 2231435 40738889 := bstep (se 2 (by rfl) ⟨15277083, by rfl⟩ : syracuseStep 40738889 = 30554167) B30554167
theorem B27159259 : Blo 2231435 27159259 := bstep (se 1 (by rfl) ⟨20369444, by rfl⟩ : syracuseStep 27159259 = 40738889) B40738889
theorem B36212345 : Blo 2231435 36212345 := bstep (se 2 (by rfl) ⟨13579629, by rfl⟩ : syracuseStep 36212345 = 27159259) B27159259
theorem B24141563 : Blo 2231435 24141563 := bstep (se 1 (by rfl) ⟨18106172, by rfl⟩ : syracuseStep 24141563 = 36212345) B36212345
theorem B16094375 : Blo 2231435 16094375 := bstep (se 1 (by rfl) ⟨12070781, by rfl⟩ : syracuseStep 16094375 = 24141563) B24141563
theorem B10729583 : Blo 2231435 10729583 := bstep (se 1 (by rfl) ⟨8047187, by rfl⟩ : syracuseStep 10729583 = 16094375) B16094375
theorem B7153055 : Blo 2231435 7153055 := bstep (se 1 (by rfl) ⟨5364791, by rfl⟩ : syracuseStep 7153055 = 10729583) B10729583
theorem B4768703 : Blo 2231435 4768703 := bstep (se 1 (by rfl) ⟨3576527, by rfl⟩ : syracuseStep 4768703 = 7153055) B7153055
theorem B3179135 : Blo 2231435 3179135 := bstep (se 1 (by rfl) ⟨2384351, by rfl⟩ : syracuseStep 3179135 = 4768703) B4768703
theorem B8477693 : Blo 2231435 8477693 := bstep (se 3 (by rfl) ⟨1589567, by rfl⟩ : syracuseStep 8477693 = 3179135) B3179135
theorem B5651795 : Blo 2231435 5651795 := bstep (se 1 (by rfl) ⟨4238846, by rfl⟩ : syracuseStep 5651795 = 8477693) B8477693
theorem B3767863 : Blo 2231435 3767863 := bstep (se 1 (by rfl) ⟨2825897, by rfl⟩ : syracuseStep 3767863 = 5651795) B5651795
theorem B5023817 : Blo 2231435 5023817 := bstep (se 2 (by rfl) ⟨1883931, by rfl⟩ : syracuseStep 5023817 = 3767863) B3767863
theorem B3349211 : Blo 2231435 3349211 := bstep (se 1 (by rfl) ⟨2511908, by rfl⟩ : syracuseStep 3349211 = 5023817) B5023817
theorem B2232807 : Blo 2231435 2232807 := bstep (se 1 (by rfl) ⟨1674605, by rfl⟩ : syracuseStep 2232807 = 3349211) B3349211
theorem B2511913 : Blo 2231435 2511913 := bbase (se 2 (by rfl) ⟨941967, by rfl⟩ : syracuseStep 2511913 = 1883935) (by norm_num)
theorem B3349217 : Blo 2231435 3349217 := bstep (se 2 (by rfl) ⟨1255956, by rfl⟩ : syracuseStep 3349217 = 2511913) B2511913
theorem B2232811 : Blo 2231435 2232811 := bstep (se 1 (by rfl) ⟨1674608, by rfl⟩ : syracuseStep 2232811 = 3349217) B3349217
theorem B19335125 : Blo 2231435 19335125 := bbase (se 7 (by rfl) ⟨226583, by rfl⟩ : syracuseStep 19335125 = 453167) (by norm_num)
theorem B51560333 : Blo 2231435 51560333 := bstep (se 3 (by rfl) ⟨9667562, by rfl⟩ : syracuseStep 51560333 = 19335125) B19335125
theorem B34373555 : Blo 2231435 34373555 := bstep (se 1 (by rfl) ⟨25780166, by rfl⟩ : syracuseStep 34373555 = 51560333) B51560333
theorem B22915703 : Blo 2231435 22915703 := bstep (se 1 (by rfl) ⟨17186777, by rfl⟩ : syracuseStep 22915703 = 34373555) B34373555
theorem B15277135 : Blo 2231435 15277135 := bstep (se 1 (by rfl) ⟨11457851, by rfl⟩ : syracuseStep 15277135 = 22915703) B22915703
theorem B20369513 : Blo 2231435 20369513 := bstep (se 2 (by rfl) ⟨7638567, by rfl⟩ : syracuseStep 20369513 = 15277135) B15277135
theorem B54318701 : Blo 2231435 54318701 := bstep (se 3 (by rfl) ⟨10184756, by rfl⟩ : syracuseStep 54318701 = 20369513) B20369513
theorem B36212467 : Blo 2231435 36212467 := bstep (se 1 (by rfl) ⟨27159350, by rfl⟩ : syracuseStep 36212467 = 54318701) B54318701
theorem B48283289 : Blo 2231435 48283289 := bstep (se 2 (by rfl) ⟨18106233, by rfl⟩ : syracuseStep 48283289 = 36212467) B36212467
theorem B32188859 : Blo 2231435 32188859 := bstep (se 1 (by rfl) ⟨24141644, by rfl⟩ : syracuseStep 32188859 = 48283289) B48283289
theorem B21459239 : Blo 2231435 21459239 := bstep (se 1 (by rfl) ⟨16094429, by rfl⟩ : syracuseStep 21459239 = 32188859) B32188859
theorem B14306159 : Blo 2231435 14306159 := bstep (se 1 (by rfl) ⟨10729619, by rfl⟩ : syracuseStep 14306159 = 21459239) B21459239
theorem B9537439 : Blo 2231435 9537439 := bstep (se 1 (by rfl) ⟨7153079, by rfl⟩ : syracuseStep 9537439 = 14306159) B14306159
theorem B12716585 : Blo 2231435 12716585 := bstep (se 2 (by rfl) ⟨4768719, by rfl⟩ : syracuseStep 12716585 = 9537439) B9537439
theorem B8477723 : Blo 2231435 8477723 := bstep (se 1 (by rfl) ⟨6358292, by rfl⟩ : syracuseStep 8477723 = 12716585) B12716585
theorem B5651815 : Blo 2231435 5651815 := bstep (se 1 (by rfl) ⟨4238861, by rfl⟩ : syracuseStep 5651815 = 8477723) B8477723
theorem B7535753 : Blo 2231435 7535753 := bstep (se 2 (by rfl) ⟨2825907, by rfl⟩ : syracuseStep 7535753 = 5651815) B5651815
theorem B5023835 : Blo 2231435 5023835 := bstep (se 1 (by rfl) ⟨3767876, by rfl⟩ : syracuseStep 5023835 = 7535753) B7535753
theorem B3349223 : Blo 2231435 3349223 := bstep (se 1 (by rfl) ⟨2511917, by rfl⟩ : syracuseStep 3349223 = 5023835) B5023835
theorem B2232815 : Blo 2231435 2232815 := bstep (se 1 (by rfl) ⟨1674611, by rfl⟩ : syracuseStep 2232815 = 3349223) B3349223
theorem B3349229 : Blo 2231435 3349229 := bbase (se 3 (by rfl) ⟨627980, by rfl⟩ : syracuseStep 3349229 = 1255961) (by norm_num)
theorem B2232819 : Blo 2231435 2232819 := bstep (se 1 (by rfl) ⟨1674614, by rfl⟩ : syracuseStep 2232819 = 3349229) B3349229
theorem B5023853 : Blo 2231435 5023853 := bbase (se 3 (by rfl) ⟨941972, by rfl⟩ : syracuseStep 5023853 = 1883945) (by norm_num)
theorem B3349235 : Blo 2231435 3349235 := bstep (se 1 (by rfl) ⟨2511926, by rfl⟩ : syracuseStep 3349235 = 5023853) B5023853
theorem B2232823 : Blo 2231435 2232823 := bstep (se 1 (by rfl) ⟨1674617, by rfl⟩ : syracuseStep 2232823 = 3349235) B3349235
theorem B4238885 : Blo 2231435 4238885 := bbase (se 4 (by rfl) ⟨397395, by rfl⟩ : syracuseStep 4238885 = 794791) (by norm_num)
theorem B2825923 : Blo 2231435 2825923 := bstep (se 1 (by rfl) ⟨2119442, by rfl⟩ : syracuseStep 2825923 = 4238885) B4238885
theorem B3767897 : Blo 2231435 3767897 := bstep (se 2 (by rfl) ⟨1412961, by rfl⟩ : syracuseStep 3767897 = 2825923) B2825923
theorem B2511931 : Blo 2231435 2511931 := bstep (se 1 (by rfl) ⟨1883948, by rfl⟩ : syracuseStep 2511931 = 3767897) B3767897
theorem B3349241 : Blo 2231435 3349241 := bstep (se 2 (by rfl) ⟨1255965, by rfl⟩ : syracuseStep 3349241 = 2511931) B2511931
theorem B2232827 : Blo 2231435 2232827 := bstep (se 1 (by rfl) ⟨1674620, by rfl⟩ : syracuseStep 2232827 = 3349241) B3349241
theorem B6201269 : Blo 2231435 6201269 := bbase (se 5 (by rfl) ⟨290684, by rfl⟩ : syracuseStep 6201269 = 581369) (by norm_num)
theorem B4134179 : Blo 2231435 4134179 := bstep (se 1 (by rfl) ⟨3100634, by rfl⟩ : syracuseStep 4134179 = 6201269) B6201269
theorem B2756119 : Blo 2231435 2756119 := bstep (se 1 (by rfl) ⟨2067089, by rfl⟩ : syracuseStep 2756119 = 4134179) B4134179
theorem B3674825 : Blo 2231435 3674825 := bstep (se 2 (by rfl) ⟨1378059, by rfl⟩ : syracuseStep 3674825 = 2756119) B2756119
theorem B2449883 : Blo 2231435 2449883 := bstep (se 1 (by rfl) ⟨1837412, by rfl⟩ : syracuseStep 2449883 = 3674825) B3674825
theorem B6533021 : Blo 2231435 6533021 := bstep (se 3 (by rfl) ⟨1224941, by rfl⟩ : syracuseStep 6533021 = 2449883) B2449883
theorem B17421389 : Blo 2231435 17421389 := bstep (se 3 (by rfl) ⟨3266510, by rfl⟩ : syracuseStep 17421389 = 6533021) B6533021
theorem B11614259 : Blo 2231435 11614259 := bstep (se 1 (by rfl) ⟨8710694, by rfl⟩ : syracuseStep 11614259 = 17421389) B17421389
theorem B7742839 : Blo 2231435 7742839 := bstep (se 1 (by rfl) ⟨5807129, by rfl⟩ : syracuseStep 7742839 = 11614259) B11614259
theorem B10323785 : Blo 2231435 10323785 := bstep (se 2 (by rfl) ⟨3871419, by rfl⟩ : syracuseStep 10323785 = 7742839) B7742839
theorem B27530093 : Blo 2231435 27530093 := bstep (se 3 (by rfl) ⟨5161892, by rfl⟩ : syracuseStep 27530093 = 10323785) B10323785
theorem B18353395 : Blo 2231435 18353395 := bstep (se 1 (by rfl) ⟨13765046, by rfl⟩ : syracuseStep 18353395 = 27530093) B27530093
theorem B24471193 : Blo 2231435 24471193 := bstep (se 2 (by rfl) ⟨9176697, by rfl⟩ : syracuseStep 24471193 = 18353395) B18353395
theorem B32628257 : Blo 2231435 32628257 := bstep (se 2 (by rfl) ⟨12235596, by rfl⟩ : syracuseStep 32628257 = 24471193) B24471193
theorem B21752171 : Blo 2231435 21752171 := bstep (se 1 (by rfl) ⟨16314128, by rfl⟩ : syracuseStep 21752171 = 32628257) B32628257
theorem B14501447 : Blo 2231435 14501447 := bstep (se 1 (by rfl) ⟨10876085, by rfl⟩ : syracuseStep 14501447 = 21752171) B21752171
theorem B9667631 : Blo 2231435 9667631 := bstep (se 1 (by rfl) ⟨7250723, by rfl⟩ : syracuseStep 9667631 = 14501447) B14501447
theorem B25780349 : Blo 2231435 25780349 := bstep (se 3 (by rfl) ⟨4833815, by rfl⟩ : syracuseStep 25780349 = 9667631) B9667631
theorem B17186899 : Blo 2231435 17186899 := bstep (se 1 (by rfl) ⟨12890174, by rfl⟩ : syracuseStep 17186899 = 25780349) B25780349
theorem B22915865 : Blo 2231435 22915865 := bstep (se 2 (by rfl) ⟨8593449, by rfl⟩ : syracuseStep 22915865 = 17186899) B17186899
theorem B15277243 : Blo 2231435 15277243 := bstep (se 1 (by rfl) ⟨11457932, by rfl⟩ : syracuseStep 15277243 = 22915865) B22915865
theorem B20369657 : Blo 2231435 20369657 := bstep (se 2 (by rfl) ⟨7638621, by rfl⟩ : syracuseStep 20369657 = 15277243) B15277243
theorem B54319085 : Blo 2231435 54319085 := bstep (se 3 (by rfl) ⟨10184828, by rfl⟩ : syracuseStep 54319085 = 20369657) B20369657
theorem B36212723 : Blo 2231435 36212723 := bstep (se 1 (by rfl) ⟨27159542, by rfl⟩ : syracuseStep 36212723 = 54319085) B54319085
theorem B24141815 : Blo 2231435 24141815 := bstep (se 1 (by rfl) ⟨18106361, by rfl⟩ : syracuseStep 24141815 = 36212723) B36212723
theorem B16094543 : Blo 2231435 16094543 := bstep (se 1 (by rfl) ⟨12070907, by rfl⟩ : syracuseStep 16094543 = 24141815) B24141815
theorem B42918781 : Blo 2231435 42918781 := bstep (se 3 (by rfl) ⟨8047271, by rfl⟩ : syracuseStep 42918781 = 16094543) B16094543
theorem B57225041 : Blo 2231435 57225041 := bstep (se 2 (by rfl) ⟨21459390, by rfl⟩ : syracuseStep 57225041 = 42918781) B42918781
theorem B38150027 : Blo 2231435 38150027 := bstep (se 1 (by rfl) ⟨28612520, by rfl⟩ : syracuseStep 38150027 = 57225041) B57225041
theorem B25433351 : Blo 2231435 25433351 := bstep (se 1 (by rfl) ⟨19075013, by rfl⟩ : syracuseStep 25433351 = 38150027) B38150027
theorem B16955567 : Blo 2231435 16955567 := bstep (se 1 (by rfl) ⟨12716675, by rfl⟩ : syracuseStep 16955567 = 25433351) B25433351
theorem B11303711 : Blo 2231435 11303711 := bstep (se 1 (by rfl) ⟨8477783, by rfl⟩ : syracuseStep 11303711 = 16955567) B16955567
theorem B7535807 : Blo 2231435 7535807 := bstep (se 1 (by rfl) ⟨5651855, by rfl⟩ : syracuseStep 7535807 = 11303711) B11303711
theorem B5023871 : Blo 2231435 5023871 := bstep (se 1 (by rfl) ⟨3767903, by rfl⟩ : syracuseStep 5023871 = 7535807) B7535807
theorem B3349247 : Blo 2231435 3349247 := bstep (se 1 (by rfl) ⟨2511935, by rfl⟩ : syracuseStep 3349247 = 5023871) B5023871
theorem B2232831 : Blo 2231435 2232831 := bstep (se 1 (by rfl) ⟨1674623, by rfl⟩ : syracuseStep 2232831 = 3349247) B3349247
theorem B3349253 : Blo 2231435 3349253 := bbase (se 4 (by rfl) ⟨313992, by rfl⟩ : syracuseStep 3349253 = 627985) (by norm_num)
theorem B2232835 : Blo 2231435 2232835 := bstep (se 1 (by rfl) ⟨1674626, by rfl⟩ : syracuseStep 2232835 = 3349253) B3349253
theorem B3767917 : Blo 2231435 3767917 := bbase (se 3 (by rfl) ⟨706484, by rfl⟩ : syracuseStep 3767917 = 1412969) (by norm_num)
theorem B5023889 : Blo 2231435 5023889 := bstep (se 2 (by rfl) ⟨1883958, by rfl⟩ : syracuseStep 5023889 = 3767917) B3767917
theorem B3349259 : Blo 2231435 3349259 := bstep (se 1 (by rfl) ⟨2511944, by rfl⟩ : syracuseStep 3349259 = 5023889) B5023889
theorem B2232839 : Blo 2231435 2232839 := bstep (se 1 (by rfl) ⟨1674629, by rfl⟩ : syracuseStep 2232839 = 3349259) B3349259
theorem B2511949 : Blo 2231435 2511949 := bbase (se 3 (by rfl) ⟨470990, by rfl⟩ : syracuseStep 2511949 = 941981) (by norm_num)
theorem B3349265 : Blo 2231435 3349265 := bstep (se 2 (by rfl) ⟨1255974, by rfl⟩ : syracuseStep 3349265 = 2511949) B2511949
theorem B2232843 : Blo 2231435 2232843 := bstep (se 1 (by rfl) ⟨1674632, by rfl⟩ : syracuseStep 2232843 = 3349265) B3349265
theorem B7535861 : Blo 2231435 7535861 := bbase (se 5 (by rfl) ⟨353243, by rfl⟩ : syracuseStep 7535861 = 706487) (by norm_num)
theorem B5023907 : Blo 2231435 5023907 := bstep (se 1 (by rfl) ⟨3767930, by rfl⟩ : syracuseStep 5023907 = 7535861) B7535861
theorem B3349271 : Blo 2231435 3349271 := bstep (se 1 (by rfl) ⟨2511953, by rfl⟩ : syracuseStep 3349271 = 5023907) B5023907
theorem B2232847 : Blo 2231435 2232847 := bstep (se 1 (by rfl) ⟨1674635, by rfl⟩ : syracuseStep 2232847 = 3349271) B3349271
theorem B3349277 : Blo 2231435 3349277 := bbase (se 3 (by rfl) ⟨627989, by rfl⟩ : syracuseStep 3349277 = 1255979) (by norm_num)
theorem B2232851 : Blo 2231435 2232851 := bstep (se 1 (by rfl) ⟨1674638, by rfl⟩ : syracuseStep 2232851 = 3349277) B3349277
theorem B5023925 : Blo 2231435 5023925 := bbase (se 5 (by rfl) ⟨235496, by rfl⟩ : syracuseStep 5023925 = 470993) (by norm_num)
theorem B3349283 : Blo 2231435 3349283 := bstep (se 1 (by rfl) ⟨2511962, by rfl⟩ : syracuseStep 3349283 = 5023925) B5023925
theorem B2232855 : Blo 2231435 2232855 := bstep (se 1 (by rfl) ⟨1674641, by rfl⟩ : syracuseStep 2232855 = 3349283) B3349283
theorem B5364917 : Blo 2231435 5364917 := bbase (se 5 (by rfl) ⟨251480, by rfl⟩ : syracuseStep 5364917 = 502961) (by norm_num)
theorem B3576611 : Blo 2231435 3576611 := bstep (se 1 (by rfl) ⟨2682458, by rfl⟩ : syracuseStep 3576611 = 5364917) B5364917
theorem B2384407 : Blo 2231435 2384407 := bstep (se 1 (by rfl) ⟨1788305, by rfl⟩ : syracuseStep 2384407 = 3576611) B3576611
theorem B12716837 : Blo 2231435 12716837 := bstep (se 4 (by rfl) ⟨1192203, by rfl⟩ : syracuseStep 12716837 = 2384407) B2384407
theorem B8477891 : Blo 2231435 8477891 := bstep (se 1 (by rfl) ⟨6358418, by rfl⟩ : syracuseStep 8477891 = 12716837) B12716837
theorem B5651927 : Blo 2231435 5651927 := bstep (se 1 (by rfl) ⟨4238945, by rfl⟩ : syracuseStep 5651927 = 8477891) B8477891
theorem B3767951 : Blo 2231435 3767951 := bstep (se 1 (by rfl) ⟨2825963, by rfl⟩ : syracuseStep 3767951 = 5651927) B5651927
theorem B2511967 : Blo 2231435 2511967 := bstep (se 1 (by rfl) ⟨1883975, by rfl⟩ : syracuseStep 2511967 = 3767951) B3767951
theorem B3349289 : Blo 2231435 3349289 := bstep (se 2 (by rfl) ⟨1255983, by rfl⟩ : syracuseStep 3349289 = 2511967) B2511967
theorem B2232859 : Blo 2231435 2232859 := bstep (se 1 (by rfl) ⟨1674644, by rfl⟩ : syracuseStep 2232859 = 3349289) B3349289
theorem B2546245 : Blo 2231435 2546245 := bbase (se 4 (by rfl) ⟨238710, by rfl⟩ : syracuseStep 2546245 = 477421) (by norm_num)
theorem B13579973 : Blo 2231435 13579973 := bstep (se 4 (by rfl) ⟨1273122, by rfl⟩ : syracuseStep 13579973 = 2546245) B2546245
theorem B9053315 : Blo 2231435 9053315 := bstep (se 1 (by rfl) ⟨6789986, by rfl⟩ : syracuseStep 9053315 = 13579973) B13579973
theorem B6035543 : Blo 2231435 6035543 := bstep (se 1 (by rfl) ⟨4526657, by rfl⟩ : syracuseStep 6035543 = 9053315) B9053315
theorem B4023695 : Blo 2231435 4023695 := bstep (se 1 (by rfl) ⟨3017771, by rfl⟩ : syracuseStep 4023695 = 6035543) B6035543
theorem B2682463 : Blo 2231435 2682463 := bstep (se 1 (by rfl) ⟨2011847, by rfl⟩ : syracuseStep 2682463 = 4023695) B4023695
theorem B3576617 : Blo 2231435 3576617 := bstep (se 2 (by rfl) ⟨1341231, by rfl⟩ : syracuseStep 3576617 = 2682463) B2682463
theorem B2384411 : Blo 2231435 2384411 := bstep (se 1 (by rfl) ⟨1788308, by rfl⟩ : syracuseStep 2384411 = 3576617) B3576617
theorem B6358429 : Blo 2231435 6358429 := bstep (se 3 (by rfl) ⟨1192205, by rfl⟩ : syracuseStep 6358429 = 2384411) B2384411
theorem B8477905 : Blo 2231435 8477905 := bstep (se 2 (by rfl) ⟨3179214, by rfl⟩ : syracuseStep 8477905 = 6358429) B6358429
theorem B11303873 : Blo 2231435 11303873 := bstep (se 2 (by rfl) ⟨4238952, by rfl⟩ : syracuseStep 11303873 = 8477905) B8477905
theorem B7535915 : Blo 2231435 7535915 := bstep (se 1 (by rfl) ⟨5651936, by rfl⟩ : syracuseStep 7535915 = 11303873) B11303873
theorem B5023943 : Blo 2231435 5023943 := bstep (se 1 (by rfl) ⟨3767957, by rfl⟩ : syracuseStep 5023943 = 7535915) B7535915
theorem B3349295 : Blo 2231435 3349295 := bstep (se 1 (by rfl) ⟨2511971, by rfl⟩ : syracuseStep 3349295 = 5023943) B5023943
theorem B2232863 : Blo 2231435 2232863 := bstep (se 1 (by rfl) ⟨1674647, by rfl⟩ : syracuseStep 2232863 = 3349295) B3349295
theorem B3349301 : Blo 2231435 3349301 := bbase (se 5 (by rfl) ⟨156998, by rfl⟩ : syracuseStep 3349301 = 313997) (by norm_num)
theorem B2232867 : Blo 2231435 2232867 := bstep (se 1 (by rfl) ⟨1674650, by rfl⟩ : syracuseStep 2232867 = 3349301) B3349301
theorem B5651957 : Blo 2231435 5651957 := bbase (se 5 (by rfl) ⟨264935, by rfl⟩ : syracuseStep 5651957 = 529871) (by norm_num)
theorem B3767971 : Blo 2231435 3767971 := bstep (se 1 (by rfl) ⟨2825978, by rfl⟩ : syracuseStep 3767971 = 5651957) B5651957
theorem B5023961 : Blo 2231435 5023961 := bstep (se 2 (by rfl) ⟨1883985, by rfl⟩ : syracuseStep 5023961 = 3767971) B3767971
theorem B3349307 : Blo 2231435 3349307 := bstep (se 1 (by rfl) ⟨2511980, by rfl⟩ : syracuseStep 3349307 = 5023961) B5023961
theorem B2232871 : Blo 2231435 2232871 := bstep (se 1 (by rfl) ⟨1674653, by rfl⟩ : syracuseStep 2232871 = 3349307) B3349307
theorem B2511985 : Blo 2231435 2511985 := bbase (se 2 (by rfl) ⟨941994, by rfl⟩ : syracuseStep 2511985 = 1883989) (by norm_num)
theorem B3349313 : Blo 2231435 3349313 := bstep (se 2 (by rfl) ⟨1255992, by rfl⟩ : syracuseStep 3349313 = 2511985) B2511985
theorem B2232875 : Blo 2231435 2232875 := bstep (se 1 (by rfl) ⟨1674656, by rfl⟩ : syracuseStep 2232875 = 3349313) B3349313
theorem B7153285 : Blo 2231435 7153285 := bbase (se 4 (by rfl) ⟨670620, by rfl⟩ : syracuseStep 7153285 = 1341241) (by norm_num)
theorem B9537713 : Blo 2231435 9537713 := bstep (se 2 (by rfl) ⟨3576642, by rfl⟩ : syracuseStep 9537713 = 7153285) B7153285
theorem B6358475 : Blo 2231435 6358475 := bstep (se 1 (by rfl) ⟨4768856, by rfl⟩ : syracuseStep 6358475 = 9537713) B9537713
theorem B4238983 : Blo 2231435 4238983 := bstep (se 1 (by rfl) ⟨3179237, by rfl⟩ : syracuseStep 4238983 = 6358475) B6358475
theorem B5651977 : Blo 2231435 5651977 := bstep (se 2 (by rfl) ⟨2119491, by rfl⟩ : syracuseStep 5651977 = 4238983) B4238983
theorem B7535969 : Blo 2231435 7535969 := bstep (se 2 (by rfl) ⟨2825988, by rfl⟩ : syracuseStep 7535969 = 5651977) B5651977
theorem B5023979 : Blo 2231435 5023979 := bstep (se 1 (by rfl) ⟨3767984, by rfl⟩ : syracuseStep 5023979 = 7535969) B7535969
theorem B3349319 : Blo 2231435 3349319 := bstep (se 1 (by rfl) ⟨2511989, by rfl⟩ : syracuseStep 3349319 = 5023979) B5023979
theorem B2232879 : Blo 2231435 2232879 := bstep (se 1 (by rfl) ⟨1674659, by rfl⟩ : syracuseStep 2232879 = 3349319) B3349319
theorem B3349325 : Blo 2231435 3349325 := bbase (se 3 (by rfl) ⟨627998, by rfl⟩ : syracuseStep 3349325 = 1255997) (by norm_num)
theorem B2232883 : Blo 2231435 2232883 := bstep (se 1 (by rfl) ⟨1674662, by rfl⟩ : syracuseStep 2232883 = 3349325) B3349325
theorem B5023997 : Blo 2231435 5023997 := bbase (se 3 (by rfl) ⟨941999, by rfl⟩ : syracuseStep 5023997 = 1883999) (by norm_num)
theorem B3349331 : Blo 2231435 3349331 := bstep (se 1 (by rfl) ⟨2511998, by rfl⟩ : syracuseStep 3349331 = 5023997) B5023997
theorem B2232887 : Blo 2231435 2232887 := bstep (se 1 (by rfl) ⟨1674665, by rfl⟩ : syracuseStep 2232887 = 3349331) B3349331
theorem B3768005 : Blo 2231435 3768005 := bbase (se 4 (by rfl) ⟨353250, by rfl⟩ : syracuseStep 3768005 = 706501) (by norm_num)
theorem B2512003 : Blo 2231435 2512003 := bstep (se 1 (by rfl) ⟨1884002, by rfl⟩ : syracuseStep 2512003 = 3768005) B3768005
theorem B3349337 : Blo 2231435 3349337 := bstep (se 2 (by rfl) ⟨1256001, by rfl⟩ : syracuseStep 3349337 = 2512003) B2512003
theorem B2232891 : Blo 2231435 2232891 := bstep (se 1 (by rfl) ⟨1674668, by rfl⟩ : syracuseStep 2232891 = 3349337) B3349337
theorem B16956053 : Blo 2231435 16956053 := bbase (se 6 (by rfl) ⟨397407, by rfl⟩ : syracuseStep 16956053 = 794815) (by norm_num)
theorem B11304035 : Blo 2231435 11304035 := bstep (se 1 (by rfl) ⟨8478026, by rfl⟩ : syracuseStep 11304035 = 16956053) B16956053
theorem B7536023 : Blo 2231435 7536023 := bstep (se 1 (by rfl) ⟨5652017, by rfl⟩ : syracuseStep 7536023 = 11304035) B11304035
theorem B5024015 : Blo 2231435 5024015 := bstep (se 1 (by rfl) ⟨3768011, by rfl⟩ : syracuseStep 5024015 = 7536023) B7536023
theorem B3349343 : Blo 2231435 3349343 := bstep (se 1 (by rfl) ⟨2512007, by rfl⟩ : syracuseStep 3349343 = 5024015) B5024015
theorem B2232895 : Blo 2231435 2232895 := bstep (se 1 (by rfl) ⟨1674671, by rfl⟩ : syracuseStep 2232895 = 3349343) B3349343
theorem B3349349 : Blo 2231435 3349349 := bbase (se 4 (by rfl) ⟨314001, by rfl⟩ : syracuseStep 3349349 = 628003) (by norm_num)
theorem B2232899 : Blo 2231435 2232899 := bstep (se 1 (by rfl) ⟨1674674, by rfl⟩ : syracuseStep 2232899 = 3349349) B3349349
theorem B4239029 : Blo 2231435 4239029 := bbase (se 5 (by rfl) ⟨198704, by rfl⟩ : syracuseStep 4239029 = 397409) (by norm_num)
theorem B2826019 : Blo 2231435 2826019 := bstep (se 1 (by rfl) ⟨2119514, by rfl⟩ : syracuseStep 2826019 = 4239029) B4239029
theorem B3768025 : Blo 2231435 3768025 := bstep (se 2 (by rfl) ⟨1413009, by rfl⟩ : syracuseStep 3768025 = 2826019) B2826019
theorem B5024033 : Blo 2231435 5024033 := bstep (se 2 (by rfl) ⟨1884012, by rfl⟩ : syracuseStep 5024033 = 3768025) B3768025
theorem B3349355 : Blo 2231435 3349355 := bstep (se 1 (by rfl) ⟨2512016, by rfl⟩ : syracuseStep 3349355 = 5024033) B5024033
theorem B2232903 : Blo 2231435 2232903 := bstep (se 1 (by rfl) ⟨1674677, by rfl⟩ : syracuseStep 2232903 = 3349355) B3349355
theorem B2512021 : Blo 2231435 2512021 := bbase (se 6 (by rfl) ⟨58875, by rfl⟩ : syracuseStep 2512021 = 117751) (by norm_num)
theorem B3349361 : Blo 2231435 3349361 := bstep (se 2 (by rfl) ⟨1256010, by rfl⟩ : syracuseStep 3349361 = 2512021) B2512021
theorem B2232907 : Blo 2231435 2232907 := bstep (se 1 (by rfl) ⟨1674680, by rfl⟩ : syracuseStep 2232907 = 3349361) B3349361
theorem B2826029 : Blo 2231435 2826029 := bbase (se 3 (by rfl) ⟨529880, by rfl⟩ : syracuseStep 2826029 = 1059761) (by norm_num)
theorem B7536077 : Blo 2231435 7536077 := bstep (se 3 (by rfl) ⟨1413014, by rfl⟩ : syracuseStep 7536077 = 2826029) B2826029
theorem B5024051 : Blo 2231435 5024051 := bstep (se 1 (by rfl) ⟨3768038, by rfl⟩ : syracuseStep 5024051 = 7536077) B7536077
theorem B3349367 : Blo 2231435 3349367 := bstep (se 1 (by rfl) ⟨2512025, by rfl⟩ : syracuseStep 3349367 = 5024051) B5024051
theorem B2232911 : Blo 2231435 2232911 := bstep (se 1 (by rfl) ⟨1674683, by rfl⟩ : syracuseStep 2232911 = 3349367) B3349367
theorem B3349373 : Blo 2231435 3349373 := bbase (se 3 (by rfl) ⟨628007, by rfl⟩ : syracuseStep 3349373 = 1256015) (by norm_num)
theorem B2232915 : Blo 2231435 2232915 := bstep (se 1 (by rfl) ⟨1674686, by rfl⟩ : syracuseStep 2232915 = 3349373) B3349373
theorem B5024069 : Blo 2231435 5024069 := bbase (se 4 (by rfl) ⟨471006, by rfl⟩ : syracuseStep 5024069 = 942013) (by norm_num)
theorem B3349379 : Blo 2231435 3349379 := bstep (se 1 (by rfl) ⟨2512034, by rfl⟩ : syracuseStep 3349379 = 5024069) B5024069
theorem B2232919 : Blo 2231435 2232919 := bstep (se 1 (by rfl) ⟨1674689, by rfl⟩ : syracuseStep 2232919 = 3349379) B3349379
theorem B7251029 : Blo 2231435 7251029 := bbase (se 8 (by rfl) ⟨42486, by rfl⟩ : syracuseStep 7251029 = 84973) (by norm_num)
theorem B4834019 : Blo 2231435 4834019 := bstep (se 1 (by rfl) ⟨3625514, by rfl⟩ : syracuseStep 4834019 = 7251029) B7251029
theorem B3222679 : Blo 2231435 3222679 := bstep (se 1 (by rfl) ⟨2417009, by rfl⟩ : syracuseStep 3222679 = 4834019) B4834019
theorem B4296905 : Blo 2231435 4296905 := bstep (se 2 (by rfl) ⟨1611339, by rfl⟩ : syracuseStep 4296905 = 3222679) B3222679
theorem B2864603 : Blo 2231435 2864603 := bstep (se 1 (by rfl) ⟨2148452, by rfl⟩ : syracuseStep 2864603 = 4296905) B4296905
theorem B7638941 : Blo 2231435 7638941 := bstep (se 3 (by rfl) ⟨1432301, by rfl⟩ : syracuseStep 7638941 = 2864603) B2864603
theorem B5092627 : Blo 2231435 5092627 := bstep (se 1 (by rfl) ⟨3819470, by rfl⟩ : syracuseStep 5092627 = 7638941) B7638941
theorem B6790169 : Blo 2231435 6790169 := bstep (se 2 (by rfl) ⟨2546313, by rfl⟩ : syracuseStep 6790169 = 5092627) B5092627
theorem B4526779 : Blo 2231435 4526779 := bstep (se 1 (by rfl) ⟨3395084, by rfl⟩ : syracuseStep 4526779 = 6790169) B6790169
theorem B6035705 : Blo 2231435 6035705 := bstep (se 2 (by rfl) ⟨2263389, by rfl⟩ : syracuseStep 6035705 = 4526779) B4526779
theorem B4023803 : Blo 2231435 4023803 := bstep (se 1 (by rfl) ⟨3017852, by rfl⟩ : syracuseStep 4023803 = 6035705) B6035705
theorem B10730141 : Blo 2231435 10730141 := bstep (se 3 (by rfl) ⟨2011901, by rfl⟩ : syracuseStep 10730141 = 4023803) B4023803
theorem B7153427 : Blo 2231435 7153427 := bstep (se 1 (by rfl) ⟨5365070, by rfl⟩ : syracuseStep 7153427 = 10730141) B10730141
theorem B4768951 : Blo 2231435 4768951 := bstep (se 1 (by rfl) ⟨3576713, by rfl⟩ : syracuseStep 4768951 = 7153427) B7153427
theorem B6358601 : Blo 2231435 6358601 := bstep (se 2 (by rfl) ⟨2384475, by rfl⟩ : syracuseStep 6358601 = 4768951) B4768951
theorem B4239067 : Blo 2231435 4239067 := bstep (se 1 (by rfl) ⟨3179300, by rfl⟩ : syracuseStep 4239067 = 6358601) B6358601
theorem B5652089 : Blo 2231435 5652089 := bstep (se 2 (by rfl) ⟨2119533, by rfl⟩ : syracuseStep 5652089 = 4239067) B4239067
theorem B3768059 : Blo 2231435 3768059 := bstep (se 1 (by rfl) ⟨2826044, by rfl⟩ : syracuseStep 3768059 = 5652089) B5652089
theorem B2512039 : Blo 2231435 2512039 := bstep (se 1 (by rfl) ⟨1884029, by rfl⟩ : syracuseStep 2512039 = 3768059) B3768059
theorem B3349385 : Blo 2231435 3349385 := bstep (se 2 (by rfl) ⟨1256019, by rfl⟩ : syracuseStep 3349385 = 2512039) B2512039
theorem B2232923 : Blo 2231435 2232923 := bstep (se 1 (by rfl) ⟨1674692, by rfl⟩ : syracuseStep 2232923 = 3349385) B3349385
theorem B11304197 : Blo 2231435 11304197 := bbase (se 4 (by rfl) ⟨1059768, by rfl⟩ : syracuseStep 11304197 = 2119537) (by norm_num)
theorem B7536131 : Blo 2231435 7536131 := bstep (se 1 (by rfl) ⟨5652098, by rfl⟩ : syracuseStep 7536131 = 11304197) B11304197
theorem B5024087 : Blo 2231435 5024087 := bstep (se 1 (by rfl) ⟨3768065, by rfl⟩ : syracuseStep 5024087 = 7536131) B7536131
theorem B3349391 : Blo 2231435 3349391 := bstep (se 1 (by rfl) ⟨2512043, by rfl⟩ : syracuseStep 3349391 = 5024087) B5024087
theorem B2232927 : Blo 2231435 2232927 := bstep (se 1 (by rfl) ⟨1674695, by rfl⟩ : syracuseStep 2232927 = 3349391) B3349391
theorem B3349397 : Blo 2231435 3349397 := bbase (se 6 (by rfl) ⟨78501, by rfl⟩ : syracuseStep 3349397 = 157003) (by norm_num)
theorem B2232931 : Blo 2231435 2232931 := bstep (se 1 (by rfl) ⟨1674698, by rfl⟩ : syracuseStep 2232931 = 3349397) B3349397
theorem B12717269 : Blo 2231435 12717269 := bbase (se 7 (by rfl) ⟨149030, by rfl⟩ : syracuseStep 12717269 = 298061) (by norm_num)
theorem B8478179 : Blo 2231435 8478179 := bstep (se 1 (by rfl) ⟨6358634, by rfl⟩ : syracuseStep 8478179 = 12717269) B12717269
theorem B5652119 : Blo 2231435 5652119 := bstep (se 1 (by rfl) ⟨4239089, by rfl⟩ : syracuseStep 5652119 = 8478179) B8478179
theorem B3768079 : Blo 2231435 3768079 := bstep (se 1 (by rfl) ⟨2826059, by rfl⟩ : syracuseStep 3768079 = 5652119) B5652119
theorem B5024105 : Blo 2231435 5024105 := bstep (se 2 (by rfl) ⟨1884039, by rfl⟩ : syracuseStep 5024105 = 3768079) B3768079
theorem B3349403 : Blo 2231435 3349403 := bstep (se 1 (by rfl) ⟨2512052, by rfl⟩ : syracuseStep 3349403 = 5024105) B5024105
theorem B2232935 : Blo 2231435 2232935 := bstep (se 1 (by rfl) ⟨1674701, by rfl⟩ : syracuseStep 2232935 = 3349403) B3349403
theorem B2512057 : Blo 2231435 2512057 := bbase (se 2 (by rfl) ⟨942021, by rfl⟩ : syracuseStep 2512057 = 1884043) (by norm_num)
theorem B3349409 : Blo 2231435 3349409 := bstep (se 2 (by rfl) ⟨1256028, by rfl⟩ : syracuseStep 3349409 = 2512057) B2512057
theorem B2232939 : Blo 2231435 2232939 := bstep (se 1 (by rfl) ⟨1674704, by rfl⟩ : syracuseStep 2232939 = 3349409) B3349409
theorem B4834061 : Blo 2231435 4834061 := bbase (se 3 (by rfl) ⟨906386, by rfl⟩ : syracuseStep 4834061 = 1812773) (by norm_num)
theorem B3222707 : Blo 2231435 3222707 := bstep (se 1 (by rfl) ⟨2417030, by rfl⟩ : syracuseStep 3222707 = 4834061) B4834061
theorem B8593885 : Blo 2231435 8593885 := bstep (se 3 (by rfl) ⟨1611353, by rfl⟩ : syracuseStep 8593885 = 3222707) B3222707
theorem B11458513 : Blo 2231435 11458513 := bstep (se 2 (by rfl) ⟨4296942, by rfl⟩ : syracuseStep 11458513 = 8593885) B8593885
theorem B15278017 : Blo 2231435 15278017 := bstep (se 2 (by rfl) ⟨5729256, by rfl⟩ : syracuseStep 15278017 = 11458513) B11458513
theorem B20370689 : Blo 2231435 20370689 := bstep (se 2 (by rfl) ⟨7639008, by rfl⟩ : syracuseStep 20370689 = 15278017) B15278017
theorem B13580459 : Blo 2231435 13580459 := bstep (se 1 (by rfl) ⟨10185344, by rfl⟩ : syracuseStep 13580459 = 20370689) B20370689
theorem B9053639 : Blo 2231435 9053639 := bstep (se 1 (by rfl) ⟨6790229, by rfl⟩ : syracuseStep 9053639 = 13580459) B13580459
theorem B6035759 : Blo 2231435 6035759 := bstep (se 1 (by rfl) ⟨4526819, by rfl⟩ : syracuseStep 6035759 = 9053639) B9053639
theorem B4023839 : Blo 2231435 4023839 := bstep (se 1 (by rfl) ⟨3017879, by rfl⟩ : syracuseStep 4023839 = 6035759) B6035759
theorem B2682559 : Blo 2231435 2682559 := bstep (se 1 (by rfl) ⟨2011919, by rfl⟩ : syracuseStep 2682559 = 4023839) B4023839
theorem B3576745 : Blo 2231435 3576745 := bstep (se 2 (by rfl) ⟨1341279, by rfl⟩ : syracuseStep 3576745 = 2682559) B2682559
theorem B4768993 : Blo 2231435 4768993 := bstep (se 2 (by rfl) ⟨1788372, by rfl⟩ : syracuseStep 4768993 = 3576745) B3576745
theorem B6358657 : Blo 2231435 6358657 := bstep (se 2 (by rfl) ⟨2384496, by rfl⟩ : syracuseStep 6358657 = 4768993) B4768993
theorem B8478209 : Blo 2231435 8478209 := bstep (se 2 (by rfl) ⟨3179328, by rfl⟩ : syracuseStep 8478209 = 6358657) B6358657
theorem B5652139 : Blo 2231435 5652139 := bstep (se 1 (by rfl) ⟨4239104, by rfl⟩ : syracuseStep 5652139 = 8478209) B8478209
theorem B7536185 : Blo 2231435 7536185 := bstep (se 2 (by rfl) ⟨2826069, by rfl⟩ : syracuseStep 7536185 = 5652139) B5652139
theorem B5024123 : Blo 2231435 5024123 := bstep (se 1 (by rfl) ⟨3768092, by rfl⟩ : syracuseStep 5024123 = 7536185) B7536185
theorem B3349415 : Blo 2231435 3349415 := bstep (se 1 (by rfl) ⟨2512061, by rfl⟩ : syracuseStep 3349415 = 5024123) B5024123
theorem B2232943 : Blo 2231435 2232943 := bstep (se 1 (by rfl) ⟨1674707, by rfl⟩ : syracuseStep 2232943 = 3349415) B3349415
theorem B3349421 : Blo 2231435 3349421 := bbase (se 3 (by rfl) ⟨628016, by rfl⟩ : syracuseStep 3349421 = 1256033) (by norm_num)
theorem B2232947 : Blo 2231435 2232947 := bstep (se 1 (by rfl) ⟨1674710, by rfl⟩ : syracuseStep 2232947 = 3349421) B3349421
theorem B5024141 : Blo 2231435 5024141 := bbase (se 3 (by rfl) ⟨942026, by rfl⟩ : syracuseStep 5024141 = 1884053) (by norm_num)
theorem B3349427 : Blo 2231435 3349427 := bstep (se 1 (by rfl) ⟨2512070, by rfl⟩ : syracuseStep 3349427 = 5024141) B5024141
theorem B2232951 : Blo 2231435 2232951 := bstep (se 1 (by rfl) ⟨1674713, by rfl⟩ : syracuseStep 2232951 = 3349427) B3349427
theorem B2826085 : Blo 2231435 2826085 := bbase (se 4 (by rfl) ⟨264945, by rfl⟩ : syracuseStep 2826085 = 529891) (by norm_num)
theorem B3768113 : Blo 2231435 3768113 := bstep (se 2 (by rfl) ⟨1413042, by rfl⟩ : syracuseStep 3768113 = 2826085) B2826085
theorem B2512075 : Blo 2231435 2512075 := bstep (se 1 (by rfl) ⟨1884056, by rfl⟩ : syracuseStep 2512075 = 3768113) B3768113
theorem B3349433 : Blo 2231435 3349433 := bstep (se 2 (by rfl) ⟨1256037, by rfl⟩ : syracuseStep 3349433 = 2512075) B2512075
theorem B2232955 : Blo 2231435 2232955 := bstep (se 1 (by rfl) ⟨1674716, by rfl⟩ : syracuseStep 2232955 = 3349433) B3349433
theorem B8047733 : Blo 2231435 8047733 := bbase (se 5 (by rfl) ⟨377237, by rfl⟩ : syracuseStep 8047733 = 754475) (by norm_num)
theorem B21460621 : Blo 2231435 21460621 := bstep (se 3 (by rfl) ⟨4023866, by rfl⟩ : syracuseStep 21460621 = 8047733) B8047733
theorem B28614161 : Blo 2231435 28614161 := bstep (se 2 (by rfl) ⟨10730310, by rfl⟩ : syracuseStep 28614161 = 21460621) B21460621
theorem B19076107 : Blo 2231435 19076107 := bstep (se 1 (by rfl) ⟨14307080, by rfl⟩ : syracuseStep 19076107 = 28614161) B28614161
theorem B25434809 : Blo 2231435 25434809 := bstep (se 2 (by rfl) ⟨9538053, by rfl⟩ : syracuseStep 25434809 = 19076107) B19076107
theorem B16956539 : Blo 2231435 16956539 := bstep (se 1 (by rfl) ⟨12717404, by rfl⟩ : syracuseStep 16956539 = 25434809) B25434809
theorem B11304359 : Blo 2231435 11304359 := bstep (se 1 (by rfl) ⟨8478269, by rfl⟩ : syracuseStep 11304359 = 16956539) B16956539
theorem B7536239 : Blo 2231435 7536239 := bstep (se 1 (by rfl) ⟨5652179, by rfl⟩ : syracuseStep 7536239 = 11304359) B11304359
theorem B5024159 : Blo 2231435 5024159 := bstep (se 1 (by rfl) ⟨3768119, by rfl⟩ : syracuseStep 5024159 = 7536239) B7536239
theorem B3349439 : Blo 2231435 3349439 := bstep (se 1 (by rfl) ⟨2512079, by rfl⟩ : syracuseStep 3349439 = 5024159) B5024159
theorem B2232959 : Blo 2231435 2232959 := bstep (se 1 (by rfl) ⟨1674719, by rfl⟩ : syracuseStep 2232959 = 3349439) B3349439
theorem B3349445 : Blo 2231435 3349445 := bbase (se 4 (by rfl) ⟨314010, by rfl⟩ : syracuseStep 3349445 = 628021) (by norm_num)
theorem B2232963 : Blo 2231435 2232963 := bstep (se 1 (by rfl) ⟨1674722, by rfl⟩ : syracuseStep 2232963 = 3349445) B3349445
theorem B3768133 : Blo 2231435 3768133 := bbase (se 4 (by rfl) ⟨353262, by rfl⟩ : syracuseStep 3768133 = 706525) (by norm_num)
theorem B5024177 : Blo 2231435 5024177 := bstep (se 2 (by rfl) ⟨1884066, by rfl⟩ : syracuseStep 5024177 = 3768133) B3768133
theorem B3349451 : Blo 2231435 3349451 := bstep (se 1 (by rfl) ⟨2512088, by rfl⟩ : syracuseStep 3349451 = 5024177) B5024177
theorem B2232967 : Blo 2231435 2232967 := bstep (se 1 (by rfl) ⟨1674725, by rfl⟩ : syracuseStep 2232967 = 3349451) B3349451
theorem B2512093 : Blo 2231435 2512093 := bbase (se 3 (by rfl) ⟨471017, by rfl⟩ : syracuseStep 2512093 = 942035) (by norm_num)
theorem B3349457 : Blo 2231435 3349457 := bstep (se 2 (by rfl) ⟨1256046, by rfl⟩ : syracuseStep 3349457 = 2512093) B2512093
theorem B2232971 : Blo 2231435 2232971 := bstep (se 1 (by rfl) ⟨1674728, by rfl⟩ : syracuseStep 2232971 = 3349457) B3349457
theorem B7536293 : Blo 2231435 7536293 := bbase (se 4 (by rfl) ⟨706527, by rfl⟩ : syracuseStep 7536293 = 1413055) (by norm_num)
theorem B5024195 : Blo 2231435 5024195 := bstep (se 1 (by rfl) ⟨3768146, by rfl⟩ : syracuseStep 5024195 = 7536293) B7536293
theorem B3349463 : Blo 2231435 3349463 := bstep (se 1 (by rfl) ⟨2512097, by rfl⟩ : syracuseStep 3349463 = 5024195) B5024195
theorem B2232975 : Blo 2231435 2232975 := bstep (se 1 (by rfl) ⟨1674731, by rfl⟩ : syracuseStep 2232975 = 3349463) B3349463
theorem B3349469 : Blo 2231435 3349469 := bbase (se 3 (by rfl) ⟨628025, by rfl⟩ : syracuseStep 3349469 = 1256051) (by norm_num)
theorem B2232979 : Blo 2231435 2232979 := bstep (se 1 (by rfl) ⟨1674734, by rfl⟩ : syracuseStep 2232979 = 3349469) B3349469
theorem B5024213 : Blo 2231435 5024213 := bbase (se 7 (by rfl) ⟨58877, by rfl⟩ : syracuseStep 5024213 = 117755) (by norm_num)
theorem B3349475 : Blo 2231435 3349475 := bstep (se 1 (by rfl) ⟨2512106, by rfl⟩ : syracuseStep 3349475 = 5024213) B5024213
theorem B2232983 : Blo 2231435 2232983 := bstep (se 1 (by rfl) ⟨1674737, by rfl⟩ : syracuseStep 2232983 = 3349475) B3349475
theorem B4355653 : Blo 2231435 4355653 := bbase (se 4 (by rfl) ⟨408342, by rfl⟩ : syracuseStep 4355653 = 816685) (by norm_num)
theorem B5807537 : Blo 2231435 5807537 := bstep (se 2 (by rfl) ⟨2177826, by rfl⟩ : syracuseStep 5807537 = 4355653) B4355653
theorem B3871691 : Blo 2231435 3871691 := bstep (se 1 (by rfl) ⟨2903768, by rfl⟩ : syracuseStep 3871691 = 5807537) B5807537
theorem B2581127 : Blo 2231435 2581127 := bstep (se 1 (by rfl) ⟨1935845, by rfl⟩ : syracuseStep 2581127 = 3871691) B3871691
theorem B27532021 : Blo 2231435 27532021 := bstep (se 5 (by rfl) ⟨1290563, by rfl⟩ : syracuseStep 27532021 = 2581127) B2581127
theorem B36709361 : Blo 2231435 36709361 := bstep (se 2 (by rfl) ⟨13766010, by rfl⟩ : syracuseStep 36709361 = 27532021) B27532021
theorem B24472907 : Blo 2231435 24472907 := bstep (se 1 (by rfl) ⟨18354680, by rfl⟩ : syracuseStep 24472907 = 36709361) B36709361
theorem B16315271 : Blo 2231435 16315271 := bstep (se 1 (by rfl) ⟨12236453, by rfl⟩ : syracuseStep 16315271 = 24472907) B24472907
theorem B10876847 : Blo 2231435 10876847 := bstep (se 1 (by rfl) ⟨8157635, by rfl⟩ : syracuseStep 10876847 = 16315271) B16315271
theorem B29004925 : Blo 2231435 29004925 := bstep (se 3 (by rfl) ⟨5438423, by rfl⟩ : syracuseStep 29004925 = 10876847) B10876847
theorem B38673233 : Blo 2231435 38673233 := bstep (se 2 (by rfl) ⟨14502462, by rfl⟩ : syracuseStep 38673233 = 29004925) B29004925
theorem B25782155 : Blo 2231435 25782155 := bstep (se 1 (by rfl) ⟨19336616, by rfl⟩ : syracuseStep 25782155 = 38673233) B38673233
theorem B17188103 : Blo 2231435 17188103 := bstep (se 1 (by rfl) ⟨12891077, by rfl⟩ : syracuseStep 17188103 = 25782155) B25782155
theorem B45834941 : Blo 2231435 45834941 := bstep (se 3 (by rfl) ⟨8594051, by rfl⟩ : syracuseStep 45834941 = 17188103) B17188103
theorem B122226509 : Blo 2231435 122226509 := bstep (se 3 (by rfl) ⟨22917470, by rfl⟩ : syracuseStep 122226509 = 45834941) B45834941
theorem B81484339 : Blo 2231435 81484339 := bstep (se 1 (by rfl) ⟨61113254, by rfl⟩ : syracuseStep 81484339 = 122226509) B122226509
theorem B108645785 : Blo 2231435 108645785 := bstep (se 2 (by rfl) ⟨40742169, by rfl⟩ : syracuseStep 108645785 = 81484339) B81484339
theorem B72430523 : Blo 2231435 72430523 := bstep (se 1 (by rfl) ⟨54322892, by rfl⟩ : syracuseStep 72430523 = 108645785) B108645785
theorem B48287015 : Blo 2231435 48287015 := bstep (se 1 (by rfl) ⟨36215261, by rfl⟩ : syracuseStep 48287015 = 72430523) B72430523
theorem B32191343 : Blo 2231435 32191343 := bstep (se 1 (by rfl) ⟨24143507, by rfl⟩ : syracuseStep 32191343 = 48287015) B48287015
theorem B21460895 : Blo 2231435 21460895 := bstep (se 1 (by rfl) ⟨16095671, by rfl⟩ : syracuseStep 21460895 = 32191343) B32191343
theorem B14307263 : Blo 2231435 14307263 := bstep (se 1 (by rfl) ⟨10730447, by rfl⟩ : syracuseStep 14307263 = 21460895) B21460895
theorem B9538175 : Blo 2231435 9538175 := bstep (se 1 (by rfl) ⟨7153631, by rfl⟩ : syracuseStep 9538175 = 14307263) B14307263
theorem B6358783 : Blo 2231435 6358783 := bstep (se 1 (by rfl) ⟨4769087, by rfl⟩ : syracuseStep 6358783 = 9538175) B9538175
theorem B8478377 : Blo 2231435 8478377 := bstep (se 2 (by rfl) ⟨3179391, by rfl⟩ : syracuseStep 8478377 = 6358783) B6358783
theorem B5652251 : Blo 2231435 5652251 := bstep (se 1 (by rfl) ⟨4239188, by rfl⟩ : syracuseStep 5652251 = 8478377) B8478377
theorem B3768167 : Blo 2231435 3768167 := bstep (se 1 (by rfl) ⟨2826125, by rfl⟩ : syracuseStep 3768167 = 5652251) B5652251
theorem B2512111 : Blo 2231435 2512111 := bstep (se 1 (by rfl) ⟨1884083, by rfl⟩ : syracuseStep 2512111 = 3768167) B3768167
theorem B3349481 : Blo 2231435 3349481 := bstep (se 2 (by rfl) ⟨1256055, by rfl⟩ : syracuseStep 3349481 = 2512111) B2512111
theorem B2232987 : Blo 2231435 2232987 := bstep (se 1 (by rfl) ⟨1674740, by rfl⟩ : syracuseStep 2232987 = 3349481) B3349481
theorem B2864689 : Blo 2231435 2864689 := bbase (se 2 (by rfl) ⟨1074258, by rfl⟩ : syracuseStep 2864689 = 2148517) (by norm_num)
theorem B15278341 : Blo 2231435 15278341 := bstep (se 4 (by rfl) ⟨1432344, by rfl⟩ : syracuseStep 15278341 = 2864689) B2864689
theorem B20371121 : Blo 2231435 20371121 := bstep (se 2 (by rfl) ⟨7639170, by rfl⟩ : syracuseStep 20371121 = 15278341) B15278341
theorem B13580747 : Blo 2231435 13580747 := bstep (se 1 (by rfl) ⟨10185560, by rfl⟩ : syracuseStep 13580747 = 20371121) B20371121
theorem B9053831 : Blo 2231435 9053831 := bstep (se 1 (by rfl) ⟨6790373, by rfl⟩ : syracuseStep 9053831 = 13580747) B13580747
theorem B6035887 : Blo 2231435 6035887 := bstep (se 1 (by rfl) ⟨4526915, by rfl⟩ : syracuseStep 6035887 = 9053831) B9053831
theorem B8047849 : Blo 2231435 8047849 := bstep (se 2 (by rfl) ⟨3017943, by rfl⟩ : syracuseStep 8047849 = 6035887) B6035887
theorem B10730465 : Blo 2231435 10730465 := bstep (se 2 (by rfl) ⟨4023924, by rfl⟩ : syracuseStep 10730465 = 8047849) B8047849
theorem B7153643 : Blo 2231435 7153643 := bstep (se 1 (by rfl) ⟨5365232, by rfl⟩ : syracuseStep 7153643 = 10730465) B10730465
theorem B19076381 : Blo 2231435 19076381 := bstep (se 3 (by rfl) ⟨3576821, by rfl⟩ : syracuseStep 19076381 = 7153643) B7153643
theorem B12717587 : Blo 2231435 12717587 := bstep (se 1 (by rfl) ⟨9538190, by rfl⟩ : syracuseStep 12717587 = 19076381) B19076381
theorem B8478391 : Blo 2231435 8478391 := bstep (se 1 (by rfl) ⟨6358793, by rfl⟩ : syracuseStep 8478391 = 12717587) B12717587
theorem B11304521 : Blo 2231435 11304521 := bstep (se 2 (by rfl) ⟨4239195, by rfl⟩ : syracuseStep 11304521 = 8478391) B8478391
theorem B7536347 : Blo 2231435 7536347 := bstep (se 1 (by rfl) ⟨5652260, by rfl⟩ : syracuseStep 7536347 = 11304521) B11304521
theorem B5024231 : Blo 2231435 5024231 := bstep (se 1 (by rfl) ⟨3768173, by rfl⟩ : syracuseStep 5024231 = 7536347) B7536347
theorem B3349487 : Blo 2231435 3349487 := bstep (se 1 (by rfl) ⟨2512115, by rfl⟩ : syracuseStep 3349487 = 5024231) B5024231
theorem B2232991 : Blo 2231435 2232991 := bstep (se 1 (by rfl) ⟨1674743, by rfl⟩ : syracuseStep 2232991 = 3349487) B3349487
theorem B3349493 : Blo 2231435 3349493 := bbase (se 5 (by rfl) ⟨157007, by rfl⟩ : syracuseStep 3349493 = 314015) (by norm_num)
theorem B2232995 : Blo 2231435 2232995 := bstep (se 1 (by rfl) ⟨1674746, by rfl⟩ : syracuseStep 2232995 = 3349493) B3349493
theorem B5365253 : Blo 2231435 5365253 := bbase (se 4 (by rfl) ⟨502992, by rfl⟩ : syracuseStep 5365253 = 1005985) (by norm_num)
theorem B3576835 : Blo 2231435 3576835 := bstep (se 1 (by rfl) ⟨2682626, by rfl⟩ : syracuseStep 3576835 = 5365253) B5365253
theorem B4769113 : Blo 2231435 4769113 := bstep (se 2 (by rfl) ⟨1788417, by rfl⟩ : syracuseStep 4769113 = 3576835) B3576835
theorem B6358817 : Blo 2231435 6358817 := bstep (se 2 (by rfl) ⟨2384556, by rfl⟩ : syracuseStep 6358817 = 4769113) B4769113
theorem B4239211 : Blo 2231435 4239211 := bstep (se 1 (by rfl) ⟨3179408, by rfl⟩ : syracuseStep 4239211 = 6358817) B6358817
theorem B5652281 : Blo 2231435 5652281 := bstep (se 2 (by rfl) ⟨2119605, by rfl⟩ : syracuseStep 5652281 = 4239211) B4239211
theorem B3768187 : Blo 2231435 3768187 := bstep (se 1 (by rfl) ⟨2826140, by rfl⟩ : syracuseStep 3768187 = 5652281) B5652281
theorem B5024249 : Blo 2231435 5024249 := bstep (se 2 (by rfl) ⟨1884093, by rfl⟩ : syracuseStep 5024249 = 3768187) B3768187
theorem B3349499 : Blo 2231435 3349499 := bstep (se 1 (by rfl) ⟨2512124, by rfl⟩ : syracuseStep 3349499 = 5024249) B5024249
theorem B2232999 : Blo 2231435 2232999 := bstep (se 1 (by rfl) ⟨1674749, by rfl⟩ : syracuseStep 2232999 = 3349499) B3349499
theorem B2512129 : Blo 2231435 2512129 := bbase (se 2 (by rfl) ⟨942048, by rfl⟩ : syracuseStep 2512129 = 1884097) (by norm_num)
theorem B3349505 : Blo 2231435 3349505 := bstep (se 2 (by rfl) ⟨1256064, by rfl⟩ : syracuseStep 3349505 = 2512129) B2512129
theorem B2233003 : Blo 2231435 2233003 := bstep (se 1 (by rfl) ⟨1674752, by rfl⟩ : syracuseStep 2233003 = 3349505) B3349505
theorem B5652301 : Blo 2231435 5652301 := bbase (se 3 (by rfl) ⟨1059806, by rfl⟩ : syracuseStep 5652301 = 2119613) (by norm_num)
theorem B7536401 : Blo 2231435 7536401 := bstep (se 2 (by rfl) ⟨2826150, by rfl⟩ : syracuseStep 7536401 = 5652301) B5652301
theorem B5024267 : Blo 2231435 5024267 := bstep (se 1 (by rfl) ⟨3768200, by rfl⟩ : syracuseStep 5024267 = 7536401) B7536401
theorem B3349511 : Blo 2231435 3349511 := bstep (se 1 (by rfl) ⟨2512133, by rfl⟩ : syracuseStep 3349511 = 5024267) B5024267
theorem B2233007 : Blo 2231435 2233007 := bstep (se 1 (by rfl) ⟨1674755, by rfl⟩ : syracuseStep 2233007 = 3349511) B3349511
theorem B3349517 : Blo 2231435 3349517 := bbase (se 3 (by rfl) ⟨628034, by rfl⟩ : syracuseStep 3349517 = 1256069) (by norm_num)
theorem B2233011 : Blo 2231435 2233011 := bstep (se 1 (by rfl) ⟨1674758, by rfl⟩ : syracuseStep 2233011 = 3349517) B3349517
theorem B5024285 : Blo 2231435 5024285 := bbase (se 3 (by rfl) ⟨942053, by rfl⟩ : syracuseStep 5024285 = 1884107) (by norm_num)
theorem B3349523 : Blo 2231435 3349523 := bstep (se 1 (by rfl) ⟨2512142, by rfl⟩ : syracuseStep 3349523 = 5024285) B5024285
theorem B2233015 : Blo 2231435 2233015 := bstep (se 1 (by rfl) ⟨1674761, by rfl⟩ : syracuseStep 2233015 = 3349523) B3349523
theorem B3768221 : Blo 2231435 3768221 := bbase (se 3 (by rfl) ⟨706541, by rfl⟩ : syracuseStep 3768221 = 1413083) (by norm_num)
theorem B2512147 : Blo 2231435 2512147 := bstep (se 1 (by rfl) ⟨1884110, by rfl⟩ : syracuseStep 2512147 = 3768221) B3768221
theorem B3349529 : Blo 2231435 3349529 := bstep (se 2 (by rfl) ⟨1256073, by rfl⟩ : syracuseStep 3349529 = 2512147) B2512147
theorem B2233019 : Blo 2231435 2233019 := bstep (se 1 (by rfl) ⟨1674764, by rfl⟩ : syracuseStep 2233019 = 3349529) B3349529
theorem B21461237 : Blo 2231435 21461237 := bbase (se 5 (by rfl) ⟨1005995, by rfl⟩ : syracuseStep 21461237 = 2011991) (by norm_num)
theorem B14307491 : Blo 2231435 14307491 := bstep (se 1 (by rfl) ⟨10730618, by rfl⟩ : syracuseStep 14307491 = 21461237) B21461237
theorem B9538327 : Blo 2231435 9538327 := bstep (se 1 (by rfl) ⟨7153745, by rfl⟩ : syracuseStep 9538327 = 14307491) B14307491
theorem B12717769 : Blo 2231435 12717769 := bstep (se 2 (by rfl) ⟨4769163, by rfl⟩ : syracuseStep 12717769 = 9538327) B9538327
theorem B16957025 : Blo 2231435 16957025 := bstep (se 2 (by rfl) ⟨6358884, by rfl⟩ : syracuseStep 16957025 = 12717769) B12717769
theorem B11304683 : Blo 2231435 11304683 := bstep (se 1 (by rfl) ⟨8478512, by rfl⟩ : syracuseStep 11304683 = 16957025) B16957025
theorem B7536455 : Blo 2231435 7536455 := bstep (se 1 (by rfl) ⟨5652341, by rfl⟩ : syracuseStep 7536455 = 11304683) B11304683
theorem B5024303 : Blo 2231435 5024303 := bstep (se 1 (by rfl) ⟨3768227, by rfl⟩ : syracuseStep 5024303 = 7536455) B7536455
theorem B3349535 : Blo 2231435 3349535 := bstep (se 1 (by rfl) ⟨2512151, by rfl⟩ : syracuseStep 3349535 = 5024303) B5024303
theorem B2233023 : Blo 2231435 2233023 := bstep (se 1 (by rfl) ⟨1674767, by rfl⟩ : syracuseStep 2233023 = 3349535) B3349535
theorem B3349541 : Blo 2231435 3349541 := bbase (se 4 (by rfl) ⟨314019, by rfl⟩ : syracuseStep 3349541 = 628039) (by norm_num)
theorem B2233027 : Blo 2231435 2233027 := bstep (se 1 (by rfl) ⟨1674770, by rfl⟩ : syracuseStep 2233027 = 3349541) B3349541
theorem B2826181 : Blo 2231435 2826181 := bbase (se 4 (by rfl) ⟨264954, by rfl⟩ : syracuseStep 2826181 = 529909) (by norm_num)
theorem B3768241 : Blo 2231435 3768241 := bstep (se 2 (by rfl) ⟨1413090, by rfl⟩ : syracuseStep 3768241 = 2826181) B2826181
theorem B5024321 : Blo 2231435 5024321 := bstep (se 2 (by rfl) ⟨1884120, by rfl⟩ : syracuseStep 5024321 = 3768241) B3768241
theorem B3349547 : Blo 2231435 3349547 := bstep (se 1 (by rfl) ⟨2512160, by rfl⟩ : syracuseStep 3349547 = 5024321) B5024321
theorem B2233031 : Blo 2231435 2233031 := bstep (se 1 (by rfl) ⟨1674773, by rfl⟩ : syracuseStep 2233031 = 3349547) B3349547
theorem B2512165 : Blo 2231435 2512165 := bbase (se 4 (by rfl) ⟨235515, by rfl⟩ : syracuseStep 2512165 = 471031) (by norm_num)
theorem B3349553 : Blo 2231435 3349553 := bstep (se 2 (by rfl) ⟨1256082, by rfl⟩ : syracuseStep 3349553 = 2512165) B2512165
theorem B2233035 : Blo 2231435 2233035 := bstep (se 1 (by rfl) ⟨1674776, by rfl⟩ : syracuseStep 2233035 = 3349553) B3349553
theorem B5365349 : Blo 2231435 5365349 := bbase (se 4 (by rfl) ⟨503001, by rfl⟩ : syracuseStep 5365349 = 1006003) (by norm_num)
theorem B3576899 : Blo 2231435 3576899 := bstep (se 1 (by rfl) ⟨2682674, by rfl⟩ : syracuseStep 3576899 = 5365349) B5365349
theorem B9538397 : Blo 2231435 9538397 := bstep (se 3 (by rfl) ⟨1788449, by rfl⟩ : syracuseStep 9538397 = 3576899) B3576899
theorem B6358931 : Blo 2231435 6358931 := bstep (se 1 (by rfl) ⟨4769198, by rfl⟩ : syracuseStep 6358931 = 9538397) B9538397
theorem B4239287 : Blo 2231435 4239287 := bstep (se 1 (by rfl) ⟨3179465, by rfl⟩ : syracuseStep 4239287 = 6358931) B6358931
theorem B2826191 : Blo 2231435 2826191 := bstep (se 1 (by rfl) ⟨2119643, by rfl⟩ : syracuseStep 2826191 = 4239287) B4239287
theorem B7536509 : Blo 2231435 7536509 := bstep (se 3 (by rfl) ⟨1413095, by rfl⟩ : syracuseStep 7536509 = 2826191) B2826191
theorem B5024339 : Blo 2231435 5024339 := bstep (se 1 (by rfl) ⟨3768254, by rfl⟩ : syracuseStep 5024339 = 7536509) B7536509
theorem B3349559 : Blo 2231435 3349559 := bstep (se 1 (by rfl) ⟨2512169, by rfl⟩ : syracuseStep 3349559 = 5024339) B5024339
theorem B2233039 : Blo 2231435 2233039 := bstep (se 1 (by rfl) ⟨1674779, by rfl⟩ : syracuseStep 2233039 = 3349559) B3349559
theorem B3349565 : Blo 2231435 3349565 := bbase (se 3 (by rfl) ⟨628043, by rfl⟩ : syracuseStep 3349565 = 1256087) (by norm_num)
theorem B2233043 : Blo 2231435 2233043 := bstep (se 1 (by rfl) ⟨1674782, by rfl⟩ : syracuseStep 2233043 = 3349565) B3349565
theorem B5024357 : Blo 2231435 5024357 := bbase (se 4 (by rfl) ⟨471033, by rfl⟩ : syracuseStep 5024357 = 942067) (by norm_num)
theorem B3349571 : Blo 2231435 3349571 := bstep (se 1 (by rfl) ⟨2512178, by rfl⟩ : syracuseStep 3349571 = 5024357) B5024357
theorem B2233047 : Blo 2231435 2233047 := bstep (se 1 (by rfl) ⟨1674785, by rfl⟩ : syracuseStep 2233047 = 3349571) B3349571
theorem B5652413 : Blo 2231435 5652413 := bbase (se 3 (by rfl) ⟨1059827, by rfl⟩ : syracuseStep 5652413 = 2119655) (by norm_num)
theorem B3768275 : Blo 2231435 3768275 := bstep (se 1 (by rfl) ⟨2826206, by rfl⟩ : syracuseStep 3768275 = 5652413) B5652413
theorem B2512183 : Blo 2231435 2512183 := bstep (se 1 (by rfl) ⟨1884137, by rfl⟩ : syracuseStep 2512183 = 3768275) B3768275
theorem B3349577 : Blo 2231435 3349577 := bstep (se 2 (by rfl) ⟨1256091, by rfl⟩ : syracuseStep 3349577 = 2512183) B2512183
theorem B2233051 : Blo 2231435 2233051 := bstep (se 1 (by rfl) ⟨1674788, by rfl⟩ : syracuseStep 2233051 = 3349577) B3349577
theorem B4239317 : Blo 2231435 4239317 := bbase (se 7 (by rfl) ⟨49679, by rfl⟩ : syracuseStep 4239317 = 99359) (by norm_num)
theorem B11304845 : Blo 2231435 11304845 := bstep (se 3 (by rfl) ⟨2119658, by rfl⟩ : syracuseStep 11304845 = 4239317) B4239317
theorem B7536563 : Blo 2231435 7536563 := bstep (se 1 (by rfl) ⟨5652422, by rfl⟩ : syracuseStep 7536563 = 11304845) B11304845
theorem B5024375 : Blo 2231435 5024375 := bstep (se 1 (by rfl) ⟨3768281, by rfl⟩ : syracuseStep 5024375 = 7536563) B7536563
theorem B3349583 : Blo 2231435 3349583 := bstep (se 1 (by rfl) ⟨2512187, by rfl⟩ : syracuseStep 3349583 = 5024375) B5024375
theorem B2233055 : Blo 2231435 2233055 := bstep (se 1 (by rfl) ⟨1674791, by rfl⟩ : syracuseStep 2233055 = 3349583) B3349583
theorem B3349589 : Blo 2231435 3349589 := bbase (se 8 (by rfl) ⟨19626, by rfl⟩ : syracuseStep 3349589 = 39253) (by norm_num)
theorem B2233059 : Blo 2231435 2233059 := bstep (se 1 (by rfl) ⟨1674794, by rfl⟩ : syracuseStep 2233059 = 3349589) B3349589
theorem B2546473 : Blo 2231435 2546473 := bbase (se 2 (by rfl) ⟨954927, by rfl⟩ : syracuseStep 2546473 = 1909855) (by norm_num)
theorem B3395297 : Blo 2231435 3395297 := bstep (se 2 (by rfl) ⟨1273236, by rfl⟩ : syracuseStep 3395297 = 2546473) B2546473
theorem B9054125 : Blo 2231435 9054125 := bstep (se 3 (by rfl) ⟨1697648, by rfl⟩ : syracuseStep 9054125 = 3395297) B3395297
theorem B6036083 : Blo 2231435 6036083 := bstep (se 1 (by rfl) ⟨4527062, by rfl⟩ : syracuseStep 6036083 = 9054125) B9054125
theorem B4024055 : Blo 2231435 4024055 := bstep (se 1 (by rfl) ⟨3018041, by rfl⟩ : syracuseStep 4024055 = 6036083) B6036083
theorem B2682703 : Blo 2231435 2682703 := bstep (se 1 (by rfl) ⟨2012027, by rfl⟩ : syracuseStep 2682703 = 4024055) B4024055
theorem B14307749 : Blo 2231435 14307749 := bstep (se 4 (by rfl) ⟨1341351, by rfl⟩ : syracuseStep 14307749 = 2682703) B2682703
theorem B9538499 : Blo 2231435 9538499 := bstep (se 1 (by rfl) ⟨7153874, by rfl⟩ : syracuseStep 9538499 = 14307749) B14307749
theorem B6358999 : Blo 2231435 6358999 := bstep (se 1 (by rfl) ⟨4769249, by rfl⟩ : syracuseStep 6358999 = 9538499) B9538499
theorem B8478665 : Blo 2231435 8478665 := bstep (se 2 (by rfl) ⟨3179499, by rfl⟩ : syracuseStep 8478665 = 6358999) B6358999
theorem B5652443 : Blo 2231435 5652443 := bstep (se 1 (by rfl) ⟨4239332, by rfl⟩ : syracuseStep 5652443 = 8478665) B8478665
theorem B3768295 : Blo 2231435 3768295 := bstep (se 1 (by rfl) ⟨2826221, by rfl⟩ : syracuseStep 3768295 = 5652443) B5652443
theorem B5024393 : Blo 2231435 5024393 := bstep (se 2 (by rfl) ⟨1884147, by rfl⟩ : syracuseStep 5024393 = 3768295) B3768295
theorem B3349595 : Blo 2231435 3349595 := bstep (se 1 (by rfl) ⟨2512196, by rfl⟩ : syracuseStep 3349595 = 5024393) B5024393
theorem B2233063 : Blo 2231435 2233063 := bstep (se 1 (by rfl) ⟨1674797, by rfl⟩ : syracuseStep 2233063 = 3349595) B3349595
theorem B2512201 : Blo 2231435 2512201 := bbase (se 2 (by rfl) ⟨942075, by rfl⟩ : syracuseStep 2512201 = 1884151) (by norm_num)
theorem B3349601 : Blo 2231435 3349601 := bstep (se 2 (by rfl) ⟨1256100, by rfl⟩ : syracuseStep 3349601 = 2512201) B2512201
theorem B2233067 : Blo 2231435 2233067 := bstep (se 1 (by rfl) ⟨1674800, by rfl⟩ : syracuseStep 2233067 = 3349601) B3349601
theorem B10185925 : Blo 2231435 10185925 := bbase (se 4 (by rfl) ⟨954930, by rfl⟩ : syracuseStep 10185925 = 1909861) (by norm_num)
theorem B13581233 : Blo 2231435 13581233 := bstep (se 2 (by rfl) ⟨5092962, by rfl⟩ : syracuseStep 13581233 = 10185925) B10185925
theorem B9054155 : Blo 2231435 9054155 := bstep (se 1 (by rfl) ⟨6790616, by rfl⟩ : syracuseStep 9054155 = 13581233) B13581233
theorem B6036103 : Blo 2231435 6036103 := bstep (se 1 (by rfl) ⟨4527077, by rfl⟩ : syracuseStep 6036103 = 9054155) B9054155
theorem B32192549 : Blo 2231435 32192549 := bstep (se 4 (by rfl) ⟨3018051, by rfl⟩ : syracuseStep 32192549 = 6036103) B6036103
theorem B21461699 : Blo 2231435 21461699 := bstep (se 1 (by rfl) ⟨16096274, by rfl⟩ : syracuseStep 21461699 = 32192549) B32192549
theorem B14307799 : Blo 2231435 14307799 := bstep (se 1 (by rfl) ⟨10730849, by rfl⟩ : syracuseStep 14307799 = 21461699) B21461699
theorem B19077065 : Blo 2231435 19077065 := bstep (se 2 (by rfl) ⟨7153899, by rfl⟩ : syracuseStep 19077065 = 14307799) B14307799
theorem B12718043 : Blo 2231435 12718043 := bstep (se 1 (by rfl) ⟨9538532, by rfl⟩ : syracuseStep 12718043 = 19077065) B19077065
theorem B8478695 : Blo 2231435 8478695 := bstep (se 1 (by rfl) ⟨6359021, by rfl⟩ : syracuseStep 8478695 = 12718043) B12718043
theorem B5652463 : Blo 2231435 5652463 := bstep (se 1 (by rfl) ⟨4239347, by rfl⟩ : syracuseStep 5652463 = 8478695) B8478695
theorem B7536617 : Blo 2231435 7536617 := bstep (se 2 (by rfl) ⟨2826231, by rfl⟩ : syracuseStep 7536617 = 5652463) B5652463
theorem B5024411 : Blo 2231435 5024411 := bstep (se 1 (by rfl) ⟨3768308, by rfl⟩ : syracuseStep 5024411 = 7536617) B7536617
theorem B3349607 : Blo 2231435 3349607 := bstep (se 1 (by rfl) ⟨2512205, by rfl⟩ : syracuseStep 3349607 = 5024411) B5024411
theorem B2233071 : Blo 2231435 2233071 := bstep (se 1 (by rfl) ⟨1674803, by rfl⟩ : syracuseStep 2233071 = 3349607) B3349607
theorem B3349613 : Blo 2231435 3349613 := bbase (se 3 (by rfl) ⟨628052, by rfl⟩ : syracuseStep 3349613 = 1256105) (by norm_num)
theorem B2233075 : Blo 2231435 2233075 := bstep (se 1 (by rfl) ⟨1674806, by rfl⟩ : syracuseStep 2233075 = 3349613) B3349613
theorem B5024429 : Blo 2231435 5024429 := bbase (se 3 (by rfl) ⟨942080, by rfl⟩ : syracuseStep 5024429 = 1884161) (by norm_num)
theorem B3349619 : Blo 2231435 3349619 := bstep (se 1 (by rfl) ⟨2512214, by rfl⟩ : syracuseStep 3349619 = 5024429) B5024429
theorem B2233079 : Blo 2231435 2233079 := bstep (se 1 (by rfl) ⟨1674809, by rfl⟩ : syracuseStep 2233079 = 3349619) B3349619
theorem B4769293 : Blo 2231435 4769293 := bbase (se 3 (by rfl) ⟨894242, by rfl⟩ : syracuseStep 4769293 = 1788485) (by norm_num)
theorem B6359057 : Blo 2231435 6359057 := bstep (se 2 (by rfl) ⟨2384646, by rfl⟩ : syracuseStep 6359057 = 4769293) B4769293
theorem B4239371 : Blo 2231435 4239371 := bstep (se 1 (by rfl) ⟨3179528, by rfl⟩ : syracuseStep 4239371 = 6359057) B6359057
theorem B2826247 : Blo 2231435 2826247 := bstep (se 1 (by rfl) ⟨2119685, by rfl⟩ : syracuseStep 2826247 = 4239371) B4239371
theorem B3768329 : Blo 2231435 3768329 := bstep (se 2 (by rfl) ⟨1413123, by rfl⟩ : syracuseStep 3768329 = 2826247) B2826247
theorem B2512219 : Blo 2231435 2512219 := bstep (se 1 (by rfl) ⟨1884164, by rfl⟩ : syracuseStep 2512219 = 3768329) B3768329
theorem B3349625 : Blo 2231435 3349625 := bstep (se 2 (by rfl) ⟨1256109, by rfl⟩ : syracuseStep 3349625 = 2512219) B2512219
theorem B2233083 : Blo 2231435 2233083 := bstep (se 1 (by rfl) ⟨1674812, by rfl⟩ : syracuseStep 2233083 = 3349625) B3349625
theorem B2417185 : Blo 2231435 2417185 := bbase (se 2 (by rfl) ⟨906444, by rfl⟩ : syracuseStep 2417185 = 1812889) (by norm_num)
theorem B12891653 : Blo 2231435 12891653 := bstep (se 4 (by rfl) ⟨1208592, by rfl⟩ : syracuseStep 12891653 = 2417185) B2417185
theorem B8594435 : Blo 2231435 8594435 := bstep (se 1 (by rfl) ⟨6445826, by rfl⟩ : syracuseStep 8594435 = 12891653) B12891653
theorem B5729623 : Blo 2231435 5729623 := bstep (se 1 (by rfl) ⟨4297217, by rfl⟩ : syracuseStep 5729623 = 8594435) B8594435
theorem B30557989 : Blo 2231435 30557989 := bstep (se 4 (by rfl) ⟨2864811, by rfl⟩ : syracuseStep 30557989 = 5729623) B5729623
theorem B40743985 : Blo 2231435 40743985 := bstep (se 2 (by rfl) ⟨15278994, by rfl⟩ : syracuseStep 40743985 = 30557989) B30557989
theorem B54325313 : Blo 2231435 54325313 := bstep (se 2 (by rfl) ⟨20371992, by rfl⟩ : syracuseStep 54325313 = 40743985) B40743985
theorem B36216875 : Blo 2231435 36216875 := bstep (se 1 (by rfl) ⟨27162656, by rfl⟩ : syracuseStep 36216875 = 54325313) B54325313
theorem B24144583 : Blo 2231435 24144583 := bstep (se 1 (by rfl) ⟨18108437, by rfl⟩ : syracuseStep 24144583 = 36216875) B36216875
theorem B32192777 : Blo 2231435 32192777 := bstep (se 2 (by rfl) ⟨12072291, by rfl⟩ : syracuseStep 32192777 = 24144583) B24144583
theorem B21461851 : Blo 2231435 21461851 := bstep (se 1 (by rfl) ⟨16096388, by rfl⟩ : syracuseStep 21461851 = 32192777) B32192777
theorem B28615801 : Blo 2231435 28615801 := bstep (se 2 (by rfl) ⟨10730925, by rfl⟩ : syracuseStep 28615801 = 21461851) B21461851
theorem B38154401 : Blo 2231435 38154401 := bstep (se 2 (by rfl) ⟨14307900, by rfl⟩ : syracuseStep 38154401 = 28615801) B28615801
theorem B25436267 : Blo 2231435 25436267 := bstep (se 1 (by rfl) ⟨19077200, by rfl⟩ : syracuseStep 25436267 = 38154401) B38154401
theorem B16957511 : Blo 2231435 16957511 := bstep (se 1 (by rfl) ⟨12718133, by rfl⟩ : syracuseStep 16957511 = 25436267) B25436267
theorem B11305007 : Blo 2231435 11305007 := bstep (se 1 (by rfl) ⟨8478755, by rfl⟩ : syracuseStep 11305007 = 16957511) B16957511
theorem B7536671 : Blo 2231435 7536671 := bstep (se 1 (by rfl) ⟨5652503, by rfl⟩ : syracuseStep 7536671 = 11305007) B11305007
theorem B5024447 : Blo 2231435 5024447 := bstep (se 1 (by rfl) ⟨3768335, by rfl⟩ : syracuseStep 5024447 = 7536671) B7536671
theorem B3349631 : Blo 2231435 3349631 := bstep (se 1 (by rfl) ⟨2512223, by rfl⟩ : syracuseStep 3349631 = 5024447) B5024447
theorem B2233087 : Blo 2231435 2233087 := bstep (se 1 (by rfl) ⟨1674815, by rfl⟩ : syracuseStep 2233087 = 3349631) B3349631
theorem B3349637 : Blo 2231435 3349637 := bbase (se 4 (by rfl) ⟨314028, by rfl⟩ : syracuseStep 3349637 = 628057) (by norm_num)
theorem B2233091 : Blo 2231435 2233091 := bstep (se 1 (by rfl) ⟨1674818, by rfl⟩ : syracuseStep 2233091 = 3349637) B3349637
theorem B3768349 : Blo 2231435 3768349 := bbase (se 3 (by rfl) ⟨706565, by rfl⟩ : syracuseStep 3768349 = 1413131) (by norm_num)
theorem B5024465 : Blo 2231435 5024465 := bstep (se 2 (by rfl) ⟨1884174, by rfl⟩ : syracuseStep 5024465 = 3768349) B3768349
theorem B3349643 : Blo 2231435 3349643 := bstep (se 1 (by rfl) ⟨2512232, by rfl⟩ : syracuseStep 3349643 = 5024465) B5024465
theorem B2233095 : Blo 2231435 2233095 := bstep (se 1 (by rfl) ⟨1674821, by rfl⟩ : syracuseStep 2233095 = 3349643) B3349643
theorem B2512237 : Blo 2231435 2512237 := bbase (se 3 (by rfl) ⟨471044, by rfl⟩ : syracuseStep 2512237 = 942089) (by norm_num)
theorem B3349649 : Blo 2231435 3349649 := bstep (se 2 (by rfl) ⟨1256118, by rfl⟩ : syracuseStep 3349649 = 2512237) B2512237
theorem B2233099 : Blo 2231435 2233099 := bstep (se 1 (by rfl) ⟨1674824, by rfl⟩ : syracuseStep 2233099 = 3349649) B3349649
theorem B7536725 : Blo 2231435 7536725 := bbase (se 8 (by rfl) ⟨44160, by rfl⟩ : syracuseStep 7536725 = 88321) (by norm_num)
theorem B5024483 : Blo 2231435 5024483 := bstep (se 1 (by rfl) ⟨3768362, by rfl⟩ : syracuseStep 5024483 = 7536725) B7536725
theorem B3349655 : Blo 2231435 3349655 := bstep (se 1 (by rfl) ⟨2512241, by rfl⟩ : syracuseStep 3349655 = 5024483) B5024483
theorem B2233103 : Blo 2231435 2233103 := bstep (se 1 (by rfl) ⟨1674827, by rfl⟩ : syracuseStep 2233103 = 3349655) B3349655
theorem B3349661 : Blo 2231435 3349661 := bbase (se 3 (by rfl) ⟨628061, by rfl⟩ : syracuseStep 3349661 = 1256123) (by norm_num)
theorem B2233107 : Blo 2231435 2233107 := bstep (se 1 (by rfl) ⟨1674830, by rfl⟩ : syracuseStep 2233107 = 3349661) B3349661
theorem B5024501 : Blo 2231435 5024501 := bbase (se 5 (by rfl) ⟨235523, by rfl⟩ : syracuseStep 5024501 = 471047) (by norm_num)
theorem B3349667 : Blo 2231435 3349667 := bstep (se 1 (by rfl) ⟨2512250, by rfl⟩ : syracuseStep 3349667 = 5024501) B5024501
theorem B2233111 : Blo 2231435 2233111 := bstep (se 1 (by rfl) ⟨1674833, by rfl⟩ : syracuseStep 2233111 = 3349667) B3349667
theorem B7849477 : Blo 2231435 7849477 := bbase (se 4 (by rfl) ⟨735888, by rfl⟩ : syracuseStep 7849477 = 1471777) (by norm_num)
theorem B41863877 : Blo 2231435 41863877 := bstep (se 4 (by rfl) ⟨3924738, by rfl⟩ : syracuseStep 41863877 = 7849477) B7849477
theorem B27909251 : Blo 2231435 27909251 := bstep (se 1 (by rfl) ⟨20931938, by rfl⟩ : syracuseStep 27909251 = 41863877) B41863877
theorem B18606167 : Blo 2231435 18606167 := bstep (se 1 (by rfl) ⟨13954625, by rfl⟩ : syracuseStep 18606167 = 27909251) B27909251
theorem B12404111 : Blo 2231435 12404111 := bstep (se 1 (by rfl) ⟨9303083, by rfl⟩ : syracuseStep 12404111 = 18606167) B18606167
theorem B33077629 : Blo 2231435 33077629 := bstep (se 3 (by rfl) ⟨6202055, by rfl⟩ : syracuseStep 33077629 = 12404111) B12404111
theorem B176414021 : Blo 2231435 176414021 := bstep (se 4 (by rfl) ⟨16538814, by rfl⟩ : syracuseStep 176414021 = 33077629) B33077629
theorem B117609347 : Blo 2231435 117609347 := bstep (se 1 (by rfl) ⟨88207010, by rfl⟩ : syracuseStep 117609347 = 176414021) B176414021
theorem B313624925 : Blo 2231435 313624925 := bstep (se 3 (by rfl) ⟨58804673, by rfl⟩ : syracuseStep 313624925 = 117609347) B117609347
theorem B209083283 : Blo 2231435 209083283 := bstep (se 1 (by rfl) ⟨156812462, by rfl⟩ : syracuseStep 209083283 = 313624925) B313624925
theorem B139388855 : Blo 2231435 139388855 := bstep (se 1 (by rfl) ⟨104541641, by rfl⟩ : syracuseStep 139388855 = 209083283) B209083283
theorem B371703613 : Blo 2231435 371703613 := bstep (se 3 (by rfl) ⟨69694427, by rfl⟩ : syracuseStep 371703613 = 139388855) B139388855
theorem B495604817 : Blo 2231435 495604817 := bstep (se 2 (by rfl) ⟨185851806, by rfl⟩ : syracuseStep 495604817 = 371703613) B371703613
theorem B330403211 : Blo 2231435 330403211 := bstep (se 1 (by rfl) ⟨247802408, by rfl⟩ : syracuseStep 330403211 = 495604817) B495604817
theorem B220268807 : Blo 2231435 220268807 := bstep (se 1 (by rfl) ⟨165201605, by rfl⟩ : syracuseStep 220268807 = 330403211) B330403211
theorem B146845871 : Blo 2231435 146845871 := bstep (se 1 (by rfl) ⟨110134403, by rfl⟩ : syracuseStep 146845871 = 220268807) B220268807
theorem B97897247 : Blo 2231435 97897247 := bstep (se 1 (by rfl) ⟨73422935, by rfl⟩ : syracuseStep 97897247 = 146845871) B146845871
theorem B65264831 : Blo 2231435 65264831 := bstep (se 1 (by rfl) ⟨48948623, by rfl⟩ : syracuseStep 65264831 = 97897247) B97897247
theorem B43509887 : Blo 2231435 43509887 := bstep (se 1 (by rfl) ⟨32632415, by rfl⟩ : syracuseStep 43509887 = 65264831) B65264831
theorem B29006591 : Blo 2231435 29006591 := bstep (se 1 (by rfl) ⟨21754943, by rfl⟩ : syracuseStep 29006591 = 43509887) B43509887
theorem B77350909 : Blo 2231435 77350909 := bstep (se 3 (by rfl) ⟨14503295, by rfl⟩ : syracuseStep 77350909 = 29006591) B29006591
theorem B103134545 : Blo 2231435 103134545 := bstep (se 2 (by rfl) ⟨38675454, by rfl⟩ : syracuseStep 103134545 = 77350909) B77350909
theorem B68756363 : Blo 2231435 68756363 := bstep (se 1 (by rfl) ⟨51567272, by rfl⟩ : syracuseStep 68756363 = 103134545) B103134545
theorem B45837575 : Blo 2231435 45837575 := bstep (se 1 (by rfl) ⟨34378181, by rfl⟩ : syracuseStep 45837575 = 68756363) B68756363
theorem B30558383 : Blo 2231435 30558383 := bstep (se 1 (by rfl) ⟨22918787, by rfl⟩ : syracuseStep 30558383 = 45837575) B45837575
theorem B20372255 : Blo 2231435 20372255 := bstep (se 1 (by rfl) ⟨15279191, by rfl⟩ : syracuseStep 20372255 = 30558383) B30558383
theorem B13581503 : Blo 2231435 13581503 := bstep (se 1 (by rfl) ⟨10186127, by rfl⟩ : syracuseStep 13581503 = 20372255) B20372255
theorem B9054335 : Blo 2231435 9054335 := bstep (se 1 (by rfl) ⟨6790751, by rfl⟩ : syracuseStep 9054335 = 13581503) B13581503
theorem B6036223 : Blo 2231435 6036223 := bstep (se 1 (by rfl) ⟨4527167, by rfl⟩ : syracuseStep 6036223 = 9054335) B9054335
theorem B8048297 : Blo 2231435 8048297 := bstep (se 2 (by rfl) ⟨3018111, by rfl⟩ : syracuseStep 8048297 = 6036223) B6036223
theorem B5365531 : Blo 2231435 5365531 := bstep (se 1 (by rfl) ⟨4024148, by rfl⟩ : syracuseStep 5365531 = 8048297) B8048297
theorem B28616165 : Blo 2231435 28616165 := bstep (se 4 (by rfl) ⟨2682765, by rfl⟩ : syracuseStep 28616165 = 5365531) B5365531
theorem B19077443 : Blo 2231435 19077443 := bstep (se 1 (by rfl) ⟨14308082, by rfl⟩ : syracuseStep 19077443 = 28616165) B28616165
theorem B12718295 : Blo 2231435 12718295 := bstep (se 1 (by rfl) ⟨9538721, by rfl⟩ : syracuseStep 12718295 = 19077443) B19077443
theorem B8478863 : Blo 2231435 8478863 := bstep (se 1 (by rfl) ⟨6359147, by rfl⟩ : syracuseStep 8478863 = 12718295) B12718295
theorem B5652575 : Blo 2231435 5652575 := bstep (se 1 (by rfl) ⟨4239431, by rfl⟩ : syracuseStep 5652575 = 8478863) B8478863
theorem B3768383 : Blo 2231435 3768383 := bstep (se 1 (by rfl) ⟨2826287, by rfl⟩ : syracuseStep 3768383 = 5652575) B5652575
theorem B2512255 : Blo 2231435 2512255 := bstep (se 1 (by rfl) ⟨1884191, by rfl⟩ : syracuseStep 2512255 = 3768383) B3768383
theorem B3349673 : Blo 2231435 3349673 := bstep (se 2 (by rfl) ⟨1256127, by rfl⟩ : syracuseStep 3349673 = 2512255) B2512255
theorem B2233115 : Blo 2231435 2233115 := bstep (se 1 (by rfl) ⟨1674836, by rfl⟩ : syracuseStep 2233115 = 3349673) B3349673
theorem B5365541 : Blo 2231435 5365541 := bbase (se 4 (by rfl) ⟨503019, by rfl⟩ : syracuseStep 5365541 = 1006039) (by norm_num)
theorem B3577027 : Blo 2231435 3577027 := bstep (se 1 (by rfl) ⟨2682770, by rfl⟩ : syracuseStep 3577027 = 5365541) B5365541
theorem B4769369 : Blo 2231435 4769369 := bstep (se 2 (by rfl) ⟨1788513, by rfl⟩ : syracuseStep 4769369 = 3577027) B3577027
theorem B3179579 : Blo 2231435 3179579 := bstep (se 1 (by rfl) ⟨2384684, by rfl⟩ : syracuseStep 3179579 = 4769369) B4769369
theorem B8478877 : Blo 2231435 8478877 := bstep (se 3 (by rfl) ⟨1589789, by rfl⟩ : syracuseStep 8478877 = 3179579) B3179579
theorem B11305169 : Blo 2231435 11305169 := bstep (se 2 (by rfl) ⟨4239438, by rfl⟩ : syracuseStep 11305169 = 8478877) B8478877
theorem B7536779 : Blo 2231435 7536779 := bstep (se 1 (by rfl) ⟨5652584, by rfl⟩ : syracuseStep 7536779 = 11305169) B11305169
theorem B5024519 : Blo 2231435 5024519 := bstep (se 1 (by rfl) ⟨3768389, by rfl⟩ : syracuseStep 5024519 = 7536779) B7536779
theorem B3349679 : Blo 2231435 3349679 := bstep (se 1 (by rfl) ⟨2512259, by rfl⟩ : syracuseStep 3349679 = 5024519) B5024519
theorem B2233119 : Blo 2231435 2233119 := bstep (se 1 (by rfl) ⟨1674839, by rfl⟩ : syracuseStep 2233119 = 3349679) B3349679
theorem B3349685 : Blo 2231435 3349685 := bbase (se 5 (by rfl) ⟨157016, by rfl⟩ : syracuseStep 3349685 = 314033) (by norm_num)
theorem B2233123 : Blo 2231435 2233123 := bstep (se 1 (by rfl) ⟨1674842, by rfl⟩ : syracuseStep 2233123 = 3349685) B3349685
theorem B5652605 : Blo 2231435 5652605 := bbase (se 3 (by rfl) ⟨1059863, by rfl⟩ : syracuseStep 5652605 = 2119727) (by norm_num)
theorem B3768403 : Blo 2231435 3768403 := bstep (se 1 (by rfl) ⟨2826302, by rfl⟩ : syracuseStep 3768403 = 5652605) B5652605
theorem B5024537 : Blo 2231435 5024537 := bstep (se 2 (by rfl) ⟨1884201, by rfl⟩ : syracuseStep 5024537 = 3768403) B3768403
theorem B3349691 : Blo 2231435 3349691 := bstep (se 1 (by rfl) ⟨2512268, by rfl⟩ : syracuseStep 3349691 = 5024537) B5024537
theorem B2233127 : Blo 2231435 2233127 := bstep (se 1 (by rfl) ⟨1674845, by rfl⟩ : syracuseStep 2233127 = 3349691) B3349691
theorem B2512273 : Blo 2231435 2512273 := bbase (se 2 (by rfl) ⟨942102, by rfl⟩ : syracuseStep 2512273 = 1884205) (by norm_num)
theorem B3349697 : Blo 2231435 3349697 := bstep (se 2 (by rfl) ⟨1256136, by rfl⟩ : syracuseStep 3349697 = 2512273) B2512273
theorem B2233131 : Blo 2231435 2233131 := bstep (se 1 (by rfl) ⟨1674848, by rfl⟩ : syracuseStep 2233131 = 3349697) B3349697
theorem B4239469 : Blo 2231435 4239469 := bbase (se 3 (by rfl) ⟨794900, by rfl⟩ : syracuseStep 4239469 = 1589801) (by norm_num)
theorem B5652625 : Blo 2231435 5652625 := bstep (se 2 (by rfl) ⟨2119734, by rfl⟩ : syracuseStep 5652625 = 4239469) B4239469
theorem B7536833 : Blo 2231435 7536833 := bstep (se 2 (by rfl) ⟨2826312, by rfl⟩ : syracuseStep 7536833 = 5652625) B5652625
theorem B5024555 : Blo 2231435 5024555 := bstep (se 1 (by rfl) ⟨3768416, by rfl⟩ : syracuseStep 5024555 = 7536833) B7536833
theorem B3349703 : Blo 2231435 3349703 := bstep (se 1 (by rfl) ⟨2512277, by rfl⟩ : syracuseStep 3349703 = 5024555) B5024555
theorem B2233135 : Blo 2231435 2233135 := bstep (se 1 (by rfl) ⟨1674851, by rfl⟩ : syracuseStep 2233135 = 3349703) B3349703
theorem B3349709 : Blo 2231435 3349709 := bbase (se 3 (by rfl) ⟨628070, by rfl⟩ : syracuseStep 3349709 = 1256141) (by norm_num)
theorem B2233139 : Blo 2231435 2233139 := bstep (se 1 (by rfl) ⟨1674854, by rfl⟩ : syracuseStep 2233139 = 3349709) B3349709
theorem B5024573 : Blo 2231435 5024573 := bbase (se 3 (by rfl) ⟨942107, by rfl⟩ : syracuseStep 5024573 = 1884215) (by norm_num)
theorem B3349715 : Blo 2231435 3349715 := bstep (se 1 (by rfl) ⟨2512286, by rfl⟩ : syracuseStep 3349715 = 5024573) B5024573
theorem B2233143 : Blo 2231435 2233143 := bstep (se 1 (by rfl) ⟨1674857, by rfl⟩ : syracuseStep 2233143 = 3349715) B3349715
theorem B3768437 : Blo 2231435 3768437 := bbase (se 5 (by rfl) ⟨176645, by rfl⟩ : syracuseStep 3768437 = 353291) (by norm_num)
theorem B2512291 : Blo 2231435 2512291 := bstep (se 1 (by rfl) ⟨1884218, by rfl⟩ : syracuseStep 2512291 = 3768437) B3768437
theorem B3349721 : Blo 2231435 3349721 := bstep (se 2 (by rfl) ⟨1256145, by rfl⟩ : syracuseStep 3349721 = 2512291) B2512291
theorem B2233147 : Blo 2231435 2233147 := bstep (se 1 (by rfl) ⟨1674860, by rfl⟩ : syracuseStep 2233147 = 3349721) B3349721
theorem B4769437 : Blo 2231435 4769437 := bbase (se 3 (by rfl) ⟨894269, by rfl⟩ : syracuseStep 4769437 = 1788539) (by norm_num)
theorem B6359249 : Blo 2231435 6359249 := bstep (se 2 (by rfl) ⟨2384718, by rfl⟩ : syracuseStep 6359249 = 4769437) B4769437
theorem B16957997 : Blo 2231435 16957997 := bstep (se 3 (by rfl) ⟨3179624, by rfl⟩ : syracuseStep 16957997 = 6359249) B6359249
theorem B11305331 : Blo 2231435 11305331 := bstep (se 1 (by rfl) ⟨8478998, by rfl⟩ : syracuseStep 11305331 = 16957997) B16957997
theorem B7536887 : Blo 2231435 7536887 := bstep (se 1 (by rfl) ⟨5652665, by rfl⟩ : syracuseStep 7536887 = 11305331) B11305331
theorem B5024591 : Blo 2231435 5024591 := bstep (se 1 (by rfl) ⟨3768443, by rfl⟩ : syracuseStep 5024591 = 7536887) B7536887
theorem B3349727 : Blo 2231435 3349727 := bstep (se 1 (by rfl) ⟨2512295, by rfl⟩ : syracuseStep 3349727 = 5024591) B5024591
theorem B2233151 : Blo 2231435 2233151 := bstep (se 1 (by rfl) ⟨1674863, by rfl⟩ : syracuseStep 2233151 = 3349727) B3349727
theorem B3349733 : Blo 2231435 3349733 := bbase (se 4 (by rfl) ⟨314037, by rfl⟩ : syracuseStep 3349733 = 628075) (by norm_num)
theorem B2233155 : Blo 2231435 2233155 := bstep (se 1 (by rfl) ⟨1674866, by rfl⟩ : syracuseStep 2233155 = 3349733) B3349733
theorem B5093165 : Blo 2231435 5093165 := bbase (se 3 (by rfl) ⟨954968, by rfl⟩ : syracuseStep 5093165 = 1909937) (by norm_num)
theorem B3395443 : Blo 2231435 3395443 := bstep (se 1 (by rfl) ⟨2546582, by rfl⟩ : syracuseStep 3395443 = 5093165) B5093165
theorem B4527257 : Blo 2231435 4527257 := bstep (se 2 (by rfl) ⟨1697721, by rfl⟩ : syracuseStep 4527257 = 3395443) B3395443
theorem B12072685 : Blo 2231435 12072685 := bstep (se 3 (by rfl) ⟨2263628, by rfl⟩ : syracuseStep 12072685 = 4527257) B4527257
theorem B16096913 : Blo 2231435 16096913 := bstep (se 2 (by rfl) ⟨6036342, by rfl⟩ : syracuseStep 16096913 = 12072685) B12072685
theorem B10731275 : Blo 2231435 10731275 := bstep (se 1 (by rfl) ⟨8048456, by rfl⟩ : syracuseStep 10731275 = 16096913) B16096913
theorem B7154183 : Blo 2231435 7154183 := bstep (se 1 (by rfl) ⟨5365637, by rfl⟩ : syracuseStep 7154183 = 10731275) B10731275
theorem B4769455 : Blo 2231435 4769455 := bstep (se 1 (by rfl) ⟨3577091, by rfl⟩ : syracuseStep 4769455 = 7154183) B7154183
theorem B6359273 : Blo 2231435 6359273 := bstep (se 2 (by rfl) ⟨2384727, by rfl⟩ : syracuseStep 6359273 = 4769455) B4769455
theorem B4239515 : Blo 2231435 4239515 := bstep (se 1 (by rfl) ⟨3179636, by rfl⟩ : syracuseStep 4239515 = 6359273) B6359273
theorem B2826343 : Blo 2231435 2826343 := bstep (se 1 (by rfl) ⟨2119757, by rfl⟩ : syracuseStep 2826343 = 4239515) B4239515
theorem B3768457 : Blo 2231435 3768457 := bstep (se 2 (by rfl) ⟨1413171, by rfl⟩ : syracuseStep 3768457 = 2826343) B2826343
theorem B5024609 : Blo 2231435 5024609 := bstep (se 2 (by rfl) ⟨1884228, by rfl⟩ : syracuseStep 5024609 = 3768457) B3768457
theorem B3349739 : Blo 2231435 3349739 := bstep (se 1 (by rfl) ⟨2512304, by rfl⟩ : syracuseStep 3349739 = 5024609) B5024609
theorem B2233159 : Blo 2231435 2233159 := bstep (se 1 (by rfl) ⟨1674869, by rfl⟩ : syracuseStep 2233159 = 3349739) B3349739
theorem B2512309 : Blo 2231435 2512309 := bbase (se 5 (by rfl) ⟨117764, by rfl⟩ : syracuseStep 2512309 = 235529) (by norm_num)
theorem B3349745 : Blo 2231435 3349745 := bstep (se 2 (by rfl) ⟨1256154, by rfl⟩ : syracuseStep 3349745 = 2512309) B2512309
theorem B2233163 : Blo 2231435 2233163 := bstep (se 1 (by rfl) ⟨1674872, by rfl⟩ : syracuseStep 2233163 = 3349745) B3349745
theorem B2826353 : Blo 2231435 2826353 := bbase (se 2 (by rfl) ⟨1059882, by rfl⟩ : syracuseStep 2826353 = 2119765) (by norm_num)
theorem B7536941 : Blo 2231435 7536941 := bstep (se 3 (by rfl) ⟨1413176, by rfl⟩ : syracuseStep 7536941 = 2826353) B2826353
theorem B5024627 : Blo 2231435 5024627 := bstep (se 1 (by rfl) ⟨3768470, by rfl⟩ : syracuseStep 5024627 = 7536941) B7536941
theorem B3349751 : Blo 2231435 3349751 := bstep (se 1 (by rfl) ⟨2512313, by rfl⟩ : syracuseStep 3349751 = 5024627) B5024627
theorem B2233167 : Blo 2231435 2233167 := bstep (se 1 (by rfl) ⟨1674875, by rfl⟩ : syracuseStep 2233167 = 3349751) B3349751
theorem B3349757 : Blo 2231435 3349757 := bbase (se 3 (by rfl) ⟨628079, by rfl⟩ : syracuseStep 3349757 = 1256159) (by norm_num)
theorem B2233171 : Blo 2231435 2233171 := bstep (se 1 (by rfl) ⟨1674878, by rfl⟩ : syracuseStep 2233171 = 3349757) B3349757
theorem B5024645 : Blo 2231435 5024645 := bbase (se 4 (by rfl) ⟨471060, by rfl⟩ : syracuseStep 5024645 = 942121) (by norm_num)
theorem B3349763 : Blo 2231435 3349763 := bstep (se 1 (by rfl) ⟨2512322, by rfl⟩ : syracuseStep 3349763 = 5024645) B5024645
theorem B2233175 : Blo 2231435 2233175 := bstep (se 1 (by rfl) ⟨1674881, by rfl⟩ : syracuseStep 2233175 = 3349763) B3349763
theorem B2384749 : Blo 2231435 2384749 := bbase (se 3 (by rfl) ⟨447140, by rfl⟩ : syracuseStep 2384749 = 894281) (by norm_num)
theorem B3179665 : Blo 2231435 3179665 := bstep (se 2 (by rfl) ⟨1192374, by rfl⟩ : syracuseStep 3179665 = 2384749) B2384749
theorem B4239553 : Blo 2231435 4239553 := bstep (se 2 (by rfl) ⟨1589832, by rfl⟩ : syracuseStep 4239553 = 3179665) B3179665
theorem B5652737 : Blo 2231435 5652737 := bstep (se 2 (by rfl) ⟨2119776, by rfl⟩ : syracuseStep 5652737 = 4239553) B4239553
theorem B3768491 : Blo 2231435 3768491 := bstep (se 1 (by rfl) ⟨2826368, by rfl⟩ : syracuseStep 3768491 = 5652737) B5652737
theorem B2512327 : Blo 2231435 2512327 := bstep (se 1 (by rfl) ⟨1884245, by rfl⟩ : syracuseStep 2512327 = 3768491) B3768491
theorem B3349769 : Blo 2231435 3349769 := bstep (se 2 (by rfl) ⟨1256163, by rfl⟩ : syracuseStep 3349769 = 2512327) B2512327
theorem B2233179 : Blo 2231435 2233179 := bstep (se 1 (by rfl) ⟨1674884, by rfl⟩ : syracuseStep 2233179 = 3349769) B3349769
theorem B11305493 : Blo 2231435 11305493 := bbase (se 6 (by rfl) ⟨264972, by rfl⟩ : syracuseStep 11305493 = 529945) (by norm_num)
theorem B7536995 : Blo 2231435 7536995 := bstep (se 1 (by rfl) ⟨5652746, by rfl⟩ : syracuseStep 7536995 = 11305493) B11305493
theorem B5024663 : Blo 2231435 5024663 := bstep (se 1 (by rfl) ⟨3768497, by rfl⟩ : syracuseStep 5024663 = 7536995) B7536995
theorem B3349775 : Blo 2231435 3349775 := bstep (se 1 (by rfl) ⟨2512331, by rfl⟩ : syracuseStep 3349775 = 5024663) B5024663
theorem B2233183 : Blo 2231435 2233183 := bstep (se 1 (by rfl) ⟨1674887, by rfl⟩ : syracuseStep 2233183 = 3349775) B3349775
theorem B3349781 : Blo 2231435 3349781 := bbase (se 6 (by rfl) ⟨78510, by rfl⟩ : syracuseStep 3349781 = 157021) (by norm_num)
theorem B2233187 : Blo 2231435 2233187 := bstep (se 1 (by rfl) ⟨1674890, by rfl⟩ : syracuseStep 2233187 = 3349781) B3349781
theorem B4024285 : Blo 2231435 4024285 := bbase (se 3 (by rfl) ⟨754553, by rfl⟩ : syracuseStep 4024285 = 1509107) (by norm_num)
theorem B21462853 : Blo 2231435 21462853 := bstep (se 4 (by rfl) ⟨2012142, by rfl⟩ : syracuseStep 21462853 = 4024285) B4024285
theorem B28617137 : Blo 2231435 28617137 := bstep (se 2 (by rfl) ⟨10731426, by rfl⟩ : syracuseStep 28617137 = 21462853) B21462853
theorem B19078091 : Blo 2231435 19078091 := bstep (se 1 (by rfl) ⟨14308568, by rfl⟩ : syracuseStep 19078091 = 28617137) B28617137
theorem B12718727 : Blo 2231435 12718727 := bstep (se 1 (by rfl) ⟨9539045, by rfl⟩ : syracuseStep 12718727 = 19078091) B19078091
theorem B8479151 : Blo 2231435 8479151 := bstep (se 1 (by rfl) ⟨6359363, by rfl⟩ : syracuseStep 8479151 = 12718727) B12718727
theorem B5652767 : Blo 2231435 5652767 := bstep (se 1 (by rfl) ⟨4239575, by rfl⟩ : syracuseStep 5652767 = 8479151) B8479151
theorem B3768511 : Blo 2231435 3768511 := bstep (se 1 (by rfl) ⟨2826383, by rfl⟩ : syracuseStep 3768511 = 5652767) B5652767
theorem B5024681 : Blo 2231435 5024681 := bstep (se 2 (by rfl) ⟨1884255, by rfl⟩ : syracuseStep 5024681 = 3768511) B3768511
theorem B3349787 : Blo 2231435 3349787 := bstep (se 1 (by rfl) ⟨2512340, by rfl⟩ : syracuseStep 3349787 = 5024681) B5024681
theorem B2233191 : Blo 2231435 2233191 := bstep (se 1 (by rfl) ⟨1674893, by rfl⟩ : syracuseStep 2233191 = 3349787) B3349787
theorem B2512345 : Blo 2231435 2512345 := bbase (se 2 (by rfl) ⟨942129, by rfl⟩ : syracuseStep 2512345 = 1884259) (by norm_num)
theorem B3349793 : Blo 2231435 3349793 := bstep (se 2 (by rfl) ⟨1256172, by rfl⟩ : syracuseStep 3349793 = 2512345) B2512345
theorem B2233195 : Blo 2231435 2233195 := bstep (se 1 (by rfl) ⟨1674896, by rfl⟩ : syracuseStep 2233195 = 3349793) B3349793
theorem B3179693 : Blo 2231435 3179693 := bbase (se 3 (by rfl) ⟨596192, by rfl⟩ : syracuseStep 3179693 = 1192385) (by norm_num)
theorem B8479181 : Blo 2231435 8479181 := bstep (se 3 (by rfl) ⟨1589846, by rfl⟩ : syracuseStep 8479181 = 3179693) B3179693
theorem B5652787 : Blo 2231435 5652787 := bstep (se 1 (by rfl) ⟨4239590, by rfl⟩ : syracuseStep 5652787 = 8479181) B8479181
theorem B7537049 : Blo 2231435 7537049 := bstep (se 2 (by rfl) ⟨2826393, by rfl⟩ : syracuseStep 7537049 = 5652787) B5652787
theorem B5024699 : Blo 2231435 5024699 := bstep (se 1 (by rfl) ⟨3768524, by rfl⟩ : syracuseStep 5024699 = 7537049) B7537049
theorem B3349799 : Blo 2231435 3349799 := bstep (se 1 (by rfl) ⟨2512349, by rfl⟩ : syracuseStep 3349799 = 5024699) B5024699
theorem B2233199 : Blo 2231435 2233199 := bstep (se 1 (by rfl) ⟨1674899, by rfl⟩ : syracuseStep 2233199 = 3349799) B3349799
theorem B3349805 : Blo 2231435 3349805 := bbase (se 3 (by rfl) ⟨628088, by rfl⟩ : syracuseStep 3349805 = 1256177) (by norm_num)
theorem B2233203 : Blo 2231435 2233203 := bstep (se 1 (by rfl) ⟨1674902, by rfl⟩ : syracuseStep 2233203 = 3349805) B3349805
theorem B5024717 : Blo 2231435 5024717 := bbase (se 3 (by rfl) ⟨942134, by rfl⟩ : syracuseStep 5024717 = 1884269) (by norm_num)
theorem B3349811 : Blo 2231435 3349811 := bstep (se 1 (by rfl) ⟨2512358, by rfl⟩ : syracuseStep 3349811 = 5024717) B5024717
theorem B2233207 : Blo 2231435 2233207 := bstep (se 1 (by rfl) ⟨1674905, by rfl⟩ : syracuseStep 2233207 = 3349811) B3349811
theorem B2826409 : Blo 2231435 2826409 := bbase (se 2 (by rfl) ⟨1059903, by rfl⟩ : syracuseStep 2826409 = 2119807) (by norm_num)
theorem B3768545 : Blo 2231435 3768545 := bstep (se 2 (by rfl) ⟨1413204, by rfl⟩ : syracuseStep 3768545 = 2826409) B2826409
theorem B2512363 : Blo 2231435 2512363 := bstep (se 1 (by rfl) ⟨1884272, by rfl⟩ : syracuseStep 2512363 = 3768545) B3768545
theorem B3349817 : Blo 2231435 3349817 := bstep (se 2 (by rfl) ⟨1256181, by rfl⟩ : syracuseStep 3349817 = 2512363) B2512363
theorem B2233211 : Blo 2231435 2233211 := bstep (se 1 (by rfl) ⟨1674908, by rfl⟩ : syracuseStep 2233211 = 3349817) B3349817
theorem B10731541 : Blo 2231435 10731541 := bbase (se 6 (by rfl) ⟨251520, by rfl⟩ : syracuseStep 10731541 = 503041) (by norm_num)
theorem B14308721 : Blo 2231435 14308721 := bstep (se 2 (by rfl) ⟨5365770, by rfl⟩ : syracuseStep 14308721 = 10731541) B10731541
theorem B9539147 : Blo 2231435 9539147 := bstep (se 1 (by rfl) ⟨7154360, by rfl⟩ : syracuseStep 9539147 = 14308721) B14308721
theorem B25437725 : Blo 2231435 25437725 := bstep (se 3 (by rfl) ⟨4769573, by rfl⟩ : syracuseStep 25437725 = 9539147) B9539147
theorem B16958483 : Blo 2231435 16958483 := bstep (se 1 (by rfl) ⟨12718862, by rfl⟩ : syracuseStep 16958483 = 25437725) B25437725
theorem B11305655 : Blo 2231435 11305655 := bstep (se 1 (by rfl) ⟨8479241, by rfl⟩ : syracuseStep 11305655 = 16958483) B16958483
theorem B7537103 : Blo 2231435 7537103 := bstep (se 1 (by rfl) ⟨5652827, by rfl⟩ : syracuseStep 7537103 = 11305655) B11305655
theorem B5024735 : Blo 2231435 5024735 := bstep (se 1 (by rfl) ⟨3768551, by rfl⟩ : syracuseStep 5024735 = 7537103) B7537103
theorem B3349823 : Blo 2231435 3349823 := bstep (se 1 (by rfl) ⟨2512367, by rfl⟩ : syracuseStep 3349823 = 5024735) B5024735
theorem B2233215 : Blo 2231435 2233215 := bstep (se 1 (by rfl) ⟨1674911, by rfl⟩ : syracuseStep 2233215 = 3349823) B3349823
theorem B3349829 : Blo 2231435 3349829 := bbase (se 4 (by rfl) ⟨314046, by rfl⟩ : syracuseStep 3349829 = 628093) (by norm_num)
theorem B2233219 : Blo 2231435 2233219 := bstep (se 1 (by rfl) ⟨1674914, by rfl⟩ : syracuseStep 2233219 = 3349829) B3349829
theorem B3768565 : Blo 2231435 3768565 := bbase (se 5 (by rfl) ⟨176651, by rfl⟩ : syracuseStep 3768565 = 353303) (by norm_num)
theorem B5024753 : Blo 2231435 5024753 := bstep (se 2 (by rfl) ⟨1884282, by rfl⟩ : syracuseStep 5024753 = 3768565) B3768565
theorem B3349835 : Blo 2231435 3349835 := bstep (se 1 (by rfl) ⟨2512376, by rfl⟩ : syracuseStep 3349835 = 5024753) B5024753
theorem B2233223 : Blo 2231435 2233223 := bstep (se 1 (by rfl) ⟨1674917, by rfl⟩ : syracuseStep 2233223 = 3349835) B3349835
theorem B2512381 : Blo 2231435 2512381 := bbase (se 3 (by rfl) ⟨471071, by rfl⟩ : syracuseStep 2512381 = 942143) (by norm_num)
theorem B3349841 : Blo 2231435 3349841 := bstep (se 2 (by rfl) ⟨1256190, by rfl⟩ : syracuseStep 3349841 = 2512381) B2512381
theorem B2233227 : Blo 2231435 2233227 := bstep (se 1 (by rfl) ⟨1674920, by rfl⟩ : syracuseStep 2233227 = 3349841) B3349841
theorem B7537157 : Blo 2231435 7537157 := bbase (se 4 (by rfl) ⟨706608, by rfl⟩ : syracuseStep 7537157 = 1413217) (by norm_num)
theorem B5024771 : Blo 2231435 5024771 := bstep (se 1 (by rfl) ⟨3768578, by rfl⟩ : syracuseStep 5024771 = 7537157) B7537157
theorem B3349847 : Blo 2231435 3349847 := bstep (se 1 (by rfl) ⟨2512385, by rfl⟩ : syracuseStep 3349847 = 5024771) B5024771
theorem B2233231 : Blo 2231435 2233231 := bstep (se 1 (by rfl) ⟨1674923, by rfl⟩ : syracuseStep 2233231 = 3349847) B3349847
theorem B3349853 : Blo 2231435 3349853 := bbase (se 3 (by rfl) ⟨628097, by rfl⟩ : syracuseStep 3349853 = 1256195) (by norm_num)
theorem B2233235 : Blo 2231435 2233235 := bstep (se 1 (by rfl) ⟨1674926, by rfl⟩ : syracuseStep 2233235 = 3349853) B3349853
theorem B5024789 : Blo 2231435 5024789 := bbase (se 6 (by rfl) ⟨117768, by rfl⟩ : syracuseStep 5024789 = 235537) (by norm_num)
theorem B3349859 : Blo 2231435 3349859 := bstep (se 1 (by rfl) ⟨2512394, by rfl⟩ : syracuseStep 3349859 = 5024789) B5024789
theorem B2233239 : Blo 2231435 2233239 := bstep (se 1 (by rfl) ⟨1674929, by rfl⟩ : syracuseStep 2233239 = 3349859) B3349859
theorem B8479349 : Blo 2231435 8479349 := bbase (se 5 (by rfl) ⟨397469, by rfl⟩ : syracuseStep 8479349 = 794939) (by norm_num)
theorem B5652899 : Blo 2231435 5652899 := bstep (se 1 (by rfl) ⟨4239674, by rfl⟩ : syracuseStep 5652899 = 8479349) B8479349
theorem B3768599 : Blo 2231435 3768599 := bstep (se 1 (by rfl) ⟨2826449, by rfl⟩ : syracuseStep 3768599 = 5652899) B5652899
theorem B2512399 : Blo 2231435 2512399 := bstep (se 1 (by rfl) ⟨1884299, by rfl⟩ : syracuseStep 2512399 = 3768599) B3768599
theorem B3349865 : Blo 2231435 3349865 := bstep (se 2 (by rfl) ⟨1256199, by rfl⟩ : syracuseStep 3349865 = 2512399) B2512399
theorem B2233243 : Blo 2231435 2233243 := bstep (se 1 (by rfl) ⟨1674932, by rfl⟩ : syracuseStep 2233243 = 3349865) B3349865
theorem B2384821 : Blo 2231435 2384821 := bbase (se 5 (by rfl) ⟨111788, by rfl⟩ : syracuseStep 2384821 = 223577) (by norm_num)
theorem B12719045 : Blo 2231435 12719045 := bstep (se 4 (by rfl) ⟨1192410, by rfl⟩ : syracuseStep 12719045 = 2384821) B2384821
theorem B8479363 : Blo 2231435 8479363 := bstep (se 1 (by rfl) ⟨6359522, by rfl⟩ : syracuseStep 8479363 = 12719045) B12719045
theorem B11305817 : Blo 2231435 11305817 := bstep (se 2 (by rfl) ⟨4239681, by rfl⟩ : syracuseStep 11305817 = 8479363) B8479363
theorem B7537211 : Blo 2231435 7537211 := bstep (se 1 (by rfl) ⟨5652908, by rfl⟩ : syracuseStep 7537211 = 11305817) B11305817
theorem B5024807 : Blo 2231435 5024807 := bstep (se 1 (by rfl) ⟨3768605, by rfl⟩ : syracuseStep 5024807 = 7537211) B7537211
theorem B3349871 : Blo 2231435 3349871 := bstep (se 1 (by rfl) ⟨2512403, by rfl⟩ : syracuseStep 3349871 = 5024807) B5024807
theorem B2233247 : Blo 2231435 2233247 := bstep (se 1 (by rfl) ⟨1674935, by rfl⟩ : syracuseStep 2233247 = 3349871) B3349871
theorem B3349877 : Blo 2231435 3349877 := bbase (se 5 (by rfl) ⟨157025, by rfl⟩ : syracuseStep 3349877 = 314051) (by norm_num)
theorem B2233251 : Blo 2231435 2233251 := bstep (se 1 (by rfl) ⟨1674938, by rfl⟩ : syracuseStep 2233251 = 3349877) B3349877
theorem B3179773 : Blo 2231435 3179773 := bbase (se 3 (by rfl) ⟨596207, by rfl⟩ : syracuseStep 3179773 = 1192415) (by norm_num)
theorem B4239697 : Blo 2231435 4239697 := bstep (se 2 (by rfl) ⟨1589886, by rfl⟩ : syracuseStep 4239697 = 3179773) B3179773
theorem B5652929 : Blo 2231435 5652929 := bstep (se 2 (by rfl) ⟨2119848, by rfl⟩ : syracuseStep 5652929 = 4239697) B4239697
theorem B3768619 : Blo 2231435 3768619 := bstep (se 1 (by rfl) ⟨2826464, by rfl⟩ : syracuseStep 3768619 = 5652929) B5652929
theorem B5024825 : Blo 2231435 5024825 := bstep (se 2 (by rfl) ⟨1884309, by rfl⟩ : syracuseStep 5024825 = 3768619) B3768619
theorem B3349883 : Blo 2231435 3349883 := bstep (se 1 (by rfl) ⟨2512412, by rfl⟩ : syracuseStep 3349883 = 5024825) B5024825
theorem B2233255 : Blo 2231435 2233255 := bstep (se 1 (by rfl) ⟨1674941, by rfl⟩ : syracuseStep 2233255 = 3349883) B3349883
theorem B2512417 : Blo 2231435 2512417 := bbase (se 2 (by rfl) ⟨942156, by rfl⟩ : syracuseStep 2512417 = 1884313) (by norm_num)
theorem B3349889 : Blo 2231435 3349889 := bstep (se 2 (by rfl) ⟨1256208, by rfl⟩ : syracuseStep 3349889 = 2512417) B2512417
theorem B2233259 : Blo 2231435 2233259 := bstep (se 1 (by rfl) ⟨1674944, by rfl⟩ : syracuseStep 2233259 = 3349889) B3349889
theorem B5652949 : Blo 2231435 5652949 := bbase (se 7 (by rfl) ⟨66245, by rfl⟩ : syracuseStep 5652949 = 132491) (by norm_num)
theorem B7537265 : Blo 2231435 7537265 := bstep (se 2 (by rfl) ⟨2826474, by rfl⟩ : syracuseStep 7537265 = 5652949) B5652949
theorem B5024843 : Blo 2231435 5024843 := bstep (se 1 (by rfl) ⟨3768632, by rfl⟩ : syracuseStep 5024843 = 7537265) B7537265
theorem B3349895 : Blo 2231435 3349895 := bstep (se 1 (by rfl) ⟨2512421, by rfl⟩ : syracuseStep 3349895 = 5024843) B5024843
theorem B2233263 : Blo 2231435 2233263 := bstep (se 1 (by rfl) ⟨1674947, by rfl⟩ : syracuseStep 2233263 = 3349895) B3349895
theorem B3349901 : Blo 2231435 3349901 := bbase (se 3 (by rfl) ⟨628106, by rfl⟩ : syracuseStep 3349901 = 1256213) (by norm_num)
theorem B2233267 : Blo 2231435 2233267 := bstep (se 1 (by rfl) ⟨1674950, by rfl⟩ : syracuseStep 2233267 = 3349901) B3349901
theorem B5024861 : Blo 2231435 5024861 := bbase (se 3 (by rfl) ⟨942161, by rfl⟩ : syracuseStep 5024861 = 1884323) (by norm_num)
theorem B3349907 : Blo 2231435 3349907 := bstep (se 1 (by rfl) ⟨2512430, by rfl⟩ : syracuseStep 3349907 = 5024861) B5024861
theorem B2233271 : Blo 2231435 2233271 := bstep (se 1 (by rfl) ⟨1674953, by rfl⟩ : syracuseStep 2233271 = 3349907) B3349907
theorem B3768653 : Blo 2231435 3768653 := bbase (se 3 (by rfl) ⟨706622, by rfl⟩ : syracuseStep 3768653 = 1413245) (by norm_num)
theorem B2512435 : Blo 2231435 2512435 := bstep (se 1 (by rfl) ⟨1884326, by rfl⟩ : syracuseStep 2512435 = 3768653) B3768653
theorem B3349913 : Blo 2231435 3349913 := bstep (se 2 (by rfl) ⟨1256217, by rfl⟩ : syracuseStep 3349913 = 2512435) B2512435
theorem B2233275 : Blo 2231435 2233275 := bstep (se 1 (by rfl) ⟨1674956, by rfl⟩ : syracuseStep 2233275 = 3349913) B3349913
theorem B5093437 : Blo 2231435 5093437 := bbase (se 3 (by rfl) ⟨955019, by rfl⟩ : syracuseStep 5093437 = 1910039) (by norm_num)
theorem B6791249 : Blo 2231435 6791249 := bstep (se 2 (by rfl) ⟨2546718, by rfl⟩ : syracuseStep 6791249 = 5093437) B5093437
theorem B4527499 : Blo 2231435 4527499 := bstep (se 1 (by rfl) ⟨3395624, by rfl⟩ : syracuseStep 4527499 = 6791249) B6791249
theorem B6036665 : Blo 2231435 6036665 := bstep (se 2 (by rfl) ⟨2263749, by rfl⟩ : syracuseStep 6036665 = 4527499) B4527499
theorem B16097773 : Blo 2231435 16097773 := bstep (se 3 (by rfl) ⟨3018332, by rfl⟩ : syracuseStep 16097773 = 6036665) B6036665
theorem B21463697 : Blo 2231435 21463697 := bstep (se 2 (by rfl) ⟨8048886, by rfl⟩ : syracuseStep 21463697 = 16097773) B16097773
theorem B14309131 : Blo 2231435 14309131 := bstep (se 1 (by rfl) ⟨10731848, by rfl⟩ : syracuseStep 14309131 = 21463697) B21463697
theorem B19078841 : Blo 2231435 19078841 := bstep (se 2 (by rfl) ⟨7154565, by rfl⟩ : syracuseStep 19078841 = 14309131) B14309131
theorem B12719227 : Blo 2231435 12719227 := bstep (se 1 (by rfl) ⟨9539420, by rfl⟩ : syracuseStep 12719227 = 19078841) B19078841
theorem B16958969 : Blo 2231435 16958969 := bstep (se 2 (by rfl) ⟨6359613, by rfl⟩ : syracuseStep 16958969 = 12719227) B12719227
theorem B11305979 : Blo 2231435 11305979 := bstep (se 1 (by rfl) ⟨8479484, by rfl⟩ : syracuseStep 11305979 = 16958969) B16958969
theorem B7537319 : Blo 2231435 7537319 := bstep (se 1 (by rfl) ⟨5652989, by rfl⟩ : syracuseStep 7537319 = 11305979) B11305979
theorem B5024879 : Blo 2231435 5024879 := bstep (se 1 (by rfl) ⟨3768659, by rfl⟩ : syracuseStep 5024879 = 7537319) B7537319
theorem B3349919 : Blo 2231435 3349919 := bstep (se 1 (by rfl) ⟨2512439, by rfl⟩ : syracuseStep 3349919 = 5024879) B5024879
theorem B2233279 : Blo 2231435 2233279 := bstep (se 1 (by rfl) ⟨1674959, by rfl⟩ : syracuseStep 2233279 = 3349919) B3349919
theorem B3349925 : Blo 2231435 3349925 := bbase (se 4 (by rfl) ⟨314055, by rfl⟩ : syracuseStep 3349925 = 628111) (by norm_num)
theorem B2233283 : Blo 2231435 2233283 := bstep (se 1 (by rfl) ⟨1674962, by rfl⟩ : syracuseStep 2233283 = 3349925) B3349925
theorem B2826505 : Blo 2231435 2826505 := bbase (se 2 (by rfl) ⟨1059939, by rfl⟩ : syracuseStep 2826505 = 2119879) (by norm_num)
theorem B3768673 : Blo 2231435 3768673 := bstep (se 2 (by rfl) ⟨1413252, by rfl⟩ : syracuseStep 3768673 = 2826505) B2826505
theorem B5024897 : Blo 2231435 5024897 := bstep (se 2 (by rfl) ⟨1884336, by rfl⟩ : syracuseStep 5024897 = 3768673) B3768673
theorem B3349931 : Blo 2231435 3349931 := bstep (se 1 (by rfl) ⟨2512448, by rfl⟩ : syracuseStep 3349931 = 5024897) B5024897
theorem B2233287 : Blo 2231435 2233287 := bstep (se 1 (by rfl) ⟨1674965, by rfl⟩ : syracuseStep 2233287 = 3349931) B3349931
theorem B2512453 : Blo 2231435 2512453 := bbase (se 4 (by rfl) ⟨235542, by rfl⟩ : syracuseStep 2512453 = 471085) (by norm_num)
theorem B3349937 : Blo 2231435 3349937 := bstep (se 2 (by rfl) ⟨1256226, by rfl⟩ : syracuseStep 3349937 = 2512453) B2512453
theorem B2233291 : Blo 2231435 2233291 := bstep (se 1 (by rfl) ⟨1674968, by rfl⟩ : syracuseStep 2233291 = 3349937) B3349937
theorem B4239773 : Blo 2231435 4239773 := bbase (se 3 (by rfl) ⟨794957, by rfl⟩ : syracuseStep 4239773 = 1589915) (by norm_num)
theorem B2826515 : Blo 2231435 2826515 := bstep (se 1 (by rfl) ⟨2119886, by rfl⟩ : syracuseStep 2826515 = 4239773) B4239773
theorem B7537373 : Blo 2231435 7537373 := bstep (se 3 (by rfl) ⟨1413257, by rfl⟩ : syracuseStep 7537373 = 2826515) B2826515
theorem B5024915 : Blo 2231435 5024915 := bstep (se 1 (by rfl) ⟨3768686, by rfl⟩ : syracuseStep 5024915 = 7537373) B7537373
theorem B3349943 : Blo 2231435 3349943 := bstep (se 1 (by rfl) ⟨2512457, by rfl⟩ : syracuseStep 3349943 = 5024915) B5024915
theorem B2233295 : Blo 2231435 2233295 := bstep (se 1 (by rfl) ⟨1674971, by rfl⟩ : syracuseStep 2233295 = 3349943) B3349943
theorem B3349949 : Blo 2231435 3349949 := bbase (se 3 (by rfl) ⟨628115, by rfl⟩ : syracuseStep 3349949 = 1256231) (by norm_num)
theorem B2233299 : Blo 2231435 2233299 := bstep (se 1 (by rfl) ⟨1674974, by rfl⟩ : syracuseStep 2233299 = 3349949) B3349949
theorem B5024933 : Blo 2231435 5024933 := bbase (se 4 (by rfl) ⟨471087, by rfl⟩ : syracuseStep 5024933 = 942175) (by norm_num)
theorem B3349955 : Blo 2231435 3349955 := bstep (se 1 (by rfl) ⟨2512466, by rfl⟩ : syracuseStep 3349955 = 5024933) B5024933
theorem B2233303 : Blo 2231435 2233303 := bstep (se 1 (by rfl) ⟨1674977, by rfl⟩ : syracuseStep 2233303 = 3349955) B3349955
theorem B5653061 : Blo 2231435 5653061 := bbase (se 4 (by rfl) ⟨529974, by rfl⟩ : syracuseStep 5653061 = 1059949) (by norm_num)
theorem B3768707 : Blo 2231435 3768707 := bstep (se 1 (by rfl) ⟨2826530, by rfl⟩ : syracuseStep 3768707 = 5653061) B5653061
theorem B2512471 : Blo 2231435 2512471 := bstep (se 1 (by rfl) ⟨1884353, by rfl⟩ : syracuseStep 2512471 = 3768707) B3768707
theorem B3349961 : Blo 2231435 3349961 := bstep (se 2 (by rfl) ⟨1256235, by rfl⟩ : syracuseStep 3349961 = 2512471) B2512471
theorem B2233307 : Blo 2231435 2233307 := bstep (se 1 (by rfl) ⟨1674980, by rfl⟩ : syracuseStep 2233307 = 3349961) B3349961
theorem B2683001 : Blo 2231435 2683001 := bbase (se 2 (by rfl) ⟨1006125, by rfl⟩ : syracuseStep 2683001 = 2012251) (by norm_num)
theorem B7154669 : Blo 2231435 7154669 := bstep (se 3 (by rfl) ⟨1341500, by rfl⟩ : syracuseStep 7154669 = 2683001) B2683001
theorem B4769779 : Blo 2231435 4769779 := bstep (se 1 (by rfl) ⟨3577334, by rfl⟩ : syracuseStep 4769779 = 7154669) B7154669
theorem B6359705 : Blo 2231435 6359705 := bstep (se 2 (by rfl) ⟨2384889, by rfl⟩ : syracuseStep 6359705 = 4769779) B4769779
theorem B4239803 : Blo 2231435 4239803 := bstep (se 1 (by rfl) ⟨3179852, by rfl⟩ : syracuseStep 4239803 = 6359705) B6359705
theorem B11306141 : Blo 2231435 11306141 := bstep (se 3 (by rfl) ⟨2119901, by rfl⟩ : syracuseStep 11306141 = 4239803) B4239803
theorem B7537427 : Blo 2231435 7537427 := bstep (se 1 (by rfl) ⟨5653070, by rfl⟩ : syracuseStep 7537427 = 11306141) B11306141
theorem B5024951 : Blo 2231435 5024951 := bstep (se 1 (by rfl) ⟨3768713, by rfl⟩ : syracuseStep 5024951 = 7537427) B7537427
theorem B3349967 : Blo 2231435 3349967 := bstep (se 1 (by rfl) ⟨2512475, by rfl⟩ : syracuseStep 3349967 = 5024951) B5024951
theorem B2233311 : Blo 2231435 2233311 := bstep (se 1 (by rfl) ⟨1674983, by rfl⟩ : syracuseStep 2233311 = 3349967) B3349967
theorem B3349973 : Blo 2231435 3349973 := bbase (se 7 (by rfl) ⟨39257, by rfl⟩ : syracuseStep 3349973 = 78515) (by norm_num)
theorem B2233315 : Blo 2231435 2233315 := bstep (se 1 (by rfl) ⟨1674986, by rfl⟩ : syracuseStep 2233315 = 3349973) B3349973
theorem B8479637 : Blo 2231435 8479637 := bbase (se 6 (by rfl) ⟨198741, by rfl⟩ : syracuseStep 8479637 = 397483) (by norm_num)
theorem B5653091 : Blo 2231435 5653091 := bstep (se 1 (by rfl) ⟨4239818, by rfl⟩ : syracuseStep 5653091 = 8479637) B8479637
theorem B3768727 : Blo 2231435 3768727 := bstep (se 1 (by rfl) ⟨2826545, by rfl⟩ : syracuseStep 3768727 = 5653091) B5653091
theorem B5024969 : Blo 2231435 5024969 := bstep (se 2 (by rfl) ⟨1884363, by rfl⟩ : syracuseStep 5024969 = 3768727) B3768727
theorem B3349979 : Blo 2231435 3349979 := bstep (se 1 (by rfl) ⟨2512484, by rfl⟩ : syracuseStep 3349979 = 5024969) B5024969
theorem B2233319 : Blo 2231435 2233319 := bstep (se 1 (by rfl) ⟨1674989, by rfl⟩ : syracuseStep 2233319 = 3349979) B3349979
theorem B2512489 : Blo 2231435 2512489 := bbase (se 2 (by rfl) ⟨942183, by rfl⟩ : syracuseStep 2512489 = 1884367) (by norm_num)
theorem B3349985 : Blo 2231435 3349985 := bstep (se 2 (by rfl) ⟨1256244, by rfl⟩ : syracuseStep 3349985 = 2512489) B2512489
theorem B2233323 : Blo 2231435 2233323 := bstep (se 1 (by rfl) ⟨1674992, by rfl⟩ : syracuseStep 2233323 = 3349985) B3349985
theorem B4769813 : Blo 2231435 4769813 := bbase (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) (by norm_num)
theorem B12719501 : Blo 2231435 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B8479667 : Blo 2231435 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B5653111 : Blo 2231435 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B7537481 : Blo 2231435 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B5024987 : Blo 2231435 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B3349991 : Blo 2231435 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B2233327 : Blo 2231435 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B3349997 : Blo 2231435 3349997 := bbase (se 3 (by rfl) ⟨628124, by rfl⟩ : syracuseStep 3349997 = 1256249) (by norm_num)
theorem B2233331 : Blo 2231435 2233331 := bstep (se 1 (by rfl) ⟨1674998, by rfl⟩ : syracuseStep 2233331 = 3349997) B3349997
theorem B5025005 : Blo 2231435 5025005 := bbase (se 3 (by rfl) ⟨942188, by rfl⟩ : syracuseStep 5025005 = 1884377) (by norm_num)
theorem B3350003 : Blo 2231435 3350003 := bstep (se 1 (by rfl) ⟨2512502, by rfl⟩ : syracuseStep 3350003 = 5025005) B5025005
theorem B2233335 : Blo 2231435 2233335 := bstep (se 1 (by rfl) ⟨1675001, by rfl⟩ : syracuseStep 2233335 = 3350003) B3350003
theorem B3179893 : Blo 2231435 3179893 := bbase (se 5 (by rfl) ⟨149057, by rfl⟩ : syracuseStep 3179893 = 298115) (by norm_num)
theorem B4239857 : Blo 2231435 4239857 := bstep (se 2 (by rfl) ⟨1589946, by rfl⟩ : syracuseStep 4239857 = 3179893) B3179893
theorem B2826571 : Blo 2231435 2826571 := bstep (se 1 (by rfl) ⟨2119928, by rfl⟩ : syracuseStep 2826571 = 4239857) B4239857
theorem B3768761 : Blo 2231435 3768761 := bstep (se 2 (by rfl) ⟨1413285, by rfl⟩ : syracuseStep 3768761 = 2826571) B2826571
theorem B2512507 : Blo 2231435 2512507 := bstep (se 1 (by rfl) ⟨1884380, by rfl⟩ : syracuseStep 2512507 = 3768761) B3768761
theorem B3350009 : Blo 2231435 3350009 := bstep (se 2 (by rfl) ⟨1256253, by rfl⟩ : syracuseStep 3350009 = 2512507) B2512507
theorem B2233339 : Blo 2231435 2233339 := bstep (se 1 (by rfl) ⟨1675004, by rfl⟩ : syracuseStep 2233339 = 3350009) B3350009
theorem B9178805 : Blo 2231435 9178805 := bbase (se 5 (by rfl) ⟨430256, by rfl⟩ : syracuseStep 9178805 = 860513) (by norm_num)
theorem B24476813 : Blo 2231435 24476813 := bstep (se 3 (by rfl) ⟨4589402, by rfl⟩ : syracuseStep 24476813 = 9178805) B9178805
theorem B16317875 : Blo 2231435 16317875 := bstep (se 1 (by rfl) ⟨12238406, by rfl⟩ : syracuseStep 16317875 = 24476813) B24476813
theorem B10878583 : Blo 2231435 10878583 := bstep (se 1 (by rfl) ⟨8158937, by rfl⟩ : syracuseStep 10878583 = 16317875) B16317875
theorem B14504777 : Blo 2231435 14504777 := bstep (se 2 (by rfl) ⟨5439291, by rfl⟩ : syracuseStep 14504777 = 10878583) B10878583
theorem B9669851 : Blo 2231435 9669851 := bstep (se 1 (by rfl) ⟨7252388, by rfl⟩ : syracuseStep 9669851 = 14504777) B14504777
theorem B6446567 : Blo 2231435 6446567 := bstep (se 1 (by rfl) ⟨4834925, by rfl⟩ : syracuseStep 6446567 = 9669851) B9669851
theorem B4297711 : Blo 2231435 4297711 := bstep (se 1 (by rfl) ⟨3223283, by rfl⟩ : syracuseStep 4297711 = 6446567) B6446567
theorem B5730281 : Blo 2231435 5730281 := bstep (se 2 (by rfl) ⟨2148855, by rfl⟩ : syracuseStep 5730281 = 4297711) B4297711
theorem B3820187 : Blo 2231435 3820187 := bstep (se 1 (by rfl) ⟨2865140, by rfl⟩ : syracuseStep 3820187 = 5730281) B5730281
theorem B2546791 : Blo 2231435 2546791 := bstep (se 1 (by rfl) ⟨1910093, by rfl⟩ : syracuseStep 2546791 = 3820187) B3820187
theorem B13582885 : Blo 2231435 13582885 := bstep (se 4 (by rfl) ⟨1273395, by rfl⟩ : syracuseStep 13582885 = 2546791) B2546791
theorem B18110513 : Blo 2231435 18110513 := bstep (se 2 (by rfl) ⟨6791442, by rfl⟩ : syracuseStep 18110513 = 13582885) B13582885
theorem B48294701 : Blo 2231435 48294701 := bstep (se 3 (by rfl) ⟨9055256, by rfl⟩ : syracuseStep 48294701 = 18110513) B18110513
theorem B32196467 : Blo 2231435 32196467 := bstep (se 1 (by rfl) ⟨24147350, by rfl⟩ : syracuseStep 32196467 = 48294701) B48294701
theorem B85857245 : Blo 2231435 85857245 := bstep (se 3 (by rfl) ⟨16098233, by rfl⟩ : syracuseStep 85857245 = 32196467) B32196467
theorem B57238163 : Blo 2231435 57238163 := bstep (se 1 (by rfl) ⟨42928622, by rfl⟩ : syracuseStep 57238163 = 85857245) B85857245
theorem B38158775 : Blo 2231435 38158775 := bstep (se 1 (by rfl) ⟨28619081, by rfl⟩ : syracuseStep 38158775 = 57238163) B57238163
theorem B25439183 : Blo 2231435 25439183 := bstep (se 1 (by rfl) ⟨19079387, by rfl⟩ : syracuseStep 25439183 = 38158775) B38158775
theorem B16959455 : Blo 2231435 16959455 := bstep (se 1 (by rfl) ⟨12719591, by rfl⟩ : syracuseStep 16959455 = 25439183) B25439183
theorem B11306303 : Blo 2231435 11306303 := bstep (se 1 (by rfl) ⟨8479727, by rfl⟩ : syracuseStep 11306303 = 16959455) B16959455
theorem B7537535 : Blo 2231435 7537535 := bstep (se 1 (by rfl) ⟨5653151, by rfl⟩ : syracuseStep 7537535 = 11306303) B11306303
theorem B5025023 : Blo 2231435 5025023 := bstep (se 1 (by rfl) ⟨3768767, by rfl⟩ : syracuseStep 5025023 = 7537535) B7537535
theorem B3350015 : Blo 2231435 3350015 := bstep (se 1 (by rfl) ⟨2512511, by rfl⟩ : syracuseStep 3350015 = 5025023) B5025023
theorem B2233343 : Blo 2231435 2233343 := bstep (se 1 (by rfl) ⟨1675007, by rfl⟩ : syracuseStep 2233343 = 3350015) B3350015
theorem B3350021 : Blo 2231435 3350021 := bbase (se 4 (by rfl) ⟨314064, by rfl⟩ : syracuseStep 3350021 = 628129) (by norm_num)
theorem B2233347 : Blo 2231435 2233347 := bstep (se 1 (by rfl) ⟨1675010, by rfl⟩ : syracuseStep 2233347 = 3350021) B3350021
theorem B3768781 : Blo 2231435 3768781 := bbase (se 3 (by rfl) ⟨706646, by rfl⟩ : syracuseStep 3768781 = 1413293) (by norm_num)
theorem B5025041 : Blo 2231435 5025041 := bstep (se 2 (by rfl) ⟨1884390, by rfl⟩ : syracuseStep 5025041 = 3768781) B3768781
theorem B3350027 : Blo 2231435 3350027 := bstep (se 1 (by rfl) ⟨2512520, by rfl⟩ : syracuseStep 3350027 = 5025041) B5025041
theorem B2233351 : Blo 2231435 2233351 := bstep (se 1 (by rfl) ⟨1675013, by rfl⟩ : syracuseStep 2233351 = 3350027) B3350027
theorem B2512525 : Blo 2231435 2512525 := bbase (se 3 (by rfl) ⟨471098, by rfl⟩ : syracuseStep 2512525 = 942197) (by norm_num)
theorem B3350033 : Blo 2231435 3350033 := bstep (se 2 (by rfl) ⟨1256262, by rfl⟩ : syracuseStep 3350033 = 2512525) B2512525
theorem B2233355 : Blo 2231435 2233355 := bstep (se 1 (by rfl) ⟨1675016, by rfl⟩ : syracuseStep 2233355 = 3350033) B3350033
theorem B7537589 : Blo 2231435 7537589 := bbase (se 5 (by rfl) ⟨353324, by rfl⟩ : syracuseStep 7537589 = 706649) (by norm_num)
theorem B5025059 : Blo 2231435 5025059 := bstep (se 1 (by rfl) ⟨3768794, by rfl⟩ : syracuseStep 5025059 = 7537589) B7537589
theorem B3350039 : Blo 2231435 3350039 := bstep (se 1 (by rfl) ⟨2512529, by rfl⟩ : syracuseStep 3350039 = 5025059) B5025059
theorem B2233359 : Blo 2231435 2233359 := bstep (se 1 (by rfl) ⟨1675019, by rfl⟩ : syracuseStep 2233359 = 3350039) B3350039
theorem B3350045 : Blo 2231435 3350045 := bbase (se 3 (by rfl) ⟨628133, by rfl⟩ : syracuseStep 3350045 = 1256267) (by norm_num)
theorem B2233363 : Blo 2231435 2233363 := bstep (se 1 (by rfl) ⟨1675022, by rfl⟩ : syracuseStep 2233363 = 3350045) B3350045
theorem B5025077 : Blo 2231435 5025077 := bbase (se 5 (by rfl) ⟨235550, by rfl⟩ : syracuseStep 5025077 = 471101) (by norm_num)
theorem B3350051 : Blo 2231435 3350051 := bstep (se 1 (by rfl) ⟨2512538, by rfl⟩ : syracuseStep 3350051 = 5025077) B5025077
theorem B2233367 : Blo 2231435 2233367 := bstep (se 1 (by rfl) ⟨1675025, by rfl⟩ : syracuseStep 2233367 = 3350051) B3350051
theorem B17191061 : Blo 2231435 17191061 := bbase (se 6 (by rfl) ⟨402915, by rfl⟩ : syracuseStep 17191061 = 805831) (by norm_num)
theorem B11460707 : Blo 2231435 11460707 := bstep (se 1 (by rfl) ⟨8595530, by rfl⟩ : syracuseStep 11460707 = 17191061) B17191061
theorem B7640471 : Blo 2231435 7640471 := bstep (se 1 (by rfl) ⟨5730353, by rfl⟩ : syracuseStep 7640471 = 11460707) B11460707
theorem B5093647 : Blo 2231435 5093647 := bstep (se 1 (by rfl) ⟨3820235, by rfl⟩ : syracuseStep 5093647 = 7640471) B7640471
theorem B27166117 : Blo 2231435 27166117 := bstep (se 4 (by rfl) ⟨2546823, by rfl⟩ : syracuseStep 27166117 = 5093647) B5093647
theorem B36221489 : Blo 2231435 36221489 := bstep (se 2 (by rfl) ⟨13583058, by rfl⟩ : syracuseStep 36221489 = 27166117) B27166117
theorem B24147659 : Blo 2231435 24147659 := bstep (se 1 (by rfl) ⟨18110744, by rfl⟩ : syracuseStep 24147659 = 36221489) B36221489
theorem B16098439 : Blo 2231435 16098439 := bstep (se 1 (by rfl) ⟨12073829, by rfl⟩ : syracuseStep 16098439 = 24147659) B24147659
theorem B21464585 : Blo 2231435 21464585 := bstep (se 2 (by rfl) ⟨8049219, by rfl⟩ : syracuseStep 21464585 = 16098439) B16098439
theorem B14309723 : Blo 2231435 14309723 := bstep (se 1 (by rfl) ⟨10732292, by rfl⟩ : syracuseStep 14309723 = 21464585) B21464585
theorem B9539815 : Blo 2231435 9539815 := bstep (se 1 (by rfl) ⟨7154861, by rfl⟩ : syracuseStep 9539815 = 14309723) B14309723
theorem B12719753 : Blo 2231435 12719753 := bstep (se 2 (by rfl) ⟨4769907, by rfl⟩ : syracuseStep 12719753 = 9539815) B9539815
theorem B8479835 : Blo 2231435 8479835 := bstep (se 1 (by rfl) ⟨6359876, by rfl⟩ : syracuseStep 8479835 = 12719753) B12719753
theorem B5653223 : Blo 2231435 5653223 := bstep (se 1 (by rfl) ⟨4239917, by rfl⟩ : syracuseStep 5653223 = 8479835) B8479835
theorem B3768815 : Blo 2231435 3768815 := bstep (se 1 (by rfl) ⟨2826611, by rfl⟩ : syracuseStep 3768815 = 5653223) B5653223
theorem B2512543 : Blo 2231435 2512543 := bstep (se 1 (by rfl) ⟨1884407, by rfl⟩ : syracuseStep 2512543 = 3768815) B3768815
theorem B3350057 : Blo 2231435 3350057 := bstep (se 2 (by rfl) ⟨1256271, by rfl⟩ : syracuseStep 3350057 = 2512543) B2512543
theorem B2233371 : Blo 2231435 2233371 := bstep (se 1 (by rfl) ⟨1675028, by rfl⟩ : syracuseStep 2233371 = 3350057) B3350057
theorem B5730365 : Blo 2231435 5730365 := bbase (se 3 (by rfl) ⟨1074443, by rfl⟩ : syracuseStep 5730365 = 2148887) (by norm_num)
theorem B3820243 : Blo 2231435 3820243 := bstep (se 1 (by rfl) ⟨2865182, by rfl⟩ : syracuseStep 3820243 = 5730365) B5730365
theorem B5093657 : Blo 2231435 5093657 := bstep (se 2 (by rfl) ⟨1910121, by rfl⟩ : syracuseStep 5093657 = 3820243) B3820243
theorem B3395771 : Blo 2231435 3395771 := bstep (se 1 (by rfl) ⟨2546828, by rfl⟩ : syracuseStep 3395771 = 5093657) B5093657
theorem B2263847 : Blo 2231435 2263847 := bstep (se 1 (by rfl) ⟨1697885, by rfl⟩ : syracuseStep 2263847 = 3395771) B3395771
theorem B6036925 : Blo 2231435 6036925 := bstep (se 3 (by rfl) ⟨1131923, by rfl⟩ : syracuseStep 6036925 = 2263847) B2263847
theorem B8049233 : Blo 2231435 8049233 := bstep (se 2 (by rfl) ⟨3018462, by rfl⟩ : syracuseStep 8049233 = 6036925) B6036925
theorem B21464621 : Blo 2231435 21464621 := bstep (se 3 (by rfl) ⟨4024616, by rfl⟩ : syracuseStep 21464621 = 8049233) B8049233
theorem B14309747 : Blo 2231435 14309747 := bstep (se 1 (by rfl) ⟨10732310, by rfl⟩ : syracuseStep 14309747 = 21464621) B21464621
theorem B9539831 : Blo 2231435 9539831 := bstep (se 1 (by rfl) ⟨7154873, by rfl⟩ : syracuseStep 9539831 = 14309747) B14309747
theorem B6359887 : Blo 2231435 6359887 := bstep (se 1 (by rfl) ⟨4769915, by rfl⟩ : syracuseStep 6359887 = 9539831) B9539831
theorem B8479849 : Blo 2231435 8479849 := bstep (se 2 (by rfl) ⟨3179943, by rfl⟩ : syracuseStep 8479849 = 6359887) B6359887
theorem B11306465 : Blo 2231435 11306465 := bstep (se 2 (by rfl) ⟨4239924, by rfl⟩ : syracuseStep 11306465 = 8479849) B8479849
theorem B7537643 : Blo 2231435 7537643 := bstep (se 1 (by rfl) ⟨5653232, by rfl⟩ : syracuseStep 7537643 = 11306465) B11306465
theorem B5025095 : Blo 2231435 5025095 := bstep (se 1 (by rfl) ⟨3768821, by rfl⟩ : syracuseStep 5025095 = 7537643) B7537643
theorem B3350063 : Blo 2231435 3350063 := bstep (se 1 (by rfl) ⟨2512547, by rfl⟩ : syracuseStep 3350063 = 5025095) B5025095
theorem B2233375 : Blo 2231435 2233375 := bstep (se 1 (by rfl) ⟨1675031, by rfl⟩ : syracuseStep 2233375 = 3350063) B3350063
theorem B3350069 : Blo 2231435 3350069 := bbase (se 5 (by rfl) ⟨157034, by rfl⟩ : syracuseStep 3350069 = 314069) (by norm_num)
theorem B2233379 : Blo 2231435 2233379 := bstep (se 1 (by rfl) ⟨1675034, by rfl⟩ : syracuseStep 2233379 = 3350069) B3350069
theorem B5653253 : Blo 2231435 5653253 := bbase (se 4 (by rfl) ⟨529992, by rfl⟩ : syracuseStep 5653253 = 1059985) (by norm_num)
theorem B3768835 : Blo 2231435 3768835 := bstep (se 1 (by rfl) ⟨2826626, by rfl⟩ : syracuseStep 3768835 = 5653253) B5653253
theorem B5025113 : Blo 2231435 5025113 := bstep (se 2 (by rfl) ⟨1884417, by rfl⟩ : syracuseStep 5025113 = 3768835) B3768835
theorem B3350075 : Blo 2231435 3350075 := bstep (se 1 (by rfl) ⟨2512556, by rfl⟩ : syracuseStep 3350075 = 5025113) B5025113
theorem B2233383 : Blo 2231435 2233383 := bstep (se 1 (by rfl) ⟨1675037, by rfl⟩ : syracuseStep 2233383 = 3350075) B3350075
theorem B2512561 : Blo 2231435 2512561 := bbase (se 2 (by rfl) ⟨942210, by rfl⟩ : syracuseStep 2512561 = 1884421) (by norm_num)
theorem B3350081 : Blo 2231435 3350081 := bstep (se 2 (by rfl) ⟨1256280, by rfl⟩ : syracuseStep 3350081 = 2512561) B2512561
theorem B2233387 : Blo 2231435 2233387 := bstep (se 1 (by rfl) ⟨1675040, by rfl⟩ : syracuseStep 2233387 = 3350081) B3350081
theorem B3018485 : Blo 2231435 3018485 := bbase (se 5 (by rfl) ⟨141491, by rfl⟩ : syracuseStep 3018485 = 282983) (by norm_num)
theorem B8049293 : Blo 2231435 8049293 := bstep (se 3 (by rfl) ⟨1509242, by rfl⟩ : syracuseStep 8049293 = 3018485) B3018485
theorem B5366195 : Blo 2231435 5366195 := bstep (se 1 (by rfl) ⟨4024646, by rfl⟩ : syracuseStep 5366195 = 8049293) B8049293
theorem B3577463 : Blo 2231435 3577463 := bstep (se 1 (by rfl) ⟨2683097, by rfl⟩ : syracuseStep 3577463 = 5366195) B5366195
theorem B2384975 : Blo 2231435 2384975 := bstep (se 1 (by rfl) ⟨1788731, by rfl⟩ : syracuseStep 2384975 = 3577463) B3577463
theorem B6359933 : Blo 2231435 6359933 := bstep (se 3 (by rfl) ⟨1192487, by rfl⟩ : syracuseStep 6359933 = 2384975) B2384975
theorem B4239955 : Blo 2231435 4239955 := bstep (se 1 (by rfl) ⟨3179966, by rfl⟩ : syracuseStep 4239955 = 6359933) B6359933
theorem B5653273 : Blo 2231435 5653273 := bstep (se 2 (by rfl) ⟨2119977, by rfl⟩ : syracuseStep 5653273 = 4239955) B4239955
theorem B7537697 : Blo 2231435 7537697 := bstep (se 2 (by rfl) ⟨2826636, by rfl⟩ : syracuseStep 7537697 = 5653273) B5653273
theorem B5025131 : Blo 2231435 5025131 := bstep (se 1 (by rfl) ⟨3768848, by rfl⟩ : syracuseStep 5025131 = 7537697) B7537697
theorem B3350087 : Blo 2231435 3350087 := bstep (se 1 (by rfl) ⟨2512565, by rfl⟩ : syracuseStep 3350087 = 5025131) B5025131
theorem B2233391 : Blo 2231435 2233391 := bstep (se 1 (by rfl) ⟨1675043, by rfl⟩ : syracuseStep 2233391 = 3350087) B3350087
theorem B3350093 : Blo 2231435 3350093 := bbase (se 3 (by rfl) ⟨628142, by rfl⟩ : syracuseStep 3350093 = 1256285) (by norm_num)
theorem B2233395 : Blo 2231435 2233395 := bstep (se 1 (by rfl) ⟨1675046, by rfl⟩ : syracuseStep 2233395 = 3350093) B3350093
theorem B5025149 : Blo 2231435 5025149 := bbase (se 3 (by rfl) ⟨942215, by rfl⟩ : syracuseStep 5025149 = 1884431) (by norm_num)
theorem B3350099 : Blo 2231435 3350099 := bstep (se 1 (by rfl) ⟨2512574, by rfl⟩ : syracuseStep 3350099 = 5025149) B5025149
theorem B2233399 : Blo 2231435 2233399 := bstep (se 1 (by rfl) ⟨1675049, by rfl⟩ : syracuseStep 2233399 = 3350099) B3350099
theorem B3768869 : Blo 2231435 3768869 := bbase (se 4 (by rfl) ⟨353331, by rfl⟩ : syracuseStep 3768869 = 706663) (by norm_num)
theorem B2512579 : Blo 2231435 2512579 := bstep (se 1 (by rfl) ⟨1884434, by rfl⟩ : syracuseStep 2512579 = 3768869) B3768869
theorem B3350105 : Blo 2231435 3350105 := bstep (se 2 (by rfl) ⟨1256289, by rfl⟩ : syracuseStep 3350105 = 2512579) B2512579
theorem B2233403 : Blo 2231435 2233403 := bstep (se 1 (by rfl) ⟨1675052, by rfl⟩ : syracuseStep 2233403 = 3350105) B3350105
theorem B3179989 : Blo 2231435 3179989 := bbase (se 7 (by rfl) ⟨37265, by rfl⟩ : syracuseStep 3179989 = 74531) (by norm_num)
theorem B16959941 : Blo 2231435 16959941 := bstep (se 4 (by rfl) ⟨1589994, by rfl⟩ : syracuseStep 16959941 = 3179989) B3179989
theorem B11306627 : Blo 2231435 11306627 := bstep (se 1 (by rfl) ⟨8479970, by rfl⟩ : syracuseStep 11306627 = 16959941) B16959941
theorem B7537751 : Blo 2231435 7537751 := bstep (se 1 (by rfl) ⟨5653313, by rfl⟩ : syracuseStep 7537751 = 11306627) B11306627
theorem B5025167 : Blo 2231435 5025167 := bstep (se 1 (by rfl) ⟨3768875, by rfl⟩ : syracuseStep 5025167 = 7537751) B7537751
theorem B3350111 : Blo 2231435 3350111 := bstep (se 1 (by rfl) ⟨2512583, by rfl⟩ : syracuseStep 3350111 = 5025167) B5025167
theorem B2233407 : Blo 2231435 2233407 := bstep (se 1 (by rfl) ⟨1675055, by rfl⟩ : syracuseStep 2233407 = 3350111) B3350111
theorem B3350117 : Blo 2231435 3350117 := bbase (se 4 (by rfl) ⟨314073, by rfl⟩ : syracuseStep 3350117 = 628147) (by norm_num)
theorem B2233411 : Blo 2231435 2233411 := bstep (se 1 (by rfl) ⟨1675058, by rfl⟩ : syracuseStep 2233411 = 3350117) B3350117
theorem B2385001 : Blo 2231435 2385001 := bbase (se 2 (by rfl) ⟨894375, by rfl⟩ : syracuseStep 2385001 = 1788751) (by norm_num)
theorem B3180001 : Blo 2231435 3180001 := bstep (se 2 (by rfl) ⟨1192500, by rfl⟩ : syracuseStep 3180001 = 2385001) B2385001
theorem B4240001 : Blo 2231435 4240001 := bstep (se 2 (by rfl) ⟨1590000, by rfl⟩ : syracuseStep 4240001 = 3180001) B3180001
theorem B2826667 : Blo 2231435 2826667 := bstep (se 1 (by rfl) ⟨2120000, by rfl⟩ : syracuseStep 2826667 = 4240001) B4240001
theorem B3768889 : Blo 2231435 3768889 := bstep (se 2 (by rfl) ⟨1413333, by rfl⟩ : syracuseStep 3768889 = 2826667) B2826667
theorem B5025185 : Blo 2231435 5025185 := bstep (se 2 (by rfl) ⟨1884444, by rfl⟩ : syracuseStep 5025185 = 3768889) B3768889
theorem B3350123 : Blo 2231435 3350123 := bstep (se 1 (by rfl) ⟨2512592, by rfl⟩ : syracuseStep 3350123 = 5025185) B5025185
theorem B2233415 : Blo 2231435 2233415 := bstep (se 1 (by rfl) ⟨1675061, by rfl⟩ : syracuseStep 2233415 = 3350123) B3350123
theorem B2512597 : Blo 2231435 2512597 := bbase (se 7 (by rfl) ⟨29444, by rfl⟩ : syracuseStep 2512597 = 58889) (by norm_num)
theorem B3350129 : Blo 2231435 3350129 := bstep (se 2 (by rfl) ⟨1256298, by rfl⟩ : syracuseStep 3350129 = 2512597) B2512597
theorem B2233419 : Blo 2231435 2233419 := bstep (se 1 (by rfl) ⟨1675064, by rfl⟩ : syracuseStep 2233419 = 3350129) B3350129
theorem B2826677 : Blo 2231435 2826677 := bbase (se 5 (by rfl) ⟨132500, by rfl⟩ : syracuseStep 2826677 = 265001) (by norm_num)
theorem B7537805 : Blo 2231435 7537805 := bstep (se 3 (by rfl) ⟨1413338, by rfl⟩ : syracuseStep 7537805 = 2826677) B2826677
theorem B5025203 : Blo 2231435 5025203 := bstep (se 1 (by rfl) ⟨3768902, by rfl⟩ : syracuseStep 5025203 = 7537805) B7537805
theorem B3350135 : Blo 2231435 3350135 := bstep (se 1 (by rfl) ⟨2512601, by rfl⟩ : syracuseStep 3350135 = 5025203) B5025203
theorem B2233423 : Blo 2231435 2233423 := bstep (se 1 (by rfl) ⟨1675067, by rfl⟩ : syracuseStep 2233423 = 3350135) B3350135
theorem B3350141 : Blo 2231435 3350141 := bbase (se 3 (by rfl) ⟨628151, by rfl⟩ : syracuseStep 3350141 = 1256303) (by norm_num)
theorem B2233427 : Blo 2231435 2233427 := bstep (se 1 (by rfl) ⟨1675070, by rfl⟩ : syracuseStep 2233427 = 3350141) B3350141
theorem B5025221 : Blo 2231435 5025221 := bbase (se 4 (by rfl) ⟨471114, by rfl⟩ : syracuseStep 5025221 = 942229) (by norm_num)
theorem B3350147 : Blo 2231435 3350147 := bstep (se 1 (by rfl) ⟨2512610, by rfl⟩ : syracuseStep 3350147 = 5025221) B5025221
theorem B2233431 : Blo 2231435 2233431 := bstep (se 1 (by rfl) ⟨1675073, by rfl⟩ : syracuseStep 2233431 = 3350147) B3350147
theorem B2546897 : Blo 2231435 2546897 := bbase (se 2 (by rfl) ⟨955086, by rfl⟩ : syracuseStep 2546897 = 1910173) (by norm_num)
theorem B6791725 : Blo 2231435 6791725 := bstep (se 3 (by rfl) ⟨1273448, by rfl⟩ : syracuseStep 6791725 = 2546897) B2546897
theorem B9055633 : Blo 2231435 9055633 := bstep (se 2 (by rfl) ⟨3395862, by rfl⟩ : syracuseStep 9055633 = 6791725) B6791725
theorem B12074177 : Blo 2231435 12074177 := bstep (se 2 (by rfl) ⟨4527816, by rfl⟩ : syracuseStep 12074177 = 9055633) B9055633
theorem B8049451 : Blo 2231435 8049451 := bstep (se 1 (by rfl) ⟨6037088, by rfl⟩ : syracuseStep 8049451 = 12074177) B12074177
theorem B10732601 : Blo 2231435 10732601 := bstep (se 2 (by rfl) ⟨4024725, by rfl⟩ : syracuseStep 10732601 = 8049451) B8049451
theorem B7155067 : Blo 2231435 7155067 := bstep (se 1 (by rfl) ⟨5366300, by rfl⟩ : syracuseStep 7155067 = 10732601) B10732601
theorem B9540089 : Blo 2231435 9540089 := bstep (se 2 (by rfl) ⟨3577533, by rfl⟩ : syracuseStep 9540089 = 7155067) B7155067
theorem B6360059 : Blo 2231435 6360059 := bstep (se 1 (by rfl) ⟨4770044, by rfl⟩ : syracuseStep 6360059 = 9540089) B9540089
theorem B4240039 : Blo 2231435 4240039 := bstep (se 1 (by rfl) ⟨3180029, by rfl⟩ : syracuseStep 4240039 = 6360059) B6360059
theorem B5653385 : Blo 2231435 5653385 := bstep (se 2 (by rfl) ⟨2120019, by rfl⟩ : syracuseStep 5653385 = 4240039) B4240039
theorem B3768923 : Blo 2231435 3768923 := bstep (se 1 (by rfl) ⟨2826692, by rfl⟩ : syracuseStep 3768923 = 5653385) B5653385
theorem B2512615 : Blo 2231435 2512615 := bstep (se 1 (by rfl) ⟨1884461, by rfl⟩ : syracuseStep 2512615 = 3768923) B3768923
theorem B3350153 : Blo 2231435 3350153 := bstep (se 2 (by rfl) ⟨1256307, by rfl⟩ : syracuseStep 3350153 = 2512615) B2512615
theorem B2233435 : Blo 2231435 2233435 := bstep (se 1 (by rfl) ⟨1675076, by rfl⟩ : syracuseStep 2233435 = 3350153) B3350153
theorem C0 (j : ℕ) (h1 : 557858 ≤ j) (h2 : j ≤ 558358) : Blo 2231435 (4 * j + 3) := by
  interval_cases j
  · exact B2231435
  · exact B2231439
  · exact B2231443
  · exact B2231447
  · exact B2231451
  · exact B2231455
  · exact B2231459
  · exact B2231463
  · exact B2231467
  · exact B2231471
  · exact B2231475
  · exact B2231479
  · exact B2231483
  · exact B2231487
  · exact B2231491
  · exact B2231495
  · exact B2231499
  · exact B2231503
  · exact B2231507
  · exact B2231511
  · exact B2231515
  · exact B2231519
  · exact B2231523
  · exact B2231527
  · exact B2231531
  · exact B2231535
  · exact B2231539
  · exact B2231543
  · exact B2231547
  · exact B2231551
  · exact B2231555
  · exact B2231559
  · exact B2231563
  · exact B2231567
  · exact B2231571
  · exact B2231575
  · exact B2231579
  · exact B2231583
  · exact B2231587
  · exact B2231591
  · exact B2231595
  · exact B2231599
  · exact B2231603
  · exact B2231607
  · exact B2231611
  · exact B2231615
  · exact B2231619
  · exact B2231623
  · exact B2231627
  · exact B2231631
  · exact B2231635
  · exact B2231639
  · exact B2231643
  · exact B2231647
  · exact B2231651
  · exact B2231655
  · exact B2231659
  · exact B2231663
  · exact B2231667
  · exact B2231671
  · exact B2231675
  · exact B2231679
  · exact B2231683
  · exact B2231687
  · exact B2231691
  · exact B2231695
  · exact B2231699
  · exact B2231703
  · exact B2231707
  · exact B2231711
  · exact B2231715
  · exact B2231719
  · exact B2231723
  · exact B2231727
  · exact B2231731
  · exact B2231735
  · exact B2231739
  · exact B2231743
  · exact B2231747
  · exact B2231751
  · exact B2231755
  · exact B2231759
  · exact B2231763
  · exact B2231767
  · exact B2231771
  · exact B2231775
  · exact B2231779
  · exact B2231783
  · exact B2231787
  · exact B2231791
  · exact B2231795
  · exact B2231799
  · exact B2231803
  · exact B2231807
  · exact B2231811
  · exact B2231815
  · exact B2231819
  · exact B2231823
  · exact B2231827
  · exact B2231831
  · exact B2231835
  · exact B2231839
  · exact B2231843
  · exact B2231847
  · exact B2231851
  · exact B2231855
  · exact B2231859
  · exact B2231863
  · exact B2231867
  · exact B2231871
  · exact B2231875
  · exact B2231879
  · exact B2231883
  · exact B2231887
  · exact B2231891
  · exact B2231895
  · exact B2231899
  · exact B2231903
  · exact B2231907
  · exact B2231911
  · exact B2231915
  · exact B2231919
  · exact B2231923
  · exact B2231927
  · exact B2231931
  · exact B2231935
  · exact B2231939
  · exact B2231943
  · exact B2231947
  · exact B2231951
  · exact B2231955
  · exact B2231959
  · exact B2231963
  · exact B2231967
  · exact B2231971
  · exact B2231975
  · exact B2231979
  · exact B2231983
  · exact B2231987
  · exact B2231991
  · exact B2231995
  · exact B2231999
  · exact B2232003
  · exact B2232007
  · exact B2232011
  · exact B2232015
  · exact B2232019
  · exact B2232023
  · exact B2232027
  · exact B2232031
  · exact B2232035
  · exact B2232039
  · exact B2232043
  · exact B2232047
  · exact B2232051
  · exact B2232055
  · exact B2232059
  · exact B2232063
  · exact B2232067
  · exact B2232071
  · exact B2232075
  · exact B2232079
  · exact B2232083
  · exact B2232087
  · exact B2232091
  · exact B2232095
  · exact B2232099
  · exact B2232103
  · exact B2232107
  · exact B2232111
  · exact B2232115
  · exact B2232119
  · exact B2232123
  · exact B2232127
  · exact B2232131
  · exact B2232135
  · exact B2232139
  · exact B2232143
  · exact B2232147
  · exact B2232151
  · exact B2232155
  · exact B2232159
  · exact B2232163
  · exact B2232167
  · exact B2232171
  · exact B2232175
  · exact B2232179
  · exact B2232183
  · exact B2232187
  · exact B2232191
  · exact B2232195
  · exact B2232199
  · exact B2232203
  · exact B2232207
  · exact B2232211
  · exact B2232215
  · exact B2232219
  · exact B2232223
  · exact B2232227
  · exact B2232231
  · exact B2232235
  · exact B2232239
  · exact B2232243
  · exact B2232247
  · exact B2232251
  · exact B2232255
  · exact B2232259
  · exact B2232263
  · exact B2232267
  · exact B2232271
  · exact B2232275
  · exact B2232279
  · exact B2232283
  · exact B2232287
  · exact B2232291
  · exact B2232295
  · exact B2232299
  · exact B2232303
  · exact B2232307
  · exact B2232311
  · exact B2232315
  · exact B2232319
  · exact B2232323
  · exact B2232327
  · exact B2232331
  · exact B2232335
  · exact B2232339
  · exact B2232343
  · exact B2232347
  · exact B2232351
  · exact B2232355
  · exact B2232359
  · exact B2232363
  · exact B2232367
  · exact B2232371
  · exact B2232375
  · exact B2232379
  · exact B2232383
  · exact B2232387
  · exact B2232391
  · exact B2232395
  · exact B2232399
  · exact B2232403
  · exact B2232407
  · exact B2232411
  · exact B2232415
  · exact B2232419
  · exact B2232423
  · exact B2232427
  · exact B2232431
  · exact B2232435
  · exact B2232439
  · exact B2232443
  · exact B2232447
  · exact B2232451
  · exact B2232455
  · exact B2232459
  · exact B2232463
  · exact B2232467
  · exact B2232471
  · exact B2232475
  · exact B2232479
  · exact B2232483
  · exact B2232487
  · exact B2232491
  · exact B2232495
  · exact B2232499
  · exact B2232503
  · exact B2232507
  · exact B2232511
  · exact B2232515
  · exact B2232519
  · exact B2232523
  · exact B2232527
  · exact B2232531
  · exact B2232535
  · exact B2232539
  · exact B2232543
  · exact B2232547
  · exact B2232551
  · exact B2232555
  · exact B2232559
  · exact B2232563
  · exact B2232567
  · exact B2232571
  · exact B2232575
  · exact B2232579
  · exact B2232583
  · exact B2232587
  · exact B2232591
  · exact B2232595
  · exact B2232599
  · exact B2232603
  · exact B2232607
  · exact B2232611
  · exact B2232615
  · exact B2232619
  · exact B2232623
  · exact B2232627
  · exact B2232631
  · exact B2232635
  · exact B2232639
  · exact B2232643
  · exact B2232647
  · exact B2232651
  · exact B2232655
  · exact B2232659
  · exact B2232663
  · exact B2232667
  · exact B2232671
  · exact B2232675
  · exact B2232679
  · exact B2232683
  · exact B2232687
  · exact B2232691
  · exact B2232695
  · exact B2232699
  · exact B2232703
  · exact B2232707
  · exact B2232711
  · exact B2232715
  · exact B2232719
  · exact B2232723
  · exact B2232727
  · exact B2232731
  · exact B2232735
  · exact B2232739
  · exact B2232743
  · exact B2232747
  · exact B2232751
  · exact B2232755
  · exact B2232759
  · exact B2232763
  · exact B2232767
  · exact B2232771
  · exact B2232775
  · exact B2232779
  · exact B2232783
  · exact B2232787
  · exact B2232791
  · exact B2232795
  · exact B2232799
  · exact B2232803
  · exact B2232807
  · exact B2232811
  · exact B2232815
  · exact B2232819
  · exact B2232823
  · exact B2232827
  · exact B2232831
  · exact B2232835
  · exact B2232839
  · exact B2232843
  · exact B2232847
  · exact B2232851
  · exact B2232855
  · exact B2232859
  · exact B2232863
  · exact B2232867
  · exact B2232871
  · exact B2232875
  · exact B2232879
  · exact B2232883
  · exact B2232887
  · exact B2232891
  · exact B2232895
  · exact B2232899
  · exact B2232903
  · exact B2232907
  · exact B2232911
  · exact B2232915
  · exact B2232919
  · exact B2232923
  · exact B2232927
  · exact B2232931
  · exact B2232935
  · exact B2232939
  · exact B2232943
  · exact B2232947
  · exact B2232951
  · exact B2232955
  · exact B2232959
  · exact B2232963
  · exact B2232967
  · exact B2232971
  · exact B2232975
  · exact B2232979
  · exact B2232983
  · exact B2232987
  · exact B2232991
  · exact B2232995
  · exact B2232999
  · exact B2233003
  · exact B2233007
  · exact B2233011
  · exact B2233015
  · exact B2233019
  · exact B2233023
  · exact B2233027
  · exact B2233031
  · exact B2233035
  · exact B2233039
  · exact B2233043
  · exact B2233047
  · exact B2233051
  · exact B2233055
  · exact B2233059
  · exact B2233063
  · exact B2233067
  · exact B2233071
  · exact B2233075
  · exact B2233079
  · exact B2233083
  · exact B2233087
  · exact B2233091
  · exact B2233095
  · exact B2233099
  · exact B2233103
  · exact B2233107
  · exact B2233111
  · exact B2233115
  · exact B2233119
  · exact B2233123
  · exact B2233127
  · exact B2233131
  · exact B2233135
  · exact B2233139
  · exact B2233143
  · exact B2233147
  · exact B2233151
  · exact B2233155
  · exact B2233159
  · exact B2233163
  · exact B2233167
  · exact B2233171
  · exact B2233175
  · exact B2233179
  · exact B2233183
  · exact B2233187
  · exact B2233191
  · exact B2233195
  · exact B2233199
  · exact B2233203
  · exact B2233207
  · exact B2233211
  · exact B2233215
  · exact B2233219
  · exact B2233223
  · exact B2233227
  · exact B2233231
  · exact B2233235
  · exact B2233239
  · exact B2233243
  · exact B2233247
  · exact B2233251
  · exact B2233255
  · exact B2233259
  · exact B2233263
  · exact B2233267
  · exact B2233271
  · exact B2233275
  · exact B2233279
  · exact B2233283
  · exact B2233287
  · exact B2233291
  · exact B2233295
  · exact B2233299
  · exact B2233303
  · exact B2233307
  · exact B2233311
  · exact B2233315
  · exact B2233319
  · exact B2233323
  · exact B2233327
  · exact B2233331
  · exact B2233335
  · exact B2233339
  · exact B2233343
  · exact B2233347
  · exact B2233351
  · exact B2233355
  · exact B2233359
  · exact B2233363
  · exact B2233367
  · exact B2233371
  · exact B2233375
  · exact B2233379
  · exact B2233383
  · exact B2233387
  · exact B2233391
  · exact B2233395
  · exact B2233399
  · exact B2233403
  · exact B2233407
  · exact B2233411
  · exact B2233415
  · exact B2233419
  · exact B2233423
  · exact B2233427
  · exact B2233431
  · exact B2233435
theorem solution (m : ℕ) (hlo : 2231435 ≤ m) (hhi : m ≤ 2233435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 557858 ≤ j := by omega
    have hj2 : j ≤ 558358 := by omega
    have hb : Blo 2231435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
